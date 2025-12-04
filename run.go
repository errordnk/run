package main

import (
	"context"
	"fmt"
	"io"
	"net/http"
	"os"
	"os/exec"
	"strings"
	"time"

	"github.com/charmbracelet/bubbles/progress"
	"github.com/charmbracelet/bubbles/textarea"
	"github.com/charmbracelet/bubbles/viewport"
	tea "github.com/charmbracelet/bubbletea"
	"github.com/charmbracelet/lipgloss"
	"github.com/redis/go-redis/v9"
)

var (
	servers []string
	localIP string
	rdb     *redis.Client
	ctx     = context.Background()
)

const (
	serverListURL       = "https://sarnet.ru/srv/"
	localIPURL          = "https://sarnet.ru/ip"
	redisAddr           = "sarnet.ru:6379"
	redisHistoryKey     = "run:history"
	identityFile        = "~/.ssh/id_rsa" // Укажите путь к вашему SSH ключу здесь, если нужно использовать конкретный ключ. Если стандартный - оставьте как есть или "" для дефолта.
	sshTimeout          = 5               // SSH connect timeout in seconds
	sshAliveInterval    = 3               // SSH keep-alive interval in seconds
	maxRetries          = 3               // Maximum number of retry attempts for network errors
	retryBaseDelay      = 100             // Base retry delay in milliseconds (exponential backoff)
	maxConcurrentSSH    = 20              // Maximum concurrent SSH connections
	sshConnectionDelay  = 50              // Delay between starting SSH connections in milliseconds
	maxExecutionTime    = 30              // Maximum execution time per server in seconds
)

// Interactive TUI programs that should not be run via ssh
var interactiveTUIPrograms = []string{
	"mc", "lazygit", "gdu", "htop", "top", "vim", "vi", "nano",
	"emacs", "nvim", "less", "more", "tmux", "screen", "mutt", "ranger",
	"nnn", "vifm", "cmus", "ncmpcpp", "weechat", "irssi", "lynx",
}

type resultMsg struct {
	server      string
	serverIndex int
	command     string
	output      string
	err         error
	duration    time.Duration
}

type model struct {
	textarea       textarea.Model
	viewport       viewport.Model
	progress       progress.Model
	output         string
	results        []resultMsg
	totalTasks     int
	completedTasks int
	currentCommand string
	ready          bool
	width          int
	height         int
	commandHistory []string
	historyIndex   int
	tempCommand    string
}

var (
	successBadgeStyle = lipgloss.NewStyle().
				Background(lipgloss.Color("149")).
				Foreground(lipgloss.Color("15")).
				Bold(true).
				Padding(0, 1)

	errorBadgeStyle = lipgloss.NewStyle().
			Background(lipgloss.Color("167")).
			Foreground(lipgloss.Color("15")).
			Bold(true).
			Padding(0, 1)

	errorStyle = lipgloss.NewStyle().
			Foreground(lipgloss.Color("1")) // Red for error counter
)

func (m model) Init() tea.Cmd {
	return textarea.Blink
}

func (m model) Update(msg tea.Msg) (tea.Model, tea.Cmd) {
	var cmds []tea.Cmd
	var cmd tea.Cmd

	switch msg := msg.(type) {
	case tea.KeyMsg:
		switch msg.String() {
		case "ctrl+c", "esc":
			return m, tea.Quit
		case "enter":
			if m.textarea.Value() != "" {
				command := strings.TrimSpace(m.textarea.Value())
				m.textarea.Reset()
				m.currentCommand = command
				m.completedTasks = 0
				m.totalTasks = len(servers)
				m.results = []resultMsg{}
				m.output = ""
				m.viewport.SetContent(m.output)
				m.viewport.GotoTop() // Reset viewport scroll position

				// Add to history if not duplicate of last command
				if len(m.commandHistory) == 0 || m.commandHistory[len(m.commandHistory)-1] != command {
					m.commandHistory = append(m.commandHistory, command)
					// Save to Redis asynchronously (ignore errors to not block UI)
					go saveCommandToRedis(command)
				}
				m.historyIndex = 0
				m.tempCommand = ""

				cmd = m.executeCommands(command)
				cmds = append(cmds, cmd)
			}
		case "ctrl+up":
			// Navigate command history backwards (newer to older)
			if len(m.commandHistory) > 0 && m.historyIndex < len(m.commandHistory) {
				if m.historyIndex == 0 {
					// Save current input before entering history
					m.tempCommand = m.textarea.Value()
				}
				m.historyIndex++
				m.textarea.SetValue(m.commandHistory[len(m.commandHistory)-m.historyIndex])
			}
			return m, nil
		case "ctrl+down":
			// Navigate command history forwards (older to newer)
			if m.historyIndex > 0 {
				m.historyIndex--
				if m.historyIndex == 0 {
					// Restore saved input
					m.textarea.SetValue(m.tempCommand)
					m.tempCommand = ""
				} else {
					m.textarea.SetValue(m.commandHistory[len(m.commandHistory)-m.historyIndex])
				}
			}
			return m, nil
		case "home":
			m.viewport.GotoTop()
			return m, nil
		case "end":
			m.viewport.GotoBottom()
			return m, nil
		case "up", "down", "pgup", "pgdown":
			// Viewport navigation
			m.viewport, cmd = m.viewport.Update(msg)
			cmds = append(cmds, cmd)
			return m, tea.Batch(cmds...)
		}
	case tea.WindowSizeMsg:
		m.width = msg.Width
		m.height = msg.Height

		// Input area: 1 line + borders = 3 lines total
		inputHeight := 3
		// Progress bar: 1 line
		progressHeight := 1
		// Headers and spacing: ~2 lines
		headerHeight := 2

		// Viewport gets the rest
		viewportHeight := msg.Height - inputHeight - progressHeight - headerHeight
		if viewportHeight < 5 {
			viewportHeight = 5
		}

		m.viewport.Width = msg.Width - 4
		m.viewport.Height = viewportHeight
		m.textarea.SetWidth(msg.Width - 4)
		m.textarea.SetHeight(1)           // Single line input
		m.progress.Width = msg.Width - 10 // Reserve space for error counter on the right

		// Re-render results with new width
		m.renderResults()

		if !m.ready {
			m.viewport.YPosition = 0
			m.ready = true
		}
	case resultMsg:
		// Store result
		m.results = append(m.results, msg)
		m.completedTasks++

		// Re-render all results
		m.renderResults()

		if m.totalTasks > 0 {
			cmd = m.progress.SetPercent(float64(m.completedTasks) / float64(m.totalTasks))
			cmds = append(cmds, cmd)
		}
	case progress.FrameMsg:
		progressModel, cmd := m.progress.Update(msg)
		m.progress = progressModel.(progress.Model)
		cmds = append(cmds, cmd)
	}

	m.textarea, cmd = m.textarea.Update(msg)
	cmds = append(cmds, cmd)

	return m, tea.Batch(cmds...)
}

func (m model) View() string {
	if !m.ready {
		return "Initializing..."
	}

	// Output viewport (scrollable, takes most of the screen)
	outputPanel := lipgloss.NewStyle().
		Border(lipgloss.NormalBorder()).
		BorderForeground(lipgloss.Color("63")).
		Padding(0, 1).
		Render(m.viewport.View())

	// Progress bar with error counter on the right
	errorCount := 0
	for _, result := range m.results {
		if result.err != nil {
			errorCount++
		}
	}
	errorCounter := errorStyle.Render(fmt.Sprintf(" Errors:%2d", errorCount))
	progressBar := lipgloss.JoinHorizontal(lipgloss.Left, m.progress.View(), errorCounter)

	// Input area (fixed at bottom)
	inputPanel := lipgloss.NewStyle().
		Border(lipgloss.NormalBorder()).
		BorderForeground(lipgloss.Color("63")).
		Padding(0, 1).
		Render(m.textarea.View())

	return lipgloss.JoinVertical(lipgloss.Left,
		outputPanel,
		progressBar,
		inputPanel,
	)
}

func wrapText(text string, width int) string {
	if width <= 0 {
		return text
	}

	// Don't wrap text with ANSI escape codes - preserve formatting as-is
	if strings.Contains(text, "\x1b[") {
		return text
	}

	lines := strings.Split(text, "\n")
	var wrapped []string

	for _, line := range lines {
		if len(line) <= width {
			wrapped = append(wrapped, line)
			continue
		}

		// Wrap long lines without ANSI codes
		for len(line) > width {
			wrapped = append(wrapped, line[:width])
			line = line[width:]
		}
		if len(line) > 0 {
			wrapped = append(wrapped, line)
		}
	}

	return strings.Join(wrapped, "\n")
}

func (m *model) renderResults() {
	m.output = ""

	// Calculate progress and find pending servers
	progress := float64(m.completedTasks) / float64(m.totalTasks)
	var pendingServers []int
	if progress > 0.95 && m.completedTasks < m.totalTasks {
		// Find which servers haven't responded yet
		respondedServers := make(map[int]bool)
		for _, result := range m.results {
			respondedServers[result.serverIndex] = true
		}
		for i := 0; i < m.totalTasks; i++ {
			if !respondedServers[i] {
				pendingServers = append(pendingServers, i)
			}
		}
	}

	for i, result := range m.results {
		indexStr := fmt.Sprintf("%d", i)
		if i < 10 {
			indexStr = fmt.Sprintf("0%d", i)
		}

		// Format badge with time right-aligned
		icon := "✓"
		style := successBadgeStyle
		if result.err != nil {
			icon = "✗"
			style = errorBadgeStyle
		}

		// Format pending servers list
		pendingStr := ""
		if len(pendingServers) > 0 {
			pendingNumbers := make([]string, len(pendingServers))
			for i, idx := range pendingServers {
				pendingNumbers[i] = fmt.Sprintf("%d", idx)
			}
			pendingStr = fmt.Sprintf("[%s] ", strings.Join(pendingNumbers, ","))
		}

		timeStr := fmt.Sprintf("%.2f ", result.duration.Seconds())
		leftPart := fmt.Sprintf("%s %s [%02d] %-15s ", indexStr, icon, result.serverIndex, result.server)

		// Calculate available space for command (accounting for pending servers)
		badgeWidth := m.width - 3
		availableForCommand := badgeWidth - len(leftPart) - len(timeStr) - len(pendingStr) - 2 // -2 for padding

		command := result.command
		if len(command) > availableForCommand {
			if availableForCommand > 3 {
				command = command[:availableForCommand-3] + "..."
			} else {
				command = "..."
			}
		}

		// Right-align time with pending servers
		leftWithCmd := leftPart + command
		padding := badgeWidth - len(leftWithCmd) - len(pendingStr) - len(timeStr)
		if padding < 0 {
			padding = 0
		}
		badgeText := leftWithCmd + strings.Repeat(" ", padding) + pendingStr + timeStr

		badge := style.Width(badgeWidth).Render(badgeText)
		m.output += badge + "\n"

		isLast := i == len(m.results)-1

		// Wrap output to viewport width
		wrapWidth := m.width - 4 // Account for viewport padding

		if result.err != nil {
			m.output += strings.TrimSpace(result.err.Error())
		} else if trimmedOutput := strings.TrimSpace(result.output); trimmedOutput != "" {
			wrappedOutput := wrapText(trimmedOutput, wrapWidth)
			// Don't render with outputStyle to preserve ANSI colors from commands
			m.output += wrappedOutput
		}
		if !isLast {
			m.output += "\n"
		}
	}
	m.viewport.SetContent(m.output)
}

func cleanTerminalOutput(output string) string {
	// Normalize line endings
	output = strings.ReplaceAll(output, "\r\n", "\n")

	// Process each line separately
	lines := strings.Split(output, "\n")
	var cleaned []string

	for _, line := range lines {
		// If line contains \r, take only the last segment (final version of progress bar)
		if strings.Contains(line, "\r") {
			segments := strings.Split(line, "\r")
			// Find last non-empty segment
			for i := len(segments) - 1; i >= 0; i-- {
				if trimmed := strings.TrimSpace(segments[i]); trimmed != "" {
					cleaned = append(cleaned, segments[i])
					break
				}
			}
		} else {
			// No carriage return, keep line as is if not empty
			if strings.TrimSpace(line) != "" {
				cleaned = append(cleaned, line)
			}
		}
	}

	return strings.Join(cleaned, "\n")
}

// isInteractiveTUI checks if command is an interactive TUI program
func isInteractiveTUI(command string) bool {
	// Extract first word (program name) from command
	fields := strings.Fields(command)
	if len(fields) == 0 {
		return false
	}

	program := strings.TrimSpace(fields[0])

	// Check against known interactive TUI programs
	for _, tui := range interactiveTUIPrograms {
		if program == tui {
			return true
		}
	}

	return false
}

// isNetworkError checks if error is a network-related error that should be retried
func isNetworkError(err error) bool {
	if err == nil {
		return false
	}

	errStr := strings.ToLower(err.Error())

	// Common SSH network errors that should trigger retry
	networkErrors := []string{
		"connection refused",
		"connection reset",
		"connection timed out",
		"no route to host",
		"network is unreachable",
		"i/o timeout",
		"broken pipe",
		"connection closed by remote host",
		"ssh: handshake failed",
		"ssh: connect to host",
		"dial tcp",
		"temporary failure",
		"resource temporarily unavailable",
		"operation timed out",
		"transport endpoint is not connected",
		"software caused connection abort",
		"host is down",
		"socket is not connected",
		"connection reset by peer",
		"network dropped connection",
		"protocol error",
		"bad file descriptor",
	}

	for _, netErr := range networkErrors {
		if strings.Contains(errStr, netErr) {
			return true
		}
	}

	return false
}

// executeSSHWithRetry executes SSH command with retry logic for network errors
func executeSSHWithRetry(server string, args []string, maxTime time.Duration) ([]byte, error, int) {
	var output []byte
	var err error
	attempts := 0
	var lastErrorOutput []byte

	startTime := time.Now()

	for attempt := 0; attempt <= maxRetries; attempt++ {
		attempts = attempt + 1

		// Check if we've exceeded max execution time
		elapsed := time.Since(startTime)
		if elapsed >= maxTime {
			return lastErrorOutput, fmt.Errorf("execution timeout after %v", elapsed), attempts
		}

		// Execute SSH command with timeout
		remainingTime := maxTime - elapsed
		if remainingTime < time.Duration(sshTimeout)*time.Second {
			// Not enough time for another attempt
			break
		}

		sshCmd := exec.Command("ssh", args...)
		output, err = sshCmd.CombinedOutput()
		lastErrorOutput = output

		// Success - return immediately
		if err == nil {
			return output, nil, attempts
		}

		// Check if it's exit status 255 (SSH connection failure)
		if exitErr, ok := err.(*exec.ExitError); ok {
			if exitErr.ExitCode() == 255 {
				// SSH connection failure - check if we have time to retry
				if attempt < maxRetries {
					delay := time.Duration(retryBaseDelay*(1<<uint(attempt))) * time.Millisecond

					// Check if we have time for the delay + another attempt
					if time.Since(startTime)+delay+time.Duration(sshTimeout)*time.Second < maxTime {
						time.Sleep(delay)
						continue
					}
					// Not enough time left, break
					break
				}
			}
		}

		// Non-network error - don't retry
		if !isNetworkError(err) {
			return output, err, attempts
		}

		// Network error - retry with exponential backoff if we have time
		if attempt < maxRetries {
			delay := time.Duration(retryBaseDelay*(1<<uint(attempt))) * time.Millisecond

			// Check if we have time for the delay + another attempt
			if time.Since(startTime)+delay+time.Duration(sshTimeout)*time.Second < maxTime {
				time.Sleep(delay)
			} else {
				// Not enough time left, break
				break
			}
		}
	}

	// If we exhausted all retries, append SSH error details to output
	if len(lastErrorOutput) > 0 {
		return lastErrorOutput, err, attempts
	}
	return output, err, attempts
}

func (m *model) executeCommands(command string) tea.Cmd {
	// Check if command is an interactive TUI program
	if isInteractiveTUI(command) {
		// Return error result for all servers
		cmds := make([]tea.Cmd, len(servers))
		for i, server := range servers {
			serverIdx := i
			srv := server
			cmds[i] = func() tea.Msg {
				return resultMsg{
					server:      srv,
					serverIndex: serverIdx,
					command:     command,
					output:      "",
					err:         fmt.Errorf("interactive TUI program detected - use direct SSH instead"),
					duration:    0,
				}
			}
		}
		return tea.Batch(cmds...)
	}

	// Create semaphore for limiting concurrent SSH connections
	sem := make(chan struct{}, maxConcurrentSSH)

	cmds := make([]tea.Cmd, len(servers))
	for i, server := range servers {
		// Add small delay between connection attempts to avoid overwhelming the system
		delay := time.Duration(i*sshConnectionDelay) * time.Millisecond
		cmds[i] = m.executeOnServerWithSemaphore(i, server, command, sem, delay)
	}
	return tea.Batch(cmds...)
}

func (m *model) executeOnServerWithSemaphore(serverIndex int, server, command string, sem chan struct{}, delay time.Duration) tea.Cmd {
	return func() tea.Msg {
		// Add initial delay to stagger connection attempts
		if delay > 0 {
			time.Sleep(delay)
		}

		// Acquire semaphore
		sem <- struct{}{}
		defer func() { <-sem }()

		start := time.Now()

		args := []string{
			"-tt", // Force pseudo-terminal allocation for honest terminal emulation
			"-q",  // Quiet mode: suppress connection closed messages
			"-o", fmt.Sprintf("ConnectTimeout=%d", sshTimeout),
			"-o", fmt.Sprintf("ServerAliveInterval=%d", sshAliveInterval),
			"-o", "ServerAliveCountMax=2",
			"-o", "BatchMode=yes",                    // Disable password prompts
			"-o", "StrictHostKeyChecking=accept-new", // Accept new host keys
			"-o", "TCPKeepAlive=yes",                 // Enable TCP keepalive
			"-o", "Compression=yes",                  // Enable compression for faster transfer
		}
		if identityFile != "" {
			args = append(args, "-i", identityFile)
		}

		// Wrap command with environment variables to force color output on remote server
		wrappedCommand := fmt.Sprintf("TERM=xterm-256color COLORTERM=truecolor CLICOLOR_FORCE=1 %s", command)
		args = append(args, server, wrappedCommand)

		output, err, _ := executeSSHWithRetry(server, args, time.Duration(maxExecutionTime)*time.Second)

		duration := time.Since(start)

		// Clean output: remove carriage returns and filter progress updates
		cleanOutput := cleanTerminalOutput(string(output))

		return resultMsg{
			server:      server,
			serverIndex: serverIndex,
			command:     command,
			output:      strings.TrimSpace(cleanOutput),
			err:         err,
			duration:    duration,
		}
	}
}

func (m *model) executeOnServer(serverIndex int, server, command string) tea.Cmd {
	return func() tea.Msg {
		start := time.Now()

		args := []string{
			"-tt", // Force pseudo-terminal allocation for honest terminal emulation
			"-q",  // Quiet mode: suppress connection closed messages
			"-o", fmt.Sprintf("ConnectTimeout=%d", sshTimeout),
			"-o", fmt.Sprintf("ServerAliveInterval=%d", sshAliveInterval),
			"-o", "ServerAliveCountMax=2",
			"-o", "BatchMode=yes",                    // Disable password prompts
			"-o", "StrictHostKeyChecking=accept-new", // Accept new host keys
			"-o", "TCPKeepAlive=yes",                 // Enable TCP keepalive
			"-o", "Compression=yes",                  // Enable compression for faster transfer
		}
		if identityFile != "" {
			args = append(args, "-i", identityFile)
		}

		// Wrap command with environment variables to force color output on remote server
		wrappedCommand := fmt.Sprintf("TERM=xterm-256color COLORTERM=truecolor CLICOLOR_FORCE=1 %s", command)
		args = append(args, server, wrappedCommand)

		output, err, _ := executeSSHWithRetry(server, args, time.Duration(maxExecutionTime)*time.Second)

		duration := time.Since(start)

		// Clean output: remove carriage returns and filter progress updates
		cleanOutput := cleanTerminalOutput(string(output))

		return resultMsg{
			server:      server,
			serverIndex: serverIndex,
			command:     command,
			output:      strings.TrimSpace(cleanOutput),
			err:         err,
			duration:    duration,
		}
	}
}

func fetchLocalIP() error {
	resp, err := http.Get(localIPURL)
	if err != nil {
		return fmt.Errorf("error fetching local IP: %w", err)
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		return fmt.Errorf("unexpected status code: %d", resp.StatusCode)
	}

	body, err := io.ReadAll(resp.Body)
	if err != nil {
		return fmt.Errorf("error reading local IP: %w", err)
	}

	localIP = strings.TrimSpace(string(body))
	if localIP == "" {
		return fmt.Errorf("empty local IP")
	}
	return nil
}

func fetchServers() error {
	resp, err := http.Get(serverListURL)
	if err != nil {
		return fmt.Errorf("error fetching server list: %w", err)
	}
	defer resp.Body.Close()

	if resp.StatusCode != http.StatusOK {
		return fmt.Errorf("unexpected status code: %d", resp.StatusCode)
	}

	body, err := io.ReadAll(resp.Body)
	if err != nil {
		return fmt.Errorf("error reading response body: %w", err)
	}

	lines := strings.Split(string(body), "\n")
	var filtered []string
	for _, line := range lines {
		trimmed := strings.TrimSpace(line)
		if trimmed != "" {
			filtered = append(filtered, trimmed)
		}
	}
	servers = filtered
	return nil
}

// noopLogger is a logger that discards all output
type noopLogger struct{}

func (l *noopLogger) Printf(_ context.Context, _ string, _ ...interface{}) {}

func initRedis() error {
	// Disable Redis client logging completely
	redis.SetLogger(&noopLogger{})

	rdb = redis.NewClient(&redis.Options{
		Addr:             redisAddr,
		DisableIndentity: true, // Disable client-side caching to avoid compatibility issues
	})

	// Test connection
	if err := rdb.Ping(ctx).Err(); err != nil {
		return fmt.Errorf("error connecting to Redis: %w", err)
	}

	return nil
}

func loadHistoryFromRedis() ([]string, error) {
	// Get all commands from Redis list
	commands, err := rdb.LRange(ctx, redisHistoryKey, 0, -1).Result()
	if err != nil && err != redis.Nil {
		return nil, fmt.Errorf("error loading history from Redis: %w", err)
	}

	return commands, nil
}

func saveCommandToRedis(command string) error {
	// Remove command if it already exists (to maintain uniqueness)
	if err := rdb.LRem(ctx, redisHistoryKey, 0, command).Err(); err != nil {
		return fmt.Errorf("error removing duplicate command: %w", err)
	}

	// Add command to the end of the list
	if err := rdb.RPush(ctx, redisHistoryKey, command).Err(); err != nil {
		return fmt.Errorf("error saving command to Redis: %w", err)
	}

	return nil
}

// runCommandNonInteractive executes command on all servers in non-interactive mode
func runCommandNonInteractive(command string) {
	// Check if command is an interactive TUI program
	if isInteractiveTUI(command) {
		fmt.Fprintf(os.Stderr, "Error: interactive TUI program detected - use direct SSH instead\n")
		os.Exit(1)
	}

	// Create semaphore for limiting concurrent SSH connections
	sem := make(chan struct{}, maxConcurrentSSH)

	// Execute command on all servers concurrently
	results := make(chan resultMsg, len(servers))
	for i, server := range servers {
		go func(idx int, srv string) {
			// Add small delay to stagger connection attempts
			if idx > 0 {
				time.Sleep(time.Duration(idx*sshConnectionDelay) * time.Millisecond)
			}

			// Acquire semaphore
			sem <- struct{}{}
			defer func() { <-sem }()

			start := time.Now()

			args := []string{
				"-tt", // Force pseudo-terminal allocation for honest terminal emulation
				"-q",  // Quiet mode: suppress connection closed messages
				"-o", fmt.Sprintf("ConnectTimeout=%d", sshTimeout),
				"-o", fmt.Sprintf("ServerAliveInterval=%d", sshAliveInterval),
				"-o", "ServerAliveCountMax=2",
				"-o", "BatchMode=yes",                    // Disable password prompts
				"-o", "StrictHostKeyChecking=accept-new", // Accept new host keys
				"-o", "TCPKeepAlive=yes",                 // Enable TCP keepalive
				"-o", "Compression=yes",                  // Enable compression for faster transfer
			}
			if identityFile != "" {
				args = append(args, "-i", identityFile)
			}

			// Wrap command with environment variables to force color output on remote server
			wrappedCommand := fmt.Sprintf("TERM=xterm-256color COLORTERM=truecolor CLICOLOR_FORCE=1 %s", command)
			args = append(args, srv, wrappedCommand)

			output, err, _ := executeSSHWithRetry(srv, args, time.Duration(maxExecutionTime)*time.Second)

			duration := time.Since(start)

			// Clean output: remove carriage returns and filter progress updates
			cleanOutput := cleanTerminalOutput(string(output))

			results <- resultMsg{
				server:      srv,
				serverIndex: idx,
				command:     command,
				output:      cleanOutput,
				err:         err,
				duration:    duration,
			}
		}(i, server)
	}

	// Collect all results
	allResults := make([]resultMsg, 0, len(servers))
	for range servers {
		allResults = append(allResults, <-results)
	}

	// Sort results by server index
	sortedResults := make([]resultMsg, len(allResults))
	for _, r := range allResults {
		sortedResults[r.serverIndex] = r
	}

	// Print results
	successCount := 0
	errorCount := 0
	for _, result := range sortedResults {
		if result.err == nil {
			successCount++
		} else {
			errorCount++
		}

		// Print server header
		icon := "✓"
		if result.err != nil {
			icon = "✗"
		}
		fmt.Printf("%s [%02d] %s (%.2fs)\n", icon, result.serverIndex, result.server, result.duration.Seconds())

		// Print output or error
		if result.err != nil {
			fmt.Fprintf(os.Stderr, "  Error: %v\n", result.err)
		}
		if trimmedOutput := strings.TrimSpace(result.output); trimmedOutput != "" {
			// Indent output
			lines := strings.Split(trimmedOutput, "\n")
			for _, line := range lines {
				fmt.Printf("  %s\n", line)
			}
		}
		fmt.Println()
	}

	// Print summary
	fmt.Printf("Total: %d | Success: %d | Failed: %d\n", len(servers), successCount, errorCount)

	// Exit with error if any server failed
	if errorCount > 0 {
		os.Exit(1)
	}
}

func main() {
	if err := fetchLocalIP(); err != nil {
		os.Exit(1)
	}

	if err := fetchServers(); err != nil {
		os.Exit(1)
	}

	if len(servers) == 0 {
		os.Exit(1)
	}

	if err := initRedis(); err != nil {
		os.Exit(1)
	}
	defer rdb.Close()

	// Check if command provided as CLI arguments
	if len(os.Args) > 1 {
		// Non-interactive mode: execute command from arguments
		command := strings.Join(os.Args[1:], " ")
		runCommandNonInteractive(command)
		return
	}

	// Interactive TUI mode
	// Load command history from Redis
	history, err := loadHistoryFromRedis()
	if err != nil {
		os.Exit(1)
	}

	ta := textarea.New()
	ta.ShowLineNumbers = false
	ta.SetHeight(1)
	ta.Cursor.Style = lipgloss.NewStyle().Foreground(lipgloss.Color("#90ee90"))
	ta.Cursor.SetChar("▂") // Lower quarter block as underline cursor
	ta.Focus()

	vp := viewport.New(0, 0) // Will be set by WindowSizeMsg
	vp.Style = lipgloss.NewStyle()

	p := tea.NewProgram(
		model{
			textarea:       ta,
			viewport:       vp,
			progress:       progress.New(progress.WithDefaultGradient()),
			output:         "",
			commandHistory: history,
			historyIndex:   0,
		},
		tea.WithAltScreen(),
	)

	if _, err := p.Run(); err != nil {
		os.Exit(1)
	}
}
