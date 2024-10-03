package configparser

import (
"bufio"
"fmt"
"io"
"os"
"strconv"
"strings"
)

type ConfigMap map[string]interface{}

// ParseConfigFile reads a file with sysctl.conf-like syntax and returns a nested map structure
func ParseConfigFile(filename string) (ConfigMap, error) {
file, err := os.Open(filename)
if err != nil {
return nil, fmt.Errorf("error opening file: %w", err)
}
defer file.Close()

return ParseConfigReader(file)
}

// ParseConfigReader reads from an io.Reader with sysctl.conf-like syntax and returns a nested map structure
func ParseConfigReader(reader io.Reader) (ConfigMap, error) {
scanner := bufio.NewScanner(reader)
result := make(ConfigMap)

for scanner.Scan() {
line := strings.TrimSpace(scanner.Text())

// Skip empty lines and comments
if line == "" || strings.HasPrefix(line, "#") {
continue
}

// Split the line into key and value
parts := strings.SplitN(line, "=", 2)
if len(parts) != 2 {
return nil, fmt.Errorf("invalid line format: %s", line)
}

key := strings.TrimSpace(parts[0])
value := strings.TrimSpace(parts[1])

// Remove quotes if present
value = strings.Trim(value, "\"'")

// Parse the value
var parsedValue interface{}
if strings.ToLower(value) == "true" {
parsedValue = true
} else if strings.ToLower(value) == "false" {
parsedValue = false
} else if i, err := strconv.Atoi(value); err == nil {
parsedValue = i
} else if f, err := strconv.ParseFloat(value, 64); err == nil {
parsedValue = f
} else {
parsedValue = value
}

// Set the value in the nested structure
setNestedValue(result, strings.Split(key, "."), parsedValue)
}

if err := scanner.Err(); err != nil {
return nil, fmt.Errorf("error reading file: %w", err)
}

return result, nil
}

// setNestedValue sets a value in a nested map structure
func setNestedValue(config ConfigMap, keys []string, value interface{}) {
if len(keys) == 1 {
config[keys[0]] = value
return
}

if _, ok := config[keys[0]]; !ok {
config[keys[0]] = make(ConfigMap)
}

subConfig, ok := config[keys[0]].(ConfigMap)
if !ok {
subConfig = make(ConfigMap)
config[keys[0]] = subConfig
}

setNestedValue(subConfig, keys[1:], value)
}package sysctlconf

import (
    "bufio"
    "fmt"
    "os"
    "strings"
)

func ParseSysctlConf(filename string) (map[string]string, error) {
    file, err := os.Open(filename)
    if err != nil {
        return nil, err
    }
    defer file.Close()

    scanner := bufio.NewScanner(file)
    result := make(map[string]string)
    var currentLine string

    for scanner.Scan() {
        line := scanner.Text()

        lineContinues := strings.HasSuffix(line, "\\")
        if lineContinues {
            line = strings.TrimSuffix(line, "\\")
        }

        currentLine += line

        if lineContinues {
            continue
        }

        currentLine = removeInlineComments(currentLine)

        // Skip empty lines
        if strings.TrimSpace(currentLine) == "" {
            currentLine = ""
            continue
        }

        // Parse the line into key and value
        index := strings.Index(currentLine, "=")
        if index == -1 {
            return nil, fmt.Errorf("無効な行: %s", currentLine)
        }

        key := strings.TrimSpace(currentLine[:index])
        value := strings.TrimSpace(currentLine[index+1:])

        if isQuoted(value) {
            quoteChar := value[0]
            if value[len(value)-1] != quoteChar {

                value = value[1:] 
                for {
                    if scanner.Scan() {
                        nextLine := scanner.Text()
                        lineContinues := strings.HasSuffix(nextLine, "\\")
                        if lineContinues {
                            nextLine = strings.TrimSuffix(nextLine, "\\")
                        }

                        value += "\n" + nextLine

                        if lineContinues {
                            continue
                        }

                        if strings.HasSuffix(strings.TrimSpace(nextLine), string(quoteChar)) {
                            // Remove trailing quote
                            value = value[:len(value)-1]
                            break
                        }
                    } else {
                        return nil, fmt.Errorf("クオートが閉じられていません")
                    }
                }
            } else {

                value = value[1 : len(value)-1]
            }
        } else {

            value = strings.SplitN(value, "#", 2)[0]
            value = strings.TrimSpace(value)
        }

        result[key] = value
        currentLine = ""
    }

    if err := scanner.Err(); err != nil {
        return nil, err
    }

    return result, nil
}


func isQuoted(s string) bool {
    return (strings.HasPrefix(s, "\"") && strings.HasSuffix(s, "\"")) ||
        (strings.HasPrefix(s, "'") && strings.HasSuffix(s, "'")) ||
        (strings.HasPrefix(s, "\"") && !strings.HasSuffix(s, "\"")) ||
        (strings.HasPrefix(s, "'") && !strings.HasSuffix(s, "'"))
}


func removeInlineComments(s string) string {
    var result strings.Builder
    inSingleQuote := false
    inDoubleQuote := false

    for i := 0; i < len(s); i++ {
        char := s[i]
        if char == '\'' && !inDoubleQuote {
            inSingleQuote = !inSingleQuote
        } else if char == '"' && !inSingleQuote {
            inDoubleQuote = !inDoubleQuote
        }

        if char == '#' && !inSingleQuote && !inDoubleQuote {
            break
        }

        result.WriteByte(char)
    }

    return result.String()
}