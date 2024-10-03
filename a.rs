use std::collections::HashMap;
use std::fs::File;
use std::io::{self, BufRead, BufReader};

pub fn parse_sysctl_conf(filename: &str) -> io::Result<HashMap<String, String>> {
    let file = File::open(filename)?;
    let reader = BufReader::new(file);

    let mut result = HashMap::new();
    let mut current_line = String::new();
    let mut lines = reader.lines();

    while let Some(line) = lines.next() {
        let line = line?;
        let mut trimmed_line = line.trim_end().to_string();

        // 行継続記号の処理
        let line_continues = trimmed_line.ends_with('\\');
        if line_continues {
            trimmed_line.pop(); // バックスラッシュを削除
        }

        current_line.push_str(trimmed_line.trim_start());

        if line_continues {
            current_line.push('\n');
            continue;
        }

        // コメントの除去（クオート外のコメントのみ）
        current_line = remove_inline_comments(&current_line);

        // 空行のスキップ
        if current_line.trim().is_empty() {
            current_line.clear();
            continue;
        }

        // キーと値の分割
        let index = current_line.find('=');
        if index.is_none() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                format!("無効な行: {}", current_line),
            ));
        }
        let index = index.unwrap();
        let key = current_line[..index].trim().to_string();
        let mut value = current_line[index + 1..].trim().to_string();

        // クオートされた値の処理
        if is_quoted(&value) {
            let quote_char = value.chars().next().unwrap();
            if !value.ends_with(quote_char) || value.len() == 1 {
                // 複数行のクオート値
                value = value[1..].to_string(); // 開始クオートを削除
                loop {
                    if let Some(line) = lines.next() {
                        let next_line = line?;
                        let mut next_trimmed = next_line.trim_end().to_string();

                        // 行継続記号の処理
                        let next_line_continues = next_trimmed.ends_with('\\');
                        if next_line_continues {
                            next_trimmed.pop(); // バックスラッシュを削除
                        }

                        value.push('\n');
                        value.push_str(next_trimmed.trim_start());

                        if next_line_continues {
                            continue;
                        }

                        if next_trimmed.ends_with(quote_char) {
                            // 終了クオートを削除
                            value = value[..value.len() - 1].to_string();
                            break;
                        }
                    } else {
                        return Err(io::Error::new(
                            io::ErrorKind::InvalidData,
                            "クオートが閉じられていません",
                        ));
                    }
                }
            } else {
                // 一行のクオート値
                value = value[1..value.len() - 1].to_string();
            }
        } else {
            // クオートされていない値のコメント除去
            if let Some(comment_index) = value.find('#') {
                value = value[..comment_index].trim_end().to_string();
            }
        }

        result.insert(key, value);
        current_line.clear();
    }

    Ok(result)
}

// クオートされているかを判定するヘルパー関数
fn is_quoted(s: &str) -> bool {
    let chars: Vec<char> = s.chars().collect();
    if chars.is_empty() {
        return false;
    }
    (chars[0] == '"' || chars[0] == '\'') && (chars.len() == 1 || chars[chars.len() - 1] != chars[0])
        || (chars[0] == '"' && chars[chars.len() - 1] == '"')
        || (chars[0] == '\'' && chars[chars.len() - 1] == '\'')
}

// クオート外のインラインコメントを除去するヘルパー関数
fn remove_inline_comments(s: &str) -> String {
    let mut result = String::new();
    let mut in_single_quote = false;
    let mut in_double_quote = false;
    let mut chars = s.chars().peekable();

    while let Some(c) = chars.next() {
        if c == '\'' && !in_double_quote {
            in_single_quote = !in_single_quote;
        } else if c == '"' && !in_single_quote {
            in_double_quote = !in_double_quote;
        } else if c == '#' && !in_single_quote && !in_double_quote {
            // コメントを無視
            break;
        }
        result.push(c);
    }

    result
}