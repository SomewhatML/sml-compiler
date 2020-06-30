use super::span::Span;
use std::fmt;

#[derive(Debug, Clone, PartialEq)]
pub enum Level {
    Warn,
    Error,
    Bug,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Annotation {
    pub span: Span,
    pub info: String,
}

#[derive(Clone, PartialEq)]
pub struct Diagnostic {
    pub level: Level,
    pub primary: Annotation,
    pub info: Vec<String>,
    pub other: Vec<Annotation>,
}

impl Annotation {
    pub fn new<S: Into<String>>(span: Span, message: S) -> Annotation {
        Annotation {
            span,
            info: message.into(),
        }
    }
}

impl Diagnostic {
    pub fn error<S: Into<String>>(span: Span, message: S) -> Diagnostic {
        Diagnostic {
            level: Level::Error,
            primary: Annotation::new(span, message),
            other: Vec::new(),
            info: Vec::new(),
        }
    }

    pub fn warn<S: Into<String>>(span: Span, message: S) -> Diagnostic {
        Diagnostic {
            level: Level::Warn,
            primary: Annotation::new(span, message),
            other: Vec::new(),
            info: Vec::new(),
        }
    }

    pub fn bug<S: Into<String>>(span: Span, message: S) -> Diagnostic {
        Diagnostic {
            level: Level::Bug,
            primary: Annotation::new(span, message),
            other: Vec::new(),
            info: Vec::new(),
        }
    }

    pub fn message<S: Into<String>>(mut self, span: Span, message: S) -> Diagnostic {
        self.other.push(Annotation::new(span, message));
        self
    }

    pub fn info<S: Into<String>>(mut self, info: S) -> Diagnostic {
        self.info.push(info.into());
        self
    }

    pub fn lines(&self) -> std::ops::Range<u16> {
        let mut range = std::ops::Range {
            start: self.primary.span.start.line,
            end: self.primary.span.end.line + 1,
        };

        for addl in &self.other {
            if addl.span.start.line < range.start {
                range.start = addl.span.start.line;
            }
            if addl.span.end.line + 1 > range.end {
                range.end = addl.span.end.line + 1;
            }
        }
        range
    }

    // pub fn code_format(src: &str, diag: Diagnostic) {
    //     // let lines = diag.ot
    //     //     .iter()
    //     //     .map(|(_, sp)| sp.start.line)
    //     //     .collect::<std::collections::HashSet<_>>();
    //     let srcl = src.lines().collect::<Vec<&str>>();

    //     let mut msgs = diag.other.clone();
    //     msgs.insert(0, diag.primary.clone());

    //     for line in diag.lines() {
    //         println!("| {} {}", line + 1, &srcl[line as usize]);
    //         for anno in &msgs {
    //             if anno.span.start.line != line {
    //                 continue;
    //             }
    //             let empty = (0..anno.span.start.col + 3).map(|_| ' ').collect::<String>();
    //             let tilde = (1..anno.span.end.col.saturating_sub(anno.span.start.col))
    //                 .map(|_| '~')
    //                 .collect::<String>();
    //             println!("{}^{}^ --- {}", empty, tilde, anno.info);
    //         }
    //     }
    // }

    pub fn report(mut self, source: &str) -> String {
        let lines = source.lines().collect::<Vec<&str>>();

        let mut output = format!("{:?}\n", self.level);
        self.other.insert(0, self.primary);
        for anno in self.other {
            if anno.span == Span::dummy() {
                output.push_str(&anno.info);
                output.push('\n');
            } else {
                let range = std::ops::Range {
                    start: anno.span.start.line.saturating_sub(1),
                    end: anno.span.end.line + 1,
                };
                let width = anno.span.end.line.to_string().len();
                for l in range {
                    output.push_str(&format!("{:>.*} | {}\n", width, l + 1, lines[l as usize]));
                    if l == anno.span.start.line {
                        let empty = (0..anno.span.start.col + 3 + width as u16)
                            .map(|_| ' ')
                            .collect::<String>();
                        let tilde = (1..anno.span.end.col.saturating_sub(anno.span.start.col))
                            .map(|_| '~')
                            .collect::<String>();
                        output.push_str(&format!("{}^{}^ {}\n", empty, tilde, anno.info))
                    }
                }
            }
        }
        output
    }
}

impl fmt::Debug for Diagnostic {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "\n{:?}: {} starting at line {}, col {}\n{}",
            self.level,
            self.primary.info,
            self.primary.span.start.line + 1,
            self.primary.span.start.col + 1,
            self.other
                .iter()
                .map(|a| a.info.clone())
                .collect::<Vec<_>>()
                .join("\n")
        )
    }
}
