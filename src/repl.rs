use std::io::Write;
use std::io;

use termion::clear;
use termion::cursor;

#[derive(Default)]
pub struct NewCoolRepl {
    pub buffer: Vec<char>,
    pub buffer_cursor: usize,
    pub popup: Vec<String>,
    pub popup_cursor: usize,
}

impl NewCoolRepl {
    pub fn clear(&mut self) {
        self.buffer.clear();
        self.buffer_cursor = 0;
        self.popup.clear();
        self.popup_cursor = 0;
    }

    pub fn take(&mut self) -> String {
        let result = self.buffer.iter().collect();
        self.clear();
        result
    }

    pub fn insert_char(&mut self, x: char) {
        self.buffer.insert(self.buffer_cursor, x);
        self.buffer_cursor += 1;
    }

    pub fn backspace(&mut self) {
        if self.buffer_cursor > 0 {
            self.buffer.remove(self.buffer_cursor - 1);
            self.buffer_cursor -= 1;
        }
    }

    pub fn home(&mut self) {
        self.buffer_cursor = 0;
    }

    pub fn end(&mut self) {
        self.buffer_cursor = self.buffer.len();
    }

    pub fn up(&mut self) {
        if self.popup_cursor > 0 {
            self.popup_cursor -= 1
        }
    }

    pub fn down(&mut self) {
        if self.popup_cursor < self.popup.len() - 1 {
            self.popup_cursor += 1
        }
    }

    pub fn left_word(&mut self) {
        while self.buffer_cursor > 0 && self.buffer_cursor <= self.buffer.len() && !self.buffer.get(self.buffer_cursor - 1).unwrap().is_alphanumeric() {
            self.buffer_cursor -= 1;
        }
        while self.buffer_cursor > 0 && self.buffer_cursor <= self.buffer.len() && self.buffer.get(self.buffer_cursor - 1).unwrap().is_alphanumeric() {
            self.buffer_cursor -= 1;
        }
    }

    pub fn right_word(&mut self) {
        while self.buffer_cursor < self.buffer.len() && !self.buffer.get(self.buffer_cursor).unwrap().is_alphanumeric() {
            self.buffer_cursor += 1;
        }
        while self.buffer_cursor < self.buffer.len() && self.buffer.get(self.buffer_cursor).unwrap().is_alphanumeric() {
            self.buffer_cursor += 1;
        }
    }

    pub fn left_char(&mut self) {
        if self.buffer_cursor > 0 {
            self.buffer_cursor -= 1;
        }
    }

    pub fn right_char(&mut self) {
        if self.buffer_cursor < self.buffer.len() {
            self.buffer_cursor += 1;
        }
    }

    pub fn render(&self, prompt: &str, sink: &mut impl Write) -> io::Result<()> {
        const POPUP_SIZE: usize = 5;
        let buffer: String = self.buffer.iter().collect();
        write!(sink, "\r{}{}{}\r\n", clear::AfterCursor, prompt, &buffer)?;
        for (index, line) in self.popup.iter().take(POPUP_SIZE).enumerate() {
            if index == self.popup_cursor {
                write!(sink, ">")?
            } else {
                write!(sink, " ")?
            }
            write!(sink, " {}\r\n", line)?;
        }
        write!(sink, "{}{}",
               cursor::Up((POPUP_SIZE.min(self.popup.len()) + 1).try_into().unwrap()),
               cursor::Right((prompt.len() + self.buffer_cursor).try_into().unwrap()))?;
        Ok(())
    }
}
