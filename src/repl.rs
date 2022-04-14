use std::io::Write;
use std::io;

use termion::clear;
use termion::cursor;

#[derive(Default)]
pub struct NewCoolRepl {
    pub buffer: Vec<char>,
    pub cursor: usize,
    pub popup: Vec<String>,
}

impl NewCoolRepl {
    pub fn clear(&mut self) {
        self.buffer.clear();
        self.cursor = 0;
    }

    pub fn take(&mut self) -> String {
        let result = self.buffer.iter().collect();
        self.clear();
        result
    }

    pub fn insert_char(&mut self, x: char) {
        self.buffer.insert(self.cursor, x);
        self.cursor += 1;
    }

    pub fn backspace(&mut self) {
        if self.cursor > 0 {
            self.buffer.remove(self.cursor - 1);
            self.cursor -= 1;
        }
    }

    pub fn home(&mut self) {
        self.cursor = 0;
    }

    pub fn end(&mut self) {
        self.cursor = self.buffer.len();
    }

    pub fn left_word(&mut self) {
        while self.cursor > 0 && self.cursor <= self.buffer.len() && !self.buffer.get(self.cursor - 1).unwrap().is_alphanumeric() {
            self.cursor -= 1;
        }
        while self.cursor > 0 && self.cursor <= self.buffer.len() && self.buffer.get(self.cursor - 1).unwrap().is_alphanumeric() {
            self.cursor -= 1;
        }
    }

    pub fn right_word(&mut self) {
        while self.cursor < self.buffer.len() && !self.buffer.get(self.cursor).unwrap().is_alphanumeric() {
            self.cursor += 1;
        }
        while self.cursor < self.buffer.len() && self.buffer.get(self.cursor).unwrap().is_alphanumeric() {
            self.cursor += 1;
        }
    }

    pub fn left_char(&mut self) {
        if self.cursor > 0 {
            self.cursor -= 1;
        }
    }

    pub fn right_char(&mut self) {
        if self.cursor < self.buffer.len() {
            self.cursor += 1;
        }
    }

    pub fn render(&self, prompt: &str, sink: &mut impl Write) -> io::Result<()> {
        const POPUP_SIZE: usize = 5;
        let buffer: String = self.buffer.iter().collect();
        write!(sink, "\r{}{}{}\r\n", clear::AfterCursor, prompt, &buffer)?;
        for line in self.popup.iter().take(POPUP_SIZE) {
            write!(sink, "{}\r\n", line)?;
        }
        write!(sink, "{}{}",
               cursor::Up((POPUP_SIZE.min(self.popup.len()) + 1).try_into().unwrap()),
               cursor::Right((prompt.len() + self.cursor).try_into().unwrap()))?;
        Ok(())
    }
}
