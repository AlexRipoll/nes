#[derive(Debug)]
pub struct PPUScroll {
    pub scroll_x: u8,
    pub scroll_y: u8,
    pub latch: bool,
}

impl PPUScroll {
    pub fn new() -> Self {
        Self {
            scroll_x: 0,
            scroll_y: 0,
            latch: false,
        }
    }

    pub fn write(&mut self, data: u8) {
        if !self.latch {
            self.scroll_x = data;
        } else {
            self.scroll_y = data;
        }
        self.latch = !self.latch;
    }

    pub fn reset_latch(&mut self) {
        self.latch = false;
    }
}
