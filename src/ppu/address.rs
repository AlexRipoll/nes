#[derive(Debug)]
pub struct PPUAddr {
    address: u16,
    latch: bool,
}

impl PPUAddr {
    pub fn new() -> Self {
        Self {
            address: 0,
            latch: false,
        }
    }
    /// Writes a byte to the PPUAddr register.
    /// Alternates between setting the high byte and low byte.
    pub fn write(&mut self, data: u8) {
        if !self.latch {
            // First write: set high byte (upper 7 bits, bits 8-14)
            // Preserve lower 8 bits and update upper bits
            self.address = (self.address & 0x00FF) | ((data as u16 & 0x3F) << 8);
        } else {
            // Second write: set low byte (bits 0-7)
            // Preserve upper 7 bits and update lower bits
            self.address = (self.address & 0x7F00) | data as u16;
        }
        self.latch = !self.latch;
    }

    /// Returns the current 15-bit VRAM (name table) address.
    pub fn vram_address(&self) -> u16 {
        // Mask to ensure 15-bit VRAM address
        self.address & 0x3FFF
    }

    /// Increments the VRAM address by a given value (for example, 1 or 32).
    /// The address wraps around to 15 bits (VRAM address space).
    pub fn increment(&mut self, increment_value: u8) {
        self.address = self.address.wrapping_add(increment_value as u16) & 0x3FFF;
        // Wraps around the 15-bit space
    }

    pub fn reset_latch(&mut self) {
        self.latch = false;
    }
}
