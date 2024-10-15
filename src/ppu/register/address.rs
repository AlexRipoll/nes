#[derive(Debug)]
struct PPUAddr {
    address: u16,
    latch: bool,
}

impl PPUAddr {
    /// Writes a byte to the PPUAddr register.
    /// Alternates between setting the high byte and low byte.
    fn write(&mut self, data: u8) {
        if !self.latch {
            // First write: set high byte (upper 7 bits, bits 8-14)
            // Preserve lower 8 bits and update upper bits
            self.address = (self.address & 0x00FF) | ((data as u16 & 0x3F) << 8);
            self.latch = true;
        } else {
            // Second write: set low byte (bits 0-7)
            // Preserve upper 7 bits and update lower bits
            self.address = (self.address & 0x7F00) | data as u16;
            self.latch = false;
        }
    }

    /// Returns the current 15-bit VRAM address.
    pub fn address(&self) -> u16 {
        // Mask to ensure 15-bit VRAM address
        self.address & 0x3FFF
    }

    /// Increments the VRAM address by a given value (for example, 1 or 32).
    /// The address wraps around to 15 bits (VRAM address space).
    pub fn increment(&mut self, increment_value: u16) {
        self.address = (self.address + increment_value) & 0x3FFF; // Wraps around the 15-bit space
    }
}
