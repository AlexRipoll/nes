// This register controls various important settings of the PPU, such as
/// the base address of the name tables, VRAM address increments, pattern table addresses,
/// sprite sizes, and Non-Maskable Interrupt (NMI) behavior.
///
/// PPUCtrl Register (Control Register 1):
///
/// ```text
///  Bit  |  Function
///  -----|-----------------------------------------------
///    7  |  NMI Enable (VBlank): 1 = Enable NMI on VBlank
///    6  |  PPU Master/Slave (not used on NES)
///    5  |  Sprite Size: 0 = 8x8 pixels, 1 = 8x16 pixels
///    4  |  Background Pattern Table Address: 0 = $0000, 1 = $1000
///    3  |  Sprite Pattern Table Address: 0 = $0000, 1 = $1000
///    2  |  VRAM Address Increment: 0 = add 1, 1 = add 32
///  1-0  |  Base Nametable Address:
///        |  00 = $2000 (Name Table 0)
///        |  01 = $2400 (Name Table 1)
///        |  10 = $2800 (Name Table 2)
///        |  11 = $2C00 (Name Table 3)
/// ```
/// read more: https://www.nesdev.org/wiki/PPU_registers#PPUCTRL
#[derive(Debug)]
pub struct PPUCtrl {
    register: u8,
}

impl PPUCtrl {
    pub fn new() -> Self {
        Self { register: 0 }
    }

    pub fn reset(&mut self) {
        self.register = 0;
    }

    pub fn write(&mut self, data: u8) {
        self.register = data;
    }

    /// Returns the base nametable address (bits 0 and 1).
    pub fn base_nametable_address(&self) -> u16 {
        match self.register & 0b00000011 {
            0b00 => 0x2000,
            0b01 => 0x2400,
            0b10 => 0x2800,
            0b11 => 0x2C00,
            _ => unreachable!(),
        }
    }

    /// Set the base nametable address (bits 0 and 1).
    pub fn set_base_nametable_address(&mut self, value: u16) {
        let bits = match value {
            0x2000 => 0b00,
            0x2400 => 0b01,
            0x2800 => 0b10,
            0x2C00 => 0b11,
            _ => panic!("Invalid nametable address"),
        };
        self.register = (self.register & 0b11111100) | bits;
    }

    /// Returns the VRAM address increment (bit 2).
    /// This determines how much the PPU address is incremented after a read/write operation:
    /// - 0: Increment by 1 (moving horizontally across the screen)
    /// - 1: Increment by 32 (moving vertically down the screen)
    pub fn vram_address_increment(&self) -> u8 {
        if self.register & 0b00000100 != 0 {
            32 // Increment by 32
        } else {
            1 // Increment by 1
        }
    }

    /// Sets the VRAM address increment (bit 2).
    /// Use 1 to increment horizontally, or 32 to increment vertically.
    pub fn set_vram_address_increment(&mut self, increment: u8) {
        match increment {
            32 => {
                self.register |= 0b00000100; // Set bit 2
            }
            1 => {
                self.register &= !0b00000100; // Clear bit 2
            }
            _ => panic!("Invalid increment value"),
        }
    }

    /// Returns the sprite pattern table address (for 8x8 sprites).
    /// This controls where the sprite pattern data is stored:
    /// - 0: Use pattern table at $0000
    /// - 1: Use pattern table at $1000
    pub fn sprite_pattern_table_address(&self) -> u16 {
        if self.register & 0b00001000 != 0 {
            0x1000
        } else {
            0x0000
        }
    }

    /// Sets the sprite pattern table address (bit 3).
    /// Use $0000 or $1000 for the sprite pattern table.
    pub fn set_sprite_pattern_table_address(&mut self, address: u16) {
        match address {
            0x1000 => self.register |= 0b00001000,  // Set bit 3
            0x0000 => self.register &= !0b00001000, // Clear bit 3
            _ => panic!("Invalid sprite pattern table address: {:#X}", address),
        }
    }

    /// Returns the background pattern table address (bit 4).
    /// This controls where the background pattern data is stored:
    /// - 0: Use pattern table at $0000
    /// - 1: Use pattern table at $1000
    pub fn background_pattern_table_address(&self) -> u16 {
        if self.register & 0b00010000 != 0 {
            0x1000
        } else {
            0x0000
        }
    }

    /// Sets the background pattern table address (bit 4).
    /// Use $0000 or $1000 for the background pattern table.
    pub fn set_background_pattern_table_address(&mut self, address: u16) {
        match address {
            0x1000 => self.register |= 0b00010000,  // Set bit 4
            0x0000 => self.register &= !0b00010000, // Clear bit 4
            _ => panic!("Invalid background pattern table address: {:#X}", address),
        }
    }

    /// Returns the sprite size (bit 5).
    /// This controls the size of the sprites:
    /// - 0: 8x8 pixels
    /// - 1: 8x16 pixels
    pub fn sprite_size(&self) -> u8 {
        if self.register & 0b00100000 != 0 {
            16
        } else {
            8
        }
    }

    /// Sets the sprite size (bit 5).
    /// Use 8 for 8x8 sprites, or 16 for 8x16 sprites.
    pub fn set_sprite_size(&mut self, size: u8) {
        match size {
            16 => self.register |= 0b00100000, // Set bit 5 for 16x16 sprites
            8 => self.register &= !0b00100000, // Clear bit 5 for 8x8 sprites
            _ => panic!("Invalid sprite size: {}", size),
        }
    }

    /// Returns true if NMI on VBlank is enabled (bit 7).
    /// - 0: Disable NMI
    /// - 1: Enable NMI on VBlank
    pub fn vblank_nmi_enabled(&self) -> bool {
        self.register & 0b10000000 != 0
    }

    /// Set the NMI on VBlank flag (bit 7).
    pub fn set_vblank_nmi(&mut self, enable: bool) {
        if enable {
            self.register |= 0b10000000; // Set bit 7
        } else {
            self.register &= !0b10000000; // Clear bit 7
        }
    }
}
