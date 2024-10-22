/// This register reports various status flags from the PPU, such as
/// whether the PPU is in VBlank, whether there was a sprite 0 hit, or
/// whether there is a sprite overflow.
///
/// PPUStatus Register (Status Register):
///
/// ```text
///  Bit  |  Function
///  -----|-----------------------------------------------
///    7  |  VBlank (Vertical Blank Occurrence): 1 = In VBlank, 0 = Not in VBlank
///       |  This bit is set when the PPU enters the VBlank period, and is cleared when the
///       |  CPU reads from the PPU status register.
///    6  |  Sprite 0 Hit: 1 = Sprite 0 overlaps with non-transparent background
///       |  Set when a non-transparent pixel of sprite 0 overlaps with a non-transparent
///       |  background pixel, typically used for collision detection.
///    5  |  Sprite Overflow: 1 = More than 8 sprites on a scanline
///       |  This bit is set when more than 8 sprites appear on a single scanline.
///  4-0  |  Unused (always return 0)
/// ```
///
/// ### Detailed Functionality:
/// - **VBlank (Bit 7):** This bit is set when the PPU enters the vertical blanking period,
///   which occurs at the end of the frame. It is cleared when the CPU reads from the PPUStatus
///   register. This allows the CPU to know when it can safely update PPU data.
///   
/// - **Sprite 0 Hit (Bit 6):** This bit is set when there is a pixel-level collision between
///   sprite 0 and the background on the current scanline. It's often used to trigger events
///   in games, such as determining when to scroll the screen.
///   
/// - **Sprite Overflow (Bit 5):** Set when more than 8 sprites are detected on a single scanline.
///   While the NES hardware only renders the first 8 sprites on a scanline, this bit allows the
///   program to know that more sprites are present, potentially used to handle custom overflow
///   behaviors or optimizations.
///
/// - **Bits 4-0:** These bits are unused and always return `0`.
///
/// The **PPUStatus** register is read-only from the CPU's perspective, and the
/// PPU clears the VBlank flag immediately after the CPU reads the register.
#[derive(Debug)]
pub struct PPUStatus {
    pub register: u8, // 8-bit status register
}

const VBLANK_BIT: u8 = 0b1000_0000; // Bit 7
const SPRITE_ZERO_HIT_BIT: u8 = 0b0100_0000; // Bit 6
const SPRITE_OVERFLOW_BIT: u8 = 0b0010_0000; // Bit 5

impl PPUStatus {
    pub fn new() -> Self {
        Self { register: 0 }
    }

    pub fn reset(&mut self) {
        self.register = 0;
    }

    /// Reads the PPUStatus register. This method will also clear the VBlank bit (bit 7).
    pub fn read(&mut self) -> u8 {
        let status = self.register;
        self.register &= !VBLANK_BIT; // Clear VBlank flag after reading
        status
    }

    /// Sets the VBlank flag (bit 7)
    pub fn set_vblank(&mut self) {
        self.register |= VBLANK_BIT;
    }

    /// Clears the VBlank flag (bit 7)
    pub fn clear_vblank(&mut self) {
        self.register &= !VBLANK_BIT;
    }

    /// Sets the Sprite 0 Hit flag (bit 6)
    pub fn set_sprite_zero_hit(&mut self) {
        self.register |= SPRITE_ZERO_HIT_BIT;
    }

    /// Clears the Sprite 0 Hit flag (bit 6)
    pub fn clear_sprite_zero_hit(&mut self) {
        self.register &= !SPRITE_ZERO_HIT_BIT;
    }

    /// Sets the Sprite Overflow flag (bit 5)
    pub fn set_sprite_overflow(&mut self) {
        self.register |= SPRITE_OVERFLOW_BIT;
    }

    /// Clears the Sprite Overflow flag (bit 5)
    pub fn clear_sprite_overflow(&mut self) {
        self.register &= !SPRITE_OVERFLOW_BIT;
    }

    /// Resets the PPUStatus for a new frame. Clears the Sprite 0 Hit and Sprite Overflow flags.
    pub fn reset_for_new_frame(&mut self) {
        self.clear_sprite_zero_hit();
        self.clear_sprite_overflow();
    }
}
