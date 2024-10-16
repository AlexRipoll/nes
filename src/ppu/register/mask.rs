/// This register controls various aspects of how the Picture Processing Unit (PPU)
/// renders the background, sprites, and colors on the screen.
///
/// PPUMask Register (Mask Register):
///
/// ```text
///  Bit  |  Function
///  -----|-----------------------------------------------
///    7  |  Emphasize Blue: 1 = Emphasize blue color component
///    6  |  Emphasize Green: 1 = Emphasize green color component
///    5  |  Emphasize Red: 1 = Emphasize red color component
///    4  |  Show Sprites in Leftmost 8 Pixels: 1 = Show sprites
///    3  |  Show Background in Leftmost 8 Pixels: 1 = Show background
///    2  |  Show Sprites: 1 = Enable sprite rendering
///    1  |  Show Background: 1 = Enable background rendering
///    0  |  Grayscale Mode: 1 = Render in grayscale (ignore color)
/// ```
///
/// ### Detailed Explanation of Each Bit:
/// - **Bit 7 (Emphasize Blue)**:
///   - When set, emphasizes the blue color component in the video output.
///   - This can be used to create visual effects where the blue component is boosted.
///
/// - **Bit 6 (Emphasize Green)**:
///   - When set, emphasizes the green color component in the video output.
///   - Like the blue emphasis, this is used to adjust or boost the green component for effects.
///
/// - **Bit 5 (Emphasize Red)**:
///   - When set, emphasizes the red color component in the video output.
///   - Can be combined with other color emphasis bits for various visual effects.
///
/// - **Bit 4 (Show Sprites in Leftmost 8 Pixels)**:
///   - When set, sprites will be rendered in the leftmost 8 pixels of the screen.
///   - If clear, sprites are hidden in this area of the screen (useful for certain visual tricks).
///
/// - **Bit 3 (Show Background in Leftmost 8 Pixels)**:
///   - When set, the background will be rendered in the leftmost 8 pixels of the screen.
///   - If clear, the background is hidden in the leftmost 8 pixels (can be used to hide UI elements).
///
/// - **Bit 2 (Show Sprites)**:
///   - When set, enables rendering of sprites on the screen.
///   - When clear, sprites are disabled and will not appear.
///
/// - **Bit 1 (Show Background)**:
///   - When set, enables rendering of the background tiles on the screen.
///   - When clear, the background will not be displayed.
///
/// - **Bit 0 (Grayscale Mode)**:
///   - When set, renders the entire screen in grayscale, ignoring color information.
///   - This can be useful for debug purposes or visual effects where only brightness is needed.
#[derive(Debug)]
pub struct PPUMask {
    register: u8,
}

impl PPUMask {
    pub fn new() -> Self {
        Self { register: 0 }
    }

    pub fn write(&mut self, data: u8) {
        self.register = data;
    }

    /// Bit 0: Greyscale mode
    /// - 0: Normal color rendering
    /// - 1: Greyscale rendering (the screen is rendered in shades of grey)
    /// Sets or clears the grayscale mode.
    pub fn set_grayscale(&mut self, enabled: bool) {
        if enabled {
            self.register |= 0b00000001; // Set bit 0
        } else {
            self.register &= !0b00000001; // Clear bit 0
        }
    }

    /// Returns whether the PPU is currently in grayscale mode.
    pub fn is_grayscale(&self) -> bool {
        self.register & 0b00000001 != 0 // Check if bit 0 is set
    }

    /// Bit 1: Show background
    /// - 0: Do not render background
    /// - 1: Render background
    /// Controls whether the background is rendered on the screen.
    pub fn set_show_background(&mut self, enabled: bool) {
        if enabled {
            self.register |= 0b00000010; // Set bit 1
        } else {
            self.register &= !0b00000010; // Clear bit 1
        }
    }

    /// Returns whether the background is currently being rendered.
    pub fn is_showing_background(&self) -> bool {
        self.register & 0b00000010 != 0 // Check if bit 1 is set
    }

    /// Bit 2: Show sprites
    /// - 0: Do not render sprites
    /// - 1: Render sprites
    /// Controls whether sprites are rendered on the screen.
    pub fn set_show_sprites(&mut self, enabled: bool) {
        if enabled {
            self.register |= 0b00000100; // Set bit 2
        } else {
            self.register &= !0b00000100; // Clear bit 2
        }
    }

    /// Returns whether sprites are currently being rendered.
    pub fn is_showing_sprites(&self) -> bool {
        self.register & 0b00000100 != 0 // Check if bit 2 is set
    }

    /// Bit 3: Show background in the leftmost 8 pixels of the screen
    /// - 0: Do not render the background in the leftmost 8 pixels
    /// - 1: Render the background in the leftmost 8 pixels
    /// Controls whether the background is rendered in the leftmost 8 pixels of the screen.
    pub fn set_show_background_left(&mut self, enabled: bool) {
        if enabled {
            self.register |= 0b00001000; // Set bit 3
        } else {
            self.register &= !0b00001000; // Clear bit 3
        }
    }

    /// Returns whether the background is being rendered in the leftmost 8 pixels.
    pub fn is_showing_background_left(&self) -> bool {
        self.register & 0b00001000 != 0 // Check if bit 3 is set
    }

    /// Bit 4: Show sprites in the leftmost 8 pixels of the screen
    /// - 0: Do not render sprites in the leftmost 8 pixels
    /// - 1: Render sprites in the leftmost 8 pixels
    /// Controls whether sprites are rendered in the leftmost 8 pixels of the screen.
    pub fn set_show_sprites_left(&mut self, enabled: bool) {
        if enabled {
            self.register |= 0b00010000; // Set bit 4
        } else {
            self.register &= !0b00010000; // Clear bit 4
        }
    }

    /// Returns whether sprites are being rendered in the leftmost 8 pixels.
    pub fn is_showing_sprites_left(&self) -> bool {
        self.register & 0b00010000 != 0 // Check if bit 4 is set
    }

    /// Bit 5: Emphasize red
    /// - 0: Normal color rendering
    /// - 1: Emphasize red color component
    /// When set, this bit emphasizes the red color component in the rendered output.
    pub fn set_emphasize_red(&mut self, enabled: bool) {
        if enabled {
            self.register |= 0b00100000; // Set bit 5
        } else {
            self.register &= !0b00100000; // Clear bit 5
        }
    }

    /// Returns whether the red color component is emphasized.
    pub fn is_emphasizing_red(&self) -> bool {
        self.register & 0b00100000 != 0 // Check if bit 5 is set
    }

    /// Bit 6: Emphasize green
    /// - 0: Normal color rendering
    /// - 1: Emphasize green color component
    /// When set, this bit emphasizes the green color component in the rendered output.
    pub fn set_emphasize_green(&mut self, enabled: bool) {
        if enabled {
            self.register |= 0b01000000; // Set bit 6
        } else {
            self.register &= !0b01000000; // Clear bit 6
        }
    }

    /// Returns whether the green color component is emphasized.
    pub fn is_emphasizing_green(&self) -> bool {
        self.register & 0b01000000 != 0 // Check if bit 6 is set
    }

    /// Bit 7: Emphasize blue
    /// - 0: Normal color rendering
    /// - 1: Emphasize blue color component
    /// When set, this bit emphasizes the blue color component in the rendered output.
    pub fn set_emphasize_blue(&mut self, enabled: bool) {
        if enabled {
            self.register |= 0b10000000; // Set bit 7
        } else {
            self.register &= !0b10000000; // Clear bit 7
        }
    }

    /// Returns whether the blue color component is emphasized.
    pub fn is_emphasizing_blue(&self) -> bool {
        self.register & 0b10000000 != 0 // Check if bit 7 is set
    }
}
