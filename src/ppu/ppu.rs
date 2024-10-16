use crate::cartridge::Mirroring;

use super::register::{address::PPUAddr, controller::PPUCtrl};

#[derive(Debug)]
struct PPU {
    chr_rom: Vec<u8>,        // 8 KB pattern mem (contains the sprites)
    vram: [u8; 2048],        // name table mem (layout of the background)
    palette_table: [u8; 32], // colors
    oam_data: [u8; 256],
    mirroring: Mirroring,

    addr: PPUAddr,
    ctrl: PPUCtrl,
}

impl PPU {
    fn new(chr_rom: Vec<u8>, mirroring: Mirroring) -> Self {
        Self {
            chr_rom,
            palette_table: [0u8; 32],
            vram: [0u8; 2048],
            oam_data: [0u8; 256],
            mirroring,
            addr: PPUAddr::new(),
            ctrl: PPUCtrl::new(),
        }
    }
}
