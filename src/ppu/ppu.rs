use crate::cartridge::Mirroring;

use super::register::{
    address::PPUAddr, controller::PPUCtrl, mask::PPUMask, scroll::PPUScroll, status::PPUStatus,
};

#[derive(Debug)]
struct PPU {
    chr_rom: Vec<u8>,        // 8 KB pattern mem (contains the sprites)
    vram: [u8; 2048],        // name table mem (layout of the background)
    palette_table: [u8; 32], // colors
    oam_addr: u8,
    oam_data: [u8; 256],
    mirroring: Mirroring,

    ctrl: PPUCtrl,
    mask: PPUMask,
    status: PPUStatus,
    scroll: PPUScroll,
    addr: PPUAddr,

    internal_data_buf: u8,
}

impl PPU {
    fn new(chr_rom: Vec<u8>, mirroring: Mirroring) -> Self {
        Self {
            chr_rom,
            palette_table: [0u8; 32],
            vram: [0u8; 2048],
            oam_addr: 0,
            oam_data: [0u8; 256],
            mirroring,
            ctrl: PPUCtrl::new(),
            mask: PPUMask::new(),
            status: PPUStatus::new(),
            scroll: PPUScroll::new(),
            addr: PPUAddr::new(),

            internal_data_buf: 0,
        }
    }

    fn write_to_ctrl(&mut self, data: u8) {
        self.ctrl.write(data);
    }

    fn write_to_mask(&mut self, data: u8) {
        self.mask.write(data);
    }

    fn read_status(&mut self) -> u8 {
        let data = self.status.read();
        self.addr.reset_latch();
        self.scroll.reset_latch();

        data
    }

    fn write_to_oam_addr(&mut self, value: u8) {
        self.oam_addr = value;
    }

    fn write_to_oam_data(&mut self, value: u8) {
        self.oam_data[self.oam_addr as usize] = value;
        self.oam_addr = self.oam_addr.wrapping_add(1);
    }

    fn read_oam_data(&self) -> u8 {
        self.oam_data[self.oam_addr as usize]
    }

    fn write_to_scroll(&mut self, data: u8) {
        self.scroll.write(data);
    }

    fn write_to_addr(&mut self, data: u8) {
        self.addr.write(data);
    }

    fn write_to_data(&mut self, value: u8) {
        let addr = self.addr.address();

        match addr {
            0..=0x1fff => println!("attempt to write to chr rom space {}", addr),
            0x2000..=0x2fff => {
                self.vram[self.mirror_vram_addr(addr) as usize] = value;
            }
            0x3000..=0x3eff => unimplemented!("addr {} shouldn't be used in reallity", addr),

            //Addresses $3F10/$3F14/$3F18/$3F1C are mirrors of $3F00/$3F04/$3F08/$3F0C
            0x3f10 | 0x3f14 | 0x3f18 | 0x3f1c => {
                let add_mirror = addr - 0x10;
                self.palette_table[(add_mirror - 0x3f00) as usize] = value;
            }
            0x3f00..=0x3fff => {
                self.palette_table[(addr - 0x3f00) as usize] = value;
            }
            _ => panic!("unexpected access to mirrored space {}", addr),
        }
        self.increment_vram_addr();
    }

    fn read_data(&mut self) -> u8 {
        let addr = self.addr.address();

        self.increment_vram_addr();

        match addr {
            0..=0x1fff => {
                let result = self.internal_data_buf;
                self.internal_data_buf = self.chr_rom[addr as usize];
                result
            }
            0x2000..=0x2fff => {
                let result = self.internal_data_buf;
                self.internal_data_buf = self.vram[self.mirror_vram_addr(addr) as usize];
                result
            }
            0x3000..=0x3eff => unimplemented!("addr {} shouldn't be used in reallity", addr),

            //Addresses $3F10/$3F14/$3F18/$3F1C are mirrors of $3F00/$3F04/$3F08/$3F0C
            0x3f10 | 0x3f14 | 0x3f18 | 0x3f1c => {
                let add_mirror = addr - 0x10;
                self.palette_table[(add_mirror - 0x3f00) as usize]
            }

            0x3f00..=0x3fff => self.palette_table[(addr - 0x3f00) as usize],
            _ => panic!("unexpected access to mirrored space {}", addr),
        }
    }

    pub fn mirror_vram_addr(&self, addr: u16) -> u16 {
        let mirrored_vram = addr & 0b10111111111111; // mirror down 0x3000-0x3eff to 0x2000 - 0x2eff
        let vram_index = mirrored_vram - 0x2000; // to vram vector
        let name_table = vram_index / 0x400;
        match (&self.mirroring, name_table) {
            (Mirroring::Vertical, 2) | (Mirroring::Vertical, 3) => vram_index - 0x800,
            (Mirroring::Horizontal, 2) => vram_index - 0x400,
            (Mirroring::Horizontal, 1) => vram_index - 0x400,
            (Mirroring::Horizontal, 3) => vram_index - 0x800,
            _ => vram_index,
        }
    }

    fn write_oam_dma(&mut self, data: &[u8; 256]) {
        for x in data.iter() {
            self.oam_data[self.oam_addr as usize] = *x;
            self.oam_addr = self.oam_addr.wrapping_add(1);
        }
    }

    fn increment_vram_addr(&mut self) {
        self.addr.increment(self.ctrl.vram_address_increment());
    }
}
