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
    pub fn new_empty_rom() -> Self {
        Self::new(vec![0; 2048], Mirroring::Horizontal)
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

#[cfg(test)]
pub mod test {
    use super::*;

    #[test]
    fn test_ppu_vram_writes() {
        let mut ppu = PPU::new_empty_rom();
        ppu.write_to_addr(0x23);
        ppu.write_to_addr(0x05);
        ppu.write_to_data(0x66);

        assert_eq!(ppu.vram[0x0305], 0x66);
    }

    #[test]
    fn test_ppu_vram_reads() {
        let mut ppu = PPU::new_empty_rom();
        ppu.write_to_ctrl(0);
        ppu.vram[0x0305] = 0x66;

        ppu.write_to_addr(0x23);
        ppu.write_to_addr(0x05);

        ppu.read_data(); //load_into_buffer
        assert_eq!(ppu.addr.address(), 0x2306);
        assert_eq!(ppu.read_data(), 0x66);
    }

    #[test]
    fn test_ppu_vram_reads_cross_page() {
        let mut ppu = PPU::new_empty_rom();
        ppu.write_to_ctrl(0);
        ppu.vram[0x01ff] = 0x66;
        ppu.vram[0x0200] = 0x77;

        ppu.write_to_addr(0x21);
        ppu.write_to_addr(0xff);

        ppu.read_data(); //load_into_buffer
        assert_eq!(ppu.read_data(), 0x66);
        assert_eq!(ppu.read_data(), 0x77);
    }

    #[test]
    fn test_ppu_vram_reads_step_32() {
        let mut ppu = PPU::new_empty_rom();
        ppu.write_to_ctrl(0b100);
        ppu.vram[0x01ff] = 0x66;
        ppu.vram[0x01ff + 32] = 0x77;
        ppu.vram[0x01ff + 64] = 0x88;

        ppu.write_to_addr(0x21);
        ppu.write_to_addr(0xff);

        ppu.read_data(); //load_into_buffer
        assert_eq!(ppu.read_data(), 0x66);
        assert_eq!(ppu.read_data(), 0x77);
        assert_eq!(ppu.read_data(), 0x88);
    }

    // Horizontal: https://wiki.nesdev.com/w/index.php/Mirroring
    //   [0x2000 A ] [0x2400 a ]
    //   [0x2800 B ] [0x2C00 b ]
    #[test]
    fn test_vram_horizontal_mirror() {
        let mut ppu = PPU::new_empty_rom();
        ppu.write_to_addr(0x24);
        ppu.write_to_addr(0x05);

        ppu.write_to_data(0x66); //write to a

        ppu.write_to_addr(0x28);
        ppu.write_to_addr(0x05);

        ppu.write_to_data(0x77); //write to B

        ppu.write_to_addr(0x20);
        ppu.write_to_addr(0x05);

        ppu.read_data(); //load into buffer
        assert_eq!(ppu.read_data(), 0x66); //read from A

        ppu.write_to_addr(0x2C);
        ppu.write_to_addr(0x05);

        ppu.read_data(); //load into buffer
        assert_eq!(ppu.read_data(), 0x77); //read from b
    }

    // Vertical: https://wiki.nesdev.com/w/index.php/Mirroring
    //   [0x2000 A ] [0x2400 B ]
    //   [0x2800 a ] [0x2C00 b ]
    #[test]
    fn test_vram_vertical_mirror() {
        let mut ppu = PPU::new(vec![0; 2048], Mirroring::Vertical);

        ppu.write_to_addr(0x20);
        ppu.write_to_addr(0x05);

        ppu.write_to_data(0x66); //write to A

        ppu.write_to_addr(0x2C);
        ppu.write_to_addr(0x05);

        ppu.write_to_data(0x77); //write to b

        ppu.write_to_addr(0x28);
        ppu.write_to_addr(0x05);

        ppu.read_data(); //load into buffer
        assert_eq!(ppu.read_data(), 0x66); //read from a

        ppu.write_to_addr(0x24);
        ppu.write_to_addr(0x05);

        ppu.read_data(); //load into buffer
        assert_eq!(ppu.read_data(), 0x77); //read from B
    }

    #[test]
    fn test_read_status_resets_latch() {
        let mut ppu = PPU::new_empty_rom();
        ppu.vram[0x0305] = 0x66;

        ppu.write_to_addr(0x21);
        ppu.write_to_addr(0x23);
        ppu.write_to_addr(0x05);

        ppu.read_data(); //load_into_buffer
        assert_ne!(ppu.read_data(), 0x66);

        ppu.read_status();

        ppu.write_to_addr(0x23);
        ppu.write_to_addr(0x05);

        ppu.read_data(); //load_into_buffer
        assert_eq!(ppu.read_data(), 0x66);
    }

    #[test]
    fn test_ppu_vram_mirroring() {
        let mut ppu = PPU::new_empty_rom();
        ppu.write_to_ctrl(0);
        ppu.vram[0x0305] = 0x66;

        ppu.write_to_addr(0x63); //0x6305 -> 0x2305
        ppu.write_to_addr(0x05);

        ppu.read_data(); //load into_buffer
        assert_eq!(ppu.read_data(), 0x66);
        // assert_eq!(ppu.addr.read(), 0x0306)
    }

    #[test]
    fn test_read_status_resets_vblank() {
        let mut ppu = PPU::new_empty_rom();
        ppu.status.set_vblank();

        let status = ppu.read_status();

        assert_eq!(status >> 7, 1);
        assert_eq!(ppu.status.read() >> 7, 0);
    }

    #[test]
    fn test_oam_read_write() {
        let mut ppu = PPU::new_empty_rom();
        ppu.write_to_oam_addr(0x10);
        ppu.write_to_oam_data(0x66);
        ppu.write_to_oam_data(0x77);

        ppu.write_to_oam_addr(0x10);
        assert_eq!(ppu.read_oam_data(), 0x66);

        ppu.write_to_oam_addr(0x11);
        assert_eq!(ppu.read_oam_data(), 0x77);
    }

    #[test]
    fn test_oam_dma() {
        let mut ppu = PPU::new_empty_rom();

        let mut data = [0x66; 256];
        data[0] = 0x77;
        data[255] = 0x88;

        ppu.write_to_oam_addr(0x10);
        ppu.write_oam_dma(&data);

        ppu.write_to_oam_addr(0xf); //wrap around
        assert_eq!(ppu.read_oam_data(), 0x88);

        ppu.write_to_oam_addr(0x10);
        assert_eq!(ppu.read_oam_data(), 0x77);

        ppu.write_to_oam_addr(0x11);
        assert_eq!(ppu.read_oam_data(), 0x66);
    }
}
