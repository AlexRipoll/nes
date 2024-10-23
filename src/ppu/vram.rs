use crate::cartridge::Mirroring;

const PALETTE_SIZE: usize = 0x20;

#[derive(Debug)]
pub struct Vram {
    nametables: [u8; 0x800],
    palettes_table: [u8; 0x20],
    mirroring: Mirroring,
    chr_rom: Vec<u8>,
    read_buffer: u8,
}

impl Vram {
    pub fn new(chr_rom: Vec<u8>, mirroring: Mirroring) -> Self {
        Self {
            nametables: [0u8; 0x800],
            palettes_table: [0u8; 0x20],
            mirroring,
            // TODO:
            chr_rom,
            read_buffer: 0,
        }
    }

    pub fn reset(&mut self) {
        self.nametables = [0xFF; 0x800];
        self.palettes_table = [0u8; 0x20];
        self.mirroring = Mirroring::Horizontal;
        self.chr_rom = Vec::new();
        self.read_buffer = 0;
    }

    pub fn write_byte(&mut self, address: u16, value: u8) {
        match address {
            0x0000..=0x1FFF => println!("attempt to write to chr rom space {}", address),
            0x2000..=0x2FFF => {
                self.nametables[self.mirror_nametable(address) as usize] = value;
            }
            0x3000..=0x3EFF => unimplemented!("addr {} shouldn't be used in reallity", address),

            //Addresses $3F10/$3F14/$3F18/$3F1C are mirrors of $3F00/$3F04/$3F08/$3F0C
            0x3F10 | 0x3F14 | 0x3F18 | 0x3F1C => {
                let add_mirror = address - 0x10;
                self.palettes_table[(add_mirror - 0x3F00) as usize] = value;
            }
            0x3F00..=0x3FFF => {
                self.palettes_table[self.mirror_palette(address)] = value;
            }
            _ => panic!("unexpected access to mirrored space {}", address),
        }
    }

    pub fn read_byte(&mut self, address: u16) -> u8 {
        match address {
            // TODO:
            // 0x0000..=0x1FFF => self.chr_rom[address as usize],
            0x0000..=0x1FFF => {
                println!("To be implemented");
                let result = self.read_buffer;
                self.read_buffer = self.chr_rom[address as usize];
                result
            }
            0x2000..=0x2FFF => self.nametables[self.mirror_nametable(address) as usize],
            0x3000..=0x3EFF => unimplemented!("address {} shouldn't be used in reallity", address),

            //Addresses $3F10/$3F14/$3F18/$3F1C are mirrors of $3F00/$3F04/$3F08/$3F0C
            0x3F10 | 0x3F14 | 0x3F18 | 0x3F1C => {
                let add_mirror = address - 0x10;
                self.palettes_table[(add_mirror - 0x3F00) as usize]
            }

            0x3F00..=0x3FFF => self.palettes_table[self.mirror_palette(address)],
            _ => panic!("unexpected access to mirrored space {}", address),
        }
    }

    pub fn buffered_read_byte(&mut self, address: u16) -> u8 {
        if address < 0x3F00 {
            let result = self.read_buffer;
            self.read_buffer = self.read_byte(address);
            result
        } else {
            self.read_buffer = self.nametables[self.mirror_nametable(address) as usize];
            self.read_byte(address)
        }
    }

    fn mirror_palette(&self, address: u16) -> usize {
        let address = (address as usize) % PALETTE_SIZE;

        match address {
            0x10 | 0x14 | 0x18 | 0x1C => address - 0x10,
            _ => address,
        }
    }

    pub fn mirror_nametable(&self, address: u16) -> u16 {
        let mirrored_vram = address & 0b10111111111111; // mirror down 0x3000-0x3eff to 0x2000 - 0x2eff
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
}

#[cfg(test)]
mod test {
    use crate::{cartridge::Mirroring, ppu::vram::Vram};

    #[test]
    fn test_read_byte_nametable() {
        let mut v = Vram::new(vec![0x01], Mirroring::Vertical);
        v.nametables[0x201] = 0x11;
        assert_eq!(v.read_byte(0x2201), 0x11);
        assert_eq!(v.read_byte(0x2200), 0);
    }

    #[test]
    fn test_write_byte_nametable() {
        let mut v = Vram::new(vec![0x01], Mirroring::Vertical);
        v.write_byte(0x2201, 0x11);
        assert_eq!(v.nametables[0x201], 0x11);
        assert_eq!(v.nametables[0x200], 0x00);
    }

    #[test]
    fn test_read_byte_palette() {
        let mut v = Vram::new(vec![0x01], Mirroring::Vertical);
        v.palettes_table[0x09] = 0x22;
        v.palettes_table[0] = 0x33;
        assert_eq!(v.read_byte(0x3F09), 0x22);
        assert_eq!(v.read_byte(0x3F00), 0x33);
        assert_eq!(v.read_byte(0x3F11), 0);
    }

    #[test]
    fn test_write_byte_palette() {
        let mut v = Vram::new(vec![0x01], Mirroring::Vertical);
        v.write_byte(0x3F09, 0x11);
        assert_eq!(v.palettes_table[0x09], 0x11);
    }

    #[test]
    fn test_buffered_read_byte() {
        let mut v = Vram::new(vec![0x01], Mirroring::Horizontal);
        v.nametables[0x201] = 0x11;
        v.nametables[0x202] = 0x12;
        assert_eq!(v.buffered_read_byte(0x2201), 0);
        assert_eq!(v.buffered_read_byte(0x2202), 0x11);
        assert_eq!(v.buffered_read_byte(0x2203), 0x12);
        assert_eq!(v.buffered_read_byte(0x2204), 0);
    }

    #[test]
    fn test_mirror_nametable_horizontally() {
        let v = Vram::new(vec![0x01], Mirroring::Horizontal);

        // Nametable 1 - starting at 0x2000
        assert_eq!(v.mirror_nametable(0x2001), 1);
        assert_eq!(v.mirror_nametable(0x2201), 0x201);
        assert_eq!(v.mirror_nametable(0x2401), 1);
        assert_eq!(v.mirror_nametable(0x2601), 0x201);

        // Nametable 1 - mirrored at 0x3000
        assert_eq!(v.mirror_nametable(0x3001), 1);
        assert_eq!(v.mirror_nametable(0x3201), 0x201);
        assert_eq!(v.mirror_nametable(0x3401), 1);
        assert_eq!(v.mirror_nametable(0x3601), 0x201);

        // Nametable 2 - starting at 0x2800
        assert_eq!(v.mirror_nametable(0x2801), 0x401);
        assert_eq!(v.mirror_nametable(0x2A01), 0x601);
        assert_eq!(v.mirror_nametable(0x2C01), 0x401);
        assert_eq!(v.mirror_nametable(0x2E01), 0x601);

        // Nametable 2 - mirrored at 0x3800
        assert_eq!(v.mirror_nametable(0x3801), 0x401);
        assert_eq!(v.mirror_nametable(0x3A01), 0x601);
        assert_eq!(v.mirror_nametable(0x3C01), 0x401);
        assert_eq!(v.mirror_nametable(0x3E01), 0x601);
    }

    #[test]
    fn test_mirror_nametable_vertically() {
        let v = Vram::new(vec![0x01], Mirroring::Vertical);

        // Nametable 1 - starting at 0x2000
        assert_eq!(v.mirror_nametable(0x2001), 1);
        assert_eq!(v.mirror_nametable(0x2201), 0x201);
        assert_eq!(v.mirror_nametable(0x2801), 1);
        assert_eq!(v.mirror_nametable(0x2A01), 0x201);

        // Nametable 1 - mirrored at 0x3000
        assert_eq!(v.mirror_nametable(0x3001), 1);
        assert_eq!(v.mirror_nametable(0x3201), 0x201);
        assert_eq!(v.mirror_nametable(0x3801), 1);
        assert_eq!(v.mirror_nametable(0x3A01), 0x201);

        // Nametable 2 - starting at 0x2400
        assert_eq!(v.mirror_nametable(0x2401), 0x401);
        assert_eq!(v.mirror_nametable(0x2601), 0x601);
        assert_eq!(v.mirror_nametable(0x2C01), 0x401);
        assert_eq!(v.mirror_nametable(0x2E01), 0x601);

        // Nametable 2 - mirrored at 0x3800
        assert_eq!(v.mirror_nametable(0x3401), 0x401);
        assert_eq!(v.mirror_nametable(0x3601), 0x601);
        assert_eq!(v.mirror_nametable(0x3C01), 0x401);
        assert_eq!(v.mirror_nametable(0x3E01), 0x601);
    }

    #[test]
    fn test_mirror_palette() {
        let v = Vram::new(vec![0x01], Mirroring::Horizontal);
        assert_eq!(v.mirror_palette(0x3F01), 1);
        assert_eq!(v.mirror_palette(0x3F21), 1);
        assert_eq!(v.mirror_palette(0x3F41), 1);
        assert_eq!(v.mirror_palette(0x3F11), 0x11);
        // Test mirroring of 0x10
        assert_eq!(v.mirror_palette(0x3F10), 0);
        assert_eq!(v.mirror_palette(0x3F30), 0);
        // Test mirroring of 0x14
        assert_eq!(v.mirror_palette(0x3F14), 4);
        assert_eq!(v.mirror_palette(0x3F34), 4);
        // Test mirroring of 0x18
        assert_eq!(v.mirror_palette(0x3F18), 8);
        assert_eq!(v.mirror_palette(0x3F38), 8);
        // Test mirroring of 0x1c
        assert_eq!(v.mirror_palette(0x3F1C), 0x0C);
        assert_eq!(v.mirror_palette(0x3F3C), 0x0C);
    }
}
