use std::usize;

use crate::cartridge::Rom;

// Represents the start address of the RAM region in the memory map.
const RAM_START_ADDRESS: u16 = 0x0000;
// Represents the end address of the mirrored RAM region in the memory map.
const RAM_MIRRORS_END_ADDRESS: u16 = 0x1FFF;
// Represents the start address of the PPU (Picture Processing Unit) registers.
const PPU_REGISTERS_START_ADDRESS: u16 = 0x2000;
// Represents the end address of the mirrored PPU registers in the memory map.
const PPU_REGISTERS_MIRRORS_END_ADDRESS: u16 = 0x3FFF;

#[derive(Debug)]
pub struct Bus {
    cpu_vram: [u8; 2048],
    rom: Rom,
}

impl Bus {
    pub fn new(rom: Rom) -> Self {
        Bus {
            cpu_vram: [0; 2048],
            rom,
        }
    }

    pub fn mem_read(&self, address: u16) -> u8 {
        match address {
            RAM_START_ADDRESS..=RAM_MIRRORS_END_ADDRESS => {
                let masked_address = address & 0b00000111_11111111;
                self.cpu_vram[masked_address as usize]
            }
            PPU_REGISTERS_START_ADDRESS..=PPU_REGISTERS_MIRRORS_END_ADDRESS => {
                let masked_address = address & 0b00100000_00000111;
                unimplemented!()
            }
            _ => {
                println!("Ignoring mem access at {:X}", address);
                0
            }
        }
    }

    pub fn mem_write(&mut self, address: u16, data: u8) {
        match address {
            RAM_START_ADDRESS..=RAM_MIRRORS_END_ADDRESS => {
                let masked_address = address & 0b00000111_11111111;
                self.cpu_vram[masked_address as usize] = data;
            }
            PPU_REGISTERS_START_ADDRESS..=PPU_REGISTERS_MIRRORS_END_ADDRESS => {
                let masked_address = address & 0b00100000_00000111;
                unimplemented!()
            }
            _ => {
                println!("Ignoring mem write-access at {:X}", address);
            }
        }
    }

    /// Reads two bytes from memory at the specified `address`, returning a 16-bit value.
    /// This is little-endian, meaning the least significant byte is read first.
    pub fn mem_read_u16(&self, address: u16) -> u16 {
        let lsb = self.mem_read(address) as u16;
        let msb = self.mem_read(address + 1) as u16;
        (msb << 8) | (lsb as u16)
    }

    /// Writes a 16-bit value to memory at the specified `address`.
    pub fn mem_write_u16(&mut self, address: u16, data: u16) {
        let msb = (data >> 8) as u8;
        let lsb = (data & 0xff) as u8;
        self.mem_write(address, lsb);
        self.mem_write(address + 1, msb);
    }
}

#[cfg(test)]
mod test {
    use crate::{
        bus::Bus,
        cartridge::{Rom, CHR_ROM_8KB_UNITS, PRG_ROM_16KB_UNITS},
    };

    fn rom_init() -> Rom {
        let mut raw_rom_data = vec![
            0x4E,
            0x45,
            0x53,
            0x1A,        // iNES header
            0x01,        // 1 unit of 16KB PRG ROM
            0x01,        // 1 unit of 8KB CHR ROM
            0b0000_0001, // Mirroring = Vertical, no trainer
            0b0000_0000, // Mapper info
            0x00,
            0x00,
            0x00,
            0x00, // Padding (not used for these tests)
            0x00, // Padding (not used for these tests)
            0x00, // Padding (not used for these tests)
            0x00, // Padding (not used for these tests)
            0x00, // Padding (not used for these tests)
        ];
        raw_rom_data.extend(vec![0xFF; PRG_ROM_16KB_UNITS]); // 16KB PRG ROM filled with 0xFF
        raw_rom_data.extend(vec![0xFF; CHR_ROM_8KB_UNITS]); // 8KB CHR ROM filled with 0xFF

        Rom::new(raw_rom_data).unwrap()
    }

    #[test]
    fn test_mem_read() {
        let rom = rom_init();
        let mut bus = Bus::new(rom);
        bus.cpu_vram[0x12] = 100;
        assert_eq!(bus.mem_read(0x12), 100);
    }

    #[test]
    fn test_mem_write() {
        let rom = rom_init();
        let mut bus = Bus::new(rom);
        bus.mem_write(0x12, 100);
        assert_eq!(bus.cpu_vram[0x12], 100);
    }

    #[test]
    fn test_mem_read_u16() {
        let rom = rom_init();
        let mut bus = Bus::new(rom);
        bus.cpu_vram[0xab] = 0x10;
        bus.cpu_vram[0xac] = 0x11;
        assert_eq!(bus.mem_read_u16(0xab), 0x1110);
    }

    #[test]
    fn test_mem_write_u16() {
        let rom = rom_init();
        let mut bus = Bus::new(rom);
        bus.mem_write_u16(0xab, 0x10ab);
        assert_eq!(bus.cpu_vram[0xab], 0xab);
        assert_eq!(bus.cpu_vram[0xac], 0x10);
    }
}
