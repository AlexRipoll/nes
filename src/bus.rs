use std::usize;

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
}

impl Bus {
    pub fn new() -> Self {
        Bus {
            cpu_vram: [0; 2048],
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
    use crate::bus::Bus;

    #[test]
    fn test_mem_read() {
        let mut bus = Bus::new();
        bus.cpu_vram[0x12] = 100;
        assert_eq!(bus.mem_read(0x12), 100);
    }

    #[test]
    fn test_mem_write() {
        let mut bus = Bus::new();
        bus.mem_write(0x12, 100);
        assert_eq!(bus.cpu_vram[0x12], 100);
    }

    #[test]
    fn test_mem_read_u16() {
        let mut bus = Bus::new();
        bus.cpu_vram[0xab] = 0x10;
        bus.cpu_vram[0xac] = 0x11;
        assert_eq!(bus.mem_read_u16(0xab), 0x1110);
    }

    #[test]
    fn test_mem_write_u16() {
        let mut bus = Bus::new();
        bus.mem_write_u16(0xab, 0x10ab);
        assert_eq!(bus.cpu_vram[0xab], 0xab);
        assert_eq!(bus.cpu_vram[0xac], 0x10);
    }
}
