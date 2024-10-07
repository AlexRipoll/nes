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
}
