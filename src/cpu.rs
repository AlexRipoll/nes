#[derive(Debug)]
struct CPU {
    register_a: u8,
    register_x: u8,
    register_y: u8,
    status: u8,
    program_counter: u16,
    memory: [u8; 0xFFFF],
}

#[derive(Debug)]
#[allow(non_camel_case_types)]
pub enum AddressingMode {
    Immediate,
    ZeroPage,
    ZeroPage_X,
    ZeroPage_Y,
    Absolute,
    Absolute_X,
    Absolute_Y,
    Indirect,
    Indirect_X,
    Indirect_Y,
    NoneAddressing,
}

impl CPU {
    fn new() -> Self {
        CPU {
            register_a: 0,
            register_x: 0,
            register_y: 0,
            status: 0,
            program_counter: 0,
            memory: [0u8; 0xFFFF],
        }
    }

    fn mem_read(&self, address: u16) -> u8 {
        self.memory[address as usize]
    }

    fn mem_write(&mut self, address: u16, data: u8) {
        self.memory[address as usize] = data;
    }

    fn mem_read_u16(&self, address: u16) -> u16 {
        let lo = self.mem_read(address) as u16;
        let hi = self.mem_read(address + 1) as u16;
        (hi << 8) | (lo as u16)
    }

    fn mem_write_u16(&mut self, address: u16, data: u16) {
        let le_bytes = data.to_le_bytes();
        self.memory[address as usize..=address as usize + 1].copy_from_slice(&le_bytes);
    }

    fn load(&mut self, program: Vec<u8>) {
        self.memory[0x8000..(0x8000 + program.len())].copy_from_slice(&program);
        self.mem_write_u16(0xFFFC, 0x8000);
    }

    fn reset(&mut self) {
        self.register_a = 0;
        self.register_x = 0;
        self.status = 0;

        self.program_counter = self.mem_read_u16(0xFFFC);
    }

    fn run(&mut self, program: Vec<u8>) {
        self.load(program);
        self.reset();
        self.interpret();
    }

    pub fn interpret(&mut self) {
        loop {
            let opcode = self.mem_read(self.program_counter);
            self.program_counter += 1;

            match opcode {
                0xA9 => {
                    self.lda(&AddressingMode::Immediate);
                    self.program_counter += 1;
                }
                0xAA => {
                    self.register_x = self.register_a;

                    self.set_zero_and_negative_flags(self.register_x);
                }
                0xE8 => {
                    self.register_x = self.register_x.wrapping_add(1);

                    self.set_zero_and_negative_flags(self.register_x);
                }
                0x00 => {
                    return;
                }
                _ => todo!(),
            }
        }
    }

    /// Read bout Addressing Modes implementations: https://www.nesdev.org/obelisk-6502-guide/addressing.html
    fn operand_address(&self, mode: &AddressingMode) -> u16 {
        match mode {
            AddressingMode::Immediate => self.program_counter,
            AddressingMode::ZeroPage => self.mem_read(self.program_counter) as u16,
            AddressingMode::ZeroPage_X => {
                let operand = self.mem_read(self.program_counter);
                let address = operand.wrapping_add(self.register_x) as u16;
                address
            }
            AddressingMode::ZeroPage_Y => {
                let operand = self.mem_read(self.program_counter);
                let address = operand.wrapping_add(self.register_y) as u16;
                address
            }
            AddressingMode::Absolute => self.mem_read_u16(self.program_counter),
            AddressingMode::Absolute_X => {
                let operand = self.mem_read_u16(self.program_counter);
                let address = operand.wrapping_add(self.register_x as u16);
                address
            }
            AddressingMode::Absolute_Y => {
                let operand = self.mem_read_u16(self.program_counter);
                let address = operand.wrapping_add(self.register_y as u16);
                address
            }
            AddressingMode::Indirect => {
                let operand = self.mem_read(self.program_counter);

                let lsb = self.mem_read(operand as u16);
                let msb = self.mem_read((operand as u8).wrapping_add(1) as u16);
                (msb as u16) << 8 | (lsb as u16)
            }
            AddressingMode::Indirect_X => {
                let operand = self.mem_read(self.program_counter);

                let ptr: u8 = (operand as u8).wrapping_add(self.register_x);
                let lsb = self.mem_read(ptr as u16);
                let msb = self.mem_read(ptr.wrapping_add(1) as u16);
                (msb as u16) << 8 | (lsb as u16)
            }
            AddressingMode::Indirect_Y => {
                let operand = self.mem_read(self.program_counter);

                let lsb = self.mem_read(operand as u16);
                let msb = self.mem_read((operand as u8).wrapping_add(1) as u16);
                let address = (msb as u16) << 8 | (lsb as u16);
                let address = address.wrapping_add(self.register_y as u16);
                address
            }
            AddressingMode::NoneAddressing => {
                panic!("mode {:?} is not supported", mode);
            }
        }
    }

    fn set_zero_and_negative_flags(&mut self, register: u8) {
        // Clear zero and negative flags
        self.status &= 0b0111_1101;

        if register == 0 {
            self.status |= 0b0000_0010;
        }

        if register & 0b1000_0000 != 0 {
            self.status |= 0b1000_0000;
        }
    }

    fn lda(&mut self, mode: &AddressingMode) {
        let address = self.operand_address(mode);
        let value = self.mem_read(address);
        self.register_a = value;

        // Clear zero and negative flags
        self.status &= 0b0111_1101;

        self.set_zero_and_negative_flags(self.register_a);
    }
}

#[cfg(test)]
mod test {
    use crate::cpu::CPU;

    #[test]
    fn test_0xa9_lda_opcode() {
        let mut cpu = CPU::new();
        cpu.run(vec![0xa9, 0x05, 0x00]);
        assert_eq!(cpu.register_a, 0x05);
        assert!(cpu.status & 0b1000_0010 == 0);
    }

    #[test]
    fn test_0xa9_lda_opcode_zero_flag_set() {
        let mut cpu = CPU::new();
        cpu.run(vec![0xa9, 0x00, 0x00]);
        assert!(cpu.status & 0b0000_0010 == 0b10);
    }

    #[test]
    fn test_0xa9_lda_opcode_negative_flag_set() {
        let mut cpu = CPU::new();
        cpu.run(vec![0xa9, 0xf0, 0x00]);
        assert!(cpu.status & 0b1000_0000 == 0b1000_0000);
    }

    #[test]
    fn test_0xaa_tax_opcode() {
        let mut cpu = CPU::new();
        cpu.load(vec![0xaa, 0x00]);
        cpu.reset();
        cpu.register_a = 0x05;
        cpu.interpret();
        assert_eq!(cpu.register_x, 0x05);
        assert!(cpu.status & 0b1000_0010 == 0);
    }

    #[test]
    fn test_0xaa_tax_opcode_zero_flag_set() {
        let mut cpu = CPU::new();
        cpu.load(vec![0xaa, 0x00]);
        cpu.reset();
        cpu.register_a = 0x00;
        cpu.interpret();
        assert!(cpu.status & 0b0000_0010 == 0b10);
    }

    #[test]
    fn test_0xaa_tax_opcode_negative_flag_set() {
        let mut cpu = CPU::new();
        cpu.load(vec![0xaa, 0x00]);
        cpu.reset();
        cpu.register_a = 0xf5;
        cpu.interpret();
        assert!(cpu.status & 0b1000_0000 == 0b1000_0000);
    }

    #[test]
    fn test_0xe8_inx_opcode() {
        let mut cpu = CPU::new();
        cpu.load(vec![0xe8, 0x00]);
        cpu.reset();
        cpu.register_x = 0x05;
        cpu.interpret();
        assert_eq!(cpu.register_x, 0x06);
        assert!(cpu.status & 0b1000_0010 == 0);
    }

    #[test]
    fn test_0xe8_inx_opcode_zero_flag_set_with_overflow() {
        let mut cpu = CPU::new();
        cpu.load(vec![0xe8, 0x00]);
        cpu.reset();
        cpu.register_x = 0xff;
        cpu.interpret();
        assert_eq!(cpu.register_x, 0x00);
        assert!(cpu.status & 0b0000_0010 == 0b10);
    }

    #[test]
    fn test_0xe8_inx_opcode_negative_flag_set() {
        let mut cpu = CPU::new();
        cpu.load(vec![0xe8, 0x00]);
        cpu.reset();
        cpu.register_x = 0xf5;
        cpu.interpret();
        assert_eq!(cpu.register_x, 0xf6);
        assert!(cpu.status & 0b1000_0000 == 0b1000_0000);
    }

    #[test]
    fn test_opcode_combination() {
        let mut cpu = CPU::new();
        cpu.run(vec![0xa9, 0xc0, 0xaa, 0xe8, 0x00]);

        assert_eq!(cpu.register_x, 0xc1)
    }

    #[test]
    fn test_mem_read() {
        let mut cpu = CPU::new();
        cpu.memory[0x12ab] = 100;
        assert_eq!(cpu.mem_read(0x12ab), 100);
    }

    #[test]
    fn test_mem_write() {
        let mut cpu = CPU::new();
        cpu.mem_write(0x12ab, 100);
        assert_eq!(cpu.memory[0x12ab], 100);
    }

    #[test]
    fn test_mem_read_u16() {
        let mut cpu = CPU::new();
        cpu.memory[0x12ab] = 0x10;
        cpu.memory[0x12ac] = 0x11;
        assert_eq!(cpu.mem_read_u16(0x12ab), 0x1110);
    }

    #[test]
    fn test_mem_write_u16() {
        let mut cpu = CPU::new();
        cpu.mem_write_u16(0x12ab, 0x10ab);
        assert_eq!(cpu.memory[0x12ab], 0xab);
        assert_eq!(cpu.memory[0x12ac], 0x10);
    }

    #[test]
    fn test_load_program() {
        let mut cpu = CPU::new();
        cpu.load(vec![0xa9, 0xc0, 0xaa, 0xe8, 0x00]);
        assert_eq!(cpu.memory[0x8000], 0xa9);
        assert_eq!(cpu.memory[0x8001], 0xc0);
        assert_eq!(cpu.memory[0x8002], 0xaa);
        assert_eq!(cpu.memory[0x8003], 0xe8);
        assert_eq!(cpu.memory[0x8004], 0x00);
        assert_eq!(cpu.mem_read_u16(0xFFFC), 0x8000);
    }
}
