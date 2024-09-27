use std::u16;

use crate::instruction::{self, AddressingMode, Instruction};

/// Status Flags
///   7   6   5   4   3   2   1   0
/// +---+---+---+---+---+---+---+---+
/// | N | V | - | B | D | I | Z | C |
/// +---+---+---+---+---+---+---+---+

#[derive(Debug)]
struct CPU {
    register_a: u8,
    register_x: u8,
    register_y: u8,
    status: u8,
    program_counter: u16,
    memory: [u8; 0xFFFF],
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
        let lsb = self.mem_read(address) as u16;
        let msb = self.mem_read(address + 1) as u16;
        (msb << 8) | (lsb as u16)
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
                // ADC
                0x69 | 0x65 | 0x75 | 0x6D | 0x7D | 0x79 | 0x61 | 0x71 => {
                    self.adc(opcode);
                }
                // AND
                0x29 | 0x25 | 0x35 | 0x2D | 0x3D | 0x39 | 0x21 | 0x31 => {
                    self.and(opcode);
                }
                // LDA
                0xA9 | 0xA5 | 0xB5 | 0xAD | 0xBD | 0xB9 | 0xA1 | 0xB1 => {
                    self.lda(opcode);
                }
                // STA
                0x85 | 0x95 | 0x8D | 0x9D | 0x99 | 0x81 | 0x91 => {
                    self.sta(opcode);
                }
                // TAX
                0xAA => {
                    self.tax(opcode);
                }
                // INC
                0xE8 => {
                    self.inc(opcode);
                }
                // BRK
                0x00 => {
                    return;
                }
                _ => todo!(),
            }
        }
    }

    /// Read bout Addressing Modes implementations: https://www.nesdev.org/obelisk-6502-guide/addressing.html
    fn operand_address(&self, mode: &AddressingMode) -> Option<u16> {
        match mode {
            AddressingMode::Implied => None,
            AddressingMode::Immediate => Some(self.program_counter),
            AddressingMode::ZeroPage => Some(self.mem_read(self.program_counter) as u16),
            AddressingMode::ZeroPage_X => {
                let operand = self.mem_read(self.program_counter);
                let address = operand.wrapping_add(self.register_x) as u16;
                Some(address)
            }
            AddressingMode::ZeroPage_Y => {
                let operand = self.mem_read(self.program_counter);
                let address = operand.wrapping_add(self.register_y) as u16;
                Some(address)
            }
            AddressingMode::Absolute => Some(self.mem_read_u16(self.program_counter)),
            AddressingMode::Absolute_X => {
                let operand = self.mem_read_u16(self.program_counter);
                let address = operand.wrapping_add(self.register_x as u16);
                Some(address)
            }
            AddressingMode::Absolute_Y => {
                let operand = self.mem_read_u16(self.program_counter);
                let address = operand.wrapping_add(self.register_y as u16);
                Some(address)
            }
            AddressingMode::Indirect => {
                let operand = self.mem_read(self.program_counter);

                let lsb = self.mem_read(operand as u16);
                let msb = self.mem_read((operand as u8).wrapping_add(1) as u16);
                Some((msb as u16) << 8 | (lsb as u16))
            }
            AddressingMode::Indirect_X => {
                let operand = self.mem_read(self.program_counter);

                let ptr: u8 = (operand as u8).wrapping_add(self.register_x);
                let lsb = self.mem_read(ptr as u16);
                let msb = self.mem_read(ptr.wrapping_add(1) as u16);
                Some((msb as u16) << 8 | (lsb as u16))
            }
            AddressingMode::Indirect_Y => {
                let operand = self.mem_read(self.program_counter);

                let lsb = self.mem_read(operand as u16);
                let msb = self.mem_read((operand as u8).wrapping_add(1) as u16);
                let address = (msb as u16) << 8 | (lsb as u16);
                let address = address.wrapping_add(self.register_y as u16);
                Some(address)
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
}

impl CPU {
    fn lda(&mut self, opcode: u8) {
        let instruction = Instruction::from(opcode);
        let address = self.operand_address(&instruction.mode).unwrap();
        let value = self.mem_read(address);
        self.register_a = value;

        // Clear zero and negative flags
        self.status &= 0b0111_1101;

        self.set_zero_and_negative_flags(self.register_a);

        self.program_counter += instruction.size as u16 - 1;
    }

    fn sta(&mut self, opcode: u8) {
        let instruction = Instruction::from(opcode);
        let address = self.operand_address(&instruction.mode).unwrap();
        self.mem_write(address, self.register_a);

        self.program_counter += instruction.size as u16 - 1;
    }

    fn tax(&mut self, opcode: u8) {
        let instruction = Instruction::from(opcode);
        self.register_x = self.register_a;
        self.set_zero_and_negative_flags(self.register_x);

        self.program_counter += instruction.size as u16 - 1;
    }

    fn inc(&mut self, opcode: u8) {
        let instruction = Instruction::from(opcode);
        self.register_x = self.register_x.wrapping_add(1);
        self.set_zero_and_negative_flags(self.register_x);

        self.program_counter += instruction.size as u16 - 1;
    }

    fn adc(&mut self, opcode: u8) {
        let instruction = Instruction::from(opcode);
        let address = self.operand_address(&instruction.mode).unwrap();
        let operand = self.mem_read(address);
        let res = self.register_a as u16 + operand as u16 + (self.status & 0b0000_0001) as u16;

        // set Carry flag
        if res > 255 {
            self.status |= 0b0000_0001;
        } else {
            self.status &= 0b1111_1110;
        }

        // set Zero flag
        if res as u8 == 0 {
            self.status |= 0b0000_0010;
        } else {
            self.status &= 0b1111_1101;
        }

        // set Overflow flag
        if (operand ^ res as u8) & (res as u8 ^ self.register_a) & 0x80 != 0 {
            self.status |= 0b0100_0000;
        } else {
            self.status &= 0b1011_1111;
        }

        // set Negative flag
        if res as u8 & 0x80 != 0 {
            self.status |= 0b1000_0000;
        } else {
            self.status &= 0b0111_1111;
        }

        self.register_a = res as u8;

        self.program_counter += instruction.size as u16 - 1;
    }

    fn and(&mut self, opcode: u8) {
        let instruction = Instruction::from(opcode);
        let address = self.operand_address(&instruction.mode).unwrap();
        let operand = self.mem_read(address);

        self.register_a &= operand;

        self.set_zero_and_negative_flags(self.register_a);

        self.program_counter += instruction.size as u16 - 1;
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
    fn test_0xa5_lda_opcode() {
        let mut cpu = CPU::new();
        cpu.mem_write(0x05, 0x7a);
        cpu.run(vec![0xa5, 0x05, 0x00]);
        assert_eq!(cpu.register_a, 0x7a);
    }

    #[test]
    fn test_0xb5_lda_opcode() {
        let mut cpu = CPU::new();
        cpu.mem_write(0x16, 0x7a);
        cpu.load(vec![0xb5, 0x12, 0x00]);
        cpu.reset();
        cpu.register_x = 0x04;
        cpu.interpret();
        assert_eq!(cpu.register_a, 0x7a);
    }

    #[test]
    fn test_0xad_lda_opcode() {
        let mut cpu = CPU::new();
        cpu.mem_write(0xaa12, 0x7a);
        cpu.run(vec![0xad, 0x12, 0xaa, 0x00]);
        assert_eq!(cpu.register_a, 0x7a);
    }

    #[test]
    fn test_0xbd_lda_opcode() {
        let mut cpu = CPU::new();
        cpu.mem_write(0xaa16, 0x7a);
        cpu.load(vec![0xbd, 0x12, 0xaa, 0x00]);
        cpu.reset();
        cpu.register_x = 0x04;
        cpu.interpret();
        assert_eq!(cpu.register_a, 0x7a);
    }

    #[test]
    fn test_0xb9_lda_opcode() {
        let mut cpu = CPU::new();
        cpu.mem_write(0xaa16, 0x7a);
        cpu.load(vec![0xb9, 0x12, 0xaa, 0x00]);
        cpu.reset();
        cpu.register_y = 0x04;
        cpu.interpret();
        assert_eq!(cpu.register_a, 0x7a);
    }

    #[test]
    fn test_0xa1_lda_opcode() {
        let mut cpu = CPU::new();
        cpu.mem_write(0x16, 0x07);
        cpu.mem_write(0x17, 0x1a);
        cpu.mem_write(0x1a07, 0x33);
        cpu.load(vec![0xa1, 0x12, 0x00]);
        cpu.reset();
        cpu.register_x = 0x04;
        cpu.interpret();
        assert_eq!(cpu.register_a, 0x33);
    }

    #[test]
    fn test_0xa1_lda_opcode_wrapping_overflow() {
        let mut cpu = CPU::new();
        cpu.mem_write(0x01, 0xee);
        cpu.mem_write(0x02, 0x12);
        cpu.mem_write(0x12ee, 0x33);
        cpu.load(vec![0xa1, 0x02, 0x00]);
        cpu.reset();
        cpu.register_x = 0xff;
        cpu.interpret();
        assert_eq!(cpu.register_a, 0x33);
    }

    #[test]
    fn test_0xb1_lda_opcode() {
        let mut cpu = CPU::new();
        cpu.mem_write(0x12, 0x07);
        cpu.mem_write(0x13, 0x1a);
        cpu.mem_write(0x1a0b, 0x33);
        cpu.load(vec![0xb1, 0x12, 0x00]);
        cpu.reset();
        cpu.register_y = 0x04;
        cpu.interpret();
        assert_eq!(cpu.register_a, 0x33);
    }

    #[test]
    fn test_0xb1_lda_opcode_wrapping_overflow() {
        let mut cpu = CPU::new();
        cpu.mem_write(0x12, 0xff);
        cpu.mem_write(0x13, 0xff);
        cpu.mem_write(0x01, 0x33);
        cpu.load(vec![0xb1, 0x12, 0x00]);
        cpu.reset();
        cpu.register_y = 0x02;
        cpu.interpret();
        assert_eq!(cpu.register_a, 0x33);
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

    #[test]
    fn test_adc_no_carry() {
        let mut cpu = CPU::new();
        cpu.load(vec![0x69, 20]);
        cpu.reset();
        cpu.register_a = 10; // A = 10
        cpu.interpret();

        assert_eq!(cpu.register_a, 30); // A should be 10 + 20 = 30
        assert_eq!(cpu.status & 0b0000_0001, 0); // Carry flag should be clear
        assert_eq!(cpu.status & 0b0000_0010, 0); // Zero flag should be clear
        assert_eq!(cpu.status & 0b1000_0000, 0); // Negative flag should be clear
    }

    #[test]
    fn test_adc_with_carry() {
        let mut cpu = CPU::new();
        cpu.load(vec![0x69, 100]);
        cpu.reset();
        cpu.register_a = 200;
        cpu.interpret();

        assert_eq!(cpu.register_a, 44); // A should be (200 + 100) % 256 = 44
        assert_eq!(cpu.status & 0b0000_0001, 1); // Carry flag should be set
        assert_eq!(cpu.status & 0b0000_0010, 0); // Zero flag should be clear
        assert_eq!(cpu.status & 0b1000_0000, 0); // Negative flag should be clear
    }

    #[test]
    fn test_adc_zero_result() {
        let mut cpu = CPU::new();
        cpu.load(vec![0x69, 126]);
        cpu.reset();
        cpu.register_a = 130;
        cpu.interpret();

        assert_eq!(cpu.register_a, 0); // A should be 130 + 126 = 0 (256 -> wrapped to 0)
        assert_eq!(cpu.status & 0b0000_0001, 1); // Carry flag should be set
        assert_eq!(cpu.status & 0b0000_0010, 0b10); // Zero flag should be set
        assert_eq!(cpu.status & 0b1000_0000, 0); // Negative flag should be clear
    }

    #[test]
    fn test_adc_overflow() {
        let mut cpu = CPU::new();
        cpu.load(vec![0x69, 1]);
        cpu.reset();
        cpu.register_a = 127; // A = 127 (positive)
        cpu.interpret();

        assert_eq!(cpu.register_a, 128); // A should be 128 (negative in two's complement)
        assert_eq!(cpu.status & 0b0000_0001, 0); // Carry flag should be clear
        assert_eq!(cpu.status & 0b0100_0000, 0b0100_0000); // Overflow flag should be set
        assert_eq!(cpu.status & 0b1000_0000, 0b1000_0000); // Negative flag should be set
    }

    #[test]
    fn test_adc_negative() {
        let mut cpu = CPU::new();
        cpu.load(vec![0x69, 0x80]);
        cpu.reset();
        cpu.register_a = 0x80; // A = 128 (negative in two's complement)
        cpu.interpret();

        assert_eq!(cpu.register_a, 0); // A should wrap to 0
        assert_eq!(cpu.status & 0b0000_0001, 1); // Carry flag should be set
        assert_eq!(cpu.status & 0b0100_0000, 0b0100_0000); // Overflow flag should be set
        assert_eq!(cpu.status & 0b1000_0000, 0); // Negative flag should be clear
        assert_eq!(cpu.status & 0b0000_0010, 0b0000_0010); // Zero flag should be set
    }

    #[test]
    fn test_adc_with_initial_carry() {
        let mut cpu = CPU::new();
        cpu.load(vec![0x69, 10]);
        cpu.reset();
        cpu.status = 0b0000_0001; // Set the carry flag to 1
        cpu.register_a = 5;
        cpu.interpret();

        assert_eq!(cpu.register_a, 16); // A should be 5 + 10 + 1 (carry) = 16
        assert_eq!(cpu.status & 0b0000_0001, 0); // Carry flag should be clear
        assert_eq!(cpu.status & 0b0000_0010, 0); // Zero flag should be clear
        assert_eq!(cpu.status & 0b1000_0000, 0); // Negative flag should be clear
    }

    #[test]
    fn test_and_immediate() {
        let mut cpu = CPU::new();
        cpu.load(vec![0x29, 0b10101010]); // AND Immediate with 0xAA
        cpu.reset();
        cpu.register_a = 0b11001100; // A = 0xCC (204 in decimal)

        cpu.interpret(); // Execute AND instruction

        assert_eq!(cpu.register_a, 0b10001000); // A should now be 0x88 (136 in decimal)
        assert_eq!(cpu.status & 0b0000_0010, 0); // Zero flag should be clear (result is not zero)
        assert_eq!(cpu.status & 0b1000_0000, 0b1000_0000); // Negative flag should be clear (most significant bit is 1)
    }

    #[test]
    fn test_and_zero_result() {
        let mut cpu = CPU::new();
        cpu.load(vec![0x29, 0b00110011]); // AND Immediate with 0x33
        cpu.reset();
        cpu.register_a = 0b11001100; // A = 0xCC (204 in decimal)

        cpu.interpret(); // Execute AND instruction

        assert_eq!(cpu.register_a, 0); // A should now be 0x00
        assert_eq!(cpu.status & 0b0000_0010, 0b0000_0010); // Zero flag should be set (result is zero)
        assert_eq!(cpu.status & 0b1000_0000, 0); // Negative flag should be clear (most significant bit is 0)
    }

    #[test]
    fn test_and_negative_result() {
        let mut cpu = CPU::new();
        cpu.load(vec![0x29, 0b10101010]); // AND Immediate with 0xAA
        cpu.reset();
        cpu.register_a = 0b11110000; // A = 0xF0 (240 in decimal, negative in two's complement)

        cpu.interpret(); // Execute AND instruction

        assert_eq!(cpu.register_a, 0b10100000); // A should now be 0xA0 (160 in decimal)
        assert_eq!(cpu.status & 0b0000_0010, 0); // Zero flag should be clear (result is not zero)
        assert_eq!(cpu.status & 0b1000_0000, 0b1000_0000); // Negative flag should be set (most significant bit is 1)
    }
}
