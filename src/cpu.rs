use core::panic;

use crate::instruction::{AddressingMode, Instruction};

/// Status Flags
///   7   6   5   4   3   2   1   0
/// +---+---+---+---+---+---+---+---+
/// | N | V | - | B | D | I | Z | C |
/// +---+---+---+---+---+---+---+---+
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StatusFlag {
    Carry = 0b0000_0001,
    Zero = 0b0000_0010,
    Interrupt = 0b0000_0100,
    Decimal = 0b0000_1000,
    Break = 0b0001_0000,
    Overflow = 0b0100_0000,
    Negative = 0b1000_0000,
}

impl StatusFlag {
    pub fn to_mask(self) -> u8 {
        self as u8
    }
}

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

    fn set_flag(&mut self, flag: StatusFlag) {
        self.status |= flag.to_mask();
    }

    fn clear_flag(&mut self, flag: StatusFlag) {
        self.status &= !flag.to_mask();
    }

    fn is_flag_set(&self, flag: StatusFlag) -> bool {
        self.status & flag.to_mask() != 0
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
                // ASL
                0x0A | 0x06 | 0x16 | 0x0E | 0x1E => {
                    self.asl(opcode);
                }
                // BCC
                0x90 => self.bcc(opcode),
                // BCS
                0xB0 => self.bcs(opcode),
                // BEQ
                0xF0 => self.beq(opcode),
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
                _ => panic!("Opcode not supported {:X}", opcode),
            }
        }
    }

    /// Read bout Addressing Modes implementations: https://www.nesdev.org/obelisk-6502-guide/addressing.html
    fn operand_address(&self, mode: &AddressingMode) -> Option<u16> {
        match mode {
            AddressingMode::Implied => None,
            AddressingMode::Accumulator => None,
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
            AddressingMode::Relative => Some(self.mem_read(self.program_counter) as u16),
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
        self.clear_flag(StatusFlag::Zero);
        self.clear_flag(StatusFlag::Negative);

        if register == 0 {
            self.set_flag(StatusFlag::Zero);
        }

        if register & StatusFlag::Negative.to_mask() != 0 {
            self.set_flag(StatusFlag::Negative);
        }
    }
}

impl CPU {
    fn lda(&mut self, opcode: u8) {
        let instruction = Instruction::from(opcode);
        let address = self.operand_address(&instruction.mode).unwrap();
        let value = self.mem_read(address);
        self.register_a = value;

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
        let res = self.register_a as u16
            + operand as u16
            + (self.status & StatusFlag::Carry.to_mask()) as u16;

        // set Carry flag
        if res > 255 {
            self.set_flag(StatusFlag::Carry);
        } else {
            self.clear_flag(StatusFlag::Carry);
        }

        // set Zero flag
        if res as u8 == 0 {
            self.set_flag(StatusFlag::Zero);
        } else {
            self.clear_flag(StatusFlag::Zero);
        }

        // set Overflow flag
        if (operand ^ res as u8) & (res as u8 ^ self.register_a) & 0x80 != 0 {
            self.set_flag(StatusFlag::Overflow);
        } else {
            self.clear_flag(StatusFlag::Overflow);
        }

        // set Negative flag
        if res as u8 & 0x80 != 0 {
            self.set_flag(StatusFlag::Negative);
        } else {
            self.clear_flag(StatusFlag::Negative);
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

    fn asl(&mut self, opcode: u8) {
        let instruction = Instruction::from(opcode);
        match instruction.mode {
            AddressingMode::Accumulator => {
                if self.register_a & 0b1000_0000 != 0 {
                    self.set_flag(StatusFlag::Carry);
                } else {
                    self.clear_flag(StatusFlag::Carry);
                }
                self.register_a = self.register_a << 1;
                self.set_zero_and_negative_flags(self.register_a);
            }
            _ => {
                let address = self.operand_address(&instruction.mode).unwrap();
                let operand = self.mem_read(address);

                if operand & 0b1000_0000 != 0 {
                    self.set_flag(StatusFlag::Carry);
                } else {
                    self.clear_flag(StatusFlag::Carry);
                }

                let res = operand << 1;
                self.mem_write(address, res);
                self.set_zero_and_negative_flags(res);
            }
        }

        self.program_counter += instruction.size as u16 - 1;
    }

    fn bcc(&mut self, opcode: u8) {
        self.branch(opcode, !self.is_flag_set(StatusFlag::Carry));
    }

    fn bcs(&mut self, opcode: u8) {
        self.branch(opcode, self.is_flag_set(StatusFlag::Carry));
    }

    fn beq(&mut self, opcode: u8) {
        self.branch(opcode, self.is_flag_set(StatusFlag::Zero));
    }

    fn branch(&mut self, opcode: u8, condition: bool) {
        let instruction = Instruction::from(opcode);
        let offset = self.operand_address(&instruction.mode).unwrap() as i8;
        self.program_counter += instruction.size as u16 - 1;

        if condition {
            // jump to address
            self.program_counter = self.program_counter.wrapping_add(offset as u16);
        }
    }
}

#[cfg(test)]
mod test {
    use crate::cpu::{StatusFlag, CPU};

    #[test]
    fn test_set_flag() {
        let mut cpu = CPU::new();

        // Set Carry flag
        cpu.set_flag(StatusFlag::Carry);
        assert_eq!(
            cpu.status & StatusFlag::Carry as u8,
            StatusFlag::Carry as u8
        );

        // Set Zero flag
        cpu.set_flag(StatusFlag::Zero);
        assert_eq!(cpu.status & StatusFlag::Zero as u8, StatusFlag::Zero as u8);

        // Both Carry and Zero flags should be set
        assert_eq!(
            cpu.status & (StatusFlag::Carry as u8 | StatusFlag::Zero as u8),
            0b0000_0011
        );
    }

    #[test]
    fn test_clear_flag() {
        let mut cpu = CPU::new();

        // Initially set Carry and Zero flags
        cpu.set_flag(StatusFlag::Carry);
        cpu.set_flag(StatusFlag::Zero);

        // Clear Carry flag
        cpu.clear_flag(StatusFlag::Carry);
        assert_eq!(cpu.status & StatusFlag::Carry as u8, 0); // Carry should be cleared

        // Ensure Zero flag is still set
        assert_eq!(cpu.status & StatusFlag::Zero as u8, StatusFlag::Zero as u8);

        // Clear Zero flag
        cpu.clear_flag(StatusFlag::Zero);
        assert_eq!(cpu.status & StatusFlag::Zero as u8, 0); // Zero should be cleared
    }

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

    #[test]
    fn test_asl_accumulator() {
        let mut cpu = CPU::new();

        // Load the program: ASL Accumulator (0x0A)
        // In this case, we shift 0x81 (10000001 in binary) to the left
        // Expected result: 0x02 (00000010 in binary)
        // The carry flag should be set because bit 7 was 1
        // The negative flag should be clear because bit 7 of the result is 0
        // The zero flag should be clear because the result is not zero
        cpu.load(vec![0x0A]);
        cpu.reset();
        cpu.register_a = 0x81; // Set accumulator to 0x81
        cpu.interpret();

        assert_eq!(cpu.register_a, 0x02); // Result after shift
        assert_eq!(cpu.status & 0b0000_0001, 0b0000_0001); // Carry flag should be set
        assert_eq!(cpu.status & 0b1000_0000, 0); // Negative flag should be clear
        assert_eq!(cpu.status & 0b0000_0010, 0); // Zero flag should be clear
    }

    #[test]
    fn test_asl_accumulator_zero() {
        let mut cpu = CPU::new();

        // Load the program: ASL Accumulator (0x0A)
        // In this case, we shift 0x80 (10000000 in binary) to the left
        // Expected result: 0x00 (all bits shifted out)
        // The carry flag should be set because bit 7 was 1
        // The zero flag should be set because the result is 0
        // The negative flag should be clear because bit 7 of the result is 0
        cpu.load(vec![0x0A]);
        cpu.reset();
        cpu.register_a = 0x80; // Set accumulator to 0x80
        cpu.interpret();

        assert_eq!(cpu.register_a, 0x00); // Result after shift
        assert_eq!(cpu.status & 0b0000_0001, 0b0000_0001); // Carry flag should be set
        assert_eq!(cpu.status & 0b0000_0010, 0b0000_0010); // Zero flag should be set
        assert_eq!(cpu.status & 0b1000_0000, 0); // Negative flag should be clear
    }

    #[test]
    fn test_asl_zero_page() {
        let mut cpu = CPU::new();

        // Load the program: ASL $10 (0x06 0x10)
        // Shift value at memory location 0x0010, initially set to 0x40 (01000000 in binary)
        // Expected result: 0x80 (10000000 in binary)
        // Carry flag should be clear because bit 7 was 0
        // Negative flag should be set because bit 7 of the result is 1
        // Zero flag should be clear because the result is not zero
        cpu.load(vec![0x06, 0x10]); // ASL $10
        cpu.reset();
        cpu.mem_write(0x0010, 0x40); // Set memory at 0x10 to 0x40
        cpu.interpret();

        assert_eq!(cpu.mem_read(0x0010), 0x80); // Result after shift
        assert_eq!(cpu.status & 0b0000_0001, 0); // Carry flag should be clear
        assert_eq!(cpu.status & 0b1000_0000, 0b1000_0000); // Negative flag should be set
        assert_eq!(cpu.status & 0b0000_0010, 0); // Zero flag should be clear
    }

    #[test]
    fn test_asl_zero_page_with_carry() {
        let mut cpu = CPU::new();

        // Load the program: ASL $10 (0x06 0x10)
        // Shift value at memory location 0x0010, initially set to 0xFF (11111111 in binary)
        // Expected result: 0xFE (11111110 in binary)
        // Carry flag should be set because bit 7 was 1
        // Negative flag should be set because bit 7 of the result is 1
        // Zero flag should be clear because the result is not zero
        cpu.load(vec![0x06, 0x10]); // ASL $10
        cpu.reset();
        cpu.mem_write(0x0010, 0xFF); // Set memory at 0x10 to 0xFF
        cpu.interpret();

        assert_eq!(cpu.mem_read(0x0010), 0xFE); // Result after shift
        assert_eq!(cpu.status & 0b0000_0001, 0b0000_0001); // Carry flag should be set
        assert_eq!(cpu.status & 0b1000_0000, 0b1000_0000); // Negative flag should be set
        assert_eq!(cpu.status & 0b0000_0010, 0); // Zero flag should be clear
    }

    #[test]
    fn test_asl_zero_page_to_zero() {
        let mut cpu = CPU::new();

        // Load the program: ASL $10 (0x06 0x10)
        // Shift value at memory location 0x0010, initially set to 0x01 (00000001 in binary)
        // Expected result: 0x02 (00000010 in binary)
        // Carry flag should be clear because bit 7 was 0
        // Zero flag should be clear because the result is not zero
        // Negative flag should be clear because bit 7 of the result is 0
        cpu.load(vec![0x06, 0x10]); // ASL $10
        cpu.reset();
        cpu.mem_write(0x0010, 0x01); // Set memory at 0x10 to 0x01
        cpu.interpret();

        assert_eq!(cpu.mem_read(0x0010), 0x02); // Result after shift
        assert_eq!(cpu.status & 0b0000_0001, 0); // Carry flag should be clear
        assert_eq!(cpu.status & 0b1000_0000, 0); // Negative flag should be clear
        assert_eq!(cpu.status & 0b0000_0010, 0); // Zero flag should be clear
    }

    #[test]
    fn test_bcc_no_branch() {
        let mut cpu = CPU::new();

        // Load the BCC instruction with a relative offset of 2
        cpu.load(vec![0x90, 0x02, 0x00]); // BCC with offset 2
        cpu.reset();

        // Set the Carry flag (so the branch shouldn't occur)
        cpu.set_flag(StatusFlag::Carry);
        let initial_pc = cpu.program_counter;

        // Run the instruction
        cpu.interpret();

        // The program counter should only increment by 2 (BCC opcode + operand + BRK opcode),
        // since the Carry flag is set and the branch doesn't occur
        assert_eq!(cpu.program_counter, initial_pc + 3);
    }

    #[test]
    fn test_bcc_branch_forward() {
        let mut cpu = CPU::new();

        // Load the BCC instruction with a relative offset of 2
        cpu.load(vec![0x90, 0x02]); // BCC with offset 2
        cpu.reset();

        let initial_pc = cpu.program_counter;
        cpu.interpret();

        // The program counter should jump forward by the offset
        assert_eq!(cpu.program_counter, initial_pc + 2 + 2 + 1); // 2-byte instruction + offset + brk
    }

    #[test]
    fn test_bcc_branch_backward() {
        let mut cpu = CPU::new();

        // Load the BCC instruction with a negative offset (-2)
        cpu.load(vec![0x90, 0xFD]); // BCC with offset -3 (0xFE is -3 in two's complement)
        cpu.reset();
        let initial_pc = cpu.program_counter;
        cpu.interpret();

        // After the BCC opcode (1 byte) and the offset byte (1 byte), the program counter is at initial_pc + 3 +1 corresponding to the BRK opcode
        assert_eq!(
            cpu.program_counter,
            initial_pc.wrapping_add(2).wrapping_sub(3).wrapping_add(1)
        );
    }

    #[test]
    fn test_bcs_branch_forward() {
        let mut cpu = CPU::new();

        // Load the BCS instruction with a positive offset (+4)
        cpu.load(vec![0xB0, 0x04]); // BCS (0xB0) with offset +4
        cpu.reset();
        // Set the Carry flag (so the branch should occur)
        cpu.set_flag(StatusFlag::Carry);
        let initial_pc = cpu.program_counter;
        cpu.interpret();

        // The program counter should move forward by 4 (+1 for the BRK opcode) (opcode + offset + BRK)
        assert_eq!(
            cpu.program_counter,
            initial_pc.wrapping_add(2).wrapping_add(5)
        );
    }

    #[test]
    fn test_bcs_no_branch_when_carry_clear() {
        let mut cpu = CPU::new();

        // Load the BCS instruction with a positive offset (+4)
        cpu.load(vec![0xB0, 0x04]); // BCS (0xB0) with offset +4
        cpu.reset();
        let initial_pc = cpu.program_counter;
        cpu.interpret();

        // The program counter should only move forward by 2 (for the opcode and offset) and not branch
        // +1 for the BRK
        assert_eq!(cpu.program_counter, initial_pc.wrapping_add(3));
    }

    #[test]
    fn test_bcs_branch_backward() {
        let mut cpu = CPU::new();

        // Load the BCS instruction with a negative offset (-2)
        cpu.load(vec![0xB0, 0xFD]); // BCS (0xB0) with offset -2 (0xFE in two's complement is -2)
        cpu.reset();
        // Set the Carry flag (so the branch should occur)
        cpu.set_flag(StatusFlag::Carry);
        let initial_pc = cpu.program_counter;
        cpu.interpret();

        // The program counter should jump backward by 2 + +1 for the BRK
        assert_eq!(
            cpu.program_counter,
            initial_pc.wrapping_add(2).wrapping_sub(3).wrapping_add(1)
        );
    }

    #[test]
    fn test_beq_branch_forward() {
        let mut cpu = CPU::new();

        // Load the BEQ instruction with a positive offset (+4)
        cpu.load(vec![0xF0, 0x04]); // BEQ (0xF0) with offset +4
        cpu.reset();
        cpu.set_flag(StatusFlag::Zero);
        let initial_pc = cpu.program_counter;
        cpu.interpret();

        // The program counter should move forward by 4 (opcode + offset) + 1 (BRK)
        assert_eq!(
            cpu.program_counter,
            initial_pc.wrapping_add(2).wrapping_add(5)
        );
    }

    #[test]
    fn test_beq_no_branch_when_zero_clear() {
        let mut cpu = CPU::new();

        // Load the BEQ instruction with a positive offset (+4)
        cpu.load(vec![0xF0, 0x04]); // BEQ (0xF0) with offset +4
        cpu.reset();
        let initial_pc = cpu.program_counter;
        cpu.interpret();

        // The program counter should only move forward by 2 (for the opcode and offset) and not branch + 1 (BRK)
        assert_eq!(cpu.program_counter, initial_pc.wrapping_add(3));
    }

    #[test]
    fn test_beq_branch_backward() {
        let mut cpu = CPU::new();

        // Load the BEQ instruction with a negative offset (-2)
        cpu.load(vec![0xF0, 0xFD]); // BEQ (0xF0) with offset -2 (0xFE in two's complement is -2)
        cpu.reset();
        // Set the Zero flag (so the branch should occur)
        cpu.set_flag(StatusFlag::Zero);
        let initial_pc = cpu.program_counter;
        cpu.interpret();

        // The program counter should jump backward by 2 + 1 (BRK)
        assert_eq!(
            cpu.program_counter,
            initial_pc.wrapping_add(2).wrapping_sub(3).wrapping_add(1)
        );
    }
}
