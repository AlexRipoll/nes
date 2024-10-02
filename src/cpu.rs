use core::panic;
use std::os::linux::raw::stat;

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
    Unused = 0b0010_0000,
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
    stack_ptr: u8,
    memory: [u8; 0xFFFF + 1],
}

impl CPU {
    fn new() -> Self {
        CPU {
            register_a: 0,
            register_x: 0,
            register_y: 0,
            status: 0,
            program_counter: 0,
            stack_ptr: 0xFD,
            memory: [0u8; 0xFFFF + 1],
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

    fn copy_bit_from(&mut self, src: u8, flag: StatusFlag) {
        if src & flag.to_mask() != 0 {
            self.set_flag(flag);
        } else {
            self.clear_flag(flag);
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

    fn stack_push(&mut self, data: u8) {
        if self.stack_ptr == 0x00 {
            panic!("Stack overflow! Cannot push more data.");
        }

        // Stack is located from 0x0100 to 0x01FF, so add 0x100 to SP to get the address
        let stack_address = 0x0100 + self.stack_ptr as u16;
        self.mem_write(stack_address, data);

        self.stack_ptr = self.stack_ptr.wrapping_sub(1);
    }

    fn stack_pop(&mut self) -> u8 {
        // Check for stack underflow (stack pointer should not exceed 0xFF)
        if self.stack_ptr == 0xFF {
            panic!("Stack underflow! Cannot pop more data.");
        }

        // Increment the stack pointer to point to the current value (since it is decremented on push)
        self.stack_ptr = self.stack_ptr.wrapping_add(1);
        let stack_address = 0x0100 + self.stack_ptr as u16;

        self.mem_read(stack_address)
    }

    fn stack_push_u16(&mut self, data: u16) {
        let msb = (data >> 8) as u8;
        let lsb = (data & 0xff) as u8;
        self.stack_push(msb);
        self.stack_push(lsb);
    }

    fn stack_pop_u16(&mut self) -> u16 {
        let lsb = self.stack_pop() as u16;
        let msb = self.stack_pop() as u16;

        msb << 8 | lsb
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
                // BIT
                0x24 | 0x2C => self.bit(opcode),
                // BMI
                0x30 => self.bmi(opcode),
                // BNE
                0xD0 => self.bne(opcode),
                // BPL
                0x10 => self.bpl(opcode),
                // BVC
                0x50 => self.bvc(opcode),
                // BVS
                0x70 => self.bvs(opcode),
                // CLC
                0x18 => self.clc(opcode),
                // CLD
                0xD8 => self.cld(opcode),
                // CLI
                0x58 => self.cli(opcode),
                // CLV
                0xB8 => self.clv(opcode),
                // CMP
                0xC9 | 0xC5 | 0xD5 | 0xCD | 0xDD | 0xD9 | 0xC1 | 0xD1 => {
                    self.cmp(opcode);
                }
                // CPX
                0xE0 | 0xE4 | 0xEC => {
                    self.cpx(opcode);
                }
                // CPY
                0xC0 | 0xC4 | 0xCC => {
                    self.cpy(opcode);
                }
                // DEC
                0xC6 | 0xD6 | 0xCE | 0xDE => {
                    self.dec(opcode);
                }
                // DEX
                0xCA => self.dex(opcode),
                // DEY
                0x88 => self.dey(opcode),
                // EOR
                0x49 | 0x45 | 0x55 | 0x4D | 0x5D | 0x59 | 0x41 | 0x51 => {
                    self.eor(opcode);
                }
                // INC
                0xE6 | 0xF6 | 0xEE | 0xFE => {
                    self.inc(opcode);
                }
                // INX
                0xE8 => {
                    self.inx(opcode);
                }
                // INY
                0xC8 => {
                    self.iny(opcode);
                }
                // JMP
                0x4C | 0x6C => {
                    self.jmp(opcode);
                }
                // JSR
                0x20 => {
                    self.jsr(opcode);
                }
                // LDA
                0xA9 | 0xA5 | 0xB5 | 0xAD | 0xBD | 0xB9 | 0xA1 | 0xB1 => {
                    self.lda(opcode);
                }
                // LDX
                0xA2 | 0xA6 | 0xB6 | 0xAE | 0xBE => {
                    self.ldx(opcode);
                }
                // LDY
                0xA0 | 0xA4 | 0xB4 | 0xAC | 0xBC => {
                    self.ldy(opcode);
                }
                // LSR
                0x4A | 0x46 | 0x56 | 0x4E | 0x5E => {
                    self.lsr(opcode);
                }
                // NOP
                0xEA => self.nop(opcode),
                // ORA
                0x09 | 0x05 | 0x15 | 0x0D | 0x1D | 0x19 | 0x01 | 0x11 => {
                    self.ora(opcode);
                }
                // PHA
                0x48 => self.pha(opcode),
                // PHP
                0x08 => self.php(opcode),
                // PLA
                0x68 => self.pla(opcode),
                // PLP
                0x28 => self.plp(opcode),
                // ROL
                0x2A | 0x26 | 0x36 | 0x2E | 0x3E => {
                    self.rol(opcode);
                }
                // ROR
                0x6A | 0x66 | 0x76 | 0x6E | 0x7E => {
                    self.ror(opcode);
                }
                // RTI
                0x40 => self.rti(opcode),
                // RTS
                0x60 => self.rts(opcode),
                // STA
                0x85 | 0x95 | 0x8D | 0x9D | 0x99 | 0x81 | 0x91 => {
                    self.sta(opcode);
                }
                // TAX
                0xAA => {
                    self.tax(opcode);
                }
                // BRK
                0x00 => {
                    // self.brk();
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
            // The original 6502 CPU has a bug when fetching the target address in indirect jumps if the pointer falls on a page
            // boundary (e.g., addresses ending with $FF, such as $xxFF, where xx can be any value from $00 to $FF). In these cases,
            // the CPU correctly retrieves the least significant byte (LSB) from the expected address ($xxFF), but it mistakenly obtains
            // the most significant byte (MSB) from the start of the same page ($xx00).
            AddressingMode::Indirect => {
                let operand = self.mem_read_u16(self.program_counter);

                let address = if operand & 0x00FF == 0x00FF {
                    let lsb = self.mem_read(operand);
                    let msb = self.mem_read(operand & 0xFF00);
                    (msb as u16) << 8 | (lsb as u16)
                } else {
                    self.mem_read_u16(operand)
                };

                Some(address)
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

    fn branch(&mut self, opcode: u8, condition: bool) {
        let instruction = Instruction::from(opcode);
        let offset = self.operand_address(&instruction.mode).unwrap() as i8;
        self.program_counter += instruction.size as u16 - 1;

        if condition {
            // jump to address
            self.program_counter = self.program_counter.wrapping_add(offset as u16);
        }
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

    fn bit(&mut self, opcode: u8) {
        let instruction = Instruction::from(opcode);
        let address = self.operand_address(&instruction.mode).unwrap();
        let operand = self.mem_read(address);

        if self.register_a & operand == 0 {
            self.set_flag(StatusFlag::Zero);
        } else {
            self.clear_flag(StatusFlag::Zero);
        }

        self.copy_bit_from(operand, StatusFlag::Overflow);
        self.copy_bit_from(operand, StatusFlag::Negative);

        self.program_counter += instruction.size as u16 - 1;
    }

    fn bmi(&mut self, opcode: u8) {
        self.branch(opcode, self.is_flag_set(StatusFlag::Negative));
    }

    fn bne(&mut self, opcode: u8) {
        self.branch(opcode, !self.is_flag_set(StatusFlag::Zero));
    }

    fn bpl(&mut self, opcode: u8) {
        self.branch(opcode, !self.is_flag_set(StatusFlag::Negative));
    }

    fn brk(&mut self) {
        // Push the current PC (next instruction address) onto the stack
        let pc_msb = (self.program_counter >> 8) as u8;
        let pc_lsb = self.program_counter as u8;
        self.stack_push(pc_msb);
        self.stack_push(pc_lsb);

        // Push the processor status onto the stack (with the Break flag set)
        self.set_flag(StatusFlag::Break);
        self.set_flag(StatusFlag::Unused); // set to 1 as per 6502 conventions
        self.stack_push(self.status);

        // Fetch the interrupt vector address from $FFFE-$FFFF
        let irq_lsb = self.mem_read(0xFFFE);
        let irq_msb = self.mem_read(0xFFFF);
        let irq_vector = (irq_msb as u16) << 8 | (irq_lsb as u16);

        self.program_counter = irq_vector;
    }

    fn bvc(&mut self, opcode: u8) {
        self.branch(opcode, !self.is_flag_set(StatusFlag::Overflow));
    }

    fn bvs(&mut self, opcode: u8) {
        self.branch(opcode, self.is_flag_set(StatusFlag::Overflow));
    }

    fn clc(&mut self, opcode: u8) {
        let instruction = Instruction::from(opcode);
        self.clear_flag(StatusFlag::Carry);

        self.program_counter += instruction.size as u16 - 1;
    }

    fn cld(&mut self, opcode: u8) {
        let instruction = Instruction::from(opcode);
        self.clear_flag(StatusFlag::Decimal);

        self.program_counter += instruction.size as u16 - 1;
    }

    fn cli(&mut self, opcode: u8) {
        let instruction = Instruction::from(opcode);
        self.clear_flag(StatusFlag::Interrupt);

        self.program_counter += instruction.size as u16 - 1;
    }

    fn clv(&mut self, opcode: u8) {
        let instruction = Instruction::from(opcode);
        self.clear_flag(StatusFlag::Overflow);

        self.program_counter += instruction.size as u16 - 1;
    }

    fn compare(&mut self, opcode: u8, register: u8) {
        let instruction = Instruction::from(opcode);
        let address = self.operand_address(&instruction.mode).unwrap();
        let operand = self.mem_read(address);

        if register >= operand {
            self.set_flag(StatusFlag::Carry);
        } else {
            self.clear_flag(StatusFlag::Carry);
        }
        if register == operand {
            self.set_flag(StatusFlag::Zero);
        } else {
            self.clear_flag(StatusFlag::Zero);
        }

        self.copy_bit_from(register.wrapping_sub(operand), StatusFlag::Negative);

        self.program_counter += instruction.size as u16 - 1;
    }

    fn cmp(&mut self, opcode: u8) {
        self.compare(opcode, self.register_a);
    }

    fn cpx(&mut self, opcode: u8) {
        self.compare(opcode, self.register_x);
    }

    fn cpy(&mut self, opcode: u8) {
        self.compare(opcode, self.register_y);
    }

    fn dec(&mut self, opcode: u8) {
        let instruction = Instruction::from(opcode);
        let address = self.operand_address(&instruction.mode).unwrap();
        let operand = self.mem_read(address);

        let res = operand.wrapping_sub(1);
        self.mem_write(address, res);

        self.set_zero_and_negative_flags(res);

        self.program_counter += instruction.size as u16 - 1;
    }

    fn dex(&mut self, opcode: u8) {
        let instruction = Instruction::from(opcode);

        self.register_x = self.register_x.wrapping_sub(1);
        self.set_zero_and_negative_flags(self.register_x);

        self.program_counter += instruction.size as u16 - 1;
    }

    fn dey(&mut self, opcode: u8) {
        let instruction = Instruction::from(opcode);

        self.register_y = self.register_y.wrapping_sub(1);
        self.set_zero_and_negative_flags(self.register_y);

        self.program_counter += instruction.size as u16 - 1;
    }

    fn eor(&mut self, opcode: u8) {
        let instruction = Instruction::from(opcode);
        let address = self.operand_address(&instruction.mode).unwrap();
        let operand = self.mem_read(address);

        self.register_a ^= operand;

        self.set_zero_and_negative_flags(self.register_a);

        self.program_counter += instruction.size as u16 - 1;
    }

    fn inc(&mut self, opcode: u8) {
        let instruction = Instruction::from(opcode);
        let address = self.operand_address(&instruction.mode).unwrap();
        let operand = self.mem_read(address);

        let res = operand.wrapping_add(1);
        self.mem_write(address, res);

        self.set_zero_and_negative_flags(res);

        self.program_counter += instruction.size as u16 - 1;
    }

    fn inx(&mut self, opcode: u8) {
        let instruction = Instruction::from(opcode);
        self.register_x = self.register_x.wrapping_add(1);
        self.set_zero_and_negative_flags(self.register_x);

        self.program_counter += instruction.size as u16 - 1;
    }

    fn iny(&mut self, opcode: u8) {
        let instruction = Instruction::from(opcode);
        self.register_y = self.register_y.wrapping_add(1);
        self.set_zero_and_negative_flags(self.register_y);

        self.program_counter += instruction.size as u16 - 1;
    }

    fn jmp(&mut self, opcode: u8) {
        let instruction = Instruction::from(opcode);
        let address = self.operand_address(&instruction.mode).unwrap();

        self.program_counter = address;
    }

    fn jsr(&mut self, opcode: u8) {
        let instruction = Instruction::from(opcode);
        let subroutine_address = self.operand_address(&instruction.mode).unwrap();

        self.stack_push_u16(self.program_counter + 2 - 1);

        self.program_counter = subroutine_address;
    }

    fn lda(&mut self, opcode: u8) {
        let instruction = Instruction::from(opcode);
        let address = self.operand_address(&instruction.mode).unwrap();
        let value = self.mem_read(address);
        self.register_a = value;

        self.set_zero_and_negative_flags(self.register_a);

        self.program_counter += instruction.size as u16 - 1;
    }

    fn ldx(&mut self, opcode: u8) {
        let instruction = Instruction::from(opcode);
        let address = self.operand_address(&instruction.mode).unwrap();
        let value = self.mem_read(address);
        self.register_x = value;

        self.set_zero_and_negative_flags(self.register_x);

        self.program_counter += instruction.size as u16 - 1;
    }

    fn ldy(&mut self, opcode: u8) {
        let instruction = Instruction::from(opcode);
        let address = self.operand_address(&instruction.mode).unwrap();
        let value = self.mem_read(address);
        self.register_y = value;

        self.set_zero_and_negative_flags(self.register_y);

        self.program_counter += instruction.size as u16 - 1;
    }

    fn lsr(&mut self, opcode: u8) {
        let instruction = Instruction::from(opcode);
        match instruction.mode {
            AddressingMode::Accumulator => {
                if self.register_a & 0b0000_0001 != 0 {
                    self.set_flag(StatusFlag::Carry);
                } else {
                    self.clear_flag(StatusFlag::Carry);
                }

                self.register_a = self.register_a >> 1;
                self.set_zero_and_negative_flags(self.register_a);
            }
            _ => {
                let address = self.operand_address(&instruction.mode).unwrap();
                let operand = self.mem_read(address);

                if self.register_a & 0b0000_0001 != 0 {
                    self.set_flag(StatusFlag::Carry);
                } else {
                    self.clear_flag(StatusFlag::Carry);
                }

                let res = operand >> 1;
                self.mem_write(address, res);
                self.set_zero_and_negative_flags(res);
            }
        }

        self.program_counter += instruction.size as u16 - 1;
    }

    fn nop(&mut self, opcode: u8) {
        let instruction = Instruction::from(opcode);

        self.program_counter += instruction.size as u16 - 1;
    }

    fn ora(&mut self, opcode: u8) {
        let instruction = Instruction::from(opcode);
        let address = self.operand_address(&instruction.mode).unwrap();
        let operand = self.mem_read(address);

        self.register_a |= operand;

        self.set_zero_and_negative_flags(self.register_a);

        self.program_counter += instruction.size as u16 - 1;
    }

    fn pha(&mut self, opcode: u8) {
        let instruction = Instruction::from(opcode);

        self.stack_push(self.register_a);

        self.program_counter += instruction.size as u16 - 1;
    }

    fn php(&mut self, opcode: u8) {
        let instruction = Instruction::from(opcode);

        self.stack_push(self.status);

        self.program_counter += instruction.size as u16 - 1;
    }

    fn pla(&mut self, opcode: u8) {
        let instruction = Instruction::from(opcode);

        self.register_a = self.stack_pop();
        self.set_zero_and_negative_flags(self.register_a);

        self.program_counter += instruction.size as u16 - 1;
    }

    fn plp(&mut self, opcode: u8) {
        let instruction = Instruction::from(opcode);

        self.status = self.stack_pop();

        self.program_counter += instruction.size as u16 - 1;
    }

    fn rol(&mut self, opcode: u8) {
        let instruction = Instruction::from(opcode);
        match instruction.mode {
            AddressingMode::Accumulator => {
                let old_accumulator = self.register_a;

                self.register_a = (self.register_a << 1) | (self.status & 0b0000_0001);
                self.copy_bit_from(old_accumulator >> 7, StatusFlag::Carry);

                self.set_zero_and_negative_flags(self.register_a);
            }
            _ => {
                let address = self.operand_address(&instruction.mode).unwrap();
                let operand = self.mem_read(address);

                let rotated_operand = (operand << 1) | (self.status & 0b0000_0001);
                self.copy_bit_from(operand >> 7, StatusFlag::Carry);
                self.mem_write(address, rotated_operand);

                self.set_zero_and_negative_flags(rotated_operand);
            }
        }

        self.program_counter += instruction.size as u16 - 1;
    }

    fn ror(&mut self, opcode: u8) {
        let instruction = Instruction::from(opcode);
        match instruction.mode {
            AddressingMode::Accumulator => {
                let old_accumulator = self.register_a;

                self.register_a = (self.register_a >> 1) | ((self.status & 0b0000_0001) << 7);
                self.copy_bit_from(old_accumulator, StatusFlag::Carry);

                self.set_zero_and_negative_flags(self.register_a);
            }
            _ => {
                let address = self.operand_address(&instruction.mode).unwrap();
                let operand = self.mem_read(address);

                let rotated_operand = (operand >> 1) | ((self.status & 0b0000_0001) << 7);
                self.copy_bit_from(operand, StatusFlag::Carry);
                self.mem_write(address, rotated_operand);

                self.set_zero_and_negative_flags(rotated_operand);
            }
        }

        self.program_counter += instruction.size as u16 - 1;
    }

    fn rti(&mut self, opcode: u8) {
        let instruction = Instruction::from(opcode);

        self.status = self.stack_pop();
        self.program_counter = self.stack_pop_u16();

        self.program_counter += instruction.size as u16 - 1;
    }

    fn rts(&mut self, opcode: u8) {
        let instruction = Instruction::from(opcode);

        // According to the 6502 specification, after pulling the address from the stack, the program counter should be incremented by 1.
        self.program_counter = self.stack_pop_u16() + 1;

        self.program_counter += instruction.size as u16 - 1;
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

    #[test]
    fn test_bit_zero_flag() {
        let mut cpu = CPU::new();

        // Load the BIT instruction (0x24 for Zero Page) and a memory value into Zero Page
        cpu.mem_write(0x10, 0x00); // Write 0x00 to memory location 0x10
        cpu.load(vec![0x24, 0x10]); // BIT instruction with Zero Page addressing (operand at 0x10)
        cpu.reset();
        cpu.register_a = 0xFF; // Set the accumulator to 0xFF
        cpu.interpret();

        // Since 0xFF & 0x00 = 0, the Zero flag should be set
        assert!(cpu.status & StatusFlag::Zero as u8 != 0);
    }

    #[test]
    fn test_bit_negative_flag() {
        let mut cpu = CPU::new();

        // Write a value with bit 7 set (0x80) to memory location 0x10
        cpu.mem_write(0x10, 0x80);
        cpu.load(vec![0x24, 0x10]); // BIT instruction with Zero Page addressing
        cpu.reset();
        cpu.register_a = 0xFF; // Set the accumulator to 0xFF
        cpu.interpret();

        // Since memory[0x10] has bit 7 set (0x80), the Negative flag should be set
        assert!(cpu.status & StatusFlag::Negative as u8 != 0);
    }

    #[test]
    fn test_bit_overflow_flag() {
        let mut cpu = CPU::new();

        // Write a value with bit 6 set (0x40) to memory location 0x10
        cpu.mem_write(0x10, 0x40);
        cpu.load(vec![0x24, 0x10]); // BIT instruction with Zero Page addressing
        cpu.reset();
        cpu.register_a = 0xFF; // Set the accumulator to 0xFF
        cpu.interpret();

        // Since memory[0x10] has bit 6 set (0x40), the Overflow flag should be set
        assert!(cpu.status & StatusFlag::Overflow as u8 != 0);
    }

    #[test]
    fn test_bit_no_flags_set() {
        let mut cpu = CPU::new();

        // Write a value with neither bit 6 nor bit 7 set (0x3F) to memory location 0x10
        cpu.mem_write(0x10, 0x3F);
        cpu.load(vec![0x24, 0x10]); // BIT instruction with Zero Page addressing
        cpu.reset();
        cpu.register_a = 0x01; // Set the accumulator to 0x01
        cpu.interpret();

        // Since 0x01 & 0x3F != 0, Zero flag should NOT be set
        assert!(cpu.status & StatusFlag::Zero as u8 == 0);

        // Neither bit 6 nor bit 7 are set in memory, so neither Overflow nor Negative should be set
        assert!(cpu.status & StatusFlag::Overflow as u8 == 0);
        assert!(cpu.status & StatusFlag::Negative as u8 == 0);
    }

    #[test]
    fn test_bmi_branch_taken() {
        let mut cpu = CPU::new();

        // Load the BMI instruction with a positive offset (e.g., +9)
        cpu.load(vec![0x30, 0x09]); // BMI with offset +9
        cpu.reset();
        // Set the Negative flag (so the branch should occur)
        cpu.set_flag(StatusFlag::Negative);
        let initial_pc = cpu.program_counter;
        cpu.interpret();

        // The program counter should jump forward by 12 (opcode + operand + offset (+9) + BRK)
        assert_eq!(cpu.program_counter, initial_pc.wrapping_add(12));
    }

    #[test]
    fn test_bmi_no_branch() {
        let mut cpu = CPU::new();

        // Load the BMI instruction with a positive offset (e.g., +4)
        cpu.load(vec![0x30, 0x04]); // BMI with offset +4
        cpu.reset();
        let initial_pc = cpu.program_counter;
        cpu.interpret();

        // The program counter should NOT jump, it should just move to the next instruction (opcode + operand + BRK)
        assert_eq!(cpu.program_counter, initial_pc.wrapping_add(3));
    }

    #[test]
    fn test_bne_branch_forward() {
        let mut cpu = CPU::new();

        // Load the BNE instruction with a positive offset (+4)
        cpu.load(vec![0xD0, 0x04]); // BNE (0xD0) with offset +4
        cpu.reset();
        let initial_pc = cpu.program_counter;
        cpu.interpret();

        // The program counter should move forward by 4 (opcode + offset) + 1 (BRK)
        assert_eq!(
            cpu.program_counter,
            initial_pc.wrapping_add(2).wrapping_add(5)
        );
    }

    #[test]
    fn test_bne_no_branch_when_zero_set() {
        let mut cpu = CPU::new();

        // Load the BEQ instruction with a positive offset (+4)
        cpu.load(vec![0xD0, 0x04]); // BNE (0xD0) with offset +4
        cpu.reset();
        cpu.set_flag(StatusFlag::Zero);
        let initial_pc = cpu.program_counter;
        cpu.interpret();

        // The program counter should only move forward by 2 (for the opcode and offset) and not branch + 1 (BRK)
        assert_eq!(cpu.program_counter, initial_pc.wrapping_add(3));
    }

    #[test]
    fn test_bne_branch_backward() {
        let mut cpu = CPU::new();

        // Load the BEQ instruction with a negative offset (-2)
        cpu.load(vec![0xD0, 0xFD]); // BNE (0xD0) with offset -2 (0xFE in two's complement is -2)
        cpu.reset();
        let initial_pc = cpu.program_counter;
        cpu.interpret();

        // The program counter should jump backward by 2 + 1 (BRK)
        assert_eq!(
            cpu.program_counter,
            initial_pc.wrapping_add(2).wrapping_sub(3).wrapping_add(1)
        );
    }

    #[test]
    fn test_bpl_branch_forward() {
        let mut cpu = CPU::new();

        // Load the BPL instruction with a positive offset (+4)
        cpu.load(vec![0x10, 0x04]); // BPL (0x10) with offset +4
        cpu.reset();
        let initial_pc = cpu.program_counter;
        cpu.interpret();

        // The program counter should move forward by 4 (opcode + offset) + 1 (BRK)
        assert_eq!(
            cpu.program_counter,
            initial_pc.wrapping_add(2).wrapping_add(5)
        );
    }

    #[test]
    fn test_bpl_no_branch_when_negative_set() {
        let mut cpu = CPU::new();

        // Load the BEQ instruction with a positive offset (+4)
        cpu.load(vec![0x10, 0x04]); // BPL (0x10) with offset +4
        cpu.reset();
        cpu.set_flag(StatusFlag::Negative);
        let initial_pc = cpu.program_counter;
        cpu.interpret();

        // The program counter should only move forward by 2 (for the opcode and offset) and not branch + 1 (BRK)
        assert_eq!(cpu.program_counter, initial_pc.wrapping_add(3));
    }

    #[test]
    fn test_bpl_branch_backward() {
        let mut cpu = CPU::new();

        // Load the BEQ instruction with a negative offset (-2)
        cpu.load(vec![0x10, 0xFD]); // BPL (0x10) with offset -2 (0xFE in two's complement is -2)
        cpu.reset();
        let initial_pc = cpu.program_counter;
        cpu.interpret();

        // The program counter should jump backward by 2 + 1 (BRK)
        assert_eq!(
            cpu.program_counter,
            initial_pc.wrapping_add(2).wrapping_sub(3).wrapping_add(1)
        );
    }

    #[test]
    #[should_panic(expected = "Stack overflow! Cannot push more data.")]
    fn test_stack_push_overflow() {
        let mut cpu = CPU::new();

        // Set the stack pointer to 0x00 (stack is full)
        cpu.stack_ptr = 0x00;

        // Try pushing a value when the stack is full
        // This should panic with "Stack overflow" message
        cpu.stack_push(0x42);
    }

    //  TODO:
    // #[test]
    // fn test_brk_instruction() {
    //     let mut cpu = CPU::new();
    //
    //     // Setup: Writing the IRQ vector at $FFFE/$FFFF to point to 0x1234 (interrupt handler)
    //     cpu.mem_write(0xFFFE, 0x34); // Low byte of interrupt vector
    //     cpu.mem_write(0xFFFF, 0x12); // High byte of interrupt vector
    //
    //     // Load the BRK instruction
    //     cpu.load(vec![0x00]); // 0x00 is the opcode for BRK
    //     cpu.reset();
    //
    //     // Set the program counter and accumulator to a known value
    //     cpu.program_counter = 0x1000; // Initial PC value
    //     cpu.interpret();
    //
    //     // Check that the status register was pushed to the stack
    //     // The Break (B) flag (0x10) and the unused bit (0x20) should be set in the status register.
    //     let status = cpu.stack_pop();
    //     assert_eq!(status & 0b00110000, 0b00110000); // Break (B) flag and Unused bit should be set
    //
    //     // Check that the correct PC value (next instruction address) was pushed to the stack
    //     assert_eq!(cpu.stack_pop(), 0x01); // Low byte of PC (0x1001)
    //     assert_eq!(cpu.stack_pop(), 0x10); // High byte of PC (0x1001)
    //
    //     // Check that the program counter is set to the IRQ vector (0x1234)
    //     assert_eq!(cpu.program_counter, 0x1234);
    // }

    #[test]
    fn test_bvc_branch_forward() {
        let mut cpu = CPU::new();

        // Load the BVC instruction with a positive offset (+4)
        cpu.load(vec![0x50, 0x04]); // BVC (0x50) with offset +4
        cpu.reset();
        let initial_pc = cpu.program_counter;
        cpu.interpret();

        // The program counter should move forward by 4 (opcode + offset) + 1 (BRK)
        assert_eq!(
            cpu.program_counter,
            initial_pc.wrapping_add(2).wrapping_add(5)
        );
    }

    #[test]
    fn test_bvc_no_branch_when_overflow_set() {
        let mut cpu = CPU::new();

        // Load the BVC instruction with a positive offset (+4)
        cpu.load(vec![0x50, 0x04]); // BVC (0x10) with offset +4
        cpu.reset();
        cpu.set_flag(StatusFlag::Overflow);
        let initial_pc = cpu.program_counter;
        cpu.interpret();

        // The program counter should only move forward by 2 (for the opcode and offset) and not branch + 1 (BRK)
        assert_eq!(cpu.program_counter, initial_pc.wrapping_add(3));
    }

    #[test]
    fn test_bvc_branch_backward() {
        let mut cpu = CPU::new();

        // Load the BVC instruction with a negative offset (-2)
        cpu.load(vec![0x50, 0xFD]); // BVC (0x10) with offset -2 (0xFE in two's complement is -2)
        cpu.reset();
        let initial_pc = cpu.program_counter;
        cpu.interpret();

        // The program counter should jump backward by 2 + 1 (BRK)
        assert_eq!(
            cpu.program_counter,
            initial_pc.wrapping_add(2).wrapping_sub(3).wrapping_add(1)
        );
    }

    #[test]
    fn test_bvs_branch_forward() {
        let mut cpu = CPU::new();

        // Load the BVS instruction with a positive offset (+4)
        cpu.load(vec![0x70, 0x04]); // BVS (0x70) with offset +4
        cpu.reset();
        cpu.set_flag(StatusFlag::Overflow);
        let initial_pc = cpu.program_counter;
        cpu.interpret();

        // The program counter should move forward by 4 (opcode + offset) + 1 (BRK)
        assert_eq!(
            cpu.program_counter,
            initial_pc.wrapping_add(2).wrapping_add(5)
        );
    }

    #[test]
    fn test_bvs_no_branch_when_overflow_set() {
        let mut cpu = CPU::new();

        // Load the BVS instruction with a positive offset (+4)
        cpu.load(vec![0x70, 0x04]); // BVS (0x70) with offset +4
        cpu.reset();
        let initial_pc = cpu.program_counter;
        cpu.interpret();

        // The program counter should only move forward by 2 (for the opcode and offset) and not branch + 1 (BRK)
        assert_eq!(cpu.program_counter, initial_pc.wrapping_add(3));
    }

    #[test]
    fn test_bvs_branch_backward() {
        let mut cpu = CPU::new();

        // Load the BVS instruction with a negative offset (-2)
        cpu.load(vec![0x70, 0xFD]); // BVS (0x70) with offset -2 (0xFE in two's complement is -2)
        cpu.reset();
        cpu.set_flag(StatusFlag::Overflow);
        let initial_pc = cpu.program_counter;
        cpu.interpret();

        // The program counter should jump backward by 2 + 1 (BRK)
        assert_eq!(
            cpu.program_counter,
            initial_pc.wrapping_add(2).wrapping_sub(3).wrapping_add(1)
        );
    }

    #[test]
    fn test_clc_instruction() {
        let mut cpu = CPU::new();

        // Load the CLC instruction (opcode 0x18)
        cpu.load(vec![0x18]);
        cpu.reset();
        // Set the Carry flag before running CLC
        cpu.set_flag(StatusFlag::Carry);
        assert!(cpu.status & StatusFlag::Carry as u8 != 0); // Ensure Carry flag is set
        cpu.interpret();

        assert!(cpu.status & StatusFlag::Carry as u8 == 0);
    }

    #[test]
    fn test_cld_instruction() {
        let mut cpu = CPU::new();

        // Load the CLD instruction (opcode 0xD8)
        cpu.load(vec![0xD8]);
        cpu.reset();
        // Set the Carry flag before running CLC
        cpu.set_flag(StatusFlag::Decimal);
        assert!(cpu.status & StatusFlag::Decimal as u8 != 0); // Ensure Decimal flag is set
        cpu.interpret();

        assert!(cpu.status & StatusFlag::Decimal as u8 == 0);
    }

    #[test]
    fn test_cli_instruction() {
        let mut cpu = CPU::new();

        // Load the CLI instruction (opcode 0x58)
        cpu.load(vec![0x58]);
        cpu.reset();
        // Set the Interrupt flag before running CLI
        cpu.set_flag(StatusFlag::Interrupt);
        assert!(cpu.status & StatusFlag::Interrupt as u8 != 0); // Ensure Interrupt flag is set
        cpu.interpret();

        assert!(cpu.status & StatusFlag::Interrupt as u8 == 0);
    }

    #[test]
    fn test_clv_instruction() {
        let mut cpu = CPU::new();

        // Load the CLV instruction (opcode 0xB8)
        cpu.load(vec![0xB8]);
        cpu.reset();
        // Set the Overflow flag before running CLV
        cpu.set_flag(StatusFlag::Overflow);
        assert!(cpu.status & StatusFlag::Overflow as u8 != 0); // Ensure Overflow flag is set
        cpu.interpret();

        assert!(cpu.status & StatusFlag::Overflow as u8 == 0);
    }

    #[test]
    fn test_cmp_carry_flag_set() {
        let mut cpu = CPU::new();

        // Load the CMP instruction with a value less than the accumulator
        cpu.load(vec![0xC9, 0x10]); // CMP with immediate mode, compare with 0x10
        cpu.reset();
        cpu.register_a = 0x20; // Set A to 0x20 (32 in decimal)
        cpu.interpret();

        // Carry flag should be set because A (0x20) > operand (0x10)
        assert!(cpu.status & StatusFlag::Carry as u8 != 0);
        // Zero flag should be clear
        assert!(cpu.status & StatusFlag::Zero as u8 == 0);
        // Negative flag should be clear
        assert!(cpu.status & StatusFlag::Negative as u8 == 0);
    }

    #[test]
    fn test_cmp_zero_flag_set() {
        let mut cpu = CPU::new();

        // Load the CMP instruction with a value equal to the accumulator
        cpu.load(vec![0xC9, 0x10]); // CMP with immediate mode
        cpu.reset();
        cpu.register_a = 0x10; // Set A to 0x10 (16 in decimal)
        cpu.interpret();

        // Carry flag should be set
        assert!(cpu.status & StatusFlag::Carry as u8 != 0);
        // Zero flag should be set because A == operand
        assert!(cpu.status & StatusFlag::Zero as u8 != 0);
        // Negative flag should be clear
        assert!(cpu.status & StatusFlag::Negative as u8 == 0);
    }

    #[test]
    fn test_cmp_negative_flag_set() {
        let mut cpu = CPU::new();

        // Load the CMP instruction with a value greater than the accumulator
        cpu.load(vec![0xC9, 0x20]); // CMP with immediate mode
        cpu.reset();
        cpu.register_a = 0x10; // Set A to 0x10 (16 in decimal)
        cpu.interpret();

        // Carry flag should be clear because A (0x10) < operand (0x20)
        assert!(cpu.status & StatusFlag::Carry as u8 == 0);
        // Zero flag should be clear
        assert!(cpu.status & StatusFlag::Zero as u8 == 0);
        // Negative flag should be clear
        assert!(cpu.status & StatusFlag::Negative as u8 != 0);
    }

    #[test]
    fn test_cmp_carry_flag_clear() {
        let mut cpu = CPU::new();

        // Load the CMP instruction with a value that makes the result negative
        cpu.load(vec![0xC9, 0x80]); // CMP with immediate mode
        cpu.reset();
        cpu.register_a = 0x30; // Set A to 0x30 (48 in decimal)
        cpu.interpret();

        // Carry flag should be set because A (0x30) > operand (0x80)
        assert!(cpu.status & StatusFlag::Carry as u8 == 0);
        // Zero flag should be clear
        assert!(cpu.status & StatusFlag::Zero as u8 == 0);
        // Negative flag should be set because result (0x30 - 0x80) = 0xB0 is negative
        assert!(cpu.status & StatusFlag::Negative as u8 != 0);
    }

    #[test]
    fn test_cpx_carry_flag_set() {
        let mut cpu = CPU::new();

        // Load the CPX instruction with a value less than the X register
        cpu.load(vec![0xE0, 0x10]); // CPX with immediate mode, compare with 0x10
        cpu.reset();
        cpu.register_x = 0x20; // Set X to 0x20 (32 in decimal)
        cpu.interpret();

        // Carry flag should be set because X (0x20) > operand (0x10)
        assert!(cpu.status & StatusFlag::Carry as u8 != 0);
        // Zero flag should be clear
        assert!(cpu.status & StatusFlag::Zero as u8 == 0);
        // Negative flag should be clear
        assert!(cpu.status & StatusFlag::Negative as u8 == 0);
    }

    #[test]
    fn test_cpx_zero_flag_set() {
        let mut cpu = CPU::new();

        // Load the CPX instruction with a value equal to the X register
        cpu.load(vec![0xE0, 0x10]); // CPX with immediate mode
        cpu.reset();
        cpu.register_x = 0x10; // Set X to 0x10 (16 in decimal)
        cpu.interpret();

        // Carry flag should be set
        assert!(cpu.status & StatusFlag::Carry as u8 != 0);
        // Zero flag should be set because X == operand
        assert!(cpu.status & StatusFlag::Zero as u8 != 0);
        // Negative flag should be clear
        assert!(cpu.status & StatusFlag::Negative as u8 == 0);
    }

    #[test]
    fn test_cpx_negative_flag_set() {
        let mut cpu = CPU::new();

        // Load the CPX instruction with a value greater than the X register
        cpu.load(vec![0xE0, 0x20]); // CPX with immediate mode
        cpu.reset();
        cpu.register_x = 0x10; // Set X to 0x10 (16 in decimal)
        cpu.interpret();

        // Carry flag should be clear because X (0x10) < operand (0x20)
        assert!(cpu.status & StatusFlag::Carry as u8 == 0);
        // Zero flag should be clear
        assert!(cpu.status & StatusFlag::Zero as u8 == 0);
        // Negative flag should be set because X - operand is negative
        assert!(cpu.status & StatusFlag::Negative as u8 != 0);
    }

    #[test]
    fn test_cpx_carry_flag_clear() {
        let mut cpu = CPU::new();

        // Load the CPX instruction with a value that makes the result negative
        cpu.load(vec![0xE0, 0x80]); // CPX with immediate mode
        cpu.reset();
        cpu.register_x = 0x30; // Set X to 0x30 (48 in decimal)
        cpu.interpret();

        // Carry flag should be clear because X (0x30) < operand (0x80)
        assert!(cpu.status & StatusFlag::Carry as u8 == 0);
        // Zero flag should be clear
        assert!(cpu.status & StatusFlag::Zero as u8 == 0);
        // Negative flag should be set because result (0x30 - 0x80) = 0xB0 is negative
        assert!(cpu.status & StatusFlag::Negative as u8 != 0);
    }

    #[test]
    fn test_cpy_carry_flag_set() {
        let mut cpu = CPU::new();

        // Load the CPY instruction with a value less than the Y register
        cpu.load(vec![0xC0, 0x10]); // CPY with immediate mode, compare with 0x10
        cpu.reset();
        cpu.register_y = 0x20; // Set Y to 0x20 (32 in decimal)
        cpu.interpret();

        // Carry flag should be set because Y (0x20) > operand (0x10)
        assert!(cpu.status & StatusFlag::Carry as u8 != 0);
        // Zero flag should be clear
        assert!(cpu.status & StatusFlag::Zero as u8 == 0);
        // Negative flag should be clear
        assert!(cpu.status & StatusFlag::Negative as u8 == 0);
    }

    #[test]
    fn test_cpy_zero_flag_set() {
        let mut cpu = CPU::new();

        // Load the CPY instruction with a value equal to the Y register
        cpu.load(vec![0xC0, 0x10]); // CPY with immediate mode
        cpu.reset();
        cpu.register_y = 0x10; // Set Y to 0x10 (16 in decimal)
        cpu.interpret();

        // Carry flag should be set because Y == operand
        assert!(cpu.status & StatusFlag::Carry as u8 != 0);
        // Zero flag should be set because Y == operand
        assert!(cpu.status & StatusFlag::Zero as u8 != 0);
        // Negative flag should be clear
        assert!(cpu.status & StatusFlag::Negative as u8 == 0);
    }

    #[test]
    fn test_cpy_negative_flag_set() {
        let mut cpu = CPU::new();

        // Load the CPY instruction with a value greater than the Y register
        cpu.load(vec![0xC0, 0x20]); // CPY with immediate mode
        cpu.reset();
        cpu.register_y = 0x10; // Set Y to 0x10 (16 in decimal)
        cpu.interpret();

        // Carry flag should be clear because Y (0x10) < operand (0x20)
        assert!(cpu.status & StatusFlag::Carry as u8 == 0);
        // Zero flag should be clear
        assert!(cpu.status & StatusFlag::Zero as u8 == 0);
        // Negative flag should be set because the result (Y - operand) is negative
        assert!(cpu.status & StatusFlag::Negative as u8 != 0);
    }

    #[test]
    fn test_cpy_carry_flag_clear() {
        let mut cpu = CPU::new();

        // Load the CPY instruction with a value that makes the result negative
        cpu.load(vec![0xC0, 0x80]); // CPY with immediate mode
        cpu.reset();
        cpu.register_y = 0x30; // Set Y to 0x30 (48 in decimal)
        cpu.interpret();

        // Carry flag should be clear because Y (0x30) < operand (0x80)
        assert!(cpu.status & StatusFlag::Carry as u8 == 0);
        // Zero flag should be clear
        assert!(cpu.status & StatusFlag::Zero as u8 == 0);
        // Negative flag should be set because the result (Y - operand) is negative
        assert!(cpu.status & StatusFlag::Negative as u8 != 0);
    }

    #[test]
    fn test_dec_zero_flag_set() {
        let mut cpu = CPU::new();

        // Load the DEC instruction to decrement memory at 0x10
        cpu.load(vec![0xC6, 0x10]); // DEC with Zero Page addressing
        cpu.reset();
        cpu.mem_write(0x10, 0x01); // Write 0x01 to memory location 0x10
        cpu.interpret();

        // Memory at 0x10 should be decremented from 0x01 to 0x00
        assert_eq!(cpu.mem_read(0x10), 0x00);

        // Zero flag should be set because the result is zero
        assert!(cpu.status & StatusFlag::Zero as u8 != 0);

        // Negative flag should be clear
        assert!(cpu.status & StatusFlag::Negative as u8 == 0);
    }

    #[test]
    fn test_dec_negative_flag_set() {
        let mut cpu = CPU::new();

        // Load the DEC instruction to decrement memory at 0x10
        cpu.load(vec![0xC6, 0x10]); // DEC with Zero Page addressing
        cpu.reset();
        cpu.mem_write(0x10, 0x00); // Write 0x00 to memory location 0x10
        cpu.interpret();

        // Memory at 0x10 should be decremented from 0x00 to 0xFF
        assert_eq!(cpu.mem_read(0x10), 0xFF);

        // Zero flag should be clear because the result is not zero
        assert!(cpu.status & StatusFlag::Zero as u8 == 0);

        // Negative flag should be set because the result (0xFF) is negative
        assert!(cpu.status & StatusFlag::Negative as u8 != 0);
    }

    #[test]
    fn test_dec_positive_result() {
        let mut cpu = CPU::new();

        // Load the DEC instruction to decrement memory at 0x10
        cpu.load(vec![0xC6, 0x10]); // DEC with Zero Page addressing
        cpu.reset();
        cpu.mem_write(0x10, 0x05); // Write 0x05 to memory location 0x10
        cpu.interpret();

        // Memory at 0x10 should be decremented from 0x05 to 0x04
        assert_eq!(cpu.mem_read(0x10), 0x04);

        // Zero flag should be clear because the result is not zero
        assert!(cpu.status & StatusFlag::Zero as u8 == 0);

        // Negative flag should be clear because the result (0x04) is positive
        assert!(cpu.status & StatusFlag::Negative as u8 == 0);
    }

    #[test]
    fn test_dex_zero_flag_set() {
        let mut cpu = CPU::new();

        // Load the DEX instruction (Implied mode)
        cpu.load(vec![0xCA]); // DEX instruction
        cpu.reset();
        cpu.register_x = 0x01; // Set X register to 0x01
        cpu.interpret();

        // X register should be decremented from 0x01 to 0x00
        assert_eq!(cpu.register_x, 0x00);

        // Zero flag should be set because the result is zero
        assert!(cpu.status & StatusFlag::Zero as u8 != 0);

        // Negative flag should be clear because the result is not negative
        assert!(cpu.status & StatusFlag::Negative as u8 == 0);
    }

    #[test]
    fn test_dex_negative_flag_set() {
        let mut cpu = CPU::new();

        // Load the DEX instruction (Implied mode)
        cpu.load(vec![0xCA]); // DEX instruction
        cpu.reset();
        cpu.register_x = 0x00; // Set X register to 0x00
        cpu.interpret();

        // X register should be decremented from 0x00 to 0xFF (two's complement)
        assert_eq!(cpu.register_x, 0xFF);

        // Zero flag should be clear because the result is not zero
        assert!(cpu.status & StatusFlag::Zero as u8 == 0);

        // Negative flag should be set because the result (0xFF) is negative
        assert!(cpu.status & StatusFlag::Negative as u8 != 0);
    }

    #[test]
    fn test_dex_positive_result() {
        let mut cpu = CPU::new();

        // Load the DEX instruction (Implied mode)
        cpu.load(vec![0xCA]); // DEX instruction
        cpu.reset();
        cpu.register_x = 0x05; // Set X register to 0x05
        cpu.interpret();

        // X register should be decremented from 0x05 to 0x04
        assert_eq!(cpu.register_x, 0x04);

        // Zero flag should be clear because the result is not zero
        assert!(cpu.status & StatusFlag::Zero as u8 == 0);

        // Negative flag should be clear because the result is positive
        assert!(cpu.status & StatusFlag::Negative as u8 == 0);
    }

    #[test]
    fn test_dey_zero_flag_set() {
        let mut cpu = CPU::new();

        // Load the DEY instruction (Implied mode)
        cpu.load(vec![0x88]); // DEY instruction
        cpu.reset();
        cpu.register_y = 0x01; // Set Y register to 0x01
        cpu.interpret();

        // Y register should be decremented from 0x01 to 0x00
        assert_eq!(cpu.register_y, 0x00);

        // Zero flag should be set because the result is zero
        assert!(cpu.status & StatusFlag::Zero as u8 != 0);

        // Negative flag should be clear because the result is not negative
        assert!(cpu.status & StatusFlag::Negative as u8 == 0);
    }

    #[test]
    fn test_dey_negative_flag_set() {
        let mut cpu = CPU::new();

        // Load the DEY instruction (Implied mode)
        cpu.load(vec![0x88]); // DEY instruction
        cpu.reset();
        cpu.register_y = 0x00; // Set Y register to 0x00
        cpu.interpret();

        // Y register should be decremented from 0x00 to 0xFF (two's complement)
        assert_eq!(cpu.register_y, 0xFF);

        // Zero flag should be clear because the result is not zero
        assert!(cpu.status & StatusFlag::Zero as u8 == 0);

        // Negative flag should be set because the result (0xFF) is negative
        assert!(cpu.status & StatusFlag::Negative as u8 != 0);
    }

    #[test]
    fn test_dey_positive_result() {
        let mut cpu = CPU::new();

        // Load the DEY instruction (Implied mode)
        cpu.load(vec![0x88]); // DEY instruction
        cpu.reset();
        cpu.register_y = 0x05; // Set Y register to 0x05
        cpu.interpret();

        // Y register should be decremented from 0x05 to 0x04
        assert_eq!(cpu.register_y, 0x04);

        // Zero flag should be clear because the result is not zero
        assert!(cpu.status & StatusFlag::Zero as u8 == 0);

        // Negative flag should be clear because the result is positive
        assert!(cpu.status & StatusFlag::Negative as u8 == 0);
    }

    #[test]
    fn test_eor_non_zero_result() {
        let mut cpu = CPU::new();

        // Load the EOR instruction (Immediate mode) and XOR with 0b10101010
        cpu.load(vec![0x49, 0b10101010]); // EOR #$AA
        cpu.reset();
        cpu.register_a = 0b11001100; // Set A to 0b11001100 (204 in decimal)
        cpu.interpret();

        // The result of 0b11001100 ^ 0b10101010 should be 0b01100110
        assert_eq!(cpu.register_a, 0b01100110);

        // Neither Zero nor Negative flags should be set
        assert!(cpu.status & StatusFlag::Zero as u8 == 0);
        assert!(cpu.status & StatusFlag::Negative as u8 == 0);
    }

    #[test]
    fn test_eor_zero_result() {
        let mut cpu = CPU::new();

        // Load the EOR instruction (Immediate mode) and XOR with 0xFF
        cpu.load(vec![0x49, 0xFF]); // EOR #$FF
        cpu.reset();
        cpu.register_a = 0xFF; // Set A to 0xFF (255 in decimal)
        cpu.interpret();

        // The result of 0xFF ^ 0xFF should be 0x00
        assert_eq!(cpu.register_a, 0x00);

        // Zero flag should be set
        assert!(cpu.status & StatusFlag::Zero as u8 != 0);
        // Negative flag should be clear
        assert!(cpu.status & StatusFlag::Negative as u8 == 0);
    }

    #[test]
    fn test_eor_negative_result() {
        let mut cpu = CPU::new();

        // Load the EOR instruction (Immediate mode) and XOR with 0xFF
        cpu.load(vec![0x49, 0x01]); // EOR #$01
        cpu.reset();
        cpu.register_a = 0x80; // Set A to 0x80 (128 in decimal, MSB set)
        cpu.interpret();

        // The result of 0x80 ^ 0x01 should be 0x81 (negative in two's complement)
        assert_eq!(cpu.register_a, 0x81);

        // Negative flag should be set
        assert!(cpu.status & StatusFlag::Negative as u8 != 0);
        // Zero flag should be clear
        assert!(cpu.status & StatusFlag::Zero as u8 == 0);
    }

    #[test]
    fn test_eor_zero_accumulator() {
        let mut cpu = CPU::new();

        // Load the EOR instruction (Immediate mode) and XOR with 0x55
        cpu.load(vec![0x49, 0x55]); // EOR #$55
        cpu.reset();
        cpu.register_a = 0x00; // Set A to 0x00 (accumulator is zero)
        cpu.interpret();

        // The result of 0x00 ^ 0x55 should be 0x55
        assert_eq!(cpu.register_a, 0x55);

        // Zero flag should be clear
        assert!(cpu.status & StatusFlag::Zero as u8 == 0);
        // Negative flag should be clear
        assert!(cpu.status & StatusFlag::Negative as u8 == 0);
    }

    #[test]
    fn test_inc_memory() {
        let mut cpu = CPU::new();

        // Load the INC instruction for Zero Page addressing
        cpu.load(vec![0xE6, 0x20]); // INC $20
        cpu.reset();
        // Write an initial value of 0x10 to memory location 0x20
        cpu.mem_write(0x20, 0x10);
        cpu.interpret();

        // The value at memory location 0x20 should be incremented to 0x11
        assert_eq!(cpu.mem_read(0x20), 0x11);

        // Zero flag should be clear (result is not zero)
        assert!(cpu.status & StatusFlag::Zero as u8 == 0);
        // Negative flag should be clear (result is not negative)
        assert!(cpu.status & StatusFlag::Negative as u8 == 0);
    }

    #[test]
    fn test_inc_memory_zero_result() {
        let mut cpu = CPU::new();

        // Load the INC instruction for Zero Page addressing
        cpu.load(vec![0xE6, 0x20]); // INC $20
        cpu.reset();
        // Write an initial value of 0xFF to memory location 0x20 (incrementing will wrap around)
        cpu.mem_write(0x20, 0xFF);
        cpu.interpret();

        // The value at memory location 0x20 should be incremented to 0x00 (wraps around)
        assert_eq!(cpu.mem_read(0x20), 0x00);

        // Zero flag should be set (result is zero)
        assert!(cpu.status & StatusFlag::Zero as u8 != 0);
        // Negative flag should be clear
        assert!(cpu.status & StatusFlag::Negative as u8 == 0);
    }

    #[test]
    fn test_inc_memory_negative_result() {
        let mut cpu = CPU::new();

        // Load the INC instruction for Zero Page addressing
        cpu.load(vec![0xE6, 0x20]); // INC $20
        cpu.reset();
        // Write an initial value of 0x7F to memory location 0x20
        cpu.mem_write(0x20, 0x7F);
        cpu.interpret();

        // The value at memory location 0x20 should be incremented to 0x80
        assert_eq!(cpu.mem_read(0x20), 0x80);

        // Zero flag should be clear
        assert!(cpu.status & StatusFlag::Zero as u8 == 0);
        // Negative flag should be set (result is negative)
        assert!(cpu.status & StatusFlag::Negative as u8 != 0);
    }

    #[test]
    fn test_inx_x_register() {
        let mut cpu = CPU::new();

        // Load the INC instruction for the X register
        cpu.load(vec![0xE8]); // INC X
        cpu.reset();
        cpu.register_x = 0x10; // Set X to 0x10
        cpu.interpret();

        // The value in the X register should be incremented to 0x11
        assert_eq!(cpu.register_x, 0x11);

        // Zero flag should be clear (result is not zero)
        assert!(cpu.status & StatusFlag::Zero as u8 == 0);
        // Negative flag should be clear (result is not negative)
        assert!(cpu.status & StatusFlag::Negative as u8 == 0);
    }

    #[test]
    fn test_inx_zero_result() {
        let mut cpu = CPU::new();

        // Load the INC instruction for the X register
        cpu.load(vec![0xE8]); // INC X
        cpu.reset();
        cpu.register_x = 0xFF; // Set X to 0xFF (will wrap to 0x00)
        cpu.interpret();

        // The value in the X register should be incremented to 0x00
        assert_eq!(cpu.register_x, 0x00);

        // Zero flag should be set (result is zero)
        assert!(cpu.status & StatusFlag::Zero as u8 != 0);
        // Negative flag should be clear
        assert!(cpu.status & StatusFlag::Negative as u8 == 0);
    }

    #[test]
    fn test_iny_y_register() {
        let mut cpu = CPU::new();

        // Load the INC instruction for the X register
        cpu.load(vec![0xC8]); // INC X
        cpu.reset();
        cpu.register_y = 0x10; // Set X to 0x10
        cpu.interpret();

        // The value in the X register should be incremented to 0x11
        assert_eq!(cpu.register_y, 0x11);

        // Zero flag should be clear (result is not zero)
        assert!(cpu.status & StatusFlag::Zero as u8 == 0);
        // Negative flag should be clear (result is not negative)
        assert!(cpu.status & StatusFlag::Negative as u8 == 0);
    }

    #[test]
    fn test_iny_zero_result() {
        let mut cpu = CPU::new();

        // Load the INC instruction for the X register
        cpu.load(vec![0xC8]); // INC X
        cpu.reset();
        cpu.register_y = 0xFF; // Set X to 0xFF (will wrap to 0x00)
        cpu.interpret();

        // The value in the X register should be incremented to 0x00
        assert_eq!(cpu.register_y, 0x00);

        // Zero flag should be set (result is zero)
        assert!(cpu.status & StatusFlag::Zero as u8 != 0);
        // Negative flag should be clear
        assert!(cpu.status & StatusFlag::Negative as u8 == 0);
    }

    #[test]
    fn test_jmp_absolute() {
        let mut cpu = CPU::new();

        // Load memory with JMP absolute instruction (0x4C) and target address $1234
        cpu.load(vec![0x4C, 0x34, 0x12]); // JMP $1234
        cpu.reset();
        cpu.interpret();

        // Assert that the program counter is updated to the target address ($1234) + 1 BRK
        assert_eq!(cpu.program_counter, 0x1235);
    }

    #[test]
    fn test_jmp_indirect() {
        let mut cpu = CPU::new();

        // Load memory with JMP indirect instruction (0x6C) and pointer $0120
        cpu.load(vec![0x6C, 0x20, 0x01]); // JMP ($0120)
        cpu.reset();
        // Set the memory location $0120 to point to $1234
        cpu.mem_write(0x0120, 0x34); // Low byte of target address
        cpu.mem_write(0x0121, 0x12); // High byte of target address
        cpu.interpret();

        // Assert that the program counter is updated to the target address ($1234) + 1 BRK
        assert_eq!(cpu.program_counter, 0x1235);
    }

    #[test]
    fn test_jmp_indirect_page_boundary_bug() {
        let mut cpu = CPU::new();

        // Load memory with JMP indirect instruction (0x6C) and pointer $01FF
        cpu.load(vec![0x6C, 0xFF, 0x01]); // JMP ($01FF)
        cpu.reset();
        // Set the memory location $01FF to 0x34 and simulate the bug (wrap around to $0100)
        cpu.mem_write(0x01FF, 0x34); // Low byte of target address
        cpu.mem_write(0x0100, 0x12); // High byte of target address (wrap around due to the bug)
        cpu.interpret();

        // Assert that the program counter is updated to the target address ($1234) +1 (BRK), not $12XX
        assert_eq!(cpu.program_counter, 0x1235);
    }

    #[test]
    fn test_jsr_jumps_to_subroutine() {
        let mut cpu = CPU::new();

        // Load a JSR instruction with target address $1234
        cpu.load(vec![0x20, 0x34, 0x12]); // JSR $1234
        cpu.reset();
        // Capture the initial state before JSR execution
        let initial_pc = cpu.program_counter;
        cpu.interpret();

        // After JSR, PC should be set to the target address $1234 + 1 (BRK)
        assert_eq!(cpu.program_counter, 0x1235);

        // Ensure the return address (initial_pc + 2) is pushed onto the stack
        // The return address is (initial_pc + 2). he return address pushed onto the stack is the
        // address of the last byte of the JSR instruction (which is the second byte of the
        // address), not the address of the next instruction.
        let return_address = initial_pc + 2;
        assert_eq!(cpu.stack_pop_u16(), return_address);
    }

    #[test]
    fn test_jsr_updates_stack_pointer() {
        let mut cpu = CPU::new();

        // Load a JSR instruction
        cpu.load(vec![0x20, 0x34, 0x12]); // JSR $1234
        cpu.reset();
        // CApture the initial stack pointer value
        let initial_sp = cpu.stack_ptr;
        cpu.interpret();

        // The stack pointer should be decremented by 2 after pushing the return address
        assert_eq!(cpu.stack_ptr, initial_sp.wrapping_sub(2));
    }

    #[test]
    fn test_ldx_immediate() {
        let mut cpu = CPU::new();

        // Load the LDX instruction with Immediate mode and a value to load into X
        cpu.load(vec![0xA2, 0x10]); // LDX #$10
        cpu.reset();
        cpu.interpret();

        // X register should be loaded with 0x10
        assert_eq!(cpu.register_x, 0x10);

        // Zero flag should be clear because X != 0
        assert!(cpu.status & StatusFlag::Zero as u8 == 0);

        // Negative flag should be clear because X is positive (bit 7 is 0)
        assert!(cpu.status & StatusFlag::Negative as u8 == 0);
    }

    #[test]
    fn test_ldx_zero_page() {
        let mut cpu = CPU::new();

        // Load the LDX instruction with Zero Page mode
        cpu.load(vec![0xA6, 0x10]); // LDX $10
        cpu.reset();
        // Load a value into memory at zero page address 0x10
        cpu.mem_write(0x10, 0x20);
        cpu.interpret();

        // X register should be loaded with 0x20
        assert_eq!(cpu.register_x, 0x20);

        // Zero flag should be clear because X != 0
        assert!(cpu.status & StatusFlag::Zero as u8 == 0);

        // Negative flag should be clear because X is positive (bit 7 is 0)
        assert!(cpu.status & StatusFlag::Negative as u8 == 0);
    }

    #[test]
    fn test_ldx_zero_flag() {
        let mut cpu = CPU::new();

        // Load the LDX instruction with Immediate mode and a value of 0
        cpu.load(vec![0xA2, 0x00]); // LDX #$00
        cpu.reset();
        cpu.interpret();

        // X register should be loaded with 0x00
        assert_eq!(cpu.register_x, 0x00);

        // Zero flag should be set because X == 0
        assert!(cpu.status & StatusFlag::Zero as u8 != 0);

        // Negative flag should be clear because X is not negative (bit 7 is 0)
        assert!(cpu.status & StatusFlag::Negative as u8 == 0);
    }

    #[test]
    fn test_ldx_negative_flag() {
        let mut cpu = CPU::new();

        // Load the LDX instruction with Immediate mode and a value with bit 7 set (negative number)
        cpu.load(vec![0xA2, 0xFF]); // LDX #$FF
        cpu.reset();
        cpu.interpret();

        // X register should be loaded with 0xFF
        assert_eq!(cpu.register_x, 0xFF);

        // Zero flag should be clear because X != 0
        assert!(cpu.status & StatusFlag::Zero as u8 == 0);

        // Negative flag should be set because X is negative (bit 7 is 1)
        assert!(cpu.status & StatusFlag::Negative as u8 != 0);
    }

    #[test]
    fn test_ldy_immediate() {
        let mut cpu = CPU::new();

        // Load the LDY instruction with Immediate mode and a value to load into Y
        cpu.load(vec![0xA0, 0x10]); // LDY #$10
        cpu.reset();
        cpu.interpret();

        // Y register should be loaded with 0x10
        assert_eq!(cpu.register_y, 0x10);

        // Zero flag should be clear because Y != 0
        assert!(cpu.status & StatusFlag::Zero as u8 == 0);

        // Negative flag should be clear because Y is positive (bit 7 is 0)
        assert!(cpu.status & StatusFlag::Negative as u8 == 0);
    }

    #[test]
    fn test_ldy_zero_page() {
        let mut cpu = CPU::new();

        // Load the LDY instruction with Zero Page mode
        cpu.load(vec![0xA4, 0x10]); // LDY $10
        cpu.reset();
        // Load a value into memory at zero page address 0x10
        cpu.mem_write(0x10, 0x20);
        cpu.interpret();

        // Y register should be loaded with 0x20
        assert_eq!(cpu.register_y, 0x20);

        // Zero flag should be clear because Y != 0
        assert!(cpu.status & StatusFlag::Zero as u8 == 0);

        // Negative flag should be clear because Y is positive (bit 7 is 0)
        assert!(cpu.status & StatusFlag::Negative as u8 == 0);
    }

    #[test]
    fn test_ldy_zero_flag() {
        let mut cpu = CPU::new();

        // Load the LDY instruction with Immediate mode and a value of 0
        cpu.load(vec![0xA0, 0x00]); // LDY #$00
        cpu.reset();
        cpu.interpret();

        // Y register should be loaded with 0x00
        assert_eq!(cpu.register_y, 0x00);

        // Zero flag should be set because Y == 0
        assert!(cpu.status & StatusFlag::Zero as u8 != 0);

        // Negative flag should be clear because Y is not negative (bit 7 is 0)
        assert!(cpu.status & StatusFlag::Negative as u8 == 0);
    }

    #[test]
    fn test_ldy_negative_flag() {
        let mut cpu = CPU::new();

        // Load the LDY instruction with Immediate mode and a value with bit 7 set (negative number)
        cpu.load(vec![0xA0, 0xFF]); // LDY #$FF
        cpu.reset();
        cpu.interpret();

        // Y register should be loaded with 0xFF
        assert_eq!(cpu.register_y, 0xFF);

        // Zero flag should be clear because Y != 0
        assert!(cpu.status & StatusFlag::Zero as u8 == 0);

        // Negative flag should be set because Y is negative (bit 7 is 1)
        assert!(cpu.status & StatusFlag::Negative as u8 != 0);
    }

    #[test]
    fn test_lsr_accumulator() {
        let mut cpu = CPU::new();

        // Load the LSR instruction for Accumulator mode
        cpu.load(vec![0x4A]); // LSR A
        cpu.reset();
        cpu.register_a = 0x04; // Set the accumulator to 0x04 (binary: 00000100)
        cpu.interpret();

        // Accumulator should be shifted right (0x04 >> 1 = 0x02)
        assert_eq!(cpu.register_a, 0x02);

        // Carry flag should be clear because bit 0 of 0x04 is 0
        assert!(cpu.status & StatusFlag::Carry as u8 == 0);

        // Zero flag should be clear because the result is not zero
        assert!(cpu.status & StatusFlag::Zero as u8 == 0);

        // Negative flag should be clear because bit 7 is 0
        assert!(cpu.status & StatusFlag::Negative as u8 == 0);
    }

    #[test]
    fn test_lsr_carry_flag_set() {
        let mut cpu = CPU::new();

        // Load the LSR instruction for Accumulator mode
        cpu.load(vec![0x4A]); // LSR A
        cpu.reset();
        cpu.register_a = 0x03; // Set the accumulator to 0x03 (binary: 00000011)
        cpu.interpret();

        // Accumulator should be shifted right (0x03 >> 1 = 0x01)
        assert_eq!(cpu.register_a, 0x01);

        // Carry flag should be set because bit 0 of 0x03 is 1
        assert!(cpu.status & StatusFlag::Carry as u8 != 0);

        // Zero flag should be clear because the result is not zero
        assert!(cpu.status & StatusFlag::Zero as u8 == 0);

        // Negative flag should be clear because bit 7 is 0
        assert!(cpu.status & StatusFlag::Negative as u8 == 0);
    }

    #[test]
    fn test_lsr_zero_flag_set() {
        let mut cpu = CPU::new();

        // Load the LSR instruction for Accumulator mode
        cpu.load(vec![0x4A]); // LSR A
        cpu.reset();
        cpu.register_a = 0x01; // Set the accumulator to 0x01 (binary: 00000001)
        cpu.interpret();

        // Accumulator should be shifted right (0x01 >> 1 = 0x00)
        assert_eq!(cpu.register_a, 0x00);

        // Carry flag should be set because bit 0 of 0x01 is 1
        assert!(cpu.status & StatusFlag::Carry as u8 != 0);

        // Zero flag should be set because the result is 0
        assert!(cpu.status & StatusFlag::Zero as u8 != 0);

        // Negative flag should be clear because bit 7 is 0
        assert!(cpu.status & StatusFlag::Negative as u8 == 0);
    }

    #[test]
    fn test_lsr_zero_page() {
        let mut cpu = CPU::new();

        // Load the LSR instruction for Zero Page mode
        cpu.load(vec![0x46, 0x10]); // LSR $10
        cpu.reset();
        // Write a value to Zero Page memory at address 0x10
        cpu.mem_write(0x10, 0x08); // Set memory[0x10] = 0x08 (binary: 00001000)
        cpu.interpret();

        // The value at 0x10 should be shifted right (0x08 >> 1 = 0x04)
        assert_eq!(cpu.mem_read(0x10), 0x04);

        // Carry flag should be clear because bit 0 of 0x08 is 0
        assert!(cpu.status & StatusFlag::Carry as u8 == 0);

        // Zero flag should be clear because the result is not zero
        assert!(cpu.status & StatusFlag::Zero as u8 == 0);

        // Negative flag should be clear because bit 7 is 0
        assert!(cpu.status & StatusFlag::Negative as u8 == 0);
    }

    #[test]
    fn test_nop() {
        let mut cpu = CPU::new();

        // Load the NOP instruction (0xEA) into the program memory
        cpu.load(vec![0xEA]); // NOP
        cpu.reset();
        let initial_pc = cpu.program_counter; // Save the initial program counter
        cpu.interpret();

        // The program counter should increment by 1 (NOP is a 1-byte instruction) + 1 (BRK)
        assert_eq!(cpu.program_counter, initial_pc + 2);

        // No flags should be modified, so we check if the status register remains the same
        assert_eq!(cpu.status, 0);
    }

    #[test]
    fn test_nop_multiple() {
        let mut cpu = CPU::new();

        // Load multiple NOP instructions into the program memory
        cpu.load(vec![0xEA, 0xEA, 0xEA]); // NOP, NOP, NOP
        cpu.reset();
        let initial_pc = cpu.program_counter; // Save the initial program counter
        cpu.interpret();

        // The program counter should increment by 3 (since we executed 3 NOPs) + 1 (BRK)
        assert_eq!(cpu.program_counter, initial_pc + 4);

        // No flags should be modified, so we check if the status register remains the same
        assert_eq!(cpu.status, 0);
    }

    #[test]
    fn test_ora_zero_result() {
        let mut cpu = CPU::new();

        // Load the ORA instruction (0x09) with immediate addressing mode
        cpu.load(vec![0x09, 0x00]); // ORA #$00 (A | 0x00)
        cpu.reset();
        cpu.register_a = 0x00; // Set accumulator to 0x00
        cpu.interpret();

        // The result should be 0x00 (0x00 | 0x00 = 0x00)
        assert_eq!(cpu.register_a, 0x00);

        // Zero flag should be set because the result is zero
        assert!(cpu.status & StatusFlag::Zero as u8 != 0);

        // Negative flag should be clear because the result is not negative
        assert!(cpu.status & StatusFlag::Negative as u8 == 0);
    }

    #[test]
    fn test_ora_non_zero_result() {
        let mut cpu = CPU::new();

        // Load the ORA instruction (0x09) with immediate addressing mode
        cpu.load(vec![0x09, 0x0F]); // ORA #$0F (A | 0x0F)
        cpu.reset();
        cpu.register_a = 0xF0; // Set accumulator to 0xF0
        cpu.interpret();

        // The result should be 0xFF (0xF0 | 0x0F = 0xFF)
        assert_eq!(cpu.register_a, 0xFF);

        // Zero flag should be clear because the result is not zero
        assert!(cpu.status & StatusFlag::Zero as u8 == 0);

        // Negative flag should be set because the result is negative (0xFF has the high bit set)
        assert!(cpu.status & StatusFlag::Negative as u8 != 0);
    }

    #[test]
    fn test_ora_zero_flag_clear() {
        let mut cpu = CPU::new();

        // Load the ORA instruction (0x09) with immediate addressing mode
        cpu.load(vec![0x09, 0x0F]); // ORA #$0F
        cpu.reset();

        cpu.register_a = 0x10; // Set accumulator to 0x10

        cpu.interpret();

        // The result should be 0x1F (0x10 | 0x0F = 0x1F)
        assert_eq!(cpu.register_a, 0x1F);

        // Zero flag should be clear because the result is non-zero
        assert!(cpu.status & StatusFlag::Zero as u8 == 0);

        // Negative flag should be clear because the result is positive
        assert!(cpu.status & StatusFlag::Negative as u8 == 0);
    }

    #[test]
    fn test_ora_negative_flag_set() {
        let mut cpu = CPU::new();

        // Load the ORA instruction (0x09) with immediate addressing mode
        cpu.load(vec![0x09, 0x80]); // ORA #$80 (A | 0x80)
        cpu.reset();
        cpu.register_a = 0x00; // Set accumulator to 0x00
        cpu.interpret();

        // The result should be 0x80 (0x00 | 0x80 = 0x80)
        assert_eq!(cpu.register_a, 0x80);

        // Zero flag should be clear because the result is non-zero
        assert!(cpu.status & StatusFlag::Zero as u8 == 0);

        // Negative flag should be set because the result is negative (0x80 has the high bit set)
        assert!(cpu.status & StatusFlag::Negative as u8 != 0);
    }

    #[test]
    fn test_pha() {
        let mut cpu = CPU::new();

        // Load the PHA instruction (0x48)
        cpu.load(vec![0x48]); // PHA (Push Accumulator)
        cpu.reset();
        cpu.register_a = 0x42; // Set accumulator to 0x42
        let initial_sp = cpu.stack_ptr; // Store the initial stack pointer
        cpu.interpret();

        // The accumulator value should be pushed onto the stack
        let stack_address = 0x0100 + initial_sp as u16;
        assert_eq!(cpu.mem_read(stack_address), 0x42);

        // The stack pointer should be decremented by 1
        assert_eq!(cpu.stack_ptr, initial_sp.wrapping_sub(1));
    }

    #[test]
    fn test_php() {
        let mut cpu = CPU::new();

        // Load the PHP instruction (0x08)
        cpu.load(vec![0x08]); // PHP (Push Processor Status)
        cpu.reset();
        // Set some status flags: Carry, Zero, and Negative
        cpu.set_flag(StatusFlag::Carry);
        cpu.set_flag(StatusFlag::Zero);
        cpu.set_flag(StatusFlag::Negative);

        let initial_sp = cpu.stack_ptr; // Store the initial stack pointer
        cpu.interpret();

        // The status register should be pushed onto the stack
        let pushed_status = cpu.mem_read(0x0100 + initial_sp as u16);
        let expected_status =
            StatusFlag::Carry as u8 | StatusFlag::Zero as u8 | StatusFlag::Negative as u8;

        // Assert the pushed status includes all set flags plus the Break flag
        assert_eq!(pushed_status, expected_status);

        // The stack pointer should be decremented by 1
        assert_eq!(cpu.stack_ptr, initial_sp.wrapping_sub(1));
    }

    #[test]
    fn test_pla_pulls_value_from_stack() {
        let mut cpu = CPU::new();

        // Load the PLA instruction (0x68)
        cpu.load(vec![0x68]); // PLA (Pull Accumulator)
        cpu.reset();
        let initial_sp = cpu.stack_ptr; // Store the initial stack pointer
        let value_to_pull = 0x42; // Manually push a value onto the stack (simulating a previous PHA or other operation)
        cpu.stack_ptr = 0xFD; // Set the stack pointer to a position where the value is stored
        cpu.mem_write(0x0100 + cpu.stack_ptr as u16 + 1, value_to_pull);
        cpu.interpret();

        // The accumulator should now contain the value that was on the stack
        assert_eq!(cpu.register_a, value_to_pull);

        // The stack pointer should be incremented by 1
        assert_eq!(cpu.stack_ptr, initial_sp.wrapping_add(1));
    }

    #[test]
    fn test_pla_sets_zero_flag() {
        let mut cpu = CPU::new();

        // Load the PLA instruction (0x68)
        cpu.load(vec![0x68]); // PLA (Pull Accumulator)
        cpu.reset();
        // Push 0x00 onto the stack to simulate a value previously placed there
        cpu.stack_ptr = 0xFD;
        cpu.mem_write(0x0100 + cpu.stack_ptr as u16 + 1, 0x00); // Push 0x00 onto the stack
        cpu.interpret();

        // Accumulator should be 0, and the Zero flag should be set
        assert_eq!(cpu.register_a, 0x00);
        assert!(cpu.status & StatusFlag::Zero as u8 != 0);
    }

    #[test]
    fn test_pla_sets_negative_flag() {
        let mut cpu = CPU::new();

        // Load the PLA instruction (0x68)
        cpu.load(vec![0x68]); // PLA (Pull Accumulator)
        cpu.reset();
        // Push a negative value (e.g., 0x80) onto the stack to simulate a value previously placed there
        cpu.stack_ptr = 0xFD;
        cpu.mem_write(0x0100 + cpu.stack_ptr as u16 + 1, 0x80); // Push 0x80 (signed -128) onto the stack
        cpu.interpret();

        // Accumulator should now be 0x80, and the Negative flag should be set
        assert_eq!(cpu.register_a, 0x80);
        assert!(cpu.status & StatusFlag::Negative as u8 != 0);
    }

    #[test]
    fn test_plp() {
        let mut cpu = CPU::new();

        // Load the PLP instruction (0x28)
        cpu.load(vec![0x28]); // PLP (Pull Processor Status)
        cpu.reset();
        cpu.status = 0b0001_0011;

        // Push a value onto the stack that we will later pull into the processor status
        let status_to_pull = 0b1100_0110; // Example value with some flags set
        cpu.stack_ptr = 0xFD; // Set the stack pointer to a position where we simulate the value is stored
        cpu.mem_write(0x0100 + cpu.stack_ptr as u16 + 1, status_to_pull);
        cpu.interpret();

        // The processor status register should now contain the value pulled from the stack
        assert_eq!(cpu.status, status_to_pull);
    }

    #[test]
    fn test_rol_accumulator_no_carry() {
        let mut cpu = CPU::new();

        // Load ROL instruction for Accumulator mode (0x2A)
        cpu.load(vec![0x2A]); // ROL Accumulator
        cpu.reset();
        cpu.register_a = 0b01010101; // Initial value in accumulator (0x55)
        cpu.interpret();

        // After ROL, the value should shift left, and LSB should be 0
        assert_eq!(cpu.register_a, 0b10101010); // Result should be 0xAA

        // Carry flag should be clear since the MSB was 0
        assert!(cpu.status & StatusFlag::Carry as u8 == 0);
        // Negative flag should be set because MSB of result is 1
        assert!(cpu.status & StatusFlag::Negative as u8 != 0);
        // Zero flag should be clear since result is non-zero
        assert!(cpu.status & StatusFlag::Zero as u8 == 0);
    }

    #[test]
    fn test_rol_accumulator_with_carry() {
        let mut cpu = CPU::new();

        // Load ROL instruction for Accumulator mode (0x2A)
        cpu.load(vec![0x2A]); // ROL Accumulator
        cpu.reset();
        cpu.register_a = 0b11010101; // Initial value in accumulator (0xD5)
        cpu.interpret();

        // After ROL, the value should shift left, and MSB will go to the Carry flag
        assert_eq!(cpu.register_a, 0b10101010); // Result should be 0xAA

        // Carry flag should be set since the MSB was 1 before rotation
        assert!(cpu.status & StatusFlag::Carry as u8 != 0);
        // Negative flag should be set because MSB of result is 1
        assert!(cpu.status & StatusFlag::Negative as u8 != 0);
        // Zero flag should be clear since result is non-zero
        assert!(cpu.status & StatusFlag::Zero as u8 == 0);
    }

    #[test]
    fn test_rol_accumulator_with_existing_carry() {
        let mut cpu = CPU::new();

        // Load ROL instruction for Accumulator mode (0x2A)
        cpu.load(vec![0x2A]); // ROL Accumulator
        cpu.reset();
        cpu.register_a = 0b01010101; // Initial value in accumulator (0x55)
        cpu.set_flag(StatusFlag::Carry); // Set Carry flag
        cpu.interpret();

        // After ROL, the value should shift left, and Carry flag value should be placed into the LSB
        assert_eq!(cpu.register_a, 0b10101011); // Result should be 0xAB

        // Carry flag should be clear since the MSB was 0
        assert!(cpu.status & StatusFlag::Carry as u8 == 0);
        // Negative flag should be set because MSB of result is 1
        assert!(cpu.status & StatusFlag::Negative as u8 != 0);
        // Zero flag should be clear since result is non-zero
        assert!(cpu.status & StatusFlag::Zero as u8 == 0);
    }

    #[test]
    fn test_rol_zero_page() {
        let mut cpu = CPU::new();

        // Load ROL instruction for Zero Page mode (0x26)
        cpu.load(vec![0x26, 0x10]); // ROL Zero Page address 0x10
        cpu.reset();
        cpu.mem_write(0x10, 0b01010101); // Initial value in memory (0x55)
        cpu.interpret();

        // After ROL, the value should shift left, and LSB should be 0
        assert_eq!(cpu.mem_read(0x10), 0b10101010); // Result should be

        // Carry flag should be clear since the MSB was 0
        assert!(cpu.status & StatusFlag::Carry as u8 == 0);
        // Negative flag should be set because MSB of result is 1
        assert!(cpu.status & StatusFlag::Negative as u8 != 0);
        // Zero flag should be clear since result is non-zero
        assert!(cpu.status & StatusFlag::Zero as u8 == 0);
    }

    #[test]
    fn test_rol_zero_page_with_carry() {
        let mut cpu = CPU::new();

        // Load ROL instruction for Zero Page mode (0x26)
        cpu.load(vec![0x26, 0x10]); // ROL Zero Page address 0x10
        cpu.reset();
        cpu.mem_write(0x10, 0b11010101); // Initial value in memory (0xD5)
        cpu.interpret();

        // After ROL, the value should shift left, and MSB will go to the Carry flag
        assert_eq!(cpu.mem_read(0x10), 0b10101010); // Result should be 0xAA

        // Carry flag should be set since the MSB was 1 before rotation
        assert!(cpu.status & StatusFlag::Carry as u8 != 0);
        // Negative flag should be set because MSB of result is 1
        assert!(cpu.status & StatusFlag::Negative as u8 != 0);
        // Zero flag should be clear since result is non-zero
        assert!(cpu.status & StatusFlag::Zero as u8 == 0);
    }

    #[test]
    fn test_rol_zero_flag_set() {
        let mut cpu = CPU::new();

        // Load ROL instruction for Accumulator mode (0x2A)
        cpu.load(vec![0x2A]); // ROL Accumulator
        cpu.reset();
        cpu.register_a = 0b00000000; // Initial value in accumulator (0x00)
        cpu.interpret();

        // After ROL, the value is still zero
        assert_eq!(cpu.register_a, 0b00000000); // Result should be 0x00

        // Carry flag should be clear since the MSB was 0
        assert!(cpu.status & StatusFlag::Carry as u8 == 0);
        // Negative flag should be clear since the MSB is 0
        assert!(cpu.status & StatusFlag::Negative as u8 == 0);
        // Zero flag should be set because result is zero
        assert!(cpu.status & StatusFlag::Zero as u8 != 0);
    }

    #[test]
    fn test_ror_accumulator_no_carry() {
        let mut cpu = CPU::new();

        // Load ROR instruction for Accumulator mode (0x6A)
        cpu.load(vec![0x6A]); // ROR Accumulator
        cpu.reset();
        cpu.register_a = 0b10101010; // Initial value in accumulator (0xAA)
        cpu.interpret();

        // After ROR, the value should shift right, and MSB should be 0
        assert_eq!(cpu.register_a, 0b01010101); // Result should be 0x55

        // Carry flag should be set since the LSB was 1 before rotation
        assert!(cpu.status & StatusFlag::Carry as u8 == 0);
        // Negative flag should be clear since the MSB of the result is 0
        assert!(cpu.status & StatusFlag::Negative as u8 == 0);
        // Zero flag should be clear since result is non-zero
        assert!(cpu.status & StatusFlag::Zero as u8 == 0);
    }

    #[test]
    fn test_ror_accumulator_with_carry() {
        let mut cpu = CPU::new();

        // Load ROR instruction for Accumulator mode (0x6A)
        cpu.load(vec![0x6A]); // ROR Accumulator
        cpu.reset();
        cpu.register_a = 0b10101010; // Initial value in accumulator (0xAA)
        cpu.set_flag(StatusFlag::Carry); // Set Carry flag
        cpu.interpret();

        // After ROR, the value should shift right, and Carry flag value should be placed into the MSB
        assert_eq!(cpu.register_a, 0b11010101); // Result should be 0xD5

        // Carry flag should be clear since the LSB was 0
        assert!(cpu.status & StatusFlag::Carry as u8 == 0);
        // Negative flag should be set because the MSB of result is 1
        assert!(cpu.status & StatusFlag::Negative as u8 != 0);
        // Zero flag should be clear since result is non-zero
        assert!(cpu.status & StatusFlag::Zero as u8 == 0);
    }

    #[test]
    fn test_ror_accumulator_with_existing_carry() {
        let mut cpu = CPU::new();

        // Load ROR instruction for Accumulator mode (0x6A)
        cpu.load(vec![0x6A]); // ROR Accumulator
        cpu.reset();
        cpu.register_a = 0b10101010; // Initial value in accumulator (0xAA)
        cpu.set_flag(StatusFlag::Carry); // Set Carry flag
        cpu.interpret();

        // After ROR, the value should shift right, and Carry flag should move into MSB
        assert_eq!(cpu.register_a, 0b11010101); // Result should be 0xD5

        // Carry flag should be clear since the LSB was 0
        assert!(cpu.status & StatusFlag::Carry as u8 == 0);
        // Negative flag should be set because the MSB of result is 1
        assert!(cpu.status & StatusFlag::Negative as u8 != 0);
        // Zero flag should be clear since result is non-zero
        assert!(cpu.status & StatusFlag::Zero as u8 == 0);
    }

    #[test]
    fn test_ror_zero_page() {
        let mut cpu = CPU::new();

        // Load ROR instruction for Zero Page mode (0x66)
        cpu.load(vec![0x66, 0x10]); // ROR Zero Page address 0x10
        cpu.reset();
        cpu.mem_write(0x10, 0b10101010); // Initial value in memory (0xAA)
        cpu.interpret();

        // After ROR, the value should shift right, and MSB should be 0
        assert_eq!(cpu.mem_read(0x10), 0b01010101); // Result should be 0x55

        // Carry flag should be set since the LSB was 1 before rotation
        assert!(cpu.status & StatusFlag::Carry as u8 == 0);
        // Negative flag should be clear since the MSB of result is 0
        assert!(cpu.status & StatusFlag::Negative as u8 == 0);
        // Zero flag should be clear since result is non-zero
        assert!(cpu.status & StatusFlag::Zero as u8 == 0);
    }

    #[test]
    fn test_ror_zero_page_with_carry() {
        let mut cpu = CPU::new();

        // Load ROR instruction for Zero Page mode (0x66)
        cpu.load(vec![0x66, 0x10]); // ROR Zero Page address 0x10
        cpu.reset();
        cpu.mem_write(0x10, 0b10101010); // Initial value in memory (0xAA)
        cpu.set_flag(StatusFlag::Carry); // Set Carry flag
        cpu.interpret();

        // After ROR, the value should shift right, and MSB will take the carry flag
        assert_eq!(cpu.mem_read(0x10), 0b11010101); // Result should be 0xD5

        // Carry flag should be clear since the LSB was 0
        assert!(cpu.status & StatusFlag::Carry as u8 == 0);
        // Negative flag should be set since MSB of result is 1
        assert!(cpu.status & StatusFlag::Negative as u8 != 0);
        // Zero flag should be clear since result is non-zero
        assert!(cpu.status & StatusFlag::Zero as u8 == 0);
    }

    #[test]
    fn test_ror_accumulator_zero_flag_set() {
        let mut cpu = CPU::new();

        // Load ROR instruction for Accumulator mode (0x6A)
        cpu.load(vec![0x6A]); // ROR Accumulator
        cpu.reset();
        cpu.register_a = 0b00000000; // Initial value in accumulator (0x00)
        cpu.interpret();

        // After ROR, the value is still zero
        assert_eq!(cpu.register_a, 0b00000000); // Result should be 0x00

        // Carry flag should be clear since the LSB was 0
        assert!(cpu.status & StatusFlag::Carry as u8 == 0);
        // Negative flag should be clear since MSB is 0
        assert!(cpu.status & StatusFlag::Negative as u8 == 0);
        // Zero flag should be set because result is zero
        assert!(cpu.status & StatusFlag::Zero as u8 != 0);
    }

    #[test]
    fn test_rti() {
        let mut cpu = CPU::new();

        // Execute RTI instruction
        cpu.load(vec![0x40]); // Load RTI opcode
        cpu.reset();
        // Set processor status flags
        cpu.set_flag(StatusFlag::Carry);
        cpu.set_flag(StatusFlag::Zero); // Set Zero flag
        cpu.set_flag(StatusFlag::Negative); // Set Negative flag

        // Simulate pushing a return address onto the stack
        cpu.stack_ptr = 0xF0;

        // Push the status onto the stack
        cpu.mem_write(0x01F1, cpu.status); // Push status
        cpu.mem_write(0x01F2, 0x34); // High byte of return address (0x0034)
        cpu.mem_write(0x01F3, 0x12); // Low byte of return address (0x1234)

        // Clear some flags
        cpu.clear_flag(StatusFlag::Carry);
        cpu.clear_flag(StatusFlag::Zero);
        cpu.clear_flag(StatusFlag::Negative);
        cpu.interpret();

        // Check that the program counter is set to the return address + 1 (BRK)
        assert_eq!(cpu.program_counter, 0x1235);

        // Check that the processor status is restored
        assert_eq!(cpu.status, 0b10000011); // Both Carry and Zero flags should be set
    }

    #[test]
    fn test_rts() {
        let mut cpu = CPU::new();

        // Execute RTS instruction
        cpu.load(vec![0x60]); // Load RTS opcode
        cpu.reset();

        // Simulate pushing a return address onto the stack
        cpu.stack_ptr = 0xF1;

        // Push the status onto the stack
        cpu.mem_write(0x01F2, 0x34); // High byte of return address (0x0034)
        cpu.mem_write(0x01F3, 0x12); // Low byte of return address (0x1234)
        cpu.interpret();

        // Check that the program counter is set to the return address + 1 (from spec) + 1 (BRK)
        assert_eq!(cpu.program_counter, 0x1236);
    }
}
