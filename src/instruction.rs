use core::panic;

#[derive(Debug)]
pub struct Instruction {
    opcode: u8,
    mnemonic: Mnemonic,
    pub mode: AddressingMode,
    pub size: u8,
    cycles: u8,
}

#[derive(Debug)]
enum Mnemonic {
    ADC,
    LDA,
    STA,
    TAX,
    INC,
}

#[derive(Debug)]
#[allow(non_camel_case_types)]
pub enum AddressingMode {
    Implied,
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

impl From<u8> for Instruction {
    fn from(opcode: u8) -> Self {
        match opcode {
            // ADC
            0x69 => Instruction {
                opcode,
                mnemonic: Mnemonic::ADC,
                mode: AddressingMode::Immediate,
                size: 2,
                cycles: 2,
            },
            0x65 => Instruction {
                opcode,
                mnemonic: Mnemonic::ADC,
                mode: AddressingMode::ZeroPage,
                size: 2,
                cycles: 3,
            },
            0x75 => Instruction {
                opcode,
                mnemonic: Mnemonic::ADC,
                mode: AddressingMode::ZeroPage_X,
                size: 2,
                cycles: 4,
            },
            0x6D => Instruction {
                opcode,
                mnemonic: Mnemonic::ADC,
                mode: AddressingMode::Absolute,
                size: 3,
                cycles: 4,
            },
            0x7D => Instruction {
                opcode,
                mnemonic: Mnemonic::ADC,
                mode: AddressingMode::Absolute_X,
                size: 3,
                cycles: 4,
            },
            0x79 => Instruction {
                opcode,
                mnemonic: Mnemonic::ADC,
                mode: AddressingMode::Absolute_Y,
                size: 3,
                cycles: 4,
            },
            0x61 => Instruction {
                opcode,
                mnemonic: Mnemonic::ADC,
                mode: AddressingMode::Indirect_X,
                size: 2,
                cycles: 6,
            },
            0x71 => Instruction {
                opcode,
                mnemonic: Mnemonic::ADC,
                mode: AddressingMode::Indirect_Y,
                size: 2,
                cycles: 5,
            },
            // LDA
            0xA9 => Instruction {
                opcode,
                mnemonic: Mnemonic::LDA,
                mode: AddressingMode::Immediate,
                size: 2,
                cycles: 2,
            },
            0xA5 => Instruction {
                opcode,
                mnemonic: Mnemonic::LDA,
                mode: AddressingMode::ZeroPage,
                size: 2,
                cycles: 3,
            },
            0xB5 => Instruction {
                opcode,
                mnemonic: Mnemonic::LDA,
                mode: AddressingMode::ZeroPage_X,
                size: 2,
                cycles: 4,
            },
            0xAD => Instruction {
                opcode,
                mnemonic: Mnemonic::LDA,
                mode: AddressingMode::Absolute,
                size: 3,
                cycles: 4,
            },
            0xBD => Instruction {
                opcode,
                mnemonic: Mnemonic::LDA,
                mode: AddressingMode::Absolute_X,
                size: 3,
                cycles: 4,
            },
            0xB9 => Instruction {
                opcode,
                mnemonic: Mnemonic::LDA,
                mode: AddressingMode::Absolute_Y,
                size: 3,
                cycles: 4,
            },
            0xA1 => Instruction {
                opcode,
                mnemonic: Mnemonic::LDA,
                mode: AddressingMode::Indirect_X,
                size: 2,
                cycles: 6,
            },
            0xB1 => Instruction {
                opcode,
                mnemonic: Mnemonic::LDA,
                mode: AddressingMode::Indirect_Y,
                size: 2,
                cycles: 5,
            },
            // STA
            0x85 => Instruction {
                opcode,
                mnemonic: Mnemonic::STA,
                mode: AddressingMode::ZeroPage,
                size: 2,
                cycles: 3,
            },
            0x95 => Instruction {
                opcode,
                mnemonic: Mnemonic::STA,
                mode: AddressingMode::ZeroPage_X,
                size: 2,
                cycles: 4,
            },
            0x8D => Instruction {
                opcode,
                mnemonic: Mnemonic::STA,
                mode: AddressingMode::Absolute,
                size: 3,
                cycles: 4,
            },
            0x9D => Instruction {
                opcode,
                mnemonic: Mnemonic::STA,
                mode: AddressingMode::Absolute_X,
                size: 3,
                cycles: 5,
            },
            0x99 => Instruction {
                opcode,
                mnemonic: Mnemonic::STA,
                mode: AddressingMode::Absolute_Y,
                size: 3,
                cycles: 5,
            },
            0x81 => Instruction {
                opcode,
                mnemonic: Mnemonic::STA,
                mode: AddressingMode::Indirect_X,
                size: 2,
                cycles: 6,
            },
            0x91 => Instruction {
                opcode,
                mnemonic: Mnemonic::STA,
                mode: AddressingMode::Indirect_Y,
                size: 2,
                cycles: 6,
            },
            // TAX
            0xAA => Instruction {
                opcode,
                mnemonic: Mnemonic::TAX,
                mode: AddressingMode::Implied,
                size: 1,
                cycles: 2,
            },
            // INC
            0xE8 => Instruction {
                opcode,
                mnemonic: Mnemonic::INC,
                mode: AddressingMode::Implied,
                size: 1,
                cycles: 2,
            },
            _ => panic!("Unknown opcode {}", opcode),
        }
    }
}
