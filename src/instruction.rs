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
    AND,
    ASL,
    BCC,
    BCS,
    BEQ,
    BIT,
    BMI,
    BNE,
    BPL,
    BRK,
    BVC,
    BVS,
    CLC,
    CLD,
    CLI,
    CLV,
    CMP,
    CPX,
    CPY,
    DEC,
    DEX,
    DEY,
    EOR,
    LDA,
    STA,
    TAX,
    INC,
}

#[derive(Debug)]
#[allow(non_camel_case_types)]
pub enum AddressingMode {
    Implied,
    Accumulator,
    Immediate,
    ZeroPage,
    ZeroPage_X,
    ZeroPage_Y,
    Relative,
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
            // AND
            0x29 => Instruction {
                opcode,
                mnemonic: Mnemonic::AND,
                mode: AddressingMode::Immediate,
                size: 2,
                cycles: 2,
            },
            0x25 => Instruction {
                opcode,
                mnemonic: Mnemonic::AND,
                mode: AddressingMode::ZeroPage,
                size: 2,
                cycles: 3,
            },
            0x35 => Instruction {
                opcode,
                mnemonic: Mnemonic::AND,
                mode: AddressingMode::ZeroPage_X,
                size: 2,
                cycles: 4,
            },
            0x2D => Instruction {
                opcode,
                mnemonic: Mnemonic::AND,
                mode: AddressingMode::Absolute,
                size: 3,
                cycles: 4,
            },
            0x3D => Instruction {
                opcode,
                mnemonic: Mnemonic::AND,
                mode: AddressingMode::Absolute_X,
                size: 3,
                cycles: 4,
            },
            0x39 => Instruction {
                opcode,
                mnemonic: Mnemonic::AND,
                mode: AddressingMode::Absolute_Y,
                size: 3,
                cycles: 4,
            },
            0x21 => Instruction {
                opcode,
                mnemonic: Mnemonic::AND,
                mode: AddressingMode::Indirect_X,
                size: 2,
                cycles: 6,
            },
            0x31 => Instruction {
                opcode,
                mnemonic: Mnemonic::AND,
                mode: AddressingMode::Indirect_Y,
                size: 2,
                cycles: 5,
            },
            // ASL
            0x0A => Instruction {
                opcode,
                mnemonic: Mnemonic::ASL,
                mode: AddressingMode::Accumulator,
                size: 1,
                cycles: 2,
            },
            0x06 => Instruction {
                opcode,
                mnemonic: Mnemonic::ASL,
                mode: AddressingMode::ZeroPage,
                size: 2,
                cycles: 5,
            },
            0x16 => Instruction {
                opcode,
                mnemonic: Mnemonic::ASL,
                mode: AddressingMode::ZeroPage_X,
                size: 2,
                cycles: 6,
            },
            0x0E => Instruction {
                opcode,
                mnemonic: Mnemonic::ASL,
                mode: AddressingMode::Absolute,
                size: 3,
                cycles: 6,
            },
            0x1E => Instruction {
                opcode,
                mnemonic: Mnemonic::ASL,
                mode: AddressingMode::Absolute_X,
                size: 3,
                cycles: 7,
            },
            // BCC
            0x90 => Instruction {
                opcode,
                mnemonic: Mnemonic::BCC,
                mode: AddressingMode::Relative,
                size: 2,
                cycles: 2, // +1 if branch succeeds +2 if to a new page)
            },
            // BCS
            0xB0 => Instruction {
                opcode,
                mnemonic: Mnemonic::BCS,
                mode: AddressingMode::Relative,
                size: 2,
                cycles: 2, // +1 if branch succeeds +2 if to a new page)
            },
            // BEQ
            0xF0 => Instruction {
                opcode,
                mnemonic: Mnemonic::BEQ,
                mode: AddressingMode::Relative,
                size: 2,
                cycles: 2, // +1 if branch succeeds +2 if to a new page)
            },
            // BIT
            0x24 => Instruction {
                opcode,
                mnemonic: Mnemonic::BIT,
                mode: AddressingMode::ZeroPage,
                size: 2,
                cycles: 3,
            },
            0x2C => Instruction {
                opcode,
                mnemonic: Mnemonic::BIT,
                mode: AddressingMode::Absolute,
                size: 3,
                cycles: 4,
            },
            // BMI
            0x30 => Instruction {
                opcode,
                mnemonic: Mnemonic::BMI,
                mode: AddressingMode::Relative,
                size: 2,
                cycles: 2, // +1 if branch succeeds +2 if to a new page)
            },
            // BMI
            0xD0 => Instruction {
                opcode,
                mnemonic: Mnemonic::BNE,
                mode: AddressingMode::Relative,
                size: 2,
                cycles: 2, // +1 if branch succeeds +2 if to a new page)
            },
            // BPL
            0x10 => Instruction {
                opcode,
                mnemonic: Mnemonic::BPL,
                mode: AddressingMode::Relative,
                size: 2,
                cycles: 2, // +1 if branch succeeds +2 if to a new page)
            },
            // BRK
            0x00 => Instruction {
                opcode,
                mnemonic: Mnemonic::BRK,
                mode: AddressingMode::Implied,
                size: 1,
                cycles: 7,
            },
            // BVC
            0x50 => Instruction {
                opcode,
                mnemonic: Mnemonic::BVC,
                mode: AddressingMode::Relative,
                size: 2,
                cycles: 2, // +1 if branch succeeds +2 if to a new page)
            },
            // BVS
            0x70 => Instruction {
                opcode,
                mnemonic: Mnemonic::BVS,
                mode: AddressingMode::Relative,
                size: 2,
                cycles: 2, // +1 if branch succeeds +2 if to a new page)
            },
            // CLC
            0x18 => Instruction {
                opcode,
                mnemonic: Mnemonic::CLC,
                mode: AddressingMode::Relative,
                size: 1,
                cycles: 2,
            },
            // CLD
            0xD8 => Instruction {
                opcode,
                mnemonic: Mnemonic::CLD,
                mode: AddressingMode::Relative,
                size: 1,
                cycles: 2,
            },
            // CLI
            0x58 => Instruction {
                opcode,
                mnemonic: Mnemonic::CLI,
                mode: AddressingMode::Relative,
                size: 1,
                cycles: 2,
            },
            // CLV
            0xB8 => Instruction {
                opcode,
                mnemonic: Mnemonic::CLV,
                mode: AddressingMode::Relative,
                size: 1,
                cycles: 2,
            },
            // CMP
            0xC9 => Instruction {
                opcode,
                mnemonic: Mnemonic::CMP,
                mode: AddressingMode::Immediate,
                size: 2,
                cycles: 2,
            },
            0xC5 => Instruction {
                opcode,
                mnemonic: Mnemonic::CMP,
                mode: AddressingMode::ZeroPage,
                size: 2,
                cycles: 3,
            },
            0xD5 => Instruction {
                opcode,
                mnemonic: Mnemonic::CMP,
                mode: AddressingMode::ZeroPage_X,
                size: 2,
                cycles: 4,
            },
            0xCD => Instruction {
                opcode,
                mnemonic: Mnemonic::CMP,
                mode: AddressingMode::Absolute,
                size: 3,
                cycles: 4,
            },
            0xDD => Instruction {
                opcode,
                mnemonic: Mnemonic::CMP,
                mode: AddressingMode::Absolute_X,
                size: 3,
                cycles: 4,
            },
            0xD9 => Instruction {
                opcode,
                mnemonic: Mnemonic::CMP,
                mode: AddressingMode::Absolute_Y,
                size: 3,
                cycles: 4,
            },
            0xC1 => Instruction {
                opcode,
                mnemonic: Mnemonic::CMP,
                mode: AddressingMode::Indirect_X,
                size: 2,
                cycles: 6,
            },
            0xD1 => Instruction {
                opcode,
                mnemonic: Mnemonic::CMP,
                mode: AddressingMode::Indirect_Y,
                size: 2,
                cycles: 5,
            },
            // CPX
            0xE0 => Instruction {
                opcode,
                mnemonic: Mnemonic::CPX,
                mode: AddressingMode::Immediate,
                size: 2,
                cycles: 2,
            },
            0xE4 => Instruction {
                opcode,
                mnemonic: Mnemonic::CPX,
                mode: AddressingMode::ZeroPage,
                size: 2,
                cycles: 3,
            },
            0xEC => Instruction {
                opcode,
                mnemonic: Mnemonic::CPX,
                mode: AddressingMode::Absolute,
                size: 3,
                cycles: 4,
            },
            // CPY
            0xC0 => Instruction {
                opcode,
                mnemonic: Mnemonic::CPY,
                mode: AddressingMode::Immediate,
                size: 2,
                cycles: 2,
            },
            0xC4 => Instruction {
                opcode,
                mnemonic: Mnemonic::CPY,
                mode: AddressingMode::ZeroPage,
                size: 2,
                cycles: 3,
            },
            0xCC => Instruction {
                opcode,
                mnemonic: Mnemonic::CPY,
                mode: AddressingMode::Absolute,
                size: 3,
                cycles: 4,
            },
            // DEC
            0xC6 => Instruction {
                opcode,
                mnemonic: Mnemonic::DEC,
                mode: AddressingMode::ZeroPage,
                size: 2,
                cycles: 5,
            },
            0xD6 => Instruction {
                opcode,
                mnemonic: Mnemonic::DEC,
                mode: AddressingMode::ZeroPage_X,
                size: 2,
                cycles: 6,
            },
            0xCE => Instruction {
                opcode,
                mnemonic: Mnemonic::DEC,
                mode: AddressingMode::Absolute,
                size: 3,
                cycles: 6,
            },
            0xDE => Instruction {
                opcode,
                mnemonic: Mnemonic::DEC,
                mode: AddressingMode::Absolute_X,
                size: 3,
                cycles: 7,
            },
            // DEX
            0xCA => Instruction {
                opcode,
                mnemonic: Mnemonic::DEX,
                mode: AddressingMode::Implied,
                size: 1,
                cycles: 2,
            },
            // DEY
            0x88 => Instruction {
                opcode,
                mnemonic: Mnemonic::DEY,
                mode: AddressingMode::Implied,
                size: 1,
                cycles: 2,
            },
            // EOR
            0x49 => Instruction {
                opcode,
                mnemonic: Mnemonic::EOR,
                mode: AddressingMode::Immediate,
                size: 2,
                cycles: 2,
            },
            0x45 => Instruction {
                opcode,
                mnemonic: Mnemonic::EOR,
                mode: AddressingMode::ZeroPage,
                size: 2,
                cycles: 3,
            },
            0x55 => Instruction {
                opcode,
                mnemonic: Mnemonic::EOR,
                mode: AddressingMode::ZeroPage_X,
                size: 2,
                cycles: 4,
            },
            0x4D => Instruction {
                opcode,
                mnemonic: Mnemonic::EOR,
                mode: AddressingMode::Absolute,
                size: 3,
                cycles: 4,
            },
            0x5D => Instruction {
                opcode,
                mnemonic: Mnemonic::EOR,
                mode: AddressingMode::Absolute_X,
                size: 3,
                cycles: 4,
            },
            0x59 => Instruction {
                opcode,
                mnemonic: Mnemonic::EOR,
                mode: AddressingMode::Absolute_Y,
                size: 3,
                cycles: 4,
            },
            0x41 => Instruction {
                opcode,
                mnemonic: Mnemonic::EOR,
                mode: AddressingMode::Indirect_X,
                size: 2,
                cycles: 6,
            },
            0x51 => Instruction {
                opcode,
                mnemonic: Mnemonic::EOR,
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
