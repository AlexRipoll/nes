use core::panic;
use std::fmt;

/// Represents a CPU instruction for the 6502 processor.
///
/// This struct holds information about a single instruction, including its
/// opcode, mnemonic, addressing mode, size, and the number of cycles it
/// takes to execute. It is used by the CPU emulator to understand and
/// execute 6502 assembly language instructions.
#[derive(Debug)]
pub struct Instruction {
    /// The opcode byte that identifies the instruction.
    ///
    /// This is a unique byte (0x00 to 0xFF) that corresponds to a specific
    /// operation the CPU will perform. The opcode is used to look up the
    /// associated mnemonic and addressing mode.
    pub opcode: u8,

    /// The human-readable name of the instruction.
    ///
    /// This field represents the mnemonic of the instruction (e.g., `LDA`, `STA`,
    /// `ADC`, etc.) and provides a way to identify the instruction in a more
    /// meaningful way than just the opcode.
    pub mnemonic: Mnemonic,

    /// The mode used to access operands for the instruction.
    ///
    /// This field specifies how the instruction accesses its data, which can
    /// affect how operands are read from memory or registers. The addressing
    /// mode can be immediate, zero page, absolute, indirect, etc.
    pub mode: AddressingMode,

    pub none_addressing: bool,

    /// The size of the instruction in bytes.
    ///
    /// This field indicates how many bytes the instruction occupies in memory.
    /// It can be one byte for simple instructions (e.g., `NOP`), or more for
    /// instructions that access data (e.g., `LDA #$01`).
    pub size: u8,

    /// The number of clock cycles required to execute the instruction.
    ///
    /// This field represents how many cycles the instruction takes to complete.
    /// Different instructions can have varying cycle counts based on their complexity
    /// and the addressing modes used.
    pub cycles: u8,
}

/// Represents the different CPU instructions (mnemonics) available on the 6502 processor.
///
/// The 6502 processor supports a wide range of instructions, each identified
/// by a mnemonic. This enum lists all the valid mnemonics that the CPU
/// can execute. Each variant corresponds to a specific operation.
///
/// Mnemonics include operations like arithmetic, bit manipulation, branching,
/// and control instructions.
#[derive(Debug)]
pub enum Mnemonic {
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
    INC,
    INX,
    INY,
    JMP,
    JSR,
    LDA,
    LDX,
    LDY,
    LSR,
    NOP,
    ORA,
    PHA,
    PHP,
    PLA,
    PLP,
    ROL,
    ROR,
    RTI,
    RTS,
    SBC,
    SEC,
    SED,
    SEI,
    STA,
    STX,
    STY,
    TAX,
    TAY,
    TSX,
    TXA,
    TXS,
    TYA,
    UNOP,
    LAX,
    SAX,
    USBC,
    DCP,
    ISB,
    SLO,
    RLA,
    SRE,
    RRA,
    UNKOWN,
}

impl fmt::Display for Mnemonic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mnemonic_str = match self {
            Mnemonic::ADC => "ADC",
            Mnemonic::AND => "AND",
            Mnemonic::ASL => "ASL",
            Mnemonic::BCC => "BCC",
            Mnemonic::BCS => "BCS",
            Mnemonic::BEQ => "BEQ",
            Mnemonic::BIT => "BIT",
            Mnemonic::BMI => "BMI",
            Mnemonic::BNE => "BNE",
            Mnemonic::BPL => "BPL",
            Mnemonic::BRK => "BRK",
            Mnemonic::BVC => "BVC",
            Mnemonic::BVS => "BVS",
            Mnemonic::CLC => "CLC",
            Mnemonic::CLD => "CLD",
            Mnemonic::CLI => "CLI",
            Mnemonic::CLV => "CLV",
            Mnemonic::CMP => "CMP",
            Mnemonic::CPX => "CPX",
            Mnemonic::CPY => "CPY",
            Mnemonic::DEC => "DEC",
            Mnemonic::DEX => "DEX",
            Mnemonic::DEY => "DEY",
            Mnemonic::EOR => "EOR",
            Mnemonic::INC => "INC",
            Mnemonic::INX => "INX",
            Mnemonic::INY => "INY",
            Mnemonic::JMP => "JMP",
            Mnemonic::JSR => "JSR",
            Mnemonic::LDA => "LDA",
            Mnemonic::LDX => "LDX",
            Mnemonic::LDY => "LDY",
            Mnemonic::LSR => "LSR",
            Mnemonic::NOP => "NOP",
            Mnemonic::ORA => "ORA",
            Mnemonic::PHA => "PHA",
            Mnemonic::PHP => "PHP",
            Mnemonic::PLA => "PLA",
            Mnemonic::PLP => "PLP",
            Mnemonic::ROL => "ROL",
            Mnemonic::ROR => "ROR",
            Mnemonic::RTI => "RTI",
            Mnemonic::RTS => "RTS",
            Mnemonic::SBC => "SBC",
            Mnemonic::SEC => "SEC",
            Mnemonic::SED => "SED",
            Mnemonic::SEI => "SEI",
            Mnemonic::STA => "STA",
            Mnemonic::STX => "STX",
            Mnemonic::STY => "STY",
            Mnemonic::TAX => "TAX",
            Mnemonic::TAY => "TAY",
            Mnemonic::TSX => "TSX",
            Mnemonic::TXA => "TXA",
            Mnemonic::TXS => "TXS",
            Mnemonic::TYA => "TYA",
            Mnemonic::UNOP => "*NOP",
            Mnemonic::LAX => "*LAX",
            Mnemonic::SAX => "*SAX",
            Mnemonic::USBC => "*SBC",
            Mnemonic::DCP => "*DCP",
            Mnemonic::ISB => "*ISB",
            Mnemonic::SLO => "*SLO",
            Mnemonic::RLA => "*RLA",
            Mnemonic::SRE => "*SRE",
            Mnemonic::RRA => "*RRA",
            Mnemonic::UNKOWN => "UNKNOWN",
        };

        write!(f, "{}", mnemonic_str)
    }
}

/// Represents the different addressing modes used by the 6502 processor.
///
/// Addressing modes define how the operands of an instruction are accessed.
/// Depending on the mode, operands may be immediate values, memory addresses,
/// or registers. The addressing mode affects how the CPU fetches and interprets
/// data for a given instruction.
#[derive(Debug)]
#[allow(non_camel_case_types)]
pub enum AddressingMode {
    /// Implied addressing mode.
    ///
    /// In this mode, the instruction does not require an explicit operand.
    /// The operation is performed on a known location, such as the accumulator,
    /// or affects the processor status.
    Implied,

    /// Accumulator addressing mode.
    ///
    /// In this mode, the operand is implicitly the accumulator register (`A`).
    /// Many instructions like shifts and rotations operate directly on `A`.
    Accumulator,

    /// Immediate addressing mode.
    ///
    /// The operand is provided as part of the instruction itself, typically
    /// as the next byte. This mode is often used for loading values into
    /// registers or performing operations on constants.
    Immediate,

    /// Zero Page addressing mode.
    ///
    /// The operand is located in the first 256 bytes of memory (zero page).
    /// This mode is more efficient as it requires fewer bytes to represent
    /// the address.
    ZeroPage,

    /// Zero Page X-indexed addressing mode.
    ///
    /// Similar to Zero Page addressing, but the effective address is calculated
    /// by adding the X register to the base zero page address.
    ZeroPage_X,

    /// Zero Page Y-indexed addressing mode.
    ///
    /// Similar to Zero Page addressing, but the effective address is calculated
    /// by adding the Y register to the base zero page address.
    ZeroPage_Y,

    /// Relative addressing mode.
    ///
    /// Typically used for branch instructions, the operand is a signed 8-bit
    /// offset from the program counter. This allows for short jumps forward
    /// or backward in the code.
    Relative,

    /// Absolute addressing mode.
    ///
    /// The operand is a full 16-bit address. The instruction operates on the
    /// memory location specified by this address.
    Absolute,

    /// Absolute X-indexed addressing mode.
    ///
    /// Similar to Absolute addressing, but the effective address is calculated
    /// by adding the X register to the 16-bit base address.
    Absolute_X,

    /// Absolute Y-indexed addressing mode.
    ///
    /// Similar to Absolute addressing, but the effective address is calculated
    /// by adding the Y register to the 16-bit base address.
    Absolute_Y,

    /// Indirect addressing mode.
    ///
    /// In this mode, the operand is a pointer to a memory location.
    /// The address stored at the operand's location is used as the effective
    /// address.
    Indirect,

    /// Indexed indirect addressing mode (X, Indirect).
    ///
    /// The operand is an 8-bit zero page address. This address is added to the
    /// X register to form the effective address, and the value at this address
    /// is used as the final memory address for the operation.
    Indirect_X,

    /// Indirect indexed addressing mode (Indirect, Y).
    ///
    /// In this mode, the operand is an 8-bit zero page address. The memory
    /// address stored at this location is added to the Y register to form
    /// the effective address.
    Indirect_Y,
}

impl From<u8> for Instruction {
    fn from(opcode: u8) -> Self {
        match opcode {
            // ADC
            0x69 => Instruction {
                opcode,
                mnemonic: Mnemonic::ADC,
                mode: AddressingMode::Immediate,
                none_addressing: false,
                size: 2,
                cycles: 2,
            },
            0x65 => Instruction {
                opcode,
                mnemonic: Mnemonic::ADC,
                mode: AddressingMode::ZeroPage,
                none_addressing: false,
                size: 2,
                cycles: 3,
            },
            0x75 => Instruction {
                opcode,
                mnemonic: Mnemonic::ADC,
                mode: AddressingMode::ZeroPage_X,
                none_addressing: false,
                size: 2,
                cycles: 4,
            },
            0x6D => Instruction {
                opcode,
                mnemonic: Mnemonic::ADC,
                mode: AddressingMode::Absolute,
                none_addressing: false,
                size: 3,
                cycles: 4,
            },
            0x7D => Instruction {
                opcode,
                mnemonic: Mnemonic::ADC,
                mode: AddressingMode::Absolute_X,
                none_addressing: false,
                size: 3,
                cycles: 4,
            },
            0x79 => Instruction {
                opcode,
                mnemonic: Mnemonic::ADC,
                mode: AddressingMode::Absolute_Y,
                none_addressing: false,
                size: 3,
                cycles: 4,
            },
            0x61 => Instruction {
                opcode,
                mnemonic: Mnemonic::ADC,
                mode: AddressingMode::Indirect_X,
                none_addressing: false,
                size: 2,
                cycles: 6,
            },
            0x71 => Instruction {
                opcode,
                mnemonic: Mnemonic::ADC,
                mode: AddressingMode::Indirect_Y,
                none_addressing: false,
                size: 2,
                cycles: 5,
            },
            // AND
            0x29 => Instruction {
                opcode,
                mnemonic: Mnemonic::AND,
                mode: AddressingMode::Immediate,
                none_addressing: false,
                size: 2,
                cycles: 2,
            },
            0x25 => Instruction {
                opcode,
                mnemonic: Mnemonic::AND,
                mode: AddressingMode::ZeroPage,
                none_addressing: false,
                size: 2,
                cycles: 3,
            },
            0x35 => Instruction {
                opcode,
                mnemonic: Mnemonic::AND,
                mode: AddressingMode::ZeroPage_X,
                none_addressing: false,
                size: 2,
                cycles: 4,
            },
            0x2D => Instruction {
                opcode,
                mnemonic: Mnemonic::AND,
                mode: AddressingMode::Absolute,
                none_addressing: false,
                size: 3,
                cycles: 4,
            },
            0x3D => Instruction {
                opcode,
                mnemonic: Mnemonic::AND,
                mode: AddressingMode::Absolute_X,
                none_addressing: false,
                size: 3,
                cycles: 4,
            },
            0x39 => Instruction {
                opcode,
                mnemonic: Mnemonic::AND,
                mode: AddressingMode::Absolute_Y,
                none_addressing: false,
                size: 3,
                cycles: 4,
            },
            0x21 => Instruction {
                opcode,
                mnemonic: Mnemonic::AND,
                mode: AddressingMode::Indirect_X,
                none_addressing: false,
                size: 2,
                cycles: 6,
            },
            0x31 => Instruction {
                opcode,
                mnemonic: Mnemonic::AND,
                mode: AddressingMode::Indirect_Y,
                none_addressing: false,
                size: 2,
                cycles: 5,
            },
            // ASL
            0x0A => Instruction {
                opcode,
                mnemonic: Mnemonic::ASL,
                mode: AddressingMode::Accumulator,
                none_addressing: true,
                size: 1,
                cycles: 2,
            },
            0x06 => Instruction {
                opcode,
                mnemonic: Mnemonic::ASL,
                mode: AddressingMode::ZeroPage,
                none_addressing: false,
                size: 2,
                cycles: 5,
            },
            0x16 => Instruction {
                opcode,
                mnemonic: Mnemonic::ASL,
                mode: AddressingMode::ZeroPage_X,
                none_addressing: false,
                size: 2,
                cycles: 6,
            },
            0x0E => Instruction {
                opcode,
                mnemonic: Mnemonic::ASL,
                mode: AddressingMode::Absolute,
                none_addressing: false,
                size: 3,
                cycles: 6,
            },
            0x1E => Instruction {
                opcode,
                mnemonic: Mnemonic::ASL,
                mode: AddressingMode::Absolute_X,
                none_addressing: false,
                size: 3,
                cycles: 7,
            },
            // BCC
            0x90 => Instruction {
                opcode,
                mnemonic: Mnemonic::BCC,
                mode: AddressingMode::Relative,
                none_addressing: true,
                size: 2,
                cycles: 2, // +1 if branch succeeds +2 if to a new page)
            },
            // BCS
            0xB0 => Instruction {
                opcode,
                mnemonic: Mnemonic::BCS,
                mode: AddressingMode::Relative,
                none_addressing: true,
                size: 2,
                cycles: 2, // +1 if branch succeeds +2 if to a new page)
            },
            // BEQ
            0xF0 => Instruction {
                opcode,
                mnemonic: Mnemonic::BEQ,
                mode: AddressingMode::Relative,
                none_addressing: true,
                size: 2,
                cycles: 2, // +1 if branch succeeds +2 if to a new page)
            },
            // BIT
            0x24 => Instruction {
                opcode,
                mnemonic: Mnemonic::BIT,
                mode: AddressingMode::ZeroPage,
                none_addressing: false,
                size: 2,
                cycles: 3,
            },
            0x2C => Instruction {
                opcode,
                mnemonic: Mnemonic::BIT,
                mode: AddressingMode::Absolute,
                none_addressing: false,
                size: 3,
                cycles: 4,
            },
            // BMI
            0x30 => Instruction {
                opcode,
                mnemonic: Mnemonic::BMI,
                mode: AddressingMode::Relative,
                none_addressing: true,
                size: 2,
                cycles: 2, // +1 if branch succeeds +2 if to a new page)
            },
            // BMI
            0xD0 => Instruction {
                opcode,
                mnemonic: Mnemonic::BNE,
                mode: AddressingMode::Relative,
                none_addressing: true,
                size: 2,
                cycles: 2, // +1 if branch succeeds +2 if to a new page)
            },
            // BPL
            0x10 => Instruction {
                opcode,
                mnemonic: Mnemonic::BPL,
                mode: AddressingMode::Relative,
                none_addressing: true,
                size: 2,
                cycles: 2, // +1 if branch succeeds +2 if to a new page)
            },
            // BRK
            0x00 => Instruction {
                opcode,
                mnemonic: Mnemonic::BRK,
                mode: AddressingMode::Implied,
                none_addressing: true,
                size: 1,
                cycles: 7,
            },
            // BVC
            0x50 => Instruction {
                opcode,
                mnemonic: Mnemonic::BVC,
                mode: AddressingMode::Relative,
                none_addressing: true,
                size: 2,
                cycles: 2, // +1 if branch succeeds +2 if to a new page)
            },
            // BVS
            0x70 => Instruction {
                opcode,
                mnemonic: Mnemonic::BVS,
                mode: AddressingMode::Relative,
                none_addressing: true,
                size: 2,
                cycles: 2, // +1 if branch succeeds +2 if to a new page)
            },
            // CLC
            0x18 => Instruction {
                opcode,
                mnemonic: Mnemonic::CLC,
                mode: AddressingMode::Relative,
                none_addressing: true,
                size: 1,
                cycles: 2,
            },
            // CLD
            0xD8 => Instruction {
                opcode,
                mnemonic: Mnemonic::CLD,
                mode: AddressingMode::Relative,
                none_addressing: true,
                size: 1,
                cycles: 2,
            },
            // CLI
            0x58 => Instruction {
                opcode,
                mnemonic: Mnemonic::CLI,
                mode: AddressingMode::Relative,
                none_addressing: true,
                size: 1,
                cycles: 2,
            },
            // CLV
            0xB8 => Instruction {
                opcode,
                mnemonic: Mnemonic::CLV,
                mode: AddressingMode::Relative,
                none_addressing: true,
                size: 1,
                cycles: 2,
            },
            // CMP
            0xC9 => Instruction {
                opcode,
                mnemonic: Mnemonic::CMP,
                mode: AddressingMode::Immediate,
                none_addressing: false,
                size: 2,
                cycles: 2,
            },
            0xC5 => Instruction {
                opcode,
                mnemonic: Mnemonic::CMP,
                mode: AddressingMode::ZeroPage,
                none_addressing: false,
                size: 2,
                cycles: 3,
            },
            0xD5 => Instruction {
                opcode,
                mnemonic: Mnemonic::CMP,
                mode: AddressingMode::ZeroPage_X,
                none_addressing: false,
                size: 2,
                cycles: 4,
            },
            0xCD => Instruction {
                opcode,
                mnemonic: Mnemonic::CMP,
                mode: AddressingMode::Absolute,
                none_addressing: false,
                size: 3,
                cycles: 4,
            },
            0xDD => Instruction {
                opcode,
                mnemonic: Mnemonic::CMP,
                mode: AddressingMode::Absolute_X,
                none_addressing: false,
                size: 3,
                cycles: 4,
            },
            0xD9 => Instruction {
                opcode,
                mnemonic: Mnemonic::CMP,
                mode: AddressingMode::Absolute_Y,
                none_addressing: false,
                size: 3,
                cycles: 4,
            },
            0xC1 => Instruction {
                opcode,
                mnemonic: Mnemonic::CMP,
                mode: AddressingMode::Indirect_X,
                none_addressing: false,
                size: 2,
                cycles: 6,
            },
            0xD1 => Instruction {
                opcode,
                mnemonic: Mnemonic::CMP,
                mode: AddressingMode::Indirect_Y,
                none_addressing: false,
                size: 2,
                cycles: 5,
            },
            // CPX
            0xE0 => Instruction {
                opcode,
                mnemonic: Mnemonic::CPX,
                mode: AddressingMode::Immediate,
                none_addressing: false,
                size: 2,
                cycles: 2,
            },
            0xE4 => Instruction {
                opcode,
                mnemonic: Mnemonic::CPX,
                mode: AddressingMode::ZeroPage,
                none_addressing: false,
                size: 2,
                cycles: 3,
            },
            0xEC => Instruction {
                opcode,
                mnemonic: Mnemonic::CPX,
                mode: AddressingMode::Absolute,
                none_addressing: false,
                size: 3,
                cycles: 4,
            },
            // CPY
            0xC0 => Instruction {
                opcode,
                mnemonic: Mnemonic::CPY,
                mode: AddressingMode::Immediate,
                none_addressing: false,
                size: 2,
                cycles: 2,
            },
            0xC4 => Instruction {
                opcode,
                mnemonic: Mnemonic::CPY,
                mode: AddressingMode::ZeroPage,
                none_addressing: false,
                size: 2,
                cycles: 3,
            },
            0xCC => Instruction {
                opcode,
                mnemonic: Mnemonic::CPY,
                mode: AddressingMode::Absolute,
                none_addressing: false,
                size: 3,
                cycles: 4,
            },
            // DEC
            0xC6 => Instruction {
                opcode,
                mnemonic: Mnemonic::DEC,
                mode: AddressingMode::ZeroPage,
                none_addressing: false,
                size: 2,
                cycles: 5,
            },
            0xD6 => Instruction {
                opcode,
                mnemonic: Mnemonic::DEC,
                mode: AddressingMode::ZeroPage_X,
                none_addressing: false,
                size: 2,
                cycles: 6,
            },
            0xCE => Instruction {
                opcode,
                mnemonic: Mnemonic::DEC,
                mode: AddressingMode::Absolute,
                none_addressing: false,
                size: 3,
                cycles: 6,
            },
            0xDE => Instruction {
                opcode,
                mnemonic: Mnemonic::DEC,
                mode: AddressingMode::Absolute_X,
                none_addressing: false,
                size: 3,
                cycles: 7,
            },
            // DEX
            0xCA => Instruction {
                opcode,
                mnemonic: Mnemonic::DEX,
                mode: AddressingMode::Implied,
                none_addressing: true,
                size: 1,
                cycles: 2,
            },
            // DEY
            0x88 => Instruction {
                opcode,
                mnemonic: Mnemonic::DEY,
                mode: AddressingMode::Implied,
                none_addressing: true,
                size: 1,
                cycles: 2,
            },
            // EOR
            0x49 => Instruction {
                opcode,
                mnemonic: Mnemonic::EOR,
                mode: AddressingMode::Immediate,
                none_addressing: false,
                size: 2,
                cycles: 2,
            },
            0x45 => Instruction {
                opcode,
                mnemonic: Mnemonic::EOR,
                mode: AddressingMode::ZeroPage,
                none_addressing: false,
                size: 2,
                cycles: 3,
            },
            0x55 => Instruction {
                opcode,
                mnemonic: Mnemonic::EOR,
                mode: AddressingMode::ZeroPage_X,
                none_addressing: false,
                size: 2,
                cycles: 4,
            },
            0x4D => Instruction {
                opcode,
                mnemonic: Mnemonic::EOR,
                mode: AddressingMode::Absolute,
                none_addressing: false,
                size: 3,
                cycles: 4,
            },
            0x5D => Instruction {
                opcode,
                mnemonic: Mnemonic::EOR,
                mode: AddressingMode::Absolute_X,
                none_addressing: false,
                size: 3,
                cycles: 4,
            },
            0x59 => Instruction {
                opcode,
                mnemonic: Mnemonic::EOR,
                mode: AddressingMode::Absolute_Y,
                none_addressing: false,
                size: 3,
                cycles: 4,
            },
            0x41 => Instruction {
                opcode,
                mnemonic: Mnemonic::EOR,
                mode: AddressingMode::Indirect_X,
                none_addressing: false,
                size: 2,
                cycles: 6,
            },
            0x51 => Instruction {
                opcode,
                mnemonic: Mnemonic::EOR,
                mode: AddressingMode::Indirect_Y,
                none_addressing: false,
                size: 2,
                cycles: 5,
            },
            // INC
            0xE6 => Instruction {
                opcode,
                mnemonic: Mnemonic::INC,
                mode: AddressingMode::ZeroPage,
                none_addressing: false,
                size: 2,
                cycles: 5,
            },
            0xF6 => Instruction {
                opcode,
                mnemonic: Mnemonic::INC,
                mode: AddressingMode::ZeroPage_X,
                none_addressing: false,
                size: 2,
                cycles: 6,
            },
            0xEE => Instruction {
                opcode,
                mnemonic: Mnemonic::INC,
                mode: AddressingMode::Absolute,
                none_addressing: false,
                size: 3,
                cycles: 6,
            },
            0xFE => Instruction {
                opcode,
                mnemonic: Mnemonic::INC,
                mode: AddressingMode::Absolute_X,
                none_addressing: false,
                size: 3,
                cycles: 7,
            },
            // INX
            0xE8 => Instruction {
                opcode,
                mnemonic: Mnemonic::INX,
                mode: AddressingMode::Implied,
                none_addressing: true,
                size: 1,
                cycles: 2,
            },
            // INY
            0xC8 => Instruction {
                opcode,
                mnemonic: Mnemonic::INY,
                mode: AddressingMode::Implied,
                none_addressing: true,
                size: 1,
                cycles: 2,
            },
            // JMP
            0x4C => Instruction {
                opcode,
                mnemonic: Mnemonic::JMP,
                mode: AddressingMode::Absolute,
                none_addressing: true,
                size: 3,
                cycles: 3,
            },
            0x6C => Instruction {
                opcode,
                mnemonic: Mnemonic::JMP,
                mode: AddressingMode::Indirect,
                none_addressing: true,
                size: 3,
                cycles: 5,
            },
            // JSR
            0x20 => Instruction {
                opcode,
                mnemonic: Mnemonic::JSR,
                mode: AddressingMode::Absolute,
                none_addressing: true,
                size: 3,
                cycles: 6,
            },
            // LDA
            0xA9 => Instruction {
                opcode,
                mnemonic: Mnemonic::LDA,
                mode: AddressingMode::Immediate,
                none_addressing: false,
                size: 2,
                cycles: 2,
            },
            0xA5 => Instruction {
                opcode,
                mnemonic: Mnemonic::LDA,
                mode: AddressingMode::ZeroPage,
                none_addressing: false,
                size: 2,
                cycles: 3,
            },
            0xB5 => Instruction {
                opcode,
                mnemonic: Mnemonic::LDA,
                mode: AddressingMode::ZeroPage_X,
                none_addressing: false,
                size: 2,
                cycles: 4,
            },
            0xAD => Instruction {
                opcode,
                mnemonic: Mnemonic::LDA,
                mode: AddressingMode::Absolute,
                none_addressing: false,
                size: 3,
                cycles: 4,
            },
            0xBD => Instruction {
                opcode,
                mnemonic: Mnemonic::LDA,
                mode: AddressingMode::Absolute_X,
                none_addressing: false,
                size: 3,
                cycles: 4,
            },
            0xB9 => Instruction {
                opcode,
                mnemonic: Mnemonic::LDA,
                mode: AddressingMode::Absolute_Y,
                none_addressing: false,
                size: 3,
                cycles: 4,
            },
            0xA1 => Instruction {
                opcode,
                mnemonic: Mnemonic::LDA,
                mode: AddressingMode::Indirect_X,
                none_addressing: false,
                size: 2,
                cycles: 6,
            },
            0xB1 => Instruction {
                opcode,
                mnemonic: Mnemonic::LDA,
                mode: AddressingMode::Indirect_Y,
                none_addressing: false,
                size: 2,
                cycles: 5,
            },
            // LDX
            0xA2 => Instruction {
                opcode,
                mnemonic: Mnemonic::LDX,
                mode: AddressingMode::Immediate,
                none_addressing: false,
                size: 2,
                cycles: 2,
            },
            0xA6 => Instruction {
                opcode,
                mnemonic: Mnemonic::LDX,
                mode: AddressingMode::ZeroPage,
                none_addressing: false,
                size: 2,
                cycles: 3,
            },
            0xB6 => Instruction {
                opcode,
                mnemonic: Mnemonic::LDX,
                mode: AddressingMode::ZeroPage_Y,
                none_addressing: false,
                size: 2,
                cycles: 4,
            },
            0xAE => Instruction {
                opcode,
                mnemonic: Mnemonic::LDX,
                mode: AddressingMode::Absolute,
                none_addressing: false,
                size: 3,
                cycles: 4,
            },
            0xBE => Instruction {
                opcode,
                mnemonic: Mnemonic::LDX,
                mode: AddressingMode::Absolute_Y,
                none_addressing: false,
                size: 3,
                cycles: 4,
            },
            // LDY
            0xA0 => Instruction {
                opcode,
                mnemonic: Mnemonic::LDY,
                mode: AddressingMode::Immediate,
                none_addressing: false,
                size: 2,
                cycles: 2,
            },
            0xA4 => Instruction {
                opcode,
                mnemonic: Mnemonic::LDY,
                mode: AddressingMode::ZeroPage,
                none_addressing: false,
                size: 2,
                cycles: 3,
            },
            0xB4 => Instruction {
                opcode,
                mnemonic: Mnemonic::LDY,
                mode: AddressingMode::ZeroPage_X,
                none_addressing: false,
                size: 2,
                cycles: 4,
            },
            0xAC => Instruction {
                opcode,
                mnemonic: Mnemonic::LDY,
                mode: AddressingMode::Absolute,
                none_addressing: false,
                size: 3,
                cycles: 4,
            },
            0xBC => Instruction {
                opcode,
                mnemonic: Mnemonic::LDY,
                mode: AddressingMode::Absolute_X,
                none_addressing: false,
                size: 3,
                cycles: 4,
            },
            // LSR
            0x4A => Instruction {
                opcode,
                mnemonic: Mnemonic::LSR,
                mode: AddressingMode::Accumulator,
                none_addressing: true,
                size: 1,
                cycles: 2,
            },
            0x46 => Instruction {
                opcode,
                mnemonic: Mnemonic::LSR,
                mode: AddressingMode::ZeroPage,
                none_addressing: false,
                size: 2,
                cycles: 5,
            },
            0x56 => Instruction {
                opcode,
                mnemonic: Mnemonic::LSR,
                mode: AddressingMode::ZeroPage_X,
                none_addressing: false,
                size: 2,
                cycles: 6,
            },
            0x4E => Instruction {
                opcode,
                mnemonic: Mnemonic::LSR,
                mode: AddressingMode::Absolute,
                none_addressing: false,
                size: 3,
                cycles: 6,
            },
            0x5E => Instruction {
                opcode,
                mnemonic: Mnemonic::LSR,
                mode: AddressingMode::Absolute_X,
                none_addressing: false,
                size: 3,
                cycles: 7,
            },
            // NOP
            0xEA => Instruction {
                opcode,
                mnemonic: Mnemonic::NOP,
                mode: AddressingMode::Implied,
                none_addressing: true,
                size: 1,
                cycles: 2,
            },
            // ORA
            0x09 => Instruction {
                opcode,
                mnemonic: Mnemonic::ORA,
                mode: AddressingMode::Immediate,
                none_addressing: false,
                size: 2,
                cycles: 2,
            },
            0x05 => Instruction {
                opcode,
                mnemonic: Mnemonic::ORA,
                mode: AddressingMode::ZeroPage,
                none_addressing: false,
                size: 2,
                cycles: 3,
            },
            0x15 => Instruction {
                opcode,
                mnemonic: Mnemonic::ORA,
                mode: AddressingMode::ZeroPage_X,
                none_addressing: false,
                size: 2,
                cycles: 4,
            },
            0x0D => Instruction {
                opcode,
                mnemonic: Mnemonic::ORA,
                mode: AddressingMode::Absolute,
                none_addressing: false,
                size: 3,
                cycles: 4,
            },
            0x1D => Instruction {
                opcode,
                mnemonic: Mnemonic::ORA,
                mode: AddressingMode::Absolute_X,
                none_addressing: false,
                size: 3,
                cycles: 4,
            },
            0x19 => Instruction {
                opcode,
                mnemonic: Mnemonic::ORA,
                mode: AddressingMode::Absolute_Y,
                none_addressing: false,
                size: 3,
                cycles: 4,
            },
            0x01 => Instruction {
                opcode,
                mnemonic: Mnemonic::ORA,
                mode: AddressingMode::Indirect_X,
                none_addressing: false,
                size: 2,
                cycles: 6,
            },
            0x11 => Instruction {
                opcode,
                mnemonic: Mnemonic::ORA,
                mode: AddressingMode::Indirect_Y,
                none_addressing: false,
                size: 2,
                cycles: 5,
            },
            // PHA
            0x48 => Instruction {
                opcode,
                mnemonic: Mnemonic::PHA,
                mode: AddressingMode::Implied,
                none_addressing: true,
                size: 1,
                cycles: 3,
            },
            // PHP
            0x08 => Instruction {
                opcode,
                mnemonic: Mnemonic::PHP,
                mode: AddressingMode::Implied,
                none_addressing: true,
                size: 1,
                cycles: 3,
            },
            // PLA
            0x68 => Instruction {
                opcode,
                mnemonic: Mnemonic::PLA,
                mode: AddressingMode::Implied,
                none_addressing: true,
                size: 1,
                cycles: 4,
            },
            // PLP
            0x28 => Instruction {
                opcode,
                mnemonic: Mnemonic::PLP,
                mode: AddressingMode::Implied,
                none_addressing: true,
                size: 1,
                cycles: 4,
            },
            // ROL
            0x2A => Instruction {
                opcode,
                mnemonic: Mnemonic::ROL,
                mode: AddressingMode::Accumulator,
                none_addressing: true,
                size: 1,
                cycles: 2,
            },
            0x26 => Instruction {
                opcode,
                mnemonic: Mnemonic::ROL,
                mode: AddressingMode::ZeroPage,
                none_addressing: false,
                size: 2,
                cycles: 5,
            },
            0x36 => Instruction {
                opcode,
                mnemonic: Mnemonic::ROL,
                mode: AddressingMode::ZeroPage_X,
                none_addressing: false,
                size: 2,
                cycles: 6,
            },
            0x2E => Instruction {
                opcode,
                mnemonic: Mnemonic::ROL,
                mode: AddressingMode::Absolute,
                none_addressing: false,
                size: 3,
                cycles: 6,
            },
            0x3E => Instruction {
                opcode,
                mnemonic: Mnemonic::ROL,
                mode: AddressingMode::Absolute_X,
                none_addressing: false,
                size: 3,
                cycles: 7,
            },
            // ROR
            0x6A => Instruction {
                opcode,
                mnemonic: Mnemonic::ROR,
                mode: AddressingMode::Accumulator,
                none_addressing: true,
                size: 1,
                cycles: 2,
            },
            0x66 => Instruction {
                opcode,
                mnemonic: Mnemonic::ROR,
                mode: AddressingMode::ZeroPage,
                none_addressing: false,
                size: 2,
                cycles: 5,
            },
            0x76 => Instruction {
                opcode,
                mnemonic: Mnemonic::ROR,
                mode: AddressingMode::ZeroPage_X,
                none_addressing: false,
                size: 2,
                cycles: 6,
            },
            0x6E => Instruction {
                opcode,
                mnemonic: Mnemonic::ROR,
                mode: AddressingMode::Absolute,
                none_addressing: false,
                size: 3,
                cycles: 6,
            },
            0x7E => Instruction {
                opcode,
                mnemonic: Mnemonic::ROR,
                mode: AddressingMode::Absolute_X,
                none_addressing: false,
                size: 3,
                cycles: 7,
            },
            // RTI
            0x40 => Instruction {
                opcode,
                mnemonic: Mnemonic::RTI,
                mode: AddressingMode::Implied,
                none_addressing: true,
                size: 1,
                cycles: 6,
            },
            // RTS
            0x60 => Instruction {
                opcode,
                mnemonic: Mnemonic::RTS,
                mode: AddressingMode::Implied,
                none_addressing: true,
                size: 1,
                cycles: 6,
            },
            // SBC
            0xE9 => Instruction {
                opcode,
                mnemonic: Mnemonic::SBC,
                mode: AddressingMode::Immediate,
                none_addressing: false,
                size: 2,
                cycles: 2,
            },
            0xE5 => Instruction {
                opcode,
                mnemonic: Mnemonic::SBC,
                mode: AddressingMode::ZeroPage,
                none_addressing: false,
                size: 2,
                cycles: 3,
            },
            0xF5 => Instruction {
                opcode,
                mnemonic: Mnemonic::SBC,
                mode: AddressingMode::ZeroPage_X,
                none_addressing: false,
                size: 2,
                cycles: 4,
            },
            0xED => Instruction {
                opcode,
                mnemonic: Mnemonic::SBC,
                mode: AddressingMode::Absolute,
                none_addressing: false,
                size: 3,
                cycles: 4,
            },
            0xFD => Instruction {
                opcode,
                mnemonic: Mnemonic::SBC,
                mode: AddressingMode::Absolute_X,
                none_addressing: false,
                size: 3,
                cycles: 4,
            },
            0xF9 => Instruction {
                opcode,
                mnemonic: Mnemonic::SBC,
                mode: AddressingMode::Absolute_Y,
                none_addressing: false,
                size: 3,
                cycles: 4,
            },
            0xE1 => Instruction {
                opcode,
                mnemonic: Mnemonic::SBC,
                mode: AddressingMode::Indirect_X,
                none_addressing: false,
                size: 2,
                cycles: 6,
            },
            0xF1 => Instruction {
                opcode,
                mnemonic: Mnemonic::SBC,
                mode: AddressingMode::Indirect_Y,
                none_addressing: false,
                size: 2,
                cycles: 5,
            },
            // SEC
            0x38 => Instruction {
                opcode,
                mnemonic: Mnemonic::SEC,
                mode: AddressingMode::Implied,
                none_addressing: true,
                size: 1,
                cycles: 2,
            },
            // SED
            0xF8 => Instruction {
                opcode,
                mnemonic: Mnemonic::SED,
                mode: AddressingMode::Implied,
                none_addressing: true,
                size: 1,
                cycles: 2,
            },
            // SEI
            0x78 => Instruction {
                opcode,
                mnemonic: Mnemonic::SEI,
                mode: AddressingMode::Implied,
                none_addressing: true,
                size: 1,
                cycles: 2,
            },
            // STA
            0x85 => Instruction {
                opcode,
                mnemonic: Mnemonic::STA,
                mode: AddressingMode::ZeroPage,
                none_addressing: false,
                size: 2,
                cycles: 3,
            },
            0x95 => Instruction {
                opcode,
                mnemonic: Mnemonic::STA,
                mode: AddressingMode::ZeroPage_X,
                none_addressing: false,
                size: 2,
                cycles: 4,
            },
            0x8D => Instruction {
                opcode,
                mnemonic: Mnemonic::STA,
                mode: AddressingMode::Absolute,
                none_addressing: false,
                size: 3,
                cycles: 4,
            },
            0x9D => Instruction {
                opcode,
                mnemonic: Mnemonic::STA,
                mode: AddressingMode::Absolute_X,
                none_addressing: false,
                size: 3,
                cycles: 5,
            },
            0x99 => Instruction {
                opcode,
                mnemonic: Mnemonic::STA,
                mode: AddressingMode::Absolute_Y,
                none_addressing: false,
                size: 3,
                cycles: 5,
            },
            0x81 => Instruction {
                opcode,
                mnemonic: Mnemonic::STA,
                mode: AddressingMode::Indirect_X,
                none_addressing: false,
                size: 2,
                cycles: 6,
            },
            0x91 => Instruction {
                opcode,
                mnemonic: Mnemonic::STA,
                mode: AddressingMode::Indirect_Y,
                none_addressing: false,
                size: 2,
                cycles: 6,
            },
            // STX
            0x86 => Instruction {
                opcode,
                mnemonic: Mnemonic::STX,
                mode: AddressingMode::ZeroPage,
                none_addressing: false,
                size: 2,
                cycles: 3,
            },
            0x96 => Instruction {
                opcode,
                mnemonic: Mnemonic::STX,
                mode: AddressingMode::ZeroPage_Y,
                none_addressing: false,
                size: 2,
                cycles: 4,
            },
            0x8E => Instruction {
                opcode,
                mnemonic: Mnemonic::STX,
                mode: AddressingMode::Absolute,
                none_addressing: false,
                size: 3,
                cycles: 4,
            },
            // STY
            0x84 => Instruction {
                opcode,
                mnemonic: Mnemonic::STY,
                mode: AddressingMode::ZeroPage,
                none_addressing: false,
                size: 2,
                cycles: 3,
            },
            0x94 => Instruction {
                opcode,
                mnemonic: Mnemonic::STY,
                mode: AddressingMode::ZeroPage_X,
                none_addressing: false,
                size: 2,
                cycles: 4,
            },
            0x8C => Instruction {
                opcode,
                mnemonic: Mnemonic::STY,
                mode: AddressingMode::Absolute,
                none_addressing: false,
                size: 3,
                cycles: 4,
            },
            // TAX
            0xAA => Instruction {
                opcode,
                mnemonic: Mnemonic::TAX,
                mode: AddressingMode::Implied,
                none_addressing: true,
                size: 1,
                cycles: 2,
            },
            // TAY
            0xA8 => Instruction {
                opcode,
                mnemonic: Mnemonic::TAY,
                mode: AddressingMode::Implied,
                none_addressing: true,
                size: 1,
                cycles: 2,
            },
            // TSX
            0xBA => Instruction {
                opcode,
                mnemonic: Mnemonic::TSX,
                mode: AddressingMode::Implied,
                none_addressing: true,
                size: 1,
                cycles: 2,
            },
            // TXA
            0x8A => Instruction {
                opcode,
                mnemonic: Mnemonic::TXA,
                mode: AddressingMode::Implied,
                none_addressing: true,
                size: 1,
                cycles: 2,
            },
            // TXS
            0x9A => Instruction {
                opcode,
                mnemonic: Mnemonic::TXS,
                mode: AddressingMode::Implied,
                none_addressing: true,
                size: 1,
                cycles: 2,
            },
            // TYA
            0x98 => Instruction {
                opcode,
                mnemonic: Mnemonic::TYA,
                mode: AddressingMode::Implied,
                none_addressing: true,
                size: 1,
                cycles: 2,
            },
            // Unofficial opcodes
            0x04 | 0x44 | 0x64 => Instruction {
                opcode,
                mnemonic: Mnemonic::UNOP,
                mode: AddressingMode::ZeroPage,
                none_addressing: false,
                size: 2,
                cycles: 3,
            },
            0x14 | 0x34 | 0x54 | 0x74 | 0xD4 | 0xF4 => Instruction {
                opcode,
                mnemonic: Mnemonic::UNOP,
                mode: AddressingMode::ZeroPage_X,
                none_addressing: false,
                size: 2,
                cycles: 4,
            },
            0x0C => Instruction {
                opcode,
                mnemonic: Mnemonic::UNOP,
                mode: AddressingMode::Absolute,
                none_addressing: false,
                size: 3,
                cycles: 4,
            },
            0x1C | 0x3C | 0x5C | 0x7C | 0xDC | 0xFC => Instruction {
                opcode,
                mnemonic: Mnemonic::UNOP,
                mode: AddressingMode::Absolute_X,
                none_addressing: false,
                size: 3,
                cycles: 4,
            },
            // KIL
            0x02 | 0x12 | 0x22 | 0x32 | 0x42 | 0x52 | 0x62 | 0x72 | 0x92 | 0xB2 | 0xD2 | 0xF2 => {
                Instruction {
                    opcode,
                    mnemonic: Mnemonic::UNOP,
                    mode: AddressingMode::Implied,
                    none_addressing: false,
                    size: 1,
                    cycles: 2,
                }
            }
            0x1A | 0x3A | 0x5A | 0x7A | 0xDA | 0xFA => Instruction {
                opcode,
                mnemonic: Mnemonic::UNOP,
                mode: AddressingMode::Implied,
                none_addressing: false,
                size: 1,
                cycles: 2,
            },
            0x80 | 0x82 | 0x89 | 0xc2 | 0xe2 => Instruction {
                opcode,
                mnemonic: Mnemonic::UNOP,
                mode: AddressingMode::Immediate,
                none_addressing: false,
                size: 2,
                cycles: 2,
            },
            // LAX
            0xA7 => Instruction {
                opcode,
                mnemonic: Mnemonic::LAX,
                mode: AddressingMode::ZeroPage,
                none_addressing: false,
                size: 2,
                cycles: 3,
            },
            0xB7 => Instruction {
                opcode,
                mnemonic: Mnemonic::LAX,
                mode: AddressingMode::ZeroPage_Y,
                none_addressing: false,
                size: 2,
                cycles: 4,
            },
            0xAF => Instruction {
                opcode,
                mnemonic: Mnemonic::LAX,
                mode: AddressingMode::Absolute,
                none_addressing: false,
                size: 3,
                cycles: 4,
            },
            0xBF => Instruction {
                opcode,
                mnemonic: Mnemonic::LAX,
                mode: AddressingMode::Absolute_Y,
                none_addressing: false,
                size: 3,
                cycles: 4,
            },
            0xA3 => Instruction {
                opcode,
                mnemonic: Mnemonic::LAX,
                mode: AddressingMode::Indirect_X,
                none_addressing: false,
                size: 2,
                cycles: 6,
            },
            0xB3 => Instruction {
                opcode,
                mnemonic: Mnemonic::LAX,
                mode: AddressingMode::Indirect_Y,
                none_addressing: false,
                size: 2,
                cycles: 6,
            },
            // SAX
            0x87 => Instruction {
                opcode,
                mnemonic: Mnemonic::SAX,
                mode: AddressingMode::ZeroPage,
                none_addressing: false,
                size: 2,
                cycles: 3,
            },
            0x97 => Instruction {
                opcode,
                mnemonic: Mnemonic::SAX,
                mode: AddressingMode::ZeroPage_Y,
                none_addressing: false,
                size: 2,
                cycles: 4,
            },
            0x8F => Instruction {
                opcode,
                mnemonic: Mnemonic::SAX,
                mode: AddressingMode::Absolute,
                none_addressing: false,
                size: 3,
                cycles: 4,
            },
            0x83 => Instruction {
                opcode,
                mnemonic: Mnemonic::SAX,
                mode: AddressingMode::Indirect_X,
                none_addressing: false,
                size: 2,
                cycles: 6,
            },
            0xEB => Instruction {
                opcode,
                mnemonic: Mnemonic::USBC,
                mode: AddressingMode::Immediate,
                none_addressing: false,
                size: 2,
                cycles: 2,
            },
            // DCP
            0xC7 => Instruction {
                opcode,
                mnemonic: Mnemonic::DCP,
                mode: AddressingMode::ZeroPage,
                none_addressing: false,
                size: 2,
                cycles: 5,
            },
            0xD7 => Instruction {
                opcode,
                mnemonic: Mnemonic::DCP,
                mode: AddressingMode::ZeroPage_X,
                none_addressing: false,
                size: 2,
                cycles: 6,
            },
            0xCF => Instruction {
                opcode,
                mnemonic: Mnemonic::DCP,
                mode: AddressingMode::Absolute,
                none_addressing: false,
                size: 3,
                cycles: 6,
            },
            0xDF => Instruction {
                opcode,
                mnemonic: Mnemonic::DCP,
                mode: AddressingMode::Absolute_X,
                none_addressing: false,
                size: 3,
                cycles: 7,
            },
            0xDB => Instruction {
                opcode,
                mnemonic: Mnemonic::DCP,
                mode: AddressingMode::Absolute_Y,
                none_addressing: false,
                size: 3,
                cycles: 7,
            },
            0xD3 => Instruction {
                opcode,
                mnemonic: Mnemonic::DCP,
                mode: AddressingMode::Indirect_Y,
                none_addressing: false,
                size: 2,
                cycles: 8,
            },
            0xC3 => Instruction {
                opcode,
                mnemonic: Mnemonic::DCP,
                mode: AddressingMode::Indirect_X,
                none_addressing: false,
                size: 2,
                cycles: 8,
            },
            // ISB
            0xE7 => Instruction {
                opcode,
                mnemonic: Mnemonic::ISB,
                mode: AddressingMode::ZeroPage,
                none_addressing: false,
                size: 2,
                cycles: 5,
            },
            0xF7 => Instruction {
                opcode,
                mnemonic: Mnemonic::ISB,
                mode: AddressingMode::ZeroPage_X,
                none_addressing: false,
                size: 2,
                cycles: 6,
            },
            0xEF => Instruction {
                opcode,
                mnemonic: Mnemonic::ISB,
                mode: AddressingMode::Absolute,
                none_addressing: false,
                size: 3,
                cycles: 6,
            },
            0xFF => Instruction {
                opcode,
                mnemonic: Mnemonic::ISB,
                mode: AddressingMode::Absolute_X,
                none_addressing: false,
                size: 3,
                cycles: 7,
            },
            0xFB => Instruction {
                opcode,
                mnemonic: Mnemonic::ISB,
                mode: AddressingMode::Absolute_Y,
                none_addressing: false,
                size: 3,
                cycles: 7,
            },
            0xE3 => Instruction {
                opcode,
                mnemonic: Mnemonic::ISB,
                mode: AddressingMode::Indirect_X,
                none_addressing: false,
                size: 2,
                cycles: 8,
            },
            0xF3 => Instruction {
                opcode,
                mnemonic: Mnemonic::ISB,
                mode: AddressingMode::Indirect_Y,
                none_addressing: false,
                size: 2,
                cycles: 8,
            },
            // SLO
            0x07 => Instruction {
                opcode,
                mnemonic: Mnemonic::SLO,
                mode: AddressingMode::ZeroPage,
                none_addressing: false,
                size: 2,
                cycles: 5,
            },
            0x17 => Instruction {
                opcode,
                mnemonic: Mnemonic::SLO,
                mode: AddressingMode::ZeroPage_X,
                none_addressing: false,
                size: 2,
                cycles: 6,
            },
            0x0F => Instruction {
                opcode,
                mnemonic: Mnemonic::SLO,
                mode: AddressingMode::Absolute,
                none_addressing: false,
                size: 3,
                cycles: 6,
            },
            0x1F => Instruction {
                opcode,
                mnemonic: Mnemonic::SLO,
                mode: AddressingMode::Absolute_X,
                none_addressing: false,
                size: 3,
                cycles: 7,
            },
            0x1B => Instruction {
                opcode,
                mnemonic: Mnemonic::SLO,
                mode: AddressingMode::Absolute_Y,
                none_addressing: false,
                size: 3,
                cycles: 7,
            },
            0x03 => Instruction {
                opcode,
                mnemonic: Mnemonic::SLO,
                mode: AddressingMode::Indirect_X,
                none_addressing: false,
                size: 2,
                cycles: 8,
            },
            0x13 => Instruction {
                opcode,
                mnemonic: Mnemonic::SLO,
                mode: AddressingMode::Indirect_Y,
                none_addressing: false,
                size: 2,
                cycles: 8,
            },
            // RLA
            0x27 => Instruction {
                opcode,
                mnemonic: Mnemonic::RLA,
                mode: AddressingMode::ZeroPage,
                none_addressing: false,
                size: 2,
                cycles: 5,
            },
            0x37 => Instruction {
                opcode,
                mnemonic: Mnemonic::RLA,
                mode: AddressingMode::ZeroPage_X,
                none_addressing: false,
                size: 2,
                cycles: 6,
            },
            0x2F => Instruction {
                opcode,
                mnemonic: Mnemonic::RLA,
                mode: AddressingMode::Absolute,
                none_addressing: false,
                size: 3,
                cycles: 6,
            },
            0x3F => Instruction {
                opcode,
                mnemonic: Mnemonic::RLA,
                mode: AddressingMode::Absolute_X,
                none_addressing: false,
                size: 3,
                cycles: 7,
            },
            0x3B => Instruction {
                opcode,
                mnemonic: Mnemonic::RLA,
                mode: AddressingMode::Absolute_Y,
                none_addressing: false,
                size: 3,
                cycles: 7,
            },
            0x23 => Instruction {
                opcode,
                mnemonic: Mnemonic::RLA,
                mode: AddressingMode::Indirect_X,
                none_addressing: false,
                size: 2,
                cycles: 8,
            },
            0x33 => Instruction {
                opcode,
                mnemonic: Mnemonic::RLA,
                mode: AddressingMode::Indirect_Y,
                none_addressing: false,
                size: 2,
                cycles: 8,
            },
            // SRE
            0x47 => Instruction {
                opcode,
                mnemonic: Mnemonic::SRE,
                mode: AddressingMode::ZeroPage,
                none_addressing: false,
                size: 2,
                cycles: 5,
            },
            0x57 => Instruction {
                opcode,
                mnemonic: Mnemonic::SRE,
                mode: AddressingMode::ZeroPage_X,
                none_addressing: false,
                size: 2,
                cycles: 6,
            },
            0x4F => Instruction {
                opcode,
                mnemonic: Mnemonic::SRE,
                mode: AddressingMode::Absolute,
                none_addressing: false,
                size: 3,
                cycles: 6,
            },
            0x5F => Instruction {
                opcode,
                mnemonic: Mnemonic::SRE,
                mode: AddressingMode::Absolute_X,
                none_addressing: false,
                size: 3,
                cycles: 7,
            },
            0x5B => Instruction {
                opcode,
                mnemonic: Mnemonic::SRE,
                mode: AddressingMode::Absolute_Y,
                none_addressing: false,
                size: 3,
                cycles: 7,
            },
            0x43 => Instruction {
                opcode,
                mnemonic: Mnemonic::SRE,
                mode: AddressingMode::Indirect_X,
                none_addressing: false,
                size: 2,
                cycles: 8,
            },
            0x53 => Instruction {
                opcode,
                mnemonic: Mnemonic::SRE,
                mode: AddressingMode::Indirect_Y,
                none_addressing: false,
                size: 2,
                cycles: 8,
            },
            // RRA
            0x67 => Instruction {
                opcode,
                mnemonic: Mnemonic::RRA,
                mode: AddressingMode::ZeroPage,
                none_addressing: false,
                size: 2,
                cycles: 5,
            },
            0x77 => Instruction {
                opcode,
                mnemonic: Mnemonic::RRA,
                mode: AddressingMode::ZeroPage_X,
                none_addressing: false,
                size: 2,
                cycles: 6,
            },
            0x6F => Instruction {
                opcode,
                mnemonic: Mnemonic::RRA,
                mode: AddressingMode::Absolute,
                none_addressing: false,
                size: 3,
                cycles: 6,
            },
            0x7F => Instruction {
                opcode,
                mnemonic: Mnemonic::RRA,
                mode: AddressingMode::Absolute_X,
                none_addressing: false,
                size: 3,
                cycles: 7,
            },
            0x7B => Instruction {
                opcode,
                mnemonic: Mnemonic::RRA,
                mode: AddressingMode::Absolute_Y,
                none_addressing: false,
                size: 3,
                cycles: 7,
            },
            0x63 => Instruction {
                opcode,
                mnemonic: Mnemonic::RRA,
                mode: AddressingMode::Indirect_X,
                none_addressing: false,
                size: 2,
                cycles: 8,
            },
            0x73 => Instruction {
                opcode,
                mnemonic: Mnemonic::RRA,
                mode: AddressingMode::Indirect_Y,
                none_addressing: false,
                size: 2,
                cycles: 8,
            },

            _ => Instruction {
                opcode,
                mnemonic: Mnemonic::UNKOWN,
                mode: AddressingMode::ZeroPage,
                none_addressing: false,
                size: 1,
                cycles: 3,
            },
            // _ => panic!("Unknown opcode {:X}", opcode),
        }
    }
}
