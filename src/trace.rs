use crate::{
    cpu::CPU,
    instruction::{AddressingMode, Instruction},
};

pub fn trace(cpu: &CPU) -> String {
    let opcode = cpu.mem_read(cpu.program_counter);
    let instruction: Instruction = Instruction::from(opcode);

    let begin = cpu.program_counter;
    let mut hex_dump: Vec<u8> = Vec::new();
    hex_dump.push(opcode);

    let (mem_address, stored_value) = match instruction.mode {
        AddressingMode::Implied | AddressingMode::Accumulator => (0, 0),
        _ => {
            let address = cpu.absolute_address(&instruction.mode, begin + 1);
            (address, cpu.mem_read(address))
        }
    };

    let tmp = match instruction.size {
        1 => match instruction.opcode {
            0x0a | 0x4a | 0x2a | 0x6a => format!("A "),
            _ => String::new(),
        },
        2 => {
            let address = cpu.mem_read(begin + 1);
            hex_dump.push(address);
            format_two_byte_instruction(
                cpu,
                instruction.mode,
                address,
                mem_address,
                stored_value,
                begin,
            )
        }
        3 => format_three_byte_instruction(
            cpu,
            begin,
            &mut hex_dump,
            &instruction,
            mem_address,
            stored_value,
        ),

        _ => "".to_string(),
    };

    let hex_str = hex_dump
        .iter()
        .map(|z| format!("{:02x}", z))
        .collect::<Vec<String>>()
        .join(" ");

    let asm_str = format!(
        "{:04x}  {:8} {: >4} {}",
        begin,
        hex_str,
        instruction.mnemonic.to_string(),
        tmp
    )
    .trim()
    .to_string();

    format!(
        "{:47} A:{:02x} X:{:02x} Y:{:02x} P:{:02x} SP:{:02x}",
        asm_str, cpu.register_a, cpu.register_x, cpu.register_y, cpu.status, cpu.stack_ptr,
    )
    .to_ascii_uppercase()
}

fn format_two_byte_instruction(
    cpu: &CPU,
    mode: AddressingMode,
    address: u8,
    mem_address: u16,
    stored_value: u8,
    begin: u16,
) -> String {
    match mode {
        AddressingMode::Immediate => format!("#${:02x}", address),
        AddressingMode::ZeroPage => format!("${:02x} = {:02x}", mem_address, stored_value),
        AddressingMode::ZeroPage_X => format!(
            "${:02x},X @ {:02x} = {:02x}",
            address, mem_address, stored_value
        ),
        AddressingMode::ZeroPage_Y => format!(
            "${:02x},Y @ {:02x} = {:02x}",
            address, mem_address, stored_value
        ),
        AddressingMode::Relative => {
            let target_address = (begin as usize + 2).wrapping_add(address as i8 as usize);
            format!("${:04x}", target_address)
        }
        AddressingMode::Indirect_X => format!(
            "(${:02x},X) @ {:02x} = {:04x} = {:02x}",
            address,
            (address.wrapping_add(cpu.register_x)),
            mem_address,
            stored_value
        ),
        AddressingMode::Indirect_Y => format!(
            "(${:02x}),Y = {:04x} @ {:04x} = {:02x}",
            address,
            mem_address.wrapping_sub(cpu.register_y as u16),
            mem_address,
            stored_value
        ),
        _ => unreachable!(
            "unexpected addressing mode {:?} for instruction size 2",
            mode
        ),
    }
}

fn format_three_byte_instruction(
    cpu: &CPU,
    begin: u16,
    hex_dump: &mut Vec<u8>,
    instruction: &Instruction,
    mem_address: u16,
    stored_value: u8,
) -> String {
    let address_lsb = cpu.mem_read(begin + 1);
    let address_msb = cpu.mem_read(begin + 2);
    hex_dump.push(address_lsb);
    hex_dump.push(address_msb);

    let address = cpu.mem_read_u16(begin + 1);

    if instruction.none_addressing {
        if instruction.opcode == 0x6c {
            //jmp indirect
            let jmp_addr = if address & 0x00FF == 0x00FF {
                let lo = cpu.mem_read(address);
                let hi = cpu.mem_read(address & 0xFF00);
                (hi as u16) << 8 | (lo as u16)
            } else {
                cpu.mem_read_u16(address)
            };

            return format!("(${:04x}) = {:04x}", address, jmp_addr);
        } else {
            return format!("${:04x}", mem_address);
        }
    }

    match instruction.mode {
        AddressingMode::Indirect => {
            //jmp indirect
            let jmp_addr = if address & 0x00FF == 0x00FF {
                let lo = cpu.mem_read(address);
                let hi = cpu.mem_read(address & 0xFF00);
                (hi as u16) << 8 | (lo as u16)
            } else {
                cpu.mem_read_u16(address)
            };

            // let jmp_addr = cpu.mem_read_u16(address);
            format!("(${:04x}) = {:04x}", address, jmp_addr)
        }
        AddressingMode::Absolute => {
            format!("${:04x} = {:02x}", mem_address, stored_value)
        }
        AddressingMode::Absolute_X => format!(
            "${:04x},X @ {:04x} = {:02x}",
            address, mem_address, stored_value
        ),
        AddressingMode::Absolute_Y => format!(
            "${:04x},Y @ {:04x} = {:02x}",
            address, mem_address, stored_value
        ),
        _ => panic!(
            "unexpected addressing mode {:?} has ops-len 3. code {:02x}",
            instruction.mode, instruction.opcode
        ),
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{
        bus::Bus,
        cartridge::{Rom, CHR_ROM_8KB_UNITS, PRG_ROM_16KB_UNITS},
    };

    fn rom_test() -> Rom {
        let mut raw_rom_data = vec![
            0x4E,
            0x45,
            0x53,
            0x1A,        // iNES header
            0x02,        // 2 unit of 16KB PRG ROM
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
        raw_rom_data.extend(vec![0xFF; 2 * PRG_ROM_16KB_UNITS]); // 16KB PRG ROM filled with 0xFF
        raw_rom_data.extend(vec![0xFF; CHR_ROM_8KB_UNITS]); // 8KB CHR ROM filled with 0xFF

        Rom::new(raw_rom_data).unwrap()
    }

    #[test]
    fn test_format_trace() {
        let mut bus = Bus::new(rom_test());
        bus.mem_write(100, 0xa2);
        bus.mem_write(101, 0x01);
        bus.mem_write(102, 0xca);
        bus.mem_write(103, 0x88);
        bus.mem_write(104, 0x00);

        let mut cpu = CPU::new(bus);
        cpu.program_counter = 0x64;
        cpu.register_a = 1;
        cpu.register_x = 2;
        cpu.register_y = 3;
        let mut result: Vec<String> = vec![];
        cpu.execute_program_with_callback(|cpu| {
            result.push(trace(cpu));
        });
        assert_eq!(
            "0064  A2 01     LDX #$01                        A:01 X:02 Y:03 P:24 SP:FD",
            result[0]
        );
        assert_eq!(
            "0066  CA        DEX                             A:01 X:01 Y:03 P:24 SP:FD",
            result[1]
        );
        assert_eq!(
            "0067  88        DEY                             A:01 X:00 Y:03 P:26 SP:FD",
            result[2]
        );
    }

    #[test]
    fn test_format_mem_access() {
        let mut bus = Bus::new(rom_test());
        // ORA ($33), Y
        bus.mem_write(100, 0x11);
        bus.mem_write(101, 0x33);

        //data
        bus.mem_write(0x33, 00);
        bus.mem_write(0x34, 04);

        //target cell
        bus.mem_write(0x400, 0xAA);

        let mut cpu = CPU::new(bus);
        cpu.program_counter = 0x64;
        cpu.register_y = 0;
        let mut result: Vec<String> = vec![];
        cpu.execute_program_with_callback(|cpu| {
            result.push(trace(cpu));
        });
        assert_eq!(
            "0064  11 33     ORA ($33),Y = 0400 @ 0400 = AA  A:00 X:00 Y:00 P:24 SP:FD",
            result[0]
        );
    }
}
