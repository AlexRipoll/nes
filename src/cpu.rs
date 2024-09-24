#[derive(Debug, Default)]
struct CPU {
    register_a: u8,
    register_x: u8,
    status: u8,
    program_counter: u16,
}

impl CPU {
    fn new() -> Self {
        CPU {
            register_a: 0,
            register_x: 0,
            status: 0,
            program_counter: 0,
        }
    }

    pub fn interpret(&mut self, program: Vec<u8>) {
        self.program_counter = 0;

        loop {
            let opcode = program[self.program_counter as usize];
            self.program_counter += 1;

            match opcode {
                0xA9 => {
                    let parameter = program[self.program_counter as usize];
                    self.program_counter += 1;
                    self.register_a = parameter;

                    // Clear zero and negative flags
                    self.status &= 0b0111_1101;

                    self.set_zero_and_negative_flags(self.register_a);
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

#[cfg(test)]
mod test {
    use crate::cpu::CPU;

    #[test]
    fn test_0xa9_lda_opcode() {
        let mut cpu = CPU::new();
        cpu.interpret(vec![0xa9, 0x05, 0x00]);
        assert_eq!(cpu.register_a, 0x05);
        assert!(cpu.status & 0b1000_0010 == 0);
    }

    #[test]
    fn test_0xa9_lda_opcode_zero_flag_set() {
        let mut cpu = CPU::new();
        cpu.interpret(vec![0xa9, 0x00, 0x00]);
        assert!(cpu.status & 0b0000_0010 == 0b10);
    }

    #[test]
    fn test_0xa9_lda_opcode_negative_flag_set() {
        let mut cpu = CPU::new();
        cpu.interpret(vec![0xa9, 0xf0, 0x00]);
        assert!(cpu.status & 0b1000_0000 == 0b1000_0000);
    }

    #[test]
    fn test_0xaa_tax_opcode() {
        let mut cpu = CPU::new();
        cpu.register_a = 0x05;
        cpu.interpret(vec![0xaa, 0x00]);
        assert_eq!(cpu.register_x, 0x05);
        assert!(cpu.status & 0b1000_0010 == 0);
    }

    #[test]
    fn test_0xaa_tax_opcode_zero_flag_set() {
        let mut cpu = CPU::new();
        cpu.register_a = 0x00;
        cpu.interpret(vec![0xaa, 0x00]);
        assert!(cpu.status & 0b0000_0010 == 0b10);
    }

    #[test]
    fn test_0xaa_tax_opcode_negative_flag_set() {
        let mut cpu = CPU::new();
        cpu.register_a = 0xf5;
        cpu.interpret(vec![0xaa, 0x00]);
        assert!(cpu.status & 0b1000_0000 == 0b1000_0000);
    }

    #[test]
    fn test_0xe8_inx_opcode() {
        let mut cpu = CPU::new();
        cpu.register_x = 0x05;
        cpu.interpret(vec![0xe8, 0x00]);
        assert_eq!(cpu.register_x, 0x06);
        assert!(cpu.status & 0b1000_0010 == 0);
    }

    #[test]
    fn test_0xe8_inx_opcode_zero_flag_set_with_overflow() {
        let mut cpu = CPU::new();
        cpu.register_x = 0xff;
        cpu.interpret(vec![0xe8, 0x00]);
        assert_eq!(cpu.register_x, 0x00);
        assert!(cpu.status & 0b0000_0010 == 0b10);
    }

    #[test]
    fn test_0xe8_inx_opcode_negative_flag_set() {
        let mut cpu = CPU::new();
        cpu.register_x = 0xf5;
        cpu.interpret(vec![0xe8, 0x00]);
        assert_eq!(cpu.register_x, 0xf6);
        assert!(cpu.status & 0b1000_0000 == 0b1000_0000);
    }

    #[test]
    fn test_opcode_combination() {
        let mut cpu = CPU::new();
        cpu.interpret(vec![0xa9, 0xc0, 0xaa, 0xe8, 0x00]);

        assert_eq!(cpu.register_x, 0xc1)
    }
}
