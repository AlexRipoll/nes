use std::usize;

const INES_MAGIC_NUMBER: [u8; 4] = [0x4E, 0x45, 0x53, 0x1A]; //  corresponds to the string NES^Z
pub const PRG_ROM_16KB_UNITS: usize = 16_384;
pub const CHR_ROM_8KB_UNITS: usize = 8_192;
const HEADER_SIZE: usize = 16;
const TRAINER_SIZE: usize = 512;

#[derive(Debug)]
pub enum Mirroring {
    Horizontal,
    Vertical,
    FourScreen,
}

#[derive(Debug)]
pub struct Rom {
    pub prg_rom: Vec<u8>,
    chr_rom: Vec<u8>,
    mapper: u8,
    screen_mirroring: Mirroring,
}

impl Rom {
    /// https://www.nesdev.org/wiki/INES
    pub fn new(raw: Vec<u8>) -> Result<Rom, String> {
        if &raw[0..4] != INES_MAGIC_NUMBER {
            return Err("Invalid iNES file format".to_string());
        }

        if &raw[7] & 0b0000_1100 == 0b0000_1100 {
            return Err("iNES2.0 format is not suported".to_string());
        }

        let prg_rom_size = raw[4] as usize * PRG_ROM_16KB_UNITS;
        let chr_rom_size = raw[5] as usize * CHR_ROM_8KB_UNITS;

        let prg_rom_start = HEADER_SIZE
            + if &raw[6] & 0b0000_0100 != 0 {
                TRAINER_SIZE
            } else {
                0
            };
        let chr_rom_start = prg_rom_start + prg_rom_size;

        let prg_rom = raw[prg_rom_start..(prg_rom_start + prg_rom_size)].to_vec();
        let chr_rom = raw[chr_rom_start..(chr_rom_start + chr_rom_size)].to_vec();

        let lower_mapper = &raw[6] & 0b1111_0000;
        let upper_mapper = &raw[7] & 0b1111_0000;
        let mapper = upper_mapper | (lower_mapper >> 4);

        let screen_mirroring = match (&raw[6] & 0b0000_0001 != 0, &raw[6] & 0b0000_1000 != 0) {
            (_, true) => Mirroring::FourScreen,
            (false, false) => Mirroring::Horizontal,
            (true, false) => Mirroring::Vertical,
        };

        Ok(Rom {
            prg_rom,
            chr_rom,
            mapper,
            screen_mirroring,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_valid_ines_rom() {
        // A mock valid iNES ROM with a simple 16KB PRG ROM and 8KB CHR ROM
        let mut raw_rom_data = vec![
            0x4E,
            0x45,
            0x53,
            0x1A,        // iNES header
            0x01,        // 1 unit of 16KB PRG ROM
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
        raw_rom_data.extend(vec![0xFF; PRG_ROM_16KB_UNITS]); // 16KB PRG ROM filled with 0xFF
        raw_rom_data.extend(vec![0xFF; CHR_ROM_8KB_UNITS]); // 8KB CHR ROM filled with 0xFF

        let rom = Rom::new(raw_rom_data).expect("ROM should parse successfully");

        assert_eq!(rom.prg_rom.len(), PRG_ROM_16KB_UNITS);
        assert_eq!(rom.chr_rom.len(), CHR_ROM_8KB_UNITS);
        assert_eq!(rom.mapper, 0);
        assert!(matches!(rom.screen_mirroring, Mirroring::Vertical));
    }

    #[test]
    fn test_horizontal_mirroring() {
        let mut raw_rom_data = vec![
            0x4E,
            0x45,
            0x53,
            0x1A,        // iNES header
            0x01,        // 1 unit of 16KB PRG ROM
            0x01,        // 1 unit of 8KB CHR ROM
            0b0000_0000, // Mirroring = Horizontal, no trainer
            0b0000_0000, // Mapper info
            0x00,
            0x00,
            0x00,
            0x00,
            0x00, // Padding (not used for these tests)
            0x00, // Padding (not used for these tests)
            0x00, // Padding (not used for these tests)
            0x00, // Padding (not used for these tests)
            0x00, // Padding (not used for these tests)
        ];
        raw_rom_data.extend(vec![0xFF; PRG_ROM_16KB_UNITS]); // 16KB PRG ROM filled with 0xFF
        raw_rom_data.extend(vec![0xFF; CHR_ROM_8KB_UNITS]); // 8KB CHR ROM filled with 0xFF

        let rom = Rom::new(raw_rom_data).expect("ROM should parse successfully");

        assert_eq!(rom.prg_rom.len(), PRG_ROM_16KB_UNITS);
        assert_eq!(rom.chr_rom.len(), CHR_ROM_8KB_UNITS);
        assert_eq!(rom.mapper, 0);
        assert!(matches!(rom.screen_mirroring, Mirroring::Horizontal));
    }

    #[test]
    fn test_four_screen_mirroring() {
        let mut raw_rom_data = vec![
            0x4E,
            0x45,
            0x53,
            0x1A,        // iNES header
            0x01,        // 1 unit of 16KB PRG ROM
            0x01,        // 1 unit of 8KB CHR ROM
            0b0000_1000, // Four-screen mirroring, no trainer
            0b0000_0000, // Mapper info
            0x00,
            0x00,
            0x00,
            0x00,
            0x00, // Padding (not used for these tests)
            0x00, // Padding (not used for these tests)
            0x00, // Padding (not used for these tests)
            0x00, // Padding (not used for these tests)
            0x00, // Padding (not used for these tests)
        ];
        raw_rom_data.extend(vec![0xFF; PRG_ROM_16KB_UNITS]); // 16KB PRG ROM filled with 0xFF
        raw_rom_data.extend(vec![0xFF; CHR_ROM_8KB_UNITS]); // 8KB CHR ROM filled with 0xFF

        let rom = Rom::new(raw_rom_data).expect("ROM should parse successfully");

        assert_eq!(rom.prg_rom.len(), PRG_ROM_16KB_UNITS);
        assert_eq!(rom.chr_rom.len(), CHR_ROM_8KB_UNITS);
        assert_eq!(rom.mapper, 0);
        assert!(matches!(rom.screen_mirroring, Mirroring::FourScreen));
    }

    #[test]
    fn test_unsupported_ines2_format() {
        let mut raw_rom_data = vec![
            0x4E,
            0x45,
            0x53,
            0x1A,        // iNES header
            0x01,        // 1 unit of 16KB PRG ROM
            0x01,        // 1 unit of 8KB CHR ROM
            0b0000_0001, // Mirroring = Vertical, no trainer
            0b0000_1100, // Indicates iNES 2.0 format
            0x00,
            0x00,
            0x00,
            0x00,
            0x00, // Padding (not used for these tests)
            0x00, // Padding (not used for these tests)
            0x00, // Padding (not used for these tests)
            0x00, // Padding (not used for these tests)
            0x00, // Padding (not used for these tests)
        ];
        raw_rom_data.extend(vec![0xFF; 16_384]); // 16KB PRG ROM filled with 0xFF

        let result = Rom::new(raw_rom_data);

        assert!(result.is_err());
        assert_eq!(
            result.unwrap_err(),
            "iNES2.0 format is not suported".to_string()
        );
    }

    #[test]
    fn test_invalid_ines_file_format() {
        let mut raw_rom_data = vec![
            0x00,
            0x00,
            0x00,
            0x00,        // Invalid iNES header
            0x01,        // 1 unit of 16KB PRG ROM
            0x01,        // 1 unit of 8KB CHR ROM
            0b0000_0001, // Mirroring = Vertical, no trainer
            0b0000_0000, // Mapper info
            0x00,
            0x00,
            0x00,
            0x00,
            0x00, // Padding (not used for these tests)
            0x00, // Padding (not used for these tests)
            0x00, // Padding (not used for these tests)
            0x00, // Padding (not used for these tests)
            0x00, // Padding (not used for these tests)
        ];
        raw_rom_data.extend(vec![0xFF; 16_384]); // 16KB PRG ROM filled with 0xFF

        let result = Rom::new(raw_rom_data);

        assert!(result.is_err());
        assert_eq!(result.unwrap_err(), "Invalid iNES file format".to_string());
    }
}
