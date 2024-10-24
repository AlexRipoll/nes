use crate::cartridge::Mirroring;

use super::{
    address::PPUAddr, controller::PPUCtrl, mask::PPUMask, scroll::PPUScroll, status::PPUStatus,
    vram::Vram,
};

const MAX_CYCLES_PER_SCANLINE: u16 = 341;

#[derive(Debug)]
pub struct PPU {
    // Memory Map
    pub chr_rom: Vec<u8>,
    pub vram: Vram,

    //Registers
    pub ctrl: PPUCtrl,
    mask: PPUMask,
    status: PPUStatus,
    oam_address: u8,
    oam_data: [u8; 256],
    scroll: PPUScroll,
    addr: PPUAddr,

    cycles: usize,
    scanline: u16,
    open_bus: u8,
    pub nmi_interrupt: bool,
}

impl PPU {
    pub fn new(chr_rom: Vec<u8>, mirroring: Mirroring) -> Self {
        Self {
            chr_rom: chr_rom.clone(),
            vram: Vram::new(chr_rom, mirroring),

            ctrl: PPUCtrl::new(),
            mask: PPUMask::new(),
            status: PPUStatus::new(),
            oam_address: 0,
            oam_data: [0u8; 256],
            scroll: PPUScroll::new(),
            addr: PPUAddr::new(),

            cycles: 0,
            scanline: 0,
            open_bus: 0,
            nmi_interrupt: false,
        }
    }

    pub fn reset(&mut self) {
        self.ctrl.reset();
        self.status.reset();
        self.mask.reset();
        self.oam_data = [0; 0x100];
        self.vram.reset();
    }

    pub fn write_to_ctrl(&mut self, data: u8) {
        let ctrl_nmi_status = self.ctrl.vblank_nmi_enabled();
        self.ctrl.write(data);
        if !ctrl_nmi_status && self.ctrl.vblank_nmi_enabled() {
            self.nmi_interrupt = true;
        }
        // TODO: update t_address
    }

    pub fn write_to_mask(&mut self, data: u8) {
        self.mask.write(data);
    }

    pub fn read_status(&mut self) -> u8 {
        let data = self.status.read();
        self.addr.reset_latch();
        self.scroll.reset_latch();

        data
    }

    pub fn write_to_oam_addr(&mut self, value: u8) {
        self.oam_address = value;
    }

    pub fn write_to_oam_data(&mut self, value: u8) {
        self.oam_data[self.oam_address as usize] = value;
        self.oam_address = self.oam_address.wrapping_add(1);
    }

    pub fn read_oam_data(&self) -> u8 {
        self.oam_data[self.oam_address as usize]
    }

    pub fn write_to_scroll(&mut self, data: u8) {
        self.scroll.write(data);
    }

    pub fn write_to_addr(&mut self, data: u8) {
        self.addr.write(data);
    }

    pub fn write_data(&mut self, value: u8) {
        let address = self.addr.vram_address();
        self.vram.write_byte(address, value);

        self.addr.increment(self.ctrl.vram_address_increment());
    }

    pub fn read_data(&mut self) -> u8 {
        let address = self.addr.vram_address();
        self.addr.increment(self.ctrl.vram_address_increment());
        self.vram.read_byte(address)
    }

    pub fn write_oam_dma(&mut self, data: &[u8; 256]) {
        for x in data.iter() {
            self.oam_data[self.oam_address as usize] = *x;
            self.oam_address = self.oam_address.wrapping_add(1);
        }
    }

    fn increment_vram_addr(&mut self) {
        self.addr.increment(self.ctrl.vram_address_increment());
    }

    pub fn poll_nmi_interrupt(&mut self) -> bool {
        if self.nmi_interrupt {
            self.nmi_interrupt = false;
            return true;
        }

        self.nmi_interrupt
    }
}
