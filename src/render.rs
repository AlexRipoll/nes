use sdl2::{event::Event, keyboard::Keycode, pixels::PixelFormatEnum};

use crate::cartridge::Rom;
use crate::frame::{self, Frame};
use crate::ppu::ppu::PPU;

fn show_tile(chr_rom: &Vec<u8>, bank: usize, tile_n: usize) -> Frame {
    assert!(bank <= 1);

    let mut frame = Frame::new();
    let bank = (bank * 0x1000) as usize;

    let tile = &chr_rom[(bank + tile_n * 16)..=(bank + tile_n * 16 + 15)];

    for y in 0..=7 {
        let mut upper = tile[y];
        let mut lower = tile[y + 8];

        for x in (0..=7).rev() {
            let value = (1 & upper) << 1 | (1 & lower);
            upper = upper >> 1;
            lower = lower >> 1;
            let rgb = match value {
                0 => frame::SYSTEM_PALLETE[0x01],
                1 => frame::SYSTEM_PALLETE[0x23],
                2 => frame::SYSTEM_PALLETE[0x27],
                3 => frame::SYSTEM_PALLETE[0x30],
                _ => panic!("can't be"),
            };
            frame.set_pixel(x, y, rgb)
        }
    }

    frame
}

fn show_tile_bank(chr_rom: &Vec<u8>, bank: usize) -> Frame {
    assert!(bank <= 1);

    let mut frame = Frame::new();
    let mut tile_y = 0;
    let mut tile_x = 0;
    let bank = (bank * 0x1000) as usize;

    for tile_n in 0..255 {
        if tile_n != 0 && tile_n % 20 == 0 {
            tile_y += 10;
            tile_x = 0;
        }
        let tile = &chr_rom[(bank + tile_n * 16)..=(bank + tile_n * 16 + 15)];

        for y in 0..=7 {
            let mut upper = tile[y];
            let mut lower = tile[y + 8];

            for x in (0..=7).rev() {
                let value = (1 & upper) << 1 | (1 & lower);
                upper = upper >> 1;
                lower = lower >> 1;
                let rgb = match value {
                    0 => frame::SYSTEM_PALLETE[0x01],
                    1 => frame::SYSTEM_PALLETE[0x23],
                    2 => frame::SYSTEM_PALLETE[0x27],
                    3 => frame::SYSTEM_PALLETE[0x30],
                    _ => panic!("can't be"),
                };
                frame.set_pixel(tile_x + x, tile_y + y, rgb)
            }
        }

        tile_x += 10;
    }
    frame
}

fn render_tiles() {
    // init sdl2
    let sdl_context = sdl2::init().unwrap();
    let video_subsystem = sdl_context.video().unwrap();
    let window = video_subsystem
        .window("Tile viewer", (256.0 * 3.0) as u32, (240.0 * 3.0) as u32)
        .position_centered()
        .build()
        .unwrap();

    let mut canvas = window.into_canvas().present_vsync().build().unwrap();
    let mut event_pump = sdl_context.event_pump().unwrap();
    canvas.set_scale(3.0, 3.0).unwrap();

    let creator = canvas.texture_creator();
    let mut texture = creator
        .create_texture_target(PixelFormatEnum::RGB24, 256, 240)
        .unwrap();

    //load the game
    let bytes: Vec<u8> = std::fs::read("Alter_Ego.nes").unwrap();
    let rom = Rom::new(bytes).unwrap();

    let right_bank = show_tile_bank(&rom.chr_rom, 1);

    texture.update(None, &right_bank.data, 256 * 3).unwrap();
    canvas.copy(&texture, None, None).unwrap();
    canvas.present();

    loop {
        for event in event_pump.poll_iter() {
            match event {
                Event::Quit { .. }
                | Event::KeyDown {
                    keycode: Some(Keycode::Escape),
                    ..
                } => std::process::exit(0),
                _ => { /* do nothing */ }
            }
        }
    }
}

pub fn render(ppu: &PPU, frame: &mut Frame) {
    let bank = ppu.ctrl.background_pattern_table_address();

    for i in 0..0x03c0 {
        // just for now, lets use the first nametable
        let tile = ppu.vram[i] as u16;
        let tile_x = i % 32;
        let tile_y = i / 32;
        let tile = &ppu.chr_rom[(bank + tile * 16) as usize..=(bank + tile * 16 + 15) as usize];

        for y in 0..=7 {
            let mut upper = tile[y];
            let mut lower = tile[y + 8];

            for x in (0..=7).rev() {
                let value = (1 & upper) << 1 | (1 & lower);
                upper = upper >> 1;
                lower = lower >> 1;
                let rgb = match value {
                    0 => frame::SYSTEM_PALLETE[0x01],
                    1 => frame::SYSTEM_PALLETE[0x23],
                    2 => frame::SYSTEM_PALLETE[0x27],
                    3 => frame::SYSTEM_PALLETE[0x30],
                    _ => panic!("can't be"),
                };
                frame.set_pixel(tile_x * 8 + x, tile_y * 8 + y, rgb)
            }
        }
    }
}
