use std::fs;

use bus::Bus;
use cartridge::Rom;
use cpu::CPU;
use sdl2::event::Event;
use sdl2::keyboard::Keycode;
use sdl2::pixels::{Color, PixelFormatEnum};
use sdl2::EventPump;
use trace::trace;

mod bus;
mod cartridge;
mod cpu;
mod frame;
mod instruction;
mod ppu;
mod render;
mod trace;

fn main() -> Result<(), String> {
    // let sdl_context = sdl2::init()?;
    // let video_subsystem = sdl_context.video()?;
    //
    // let window = video_subsystem
    //     .window("Snake game", (32.0 * 10.0) as u32, (32.0 * 10.0) as u32)
    //     .position_centered()
    //     .resizable()
    //     .build()
    //     .map_err(|e| e.to_string())?;
    //
    // let mut canvas = window.into_canvas().build().map_err(|e| e.to_string())?;
    //
    // let mut event_pump = sdl_context.event_pump()?;
    //
    // let creator = canvas.texture_creator();
    // let mut texture = creator
    //     .create_texture_target(PixelFormatEnum::RGB24, 32, 32)
    //     .unwrap();
    //
    // let mut screen_state = [0 as u8; 32 * 3 * 32];
    // let mut rng = rand::thread_rng();

    let rom_dump = fs::read("nestest.nes").unwrap();
    let rom = Rom::new(rom_dump).unwrap();
    let bus = Bus::new(rom);

    let mut cpu = CPU::new(bus);

    cpu.reset();
    cpu.program_counter = 0xC000;
    cpu.execute_program_with_callback(move |cpu| {
        println!("{}", trace(cpu));
    });

    // cpu.run_with_callback(game_code, move |cpu| {
    //     handle_user_input(cpu, &mut event_pump);
    //
    //     cpu.mem_write(0xfe, rng.gen_range(1..16));
    //
    //     if read_screen_state(cpu, &mut screen_state) {
    //         texture.update(None, &screen_state, 32 * 3).unwrap();
    //         canvas.copy(&texture, None, None).unwrap();
    //         canvas.present();
    //     }
    //
    //     ::std::thread::sleep(std::time::Duration::new(0, 70_000));
    // });

    Ok(())
}

fn handle_user_input(cpu: &mut CPU, event_pump: &mut EventPump) {
    for event in event_pump.poll_iter() {
        match event {
            Event::Quit { .. }
            | Event::KeyDown {
                keycode: Some(Keycode::Escape),
                ..
            } => std::process::exit(0),
            Event::KeyDown {
                keycode: Some(Keycode::W),
                ..
            } => {
                cpu.mem_write(0xff, 0x77);
            }
            Event::KeyDown {
                keycode: Some(Keycode::S),
                ..
            } => {
                cpu.mem_write(0xff, 0x73);
            }
            Event::KeyDown {
                keycode: Some(Keycode::A),
                ..
            } => {
                cpu.mem_write(0xff, 0x61);
            }
            Event::KeyDown {
                keycode: Some(Keycode::D),
                ..
            } => {
                cpu.mem_write(0xff, 0x64);
            }
            _ => { /* do nothing */ }
        }
    }
}

fn color(byte: u8) -> Color {
    match byte {
        0 => sdl2::pixels::Color::BLACK,
        1 => sdl2::pixels::Color::WHITE,
        2 | 9 => sdl2::pixels::Color::GREY,
        3 | 10 => sdl2::pixels::Color::RED,
        4 | 11 => sdl2::pixels::Color::GREEN,
        5 | 12 => sdl2::pixels::Color::BLUE,
        6 | 13 => sdl2::pixels::Color::MAGENTA,
        7 | 14 => sdl2::pixels::Color::YELLOW,
        _ => sdl2::pixels::Color::CYAN,
    }
}

fn read_screen_state(cpu: &CPU, frame: &mut [u8; 32 * 3 * 32]) -> bool {
    let mut frame_idx = 0;
    let mut update = false;
    for i in 0x0200..0x600 {
        let color_idx = cpu.mem_read(i as u16);
        let (b1, b2, b3) = color(color_idx).rgb();
        if frame[frame_idx] != b1 || frame[frame_idx + 1] != b2 || frame[frame_idx + 2] != b3 {
            frame[frame_idx] = b1;
            frame[frame_idx + 1] = b2;
            frame[frame_idx + 2] = b3;
            update = true;
        }
        frame_idx += 3;
    }
    update
}
