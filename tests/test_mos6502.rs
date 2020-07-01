extern crate bc64;

use bc64::{cpu::CPU, interconnect::Interconnect};
use std::fs::File;
use std::io::Read;

struct DummyBus {
    ram: Box<[u8]>,
}

impl DummyBus {
    fn new() -> Self {
        Self {
            ram: vec![0u8; 0x10000].into_boxed_slice(),
        }
    }
}

impl Interconnect for DummyBus {
    fn readb(&self, addr: u16) -> u8 {
        self.ram[addr as usize]
    }
    fn writeb(&mut self, addr: u16, data: u8) {
        self.ram[addr as usize] = data;
    }
}

#[inline(always)]
fn read_file(mem: &mut [u8], path: &str) -> std::io::Result<()> {
    let mut file = File::open(path)?;
    file.read(mem)?;
    Ok(())
}

#[test]
fn functional_test() {
    let bus = DummyBus::new();
    let mut cpu = CPU::new(0x400, bus);

    match read_file(&mut cpu.sys.ram, "tests/resources/6502_functional_test.bin") {
        Ok(()) => (),
        Err(e) => panic!("{:?}", e.to_string()),
    }

    loop {
        match cpu.step() {
            Ok(()) => (),
            Err(e) => {
                if *cpu.get_pc() == 0x3464 {
                    assert_eq!(*cpu.get_pc(), 0x3464);
                } else {
                    panic!("{:?}", e.to_string());
                }
            }
        }
    }
}
