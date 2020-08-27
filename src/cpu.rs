use crate::interconnect::Interconnect;
use crate::opcodes::INSTRUCTIONS;
use bitfield::bitfield;
use std::{default::Default, error::Error, fmt};

/// NMI vector location
pub const NMI_VECTOR: u16 = 0xFFFA;
/// Reset vector location
pub const RES_VECTOR: u16 = 0xFFFC;
/// IRQ vector location
pub const IRQ_VECTOR: u16 = 0xFFFE;

#[derive(Debug, PartialEq)]
pub enum EmulatorError {
    // I might have to remove this error in the future.
    // I have seen NES roms which have infinite loops,
    // and are interrupt driven.
    InfiniteLoop(u16),
    InvalidOpcode(u16, u8),
}

impl fmt::Display for EmulatorError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            EmulatorError::InfiniteLoop(pc) => write!(f, "Infinite loop at PC: {:#06X}!", pc),
            EmulatorError::InvalidOpcode(pc, op) => {
                write!(f, "Invalid opcode! PC: {:#06X}, OP: {:#04X}", pc, op)
            }
        }
    }
}

impl Error for EmulatorError {}

pub enum InterruptStatus {
    IRQ,
    NMI,
}

#[derive(Debug, Copy, Clone, PartialEq)]
pub(super) enum AddressingModes {
    Absolute,
    AbsoluteX,
    AbsoluteY,
    Accumulator,
    Immediate,
    Implied,
    IndexedIndirect,
    Indirect,
    IndirectIndexed,
    Relative,
    ZeroPage,
    ZeroPageX,
    ZeroPageY,
}

#[derive(Debug, Copy, Clone, PartialEq)]
pub(super) struct Instruction {
    name: &'static str,
    mode: AddressingModes,
    cycles: u32,
    length: u16,
}

impl Instruction {
    pub(super) const fn new(
        name: &'static str,
        mode: AddressingModes,
        cycles: u32,
        length: u16,
    ) -> Self {
        Self {
            name,
            mode,
            cycles,
            length,
        }
    }
}

impl Default for Instruction {
    fn default() -> Self {
        Instruction::new("", AddressingModes::Implied, 0, 0)
    }
}

bitfield! {
    struct StatusRegister(u8);
    impl Debug;
    get_c, set_c: 0;
    get_z, set_z: 1;
    get_i, set_i: 2;
    get_d, set_d: 3;
    get_b, set_b: 4;
    get_u, set_u: 5;
    get_v, set_v: 6;
    get_n, set_n: 7;
}

pub struct CPU<I: Interconnect> {
    // Registers
    a: u8,
    x: u8,
    y: u8,
    sp: u8,
    pc: u16,
    sr: StatusRegister,

    pub sys: I,
    pub cycles: u32,
    pub intr_status: Option<InterruptStatus>,

    // Helpers
    instr: Instruction,
    opcode: u8,
    data: u8,
    address: u16,
}

impl<I: Interconnect> Interconnect for CPU<I> {
    fn readb(&self, addr: u16) -> u8 {
        self.sys.readb(addr)
    }
    fn writeb(&mut self, addr: u16, data: u8) {
        self.sys.writeb(addr, data);
    }
}

impl<I: Interconnect> CPU<I> {
    pub fn new(pc: u16, sys: I) -> Self {
        Self {
            a: 0,
            x: 0,
            y: 0,
            sp: 0xFD,
            pc,
            sr: StatusRegister(0x34),
            sys,
            cycles: 0,
            intr_status: None,
            instr: Default::default(),
            opcode: 0,
            data: 0,
            address: 0,
        }
    }

    pub fn reset(&mut self) {
        self.a = 0;
        self.x = 0;
        self.y = 0;
        self.sp = 0xFD;
        self.pc = self.readw(RES_VECTOR);
        self.sr.0 = 0x34;
        self.cycles = 7;
        self.intr_status = None;
    }

    pub fn get_pc(&self) -> u16 {
        self.pc
    }

    pub fn dump_state(&self) -> String {
        format!(
            "A:{:02X} X:{:02X} Y:{:02X} P:{:02X} SP:{:02X} Cycles:{}",
            self.a, self.x, self.y, self.sr.0, self.sp, self.cycles
        )
    }

    pub fn disassembler(&self) -> String {
        type A = AddressingModes;
        let argb = self.readb(self.pc + 1);
        let argw = self.readw(self.pc + 1);
        if self.instr.mode == A::Implied {
            self.instr.name.to_string()
        } else {
            format!(
                "{} {}",
                self.instr.name,
                match self.instr.mode {
                    A::Absolute => format!("${:X}", argw),
                    A::AbsoluteX => format!("${:X},X", argw),
                    A::AbsoluteY => format!("${:X},Y", argw),
                    A::Accumulator => "A".to_string(),
                    A::Immediate => format!("$#{:02X}", argb),
                    A::IndexedIndirect => format!("(${:02X},X)", argb),
                    A::Indirect => format!("(${:X})", argw),
                    A::IndirectIndexed => format!("(${:02X}),Y", argb),
                    A::Relative => format!("$#{:02X}", argb),
                    A::ZeroPage => format!("$#{:02X}", argb),
                    A::ZeroPageX => format!("$#{:02X},X", argb),
                    A::ZeroPageY => format!("$#{:02X},Y", argb),
                    _ => unreachable!(),
                }
            )
        }
    }

    fn buggy_read16(&self, addr: u16) -> u16 {
        let msb = addr & 0xFF00;
        let lsb: u16 = if addr & 0xFF != 0xFF {
            (addr & 0xFF) + 1
        } else {
            0x00
        };
        let next_addr = msb | lsb;

        let lo: u8 = self.readb(addr);
        let hi: u8 = self.readb(next_addr);
        (hi as u16) << 8 | (lo as u16)
    }

    fn pop(&mut self) -> u8 {
        let ret = self.readb(0x100 | (self.sp.wrapping_add(1)) as u16);
        self.sp = self.sp.wrapping_add(1);
        ret
    }

    fn pop16(&mut self) -> u16 {
        let ret = self.readw(0x100 | (self.sp.wrapping_add(1)) as u16);
        self.sp = self.sp.wrapping_add(2);
        ret
    }

    #[inline(always)]
    fn push(&mut self, val: u8) {
        self.writeb(self.sp as u16 | 0x100, val);
        self.sp = self.sp.wrapping_sub(1);
    }

    fn push16(&mut self, val: u16) {
        self.writeb(self.sp as u16 | 0x100, (val >> 8) as u8);
        self.writeb((self.sp.wrapping_sub(1) as u16) | 0x100, (val & 0xFF) as u8);
        self.sp = self.sp.wrapping_sub(2);
    }

    #[inline(always)]
    fn pop_sr(&mut self) {
        self.sr.0 = self.pop() | 0x30;
    }

    #[inline(always)]
    fn push_sr(&mut self) {
        let stack_sr = self.sr.0 | 0x30;
        self.push(stack_sr);
    }

    fn extra_cycle(&mut self) {
        type A = AddressingModes;
        match self.instr.mode {
            A::IndirectIndexed => {
                if self.opcode != 0x91 {
                    self.cycles += 1;
                }
            }
            A::AbsoluteY => {
                if self.opcode != 0x99 {
                    self.cycles += 1;
                }
            }
            A::AbsoluteX => {
                if (self.opcode & 0x0F) != 0x0E && self.opcode != 0x9D {
                    self.cycles += 1;
                }
            }
            _ => (),
        }
    }

    // Addressing Mode data
    fn get_abs_data(&mut self, val: u8) {
        let addr = val as u16 + self.readw(self.pc + 1);
        if self.is_different_page(self.readw(self.pc + 1), addr) {
            self.extra_cycle();
        }
        self.address = addr;
        self.data = self.readb(addr);
    }

    fn get_zp_data(&mut self, val: u8) {
        let addr = val.wrapping_add(self.readb(self.pc + 1));
        self.address = addr as u16;
        self.data = self.readb(addr as u16);
    }

    fn get_ind_data(&mut self, val: u8, val2: u8) {
        let ptr = val.wrapping_add(self.readb(self.pc + 1));
        let addr = val2 as u16 + self.buggy_read16(ptr as u16);
        if self.is_different_page(self.buggy_read16(ptr as u16), addr) {
            self.extra_cycle();
        }
        self.address = addr as u16;
        self.data = self.readb(addr as u16);
    }

    fn set_data(&mut self) {
        type A = AddressingModes;
        match self.instr.mode {
            A::Absolute => self.get_abs_data(0),
            A::AbsoluteX => self.get_abs_data(self.x),
            A::AbsoluteY => self.get_abs_data(self.y),
            A::Accumulator => self.data = self.a,
            A::Immediate => self.data = self.readb(self.pc + 1),
            A::Implied => (),
            A::IndexedIndirect => self.get_ind_data(self.x, 0),
            A::Indirect => self.address = self.buggy_read16(self.readw(self.pc + 1)),
            A::IndirectIndexed => self.get_ind_data(0, self.y),
            A::Relative => (),
            A::ZeroPage => self.get_zp_data(0),
            A::ZeroPageX => self.get_zp_data(self.x),
            A::ZeroPageY => self.get_zp_data(self.y),
        }
    }

    fn interrupt(&mut self, vector: u16) {
        self.cycles += 7;
        self.push16(self.pc);
        if self.opcode == 0x00 {
            self.push_sr();
        } else {
            self.push(self.sr.0);
        }
        self.pc = self.readw(vector);
        self.sr.set_i(true);
    }

    fn write_data(&mut self) {
        match self.instr.mode {
            AddressingModes::Accumulator => self.a = self.data,
            _ => self.writeb(self.address, self.data),
        }
    }

    #[inline(always)]
    fn is_different_page(&self, orig: u16, new: u16) -> bool {
        (orig >> 8) & 0xFF != (new >> 8) & 0xFF
    }

    #[inline(always)]
    fn set_zn(&mut self, data: u8) {
        self.sr.set_z(data == 0x00);
        self.sr.set_n((data & 0x80) == 0x80);
    }

    fn branch(&mut self, cond: bool) -> Result<(), EmulatorError> {
        if cond {
            self.cycles += 1;
            let offset = self.readb(self.pc - 1) as i8;
            let new_pc = self.pc.wrapping_add(offset as u16);
            if self.is_different_page(self.pc, new_pc) {
                self.cycles += 1;
            }
            if (self.pc - self.instr.length) == new_pc {
                return Err(EmulatorError::InfiniteLoop(new_pc));
            }
            self.pc = new_pc;
        }
        Ok(())
    }

    fn adc(&mut self) {
        let a = self.a as u16;
        let d = self.data as u16;
        let c = self.sr.get_c() as u16;
        let result = if self.sr.get_d() {
            let mut res = (a & 0xF).wrapping_add(d & 0xF).wrapping_add(c);
            if res > 0x9 {
                res = res.wrapping_add(0x6);
            }

            res = res.wrapping_add(a & 0xF0).wrapping_add(d & 0xF0);

            if (res & 0x1F0) > 0x90 {
                res = res.wrapping_add(0x60);
            }

            self.sr.set_c((res & 0xFF0) > 0xF0);
            self.sr.set_z((a).wrapping_add(d).wrapping_add(c) == 0);
            self.sr.set_n(res & 0x80 == 0x80);
            res
        } else {
            let res = (a).wrapping_add(d).wrapping_add(c);
            self.sr.set_c(res > 0xFF);
            self.set_zn(res as u8);
            res
        };

        self.sr
            .set_v((!(self.a ^ self.data) & (self.a ^ result as u8) & 0x80) == 0x80);
        self.a = result as u8;
    }

    fn sbc(&mut self) {
        let a = self.a as u16;
        let d = self.data as u16;
        let c = !self.sr.get_c() as u16;
        let result = if self.sr.get_d() {
            let mut res = (a & 0xF).wrapping_sub(d & 0xF).wrapping_sub(c);
            if (res & 0x10) != 0 {
                res = ((res.wrapping_sub(0x6)) & 0xF)
                    | ((a & 0xF0).wrapping_sub(d & 0xF0).wrapping_sub(0x10));
            } else {
                res = (res & 0xF) | (a & 0xF0).wrapping_sub(d & 0xF0);
            }

            if (res & 0x100) != 0 {
                res = res.wrapping_sub(0x60);
            }
            res
        } else {
            a.wrapping_sub(d).wrapping_sub(c)
        };

        self.sr.set_c(result < 0x100);
        self.set_zn(result as u8);
        self.sr
            .set_v(((a ^ self.data as u16) & 0x80) != 0 && ((a ^ result) & 0x80) != 0);
        self.a = result as u8;
    }

    /// Step through one CPU instruction.
    ///
    /// This method returns a Result that does nothing on success, but returns
    /// an EmulatorError on failure. See the documentation for EmulatorError for more info.
    pub fn step(&mut self) -> Result<(), EmulatorError> {
        match self.intr_status {
            None => (),
            Some(InterruptStatus::IRQ) => self.interrupt(IRQ_VECTOR),
            Some(InterruptStatus::NMI) => self.interrupt(NMI_VECTOR),
        }

        self.opcode = self.readb(self.pc);
        self.instr = INSTRUCTIONS[self.opcode as usize]
            .ok_or(EmulatorError::InvalidOpcode(self.pc, self.opcode))?;
        self.set_data();
        self.pc += self.instr.length;
        self.cycles += self.instr.cycles;
        match self.opcode {
            // BRK
            0x00 => {
                self.pc += 1;
                self.interrupt(IRQ_VECTOR);
            }
            // ORA
            0x01 | 0x05 | 0x09 | 0x0D | 0x11 | 0x15 | 0x19 | 0x1D => {
                self.a |= self.data;
                self.set_zn(self.a);
            }
            // ASL
            0x06 | 0x0A | 0x0E | 0x16 | 0x1E => {
                self.sr.set_c((self.data >> 7) == 0x1);
                self.data <<= 1;
                self.set_zn(self.data);
                self.write_data();
            }
            // PHP
            0x08 => self.push_sr(),
            // BPL
            0x10 => self.branch(!self.sr.get_n())?,
            // CLC
            0x18 => self.sr.set_c(false),
            // JSR
            0x20 => {
                self.push16(self.pc - 1);
                self.pc = self.address;
            }
            // AND
            0x21 | 0x25 | 0x29 | 0x2D | 0x31 | 0x35 | 0x39 | 0x3D => {
                self.a &= self.data;
                self.set_zn(self.a);
            }
            // BIT
            0x24 | 0x2C => {
                let result = self.a & self.data;
                self.sr.set_z(result == 0);
                self.sr.set_n((self.data >> 7) == 0x1);
                self.sr.set_v(((self.data & 0x40) >> 6) == 0x1);
            }
            // ROL
            0x26 | 0x2A | 0x2E | 0x36 | 0x3E => {
                let result = (self.data as u16) << 1 | self.sr.get_c() as u16;
                self.sr.set_c(result > 0xFF);
                self.set_zn(result as u8);
                self.data = result as u8;
                self.write_data();
            }
            // PLP
            0x28 => self.pop_sr(),
            // BMI
            0x30 => self.branch(self.sr.get_n())?,
            // SEC
            0x38 => self.sr.set_c(true),
            // RTI
            0x40 => {
                self.pop_sr();
                self.pc = self.pop16();
            }
            // EOR
            0x41 | 0x45 | 0x49 | 0x4D | 0x51 | 0x55 | 0x59 | 0x5D => {
                self.a ^= self.data;
                self.set_zn(self.a);
            }
            // LSR
            0x46 | 0x4A | 0x4E | 0x56 | 0x5E => {
                self.sr.set_c((self.data & 0x01) == 0x01);
                self.data >>= 1;
                self.set_zn(self.data);
                self.write_data();
            }
            // PHA
            0x48 => self.push(self.a),
            // JMP
            0x4C | 0x6C => {
                if (self.pc - self.instr.length) == self.address {
                    return Err(EmulatorError::InfiniteLoop(self.address));
                }
                self.pc = self.address;
            }

            // BVC
            0x50 => self.branch(!self.sr.get_v())?,
            // CLI
            0x58 => self.sr.set_i(false),
            // RTS
            0x60 => self.pc = self.pop16() + 1,
            // ADC
            0x61 | 0x65 | 0x69 | 0x6D | 0x71 | 0x75 | 0x79 | 0x7D => self.adc(),
            // ROR
            0x66 | 0x6A | 0x6E | 0x76 | 0x7E => {
                let result = (self.sr.get_c() as u16) << 7 | (self.data as u16) >> 1;
                self.sr.set_c((self.data & 0x01) == 0x01);
                self.set_zn(result as u8);
                self.data = result as u8;
                self.write_data();
            }
            // PLA
            0x68 => {
                self.a = self.pop();
                self.set_zn(self.a);
            }
            // BVS
            0x70 => self.branch(self.sr.get_v())?,
            // SEI
            0x78 => self.sr.set_i(true),
            // STA
            0x81 | 0x85 | 0x89 | 0x8D | 0x91 | 0x95 | 0x99 | 0x9D => {
                self.writeb(self.address, self.a)
            }

            // STY
            0x84 | 0x8C | 0x94 => self.writeb(self.address, self.y),
            // STX
            0x86 | 0x8E | 0x96 => self.writeb(self.address, self.x),
            // DEY
            0x88 => {
                self.y = self.y.wrapping_sub(1);
                self.set_zn(self.y);
            }
            // TXA
            0x8A => {
                self.a = self.x;
                self.set_zn(self.a);
            }
            // BCC
            0x90 => self.branch(!self.sr.get_c())?,
            // TYA
            0x98 => {
                self.a = self.y;
                self.set_zn(self.a);
            }
            // TXS
            0x9A => self.sp = self.x,
            // LDY
            0xA0 | 0xA4 | 0xAC | 0xB4 | 0xBC => {
                self.y = self.data;
                self.set_zn(self.y);
            }
            // LDA
            0xA1 | 0xA5 | 0xA9 | 0xAD | 0xB1 | 0xB5 | 0xB9 | 0xBD => {
                self.a = self.data;
                self.set_zn(self.a);
            }
            // LDX
            0xA2 | 0xA6 | 0xAE | 0xB6 | 0xBE => {
                self.x = self.data;
                self.set_zn(self.x);
            }
            // TAY
            0xA8 => {
                self.y = self.a;
                self.set_zn(self.y);
            }
            // TAX
            0xAA => {
                self.x = self.a;
                self.set_zn(self.x);
            }
            // BCS
            0xB0 => self.branch(self.sr.get_c())?,
            // CLV
            0xB8 => self.sr.set_v(false),
            // TSX
            0xBA => {
                self.x = self.sp;
                self.set_zn(self.x);
            }
            // CPY
            0xC0 | 0xC4 | 0xCC => {
                self.sr.set_c(self.y >= self.data);
                self.set_zn(self.y.wrapping_sub(self.data));
            }
            // CMP
            0xC1 | 0xC5 | 0xC9 | 0xCD | 0xD1 | 0xD5 | 0xD9 | 0xDD => {
                self.sr.set_c(self.a >= self.data);
                self.set_zn(self.a.wrapping_sub(self.data));
            }
            // DEC
            0xC6 | 0xCE | 0xD6 | 0xDE => {
                self.data = self.data.wrapping_sub(1);
                self.set_zn(self.data);
                self.writeb(self.address, self.data);
            }
            // INY
            0xC8 => {
                self.y = self.y.wrapping_add(1);
                self.set_zn(self.y);
            }
            // DEX
            0xCA => {
                self.x = self.x.wrapping_sub(1);
                self.set_zn(self.x);
            }
            // BNE
            0xD0 => self.branch(!self.sr.get_z())?,
            // CLD
            0xD8 => self.sr.set_d(false),
            // CPX
            0xE0 | 0xE4 | 0xEC => {
                self.sr.set_c(self.x >= self.data);
                self.set_zn(self.x.wrapping_sub(self.data));
            }
            // SBC
            0xE1 | 0xE5 | 0xE9 | 0xED | 0xF1 | 0xF5 | 0xF9 | 0xFD => self.sbc(),
            // INC
            0xE6 | 0xEE | 0xF6 | 0xFE => {
                self.data = self.data.wrapping_add(1);
                self.set_zn(self.data);
                self.writeb(self.address, self.data);
            }
            // INX
            0xE8 => {
                self.x = self.x.wrapping_add(1);
                self.set_zn(self.x);
            }
            // NOP
            0xEA => (),
            // BEQ
            0xF0 => self.branch(self.sr.get_z())?,
            // SED
            0xF8 => self.sr.set_d(true),

            _ => return Err(EmulatorError::InvalidOpcode(self.pc, self.opcode)),
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

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

    #[test]
    fn test_sr() {
        let mut sr = StatusRegister(0x34);
        sr.set_n(true);
        sr.set_c(true);
        assert_eq!(sr.0, 0xB5);
    }

    #[test]
    fn test_jmp_bug() {
        let bus = DummyBus::new();
        let mut cpu = CPU::new(0x200, bus);
        cpu.sys.ram[0xFF] = 0x00;
        cpu.sys.ram[0x00] = 0x02;
        assert_eq!(cpu.buggy_read16(0xFF), 0x200);
    }

    #[test]
    fn test_interrupts() {
        let bus = DummyBus::new();
        let mut cpu = CPU::new(0x200, bus);
        cpu.writew(IRQ_VECTOR, 0x200);
        cpu.writew(NMI_VECTOR, 0x200);
        cpu.writew(0x200, 0x70A9);
        cpu.intr_status = Some(InterruptStatus::IRQ);
        cpu.step().unwrap();
        assert_eq!(cpu.a, 0x70);

        cpu.writew(0x200, 0x70A0);
        cpu.intr_status = Some(InterruptStatus::NMI);
        cpu.step().unwrap();
        assert_eq!(cpu.y, 0x70);
    }

    #[test]
    fn test_zn() {
        let bus = DummyBus::new();
        let mut cpu = CPU::new(0x200, bus);
        cpu.set_zn(0x80);
        assert_eq!(cpu.sr.0, 0xB4);
        cpu.set_zn(0x00);
        assert_eq!(cpu.sr.0, 0x36);
    }

    #[test]
    fn test_branch() {
        let bus = DummyBus::new();
        let mut cpu = CPU::new(0x200, bus);
        cpu.writeb(0x1FF, 0xA4);
        cpu.branch(true).unwrap();
        assert_eq!(cpu.pc, 0x1A4);

        cpu.writeb(0x1A3, 0x10);
        cpu.branch(true).unwrap();
        assert_eq!(cpu.pc, 0x1B4);
    }

    #[test]
    fn test_different_page() {
        let bus = DummyBus::new();
        let cpu = CPU::new(0x200, bus);
        assert_eq!(cpu.is_different_page(0xAA00, 0xAB00), true);
    }

    #[test]
    fn test_stack() {
        let bus = DummyBus::new();
        let mut cpu = CPU::new(0x200, bus);
        cpu.push(0xAA);
        assert_eq!(cpu.sp, 0xFC);
        assert_eq!(cpu.pop(), 0xAA);

        cpu.push16(0xAA00);
        assert_eq!(cpu.sp, 0xFB);
        assert_eq!(cpu.pop16(), 0xAA00);

        cpu.sr.set_u(false);
        cpu.push_sr();
        cpu.pop_sr();
        assert_eq!(cpu.sr.0, 0x34);
    }
}
