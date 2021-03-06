use crate::cpu::AddressingModes;
use crate::cpu::Instruction;

const NUM_OF_INSTR: usize = 256;
type A = AddressingModes;

pub(super) const INSTRUCTIONS: [Option<Instruction>; NUM_OF_INSTR] = [
    Some(Instruction::new("BRK", A::Implied, 7, 1)),
    Some(Instruction::new("ORA", A::IndexedIndirect, 6, 2)),
    None,
    None,
    None,
    Some(Instruction::new("ORA", A::ZeroPage, 3, 2)),
    Some(Instruction::new("ASL", A::ZeroPage, 5, 2)),
    None,
    Some(Instruction::new("PHP", A::Implied, 3, 1)),
    Some(Instruction::new("ORA", A::Immediate, 2, 2)),
    Some(Instruction::new("ASL", A::Accumulator, 2, 1)),
    None,
    None,
    Some(Instruction::new("ORA", A::Absolute, 4, 3)),
    Some(Instruction::new("ASL", A::Absolute, 6, 3)),
    None,
    Some(Instruction::new("BPL", A::Relative, 2, 2)),
    Some(Instruction::new("ORA", A::IndirectIndexed, 5, 2)),
    None,
    None,
    None,
    Some(Instruction::new("ORA", A::ZeroPageX, 4, 2)),
    Some(Instruction::new("ASL", A::ZeroPageX, 6, 2)),
    None,
    Some(Instruction::new("CLC", A::Implied, 2, 1)),
    Some(Instruction::new("ORA", A::AbsoluteY, 4, 3)),
    None,
    None,
    None,
    Some(Instruction::new("ORA", A::AbsoluteX, 4, 3)),
    Some(Instruction::new("ASL", A::AbsoluteX, 7, 3)),
    None,
    Some(Instruction::new("JSR", A::Absolute, 6, 3)),
    Some(Instruction::new("AND", A::IndexedIndirect, 6, 2)),
    None,
    None,
    Some(Instruction::new("BIT", A::ZeroPage, 3, 2)),
    Some(Instruction::new("AND", A::ZeroPage, 3, 2)),
    Some(Instruction::new("ROL", A::ZeroPage, 5, 2)),
    None,
    Some(Instruction::new("PLP", A::Implied, 4, 1)),
    Some(Instruction::new("AND", A::Immediate, 2, 2)),
    Some(Instruction::new("ROL", A::Accumulator, 2, 1)),
    None,
    Some(Instruction::new("BIT", A::Absolute, 4, 3)),
    Some(Instruction::new("AND", A::Absolute, 4, 3)),
    Some(Instruction::new("ROL", A::Absolute, 6, 3)),
    None,
    Some(Instruction::new("BMI", A::Relative, 2, 2)),
    Some(Instruction::new("AND", A::IndirectIndexed, 5, 2)),
    None,
    None,
    None,
    Some(Instruction::new("AND", A::ZeroPageX, 4, 2)),
    Some(Instruction::new("ROL", A::ZeroPageX, 6, 2)),
    None,
    Some(Instruction::new("SEC", A::Implied, 2, 1)),
    Some(Instruction::new("AND", A::AbsoluteY, 4, 3)),
    None,
    None,
    None,
    Some(Instruction::new("AND", A::AbsoluteX, 4, 3)),
    Some(Instruction::new("ROL", A::AbsoluteX, 7, 3)),
    None,
    Some(Instruction::new("RTI", A::Implied, 6, 1)),
    Some(Instruction::new("EOR", A::IndexedIndirect, 6, 2)),
    None,
    None,
    None,
    Some(Instruction::new("EOR", A::ZeroPage, 3, 2)),
    Some(Instruction::new("LSR", A::ZeroPage, 5, 2)),
    None,
    Some(Instruction::new("PHA", A::Implied, 3, 1)),
    Some(Instruction::new("EOR", A::Immediate, 2, 2)),
    Some(Instruction::new("LSR", A::Accumulator, 2, 1)),
    None,
    Some(Instruction::new("JMP", A::Absolute, 3, 3)),
    Some(Instruction::new("EOR", A::Absolute, 4, 3)),
    Some(Instruction::new("LSR", A::Absolute, 6, 3)),
    None,
    Some(Instruction::new("BVC", A::Relative, 2, 2)),
    Some(Instruction::new("EOR", A::IndirectIndexed, 5, 2)),
    None,
    None,
    None,
    Some(Instruction::new("EOR", A::ZeroPageX, 4, 2)),
    Some(Instruction::new("LSR", A::ZeroPageX, 6, 2)),
    None,
    Some(Instruction::new("CLI", A::Implied, 2, 1)),
    Some(Instruction::new("EOR", A::AbsoluteY, 4, 3)),
    None,
    None,
    None,
    Some(Instruction::new("EOR", A::AbsoluteX, 4, 3)),
    Some(Instruction::new("LSR", A::AbsoluteX, 7, 3)),
    None,
    Some(Instruction::new("RTS", A::Implied, 6, 1)),
    Some(Instruction::new("ADC", A::IndexedIndirect, 6, 2)),
    None,
    None,
    None,
    Some(Instruction::new("ADC", A::ZeroPage, 3, 2)),
    Some(Instruction::new("ROR", A::ZeroPage, 5, 2)),
    None,
    Some(Instruction::new("PLA", A::Implied, 4, 1)),
    Some(Instruction::new("ADC", A::Immediate, 2, 2)),
    Some(Instruction::new("ROR", A::Accumulator, 2, 1)),
    None,
    Some(Instruction::new("JMP", A::Indirect, 5, 3)),
    Some(Instruction::new("ADC", A::Absolute, 4, 3)),
    Some(Instruction::new("ROR", A::Absolute, 6, 3)),
    None,
    Some(Instruction::new("BVS", A::Relative, 2, 2)),
    Some(Instruction::new("ADC", A::IndirectIndexed, 5, 2)),
    None,
    None,
    None,
    Some(Instruction::new("ADC", A::ZeroPageX, 4, 2)),
    Some(Instruction::new("ROR", A::ZeroPageX, 6, 2)),
    None,
    Some(Instruction::new("SEI", A::Implied, 2, 1)),
    Some(Instruction::new("ADC", A::AbsoluteY, 4, 3)),
    None,
    None,
    None,
    Some(Instruction::new("ADC", A::AbsoluteX, 4, 3)),
    Some(Instruction::new("ROR", A::AbsoluteX, 7, 3)),
    None,
    None,
    Some(Instruction::new("STA", A::IndexedIndirect, 6, 2)),
    None,
    None,
    Some(Instruction::new("STY", A::ZeroPage, 3, 2)),
    Some(Instruction::new("STA", A::ZeroPage, 3, 2)),
    Some(Instruction::new("STX", A::ZeroPage, 3, 2)),
    None,
    Some(Instruction::new("DEY", A::Implied, 2, 1)),
    None,
    Some(Instruction::new("TXA", A::Implied, 2, 1)),
    None,
    Some(Instruction::new("STY", A::Absolute, 4, 3)),
    Some(Instruction::new("STA", A::Absolute, 4, 3)),
    Some(Instruction::new("STX", A::Absolute, 4, 3)),
    None,
    Some(Instruction::new("BCC", A::Relative, 2, 2)),
    Some(Instruction::new("STA", A::IndirectIndexed, 6, 2)),
    None,
    None,
    Some(Instruction::new("STY", A::ZeroPageX, 4, 2)),
    Some(Instruction::new("STA", A::ZeroPageX, 4, 2)),
    Some(Instruction::new("STX", A::ZeroPageY, 4, 2)),
    None,
    Some(Instruction::new("TYA", A::Implied, 2, 1)),
    Some(Instruction::new("STA", A::AbsoluteY, 5, 3)),
    Some(Instruction::new("TXS", A::Implied, 2, 1)),
    None,
    None,
    Some(Instruction::new("STA", A::AbsoluteX, 5, 3)),
    None,
    None,
    Some(Instruction::new("LDY", A::Immediate, 2, 2)),
    Some(Instruction::new("LDA", A::IndexedIndirect, 6, 2)),
    Some(Instruction::new("LDX", A::Immediate, 2, 2)),
    None,
    Some(Instruction::new("LDY", A::ZeroPage, 3, 2)),
    Some(Instruction::new("LDA", A::ZeroPage, 3, 2)),
    Some(Instruction::new("LDX", A::ZeroPage, 3, 2)),
    None,
    Some(Instruction::new("TAY", A::Implied, 2, 1)),
    Some(Instruction::new("LDA", A::Immediate, 2, 2)),
    Some(Instruction::new("TAX", A::Implied, 2, 1)),
    None,
    Some(Instruction::new("LDY", A::Absolute, 4, 3)),
    Some(Instruction::new("LDA", A::Absolute, 4, 3)),
    Some(Instruction::new("LDX", A::Absolute, 4, 3)),
    None,
    Some(Instruction::new("BCS", A::Relative, 2, 2)),
    Some(Instruction::new("LDA", A::IndirectIndexed, 5, 2)),
    None,
    None,
    Some(Instruction::new("LDY", A::ZeroPageX, 4, 2)),
    Some(Instruction::new("LDA", A::ZeroPageX, 4, 2)),
    Some(Instruction::new("LDX", A::ZeroPageY, 4, 2)),
    None,
    Some(Instruction::new("CLV", A::Implied, 2, 1)),
    Some(Instruction::new("LDA", A::AbsoluteY, 4, 3)),
    Some(Instruction::new("TSX", A::Implied, 2, 1)),
    None,
    Some(Instruction::new("LDY", A::AbsoluteX, 4, 3)),
    Some(Instruction::new("LDA", A::AbsoluteX, 4, 3)),
    Some(Instruction::new("LDX", A::AbsoluteY, 4, 3)),
    None,
    Some(Instruction::new("CPY", A::Immediate, 2, 2)),
    Some(Instruction::new("CMP", A::IndexedIndirect, 6, 2)),
    None,
    None,
    Some(Instruction::new("CPY", A::ZeroPage, 3, 2)),
    Some(Instruction::new("CMP", A::ZeroPage, 3, 2)),
    Some(Instruction::new("DEC", A::ZeroPage, 5, 2)),
    None,
    Some(Instruction::new("INY", A::Implied, 2, 1)),
    Some(Instruction::new("CMP", A::Immediate, 2, 2)),
    Some(Instruction::new("DEX", A::Implied, 2, 1)),
    None,
    Some(Instruction::new("CPY", A::Absolute, 4, 3)),
    Some(Instruction::new("CMP", A::Absolute, 4, 3)),
    Some(Instruction::new("DEC", A::Absolute, 6, 3)),
    None,
    Some(Instruction::new("BNE", A::Relative, 2, 2)),
    Some(Instruction::new("CMP", A::IndirectIndexed, 5, 2)),
    None,
    None,
    None,
    Some(Instruction::new("CMP", A::ZeroPageX, 4, 2)),
    Some(Instruction::new("DEC", A::ZeroPageX, 6, 2)),
    None,
    Some(Instruction::new("CLD", A::Implied, 2, 1)),
    Some(Instruction::new("CMP", A::AbsoluteY, 4, 3)),
    None,
    None,
    None,
    Some(Instruction::new("CMP", A::AbsoluteX, 4, 3)),
    Some(Instruction::new("DEC", A::AbsoluteX, 7, 3)),
    None,
    Some(Instruction::new("CPX", A::Immediate, 2, 2)),
    Some(Instruction::new("SBC", A::IndexedIndirect, 6, 2)),
    None,
    None,
    Some(Instruction::new("CPX", A::ZeroPage, 3, 2)),
    Some(Instruction::new("SBC", A::ZeroPage, 3, 2)),
    Some(Instruction::new("INC", A::ZeroPage, 5, 2)),
    None,
    Some(Instruction::new("INX", A::Implied, 2, 1)),
    Some(Instruction::new("SBC", A::Immediate, 2, 2)),
    Some(Instruction::new("NOP", A::Implied, 2, 1)),
    None,
    Some(Instruction::new("CPX", A::Absolute, 4, 3)),
    Some(Instruction::new("SBC", A::Absolute, 4, 3)),
    Some(Instruction::new("INC", A::Absolute, 6, 3)),
    None,
    Some(Instruction::new("BEQ", A::Relative, 2, 2)),
    Some(Instruction::new("SBC", A::IndirectIndexed, 5, 2)),
    None,
    None,
    None,
    Some(Instruction::new("SBC", A::ZeroPageX, 4, 2)),
    Some(Instruction::new("INC", A::ZeroPageX, 6, 2)),
    None,
    Some(Instruction::new("SED", A::Implied, 2, 1)),
    Some(Instruction::new("SBC", A::AbsoluteY, 4, 3)),
    None,
    None,
    None,
    Some(Instruction::new("SBC", A::AbsoluteX, 4, 3)),
    Some(Instruction::new("INC", A::AbsoluteX, 7, 3)),
    None,
];
