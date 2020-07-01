pub trait Interconnect: Sized {
    fn readb(&self, addr: u16) -> u8;
    fn writeb(&mut self, addr: u16, data: u8);
    fn readw(&self, addr: u16) -> u16 {
        (self.readb(addr + 1) as u16) << 8 | self.readb(addr) as u16
    }
    fn writew(&mut self, addr: u16, data: u16) {
        self.writeb(addr, (data & 0xFF) as u8);
        self.writeb(addr + 1, (data >> 8) as u8);
    }
}
