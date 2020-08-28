use bitfield::bitfield;

bitfield! {
    struct ControlRegister1(u8);
    impl Debug;
    get_ysc, set_ysc: 2, 0;
    get_res, set_res: 3;
    get_den, set_den: 4;
    get_bmm, set_bmm: 5;
    get_ecm, set_ecm: 6;
    get_rs8, set_rs8: 7;
}

bitfield! {
    struct ControlRegister2(u8);
    impl Debug;
    get_xsc, set_xsc: 2, 0;
    get_cse, set_cse: 3;
    get_mcm, set_mcm: 4;
    get_res, set_res: 5;
    get_cr2_last2, _: 7, 6;
}

pub struct Vic {
    x_coor: [u8; 8],
    y_coor: [u8; 8],
    msb_x: u8,
    cr1: ControlRegister1,
    cr2: ControlRegister2,
}

impl Vic {}
