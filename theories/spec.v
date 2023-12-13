From stdpp Require Import ssreflect unstable.bitvector.
From theories Require Import rom.

Local Open Scope bv.

Definition bit {n} i (w : bv n) : bool := Z.testbit (bv_unsigned w) i.
Definition trunc {n} m (w : bv n) : bv m := bv_zero_extend m w.
Definition bv_eqb {n} (w1 w2 : bv n) : bool := Z.eqb (bv_unsigned w1) (bv_unsigned w2).
(* The library puts the big end first. I want the little end first. *)
Definition bv_concat n {n1 n2} (b1 : bv n1) (b2 : bv n2) : bv n := bv_concat n b2 b1.

Definition add_with_carry {n} (c_in : bool) (w1 w2 : bv n) : bv n * bool :=
    let out :=
        bv_zero_extend (n + 1) (bool_to_bv 1 c_in) +
        (bv_zero_extend (n + 1) w1 + bv_zero_extend (n + 1) w2)
    in (trunc n out, bit (Z.of_N n) out).
Definition sub_with_inverted_borrow {n} cin (w1 w2 : bv n) : bv n * bool :=
    add_with_carry cin w1 (bv_not w2).

Inductive reg := X|Y|A|SP.
Inductive flag := N|B|V|D|I|Z|C.

Definition reg_eqb (r1 r2 : reg) : bool :=
    match (r1, r2) with
    | (X,X) | (Y,Y) | (A,A) | (SP,SP) => true
    | _ => false
    end.
Theorem reg_eqP {r1 r2} : reflect (r1 = r2) (reg_eqb r1 r2).
Proof.
    case r1; case r2; by constructor.
Qed.

Definition flag_eqb (r1 r2 : flag) : bool :=
    match (r1, r2) with
    | (N,N) | (B,B) | (V,V) | (D,D) | (I,I) | (Z,Z) | (C,C) => true
    | _ => false
    end.
Theorem flag_eqP {r1 r2} : reflect (r1 = r2) (flag_eqb r1 r2).
Proof.
    case r1; case r2; by constructor.
Qed.


Record state := {
    Reg : reg -> bv 8;
    Flag : flag -> bool;
    RAM : bv 7 -> bv 8;
    PC : bv 16;
}.

Record initial (s : state) : Prop := {
    init_interrupt_disable : Flag s I;
    pc_init : PC s = bv_concat 16 (ROM 0x7fc) (ROM 0x7fd)
}.

Definition fetch (s : state) (addr : bv 16) (value : bv 8) : Prop :=
if bit 12 addr
then value = ROM (trunc 11 addr)
else if negb (bit 7 addr) || bit 9 addr
(* TIA or PIA. I don't model these, so I assume they can return any value to the processor. *)
then True
else value = RAM s (trunc 7 addr).

Definition write (addr : bv 16) (value : bv 8) (ram : bv 7 -> bv 8) : bv 7 -> bv 8 :=
if Z.testbit (bv_unsigned addr) 12
then ram
else if negb (Z.testbit (bv_unsigned addr) 7) || Z.testbit (bv_unsigned addr) 9
then ram
else fun addr' => if bv_eqb (trunc 7 addr) addr' then value else ram addr'.

Section StepSpec.

Context (s1 s2 : state).



Definition setReg (r : reg) (value : bv 8) : reg -> bv 8 := fun r' =>
    if reg_eqb r r' then value else Reg s1 r'.

Definition setNZ (value : bv 8) : flag -> bool := fun f =>
    match f with
    | N => bit 7 value
    | Z => bv_eqb value 0x00
    | _ => Flag s1 f
    end.

Definition transfer_instruction r1 r2 :=
    PC s2 = bv_add_Z (PC s1) 1 /\
    Reg s2 = setReg r2 (Reg s1 r1) /\
    Flag s2 = setNZ (Reg s1 r1) /\
    RAM s2 = RAM s1.

Definition flag_instruction (f : flag) (value : bool) : Prop :=
    PC s2 = bv_add_Z (PC s1) 1 /\
    Reg s2 = Reg s1 /\
    Flag s2 = (fun f' => if flag_eqb f f' then value else Flag s1 f') /\
    RAM s2 = RAM s1.

Definition branch_instruction (cond : state -> bool) : Prop :=
    exists dist,
        fetch s1 (bv_add_Z (PC s1) 1) dist /\
        (PC s2 =
            let pc := bv_add_Z (PC s1) 2 in
            if cond s1 then bv_add pc (bv_sign_extend 16 dist) else pc) /\
        Reg s2 = Reg s1 /\
        Flag s2 = Flag s1 /\
        RAM s2 = RAM s1.

Definition mem_addressing_mode := state -> bv 16 -> Prop.
Definition absolute : mem_addressing_mode :=
    fun s addr => exists w1 w2,
        fetch s (bv_add_Z (PC s) 1) w1 /\
        fetch s (bv_add_Z (PC s) 2) w2 /\
        addr = bv_concat 16 w1 w2.
Definition absolute_x : mem_addressing_mode :=
    fun s addr => exists w1 w2,
        fetch s (bv_add_Z (PC s) 1) w1 /\
        fetch s (bv_add_Z (PC s) 2) w2 /\
        addr = bv_add (bv_concat 16 w1 w2) (bv_zero_extend 16 (Reg s X)).
Definition absolute_y : mem_addressing_mode :=
    fun s addr => exists w1 w2,
        fetch s (bv_add_Z (PC s) 1) w1 /\
        fetch s (bv_add_Z (PC s) 2) w2 /\
        addr = bv_add (bv_concat 16 w1 w2) (bv_zero_extend 16 (Reg s Y)).
Definition zero_page : mem_addressing_mode :=
    fun s addr => exists w,
        fetch s (bv_add_Z (PC s) 1) w /\
        addr = bv_zero_extend 16 w.
Definition zero_page_x : mem_addressing_mode :=
    fun s addr => exists w,
        fetch s (bv_add_Z (PC s) 1) w /\
        addr = bv_zero_extend 16 (bv_add w (Reg s X)).
Definition zero_page_y : mem_addressing_mode :=
    fun s addr => exists w,
        fetch s (bv_add_Z (PC s) 1) w /\
        addr = bv_zero_extend 16 (bv_add w (Reg s Y)).
Definition indirect_x : mem_addressing_mode :=
    fun s addr => exists w w1 w2,
        fetch s (bv_add_Z (PC s) 1) w /\
        let indir := bv_add w (Reg s X) in
        fetch s (bv_zero_extend 16 indir) w1 /\
        fetch s (bv_zero_extend 16 (bv_add_Z indir 1)) w2 /\
        addr = bv_concat 16 w1 w2.
Definition indirect_y : mem_addressing_mode :=
    fun s addr => exists indir w1 w2,
        fetch s (bv_add_Z (PC s) 1) indir /\
        fetch s (bv_zero_extend 16 indir) w1 /\
        fetch s (bv_zero_extend 16 (bv_add_Z indir 1)) w2 /\
        addr = bv_add (bv_concat 16 w1 w2) (bv_zero_extend 16 (Reg s Y)).
(* This isn't traditionally treated as a *memory* addressing mode.
But in a sense, it is. It accesses the memory immediately following the opcode! *)
Definition immediate : mem_addressing_mode :=
    fun s addr => addr = bv_add_Z (PC s) 1.

Definition store_instruction register mode mode_len :=
    exists addr,
        mode s1 addr /\
        PC s2 = bv_add_Z (PC s1) mode_len /\
        Reg s2 = Reg s1 /\
        Flag s2 = Flag s1 /\
        RAM s2 = write addr (Reg s1 register) (RAM s1).

Definition load_instruction register mode mode_len :=
    exists addr w,
        mode s1 addr /\
        fetch s1 addr w /\
        PC s2 = bv_add_Z (PC s1) mode_len /\
        Reg s2 = setReg register w /\
        Flag s2 = setNZ w /\
        RAM s2 = RAM s1.

Definition logic_instruction operation mode mode_len :=
    exists addr w,
        mode s1 addr /\
        fetch s1 addr w /\
        let w := operation (Reg s1 A) w in
        PC s2 = bv_add_Z (PC s1) mode_len /\
        Reg s2 = setReg A w /\
        Flag s2 = setNZ w /\
        RAM s2 = RAM s1.

Definition BIT_mode mode mode_len :=
    exists addr w,
        mode s1 addr /\
        fetch s1 addr w /\
        let w := bv_and (Reg s1 A) w in
        PC s2 = bv_add_Z (PC s1) mode_len /\
        Reg s2 = Reg s1 /\
        Flag s2 = (fun f =>
            match f with
            | Z => bv_eqb w 0x00
            | N => bit 7 w
            | V => bit 6 w
            | _ => Flag s1 f
            end) /\
        RAM s2 = RAM s1.

Definition INC_reg r :=
    let w := bv_add_Z (Reg s1 r) 1 in
    PC s2 = bv_add_Z (PC s1) 1 /\
    Reg s2 = setReg r w /\
    Flag s2 = setNZ w /\
    RAM s2 = RAM s1.
Definition INC_mode mode mode_len :=
    exists addr w,
        mode s1 addr /\
        fetch s1 addr w /\
        let w := bv_add_Z w 1 in
        PC s2 = bv_add_Z (PC s1) mode_len /\
        Reg s2 = Reg s1 /\
        Flag s2 = setNZ w /\
        RAM s2 = write addr w (RAM s1).
Definition DEC_reg r :=
    let w := bv_sub_Z (Reg s1 r) 1 in
    PC s2 = bv_add_Z (PC s1) 1 /\
    Reg s2 = setReg r w /\
    Flag s2 = setNZ w /\
    RAM s2 = RAM s1.
Definition DEC_mode mode mode_len :=
    exists addr w,
        mode s1 addr /\
        fetch s1 addr w /\
        let w := bv_sub_Z w 1 in
        PC s2 = bv_add_Z (PC s1) mode_len /\
        Reg s2 = Reg s1 /\
        Flag s2 = setNZ w /\
        RAM s2 = write addr w (RAM s1).


Definition shift_instruction_A (shift_spec : bv 8 -> bool -> bv 8 -> bool -> Prop) :=
    exists cout (w : bv 8),
        shift_spec
            (Reg s1 A) (Flag s1 C)
            w cout /\
        PC s2 = bv_add_Z (PC s1) 1 /\
        Reg s2 = setReg A w /\
        Flag s2 = (fun f =>
            match f with
            | N => bit 7 w
            | Z => bv_eqb w 0x00
            | C => cout
            | _ => Flag s1 f
            end) /\
        RAM s2 = RAM s1.
Definition shift_instruction_mode
    (shift_spec : bv 8 -> bool -> bv 8 -> bool -> Prop) mode mode_len :=
    exists addr w_in cout (w_out : bv 8),
        mode s1 addr /\
        fetch s1 addr w_in /\
        shift_spec
            w_in (Flag s1 C)
            w_out cout /\
        PC s2 = bv_add_Z (PC s1) mode_len /\
        Reg s2 = Reg s1 /\
        Flag s2 = (fun f =>
            match f with
            | N => bit 7 w_out
            | Z => bv_eqb w_out 0x00
            | C => cout
            | _ => Flag s1 f
            end) /\
        RAM s2 = write addr w_out (RAM s1).
Definition ROL_spec (w1 : bv 8) c1 (w2 : bv 8) c2 :=
    bv_concat 9 w2 (bool_to_bv 1 c2) =
    bv_concat 9 (bool_to_bv 1 c1) w1.
Definition ROR_spec (w1 : bv 8) c1 (w2 : bv 8) c2 :=
    bv_concat 9 (bool_to_bv 1 c2) w2 =
    bv_concat 9 w1 (bool_to_bv 1 c1).
Definition ASL_spec (w1 : bv 8) (_ : bool) (w2 : bv 8) c2 :=
    bv_concat 9 w2 (bool_to_bv 1 c2) =
    bv_concat 9 (bool_to_bv 1 false) w1.
Definition LSR_spec (w1 : bv 8) (_ : bool) (w2 : bv 8) c2 :=
    bv_concat 9 (bool_to_bv 1 c2) w2 =
    bv_concat 9 w1 (bool_to_bv 1 false).


Definition CMP_mode register mode mode_len :=
    exists addr w,
        mode s1 addr /\
        fetch s1 addr w /\
        let: (w, c) := sub_with_inverted_borrow true (Reg s1 register) w in
        PC s2 = bv_add_Z (PC s1) mode_len /\
        Reg s2 = Reg s1 /\
        Flag s2 = (fun f =>
            match f with
            | N => bit 7 w
            | Z => bv_eqb w 0x00
            | C => c
            | _ => Flag s1 f
            end) /\
        RAM s2 = RAM s1.

Definition is_bcd (w : bv 8) (n : BinNums.Z) : Prop :=
    exists w1 w2 : bv 4,
        (w = bv_concat 8 w1 w2 /\
        bv_unsigned w1 <? 10 /\
        bv_unsigned w2 <? 10 /\
        n = bv_unsigned w1 * 10 + bv_unsigned w2)%Z.

Definition ADC_decimal_relation (c_in : bool) (w1 w2 w : bv 8) (c_out : bool) : Prop :=
    forall n1 n2, is_bcd w1 n1 -> is_bcd w2 n2 ->
    exists n, is_bcd w n /\
    (n + (if c_out then 100 else 0) = (if c_in then 1 else 0) + n1 + n2)%Z.

Definition ADC_mode mode mode_len :=
    if Flag s1 D
    then exists addr w_in w_out c_out v,
        mode s1 addr /\
        fetch s1 addr w_in /\
        ADC_decimal_relation (Flag s1 C) (Reg s1 A) w_in w_out c_out /\
        PC s2 = bv_add_Z (PC s1) mode_len /\
        Reg s2 = setReg A w_out /\
        Flag s2 = (fun f =>
            match f with
            | N => bit 7 w_out
            | Z => bv_eqb w_out 0x00
            | C => c_out
            | V => v
            | _ => Flag s1 f
            end) /\
        RAM s2 = RAM s1
    else exists addr w_in,
        mode s1 addr /\
        fetch s1 addr w_in /\
        let: (w_out, c) := add_with_carry (Flag s1 C) (Reg s1 A) w_in in
        PC s2 = bv_add_Z (PC s1) mode_len /\
        Reg s2 = setReg A w_out /\
        Flag s2 = (fun f =>
            match f with
            | N => bit 7 w_out
            | Z => bv_eqb w_out 0x00
            | C => c
            | V =>
                negb (Bool.eqb (bit 7 w_out) (bit 7 (Reg s1 A))) &&
                negb (Bool.eqb (bit 7 w_out) (bit 7 w_in))
            | _ => Flag s1 f
            end) /\
        RAM s2 = RAM s1.

Definition SBC_decimal_relation (c_in : bool) (w1 w2 w : bv 8) (c_out : bool) : Prop :=
    forall n1 n2, is_bcd w1 n1 -> is_bcd w2 n2 ->
    exists n, is_bcd w n /\
    (n + (if c_out then 0 else 100) + n2 + (if c_in then 0 else 1) = n1)%Z.

Definition SBC_mode mode mode_len :=
    if Flag s1 D
    then exists addr w_in w_out c_out v,
        mode s1 addr /\
        fetch s1 addr w_in /\
        SBC_decimal_relation (Flag s1 C) (Reg s1 A) w_in w_out c_out /\
        PC s2 = bv_add_Z (PC s1) mode_len /\
        Reg s2 = setReg A w_out /\
        Flag s2 = (fun f =>
            match f with
            | N => bit 7 w_out
            | Z => bv_eqb w_out 0x00
            | C => c_out
            | V => v
            | _ => Flag s1 f
            end) /\
        RAM s2 = RAM s1
    else exists addr w_in,
        mode s1 addr /\
        fetch s1 addr w_in /\
        let: (w_out, c) := sub_with_inverted_borrow (Flag s1 C) (Reg s1 A) w_in in
        PC s2 = bv_add_Z (PC s1) mode_len /\
        Reg s2 = setReg A w_out /\
        Flag s2 = (fun f =>
            match f with
            | N => bit 7 w_out
            | Z => bv_eqb w_out 0x00
            | C => c
            | V =>
                negb (Bool.eqb (bit 7 w_out) (bit 7 (Reg s1 A))) &&
                negb (Bool.eqb (bit 7 w_out) (bit 7 w_in))
            | _ => Flag s1 f
            end) /\
        RAM s2 = RAM s1.


Record instruction (op : bv 8) : Prop := {
    NOP : op = 0xea -> PC s2 = bv_add_Z (PC s1) 1 /\ Reg s2 = Reg s1 /\ Flag s2 = Flag s1 /\ RAM s2 = RAM s1;

    TXS : op = 0x9a -> PC s2 = bv_add_Z (PC s1) 1 /\ Reg s2 = setReg SP (Reg s1 X) /\ Flag s2 = Flag s1 /\ RAM s2 = RAM s1;
    TSX : op = 0xba -> transfer_instruction SP X;
    TAX : op = 0xaa -> transfer_instruction A X;
    TXA : op = 0x8a -> transfer_instruction X A;
    TAY : op = 0xa8 -> transfer_instruction A Y;
    TYA : op = 0x98 -> transfer_instruction Y A;

    CLC : op = 0x18 -> flag_instruction C false;
    SEC : op = 0x38 -> flag_instruction C true;
    CLI : op = 0x58 -> flag_instruction I false;
    SEI : op = 0x78 -> flag_instruction I true;
    CLV : op = 0xb8 -> flag_instruction V false;
    CLD : op = 0xd8 -> flag_instruction D false;
    SED : op = 0xf8 -> flag_instruction D true;

    RTS : op = 0x60 -> exists w1 w2,
        fetch s1 (bv_zero_extend 16 (bv_add_Z (Reg s1 SP) 1)) w1 /\
        fetch s2 (bv_zero_extend 16 (bv_add_Z (Reg s1 SP) 2)) w2 /\
        PC s2 = bv_add_Z (bv_concat 16 w1 w2) 1 /\
        Reg s2 = Reg s1 /\
        Flag s2 = Flag s1 /\
        RAM s2 = RAM s1;

    BPL : op = 0x10 -> branch_instruction (fun s => negb (Flag s N));
    BMI : op = 0x30 -> branch_instruction (fun s =>      (Flag s N));
    BVC : op = 0x50 -> branch_instruction (fun s => negb (Flag s V));
    BVS : op = 0x70 -> branch_instruction (fun s =>      (Flag s V));
    BCC : op = 0x90 -> branch_instruction (fun s => negb (Flag s N));
    BCS : op = 0xb0 -> branch_instruction (fun s =>      (Flag s N));
    BNE : op = 0xd0 -> branch_instruction (fun s => negb (Flag s Z));
    BEQ : op = 0xf0 -> branch_instruction (fun s =>      (Flag s Z));

    STA_absolute   : op = 0x8d -> store_instruction A absolute 3;
    STX_absolute   : op = 0x8e -> store_instruction X absolute 3;
    STY_absolute   : op = 0x8c -> store_instruction Y absolute 3;
    STA_absolute_x : op = 0x9d -> store_instruction A absolute_x 3;
    STA_absolute_y : op = 0x99 -> store_instruction A absolute_y 3;
    STA_zero_page  : op = 0x85 -> store_instruction A zero_page 2;
    STX_zero_page  : op = 0x86 -> store_instruction X zero_page 2;
    STY_zero_page  : op = 0x84 -> store_instruction Y zero_page 2;
    STA_zero_page_x: op = 0x95 -> store_instruction A zero_page_x 2;
    STX_zero_page_y: op = 0x96 -> store_instruction X zero_page_y 2;
    STY_zero_page_x: op = 0x94 -> store_instruction Y zero_page_x 2;
    STA_indirect_x : op = 0x81 -> store_instruction A indirect_x 2;
    STA_indirect_y : op = 0x91 -> store_instruction A indirect_y 2;

    LDA_absolute   : op = 0xad -> load_instruction A absolute 3;
    LDX_absolute   : op = 0xae -> load_instruction X absolute 3;
    LDY_absolute   : op = 0xac -> load_instruction Y absolute 3;
    LDA_absolute_x : op = 0xbd -> load_instruction A absolute_x 3;
    LDA_absolute_y : op = 0xb9 -> load_instruction A absolute_y 3;
    LDX_absolute_y : op = 0xbe -> load_instruction X absolute_y 3;
    LDY_absolute_x : op = 0xbc -> load_instruction Y absolute_x 3;
    LDA_immediate  : op = 0xa9 -> load_instruction A immediate 2;
    LDX_immediate  : op = 0xa2 -> load_instruction X immediate 2;
    LDY_immediate  : op = 0xa0 -> load_instruction Y immediate 2;
    LDA_zero_page  : op = 0xa5 -> load_instruction A zero_page 2;
    LDX_zero_page  : op = 0xa6 -> load_instruction X zero_page 2;
    LDY_zero_page  : op = 0xa4 -> load_instruction Y zero_page 2;
    LDA_zero_page_x: op = 0xb5 -> load_instruction A zero_page_x 2;
    LDX_zero_page_y: op = 0xb6 -> load_instruction X zero_page_y 2;
    LDY_zero_page_x: op = 0xb4 -> load_instruction Y zero_page_x 2;
    LDA_indirect_x : op = 0xa1 -> load_instruction A indirect_x 2;
    LDA_indirect_y : op = 0xb1 -> load_instruction A indirect_y 2;
    
    ORA_indirect_x : op = 0x01 -> logic_instruction bv_or  indirect_x 2;
    ORA_zero_page  : op = 0x05 -> logic_instruction bv_or  zero_page  2;
    ORA_immediate  : op = 0x09 -> logic_instruction bv_or  immediate  2;
    ORA_absolute   : op = 0x0d -> logic_instruction bv_or  absolute   3;
    ORA_indirect_y : op = 0x11 -> logic_instruction bv_or  indirect_y 2;
    ORA_zero_page_x: op = 0x15 -> logic_instruction bv_or  zero_page_x 2;
    ORA_absolute_y : op = 0x19 -> logic_instruction bv_or  absolute_y 3;
    ORA_absolute_x : op = 0x1d -> logic_instruction bv_or  absolute_x 3;
    AND_indirect_x : op = 0x21 -> logic_instruction bv_and indirect_x 2;
    AND_zero_page  : op = 0x25 -> logic_instruction bv_and zero_page  2;
    AND_immediate  : op = 0x29 -> logic_instruction bv_and immediate  2;
    AND_absolute   : op = 0x2d -> logic_instruction bv_and absolute   3;
    AND_indirect_y : op = 0x31 -> logic_instruction bv_and indirect_y 2;
    AND_zero_page_x: op = 0x35 -> logic_instruction bv_and zero_page_x 2;
    AND_absolute_y : op = 0x39 -> logic_instruction bv_and absolute_y 3;
    AND_absolute_x : op = 0x3d -> logic_instruction bv_and absolute_x 3;
    EOR_indirect_x : op = 0x41 -> logic_instruction bv_xor indirect_x 2;
    EOR_zero_page  : op = 0x45 -> logic_instruction bv_xor zero_page  2;
    EOR_immediate  : op = 0x49 -> logic_instruction bv_xor immediate  2;
    EOR_absolute   : op = 0x4d -> logic_instruction bv_xor absolute   3;
    EOR_indirect_y : op = 0x51 -> logic_instruction bv_xor indirect_y 2;
    EOR_zero_page_x: op = 0x55 -> logic_instruction bv_xor zero_page_x 2;
    EOR_absolute_y : op = 0x59 -> logic_instruction bv_xor absolute_y 3;
    EOR_absolute_x : op = 0x5d -> logic_instruction bv_xor absolute_x 3;

    BIT_absolute   : op = 0x2c -> BIT_mode absolute  3;
    BIT_zero_page  : op = 0x24 -> BIT_mode zero_page 2;
    BIT_immediate  : op = 0x89 -> BIT_mode immediate 2;

    INX : op = 0xe8 -> INC_reg X;
    INY : op = 0xc8 -> INC_reg Y;
    DEX : op = 0xca -> DEC_reg X;
    DEY : op = 0x88 -> DEC_reg Y;
    
    INC_absolute   : op = 0xee -> INC_mode absolute 3;
    INC_absolute_x : op = 0xfe -> INC_mode absolute_x 3;
    INC_zero_page  : op = 0xe6 -> INC_mode zero_page 2;
    INC_zero_page_x: op = 0xf6 -> INC_mode zero_page_x 2;
    DEC_absolute   : op = 0xce -> DEC_mode absolute 3;
    DEC_absolute_x : op = 0xde -> DEC_mode absolute_x 3;
    DEC_zero_page  : op = 0xc6 -> DEC_mode zero_page 2;
    DEC_zero_page_x: op = 0xd6 -> DEC_mode zero_page_x 2;

    ASL_A          : op = 0x0a -> shift_instruction_A ASL_spec;
    ROL_A          : op = 0x2a -> shift_instruction_A ROL_spec;
    LSR_A          : op = 0x4a -> shift_instruction_A LSR_spec;
    ROR_A          : op = 0x6a -> shift_instruction_A ROR_spec;
    ASL_absolute   : op = 0x0e -> shift_instruction_mode ASL_spec absolute 3;
    ROL_absolute   : op = 0x2e -> shift_instruction_mode ROL_spec absolute 3;
    LSR_absolute   : op = 0x4e -> shift_instruction_mode LSR_spec absolute 3;
    ROR_absolute   : op = 0x6e -> shift_instruction_mode ROR_spec absolute 3;
    ASL_absolute_x : op = 0x1e -> shift_instruction_mode ASL_spec absolute_x 3;
    ROL_absolute_x : op = 0x3e -> shift_instruction_mode ROL_spec absolute_x 3;
    LSR_absolute_x : op = 0x5e -> shift_instruction_mode LSR_spec absolute_x 3;
    ROR_absolute_x : op = 0x7e -> shift_instruction_mode ROR_spec absolute_x 3;
    ASL_zero_page  : op = 0x06 -> shift_instruction_mode ASL_spec zero_page 2;
    ROL_zero_page  : op = 0x26 -> shift_instruction_mode ROL_spec zero_page 2;
    LSR_zero_page  : op = 0x46 -> shift_instruction_mode LSR_spec zero_page 2;
    ROR_zero_page  : op = 0x66 -> shift_instruction_mode ROR_spec zero_page 2;
    ASL_zero_page_x: op = 0x16 -> shift_instruction_mode ASL_spec zero_page_x 2;
    ROL_zero_page_x: op = 0x36 -> shift_instruction_mode ROL_spec zero_page_x 2;
    LSR_zero_page_x: op = 0x56 -> shift_instruction_mode LSR_spec zero_page_x 2;
    ROR_zero_page_x: op = 0x76 -> shift_instruction_mode ROR_spec zero_page_x 2;
    
    CMP_absolute   : op = 0xcd -> CMP_mode A absolute    3;
    CPX_absolute   : op = 0xec -> CMP_mode X absolute    3;
    CPY_absolute   : op = 0xcc -> CMP_mode Y absolute    3;
    CMP_absolute_x : op = 0xdd -> CMP_mode A absolute_x  3;
    CMP_absolute_y : op = 0xd9 -> CMP_mode A absolute_y  3;
    CMP_immediate  : op = 0xc9 -> CMP_mode A immediate   2;
    CPX_immediate  : op = 0xe0 -> CMP_mode X immediate   2;
    CPY_immediate  : op = 0xc0 -> CMP_mode Y immediate   2;
    CMP_zero_page  : op = 0xc5 -> CMP_mode A zero_page   2;
    CPX_zero_page  : op = 0xe4 -> CMP_mode X zero_page   2;
    CPY_zero_page  : op = 0xc4 -> CMP_mode Y zero_page   2;
    CMP_zero_page_x: op = 0xd5 -> CMP_mode A zero_page_x 2;
    CMP_indirect_x : op = 0xc1 -> CMP_mode A indirect_x  2;
    CMP_indirect_y : op = 0xd1 -> CMP_mode A indirect_y  2;
    
    ADC_absolute   : op = 0x6d -> ADC_mode absolute    3;
    ADC_absolute_x : op = 0x7d -> ADC_mode absolute_x  3;
    ADC_absolute_y : op = 0x79 -> ADC_mode absolute_y  3;
    ADC_immediate  : op = 0x69 -> ADC_mode immediate   2;
    ADC_zero_page  : op = 0x65 -> ADC_mode zero_page   2;
    ADC_zero_page_x: op = 0x75 -> ADC_mode zero_page_x 2;
    ADC_indirect_x : op = 0x61 -> ADC_mode indirect_x  2;
    ADC_indirect_y : op = 0x71 -> ADC_mode indirect_y  2;
    SBC_absolute   : op = 0xed -> SBC_mode absolute    3;
    SBC_absolute_x : op = 0xfd -> SBC_mode absolute_x  3;
    SBC_absolute_y : op = 0xf9 -> SBC_mode absolute_y  3;
    SBC_immediate  : op = 0xe9 -> SBC_mode immediate   2;
    SBC_zero_page  : op = 0xe5 -> SBC_mode zero_page   2;
    SBC_zero_page_x: op = 0xf5 -> SBC_mode zero_page_x 2;
    SBC_indirect_x : op = 0xe1 -> SBC_mode indirect_x  2;
    SBC_indirect_y : op = 0xf1 -> SBC_mode indirect_y  2;

    JMP : op = 0x4c -> exists addr,
        absolute s1 addr /\ PC s2 = addr /\ Reg s2 = Reg s1 /\ Flag s2 = Flag s1 /\ RAM s2 = RAM s1;
    (* Note: If I were to specify JMP_indirect, I'd have to account for the hardware bug. *)

    JSR : op = 0x20 -> exists addr,
        absolute s1 addr /\
        PC s2 = addr /\
        Reg s2 = setReg SP (bv_sub_Z (Reg s1 SP) 2) /\
        Flag s2 = Flag s1 /\
        RAM s2 =
            let pc := bv_sub_Z (PC s1) 1 in
            write (bv_zero_extend 16 (bv_sub_Z (Reg s1 SP) 1)) (bv_extract 0 8 pc)
                (write (bv_zero_extend 16 (Reg s1 SP)) (bv_extract 0 8 pc)
                    (RAM s1));
}.

Definition step : Prop := exists opcode, fetch s1 (PC s1) opcode /\ instruction opcode.


End StepSpec.






Inductive Player := P0 | P1.

Definition player_active (s : state) (p : Player) :=
    RAM s 0x0f = match p with P0 => 0x00 | P1 => 0x01 end.

(*
What does it mean to win Dragster?

The best I could figure out is that Dragster has been won if the branch at address 0xF39E is taken.
I was hoping there'd be a variable that clearly says "You have won!", but I couldn't find one.
*)
Definition has_just_won (s : state) (p : Player) :=
    player_active s p /\ trunc 11 (PC s) = 0x39e /\ ~~ Flag s Z.

Definition timer_in_hundredths (s : state) (p : Player) (t : BinNums.Z) : Prop :=
    exists secs hundredths,
        is_bcd (RAM s (match p with P0 => 51 | P1 => 52 end)) secs /\
        is_bcd (RAM s (match p with P0 => 53 | P1 => 54 end)) hundredths /\
        t = (hundredths + secs * 100)%Z.

(* This is the claim that any speedrun of Dragster must take at least 5.57 seconds.
The goal of this project is to prove this.
*)
Definition Goal : Prop :=
    (* Choose any valid initial state of the Atari. *)
    forall s0, initial s0 ->
    (* Choose any later state, reachable from the starting state. *)
    forall s, rtc step s0 s ->
    (* Then if some player has just won, *)
    forall p, has_just_won s p ->
    (* Then that player's timer is a valid number, which is at least 5.57 seconds. *)
    exists t, timer_in_hundredths s p t /\ (t >=? 557)%Z.
