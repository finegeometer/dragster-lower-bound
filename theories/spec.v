(*|
===================
Atari Specification
===================

In this file, I specify the behavior of the Atari 2600.
I then use this specification to define the *claim* that Dragster cannot be beaten in less than 5.57 seconds.

Since the goal of this project is to prove that something *isn't* possible, I *overapproximate* the behavior of the Atari.
So my spec might say something is possible even if it isn't, but it will never say something is impossible if it actually is.

As this file defines the thing we are proving, it is the one thing that is not formally verified.
This is a weakness in this proof — if I've misstated the behavior of the Atari, the proof doesn't prove what I think it does.
But I would expect such an error to cause a big enough impact to completely mess up the proof, which would mean I would've noticed it.

This weakness could be ameliorated by proving a relationship between this specification and the http://www.visual6502.org/ netlist.
But I don't know how to properly specify the set of possible behaviors of a transistor circuit.

--------------
Bits and Bytes
--------------

A `bitvector library <https://plv.mpi-sws.org/coqdoc/stdpp/stdpp.unstable.bitvector.html>` is provided by ``std++``, but there are a few things that bother me.
|*)

From stdpp Require Import ssreflect unstable.bitvector.
Local Open Scope bv.

(*|
1. Somehow, there doesn't seem to be a bit test function on bitvectors?
|*)

Definition bit {n} i (w : bv n) : bool := Z.testbit (bv_unsigned w) i.

(*|
2. While zero-extension to a shorter word acts as truncation, that's really not intuitive when your code needs a truncation operation.
|*)

Definition trunc {n} m (w : bv n) : bv m := bv_zero_extend m w.

(*|
3. I need a boolean-valued equality test.
|*)

Definition bv_eqb {n} (w1 w2 : bv n) : bool :=
    if decide (w1 = w2) then true else false.

(*|
4. The library's ``bv_concat`` takes the high word first. But I want to think in little-endian, so I need to swap that.
|*)

Definition bv_concat n {n1 n2} (b1 : bv n1) (b2 : bv n2) : bv n :=
    bv_concat n b2 b1.

(*|
5. I need addition and subtraction operations that take and return carry bits.
|*)

Definition add_with_carry {n}
    (c_in : bool) (w1 w2 : bv n) : bv n * bool :=
    let out :=
        bv_zero_extend (n + 1) (bool_to_bv 1 c_in) +
        (bv_zero_extend (n + 1) w1 + bv_zero_extend (n + 1) w2)
    in (trunc n out, bit (Z.of_N n) out).
Definition sub_with_inverted_borrow {n}
    cin (w1 w2 : bv n) : bv n * bool :=
    add_with_carry cin w1 (bv_not w2).

(*|
-----------
Atari State
-----------

The Atari 2600 uses a 6507 processor, which is basically a 6502 in a smaller package.

The 6502 has four registers:
* The accumulator, ``A``.
* The index registers, ``X`` and ``Y``.
* The stack pointer, ``SP``.
|*)

Inductive reg := X|Y|A|SP.

Global Instance reg_eq_dec : EqDecision reg.
Proof.
    unfold EqDecision, Decision.
    case; case; try (by left); by right.
Defined.

Definition reg_eqb (r1 r2 : reg) : bool :=
    if decide (r1 = r2) then true else false.

(*|
It also has seven boolean flags.
|*)

Inductive flag := N|B|V|D|I|Z|C.

Global Instance flag_eq_dec : EqDecision flag.
Proof.
    unfold EqDecision, Decision.
    case; case; try (by left); by right.
Defined.

Definition flag_eqb (f1 f2 : flag) : bool :=
    if decide (f1 = f2) then true else false.

(*|
Finally, it has a sixteen-bit program counter.

In addition to the processor, the Atari has 128 bytes of RAM.

There are also a few other components, which handle things like hardware timers, I/O, and graphics.
I take a very simple approach to modeling these: Don't!
I make no assumptions at all about the result of reading from these chips, so I don't have to keep track of their state or behavior.

With that in mind, the following structure models the state of the Atari.
|*)

Record state := {
    (* processor *)
    Reg : reg -> bv 8;
    Flag : flag -> bool;
    PC : bv 16;

    (* memory *)
    RAM : bv 7 -> bv 8;
}.

(*|
----------------
Reads and Writes
----------------

The Atari 2600's address space is memory-mapped as follows::

    ___1 _xxx xxxx xxxx => ROM
    ___0 ____ 0_xx xxxx => Television Interface Adapter
    ___0 __1_ 1xxx xxxx => RAM
    ___0 __0_ 1__x xxxx => Peripheral Interface Adapter

(Technically, the Peripheral Interface Adapter contains the RAM. But I'm using the term to mean the part that isn't the RAM.)


Let's implement this.
|*)

From theories Require Import rom.

(*|
``fetch s addr value`` is the statement, "If the Atari is in state ``s``, a read from ``addr`` *might* return ``value``.".

In particular, when ``addr`` points to the TIA or PIA, ``fetch s addr value`` is simply ``True``.
Since I don't model those components, I assume they can do anything they want.
|*)

Definition fetch (s : state) (addr : bv 16) (value : bv 8) : Prop :=
    if bit 12 addr
    then value = ROM (trunc 11 addr)
    else if negb (bit 7 addr) || bit 9 addr
    then True
    else value = RAM s (trunc 7 addr).

(*|
If ``ram`` is the current state of the RAM, ``write addr value ram`` is the state after writing ``value`` to address ``addr``.

Note that if you write to anything other than the RAM, nothing happens:

* Writing to the TIA or PIA will change their state. But that state isn't modeled, so who cares?
* If you write to the ROM...

  Honestly, I can't find a clear answer for what happens.
  But the ROM has no state to change, and all the other chips are deselected,
  so the only reasonable option seems to be that nothing happens.

.. coq::
|*)

Definition write (addr : bv 16) (value : bv 8)
    (ram : bv 7 -> bv 8) : bv 7 -> bv 8 :=
    if bit 12 addr
    then ram
    else if negb (bit 7 addr) || bit 9 addr
    then ram
    else fun addr' =>
        if bv_eqb (trunc 7 addr) addr'
        then value
        else ram addr'.

(*|
-------
Startup
-------

When the Atari is turned on, the interrupt-disable flag is turned on,
and the program counter is set to the address stored at 0xfffc and 0xfffd.
|*)

Record initial (s : state) : Prop := {
    init_interrupt_disable : Flag s I;
    pc_init : exists w1 w2,
        fetch s 0xfffc w1 /\
        fetch s 0xfffd w2 /\
        PC s = bv_concat 16 w1 w2
}.

(*|
--------------------
Instruction Stepping
--------------------

If the current state is ``s1``, is it possible that after one instruction, the state will be ``s2``?

Recall that I am *overapproximating* the behavior of the Atari.
So the specification takes the form a long list of restrictions.
E.g. "If running instruction ``0xea`` can transform state ``s1`` into ``s2``,
then we must have ``PC s2 = PC s1 + 1``, ``Reg s2 = Reg s1``, ``Flag s2 = Flag s1``, and ``RAM s2 = RAM s1``.".

If you scroll to the bottom of this section, you'll find the record ``instruction``.
This is that list. Everything above that is helper functions for defining the restrictions.
|*)

Section StepSpec.

Context (s1 s2 : state).

Definition setReg (r : reg) (value : bv 8) : reg -> bv 8 :=
    fun r' => if reg_eqb r r' then value else Reg s1 r'.

Definition setNZ (value : bv 8) : flag -> bool := fun f =>
    match f with
    | N => bit 7 value
    | Z => bv_eqb value 0x00
    | _ => Flag s1 f
    end.

Definition transfer_instr r1 r2 :=
    PC s2 = PC s1 `+Z` 1 /\
    Reg s2 = setReg r2 (Reg s1 r1) /\
    Flag s2 = setNZ (Reg s1 r1) /\
    RAM s2 = RAM s1.

Definition flag_instr (f : flag) (value : bool) : Prop :=
    PC s2 = PC s1 `+Z` 1 /\
    Reg s2 = Reg s1 /\
    (Flag s2 = fun f' => 
        if flag_eqb f f'
        then value
        else Flag s1 f') /\
    RAM s2 = RAM s1.

Definition branch_instr (cond : state -> bool) : Prop :=
    exists dist,
        fetch s1 (PC s1 `+Z` 1) dist /\
        (PC s2 =
            let pc := PC s1 `+Z` 2 in
            if cond s1
            then pc + bv_sign_extend 16 dist
            else pc) /\
        Reg s2 = Reg s1 /\
        Flag s2 = Flag s1 /\
        RAM s2 = RAM s1.

Definition mem_addressing_mode := state -> bv 16 -> Prop.
Definition absolute : mem_addressing_mode :=
    fun s addr => exists w1 w2,
        fetch s (PC s `+Z` 1) w1 /\
        fetch s (PC s `+Z` 2) w2 /\
        addr = bv_concat 16 w1 w2.
Definition absolute_x : mem_addressing_mode :=
    fun s addr => exists w1 w2,
        fetch s (PC s `+Z` 1) w1 /\
        fetch s (PC s `+Z` 2) w2 /\
        addr = bv_concat 16 w1 w2 + bv_zero_extend 16 (Reg s X).
Definition absolute_y : mem_addressing_mode :=
    fun s addr => exists w1 w2,
        fetch s (PC s `+Z` 1) w1 /\
        fetch s (PC s `+Z` 2) w2 /\
        addr = bv_concat 16 w1 w2 + bv_zero_extend 16 (Reg s Y).
Definition zero_page : mem_addressing_mode :=
    fun s addr => exists w,
        fetch s (PC s `+Z` 1) w /\
        addr = bv_zero_extend 16 w.
Definition zero_page_x : mem_addressing_mode :=
    fun s addr => exists w,
        fetch s (PC s `+Z` 1) w /\
        addr = bv_zero_extend 16 (w + Reg s X).
Definition zero_page_y : mem_addressing_mode :=
    fun s addr => exists w,
        fetch s (PC s `+Z` 1) w /\
        addr = bv_zero_extend 16 (w + Reg s Y).
Definition indirect_x : mem_addressing_mode :=
    fun s addr => exists w w1 w2,
        fetch s (PC s `+Z` 1) w /\
        let indir := w + Reg s X in
        fetch s (bv_zero_extend 16 indir) w1 /\
        fetch s (bv_zero_extend 16 (indir `+Z` 1)) w2 /\
        addr = bv_concat 16 w1 w2.
Definition indirect_y : mem_addressing_mode :=
    fun s addr => exists indir w1 w2,
        fetch s (PC s `+Z` 1) indir /\
        fetch s (bv_zero_extend 16 indir) w1 /\
        fetch s (bv_zero_extend 16 (indir `+Z` 1)) w2 /\
        addr = bv_concat 16 w1 w2 + bv_zero_extend 16 (Reg s Y).
(* This isn't traditionally treated as a *memory* addressing mode.
    But in a sense, it is.
    It accesses the memory immediately following the opcode! *)
Definition immediate : mem_addressing_mode :=
    fun s addr => addr = PC s `+Z` 1.

Definition store_instr register mode mode_len :=
    exists addr,
        mode s1 addr /\
        PC s2 = PC s1 `+Z` mode_len /\
        Reg s2 = Reg s1 /\
        Flag s2 = Flag s1 /\
        RAM s2 = write addr (Reg s1 register) (RAM s1).

Definition load_instr register mode mode_len :=
    exists addr w,
        mode s1 addr /\
        fetch s1 addr w /\
        PC s2 = PC s1 `+Z` mode_len /\
        Reg s2 = setReg register w /\
        Flag s2 = setNZ w /\
        RAM s2 = RAM s1.

Definition logic_instr operation mode mode_len :=
    exists addr w,
        mode s1 addr /\
        fetch s1 addr w /\
        let w := operation (Reg s1 A) w in
        PC s2 = PC s1 `+Z` mode_len /\
        Reg s2 = setReg A w /\
        Flag s2 = setNZ w /\
        RAM s2 = RAM s1.

Definition BIT_mode mode mode_len :=
    exists addr w,
        mode s1 addr /\
        fetch s1 addr w /\
        let w := bv_and (Reg s1 A) w in
        PC s2 = PC s1 `+Z` mode_len /\
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
    let w := Reg s1 r `+Z` 1 in
    PC s2 = PC s1 `+Z` 1 /\
    Reg s2 = setReg r w /\
    Flag s2 = setNZ w /\
    RAM s2 = RAM s1.
Definition INC_mode mode mode_len :=
    exists addr w,
        mode s1 addr /\
        fetch s1 addr w /\
        let w := w `+Z` 1 in
        PC s2 = PC s1 `+Z` mode_len /\
        Reg s2 = Reg s1 /\
        Flag s2 = setNZ w /\
        RAM s2 = write addr w (RAM s1).
Definition DEC_reg r :=
    let w := Reg s1 r `-Z` 1 in
    PC s2 = PC s1 `+Z` 1 /\
    Reg s2 = setReg r w /\
    Flag s2 = setNZ w /\
    RAM s2 = RAM s1.
Definition DEC_mode mode mode_len :=
    exists addr w,
        mode s1 addr /\
        fetch s1 addr w /\
        let w := bv_sub_Z w 1 in
        PC s2 = PC s1 `+Z` mode_len /\
        Reg s2 = Reg s1 /\
        Flag s2 = setNZ w /\
        RAM s2 = write addr w (RAM s1).


Definition shift_instr_A
    (shift_spec : bv 8 -> bool -> bv 8 -> bool -> Prop) :=
    exists cout (w : bv 8),
        shift_spec
            (Reg s1 A) (Flag s1 C)
            w cout /\
        PC s2 = PC s1 `+Z` 1 /\
        Reg s2 = setReg A w /\
        Flag s2 = (fun f =>
            match f with
            | N => bit 7 w
            | Z => bv_eqb w 0x00
            | C => cout
            | _ => Flag s1 f
            end) /\
        RAM s2 = RAM s1.
Definition shift_instr_mode
    (shift_spec : bv 8 -> bool -> bv 8 -> bool -> Prop) mode mode_len :=
    exists addr w_in cout (w_out : bv 8),
        mode s1 addr /\
        fetch s1 addr w_in /\
        shift_spec
            w_in (Flag s1 C)
            w_out cout /\
        PC s2 = PC s1 `+Z` mode_len /\
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
        let: (w, c) :=
            sub_with_inverted_borrow true (Reg s1 register) w
        in
        PC s2 = PC s1 `+Z` mode_len /\
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

Definition ADC_decimal_relation
    (c_in : bool) (w1 w2 w : bv 8) (c_out : bool) : Prop :=
    forall n1 n2, is_bcd w1 n1 -> is_bcd w2 n2 ->
    exists n, is_bcd w n /\
    ( n + (if c_out then 100 else 0)
    = (if c_in then 1 else 0) + n1 + n2
    )%Z.

Definition ADC_mode mode mode_len :=
    if Flag s1 D
    then exists addr w_in w_out c_out v,
        mode s1 addr /\
        fetch s1 addr w_in /\
        ADC_decimal_relation (Flag s1 C) (Reg s1 A) w_in w_out c_out /\
        PC s2 = PC s1 `+Z` mode_len /\
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
        let:
            (w_out, c) := add_with_carry (Flag s1 C) (Reg s1 A) w_in
        in
        PC s2 = PC s1 `+Z` mode_len /\
        Reg s2 = setReg A w_out /\
        Flag s2 = (fun f =>
            match f with
            | N => bit 7 w_out
            | Z => bv_eqb w_out 0x00
            | C => c
            | V => negb
                (bv_signed w_out =?
                    bv_signed (Reg s1 A) + bv_signed w_in)%Z
            | _ => Flag s1 f
            end) /\
        RAM s2 = RAM s1.

Definition SBC_decimal_relation
    (c_in : bool) (w1 w2 w : bv 8) (c_out : bool) : Prop :=
    forall n1 n2, is_bcd w1 n1 -> is_bcd w2 n2 ->
    exists n, is_bcd w n /\
    ( n + (if c_out then 0 else 100) + n2 + (if c_in then 0 else 1)
    = n1)%Z.

Definition SBC_mode mode mode_len :=
    if Flag s1 D
    then exists addr w_in w_out c_out v,
        mode s1 addr /\
        fetch s1 addr w_in /\
        SBC_decimal_relation (Flag s1 C) (Reg s1 A) w_in w_out c_out /\
        PC s2 = PC s1 `+Z` mode_len /\
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
        let: (w_out, c) :=
            sub_with_inverted_borrow (Flag s1 C) (Reg s1 A) w_in
        in
        PC s2 = PC s1 `+Z` mode_len /\
        Reg s2 = setReg A w_out /\
        Flag s2 = (fun f =>
            match f with
            | N => bit 7 w_out
            | Z => bv_eqb w_out 0x00
            | C => c
            | V => negb
                (bv_signed w_out =?
                    bv_signed (Reg s1 A) - bv_signed w_in)%Z
            | _ => Flag s1 f
            end) /\
        RAM s2 = RAM s1.


Record instruction (op : bv 8) : Prop := {
    NOP : op = 0xea ->
        PC s2 = PC s1 `+Z` 1 /\
        Reg s2 = Reg s1 /\
        Flag s2 = Flag s1 /\
        RAM s2 = RAM s1;

    TXS : op = 0x9a ->
        PC s2 = PC s1 `+Z` 1 /\
        Reg s2 = setReg SP (Reg s1 X) /\
        Flag s2 = Flag s1 /\
        RAM s2 = RAM s1;
    TSX : op = 0xba -> transfer_instr SP X;
    TAX : op = 0xaa -> transfer_instr A X;
    TXA : op = 0x8a -> transfer_instr X A;
    TAY : op = 0xa8 -> transfer_instr A Y;
    TYA : op = 0x98 -> transfer_instr Y A;

    CLC : op = 0x18 -> flag_instr C false;
    SEC : op = 0x38 -> flag_instr C true;
    CLI : op = 0x58 -> flag_instr I false;
    SEI : op = 0x78 -> flag_instr I true;
    CLV : op = 0xb8 -> flag_instr V false;
    CLD : op = 0xd8 -> flag_instr D false;
    SED : op = 0xf8 -> flag_instr D true;

    BPL : op = 0x10 -> branch_instr (fun s => negb (Flag s N));
    BMI : op = 0x30 -> branch_instr (fun s =>      (Flag s N));
    BVC : op = 0x50 -> branch_instr (fun s => negb (Flag s V));
    BVS : op = 0x70 -> branch_instr (fun s =>      (Flag s V));
    BCC : op = 0x90 -> branch_instr (fun s => negb (Flag s C));
    BCS : op = 0xb0 -> branch_instr (fun s =>      (Flag s C));
    BNE : op = 0xd0 -> branch_instr (fun s => negb (Flag s Z));
    BEQ : op = 0xf0 -> branch_instr (fun s =>      (Flag s Z));

    STA_absolute   : op = 0x8d -> store_instr A absolute 3;
    STX_absolute   : op = 0x8e -> store_instr X absolute 3;
    STY_absolute   : op = 0x8c -> store_instr Y absolute 3;
    STA_absolute_x : op = 0x9d -> store_instr A absolute_x 3;
    STA_absolute_y : op = 0x99 -> store_instr A absolute_y 3;
    STA_zero_page  : op = 0x85 -> store_instr A zero_page 2;
    STX_zero_page  : op = 0x86 -> store_instr X zero_page 2;
    STY_zero_page  : op = 0x84 -> store_instr Y zero_page 2;
    STA_zero_page_x: op = 0x95 -> store_instr A zero_page_x 2;
    STX_zero_page_y: op = 0x96 -> store_instr X zero_page_y 2;
    STY_zero_page_x: op = 0x94 -> store_instr Y zero_page_x 2;
    STA_indirect_x : op = 0x81 -> store_instr A indirect_x 2;
    STA_indirect_y : op = 0x91 -> store_instr A indirect_y 2;

    LDA_absolute   : op = 0xad -> load_instr A absolute 3;
    LDX_absolute   : op = 0xae -> load_instr X absolute 3;
    LDY_absolute   : op = 0xac -> load_instr Y absolute 3;
    LDA_absolute_x : op = 0xbd -> load_instr A absolute_x 3;
    LDA_absolute_y : op = 0xb9 -> load_instr A absolute_y 3;
    LDX_absolute_y : op = 0xbe -> load_instr X absolute_y 3;
    LDY_absolute_x : op = 0xbc -> load_instr Y absolute_x 3;
    LDA_immediate  : op = 0xa9 -> load_instr A immediate 2;
    LDX_immediate  : op = 0xa2 -> load_instr X immediate 2;
    LDY_immediate  : op = 0xa0 -> load_instr Y immediate 2;
    LDA_zero_page  : op = 0xa5 -> load_instr A zero_page 2;
    LDX_zero_page  : op = 0xa6 -> load_instr X zero_page 2;
    LDY_zero_page  : op = 0xa4 -> load_instr Y zero_page 2;
    LDA_zero_page_x: op = 0xb5 -> load_instr A zero_page_x 2;
    LDX_zero_page_y: op = 0xb6 -> load_instr X zero_page_y 2;
    LDY_zero_page_x: op = 0xb4 -> load_instr Y zero_page_x 2;
    LDA_indirect_x : op = 0xa1 -> load_instr A indirect_x 2;
    LDA_indirect_y : op = 0xb1 -> load_instr A indirect_y 2;

    ORA_indirect_x : op = 0x01 -> logic_instr bv_or  indirect_x 2;
    ORA_zero_page  : op = 0x05 -> logic_instr bv_or  zero_page  2;
    ORA_immediate  : op = 0x09 -> logic_instr bv_or  immediate  2;
    ORA_absolute   : op = 0x0d -> logic_instr bv_or  absolute   3;
    ORA_indirect_y : op = 0x11 -> logic_instr bv_or  indirect_y 2;
    ORA_zero_page_x: op = 0x15 -> logic_instr bv_or  zero_page_x 2;
    ORA_absolute_y : op = 0x19 -> logic_instr bv_or  absolute_y 3;
    ORA_absolute_x : op = 0x1d -> logic_instr bv_or  absolute_x 3;
    AND_indirect_x : op = 0x21 -> logic_instr bv_and indirect_x 2;
    AND_zero_page  : op = 0x25 -> logic_instr bv_and zero_page  2;
    AND_immediate  : op = 0x29 -> logic_instr bv_and immediate  2;
    AND_absolute   : op = 0x2d -> logic_instr bv_and absolute   3;
    AND_indirect_y : op = 0x31 -> logic_instr bv_and indirect_y 2;
    AND_zero_page_x: op = 0x35 -> logic_instr bv_and zero_page_x 2;
    AND_absolute_y : op = 0x39 -> logic_instr bv_and absolute_y 3;
    AND_absolute_x : op = 0x3d -> logic_instr bv_and absolute_x 3;
    EOR_indirect_x : op = 0x41 -> logic_instr bv_xor indirect_x 2;
    EOR_zero_page  : op = 0x45 -> logic_instr bv_xor zero_page  2;
    EOR_immediate  : op = 0x49 -> logic_instr bv_xor immediate  2;
    EOR_absolute   : op = 0x4d -> logic_instr bv_xor absolute   3;
    EOR_indirect_y : op = 0x51 -> logic_instr bv_xor indirect_y 2;
    EOR_zero_page_x: op = 0x55 -> logic_instr bv_xor zero_page_x 2;
    EOR_absolute_y : op = 0x59 -> logic_instr bv_xor absolute_y 3;
    EOR_absolute_x : op = 0x5d -> logic_instr bv_xor absolute_x 3;

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

    ASL_A          : op = 0x0a->shift_instr_A ASL_spec;
    ROL_A          : op = 0x2a->shift_instr_A ROL_spec;
    LSR_A          : op = 0x4a->shift_instr_A LSR_spec;
    ROR_A          : op = 0x6a->shift_instr_A ROR_spec;
    ASL_absolute   : op = 0x0e->shift_instr_mode ASL_spec absolute 3;
    ROL_absolute   : op = 0x2e->shift_instr_mode ROL_spec absolute 3;
    LSR_absolute   : op = 0x4e->shift_instr_mode LSR_spec absolute 3;
    ROR_absolute   : op = 0x6e->shift_instr_mode ROR_spec absolute 3;
    ASL_absolute_x : op = 0x1e->shift_instr_mode ASL_spec absolute_x 3;
    ROL_absolute_x : op = 0x3e->shift_instr_mode ROL_spec absolute_x 3;
    LSR_absolute_x : op = 0x5e->shift_instr_mode LSR_spec absolute_x 3;
    ROR_absolute_x : op = 0x7e->shift_instr_mode ROR_spec absolute_x 3;
    ASL_zero_page  : op = 0x06->shift_instr_mode ASL_spec zero_page 2;
    ROL_zero_page  : op = 0x26->shift_instr_mode ROL_spec zero_page 2;
    LSR_zero_page  : op = 0x46->shift_instr_mode LSR_spec zero_page 2;
    ROR_zero_page  : op = 0x66->shift_instr_mode ROR_spec zero_page 2;
    ASL_zero_page_x: op = 0x16->shift_instr_mode ASL_spec zero_page_x 2;
    ROL_zero_page_x: op = 0x36->shift_instr_mode ROL_spec zero_page_x 2;
    LSR_zero_page_x: op = 0x56->shift_instr_mode LSR_spec zero_page_x 2;
    ROR_zero_page_x: op = 0x76->shift_instr_mode ROR_spec zero_page_x 2;

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
        absolute s1 addr /\
        PC s2 = addr /\
        Reg s2 = Reg s1 /\
        Flag s2 = Flag s1 /\
        RAM s2 = RAM s1;
    (* Note: If I were to specify JMP_indirect,
        I'd have to account for the hardware bug. *)

    JSR : op = 0x20 -> exists addr,
        absolute s1 addr /\
        PC s2 = addr /\
        Reg s2 = setReg SP (bv_sub_Z (Reg s1 SP) 2) /\
        Flag s2 = Flag s1 /\
        RAM s2 =
            let pc := bv_sub_Z (PC s1) 1 in
            write
                (bv_zero_extend 16 (bv_sub_Z (Reg s1 SP) 1))
                (bv_extract 0 8 pc)
                (write
                    (bv_zero_extend 16 (Reg s1 SP))
                    (bv_extract 0 8 pc)
                    (RAM s1));

    RTS : op = 0x60 -> exists w1 w2,
        fetch s1 (bv_zero_extend 16 (Reg s1 SP `+Z` 1)) w1 /\
        fetch s1 (bv_zero_extend 16 (Reg s1 SP `+Z` 2)) w2 /\
        PC s2 = bv_concat 16 w1 w2 `+Z` 1 /\
        Reg s2 = setReg SP (bv_add_Z (Reg s1 SP) 2) /\
        Flag s2 = Flag s1 /\
        RAM s2 = RAM s1;

}.

Definition step : Prop :=
    exists opcode, fetch s1 (PC s1) opcode /\ instruction opcode.

End StepSpec.

(*|
This completes the specification of the Atari.

----
Goal
----

Ultimately, we want to prove that Dragster cannot be beaten in less than 5.57 seconds.
Here, I simply *state* the claim.

What does it mean to win Dragster?

The best I can figure out is that Dragster has been won if the branch at address 0xF39E is taken.
I was hoping there'd be a variable that clearly says "You have won!", but I couldn't find one.
|*)

Definition someone_has_won (s : state) :=
    trunc 11 (PC s) = 0x39e /\ ~~ Flag s Z.

(*|
But we need to know *who* has won, so we can check the right player's timer.

The active player is stored at RAM location 0x0f.
|*)

Inductive Player := P0 | P1.

Definition player_active (s : state) (p : Player) :=
    RAM s 0x0f = match p with P0 => 0x00 | P1 => 0x01 end.

Definition player_has_won (s : state) (p : Player) :=
    player_active s p /\ someone_has_won s.

(*|
How do we check the timer?

Each player's timer is stored in binary-coded decimal, as a three-byte number.
The first byte is in seconds, the second in hundredths, and the third in ten-thousandths of a second.
For our level of precision, we only need the first two bytes,
which are stored at 0x33 and 0x35 for player zero, and 0x34 and 0x36 for player one.
|*)

Definition timer_in_hundredths
    (s : state) (p : Player) (t : BinNums.Z) : Prop :=
    exists secs hundredths,
        is_bcd
            (RAM s (match p with P0 => 0x33 | P1 => 0x34 end))
            secs /\
        is_bcd
            (RAM s (match p with P0 => 0x35 | P1 => 0x36 end))
            hundredths /\
        t = (hundredths + secs * 100)%Z.

(*|
And at last, we can state the claim.
|*)

Definition Goal : Prop :=
    (* Choose any state the Atari might have upon startup. *)
    forall s0, initial s0 ->
    (* Choose any later state, reachable from the starting state. *)
    forall s, rtc step s0 s ->
    (* Then if some player has just won, *)
    forall p, player_has_won s p ->
    (* Then that player's timer is a valid number, *)
    exists t, timer_in_hundredths s p t /\
    (* which is at least 5.57 seconds. *)
    (t >=? 557)%Z.
