(*|
###########
Instruction
###########

The 6502 has a lot of opcodes.
About a hundred and thirty that I'm modeling, and a few I'm not.
In this file, I condense this down to something managable.

This file comes in three parts.
1. I define a language of instructions.
2. I define its behavior.
3. I prove its behavior matches the Atari's spec.


================
Part 1: Language
================

|*)

From theories Require Import spec.

(*|

----------------
addressing Modes
----------------

A hundred and thirty opcodes sounds scary.
But much of the variety comes from the proliferation of *addressing modes*;
places the instruction can find the value to operate on.

Most of these pick out a memory address. I'll call these "memory addressing modes".

|*)

Inductive mem_mode :=
| Imm
| Abs (r : option reg)
| Zpg (r : option reg)
| XInd
| IndY
| Rel
.

(*|

But an addressing mode can also pick out a register.

Only one addressing mode actually does this: the "Accumulator" mode.
Except that isn't entirely true.
Instructions like ``INX`` and ``INY``, or ``TXA`` and ``TYA``,
technically don't use an addressing mode.
But it's simpler to think of them as addressing the `X` and `Y` registers!

So I'll say there's an addressing mode for each register.

|*)

Inductive mode :=
| RegMode : reg -> mode
| MemMode : mem_mode -> mode
.

(*|

------------
Instructions
------------

Now that that's handled, what types of instructions are there?

First, there's the control flow instructions;
those where the program counter does something other than
simply proceed to the next instruction.

|*)

Inductive control :=
(* Branch if flag `f` is set to `val`. *)
| Branch (f : flag) (val : bool)
| Jmp
| Jsr
| Rts
.


(*|

Then, there are the rest. Most of these follow a simple pattern:

* Use an addressing mode to determine a location, ``l``.

  Note that this might not be the addressing mode you'd expect.
  For an operation like `ADC $0000`,
  this is the accumulator rather than the memory address.

  This is certainly a nonstandard way to think about this,
  but it seems to work well.
* Reads a value from `l`.
* Does some computation with that value.
  This may involve doing more reads, and may set the C or V flags.
* Optionally, set the N and Z flags based on the result.
* Optionally, write the result back to `l`.

But there are also a few oddballs, like the flag-setting instructions, or ``NOP``.

|*)

Inductive binop := And | Or | Xor | Adc | Sbc | Cmp | Bit | Mov.

Inductive operation :=
| Binop (_ : binop) (_ : mode)
| Inc
| Dec
| ShiftL (roll : bool)
| ShiftR (roll : bool)
.

Inductive instr :=
| Control (_ : control)
| Typical (_ : mode) (_ : operation) (setNZ : bool)
| SetFlag (_ : flag) (_ : bool)
| Nop
.


(*|
=================
Part 2: Semantics
=================

This is all well and good. But we need to explain
what the language actually means! Otherwise it's useless.

|*)

From stdpp Require Import ssreflect propset unstable.bitvector.
Local Open Scope bv_scope.

(*|

For ease of programming, let's specify nondeterministic operations
as returning the set of things they might possibly output.

For example, fetching a value from memory can nondeterministic.
Sure, ROM and RAM are predictable, but address 0x0280 points to the joystick!

|*)

Definition fetch (s : state) (addr : bv 16) : propset (bv 8) :=
    {[ w | fetch s addr w ]}.

(*|

After defining a helper for fetching 16-bit words,
it's easy to write down the behavior of all the addressing modes.

|*)

Definition fetch16 (s : state) (a1 a2 : bv 16) : propset (bv 16) :=
    w1 ← fetch s a1;
    w2 ← fetch s a2;
    {[ spec.bv_concat 16 w1 w2 ]}.

Definition mem_mode_addr (s : state) (m : mem_mode) : propset (bv 16) :=
    match m with
    | Imm => {[ PC s `+Z` 1 ]}
    | Abs r =>
        a ← fetch16 s (PC s `+Z` 1) (PC s `+Z` 2);
        {[ if r is Some r then a + bv_zero_extend 16 (Reg s r) else a ]}
    | Zpg r =>
        a ← fetch s (PC s `+Z` 1);
        {[ bv_zero_extend 16 (if r is Some r then a + Reg s r else a) ]}
    | XInd =>
        a ← fetch s (PC s `+Z` 1);
        let b := a + Reg s X in
        fetch16 s (bv_zero_extend 16 b) (bv_zero_extend 16 (b + 1))
    | IndY =>
        a ← fetch s (PC s `+Z` 1);
        b ← fetch16 s (bv_zero_extend 16 a) (bv_zero_extend 16 (a + 1));
        {[ b + bv_zero_extend 16 (Reg s Y) ]}
    | Rel => 
        a ← fetch s (PC s `+Z` 1);
        {[ (PC s `+Z` 2) + bv_sign_extend 16 a ]}
    end.


(* A location, either in a register or in memory. *)
Inductive loc := RegLoc : reg -> loc | MemLoc : bv 16 -> loc.

Definition mode_loc (s : state) (m : mode) : propset loc :=
    match m with
    | RegMode r => {[ RegLoc r ]}
    | MemMode m => MemLoc <$> mem_mode_addr s m
    end.


(*|

Now for the instructions.

Let's start with the control flow.

|*)

Definition run_control (ι : control) (s : state) : propset state :=
    match ι with
    | Branch f v =>
        if decide (Flag s f = v)
        then
            addr ← mem_mode_addr s Rel;
            {[ {|
                PC := addr;
                Reg := Reg s;
                Flag := Flag s;
                RAM := RAM s;
            |} ]}
        else {[ {|
            PC := PC s `+Z` 2;
            Reg := Reg s;
            Flag := Flag s;
            RAM := RAM s;
        |} ]}
    | Jmp =>
        addr ← mem_mode_addr s (Abs None);
        {[ {|
            PC := addr;
            Reg := Reg s;
            Flag := Flag s;
            RAM := RAM s;
        |} ]}
    | Jsr =>
        addr ← mem_mode_addr s (Abs None);
        {[ {|
            PC := addr;
            Reg := fun r =>
                if reg_eqb r SP
                then Reg s SP `-Z` 2
                else Reg s r;
            Flag := Flag s;
            RAM :=
                let pc := PC s `-Z` 1 in
                write
                    (bv_zero_extend 16 (Reg s SP `-Z` 1))
                    (bv_extract 0 8 pc)
                    (write
                        (bv_zero_extend 16 (Reg s SP))
                        (bv_extract 0 8 pc)
                        (RAM s));
        |} ]}
    | Rts =>
        addr ← fetch16 s
            (bv_zero_extend 16 (Reg s SP `+Z` 1))
            (bv_zero_extend 16 (Reg s SP `+Z` 2));
        {[ {|
            PC := addr `+Z` 1;
            Reg := fun r =>
                if reg_eqb r SP
                then Reg s SP `+Z` 2
                else Reg s r;
            Flag := Flag s;
            RAM := RAM s;
        |} ]}
    end.


(*|

For the rest of the instructions, we need to know how much space
they take up, so we know where to find the next instruction.

Fortunately, that's simple to calculate.
The opcode itself takes one byte.
Then any remaining bytes are inputs to the addressing mode.

There is the question of which addressing mode,
since I'm treating e.g. ``ADC $0000``
as using both the accumulator and absolute modes.
The answer is that one of them will always have length zero, so use the other.

|*)


(* How many bytes of input does the addressing mode take? *)
Program Definition mode_len (l : mode) : nat :=
    match l with
    | RegMode _ => 0
    | MemMode Imm => 1
    | MemMode (Abs _) => 2
    | MemMode (Zpg _) => 1
    | MemMode XInd => 1
    | MemMode IndY => 1
    | MemMode Rel => 1
    end.


(*|

Next, let's tackle the typical instructions.
We'll start with the operations.

|*)

Definition run_binop (op : binop) (s : state)
    (w1 w2 : bv 8) : propset ((bv 8 * bool) * bool) :=
    match op with
    | And => {[ ((bv_and w1 w2, Flag s C), Flag s V) ]}
    | Or  => {[ ((bv_or  w1 w2, Flag s C), Flag s V) ]}
    | Xor => {[ ((bv_xor w1 w2, Flag s C), Flag s V) ]}
    | Adc =>
        if Flag s D
        then
            v ← ⊤;
            wc ← {[wc|ADC_decimal_relation (Flag s C) w1 w2 wc.1 wc.2]};
            {[ (wc, v) ]}
        else 
            let wc := spec.add_with_carry (Flag s C) w1 w2 in
            let v:=negb(bv_signed wc.1 =? bv_signed w1 + bv_signed w2)%Z
            in {[ (wc, v) ]}
    | Sbc =>
        if Flag s D
        then
            v ← ⊤;
            wc ← {[wc|SBC_decimal_relation (Flag s C) w1 w2 wc.1 wc.2]};
            {[ (wc, v) ]}
        else 
            let wc := spec.sub_with_inverted_borrow (Flag s C) w1 w2 in
            let v:=negb(bv_signed wc.1 =? bv_signed w1 - bv_signed w2)%Z
            in {[ (wc, v) ]}
    | Cmp => {[ (spec.sub_with_inverted_borrow true w1 w2, Flag s V) ]}
    | Bit =>
        let w := bv_and w1 w2 in
        {[ ((w, Flag s C), bit 6 w) ]}
    | Mov => {[ ((w2, Flag s C), Flag s V) ]}
    end.


Definition read (s : state) (l : loc) : propset (bv 8) :=
    match l with
    | RegLoc r => {[ Reg s r ]}
    | MemLoc addr => fetch s addr
    end.

Definition run_operation (op : operation) (s : state)
    (w : bv 8) : propset ((bv 8 * bool) * bool) :=
    match op with
    | Binop op m =>
        l ← mode_loc s m;
        w2 ← read s l;
        run_binop op s w w2
    | Inc => {[ ((w `+Z` 1, Flag s C), Flag s V) ]}
    | Dec => {[ ((w `-Z` 1, Flag s C), Flag s V) ]}
    | ShiftL roll =>
        let shift_in := if roll then Flag s C else false in
        wc ←
            {[ out
            | spec.bv_concat 9 out.1 (bool_to_bv 1 out.2)
            = spec.bv_concat 9 (bool_to_bv 1 shift_in) w
            ]};
        {[ (wc, Flag s V) ]}
    | ShiftR roll =>
        let shift_in := if roll then Flag s C else false in
        wc ←
            {[ out
            | spec.bv_concat 9 (bool_to_bv 1 out.2) out.1
            = spec.bv_concat 9 w (bool_to_bv 1 shift_in)
            ]};
        {[ (wc, Flag s V) ]}
    end.

Definition run_instr (i : instr) (s : state) : propset state :=
    match i with
    | Control i => run_control i s
    | Typical m op setNZ =>
        l ← mode_loc s m;
        w ← read s l;
        computed ← run_operation op s w;
        let: ((w, c), v) := computed in
        let len :=
            Z.of_nat (S (Nat.max (mode_len m)
                match op with
                | Binop _ m' => mode_len m'
                | _ => 0
                end))
        in
        let write_back :=
            match op with
            | Binop (Cmp | Bit) _ => false
            | _ => true
            end
        in
        {[ {|
            PC := PC s `+Z` len;
            Reg :=
                match write_back, l with
                | true, RegLoc r => fun r' =>
                    if reg_eqb r r' then w else Reg s r'
                | _, _ => Reg s
                end;
            RAM :=
                match write_back, l with
                | _, MemLoc a => write a w (RAM s)
                | _, _ => RAM s
                end;
            Flag := fun f =>
                match setNZ, f with
                | true, spec.N => bit 7 w
                | true, spec.Z => bv_eqb w 0
                | _, spec.C => c
                | _, spec.V => v
                | _, _ => Flag s f
                end;
        |} ]}
    | SetFlag f val =>
        {[ {|
            PC := PC s `+Z` 1;
            Reg := Reg s;
            Flag := fun f' =>
                if flag_eqb f f'
                then val
                else Flag s f';
            RAM := RAM s;
        |} ]}
    | Nop =>
        {[ {|
            PC := PC s `+Z` 1;
            Reg := Reg s;
            Flag := Flag s;
            RAM := RAM s;
        |} ]}
    end.


(*|

===================
Part 3: Correctness
===================

The language is defined.
But for this to mean anything, we need to relate it back to the 6502.

To start, let's assign to each 6502 opcode its corresponding instruction in our language.

|*)

Local Notation Zpg0 := (Zpg None).
Local Notation ZpgX := (Zpg (Some X)).
Local Notation ZpgY := (Zpg (Some Y)).
Local Notation Abs0 := (Abs None).
Local Notation AbsX := (Abs (Some X)).
Local Notation AbsY := (Abs (Some Y)).
Local Notation RegA := (RegMode A).
Local Notation RegX := (RegMode X).
Local Notation RegY := (RegMode Y).

Local Coercion MemMode : mem_mode >-> mode.

Definition parse_instr (opcode : bv 8) : option instr :=
    match opcode with
    (* ......01 *)
    | 0x01 => Some (Typical RegA (Binop Or XInd) true)
    | 0x05 => Some (Typical RegA (Binop Or Zpg0) true)
    | 0x09 => Some (Typical RegA (Binop Or Imm ) true)
    | 0x0d => Some (Typical RegA (Binop Or Abs0) true)
    | 0x11 => Some (Typical RegA (Binop Or IndY) true)
    | 0x15 => Some (Typical RegA (Binop Or ZpgX) true)
    | 0x19 => Some (Typical RegA (Binop Or AbsY) true)
    | 0x1d => Some (Typical RegA (Binop Or AbsX) true)

    | 0x21 => Some (Typical RegA (Binop And XInd) true)
    | 0x25 => Some (Typical RegA (Binop And Zpg0) true)
    | 0x29 => Some (Typical RegA (Binop And Imm ) true)
    | 0x2d => Some (Typical RegA (Binop And Abs0) true)
    | 0x31 => Some (Typical RegA (Binop And IndY) true)
    | 0x35 => Some (Typical RegA (Binop And ZpgX) true)
    | 0x39 => Some (Typical RegA (Binop And AbsY) true)
    | 0x3d => Some (Typical RegA (Binop And AbsX) true)

    | 0x41 => Some (Typical RegA (Binop Xor XInd) true)
    | 0x45 => Some (Typical RegA (Binop Xor Zpg0) true)
    | 0x49 => Some (Typical RegA (Binop Xor Imm ) true)
    | 0x4d => Some (Typical RegA (Binop Xor Abs0) true)
    | 0x51 => Some (Typical RegA (Binop Xor IndY) true)
    | 0x55 => Some (Typical RegA (Binop Xor ZpgX) true)
    | 0x59 => Some (Typical RegA (Binop Xor AbsY) true)
    | 0x5d => Some (Typical RegA (Binop Xor AbsX) true)

    | 0x61 => Some (Typical RegA (Binop Adc XInd) true)
    | 0x65 => Some (Typical RegA (Binop Adc Zpg0) true)
    | 0x69 => Some (Typical RegA (Binop Adc Imm ) true)
    | 0x6d => Some (Typical RegA (Binop Adc Abs0) true)
    | 0x71 => Some (Typical RegA (Binop Adc IndY) true)
    | 0x75 => Some (Typical RegA (Binop Adc ZpgX) true)
    | 0x79 => Some (Typical RegA (Binop Adc AbsY) true)
    | 0x7d => Some (Typical RegA (Binop Adc AbsX) true)

    | 0x81 => Some (Typical XInd (Binop Mov RegA) false)
    | 0x85 => Some (Typical Zpg0 (Binop Mov RegA) false)
    | 0x8d => Some (Typical Abs0 (Binop Mov RegA) false)
    | 0x91 => Some (Typical IndY (Binop Mov RegA) false)
    | 0x95 => Some (Typical ZpgX (Binop Mov RegA) false)
    | 0x99 => Some (Typical AbsY (Binop Mov RegA) false)
    | 0x9d => Some (Typical AbsX (Binop Mov RegA) false)

    | 0xa1 => Some (Typical RegA (Binop Mov XInd) true)
    | 0xa5 => Some (Typical RegA (Binop Mov Zpg0) true)
    | 0xa9 => Some (Typical RegA (Binop Mov Imm ) true)
    | 0xad => Some (Typical RegA (Binop Mov Abs0) true)
    | 0xb1 => Some (Typical RegA (Binop Mov IndY) true)
    | 0xb5 => Some (Typical RegA (Binop Mov ZpgX) true)
    | 0xb9 => Some (Typical RegA (Binop Mov AbsY) true)
    | 0xbd => Some (Typical RegA (Binop Mov AbsX) true)

    | 0xc1 => Some (Typical RegA (Binop Cmp XInd) true)
    | 0xc5 => Some (Typical RegA (Binop Cmp Zpg0) true)
    | 0xc9 => Some (Typical RegA (Binop Cmp Imm ) true)
    | 0xcd => Some (Typical RegA (Binop Cmp Abs0) true)
    | 0xd1 => Some (Typical RegA (Binop Cmp IndY) true)
    | 0xd5 => Some (Typical RegA (Binop Cmp ZpgX) true)
    | 0xd9 => Some (Typical RegA (Binop Cmp AbsY) true)
    | 0xdd => Some (Typical RegA (Binop Cmp AbsX) true)

    | 0xe1 => Some (Typical RegA (Binop Sbc XInd) true)
    | 0xe5 => Some (Typical RegA (Binop Sbc Zpg0) true)
    | 0xe9 => Some (Typical RegA (Binop Sbc Imm ) true)
    | 0xed => Some (Typical RegA (Binop Sbc Abs0) true)
    | 0xf1 => Some (Typical RegA (Binop Sbc IndY) true)
    | 0xf5 => Some (Typical RegA (Binop Sbc ZpgX) true)
    | 0xf9 => Some (Typical RegA (Binop Sbc AbsY) true)
    | 0xfd => Some (Typical RegA (Binop Sbc AbsX) true)

    (* ......10 *)
    | 0x06 => Some (Typical Zpg0 (ShiftL false) true)
    | 0x0a => Some (Typical RegA (ShiftL false) true)
    | 0x0e => Some (Typical Abs0 (ShiftL false) true)
    | 0x16 => Some (Typical ZpgX (ShiftL false) true)
    | 0x1e => Some (Typical AbsX (ShiftL false) true)

    | 0x26 => Some (Typical Zpg0 (ShiftL true) true)
    | 0x2a => Some (Typical RegA (ShiftL true) true)
    | 0x2e => Some (Typical Abs0 (ShiftL true) true)
    | 0x36 => Some (Typical ZpgX (ShiftL true) true)
    | 0x3e => Some (Typical AbsX (ShiftL true) true)

    | 0x46 => Some (Typical Zpg0 (ShiftR false) true)
    | 0x4a => Some (Typical RegA (ShiftR false) true)
    | 0x4e => Some (Typical Abs0 (ShiftR false) true)
    | 0x56 => Some (Typical ZpgX (ShiftR false) true)
    | 0x5e => Some (Typical AbsX (ShiftR false) true)

    | 0x66 => Some (Typical Zpg0 (ShiftR true) true)
    | 0x6a => Some (Typical RegA (ShiftR true) true)
    | 0x6e => Some (Typical Abs0 (ShiftR true) true)
    | 0x76 => Some (Typical ZpgX (ShiftR true) true)
    | 0x7e => Some (Typical AbsX (ShiftR true) true)

    | 0x86 => Some (Typical Zpg0 (Binop Mov RegX) false)
    | 0x8a => Some (Typical RegA (Binop Mov RegX) true)
    | 0x8e => Some (Typical Abs0 (Binop Mov RegX) false)
    | 0x96 => Some (Typical ZpgY (Binop Mov RegX) false)
    | 0x9a => Some (Typical (RegMode SP) (Binop Mov RegX) false)

    | 0xa2 => Some (Typical RegX (Binop Mov Imm ) true)
    | 0xa6 => Some (Typical RegX (Binop Mov Zpg0) true)
    | 0xaa => Some (Typical RegX (Binop Mov RegA) true)
    | 0xae => Some (Typical RegX (Binop Mov Abs0) true)
    | 0xb6 => Some (Typical RegX (Binop Mov ZpgY) true)
    | 0xba => Some (Typical RegX (Binop Mov (RegMode SP)) true)
    | 0xbe => Some (Typical RegX (Binop Mov AbsY) true)

    | 0xc6 => Some (Typical Zpg0 Dec true)
    | 0xca => Some (Typical RegX Dec true)
    | 0xce => Some (Typical Abs0 Dec true)
    | 0xd6 => Some (Typical ZpgX Dec true)
    | 0xde => Some (Typical AbsX Dec true)

    | 0xe6 => Some (Typical Zpg0 Inc true)
    | 0xea => Some Nop
    | 0xee => Some (Typical Abs0 Inc true)
    | 0xf6 => Some (Typical ZpgX Inc true)
    | 0xfe => Some (Typical AbsX Inc true)

    (* .....100 *)
    | 0x24 => Some (Typical RegA (Binop Bit Zpg0) true)
    | 0x2c => Some (Typical RegA (Binop Bit Abs0) true)

    | 0x4c => Some (Control Jmp)

    | 0x84 => Some (Typical Zpg0 (Binop Mov RegY) false)
    | 0x8c => Some (Typical Abs0 (Binop Mov RegY) false)
    | 0x94 => Some (Typical ZpgX (Binop Mov RegY) false)
    | 0x98 => Some (Typical RegA (Binop Mov RegY) true)

    | 0xa4 => Some (Typical RegY (Binop Mov Zpg0) true)
    | 0xac => Some (Typical RegY (Binop Mov Abs0) true)
    | 0xb4 => Some (Typical RegY (Binop Mov ZpgX) true)
    | 0xbc => Some (Typical RegY (Binop Mov AbsX) true)

    | 0xc4 => Some (Typical RegY (Binop Cmp Zpg0) true)
    | 0xcc => Some (Typical RegY (Binop Cmp Abs0) true)

    | 0xe4 => Some (Typical RegX (Binop Cmp Zpg0) true)
    | 0xec => Some (Typical RegX (Binop Cmp Abs0) true)

    (* ...0.000 *)
    | 0x20 => Some (Control Jsr)

    | 0x60 => Some (Control Rts)

    | 0x88 => Some (Typical RegY Dec true)

    | 0xa0 => Some (Typical RegY (Binop Mov Imm ) true)
    | 0xa8 => Some (Typical RegY (Binop Mov RegA) true)

    | 0xc0 => Some (Typical RegY (Binop Cmp Imm ) true)
    | 0xc8 => Some (Typical RegY Inc true)

    | 0xe0 => Some (Typical RegX (Binop Cmp Imm ) true)
    | 0xe8 => Some (Typical RegX Inc true)

    (* ...11000 *)
    | 0x18 => Some (SetFlag spec.C false)
    | 0x38 => Some (SetFlag spec.C true)
    | 0x58 => Some (SetFlag spec.I false)
    | 0x78 => Some (SetFlag spec.I true)
    | 0xb8 => Some (SetFlag spec.V false)
    | 0xd8 => Some (SetFlag spec.D false)
    | 0xf8 => Some (SetFlag spec.D true)

    (* ...10000 *)
    | 0x10 => Some (Control (Branch spec.N false))
    | 0x30 => Some (Control (Branch spec.N true))
    | 0x50 => Some (Control (Branch spec.V false))
    | 0x70 => Some (Control (Branch spec.V true))
    | 0x90 => Some (Control (Branch spec.C false))
    | 0xb0 => Some (Control (Branch spec.C true))
    | 0xd0 => Some (Control (Branch spec.Z false))
    | 0xf0 => Some (Control (Branch spec.Z true))

    | _ => None
    end.


(*|

Now, I claim if an opcode corresponds to an instruction,
the instruction's behavior faithfully represents the opcode's.

The rest of this file is a proof of this fact.

|*)

From Coq Require Import FunctionalExtensionality.

Fact can_always_fetch s addr : exists w, w ∈ fetch s addr.
Proof.
    set_unfold.
    rewrite /spec.fetch.
    case (bit 12 addr).
    by eexists.
    case (negb (bit 7 addr) || bit 9 addr).
    by exists inhabitant.
    by eexists.
Qed.



(* Theorems relating `mem_mode`s, as defined in this file,
to `mem_addressing_mode`s, as defined in `spec/Main.v`. *)
Theorem immediate_mode s addr :
    immediate s addr -> MemLoc addr ∈ mode_loc s Imm.
Proof.
    move=>->.
    eexists; split; last reflexivity.
    reflexivity.
Qed.
Theorem absolute_mode s addr :
    absolute s addr -> MemLoc addr ∈ mode_loc s Abs0.
Proof.
    move=> [w1 [w2 [fetch_w1 [fetch_w2 ->]]]].
    eexists; split; first reflexivity.
    eexists; split; first reflexivity.
    eexists; split; last exact fetch_w1.
    eexists; split; last exact fetch_w2.
    reflexivity.
Qed.
Theorem absolute_x_mode s addr :
    absolute_x s addr -> MemLoc addr ∈ mode_loc s AbsX.
Proof.
    move=> [w1 [w2 [fetch_w1 [fetch_w2 ->]]]].
    eexists; split; first reflexivity.
    eexists; split; first reflexivity.
    eexists; split; last exact fetch_w1.
    eexists; split; last exact fetch_w2.
    reflexivity.
Qed.
Theorem absolute_y_mode s addr :
    absolute_y s addr -> MemLoc addr ∈ mode_loc s AbsY.
Proof.
    move=> [w1 [w2 [fetch_w1 [fetch_w2 ->]]]].
    eexists; split; first reflexivity.
    eexists; split; first reflexivity.
    eexists; split; last exact fetch_w1.
    eexists; split; last exact fetch_w2.
    reflexivity.
Qed.
Theorem zero_page_mode s addr :
    zero_page s addr -> MemLoc addr ∈ mode_loc s Zpg0.
Proof.
    move=> [w [fetch_w ->]].
    eexists; split; first reflexivity.
    eexists; split; first reflexivity.
    exact fetch_w.
Qed.
Theorem zero_page_x_mode s addr :
    zero_page_x s addr -> MemLoc addr ∈ mode_loc s ZpgX.
Proof.
    move=> [w [fetch_w ->]].
    eexists; split; first reflexivity.
    eexists; split; first reflexivity.
    exact fetch_w.
Qed.
Theorem zero_page_y_mode s addr :
    zero_page_y s addr -> MemLoc addr ∈ mode_loc s ZpgY.
Proof.
    move=> [w [fetch_w ->]].
    eexists; split; first reflexivity.
    eexists; split; first reflexivity.
    exact fetch_w.
Qed.
Theorem indirect_x_mode s addr :
    indirect_x s addr -> MemLoc addr ∈ mode_loc s XInd.
Proof.
    move=> [w [w1 [w2 [fetch_w [fetch_w1 [fetch_w2 ->]]]]]].
    eexists; split; first reflexivity.
    eexists; split; last exact fetch_w.
    eexists; split; last exact fetch_w1.
    eexists; split; last exact fetch_w2.
    reflexivity.
Qed.
Theorem indirect_y_mode s addr :
    indirect_y s addr -> MemLoc addr ∈ mode_loc s IndY.
Proof.
    move=> [w [w1 [w2 [fetch_w [fetch_w1 [fetch_w2 ->]]]]]].
    eexists; split; first reflexivity.
    eexists; split; last exact fetch_w.
    eexists; split; first reflexivity.
    eexists; split; last exact fetch_w1.
    eexists; split; last exact fetch_w2.
    reflexivity.
Qed.





Lemma run_SetFlag s1 s2 f val :
    flag_instr s1 s2 f val -> s2 ∈ run_instr (SetFlag f val) s1.
Proof.
    rewrite /flag_instr.
    destruct s2; simpl.
    by move=> [-> [-> [-> ->]]].
Qed.

Lemma run_transfer s1 s2 r1 r2 :
    transfer_instr s1 s2 r1 r2 ->
    s2 ∈ run_instr (Typical (RegMode r2) (Binop Mov (RegMode r1)) true) s1.
Proof.
    rewrite /transfer_instr.
    destruct s2; simpl.
    move=> [-> [-> [-> ->]]].
    eexists; split; last reflexivity.
    eexists; split; last reflexivity.
    eexists (_,_,_); split.
    2: {
        eexists; split; last reflexivity.
        eexists; split; last reflexivity.
        reflexivity.
    }
    set_unfold.
    f_equal.
    by apply functional_extensionality; case.
Qed.

Lemma run_store s1 s2 r mode (mode' : mem_mode) len :
    len = Z.of_nat (S (mode_len mode')) ->
    store_instr s1 s2 r mode len ->
    (forall addr, mode s1 addr -> MemLoc addr ∈ mode_loc s1 mode') ->
    s2 ∈ run_instr (Typical mode' (Binop Mov (RegMode r)) false) s1.
Proof.
    move=> -> H mode_spec; move: H.
    rewrite /store_instr.
    destruct s2; simpl.
    move => [addr [/mode_spec m [-> [-> [-> ->]]]]].
    eexists; split; last exact m.
    move: (can_always_fetch s1 addr) => [? tmp];
        eexists; split; last exact tmp.
    eexists (_,_,_); split.
    2: {
        eexists; split; last reflexivity.
        eexists; split; last reflexivity.
        reflexivity.
    }
    set_unfold.
    f_equal.
    - by apply functional_extensionality; case.
    - by case mode'.
Qed.

Lemma run_load s1 s2 r mode (mode' : mem_mode) len :
    len = Z.of_nat (S (mode_len mode')) ->
    load_instr s1 s2 r mode len ->
    (forall addr, mode s1 addr -> MemLoc addr ∈ mode_loc s1 mode') ->
    s2 ∈ run_instr (Typical (RegMode r) (Binop Mov mode') true) s1.
Proof.
    move=> -> H mode_spec; move: H.
    rewrite /load_instr.
    destruct s2; simpl.
    move=> [addr [w [/mode_spec m [fetch_w [-> [-> [-> ->]]]]]]].
    eexists; split; last reflexivity.
    eexists; split; last reflexivity.
    eexists (_,_,_); split.
    2: {
        eexists; split; last exact m.
        eexists; split; last exact fetch_w.
        reflexivity.
    }
    set_unfold.
    f_equal.
    by apply functional_extensionality; case.
Qed.

Lemma run_Or s1 s2 mode (mode' : mem_mode) len :
    len = Z.of_nat (S (mode_len mode')) ->
    logic_instr s1 s2 bv_or mode len ->
    (forall addr, mode s1 addr -> MemLoc addr ∈ mode_loc s1 mode') ->
    s2 ∈ run_instr (Typical RegA (Binop Or mode') true) s1.
Proof.
    move=> -> H mode_spec; move: H.
    rewrite /logic_instr.
    destruct s2; simpl.
    move=> [addr' [w [/mode_spec m [fetch_w [-> [-> [-> ->]]]]]]].
    eexists; split; last reflexivity.
    eexists; split; last reflexivity.
    eexists; split.
    2: {
        eexists; split; last exact m.
        eexists; split; last exact fetch_w.
        reflexivity.
    }
    set_unfold.
    f_equal.
    by apply functional_extensionality; case.
Qed.
Lemma run_And s1 s2 mode (mode' : mem_mode) len :
    len = Z.of_nat (S (mode_len mode')) ->
    logic_instr s1 s2 bv_and mode len ->
    (forall addr, mode s1 addr -> MemLoc addr ∈ mode_loc s1 mode') ->
    s2 ∈ run_instr (Typical RegA (Binop And mode') true) s1.
Proof.
    move=> -> H mode_spec; move: H.
    rewrite /logic_instr.
    destruct s2; simpl.
    move=> [addr' [w [/mode_spec m [fetch_w [-> [-> [-> ->]]]]]]].
    eexists; split; last reflexivity.
    eexists; split; last reflexivity.
    eexists; split.
    2: {
        eexists; split; last exact m.
        eexists; split; last exact fetch_w.
        reflexivity.
    }
    set_unfold.
    f_equal.
    by apply functional_extensionality; case.
Qed.
Lemma run_Xor s1 s2 mode (mode' : mem_mode) len :
    len = Z.of_nat (S (mode_len mode')) ->
    logic_instr s1 s2 bv_xor mode len ->
    (forall addr, mode s1 addr -> MemLoc addr ∈ mode_loc s1 mode') ->
    s2 ∈ run_instr (Typical RegA (Binop Xor mode') true) s1.
Proof.
    move=> -> H mode_spec; move: H.
    rewrite /logic_instr.
    destruct s2; simpl.
    move=> [addr' [w [/mode_spec m [fetch_w [-> [-> [-> ->]]]]]]].
    eexists; split; last reflexivity.
    eexists; split; last reflexivity.
    eexists; split.
    2: {
        eexists; split; last exact m.
        eexists; split; last exact fetch_w.
        reflexivity.
    }
    set_unfold.
    f_equal.
    by apply functional_extensionality; case.
Qed.
Lemma run_Bit s1 s2 mode (mode' : mem_mode) len :
    len = Z.of_nat (S (mode_len mode')) ->
    BIT_mode s1 s2 mode len ->
    (forall addr, mode s1 addr -> MemLoc addr ∈ mode_loc s1 mode') ->
    s2 ∈ run_instr (Typical RegA (Binop Bit mode') true) s1.
Proof.
    move=> -> H mode_spec; move: H.
    rewrite /BIT_mode.
    destruct s2; simpl.
    move=> [addr' [w [/mode_spec m [fetch_w [-> [-> [-> ->]]]]]]].
    eexists; split; last reflexivity.
    eexists; split; last reflexivity.
    eexists (_,_,_); split.
    2: {
        eexists; split; last exact m.
        eexists; split; last exact fetch_w.
        reflexivity.
    }
    set_unfold.
    f_equal.
    by apply functional_extensionality; case.
Qed.


Lemma run_Adc s1 s2 mode (mode' : mem_mode) len :
    len = Z.of_nat (S (mode_len mode')) ->
    ADC_mode s1 s2 mode len ->
    (forall addr, mode s1 addr -> MemLoc addr ∈ mode_loc s1 mode') ->
    s2 ∈ run_instr (Typical RegA (Binop Adc mode') true) s1.
Proof.
    move=> -> H mode_spec; move: H.

    have [d d_def]: exists d, d = Flag s1 D by exists (Flag s1 D).
    rewrite /ADC_mode -d_def; case: d d_def => d_def.
    - destruct s2; simpl.
        move=> [addr' [w_in [w_out [c_out [v [/mode_spec m [fetch_w_in [is_dec_Adc [-> [-> [-> ->]]]]]]]]]]].
        eexists; split; last reflexivity.
        eexists; split; last reflexivity.
        eexists (_,_,_); split.
        2: {
            eexists; split; last exact m.
            eexists; split; last exact fetch_w_in.
            rewrite -d_def.
            exists v; split; last done.
            exists (w_out,c_out); split; last exact is_dec_Adc.
            reflexivity.
        }
        done.
    - destruct s2; simpl.
        move=> [addr' [w_in [/mode_spec m [fetch_w_in tmp]]]]; move: tmp.
        move=> [-> [-> [-> ->]]].
        eexists; split; last reflexivity.
        eexists; split; last reflexivity.
        eexists (_,_,_); split.
        2: {
            eexists; split; last exact m.
            eexists; split; last exact fetch_w_in.
            rewrite -d_def.
            reflexivity.
        }
        done.
Qed.
Lemma run_Sbc s1 s2 mode (mode' : mem_mode) len :
    len = Z.of_nat (S (mode_len mode')) ->
    SBC_mode s1 s2 mode len ->
    (forall addr, mode s1 addr -> MemLoc addr ∈ mode_loc s1 mode') ->
    s2 ∈ run_instr (Typical RegA (Binop Sbc mode') true) s1.
Proof.
    move=> -> H mode_spec; move: H.

    have [d d_def]: exists d, d = Flag s1 D by exists (Flag s1 D).
    rewrite /SBC_mode -d_def; case: d d_def => d_def.
    - destruct s2; simpl.
        move=> [addr' [w_in [w_out [c_out [v [/mode_spec m [fetch_w_in [is_dec_Adc [-> [-> [-> ->]]]]]]]]]]].
        eexists; split; last reflexivity.
        eexists; split; last reflexivity.
        eexists (_,_,_); split.
        2: {
            eexists; split; last exact m.
            eexists; split; last exact fetch_w_in.
            rewrite -d_def.
            exists v; split; last done.
            exists (w_out,c_out); split; last exact is_dec_Adc.
            reflexivity.
        }
        done.
    - destruct s2; simpl.
        move=> [addr' [w_in [/mode_spec m [fetch_w_in tmp]]]]; move: tmp.
        move=> [-> [-> [-> ->]]].
        eexists; split; last reflexivity.
        eexists; split; last reflexivity.
        eexists (_,_,_); split.
        2: {
            eexists; split; last exact m.
            eexists; split; last exact fetch_w_in.
            rewrite -d_def.
            reflexivity.
        }
        done.
Qed.

Lemma run_Cmp s1 s2 r mode (mode' : mem_mode) len :
    len = Z.of_nat (S (mode_len mode')) ->
    CMP_mode s1 s2 r mode len ->
    (forall addr, mode s1 addr -> MemLoc addr ∈ mode_loc s1 mode') ->
    s2 ∈ run_instr (Typical (RegMode r) (Binop Cmp mode') true) s1.
Proof.
    move=> -> H mode_spec; move: H.
    rewrite /CMP_mode.
    destruct s2; simpl.
    move=> [addr' [w_in [/mode_spec m [fetch_w_in tmp]]]]; move: tmp.
    move=> [-> [-> [-> ->]]].
    eexists; split; last reflexivity.
    eexists; split; last reflexivity.
    eexists (_,_,_); split.
    2: {
        eexists; split; last exact m.
        eexists; split; last exact fetch_w_in.
        reflexivity.
    }
    set_unfold.
    f_equal.
    by apply functional_extensionality; case.
Qed.


Lemma run_Shift (right roll : bool) s1 s2 mode (mode' : mem_mode) len :
    len = Z.of_nat (S (mode_len mode')) ->
    @shift_instr_mode s1 s2
        (if right
        then (if roll then ROR_spec else LSR_spec)
        else (if roll then ROL_spec else ASL_spec))
    mode len ->
    (forall addr, mode s1 addr -> MemLoc addr ∈ mode_loc s1 mode') ->
    s2 ∈ run_instr (Typical mode' ((if right then ShiftR else ShiftL) roll) true) s1.
Proof.
    move=> -> H mode_spec; move: H.
    rewrite /shift_instr_mode.
    destruct s2; simpl.
    move=> [addr' [w_in [c_out [w_out [/mode_spec m [fetch_w_in [is_shift [-> [-> [-> ->]]]]]]]]]].
    eexists; split; last exact m.
    eexists; split; last exact fetch_w_in.
    eexists (_,_,_); split.
    2: {
        rewrite /run_operation.
        move: is_shift; case: right; case: roll; move=> is_shift;
            (eexists; split; [reflexivity | exact is_shift]).
    }
    set_unfold.
    f_equal.
    - by rewrite Tauto.if_same.
    - by apply functional_extensionality; case.
    - by case mode'; case right.
Qed.
Lemma run_Shift_A (right roll : bool) s1 s2 :
    @shift_instr_A s1 s2
        (if right
        then (if roll then ROR_spec else LSR_spec)
        else (if roll then ROL_spec else ASL_spec)) ->
    s2 ∈ run_instr (Typical RegA ((if right then ShiftR else ShiftL) roll) true) s1.
Proof.
    rewrite /shift_instr_A.
    destruct s2; simpl.
    move=> [addr' [w [is_shift [-> [-> [-> ->]]]]]].
    eexists; split; last reflexivity.
    eexists; split; last reflexivity.
    eexists (_,_,_); split.
    2: {
        rewrite /run_operation.
        move: is_shift; case: right; case: roll; move=> is_shift;
            (eexists; split; [reflexivity | exact is_shift]).
    }
    set_unfold.
    f_equal.
    - move: is_shift; by case right.
    - by apply functional_extensionality; case.
    - by case right.
Qed.

Lemma run_Inc_mode s1 s2 mode (mode' : mem_mode) len :
    len = Z.of_nat (S (mode_len mode')) ->
    INC_mode s1 s2 mode len ->
    (forall addr, mode s1 addr -> MemLoc addr ∈ mode_loc s1 mode') ->
    s2 ∈ run_instr (Typical mode' Inc true) s1.
Proof.
    move=> -> H mode_spec; move: H.
    rewrite /INC_mode.
    destruct s2; simpl.
    move=> [addr' [w [/mode_spec m [fetch_w [-> [-> [-> ->]]]]]]].
    eexists; split; last exact m.
    eexists; split; last exact fetch_w.
    eexists; split; last reflexivity.
    set_unfold.
    f_equal.
    - by apply functional_extensionality; case.
    - by case mode'.
Qed.
Lemma run_Inc_reg s1 s2 r :
    INC_reg s1 s2 r ->
    s2 ∈ run_instr (Typical (RegMode r) Inc true) s1.
Proof.
    rewrite /INC_reg.
    destruct s2; simpl.
    move=> [-> [-> [-> ->]]].
    eexists; split; last reflexivity.
    eexists; split; last reflexivity.
    eexists; split; last reflexivity.
    set_unfold.
    f_equal.
    by apply functional_extensionality; case.
Qed.

Lemma run_Dec_mode s1 s2 mode (mode' : mem_mode) len :
    len = Z.of_nat (S (mode_len mode')) ->
    DEC_mode s1 s2 mode len ->
    (forall addr, mode s1 addr -> MemLoc addr ∈ mode_loc s1 mode') ->
    s2 ∈ run_instr (Typical mode' Dec true) s1.
Proof.
    move=> -> H mode_spec; move: H.
    rewrite /DEC_mode.
    destruct s2; simpl.
    move=> [addr' [w [/mode_spec m [fetch_w [-> [-> [-> ->]]]]]]].
    eexists; split; last exact m.
    eexists; split; last exact fetch_w.
    eexists; split; last reflexivity.
    set_unfold.
    f_equal.
    - by apply functional_extensionality; case.
    - by case mode'.
Qed.
Lemma run_Dec_reg s1 s2 r :
    DEC_reg s1 s2 r ->
    s2 ∈ run_instr (Typical (RegMode r) Dec true) s1.
Proof.
    rewrite /DEC_reg.
    destruct s2; simpl.
    move=> [-> [-> [-> ->]]].
    eexists; split; last reflexivity.
    eexists; split; last reflexivity.
    eexists; split; last reflexivity.
    set_unfold.
    f_equal.
    by apply functional_extensionality; case.
Qed.


Lemma run_Branch s1 s2 f (val : bool) :
    branch_instr s1 s2
        (if val
        then (fun s => Flag s f)
        else (fun s => negb (Flag s f))) ->
    s2 ∈ run_instr (Control (Branch f val)) s1.
Proof.
    rewrite /branch_instr.
    destruct s2; simpl.
    move=> [dist [fetch_dist [-> [-> [-> ->]]]]].
    case (decide (spec.Flag s1 f = val)) as [eq|neq].
    - eexists; split; first reflexivity.
        eexists; split; last exact fetch_dist.
        move: eq; case val; move=> ->; reflexivity.
    - set_unfold.
        f_equal.
        move: neq.
        by case val; case: (spec.Flag s1 f).
Qed.

From theories Require Import utils.

Theorem run_instr_spec opcode :
    match parse_instr opcode with
    | None => True
    | Some i => forall s1 s2,
        instruction s1 s2 opcode -> s2 ∈ run_instr i s1
    end.
Proof.
    rewrite -(bv_of_byte_of_bv opcode) bv_of_byte_speedup.
    case (byte_of_bv opcode); set tmp := (parse_instr _); simpl in tmp; rewrite /tmp.

    (* 0 *)
    - trivial.
    - by intros; eapply run_Or; [reflexivity | eapply ORA_indirect_x | apply indirect_x_mode].
    - trivial.
    - trivial.
    - trivial.
    - by intros; eapply run_Or; [reflexivity | eapply ORA_zero_page | apply zero_page_mode].
    - by intros; eapply (run_Shift false false); [reflexivity | eapply ASL_zero_page | apply zero_page_mode].
    - trivial.
    - trivial.
    - by intros; eapply run_Or; [reflexivity | eapply ORA_immediate | apply immediate_mode].
    - by intros; eapply (run_Shift_A false false); eapply ASL_A.
    - trivial.
    - trivial.
    - by intros; eapply run_Or; [reflexivity | eapply ORA_absolute | apply absolute_mode].
    - by intros; eapply (run_Shift false false); [reflexivity | eapply ASL_absolute | apply absolute_mode].
    - trivial.

    (* 1 *)
    - by intros; eapply run_Branch; eapply BPL.
    - by intros; eapply run_Or; [reflexivity | eapply ORA_indirect_y | apply indirect_y_mode].
    - trivial.
    - trivial.
    - trivial.
    - by intros; eapply run_Or; [reflexivity | eapply ORA_zero_page_x | apply zero_page_x_mode].
    - by intros; eapply (run_Shift false false); [reflexivity | eapply ASL_zero_page_x | apply zero_page_x_mode].
    - trivial.
    - by intros; eapply run_SetFlag; eapply CLC.
    - by intros; eapply run_Or; [reflexivity | eapply ORA_absolute_y | apply absolute_y_mode].
    - trivial.
    - trivial.
    - trivial.
    - by intros; eapply run_Or; [reflexivity | eapply ORA_absolute_x | apply absolute_x_mode].
    - by intros; eapply (run_Shift false false); [reflexivity | eapply ASL_absolute_x | apply absolute_x_mode].
    - trivial.

    (* 2 *)
    - move=> s1 [? ? ? ?] /JSR H; specialize (H eq_refl); simpl in H; move: H => [pc [/absolute_mode [? [eq m]] [-> [-> [-> ->]]]]].
        eexists; split; last exact m.
        set_unfold.
        f_equal.
        + by apply functional_extensionality; case.
        + by inversion eq.
    - by intros; eapply run_And; [reflexivity | eapply AND_indirect_x | apply indirect_x_mode].
    - trivial.
    - trivial.
    - by intros; eapply run_Bit; [reflexivity | eapply BIT_zero_page | apply zero_page_mode].
    - by intros; eapply run_And; [reflexivity | eapply AND_zero_page | apply zero_page_mode].
    - by intros; eapply (run_Shift false true); [reflexivity | eapply ROL_zero_page | apply zero_page_mode].
    - trivial.
    - trivial.
    - by intros; eapply run_And; [reflexivity | eapply AND_immediate | apply immediate_mode].
    - by intros; eapply (run_Shift_A false true); eapply ROL_A.
    - trivial.
    - by intros; eapply run_Bit; [reflexivity | eapply BIT_absolute | apply absolute_mode].
    - by intros; eapply run_And; [reflexivity | eapply AND_absolute | apply absolute_mode].
    - by intros; eapply (run_Shift false true); [reflexivity | eapply ROL_absolute | apply absolute_mode].
    - trivial.

    (* 3 *)
    - by intros; eapply run_Branch; eapply BMI.
    - by intros; eapply run_And; [reflexivity | eapply AND_indirect_y | apply indirect_y_mode].
    - trivial.
    - trivial.
    - trivial.
    - by intros; eapply run_And; [reflexivity | eapply AND_zero_page_x | apply zero_page_x_mode].
    - by intros; eapply (run_Shift false true); [reflexivity | eapply ROL_zero_page_x | apply zero_page_x_mode].
    - trivial.
    - by intros; eapply run_SetFlag; eapply SEC.
    - by intros; eapply run_And; [reflexivity | eapply AND_absolute_y | apply absolute_y_mode].
    - trivial.
    - trivial.
    - trivial.
    - by intros; eapply run_And; [reflexivity | eapply AND_absolute_x | apply absolute_x_mode].
    - by intros; eapply (run_Shift false true); [reflexivity | eapply ROL_absolute_x | apply absolute_x_mode].
    - trivial.

    (* 4 *)
    - trivial.
    - by intros; eapply run_Xor; [reflexivity | eapply EOR_indirect_x | apply indirect_x_mode].
    - trivial.
    - trivial.
    - trivial.
    - by intros; eapply run_Xor; [reflexivity | eapply EOR_zero_page | apply zero_page_mode].
    - by intros; eapply (run_Shift true false); [reflexivity | eapply LSR_zero_page | apply zero_page_mode].
    - trivial.
    - trivial.
    - by intros; eapply run_Xor; [reflexivity | eapply EOR_immediate | apply immediate_mode].
    - by intros; eapply (run_Shift_A true false); eapply LSR_A.
    - trivial.
    - move=> s1 [? ? ? ?] /JMP H; specialize (H eq_refl); simpl in H; move: H => [pc [/absolute_mode [? [eq m]] [-> [-> [-> ->]]]]].
        eexists; split; last exact m.
        inversion eq.
        reflexivity.
    - by intros; eapply run_Xor; [reflexivity | eapply EOR_absolute | apply absolute_mode].
    - by intros; eapply (run_Shift true false); [reflexivity | eapply LSR_absolute | apply absolute_mode].
    - trivial.

    (* 5 *)
    - by intros; eapply run_Branch; eapply BVC.
    - by intros; eapply run_Xor; [reflexivity | eapply EOR_indirect_y | apply indirect_y_mode].
    - trivial.
    - trivial.
    - trivial.
    - by intros; eapply run_Xor; [reflexivity | eapply EOR_zero_page_x | apply zero_page_x_mode].
    - by intros; eapply (run_Shift true false); [reflexivity | eapply LSR_zero_page_x | apply zero_page_x_mode].
    - trivial.
    - by intros; eapply run_SetFlag; eapply CLI.
    - by intros; eapply run_Xor; [reflexivity | eapply EOR_absolute_y | apply absolute_y_mode].
    - trivial.
    - trivial.
    - trivial.
    - by intros; eapply run_Xor; [reflexivity | eapply EOR_absolute_x | apply absolute_x_mode].
    - by intros; eapply (run_Shift true false); [reflexivity | eapply LSR_absolute_x | apply absolute_x_mode].
    - trivial.

    (* 6 *)
    - move=> s1 [? ? ? ?] /RTS H; specialize (H eq_refl); simpl in H; move: H => [w1 [w2 [fetch_w1 [fetch_w2 [-> [-> [-> ->]]]]]]].
        eexists; split.
        2: {
            eexists; split; last exact fetch_w1.
            eexists; split; last exact fetch_w2.
            reflexivity.
        }
        set_unfold.
        f_equal.
        by apply functional_extensionality; case.
    - by intros; eapply run_Adc; [reflexivity | eapply ADC_indirect_x | apply indirect_x_mode].
    - trivial.
    - trivial.
    - trivial.
    - by intros; eapply run_Adc; [reflexivity | eapply ADC_zero_page | apply zero_page_mode].
    - by intros; eapply (run_Shift true true); [reflexivity | eapply ROR_zero_page | apply zero_page_mode].
    - trivial.
    - trivial.
    - by intros; eapply run_Adc; [reflexivity | eapply ADC_immediate | apply immediate_mode].
    - by intros; eapply (run_Shift_A true true); eapply ROR_A.
    - trivial.
    - trivial.
    - by intros; eapply run_Adc; [reflexivity | eapply ADC_absolute | apply absolute_mode].
    - by intros; eapply (run_Shift true true); [reflexivity | eapply ROR_absolute | apply absolute_mode].
    - trivial.

    (* 7 *)
    - by intros; eapply run_Branch; eapply BVS.
    - by intros; eapply run_Adc; [reflexivity | eapply ADC_indirect_y | apply indirect_y_mode].
    - trivial.
    - trivial.
    - trivial.
    - by intros; eapply run_Adc; [reflexivity | eapply ADC_zero_page_x | apply zero_page_x_mode].
    - by intros; eapply (run_Shift true true); [reflexivity | eapply ROR_zero_page_x | apply zero_page_x_mode].
    - trivial.
    - by intros; eapply run_SetFlag; eapply SEI.
    - by intros; eapply run_Adc; [reflexivity | eapply ADC_absolute_y | apply absolute_y_mode].
    - trivial.
    - trivial.
    - trivial.
    - by intros; eapply run_Adc; [reflexivity | eapply ADC_absolute_x | apply absolute_x_mode].
    - by intros; eapply (run_Shift true true); [reflexivity | eapply ROR_absolute_x | apply absolute_x_mode].
    - trivial.

    (* 8 *)
    - trivial.
    - by intros; eapply run_store; [reflexivity | eapply STA_indirect_x | apply indirect_x_mode].
    - trivial.
    - trivial.
    - by intros; eapply run_store; [reflexivity | eapply STY_zero_page | apply zero_page_mode].
    - by intros; eapply run_store; [reflexivity | eapply STA_zero_page | apply zero_page_mode].
    - by intros; eapply run_store; [reflexivity | eapply STX_zero_page | apply zero_page_mode].
    - trivial.
    - by intros; eapply run_Dec_reg; eapply DEY.
    - trivial.
    - by intros; eapply run_transfer; eapply TXA.
    - trivial.
    - by intros; eapply run_store; [reflexivity | eapply STY_absolute | apply absolute_mode].
    - by intros; eapply run_store; [reflexivity | eapply STA_absolute | apply absolute_mode].
    - by intros; eapply run_store; [reflexivity | eapply STX_absolute | apply absolute_mode].
    - trivial.

    (* 9 *)
    - by intros; eapply run_Branch; eapply BCC.
    - by intros; eapply run_store; [reflexivity | eapply STA_indirect_y | apply indirect_y_mode].
    - trivial.
    - trivial.
    - by intros; eapply run_store; [reflexivity | eapply STY_zero_page_x | apply zero_page_x_mode].
    - by intros; eapply run_store; [reflexivity | eapply STA_zero_page_x | apply zero_page_x_mode].
    - by intros; eapply run_store; [reflexivity | eapply STX_zero_page_y | apply zero_page_y_mode].
    - trivial.
    - by intros; eapply run_transfer; eapply TYA.
    - by intros; eapply run_store; [reflexivity | eapply STA_absolute_y | apply absolute_y_mode].
    - move=> s1 [? ? ? ?] /TXS H; specialize (H eq_refl); simpl in H; move: H => [-> [-> [-> ->]]].
        eexists; split; last reflexivity.
        eexists; split; last reflexivity.
        eexists (_,_,_); split.
        2: {
            eexists; split; last reflexivity.
            eexists; split; last reflexivity.
            reflexivity.
        }
        set_unfold.
        f_equal.
        by apply functional_extensionality; case.
    - trivial.
    - trivial.
    - by intros; eapply run_store; [reflexivity | eapply STA_absolute_x | apply absolute_x_mode].
    - trivial.
    - trivial.

    (* A *)
    - by intros; eapply run_load; [reflexivity | eapply LDY_immediate | apply immediate_mode].
    - by intros; eapply run_load; [reflexivity | eapply LDA_indirect_x | apply indirect_x_mode].
    - by intros; eapply run_load; [reflexivity | eapply LDX_immediate | apply immediate_mode].
    - trivial.
    - by intros; eapply run_load; [reflexivity | eapply LDY_zero_page | apply zero_page_mode].
    - by intros; eapply run_load; [reflexivity | eapply LDA_zero_page | apply zero_page_mode].
    - by intros; eapply run_load; [reflexivity | eapply LDX_zero_page | apply zero_page_mode].
    - trivial.
    - by intros; eapply run_transfer; eapply TAY.
    - by intros; eapply run_load; [reflexivity | eapply LDA_immediate | apply immediate_mode].
    - by intros; eapply run_transfer; eapply TAX.
    - trivial.
    - by intros; eapply run_load; [reflexivity | eapply LDY_absolute | apply absolute_mode].
    - by intros; eapply run_load; [reflexivity | eapply LDA_absolute | apply absolute_mode].
    - by intros; eapply run_load; [reflexivity | eapply LDX_absolute | apply absolute_mode].
    - trivial.

    (* B *)
    - by intros; eapply run_Branch; eapply BCS.
    - by intros; eapply run_load; [reflexivity | eapply LDA_indirect_y | apply indirect_y_mode].
    - trivial.
    - trivial.
    - by intros; eapply run_load; [reflexivity | eapply LDY_zero_page_x | apply zero_page_x_mode].
    - by intros; eapply run_load; [reflexivity | eapply LDA_zero_page_x | apply zero_page_x_mode].
    - by intros; eapply run_load; [reflexivity | eapply LDX_zero_page_y | apply zero_page_y_mode].
    - trivial.
    - by intros; eapply run_SetFlag; eapply CLV.
    - by intros; eapply run_load; [reflexivity | eapply LDA_absolute_y | apply absolute_y_mode].
    - by intros; eapply run_transfer; eapply TSX.
    - trivial.
    - by intros; eapply run_load; [reflexivity | eapply LDY_absolute_x | apply absolute_x_mode].
    - by intros; eapply run_load; [reflexivity | eapply LDA_absolute_x | apply absolute_x_mode].
    - by intros; eapply run_load; [reflexivity | eapply LDX_absolute_y | apply absolute_y_mode].
    - trivial.

    (* C *)
    - by intros; eapply run_Cmp; [reflexivity | eapply CPY_immediate | apply immediate_mode].
    - by intros; eapply run_Cmp; [reflexivity | eapply CMP_indirect_x | apply indirect_x_mode].
    - trivial.
    - trivial.
    - by intros; eapply run_Cmp; [reflexivity | eapply CPY_zero_page | apply zero_page_mode].
    - by intros; eapply run_Cmp; [reflexivity | eapply CMP_zero_page | apply zero_page_mode].
    - by intros; eapply run_Dec_mode; [reflexivity | eapply DEC_zero_page | apply zero_page_mode].
    - trivial.
    - by intros; eapply run_Inc_reg; eapply INY.
    - by intros; eapply run_Cmp; [reflexivity | eapply CMP_immediate | apply immediate_mode].
    - by intros; eapply run_Dec_reg; eapply DEX.
    - trivial.
    - by intros; eapply run_Cmp; [reflexivity | eapply CPY_absolute | apply absolute_mode].
    - by intros; eapply run_Cmp; [reflexivity | eapply CMP_absolute | apply absolute_mode].
    - by intros; eapply run_Dec_mode; [reflexivity | eapply DEC_absolute | apply absolute_mode].
    - trivial.

    (* D *)
    - by intros; eapply run_Branch; eapply BNE.
    - by intros; eapply run_Cmp; [reflexivity | eapply CMP_indirect_y | apply indirect_y_mode].
    - trivial.
    - trivial.
    - trivial.
    - by intros; eapply run_Cmp; [reflexivity | eapply CMP_zero_page_x | apply zero_page_x_mode].
    - by intros; eapply run_Dec_mode; [reflexivity | eapply DEC_zero_page_x | apply zero_page_x_mode].
    - trivial.
    - by intros; eapply run_SetFlag; eapply CLD.
    - by intros; eapply run_Cmp; [reflexivity | eapply CMP_absolute_y | apply absolute_y_mode].
    - trivial.
    - trivial.
    - trivial.
    - by intros; eapply run_Cmp; [reflexivity | eapply CMP_absolute_x | apply absolute_x_mode].
    - by intros; eapply run_Dec_mode; [reflexivity | eapply DEC_absolute_x | apply absolute_x_mode].
    - trivial.

    (* E *)
    - by intros; eapply run_Cmp; [reflexivity | eapply CPX_immediate | apply immediate_mode].
    - by intros; eapply run_Sbc; [reflexivity | eapply SBC_indirect_x | apply indirect_x_mode].
    - trivial.
    - trivial.
    - by intros; eapply run_Cmp; [reflexivity | eapply CPX_zero_page | apply zero_page_mode].
    - by intros; eapply run_Sbc; [reflexivity | eapply SBC_zero_page | apply zero_page_mode].
    - by intros; eapply run_Inc_mode; [reflexivity | eapply INC_zero_page | apply zero_page_mode].
    - trivial.
    - by intros; eapply run_Inc_reg; eapply INX.
    - by intros; eapply run_Sbc; [reflexivity | eapply SBC_immediate | apply immediate_mode].
    - by move=> s1 [? ? ? ?] /NOP => H; specialize (H eq_refl); simpl in H; move: H => [-> [-> [-> ->]]].
    - trivial.
    - by intros; eapply run_Cmp; [reflexivity | eapply CPX_absolute | apply absolute_mode].
    - by intros; eapply run_Sbc; [reflexivity | eapply SBC_absolute | apply absolute_mode].
    - by intros; eapply run_Inc_mode; [reflexivity | eapply INC_absolute | apply absolute_mode].
    - trivial.

    (* F *)
    - by intros; eapply run_Branch; eapply BEQ.
    - by intros; eapply run_Sbc; [reflexivity | eapply SBC_indirect_y | apply indirect_y_mode].
    - trivial.
    - trivial.
    - trivial.
    - by intros; eapply run_Sbc; [reflexivity | eapply SBC_zero_page_x | apply zero_page_x_mode].
    - by intros; eapply run_Inc_mode; [reflexivity | eapply INC_zero_page_x | apply zero_page_x_mode].
    - trivial.
    - by intros; eapply run_SetFlag; eapply SED.
    - by intros; eapply run_Sbc; [reflexivity | eapply SBC_absolute_y | apply absolute_y_mode].
    - trivial.
    - trivial.
    - trivial.
    - by intros; eapply run_Sbc; [reflexivity | eapply SBC_absolute_x | apply absolute_x_mode].
    - by intros; eapply run_Inc_mode; [reflexivity | eapply INC_absolute_x | apply absolute_x_mode].
    - trivial.
Qed.

(* Thus the machine language has been upgraded to an assembly language.
The benefits are as follows:
- No longer do I have to deal with a hundred plus opcodes.
    The assembly instruction set, while not trivial, is a lot smaller.
- Control flow is decoupled from program behavior;
    it is trivial to extract the next PC value from `run_instr`.
- A structured language, even an assebly language,
    is the first step on the path to higher abstraction.
    And higher abstraction, done right, leads to a simpler description of the game.
*)
