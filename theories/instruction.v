From stdpp Require Import ssreflect unstable.bitvector unstable.bitvector_tactics.
From theories Require Import utils spec.

Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

Fact bv_inc_inc {n} (x : bv n) : (bv_add_Z (bv_add_Z x 1) 1 = bv_add_Z x 2)%Z.
Proof.
    bv_simplify.
    f_equal.
    lia.
Qed.


Local Open Scope bv_scope.

(* A location, either in a register or in memory. *)
Inductive loc := RegLoc : reg -> loc | MemLoc : bv 16 -> loc.
Definition read (s : state) (l : loc) (w : bv 8) : Prop :=
    match l with RegLoc r => w = Reg s r | MemLoc addr => fetch s addr w end.
Definition write (s : state) (l : loc) (w : bv 8) : state -> Prop :=
    fun s' => match l with
    | RegLoc r => Reg s' = (fun r' => if reg_eqb r r' then w else Reg s r') /\ RAM s' = RAM s
    | MemLoc addr => Reg s' = Reg s /\ RAM s' = write addr w (RAM s)
    end.


(* A description of how to find a location.
Covers all of the 6502's addressing modes,
except implied, which doesn't need a location,
and relative, which is only used for branches.
*)
Inductive mode :=
| RegMode : reg -> mode
| MemMode : mem_mode -> mode

(* Memory modes are treated separately,
because it is possible to read two bytes from them.
This wouldn't make sense for registers.
*)
with mem_mode :=
(* The location in memory immediately following the opcode. *)
| Args : mem_mode
(* Read two bytes from a memory location, optionally add the value in a register, and return that location in memory. *)
| Abs : mem_mode -> option reg -> mem_mode
(* Read a byte from a location, optionally add the value in a register, and return that location in the zero page. *)
| Zpg :     mode -> option reg -> mem_mode.

Coercion MemMode : mem_mode >-> mode.



(* Next, I define the relationship between `mode`s and locations,
and between `mem_mode`s and memory addresses. *)

(* Account for the fact that zero-page addresses wrap differently than absolute addresses. *)
Inductive addr :=
| Word16 : bv 16 -> addr
| Word8 : bv 8 -> addr
.
Definition word16_of_addr (addr : addr) : bv 16 :=
    match addr with
    | Word16 w => w
    | Word8 w => bv_zero_extend 16 w
    end.
Definition inc_addr (a : addr) : addr :=
    match a with
    | Word16 w => Word16 (bv_add_Z w 1)
    | Word8 w => Word8 (bv_add_Z w 1)
    end.
Definition fetch_addr s addr w := fetch s (word16_of_addr addr) w.
Definition fetch16_addr s addr w :=
    exists w1 w2,
    fetch_addr s addr w1 /\
    fetch_addr s (inc_addr addr) w2 /\
    w = spec.bv_concat 16 w1 w2.


Fixpoint mode_loc (s : state) (m : mode) : loc -> Prop :=
    match m with
    | RegMode r => fun l => l = RegLoc r
    | MemMode m => fun l => exists addr, mem_mode_addr s m addr /\ l = MemLoc (word16_of_addr addr)
    end
with mem_mode_addr (s : state) (m : mem_mode) : addr -> Prop :=
    match m with
    | Args => fun addr => addr = Word16 (bv_add_Z (PC s) 1)
    | Abs m r => fun addr =>
        exists addr' w,
        mem_mode_addr s m addr' /\
        fetch16_addr s addr' w /\
        addr = Word16 match r with
        | None => w
        | Some r => w + (bv_zero_extend 16 (Reg s r))
        end
    | Zpg m r => fun addr =>
        exists l w,
        mode_loc s m l /\
        read s l w /\
        addr = Word8 match r with
        | None => w
        | Some r => w + (Reg s r)
        end
    end.




(* Lemmas: The `Word8` and `Word16` constructors for `addr` are injective *)
Lemma Word8_inj w1 w2 : Word8 w1 = Word8 w2 -> w1 = w2.
Proof.
    move=> H.
    set f := (fun a => match a with Word8 w => w = w1 | Word16 _ => False end).
    have: f (Word8 w1) by trivial.
    rewrite H.
    done.
Qed.
Lemma Word16_inj w1 w2 : Word16 w1 = Word16 w2 -> w1 = w2.
Proof.
    move=> H.
    set f := (fun a => match a with Word16 w => w = w1 | Word8 _ => False end).
    have: f (Word16 w1) by trivial.
    rewrite H.
    done.
Qed.

(* Theorems relating `mem_mode`s, as defined in this file,
to `mem_addressing_mode`s, as defined in `spec/Main.v`. *)
Theorem immediate_mode s addr :
    immediate s addr -> mode_loc s Args (MemLoc addr).
Proof.
    rewrite /immediate /mem_mode_addr.
    move=>->.
    by exists (Word16 (bv_add_Z (PC s) 1)).
Qed.
Theorem absolute_mode s addr :
    absolute s addr -> mode_loc s (Abs Args None) (MemLoc addr).
Proof.
    move=> [w1 [w2 [fetch_w1 [fetch_w2 ->]]]].
    exists (Word16 (spec.bv_concat 16 w1 w2)).
    split; last reflexivity.
    exists (Word16 (bv_add_Z (PC s) 1)), (spec.bv_concat 16 w1 w2).
    split; first reflexivity.
    split; last reflexivity.
    rewrite /fetch16_addr /inc_addr bv_inc_inc.
    by exists w1, w2.
Qed.
Theorem absolute_x_mode s addr :
    absolute_x s addr -> mode_loc s (Abs Args (Some X)) (MemLoc addr).
Proof.
    move=> [w1 [w2 [fetch_w1 [fetch_w2 ->]]]].
    exists (Word16 (spec.bv_concat 16 w1 w2 + bv_zero_extend 16 (Reg s X))).
    split; last reflexivity.
    exists (Word16 (bv_add_Z (PC s) 1)), (spec.bv_concat 16 w1 w2).
    split; first reflexivity.
    split; last reflexivity.
    rewrite /fetch16_addr /inc_addr bv_inc_inc.
    by exists w1, w2.
Qed.
Theorem absolute_y_mode s addr :
    absolute_y s addr -> mode_loc s (Abs Args (Some Y)) (MemLoc addr).
Proof.
    move=> [w1 [w2 [fetch_w1 [fetch_w2 ->]]]].
    exists (Word16 (spec.bv_concat 16 w1 w2 + bv_zero_extend 16 (Reg s Y))).
    split; last reflexivity.
    exists (Word16 (bv_add_Z (PC s) 1)), (spec.bv_concat 16 w1 w2).
    split; first reflexivity.
    split; last reflexivity.
    rewrite /fetch16_addr /inc_addr bv_inc_inc.
    by exists w1, w2.
Qed.
Theorem zero_page_mode s addr :
    zero_page s addr -> mode_loc s (Zpg Args None) (MemLoc addr).
Proof.
    move=> [w [fetch_w ->]].
    rewrite /mode_loc.
    exists (Word8 w).
    split; last reflexivity.
    exists (MemLoc (bv_add_Z (PC s) 1)), w.
    split; last done.
    by exists (Word16 (bv_add_Z (PC s) 1)).
Qed.
Theorem zero_page_x_mode s addr :
    zero_page_x s addr -> mode_loc s (Zpg Args (Some X)) (MemLoc addr).
Proof.
    move=> [w [fetch_w ->]].
    rewrite /mode_loc.
    exists (Word8 (w + (Reg s X))).
    split; last reflexivity.
    exists (MemLoc (bv_add_Z (PC s) 1)), w.
    split; last done.
    by exists (Word16 (bv_add_Z (PC s) 1)).
Qed.
Theorem zero_page_y_mode s addr :
    zero_page_y s addr -> mode_loc s (Zpg Args (Some Y)) (MemLoc addr).
Proof.
    move=> [w [fetch_w ->]].
    rewrite /mode_loc.
    exists (Word8 (w + (Reg s Y))).
    split; last reflexivity.
    exists (MemLoc (bv_add_Z (PC s) 1)), w.
    split; last done.
    by exists (Word16 (bv_add_Z (PC s) 1)).
Qed.
Theorem indirect_x_mode s addr :
    indirect_x s addr -> mode_loc s (Abs (Zpg Args (Some X)) None) (MemLoc addr).
Proof.
    rewrite /indirect_x /mem_mode_addr.
    move=> [w [w1 [w2 [fetch_w [fetch_w1 [fetch_w2 ->]]]]]].
    exists (Word16 (spec.bv_concat 16 w1 w2)).
    split; last reflexivity.
    exists (Word8 (w + (Reg s X))), (spec.bv_concat 16 w1 w2).
    split.
    - exists (MemLoc (bv_add_Z (PC s) 1)), w.
        split.
        + by exists (Word16 (bv_add_Z (PC s) 1)).
        + done.
    - split; last reflexivity.
        by exists w1, w2.
Qed.
Theorem indirect_y_mode s addr :
    indirect_y s addr -> mode_loc s (Abs (Zpg Args None) (Some Y)) (MemLoc addr).
Proof.
    rewrite /indirect_y /mem_mode_addr.
    move=> [w [w1 [w2 [fetch_w [fetch_w1 [fetch_w2 ->]]]]]].
    rewrite /mode_loc.
    exists (Word16 ((spec.bv_concat 16 w1 w2) + (bv_zero_extend 16 (Reg s Y)))).
    split; last reflexivity.
    exists (Word8 w), (spec.bv_concat 16 w1 w2).
    split.
    - exists (MemLoc (bv_add_Z (PC s) 1)), w.
        split; last done.
        by exists (Word16 (bv_add_Z (PC s) 1)).
    - split; last reflexivity.
        by exists w1, w2.
Qed.





(* A simplified assembly language,
corresponding to the non-jumping instructions of the 6502. *)

Inductive binop := And | Or | Xor | Add | Sub.
Inductive bintest := Cmp | Bit.
Inductive unop := Inc | Dec | ShiftL (roll : bool) | ShiftR (roll : bool).

Inductive typical_instr :=
| Binary : binop -> mode -> mode -> typical_instr
| Unary : unop -> mode -> typical_instr
| BinTest : bintest -> mode -> mode -> typical_instr
(* The bool determined whether the N and Z flags will be set. *)
| Mov : bool -> mode -> mode -> typical_instr
.

Inductive linear_instr :=
| Typical : typical_instr -> linear_instr
| SetFlag : flag -> bool -> linear_instr
| Nop
.
Coercion Typical : typical_instr >-> linear_instr.

(* Inductive instr :=
| Linear : linear_instr -> instr
| JMP : mem_mode -> instr
| JSR : mem_mode -> instr
| RET
.
Coercion Linear : linear_instr >-> instr. *)





(* Compute the length of an instruction. *)
Fixpoint mode_arg_len (l : mode) : nat :=
    match l with
    | RegMode _ => 0
    | MemMode l =>
        (fix help (bytes_needed : nat) (l : mem_mode) := match l with
        | Args => bytes_needed
        | Abs l _ => help 2%nat l
        | Zpg l _ => mode_arg_len l
        end) 1%nat l
    end.
Definition instr_arg_len (i : linear_instr) : nat :=
    match i with
    | Binary _ l1 l2 => Nat.max (mode_arg_len l1) (mode_arg_len l2)
    | BinTest _ l1 l2 => Nat.max (mode_arg_len l1) (mode_arg_len l2)
    | Unary _ l => mode_arg_len l
    | Mov _ l1 l2 => Nat.max (mode_arg_len l1) (mode_arg_len l2)
    | SetFlag _ _ => 0
    | Nop => 0
    end.




(* A definition of what it means to run an assembly instruction. *)
Definition run_binop (op : binop) (d : bool) (w1 w2 w : bv 8) (c_in c_out : bool) : Prop :=
    match op with
    | And => w = bv_and w1 w2 /\ c_in = c_out
    | Or  => w = bv_or  w1 w2 /\ c_in = c_out
    | Xor => w = bv_xor w1 w2 /\ c_in = c_out
    | Add =>
        if d
        then ADC_decimal_relation c_in w1 w2 w c_out
        else (w, c_out) = spec.add_with_carry c_in w1 w2
    | Sub =>
        if d
        then SBC_decimal_relation c_in w1 w2 w c_out
        else (w, c_out) = spec.sub_with_inverted_borrow c_in w1 w2
    end.

Definition run_bintest (test : bintest) (w1 w2 w : bv 8) (c_in c_out : bool) : Prop :=
    match test with
    | Bit => w = bv_and w1 w2 /\ c_in = c_out
    | Cmp => (w, c_out) = spec.sub_with_inverted_borrow true w1 w2
    end.

Definition run_unop (op : unop) (w_in w_out : bv 8) (c_in c_out : bool) : Prop :=
    match op with
    | Inc => w_out = bv_add_Z w_in 1 /\ c_out = c_in
    | Dec => w_out = bv_sub_Z w_in 1 /\ c_out = c_in
    | ShiftL roll =>
        spec.bv_concat 9 w_out (bool_to_bv 1 c_out) =
        spec.bv_concat 9 (bool_to_bv 1 (if roll then c_in else false)) w_in
    | ShiftR roll =>
        spec.bv_concat 9 (bool_to_bv 1 c_out) w_out =
        spec.bv_concat 9 w_in (bool_to_bv 1 (if roll then c_in else false))
    end.

Definition run_instr (i : linear_instr) (s1 s2 : state) : Prop :=
    PC s2 = bv_add_Z (PC s1) (Z.of_nat (S (instr_arg_len i))) /\
    match i with
    | Nop =>
        Reg s2 = Reg s1 /\
        Flag s2 = Flag s1 /\
        RAM s2 = RAM s1
    | SetFlag f value =>
        Reg s2 = Reg s1 /\
        (Flag s2 = fun f' => if flag_eqb f f' then value else Flag s1 f') /\
        RAM s2 = RAM s1
    | Typical i =>
        Flag s2 D = Flag s1 D /\
        exists computed_value : bv 8,
        match i with
        | Binary op m1 m2 =>
            exists l1 l2 w1 w2,
            mode_loc s1 m1 l1 /\
            mode_loc s1 m2 l2 /\
            read s1 l1 w1 /\
            read s1 l2 w2 /\
            run_binop op (Flag s1 D) w1 w2 computed_value (Flag s1 C) (Flag s2 C) /\
            write s1 l1 computed_value s2
        | BinTest test m1 m2 =>
            exists l1 l2 w1 w2,
            mode_loc s1 m1 l1 /\
            mode_loc s1 m2 l2 /\
            read s1 l1 w1 /\
            read s1 l2 w2 /\
            run_bintest test w1 w2 computed_value (Flag s1 C) (Flag s2 C) /\
            Reg s2 = Reg s1 /\ RAM s2 = RAM s1
        | Unary op m =>
            exists l w,
            mode_loc s1 m l /\
            read s1 l w /\
            run_unop op w computed_value (Flag s1 C) (Flag s2 C) /\
            write s1 l computed_value s2
        | Mov _ m1 m2 =>
            exists l1 l2,
            mode_loc s1 m1 l1 /\
            mode_loc s1 m2 l2 /\
            read s1 l1 computed_value /\
            write s1 l2 computed_value s2 /\
            Flag s1 C = Flag s2 C
        end /\
        match i with
        | Mov false _ _ =>
            Flag s2 N = Flag s1 N
            /\ Flag s2 Z = Flag s1 Z
        | _ =>
            Flag s2 N = bit 7 computed_value /\
            Flag s2 Z = bv_eqb computed_value 0x00
        end
    end.


(* A function mapping opcodes to instructions. *)
Definition parse_instr (opcode : bv 8) : option linear_instr :=
    match opcode with

    | 0x01 => Some (Typical (Binary  Or  (RegMode A) (Abs (Zpg Args (Some X)) None)))
    | 0x21 => Some (Typical (Binary  And (RegMode A) (Abs (Zpg Args (Some X)) None)))
    | 0x41 => Some (Typical (Binary  Xor (RegMode A) (Abs (Zpg Args (Some X)) None)))
    | 0x61 => Some (Typical (Binary  Add (RegMode A) (Abs (Zpg Args (Some X)) None)))
    | 0x81 => Some (Typical (Mov false   (RegMode A) (Abs (Zpg Args (Some X)) None)))
    | 0xa1 => Some (Typical (Mov true    (Abs (Zpg Args (Some X)) None) (RegMode A)))
    | 0xc1 => Some (Typical (BinTest Cmp (RegMode A) (Abs (Zpg Args (Some X)) None)))
    | 0xe1 => Some (Typical (Binary  Sub (RegMode A) (Abs (Zpg Args (Some X)) None)))

    | 0x05 => Some (Typical (Binary  Or  (RegMode A) (Zpg Args None)))
    | 0x25 => Some (Typical (Binary  And (RegMode A) (Zpg Args None)))
    | 0x45 => Some (Typical (Binary  Xor (RegMode A) (Zpg Args None)))
    | 0x65 => Some (Typical (Binary  Add (RegMode A) (Zpg Args None)))
    | 0x85 => Some (Typical (Mov false   (RegMode A) (Zpg Args None)))
    | 0xa5 => Some (Typical (Mov true    (Zpg Args None) (RegMode A)))
    | 0xc5 => Some (Typical (BinTest Cmp (RegMode A) (Zpg Args None)))
    | 0xe5 => Some (Typical (Binary  Sub (RegMode A) (Zpg Args None)))

    | 0x09 => Some (Typical (Binary  Or  (RegMode A) Args))
    | 0x29 => Some (Typical (Binary  And (RegMode A) Args))
    | 0x49 => Some (Typical (Binary  Xor (RegMode A) Args))
    | 0x69 => Some (Typical (Binary  Add (RegMode A) Args))
    | 0xa9 => Some (Typical (Mov true    Args (RegMode A)))
    | 0xc9 => Some (Typical (BinTest Cmp (RegMode A) Args))
    | 0xe9 => Some (Typical (Binary  Sub (RegMode A) Args))

    | 0x0d => Some (Typical (Binary  Or  (RegMode A) (Abs Args None)))
    | 0x2d => Some (Typical (Binary  And (RegMode A) (Abs Args None)))
    | 0x4d => Some (Typical (Binary  Xor (RegMode A) (Abs Args None)))
    | 0x6d => Some (Typical (Binary  Add (RegMode A) (Abs Args None)))
    | 0x8d => Some (Typical (Mov false   (RegMode A) (Abs Args None)))
    | 0xad => Some (Typical (Mov true    (Abs Args None) (RegMode A)))
    | 0xcd => Some (Typical (BinTest Cmp (RegMode A) (Abs Args None)))
    | 0xed => Some (Typical (Binary  Sub (RegMode A) (Abs Args None)))

    | 0x11 => Some (Typical (Binary  Or  (RegMode A) (Abs (Zpg Args None) (Some Y))))
    | 0x31 => Some (Typical (Binary  And (RegMode A) (Abs (Zpg Args None) (Some Y))))
    | 0x51 => Some (Typical (Binary  Xor (RegMode A) (Abs (Zpg Args None) (Some Y))))
    | 0x71 => Some (Typical (Binary  Add (RegMode A) (Abs (Zpg Args None) (Some Y))))
    | 0x91 => Some (Typical (Mov false   (RegMode A) (Abs (Zpg Args None) (Some Y))))
    | 0xb1 => Some (Typical (Mov true    (Abs (Zpg Args None) (Some Y)) (RegMode A)))
    | 0xd1 => Some (Typical (BinTest Cmp (RegMode A) (Abs (Zpg Args None) (Some Y))))
    | 0xf1 => Some (Typical (Binary  Sub (RegMode A) (Abs (Zpg Args None) (Some Y))))

    | 0x15 => Some (Typical (Binary  Or  (RegMode A) (Zpg Args (Some X))))
    | 0x35 => Some (Typical (Binary  And (RegMode A) (Zpg Args (Some X))))
    | 0x55 => Some (Typical (Binary  Xor (RegMode A) (Zpg Args (Some X))))
    | 0x75 => Some (Typical (Binary  Add (RegMode A) (Zpg Args (Some X))))
    | 0x95 => Some (Typical (Mov false   (RegMode A) (Zpg Args (Some X))))
    | 0xb5 => Some (Typical (Mov true    (Zpg Args (Some X)) (RegMode A)))
    | 0xd5 => Some (Typical (BinTest Cmp (RegMode A) (Zpg Args (Some X))))
    | 0xf5 => Some (Typical (Binary  Sub (RegMode A) (Zpg Args (Some X))))

    | 0x19 => Some (Typical (Binary  Or  (RegMode A) (Abs Args (Some Y))))
    | 0x39 => Some (Typical (Binary  And (RegMode A) (Abs Args (Some Y))))
    | 0x59 => Some (Typical (Binary  Xor (RegMode A) (Abs Args (Some Y))))
    | 0x79 => Some (Typical (Binary  Add (RegMode A) (Abs Args (Some Y))))
    | 0x99 => Some (Typical (Mov false   (RegMode A) (Abs Args (Some Y))))
    | 0xb9 => Some (Typical (Mov true    (Abs Args (Some Y)) (RegMode A)))
    | 0xd9 => Some (Typical (BinTest Cmp (RegMode A) (Abs Args (Some Y))))
    | 0xf9 => Some (Typical (Binary  Sub (RegMode A) (Abs Args (Some Y))))

    | 0x1d => Some (Typical (Binary  Or  (RegMode A) (Abs Args (Some X))))
    | 0x3d => Some (Typical (Binary  And (RegMode A) (Abs Args (Some X))))
    | 0x5d => Some (Typical (Binary  Xor (RegMode A) (Abs Args (Some X))))
    | 0x7d => Some (Typical (Binary  Add (RegMode A) (Abs Args (Some X))))
    | 0x9d => Some (Typical (Mov false   (RegMode A) (Abs Args (Some X))))
    | 0xbd => Some (Typical (Mov true    (Abs Args (Some X)) (RegMode A)))
    | 0xdd => Some (Typical (BinTest Cmp (RegMode A) (Abs Args (Some X))))
    | 0xfd => Some (Typical (Binary  Sub (RegMode A) (Abs Args (Some X))))


    | 0x06 => Some (Typical (Unary (ShiftL false) (Zpg Args None)))
    | 0x26 => Some (Typical (Unary (ShiftL true ) (Zpg Args None)))
    | 0x46 => Some (Typical (Unary (ShiftR false) (Zpg Args None)))
    | 0x66 => Some (Typical (Unary (ShiftR true ) (Zpg Args None)))
    | 0x86 => Some (Typical (Mov false (RegMode X) (Zpg Args None)))
    | 0xa6 => Some (Typical (Mov true  (Zpg Args None) (RegMode X)))
    | 0xc6 => Some (Typical (Unary Dec            (Zpg Args None)))
    | 0xe6 => Some (Typical (Unary Inc            (Zpg Args None)))

    | 0x0a => Some (Typical (Unary (ShiftL false) (RegMode A)))
    | 0x2a => Some (Typical (Unary (ShiftL true ) (RegMode A)))
    | 0x4a => Some (Typical (Unary (ShiftR false) (RegMode A)))
    | 0x6a => Some (Typical (Unary (ShiftR true ) (RegMode A)))
    | 0x8a => Some (Typical (Mov true  (RegMode X) (RegMode A)))
    | 0xaa => Some (Typical (Mov true  (RegMode A) (RegMode X)))
    | 0xca => Some (Typical (Unary Dec            (RegMode X)))
    | 0xea => Some Nop

    | 0x0e => Some (Typical (Unary (ShiftL false) (Abs Args None)))
    | 0x2e => Some (Typical (Unary (ShiftL true ) (Abs Args None)))
    | 0x4e => Some (Typical (Unary (ShiftR false) (Abs Args None)))
    | 0x6e => Some (Typical (Unary (ShiftR true ) (Abs Args None)))
    | 0x8e => Some (Typical (Mov false (RegMode X) (Abs Args None)))
    | 0xae => Some (Typical (Mov true  (Abs Args None) (RegMode X)))
    | 0xce => Some (Typical (Unary Dec            (Abs Args None)))
    | 0xee => Some (Typical (Unary Inc            (Abs Args None)))

    | 0x16 => Some (Typical (Unary (ShiftL false) (Zpg Args (Some X))))
    | 0x36 => Some (Typical (Unary (ShiftL true ) (Zpg Args (Some X))))
    | 0x56 => Some (Typical (Unary (ShiftR false) (Zpg Args (Some X))))
    | 0x76 => Some (Typical (Unary (ShiftR true ) (Zpg Args (Some X))))
    | 0x96 => Some (Typical (Mov false (RegMode X) (Zpg Args (Some Y))))
    | 0xb6 => Some (Typical (Mov true  (Zpg Args (Some Y)) (RegMode X)))
    | 0xd6 => Some (Typical (Unary Dec            (Zpg Args (Some X))))
    | 0xf6 => Some (Typical (Unary Inc            (Zpg Args (Some X))))

    | 0x9a => Some (Typical (Mov false (RegMode X) (RegMode SP)))
    | 0xba => Some (Typical (Mov true  (RegMode SP) (RegMode X)))

    | 0x1e => Some (Typical (Unary (ShiftL false) (Abs Args (Some X))))
    | 0x3e => Some (Typical (Unary (ShiftL true ) (Abs Args (Some X))))
    | 0x5e => Some (Typical (Unary (ShiftR false) (Abs Args (Some X))))
    | 0x7e => Some (Typical (Unary (ShiftR true ) (Abs Args (Some X))))
    | 0xbe => Some (Typical (Mov true  (Abs Args (Some Y)) (RegMode X)))
    | 0xde => Some (Typical (Unary Dec            (Abs Args (Some X))))
    | 0xfe => Some (Typical (Unary Inc            (Abs Args (Some X))))


    | 0x24 => Some (Typical (BinTest Bit (RegMode A) (Zpg Args None)))
    | 0x84 => Some (Typical (Mov false   (RegMode Y) (Zpg Args None)))
    | 0xa4 => Some (Typical (Mov true    (Zpg Args None) (RegMode Y)))
    | 0xc4 => Some (Typical (BinTest Cmp (RegMode Y) (Zpg Args None)))
    | 0xe4 => Some (Typical (BinTest Cmp (RegMode X) (Zpg Args None)))

    | 0x88 => Some (Typical (Unary   Dec (RegMode Y)))
    | 0xa8 => Some (Typical (Mov true    (RegMode A) (RegMode Y)))
    | 0xc8 => Some (Typical (Unary   Inc (RegMode Y)))
    | 0xe8 => Some (Typical (Unary   Inc (RegMode X)))

    | 0x2c => Some (Typical (BinTest Bit (RegMode A) (Abs Args None)))
    | 0x8c => Some (Typical (Mov false   (RegMode Y) (Abs Args None)))
    | 0xac => Some (Typical (Mov true    (Abs Args None) (RegMode Y)))
    | 0xcc => Some (Typical (BinTest Cmp (RegMode Y) (Abs Args None)))
    | 0xec => Some (Typical (BinTest Cmp (RegMode X) (Abs Args None)))

    | 0x94 => Some (Typical (Mov false   (RegMode Y) (Zpg Args (Some X))))
    | 0xb4 => Some (Typical (Mov true    (Zpg Args (Some X)) (RegMode Y)))
    | 0x98 => Some (Typical (Mov true    (RegMode Y) (RegMode A)))
    | 0xbc => Some (Typical (Mov true    (Abs Args (Some X)) (RegMode Y)))


    | 0x18 => Some (SetFlag C false)
    | 0x38 => Some (SetFlag C true)
    | 0x58 => Some (SetFlag I false)
    | 0x78 => Some (SetFlag I true)
    | 0xb8 => Some (SetFlag V false)
    | 0xd8 => Some (SetFlag D false)
    | 0xf8 => Some (SetFlag D true)


    | 0xa2 => Some (Typical (Mov true Args (RegMode X)))
    | 0xa0 => Some (Typical (Mov true Args (RegMode Y)))
    | 0xc0 => Some (Typical (BinTest Cmp (RegMode Y) Args))
    | 0xe0 => Some (Typical (BinTest Cmp (RegMode X) Args))

    | _ => None
    end.



(* Lemmas leading up to the theorem 300 lines below. *)
Lemma run_SetFlag s1 s2 f val :
    flag_instruction s1 s2 f val ->
    run_instr (SetFlag f val) s1 s2.
Proof.
    rewrite /run_instr.
    by move=> [-> [-> [-> ->]]].
Qed.

Lemma run_transfer s1 s2 r1 r2 :
    transfer_instruction s1 s2 r1 r2 ->
    run_instr (Mov true (RegMode r1) (RegMode r2)) s1 s2.
Proof.
    rewrite /run_instr /write.
    move=> [-> [-> [-> ->]]].
    split; first reflexivity.
    split; first reflexivity.
    exists (Reg s1 r1).
    split; last done.
    by exists (RegLoc r1), (RegLoc r2).
Qed.
Lemma run_store s1 s2 r mode (mode' : mem_mode) len :
    len = Z.of_nat (S (mode_arg_len mode')) ->
    store_instruction s1 s2 r mode len ->
    (forall addr, mode s1 addr -> mode_loc s1 mode' (MemLoc addr)) ->
    run_instr (Mov false (RegMode r) mode') s1 s2.
Proof.
    rewrite /run_instr /write.
    move=> -> H mode_spec.
    move: H => [addr' [/mode_spec m [-> [-> [-> ->]]]]].
    split; first reflexivity.
    split; first reflexivity.
    exists (Reg s1 r).
    split; last done.
    by exists (RegLoc r), (MemLoc addr').
Qed.
Lemma run_load s1 s2 r mode (mode' : mem_mode) len :
    len = Z.of_nat (S (mode_arg_len mode')) ->
    load_instruction s1 s2 r mode len ->
    (forall addr, mode s1 addr -> mode_loc s1 mode' (MemLoc addr)) ->
    run_instr (Mov true mode' (RegMode r)) s1 s2.
Proof.
    rewrite /run_instr /write.
    move=> -> H mode_spec.
    move: H => [addr' [w [/mode_spec m [fetch_w [-> [-> [-> ->]]]]]]].
    split; first by rewrite /instr_arg_len PeanoNat.Nat.max_0_r.
    split; first reflexivity.
    exists w.
    split; last done.
    by exists (MemLoc addr'), (RegLoc r).
Qed.

Lemma run_Or s1 s2 mode (mode' : mem_mode) len :
    len = Z.of_nat (S (mode_arg_len mode')) ->
    logic_instruction s1 s2 bv_or mode len ->
    (forall addr, mode s1 addr -> mode_loc s1 mode' (MemLoc addr)) ->
    run_instr (Binary Or (RegMode A) mode') s1 s2.
Proof.
    rewrite /run_instr /write.
    move=> -> H mode_spec.
    move: H => [addr' [w [/mode_spec m [fetch_w [-> [-> [-> ->]]]]]]].
    split; first reflexivity.
    split; first reflexivity.
    exists (bv_or (Reg s1 A) w).
    split; last done.
    by exists (RegLoc A), (MemLoc addr'), (Reg s1 A), w.
Qed.
Lemma run_And s1 s2 mode (mode' : mem_mode) len :
    len = Z.of_nat (S (mode_arg_len mode')) ->
    logic_instruction s1 s2 bv_and mode len ->
    (forall addr, mode s1 addr -> mode_loc s1 mode' (MemLoc addr)) ->
    run_instr (Binary And (RegMode A) mode') s1 s2.
Proof.
    rewrite /run_instr /write.
    move=> -> H mode_spec.
    move: H => [addr' [w [/mode_spec m [fetch_w [-> [-> [-> ->]]]]]]].
    split; first reflexivity.
    split; first reflexivity.
    exists (bv_and (Reg s1 A) w).
    split; last done.
    by exists (RegLoc A), (MemLoc addr'), (Reg s1 A), w.
Qed.
Lemma run_Xor s1 s2 mode (mode' : mem_mode) len :
    len = Z.of_nat (S (mode_arg_len mode')) ->
    logic_instruction s1 s2 bv_xor mode len ->
    (forall addr, mode s1 addr -> mode_loc s1 mode' (MemLoc addr)) ->
    run_instr (Binary Xor (RegMode A) mode') s1 s2.
Proof.
    rewrite /run_instr /write.
    move=> -> H mode_spec.
    move: H => [addr' [w [/mode_spec m [fetch_w [-> [-> [-> ->]]]]]]].
    split; first reflexivity.
    split; first reflexivity.
    exists (bv_xor (Reg s1 A) w).
    split; last done.
    by exists (RegLoc A), (MemLoc addr'), (Reg s1 A), w.
Qed.
Lemma run_Bit s1 s2 mode (mode' : mem_mode) len :
    len = Z.of_nat (S (mode_arg_len mode')) ->
    BIT_mode s1 s2 mode len ->
    (forall addr, mode s1 addr -> mode_loc s1 mode' (MemLoc addr)) ->
    run_instr (BinTest Bit (RegMode A) mode') s1 s2.
Proof.
    rewrite /run_instr.
    move=> -> H mode_spec.
    move: H => [addr' [w [/mode_spec m [fetch_w [-> [-> [-> ->]]]]]]].
    split; first reflexivity.
    split; first reflexivity.
    exists (bv_and (Reg s1 A) w).
    split; last done.
    by exists (RegLoc A), (MemLoc addr'), (Reg s1 A), w.
Qed.


Lemma run_Add s1 s2 mode (mode' : mem_mode) len :
    len = Z.of_nat (S (mode_arg_len mode')) ->
    ADC_mode s1 s2 mode len ->
    (forall addr, mode s1 addr -> mode_loc s1 mode' (MemLoc addr)) ->
    run_instr (Binary Add (RegMode A) mode') s1 s2.
Proof.
    rewrite /run_instr /write.
    move=> -> H mode_spec; move: H.

    have [d d_def]: exists d, d = Flag s1 D by exists (Flag s1 D).
    rewrite /ADC_mode -d_def; case: d d_def => d_def.
    - move=> [addr' [w_in [w_out [c_out [v [/mode_spec m [fetch_w_in [is_dec_add [-> [-> [-> ->]]]]]]]]]]].
        split; first reflexivity.
        split; first by rewrite -d_def.
        exists w_out.
        split; last done.
        by exists (RegLoc A), (MemLoc addr'), (Reg s1 A), w_in.
    - move=> [addr' [w_in [/mode_spec m [fetch_w_in tmp]]]]; move: tmp.
        move=> [-> [-> [-> ->]]].
        split; first reflexivity.
        split; first by rewrite -d_def.
        exists (fst (spec.add_with_carry (Flag s1 C) (Reg s1 A) w_in)).
        split; last done.
        by exists (RegLoc A), (MemLoc addr'), (Reg s1 A), w_in.
Qed.
Lemma run_Sub s1 s2 mode (mode' : mem_mode) len :
    len = Z.of_nat (S (mode_arg_len mode')) ->
    SBC_mode s1 s2 mode len ->
    (forall addr, mode s1 addr -> mode_loc s1 mode' (MemLoc addr)) ->
    run_instr (Binary Sub (RegMode A) mode') s1 s2.
Proof.
    rewrite /run_instr /write.
    move=> -> H mode_spec; move: H.

    have [d d_def]: exists d, d = Flag s1 D by exists (Flag s1 D).

    rewrite /SBC_mode -d_def; case: d d_def => d_def.
    + move=> [addr' [w_in [w_out [c_out [v [/mode_spec m [fetch_w_in [is_dec_add [-> [-> [-> ->]]]]]]]]]]].
        split; first reflexivity.
        split; first by rewrite -d_def.
        exists w_out.
        split; last done.
        by exists (RegLoc A), (MemLoc addr'), (Reg s1 A), w_in.
    + move=> [addr' [w_in [/mode_spec m [fetch_w_in tmp]]]]; move: tmp.
        move=> [-> [-> [-> ->]]].
        split; first reflexivity.
        split; first by rewrite -d_def.
        exists (fst (spec.sub_with_inverted_borrow (Flag s1 C) (Reg s1 A) w_in)).
        split; last done.
        by exists (RegLoc A), (MemLoc addr'), (Reg s1 A), w_in.
Qed.
Lemma run_Cmp s1 s2 r mode (mode' : mem_mode) len :
    len = Z.of_nat (S (mode_arg_len mode')) ->
    CMP_mode s1 s2 r mode len ->
    (forall addr, mode s1 addr -> mode_loc s1 mode' (MemLoc addr)) ->
    run_instr (BinTest Cmp (RegMode r) mode') s1 s2.
Proof.
    rewrite /run_instr.

    move=> -> H mode_spec.
    move: H => [addr' [w_in [/mode_spec m [fetch_w_in tmp]]]]; move: tmp.
    move=> [-> [-> [-> ->]]].
    split; first reflexivity.
    split; first reflexivity.
    exists (fst (spec.sub_with_inverted_borrow true (Reg s1 r) w_in)).
    split; last done.
    by exists (RegLoc r), (MemLoc addr'), (Reg s1 r), w_in.
Qed.


Lemma run_Shift (right roll : bool) s1 s2 mode (mode' : mem_mode) len :
    len = Z.of_nat (S (mode_arg_len mode')) ->
    @shift_instruction_mode s1 s2
        (if right
        then (if roll then ROR_spec else LSR_spec)
        else (if roll then ROL_spec else ASL_spec))
    mode len ->
    (forall addr, mode s1 addr -> mode_loc s1 mode' (MemLoc addr)) ->
    run_instr (Unary ((if right then ShiftR else ShiftL) roll) mode') s1 s2.
Proof.
    rewrite /run_instr /write.
    move=> -> H mode_spec.
    move: H => [addr' [w_in [c_out [w_out [/mode_spec m [fetch_w_in [is_shift [-> [-> [-> ->]]]]]]]]]].
    split; first reflexivity.
    split; first reflexivity.
    exists w_out.
    split; last done.
    exists (MemLoc addr'), w_in.
    by move: is_shift; case right, roll.
Qed.

Lemma run_Inc_mode s1 s2 mode (mode' : mem_mode) len :
    len = Z.of_nat (S (mode_arg_len mode')) ->
    INC_mode s1 s2 mode len ->
    (forall addr, mode s1 addr -> mode_loc s1 mode' (MemLoc addr)) ->
    run_instr (Unary Inc mode') s1 s2.
Proof.
    rewrite /run_instr /write.
    move=> -> H mode_spec.
    move: H => [addr' [w [/mode_spec m [fetch_w [-> [-> [-> ->]]]]]]].
    split; first reflexivity.
    split; first reflexivity.
    exists (bv_add_Z w 1).
    split; last done.
    by exists (MemLoc addr'), w.
Qed.
Lemma run_Inc_reg s1 s2 r :
    INC_reg s1 s2 r ->
    run_instr (Unary Inc (RegMode r)) s1 s2.
Proof.
    rewrite /run_instr /write.
    move=> H.
    move: H => [-> [-> [-> ->]]].
    split; first reflexivity.
    split; first reflexivity.
    exists (bv_add_Z (Reg s1 r) 1).
    split; last done.
    by exists (RegLoc r), (Reg s1 r).
Qed.

Lemma run_Dec_mode s1 s2 mode (mode' : mem_mode) len :
    len = Z.of_nat (S (mode_arg_len mode')) ->
    DEC_mode s1 s2 mode len ->
    (forall addr, mode s1 addr -> mode_loc s1 mode' (MemLoc addr)) ->
    run_instr (Unary Dec mode') s1 s2.
Proof.
    rewrite /run_instr /write.
    move=> -> H mode_spec.
    move: H => [addr' [w [/mode_spec m [fetch_w [-> [-> [-> ->]]]]]]].
    split; first reflexivity.
    split; first reflexivity.
    exists (bv_sub_Z w 1).
    split; last done.
    by exists (MemLoc addr'), w.
Qed.
Lemma run_Dec_reg s1 s2 r :
    DEC_reg s1 s2 r ->
    run_instr (Unary Dec (RegMode r)) s1 s2.
Proof.
    rewrite /run_instr /write.
    move=> H.
    move: H => [-> [-> [-> ->]]].
    split; first reflexivity.
    split; first reflexivity.
    exists (bv_sub_Z (Reg s1 r) 1).
    split; last done.
    by exists (RegLoc r), (Reg s1 r).
Qed.



(* The big theorem of this file. If an opcode corresponds to an assembly instruction,
the behavior of the assembly instruction fully captures
the possible behaviors of the machine instruction.
*)
Theorem run_instr_spec opcode :
    match parse_instr opcode with
    | None => True
    | Some i => forall s1 s2, instruction s1 s2 opcode -> run_instr i s1 s2
    end.
Proof.
    rewrite -(bv_of_byte_of_bv opcode) bv_of_byte_speedup.
    case (byte_of_bv opcode); simpl.

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
    - rewrite /run_instr /write.
         move=> s1 s2 /ASL_A H; specialize (H eq_refl); move: H => [c [w [? [-> [-> [-> ->]]]]]].
         split; first reflexivity.
         split; first reflexivity.
         exists w.
         split; last done.
         by exists (RegLoc A), (Reg s1 A).
    - trivial.
    - trivial.
    - by intros; eapply run_Or; [reflexivity | eapply ORA_absolute | apply absolute_mode].
    - by intros; eapply (run_Shift false false); [reflexivity | eapply ASL_absolute | apply absolute_mode].
    - trivial.

    (* 1 *)
    - trivial.
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
    - trivial.
    - by intros; eapply run_And; [reflexivity | eapply AND_indirect_x | apply indirect_x_mode].
    - trivial.
    - trivial.
    - by intros; eapply run_Bit; [reflexivity | eapply BIT_zero_page | apply zero_page_mode].
    - by intros; eapply run_And; [reflexivity | eapply AND_zero_page | apply zero_page_mode].
    - by intros; eapply (run_Shift false true); [reflexivity | eapply ROL_zero_page | apply zero_page_mode].
    - trivial.
    - trivial.
    - by intros; eapply run_And; [reflexivity | eapply AND_immediate | apply immediate_mode].
    - rewrite /run_instr /write.
         move=> s1 s2 /ROL_A H; specialize (H eq_refl); move: H => [c [w [? [-> [-> [-> ->]]]]]].
         split; first reflexivity.
         split; first reflexivity.
         exists w.
         split; last done.
         by exists (RegLoc A), (Reg s1 A).
    - trivial.
    - by intros; eapply run_Bit; [reflexivity | eapply BIT_absolute | apply absolute_mode].
    - by intros; eapply run_And; [reflexivity | eapply AND_absolute | apply absolute_mode].
    - by intros; eapply (run_Shift false true); [reflexivity | eapply ROL_absolute | apply absolute_mode].
    - trivial.

    (* 3 *)
    - trivial.
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
    - rewrite /run_instr /write.
         move=> s1 s2 /LSR_A H; specialize (H eq_refl); move: H => [c [w [? [-> [-> [-> ->]]]]]].
         split; first reflexivity.
         split; first reflexivity.
         exists w.
         split; last done.
         by exists (RegLoc A), (Reg s1 A).
    - trivial.
    - trivial.
    - by intros; eapply run_Xor; [reflexivity | eapply EOR_absolute | apply absolute_mode].
    - by intros; eapply (run_Shift true false); [reflexivity | eapply LSR_absolute | apply absolute_mode].
    - trivial.

    (* 5 *)
    - trivial.
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
    - trivial.
    - by intros; eapply run_Add; [reflexivity | eapply ADC_indirect_x | apply indirect_x_mode].
    - trivial.
    - trivial.
    - trivial.
    - by intros; eapply run_Add; [reflexivity | eapply ADC_zero_page | apply zero_page_mode].
    - by intros; eapply (run_Shift true true); [reflexivity | eapply ROR_zero_page | apply zero_page_mode].
    - trivial.
    - trivial.
    - by intros; eapply run_Add; [reflexivity | eapply ADC_immediate | apply immediate_mode].
    - rewrite /run_instr /write.
         move=> s1 s2 /ROR_A H; specialize (H eq_refl); move: H => [c [w [? [-> [-> [-> ->]]]]]].
         split; first reflexivity.
         split; first reflexivity.
         exists w.
         split; last done.
         by exists (RegLoc A), (Reg s1 A).
    - trivial.
    - trivial.
    - by intros; eapply run_Add; [reflexivity | eapply ADC_absolute | apply absolute_mode].
    - by intros; eapply (run_Shift true true); [reflexivity | eapply ROR_absolute | apply absolute_mode].
    - trivial.

    (* 7 *)
    - trivial.
    - by intros; eapply run_Add; [reflexivity | eapply ADC_indirect_y | apply indirect_y_mode].
    - trivial.
    - trivial.
    - trivial.
    - by intros; eapply run_Add; [reflexivity | eapply ADC_zero_page_x | apply zero_page_x_mode].
    - by intros; eapply (run_Shift true true); [reflexivity | eapply ROR_zero_page_x | apply zero_page_x_mode].
    - trivial.
    - by intros; eapply run_SetFlag; eapply SEI.
    - by intros; eapply run_Add; [reflexivity | eapply ADC_absolute_y | apply absolute_y_mode].
    - trivial.
    - trivial.
    - trivial.
    - by intros; eapply run_Add; [reflexivity | eapply ADC_absolute_x | apply absolute_x_mode].
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
    - trivial.
    - by intros; eapply run_store; [reflexivity | eapply STA_indirect_y | apply indirect_y_mode].
    - trivial.
    - trivial.
    - by intros; eapply run_store; [reflexivity | eapply STY_zero_page_x | apply zero_page_x_mode].
    - by intros; eapply run_store; [reflexivity | eapply STA_zero_page_x | apply zero_page_x_mode].
    - by intros; eapply run_store; [reflexivity | eapply STX_zero_page_y | apply zero_page_y_mode].
    - trivial.
    - by intros; eapply run_transfer; eapply TYA.
    - by intros; eapply run_store; [reflexivity | eapply STA_absolute_y | apply absolute_y_mode].
    - rewrite /run_instr /write.
        move=> s1 s2 /TXS H; specialize (H eq_refl); move: H => [-> [-> [-> ->]]].
        split; first reflexivity.
        split; first reflexivity.
        exists (Reg s1 X).
        split; last done.
        by exists (RegLoc X), (RegLoc SP).
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
    - trivial.
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
    - trivial.
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
    - by intros; eapply run_Sub; [reflexivity | eapply SBC_indirect_x | apply indirect_x_mode].
    - trivial.
    - trivial.
    - by intros; eapply run_Cmp; [reflexivity | eapply CPX_zero_page | apply zero_page_mode].
    - by intros; eapply run_Sub; [reflexivity | eapply SBC_zero_page | apply zero_page_mode].
    - by intros; eapply run_Inc_mode; [reflexivity | eapply INC_zero_page | apply zero_page_mode].
    - trivial.
    - by intros; eapply run_Inc_reg; eapply INX.
    - by intros; eapply run_Sub; [reflexivity | eapply SBC_immediate | apply immediate_mode].
    - rewrite /run_instr.
        by move=> s1 s2 /NOP => H; specialize (H eq_refl); move: H => [-> [-> [-> ->]]].
    - trivial.
    - by intros; eapply run_Cmp; [reflexivity | eapply CPX_absolute | apply absolute_mode].
    - by intros; eapply run_Sub; [reflexivity | eapply SBC_absolute | apply absolute_mode].
    - by intros; eapply run_Inc_mode; [reflexivity | eapply INC_absolute | apply absolute_mode].
    - trivial.

    (* F *)
    - trivial.
    - by intros; eapply run_Sub; [reflexivity | eapply SBC_indirect_y | apply indirect_y_mode].
    - trivial.
    - trivial.
    - trivial.
    - by intros; eapply run_Sub; [reflexivity | eapply SBC_zero_page_x | apply zero_page_x_mode].
    - by intros; eapply run_Inc_mode; [reflexivity | eapply INC_zero_page_x | apply zero_page_x_mode].
    - trivial.
    - by intros; eapply run_SetFlag; eapply SED.
    - by intros; eapply run_Sub; [reflexivity | eapply SBC_absolute_y | apply absolute_y_mode].
    - trivial.
    - trivial.
    - trivial.
    - by intros; eapply run_Sub; [reflexivity | eapply SBC_absolute_x | apply absolute_x_mode].
    - by intros; eapply run_Inc_mode; [reflexivity | eapply INC_absolute_x | apply absolute_x_mode].
    - trivial.
Qed.

(* Thus the machine language has been (mostly) upgraded to an assembly language.
The benefits are as follows:
- No longer do I have to deal with 256 possible opcodes.
    The assembly instruction set, while not trivial, is a lot smaller.
- Control flow is decoupled from program behavior;
    it is trivial to extract the next PC value from `run_instr`.
- A structured language, even an assebly language,
    is the first step on the path to higher abstraction.
    And higher abstraction, done right, leads to a simpler description of the game.
*)
