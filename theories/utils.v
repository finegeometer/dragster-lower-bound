(*|
=====
Utils
=====

Helper code for the rest of the project.

----
Byte
----

Mostly thorems relating Coq's builtin ``byte`` type to ``std++``'s ``bv 8``.
I try to stick to the latter, but there's occasionally a reason to use the former.

This is a bit of a low-effort file — I basically handle all the proofs by 256-way case splits, even when there's a more elegant method.

|*)

Import Byte.
From stdpp Require Import
    ssreflect unstable.bitvector unstable.bitvector_tactics.

Global Instance byte_inhab : Inhabited byte := populate x00.

Definition Z_of_byte (w : byte) : Z :=
    let: (a, (b, (c, (d, (e, (f, (g, h))))))) := to_bits w in
    (bool_to_Z a + 2 * 
    (bool_to_Z b + 2 * 
    (bool_to_Z c + 2 * 
    (bool_to_Z d + 2 * 
    (bool_to_Z e + 2 * 
    (bool_to_Z f + 2 * 
    (bool_to_Z g + 2 * 
    bool_to_Z h))))))).

Definition byte_of_Z (z : Z) : byte := of_bits
    (Z.testbit z 0,
    (Z.testbit z 1,
    (Z.testbit z 2,
    (Z.testbit z 3,
    (Z.testbit z 4,
    (Z.testbit z 5,
    (Z.testbit z 6,
    (Z.testbit z 7
    )))))))).

Global Instance BvWf_of_byte w : BvWf 8 (Z_of_byte w).
Proof. by case w. Qed.

Definition bv_of_byte (w : byte) : bv 8 := BV _ (Z_of_byte w).
Definition byte_of_bv (w : bv 8) : byte := byte_of_Z (bv_unsigned w).

Theorem bv_of_byte_of_bv w : bv_of_byte (byte_of_bv w) = w.
Proof.
    apply bv_eq.
    case: w.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
    case; try done.
Qed.

Theorem byte_of_bv_of_byte w : byte_of_bv (bv_of_byte w) = w.
Proof.
    by case w.
Qed.

(* ``bv_to_byte``, as a giant lookup table.
This is more efficient, and avoids annoying computations in proofs. *)
Definition fast_bv_of_byte (w : byte) : bv 8 :=
match w with
| x00 => 0x00
| x01 => 0x01
| x02 => 0x02
| x03 => 0x03
| x04 => 0x04
| x05 => 0x05
| x06 => 0x06
| x07 => 0x07
| x08 => 0x08
| x09 => 0x09
| x0a => 0x0a
| x0b => 0x0b
| x0c => 0x0c
| x0d => 0x0d
| x0e => 0x0e
| x0f => 0x0f
| x10 => 0x10
| x11 => 0x11
| x12 => 0x12
| x13 => 0x13
| x14 => 0x14
| x15 => 0x15
| x16 => 0x16
| x17 => 0x17
| x18 => 0x18
| x19 => 0x19
| x1a => 0x1a
| x1b => 0x1b
| x1c => 0x1c
| x1d => 0x1d
| x1e => 0x1e
| x1f => 0x1f
| x20 => 0x20
| x21 => 0x21
| x22 => 0x22
| x23 => 0x23
| x24 => 0x24
| x25 => 0x25
| x26 => 0x26
| x27 => 0x27
| x28 => 0x28
| x29 => 0x29
| x2a => 0x2a
| x2b => 0x2b
| x2c => 0x2c
| x2d => 0x2d
| x2e => 0x2e
| x2f => 0x2f
| x30 => 0x30
| x31 => 0x31
| x32 => 0x32
| x33 => 0x33
| x34 => 0x34
| x35 => 0x35
| x36 => 0x36
| x37 => 0x37
| x38 => 0x38
| x39 => 0x39
| x3a => 0x3a
| x3b => 0x3b
| x3c => 0x3c
| x3d => 0x3d
| x3e => 0x3e
| x3f => 0x3f
| x40 => 0x40
| x41 => 0x41
| x42 => 0x42
| x43 => 0x43
| x44 => 0x44
| x45 => 0x45
| x46 => 0x46
| x47 => 0x47
| x48 => 0x48
| x49 => 0x49
| x4a => 0x4a
| x4b => 0x4b
| x4c => 0x4c
| x4d => 0x4d
| x4e => 0x4e
| x4f => 0x4f
| x50 => 0x50
| x51 => 0x51
| x52 => 0x52
| x53 => 0x53
| x54 => 0x54
| x55 => 0x55
| x56 => 0x56
| x57 => 0x57
| x58 => 0x58
| x59 => 0x59
| x5a => 0x5a
| x5b => 0x5b
| x5c => 0x5c
| x5d => 0x5d
| x5e => 0x5e
| x5f => 0x5f
| x60 => 0x60
| x61 => 0x61
| x62 => 0x62
| x63 => 0x63
| x64 => 0x64
| x65 => 0x65
| x66 => 0x66
| x67 => 0x67
| x68 => 0x68
| x69 => 0x69
| x6a => 0x6a
| x6b => 0x6b
| x6c => 0x6c
| x6d => 0x6d
| x6e => 0x6e
| x6f => 0x6f
| x70 => 0x70
| x71 => 0x71
| x72 => 0x72
| x73 => 0x73
| x74 => 0x74
| x75 => 0x75
| x76 => 0x76
| x77 => 0x77
| x78 => 0x78
| x79 => 0x79
| x7a => 0x7a
| x7b => 0x7b
| x7c => 0x7c
| x7d => 0x7d
| x7e => 0x7e
| x7f => 0x7f
| x80 => 0x80
| x81 => 0x81
| x82 => 0x82
| x83 => 0x83
| x84 => 0x84
| x85 => 0x85
| x86 => 0x86
| x87 => 0x87
| x88 => 0x88
| x89 => 0x89
| x8a => 0x8a
| x8b => 0x8b
| x8c => 0x8c
| x8d => 0x8d
| x8e => 0x8e
| x8f => 0x8f
| x90 => 0x90
| x91 => 0x91
| x92 => 0x92
| x93 => 0x93
| x94 => 0x94
| x95 => 0x95
| x96 => 0x96
| x97 => 0x97
| x98 => 0x98
| x99 => 0x99
| x9a => 0x9a
| x9b => 0x9b
| x9c => 0x9c
| x9d => 0x9d
| x9e => 0x9e
| x9f => 0x9f
| xa0 => 0xa0
| xa1 => 0xa1
| xa2 => 0xa2
| xa3 => 0xa3
| xa4 => 0xa4
| xa5 => 0xa5
| xa6 => 0xa6
| xa7 => 0xa7
| xa8 => 0xa8
| xa9 => 0xa9
| xaa => 0xaa
| xab => 0xab
| xac => 0xac
| xad => 0xad
| xae => 0xae
| xaf => 0xaf
| xb0 => 0xb0
| xb1 => 0xb1
| xb2 => 0xb2
| xb3 => 0xb3
| xb4 => 0xb4
| xb5 => 0xb5
| xb6 => 0xb6
| xb7 => 0xb7
| xb8 => 0xb8
| xb9 => 0xb9
| xba => 0xba
| xbb => 0xbb
| xbc => 0xbc
| xbd => 0xbd
| xbe => 0xbe
| xbf => 0xbf
| xc0 => 0xc0
| xc1 => 0xc1
| xc2 => 0xc2
| xc3 => 0xc3
| xc4 => 0xc4
| xc5 => 0xc5
| xc6 => 0xc6
| xc7 => 0xc7
| xc8 => 0xc8
| xc9 => 0xc9
| xca => 0xca
| xcb => 0xcb
| xcc => 0xcc
| xcd => 0xcd
| xce => 0xce
| xcf => 0xcf
| xd0 => 0xd0
| xd1 => 0xd1
| xd2 => 0xd2
| xd3 => 0xd3
| xd4 => 0xd4
| xd5 => 0xd5
| xd6 => 0xd6
| xd7 => 0xd7
| xd8 => 0xd8
| xd9 => 0xd9
| xda => 0xda
| xdb => 0xdb
| xdc => 0xdc
| xdd => 0xdd
| xde => 0xde
| xdf => 0xdf
| xe0 => 0xe0
| xe1 => 0xe1
| xe2 => 0xe2
| xe3 => 0xe3
| xe4 => 0xe4
| xe5 => 0xe5
| xe6 => 0xe6
| xe7 => 0xe7
| xe8 => 0xe8
| xe9 => 0xe9
| xea => 0xea
| xeb => 0xeb
| xec => 0xec
| xed => 0xed
| xee => 0xee
| xef => 0xef
| xf0 => 0xf0
| xf1 => 0xf1
| xf2 => 0xf2
| xf3 => 0xf3
| xf4 => 0xf4
| xf5 => 0xf5
| xf6 => 0xf6
| xf7 => 0xf7
| xf8 => 0xf8
| xf9 => 0xf9
| xfa => 0xfa
| xfb => 0xfb
| xfc => 0xfc
| xfd => 0xfd
| xfe => 0xfe
| xff => 0xff
end.

Theorem bv_of_byte_speedup w : bv_of_byte w = fast_bv_of_byte w.
Proof.
    case w; compute; by apply bv_eq.
Qed.
