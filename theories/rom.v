(*|
============
Dragster ROM
============

|*)

From Coq Require List.
Import Byte List.ListNotations.

(*|

The Dragster ROM, as a list of 2048 bytes.

You'll notice I'm using the ``byte`` type, instead of ``bv 8``.
They're equivalent, but this seems to compile two orders of magnitude faster.
So it's worth the annoyance of converting back and forth.

|*)

Definition ROM_list : list byte := [
    x78;xd8;xa2;x00; xa9;x00;x95;x00; x9a;xe8;xd0;xfa; xa5;x82;xd0;x03;
    x4c;xfd;xf2;x20; xd3;xf6;xa2;x06; xbd;xca;xf6;x45; x84;x25;x85;x95;
    x86;xca;x10;xf4; xea;xea;xea;xea; xea;xa6;x8f;x38; xa0;x00;xb5;xba;
    xc8;xe9;x03;x10; xfb;x88;x38;x98; xa0;x00;xc8;xe9; x05;x10;xfb;x88;
    x94;xbc;x69;x05; x95;xbe;xad;x84; x02;xd0;xfb;x85; x02;x85;x01;x85;
    xaa;xa6;xaa;xb5; xba;x20;xe5;xf4; xa6;xaa;xa9;x03; x85;x04;x85;x05;
    xb4;xc4;xb9;xc0; xf6;x85;x02;x85; x0d;x85;x0f;xb9; xc4;xf6;x85;x0e;
    x20;xd0;xf7;xa0; x05;x85;x02;x88; x10;xfb;xa6;xaa; xb4;xbc;x88;x10;
    xfd;xb4;xbe;xc0; x04;xf0;x0e;xc0; x03;xf0;x0d;xc0; x02;xf0;x0c;xc0;
    x01;xf0;x0b;xd0; x0b;xea;xa5;xd8; xea;xa5;xd8;xea; xa5;xd8;xa5;xd8;
    xea;xea;xa9;x16; x85;x8e;x18;xa4; x8e;xb1;x90;x85; x1b;xb1;x92;x85;
    x1c;xb1;x94;x85; x1b;xb1;x9a;x85; xd8;xb1;x98;xaa; xb1;x96;xa4;xd8;
    x85;x1c;x86;x1b; x84;x1c;x85;x1b; xa5;xd8;xea;xa5; x8e;x4a;x4a;x4a;
    xa8;xb9;xd0;xf6; x85;x0d;x85;x0e; x85;x0f;xa4;x8e; xb1;x90;x85;x1b;
    xb1;x92;x85;x1c; xb1;x94;x85;x1b; xb1;x96;xa4;xd8; x85;x1c;x86;x1b;
    x84;x1c;x85;x1b; xea;xea;xea;xc6; x8e;x10;xac;xa2; x01;xa0;x00;x84;
    x1b;x84;x1c;xca; x10;xf7;x86;x02; xa5;x88;x85;x09; xa2;x09;x85;x02;
    xa9;xf7;x95;x90; xca;xca;x10;xf6; xa5;x89;x85;x09; xa9;x02;x85;x0a;
    xa5;x8a;x85;x06; xa5;x8b;x85;x07; xa6;xaa;xa0;x07; x85;x02;xb5;x9c;
    x85;x0d;xb5;x9e; x85;x0e;xb5;xa0; x85;x0f;xa5;xd8; xb5;xa2;x85;x0d;
    xa5;xd8;xb5;xa4; x85;x0e;xa5;xd8; xb5;xa6;x85;x0f; x88;x10;xdd;x85;
    x02;xc8;x84;x0d; x84;x0e;x84;x0f; xa9;x10;x85;x0a; xa5;x86;x85;x06;
    x85;x07;xa9;x0f; x20;xe5;xf4;xa9; x06;x85;x04;xa9; x01;x85;x05;xa6;
    xaa;xb4;xd4;x85; x02;xf0;x0a;x20; x3b;xf5;x85;x02; x85;x02;x4c;x09;
    xf2;xa5;x8c;x85; x08;xa6;xaa;xa0; x68;xb5;xb3;xf0; x08;xa0;x50;x29;
    xf0;xf0;x02;x4a; xa8;x85;x02;x98; x85;x90;xb5;xb3; x29;x0f;x0a;x0a;
    x0a;x85;x92;xb5; xb5;x29;xf0;x4a; x85;x96;xa5;x8d; xf0;x08;x29;xf0;
    x4a;x69;x08;x4c; xbd;xf1;xb5;xb5; x29;x0f;x0a;x0a; x0a;x85;x94;xa9;
    x0c;xb4;xcc;x30; x05;x98;xd0;x02; xa9;x0b;x0a;x0a; x0a;x85;x98;xa9;
    x07;xb4;xb5;xc0; xaa;xd0;x02;xa9; x0a;xaa;xa0;x07; x85;x02;xea;xb1;
    x92;x85;x1c;xb1; x90;x85;x1b;xb1; x96;x85;x1c;xb1; x94;x85;x1b;x85;
    x1c;xb1;x98;x85; x1b;x85;x1c;xbd; x6a;xf5;x85;x1f; xca;x88;x10;xdc;
    xc8;x84;x1b;x84; x1c;x84;x1b;x84; x1f;xa5;x88;x85; x08;xe6;xaa;xa5;
    xaa;x4a;x90;x03; x4c;x51;xf0;xa9; x0f;x20;xe5;xf4; xa0;x39;x20;x3b;
    xf5;xa9;x21;x8d; x96;x02;xa5;x81; x29;x01;xaa;x86; x8f;xa0;x00;xa5;
    xb9;x30;x4c;xb5; xd2;xd0;x48;xb5; xd0;xf0;x07;xa0; x08;xd6;xd0;x4c;
    x4e;xf2;xa5;x8d; xf0;x11;x29;x0f; xd0;x0d;xa0;x0c; xa9;x18;x95;x19;
    x94;x17;x94;x15; x4c;x85;xf2;xb5; xce;xd0;x24;xa5; x81;x29;x02;xf0;
    x10;xa0;x09;xa9; x01;x95;x17;xb5; xc0;xf0;x06;xb5; xc8;x15;xca;xd0;
    x0e;xb5;xa8;xc9; x20;x90;x02;xa9; x1f;x49;x1f;x95; x17;xa0;x03;x94;
    x15;xb5;xb1;x95; x19;xad;x84;x02; xd0;xfb;xa0;x82; x84;x02;x84;x01;
    x84;x00;x84;x02; x84;x02;x84;x02; x85;x00;xe6;x81; xd0;x07;xe6;xb9;
    xd0;x03;x38;x66; xb9;xa0;xff;xad; x82;x02;x29;x08; xd0;x02;xa0;x0f;
    xa9;x00;x24;xb9; x10;x07;x98;x29; xf7;xa8;xa5;xb9; x0a;x85;x84;x84;
    x85;xa9;x19;x85; x02;x8d;x96;x02; xad;x80;x02;xa8; x29;x0f;x85;xae;
    x98;x4a;x4a;x4a; x4a;x85;xad;xa5; xa8;x05;xa9;xd0; x06;xb5;xad;xc9;
    x07;xf0;x06;xad; x82;x02;x4a;xb0; x05;xa2;xb9;x4c; x04;xf0;xa0;x00;
    x4a;xb0;x29;xa5; xb0;xf0;x04;xc6; xb0;x10;x23;xe6; x80;xa5;x80;x29;
    x01;x85;x80;x85; xb9;xa8;xc8;x84; xcc;x20;xd3;xf6; xa9;x0a;x85;xcd;
    xa9;x00;x85;x8d; x85;xd4;xa0;x1e; x84;xd2;x84;xd3; x84;xb0;xa5;x8d;
    xf0;x0c;xc6;x8d; xd0;x08;xa2;x05; x4a;x95;xb3;xca; x10;xfb;xa6;x8f;
    xa5;xb9;x30;x0d; xb5;xd2;xf0;x0c; xa0;x01;x94;xd2; x88;x94;xa8;x94;
    xc8;x4c;xa4;xf4; xa5;x8d;xd0;x1f; xf8;x18;xb5;xb7; x69;x34;x95;xb7;
    xb5;xb5;x69;x03; x95;xb5;xb5;xb3; x69;x00;x95;xb3; xd8;x90;x08;xa9;
    x99;x95;xb3;x95; xb5;xd0;xd1;xb5; xc0;xf0;x35;x18; x75;xc2;x95;xc2;
    x90;x02;xf6;xba; xb5;xc0;x2a;x2a; x2a;x29;x03;xa8; xb9;xc8;xf6;x25;
    x81;xd0;x0f;xf6; xc4;x18;xb5;xc6; x69;x17;xc9;x2f; x90;x02;xa9;x00;
    x95;xc6;xb5;xc4; x29;x03;x95;xc4; xb5;xba;xc9;x60; x90;x02;xd0;xc5;
    xb5;xce;xd0;x2b; xa5;x81;xb4;xcc; x10;x02;xa0;x00; x39;xf6;xf6;xd0;
    x50;xb5;x0c;x30; x1c;xb5;xca;xf0; x06;xa5;x81;x29; x02;xf0;x12;x18;
    xb5;xa8;x79;xfb; xf6;x95;xa8;xa9; x0c;x95;xb1;x85; xb9;xd0;x14;xd0;
    x6a;x38;xb5;xa8; xf9;xfb;xf6;x95; xa8;xd6;xb1;xa9; x04;xd5;xb1;x90;
    x02;x95;xb1;xb5; xa8;x10;x02;xa9; x00;xc9;x20;x90; x12;xa9;x0f;x95;
    xd0;xa9;x01;x95; xd4;xa9;x04;x95; xab;xa9;x1a;x95; xce;xa9;x00;x95;
    xa8;xa9;x00;x95; xc8;x98;xf0;x33; xb5;xa8;xc9;x14; x88;xf0;x04;x2a;
    x4c;x0c;xf4;x85; xd8;xd5;xc0;xf0; x22;xb0;x09;xb5; xc0;xf0;x1c;xd6;
    xc0;x4c;x3b;xf4; xa5;xd8;x38;xf5; xc0;xf6;xc0;xf6; xc0;xc9;x10;x90;
    x0a;xb5;xce;xd0; x06;xa9;x17;x95; xc8;xd6;xa8;xb5; xad;x29;x04;xd5;
    xd6;x95;xd6;xf0; x21;xc9;x00;xd0; x07;x16;xcc;x38; x76;xcc;x30;x16;
    xa5;x8d;xf0;x04; xa9;x1d;x95;xd4; xf6;xcc;xb5;xcc; x29;x7f;xc9;x04;
    x90;x02;xa9;x04; x95;xcc;xa5;x80; x4a;x90;x39;xb5; xce;xd0;x35;xb5;
    xc0;xf0;x31;xa5; x81;x29;x06;xd0; x2b;xb5;xad;x4a; xb0;x02;xd6;xab;
    x4a;xb0;x02;xf6; xab;xa5;x82;x10; x04;xf6;xab;xf6; xab;xd6;xab;xa9;
    x00;x95;xca;xb4; xab;x10;x03;xa8; xf6;xca;xc0;x08; x90;x04;xa0;x08;
    xf6;xca;x94;xab; xa5;x82;x0a;x0a; x0a;x45;x82;x0a; x26;x82;x8a;x09;
    x0a;xa8;xa9;x00; x99;x9c;x00;x88; x88;x10;xf9;xb4; xa8;xc0;x13;x90;
    x10;x98;xe9;x13; xa8;xa9;xff;x95; x9c;x95;x9e;x95; xa0;x8a;x09;x06;
    xaa;x88;x30;x0e; xb5;x9c;x09;x08; x0a;x95;x9c;x76; x9e;x36;xa0;x4c;
    xd1;xf4;x4c;x16; xf0;x85;xd9;xa2; x00;x85;x2b;xa4; x8c;x84;x02;x84;
    x09;x18;x69;x2e; xa8;x29;x0f;x85; xd8;x98;x4a;x4a; x4a;x4a;xa8;x18;
    x65;xd8;xc9;x0f; x90;x03;xe9;x0f; xc8;x49;x07;x0a; x0a;x0a;x0a;x95;
    x20;x85;x02;x88; x10;xfd;x95;x10; xa5;xd9;x18;x69; x08;xe8;xe0;x02;
    x90;xc9;x85;x02; x85;x2a;xa5;x89; x85;x02;x85;x09; x60;xb9;xc5;xf7;
    x99;x91;x00;x88; x88;x30;x03;x4c; xd2;xf7;x60;xa9; x01;x85;x04;x85;
    x02;xa2;x06;x85; x02;xc8;xb9;x6e; xf7;x85;x1b;xb9; x75;xf7;x85;x1c;
    xb9;x7c;xf7;x85; x1b;xb9;x83;xf7; xea;x85;x1c;x85; x1b;xca;x10;xe3;
    xe8;x86;x1b;x86; x1c;x86;x1b;x85; x02;x60;x02;x02; x02;x02;x00;x00;
    x00;x00;x00;x00; x00;x00;x07;x1f; x3f;x7e;x7d;xfd; xef;xf7;xfe;x7e;
    x7d;x3f;x1f;x07; x01;x00;x00;x00; x00;x00;x00;x00; x00;x07;x1f;x3f;
    x77;x77;xfb;xff; xff;xfb;x77;x7f; x3f;x1f;x07;x01; x00;x00;x00;x00;
    x00;x00;x00;x00; x07;x1f;x3f;x7f; x6f;xf6;xfb;xff; xfd;x7b;x77;x3f;
    x1f;x07;x01;x00; x00;x00;x00;x00; x00;x00;x00;x80; xe0;xf7;xfb;xfb;
    xff;xbf;xdf;xfd; xfa;xfa;xf6;xec; xb8;xe0;x00;x00; x00;x00;x00;x00;
    x00;x00;x80;xe0; xf7;xfb;xbb;x7f; xff;xff;x7d;xba; xba;xf6;xec;xb8;
    xe0;x00;x00;x00; x00;x00;x00;x00; x00;x80;xe0;xf7; xbb;x7b;xff;xff;
    x7f;xbd;xda;xfa; xf6;xec;xb8;xe0; x00;x00;x00;x00; x00;x00;x00;x00;
    x00;x00;x00;x00; x00;x00;x00;x00; x44;x22;xee;xf7; xfb;xfd;xff;xef;
    xe8;xf8;x00;x00; x00;x00;x00;x00; x00;x00;x00;x00; x00;x00;x00;x00;
    x00;x20;x92;xe1; xf6;xfb;xfb;xff; xef;xe0;x00;x00; x00;x00;x00;x00;
    x00;x00;x00;x00; x00;x00;x40;x20; xef;x74;xba;xdd; xff;xff;x00;x00;
    x00;x00;x00;x00; x00;x00;x00;x00; x00;x00;x00;x00; x00;x00;x00;x00;
    x00;x20;x10;x60; xb6;xbb;xfa;xff; x0f;x00;x00;x00; x00;x00;x00;x00;
    x00;x00;x00;x00; x00;x00;xff;x00; xff;x80;x80;x80; x00;x00;x00;x00;
    x00;x00;x00;x00; x00;x00;x00;x00; x00;x00;x00;x00; x00;x00;x00;x00;
    x00;x00;x00;xf0; x0e;xe1;x1f;x00; x00;x00;x00;x00; x00;x00;x00;x00;
    x00;x00;x30;x78; xfc;xfe;xfa;x34; x18;x00;x00;x00; x00;x00;x00;x00;
    x00;x00;x00;x00; x00;x00;x00;x00; x00;x00;x00;x00; x00;x00;x00;x00;
    x00;x60;xf0;xf8; xfc;xf4;x68;x30; x00;x00;x00;x00; x00;x00;x00;x00;
    x77;xbb;xdd;xee; xee;xdd;xbb;x77; x06;x02;x00;x00; x88;xcc;xd8;x46;
    x00;x00;xff;xa9; x9f;x85;x8d;xa2; x01;xa9;x01;x95; x25;x85;x82;xa9;
    xaa;x95;xb3;x95; xb5;xa9;x04;x95; xab;x95;xd6;x95; xb1;xca;x10;xe9;
    xaa;xa9;x23;x4c; xe9;xf4;x00;x00; x02;x06;x0e;x03; x01;x01;x01;x01;
    x3c;x66;x66;x66; x66;x66;x66;x3c; x7e;x18;x18;x18; x18;x78;x38;x18;
    x7e;x60;x60;x3c; x06;x06;x46;x3c; x3c;x46;x06;x0c; x0c;x06;x46;x3c;
    x0c;x0c;x0c;x7e; x4c;x2c;x1c;x0c; x7c;x46;x06;x06; x7c;x60;x60;x7e;
    x3c;x66;x66;x66; x7c;x60;x62;x3c; x18;x18;x18;x18; x0c;x06;x42;x7e;
    x3c;x66;x66;x3c; x3c;x66;x66;x3c; x3c;x46;x06;x3e; x66;x66;x66;x3c;
    x00;x00;x00;x00; x00;x00;x00;x00; xc3;xc7;xcf;xdf; xfb;xf3;xe3;xc3;
    x7e;xc3;xc0;xc0; xc0;xc0;xc3;x7e; x7e;xc3;xc3;xcf; xc0;xc0;xc3;x7e;
    xf2;x4a;x4a;x72; x4a;x4a;xf3;x0e; x11;x11;x11;x11; x11;xce;x45;x45;
    x45;x45;x55;x6d; x45;x10;x90;x50; x30;x10;x10;x10; xf8;x81;x82;xe2;
    x83;x82;xfa;x8f; x48;x28;x2f;xea; x29;x28;x21;xa1; xa0;x20;x20;x20;
    xbe;x10;x10;xa0; x40;x40;x40;x40; x0f;x41;xed;xa9; xe9;xa9;xad;xf0;
    x11;x53;x56;x5c; x58;x50;xfe;x80; x3a;xa2;xba;x8a; xba;x00;x00;xe9;
    xad;xaf;xab;xe9; x6e;xf5;xb3;xf5; x00;xf6;x2e;xf6; x5c;xf6;x8a;xf6;
    xa0;x0a;xb9;xc4; xf7;x18;x75;xab; xc0;x04;x90;x15; x18;x75;xc8;xc0;
    x08;xb0;x11;x85; xd8;xb5;xce;xf0; x03;x79;xf2;xf6; x65;xd8;x4c;xf4;
    xf7;x18;x75;xc6; x99;x90;x00;x4c; x2d;xf5;x00;x00; x00;xf0;x00;x00].

(*|

Next, I translate this to a function ``bv 11 -> bv 8``,
as that's what I need in practice.

|*)


From stdpp Require Import ssreflect unstable.bitvector.
From theories Require Import utils.

Definition ROM (addr : bv 11) : bv 8
    := bv_of_byte (ROM_list !!! (Z.to_nat (bv_unsigned addr))).

(*|

But that definition feels a bit sketchy.
Or at least, less obviously correct than I'd hope.
There's a lot of implicit default behavior going on.

* ``Z.to_nat`` returns zero on negative numbers.
* ``!!!`` returns ``inhabitant`` when the index is out of range.

So I prove something that more clearly states ROM's behavior.

|*)

Theorem ROM_spec (addr : bv 11) :
    exists n : nat, Z_of_nat n = bv_unsigned addr /\
    option_map bv_of_byte (ROM_list !! n) = Some (ROM addr).
Proof.
    exists (Z.to_nat (bv_unsigned addr)).
    split.
    - apply Z2Nat.id.
        move: (bv_is_wf addr) => /bv_wf_in_range [// _].
    - rewrite /ROM list_lookup_total_alt.
        set w := ROM_list !! Z.to_nat (bv_unsigned addr).
        have: is_Some w.
        {
            apply lookup_lt_is_Some.
            move: (bv_is_wf addr) =>
                /bv_wf_in_range [pf1 /Z2Nat.inj_lt pf2].
            apply pf2.
            - exact pf1.
            - apply Z.lt_le_incl.
                apply bv_modulus_pos.
        }
        case: w => [w|].
        + done.
        + move=> [_ //].
Qed.
