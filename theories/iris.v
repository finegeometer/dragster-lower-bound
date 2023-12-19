(*|
================
Iris Logic Setup
================

How does one reason about the behavior of imperative code?

A standard method is *Hoare logic*. The idea is as follows:

* Before and after every line of code,
  we describe a condition that must hold.
* We can then *locally* check that everything is consistent.
  If the precondition holds before running a statement,
  then the statement must run without crashing,
  and the postcondition must hold afterwards.

Hoare logic has a refinement called *separation logic*.
It adds a new logical operator, called the separating conjunction.
Roughly, while ``(addr1 ↦ val1) ∧ (addr2 ↦ val2)``
allows the two addresses to be the same,
``(addr1 ↦ val1) ∗ (addr2 ↦ val2)`` does not.
You can also vew this as tracking ownership of memory;
if I own the value at ``addr1``, and you own the value at ``addr2``,
then they can't be the same address.

This vastly simplifies the specification of writing to memory.
It also helps analyze concurrent code,
but I don't care about that right now.

Coq has a nice separation logic implementation,
called `Iris <https://iris-project.org/>`_. So let's use it!

An important point: While Iris is a big part of the proof,
it is *not* part of the claim I'm proving. So, since Coq verifies
that the proof is correct, it is *not necessary* to trust
the authors of the Iris library! If they did something wrong,
Coq would either reject their proofs, reject *my* proof,
or turn up something suspicious when I run ``Print Assumptions``
in ``main.v``.

--------
Language
--------

Iris is designed to be used for programming languages,
which have statements and expressions and so forth.
But I want to use it for a machine language. What do I do?

Here's a cool trick. Imagine an expression-based language
with a single expression. Attempting to reduce that expression
will return that same expression, with the side-effect of running
one machine instruction. Then trying to run the program to completion
will repeatedly run machine instructions. In other words,
it will simulate the behavior of the Atari.

I implement this strategy, with one tweak.
If the machine state says that the Dragster has been beaten in
less than 5.57 seconds, reducing the expression will crash.
This means that if the program cannot crash,
the game cannot be beaten in less than 5.57 seconds!

|*)

From iris.program_logic Require Import language.
From theories Require Import spec.

(* There is exactly one expression. *)
Inductive expr := Expr.
(* The expression never finishes reducing, so there are no values. *)
Inductive val :=.
(* I don't actually know what this does, but it's required. *)
Inductive observation :=.

Definition of_val (v : val) : expr := Expr.
Definition to_val (e : expr) : option val := None.

Definition claim (s : state) : Prop :=
    forall p, player_has_won s p ->
    exists t, timer_in_hundredths s p t /\ (t >=? 557)%Z.

(* Allow the unique expression to reduce to itself if
the game has not been beaten in less than 5.57 seconds.
Reduction causes the state to be updated by running
one machine instruction, and does not fork off any new threads.
|*)
Definition prim_step (e : expr) (s : state) (κs : list observation)
    (e' : expr) (s' : state) (efs : list expr) : Prop :=
    claim s /\ step s s' /\ efs = [].

Lemma lang_mixin : LanguageMixin of_val to_val prim_step.
Proof. done. Qed.
Canonical Structure lang := Language lang_mixin.

(*|

I claimed above that if evaluating the expression cannot crash,
Dragster cannot be beaten in less than 5.57 seconds. Let's prove this.

|*)

From stdpp Require Import unstable.bitvector_tactics.

Lemma initial_claim s : initial s -> claim s.
Proof.
    rewrite /claim /player_has_won /someone_has_won.
    move=> [_ [? [? [-> [-> ->]]]]].
    move=> ? [_ [contra _]].
    exfalso; move: contra.
    clear.
    have ->: (trunc 11 (0xfffc : bv 16) = 0x7fc)%bv by bv_simplify.
    have ->: (trunc 11 (0xfffd : bv 16) = 0x7fd)%bv by bv_simplify.
    by compute.
Qed.

Theorem no_crash_implies_goal :
    (forall s0, initial s0 ->
        forall s, rtc erased_step ([Expr], s0) ([Expr], s) ->
            not_stuck Expr s) ->
    Goal.
Proof.
    move=> H s0 s0_initial s reachable; fold (claim s).
    specialize (H s0 s0_initial).

    eapply (rtc_ind_r
        (fun s => claim s /\ rtc erased_step ([Expr], s0) ([Expr], s))
    ); last exact reachable.
    - split.
        + by apply initial_claim.
        + constructor.
    - clear reachable => s1 s2 reachable σ [IH1 IH2].
        suff: rtc erased_step ([Expr], s0) ([Expr], s2).
        {
            split; last done.
            suff: not_stuck Expr s2
                by case => [[_ //]|[_ [[] [_ [_ [// _]]]]]].
            by apply H.
        }

        eapply rtc_r.
        + exact IH2.
        + exists [].
            by apply (step_atomic _ _ _ _ [] [] [] eq_refl eq_refl).
Qed.

(*|

-----
Logic
-----

Now that the language has been created,
let's connect it to the Iris logic.

I find this difficult to explain, possibly because I don't
fully understand it myself. But I'll do my best.

Here's the idea.

Iris has a concept of "ghost state", which is an abstract ... thing ...
that you can own. After describing some available ghost state,
we split it into two parts; one owned by the state,
and one owned by the user of the logic.

|*)

From stdpp Require Import finite.
From iris.algebra Require Export excl_auth functions.
From iris.base_logic.lib Require Import own.

(*|

To begin, I define a type of places values can be stored,
along with the type of value stored there.
I also explain to Coq how to tell if two places are the same or not.

|*)

Inductive byte_place := 
| RAM (addr : bv 7)
| Reg (r : reg)
.
Inductive place :=
| BytePlace of byte_place
| PC
| Flag of flag
.
Coercion BytePlace : byte_place >-> place.

Definition place_data (p : place) : Set :=
    match p with
    | BytePlace _ => bv 8
    | PC => bv 16
    | Flag _ => bool
    end.

Global Instance byte_place_eq_def : EqDecision byte_place.
Proof.
    case=> [a1|r1]; case=> [a2|r2].
    - case (decide (a1 = a2)).
        + by left; apply f_equal.
        + by right=> eq; inversion eq.
    - by right.
    - by right.
    - case (decide (r1 = r2)).
        + by left; apply f_equal.
        + by right=> eq; inversion eq.
Defined.

Global Instance place_eq_def : EqDecision place.
Proof.
    case=> [b1||f1]; case=> [b2||f2].
    - case (decide (b1 = b2)).
        + by left; apply f_equal.
        + by right=> eq; inversion eq.
    - by right.
    - by right.
    - by right.
    - by left.
    - by right.
    - by right.
    - by right.
    - case (decide (f1 = f2)).
        + by left; apply f_equal.
        + by right=> eq; inversion eq.
Defined.

Global Program Instance byte_place_finite : Finite byte_place := {|
    enum := Reg X :: Reg Y :: Reg A :: Reg SP :: (RAM <$> enum (bv 7));
|}.
Next Obligation.
Proof.
    constructor.
    {
        do 3 (case /elem_of_cons; first done).
        move=> tmp; apply elem_of_list_fmap_2 in tmp; move: tmp.
        move=> [_ [// _]].
    }
    constructor.
    {
        do 2 (case /elem_of_cons; first done).
        move=> tmp; apply elem_of_list_fmap_2 in tmp; move: tmp.
        move=> [_ [// _]].
    }
    constructor.
    {
        do 1 (case /elem_of_cons; first done).
        move=> tmp; apply elem_of_list_fmap_2 in tmp; move: tmp.
        move=> [_ [// _]].
    }
    constructor.
    {
        do 0 (case /elem_of_cons; first done).
        move=> tmp; apply elem_of_list_fmap_2 in tmp; move: tmp.
        move=> [_ [// _]].
    }
    apply NoDup_fmap_2; last apply NoDup_enum.
    by move=> x y eq; inversion eq.
Qed.
Next Obligation.
Proof.
    case; last case; do 4 constructor.
    apply elem_of_list_fmap_1.
    apply elem_of_enum.
Qed.

Global Program Instance place_finite : Finite place := {|
    enum := PC
        :: Flag spec.N 
        :: Flag spec.B 
        :: Flag spec.V 
        :: Flag spec.D 
        :: Flag spec.I 
        :: Flag spec.Z 
        :: Flag spec.C
        :: (BytePlace <$> enum byte_place);
|}.
Next Obligation.
Proof.
    constructor.
    {
        do 7 (case /elem_of_cons; first done).
        move=> tmp; apply elem_of_list_fmap_2 in tmp; move: tmp.
        move=> [_ [// _]].
    }
    constructor.
    {
        do 6 (case /elem_of_cons; first done).
        move=> tmp; apply elem_of_list_fmap_2 in tmp; move: tmp.
        move=> [_ [// _]].
    }
    constructor.
    {
        do 5 (case /elem_of_cons; first done).
        move=> tmp; apply elem_of_list_fmap_2 in tmp; move: tmp.
        move=> [_ [// _]].
    }
    constructor.
    {
        do 4 (case /elem_of_cons; first done).
        move=> tmp; apply elem_of_list_fmap_2 in tmp; move: tmp.
        move=> [_ [// _]].
    }
    constructor.
    {
        do 3 (case /elem_of_cons; first done).
        move=> tmp; apply elem_of_list_fmap_2 in tmp; move: tmp.
        move=> [_ [// _]].
    }
    constructor.
    {
        do 2 (case /elem_of_cons; first done).
        move=> tmp; apply elem_of_list_fmap_2 in tmp; move: tmp.
        move=> [_ [// _]].
    }
    constructor.
    {
        do 1 (case /elem_of_cons; first done).
        move=> tmp; apply elem_of_list_fmap_2 in tmp; move: tmp.
        move=> [_ [// _]].
    }
    constructor.
    {
        do 0 (case /elem_of_cons; first done).
        move=> tmp; apply elem_of_list_fmap_2 in tmp; move: tmp.
        move=> [_ [// _]].
    }
    apply NoDup_fmap_2; last apply NoDup_enum.
    by move=> x y eq; inversion eq.
Qed.
Next Obligation.
Proof.
    case; last case; do 8 constructor.
    apply elem_of_list_fmap_1.
    apply elem_of_enum.
Qed.


(*|

Now, I define the relevant ghost state.

I use a very specific, but useful, type of ghost state.
Iris calls it "ExclAuth". The idea is as follows:

* The state is a pair of propositions, ``◯E x`` and ``●E x``.
* These propositions are "entangled", in the sense that
  if you own ``◯E x``, and someone else owns ``●E y``, then ``x = y``.

I define one such pair for each place a value can be stored.

|*)

Definition atari_camera :=
    discrete_funR (fun p => excl_authUR (leibnizO (place_data p))).

Class atariGpreS (Σ : gFunctors) := {
    atari_data :: inG Σ atari_camera;
}.
Class atariGS (Σ : gFunctors) := {
    atari_inG :: atariGpreS Σ;
    atari_name : gname;
}.

(*|

I now let the state own the ``●`` part, and the user own the ``◯`` part.
The entanglement then allows the user's assertions
to talk about the Atari's state.

|*)

Definition state_interp_help `{!atariGS Σ} (s : state) : atari_camera :=
    fun p => ●E match p return leibnizO (place_data p) with
    | RAM a => spec.RAM s a
    | Reg r => spec.Reg s r
    | PC => spec.PC s
    | Flag f => spec.Flag s f
    end.

Definition state_interp `{!atariGS Σ} (s : state) : iProp Σ :=
    own atari_name (state_interp_help s).


(*|

The user will want to discuss the state in terms of assertions like
``Reg X ↦ 0x00%bv``. Let's implement that.

|*)

Section pointsto.
    Context `{!atariGS Σ}.

    Definition pointsto_fun (l : place) (v : place_data l) :
        atari_camera.
        eapply discrete_fun_singleton.
        refine (◯E _).
        exact v.
    Defined.
    Definition pointsto_def (l : place) (v : place_data l) : iProp Σ :=
        own atari_name (pointsto_fun l v).

    Definition pointsto_aux : seal (@pointsto_def). by eexists. Qed.
    Definition pointsto := pointsto_aux.(unseal).
    Definition pointsto_eq : @pointsto = @pointsto_def :=
        pointsto_aux.(seal_eq).
End pointsto.
Notation "l ↦ v" := (pointsto l v)
  (at level 20, format "l  ↦  v") : bi_scope.

(*|

Or sometimes you just want ownership of the location, without caring what's stored there.

|*)

Notation "l ↦ ?" := (∃ v, l ↦ v)%I
  (at level 20, format "l  ↦ ?") : bi_scope.

(*|

-------
Startup
-------

When the Atari boots up, what do we know?

* The program counter points to the value stored at 0xFFFC and 0xFFFD,
  which happens to be 0xF000.
* The interrupt disable flag is set.
* Everything else points to *something*, but we don't know what.

|*)

Definition init `{!atariGS Σ} : iProp Σ :=
    PC ↦ 0xf000%bv
    ∗ Reg X ↦ ?
    ∗ Reg Y ↦ ?
    ∗ Reg A ↦ ?
    ∗ Reg SP ↦ ?
    ∗ Flag spec.N ↦ ?
    ∗ Flag spec.B ↦ ?
    ∗ Flag spec.V ↦ ?
    ∗ Flag spec.D ↦ ?
    ∗ Flag spec.I ↦ true
    ∗ Flag spec.Z ↦ ?
    ∗ Flag spec.C ↦ ?
    ∗ [∗ list] addr ∈ enum (bv 7), RAM addr ↦ ?
    .

(*|

A few lemmas, for the correctness proof.

|*)

Lemma discrete_fun_lookup_big_opL {A : Type} {B : A → ucmra} {X : Type}
    (f : X -> discrete_fun B) (l : list X) (a : A) :
    ([^op list] x ∈ l, f x) a = ([^op list] x ∈ l, f x a).
Proof.
    induction l as [|x l IH].
    - done.
    - simpl.
        by rewrite discrete_fun_lookup_op IH.
Qed.

Lemma split_into_pointers `{!atariGS Σ}
    (f : forall p, leibnizO (place_data p)) :
    own atari_name ((fun p => ◯E (f p)) : atari_camera) ⊣⊢
    [∗ list] p ∈ enum place, p ↦ f p.
Proof.
    rewrite pointsto_eq -big_opL_own; last done.
    apply own_proper.
    move=> p.
    rewrite discrete_fun_lookup_big_opL.

    (* Well, this is an annoying proof. *)
    pose (NoDup_enum place) as tmp; move: tmp.
    induction (elem_of_enum p) as [p l|p q l elem IH].
    - rewrite NoDup_cons big_opL_cons.
        move=> [notin nodup].
        have <-: (ε = [^op list] x ∈ l, pointsto_fun x (f x) p).
        {
            move: notin.
            clear.
            induction l as [|q l IH].
            - move=> //.
            - move=> notin.
                rewrite big_opL_cons.
                rewrite /pointsto_fun discrete_fun_lookup_singleton_ne;
                    first rewrite -IH.
                + done.
                + move=> elem; apply notin; by constructor.
                + move=> eq; apply notin; rewrite eq; constructor.
        }
        rewrite ucmra_unit_right_id.
        rewrite /pointsto_fun.
        by rewrite discrete_fun_lookup_singleton.
    - rewrite NoDup_cons big_opL_cons.
        move=> [notin /IH <-].
        rewrite /pointsto_fun.
        rewrite discrete_fun_lookup_singleton_ne.
        + by rewrite ucmra_unit_left_id.
        + by move=> eq; rewrite eq in notin.
Qed.

(*|

The correctness statement is a bit more complicated
than you might expect. That's because we're booting up
not just the Atari, but the Iris machinery as well.

|*)

From iris.proofmode Require Import proofmode.

Theorem atari_init `{!atariGpreS Σ} s (s_initial : initial s) :
    ⊢ |==> ∃ _ : atariGS Σ, state_interp s ∗ init.
Proof.
    (* Define a ghost resource. *)
    set f : forall p, leibnizO (place_data p) := fun p =>
        match p return leibnizO (place_data p) with
        | RAM a => spec.RAM s a
        | Reg r => spec.Reg s r
        | PC => spec.PC s
        | Flag f => spec.Flag s f
        end.
    set ghost_resource : atari_camera := fun l => (●E (f l) ⋅ ◯E (f l)).

    (* Allocate the ghost resource. *)
    iMod (own_alloc ghost_resource) as (name) "H".
    {
        move=> l. by rewrite auth_both_valid.
    }
    iModIntro.

    set atariGS0 := Build_atariGS Σ atariGpreS0 name.
    iExists (atariGS0).

    (* Half of the resource is given to the state interpretation. *)
    rewrite own_op.
    iDestruct "H" as "[stateI H]".
    iSplitL "stateI"; first done.

    (* The other half needs to be split apart, to hand to the user. *)
    pose (split_into_pointers f) as tmp;
        unfold atari_name, atariGS0 in tmp;
        iPoseProof (tmp with "H") as "(PC&N&B&V&D&I&Z&C&Bytes)";
        clear tmp.
    do 4 rewrite fmap_cons.
    iDestruct "Bytes" as "(X&Y&A&SP&RAM)".
    rewrite /init.

    iSplitL "PC".
    {
        simpl.
        move: (pc_init s s_initial) => [? [? [-> [-> ->]]]].
        have ->: spec.bv_concat 16
            (rom.ROM 0x7fc) (rom.ROM 0x7fd) = 0xf000%bv
            by bv_simplify_arith.
        iExact "PC".
    }
    iSplitL "X"; first (iExists _; iAssumption).
    iSplitL "Y"; first (iExists _; iAssumption).
    iSplitL "A"; first (iExists _; iAssumption).
    iSplitL "SP"; first (iExists _; iAssumption).
    iSplitL "N"; first (iExists _; iAssumption).
    iSplitL "B"; first (iExists _; iAssumption).
    iSplitL "V"; first (iExists _; iAssumption).
    iSplitL "D"; first (iExists _; iAssumption).
    iSplitL "I".
    {
        simpl.
        pose (init_interrupt_disable s s_initial) as tmp; move: tmp.
        by case (spec.Flag s I).
    }
    iSplitL "Z"; first (iExists _; iAssumption).
    iSplitL "C"; first (iExists _; iAssumption).
    iStopProof.

    do 2 rewrite big_sepL_fmap.
    apply big_sepL_mono => _ a _.

    by iIntros; iExists _.
Qed.

(*|

--------
Adequacy
--------

An *adequacy theorem* basically says
that proofs in the Iris logic are actually meaningful.

In our case, I'll prove that a specific Iris assertion implies
Dragster cannot be beaten in less than 5.57 seconds.

|*)

From iris.program_logic Require Import adequacy.

(*|

Iris's adequacy machinery needs a bit more ghost state to function.

|*)

Class langGS Σ := LangGS {
  lang_invGS : invGS Σ;
  lang_atari :: atariGS Σ;
}.
Global Instance langGS_irisGS `{!langGS Σ} : irisGS lang Σ := {
  iris_invGS := lang_invGS;
  state_interp s _ _ _ := iris.state_interp s;
  fork_post _ := True%I;
  num_laters_per_step _ := 0;
  state_interp_mono _ _ _ _ := fupd_intro _ _
}.
Class langGpreS Σ := LangPreG {
  lang_preG_iris :: invGpreS Σ;
  lang_preG_atari :: atariGpreS Σ;
}.

(*|

I can now define ``safe``,
an Iris assertion saying the program will not crash.

|*)

Definition safe `{!langGS Σ} : iProp Σ :=
    wp NotStuck top Expr (fun v : iris.val => ⌜match v with end⌝)%I.

(*|

And if the program cannot crash when started
at any valid initial state of the Atari,
then Dragster cannot be beaten in less than 5.57 seconds.

|*)

Theorem iris_goal Σ `{!langGpreS Σ} :
    (forall `{!langGS Σ}, ⊢ |={⊤}=> init -∗ safe) -> Goal.
Proof.
    move=> iris_proof.
    apply no_crash_implies_goal => s0 s0_initial s reachable.

    suff: adequate NotStuck Expr s0 (fun v _ => match v with end).
    {
        move=> a.
        eapply adequate_not_stuck.
        - exact a.
        - reflexivity.
        - exact reachable.
        - constructor.
    }

    refine (wp_adequacy Σ lang NotStuck Expr s0 _ _).
    move=> Hinv κs.
    iMod (atari_init s0 s0_initial) as (atari) "[stateI init]".
    set langGS0 := LangGS Σ Hinv atari.
    iMod (iris_proof _) as "iris_proof".
    iModIntro.
    iExists (fun s _ => iris.state_interp s).
    iExists (fun _ => True%I).
    iSplitL "stateI"; first done.
    by iApply "iris_proof".
Qed.

(*|

This is a crucial theorem. It says we can prove
the minimum Dragster time by proving the Iris assertion
``|={⊤}=> init -∗ safe``.

But to do this, we will need ways to work with ``safe``.

-----------------
Working with Safe
-----------------

To be continued...

|*)

