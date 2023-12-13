From stdpp Require Import finite unstable.bitvector.
From iris.algebra Require Export excl_auth functions.
From iris.program_logic Require Export language adequacy.
From iris.proofmode Require Import proofmode.
From theories Require Import spec.


Definition claim (s : state) : Prop :=
    forall p, player_has_won s p ->
    exists t, timer_in_hundredths s p t /\ (t >=? 557)%Z.

Inductive val :=.
Inductive expr.
Inductive observation :=.

Definition of_val (v : val) : expr := Build_expr.
Definition to_val (e : expr) : option val := None.

Definition prim_step (e : expr) (s : state) (κs : list observation) (e' : expr) (s' : state) (efs : list expr) : Prop :=
    claim s /\ step s s' /\ efs = [].

Lemma lang_mixin : LanguageMixin of_val to_val prim_step.
Proof.
    split.
    - case.
    - move=> [_ _ //].
    - trivial.
Qed.
Canonical Structure lang := Language lang_mixin.









Inductive loc := RAM (addr : bv 7) | Reg (r : reg) | PC | FlagD | FlagC | FlagN | FlagZ.
Definition loc_data (l : loc) : Set :=
    match l with
    | RAM _ => bv 8
    | Reg _ => bv 8
    | PC => bv 16
    | FlagD => bool
    | FlagC => bool
    | FlagN => bool
    | FlagZ => bool
    end.

Global Instance loc_eq_def : EqDecision loc.
Admitted.


Definition atari_camera := discrete_funR (fun l : loc => excl_authUR (leibnizO (loc_data l))).

Class atariGpreS (Σ : gFunctors) := {
    (* atari_PC : inG Σ (authR (optionUR (exclR (leibnizO (bv 16))))); *)
    atari_data :: inG Σ atari_camera;
}.
Class atariGS (Σ : gFunctors) := {
    atari_inG :: atariGpreS Σ;
    atari_name : gname;
}.

Section definitions.
    Context `{!atariGS Σ}.

    Definition pointsto_fun (l : loc) (v : loc_data l) : atari_camera.
        eapply discrete_fun_singleton.
        refine (◯E _).
        exact v.
    Defined.
    Definition pointsto_def (l : loc) (v : loc_data l) : iProp Σ :=
        own atari_name (pointsto_fun l v).

    Definition pointsto_aux : seal (@pointsto_def). by eexists. Qed.
    Definition pointsto := pointsto_aux.(unseal).
    Definition pointsto_eq : @pointsto = @pointsto_def := pointsto_aux.(seal_eq).

    Definition pointsto_auth_fun (l : loc) (v : loc_data l) : atari_camera.
        eapply discrete_fun_singleton.
        refine (●E _).
        exact v.
    Defined.
    Definition pointsto_auth_def (l : loc) (v : loc_data l) : iProp Σ :=
        own atari_name (pointsto_auth_fun l v).

    Definition pointsto_auth_aux : seal (@pointsto_auth_def). by eexists. Qed.
    Definition pointsto_auth := pointsto_auth_aux.(unseal).
    Definition pointsto_auth_eq : @pointsto_auth = @pointsto_auth_def := pointsto_auth_aux.(seal_eq).
End definitions.

Notation "l ↦ v" := (pointsto l v)
  (at level 20, format "l  ↦  v") : bi_scope.

Notation "l ↦ ?" := (∃ v, l ↦ v)%I
  (at level 20, format "l  ↦ ?") : bi_scope.

Local Notation "l ↦● v" := (pointsto_auth l v)
  (at level 20, format "l  ↦●  v") : bi_scope.

Lemma pointsto_agree `{!atariGS Σ} (l : loc) (a b : loc_data l) : l ↦● a ∗ l ↦ b ⊢ ⌜a = b⌝.
Proof.
    rewrite pointsto_eq pointsto_auth_eq /pointsto_def /pointsto_auth_def -own_op discrete_fun_singleton_op.
    rewrite own_valid.
    iPureIntro.
    move=> valid.
    specialize (valid l).
    rewrite discrete_fun_lookup_singleton in valid.
    apply excl_auth_agree in valid.
    exact valid.
Qed.

Lemma pointsto_update `{!atariGS Σ} (l : loc) (a b : loc_data l) :
    l ↦● a ∗ l ↦ a ⊢ |==> l ↦● b ∗ l ↦ b.
Proof.
    rewrite pointsto_eq pointsto_auth_eq /pointsto_def /pointsto_auth_def -own_op -own_op.
    apply own_update.
    rewrite /pointsto_auth_fun /pointsto_fun discrete_fun_singleton_op discrete_fun_singleton_op.
    apply discrete_fun_singleton_update.
    apply auth_update.
    apply option_local_update.
    by apply exclusive_local_update.
Qed.






Definition state_interp `{!atariGS Σ} (s : state) : iProp Σ :=
    PC ↦● spec.PC s
    ∗ Reg X ↦● spec.Reg s X
    ∗ Reg Y ↦● spec.Reg s Y
    ∗ Reg A ↦● spec.Reg s A
    ∗ Reg SP ↦● spec.Reg s SP
    ∗ FlagD ↦● spec.Flag s D
    ∗ FlagC ↦● spec.Flag s C
    ∗ FlagN ↦● spec.Flag s N
    ∗ FlagZ ↦● spec.Flag s Z
    ∗ [∗ list] addr ∈ enum (bv 7), RAM addr ↦● spec.RAM s addr.
















(* Lemma discrete_fun_lookup_big_opL
    {A : Type} {B : A → ucmra} {X : Type} (f : X -> discrete_fun B) (l : list X) (a : A) :
    ([^op list] x ∈ l, f x) a = ([^op list] x ∈ l, f x a).
Proof.
    induction l as [|x l IH].
    - done.
    - simpl.
        by rewrite discrete_fun_lookup_op IH.
Qed. *)

Lemma atari_init `{!atariGpreS Σ} s (s_initial : initial s) :
    ⊢ |==> ∃ _ : atariGS Σ,
        state_interp s
        ∗ PC ↦ 0xf000%bv
        ∗ Reg X ↦ ?
        ∗ Reg Y ↦ ?
        ∗ Reg A ↦ ?
        ∗ Reg SP ↦ ?
        ∗ FlagD ↦ ?
        ∗ FlagC ↦ ?
        ∗ FlagN ↦ ?
        ∗ FlagZ ↦ ?
        ∗ [∗ list] addr ∈ enum (bv 7), RAM addr ↦ ?
        .
Proof.
    set f : forall l, leibnizO (loc_data l) :=
        fun l => match l return loc_data l with
        | RAM addr => spec.RAM s addr
        | Reg r => spec.Reg s r
        | PC => spec.PC s
        | FlagD => spec.Flag s D
        | FlagC => spec.Flag s C
        | FlagN => spec.Flag s N
        | FlagZ => spec.Flag s Z
        end.
    set loc_list := [Reg X;Reg Y;Reg A;Reg SP;FlagD;FlagC;FlagN;FlagZ] ++ (RAM <$> enum (bv 7)).
    change (⊢ |==> ∃ _ : atariGS Σ,
    ([∗ list] l ∈ PC :: loc_list, l ↦● f l ) ∗ PC ↦ 61440%bv ∗ ([∗ list] l ∈ loc_list, l ↦?)).


    set g : atari_camera := fun l => (●E (f l) ⋅ ◯E (f l)).

    iMod (own_alloc g) as (γ) "H".
    { move=> l. by rewrite auth_both_valid. }
    iModIntro.

    set atariGS0 := Build_atariGS Σ atariGpreS0 γ.
    iExists (atariGS0).

    iAssert (own γ ([^op list] l ∈ PC :: loc_list, pointsto_auth_fun l (f l) ⋅ pointsto_fun l (f l))%I) with "[H]" as "H".
    {
        iApply (own_mono with "H").

        exists ε.
        move=> l.

        admit.
    }

    rewrite big_opL_own; last done.

    iAssert ([∗ list] l ∈ PC :: loc_list, l ↦● f l ∗ l ↦ f l)%I with "[H]" as "H".
    {
        iApply (big_sepL_mono with "H").
        move=> _ l _.
        iIntros "H".
        rewrite own_op.
        rewrite pointsto_eq pointsto_auth_eq.
        iExact "H".
    }

    rewrite big_sepL_sep.
    iDestruct "H" as "[H1 [PC H2]]".
    iSplitL "H1"; first done.
    iSplitL "PC".
    - rewrite /f.

        move: (pc_init s s_initial) => H.
        rewrite /fetch in H.
        simpl in H.
        move: H => [? [? [-> [-> ->]]]].

        have ->: bv_concat 16 (rom.ROM 0x7fc) (rom.ROM 0x7fd) = 0xf000%bv.
        {
            compute.
            From stdpp Require Import unstable.bitvector_tactics.
            bv_simplify_arith.
            done.
        }
        iExact "PC".
    - iApply (big_sepL_mono with "H2").
        move=> _ l _.
        iIntros "H".
        iExists (f l).
        iExact "H".
Admitted.






Class langGS Σ := LangGS {
  lang_invGS : invGS Σ;
  lang_atari :: atariGS Σ;
}.

Global Instance langGS_irisGS `{!langGS Σ} : irisGS lang Σ := {
  iris_invGS := lang_invGS;
  state_interp s _ _ _ := state_interp s;
  fork_post _ := True%I;
  num_laters_per_step _ := 0;
  state_interp_mono _ _ _ _ := fupd_intro _ _
}.

Class langGpreS Σ := LangPreG {
  lang_preG_iris :: invGpreS Σ;
  lang_preG_atari :: atariGpreS Σ;
}.

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


Notation safe := (wp NotStuck top Build_expr (fun v : val => bi_pure match v return Prop with end)).

Theorem iris_goal Σ `{!langGpreS Σ}
    (iris_proof : forall `{!langGS Σ}, ⊢ |={⊤}=>
        ( PC ↦ 0xf000%bv
        ∗ Reg X ↦ ?
        ∗ Reg Y ↦ ?
        ∗ Reg A ↦ ?
        ∗ Reg SP ↦ ?
        ∗ FlagD ↦ ?
        ∗ FlagC ↦ ?
        ∗ FlagN ↦ ?
        ∗ FlagZ ↦ ?
        ∗ [∗ list] addr ∈ enum (bv 7), RAM addr ↦ ?
        ) -∗ safe)
    : Goal.
Proof.
    rewrite /Goal.
    move=> s0 s0_initial.

    suff: forall s, rtc erased_step ([Build_expr], s0) ([Build_expr], s) -> claim s.
    {
        move=> Hyp s reachable.
        change (claim s).

        eapply (rtc_ind_r (fun s => claim s /\ rtc erased_step ([Build_expr], s0) ([Build_expr], s))); last exact reachable.
        - split.
            + by apply initial_claim.
            + constructor.
        - clear reachable => s1 s2 reachable σ [IH1 IH2].
            have: rtc erased_step ([Build_expr], s0) ([Build_expr], s2).
            {
                eapply rtc_r; first exact IH2.
                rewrite /erased_step.
                exists [].
                by apply (step_atomic _ _ _ _ [] [] [] eq_refl eq_refl).
            }
            clear reachable => reachable.
            split.
            + apply Hyp; exact reachable.
            + exact reachable.
    }

    move=> s reachable.

    suff: not_stuck Build_expr s.
    {
        case.
        - move=> [_ //].
        - move=> [_ [_ [_ [_ [// _]]]]].
    }

    suff: adequate NotStuck Build_expr s0 (fun v _ => match v with end).
    {
        move=> a.
        eapply adequate_not_stuck.
        - exact a.
        - trivial.
        - exact reachable.
        - constructor.
    }

    refine (wp_adequacy Σ lang NotStuck Build_expr s0 _ _).
    move=> Hinv κs.

    iMod (atari_init s0 s0_initial) as (atari) "[interp mem_ownership]".
    set langGS0 := LangGS Σ Hinv atari.
    iMod (iris_proof _) as "iris_proof".
    iModIntro.
    iExists (fun s _ => state_interp s).
    iExists (fun _ => True%I).
    iFrame.
    iApply "iris_proof".
    iExact "mem_ownership".
Qed.
