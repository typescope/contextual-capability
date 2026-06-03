(* ------------------------------------------------------------------- *)
(* This file formalizes Lambda^CC, a simply-typed lambda calculus      *)
(* with contextual capabilities and explicit effect annotations        *)
(* tracking which capability indices may be read.                      *)
(*                                                                     *)
(* The proof follows a logical-relations style normalization argument. *)
(* ------------------------------------------------------------------- *)


(* ------------------------------------------------------------------- *)
(* Why No Explicit Well-formedness/Stratification of Pi                *)
(*                                                                     *)
(* A natural concern is whether Pi can contain cyclic declarations     *)
(* such as p : Int{p} => Int and thereby invalidate normalization.     *)
(* The representative example is                                       *)
(*                                                                     *)
(*   (p 10) with p = (lambda x{p}. p x)                                *)
(*                                                                     *)
(* In this development, the typing relation already prevents this      *)
(* pattern from becoming a well-typed closed term:                     *)
(* 1) typing_app requires t1 to have type tp_arr T1 T2 Tp_cp p.        *)
(* 2) typing_app also requires cp_type Pi p = Some Tp_cp.              *)
(* 3) If t1 is tm_cvar p, typing_cvar gives                            *)
(*      cp_type Pi p = Some (tp_arr T1 T2 Tp_cp p).                    *)
(* 4) Therefore both equalities force                                  *)
(*      Tp_cp = tp_arr T1 T2 Tp_cp p,                                  *)
(*    i.e. a finite self-referential type equation.                    *)
(*                                                                     *)
(* Since the syntax of types is finite and inductive, this equation    *)
(* cannot be satisfied. Hence the cyclic use is rejected by ordinary   *)
(* typing constraints, without adding a separate global stratification *)
(* judgment for Pi solely to rule out this case.                       *)
(*                                                                     *)
(* ------------------------------------------------------------------- *)


From Coq Require Import Arith List Bool.

Set Implicit Arguments.

(* ================================================================ *)
(* Lambda^CC calculus (contextual capabilities)                    *)
(* ================================================================ *)

From Coq Require Import Arith List Bool PeanoNat Lia.

(* Use nat as names for term variables *)
Definition name := nat.

(* Effects: finite sets of capability indices, represented as lists *)
Definition effect := list nat.

Definition eff_empty : effect := nil.
Definition eff_singleton (p: nat) : effect := p :: nil.

Fixpoint eff_mem (p: nat) (e: effect) : bool :=
  match e with
  | nil => false
  | q :: rest => if Nat.eq_dec p q then true else eff_mem p rest
  end.

Definition eff_add (p: nat) (e: effect) : effect := p :: e.
Definition eff_union (e1 e2: effect) : effect := e1 ++ e2.
Definition eff_diff (e1 e2: effect) : effect :=
  filter (fun p => negb (eff_mem p e2)) e1.
Definition eff_subset (e1 e2: effect) : Prop :=
  forall p, eff_mem p e1 = true -> eff_mem p e2 = true.

(* Types *)
Inductive type : Type :=
  | tp_nat
  | tp_arr (T1 T2 Tp_cp: type) (p: nat).

(* Capability declarations: list of types for capability indices 0,1,2,... *)
Definition cp_decl := list type.

Definition cp_type (Pi: cp_decl) (p: nat) : option type :=
  nth_error Pi p.

Definition Pi_effects (Pi: cp_decl) : effect :=
  seq 0 (length Pi).


(* Terms *)
Inductive term : Type :=
  | tm_const (n: nat)
  | tm_var (x: name)
  | tm_cvar (p: nat)
  | tm_abs (x: name) (T: type) (Tp_cp: type) (p: nat) (body: term)
  | tm_app (e1 e2: term)
  | tm_with (p: nat) (e1 e2: term)
  | tm_allow (eff: effect) (e: term).

(* Values *)
Inductive value : Type :=
  | vl_const (n: nat)
  | vl_clos (x: name) (T: type) (Tp_cp: type) (p: nat) (body: term)
            (env: list (name * value)) (cpenv: list (option value)).

(* Environments *)
Definition tp_env := list (name * type).
Definition vl_env := list (name * value).
Definition cp_env := list (option value).

Definition cp_empty : cp_env := nil.

Fixpoint cp_lookup (p: nat) (e: cp_env) : option value :=
  match e, p with
  | nil, _ => None
  | v :: _, 0 => v
  | _ :: rest, S p' => cp_lookup p' rest
  end.

Lemma cp_lookup_nil : forall p, cp_lookup p nil = None.
Proof. intros p; destruct p; reflexivity. Qed.

Fixpoint cp_update (p: nat) (v: value) (e: cp_env) {struct p} : cp_env :=
  match p, e with
  | 0, nil => Some v :: nil
  | 0, _ :: rest => Some v :: rest
  | S p', nil => None :: cp_update p' v nil
  | S p', x :: rest => x :: cp_update p' v rest
  end.

Fixpoint cp_restrict_aux (i: nat) (eff: effect) (e: cp_env) {struct e} : cp_env :=
  match e with
  | nil => nil
  | v :: rest =>
      (if eff_mem i eff then v else None) ::
      cp_restrict_aux (S i) eff rest
  end.

Definition cp_restrict (eff: effect) (e: cp_env) : cp_env :=
  cp_restrict_aux 0 eff e.

Fixpoint cp_diff_aux (i: nat) (e: cp_env) (eff: effect) {struct e} : cp_env :=
  match e with
  | nil => nil
  | v :: rest =>
      (if eff_mem i eff then None else v) :: cp_diff_aux (S i) rest eff
  end.

Definition cp_diff (e: cp_env) (eff: effect) : cp_env :=
  cp_diff_aux 0 e eff.

Fixpoint cp_merge (e1 e2: cp_env) {struct e1} : cp_env :=
  match e1, e2 with
  | nil, _ => e2
  | v1 :: r1, nil => v1 :: cp_merge r1 nil
  | v1 :: r1, v2 :: r2 =>
      (match v2 with Some _ => v2 | None => v1 end) :: cp_merge r1 r2
  end.

(* Lookup for list-based environments *)
Fixpoint lookup {A: Type} (k: name) (l: list (name * A)) : option A :=
  match l with
  | nil => None
  | (a, b)::rest => if Nat.eq_dec k a then Some b else lookup k rest
  end.

(* Big-step evaluation *)
Reserved Notation "'<<' t ',' env ',' cpenv '>>' '==>' v" (at level 40).

Inductive eval : term -> vl_env -> cp_env -> value -> Prop :=
  | eval_const : forall env cpenv n,
      << tm_const n, env, cpenv >> ==> (vl_const n)
  | eval_var : forall env cpenv x v,
      lookup x env = Some v ->
      << tm_var x, env, cpenv >> ==> v
  | eval_cvar : forall env cpenv p v,
      cp_lookup p cpenv = Some v ->
      << tm_cvar p, env, cpenv >> ==> v
  | eval_abs : forall env cpenv x T Tp_cp p t,
      << tm_abs x T Tp_cp p t, env, cpenv >> ==>
        (vl_clos x T Tp_cp p t env (cp_diff cpenv (eff_singleton p)))
  | eval_app : forall env cpenv x T Tp_cp p t t1 t2 v2 v3 env1 cpenv1,
      << t1, env, cpenv >> ==> (vl_clos x T Tp_cp p t env1 cpenv1) ->
      << t2, env, cpenv >> ==> v2 ->
      << t, ((x, v2) :: env1), (cp_merge cpenv cpenv1) >> ==> v3 ->
      << tm_app t1 t2, env, cpenv >> ==> v3
  | eval_with : forall env cpenv p e1 e2 v1 v2,
      << e1, env, cpenv >> ==> v1 ->
      << e2, env, (cp_update p v1 cpenv) >> ==> v2 ->
      << tm_with p e1 e2, env, cpenv >> ==> v2
  | eval_allow : forall env cpenv eff e v,
      << e, env, (cp_restrict eff cpenv) >> ==> v ->
      << tm_allow eff e, env, cpenv >> ==> v

where "'<<' t ',' env ',' cpenv '>>' '==>' v" := (eval t env cpenv v).

(* Typing *)
Reserved Notation "'[' Pi ',' Gamma ']' '|-' t ':::' T '!' eff" (at level 40).

Inductive typing : cp_decl -> tp_env -> term -> type -> effect -> Prop :=
  | typing_const : forall Pi Gamma n,
      [ Pi, Gamma ] |- (tm_const n) ::: tp_nat ! eff_empty
  | typing_var : forall Pi Gamma x T,
      lookup x Gamma = Some T ->
      [ Pi, Gamma ] |- (tm_var x) ::: T ! eff_empty
  | typing_cvar : forall Pi Gamma p T,
      eff_mem p (Pi_effects Pi) = true ->
      cp_type Pi p = Some T ->
      [ Pi, Gamma ] |- (tm_cvar p) ::: T ! (eff_singleton p)
  | typing_abs : forall Pi Gamma T1 T2 Tp_cp x p eff' t,
      cp_type Pi p = Some Tp_cp ->
      [ Pi, ((x, T1)::Gamma) ] |- t ::: T2 ! eff' ->
      [ Pi, Gamma ] |- (tm_abs x T1 Tp_cp p t) ::: (tp_arr T1 T2 Tp_cp p) ! (eff_diff eff' (eff_singleton p))
  | typing_app : forall Pi Gamma T1 T2 Tp_cp p eff1 eff2 t1 t2,
      [ Pi, Gamma ] |- t1 ::: (tp_arr T1 T2 Tp_cp p) ! eff1 ->
      [ Pi, Gamma ] |- t2 ::: T1 ! eff2 ->
      cp_type Pi p = Some Tp_cp ->
      [ Pi, Gamma ] |- (tm_app t1 t2) ::: T2 ! (eff_union (eff_singleton p) (eff_union eff1 eff2))
  | typing_with : forall Pi Gamma p e1 e2 T1 T2 eff1 eff2,
      cp_type Pi p = Some T1 ->
      [ Pi, Gamma ] |- e1 ::: T1 ! eff1 ->
      eff_mem p (Pi_effects Pi) = true ->
      [ Pi, Gamma ] |- e2 ::: T2 ! eff2 ->
      [ Pi, Gamma ] |- (tm_with p e1 e2) ::: T2 ! (eff_union eff1 (eff_diff eff2 (eff_singleton p)))
  | typing_allow : forall Pi Gamma eff e T eff',
      [ Pi, Gamma ] |- e ::: T ! eff' ->
      eff_subset eff' eff ->
      [ Pi, Gamma ] |- (tm_allow eff e) ::: T ! eff'
  | typing_sub : forall Pi Gamma t T eff p,
      [ Pi, Gamma ] |- t ::: T ! eff ->
      eff_mem p (Pi_effects Pi) = true ->
      [ Pi, Gamma ] |- t ::: T ! (eff_add p eff)

where "'[' Pi ',' Gamma ']' '|-' t ':::' T '!' eff" := (typing Pi Gamma t T eff).

(* ================================================================ *)
(* soundness specification                                          *)
(* ================================================================ *)

Definition soundness_spec: Prop := forall Pi t T,
    [ Pi, nil ] |- t ::: T ! eff_empty ->
    exists v, << t, nil, cp_empty >> ==> v.

(* ================================================================ *)
(* proof                                                            *)
(* ================================================================ *)

(* Halting predicates *)
Fixpoint halts_value (Pi: cp_decl) (v: value) (T: type) : Prop :=
  match T, v with
  | tp_nat, vl_const _ => True
  | tp_arr T1 T2 Tp_cp p, vl_clos x T1' Tp_cp' p' body env cpenv =>
      T1 = T1' /\ Tp_cp = Tp_cp' /\ p = p' /\
      forall v2,
        halts_value Pi v2 T1 ->
        forall cpenv_arg cpv,
          cp_lookup p cpenv_arg = Some cpv ->
          halts_value Pi cpv Tp_cp ->
          exists v3, << body, (x, v2)::env, (cp_merge cpenv_arg cpenv) >> ==> v3 /\
                     halts_value Pi v3 T2
  | _, _ => False
  end.

Inductive halts_env : cp_decl -> tp_env -> vl_env -> Prop :=
| halts_env_empty : forall Pi, halts_env Pi nil nil
| halts_env_ext : forall Pi x v Gamma env T,
    halts_env Pi Gamma env ->
    halts_value Pi v T ->
    halts_env Pi ((x, T) :: Gamma) ((x, v)::env).

#[local] Hint Constructors halts_env : core.

Lemma lookup_safe_halts : forall Pi Gamma env x T,
  halts_env Pi Gamma env ->
  lookup x Gamma = Some T ->
  exists v, lookup x env = Some v /\ halts_value Pi v T.
Proof.
  intros Pi Gamma env x T Henv. revert x T.
  induction Henv as [|Pi' x' v' Gamma' env' T' Henv' IH Hv]; intros y Ty Hlk; simpl in *.
  - discriminate.
  - destruct (Nat.eq_dec y x').
    + subst. inversion Hlk. subst. eexists. split; [reflexivity|exact Hv].
    + apply IH in Hlk. destruct Hlk as [v0 [Hlkv Hv0]]. eexists. split; [rewrite Hlkv; reflexivity|assumption].
Qed.

Fixpoint halts_cpenv(Pi: cp_decl) (eff: effect) (cpenv: cp_env): Prop :=
  match eff with
  | nil => True
  | p :: eff' =>
    halts_cpenv Pi eff' cpenv /\
    exists T v, cp_type Pi p = Some T /\ cp_lookup p cpenv = Some v /\ halts_value Pi v T
  end.

Lemma cp_lookup_merge : forall p e1 e2,
  cp_lookup p (cp_merge e1 e2) =
  match cp_lookup p e2 with
  | Some v => Some v
  | None => cp_lookup p e1
  end.
Proof.
  intros p e1 e2.
  revert p e2.
  induction e1 as [|v1 r1 IHe1]; intros p e2; simpl.
  - destruct (cp_lookup p e2) eqn:Hlk; simpl; try reflexivity.
    destruct p; reflexivity.
  - destruct e2 as [|v2 r2].
    + destruct p; simpl.
      * reflexivity.
      * rewrite IHe1. rewrite cp_lookup_nil. reflexivity.
    + destruct p; simpl.
      * destruct v2; reflexivity.
      * destruct v2; simpl; apply IHe1.
Qed.

Lemma cp_lookup_update_eq : forall p v,
  cp_lookup p (cp_update p v nil) = Some v.
Proof.
  induction p; simpl.
  - reflexivity.
  - exact IHp.
Qed.

Lemma cp_lookup_update_neq : forall p q v,
  p <> q ->
  cp_lookup p (cp_update q v nil) = None.
Proof.
  induction p; destruct q; intros v Hneq; simpl.
  - contradiction.
  - reflexivity.
  - rewrite cp_lookup_nil. reflexivity.
  - apply IHp. congruence.
Qed.

Lemma cp_lookup_update_eq_gen : forall p v cpenv,
  cp_lookup p (cp_update p v cpenv) = Some v.
Proof.
  induction p; destruct cpenv; simpl; try reflexivity.
  - rewrite IHp. reflexivity.
  - rewrite IHp. reflexivity.
Qed.

Lemma cp_lookup_update_neq_gen : forall p q v cpenv,
  p <> q ->
  cp_lookup q (cp_update p v cpenv) = cp_lookup q cpenv.
Proof.
  induction p; intros q v cpenv Hneq.
  - destruct q; simpl.
    + contradiction.
    + destruct cpenv; simpl; try rewrite cp_lookup_nil; reflexivity.
  - destruct q; simpl.
    + destruct cpenv; simpl; try rewrite cp_lookup_nil; reflexivity.
    + destruct cpenv; simpl.
      * rewrite <- (cp_lookup_nil q). apply IHp. congruence.
      * apply IHp. congruence.
Qed.

Lemma cp_lookup_diff : forall p cpenv eff,
  cp_lookup p (cp_diff cpenv eff) =
    if eff_mem p eff then None else cp_lookup p cpenv.
Proof.
  intros p cpenv eff.
  unfold cp_diff.
  assert (Haux : forall k idx e,
    cp_lookup idx (cp_diff_aux k e eff) =
      if eff_mem (idx + k) eff then None else cp_lookup idx e).
  {
    intros k idx e.
    revert k idx.
    induction e as [|v rest IH]; intros k idx; simpl.
    - destruct idx as [|idx'].
      + destruct (eff_mem (0 + k) eff); reflexivity.
      + destruct (eff_mem (S idx' + k) eff); reflexivity.
    - destruct idx as [|idx']; simpl.
      + reflexivity.
      + rewrite (IH (S k) idx').
        replace (idx' + S k) with (S idx' + k) by lia.
        reflexivity.
  }
  specialize (Haux 0 p cpenv). simpl in Haux.
  rewrite Nat.add_0_r in Haux.
  exact Haux.
Qed.

Lemma cp_lookup_restrict : forall p eff cpenv,
  cp_lookup p (cp_restrict eff cpenv) =
    if eff_mem p eff then cp_lookup p cpenv else None.
Proof.
  intros p eff cpenv.
  unfold cp_restrict.
  assert (Haux : forall k idx e,
    cp_lookup idx (cp_restrict_aux k eff e) =
      if eff_mem (idx + k) eff then cp_lookup idx e else None).
  {
    intros k idx e.
    revert k idx.
    induction e as [|v rest IH]; intros k idx; simpl.
    - destruct idx as [|idx'].
      + destruct (eff_mem (0 + k) eff); reflexivity.
      + destruct (eff_mem (S idx' + k) eff); reflexivity.
    - destruct idx as [|idx']; simpl.
      + reflexivity.
      + rewrite (IH (S k) idx').
        replace (idx' + S k) with (S idx' + k) by lia.
        reflexivity.
  }
  specialize (Haux 0 p cpenv). simpl in Haux.
  rewrite Nat.add_0_r in Haux.
  exact Haux.
Qed.

Lemma cp_type_unique : forall Pi p T1 T2,
  cp_type Pi p = Some T1 ->
  cp_type Pi p = Some T2 ->
  T1 = T2.
Proof.
  intros Pi p T1 T2 H1 H2.
  revert p H1 H2.
  induction Pi as [|T Pi IHPi]; intros [|p'] H1 H2; simpl in *; try discriminate.
  - inversion H1; inversion H2; subst; reflexivity.
  - apply (IHPi p'); assumption.
Qed.

Lemma cp_lookup_diff_same : forall p cpenv,
  cp_lookup p (cp_diff cpenv (eff_singleton p)) = None.
Proof.
  intros p cpenv. rewrite cp_lookup_diff.
  simpl. destruct (Nat.eq_dec p p); [reflexivity|contradiction].
Qed.

Lemma cp_lookup_diff_other : forall p q cpenv,
  p <> q ->
  cp_lookup p (cp_diff cpenv (eff_singleton q)) = cp_lookup p cpenv.
Proof.
  intros p q cpenv Hneq.
  rewrite cp_lookup_diff.
  simpl. destruct (Nat.eq_dec p q); [contradiction|reflexivity].
Qed.

Lemma halts_cpenv_mem : forall Pi eff cpenv p,
  halts_cpenv Pi eff cpenv ->
  eff_mem p eff = true ->
  exists T v, cp_type Pi p = Some T /\ cp_lookup p cpenv = Some v /\ halts_value Pi v T.
Proof.
  intros Pi eff cpenv p Hh Hmem.
  revert p Hmem.
  induction eff as [|q eff' IH]; intros p Hmem; simpl in *.
  - discriminate.
  - destruct Hh as [Hrest [T [v [Hctp [Hlk Hv]]]]].
    destruct (Nat.eq_dec p q) as [Heq|Hneq].
    + subst. simpl in Hmem. destruct (Nat.eq_dec q q); [|contradiction].
      eauto.
    + simpl in Hmem. apply IH in Hmem; auto.
Qed.

Lemma eff_subset_cons_tail : forall p eff1 eff2,
  eff_subset (p :: eff1) eff2 ->
  eff_subset eff1 eff2.
Proof.
  unfold eff_subset. intros p eff1 eff2 Hsub q Hmem.
  apply Hsub. simpl. destruct (Nat.eq_dec q p); auto.
Qed.

Lemma eff_mem_app_l : forall p e1 e2,
  eff_mem p e1 = true ->
  eff_mem p (e1 ++ e2) = true.
Proof.
  intros p e1 e2 Hmem. induction e1 as [|q rest IH]; simpl in *; auto.
  - inversion Hmem.
  - destruct (Nat.eq_dec p q); auto.
Qed.

Lemma eff_mem_app_r : forall p e1 e2,
  eff_mem p e2 = true ->
  eff_mem p (e1 ++ e2) = true.
Proof.
  intros p e1 e2 Hmem. induction e1 as [|q rest IH]; simpl; auto.
  destruct (Nat.eq_dec p q); auto.
Qed.

Lemma eff_subset_add : forall p eff,
  eff_subset eff (eff_add p eff).
Proof.
  unfold eff_subset, eff_add. intros p eff q Hmem.
  simpl. destruct (Nat.eq_dec q p); auto.
Qed.

Lemma eff_subset_union_l : forall e1 e2,
  eff_subset e1 (eff_union e1 e2).
Proof.
  unfold eff_subset, eff_union. intros e1 e2 p Hmem.
  apply eff_mem_app_l. exact Hmem.
Qed.

Lemma eff_subset_union_r : forall e1 e2,
  eff_subset e2 (eff_union e1 e2).
Proof.
  unfold eff_subset, eff_union. intros e1 e2 p Hmem.
  apply eff_mem_app_r. exact Hmem.
Qed.

Lemma halts_cpenv_subset : forall Pi eff1 eff2 cpenv,
  eff_subset eff1 eff2 ->
  halts_cpenv Pi eff2 cpenv ->
  halts_cpenv Pi eff1 cpenv.
Proof.
  intros Pi eff1 eff2 cpenv Hsub Hh2.
  induction eff1 as [|p eff1' IH]; simpl; auto.
  split.
  { apply IH. apply eff_subset_cons_tail with (p:=p). exact Hsub. }
  { eapply halts_cpenv_mem with (eff:=eff2) in Hh2.
    2:{
      specialize (Hsub p).
      assert (Hmem: eff_mem p (p :: eff1') = true).
      { simpl. destruct (Nat.eq_dec p p); [reflexivity|contradiction]. }
      apply Hsub. exact Hmem.
    }
    exact Hh2. }
Qed.

Lemma halts_cpenv_restrict : forall Pi eff' eff cpenv,
  eff_subset eff' eff ->
  halts_cpenv Pi eff' cpenv ->
  halts_cpenv Pi eff' (cp_restrict eff cpenv).
Proof.
  intros Pi eff' eff cpenv Hsub Hh.
  induction eff' as [|p eff'' IH]; simpl; auto.
  destruct Hh as [Hrest [T [v [Hct [Hlk Hv]]]]].
  split.
  - apply IH.
    + apply eff_subset_cons_tail with (p:=p). exact Hsub.
    + exact Hrest.
  - exists T, v. split; [assumption|].
    split.
    + rewrite cp_lookup_restrict.
      specialize (Hsub p).
      assert (Hmem: eff_mem p (p :: eff'') = true).
      { simpl. destruct (Nat.eq_dec p p); [reflexivity|contradiction]. }
      specialize (Hsub Hmem). rewrite Hsub. exact Hlk.
    + exact Hv.
Qed.

Lemma halts_cpenv_update : forall Pi eff cpenv p Tp v,
  cp_type Pi p = Some Tp ->
  halts_value Pi v Tp ->
  halts_cpenv Pi eff cpenv ->
  halts_cpenv Pi eff (cp_update p v cpenv).
Proof.
  intros Pi eff cpenv p Tp v Hctp Hv Hh.
  induction eff as [|q eff' IH]; simpl in *; auto.
  destruct Hh as [Hrest [Tq [vq [Hctq [Hlkq Hvq]]]]].
  split.
  - apply IH. exact Hrest.
  - destruct (Nat.eq_dec q p) as [Heq|Hneq].
    + subst q.
      exists Tp, v. split; [assumption|].
      split.
      * apply cp_lookup_update_eq_gen.
      * exact Hv.
    + exists Tq, vq. split; [assumption|].
      split.
      * rewrite cp_lookup_update_neq_gen; [exact Hlkq|congruence].
      * exact Hvq.
Qed.

Lemma halts_cpenv_update_diff : forall Pi eff cpenv p Tp v,
  cp_type Pi p = Some Tp ->
  halts_value Pi v Tp ->
  halts_cpenv Pi (eff_diff eff (eff_singleton p)) cpenv ->
  halts_cpenv Pi eff (cp_update p v cpenv).
Proof.
  intros Pi eff cpenv p Tp v Hctp Hv Hh.
  induction eff as [|q eff' IH]; simpl in *; auto.
  destruct (Nat.eq_dec q p) as [Heq|Hneq].
  - subst q. simpl in Hh. destruct (Nat.eq_dec p p); [|contradiction].
    split.
    + apply IH. exact Hh.
    + exists Tp, v. split; [assumption|].
      split.
      * apply cp_lookup_update_eq_gen.
      * exact Hv.
  - simpl in Hh. destruct (Nat.eq_dec q p); [contradiction|].
    destruct Hh as [Hrest [Tq [vq [Hctq [Hlkq Hvq]]]]].
    split.
    + apply IH. exact Hrest.
    + exists Tq, vq. split; [assumption|].
      split.
      * rewrite cp_lookup_update_neq_gen; [exact Hlkq|congruence].
      * exact Hvq.
Qed.

Lemma halts_cpenv_diff_merge : forall Pi eff' cpenv p cpv Tp_cp cpenv_arg,
  cp_type Pi p = Some Tp_cp ->
  halts_value Pi cpv Tp_cp ->
  cp_lookup p cpenv_arg = Some cpv ->
  halts_cpenv Pi (eff_diff eff' (eff_singleton p)) cpenv ->
  halts_cpenv Pi eff' (cp_merge cpenv_arg (cp_diff cpenv (eff_singleton p))).
Proof.
  intros Pi eff' cpenv p cpv Tp_cp cpenv_arg Hctp Hcpv Hlkp Hh.
  induction eff' as [|q eff'' IH]; simpl in *; auto.
  destruct (Nat.eq_dec q p) as [Heq|Hneq].
  - subst q. simpl in Hh. destruct (Nat.eq_dec p p); [|contradiction].
    split.
    + apply IH; assumption.
    + exists Tp_cp, cpv. split; [assumption|].
      split.
      * rewrite cp_lookup_merge.
        rewrite cp_lookup_diff_same.
        rewrite Hlkp. reflexivity.
      * exact Hcpv.
  - simpl in Hh. destruct (Nat.eq_dec q p); [contradiction|].
    destruct Hh as [Hrest [Tq [vq [Hctq [Hlkq Hvq]]]]].
    split.
    + apply IH; assumption.
    + exists Tq, vq. split; [assumption|].
      split.
      * rewrite cp_lookup_merge.
        rewrite cp_lookup_diff_other by exact Hneq.
        rewrite Hlkq. reflexivity.
      * exact Hvq.
Qed.

Lemma halts_env_closed : forall Pi Gamma env cpenv T t eff,
    halts_env Pi Gamma env ->
    halts_cpenv Pi eff cpenv ->
    [ Pi, Gamma ] |- t ::: T ! eff ->
    exists v, << t, env, cpenv >> ==> v /\ halts_value Pi v T.
Proof.
  intros Pi Gamma env cpenv T t eff Henv Hcpenv Htyp.
  revert env cpenv Henv Hcpenv.
  induction Htyp; intros env cpenv Henv Hcpenv.
  - (* const *)
    exists (vl_const n). split; constructor.
  - (* var *)
    destruct (@lookup_safe_halts Pi Gamma env x T Henv H) as [v [Hlkv Hv]]. exists v. split; [constructor; exact Hlkv | exact Hv].
  - (* cvar *)
    destruct Hcpenv as [Hrest [T' [v0 [Hcp' [Hlk Hv0]]]]]. rewrite H0 in Hcp'. inversion Hcp'. subst T'.
    exists v0. split; [constructor; exact Hlk | exact Hv0].
  - (* abs *)
    exists (vl_clos x T1 Tp_cp p t env (cp_diff cpenv (eff_singleton p))).
    split; [constructor|].
    simpl. split; [reflexivity|split; [reflexivity|split; [reflexivity|]]].
    intros v2 Hv2 cpenv_arg cpv Hcp_lookup Hcpv.
    assert (Henv_body : halts_env Pi ((x, T1) :: Gamma) ((x, v2) :: env)) by (constructor; assumption).
    assert (Hcpenv_body : halts_cpenv Pi eff' (cp_merge cpenv_arg (cp_diff cpenv (eff_singleton p))))
      by (eapply halts_cpenv_diff_merge; eauto).
    destruct (IHHtyp ((x, v2) :: env) (cp_merge cpenv_arg (cp_diff cpenv (eff_singleton p))) Henv_body Hcpenv_body)
      as [v3 [Hev3 Hv3]]. exists v3. split; [exact Hev3|exact Hv3].
  - (* app *)
    assert (Hcpenv12 : halts_cpenv Pi (eff_union eff1 eff2) cpenv)
      by (eapply halts_cpenv_subset; [apply eff_subset_union_r|exact Hcpenv]).
    assert (Hcpenv1 : halts_cpenv Pi eff1 cpenv)
      by (eapply halts_cpenv_subset; [apply eff_subset_union_l|exact Hcpenv12]).
    assert (Hcpenv2 : halts_cpenv Pi eff2 cpenv)
      by (eapply halts_cpenv_subset; [apply eff_subset_union_r|exact Hcpenv12]).
    destruct (IHHtyp1 env cpenv Henv Hcpenv1) as [v1 [Hev1 Hv1]].
    destruct (IHHtyp2 env cpenv Henv Hcpenv2) as [v2 [Hev2 Hv2]].
    simpl in Hv1.
    destruct v1 as [n|x' T1' Tp_cp' p' body env1 cpenv1]; [contradiction|].
    destruct Hv1 as [HTeq [HTcp [Hp Hsem]]]. subst.
    specialize (Hsem v2 Hv2) as Hsem'.
    assert (Hcpenv_p : halts_cpenv Pi (eff_singleton p') cpenv)
      by (eapply halts_cpenv_subset; [apply eff_subset_union_l|exact Hcpenv]).
    destruct Hcpenv_p as [_ [Tpv [vpv [Hctp [Hlk Hvvp]]]]].
    assert (HpTp : Tp_cp' = Tpv).
    {
      match goal with
      | Hcpfun : cp_type Pi p' = Some Tp_cp' |- _ =>
          eapply cp_type_unique; [exact Hcpfun | exact Hctp]
      end.
    }
    rewrite <- HpTp in Hvvp.
    specialize (Hsem' cpenv vpv Hlk Hvvp) as [v3 [Hev3 Hv3]].
    exists v3. split; [econstructor; eauto|exact Hv3].
  - (* with *)
    { assert (Hcpenv1 : halts_cpenv Pi eff1 cpenv)
        by (eapply halts_cpenv_subset; [apply eff_subset_union_l|exact Hcpenv]).
      assert (Hcpenv2diff : halts_cpenv Pi (eff_diff eff2 (eff_singleton p)) cpenv)
        by (eapply halts_cpenv_subset; [apply eff_subset_union_r|exact Hcpenv]).
      destruct (IHHtyp1 env cpenv Henv Hcpenv1) as [v1 [Hev1 Hv1]].
      assert (Hcpenv_update : halts_cpenv Pi eff2 (cp_update p v1 cpenv))
        by (eapply halts_cpenv_update_diff; eauto).
      destruct (IHHtyp2 env (cp_update p v1 cpenv) Henv Hcpenv_update) as [v2 [Hev2 Hv2]].
      exists v2. split; [econstructor; eauto|exact Hv2]. }
  - (* allow *)
    { assert (Hcpenv_restrict : halts_cpenv Pi eff' (cp_restrict eff cpenv))
        by (eapply halts_cpenv_restrict; eauto).
      destruct (IHHtyp env (cp_restrict eff cpenv) Henv Hcpenv_restrict)
        as [v [Hev Hv]].
      exists v. split; [constructor; exact Hev|exact Hv]. }
  - (* sub *)
    { assert (Hcpenv' : halts_cpenv Pi eff cpenv)
        by (eapply halts_cpenv_subset; [apply eff_subset_add|exact Hcpenv]).
      destruct (IHHtyp env cpenv Henv Hcpenv') as [v [Hev Hv]].
      exists v. split; [assumption|exact Hv]. }
Qed.

Theorem soundness_spec_proof : soundness_spec.
Proof.
  intros Pi t T Htyp.
  assert (Henv: halts_env Pi nil nil) by constructor.
  assert (Hcpenv: halts_cpenv Pi eff_empty cp_empty).
  { simpl. trivial. }
  destruct (halts_env_closed (Pi:=Pi) (Gamma:=nil) (env:=nil) cp_empty (T:=T) (t:=t) (eff:=eff_empty) Henv Hcpenv Htyp)
    as [v [Hev _]].
  exists v. exact Hev.
Qed.

Print Assumptions soundness_spec_proof.
