Require Import PeanoNat.
Require Import Coq.Lists.List.

Inductive aoper :=
| oadd : aoper
| osub : aoper
| omul : aoper.

Inductive aexpr :=
| aop : aoper -> aexpr -> aexpr -> aexpr
| alit : nat -> aexpr
| avar : nat -> aexpr.

Inductive boper :=
| oeq : boper
| olt : boper
| ole : boper
| ogt : boper
| oge : boper.

Inductive bcomb :=
| oand : bcomb
| oor : bcomb
| oimpl : bcomb.

Inductive bexpr :=
| oop : boper -> aexpr -> aexpr -> bexpr
| bco : bcomb -> bexpr -> bexpr -> bexpr
| bnot : bexpr -> bexpr.

Inductive com :=
| cskip : com
| cassign : nat -> aexpr -> com
| cif : bexpr -> com -> com -> com
| cwhile : nat -> bexpr -> com -> com
(* | ccall : nat -> nat -> nat -> com *)
| cseq : com -> com -> com
| cprod : com -> com -> com.

Notation "x '::=' a" := (cassign x a) (at level 60).

Definition state' := nat -> nat.

Inductive state :=
| singleton : state' -> state
| composite : state -> state -> state.

Definition stempty : state' := fun x => 0.
Definition stupdate x n st : state' := fun k => if k =? x then n else st k.

Fixpoint stupdates xs ns st : state' :=
  match xs with
  | nil => st
  | x :: xs => match ns with
               | nil => st
               | n :: ns => stupdates xs ns (stupdate x n st)
               end
  end.

Fixpoint aeval (st:state') (e:aexpr) : nat :=
  match e with
  | aop o e1 e2 => match o with
                   | oadd => aeval st e1 + aeval st e2
                   | osub => aeval st e1 - aeval st e2
                   | omul => aeval st e1 * aeval st e2
                   end
  | alit n => n
  | avar x => st x
  end.

Fixpoint beval (st:state') (e:bexpr) : bool :=
  match e with
  | oop o e1 e2 => match o with
                   | oeq => aeval st e1 =? aeval st e2
                   | olt => aeval st e1 <? aeval st e2
                   | ole => aeval st e1 <=? aeval st e2
                   | ogt => negb (aeval st e1 <=? aeval st e2)
                   | oge => negb (aeval st e1 <? aeval st e2)
                   end
  | bco o e1 e2 => match o with
                   | oand  => andb  (beval st e1) (beval st e2)
                   | oor   => orb   (beval st e1) (beval st e2)
                   | oimpl => implb (beval st e1) (beval st e2)
                   end
  | bnot e1 => negb (beval st e1)
  end.

Inductive ceval : com -> state -> state -> Prop :=
| ESkip : forall st, ceval cskip st st
| EAssign : forall st x e n,
    aeval st e = n ->
    ceval (x ::= e) (singleton st) (singleton (stupdate x n st))
| EIfTrue : forall st st' e c1 c2,
    beval st e = true ->
    ceval c1 (singleton st) (singleton st') ->
    ceval (cif e c1 c2) (singleton st) (singleton st')
| EIfFalse : forall st st' e c1 c2,
    beval st e = false ->
    ceval c2 (singleton st) (singleton st') ->
    ceval (cif e c1 c2) (singleton st) (singleton st')
| EWhileTrue : forall st st' st'' n e c,
    beval st e = true ->
    ceval c (singleton st) (singleton st') ->
    ceval (cwhile n e c) (singleton st') (singleton st'') ->
    ceval (cwhile (S n) e c) (singleton st) (singleton st'')
| EWhileFalse : forall st e c,
    beval st e = false ->
    ceval (cwhile 0 e c) (singleton st) (singleton st)
| ESeq : forall st st' st'' c1 c2,
    ceval c1 st st' ->
    ceval c2 st' st'' ->
    ceval (cseq c1 c2) st st''
| EProd : forall st1 st1' st2 st2' c1 c2,
    ceval c1 st1 st1' ->
    ceval c2 st2 st2' ->
    ceval (cprod c1 c2) (composite st1 st2) (composite st1' st2')
Hint Constructors ceval.

Definition Assertion := state -> Prop.
Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

Definition assn_sub x e P : Assertion :=
  fun (st : state) => match st with
  | singleton s => P (singleton (stupdate x (aeval s e) s))
  | composite _ _ => False
  end.

Definition triple (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st st', ceval c st st' -> P st -> Q st'.

Notation "{{ P }} c {{ Q }}" := (triple P c Q) (at level 90, c at next level).

Definition bassn b : Assertion :=
  fun st => match st with
            | singleton s => (beval s b = true)
            | composite _ _ => False
            | True => False
            end.

Theorem skip : forall P, {{P}} cskip {{P}}.
Proof.
  unfold triple.
  intros.
  inversion H; subst; auto.
Qed.

Lemma while_unfold : forall n e c st st',
  ceval (cwhile (S n) e c) (singleton st) (singleton st') <->
  (ceval (cseq (cif e c cskip) (cwhile n e c)) (singleton st) (singleton st') /\ beval st e = true)
.
Proof.
  split; intros.
  - inversion H; subst.
    split.
    econstructor; try eassumption.
    apply EIfTrue; eassumption.
    assumption.
  - inversion H; subst.
    inversion H0; subst.
    inversion H4; subst.
    inversion H7; subst.
    eapply EWhileTrue; eassumption.
    eapply EWhileTrue; eassumption.
    congruence.
Qed.


Axiom while : forall P c0 n e,
  ({{P}} cwhile n e c0 {{P}} ->
   {{P}} cseq (cif e c0 cskip) (cwhile n e c0) {{P}}) ->
  {{P}} cwhile (S n) e c0 {{P}}.

Theorem consequence : forall P P' Q Q' c,
  assert_implies P P' ->
  assert_implies Q' Q ->
  {{P'}} c {{Q'}} ->
  {{P}} c {{Q}}.
Proof. unfold triple, assert_implies; eauto. Qed.

Theorem assign : forall P x e,
  {{ assn_sub x e P }} cassign x e {{P}}.
Proof.
  unfold triple; intros; inversion H; subst; auto.
Qed.

Definition first (P:Assertion) (f:state -> Prop) : Assertion :=
  fun st => match st with
  | composite st0 st1 => P st /\ f st0
  | _ => False
  end.

Theorem hoare_if : forall P Q e c0 c1 c2,
  {{first P (fun st => bassn e st)}} cprod c0 c2 {{Q}} ->
  {{first P (fun st => ~(bassn e st))}} cprod c1 c2 {{Q}} ->
  {{P}} cprod (cif e c0 c1) c2 {{Q}}.
Proof.
  unfold triple; intros.
  inversion H1; subst.
  inversion H5; subst.
  - eapply H. constructor; eauto. simpl; eauto.
  - eapply H0. constructor; eauto. simpl. split; eauto. congruence.
Qed.

Inductive partition : com -> com -> com -> Prop :=
| PartL : forall c0 c0' c0'' c1,
    partition c0' c0'' c0 ->
    partition c0' (cseq c0'' c1) (cseq c0 c1)
| PartR : forall c0 c1 c1' c1'',
    partition c1' c1'' c1 ->
    partition (cseq c0 c1') c1'' (cseq c0 c1)
| PSeq : forall c0 c1,
    partition c0 c1 (cseq c0 c1)
| PSkipL : forall c, partition cskip c c
| PSkipR : forall c, partition c cskip c.

Lemma seqassoc : forall c0 c0' c0'' st st',
  ceval (cseq c0 (cseq c0' c0'')) st st' <->
  ceval (cseq (cseq c0 c0') c0'') st st'.
Proof.
  split; intros; inversion H; subst.
  - inversion H5; subst.
    eapply ESeq. eapply ESeq. apply H2. apply H3. assumption.
  - inversion H2; subst.
    eapply ESeq. apply H3. eapply ESeq. apply H7. assumption.
Qed.

Lemma partdeterm : forall c1 c2 c0 st st',
  partition c1 c2 c0 ->
  ceval c0 st st' <-> ceval (cseq c1 c2) st st'.
Proof.
  intros.
  generalize dependent st.
  generalize dependent st'.
  induction H; subst; intros; try (rewrite seqassoc).
  - split; intros H0; inversion H0; subst
    ; econstructor; try (apply IHpartition); eauto.
  - split; intros H0; inversion H0; subst.
    + rewrite <- seqassoc. econstructor; try (apply IHpartition); eauto.
    + inversion H3; repeat (try econstructor; eauto; try (apply IHpartition)).
  - reflexivity.
  - split; intros.
    + eauto.
    + inversion H; inversion H2; auto.
  - split; intros.
    + eapply ESeq. apply H. apply ESkip.
    + inversion H; subst. inversion H5; subst. assumption.
Qed.

Definition pairwise (P:Assertion) (Q:Assertion) : Assertion :=
  fun st => match st with
            | singleton st => False
            | composite st0 st1 => P st0 /\ Q st1
            end.

Lemma splitting : forall (A : Type) (P Q : A -> A -> Prop),
  (forall a b c d, P a b /\ Q c d) <-> (forall a b, P a b) /\ (forall c d, Q c d).
Proof.
  intuition; apply H; auto.
Qed.

Theorem pairing' : forall (P Q R S : Assertion) c0 c1 st0 st1,
  ceval c1 st0 st1 -> Q st0 ->
  {{pairwise P Q}} cprod c0 c1 {{pairwise R S}} ->
  {{P}}c0{{R}}.
Proof.
  unfold triple; intros.
  assert (pairwise R S (composite st' st1)).
  eapply H1.
  constructor; eauto.
  simpl; eauto.
  simpl in H4; apply H4.
Qed.

(* How do I know that the state of c0 does not refer to the state of c1? *)
Lemma pairwise_split : forall P Q R S c0 c1,
  ({{P}} c0 {{R}} /\ {{Q}} c1 {{S}}) <->
  {{pairwise P Q}} cprod c0 c1 {{pairwise R S}}.
Proof.
  unfold triple; split; intros.
  - inversion H; clear H.
    inversion H0; subst; clear H0.
    simpl in *; split.
    + eapply H2. eauto. apply H1.
    + eapply H3. eauto. apply H1.
  - Check consequence.
    apply splitting.
    intros.
    assert
      (ceval c0 a b /\ ceval c1 c d -> P a -> Q c -> R b /\ S d).
    + intros.
      assert (pairwise R S (composite b d)).
      eapply H.
      constructor; apply H0.
      simpl; auto.
      simpl in H3; auto.
    + split.
    apply (composite a b) (composite c d) H.
    apply split_composite.
    Check EProd.
    apply H.

Axiom pairing' : forall P Q R S c0 c1,
  {{pairwise P Q}} cprod c0 c1 {{pairwise R S}} ->
  {{P}}c0{{R}}.

Theorem part : forall P Q R c0 c1 c2,
  partition c1 c2 c0 ->
  (* {{P}} c1 {{R}} -> *)
  {{pairwise P R}} cprod c1 c2 {{pairwise R Q}} ->
  {{P}} c0 {{Q}}.
Proof.
  intros.
  assert ({{P}} c1 {{R}}).
  - eapply pairing'.
    apply H0.
  - unfold triple in *; intros.
    apply (partdeterm c1 c2 c0 st st' H) in H2. inversion H2; subst.
    assert (ceval (cprod c1 c2) (composite st st'0) (composite st'0 st')).
    + constructor; assumption.
    + apply (H0 (composite st st'0) (composite st'0 st') H4).
      unfold pairwise.
      split.
      * assumption.
      * apply H1 with st; auto.
Qed.

Definition commute (P:Assertion) : Assertion :=
  fun st => match st with
            | singleton st => False
            | composite st0 st1 => P (composite st1 st0)
            end.

Theorem comm : forall P Q c0 c1,
  {{ commute P }} cprod c1 c0 {{ commute Q }} ->
  {{ P }} cprod c0 c1 {{ Q }}.
Proof.
  unfold triple. intros.
  inversion H0; subst.
  assert (ceval (cprod c1 c0) (composite st2 st1) (composite st2' st1')).
  - constructor; auto.
  - apply (H (composite st2 st1) (composite st2' st1') H2).
    unfold commute.
    auto.
Qed.

Definition associate (P:Assertion) : Assertion :=
  fun st => match st with
  | composite (composite st0 st1) st2 => P (composite st0 (composite st1 st2))
  | _ => False
  end.

Theorem assoc : forall P Q c0 c1 c2,
  {{ associate P }} cprod (cprod c0 c1) c2 {{ associate Q }} ->
  {{ P }} cprod c0 (cprod c1 c2) {{ Q }}.
Proof.
  unfold triple. intros.
  inversion H0; subst.
  inversion H7; subst.
  assert (ceval (cprod (cprod c0 c1) c2)
            (composite (composite st1 st0) st3)
            (composite (composite st1' st1'0) st2'0)).
  - constructor; auto.
  - apply (H (composite (composite st1 st0) st3)
             (composite (composite st1' st1'0) st2'0) H2).
    unfold associate.
    assumption.
Qed.

Theorem split : forall t (P Q P0 P1 Q0 Q1 : Assertion) c0 c1,
  (forall st0 st1, P (composite st0 st1) -> (P0 st0 /\ P1 st1)) ->
  (forall st0 st1, (Q0 st0 /\ Q1 st1) -> Q (composite st0 st1)) ->
  t |- {{P0}} c0 {{Q0}} ->
  t |- {{P1}} c1 {{Q1}} ->
  t |- {{P}} cprod c0 c1 {{Q}}.
Proof.
  unfold triple.intros.
  inversion H3; subst.
  apply H0.
  split; repeat (try (eapply H2); try (eapply H1); try (eapply H); eauto).
Qed.
