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
| cwhile : bexpr -> com -> com
| cseq : com -> com -> com
| cprod : com -> com -> com.

Notation "x '::=' a" := (cassign x a) (at level 60).

Definition state := nat -> nat.

Definition stempty : state := fun x => 0.
Definition stupdate x n st : state := fun k => if k =? x then n else st k.

Fixpoint aeval (st:state) (e:aexpr) : nat :=
  match e with
  | aop o e1 e2 => match o with
                   | oadd => aeval st e1 + aeval st e2
                   | osub => aeval st e1 - aeval st e2
                   | omul => aeval st e1 * aeval st e2
                   end
  | alit n => n
  | avar x => st x
  end.

Fixpoint beval (st:state) (e:bexpr) : bool :=
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
    ceval (x ::= e) st (stupdate x n st)
| EIfTrue : forall st st' e c1 c2,
    beval st e = true ->
    ceval c1 st st' ->
    ceval (cif e c1 c2) st st'
| EIfFalse : forall st st' e c1 c2,
    beval st e = false ->
    ceval c2 st st' ->
    ceval (cif e c1 c2) st st'
| EWhileTrue : forall st st' st'' e c,
    beval st e = true ->
    ceval c st st' ->
    ceval (cwhile e c) st' st'' ->
    ceval (cwhile e c) st st''
| EWhileFalse : forall st e c,
    beval st e = false ->
    ceval (cwhile e c) st st
| ESeq : forall st st' st'' c1 c2,
    ceval c1 st st' ->
    ceval c2 st' st'' ->
    ceval (cseq c1 c2) st st''.
Hint Constructors ceval.

Inductive ieval : nat -> com -> state -> state -> Prop :=
| ISkip : forall k st, ieval k cskip st st
| IAssign : forall k st x e n,
    aeval st e = n ->
    ieval k (x ::= e) st (stupdate x n st)
| IIfTrue : forall k st st' e c1 c2,
    beval st e = true ->
    ieval k c1 st st' ->
    ieval k (cif e c1 c2) st st'
| IIfFalse : forall k st st' e c1 c2,
    beval st e = false ->
    ieval k c2 st st' ->
    ieval k (cif e c1 c2) st st'
| IWhileTrue : forall k st st' st'' e c,
    beval st e = true ->
    ieval (S k) c st st' ->
    ieval (S k) (cwhile e c) st' st'' ->
    ieval k (cwhile e c) st st''
| IWhileFalse : forall k st e c,
    beval st e = false ->
    ieval k (cwhile e c) st st
| ISeq : forall k st st' st'' c1 c2,
    ieval k c1 st st' ->
    ieval k c2 st' st'' ->
    ieval k (cseq c1 c2) st st''.
Hint Constructors ieval.

Definition Assertion := state -> Prop.
Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

Definition assn_sub x e P : Assertion :=
  fun (st : state) => P (stupdate x (aeval st e) st).

Definition triple (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st st', ceval c st st' -> P st -> Q st'.

Notation "{{ P }} c {{ Q }}" := (triple P c Q) (at level 90, c at next level).

Definition itriple (k:nat) (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st st', ieval k c st st' -> P st -> Q st'.

Notation "k |- {{ P }} c {{ Q }}" := (itriple k P c Q) (at level 90, c at next level).

Definition bassn b : Assertion :=
  fun st => beval st b = true.

Theorem skip : forall P, {{P}} cskip {{P}}.
Proof.
  unfold triple.
  intros.
  inversion H; subst; auto.
Qed.

Lemma increase_depth : forall j k c st st',
  j <= k ->
  ieval j c st st' ->
  ieval k c st st'.
Proof.
  intros j k c.
  induction c; intros; inversion H0; eauto.
  - subst. admit.
Admitted.

Lemma iwhile_seq : forall P Q k c e,
  S k |- {{P}} cseq (cif e c cskip) (cwhile e c) {{Q}} <->
  k |- {{P}} cwhile e c {{Q}}.
Proof.
  split; unfold itriple; intros.
  - eapply H.
    inversion H0; subst.
    econstructor.
    eapply IIfTrue; eauto.
    eauto.
    econstructor.
    eapply IIfFalse; eauto.
    inversion H0; subst.
    apply increase_depth with k; eauto.
    apply increase_depth with k; eauto.
    eauto.
  - inversion H0; subst.
    eapply H.
    inversion H5; subst.
    eapply IWhileTrue; eauto.
    inversion H11; subst.
    inversion H8; subst.
    congruence.
    eapply IWhileFalse. eauto.
    eauto.
Qed.

Theorem iwhile : forall P k c e,
  (S k |- {{P}} cwhile e c {{fun st => P st /\ not (bassn e st)}} ->
   S k |- {{P}} cseq (cif e c cskip) (cwhile e c) {{fun st => P st /\ not (bassn e st)}}) ->
  k |- {{P}} cwhile e c {{fun st => P st /\ not (bassn e st)}}.
Proof.
  unfold itriple in *; intros; induction k.
  - admit.
  - eapply IHk; intros.
    eapply H; intros.
    inversion H0; subst.


Lemma while_unfold : forall n e c st st',
  ceval (cwhile (S n) e c) st st' <->
  beval st e = true /\ ceval (cseq c (cwhile n e c)) st st'.
Proof.
  split; intros.
  - inversion H; subst; eauto.
  - inversion H; subst; eauto.
    inversion H1; subst.
    econstructor; eauto.
Qed.

Lemma while_unfold_t : forall P Q n e c,
  {{P}} cseq c (cwhile n e c) {{Q}} ->
  {{P}} cwhile (S n) e c {{Q}}.
Proof.
  unfold triple; intros.
  eapply H.
  rewrite while_unfold in H0.
  inversion H0; subst; clear H0.
  inversion H3; subst; clear H3.
  econstructor; eauto.
  eauto.
Qed.

Theorem hoare_seq : forall P Q R c0 c1,
  {{P}} c0 {{R}} ->
  {{R}} c1 {{Q}} ->
  {{P}} cseq c0 c1 {{Q}}.
Admitted.


Theorem while : forall P n c e,
  ({{P}} cwhile n e c {{fun st => P st /\ not (bassn e st)}} ->
   {{P}} cseq c (cwhile n e c) {{fun st => P st /\ not (bassn e st)}}) ->
  {{P}} cwhile (S n) e c {{fun st => P st /\ not (bassn e st)}}.
Proof.
  intros.
  induction n.
  - unfold triple in *; intros; rewrite while_unfold in H0.
    inversion H0.
    eapply H; intros; eauto.
    + inversion H4; subst.
      split; auto; try congruence.
  - apply while_unfold_t.
    eapply hoare_seq.
    + admit.
    + apply IHn.
    + unfold triple in *; intros.
      eapply H; intros.
      eapply IHn; intros.
    a

Qed.

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

Definition pairwise (P:Assertion) (Q:Assertion) : Assertion :=
  fun st => match st with
            | singleton st => False
            | composite st0 st1 => P st0 /\ Q st1
            end.

Theorem part : forall P Q R c0 c1 c2,
  partition c1 c2 c0 ->
  {{P}} c1 {{R}} ->
  {{pairwise P R}} cprod c1 c2 {{pairwise R Q}} ->
  {{P}} c0 {{Q}}.
Proof.
  unfold triple; intros.
  apply (partdeterm c1 c2 c0 st st' H) in H2. inversion H2; subst.
  assert (ceval (cprod c1 c2) (composite st st'0) (composite st'0 st')).
  - constructor; assumption.
  - apply (H1 (composite st st'0) (composite st'0 st') H4).
    unfold pairwise.
    split.
    + assumption.
    + apply H0 with st; auto.
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

Theorem split : forall (P Q P0 P1 Q0 Q1 : Assertion) c0 c1,
  (forall st0 st1, P (composite st0 st1) -> (P0 st0 /\ P1 st1)) ->
  (forall st0 st1, (Q0 st0 /\ Q1 st1) -> Q (composite st0 st1)) ->
  {{P0}} c0 {{Q0}} ->
  {{P1}} c1 {{Q1}} ->
  {{P}} cprod c0 c1 {{Q}}.
Proof.
  unfold triple; intros.
  inversion H3; subst.
  apply H0.
  split; repeat (try (eapply H2); try (eapply H1); try (eapply H); eauto).
Qed.

Theorem seq : forall (P Q R : Assertion) c0 c1 c2,
  partition c1 c2 c0 ->
  {{P}} c1 {{Q}} ->
  {{Q}} c2 {{R}} ->
  {{P}} c0 {{R}}.
Proof.
  intros.
  eapply part; eauto.
  eapply split; simpl; eauto.
Qed.
