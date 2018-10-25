Require Import PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Max.
Require Import Coq.omega.Omega.

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
| EWhileTrue : forall st st' st'' e c,
    beval st e = true ->
    ceval c (singleton st) (singleton st') ->
    ceval (cwhile e c) (singleton st') (singleton st'') ->
    ceval (cwhile e c) (singleton st) (singleton st'')
| EWhileFalse : forall st e c,
    beval st e = false ->
    ceval (cwhile e c) (singleton st) (singleton st)
| ESeq : forall st st' st'' c1 c2,
    ceval c1 st st' ->
    ceval c2 st' st'' ->
    ceval (cseq c1 c2) st st''
| EProd : forall st1 st1' st2 st2' c1 c2,
    ceval c1 st1 st1' ->
    ceval c2 st2 st2' ->
    ceval (cprod c1 c2) (composite st1 st2) (composite st1' st2').
Hint Constructors ceval.

(* Evaluation relation where while depth is restricted to k iterations. *)
Inductive keval : nat -> com -> state -> state -> Prop :=
| KSkip : forall k st, keval k cskip st st
| KAssign : forall k st x e n,
    aeval st e = n ->
    keval k (x ::= e) (singleton st) (singleton (stupdate x n st))
| KIfTrue : forall k st st' e c1 c2,
    beval st e = true ->
    keval k c1 (singleton st) (singleton st') ->
    keval k (cif e c1 c2) (singleton st) (singleton st')
| KIfFalse : forall k st st' e c1 c2,
    beval st e = false ->
    keval k c2 (singleton st) (singleton st') ->
    keval k (cif e c1 c2) (singleton st) (singleton st')
| KWhileTrue : forall k st st' st'' e c,
    beval st e = true ->
    keval k c (singleton st) (singleton st') ->
    keval k (cwhile e c) (singleton st') (singleton st'') ->
    keval (S k) (cwhile e c) (singleton st) (singleton st'')
| KWhileFalse : forall k st e c,
    beval st e = false ->
    keval k (cwhile e c) (singleton st) (singleton st)
| KSeq : forall k st st' st'' c1 c2,
    keval k c1 st st' ->
    keval k c2 st' st'' ->
    keval k (cseq c1 c2) st st''
| KProd : forall k st1 st1' st2 st2' c1 c2,
    keval k c1 st1 st1' ->
    keval k c2 st2 st2' ->
    keval k (cprod c1 c2) (composite st1 st2) (composite st1' st2').
Hint Constructors keval.

Lemma keval_up : forall st st' c k k',
  k <= k' -> keval k c st st' -> keval k' c st st'.
Proof.
  intros.
  generalize dependent k'.
  induction H0; auto; intros.
  - destruct k'.
    inversion H0.
    eapply KWhileTrue; eauto.
    eapply IHkeval1; omega.
    eapply IHkeval2; omega.
  - eapply KSeq.
    eapply IHkeval1; auto.
    eapply IHkeval2; auto.
Qed.

Lemma keval_ceval : forall st st' c,
  ceval c st st' -> exists k, keval k c st st'.
Proof.
  induction 1.
  - exists 0. auto.
  - exists 0. auto.
  - inversion IHceval; subst.
    exists x.
    eapply KIfTrue; auto.
  - inversion IHceval; subst.
    exists x.
    eapply KIfFalse; auto.
  - inversion IHceval1; subst.
    inversion IHceval2; subst.
    exists (S (max x x0)).
    eapply KWhileTrue; eauto.
    assert (x <= max x x0). apply le_max_l.
    eapply keval_up in H2.
    eapply H2.
    auto.
    assert (x0 <= max x x0). apply le_max_r.
    eapply keval_up in H3.
    eapply H3.
    auto.
  - exists 0. auto.
  - inversion IHceval1; subst.
    inversion IHceval2; subst.
    exists (max x x0).
    assert (x <= max x x0). apply le_max_l.
    assert (x0 <= max x x0). apply le_max_r.
    eapply keval_up in H1; eauto.
    eapply keval_up in H2; eauto.
  - inversion IHceval1; subst.
    inversion IHceval2; subst.
    exists (max x x0).
    assert (x <= max x x0). apply le_max_l.
    assert (x0 <= max x x0). apply le_max_r.
    eapply keval_up in H1; eauto.
    eapply keval_up in H2; eauto.
Qed.



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

Definition ktriple (k:nat) (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st st', keval k c st st' -> P st -> Q st'.

Notation "k |- {{ P }} c {{ Q }}" := (ktriple k P c Q) (at level 90, c at next level).

Definition bassn b : Assertion :=
  fun st => match st with
            | singleton s => (beval s b = true)
            | composite _ _ => False
            end.

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
| PSkipR : forall c, partition c cskip c
| PProd : forall c0 c1 c0' c0'' c1' c1'',
    partition c0' c0'' c0 ->
    partition c1' c1'' c1 ->
    partition (cprod c0' c1') (cprod c0'' c1'') (cprod c0 c1).

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
  - split; intros.
    + inversion H1; subst.
      apply IHpartition1 in H4.
      apply IHpartition2 in H7.
      inversion H4; subst.
      inversion H7; subst.
      econstructor; eauto.
    + inversion H1; subst.
      inversion H4; subst.
      inversion H7; subst.
      constructor.
      apply IHpartition1; eauto.
      apply IHpartition2; eauto.
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

Theorem skip : forall P, {{P}} cskip {{P}}.
Proof.
  unfold triple.
  intros.
  inversion H; subst; auto.
Qed.

Definition first (P:Assertion) (f:state -> Prop) : Assertion :=
  fun st => match st with
  | composite st0 st1 => P st /\ f st0
  | _ => False
  end.

(* Theorem while' : forall P e c0 c1, *)
(*   (1* {{P}} cprod cskip c1 {{P}} -> *1) *)
(*   {{first P (fun st => bassn e st)}} cprod c0 c1 {{P}} -> *)
(*   {{P}} cprod (cwhile e c0) c1 {{first P (fun st => ~(bassn e st))}}. *)
(* Proof. *)
(*   unfold triple. *)
(*   intros. *)
(*   inversion H0; subst. *)
(*   remember (cwhile e c0) as Hc. *)
(*   induction H0; try inversion HeqHc; simpl in *; subst. *)
(*   - simpl. *)
(*   - split. *)
(*     eapply H. *)
(*     inversion H0; subst. *)
(*     inversion H6; subst. *)
    

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

Theorem kseq : forall k (P Q R : Assertion) c0 c1,
  k |- {{P}} c0 {{Q}} ->
  k |- {{Q}} c1 {{R}} ->
  k |- {{P}} cseq c0 c1 {{R}}.
Proof.
  unfold ktriple.
  intros.
  inversion H1; subst.
  eapply H0; eauto.
  eapply H; eauto.
Qed.

Definition pre := pred.

Theorem ktriple_up : forall k k' P Q c,
  k <= k' ->
  k' |- {{P}} c {{Q}} ->
  k |- {{P}} c {{Q}}.
Proof.
  unfold ktriple.
  intros.
  eapply H0.
  eapply  keval_up in H1.
  apply H1.
  auto.
  auto.
Qed.

Theorem kwhile : forall k P c0 e,
  (pre k |- {{fun st => P st /\ bassn e st}}c0{{P}}) ->
  ((pre k |- {{P}} cwhile e c0 {{fun st => P st /\ ~(bassn e st)}}) ->
   (pre k |- {{P}} cseq (cif e c0 cskip) (cwhile e c0) {{fun st => P st /\ ~(bassn e st)}})) ->
  (k |- {{P}} cwhile e c0 {{fun st => P st /\ ~(bassn e st)}}).
Proof.
  intros.
  induction k.
  - unfold ktriple. intros.
    inversion H1; subst. unfold bassn. split; auto; congruence.
  - simpl in *.
    unfold ktriple. intros.
    inversion H1; clear H1; subst.
    + (* True *)
      eapply H0.
      eapply IHk.
      eapply ktriple_up in H.
      apply H.
      unfold pre.
      omega.
      intros.
      apply kseq with P.
      unfold ktriple; intros.
      inversion H3; subst.
      unfold ktriple in H.
      eapply H.
      eapply keval_up in H15.
      apply H15.
      unfold pre.
      omega.
      split; auto.
      inversion H15; subst.
      auto.
      auto.
      econstructor.
      eapply KIfTrue; eauto.
      eauto.
      eauto.
    + (* False *)
      split. auto. unfold bassn. congruence.
Qed.

(* TODO *)
Axiom while : forall P c0 n e,
  ({{P}} cwhile e c0 {{fun st => P st /\ ~(bassn e st)}} ->
   {{P}} cseq (cif e c0 cskip) (cwhile e c0) {{fun st => P st /\ ~(bassn e st)}}) ->
  {{P}} cwhile e c0 {{fun st => P st /\ ~(bassn e st)}}.

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
