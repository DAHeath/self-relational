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
| bop : boper -> aexpr -> aexpr -> bexpr
| bco : bcomb -> bexpr -> bexpr -> bexpr
| bnot : bexpr -> bexpr.

Inductive com :=
| cassign : nat -> aexpr -> com
| cassume : bexpr -> com
| cseq : com -> com -> com
| csum : com -> com -> com
| cprod : com -> com -> com
| cloop : com -> com
| cskip : com.

Notation "x '::=' a" := (cassign x a) (at level 20).
Notation "'ASSUME' e" := (cassume e) (at level 20, right associativity).
Notation "c0 ';;' c1" := (cseq c0 c1) (at level 55, right associativity).
Notation "c0 '+++' c1" := (csum c0 c1) (at level 60, right associativity).
Notation "c0 '***' c1" := (cprod c0 c1) (at level 65, right associativity).
Notation "'LOOP' c0" := (cloop c0) (at level 20, right associativity).
Notation "'SKIP'" := cskip.

Inductive state :=
| singleton : (nat -> nat) -> state
| composite : state -> state -> state.

Notation "st0 '<*>' st1" := (composite st0 st1) (at level 60, right associativity).

Definition stempty : nat -> nat := fun x => 0.
Definition stupdate x n st : nat -> nat := fun k => if k =? x then n else st k.

Fixpoint aeval (st:nat -> nat) (e:aexpr) : nat :=
  match e with
  | aop o e1 e2 => match o with
                   | oadd => aeval st e1 + aeval st e2
                   | osub => aeval st e1 - aeval st e2
                   | omul => aeval st e1 * aeval st e2
                   end
  | alit n => n
  | avar x => st x
  end.

Fixpoint beval (st:nat -> nat) (e:bexpr) : bool :=
  match e with
  | bop o e1 e2 => match o with
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
| EAssign : forall st x e n,
    aeval st e = n ->
    ceval (x ::= e) (singleton st) (singleton (stupdate x n st))
| EAssume : forall st e,
    beval st e = true ->
    ceval (cassume e) (singleton st) (singleton st)
| ESeq : forall st st' st'' c0 c1,
    ceval c0 st st' ->
    ceval c1 st' st'' ->
    ceval (cseq c0 c1) st st''
| ESumLeft : forall st st' c0 c1,
    ceval c0 st st' ->
    ceval (csum c0 c1) st st'
| ESumRight : forall st st' c0 c1,
    ceval c1 st st' ->
    ceval (csum c0 c1) st st'
| EProd : forall st1 st1' st2 st2' c1 c2,
    ceval c1 st1 st1' ->
    ceval c2 st2 st2' ->
    ceval (cprod c1 c2) (st1 <*> st2) (st1' <*> st2')
| ELoop : forall st st' st'' c,
    ceval c st st' ->
    ceval (cloop c) st' st'' ->
    ceval (cloop c) st st''
| EBreak : forall st c,
    ceval (cloop c) st st
| ESkip : forall st, ceval cskip st st.
Hint Constructors ceval.

Definition supersedes (c0:com) (c1:com) : Prop :=
  forall st st', 
    ceval c0 st st' -> ceval c1 st st'.

Definition isomorphic (c0:com) (c1:com) : Prop :=
  supersedes c0 c1 /\ supersedes c1 c0.

Notation "c0 '~>' c1" := (supersedes c0 c1) (at level 80, right associativity) : type_scope.
Notation "c0 '~=' c1" := (isomorphic c0 c1) (at level 80, right associativity) : type_scope.

Check (forall c, c ~= c).

Theorem irefl : forall c, c ~= c.
Proof. unfold isomorphic; intuition. Qed.

Theorem isymm : forall c0 c1, c0 ~= c1 -> c1 ~= c0.
Proof. unfold isomorphic; intuition; eapply H; eauto. Qed.

Theorem itrans : forall c0 c1 c2, c0 ~= c1 -> c1 ~= c2 -> c0 ~= c2.
Proof.
  unfold isomorphic; intuition.
  - eapply H0; eapply H; eauto.
  - eapply H; eapply H0; eauto.
Qed.

Theorem iskipl : forall c, SKIP ;; c ~= c.
Proof.
  unfold isomorphic; split; intros.
  inversion H; subst.
  - inversion H2; eauto.
  - eauto.
Qed.

Theorem iskipr : forall c, c ;; SKIP ~= c.
Proof.
  unfold isomorphic; split; intros.
  inversion H; subst.
  - inversion H5; subst; eauto.
  - eauto.
Qed.

Theorem iseqassoc : forall c0 c1 c2, (c0 ;; c1) ;; c2 ~= c0 ;; (c1 ;; c2).
Proof.
  unfold isomorphic; split; intros.
  - inversion H; subst; clear H.
    inversion H2; subst; clear H2.
    eauto.
  - inversion H; subst; clear H.
    inversion H5; subst; clear H5.
    eauto.
Qed.

Theorem iskipprod : SKIP *** SKIP ~= SKIP.
Proof.
  unfold isomorphic; split; intros.
  - inversion H; subst.
    inversion H2; subst.
    inversion H5; subst.
    eauto.
  - inversion H; subst.
    destruct st'.
    + admit. (* ??? *)
    + eauto.
Admitted.

Theorem iseqprod : forall c0 c1 c2 c3,
  (c0 ;; c1) *** (c2 ;; c3) ~= (c0 *** c2) ;; (c1 *** c3).
Proof.
  unfold isomorphic; split; intros.
  - inversion H.
    inversion H2.
    inversion H5; subst.
    eauto.
  - inversion H.
    inversion H2; subst.
    inversion H5; subst.
    eauto.
Qed.

Theorem isumprod : forall c0 c1 c2,
  (c0 +++ c1) *** c2 ~= (c0 *** c2) +++ (c1 *** c2).
Proof.
  unfold isomorphic; split; intros.
  - inversion H; subst; inversion H2; subst; firstorder.
  - inversion H; subst; inversion H4; subst; firstorder.
Qed.

Theorem iseq : forall c0 c0' c1 c1',
  c0 ~= c0' -> c1 ~= c1' -> c0 ;; c1 ~= c0' ;; c1'.
Proof.
  unfold isomorphic; split; intros; inversion H1; subst; econstructor
  ; try (eapply H) ; try (eapply H0) ; eauto.
Qed.

Theorem isum : forall c0 c0' c1 c1',
  c0 ~= c0' -> c1 ~= c1' -> c0 +++ c1 ~= c0' +++ c1'.
Proof.
  unfold isomorphic; split; intros; inversion H1; subst;
  [ eapply ESumLeft; eapply H
  | eapply ESumRight; eapply H0
  | eapply ESumLeft; eapply H
  | eapply ESumRight; eapply H0
  ]; eauto.
Qed.

Theorem iprod : forall c0 c0' c1 c1',
  c0 ~= c0' -> c1 ~= c1' -> c0 *** c1 ~= c0' *** c1'.
Proof.
  unfold isomorphic; split; intros; inversion H1; subst; econstructor
  ; try (eapply H) ; try (eapply H0) ; eauto.
Qed.

Theorem iloop : forall c c',
  c ~= c' -> LOOP c ~= LOOP c'.
Proof.
  unfold isomorphic; split; intros
  ; [ remember (LOOP c) as loop
    | remember (LOOP c') as loop
    ] ; induction H0; try (inversion Heqloop); subst; intuition;
    econstructor; try (eapply H); eauto.
Qed.

Theorem iloop_prod : forall c0 c1,
  LOOP c0 *** LOOP c1 ~>
  LOOP (c0 +++ SKIP *** c1 +++ SKIP).
Proof.
  unfold supersedes; intros.
  inversion H; subst.
  remember (LOOP c0) as loop0.
  induction H2; try (inversion Heqloop0); clear Heqloop0; subst.
  + intuition.
    econstructor.
    econstructor;
      [ eapply ESumLeft
      | eapply ESumRight
      ] ; eauto.
    eapply H0. eauto.
  + remember (LOOP c1) as loop1.
    induction H5; try (inversion Heqloop1); clear Heqloop1; subst.
    * intuition.
      econstructor.
      econstructor;
        [ eapply ESumRight
        | eapply ESumLeft
        ] ; eauto.
      eapply H0; eauto.
    * eauto.
Qed.

Definition Assertion := state -> Prop.

Definition assn_sub x e P : Assertion :=
  fun (st : state) => match st with
  | singleton s => P (singleton (stupdate x (aeval s e) s))
  | singleton s <*> st' => P (singleton (stupdate x (aeval s e) s) <*> st')
  | _ <*> _ => False
  end.

Definition triple (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st st', ceval c st st' -> P st -> Q st'.

Notation "{{ P }} c {{ Q }}" := (triple P c Q) (at level 90, c at next level).

Definition bassn b : Assertion :=
  fun st => match st with
            | singleton s => beval s b = true
            | singleton s <*> _ => beval s b = true
            | _ <*> _ => False
            end.

Definition commute (P:Assertion) : Assertion :=
  fun st => match st with
            | singleton st => False
            | composite st0 st1 => P (composite st1 st0)
            end.

Definition hoare_comm : forall P Q c0 c1,
  {{commute P}} c1 *** c0 {{commute Q}} ->
  {{P}} c0 *** c1 {{Q}}.
Proof.
  unfold triple, commute; intros.
  inversion H0; subst; simpl in *.
  assert (ceval (c1 *** c0) (st2 <*> st1) (st2' <*> st1')); auto.
  apply (H (st2 <*> st1) (st2' <*> st1') H2).
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

Theorem hoare_supersedes : forall (P Q : Assertion) c c',
  c ~> c' -> {{P}} c' {{Q}} -> {{P}} c {{Q}}.
Proof.
  unfold supersedes, triple; intros.
  eapply H0; eauto.
Qed.

Theorem hoare_iso : forall (P Q : Assertion) c c',
  c ~= c' -> {{P}} c' {{Q}} -> {{P}} c {{Q}}.
Proof.
  unfold isomorphic, triple; intros.
  eapply H0; eauto.
  eapply H; eauto.
Qed.

Definition left (P : Assertion) : Assertion := fun st =>
  match st with
  | st0 <*> st1 => P st0
  | _ => False
  end.

Theorem hoare_skip_intro : forall (P Q : Assertion) c,
  {{left P}} c *** SKIP {{left Q}} ->
  {{P}} c {{Q}}.
Proof.
  unfold triple; intros.
  assert (left Q (st' <*> singleton (fun _ => 0))). eapply H.
  econstructor; eauto.
  simpl; eauto.
  eauto.
Qed.

Theorem hoare_assign : forall P x e,
  {{assn_sub x e P}} x ::= e {{P}}.
Proof.
  unfold triple, assn_sub; intros; inversion H; subst; eauto.
Qed.

Theorem hoare_assume : forall P e,
  {{P}} ASSUME e {{fun st => P st /\ bassn e st}}.
Proof.
  unfold triple, bassn; intros; inversion H; subst; eauto.
Qed.

Theorem hoare_skip : forall P,
  {{P}} SKIP {{P}}.
Proof.
  unfold triple; intros; inversion H; subst; auto.
Qed.

Theorem hoare_sum : forall P Q c0 c1,
  {{P}} c0 {{Q}} ->
  {{P}} c1 {{Q}} ->
  {{P}} c0 +++ c1 {{Q}}.
Proof.
  unfold triple; intros; inversion H1; inversion H5; subst; eauto.
Qed.

Definition pairwise (P:Assertion) (Q:Assertion) : Assertion :=
  fun st => match st with
            | singleton st => False
            | composite st0 st1 => P st0 /\ Q st1
            end.

Theorem hoare_seq : forall P Q R c0 c1,
  {{P}} c0 {{R}} ->
  {{pairwise P R}} c0 *** c1 {{pairwise R Q}} ->
  {{P}} c0 ;; c1 {{Q}}.
Proof.
  unfold triple; intros.
  inversion H1; subst; clear H1.
  assert (ceval (c0 *** c1) (st <*> st'0) (st'0 <*> st')).
  - constructor; assumption.
  - assert (pairwise P R (st <*> st'0) -> pairwise R Q (st'0 <*> st')).
    intros.
    eapply H0; eauto.
    firstorder.
Qed.

Theorem hoare_prod : forall (P P0 P1 Q Q0 Q1 : Assertion) c0 c1,
  (forall st0 st1, P (st0 <*> st1) -> P0 st0 /\ P1 st1) ->
  (forall st0 st1, Q0 st0 /\ Q1 st1 -> Q (st0 <*> st1)) ->
  {{P0}} c0 {{Q0}} ->
  {{P1}} c1 {{Q1}} ->
  {{P}} c0 *** c1 {{Q}}.
Proof.
  unfold triple; intros.
  inversion H3; subst.
  eapply H0.
  firstorder.
Qed.

Theorem hoare_cons : forall (P P' Q Q' : Assertion) c,
  (forall st, P st -> P' st) ->
  (forall st, Q' st -> Q st) ->
  {{P'}} c {{Q'}} ->
  {{P}} c {{Q}}.
Proof. firstorder. Qed.

Theorem hoare_loop : forall (P : Assertion) c,
  {{P}} c {{P}} ->
  {{P}} LOOP c {{P}}.
Proof.
  unfold triple; intros.
  remember (LOOP c) as loop.
  induction H0; try (inversion Heqloop); clear Heqloop; subst; intuition; eauto.
Qed.
