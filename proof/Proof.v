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

Inductive state :=
| singleton : (nat -> nat) -> state
| composite : state -> state -> state.

Definition assertion := state -> Prop.

Inductive com :=
| cassign : nat -> aexpr -> com
| cassume : assertion -> com
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
Notation "'LOOP' '{' c0 '}'" := (cloop c0) (at level 20, right associativity).
Notation "'SKIP'" := cskip.

Notation "st0 '<*>' st1" := (composite st0 st1) (at level 60, right associativity).

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

Inductive ceval : com -> state -> state -> Prop :=
| EAssign : forall st x e n,
    aeval st e = n ->
    ceval (x ::= e) (singleton st) (singleton (stupdate x n st))
| EAssume : forall st (e : assertion),
    e st -> ceval (cassume e) st st
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
  forall st st', 
    ceval c0 st st' <-> ceval c1 st st'.

Notation "c0 '~>' c1" := (supersedes c0 c1) (at level 80, right associativity) : type_scope.
Notation "c0 '~=' c1" := (isomorphic c0 c1) (at level 80, right associativity) : type_scope.

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

Theorem iloop_prod : forall c0 c1,
  LOOP { c0 } *** LOOP { c1 } ~>
  LOOP { c0 +++ SKIP *** c1 +++ SKIP }.
Proof.
  unfold supersedes; intros.
  inversion H; subst.
  remember (LOOP { c0 }) as loop0.
  induction H2; try (inversion Heqloop0); clear Heqloop0; subst.
  + intuition.
    econstructor.
    econstructor;
      [ eapply ESumLeft
      | eapply ESumRight
      ] ; eauto.
    eapply H0. eauto.
  + remember (LOOP { c1 }) as loop1.
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

Theorem iloop_prod2 : forall c0 c1,
  LOOP { c0 } *** LOOP { c1 } ~>
  LOOP { c0 *** c1 } ;; ((LOOP { c0 } *** SKIP) ;; (SKIP *** LOOP { c1 })).
Proof.
  unfold supersedes; intros.
  inversion H; subst; clear H.
  inversion H2; inversion H5; subst; eauto.
Qed.


Definition left (P:assertion) st0 : assertion :=
  fun st1 => P (st0 <*> st1).

Definition right (P:assertion) st1 : assertion :=
  fun st0 => P (st0 <*> st1).

Definition split (P Q:assertion) : assertion :=
  fun st => match st with
  | singleton _ => False
  | composite st0 st1 => P st0 /\ Q st1
  end.

Definition join (P : assertion) : assertion :=
  fun st => match st with
  | singleton _ => False
  | composite st0 st1 => P st0 /\ st0 = st1
  end.

Definition assn_sub x e P : assertion :=
  fun (st : state) => match st with
  | singleton s => P (singleton (stupdate x (aeval s e) s))
  | singleton s <*> st' => P (singleton (stupdate x (aeval s e) s) <*> st')
  | _ <*> _ => False
  end.

Definition commute (P:assertion) : assertion :=
  fun st => match st with
            | singleton st => False
            | composite st0 st1 => P (composite st1 st0)
            end.

Definition associate (P:assertion) : assertion :=
  fun st => match st with
  | composite (composite st0 st1) st2 => P (composite st0 (composite st1 st2))
  | _ => False
  end.

Definition triple (P:assertion) (c:com) (Q:assertion) : Prop :=
  forall st st', ceval c st st' -> P st -> Q st'.

Notation "{{ P }} c {{ Q }}" := (triple P c Q) (at level 90, c at next level).

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

Theorem hoare_supersedes : forall (P Q : assertion) c c',
  c ~> c' -> {{P}} c' {{Q}} -> {{P}} c {{Q}}.
Proof.
  unfold supersedes, triple; intros.
  eapply H0; eauto.
Qed.

Theorem hoare_iso : forall (P Q : assertion) c c',
  c ~= c' -> {{P}} c' {{Q}} -> {{P}} c {{Q}}.
Proof.
  unfold isomorphic, triple; intros.
  eapply H0; eauto.
  eapply H; eauto.
Qed.

Theorem hoare_assign : forall P x e,
  {{assn_sub x e P}} x ::= e {{P}}.
Proof.
  unfold triple, assn_sub; intros; inversion H; subst; eauto.
Qed.

Theorem hoare_assume : forall P e,
  {{P}} ASSUME e {{fun st => P st /\ e st}}.
Proof.
  unfold triple; intros; inversion H; subst; eauto.
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

Theorem hoare_seq : forall (P Q R S : assertion) c0 c1,
  {{join P}} SKIP *** c0 {{R}} ->
  {{R}} c0 *** c1 {{S}} ->
  {{S}} c1 *** SKIP {{join Q}} ->
  {{P}} c0 ;; c1 {{Q}}.
Proof.
  unfold triple, join; intros.
  inversion H2; subst.
  apply (H1 (st'0 <*> st') (st' <*> st')).
  econstructor; eauto.
  eapply H0; eauto.
  eapply H; eauto.
  simpl; eauto.
Qed.

Theorem hoare_prod : forall (P Q R : assertion) c0 c1,
  (forall st1, {{right P st1}} c0 {{right R st1}}) ->
  (forall st0, {{left R st0}} c1 {{left Q st0}}) ->
  {{P}} c0 *** c1 {{Q}}.
Proof.
  unfold triple, left, right; intros.
  inversion H1; subst.
  eauto.
Qed.

Theorem hoare_prod2 : forall (P0 P1 Q0 Q1 : assertion) c0 c1,
  {{P0}} c0 {{Q0}} ->
  {{P1}} c1 {{Q1}} ->
  {{split P0 P1}} c0 *** c1 {{split Q0 Q1}}.

Theorem hoare_cons : forall (P P' Q Q' : assertion) c,
  (forall st, P st -> P' st) ->
  (forall st, Q' st -> Q st) ->
  {{P'}} c {{Q'}} ->
  {{P}} c {{Q}}.
Proof. firstorder. Qed.

Theorem hoare_loop : forall (P : assertion) c,
  {{P}} c {{P}} ->
  {{P}} LOOP { c } {{P}}.
Proof.
  unfold triple; intros.
  remember (LOOP { c }) as loop.
  induction H0; try (inversion Heqloop); clear Heqloop; subst; intuition; eauto.
Qed.
