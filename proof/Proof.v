Require Import PeanoNat.

(** The space of arithmetic operations. *)
Inductive aoper :=
| oadd : aoper
| osub : aoper
| omul : aoper.

(** The space of arithmetic expressions. *)
Inductive aexpr :=
| aop : aoper -> aexpr -> aexpr -> aexpr
| alit : nat -> aexpr
| avar : nat -> aexpr.

(** The space of program states. *)
Inductive state :=
| singleton : (nat -> nat) -> state (* Singleton map from variable to value *)
| composite : state -> state -> state. (* Two parallel states *)

(** An assertion is a function from a program state to a proposition *)
Definition assertion := state -> Prop.

(** The space of (non-deterministic) program comnmands. *)
Inductive com :=
| cassign : nat -> aexpr -> com
| cassert : assertion -> com
| cseq : com -> com -> com
| csum : com -> com -> com
| cprod : com -> com -> com
| cloop : com -> com
| cskip : com.

Notation "x '::=' a" := (cassign x a) (at level 20).
Notation "'ASSERT' e" := (cassert e) (at level 20, right associativity).
Notation "c0 ';;' c1" := (cseq c0 c1) (at level 55, right associativity).
Notation "c0 '+++' c1" := (csum c0 c1) (at level 60, right associativity).
Notation "c0 '***' c1" := (cprod c0 c1) (at level 65, right associativity).
Notation "'LOOP' '{' c0 '}'" := (cloop c0) (at level 20, right associativity).
Notation "'SKIP'" := cskip.

Notation "st0 '<*>' st1" := (composite st0 st1) (at level 60, right associativity).

(** Replace `x' in the singleton state `st'. *)
Definition stupdate x n st : nat -> nat := fun k => if k =? x then n else st k.

(** Evaluate an arithmetic expression over a singleton state. *)
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

(** The inductively defined evaluation relation for commands. *)
Inductive ceval : com -> state -> state -> Prop :=
(* Assignments update the state by replacing the variable by the result of
 * evaluating the expression. *)
| EAssign : forall st x e n,
    aeval st e = n ->
    ceval (x ::= e) (singleton st) (singleton (stupdate x n st))
(* Assertions have no effect on the state. If the assertion does not hold, the
 * evaluation is stuck. *)
| EAssert : forall st (e : assertion),
    e st -> ceval (cassert e) st st
(* Sequences thread state between the two commands. *)
| ESeq : forall st st' st'' c0 c1,
    ceval c0 st st' ->
    ceval c1 st' st'' ->
    ceval (cseq c0 c1) st st''
(* A sum can carry the effect of evaluating the left summand. *)
| ESumLeft : forall st st' c0 c1,
    ceval c0 st st' ->
    ceval (csum c0 c1) st st'
(* A sum can carry the effect of evaluating the right summand. *)
| ESumRight : forall st st' c0 c1,
    ceval c1 st st' ->
    ceval (csum c0 c1) st st'
(* Products evaluate over two parallel states independently *)
| EProd : forall st1 st1' st2 st2' c1 c2,
    ceval c1 st1 st1' ->
    ceval c2 st2 st2' ->
    ceval (cprod c1 c2) (st1 <*> st2) (st1' <*> st2')
(* A loop can carry the effect of evaluating its body followed by evaluating itself. *)
| ELoop : forall st st' st'' c,
    ceval c st st' ->
    ceval (cloop c) st' st'' ->
    ceval (cloop c) st st''
(* A loop can have no effect. *)
| EBreak : forall st c,
    ceval (cloop c) st st
(* Skip has no effect. *)
| ESkip : forall st, ceval cskip st st.
Hint Constructors ceval.

(** To handle most interesting proofs, we need a way to rewrite commands if
 * they are equivalent. We capture this equivalence through an isomorphism
 * definition which states that the effect of evaluating the two commands is
 * the same. *)
Definition isomorphic (c0:com) (c1:com) : Prop :=
  forall st st', 
    ceval c0 st st' <-> ceval c1 st st'.

(** Supersedes is a weaker form of isomorphism. We say that c0 supersedes c1 if
 * c0 captures the effect of c1. *)
Definition supersedes (c0:com) (c1:com) : Prop :=
  forall st st', 
    ceval c0 st st' -> ceval c1 st st'.

Notation "c0 '~>' c1" := (supersedes c0 c1) (at level 80, right associativity) : type_scope.
Notation "c0 '~=' c1" := (isomorphic c0 c1) (at level 80, right associativity) : type_scope.

Definition expansive (c:com) : Prop :=
  (LOOP { c }) ~= (LOOP { c } ;; c).

(** We can sequence skips to the left of commands *)
Theorem iskipl : forall c, SKIP ;; c ~= c.
Proof.
  unfold isomorphic; split; intros.
  inversion H; subst.
  - inversion H2; eauto.
  - eauto.
Qed.

(** We can sequence skips to the right of commands *)
Theorem iskipr : forall c, c ;; SKIP ~= c.
Proof.
  unfold isomorphic; split; intros.
  inversion H; subst.
  - inversion H5; subst; eauto.
  - eauto.
Qed.

(** Command sequencing is associative with respect to evaluation. *)
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

(** Product distributes over sequences. *)
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

(** Product distributes over sums. *)
Theorem isumprod : forall c0 c1 c2,
  (c0 +++ c1) *** c2 ~= (c0 *** c2) +++ (c1 *** c2).
Proof.
  unfold isomorphic; split; intros.
  - inversion H; subst; inversion H2; subst; firstorder.
  - inversion H; subst; inversion H4; subst; firstorder.
Qed.

(** The product of loops can be rewritten as a loop of products (with additional subsequent commands). *)
Theorem iloop_prod : forall c0 c1,
  LOOP { c0 } *** LOOP { c1 } ~>
  LOOP { c0 *** c1 } ;; ((LOOP { c0 } *** SKIP) ;; (SKIP *** LOOP { c1 })).
Proof.
  unfold supersedes; intros.
  inversion H; subst; clear H.
  inversion H2; inversion H5; subst; eauto.
Qed.

Theorem iseq : forall c0 c1 c0' c1',
  c0 ~= c0' ->
  c1 ~= c1' ->
  c0 ;; c1 ~= c0' ;; c1'.
Proof.
  unfold isomorphic.
  split; intros.
  - inversion H1; subst.
    econstructor. rewrite <- H. eapply H4.
    firstorder.
  - inversion H1; subst.
    econstructor. rewrite H. eapply H4.
    firstorder.
Qed.

Theorem iprod : forall c0 c1 c0' c1',
  c0 ~= c0' ->
  c1 ~= c1' ->
  c0 *** c1 ~= c0' *** c1'.
Proof.
  unfold isomorphic.
  split; intros.
  - inversion H1; subst.
    econstructor. rewrite <- H. eapply H4.
    firstorder.
  - inversion H1; subst.
    econstructor. rewrite H. eapply H4.
    firstorder.
Qed.

Theorem irefl : forall c, c ~= c.
Proof.  firstorder. Qed.

Theorem isymm : forall c0 c1, c0 ~= c1 -> c1 ~= c0.
Proof. firstorder. Qed.

Theorem itrans : forall c0 c1 c2, c0 ~= c1 -> c1 ~= c2 -> c0 ~= c2.
Proof. unfold isomorphic. firstorder.
  rewrite <- H0.  rewrite <- H.  eauto.
  apply H.  apply H0.  eauto.
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

Definition pairwise (P Q : assertion) : assertion :=
  fun st => match st with
  | singleton _ => False
  | composite st0 st1 => P st0 /\ Q st1
  end.

Definition assn_sub x e P : assertion :=
  fun (st : state) => match st with
  | singleton s => P (singleton (stupdate x (aeval s e) s))
  | singleton s <*> st' => P (singleton (stupdate x (aeval s e) s) <*> st')
  | _ <*> _ => False
  end.

Definition triple (P:assertion) (c:com) (Q:assertion) : Prop :=
  forall st st', ceval c st st' -> P st -> Q st'.

Notation "{{ P }} c {{ Q }}" := (triple P c Q) (at level 90, c at next level).

Definition bind : assertion :=
  fun st => match st with
  | composite st0 st1 => st0 = st1
  | _ => False
  end.

Theorem hoare_cons : forall (P P' Q Q' : assertion) c,
  (forall st, P st -> P' st) ->
  (forall st, Q' st -> Q st) ->
  {{P'}} c {{Q'}} ->
  {{P}} c {{Q}}.
Proof. firstorder. Qed.

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

Theorem hoare_assert : forall P e,
  {{P}} ASSERT e {{fun st => P st /\ e st}}.
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

Theorem hoare_seq : forall (P Q R : assertion) c0 c1,
  {{P}} c0 {{R}} ->
  {{R}} c1 {{Q}} ->
  {{P}} c0 ;; c1 {{Q}}.
Proof.
  unfold triple; intros. inversion H1; firstorder.
Qed.

Theorem hoare_loop : forall (P : assertion) c,
  {{P}} c {{P}} ->
  {{P}} LOOP { c } {{P}}.
Proof.
  unfold triple; intros.
  remember (LOOP { c }) as loop.
  induction H0; try (inversion Heqloop); clear Heqloop; subst; intuition; eauto.
Qed.

Theorem hoare_dupl : forall (P Q : assertion) c,
  {{join P}} c *** c {{join Q}} ->
  {{P}} c {{Q}}.
Proof.
  unfold triple, join; intros.
  assert (Q st' /\ st' = st').
  eapply (H (composite st st) (composite st' st')); eauto.
  eapply H2.
Qed.

Theorem hoare_dupl' : forall (P Q : assertion) c,
  {{join P}} c *** c {{pairwise Q Q}} ->
  {{P}} c {{Q}}.
Proof.
  unfold triple, join, pairwise; intros.
  eapply (H (composite st st) (composite st' st')); eauto.
Qed.

Theorem hoare_prod_seq : forall (P Q R S : assertion) c0 c1,
  {{join P}} SKIP *** c0 {{R}} ->
  {{R}} c0 *** c1 {{S}} ->
  {{S}} c1 *** SKIP {{join Q}} ->
  {{P}} c0 ;; c1 {{Q}}.
Proof.
  intros.
  eapply hoare_dupl.
  assert ((c0 ;; c1 *** c0 ;; c1) ~= ((SKIP *** c0) ;; (c0 *** c1) ;; (c1 *** SKIP))).
  - eapply itrans.
    { eapply iprod.
      + eapply isymm. eapply iskipl.
      + eapply isymm. eapply iseq. eapply irefl. eapply iskipr.  }
    { eapply itrans.
      + eapply iseqprod.
      + eapply iseq. eapply irefl. eapply iseqprod.  }
  - eapply hoare_iso. eapply H2.
    eapply hoare_seq; eauto.
    eapply hoare_seq; eauto.
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
