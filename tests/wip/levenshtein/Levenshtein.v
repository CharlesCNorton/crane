(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Copyright (c) 2019 Joomy Korkut. MIT license. *)
(* Intrinsically proven sound Levenshtein distance implementation *)
From Stdlib Require Import String Ascii Nat Lia.
From Stdlib Require Import Program.Equality.
From Stdlib Require Import Arith.Wf_nat.

Open Scope string_scope.
Infix "::" := String (at level 60, right associativity) : string_scope.
Notation "[ x ]" := (String x EmptyString) : string_scope.
Notation "[ x ; y ; .. ; z ]" := (String x (String y .. (String z EmptyString) ..)) : string_scope.

Module Levenshtein.

Inductive edit : string -> string -> Type :=
| insertion (a : ascii) {s : string} : edit s (a :: s)
| deletion (a : ascii) {s : string} : edit (a :: s) s
| update (a' : ascii) (a : ascii)
         {neq : a' <> a} {s : string} : edit (a' :: s) (a :: s).

Inductive chain : string -> string -> nat -> Type :=
| empty : chain "" "" 0
| skip {a : ascii} {s t : string} {n : nat} :
    chain s t n -> chain (a :: s) (a :: t) n
| change {s t u : string} {n : nat} :
    edit s t -> chain t u n -> chain s u (S n).

Lemma chain_length_bounds :
  forall s t n (c : chain s t n),
    length t <= length s + n /\ length s <= length t + n.
Proof.
  intros s t n c.
  induction c as [|a s t n c IH|s t u n e c IH].
  - simpl. split; lia.
  - destruct IH as [IH1 IH2].
    simpl in *.
    split; lia.
  - destruct IH as [IH1 IH2].
    destruct e.
    + simpl in *.
      split; lia.
    + simpl in *.
      split; lia.
    + simpl in *.
      split; lia.
Qed.

Lemma same_chain : forall s, chain s s 0.
Proof.
  intros s. induction s; constructor; auto.
Defined.

Lemma chain_is_same : forall s t, chain s t 0 -> s = t.
Proof.
  intros s t c. dependent induction c.
  auto. f_equal. auto.
Qed.

Lemma insert_chain : forall c s1 s2 n, chain s1 s2 n -> chain s1 (c :: s2) (S n).
Proof.
  intros c s1 s2 n C.
  apply (@change _ (c :: s1)); constructor. auto.
Defined.

Lemma inserts_chain : forall s1 s2, chain s2 (s1 ++ s2) (length s1).
Proof.
  intros.
  induction s1; simpl.
  induction s2; constructor; auto.
  apply insert_chain; auto.
Defined.

(* transparent string version of app_nil_r *)
Lemma tr_app_empty_r : forall {A : Type} (l : string), l ++ "" = l.
Proof.
  intros A l; induction l. auto. simpl; rewrite IHl; auto.
Defined.

Lemma inserts_chain_empty : forall s, chain "" s (length s).
Proof.
  intros s.
  induction s; simpl.
  constructor.
  apply insert_chain. auto.
Defined.

Lemma delete_chain : forall c s1 s2 n, chain s1 s2 n -> chain (c :: s1) s2 (S n).
Proof.
  intros c s1 s2 n C.
  apply (@change _ s1). constructor. auto.
Defined.

Lemma deletes_chain : forall s1 s2, chain (s1 ++ s2) s2 (length s1).
Proof.
  intros.
  induction s1; simpl.
  apply same_chain.
  apply delete_chain.
  auto.
Defined.

Lemma deletes_chain_empty : forall s, chain s "" (length s).
Proof.
  intros s.
  induction s; simpl.
  constructor. apply delete_chain. auto.
Defined.

Lemma update_chain : forall c c' s1 s2 n,
    c <> c' -> chain s1 s2 n -> chain (c :: s1) (c' :: s2) (S n).
Proof.
  intros c c' s1 s2 n neq C.
  apply (@change _ (c' :: s1)). constructor. auto. apply skip. auto.
Defined.

(* These aux lemmas are needed because Coq wants to use the fixpoint
   we are defining as a higher order function otherwise. *)
Lemma aux_insert : forall s t x xs y ys n,
    s = x :: xs -> t = y :: ys -> chain s ys n -> chain s t (S n).
Proof.
  intros s t x xs y ys n eq1 eq2 r1.
  subst.
  apply (insert_chain y (x :: xs) ys n r1).
Defined.

Lemma aux_delete : forall s t x xs y ys n,
    s = x :: xs -> t = y :: ys -> chain xs (y :: ys) n -> chain s t (S n).
Proof.
  intros s t x xs y ys n eq1 eq2 r2.
  subst.
  apply (delete_chain x xs (y :: ys) n r2).
Defined.

Lemma aux_update : forall s t x xs y ys n,
    x <> y -> s = x :: xs -> t = y :: ys -> chain xs ys n -> chain s t (S n).
Proof.
  intros s t x xs y ys n neq eq1 eq2 r3.
  subst.
  apply (update_chain x y xs ys n neq r3).
Defined.

Lemma aux_eq_char : forall s t x xs y ys n,
    s = x :: xs -> t = y :: ys -> x = y -> chain xs ys n -> chain s t n.
Proof.
  intros s t x xs y ys n eq1 eq2 ceq C.
  subst. apply skip. auto.
Defined.

Lemma aux_both_empty : forall s t, s = "" -> t = "" -> chain s t 0.
Proof.
  intros s t eq1 eq2. subst. constructor.
Defined.

Lemma leb_false : forall (n m : nat), (n <=? m)%nat = false -> (m <? n)%nat = true.
Proof.
  intros n m H.
  rewrite PeanoNat.Nat.leb_antisym in *.
  assert (eq : forall b, negb b = false -> b = true).
    intros; destruct b; auto.
  exact (eq _ H).
Qed.

Definition min3_app {t : Type} (x y z : t) (f : t -> nat) : t :=
  let n1 := f x in let n2 := f y in let n3 := f z in
  match (Nat.leb n1 n2) with
  | true => match (Nat.leb n1 n3) with | true => x | false => z end
  | false => match (Nat.leb n2 n3) with | true => y | false => z end
  end.

Lemma min3_app_pf {t : Type} (x y z : t) (f : t -> nat) :
    (f (min3_app x y z f) <= f x
  /\ f (min3_app x y z f) <= f y
  /\ f (min3_app x y z f) <= f z)%nat.
Proof.
  unfold min3_app.
  destruct (Nat.leb (f x) (f y)) eqn:leb1.
  * destruct (Nat.leb (f x) (f z)) eqn:leb2.
    - rewrite (PeanoNat.Nat.leb_le (f x) (f y)) in *.
      rewrite (PeanoNat.Nat.leb_le (f x) (f z)) in *.
      auto.
    - rewrite (PeanoNat.Nat.leb_le (f x) (f y)) in *.
      pose ((proj1 (PeanoNat.Nat.ltb_lt (f z) (f x))) (leb_false _ _ leb2)).
      lia.
  * destruct (Nat.leb (f y) (f z)) eqn:leb3.
    - rewrite (PeanoNat.Nat.leb_le (f y) (f z)) in *.
      pose ((proj1 (PeanoNat.Nat.ltb_lt (f y) (f x))) (leb_false _ _ leb1)).
      lia.
    - pose ((proj1 (PeanoNat.Nat.ltb_lt (f z) (f y))) (leb_false _ _ leb3)).
      pose ((proj1 (PeanoNat.Nat.ltb_lt (f y) (f x))) (leb_false _ _ leb1)).
      lia.
Qed.

Lemma min3_app_cases {t : Type} (x y z : t) (f : t -> nat) (P : t -> Prop) :
  P x -> P y -> P z -> P (min3_app x y z f).
Proof.
  intros Hx Hy Hz.
  unfold min3_app.
  destruct (Nat.leb (f x) (f y)); destruct (Nat.leb _ _); auto.
Qed.

Lemma min3_app_value {t : Type} (x y z : t) (f : t -> nat) :
  f (min3_app x y z f) = Nat.min (f x) (Nat.min (f y) (f z)).
Proof.
  unfold min3_app.
  destruct (Nat.leb (f x) (f y)) eqn:Hxy.
  - destruct (Nat.leb (f x) (f z)) eqn:Hxz.
    + apply PeanoNat.Nat.leb_le in Hxy.
      apply PeanoNat.Nat.leb_le in Hxz.
      rewrite (PeanoNat.Nat.min_l (f x) (Nat.min (f y) (f z))).
      2:{ apply PeanoNat.Nat.min_glb; lia. }
      reflexivity.
    + apply PeanoNat.Nat.leb_le in Hxy.
      apply PeanoNat.Nat.leb_gt in Hxz.
      rewrite (PeanoNat.Nat.min_r (f y) (f z)) by lia.
      rewrite (PeanoNat.Nat.min_r (f x) (f z)) by lia.
      reflexivity.
  - destruct (Nat.leb (f y) (f z)) eqn:Hyz.
    + apply PeanoNat.Nat.leb_gt in Hxy.
      apply PeanoNat.Nat.leb_le in Hyz.
      rewrite (PeanoNat.Nat.min_l (f y) (f z)) by lia.
      rewrite (PeanoNat.Nat.min_r (f x) (f y)) by lia.
      reflexivity.
    + apply PeanoNat.Nat.leb_gt in Hxy.
      apply PeanoNat.Nat.leb_gt in Hyz.
      rewrite (PeanoNat.Nat.min_r (f y) (f z)) by lia.
      rewrite (PeanoNat.Nat.min_r (f x) (f z)) by lia.
      reflexivity.
Qed.

Lemma min3_comm12 : forall a b c : nat,
  Nat.min a (Nat.min b c) = Nat.min b (Nat.min a c).
Proof.
  intros a b c.
  lia.
Qed.

Fixpoint levenshtein_chain (s : string)  :=
  fix levenshtein_chain1 (t : string) : {n : nat & chain s t n} :=
    (match s as s', t as t' return s = s' -> t = t' -> {n : nat & chain s t n} with
    | "" , "" =>
        fun eq1 eq2 => existT _ 0 (aux_both_empty s t eq1 eq2)
    | "" , _ =>
        fun eq1 eq2 =>
          existT _ (length t)
            ltac:(rewrite eq1; apply (inserts_chain_empty t))
    | y :: ys , "" =>
        fun eq1 eq2 =>
          existT _ (length s)
            ltac:(rewrite eq1, eq2; apply (deletes_chain_empty (y :: ys)))
    | x :: xs, y :: ys =>
      fun eq1 eq2 =>
        match ascii_dec x y with
        | left ceq =>
          let (n, c) := levenshtein_chain xs ys in
          existT _ n (aux_eq_char s t x xs y ys n eq1 eq2 ceq c)
        | right neq =>
          let (n1, r1) := levenshtein_chain1 ys in
          let (n2, r2) := levenshtein_chain xs (y :: ys) in
          let (n3, r3) := levenshtein_chain xs ys in
          let r1' : chain s t (S n1) :=
              aux_insert s t x xs y ys n1 eq1 eq2 r1 in
          let r2' : chain s t (S n2) :=
              aux_delete s t x xs y ys n2 eq1 eq2 r2 in
          let r3' : chain s t (S n3) :=
              aux_update s t x xs y ys n3 neq eq1 eq2 r3 in
          min3_app (existT (fun (n : nat) => chain s t n) (S n1) r1')
                   (existT _ (S n2) r2')
                   (existT _ (S n3) r3')
                   (fun p => projT1 p)
        end
    end) (eq_refl s) (eq_refl t).

Definition levenshtein_computed (s t : string) : nat :=
  projT1 (levenshtein_chain s t).

Lemma levenshtein_computed_of_chain :
  forall s t n (c : chain s t n),
    levenshtein_chain s t = existT (fun k : nat => chain s t k) n c ->
    levenshtein_computed s t = n.
Proof.
  intros s t n c Hc.
  unfold levenshtein_computed.
  rewrite Hc.
  reflexivity.
Qed.

Definition levenshtein (s t : string) : nat :=
  levenshtein_computed s t.

Lemma levenshtein_computed_nil_l :
  forall t, levenshtein_computed EmptyString t = length t.
Proof.
  intros t.
  unfold levenshtein_computed.
  destruct t as [|a t']; cbn; reflexivity.
Qed.

Lemma levenshtein_computed_nil_r :
  forall s, levenshtein_computed s EmptyString = length s.
Proof.
  intros s.
  unfold levenshtein_computed.
  destruct s as [|a s']; cbn; reflexivity.
Qed.

Lemma levenshtein_computed_length_bounds :
  forall s t,
    length t <= length s + levenshtein_computed s t
    /\ length s <= length t + levenshtein_computed s t.
Proof.
  intros s t.
  unfold levenshtein_computed.
  destruct (levenshtein_chain s t) as [n c].
  simpl.
  exact (chain_length_bounds s t n c).
Qed.

Lemma levenshtein_le_computed : forall s t, levenshtein s t <= projT1 (levenshtein_chain s t).
Proof.
  intros s t.
  unfold levenshtein, levenshtein_computed.
  lia.
Qed.

Lemma levenshtein_computed_skip_eq : forall a s t,
    levenshtein_computed (a :: s) (a :: t) = levenshtein_computed s t.
Proof.
  intros a s t.
  unfold levenshtein_computed.
  cbn.
  destruct (ascii_dec a a) as [Haa|Haa].
  - dependent destruction Haa.
    destruct (levenshtein_chain s t) as [n c].
    cbn.
    reflexivity.
  - exfalso.
    apply Haa.
    reflexivity.
Qed.

Lemma levenshtein_computed_cons_neq :
  forall a b s t,
    a <> b ->
    levenshtein_computed (a :: s) (b :: t) =
      Nat.min (S (levenshtein_computed (a :: s) t))
              (Nat.min (S (levenshtein_computed s (b :: t)))
                       (S (levenshtein_computed s t))).
Proof.
  intros a b s t Hneq.
  unfold levenshtein_computed.
  cbn.
  destruct (ascii_dec a b) as [Heq|Hneqab].
  - exfalso.
    apply Hneq.
    exact Heq.
  - remember (levenshtein_chain (a :: s) t) as p1.
    remember (levenshtein_chain s (b :: t)) as p2.
    remember (levenshtein_chain s t) as p3.
    destruct p1 as [n1 c1], p2 as [n2 c2], p3 as [n3 c3].
    cbn.
    try match goal with
    | |- context [let (_, _) := ?p in _] =>
        change p with (levenshtein_chain (a :: s) t)
    end.
    try rewrite <- Heqp1.
    cbn.
    try match goal with
    | |- context [let (_, _) := ?p in _] =>
        change p with (levenshtein_chain s (b :: t))
    end.
    try rewrite <- Heqp2.
    cbn.
    try match goal with
    | |- context [let (_, _) := ?p in _] =>
        change p with (levenshtein_chain s t)
    end.
    try rewrite <- Heqp3.
    cbn.
    rewrite (min3_app_value
      (existT (fun n : nat => chain (a :: s) (b :: t) n) (S n1)
              (insert_chain b (a :: s) t n1 c1))
      (existT (fun n : nat => chain (a :: s) (b :: t) n) (S n2)
              (delete_chain a s (b :: t) n2 c2))
      (existT (fun n : nat => chain (a :: s) (b :: t) n) (S n3)
              (update_chain a b s t n3 Hneqab c3))
      (fun p => projT1 p)).
    pose proof
      (levenshtein_computed_of_chain (a :: s) t n1 c1 (eq_sym Heqp1))
      as Hp1.
    pose proof
      (levenshtein_computed_of_chain s (b :: t) n2 c2 (eq_sym Heqp2))
      as Hp2.
    pose proof
      (levenshtein_computed_of_chain s t n3 c3 (eq_sym Heqp3))
      as Hp3.
    cbn.
    reflexivity.
Qed.

Lemma levenshtein_computed_mismatch_upper_insert : forall a b s t,
    a <> b ->
    levenshtein_computed (a :: s) (b :: t) <= S (levenshtein_computed (a :: s) t).
Proof.
  intros a b s t Hneq.
  rewrite levenshtein_computed_cons_neq by exact Hneq.
  lia.
Qed.

Lemma levenshtein_computed_mismatch_upper_delete : forall a b s t,
    a <> b ->
    levenshtein_computed (a :: s) (b :: t) <= S (levenshtein_computed s (b :: t)).
Proof.
  intros a b s t Hneq.
  rewrite levenshtein_computed_cons_neq by exact Hneq.
  lia.
Qed.

Lemma levenshtein_computed_mismatch_upper_update : forall a b s t,
    a <> b ->
    levenshtein_computed (a :: s) (b :: t) <= S (levenshtein_computed s t).
Proof.
  intros a b s t Hneq.
  rewrite levenshtein_computed_cons_neq by exact Hneq.
  lia.
Qed.

Lemma levenshtein_computed_insert_lower :
  forall a s t,
    levenshtein_computed s t <= S (levenshtein_computed (a :: s) t).
Proof.
  intros a0 s0 t0.
  refine (
    well_founded_induction
      lt_wf
      (fun m =>
         forall a s t, length s + length t = m ->
           levenshtein_computed s t <= S (levenshtein_computed (a :: s) t))
      _
      (length s0 + length t0)
      a0 s0 t0 eq_refl).
  intros m IH a s t Hm.
  destruct s as [|x xs], t as [|y ys].
  - rewrite levenshtein_computed_nil_l, levenshtein_computed_nil_r.
    simpl. lia.
  - assert (Hlen :
        length ys <= levenshtein_computed (a :: "") (y :: ys)).
    {
      pose proof (levenshtein_computed_length_bounds (a :: "") (y :: ys)) as [H1 _].
      simpl in H1.
      lia.
    }
    rewrite levenshtein_computed_nil_l.
    simpl. lia.
  - rewrite !levenshtein_computed_nil_r.
    simpl. lia.
  - destruct (ascii_dec x y) as [Hxy|Hxy].
    + subst y.
      rewrite levenshtein_computed_skip_eq.
      destruct (ascii_dec a x) as [Hax|Hax].
      * subst a.
        rewrite levenshtein_computed_skip_eq.
        assert (Hrec :
          levenshtein_computed xs ys <=
          S (levenshtein_computed (x :: xs) ys)).
        {
          apply (IH (length xs + length ys)).
          - simpl in Hm. lia.
          - reflexivity.
        }
        exact Hrec.
      * unfold levenshtein_computed.
        cbn.
        destruct (ascii_dec a x) as [Hcontra|Hnax].
        { exfalso. apply Hax. exact Hcontra. }
        remember (levenshtein_chain (a :: x :: xs) ys) as p1.
        remember (levenshtein_chain (x :: xs) (x :: ys)) as p2.
        remember (levenshtein_chain (x :: xs) ys) as p3.
        destruct p1 as [n1 r1], p2 as [n2 r2], p3 as [n3 r3].
        cbn.
        assert (H3 :
          levenshtein_computed xs ys <= S n3).
        {
          assert (Hrec :
            levenshtein_computed xs ys <=
            S (levenshtein_computed (x :: xs) ys)).
          {
            apply (IH (length xs + length ys)).
            - simpl in Hm. lia.
            - reflexivity.
          }
          pose proof
            (levenshtein_computed_of_chain (x :: xs) ys n3 r3 (eq_sym Heqp3))
            as Hc3.
          rewrite Hc3 in Hrec.
          exact Hrec.
        }
        assert (H1 :
          levenshtein_computed xs ys <= S (S n1)).
        {
          assert (Hxys :
            levenshtein_computed (x :: xs) ys <= S n1).
          {
            assert (Htmp :
              levenshtein_computed (x :: xs) ys <=
              S (levenshtein_computed (a :: x :: xs) ys)).
            {
              apply (IH (S (length xs) + length ys)).
              - simpl in Hm. lia.
              - reflexivity.
            }
            pose proof
              (levenshtein_computed_of_chain (a :: x :: xs) ys n1 r1 (eq_sym Heqp1))
              as Hc1.
            rewrite Hc1 in Htmp.
            exact Htmp.
          }
          assert (Hrec :
            levenshtein_computed xs ys <=
            S (levenshtein_computed (x :: xs) ys)).
          {
            apply (IH (length xs + length ys)).
            - simpl in Hm. lia.
            - reflexivity.
          }
          lia.
        }
        assert (H2 :
          levenshtein_computed xs ys <= S (S n2)).
        {
          pose proof
            (levenshtein_computed_of_chain (x :: xs) (x :: ys) n2 r2 (eq_sym Heqp2))
            as Hc2.
          rewrite levenshtein_computed_skip_eq in Hc2.
          lia.
        }
        match goal with
        | |- context [let (_, _) := ?p in _] =>
            change p with (levenshtein_chain (a :: x :: xs) ys)
        end.
        try rewrite <- Heqp1.
        cbn.
        match goal with
        | |- context [let (_, _) := ?p in _] =>
            change p with (levenshtein_chain (x :: xs) (x :: ys))
        end.
        rewrite <- Heqp2.
        cbn.
        match goal with
        | |- context [let (_, _) := ?p in _] =>
            change p with (levenshtein_chain (x :: xs) ys)
        end.
        rewrite <- Heqp3.
        cbn.
        eapply (min3_app_cases
          (existT (fun n : nat => chain (a :: x :: xs) (x :: ys) n) (S n1)
                  (insert_chain x (a :: x :: xs) ys n1 r1))
          (existT (fun n : nat => chain (a :: x :: xs) (x :: ys) n) (S n2)
                  (delete_chain a (x :: xs) (x :: ys) n2 r2))
          (existT (fun n : nat => chain (a :: x :: xs) (x :: ys) n) (S n3)
                  (update_chain a x (x :: xs) ys n3 Hnax r3))
          (fun p => projT1 p)
          (fun p => levenshtein_computed xs ys <= S (projT1 p))).
        -- exact H1.
        -- exact H2.
        -- cbn. lia.
    + unfold levenshtein_computed.
      cbn.
      remember (levenshtein_chain (x :: xs) ys) as q1.
      remember (levenshtein_chain xs (y :: ys)) as q2.
      remember (levenshtein_chain xs ys) as q3.
      destruct q1 as [l1 c1], q2 as [l2 c2], q3 as [l3 c3].
      cbn.
      pose proof (min3_app_pf
        (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S l1)
                (insert_chain y (x :: xs) ys l1 c1))
        (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S l2)
                (delete_chain x xs (y :: ys) l2 c2))
        (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S l3)
                (update_chain x y xs ys l3 Hxy c3))
        (fun p => projT1 p)) as [HL1 [HL2 HL3]].
      destruct (ascii_dec a y) as [Hay|Hay].
      * subst a.
        assert (Hq1 :
          levenshtein_computed (x :: xs) ys = l1).
        {
          exact (levenshtein_computed_of_chain (x :: xs) ys l1 c1 (eq_sym Heqq1)).
        }
        destruct (ascii_dec x y) as [Hcontra|Hxy'].
        { exfalso. apply Hxy. exact Hcontra. }
        cbn.
        match goal with
        | |- context [let (_, _) := ?p in _] =>
            change p with (levenshtein_chain (x :: xs) ys)
        end.
        rewrite <- Heqq1.
        cbn.
        pose proof (min3_app_pf
          (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S l1)
                  (insert_chain y (x :: xs) ys l1 c1))
          (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S l2)
                  (delete_chain x xs (y :: ys) l2 c2))
          (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S l3)
                  (update_chain x y xs ys l3 Hxy' c3))
          (fun p => projT1 p)) as [HL1' _].
        cbn in HL1'.
        exact HL1'.
      * unfold levenshtein_computed.
        cbn.
        destruct (ascii_dec a y) as [Hcontra|Hnay].
        { exfalso. apply Hay. exact Hcontra. }
        remember (levenshtein_chain (a :: x :: xs) ys) as p1.
        remember (levenshtein_chain (x :: xs) (y :: ys)) as p2.
        remember (levenshtein_chain (x :: xs) ys) as p3.
        destruct p1 as [n1 r1], p2 as [n2 r2], p3 as [n3 r3].
        cbn.
        assert (Hc1 :
          projT1 (min3_app
            (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S l1)
                    (insert_chain y (x :: xs) ys l1 c1))
            (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S l2)
                    (delete_chain x xs (y :: ys) l2 c2))
            (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S l3)
                    (update_chain x y xs ys l3 Hxy c3))
            (fun p => projT1 p)) <= S l1).
        {
          exact HL1.
        }
        assert (H1 :
          projT1 (min3_app
            (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S l1)
                    (insert_chain y (x :: xs) ys l1 c1))
            (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S l2)
                    (delete_chain x xs (y :: ys) l2 c2))
            (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S l3)
                    (update_chain x y xs ys l3 Hxy c3))
            (fun p => projT1 p)) <= S (S n1)).
        {
          assert (Hrec :
            levenshtein_computed (x :: xs) ys <=
            S (levenshtein_computed (a :: x :: xs) ys)).
          {
            apply (IH (S (length xs) + length ys)).
            - simpl in Hm. lia.
            - reflexivity.
          }
          assert (Hl1n3 : l1 = n3).
          { inversion Heqq1. reflexivity. }
          pose proof
            (levenshtein_computed_of_chain (x :: xs) ys n3 r3 (eq_sym Heqp3))
            as Hq3.
          pose proof
            (levenshtein_computed_of_chain (a :: x :: xs) ys n1 r1 (eq_sym Heqp1))
            as Hp1.
          rewrite Hq3 in Hrec.
          rewrite Hp1 in Hrec.
          assert (Hl1le : l1 <= S n1).
          { rewrite Hl1n3. exact Hrec. }
          lia.
        }
        assert (H2 :
          projT1 (min3_app
            (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S l1)
                    (insert_chain y (x :: xs) ys l1 c1))
            (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S l2)
                    (delete_chain x xs (y :: ys) l2 c2))
            (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S l3)
                    (update_chain x y xs ys l3 Hxy c3))
            (fun p => projT1 p)) <= S (S n2)).
        {
          assert (Hrec2 :
            levenshtein_computed xs (y :: ys) <=
            S (levenshtein_computed (x :: xs) (y :: ys))).
          {
            apply (IH (length xs + S (length ys))).
            - simpl in Hm. lia.
            - reflexivity.
          }
          pose proof
            (levenshtein_computed_of_chain xs (y :: ys) l2 c2 (eq_sym Heqq2))
            as Hq2.
          pose proof
            (levenshtein_computed_of_chain (x :: xs) (y :: ys) n2 r2 (eq_sym Heqp2))
            as Hp2.
          rewrite Hq2 in Hrec2.
          rewrite Hp2 in Hrec2.
          eapply PeanoNat.Nat.le_trans.
          - exact HL2.
          - cbn. lia.
        }
        assert (H3 :
          projT1 (min3_app
            (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S l1)
                    (insert_chain y (x :: xs) ys l1 c1))
            (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S l2)
                    (delete_chain x xs (y :: ys) l2 c2))
            (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S l3)
                    (update_chain x y xs ys l3 Hxy c3))
            (fun p => projT1 p)) <= S (S n3)).
        {
          assert (Hrec3 :
            levenshtein_computed xs ys <=
            S (levenshtein_computed (x :: xs) ys)).
          {
            apply (IH (length xs + length ys)).
            - simpl in Hm. lia.
            - reflexivity.
          }
          pose proof
            (levenshtein_computed_of_chain xs ys l3 c3 (eq_sym Heqq3))
            as Hq3'.
          pose proof
            (levenshtein_computed_of_chain (x :: xs) ys n3 r3 (eq_sym Heqp3))
            as Hp3.
          rewrite Hq3' in Hrec3.
          rewrite Hp3 in Hrec3.
          eapply PeanoNat.Nat.le_trans.
          - exact HL3.
          - cbn. lia.
        }
        destruct (ascii_dec x y) as [Hcontra|Hxy'].
        { exfalso. apply Hxy. exact Hcontra. }
        cbn.
        assert (Hn3n1 : n3 <= S n1).
        {
          assert (Hrecx :
            levenshtein_computed (x :: xs) ys <=
            S (levenshtein_computed (a :: x :: xs) ys)).
          {
            apply (IH (S (length xs) + length ys)).
            - simpl in Hm. lia.
            - reflexivity.
          }
          pose proof
            (levenshtein_computed_of_chain (x :: xs) ys n3 r3 (eq_sym Heqp3))
            as Hp3.
          pose proof
            (levenshtein_computed_of_chain (a :: x :: xs) ys n1 r1 (eq_sym Heqp1))
            as Hp1.
          rewrite Hp3 in Hrecx.
          rewrite Hp1 in Hrecx.
          exact Hrecx.
        }
        remember (min3_app
          (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S n3)
                  (insert_chain y (x :: xs) ys n3 r3))
          (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S l2)
                  (delete_chain x xs (y :: ys) l2 c2))
          (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S l3)
                  (update_chain x y xs ys l3 Hxy' c3))
          (fun p => projT1 p)) as q2.
        destruct q2 as [m2 c2'].
        cbn.
        pose proof (min3_app_pf
          (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S n3)
                  (insert_chain y (x :: xs) ys n3 r3))
          (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S l2)
                  (delete_chain x xs (y :: ys) l2 c2))
          (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S l3)
                  (update_chain x y xs ys l3 Hxy' c3))
          (fun p => projT1 p)) as [Hm2_1 [Hm2_2 Hm2_3]].
        cbn in Hm2_1, Hm2_2, Hm2_3.
        assert (Hm2_1' : m2 <= S n3).
        {
          change m2 with
            (projT1
               (existT (fun n : nat => chain (x :: xs) (y :: ys) n) m2 c2')).
          rewrite Heqq0.
          exact Hm2_1.
        }
        try match goal with
        | |- context [let (_, _) := ?p in _] =>
            change p with (levenshtein_chain (x :: xs) ys)
        end.
        rewrite <- Heqp3.
        cbn.
        try rewrite <- Heqq0.
        cbn.
        try match goal with
        | |- context [let (_, _) := ?p in _] =>
            change p with (levenshtein_chain (a :: x :: xs) ys)
        end.
        try rewrite <- Heqp1.
        cbn.
        try match goal with
        | |- context [let (_, _) := ?p in _] =>
            change p with (levenshtein_chain (x :: xs) (y :: ys))
        end.
        try rewrite <- Heqq0.
        cbn.
        try match goal with
        | |- context [let (_, _) := ?p in _] =>
            change p with (levenshtein_chain (x :: xs) ys)
        end.
        try rewrite <- Heqp3.
        cbn.
        eapply (min3_app_cases
          (existT (fun n : nat => chain (a :: x :: xs) (y :: ys) n) (S n1)
                  (insert_chain y (a :: x :: xs) ys n1 r1))
          (existT (fun n : nat => chain (a :: x :: xs) (y :: ys) n) (S m2)
                  (delete_chain a (x :: xs) (y :: ys) m2 c2'))
          (existT (fun n : nat => chain (a :: x :: xs) (y :: ys) n) (S n3)
                  (update_chain a y (x :: xs) ys n3 Hay r3))
          (fun p => projT1 p)
          (fun p => m2 <= S (projT1 p))).
        -- eapply PeanoNat.Nat.le_trans.
           ++ exact Hm2_1'.
           ++ cbn. lia.
        -- cbn. lia.
        -- eapply PeanoNat.Nat.le_trans.
           ++ exact Hm2_1'.
           ++ cbn. lia.
Qed.

Lemma levenshtein_computed_sym :
  forall s t, levenshtein_computed s t = levenshtein_computed t s.
Proof.
  intros s0 t0.
  refine (
    well_founded_induction
      lt_wf
      (fun m =>
         forall s t, length s + length t = m ->
           levenshtein_computed s t = levenshtein_computed t s)
      _
      (length s0 + length t0)
      s0 t0 eq_refl).
  intros m IH s t Hm.
  destruct s as [|x xs], t as [|y ys].
  - reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - destruct (ascii_dec x y) as [Hxy|Hxy].
    + subst y.
      rewrite levenshtein_computed_skip_eq.
      rewrite (levenshtein_computed_skip_eq x ys xs).
      apply (IH (length xs + length ys)).
      { simpl in Hm. lia. }
      { reflexivity. }
    + unfold levenshtein_computed.
      cbn.
      destruct (ascii_dec x y) as [Hcontra|Hnxy].
      { exfalso. apply Hxy. exact Hcontra. }
      destruct (ascii_dec y x) as [Hyx|Hnyx].
      { exfalso. apply Hxy. symmetry. exact Hyx. }
      remember (levenshtein_chain (x :: xs) ys) as p1.
      remember (levenshtein_chain xs (y :: ys)) as p2.
      remember (levenshtein_chain xs ys) as p3.
      remember (levenshtein_chain (y :: ys) xs) as q1.
      remember (levenshtein_chain ys (x :: xs)) as q2.
      remember (levenshtein_chain ys xs) as q3.
      destruct p1 as [n1 c1], p2 as [n2 c2], p3 as [n3 c3].
      destruct q1 as [m1 c4], q2 as [m2 c5], q3 as [m3 c6].
      cbn.
      assert (H12 : n1 = m2).
      {
        assert (Hrec :
          levenshtein_computed (x :: xs) ys =
          levenshtein_computed ys (x :: xs)).
        {
          apply (IH (S (length xs) + length ys)).
          { simpl in Hm. lia. }
          { reflexivity. }
        }
        pose proof
          (levenshtein_computed_of_chain (x :: xs) ys n1 c1 (eq_sym Heqp1))
          as Hp1.
        pose proof
          (levenshtein_computed_of_chain ys (x :: xs) m2 c5 (eq_sym Heqq2))
          as Hq2.
        rewrite Hp1 in Hrec.
        rewrite Hq2 in Hrec.
        exact Hrec.
      }
      assert (H21 : n2 = m1).
      {
        assert (Hrec :
          levenshtein_computed xs (y :: ys) =
          levenshtein_computed (y :: ys) xs).
        {
          apply (IH (length xs + S (length ys))).
          { simpl in Hm. lia. }
          { reflexivity. }
        }
        pose proof
          (levenshtein_computed_of_chain xs (y :: ys) n2 c2 (eq_sym Heqp2))
          as Hp2.
        pose proof
          (levenshtein_computed_of_chain (y :: ys) xs m1 c4 (eq_sym Heqq1))
          as Hq1.
        rewrite Hp2 in Hrec.
        rewrite Hq1 in Hrec.
        exact Hrec.
      }
      assert (H33 : n3 = m3).
      {
        assert (Hrec :
          levenshtein_computed xs ys =
          levenshtein_computed ys xs).
        {
          apply (IH (length xs + length ys)).
          { simpl in Hm. lia. }
          { reflexivity. }
        }
        pose proof
          (levenshtein_computed_of_chain xs ys n3 c3 (eq_sym Heqp3))
          as Hp3.
        pose proof
          (levenshtein_computed_of_chain ys xs m3 c6 (eq_sym Heqq3))
          as Hq3.
        rewrite Hp3 in Hrec.
        rewrite Hq3 in Hrec.
        exact Hrec.
      }
      try match goal with
      | |- context [let (_, _) := ?p in _] =>
          change p with (levenshtein_chain (x :: xs) ys)
      end.
      try rewrite <- Heqp1.
      cbn.
      try match goal with
      | |- context [let (_, _) := ?p in _] =>
          change p with (levenshtein_chain xs (y :: ys))
      end.
      try rewrite <- Heqp2.
      cbn.
      try match goal with
      | |- context [let (_, _) := ?p in _] =>
          change p with (levenshtein_chain xs ys)
      end.
      try rewrite <- Heqp3.
      cbn.
      try match goal with
      | |- context [let (_, _) := ?p in _] =>
          change p with (levenshtein_chain (y :: ys) xs)
      end.
      try rewrite <- Heqq1.
      cbn.
      try match goal with
      | |- context [let (_, _) := ?p in _] =>
          change p with (levenshtein_chain ys (x :: xs))
      end.
      try rewrite <- Heqq2.
      cbn.
      try match goal with
      | |- context [let (_, _) := ?p in _] =>
          change p with (levenshtein_chain ys xs)
      end.
      try rewrite <- Heqq3.
      cbn.
      rewrite (min3_app_value
        (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S n1)
                (insert_chain y (x :: xs) ys n1 c1))
        (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S n2)
                (delete_chain x xs (y :: ys) n2 c2))
        (existT (fun n : nat => chain (x :: xs) (y :: ys) n) (S n3)
                (update_chain x y xs ys n3 Hnxy c3))
        (fun p => projT1 p)).
      rewrite (min3_app_value
        (existT (fun n : nat => chain (y :: ys) (x :: xs) n) (S m1)
                (insert_chain x (y :: ys) xs m1 c4))
        (existT (fun n : nat => chain (y :: ys) (x :: xs) n) (S m2)
                (delete_chain y ys (x :: xs) m2 c5))
        (existT (fun n : nat => chain (y :: ys) (x :: xs) n) (S m3)
                (update_chain y x ys xs m3 Hnyx c6))
        (fun p => projT1 p)).
      cbn.
      rewrite <- H12, <- H21, <- H33.
      f_equal.
      apply min3_comm12.
Qed.

Lemma levenshtein_computed_insert_lower_r :
  forall a s t,
    levenshtein_computed s t <= S (levenshtein_computed s (a :: t)).
Proof.
  intros a s t.
  rewrite (levenshtein_computed_sym s t).
  rewrite (levenshtein_computed_sym s (a :: t)).
  apply levenshtein_computed_insert_lower.
Qed.

Lemma levenshtein_computed_delete_upper :
  forall a s t,
    levenshtein_computed (a :: s) t <= S (levenshtein_computed s t).
  Proof.
  intros a s t.
  destruct t as [|b ys].
  - rewrite !levenshtein_computed_nil_r.
    simpl. lia.
  - destruct (ascii_dec a b) as [Hab|Hab].
    + subst b.
      rewrite levenshtein_computed_skip_eq.
      apply levenshtein_computed_insert_lower_r.
    + apply levenshtein_computed_mismatch_upper_delete.
      exact Hab.
Qed.

Lemma levenshtein_computed_update_upper :
  forall a a' s t,
    a' <> a ->
    levenshtein_computed (a' :: s) t <= S (levenshtein_computed (a :: s) t).
Proof.
  intros a0 a'0 s0 t0 Hneq0.
  refine (
    well_founded_induction
      lt_wf
      (fun m =>
         forall a a' s t, a' <> a ->
           length s + length t = m ->
           levenshtein_computed (a' :: s) t <=
           S (levenshtein_computed (a :: s) t))
      _
      (length s0 + length t0)
      a0 a'0 s0 t0 Hneq0 eq_refl).
  intros m IH a a' s t Hneq Hm.
  destruct t as [|b ys].
  - rewrite !levenshtein_computed_nil_r.
    simpl. lia.
  - destruct (ascii_dec a' b) as [Ha'b|Ha'b].
    + subst b.
      rewrite levenshtein_computed_skip_eq.
      unfold levenshtein_computed.
      cbn.
      destruct (ascii_dec a a') as [Hcontra|Hna].
      { exfalso. apply Hneq. symmetry. exact Hcontra. }
      remember (levenshtein_chain (a :: s) ys) as p1.
      remember (levenshtein_chain s (a' :: ys)) as p2.
      remember (levenshtein_chain s ys) as p3.
      destruct p1 as [n1 r1], p2 as [n2 r2], p3 as [n3 r3].
      cbn.
      assert (H1 : levenshtein_computed s ys <= S (S n1)).
      {
        assert (Hrec : levenshtein_computed s ys <= S (levenshtein_computed (a :: s) ys)).
        { apply levenshtein_computed_insert_lower. }
        pose proof
          (levenshtein_computed_of_chain (a :: s) ys n1 r1 (eq_sym Heqp1))
          as Hp1.
        rewrite Hp1 in Hrec.
        lia.
      }
      assert (H2 : levenshtein_computed s ys <= S (S n2)).
      {
        assert (Hrec : levenshtein_computed s ys <= S (levenshtein_computed s (a' :: ys))).
        { apply levenshtein_computed_insert_lower_r. }
        pose proof
          (levenshtein_computed_of_chain s (a' :: ys) n2 r2 (eq_sym Heqp2))
          as Hp2.
        rewrite Hp2 in Hrec.
        lia.
      }
      assert (H3 : levenshtein_computed s ys <= S (S n3)).
      {
        pose proof
          (levenshtein_computed_of_chain s ys n3 r3 (eq_sym Heqp3))
          as Hp3.
        rewrite Hp3.
        lia.
      }
      pose proof
        (levenshtein_computed_of_chain s ys n3 r3 (eq_sym Heqp3))
        as Hs.
      try rewrite <- Hs.
      try match goal with
      | |- context [let (_, _) := ?p in _] =>
          change p with (levenshtein_chain (a :: s) ys)
      end.
      try rewrite <- Heqp1.
      cbn.
      try match goal with
      | |- context [let (_, _) := ?p in _] =>
          change p with (levenshtein_chain s (a' :: ys))
      end.
      try rewrite <- Heqp2.
      cbn.
      try match goal with
      | |- context [let (_, _) := ?p in _] =>
          change p with (levenshtein_chain s ys)
      end.
      try rewrite <- Heqp3.
      cbn.
      eapply (min3_app_cases
        (existT (fun n : nat => chain (a :: s) (a' :: ys) n) (S n1)
                (insert_chain a' (a :: s) ys n1 r1))
        (existT (fun n : nat => chain (a :: s) (a' :: ys) n) (S n2)
                (delete_chain a s (a' :: ys) n2 r2))
        (existT (fun n : nat => chain (a :: s) (a' :: ys) n) (S n3)
                (update_chain a a' s ys n3 Hna r3))
        (fun p => projT1 p)
        (fun p => n3 <= S (projT1 p))).
      * rewrite Hs in H1. exact H1.
      * rewrite Hs in H2. exact H2.
      * rewrite Hs in H3. exact H3.
    + unfold levenshtein_computed.
      cbn.
      destruct (ascii_dec a' b) as [Hcontra|Hna'b].
      { exfalso. apply Ha'b. exact Hcontra. }
      remember (levenshtein_chain (a' :: s) ys) as q1.
      remember (levenshtein_chain s (b :: ys)) as q2.
      remember (levenshtein_chain s ys) as q3.
      destruct q1 as [l1 c1], q2 as [l2 c2], q3 as [l3 c3].
      cbn.
      pose proof (min3_app_pf
        (existT (fun n : nat => chain (a' :: s) (b :: ys) n) (S l1)
                (insert_chain b (a' :: s) ys l1 c1))
        (existT (fun n : nat => chain (a' :: s) (b :: ys) n) (S l2)
                (delete_chain a' s (b :: ys) l2 c2))
        (existT (fun n : nat => chain (a' :: s) (b :: ys) n) (S l3)
                (update_chain a' b s ys l3 Hna'b c3))
        (fun p => projT1 p)) as [HL1 [HL2 HL3]].
      destruct (ascii_dec a b) as [Hab|Hab].
      * subst b.
        try match goal with
        | |- context [let (_, _) := ?p in _] =>
            change p with (levenshtein_chain (a' :: s) ys)
        end.
        try rewrite <- Heqq1.
        cbn.
        try match goal with
        | |- context [let (_, _) := ?p in _] =>
            change p with (levenshtein_chain s (a :: ys))
        end.
        try rewrite <- Heqq2.
        cbn.
        try match goal with
        | |- context [let (_, _) := ?p in _] =>
            change p with (levenshtein_chain s ys)
        end.
        try rewrite <- Heqq3.
        cbn.
        exact HL3.
      * unfold levenshtein_computed.
        cbn.
        destruct (ascii_dec a b) as [Hcontra2|Hnab].
        { exfalso. apply Hab. exact Hcontra2. }
        remember (levenshtein_chain (a :: s) ys) as p1.
        remember (levenshtein_chain s (b :: ys)) as p2.
        remember (levenshtein_chain s ys) as p3.
        destruct p1 as [n1 r1], p2 as [n2 r2], p3 as [n3 r3].
        cbn.
        assert (H1 :
          projT1 (min3_app
            (existT (fun n : nat => chain (a' :: s) (b :: ys) n) (S l1)
                    (insert_chain b (a' :: s) ys l1 c1))
            (existT (fun n : nat => chain (a' :: s) (b :: ys) n) (S l2)
                    (delete_chain a' s (b :: ys) l2 c2))
            (existT (fun n : nat => chain (a' :: s) (b :: ys) n) (S l3)
                    (update_chain a' b s ys l3 Hna'b c3))
            (fun p => projT1 p)) <= S (S n1)).
        {
          assert (Hl1n1 : l1 <= S n1).
          {
            assert (Hrec :
              levenshtein_computed (a' :: s) ys <=
              S (levenshtein_computed (a :: s) ys)).
            {
              apply (IH (length s + length ys)).
              - simpl in Hm. lia.
              - exact Hneq.
              - reflexivity.
            }
            pose proof
              (levenshtein_computed_of_chain (a' :: s) ys l1 c1 (eq_sym Heqq1))
              as Hq1.
            pose proof
              (levenshtein_computed_of_chain (a :: s) ys n1 r1 (eq_sym Heqp1))
              as Hp1.
            rewrite Hq1 in Hrec.
            rewrite Hp1 in Hrec.
            exact Hrec.
          }
          eapply PeanoNat.Nat.le_trans.
          - exact HL1.
          - cbn. lia.
        }
        assert (H2 :
          projT1 (min3_app
            (existT (fun n : nat => chain (a' :: s) (b :: ys) n) (S l1)
                    (insert_chain b (a' :: s) ys l1 c1))
            (existT (fun n : nat => chain (a' :: s) (b :: ys) n) (S l2)
                    (delete_chain a' s (b :: ys) l2 c2))
            (existT (fun n : nat => chain (a' :: s) (b :: ys) n) (S l3)
                    (update_chain a' b s ys l3 Hna'b c3))
            (fun p => projT1 p)) <= S (S n2)).
        {
          assert (Hl2n2 : l2 = n2).
          {
            inversion Heqq2.
            reflexivity.
          }
          eapply PeanoNat.Nat.le_trans.
          - exact HL2.
          - cbn. lia.
        }
        assert (H3 :
          projT1 (min3_app
            (existT (fun n : nat => chain (a' :: s) (b :: ys) n) (S l1)
                    (insert_chain b (a' :: s) ys l1 c1))
            (existT (fun n : nat => chain (a' :: s) (b :: ys) n) (S l2)
                    (delete_chain a' s (b :: ys) l2 c2))
            (existT (fun n : nat => chain (a' :: s) (b :: ys) n) (S l3)
                    (update_chain a' b s ys l3 Hna'b c3))
            (fun p => projT1 p)) <= S (S n3)).
        {
          assert (Hl3n3 : l3 = n3).
          {
            inversion Heqq3.
            reflexivity.
          }
          eapply PeanoNat.Nat.le_trans.
          - exact HL3.
          - cbn. lia.
        }
        assert (Heq2' :
          existT (fun n : nat => chain s (b :: ys) n) l2 c2 =
          levenshtein_chain s (b :: ys)).
        {
          rewrite Heqq2.
          exact Heqp2.
        }
        assert (Heq3' :
          existT (fun n : nat => chain s ys n) l3 c3 =
          levenshtein_chain s ys).
        {
          rewrite Heqq3.
          exact Heqp3.
        }
        try match goal with
        | |- context [let (_, _) := ?p in _] =>
            change p with (levenshtein_chain (a' :: s) ys)
        end.
        try rewrite <- Heqq1.
        cbn.
        try match goal with
        | |- context [let (_, _) := ?p in _] =>
            change p with (levenshtein_chain s (b :: ys))
        end.
        try rewrite <- Heq2'.
        cbn.
        try match goal with
        | |- context [let (_, _) := ?p in _] =>
            change p with (levenshtein_chain s ys)
        end.
        try rewrite <- Heq3'.
        cbn.
        try match goal with
        | |- context [let (_, _) := ?p in _] =>
            change p with (levenshtein_chain (a :: s) ys)
        end.
        try rewrite <- Heqp1.
        cbn.
        try match goal with
        | |- context [let (_, _) := ?p in _] =>
            change p with (levenshtein_chain s (b :: ys))
        end.
        try rewrite <- Heqp2.
        cbn.
        try match goal with
        | |- context [let (_, _) := ?p in _] =>
            change p with (levenshtein_chain s ys)
        end.
        try rewrite <- Heqp3.
        cbn.
        eapply (min3_app_cases
          (existT (fun n : nat => chain (a :: s) (b :: ys) n) (S n1)
                  (insert_chain b (a :: s) ys n1 r1))
          (existT (fun n : nat => chain (a :: s) (b :: ys) n) (S l2)
                  (delete_chain a s (b :: ys) l2 c2))
          (existT (fun n : nat => chain (a :: s) (b :: ys) n) (S l3)
                  (update_chain a b s ys l3 Hab c3))
          (fun p => projT1 p)
          (fun p =>
             projT1 (min3_app
                (existT (fun n : nat => chain (a' :: s) (b :: ys) n) (S l1)
                       (insert_chain b (a' :: s) ys l1 c1))
               (existT (fun n : nat => chain (a' :: s) (b :: ys) n) (S l2)
                       (delete_chain a' s (b :: ys) l2 c2))
               (existT (fun n : nat => chain (a' :: s) (b :: ys) n) (S l3)
                        (update_chain a' b s ys l3 Hna'b c3))
                (fun p0 => projT1 p0))
              <= S (projT1 p))).
        -- exact H1.
        -- assert (Hn2l2 : n2 = l2).
           { inversion Heqq2. reflexivity. }
           rewrite Hn2l2 in H2.
           exact H2.
        -- assert (Hn3l3 : n3 = l3).
           { inversion Heqq3. reflexivity. }
           rewrite Hn3l3 in H3.
           exact H3.
Qed.

Theorem levenshtein_computed_is_minimal :
  forall s t n (c : chain s t n),
    levenshtein_computed s t <= n.
Proof.
  intros s t n c.
  induction c.
  - reflexivity.
  - rewrite levenshtein_computed_skip_eq.
    exact IHc.
  - destruct e.
    + eapply PeanoNat.Nat.le_trans.
      * apply (levenshtein_computed_insert_lower a s u).
      * apply (proj1 (PeanoNat.Nat.succ_le_mono _ _)).
        exact IHc.
    + eapply PeanoNat.Nat.le_trans.
      * apply (levenshtein_computed_delete_upper a s u).
      * apply (proj1 (PeanoNat.Nat.succ_le_mono _ _)).
        exact IHc.
    + eapply PeanoNat.Nat.le_trans.
      * apply (levenshtein_computed_update_upper a a' s u).
        exact neq.
      * apply (proj1 (PeanoNat.Nat.succ_le_mono _ _)).
        exact IHc.
Qed.

Theorem levenshtein_eq_computed : forall s t, levenshtein s t = projT1 (levenshtein_chain s t).
Proof.
  intros s t.
  reflexivity.
Qed.

Theorem levenshtein_is_minimal (s t : string) :
  forall (n : nat) (c : chain s t n), levenshtein s t <= n.
Proof.
  intros n c.
  unfold levenshtein.
  apply (levenshtein_computed_is_minimal s t n c).
Qed.

(* Eval compute in (levenshtein_chain "pascal" "haskell"). *)

End Levenshtein.

(* ================================================================ *)
(*        DP BRIDGE: loop-structured DP = intrinsic model           *)
(* ================================================================ *)
(* The following section defines a Wagner-Fischer-style DP model     *)
(* operating on list ascii / nat, then proves it computes the same   *)
(* value as the intrinsic levenshtein_computed above.  The key       *)
(* difficulty is that the DP scans left-to-right while the intrinsic *)
(* model works right-to-left; a reversal argument closes the gap.    *)

From Stdlib Require Import List.
Import Levenshtein.
Import ListNotations.

Open Scope nat_scope.
Local Open Scope list_scope.

Definition dp_min (result distance bDistance : nat) : nat :=
  if Nat.ltb result distance then
    if Nat.ltb result bDistance then S result else bDistance
  else
    if Nat.ltb distance bDistance then S distance else bDistance.

Fixpoint inner_loop (a_chars : list ascii) (b_char : ascii) (old_cache : list nat)
    (distance result : nat) : list nat * nat * nat :=
  match a_chars, old_cache with
  | a_i :: a_rest, c_i :: c_rest =>
      let bDistance := if ascii_dec b_char a_i then distance else S distance in
      let new_result := dp_min result c_i bDistance in
      let '(rest_cache, fd, fr) :=
          inner_loop a_rest b_char c_rest c_i new_result in
      (new_result :: rest_cache, fd, fr)
  | _, _ => ([], distance, result)
  end.

Definition process_row (a_chars : list ascii) (b_char : ascii)
    (old_cache : list nat) (bIndex : nat) : list nat * nat :=
  let '(new_cache, _, final_result) :=
      inner_loop a_chars b_char old_cache bIndex bIndex in
  (new_cache, final_result).

Fixpoint outer_cache (a_chars b_chars : list ascii) (init : list nat)
    (k : nat) : list nat :=
  match k with
  | O => init
  | S k' =>
      let prev := outer_cache a_chars b_chars init k' in
      let b_j := nth k' b_chars Ascii.zero in
      fst (process_row a_chars b_j prev k')
  end.

Definition outer_result (a_chars b_chars : list ascii) (init : list nat)
    (k : nat) : nat :=
  match k with
  | O => 0
  | S k' =>
      let prev := outer_cache a_chars b_chars init k' in
      let b_j := nth k' b_chars Ascii.zero in
      snd (process_row a_chars b_j prev k')
  end.

Fixpoint outer_result_run (a_chars b_chars : list ascii)
    (cache : list nat) (bIndex : nat) : nat :=
  match b_chars with
  | [] => 0
  | ch :: bs =>
      let '(cache', row_res) := process_row a_chars ch cache bIndex in
      match bs with
      | [] => row_res
      | _ :: _ => outer_result_run a_chars bs cache' (S bIndex)
      end
  end.

Definition init_cache (la : nat) : list nat :=
  map S (seq 0 la).

Definition lev_dp_list (a_chars b_chars : list ascii) : nat :=
  let la := length a_chars in
  let lb := length b_chars in
  if la =? 0 then lb
  else if lb =? 0 then la
  else outer_result_run a_chars b_chars (init_cache la) 0.

Definition lev_dp_string (s t : string) : nat :=
  lev_dp_list (list_ascii_of_string s) (list_ascii_of_string t).

Lemma list_ascii_of_string_length :
  forall s, length (list_ascii_of_string s) = String.length s.
Proof.
  intros s.
  induction s as [|a s' IH]; cbn; [reflexivity |].
  now rewrite IH.
Qed.

(* levenshtein_computed_nil_l, levenshtein_computed_nil_r, and
   levenshtein_computed_cons_neq are already proved inside the Module. *)

Definition lev_spec_list (a b : list ascii) : nat :=
  levenshtein_computed (string_of_list_ascii a) (string_of_list_ascii b).

Lemma string_of_list_ascii_length :
  forall l, String.length (string_of_list_ascii l) = length l.
Proof.
  intros l.
  induction l as [|a l IH]; cbn; [reflexivity|].
  now rewrite IH.
Qed.

Lemma lev_spec_list_nil_l :
  forall b, lev_spec_list [] b = length b.
Proof.
  intros b.
  unfold lev_spec_list.
  rewrite levenshtein_computed_nil_l.
  rewrite string_of_list_ascii_length.
  reflexivity.
Qed.

Lemma lev_spec_list_nil_r :
  forall a, lev_spec_list a [] = length a.
Proof.
  intros a.
  unfold lev_spec_list.
  rewrite levenshtein_computed_nil_r.
  rewrite string_of_list_ascii_length.
  reflexivity.
Qed.

Lemma lev_spec_list_cons_eq :
  forall x xs ys,
    lev_spec_list (x :: xs) (x :: ys) = lev_spec_list xs ys.
Proof.
  intros x xs ys.
  unfold lev_spec_list.
  cbn.
  apply levenshtein_computed_skip_eq.
Qed.

Lemma lev_spec_list_cons_neq :
  forall x xs y ys,
    x <> y ->
    lev_spec_list (x :: xs) (y :: ys) =
      Nat.min (S (lev_spec_list (x :: xs) ys))
              (Nat.min (S (lev_spec_list xs (y :: ys)))
                       (S (lev_spec_list xs ys))).
Proof.
  intros x xs y ys Hxy.
  unfold lev_spec_list.
  cbn.
  apply levenshtein_computed_cons_neq.
  exact Hxy.
Qed.

Lemma dp_min_spec : forall r d bd,
  dp_min r d bd = Nat.min (S r) (Nat.min (S d) bd).
Proof.
  intros r d bd.
  unfold dp_min.
  destruct (Nat.ltb r d) eqn:Hrd.
  - destruct (Nat.ltb r bd) eqn:Hrb.
    + apply PeanoNat.Nat.ltb_lt in Hrd.
      apply PeanoNat.Nat.ltb_lt in Hrb.
      rewrite (PeanoNat.Nat.min_l (S r) (Nat.min (S d) bd)).
      2:{
        apply PeanoNat.Nat.min_glb.
        lia.
        apply PeanoNat.Nat.le_trans with (m := S r); lia.
      }
      reflexivity.
    + apply PeanoNat.Nat.ltb_lt in Hrd.
      apply PeanoNat.Nat.ltb_ge in Hrb.
      rewrite (PeanoNat.Nat.min_r (S d) bd) by lia.
      rewrite (PeanoNat.Nat.min_r (S r) bd) by lia.
      reflexivity.
  - destruct (Nat.ltb d bd) eqn:Hdb.
    + apply PeanoNat.Nat.ltb_ge in Hrd.
      apply PeanoNat.Nat.ltb_lt in Hdb.
      rewrite (PeanoNat.Nat.min_l (S d) bd) by lia.
      rewrite (PeanoNat.Nat.min_r (S r) (S d)) by lia.
      reflexivity.
    + apply PeanoNat.Nat.ltb_ge in Hrd.
      apply PeanoNat.Nat.ltb_ge in Hdb.
      rewrite (PeanoNat.Nat.min_r (S d) bd) by lia.
      rewrite (PeanoNat.Nat.min_r (S r) bd) by lia.
      reflexivity.
Qed.

Lemma lev_dp_list_nil_l : forall b,
  lev_dp_list [] b = length b.
Proof.
  intros b.
  unfold lev_dp_list.
  simpl.
  reflexivity.
Qed.

Lemma lev_dp_list_nil_r : forall a,
  lev_dp_list a [] = length a.
Proof.
  intros a.
  unfold lev_dp_list.
  destruct a; simpl; reflexivity.
Qed.

Lemma lev_dp_string_nil_l_eq :
  forall t, lev_dp_string EmptyString t = levenshtein_computed EmptyString t.
Proof.
  intros t.
  unfold lev_dp_string.
  rewrite lev_dp_list_nil_l.
  rewrite list_ascii_of_string_length.
  rewrite levenshtein_computed_nil_l.
  reflexivity.
Qed.

Lemma lev_dp_string_nil_r_eq :
  forall s, lev_dp_string s EmptyString = levenshtein_computed s EmptyString.
Proof.
  intros s.
  unfold lev_dp_string.
  rewrite lev_dp_list_nil_r.
  rewrite list_ascii_of_string_length.
  rewrite levenshtein_computed_nil_r.
  reflexivity.
Qed.

(* Row specification where [pre_rev] is the reverse of the already-processed
   prefix of [a], and [brow] is the reverse of the current [b]-prefix. *)
Fixpoint row_values (pre_rev a_rest brow : list ascii) : list nat :=
  match a_rest with
  | [] => []
  | a_i :: a_tail =>
      lev_spec_list (a_i :: pre_rev) brow
      :: row_values (a_i :: pre_rev) a_tail brow
  end.

Fixpoint row_last (pre_rev a_rest brow : list ascii) : nat :=
  match a_rest with
  | [] => lev_spec_list pre_rev brow
  | a_i :: a_tail => row_last (a_i :: pre_rev) a_tail brow
  end.

Lemma row_values_nil :
  forall pre_rev a_rest,
    row_values pre_rev a_rest [] =
    map S (seq (length pre_rev) (length a_rest)).
Proof.
  intros pre_rev a_rest.
  revert pre_rev.
  induction a_rest as [|a_i a_tail IH]; intros pre_rev; cbn [row_values].
  - reflexivity.
  - rewrite lev_spec_list_nil_r.
    rewrite IH.
    reflexivity.
Qed.

Lemma init_cache_row_values :
  forall a_rest, init_cache (length a_rest) = row_values [] a_rest [].
Proof.
  intros a_rest.
  unfold init_cache.
  rewrite row_values_nil.
  reflexivity.
Qed.

Lemma lev_spec_list_insert_lower_l :
  forall a s t,
    lev_spec_list s t <= S (lev_spec_list (a :: s) t).
Proof.
  intros a s t.
  unfold lev_spec_list.
  apply levenshtein_computed_insert_lower.
Qed.

Lemma lev_spec_list_insert_lower_r :
  forall a s t,
    lev_spec_list s t <= S (lev_spec_list s (a :: t)).
Proof.
  intros a s t.
  unfold lev_spec_list.
  apply levenshtein_computed_insert_lower_r.
Qed.

Lemma dp_cell_eq_cont :
  forall x pre_rev bpre_rev,
    dp_min (lev_spec_list pre_rev (x :: bpre_rev))
           (lev_spec_list (x :: pre_rev) bpre_rev)
           (lev_spec_list pre_rev bpre_rev)
    = lev_spec_list (x :: pre_rev) (x :: bpre_rev).
Proof.
  intros x pre_rev bpre_rev.
  rewrite dp_min_spec.
  rewrite lev_spec_list_cons_eq.
  rewrite (PeanoNat.Nat.min_r
             (S (lev_spec_list (x :: pre_rev) bpre_rev))
             (lev_spec_list pre_rev bpre_rev)).
  2:{ apply lev_spec_list_insert_lower_l. }
  rewrite (PeanoNat.Nat.min_r
             (S (lev_spec_list pre_rev (x :: bpre_rev)))
             (lev_spec_list pre_rev bpre_rev)).
  2:{ apply lev_spec_list_insert_lower_r. }
  reflexivity.
Qed.

Lemma dp_cell_neq_cont :
  forall x y pre_rev bpre_rev,
    x <> y ->
    dp_min (lev_spec_list pre_rev (y :: bpre_rev))
           (lev_spec_list (x :: pre_rev) bpre_rev)
           (S (lev_spec_list pre_rev bpre_rev))
    = lev_spec_list (x :: pre_rev) (y :: bpre_rev).
Proof.
  intros x y pre_rev bpre_rev Hxy.
  rewrite dp_min_spec.
  rewrite lev_spec_list_cons_neq by exact Hxy.
  rewrite min3_comm12.
  reflexivity.
Qed.

Lemma dp_cell_first_eq :
  forall x bpre_rev,
    dp_min (lev_spec_list [] bpre_rev)
           (lev_spec_list [x] bpre_rev)
           (lev_spec_list [] bpre_rev)
    = lev_spec_list [x] (x :: bpre_rev).
Proof.
  intros x bpre_rev.
  rewrite dp_min_spec.
  rewrite lev_spec_list_cons_eq.
  rewrite PeanoNat.Nat.min_r by lia.
  rewrite PeanoNat.Nat.min_r.
  2:{
    specialize (lev_spec_list_insert_lower_l x [] bpre_rev) as H.
    simpl in H.
    exact H.
  }
  reflexivity.
Qed.

Lemma dp_cell_first_neq :
  forall x y bpre_rev,
    x <> y ->
    dp_min (lev_spec_list [] bpre_rev)
           (lev_spec_list [x] bpre_rev)
           (S (lev_spec_list [] bpre_rev))
    = lev_spec_list [x] (y :: bpre_rev).
Proof.
  intros x y bpre_rev Hxy.
  set (d := lev_spec_list [] bpre_rev).
  set (c := lev_spec_list [x] bpre_rev).
  rewrite dp_min_spec.
  rewrite lev_spec_list_cons_neq by exact Hxy.
  assert (Hd : lev_spec_list [] (y :: bpre_rev) = S d).
  {
    unfold d.
    rewrite !lev_spec_list_nil_l.
    simpl.
    lia.
  }
  rewrite Hd.
  fold c d.
  rewrite min3_comm12.
  rewrite PeanoNat.Nat.min_id.
  replace (Nat.min (S (S d)) (S d)) with (S d).
  2:{ symmetry. apply PeanoNat.Nat.min_r. lia. }
  reflexivity.
Qed.

Lemma inner_loop_cont_correct :
  forall pre_rev a_rest b_char bpre_rev,
    inner_loop a_rest b_char (row_values pre_rev a_rest bpre_rev)
      (lev_spec_list pre_rev bpre_rev)
      (lev_spec_list pre_rev (b_char :: bpre_rev))
    =
    (row_values pre_rev a_rest (b_char :: bpre_rev),
     row_last pre_rev a_rest bpre_rev,
     row_last pre_rev a_rest (b_char :: bpre_rev)).
Proof.
  intros pre_rev a_rest.
  revert pre_rev.
  induction a_rest as [|a_i a_tail IH]; intros pre_rev b_char bpre_rev; cbn.
  - reflexivity.
  - destruct (ascii_dec b_char a_i) as [Heq|Hneq].
    + subst a_i.
      rewrite dp_cell_eq_cont.
      rewrite (IH (b_char :: pre_rev) b_char bpre_rev).
      reflexivity.
    + rewrite dp_cell_neq_cont.
      2:{ intro Hc. apply Hneq. symmetry. exact Hc. }
      rewrite (IH (a_i :: pre_rev) b_char bpre_rev).
      reflexivity.
Qed.

Lemma process_row_correct_nonempty :
  forall a0 a_tail b_char bpre_rev,
    process_row (a0 :: a_tail) b_char
      (row_values [] (a0 :: a_tail) bpre_rev)
      (length bpre_rev)
    =
    (row_values [] (a0 :: a_tail) (b_char :: bpre_rev),
     row_last [] (a0 :: a_tail) (b_char :: bpre_rev)).
Proof.
  intros a0 a_tail b_char bpre_rev.
  unfold process_row.
  cbn [row_values].
  replace (length bpre_rev) with (lev_spec_list [] bpre_rev).
  2:{ exact (lev_spec_list_nil_l bpre_rev). }
  destruct (ascii_dec b_char a0) as [Heq|Hneq].
  - subst a0.
    cbn.
    destruct (ascii_dec b_char b_char) as [Hbb|Hbb].
    2:{ exfalso. apply Hbb. reflexivity. }
    rewrite dp_cell_first_eq.
    rewrite inner_loop_cont_correct with
      (pre_rev := [b_char]) (a_rest := a_tail)
      (b_char := b_char) (bpre_rev := bpre_rev).
    reflexivity.
  - remember (if ascii_dec b_char a0
              then lev_spec_list [] bpre_rev
              else S (lev_spec_list [] bpre_rev)) as bd0 eqn:Hbd0.
    assert (Hbd0' : bd0 = S (lev_spec_list [] bpre_rev)).
    {
      rewrite Hbd0.
      destruct (ascii_dec b_char a0) as [Hc|Hc].
      - exfalso. apply Hneq. exact Hc.
      - reflexivity.
    }
    rewrite Hbd0' in *.
    cbn [inner_loop].
    destruct (ascii_dec b_char a0) as [Hc|Hc].
    + exfalso. apply Hneq. exact Hc.
    + cbn.
    rewrite (dp_cell_first_neq a0 b_char bpre_rev).
    2:{ intro Heq'. apply Hneq. symmetry. exact Heq'. }
    rewrite inner_loop_cont_correct with
      (pre_rev := [a0]) (a_rest := a_tail)
      (b_char := b_char) (bpre_rev := bpre_rev).
    reflexivity.
Qed.

Lemma row_last_rev :
  forall pre_rev a_rest brow,
    row_last pre_rev a_rest brow =
    lev_spec_list (rev a_rest ++ pre_rev) brow.
Proof.
  intros pre_rev a_rest brow.
  revert pre_rev.
  induction a_rest as [|a_i a_tail IH]; intros pre_rev; cbn.
  - reflexivity.
  - rewrite (IH (a_i :: pre_rev)).
    cbn [rev].
    change (a_i :: pre_rev) with ([a_i] ++ pre_rev).
    rewrite <- app_assoc.
    reflexivity.
Qed.

Lemma outer_result_run_correct :
  forall a b bpre_rev,
    a <> [] ->
    b <> [] ->
    outer_result_run a b (row_values [] a bpre_rev) (length bpre_rev)
    = row_last [] a (rev b ++ bpre_rev).
Proof.
  intros a b bpre_rev Ha Hb.
  revert bpre_rev Hb.
  induction b as [|b0 b_tail IH]; intros bpre_rev Hb; [contradiction|].
  destruct a as [|a0 a_tail]; [contradiction|].
  cbn [outer_result_run].
  rewrite process_row_correct_nonempty.
  destruct b_tail as [|b1 b_tail'].
  - cbn.
    reflexivity.
  -
    specialize (IH (b0 :: bpre_rev) ltac:(discriminate)).
    replace (S (length bpre_rev)) with (length (b0 :: bpre_rev)) by reflexivity.
    rewrite IH.
    cbn [rev].
    change (b0 :: bpre_rev) with ([b0] ++ bpre_rev).
    repeat rewrite <- app_assoc.
    reflexivity.
Qed.

Theorem lev_dp_list_rev_spec :
  forall a b,
    lev_dp_list a b = lev_spec_list (rev a) (rev b).
Proof.
  intros a b.
  destruct a as [|a0 a_tail].
  - rewrite lev_dp_list_nil_l.
    rewrite lev_spec_list_nil_l.
    rewrite length_rev.
    reflexivity.
  - destruct b as [|b0 b_tail].
    + rewrite lev_dp_list_nil_r.
      rewrite lev_spec_list_nil_r.
      rewrite length_rev.
      reflexivity.
    + unfold lev_dp_list.
      cbn [length Nat.eqb].
      change (init_cache (S (length a_tail)))
        with (init_cache (length (a0 :: a_tail))).
      rewrite init_cache_row_values.
      rewrite outer_result_run_correct by discriminate.
      rewrite row_last_rev with (pre_rev := []).
      cbn.
      repeat rewrite app_nil_r.
      reflexivity.
Qed.

Lemma lev_dp_string_rev_spec :
  forall s t,
    lev_dp_string s t =
    lev_spec_list (rev (list_ascii_of_string s))
                  (rev (list_ascii_of_string t)).
Proof.
  intros s t.
  unfold lev_dp_string.
  apply lev_dp_list_rev_spec.
Qed.

Lemma chain_append_right :
  forall s t n (c : chain s t n) u,
    chain (s ++ u) (t ++ u) n.
Proof.
  intros s t n c.
  induction c as [|a s1 t1 n1 c1 IH|s1 t1 u1 n1 e c1 IH]; intros u.
  - exact (same_chain u).
  - cbn [String.append].
    apply skip.
    exact (IH u).
  - destruct e.
    + cbn [String.append].
      eapply change.
      * exact (insertion a).
      * exact (IH u).
    + cbn [String.append].
      eapply change.
      * exact (deletion a).
      * exact (IH u).
    + cbn [String.append].
      eapply change.
      * exact (update a' a (neq := neq)).
      * exact (IH u).
Qed.

Lemma chain_add_last_source :
  forall s t n (c : chain s t n) a,
    chain (s ++ String a EmptyString) t (S n).
Proof.
  intros s t n c.
  induction c as [|x s1 t1 n1 c1 IH|s1 t1 u1 n1 e c1 IH]; intros a.
  - cbn [String.append].
    exact (delete_chain a EmptyString EmptyString 0 empty).
  - cbn [String.append].
    apply skip.
    exact (IH a).
  - destruct e.
    + cbn [String.append].
      eapply change.
      * exact (insertion a0).
      * exact (IH a).
    + cbn [String.append].
      eapply change.
      * exact (deletion a0).
      * exact (IH a).
    + cbn [String.append].
      eapply change.
      * exact (update a' a0 (neq := neq)).
      * exact (IH a).
Qed.

Lemma chain_strip_last_source :
  forall s a t n,
    chain (s ++ String a EmptyString) t n ->
    chain s t (S n).
Proof.
  intros s a t n c.
  remember (String.append s (String a EmptyString)) as src eqn:Hsrc.
  revert s a Hsrc.
  induction c as [|x s1 t1 n1 c1 IH|s1 t1 u1 n1 e c1 IH];
    intros s0 a0 Hsrc.
  - destruct s0; cbn in Hsrc; discriminate.
  - destruct s0 as [|y s0']; cbn in Hsrc.
    + inversion Hsrc; subst.
      eapply change.
      * constructor.
      * apply skip.
        exact c1.
    + inversion Hsrc; subst.
      apply skip.
      apply IH with (a := a0).
      reflexivity.
  - destruct e as [ch s2|ch s2|ch' ch Hneq s2].
    + eapply change.
      * constructor.
      * apply IH with (s := String ch s0) (a := a0).
        cbn [String.append].
        now rewrite Hsrc.
    + destruct s0 as [|y s0']; cbn in Hsrc.
      * inversion Hsrc; subst.
        eapply change.
        -- exact (insertion a0).
        -- eapply change.
           ++ exact (deletion a0).
           ++ exact c1.
      * inversion Hsrc; subst.
        eapply change.
        -- exact (deletion y).
        -- apply IH with (s := s0') (a := a0).
           reflexivity.
    + destruct s0 as [|y s0']; cbn in Hsrc.
      * inversion Hsrc; subst.
        eapply change.
        -- exact (insertion a0).
        -- eapply change.
           ++ exact (update a0 ch (neq := Hneq)).
           ++ exact c1.
      * inversion Hsrc; subst.
        eapply change.
        -- exact (update y ch (neq := Hneq)).
        -- apply IH with (s := String ch s0') (a := a0).
           cbn [String.append].
           reflexivity.
Qed.

Lemma chain_update_last_source :
  forall s a a' t n,
    a' <> a ->
    chain (s ++ String a EmptyString) t n ->
    chain (s ++ String a' EmptyString) t (S n).
Proof.
  intros s a a' t n Hneq_sa c.
  remember (String.append s (String a EmptyString)) as src eqn:Hsrc.
  revert s a Hneq_sa Hsrc.
  induction c as [|x s1 t1 n1 c1 IH|s1 t1 u1 n1 e c1 IH];
    intros s0 a0 Hneq0 Hsrc.
  - destruct s0; cbn in Hsrc; discriminate.
  - destruct s0 as [|y s0']; cbn in Hsrc.
    + inversion Hsrc; subst.
      eapply change.
      * exact (update a' a0 (neq := Hneq0)).
      * apply skip.
        exact c1.
    + inversion Hsrc; subst.
      apply skip.
      apply IH with (a := a0).
      * exact Hneq0.
      * reflexivity.
  - destruct e as [ch s2|ch s2|ch' ch Hneq_e s2].
    + eapply change.
      * exact (insertion ch).
      * apply IH with (s := String ch s0) (a := a0).
        -- exact Hneq0.
        -- cbn [String.append].
           now rewrite Hsrc.
    + destruct s0 as [|y s0']; cbn in Hsrc.
      * inversion Hsrc; subst.
        eapply change.
        -- exact (update a' a0 (neq := Hneq0)).
        -- eapply change.
           ++ exact (deletion a0).
           ++ exact c1.
      * inversion Hsrc; subst.
        eapply change.
        -- exact (deletion y).
        -- apply IH with (s := s0') (a := a0).
           ++ exact Hneq0.
           ++ reflexivity.
    + destruct s0 as [|y s0']; cbn in Hsrc.
      * inversion Hsrc; subst.
        eapply change.
        -- exact (update a' a0 (neq := Hneq0)).
        -- eapply change.
           ++ exact (update a0 ch (neq := Hneq_e)).
           ++ exact c1.
      * inversion Hsrc; subst.
        eapply change.
        -- exact (update y ch (neq := Hneq_e)).
        -- apply IH with (s := String ch s0') (a := a0).
           ++ exact Hneq0.
           ++ cbn [String.append].
              reflexivity.
Qed.

Lemma string_of_list_ascii_app :
  forall l1 l2,
    string_of_list_ascii (l1 ++ l2) =
    String.append (string_of_list_ascii l1) (string_of_list_ascii l2).
Proof.
  intros l1 l2.
  induction l1 as [|x xs IH]; cbn.
  - reflexivity.
  - rewrite IH.
    reflexivity.
Qed.

Definition rev_string (s : string) : string :=
  string_of_list_ascii (rev (list_ascii_of_string s)).

Lemma rev_string_cons :
  forall a s,
    rev_string (String a s) =
    String.append (rev_string s) (String a EmptyString).
Proof.
  intros a s.
  unfold rev_string.
  cbn [list_ascii_of_string rev].
  rewrite string_of_list_ascii_app.
  cbn [string_of_list_ascii String.append].
  reflexivity.
Qed.

Lemma rev_string_of_list :
  forall l,
    rev_string (string_of_list_ascii l) = string_of_list_ascii (rev l).
Proof.
  intros l.
  unfold rev_string.
  rewrite list_ascii_of_string_of_list_ascii.
  reflexivity.
Qed.

Lemma rev_string_involutive :
  forall s, rev_string (rev_string s) = s.
Proof.
  intros s.
  unfold rev_string.
  rewrite list_ascii_of_string_of_list_ascii.
  rewrite rev_involutive.
  rewrite string_of_list_ascii_of_string.
  reflexivity.
Qed.

Lemma chain_rev_string :
  forall s t n (c : chain s t n),
    chain (rev_string s) (rev_string t) n.
Proof.
  intros s t n c.
  induction c as [|a s1 t1 n1 c1 IH|s1 t1 u1 n1 e c1 IH].
  - unfold rev_string.
    cbn [list_ascii_of_string rev string_of_list_ascii].
    constructor.
  - rewrite !rev_string_cons.
    exact (chain_append_right _ _ _ IH (String a EmptyString)).
  - destruct e as [ch s2|ch s2|ch' ch Hneq s2].
    + rewrite rev_string_cons in IH.
      exact (chain_strip_last_source (rev_string s2) ch (rev_string u1) n1 IH).
    + rewrite rev_string_cons.
      exact (chain_add_last_source (rev_string s2) (rev_string u1) n1 IH ch).
    + rewrite rev_string_cons.
      rewrite rev_string_cons in IH.
      exact (chain_update_last_source (rev_string s2) ch ch' (rev_string u1) n1 Hneq IH).
Qed.

Lemma levenshtein_computed_rev_string :
  forall s t,
    levenshtein_computed (rev_string s) (rev_string t) =
    levenshtein_computed s t.
Proof.
  intros s t.
  apply PeanoNat.Nat.le_antisymm.
  - destruct (levenshtein_chain s t) as [n c] eqn:Hchain.
    pose proof
      (levenshtein_computed_of_chain s t n c Hchain)
      as Hn.
    pose proof
      (chain_rev_string s t n c)
      as Hrev.
    pose proof
      (levenshtein_computed_is_minimal (rev_string s) (rev_string t) n Hrev)
      as Hmin.
    rewrite <- Hn in Hmin.
    exact Hmin.
  - destruct (levenshtein_chain (rev_string s) (rev_string t)) as [n c] eqn:Hchain.
    pose proof
      (levenshtein_computed_of_chain (rev_string s) (rev_string t) n c Hchain)
      as Hn.
    pose proof
      (chain_rev_string (rev_string s) (rev_string t) n c)
      as Hrev.
    pose proof
      (levenshtein_computed_is_minimal
         (rev_string (rev_string s)) (rev_string (rev_string t)) n Hrev)
      as Hmin.
    rewrite !rev_string_involutive in Hmin.
    rewrite Hn.
    exact Hmin.
Qed.

Lemma lev_spec_list_rev :
  forall a b,
    lev_spec_list (rev a) (rev b) = lev_spec_list a b.
Proof.
  intros a b.
  unfold lev_spec_list.
  rewrite <- (rev_string_of_list a).
  rewrite <- (rev_string_of_list b).
  apply levenshtein_computed_rev_string.
Qed.

Theorem lev_dp_string_eq_levenshtein_computed :
  forall s t, lev_dp_string s t = levenshtein_computed s t.
Proof.
  intros s t.
  rewrite lev_dp_string_rev_spec.
  rewrite lev_spec_list_rev.
  unfold lev_spec_list.
  rewrite !string_of_list_ascii_of_string.
  reflexivity.
Qed.

Require Crane.Extraction.
Crane Extraction "levenshtein" Levenshtein.
