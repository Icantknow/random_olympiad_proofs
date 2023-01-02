Require Import Coq.Reals.Reals.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Lists.List.
Import ListNotations.

(* List Properties *)

Lemma nth_last : forall (A: Type) (a: A) (l: list A) (default: A),
  nth (length l) (l ++ [a]) default = a.
Proof.
  intros A a l.
  remember (length l) as n.
  generalize dependent a. generalize dependent l.
  induction n; intros.
  - symmetry in Heqn. apply length_zero_iff_nil in Heqn.
    rewrite Heqn. reflexivity.
  - rewrite Heqn. replace (length l) with (length l + 0) by apply Nat.add_0_r.
    rewrite app_nth2_plus. reflexivity.
Qed.

Lemma final_of_list : forall (A: Type) (n: nat) (l: list A),
  1 <= n -> n = length l -> exists l' x, l = l' ++ [x].
Proof.
  induction n; intros.
  inversion H.
  destruct l.
  inversion H0.
  destruct l.
  - exists [], a. reflexivity.
  - destruct n. discriminate H0.
    specialize (IHn (a0 :: l)).
    assert (1 <= S n).
      { replace 1 with (1+0) by reflexivity.
        apply plus_le_compat_l. apply Nat.le_0_l. }
    apply IHn in H1.
    destruct H1, H1.
    exists (a :: x), x0.
    rewrite H1.
    simpl. reflexivity.
    inversion H0.
    reflexivity.
Qed.

Lemma map_nth_variant : forall {A B: Type} (n: nat) (l: list A) (f: A -> B) (d1: A) (d2: B),
  n < length l -> nth n (map f l) d2 = f (nth n l d1).
Proof.
  induction n; intros.
  - destruct l. inversion H.
    reflexivity.
  - destruct l. inversion H.
    simpl in H. apply lt_S_n in H.
    simpl.
    apply IHn. assumption.
Qed.

Lemma map_erases_seq : forall {A B: Type} (default: A) (l: list A) (f: A -> B),
  (map (fun i : nat => f (nth i l default)) (seq 0 (length l))) = map f l.
Proof.
  intros.
  remember (length l) as n.
  generalize dependent f.
  generalize dependent l.
  induction n; intros.
  - symmetry in Heqn. apply length_zero_iff_nil in Heqn.
    rewrite Heqn in *.
    reflexivity.
  - destruct l. inversion Heqn.
    simpl in Heqn. injection Heqn as Heqn.
    rewrite seq_S. rewrite map_last.
    assert (exists l' x, a :: l = l' ++ [x]).
      { apply (final_of_list _ (S n) _).
        replace 1%nat with (1+0)%nat by reflexivity.
        apply plus_le_compat_l, Nat.le_0_l.
        simpl. f_equal. assumption. }
    destruct H, H.
    assert (n = length x).
      { apply (@f_equal (list A) (nat) (fun arr => length arr) (a :: l) (x ++ [x0])) in H.
        rewrite app_length in H. simpl in H.
        rewrite plus_comm in H.
        injection H as H.
        rewrite <- H. assumption. }
    assert (map (fun i : nat => f (nth i x default)) (seq 0 n) = map f x).
      { apply IHn. assumption. }
    rewrite H. simpl.
    rewrite map_app. simpl.
    replace (map (fun i : nat => f (nth i (x ++ [x0]) default)) (seq 0 n)) with (map f x).
    replace (nth n (x ++ [x0]) default) with x0.
    reflexivity.
    + rewrite H0. symmetry. apply nth_last.
    + rewrite <- H1.
      apply (nth_ext _ _ (f (default)) (f (default))).
      rewrite map_length, map_length. reflexivity.
      intros. rewrite map_length, seq_length in H2.
      rewrite (map_nth_variant _ _ _ 0 _).
      rewrite (map_nth_variant _ _ _ 0 _).
      rewrite seq_nth; try assumption.
      f_equal. simpl.
      symmetry. apply app_nth1.
      rewrite <- H0. assumption.
      rewrite seq_length. assumption.
      rewrite seq_length. assumption.
Qed.

Local Open Scope R_scope.

(* Useful Lemmas on Real Numbers *)

Lemma neg_minus_equiv : forall (r : R), -1 * r = -r.
Proof.
  intros.
  apply (Rplus_eq_reg_l r).
  rewrite Rplus_opp_r.
  replace r with (1 * r) at 1 by apply Rmult_1_l.
  rewrite <- Rmult_plus_distr_r.
  rewrite Rplus_opp_r.
  rewrite Rmult_0_l.
  reflexivity.
Qed.

Lemma neg_inv_prod : forall (r : R), r <> 0 -> - / r * r = -1.
Proof.
  intros.
  replace (- / r) with (-1 * / r).
  rewrite Rmult_assoc.
  rewrite Rinv_l.
  Rcompute.
  assumption.
  apply neg_minus_equiv.
Qed.

Fixpoint nat_to_R (n: nat) : R :=
  match n with
  | 0%nat => 0
  | (S n)%nat => 1 + nat_to_R n
  end.

Lemma nonneg_R_nat :
  forall (n: nat), 0 <= nat_to_R n.
Proof.
  induction n; intros.
  - simpl. right. reflexivity.
  - simpl.
    apply (Rle_trans _ (nat_to_R n) _).
    assumption.
    rewrite <- Rplus_0_l at 1.
    apply Rplus_le_compat_r.
    left.
    prove_sup.
Qed.

(* Useful Notions *)

Fixpoint Rlist_sum (l: list R) : R :=
  match l with
  | [] => 0
  | h :: t => h + Rlist_sum t
  end.

Fixpoint Rsum_skip (n: nat) (l: list R) : R :=
  match n, l with
  | 0, nil => 0
  | 0, h :: t => Rlist_sum t
  | S n', nil => 0
  | S n', h :: t => h + Rsum_skip n' t
  end.

Definition Rmean (l: list R) : R :=
  Rlist_sum l / nat_to_R (length l).

Fixpoint all_at_most (r: R) (l: list R) : Prop :=
  match l with
  | [] => True
  | h :: t => (h < r) /\ (all_at_most r t)
  end.

Fixpoint all_at_least (r: R) (l: list R) : Prop :=
  match l with
  | [] => True
  | h :: t => (r < h) /\ (all_at_least r t)
  end.

Lemma Rnat_to_R_plus_distr : forall (n m: nat),
  nat_to_R (n + m)%nat = nat_to_R n%nat + nat_to_R m%nat.
Proof.
  induction n; intros.
  - simpl. symmetry. apply Rplus_0_l.
  - simpl. rewrite Rplus_assoc.
    apply Rplus_eq_compat_l.
    apply IHn.
Qed.

Lemma Rnat_to_R_mult_distr : forall (n m: nat),
  nat_to_R (n * m)%nat = nat_to_R n%nat * nat_to_R m%nat.
Proof.
  induction n; intros.
  - simpl. symmetry. apply Rmult_0_l.
  - simpl. rewrite Rmult_plus_distr_r.
    rewrite Rmult_1_l.
    rewrite Rnat_to_R_plus_distr.
    apply Rplus_eq_compat_l.
    apply IHn.
Qed.

Lemma Rlist_sum_ge_0 : forall (l: list R),
  all_at_least 0 l -> 0 <= Rlist_sum l.
Proof.
  induction l; intros.
  - right. reflexivity.
  - destruct H.
    apply IHl in H0.
    simpl.
    left.
    apply (Rlt_le_trans 0 a (a + Rlist_sum l) ).
    + assumption.
    + rewrite <- Rplus_0_r at 1.
      apply Rplus_le_compat_l.
      assumption.
Qed.

Lemma Rlist_sum_distr : forall (l1 l2: list R),
  Rlist_sum (l1 ++ l2) = Rlist_sum l1 + Rlist_sum l2.
Proof.
  induction l1; intros.
  - simpl. symmetry. apply Rplus_0_l.
  - simpl. rewrite Rplus_assoc.
    apply Rplus_eq_compat_l.
    apply IHl1.
Qed.

Lemma nontrivial_all_pos_implies_pos_sum : forall (l: list R),
  (1 <= length l)%nat -> all_at_least 0 l -> 0 < Rlist_sum l.
Proof.
  induction l; intros.
  - inversion H.
  - simpl in H0.
    destruct H0.
    simpl.
    assert (0 <= Rlist_sum l).
      { apply Rlist_sum_ge_0. assumption. }
    apply (Rlt_le_trans 0 a (a + Rlist_sum l)).
    + assumption.
    + rewrite <- Rplus_0_r at 1.
      apply Rplus_le_compat_l.
      assumption.
Qed.

Lemma Rsum_skip_equiv_sum : forall (n: nat) (l: list R),
  (length l <= n)%nat -> Rlist_sum l = Rsum_skip n l.
Proof.
  induction n; intros.
  - inversion H.
    destruct l; try inversion H1.
    reflexivity.
  - inversion H.
    + rewrite H1.
      destruct l; try inversion H1.
      rewrite <- H2 in *.
      simpl.
      f_equal.
      apply IHn.
      apply le_n.
    + assert (Rlist_sum l = Rsum_skip n l). apply IHn. assumption.
      destruct l. reflexivity.
      simpl.
      f_equal.
      apply IHn.
      apply (le_trans (length l) (length (r :: l)) n).
      simpl. apply le_S. apply le_n.
      assumption.
Qed.

Lemma Rsum_skip_equiv_nth : forall (n: nat) (l: list R),
  Rsum_skip n l = Rlist_sum l - nth n l 0.
Proof.
  intros.
  apply (Rplus_eq_reg_l (nth n l 0)).
  replace (nth n l 0 + (Rlist_sum l - nth n l 0))
    with ((Rlist_sum l - nth n l 0) + nth n l 0) by apply Rplus_comm.
  unfold Rminus.
  rewrite Rplus_assoc.
  simpl.
  replace (- nth n l 0 + nth n l 0)
    with (nth n l 0 + - nth n l 0) by apply Rplus_comm.
  rewrite Rplus_opp_r.
  rewrite Rplus_0_r.
  destruct (length l <=? n) eqn:Hn.
  - assert (nth n l 0 = 0). { apply nth_overflow. apply leb_complete. assumption. }
    rewrite H.
    assert (Rlist_sum l = Rsum_skip n l). { apply Rsum_skip_equiv_sum. apply leb_complete. assumption. }
    rewrite H0.
    apply Rplus_0_l.
  - generalize dependent l.
    induction n; intros.
    + destruct l; inversion Hn.
      reflexivity.
    + destruct l; simpl; try Rcompute.
      rewrite <- Rplus_assoc.
      replace (nth n l 0 + r) with (r + nth n l 0) by (apply Rplus_comm).
      rewrite Rplus_assoc.
      apply Rplus_eq_compat_l.
      apply IHn.
      apply leb_iff_conv. apply leb_iff_conv in Hn.
      simpl in Hn. apply lt_S_n in Hn.
      apply Hn.
Qed.

Lemma Rsum_skip_ge_0 : forall (n: nat) (l: list R),
  all_at_least 0 l -> 0 <= Rsum_skip n l.
Proof.
  induction n; induction l; intros.
  - simpl. right. reflexivity.
  - simpl. destruct H. apply Rlist_sum_ge_0. assumption.
  - simpl. right. reflexivity.
  - simpl. destruct H.
    replace 0 with (0 + 0) by Rcompute.
    apply Rplus_le_compat.
    + left. assumption.
    + apply IHn. assumption.
Qed.

Lemma all_at_most_monotonic:
  forall (r1 r2 : R) (l: list R),
    r1 < r2 -> all_at_most r1 l -> all_at_most r2 l.
Proof.
  intros r1 r2 l.
  generalize dependent r2.
  generalize dependent r1.
  induction l; intros.
  - reflexivity.
  - assert (r1 < r2) as Hineq by apply H.
    apply IHl in H.
    destruct H0.
    split.
    apply (Rlt_trans _ r1 _); assumption.
    assumption.
    destruct H0. assumption.
Qed.

Lemma sum_at_least : forall (r: R) (l: list R),
  all_at_least r l -> (nat_to_R (length l)) * r <= Rlist_sum l.
Proof.
  intros r l.
  remember (length l) as n.
  generalize dependent l.
  generalize dependent r.
  induction n; intros.
  - simpl. rewrite Rmult_0_l.
    destruct l; try inversion Heqn.
    simpl. right. reflexivity.
  - destruct l; try inversion Heqn.
    simpl in Heqn. injection Heqn as Heqn.
    specialize (IHn r l).
    apply IHn in H1.
    simpl.
    rewrite Rmult_plus_distr_r.
    apply Rplus_le_compat.
    destruct H. rewrite Rmult_1_l. left. assumption.
    rewrite <- Heqn. assumption.
    destruct H. assumption.
Qed.

Lemma mean_at_least : forall (r: R) (l: list R),
  (1 <= length l)%nat -> all_at_least r l -> r < Rmean l.
Proof.
  intros r l.
  remember (length l) as n.
  generalize dependent l.
  generalize dependent r.
  induction n; intros.
  - inversion H.
  - destruct l. inversion Heqn.
    simpl in Heqn.
    injection Heqn as Heqn.
    specialize (IHn r l).
    unfold Rmean.
    simpl.
    rewrite <- Rmult_1_r at 1.
    unfold Rdiv.
    rewrite <- (Rinv_r (1 + nat_to_R (length l))) at 1.
    rewrite <- Rmult_assoc.
    apply Rmult_lt_compat_r.
    apply Rinv_0_lt_compat.
      { apply (Rlt_le_trans 0 1 (1 + nat_to_R (length l))).
        prove_sup.
        rewrite <- Rplus_0_r at 1.
        apply Rplus_le_compat_l.
        apply nonneg_R_nat. }
    rewrite Rmult_plus_distr_l.
    rewrite Rmult_1_r.
    apply (Rlt_le_trans _ (r0 + r * nat_to_R (length l)) _).
    apply Rplus_lt_compat_r. destruct H0. assumption.
    apply Rplus_le_compat_l.
    rewrite Rmult_comm.
    apply sum_at_least. destruct H0. assumption.
      { apply Rgt_not_eq.
        apply (Rlt_le_trans 0 1 (1 + nat_to_R (length l))).
        prove_sup.
        rewrite <- Rplus_0_r at 1.
        apply Rplus_le_compat_l.
        apply nonneg_R_nat. }
Qed.

Lemma sum_at_most : forall (r: R) (l: list R),
  all_at_most r l -> (nat_to_R (length l)) * r >= Rlist_sum l.
Proof.
  intros r l.
  remember (length l) as n.
  generalize dependent l.
  generalize dependent r.
  induction n; intros.
  - simpl. rewrite Rmult_0_l.
    destruct l; try inversion Heqn.
    simpl. right. reflexivity.
  - destruct l; try inversion Heqn.
    simpl in Heqn. injection Heqn as Heqn.
    specialize (IHn r l).
    apply IHn in H1.
    simpl.
    rewrite Rmult_plus_distr_r.
    apply Rplus_ge_compat.
    destruct H. rewrite Rmult_1_l. left. assumption.
    rewrite <- Heqn. assumption.
    destruct H. assumption.
Qed.

Lemma mean_at_most : forall (r: R) (l: list R),
  (1 <= length l)%nat -> all_at_most r l -> r > Rmean l.
Proof.
  intros r l.
  remember (length l) as n.
  generalize dependent l.
  generalize dependent r.
  induction n; intros.
  - inversion H.
  - destruct l. inversion Heqn.
    simpl in Heqn.
    injection Heqn as Heqn.
    specialize (IHn r l).
    unfold Rmean.
    simpl.
    rewrite <- Rmult_1_r at 1.
    unfold Rdiv.
    rewrite <- (Rinv_r (1 + nat_to_R (length l))) at 1.
    rewrite <- Rmult_assoc.
    apply Rmult_gt_compat_r.
    apply Rlt_gt.
    apply Rinv_0_lt_compat.
      { apply (Rlt_le_trans 0 1 (1 + nat_to_R (length l))).
        prove_sup.
        rewrite <- Rplus_0_r at 1.
        apply Rplus_le_compat_l.
        apply nonneg_R_nat. }
    rewrite Rmult_plus_distr_l.
    rewrite Rmult_1_r.
    apply (Rle_lt_trans _ (r0 + r * nat_to_R (length l)) _).
    apply Rplus_le_compat_l. apply Rge_le.
    rewrite Rmult_comm.
    apply sum_at_most. destruct H0. assumption.
    apply Rplus_lt_compat_r. destruct H0. assumption.
      { apply Rgt_not_eq.
        apply (Rlt_le_trans 0 1 (1 + nat_to_R (length l))).
        prove_sup.
        rewrite <- Rplus_0_r at 1.
        apply Rplus_le_compat_l.
        apply nonneg_R_nat. }
Qed.

Lemma sum_plus_any_is_max: forall (r: R) (l: list R),
  all_at_least 0 l -> 0 < r -> all_at_most (Rlist_sum (r :: l)) l.
Proof.
  intros r l.
  generalize dependent r.
  induction l; intros.
  - reflexivity.
  - split.
    + simpl.
      rewrite Rplus_comm, Rplus_assoc.
      replace a with (a + 0) at 1 by apply Rplus_0_r.
      apply Rplus_lt_compat_l.
      apply (Rlt_le_trans 0 r (Rlist_sum l + r)); try assumption.
      replace r with (0 + r) at 1 by apply Rplus_0_l.
      apply Rplus_le_compat_r.
      apply Rlist_sum_ge_0. destruct H. assumption.
    + specialize (IHl (r + a)).
      destruct H. apply IHl in H1.
      simpl in H1. simpl. rewrite <- Rplus_assoc.
      assumption.
      replace 0 with (0 + 0) by Rcompute.
      apply Rplus_lt_compat; assumption.
Qed.

Theorem sum_is_max: forall (l: list R),
  (2 <= length l)%nat -> all_at_least 0 l -> all_at_most (Rlist_sum l) l.
Proof.
  intros.
  remember (length l) as n.
  generalize dependent H0.
  generalize dependent Heqn.
  generalize dependent H.
  generalize dependent l.
  induction n; intros.
  - inversion H.
  - destruct l. inversion Heqn.
    split.
    + simpl.
      replace r with (r + 0) at 1 by apply Rplus_0_r.
      apply Rplus_lt_compat_l.
      replace 2%nat with (1 + 1)%nat in H by trivial.
      apply plus_le_reg_l in H.
      inversion Heqn.
      rewrite H2 in H.
      destruct H0.
      apply nontrivial_all_pos_implies_pos_sum; assumption.
    + destruct H0.
      apply sum_plus_any_is_max; assumption.
Qed.

(* too bad we don't have filtering capability *)
Lemma In_all_at_most : forall (r: R) (l: list R),
  all_at_most r l <-> (forall a, In a l -> a < r).
Proof.
  intros r l. generalize dependent r.
  induction l; split; intros.
  - inversion H0.
  - reflexivity.
  - destruct H.
    destruct H0.
    + rewrite H0 in H. assumption.
    + assert (forall a : R, In a l -> a < r).
        { apply IHl. assumption. }
      apply H2 in H0. assumption.
  - split.
    + specialize (H a).
      apply H. left. reflexivity.
    + apply IHl.
      intros.
      specialize (H a0). apply H.
      right. assumption.
Qed.

(* practically the same proof except for 3 characters *)
Lemma In_all_at_least : forall (r: R) (l: list R),
  all_at_least r l <-> (forall a, In a l -> r < a).
Proof.
  intros r l. generalize dependent r.
  induction l; split; intros.
  - inversion H0.
  - reflexivity.
  - destruct H.
    destruct H0.
    + rewrite H0 in H. assumption.
    + assert (forall a : R, In a l -> r < a).
        { apply IHl. assumption. }
      apply H2 in H0. assumption.
  - split.
    + specialize (H a).
      apply H. left. reflexivity.
    + apply IHl.
      intros.
      specialize (H a0). apply H.
      right. assumption.
Qed.

Theorem trivial_ineq : forall (r : R), r² >= 0.
Proof.
  intros.
  unfold Rsqr.
  assert (0 < r \/ 0 = r \/ 0 > r) by apply Rtotal_order.
  destruct H; try destruct H.
  - left.
    rewrite <- (Rmult_0_l r).
    apply Rmult_gt_compat_r; assumption.
  - right. rewrite <- H. Rcompute.
  - left.
    rewrite <- (Rmult_0_r r).
    apply Rmult_lt_gt_compat_neg_l; assumption.
Qed.

Lemma r_plus_inv : forall (r : R), r > 0 -> r + / r - 2 >= 0.
Proof.
  unfold Rminus.
  intros.
  remember (sqrt r) as s.
  assert (0 <= s).
    { rewrite Heqs. apply sqrt_pos. }
  assert (s * s = r).
    { apply sqrt_lem_0.
      - left. apply Rgt_lt. assumption.
      - assumption.
      - symmetry. assumption. }
  rewrite <- H1.
  replace (s * s + / (s * s) + - (2)) with ((s + - / s)²).
  apply trivial_ineq.
  unfold Rsqr.
  rewrite Rmult_plus_distr_r.
  rewrite Rmult_plus_distr_l.
  rewrite Rmult_plus_distr_l.
  rewrite Rmult_opp_opp.
  assert (0 < s).
    { rewrite Heqs. apply sqrt_lt_R0. apply Rgt_lt. assumption. }
  replace (s * - / s) with (-1).
  replace (- / s * s) with (-1).
  - rewrite Rplus_assoc, Rplus_assoc.
    apply Rplus_eq_compat_l.
    rewrite <- Rplus_assoc.
    rewrite Rplus_comm.
    rewrite Rinv_mult_distr; try apply Rgt_not_eq; try assumption.
    apply Rplus_eq_compat_l. Rcompute.
  - symmetry. apply neg_inv_prod. apply Rgt_not_eq. assumption.
  - symmetry. rewrite Rmult_comm. apply neg_inv_prod.
    apply Rgt_not_eq. assumption.
Qed.

(* Midpoint-convexity *)

Definition mid_convex_on_open_a_b (a b: R) (f: R -> R) :=
  forall x1 x2, (a < x1 < b) /\ (a < x2 < b) -> f ((x1 + x2) / 2) <= (f x1 + f x2) / 2.

Lemma mid_convex_closure_pos_scalar_mult:
  forall c a b f, 0 <= c -> mid_convex_on_open_a_b a b f -> mid_convex_on_open_a_b a b (fun x => c * f x).
Proof.
  unfold mid_convex_on_open_a_b.
  unfold Rdiv.
  intros.
  rewrite <- Rmult_plus_distr_l.
  assert (0 < c \/ 0 = c \/ 0 > c) by apply Rtotal_order.
  destruct H2; try destruct H2.
  - rewrite Rmult_assoc.
    apply Rmult_le_compat_l.
    apply Rlt_le. assumption.
    apply H0. assumption.
  - rewrite Rmult_assoc.
    apply Rmult_le_compat_l.
    rewrite H2. apply Rle_refl.
    apply H0. assumption.
  - exfalso.
    apply Rgt_lt in H2.
    assert (c < c).
      { apply (Rlt_le_trans _ 0 _); assumption. }
    assert (~ c < c) by apply Rlt_irrefl.
    apply H4. apply H3.
Qed.

Lemma mid_convex_closure_add:
  forall c a b f, mid_convex_on_open_a_b a b f -> mid_convex_on_open_a_b a b (fun x => c + f x).
Proof.
  unfold mid_convex_on_open_a_b.
  unfold Rdiv.
  intros.
  apply H in H0.
  replace (c + f x2) with (f x2 + c) by apply Rplus_comm.
  rewrite Rplus_assoc.
  replace (f x1 + (f x2 + c)) with ((f x1 + f x2) + c) by apply Rplus_assoc.
  replace (f x1 + f x2 + c) with (c + (f x1 + f x2)) by apply Rplus_comm.
  rewrite <- Rplus_assoc.
  assert ((c + c + (f x1 + f x2)) * / 2 = (c + c) * / 2 + (f x1 + f x2) * / 2) by apply Rmult_plus_distr_r.
  rewrite H1.
  assert ((c + c) * / 2 = c).
    { replace c with (1 * c) by apply Rmult_1_l. rewrite <- Rmult_plus_distr_r.
      rewrite Rmult_comm. rewrite <- Rmult_assoc. apply Rmult_eq_compat_r.
      replace (1 + 1) with 2 by Rcompute. symmetry. apply Rinv_l_sym. discrR. }
  rewrite H2.
  apply Rplus_le_compat_l.
  assumption.
Qed.

Lemma mid_convex_closure_translate:
  forall c a b f, mid_convex_on_open_a_b a b f -> mid_convex_on_open_a_b (a-c) (b-c) (fun x => f (x + c)).
Proof.
  unfold mid_convex_on_open_a_b.
  unfold Rminus.
  unfold Rdiv.
  intros.
  specialize (H (x1+c) (x2+c)).
  assert (f ((x1 + c + (x2 + c)) * / 2) <= (f (x1 + c) + f (x2 + c)) / 2).
    { apply H. destruct H0. destruct H0. destruct H1. split; split;
        apply (Rplus_lt_reg_r (- c)); rewrite Rplus_assoc;
        rewrite Rplus_opp_r; rewrite Rplus_0_r; assumption. }
  apply (Rle_trans _ (f ((x1 + c + (x2 + c)) * / 2)) _); try assumption.
  right.
  rewrite Rplus_assoc.
  replace (c + (x2 + c)) with ((x2 + c) + c) by apply Rplus_comm.
  rewrite Rplus_assoc. rewrite <- Rplus_assoc.
  assert ((x1 + x2 + (c + c)) * / 2 = (x1 + x2) * / 2 + (c + c) * / 2) by apply Rmult_plus_distr_r.
  rewrite H2.
  assert ((c + c) * / 2 = c).
    { replace c with (1 * c) by apply Rmult_1_l. rewrite <- Rmult_plus_distr_r.
      rewrite Rmult_comm. rewrite <- Rmult_assoc. apply Rmult_eq_compat_r.
      replace (1 + 1) with 2 by Rcompute. symmetry. apply Rinv_l_sym. discrR. }
  rewrite H3.
  reflexivity.
Qed.

Lemma neg_2_over_x_mid_convex: mid_convex_on_open_a_b (-2) (-1) (fun x => - 2 / x).
Proof.
  unfold mid_convex_on_open_a_b.
  unfold Rdiv.
  intros.
  rewrite <- Rmult_plus_distr_l.
  rewrite Rmult_assoc.
  apply Rmult_le_compat_neg_l.
    { left. prove_sup. }
  assert (x1+x2 < 0).
    { apply (Rlt_trans _ (-1 + -1) _).
      - destruct H, H, H0.
        apply Rplus_lt_compat; assumption.
      - prove_sup. }
  assert (x1+x2 <> 0).
    { apply Rlt_not_eq; assumption. }
  rewrite Rinv_mult_distr.
  - rewrite Rinv_involutive; try discrR.
    apply (Rmult_le_reg_r 2); try prove_sup.
    rewrite Rmult_assoc.
    rewrite Rinv_l; try discrR.
    rewrite Rmult_1_r.
    rewrite Rmult_assoc.
    replace (2 * 2) with 4 by Rcompute.
    rewrite <- Rmult_1_l at 1.
    rewrite <- (Rinv_l (x1 + x2)); try assumption.
    rewrite Rmult_assoc.
    apply Rmult_le_compat_neg_l.
      { apply Rlt_le.
        apply Rinv_lt_0_compat.
        assumption. }
    rewrite Rmult_plus_distr_r.
    rewrite Rmult_plus_distr_l.
    rewrite Rmult_plus_distr_l.
    rewrite Rinv_r; try rewrite Rinv_r.
    + rewrite Rplus_assoc, Rplus_comm.
      apply (Rplus_le_reg_r (-4)).
      rewrite Rplus_opp_r.
      rewrite Rplus_assoc.
      rewrite Rplus_assoc.
      replace (1 + -4) with (-3) by Rcompute.
      rewrite Rplus_assoc.
      replace (1 + -3) with (-2) by Rcompute.
      assert (x1 * / x2 > 0).
        { destruct H, H, H2.
          apply Rinv_lt_contravar in H2.
          apply (Rgt_trans (x1 * / x2) (x1 * / -2) 0).
          apply Rmult_lt_gt_compat_neg_l.
          - apply (Rlt_trans _ (-1) _).
            assumption. prove_sup.
          - assumption.
          - replace 0 with (0 * 1) by Rcompute.
            replace 1 with (- 2 * / - 2).
            rewrite <- Rmult_assoc.
            rewrite Rmult_comm.
            replace (0 * -2 * / -2) with (/ -2 * (0 * -2 )) by apply Rmult_comm.
            apply Rmult_lt_gt_compat_neg_l.
            + apply Rinv_lt_0_compat. prove_sup.
            + rewrite Rmult_0_l.
              apply (Rlt_trans _ (-1) _).
              assumption. prove_sup.
            + apply Rinv_r. discrR.
          - apply (Rlt_trans _ (-2 * -1) _).
            replace (-2 * -1) with 2 by Rcompute. prove_sup.
            apply Rmult_lt_gt_compat_neg_l.
            prove_sup. assumption. }
      assert (x1 * / x2 + (x2 * / x1 + -2) = (x1 * / x2 + / (x1 * / x2) - 2)).
      * unfold Rminus.
        rewrite Rplus_assoc.
        apply Rplus_eq_compat_l.
        rewrite Rinv_mult_distr.
        -- rewrite Rinv_involutive.
           rewrite Rmult_comm.
           apply Rplus_eq_compat_l.
           Rcompute.
           destruct H, H3.
           apply Rlt_not_eq.
           apply (Rlt_trans _ (-1) _).
           assumption. prove_sup.
        -- destruct H, H.
           apply Rlt_not_eq.
           apply (Rlt_trans _ (-1) _).
           assumption. prove_sup.
        -- destruct H, H3.
           apply Rlt_not_eq.
           apply Rinv_lt_0_compat.
           apply (Rlt_trans _ (-1) _).
           assumption. prove_sup.
      * rewrite H3.
        apply Rge_le.
        apply r_plus_inv.
        assumption.
    + destruct H. destruct H2. apply Rlt_not_eq.
      apply (Rlt_trans _ (-1) _); try assumption; prove_sup.
    + destruct H. destruct H. apply Rlt_not_eq.
      apply (Rlt_trans _ (-1) _); try assumption; prove_sup.
  - assumption.
  - apply Rgt_not_eq.
    apply (Rmult_gt_reg_l 2); try prove_sup.
    rewrite Rinv_r; try prove_sup; discrR.
Qed.

Lemma x_2x_1_mid_convex: mid_convex_on_open_a_b 0 1 (fun x => x / (2-x)).
Proof.
  unfold mid_convex_on_open_a_b.
  intros.
  rename H into Hineq.
  assert (forall f, mid_convex_on_open_a_b 0 1 f -> mid_convex_on_open_a_b 0 1 (fun x => -1 + f x))
    by apply mid_convex_closure_add.
  assert (forall f, mid_convex_on_open_a_b (-2) (-1) f -> mid_convex_on_open_a_b 0 1 (fun x => f (x - 2))).
    { intros. specialize (mid_convex_closure_translate (-2) (-2) (-1) f).
      intros. apply H1 in H0.
      replace (-2 - -2) with 0 in H0 by Rcompute.
      replace (-1 - -2) with 1 in H0 by Rcompute.
      assumption. }
  assert (mid_convex_on_open_a_b (-2) (-1) (fun x => - 2 / x)) by apply neg_2_over_x_mid_convex.
  apply H0 in H1.
  apply H in H1.
  unfold mid_convex_on_open_a_b in H1.
  assert (0 < x1 < 1 /\ 0 < x2 < 1) as cond by assumption.
  apply H1 in cond.
  remember (fun x : R => x / (2 - x)) as f1.
  remember (fun x : R => -1 + -2 / (x - 2)) as f2.
  assert ((x1 + x2) / 2 < 1).
    { destruct Hineq, H2, H3.
      unfold Rdiv.
      apply (Rmult_lt_reg_r 2); try prove_sup.
      rewrite Rmult_assoc.
      rewrite Rinv_l.
      rewrite Rmult_1_l, Rmult_1_r.
      replace 2 with (1 + 1) by Rcompute.
      apply Rplus_lt_compat; assumption.
      discrR. }
  replace ((x1 + x2) / 2 / (2 - (x1 + x2) / 2)) with (f1 ((x1 + x2) / 2)).
  replace ((x1 / (2 - x1) + x2 / (2 - x2)) / 2) with ((f1 x1 + f1 x2) / 2).
  replace (-1 + -2 / ((x1 + x2) / 2 - 2)) with (f2 (((x1 + x2) / 2))) in cond.
  replace ((-1 + -2 / (x1 - 2) + (-1 + -2 / (x2 - 2))) / 2) with ((f2 x1 + f2 x2) / 2) in cond.
  assert (forall x, x < 1 -> f1 x = f2 x).
  - intros.
    rewrite Heqf1.
    rewrite Heqf2.
    unfold Rdiv.
    replace (x - 2) with (- (2 - x)).
    replace (-1) with (-1 * 1) by Rcompute.
    rewrite <- (Rinv_r (- (2 - x))).
    rewrite <- Rmult_assoc.
    rewrite <- Rmult_plus_distr_r.
    rewrite neg_minus_equiv.
    rewrite Ropp_involutive.
    rewrite Rplus_comm.
    rewrite <- Ropp_inv_permute.
    rewrite <- neg_minus_equiv.
    rewrite <- Rmult_assoc.
    rewrite Rmult_plus_distr_r.
    replace (-2 * -1) with 2 by Rcompute.
    replace (2 + (2 - x) * -1) with x.
    + reflexivity.
    + unfold Rminus.
      rewrite Rmult_plus_distr_r.
      rewrite <- Rplus_assoc.
      replace (2 + 2 * -1) with 0 by Rcompute.
      rewrite Rplus_0_l.
      rewrite Rmult_comm.
      rewrite neg_minus_equiv.
      symmetry.
      apply Ropp_involutive.
    + apply Rgt_not_eq.
      unfold Rminus.
      replace 0 with (x + -x) by apply Rplus_opp_r.
      apply Rplus_gt_compat_r.
      apply Rlt_gt.
      apply (Rlt_trans _ 1 _).
      assumption. prove_sup.
    + apply Rlt_not_eq.
      unfold Rminus.
      rewrite Ropp_plus_distr.
      replace 0 with (-x + --x) by apply Rplus_opp_r.
      apply Rplus_lt_compat_r.
      apply Ropp_lt_contravar.
      apply (Rlt_trans _ 1 _).
      assumption. prove_sup.
    + unfold Rminus.
      rewrite Ropp_plus_distr.
      rewrite Ropp_involutive.
      apply Rplus_comm.
  - replace (f2 ((x1 + x2) / 2)) with (f1 ((x1 + x2) / 2)) in cond.
    replace (f2 x1) with (f1 x1) in cond.
    replace (f2 x2) with (f1 x2) in cond.
    apply cond.
    apply H3. apply Hineq.
    apply H3. apply Hineq.
    apply H3. assumption.
  - rewrite Heqf2. reflexivity.
  - rewrite Heqf2. reflexivity.
  - rewrite Heqf1. reflexivity.
  - rewrite Heqf1. reflexivity.
Qed.

Close Scope R_scope.

(* Cauchy Induction *)

Lemma _4_n_2_n1: forall n, 1 <= n -> 2 * S n <= 2 * (2 * n).
Proof.
  induction n; intros.
  - inversion H.
  - destruct (1 <=? n) eqn:Hn.
    + apply leb_complete in Hn.
      apply IHn in Hn.
      replace (2 * S (S n)) with (2 + 2 * S n).
      replace (2 * (2 * S n)) with (4 + 2 * (2 * n)).
      apply plus_le_compat.
      constructor. constructor. constructor.
      assumption.
      rewrite Nat.mul_assoc, Nat.mul_assoc.
      replace (2 * 2) with 4 by reflexivity.
      replace (S n) with (1 + n) by reflexivity.
      replace 4 with (4 * 1) at 1 by reflexivity.
      symmetry. apply Nat.mul_add_distr_l.
      replace (S (S n)) with (1 + S n) by reflexivity.
      replace 2 with (2 * 1) at 1 by reflexivity.
      symmetry. apply Nat.mul_add_distr_l.
    + apply Nat.leb_nle in Hn.
      inversion H.
      reflexivity.
      exfalso. apply Hn. assumption.
Qed.

Lemma _silly_eq : forall (n m : nat),
  m <= n <= m -> n = m.
Proof.
  intros.
  destruct H.
  inversion H.
  reflexivity.
  exfalso.
  rewrite <- H2 in H0.
  assert (S m0 <= m0).
    { apply (le_trans _ m _); assumption. }
  apply Nat.nle_succ_diag_l in H3.
  apply H3.
Qed.

Lemma bounded_induction_by_doubling:
  forall (n: nat) (P: nat -> Prop),
    1 <= n ->
    P(1) ->
    (forall a b,
      ((forall k, a <= k <= b -> P(k)) -> (forall k, 2 * a <= k <= 2 * b -> P(k)))
    )
    -> (forall k, 1 <= k <= 2*n -> P(k)).
Proof.
  induction n; intros.
  - inversion H.
  - destruct (1 <=? n) eqn:Hn.
    + apply leb_complete in Hn.
      assert (forall k : nat, 1 <= k <= 2 * n -> P k).
        { apply IHn; assumption. }
      (* assert (H1' := H1). *)
      specialize (H1 1 (2 * n)).
      assert (forall k : nat, 2 * 1 <= k <= 2 * (2 * n) -> P k).
        { apply H1. assumption. }
      destruct (2 <=? k) eqn:Hk.
      * apply leb_complete in Hk.
        apply H4.
        split.
        apply Hk.
        destruct H2.
        apply (le_trans k (2 * S n) (2 * (2 * n))).
        assumption. apply _4_n_2_n1.
        apply Hn.
      * apply Nat.leb_nle in Hk.
        assert (1 = k).
        { destruct H2.
          apply not_le in Hk.
          inversion H2. reflexivity.
          destruct m. reflexivity.
          rewrite <- H7 in Hk.
          inversion Hk. inversion H9. inversion H11. }
        rewrite <- H5.
        assumption.
    + apply Nat.leb_nle in Hn.
      destruct (0 =? n) eqn:Hn'.
      * apply Nat.eqb_eq in Hn'.
        rewrite <- Hn' in H2.
        simpl in H2.
        inversion H2.
        inversion H4.
        specialize (H1 1 1).
        assert (forall k : nat, 2 * 1 <= k <= 2 * 1 -> P k).
        { apply H1. intros.
          apply _silly_eq in H6.
          rewrite H6. assumption. }
        specialize (H6 2).
        apply H6.
        split; trivial.
        assert (k = 1).
        { apply _silly_eq. split; assumption. }
        rewrite H7. assumption.
      * exfalso.
        apply Hn.
        apply Nat.eqb_neq in Hn'.
        apply neq_0_lt in Hn'.
        apply lt_le_S. assumption.
Qed.

Lemma induction_by_doubling:
  forall (P: nat -> Prop),
    P(1) ->
    (forall a b,
      ((forall k, a <= k <= b -> P(k)) -> (forall k, 2 * a <= k <= 2 * b -> P(k)))
    )
    -> (forall k, 1 <= k -> P(k)).
Proof.
  intros.
  specialize (bounded_induction_by_doubling k P).
  intros.
  assert (forall k0 : nat, 1 <= k0 <= 2 * k -> P k0).
  apply H2; assumption.
  specialize (H3 k).
  apply H3.
  split; try assumption.
  replace 2 with (1 + 1) by reflexivity.
  rewrite Nat.mul_add_distr_r.
  simpl.
  replace (k + 0) with k by trivial.
  replace k with (k + 0) at 1 by auto.
  apply plus_le_compat_l.
  apply Nat.le_0_l.
Qed.

Theorem finite_descent_variant : forall (P: nat -> Prop),
  (forall k, 1 <= k -> P(S k) -> P(k))
    -> (forall k, P(k) -> (forall i, 1 <= i <= k -> P(i))).
Proof.
  intros P Hk.
  induction k; intros.
  - assert (1 <= 0).
    apply (le_trans _ i _); apply H0.
    inversion H1.
  - destruct (0 =? k) eqn:Hk'.
    + apply Nat.eqb_eq in Hk'. rewrite <- Hk' in *.
      apply _silly_eq in H0.
      rewrite H0. assumption.
    + apply Nat.eqb_neq in Hk'.
      apply neq_0_lt in Hk'.
      apply lt_le_S in Hk'.
      apply Hk in Hk'; try assumption.
      destruct (i <=? k) eqn:Hik.
      * apply leb_complete in Hik.
        assert (1 <= i <= k -> P i).
          { apply IHk. assumption. }
        apply H1.
        split; destruct H0; assumption.
      * apply Nat.leb_nle in Hik.
        Search (~ _ <= _ -> _).
        apply not_le in Hik.
        apply lt_le_S in Hik.
        destruct H0.
        assert (i = S k).
          { apply _silly_eq. split; assumption. }
        rewrite H2. assumption.
Qed.

Theorem cauchy_induction:
  forall (P: nat -> Prop),
    P(1)
    -> (forall k, 1 <= k -> P(k) -> P(2 * k))
    -> (forall k, 1 <= k -> P(S k) -> P(k))
    -> (forall k, 1 <= k -> P(k)).
Proof.
  intros.
  apply induction_by_doubling; try assumption.
  intros.
  destruct H4.
  assert (2 * a <= 2 * b).
    { apply (le_trans _ k0 _); assumption. }
  apply le_double in H6.
  specialize (H0 b).
  assert (P b).
    { apply H3. split. assumption. constructor. }
  apply H0 in H7.
  assert (b <= 2*b) by apply le_n_2n.
  assert (forall i : nat, 1 <= i <= 2 * b -> P i).
    { apply finite_descent_variant; assumption. }
  destruct (0 =? k0) eqn:Hk0.
  - apply Nat.eqb_eq in Hk0.
    rewrite <- Hk0 in H4.
    replace 0 with (2 * 0) in H4 at 2 by reflexivity.
    apply mult_S_le_reg_l in H4.
    inversion H4.
    apply H3.
    split.
    + rewrite <- Hk0. rewrite H10. constructor.
    + rewrite <- Hk0. apply Nat.le_0_l.
  - apply Nat.eqb_neq in Hk0.
    apply neq_0_lt in Hk0.
    apply H9.
    split.
    + apply Hk0.
    + apply H5.
Qed.

Lemma half_lists : forall (A: Type) (n: nat) (l: list A),
  (2 * n = length l)%nat ->
    exists l1 l2, n = length l1 /\ n = length l2 /\ l = l1 ++ l2.
Proof.
  induction n; intros.
  - exists [], [].
    simpl in H. symmetry in H. apply length_zero_iff_nil in H.
    rewrite H.
    split; try split; try reflexivity.
  - destruct l.
    inversion H.
    destruct l.
    inversion H. rewrite <- plus_n_Sm in H1. inversion H1.
    simpl in H. rewrite <- plus_n_Sm in H. injection H as H.
    specialize (IHn l).
    assert (H' := H).
    apply IHn in H'.
    destruct H', H0, H0, H1.
    destruct n.
    + exists [a], [a0].
      simpl.
      symmetry in H. apply length_zero_iff_nil in H.
      rewrite H.
      split; try split; reflexivity.
    + assert (exists (l' : list A) (x0 : A), x = l' ++ [x0]).
        { apply (final_of_list _ (S n) _).
          replace 1 with (1+0) by reflexivity.
          apply plus_le_compat_l. apply Nat.le_0_l.
          assumption. }
      destruct H3, H3.
      destruct x0. inversion H1.
      exists(a :: a0 :: x1), (x2 :: a1 :: x0).
      split; try split.
      * simpl. f_equal.
        rewrite H3 in H0.
        rewrite last_length in H0. assumption.
      * simpl. f_equal. simpl in H1. assumption.
      * rewrite H2. rewrite H3.
        simpl.
        f_equal. f_equal.
        rewrite <- app_assoc.
        reflexivity.
Qed.

Local Open Scope R_scope.

(* Finite Jensen's *)

Lemma front_at_least : forall (r: R) (l1 l2: list R),
  all_at_least r (l1 ++ l2) -> all_at_least r l1.
Proof.
  intros r l1.
  generalize dependent r.
  induction l1; intros.
  - reflexivity.
  - destruct H.
    split; try assumption.
    apply (IHl1 r l2). assumption.
Qed.

Lemma back_at_least : forall (r: R) (l1 l2: list R),
  all_at_least r (l1 ++ l2) -> all_at_least r l2.
Proof.
  intros r l1 l2.
  generalize dependent l1. generalize dependent r.
  induction l2; intros.
  - reflexivity.
  - specialize (IHl2 r (l1 ++ [a])). rewrite <- app_assoc in IHl2.
    split.
    + apply (In_all_at_least r (l1 ++ a :: l2)).
      apply H.
      apply in_or_app.
      right. left. reflexivity.
    + apply IHl2. apply H.
Qed.

Lemma front_at_most : forall (r: R) (l1 l2: list R),
  all_at_most r (l1 ++ l2) -> all_at_most r l1.
Proof.
  intros r l1.
  generalize dependent r.
  induction l1; intros.
  - reflexivity.
  - destruct H.
    split; try assumption.
    apply (IHl1 r l2). assumption.
Qed.

Lemma back_at_most : forall (r: R) (l1 l2: list R),
  all_at_most r (l1 ++ l2) -> all_at_most r l2.
Proof.
  intros r l1 l2.
  generalize dependent l1. generalize dependent r.
  induction l2; intros.
  - reflexivity.
  - specialize (IHl2 r (l1 ++ [a])). rewrite <- app_assoc in IHl2.
    split.
    + apply (In_all_at_most r (l1 ++ a :: l2)).
      apply H.
      apply in_or_app.
      right. left. reflexivity.
    + apply IHl2. apply H.
Qed.

Lemma mean_with_mean:
  forall (l: list R), (1 <= length l)%nat -> Rmean l = Rmean ((Rmean l) :: l).
Proof.
  intros.
  unfold Rmean.
  simpl.
  remember (length l) as n.
  remember (nat_to_R n) as Rn.
  remember (Rlist_sum l) as lsum.
  unfold Rdiv.
  apply (Rmult_eq_reg_r (1 + Rn)).
  replace ((lsum * / Rn + lsum) * / (1 + Rn) * (1 + Rn))
    with ((lsum * / Rn + lsum) * (/ (1 + Rn) * (1 + Rn))).
  rewrite Rinv_l.
  rewrite Rmult_1_r.
  rewrite Rmult_plus_distr_l.
  rewrite Rmult_1_r.
  rewrite Rmult_assoc.
  rewrite Rinv_l.
  rewrite Rmult_1_r.
  reflexivity.
  - destruct l.
    simpl in Heqn.
    rewrite Heqn in H.
    inversion H.
    apply Rgt_not_eq.
    simpl in Heqn.
    rewrite Heqn in HeqRn.
    simpl in HeqRn.
    rewrite HeqRn.
    apply (Rlt_le_trans 0 1 (1 + nat_to_R (length l))).
    prove_sup.
    replace 1 with (1 + 0) at 1 by Rcompute.
    apply Rplus_le_compat_l, nonneg_R_nat.
  - apply Rgt_not_eq.
    rewrite HeqRn.
    apply (Rlt_le_trans 0 1 (1 + nat_to_R n)).
    prove_sup.
    replace 1 with (1 + 0) at 1 by Rcompute.
    apply Rplus_le_compat_l, nonneg_R_nat.
  - symmetry. apply Rmult_assoc.
  - apply Rgt_not_eq.
    rewrite HeqRn.
    apply (Rlt_le_trans 0 1 (1 + nat_to_R n)).
    prove_sup.
    replace 1 with (1 + 0) at 1 by Rcompute.
    apply Rplus_le_compat_l, nonneg_R_nat.
Qed.

Lemma low_value_is_low : forall (r: R) (l: list R),
  (1 <= length l)%nat -> r <= Rmean (r :: l) -> r <= Rmean l.
Proof.
  unfold Rmean. unfold Rdiv.
  intros.
  assert (nat_to_R (length l) > 0) as Hl.
      { destruct l. inversion H. simpl.
        apply (Rlt_le_trans 0 1 (1 + nat_to_R (length l))).
        prove_sup.
        rewrite <- Rplus_0_r at 1.
        apply Rplus_le_compat_l.
        apply nonneg_R_nat. }
  simpl in H0.
  apply (Rmult_le_compat_r (1 + nat_to_R (length l))) in H0.
  rewrite Rmult_assoc, Rinv_l, Rmult_plus_distr_l, Rmult_1_r, Rmult_1_r in H0.
  apply Rplus_le_reg_l in H0.
  apply (Rmult_le_reg_r (nat_to_R (length l))). apply Hl.
  rewrite Rmult_assoc, Rinv_l, Rmult_1_r.
  apply H0.
  apply Rgt_not_eq; assumption.
  apply Rgt_not_eq, (Rlt_trans _ 1 _); try prove_sup.
  rewrite <- Rplus_0_r at 1.
  apply Rplus_lt_compat_l. apply Hl.
  left.
  apply (Rlt_trans _ 1 _); try prove_sup.
  rewrite <- Rplus_0_r at 1.
  apply Rplus_lt_compat_l. apply Hl.
Qed.

Lemma low_value_low_avg : forall (r: R) (l: list R),
  (1 <= length l)%nat -> r <= Rmean (r :: l) -> Rmean (r :: l) <= Rmean l.
Proof.
  intros r l.
  remember (length l) as n.
  generalize dependent r.
  generalize dependent l.
  induction n; intros.
  - inversion H.
  - destruct l. inversion Heqn.
    simpl in Heqn. injection Heqn as Heqn.
    remember (r0 :: l) as l'.
    unfold Rmean. unfold Rdiv.
    simpl.
    assert (nat_to_R (length l') > 0) as lenl'.
      { rewrite Heql'. simpl.
        apply (Rlt_le_trans 0 1 (1 + nat_to_R (length l))).
        prove_sup.
        replace 1 with (1 + 0) at 1 by Rcompute.
        apply Rplus_le_compat_l.
        apply nonneg_R_nat. }
    assert (1 + nat_to_R (length l') > 0) as l'neq0.
      { apply (Rlt_trans 0 (nat_to_R (length l')) (1 + nat_to_R (length l'))).
        apply lenl'.
        rewrite <- Rplus_0_l at 1.
        apply Rplus_lt_compat_r.
        prove_sup. }
    apply (Rmult_le_reg_r (1 + nat_to_R (length l'))). apply l'neq0.
    rewrite Rmult_assoc, Rinv_l, Rmult_1_r.
    rewrite Rmult_comm, <- Rmult_assoc.
    apply (Rmult_le_reg_r (nat_to_R (length l'))). apply lenl'.
    rewrite Rmult_assoc, Rinv_l, Rmult_1_r.
    rewrite Rmult_plus_distr_r, Rmult_plus_distr_r.
    replace (Rlist_sum l' * nat_to_R (length l')) with (nat_to_R (length l') * Rlist_sum l') by apply Rmult_comm.
    apply Rplus_le_compat_r.
    rewrite Rmult_1_l.
    assert (r <= Rmean l').
      { apply low_value_is_low; try assumption.
        rewrite Heql'. simpl. rewrite <- Heqn.
        assumption. }
    unfold Rmean, Rdiv in H1.
    apply (Rmult_le_compat_r (nat_to_R (length l'))) in H1.
    rewrite Rmult_assoc, Rinv_l, Rmult_1_r in H1.
    apply H1.
    apply Rgt_not_eq. apply lenl'.
    left. apply lenl'.
    apply Rgt_not_eq. apply lenl'.
    apply Rgt_not_eq. apply l'neq0.
Qed.

Lemma drop_lowest_improves_avg : forall (r: R) (l: list R),
  (1 <= length l)%nat -> r <= Rmean l -> Rmean (r :: l) <= Rmean l.
Proof.
  intros r l.
  remember (length l) as n.
  generalize dependent r.
  generalize dependent l.
  induction n; intros.
  - inversion H.
  - destruct l. inversion Heqn.
    simpl in Heqn. injection Heqn as Heqn.
    remember (r0 :: l) as l'.
    unfold Rmean. unfold Rdiv.
    simpl.
    assert (nat_to_R (length l') > 0) as lenl'.
      { rewrite Heql'. simpl.
        apply (Rlt_le_trans 0 1 (1 + nat_to_R (length l))).
        prove_sup.
        replace 1 with (1 + 0) at 1 by Rcompute.
        apply Rplus_le_compat_l.
        apply nonneg_R_nat. }
    assert (1 + nat_to_R (length l') > 0) as l'neq0.
      { apply (Rlt_trans 0 (nat_to_R (length l')) (1 + nat_to_R (length l'))).
        apply lenl'.
        rewrite <- Rplus_0_l at 1.
        apply Rplus_lt_compat_r.
        prove_sup. }
    apply (Rmult_le_reg_r (1 + nat_to_R (length l'))). apply l'neq0.
    rewrite Rmult_assoc, Rinv_l, Rmult_1_r.
    rewrite Rmult_comm, <- Rmult_assoc.
    apply (Rmult_le_reg_r (nat_to_R (length l'))). apply lenl'.
    rewrite Rmult_assoc, Rinv_l, Rmult_1_r.
    rewrite Rmult_plus_distr_r, Rmult_plus_distr_r.
    replace (Rlist_sum l' * nat_to_R (length l')) with (nat_to_R (length l') * Rlist_sum l') by apply Rmult_comm.
    apply Rplus_le_compat_r.
    rewrite Rmult_1_l.
    unfold Rmean in H0. unfold Rdiv in H0.
    apply (Rmult_le_compat_r (nat_to_R (length l'))) in H0.
    rewrite Rmult_assoc in H0.
    rewrite Rinv_l in H0.
    rewrite Rmult_1_r in H0.
    assumption.
    apply Rgt_not_eq. apply lenl'.
    left. apply lenl'.
    apply Rgt_not_eq. apply lenl'.
    apply Rgt_not_eq. apply l'neq0.
Qed.

Definition fulfill_n_var_jensen (n: nat) :=
  forall (a b: R) (l: list R) (f: R -> R),
    (n = length l /\ all_at_least a l /\ all_at_most b l /\
      mid_convex_on_open_a_b a b f)
    -> f (Rmean l) <= Rmean (map f l).

Lemma one_var_jensen : fulfill_n_var_jensen 1.
Proof.
  unfold fulfill_n_var_jensen.
  intros.
  destruct H, H0, H1.
  destruct l; try inversion H.
  destruct l; try inversion H4.
  unfold Rmean.
  simpl.
  rewrite Rplus_0_r, Rplus_0_r, Rplus_0_r.
  unfold Rdiv.
  rewrite Rinv_1.
  rewrite Rmult_1_r, Rmult_1_r.
  right. reflexivity.
Qed.

Lemma S_n_var_jensen_implies_n_var_jensen :
  forall n, (1 <= n)%nat ->
    fulfill_n_var_jensen (S n) -> fulfill_n_var_jensen n.
Proof.
  unfold fulfill_n_var_jensen.
  intros.
  remember (Rmean l) as mu.
  remember (mu :: l) as l'.
  assert (Hmain := H0).
  specialize (Hmain a b l' f).

  assert (f (Rmean l') <= Rmean (map f l')).
    { destruct H1, H2, H3.
      apply Hmain. split; try split; try split.
      - rewrite Heql'. rewrite H1.
        reflexivity.
      - rewrite Heql'. simpl. split; try assumption.
        rewrite Heqmu.
        apply mean_at_least.
        rewrite <- H1. assumption. assumption.
      - rewrite Heql'. simpl. split; try assumption.
        rewrite Heqmu.
        apply mean_at_most.
        rewrite <- H1. assumption. assumption.
      - assumption. }
  assert (mu = Rmean l').
    { rewrite Heql'.
      rewrite Heqmu.
      apply mean_with_mean.
      destruct H1.
      rewrite H1 in H.
      assumption. }
  rewrite <- H3 in H2.
  apply (Rle_trans _ (Rmean (map f l')) _); try assumption.
  rewrite Heql'.
  simpl.
  apply low_value_low_avg.
  rewrite map_length. destruct H1. rewrite <- H1. assumption.
  rewrite Heql' in H2. simpl in H2.
  assumption.
Qed.

Lemma n_var_jensen_implies_2n_var_jensen :
  forall n, (1 <= n)%nat ->
    fulfill_n_var_jensen n -> fulfill_n_var_jensen (2 * n).
Proof.
  unfold fulfill_n_var_jensen.
  induction n; intros.
  inversion H.
  destruct H1, H2, H3.
  assert (exists l1 l2, S n = length l1 /\ S n = length l2 /\ l = l1 ++ l2).
    { apply half_lists. assumption. }
  destruct H5, H5, H5, H6.
  rename H7 into lxx0.
  assert (f (Rmean x) <= Rmean (map f x)).
    { apply (H0 a b).
      split; try split; try split.
      - assumption.
      - apply (front_at_least a x x0).
        rewrite <- lxx0. assumption.
      - apply (front_at_most b x x0).
        rewrite <- lxx0. assumption.
      - assumption. }
  assert (f (Rmean x0) <= Rmean (map f x0)).
    { apply (H0 a b).
      split; try split; try split.
      - assumption.
      - apply (back_at_least a x x0).
        rewrite <- lxx0. assumption.
      - apply (back_at_most b x x0).
        rewrite <- lxx0. assumption.
      - assumption. }
  assert (Rmean l = (Rmean x + Rmean x0) / 2).
    { unfold Rmean, Rdiv.
      rewrite <- H1, <- H5, <- H6.
      rewrite lxx0.
      rewrite Rlist_sum_distr.
      rewrite <- Rmult_plus_distr_r.
      rewrite Rmult_assoc.
      replace (/ nat_to_R (S n) * / 2)
        with (/ 2 * / nat_to_R (S n)) by apply Rmult_comm.
      rewrite <- Rinv_mult_distr.
      replace 2 with (nat_to_R 2).
      rewrite <- Rnat_to_R_mult_distr.
      reflexivity.
      simpl. Rcompute.
      discrR.
      simpl. apply Rgt_not_eq.
      apply (Rlt_le_trans 0 1 (1 + nat_to_R n)).
      prove_sup.
      replace 1 with (1+0) at 1 by Rcompute.
      apply Rplus_le_compat_l.
      apply nonneg_R_nat. }
  assert (Rmean (map f l) = (Rmean (map f x) + Rmean (map f x0)) / 2).
    { unfold Rmean, Rdiv.
      rewrite map_length, map_length, map_length.
      rewrite <- H1, <- H5, <- H6.
      rewrite lxx0, map_app, Rlist_sum_distr.
      rewrite <- Rmult_plus_distr_r.
      rewrite Rmult_assoc.
      replace (/ nat_to_R (S n) * / 2)
        with (/ 2 * / nat_to_R (S n)) by apply Rmult_comm.
      rewrite <- Rinv_mult_distr.
      replace 2 with (nat_to_R 2).
      rewrite <- Rnat_to_R_mult_distr.
      reflexivity.
      simpl. Rcompute.
      discrR.
      simpl. apply Rgt_not_eq.
      apply (Rlt_le_trans 0 1 (1 + nat_to_R n)).
      prove_sup.
      replace 1 with (1+0) at 1 by Rcompute.
      apply Rplus_le_compat_l.
      apply nonneg_R_nat. }
  rewrite H9, H10.
  apply (Rle_trans _ ((f (Rmean x) + f (Rmean x0)) / 2) _).
  - unfold mid_convex_on_open_a_b in H4.
    specialize (H4 (Rmean x) (Rmean x0)).
    apply H4.
    assert (1 <= length x)%nat.
      { rewrite <- H5.
        replace 1%nat with (1+0)%nat by reflexivity.
        apply plus_le_compat_l, Nat.le_0_l. }
    assert (1 <= length x0)%nat.
      { rewrite <- H6.
        replace 1%nat with (1+0)%nat by reflexivity.
        apply plus_le_compat_l, Nat.le_0_l. }
    assert (forall e : R, (In e x \/ In e x0) -> a < e).
      { intros. apply in_or_app in H13. rewrite <- lxx0 in H13.
        generalize dependent e.
        apply In_all_at_least. assumption. }
    assert (forall e : R, (In e x \/ In e x0) -> e < b).
      { intros. apply in_or_app in H14. rewrite <- lxx0 in H14.
        generalize dependent e.
        apply In_all_at_most. assumption. }
    split; split.
    + apply mean_at_least. assumption.
      apply In_all_at_least. intros.
      apply H13. left. assumption.
    + apply mean_at_most. assumption.
      apply In_all_at_most. intros.
      apply H14. left. assumption.
    + apply mean_at_least. assumption.
      apply In_all_at_least. intros.
      apply H13. right. assumption.
    + apply mean_at_most. assumption.
      apply In_all_at_most. intros.
      apply H14. right. assumption.
  - unfold Rdiv.
    apply Rmult_le_compat_r.
      { left. apply Rinv_0_lt_compat. prove_sup. }
    apply Rplus_le_compat; assumption.
Qed.

(* For some reason the common olympiad statement
statement of jensen's usually only mentions means,
not weighted means, and yet the proof involves the
continuous world of weighted means. the statement
with just means can be proven only from a weaker
midpoint-convex condition and a "Cauchy induction"
spin on regular mathematical induction competitors
should see sometime, so I'm not sure about the reason
for the discrepancy. anyway, this problem only requires
the midpoint-convexity condition. For a human readable
version of the midpoint-convexity proof, I found
https://matthewhr.wordpress.com/2012/11/10/convexity-continuity-and-jensens-inequality/ *)
Theorem n_var_finite_jensen_on_open_a_b :
  forall (n: nat) (a b: R) (l: list R) (f: R -> R),
    ((1 <= n)%nat /\ n = length l /\ all_at_least a l /\ all_at_most b l /\
      mid_convex_on_open_a_b a b f)
    -> f (Rmean l) <= Rmean (map f l).
Proof.
  intros.
  assert (fulfill_n_var_jensen n).
    { apply cauchy_induction.
      - apply one_var_jensen.
      - apply n_var_jensen_implies_2n_var_jensen.
      - apply S_n_var_jensen_implies_n_var_jensen.
      - destruct H. assumption. }
  unfold fulfill_n_var_jensen in H0.
  apply (H0 a b).
  apply H.
Qed.

Theorem finite_jensen_on_open_a_b :
  forall (a b: R) (l: list R) (f: R -> R),
    ((1 <= length l)%nat /\ all_at_least a l /\ all_at_most b l /\
      mid_convex_on_open_a_b a b f)
    -> f (Rmean l) <= Rmean (map f l).
Proof.
  intros.
  apply (n_var_finite_jensen_on_open_a_b (length l) a b).
  split; try split; try split; apply H.
Qed.

(* ACTUAL PROBLEM *)

(* Note the list a_i's in the problem statement is 1-indexed,
but here I'll 0-index them for consistency. *)
Theorem BMO1984_P1 :
  forall (n : nat) (a_i : list R),
  ((2 <= n)%nat /\ (n = length a_i) /\
    all_at_least 0 a_i /\
    (Rlist_sum a_i = 1))
  -> (Rlist_sum (map (fun i => (nth i a_i 0) / (1 + Rsum_skip i a_i)) (seq 0 n)))
        >= (nat_to_R n) / (2 * (nat_to_R n) - 1).
Proof.
  intros.
  destruct H, H0, H1.
  replace (fun i : nat => nth i a_i 0 / (1 + Rsum_skip i a_i))
    with (fun i : nat => nth i a_i 0 / (2 - nth i a_i 0)).
  - assert (mid_convex_on_open_a_b 0 1 (fun x => x / (2-x)))
      by apply x_2x_1_mid_convex.
    remember (fun x : R => x / (2 - x)) as f.
    (* specialize (finite_jensen_on_open_a_b 0 1 a_i f). intros. *)
    assert (f (Rmean a_i) <= Rmean (map f a_i)).
      { apply (finite_jensen_on_open_a_b 0 1).
        split; try split; try split.
        - apply (le_trans 1 2 (length a_i)).
          constructor. constructor.
          rewrite <- H0. assumption.
        - assumption.
        - rewrite <- H2. apply sum_is_max.
          rewrite <- H0. assumption.
          assumption.
        - assumption. }
    assert (Rmean a_i = 1 / nat_to_R n).
      { unfold Rmean, Rdiv. rewrite <- H0.
        apply Rmult_eq_compat_r. assumption. }
    replace (map (fun i : nat => nth i a_i 0 / (2 - nth i a_i 0)) (seq 0 n))
      with (map f a_i).
    + assert (nat_to_R n > 0) as helpful.
        { inversion H. simpl.
          replace (1 + (1 + 0)) with 2 by Rcompute.
          prove_sup.
          apply (Rlt_le_trans _ 1 _); try prove_sup.
          replace 1 with (1+0) at 1 by apply Rplus_0_r.
          apply Rplus_le_compat_l. apply nonneg_R_nat. }
      rewrite H5 in H4.
      unfold Rmean, Rdiv in H4.
      rewrite map_length, <- H0 in H4.
      apply (Rmult_le_compat_r (nat_to_R n)) in H4.
      rewrite Rmult_assoc, Rinv_l, Rmult_1_r in H4.
      apply Rle_ge.
      apply (Rle_trans _ (f (1 * / nat_to_R n) * nat_to_R n) _); try assumption.
      right.
      rewrite Heqf, Rmult_1_l.
      unfold Rdiv.
      replace (/ nat_to_R n * / (2 - / nat_to_R n) * nat_to_R n)
        with (nat_to_R n * (/ nat_to_R n * / (2 - / nat_to_R n))) by apply Rmult_comm.
      apply Rmult_eq_compat_l.
      rewrite <- Rinv_mult_distr.
      f_equal.
      unfold Rminus.
      rewrite Rmult_plus_distr_l.
      symmetry. rewrite <- neg_minus_equiv.
      replace (-1 * / nat_to_R n) with (/ nat_to_R n * - 1) by apply Rmult_comm.
      rewrite <- Rmult_assoc, Rinv_r, Rmult_1_l.
      f_equal. apply Rmult_comm.
      (* bunch of tedious proving nonzero *)
      * apply Rgt_not_eq. assumption.
      * apply Rgt_not_eq. assumption.
      * apply Rgt_not_eq. unfold Rminus.
        replace 0 with (/ nat_to_R n + - / nat_to_R n) by apply Rplus_opp_r.
        apply Rplus_gt_compat_r.
        apply (Rmult_lt_reg_r (nat_to_R n)).
        apply helpful.
        rewrite Rinv_l.
        inversion H. simpl. prove_sup.
        simpl. rewrite Rmult_plus_distr_l.
        apply (Rge_gt_trans _ (2 * 1) _); try prove_sup.
        apply Rle_ge. rewrite <- Rplus_0_r at 1.
        apply Rplus_le_compat_l.
        rewrite <- (Rmult_0_r 2).
        apply Rmult_le_compat_l. left. prove_sup.
        apply nonneg_R_nat.
        apply Rgt_not_eq. assumption.
      * apply Rgt_not_eq. assumption.
      * apply nonneg_R_nat.
    + replace (fun i : nat => nth i a_i 0 / (2 - nth i a_i 0))
        with (fun i : nat => f (nth i a_i 0)).
        rewrite H0.
        rewrite map_erases_seq. reflexivity.
        rewrite Heqf. reflexivity.
  - (* Proving (1 + Rsum_skip i a_i) can be replaced with (2 - nth i a_i 0). *)
    apply functional_extensionality.
    intros.
    unfold Rdiv.
    apply Rmult_eq_compat_l.
    assert (forall a : R, In a a_i -> a < 1).
      { apply In_all_at_most.
        rewrite <- H2.
        apply sum_is_max.
        rewrite H0 in H. assumption.
        assumption. }
    assert (2 - nth x a_i 0 <> 0).
      { destruct (x <? length a_i) eqn:Hx.
        - apply Nat.ltb_lt in Hx.
          assert (In (nth x a_i 0) a_i). apply nth_In. assumption.
          apply H3 in H4.
          apply Rgt_not_eq.
          unfold Rminus.
          replace 0 with (nth x a_i 0 + - nth x a_i 0) at 2 by apply Rplus_opp_r.
          apply Rplus_gt_compat_r.
          apply (Rlt_trans (nth x a_i 0) 1 2).
          assumption. prove_sup.
        - apply Nat.ltb_ge in Hx.
          assert (nth x a_i 0 = 0). apply nth_overflow. assumption.
          rewrite H4. discrR. }
    assert (1 + Rsum_skip x a_i <> 0).
      { assert (0 <= Rsum_skip x a_i).
        apply Rsum_skip_ge_0. assumption.
        apply Rgt_not_eq.
        apply (Rlt_le_trans _ 1 _).
        prove_sup.
        replace 1 with (1 + 0) at 1 by apply Rplus_0_r.
        apply Rplus_le_compat_l. assumption. }
    apply (Rmult_eq_reg_l (2 - nth x a_i 0)); try assumption.
    rewrite Rinv_r; try assumption.
    apply (Rmult_eq_reg_r (1 + Rsum_skip x a_i)); try assumption.
    rewrite Rmult_comm. rewrite Rmult_1_r.
    rewrite Rmult_assoc.
    rewrite <- Rinv_l_sym; try assumption.
    rewrite Rmult_1_r.
    assert (Rsum_skip x a_i = Rlist_sum a_i - nth x a_i 0) by apply Rsum_skip_equiv_nth.
    rewrite H6.
    rewrite H2.
    unfold Rminus.
    rewrite <- Rplus_assoc.
    apply Rplus_eq_compat_r.
    Rcompute.
Qed.

Close Scope R_scope.
