/-
Copyright (c) 2026 Matthew Cotter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Cotter
-/
module

public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Tactic

public section

/-- Takes an increasing vector (corresponding to an `n`-set) and returns its cascade
  value. -/
def cascade {n : ℕ} : (Fin n → ℕ) → ℕ :=
    fun h ↦ ∑ i : Fin n, Nat.choose (h i) (i + 1)

/-- Function which picks the largest `j` such that `j.choose k ≤ n`. -/
def BigChoose (n k : ℕ) : ℕ :=
  Nat.findGreatest (fun j ↦ j.choose k ≤ n) (n + k)

/-- Takes a number and returns its Macaulay coefficients as a vector of natural numbers.
 Notably, this will return garbage (the empty vector) when `n = 0`. -/
def unCascade : ∀ j, ℕ → (Fin j → ℕ)
  | 0, _ =>  Fin.elim0
  | k + 1, n =>
    let m := BigChoose n (k + 1)
    Fin.snoc (unCascade k (n - m.choose (k + 1))) m

/-- Big choose `1` is `n`. -/
@[simp]
lemma big_choose_one (n : ℕ) : BigChoose n 1 = n := by
  unfold BigChoose
  simp only [Nat.choose_one_right, add_le_iff_nonpos_right, nonpos_iff_eq_zero, one_ne_zero,
    not_false_eq_true, Nat.findGreatest_of_not, Std.le_refl, Nat.findGreatest_eq]

/-- Cascade of the empty vector is `0`. -/
@[simp]
lemma cascade_elim : cascade (Fin.elim0) = 0 := by
  unfold cascade
  simp only [Finset.univ_eq_empty, Finset.sum_empty]

/-- Inductive definition of cascade. -/
@[simp]
lemma cascade_snoc {n : ℕ} (x : ℕ) (h : Fin n → ℕ) : cascade (Fin.snoc h x) =
    cascade h + x.choose (n + 1) := by
  unfold cascade
  rw [Fin.sum_univ_castSucc]
  simp

/-- Uncascade returns the empty set when `n = 0`. -/
@[simp]
lemma uncascade_zero {k : ℕ} : unCascade 0 k = Fin.elim0 := by rfl

/-- Inductive definition of uncascade. -/
@[simp]
lemma uncascade_succ {k n : ℕ} : unCascade (k + 1) n =
    Fin.snoc (unCascade k (n - (BigChoose n (k + 1)).choose (k + 1))) (BigChoose n (k + 1))
  := by rfl

/-- Multichoose is monotone increasing with respect to the bottom entry. -/
theorem multichoose_mono {n j k : ℕ} (hjk : j ≤ k) :
    (n + j).choose (j + 1) ≤ (n + k).choose (k + 1) := by
  rw [le_iff_exists_add] at hjk
  rcases hjk with ⟨a, ha⟩
  rw [ha]
  clear ha
  induction a with
  | zero => rfl
  | succ k hk => exact le_trans hk (Nat.le.intro rfl)

/-- Big choose does what its supposed to (when `0 ≤ k` it returns the biggest `j` such that blah) -/
theorem big_choose_maximal (n k j : ℕ) : j.choose (k + 1) ≤ n → j ≤ BigChoose n (k + 1) := by
  intro hjch
  have : j ≤ n + k := by
    contrapose! hjch
    rw [Nat.lt_iff_add_one_le] at ⊢ hjch
    calc
      _ = (n + 1).choose 1 := Eq.symm (Nat.choose_one_right _)
      _ = ((n + 1) + 0).choose (0 + 1) := by norm_num
      _ ≤ ((n + 1) + k).choose (k + 1) := multichoose_mono (Nat.zero_le k)
      _ ≤ j.choose (k + 1) := by apply Nat.choose_le_choose; lia
  exact Nat.le_findGreatest (Nat.le_succ_of_le this) hjch

/-- Big choose is less than `n` (also an intended property). -/
theorem big_choose_choose_le (n k : ℕ) : (BigChoose n (k + 1)).choose (k + 1) ≤ n := by
  unfold BigChoose
  let P := (fun j : ℕ ↦ j.choose (k + 1) ≤ n)
  change P _
  apply Nat.findGreatest_spec (Nat.le_add_left 0 _)
  rw [Nat.choose_zero_succ]
  exact zero_le _

/-- Big choose is monotone increasing. -/
theorem big_choose_mono (n m k : ℕ) (hnm : n ≤ m) :BigChoose n (k + 1) ≤ BigChoose m (k + 1) :=
  big_choose_maximal _ _ _ <| le_trans (big_choose_choose_le _ _) hnm

/-
  If I defined everything with straight multichoose then this lemma would be unnecessary,
  but I wanted to do it this way because Kruskal-Katona (maybe?).
-/

/-- Criterion of strict monotonicity of snoc. -/
theorem strict_mono_snoc {σ : Type} {n : ℕ} [Preorder σ] (f : Fin (n + 1) → σ) (s : σ) :
    StrictMono (Fin.snoc f s) ↔ StrictMono f ∧ (f (Fin.last n)) < s := by
  constructor <;> intro h
  · rw [Fin.strictMono_iff_lt_succ] at ⊢ h
    constructor
    · intro i
      calc
        _ = (Fin.snoc f s : Fin (n + 2) → σ) i.castSucc.castSucc := by rw [Fin.snoc_castSucc]
        _ < (Fin.snoc f s : Fin (n + 2) → σ) i.castSucc.succ := h _
        _ = f i.succ := by rw [← Fin.castSucc_succ, Fin.snoc_castSucc]
    · calc
        _ = ((Fin.snoc f s) : Fin (n + 2) → σ) (Fin.last n).castSucc := by rw [Fin.snoc_castSucc]
        _ < ((Fin.snoc f s) : Fin (n + 2) → σ) (Fin.last n).succ := h _
        _ = s := by simp only [Fin.succ_last, Nat.succ_eq_add_one, Fin.snoc_last]
  · rw [Fin.strictMono_iff_lt_succ] at ⊢ h
    intro i
    simp only [Fin.snoc_castSucc]
    cases i using Fin.lastCases with
    | last => simp [h.2]
    | cast j =>
      rw [← Fin.castSucc_succ, Fin.snoc_castSucc]
      apply h.1

/-- Uncascade is strict mono (the greedy algorithm does what we want). -/
theorem uncascade_strict_mono (j : ℕ) : ∀ n, StrictMono (unCascade (j + 1) n) := by
  induction j with
  | zero => unfold StrictMono; simp
  | succ k hk =>
    intro n
    rw [uncascade_succ, strict_mono_snoc]
    constructor
    · exact hk _
    · unfold unCascade
      rw [Fin.snoc_last]
      by_contra!
      let nj := BigChoose n (k + 1 + 1)
      let nj1 := BigChoose (n - (BigChoose n (k + 1 + 1)).choose (k + 1 + 1)) (k + 1)
      have : (nj + 1).choose (k + 2) ≤ nj.choose (k + 2) + nj1.choose (k + 1) := by
        calc
          _ = nj.choose (k + 2) + nj.choose (k + 1) := by
            rw [Nat.choose_succ_succ]
            ring
          _ ≤ nj.choose (k + 2) + nj1.choose (k + 1) :=
            add_le_add (le_refl _) (Nat.choose_mono _ this)
      have : (nj + 1) ≤ nj := by
        apply big_choose_maximal
        calc
          _ ≤ nj.choose (k + 2) + nj1.choose (k + 1) := this
          _ ≤ nj.choose (k + 2) + (n - nj.choose (k + 2)) :=
            add_le_add (le_refl _) (big_choose_choose_le _ _)
          _ = n := Nat.add_sub_of_le (big_choose_choose_le _ _)
      linarith

-- Honestly, it might be easier to prove ts directly, as opposed to using hockey sticks.
/-- Auxiliary identity about choose sums, notably this (should) be an immediate
  consequence of Hockey sticks. -/
theorem aux1 {j m : ℕ} (hm : j ≤ m + 1) :
     ∑ i : Fin j, Nat.choose ((m + i + 1 - j)) (i + 1) + 1 = (m + 1).choose j := by
  induction lt_or_eq_of_le hm with
  | inr h =>
    calc
      _ = ∑ i : Fin j, 0 + 1 := by
        congr
        ext i
        nth_rw 2 [h]
        simp only [Nat.reduceSubDiff, add_tsub_cancel_left, Nat.choose_succ_self]
      _ = (m + 1).choose j := by simp only [Finset.sum_const_zero, zero_add, h, Nat.choose_self]
  | inl _ =>
    calc
      _ = ∑ i : Fin j, Nat.choose (m + i + 1 - j) (i + 1) +
          Nat.choose (m + 0 - j) (0) := by rw [Nat.choose_zero_right]
      _ = ∑ i : Fin (j + 1), Nat.choose (m + i - j) i := by
        rw [Fin.sum_univ_succ, add_comm]
        congr
      _ = ∑ i : Fin (j + 1), Nat.choose (m + i - j) (m - j) := by
        congr 1
        ext i
        rw [← Nat.choose_symm]
        · congr 1
          grind only [#a03e]
        · grind only [#6520]
      _ = ∑ i ∈ Finset.range (j + 1), Nat.choose (m + i - j) (m - j) := by
        exact Eq.symm (Finset.sum_range fun i ↦ (m + i - j).choose (m - j))
      _ =  ∑ i ∈ Finset.range (j + 1), Nat.choose (i + (m- j)) (m - j) := by
        congr
        ext i
        congr 1
        omega
      _ = (m + 1).choose j := by
        rw [Nat.sum_range_add_choose, ← Nat.choose_symm] <;> grind only [#25b6, #d648, #e4b2]

/-- A strictly monotone `(n + 1)`-vector has its `i`th entry plus `n` less than its
  `n`th entry plus `i`. -/
theorem strict_mono_le_fin_last (n : ℕ) (f : Fin (n + 1) → ℕ) (hf : StrictMono f) (i : Fin (n + 1)) :
    f i + n ≤ f (Fin.last n) + i := by
  induction n with
  | zero =>
    simp [show i = 0 by omega]
  | succ k hk =>
    rw [← add_assoc, ← Nat.lt_iff_add_one_le]
    rw [← Fin.snoc_init_self f, strict_mono_snoc] at hf
    cases i using Fin.lastCases with
    | last => simp only [Fin.val_last, add_lt_add_iff_left, lt_add_iff_pos_right, Order.lt_one_iff]
    | cast j =>
      rw [← Fin.snoc_init_self f]
      simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc]
      exact lt_of_le_of_lt (hk (Fin.init f) hf.1 j) (add_lt_add_of_lt_of_le (hf.2) (le_refl _))

/-- A strictly monotone -vector has its `0`th entry plus `i` less than its `i`th entry. -/
theorem init_i_le_of_i (n : ℕ) (f : Fin (n + 1) → ℕ) (hf : StrictMono f) (i : Fin (n + 1)) :
    f 0 + i ≤ f i := by
  induction n with
  | zero => simp [show i = 0 by omega]
  | succ k hk =>
    rw [← Fin.snoc_init_self f, strict_mono_snoc] at hf
    cases i using Fin.lastCases with
    | last =>
      calc
        _ = (Fin.init f) 0 + k + 1 := by
          rw [← Fin.snoc_init_self f, Fin.snoc_apply_zero, Fin.val_last,
            Fin.snoc_init_self, ← add_assoc]
        _ ≤ (Fin.init f) (Fin.last k) + 1 := by
          apply add_le_add ?_ (le_refl _)
          · rcases hk (Fin.init f) hf.1 (Fin.last k) with _
            simpa only
        _ ≤ f (Fin.last (k + 1)) := by
          rw [← Nat.lt_iff_add_one_le]
          exact hf.2
    | cast j =>
      rw [← Fin.snoc_init_self f]
      simp only [Fin.snoc_apply_zero, Fin.val_castSucc, Fin.snoc_castSucc]
      exact hk _ hf.1 _

/-- Cascade will be less than its last entry choose `k` plus one. -/
theorem cascade_le_choose (n : ℕ) (f : Fin (n + 1) → ℕ) (hf : StrictMono f) :
    cascade f < (f (Fin.last n) + 1).choose (n + 1) := by
  unfold cascade
  rw [← aux1, ← Nat.le_iff_lt_add_one]
  · apply Finset.sum_le_sum
    intro i hi
    apply Nat.choose_mono
    calc
      _ = (f i + n) + 1 - (n + 1) := by simp only [Nat.reduceSubDiff, add_tsub_cancel_right]
      _ ≤ f (Fin.last n) + ↑i + 1 - (n + 1) := by
        apply Nat.sub_le_sub_right
        apply Nat.add_le_add ?_ (le_refl _)
        exact strict_mono_le_fin_last _ _ hf _
  apply add_le_add ?_ (le_refl _)
  calc
    _ ≤ f 0 + n := Nat.le_add_left n (f 0)
    _ = f 0 + (Fin.last n) := by rw [Fin.last]
    _ ≤ f (Fin.last n) := init_i_le_of_i _ _ hf _

/-- Big choose cascade returns what we want (first entry in the greedy algorithm). -/
theorem big_choose_cascade (n : ℕ) (f : Fin (n + 1) → ℕ) (hf : StrictMono f) :
    BigChoose (cascade f) (n + 1) = f (Fin.last n) := by
  apply le_antisymm
  · rw [Nat.le_iff_lt_add_one, lt_iff_not_ge]
    exact (Nat.choose_le_choose (n + 1)).mt <| not_le.mpr <|
      lt_of_le_of_lt (big_choose_choose_le _ _) (cascade_le_choose n f hf)
  · have ts : (f (Fin.last n)).choose (n + 1) ≤ cascade f := by
      unfold cascade
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last, le_add_iff_nonneg_left, zero_le]
    exact big_choose_maximal _ _ _ ts

/-- Cascade of uncascade is the identity. -/
theorem cascade_uncascade (j : ℕ) : ∀ n, cascade (unCascade (j + 1) n) = n := by
  induction j with
  | zero =>
    unfold cascade
    intro nsorry
    simp [Fin.snoc_zero]
  | succ k hk =>
    intro n
    rw [uncascade_succ, cascade_snoc, hk]
    exact Nat.sub_add_cancel (big_choose_choose_le _ _)

/-- Uncascade of cascade is the identity when its input is strictly monotone. -/
theorem uncascade_cascade {n : ℕ} (f : Fin n → ℕ) (hf : StrictMono f) :
    unCascade n (cascade f) = f := by
  induction n with
  | zero =>
    rw [uncascade_zero]
    exact List.ofFn_inj.mp rfl
  | succ k hk =>
    rw [uncascade_succ, big_choose_cascade _ _ hf]
    nth_rw 1 [← Fin.snoc_init_self f]
    rw [cascade_snoc, add_tsub_cancel_right, hk, Fin.snoc_init_self]
    exact strictMono_dual_iff.mp fun _ _ a ↦ hf a
