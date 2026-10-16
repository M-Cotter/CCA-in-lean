/-
Copyright (c) 2026 Matthew Cotter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Cotter
-/
module

public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Tactic

namespace Macaulay

open Fin

public section

/-- Takes an increasing vector (corresponding to an `n`-set) and returns its value as a sum
  of binomial coefficients. -/
def InvMacaulayExp {n : ℕ} : (Fin n → ℕ) → ℕ :=
    fun h ↦ ∑ i : Fin n, Nat.choose (h i) (i + 1)

/-- Function which picks the largest `j` such that `j.choose k ≤ n`. -/
def BigChoose (n k : ℕ) : ℕ :=
  Nat.findGreatest (fun j ↦ j.choose k ≤ n) (n + k)

/-- Takes a number and returns its Macaulay coefficients as a vector of natural numbers.
 Notably, this will return garbage (the empty vector) when `j = 0`. -/
def MacaulayExp : ∀ j, (k : ℕ) → (Fin j → ℕ)
  | 0, _ =>  Fin.elim0
  | k + 1, n =>
    let m := BigChoose n (k + 1)
    snoc (MacaulayExp k (n - m.choose (k + 1))) m

/-- Big choose `1` is `n`. -/
@[simp]
lemma big_choose_one (n : ℕ) : BigChoose n 1 = n := by simp [BigChoose]

/-- InvMacaulayExp of the empty vector is `0`. -/
@[simp]
lemma InvMacaulayExp_elim : InvMacaulayExp (Fin.elim0) = 0 := by simp [InvMacaulayExp]

@[simp]
lemma InvMacaulayExp_zero {f : Fin 0 → ℕ} : InvMacaulayExp f = 0 := by trivial

@[simp]
lemma InvMacaulayExp_one {f : Fin 1 → ℕ} : InvMacaulayExp f = f 0 := by simp [InvMacaulayExp]

/-- Inductive definition of InvMacaulayExp. -/
@[simp]
lemma InvMacaulayExp_snoc {n : ℕ} (x : ℕ) (h : Fin n → ℕ) :
    InvMacaulayExp (Fin.snoc h x) = InvMacaulayExp h + x.choose (n + 1) := by
  unfold InvMacaulayExp
  rw [Fin.sum_univ_castSucc]
  simp

theorem InvMacaulayExp_succ {n : ℕ} {f : Fin (n + 1) → ℕ} :
    InvMacaulayExp f = InvMacaulayExp (Fin.init f) + Nat.choose (f (Fin.last _)) (n + 1) := by
  unfold InvMacaulayExp
  rw [Fin.sum_univ_castSucc, ← Fin.snoc_init_self f]
  simp

/-- MacaulayExp returns the empty set when `n = 0`. -/
@[simp]
lemma MacaulayExp_zero {k : ℕ} : MacaulayExp 0 k = Fin.elim0 := by rfl

/-- Inductive definition of MacaulayExp. -/
@[simp]
lemma MacaulayExp_succ {k n : ℕ} : MacaulayExp (k + 1) n =
    snoc (MacaulayExp k (n - (BigChoose n (k + 1)).choose (k + 1))) (BigChoose n (k + 1)) := by rfl

/-- Multichoose is monotone increasing with respect to the bottom entry. -/
theorem multichoose_mono {n j k : ℕ} (hjk : j ≤ k) :
    (n + j).choose (j + 1) ≤ (n + k).choose (k + 1) := by
  obtain ⟨a, rfl⟩ := le_iff_exists_add.mp hjk
  clear hjk
  induction a with
  | zero => rfl
  | succ k hk => exact le_trans hk (Nat.le.intro rfl)

/-- Big choose does what its supposed to (when `0 ≤ k` it returns the biggest `j` such that blah) -/
theorem big_choose_maximal {n k j : ℕ} (hj : j.choose (k + 1) ≤ n) : j ≤ BigChoose n (k + 1) := by
  refine Nat.le_findGreatest (Nat.le_succ_of_le ?_) hj
  contrapose! hj
  calc
    _ = ((n + 1) + 0).choose (0 + 1) := by rw [← Nat.choose_one_right n]; norm_num
    _ ≤ ((n + 1) + k).choose (k + 1) := multichoose_mono (Nat.zero_le k)
    _ ≤ j.choose (k + 1) := Nat.choose_le_choose _ (by lia)

/-- Big choose is less than `n` (also an intended property). -/
theorem big_choose_choose_le {n k : ℕ} : (BigChoose n (k + 1)).choose (k + 1) ≤ n := by
  let P := (fun j : ℕ ↦ j.choose (k + 1) ≤ n)
  change P _
  exact Nat.findGreatest_spec (Nat.le_add_left 0 _) <| Nat.choose_zero_succ k ▸ zero_le _

/-- Big choose is monotone increasing. -/
theorem big_choose_mono (n m k : ℕ) (hnm : n ≤ m) :BigChoose n (k + 1) ≤ BigChoose m (k + 1) :=
  big_choose_maximal <| le_trans big_choose_choose_le hnm

lemma strict_mono_init {σ : Type} {n : ℕ} [Preorder σ] {f : Fin (n + 1) → σ} (hf : StrictMono f) :
    StrictMono (init f) := by
  induction n with
  | zero => simp [StrictMono]
  | succ k hk =>
    rw [Fin.strictMono_iff_lt_succ] at hf ⊢
    intro i
    rw [Fin.init, Fin.init, ← succ_castSucc]
    exact hf i.castSucc

/-- Criterion of strict monotonicity of snoc. -/
theorem strict_mono_snoc {σ : Type} {n : ℕ} [Preorder σ] {f : Fin (n + 1) → σ} {s : σ} :
    StrictMono (snoc f s) ↔ StrictMono f ∧ (f (Fin.last n)) < s := by
  constructor <;> intro h
  · constructor
    · have : Fin.init (snoc f s : Fin (n + 2) → σ) = f := by norm_num
      exact this.symm ▸ strict_mono_init h
    · rw [Fin.strictMono_iff_lt_succ] at h
      calc
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

/-- MacaulayExp is strict mono (the greedy algorithm does what we want). -/
@[simp]
theorem MacaulayExp_strict_mono' (j : ℕ) : ∀ n, StrictMono (MacaulayExp (j + 1) n) := by
  induction j with
  | zero => unfold StrictMono; simp
  | succ k hk =>
    intro n
    rw [MacaulayExp_succ, strict_mono_snoc]
    constructor
    · exact hk _
    · unfold MacaulayExp
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
            add_le_add (le_refl _) big_choose_choose_le
          _ = n := Nat.add_sub_of_le big_choose_choose_le
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

/-- InvMacaulayExp will be less than its last entry choose `k` plus one. -/
theorem InvMacaulayExp_lt_choose {n : ℕ} {f : Fin (n + 1) → ℕ} (hf : StrictMono f) :
    InvMacaulayExp f < (f (Fin.last n) + 1).choose (n + 1) := by
  unfold InvMacaulayExp
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

/-- Big choose InvMacaulayExp returns what we want (first entry in the greedy algorithm). -/
theorem big_choose_InvMacaulayExp (n : ℕ) (f : Fin (n + 1) → ℕ) (hf : StrictMono f) :
    BigChoose (InvMacaulayExp f) (n + 1) = f (Fin.last n) := by
  apply le_antisymm
  · rw [Nat.le_iff_lt_add_one, lt_iff_not_ge]
    exact (Nat.choose_le_choose (n + 1)).mt <| not_le.mpr <|
      lt_of_le_of_lt big_choose_choose_le (InvMacaulayExp_lt_choose hf)
  · refine big_choose_maximal ?_
    simp [InvMacaulayExp, Fin.sum_univ_castSucc]

/-- InvMacaulayExp of MacaulayExp is the identity. -/
theorem InvMacaulayExp_MacaulayExp (j : ℕ) : ∀ n, InvMacaulayExp (MacaulayExp (j + 1) n) = n := by
  induction j with
  | zero => simp [InvMacaulayExp, Fin.snoc_zero]
  | succ k hk =>
    intro _
    rw [MacaulayExp_succ, InvMacaulayExp_snoc, hk]
    exact Nat.sub_add_cancel big_choose_choose_le

/-- MacaulayExp of InvMacaulayExp is the identity when its input is strictly monotone. -/
theorem MacaulayExp_InvMacaulayExp {n : ℕ} {f : Fin n → ℕ} (hf : StrictMono f) :
    MacaulayExp n (InvMacaulayExp f) = f := by
  induction n with
  | zero =>
    rw [MacaulayExp_zero]
    exact List.ofFn_inj.mp rfl
  | succ k hk =>
    rw [MacaulayExp_succ, big_choose_InvMacaulayExp _ _ hf]
    nth_rw 1 [← Fin.snoc_init_self f]
    rw [InvMacaulayExp_snoc, add_tsub_cancel_right, hk, Fin.snoc_init_self]
    exact fun _ _ a ↦ hf a

theorem last_lt_implies_InvMacaulayExp_lt {n : ℕ} {f g : Fin (n + 1) → ℕ} (hf : StrictMono f)
    (hfg : f (Fin.last _) < g (Fin.last _)) :
    InvMacaulayExp f < InvMacaulayExp g := calc
  _ < Nat.choose (f (Fin.last n) + 1) (n + 1) := InvMacaulayExp_lt_choose hf
  _ ≤ Nat.choose (g (Fin.last n)) (n + 1) := Nat.choose_mono _ (Nat.add_one_le_iff.mp hfg)
  _ ≤ InvMacaulayExp g := InvMacaulayExp_succ ▸ Nat.le_add_left _ _

lemma Pi.Colex.lt_def {n : ℕ} {s t : Fin n → ℕ} : toColex s < toColex t ↔
  ∃ i, (∀ j > i, s j = t j) ∧ s i < t i := by rfl

/-- Macaulay expansions under colex are an order bijection with the natural numbers. -/
theorem InvMacaulayExp_lt_iff {n : ℕ} {f g : Fin n → ℕ} (hf : StrictMono f) (hg : StrictMono g) :
    InvMacaulayExp f < InvMacaulayExp g ↔ toColex f < toColex g := by
  rw [Pi.Colex.lt_def]
  induction n with
  | zero => simp
  | succ k hk =>
    by_cases hfg : f (Fin.last _) = g (Fin.last _)
    · rw [← Fin.snoc_init_self f, ← Fin.snoc_init_self g, InvMacaulayExp_snoc, InvMacaulayExp_snoc,
        hfg, add_lt_add_iff_right, hk (strict_mono_init hf) (strict_mono_init hg)]
      constructor <;> rintro ⟨x, hx₁, hx₂⟩
      · use (x.castSucc)
        constructor
        · intro i hi
          induction i using Fin.lastCases with
          | cast _ => simp [hx₁ _ hi]
          | last => simp
        · simpa only [Fin.snoc_castSucc]
      · induction x using Fin.lastCases with
        | cast c =>
          use c
          rw [Fin.snoc_castSucc, Fin.snoc_castSucc] at hx₂
          refine ⟨fun i hi ↦ ?_, hx₂⟩
          have := hx₁ i.castSucc (Fin.castSucc_lt_castSucc_iff.mpr hi)
          simpa
        | last => simp at hx₂
    · constructor <;> intro h
      · use Fin.last _
        constructor
        · intro i hi
          grind only [usr Fin.val_last]
        · contrapose! h
          exact le_of_lt <| last_lt_implies_InvMacaulayExp_lt hg <| lt_of_le_of_ne h (Ne.symm hfg)
      · obtain ⟨x, hx₁, hx₂⟩ := h
        rw [show x = Fin.last k by exact Fin.eq_last_of_not_lt fun a ↦ hfg (hx₁ _ a)] at hx₂
        exact last_lt_implies_InvMacaulayExp_lt hf hx₂

theorem MacaulayExp_colex_lt_iff {x y n : ℕ} :
    x < y ↔ toColex (MacaulayExp (n + 1) x) < toColex (MacaulayExp (n + 1) y) := by
  rw [← @InvMacaulayExp_MacaulayExp n x, ← @InvMacaulayExp_MacaulayExp n y, InvMacaulayExp_lt_iff,
      InvMacaulayExp_MacaulayExp, InvMacaulayExp_MacaulayExp]
  · exact MacaulayExp_strict_mono' n x
  · exact MacaulayExp_strict_mono' n y

def Macaulay (k n : ℕ) : ℕ := InvMacaulayExp (1 + MacaulayExp k n)

@[simp]
lemma macaulay_one {n : ℕ} : Macaulay 1 n = 1 + n := by
  simp [Macaulay, InvMacaulayExp]
  trivial

@[simp]
lemma macaulay_zero {n : ℕ} : Macaulay 0 n = 0 := by simp [Macaulay]

lemma macaulay_succ {k n : ℕ} :
    Macaulay (k + 1) n =
    Macaulay k (n - (BigChoose n (k + 1)).choose (k + 1)) + (1 + BigChoose n (k + 1)).choose (k + 1)
    := by
  unfold Macaulay
  change InvMacaulayExp ((fun x ↦ 1 + x) ∘ _) = _
  rw [MacaulayExp_succ, Fin.comp_snoc, InvMacaulayExp_snoc]
  congr 1

end

end Macaulay
