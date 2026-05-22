/-
Copyright (c) 2026 Matthew Cotter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Cotter
-/
module

public import Mathlib.Combinatorics.Colex
import Mathlib
public section

#check Nat.choose

def cascade {n : ℕ} : (Fin n → ℕ) → ℕ :=
    fun h ↦ ∑ i : Fin n, Nat.choose (h i) (i + 1)

theorem multichoose_mono {n j k : ℕ} (hjk : j ≤ k) :
    (n + j).choose (j + 1) ≤ (n + k).choose (k + 1) := by
  rw [le_iff_exists_add] at hjk
  rcases hjk with ⟨a, ha⟩
  rw [ha]
  clear ha
  induction a with
  | zero => rfl
  | succ k hk => exact le_trans hk (Nat.le.intro rfl)

theorem aux {x k n : ℕ} (hx : x.choose (k + 2) ≤ n) : x ≤ n + k + 2 := by
  contrapose! hx
  rw [Nat.lt_iff_add_one_le] at ⊢ hx
  calc
    _ = (n + 1).choose 1 := Eq.symm (Nat.choose_one_right _)
    _ = ((n + 1) + 0).choose (0 + 1) := by norm_num
    _ ≤ ((n + 1) + (k + 1)).choose ((k + 1) + 1) := by apply multichoose_mono; norm_num
    _ ≤ x.choose (k + 2) := by apply Nat.choose_le_choose; omega

example {σ : Type} {n : ℕ} [Preorder σ] (f : Fin (n + 1) → σ) (s : σ) :
    StrictMono (Fin.snoc f s) ↔ StrictMono f ∧ (f (Fin.last n)) < s := by
  constructor <;> intro h
  · rw [Fin.strictMono_iff_lt_succ] at ⊢ h
    constructor
    · intro i
      calc
        _ = (Fin.snoc f s : Fin (n + 1 + 1) → σ) i.castSucc.castSucc := by simp
        _ < (Fin.snoc f s : Fin (n + 1 + 1) → σ) i.castSucc.succ := h _
        _ = f i.succ := by
    · calc
        _ = ((Fin.snoc f s) : Fin (n + 1 + 1) → σ) (Fin.last n).castSucc := by simp
        _ < ((Fin.snoc f s) : Fin (n + 1 + 1) → σ) (Fin.last n).succ := h _
        _ = s := by rw [Fin.castSucc_succ]
  · sorry

/-
have : s = ((Fin.snoc f s) : Fin (n + 1 + 1) → σ) (Fin.last n).succ := by
        simp only [Fin.succ_last, Nat.succ_eq_add_one, Fin.snoc_last]
      have : ((Fin.snoc f s) : Fin (n + 1 + 1) → σ) (Fin.last n).castSucc < s := by
        nth_rw 2 [this]
        apply h
      have : f (Fin.last n) = ((Fin.snoc f s) : Fin (n + 1 + 1) → σ) (Fin.last n).castSucc := by
        simp
      rwa [this]
-/

example (j : ℕ) : ∀ n : ℕ, ∃ h : Fin (j + 1) → ℕ, StrictMono h ∧ cascade h = n := by
  induction j with
  | zero =>
    intro n
    use (fun _ ↦ n)
    unfold cascade StrictMono
    simp
  | succ k hk =>
    intro n
    let A : Set ℕ := {x : ℕ | x.choose (k + 2) ≤ n}
    have : Finite A := Set.Finite.subset (Set.finite_le_nat _) (fun a b ↦ aux b)
    let AFin : Finset ℕ := Set.toFinset A
    have : AFin.Nonempty := ⟨0, by simp [AFin, A]⟩
    let a := Finset.max' AFin this
    rcases hk (n - a.choose (k + 2)) with ⟨c, hc⟩
    use Fin.snoc c a
    constructor
    · sorry
    · unfold cascade
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.val_castSucc, Fin.snoc_last, Fin.val_last]
      rw [← cascade, hc.2]
      apply Nat.sub_add_cancel
      apply Set.mem_toFinset.mp (Finset.max'_mem A.toFinset this)
