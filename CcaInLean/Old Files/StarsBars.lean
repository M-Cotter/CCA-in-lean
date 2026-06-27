import Mathlib

variable {n s : ℕ} {f : Fin (n + 1) → ℕ}

def toMonoInit {n : ℕ} (f : Fin (n + 1) → ℕ) : Fin (n + 1) → ℕ
  | 0 => f 0
  | i => f i - f (i - 1) - 1

@[simp]
lemma toMonoInit_zero : toMonoInit f 0 = f 0 := by rfl

@[simp]
lemma toMonoInit_succ {i : Fin n} : toMonoInit f i.succ = f i.succ - f (i.castSucc) - 1 := by
  rw [show i.castSucc = i.succ - 1 from eq_sub_of_add_eq (by norm_num)]
  rfl

@[simp]
lemma toMonoInit_last {f : Fin (n + 2) → ℕ} :
    toMonoInit f (Fin.last _) = f (Fin.last _) - f (Fin.last _ - 1) - 1 := by simp [toMonoInit]

@[simp]
theorem toMonoInit_snoc :
    toMonoInit (Fin.snoc f s) = Fin.snoc (toMonoInit f) (s - f (Fin.last _) - 1) := by
  ext i
  induction i using Fin.lastCases with
  | cast c =>
    simp only [Fin.snoc_castSucc]
    induction c using Fin.cases with
    | zero => simp
    | succ x =>
      simp only [toMonoInit_succ, Fin.castSucc_succ, Fin.snoc_castSucc]
      rw [← Fin.castSucc_succ, Fin.snoc_castSucc]
  | last =>
    simp [show Fin.last (n + 1) - 1 = (Fin.last n).castSucc
      from (eq_sub_of_add_eq (by norm_num)).symm]

def ofMonoInit (f : Fin (n + 1) → ℕ) : Fin (n + 1) → ℕ :=
  fun i ↦ ∑ j ∈ Finset.Icc 0 i, f j + i

@[simp]
lemma ofMonoInit_one {f : Fin (1) → ℕ} : ofMonoInit f = f 0 := by
  unfold ofMonoInit
  ext i
  simp [show i = 0 by lia]

@[simp]
lemma ofMonoInit_snoc {s : ℕ} {f : Fin (n + 1) → ℕ} :
    ofMonoInit (Fin.snoc f s) = Fin.snoc (ofMonoInit f) (∑ j, f j + s + n + 1) := by
  ext i
  induction i using Fin.lastCases with
  | cast c =>
    simp [ofMonoInit]
    calc
      _ = ∑ j ∈ Finset.image Fin.castSucc (Finset.Icc 0 c), Fin.snoc f s j := by
        simp only [Fin.finsetImage_castSucc_Icc, Fin.castSucc_zero]
      _ = ∑ j ∈ Finset.Icc 0 c, (Fin.snoc f s : Fin (n + 2) → ℕ) (Fin.castSucc j) := by
        rw [Finset.sum_image]
        norm_num
      _ = _ := by simp only [Fin.snoc_castSucc]
  | last =>
    simp only [ofMonoInit, Fin.val_last, Fin.snoc_last]
    rw [← Fin.top_eq_last, ← Fin.bot_eq_zero, Finset.Icc_bot_top, Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
    ring

theorem ofMonoInit_strictMono (f : Fin (n + 1) → ℕ) :
    StrictMono (ofMonoInit f) := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  unfold ofMonoInit
  refine Nat.add_lt_add_of_le_of_lt ?_ (Nat.lt_add_one i.castSucc)
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ ↦ Nat.zero_le (f _))
  exact Finset.Icc_subset_Icc (le_refl _) (Fin.castSucc_le_succ i)

theorem toMonoInit_ofMonoInit (f : Fin (n + 1) → ℕ) :
    toMonoInit (ofMonoInit f) = f := by
  induction n with
  | zero =>
    unfold toMonoInit ofMonoInit
    ext i
    simp only [Nat.reduceAdd, Fin.isValue, Finset.Icc_self, Finset.sum_singleton, Fin.val_eq_zero,
      add_zero, sub_zero, tsub_self, zero_tsub]
    induction i using Fin.cases with
    | succ c => grind only [usr Fin.val_succ]
    | zero => gcongr
  | succ k hk =>
    nth_rw 1 [← Fin.snoc_init_self f]
    rw [ofMonoInit_snoc, toMonoInit_snoc, hk (Fin.init f)]
    ext i
    induction i using Fin.lastCases with
    | cast c =>
      simp only [Fin.snoc_castSucc]
      trivial
    | last =>
      have : ∑ j ∈ Finset.Icc 0 (Fin.last k), Fin.init f j = ∑ j, Fin.init f j := by
        rw [← Fin.top_eq_last, ← Fin.bot_eq_zero, Finset.Icc_bot_top, Fin.sum_univ_castSucc]
      simp [ofMonoInit, this]
      lia

theorem ofMonoInit_toMonoInit {f : Fin (n + 1) → ℕ} (hf : StrictMono f) :
    ofMonoInit (toMonoInit f) = f := by
  induction n with
  | zero =>
    unfold ofMonoInit toMonoInit
    ext i
    induction i using Fin.cases with
    | succ c => grind only [usr Fin.val_succ]
    | zero => simp
  | succ k hk =>
    nth_rw 1 [← Fin.snoc_init_self f]
    rw [toMonoInit_snoc, ofMonoInit_snoc]
    ext i
    have hfi : StrictMono (Fin.init f) := sorry
    induction i using Fin.lastCases with
    | cast c =>
      simp [hk hfi]
      trivial
    | last =>
      simp
      have : ∑ j, toMonoInit (Fin.init f) j + k =
          ofMonoInit (toMonoInit <| Fin.init f) (Fin.last k) := by
        unfold ofMonoInit
        rw [← Fin.top_eq_last, ← Fin.bot_eq_zero, Finset.Icc_bot_top,
          Fin.sum_univ_castSucc, Fin.top_eq_last]
        congr 1
      calc
        _ = ∑ j, toMonoInit (Fin.init f) j + k + (f (Fin.last (k + 1)) -
          Fin.init f (Fin.last k) - 1) + 1 := by lia
        _ = Fin.init f (Fin.last k) + (f (Fin.last (k + 1)) - Fin.init f (Fin.last k) - 1) + 1 := by
          rw [this, hk hfi]
        _ = _ := by
          have : Fin.init f (Fin.last k) < f (Fin.last (k + 1)) := by
            have : Fin.init f (Fin.last k) = f ((Fin.last k).castSucc) :=
              Nat.add_zero (f (Fin.last k).castSucc)
            rw [this]
            apply hf
            norm_num
          lia

/-
lemma lt_def {s t : Fin n → ℕ} : toLex s < toLex t ↔
  ∃ i : Fin n, (∀ j : Fin n, j < i → s j = t j) ∧ (s i) < (t i) := by rfl

example {f g : Fin (n + 1) → ℕ} (hf : StrictMono f) (hfg : toLex f < toLex g) :
    toLex (toMonoInit f) < toLex (toMonoInit g) := by
  rw [lt_def] at hfg ⊢
  obtain ⟨i, hi₁, hi₂⟩ := hfg
  use i
  constructor
  · intro j hj
    induction j using Fin.cases with
    | zero => simp [hi₁ _ hj]
    | succ c =>
      simp only [toMonoInit_succ]
      rw [← hi₁ _ hj, ← hi₁ (c.castSucc) (lt_trans Fin.castSucc_lt_succ hj)]
  · induction i using Fin.cases with
    | zero => rwa [toMonoInit_zero, toMonoInit_zero]
    | succ c =>
      rw [toMonoInit_succ, toMonoInit_succ, hi₁ _ Fin.castSucc_lt_succ]
      have : f c.castSucc = g c.castSucc := hi₁ _ Fin.castSucc_lt_succ
      have : f c.castSucc + 1 ≤ f c.succ := hf (Fin.castSucc_lt_succ)
      lia

example {f g : Fin (n + 1) → ℕ} (hfg : toLex f < toLex g) :
    toLex (ofMonoInit f) < toLex (ofMonoInit g) := by
  rw [lt_def] at hfg ⊢
  obtain ⟨x, hx₁, hx₂⟩ := hfg
  use x
  constructor
  · intro j hj
    unfold ofMonoInit
    congr 1
    exact Finset.sum_congr (rfl) (fun _ hk ↦ hx₁ _ <| lt_of_le_of_lt (Finset.mem_Icc.mp hk).2 hj)
  · unfold ofMonoInit
    have : ∑ j ∈ Finset.Ico 0 x, f j = ∑ j ∈ Finset.Ico 0 x, g j :=
      Finset.sum_congr rfl (fun _ hj ↦ hx₁ _ (Finset.mem_Ico.mp hj).2)
    rwa [Finset.Icc_eq_cons_Ico, Finset.sum_cons, Finset.sum_cons,
      this, add_assoc, add_assoc, Nat.add_lt_add_iff_right]
    exact Fin.zero_le x
-/
