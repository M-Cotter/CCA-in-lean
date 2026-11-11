import Mathlib

-- # Problem 1

variable {G : Type*} [Group G] (H K J : Subgroup G) {g : G} {m n k : ℤ}

open Pointwise

/-- Subgroup structure given to the pointwise product of two subgroups of a group
  `G` when the subgroups commute. -/
def SubgroupFromCommSubgroups (hHK : (H : Set G) * K = K * H) : Subgroup G := {
  carrier := (H : Set G) * K
  mul_mem' := by
    intro a b ⟨h₁, hh₁, k₁, hk₁⟩ ⟨h₂, hh₂, k₂, hk₂⟩
    have : k₁ * h₂ ∈ K * (H : Set G) := ⟨_, hk₁.1, h₂, by simp [hh₂]⟩
    obtain ⟨_, hh₃, _, hk₃⟩ := hHK ▸ this
    refine ⟨_, H.mul_mem hh₁ hh₃, _, K.mul_mem hk₃.1 hk₂.1, ?_⟩
    grind
  one_mem' := ⟨1, one_mem _, 1, by simp⟩
  inv_mem' := by
    intro x ⟨h, hh, k, hk, hx⟩
    simp [hx.symm, hHK]
    refine ⟨k⁻¹, K.inv_mem hk, h⁻¹, H.inv_mem hh, by simp⟩
}

/-- If for two subgroups `H` and `K` we find that `H * K` (in the pointwise
  sense) is a subgroup of `G`, then the two subgroups commute. -/
theorem pointwise_mul_group_comm (hJ : J = (H : Set G) * K) :
    (H : Set G) * K = K * H := by
  ext g
  have hJ₁ : ∀ x : G, x ∈ J ↔ x ∈ (H : Set G) * K := by simp [← hJ]
  constructor
  · intro hg
    obtain ⟨h, hh, k, hk, hg⟩ :=  hJ₁ _ |>.mp (J.inv_mem <| hJ₁ _ |>.mpr hg)
    rw [← inv_eq_iff_eq_inv] at hg
    exact hg ▸ ⟨k⁻¹, K.inv_mem hk, h⁻¹, H.inv_mem hh, by simp⟩
  · intro ⟨h, hh, k, hk, hg⟩
    rw [show g = (1 * h) * (k * 1) by simp [hg], ← hJ]
    apply J.mul_mem <;> rw [hJ₁]
    · exact ⟨1, H.one_mem, h, hh, by simp⟩
    · exact ⟨k, hk, 1, K.one_mem, by simp⟩

-- # Problem 2

/-- For an integer `m`, `g ^ m = 0` if and only if the order of `g` divides `m`. -/
theorem pow_eq_one_iff_orderOf_dvd (hg : 0 < orderOf g) :
     g ^ m = 1 ↔ (orderOf g : ℤ) ∣ m := by
  constructor <;> intro h
  · obtain ⟨j, k, hjk⟩ := exists_gcd_eq_mul_add_mul m (orderOf g)
    have : g ^ (gcd m ↑(orderOf g)) = 1 := by
      simp [hjk, zpow_add, zpow_mul, h]
    have : gcd m ↑(orderOf g) = orderOf g := by
      apply le_antisymm
      · exact Int.le_of_dvd (Int.natCast_pos.mpr hg) (gcd_dvd_right _ _)
      · apply Int.ofNat_le_ofNat_of_le
        apply orderOf_le_of_pow_eq_one <| Int.gcd_pos_iff.mpr _ <;> aesop
    exact Int.gcd_eq_right_iff_dvd (Int.natCast_nonneg _) |>.mp this
  obtain ⟨a, ha⟩ := h
  simp [ha, zpow_mul]

variable {H : Type*} [Group H] (φ : G →* H)

/-- For a group homomorphism `φ : G →* H`, the order of `φ g` divides that of `g`. -/
theorem orderOf_map_dvd_orderOf (hg : 0 < orderOf g) :
    orderOf (φ g) ∣ orderOf g := by
  have hpg : 0 < orderOf (φ g) := by
    rw [@orderOf_pos_iff, isOfFinOrder_iff_pow_eq_one]
    use orderOf g
    simp [hg, ← map_pow]
  apply Mathlib.Tactic.Zify.natCast_dvd _ _ |>.mpr
  apply pow_eq_one_iff_orderOf_dvd hpg |>.mp
  simp [← map_pow]

-- # Problem 3

variable {G : Type*} [AddCommGroup G] (K : AddSubgroup G) (d : G)

/-- Our set for problem `3`. -/
def H₀ : Set G := {x | ∃ k ∈ K, ∃ n : ℤ, x = k + n • d}

/-- Axiliarly lemma about `H`. -/
@[simp] lemma mem_H₀ {x : G} : x ∈ H₀ K d ↔ ∃ k ∈ K, ∃ n : ℤ, x = k + n • d := by simp [H₀]

/-- `H` is a subgroup. -/
def H₀Subgroup : AddSubgroup G := {
  carrier := H₀ K d
  add_mem' := by
    intro a b ⟨k₁, hk₁, n₁, h₁⟩ ⟨k₂, hk₂, n₂, h₂⟩
    exact ⟨k₁ + k₂, add_mem hk₁ hk₂, (n₁ + n₂), by rw [h₁, h₂, add_smul]; abel⟩
  zero_mem' := ⟨0, K.zero_mem, 0, by simp⟩
  neg_mem' := fun {x} ⟨k, hk, n, hx⟩ ↦ ⟨-k, K.neg_mem hk, -n, by simp [hx, add_comm]⟩
}
/-- `K` is contained in `H`. -/
lemma K_subset_H₀ : (K : Set G) ⊆ H₀ K d := fun k hk ↦ ⟨k, hk, 0, by simp⟩

/-- The quotient of `H` by `K` is cyclic with generator (more or less) `d`.-/
theorem H₀_quot_K_cyclic :
    IsAddCyclic ((H₀Subgroup K d) ⧸ (K.addSubgroupOf (H₀Subgroup K d))) := by
  rw [isAddCyclic_iff_exists_zmultiples_eq_top]
  let d₀ : H₀Subgroup K d := ⟨d, ⟨0, K.zero_mem, 1, by simp⟩⟩
  use d₀
  apply eq_top_iff.mpr
  intro x _
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective x
  obtain ⟨k, hk, n, hx⟩ : (x : G) ∈ H₀ K d := x.2
  apply AddSubgroup.mem_zmultiples_iff.mpr
  use n
  rw [← QuotientAddGroup.mk_zsmul _ d₀ n]
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  change ((n • d₀ - x) : G) ∈ K
  simp [hx, d₀, hk]

-- # Problem 4

variable {A : GL (Fin 2) ℝ}

/-- The *set* of positive determinant `2 × 2` real matrices. -/
def P_carrier : Set (GL (Fin 2) ℝ) := {A | A.1.det > 0}

@[simp] lemma mem_P₀ : A ∈ P_carrier ↔ A.1.det > 0 := by trivial

/-- `P` given subgroup structure. -/
def P : Subgroup (GL (Fin 2) ℝ) := {
  carrier := P_carrier
  mul_mem' := by
    intro a b ha hb
    simp only [mem_P₀, Units.val_mul, Matrix.det_mul] at ha hb ⊢
    positivity
  one_mem' := by simp
  inv_mem' := by simp
}

/-- Auxiliarly lemmas. -/
@[simp] lemma mem_P : A ∈ P ↔ A.1.det > 0 := by trivial

@[simp] lemma P_det_pos {p : P} : 0 < p.1.1.det := by aesop

/-- `P` is a normal subgroup. -/
theorem P_normal₁ : P.Normal := by
  apply Subgroup.Normal.mk
  intro p hp g
  simp at hp ⊢
  rwa [mul_comm, ← mul_assoc, inv_mul_cancel₀, one_mul]
  exact Matrix.GeneralLinearGroup.det_ne_zero _

noncomputable
def f : P →* ℝ := {
  toFun := fun p ↦ SignType.sign p.1.1.det
  map_one' := by simp
  map_mul' := by aesop
}

/- If you don't know already Lean uses a type theory, so everything is defined
  relative to a type, in this case we are dealing in the type of Sets of elements
  of `P`, so the universe (`Set.univ P`) is `P` itself (as a set). Actually,
  here `P_carrier` will not work since this will be a set of elements of the
  general linear group of `ℝ ^ 2`, which is slightly worse to deal with. -/

/-- The kernel of `f` is exactly`P`.-/
example : (f.ker : Set P) = Set.univ :=
  Set.univ_subset_iff.mp <| fun x hx ↦ by simp [f]

-- # Problem 5

variable {H G K : Type*} [Group G] [Group H] [Group K] (i : H →* G) (p : G →* K)

lemma i_range_normal  (hip : i.range = p.ker) :i.range.Normal := hip ▸ p.normal_ker

-- I'm not defining the isomorphism.

-- # Problem 6

variable {p q : ℕ} {G : Type*} [Group G] [Finite G] (H : Subgroup G)

-- My Lean client is complaining about some stuff, so I had to introduct this. idk
theorem index_eq_card_div [Finite H] : H.index = Nat.card G / Nat.card H := by
  rw [← Subgroup.card_mul_index H, Nat.mul_div_cancel_left _ Nat.card_pos]

/-- A group `G` of order `p * q ^ 3` with `p < q` is simple. -/
theorem normal_subgroup_from_p_q (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p < q)
      (hG : Nat.card G = p * q ^ 3) :
    ∃ (N : Subgroup G), N.Normal := by
  have hmod := @card_sylow_modEq_one q G _ {out := hq} (Finite.of_fintype _)
  have hdvd := @Sylow.card_dvd_index q G _ {out := hq} (Finite.of_fintype _)
  have : Nat.card (Sylow q G) ∣ p := by
    have := hdvd (@Sylow.nonempty q G _).some
    rw [index_eq_card_div, @Sylow.card_eq_multiplicity G _ _ q {out := hq}, hG] at this
    have hfactor : (p * q ^ 3).factorization q = 3 := by
      simp [hp.ne_zero, hq.ne_zero, hp.factorization, hq.factorization_pow, ne_of_lt hpq]
    simp only [hfactor, hq.pos, pow_succ_pos, Nat.mul_div_left] at this
    exact this
  rw [Nat.dvd_prime hp] at this
  cases this with
  | inl hl =>
    use (@Sylow.nonempty q G _).some
    apply Subgroup.Normal.of_conjugate_fixed
    intro g
    rw [← Sylow.coe_subgroup_smul]
    congr
    apply Fintype.card_le_one_iff.mp (le_of_eq  _)
    rw [Nat.card_eq_fintype_card] at hl
    exact hl
  | inr hr =>
    have := hmod.eq_of_lt_of_lt (hr ▸ hpq) hq.one_lt
    aesop
