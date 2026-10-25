import SupercriticalLQGUniqueness.Uniqueness.Positivity.Grids.AX11Grid
import Mathlib.Analysis.SpecialFunctions.Pow.Real




 



set_option autoImplicit false
noncomputable section

open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Positivity.Grids

 
def radius (k : ℕ) : ℝ := ((2 : ℝ) ^ k)⁻¹

theorem radius_pos (k : ℕ) : 0 < radius k := by
  unfold radius
  positivity

theorem radius_antitone : Antitone radius := by
  intro i j hij
  unfold radius
  apply inv_anti₀ (by positivity)
  exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hij

theorem mesh_eq_radius (K : ℕ) : mesh K = radius (K + 10) := rfl

theorem near_point_inner (K k : ℕ) (hk : k ≤ K) :
    mesh K < (11 / 20 : ℝ) * radius k := by
  rw [mesh_eq_radius]
  have hr : radius (K + 10) ≤ radius (k + 10) :=
    radius_antitone (by omega)
  have hstep : radius (k + 10) = radius k / 1024 := by
    simp only [radius, pow_succ]
    norm_num
    ring
  have hpos := radius_pos k
  rw [hstep] at hr
  nlinarith

theorem far_point_outer (K : ℕ) (hK : 8 ≤ K) :
    (1 / 15 : ℝ) - mesh K > (4 / 5 : ℝ) * radius (K / 2) := by
  have hδ : mesh K ≤ radius 18 := by
    rw [mesh_eq_radius]
    exact radius_antitone (by omega)
  have hk : 4 ≤ K / 2 := by omega
  have hr : radius (K / 2) ≤ radius 4 := radius_antitone hk
  have hr4 : radius 4 = (1 / 16 : ℝ) := by norm_num [radius]
  have hr18 : radius 18 = (1 / 262144 : ℝ) := by norm_num [radius]
  rw [hr4] at hr
  rw [hr18] at hδ
  linarith

theorem separated_dyadic_annuli (k : ℕ) :
    (4 / 5 : ℝ) * radius (k + 1) < (11 / 20 : ℝ) * radius k := by
  have hr : radius (k + 1) = radius k / 2 := by
    simp only [radius, pow_succ]
    ring
  rw [hr]
  have hp := radius_pos k
  nlinarith

 
def closedCrossingAnnulus (z : ℂ) (k : ℕ) : Set ℂ :=
  {w | (11 / 20 : ℝ) * radius k ≤ dist w z ∧
    dist w z ≤ (4 / 5 : ℝ) * radius k}

theorem crossing_annuli_disjoint (z : ℂ) {k l : ℕ} (hkl : k < l) :
    Disjoint (closedCrossingAnnulus z k) (closedCrossingAnnulus z l) := by
  rw [Set.disjoint_left]
  intro w hwk hwl
  have hlr : radius l ≤ radius (k + 1) := radius_antitone (by omega)
  have hsep := separated_dyadic_annuli k
  have hk := hwk.1
  have hl := hwl.2
  nlinarith

 
theorem far_point_of_opposites {ρ : ℝ} {x y w : ℂ}
    (hxy : 2 * ρ ≤ dist x y) : ρ ≤ dist w x ∨ ρ ≤ dist w y := by
  by_contra h
  push Not at h
  have ht := dist_triangle x w y
  rw [dist_comm x w] at ht
  linarith

 
theorem far_from_grid {ρ δ : ℝ} {w v z : ℂ}
    (hwz : dist w z ≤ δ) (hwv : ρ ≤ dist w v) :
    ρ - δ ≤ dist v z := by
  have ht := dist_triangle w z v
  rw [dist_comm z v] at ht
  linarith

 
theorem opposite_beyond_outer (K k : ℕ) (hK : 8 ≤ K) (hk : K / 2 ≤ k)
    {w v z : ℂ} (hwz : dist w z ≤ mesh K)
    (hwv : (1 / 15 : ℝ) ≤ dist w v) :
    (4 / 5 : ℝ) * radius k < dist v z := by
  have hfar := far_from_grid hwz hwv
  have hnum := far_point_outer K hK
  have hr := radius_antitone hk
  nlinarith

 
theorem paid_cost_ge_c (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : Q ≤ 0)
    (c : ℝ) (hc : 0 < c) (k : ℕ) (H : ℝ) (hH : 0 ≤ H) :
    ENNReal.ofReal c ≤ ENNReal.ofReal
      (c * radius k ^ ((ξ : ℝ) * Q) * Real.exp ((ξ : ℝ) * H)) := by
  have hr0 := radius_pos k
  have hr1 : radius k ≤ 1 := by
    have h := radius_antitone (Nat.zero_le k)
    simpa only [radius, pow_zero, inv_one] using h
  have hpow : 1 ≤ radius k ^ ((ξ : ℝ) * Q) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr0 hr1
      (mul_nonpos_of_nonneg_of_nonpos ξ.2.le hQ)
  have he : 1 ≤ Real.exp ((ξ : ℝ) * H) :=
    Real.one_le_exp (mul_nonneg ξ.2.le hH)
  apply ENNReal.ofReal_le_ofReal
  calc
    c = c * 1 * 1 := by ring
    _ ≤ c * radius k ^ ((ξ : ℝ) * Q) * 1 := by
      gcongr
    _ ≤ c * radius k ^ ((ξ : ℝ) * Q) * Real.exp ((ξ : ℝ) * H) := by
      gcongr

 
theorem low_count_of_good_and_paid {ι : Type*} [DecidableEq ι]
    (I : Finset ι) (good nonneg : ι → Prop)
    [DecidablePred good] [DecidablePred nonneg]
    (hgood : (3 / 4 : ℝ) * I.card ≤ ((I.filter good).card : ℝ))
    (hpaid : (((I.filter fun k => good k ∧ nonneg k).card : ℝ) <
      (1 / 4 : ℝ) * I.card)) :
    (((I.filter nonneg).card : ℝ) < (1 / 2 : ℝ) * I.card) := by
  classical
  let paid := I.filter fun k => good k ∧ nonneg k
  let bad := I.filter fun k => ¬ good k
  have hsub : I.filter nonneg ⊆ paid ∪ bad := by
    intro k hk
    have hkI := (Finset.mem_filter.mp hk).1
    have hkn := (Finset.mem_filter.mp hk).2
    by_cases hkg : good k
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hkI, ⟨hkg, hkn⟩⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hkI, hkg⟩))
  have hcard : (I.filter nonneg).card ≤ paid.card + bad.card :=
    (Finset.card_le_card hsub).trans (Finset.card_union_le paid bad)
  have hpartition : (I.filter good).card + bad.card = I.card := by
    exact I.card_filter_add_card_filter_not good
  have hcardR : (((I.filter nonneg).card : ℝ) ≤ (paid.card : ℝ) + (bad.card : ℝ)) := by
    exact_mod_cast hcard
  have hpartR : (((I.filter good).card : ℝ) + (bad.card : ℝ) = I.card) := by
    exact_mod_cast hpartition
  dsimp [paid] at hcardR
  linarith


end SupercriticalLQGUniqueness.Uniqueness.Positivity.Grids
