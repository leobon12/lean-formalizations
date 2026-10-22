import HigherDimLQGMetric.DGZ.NondegTight
import HigherDimLQGMetric.DGZ.TightNondegCross

/-!
# Crossing values as continuous functionals of locally uniform metric limits

The set-to-set distance between two compact hypercubic spheres is a continuous functional of
the ambient continuous distance function. This is the portmanteau observable for DGZ Prop 6.4.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped Pointwise

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP

variable {d : ℕ}

/-- The compact set of pairs of points on two hypercubic spheres. -/
def nd_shellPairs (c : Rd d) (r₁ r₂ : ℝ) : Set (Rd d × Rd d) :=
  lsph c r₂ ×ˢ lsph c r₁

theorem nd_isCompact_shellPairs (c : Rd d) (r₁ r₂ : ℝ) :
    IsCompact (nd_shellPairs c r₁ r₂) :=
  (tn_isCompact_lsph c r₂).prod (tn_isCompact_lsph c r₁)

theorem nd_shellPairs_nonempty (hd : 0 < d) (c : Rd d) {r₁ r₂ : ℝ}
    (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂) :
    (nd_shellPairs c r₁ r₂).Nonempty :=
  (lsph_nonempty hd c hr₂).prod (lsph_nonempty hd c hr₁)

/-- Crossing value of a continuous candidate metric, defined even for a pseudometric. -/
def nd_crossPhi (c : Rd d) (r₁ r₂ : ℝ) (D : C(Rd d × Rd d, ℝ)) : ℝ :=
  sInf (D '' nd_shellPairs c r₁ r₂)

theorem nd_continuous_crossPhi (c : Rd d) (r₁ r₂ : ℝ) :
    Continuous (nd_crossPhi c r₁ r₂) :=
  (nd_isCompact_shellPairs c r₁ r₂).continuous_sInf
    (f := fun (D : C(Rd d × Rd d, ℝ)) p => D p) continuous_eval

theorem nd_crossPhi_le (c : Rd d) (r₁ r₂ : ℝ) (D : C(Rd d × Rd d, ℝ))
    {p : Rd d × Rd d} (hp : p ∈ nd_shellPairs c r₁ r₂) :
    nd_crossPhi c r₁ r₂ D ≤ D p :=
  csInf_le ((nd_isCompact_shellPairs c r₁ r₂).image D.continuous).bddBelow
    ⟨p, hp, rfl⟩

theorem nd_exists_crossPhi_eq (hd : 0 < d) (c : Rd d) {r₁ r₂ : ℝ}
    (hr₁ : 0 ≤ r₁) (hr₂ : 0 ≤ r₂) (D : C(Rd d × Rd d, ℝ)) :
    ∃ p ∈ nd_shellPairs c r₁ r₂, nd_crossPhi c r₁ r₂ D = D p := by
  obtain ⟨p, hp, hmin⟩ := (nd_isCompact_shellPairs c r₁ r₂).exists_isMinOn
    (nd_shellPairs_nonempty hd c hr₁ hr₂) D.continuous.continuousOn
  refine ⟨p, hp, le_antisymm (nd_crossPhi_le c r₁ r₂ D hp) ?_⟩
  exact le_csInf ((nd_shellPairs_nonempty hd c hr₁ hr₂).image _)
    (by rintro _ ⟨q, hq, rfl⟩; exact hmin hq)

/-- The continuous crossing observable agrees with normalized LFPP crossing distance. -/
theorem nd_crossPhi_normMetricC {φ : Rd d → ℝ} (hφ : Continuous φ)
    {a : ℝ} (ha : 0 < a) (ξ : ℝ) (c : Rd d) (r₁ r₂ : ℝ) :
    nd_crossPhi c r₁ r₂ (normMetricC ξ φ a) = a⁻¹ * acrossDist ξ φ c r₁ r₂ := by
  have hf : ∀ p : Rd d × Rd d,
      normMetricC ξ φ a p = a⁻¹ * lfppMetric ξ φ p.1 p.2 :=
    normMetricC_apply hφ a
  unfold nd_crossPhi acrossDist lfppSetDist
  change sInf ((normMetricC ξ φ a) '' nd_shellPairs c r₁ r₂) = _
  simp_rw [hf]
  change sInf ((fun p : Rd d × Rd d => a⁻¹ * lfppMetric ξ φ p.1 p.2) ''
    nd_shellPairs c r₁ r₂) =
      a⁻¹ * sInf ((fun p : Rd d × Rd d => lfppMetric ξ φ p.1 p.2) ''
        nd_shellPairs c r₁ r₂)
  have himage :
      ((fun p : Rd d × Rd d => a⁻¹ * lfppMetric ξ φ p.1 p.2) ''
        nd_shellPairs c r₁ r₂) =
      a⁻¹ • ((fun p : Rd d × Rd d => lfppMetric ξ φ p.1 p.2) ''
        nd_shellPairs c r₁ r₂) := by
    ext y
    simp only [Set.mem_image, Set.mem_smul_set]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨lfppMetric ξ φ p.1 p.2, ⟨p, hp, rfl⟩, by simp [smul_eq_mul]⟩
    · rintro ⟨v, ⟨p, hp, rfl⟩, rfl⟩
      exact ⟨p, hp, by simp [smul_eq_mul]⟩
  rw [himage, Real.sInf_smul_of_nonneg (inv_nonneg.2 ha.le)]
  simp only [smul_eq_mul]

end HigherDimLQGMetric.DGZ
