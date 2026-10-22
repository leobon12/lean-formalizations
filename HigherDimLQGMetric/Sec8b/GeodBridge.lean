import HigherDimLQGMetric.Sec8.Geod

/-! A constant-speed selected geodesic is a geodesic for the real-interval trap API. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set unitInterval
open HigherDimLFPP (Rd)
open LQGMetric.MetricGeometry

variable {d : ℕ}

/-- Restrict the selected path to the real unit interval using the standard projection. -/
def s7b_realPath (η : C(unitInterval, Rd d)) (t : ℝ) : Rd d :=
  η (projIcc 0 1 zero_le_one t)

theorem s7b_realPath_zero (η : C(unitInterval, Rd d)) : s7b_realPath η 0 = η 0 := by
  simp [s7b_realPath]

theorem s7b_realPath_one (η : C(unitInterval, Rd d)) : s7b_realPath η 1 = η 1 := by
  simp [s7b_realPath]

theorem s7b_realPath_coe (η : C(unitInterval, Rd d)) (t : unitInterval) :
    s7b_realPath η (t : ℝ) = η t := by
  simp [s7b_realPath, projIcc_of_mem _ t.property]

/-- Port of the generic metric-geodesic length argument used by GaussianLQG. -/
theorem s7b_constSpeed_isGeod (D : ContMetric d) (x y : Rd d)
    (η : C(unitInterval, Rd d)) (hη : IsConstSpeedGeod D x y η) :
    IsGeod D (s7b_realPath η) := by
  have hcont : Continuous (s7b_realPath η) :=
    η.continuous.comp continuous_projIcc
  have hL : 0 ≤ D.1 (x, y) := D.nonneg x y
  let C : NNReal := ⟨D.1 (x, y), hL⟩
  have hdist : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      edist (D.pt (s7b_realPath η s)) (D.pt (s7b_realPath η t)) =
        ENNReal.ofReal (|s - t| * D.1 (x, y)) := by
    intro s hs t ht
    have hs' : projIcc 0 1 zero_le_one s = (⟨s, hs⟩ : unitInterval) := by
      apply Subtype.ext
      simp [projIcc_of_mem _ hs]
    have ht' : projIcc 0 1 zero_le_one t = (⟨t, ht⟩ : unitInterval) := by
      apply Subtype.ext
      simp [projIcc_of_mem _ ht]
    simp only [s7b_realPath, hs', ht', ContMetric.edist_pt, hη.2.2]
  have hlen : D.len (s7b_realPath η) 0 1 = ENNReal.ofReal (D.1 (x, y)) := by
    have hlen_le : D.len (s7b_realPath η) 0 1 ≤ ENNReal.ofReal (D.1 (x, y)) := by
      have hlip : LipschitzOnWith C
          (D.pt ∘ s7b_realPath η) (Icc (0 : ℝ) 1) := by
        intro s hs t ht
        simp only [Function.comp_apply]
        rw [hdist s hs t ht, edist_dist, Real.dist_eq]
        have hC : (C : ENNReal) = ENNReal.ofReal (D.1 (x, y)) := by
          rw [ENNReal.coe_nnreal_eq]
          rfl
        rw [hC, ENNReal.ofReal_mul (abs_nonneg _)]
        simpa only [mul_comm] using (le_refl
          (ENNReal.ofReal |s - t| * ENNReal.ofReal (D.1 (x, y))))
      change eVariationOn (D.pt ∘ s7b_realPath η) (Icc (0 : ℝ) 1) ≤ _
      calc
        eVariationOn (D.pt ∘ s7b_realPath η) (Icc (0 : ℝ) 1) =
            eVariationOn ((D.pt ∘ s7b_realPath η) ∘ id) (Icc 0 1) := rfl
        _ ≤ (C : ENNReal) * eVariationOn id (Icc 0 1) :=
          hlip.comp_eVariationOn_le (mapsTo_id _)
        _ = ENNReal.ofReal (D.1 (x, y)) := by
          rw [eVariationOn_id_Icc]
          rw [ENNReal.coe_nnreal_eq]
          simp [C]
          rfl
    have hlen_ge : ENNReal.ofReal (D.1 (x, y)) ≤ D.len (s7b_realPath η) 0 1 := by
      simpa [s7b_realPath_zero, s7b_realPath_one, hη.1, hη.2.1] using
        D.ofReal_le_len (s7b_realPath η) zero_le_one
    exact le_antisymm hlen_le hlen_ge
  exact ⟨hcont.continuousOn, by simpa [s7b_realPath_zero, s7b_realPath_one,
    hη.1, hη.2.1] using hlen⟩

end HigherDimLQGMetric
