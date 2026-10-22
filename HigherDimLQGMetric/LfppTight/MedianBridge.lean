import HigherDimLQGMetric.LfppTight.MedianPos
import HigherDimLQGMetric.LfppTight.MedianProduct
import HigherDimLFPP.Paths.Compare

/-! Exact scalar split of convolution LFPP and lower-median bookkeeping. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁)

def l6a_convSphereMean {d : ℕ} (κ : Rd d → ℝ) (ε : ℝ) (h : DistRd d) : ℝ :=
  ∫ u, convMollify κ ε h u ∂(unitSphereProb d)

/-- The global sphere mean multiplies every LFPP distance by the same Weyl
factor. -/
theorem l6a_lfppDist_sphereMean_split {d : ℕ}
    (κ : Rd d → ℝ) (ξ ε : ℝ) (h : DistRd d) (p : Rd d × Rd d) :
    lfppDist κ ξ ε h p =
      Real.exp (ξ * l6a_convSphereMean κ ε h) *
        HigherDimLFPP.lfppDistOn ξ (convMollifyNorm κ ε h) univ p.1 p.2 := by
  have hfield : (fun z => convMollify κ ε h z) =
      fun z => convMollifyNorm κ ε h z + l6a_convSphereMean κ ε h := by
    funext z
    simp only [convMollifyNorm, l6a_convSphereMean]
    ring
  rw [lfppDist]
  change HigherDimLFPP.lfppDistOn ξ (fun z => convMollify κ ε h z) univ p.1 p.2 = _
  rw [hfield, HigherDimLFPP.lfppDistOn_add_const]

/-- A quantitative lower-median bridge. Each of the two scalar factors is
outside `[m,M]` with probability at most `1/8`; the normalized LFPP median is
then between `m² a` and `M² a`. -/
theorem l6a_aEps_bounds_of_factor_tails {d : ℕ} (hd : 2 ≤ d)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (ξ : ℝ) {ε : ℝ} (hε : 0 < ε)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P)
    {a m M : ℝ} (ha : 0 < a) (hm : 0 ≤ m) (hM : 0 ≤ M)
    (hA : P {ω | Real.exp (ξ * l6a_convSphereMean κ ε (h ω)) < m ∨
      M < Real.exp (ξ * l6a_convSphereMean κ ε (h ω))} ≤ (8⁻¹ : ℝ≥0∞))
    (hB : P {ω | a⁻¹ * HigherDimLFPP.lfppDistOn ξ
        (convMollifyNorm κ ε (h ω)) univ 0 (e₁ d) < m ∨
      M < a⁻¹ * HigherDimLFPP.lfppDistOn ξ
        (convMollifyNorm κ ε (h ω)) univ 0 (e₁ d)} ≤ (8⁻¹ : ℝ≥0∞)) :
    m ^ 2 * a ≤ aEps κ ξ ε ∧ aEps κ ξ ε ≤ M ^ 2 * a := by
  let A : Ω → ℝ := fun ω => Real.exp (ξ * l6a_convSphereMean κ ε (h ω))
  let B : Ω → ℝ := fun ω => a⁻¹ * HigherDimLFPP.lfppDistOn ξ
    (convMollifyNorm κ ε (h ω)) univ 0 (e₁ d)
  let D : Ω → ℝ := fun ω => lfppDist κ ξ ε (h ω) (0, e₁ d)
  have hD : AEMeasurable D P :=
    l10a_aemeasurable_lfppPoint hd κ hκ ξ P h hh hε
  have hdecomp (ω : Ω) : D ω = A ω * B ω * a := by
    dsimp only [D, A, B]
    rw [l6a_lfppDist_sphereMean_split]
    field_simp [ha.ne']
  have hbad : P {ω | D ω < m ^ 2 * a ∨ M ^ 2 * a < D ω} ≤ (4⁻¹ : ℝ≥0∞) := by
    have hsub : {ω | D ω < m ^ 2 * a ∨ M ^ 2 * a < D ω} ⊆
        {ω | A ω < m ∨ M < A ω} ∪ {ω | B ω < m ∨ M < B ω} := by
      intro ω hw
      by_contra hn
      simp only [mem_union, mem_ofPred_eq, not_or, not_lt] at hn
      obtain ⟨hAm, hAM⟩ := hn.1
      obtain ⟨hBm, hBM⟩ := hn.2
      have hlow : m ^ 2 * a ≤ D ω := by
        rw [hdecomp]
        gcongr
        nlinarith [mul_le_mul hAm hBm hm (le_trans hm hAm)]
      have hupp : D ω ≤ M ^ 2 * a := by
        rw [hdecomp]
        gcongr
        nlinarith [mul_le_mul hAM hBM (le_trans hm hBm) hM]
      exact hw.elim (fun hlt => (not_lt_of_ge hlow) hlt)
        (fun hlt => (not_lt_of_ge hupp) hlt)
    calc
      P {ω | D ω < m ^ 2 * a ∨ M ^ 2 * a < D ω} ≤
          P ({ω | A ω < m ∨ M < A ω} ∪ {ω | B ω < m ∨ M < B ω}) :=
            measure_mono hsub
      _ ≤ P {ω | A ω < m ∨ M < A ω} + P {ω | B ω < m ∨ M < B ω} :=
        measure_union_le _ _
      _ ≤ (8⁻¹ : ℝ≥0∞) + 8⁻¹ := add_le_add hA hB
      _ = (4⁻¹ : ℝ≥0∞) := by
        rw [← ENNReal.ofReal_ofNat 8, ← ENNReal.ofReal_ofNat 4,
          ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 8),
          ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 4),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        norm_num
  rw [l6a_aEps_eq_sample_lowerMedian hd κ hκ ξ hε P h hh,
    l6a_lowerMedian_eq_lowerQuantile_map P D hD]
  exact HigherDimLFPP.Crude.lowerQuantile_mem_Icc_of_measure_le hD
    (by norm_num : (0 : ℝ≥0∞) < 2⁻¹)
    (by norm_num : (2⁻¹ : ℝ≥0∞) < 1)
    (by norm_num : (4⁻¹ : ℝ≥0∞) < 2⁻¹)
    (by norm_num : (4⁻¹ : ℝ≥0∞) ≤ 1 - 2⁻¹) hbad

end HigherDimLQGMetric
