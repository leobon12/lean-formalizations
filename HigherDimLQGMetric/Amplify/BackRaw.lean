import HigherDimLQGMetric.Amplify.BackNorm

/-! Undo the local normalizer in the four return-transfer inequalities. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

/-- The full-field version of inequalities (15). -/
def AmplifyBackEvent (D Dt : ContMetric d) (ξ Q cs c1 ℓ δ s : ℝ)
    (w : Rd d) (H : DistRd d) : Prop :=
  let sn := sNorm ξ Q H s w
  ENNReal.ofReal (Real.exp (-2 * ξ * δ) * (4 * max 1 cs⁻¹ * ℓ) * sn) <
    setDistIn D (ann w (s / 2) (5 * s)) (annCl w s (2 * s))
      (Metric.sphere w (3 * s / 4) ∪ Metric.sphere w (3 * s)) ∧
  ∃ P : ℝ → Rd d, ContinuousOn P (Icc 0 1) ∧
    (∀ τ ∈ Icc (0 : ℝ) 1, P τ ∈ annCl w s (2 * s)) ∧
    ENNReal.ofReal (Real.exp (-2 * ξ * δ) * (ℓ / (2 * c1)) * sn) ≤
      D.internal (ann w (3 * s / 4) (3 * s)) (P 0) (P 1) ∧
    Dt.len P 0 1 ≤ ENNReal.ofReal (Real.exp (2 * ξ * δ) * ℓ * sn) ∧
    Dt.len P 0 1 ≤ ENNReal.ofReal (Real.exp (4 * ξ * δ) * c1) *
      D.internal (ann w (3 * s / 4) (3 * s)) (P 0) (P 1)

/-- Normalized inequalities are equivalent to their raw form after multiplying
by the positive sphere-average scale. -/
theorem amplify_backEvent_of_norm
    (D Dt : DistRd d → ContMetric d) (ξ Q cs c1 ℓ δ : ℝ)
    {s : ℝ} (hs : 0 < s) (w : Rd d) (H : DistRd d)
    (hback :
      ENNReal.ofReal (Real.exp (-2 * ξ * δ) * (4 * max 1 cs⁻¹ * ℓ)) <
        amplify_normSetDist ξ Q D H s w (ann w (s / 2) (5 * s))
          (annCl w s (2 * s))
          (Metric.sphere w (3 * s / 4) ∪ Metric.sphere w (3 * s)) ∧
      ∃ P : ℝ → Rd d, ContinuousOn P (Icc 0 1) ∧
        (∀ τ ∈ Icc (0 : ℝ) 1, P τ ∈ annCl w s (2 * s)) ∧
        ENNReal.ofReal (Real.exp (-2 * ξ * δ) * (ℓ / (2 * c1))) ≤
          normInt ξ Q D H s w (ann w (3 * s / 4) (3 * s)) (P 0) (P 1) ∧
        curveLengthWith (normInt ξ Q Dt H s w (ann w (3 * s / 4) (3 * s))) P 0 1 ≤
          ENNReal.ofReal (Real.exp (2 * ξ * δ) * ℓ) ∧
        curveLengthWith (normInt ξ Q Dt H s w (ann w (3 * s / 4) (3 * s))) P 0 1 ≤
          ENNReal.ofReal (Real.exp (4 * ξ * δ) * c1) *
            normInt ξ Q D H s w (ann w (3 * s / 4) (3 * s)) (P 0) (P 1)) :
    AmplifyBackEvent (D H) (Dt H) ξ Q cs c1 ℓ δ s w H := by
  let O := ann w (3 * s / 4) (3 * s)
  let sn := sNorm ξ Q H s w
  have hsn : 0 < sn := sNorm_pos ξ Q H hs w
  obtain ⟨hcoll, P, hPc, hPK, hlow, hhigh, hratio⟩ := hback
  have hPO : MapsTo P (Icc 0 1) O :=
    fun t ht => amplify_core_subset_open hs w (hPK t ht)
  have hlen : curveLengthWith (normInt ξ Q Dt H s w O) P 0 1 =
      ENNReal.ofReal sn⁻¹ * (Dt H).len P 0 1 :=
    amplify_normInt_curveLength ξ Q Dt H s w O P hPc hPO
  dsimp only [AmplifyBackEvent]
  refine ⟨?_, P, hPc, hPK, ?_, ?_, ?_⟩
  · rw [amplify_normSetDist_eq ξ Q D H hs w] at hcoll
    exact (amplify_scale_lower_strict_iff hsn).2 hcoll
  · exact (amplify_scale_lower_iff hsn).2 hlow
  · exact (amplify_scale_upper_iff hsn).2 (hlen ▸ hhigh)
  · have hsn0 : ENNReal.ofReal sn⁻¹ ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (inv_pos.mpr hsn)).ne'
    have hsnT : ENNReal.ofReal sn⁻¹ ≠ ⊤ := ENNReal.ofReal_ne_top
    apply (ENNReal.mul_le_mul_iff_right hsn0 hsnT).1
    rw [hlen] at hratio
    simpa only [hlen, normInt, mul_left_comm] using hratio

end HigherDimLQGMetric
