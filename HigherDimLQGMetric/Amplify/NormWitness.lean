import HigherDimLQGMetric.Amplify.TrialLocal
import HigherDimLQGMetric.Amplify.Geometry

/-! The part of a regular witness used to start a fine-field trial. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

/-- Normalized internal path length equals normalized metric path length when
the path stays in the open set. -/
theorem amplify_normInt_curveLength (ξ Q : ℝ)
    (D : DistRd d → ContMetric d) (g : DistRd d) (r : ℝ) (z : Rd d)
    (O : Set (Rd d)) (P : ℝ → Rd d)
    (hPc : ContinuousOn P (Icc 0 1)) (hPO : MapsTo P (Icc 0 1) O) :
    curveLengthWith (normInt ξ Q D g r z O) P 0 1 =
      ENNReal.ofReal ((sNorm ξ Q g r z)⁻¹) * (D g).len P 0 1 := by
  unfold normInt
  rw [curveLengthWith_const_mul, (D g).curveLengthWith_internal hPc hPO]

/-- A lower-pair witness supplies the normalized collar and path bounds
needed in the fine-field trial transfer. -/
theorem amplify_wit_normalized_data
    (D Dt : DistRd d → ContMetric d) (ξ Q cs a A₀ ℓ β₀ c1 : ℝ)
    {s : ℝ} (hs : 0 < s) (w : Rd d) (g : DistRd d)
    (hW : g ∈ WitEvent Dt D ξ Q cs⁻¹ a A₀ ℓ β₀ c1⁻¹ s w) :
    (∀ ρ ∈ ({3 * s / 4, 3 * s} : Set ℝ),
      ENNReal.ofReal (4 * max 1 cs⁻¹ * ℓ) <
        amplify_normSetDist ξ Q D g s w
          (ann w (s / 2) (5 * s)) (annCl w s (2 * s)) (Metric.sphere w ρ)) ∧
    ∃ P : ℝ → Rd d, ContinuousOn P (Icc 0 1) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, P t ∈ annCl w s (2 * s)) ∧
      ENNReal.ofReal (ℓ / 2) ≤
        curveLengthWith (normInt ξ Q Dt g s w (ann w (3 * s / 4) (3 * s))) P 0 1 ∧
      curveLengthWith (normInt ξ Q Dt g s w (ann w (3 * s / 4) (3 * s))) P 0 1 ≤
        ENNReal.ofReal ℓ ∧
      ENNReal.ofReal c1⁻¹ *
        curveLengthWith (normInt ξ Q Dt g s w (ann w (3 * s / 4) (3 * s))) P 0 1 <
        normInt ξ Q D g s w (ann w (3 * s / 4) (3 * s)) (P 0) (P 1) := by
  rcases hW with ⟨hReg, P, hPK, hGeo, hLow, hHigh, hRatio⟩
  let sn := sNorm ξ Q g s w
  have hsn : 0 < sn := sNorm_pos ξ Q g hs w
  have hPO : MapsTo P (Icc 0 1) (ann w (3 * s / 4) (3 * s)) :=
    fun t ht => amplify_core_subset_open hs w (hPK t ht)
  have hlen : curveLengthWith
      (normInt ξ Q Dt g s w (ann w (3 * s / 4) (3 * s))) P 0 1 =
      ENNReal.ofReal sn⁻¹ * (Dt g).len P 0 1 :=
    amplify_normInt_curveLength ξ Q Dt g s w _ P hGeo.1 hPO
  refine ⟨?_, P, hGeo.1, hPK, ?_, ?_, ?_⟩
  · intro ρ hρ
    have hc := (hReg.2.2.1 ρ hρ).2
    rw [amplify_normSetDist_eq ξ Q D g hs w] 
    exact (amplify_scale_lower_strict_iff hsn).1 hc
  · rw [hlen]
    exact (amplify_scale_lower_iff hsn).1 hLow
  · rw [hlen]
    exact (amplify_scale_upper_iff hsn).1 hHigh
  · rw [hlen, normInt]
    have hpos : ENNReal.ofReal sn⁻¹ ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (inv_pos.mpr hsn)).ne'
    have hfin : ENNReal.ofReal sn⁻¹ ≠ ⊤ := ENNReal.ofReal_ne_top
    have hscaled := ENNReal.mul_lt_mul_left hpos hfin hRatio
    simpa only [sn, mul_comm, mul_left_comm, mul_assoc] using hscaled

end HigherDimLQGMetric
