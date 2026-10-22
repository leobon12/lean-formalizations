import HigherDimLQGMetric.Amplify.LengthScale
import HigherDimLQGMetric.Amplify.TrialLocal

/-! Unit-scale witness conditions for the joint centered metric law. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace HigherDimLQGMetric

open Set Metric
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

def AmplifyUnitWit (M N : ContMetric d) (U a A₀ ℓ β₀ t : ℝ) : Prop :=
  UnitReg M N U a A₀ ℓ β₀ ∧
  ∃ P : ℝ → Rd d, (∀ τ ∈ Icc (0 : ℝ) 1, P τ ∈ annCl 0 1 2) ∧
    IsGeodIn M (ann 0 (3 / 4) 3) P ∧
    ENNReal.ofReal (ℓ / 2) ≤ M.len P 0 1 ∧
    M.len P 0 1 ≤ ENNReal.ofReal ℓ ∧
    ENNReal.ofReal t * M.len P 0 1 <
      N.internal (ann 0 (3 / 4) 3) (P 0) (P 1)

theorem amplify_scale_upper_strict_iff {s t : ℝ} (hs : 0 < s) {x : ℝ≥0∞} :
    x < ENNReal.ofReal (t * s) ↔
      ENNReal.ofReal s⁻¹ * x < ENNReal.ofReal t := by
  constructor
  · intro h
    have hpos : ENNReal.ofReal s⁻¹ ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (inv_pos.mpr hs)).ne'
    have hfin : ENNReal.ofReal s⁻¹ ≠ ⊤ := ENNReal.ofReal_ne_top
    calc
      ENNReal.ofReal s⁻¹ * x <
          ENNReal.ofReal s⁻¹ * ENNReal.ofReal (t * s) := by
            simpa only [mul_comm] using ENNReal.mul_lt_mul_left hpos hfin h
      _ = ENNReal.ofReal t := amplify_scale_ofReal s t hs
  · exact unscale_lt hs

/-- Reverse the regular-event normalization already present in `ScaledEvent`.
The source witness hypothesis is at a physical center and radius. -/
theorem amplify_unitReg_of_regEvent (ξ Q U a A₀ ℓ β₀ : ℝ)
    (A B : DistRd d → ContMetric d) (X : DistRd d)
    {r : ℝ} (hr : 0 < r) (z : Rd d)
    (hreg : X ∈ RegEvent A B ξ Q U a A₀ ℓ β₀ r z) :
    UnitReg
      (weakScaledMetric ξ A (fun t => t ^ (ξ * Q)) X hr z
        (Real.rpow_pos_of_pos hr _))
      (weakScaledMetric ξ B (fun t => t ^ (ξ * Q)) X hr z
        (Real.rpow_pos_of_pos hr _)) U a A₀ ℓ β₀ := by
  let sn := sNorm ξ Q X r z
  have hsn : 0 < sn := sNorm_pos ξ Q X hr z
  rcases hreg with ⟨hAcross, hDiam, hCollar, hMod⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [sharpScaled_coreAcross]
    exact (amplify_scale_lower_iff hsn).1 hAcross
  · rw [sharpScaled_coreDiameter]
    exact (amplify_scale_upper_iff hsn).1 hDiam
  · intro ρ hρ
    have hcase : ρ = 3 / 4 ∨ ρ = 3 := by
      simpa only [mem_insert_iff, mem_singleton_iff] using hρ
    rcases hcase with rfl | rfl
    · obtain ⟨ha, hb⟩ := hCollar (3 * r / 4) (by simp)
      rw [sharpScaled_collarDistance, sharpScaled_collarDistance]
      constructor
      · convert (amplify_scale_lower_strict_iff hsn).1 ha using 1; all_goals (try ring; try ac_rfl)
      · convert (amplify_scale_lower_strict_iff hsn).1 hb using 1; all_goals (try ring; try ac_rfl)
    · obtain ⟨ha, hb⟩ := hCollar (3 * r) (by simp)
      rw [sharpScaled_collarDistance, sharpScaled_collarDistance]
      constructor
      · convert (amplify_scale_lower_strict_iff hsn).1 ha using 1; all_goals (try ring; try ac_rfl)
      · convert (amplify_scale_lower_strict_iff hsn).1 hb using 1; all_goals (try ring; try ac_rfl)
  · intro u hu v hv huv
    have himage : (fun x : Rd d => r • x + z) '' annCl 0 1 2 =
        annCl z r (2 * r) := by
      convert image_annCl_affine hr z 1 2 using 1; all_goals ring
    have hu' : r • u + z ∈ annCl z r (2 * r) := by
      rw [← himage]
      exact ⟨u, hu, rfl⟩
    have hv' : r • v + z ∈ annCl z r (2 * r) := by
      rw [← himage]
      exact ⟨v, hv, rfl⟩
    have hnorm : ‖(r • u + z) - (r • v + z)‖ ≤ β₀ * r := by
      rw [show (r • u + z) - (r • v + z) = r • (u - v) by module,
        norm_smul, Real.norm_eq_abs, abs_of_pos hr]
      nlinarith
    have hm := hMod _ hu' _ hv' hnorm
    rw [sharpScaledMetric_internal, image_ann_affine hr z] 
    convert (amplify_scale_upper_strict_iff hsn).1 hm using 1; all_goals (try ring; try ac_rfl)

end HigherDimLQGMetric
