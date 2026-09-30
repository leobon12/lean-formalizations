import QuantumZipper.Proofs.Thm18.G3GeoCore
import Mathlib.Probability.Distributions.Exponential

/-!
# G3-GEO, part 2: the Palm tail bound

The Palm law of the concrete G3 scheme (`G3Concrete.lean`) is
`g3PalmLaw = (P₀ ⊗ Exp 1).withDensity (g3W)` with `g3W = Z⁻¹ · e^ℓ 1{0 < ℓ ≤ ν[−δ,0]}`.
Since `Exp 1` has density `e^{−ℓ}`, the `e^ℓ` cancels the exponential density and the Palm tail
bound becomes an elementary computation (`lintegral_expMeasure_palmKernel`, `G3FidMass.lean`).
Combined with the deterministic containment `g3Bad_subset_mass` (`G3GeoCore.lean`):

`g3PalmLaw_bad_le`: for `0 < g3Z < ⊤` and `m' < η/4`,
`P(x has left the region-1 half-disc by margin m') ≤ Z⁻¹ · E[(ν₁+ν₀)[−(3η/4+m'), 0]]`.

This is the Palm estimate behind the `x`-half of `G3GeoStmt`: the right-hand side is the Palm
average of `(ν₁+ν₀)[−a, 0]` with `a = 3η/4 + m' → 0` as `η → 0` (with `δ` fixed), so it can be
made small by taking `η` small — the residual input is the vanishing of `E ν_h[−a, 0]` as
`a ↓ 0` (no atom of `ν_h` at `0`, F2/`G3FidMass`, plus the finiteness of `E ν_h[−δ, 0]`, F3
`G3HonestFinStmt`). Own elementary arguments (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

local notation "Ω₀" => gffBase.Ω

/-- **Palm tail bound.** For `0 < g3Z < ⊤` (so the Palm measure is the normalised weight
`Z⁻¹ e^ℓ 1{0 < ℓ ≤ m[−δ,0]}` against `P₀ ⊗ Exp 1`) and `m' < η/4`,

`P(bad) ≤ Z⁻¹ · E[(ν₁+ν₀)[−(3η/4+m'), 0]]`,  `bad = {p : r₁ ≤ |g3X p − t₁| + m'}`. -/
theorem g3PalmLaw_bad_le (γ : ℝ) (i : G3Idx) {m' : ℝ} (hmη : m' < i.η / 4)
    (hZ : 0 < g3Z γ i ∧ g3Z γ i < ⊤) :
    g3PalmLaw γ i {p : Ω₀ × ℝ | i.r₁ ≤ |g3X γ i p - i.t₁| + m'} ≤
      (g3Z γ i)⁻¹ * ∫⁻ ω, (g3ν₁ γ i ω + g3ν₀ γ i ω) (Icc (-(3 * i.η / 4 + m')) 0) ∂gffBase.P := by
  haveI : IsProbabilityMeasure gffBase.P := gffBase.prob
  haveI : IsProbabilityMeasure L₀ := isProbabilityMeasure_expMeasure one_pos
  set B : Set (Ω₀ × ℝ) := {p | i.r₁ ≤ |g3X γ i p - i.t₁| + m'} with hBdef
  set md : Ω₀ → ℝ≥0∞ := fun ω => (g3ν₁ γ i ω + g3ν₀ γ i ω) (Icc (-(3 * i.η / 4 + m')) 0)
    with hmddef
  have hg3Xm : Measurable (g3X γ i) := (measurable_g3X γ i).mono (sig_le_g3 i _ _) le_rfl
  have hBm : MeasurableSet B := by
    rw [hBdef]
    exact measurableSet_le measurable_const
      ((continuous_abs.measurable.comp (hg3Xm.sub measurable_const)).add measurable_const)
  have hmdm : Measurable md := by
    rw [hmddef]
    exact (Measure.measurable_coe measurableSet_Icc).comp ((measurable_g3sum₁ γ i).mono
      (sup_le (localSigma_le gffBase.gff i.t₁ i.r₁)
        (outsideSigma2_le gffBase.gff i.t₁ i.r₁ i.t₂ i.r₂)) le_rfl)
  have hg3W0m : Measurable (g3W0 γ i) := (measurable_g3W0 γ i).mono (sig_le_g3 i _ _) le_rfl
  have hfm : Measurable fun p : Ω₀ × ℝ =>
      (if ENNReal.ofReal p.2 ≤ md p.1 then g3W0 γ i p else 0) :=
    Measurable.ite (measurableSet_le (ENNReal.measurable_ofReal.comp measurable_snd)
      (hmdm.comp measurable_fst)) hg3W0m measurable_const
  -- the pointwise bound on the bad set
  have hpt : ∀ p ∈ B, (g3W γ i p : ℝ≥0∞) ≤
      (g3Z γ i)⁻¹ * (if ENNReal.ofReal p.2 ≤ md p.1 then g3W0 γ i p else 0) := by
    intro p hp
    have hcoe : ((g3W γ i p : ℝ≥0) : ℝ≥0∞) = (g3Z γ i)⁻¹ * g3W0 γ i p := by
      unfold g3W; rw [if_pos hZ]
      exact ENNReal.coe_toNNReal (ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hZ.1.ne')
        (g3W0_ne_top γ i p))
    by_cases h : ENNReal.ofReal p.2 ≤ md p.1
    · rw [if_pos h, hcoe]
    · rw [if_neg h]
      have hnot : ¬ ENNReal.ofReal p.2 ≤ g3Mass γ i p.1 :=
        fun hle => h (g3Bad_subset_mass γ i hmη ⟨hp, hle⟩)
      have hz : g3W0 γ i p = 0 := by
        unfold g3W0
        rw [if_neg (fun hc => hnot hc.2)]
      rw [hcoe, hz, mul_zero]
  -- the length integral: `∫ (1{ℓ ≤ c} · W0) ≤ ∫ c`
  have hkey : ∫⁻ p, (if ENNReal.ofReal p.2 ≤ md p.1 then g3W0 γ i p else 0)
      ∂(gffBase.P.prod L₀) ≤ ∫⁻ ω, md ω ∂gffBase.P := by
    rw [lintegral_prod _ hfm.aemeasurable]
    refine lintegral_mono fun ω => ?_
    have hstep : ∀ ℓ : ℝ, (if ENNReal.ofReal ℓ ≤ md ω then g3W0 γ i (ω, ℓ) else 0) ≤
        (if 0 < ℓ ∧ ENNReal.ofReal ℓ ≤ md ω then ENNReal.ofReal (Real.exp ℓ) else 0) := by
      intro ℓ
      by_cases h : ENNReal.ofReal ℓ ≤ md ω
      · rw [if_pos h]
        by_cases h0 : 0 < ℓ
        · by_cases h1' : ENNReal.ofReal ℓ ≤ g3Mass γ i ω
          · rw [if_pos ⟨h0, h⟩]
            have hz : g3W0 γ i (ω, ℓ) = ENNReal.ofReal (Real.exp ℓ) := by
              unfold g3W0; exact if_pos ⟨h0, h1'⟩
            rw [hz]
          · rw [if_pos ⟨h0, h⟩]
            have hz : g3W0 γ i (ω, ℓ) = 0 := by
              unfold g3W0; exact if_neg (fun hc => h1' hc.2)
            rw [hz]
            exact bot_le
        · rw [if_neg (fun hc => h0 hc.1)]
          have hz : g3W0 γ i (ω, ℓ) = 0 := by
            unfold g3W0; exact if_neg (fun hc => h0 hc.1)
          rw [hz]
      · rw [if_neg h]
        exact bot_le
    calc ∫⁻ ℓ, (if ENNReal.ofReal ℓ ≤ md ω then g3W0 γ i (ω, ℓ) else 0) ∂L₀
        ≤ ∫⁻ ℓ, (if 0 < ℓ ∧ ENNReal.ofReal ℓ ≤ md ω then
            ENNReal.ofReal (Real.exp ℓ) else 0) ∂L₀ := lintegral_mono hstep
      _ = md ω := lintegral_expMeasure_palmKernel (md ω)
  calc g3PalmLaw γ i B
      = ∫⁻ p in B, (g3W γ i p : ℝ≥0∞) ∂(gffBase.P.prod L₀) := by
        rw [g3PalmLaw, withDensity_apply _ hBm]
    _ ≤ ∫⁻ p in B, (g3Z γ i)⁻¹ *
          (if ENNReal.ofReal p.2 ≤ md p.1 then g3W0 γ i p else 0) ∂(gffBase.P.prod L₀) := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem hBm] with p hp
        exact hpt p hp
    _ ≤ ∫⁻ p, (g3Z γ i)⁻¹ *
          (if ENNReal.ofReal p.2 ≤ md p.1 then g3W0 γ i p else 0) ∂(gffBase.P.prod L₀) := by
        simpa only [Measure.restrict_univ] using lintegral_mono_set (Set.subset_univ B)
    _ = (g3Z γ i)⁻¹ * ∫⁻ p, (if ENNReal.ofReal p.2 ≤ md p.1 then g3W0 γ i p else 0)
          ∂(gffBase.P.prod L₀) := lintegral_const_mul _ hfm
    _ ≤ (g3Z γ i)⁻¹ * ∫⁻ ω, md ω ∂gffBase.P := mul_le_mul_of_nonneg_left hkey bot_le
    _ = (g3Z γ i)⁻¹ * ∫⁻ ω, (g3ν₁ γ i ω + g3ν₀ γ i ω) (Icc (-(3 * i.η / 4 + m')) 0)
          ∂gffBase.P := rfl

end Thm18Asm
end QuantumZipper
