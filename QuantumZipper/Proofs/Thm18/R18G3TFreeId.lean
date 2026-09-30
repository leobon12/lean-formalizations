import QuantumZipper.Proofs.Thm18.R18G3TSplit
import QuantumZipper.Proofs.Thm18.R18G3Free

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18-G3 step 5T: the free-field joint limit with the limit laws of the mixing body

`R18.g3FreeTwoPoint_holds` gives some limit laws `μ', ν'` for the free scheme; T5-J needs the
joint limit with the limit laws `μ, ν` of a given fixed-region mixing body (those that the
per-region transfer carries to scheme `C`). They agree on cylinder events: along `g3Filter` the
marginal cylinder probabilities converge to `μ(s)` by the geometric bound and the mixing body
(`mix_of_geo_fix` with `G = univ`) and to `μ'(s)` by `g3FreeTwoPoint_holds`. Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper
namespace R18

open Thm18Asm

/-- Marginal limit from the mixing body and the geometric bound (`G = univ`). -/
theorem tendsto_of_mix_univ {f : G3Idx → ℝ} {c : ℝ}
    (h : ∀ ε > 0, ∀ᶠ i in g3Filter, |f i - c| ≤ ε) : Tendsto f g3Filter (𝓝 c) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [h (ε / 2) (half_pos hε)] with i hi
  rw [Real.dist_eq]
  linarith

/-- **The free scheme's joint cylinder limit with the limit laws of its mixing body.** -/
theorem g3FreeJointLim_of_body {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {μ ν : Measure LawD}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hbody : G3FixMixBody μ ν (g3PalmLaw γ) (g3X γ) (g3R γ) (g3Uf γ) (g3Vf γ)) :
    ∀ s ∈ lawCyl, ∀ t ∈ lawCyl,
      Tendsto (fun i => (g3PalmLaw γ i).real (g3Uf γ i ⁻¹' s ∩ g3Vf γ i ⁻¹' t)) g3Filter
        (𝓝 (μ.real s * ν.real t)) := by
  intro s hs t ht
  have hG : G3GeoStmt γ := g3GeoStmt_of_tight hγ hγ2 (g3PalmRTightStmt_holds hγ hγ2)
  have hU := mix_of_geo_fix (P := g3PalmLaw γ)
    (fun i => outsideSigmaPalm ℝ gffBase.X i.t₁ i.r₁ i.t₂ i.r₂)
    (fun i => g3X γ i) (measurable_g3X' γ) (fun i => i.t₁) (fun i => i.r₁) (g3Uf γ) s
    measureReal_nonneg (measureReal_le_one_of_prob μ s) hG.1 (hbody.1 s hs)
  have hV := mix_of_geo_fix (P := g3PalmLaw γ)
    (fun i => outsideSigmaPalm ℝ gffBase.X i.t₁ i.r₁ i.t₂ i.r₂)
    (fun i => g3R γ i) (measurable_g3R' γ) (fun i => i.t₂) (fun i => i.r₂) (g3Vf γ) t
    measureReal_nonneg (measureReal_le_one_of_prob ν t) hG.2 (hbody.2 t ht)
  have hmU : Tendsto (fun i => (g3PalmLaw γ i).real (g3Uf γ i ⁻¹' s)) g3Filter
      (𝓝 (μ.real s)) := by
    refine tendsto_of_mix_univ fun ε hε => (hU ε hε).mono fun i hi => ?_
    have := hi univ MeasurableSet.univ
    rwa [inter_univ, probReal_univ, mul_one] at this
  have hmV : Tendsto (fun i => (g3PalmLaw γ i).real (g3Vf γ i ⁻¹' t)) g3Filter
      (𝓝 (ν.real t)) := by
    refine tendsto_of_mix_univ fun ε hε => (hV ε hε).mono fun i hi => ?_
    have := hi univ MeasurableSet.univ
    rwa [inter_univ, probReal_univ, mul_one] at this
  obtain ⟨μ', ν', _, _, hlim⟩ := g3FreeTwoPoint_holds hγ hγ2
  obtain ⟨hJ, hJs, hJt⟩ := hlim s hs t ht
  have e1 : μ'.real s = μ.real s := tendsto_nhds_unique hJs hmU
  have e2 : ν'.real t = ν.real t := tendsto_nhds_unique hJt hmV
  rwa [e1, e2] at hJ

end R18
end QuantumZipper
