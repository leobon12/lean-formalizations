/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.TwoSeedExistsLevy
import InteractingSLE.Spec.Sec2.TwoSeedLaw
import InteractingSLE.Frozen.Spec.IsIntegratedSLEEvolution

/-!
# Two seeds at `0⁻, 0⁺`: existence of the evolution from a Jacobi diffusion

Packet PROVE-SEC2-JAC3 (Specification L496–L534, the construction in the proof of Theorem 2.2).

* `exists_isIntegratedSLEEvolution_twoSeed_of_jacobi`: if a Jacobi diffusion with parameters
  `κ, ρ_L + 2, ρ_R + 2` exists on the logarithmic clock (`Jacobi.IsJacobiDiffusion`, in some
  filtration on some probability space), then the integrated `SLE_κ(ρ_L; ρ_R)` evolution with one
  force point at `0⁻` and one at `0⁺` exists, in exactly the frozen form of
  `exists_isIntegratedSLEEvolution` (lifetime `⊤`). The Brownian motion is
  `isFilteredBrownianReal_bPath`; the pathwise conditions are the landed
  `isIntegratedSLEPath_twoSeed` applied to the modified (everywhere good) Jacobi path.
* `exists_isIntegratedSLEEvolution_twoSeed_of_jacobiExists`: all weights at once (a weight `≤ -2`
  is the landed `exists_isIntegratedSLEEvolution_twoSeed_of_le`).

The hypothesis is the existence of the Jacobi diffusion itself, a cited external input of the
specification (p. 4, "Bessel/Jacobi diffusion theory"; L498–L506), not a step of this proof.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec2

namespace TwoSeed

open Jacobi

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {κ a b : ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
  {𝓗 : Filtration ℝ mΩ} {U : ℝ → Ω → ℝ}

/-- `phys` of `driver`, `lowerL`, `upperL` along the modified path is adapted before `⊤`. -/
theorem adaptedBefore_phys (hU : IsJacobiDiffusion κ a b P 𝓗 U) (hκ : 0 ≤ κ) (ha : 0 < a)
    (hb : 0 < b) {F : (ℝ → ℝ) → ℝ → ℝ} (hF : ∀ u, Measurable fun f : CPathR => F (clampU f) u)
    (hloc : ∀ (u : ℝ) (f g : ℝ → ℝ), (∀ v ≤ u, f v = g v) → F f u = F g u)
    (hFc : ∀ ω, Continuous fun u => F (modU U · ω) u) :
    AdaptedBefore (physFilt hU hκ ha hb) (fun _ => ⊤)
      (fun t ω => phys (modU U · ω) (F (modU U · ω)) t) := by
  intro t A hA
  have hFa : ∀ u, Measurable[augF 𝓗 P u] fun ω => F (modU U · ω) u := fun u =>
    measurable_pathFun (F := fun f => F f u) (continuous_modU hU) (adapted_modU hU hκ ha hb)
      (modU_mem hU) (hF u) u (hloc u)
  have h := measurable_phys_physFilt hU hκ ha hb hFa hFc t hA
  have e : {ω | ((t : ℝ≥0∞) < ⊤) ∧ phys (modU U · ω) (F (modU U · ω)) t ∈ A} =
      (fun ω => phys (modU U · ω) (F (modU U · ω)) t) ⁻¹' A := by
    ext ω; simp
  rw [e]; exact h

end TwoSeed

open TwoSeed Jacobi

/-- **Theorem 2.2, existence, two seeds at `0⁻, 0⁺`, weights `> -2`, from a Jacobi diffusion.** -/
theorem exists_isIntegratedSLEEvolution_twoSeed_of_jacobi {κ : ℝ} (hκ : 0 < κ)
    {xL xR : Fin 1 → ℝ} (hxL : ∀ i, xL i = 0) (hxR : ∀ i, xR i = 0) {ρL ρR : Fin 1 → ℝ}
    (hρL : -2 < ρL 0) (hρR : -2 < ρR 0)
    (hJ : ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓗 : Filtration ℝ mΩ) (U : ℝ → Ω → ℝ), IsJacobiDiffusion κ (ρL 0 + 2) (ρR 0 + 2) P 𝓗 U) :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin 1 → ℝ≥0 → Ω → ℝ)
      (VR : Fin 1 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ := by
  obtain ⟨Ω, mΩ, P, hP, 𝓗, U, hU⟩ := hJ
  obtain rfl : xL = fun _ => 0 := funext hxL
  obtain rfl : xR = fun _ => 0 := funext hxR
  have ha : 0 < ρL 0 + 2 := by linarith
  have hb : 0 < ρR 0 + 2 := by linarith
  have hρL' : ∀ i, -2 < ρL i := fun i => by rw [Subsingleton.elim i 0]; exact hρL
  have hρR' : ∀ i, -2 < ρR i := fun i => by rw [Subsingleton.elim i 0]; exact hρR
  refine ⟨Ω, mΩ, P, hP, physFilt hU hκ.le ha hb, fun t ω => wPath (modU U · ω) t,
    fun i t ω => vLPath (modU U · ω) i t, fun i t ω => vRPath (modU U · ω) i t,
    fun t ω => bPath κ ρL ρR (modU U · ω) t, fun _ => ⊤, ?_, ?_, ?_, ?_, ?_⟩
  · exact isFilteredBrownianReal_bPath hU hκ ha hb
  · exact adaptedBefore_phys hU hκ.le ha hb (F := driver) measurable_driver
      (fun _ _ _ h => driver_congr h) fun ω =>
        continuous_driver (continuous_modU hU ω) fun v => modU_mem hU v ω
  · exact fun _ => adaptedBefore_phys hU hκ.le ha hb (F := lowerL) measurable_lowerL
      (fun _ _ _ h => lowerL_congr h) fun ω =>
        continuous_lowerL (continuous_modU hU ω) fun v => modU_mem hU v ω
  · exact fun _ => adaptedBefore_phys hU hκ.le ha hb (F := upperL) measurable_upperL
      (fun _ _ _ h => upperL_congr h) fun ω =>
        continuous_upperL (continuous_modU hU ω) fun v => modU_mem hU v ω
  · exact ae_of_all _ fun ω => isIntegratedSLEPath_twoSeed (continuous_modU hU ω)
      (fun v => modU_mem hU v ω) (volume_modU_boundary ω) (tendsto_clock_modU hU ω) hκ hρL' hρR'

/-- **Theorem 2.2, existence, two seeds at `0⁻, 0⁺`, every weight**, given the existence of the
Jacobi diffusion for all positive parameters. -/
theorem exists_isIntegratedSLEEvolution_twoSeed_of_jacobiExists {κ : ℝ} (hκ : 0 < κ)
    (hJ : ∀ a b : ℝ, 0 < a → 0 < b →
      ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
        (𝓗 : Filtration ℝ mΩ) (U : ℝ → Ω → ℝ), IsJacobiDiffusion κ a b P 𝓗 U)
    {xL xR : Fin 1 → ℝ} (hxL : ∀ i, xL i = 0) (hxR : ∀ i, xR i = 0) (ρL ρR : Fin 1 → ℝ) :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin 1 → ℝ≥0 → Ω → ℝ)
      (VR : Fin 1 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ := by
  by_cases hdeg : ρL 0 ≤ -2 ∨ ρR 0 ≤ -2
  · exact exists_isIntegratedSLEEvolution_twoSeed_of_le hxL hxR ρL ρR hdeg
  · push Not at hdeg
    exact exists_isIntegratedSLEEvolution_twoSeed_of_jacobi hκ hxL hxR hdeg.1 hdeg.2
      (hJ _ _ (by linarith [hdeg.1]) (by linarith [hdeg.2]))

end Sec2

end InteractingSLE
