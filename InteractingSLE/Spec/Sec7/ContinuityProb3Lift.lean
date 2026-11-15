/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.Assembly2Strong
import InteractingSLE.Spec.Sec2.RestartLaw

/-!
# §7.3: evolutions from a start at which almost every Brownian path is solvable, in every universe

Packet PROVE-RANDRESTART2. The completeness of a force word (`LP.IsCompleteForceWord.{u}`) is a statement about
the evolutions of the word on probability spaces in the universe `u`. To use it at a start `s` realized by a
restart, we need one evolution from `s` in that universe. PROVE-SEC2-PATCH2's Yamada–Watanabe construction
(`exists_isIntegratedSLEEvolution_of_ae_mem`) gives one on `CPath` (universe `0`) when Wiener-almost every
path drives a solution from `s`; this file

* pulls an evolution back along a measure-preserving map (`isIntegratedSLEEvolution_comap`; filtration
  `comapFiltration`), which lifts it to `ULift.{u}`;
* restates the solvability hypothesis with the Wiener measure `Sec2.Restart.wienerPath` on `ℝ≥0 → ℝ`
  (`exists_isIntegratedSLEEvolution_of_ae_wienerPath`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Sec7

namespace RandRestart

open Sec2 Sec2.Assembly Sec2.Restart

section Comap

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}

/-- The filtration pulled back along a measurable map. -/
def comapFiltration (𝓕 : Filtration ℝ≥0 mΩ) (φ : Ω' → Ω) (hφ : Measurable φ) : Filtration ℝ≥0 mΩ' :=
  ⟨fun t => (𝓕 t).comap φ, fun _ _ hst => MeasurableSpace.comap_mono (𝓕.mono hst),
    fun t => (MeasurableSpace.comap_mono (𝓕.le t)).trans hφ.comap_le⟩

theorem comapFiltration_apply (𝓕 : Filtration ℝ≥0 mΩ) (φ : Ω' → Ω) (hφ : Measurable φ) (t : ℝ≥0) :
    comapFiltration 𝓕 φ hφ t = (𝓕 t).comap φ := rfl

/-- Independence of two sub-σ-algebras passes to their pullbacks along a measure-preserving map. -/
theorem indep_comap_of_map_eq {P : Measure Ω} {P' : Measure Ω'} {φ : Ω' → Ω} (hφ : Measurable φ)
    (hP : P'.map φ = P) {m₁ m₂ : MeasurableSpace Ω} (h₁ : m₁ ≤ mΩ) (h₂ : m₂ ≤ mΩ)
    (h : Indep m₁ m₂ P) : Indep (m₁.comap φ) (m₂.comap φ) P' := by
  rw [Indep_iff] at h ⊢
  rintro _ _ ⟨s₁, hs₁, rfl⟩ ⟨s₂, hs₂, rfl⟩
  have e : ∀ s : Set Ω, MeasurableSet[mΩ] s → P' (φ ⁻¹' s) = P s := fun s hs => by
    rw [← hP, Measure.map_apply hφ hs]
  rw [← preimage_inter, e _ ((h₁ _ hs₁).inter (h₂ _ hs₂)), e _ (h₁ _ hs₁), e _ (h₂ _ hs₂)]
  exact h _ _ hs₁ hs₂

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- **Pullback of an evolution along a measure-preserving map.** -/
theorem isIntegratedSLEEvolution_comap {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ) {P' : Measure Ω'} {φ : Ω' → Ω}
    (hφ : Measurable φ) (hP : P'.map φ = P) :
    IsIntegratedSLEEvolution a xL xR ρL ρR P' (comapFiltration 𝓕 φ hφ) (fun t ω => W t (φ ω))
      (fun i t ω => VL i t (φ ω)) (fun j t ω => VR j t (φ ω)) (fun t ω => B t (φ ω))
      (fun ω => ζ (φ ω)) := by
  obtain ⟨⟨hBb, hBa, hBi⟩, hW, hVL, hVR, hpath⟩ := hE
  have hlaw : HasLaw φ P P' := ⟨hφ.aemeasurable, hP⟩
  have hae : ∀ {p : Ω → Prop}, (∀ᵐ ω ∂P, p ω) → ∀ᵐ ω' ∂P', p (φ ω') := fun h =>
    ae_of_ae_map hφ.aemeasurable (hP ▸ h)
  have hAB : ∀ {X : ℝ≥0 → Ω → ℝ}, AdaptedBefore 𝓕 ζ X →
      AdaptedBefore (comapFiltration 𝓕 φ hφ) (fun ω => ζ (φ ω)) (fun t ω => X t (φ ω)) :=
    fun hX t A hA => ⟨_, hX t A hA, rfl⟩
  refine ⟨⟨⟨⟨fun I => (hBb.hasLaw I).comp hlaw⟩, hae hBb.cont⟩, fun t => ?_, fun s t hst => ?_⟩,
    hAB hW, fun i => hAB (hVL i), fun j => hAB (hVR j), hae hpath⟩
  · exact (hBa t).comp (comap_measurable φ)
  · have hm : ∀ r, Measurable (B r) := fun r => (hBa r).mono (𝓕.le r) le_rfl
    have h := indep_comap_of_map_eq hφ hP ((hm t).sub (hm s)).comap_le (𝓕.le s) (hBi s t hst)
    rw [MeasurableSpace.comap_comp] at h
    exact h

end Comap


section Exists

open QuantumZipper.RS

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- **An evolution from a separated start at which Wiener-almost every path is solvable, in any universe**
(PROVE-SEC2-PATCH2's Yamada–Watanabe construction on `CPath`, lifted to `ULift.{u}`). -/
theorem exists_isIntegratedSLEEvolution_of_ae_wienerPath (hsep : ∀ i j, xL i < xR j)
    (hae : ∀ᵐ g ∂wienerPath, enc g ∈ Prod.fst '' CRel a xL xR ρL ρR) :
    ∃ (Ω : Type u) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
      (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ := by
  obtain ⟨Ω₀, mΩ₀, P₀, hP₀, 𝓕₀, B₀, hB₀, hB₀c, -⟩ := OneForce.exists_filteredBrownian
  have hB₀m : ∀ t, Measurable (B₀ t) := fun t => (hB₀.2.1 t).mono (𝓕₀.le t) le_rfl
  set μ : Measure CPath := P₀.map (toCPath B₀ hB₀c) with hμ
  have hcan : IsBrownianReal canonBM μ := isBrownianReal_canonBM hB₀.1.toIsPreBrownianReal hB₀m hB₀c
  have : IsProbabilityMeasure μ := hcan.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  have hpm : Measurable fun (f : CPath) (s : ℝ≥0) => canonBM s f :=
    measurable_pi_iff.2 measurable_canonBM
  have hmap : μ.map (fun (f : CPath) (s : ℝ≥0) => canonBM s f) = wienerPath :=
    map_path_eq_wienerPath hcan.toIsPreBrownianReal hpm
  have hae' : ∀ᵐ f ∂μ, encC f ∈ Prod.fst '' CRel a xL xR ρL ρR := by
    rw [← hmap] at hae
    exact ae_of_ae_map hpm.aemeasurable hae
  obtain ⟨Ω₁, mΩ₁, P₁, hP₁, 𝓕₁, W, VL, VR, B, ζ, hE⟩ :=
    exists_isIntegratedSLEEvolution_of_ae_mem hsep hcan hae'
  have hdown : Measurable (ULift.down : ULift.{u} Ω₁ → Ω₁) := measurable_down
  have hup : Measurable (ULift.up : Ω₁ → ULift.{u} Ω₁) := measurable_up
  refine ⟨ULift.{u} Ω₁, inferInstance, P₁.map ULift.up, ?_, comapFiltration 𝓕₁ ULift.down hdown, _, _, _, _,
    _, isIntegratedSLEEvolution_comap hE hdown ?_⟩
  · exact ⟨by rw [Measure.map_apply hup MeasurableSet.univ, preimage_univ, measure_univ]⟩
  · rw [Measure.map_map hdown hup]
    exact Measure.map_id

end Exists

end RandRestart

end Sec7

end InteractingSLE
