/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondStagedKillTrace

/-!
# Proposition 5.9's killed stage law from the conditional law of the piece

Packet PROVE-STAGED8. The cross-conditioning chain delivers a stage piece through its **conditional law** given the
past (a word entrance under the regular conditional law, continued to an integrated evolution). This file converts
that law form into the comparison forms consumed by PROVE-PROP59T2's experiment:

* `pieceSamp`, `farSamp`: the killed rational-time samples of a piece (killed at its own lifetime) and of an
  evolution (killed at its first far contact, `farLife`);
* `HasKilledRep`: a law `ν` on samples is the killed-sample law of some integrated evolution from `y₀` on a
  probability space in `Type`, with an almost surely existing generating trace up to a chosen horizon (`true`: the
  whole lifetime, as `CompPremiseFar` demands; `false`: the killed lifetime `farLife` only, as `CompPremiseFarK`
  demands);
* **`isStageLawFar_of_condLaw`**: if, for almost every past sample `ω₀` of the stage event, the law of the piece's
  samples under `condExpKernel P 𝓠 ω₀` is the killed-sample law of a traced integrated evolution from `y ω₀`, the
  stage obeys `IsStageLawFar`; **`isStageLawFarK_of_condLaw`**: the same with traces up to the kill, giving
  `IsStageLawFarK`;
* `hasKilledRep_of_ae_eq`: the representation on the conditional law's own space, from an evolution whose killed
  samples agree almost surely with the piece's.

The disintegration follows PROVE-PROP59T3's `Prop59Stage.isStageLaw_of_isRandomWordEvolution`: the premise bounds the
conditional probability of the Borel event from below at almost every `ω₀`, the start is fixed by the conditional law
(`Sec7.Aux122Disint.ae_ae_condExpKernel_eq`), and integrating over a past event `A ⊆ R`
(`KernelTower.setLIntegral_condExpKernel`) gives `p P(A) ≤ P(A ∩ {(start, samples) ∈ S})`.

Conditional helpers with distinct names; they replace no source theorem. R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CrossCond.StagedKill

open Prop59Stage Prop59Nodes Sec7.Aux122Disint

/-! ### Killed samples and their representations -/

section Rep

variable {nL nR : ℕ}

/-- The rational-time samples of a piece killed at its own lifetime `ζ`. -/
abbrev pieceSamp {Ω : Type*} (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (ζ : Ω → ℝ≥0∞) (ω : Ω) : Samp nL nR :=
  samp (W · ω) (fun i t => VL i t ω) (fun k t => VR k t ω) (ζ ω)

/-- The rational-time samples of an evolution killed at its first far contact. -/
abbrev farSamp {Ω : Type*} (iL : Fin nL) (iR : Fin nR) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω) : Samp nL nR :=
  samp (W · ω) (fun i t => VL i t ω) (fun k t => VR k t ω)
    (farLife iL iR (W · ω) (fun i t => VL i t ω) (fun k t => VR k t ω) (ζ ω))

/-- The trace horizon of an evolution: its whole lifetime (`full = true`) or its killed lifetime `farLife`
(`full = false`). -/
def traceHorizon {Ω : Type*} (full : Bool) (iL : Fin nL) (iR : Fin nR) (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω) : ℝ≥0∞ :=
  if full then ζ ω else farLife iL iR (W · ω) (fun i t => VL i t ω) (fun k t => VR k t ω) (ζ ω)

/-- **A killed-sample law represented by a traced evolution**: `ν` is the law of the samples, killed at the first far
contact, of an integrated `SLE_κ(ρ)` evolution from `y₀` (on a probability space in `Type`) whose generating trace
exists almost surely up to the horizon `traceHorizon full`. -/
def HasKilledRep (κ : ℝ) (full : Bool) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (iL : Fin nL) (iR : Fin nR)
    (y₀ : Start nL nR) (ν : Measure (Samp nL nR)) : Prop :=
  ∃ (Ω' : Type) (mΩ' : MeasurableSpace Ω') (P' : Measure Ω') (_ : IsProbabilityMeasure P')
    (𝓕' : Filtration ℝ≥0 mΩ') (W' : ℝ≥0 → Ω' → ℝ) (VL' : Fin nL → ℝ≥0 → Ω' → ℝ)
    (VR' : Fin nR → ℝ≥0 → Ω' → ℝ) (B' : ℝ≥0 → Ω' → ℝ) (ζ' : Ω' → ℝ≥0∞),
    IsIntegratedSLEEvolution κ y₀.2.1 y₀.2.2 ρL ρR P' 𝓕' W' VL' VR' B' ζ' ∧
    (∀ᵐ ω' ∂P', ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W' t ω') (traceHorizon full iL iR W' VL' VR' ζ' ω') η) ∧
    AEMeasurable (farSamp iL iR W' VL' VR' ζ') P' ∧ P'.map (farSamp iL iR W' VL' VR' ζ') = ν

/-- A representation traced through the lifetime is traced up to the kill. -/
theorem HasKilledRep.toK {κ : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {iL : Fin nL} {iR : Fin nR}
    {y₀ : Start nL nR} {ν : Measure (Samp nL nR)} (h : HasKilledRep κ true ρL ρR iL iR y₀ ν) :
    HasKilledRep κ false ρL ρR iL iR y₀ ν := by
  obtain ⟨Ω', mΩ', P', hP', 𝓕', W', VL', VR', B', ζ', hE, htr, hm, hmap⟩ := h
  refine ⟨Ω', mΩ', P', hP', 𝓕', W', VL', VR', B', ζ', hE, ?_, hm, hmap⟩
  filter_upwards [htr] with ω' hω'
  obtain ⟨η, hη⟩ := hω'
  exact ⟨η, hη.mono_horizon farLife_le⟩

/-- **The representation on the conditional law's own space**: an integrated evolution on `(Ω, μ)` with a trace up to
the chosen horizon whose killed samples agree `μ`-almost surely with the piece's represents the law of the piece's
samples under `μ`. -/
theorem hasKilledRep_of_ae_eq {κ : ℝ} {full : Bool} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {iL : Fin nL}
    {iR : Fin nR} {y₀ : Start nL nR} {Ω : Type} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hobs : Measurable (pieceSamp W VL VR ζ)) {𝓕' : Filtration ℝ≥0 mΩ} {W' : ℝ≥0 → Ω → ℝ}
    {VL' : Fin nL → ℝ≥0 → Ω → ℝ} {VR' : Fin nR → ℝ≥0 → Ω → ℝ} {B' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution κ y₀.2.1 y₀.2.2 ρL ρR μ 𝓕' W' VL' VR' B' ζ')
    (htr : ∀ᵐ ω ∂μ, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W' t ω) (traceHorizon full iL iR W' VL' VR' ζ' ω) η)
    (hag : ∀ᵐ ω ∂μ, farSamp iL iR W' VL' VR' ζ' ω = pieceSamp W VL VR ζ ω) :
    HasKilledRep κ full ρL ρR iL iR y₀ (μ.map (pieceSamp W VL VR ζ)) := by
  have hag' : farSamp iL iR W' VL' VR' ζ' =ᵐ[μ] pieceSamp W VL VR ζ := hag
  exact ⟨Ω, mΩ, μ, inferInstance, 𝓕', W', VL', VR', B', ζ', hE, htr,
    hobs.aemeasurable.congr hag'.symm, Measure.map_congr hag'⟩

end Rep

/-! ### The comparison forms from the conditional law -/

section Bridge

variable {κ : ℝ} {Ω : Type} {𝓠 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {iL : Fin nL}
  {iR : Fin nR} {R : Set Ω} {y : Ω → Start nL nR} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- The pointwise step: at a sample `ω₀` where the start is fixed by the conditional law and the conditional law of the
samples is represented by an evolution `E'`, every premise bound for `E'` bounds the conditional probability of the
event `{(start, samples) ∈ S}`. -/
theorem le_condExpKernel_of_rep {full : Bool} (hobs : Measurable (pieceSamp W VL VR ζ))
    {S : Set (Start nL nR × Samp nL nR)} (hS : MeasurableSet S) {p : ℝ≥0∞} {ω₀ : Ω}
    (hy₀ : ∀ᵐ ω ∂(condExpKernel P 𝓠 ω₀), y ω = y ω₀)
    (hprem : ∀ (Ω' : Type) (mΩ' : MeasurableSpace Ω') (P' : Measure Ω') [IsProbabilityMeasure P']
      (𝓕' : Filtration ℝ≥0 mΩ') (W' : ℝ≥0 → Ω' → ℝ) (VL' : Fin nL → ℝ≥0 → Ω' → ℝ)
      (VR' : Fin nR → ℝ≥0 → Ω' → ℝ) (B' : ℝ≥0 → Ω' → ℝ) (ζ' : Ω' → ℝ≥0∞),
      IsIntegratedSLEEvolution κ (y ω₀).2.1 (y ω₀).2.2 ρL ρR P' 𝓕' W' VL' VR' B' ζ' →
      (∀ᵐ ω' ∂P', ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W' t ω') (traceHorizon full iL iR W' VL' VR' ζ' ω') η) →
      p ≤ P' {ω' | (y ω₀, farSamp iL iR W' VL' VR' ζ' ω') ∈ S})
    (hrep : HasKilledRep κ full ρL ρR iL iR (y ω₀) ((condExpKernel P 𝓠 ω₀).map (pieceSamp W VL VR ζ))) :
    p ≤ condExpKernel P 𝓠 ω₀ ((fun ω => (y ω, pieceSamp W VL VR ζ ω)) ⁻¹' S) := by
  obtain ⟨Ω', mΩ', P', hP', 𝓕', W', VL', VR', B', ζ', hE, htr, hm, hmap⟩ := hrep
  have hb := hprem Ω' mΩ' P' 𝓕' W' VL' VR' B' ζ' hE htr
  have hsec : MeasurableSet (Prod.mk (y ω₀) ⁻¹' S) := measurable_prodMk_left hS
  have e1 : P' {ω' | (y ω₀, farSamp iL iR W' VL' VR' ζ' ω') ∈ S} =
      (P'.map (farSamp iL iR W' VL' VR' ζ')) (Prod.mk (y ω₀) ⁻¹' S) := by
    rw [Measure.map_apply_of_aemeasurable hm hsec]
    rfl
  rw [e1, hmap, Measure.map_apply hobs hsec] at hb
  refine hb.trans (le_of_eq (measure_congr ?_))
  filter_upwards [hy₀] with ω hω
  change (pieceSamp W VL VR ζ ω ∈ Prod.mk (y ω₀) ⁻¹' S) = ((y ω, pieceSamp W VL VR ζ ω) ∈ S)
  rw [hω]
  rfl

/-- **The killed stage law from the conditional law (traces through the lifetime).** Let the start `y` be
past-measurable and the piece's samples measurable, let clause 1 hold, and let, for almost every `ω₀` in the stage
event, the law of the piece's samples under `condExpKernel P 𝓠 ω₀` be the killed-sample law of an integrated evolution
from `y ω₀` with a trace through its lifetime. Then the stage obeys `IsStageLawFar`. -/
theorem isStageLawFar_of_condLaw (hle : 𝓠 ≤ mΩ) (hy : Measurable[𝓠] y)
    (hobs : Measurable (pieceSamp W VL VR ζ))
    (h1 : ∀ᵐ ω ∂P, ω ∈ R → IsOrderedForceWord (y ω).2.1 (y ω).2.2 ∧ StrictAnti (y ω).2.1 ∧
      StrictMono (y ω).2.2 ∧ Sec2.IsSLEPathUpTo κ (y ω).2.1 (y ω).2.2 ρL ρR (W · ω) (fun i t => VL i t ω)
        (fun k t => VR k t ω) (B · ω) (ζ ω))
    (hcond : ∀ᵐ ω₀ ∂P, ω₀ ∈ R →
      HasKilledRep κ true ρL ρR iL iR (y ω₀) ((condExpKernel P 𝓠 ω₀).map (pieceSamp W VL VR ζ))) :
    IsStageLawFar κ P 𝓠 R ρL ρR iL iR y W VL VR B ζ := by
  refine ⟨h1, fun S hS p hprem A hA hAR => ?_⟩
  have hobsY : Measurable fun ω => (y ω, pieceSamp W VL VR ζ ω) := (hy.mono hle le_rfl).prodMk hobs
  have hSm : MeasurableSet ((fun ω => (y ω, pieceSamp W VL VR ζ ω)) ⁻¹' S) := hobsY hS
  have hpt : ∀ᵐ ω₀ ∂P, ω₀ ∈ A → p ≤ condExpKernel P 𝓠 ω₀ ((fun ω => (y ω, pieceSamp W VL VR ζ ω)) ⁻¹' S) := by
    filter_upwards [hcond, ae_ae_condExpKernel_eq hle hy] with ω₀ hc hy₀ hω₀A
    exact le_condExpKernel_of_rep (full := true) hobs hS hy₀
      (fun Ω' mΩ' P' _ 𝓕' W' VL' VR' B' ζ' hE htr =>
        hprem (y ω₀) (mem_univ _) Ω' mΩ' P' 𝓕' W' VL' VR' B' ζ' hE htr) (hc (hAR hω₀A))
  calc p * P A = ∫⁻ _ in A, p ∂P := (setLIntegral_const A p).symm
    _ ≤ ∫⁻ ω₀ in A, condExpKernel P 𝓠 ω₀ ((fun ω => (y ω, pieceSamp W VL VR ζ ω)) ⁻¹' S) ∂P :=
        setLIntegral_mono_ae' (hle _ hA) hpt
    _ = P (A ∩ (fun ω => (y ω, pieceSamp W VL VR ζ ω)) ⁻¹' S) := KernelTower.setLIntegral_condExpKernel hle hA hSm
    _ = P (A ∩ {ω | (y ω, samp (W · ω) (fun i t => VL i t ω) (fun k t => VR k t ω) (ζ ω)) ∈ S}) := rfl

/-- **The killed stage law from the conditional law (traces up to the kill).** As `isStageLawFar_of_condLaw`, with the
representing evolutions traced only up to their killed lifetime; the conclusion is the trace-up-to-the-kill form
`IsStageLawFarK`. -/
theorem isStageLawFarK_of_condLaw (hle : 𝓠 ≤ mΩ) (hy : Measurable[𝓠] y)
    (hobs : Measurable (pieceSamp W VL VR ζ))
    (h1 : ∀ᵐ ω ∂P, ω ∈ R → IsOrderedForceWord (y ω).2.1 (y ω).2.2 ∧ StrictAnti (y ω).2.1 ∧
      StrictMono (y ω).2.2 ∧ Sec2.IsSLEPathUpTo κ (y ω).2.1 (y ω).2.2 ρL ρR (W · ω) (fun i t => VL i t ω)
        (fun k t => VR k t ω) (B · ω) (ζ ω))
    (hcond : ∀ᵐ ω₀ ∂P, ω₀ ∈ R →
      HasKilledRep κ false ρL ρR iL iR (y ω₀) ((condExpKernel P 𝓠 ω₀).map (pieceSamp W VL VR ζ))) :
    IsStageLawFarK κ P 𝓠 R ρL ρR iL iR y W VL VR B ζ := by
  refine ⟨h1, fun S hS p hprem A hA hAR => ?_⟩
  have hobsY : Measurable fun ω => (y ω, pieceSamp W VL VR ζ ω) := (hy.mono hle le_rfl).prodMk hobs
  have hSm : MeasurableSet ((fun ω => (y ω, pieceSamp W VL VR ζ ω)) ⁻¹' S) := hobsY hS
  have hpt : ∀ᵐ ω₀ ∂P, ω₀ ∈ A → p ≤ condExpKernel P 𝓠 ω₀ ((fun ω => (y ω, pieceSamp W VL VR ζ ω)) ⁻¹' S) := by
    filter_upwards [hcond, ae_ae_condExpKernel_eq hle hy] with ω₀ hc hy₀ hω₀A
    exact le_condExpKernel_of_rep (full := false) hobs hS hy₀
      (fun Ω' mΩ' P' _ 𝓕' W' VL' VR' B' ζ' hE htr =>
        hprem (y ω₀) (mem_univ _) Ω' mΩ' P' 𝓕' W' VL' VR' B' ζ' hE htr) (hc (hAR hω₀A))
  calc p * P A = ∫⁻ _ in A, p ∂P := (setLIntegral_const A p).symm
    _ ≤ ∫⁻ ω₀ in A, condExpKernel P 𝓠 ω₀ ((fun ω => (y ω, pieceSamp W VL VR ζ ω)) ⁻¹' S) ∂P :=
        setLIntegral_mono_ae' (hle _ hA) hpt
    _ = P (A ∩ (fun ω => (y ω, pieceSamp W VL VR ζ ω)) ⁻¹' S) := KernelTower.setLIntegral_condExpKernel hle hA hSm
    _ = P (A ∩ {ω | (y ω, samp (W · ω) (fun i t => VL i t ω) (fun k t => VR k t ω) (ζ ω)) ∈ S}) := rfl

end Bridge

end InteractingSLE.Sec5.CrossCond.StagedKill
