/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop59StageLaw
import InteractingSLE.Spec.Restart.DomainMarkovKernel
import InteractingSLE.Spec.Supplement.KernelTower

/-!
# Proposition 5.9's stage law: the disintegration step

Packet PROVE-PROP59T3. Specification §5.2, proof of Proposition 5.9 (`source/spec/p097-144.md` L1000–L1006, p. 144):
"Condition on the entire already revealed history. If we use the extreme angle `−e_j π/2`, […] the driver reaches
`e_j(2 + 1/8)` before the trajectory hits the revealed counterflow or its continuation threshold." The experiment of
PROVE-PROP59T2 consumes this conditional law in the comparison form `IsStageLaw` (`Prop59StageLaw`). This file proves
that comparison form from the form in which the cross-conditioning laws and the restart lemmas deliver a new piece:

* the piece is an **integrated evolution with an initially measurable random word**
  (`Sec7.Aux122Disint.IsRandomWordEvolution`): a Brownian motion of a filtration whose time-`0` σ-algebra contains
  the past `𝓠`, coordinates adapted before the lifetime, and, almost surely on the stage event `R`, the integrated
  equations of Definition 2.1 from the past-measurable word;

together with the absolute driver position being past-measurable, the strictness of the start, and an almost surely
existing generating trace on `R` (the piece is a flow line, a continuous curve).

The proof disintegrates along the regular conditional law `condExpKernel P 𝓠` (Aux. lemma 122,
`Restart.DomainMarkov.exists_ae_condExpKernel_agree`): for `P`-almost every `ω₀ ∈ R`, under `condExpKernel P 𝓠 ω₀`
modified processes (equal to the piece off a null set) form an integrated evolution of the deterministic word of
`ω₀`, with a generating trace almost surely, and the start equals `y ω₀` almost surely. The premise of the comparison
form then bounds the conditional probability of the Borel event from below, and integrating over a past event
`A ⊆ R` (`KernelTower.setLIntegral_condExpKernel`) gives `p P(A) ≤ P(A ∩ {(start, samples) ∈ S})`.

## Main results

* **`isStageLaw_of_isRandomWordEvolution`**: `IsRandomWordEvolution` + past-measurable absolute driver + strict
  ordered start + a.s. trace ⟹ `IsStageLaw` (standard Borel `Ω`).
* `IsStagePieceLaw`: these hypotheses for one stage, bundled for a stage of a stage system.
* **`prop59StageLawStatement_of_pieceLaw`**: `Prop59StageLawStatement` for a stage system all of whose stages have
  `IsStagePieceLaw` with the deterministic stage words.

Conditional helpers with distinct names; they replace no source theorem.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec5

namespace Prop59Stage

open Sec7.Aux122Disint

section Bridge

variable {κ : ℝ} {Ω : Type} {𝓠 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- The (start, samples) map of a stage. -/
def stageObs {Ω : Type*} {nL nR : ℕ} (y : Ω → Start nL nR) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω) : Start nL nR × Samp nL nR :=
  (y ω, samp (W · ω) (fun i t => VL i t ω) (fun k t => VR k t ω) (ζ ω))

/-- **The disintegration step of the stage law** (Proposition 5.9, p. 144: "condition on the entire already revealed
history"). Let the piece `(W, V_L, V_R, B, ζ)` be an integrated evolution with the initially measurable random word
`((y ·).2.1, (y ·).2.2)` on the stage event `R` (`IsRandomWordEvolution` with initial σ-algebra the past `𝓠`), let the
absolute driver position `(y ·).1` be past-measurable, and almost surely on `R` let the start be a strictly ordered
force word and the piece have a generating trace. On a standard Borel space, the stage then obeys `IsStageLaw`. -/
theorem isStageLaw_of_isRandomWordEvolution {R : Set Ω} {y : Ω → Start nL nR}
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : @IsRandomWordEvolution Ω mΩ κ nL nR P 𝓠 R (fun ω => (y ω).2.1) (fun ω => (y ω).2.2) ρL ρR 𝓕 W VL VR
      B ζ)
    (hy1 : Measurable[𝓠] fun ω => (y ω).1)
    (hord : ∀ᵐ ω ∂P, ω ∈ R → IsOrderedForceWord (y ω).2.1 (y ω).2.2 ∧ StrictAnti (y ω).2.1 ∧
      StrictMono (y ω).2.2)
    (htr : ∀ᵐ ω ∂P, ω ∈ R → ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η) :
    @IsStageLaw κ Ω mΩ P 𝓠 R nL nR ρL ρR y W VL VR B ζ := by
  have hE' := hE
  obtain ⟨h0, hR, hΘL, hΘR, -, hWa, hVLa, hVRa, hpath⟩ := hE'
  have hle : 𝓠 ≤ mΩ := h0.trans (𝓕.le 0)
  refine ⟨?_, ?_⟩
  · filter_upwards [hord, hpath] with ω h1 h2 hω
    exact ⟨(h1 hω).1, (h1 hω).2.1, (h1 hω).2.2, h2 hω⟩
  intro S hS p hprem A hA hAR
  -- the disintegration of the piece
  obtain ⟨N, 𝓖, W', VL', VR', B', -, hN0, hagree, hev⟩ := Restart.DomainMarkov.exists_ae_condExpKernel_agree hE
  have hy : Measurable[𝓠] y := hy1.prodMk (hΘL.prodMk hΘR)
  have hobs : Measurable (stageObs y W VL VR ζ) :=
    (hy.mono hle le_rfl).prodMk (measurable_samp_of_adaptedBefore hWa hVLa hVRa)
  have hSm : MeasurableSet (stageObs y W VL VR ζ ⁻¹' S) := hobs hS
  have hNc : ∀ᵐ ω ∂P, ω ∉ N := measure_eq_zero_iff_ae_notMem.1 hN0
  -- the pointwise bound under almost every conditional law
  have hpt : ∀ᵐ ω₀ ∂P, ω₀ ∈ A → p ≤ condExpKernel P 𝓠 ω₀ (stageObs y W VL VR ζ ⁻¹' S) := by
    filter_upwards [hev, ae_ae_condExpKernel hle hNc, ae_ae_condExpKernel_mem hle hR,
      ae_ae_condExpKernel hle htr, ae_ae_condExpKernel_eq hle hy] with ω₀ hev₀ hN₀ hR₀ htr₀ hy₀ hω₀A
    have hω₀R : ω₀ ∈ R := hAR hω₀A
    have hgood : ∀ᵐ ω ∂(condExpKernel P 𝓠 ω₀), ω ∉ N ∧ ω ∈ R ∧ y ω = y ω₀ ∧
        (ω ∈ R → ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η) := by
      filter_upwards [hN₀, hR₀ hω₀R, hy₀, htr₀] with ω h1 h2 h3 h4
      exact ⟨h1, h2, h3, h4⟩
    have htr' : ∀ᵐ ω ∂(condExpKernel P 𝓠 ω₀), ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W' t ω) (ζ ω) η := by
      filter_upwards [hgood] with ω hω
      obtain ⟨h1, h2, -, h4⟩ := hω
      obtain ⟨η, hη⟩ := h4 h2
      refine ⟨η, ?_⟩
      have e : (fun t => W' t ω) = fun t => W t ω := funext fun t => (hagree ω h1 h2 t).1
      rw [e]
      exact hη
    have hbound := hprem (y ω₀) Ω mΩ (condExpKernel P 𝓠 ω₀) 𝓖 W' VL' VR' B' ζ (hev₀ hω₀R) htr'
    refine hbound.trans (measure_mono_ae ?_)
    filter_upwards [hgood] with ω hg hω
    obtain ⟨h1, h2, h3, -⟩ := hg
    have eW : (fun t => W' t ω) = fun t => W t ω := funext fun t => (hagree ω h1 h2 t).1
    have eL : (fun i t => VL' i t ω) = fun i t => VL i t ω :=
      funext fun i => funext fun t => (hagree ω h1 h2 t).2.1 i
    have eR : (fun k t => VR' k t ω) = fun k t => VR k t ω :=
      funext fun k => funext fun t => (hagree ω h1 h2 t).2.2.1 k
    show stageObs y W VL VR ζ ω ∈ S
    have hω' : (y ω₀, samp (fun t => W' t ω) (fun i t => VL' i t ω) (fun k t => VR' k t ω) (ζ ω)) ∈ S := hω
    rw [eW, eL, eR, ← h3] at hω'
    exact hω'
  -- integrate over `A`
  calc p * P A = ∫⁻ _ in A, p ∂P := (setLIntegral_const A p).symm
    _ ≤ ∫⁻ ω₀ in A, condExpKernel P 𝓠 ω₀ (stageObs y W VL VR ζ ⁻¹' S) ∂P :=
        setLIntegral_mono_ae' (hle _ hA) hpt
    _ = P (A ∩ stageObs y W VL VR ζ ⁻¹' S) := KernelTower.setLIntegral_condExpKernel hle hA hSm
    _ = P (A ∩ {ω | (y ω, samp (W · ω) (fun i t => VL i t ω) (fun k t => VR k t ω) (ζ ω)) ∈ S}) := rfl

/-- **The law of one stage piece in its delivered form** (the hypotheses of `isStageLaw_of_isRandomWordEvolution`):
for some filtration, the piece is an integrated evolution with the initially measurable random word `(y ·).2` on the
stage event `R` (initial σ-algebra the past `𝓠`); the absolute driver `(y ·).1` is past-measurable; almost surely on
`R` the start is a strictly ordered force word and the piece has a generating trace. -/
def IsStagePieceLaw (κ : ℝ) {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) (𝓠 : MeasurableSpace Ω)
    (R : Set Ω) {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (y : Ω → Start nL nR) (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) : Prop :=
  (∃ 𝓕 : Filtration ℝ≥0 mΩ, @IsRandomWordEvolution Ω mΩ κ nL nR P 𝓠 R (fun ω => (y ω).2.1)
    (fun ω => (y ω).2.2) ρL ρR 𝓕 W VL VR B ζ) ∧
  Measurable[𝓠] (fun ω => (y ω).1) ∧
  (∀ᵐ ω ∂P, ω ∈ R → IsOrderedForceWord (y ω).2.1 (y ω).2.2 ∧ StrictAnti (y ω).2.1 ∧ StrictMono (y ω).2.2) ∧
  ∀ᵐ ω ∂P, ω ∈ R → ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η

/-- `IsStagePieceLaw` gives `IsStageLaw` (standard Borel `Ω`). -/
theorem IsStagePieceLaw.isStageLaw {R : Set Ω} {y : Ω → Start nL nR} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (h : @IsStagePieceLaw κ Ω mΩ P 𝓠 R nL nR ρL ρR y W VL VR B ζ) :
    @IsStageLaw κ Ω mΩ P 𝓠 R nL nR ρL ρR y W VL VR B ζ := by
  obtain ⟨⟨𝓕, hE⟩, hy1, hord, htr⟩ := h
  exact isStageLaw_of_isRandomWordEvolution hE hy1 hord htr

end Bridge

/-! ### Transfers of the stage law -/

section Transfer

variable {κ : ℝ} {Ω : Type*} {𝓠 𝓠' : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {R : Set Ω}
  {nL nR : ℕ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- **A smaller past.** The stage law for a past `𝓠` gives it for every smaller past `𝓠′ ≤ 𝓠` (fewer events `A` to
test; the delivered σ-algebra of a cross-conditioning law may be larger than the past recorded by a stage system). -/
theorem IsStageLaw.mono_past {y : Ω → Start nL nR} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (h : @IsStageLaw κ Ω mΩ P 𝓠 R nL nR ρL ρR y W VL VR B ζ) (h' : 𝓠' ≤ 𝓠) :
    @IsStageLaw κ Ω mΩ P 𝓠' R nL nR ρL ρR y W VL VR B ζ :=
  ⟨h.1, fun S hS p hp A hA hAR => h.2 S hS p hp A (h' _ hA) hAR⟩

/-- **Versions.** If the (start, samples) of two families agree almost surely on the stage event and the second
family has the pathwise properties of clause 1, the stage law passes from the first to the second (clause 2 sees only
the joint law of the past events and (start, samples)). -/
theorem IsStageLaw.congr {y y' : Ω → Start nL nR} {W W' : ℝ≥0 → Ω → ℝ} {VL VL' : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR VR' : Fin nR → ℝ≥0 → Ω → ℝ} {B B' : ℝ≥0 → Ω → ℝ} {ζ ζ' : Ω → ℝ≥0∞}
    (h : @IsStageLaw κ Ω mΩ P 𝓠 R nL nR ρL ρR y W VL VR B ζ)
    (hobs : ∀ᵐ ω ∂P, ω ∈ R → stageObs y' W' VL' VR' ζ' ω = stageObs y W VL VR ζ ω)
    (h1 : ∀ᵐ ω ∂P, ω ∈ R → IsOrderedForceWord (y' ω).2.1 (y' ω).2.2 ∧ StrictAnti (y' ω).2.1 ∧
      StrictMono (y' ω).2.2 ∧ IsIntegratedSLEPath κ (y' ω).2.1 (y' ω).2.2 ρL ρR (W' · ω)
        (fun i t => VL' i t ω) (fun k t => VR' k t ω) (B' · ω) (ζ' ω)) :
    @IsStageLaw κ Ω mΩ P 𝓠 R nL nR ρL ρR y' W' VL' VR' B' ζ' := by
  refine ⟨h1, fun S hS p hp A hA hAR => (h.2 S hS p hp A hA hAR).trans (le_of_eq (measure_congr ?_))⟩
  filter_upwards [hobs] with ω hω
  refine propext ⟨fun ⟨h1, h2⟩ => ⟨h1, ?_⟩, fun ⟨h1, h2⟩ => ⟨h1, ?_⟩⟩
  · have e := hω (hAR h1)
    show stageObs y' W' VL' VR' ζ' ω ∈ S
    rw [e]; exact h2
  · have e := hω (hAR h1)
    show stageObs y W VL VR ζ ω ∈ S
    rw [← e]; exact h2

end Transfer

/-! ### The stage law of a stage system -/

/-- **Every stage of a stage system has the delivered piece law** with the deterministic stage word
`(stageρL κ ρL₀ j; stageρR κ ρR₀ j)` (the form in which the cross-conditioning laws give each new extreme-angle
piece, conditionally on the revealed counterflow and flow prefix). -/
def Prop59StagePieceLawStatement (κ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) {nL₀ nR₀ : ℕ}
    (ρL₀ : Fin nL₀ → ℝ) (ρR₀ : Fin nR₀ → ℝ) (sys : StageSys Ω nL₀ nR₀) : Prop :=
  ∀ (r : ℕ → ℕ) (j : ℕ), IsStagePieceLaw κ P (sys r j).past (sys r j).R (stageρL κ ρL₀ j) (stageρR κ ρR₀ j)
    (sys r j).y (sys r j).W (sys r j).VL (sys r j).VR (sys r j).B (sys r j).ζ

/-- **The stage law from the delivered piece laws** (standard Borel `Ω`): `Prop59StageLawStatement` holds for every
stage system whose stages have the piece law of `Prop59StagePieceLawStatement`. -/
theorem prop59StageLawStatement_of_pieceLaw {κ : ℝ} {Ω : Type} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {nL₀ nR₀ : ℕ} {ρL₀ : Fin nL₀ → ℝ} {ρR₀ : Fin nR₀ → ℝ}
    {sys : StageSys Ω nL₀ nR₀} (h : Prop59StagePieceLawStatement κ P ρL₀ ρR₀ sys) :
    Prop59StageLawStatement κ P ρL₀ ρR₀ sys := fun r j => (h r j).isStageLaw

end Prop59Stage

end Sec5

end InteractingSLE
