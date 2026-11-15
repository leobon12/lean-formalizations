/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux126
import InteractingSLE.Spec.Sec7.ContinuityProb3Lift
import InteractingSLE.Spec.Sec7.ContinuityProbCollision
import InteractingSLE.Spec.Sec2.Assembly2Entr
import Mathlib.Probability.Kernel.Condexp
import InteractingSLE.Spec.Sec7.Aux122DisintEvol

/-!
# §7.4, Lemma 7.25: the driving reference and Aux. lemma 127's selection at the driver level

Packet PROVE-AUX119-130. Specification §7.4.1, Lemma 7.25 and its proof (`source/spec/p385-432.md` L490–L515,
pp. 413–414), Aux. lemma 125 (L197–L250, pp. 395–399) and Aux. lemma 127 (L318–L333, pp. 402–403).

The open κ > 4 input of Theorem 1.3 left by PROVE-AUX126 is `Sec7.Aux126.Lemma725DriverReferenceStatement`
(`h725`). This file shows:

* **The driving reference is exactly Lemma 7.25's trace statement.** `lemma725DriverReferenceStatement_of_trace`:
  the two-seed word itself (no distant mark) is an admissible reference once its trace is continuous, and every
  admissible word has an evolution (Theorem 2.2, existence). With PROVE-AUX126's converse
  (`lemma725TraceStatement_of_driverReference`) this gives `lemma725DriverReferenceStatement_iff_trace`:
  `h725` is `LP.Lemma725TraceStatement` (finite-time continuity of the both-low two-seed law) and nothing weaker.
  So no driver-level shortcut exists: the input is Lemma 7.25's own conclusion, and the source proves it only through
  the pocket traversal.
* **Aux. lemma 127 at the driver level.** `PocketDriverKernel κ rL rR` is the driving part of Aux. lemma 125's
  conclusion on the positive-probability event of Aux. lemma 130 ("conditionally on `𝓔`, … this kernel has the
  canonical integrated SLE driving marginal", p. 395; the erased traversal is continuous, p. 397): on a standard
  Borel probability space, an initial σ-algebra `𝓔`, an `𝓔`-event `F` of positive probability and an `𝓔`-measurable
  normalized word `Θ = (ΘL, ΘR)` with the prescribed seed weights and separated other marks on `F`; one family of
  relative driving processes which, under the conditional law `condExpKernel P 𝓔 ω₀` for almost every `ω₀ ∈ F`, is
  an integrated evolution of the word `Θ ω₀` with a continuous trace before its lifetime. Aux. lemma 127's selection
  ("Choose one deterministic `θ_*` outside that null set. Such a choice exists because `ν` is a probability measure",
  p. 403) is `aux126DriverReference_of_pocketDriverKernel`, and Lemma 7.25's driving reference follows
  (`lemma725DriverReferenceStatement_of_pocketDriverKernel`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

universe u v

namespace InteractingSLE

namespace Sec7

namespace Lemma725Ref

/-- The two-seed word (one mark at `0⁻`, one at `0⁺`) is ordered. -/
theorem isOrderedForceWord_twoSeed : IsOrderedForceWord LP.twoSeedXL LP.twoSeedXR :=
  ⟨fun _ _ _ => le_rfl, fun _ => le_rfl, fun _ _ _ => le_rfl, fun _ => le_rfl⟩

/-- **Theorem 2.2's existence on a space in any universe** (the assembled existence theorem on a space in `Type`,
lifted along `ULift.down`, `isIntegratedSLEEvolution_comap`). -/
theorem exists_isIntegratedSLEEvolution_ulift {a : ℝ} (ha : 0 < a) {nL nR : ℕ} {xL : Fin nL → ℝ}
    {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR) :
    ∃ (Ω : Type v) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
      (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ := by
  obtain ⟨Ω₁, mΩ₁, P₁, hP₁, 𝓕₁, W, VL, VR, B, ζ, hE⟩ :=
    exists_isIntegratedSLEEvolution_assembled (ρL := ρL) (ρR := ρR) ha hF
  have hdown : Measurable (ULift.down : ULift.{v} Ω₁ → Ω₁) := measurable_down
  have hup : Measurable (ULift.up : Ω₁ → ULift.{v} Ω₁) := measurable_up
  refine ⟨ULift.{v} Ω₁, inferInstance, P₁.map ULift.up, ?_, RandRestart.comapFiltration 𝓕₁ ULift.down hdown,
    _, _, _, _, _, RandRestart.isIntegratedSLEEvolution_comap hE hdown ?_⟩
  · exact ⟨by rw [Measure.map_apply hup MeasurableSet.univ, preimage_univ, measure_univ]⟩
  · rw [Measure.map_map hdown hup]
    exact Measure.map_id

/-- **The two-seed word is a driving reference once its trace is continuous.** If every two-seed evolution with
weights `rL, rR > −2` has a continuous generating trace on `[0, ζ]`, the two-seed word (no distant mark: `nL = nR = 0`)
satisfies `Aux126DriverReference`. -/
theorem aux126DriverReference_of_twoSeedTrace {κ rL rR : ℝ} (hκ : 0 < κ)
    (htr : ∀ {Ω : Type v} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin 1 → ℝ≥0 → Ω → ℝ) (VR : Fin 1 → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution κ LP.twoSeedXL LP.twoSeedXR (fun _ => rL) (fun _ => rR) P 𝓕 W VL VR B ζ →
        ∀ᵐ ω ∂P, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η) :
    Aux126.Aux126DriverReference.{v} κ rL rR := by
  obtain ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, hE⟩ :=
    exists_isIntegratedSLEEvolution_ulift.{v} (ρL := fun _ => rL) (ρR := fun _ => rR) hκ isOrderedForceWord_twoSeed
  refine ⟨0, 0, LP.twoSeedXL, LP.twoSeedXR, fun _ => rL, fun _ => rR, isOrderedForceWord_twoSeed, rfl, rfl,
    fun i hi => (hi (Fin.fin_one_eq_zero i)).elim, fun i hi => (hi (Fin.fin_one_eq_zero i)).elim, rfl, rfl,
    Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, hE, ?_⟩
  filter_upwards [htr P 𝓕 W VL VR B ζ hE] with ω ⟨η, hη⟩ T hT
  exact ⟨η, hη.mono_horizon hT.le⟩

/-- **Lemma 7.25's driving reference from its trace statement**: `LP.Lemma725TraceStatement` (finite-time continuity
of every both-low two-seed evolution) gives `Lemma725DriverReferenceStatement`, with the two-seed word itself as the
reference. -/
theorem lemma725DriverReferenceStatement_of_trace (h : LP.Lemma725TraceStatement.{v}) :
    Aux126.Lemma725DriverReferenceStatement.{v} :=
  fun κ hκ rL rR hL hLd hR hRd =>
    aux126DriverReference_of_twoSeedTrace (by linarith) fun P _ 𝓕 W VL VR B ζ hE =>
      h κ hκ rL rR hL hLd hR hRd P 𝓕 W VL VR B ζ hE

/-- **The driving reference of Lemma 7.25 is Lemma 7.25's trace statement.** With PROVE-AUX126's converse
(`Aux126.lemma725TraceStatement_of_driverReference`, through the change of measure of Aux. lemma 126 and the dilation
step), the two statements are equivalent: the open input `h725` of Theorem 1.3 is finite-time continuity of the
both-low two-seed law itself. -/
theorem lemma725DriverReferenceStatement_iff_trace :
    Aux126.Lemma725DriverReferenceStatement.{v} ↔ LP.Lemma725TraceStatement.{v} :=
  ⟨Aux126.lemma725TraceStatement_of_driverReference, lemma725DriverReferenceStatement_of_trace⟩

/-! ### Aux. lemma 127 at the driver level -/

/-- **The driving part of Aux. lemma 125's conclusion on the event of Aux. lemma 130** (pp. 395–397 and p. 402),
for the seed weights `rL, rR`: a word shape `(nL, nR)` with deterministic weights `ρL, ρR` (the cumulative values
(FW9.1)–(FW9.3) of Aux. lemma 121 are deterministic once the shape is fixed), seed weights `ρL 0 = rL`, `ρR 0 = rR`;
a standard Borel probability space with an initial σ-algebra `𝓔` ("the initial marked `A`"), an `𝓔`-event `F` of
positive probability (Aux. lemma 130's `F_r`, "measurable from the initial marked incoming configuration"), an
`𝓔`-measurable normalized word `Θ = (ΘL, ΘR)` which on `F` is ordered with both seeds at `0` and its other marks
strictly separated from `0` (Aux. lemma 127: "All nonseed marks must be actual marks and must be distinct from the
entry and terminal prime ends"); and one family of relative driving processes `(W, VL, VR, B, ζ)` with a filtration
`𝓕`, such that for almost every `ω₀ ∈ F`, under the conditional law `condExpKernel P 𝓔 ω₀` ("conditionally on `𝓔`,
their full joint law is one kernel `Q_Θ` … this kernel has the canonical integrated SLE driving marginal"), the
processes form an integrated `SLE_κ(Θ ω₀)` evolution whose trace is continuous before its lifetime ("the erased
counterflow is therefore a complete continuous traversal … with a continuous relative driver", p. 414). -/
def PocketDriverKernel (κ rL rR : ℝ) : Prop :=
  ∃ (nL nR : ℕ) (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ), ρL 0 = rL ∧ ρR 0 = rR ∧
    ∃ (Ω : Type v) (mΩ : MeasurableSpace Ω) (_ : StandardBorelSpace Ω) (P : Measure Ω)
      (_ : IsProbabilityMeasure P) (𝓔 : MeasurableSpace Ω) (F : Set Ω) (ΘL : Ω → Fin (nL + 1) → ℝ)
      (ΘR : Ω → Fin (nR + 1) → ℝ),
      MeasurableSet[𝓔] F ∧ 0 < P F ∧ Measurable[𝓔] ΘL ∧ Measurable[𝓔] ΘR ∧
      (∀ ω ∈ F, IsOrderedForceWord (ΘL ω) (ΘR ω) ∧ ΘL ω 0 = 0 ∧ ΘR ω 0 = 0 ∧
        (∀ i, i ≠ 0 → ΘL ω i < 0) ∧ (∀ i, i ≠ 0 → 0 < ΘR ω i)) ∧
      ∃ (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ)
        (VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
        ∀ᵐ ω₀ ∂P, ω₀ ∈ F →
          IsIntegratedSLEEvolution κ (ΘL ω₀) (ΘR ω₀) ρL ρR (condExpKernel (mΩ := mΩ) P 𝓔 ω₀) 𝓕 W VL VR B ζ ∧
            ∀ᵐ ω ∂(condExpKernel (mΩ := mΩ) P 𝓔 ω₀), ∀ T : ℝ≥0, (T : ℝ≥0∞) < ζ ω →
              ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) T η

/-- **Aux. lemma 127, driver level** (p. 403): "Choose one deterministic `θ_*` outside that null set. Such a choice
exists because `ν` is a probability measure; it does not require an atom at `θ_*` or an event of positive
probability fixing its positions exactly. … its seed weights are exactly the prescribed `r_L, r_R`. Therefore
`Q_{θ_*}` satisfies the hypotheses of Aux. lemma 126." The exceptional set is `P`-null and `F` is not, so some
`ω₀ ∈ F` is good; the conditional law at `ω₀` is a probability measure carrying an evolution of the deterministic
word `Θ ω₀`. -/
theorem aux126DriverReference_of_pocketDriverKernel {κ rL rR : ℝ} (h : PocketDriverKernel.{v} κ rL rR) :
    Aux126.Aux126DriverReference.{v} κ rL rR := by
  obtain ⟨nL, nR, ρL, ρR, hρL, hρR, Ω, mΩ, hSB, P, hP, 𝓔, F, ΘL, ΘR, -, hF, -, -, hword, 𝓕, W, VL, VR, B, ζ,
    hgood⟩ := h
  have hne : ∃ ω₀ ∈ F,
      IsIntegratedSLEEvolution κ (ΘL ω₀) (ΘR ω₀) ρL ρR (condExpKernel (mΩ := mΩ) P 𝓔 ω₀) 𝓕 W VL VR B ζ ∧
      ∀ᵐ ω ∂(condExpKernel (mΩ := mΩ) P 𝓔 ω₀), ∀ T : ℝ≥0, (T : ℝ≥0∞) < ζ ω →
        ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) T η := by
    by_contra hcon
    simp only [not_exists, not_and] at hcon
    have hsub : F ⊆ {ω₀ | ¬ (ω₀ ∈ F →
        IsIntegratedSLEEvolution κ (ΘL ω₀) (ΘR ω₀) ρL ρR (condExpKernel (mΩ := mΩ) P 𝓔 ω₀) 𝓕 W VL VR B ζ ∧
          ∀ᵐ ω ∂(condExpKernel (mΩ := mΩ) P 𝓔 ω₀), ∀ T : ℝ≥0, (T : ℝ≥0∞) < ζ ω →
            ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) T η)} := by
      intro ω₀ hω₀ himp
      obtain ⟨h1, h2⟩ := himp hω₀
      exact hcon ω₀ hω₀ h1 h2
    exact hF.ne' (measure_mono_null hsub (ae_iff.1 hgood))
  obtain ⟨ω₀, hω₀, hE, htr⟩ := hne
  obtain ⟨hord, hL0, hR0, hLn, hRp⟩ := hword ω₀ hω₀
  exact ⟨nL, nR, ΘL ω₀, ΘR ω₀, ρL, ρR, hord, hL0, hR0, hLn, hRp, hρL, hρR, Ω, mΩ, condExpKernel (mΩ := mΩ) P 𝓔 ω₀,
    inferInstance, 𝓕, W, VL, VR, B, ζ, hE, htr⟩

/-- **Lemma 7.25's driving reference from the pocket kernels** (Lemma 7.25's proof, p. 414: "Aux. lemma 125 gives
the complete canonical pair kernel `Q_Θ` … Finally Aux. lemma 127 selects a good deterministic member of this family
and applies Aux. lemma 126"): if for every `κ > 4` and both-low seed weights the driving part of Aux. lemma 125's
conclusion holds on a positive-probability initial event, then `Lemma725DriverReferenceStatement` holds. -/
theorem lemma725DriverReferenceStatement_of_pocketDriverKernel
    (h : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → rL < κ / 2 - 4 → -2 < rR → rR < κ / 2 - 4 →
      PocketDriverKernel.{v} κ rL rR) :
    Aux126.Lemma725DriverReferenceStatement.{v} :=
  fun κ hκ rL rR hL hLd hR hRd => aux126DriverReference_of_pocketDriverKernel (h κ hκ rL rR hL hLd hR hRd)

/-! ### The pocket input in the conclusion form of Aux. lemma 122 -/

/-- **The pocket traversal's relative driver as an evolution with a random initial word** (Aux. lemma 122's
conclusion, p. 390: "Conditional on initial information fixing the word and its marked positions, the coordinates
satisfy this SDE with Brownian noise independent of that initial information"; on the event of Aux. lemma 130, with the
word of Aux. lemmas 119–121 and the continuous erased traversal of p. 414): as `PocketDriverKernel`, but with the
processes given as an integrated evolution of the `𝓔`-measurable word `Θ` in a filtration with `𝓔 ≤ 𝓕 0`
(`Aux122Disint.IsRandomWordEvolution`) whose trace is continuous before its lifetime almost surely on `F`. -/
def PocketWordEvolution (κ rL rR : ℝ) : Prop :=
  ∃ (nL nR : ℕ) (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ), ρL 0 = rL ∧ ρR 0 = rR ∧
    ∃ (Ω : Type v) (mΩ : MeasurableSpace Ω) (_ : StandardBorelSpace Ω) (P : Measure Ω)
      (_ : IsProbabilityMeasure P) (𝓔 : MeasurableSpace Ω) (F : Set Ω) (ΘL : Ω → Fin (nL + 1) → ℝ)
      (ΘR : Ω → Fin (nR + 1) → ℝ), 0 < P F ∧
      (∀ ω ∈ F, IsOrderedForceWord (ΘL ω) (ΘR ω) ∧ ΘL ω 0 = 0 ∧ ΘR ω 0 = 0 ∧
        (∀ i, i ≠ 0 → ΘL ω i < 0) ∧ (∀ i, i ≠ 0 → 0 < ΘR ω i)) ∧
      ∃ (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ)
        (VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
        Aux122Disint.IsRandomWordEvolution (mΩ := mΩ) κ P 𝓔 F ΘL ΘR ρL ρR 𝓕 W VL VR B ζ ∧
          ∀ᵐ ω ∂P, ω ∈ F → ∀ T : ℝ≥0, (T : ℝ≥0∞) < ζ ω →
            ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) T η

/-- **Disintegration turns the random-word pocket evolution into the conditional pocket kernels** (Aux. lemma 122,
p. 391: "Disintegration over that initial information preserves the integrated SDE and this Brownian property";
`Aux122Disint.IsRandomWordEvolution.exists_ae_condExpKernel`). -/
theorem pocketDriverKernel_of_pocketWordEvolution {κ rL rR : ℝ} (h : PocketWordEvolution.{v} κ rL rR) :
    PocketDriverKernel.{v} κ rL rR := by
  obtain ⟨nL, nR, ρL, ρR, hρL, hρR, Ω, mΩ, hSB, P, hP, 𝓔, F, ΘL, ΘR, hPF, hword, 𝓕, W, VL, VR, B, ζ, hE,
    htr⟩ := h
  obtain ⟨N, 𝓖, W', VL', VR', B', -, hN0, hWW, hae⟩ := hE.exists_ae_condExpKernel (mΩ := mΩ)
  have hle : 𝓔 ≤ mΩ := hE.1.trans (𝓕.le 0)
  have htr' : ∀ᵐ ω ∂P, ω ∈ F → ∀ T : ℝ≥0, (T : ℝ≥0∞) < ζ ω →
      ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W' t ω) T η := by
    filter_upwards [htr, measure_eq_zero_iff_ae_notMem.1 hN0] with ω h1 hωN hωF T hT
    obtain ⟨η, hη⟩ := h1 hωF T hT
    have e : (fun t => W' t ω) = fun t => W t ω := funext (hWW ω hωN hωF)
    exact ⟨η, e ▸ hη⟩
  refine ⟨nL, nR, ρL, ρR, hρL, hρR, Ω, mΩ, hSB, P, hP, 𝓔, F, ΘL, ΘR, hE.2.1, hPF, hE.2.2.1, hE.2.2.2.1,
    hword, 𝓖, W', VL', VR', B', ζ, ?_⟩
  filter_upwards [hae, Aux122Disint.ae_ae_condExpKernel (mΩ := mΩ) hle htr',
    Aux122Disint.ae_ae_condExpKernel_mem (mΩ := mΩ) hle hE.2.1] with ω₀ hev htrν hmem hω₀F
  refine ⟨hev hω₀F, ?_⟩
  filter_upwards [htrν, hmem hω₀F] with ω h1 h2 using h1 h2

/-- **Lemma 7.25's driving reference from the random-word pocket evolutions**: disintegration
(`pocketDriverKernel_of_pocketWordEvolution`) and Aux. lemma 127's selection
(`aux126DriverReference_of_pocketDriverKernel`). -/
theorem lemma725DriverReferenceStatement_of_pocketWordEvolution
    (h : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → rL < κ / 2 - 4 → -2 < rR → rR < κ / 2 - 4 →
      PocketWordEvolution.{v} κ rL rR) :
    Aux126.Lemma725DriverReferenceStatement.{v} :=
  lemma725DriverReferenceStatement_of_pocketDriverKernel fun κ hκ rL rR hL hLd hR hRd =>
    pocketDriverKernel_of_pocketWordEvolution (h κ hκ rL rR hL hLd hR hRd)

end Lemma725Ref

end Sec7

end InteractingSLE
