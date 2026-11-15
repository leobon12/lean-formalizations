/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Theorem13Inputs

/-!
# Lemma LP1 and the one-seed parameter coverage, through the zero-weight left seed

Packet PROVE-LP14. Supplement §6.1, Lemma LP1 (`source/spec/p433-480.md` L1086–L1120, pp. 478–479): "Let `k > 0`,
`−2 < ρ < c`, and `q > −2`. Suppose the canonical two-seed `SLE_k(q; ρ)` driving law has a continuous trace on every
finite capacity interval. Then the canonical single-right-seed `SLE_k(ρ)` driving law has a continuous trace on every
finite capacity interval", and its use, the "One-seed parameter coverage" (p. 479): "every admissible one-seed weight
has finite-time continuity by these inputs". Theorem LP10 consumes it as "the one-seed theorem for every admissible
continuation" (p. 486), inside the one-force base `OneForceStatement` (Aux. lemma 99 with the one-seed theorem,
`Sec7.oneForceStatement_of_stopped`, whose seed premise is PROVE-T13-ASM's `Theorem13.SeedOneForceGTFourStatement`).

LP1's proof waits for a collision of the driver with the right seed, maps out, and deletes the separated left drift by
a bounded-energy change of measure, because its references (Lemma 7.25, Aux. lemma 131, Theorem R.7) supply only
particular pairs `(q, ρ)`. Theorem LP10 instead assumes the complete two-seed theorem for *every* admissible pair, in
particular for `q = 0`. With `q = 0` no extraction is needed: the left seed has weight zero, the driving equation of
`SLE_k(0; ρ)` is that of `SLE_k(ρ)`, and deleting the zero-weight left coordinate turns a two-seed evolution into a
one-seed evolution (`IsIntegratedSLEEvolution.compEmb`). The one-seed word has no left mark, so its start is separated
and every event of its driver has one canonical probability (`Sec7.RandRestart.measure_eventOf_eq_codeLaw`): the trace
event (continuity through the lifetime and transience) transfers from the deleted two-seed evolution to every one-seed
evolution. This proves the one-seed theorem, transience included, for every weight `ρ > −2` and every `k > 0`.

## Main results

* `isCompleteForceWord_of_ae_traceEvent`: a word with a separated start is complete as soon as one of its evolutions
  (on any probability space) almost surely has the trace event.
* `exists_isIntegratedSLEEvolution_ulift`: Theorem 2.2's existence on a probability space in every universe.
* `isCompleteForceWord_seed_of_twoSeed` (**LP1 with `q = 0`**, continuity and transience): the one-seed word `SLE_k(ρ)`
  is complete if the two-seed word `SLE_k(0; ρ)` is.
* **`seedOneForce_of_twoSeedComplete`**: the one-seed theorem from LP10's two-seed premise `TwoSeedComplete κ`, in the
  exact form of the `hseed` premise of `Sec7.oneForceStatement_of_stopped`.
* `oneForceStatement_of_twoSeedComplete`: LP10's one-force base from Aux. lemma 99 and the two-seed premise.

The general-`q` extraction of LP1 (Jacobi endpoint accessibility, strong Markov restart, Yuan's mapping-out theorem,
disintegration, bounded-energy deletion) is not formalized: no consumer needs it.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.LP

open Sec7 Sec7.RandRestart

variable {κ : ℝ} {nL nR : ℕ}

/-- **Completeness of a separated word from one evolution.** If the start of the word is separated (`xL i < xR j`; for
instance there is no left mark) and one evolution of the word, on any probability space, almost surely has a
continuous generating trace through its lifetime which is transient on infinite lifetime, then every evolution has
this property: its probability is the canonical one of the word (`measure_eventOf_eq_codeLaw`, through the measurable
trace coding `traceCodeSet`). -/
theorem isCompleteForceWord_of_ae_traceEvent (hκ : 0 < κ) {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hsep : ∀ i j, xL i < xR j) {Ω₀ : Type*} {m₀ : MeasurableSpace Ω₀}
    {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀] {𝓕₀ : Filtration ℝ≥0 m₀} {W₀ : ℝ≥0 → Ω₀ → ℝ}
    {VL₀ : Fin nL → ℝ≥0 → Ω₀ → ℝ} {VR₀ : Fin nR → ℝ≥0 → Ω₀ → ℝ} {B₀ : ℝ≥0 → Ω₀ → ℝ} {ζ₀ : Ω₀ → ℝ≥0∞}
    (hE₀ : IsIntegratedSLEEvolution κ xL xR ρL ρR P₀ 𝓕₀ W₀ VL₀ VR₀ B₀ ζ₀)
    (htr₀ : HasTransientGeneratingTrace P₀ W₀ ζ₀) : IsCompleteForceWord.{u} κ xL xR ρL ρR := by
  intro Ω mΩ P _ 𝓕 W VL VR B ζ hE
  have e := measure_eventOf_eq_codeLaw hκ hsep hE (Φ := fun w τ => ¬ TraceEvent w τ)
    measurableSet_traceCodeSet.compl compl_traceCodeSet_iff not_traceEvent_congr
  have e₀ := measure_eventOf_eq_codeLaw hκ hsep hE₀ (Φ := fun w τ => ¬ TraceEvent w τ)
    measurableSet_traceCodeSet.compl compl_traceCodeSet_iff not_traceEvent_congr
  have h0 : P₀ {ω | ¬ TraceEvent (fun t => W₀ t ω) (ζ₀ ω)} = 0 := ae_iff.1 htr₀
  rw [h0] at e₀
  exact ae_iff.2 (e.trans e₀.symm)

/-- **Theorem 2.2's existence in every universe**: an ordered word has an evolution on a probability space in the
universe `u` (the assembled existence theorem on a space in `Type`, lifted by `ULift`). -/
theorem exists_isIntegratedSLEEvolution_ulift (hκ : 0 < κ) {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} (hF : IsOrderedForceWord xL xR) :
    ∃ (Ω : Type u) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
      (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ := by
  obtain ⟨Ω₁, mΩ₁, P₁, hP₁, 𝓕₁, W, VL, VR, B, ζ, hE⟩ :=
    Theorem13.existsEvolutionStatement hκ xL xR ρL ρR hF
  have hdown : Measurable (ULift.down : ULift.{u} Ω₁ → Ω₁) := measurable_down
  have hup : Measurable (ULift.up : Ω₁ → ULift.{u} Ω₁) := measurable_up
  refine ⟨ULift.{u} Ω₁, inferInstance, P₁.map ULift.up, ?_, comapFiltration 𝓕₁ ULift.down hdown, _, _, _, _,
    _, isIntegratedSLEEvolution_comap hE hdown ?_⟩
  · exact ⟨by rw [Measure.map_apply hup MeasurableSet.univ, preimage_univ, measure_univ]⟩
  · rw [Measure.map_map hdown hup]
    exact Measure.map_id

/-- The two-seed word is ordered. -/
theorem isOrderedForceWord_twoSeed : IsOrderedForceWord twoSeedXL twoSeedXR :=
  ⟨fun _ _ _ => le_rfl, fun _ => le_rfl, fun _ _ _ => le_rfl, fun _ => le_rfl⟩

/-- **Lemma LP1 with `q = 0`, continuity and transience** (supplement p. 478): the single-right-seed word `SLE_k(r)`
(no left mark, one right mark at `0⁺` of weight `r`) is complete if the two-seed word `SLE_k(0; r)` is. A two-seed
evolution with left weight `0` is, after deleting its left coordinate, a one-seed evolution with the same driver, and
the one-seed word has a separated start. -/
theorem isCompleteForceWord_seed_of_twoSeed (hκ : 0 < κ) (r : ℝ)
    (h2 : IsCompleteForceWord.{u} κ twoSeedXL twoSeedXR (fun _ => 0) (fun _ => r)) (xL ρL : Fin 0 → ℝ) :
    IsCompleteForceWord.{u} κ xL (fun _ : Fin 1 => (0 : ℝ)) ρL (fun _ => r) := by
  obtain ⟨Ω₀, m₀, P₀, hP₀, 𝓕₀, W₀, VL₀, VR₀, B₀, ζ₀, hE₀⟩ :=
    exists_isIntegratedSLEEvolution_ulift.{u} (ρL := fun _ => 0) (ρR := fun _ => r) hκ isOrderedForceWord_twoSeed
  have htr₀ := h2 P₀ 𝓕₀ W₀ VL₀ VR₀ B₀ ζ₀ hE₀
  have hD := hE₀.compEmb (OrderEmbedding.ofIsEmpty : Fin 0 ↪o Fin 1)
    (RelEmbedding.refl (· ≤ ·) : Fin 1 ↪o Fin 1) (fun _ _ => rfl) (fun i hi => absurd ⟨i, rfl⟩ hi)
  obtain rfl : xL = fun j => twoSeedXL ((OrderEmbedding.ofIsEmpty : Fin 0 ↪o Fin 1) j) := Subsingleton.elim _ _
  obtain rfl : ρL = fun j => (fun _ : Fin 1 => (0 : ℝ)) ((OrderEmbedding.ofIsEmpty : Fin 0 ↪o Fin 1) j) :=
    Subsingleton.elim _ _
  intro Ω mΩ
  exact isCompleteForceWord_of_ae_traceEvent hκ (fun i => i.elim0) hD htr₀

/-- **The one-seed theorem from the two-seed premise** (LP10's "one-seed theorem for every admissible continuation",
p. 486; the "One-seed parameter coverage", p. 479): if the two-seed word is complete for every admissible pair, then
for every weight `ρ > −2` the single-right-seed word is complete. This is the `hseed` premise of
`Sec7.oneForceStatement_of_stopped`, verbatim. -/
theorem seedOneForce_of_twoSeedComplete (hκ : 0 < κ) (h2 : TwoSeedComplete.{u} κ) :
    ∀ (xL ρL : Fin 0 → ℝ) (ρR : Fin 1 → ℝ), -2 < ρR 0 → IsCompleteForceWord.{u} κ xL (fun _ => 0) ρL ρR := by
  intro xL ρL ρR hρ
  have hρR : ρR = fun _ => ρR 0 := funext fun j => by rw [Fin.fin_one_eq_zero j]
  rw [hρR]
  intro Ω mΩ
  exact isCompleteForceWord_seed_of_twoSeed hκ (ρR 0) (h2 0 (ρR 0) (by norm_num) hρ) xL ρL

/-- **LP10's one-force base from Aux. lemma 99 and the two-seed premise** (p. 486: "With one group use Aux. lemma 99
through its first swallow and the one-seed theorem for every admissible continuation"). -/
theorem oneForceStatement_of_twoSeedComplete (hκ : 0 < κ) (h99 : Sec7.Aux99StoppedStatement.{u} κ)
    (h2 : TwoSeedComplete.{u} κ) : OneForceStatement.{u} κ :=
  Sec7.oneForceStatement_of_stopped h99 (seedOneForce_of_twoSeedComplete hκ h2)

end InteractingSLE.LP
