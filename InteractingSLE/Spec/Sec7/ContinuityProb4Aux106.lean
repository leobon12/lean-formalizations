/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.ContinuityProb4Aux113
import InteractingSLE.Spec.Sec7.ContinuityProbInduction

/-!
# §7.3: Aux. lemma 106 with a positive cross-gap, from finite-time continuity

Packet PROVE-SEC7-C4. Specification Aux. lemma 106 (p. 354, `source/spec/p337-384.md` L382–L416), the case of one
mark on each side with a positive cross-gap (`Sec7.Aux106SeparatedStatement`, PROVE-RANDRESTART2): "Aux. lemma 103,
with `N = 2`, gives continuity on every finite time interval, including a finite continuation endpoint, by deleting
the separated opposite mark and using Aux. lemma 99. It remains to establish transience on infinite lifetime."

* The finite-time part is `ae_isGeneratingTrace_lifetime` with `N = 2`: the words with at most one mark are complete
  by the zero-force base (`isCompleteForceWord_of_forall_eq_zero`) and the one-force cases
  (`isCompleteForceWord_one`: Aux. lemma 99 and the seed one-force theorem, the named inputs of the `κ < 4`
  induction).
* `Aux106TransienceStatement`: **named input**, transience on infinite lifetime (the second and third paragraphs of
  the proof: Aux. lemma 102 and the band comparison when a side weight is at most `−2`; the clock change (J12),
  Aux. lemma 100 and the stationary two-sided Jacobi path-law transfer (J14) with [Yua22] Corollary 1.3 otherwise).
* **`aux106SeparatedStatement_of_inputs`**.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Sec7

/-- **Named input: transience in Aux. lemma 106 for separated marks** (p. 354, from "If `a ≤ 0` or `b ≤ 0`"). For
`0 < κ < 4`, under the two-seed premise, for every evolution of a word with one mark on each side, not both at the
seed: almost surely, if the lifetime is infinite, every continuous generating trace on `[0, ∞)` tends to infinity. -/
def Aux106TransienceStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
    (∀ (xL xR ρL ρR : Fin 1 → ℝ), (∀ i, xL i = 0) → (∀ i, xR i = 0) → (∀ i, -2 < ρL i) →
      (∀ i, -2 < ρR i) → LP.IsCompleteForceWord.{u} κ xL xR ρL ρR) →
    ∀ (xL xR ρL ρR : Fin 1 → ℝ), IsOrderedForceWord xL xR → (xL 0 < 0 ∨ 0 < xR 0) →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin 1 → ℝ≥0 → Ω → ℝ) (VR : Fin 1 → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ →
      ∀ᵐ ω ∂P, ζ ω = ⊤ →
        ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η → Tendsto (fun t => ‖η t‖) atTop atTop

/-- The words with at most one mark are complete (`κ < 4`), from the named inputs of the `κ < 4` induction. -/
theorem distinctCompleteBelow_two (h1 : SeedOneForceTraceStatement.{u}) (h99 : Aux99Statement.{u}) {κ : ℝ}
    (hκ : 0 < κ) (hκ4 : κ < 4) : LP.DistinctCompleteBelow.{u} κ 2 := by
  intro nL nR xL xR ρL ρR hd hlt
  rcases (by omega : nL + nR = 0 ∨ nL + nR = 1) with h0 | h1'
  · have hL : nL = 0 := by omega
    have hR : nR = 0 := by omega
    subst hL hR
    intro Ω mΩ
    exact isCompleteForceWord_of_forall_eq_zero (ρL := ρL) (ρR := ρR) hκ xL xR (fun i => i.elim0)
      (fun i => i.elim0)
  · intro Ω mΩ
    exact isCompleteForceWord_one h1 h99 hκ hκ4 xL xR ρL ρR hd.1 h1'

/-- **`Sec7.Aux106SeparatedStatement` from Theorem 2.2's existence, the one-force inputs and transience.** -/
theorem aux106SeparatedStatement_of_inputs (hex : ExistsEvolutionStatement) (h1 : SeedOneForceTraceStatement.{u})
    (h99 : Aux99Statement.{u}) (htr : Aux106TransienceStatement.{u}) : Aux106SeparatedStatement.{u} := by
  intro κ hκ hκ4 h2 xL xR ρL ρR hF hside Ω mΩ P _ 𝓕 W VL VR B ζ hE
  have hsep : ∀ i j, xL i < xR j := by
    intro i j
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
    rcases hside with h | h
    · exact h.trans_le (hF.2.2.2 0)
    · exact (hF.2.1 0).trans_lt h
  have htrace := ae_isGeneratingTrace_lifetime hκ hex (distinctCompleteBelow_two h1 h99 hκ hκ4) hE hF
    (by norm_num) (by norm_num) (Or.inl hsep)
  filter_upwards [htrace, htr κ hκ hκ4 h2 xL xR ρL ρR hF hside P 𝓕 W VL VR B ζ hE] with ω ⟨η, hη⟩ ht
  refine ⟨η, hη, fun htop => ?_⟩
  rw [htop] at hη
  exact ht htop η hη

end Sec7

end InteractingSLE
