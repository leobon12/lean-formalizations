/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.ContinuityProb3Coding
import InteractingSLE.Spec.Sec7.ContinuityProb3Kernel
import InteractingSLE.Spec.Sec7.ContinuityProb3Lift

/-!
# §7.3: the restart with a random force word (`Sec7.RandomRestartTraceStatement`)

Packet PROVE-RANDRESTART2. PROVE-SEC7-C3's open input `Sec7.RandomRestartTraceStatement κ`: if `T` is a finite
stopping time, `A ∈ 𝓕_T`, `T < ζ` on `A`, and at every `ω ∈ A` the force word `V_T − W_T` is complete, then almost
surely on `A` the shifted driver `W_{T+·} − W_T` has a continuous generating trace up to `ζ − T`, transient when
`ζ − T = ∞`. Proved here for every `κ > 0` (`randomRestartTraceStatement`).

Proof.
* On `A ∩ {T > 0}` (the restarted word is separated, `sepStart_restart`): by the conditional law at `T`
  (`measure_restart_codeEvent`, with the Borel trace coding `traceCodeSet`),
  `P(A ∩ {no trace}) = ∫_A codeLaw (traceCodeSet)ᶜ (V_T − W_T) dP`. Almost surely on `A` the realized word `s` is
  separated and Wiener-almost every path drives a solution from it (`ae_solvable_restart`), so an evolution from `s`
  exists in the universe of `Ω` (`exists_isIntegratedSLEEvolution_of_ae_wienerPath`); `s` is complete, so that
  evolution has the trace almost surely, and by the canonical law (`measure_eventOf_eq_codeLaw`)
  `codeLaw (traceCodeSet)ᶜ s = 0`.
* On `A ∩ {T = 0}`: the word at `T` is the initial word `(xL; xR)` almost surely, which is then complete (if
  `A ∩ {T = 0}` is not null), and the shifted driver is `W` itself.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Sec7

namespace RandRestart

open Sec2 Sec2.Assembly Sec2.Restart

variable {nL nR : ℕ}

/-! ### The trace event on solution codes -/

theorem measurable_cw_cζ : Measurable fun x : XCode nL nR => (cw x, cζ x) :=
  (measurable_pi_iff.2 fun t => measurable_dec_at measurable_code_w t).prodMk measurable_cζ

/-- The Borel set of solution codes whose driver has the trace event up to the lifetime. -/
def traceCodeSet : Set (XCode nL nR) := (fun x => (cw x, cζ x)) ⁻¹' traceSet

theorem measurableSet_traceCodeSet : MeasurableSet (traceCodeSet (nL := nL) (nR := nR)) :=
  measurable_cw_cζ measurableSet_traceSet

theorem mem_traceCodeSet_iff {a : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {x : XCode nL nR}
    (hx : x ∈ CRelF a ρL ρR) (hl : HasLimW x) : x ∈ traceCodeSet ↔ TraceEvent (cw x) (cζ x) := by
  have hp : IsIntegratedSLEPath a (startOf x).1 (startOf x).2 ρL ρR (cw x) (cvL x) (cvR x) (cb x) (cζ x) :=
    hx.1.2.2
  exact mem_traceSet_iff hp.2.2.2.1 hp.1 hl

theorem compl_traceCodeSet_iff {a : ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} :
    ∀ x ∈ CRelF a ρL ρR, HasLimW x → (x ∈ (traceCodeSet (nL := nL) (nR := nR))ᶜ ↔
      (fun w τ => ¬ TraceEvent w τ) (cw x) (cζ x)) := fun x hx hl => by
  rw [mem_compl_iff, mem_traceCodeSet_iff hx hl]

theorem not_traceEvent_congr (w w' : ℝ≥0 → ℝ) (τ : ℝ≥0∞)
    (h : ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ → w t = w' t) (hn : ¬ TraceEvent w τ) : ¬ TraceEvent w' τ :=
  fun hw' => hn (hw'.congr fun t ht => (h t ht).symm)

/-! ### Complete words have canonical trace law one -/

/-- **A complete separated word at which Wiener-almost every path is solvable has canonical probability zero of
no trace.** -/
theorem codeLaw_compl_traceCodeSet_eq_zero {κ : ℝ} (hκ : 0 < κ) {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {s : (Fin nL → ℝ) × (Fin nR → ℝ)} (hc : LP.IsCompleteForceWord.{u} κ s.1 s.2 ρL ρR)
    (hsep : SepStart s) (hsolv : ∀ᵐ f ∂wienerPath, enc f ∈ Prod.fst '' CRel κ s.1 s.2 ρL ρR) :
    codeLaw κ ρL ρR (traceCodeSet (nL := nL) (nR := nR))ᶜ s = 0 := by
  obtain ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, hE⟩ :=
    exists_isIntegratedSLEEvolution_of_ae_wienerPath.{u} hsep hsolv
  have htr : ∀ᵐ ω ∂P, TraceEvent (fun t => W t ω) (ζ ω) := hc P 𝓕 W VL VR B ζ hE
  have e := measure_eventOf_eq_codeLaw hκ hsep hE (Φ := fun w τ => ¬ TraceEvent w τ)
    measurableSet_traceCodeSet.compl compl_traceCodeSet_iff not_traceEvent_congr
  rw [← e]
  exact ae_iff.1 htr

/-! ### The restart with a random word -/

/-- **`Sec7.RandomRestartTraceStatement κ` for every `κ > 0`**: restart at a stopping time where the force word is
random and every realized word is complete. -/
theorem randomRestartTraceStatement {κ : ℝ} (hκ : 0 < κ) : RandomRestartTraceStatement.{u} κ := by
  intro nL nR xL xR ρL ρR Ω mΩ P _ 𝓕 W VL VR B ζ hE T hT A hA hAζ hcomp
  set Z : Set Ω := {ω | (T ω : WithTop ℝ≥0) ≤ 0} with hZ
  have hZm : MeasurableSet[hT.measurableSpace] Z := hT.measurableSet_le' 0
  have hT0 : ∀ ω ∈ Z, T ω = 0 := fun ω hω => le_zero_iff.1 (WithTop.coe_le_coe.1 hω)
  have hTpos : ∀ ω ∉ Z, 0 < T ω := fun ω hω =>
    pos_iff_ne_zero.2 fun h => hω (show (T ω : WithTop ℝ≥0) ≤ 0 by rw [h]; exact le_rfl)
  -- the part where `T > 0`
  have hA1 : MeasurableSet[hT.measurableSpace] (A ∩ Zᶜ) := hA.inter hZm.compl
  have hA1m : MeasurableSet (A ∩ Zᶜ) := hT.measurableSpace_le _ hA1
  have hAT : ∀ ω ∈ A ∩ Zᶜ, (T ω : ℝ≥0∞) < ζ ω ∧ (0 < T ω ∨ ∀ i j, xL i < xR j) := fun ω hω =>
    ⟨hAζ ω hω.1, Or.inl (hTpos ω hω.2)⟩
  have hlaw := measure_restart_codeEvent hκ hE hT hA1 hAT (Φ := fun w τ => ¬ TraceEvent w τ)
    measurableSet_traceCodeSet.compl compl_traceCodeSet_iff not_traceEvent_congr
  have hzero : ∫⁻ ω in A ∩ Zᶜ, codeLaw κ ρL ρR (traceCodeSet (nL := nL) (nR := nR))ᶜ
      (wordAt W VL VR T ω) ∂P = 0 := by
    refine (setLIntegral_congr_fun_ae hA1m ?_).trans (setLIntegral_const _ 0 |>.trans (zero_mul _))
    filter_upwards [ae_solvable_restart hκ hE hT hA1 hAT] with ω h hω
    exact codeLaw_compl_traceCodeSet_eq_zero hκ (hcomp ω hω.1) (h hω).1 (h hω).2
  rw [hzero] at hlaw
  have h1 : ∀ᵐ ω ∂P, ω ∈ A ∩ Zᶜ → TraceEvent (fun t => W (T ω + t) ω - W (T ω) ω) (ζ ω - T ω) := by
    rw [ae_iff]
    refine le_antisymm (le_of_eq_of_le ?_ hlaw.le) bot_le
    congr 1
    ext ω
    simp only [mem_ofPred_eq, Classical.not_imp, mem_inter_iff]
  -- the part where `T = 0`
  have h0 : ∀ᵐ ω ∂P, ω ∈ A ∩ Z → TraceEvent (fun t => W (T ω + t) ω - W (T ω) ω) (ζ ω - T ω) := by
    by_cases hc0 : LP.IsCompleteForceWord.{u} κ xL xR ρL ρR
    · filter_upwards [(hc0 P 𝓕 W VL VR B ζ hE : ∀ᵐ ω ∂P, TraceEvent (fun t => W t ω) (ζ ω)),
        hE.2.2.2.2] with ω htr hp hω
      rw [hT0 ω hω.2, ENNReal.coe_zero, tsub_zero]
      refine TraceEvent.congr htr fun t _ => ?_
      simp only [zero_add, hp.1, sub_zero]
    · filter_upwards [hE.2.2.2.2] with ω hp hω
      exfalso
      refine hc0 ?_
      have hc : LP.IsCompleteForceWord.{u} κ (fun i => VL i (T ω) ω - W (T ω) ω)
          (fun j => VR j (T ω) ω - W (T ω) ω) ρL ρR := hcomp ω hω.1
      have hw0 : W 0 ω = 0 := hp.1
      have e1 : (fun i => VL i (T ω) ω - W (T ω) ω) = xL := funext fun i => by
        have : VL i 0 ω = xL i := hp.2.1 i
        rw [hT0 ω hω.2, this, hw0, sub_zero]
      have e2 : (fun j => VR j (T ω) ω - W (T ω) ω) = xR := funext fun j => by
        have : VR j 0 ω = xR j := hp.2.2.1 j
        rw [hT0 ω hω.2, this, hw0, sub_zero]
      rwa [e1, e2] at hc
  filter_upwards [h1, h0] with ω h1 h0 hω
  by_cases hωZ : ω ∈ Z
  · exact h0 ⟨hω, hωZ⟩
  · exact h1 ⟨hω, hωZ⟩

end RandRestart

end Sec7

end InteractingSLE
