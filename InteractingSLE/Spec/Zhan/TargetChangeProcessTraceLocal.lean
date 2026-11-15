/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.TargetChangeProcessTraceClose
import InteractingSLE.Spec.Sec7.ContinuityProb4Aux113
import InteractingSLE.Spec.Sec2.Assembly2Entr

/-!
# A local evolution of a complete separated word has a trace up to its horizon

Packet PROVE-SEC7-C10 (step R5 of `planning/handoffs/PROVE-SEC7-C8.md`). Let `(W, V, B)` be a local integrated
`SLE_κ(ρ)` evolution (`Sec2.IsSLEEvolutionUpTo`) before a random time `τ`, of an ordered word with a separated start
(`xL i < xR j`) that is complete (`LP.IsCompleteForceWord`: every evolution has a continuous trace up to and including
a finite continuation threshold, transient on infinite lifetime). Then almost surely the driver has a generating trace
on `[0, τ]`, transient when `τ = ∞` (`Sec2.IsSLEEvolutionUpTo.ae_trace_of_complete`).

Proof (the template of `Sec7.Band.ae_isGeneratingTrace_of_changeWeights` without its Girsanov step): Wiener-almost
every path drives a solution with the full trace event (`ae_mem_lawSetS_fullTraceSet`, the solvability from Theorem
2.2's existence); a good version of `B` has the Wiener law, so almost surely its path drives such a solution; by
pathwise uniqueness for a separated start the local path agrees with it before `τ ≤ ζ`
(`Sec7.Band.le_lifetime_of_upTo`). If `τ` is strictly below the lifetime, a rational trace event between them gives
the trace; if `τ` is the lifetime, the coded trace event of the lifetime gives it — on an infinite lifetime by the
transient coding, on a finite one by the coded uniform continuity (`exists_isGeneratingTrace_of_finCond`), which needs
no left limit of the driver.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Zhan

namespace Retarget

open Sec2 Sec2.Assembly Sec2.Restart Sec7 Sec7.RandRestart Sec7.Band

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {Q : Measure Ω} {𝓘 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {τ : Ω → ℝ≥0∞}

/-- **R5: a local evolution of a complete separated word has a trace up to its horizon.** -/
theorem _root_.InteractingSLE.Sec2.IsSLEEvolutionUpTo.ae_trace_of_complete [IsProbabilityMeasure Q]
    (hκ : 0 < κ) (hE : Sec2.IsSLEEvolutionUpTo κ xL xR ρL ρR Q 𝓘 W VL VR B τ) (hF : IsOrderedForceWord xL xR)
    (hsep : ∀ i j, xL i < xR j) (hc : LP.IsCompleteForceWord.{u} κ xL xR ρL ρR) :
    ∀ᵐ p ∂Q, ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t p) (τ p) η ∧
      (τ p = ⊤ → Tendsto (fun t => ‖η t‖) atTop atTop) := by
  -- Wiener-almost every path drives a solution with the full trace event
  obtain ⟨Ω₀, mΩ₀, P₀, hP₀, 𝓕₀, W₀, VL₀, VR₀, B₀, ζ₀, hE₀⟩ := exists_isIntegratedSLEEvolution_assembled hκ hF
  have hsolv := ae_solvable_of_isIntegratedSLEEvolution hκ hsep hE₀
  have hfull := ae_mem_lawSetS_fullTraceSet hκ (s := (xL, xR)) hc hsep hsolv
  -- a good version of `B` has the Wiener law
  obtain ⟨B', hm, hcB, -, hbm, hae⟩ := QuantumZipper.RS.exists_good_version0 hE.brownian.1
  have hpm : Measurable fun p (s : ℝ≥0) => B' s p := measurable_pi_iff.2 hm
  have hlaw : Q.map (fun p s => B' s p) = wienerPath := map_path_eq_wienerPath hbm.toIsPreBrownianReal hpm
  rw [← hlaw] at hfull
  have hgood := ae_of_ae_map hpm.aemeasurable hfull
  filter_upwards [hgood, hae, hE.ae_path] with p hg hb hp
  set f : ℝ≥0 → ℝ := fun s => B' s p with hf
  obtain ⟨x, ⟨⟨hxF, -⟩, hxS⟩, hxeq⟩ := hg
  simp only [Prod.mk.injEq] at hxeq
  have hxC : x ∈ CRel κ xL xR ρL ρR := mem_cRelF_iff.1 ⟨hxF, hxeq.1⟩
  have hxp : IsIntegratedSLEPath κ xL xR ρL ρR (cw x) (cvL x) (cvR x) (cb x) (cζ x) := hxC.1.2.2
  have hcb : cb x = f := by
    funext t
    show dec x.1 t = f t
    rw [hxeq.2]
    exact dec_enc (hcB p).continuousWithinAt
  rw [hcb] at hxp
  have hp' : IsSLEPathUpTo κ xL xR ρL ρR (fun t => W t p) (fun i t => VL i t p) (fun j t => VR j t p) f
      (τ p) := hp.congr_b fun t _ => hb t
  obtain ⟨hle, hag⟩ := le_lifetime_of_upTo hsep hp' hxp
  have hcont : ContinuousOn (cw x) {t | (t : ℝ≥0∞) < cζ x} := hxp.isForcePath.continuousOn_w
  have hw0 : cw x 0 = 0 := hxp.1
  -- trace events at rational times before the lifetime
  have hratEv : ∀ r : ℚ, ((Real.toNNReal r : ℝ≥0) : ℝ≥0∞) < cζ x →
      TraceEvent (cw x) ((Real.toNNReal r : ℝ≥0) : ℝ≥0∞) := by
    intro r hr
    have hx2 := mem_iInter.1 hxS.2 r hr
    refine (mem_traceSet_iff (hcont.mono fun t ht => ?_) hw0 fun _ _ => ?_).1 hx2
    · exact (show (t : ℝ≥0∞) < (Real.toNNReal r : ℝ≥0) from ht).trans hr
    · refine ⟨cw x (Real.toNNReal r), ?_⟩
      have hopen : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < cζ x} :=
        isOpen_lt ENNReal.continuous_coe continuous_const
      rw [ENNReal.toNNReal_coe]
      exact (hcont.continuousAt (hopen.mem_nhds hr)).tendsto.mono_left nhdsWithin_le_nhds
  rcases hle.lt_or_eq with hlt | heq
  · obtain ⟨q, -, hq1, hq2⟩ := ENNReal.lt_iff_exists_rat_btwn.1 hlt
    obtain ⟨η, hη, -⟩ := hratEv q hq2
    refine ⟨η, IsGeneratingTrace.congr_lt (hη.mono_horizon hq1.le) fun t ht => (hag t ht).1, fun htop => ?_⟩
    rw [htop] at hq1
    exact absurd hq1 (not_lt.2 le_top)
  have hx1 : (cw x, cζ x) ∈ traceSet := hxS.1
  rcases eq_or_ne (cζ x) ⊤ with htop | hfin
  · -- infinite lifetime: the transient coding
    have hc' : Continuous (cw x) := by
      rw [← continuousOn_univ]
      exact hcont.mono fun t _ => show (t : ℝ≥0∞) < cζ x by rw [htop]; exact ENNReal.coe_lt_top
    have hx1' : ratVals (cw x) ∈ transientSet := by
      rcases hx1 with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · exact absurd htop h
    obtain ⟨η, hη, htr⟩ := (mem_transientSet_iff hc' hw0).1 hx1'
    refine ⟨η, ?_, fun _ => htr⟩
    rw [heq, htop]
    exact IsGeneratingTrace.congr_lt hη fun t ht => (hag t (by rw [heq, htop]; exact ht)).1
  -- finite lifetime: the coded uniform continuity
  set Z := (cζ x).toNNReal with hZ
  have hZ' : ((Z : ℝ≥0) : ℝ≥0∞) = cζ x := ENNReal.coe_toNNReal hfin
  have hfc : FinCond (cw x) (cζ x) := by
    rcases hx1 with ⟨h, -⟩ | ⟨-, h⟩
    · exact absurd h hfin
    · exact h
  have hrat : ∀ t : ℝ≥0, t < Z → ∃ q : ℝ≥0, t < q ∧ q < Z ∧ ∃ η, IsGeneratingTrace (cw x) q η := by
    intro t ht
    obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show (t : ℝ) < Z by exact_mod_cast ht)
    have hr0 : (0 : ℝ) ≤ r := t.coe_nonneg.trans hr1.le
    have hrZ : Real.toNNReal r < Z := by rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hr0]; exact hr2
    refine ⟨Real.toNNReal r, ?_, hrZ, ?_⟩
    · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hr0]; exact hr1
    · obtain ⟨η, hη, -⟩ := hratEv r (by rw [← hZ']; exact_mod_cast hrZ)
      exact ⟨η, hη⟩
  rw [← hZ'] at hfc hcont
  obtain ⟨η, hη⟩ := exists_isGeneratingTrace_of_finCond hcont hw0 hrat hfc
  refine ⟨η, ?_, fun h => absurd (heq.symm.trans h) hfin⟩
  rw [heq, ← hZ']
  exact IsGeneratingTrace.congr_lt hη fun t ht => (hag t (by rw [heq, ← hZ']; exact ht)).1

end Retarget

end Zhan

end InteractingSLE
