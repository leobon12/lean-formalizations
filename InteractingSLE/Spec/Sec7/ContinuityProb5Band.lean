/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.ContinuityProb5Weights
import InteractingSLE.Spec.Sec7.ContinuityProb4Band

/-!
# §7.3: band transfer on an infinite band (whole-tail Girsanov)

Packet PROVE-SEC7-C5. Specification §7.3, Aux. lemma 106 (`source/spec/p337-384.md` L392, p. 354): "On the final
infinite band, deleting the opposite mark has finite energy, bounded by a constant times `∫ D^{-2} dt`. Apply the
bounded-energy comparison from each adapted band starting time with an additional integer angular-clock cutoff, and take
the countable union. This transfers the one-force transience assertion"; Aux. lemma 101 (p. 348) and the infinite final
band of Aux. lemma 102.

**`Band.ae_traceEvent_of_changeWeights_tail`**: PROVE-SEC7-C4's band transfer `ae_isGeneratingTrace_of_changeWeights`
for a stopping time `τ ≤ ζ` that need not be bounded, under a bounded energy of the change of drift before `τ`, with the
full trace event as conclusion: almost surely the driver has a continuous generating trace on `[0, τ]`, which tends to
infinity when `τ = ∞`. The proof is C4's, with the whole-tail change of weights
(`Sec2.IsSLEEvolutionUpTo.girsanov_changeWeights_tail`) in place of the bounded one; when the new solution and the band
both last forever, the trace event of the new solution's code at `⊤` includes its transience.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

namespace Band

open Sec2 Sec2.Assembly Sec2.Restart RandRestart Girsanov

variable {nL nR : ℕ} {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ τ : Ω → ℝ≥0∞}

/-- **Band transfer on an infinite band.** Let `(W, V, B)` be an evolution of a separated word and `τ ≤ ζ` a stopping
time (not necessarily bounded) before which every mark whose weight changes from `(ρL; ρR)` to `(ρL'; ρR')` stays at
distance `≥ δ > 0` from the driver, with energy of the change of drift at most `K` before `τ`. If Wiener-almost every
path drives a solution of the new word from the same start with the full trace event, then almost surely the driver has
the trace event up to `τ`: a continuous generating trace on `[0, τ]`, tending to infinity when `τ = ∞`. -/
theorem ae_traceEvent_of_changeWeights_tail [IsProbabilityMeasure P] (hκ : 0 < κ)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hsep : ∀ i j, xL i < xR j)
    (ρL' : Fin nL → ℝ) (ρR' : Fin nR → ℝ) (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω | τ ω ≤ s})
    (hτζ : ∀ ω, τ ω ≤ ζ ω) {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ ω →
      (∀ i, ρL' i ≠ ρL i → δ ≤ |W t ω - VL i t ω|) ∧ ∀ i, ρR' i ≠ ρR i → δ ≤ |W t ω - VR i t ω|)
    {K : ℝ} (hK : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ τ ω →
      ∫ s in (0 : ℝ)..(t : ℝ), shiftIntegrand κ 1 δ (weightDiff ρL ρL' ρR ρR') (W s.toNNReal ω)
        (fun k => allMarks VL VR k s.toNNReal ω) ^ 2 ≤ K)
    (hfull : ∀ᵐ f ∂wienerPath, ((xL, xR), enc f) ∈ lawSetS κ ρL' ρR' (fullTraceSet (nL := nL) (nR := nR))) :
    ∀ᵐ ω ∂P, TraceEvent (fun t => W t ω) (τ ω) := by
  obtain ⟨hQ, hE'⟩ := hE.isSLEEvolutionUpTo.girsanov_changeWeights_tail hκ ρL' ρR' hτ hτζ hδ hgap hK
  set Q := girsanovMeasureTail P 𝓕 B (weightDrift κ δ ρL ρL' ρR ρR' τ ζ W VL VR) with hQdef
  have : IsProbabilityMeasure Q := hQ.isProb
  obtain ⟨B', hm, hc, -, hbm, hae⟩ := QuantumZipper.RS.exists_good_version0 hE'.brownian.1
  have hpm : Measurable fun ω (s : ℝ≥0) => B' s ω := measurable_pi_iff.2 hm
  have hlaw : Q.map (fun ω s => B' s ω) = wienerPath := map_path_eq_wienerPath hbm.toIsPreBrownianReal hpm
  rw [← hlaw] at hfull
  have hgood := ae_of_ae_map hpm.aemeasurable hfull
  have hlim := hQ.ac.ae_le (hE.ae_tendsto_threshold hκ)
  have hpath := hQ.ac.ae_le hE.2.2.2.2
  refine hQ.ac'.ae_le ?_
  filter_upwards [hgood, hae, hE'.ae_path, hlim, hpath] with ω hg hb hp hl hpa
  set f : ℝ≥0 → ℝ := fun s => B' s ω with hf
  obtain ⟨x, ⟨⟨hxF, -⟩, hxS⟩, hxeq⟩ := hg
  simp only [Prod.mk.injEq] at hxeq
  have hxC : x ∈ CRel κ xL xR ρL' ρR' := mem_cRelF_iff.1 ⟨hxF, hxeq.1⟩
  have hxp : IsIntegratedSLEPath κ xL xR ρL' ρR' (cw x) (cvL x) (cvR x) (cb x) (cζ x) := hxC.1.2.2
  have hcb : cb x = f := by
    funext t
    show dec x.1 t = f t
    rw [hxeq.2]
    exact dec_enc (hc ω).continuousWithinAt
  rw [hcb] at hxp
  have hp' : IsSLEPathUpTo κ xL xR ρL' ρR' (fun t => W t ω) (fun i t => VL i t ω) (fun j t => VR j t ω) f
      (τ ω) := hp.congr_b fun t _ => hb t
  obtain ⟨hle, hag⟩ := le_lifetime_of_upTo hsep hp' hxp
  have hcont : ContinuousOn (cw x) {t | (t : ℝ≥0∞) < cζ x} := hxp.isForcePath.continuousOn_w
  rcases hle.lt_or_eq with hlt | heq
  · -- a rational time strictly between `τ` and the new lifetime
    obtain ⟨q, -, hq1, hq2⟩ := ENNReal.lt_iff_exists_rat_btwn.1 hlt
    have hx2 := mem_iInter.1 hxS.2 q hq2
    have hev : TraceEvent (cw x) ((Real.toNNReal q : ℝ≥0) : ℝ≥0∞) := by
      refine (mem_traceSet_iff (hcont.mono fun t ht => ?_) hxp.1 fun _ _ => ?_).1 hx2
      · exact (show (t : ℝ≥0∞) < (Real.toNNReal q : ℝ≥0) from ht).trans hq2
      · refine ⟨cw x (Real.toNNReal q), ?_⟩
        have hopen : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < cζ x} :=
          isOpen_lt ENNReal.continuous_coe continuous_const
        rw [ENNReal.toNNReal_coe]
        exact (hcont.continuousAt (hopen.mem_nhds hq2)).tendsto.mono_left nhdsWithin_le_nhds
    obtain ⟨η, hη, -⟩ := hev
    refine ⟨η, IsGeneratingTrace.congr_lt (hη.mono_horizon hq1.le) fun t ht => (hag t ht).1, fun htop => ?_⟩
    exact absurd (htop ▸ hq1 : (⊤ : ℝ≥0∞) < _) not_top_lt
  · -- the new solution dies exactly at `τ`: it inherits the left limit of the driver there
    have hHL : HasLimW x := by
      intro h0 hfin
      have hTζ : (((cζ x).toNNReal : ℝ≥0) : ℝ≥0∞) = cζ x := ENNReal.coe_toNNReal hfin.ne
      have hT0 : 0 < (cζ x).toNNReal := by
        have : (0 : ℝ≥0∞) < ((cζ x).toNNReal : ℝ≥0∞) := by rw [hTζ]; exact h0
        exact_mod_cast this
      have hW : ∃ w₀ : ℝ, Tendsto (fun t => W t ω) (𝓝[<] (cζ x).toNNReal) (𝓝 w₀) := by
        rcases (hτζ ω).lt_or_eq with hlt' | heq'
        · refine ⟨W (cζ x).toNNReal ω, ?_⟩
          have hopen : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < ζ ω} :=
            isOpen_lt ENNReal.continuous_coe continuous_const
          have hlt'' : (((cζ x).toNNReal : ℝ≥0) : ℝ≥0∞) < ζ ω := by rw [hTζ, ← heq]; exact hlt'
          exact (hpa.isForcePath.continuousOn_w.continuousAt (hopen.mem_nhds hlt'')).tendsto.mono_left
            nhdsWithin_le_nhds
        · have hTz : (((cζ x).toNNReal : ℝ≥0) : ℝ≥0∞) = ζ ω := by rw [hTζ, ← heq, heq']
          obtain ⟨w₀, vL₀, vR₀, hlim', -⟩ := hl _ hT0 hTz
          exact ⟨w₀, ((continuous_fst.tendsto _).comp hlim')⟩
      obtain ⟨w₀, hw₀⟩ := hW
      refine ⟨w₀, hw₀.congr' ?_⟩
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht' : (t : ℝ≥0∞) < τ ω := by rw [heq, ← hTζ]; exact_mod_cast ht
      exact (hag t ht').1
    have hev : TraceEvent (cw x) (cζ x) := (mem_traceCodeSet_iff hxF hHL).1 hxS.1
    rw [← heq] at hev
    exact TraceEvent.congr hev fun t ht => ((hag t ht).1).symm

end Band

end Sec7

end InteractingSLE
