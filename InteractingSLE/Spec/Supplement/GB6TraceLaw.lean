/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6TraceKernel

/-!
# Proposition GB6: the conditional counterflow under one conditional law — (f) and the protected tails

Packet PROVE-GB6D. **`gb6_kernel`**: under one conditional law `Q` on `GB6Space` with an admissible sorted word `c`, if
the chart field is a GFF with `c`, the code decoded before its lifetime drives the counterflow of the chart field at
`16/κ` and matches the canonical driver code `F (c, ·)` (the output of PROVE-RESTARTKERNEL's general kernel), the code
is good, and the junction coordinates bound the protected tails of `c`, then:

* **(f)** `IsGB6ConditionalCounterflow κ c Q gb6Field gb6WC gb6Γ` — the lifetime is infinite
  (`ae_lifetime_eq_top_of_admData`), so the code coincides with `F (c, ·)` on all dyadic times and the driver decoded
  on `[0, ∞)` again drives the counterflow (`Restart.IsCanonicalDriverCode`), with lifetime `⊤`; the complete
  finite-force
  theorem at `16/κ` (`CompleteSixteenDivStatement`) gives a continuous transient generating trace, which is `gb6Γ`;
* almost surely `IsGB6KernelGood`: in particular the trace avoids the closed tails `[jR, ∞)`, `(−∞, jL]` (GB5 at the
  junctions, simultaneously for all thresholds by `ae_forall_of_upClosed`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Supp8

namespace GB6

open Restart Sec2.Assembly LQGMetric Sec7.RandRestart

/-- **(f) and the protected tails under one conditional law.** -/
theorem gb6_kernel {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hC : CompleteSixteenDivStatement)
    {F : BoundaryWord × DistOn upperHalfPlaneOpens → PCode × ℝ≥0∞} (hF : IsCanonicalDriverCode (16 / κ) 0 F)
    {c : BoundaryWord} (hcs : c.IsSorted) (hadm : IsGB6AdmData κ c)
    {Q : Measure GB6Space} [IsProbabilityMeasure Q]
    (hgff : IsGFFWithBoundaryData Q gb6Field c.fn c.jumps)
    (hfl : IsFlowLineDriver (16 / κ) c.fn c.jumps 0 Q gb6Field gb6WCl gb6L)
    (hgood : ∀ᵐ x ∂Q, IsGoodDrvCode (gb6Code x))
    (hmatch : ∀ᵐ x ∂Q, IsDriverCodeMatch (F (c, gb6Field x)) (fun t => gb6WCl t x) (gb6L x))
    (htail : ∀ᵐ x ∂Q, IsGB6TailData κ c (gb6JL x) (gb6JR x)) :
    IsGB6ConditionalCounterflow κ c Q gb6Field gb6WC gb6Γ ∧ ∀ᵐ x ∂Q, IsGB6KernelGood x := by
  -- the infinite lifetime of the decoded code
  obtain ⟨_, 𝓕, VL, VR, B, _, hcpl⟩ := hfl
  have hLtop : ∀ᵐ x ∂Q, gb6L x = ⊤ := ae_lifetime_eq_top_of_admData hκ hadm hcpl.1
  -- the code is the canonical code
  have hcode : ∀ᵐ x ∂Q, gb6Code x = F (c, gb6Field x) := by
    filter_upwards [hLtop, hgood, hmatch] with x hL hg hm
    obtain ⟨hl, -, hd⟩ := hm
    refine Prod.ext (funext fun n => funext fun k => ?_) (hL.trans (hL ▸ hl))
    have hdk : (dyad n k : ℝ≥0∞) < gb6L x := by rw [hL]; exact ENNReal.coe_lt_top
    have h1 := hd n k hdk
    have h2 : gb6WCl (dyad n k) x = (gb6Code x).1 n k := by
      have hg' : (dyad n k : ℝ≥0∞) < (gb6Code x).2 := hdk
      show drvDec (gb6Code x) (dyad n k) = _
      rw [drvDec_of_good hg (by show 0 < gb6L x; rw [hL]; exact ENNReal.zero_lt_top)]
      exact (hg n k hg').dec_dyad le_rfl
    rw [← h2]; exact h1
  -- the driver on `[0, ∞)`
  have hfl' : IsFlowLineDriver (16 / κ) c.fn c.jumps 0 Q gb6Field gb6WC (fun _ => ⊤) := by
    refine hF.2.1 c hcs Q gb6Field gb6WC (fun _ => ⊤) hgff measurable_gb6WC measurable_const
      (fun x => (continuous_gb6WC x).continuousOn) ?_
    filter_upwards [hLtop, hgood, hcode] with x hL hg hc
    rw [← hc]
    exact isDriverCodeMatch_drvDecTop (uc_of_good_top hg hL) hL
  obtain ⟨_, 𝓕', VL', VR', B', _, hcpl'⟩ := hfl'
  have hE' := hcpl'.1
  have hword := Theorem15.isOrderedForceWord_flowLine c.fn c.jumps 0
  have hcomp := hC κ hκ hκ4 _ _ (flowLineRhoL (16 / κ) c.fn c.jumps 0 0) (flowLineRhoR (16 / κ) c.fn c.jumps 0 0)
    hword Q 𝓕' gb6WC VL' VR' B' (fun _ => ⊤) hE'
  -- the complete trace
  have htg : ∀ᵐ x ∂Q, gb6TraceGood x := by
    filter_upwards [hcomp] with x ⟨η, hη, htr⟩
    have hw0 : gb6WC 0 x = 0 := Sec7.SideHeight.w_zero_of_isGeneratingTrace hη (by simp)
    exact ⟨(mem_traceSet_iff (continuous_gb6WC x).continuousOn hw0 fun _ h => absurd h (lt_irrefl _)).2
      ⟨η, hη, htr⟩, hw0⟩
  have hgen : ∀ᵐ x ∂Q, IsGeneratingTrace (fun t => gb6WC t x) ⊤ (gb6Γ x) ∧
      Tendsto (fun t => ‖gb6Γ x t‖) atTop atTop := by
    filter_upwards [htg] with x hx using isGeneratingTrace_gb6Γ hx
  have hcf : IsGB6ConditionalCounterflow κ c Q gb6Field gb6WC gb6Γ := ⟨hgff, ⟨_, 𝓕', VL', VR', B', ‹_›, hcpl'⟩, hgen⟩
  refine ⟨hcf, ?_⟩
  -- the protected tails, simultaneously for all thresholds
  have hη : ∀ᵐ x ∂Q, IsGeneratingTrace (fun t => gb6WC t x) ⊤ (gb6Γ x) := hgen.mono fun x h => h.1
  have hζ : ∀ᵐ x ∂Q, (fun _ : GB6Space => (⊤ : ℝ≥0∞)) x = ⊤ := Eventually.of_forall fun _ => rfl
  set UR : Set ℝ := {p | 0 < p ∧ ∀ y, p < y → y ∉ c.jumps → tailLevel κ ≤ c.fn y} with hURdef
  set UL : Set ℝ := {p | 0 < p ∧ ∀ y, y < -p → y ∉ c.jumps → c.fn y ≤ -tailLevel κ} with hULdef
  have hR : ∀ᵐ x ∂Q, ∀ p ∈ UR, ∀ t : ℝ≥0, ∀ y : ℝ, p ≤ y → gb6Γ x t ≠ y :=
    ae_forall_of_upClosed (U := UR) (A := fun p x => ∀ t : ℝ≥0, ∀ y : ℝ, p ≤ y → gb6Γ x t ≠ y) (fun p hp => hp.1)
      (fun p hp p' hpp' => ⟨hp.1.trans_le hpp', fun y hy hyJ => hp.2 y (hpp'.trans_lt hy) hyJ⟩)
      (fun p hp => ae_trace_ne_of_ge_word hκ hadm hp.1 hp.2 hE' hζ hη)
      (fun p p' x hpp' h t y hy => h t y (hpp'.trans hy))
  have hL : ∀ᵐ x ∂Q, ∀ p ∈ UL, ∀ t : ℝ≥0, ∀ y : ℝ, y ≤ -p → gb6Γ x t ≠ y :=
    ae_forall_of_upClosed (U := UL) (A := fun p x => ∀ t : ℝ≥0, ∀ y : ℝ, y ≤ -p → gb6Γ x t ≠ y) (fun p hp => hp.1)
      (fun p hp p' hpp' => ⟨hp.1.trans_le hpp', fun y hy hyJ => hp.2 y (by linarith) hyJ⟩)
      (fun p hp => ae_trace_ne_of_le_word hκ hadm (neg_neg_of_pos hp.1) hp.2 hE' hζ hη)
      (fun p p' x hpp' h t y hy => h t y (by linarith))
  filter_upwards [hLtop, hgood, htg, hR, hL, htail] with x hLx hgx htgx hRx hLx' htx
  refine ⟨hLx, uc_of_good_top hgx hLx, htgx, fun t => tailGap_pos_iff.2 ?_⟩
  rintro ⟨him, hre⟩
  obtain ⟨hjL, hjR, htR, htL⟩ := htx
  have heq : gb6Γ x t = ((gb6Γ x t).re : ℂ) := by
    apply Complex.ext <;> simp [him]
  rcases hre with hre | hre
  · exact hRx (gb6JR x) ⟨hjR, htR⟩ t _ hre heq
  · exact hLx' (-gb6JL x) ⟨by linarith, fun y hy hyJ => htL y (by linarith) hyJ⟩ t _ (by linarith) heq

end GB6

end Supp8

end InteractingSLE
