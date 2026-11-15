/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.Prop418RangeCode
import InteractingSLE.Spec.Wire.WangWu
import InteractingSLE.Spec.Sec7.ContinuityProb3Kernel

/-!
# The image driver of the contact step, part 4: the Borel code of a simple transient trace

Packet PROVE-WW-B16, step B7 of PROVE-WW-B15's plan. Wang–Wu (`source/external/WW17LP/wang_wu_lean_preprocessed.pdf`,
ruling R31), Lemma 2.10 (Borel trace events: "Endpoint continuity, simplicity, avoidance of a specified marked point at
positive times, and transience are Borel events in this coding"), Lemma 4.12 and Corollary 4.13 (proved:
`Wire.ae_simple_transient_trace`).

* `goodCode`: solution codes with infinite lifetime whose driver has a transient generating trace on `[0, ∞)`, read at
  every time by the measurable trace evaluation (`codeLine`), with the two window conditions (`ImPosCond`: in `ℍ` at
  positive times, uniformly on rational windows; `SepCond`: separated rational windows) — a Borel set
  (`measurableSet_goodCode`) on which the trace is a simple proper Loewner trace (`trace_of_mem_goodCode`);
* **`codeLaw_compl_goodCode_eq_zero`**: at every strictly separated ordered word with nonnegative cumulative weights,
  Wiener-almost every driving path drives a canonical `SLE₄(ρ)` solution whose code is good (Lemma 4.12 and Corollary
  4.13 through the canonical law, `Sec7.RandRestart.measure_eventOf_eq_codeLaw`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open QuantumZipper (H fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.WangWu

namespace ImgDrv

open Sec2 Sec2.Assembly Sec2.Restart Sec7.RandRestart

variable {nL nR : ℕ}

/-! ### The good code set -/

/-- **The good path predicate**: infinite lifetime, a transient generating trace on `[0, ∞)`, and the two window
conditions on the trace read through `LP.traceAt`. -/
def GoodPath (w : ℝ≥0 → ℝ) (ζ : ℝ≥0∞) : Prop :=
  ζ = ⊤ ∧ (w, (⊤ : ℝ≥0∞)) ∈ traceSet ∧ ImPosCond (fun s : ℝ => LP.traceAt s.toNNReal w) ∧
    SepCond (fun s : ℝ => LP.traceAt s.toNNReal w)

/-- **The good codes.** -/
def goodCode : Set (XCode nL nR) :=
  {x | cζ x = ⊤} ∩ {x | (cw x, (⊤ : ℝ≥0∞)) ∈ traceSet} ∩ {x | ImPosCond (codeLine x)} ∩
    {x | SepCond (codeLine x)}

theorem measurableSet_goodCode : MeasurableSet (goodCode (nL := nL) (nR := nR)) :=
  (((measurable_cζ (measurableSet_singleton ⊤)).inter
    ((Exist.measurable_cw.prodMk measurable_const) measurableSet_traceSet)).inter
    measurableSet_imPosCond).inter measurableSet_sepCond

theorem mem_goodCode_iff {x : XCode nL nR} : x ∈ goodCode ↔ GoodPath (cw x) (cζ x) := by
  simp only [goodCode, GoodPath, mem_inter_iff, mem_ofPred_eq, and_assoc]
  exact Iff.rfl

theorem goodPath_congr (w w' : ℝ≥0 → ℝ) (τ : ℝ≥0∞) (h : ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ → w t = w' t)
    (hw : GoodPath w τ) : GoodPath w' τ := by
  have hτ : τ = ⊤ := hw.1
  have e : w = w' := funext fun t => h t (by rw [hτ]; exact ENNReal.coe_lt_top)
  rw [← e]
  exact hw

theorem not_goodPath_congr (w w' : ℝ≥0 → ℝ) (τ : ℝ≥0∞) (h : ∀ t : ℝ≥0, (t : ℝ≥0∞) < τ → w t = w' t)
    (hw : ¬ GoodPath w τ) : ¬ GoodPath w' τ := fun h' =>
  hw (goodPath_congr w' w τ (fun t ht => (h t ht).symm) h')

/-- **A good path has a simple proper generating trace**: the driver is continuous, and the trace read through
`LP.traceAt` is a generating trace on `[0, ∞)` which, as a curve on `ℝ`, is a simple proper Loewner trace. -/
theorem GoodPath.trace {w : ℝ≥0 → ℝ} (hwc : Continuous w) (hw0 : w 0 = 0) (hg : GoodPath w ⊤) :
    ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace w ⊤ η ∧ Tendsto (fun t => ‖η t‖) atTop atTop ∧
      (fun s : ℝ => LP.traceAt s.toNNReal w) = (fun s : ℝ => η s.toNNReal) ∧
      IsLoewnerTrace (Ito.rpath w) (fun s : ℝ => η s.toNNReal) ∧ IsProperArc (fun s : ℝ => η s.toNNReal) := by
  obtain ⟨-, htr, him, hsep⟩ := hg
  have hc : ContinuousOn w {t : ℝ≥0 | (t : ℝ≥0∞) < ⊤} := hwc.continuousOn
  obtain ⟨η, hη, htend⟩ := (mem_traceSet_iff hc hw0 (fun _ h => absurd h (lt_irrefl _))).1 htr
  have hline : (fun s : ℝ => LP.traceAt s.toNNReal w) = fun s : ℝ => η s.toNNReal := by
    funext s
    exact LP.traceAt_eq_of_isGeneratingTrace hη hc hw0 ENNReal.coe_lt_top
  have hηc : Continuous η := continuousOn_univ.1 (hη.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  rw [hline] at him hsep
  refine ⟨η, hη, htend rfl, hline, isLoewnerTrace_of_isGeneratingTrace hη, ?_⟩
  refine isProperArc_of_conds (hηc.comp continuous_real_toNNReal).continuousOn ?_ hsep him
    ((htend rfl).comp tendsto_real_toNNReal_atTop)
  simpa using hη.1

/-- A simple proper generating trace on `[0, ∞)` gives a good path. -/
theorem goodPath_of_trace {w : ℝ≥0 → ℝ} (hwc : Continuous w) (hw0 : w 0 = 0) {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace w ⊤ η) (hinj : Function.Injective η) (hH : ∀ t, 0 < t → η t ∈ H)
    (htend : Tendsto (fun t => ‖η t‖) atTop atTop) : GoodPath w ⊤ := by
  have hc : ContinuousOn w {t : ℝ≥0 | (t : ℝ≥0∞) < ⊤} := hwc.continuousOn
  have hline : (fun s : ℝ => LP.traceAt s.toNNReal w) = fun s : ℝ => η s.toNNReal := by
    funext s
    exact LP.traceAt_eq_of_isGeneratingTrace hη hc hw0 ENNReal.coe_lt_top
  have hηc : Continuous η := continuousOn_univ.1 (hη.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  have hP : IsProperArc fun s : ℝ => η s.toNNReal :=
    { cont := (hηc.comp continuous_real_toNNReal).continuousOn
      inj := fun s hs t ht h => by
        have := hinj h
        rw [← Real.coe_toNNReal s (mem_Ici.1 hs), ← Real.coe_toNNReal t (mem_Ici.1 ht), this]
      zero := by simpa using hη.1
      mem_H := fun t ht => hH _ (Real.toNNReal_pos.2 ht)
      tendsto := htend.comp tendsto_real_toNNReal_atTop }
  refine ⟨rfl, (mem_traceSet_iff hc hw0 (fun _ h => absurd h (lt_irrefl _))).2 ⟨η, hη, fun _ => htend⟩, ?_, ?_⟩
  · rw [hline]; exact hP.imPosCond
  · rw [hline]; exact hP.sepCond

/-! ### The canonical law of the good codes -/

/-- **Lemma 4.12 and Corollary 4.13 in code form**: at a strictly separated ordered word with nonnegative cumulative
weights, the canonical law of the non-good codes is zero. -/
theorem codeLaw_compl_goodCode_eq_zero {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    (hF : IsOrderedForceWord xL xR) (hsep : ∀ i j, xL i < xR j) (hcum : HasNonnegCumWeights ρL ρR) :
    codeLaw 4 ρL ρR (goodCode (nL := nL) (nR := nR))ᶜ (xL, xR) = 0 := by
  obtain ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, hE⟩ :=
    exists_isIntegratedSLEEvolution_assembled (a := 4) (by norm_num) hF
  have hlaw := measure_eventOf_eq_codeLaw (by norm_num : (0 : ℝ) < 4) hsep hE (S := goodCodeᶜ)
    (Φ := fun w τ => ¬ GoodPath w τ) measurableSet_goodCode.compl
    (fun x _ _ => by rw [mem_compl_iff, mem_goodCode_iff]) not_goodPath_congr
  rw [← hlaw]
  have hgood : ∀ᵐ ω ∂P, GoodPath (fun t => W t ω) (ζ ω) := by
    filter_upwards [Wire.ae_simple_transient_trace hF hcum hE, hE.2.2.2.2] with ω hω hp
    obtain ⟨hζ, -, η, hη, hinj, hH, -, htend⟩ := hω
    have hwc : Continuous fun t => W t ω := by
      have h := hp.isForcePath.continuousOn_w
      rw [hζ] at h
      exact continuousOn_univ.1 (h.mono fun t _ => ENNReal.coe_lt_top)
    rw [hζ]
    exact goodPath_of_trace hwc hp.1 hη hinj hH htend
  exact ae_iff.1 hgood

end ImgDrv

end InteractingSLE.WangWu
