/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop49QExitCode
import InteractingSLE.Spec.Sec5.Aux22StripAe

/-!
# Aux. lemma 22 for a left span, in code form

Packet PROVE-GLUECOND9. PROVE-SEC5-L's strip end (`Sec5.Aux22Strip.ae_exists_stripEnd_of_integrated`, Aux. lemma 22
after the change of target: the span is the half-line beyond the last right mark) gives, after the reflection
`z ↦ −z̄` (`IsIntegratedSLEEvolution.reflect`, `LP.isGeneratingTrace_reflect`), the **left** strip end: for an
integrated `SLE_κ(ρ)` evolution, `0 < κ ≤ 4`, from a strictly ordered start with every left mark negative and every
right mark positive, whose reflected strip word satisfies Zhan's hypotheses, almost surely the trace generates the
chain before a finite time `S > 0`, avoids `ℝ ∖ {0}` before `S`, and converges at `S` to a real point left of the
last left mark (`ae_leftEnd_of_integrated`, in the countable form `LeftEnd` of `Prop49QExitCode`).

**`codeLaw_compl_exitCode_eq_zero`**: hence the restart event `exitCode` has full canonical law at every separated
ordered start, which is the input of the restart theorem `ae_restart_code`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Sec5.Prop49Exit

open Sec2 Sec2.Assembly Sec2.Restart Sec7.RandRestart

variable {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- A generating trace on `[0, r]`, `r` before the lifetime, puts the horizon `r` in the trace set. -/
theorem mem_traceSet_of_trace (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0) {r : ℝ≥0}
    (hrζ : (r : ℝ≥0∞) < ζ) {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace w (r : ℝ≥0∞) η) :
    (w, (r : ℝ≥0∞)) ∈ traceSet := by
  have hwr : ContinuousOn w {t | (t : ℝ≥0∞) < (r : ℝ≥0∞)} := hw.mono fun t ht => lt_trans ht hrζ
  have hlim : 0 < (r : ℝ≥0∞) → (r : ℝ≥0∞) < ⊤ →
      ∃ w₀ : ℝ, Tendsto w (𝓝[<] (r : ℝ≥0∞).toNNReal) (𝓝 w₀) := fun _ _ => by
    refine ⟨w r, ?_⟩
    rw [ENNReal.toNNReal_coe]
    have hopen : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < ζ} := isOpen_lt ENNReal.continuous_coe continuous_const
    exact ((hw.continuousAt (hopen.mem_nhds hrζ)).tendsto).mono_left nhdsWithin_le_nhds
  exact (mem_traceSet_iff hwr hw0 hlim).2 ⟨η, hη, fun h => absurd h ENNReal.coe_ne_top⟩

/-- **The countable form of a left strip end.** If a trace `η` generates the chain of `w` on `[0, u]` for every
`u < S` (`0 < S ≤ ζ`, `w` continuous before `ζ` from `0`), never visits `ℝ \ {0}` before `S`, and converges at `S` to
a real `y < min 0 e`, then `LeftEnd e w ζ`. -/
theorem leftEnd_of_trace (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0) {S : ℝ≥0} (hS0 : 0 < S)
    (hSζ : (S : ℝ≥0∞) ≤ ζ) {η : ℝ≥0 → ℂ} (hgen : ∀ u : ℝ≥0, u < S → IsGeneratingTrace w u η)
    (havoid : ∀ u : ℝ≥0, u < S → ∀ z : ℝ, z ≠ 0 → η u ≠ z) {y e : ℝ} (hy0 : y < 0) (hye : y < e)
    (hconv : Tendsto η (𝓝[<] S) (𝓝 (y : ℂ))) : LeftEnd e w ζ := by
  have hlt : ∀ u : ℝ≥0, u < S → (u : ℝ≥0∞) < ζ := fun u hu => lt_of_lt_of_le (by exact_mod_cast hu) hSζ
  -- the measurable evaluation is the trace before `S`
  have htr : ∀ p : ℝ≥0, p < S → LP.traceAt p w = η p := by
    intro p hp
    obtain ⟨u, hpu, huS⟩ := exists_between hp
    exact traceAt_eq_of_trace (hgen u huS) hw hw0 (hlt u huS).le hpu
  refine ⟨S, y, hS0, hSζ, hy0, hye, fun r hr => mem_traceSet_of_trace hw hw0 (hlt _ hr) (hgen _ hr),
    fun n r hr => ?_, fun k => ?_⟩
  · -- a uniform margin on `[0, r]` by compactness
    obtain ⟨u, hru, huS⟩ := exists_between hr
    have hηc : ContinuousOn η (Icc 0 (r : ℝ≥0)) :=
      (hgen u huS).2.1.mono fun t ht => by exact_mod_cast ht.2.trans hru.le
    have hne : (GlueCond.farReal n).Nonempty := ⟨((((n : ℝ) + 1) : ℝ) : ℂ), by
      refine ⟨by simp, ?_⟩
      simp only [Complex.ofReal_re]
      rw [abs_of_pos (by positivity)]
      calc 1 / ((n : ℝ) + 1) ≤ 1 := by
            rw [div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
        _ ≤ (n : ℝ) + 1 := by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]⟩
    have hpos : ∀ t ∈ Icc (0 : ℝ≥0) r, 0 < infDist (η t) (GlueCond.farReal n) := by
      intro t ht
      refine ((GlueCond.isClosed_farReal n).notMem_iff_infDist_pos hne).1 fun hmem => ?_
      have hre : η t = ((η t).re : ℂ) := Complex.ext rfl (by simp [hmem.1])
      have hne0 : (η t).re ≠ 0 := by
        intro h0
        have := hmem.2
        rw [h0, abs_zero] at this
        have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith
      exact havoid t (lt_of_le_of_lt (by exact_mod_cast ht.2) hr) _ hne0 hre
    obtain ⟨t₀, ht₀, hmin⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := (r : ℝ≥0))).exists_isMinOn
      ⟨0, le_rfl, zero_le⟩ ((continuous_infDist_pt _).comp_continuousOn hηc)
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt (hpos t₀ ht₀)
    refine ⟨m, fun p hp => ?_⟩
    have hpI : ((p : ℝ≥0)) ∈ Icc (0 : ℝ≥0) r := ⟨zero_le, by exact_mod_cast hp⟩
    rw [htr p (lt_of_le_of_lt (by exact_mod_cast hp) hr)]
    exact hm.le.trans (hmin hpI)
  · -- the limit along rational times
    obtain ⟨δ, hδ, hδε⟩ := Metric.tendsto_nhdsWithin_nhds.1 hconv (1 / ((k : ℝ) + 1)) (by positivity)
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
    refine ⟨m, fun p hp1 hp2 => ?_⟩
    rw [htr p hp2, ← dist_eq_norm]
    refine (hδε hp2 ?_).le
    rw [NNReal.dist_eq, abs_lt]
    have hp2' : ((p : ℝ≥0) : ℝ) < S := by exact_mod_cast hp2
    constructor <;> linarith

/-- **Aux. lemma 22 for a left span** (the reflection of PROVE-SEC5-L's strip end). Let `(W, V, B)` be an integrated
`SLE_κ(ρ)` evolution, `0 < κ ≤ 4`, from a strictly ordered start (every left mark negative, every right mark positive)
whose reflected strip word satisfies Zhan's hypotheses (the prefix sums of the left weights before the last one and
of the right weights at least `κ/2 − 2`; `|q₊ − q₋| < 2`). Then almost surely the driver has a left strip end beyond
its last left mark. -/
theorem ae_leftEnd_of_integrated {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) {n j : ℕ} {xL : Fin (j + 1) → ℝ}
    {xR : Fin n → ℝ} {ρL : Fin (j + 1) → ℝ} {ρR : Fin n → ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin (j + 1) → ℝ≥0 → Ω → ℝ} {VR : Fin n → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hs : StrictStart (xL, xR))
    (hpre : Strip.HasStripPrefixSums κ (Fin.init ρL) ρR)
    (hq : |Strip.chargePlus κ (Fin.init ρL) ρR (ρL (Fin.last j)) -
      Strip.chargeMinus (Fin.init ρL) (ρL (Fin.last j))| < 2) :
    ∀ᵐ ω ∂P, LeftEnd (xL (Fin.last j)) (fun t => W t ω) (ζ ω) := by
  obtain ⟨hLa, hL0, hRm, hR0⟩ := hs
  have hR := hE.reflect
  have hend := Aux22Strip.ae_exists_stripEnd_of_integrated hκ hκ4 hR (by simpa using hL0 (Fin.last j))
    hLa.neg (fun k => by simpa using hL0 k.castSucc) hRm.neg (fun i => by simpa using hR0 i) hpre hq
  filter_upwards [hend, hE.ae_isIntegratedSLEPath] with ω ⟨S, η, y, hS0, hy, hlife, hgen, havoid, hconv⟩ hp
  have hwc : ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} := hp.isForcePath.continuousOn_w
  have hw0 : W 0 ω = 0 := hp.1
  -- the end time is before the lifetime
  have hSζ : (S : ℝ≥0∞) ≤ ζ ω := by
    by_contra h
    push Not at h
    have hfin : ζ ω ≠ ⊤ := ne_top_of_lt h
    have hu : (((ζ ω).toNNReal : ℝ≥0) : ℝ≥0∞) = ζ ω := ENNReal.coe_toNNReal hfin
    have huS : (ζ ω).toNNReal < S := by
      have : (((ζ ω).toNNReal : ℝ≥0) : ℝ≥0∞) < S := by rw [hu]; exact h
      exact_mod_cast this
    have := ((hlife _).2 huS).1
    rw [hu] at this
    exact lt_irrefl _ this
  -- reflect the trace back
  have hneg : (fun t => (-W) t ω) = -(fun t => W t ω) := by funext t; simp
  have hgen' : ∀ u : ℝ≥0, u < S → IsGeneratingTrace (fun t => W t ω) u (fun t => LP.reflectC (η t)) := by
    intro u hu
    have h := LP.isGeneratingTrace_reflect (hgen u hu)
    rw [hneg, neg_neg] at h
    exact h
  have havoid' : ∀ u : ℝ≥0, u < S → ∀ z : ℝ, z ≠ 0 → LP.reflectC (η u) ≠ z := by
    intro u hu z hz h
    have : η u = ((-z : ℝ) : ℂ) := by
      rw [← LP.reflectC_reflectC (η u), h]
      simp [LP.reflectC]
    exact havoid u hu (-z) (neg_ne_zero.2 hz) this
  have hconv' : Tendsto (fun t => LP.reflectC (η t)) (𝓝[<] S) (𝓝 ((-y : ℝ) : ℂ)) := by
    have h := (LP.continuous_reflectC.tendsto (y : ℂ)).comp hconv
    have e : LP.reflectC (y : ℂ) = ((-y : ℝ) : ℂ) := by simp [LP.reflectC]
    rw [e] at h
    exact h
  have hxl : 0 < -xL (Fin.last j) := by linarith [hL0 (Fin.last j)]
  have hy' : -xL (Fin.last j) < y := by simpa using hy
  exact leftEnd_of_trace hwc hw0 hS0 hSζ hgen' havoid' (by linarith) (by linarith) hconv'

/-- **The restart event has full canonical law at every separated ordered start** (`0 < κ ≤ 4`, Zhan's hypotheses
on the weights; the bound is the last left mark). -/
theorem codeLaw_compl_exitCode_eq_zero {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) {n j : ℕ} {ρL : Fin (j + 1) → ℝ}
    {ρR : Fin n → ℝ} (hpre : Strip.HasStripPrefixSums κ (Fin.init ρL) ρR)
    (hq : |Strip.chargePlus κ (Fin.init ρL) ρR (ρL (Fin.last j)) -
      Strip.chargeMinus (Fin.init ρL) (ρL (Fin.last j))| < 2)
    (s : (Fin (j + 1) → ℝ) × (Fin n → ℝ)) (hsep : SepStart s) (hF : IsOrderedForceWord s.1 s.2) :
    codeLaw κ ρL ρR (exitCode κ ρL ρR fun s => s.1 (Fin.last j))ᶜ s = 0 := by
  by_cases hs : StrictStart s
  · obtain ⟨Ω₀, m₀, P₀, hP₀, 𝓕₀, W₀, VL₀, VR₀, B₀, ζ₀, hE₀⟩ :=
      exists_isIntegratedSLEEvolution_assembled (a := κ) hκ hF
    exact codeLaw_compl_eq_zero_of_ae hκ hsep hE₀ (measurableSet_exitCode (by fun_prop))
      (fun x hx _ => mem_exitCode_iff hs hx) (fun w w' τ hww' h => leftEnd_congr w w' τ hww' h)
      (ae_leftEnd_of_integrated hκ hκ4 hE₀ hs hpre hq)
  · exact codeLaw_compl_exitCode_of_not hs

end InteractingSLE.Sec5.Prop49Exit
