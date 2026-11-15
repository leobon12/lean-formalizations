/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2VsSeed

/-!
# SB2(1)'s stops along one good sample (D19, step 4)

Packet PROVE-AUX61-NOJUMP (decision D19).

* `iChart I`: K2's random chart of the launch (the version chart recentred at the entry); **`sb2Rec I`**: SB2(1)'s stop
  record, the grid code of the gauge read from `iChart I` (physical part: D10's rule; relative part: D19's cap).
* **`sb2_sample`** (one sample): at a launch with `t_L < ζ`, given the sample's facts (the driven family, the
  clock, a continuous extension of the shifted launch chart's inverse reading the flow, K2's chart identity, the flow's
  regularity, step 1, step 3's core, the cover and an admissible relative seed), the stop rule along any driver `Wr`
  generating the relative trace is positive, strictly below the relative lifetime, announced by the rules `annRules`,
  and the relative trace avoids the bad set of the cell word before it.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Vs

open Vr Vq Exist.Staged Exist.StagedLaw Lv Supp8.GB6 Supp8.GB6.HullId Supp8.GB6.RelDrv.Version Supp8.Q3Stop
  Sec7.PocketTraversal

section

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}

/-- **K2's random chart of the launch** (the version chart recentred at the entry). -/
def iChart (I : K2LaunchInputs κ b jumps P h E k u ψ) (ω : Ω) : Chart :=
  (WalkInf.verChart κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
    (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1) ω).recenter (I.entry ω)

/-- **SB2(1)'s stop record.** -/
def sb2Rec (I : K2LaunchInputs κ b jumps P h E k u ψ) : Ω → RecData :=
  sb2Record (iChart I) u (sb2BadClosure κ b jumps u ψ) κ ψ I.word I.types

/-- **The stop record is measurable for the retained past.** -/
theorem measurable_sb2Rec (I : K2LaunchInputs κ b jumps P h E k u ψ) :
    Measurable[pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (k + 1)] (sb2Rec I) :=
  measurable_sb2Record _ _ _ _ _ _ _ I.chart_measurable I.word_measurable I.types_countable

/-- **SB2(1)'s stops along one good sample.** -/
theorem sb2_sample (I : K2LaunchInputs κ b jumps P h E k u ψ) {ω : Ω} {ρω : ℝ → ℂ} {Wr : ℝ≥0 → ℝ}
    {a : ℝ≥0 → ℝ≥0∞}
    (hT : Ve.entT κ b jumps E k u η ζ ω < ζ ω)
    (h1 : ζ ω = ⊤ → EqOn ρω (Vd.liftR (Ve.flowLift κ b jumps E k u η ζ ω)) (Ici 0))
    (h2 : ζ ω ≠ ⊤ → EqOn ρω (relCurve (Vd.liftR (Ve.flowLift κ b jumps E k u η ζ ω))
      ((ζ ω).toReal - (Ve.entT κ b jumps E k u η ζ ω).toReal)) (Ici 0))
    (hd : IsDrivenCurve ρω) (hcl : Sec7.Lemma71C.capLife ρω = Vk.relLife κ b jumps E k u η ζ ω)
    (hgen : ∀ T : ℝ≥0∞, T < Sec7.Lemma71C.capLife ρω → IsGeneratingTrace Wr T (capTrace ρω))
    (hWrc : ContinuousOn Wr {t | (t : ℝ≥0∞) < Sec7.Lemma71C.capLife ρω}) (hWr0 : Wr 0 = 0)
    (hac : Continuous a) (ham : Monotone a)
    (hclock : ∀ t, a t = Vc.clockOf (Ve.flowLift κ b jumps E k u η ζ ω) (Ve.entT κ b jumps E k u η ζ ω).toNNReal
      (ζ ω) t)
    (hc0 : Sec7.Lemma71C.capClock (fun r : ℝ => Ve.flowLift κ b jumps E k u η ζ ω r.toNNReal) 0 = 0)
    (hmono : ∀ T₁ : ℝ≥0, (Ve.entT κ b jumps E k u η ζ ω).toNNReal ≤ T₁ → (T₁ : ℝ≥0∞) < ζ ω →
      MonotoneOn (Sec7.Lemma71C.capClock fun r : ℝ => Ve.flowLift κ b jumps E k u η ζ ω r.toNNReal)
        (Icc 0 ((T₁ : ℝ) - (Ve.entT κ b jumps E k u η ζ ω).toNNReal)))
    (hinv : ∃ g : ℂ → ℂ, ContinuousOn g {z | 0 ≤ z.im} ∧
      EqOn g (Lw.shiftChart (Lv.launchChart κ b jumps E (k + 1) ω) u (launchEntry κ b jumps E (k + 1) u ω)).2.1 H ∧
      ∀ r : ℝ≥0, (((Ve.entT κ b jumps E k u η ζ ω).toNNReal + r : ℝ≥0) : ℝ≥0∞) < ζ ω →
        0 ≤ (Ve.flowLift κ b jumps E k u η ζ ω r).im ∧
        g (Ve.flowLift κ b jumps E k u η ζ ω r) = η ω ((Ve.entT κ b jumps E k u η ζ ω).toNNReal + r) - u)
    (hchart : iChart I ω = (Lv.launchChart κ b jumps E (k + 1) ω).recenter (launchEntry κ b jumps E (k + 1) u ω))
    (hηc : ContinuousOn (η ω) {t | (t : ℝ≥0∞) ≤ ζ ω})
    (htr : ζ ω = ⊤ → Tendsto (fun t => ‖η ω t‖) atTop atTop)
    (htip : 0 < ζ ω → ζ ω ≠ ⊤ → IsBadPoint (flowLineXL b jumps u) (flowLineXR b jumps u)
      (flowLineRhoL κ b jumps u ψ) (flowLineRhoR κ b jumps u ψ) (η ω (ζ ω).toNNReal - u))
    (hnv : 0 < ζ ω → ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → η ω t - u ∉ sb2BadClosure κ b jumps u ψ)
    {w : WordType} (hw : w ∈ I.types) (hcell : angleWordType κ ψ (I.word ω) = w)
    (hseed : ¬ ForceWord.ThresholdCondition (typedRhoL w) (typedRhoR w) 0 (cellXL κ ψ I.word w ω)
      (cellXR κ ψ I.word w ω)) (m : ℕ) :
    0 < stopRule m (sb2Rec I ω, Wr) ∧ stopRule m (sb2Rec I ω, Wr) < Sec7.Lemma71C.capLife ρω ∧
      stopRule m (sb2Rec I ω, Wr) ≠ ⊤ ∧
      (∀ n, annRules gaugeRead m n (sb2Rec I ω, Wr) < stopRule m (sb2Rec I ω, Wr)) ∧
      ⨆ n, annRules gaugeRead m n (sb2Rec I ω, Wr) = stopRule m (sb2Rec I ω, Wr) ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < stopRule m (sb2Rec I ω, Wr) →
        capTrace ρω t ∉ badSet (cellXL κ ψ I.word w ω) (cellXR κ ψ I.word w ω) (typedRhoL w) (typedRhoR w) := by
  obtain ⟨g, hgc, hgi, hgr⟩ := hinv
  set tL := (Ve.entT κ b jumps E k u η ζ ω).toNNReal with htLdef
  set γ := Ve.flowLift κ b jumps E k u η ζ ω with hγdef
  set F := sb2BadClosure κ b jumps u ψ with hFdef
  have hTLtop : Ve.entT κ b jumps E k u η ζ ω ≠ ⊤ := ne_top_of_lt hT
  have htZ : (tL : ℝ≥0∞) < ζ ω := by rw [htLdef, ENNReal.coe_toNNReal hTLtop]; exact hT
  have hζ0 : 0 < ζ ω := lt_of_le_of_lt zero_le hT
  set G := gaugeExt F κ ψ I.word I.types g ω with hGdef
  -- the readings of the clock
  have hread0 : ∀ t : ℝ≥0, tL ≤ t → (t : ℝ≥0∞) < ζ ω →
      a t = ENNReal.ofReal (Sec7.Lemma71C.capClock (Vd.liftR γ) ((t - tL : ℝ≥0) : ℝ)) ∧
      capTrace ρω (Sec7.Lemma71C.capClock (Vd.liftR γ) ((t - tL : ℝ≥0) : ℝ)).toNNReal = γ (t - tL) ∧
      ENNReal.ofReal (Sec7.Lemma71C.capClock (Vd.liftR γ) ((t - tL : ℝ≥0) : ℝ)) < Sec7.Lemma71C.capLife ρω := by
    intro t htL htζ
    have hsub : (((t - tL : ℝ≥0) : ℝ)) = (t : ℝ) - tL := NNReal.coe_sub htL
    have hs : ((((Ve.entT κ b jumps E k u η ζ ω).toNNReal + (t - tL) : ℝ≥0) : ℝ≥0∞)) < ζ ω := by
      rw [← htLdef, add_tsub_cancel_of_le htL]; exact htζ
    obtain ⟨hc1, hc2⟩ := Vk.capTrace_capClock hd hT h1 h2 hs
    refine ⟨?_, ?_, hc2⟩
    · rw [hclock, Vc.clockOf_eq htL htζ (hmono t htL htζ), hsub]; rfl
    · rw [hc1]; show γ (((t - tL : ℝ≥0) : ℝ)).toNNReal = _; rw [Real.toNNReal_coe]
  have hread : ∀ t : ℝ≥0, tL ≤ t → (t : ℝ≥0∞) < ζ ω → a t < Sec7.Lemma71C.capLife ρω ∧
      0 ≤ (capTrace ρω (a t).toNNReal).im ∧ g (capTrace ρω (a t).toNNReal) = η ω t - u := by
    intro t htL htζ
    obtain ⟨ha, hc1, hc2⟩ := hread0 t htL htζ
    have hat : (a t).toNNReal = (Sec7.Lemma71C.capClock (Vd.liftR γ) ((t - tL : ℝ≥0) : ℝ)).toNNReal := by
      rw [ha]; exact ENNReal.toNNReal_coe _
    have hs : ((tL + (t - tL) : ℝ≥0) : ℝ≥0∞) < ζ ω := by rw [add_tsub_cancel_of_le htL]; exact htζ
    obtain ⟨him, hg⟩ := hgr (t - tL) hs
    refine ⟨ha ▸ hc2, ?_, ?_⟩
    · rw [hat, hc1]; exact him
    · rw [hat, hc1, hg, add_tsub_cancel_of_le htL]
  have hatL : a tL = 0 := by
    rw [(hread0 tL le_rfl htZ).1, tsub_self, NNReal.coe_zero]
    show ENNReal.ofReal (Sec7.Lemma71C.capClock (fun r : ℝ => γ r.toNNReal) 0) = 0
    rw [hc0, ENNReal.ofReal_zero]
  have hsurj : ∀ s : ℝ≥0, (s : ℝ≥0∞) < Sec7.Lemma71C.capLife ρω →
      ∃ t : ℝ≥0, tL ≤ t ∧ (t : ℝ≥0∞) < ζ ω ∧ a t = s := by
    intro s hs
    rw [hcl] at hs
    obtain ⟨s', hs'⟩ := lt_iSup_iff.1 hs
    obtain ⟨hs'ζ, hs's⟩ := lt_iSup_iff.1 hs'
    set t₁ := tL + s' with ht₁
    have ht₁ζ : (t₁ : ℝ≥0∞) < ζ ω := hs'ζ
    have hat₁ : a t₁ = ENNReal.ofReal (Sec7.Lemma71C.capClock (Vd.liftR γ) (s' : ℝ)) := by
      rw [(hread0 t₁ le_self_add ht₁ζ).1, ht₁, add_tsub_cancel_left]
    have hmem : (s : ℝ≥0∞) ∈ Icc (a tL) (a t₁) := ⟨by rw [hatL]; exact zero_le, by rw [hat₁]; exact hs's.le⟩
    obtain ⟨t, ht, hts⟩ := intermediate_value_Icc (le_self_add : tL ≤ t₁) hac.continuousOn hmem
    exact ⟨t, ht.1, lt_of_le_of_lt (ENNReal.coe_le_coe.2 ht.2) ht₁ζ, hts⟩
  -- the gauge function
  have hGc : ContinuousOn G {z | 0 ≤ z.im} := continuousOn_gaugeExt F κ ψ I.word I.types hgc ω
  have hG1 : ∀ z, G z ≤ 1 := gaugeExt_le_one F κ ψ I.word I.types g ω
  have hGA : ∀ z, G z ≤ Aph F (g z) := fun z => (min_le_left _ _).trans (min_le_left _ _)
  have hGB : ∀ z, G z ≤ Bph (g z) := fun z => (min_le_left _ _).trans (min_le_right _ _)
  have hg0 : g 0 = η ω tL - u := by
    have := (hread tL le_rfl htZ).2.2
    rwa [hatL, ENNReal.toNNReal_zero, capTrace_zero hd] at this
  have hG0 : 0 < G 0 := by
    refine lt_min (lt_min ?_ ?_) (pos_relGauge_zero hw hcell hseed)
    · refine lt_min ?_ one_pos
      rw [hg0, infEDist_pos_iff_notMem_closure, hFdef, sb2BadClosure, closure_closure]
      exact hnv hζ0 tL htZ
    · unfold Bph; rw [ENNReal.ofReal_pos]; positivity
  -- the physical flow
  have hη' : ContinuousOn (fun t => η ω t - u) {t | (t : ℝ≥0∞) ≤ ζ ω} := hηc.sub continuousOn_const
  have hend : ∀ T : ℝ≥0, (T : ℝ≥0∞) = ζ ω → η ω T - u ∈ F := by
    intro T hTe
    have hb := htip hζ0 (by rw [← hTe]; exact ENNReal.coe_ne_top)
    rw [← hTe, ENNReal.toNNReal_coe] at hb
    exact subset_closure hb
  have htr' : ζ ω = ⊤ → Tendsto (fun t => ‖η ω t - u‖) atTop atTop := fun hζ => by
    refine tendsto_atTop_mono (fun t => ?_) (tendsto_atTop_add_const_right _ (-‖(u : ℂ)‖) (htr hζ))
    have := norm_sub_norm_le (η ω t) (u : ℂ)
    linarith
  -- the record decodes to the gauge
  have hgH : ∀ z ∈ H, g z = (iChart I ω).2.1 z - u := fun z hz => by
    rw [hgi hz, hchart]; rfl
  have hdec : ∀ z, 0 ≤ z.im → decode (sb2Rec I ω) z = (G z).toReal := fun z hz =>
    decode_sb2Record (iChart I) u F κ ψ I.word I.types hgc hgH hz
  obtain ⟨hlt, hrule, hann, hsup, hposG⟩ := sample_rules hGc hG1 hGA hGB hG0 hd hgen hWrc hWr0 ham htZ hread
    hsurj hη' hend htr' hdec m
  rw [hrule]
  refine ⟨?_, hlt, ENNReal.coe_ne_top, hann, hsup, fun t ht => ?_⟩
  · exact lt_of_le_of_lt zero_le (hann 0)
  · have hpos := hposG t (by exact_mod_cast ht)
    have hrel : 0 < relGauge κ ψ I.word I.types ω (capTrace ρω t) := lt_of_lt_of_le hpos (min_le_right _ _)
    rw [relGauge_eq κ ψ I.word I.types hw hcell] at hrel
    have hinf := (lt_min_iff.1 hrel).1
    rw [infEDist_pos_iff_notMem_closure, closure_closure] at hinf
    exact fun hb => hinf (subset_closure hb)

end

end InteractingSLE.Theorem14.SB.Vs
