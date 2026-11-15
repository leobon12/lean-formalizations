/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NdRead
import InteractingSLE.Spec.Supplement.SB2VsGauge
import InteractingSLE.Spec.Supplement.SB2VsSample

/-!
# F2b′'s stop gauge, in relative coordinates

Packet PROVE-AUX61-NOJUMP (round 21, D34, component C). SB2(1)'s gauge (`Vs.gaugeFun`) had a physical part, which
made it vanish at the relative lifetime. F2b′'s gauge is read in relative coordinates only:
`relGauge2 z = min (relGauge z) (1 / (1 + |z|))`. It vanishes at a finite relative lifetime because the relative
trace ends at a relatively bad point, and at an infinite one because the trace escapes. Both are facts about the
relative trace (component F).

* `relGauge2`, `rec2` (its grid code), `decode_rec2`, `measurable_rec2`, `continuous_relGauge2`, `relGauge2_le_one`;
* **`continuous_gco_rel`**: the coordinate gauge along a relative trace is continuous once its gauge tends to `0` at
  the lifetime;
* **`sample_rules_rel`**: SB2(1)'s `Vs.sample_rules` from continuity of the coordinate gauge (no chart).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.SB.Nd

open Vs Exist.StagedLaw Supp8.GB6 Supp8.GB6.HullId Supp8.GB6.RelDrv.Version Supp8.Q3Stop Sec7.PocketTraversal

section Gauge

variable {Ω : Type*} (κ ψ : ℝ) (cw : Ω → Restart.BoundaryWord) (types : Set WordType)

/-- **F2b′'s gauge**: the relative cell gauge, capped by `1 / (1 + |z|)`. -/
def relGauge2 (ω : Ω) (z : ℂ) : ℝ≥0∞ := min (relGauge κ ψ cw types ω z) (Bph z)

/-- **F2b′'s stop record**: the grid code of the gauge. -/
def rec2 (ω : Ω) : RecData := (recFun fun z => (relGauge2 κ ψ cw types ω z).toReal, 0, false)

theorem relGauge2_le_one (ω : Ω) (z : ℂ) : relGauge2 κ ψ cw types ω z ≤ 1 :=
  (min_le_left _ _).trans (relGauge_le_one κ ψ cw types ω z)

theorem relGauge2_le_Bph (ω : Ω) (z : ℂ) : relGauge2 κ ψ cw types ω z ≤ Bph z := min_le_right _ _

theorem continuous_relGauge2 (ω : Ω) : Continuous (relGauge2 κ ψ cw types ω) :=
  (continuous_relGauge κ ψ cw types ω).min continuous_Bph

theorem continuous_toReal_relGauge2 (ω : Ω) : Continuous fun z => (relGauge2 κ ψ cw types ω z).toReal :=
  ENNReal.continuousOn_toReal.comp_continuous (continuous_relGauge2 κ ψ cw types ω) fun z =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (relGauge2_le_one κ ψ cw types ω z)

theorem decode_rec2 (ω : Ω) {z : ℂ} (hz : 0 ≤ z.im) :
    decode (rec2 κ ψ cw types ω) z = (relGauge2 κ ψ cw types ω z).toReal :=
  decode_eq hz (continuous_toReal_relGauge2 κ ψ cw types ω).continuousWithinAt fun p _ => by
    simp only [rec2]; rw [recFun_code]

theorem measurable_rec2 {m : MeasurableSpace Ω} (hcw : Measurable[m] cw) (htypes : types.Countable) :
    Measurable[m] (rec2 κ ψ cw types) := by
  refine (measurable_recFun fun z => ?_).prodMk measurable_const
  exact ENNReal.measurable_toReal.comp ((measurable_relGauge κ ψ cw types hcw htypes z).min measurable_const)

end Gauge


section Det

variable {G : ℂ → ℝ≥0∞} {Γ : ℝ≥0 → ℂ} {U : ℝ≥0∞}

/-- **The coordinate gauge is continuous** once the gauge along the trace tends to `0` at a finite lifetime. -/
theorem continuous_gco_rel (hGc : Continuous G) (hG1 : ∀ z, G z ≤ 1) (hΓc : ContinuousOn Γ {s | (s : ℝ≥0∞) < U})
    (hlim : U ≠ ⊤ → Tendsto (fun s => (G (Γ s)).toReal) (𝓝[<] U.toNNReal) (𝓝 0)) : Continuous (gco G Γ U) := by
  have hopen : IsOpen {s : ℝ≥0 | (s : ℝ≥0∞) < U} := isOpen_lt ENNReal.continuous_coe continuous_const
  rw [continuous_iff_continuousAt]
  intro s
  rcases lt_or_ge (s : ℝ≥0∞) U with hs | hs
  · have h2 : ContinuousAt Γ s := (hΓc s hs).continuousAt (hopen.mem_nhds hs)
    have hcG : ContinuousAt (fun s => (G (Γ s)).toReal) s :=
      (ENNReal.continuousAt_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top (hG1 (Γ s)))).comp
        (f := fun s => G (Γ s)) (hGc.continuousAt.comp h2)
    refine hcG.congr ?_
    filter_upwards [hopen.mem_nhds hs] with s' hs'
    rw [gco_of_lt hs']
  · have hU : U ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hs
    rcases eq_or_lt_of_le hs with he | hlt
    · have hsU : s = U.toNNReal := by rw [he, ENNReal.toNNReal_coe]
      refine continuousAt_iff_continuous_left_right.2 ⟨?_, ?_⟩
      · refine continuousWithinAt_Iio_iff_Iic.1 ?_
        show Tendsto (gco G Γ U) (𝓝[<] s) (𝓝 (gco G Γ U s))
        rw [gco_of_le hs]
        have h := hlim hU
        rw [← hsU] at h
        refine h.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with x (hx : x < s)
        rw [gco_of_lt (by rw [he]; exact ENNReal.coe_lt_coe.2 hx)]
      · rw [ContinuousWithinAt, gco_of_le hs]
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with x hx
        exact (gco_of_le (hs.trans (ENNReal.coe_le_coe.2 hx))).symm
    · have hopen' : IsOpen {s : ℝ≥0 | U < (s : ℝ≥0∞)} := isOpen_lt continuous_const ENNReal.continuous_coe
      refine (continuousAt_const (y := (0 : ℝ))).congr ?_
      filter_upwards [hopen'.mem_nhds hlt] with s' hs'
      rw [gco_of_le hs'.le]

/-- **The stops increase to the lifetime** when the gauge is positive before it and vanishes at it. -/
theorem iSup_localStop_eq {g : ℝ≥0 → ℝ} (hg : Continuous g) (h0 : 0 < g 0)
    (hz : ∀ T : ℝ≥0, (T : ℝ≥0∞) = U → g T = 0) (hpos : ∀ t : ℝ≥0, (t : ℝ≥0∞) < U → 0 < g t) :
    ⨆ m, (localStop g m : ℝ≥0∞) = U := by
  refine le_antisymm (iSup_le fun m => (localStop_lt hg h0 hz m).le) (le_of_forall_lt fun a ha => ?_)
  have ha' : a ≠ ⊤ := ne_top_of_lt ha
  obtain ⟨m, hm⟩ := exists_lt_localStop hg (t := a.toNNReal) fun u hu => hpos u
    (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hu) (by rw [ENNReal.coe_toNNReal ha']; exact ha))
  refine lt_of_lt_of_le ?_ (le_iSup _ m)
  rw [← ENNReal.coe_toNNReal ha']
  exact ENNReal.coe_lt_coe.2 hm

variable {ρ : ℝ → ℂ} {Wr : ℝ≥0 → ℝ} {r : RecData}

/-- **The stops along one sample** (SB2(1)'s `Vs.sample_rules`, from a continuous coordinate gauge). -/
theorem sample_rules_rel (hG1 : ∀ z, G z ≤ 1) (hG0 : 0 < G 0) (hd : IsDrivenCurve ρ)
    (hgen : ∀ T : ℝ≥0∞, T < Sec7.Lemma71C.capLife ρ → IsGeneratingTrace Wr T (capTrace ρ))
    (hWrc : ContinuousOn Wr {t | (t : ℝ≥0∞) < Sec7.Lemma71C.capLife ρ}) (hWr0 : Wr 0 = 0)
    (hgc : Continuous (gco G (capTrace ρ) (Sec7.Lemma71C.capLife ρ)))
    (hdec : ∀ z, 0 ≤ z.im → decode r z = (G z).toReal) (m : ℕ) :
    (localStop (gco G (capTrace ρ) (Sec7.Lemma71C.capLife ρ)) m : ℝ≥0∞) < Sec7.Lemma71C.capLife ρ ∧
      stopRule m (r, Wr) = localStop (gco G (capTrace ρ) (Sec7.Lemma71C.capLife ρ)) m ∧
      (∀ n, annRules gaugeRead m n (r, Wr) < localStop (gco G (capTrace ρ) (Sec7.Lemma71C.capLife ρ)) m) ∧
      ⨆ n, annRules gaugeRead m n (r, Wr) = localStop (gco G (capTrace ρ) (Sec7.Lemma71C.capLife ρ)) m ∧
      ∀ t : ℝ≥0, t < localStop (gco G (capTrace ρ) (Sec7.Lemma71C.capLife ρ)) m → 0 < G (capTrace ρ t) := by
  set U := Sec7.Lemma71C.capLife ρ with hUdef
  have hΓ0 : capTrace ρ 0 = 0 := capTrace_zero hd
  set Γ := capTrace ρ with hΓdef
  have hU0 : 0 < U := Vk.capLife_pos hd
  have hΓH : ∀ s : ℝ≥0, (s : ℝ≥0∞) < U → 0 ≤ (Γ s).im := fun s hs => by
    obtain ⟨T, hsT, hTU⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hs
    exact Sec7.IsGeneratingTrace.mem_Hbar (hgen T hTU) (hWrc.mono fun x hx => lt_trans hx hTU) hWr0 hsT.le
  have hfin : ∀ z, G z ≠ ⊤ := fun z => ne_top_of_le_ne_top ENNReal.one_ne_top (hG1 z)
  have hg0 : 0 < gco G Γ U 0 := by
    rw [gco_of_lt (by exact_mod_cast hU0), hΓ0]
    exact ENNReal.toReal_pos hG0.ne' (hfin 0)
  have hterm : ∀ T : ℝ≥0, (T : ℝ≥0∞) = U → gco G Γ U T = 0 := fun T hT => gco_of_le hT.ge
  have hlt : (localStop (gco G Γ U) m : ℝ≥0∞) < U := localStop_lt hgc hg0 hterm m
  have hrd : ∀ v ≤ localStop (gco G Γ U) m, gaugeRead v (r, Wr) = gco G Γ U v := fun v hv => by
    have hvU : (v : ℝ≥0∞) < U := lt_of_le_of_lt (ENNReal.coe_le_coe.2 hv) hlt
    obtain ⟨T, hvT, hTU⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hvU
    have htr' : LP.traceAt v Wr = Γ v :=
      LP.traceAt_eq_of_isGeneratingTrace (hgen T hTU) (hWrc.mono fun s hs => lt_trans hs hTU) hWr0 hvT
    simp only [gaugeRead]
    rw [htr', hdec _ (hΓH v hvU), gco_of_lt hvU]
  have h0 : gaugeRead 0 (r, fun _ => 0) = gco G Γ U 0 := by
    rw [gaugeRead_zero_zero, hdec 0 le_rfl, gco_of_lt (by exact_mod_cast hU0), hΓ0]
  obtain ⟨h1, h2, h3⟩ := rules_of_readback hgc hg0 m h0 hrd
  refine ⟨hlt, h1, h2, h3, fun t ht => ?_⟩
  have htU : (t : ℝ≥0∞) < U := lt_trans (ENNReal.coe_lt_coe.2 ht) hlt
  have hlev : gaugeLevel (gco G Γ U 0) m < gco G Γ U t := by
    by_contra hle
    rw [not_lt] at hle
    have := gaugeStop_le_of_le (ht.le.trans (gaugeStop_le _ _ _)) hle
    exact absurd this (not_le.2 ht)
  have hpos : 0 < gco G Γ U t := lt_trans (gaugeLevel_pos hg0 m) hlev
  rw [gco_of_lt htU] at hpos
  exact ENNReal.toReal_pos_iff.1 hpos |>.1

end Det

end InteractingSLE.Theorem14.SB.Nd
