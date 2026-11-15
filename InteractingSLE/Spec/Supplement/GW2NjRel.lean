/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2NjSide
import InteractingSLE.Spec.Supplement.GW2NcEnd
import InteractingSLE.Spec.Sec7.Lemma76EJunction

/-!
# Before the contact the relative curve stays left of the counterflow junction (D81, part 2)

Packet PROVE-GW2-NEARIMG2, decision D81. Setting of `GW2NcRel` (the root-`x` relative chart, a first contact `τ`).
Before the contact, the re-centred relative trace `relBdry(x + γ t) − relBdry(x)` has its real values at most
`J₀ = jR − baseRead` (`relTr_le_junction`): the counterflow's right side is the ray beyond `J₀`, and the explored curve
does not meet it. Hence every real point `q > J₀` stays alive for the glued relative driver `cDrv` at every relative
time below the clock of a horizon before the contact (`alive_cDrv_of_gt`, from `Sec7.alive_of_trace_off`).

At a first contact at the counterflow's tip the relative clock is unbounded, so this covers every relative time.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory Complex
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull)

namespace InteractingSLE.Theorem14.GW2Ni

open Exist Staged StagedLaw Restart Supp8.GB6 Supp8.GB6.CoordB Supp8.GB6.ReadD GW2TipSystem GW2Rz GW2Wm
open MartChar.RealFlow

section Sample

variable {Ω : Type*} (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω)
  {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace (W · ω) ⊤ α)
  (hW : Continuous (W · ω)) (hW0 : W 0 ω = 0) (hζ : ζ ω = ⊤)
  {s : ℝ≥0} (hs : 0 < s) {x : ℝ} (hx : 0 ≤ x) (harc : ∀ u ∈ Icc 0 s, x * ‖α u‖ < 1)
  {w : ℝ≥0 → ℝ} (hwc : Continuous w) (hw0 : w 0 = 0) {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace w ⊤ γ)
  {τ : ℝ≥0} (hT : firstContactTime (fun t => sphereInv (((x : ℂ) + γ t : ℂ) : OnePoint ℂ))
    ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s) = (τ : ℝ≥0∞))

/-- **The counterflow junction of the root-`x` relative chart**, re-centred at the root: `jR − baseRead`. -/
abbrev junctionX (x : ℝ) (s : ℝ≥0) (cf : RecData) : ℝ := jROfRec cf - GW2Rz.baseRead x s cf

include hα hW hW0 hζ hx harc hwc hw0 hγ hT in
/-- **Before the contact, the re-centred relative trace stays left of the counterflow junction**: its real values
are at most `jR − baseRead`. -/
theorem relTr_le_junction (hneg : markPosL (rdrv (cfRec s W ζ ω)) (rtime (cfRec s W ζ ω)) 0 < 0)
    {t : ℝ≥0} (ht : t < τ) {r : ℝ}
    (hr : relBdry (rdrv (cfRec s W ζ ω)) s ((x : ℂ) + γ t) - relBdry (rdrv (cfRec s W ζ ω)) s x = r) :
    r ≤ junctionX x s (cfRec s W ζ ω) := by
  have he : IsRegularDriver (w, (⊤ : ℝ≥0∞)) := Gm.isRegularDriver_top hwc hw0
  set cf := cfRec s W ζ ω with hcf
  set U := rdrv cf with hUdef
  have hU : Continuous U := continuous_rdrv _
  have hU0 : U 0 = 0 := rdrv_zero _
  have hs0 : (0 : ℝ) ≤ s := s.coe_nonneg
  have hsafe := RootH29.trace_mem_record_relSafe W ζ ω hα hW hW0 hζ hx harc he hγ (lt_min_of_contact hT ht) le_rfl
  have hsafe0 := RootH29.trace_mem_record_relSafe W ζ ω hα hW hW0 hζ hx harc he hγ
    (lt_min_of_contact hT (lt_of_le_of_lt zero_le ht)) (t := 0) zero_le
  rw [hγ.1, add_zero] at hsafe0
  -- the root's chart value is real
  have hxim : (relBdry U s x).im = 0 := by
    by_cases hx0 : x = 0
    · subst hx0
      rw [Complex.ofReal_zero, relBdry_zero hU hU0 hs0, Complex.zero_im]
    · rw [GW2Sf.relBdry_of_real hU hU0 hs0 hx0 hsafe0.2, Complex.ofReal_im]
  have himr : (relBdry U s ((x : ℂ) + γ t)).im = 0 := by
    have h := congrArg Complex.im hr
    rw [Complex.sub_im, hxim, sub_zero, Complex.ofReal_im] at h
    exact h
  have hrt' : rtime cf = s := rtime_recOf_cfE s (by rw [hζ]; exact ENNReal.coe_lt_top)
  have hrt : (rtime cf : ℝ) = s := by rw [hrt']
  have hneg' : markPosL U s 0 < 0 := by rw [← hrt]; exact hneg
  have hle := relBdry_le_of_im_eq_zero hU hU0 hs0 hneg' hsafe himr
  have hjR : jROfRec cf = labelL U s 0 := by rw [← labelL_zero_eq_jROfRec, hrt]
  have hbase : GW2Rz.baseRead x s cf = (relBdry U s x).re := by
    unfold GW2Rz.baseRead
    rw [RootA22.boundaryRead_eq_relBdry s cf hsafe0]
  have hre := congrArg Complex.re hr
  rw [Complex.sub_re, Complex.ofReal_re] at hre
  unfold junctionX
  rw [hjR, hbase, ← hre]
  linarith

include hα hW hW0 hζ hs hx harc hwc hw0 hγ hT in
/-- **Beyond the junction every real point stays alive for the glued relative driver** (at relative times below the
clock of a horizon before the contact). -/
theorem alive_cDrv_of_gt (hneg : markPosL (rdrv (cfRec s W ζ ω)) (rtime (cfRec s W ζ ω)) 0 < 0)
    {v : ℝ≥0} (hvτ : v < τ) {t : ℝ≥0} {t₂ : ℝ} (htt₂ : (t : ℝ) < t₂)
    (ht₂ : t₂ < gClk x s (cfRec s W ζ ω) w v) {q : ℝ} (hq : junctionX x s (cfRec s W ζ ω) < q) (hq0 : 0 < q) :
    Alive (frozenDrive (cDrv x s (cfRec s W ζ ω) w τ) t₂) q t := by
  obtain ⟨h0, hm, hc⟩ := cClk_props W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT
  have hgen := isGeneratingTrace_cDrv W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT hvτ
  have ht₂0 : 0 ≤ t₂ := t.coe_nonneg.trans htt₂.le
  have hlt : ENNReal.ofReal t₂ < ENNReal.ofReal (gClk x s (cfRec s W ζ ω) w v) :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht₂0).2 ht₂
  refine Sec7.Lemma76E.alive_of_trace_off hgen (continuousOn_cDrv W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT hvτ)
    (cDrv_zero W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT) hlt htt₂ hq0 fun u hu r hr hηu => ?_
  -- the trace value at `u` is the relative trace at the time with clock `u`
  have hu' : (u : ℝ) ∈ Icc (gClk x s (cfRec s W ζ ω) w 0) (gClk x s (cfRec s W ζ ω) w v) := by
    rw [h0]
    refine ⟨u.coe_nonneg, ?_⟩
    have : (u : ℝ) ≤ t := NNReal.coe_le_coe.2 hu
    linarith
  obtain ⟨t', ht', hat'⟩ := intermediate_value_Icc (zero_le : (0 : ℝ≥0) ≤ v)
    (hc.mono fun z hz => lt_of_le_of_lt hz.2 hvτ) hu'
  have hueq : u = (gClk x s (cfRec s W ζ ω) w t').toNNReal := by rw [hat', Real.toNNReal_coe]
  rw [hueq, tip_eq_c W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT ht'.2 hvτ] at hηu
  have := relTr_le_junction W ζ ω hα hW hW0 hζ hx harc hwc hw0 hγ hT hneg (lt_of_le_of_lt ht'.2 hvτ) hηu
  linarith

end Sample

end InteractingSLE.Theorem14.GW2Ni
