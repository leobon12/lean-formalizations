/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2NeRel

/-!
# The glued root-`x` relative driver before a finite first contact

Packet PROVE-GW2-NEARIMG2, decision D69 (RELDET's `CanonContactStatement`). The setting of `GW2NeRel`, with a finite
first root-`x` contact `τ` of `x + γ` with the retained prefix. Every horizon `v < τ` is good; J31's capacity readers
of such horizons agree on their overlaps (`GW2Rz.reader_compat`). Gluing them gives one driver `cDrv`, continuous at
every clock value before `τ`, generating the re-centred relative hulls at the clock (`hull_cDrv`), whose trace at the
clock of `t < τ` is `relBdry(x + γ t) − relBdry(x)` (`traceAt_cDrv`).

* `cDrv`;
* `lt_min_of_contact`, `contact_pos'`, `cClk_props`, `pos_of_lt_gClk`, `cDrv_eq_read`, `exists_chain_cDrv`,
  `continuousAt_cDrv`, `cDrv_zero`, **`hull_cDrv`**, **`isGeneratingTrace_cDrv`**, `tip_eq_c`, `continuousOn_cDrv`,
  **`traceAt_cDrv`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory Complex
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull)

namespace InteractingSLE.Theorem14.GW2Ni

open Exist Staged StagedLaw Restart Supp8.GB6 Supp8.GB6.CoordB Supp8.GB6.ReadD GW2TipSystem GW2Rz

open scoped Classical in
/-- **The glued relative driver before the contact `τ`**: at a relative time `u` below the clock of some horizon
`v < τ`, the reader of such a horizon (`0` past every such clock value). -/
def cDrv (x : ℝ) (s : ℝ≥0) (cf : RecData) (w : ℝ≥0 → ℝ) (τ : ℝ≥0) (u : ℝ≥0) : ℝ :=
  if h : ∃ v : ℝ≥0, v < τ ∧ (u : ℝ) < gClk x s cf w v then gRead x s cf w h.choose u else 0

section Sample

variable {Ω : Type*} (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω)
  {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace (W · ω) ⊤ α)
  (hW : Continuous (W · ω)) (hW0 : W 0 ω = 0) (hζ : ζ ω = ⊤)
  {s : ℝ≥0} (hs : 0 < s) {x : ℝ} (hx : 0 ≤ x) (harc : ∀ u ∈ Icc 0 s, x * ‖α u‖ < 1)
  {w : ℝ≥0 → ℝ} (hwc : Continuous w) (hw0 : w 0 = 0) {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace w ⊤ γ)
  {τ : ℝ≥0} (hT : firstContactTime (fun t => sphereInv (((x : ℂ) + γ t : ℂ) : OnePoint ℂ))
    ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s) = (τ : ℝ≥0∞))

include hT in
/-- Every horizon before the contact is good. -/
theorem lt_min_of_contact {v : ℝ≥0} (hv : v < τ) :
    (v : ℝ≥0∞) < min (firstContactTime (fun t => sphereInv (((x : ℂ) + γ t : ℂ) : OnePoint ℂ))
      ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s)) (w, (⊤ : ℝ≥0∞)).2 :=
  lt_min (by rw [hT]; exact ENNReal.coe_lt_coe.2 hv) ENNReal.coe_lt_top

include hα hx harc hγ hT in
/-- The contact is positive. -/
theorem contact_pos' : 0 < τ := by
  have h := GW2Rz.contact_pos W ω hα hx harc hγ (s := s)
  rw [hT] at h
  exact ENNReal.coe_pos.1 h

include hα hW hW0 hζ hs hx harc hwc hw0 hγ hT in
/-- **The root-`x` clock before the contact**: `0` at `0`, strictly increasing and continuous on `[0, τ)`. -/
theorem cClk_props :
    gClk x s (cfRec s W ζ ω) w 0 = 0 ∧ StrictMonoOn (gClk x s (cfRec s W ζ ω) w) (Iio τ) ∧
      ContinuousOn (gClk x s (cfRec s W ζ ω) w) (Iio τ) := by
  obtain ⟨h0, hm, hc⟩ := GW2Rz.clock_props W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ
  have hset : {t : ℝ≥0 | (t : ℝ≥0∞) < firstContactTime (fun t => sphereInv (((x : ℂ) + γ t : ℂ) : OnePoint ℂ))
      ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s)} = Iio τ := by
    rw [hT]
    ext t
    simp only [mem_ofPred_eq, ENNReal.coe_lt_coe, mem_Iio]
  rw [hset] at hm hc
  exact ⟨h0, hm, hc⟩

include hα hW hW0 hζ hs hx harc hwc hw0 hγ hT in
/-- A horizon with a clock value above a relative time is positive. -/
theorem pos_of_lt_gClk {v u : ℝ≥0} (hu : (u : ℝ) < gClk x s (cfRec s W ζ ω) w v) : 0 < v := by
  obtain ⟨h0, -, -⟩ := cClk_props W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT
  refine pos_iff_ne_zero.2 fun hv => ?_
  rw [hv, h0] at hu
  exact absurd hu (not_lt.2 u.coe_nonneg)

include hα hW hW0 hζ hs hx harc hwc hw0 hγ hT in
/-- **The glued driver is the reader of every horizon before the contact, below its clock.** -/
theorem cDrv_eq_read {v : ℝ≥0} (hvτ : v < τ) {u : ℝ≥0} (hu : (u : ℝ) < gClk x s (cfRec s W ζ ω) w v) :
    cDrv x s (cfRec s W ζ ω) w τ u = gRead x s (cfRec s W ζ ω) w v u := by
  have he : IsRegularDriver (w, (⊤ : ℝ≥0∞)) := Gm.isRegularDriver_top hwc hw0
  have hex : ∃ v : ℝ≥0, v < τ ∧ (u : ℝ) < gClk x s (cfRec s W ζ ω) w v := ⟨v, hvτ, hu⟩
  obtain ⟨hτ', hu'⟩ := hex.choose_spec
  have e : cDrv x s (cfRec s W ζ ω) w τ u = gRead x s (cfRec s W ζ ω) w hex.choose u := by
    simp only [cDrv, hex, ↓reduceDIte]
  rw [e]
  have hv0 := pos_of_lt_gClk W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT hu
  have hv0' := pos_of_lt_gClk W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT hu'
  rcases le_total hex.choose v with h | h
  · exact reader_compat W ζ ω hα hW hW0 hζ hs hx harc he hγ h hv0' (lt_min_of_contact hT hvτ) hu'
  · exact (reader_compat W ζ ω hα hW hW0 hζ hs hx harc he hγ h hv0 (lt_min_of_contact hT hτ') hu).symm

include hα hW hW0 hζ hs hx harc hwc hw0 hγ hT in
/-- **The glued driver is a re-centred chain driver below the clock of every horizon before the contact.** -/
theorem exists_chain_cDrv {v : ℝ≥0} (hv0 : 0 < v) (hvτ : v < τ) :
    ∃ R : ℝ≥0 → ℝ, Continuous R ∧ R 0 = 0 ∧
      (∀ t ∈ Icc 0 v, fwdHull (fun r : ℝ => R r.toNNReal)
          (RootH29.forwardCapacity x s t (cfRec s W ζ ω, recOf (v : ℝ≥0∞) (w, ⊤))) =
        (fun z : ℂ => z + ((-GW2Bf.relBase x s (cfRec s W ζ ω, recOf (v : ℝ≥0∞) (w, ⊤)) : ℝ) : ℂ)) ''
          RootH29.forwardHull x s t (cfRec s W ζ ω, recOf (v : ℝ≥0∞) (w, ⊤))) ∧
      ∀ u : ℝ≥0, (u : ℝ) < gClk x s (cfRec s W ζ ω) w v → cDrv x s (cfRec s W ζ ω) w τ u = R u := by
  have he : IsRegularDriver (w, (⊤ : ℝ≥0∞)) := Gm.isRegularDriver_top hwc hw0
  obtain ⟨R, hRc, hR0, -, -, -, hRhull, hReq⟩ :=
    reader_eq_chain W ζ ω hα hW hW0 hζ hs hx harc he hγ (lt_min_of_contact hT hvτ) hv0
  refine ⟨R, hRc, hR0, hRhull, fun u hu => ?_⟩
  rw [cDrv_eq_read W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT hvτ hu]
  exact hReq u hu

include hα hW hW0 hζ hs hx harc hwc hw0 hγ hT in
/-- **The glued driver is continuous below the clock of a horizon before the contact.** -/
theorem continuousAt_cDrv {v : ℝ≥0} (hvτ : v < τ) {u : ℝ≥0} (hu : (u : ℝ) < gClk x s (cfRec s W ζ ω) w v) :
    ContinuousAt (cDrv x s (cfRec s W ζ ω) w τ) u := by
  have hv0 := pos_of_lt_gClk W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT hu
  obtain ⟨R, hRc, -, -, hReq⟩ := exists_chain_cDrv W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT hv0 hvτ
  have hnhds : {u' : ℝ≥0 | (u' : ℝ) < gClk x s (cfRec s W ζ ω) w v} ∈ 𝓝 u :=
    (isOpen_lt NNReal.continuous_coe continuous_const).mem_nhds hu
  exact hRc.continuousAt.congr (Filter.eventually_of_mem hnhds fun u' hu'' => (hReq u' hu'').symm)

include hα hW hW0 hζ hs hx harc hwc hw0 hγ hT in
theorem cDrv_zero : cDrv x s (cfRec s W ζ ω) w τ 0 = 0 := by
  obtain ⟨h0, hm, -⟩ := cClk_props W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT
  have hτ0 := contact_pos' W ω hα hx harc hγ hT
  obtain ⟨v, hv0, hvτ⟩ := exists_between hτ0
  obtain ⟨R, -, hR0, -, hReq⟩ := exists_chain_cDrv W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT hv0 hvτ
  have h1 : ((0 : ℝ≥0) : ℝ) < gClk x s (cfRec s W ζ ω) w v := by
    rw [NNReal.coe_zero, ← h0]
    exact hm (mem_Iio.2 hτ0) (mem_Iio.2 hvτ) hv0
  rw [hReq 0 h1, hR0]

include hα hW hW0 hζ hs hx harc hwc hw0 hγ hT in
/-- **The glued driver generates the re-centred relative hulls at the clock before the contact.** -/
theorem hull_cDrv {t : ℝ≥0} (ht : t < τ) :
    fwdHull (fun r : ℝ => cDrv x s (cfRec s W ζ ω) w τ r.toNNReal) (gClk x s (cfRec s W ζ ω) w t) =
      (fun z : ℂ => z + ((-GW2Bf.relBase x s (cfRec s W ζ ω, recOf (t : ℝ≥0∞) (w, ⊤)) : ℝ) : ℂ)) ''
        RootH29.forwardHull x s t (cfRec s W ζ ω, recOf (t : ℝ≥0∞) (w, ⊤)) := by
  have he : IsRegularDriver (w, (⊤ : ℝ≥0∞)) := Gm.isRegularDriver_top hwc hw0
  obtain ⟨h0, hm, -⟩ := cClk_props W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT
  set a := gClk x s (cfRec s W ζ ω) w with ha
  obtain ⟨v, htv, hvτ⟩ := exists_between ht
  have hv0 : 0 < v := lt_of_le_of_lt zero_le htv
  obtain ⟨R, -, -, hRhull, hReq⟩ := exists_chain_cDrv W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT hv0 hvτ
  have hτ0 : (0 : ℝ≥0) ∈ Iio τ := lt_of_le_of_lt zero_le ht
  have hat : 0 ≤ a t := h0 ▸ hm.monotoneOn hτ0 ht zero_le
  have hatv : a t < a v := hm ht hvτ htv
  have h1 : fwdHull (fun r : ℝ => cDrv x s (cfRec s W ζ ω) w τ r.toNNReal) (a t) =
      fwdHull (fun r : ℝ => R r.toNNReal) (a t) := by
    refine InteractingSLE.fwdHull_eq_of_eqOn hat (show a t < (a t + a v) / 2 by linarith) fun r hr => ?_
    refine hReq _ ?_
    rw [Real.coe_toNNReal _ hr.1]
    linarith [hr.2]
  have hpreC : RootH29.forwardCapacity x s t (cfRec s W ζ ω, recOf (t : ℝ≥0∞) (w, ⊤)) =
      RootH29.forwardCapacity x s t (cfRec s W ζ ω, recOf (v : ℝ≥0∞) (w, ⊤)) :=
    forwardCapacity_prefix_eq' he _ ENNReal.coe_lt_top htv.le le_rfl
  have hpreH : RootH29.forwardHull x s t (cfRec s W ζ ω, recOf (t : ℝ≥0∞) (w, ⊤)) =
      RootH29.forwardHull x s t (cfRec s W ζ ω, recOf (v : ℝ≥0∞) (w, ⊤)) :=
    forwardHull_prefix_eq he _ ENNReal.coe_lt_top htv.le le_rfl
  rw [h1]
  change fwdHull (fun r : ℝ => R r.toNNReal) (RootH29.forwardCapacity x s t
    (cfRec s W ζ ω, recOf (t : ℝ≥0∞) (w, ⊤))) = _
  rw [hpreC, hpreH]
  exact hRhull t ⟨zero_le, htv.le⟩

include hα hW hW0 hζ hs hx harc hwc hw0 hγ hT in
/-- **The capacity tip of every horizon before the contact generates the glued driver up to its clock.** -/
theorem isGeneratingTrace_cDrv {v : ℝ≥0} (hvτ : v < τ) :
    IsGeneratingTrace (cDrv x s (cfRec s W ζ ω) w τ) (ENNReal.ofReal (gClk x s (cfRec s W ζ ω) w v))
      (fun u => RootI30.capacityTipRead x s v u (cfRec s W ζ ω, recOf (v : ℝ≥0∞) (w, ⊤))) := by
  have he : IsRegularDriver (w, (⊤ : ℝ≥0∞)) := Gm.isRegularDriver_top hwc hw0
  refine GW2Bf.isGeneratingTrace_capacityTip_of_hull W ζ ω hα hW hW0 hζ hs hx harc he hγ
    (lt_min_of_contact hT hvτ) fun q hq => ?_
  have h := hull_cDrv W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT (lt_of_le_of_lt hq.2 hvτ)
  have hpreC : gClk x s (cfRec s W ζ ω) w q =
      RootH29.forwardCapacity x s q (cfRec s W ζ ω, recOf (v : ℝ≥0∞) (w, ⊤)) :=
    forwardCapacity_prefix_eq' he _ ENNReal.coe_lt_top hq.2 le_rfl
  rw [hpreC, forwardHull_prefix_eq he _ ENNReal.coe_lt_top hq.2 le_rfl] at h
  exact h

include hα hW hW0 hζ hs hx harc hwc hw0 hγ hT in
/-- **The capacity tip at the clock of `t` reads the explored curve** in the relative chart (before the contact). -/
theorem tip_eq_c {v t : ℝ≥0} (htv : t ≤ v) (hvτ : v < τ) :
    RootI30.capacityTipRead x s v (gClk x s (cfRec s W ζ ω) w t).toNNReal
        (cfRec s W ζ ω, recOf (v : ℝ≥0∞) (w, ⊤)) =
      relBdry (rdrv (cfRec s W ζ ω)) s ((x : ℂ) + γ t) - relBdry (rdrv (cfRec s W ζ ω)) s x := by
  have he : IsRegularDriver (w, (⊤ : ℝ≥0∞)) := Gm.isRegularDriver_top hwc hw0
  have hv' := lt_min_of_contact hT (w := w) hvτ
  obtain ⟨-, -, h0', hm', hc', -⟩ := RootI30.exists_reader_chain W ζ ω hα hW hW0 hζ hs hx harc he hγ hv'
  set p := (cfRec s W ζ ω, recOf (v : ℝ≥0∞) (w, (⊤ : ℝ≥0∞))) with hp
  set a := fun t => RootH29.forwardCapacity x s t p with hadef
  have h0 : a 0 = 0 := h0'
  have hm : StrictMonoOn a (Icc 0 v) := hm'
  have hc : ContinuousOn a (Icc 0 v) := hc'
  have hset : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (v : ℝ≥0∞)} = Icc 0 v := by
    ext t
    simp only [mem_ofPred_eq, ENNReal.coe_le_coe, mem_Icc, zero_le, true_and]
  have ha : IsClockOn a (v : ℝ≥0∞) := ⟨h0, hset ▸ hm, hset ▸ hc, fun h => (ENNReal.coe_ne_top h).elim⟩
  have hpre : gClk x s (cfRec s W ζ ω) w t = a t := forwardCapacity_prefix_eq' he _ ENNReal.coe_lt_top htv le_rfl
  rw [hpre]
  change RootH29.rootTipRead x s (invClock a (v : ℝ≥0∞) (a t).toNNReal) p = _
  rw [ha.invClock_apply (ENNReal.coe_le_coe.2 htv)]
  exact RootH29.rootTipRead_eq W ζ ω hα hW hW0 hζ hx harc he hγ hv' htv

include hα hW hW0 hζ hs hx harc hwc hw0 hγ hT in
/-- The glued driver is continuous below the clock of a horizon before the contact. -/
theorem continuousOn_cDrv {v : ℝ≥0} (hvτ : v < τ) :
    ContinuousOn (cDrv x s (cfRec s W ζ ω) w τ)
      {u : ℝ≥0 | (u : ℝ≥0∞) < ENNReal.ofReal (gClk x s (cfRec s W ζ ω) w v)} := fun _ hu =>
  (continuousAt_cDrv W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT hvτ
    (ENNReal.coe_lt_ofReal.1 hu)).continuousWithinAt

include hα hW hW0 hζ hs hx harc hwc hw0 hγ hT in
/-- **The trace of the glued driver at the clock of `t < τ` is `relBdry(x + γ t) − relBdry(x)`.** -/
theorem traceAt_cDrv {t : ℝ≥0} (ht : t < τ) :
    LP.traceAt (gClk x s (cfRec s W ζ ω) w t).toNNReal (cDrv x s (cfRec s W ζ ω) w τ) =
      relBdry (rdrv (cfRec s W ζ ω)) s ((x : ℂ) + γ t) - relBdry (rdrv (cfRec s W ζ ω)) s x := by
  obtain ⟨h0, hm, -⟩ := cClk_props W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT
  obtain ⟨v, htv, hvτ⟩ := exists_between ht
  have hτ0 : (0 : ℝ≥0) ∈ Iio τ := lt_of_le_of_lt zero_le ht
  have hat : 0 ≤ gClk x s (cfRec s W ζ ω) w t := h0 ▸ hm.monotoneOn hτ0 ht zero_le
  have hlt : (((gClk x s (cfRec s W ζ ω) w t).toNNReal : ℝ≥0) : ℝ≥0∞) <
      ENNReal.ofReal (gClk x s (cfRec s W ζ ω) w v) := by
    rw [ENNReal.coe_lt_ofReal, Real.coe_toNNReal _ hat]
    exact hm ht hvτ htv
  rw [LP.traceAt_eq_of_isGeneratingTrace (isGeneratingTrace_cDrv W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT hvτ)
    (continuousOn_cDrv W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT hvτ)
    (cDrv_zero W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT) hlt]
  exact tip_eq_c W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT htv.le hvτ

end Sample

end InteractingSLE.Theorem14.GW2Ni
