/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BtCanon
import InteractingSLE.Spec.Supplement.GW2NeLim

/-!
# The glued root-`x` relative driver when the explored curve never touches the retained prefix

Packet PROVE-GW2-NEARIMG2, decision D56 (`UncEndStatement`), the deterministic part on one sample. At a root `x ≥ 0`,
with the counterflow `(W, α)` and an explored driver `w` with generating trace `γ` on `[0, ∞)`, suppose the root-`x`
first contact of `x + γ` with the retained prefix `α([0, s])` never happens. Then every horizon `v` is good, and
J31's capacity readers of the horizons agree on their overlaps (`GW2Rz.reader_compat`). Gluing them gives one driver
`gDrv`, continuous at every value of the root-`x` clock `a` (`gClk`), generating the re-centred relative hulls at the
clock (`hull_gDrv`), whose trace at the clock of `t` is `relBdry(x + γ t) − relBdry(x)` (`traceAt_gDrv`).

* `gClk`, `gRead`, `gDrv`;
* `gClk_props` (`a 0 = 0`, `a` strictly increasing and continuous), `gDrv_eq_read`, `exists_chain_gDrv`,
  `continuousAt_gDrv`, `gDrv_zero`, **`hull_gDrv`**, **`isGeneratingTrace_gDrv`**, `tip_eq`, **`traceAt_gDrv`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory Complex
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull)

namespace InteractingSLE.Theorem14.GW2Ni

open Exist Staged StagedLaw Restart Supp8.GB6 Supp8.GB6.CoordB Supp8.GB6.ReadD GW2TipSystem GW2Rz

/-- **The root-`x` clock** of an explored driver `w` at a counterflow record `cf`: ROOT2's capacity reader with the
horizon at the time. -/
def gClk (x : ℝ) (s : ℝ≥0) (cf : RecData) (w : ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ :=
  RootH29.forwardCapacity x s t (cf, recOf (t : ℝ≥0∞) (w, ⊤))

/-- **J31's capacity reader of the horizon `v`.** -/
def gRead (x : ℝ) (s : ℝ≥0) (cf : RecData) (w : ℝ≥0 → ℝ) (v u : ℝ≥0) : ℝ :=
  RootJ31.capacityDriverRead x s v u (cf, recOf (v : ℝ≥0∞) (w, ⊤))

open scoped Classical in
/-- **The glued relative driver**: at a relative time `u` below the clock of some horizon `n + 1`, the reader of such
a horizon (`0` past every clock value). -/
def gDrv (x : ℝ) (s : ℝ≥0) (cf : RecData) (w : ℝ≥0 → ℝ) (u : ℝ≥0) : ℝ :=
  if h : ∃ n : ℕ, (u : ℝ) < gClk x s cf w ((n : ℝ≥0) + 1) then gRead x s cf w ((h.choose : ℝ≥0) + 1) u else 0

section Sample

variable {Ω : Type*} (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω)
  {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace (W · ω) ⊤ α)
  (hW : Continuous (W · ω)) (hW0 : W 0 ω = 0) (hζ : ζ ω = ⊤)
  {s : ℝ≥0} (hs : 0 < s) {x : ℝ} (hx : 0 ≤ x) (harc : ∀ u ∈ Icc 0 s, x * ‖α u‖ < 1)
  {w : ℝ≥0 → ℝ} (hwc : Continuous w) (hw0 : w 0 = 0) {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace w ⊤ γ)
  (hT : firstContactTime (fun t => sphereInv (((x : ℂ) + γ t : ℂ) : OnePoint ℂ))
    ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s) = ⊤)

include hT in
/-- Without a contact every horizon is good. -/
theorem lt_min_of_noContact (v : ℝ≥0) :
    (v : ℝ≥0∞) < min (firstContactTime (fun t => sphereInv (((x : ℂ) + γ t : ℂ) : OnePoint ℂ))
      ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s)) (w, (⊤ : ℝ≥0∞)).2 := by
  rw [hT, min_self]
  exact ENNReal.coe_lt_top

include hα hW hW0 hζ hs hx harc hwc hw0 hγ hT in
/-- **The root-`x` clock without contact**: `0` at `0`, strictly increasing and continuous on `[0, ∞)`. -/
theorem gClk_props :
    gClk x s (cfRec s W ζ ω) w 0 = 0 ∧ StrictMono (gClk x s (cfRec s W ζ ω) w) ∧
      Continuous (gClk x s (cfRec s W ζ ω) w) := by
  obtain ⟨h0, hm, hc⟩ := GW2Rz.clock_props W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ
  have hset : {t : ℝ≥0 | (t : ℝ≥0∞) < firstContactTime (fun t => sphereInv (((x : ℂ) + γ t : ℂ) : OnePoint ℂ))
      ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s)} = univ := by
    rw [hT]
    ext t
    simp only [mem_ofPred_eq, ENNReal.coe_lt_top, mem_univ]
  rw [hset] at hm hc
  exact ⟨h0, strictMonoOn_univ.1 hm, continuousOn_univ.1 hc⟩

include hα hW hW0 hζ hs hx harc hwc hw0 hγ hT in
/-- **The glued driver is the reader of every horizon below its clock.** -/
theorem gDrv_eq_read {v : ℝ≥0} (hv0 : 0 < v) {u : ℝ≥0} (hu : (u : ℝ) < gClk x s (cfRec s W ζ ω) w v) :
    gDrv x s (cfRec s W ζ ω) w u = gRead x s (cfRec s W ζ ω) w v u := by
  have he : IsRegularDriver (w, (⊤ : ℝ≥0∞)) := Gm.isRegularDriver_top hwc hw0
  obtain ⟨-, hm, -⟩ := gClk_props W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT
  have hex : ∃ n : ℕ, (u : ℝ) < gClk x s (cfRec s W ζ ω) w ((n : ℝ≥0) + 1) := by
    refine ⟨⌈(v : ℝ≥0)⌉₊, hu.trans_le (hm.monotone ?_)⟩
    exact (Nat.le_ceil v).trans (le_add_of_nonneg_right zero_le_one)
  have hn := hex.choose_spec
  have e : gDrv x s (cfRec s W ζ ω) w u = gRead x s (cfRec s W ζ ω) w ((hex.choose : ℝ≥0) + 1) u := by
    simp only [gDrv, hex, ↓reduceDIte]
  rw [e]
  rcases le_total ((hex.choose : ℝ≥0) + 1) v with h | h
  · exact reader_compat W ζ ω hα hW hW0 hζ hs hx harc he hγ h (add_pos_of_nonneg_of_pos zero_le one_pos)
      (lt_min_of_noContact hT v) hn
  · exact (reader_compat W ζ ω hα hW hW0 hζ hs hx harc he hγ h hv0
      (lt_min_of_noContact hT _) hu).symm

include hα hW hW0 hζ hs hx harc hwc hw0 hγ hT in
/-- **The glued driver is a re-centred chain driver below the clock of every horizon.** -/
theorem exists_chain_gDrv {v : ℝ≥0} (hv0 : 0 < v) :
    ∃ R : ℝ≥0 → ℝ, Continuous R ∧ R 0 = 0 ∧
      (∀ t ∈ Icc 0 v, fwdHull (fun r : ℝ => R r.toNNReal)
          (RootH29.forwardCapacity x s t (cfRec s W ζ ω, recOf (v : ℝ≥0∞) (w, ⊤))) =
        (fun z : ℂ => z + ((-GW2Bf.relBase x s (cfRec s W ζ ω, recOf (v : ℝ≥0∞) (w, ⊤)) : ℝ) : ℂ)) ''
          RootH29.forwardHull x s t (cfRec s W ζ ω, recOf (v : ℝ≥0∞) (w, ⊤))) ∧
      ∀ u : ℝ≥0, (u : ℝ) < gClk x s (cfRec s W ζ ω) w v → gDrv x s (cfRec s W ζ ω) w u = R u := by
  have he : IsRegularDriver (w, (⊤ : ℝ≥0∞)) := Gm.isRegularDriver_top hwc hw0
  obtain ⟨R, hRc, hR0, -, -, -, hRhull, hReq⟩ :=
    reader_eq_chain W ζ ω hα hW hW0 hζ hs hx harc he hγ (lt_min_of_noContact hT v) hv0
  refine ⟨R, hRc, hR0, hRhull, fun u hu => ?_⟩
  rw [gDrv_eq_read W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT hv0 hu]
  exact hReq u hu

include hα hW hW0 hζ hs hx harc hwc hw0 hγ hT in
/-- **The glued driver is continuous below the clock of some horizon.** -/
theorem continuousAt_gDrv {v : ℝ≥0} {u : ℝ≥0} (hu : (u : ℝ) < gClk x s (cfRec s W ζ ω) w v) :
    ContinuousAt (gDrv x s (cfRec s W ζ ω) w) u := by
  obtain ⟨-, hm, hc⟩ := gClk_props W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT
  have hu' : (u : ℝ) < gClk x s (cfRec s W ζ ω) w (v + 1) := hu.trans (hm (lt_add_one v))
  obtain ⟨R, hRc, -, -, hReq⟩ :=
    exists_chain_gDrv W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT (add_pos_of_nonneg_of_pos zero_le one_pos)
  have hnhds : {u' : ℝ≥0 | (u' : ℝ) < gClk x s (cfRec s W ζ ω) w (v + 1)} ∈ 𝓝 u :=
    (isOpen_lt NNReal.continuous_coe continuous_const).mem_nhds hu'
  exact hRc.continuousAt.congr (Filter.eventually_of_mem hnhds fun u' hu'' => (hReq u' hu'').symm)

include hα hW hW0 hζ hs hx harc hwc hw0 hγ hT in
theorem gDrv_zero : gDrv x s (cfRec s W ζ ω) w 0 = 0 := by
  obtain ⟨h0, hm, -⟩ := gClk_props W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT
  obtain ⟨R, -, hR0, -, hReq⟩ := exists_chain_gDrv W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT one_pos
  have h1 : ((0 : ℝ≥0) : ℝ) < gClk x s (cfRec s W ζ ω) w 1 := by
    rw [NNReal.coe_zero, ← h0]; exact hm one_pos
  rw [hReq 0 h1, hR0]

include hα hW hW0 hζ hs hx harc hwc hw0 hγ hT in
/-- **The glued driver generates the re-centred relative hulls at the clock.** -/
theorem hull_gDrv (t : ℝ≥0) :
    fwdHull (fun r : ℝ => gDrv x s (cfRec s W ζ ω) w r.toNNReal) (gClk x s (cfRec s W ζ ω) w t) =
      (fun z : ℂ => z + ((-GW2Bf.relBase x s (cfRec s W ζ ω, recOf (t : ℝ≥0∞) (w, ⊤)) : ℝ) : ℂ)) ''
        RootH29.forwardHull x s t (cfRec s W ζ ω, recOf (t : ℝ≥0∞) (w, ⊤)) := by
  have he : IsRegularDriver (w, (⊤ : ℝ≥0∞)) := Gm.isRegularDriver_top hwc hw0
  obtain ⟨h0, hm, -⟩ := gClk_props W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT
  set a := gClk x s (cfRec s W ζ ω) w with ha
  set v : ℝ≥0 := t + 1 with hv
  have htv : t < v := lt_add_one t
  obtain ⟨R, -, -, hRhull, hReq⟩ := exists_chain_gDrv W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT
    (add_pos_of_nonneg_of_pos zero_le one_pos : (0 : ℝ≥0) < v)
  have hat : 0 ≤ a t := h0 ▸ hm.monotone zero_le
  have hatv : a t < a v := hm htv
  have h1 : fwdHull (fun r : ℝ => gDrv x s (cfRec s W ζ ω) w r.toNNReal) (a t) =
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
/-- **The capacity tip of every horizon generates the glued driver up to the horizon's clock.** -/
theorem isGeneratingTrace_gDrv (v : ℝ≥0) :
    IsGeneratingTrace (gDrv x s (cfRec s W ζ ω) w) (ENNReal.ofReal (gClk x s (cfRec s W ζ ω) w v))
      (fun u => RootI30.capacityTipRead x s v u (cfRec s W ζ ω, recOf (v : ℝ≥0∞) (w, ⊤))) := by
  have he : IsRegularDriver (w, (⊤ : ℝ≥0∞)) := Gm.isRegularDriver_top hwc hw0
  refine GW2Bf.isGeneratingTrace_capacityTip_of_hull W ζ ω hα hW hW0 hζ hs hx harc he hγ
    (lt_min_of_noContact hT v) fun q hq => ?_
  have h := hull_gDrv W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT q
  have hpreC : gClk x s (cfRec s W ζ ω) w q =
      RootH29.forwardCapacity x s q (cfRec s W ζ ω, recOf (v : ℝ≥0∞) (w, ⊤)) :=
    forwardCapacity_prefix_eq' he _ ENNReal.coe_lt_top hq.2 le_rfl
  rw [hpreC, forwardHull_prefix_eq he _ ENNReal.coe_lt_top hq.2 le_rfl] at h
  exact h

include hα hW hW0 hζ hs hx harc hwc hw0 hγ hT in
/-- **The capacity tip at the clock of `t` reads the explored curve** in the relative chart. -/
theorem tip_eq {v t : ℝ≥0} (htv : t ≤ v) :
    RootI30.capacityTipRead x s v (gClk x s (cfRec s W ζ ω) w t).toNNReal
        (cfRec s W ζ ω, recOf (v : ℝ≥0∞) (w, ⊤)) =
      relBdry (rdrv (cfRec s W ζ ω)) s ((x : ℂ) + γ t) - relBdry (rdrv (cfRec s W ζ ω)) s x := by
  have he : IsRegularDriver (w, (⊤ : ℝ≥0∞)) := Gm.isRegularDriver_top hwc hw0
  have hv' := lt_min_of_noContact hT (w := w) v
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
/-- The glued driver is continuous below the clock of a horizon. -/
theorem continuousOn_gDrv (v : ℝ≥0) :
    ContinuousOn (gDrv x s (cfRec s W ζ ω) w)
      {u : ℝ≥0 | (u : ℝ≥0∞) < ENNReal.ofReal (gClk x s (cfRec s W ζ ω) w v)} := fun _ hu =>
  (continuousAt_gDrv W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT
    (ENNReal.coe_lt_ofReal.1 hu)).continuousWithinAt

include hα hW hW0 hζ hs hx harc hwc hw0 hγ hT in
/-- **The trace of the glued driver at the clock of `t` is `relBdry(x + γ t) − relBdry(x)`.** -/
theorem traceAt_gDrv (t : ℝ≥0) :
    LP.traceAt (gClk x s (cfRec s W ζ ω) w t).toNNReal (gDrv x s (cfRec s W ζ ω) w) =
      relBdry (rdrv (cfRec s W ζ ω)) s ((x : ℂ) + γ t) - relBdry (rdrv (cfRec s W ζ ω)) s x := by
  obtain ⟨h0, hm, -⟩ := gClk_props W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT
  have hat : 0 ≤ gClk x s (cfRec s W ζ ω) w t := h0 ▸ hm.monotone zero_le
  have hlt : (((gClk x s (cfRec s W ζ ω) w t).toNNReal : ℝ≥0) : ℝ≥0∞) <
      ENNReal.ofReal (gClk x s (cfRec s W ζ ω) w (t + 1)) := by
    rw [ENNReal.coe_lt_ofReal, Real.coe_toNNReal _ hat]
    exact hm (lt_add_one t)
  rw [LP.traceAt_eq_of_isGeneratingTrace (isGeneratingTrace_gDrv W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT _)
    (continuousOn_gDrv W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT _)
    (gDrv_zero W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT) hlt]
  exact tip_eq W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hT (lt_add_one t).le

end Sample

end InteractingSLE.Theorem14.GW2Ni
