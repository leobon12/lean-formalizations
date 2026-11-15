/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2GmClock
import InteractingSLE.Spec.Supplement.GW2RootI30Inverse
import InteractingSLE.Spec.Supplement.GW2RootI30Mobius
import InteractingSLE.Spec.Supplement.GW2RootJ31Driver
import InteractingSLE.Foundations.Loewner.CapacityEstimates

/-!
# The centered capacity-time tip generates a continuous driver (step R5's core)

Packet PROVE-GW2-GEOM2. I30 reads the relative capacity tip `RootI30.capacityTipRead x s v u p` (the
centered charted tip at the time where the relative capacity reaches `u`) and J31's stage driver reads
the Loewner driver off it (`RootJ31.capacityDriverRead`, through `RootB23.traceDriverRead`). PROVE-T14-GW2ROOT2
left open that this tip is a generating trace ("the continuous image driver is NOT yet identified with
the centered tip reader's generating driver"). This file proves it, in I30's setting (a regular driver
with a generating trace, read through its record at a cap `v` strictly before contact):

* `fwdHull_subset_closedBall_of_isFilling`: a hull filling a compact set inside a closed disc about a
  real point lies in that disc;
* `driver_zero_eq_center`: the driver of I30's relative chain starts at the chart image of the root;
* **`exists_isGeneratingTrace_capacityTip`**: the centered capacity tip is a generating trace, on
  `[0, A(v)]`, of a continuous driver starting at `0`;
* **`continuousAt_capacityDriverRead`**: hence the capacity driver reader is continuous at every
  capacity strictly below `A(v)`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Complex Metric
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

namespace InteractingSLE.Theorem14.GW2TipSystem.Gm

open Exist Staged StagedLaw Restart Supp8.GB6 Supp8.GB6.CoordB

/-- A hull filling a compact generating set inside a closed disc about a real point lies in the disc. -/
theorem subset_closedBall_of_isFilling {K A : Set ℂ} (hK : K ⊆ H) (hA : IsCompact A)
    (hfill : IsFilling K A) {c r : ℝ} (hAr : A ⊆ closedBall (c : ℂ) r) :
    K ⊆ closedBall (c : ℂ) r := by
  rw [fillH_eq_iff_isFilling_of_isClosed hA.isBounded hA.isClosed hK] at hfill
  rw [hfill]
  exact fillH_subset_closedBall (by rwa [hA.isClosed.closure_eq])

variable {Ω : Type*} (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω)
  {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace (W · ω) ⊤ α)
  (hW : Continuous (W · ω)) (hW0 : W 0 ω = 0) (hζ : ζ ω = ⊤)
  {s : ℝ≥0} (hs : 0 < s) {x : ℝ} (hx : 0 ≤ x) (harc : ∀ u ∈ Icc 0 s, x * ‖α u‖ < 1)
  {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : IsRegularDriver e) {γ : ℝ≥0 → ℂ}
  (hγ : IsGeneratingTrace e.1 e.2 γ) {v : ℝ≥0}
  (hv : (v : ℝ≥0∞) < min
    (firstContactTime (fun t => sphereInv (((x : ℂ) + γ t : ℂ) : OnePoint ℂ))
      ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s)) e.2)

include hα hW hW0 hζ hs hx harc he hγ hv

/-- **The relative capacity tip is a generating trace of a continuous driver from `0`** on the capacity
interval `[0, A(v)]`, where `A t = forwardCapacity x s t p` and `p` is the record pair at the cap `v`. -/
theorem exists_isGeneratingTrace_capacityTip :
    let p := (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e)
    let a := fun t => RootH29.forwardCapacity x s t p
    ∃ w : ℝ≥0 → ℝ, Continuous w ∧ w 0 = 0 ∧
      IsGeneratingTrace w (ENNReal.ofReal (a v)) (fun u => RootI30.capacityTipRead x s v u p) := by
  intro p a
  set U := rdrv (cfRec s W ζ ω) with hUdef
  obtain ⟨V, hV, h0', hm', hc', hK⟩ := RootI30.exists_reader_chain W ζ ω hα hW hW0 hζ hs hx harc he hγ hv
  have h0 : a 0 = 0 := h0'
  have hm : StrictMonoOn a (Icc 0 v) := hm'
  have hc : ContinuousOn a (Icc 0 v) := hc'
  have hKV : ∀ t ∈ Icc 0 v, fwdHull V (a t) = RootH29.forwardHull x s t p := fun t ht => (hK t ht).2.1
  have hrec := GaugeE.record_prefix_eq s hW0 hW.continuousOn
    (show (s : ℝ≥0∞) < ζ ω by rw [hζ]; exact ENNReal.coe_lt_top)
  have hmap : relMap U s = relMap (Ito.rpath (W · ω)) s := relMap_eq_of_eqOn s.coe_nonneg hrec
  -- the clock and its inverse
  have hset : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (v : ℝ≥0∞)} = Icc 0 v := by
    ext t
    simp only [mem_ofPred_eq, ENNReal.coe_le_coe, mem_Icc, zero_le, true_and]
  have ha : IsClockOn a (v : ℝ≥0∞) := ⟨h0, hset ▸ hm, hset ▸ hc, fun h => (ENNReal.coe_ne_top h).elim⟩
  have hlife : capLife a (v : ℝ≥0∞) = ENNReal.ofReal (a v) := by
    rw [capLife, ite_eq_right ENNReal.coe_ne_top, ENNReal.toNNReal_coe]
  -- the physical tip in the chart
  have hsafe : ∀ t ≤ v, (x : ℂ) + γ t ∈ relSafe U s := fun t ht =>
    RootH29.trace_mem_record_relSafe W ζ ω hα hW hW0 hζ hx harc he hγ hv ht
  set c₀ := relBdry U s x with hc₀
  have hsafe0 : (x : ℂ) ∈ relSafe U s := by
    have h := hsafe 0 zero_le
    rwa [hγ.1, add_zero] at h
  have hc₀im : c₀.im = 0 := im_relBdry_of_real (continuous_rdrv _) (rdrv_zero _) s.coe_nonneg hsafe0.2
  have hc₀re : ((c₀.re : ℝ) : ℂ) = c₀ := Complex.ext (by simp) (by simp [hc₀im])
  have htip : ∀ t ≤ v, RootH29.rootTipRead x s t p = relBdry U s ((x : ℂ) + γ t) - c₀ :=
    fun t ht => RootH29.rootTipRead_eq W ζ ω hα hW hW0 hζ hx harc he hγ hv ht
  have hctip := RootH29.continuousOn_rootTipRead W ζ ω hα hW hW0 hζ hx harc he hγ hv
  -- the mapped prefix is compact
  have hcpt : ∀ t ≤ v, IsCompact (relBdry U s '' ((fun q => (x : ℂ) + γ q) '' Icc 0 t)) := by
    intro t ht
    have hpc : ContinuousOn (fun q => (x : ℂ) + γ q) (Icc 0 t) :=
      continuousOn_const.add (hγ.2.1.mono fun q hq =>
        ((ENNReal.coe_le_coe.mpr (hq.2.trans ht)).trans (lt_min_iff.mp hv).2.le))
    have hK1 := isCompact_Icc.image_of_continuousOn hpc
    refine hK1.image_of_continuousOn ((continuousOn_relBdry (continuous_rdrv _) (rdrv_zero _)
      s.coe_nonneg).mono ?_)
    rintro _ ⟨q, hq, rfl⟩
    exact hsafe q (hq.2.trans ht)
  -- the forward hull fills the mapped prefix
  have hfill : ∀ t ∈ Icc 0 v, IsFilling (RootH29.forwardHull x s t p)
      (relBdry U s '' ((fun q => (x : ℂ) + γ q) '' Icc 0 t)) := by
    intro t ht
    have h := (hK t ht).2.2
    rw [← hmap] at h
    have hcomm : (fun q => γ q + (x : ℂ)) = (fun q => (x : ℂ) + γ q) :=
      funext fun q => add_comm _ _
    rw [hcomm] at h
    have hsubA : (fun q => (x : ℂ) + γ q) '' Icc 0 t ⊆ relSafe U s := by
      rintro _ ⟨q, hq, rfl⟩
      exact hsafe q (hq.2.trans ht.2)
    refine (isFilling_congr_inter_H ?_).1 h
    rw [← image_relBdry_inter_H (continuous_rdrv _) (rdrv_zero _) s.coe_nonneg hsubA,
      inter_assoc, inter_self]
  have hKH : ∀ t ∈ Icc 0 v, RootH29.forwardHull x s t p ⊆ H := by
    intro t ht
    rw [← hKV t ht]
    exact fun z hz => hz.1
  -- the driver starts at the chart image of the root
  have hV0 : 0 < v → V 0 = c₀.re := by
    intro hv0
    have hball : ∀ ε > 0, ‖((V 0 : ℝ) : ℂ) - c₀‖ ≤ ε := by
      intro ε hε
      have hct : ContinuousWithinAt (fun t => RootH29.rootTipRead x s t p) (Icc 0 v) 0 :=
        hctip 0 ⟨le_rfl, zero_le⟩
      have h00 : RootH29.rootTipRead x s 0 p = 0 := by
        rw [htip 0 zero_le, hγ.1, add_zero, sub_self]
      obtain ⟨δ, hδ, hδc⟩ := Metric.continuousWithinAt_iff.1 hct ε hε
      set t : ℝ≥0 := min v ⟨δ / 2, by positivity⟩ with htdef
      have htv : t ≤ v := min_le_left _ _
      have htpos : 0 < t := lt_min hv0 (by change (0 : ℝ) < δ / 2; positivity)
      have htδ : (t : ℝ) < δ := by
        have : (t : ℝ) ≤ δ / 2 := by
          change ((min v ⟨δ / 2, _⟩ : ℝ≥0) : ℝ) ≤ δ / 2
          exact (NNReal.coe_le_coe.2 (min_le_right _ _)).trans le_rfl
        linarith
      have hA : relBdry U s '' ((fun q => (x : ℂ) + γ q) '' Icc 0 t) ⊆ closedBall (c₀.re : ℂ) ε := by
        rintro _ ⟨_, ⟨q, hq, rfl⟩, rfl⟩
        have hqv : q ≤ v := hq.2.trans htv
        have hd := hδc ⟨zero_le, hqv⟩ (by
          rw [NNReal.dist_eq, NNReal.coe_zero, sub_zero, abs_of_nonneg (NNReal.coe_nonneg q)]
          exact (NNReal.coe_le_coe.2 hq.2).trans_lt htδ)
        rw [h00, dist_zero_right, htip q hqv] at hd
        rw [mem_closedBall, hc₀re, dist_eq]
        exact hd.le
      have hsub := subset_closedBall_of_isFilling (hKH t ⟨zero_le, htv⟩) (hcpt t htv)
        (hfill t ⟨zero_le, htv⟩) hA
      have hapos : 0 < a t := by
        have := hm (show (0 : ℝ≥0) ∈ Icc 0 v from ⟨le_rfl, zero_le⟩) ⟨zero_le, htv⟩ htpos
        simpa only [h0] using this
      have hmem := RootI30.initial_mem_closure_fwdHull hV hapos
      rw [hKV t ⟨zero_le, htv⟩] at hmem
      have hcl := closure_minimal hsub isClosed_closedBall hmem
      rw [mem_closedBall, dist_eq, hc₀re] at hcl
      exact hcl
    have hz : ((V 0 : ℝ) : ℂ) = c₀ :=
      eq_of_forall_dist_le fun ε hε => by rw [dist_eq]; exact hball ε hε
    rw [← hc₀re] at hz
    exact_mod_cast hz
  refine ⟨fun u => V u - V 0, (hV.comp NNReal.continuous_coe).sub continuous_const,
    by simp only [NNReal.coe_zero, sub_self], ?_⟩
  -- the generating property
  have hsub : {u : ℝ≥0 | (u : ℝ≥0∞) ≤ ENNReal.ofReal (a v)} ⊆
      {u | (u : ℝ≥0∞) ≤ capLife a (v : ℝ≥0∞)} := by
    intro u hu
    change (u : ℝ≥0∞) ≤ capLife a (v : ℝ≥0∞)
    rwa [hlife]
  refine ⟨?_, ?_, ?_⟩
  · -- starts at zero
    have hz := ha.invClock_apply (r := 0) (bot_le : (0 : ℝ≥0∞) ≤ (v : ℝ≥0∞))
    rw [ha.zero, Real.toNNReal_zero] at hz
    change RootH29.rootTipRead x s (invClock a (v : ℝ≥0∞) 0) p = 0
    rw [hz, htip 0 zero_le, hγ.1, add_zero, sub_self]
  · -- continuous through the closed horizon
    exact hctip.comp (ha.continuousOn_invClock.mono hsub) (fun u hu =>
      ⟨zero_le, ENNReal.coe_le_coe.mp (ha.invClock_spec (hsub hu)).1⟩)
  · -- the filling
    intro u hu
    have hu' : (u : ℝ≥0∞) ≤ capLife a (v : ℝ≥0∞) := hsub (le_of_lt hu)
    obtain ⟨htv', hat⟩ := ha.invClock_spec hu'
    set t := invClock a (v : ℝ≥0∞) u with htdef
    have htv : t ≤ v := ENNReal.coe_le_coe.mp htv'
    have hvpos : 0 < v := by
      by_contra hv0
      have hv00 : v = 0 := le_antisymm (not_lt.1 hv0) zero_le
      have : a v = 0 := by rw [hv00]; exact h0
      rw [this, ENNReal.ofReal_zero] at hu
      exact absurd hu (not_lt.2 zero_le)
    -- the driver hull
    have hhull : fwdHull (fun r : ℝ => (fun u : ℝ≥0 => V u - V 0) r.toNNReal) u =
        (fun z : ℂ => z + ((-c₀.re : ℝ) : ℂ)) '' RootH29.forwardHull x s t p := by
      have h1 : fwdHull (fun r : ℝ => (fun u : ℝ≥0 => V u - V 0) r.toNNReal) u =
          fwdHull (fun r => V r + (-c₀.re)) u := by
        refine YuanCorollary13.fwdHull_eq_of_eqOn_Icc
          ((hV.comp (NNReal.continuous_coe.comp continuous_real_toNNReal)).sub continuous_const)
          (hV.add continuous_const) u.2 fun r hr => ?_
        show V ((r.toNNReal : ℝ≥0) : ℝ) - V 0 = V r + -c₀.re
        rw [Real.coe_toNNReal r hr.1, hV0 hvpos, sub_eq_add_neg]
      rw [h1, ConformalImageFull.fwdHull_add_const, ← hKV t ⟨zero_le, htv⟩, hat]
    -- the tip image
    have hneg : (((-c₀.re : ℝ)) : ℂ) = -c₀ := by rw [ofReal_neg, hc₀re]
    have himg : (fun u => RootI30.capacityTipRead x s v u p) '' Icc 0 u =
        (fun z : ℂ => z + ((-c₀.re : ℝ) : ℂ)) ''
          (relBdry U s '' ((fun q => (x : ℂ) + γ q) '' Icc 0 t)) := by
      rw [image_image, image_image]
      ext z
      constructor
      · rintro ⟨u', hu'm, rfl⟩
        have hu'l : (u' : ℝ≥0∞) ≤ capLife a (v : ℝ≥0∞) :=
          (ENNReal.coe_le_coe.2 hu'm.2).trans hu'
        obtain ⟨ht'v, hat'⟩ := ha.invClock_spec hu'l
        have ht'v' : invClock a (v : ℝ≥0∞) u' ≤ v := ENNReal.coe_le_coe.mp ht'v
        have hle : invClock a (v : ℝ≥0∞) u' ≤ t := by
          by_contra hlt
          have := hm ⟨zero_le, htv⟩ ⟨zero_le, ht'v'⟩ (lt_of_not_ge hlt)
          rw [hat, hat'] at this
          exact absurd (NNReal.coe_le_coe.2 hu'm.2) (not_le.2 this)
        refine ⟨invClock a (v : ℝ≥0∞) u', ⟨zero_le, hle⟩, ?_⟩
        change _ = RootH29.rootTipRead x s (invClock a (v : ℝ≥0∞) u') p
        rw [htip _ ht'v', hneg]
        ring
      · rintro ⟨t', ht', rfl⟩
        have ht'v : t' ≤ v := ht'.2.trans htv
        refine ⟨(a t').toNNReal, ⟨zero_le, ?_⟩, ?_⟩
        · have hle : a t' ≤ a t := hm.monotoneOn ⟨zero_le, ht'v⟩ ⟨zero_le, htv⟩ ht'.2
          rw [hat] at hle
          exact Real.toNNReal_le_iff_le_coe.2 hle
        · change RootH29.rootTipRead x s (invClock a (v : ℝ≥0∞) (a t').toNNReal) p = _
          rw [ha.invClock_apply (ENNReal.coe_le_coe.2 ht'v), htip t' ht'v, hneg]
          ring
    rw [hhull, himg]
    have hHP : IsHPHull (RootH29.forwardHull x s t p) := by
      rw [← hKV t ⟨zero_le, htv⟩, hat]
      exact isHPHull_fwdHull hV u.2
    exact RootI30.isFilling_image_add_full hHP (-c₀.re) (hfill t ⟨zero_le, htv⟩)

/-- **The capacity driver reader is continuous below the capacity horizon.** -/
theorem continuousAt_capacityDriverRead {u : ℝ≥0}
    (hu : (u : ℝ) < RootH29.forwardCapacity x s v (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e)) :
    ContinuousAt (fun c => RootJ31.capacityDriverRead x s v c (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e))
      u := by
  obtain ⟨w, hwc, hw0, hgen⟩ :=
    exists_isGeneratingTrace_capacityTip W ζ ω hα hW hW0 hζ hs hx harc he hγ hv
  exact RootB23.continuousAt_traceDriverRead hgen hwc.continuousOn hw0
    (by rw [← ENNReal.ofReal_coe_nnreal]; exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg u.2).2 hu)

end InteractingSLE.Theorem14.GW2TipSystem.Gm
