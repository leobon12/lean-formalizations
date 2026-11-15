/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RzLive
import InteractingSLE.Spec.Supplement.GW2BnMain

/-!
# The canonical driver at a root `x` reads the explored curve `x + γ`

Packet PROVE-GW2-BUF (round 17; the root-`x` contact clause, step 1). At a root `x ≥ 0`, the explored curve is
`x + γ` and the counterflow `(W, α)` starts at `0` (ROOTX's `contactX`, `clockX`, `hullX`). Suppose a canonical driver
`Wc` has the re-centred relative hulls before the root-`x` contact, and has a generating trace `ηc` living past every
clock value there. Then before the contact, `x + γ t` is safe and
`ηc (a t) = relBdry (x + γ t) − relBdry x`, where `a` is the root-`x` clock.

Proof: at a good horizon `v > t`, BUF's `GW2Bf.isGeneratingTrace_capacityTip_of_hull` gives a generating trace of
`Wc` up to `a v` (ROOT2's capacity tip). Two generating traces of one driver are its canonical trace
(`LP.traceAt_eq_of_isGeneratingTrace`). ROOT2's tip reader at the horizon is `relBdry (x + γ t) − relBdry x`
(`RootH29.rootTipRead_eq`).

* `relSafe_record_eq`, `relBdry_record_eq` (the record driver and the counterflow path have one relative chart);
* **`canonicalX_eq_relBdry`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory Complex
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull)

namespace InteractingSLE.Theorem14.GW2Bh

open Exist Staged StagedLaw Restart Supp8.GB6 Supp8.GB6.CoordB Supp8.GB6.ReadD GW2TipSystem GW2Rz

section Record

variable {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {ω : Ω} (s : ℝ≥0)
  (hW0 : W 0 ω = 0) (hW : Continuous (W · ω)) (hζ : ζ ω = ⊤)

include hW0 hW hζ

theorem invHull_record_eq :
    Supp8.Q3Rel.invHull (rdrv (cfRec s W ζ ω)) s = Supp8.Q3Rel.invHull (rp (W · ω)) s := by
  have h : fwdHull (rdrv (cfRec s W ζ ω)) s = fwdHull (rp (W · ω)) s :=
    GaugeE.record_hull_eq s hW0 hW.continuousOn (by rw [hζ]; exact ENNReal.coe_lt_top)
  unfold Supp8.Q3Rel.invHull
  rw [h]

/-- The record driver and the counterflow path have the same safe set. -/
theorem relSafe_record_eq : relSafe (rdrv (cfRec s W ζ ω)) s = relSafe (rp (W · ω)) s := by
  unfold relSafe
  rw [invHull_record_eq s hW0 hW hζ]

/-- The record driver and the counterflow path have the same boundary chart. -/
theorem relBdry_record_eq : relBdry (rdrv (cfRec s W ζ ω)) s = relBdry (rp (W · ω)) s := by
  have h : relMap (rdrv (cfRec s W ζ ω)) s = relMap (rp (W · ω)) s :=
    GaugeE.record_relMap_eq s hW0 hW.continuousOn (by rw [hζ]; exact ENNReal.coe_lt_top)
  unfold relBdry relDomain
  rw [invHull_record_eq s hW0 hW hζ, h]

end Record

section Sample

variable {Ω : Type*} (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω)
  {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace (W · ω) ⊤ α)
  (hW : Continuous (W · ω)) (hW0 : W 0 ω = 0) (hζ : ζ ω = ⊤)
  {s : ℝ≥0} (hs : 0 < s) {x : ℝ} (hx : 0 ≤ x) (harc : ∀ u ∈ Icc 0 s, x * ‖α u‖ < 1)
  {w : ℝ≥0 → ℝ} (hwc : Continuous w) (hw0 : w 0 = 0) {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace w ⊤ γ)

include hα hW hW0 hζ hs hx harc hwc hw0 hγ

/-- **The canonical driver at a root `x` reads the explored curve**: before the root-`x` contact, `x + γ t` is safe
and the canonical trace at the root-`x` clock of `t` is `relBdry (x + γ t) − relBdry x`. -/
theorem canonicalX_eq_relBdry {Wc : ℝ≥0 → ℝ} (hWc : Continuous Wc) (hWc0 : Wc 0 = 0) {ζc : ℝ≥0∞}
    {ηc : ℝ≥0 → ℂ} (hη : IsGeneratingTrace Wc ζc ηc)
    (hK : ∀ t : ℝ≥0, (t : ℝ≥0∞) < firstContactTime (fun t => sphereInv (((x : ℂ) + γ t : ℂ) : OnePoint ℂ))
        ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s) →
      fwdHull (fun r : ℝ => Wc r.toNNReal)
          (RootH29.forwardCapacity x s t (cfRec s W ζ ω, recOf (t : ℝ≥0∞) (w, ⊤))) =
        (fun z : ℂ => z + ((-GW2Bf.relBase x s (cfRec s W ζ ω, recOf (t : ℝ≥0∞) (w, ⊤)) : ℝ) : ℂ)) ''
          RootH29.forwardHull x s t (cfRec s W ζ ω, recOf (t : ℝ≥0∞) (w, ⊤)))
    (hlife : ∀ t : ℝ≥0, (t : ℝ≥0∞) < firstContactTime (fun t => sphereInv (((x : ℂ) + γ t : ℂ) : OnePoint ℂ))
        ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s) →
      (((RootH29.forwardCapacity x s t (cfRec s W ζ ω, recOf (t : ℝ≥0∞) (w, ⊤))).toNNReal : ℝ≥0) : ℝ≥0∞) < ζc)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < firstContactTime (fun t => sphereInv (((x : ℂ) + γ t : ℂ) : OnePoint ℂ))
      ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s)) :
    (x : ℂ) + γ t ∈ relSafe (rdrv (cfRec s W ζ ω)) s ∧
      ηc (RootH29.forwardCapacity x s t (cfRec s W ζ ω, recOf (t : ℝ≥0∞) (w, ⊤))).toNNReal =
        relBdry (rdrv (cfRec s W ζ ω)) s ((x : ℂ) + γ t) - relBdry (rdrv (cfRec s W ζ ω)) s x := by
  set Tc := firstContactTime (fun t => sphereInv (((x : ℂ) + γ t : ℂ) : OnePoint ℂ))
    ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s) with hTc
  set e : (ℝ≥0 → ℝ) × ℝ≥0∞ := (w, ⊤) with hedef
  have he : IsRegularDriver e := Gm.isRegularDriver_top hwc hw0
  set U := rdrv (cfRec s W ζ ω) with hUdef
  obtain ⟨v, htv, hvT⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
  have htv' : t < v := ENNReal.coe_lt_coe.1 htv
  have hv' : (v : ℝ≥0∞) < min Tc e.2 := by rw [hedef, min_top_right]; exact hvT
  set p := (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e) with hp
  set a := fun t => RootH29.forwardCapacity x s t p with hadef
  have hpreC : ∀ {q : ℝ≥0}, q ≤ v →
      RootH29.forwardCapacity x s q (cfRec s W ζ ω, recOf (q : ℝ≥0∞) e) = a q := fun hq =>
    forwardCapacity_prefix_eq' he _ ENNReal.coe_lt_top hq le_rfl
  have hpreH : ∀ {q : ℝ≥0}, q ≤ v →
      RootH29.forwardHull x s q (cfRec s W ζ ω, recOf (q : ℝ≥0∞) e) = RootH29.forwardHull x s q p := fun hq =>
    forwardHull_prefix_eq he _ ENNReal.coe_lt_top hq le_rfl
  have hR : ∀ q ∈ Icc 0 v, fwdHull (fun r : ℝ => Wc r.toNNReal) (RootH29.forwardCapacity x s q p) =
      (fun z : ℂ => z + ((-GW2Bf.relBase x s p : ℝ) : ℂ)) '' RootH29.forwardHull x s q p := by
    intro q hq
    have h := hK q ((ENNReal.coe_le_coe.2 hq.2).trans_lt hvT)
    rw [hpreC hq.2, hpreH hq.2] at h
    exact h
  have hgen := GW2Bf.isGeneratingTrace_capacityTip_of_hull W ζ ω hα hW hW0 hζ hs hx harc he hγ hv' hR
  obtain ⟨-, -, h0', hm', hc', -⟩ := RootI30.exists_reader_chain W ζ ω hα hW hW0 hζ hs hx harc he hγ hv'
  have h0 : a 0 = 0 := h0'
  have hm : StrictMonoOn a (Icc 0 v) := hm'
  have hc : ContinuousOn a (Icc 0 v) := hc'
  have hset : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (v : ℝ≥0∞)} = Icc 0 v := by
    ext t
    simp only [mem_ofPred_eq, ENNReal.coe_le_coe, mem_Icc, zero_le, true_and]
  have ha : IsClockOn a (v : ℝ≥0∞) := ⟨h0, hset ▸ hm, hset ▸ hc, fun h => (ENNReal.coe_ne_top h).elim⟩
  have hat0 : 0 ≤ a t := by
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with h | h
    · rw [← h, h0]
    · exact le_of_lt (lt_of_eq_of_lt h0.symm (hm ⟨le_rfl, zero_le⟩ ⟨zero_le, htv'.le⟩ h))
  have hatv : a t < a v := hm ⟨zero_le, htv'.le⟩ ⟨zero_le, le_rfl⟩ htv'
  have hu : (((a t).toNNReal : ℝ≥0) : ℝ≥0∞) < ENNReal.ofReal (a v) := by
    rw [ENNReal.coe_lt_ofReal, Real.coe_toNNReal _ hat0]; exact hatv
  have htrace := LP.traceAt_eq_of_isGeneratingTrace hgen hWc.continuousOn hWc0 hu
  have hlt : (((a t).toNNReal : ℝ≥0) : ℝ≥0∞) < ζc := by
    have := hlife t ht
    rwa [hpreC htv'.le] at this
  have htrace' := LP.traceAt_eq_of_isGeneratingTrace hη hWc.continuousOn hWc0 hlt
  have htip : RootI30.capacityTipRead x s v (a t).toNNReal p = relBdry U s ((x : ℂ) + γ t) - relBdry U s x := by
    change RootH29.rootTipRead x s (invClock a (v : ℝ≥0∞) (a t).toNNReal) p = _
    rw [ha.invClock_apply (ENNReal.coe_le_coe.2 htv'.le)]
    exact RootH29.rootTipRead_eq W ζ ω hα hW hW0 hζ hx harc he hγ hv' htv'.le
  refine ⟨RootH29.trace_mem_record_relSafe W ζ ω hα hW hW0 hζ hx harc he hγ hv' htv'.le, ?_⟩
  rw [hpreC htv'.le, ← htrace', htrace, htip]

end Sample

end InteractingSLE.Theorem14.GW2Bh
