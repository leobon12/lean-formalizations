/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2TpGauge
import InteractingSLE.Spec.Supplement.GW2RzCap
import InteractingSLE.Spec.Supplement.GW2RzBack
import InteractingSLE.Spec.Dimension.TraceBridge

/-!
# The launch gauge at every root, part 3: the read-back along EVERY root-`x` relative coordinate process

Packet PROVE-GW2-RELDET (round 27). ROOTX's root-`x` read-back (`GW2Rz.physicalTraceX_of_chain`,
`GW2Rz.readback_of_local`) is stated for drivers equal to its re-centred chain driver. The cap-gauge hypothesis of
ROOTX's capped families (`GW2Rv.exists_versionsXA_of_capGauge_strict`) quantifies over EVERY root-`x` coordinate
process (`GW2Rz.CoordX`). Here:

* **`readbackX_of_hulls`** (one sample): a relative driver continuous before its life, from `0`, whose hull at every
  root-`x` clock value before the root-`x` contact is the re-centred relative hull, reads back `x + γ t` at the clock
  of `t` (freeze the driver at the clock of a later good horizon; the frozen driver is a chain driver of that horizon,
  by the prefix identities of the record readers and `fwdHull_eq_of_eqOn`);
* **`ae_readbackX`**: along every `CoordX`, almost surely on the good records `goodX x s`: the root-`x` clock is `0`
  at `0`, strictly increasing and continuous before the contact, reads `x + γ` back, covers every relative time
  before the life, and the read-back is continuous before the life.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

namespace InteractingSLE.Theorem14.GW2Rd

open Exist Staged StagedLaw Restart Supp8.GB6 Supp8.GB6.CoordB Supp8.GB6.ReadD GW2TipSystem GW2Rz

section Sample

variable {Ω : Type*} (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω)
  {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace (W · ω) ⊤ α)
  (hW : Continuous (W · ω)) (hW0 : W 0 ω = 0) (hζ : ζ ω = ⊤)
  {s : ℝ≥0} (hs : 0 < s) {x : ℝ} (hx : 0 ≤ x) (harc : ∀ u ∈ Icc 0 s, x * ‖α u‖ < 1)
  {w : ℝ≥0 → Ω → ℝ} (hwc : Continuous (w · ω)) (hw0 : w 0 ω = 0) {γ : ℝ≥0 → ℂ}
  (hγ : IsGeneratingTrace (w · ω) ⊤ γ)
  (hΨ : Supp8.Q3Rel.IsRetainedChartOff (Supp8.Q3Rel.invHull (rdrv (cfRec s W ζ ω)) s)
    (relMap (rdrv (cfRec s W ζ ω)) s) (relInv (rdrv (cfRec s W ζ ω)) s)
    (Supp8.Q3Rel.relLog (rdrv (cfRec s W ζ ω)) s) (Supp8.Q3Rel.relBad (rdrv (cfRec s W ζ ω)) s))

include hα hW hW0 hζ hs hx harc hwc hw0 hγ hΨ in
/-- **The root-`x` read-back for any relative driver with the re-centred hulls.** -/
theorem readbackX_of_hulls {D : ℝ≥0 → ℝ} {L : ℝ≥0∞} (hDc : ContinuousOn D {u | (u : ℝ≥0∞) < L})
    (hD0 : D 0 = 0)
    (hhull : ∀ t : ℝ≥0, (t : ℝ≥0∞) < firstContactTime (fun t => sphereInv (((x : ℂ) + γ t : ℂ) : OnePoint ℂ))
        ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s) →
      0 ≤ clockX x s W ζ w t ω ∧ ENNReal.ofReal (clockX x s W ζ w t ω) < L ∧
        fwdHull (fun r : ℝ => D r.toNNReal) (clockX x s W ζ w t ω) = hullX x s W ζ w t ω)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < firstContactTime (fun t => sphereInv (((x : ℂ) + γ t : ℂ) : OnePoint ℂ))
        ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s)) :
    physicalTraceX x s (clockX x s W ζ w t ω).toNNReal (cfRec s W ζ ω, D) = (x : ℂ) + γ t := by
  set Tc := firstContactTime (fun t => sphereInv (((x : ℂ) + γ t : ℂ) : OnePoint ℂ))
    ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s) with hTc
  set e : (ℝ≥0 → ℝ) × ℝ≥0∞ := ((w · ω), ⊤) with hedef
  have he : IsRegularDriver e := Gm.isRegularDriver_top hwc hw0
  -- two later good horizons
  obtain ⟨v, htv, hvT⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
  obtain ⟨v₂, hvv₂, hv₂T⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hvT
  have htv' : t < v := ENNReal.coe_lt_coe.1 htv
  have hvv₂' : v < v₂ := ENNReal.coe_lt_coe.1 hvv₂
  have hv0 : 0 < v := zero_le.trans_lt htv'
  -- the clock along the sample
  obtain ⟨-, hm, -⟩ := clock_props W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ
  have hclk : ∀ q : ℝ≥0, clockX x s W ζ w q ω =
      RootH29.forwardCapacity x s q (cfRec s W ζ ω, recOf (q : ℝ≥0∞) ((w · ω), ⊤)) := fun q => rfl
  have hpreC : ∀ {q v' : ℝ≥0}, q ≤ v' → (v' : ℝ≥0∞) < ⊤ →
      RootH29.forwardCapacity x s q (cfRec s W ζ ω, recOf (q : ℝ≥0∞) e) =
        RootH29.forwardCapacity x s q (cfRec s W ζ ω, recOf (v' : ℝ≥0∞) e) := fun hq hv' =>
    forwardCapacity_prefix_eq' he _ hv' hq le_rfl
  have hpreH : ∀ {q v' : ℝ≥0}, q ≤ v' → (v' : ℝ≥0∞) < ⊤ →
      RootH29.forwardHull x s q (cfRec s W ζ ω, recOf (q : ℝ≥0∞) e) =
        RootH29.forwardHull x s q (cfRec s W ζ ω, recOf (v' : ℝ≥0∞) e) := fun hq hv' =>
    forwardHull_prefix_eq he _ hv' hq le_rfl
  -- the frozen driver
  set c₂ : ℝ≥0 := (clockX x s W ζ w v₂ ω).toNNReal with hc₂
  have hc₂L : (c₂ : ℝ≥0∞) < L := (hhull v₂ hv₂T).2.1
  have hc₂eq : (c₂ : ℝ) = clockX x s W ζ w v₂ ω := Real.coe_toNNReal _ (hhull v₂ hv₂T).1
  set R : ℝ≥0 → ℝ := fun u => D (min u c₂) with hRdef
  have hRc : Continuous R :=
    hDc.comp_continuous (continuous_id.min continuous_const) fun u =>
      (ENNReal.coe_le_coe.2 (min_le_right u c₂)).trans_lt hc₂L
  have hR0 : R 0 = 0 := by simp only [hRdef, zero_min, hD0]
  have hRD : ∀ u ≤ c₂, R u = D u := fun u hu => by simp only [hRdef, min_eq_left hu]
  -- the clocks below `v` are strictly below the frozen horizon
  have hlt : ∀ q : ℝ≥0, q ≤ v → clockX x s W ζ w q ω < c₂ := by
    intro q hq
    have hqT : (q : ℝ≥0∞) < Tc := (ENNReal.coe_le_coe.2 hq).trans_lt hvT
    rw [hc₂eq]
    exact hm hqT hv₂T (hq.trans_lt hvv₂')
  -- the chain identity at the horizon `v`
  have hR : ∀ q ∈ Icc 0 v, fwdHull (fun r : ℝ => R r.toNNReal)
      (RootH29.forwardCapacity x s q (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e)) =
      (fun z : ℂ => z + ((-GW2Bf.relBase x s (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e) : ℝ) : ℂ)) ''
        RootH29.forwardHull x s q (cfRec s W ζ ω, recOf (v : ℝ≥0∞) e) := by
    intro q hq
    have hqT : (q : ℝ≥0∞) < Tc := (ENNReal.coe_le_coe.2 hq.2).trans_lt hvT
    rw [← hpreC hq.2 ENNReal.coe_lt_top, ← hpreH hq.2 ENNReal.coe_lt_top]
    have h0 := (hhull q hqT).1
    have hD : fwdHull (fun r : ℝ => R r.toNNReal) (clockX x s W ζ w q ω) =
        fwdHull (fun r : ℝ => D r.toNNReal) (clockX x s W ζ w q ω) := by
      refine fwdHull_eq_of_eqOn h0 (show clockX x s W ζ w q ω < (c₂ : ℝ) from hlt q hq.2) fun r hr => ?_
      exact hRD _ (Real.toNNReal_le_iff_le_coe.2 hr.2)
    rw [← hclk, hD, (hhull q hqT).2.2]
    rfl
  have hread := physicalTraceX_of_chain W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hΨ hv0 hvT hRc hR0 hR htv'
  rw [← hpreC htv'.le ENNReal.coe_lt_top, ← hclk] at hread
  rw [← hread]
  refine physicalTraceX_congr x s _ _ fun u hu => (hRD u ?_).symm
  refine hu.trans ?_
  rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ (hhull t ht).1]
  exact (hlt t htv'.le).le

end Sample

/-! ### Along every root-`x` coordinate process -/

section Ae

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κc θc : ℝ} {bc : ℝ → ℝ} {Jc : Finset ℝ} {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
  {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {α : Ω → ℝ≥0 → ℂ} {w : ℝ≥0 → Ω → ℝ} {γ : Ω → ℝ≥0 → ℂ}
  {D : ℝ≥0 → Ω → ℝ} {L : Ω → ℝ≥0∞}

/-- **The root-`x` read-back along every root-`x` coordinate process**, almost surely on the good records. -/
theorem ae_readbackX (hF : IsFlowLineDriver κc bc Jc θc P h W' ζ')
    (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (W' · ω) (ζ' ω) (α ω))
    (hNR : ∀ᵐ ω ∂P, ∀ α' : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W' t ω) (ζ' ω) α' →
      ∀ v : ℝ≥0, 0 < v → (v : ℝ≥0∞) < ζ' ω → α' v ≠ 0)
    (hcf : ∀ᵐ ω ∂P, ζ' ω = ⊤ ∧ Continuous (W' · ω) ∧ W' 0 ω = 0)
    (hwc : ∀ ω, Continuous (w · ω)) (hw0 : ∀ ω, w 0 ω = 0)
    (hγ : ∀ᵐ ω ∂P, IsGeneratingTrace (w · ω) ⊤ (γ ω))
    {s : ℝ≥0} (hs : 0 < s) {x : ℝ} (hx : 0 ≤ x) (hC : CoordX x s P W' ζ' w γ α D L) :
    ∀ᵐ ω ∂P, cfRec s W' ζ' ω ∈ goodX x s →
      clockX x s W' ζ' w 0 ω = 0 ∧
      StrictMonoOn (fun t => clockX x s W' ζ' w t ω) {t | (t : ℝ≥0∞) < contactX x s γ α ω} ∧
      ContinuousOn (fun t => clockX x s W' ζ' w t ω) {t | (t : ℝ≥0∞) < contactX x s γ α ω} ∧
      (∀ t : ℝ≥0, (t : ℝ≥0∞) < contactX x s γ α ω →
        0 ≤ clockX x s W' ζ' w t ω ∧ ENNReal.ofReal (clockX x s W' ζ' w t ω) < L ω) ∧
      (∀ t : ℝ≥0, (t : ℝ≥0∞) < contactX x s γ α ω →
        physicalTraceX x s (clockX x s W' ζ' w t ω).toNNReal (cfRec s W' ζ' ω, fun u => D u ω) =
          (x : ℂ) + γ ω t) ∧
      (∀ u : ℝ≥0, (u : ℝ≥0∞) < L ω → ∃ t : ℝ≥0, (t : ℝ≥0∞) < contactX x s γ α ω ∧
        clockX x s W' ζ' w t ω = u) ∧
      ContinuousOn (fun u => physicalTraceX x s u (cfRec s W' ζ' ω, fun v => D v ω)) {u | (u : ℝ≥0∞) < L ω} := by
  filter_upwards [hα, hcf, hγ, ae_gb6RecGood hF hα s, ae_retainedChart_record_nr hF hα hNR s, hC.relative]
    with ω hαω hcfω hγω hgood hΨ hrel hm
  obtain ⟨hζ, hWc, hW0⟩ := hcfω
  have hgb6 : cfRec s W' ζ' ω ∈ gb6TS s := hm.1
  obtain ⟨hs', hsH⟩ := (mem_gb6TS_iff hgood).2 hgb6
  have hαt : IsGeneratingTrace (W' · ω) ⊤ (α ω) := by rw [← hζ]; exact hαω
  have hAe : ∀ v ≤ s, recordTrace v (cfRec s W' ζ' ω) = α ω v := fun v hv =>
    GaugeE.recordTrace_eq (Wα := W') (ζα := ζ') s hW0 (by rw [hζ]; exact hWc.continuousOn)
      (by rw [hζ]; exact hαt) (by rw [hζ]; exact ENNReal.coe_lt_top) hv
  have hαc : Continuous (α ω) :=
    continuousOn_univ.1 (hαt.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  have hA : ContinuousOn (fun v => recordTrace v (cfRec s W' ζ' ω)) (Iic s) :=
    hαc.continuousOn.congr fun v hv => hAe v hv
  have harc : ∀ u ∈ Icc 0 s, x * ‖α ω u‖ < 1 := by
    intro u hu
    have h1 := (mem_arcSet_iff hA).1 hm.2 u hu
    rwa [hAe u hu.2] at h1
  have hΨ' := (hΨ hs' hsH).1
  obtain ⟨hcov, hhull⟩ := hrel hm
  obtain ⟨h0, hmono, hcont⟩ := clock_props W' ζ' ω hαt hWc hW0 hζ hs hx harc (hwc ω) (hw0 ω) hγω
  have hread : ∀ t : ℝ≥0, (t : ℝ≥0∞) < contactX x s γ α ω →
      physicalTraceX x s (clockX x s W' ζ' w t ω).toNNReal (cfRec s W' ζ' ω, fun u => D u ω) =
        (x : ℂ) + γ ω t := fun t ht =>
    readbackX_of_hulls W' ζ' ω hαt hWc hW0 hζ hs hx harc (hwc ω) (hw0 ω) hγω hΨ' (hC.continuous ω) (hC.zero ω)
      hhull ht
  have hback : ∀ u : ℝ≥0, (u : ℝ≥0∞) < L ω → ∃ t : ℝ≥0, (t : ℝ≥0∞) < contactX x s γ α ω ∧
      clockX x s W' ζ' w t ω = u := by
    intro u hu
    obtain ⟨T, hT, huT⟩ := hcov u hu
    obtain ⟨t, ht, hat⟩ := GaugeE.exists_clock_eq (a := fun t => clockX x s W' ζ' w t ω)
      (hcont.mono fun q hq => (ENNReal.coe_le_coe.2 hq.2).trans_lt hT) h0 huT.le
    exact ⟨t, (ENNReal.coe_le_coe.2 ht.2).trans_lt hT, hat⟩
  have hγc : Continuous (γ ω) :=
    continuousOn_univ.1 (hγω.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  have hXc := GaugeE.continuousOn_liveReadback (X := fun u => physicalTraceX x s u (cfRec s W' ζ' ω, fun v => D v ω))
    h0 hmono hcont hcov (continuous_const.add hγc) hread
  exact ⟨h0, hmono, hcont, fun t ht => ⟨(hhull t ht).1, (hhull t ht).2.1⟩, hread, hback, hXc⟩

end Ae

end InteractingSLE.Theorem14.GW2Rd
