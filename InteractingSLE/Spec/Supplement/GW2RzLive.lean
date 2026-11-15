/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RzBack
import InteractingSLE.Spec.Supplement.GW2RdGauge

/-!
# GW2 at a root `x`: relative coordinates with a live readout (decision D8, layer 4c)

Packet PROVE-GW2-ROOTX, round 3. GB6's versions are the relative coordinates frozen at the level stops of a causal
live readout (`HullId.HasLiveReadout`). At a root `x` the readout is GB6's separation readout through the re-centred
chart (`GW2Rz.separationReadX`); its physical readback is `x + γ` before the root-`x` first contact
(`GW2Rz.physicalTraceX_of_chain`). Here:

* `arcSet x s` (the protected root arc `x‖α‖ < 1` on `[0, s]`, read from the record through rational times),
  `measurableSet_arcSet`, **`mem_arcSet_iff`** (on a record with a continuous trace it is the arc bound);
  `goodX x s = gb6TS s ∩ arcSet x s`;
* on one sample: `contact_pos` (the root is off the retained prefix), **`clock_props`** (the root-`x` clock is `0` at
  `0`, strictly increasing and continuous before contact), **`readback_of_local`** (a driver equal to a re-centred
  chain driver of a later good horizon reads back `x + γ t` at the clock of `t`), **`liveReadoutX_of_readback`**
  (GB6's `ae_separationRead_regular_nr` and `hasPhysicalTerminalLimits_nr` with the physical curve `x + γ`);
* `CoordX` (GB6's `SourceC.RelativeDriverCoordinates` at a root `x`, on the good records), `HasLiveReadoutOn`
  (`HullId.HasLiveReadout` with any record event);
* **`exists_coordX_live`**: for a complete counterflow flow-line driver without return and an explored driver with a
  transient generating trace, root-`x` coordinates whose separation readout is live on `goodX x s`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory Complex
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull)

namespace InteractingSLE.Theorem14.GW2Rz

open Exist Staged StagedLaw Restart Supp8.GB6 Supp8.GB6.CoordB Supp8.GB6.ReadD Supp8.GB6.GaugeE
  Supp8.GB6.RelDrv.Version GW2TipSystem

/-! ### The protected root arc read from the record -/

/-- **The protected root arc read from the record**: a uniform margin `x‖α‖ ≤ 1 − 1/(n+1)` for the record's trace at
the rational times of `[0, s]` and at `s`. -/
def arcSet (x : ℝ) (s : ℝ≥0) : Set RecData :=
  {r | ∃ n : ℕ, (∀ q : ℚ, 0 ≤ q → (q : ℝ) ≤ s → x * ‖recordTrace (q : ℝ).toNNReal r‖ ≤ 1 - 1 / ((n : ℝ) + 1)) ∧
    x * ‖recordTrace s r‖ ≤ 1 - 1 / ((n : ℝ) + 1)}

theorem measurableSet_arcSet (x : ℝ) (s : ℝ≥0) : MeasurableSet (arcSet x s) := by
  have hf : ∀ v : ℝ≥0, Measurable fun r : RecData => x * ‖recordTrace v r‖ := fun v =>
    ((measurable_recordTrace v).norm).const_mul x
  have e : arcSet x s = ⋃ n : ℕ, ((⋂ q : ℚ, {r : RecData | 0 ≤ q → (q : ℝ) ≤ s →
      x * ‖recordTrace (q : ℝ).toNNReal r‖ ≤ 1 - 1 / ((n : ℝ) + 1)}) ∩
      {r | x * ‖recordTrace s r‖ ≤ 1 - 1 / ((n : ℝ) + 1)}) := by
    ext r
    simp only [arcSet, mem_ofPred_eq, mem_iUnion, mem_inter_iff, mem_iInter]
  rw [e]
  refine MeasurableSet.iUnion fun n => (MeasurableSet.iInter fun q => ?_).inter
    (measurableSet_le (hf s) measurable_const)
  by_cases hq : 0 ≤ q ∧ (q : ℝ) ≤ s
  · have e' : {r : RecData | 0 ≤ q → (q : ℝ) ≤ s →
        x * ‖recordTrace (q : ℝ).toNNReal r‖ ≤ 1 - 1 / ((n : ℝ) + 1)} =
        {r | x * ‖recordTrace (q : ℝ).toNNReal r‖ ≤ 1 - 1 / ((n : ℝ) + 1)} := by
      ext r
      simp only [mem_ofPred_eq, hq.1, hq.2, forall_const]
    rw [e']
    exact measurableSet_le (hf _) measurable_const
  · have e' : {r : RecData | 0 ≤ q → (q : ℝ) ≤ s →
        x * ‖recordTrace (q : ℝ).toNNReal r‖ ≤ 1 - 1 / ((n : ℝ) + 1)} = univ := by
      ext r
      simp only [mem_ofPred_eq, mem_univ, iff_true]
      intro h1 h2
      exact absurd ⟨h1, h2⟩ hq
    rw [e']
    exact MeasurableSet.univ

/-- **On a record with a continuous trace, the record arc is the protected root arc.** -/
theorem mem_arcSet_iff {x : ℝ} {s : ℝ≥0} {r : RecData} (hA : ContinuousOn (fun v => recordTrace v r) (Iic s)) :
    r ∈ arcSet x s ↔ ∀ u ∈ Icc 0 s, x * ‖recordTrace u r‖ < 1 := by
  have hf : ContinuousOn (fun v => x * ‖recordTrace v r‖) (Icc 0 s) :=
    continuousOn_const.mul (hA.norm.mono fun v hv => hv.2)
  constructor
  · rintro ⟨n, hq, hs⟩ u hu
    have hc : x * ‖recordTrace u r‖ ≤ 1 - 1 / ((n : ℝ) + 1) := by
      rcases eq_or_lt_of_le hu.2 with h | h
      · rw [h]; exact hs
      · -- rationals in `(u, s)` approach `u`
        have hseq : ∀ k : ℕ, ∃ q : ℚ, (u : ℝ) < q ∧ (q : ℝ) < min (s : ℝ) ((u : ℝ) + 1 / ((k : ℝ) + 1)) :=
          fun k => exists_rat_btwn (lt_min (NNReal.coe_lt_coe.2 h) (by
            have : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
            linarith))
        choose q hq1 hq2 using hseq
        have hq0 : ∀ k, 0 ≤ q k := fun k => by
          have := u.coe_nonneg.trans (hq1 k).le
          exact_mod_cast this
        have hqs : ∀ k, (q k : ℝ) ≤ s := fun k => ((hq2 k).trans_le (min_le_left _ _)).le
        have hlim : Tendsto (fun k => ((q k : ℝ)).toNNReal) atTop (𝓝 u) := by
          have h1 : Tendsto (fun k => (q k : ℝ)) atTop (𝓝 (u : ℝ)) := by
            refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun k => (hq1 k).le)
              (fun k => ((hq2 k).trans_le (min_le_right _ _)).le)
            have h2 : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
              tendsto_one_div_add_atTop_nhds_zero_nat
            simpa only [add_zero] using tendsto_const_nhds.add h2
          have h3 := (continuous_real_toNNReal.tendsto _).comp h1
          simpa only [Function.comp_def, Real.toNNReal_coe] using h3
        have hmem : ∀ k, ((q k : ℝ)).toNNReal ∈ Icc 0 s := fun k =>
          ⟨zero_le, Real.toNNReal_le_iff_le_coe.2 (hqs k)⟩
        have hcw : ContinuousWithinAt (fun v => x * ‖recordTrace v r‖) (Icc 0 s) u := hf u hu
        have hl := hcw.tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall hmem⟩)
        exact le_of_tendsto hl (Eventually.of_forall fun k => hq (q k) (hq0 k) (hqs k))
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  · intro h
    obtain ⟨u₀, hu₀, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 (zero_le : (0 : ℝ≥0) ≤ s)) hf
    have hM := h u₀ hu₀
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hM)
    have hle : ∀ u ∈ Icc 0 s, x * ‖recordTrace u r‖ ≤ 1 - 1 / ((n : ℝ) + 1) := fun u hu => by
      have := hmax hu
      simp only [mem_ofPred_eq] at this
      linarith
    exact ⟨n, fun q hq0 hqs => hle _ ⟨zero_le, Real.toNNReal_le_iff_le_coe.2 hqs⟩, hle s ⟨zero_le, le_rfl⟩⟩

/-- **The good records at a root `x`**: GB6's record event and the protected root arc. -/
def goodX (x : ℝ) (s : ℝ≥0) : Set RecData := gb6TS s ∩ arcSet x s

theorem measurableSet_goodX (x : ℝ) (s : ℝ≥0) : MeasurableSet (goodX x s) :=
  (measurableSet_gb6TS s).inter (measurableSet_arcSet x s)

/-! ### The root-`x` clock and the readback on one sample -/

section Sample

variable {Ω : Type*} (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (ω : Ω)
  {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace (W · ω) ⊤ α)
  (hW : Continuous (W · ω)) (hW0 : W 0 ω = 0) (hζ : ζ ω = ⊤)
  {s : ℝ≥0} (hs : 0 < s) {x : ℝ} (hx : 0 ≤ x) (harc : ∀ u ∈ Icc 0 s, x * ‖α u‖ < 1)
  {w : ℝ≥0 → ℝ} (hwc : Continuous w) (hw0 : w 0 = 0) {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace w ⊤ γ)

include hα hx harc hγ in
/-- **The root-`x` first contact is positive**: the root itself is not on the retained prefix in the inversion. -/
theorem contact_pos :
    0 < firstContactTime (fun t => sphereInv (((x : ℂ) + γ t : ℂ) : OnePoint ℂ))
      ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s) := by
  have hγc : Continuous γ := continuousOn_univ.1 (hγ.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  have hαc : Continuous α := continuousOn_univ.1 (hα.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  have hAcpt : IsCompact ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s) := by
    have hcompact : IsCompact (α '' Icc 0 s) := isCompact_Icc.image hαc
    simpa only [image_image] using hcompact.image OnePoint.continuous_coe
  have hηc : Continuous fun t => sphereInv (((x : ℂ) + γ t : ℂ) : OnePoint ℂ) :=
    continuous_sphereInv.comp (OnePoint.continuous_coe.comp (continuous_const.add hγc))
  refine pos_iff_ne_zero.2 fun h0 => ?_
  have h0' : firstContactTime (fun t => sphereInv (((x : ℂ) + γ t : ℂ) : OnePoint ℂ))
      ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s) = ((0 : ℝ≥0) : ℝ≥0∞) := by rw [h0, ENNReal.coe_zero]
  obtain ⟨v, hv, hcontact⟩ := firstContactTime_mem hηc hAcpt.isClosed h0'
  have hz := (SourceC.sphereInv_eq_iff _ _).1 hcontact.symm
  rw [hγ.1, add_zero] at hz
  have hn : ‖(x : ℂ) * α v‖ = 1 := by
    rw [eq_neg_of_add_eq_zero_left hz, norm_neg, norm_one]
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hx] at hn
  exact (harc v hv).ne hn

include hα hW hW0 hζ hs hx harc hwc hw0 hγ in
/-- **The root-`x` clock on one sample**: ROOT2's capacity reader with the horizon at the time is `0` at `0`, strictly
increasing and continuous before the root-`x` first contact. -/
theorem clock_props :
    RootH29.forwardCapacity x s 0 (cfRec s W ζ ω, recOf ((0 : ℝ≥0) : ℝ≥0∞) (w, ⊤)) = 0 ∧
    StrictMonoOn (fun t => RootH29.forwardCapacity x s t (cfRec s W ζ ω, recOf (t : ℝ≥0∞) (w, ⊤)))
      {t | (t : ℝ≥0∞) < firstContactTime (fun t => sphereInv (((x : ℂ) + γ t : ℂ) : OnePoint ℂ))
        ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s)} ∧
    ContinuousOn (fun t => RootH29.forwardCapacity x s t (cfRec s W ζ ω, recOf (t : ℝ≥0∞) (w, ⊤)))
      {t | (t : ℝ≥0∞) < firstContactTime (fun t => sphereInv (((x : ℂ) + γ t : ℂ) : OnePoint ℂ))
        ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s)} := by
  set Tc := firstContactTime (fun t => sphereInv (((x : ℂ) + γ t : ℂ) : OnePoint ℂ))
    ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s) with hTc
  have he := Gm.isRegularDriver_top hwc hw0
  have hmin : ∀ v : ℝ≥0, (v : ℝ≥0∞) < Tc → (v : ℝ≥0∞) < min Tc (w, (⊤ : ℝ≥0∞)).2 := fun v hv => by
    rw [min_top_right]; exact hv
  -- the clock at an earlier time read on a later horizon
  have hpre : ∀ {t v : ℝ≥0}, t ≤ v → RootH29.forwardCapacity x s t (cfRec s W ζ ω, recOf (t : ℝ≥0∞) (w, ⊤)) =
      RootH29.forwardCapacity x s t (cfRec s W ζ ω, recOf (v : ℝ≥0∞) (w, ⊤)) := fun htv =>
    forwardCapacity_prefix_eq' he _ ENNReal.coe_lt_top htv le_rfl
  -- a horizon strictly between `t` and the contact
  have hbtw : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc → ∃ v : ℝ≥0, t < v ∧ (v : ℝ≥0∞) < Tc := fun t ht => by
    obtain ⟨v, h1, h2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
    exact ⟨v, ENNReal.coe_lt_coe.1 h1, h2⟩
  have hTc0 : (0 : ℝ≥0∞) < Tc := contact_pos W ω hα hx harc hγ
  refine ⟨?_, fun t₁ ht₁ t₂ ht₂ h12 => ?_, fun t ht => ?_⟩
  · obtain ⟨v, hv0, hvT⟩ := hbtw 0 (by rw [ENNReal.coe_zero]; exact hTc0)
    obtain ⟨-, -, -, h0, -⟩ := reader_eq_chain W ζ ω hα hW hW0 hζ hs hx harc he hγ (hmin v hvT) hv0
    rw [hpre (zero_le : (0 : ℝ≥0) ≤ v)]
    exact h0
  · obtain ⟨v, hv, hvT⟩ := hbtw t₂ ht₂
    obtain ⟨-, -, -, -, hm, -⟩ := reader_eq_chain W ζ ω hα hW hW0 hζ hs hx harc he hγ (hmin v hvT)
      ((zero_le.trans_lt h12).trans hv)
    show RootH29.forwardCapacity x s t₁ _ < RootH29.forwardCapacity x s t₂ _
    rw [hpre (h12.le.trans hv.le), hpre hv.le]
    exact hm ⟨zero_le, h12.le.trans hv.le⟩ ⟨zero_le, hv.le⟩ h12
  · obtain ⟨v, hv, hvT⟩ := hbtw t ht
    obtain ⟨-, -, -, -, -, hc, -⟩ := reader_eq_chain W ζ ω hα hW hW0 hζ hs hx harc he hγ (hmin v hvT)
      (zero_le.trans_lt hv)
    have hc' : ContinuousOn (fun t => RootH29.forwardCapacity x s t (cfRec s W ζ ω, recOf (t : ℝ≥0∞) (w, ⊤)))
        (Icc 0 v) := hc.congr fun t' ht' => hpre ht'.2
    have hnhds : Icc 0 v ∈ 𝓝 t := by
      have : Icc (0 : ℝ≥0) v = Iic v := by ext; simp only [mem_Icc, zero_le, true_and, mem_Iic]
      rw [this]; exact Iic_mem_nhds hv
    exact (hc'.continuousAt hnhds).continuousWithinAt

include hα hW hW0 hζ hs hx harc hwc hw0 hγ in
/-- **The readback from a local chain**: a driver that equals a re-centred chain driver of a good horizon `v > t`
below the horizon's capacity reads back the physical point `x + γ t` at the root-`x` clock of `t`. -/
theorem readback_of_local
    (hΨ : Supp8.Q3Rel.IsRetainedChartOff (Supp8.Q3Rel.invHull (rdrv (cfRec s W ζ ω)) s)
      (relMap (rdrv (cfRec s W ζ ω)) s) (relInv (rdrv (cfRec s W ζ ω)) s)
      (Supp8.Q3Rel.relLog (rdrv (cfRec s W ζ ω)) s) (Supp8.Q3Rel.relBad (rdrv (cfRec s W ζ ω)) s))
    {D : ℝ≥0 → ℝ} {t : ℝ≥0}
    (hloc : ∃ v : ℝ≥0, t < v ∧ (v : ℝ≥0∞) < firstContactTime (fun t => sphereInv (((x : ℂ) + γ t : ℂ) :
        OnePoint ℂ)) ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s) ∧ ∃ R : ℝ≥0 → ℝ, Continuous R ∧ R 0 = 0 ∧
      (∀ t' ∈ Icc 0 v, fwdHull (fun r : ℝ => R r.toNNReal)
          (RootH29.forwardCapacity x s t' (cfRec s W ζ ω, recOf (v : ℝ≥0∞) (w, ⊤))) =
        (fun z : ℂ => z + ((-GW2Bf.relBase x s (cfRec s W ζ ω, recOf (v : ℝ≥0∞) (w, ⊤)) : ℝ) : ℂ)) ''
          RootH29.forwardHull x s t' (cfRec s W ζ ω, recOf (v : ℝ≥0∞) (w, ⊤))) ∧
      ∀ u : ℝ≥0, (u : ℝ) < RootH29.forwardCapacity x s v (cfRec s W ζ ω, recOf (v : ℝ≥0∞) (w, ⊤)) →
        D u = R u) :
    physicalTraceX x s (RootH29.forwardCapacity x s t (cfRec s W ζ ω, recOf (t : ℝ≥0∞) (w, ⊤))).toNNReal
      (cfRec s W ζ ω, D) = (x : ℂ) + γ t := by
  obtain ⟨v, htv, hvT, R, hRc, hR0, hRhull, hDR⟩ := hloc
  have he := Gm.isRegularDriver_top hwc hw0
  have hv' : (v : ℝ≥0∞) < min (firstContactTime (fun t => sphereInv (((x : ℂ) + γ t : ℂ) : OnePoint ℂ))
      ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s)) (w, (⊤ : ℝ≥0∞)).2 := by
    rw [min_top_right]; exact hvT
  have hv0 : 0 < v := zero_le.trans_lt htv
  obtain ⟨-, -, -, h0, hm, -⟩ := reader_eq_chain W ζ ω hα hW hW0 hζ hs hx harc he hγ hv' hv0
  have hpre : RootH29.forwardCapacity x s t (cfRec s W ζ ω, recOf (t : ℝ≥0∞) (w, ⊤)) =
      RootH29.forwardCapacity x s t (cfRec s W ζ ω, recOf (v : ℝ≥0∞) (w, ⊤)) :=
    forwardCapacity_prefix_eq' he _ ENNReal.coe_lt_top htv.le le_rfl
  have hlt : RootH29.forwardCapacity x s t (cfRec s W ζ ω, recOf (v : ℝ≥0∞) (w, ⊤)) <
      RootH29.forwardCapacity x s v (cfRec s W ζ ω, recOf (v : ℝ≥0∞) (w, ⊤)) :=
    hm ⟨zero_le, htv.le⟩ ⟨zero_le, le_rfl⟩ htv
  have hnn : 0 ≤ RootH29.forwardCapacity x s t (cfRec s W ζ ω, recOf (v : ℝ≥0∞) (w, ⊤)) := by
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with h | h
    · rw [← h]; exact h0.ge
    · exact le_of_lt (lt_of_eq_of_lt h0.symm (hm ⟨le_rfl, zero_le⟩ ⟨zero_le, htv.le⟩ h))
  rw [hpre, physicalTraceX_congr x s _ _ (w' := R) (fun u hu => hDR u ?_)]
  · exact physicalTraceX_of_chain W ζ ω hα hW hW0 hζ hs hx harc hwc hw0 hγ hΨ hv0 hvT hRc hR0 hRhull htv
  · have hu' : (u : ℝ) ≤ RootH29.forwardCapacity x s t (cfRec s W ζ ω, recOf (v : ℝ≥0∞) (w, ⊤)) := by
      have := NNReal.coe_le_coe.2 hu
      rwa [Real.coe_toNNReal _ hnn] at this
    exact hu'.trans_lt hlt

end Sample

/-! ### The live readout on one sample -/

/-- **The root-`x` live readout at one sample** (GB6's `ae_separationRead_regular_nr` and
`hasPhysicalTerminalLimits_nr` with the physical curve `x + γ`): a regular clock, the readback of the physical trace
along the clock and the range of the clock give a separation readout that is continuous and positive before the life
and tends to `0` at a finite life (contact or escape). -/
theorem liveReadoutX_of_readback {x : ℝ} {s : ℝ≥0} (hs : 0 < s) {r : RecData} {D : ℝ≥0 → ℝ} {L : ℝ≥0∞}
    {γ α : ℝ≥0 → ℂ} (hγc : Continuous γ) (hγinf : Tendsto (fun t => ‖γ t‖) atTop atTop)
    (hA : ContinuousOn (fun v => recordTrace v r) (Iic s)) (hAe : ∀ v ≤ s, recordTrace v r = α v)
    (hα0 : α 0 = 0) {a : ℝ≥0 → ℝ}
    (ha0 : a 0 = 0)
    (ham : StrictMonoOn a {t | (t : ℝ≥0∞) < firstContactTime (fun t => sphereInv (((x : ℂ) + γ t : ℂ) :
      OnePoint ℂ)) ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s)})
    (hac : ContinuousOn a {t | (t : ℝ≥0∞) < firstContactTime (fun t => sphereInv (((x : ℂ) + γ t : ℂ) :
      OnePoint ℂ)) ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s)})
    (hrange : ∀ u : ℝ≥0, (u : ℝ≥0∞) < L → ∃ T : ℝ≥0, (T : ℝ≥0∞) < firstContactTime
      (fun t => sphereInv (((x : ℂ) + γ t : ℂ) : OnePoint ℂ)) ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s) ∧
      (u : ℝ) < a T)
    (hbound : ∀ t : ℝ≥0, (t : ℝ≥0∞) < firstContactTime (fun t => sphereInv (((x : ℂ) + γ t : ℂ) :
      OnePoint ℂ)) ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s) → 0 ≤ a t ∧ ENNReal.ofReal (a t) < L)
    (hread : ∀ t : ℝ≥0, (t : ℝ≥0∞) < firstContactTime (fun t => sphereInv (((x : ℂ) + γ t : ℂ) :
      OnePoint ℂ)) ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s) →
      physicalTraceX x s (a t).toNNReal (r, D) = (x : ℂ) + γ t) :
    ContinuousOn (fun t => separationReadX x s t (r, D)) {t | (t : ℝ≥0∞) < L} ∧
      (∀ t : ℝ≥0, (t : ℝ≥0∞) < L → 0 < separationReadX x s t (r, D)) ∧
      ∀ T : ℝ≥0, (T : ℝ≥0∞) = L → Tendsto (fun t => separationReadX x s t (r, D)) (𝓝[<] T) (𝓝 0) := by
  set Tc := firstContactTime (fun t => sphereInv (((x : ℂ) + γ t : ℂ) : OnePoint ℂ))
    ((fun u => (α u : OnePoint ℂ)) '' Icc 0 s) with hTcdef
  have hxγc : Continuous fun t => (x : ℂ) + γ t := continuous_const.add hγc
  have hX := continuousOn_liveReadback (X := fun u => physicalTraceX x s u (r, D)) ha0 ham hac hrange hxγc hread
  -- every live relative time reads a physical time before contact
  have hcap : ∀ u : ℝ≥0, (u : ℝ≥0∞) < L → ∃ t : ℝ≥0, (t : ℝ≥0∞) < Tc ∧ a t = u ∧
      physicalTraceX x s u (r, D) = (x : ℂ) + γ t := by
    intro u hu
    obtain ⟨T, hT, huT⟩ := hrange u hu
    have huT' : (u : ℝ) ≤ a T := huT.le
    obtain ⟨t, ht, hat⟩ := exists_clock_eq (hac.mono fun q hq =>
      (ENNReal.coe_le_coe.2 hq.2).trans_lt hT) ha0 huT'
    have htTc : (t : ℝ≥0∞) < Tc := (ENNReal.coe_le_coe.2 ht.2).trans_lt hT
    refine ⟨t, htTc, hat, ?_⟩
    have hr := hread t htTc
    rw [hat, Real.toNNReal_coe] at hr
    exact hr
  refine ⟨continuousOn_separationReadX x s _ _ hX hA, fun t ht => ?_, fun T hTL => ?_⟩
  · apply separationReadX_pos x s t _ _ (hX.mono (fun u hu => (ENNReal.coe_le_coe.2 hu).trans_lt ht)) hA
    intro u hu v hv
    obtain ⟨q, hq, _, hXu⟩ := hcap u ((ENNReal.coe_le_coe.2 hu).trans_lt ht)
    rw [hXu, hAe v hv]
    intro hzero
    exact notMem_of_lt_firstContactTime hq ⟨v, ⟨zero_le, hv⟩,
      ((SourceC.sphereInv_eq_iff _ _).2 hzero).symm⟩
  · -- the terminal limit: contact or escape
    have hXI : ContinuousOn (fun u => physicalTraceX x s u (r, D)) (Iio T) :=
      hX.mono (fun u hu => by rw [← hTL]; exact ENNReal.coe_lt_coe.2 hu)
    have hbound' : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc → 0 ≤ a t ∧ a t < T := by
      intro t ht
      obtain ⟨hn, hl⟩ := hbound t ht
      refine ⟨hn, ?_⟩
      rw [← hTL] at hl
      simpa only [ENNReal.coe_toReal] using (ENNReal.ofReal_lt_iff_lt_toReal hn ENNReal.coe_ne_top).1 hl
    have hex : ∀ u : ℝ≥0, u < T → ∃ t : ℝ≥0, (t : ℝ≥0∞) < Tc ∧ a t = u ∧
        physicalTraceX x s u (r, D) = (x : ℂ) + γ t := fun u hu => hcap u (by rw [← hTL]; exact ENNReal.coe_lt_coe.2 hu)
    classical
    let c : ℝ≥0 → ℝ≥0 := fun u => if hu : u < T then (hex u hu).choose else 0
    have hcspec : ∀ u : ℝ≥0, u < T → (c u : ℝ≥0∞) < Tc ∧ a (c u) = u ∧
        physicalTraceX x s u (r, D) = (x : ℂ) + γ (c u) := by
      intro u hu
      simpa only [c, hu, ↓reduceDIte] using (hex u hu).choose_spec
    have hc : ∀ u : ℝ≥0, u < T → (c u : ℝ≥0∞) < Tc ∧ a (c u) = u :=
      fun u hu => ⟨(hcspec u hu).1, (hcspec u hu).2.1⟩
    have hu : ∀ᶠ u : ℝ≥0 in 𝓝[<] T, u < T := self_mem_nhdsWithin
    have he : (fun u => (x : ℂ) + γ (c u)) =ᶠ[𝓝[<] T] (fun u => physicalTraceX x s u (r, D)) :=
      hu.mono (fun u hu => (hcspec u hu).2.2.symm)
    rcases eq_top_or_lt_top Tc with htop | hfin
    · have hm : StrictMonoOn a {t | (t : ℝ≥0∞) < ⊤} := by simpa only [htop] using ham
      have hb : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ⊤ → 0 ≤ a t ∧ a t < T := by simpa only [htop] using hbound'
      have hc' : ∀ u : ℝ≥0, u < T → (c u : ℝ≥0∞) < ⊤ ∧ a (c u) = u := by simpa only [htop] using hc
      have hinf := hγinf.comp (tendsto_clockInverse_top hm hb hc')
      have hinfx : Tendsto (fun u => ‖(x : ℂ) + γ (c u)‖) (𝓝[<] T) atTop := by
        refine tendsto_atTop_mono' _ (Eventually.of_forall fun u => ?_) (tendsto_atTop_add_const_right _
          (-‖(x : ℂ)‖) hinf)
        have := norm_sub_norm_le (γ (c u)) (-(x : ℂ))
        simp only [sub_neg_eq_add, norm_neg] at this
        change ‖γ (c u)‖ + -‖(x : ℂ)‖ ≤ ‖(x : ℂ) + γ (c u)‖
        rw [add_comm (x : ℂ)]
        linarith
      exact tendsto_separationReadX_escape x s r D hs hXI hA (by rw [hAe 0 zero_le]; exact hα0)
        (hinfx.congr' (he.mono (fun _ h => congrArg norm h)))
    · let C := Tc.toNNReal
      have hTc : Tc = (C : ℝ≥0∞) := (ENNReal.coe_toNNReal hfin.ne).symm
      have hm : StrictMonoOn a {t | (t : ℝ≥0∞) < (C : ℝ≥0∞)} := by simpa only [hTc] using ham
      have hb : ∀ t : ℝ≥0, (t : ℝ≥0∞) < (C : ℝ≥0∞) → 0 ≤ a t ∧ a t < T := by simpa only [hTc] using hbound'
      have hc' : ∀ u : ℝ≥0, u < T → (c u : ℝ≥0∞) < (C : ℝ≥0∞) ∧ a (c u) = u := by simpa only [hTc] using hc
      have hlim := ((hxγc.tendsto C).comp (tendsto_clockInverse_finite hm hb hc')).congr' he
      have hAcpt : IsCompact ((fun v => (α v : OnePoint ℂ)) '' Icc 0 s) := by
        have hαc : ContinuousOn α (Icc 0 s) := (hA.congr (fun v hv => (hAe v hv).symm)).mono
          (fun v hv => hv.2)
        have hcompact : IsCompact (α '' Icc 0 s) := isCompact_Icc.image_of_continuousOn hαc
        simpa only [image_image] using hcompact.image OnePoint.continuous_coe
      obtain ⟨v, hv, hcontact⟩ := firstContactTime_mem
        (continuous_sphereInv.comp (OnePoint.continuous_coe.comp hxγc)) hAcpt.isClosed hTc
      refine tendsto_separationReadX_contact x s r D hs hXI hA hv.2 hlim ?_
      rw [hAe v hv.2]
      exact (SourceC.sphereInv_eq_iff _ _).1 hcontact.symm


/-! ### Root-`x` relative coordinates and their live readout -/

section Coord

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- **Root-`x` relative driver coordinates** (GB6's `SourceC.RelativeDriverCoordinates` at a root `x`): a measurable
driver from `0`, continuous before a positive measurable life, such that almost surely on the good records
`goodX x s` every relative time before the life is the root-`x` clock of a time before the root-`x` first contact,
and before the contact the clock is below the life and the driver's hull at the clock is the re-centred relative
hull. -/
structure CoordX (x : ℝ) (s : ℝ≥0) (P : Measure Ω) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) (w : ℝ≥0 → Ω → ℝ)
    (γ α : Ω → ℝ≥0 → ℂ) (D : ℝ≥0 → Ω → ℝ) (L : Ω → ℝ≥0∞) : Prop where
  measurable : ∀ t, Measurable (D t)
  life_measurable : Measurable L
  life_pos : ∀ ω, 0 < L ω
  continuous : ∀ ω, ContinuousOn (D · ω) {u | (u : ℝ≥0∞) < L ω}
  zero : ∀ ω, D 0 ω = 0
  adapted : AdaptedBefore (Filtration.const ℝ≥0 mΩ le_rfl) L D
  relative : ∀ᵐ ω ∂P, cfRec s W' ζ' ω ∈ goodX x s →
    (∀ u : ℝ≥0, (u : ℝ≥0∞) < L ω → ∃ t : ℝ≥0, (t : ℝ≥0∞) < contactX x s γ α ω ∧
      (u : ℝ) < clockX x s W' ζ' w t ω) ∧
    ∀ t : ℝ≥0, (t : ℝ≥0∞) < contactX x s γ α ω →
      0 ≤ clockX x s W' ζ' w t ω ∧ ENNReal.ofReal (clockX x s W' ζ' w t ω) < L ω ∧
      fwdHull (fun r : ℝ => D r.toNNReal ω) (clockX x s W' ζ' w t ω) = hullX x s W' ζ' w t ω

/-- **A causal live readout on a set of records** (`HullId.HasLiveReadout` with the record event `S`). -/
def HasLiveReadoutOn (S : Set RecData) (P : Measure Ω) (rec : Ω → RecData) (D : ℝ≥0 → Ω → ℝ)
    (L : Ω → ℝ≥0∞) : Prop :=
  ∃ G : GaugeReadout, (∀ t, Measurable (G t)) ∧ IsCausal G ∧
    ∀ᵐ ω ∂P, rec ω ∈ S →
      ContinuousOn (fun t => G t (rec ω, fun u => D u ω)) {t | (t : ℝ≥0∞) < L ω} ∧
      (∀ t : ℝ≥0, (t : ℝ≥0∞) < L ω → 0 < G t (rec ω, fun u => D u ω)) ∧
      ∀ T : ℝ≥0, (T : ℝ≥0∞) = L ω → Tendsto (fun t => G t (rec ω, fun u => D u ω)) (𝓝[<] T) (𝓝 0)

/-- **Root-`x` relative coordinates with a live readout** (GB6's `SourceC.exists_relative_driver` and
`GW2Rd.hasLiveReadout_nr` at a root `x`): for a counterflow flow-line driver without return, complete almost surely,
and an explored driver, continuous from `0`, with a transient generating trace, there are root-`x` coordinates whose
separation readout through the re-centred chart (`separationReadX`) is live on the good records. -/
theorem exists_coordX_live {P : Measure Ω} [IsProbabilityMeasure P] {κ θ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {α : Ω → ℝ≥0 → ℂ}
    (hF : IsFlowLineDriver κ b J θ P h W' ζ') (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (W' · ω) (ζ' ω) (α ω))
    (hNR : ∀ᵐ ω ∂P, ∀ α' : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W' t ω) (ζ' ω) α' →
      ∀ v : ℝ≥0, 0 < v → (v : ℝ≥0∞) < ζ' ω → α' v ≠ 0)
    (hcf : ∀ᵐ ω ∂P, ζ' ω = ⊤ ∧ Continuous (W' · ω) ∧ W' 0 ω = 0)
    {w : ℝ≥0 → Ω → ℝ} {γ : Ω → ℝ≥0 → ℂ} (hwm : ∀ t, Measurable (w t)) (hwc : ∀ ω, Continuous (w · ω))
    (hw0 : ∀ ω, w 0 ω = 0)
    (hγ : ∀ᵐ ω ∂P, IsGeneratingTrace (w · ω) ⊤ (γ ω) ∧ Tendsto (fun t => ‖γ ω t‖) atTop atTop)
    {s : ℝ≥0} (hs : 0 < s) {x : ℝ} (hx : 0 ≤ x) :
    ∃ (D : ℝ≥0 → Ω → ℝ) (L : Ω → ℝ≥0∞), CoordX x s P W' ζ' w γ α D L ∧
      HasLiveReadoutOn (goodX x s) P (cfRec s W' ζ') D L := by
  classical
  have hrecm : Measurable (cfRec s W' ζ') := (measurable_recOf_cfE hF s).2
  -- the good event
  have hall : ∀ᵐ ω ∂P, (IsGeneratingTrace (w · ω) ⊤ (γ ω) ∧ Tendsto (fun t => ‖γ ω t‖) atTop atTop) ∧
      (ζ' ω = ⊤ ∧ Continuous (W' · ω) ∧ W' 0 ω = 0) ∧ IsGeneratingTrace (W' · ω) (ζ' ω) (α ω) ∧
      ((s : ℝ≥0∞) < ζ' ω → GB6RecGood s W' ζ' α ω) ∧
      ((s : ℝ≥0∞) < ζ' ω → α ω s ∈ H →
        Supp8.Q3Rel.IsRetainedChartOff (Supp8.Q3Rel.invHull (rdrv (cfRec s W' ζ' ω)) s)
          (relMap (rdrv (cfRec s W' ζ' ω)) s) (relInv (rdrv (cfRec s W' ζ' ω)) s)
          (Supp8.Q3Rel.relLog (rdrv (cfRec s W' ζ' ω)) s) (Supp8.Q3Rel.relBad (rdrv (cfRec s W' ζ' ω)) s)) := by
    filter_upwards [hγ, hcf, hα, ae_gb6RecGood hF hα s, GW2Rd.ae_retainedChart_record_nr hF hα hNR s]
      with ω h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, fun hs hsH => (h5 hs hsH).1⟩
  obtain ⟨G, hGm, hGae, hG⟩ := SourceC.exists_measurable_good hall
  -- facts on the good event
  have hfacts : ∀ ω ∈ G, IsGeneratingTrace (W' · ω) ⊤ (α ω) ∧ Continuous (α ω) ∧ Continuous (γ ω) ∧
      (∀ v ≤ s, recordTrace v (cfRec s W' ζ' ω) = α ω v) ∧
      ContinuousOn (fun v => recordTrace v (cfRec s W' ζ' ω)) (Iic s) ∧
      ∀ v, LP.traceAt v (w · ω) = γ ω v := by
    intro ω hω
    obtain ⟨⟨hγω, -⟩, ⟨hζ, hWc, hW0⟩, hαω, -, -⟩ := hG ω hω
    rw [hζ] at hαω
    have hαc : Continuous (α ω) :=
      continuousOn_univ.1 (hαω.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top)
    have hAe : ∀ v ≤ s, recordTrace v (cfRec s W' ζ' ω) = α ω v := fun v hv =>
      recordTrace_eq (Wα := W') (ζα := ζ') s hW0 (by rw [hζ]; exact hWc.continuousOn)
        (by rw [hζ]; exact hαω) (by rw [hζ]; exact ENNReal.coe_lt_top) hv
    refine ⟨hαω, hαc, continuousOn_univ.1 (hγω.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top), hAe,
      hαc.continuousOn.congr fun v hv => hAe v hv, fun v => ?_⟩
    exact LP.traceAt_eq_of_isGeneratingTrace hγω (hwc ω).continuousOn (hw0 ω) ENNReal.coe_lt_top
  -- measurable continuous versions of the two traces
  let Γ : Ω → ℝ≥0 → ℂ := fun ω v => if ω ∈ G then LP.traceAt v (w · ω) else 0
  let A : Ω → ℝ≥0 → ℂ := fun ω v => if ω ∈ G then recordTrace (min v s) (cfRec s W' ζ' ω) else 0
  have hΓc : ∀ ω, Continuous (Γ ω) := fun ω => by
    by_cases hω : ω ∈ G
    · have e : Γ ω = γ ω := funext fun v => by simp only [Γ, hω, ↓reduceIte, (hfacts ω hω).2.2.2.2.2 v]
      rw [e]; exact (hfacts ω hω).2.2.1
    · have e : Γ ω = fun _ => 0 := funext fun v => by simp only [Γ, hω, ↓reduceIte]
      rw [e]; exact continuous_const
  have hΓm : ∀ t, Measurable fun ω => Γ ω t := fun t =>
    Measurable.ite hGm ((LP.measurable_traceAt t).comp (measurable_pi_iff.2 hwm)) measurable_const
  have hAc : ∀ ω, Continuous (A ω) := fun ω => by
    by_cases hω : ω ∈ G
    · have e : A ω = fun v => α ω (min v s) := funext fun v => by
        simp only [A, hω, ↓reduceIte, (hfacts ω hω).2.2.2.1 _ (min_le_right v s)]
      rw [e]; exact (hfacts ω hω).2.1.comp (continuous_id.min continuous_const)
    · have e : A ω = fun _ => 0 := funext fun v => by simp only [A, hω, ↓reduceIte]
      rw [e]; exact continuous_const
  have hAm : ∀ t, Measurable fun ω => A ω t := fun t =>
    Measurable.ite hGm ((measurable_recordTrace _).comp hrecm) measurable_const
  -- the arc event read from the record
  set Arc : Set Ω := cfRec s W' ζ' ⁻¹' arcSet x s with hArcdef
  have hArc : MeasurableSet Arc := hrecm (measurableSet_arcSet x s)
  have harcG : ∀ ω ∈ G, ω ∈ Arc → ∀ u ∈ Icc 0 s, x * ‖α ω u‖ < 1 := by
    intro ω hω hωA u hu
    have h := (mem_arcSet_iff (hfacts ω hω).2.2.2.2.1).1 hωA u hu
    rwa [(hfacts ω hω).2.2.2.1 u hu.2] at h
  have hgood : ∀ᵐ ω ∂P, (IsGeneratingTrace (W' · ω) ⊤ (α ω) ∧ Continuous (W' · ω) ∧ W' 0 ω = 0 ∧
      ζ' ω = ⊤) ∧ IsGeneratingTrace (w · ω) ⊤ (γ ω) ∧ (ω ∈ Arc → ∀ u ∈ Icc 0 s, x * ‖α ω u‖ < 1) ∧
      Γ ω = γ ω ∧ ∀ u ≤ s, A ω u = α ω u := by
    filter_upwards [hGae] with ω hω
    obtain ⟨⟨hγω, -⟩, ⟨hζ, hWc, hW0⟩, -, -, -⟩ := hG ω hω
    refine ⟨⟨(hfacts ω hω).1, hWc, hW0, hζ⟩, hγω, harcG ω hω, funext fun v => ?_, fun u hu => ?_⟩
    · simp only [Γ, hω, ↓reduceIte, (hfacts ω hω).2.2.2.2.2 v]
    · simp only [A, hω, ↓reduceIte, min_eq_left hu, (hfacts ω hω).2.2.2.1 u hu]
  obtain ⟨D, L, hDm, hLm, hDc, hD0, -, hrel⟩ := exists_coordX (P := P) (α := α) (γ := γ) hrecm hwm hwc hw0 hs
    hx hΓc hΓm hAc hAm hArc hgood
  -- the life is positive on the good records
  have hLpos : ∀ᵐ ω ∂P, cfRec s W' ζ' ω ∈ goodX x s → L ω ≠ 0 := by
    filter_upwards [hrel, hGae] with ω hrelω hω hgx
    obtain ⟨-, hK⟩ := hrelω hgx.2
    have hc0 : ((0 : ℝ≥0) : ℝ≥0∞) < contactX x s γ α ω := by
      rw [ENNReal.coe_zero]
      obtain ⟨⟨hγω, -⟩, -⟩ := hG ω hω
      exact contact_pos W' ω (hfacts ω hω).1 hx (harcG ω hω hgx.2) hγω
    exact (pos_of_gt (hK 0 hc0).2.1).ne'
  -- modify off the positive lives
  set L' : Ω → ℝ≥0∞ := fun ω => if L ω = 0 then ⊤ else L ω with hL'def
  set D' : ℝ≥0 → Ω → ℝ := fun t ω => if L ω = 0 then 0 else D t ω with hD'def
  have hL0m : MeasurableSet {ω | L ω = 0} := measurableSet_eq_fun hLm measurable_const
  have hL'm : Measurable L' := Measurable.ite hL0m measurable_const hLm
  have hD'm : ∀ t, Measurable (D' t) := fun t => Measurable.ite hL0m measurable_const (hDm t)
  have hDD : ∀ ω, L ω ≠ 0 → L' ω = L ω ∧ (fun u => D' u ω) = fun u => D u ω := fun ω hω =>
    ⟨by simp only [hL'def, hω, ↓reduceIte], funext fun u => by simp only [hD'def, hω, ↓reduceIte]⟩
  have hC : CoordX x s P W' ζ' w γ α D' L' := by
    refine ⟨hD'm, hL'm, fun ω => ?_, fun ω => ?_, fun ω => ?_, fun t B hB => ?_, ?_⟩
    · by_cases hω : L ω = 0
      · simp only [hL'def, hω, ↓reduceIte, ENNReal.zero_lt_top]
      · rw [(hDD ω hω).1]; exact pos_iff_ne_zero.2 hω
    · by_cases hω : L ω = 0
      · have e : (fun u => D' u ω) = fun _ => 0 := funext fun u => by simp only [hD'def, hω, ↓reduceIte]
        rw [e]; exact continuousOn_const
      · rw [(hDD ω hω).1, (hDD ω hω).2]; exact hDc ω
    · by_cases hω : L ω = 0
      · simp only [hD'def, hω, ↓reduceIte]
      · simp only [hD'def, hω, ↓reduceIte]; exact hD0 ω
    · exact (measurableSet_lt measurable_const hL'm).inter (hD'm t hB)
    · filter_upwards [hrel, hLpos] with ω hrelω hposω hgx
      obtain ⟨h1, h2⟩ := hrelω hgx.2
      obtain ⟨hL', hD'⟩ := hDD ω (hposω hgx)
      have hD'' : (fun r : ℝ => D' r.toNNReal ω) = fun r : ℝ => D r.toNNReal ω :=
        funext fun r => congrFun hD' r.toNNReal
      rw [hL', hD'']
      exact ⟨h1, fun t ht => ⟨(h2 t ht).1, (h2 t ht).2.1, (h2 t ht).2.2.1⟩⟩
  refine ⟨D', L', hC, separationReadX x s, measurable_separationReadX x s, isCausal_separationReadX x s, ?_⟩
  filter_upwards [hrel, hLpos, hGae] with ω hrelω hposω hω hgx
  obtain ⟨⟨hγω, hγinf⟩, ⟨hζ, hWc, hW0⟩, -, hrg, hΨ⟩ := hG ω hω
  obtain ⟨hαω, hαc, hγc, hAe, hA, -⟩ := hfacts ω hω
  have hsζ : (s : ℝ≥0∞) < ζ' ω := by rw [hζ]; exact ENNReal.coe_lt_top
  have hsH : α ω s ∈ H := ((mem_gb6TS_iff hrg).2 hgx.1).2
  have hΨω := hΨ hsζ hsH
  have harcω := harcG ω hω hgx.2
  obtain ⟨hL', hD'⟩ := hDD ω (hposω hgx)
  obtain ⟨hrange, hK⟩ := hrelω hgx.2
  obtain ⟨ha0, ham, hac⟩ := clock_props W' ζ' ω hαω hWc hW0 hζ hs hx harcω (hwc ω) (hw0 ω) hγω
  rw [hL', hD']
  refine liveReadoutX_of_readback hs hγc hγinf hA hAe hαω.1 (a := fun t => clockX x s W' ζ' w t ω) ha0 ham hac
    hrange (fun t ht => ⟨(hK t ht).1, (hK t ht).2.1⟩) fun t ht => ?_
  exact readback_of_local W' ζ' ω hαω hWc hW0 hζ hs hx harcω (hwc ω) (hw0 ω) hγω hΨω (hK t ht).2.2.2

end Coord

end InteractingSLE.Theorem14.GW2Rz
