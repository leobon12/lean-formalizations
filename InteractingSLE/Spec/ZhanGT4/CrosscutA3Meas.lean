/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.StripTimeLoc

/-!
# A.3.2: the chordal driver as a functional of the strip driver path

Packet PROVE-ZHAN-A34. Source: Astra, *Follow-up proofs and dependency audit*, §A.3.2
(`source/external/AstraIG1/ig1_followup_proofs.txt` L657–L720, ruling R38): "Consequently the original strip law is
the mixture … Mapping back gives the original killed chordal law as a mixture". Mapping back is the inverse of the
R36 time change: with `ξ` the strip driver path, the chordal time at strip time `t`, the end mark and the driver are

  `s(t) = ∫₀ᵗ e^{2(ξ_r − r)} dr`,   `V_{s(t)} = −1 − 2 ∫₀ᵗ e^{ξ_r − r} dr`,   `W_{s(t)} = V_{s(t)} + e^{ξ_t − t}`

(`ds/dt = (W − V)² = e^{2(ξ − t)}`, `dV/ds = 2/(V − W)`). These formulas define the chordal driver `reconDrv ξ` on
`[0, reconEnd ξ)` for every path `ξ`, so a property of the chordal hulls becomes a set of strip paths.

## Main definitions

* `reconClock ξ t`, `reconEnd ξ`, `reconTime ξ s`, `reconMark ξ t`, `reconDrv ξ s`: the reconstruction;
* `stripPath w v`: the strip driver path `t ↦ ξ_t` of a chordal pair `(w, v)` (as in the law identities of
  PROVE-ZHAN-A32/A33).

## Main results

* `Strip.IsSepMark.chordalTime_eq_integral`, `Strip.IsSepMark.v_chordalTime_eq`,
  `Strip.IsSepMark.w_chordalTime_eq`: the three formulas on a separated stretch;
* for a pair `(w, v)` that is separated on its strip life (`hsep`) with an unbounded strip clock (`hcl`):
  `reconClock_stripPath` (`reconClock ξ = s`), **`isStripLife_iff_lt_reconEnd`** (the strip life is
  `[0, reconEnd ξ)`) and **`eq_reconDrv_of_isStripLife`** (`w = reconDrv ξ` on the strip life).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Strip.IsSepMark

variable {w v : ℝ → ℝ} {S : ℝ}

theorem exp_stripDriver_sub (h : IsSepMark w v S) {t : ℝ} (ht : t ∈ Icc 0 (stripClock w v S)) :
    Real.exp (stripDriver w v t - t) = w (chordalTime w v t) - v (chordalTime w v t) := by
  rw [stripDriver, add_sub_cancel_left, Real.exp_log (sub_pos.2 (h.lt _ (h.chordalTime_mem ht)))]

theorem continuousOn_exp_two_mul (h : IsSepMark w v S) :
    ContinuousOn (fun r => Real.exp (2 * (stripDriver w v r - r))) (Icc 0 (stripClock w v S)) :=
  Real.continuous_exp.comp_continuousOn (continuousOn_const.mul (h.continuousOn_stripDriver.sub continuousOn_id))

theorem continuousOn_exp_sub (h : IsSepMark w v S) :
    ContinuousOn (fun r => Real.exp (stripDriver w v r - r)) (Icc 0 (stripClock w v S)) :=
  Real.continuous_exp.comp_continuousOn (h.continuousOn_stripDriver.sub continuousOn_id)

/-- **The chordal clock in strip coordinates**: `s(t) = ∫₀ᵗ e^{2(ξ_r − r)} dr`. -/
theorem chordalTime_eq_integral (h : IsSepMark w v S) {t : ℝ} (ht : t ∈ Icc 0 (stripClock w v S)) :
    chordalTime w v t = ∫ r in (0 : ℝ)..t, Real.exp (2 * (stripDriver w v r - r)) := by
  have hsub : Icc 0 t ⊆ Icc 0 (stripClock w v S) := Icc_subset_Icc_right ht.2
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1 (h.continuousOn_chordalTime.mono hsub)
    (fun r hr => h.hasDerivAt_chordalTime_eq_exp ⟨hr.1, lt_of_lt_of_le hr.2 ht.2⟩)
    ((h.continuousOn_exp_two_mul.mono hsub).intervalIntegrable_of_Icc ht.1), h.chordalTime_zero, sub_zero]

/-- **The end mark in strip coordinates**: `V_{s(t)} = −1 − 2 ∫₀ᵗ e^{ξ_r − r} dr`. -/
theorem v_chordalTime_eq (h : IsSepMark w v S) {t : ℝ} (ht : t ∈ Icc 0 (stripClock w v S)) :
    v (chordalTime w v t) = -1 - 2 * ∫ r in (0 : ℝ)..t, Real.exp (stripDriver w v r - r) := by
  have hsub : Icc 0 t ⊆ Icc 0 (stripClock w v S) := Icc_subset_Icc_right ht.2
  have hcont : ContinuousOn (fun r => v (chordalTime w v r)) (Icc 0 t) :=
    (h.continuousOn_v.comp h.continuousOn_chordalTime h.mapsTo_chordalTime).mono hsub
  have hderiv : ∀ r ∈ Ioo 0 t, HasDerivAt (fun r => v (chordalTime w v r))
      (-2 * Real.exp (stripDriver w v r - r)) r := by
    intro r hr
    have hr' : r ∈ Ioo 0 (stripClock w v S) := ⟨hr.1, lt_of_lt_of_le hr.2 ht.2⟩
    have hd := (h.hasDerivAt_v (h.chordalTime_mem_Ioo hr')).comp r (h.hasDerivAt_chordalTime_eq_exp hr')
    refine hd.congr_deriv ?_
    have he := h.exp_stripDriver_sub (Ioo_subset_Icc_self hr')
    have hpos : 0 < w (chordalTime w v r) - v (chordalTime w v r) :=
      sub_pos.2 (h.lt _ (h.chordalTime_mem (Ioo_subset_Icc_self hr')))
    rw [show 2 * (stripDriver w v r - r) = (stripDriver w v r - r) + (stripDriver w v r - r) by ring,
      Real.exp_add, he]
    have hba : v (chordalTime w v r) - w (chordalTime w v r) = -(w (chordalTime w v r) - v (chordalTime w v r)) := by
      ring
    rw [hba]
    field_simp [hpos.ne']
  have hint : IntervalIntegrable (fun r => -2 * Real.exp (stripDriver w v r - r)) volume 0 t :=
    ((continuousOn_const.mul h.continuousOn_exp_sub).mono hsub).intervalIntegrable_of_Icc ht.1
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1 hcont hderiv hint
  rw [intervalIntegral.integral_const_mul, h.chordalTime_zero, h.v_zero] at hftc
  linarith

/-- **The driver in strip coordinates**: `W_{s(t)} = V_{s(t)} + e^{ξ_t − t}`. -/
theorem w_chordalTime_eq (h : IsSepMark w v S) {t : ℝ} (ht : t ∈ Icc 0 (stripClock w v S)) :
    w (chordalTime w v t) = v (chordalTime w v t) + Real.exp (stripDriver w v t - t) := by
  rw [h.exp_stripDriver_sub ht]; ring

end Strip.IsSepMark

namespace ZhanGT4.A34

/-! ### The reconstruction from a strip path -/

/-- The chordal clock of a strip path: `∫₀ᵗ e^{2(ξ_r − r)} dr`. -/
def reconClock (ξ : ℝ≥0 → ℝ) (t : ℝ) : ℝ := ∫ r in (0 : ℝ)..t, Real.exp (2 * (Strip.extPath ξ r - r))

/-- The total chordal time of a strip path (the end of the strip life). -/
def reconEnd (ξ : ℝ≥0 → ℝ) : ℝ≥0∞ := ⨆ t : ℝ≥0, ENNReal.ofReal (reconClock ξ t)

/-- The strip time at chordal time `s`. -/
def reconTime (ξ : ℝ≥0 → ℝ) (s : ℝ) : ℝ := sInf {t | 0 ≤ t ∧ s ≤ reconClock ξ t}

/-- The end mark at strip time `t`: `−1 − 2 ∫₀ᵗ e^{ξ_r − r} dr`. -/
def reconMark (ξ : ℝ≥0 → ℝ) (t : ℝ) : ℝ := -1 - 2 * ∫ r in (0 : ℝ)..t, Real.exp (Strip.extPath ξ r - r)

/-- **The chordal driver reconstructed from a strip path**, at chordal time `s`. -/
def reconDrv (ξ : ℝ≥0 → ℝ) (s : ℝ) : ℝ :=
  reconMark ξ (reconTime ξ s) + Real.exp (Strip.extPath ξ (reconTime ξ s) - reconTime ξ s)

/-- The strip driver path of a chordal pair `(w, v)`. -/
def stripPath (w v : ℝ≥0 → ℝ) : ℝ≥0 → ℝ := fun t => Strip.stripDriver (Strip.extPath w) (Strip.extPath v) t

theorem extPath_stripPath (w v : ℝ≥0 → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    Strip.extPath (stripPath w v) r = Strip.stripDriver (Strip.extPath w) (Strip.extPath v) r := by
  simp [Strip.extPath, stripPath, Real.coe_toNNReal r hr]

/-! ### Paths separated on their strip life with an unbounded clock -/

section Life

variable {w v : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
  (hsep : ∀ s, Strip.IsStripLife w v ζ s → Strip.IsSepMark (Strip.extPath w) (Strip.extPath v) s)
  (hcl : Zhan.HasUnboundedStripClock w v ζ)

include hsep hcl in
theorem exists_isStripLife_mem_Icc {t : ℝ} (ht : 0 ≤ t) : ∃ S : ℝ≥0, Strip.IsStripLife w v ζ S ∧
    Strip.IsSepMark (Strip.extPath w) (Strip.extPath v) S ∧
    t ∈ Icc 0 (Strip.stripClock (Strip.extPath w) (Strip.extPath v) S) := by
  obtain ⟨S, hS, hle⟩ := hcl t
  exact ⟨S, hS, hsep S hS, ht, hle⟩

include hsep hcl in
/-- `reconClock ξ` is the chordal time at every strip time. -/
theorem reconClock_stripPath {t : ℝ} (ht : 0 ≤ t) :
    reconClock (stripPath w v) t = Strip.chordalTime (Strip.extPath w) (Strip.extPath v) t := by
  obtain ⟨S, -, hS, htS⟩ := exists_isStripLife_mem_Icc hsep hcl ht
  rw [hS.chordalTime_eq_integral htS, reconClock]
  refine intervalIntegral.integral_congr fun r hr => ?_
  rw [uIcc_of_le ht] at hr
  simp only [extPath_stripPath w v hr.1]

include hsep hcl in
theorem strictMonoOn_chordalTime_Ici :
    StrictMonoOn (Strip.chordalTime (Strip.extPath w) (Strip.extPath v)) (Ici 0) := by
  intro a ha b hb hab
  obtain ⟨S, -, hS, hbS⟩ := exists_isStripLife_mem_Icc hsep hcl (show (0 : ℝ) ≤ b from hb)
  exact hS.strictMonoOn_chordalTime ⟨ha, hab.le.trans hbS.2⟩ hbS hab

include hsep hcl in
theorem isStripLife_chordalTime {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ Strip.chordalTime (Strip.extPath w) (Strip.extPath v) t ∧
      Strip.IsStripLife w v ζ (Strip.chordalTime (Strip.extPath w) (Strip.extPath v) t).toNNReal := by
  obtain ⟨S, hlife, hS, htS⟩ := exists_isStripLife_mem_Icc hsep hcl ht
  have hm := hS.chordalTime_mem htS
  exact ⟨hm.1, hlife.mono (Real.toNNReal_le_iff_le_coe.2 hm.2)⟩

include hsep hcl in
/-- **The strip life is `[0, reconEnd ξ)`.** -/
theorem isStripLife_iff_lt_reconEnd {s : ℝ≥0} :
    Strip.IsStripLife w v ζ s ↔ (s : ℝ≥0∞) < reconEnd (stripPath w v) := by
  constructor
  · intro hs
    have hS := hsep s hs
    set t := Strip.stripClock (Strip.extPath w) (Strip.extPath v) s with htdef
    have ht0 : 0 ≤ t := hS.stripClock_nonneg ⟨s.coe_nonneg, le_rfl⟩
    have hts : Strip.chordalTime (Strip.extPath w) (Strip.extPath v) t = s :=
      hS.chordalTime_stripClock ⟨s.coe_nonneg, le_rfl⟩
    have hlt : (s : ℝ) < Strip.chordalTime (Strip.extPath w) (Strip.extPath v) (t + 1) := by
      rw [← hts]
      exact strictMonoOn_chordalTime_Ici hsep hcl (show (0 : ℝ) ≤ t from ht0)
        (show (0 : ℝ) ≤ t + 1 by linarith) (by linarith)
    refine lt_of_lt_of_le ?_ (le_iSup _ (t + 1).toNNReal)
    rw [Real.coe_toNNReal _ (by linarith), reconClock_stripPath hsep hcl (by linarith)]
    rw [← ENNReal.ofReal_coe_nnreal]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg s.coe_nonneg).2 hlt
  · intro hs
    obtain ⟨t, ht⟩ := lt_iSup_iff.1 hs
    rw [reconClock_stripPath hsep hcl t.coe_nonneg, ← ENNReal.ofReal_coe_nnreal] at ht
    have hlt := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg s.coe_nonneg).1 ht
    obtain ⟨h0, hlife⟩ := isStripLife_chordalTime hsep hcl t.coe_nonneg
    refine hlife.mono ?_
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ h0]
    exact hlt.le

include hsep hcl in
/-- **The driver is the reconstruction on the strip life.** -/
theorem eq_reconDrv_of_isStripLife {s : ℝ≥0} (hs : Strip.IsStripLife w v ζ s) :
    w s = reconDrv (stripPath w v) s := by
  have hS := hsep s hs
  set t := Strip.stripClock (Strip.extPath w) (Strip.extPath v) s with htdef
  have ht0 : 0 ≤ t := hS.stripClock_nonneg ⟨s.coe_nonneg, le_rfl⟩
  have htS : t ∈ Icc 0 (Strip.stripClock (Strip.extPath w) (Strip.extPath v) s) := ⟨ht0, le_rfl⟩
  have hts : Strip.chordalTime (Strip.extPath w) (Strip.extPath v) t = s :=
    hS.chordalTime_stripClock ⟨s.coe_nonneg, le_rfl⟩
  -- the strip time at chordal time `s` is `t`
  have hrt : reconTime (stripPath w v) s = t := by
    have hl : IsLeast {t' | 0 ≤ t' ∧ (s : ℝ) ≤ reconClock (stripPath w v) t'} t := by
      refine ⟨⟨ht0, by rw [reconClock_stripPath hsep hcl ht0, hts]⟩, fun t' ht' => ?_⟩
      by_contra hlt
      have hlt := not_le.1 hlt
      have h1 := strictMonoOn_chordalTime_Ici hsep hcl (show (0 : ℝ) ≤ t' from ht'.1)
        (show (0 : ℝ) ≤ t from ht0) hlt
      have h2 := ht'.2
      rw [reconClock_stripPath hsep hcl ht'.1] at h2
      rw [hts] at h1
      linarith
    exact hl.csInf_eq
  have hmark : reconMark (stripPath w v) t =
      Strip.extPath v (Strip.chordalTime (Strip.extPath w) (Strip.extPath v) t) := by
    rw [hS.v_chordalTime_eq htS, reconMark]
    congr 2
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le ht0] at hr
    simp only [extPath_stripPath w v hr.1]
  rw [reconDrv, hrt, hmark, extPath_stripPath w v ht0, ← hS.w_chordalTime_eq htS, hts, Strip.extPath_coe]

end Life

end ZhanGT4.A34

end InteractingSLE
