/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6GaugeEVersion
import InteractingSLE.Spec.Supplement.WalkStageLocalMeas

/-!
# GB6's separation gauge at the record's own time

Packet PROVE-BW1-INPUTS2. GB6's separation readout `ReadD.separationRead s` is a measurable causal functional of
(record, relative path) for a FIXED own time `s` of the retained prefix. Proposition BW1's retained piece ends at a
random time, which the record carries (`recS r`). `bwRead` is the same functional with `s` read from the record and
the retained trace read through LP's measurable endpoint selector (`LP.endpointTrace`): it is measurable and causal
(`measurable_bwRead`, `isCausal_bwRead`), and on a record whose retained trace is continuous it IS
`separationRead (recS r)` (`bwRead_eq_separationRead`), so all of GB6's deterministic gauge lemmas apply.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Complex
open QuantumZipper (H Hbar)
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.BW1Ver

open Exist.StagedLaw Supp8.GB6 Supp8.GB6.ReadD Supp8.GB6.RelDrv.Version

/-- The own time of a record. -/
def recS (r : RecData) : ℝ≥0 := r.2.1.toNNReal

theorem rtime_eq_recS (r : RecData) : rtime r = (recS r : ℝ) := rfl

theorem measurable_recS : Measurable recS :=
  ENNReal.measurable_toNNReal.comp (measurable_fst.comp measurable_snd)

/-- The record driver read at real times through `toNNReal` is the record driver. -/
theorem rdrv_toNNReal (r : RecData) : (fun x : ℝ => rdrv r (x.toNNReal : ℝ)) = rdrv r := by
  funext x
  simp only [rdrv, Real.toNNReal_coe]

/-- GB6's inverse read-back at the record's own time is jointly measurable. -/
theorem measurable_inverseRead_rec : Measurable fun p : RecData × ℂ => inverseRead (recS p.1) p := by
  apply StronglyMeasurable.measurable
  apply StronglyMeasurable.limUnder
  intro n
  apply Measurable.stronglyMeasurable
  have hZ : Measurable fun p : RecData × ℂ => -(CoordB.vert n (upperPoint p.2))⁻¹ :=
    (((measurable_upperPoint.comp measurable_snd).add_const _).inv).neg
  have hZH : ∀ p : RecData × ℂ, -(CoordB.vert n (upperPoint p.2))⁻¹ ∈ H :=
    fun p => neg_inv_mem_H (CoordB.vert_mem_H (upperPoint_mem p.2) n)
  have hm := Theorem14.WalkLaw.measurable_fwdMapInv_randomTime (B := fun t (p : RecData × ℂ) => rdrv p.1 t)
    (fun t => (measurable_rdrv_apply t).comp measurable_fst)
    (fun p => (continuous_rdrv p.1).comp NNReal.continuous_coe) (fun p => rdrv_zero p.1)
    (measurable_recS.comp measurable_fst) hZ hZH
  have hm' : Measurable fun p : RecData × ℂ =>
      QuantumZipper.fwdMapInv (rdrv p.1) (recS p.1 : ℝ) (-(CoordB.vert n (upperPoint p.2))⁻¹) := by
    convert hm using 1
    funext p
    rw [rdrv_toNNReal]
    rfl
  exact hm'.inv.neg

/-- GB6's physical trace read-back at the record's own time is measurable. -/
theorem measurable_physicalTrace_rec (t : ℝ≥0) :
    Measurable fun p : RecData × (ℝ≥0 → ℝ) => physicalTrace (recS p.1) t p :=
  measurable_inverseRead_rec.comp (measurable_fst.prodMk ((LP.measurable_traceAt t).comp measurable_snd))

/-- The retained trace of a record, through LP's measurable endpoint selector. -/
def retTr (r : RecData) (v : ℝ≥0) : ℂ := LP.endpointTrace (v : ℝ≥0∞) (fun u => rdrv r u)

theorem measurable_retTr_mul (q : ℝ≥0) : Measurable fun r : RecData => retTr r (recS r * q) :=
  LP.measurable_endpointTrace.comp ((measurable_coe_nnreal_ennreal.comp (measurable_recS.mul_const q)).prodMk
    (measurable_pi_iff.2 fun u => measurable_rdrv_apply u))

/-- On a retained trace that is continuous at and before `v`, the endpoint selector reads the trace. -/
theorem retTr_eq {r : RecData} {v : ℝ≥0} (hc : ContinuousOn (fun u => recordTrace u r) (Iic v))
    (h0 : recordTrace 0 r = 0) : retTr r v = recordTrace v r := by
  unfold retTr LP.endpointTrace
  by_cases hv : v = 0
  · subst hv
    simp only [ENNReal.coe_zero, ↓reduceIte, h0]
  · have hv0 : (v : ℝ≥0∞) ≠ 0 := by exact_mod_cast hv
    simp only [hv0, ↓reduceIte, ENNReal.toNNReal_coe]
    have hvp : 0 < v := lt_of_le_of_ne (zero_le : (0 : ℝ≥0) ≤ v) (Ne.symm hv)
    have hlim : Tendsto (fun n => LP.dyadicBelow n v) atTop (𝓝[Iic v] v) :=
      tendsto_nhdsWithin_iff.2 ⟨LP.tendsto_dyadicBelow v,
        Eventually.of_forall fun n => (LP.dyadicBelow_lt hvp n).le⟩
    exact ((hc v (mem_Iic.2 le_rfl)).tendsto.comp hlim).limUnder_eq

/-- **GB6's separation gauge at the record's own time**, with the retained trace read by the endpoint selector. -/
def bwRead : GaugeReadout := fun t p =>
  (⨅ q : RationalUnit × RationalUnit, ENNReal.ofReal
    (separationValue (physicalTrace (recS p.1) (t * (q.1.val : ℝ≥0)) p)
      (retTr p.1 (recS p.1 * (q.2.val : ℝ≥0))))).toReal

theorem measurable_bwRead (t : ℝ≥0) : Measurable (bwRead t) := by
  apply ENNReal.measurable_toReal.comp
  apply Measurable.iInf
  intro q
  apply Measurable.ennreal_ofReal
  unfold separationValue
  exact measurable_const.min
    (((measurable_physicalTrace_rec _).mul ((measurable_retTr_mul _).comp measurable_fst)).add_const 1 |>.norm
      |>.div (measurable_const.add (measurable_physicalTrace_rec _).norm))

theorem isCausal_bwRead : IsCausal bwRead := by
  intro t r w w' h
  unfold bwRead
  apply congrArg ENNReal.toReal
  apply iInf_congr
  intro q
  have hq : (q.1.val : ℝ≥0) ≤ 1 := by exact_mod_cast q.1.property
  have hqt : t * (q.1.val : ℝ≥0) ≤ t := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hq (zero_le : (0 : ℝ≥0) ≤ t)
  have he := physicalTrace_congr (recS r) (t * (q.1.val : ℝ≥0)) r (fun u hu => h u (hu.trans hqt))
  exact congrArg (fun z : ℂ => ENNReal.ofReal
    (separationValue z (retTr r (recS r * (q.2.val : ℝ≥0))))) he

/-- **On a record with a continuous retained trace from `0`, the gauge is GB6's `separationRead` at its own
time.** -/
theorem bwRead_eq_separationRead {r : RecData} (hc : ContinuousOn (fun u => recordTrace u r) (Iic (recS r)))
    (h0 : recordTrace 0 r = 0) (t : ℝ≥0) (w : ℝ≥0 → ℝ) :
    bwRead t (r, w) = separationRead (recS r) t (r, w) := by
  unfold bwRead separationRead
  apply congrArg ENNReal.toReal
  apply iInf_congr
  intro q
  have hq : (q.2.val : ℝ≥0) ≤ 1 := by exact_mod_cast q.2.property
  have hqs : recS r * (q.2.val : ℝ≥0) ≤ recS r := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hq (zero_le : (0 : ℝ≥0) ≤ recS r)
  change ENNReal.ofReal (separationValue _ (retTr r (recS r * (q.2.val : ℝ≥0)))) = _
  rw [retTr_eq (hc.mono (Iic_subset_Iic.2 hqs)) h0]

end InteractingSLE.Theorem14.BW1Ver
