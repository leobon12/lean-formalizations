/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RdStgChain
import InteractingSLE.Spec.Supplement.WalkInfMeas
import InteractingSLE.Spec.Supplement.BW1LMeanRet
import InteractingSLE.Spec.Sec7.StripMark

/-!
# GW2's stage identity: the stage chart has measurable data

Packet PROVE-GW2-RELDET, ruling R106. K2's lines assembly at a stage (`GW2Rd.hasRelSafe_of_lines_rec`) needs the
stage chart to be conformal with a continuous harmonic lift, and its domain, masked forward map and masked lift to be
readable at time `0` of the stage's physical filtration. This is `WalkInf.IsMeasChart` for that σ-algebra.

* `isRegularDriver_top`: a continuous driver from `0` with infinite lifetime is regular;
* `recChart_recOf_top`: the record chart of `(R, ⊤)` stopped at `a` is the centred Loewner chart `Chart.id.loewner
  (rpath R) a` (`Exist.StagedLaw.recChart_eq_loewner`; the Loewner chart only reads the driver up to `a`,
  `LocalExt.id_loewner_congr`);
* **`stgChart_eq_trans`**: the stage chart `stgChart c R a = c.loewner (rpath R) a` is `c.trans (recChart (recOf a
  (R, ⊤)))`;
* `isMeasChart_relChart`: the joint chart of a measurable record has measurable data (GB6's `RelSafeS` lemmas);
* **`isMeasChart_stgChart`**: hence the stage chart has measurable data for every σ-algebra reading the counterflow
  record and the relative record `recOf a (R, ⊤)` (`WalkInf.IsMeasChart.trans_recChart`).

Deterministic and measurability content only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.GW2Rd

open Exist.Staged Exist.StagedLaw Supp8.RelSafeS

/-- A continuous driver from `0` with infinite lifetime is regular. -/
theorem isRegularDriver_top {R : ℝ≥0 → ℝ} (hR : Continuous R) (hR0 : R 0 = 0) : IsRegularDriver (R, ⊤) :=
  ⟨hR.continuousOn, hR0, fun _ ht => absurd ht (not_le.2 ENNReal.coe_lt_top), fun h => absurd rfl h⟩

/-- **The record chart of `(R, ⊤)` stopped at `a` is the centred Loewner chart at `a`.** -/
theorem recChart_recOf_top {R : ℝ≥0 → ℝ} (hR : Continuous R) (hR0 : R 0 = 0) (a : ℝ≥0) :
    recChart (recOf (a : ℝ≥0∞) (R, ⊤)) = Chart.id.loewner (Ito.rpath R) a := by
  have he := isRegularDriver_top hR hR0
  have hlt : (a : ℝ≥0∞) < (R, (⊤ : ℝ≥0∞)).2 := ENNReal.coe_lt_top
  have hg := Sec7.StripMark.isDrvGood_recOf_of_lt he hlt
  rw [recChart_eq_loewner he hg]
  have hmin : (min (a : ℝ≥0∞) (R, (⊤ : ℝ≥0∞)).2).toNNReal = a := by
    simp only [le_top, min_eq_left, ENNReal.toNNReal_coe]
  rw [hmin]
  have hret : ∀ r : ℝ≥0, (retOf (a : ℝ≥0∞) (R, ⊤)).1 r = R (min r a) := fun r => by
    change R (min (r : ℝ≥0∞) (min (a : ℝ≥0∞) ⊤)).toNNReal = R (min r a)
    rw [min_eq_left le_top, ← ENNReal.coe_min, ENNReal.toNNReal_coe]
  have hc1 : Continuous fun x : ℝ => (retOf (a : ℝ≥0∞) (R, ⊤)).1 x.toNNReal := by
    have e : (fun x : ℝ => (retOf (a : ℝ≥0∞) (R, ⊤)).1 x.toNNReal) = fun x : ℝ => R (min x.toNNReal a) :=
      funext fun x => hret _
    rw [e]
    exact hR.comp (continuous_real_toNNReal.min continuous_const)
  have hc2 : Continuous (Ito.rpath R) := hR.comp continuous_real_toNNReal
  refine LocalExt.id_loewner_congr (t' := (a : ℝ) + 1) hc1.continuousOn hc2.continuousOn a.coe_nonneg
    (lt_add_one _) fun x hx => ?_
  change (retOf (a : ℝ≥0∞) (R, ⊤)).1 x.toNNReal = R x.toNNReal
  rw [hret, min_eq_left (Real.toNNReal_le_iff_le_coe.2 hx.2)]

/-- **The stage chart is the chart followed by the record chart of the relative driver at the start.** -/
theorem stgChart_eq_trans (c : Chart) {R : ℝ≥0 → ℝ} (hR : Continuous R) (hR0 : R 0 = 0) (a : ℝ≥0) :
    stgChart c R a = c.trans (recChart (recOf (a : ℝ≥0∞) (R, ⊤))) := by
  rw [recChart_recOf_top hR hR0 a]
  unfold stgChart Chart.loewner Chart.trans Chart.id
  simp only [add_zero]

/-- The joint chart of a measurable record has measurable data. -/
theorem isMeasChart_relChart {Ω : Type*} {m : MeasurableSpace Ω} {rec : Ω → RecData} (hr : Measurable[m] rec) :
    WalkInf.IsMeasChart m fun ω => relChart (rec ω) :=
  ⟨fun _ => isConformal_relChart _, fun _ => continuousOn_lift_relChart _, fun _ => harmonicOnNhd_lift_relChart _,
    fun z => hr (measurableSet_mem_dom_relChart z), fun z => (measurable_indicator_fwd_relChart z).comp hr,
    fun z ε => hr (BW1LMean.measurableSet_closedBall_subset_dom_relChart z ε),
    fun z => (measurable_indicator_lift_relChart z).comp hr⟩

/-- **The stage chart has measurable data** for every σ-algebra reading the counterflow record and the relative record
at the start. -/
theorem isMeasChart_stgChart {Ω : Type*} {m : MeasurableSpace Ω} {rec : Ω → RecData} (hr : Measurable[m] rec)
    {R : ℝ≥0 → Ω → ℝ} (hRc : ∀ ω, Continuous fun t => R t ω) (hR0 : ∀ ω, R 0 ω = 0) {a : Ω → ℝ≥0}
    (hra : Measurable[m] fun ω => recOf (a ω : ℝ≥0∞) (fun t => R t ω, ⊤)) :
    WalkInf.IsMeasChart m fun ω => stgChart (relChart (rec ω)) (fun t => R t ω) (a ω) := by
  have e : (fun ω => stgChart (relChart (rec ω)) (fun t => R t ω) (a ω)) =
      fun ω => (relChart (rec ω)).trans (recChart (recOf (a ω : ℝ≥0∞) (fun t => R t ω, ⊤))) :=
    funext fun ω => stgChart_eq_trans _ (hRc ω) (hR0 ω) _
  rw [e]
  exact (isMeasChart_relChart hr).trans_recChart hra

end InteractingSLE.Theorem14.GW2Rd
