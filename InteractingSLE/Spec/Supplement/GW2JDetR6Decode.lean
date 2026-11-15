/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2JDetR6Model

/-!
# A Borel physical record map without a chosen relative buffer

Stop the candidate at physical capacities decreasing to the requested time
from above. For all sufficiently late stops the inverse record is already
the requested record. Coordinate limits give one total Borel readout.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2JDetR6

open Exist.StagedLaw GW2JDetR3 GW2JDetR4 GW2TipSystem

/-- Physical times approaching the requested cutoff strictly from above. -/
def laterTime (t : ℝ≥0) (n : ℕ) : ℝ≥0 := t + (1 / 2 : ℝ≥0) ^ n

theorem lt_laterTime (t : ℝ≥0) (n : ℕ) : t < laterTime t n :=
  lt_add_of_pos_right _ (pow_pos (by norm_num) _)

theorem tendsto_laterTime (t : ℝ≥0) : Tendsto (laterTime t) atTop (𝓝 t) := by
  change Tendsto (fun n : ℕ => t + (1 / 2 : ℝ≥0) ^ n) atTop (𝓝 t)
  simpa only [add_zero] using tendsto_const_nhds.add
    (NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (1 / 2 : ℝ≥0) < 1))

/-- Approximate readout stopped at a later attained physical-capacity level. -/
def recordApprox (s t : ℝ≥0) (n : ℕ)
    (x : RecData × ((ℝ≥0 → ℝ) × ℝ≥0∞)) : RecData :=
  inverseRecord s t (x.1, (x.2.1,
    physicalCapacityStop s (laterTime t n : ℝ≥0∞) x.1 x.2))

theorem measurable_recordApprox (s t : ℝ≥0) (n : ℕ) :
    Measurable (recordApprox s t n) :=
  (measurable_inverseRecord s t).comp
    (measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk
      (measurable_physicalCapacityStop s (laterTime t n))))

/-- Total Borel physical stopped-record decoder from a retained counterflow
record and a candidate relative driver, with its continuation lifetime. -/
def recordRead (s t : ℝ≥0) (x : RecData × ((ℝ≥0 → ℝ) × ℝ≥0∞)) : RecData :=
  (fun q : ℚ => limUnder atTop fun n => (recordApprox s t n x).1 q,
    (t : ℝ≥0∞), false)

theorem measurable_recordRead (s t : ℝ≥0) : Measurable (recordRead s t) := by
  refine (measurable_pi_iff.mpr fun q : ℚ => ?_).prodMk
    (measurable_const.prodMk measurable_const)
  apply StronglyMeasurable.measurable
  apply StronglyMeasurable.limUnder
  intro n
  exact ((measurable_pi_apply q).comp
    (measurable_fst.comp (measurable_recordApprox s t n))).stronglyMeasurable

/-- Eventual correctness suffices for the total coordinate decoder. -/
theorem recordRead_eq_of_eventually (s t : ℝ≥0)
    (x : RecData × ((ℝ≥0 → ℝ) × ℝ≥0∞)) (R : RecData)
    (hR : R.2 = ((t : ℝ≥0∞), false))
    (he : ∀ᶠ n in atTop, recordApprox s t n x = R) : recordRead s t x = R := by
  refine Prod.ext (funext fun q => ?_) hR.symm
  exact (tendsto_const_nhds.congr' (he.mono fun n hn =>
    congrArg (fun y : RecData => y.1 q) hn.symm)).limUnder_eq

/-- The readout recovers the physical live record whenever the candidate
has the correct inverse hulls and remains available at the physical clock. -/
theorem recordRead_eq_of_inverse_hulls
    (s : ℝ≥0) (r : RecData) {a : ℝ≥0 → ℝ} {S T : ℝ≥0∞}
    (ha0 : a 0 = 0) (hm : StrictMonoOn a {u | (u : ℝ≥0∞) < S})
    (hc : ContinuousOn a {u | (u : ℝ≥0∞) < S})
    {e : (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hec : ContinuousOn e.1 {u | (u : ℝ≥0∞) < e.2}) (he0 : e.1 0 = 0)
    {w : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace w T γ)
    (hw : ContinuousOn w {u | (u : ℝ≥0∞) < T}) (hw0 : w 0 = 0) (hST : S ≤ T)
    (hlife : ∀ u : ℝ≥0, (u : ℝ≥0∞) < S → ((a u).toNNReal : ℝ≥0∞) < e.2)
    (hinv : ∀ u : ℝ≥0, (u : ℝ≥0∞) < S →
      Supp8.GB6.relInv (rdrv r) s '' QuantumZipper.fwdHull (Ito.rpath e.1) (a u) =
        QuantumZipper.fwdHull (Ito.rpath w) u)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < S) :
    recordRead s t (r, e) = cfRec t (fun u (_ : Unit) => w u) (fun _ => T) () := by
  apply recordRead_eq_of_eventually
  · rw [← cfRec_eq_live_samples t hw hw0 (ht.trans_le hST)]
  have hev : ∀ᶠ n in atTop, (laterTime t n : ℝ≥0∞) < S :=
    ((ENNReal.continuous_coe.tendsto t).comp (tendsto_laterTime t)).eventually
      (isOpen_Iio.mem_nhds ht)
  filter_upwards [hev] with n hn
  exact inverseRecord_capacityStop_of_inverse_hulls s r ha0 hm hc hec he0
    hγ hw hw0 hST hlife hinv (lt_laterTime t n) hn

end InteractingSLE.Theorem14.GW2JDetR6
