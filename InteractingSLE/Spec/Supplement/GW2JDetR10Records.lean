/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootV7Record
import InteractingSLE.Spec.Supplement.GB6RelDrvLift

/-!
# Stopped driver comparisons on GW2's common record carrier

Only live rational values enter either comparison event. Good canonical
driver codes therefore suffice through the observed stop; no inverse
physical record map or continuation-lifetime equality is required.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace InteractingSLE.Theorem14.GW2JDetR10

open GW2TipSystem.RootV7 Supp8.GB6 Supp8.GB6.RelDrv
  Sec2.Assembly

/-- A bound on a longer record bounds every live value of its prefix. -/
theorem mem_slowSet_of_livePrefix {z y : DriverRecord} (hle : z.1 ≤ y.1)
    (hread : ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < z.1 → z.2 q = y.2 q)
    (hy : y ∈ slowSet) : z ∈ slowSet := by
  intro q hq1 hq
  rw [hread q hq]
  exact hy q hq1 (hq.trans_le hle)

/-- The crossing test is a countable event of the common record. Stating
it directly avoids importing physical decoding or boundary-fibre results. -/
theorem measurableSet_liveCrossing : MeasurableSet {z : DriverRecord |
    ∃ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < z.1 ∧ 2 < z.2 q} := by
  have heq : {z : DriverRecord | ∃ q : ℚ≥0,
      ((q : ℝ≥0) : ℝ≥0∞) < z.1 ∧ 2 < z.2 q} =
      ⋃ q : ℚ≥0, {z : DriverRecord | ((q : ℝ≥0) : ℝ≥0∞) < z.1 ∧ 2 < z.2 q} := by
    ext z
    simp only [mem_ofPred_eq, mem_iUnion]
  rw [heq]
  exact MeasurableSet.iUnion fun q =>
    (measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt measurable_const ((measurable_pi_apply q).comp measurable_snd))

/-- The rational driver record decoded from a canonical code, stopped at
the supplied buffer and shifted to its absolute starting position. -/
def codeSample (a : ℝ) (L : ℝ≥0∞) (p : PCode × ℝ≥0∞) : DriverRecord :=
  cutRecord L (p.2, fun q => a + drvDec p q)

theorem measurable_codeSample {Ω : Type*} [MeasurableSpace Ω] (a : ℝ)
    {L : Ω → ℝ≥0∞} {p : Ω → PCode × ℝ≥0∞}
    (hL : Measurable L) (hp : Measurable p) :
    Measurable fun ω => codeSample a (L ω) (p ω) :=
  measurable_cutRecord hL (hp.snd.prodMk (measurable_pi_iff.2 fun q =>
    measurable_const.add ((measurable_drvDec q).comp hp)))

theorem codeSample_read (a : ℝ) (L : ℝ≥0∞) (p : PCode × ℝ≥0∞) {q : ℚ≥0}
    (hq : ((q : ℝ≥0) : ℝ≥0∞) < min L p.2) :
    (codeSample a L p).2 q = a + drvDec p q := ite_eq_left hq

/-- A stopped canonical driver match identifies every live rational
reading, with the physical record's own killing time. -/
theorem codeSample_liveRead_of_isStopDrvMatch {p : PCode × ℝ≥0∞}
    (hp : IsGoodDrvCode p) {W : ℝ≥0 → ℝ} {e : ℝ≥0∞}
    (hc : ContinuousOn W {t | (t : ℝ≥0∞) < e}) (hm : IsStopDrvMatch p W e)
    {a : ℝ} {z : DriverRecord} (hze : z.1 ≤ e)
    (hread : ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < z.1 → z.2 q = a + W q) :
    (codeSample a z.1 p).1 = z.1 ∧ ∀ q : ℚ≥0,
      ((q : ℝ≥0) : ℝ≥0∞) < z.1 → (codeSample a z.1 p).2 q = z.2 q := by
  have hzp : z.1 ≤ p.2 := hze.trans hm.1
  have hdec := eqOn_drvDec_of_isStopDrvMatch hp hc hm
  refine ⟨min_eq_left hzp, fun q hq => ?_⟩
  rw [codeSample_read a z.1 p (by rwa [min_eq_left hzp]),
    hdec q (hq.trans_le hze), hread q hq]

/-- Slow-event equivalence needs neither a full model-law identity nor
any information after the physical buffer. -/
theorem mem_slowSet_iff_codeSample_of_isStopDrvMatch {p : PCode × ℝ≥0∞}
    (hp : IsGoodDrvCode p) {W : ℝ≥0 → ℝ} {e : ℝ≥0∞}
    (hc : ContinuousOn W {t | (t : ℝ≥0∞) < e}) (hm : IsStopDrvMatch p W e)
    {a : ℝ} {z : DriverRecord} (hze : z.1 ≤ e)
    (hread : ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < z.1 → z.2 q = a + W q) :
    z ∈ slowSet ↔ codeSample a z.1 p ∈ slowSet := by
  obtain ⟨hlife, hvals⟩ := codeSample_liveRead_of_isStopDrvMatch hp hc hm hze hread
  constructor
  · exact mem_slowSet_of_livePrefix hlife.le (fun q hq => hvals q (hlife ▸ hq))
  · exact mem_slowSet_of_livePrefix hlife.symm.le (fun q hq => (hvals q hq).symm)

/-- The same stopped match preserves the literal rational crossing event,
including the unsuccessful and zero-lifetime cases. -/
theorem liveCrossing_iff_codeSample_of_isStopDrvMatch {p : PCode × ℝ≥0∞}
    (hp : IsGoodDrvCode p) {W : ℝ≥0 → ℝ} {e : ℝ≥0∞}
    (hc : ContinuousOn W {t | (t : ℝ≥0∞) < e}) (hm : IsStopDrvMatch p W e)
    {a : ℝ} {z : DriverRecord} (hze : z.1 ≤ e)
    (hread : ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < z.1 → z.2 q = a + W q) :
    (∃ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < z.1 ∧ 2 < z.2 q) ↔
      ∃ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < (codeSample a z.1 p).1 ∧
        2 < (codeSample a z.1 p).2 q := by
  obtain ⟨hlife, hvals⟩ := codeSample_liveRead_of_isStopDrvMatch hp hc hm hze hread
  simp only [hlife]
  constructor <;> rintro ⟨q, hq, hY⟩
  · exact ⟨q, hq, by rwa [hvals q hq]⟩
  · exact ⟨q, hq, by rwa [hvals q hq] at hY⟩

end InteractingSLE.Theorem14.GW2JDetR10
