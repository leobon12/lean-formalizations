/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2JDetR4Map
import InteractingSLE.Spec.Supplement.GW2JDetR3Cut
import InteractingSLE.Spec.Supplement.GB6LineL4

/-!
# Borel physical drivers from the two GW2 records

The physical capacity rule selects a relative hull. Its inverse chart image
is read by the total mapping-out reader and the existing driver quotient.
All functions are measurable on the entire product of record spaces.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H fwdHull)
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2JDetR4

open Exist.StagedLaw Supp8.GB6LineL GW2JDetR3 Sec7.Lemma71C

/-- A total driver readout from a hull history. -/
def hullDriverRead (A : ℝ≥0 → Set ℂ) (s : ℝ≥0) : ℝ :=
  if s = 0 then 0 else limUnder atTop fun N : ℕ => limUnder atTop fun k : ℕ =>
    (hullMapRead (A s) (zPt N) - 2 / (((k : ℂ) + 1) *
      (hullMapRead (A s) (zPt N) -
        hullMapRead (A ((s : ℝ) - 1 / ((k : ℝ) + 1)).toNNReal) (zPt N)))).re

theorem measurable_hullDriverRead {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {A : ℝ≥0 → Ω → Set ℂ} (hA : ∀ r, Measurable[mΩ, hittingSigma] (A r))
    (s : ℝ≥0) : Measurable fun ω => hullDriverRead (fun r => A r ω) s := by
  classical
  by_cases hs : s = 0
  · simp only [hullDriverRead, hs, ↓reduceIte]
    exact measurable_const
  simp only [hullDriverRead, hs, ↓reduceIte]
  apply StronglyMeasurable.measurable
  apply StronglyMeasurable.limUnder
  intro N
  apply StronglyMeasurable.limUnder
  intro k
  have h1 := (measurable_hullMapRead (zPt N)).comp (hA s)
  have h2 := (measurable_hullMapRead (zPt N)).comp
    (hA ((s : ℝ) - 1 / ((k : ℝ) + 1)).toNNReal)
  exact (Complex.measurable_re.comp (h1.sub
    (measurable_const.div (measurable_const.mul (h1.sub h2))))).stronglyMeasurable

/-- The total reader recovers an actual continuous Loewner driver. -/
theorem hullDriverRead_eq_of_prefix {A : ℝ≥0 → Set ℂ} {w : ℝ → ℝ}
    (hw : Continuous w) (hw0 : w 0 = 0) {s : ℝ≥0}
    (hA : ∀ r ≤ s, A r = fwdHull w r) : hullDriverRead A s = w s := by
  have he : hullDriverRead A s = Sec5.CrossCond.Gen.hullDriver A s := by
    classical
    by_cases hs : s = 0
    · simp only [hullDriverRead, Sec5.CrossCond.Gen.hullDriver, hs, ↓reduceIte]
    have hmap : ∀ r ≤ s, ∀ z, hullMapRead (A r) z =
        Sec5.CrossCond.Gen.hullMap A r z := by
      intro r hr z
      exact hullMapRead_eq (hA r hr ▸ isHPHull_fwdHull hw r.coe_nonneg) z
    have hr : ∀ k : ℕ, ((s : ℝ) - 1 / ((k : ℝ) + 1)).toNNReal ≤ s := by
      intro k
      apply Real.toNNReal_le_iff_le_coe.2
      have : 0 ≤ 1 / ((k : ℝ) + 1) := by positivity
      linarith
    simp only [hullDriverRead, Sec5.CrossCond.Gen.hullDriver, hs, ↓reduceIte,
      Sec5.CrossCond.Gen.hullQuot, hmap s le_rfl, hmap _ (hr _)]
  exact he.trans (Sec5.CrossCond.Gen.hullDriver_eq_of_prefix hw hw0 hA)

/-- The record driver's hull remains hitting-measurable at a random time. -/
theorem measurable_fwdHull_rdrv_time {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {r : Ω → RecData} (hr : Measurable r) {q : Ω → ℝ≥0} (hq : Measurable q) :
    Measurable[mΩ, hittingSigma] fun ω => fwdHull (rdrv (r ω)) (q ω) := by
  refine measurable_generateFrom ?_
  rintro _ ⟨U, hU, _hUH, rfl⟩
  have hcont : ∀ ω, Continuous fun t : ℝ≥0 => rdrv (r ω) t :=
    fun ω => (continuous_rdrv _).comp NNReal.continuous_coe
  have hm : ∀ t : ℝ≥0, Measurable fun ω => rdrv (r ω) t :=
    fun t => (measurable_rdrv_apply t).comp hr
  have hd : MeasurableSet {ω | Disjoint (fwdHull (rdrv (r ω)) (q ω)) U} := by
    have he : {ω | Disjoint (fwdHull (rdrv (r ω)) (q ω)) U} =
        ⋂ p : ℚ × ℚ × ℚ, ⋂ (_ : 0 < p.2.2),
        ⋂ (_ : closedBall ((p.1 : ℂ) + (p.2.1 : ℂ) * Complex.I) (p.2.2 : ℝ) ⊆ U),
          {ω | Disjoint
            (closedBall ((p.1 : ℂ) + (p.2.1 : ℂ) * Complex.I) (p.2.2 : ℝ))
            (fwdHull (rdrv (r ω)) (q ω))} := by
      ext ω
      simp only [mem_ofPred_eq, mem_iInter]
      exact disjoint_iff_forall_posRatDisc hU
    rw [he]
    refine MeasurableSet.iInter fun p => MeasurableSet.iInter fun _ =>
      MeasurableSet.iInter fun _ => ?_
    have h := measurableSet_disjoint_fwdHull_rand hcont hm
      (measurable_coe_nnreal_real.comp hq) (fun ω => (q ω).coe_nonneg)
      (D := closedBall ((p.1 : ℂ) + (p.2.1 : ℂ) * Complex.I) (p.2.2 : ℝ))
      isClosed_closedBall
    have heDrive : QuantumZipper.drive 1 (fun t ω => rdrv (r ω) t) =
        fun ω => rdrv (r ω) := by
      funext ω x
      simp only [QuantumZipper.drive, Real.sqrt_one, one_mul, rdrv, Real.toNNReal_coe]
    rw [heDrive] at h
    exact h
  convert hd.compl using 1
  ext ω
  simp only [mem_preimage, mem_ofPred_eq, mem_compl_iff,
    not_disjoint_iff_nonempty_inter]

/-- The physical hull selected by the Borel inverse-capacity clock. -/
def physicalHullRead (s t : ℝ≥0) (p : RecData × RecData) : Set ℂ :=
  inverseHull s (capacityCut s t p).toNNReal p

theorem measurable_physicalHullRead (s t : ℝ≥0) :
    Measurable[_, hittingSigma] (physicalHullRead s t) := by
  apply measurable_image_relInv s measurable_fst
  · exact measurable_fwdHull_rdrv_time measurable_snd
      (measurable_capacityCut s t).ennreal_toNNReal
  · intro p
    exact (isHPHull_fwdHull (continuous_rdrv _) (NNReal.coe_nonneg _)).1

/-- The physical driver read from a retained counterflow record and buffer. -/
def physicalDriverRead (s t : ℝ≥0) (p : RecData × RecData) : ℝ :=
  hullDriverRead (fun r => physicalHullRead s r p) t

theorem measurable_physicalDriverRead (s t : ℝ≥0) : Measurable (physicalDriverRead s t) :=
  measurable_hullDriverRead (measurable_physicalHullRead s) t

end InteractingSLE.Theorem14.GW2JDetR4
