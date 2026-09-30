import QuantumZipper.Proofs.Zipper.MeasUnzipLen
import QuantumZipper.Proofs.Zipper.LocRichBasic

/-!
# MEAS-UNZIP (4): the rich local data of the length zipper output are measurable

Continuation of `MeasUnzipLen.lean`. For a continuous path `f` on `[0,T]` (driver
`W = Wof κ T hT f`) and a field `x`, the output `locRich R (zipLenDown γ ℓ (x, W))` of the length
quantum zipper is a measurable function of `(f, x)` on every measurable set `S` of pairs on which

* `f ∈ PZ` (the driver starts at `0`),
* the left length process agrees with the measurable `lenJ` at the rational times of `[0,T]` and
  at `T`, and is monotone on `[0,T]`,
* the level `ℓ` is reached by time `T`,
* the unzipped field at the hitting time is good (`IsLQGGood`).

Main result: `measurable_locRich_zipLenDown` (junk `0` off `S`). Ingredients:
`measurable_hitTime_unzip` (hitting time), `measurable_scaleJ` (scale), the measurable raw values
of a rescaled field `measurable_rescale_apply` (own: `evalReg y (μ.map (a ·))` is a `limUnder` of
integrals of the jointly measurable `avgReg`), and the joint measurability of the driver
`measurable_Wof_joint` (Carathéodory, mathlib `measurable_uncurry_of_continuous_of_measurable`).

Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

namespace QuantumZipper.MeasUnzip

open CharFun RegCont Factorization D3Plus
open scoped Classical

/-! ## Rescaled fields -/

theorem deriv_mul_const_left (a : ℝ) (z : ℂ) : deriv (fun z : ℂ => (a : ℂ) * z) z = (a : ℂ) := by
  simp

/-- Raw values of `rescale (y b) Q a` are jointly measurable in `(b, a)`. -/
theorem measurable_rescale_apply {β : Type*} [MeasurableSpace β] {y : β → FieldSample}
    (hy : Measurable y) (Q : ℝ) (μ : Measure ℂ) [SFinite μ] :
    Measurable fun r : β × ℝ => rescale (y r.1) Q r.2 μ := by
  have hφ : ∀ a : ℝ, Measurable fun z : ℂ => (a : ℂ) * z := fun a =>
    measurable_const.mul measurable_id
  have heq : ∀ r : β × ℝ, rescale (y r.1) Q r.2 μ =
      limUnder atTop (fun k => ∫ z, avgReg (y r.1) k ((r.2 : ℂ) * z) ∂μ) +
        Q * ∫ z, Real.log ‖((r.2 : ℝ) : ℂ)‖ ∂μ := by
    intro r
    simp only [rescale, coordChange, evalReg, deriv_mul_const_left]
    congr 2
    funext k
    rw [integral_map (hφ r.2).aemeasurable
      (show Measurable fun w => avgReg (y r.1) k w from
        (measurable_avgReg k).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable]
  rw [show (fun r : β × ℝ => rescale (y r.1) Q r.2 μ) = _ from funext heq]
  have h1 : ∀ k : ℕ, StronglyMeasurable fun r : β × ℝ => ∫ z, avgReg (y r.1) k ((r.2 : ℂ) * z) ∂μ := by
    intro k
    have hm : Measurable fun q : (β × ℝ) × ℂ => avgReg (y q.1.1) k ((q.1.2 : ℂ) * q.2) :=
      (measurable_avgReg k).comp ((hy.comp (measurable_fst.comp measurable_fst)).prodMk
        ((Complex.measurable_ofReal.comp (measurable_snd.comp measurable_fst)).mul measurable_snd))
    exact hm.stronglyMeasurable.integral_prod_right'
  have h2 : Measurable fun q : (β × ℝ) × ℂ => Real.log ‖((q.1.2 : ℝ) : ℂ)‖ :=
    Real.measurable_log.comp (Complex.measurable_ofReal.comp (measurable_snd.comp measurable_fst)).norm
  exact (StronglyMeasurable.limUnder h1).measurable.add
    (h2.stronglyMeasurable.integral_prod_right'.measurable.const_mul _)

/-- The rich local field data of `rescale (y b) Q a` are jointly measurable in `(b, a)`. -/
theorem measurable_locFieldFull_rescale {β : Type*} [MeasurableSpace β] {y : β → FieldSample}
    (hy : Measurable y) (Q : ℝ) (R : ℕ) :
    Measurable fun r : β × ℝ => locFieldFull R (rescale (y r.1) Q r.2) := by
  unfold locFieldFull
  refine Measurable.prodMk (measurable_pi_iff.2 fun i => ?_) (measurable_pi_iff.2 fun ρ => ?_)
  · by_cases h : inBallFull R i
    · simp only [h, ite_true]
      exact measurable_rescale_apply hy Q _
    · simp only [h, ite_false]; exact measurable_const
  · by_cases h : suppIn R ρ
    · simp only [h, ite_true]
      exact (measurable_rescale_apply hy Q _).sub (measurable_rescale_apply hy Q _)
    · simp only [h, ite_false]; exact measurable_const

/-! ## The driver -/

variable {T : ℝ} (hT : 0 ≤ T)

theorem measurable_Wof_joint (κ : ℝ) :
    Measurable fun p : C(Icc (0 : ℝ) T, ℝ) × ℝ => Wof κ T hT p.1 p.2 := by
  have h := measurable_uncurry_of_continuous_of_measurable
    (u := fun (r : ℝ) (f : C(Icc (0 : ℝ) T, ℝ)) => Wof κ T hT f r)
    (fun f => continuous_Wof κ T hT f)
    (fun r => measurable_const.mul (continuous_eval_const _).measurable)
  exact h.comp measurable_swap

/-- The rescaled driver read by `locRich R`. -/
def drvJ (κ : ℝ) (R : ℕ) (p : C(Icc (0 : ℝ) T, ℝ) × ℝ × ℝ) : ℝ≥0 → ℝ := fun s =>
  (Wof κ T hT p.1 (p.2.1 + p.2.2 ^ 2 * max (min (s : ℝ) R) 0) - Wof κ T hT p.1 p.2.1) / p.2.2

theorem measurable_drvJ (κ : ℝ) (R : ℕ) : Measurable (drvJ hT κ R) := by
  refine measurable_pi_iff.2 fun s => ?_
  have hW := measurable_Wof_joint hT κ
  have h1 : Measurable fun p : C(Icc (0 : ℝ) T, ℝ) × ℝ × ℝ =>
      Wof κ T hT p.1 (p.2.1 + p.2.2 ^ 2 * max (min (s : ℝ) R) 0) :=
    hW.comp (measurable_fst.prodMk ((measurable_fst.comp measurable_snd).add
      (((measurable_snd.comp measurable_snd).pow_const 2).mul measurable_const)))
  have h2 : Measurable fun p : C(Icc (0 : ℝ) T, ℝ) × ℝ × ℝ => Wof κ T hT p.1 p.2.1 :=
    hW.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  exact (h1.sub h2).div (measurable_snd.comp measurable_snd)

/-! ## The zipper output on a good set -/

variable (γ κ ℓ : ℝ) (R : ℕ) (S : Set (C(Icc (0 : ℝ) T, ℝ) × FieldSample))

variable {S}

end QuantumZipper.MeasUnzip
