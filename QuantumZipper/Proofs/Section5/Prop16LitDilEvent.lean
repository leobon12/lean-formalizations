import QuantumZipper.Proofs.Section5.Prop16LitDilS
import QuantumZipper.Proofs.LQG.IndepParams
import QuantumZipper.Proofs.Zipper.Cor15LastPair

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Proposition 1.6, literal form: a Borel event forcing the dilation clause (D98)

`DilGood γ Z r s`: the countable condition `GoodA` for the rescaled field `Z(s·) + Q log s` on
`B(0, r/s) ∩ ℍ`, and, for each cutoff test function `F`, a common limit of its approximations
against `F` and of those of `Z` against `F(· / s)`. For a measurable family and a measurable
positive scale it is a Borel event (`measurableSet_dilGood`). Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Function Metric
open scoped Topology ENNReal

namespace QuantumZipper
namespace Prop16Lit

open ExA

/-- **The countable dilation condition.** -/
def DilGood (γ : ℝ) (Z : FieldSample) (r s : ℝ) : Prop :=
  GoodA γ (rescale Z (Qc γ) s) (r / s) ∧
    ∀ n : ℕ, ∀ g ∈ famF, ∃ l,
      Tendsto (fun k => ∫ z, hbCut (r / s) n z * g z ∂areaApprox γ (rescale Z (Qc γ) s) k) atTop
        (𝓝 l) ∧
      Tendsto (fun k => ∫ z, hbCut (r / s) n (z / s) * g (z / s) ∂areaApprox γ Z k) atTop (𝓝 l)

variable {α : Type*} [MeasurableSpace α]

/-- Joint measurability of the circle averages of a rescaled measurable family. -/
theorem measurable_avgReg_rescale_fam {Z : α → FieldSample} (hZ : Measurable Z) {S : α → ℝ}
    (hS : Measurable S) (hS0 : ∀ q, 0 < S q) (Q : ℝ) (k : ℕ) :
    Measurable fun p : α × ℂ => avgReg (rescale (Z p.1) Q (S p.1)) k p.2 := by
  have e : (fun p : α × ℂ => avgReg (rescale (Z p.1) Q (S p.1)) k p.2) = fun p =>
      limUnder atTop fun n : ℕ => evalReg (Z p.1) (foldedCircle
        (foldH ((S p.1 : ℂ) * dyadicRoundC n p.2)) (S p.1 * radius k)) + Q * Real.log (S p.1) := by
    funext p
    unfold avgReg
    congr 1
    funext n
    exact Thm18Asm.G1.rescale_fc_apply (Z p.1) Q (hS0 p.1) _ _
  rw [e]
  refine (StronglyMeasurable.limUnder fun n => ?_).measurable
  have hSc : Measurable fun p : α × ℂ => (S p.1 : ℂ) :=
    Complex.measurable_ofReal.comp (hS.comp measurable_fst)
  have hc : Measurable fun p : α × ℂ =>
      (foldH ((S p.1 : ℂ) * dyadicRoundC n p.2), S p.1 * radius k) :=
    (measurable_foldH.comp (hSc.mul ((Cor15Group.measurable_dyadicRoundC' n).comp
      measurable_snd))).prodMk ((hS.comp measurable_fst).mul_const _)
  exact ((IndepParams.measurable_evalReg_fc₂.comp ((hZ.comp measurable_fst).prodMk hc)).add
    (measurable_const.mul (Real.measurable_log.comp (hS.comp measurable_fst)))).stronglyMeasurable

/-- Test integrals against the approximations, from joint measurability of the averages. -/
theorem measurable_integral_areaApprox_fam' {Z : α → FieldSample} (γ : ℝ) (k : ℕ)
    (hA : Measurable fun p : α × ℂ => avgReg (Z p.1) k p.2) {T : α → ℂ → ℝ}
    (hT : Measurable fun p : α × ℂ => T p.1 p.2) :
    Measurable fun q => ∫ z, T q z ∂areaApprox γ (Z q) k := by
  have e : ∀ q, ∫ z, T q z ∂areaApprox γ (Z q) k =
      ∫ z, E6.areaDensK γ (Z q) k z * T q z ∂(volume.restrict H) :=
    fun q => E6.integral_areaApprox_eq γ (Z q) k _
  simp_rw [e]
  have hd : Measurable fun p : α × ℂ => E6.areaDensK γ (Z p.1) k p.2 := by
    unfold E6.areaDensK
    exact measurable_const.mul (Real.measurable_exp.comp (hA.const_mul γ))
  exact (StronglyMeasurable.integral_prod_right' (f := fun p : α × ℂ =>
    E6.areaDensK γ (Z p.1) k p.2 * T p.1 p.2) (hd.mul hT).stronglyMeasurable).measurable

/-- `goodExA` from joint measurability of the averages. -/
theorem measurableSet_goodExA' {γ : ℝ} {Z : α → FieldSample}
    (hA : ∀ k, Measurable fun p : α × ℂ => avgReg (Z p.1) k p.2) {r : α → ℝ} (hr : Measurable r) :
    MeasurableSet (goodExA γ Z r) := by
  have hsplit : goodExA γ Z r =
      (⋂ m : ℕ, {q | ∀ᶠ k in atTop, areaApprox γ (Z q) k (hbK (r q) m) < ∞}) ∩
      ⋂ n : ℕ, {q | ∀ g ∈ famF, ∃ l, Tendsto (fun k => ∫ z, hbCut (r q) n z * g z
        ∂(areaApprox γ (Z q) k)) atTop (𝓝 l)} := by
    ext q; simp only [goodExA, mem_setOf_eq, mem_inter_iff, mem_iInter]
  rw [hsplit]
  refine MeasurableSet.inter (MeasurableSet.iInter fun m => ?_) (MeasurableSet.iInter fun n => ?_)
  · have hmeas : ∀ k : ℕ, Measurable fun q => areaApprox γ (Z q) k (hbK (r q) m) := by
      intro k
      have hS : MeasurableSet {p : α × ℂ | p.2 ∈ hbK (r p.1) m} :=
        (measurableSet_le (f := fun p : α × ℂ => ‖p.2‖)
          (g := fun p : α × ℂ => r p.1 - 1 / ((m : ℝ) + 1)) (by fun_prop)
          ((hr.comp measurable_fst).sub measurable_const)).inter
          (measurableSet_le measurable_const (Complex.measurable_im.comp measurable_snd))
      have hd : Measurable fun p : α × ℂ => E6.areaDensK γ (Z p.1) k p.2 := by
        unfold E6.areaDensK
        exact measurable_const.mul (Real.measurable_exp.comp ((hA k).const_mul γ))
      have e : ∀ q, areaApprox γ (Z q) k (hbK (r q) m) =
          ∫⁻ z, {p : α × ℂ | p.2 ∈ hbK (r p.1) m}.indicator
            (fun p => ENNReal.ofReal (E6.areaDensK γ (Z p.1) k p.2)) (q, z) ∂(volume.restrict H) := by
        intro q
        have hK : MeasurableSet (hbK (r q) m) := (isCompact_hbK _ _).isClosed.measurableSet
        rw [show areaApprox γ (Z q) k = (volume.restrict H).withDensity
          (fun z => ENNReal.ofReal (E6.areaDensK γ (Z q) k z)) from rfl,
          withDensity_apply _ hK, ← lintegral_indicator hK]
        rfl
      simp_rw [e]
      exact Measurable.lintegral_prod_right' (hd.ennreal_ofReal.indicator hS)
    have hset : {q : α | ∀ᶠ k in atTop, areaApprox γ (Z q) k (hbK (r q) m) < ∞} =
        ⋃ K : ℕ, ⋂ k ≥ K, {q | areaApprox γ (Z q) k (hbK (r q) m) < ∞} := by
      ext q; simp only [eventually_atTop, mem_setOf_eq, mem_iUnion, mem_iInter, ge_iff_le]
    rw [hset]
    exact MeasurableSet.iUnion fun K => MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
      measurableSet_lt (hmeas k) measurable_const
  · have hset : {q : α | ∀ g ∈ famF, ∃ l, Tendsto (fun k => ∫ z, hbCut (r q) n z * g z
        ∂(areaApprox γ (Z q) k)) atTop (𝓝 l)} = ⋂ g ∈ famF, {q | ∃ l, Tendsto (fun k =>
        ∫ z, hbCut (r q) n z * g z ∂(areaApprox γ (Z q) k)) atTop (𝓝 l)} := by
      ext q; simp only [mem_setOf_eq, mem_iInter]
    rw [hset]
    refine MeasurableSet.biInter famF_countable fun g hg => ?_
    have hgm : Measurable g := (famF_dense.1 g hg).1.measurable
    refine StronglyMeasurable.measurableSet_exists_tendsto fun k => ?_
    refine (measurable_integral_areaApprox_fam' γ k (hA k)
      (T := fun q z => hbCut (r q) n z * g z) ?_).stronglyMeasurable
    unfold hbCut
    have h1 : Measurable fun p : α × ℂ => r p.1 := hr.comp measurable_fst
    exact (measurable_const.min (measurable_const.max ((measurable_const.mul
      ((h1.sub (measurable_snd.norm)).min (Complex.measurable_im.comp measurable_snd))).sub
      measurable_const))).mul (hgm.comp measurable_snd)

end Prop16Lit
end QuantumZipper
