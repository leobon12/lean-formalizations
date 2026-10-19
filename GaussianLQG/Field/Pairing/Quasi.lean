import GaussianLQG.Field.Pairing.Basic
import QuantumZipper.Proofs.Probability.CameronMartin
import LQGDimension.Existence.AssemblyAux1

/-!
# Symmetry and quasi-invariance of the coordinate measure (blueprint Lemma `lem:field`(c))

* `stdP_map_neg`: `ℙ` is invariant under `ω ↦ -ω`; it maps `(h, μ)` to `-(h, μ)` on `Ω_μ`
  (`pairing_neg`).
* `stdP_map_shiftBy`: for finitely supported `v`, the law of `ω + v` is
  `exp(∑_j v_j ω_j - ½ ∑_j v_j²) · ℙ` (Cameron–Martin, from
  `QuantumZipper.CameronMartin.map_tiltMeasure_path` applied to the coordinate process);
  hence it is mutually absolutely continuous with `ℙ` (`map_shiftBy_absolutelyContinuous`,
  `absolutelyContinuous_map_shiftBy`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace GaussianLQG

open Realization

variable {e : ℕ → ℂ → ℝ} {μ : Measure ℂ}

/-! ## Symmetry -/

/-- **Lemma `lem:field`(c)**: `ℙ` is invariant under `ω ↦ -ω`. -/
theorem stdP_map_neg : stdP.map (fun ω : Coord => -ω) = stdP := by
  have h := Measure.infinitePi_map_pi (μ := fun _ : ℕ => gaussianReal 0 1)
    (f := fun _ (x : ℝ) => -x) (fun _ => measurable_neg)
  simp only [gaussianReal_map_neg, neg_zero] at h
  exact h

theorem psum_neg (a : ℕ → ℝ) (n : ℕ) (ω : Coord) : psum a n (-ω) = -psum a n ω := by
  unfold psum
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun k _ => by rw [Pi.neg_apply, neg_mul]

/-- **Lemma `lem:field`(c)**: `ω ↦ -ω` maps `(h, μ)` to `-(h, μ)` on `Ω_μ`. -/
theorem pairing_neg {ω : Coord} (hω : ω ∈ pairingSet e μ) :
    pairing e μ (-ω) = -pairing e μ ω := by
  refine pairing_eq_of_tendsto (((tendsto_pairing_of_mem hω).neg).congr fun n => ?_)
  rw [← psum_frameCoef, ← psum_frameCoef, psum_neg]

/-! ## Cameron–Martin for finitely supported shifts -/

open QuantumZipper.CameronMartin

/-- The coordinate process `j ↦ ω_j`. -/
abbrev coordProc : ℕ → Coord → ℝ := fun j ω => ω j

theorem isGaussianProcess_coordProc : IsGaussianProcess coordProc stdP where
  hasGaussianLaw I :=
    iIndepFun.hasGaussianLaw (X := fun (i : I) (ω : Coord) => ω i)
      (fun i => LQGDimension.ExistAsm.hasGaussianLaw_eval i)
      (LQGDimension.ExistAsm.iIndepFun_eval.precomp Subtype.val_injective)

theorem covK_coordProc (i j : ℕ) : covK coordProc stdP i j = if i = j then 1 else 0 := by
  unfold covK
  split_ifs with h
  · subst h
    rw [covariance_self (measurable_pi_apply i).aemeasurable]
    exact LQGDimension.ExistAsm.variance_eval i
  · exact (LQGDimension.ExistAsm.iIndepFun_eval.indepFun h).covariance_eq_zero
      (LQGDimension.ExistAsm.hasGaussianLaw_eval i).memLp_two
      (LQGDimension.ExistAsm.hasGaussianLaw_eval j).memLp_two

theorem covShift_coordProc (v : ℕ →₀ ℝ) (j : ℕ) : covShift coordProc stdP v j = v j := by
  unfold covShift
  simp_rw [covK_coordProc, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · exact (Finsupp.notMem_support_iff.1 h).symm

theorem covNorm_coordProc (v : ℕ →₀ ℝ) :
    covNorm coordProc stdP v = ∑ j ∈ v.support, v j ^ 2 := by
  unfold covNorm
  simp_rw [covShift_coordProc, sq]

/-- The Cameron–Martin density `exp(∑_j v_j ω_j - ½ ∑_j v_j²)` of the shift by `v`. -/
def cmDensity (v : ℕ →₀ ℝ) (ω : Coord) : ℝ :=
  Real.exp (∑ j ∈ v.support, v j * ω j - (∑ j ∈ v.support, v j ^ 2) / 2)

theorem cmDensity_pos (v : ℕ →₀ ℝ) (ω : Coord) : 0 < cmDensity v ω := Real.exp_pos _

theorem measurable_cmDensity (v : ℕ →₀ ℝ) : Measurable (cmDensity v) := by
  unfold cmDensity
  refine Real.measurable_exp.comp (Measurable.sub_const ?_ _)
  exact Finset.measurable_sum _ fun j _ => (measurable_pi_apply j).const_mul _

/-- **Lemma `lem:field`(c)** (Cameron–Martin): the law of `ω + v` is
`exp(∑_j v_j ω_j - ½ ∑_j v_j²) · ℙ`. -/
theorem stdP_map_shiftBy (v : ℕ →₀ ℝ) :
    stdP.map (fun ω => shiftBy ω v) =
      stdP.withDensity fun ω => ENNReal.ofReal (cmDensity v ω) := by
  have h := map_tiltMeasure_path isGaussianProcess_coordProc (fun j => measurable_pi_apply j)
    (fun j => LQGDimension.ExistAsm.integral_eval j) v
  simp only [covShift_coordProc] at h
  have h1 : (fun (ω : Coord) (j : ℕ) => coordProc j ω) = id := rfl
  rw [h1, Measure.map_id] at h
  have h2 : (fun (ω : Coord) (j : ℕ) => coordProc j ω + v j) = fun ω => shiftBy ω v := rfl
  rw [h2] at h
  rw [← h]
  unfold tiltMeasure tiltDensity cmDensity
  rw [covNorm_coordProc]
  rfl

/-- The law of `ω + v` is absolutely continuous with respect to `ℙ`. -/
theorem map_shiftBy_absolutelyContinuous (v : ℕ →₀ ℝ) :
    stdP.map (fun ω => shiftBy ω v) ≪ stdP := by
  rw [stdP_map_shiftBy]
  exact withDensity_absolutelyContinuous _ _

/-- `ℙ` is absolutely continuous with respect to the law of `ω + v`. -/
theorem absolutelyContinuous_map_shiftBy (v : ℕ →₀ ℝ) :
    stdP ≪ stdP.map (fun ω => shiftBy ω v) := by
  rw [stdP_map_shiftBy]
  exact withDensity_absolutelyContinuous'
    (ENNReal.measurable_ofReal.comp (measurable_cmDensity v)).aemeasurable
    (ae_of_all _ fun ω => (ENNReal.ofReal_pos.2 (cmDensity_pos v ω)).ne')

end GaussianLQG
