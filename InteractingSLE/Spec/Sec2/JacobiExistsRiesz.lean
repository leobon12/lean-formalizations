/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.JacobiExistsFunctional
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.UnitInterval
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# The stationary Jacobi law on the path space `ℝ → [0, 1]` (Riesz–Markov)

Packet PROVE-YW-JACOBI. The path space `PathSpace = ℝ → [0, 1]` with the product topology is compact
Hausdorff (Tychonoff); it carries the Borel σ-algebra. The polynomial functions of finitely many
coordinates (`evalC : MvPolynomial ℝ ℝ →ₐ[ℝ] C(PathSpace, ℝ)`) are dense (Stone–Weierstrass), and the
moment functional `lam κ a b` of `JacobiExistsFunctional.lean` satisfies `|lam F| ≤ ‖evalC F‖`
(positivity). It therefore extends to a positive normalized functional on `C(PathSpace, ℝ)`
(`LinearMap.extendOfNorm`), and the Riesz–Markov–Kakutani theorem gives a probability measure
`pathMeasure` with

  `∫ F(ω_{t₁}, …, ω_{t_k}) d(pathMeasure) = lam F`   (`integral_eval_pathMeasure`)

for every polynomial `F`. This replaces the Kolmogorov extension theorem (compact state space).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology

namespace InteractingSLE

namespace Sec2

namespace JacobiExists

/-- The path space `ℝ → [0, 1]` (product topology, Borel σ-algebra). -/
def PathSpace : Type := ℝ → unitInterval

instance : TopologicalSpace PathSpace := inferInstanceAs (TopologicalSpace (ℝ → unitInterval))
instance : CompactSpace PathSpace := inferInstanceAs (CompactSpace (ℝ → unitInterval))
instance : T2Space PathSpace := inferInstanceAs (T2Space (ℝ → unitInterval))
instance : MeasurableSpace PathSpace := borel PathSpace
instance : BorelSpace PathSpace := ⟨rfl⟩

/-- The real configuration `t ↦ ω t` of a path. -/
def toConfig (ω : PathSpace) : ℝ → ℝ := fun t => ((ω : ℝ → unitInterval) t : ℝ)

theorem inCube_toConfig (ω : PathSpace) : InCube (toConfig ω) := fun t =>
  ((ω : ℝ → unitInterval) t).2

/-- Every configuration of the cube is the configuration of a path. -/
theorem exists_toConfig_eq {y : ℝ → ℝ} (hy : InCube y) : ∃ ω : PathSpace, toConfig ω = y :=
  ⟨fun t => ⟨y t, hy t⟩, rfl⟩

theorem continuous_toConfig_apply (t : ℝ) : Continuous fun ω : PathSpace => toConfig ω t :=
  continuous_subtype_val.comp (continuous_apply (A := fun _ : ℝ => unitInterval) t)

/-- The coordinate `ω ↦ ω t` as a continuous function. -/
def coordC (t : ℝ) : C(PathSpace, ℝ) := ⟨fun ω => toConfig ω t, continuous_toConfig_apply t⟩

/-- Polynomials in the coordinates. -/
def evalC : MvPolynomial ℝ ℝ →ₐ[ℝ] C(PathSpace, ℝ) := MvPolynomial.aeval coordC

theorem evalC_apply (F : MvPolynomial ℝ ℝ) (ω : PathSpace) :
    evalC F ω = MvPolynomial.eval (toConfig ω) F := by
  induction F using MvPolynomial.induction_on with
  | C c => simp [evalC]
  | add p q hp hq => simp only [map_add, ContinuousMap.add_apply, hp, hq]
  | mul_X p n hp =>
    rw [map_mul, ContinuousMap.mul_apply, hp, map_mul, MvPolynomial.eval_X]
    simp only [evalC, MvPolynomial.aeval_X]
    rfl

theorem denseRange_evalC : DenseRange (evalC : MvPolynomial ℝ ℝ → C(PathSpace, ℝ)) := by
  have hsep : (evalC.range : Subalgebra ℝ C(PathSpace, ℝ)).SeparatesPoints := by
    intro ω ω' hne
    obtain ⟨t, ht⟩ : ∃ t, (ω : ℝ → unitInterval) t ≠ (ω' : ℝ → unitInterval) t := by
      by_contra h
      push Not at h
      exact hne (funext h)
    refine ⟨coordC t, ⟨coordC t, ⟨MvPolynomial.X t, by simp [evalC]⟩, rfl⟩, ?_⟩
    intro h
    exact ht (Subtype.ext h)
  have htop := ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints _ hsep
  have hcl : closure (evalC.range : Set C(PathSpace, ℝ)) = univ := by
    rw [← Subalgebra.topologicalClosure_coe, htop, Algebra.coe_top]
  rw [DenseRange, dense_iff_closure_eq, ← AlgHom.coe_range]
  exact hcl

variable {κ a b : ℝ}

/-- `|lam F| ≤ ‖evalC F‖`. -/
theorem abs_lam_le (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b) (F : MvPolynomial ℝ ℝ) :
    |lam κ a b F| ≤ ‖evalC F‖ := by
  set M := ‖evalC F‖
  have hb' : ∀ y, InCube y → |MvPolynomial.eval y F| ≤ M := by
    intro y hy
    obtain ⟨ω, rfl⟩ := exists_toConfig_eq hy
    rw [← evalC_apply, ← Real.norm_eq_abs]
    exact ContinuousMap.norm_coe_le_norm _ ω
  have hC : ∀ c : ℝ, lam κ a b (MvPolynomial.C c) = c := by
    intro c
    rw [MvPolynomial.C_eq_smul_one, lam_smul hκ ha hb, lam_one, mul_one]
  have h1 := lam_nonneg hκ ha hb (F := MvPolynomial.C M - F) fun y hy => by
    simp only [map_sub, MvPolynomial.eval_C]
    linarith [le_abs_self (MvPolynomial.eval y F), hb' y hy]
  have h2 := lam_nonneg hκ ha hb (F := MvPolynomial.C M + F) fun y hy => by
    simp only [map_add, MvPolynomial.eval_C]
    linarith [neg_abs_le (MvPolynomial.eval y F), hb' y hy]
  rw [sub_eq_add_neg, lam_add hκ ha hb, hC, ← neg_one_smul ℝ F, lam_smul hκ ha hb] at h1
  rw [lam_add hκ ha hb, hC] at h2
  exact abs_le.2 ⟨by linarith, by linarith⟩

variable (κ a b) in
/-- The extension of the moment functional to `C(PathSpace, ℝ)`. -/
def lamExt (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b) : C(PathSpace, ℝ) →L[ℝ] ℝ :=
  (lamL κ a b hκ ha hb).extendOfNorm evalC.toLinearMap

theorem lamExt_evalC (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b) (F : MvPolynomial ℝ ℝ) :
    lamExt κ a b hκ ha hb (evalC F) = lam κ a b F :=
  LinearMap.extendOfNorm_eq denseRange_evalC ⟨1, fun F => by
    rw [one_mul]; exact abs_lam_le hκ ha hb F⟩ F

theorem norm_lamExt_le (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b) (f : C(PathSpace, ℝ)) :
    ‖lamExt κ a b hκ ha hb f‖ ≤ ‖f‖ := by
  have := LinearMap.norm_extendOfNorm_apply_le (f := lamL κ a b hκ ha hb)
    (e := evalC.toLinearMap) denseRange_evalC 1 (fun F => by
      rw [one_mul]; exact abs_lam_le hκ ha hb F) f
  rwa [one_mul] at this

theorem lamExt_one (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b) : lamExt κ a b hκ ha hb 1 = 1 := by
  have := lamExt_evalC hκ ha hb 1
  rwa [map_one, lam_one] at this

theorem lamExt_nonneg (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b) {f : C(PathSpace, ℝ)} (hf : 0 ≤ f) :
    0 ≤ lamExt κ a b hκ ha hb f := by
  set c := ‖f‖
  have hc : 0 ≤ c := norm_nonneg _
  have hle : ‖c • (1 : C(PathSpace, ℝ)) - f‖ ≤ c := by
    refine (ContinuousMap.norm_le _ hc).2 fun ω => ?_
    have h0 : 0 ≤ f ω := hf ω
    have h1 : f ω ≤ c := (le_abs_self _).trans (ContinuousMap.norm_coe_le_norm f ω)
    simp only [ContinuousMap.sub_apply, ContinuousMap.smul_apply, ContinuousMap.one_apply,
      smul_eq_mul, mul_one, Real.norm_eq_abs]
    rw [abs_le]
    constructor <;> linarith
  have h := (le_abs_self _).trans ((norm_lamExt_le hκ ha hb _).trans hle)
  rw [map_sub, map_smul, lamExt_one, smul_eq_mul, mul_one] at h
  linarith

variable (κ a b) in
/-- The positive functional on `C_c(PathSpace, ℝ)`. -/
def lamPos (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b) :
    CompactlySupportedContinuousMap PathSpace ℝ →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀
    { toFun := fun f => lamExt κ a b hκ ha hb f.toContinuousMap
      map_add' := fun f g => by
        rw [← map_add]; rfl
      map_smul' := fun c f => by
        rw [RingHom.id_apply, ← map_smul]; rfl }
    (fun f hf => lamExt_nonneg hκ ha hb fun ω => hf ω)

variable (κ a b) in
/-- **The stationary Jacobi law on the path space.** -/
def pathMeasure (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b) : Measure PathSpace :=
  RealRMK.rieszMeasure (lamPos κ a b hκ ha hb)

theorem integral_pathMeasure_continuousMap (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b)
    (f : C(PathSpace, ℝ)) : ∫ ω, f ω ∂(pathMeasure κ a b hκ ha hb) = lamExt κ a b hκ ha hb f := by
  have := RealRMK.integral_rieszMeasure (lamPos κ a b hκ ha hb)
    (CompactlySupportedContinuousMap.continuousMapEquiv f)
  exact this

instance isProbabilityMeasure_pathMeasure (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b) :
    IsProbabilityMeasure (pathMeasure κ a b hκ ha hb) := by
  have h := integral_pathMeasure_continuousMap hκ ha hb 1
  rw [lamExt_one] at h
  simp only [ContinuousMap.one_apply, integral_const, smul_eq_mul, mul_one] at h
  constructor
  rw [Measure.real, ENNReal.toReal_eq_one_iff] at h
  exact h

/-- **The moments of the path measure.** -/
theorem integral_eval_pathMeasure (hκ : 0 < κ) (ha : 0 < a) (hb : 0 < b) (F : MvPolynomial ℝ ℝ) :
    ∫ ω, MvPolynomial.eval (toConfig ω) F ∂(pathMeasure κ a b hκ ha hb) = lam κ a b F := by
  have h := integral_pathMeasure_continuousMap hκ ha hb (evalC F)
  rw [lamExt_evalC] at h
  rw [← h]
  exact integral_congr_ae (ae_of_all _ fun ω => (evalC_apply F ω).symm)

theorem continuous_eval_toConfig (F : MvPolynomial ℝ ℝ) :
    Continuous fun ω : PathSpace => MvPolynomial.eval (toConfig ω) F := by
  have : (fun ω : PathSpace => MvPolynomial.eval (toConfig ω) F) = evalC F :=
    funext fun ω => (evalC_apply F ω).symm
  rw [this]
  exact (evalC F).continuous

end JacobiExists

end Sec2

end InteractingSLE
