import QuantumZipper.Proofs.Thm18.ASepGCSkel

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP-GC, part 3: measurability of regularized evaluations along parametrized pushforwards

Generic tools for the Borel exactness input `GC.GCExStmt`:

* `measurable_avgReg_family`: if a family of field samples `Y p` is measurable in `p` at every
  folded circle of radius `2^{-k}`, its regularized averages `avgReg (Y p) k z` are jointly
  measurable in `(p, z)` (through the modified family that is `0` off those circles, which is
  measurable into `FieldSample`, and `measurable_avgReg`).
* `measurable_integral_map_family`: `p ↦ ∫ g p d(σ.map (φ p))` for jointly measurable `g`, `φ`.
* `measurable_evalReg_map_family`: `p ↦ evalReg (Y p) (σ.map (φ p))`.
* `yC v`: a field sample with circle coordinates `v` for every realizable `v ∈ C2`
  (`coordsFull_yC`), measurable in `v` (`measurable_yC`).

Own elementary argument (Fubini-type measurability of parametric integrals, mathlib
`StronglyMeasurable.integral_prod_right'`, and `limUnder` of measurable sequences).
-/

noncomputable section

open MeasureTheory Set Function Filter
open scoped NNReal ENNReal

namespace QuantumZipper
namespace ASep
namespace GC

open Thm18Asm Thm18Asm.G4Core

variable {P : Type*} [MeasurableSpace P]

/-- **Joint measurability of regularized averages of a family.** -/
theorem measurable_avgReg_family (Y : P → FieldSample)
    (hY : ∀ (d : ℂ) (k : ℕ), Measurable fun p => Y p (foldedCircle d (radius k))) (k : ℕ) :
    Measurable fun q : P × ℂ => avgReg (Y q.1) k q.2 := by
  classical
  set Y' : P → FieldSample := fun p μ =>
    if ∃ d : ℂ, ∃ k' : ℕ, μ = foldedCircle d (radius k') then Y p μ else 0 with hY'def
  have hY' : Measurable Y' := by
    refine measurable_pi_iff.2 fun μ => ?_
    by_cases h : ∃ d : ℂ, ∃ k' : ℕ, μ = foldedCircle d (radius k')
    · obtain ⟨d, k', rfl⟩ := h
      simp only [hY'def, if_pos (⟨d, k', rfl⟩ : ∃ d' : ℂ, ∃ k'' : ℕ,
        foldedCircle d (radius k') = foldedCircle d' (radius k''))]
      exact hY d k'
    · simp only [hY'def, if_neg h]
      exact measurable_const
  have e : ∀ p, avgReg (Y' p) k = avgReg (Y p) k := fun p => funext fun z => by
    simp only [avgReg, hY'def]
    congr 1
    funext n
    rw [if_pos ⟨_, k, rfl⟩]
  have h := (measurable_avgReg k).comp ((hY'.comp measurable_fst).prodMk measurable_snd)
  convert h using 1
  funext q
  simp only [Function.comp_apply, e]

/-- Parametric integrals against a parametrized pushforward. -/
theorem measurable_integral_map_family (σ : Measure ℂ) [SFinite σ] (g : P → ℂ → ℝ)
    (hg : Measurable fun q : P × ℂ => g q.1 q.2) (φ : P → ℂ → ℂ)
    (hφ : Measurable fun q : P × ℂ => φ q.1 q.2) :
    Measurable fun p => ∫ z, g p z ∂(σ.map (φ p)) := by
  have hφp : ∀ p, Measurable (φ p) := fun p =>
    hφ.comp (f := fun z : ℂ => (p, z)) (measurable_const.prodMk measurable_id)
  have hgp : ∀ p, Measurable (g p) := fun p =>
    hg.comp (f := fun z : ℂ => (p, z)) (measurable_const.prodMk measurable_id)
  have e : (fun p => ∫ z, g p z ∂(σ.map (φ p))) = fun p => ∫ w, g p (φ p w) ∂σ := by
    funext p
    exact integral_map (hφp p).aemeasurable (hgp p).aestronglyMeasurable
  rw [e]
  have hj : Measurable fun q : P × ℂ => g q.1 (φ q.1 q.2) :=
    hg.comp (measurable_fst.prodMk hφ)
  exact (StronglyMeasurable.integral_prod_right' (f := fun q : P × ℂ => g q.1 (φ q.1 q.2))
    hj.stronglyMeasurable).measurable

/-- **Regularized evaluation along a parametrized pushforward.** -/
theorem measurable_evalReg_map_family (Y : P → FieldSample)
    (hY : ∀ k : ℕ, Measurable fun q : P × ℂ => avgReg (Y q.1) k q.2)
    (σ : Measure ℂ) [SFinite σ] (φ : P → ℂ → ℂ) (hφ : Measurable fun q : P × ℂ => φ q.1 q.2) :
    Measurable fun p => evalReg (Y p) (σ.map (φ p)) := by
  unfold evalReg
  have hk : ∀ k : ℕ, StronglyMeasurable fun p => ∫ w, avgReg (Y p) k w ∂(σ.map (φ p)) :=
    fun k => (measurable_integral_map_family σ (fun p z => avgReg (Y p) k z) (hY k) φ
      hφ).stronglyMeasurable
  exact (StronglyMeasurable.limUnder hk).measurable

/-! ## A measurable field with prescribed circle coordinates -/

open Classical in
/-- A field sample with circle coordinates `v` (for realizable `v`). -/
def yC (v : ℕ → ℝ) : FieldSample := fun μ => if h : ∃ i, fcF i = μ then v (Nat.find h) else 0

theorem measurable_yC : Measurable yC := by
  classical
  refine measurable_pi_iff.2 fun μ => ?_
  by_cases h : ∃ i, fcF i = μ
  · simp only [yC, dif_pos h]; exact measurable_pi_apply _
  · simp only [yC, dif_neg h]; exact measurable_const

theorem coordsFull_yC {v : ℕ → ℝ} (hv : v ∈ C2) : CoordsFull.coordsFull (yC v) = v := by
  classical
  funext i
  have h : ∃ j, fcF j = fcF i := ⟨i, rfl⟩
  show (if h : ∃ j, fcF j = fcF i then v (Nat.find h) else 0) = v i
  rw [dif_pos h]
  exact mem_iInter.1 (mem_iInter.1 hv _) i (Nat.find_spec h)

theorem measurable_avgReg_yC (k : ℕ) :
    Measurable fun q : (ℕ → ℝ) × ℂ => avgReg (yC q.1) k q.2 :=
  (measurable_avgReg k).comp ((measurable_yC.comp measurable_fst).prodMk measurable_snd)

end GC
end ASep
end QuantumZipper
