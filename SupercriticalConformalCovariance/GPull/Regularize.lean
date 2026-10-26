import SupercriticalConformalCovariance.GPull.Coupling
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory TopologicalSpace Set

namespace SupercriticalConformalCovariance.GPull

/-- A jointly measurable field with almost surely continuous paths on an open domain
has a measurable continuous-map modification. -/
theorem exists_measurable_continuous_version
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {U : Opens ℂ} {H : Ω → U → ℝ}
    (hHm : Measurable (fun p : Ω × U => H p.1 p.2))
    (hHc : ∀ᵐ ω ∂P, Continuous (H ω)) :
    ∃ K : Ω → C(U, ℝ), Measurable K ∧
      (∀ᵐ ω ∂P, ∀ x : U, K ω x = H ω x) := by
  classical
  obtain ⟨D, hDc, hDd⟩ := exists_countable_dense U
  let _ : Countable D := hDc.to_subtype
  let e : C(U, ℝ) → (D → ℝ) := fun f d => f d
  have hem : Measurable e := Measurable.of_eval fun d =>
    ContinuousMap.measurable_eval (d : U)
  have hei : Function.Injective e := by
    intro f g h
    apply ContinuousMap.ext
    intro x
    exact congrFun (Continuous.ext_on hDd f.continuous g.continuous
      (fun y hy => congrFun h ⟨y, hy⟩)) x
  have hee : MeasurableEmbedding e := hem.measurableEmbedding hei
  let X : Ω → (D → ℝ) := fun ω d => H ω d
  have hXm : Measurable X := Measurable.of_eval fun d =>
    hHm.comp (measurable_id.prodMk measurable_const)
  let inv : (D → ℝ) → C(U, ℝ) := hee.invFun
  have hinv : ∀ f : C(U, ℝ), inv (e f) = f := hee.leftInverse_invFun
  have him : Measurable inv := hee.measurable_invFun
  refine ⟨inv ∘ X, him.comp hXm, ?_⟩
  filter_upwards [hHc] with ω hc
  let f : C(U, ℝ) := ⟨H ω, hc⟩
  have hxe : X ω = e f := by funext d; rfl
  intro x
  change inv (X ω) x = H ω x
  rw [hxe, hinv]
  rfl


end SupercriticalConformalCovariance.GPull
