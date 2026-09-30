import QuantumZipper.Proofs.Thm18.G3AreaPalmGood

/-!
# G3 area Palm input (Theorem 1.8): the Palm transfer

`G3AreaPalmStmt γ` (`G3Area.lean`) says: for every index, `g3PalmLaw γ i`-a.e. the field
translated to the Palm point `x = g3X γ i p` and to its length partner `R(x) = g3R γ i p` is
area-good. This file proves it (`g3AreaPalmStmt_holds`, `0 < γ < 2`).

Two steps:

* `IsAreaGood.translate`: area-goodness is invariant under (real) translations —
  `translate y t` has area measure `(qAreaMeasure γ y).map (· - t)` (`qAreaMeasure_translate`),
  and the preimage of an open nonempty `V ⊆ ℍ` under `z ↦ z - t` is again open, nonempty and
  inside `ℍ`;
* `ae_g3PalmLaw_of_ae_field`: a property of the field that holds `gffBase.P`-a.e. holds
  `g3PalmLaw γ i`-a.e., because the Palm law is `(P ⊗ Exp 1).withDensity g3W` and hence
  absolutely continuous with respect to `P ⊗ Exp 1`, which gives no mass to a `P`-null set of
  the field variable. **This replaces the Palm-formula transfer of the blueprint sketch**
  (`Prop17PalmABId.ae_palmFreeField_good`): since the concrete scheme's Palm law is defined by an
  explicit density against `P ⊗ Exp 1` (`G3Concrete.g3PalmLaw`), no Palm identity is needed for
  the *field* marginal — the standard remark "the rooted measure is absolutely continuous in the
  field variable". The Palm point `x` itself does not enter, because area-goodness is
  translation invariant.

With `ae_isAreaGood_normField` (Theorem 1.2's field is a.s. area-good, `G3AreaPalmGood.lean`)
this gives `G3AreaPalmStmt γ` for `0 < γ < 2`, hence `G3AreaStmt γ` via `g3AreaStmt_of_palm`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

/-! ## Area-goodness is translation invariant -/

/-- **Area-goodness is invariant under real translations.** The area measure of `translate y t`
is the pushforward of that of `y` under `z ↦ z - t` (`qAreaMeasure_translate`), and for real `t`
that map carries open nonempty subsets of `ℍ` to open nonempty subsets of `ℍ`. -/
theorem IsAreaGood.translate {γ : ℝ} {y : FieldSample} (hy : IsAreaGood γ y) (t : ℝ) :
    IsAreaGood γ (translate y (t : ℂ)) := by
  refine ⟨hy.1.translate t, fun V hV hVH hne => ?_⟩
  rw [GoodTransforms.qAreaMeasure_translate hy.1 t,
    Measure.map_apply (measurable_sub_const (t : ℂ)) hV.measurableSet]
  refine hy.2 ((fun z : ℂ => z - (t : ℂ)) ⁻¹' V) ?_ ?_ ?_
  · exact hV.preimage (continuous_id.sub continuous_const)
  · intro z hz
    have h : 0 < (z - (t : ℂ)).im := hVH hz
    show 0 < z.im
    simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero] using h
  · obtain ⟨v, hv⟩ := hne
    exact ⟨v + t, by simpa using hv⟩

/-! ## The Palm transfer -/

/-- **A `P`-a.e. property of the field holds Palm-a.e.** The Palm law is a density times
`P ⊗ Exp 1` (`g3PalmLaw`), so it is absolutely continuous with respect to it, and `P ⊗ Exp 1`
gives no mass to `{p | p.1 ∈ N}` for a `P`-null set `N`. -/
theorem ae_g3PalmLaw_of_ae_field (γ : ℝ) (i : G3Idx)
    (h : ∀ᵐ ω ∂gffBase.P, IsAreaGood γ (normField γ gffBase.X ω)) :
    ∀ᵐ p ∂(g3PalmLaw γ i), IsAreaGood γ (normField γ gffBase.X p.1) := by
  have hN : gffBase.P {ω | ¬ IsAreaGood γ (normField γ gffBase.X ω)} = 0 := ae_iff.1 h
  have hsm : (gffBase.P.prod L₀)
      {p : gffBase.Ω × ℝ | ¬ IsAreaGood γ (normField γ gffBase.X p.1)} = 0 := by
    refine measure_mono_null (t := toMeasurable gffBase.P
        {ω | ¬ IsAreaGood γ (normField γ gffBase.X ω)} ×ˢ (univ : Set ℝ))
      (fun p hp => ⟨subset_toMeasurable _ _ hp, mem_univ _⟩) ?_
    rw [Measure.prod_prod, measure_toMeasurable, hN, zero_mul]
  unfold g3PalmLaw
  exact ae_iff.2 ((withDensity_absolutelyContinuous _ _) hsm)

/-! ## The G3 area Palm input -/

/-- **G3 area Palm input (Theorem 1.8)**: for `0 < γ < 2` and every index, Palm-a.e. the field
translated to the Palm point `x` and to its length partner `R(x)` is area-good. -/
theorem g3AreaPalmStmt_holds {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) : G3AreaPalmStmt γ := by
  intro i
  filter_upwards [ae_g3PalmLaw_of_ae_field γ i
    (ae_isAreaGood_normField gffBase.gff hγ hγ2)] with p hp
  exact ⟨hp.translate _, hp.translate _⟩

end Thm18Asm
end QuantumZipper
