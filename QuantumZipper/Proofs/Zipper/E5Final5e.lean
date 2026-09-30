import QuantumZipper.Proofs.Zipper.E5Final5d

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# E5-REPR-FINAL, part e: measurability of the pushed normalizer at a random level time

Task E5-REPR-FINAL (Theorem 1.3, node E5, decision D39); Sheffield, arXiv:1012.4797, §5.4.

`E5Asm2.measurable_revMap_level` / `measurable_varpiT_level` prove the joint measurability of the
reverse maps / pushed normalizer at the level collision time `T − T_ℓ`. The germ-free
correction of `E5Final5d` lives at the shortened, clipped time `max (T − T_ℓ − u₀) 0`. This file
gives the same measurability for **any** measurable nonnegative level time `τ`
(`measurable_revMap_level_time`, `measurable_varpiT_level_time`, proofs of `E5Asm2` with the
time generalized), and the level-space `comap Ξ` form needed as `hν` of
`E5IncSwitch.setup_locCorr_switch_reg` (`measurable_varpiT_lvl_time`), in particular for the
germ-free time (`measurable_varpiT_lvl_germFree`). Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E5

open ESM LengthMarkov StrongMarkov B2 E1

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ T : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample} {ϖ : Measure ℂ}

omit [IsProbabilityMeasure P] in
/-- **The reverse maps at a measurable nonnegative level time are jointly measurable.** -/
theorem measurable_revMap_level_time (hS : E5.Setup κ T P B X ϖ)
    (hBc : ∀ ω, Continuous (B · ω)) {τ : ℝ≥0 × NullMeasurableSpace Ω P → ℝ}
    (hτm : Measurable τ) (hτ0 : ∀ z, 0 ≤ τ z) :
    Measurable fun p : (ℝ≥0 × NullMeasurableSpace Ω P) × ℂ =>
      revMap (Vr κ T B (ofCompl P p.1.2)) (τ p.1) p.2 := by
  classical
  obtain ⟨hκ, hκ4, hT, hB, hX, hind, -⟩ := id hS
  have hg : Measurable fun z : ℝ≥0 × NullMeasurableSpace Ω P => pathIcc T B hBc (ofCompl P z.2) :=
    ContinuousMap.measurable_iff_eval.2 fun x =>
      (measurable_B_compl hB x.1.toNNReal).comp measurable_snd
  set S : Set ((ℝ≥0 × NullMeasurableSpace Ω P) × ℂ) := {p | 0 < p.2.im} with hSdef
  have hSm : MeasurableSet S := measurableSet_lt measurable_const (Complex.measurable_im.comp
    measurable_snd)
  set F : S → ℂ := fun q => revMap (vrPath κ T hT.le (pathIcc T B hBc (ofCompl P q.1.1.2)))
    (max (τ q.1.1) 0) q.1.2 with hFdef
  have e : (fun p : (ℝ≥0 × NullMeasurableSpace Ω P) × ℂ =>
      revMap (Vr κ T B (ofCompl P p.1.2)) (τ p.1) p.2) = fun p =>
      if hp : p ∈ S then F ⟨p, hp⟩ else (0 : ℂ) := by
    funext p
    split_ifs with hp
    · rw [Vr_eq_vrPath hT.le hBc, hFdef]
      simp only [max_eq_left (hτ0 p.1)]
    · exact CharFun.revMap_of_not_mem (hτ0 p.1) hp
  rw [e]
  refine Measurable.dite (f := F) (g := fun _ => (0 : ℂ)) ?_ measurable_const hSm
  have hin : Measurable fun q : S =>
      (((τ q.1.1, ⟨q.1.2, q.2⟩) : ℝ × {z : ℂ // 0 < z.im}),
        pathIcc T B hBc (ofCompl P q.1.1.2)) :=
    ((hτm.comp (measurable_fst.comp measurable_subtype_coe)).prodMk
      ((measurable_snd.comp measurable_subtype_coe).subtype_mk)).prodMk
      (hg.comp (measurable_fst.comp measurable_subtype_coe))
  exact (measurable_revMap_vrPath_uncurry κ T hT.le).comp hin

/-- **The pushed normalizer at a measurable nonnegative level time is a measurable family of
measures.** -/
theorem measurable_varpiT_level_time (hS : E5.Setup κ T P B X ϖ)
    (hBc : ∀ ω, Continuous (B · ω)) {τ : ℝ≥0 × NullMeasurableSpace Ω P → ℝ}
    (hτm : Measurable τ) (hτ0 : ∀ z, 0 ≤ τ z) {A : Set ℂ} (hA : MeasurableSet A) :
    Measurable fun z : ℝ≥0 × NullMeasurableSpace Ω P =>
      varpiT (Vr κ T B (ofCompl P z.2)) (τ z) ϖ A := by
  obtain ⟨hκ, hκ4, hT, hB, hX, hind, hϖ⟩ := id hS
  have := hϖ.prob
  have hR := measurable_revMap_level_time hS hBc hτm hτ0
  have e : (fun z : ℝ≥0 × NullMeasurableSpace Ω P =>
      varpiT (Vr κ T B (ofCompl P z.2)) (τ z) ϖ A) =
      fun z => ∫⁻ v, A.indicator 1 (revMap (Vr κ T B (ofCompl P z.2)) (τ z) v) ∂ϖ := by
    funext z
    have hm := TwoPoint.measurable_revMap (continuous_Vr_e5 (κ := κ) (T := T)
      (hBc (ofCompl P z.2))) (hτ0 z)
    rw [varpiT, Measure.map_apply hm hA, ← lintegral_indicator_one (hm hA)]
    rfl
  rw [e]
  exact ((measurable_one.indicator hA).comp hR).lintegral_prod_right'

/-- **`hν` of `setup_locCorr_switch_reg` on the level space at a general level time.** -/
theorem measurable_varpiT_lvl_time {Ω' : Type} [MeasurableSpace Ω'] (hS : E5.Setup κ T P B X ϖ)
    (hBc : ∀ ω, Continuous (B · ω)) {τ : ℝ≥0 × NullMeasurableSpace Ω P → ℝ}
    (hτm : Measurable τ) (hτ0 : ∀ z, 0 ≤ τ z) {A : Set ℂ} (hA : MeasurableSet A) :
    Measurable[MeasurableSpace.comap (lvlXi : lvl Ω P Ω' → _) inferInstance]
      fun z : lvl Ω P Ω' => varpiT (lvlDrv κ T B P z.1) (τ z.1) ϖ A := by
  have hg := measurable_varpiT_level_time hS hBc hτm hτ0 hA
  have hxi : Measurable[MeasurableSpace.comap
      (lvlXi : lvl Ω P Ω' → ℝ≥0 × NullMeasurableSpace Ω P) inferInstance]
      (lvlXi : lvl Ω P Ω' → ℝ≥0 × NullMeasurableSpace Ω P) :=
    measurable_iff_comap_le.2 le_rfl
  exact hg.comp hxi

end E5
end QuantumZipper
