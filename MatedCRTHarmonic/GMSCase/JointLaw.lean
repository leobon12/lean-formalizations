import MatedCRTHarmonic.GMSCase.Defs
import MatedCRTHarmonic.GMSAppA.LemmaA1A2
import LQGMetric.Field.CircleAvgLaw
import LQGMetric.Field.CircleAvgAffine
import LQGMetric.Papers.GM.S3.DeterministicScale
import LQGMetric.Papers.GM.S1.Dilate
import LQGMetric.Papers.GM.S1.WeakStrong

/-!
# The Case 3 and Case 4 laws of [18] Proposition 4.10

Source: (`[18]:N`), Proposition 4.10, Cases 3–4,
`[18]`; Appendix A, Lemma A.2, `[18]`.

Setting: a whole-plane GFF `h` normalized by `h_1(0) = 0`, and an independent random observation
`Y : Ω → 𝒴` together with a jointly measurable family `τ z₀ : 𝒴 → 𝒴` of Case 4 transformations
whose action preserves the law of `Y`. For the frozen bundle, `Y = ((hIG₀, U), ηL)` is the **full
imaginary-geometry data** (field, phase and curve) and `τ z₀` is the Case 4
transformation of the IG field and phase together with `case4Curve z₀` (`GMSCase/IGData.lean`).
The root `z₀` is either fixed or sampled independently.

* `map_case4_pair` (Case 4, fixed root): `(h(·/2 + z₀) − h_{1/2}(z₀), τ z₀ Y)` has the law of
  `(h, Y)`, a product.
* `map_case4_marked` (Case 4, independent root): with `z₀ ∼ λ` independent, the triple
  `(z₀, h(·/2 + z₀) − h_{1/2}(z₀), τ z₀ Y)` has law `λ ⊗ law(h) ⊗ law(Y)`.
* `indepFun_halfAvg_case4Local` (Case 3, fixed root with `B̄_{1/2}(z₀) ⊆ B̄_1(0)`): the Case 3
  index `h_{1/2}(z₀)` is **independent** of the Case 4 field restricted to the unit disk and of
  `τ z₀ Y`. This is the exact form of [18]'s Case 3 comparison: the conditional law of
  `h³|_{B_{1/2}(z₀)}` given `{h²_{1/2}(z₀) = a}` is its unconditional law (Radon–Nikodym
  derivative `M_{a,z₀} ≡ 1`; the analytic construction's `lemmaA2_indepFun`), so no Hölder step is needed in Case 3.
* `map_case3_marked`: with an independent root `z₀ ∼ λ` supported where
  `B̄_{1/2}(z₀) ⊆ B̄_1(0)`, the law of `((z₀, h_{1/2}(z₀)), (restricted Case 4 field, τ z₀ Y))`
  is the product of the law of `(z₀, h_{1/2}(z₀))` and of the law of `(restricted h, Y)` — the
  disintegration of the Case 2 law over the sampled average is the constant kernel.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric TopologicalSpace
open scoped ENNReal

namespace MatedCRTHarmonic.GMSCase

open LQGMetric LQGMetric.Blueprint

/-! ## A three-variable independence lemma -/

/-- If `X ⟂ Y` and `(X, Y) ⟂ Z`, then `X ⟂ (Y, Z)`. -/
theorem indepFun_prodMk_of_indepFun {Ω α β δ : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSpace δ] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → α} {Y : Ω → β} {Z : Ω → δ}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (hXY : IndepFun X Y P) (hXYZ : IndepFun (fun ω => (X ω, Y ω)) Z P) :
    IndepFun X (fun ω => (Y ω, Z ω)) P := by
  have hXYm : Measurable fun ω => (X ω, Y ω) := hX.prodMk hY
  have hYZm : Measurable fun ω => (Y ω, Z ω) := hY.prodMk hZ
  have hXYZm : Measurable fun ω => ((X ω, Y ω), Z ω) := hXYm.prodMk hZ
  rw [indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hYZm.aemeasurable]
  have hYZ : IndepFun Y Z P := hXYZ.comp measurable_snd measurable_id
  have h1 : P.map (fun ω => ((X ω, Y ω), Z ω)) =
      (P.map fun ω => (X ω, Y ω)).prod (P.map Z) :=
    hXYZ.map_prod_eq_prod_map_map hXYm.aemeasurable hZ.aemeasurable
  have h2 : P.map (fun ω => (X ω, Y ω)) = (P.map X).prod (P.map Y) :=
    hXY.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable
  have h3 : P.map (fun ω => (Y ω, Z ω)) = (P.map Y).prod (P.map Z) :=
    hYZ.map_prod_eq_prod_map_map hY.aemeasurable hZ.aemeasurable
  have hmap : P.map (fun ω => (X ω, (Y ω, Z ω))) =
      (P.map fun ω => ((X ω, Y ω), Z ω)).map MeasurableEquiv.prodAssoc := by
    rw [Measure.map_map MeasurableEquiv.prodAssoc.measurable hXYZm]
    rfl
  rw [hmap, h1, h2, Measure.prodAssoc_prod, h3]

/-! ## Case 4: the joint law at a fixed root -/

section Law

variable {Ω 𝒴 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒴] {P : Measure Ω}
  {h : Ω → DistC} {Y : Ω → 𝒴} {τ : ℂ → 𝒴 → 𝒴}

theorem measurable_case4Normalized_left (z₀ : ℂ) :
    Measurable fun g : DistC => case4Normalized g z₀ := by
  have hpair : Measurable fun g : DistC => ((g, z₀) : DistC × ℂ) :=
    measurable_id.prodMk measurable_const
  have h := measurable_case4Normalized.comp (g := fun p : DistC × ℂ => case4Normalized p.1 p.2)
    (f := fun g : DistC => ((g, z₀) : DistC × ℂ)) hpair
  exact h

theorem measurable_transform_right (hτ : Measurable fun p : ℂ × 𝒴 => τ p.1 p.2) (z₀ : ℂ) :
    Measurable fun y : 𝒴 => τ z₀ y := by
  have hpair : Measurable fun y : 𝒴 => ((z₀, y) : ℂ × 𝒴) :=
    measurable_const.prodMk measurable_id
  have h := hτ.comp (g := fun p : ℂ × 𝒴 => τ p.1 p.2)
    (f := fun y : 𝒴 => ((z₀, y) : ℂ × 𝒴)) hpair
  exact h

theorem measurable_halfAvg_marked (hh : Measurable h) :
    Measurable fun p : Ω × ℂ => halfAvg (h p.1) p.2 := by
  have hpair : Measurable fun p : Ω × ℂ => ((h p.1, p.2) : DistC × ℂ) :=
    (hh.comp measurable_fst).prodMk measurable_snd
  have e := measurable_halfAvg.comp (g := fun q : DistC × ℂ => halfAvg q.1 q.2)
    (f := fun p : Ω × ℂ => ((h p.1, p.2) : DistC × ℂ)) hpair
  exact e

theorem measurable_case4Normalized_marked (hh : Measurable h) :
    Measurable fun p : Ω × ℂ => case4Normalized (h p.1) p.2 := by
  have hpair : Measurable fun p : Ω × ℂ => ((h p.1, p.2) : DistC × ℂ) :=
    (hh.comp measurable_fst).prodMk measurable_snd
  have e := measurable_case4Normalized.comp (g := fun q : DistC × ℂ => case4Normalized q.1 q.2)
    (f := fun p : Ω × ℂ => ((h p.1, p.2) : DistC × ℂ)) hpair
  exact e

theorem measurable_transform_marked (hτ : Measurable fun p : ℂ × 𝒴 => τ p.1 p.2)
    (hY : Measurable Y) :
    Measurable fun p : Ω × ℂ => τ p.2 (Y p.1) := by
  have hpair : Measurable fun p : Ω × ℂ => ((p.2, Y p.1) : ℂ × 𝒴) :=
    measurable_snd.prodMk (hY.comp measurable_fst)
  have e := hτ.comp (g := fun q : ℂ × 𝒴 => τ q.1 q.2)
    (f := fun p : Ω × ℂ => ((p.2, Y p.1) : ℂ × 𝒴)) hpair
  exact e

/-- The normalized Case 4 field has the law of `h` (GM's affine invariance,
`CircleAvg.map_affine_sub_circleAvg`). -/
theorem map_case4Normalized (hh : IsNormalizedWPGFF h P) (z₀ : ℂ) :
    P.map (fun ω => case4Normalized (h ω) z₀) = P.map h :=
  CircleAvg.map_affine_sub_circleAvg hh (by norm_num) z₀

/-- **Case 4 joint law at a fixed root.** -/
theorem map_case4_pair (hh : IsNormalizedWPGFF h P) (hY : Measurable Y) (hτ : Measurable fun p : ℂ × 𝒴 => τ p.1 p.2)
    (hind : IndepFun h Y P) (z₀ : ℂ)
    (hlaw : P.map (fun ω => τ z₀ (Y ω)) = P.map Y) :
    P.map (fun ω => (case4Normalized (h ω) z₀, τ z₀ (Y ω))) =
      (P.map h).prod (P.map Y) := by
  have := hh.1.gaussian.isProbabilityMeasure
  have hF := measurable_case4Normalized_left z₀
  have hG := measurable_transform_right hτ z₀
  have hind' : IndepFun (fun ω => case4Normalized (h ω) z₀) (fun ω => τ z₀ (Y ω)) P :=
    hind.comp hF hG
  have hFm : Measurable fun ω => case4Normalized (h ω) z₀ := hF.comp hh.1.measurable
  have hGm : Measurable fun ω => τ z₀ (Y ω) := hG.comp hY
  have e : P.map (fun ω => (case4Normalized (h ω) z₀, τ z₀ (Y ω))) =
      (P.map fun ω => case4Normalized (h ω) z₀).prod (P.map fun ω => τ z₀ (Y ω)) :=
    hind'.map_prod_eq_prod_map_map hFm.aemeasurable hGm.aemeasurable
  rw [e, hlaw, map_case4Normalized hh z₀]

/-! ## Case 4: an independent root -/

/-- **Case 4 joint law with an independent root `z₀ ∼ λ`.** -/
theorem map_case4_marked (hh : IsNormalizedWPGFF h P) (hY : Measurable Y) (hτ : Measurable fun p : ℂ × 𝒴 => τ p.1 p.2)
    (hind : IndepFun h Y P)
    (hlaw : ∀ z₀ : ℂ, P.map (fun ω => τ z₀ (Y ω)) = P.map Y)
    (lam : Measure ℂ) [IsProbabilityMeasure lam] :
    (P.prod lam).map (fun p : Ω × ℂ =>
        (p.2, (case4Normalized (h p.1) p.2, τ p.2 (Y p.1)))) =
      lam.prod ((P.map h).prod (P.map Y)) := by
  have := hh.1.gaussian.isProbabilityMeasure
  set F : Ω × ℂ → DistC × 𝒴 := fun p => (case4Normalized (h p.1) p.2, τ p.2 (Y p.1))
    with hF_def
  have hFm : Measurable F :=
    (measurable_case4Normalized_marked hh.1.measurable).prodMk (measurable_transform_marked hτ hY)
  have hm : Measurable fun p : Ω × ℂ => (p.2, F p) := measurable_snd.prodMk hFm
  refine (Measure.prod_eq fun A S hA hS => ?_).symm
  rw [Measure.map_apply hm (hA.prod hS)]
  have hset : MeasurableSet ((fun p : Ω × ℂ => (p.2, F p)) ⁻¹' (A ×ˢ S)) := hm (hA.prod hS)
  rw [Measure.prod_apply_symm hset]
  have hslice : ∀ z : ℂ, P ((fun x => (x, z)) ⁻¹' ((fun p : Ω × ℂ => (p.2, F p)) ⁻¹' (A ×ˢ S))) =
      A.indicator (fun _ => ((P.map h).prod (P.map Y)) S) z := by
    intro z
    by_cases hz : z ∈ A
    · rw [indicator_of_mem hz]
      have hpre : (fun x => (x, z)) ⁻¹' ((fun p : Ω × ℂ => (p.2, F p)) ⁻¹' (A ×ˢ S)) =
          (fun ω => (case4Normalized (h ω) z, τ z (Y ω))) ⁻¹' S := by
        ext ω
        simp [hF_def, hz]
      have hpair : Measurable fun ω => (case4Normalized (h ω) z, τ z (Y ω)) :=
        ((measurable_case4Normalized_left z).comp hh.1.measurable).prodMk
          ((measurable_transform_right hτ z).comp hY)
      rw [hpre, ← map_case4_pair hh hY hτ hind z (hlaw z), Measure.map_apply hpair hS]
    · rw [indicator_of_notMem hz]
      have hpre : (fun x => (x, z)) ⁻¹' ((fun p : Ω × ℂ => (p.2, F p)) ⁻¹' (A ×ˢ S)) = ∅ := by
        ext ω
        simp [hz]
      rw [hpre, measure_empty]
  simp_rw [hslice]
  rw [lintegral_indicator_const hA, mul_comm]

/-! ## Case 3: independence of the sampled average -/

/-- The unit disk and the radius-`1/2` disk about `z₀` correspond under `y ↦ 2y − 2z₀`. -/
theorem mem_ballO_half_iff (z₀ y : ℂ) :
    y ∈ ballO z₀ (1 / 2) ↔ (2 : ℝ) • y + (-(2 * z₀)) ∈ ballO (0 : ℂ) 1 := by
  simp only [ballO, Opens.mem_mk, Metric.mem_ball, dist_eq_norm, sub_zero]
  have e : (2 : ℝ) • y + -(2 * z₀) = 2 * (y - z₀) := by
    rw [Complex.real_smul]; push_cast; ring
  rw [e, norm_mul, Complex.norm_ofNat]
  constructor <;> intro hh <;> linarith

/-- Restricting the Case 4 pullback to the unit disk only sees the field on `B_{1/2}(z₀)`. -/
def case4LocalPull (z₀ : ℂ) : DistOn (ballO z₀ (1 / 2)) → DistOn (ballO (0 : ℂ) 1) :=
  fun T => ((2 : ℝ) ^ 2) • T.comp (GM.testScalePush (two_ne_zero) (mem_ballO_half_iff z₀))

theorem measurable_case4LocalPull (z₀ : ℂ) : Measurable (case4LocalPull z₀) := by
  refine measurable_distOn_iff.2 fun ψ => ?_
  show Measurable fun T : DistOn (ballO z₀ (1 / 2)) =>
    (2 : ℝ) ^ 2 * T (GM.testScalePush two_ne_zero (mem_ballO_half_iff z₀) ψ)
  exact (measurable_distOn_apply _).const_mul _

theorem restrictTo_affineComp_half (z₀ : ℂ) (g : DistC) :
    restrictTo (ballO (0 : ℂ) 1) (affineComp (1 / 2) z₀ g) =
      case4LocalPull z₀ (restrictTo (ballO z₀ (1 / 2)) g) := by
  refine DFunLike.ext _ _ fun ψ => ?_
  rw [GM.restrictTo_apply_eq_scale (r := 2) two_pos (mem_ballO_half_iff z₀)]
  have hcomp : affineComp 2 (-(2 * z₀)) (affineComp (1 / 2) z₀ g) = g := by
    rw [GM.affineComp_comp two_ne_zero (by norm_num : (1 / 2 : ℝ) ≠ 0)]
    have h1 : (1 / 2 : ℝ) * 2 = 1 := by norm_num
    have h2 : (((1 / 2 : ℝ)) : ℂ) * -(2 * z₀) + z₀ = 0 := by push_cast; ring
    rw [h1, h2]
    exact GM.affineComp_one_zero g
  rw [hcomp]
  rfl

/-- The restricted Case 4 field is the pullback of the restricted Case 3 field. -/
theorem restrictTo_case4Normalized (z₀ : ℂ) (g : DistC) :
    restrictTo (ballO (0 : ℂ) 1) (case4Normalized g z₀) =
      case4LocalPull z₀ (restrictTo (ballO z₀ (1 / 2)) (addConst g (-circleAvg g (1 / 2) z₀))) := by
  rw [case4Normalized, ← GM.affineComp_addConst (by norm_num : (0 : ℝ) < 1 / 2),
    restrictTo_affineComp_half]

/-- **Case 3 (fixed root).** For `B̄_{1/2}(z₀) ⊆ B̄_1(0)`, the sampled average `h_{1/2}(z₀)` is
independent of the pair (Case 4 field restricted to the unit disk, Case 4 curve). -/
theorem indepFun_halfAvg_case4Local (hh : IsNormalizedWPGFF h P) (hY : Measurable Y) (hτ : Measurable fun p : ℂ × 𝒴 => τ p.1 p.2)
    (hind : IndepFun h Y P) {z₀ : ℂ}
    (hz : closedBall z₀ (1 / 2) ⊆ closedBall (0 : ℂ) 1) :
    IndepFun (fun ω => halfAvg (h ω) z₀)
      (fun ω => (restrictTo (ballO (0 : ℂ) 1) (case4Normalized (h ω) z₀),
        τ z₀ (Y ω))) P := by
  have := hh.1.gaussian.isProbabilityMeasure
  set a : DistC → ℝ := fun g => circleAvg g (1 / 2) z₀ with ha_def
  have ham : Measurable a := measurable_circleAvg_left (1 / 2) z₀
  set R : DistC → DistOn (ballO z₀ (1 / 2)) := fun g =>
    restrictTo (ballO z₀ (1 / 2)) (addConst g (-a g)) with hR_def
  have hRm : Measurable R :=
    (measurable_restrictTo _).comp (DFGPS.L219.measurable_addConst_of measurable_id ham.neg)
  have hXY : IndepFun (fun ω => a (h ω)) (fun ω => R (h ω)) P :=
    GMSAppA.lemmaA2_indepFun hh (by norm_num) hz
  have hXYZ : IndepFun (fun ω => (a (h ω), R (h ω))) (fun ω => τ z₀ (Y ω)) P :=
    hind.comp (ham.prodMk hRm) (measurable_transform_right hτ z₀)
  have H := indepFun_prodMk_of_indepFun (ham.comp hh.1.measurable) (hRm.comp hh.1.measurable)
    ((measurable_transform_right hτ z₀).comp hY) hXY hXYZ
  have H2 := H.comp measurable_id ((measurable_case4LocalPull z₀).prodMap measurable_id)
  have e1 : (fun ω => halfAvg (h ω) z₀) = (id ∘ fun ω => a (h ω)) := rfl
  have e2 : (fun ω => (restrictTo (ballO (0 : ℂ) 1) (case4Normalized (h ω) z₀),
      τ z₀ (Y ω))) =
      (Prod.map (case4LocalPull z₀) id ∘ fun ω => (R (h ω), τ z₀ (Y ω))) := by
    funext ω
    simp only [Function.comp_apply, Prod.map_apply, id_eq, hR_def, ha_def]
    rw [restrictTo_case4Normalized]
  rw [e1, e2]
  exact H2

/-- **Case 3 with an independent root.** If `λ` is a probability measure on roots with
`B̄_{1/2}(z₀) ⊆ B̄_1(0)` for `λ`-a.e. `z₀`, then under `P ⊗ λ` the pair `(z₀, h_{1/2}(z₀))` is
independent of the (restricted Case 4 field, Case 4 curve), whose law is the law of
`(h|_𝔻, C)`. -/
theorem map_case3_marked (hh : IsNormalizedWPGFF h P) (hY : Measurable Y) (hτ : Measurable fun p : ℂ × 𝒴 => τ p.1 p.2)
    (hind : IndepFun h Y P)
    (hlaw : ∀ z₀ : ℂ, P.map (fun ω => τ z₀ (Y ω)) = P.map Y)
    (lam : Measure ℂ) [IsProbabilityMeasure lam]
    (hsupp : ∀ᵐ z₀ ∂lam, closedBall z₀ (1 / 2) ⊆ closedBall (0 : ℂ) 1) :
    (P.prod lam).map (fun p : Ω × ℂ =>
        ((p.2, halfAvg (h p.1) p.2),
          (restrictTo (ballO (0 : ℂ) 1) (case4Normalized (h p.1) p.2), τ p.2 (Y p.1)))) =
      ((P.prod lam).map fun p : Ω × ℂ => (p.2, halfAvg (h p.1) p.2)).prod
        (P.map fun ω => (restrictTo (ballO (0 : ℂ) 1) (h ω), Y ω)) := by
  have hP := hh.1.gaussian.isProbabilityMeasure
  set ν : Measure (DistOn (ballO (0 : ℂ) 1) × 𝒴) :=
    P.map fun ω => (restrictTo (ballO (0 : ℂ) 1) (h ω), Y ω) with hν
  have hνP : IsProbabilityMeasure ν := by rw [hν]; infer_instance
  -- measurability of the pieces on `Ω × ℂ`
  have hA : Measurable fun p : Ω × ℂ => (p.2, halfAvg (h p.1) p.2) :=
    measurable_snd.prodMk (measurable_halfAvg_marked hh.1.measurable)
  have hL : Measurable fun p : Ω × ℂ =>
      (restrictTo (ballO (0 : ℂ) 1) (case4Normalized (h p.1) p.2), τ p.2 (Y p.1)) :=
    ((measurable_restrictTo _).comp (measurable_case4Normalized_marked hh.1.measurable)).prodMk
      (measurable_transform_marked hτ hY)
  -- the slice law at a fixed admissible root
  have hslice : ∀ z₀ : ℂ, closedBall z₀ (1 / 2) ⊆ closedBall (0 : ℂ) 1 → ∀ B S : Set _,
      MeasurableSet B → MeasurableSet S →
      P {ω | halfAvg (h ω) z₀ ∈ B ∧
          (restrictTo (ballO (0 : ℂ) 1) (case4Normalized (h ω) z₀), τ z₀ (Y ω)) ∈ S} =
        P {ω | halfAvg (h ω) z₀ ∈ B} * ν S := by
    intro z₀ hz B S hB hS
    have hI := indepFun_halfAvg_case4Local hh hY hτ hind hz
    have hlocm : Measurable fun ω =>
        (restrictTo (ballO (0 : ℂ) 1) (case4Normalized (h ω) z₀), τ z₀ (Y ω)) :=
      ((measurable_restrictTo _).comp ((measurable_case4Normalized_left z₀).comp
        hh.1.measurable)).prodMk ((measurable_transform_right hτ z₀).comp hY)
    have hmeas := hI.measure_inter_preimage_eq_mul B S hB hS
    have hlaw' : P.map (fun ω =>
        (restrictTo (ballO (0 : ℂ) 1) (case4Normalized (h ω) z₀), τ z₀ (Y ω))) = ν := by
      have e := map_case4_pair hh hY hτ hind z₀ (hlaw z₀)
      have e2 : (P.map (fun ω => (case4Normalized (h ω) z₀, τ z₀ (Y ω)))).map
          (Prod.map (restrictTo (ballO (0 : ℂ) 1)) id) =
          ((P.map h).prod (P.map Y)).map (Prod.map (restrictTo (ballO (0 : ℂ) 1)) id) := by
        rw [e]
      have hpm : Measurable fun ω => (case4Normalized (h ω) z₀, τ z₀ (Y ω)) :=
        ((measurable_case4Normalized_left z₀).comp hh.1.measurable).prodMk
          ((measurable_transform_right hτ z₀).comp hY)
      rw [Measure.map_map ((measurable_restrictTo _).prodMap measurable_id) hpm] at e2
      rw [hν]
      have e3 : (P.map h).prod (P.map Y) = P.map (fun ω => (h ω, Y ω)) :=
        (hind.map_prod_eq_prod_map_map hh.1.measurable.aemeasurable hY.aemeasurable).symm
      rw [e3, Measure.map_map ((measurable_restrictTo _).prodMap measurable_id)
        (hh.1.measurable.prodMk hY)] at e2
      exact e2
    have hset : {ω | halfAvg (h ω) z₀ ∈ B ∧
        (restrictTo (ballO (0 : ℂ) 1) (case4Normalized (h ω) z₀), τ z₀ (Y ω)) ∈ S} =
        (fun ω => halfAvg (h ω) z₀) ⁻¹' B ∩ (fun ω =>
          (restrictTo (ballO (0 : ℂ) 1) (case4Normalized (h ω) z₀), τ z₀ (Y ω))) ⁻¹' S :=
      rfl
    rw [hset, hmeas, ← hlaw', Measure.map_apply hlocm hS]
    rfl
  refine (Measure.prod_eq fun E S hE hS => ?_).symm
  rw [Measure.map_apply (hA.prodMk hL) (hE.prod hS), Measure.map_apply hA hE]
  have hset1 : MeasurableSet ((fun p : Ω × ℂ => ((p.2, halfAvg (h p.1) p.2),
      (restrictTo (ballO (0 : ℂ) 1) (case4Normalized (h p.1) p.2), τ p.2 (Y p.1)))) ⁻¹'
      (E ×ˢ S)) := (hA.prodMk hL) (hE.prod hS)
  have hset2 : MeasurableSet ((fun p : Ω × ℂ => (p.2, halfAvg (h p.1) p.2)) ⁻¹' E) := hA hE
  rw [Measure.prod_apply_symm hset1, Measure.prod_apply_symm hset2, ← lintegral_mul_const _
    (measurable_measure_prodMk_right hset2)]
  refine lintegral_congr_ae ?_
  filter_upwards [hsupp] with z₀ hz
  have hEz : MeasurableSet {a : ℝ | (z₀, a) ∈ E} := measurable_prodMk_left hE
  have h1 := hslice z₀ hz {a : ℝ | (z₀, a) ∈ E} S hEz hS
  exact h1

end Law

end MatedCRTHarmonic.GMSCase
