import MatedCRTHarmonic.GMSCase.JointLaw

/-!
# The Case 3 and Case 4 laws at a general renormalization radius

Same statements as `GMSCase.JointLaw` with the radius `1/2` of [18] (4.41)–(4.42) replaced by an
arbitrary radius `r > 0` with `B̄_r(z₀) ⊆ B̄_1(0)`: the field `h(r · + z₀) − h_r(z₀)`
(`caseNormalized r h z₀`), its sampled average `h_r(z₀)` (`radAvg r h z₀`) and a law-preserving
measurable family `τ z₀` acting on an independent observation `Y`.

The repaired Case 3 argument  uses a radius `r ∈ (3/4, 1)` equal to
The radius of the γ-cone's Markov decomposition, so that the two random mesh factors have the same
law.

* `map_caseNormalized`, `map_case_pair`, `map_case_marked`;
* `indepFun_radAvg_caseLocal` (exact Lemma A.2 independence at radius `r`);
* `map_case3_marked_r` (disintegration over the sampled average = constant kernel).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric TopologicalSpace
open scoped ENNReal

namespace MatedCRTHarmonic.GMSCase

open LQGMetric LQGMetric.Blueprint

section LawR

variable {Ω 𝒴 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒴] {P : Measure Ω}
  {h : Ω → DistC} {Y : Ω → 𝒴} {τ : ℂ → 𝒴 → 𝒴}

theorem measurable_caseNormalized_left (r : ℝ) (z₀ : ℂ) :
    Measurable fun g : DistC => caseNormalized r g z₀ := by
  have hpair : Measurable fun g : DistC => ((g, z₀) : DistC × ℂ) :=
    measurable_id.prodMk measurable_const
  have e : Measurable ((fun p : DistC × ℂ => caseNormalized r p.1 p.2) ∘
      (fun g : DistC => ((g, z₀) : DistC × ℂ))) := (measurable_caseNormalized r).comp hpair
  exact e

theorem measurable_radAvg_marked (r : ℝ) (hh : Measurable h) :
    Measurable fun p : Ω × ℂ => radAvg r (h p.1) p.2 := by
  have hpair : Measurable fun p : Ω × ℂ => ((h p.1, p.2) : DistC × ℂ) :=
    (hh.comp measurable_fst).prodMk measurable_snd
  have e : Measurable ((fun q : DistC × ℂ => radAvg r q.1 q.2) ∘
      (fun p : Ω × ℂ => ((h p.1, p.2) : DistC × ℂ))) := (measurable_radAvg r).comp hpair
  exact e

theorem measurable_caseNormalized_marked (r : ℝ) (hh : Measurable h) :
    Measurable fun p : Ω × ℂ => caseNormalized r (h p.1) p.2 := by
  have hpair : Measurable fun p : Ω × ℂ => ((h p.1, p.2) : DistC × ℂ) :=
    (hh.comp measurable_fst).prodMk measurable_snd
  have e : Measurable ((fun q : DistC × ℂ => caseNormalized r q.1 q.2) ∘
      (fun p : Ω × ℂ => ((h p.1, p.2) : DistC × ℂ))) := (measurable_caseNormalized r).comp hpair
  exact e

/-- The normalized pullback has the law of `h` (GM's affine invariance). -/
theorem map_caseNormalized (hh : IsNormalizedWPGFF h P) {r : ℝ} (hr : 0 < r) (z₀ : ℂ) :
    P.map (fun ω => caseNormalized r (h ω) z₀) = P.map h :=
  CircleAvg.map_affine_sub_circleAvg hh hr z₀

/-- **Case 4 joint law at a fixed root, radius `r`.** -/
theorem map_case_pair (hh : IsNormalizedWPGFF h P) {r : ℝ} (hr : 0 < r) (hY : Measurable Y)
    (hτ : Measurable fun p : ℂ × 𝒴 => τ p.1 p.2) (hind : IndepFun h Y P) (z₀ : ℂ)
    (hlaw : P.map (fun ω => τ z₀ (Y ω)) = P.map Y) :
    P.map (fun ω => (caseNormalized r (h ω) z₀, τ z₀ (Y ω))) = (P.map h).prod (P.map Y) := by
  have := hh.1.gaussian.isProbabilityMeasure
  have hF := measurable_caseNormalized_left r z₀
  have hG := measurable_transform_right hτ z₀
  have hind' : IndepFun (fun ω => caseNormalized r (h ω) z₀) (fun ω => τ z₀ (Y ω)) P :=
    hind.comp hF hG
  have hFm : Measurable fun ω => caseNormalized r (h ω) z₀ := hF.comp hh.1.measurable
  have hGm : Measurable fun ω => τ z₀ (Y ω) := hG.comp hY
  have e : P.map (fun ω => (caseNormalized r (h ω) z₀, τ z₀ (Y ω))) =
      (P.map fun ω => caseNormalized r (h ω) z₀).prod (P.map fun ω => τ z₀ (Y ω)) :=
    hind'.map_prod_eq_prod_map_map hFm.aemeasurable hGm.aemeasurable
  rw [e, hlaw, map_caseNormalized hh hr z₀]

/-! ## Restriction to the unit disk -/

/-- The unit disk and the radius-`r` disk about `z₀` correspond under `y ↦ (y − z₀)/r`. -/
theorem mem_ballO_iff_radius {r : ℝ} (hr : 0 < r) (z₀ y : ℂ) :
    y ∈ ballO z₀ r ↔ r⁻¹ • y + (-((r⁻¹ : ℂ) * z₀)) ∈ ballO (0 : ℂ) 1 := by
  simp only [ballO, Opens.mem_mk, Metric.mem_ball, dist_eq_norm, sub_zero]
  have e : r⁻¹ • y + -((r⁻¹ : ℂ) * z₀) = (r⁻¹ : ℂ) * (y - z₀) := by
    rw [Complex.real_smul]; push_cast; ring
  have hn : ‖((r : ℂ))⁻¹‖ = r⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  rw [e, norm_mul, hn]
  constructor
  · intro hh
    calc r⁻¹ * ‖y - z₀‖ < r⁻¹ * r := mul_lt_mul_of_pos_left hh (inv_pos.2 hr)
      _ = 1 := inv_mul_cancel₀ hr.ne'
  · intro hh
    have := mul_lt_mul_of_pos_left hh hr
    rwa [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul, mul_one] at this

/-- Restricting the radius-`r` pullback to the unit disk only sees the field on `B_r(z₀)`. -/
def caseLocalPull {r : ℝ} (hr : 0 < r) (z₀ : ℂ) :
    DistOn (ballO z₀ r) → DistOn (ballO (0 : ℂ) 1) :=
  fun T => ((r⁻¹ : ℝ) ^ 2) • T.comp (GM.testScalePush (inv_ne_zero hr.ne') (mem_ballO_iff_radius hr z₀))

theorem measurable_caseLocalPull {r : ℝ} (hr : 0 < r) (z₀ : ℂ) :
    Measurable (caseLocalPull hr z₀) := by
  refine measurable_distOn_iff.2 fun ψ => ?_
  show Measurable fun T : DistOn (ballO z₀ r) =>
    (r⁻¹ : ℝ) ^ 2 * T (GM.testScalePush (inv_ne_zero hr.ne') (mem_ballO_iff_radius hr z₀) ψ)
  exact (measurable_distOn_apply _).const_mul _

theorem restrictTo_affineComp_radius {r : ℝ} (hr : 0 < r) (z₀ : ℂ) (g : DistC) :
    restrictTo (ballO (0 : ℂ) 1) (affineComp r z₀ g) =
      caseLocalPull hr z₀ (restrictTo (ballO z₀ r) g) := by
  refine DFunLike.ext _ _ fun ψ => ?_
  rw [GM.restrictTo_apply_eq_scale (r := r⁻¹) (inv_pos.2 hr) (mem_ballO_iff_radius hr z₀)]
  have hcomp : affineComp r⁻¹ (-((r⁻¹ : ℂ) * z₀)) (affineComp r z₀ g) = g := by
    rw [GM.affineComp_comp (inv_ne_zero hr.ne') hr.ne']
    have h1 : r * r⁻¹ = 1 := mul_inv_cancel₀ hr.ne'
    have h2 : (r : ℂ) * -((r⁻¹ : ℂ) * z₀) + z₀ = 0 := by
      have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
      field_simp
      ring
    rw [h1, h2]
    exact GM.affineComp_one_zero g
  rw [hcomp]
  rfl

/-- The restricted normalized pullback is the pullback of the restricted re-normalized field. -/
theorem restrictTo_caseNormalized {r : ℝ} (hr : 0 < r) (z₀ : ℂ) (g : DistC) :
    restrictTo (ballO (0 : ℂ) 1) (caseNormalized r g z₀) =
      caseLocalPull hr z₀ (restrictTo (ballO z₀ r) (addConst g (-circleAvg g r z₀))) := by
  rw [caseNormalized, ← GM.affineComp_addConst hr, restrictTo_affineComp_radius hr]

/-- **Case 3 (fixed root, radius `r`).** For `B̄_r(z₀) ⊆ B̄_1(0)`, `h_r(z₀)` is independent of the
pair (normalized pullback restricted to the unit disk, `τ z₀ Y`). -/
theorem indepFun_radAvg_caseLocal (hh : IsNormalizedWPGFF h P) {r : ℝ} (hr : 0 < r)
    (hY : Measurable Y) (hτ : Measurable fun p : ℂ × 𝒴 => τ p.1 p.2) (hind : IndepFun h Y P)
    {z₀ : ℂ} (hz : closedBall z₀ r ⊆ closedBall (0 : ℂ) 1) :
    IndepFun (fun ω => radAvg r (h ω) z₀)
      (fun ω => (restrictTo (ballO (0 : ℂ) 1) (caseNormalized r (h ω) z₀), τ z₀ (Y ω))) P := by
  have := hh.1.gaussian.isProbabilityMeasure
  set a : DistC → ℝ := fun g => circleAvg g r z₀ with ha_def
  have ham : Measurable a := measurable_circleAvg_left r z₀
  set R : DistC → DistOn (ballO z₀ r) := fun g =>
    restrictTo (ballO z₀ r) (addConst g (-a g)) with hR_def
  have hRm : Measurable R :=
    (measurable_restrictTo _).comp (DFGPS.L219.measurable_addConst_of measurable_id ham.neg)
  have hXY : IndepFun (fun ω => a (h ω)) (fun ω => R (h ω)) P :=
    GMSAppA.lemmaA2_indepFun hh hr hz
  have hXYZ : IndepFun (fun ω => (a (h ω), R (h ω))) (fun ω => τ z₀ (Y ω)) P :=
    hind.comp (ham.prodMk hRm) (measurable_transform_right hτ z₀)
  have H := indepFun_prodMk_of_indepFun (ham.comp hh.1.measurable) (hRm.comp hh.1.measurable)
    ((measurable_transform_right hτ z₀).comp hY) hXY hXYZ
  have H2 := H.comp measurable_id ((measurable_caseLocalPull hr z₀).prodMap measurable_id)
  have e1 : (fun ω => radAvg r (h ω) z₀) = (id ∘ fun ω => a (h ω)) := rfl
  have e2 : (fun ω => (restrictTo (ballO (0 : ℂ) 1) (caseNormalized r (h ω) z₀), τ z₀ (Y ω))) =
      (Prod.map (caseLocalPull hr z₀) id ∘ fun ω => (R (h ω), τ z₀ (Y ω))) := by
    funext ω
    simp only [Function.comp_apply, Prod.map_apply, id_eq, hR_def, ha_def]
    rw [restrictTo_caseNormalized hr]
  rw [e1, e2]
  exact H2

/-- **Cases 3–4 with an independent root, radius `r`.** -/
theorem map_case3_marked_r (hh : IsNormalizedWPGFF h P) {r : ℝ} (hr : 0 < r) (hY : Measurable Y)
    (hτ : Measurable fun p : ℂ × 𝒴 => τ p.1 p.2) (hind : IndepFun h Y P)
    (hlaw : ∀ z₀ : ℂ, P.map (fun ω => τ z₀ (Y ω)) = P.map Y)
    (lam : Measure ℂ) [IsProbabilityMeasure lam]
    (hsupp : ∀ᵐ z₀ ∂lam, closedBall z₀ r ⊆ closedBall (0 : ℂ) 1) :
    (P.prod lam).map (fun p : Ω × ℂ =>
        ((p.2, radAvg r (h p.1) p.2),
          (restrictTo (ballO (0 : ℂ) 1) (caseNormalized r (h p.1) p.2), τ p.2 (Y p.1)))) =
      ((P.prod lam).map fun p : Ω × ℂ => (p.2, radAvg r (h p.1) p.2)).prod
        (P.map fun ω => (restrictTo (ballO (0 : ℂ) 1) (h ω), Y ω)) := by
  have hP := hh.1.gaussian.isProbabilityMeasure
  set ν : Measure (DistOn (ballO (0 : ℂ) 1) × 𝒴) :=
    P.map fun ω => (restrictTo (ballO (0 : ℂ) 1) (h ω), Y ω) with hν
  have hνP : IsProbabilityMeasure ν := by rw [hν]; infer_instance
  have hA : Measurable fun p : Ω × ℂ => (p.2, radAvg r (h p.1) p.2) :=
    measurable_snd.prodMk (measurable_radAvg_marked r hh.1.measurable)
  have hL : Measurable fun p : Ω × ℂ =>
      (restrictTo (ballO (0 : ℂ) 1) (caseNormalized r (h p.1) p.2), τ p.2 (Y p.1)) :=
    ((measurable_restrictTo _).comp (measurable_caseNormalized_marked r hh.1.measurable)).prodMk
      (measurable_transform_marked hτ hY)
  have hslice : ∀ z₀ : ℂ, closedBall z₀ r ⊆ closedBall (0 : ℂ) 1 → ∀ B S : Set _,
      MeasurableSet B → MeasurableSet S →
      P {ω | radAvg r (h ω) z₀ ∈ B ∧
          (restrictTo (ballO (0 : ℂ) 1) (caseNormalized r (h ω) z₀), τ z₀ (Y ω)) ∈ S} =
        P {ω | radAvg r (h ω) z₀ ∈ B} * ν S := by
    intro z₀ hz B S hB hS
    have hI := indepFun_radAvg_caseLocal hh hr hY hτ hind hz
    have hlocm : Measurable fun ω =>
        (restrictTo (ballO (0 : ℂ) 1) (caseNormalized r (h ω) z₀), τ z₀ (Y ω)) :=
      ((measurable_restrictTo _).comp ((measurable_caseNormalized_left r z₀).comp
        hh.1.measurable)).prodMk ((measurable_transform_right hτ z₀).comp hY)
    have hmeas := hI.measure_inter_preimage_eq_mul B S hB hS
    have hlaw' : P.map (fun ω =>
        (restrictTo (ballO (0 : ℂ) 1) (caseNormalized r (h ω) z₀), τ z₀ (Y ω))) = ν := by
      have e := map_case_pair hh hr hY hτ hind z₀ (hlaw z₀)
      have e2 : (P.map (fun ω => (caseNormalized r (h ω) z₀, τ z₀ (Y ω)))).map
          (Prod.map (restrictTo (ballO (0 : ℂ) 1)) id) =
          ((P.map h).prod (P.map Y)).map (Prod.map (restrictTo (ballO (0 : ℂ) 1)) id) := by
        rw [e]
      have hpm : Measurable fun ω => (caseNormalized r (h ω) z₀, τ z₀ (Y ω)) :=
        ((measurable_caseNormalized_left r z₀).comp hh.1.measurable).prodMk
          ((measurable_transform_right hτ z₀).comp hY)
      rw [Measure.map_map ((measurable_restrictTo _).prodMap measurable_id) hpm] at e2
      rw [hν]
      have e3 : (P.map h).prod (P.map Y) = P.map (fun ω => (h ω, Y ω)) :=
        (hind.map_prod_eq_prod_map_map hh.1.measurable.aemeasurable hY.aemeasurable).symm
      rw [e3, Measure.map_map ((measurable_restrictTo _).prodMap measurable_id)
        (hh.1.measurable.prodMk hY)] at e2
      exact e2
    have hset : {ω | radAvg r (h ω) z₀ ∈ B ∧
        (restrictTo (ballO (0 : ℂ) 1) (caseNormalized r (h ω) z₀), τ z₀ (Y ω)) ∈ S} =
        (fun ω => radAvg r (h ω) z₀) ⁻¹' B ∩ (fun ω =>
          (restrictTo (ballO (0 : ℂ) 1) (caseNormalized r (h ω) z₀), τ z₀ (Y ω))) ⁻¹' S :=
      rfl
    rw [hset, hmeas, ← hlaw', Measure.map_apply hlocm hS]
    rfl
  refine (Measure.prod_eq fun E S hE hS => ?_).symm
  rw [Measure.map_apply (hA.prodMk hL) (hE.prod hS), Measure.map_apply hA hE]
  have hset1 : MeasurableSet ((fun p : Ω × ℂ => ((p.2, radAvg r (h p.1) p.2),
      (restrictTo (ballO (0 : ℂ) 1) (caseNormalized r (h p.1) p.2), τ p.2 (Y p.1)))) ⁻¹'
      (E ×ˢ S)) := (hA.prodMk hL) (hE.prod hS)
  have hset2 : MeasurableSet ((fun p : Ω × ℂ => (p.2, radAvg r (h p.1) p.2)) ⁻¹' E) := hA hE
  rw [Measure.prod_apply_symm hset1, Measure.prod_apply_symm hset2, ← lintegral_mul_const _
    (measurable_measure_prodMk_right hset2)]
  refine lintegral_congr_ae ?_
  filter_upwards [hsupp] with z₀ hz
  have hEz : MeasurableSet {a : ℝ | (z₀, a) ∈ E} := measurable_prodMk_left hE
  have h1 := hslice z₀ hz {a : ℝ | (z₀, a) ∈ E} S hEz hS
  exact h1

end LawR

end MatedCRTHarmonic.GMSCase
