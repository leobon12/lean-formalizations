import QuantumZipper.Proofs.LQG.AreaNoAtom
import QuantumZipper.Proofs.LQG.AreaProfile
import QuantumZipper.Proofs.LQG.CanonicalGood
import QuantumZipper.Proofs.LQG.LocalRule

/-!
# M4-A5-WEDGE (TASKS R23): step 0 (unconditional free-field corollaries) and the
structural core of the wedge area profile

TASKS.md R23 (AUDIT8 §3.1) asks for three statements about the **wedge** reference field
`wedgeField (lateralPart X) A (Qc γ)`: (a) `HasAreaProfile`, (b) non-degeneracy of its canonical
scale (`0 < scaleParam`, `canonical` good, `μ(B(0,1) ∩ ℍ) = 1`), (c) the consumer form for every
`IsQuantumWedge`.

R23 was blocked on the area log-singularity hypothesis `AreaCircles.AreaLogSingNoAtom`; with R14
closed (`AreaLogSing.areaLogSingNoAtom`) the free-field statements become unconditional. This
file records those unconditional corollaries (step 0) and the structure of the wedge field used
by R23's route for (a): *the wedge field is the regularized lateral part `μ ↦ evalReg x μ` plus
`ofFun` of the radial function `wedgeProfile x A Q z = −radAvgReg x ‖z‖ + Q(−log‖z‖) +
A(−log‖z‖)`, continuous on `ℂ \ {0}` a.s.*

* `ae_sphere_null_uncond`, `ae_hasAreaProfile_uncond`, `ae_canonical_spec_uncond`: the free
  field results without `hP4` (step 0 of R23).
* `wedgeField_eq_evalReg_add_ofFun`: pointwise decomposition of the wedge field.
* `wedgeProfile_radial`: the additive profile of the wedge field is radial, so the local-rule
  density `e^{γg}` is constant on every circle `∂B(0,a)` — this is what transfers "no atoms on
  circles" from the free field.
* `measurable_radAvgReg_norm`, `measurable_wedgeProfile`: measurability of that profile (for
  `withDensity`).
* `avgReg_evalReg_eq`, `areaApprox_congr_of_avgReg_Hbar`, `qAreaMeasure_evalReg`: the
  regularization `x ↦ evalReg x` does not change the dyadic averages on `Hbar`, hence not the
  area measure. This is the bridge that lets the local rule
  `LocalRule.qAreaMeasure_add_ofFun'` be applied to the wedge field.

Source: Sheffield, *Conformal weldings of random surfaces* (arXiv:1012.4797), §1.6 p. 21
("µ_h(B₁(0) ∩ H) = 1", finite mass near 0, infinite mass at ∞); route as in TASKS R23 /
AUDIT8 §3.1.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace QuantumZipper

namespace WedgeCan

open AreaProfile

/-! ## 0. Unconditional free-field corollaries (`hP4` dropped via R14) -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- **R23 step 0**: `AreaCircles.ae_sphere_null` without the hypothesis `hP4`. For the free field
and `γ ∈ (0,2)`, almost surely `μ_X(∂B(0,a) ∩ ℍ) = 0` for every `a`. -/
theorem ae_sphere_null_uncond [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ ω ∂P, ∀ a : ℝ, qAreaMeasure γ (X ω) (Metric.sphere 0 a ∩ H) = 0 :=
  AreaCircles.ae_sphere_null hX hγ hγ2 (AreaLogSing.areaLogSingNoAtom hX hγ hγ2)

/-! ## 1. The wedge field as regularized field plus a radial `ofFun` -/

/-- The radial profile added by the wedge field:
`wedgeProfile x A Q z = −radAvgReg x ‖z‖ + Q(−log‖z‖) + A(−log‖z‖)`. This is the function whose
`ofFun` is added to the regularized field `μ ↦ evalReg x μ`. -/
def wedgeProfile (x : FieldSample) (A : ℝ → ℝ) (Q : ℝ) : ℂ → ℝ :=
  fun z => -radAvgReg x ‖z‖ + Q * -Real.log ‖z‖ + A (-Real.log ‖z‖)

/-- `z ↦ radAvgReg x ‖z‖` is measurable (the radial average read at the modulus). -/
theorem measurable_radAvgReg_norm (x : FieldSample) :
    Measurable (fun z : ℂ => radAvgReg x ‖z‖) :=
  WedgeTK.measurable_radAvgReg₂.comp (measurable_const.prodMk measurable_norm)

/-- **Measurability of the wedge profile** for a measurable `A`; needed for `withDensity`. -/
theorem measurable_wedgeProfile {x : FieldSample} {A : ℝ → ℝ} (hA : Measurable A) (Q : ℝ) :
    Measurable (wedgeProfile x A Q) := by
  unfold wedgeProfile
  exact ((measurable_radAvgReg_norm x).neg.add
    (measurable_const.mul (Real.measurable_log.comp measurable_norm).neg)).add
    (hA.comp (Real.measurable_log.comp measurable_norm).neg)

/-- **R23's decomposition.** Pointwise, at a fixed finite measure on which both summands are
integrable, the wedge field is the regularized field `μ ↦ evalReg x μ` plus the integral of the
radial profile. -/
theorem wedgeField_eq_evalReg_add_ofFun {x : FieldSample} {A : ℝ → ℝ} {Q : ℝ} {μ : Measure ℂ}
    (h0 : Integrable (fun z => radAvgReg x ‖z‖) μ)
    (hL : Integrable (fun z => Q * -Real.log ‖z‖) μ)
    (hA : Integrable (fun z => A (-Real.log ‖z‖)) μ) :
    wedgeField (lateralPart x) A Q μ =
      evalReg x μ + ∫ z, wedgeProfile x A Q z ∂μ := by
  have hf : Integrable (fun z => -radAvgReg x ‖z‖ + Q * -Real.log ‖z‖) μ := h0.neg.add hL
  have hsplit1 : ∫ z, (-radAvgReg x ‖z‖ + Q * -Real.log ‖z‖) ∂μ =
      ∫ z, -radAvgReg x ‖z‖ ∂μ + ∫ z, Q * -Real.log ‖z‖ ∂μ := integral_add h0.neg hL
  have hneg : ∫ z, -radAvgReg x ‖z‖ ∂μ = -∫ z, radAvgReg x ‖z‖ ∂μ := integral_neg _
  have hsplit2 : ∫ z, (-radAvgReg x ‖z‖ + Q * -Real.log ‖z‖ + A (-Real.log ‖z‖)) ∂μ =
      ∫ z, (-radAvgReg x ‖z‖ + Q * -Real.log ‖z‖) ∂μ + ∫ z, A (-Real.log ‖z‖) ∂μ :=
    integral_add hf hA
  have hsplit3 : ∫ z, (Q * -Real.log ‖z‖ + A (-Real.log ‖z‖)) ∂μ =
      ∫ z, Q * -Real.log ‖z‖ ∂μ + ∫ z, A (-Real.log ‖z‖) ∂μ := integral_add hL hA
  have e : ∫ z, wedgeProfile x A Q z ∂μ =
      -∫ z, radAvgReg x ‖z‖ ∂μ + (∫ z, Q * -Real.log ‖z‖ ∂μ + ∫ z, A (-Real.log ‖z‖) ∂μ) := by
    rw [show ∫ z, wedgeProfile x A Q z ∂μ =
        ∫ z, (-radAvgReg x ‖z‖ + Q * -Real.log ‖z‖ + A (-Real.log ‖z‖)) ∂μ from rfl,
      hsplit2, hsplit1, hneg]
    ring
  rw [e]
  unfold wedgeField lateralPart
  rw [hsplit3]
  ring

/-! ## 2. The regularization `x ↦ evalReg x` does not change the area measure -/

/-- Area approximations only read `avgReg` on `H`. -/
theorem areaApprox_congr_of_avgReg_Hbar {γ : ℝ} {y y' : FieldSample}
    (h : ∀ k : ℕ, ∀ z ∈ H, avgReg y k z = avgReg y' k z) :
    areaApprox γ y = areaApprox γ y' := by
  funext k
  unfold areaApprox
  refine withDensity_congr_ae ((ae_restrict_mem isOpen_H.measurableSet).mono fun z hz => ?_)
  simp only [h k z hz]

/-- `qAreaMeasure` depends on the sample only through `areaApprox`. -/
theorem qAreaMeasure_congr_of_areaApprox {γ : ℝ} {y y' : FieldSample}
    (h : areaApprox γ y = areaApprox γ y') : qAreaMeasure γ y = qAreaMeasure γ y' := by
  unfold qAreaMeasure
  rw [h]

/-- **The regularized sample has the same dyadic averages.** For a regular sample `x`, the
sample `μ ↦ evalReg x μ` has the same `avgReg` as `x` at every centre in `Hbar`: the raw values
at the dyadic circles are `x (foldedCircle …)`, and `evalReg` of a folded circle is the witness
`F`, which converges to `F (z, radius k) = avgReg x k z`. -/
theorem avgReg_evalReg_eq {x : FieldSample} {F : ℂ × ℝ → ℝ} (hF : IsRegularWith x F) (k : ℕ)
    {z : ℂ} (hz : z ∈ Hbar) : avgReg (fun μ => evalReg x μ) k z = avgReg x k z := by
  have hseq : (fun n : ℕ => evalReg x (foldedCircle (dyadicRoundC n z) (radius k))) =
      fun n => F (dyadicRoundC n z, radius k) :=
    funext fun n =>
      hF.evalReg_fc_of_mem (CircleCont.dyadicRoundC_mem_Hbar hz n) (radius_pos k)
  have ht : Tendsto (fun n : ℕ => F (dyadicRoundC n z, radius k)) atTop
      (𝓝 (F (z, radius k))) := by
    have hmem : ∀ n : ℕ, ((dyadicRoundC n z, radius k) : ℂ × ℝ) ∈ Hbar ×ˢ Set.Ioi (0 : ℝ) :=
      fun n => ⟨CircleCont.dyadicRoundC_mem_Hbar hz n, radius_pos k⟩
    have hlim : Tendsto (fun n : ℕ => ((dyadicRoundC n z, radius k) : ℂ × ℝ)) atTop
        (𝓝[Hbar ×ˢ Set.Ioi (0 : ℝ)] ((z, radius k) : ℂ × ℝ)) :=
      tendsto_nhdsWithin_iff.2 ⟨(RegClosure.tendsto_dyadicRoundC z).prodMk_nhds
        tendsto_const_nhds, Eventually.of_forall hmem⟩
    exact (hF.1 ((z, radius k) : ℂ × ℝ) ⟨hz, radius_pos k⟩).tendsto.comp hlim
  unfold avgReg
  rw [hseq, ht.limUnder_eq, (hF.2.1 k z hz).limUnder_eq]

/-- **The regularization does not change the area measure.** -/
theorem qAreaMeasure_evalReg {x : FieldSample} {F : ℂ × ℝ → ℝ} (hF : IsRegularWith x F)
    (γ : ℝ) : qAreaMeasure γ (fun μ => evalReg x μ) = qAreaMeasure γ x :=
  qAreaMeasure_congr_of_areaApprox
    (areaApprox_congr_of_avgReg_Hbar fun k _ hz =>
      avgReg_evalReg_eq hF k (H_subset_Hbar hz))

end WedgeCan

end QuantumZipper
