import QuantumZipper.Proofs.Section5.Prop16NodeB2Rep

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Proposition 1.6, node `Prop16PalmGlobalStmt`: measurability of the Palm-shifted coordinates

`measurable_palmRawCoords`: the Palm-shifted raw coordinates
`(ω, x) ↦ ((h0 + X ω + (γ/2) G_D(x, ·))(μ_j))_j` are jointly measurable on `Ω × ℝ` (for **every**
`x`, including the junk values of `mixedGreenSample` off the free arc).

Route (own elementary argument; no published counterpart, the paper works with the continuum
Green function): for a fixed finite measure `μ` and radius `r`, the squared dual norm
`x ↦ ‖μ + fc(x, r)‖²_V` is a supremum over the (continuous) test functions `f ∈ V` of the
continuous functions `x ↦ (∫ f d(μ + fc(x,r)))² / (f,f)_∇`, hence lower semicontinuous and Borel;
so `x ↦ dualCov(μ, fc(x, r))` is Borel, and `mixedGreenSample · μ`, a `limUnder` of these, is
Borel (`StronglyMeasurable.limUnder`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal

namespace QuantumZipper

namespace Prop16Asm

/-- Continuous functions are integrable against folded circles centred in `ℍ̄`. -/
theorem integrable_foldedCircle_of_continuous_pg {g : ℂ → ℝ} (hg : Continuous g) {w : ℂ}
    (hw : w ∈ Hbar) {t : ℝ} (ht : 0 < t) : Integrable g (foldedCircle w t) := by
  have hK : IsCompact (closedBall w t ∩ Hbar) :=
    (isCompact_closedBall w t).inter_right isClosed_Hbar
  have hI : IntegrableOn g (closedBall w t ∩ Hbar) (foldedCircle w t) :=
    hg.continuousOn.integrableOn_compact hK
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem
    (ae_iff.2 (K3.foldedCircle_compl_eq_zero hw ht.le))] at hI

/-- `x ↦ ∫ f d(μ + fc(x, r))` is continuous for continuous `f` (junk `0` included). -/
theorem continuous_integral_add_fc_pg {f : ℂ → ℝ} (hf : Continuous f) (μ : Measure ℂ) {r : ℝ}
    (hr : 0 < r) : Continuous fun x : ℝ => ∫ z, f z ∂(μ + foldedCircle (x : ℂ) r) := by
  have hfc : ∀ x : ℝ, Integrable f (foldedCircle (x : ℂ) r) := fun x =>
    integrable_foldedCircle_of_continuous_pg hf (show (0 : ℝ) ≤ ((x : ℂ)).im by simp) hr
  have hc : Continuous fun x : ℝ => ∫ z, f z ∂foldedCircle (x : ℂ) r :=
    (TwoPoint.continuous_integral_foldedCircle hf).comp
      (Complex.continuous_ofReal.prodMk continuous_const)
  by_cases hμ : Integrable f μ
  · have e : (fun x : ℝ => ∫ z, f z ∂(μ + foldedCircle (x : ℂ) r)) =
        fun x : ℝ => ∫ z, f z ∂μ + ∫ z, f z ∂foldedCircle (x : ℂ) r := by
      funext x; exact integral_add_measure hμ (hfc x)
    rw [e]; exact continuous_const.add hc
  · have e : (fun x : ℝ => ∫ z, f z ∂(μ + foldedCircle (x : ℂ) r)) = fun _ : ℝ => 0 := by
      funext x
      refine integral_undef fun h => hμ ?_
      exact (integrable_add_measure.1 h).1
    rw [e]; exact continuous_const

/-- `x ↦ ‖μ + fc(x, r)‖²_V` is Borel when every test function of `V` is continuous. -/
theorem measurable_dualNormSq_add_fc_pg (D : Set ℂ) {V : Set (ℂ → ℝ)}
    (hV : ∀ f ∈ V, Continuous f) (μ : Measure ℂ) {r : ℝ} (hr : 0 < r) :
    Measurable fun x : ℝ => dualNormSq D V (μ + foldedCircle (x : ℂ) r) := by
  refine LowerSemicontinuous.measurable ?_
  unfold dualNormSq
  refine lowerSemicontinuous_iSup fun f => lowerSemicontinuous_iSup fun hf => ?_
  refine Continuous.lowerSemicontinuous ?_
  exact ENNReal.continuous_ofReal.comp
    (((continuous_integral_add_fc_pg (hV f hf.1) μ hr).pow 2).div_const _)

theorem continuous_of_mem_mixedSpace_pg {D S : Set ℂ} :
    ∀ f ∈ mixedSpace D S, Continuous f := fun _ hf => hf.1.continuous

/-- `x ↦ dualCov(μ, fc(x, r))` is Borel on the mixed test space. -/
theorem measurable_dualCov_fc_pg (D S : Set ℂ) (μ : Measure ℂ) {r : ℝ} (hr : 0 < r) :
    Measurable fun x : ℝ => dualCov D (mixedSpace D S) μ (foldedCircle (x : ℂ) r) := by
  unfold dualCov
  have h1 := measurable_dualNormSq_add_fc_pg D (continuous_of_mem_mixedSpace_pg (D := D) (S := S))
    μ hr
  have h2 := measurable_dualNormSq_add_fc_pg D (continuous_of_mem_mixedSpace_pg (D := D) (S := S))
    0 hr
  simp only [zero_add] at h2
  exact ((h1.ennreal_toReal.sub measurable_const).sub h2.ennreal_toReal).div_const _

/-- **The Palm shift direction is Borel in the boundary point.** -/
theorem measurable_mixedGreenSample_pg (D S : Set ℂ) (μ : Measure ℂ) :
    Measurable fun x : ℝ => mixedGreenSample D S x μ := by
  unfold mixedGreenSample
  exact (StronglyMeasurable.limUnder (l := atTop) (f := fun (k : ℕ) (x : ℝ) =>
    dualCov D (mixedSpace D S) μ (foldedCircle (x : ℂ) (radius k)))
    fun k => (measurable_dualCov_fc_pg D S μ (radius_pos k)).stronglyMeasurable).measurable

/-- **Joint measurability of the Palm-shifted raw coordinates.** -/
theorem measurable_palmRawCoords {γ : ℝ} {D : Set ℂ} {c d : ℝ} {h0 : ℂ → ℝ} {Ω : Type}
    [MeasurableSpace Ω] {X : Ω → FieldSample} (hXm : ∀ ν : Measure ℂ, Measurable fun ω => X ω ν)
    (μ : ℕ → Measure ℂ) : Measurable (palmRawCoords γ D c d h0 X μ) := by
  refine measurable_pi_iff.2 fun j => ?_
  have e : (fun p : Ω × ℝ => palmRawCoords γ D c d h0 X μ p j) = fun p =>
      ofFun h0 (μ j) + (X p.1 (μ j) +
        γ / 2 * mixedGreenSample D (realSet (Icc c d)) p.2 (μ j)) := by
    funext p
    simp only [palmRawCoords, palmMixedField, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [e]
  exact measurable_const.add (((hXm (μ j)).comp measurable_fst).add (measurable_const.mul
    ((measurable_mixedGreenSample_pg D _ (μ j)).comp measurable_snd)))

end Prop16Asm

end QuantumZipper
