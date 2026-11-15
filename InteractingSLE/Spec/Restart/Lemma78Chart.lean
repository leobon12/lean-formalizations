/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.ChartMeasReduce
import InteractingSLE.GFF.PushforwardLaw

/-!
# (R1) in the chart: the conditional law of the chart field

Packet PROVE-RESTART-CPL4, item (R1) of `FirstContactChartDataFCStatement` (Lemma 7.8, p. 290: conditionally on the
retained history, `h|_D` is a GFF on `D` with mean `𝔤 ∘ φ − χ arg φ′`). In the chart this is the statement that the
chart field `Hc = h ∘ ψ + χ (lift ∘ ψ)` has, conditionally on `𝒢`, the characteristic functional of the GFF on `ℍ`
with the word mean of the chart datum (`gaussCF`).

Here (R1) is reduced, for any `𝒢`-measurable random conformal chart, to its two source ingredients:

* **marked locality off the union** (Lemma 7.7, GR1/GR2): conditionally on `𝒢`, for test functions supported in the
  chart domain `D_ω`, `h` has the characteristic functional `exp(i M_ω(φ) − ½ ‖φ‖²_{H⁻¹(D_ω)})` (the form of the frozen
  optional hull coupling off the hull);
* **the mean identification** (Lemma 7.8's formula `𝒞_K = 𝔤 ∘ φ − χ arg φ′`, Aux. 27, 29, 57, 78, 80): the
  chart transport of the conditional mean `M_ω` is the word mean of the chart datum `β ω`.

The proof: the lift term `χ ∫ (lift ∘ ψ) φ'` is `𝒢`-measurable and is pulled out of the conditional expectation;
PROVE-PUSHFWD's `Chart.condExp_cexp_pullField_random_of_subset` transports the conditional law of `h` on `D_ω` to
that of `h ∘ ψ` on `ℍ` (conformal invariance of the zero-boundary covariance).

## Main results

* `chartTransport_apply_eq_pullField_add`;
* **`condExp_cexp_chartTransport_random_of_subset`**: the conditional characteristic functional of the chart field;
* **`ae_condExp_cexp_chartTransport_eq_gaussCF`**: (R1) from marked locality and the mean identification.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H zeroGFFTestCov)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE

namespace Restart

/-- The chart transport with `σ = 1`, `a = 0` is the pulled-back field plus the transport of `0` (the lift term). -/
theorem chartTransport_apply_eq_pullField_add {c : Chart} (hc : c.IsConformal) (k : ℝ) (h : DistOn upperHalfPlaneOpens)
    (φ : TestOn upperHalfPlaneOpens) :
    Chart.chartTransport hc 1 0 k h φ = Chart.pullField hc h φ + Chart.chartTransport hc 1 0 k 0 φ := by
  rw [Chart.chartTransport_apply', Chart.chartTransport_apply', Chart.pullField_apply]
  simp

theorem norm_cexp_I_mul_ofReal (x : ℝ) : ‖Complex.exp (Complex.I * (x : ℂ))‖ = 1 := by
  rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I x

section Cond

variable {Ω : Type*} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **The conditional characteristic functional of the chart field.** For a `𝒢`-measurable random conformal chart
with continuous lifts, if conditionally on `𝒢` the field `h` has, on test functions supported in the chart domain,
the characteristic functional `exp(i M_ω(φ) − ½ ‖φ‖²_{H⁻¹(D_ω)})`, then the chart field `chartTransport 1 0 k h` has,
conditionally on `𝒢`, the characteristic functional `exp(i (chartTransport 1 0 k M_ω)(φ') − ½ ‖φ'‖²_{H⁻¹(ℍ)})` for
**every** test function `φ'` on `ℍ`. -/
theorem condExp_cexp_chartTransport_random_of_subset (h𝒢 : 𝒢 ≤ mΩ) {c : Ω → Chart}
    (hc : ∀ ω, (c ω).IsConformal) (hdom : ∀ z, MeasurableSet[𝒢] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[𝒢] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable[𝒢] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hliftc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom) {h M : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h)
    (k : ℝ)
    (hcond : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, tsupport φ ⊆ (c ω).dom →
      P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | 𝒢] ω =
        Complex.exp (Complex.I * (M ω φ : ℂ) -
          (((1 / 2 : ℝ) * zeroGFFTestCov ((c ω).dom : Set ℂ) φ φ : ℝ) : ℂ)))
    (φ : TestOn upperHalfPlaneOpens) :
    P[fun ω => Complex.exp (Complex.I * (Chart.chartTransport (hc ω) 1 0 k (h ω) φ : ℂ)) | 𝒢] =ᵐ[P]
      fun ω => Complex.exp (Complex.I * (Chart.chartTransport (hc ω) 1 0 k (M ω) φ : ℂ) -
        (((1 / 2 : ℝ) * zeroGFFTestCov H φ φ : ℝ) : ℂ)) := by
  -- the lift term is `𝒢`-measurable
  set T₀ : Ω → ℝ := fun ω => Chart.chartTransport (hc ω) 1 0 k 0 φ with hT₀
  have hT₀m : Measurable[𝒢] T₀ := by
    have h0 := @Chart.measurable_chartTransport_random' Ω 𝒢 c hc hdom hfwd hliftm hliftc
      (fun _ => (0 : DistOn upperHalfPlaneOpens))
      (measurable_const : Measurable[𝒢] fun _ : Ω => (0 : DistOn upperHalfPlaneOpens)) 1 0 k
    exact (LQGMetric.measurable_distOn_apply φ).comp h0
  -- the full chart field is measurable
  have hHm : Measurable fun ω => Chart.chartTransport (hc ω) 1 0 k (h ω) φ := by
    have h1 := Chart.measurable_chartTransport_random' hc (fun z => h𝒢 _ (hdom z))
      (fun z => (hfwd z).mono h𝒢 le_rfl) (fun z => (hliftm z).mono h𝒢 le_rfl) hliftc hh 1 0 k
    exact (LQGMetric.measurable_distOn_apply φ).comp h1
  set A : Ω → ℝ := fun ω => Chart.pullField (hc ω) (h ω) φ with hA
  have hsplit : ∀ ω, Chart.chartTransport (hc ω) 1 0 k (h ω) φ = A ω + T₀ ω := fun ω =>
    chartTransport_apply_eq_pullField_add (hc ω) k (h ω) φ
  have hAm : Measurable A := by
    have : A = fun ω => Chart.chartTransport (hc ω) 1 0 k (h ω) φ - T₀ ω := by
      funext ω; rw [hsplit ω]; ring
    rw [this]; exact hHm.sub (hT₀m.mono h𝒢 le_rfl)
  -- the integrands
  set f : Ω → ℂ := fun ω => Complex.exp (Complex.I * (T₀ ω : ℂ)) with hf
  set g : Ω → ℂ := fun ω => Complex.exp (Complex.I * (A ω : ℂ)) with hg
  have hfm : StronglyMeasurable[𝒢] f :=
    (Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp hT₀m))).stronglyMeasurable
  have hgm : Measurable g := Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp hAm))
  have hgi : Integrable g P :=
    Integrable.of_bound hgm.aestronglyMeasurable 1 (Eventually.of_forall fun ω => (norm_cexp_I_mul_ofReal _).le)
  have hfgi : Integrable (fun ω => ContinuousLinearMap.mul ℝ ℂ (f ω) (g ω)) P := by
    refine Integrable.of_bound ((hfm.mono h𝒢).measurable.mul hgm).aestronglyMeasurable 1
      (Eventually.of_forall fun ω => ?_)
    simp only [ContinuousLinearMap.mul_apply', norm_mul, hf, hg, norm_cexp_I_mul_ofReal, mul_one, le_refl]
  have hpull := condExp_bilin_of_stronglyMeasurable_left (B := ContinuousLinearMap.mul ℝ ℂ) (m := 𝒢) (μ := P)
    hfm hfgi hgi
  have hkey := Chart.condExp_cexp_pullField_random_of_subset h𝒢 hc hdom hfwd hh hcond φ
  have heq : (fun ω => Complex.exp (Complex.I * (Chart.chartTransport (hc ω) 1 0 k (h ω) φ : ℂ))) =
      fun ω => ContinuousLinearMap.mul ℝ ℂ (f ω) (g ω) := by
    funext ω
    simp only [ContinuousLinearMap.mul_apply', hf, hg, hsplit ω, Complex.ofReal_add, ← Complex.exp_add]
    ring_nf
  rw [heq]
  filter_upwards [hpull, hkey] with ω h1 h2
  have h2' : P[g | 𝒢] ω = Complex.exp (Complex.I * (Chart.pullField (hc ω) (M ω) φ : ℂ) -
      (((1 / 2 : ℝ) * zeroGFFTestCov H φ φ : ℝ) : ℂ)) := h2
  rw [h1, ContinuousLinearMap.mul_apply', h2', chartTransport_apply_eq_pullField_add (hc ω) k (M ω) φ, hf,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **(R1) from marked locality and the mean identification.** If, in addition, on the event `Mset` the chart
transport of the conditional mean is the word mean of the datum `β ω`, then on `Mset` the chart field has,
conditionally on `𝒢`, the Gaussian characteristic functional `gaussCF (β ω)` (the (R1) conjunct of
`IsFirstContactChartData`). -/
theorem ae_condExp_cexp_chartTransport_eq_gaussCF (h𝒢 : 𝒢 ≤ mΩ) {c : Ω → Chart}
    (hc : ∀ ω, (c ω).IsConformal) (hdom : ∀ z, MeasurableSet[𝒢] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[𝒢] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable[𝒢] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hliftc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom) {h M : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h)
    (k : ℝ)
    (hcond : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, tsupport φ ⊆ (c ω).dom →
      P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | 𝒢] ω =
        Complex.exp (Complex.I * (M ω φ : ℂ) -
          (((1 / 2 : ℝ) * zeroGFFTestCov ((c ω).dom : Set ℂ) φ φ : ℝ) : ℂ)))
    {Mset : Set Ω} {β : Ω → BoundaryWord}
    (hmean : ∀ᵐ ω ∂P, ω ∈ Mset → ∀ φ : TestOn upperHalfPlaneOpens,
      Chart.chartTransport (hc ω) 1 0 k (M ω) φ = ∫ z, (β ω).mean z * φ z)
    (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, ω ∈ Mset →
      P[fun ω' => Complex.exp (Complex.I * (Chart.chartTransport (hc ω') 1 0 k (h ω') φ : ℂ)) | 𝒢] ω =
        gaussCF (β ω) φ := by
  filter_upwards [condExp_cexp_chartTransport_random_of_subset h𝒢 hc hdom hfwd hliftm hliftc hh k hcond φ,
    hmean] with ω h1 h2 hω
  rw [h1, h2 hω φ, gaussCF]
  have hH : (upperHalfPlaneOpens : Set ℂ) = H := rfl
  rw [hH]
  congr 1
  push_cast
  ring

/-- **(R1) for the canonical chart field.** If the path data `d` of `ChartMeas.lean` are measurable with respect to
the retained history `𝒢` (`PairData.IsMeasGood` for `𝒢`: e.g. the paths stopped at their first contact), then the
canonical chart field `hd.chartField κ h` satisfies (R1) on `Mset` as soon as marked locality off the union (`hcond`,
on the domains `D_ω`) and the mean identification (`hmean`) hold. -/
theorem ae_condExp_cexp_chartField_eq_gaussCF (h𝒢 : 𝒢 ≤ mΩ) {d : PairData Ω} (hd : @PairData.IsMeasGood Ω 𝒢 d)
    (κ : ℝ) {h M : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h)
    (hcond : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, tsupport φ ⊆ d.D ω →
      P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | 𝒢] ω =
        Complex.exp (Complex.I * (M ω φ : ℂ) - (((1 / 2 : ℝ) * zeroGFFTestCov (d.D ω) φ φ : ℝ) : ℂ)))
    {Mset : Set Ω} {β : Ω → BoundaryWord}
    (hmean : ∀ᵐ ω ∂P, ω ∈ Mset → ∀ φ : TestOn upperHalfPlaneOpens,
      Chart.chartTransport (@PairData.IsMeasGood.isConformal_chart Ω 𝒢 d hd ω) 1 0 (QuantumZipper.chiC κ) (M ω) φ =
        ∫ z, (β ω).mean z * φ z)
    (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, ω ∈ Mset →
      P[fun ω' => Complex.exp (Complex.I * (@PairData.IsMeasGood.chartField Ω 𝒢 d hd κ h ω' φ : ℂ)) | 𝒢] ω =
        gaussCF (β ω) φ := by
  obtain ⟨hdom, hfwd, hliftm⟩ := @PairData.IsMeasGood.chart_measurability Ω 𝒢 d hd
  have hcond' : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, tsupport φ ⊆ (d.chart ω).dom →
      P[fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)) | 𝒢] ω =
        Complex.exp (Complex.I * (M ω φ : ℂ) -
          (((1 / 2 : ℝ) * zeroGFFTestCov ((d.chart ω).dom : Set ℂ) φ φ : ℝ) : ℂ)) := by
    intro φ
    filter_upwards [hcond φ] with ω hω hsupp
    rw [@PairData.IsMeasGood.coe_dom_chart Ω 𝒢 d hd ω] at hsupp ⊢
    exact hω hsupp
  exact ae_condExp_cexp_chartTransport_eq_gaussCF h𝒢 (@PairData.IsMeasGood.isConformal_chart Ω 𝒢 d hd) hdom
    hfwd hliftm (@PairData.IsMeasGood.continuousOn_lift_chart Ω 𝒢 d hd) hh (QuantumZipper.chiC κ) hcond' hmean φ

end Cond

end Restart

end InteractingSLE
