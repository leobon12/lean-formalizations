/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.MartMeans2Rand
import InteractingSLE.Spec.Coupling.MartMeans2Sub
import InteractingSLE.Spec.Coupling.MartMeans
import InteractingSLE.Spec.Coupling.WholeField2Kernel

/-!
# The coupling clause transported by a random conformal chart

Packet PROVE-CPL-MART2, part (2). Lemma 7.1 (Specification p. 223–225) maps the middle flow line of a pocket `C` to
`ℍ` by the pocket chart `ψ` and needs "the joint pair with `h_ψ` has the original coupling specification", where
`h_ψ = h ∘ ψ⁻¹ − χ arg (ψ⁻¹)′` is the field in the chart coordinate (rule (1.4); the frozen `IsChartTransport`).
The source obtains, from Lemma 6.2's history locality and Remark 6.7's means, the conditional law of `h` **in the
original domain**: conditionally on `𝓖_τ`, on the remaining domain `inv_ω(ℍ ∖ K_τ)` the field is the coupling mean
written back in the original coordinate plus a zero-boundary GFF on that domain. This file states that form
(`IsChartCouplingCharFun`) and proves that it transports to the coupling clause `IsCouplingCharFun` for every chart
transport `h'` of `h` (`isCouplingCharFun_of_isChartTransport`).

The steps: `h'(φ') = h(pushTest φ') + S`, with `S = a ∫ φ' + k ∫ (lift ∘ inv) φ'` measurable for `𝓖₀` (pulled out of the
conditional expectation); `pushTest φ'` is a `𝓖₀`-measurable random test function supported in `inv_ω(ℍ ∖ K_τ)` on the
event `{supp φ' ∩ K_τ = ∅}`, so the conditional characteristic functional is evaluated there by
`condExp_cexp_apply_ae_eq_of_local`; the mean transforms by the change of variables `integral_mul_pushTest` and
`fwd ∘ inv = id`, and the variance by conformal invariance (`zeroGFFTestCov_pushTest_sub`) and
`loewnerGreenEnergy_rpath_eq_zeroGFFTestCov`.

## Main results

* `IsChartCouplingCharFun` (def): the coupling clause in the original domain of a random chart;
* **`isCouplingCharFun_of_isChartTransport`**: it implies `IsCouplingCharFun` for the transported field.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace
open QuantumZipper (H zeroGFFTestCov fwdHull)
open LQGMetric (TestOn DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Coupling

namespace MartMeans2

open Ito

variable {nL nR : ℕ}

/-! ### The coupling clause in the original domain of a random chart -/

/-- **The coupling clause written through a random chart** `c ω = (fwd, inv, lift)` with height shift `a` and lift
coefficient `k` (rule (1.4), `h' = h ∘ inv + a + k · lift ∘ inv`): for every stopping time `τ < ζ` of `𝓖`, every
choice `u` of the bounded harmonic extensions at `τ`, and every test function `φ` supported in the remaining domain
`inv_ω(ℍ ∖ K_τ)`, conditionally on `𝓖_τ` the pairing `(h, φ)` has the characteristic function of
`(m_τ, φ) + (h̃, φ)`, where `m_τ = 𝔥_τ ∘ fwd − a − k · lift` is the coupling mean written back in the original
coordinate and `h̃` is a zero-boundary GFF on `inv_ω(ℍ ∖ K_τ)`. -/
def IsChartCouplingCharFun (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) (𝓖 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (c : Ω → Chart) (a k : ℝ) (h : Ω → DistOn upperHalfPlaneOpens) :
    Prop :=
  ∀ (τ : Ω → WithTop ℝ≥0) (hτ : IsStoppingTime 𝓖 τ), (∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω) →
    ∀ u : Ω → ℂ → ℝ,
      (∀ ω, IsBoundedHarmonicExtension
          (forceBoundaryData κ ρL ρR (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
            (fun i => VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω))
          (forceJumpSet (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
            (fun i => VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω))
          (u ω)) →
      ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P,
        tsupport φ ⊆ (c ω).2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) →
          condExp hτ.measurableSpace P (fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ))) ω =
            Complex.exp (Complex.I * ((∫ z, (couplingMean κ (fun s : ℝ => W s.toNNReal ω)
                ((τ ω).untopD 0 : ℝ≥0) (u ω) ((c ω).1 z) - a - k * (c ω).2.2 z) * φ z : ℝ) : ℂ) -
              (((1 / 2 : ℝ) * zeroGFFTestCov ((c ω).2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω)
                ((τ ω).untopD 0 : ℝ≥0))) φ φ : ℝ) : ℂ))

/-! ### Deterministic helpers -/

section Helpers

/-- `ℍ ∖ K_t` is open for a driver continuous before `ζ > t`. -/
theorem isOpen_H_diff_fwdHull_rpath {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ})
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) : IsOpen (H \ fwdHull (rpath w) t) := by
  obtain ⟨t₂, htt₂, ht₂ζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 ht
  have htt₂' : (t : ℝ) < t₂ := by exact_mod_cast htt₂
  have hc := continuous_clampDrv (W := rpath w) t₂.coe_nonneg (continuousOn_rpath hw ht₂ζ)
  have heq : fwdHull (rpath w) t = fwdHull (clampDrv (rpath w) t₂) t :=
    fwdHull_eq_of_eqOn t.coe_nonneg htt₂' fun r hr => (clampDrv_eqOn (W := rpath w) (T := (t₂ : ℝ)) hr).symm
  rw [heq]
  exact QuantumZipper.FwdHolo.isOpen_compl_fwdHull hc t.coe_nonneg

/-- A function continuous on a set containing the support of a test function, times the test function, is
integrable. -/
theorem integrable_mul_test_of_continuousOn {f : ℂ → ℝ} {S : Set ℂ} (hf : ContinuousOn f S)
    (φ : TestOn upperHalfPlaneOpens) (hS : tsupport φ ⊆ S) : Integrable (fun z => f z * φ z) := by
  have hI : IntegrableOn (fun z => f z * φ z) (tsupport φ) :=
    ((hf.mono hS).mul φ.continuous.continuousOn).integrableOn_compact φ.hasCompactSupport.isCompact
  refine (integrableOn_iff_integrable_of_support_subset fun z hz => ?_).1 hI
  by_contra hns
  exact hz (by simp only [image_eq_zero_of_notMem_tsupport hns, mul_zero])

end Helpers

/-! ### The transport theorem -/

section Transport

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓖 : Filtration ℝ≥0 mΩ} {κ : ℝ}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {c : Ω → Chart} {a k : ℝ}
  {h h' : Ω → DistOn upperHalfPlaneOpens}

/-- **The coupling clause transports through a random conformal chart.** Let `c ω` be conformal charts that are
`𝓖₀`-measurable (domain events, forward maps and lifts on the domain), with lifts continuous on the chart domains,
let `h` be a random distribution satisfying the coupling clause in the original domain of the chart
(`IsChartCouplingCharFun`), and suppose that almost surely `W₀ = 0` and `W` is continuous before `ζ`. Then every chart
transport `h' = h ∘ inv + a + k · lift ∘ inv` (frozen `IsChartTransport` with `σ = 1`) satisfies the coupling clause
`IsCouplingCharFun` on `ℍ`. -/
theorem isCouplingCharFun_of_isChartTransport [IsProbabilityMeasure P] (hc : ∀ ω, (c ω).IsConformal)
    (hdom : ∀ z, MeasurableSet[𝓖 0] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hliftc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom) (hh : Measurable h)
    (hpath : ∀ᵐ ω ∂P, W 0 ω = 0 ∧ ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hcf : IsChartCouplingCharFun κ ρL ρR P 𝓖 W VL VR ζ c a k h)
    (ht : ∀ ω, IsChartTransport (c ω) 1 a k (h ω) (h' ω)) :
    MartMeans.IsCouplingCharFun κ ρL ρR P 𝓖 W VL VR ζ h' := by
  intro τ hτ hlt u hu φ'
  have h𝒢 : hτ.measurableSpace ≤ mΩ := hτ.measurableSpace_le
  have h0τ : 𝓖 0 ≤ hτ.measurableSpace := hτ.le_measurableSpace_of_const_le fun _ => bot_le
  -- the transported test function and the shift
  have hT : ∀ z, Measurable[hτ.measurableSpace] fun ω => Chart.pushTest (hc ω) φ' z := fun z =>
    (@Chart.measurable_pushTest_apply Ω (𝓖 0) c hc hdom hfwd φ' z).mono h0τ le_rfl
  have hS : Measurable[hτ.measurableSpace] fun ω => Chart.chartTransport (hc ω) 1 a k 0 φ' := by
    have := @Chart.measurable_chartTransport_random' Ω (𝓖 0) c hc hdom hfwd hliftm hliftc
      (fun _ => 0) measurable_const 1 a k
    exact ((LQGMetric.measurable_distOn_apply φ').comp this).mono h0τ le_rfl
  have hℓ : ∀ ω, LocallyIntegrableOn (fun w => (c ω).2.2 ((c ω).2.1 w)) H := fun ω =>
    Chart.locallyIntegrableOn_of_continuousOn ((hc ω).continuousOn_lift_inv (hliftc ω))
  have hSval : ∀ ω, Chart.chartTransport (hc ω) 1 a k 0 φ' =
      a * (∫ w, φ' w) + k * ∫ w, (c ω).2.2 ((c ω).2.1 w) * φ' w := fun ω => by
    rw [Chart.chartTransport_apply (hc ω) (hℓ ω)]
    simp only [zero_apply, mul_zero, zero_add]
  have hsplit : ∀ ω, h' ω φ' = h ω (Chart.pushTest (hc ω) φ') + Chart.chartTransport (hc ω) 1 a k 0 φ' :=
    fun ω => by
      rw [IsChartTransport.apply_eq (hc ω) (ht ω) φ', hSval ω]
      ring
  -- pulling out the `𝓖_τ`-measurable shift
  have hTm : Measurable fun ω => h ω (Chart.pushTest (hc ω) φ') :=
    RandomTest.measurable_apply_of_forall_measurable hh fun z => (hT z).mono h𝒢 le_rfl
  have hpull : P[fun ω => Complex.exp (Complex.I * (h' ω φ' : ℂ)) | hτ.measurableSpace] =ᵐ[P]
      fun ω => Complex.exp (Complex.I * (Chart.chartTransport (hc ω) 1 a k 0 φ' : ℂ)) *
        P[fun ω => Complex.exp (Complex.I * (h ω (Chart.pushTest (hc ω) φ') : ℂ)) | hτ.measurableSpace] ω := by
    have hE : StronglyMeasurable[hτ.measurableSpace]
        fun ω => Complex.exp (Complex.I * (Chart.chartTransport (hc ω) 1 a k 0 φ' : ℂ)) :=
      (@GFF.measurable_exp_I_mul Ω hτ.measurableSpace _ hS).stronglyMeasurable
    have hF : Integrable (fun ω => Complex.exp (Complex.I * (h ω (Chart.pushTest (hc ω) φ') : ℂ))) P :=
      GFF.integrable_exp_I_mul hTm
    have hEF : Integrable (fun ω => Complex.exp (Complex.I * (Chart.chartTransport (hc ω) 1 a k 0 φ' : ℂ)) *
        Complex.exp (Complex.I * (h ω (Chart.pushTest (hc ω) φ') : ℂ))) P :=
      hF.bdd_mul (hE.mono h𝒢).aestronglyMeasurable
        (Eventually.of_forall fun ω => (Complex.norm_exp_I_mul_ofReal _).le)
    have e : (fun ω => Complex.exp (Complex.I * (h' ω φ' : ℂ))) = fun ω =>
        Complex.exp (Complex.I * (Chart.chartTransport (hc ω) 1 a k 0 φ' : ℂ)) *
          Complex.exp (Complex.I * (h ω (Chart.pushTest (hc ω) φ') : ℂ)) := by
      funext ω
      rw [hsplit ω, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [e]
    have hp := condExp_bilin_of_stronglyMeasurable_left (ContinuousLinearMap.mul ℝ ℂ) hE
      (by simpa [ContinuousLinearMap.mul_apply'] using hEF) hF
    simpa [ContinuousLinearMap.mul_apply'] using hp
  -- the random remaining domains and the conditional characteristic functional in the chart
  set O : Ω → Opens ℂ := fun ω => ⟨interior (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)),
    isOpen_interior⟩ with hOdef
  have hOH : ∀ ω, (O ω : Set ℂ) ⊆ H := fun ω => interior_subset.trans sdiff_subset
  have hUo : ∀ ω, IsOpen ((c ω).2.1 '' (O ω : Set ℂ)) := fun ω =>
    (hc ω).isOpen_image_of_subset (O ω).isOpen (hOH ω)
  have hUH : ∀ ω, (c ω).2.1 '' (O ω : Set ℂ) ⊆ (upperHalfPlaneOpens : Set ℂ) := fun ω =>
    (image_mono (hOH ω)).trans (hc ω).2.1.image_subset
  have hUdom : ∀ ω, (c ω).2.1 '' (O ω : Set ℂ) ⊆ (c ω).dom := fun ω => by
    rw [(hc ω).coe_dom]; exact image_mono (hOH ω)
  -- the good event
  have hgood : ∀ᵐ ω ∂P, W 0 ω = 0 ∧ ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧
      (((τ ω).untopD 0 : ℝ≥0) : ℝ≥0∞) < ζ ω := by
    filter_upwards [hpath, hlt] with ω h1 h2
    refine ⟨h1.1, h1.2, ?_⟩
    obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt h2)
    rw [← hs] at h2 ⊢
    rw [WithTop.untopD_coe]
    exact h2
  have hOeq : ∀ ω, W 0 ω = 0 ∧ ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧
      (((τ ω).untopD 0 : ℝ≥0) : ℝ≥0∞) < ζ ω →
      (O ω : Set ℂ) = H \ fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) := fun ω hω =>
    (isOpen_H_diff_fwdHull_rpath (w := fun t => W t ω) hω.2.1 hω.2.2).interior_eq
  have hmc : ∀ ω, W 0 ω = 0 ∧ ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧
      (((τ ω).untopD 0 : ℝ≥0) : ℝ≥0∞) < ζ ω →
      ContinuousOn (fun z => couplingMean κ (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) (u ω)
        ((c ω).1 z) - a - k * (c ω).2.2 z) ((c ω).2.1 '' (O ω : Set ℂ)) := fun ω hω => by
    have hr := continuousOn_rpath (u := fun t => W t ω) hω.2.1 hω.2.2
    have hcm := continuousOn_couplingMean κ hr (hu ω).1
    have hmaps : MapsTo (c ω).1 ((c ω).2.1 '' (O ω : Set ℂ)) (hullDom (fun t => W t ω) ((τ ω).untopD 0)) := by
      rintro _ ⟨w, hw, rfl⟩
      rw [(hc ω).2.2 w (hOH ω hw)]
      rw [hOeq ω hω] at hw
      exact mem_hullDom hr hw.1 hw.2
    exact ((hcm.comp ((hc ω).differentiableOn_fwd.continuousOn.mono (hUdom ω)) hmaps).sub
      continuousOn_const).sub (continuousOn_const.mul ((hliftc ω).mono (hUdom ω)))
  -- the conditional characteristic functional at the random test function
  have hRT := condExp_cexp_apply_ae_eq_of_local (P := P) h𝒢 hh hUo hUH
    (Ψ := fun ω φ => Complex.exp (Complex.I * ((∫ z, (couplingMean κ (fun s : ℝ => W s.toNNReal ω)
      ((τ ω).untopD 0 : ℝ≥0) (u ω) ((c ω).1 z) - a - k * (c ω).2.2 z) * φ z : ℝ) : ℂ) -
        (((1 / 2 : ℝ) * zeroGFFTestCov ((c ω).2.1 '' (O ω : Set ℂ)) φ φ : ℝ) : ℂ)))
    (by
      filter_upwards [hgood] with ω hω R hR
      have hRH : R ≤ upperHalfPlaneOpens := fun x hx => hUH ω (hR hx)
      obtain ⟨μ, hμP, hμ⟩ := exists_gaussLocalLaw (U := (c ω).imageOpens (O ω))
        ((hc ω).imageOpens_subset_H (hOH ω)) (R := R) (by rw [(hc ω).coe_imageOpens (hOH ω)]; exact hR)
        (((hmc ω hω).mono hR).locallyIntegrableOn R.isOpen.measurableSet)
      refine ⟨μ, hμP, fun ψ => ?_⟩
      rw [hμ ψ, (hc ω).coe_imageOpens (hOH ω), GFF.coe_testIncl hRH ψ])
    (fun φ => by
      filter_upwards [hcf τ hτ hlt u hu φ, hgood] with ω h1 hω hsupp
      rw [hOeq ω hω] at hsupp ⊢
      exact h1 hsupp)
    hT
  -- assembly on the event `supp φ' ∩ K_τ = ∅`
  filter_upwards [hpull, hRT, hgood] with ω hpω hrω hω hdisj
  have hφO : tsupport φ' ⊆ (O ω : Set ℂ) := by
    rw [hOeq ω hω]
    exact fun z hz => ⟨φ'.tsupport_subset hz, fun hK => Set.disjoint_left.1 hdisj hz hK⟩
  have hTU := (hc ω).tsupport_pushTest_subset_image (hOH ω) φ' hφO
  rw [hpω, hrω hTU]
  have hvar : zeroGFFTestCov ((c ω).2.1 '' (O ω : Set ℂ)) (Chart.pushTest (hc ω) φ') (Chart.pushTest (hc ω) φ') =
      loewnerGreenEnergy (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) φ' := by
    rw [(hc ω).zeroGFFTestCov_pushTest_sub (hOH ω) φ' hφO, hOeq ω hω]
    exact (WholeField.loewnerGreenEnergy_rpath_eq_zeroGFFTestCov (w := fun t => W t ω) hω.2.1 hω.1 hω.2.2
      φ' hdisj).symm
  -- the mean
  have hr := continuousOn_rpath (u := fun t => W t ω) hω.2.1 hω.2.2
  have hI1 : Integrable fun w => couplingMean κ (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) (u ω) w *
      φ' w := by
    refine integrable_mul_test_of_continuousOn (continuousOn_couplingMean κ hr (hu ω).1) φ' fun z hz => ?_
    have hz' := hφO hz
    rw [hOeq ω hω] at hz'
    exact mem_hullDom hr hz'.1 hz'.2
  have hI0 : Integrable fun w => φ' w := φ'.continuous.integrable_of_hasCompactSupport φ'.hasCompactSupport
  have hI2 : Integrable fun w => (c ω).2.2 ((c ω).2.1 w) * φ' w :=
    integrable_mul_test_of_continuousOn ((hc ω).continuousOn_lift_inv (hliftc ω)) φ' φ'.tsupport_subset
  have hpt : ∀ w, (couplingMean κ (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) (u ω)
      ((c ω).1 ((c ω).2.1 w)) - a - k * (c ω).2.2 ((c ω).2.1 w)) * φ' w =
      couplingMean κ (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) (u ω) w * φ' w - a * φ' w -
        k * ((c ω).2.2 ((c ω).2.1 w) * φ' w) := fun w => by
    by_cases hw : w ∈ H
    · rw [(hc ω).2.2 w hw]
      ring
    · rw [image_eq_zero_of_notMem_tsupport fun h => hw (φ'.tsupport_subset h)]
      ring
  have hmean : (∫ z, (couplingMean κ (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) (u ω) ((c ω).1 z) -
      a - k * (c ω).2.2 z) * Chart.pushTest (hc ω) φ' z) =
      (∫ w, couplingMean κ (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) (u ω) w * φ' w) -
        a * (∫ w, φ' w) - k * ∫ w, (c ω).2.2 ((c ω).2.1 w) * φ' w := by
    have hI12 : Integrable fun w => couplingMean κ (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) (u ω) w *
        φ' w - a * φ' w := hI1.sub (hI0.const_mul a)
    rw [Chart.integral_mul_pushTest (hc ω) φ', integral_congr_ae (Eventually.of_forall hpt),
      integral_sub hI12 (hI2.const_mul k), integral_sub hI1 (hI0.const_mul a),
      integral_const_mul, integral_const_mul]
  rw [hvar, hmean, hSval ω, ← Complex.exp_add]
  congr 1
  push_cast
  ring

end Transport

/-! ### Consistency: the identity chart -/

section Identity

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓖 : Filtration ℝ≥0 mΩ} {κ : ℝ}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → DistOn upperHalfPlaneOpens}

/-- **Consistency of `IsChartCouplingCharFun`**: in the identity chart (no height shift, zero lift) it is the coupling
clause `IsCouplingCharFun` itself, for a driver that almost surely starts at `0` and is continuous before `ζ` (the
energy `E_τ(φ)` is `‖φ‖²_{H⁻¹(ℍ ∖ K_τ)}`, `loewnerGreenEnergy_rpath_eq_zeroGFFTestCov`). -/
theorem isChartCouplingCharFun_id_of_isCouplingCharFun
    (hpath : ∀ᵐ ω ∂P, W 0 ω = 0 ∧ ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hcf : MartMeans.IsCouplingCharFun κ ρL ρR P 𝓖 W VL VR ζ h) :
    IsChartCouplingCharFun κ ρL ρR P 𝓖 W VL VR ζ (fun _ => Chart.id) 0 0 h := by
  intro τ hτ hlt u hu φ
  filter_upwards [hcf τ hτ hlt u hu φ, hpath, hlt] with ω h1 hp hτζ hsupp
  have hτζ' : (((τ ω).untopD 0 : ℝ≥0) : ℝ≥0∞) < ζ ω := by
    obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt hτζ)
    rw [← hs] at hτζ ⊢
    rw [WithTop.untopD_coe]
    exact hτζ
  have himg : (Chart.id.2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0))) =
      H \ fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) := image_id' _
  rw [himg] at hsupp
  have hdisj : Disjoint (tsupport φ) (fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) :=
    Set.disjoint_left.2 fun z hz hK => (hsupp hz).2 hK
  rw [h1 hdisj, himg, ← WholeField.loewnerGreenEnergy_rpath_eq_zeroGFFTestCov (w := fun t => W t ω) hp.2 hp.1
    hτζ' φ hdisj]
  simp only [Chart.id, sub_zero, zero_mul]

end Identity

end MartMeans2

end Coupling

end InteractingSLE
