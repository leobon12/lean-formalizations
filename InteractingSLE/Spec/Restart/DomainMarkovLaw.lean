/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.DomainMarkovEvol
import InteractingSLE.Spec.Coupling.MartMeans2Chart
import InteractingSLE.Spec.Sec7.LocalExtIRestart
import InteractingSLE.GFF.Markov

/-!
# The domain Markov step, part 4: the restarted field's conditional law on the live event

Packet PROVE-DOMAINMARKOV2. `LocalExt.isCouplingCharFun_restart` (PROVE-LOCEXT-G) gives the half-plane coupling clause
of the restarted field `h' = restartField κ (h, K)` only at restarted stopping times `τ' < ζ − T` **almost surely**,
which
is empty when `P(T ≥ ζ) > 0`; the kernel step needs it at the deterministic restarted times, on the live event. This
file removes the almost-sure hypothesis:

* **`condExp_cexp_of_isChartTransport_of_lt`**: the chart transport of
  `MartMeans2.isCouplingCharFun_of_isChartTransport`
  at **one** stopping time `τ`, localized on `{τ < ζ}`: an original-domain clause holding almost surely on `{τ < ζ}`
  transports to the half-plane clause almost surely on `{τ < ζ}`;
* **`restartField_condExp_of_lt`**: for a frozen coupling, every stopping time `τ'` of the restarted filtration
  `𝓖'_s = 𝓓_{T+s}` and every test function `φ`, almost surely on `{τ' < ζ − T} ∩ {supp φ ∩ K'_{τ'} = ∅}`,
  `E[e^{i(h', φ)} | 𝓖'_{τ'}] = exp(i (𝔥'_{τ'}, φ) − ½ E'_{τ'}(φ))` (from PROVE-LOCEXT-I's `restart_condExp_of_lt`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace
open QuantumZipper (H zeroGFFTestCov fwdHull chiC)
open LQGMetric (TestOn DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Restart

namespace DomainMarkov

open Coupling Coupling.MartMeans2 Ito

variable {nL nR : ℕ}

/-! ### The chart transport at one stopping time, on `{τ < ζ}` -/

section Transport

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓖 : Filtration ℝ≥0 mΩ} {κ : ℝ}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {c : Ω → Chart} {a k : ℝ}
  {h h' : Ω → DistOn upperHalfPlaneOpens}

/-- **The chart transport at one stopping time, localized on `{τ < ζ}`.** Same data as
`MartMeans2.isCouplingCharFun_of_isChartTransport`, but the path conditions and the original-domain clause are only
assumed almost surely on `{τ < ζ}`, for the single stopping time `τ`; the half-plane clause follows almost surely on
`{τ < ζ}`. -/
theorem condExp_cexp_of_isChartTransport_of_lt [IsProbabilityMeasure P] (hc : ∀ ω, (c ω).IsConformal)
    (hdom : ∀ z, MeasurableSet[𝓖 0] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable[𝓖 0] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hliftc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom) (hh : Measurable h)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓖 τ)
    (hpath : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω → W 0 ω = 0 ∧ ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω})
    (u : Ω → ℂ → ℝ)
    (hu : ∀ ω, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
        (fun i => VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω))
      (forceJumpSet (fun i => VL i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)
        (fun i => VR i ((τ ω).untopD 0) ω - W ((τ ω).untopD 0) ω)) (u ω))
    (hcf : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω →
      tsupport φ ⊆ (c ω).2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) →
        condExp hτ.measurableSpace P (fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ))) ω =
          Complex.exp (Complex.I * ((∫ z, (couplingMean κ (fun s : ℝ => W s.toNNReal ω)
              ((τ ω).untopD 0 : ℝ≥0) (u ω) ((c ω).1 z) - a - k * (c ω).2.2 z) * φ z : ℝ) : ℂ) -
            (((1 / 2 : ℝ) * zeroGFFTestCov ((c ω).2.1 '' (H \ fwdHull (fun s : ℝ => W s.toNNReal ω)
              ((τ ω).untopD 0 : ℝ≥0))) φ φ : ℝ) : ℂ)))
    (ht : ∀ ω, IsChartTransport (c ω) 1 a k (h ω) (h' ω)) (φ' : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω →
      Disjoint (tsupport φ') (fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) →
        condExp hτ.measurableSpace P (fun ω' => Complex.exp (Complex.I * (h' ω' φ' : ℂ))) ω =
          Complex.exp (Complex.I * ((∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω)
              ((τ ω).untopD 0 : ℝ≥0) (u ω) z * φ' z : ℝ) : ℂ) -
            (((1 / 2 : ℝ) * loewnerGreenEnergy (fun s : ℝ => W s.toNNReal ω)
              ((τ ω).untopD 0 : ℝ≥0) φ' : ℝ) : ℂ)) := by
  classical
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
  -- the good event and the random remaining domains (empty off the good event)
  set good : Ω → Prop := fun ω => W 0 ω = 0 ∧ ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧
    (((τ ω).untopD 0 : ℝ≥0) : ℝ≥0∞) < ζ ω ∧ (τ ω : ℝ≥0∞) < ζ ω with hgooddef
  have hgood : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω → good ω := by
    filter_upwards [hpath] with ω h1 h2
    refine ⟨(h1 h2).1, (h1 h2).2, ?_, h2⟩
    obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt h2)
    rw [← hs] at h2 ⊢
    rw [WithTop.untopD_coe]
    exact h2
  set O : Ω → Opens ℂ := fun ω => if good ω then ⟨interior (H \ fwdHull (fun s : ℝ => W s.toNNReal ω)
    ((τ ω).untopD 0 : ℝ≥0)), isOpen_interior⟩ else ⊥ with hOdef
  have hOH : ∀ ω, (O ω : Set ℂ) ⊆ H := fun ω => by
    by_cases hg : good ω
    · simp only [hOdef, hg, ↓reduceIte]
      exact interior_subset.trans sdiff_subset
    · simp only [hOdef, hg, ↓reduceIte, Opens.coe_bot, empty_subset]
  have hUo : ∀ ω, IsOpen ((c ω).2.1 '' (O ω : Set ℂ)) := fun ω =>
    (hc ω).isOpen_image_of_subset (O ω).isOpen (hOH ω)
  have hUH : ∀ ω, (c ω).2.1 '' (O ω : Set ℂ) ⊆ (upperHalfPlaneOpens : Set ℂ) := fun ω =>
    (image_mono (hOH ω)).trans (hc ω).2.1.image_subset
  have hUdom : ∀ ω, (c ω).2.1 '' (O ω : Set ℂ) ⊆ (c ω).dom := fun ω => by
    rw [(hc ω).coe_dom]; exact image_mono (hOH ω)
  have hOeq : ∀ ω, good ω →
      (O ω : Set ℂ) = H \ fwdHull (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) := fun ω hω => by
    simp only [hOdef, hω, ↓reduceIte, Opens.coe_mk]
    exact (isOpen_H_diff_fwdHull_rpath (w := fun t => W t ω) hω.2.1 hω.2.2.1).interior_eq
  set m : Ω → ℂ → ℝ := fun ω z => couplingMean κ (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) (u ω)
    ((c ω).1 z) - a - k * (c ω).2.2 z with hmdef
  have hmc : ∀ ω, ContinuousOn (m ω) ((c ω).2.1 '' (O ω : Set ℂ)) := fun ω => by
    by_cases hω : good ω
    · have hr := continuousOn_rpath (u := fun t => W t ω) hω.2.1 hω.2.2.1
      have hcm := continuousOn_couplingMean κ hr (hu ω).1
      have hmaps : MapsTo (c ω).1 ((c ω).2.1 '' (O ω : Set ℂ))
          (hullDom (fun t => W t ω) ((τ ω).untopD 0)) := by
        rintro _ ⟨w, hw, rfl⟩
        rw [(hc ω).2.2 w (hOH ω hw)]
        rw [hOeq ω hω] at hw
        exact mem_hullDom hr hw.1 hw.2
      exact ((hcm.comp ((hc ω).differentiableOn_fwd.continuousOn.mono (hUdom ω)) hmaps).sub
        continuousOn_const).sub (continuousOn_const.mul ((hliftc ω).mono (hUdom ω)))
    · have hO : (O ω : Set ℂ) = ∅ := by simp only [hOdef, hω, ↓reduceIte, Opens.coe_bot]
      rw [hO, image_empty]
      exact continuousOn_empty _
  -- the conditional characteristic functional at the random test function
  have hRT := condExp_cexp_apply_ae_eq_of_local (P := P) h𝒢 hh hUo hUH
    (Ψ := fun ω φ => Complex.exp (Complex.I * ((∫ z, m ω z * φ z : ℝ) : ℂ) -
        (((1 / 2 : ℝ) * zeroGFFTestCov ((c ω).2.1 '' (O ω : Set ℂ)) φ φ : ℝ) : ℂ)))
    (Eventually.of_forall fun ω R hR => by
      have hRH : R ≤ upperHalfPlaneOpens := fun x hx => hUH ω (hR hx)
      obtain ⟨μ, hμP, hμ⟩ := exists_gaussLocalLaw (U := (c ω).imageOpens (O ω))
        ((hc ω).imageOpens_subset_H (hOH ω)) (R := R) (by rw [(hc ω).coe_imageOpens (hOH ω)]; exact hR)
        (((hmc ω).mono hR).locallyIntegrableOn R.isOpen.measurableSet)
      refine ⟨μ, hμP, fun ψ => ?_⟩
      rw [hμ ψ, (hc ω).coe_imageOpens (hOH ω), GFF.coe_testIncl hRH ψ])
    (fun φ => by
      by_cases hφ0 : φ = 0
      · subst hφ0
        have h1 : P[fun ω' => Complex.exp (Complex.I * (h ω' 0 : ℂ)) | hτ.measurableSpace] =ᵐ[P] fun _ => 1 := by
          have e : (fun ω' => Complex.exp (Complex.I * (h ω' 0 : ℂ))) = fun _ => (1 : ℂ) := by
            funext ω'; simp only [map_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero]
          rw [e, condExp_const h𝒢]
        filter_upwards [h1] with ω h1ω _
        rw [h1ω]
        have e2 : (0 : TestOn upperHalfPlaneOpens) = (0 : ℂ → ℝ) := rfl
        simp only [e2, Pi.zero_apply, mul_zero, integral_zero, Complex.ofReal_zero, GFF.zeroGFFTestCov_zero_zero,
          sub_zero, Complex.exp_zero]
      · filter_upwards [hcf φ, hgood] with ω h1 hω hsupp
        have hgω : good ω := by
          by_contra hng
          have hO : (O ω : Set ℂ) = ∅ := by simp only [hOdef, hng, ↓reduceIte, Opens.coe_bot]
          rw [hO, image_empty, subset_empty_iff] at hsupp
          exact hφ0 (TestFunction.ext fun z => image_eq_zero_of_notMem_tsupport (by rw [hsupp]; exact id))
        rw [hOeq ω hgω] at hsupp ⊢
        exact h1 hgω.2.2.2 hsupp)
    hT
  -- assembly on the event `{τ < ζ} ∩ {supp φ' ∩ K_τ = ∅}`
  filter_upwards [hpull, hRT, hgood] with ω hpω hrω hgω hτζ hdisj
  have hω := hgω hτζ
  have hφO : tsupport φ' ⊆ (O ω : Set ℂ) := by
    rw [hOeq ω hω]
    exact fun z hz => ⟨φ'.tsupport_subset hz, fun hK => Set.disjoint_left.1 hdisj hz hK⟩
  have hTU := (hc ω).tsupport_pushTest_subset_image (hOH ω) φ' hφO
  rw [hpω, hrω hTU]
  have hvar : zeroGFFTestCov ((c ω).2.1 '' (O ω : Set ℂ)) (Chart.pushTest (hc ω) φ') (Chart.pushTest (hc ω) φ') =
      loewnerGreenEnergy (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) φ' := by
    rw [(hc ω).zeroGFFTestCov_pushTest_sub (hOH ω) φ' hφO, hOeq ω hω]
    exact (WholeField.loewnerGreenEnergy_rpath_eq_zeroGFFTestCov (w := fun t => W t ω) hω.2.1 hω.1 hω.2.2.1
      φ' hdisj).symm
  -- the mean
  have hr := continuousOn_rpath (u := fun t => W t ω) hω.2.1 hω.2.2.1
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
  have hmean : (∫ z, m ω z * Chart.pushTest (hc ω) φ' z) =
      (∫ w, couplingMean κ (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) (u ω) w * φ' w) -
        a * (∫ w, φ' w) - k * ∫ w, (c ω).2.2 ((c ω).2.1 w) * φ' w := by
    have hI12 : Integrable fun w => couplingMean κ (fun s : ℝ => W s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0) (u ω) w *
        φ' w - a * φ' w := hI1.sub (hI0.const_mul a)
    rw [hmdef, Chart.integral_mul_pushTest (hc ω) φ', integral_congr_ae (Eventually.of_forall hpt),
      integral_sub hI12 (hI2.const_mul k), integral_sub hI1 (hI0.const_mul a),
      integral_const_mul, integral_const_mul]
  rw [hvar, hmean, hSval ω, ← Complex.exp_add]
  congr 1
  push_cast
  ring

end Transport

/-! ### The restarted field on the live event -/

section Restarted

open Sec7 Sec5.Markov Sec2.Restart LocalExt

variable {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}

/-- **Aux. lemma 53, the Gaussian clause of the restarted field on the live event.** For a frozen optional hull
coupling, a finite stopping time `T` of its driving filtration `𝓓`, a `𝓓_T`-measurable version `K` of the recorded
history, every stopping time `τ'` of the restarted filtration `𝓖'_s = 𝓓_{T+s}`, every bounded harmonic extension `u`
of the current force data and every test function `φ`: almost surely, if `τ' < ζ − T` and `supp φ` misses the
restarted hull `K'_{τ'}`, then `E[e^{i(h', φ)} | 𝓖'_{τ'}] = exp(i (𝔥'_{τ'}, φ) − ½ E'_{τ'}(φ))`, with
`h' = restartField κ (h, K)`. -/
theorem restartField_condExp_of_lt [IsProbabilityMeasure P]
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) (hκ : 0 < κ)
    (hX : IsMeasurableKilledDriving W VL VR ζ) {T : Ω → ℝ≥0}
    (hT : IsStoppingTime (drivingFiltration P hX) fun ω => (T ω : WithTop ℝ≥0))
    {K : Ω → DrivingHist nL nR} (hKm : Measurable[hT.measurableSpace] K)
    (hK : ∀ᵐ ω ∂P, (T ω : ℝ≥0∞) < ζ ω →
      K ω = stoppedHistory (completedState W VL VR ζ) (fun ω => (T ω : WithTop ℝ≥0)) ω)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime (restartFiltration (drivingFiltration P hX) T hT) τ)
    (u : Ω → ℂ → ℝ)
    (hu : ∀ ω, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR
        (fun i => restartMark (VL i) W T ((τ ω).untopD 0) ω - restartDrv W T ((τ ω).untopD 0) ω)
        (fun i => restartMark (VR i) W T ((τ ω).untopD 0) ω - restartDrv W T ((τ ω).untopD 0) ω))
      (forceJumpSet
        (fun i => restartMark (VL i) W T ((τ ω).untopD 0) ω - restartDrv W T ((τ ω).untopD 0) ω)
        (fun i => restartMark (VR i) W T ((τ ω).untopD 0) ω - restartDrv W T ((τ ω).untopD 0) ω))
      (u ω))
    (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < restartLife ζ T ω →
      Disjoint (tsupport φ) (fwdHull (fun s : ℝ => restartDrv W T s.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) →
        condExp hτ.measurableSpace P (fun ω' => Complex.exp (Complex.I * (restartField κ (h ω', K ω') φ : ℂ))) ω =
          Complex.exp (Complex.I * ((∫ z, couplingMean κ (fun s : ℝ => restartDrv W T s.toNNReal ω)
              ((τ ω).untopD 0 : ℝ≥0) (u ω) z * φ z : ℝ) : ℂ) -
            (((1 / 2 : ℝ) * loewnerGreenEnergy (fun s : ℝ => restartDrv W T s.toNNReal ω)
              ((τ ω).untopD 0 : ℝ≥0) φ : ℝ) : ℂ)) := by
  have hpath := hC.1.2.2.2.2
  have h0 := restartFiltration_zero (𝓕 := drivingFiltration P hX) hT
  have hKm' : Measurable[restartFiltration (drivingFiltration P hX) T hT 0] K := by rw [h0]; exact hKm
  have hTζ_of : ∀ ω, (τ ω : ℝ≥0∞) < restartLife ζ T ω → (T ω : ℝ≥0∞) < ζ ω := fun ω h4 => by
    have h5 : 0 < restartLife ζ T ω := lt_of_le_of_lt zero_le h4
    exact tsub_pos_iff_lt.1 h5
  refine condExp_cexp_of_isChartTransport_of_lt (c := fun ω => histChart (K ω)) (a := 0) (k := chiC κ)
    (fun ω => isConformal_histChart (K ω)) (fun z => hKm' (measurableSet_mem_dom_histChart z))
    (fun z => ?_) (fun z => ?_) (fun ω => continuousOn_lift_histChart (K ω)) hC.2.1 hτ ?_ u hu ?_
    (fun ω => isChartTransport_restartField κ (h ω, K ω)) φ
  · have h := (measurable_indicator_fwd_histChart (nL := nL) (nR := nR) z).comp hKm'
    have e : ({ω | z ∈ (histChart (K ω)).dom}.indicator fun ω => (histChart (K ω)).1 z) =
        ({y | z ∈ (histChart y).dom}.indicator fun y => (histChart y).1 z) ∘ K := by
      funext ω
      by_cases hz : z ∈ (histChart (K ω)).dom
      · simp only [Function.comp_apply, indicator_of_mem (show K ω ∈ {y | z ∈ (histChart y).dom} from hz),
          indicator_of_mem (show ω ∈ {ω | z ∈ (histChart (K ω)).dom} from hz)]
      · simp only [Function.comp_apply, indicator_of_notMem (show K ω ∉ {y | z ∈ (histChart y).dom} from hz),
          indicator_of_notMem (show ω ∉ {ω | z ∈ (histChart (K ω)).dom} from hz)]
    rw [e]
    exact h
  · have h := (measurable_indicator_lift_histChart (nL := nL) (nR := nR) z).comp hKm'
    have e : ({ω | z ∈ (histChart (K ω)).dom}.indicator fun ω => (histChart (K ω)).2.2 z) =
        ({y | z ∈ (histChart y).dom}.indicator fun y => (histChart y).2.2 z) ∘ K := by
      funext ω
      by_cases hz : z ∈ (histChart (K ω)).dom
      · simp only [Function.comp_apply, indicator_of_mem (show K ω ∈ {y | z ∈ (histChart y).dom} from hz),
          indicator_of_mem (show ω ∈ {ω | z ∈ (histChart (K ω)).dom} from hz)]
      · simp only [Function.comp_apply, indicator_of_notMem (show K ω ∉ {y | z ∈ (histChart y).dom} from hz),
          indicator_of_notMem (show ω ∉ {ω | z ∈ (histChart (K ω)).dom} from hz)]
    rw [e]
    exact h
  · filter_upwards [hpath] with ω hp h4
    exact ⟨by simp [restartDrv], (hp.restart (hTζ_of ω h4)).2.2.2.1⟩
  · intro φ'
    filter_upwards [restart_condExp_of_lt hC hκ hX hT τ hτ u hu φ', hK, hpath] with ω h1 h2 hp h4 hsupp
    have hTζ := hTζ_of ω h4
    have hc : histChart (K ω) = restartChart W T ω := by
      rw [h2 hTζ]
      exact (restartChart_eq_histChart hp.2.2.2.1 hp.1 hTζ).symm
    simp only [hc] at hsupp ⊢
    exact h1 h4 hsupp

end Restarted

end DomainMarkov

end Restart

end InteractingSLE
