/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondGenFinalGeometry
import InteractingSLE.Spec.Sec5.CrossCondGenFinalCollar
import InteractingSLE.Spec.Sec5.CrossCondGenFinalMarks
import InteractingSLE.Spec.Sec5.CrossCondGenFinalChart

/-!
# General image martingales from deterministic marked kernels

PROVE-CROSSCOND-GEN. The final analytic assembly below discharges the optional
kernel passage, the Gaussian bounds, and the protected right limits. It does not
assert the still missing boundary classification and stochastic image construction.
Their exact remaining requirements are `ImageWordFiltrationHypothesis`,
`ForwardImageKernelHypothesis`, `ForwardImageMarksHypothesis`, and the explicit
clock conditions. The pathwise construction is `exists_relativeImage_of_traces`;
the junction gaps and initial data are proved in `CrossCondGenFinalMarks`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Complex
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec5.CrossCond.Gen

open Ito Sec7.Lemma71D WangWu.ChartConst Word49 Theta

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {nL nR : ℕ}

/-- Forward times in the retained source interval at which a protected test avoids
the image hull. The clock `a` maps original times to relative capacities. -/
def forwardAvoid (W : ℝ≥0 → Ω → ℝ) (T : Ω → WithTop ℝ≥0) (c : Ω → Chart)
    (J : Ω → Set ℝ≥0) (a : ℝ≥0 → Ω → ℝ≥0) (φ : TestOn upperHalfPlaneOpens)
    (q : ℝ≥0) : Set Ω :=
  {ω | q ∈ J ω ∧ IsChartAvoid (W · ω) (T ω : ℝ≥0∞) (c ω) φ (a q ω)}

/-- Exact remaining deterministic-forward-time field input. In the application
`ℋ q` is the union germ joined with both stopped driving histories. Proving this
requires the surviving-side boundary identification; it assumes no random-time law. -/
def ForwardImageKernelHypothesis (P : Measure Ω) (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (T : Ω → WithTop ℝ≥0) (c : Ω → Chart) (offset coeff : ℝ)
    (h : Ω → DistOn upperHalfPlaneOpens) (ℋ : ℝ≥0 → MeasurableSpace Ω)
    (J : Ω → Set ℝ≥0) (a : ℝ≥0 → Ω → ℝ≥0) : Prop :=
  ∀ (q : ℝ≥0) (φ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P,
    ω ∈ forwardAvoid W T c J a φ q →
      P[fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) | ℋ q] ω =
        imageChar κ ρL ρR W VL VR c offset coeff (a q ω) φ ω

/-- Exact remaining marked-history reading requirement. A censored image event on
each inverse-clock dyadic cell must be readable from the forward marked union. -/
def ForwardImageMarksHypothesis (P : Measure Ω) (𝓐 : Filtration ℝ≥0 mΩ)
    (W : ℝ≥0 → Ω → ℝ) (T : Ω → WithTop ℝ≥0) (c : Ω → Chart)
    (ℋ : ℝ≥0 → MeasurableSpace Ω) (J : Ω → Set ℝ≥0)
    (a τ : ℝ≥0 → Ω → ℝ≥0) : Prop :=
  ∀ (r : ℝ≥0) (φ : TestOn upperHalfPlaneOpens) B, MeasurableSet[𝓐 r] B →
    ∀ n k, ∃ C, MeasurableSet[ℋ (dyq n k)] C ∧
      C =ᵐ[P] (B ∩ {ω | IsChartAvoid (W · ω) (T ω : ℝ≥0∞) (c ω) φ r} ∩
        {ω | dyIdx n (τ r ω) = k} ∩ forwardAvoid W T c J a φ (dyq n k))

/-- Clock facts sufficient for the upper-dyadic argument. The tail formulation
permits early dyadic ceilings to lie beyond the original available lifetime. -/
def ForwardImageClockHypothesis (T : Ω → WithTop ℝ≥0) (J : Ω → Set ℝ≥0)
    (a τ : ℝ≥0 → Ω → ℝ≥0) : Prop :=
  ∀ (r : ℝ≥0) ω, (r : ℝ≥0∞) < (T ω : ℝ≥0∞) →
    (∀ᶠ n in atTop, dyF n (τ r ω) ∈ J ω) ∧
    ∃ N : ℕ, Antitone (fun n => a (dyF (n + N) (τ r ω)) ω) ∧
      (∀ n, r < a (dyF (n + N) (τ r ω)) ω) ∧
      Tendsto (fun n => a (dyF (n + N) (τ r ω)) ω) atTop (𝓝 r)

/-- The clock requirements are deterministic consequences of a continuous strictly
increasing relative clock and an inverse taking live capacities into its open
source interval. This is valid for finite source intervals as well. -/
theorem forwardImageClockHypothesis_of_local_inverse
    {T : Ω → WithTop ℝ≥0} {J : Ω → Set ℝ≥0} {a τ : ℝ≥0 → Ω → ℝ≥0}
    (hJ : ∀ ω, IsOpen (J ω))
    (hac : ∀ ω, ContinuousOn (fun q => a q ω) (J ω))
    (ham : ∀ ω, StrictMonoOn (fun q => a q ω) (J ω))
    (hinv : ∀ (r : ℝ≥0) ω, (r : ℝ≥0∞) < (T ω : ℝ≥0∞) →
      τ r ω ∈ J ω ∧ a (τ r ω) ω = r) :
    ForwardImageClockHypothesis T J a τ := by
  intro r ω hr
  obtain ⟨hτJ, hτa⟩ := hinv r ω hr
  have hdy := tendsto_dyF (τ r ω)
  have hev : ∀ᶠ n in atTop, dyF n (τ r ω) ∈ J ω := hdy.eventually ((hJ ω).mem_nhds hτJ)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  have htail : ∀ n, dyF (n + N) (τ r ω) ∈ J ω := fun n => hN _ (Nat.le_add_left N n)
  refine ⟨hev, N, ?_, ?_, ?_⟩
  · intro n m hnm
    exact (ham ω).monotoneOn (htail m) (htail n)
      (antitone_dyF (τ r ω) (Nat.add_le_add_right hnm N))
  · intro n
    calc r = a (τ r ω) ω := hτa.symm
      _ < a (dyF (n + N) (τ r ω)) ω := ham ω hτJ (htail n) (lt_dyF _ _)
  · have ht := ((hac ω _ hτJ).tendsto).comp (tendsto_nhdsWithin_iff.2
      ⟨hdy.comp (tendsto_add_atTop_nat N), Eventually.of_forall htail⟩)
    rwa [hτa] at ht

/-- General-angle image martingales from deterministic forward marked kernels.
This eliminates `ImageTimeUnionHypothesis` as a random-inverse-time input, but
retains the explicitly named boundary/marked-construction obligations above. -/
theorem imageWordFiltGenStatement_of_forward_kernels
    {P : Measure Ω} [IsProbabilityMeasure P] {κ θ : ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {𝓐 : Filtration ℝ≥0 mΩ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ}
    {VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ} {T : Ω → WithTop ℝ≥0}
    {σ : ℕ → Ω → ℝ≥0} {c : Ω → Chart} {h : Ω → DistOn upperHalfPlaneOpens}
    (hImage : ImageWordFiltrationHypothesis P 𝓐 W VL VR T σ c) (hh : Measurable h)
    {ℋ : ℝ≥0 → MeasurableSpace Ω} (hH : ∀ q, ℋ q ≤ mΩ)
    {J : Ω → Set ℝ≥0} {a τ : ℝ≥0 → Ω → ℝ≥0}
    (hτ : ∀ r, Measurable (τ r)) (hclock : ForwardImageClockHypothesis T J a τ)
    (hkernel : ForwardImageKernelHypothesis P κ (jwL (cLT θ) κ ρL) (jwR (cRT θ) κ ρR)
      W VL VR T c (2 * π * chiC κ) (chiC κ) h ℋ J a)
    (hread : ForwardImageMarksHypothesis P 𝓐 W T c ℋ J a τ)
    (hAvoid : ∀ r (φ : TestOn upperHalfPlaneOpens),
      MeasurableSet[𝓐 r] {ω | IsChartAvoid (W · ω) (T ω : ℝ≥0∞) (c ω) φ r})
    (hChar : ∀ r (φ : TestOn upperHalfPlaneOpens), Measurable[𝓐 r]
      ({ω | IsChartAvoid (W · ω) (T ω : ℝ≥0∞) (c ω) φ r}.indicator
        (imageChar κ (jwL (cLT θ) κ ρL) (jwR (cRT θ) κ ρR) W VL VR c
          (2 * π * chiC κ) (chiC κ) r φ))) :
    ImageWordFiltGenStatement κ θ ρL ρR P 𝓐 W VL VR T := by
  apply imageWordFiltGenStatement hImage hh
  apply chartConst_of_rawChar hImage.contact hImage.conformal
  intro r φ
  have hX : Integrable (fun ω => Complex.exp (Complex.I * (h ω φ : ℂ))) P := by
    refine Integrable.of_bound (Complex.measurable_exp.comp
      (measurable_const.mul (Complex.measurable_ofReal.comp
        ((LQGMetric.measurable_distOn_apply φ).comp hh)))).aestronglyMeasurable 1 ?_
    exact Eventually.of_forall fun ω => by rw [mul_comm, Complex.norm_exp_ofReal_mul_I]
  refine ae_condExp_eq_on_of_forward_kernels (mΩ := mΩ) (P := P) (𝓐.le r)
    (hAvoid r φ) hX (Eventually.of_forall fun ω => ?_) (hChar r φ)
    (fun n k => ℋ (dyq n k)) (fun n k => hH _) (Av := forwardAvoid W T c J a φ)
    (F := fun q ω => imageChar κ (jwL (cLT θ) κ ρL) (jwR (cRT θ) κ ρR)
      W VL VR c (2 * π * chiC κ) (chiC κ) (a q ω) φ ω)
    (fun q ω hq => norm_imageChar_le_one hImage.contact (hImage.conformal ω) hq.2.1 φ)
    (fun n k => hkernel (dyq n k) φ) (hτ r) (hread r φ) ?_
  · rw [mul_comm, Complex.norm_exp_ofReal_mul_I]
  · refine Eventually.of_forall fun ω hav => ?_
    obtain ⟨hJ, N, hanti, hgt, hlim⟩ := hclock r ω hav.1
    obtain ⟨hev, hF⟩ := tendsto_imageChar_of_isChartAvoid
      (κ := κ) (ρL := jwL (cLT θ) κ ρL) (ρR := jwR (cRT θ) κ ρR)
      (a := 2 * π * chiC κ) (k := chiC κ) hImage.contact (hImage.conformal ω)
      (hImage.continuousLift ω) hav hanti hgt hlim
    refine ⟨?_, (tendsto_add_atTop_iff_nat N).1 hF⟩
    have hev' : ∀ᶠ n in atTop,
        IsChartAvoid (W · ω) (T ω : ℝ≥0∞) (c ω) φ (a (dyF n (τ r ω)) ω) := by
      obtain ⟨M, hM⟩ := eventually_atTop.1 hev
      refine eventually_atTop.2 ⟨M + N, fun n hn => ?_⟩
      have h := hM (n - N) (by omega)
      simpa only [Nat.sub_add_cancel (show N ≤ n by omega)] using h
    filter_upwards [hJ, hev'] with n hJn hAn
    exact ⟨hJn, hAn⟩

end InteractingSLE.Sec5.CrossCond.Gen
