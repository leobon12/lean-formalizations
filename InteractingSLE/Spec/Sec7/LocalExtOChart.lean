/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtOGlue
import InteractingSLE.Spec.Sec7.Lemma72CChart
import InteractingSLE.Spec.Sec7.LocalExtGKernel
import InteractingSLE.Foundations.Complex.DerivLog

/-!
# Locality transported by the restart chart, with the conditional structure kept

Packet PROVE-LOCEXT-O, steps (1)–(2). PROVE-LEMMA72C's `isLocalSet_cond_chart_of_isHistoryAvoidanceLocal` transports a
history-marked local set `B` of the centred field through a random chart `c` to the mapped set `K` with
`ℍ ∖ B = c.inv(ℍ ∖ K)`, concluding `IsLocalSet` under `P[· | E]`. The tilt at a restart (`LocalExtOTilt`) needs the
**conditional decomposition** behind that conclusion, with the marks (the recorded history, hence the restart word) in
the conditioning σ-algebra. This file states it:

* `harmonicOnNhd_lift_histChart`: the lift `Im log f′` of the Loewner chart read from a history is harmonic on the chart
  domain (`isDerivLog_fwdMap`);
* **`exists_condDecomp_chart`**: under `P[· | E]` (`E` a mark of positive probability), the chart transport of `h`
  is `M + Y`, `M` measurable for `𝒢 = 𝒜_B ∨ ℋ` and harmonic off `K`, `Y` conditionally a zero-boundary GFF on `ℍ ∖ K`
  given `𝒢`; the identity `ℍ ∖ B = c.inv(ℍ ∖ K)` is only needed `P[· | E]`-almost surely.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open QuantumZipper (H zeroGFFTestCov fwdHull)
open scoped ENNReal NNReal

universe u

namespace InteractingSLE

namespace LocalExt

open LQGMetric LocalSets WholeField

/-! ### The lift of the chart read from a history is harmonic -/

theorem harmonicOnNhd_lift_histChart {nL nR : ℕ} (y : DrivingHist nL nR) :
    InnerProductSpace.HarmonicOnNhd (histChart y).2.2 (histChart y).dom := by
  have hw : Continuous (Ito.rpath (histDrv y)) := (continuous_histDrv y).comp continuous_real_toNNReal
  have hw0 : Ito.rpath (histDrv y) 0 = 0 := by simp [Ito.rpath, histDrv_zero]
  have ht : (0 : ℝ) ≤ (histTime y : ℝ) := (histTime y).coe_nonneg
  intro z hz
  have hz2 : z ∈ (Chart.id.loewner (Ito.rpath (histDrv y)) (histTime y)).dom := hz
  rw [Chart.mem_dom_loewner_iff hw hw0 ht] at hz2
  obtain ⟨hzH, u, hu⟩ := hz2
  have hzD : z ∈ H \ fwdHull (Ito.rpath (histDrv y)) (histTime y) :=
    ⟨hzH, Ito.notMem_fwdHull_of_isForwardSol hw hzH ht hu⟩
  have hD : IsOpen (H \ fwdHull (Ito.rpath (histDrv y)) (histTime y)) :=
    QuantumZipper.FwdHolo.isOpen_compl_fwdHull hw ht
  have hL := (isDerivLog_fwdMap hw ht).1
  have han : AnalyticAt ℂ (QuantumZipper.logDerivFwd (Ito.rpath (histDrv y)) (histTime y)) z :=
    hL.analyticAt (hD.mem_nhds hzD)
  have e : (histChart y).2.2 = fun z => (QuantumZipper.logDerivFwd (Ito.rpath (histDrv y)) (histTime y) z).im := by
    funext z
    change (QuantumZipper.logDerivFwd (Ito.rpath (histDrv y)) (histTime y) z).im + 0 = _
    rw [add_zero]
  rw [e]
  exact han.harmonicAt_im

/-! ### The conditional decomposition through a random chart -/

section Decomp

variable {Ω : Type u} {ℋ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **The conditional decomposition of the transported field.** Let `h` be a measurable field whose centring
`h⁰ = h − u₀` is a zero-boundary GFF, `c` an `ℋ`-measurable random conformal chart with continuous harmonic lifts, `B` a
hitting-measurable relatively closed random set which is a history-marked local set of `h⁰` for the marks `ℋ`, and `K` a
random relatively closed set with `ℍ ∖ B = c.inv(ℍ ∖ K)` almost surely under `P[· | E]`, `E ∈ ℋ` of positive probability.
Then under `P[· | E]`, with `𝒢 = 𝒜_B ∨ ℋ`, the chart transport `h_c = chartTransport c 1 a k h` is `M + Y` with `M`
`𝒢`-measurable and harmonic off `K`, and `Y` conditionally a zero-boundary GFF on `ℍ ∖ K` given `𝒢`. -/
theorem exists_condDecomp_chart {h : Ω → DistOn upperHalfPlaneOpens} (hhm : Measurable h)
    {u₀ : ℂ → ℝ} (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh0 : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    {c : Ω → Chart} (hc : ∀ ω, (c ω).IsConformal)
    (hdom : ∀ z, MeasurableSet[ℋ] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[ℋ] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable[ℋ] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hliftc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom)
    (hlift : ∀ ω, InnerProductSpace.HarmonicOnNhd (c ω).2.2 (c ω).dom)
    (hℋ : ℋ ≤ mΩ) {B : Ω → Set ℂ} (hBm : Measurable[mΩ, hittingSigma] B)
    (hBc : ∀ ω, B ω ⊆ H ∧ IsOpen (H \ B ω)) (hloc : IsHistoryAvoidanceLocal ℋ B (centredField h u₀) P)
    {K : Ω → Set ℂ} (hK : ∀ ω, K ω ⊆ H ∧ IsOpen (H \ K ω)) {E : Set Ω} (hE : MeasurableSet[ℋ] E) (hPE : P E ≠ 0)
    (hBK : ∀ᵐ ω ∂(P[|E]), H \ B ω = (c ω).2.1 '' (H \ K ω)) (a k : ℝ) :
    ∃ M : Ω → DistOn upperHalfPlaneOpens, Measurable[germSigma B (centredField h u₀) ⊔ ℋ] M ∧
      (∀ᵐ ω ∂(P[|E]), IsHarmonicDistOn (M ω) (H \ K ω)) ∧
      IsCondZeroBoundaryGFF (P[|E]) (germSigma B (centredField h u₀) ⊔ ℋ) (fun ω => H \ K ω)
        (fun ω => Chart.chartTransport (hc ω) 1 a k (h ω) - M ω) := by
  set h0 := centredField h u₀ with hh0def
  have hh0m : Measurable h0 := measurable_centredField hhm u₀
  obtain ⟨h₁, hh₁, hharm, hcond⟩ :=
    Sec7.Lemma72C.exists_germLaw_of_isHistoryAvoidanceLocal hh0 hBm hℋ hloc (ae_of_all _ hBc)
  have h𝒢 : germSigma B h0 ⊔ ℋ ≤ mΩ := sup_le (germSigma_le hBm hh0m) hℋ
  have hℋ𝒢 : ℋ ≤ germSigma B h0 ⊔ ℋ := le_sup_right
  have : IsProbabilityMeasure (P[|E]) := cond_isProbabilityMeasure hPE
  have hac : P[|E] ≪ P := cond_absolutelyContinuous
  have hh₁m : Measurable h₁ := hh₁.mono (germSigma_le hBm hh0m) le_rfl
  have hXm : Measurable fun ω => h0 ω - h₁ ω :=
    measurable_distOn_iff.2 fun φ => ((measurable_distOn_apply φ).comp hh0m).sub ((measurable_distOn_apply φ).comp hh₁m)
  -- the conditional law under `P[· | E]`, on the image domain
  have hcondE : IsCondZeroBoundaryGFF (P[|E]) (germSigma B h0 ⊔ ℋ) (fun ω => (c ω).2.1 '' (H \ K ω)) fun ω => h0 ω - h₁ ω := by
    intro φ
    have hcov : Measurable[germSigma B h0 ⊔ ℋ] fun ω => zeroGFFTestCov (H \ relClosureH (B ω)) φ φ :=
      (measurable_comap_zeroGFFTestCov_compl B φ φ).mono ((comap_le_germSigma B h0).trans le_sup_left) le_rfl
    set c' : Ω → ℂ := fun ω => ((Real.exp (-(1 / 2) * zeroGFFTestCov (H \ relClosureH (B ω)) φ φ) : ℝ) : ℂ)
      with hc'def
    have hc'm : StronglyMeasurable[germSigma B h0 ⊔ ℋ] c' :=
      (Complex.measurable_ofReal.comp (Real.measurable_exp.comp (hcov.const_mul _))).stronglyMeasurable
    have hcB : ∀ ω, c' ω = ((Real.exp (-(1 / 2) * zeroGFFTestCov (H \ B ω) φ φ) : ℝ) : ℂ) := fun ω => by
      simp only [c', relClosureH_eq (hBc ω).1 (hBc ω).2]
    have hcc' : (fun ω => ((Real.exp (-(1 / 2) * zeroGFFTestCov (H \ B ω) φ φ) : ℝ) : ℂ)) =ᵐ[P] c' :=
      Eventually.of_forall fun ω => (hcB ω).symm
    have hc'i : Integrable c' P := (integrable_condExp.congr (hcond φ)).congr hcc'
    have hX : Integrable (fun ω => Complex.exp (Complex.I * (((h0 ω - h₁ ω) φ : ℝ) : ℂ))) P :=
      GFF.integrable_exp_I_mul ((measurable_distOn_apply φ).comp hXm)
    have key := condExp_cond_ae_eq le_rfl h𝒢 (hℋ𝒢 _ hE) hPE hX hc'm hc'i ((hcond φ).trans hcc')
    filter_upwards [key, hBK] with ω h1 h2
    rw [h1, hcB, h2]
  -- pull back through the chart
  have hpull := Sec7.Lemma72C.isCondZeroBoundaryGFF_pullField_sub h𝒢 hc (fun z => hℋ𝒢 _ (hdom z))
    (fun z => (hfwd z).mono hℋ𝒢 le_rfl) (O := fun ω => H \ K ω) (fun ω => (hK ω).2) (fun _ => sdiff_subset) hXm
    hcondE
  -- the harmonic part
  set M₀ : Ω → DistOn upperHalfPlaneOpens := fun ω => h₁ ω + SupercriticalConformalCovariance.GM24.smoothDist
    upperHalfPlaneOpens u₀ with hM₀def
  have hM₀m : Measurable[germSigma B h0 ⊔ ℋ] M₀ :=
    (Coupling.measurable_add_distOnConst _).comp (hh₁.mono le_sup_left le_rfl)
  refine ⟨fun ω => Chart.chartTransport (hc ω) 1 a k (M₀ ω), ?_, ?_, ?_⟩
  · exact @Chart.measurable_chartTransport_random' Ω (germSigma B h0 ⊔ ℋ) c hc (fun z => hℋ𝒢 _ (hdom z))
      (fun z => (hfwd z).mono hℋ𝒢 le_rfl) (fun z => (hliftm z).mono hℋ𝒢 le_rfl) hliftc M₀ hM₀m 1 a k
  · filter_upwards [hac.ae_le hharm, hBK] with ω hω hBKω
    have hsm := isHarmonicDistOn_smoothDist hu₀
    have hMh : IsHarmonicDistOn (M₀ ω) ((c ω).2.1 '' (H \ K ω)) := by
      rw [← hBKω]
      exact Coupling.IsHarmonicDistOn.add' (hBc ω).2 hω (LocalSets.IsHarmonicDistOn.mono hsm sdiff_subset)
    exact Sec7.Lemma72C.isHarmonicDistOn_chartTransport (hc ω) (hliftc ω) (hlift ω) (hK ω).2 sdiff_subset hMh a k
  · have hdiff : ∀ ω, Chart.chartTransport (hc ω) 1 a k (h ω) - Chart.chartTransport (hc ω) 1 a k (M₀ ω) =
        Chart.pullField (hc ω) (h0 ω - h₁ ω) := fun ω => by
      rw [Chart.chartTransport_sub, one_smul]
      congr 1
      simp only [hM₀def, hh0def, centredField]
      abel
    intro φ
    simp only [hdiff]
    exact hpull φ

end Decomp

end LocalExt

end InteractingSLE
