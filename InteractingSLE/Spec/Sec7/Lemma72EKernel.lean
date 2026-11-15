/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma72CChart
import InteractingSLE.Spec.Sec7.Lemma72DStop
import InteractingSLE.Spec.Sec7.Lemma72EHit

/-!
# Lemma 7.1's joint law, last steps, II: the Gaussian kernel of the pocket field given germs and marks

Packet PROVE-LEMMA72E. Specification §7.1, proof of Lemma 7.1 (`source/spec/p193-240.md` L598–L606, pp. 224–225) and
of Lemma 7.2 (L622–L640, "The identical argument … conditionally on `A`").

`exists_condExp_cexp_chartTransport_cond`: let `B = ℍ ∖ ψ⁻¹(O)` (`O ⊆ ℍ` open and random, `ψ⁻¹ = (c ω).2.1`) be a
history-marked local set of the centred field `h − u₀` for marks `ℋ` that make the chart measurable. Then there is a
random distribution `M`, almost surely harmonic on `O`, such that for every event `D` of the germs of `B` and the
marks of positive probability, under `P[· | D]` the conditional characteristic function of the transported field
`h_ψ − T = chartTransport c 1 a k h − T` (any `T` harmonic on `ℍ`) given germs ∨ marks is the Gaussian kernel
`exp(i M(χ) − ½ G_O(χ, χ))` (`WholeField.rangeKerCF`).

This is the kernel step of `Lemma72C.isLocalSet_cond_chart_of_isHistoryAvoidanceLocal`, kept as a kernel (and for a
general random open `O`, which may be empty), as `Lemma72D.isLocalSet_hull_of_kernels` needs it at every rational time.
Proof: Lemma 3.6 (iii) with the history retained (`Lemma72C.exists_germLaw_of_isHistoryAvoidanceLocal`:
`h − u₀ = h₁ + Z`,
`Z` a zero-boundary GFF on `ψ⁻¹(O)` given germs ∨ marks); the same law under `P[· | D]`; the pull-back of `Z` is a
zero-boundary GFF on `O` (`Lemma72C.isCondZeroBoundaryGFF_pullField_sub`); `M = chartTransport (h₁ + u₀) − T` is
measurable for germs ∨ marks and harmonic on `O` (`Lemma72C.isHarmonicDistOn_chartTransport`), so its phase factors out.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

open QuantumZipper (H fwdHull zeroGFFTestCov)
open SupercriticalConformalCovariance.GM24 (smoothDist)

universe u

namespace InteractingSLE.Sec7.Lemma72E

open LQGMetric LocalSets WholeField

section Kernel

variable {Ω : Type u} {ℋ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **The Gaussian kernel of the transported field given germs ∨ marks, under every conditioning on them** (see the
module docstring). -/
theorem exists_condExp_cexp_chartTransport_cond {h : Ω → DistOn upperHalfPlaneOpens} (hhm : Measurable h)
    {u₀ : ℂ → ℝ} (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh0 : IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u₀) P)
    {c : Ω → Chart} (hc : ∀ ω, (c ω).IsConformal)
    (hdom : ∀ z, MeasurableSet[ℋ] {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable[ℋ] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable[ℋ] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hliftc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom)
    (hlift : ∀ ω, InnerProductSpace.HarmonicOnNhd (c ω).2.2 (c ω).dom)
    {O : Ω → Set ℂ} (hOo : ∀ ω, IsOpen (O ω)) (hOH : ∀ ω, O ω ⊆ H)
    (hℋ : ℋ ≤ mΩ) (hBm : Measurable[mΩ, hittingSigma] fun ω => H \ (c ω).2.1 '' O ω)
    (hloc : IsHistoryAvoidanceLocal ℋ (fun ω => H \ (c ω).2.1 '' O ω) (centredField h u₀) P)
    (a k : ℝ) {T : DistOn upperHalfPlaneOpens} (hT : IsHarmonicDistOn T H) :
    ∃ M : Ω → DistOn upperHalfPlaneOpens, (∀ᵐ ω ∂P, IsHarmonicDistOn (M ω) (O ω)) ∧
      ∀ D : Set Ω, MeasurableSet[germSigma (fun ω => H \ (c ω).2.1 '' O ω) (centredField h u₀) ⊔ ℋ] D →
        P D ≠ 0 → ∀ χ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂(P[|D]),
          (P[|D])[fun ω' => Complex.exp (Complex.I * ((Chart.chartTransport (hc ω') 1 a k (h ω') - T) χ : ℂ)) |
            germSigma (fun ω => H \ (c ω).2.1 '' O ω) (centredField h u₀) ⊔ ℋ] ω = rangeKerCF (M ω) (O ω) χ := by
  set B : Ω → Set ℂ := fun ω => H \ (c ω).2.1 '' O ω with hBdef
  set h0 := centredField h u₀ with hh0def
  have himH : ∀ ω, (c ω).2.1 '' O ω ⊆ H := fun ω => (image_mono (hOH ω)).trans (hc ω).2.1.image_subset
  have hHB : ∀ ω, H \ B ω = (c ω).2.1 '' O ω := fun ω => by
    simp only [hBdef, sdiff_sdiff_right_self, inter_eq_right.2 (himH ω)]
  have hBc : ∀ ω, B ω ⊆ H ∧ IsOpen (H \ B ω) := fun ω =>
    ⟨sdiff_subset, by rw [hHB]; exact (hc ω).isOpen_image_of_subset (hOo ω) (hOH ω)⟩
  have hh0m : Measurable h0 := measurable_centredField hhm u₀
  obtain ⟨h₁, hh₁, hharm, hcond⟩ :=
    Lemma72C.exists_germLaw_of_isHistoryAvoidanceLocal hh0 hBm hℋ hloc (ae_of_all _ hBc)
  have h𝒢 : germSigma B h0 ⊔ ℋ ≤ mΩ := sup_le (germSigma_le hBm hh0m) hℋ
  have hℋ𝒢 : ℋ ≤ germSigma B h0 ⊔ ℋ := le_sup_right
  have hh₁m : Measurable h₁ := hh₁.mono (germSigma_le hBm hh0m) le_rfl
  have hXm : Measurable fun ω => h0 ω - h₁ ω :=
    measurable_distOn_iff.2 fun φ => ((measurable_distOn_apply φ).comp hh0m).sub
      ((measurable_distOn_apply φ).comp hh₁m)
  set M : Ω → DistOn upperHalfPlaneOpens := fun ω =>
    Chart.chartTransport (hc ω) 1 a k (h₁ ω + smoothDist upperHalfPlaneOpens u₀) - T with hMdef
  refine ⟨M, ?_, ?_⟩
  · -- `M` is harmonic on `O`
    filter_upwards [hharm] with ω hω
    have hsm := isHarmonicDistOn_smoothDist hu₀
    have hMh : IsHarmonicDistOn (h₁ ω + smoothDist upperHalfPlaneOpens u₀) ((c ω).2.1 '' O ω) := by
      rw [← hHB]
      exact Coupling.IsHarmonicDistOn.add' (hBc ω).2 hω (IsHarmonicDistOn.mono hsm sdiff_subset)
    exact IsHarmonicDistOn.sub' (hOo ω)
      (Lemma72C.isHarmonicDistOn_chartTransport (hc ω) (hliftc ω) (hlift ω) (hOo ω) (hOH ω) hMh a k)
      (IsHarmonicDistOn.mono hT (hOH ω))
  intro D hD hPD χ
  have : IsProbabilityMeasure (P[|D]) := cond_isProbabilityMeasure hPD
  have hac : P[|D] ≪ P := cond_absolutelyContinuous
  -- the conditional law under `P[· | D]`
  have hcondD : IsCondZeroBoundaryGFF (P[|D]) (germSigma B h0 ⊔ ℋ) (fun ω => (c ω).2.1 '' O ω)
      fun ω => h0 ω - h₁ ω := by
    intro φ
    have hcov : Measurable[germSigma B h0 ⊔ ℋ] fun ω => zeroGFFTestCov (H \ relClosureH (B ω)) φ φ :=
      (measurable_comap_zeroGFFTestCov_compl B φ φ).mono ((comap_le_germSigma B h0).trans le_sup_left) le_rfl
    set c' : Ω → ℂ := fun ω => ((Real.exp (-(1 / 2) * zeroGFFTestCov (H \ relClosureH (B ω)) φ φ) : ℝ) : ℂ)
      with hc'def
    have hc'm : StronglyMeasurable[germSigma B h0 ⊔ ℋ] c' :=
      (Complex.measurable_ofReal.comp (Real.measurable_exp.comp (hcov.const_mul _))).stronglyMeasurable
    have hcB : ∀ ω, c' ω = ((Real.exp (-(1 / 2) * zeroGFFTestCov ((c ω).2.1 '' O ω) φ φ) : ℝ) : ℂ) :=
      fun ω => by simp only [c', relClosureH_eq (hBc ω).1 (hBc ω).2, hHB]
    have hcc' : (fun ω => ((Real.exp (-(1 / 2) * zeroGFFTestCov (H \ B ω) φ φ) : ℝ) : ℂ)) =ᵐ[P] c' :=
      Eventually.of_forall fun ω => by simp only [hcB, hHB]
    have hc'i : Integrable c' P := (integrable_condExp.congr (hcond φ)).congr hcc'
    have hX : Integrable (fun ω => Complex.exp (Complex.I * (((h0 ω - h₁ ω) φ : ℝ) : ℂ))) P :=
      GFF.integrable_exp_I_mul ((measurable_distOn_apply φ).comp hXm)
    have key := LocalExt.condExp_cond_ae_eq le_rfl h𝒢 hD hPD hX hc'm hc'i ((hcond φ).trans hcc')
    exact key.trans (Eventually.of_forall fun ω => hcB ω)
  -- pull back through the chart
  have hpull := Lemma72C.isCondZeroBoundaryGFF_pullField_sub h𝒢 hc (fun z => hℋ𝒢 _ (hdom z))
    (fun z => (hfwd z).mono hℋ𝒢 le_rfl) hOo hOH hXm hcondD
  -- `M` is measurable for germs ∨ marks
  have hMm : Measurable[germSigma B h0 ⊔ ℋ] M := by
    have h1 : Measurable[germSigma B h0 ⊔ ℋ] fun ω => h₁ ω + smoothDist upperHalfPlaneOpens u₀ :=
      (Coupling.measurable_add_distOnConst _).comp (hh₁.mono le_sup_left le_rfl)
    have h2 := @Chart.measurable_chartTransport_random' Ω (germSigma B h0 ⊔ ℋ) c hc (fun z => hℋ𝒢 _ (hdom z))
      (fun z => (hfwd z).mono hℋ𝒢 le_rfl) (fun z => (hliftm z).mono hℋ𝒢 le_rfl) hliftc _ h1 1 a k
    exact (Coupling.measurable_sub_distOnConst T).comp h2
  have hdiff : ∀ ω, (Chart.chartTransport (hc ω) 1 a k (h ω) - T) χ =
      M ω χ + Chart.pullField (hc ω) (h0 ω - h₁ ω) χ := fun ω => by
    have e : Chart.chartTransport (hc ω) 1 a k (h ω) - T - M ω = Chart.pullField (hc ω) (h0 ω - h₁ ω) := by
      simp only [hMdef, sub_sub_sub_cancel_right]
      rw [Chart.chartTransport_sub, one_smul]
      congr 1
      simp only [hh0def, centredField]
      abel
    have key : ∀ A m p : DistOn upperHalfPlaneOpens, A - m = p → A χ = m χ + p χ := fun A m p hp => by
      rw [← hp, sub_apply]; ring
    exact key _ _ _ e
  -- factor the phase out
  set Wp : Ω → ℂ := fun ω => Complex.exp (Complex.I * (M ω χ : ℂ)) with hWpdef
  set F : Ω → ℂ := fun ω => Complex.exp (Complex.I * (Chart.pullField (hc ω) (h0 ω - h₁ ω) χ : ℂ)) with hFdef
  have hWpm : StronglyMeasurable[germSigma B h0 ⊔ ℋ] Wp :=
    (Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp
      ((measurable_distOn_apply χ).comp hMm)))).stronglyMeasurable
  have hWpb : ∀ ω, ‖Wp ω‖ ≤ 1 := fun ω => by
    simp only [Wp, Complex.norm_exp_I_mul_ofReal, le_refl]
  have hψm : Measurable fun ω => Chart.chartTransport (hc ω) 1 a k (h ω) :=
    Chart.measurable_chartTransport_random' hc (fun z => hℋ _ (hdom z)) (fun z => (hfwd z).mono hℋ le_rfl)
      (fun z => (hliftm z).mono hℋ le_rfl) hliftc hhm 1 a k
  have hpm : Measurable fun ω => Chart.pullField (hc ω) (h0 ω - h₁ ω) χ := by
    have e : (fun ω => Chart.pullField (hc ω) (h0 ω - h₁ ω) χ) =
        fun ω => (Chart.chartTransport (hc ω) 1 a k (h ω) - T) χ - M ω χ := funext fun ω => by
      rw [hdiff ω]; ring
    rw [e]
    exact ((measurable_distOn_apply χ).comp ((Coupling.measurable_sub_distOnConst T).comp hψm)).sub
      ((measurable_distOn_apply χ).comp (hMm.mono h𝒢 le_rfl))
  have hF : Integrable F (P[|D]) := GFF.integrable_exp_I_mul hpm
  have hWF : Integrable (fun ω => Wp ω * F ω) (P[|D]) :=
    hF.bdd_mul (hWpm.mono h𝒢).aestronglyMeasurable (Eventually.of_forall hWpb)
  have hfac := condExp_bilin_of_stronglyMeasurable_left (ContinuousLinearMap.mul ℝ ℂ) hWpm
    (by simpa [ContinuousLinearMap.mul_apply'] using hWF) hF
  have e : (fun ω' => Complex.exp (Complex.I * ((Chart.chartTransport (hc ω') 1 a k (h ω') - T) χ : ℂ))) =
      fun ω => (ContinuousLinearMap.mul ℝ ℂ) (Wp ω) (F ω) := by
    funext ω
    simp only [Wp, F, ContinuousLinearMap.mul_apply', hdiff ω, Complex.ofReal_add, ← Complex.exp_add]
    congr 1
    ring
  rw [e]
  filter_upwards [hfac, hpull χ] with ω h1 h2
  rw [h1, ContinuousLinearMap.mul_apply', h2]
  simp only [Wp, rangeKerCF, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

end Kernel

end InteractingSLE.Sec7.Lemma72E
