import SupercriticalConformalCovariance.TV.RadialKernel

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory LQGMetric QuantumZipper

namespace SupercriticalConformalCovariance.TV

/-- Exact harmonic variance in an independent recentered Markov decomposition,
on a mean-zero test. -/
theorem harmonic_variance_eq_logCov_sub_zeroGFFTestCov
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {U : TopologicalSpace.Opens ℂ}
    {h hH hZ : Ω → DistC} (hh : IsWholePlaneGFF h P)
    (X : BddOn (U : Set ℂ) → Ω → ℝ)
    (hX : IsZBGFFProcessExt U X P)
    (hEq : ∀ φ : TestOn U, X φ.toBddOn =ᵐ[P]
      fun ω => restrictTo U (hZ ω) φ)
    (hind : IndepFun hH hZ P)
    {r : ℝ} (z : ℂ)
    (hsum : ∀ ω, addConst (h ω) (-circleAvg (h ω) r z) =
      hH ω + hZ ω)
    (ψ : TestC0) (hψ : tsupport (ψ.1 : ℂ → ℝ) ⊆ U) :
    Var[fun ω => hH ω ψ.1; P] =
      logCov ψ.1 ψ.1 -
        zeroGFFTestCov U (localTestOn U ψ hψ) (localTestOn U ψ hψ) := by
  let φ : TestOn U := localTestOn U ψ hψ
  have hZL2 : MemLp (fun ω => hZ ω ψ.1) 2 P := by
    simpa only [φ, pair_restrict_localTestOn] using
      memLp_markov_zb_pair hX hEq φ
  have hZvar : Var[fun ω => hZ ω ψ.1; P] = zeroGFFTestCov U φ φ := by
    simpa only [φ, pair_restrict_localTestOn] using
      variance_markov_zb_pair hX hEq φ
  have hWL2 : MemLp (fun ω => h ω ψ.1) 2 P :=
    MarkovZB.memLp_pair hh ψ
  have hsumψ (ω : Ω) : h ω ψ.1 = hH ω ψ.1 + hZ ω ψ.1 := by
    have he := congrArg (fun T : DistC => T ψ.1) (hsum ω)
    rw [pair_recenter, add_apply] at he
    exact he
  have hHL2 : MemLp (fun ω => hH ω ψ.1) 2 P := by
    have he : (fun ω => hH ω ψ.1) =
        (fun ω => h ω ψ.1 - hZ ω ψ.1) := by
      funext ω
      linarith [hsumψ ω]
    rw [he]
    exact hWL2.sub hZL2
  have hindψ : IndepFun (fun ω => hZ ω ψ.1) (fun ω => hH ω ψ.1) P :=
    hind.symm.comp (GFFInv.measurable_pair ψ.1) (GFFInv.measurable_pair ψ.1)
  have hWvar : Var[fun ω => h ω ψ.1; P] = logCov ψ.1 ψ.1 := by
    have hm : Measurable (fun ω => h ω ψ.1) :=
      (GFFInv.measurable_pair ψ.1).comp hh.measurable
    exact (covariance_self hm.aemeasurable).symm.trans (hh.covariance_eq ψ ψ)
  have hsumvar : Var[fun ω => h ω ψ.1; P] =
      Var[fun ω => hZ ω ψ.1 + hH ω ψ.1; P] := by
    congr 1
    funext ω
    linarith [hsumψ ω]
  rw [hWvar, hindψ.variance_fun_add hZL2 hHL2, hZvar] at hsumvar
  dsimp [φ] at hsumvar
  linarith

/-- Mean-zero test pairings of the complementary harmonic field remain centered. -/
theorem harmonic_pair_centered
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {U : TopologicalSpace.Opens ℂ}
    {h hH hZ : Ω → DistC} (hh : IsWholePlaneGFF h P)
    (X : BddOn (U : Set ℂ) → Ω → ℝ)
    (hX : IsZBGFFProcessExt U X P)
    (hEq : ∀ φ : TestOn U, X φ.toBddOn =ᵐ[P]
      fun ω => restrictTo U (hZ ω) φ)
    {r : ℝ} (z : ℂ)
    (hsum : ∀ ω, addConst (h ω) (-circleAvg (h ω) r z) =
      hH ω + hZ ω)
    (ψ : TestC0) (hψ : tsupport (ψ.1 : ℂ → ℝ) ⊆ U) :
    ∫ ω, hH ω ψ.1 ∂P = 0 := by
  let φ : TestOn U := localTestOn U ψ hψ
  have hZL2 : MemLp (fun ω => hZ ω ψ.1) 2 P := by
    simpa only [φ, pair_restrict_localTestOn] using
      memLp_markov_zb_pair hX hEq φ
  have hZmean : ∫ ω, hZ ω ψ.1 ∂P = 0 := by
    have he : (fun ω => hZ ω ψ.1) =ᵐ[P] X φ.toBddOn := by
      simpa only [φ, pair_restrict_localTestOn] using (hEq φ).symm
    rw [integral_congr_ae he]
    exact hX.centered φ.toBddOn
  have hWint : Integrable (fun ω => h ω ψ.1) P :=
    (MarkovZB.memLp_pair hh ψ).integrable (by norm_num)
  have hZint : Integrable (fun ω => hZ ω ψ.1) P := hZL2.integrable (by norm_num)
  have he : (fun ω => hH ω ψ.1) = fun ω => h ω ψ.1 - hZ ω ψ.1 := by
    funext ω
    have hsumψ := congrArg (fun T : DistC => T ψ.1) (hsum ω)
    rw [pair_recenter, add_apply] at hsumψ
    exact eq_sub_iff_add_eq.mpr hsumψ.symm
  rw [he, integral_sub hWint hZint, hh.centered ψ, hZmean, sub_self]

end SupercriticalConformalCovariance.TV
