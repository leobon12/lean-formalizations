import SupercriticalConformalCovariance.TV.CutoffAgreement
import SupercriticalConformalCovariance.TV.Carrier
import SupercriticalConformalCovariance.TV.LocalTV
import LQGMetric.Field.ZeroBoundaryLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Metric Set LQGMetric LQGMetric.Blueprint
  SmallGammaGeodesics SmallGammaGeodesics.CC QuantumZipper

namespace SupercriticalConformalCovariance.TV

/-- Independent Markov zero-boundary pairings and the measurable harmonic version. -/
theorem indep_restrict_markov_zb_harmonic_version
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hH hZ G : Ω → DistC} {D : TopologicalSpace.Opens ℂ}
    (hind : IndepFun hH hZ P) (hGeq : hH =ᵐ[P] G) :
    IndepFun (fun ω (ψ : TestOn D) => restrictTo D (hZ ω) ψ) G P := by
  have hp : Measurable (fun T : DistC => fun ψ : TestOn D => restrictTo D T ψ) := by
    apply measurable_pi_iff.mpr
    intro ψ
    change Measurable (fun T : DistC =>
      T (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := D) (Ω₂ := ⊤) ψ))
    exact measurable_distOn_apply _
  have hi := hind.symm.comp hp measurable_id
  exact hi.congr (Filter.EventuallyEq.rfl) hGeq

/-- The fixed mean-zero ball tests, regarded as local tests of the containing domain. -/
def carrierLocalTests (O D : TopologicalSpace.Opens ℂ)
    (hOD : (O : Set ℂ) ⊆ D) (ρ : TestC)
    (hρO : tsupport (ρ : ℂ → ℝ) ⊆ O) (hρ1 : ∫ x, ρ x = 1)
    (n : ℕ) : ZBLocalTest D O := by
  refine ⟨localMeanZeroGenOn O D hOD ρ hρO hρ1 n, ?_, ?_⟩
  · change tsupport ((localMeanZeroGen O ρ hρO hρ1 n).1.1 : ℂ → ℝ) ⊆ O
    exact (localMeanZeroGen O ρ hρO hρ1 n).2
  · change ∫ x, (localMeanZeroGen O ρ hρO hρ1 n).1.1 x = 0
    exact (localMeanZeroGen O ρ hρO hρ1 n).1.2

theorem carrierLocalTests_coe (O D : TopologicalSpace.Opens ℂ)
    (hOD : (O : Set ℂ) ⊆ D) (ρ : TestC)
    (hρO : tsupport (ρ : ℂ → ℝ) ⊆ O) (hρ1 : ∫ x, ρ x = 1)
    (n : ℕ) :
    (carrierLocalTests O D hOD ρ hρO hρ1 n).1 =
      localMeanZeroGenOn O D hOD ρ hρO hρ1 n := rfl

/-- On the local carrier, the independent Markov shift is exactly the whole-plane field. -/
theorem markov_shifted_path_eq_ae
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {h hH hZ G : Ω → DistC}
    (s : ℝ) (z : ℂ) (D : TopologicalSpace.Opens ℂ)
    (hsum : ∀ ω, addConst (h ω) (-circleAvg (h ω) s z) = hH ω + hZ ω)
    (hharm : ∀ᵐ ω ∂P, ∃ g : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd g (D : Set ℂ) ∧
      ∀ φ : TestOn D, restrictTo D (hH ω) φ = ∫ x, g x * φ x)
    (hGeq : hH =ᵐ[P] G)
    (R L : ℝ) (hR : 0 < R) (hL : 2 * R + 4 < L)
    (hBD : ball (0 : ℂ) L ⊆ D)
    (O : TopologicalSpace.Opens ℂ) (hO : (O : Set ℂ) = ball (0 : ℂ) R)
    (hOD : (O : Set ℂ) ⊆ D)
    (ρ : TestC) (hρO : tsupport (ρ : ℂ → ℝ) ⊆ O)
    (hρ1 : ∫ x, ρ x = 1) :
    (fun ω n =>
      restrictTo D (hZ ω) (carrierLocalTests O D hOD ρ hρO hρ1 n).1 +
      ∫ x, smoothCutoffShift R hR (1 / 4) (1 / 4) (by norm_num) (G ω) x *
        (carrierLocalTests O D hOD ρ hρO hρ1 n).1 x) =ᵐ[P]
      fun ω => localCountablePath O ρ hρO hρ1 (h ω) := by
  filter_upwards [hharm, hGeq] with ω ⟨g, hg, hpair⟩ heq
  funext n
  let ψ : TestOn D := (carrierLocalTests O D hOD ρ hρO hρ1 n).1
  have hψR : tsupport (ψ : ℂ → ℝ) ⊆ ball (0 : ℂ) R := by
    rw [← hO]
    exact (carrierLocalTests O D hOD ρ hρO hρ1 n).2.1
  have hψ0 : ∫ x, ψ x = 0 :=
    (carrierLocalTests O D hOD ρ hρO hρ1 n).2.2
  have hshift := smoothCutoffShift_pair_eq_harmonic_pair hR hL hBD hg hpair ψ hψR hψ0
  rw [heq] at hshift
  have hsumψ := congrArg (fun T : DistC => T (localMeanZeroGen O ρ hρO hρ1 n).1.1)
    (hsum ω)
  rw [pair_recenter, add_apply] at hsumψ
  rw [heq] at hsumψ
  change h ω (localMeanZeroGen O ρ hρO hρ1 n).1.1 =
    G ω (localMeanZeroGen O ρ hρO hρ1 n).1.1 +
    hZ ω (localMeanZeroGen O ρ hρO hρ1 n).1.1 at hsumψ
  have hco (T : DistC) : restrictTo D T ψ =
      T (localMeanZeroGen O ρ hρO hρ1 n).1.1 := by
    change T (inclTest D ψ) = _
    congr 1
    ext x
    rw [coe_inclTest]
    change (localMeanZeroGenOn O D hOD ρ hρO hρ1 n : ℂ → ℝ) x = _
    rw [coe_localMeanZeroGenOn]
  change restrictTo D (hZ ω) ψ +
    ∫ x, smoothCutoffShift R hR (1 / 4) (1 / 4) (by norm_num) (G ω) x * ψ x = _
  rw [hshift, hco, hco]
  exact (add_comm _ _).trans hsumψ.symm

/-- The local whole-plane/zero-boundary comparison on the fixed countable carrier. -/
theorem tvDist_wp_markov_zb_le_shift_energy
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    {h hH hZ G : Ω → DistC}
    (s : ℝ) (z : ℂ) (D : TopologicalSpace.Opens ℂ)
    (hsum : ∀ ω, addConst (h ω) (-circleAvg (h ω) s z) = hH ω + hZ ω)
    (hharm : ∀ᵐ ω ∂P, ∃ g : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd g (D : Set ℂ) ∧
      ∀ φ : TestOn D, restrictTo D (hH ω) φ = ∫ x, g x * φ x)
    (hGm : Measurable G) (hGeq : hH =ᵐ[P] G) (hind : IndepFun hH hZ P)
    (hzb : IsZeroBoundaryGFF D (fun ω => restrictTo D (hZ ω)) P)
    (hadm : ZBAdmissible D)
    (R L : ℝ) (hR : 0 < R) (hL : 2 * R + 4 < L)
    (hBD : ball (0 : ℂ) L ⊆ D)
    (O : TopologicalSpace.Opens ℂ) (hO : (O : Set ℂ) = ball (0 : ℂ) R)
    (hOD : (O : Set ℂ) ⊆ D)
    (ρ : TestC) (hρO : tsupport (ρ : ℂ → ℝ) ⊆ O)
    (hρ1 : ∫ x, ρ x = 1) :
    QuantumZipper.TV.tvDist
      (wpLocalCountableLaw O ρ hρO hρ1 h P)
      (zbLocalCountableLaw O D hOD ρ hρO hρ1
        (fun ω => restrictTo D (hZ ω)) P) ≤
      ∫⁻ T, min 1 (ENNReal.ofReal (Real.sqrt
        (Real.exp (dirichletEnergyOn D
          (canonicalShift R hR (1 / 4) (1 / 4) (by norm_num) (by norm_num)
            D ((closedBall_subset_ball_zero_of_norm_add_lt (y := (0 : ℂ)) (by
              simp only [norm_zero, zero_add]; linarith)).trans hBD) T).1) - 1)))
        ∂(P.map G) := by
  let hball : closedBall (0 : ℂ) (2 * R + 2) ⊆ D :=
    (closedBall_subset_ball_zero_of_norm_add_lt (y := (0 : ℂ)) (by
      simp only [norm_zero, zero_add]; linarith)).trans hBD
  let f := canonicalShift R hR (1 / 4) (1 / 4) (by norm_num) (by norm_num) D hball
  let e := carrierLocalTests O D hOD ρ hρO hρ1
  have hne : (D : Set ℂ).Nonempty := by
    refine ⟨0, hBD ?_⟩
    rw [mem_ball, dist_self]
    linarith
  have hi := indep_restrict_markov_zb_harmonic_version hind hGeq (D := D)
  have hbound := tvDist_zb_indep_shift_le hadm hne hzb.process O e G
    hGm hi f
    (measurable_canonicalShift_pair R hR (1 / 4) (1 / 4) (by norm_num)
      (by norm_num) D hball)
    (measurable_canonicalShift_energy R hR (1 / 4) (1 / 4) (by norm_num)
      (by norm_num) D hball)
  have hpath := markov_shifted_path_eq_ae s z D hsum hharm hGeq R L hR hL
    hBD O hO hOD ρ hρO hρ1
  have hmap : P.map (fun ω n =>
      restrictTo D (hZ ω) (e n).1 + ∫ x, (f (G ω)).1 x * (e n).1 x) =
      wpLocalCountableLaw O ρ hρO hρ1 h P := by
    exact Measure.map_congr hpath
  rw [← hmap]
  exact hbound

/-- All zero-boundary GFF realizations induce the same law on the fixed carrier. -/
theorem zbLocalCountableLaw_eq
    {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'}
    (O D : TopologicalSpace.Opens ℂ) (hOD : (O : Set ℂ) ⊆ D)
    (ρ : TestC) (hρO : tsupport (ρ : ℂ → ℝ) ⊆ O)
    (hρ1 : ∫ x, ρ x = 1)
    {X : Ω → DistOn D} {Y : Ω' → DistOn D}
    (hX : IsZeroBoundaryGFF D X P) (hY : IsZeroBoundaryGFF D Y P') :
    zbLocalCountableLaw O D hOD ρ hρO hρ1 X P =
      zbLocalCountableLaw O D hOD ρ hρO hρ1 Y P' := by
  have he := IsZeroBoundaryGFF.map_eq hX hY
  unfold zbLocalCountableLaw
  rw [← Measure.map_map (measurable_localCountablePathOn O D hOD ρ hρO hρ1)
      hX.measurable,
    ← Measure.map_map (measurable_localCountablePathOn O D hOD ρ hρO hρ1)
      hY.measurable,
    he]

end SupercriticalConformalCovariance.TV
