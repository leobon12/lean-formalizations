import SupercriticalConformalCovariance.TV.Proposition210

/-!
# The source-side Cameron–Martin envelope for an arbitrary family of local tests

`exists_ig4_tv_envelope` compares the whole-plane
GFF with a zero-boundary GFF on a bounded `D ⊇ B(0,L)` on the total-variation module's fixed carrier. Its proof uses only that
the carrier tests are mean-zero and supported in `B(0,R)`. Here the same argument is run for an
**arbitrary** family `e : ℕ → ZBLocalTest D (B(0,R))`. GM (2.6) uses it with the conformally transported
tests `confPushTest φ_n⁻¹ (·)`, so the Cameron–Martin cutoff and its energy estimate stay in the source
disk (GM l. 555–562, repaired).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Metric Set LQGMetric QuantumZipper Filter Topology
  SmallGammaGeodesics SmallGammaGeodesics.CC
open scoped ENNReal

namespace SupercriticalConformalCovariance.GM24

open SupercriticalConformalCovariance.TV

/-- On mean-zero tests supported in `B(0,R)`, the Markov zero-boundary part plus the canonical cutoff
shift of the harmonic part is the whole-plane field. -/
theorem markov_shifted_general_eq_ae
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {h hH hZ G : Ω → DistC}
    (s : ℝ) (z : ℂ) (D : TopologicalSpace.Opens ℂ)
    (hsum : ∀ ω, addConst (h ω) (-circleAvg (h ω) s z) = hH ω + hZ ω)
    (hharm : ∀ᵐ ω ∂P, ∃ g : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd g (D : Set ℂ) ∧
      ∀ φ : TestOn D, restrictTo D (hH ω) φ = ∫ x, g x * φ x)
    (hGeq : hH =ᵐ[P] G)
    (R L : ℝ) (hR : 0 < R) (hL : 2 * R + 4 < L)
    (hBD : ball (0 : ℂ) L ⊆ D) (e : ℕ → ZBLocalTest D (ball (0 : ℂ) R)) :
    (fun ω n =>
      restrictTo D (hZ ω) (e n).1 +
      ∫ x, smoothCutoffShift R hR (1 / 4) (1 / 4) (by norm_num) (G ω) x * (e n).1 x) =ᵐ[P]
      fun ω n => h ω (inclTest D (e n).1) := by
  filter_upwards [hharm, hGeq] with ω ⟨g, hg, hpair⟩ heq
  funext n
  let ψ : TestOn D := (e n).1
  have hψR : tsupport (ψ : ℂ → ℝ) ⊆ ball (0 : ℂ) R := (e n).2.1
  have hψ0 : ∫ x, ψ x = 0 := (e n).2.2
  have hshift := smoothCutoffShift_pair_eq_harmonic_pair hR hL hBD hg hpair ψ hψR hψ0
  rw [heq] at hshift
  have hsumψ := congrArg (fun T : DistC => T (inclTest D ψ)) (hsum ω)
  simp only [add_apply] at hsumψ
  rw [GFFInv.addConst_apply, coe_inclTest, hψ0, zero_mul, add_zero, heq] at hsumψ
  change restrictTo D (hZ ω) ψ +
    ∫ x, smoothCutoffShift R hR (1 / 4) (1 / 4) (by norm_num) (G ω) x * ψ x = _
  rw [hshift]
  change hZ ω (inclTest D ψ) + G ω (inclTest D ψ) = _
  rw [hsumψ]
  ring

/-- **Source-side envelope for arbitrary local tests.** -/
theorem exists_tv_envelope_general (R : ℝ) (hR : 0 < R) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
        (h : Ω → DistC) (P : Measure Ω) (hh : IsWholePlaneGFF h P)
        (D : TopologicalSpace.Opens ℂ) (hDb : Bornology.IsBounded (D : Set ℂ))
        (L : ℝ) (hL : 2 * R + 6 < L) (hBD : ball (0 : ℂ) L ⊆ D)
        (e : ℕ → ZBLocalTest D (ball (0 : ℂ) R))
        (g : Ω' → DistOn D) (Q : Measure Ω') (hg : IsZeroBoundaryGFF D g Q)
        (δ : ℝ) (hδ : 0 < δ),
        QuantumZipper.TV.tvDist
          (P.map fun ω k => h ω (inclTest D (e k).1))
          (Q.map fun ω k => g ω (e k).1) ≤
          cmMixIntegrand δ + ENNReal.ofReal δ⁻¹ *
            (C * ENNReal.ofReal (diskVarianceEnvelope L (2 * R + 4))) := by
  obtain ⟨C, hCfinite, hC⟩ := exists_lintegral_cutoff_energy_le R hR
  refine ⟨C, hCfinite, ?_⟩
  intro Ω Ω' _ _ h P hh D hDb L hL hBD e g Q hg δ hδ
  letI : IsProbabilityMeasure P := hh.gaussian.isProbabilityMeasure
  obtain ⟨s, hs, hDs⟩ := exists_outside_circle_of_bounded D hDb
  obtain ⟨hH, hZ, G, X, hsum, hharm, hGm, hGeq, hind, hzb, hX, hEq⟩ :=
    exists_markov_zb_measurable_version h hh D hDb hs 0 hDs
  let hball : closedBall (0 : ℂ) (2 * R + 2) ⊆ D :=
    (closedBall_subset_ball_zero_of_norm_add_lt (y := (0 : ℂ)) (by
      simp only [norm_zero, zero_add]; linarith)).trans hBD
  let f := canonicalShift R hR (1 / 4) (1 / 4) (by norm_num) (by norm_num) D hball
  have hne : (D : Set ℂ).Nonempty := by
    refine ⟨0, hBD ?_⟩
    rw [mem_ball, dist_self]
    linarith
  have hi := indep_restrict_markov_zb_harmonic_version hind hGeq (D := D)
  have hbound := tvDist_zb_indep_shift_le (zbAdmissible_of_isBounded hDb) hne hzb.process
    (ball (0 : ℂ) R) e G hGm hi f
    (measurable_canonicalShift_pair R hR (1 / 4) (1 / 4) (by norm_num) (by norm_num) D hball)
    (measurable_canonicalShift_energy R hR (1 / 4) (1 / 4) (by norm_num) (by norm_num) D hball)
  have hpath := markov_shifted_general_eq_ae s 0 D hsum hharm hGeq R L hR (by linarith) hBD e
  have hmap : P.map (fun ω n =>
      restrictTo D (hZ ω) (e n).1 + ∫ x, (f (G ω)).1 x * (e n).1 x) =
      P.map (fun ω k => h ω (inclTest D (e k).1)) :=
    Measure.map_congr hpath
  have hπ : Measurable fun (u : DistOn D) (k : ℕ) => u (e k).1 :=
    measurable_pi_iff.2 fun k => measurable_distOn_apply _
  have hzlaw : P.map (fun ω n => restrictTo D (hZ ω) (e n).1) =
      Q.map (fun ω k => g ω (e k).1) := by
    have he := IsZeroBoundaryGFF.map_eq hzb hg
    have e1 : (fun ω n => restrictTo D (hZ ω) (e n).1) =
        (fun (u : DistOn D) (k : ℕ) => u (e k).1) ∘ fun ω => restrictTo D (hZ ω) := rfl
    have e2 : (fun ω k => g ω (e k).1) = (fun (u : DistOn D) (k : ℕ) => u (e k).1) ∘ g := rfl
    rw [e1, e2, ← Measure.map_map hπ hzb.measurable, ← Measure.map_map hπ hg.measurable, he]
  rw [← hmap, ← hzlaw]
  let E : DistC → ℝ := cutoffEnergyAt R hR L hL D hBD
  have hEm : Measurable E := measurable_cutoffEnergyAt R hR L hL D hBD
  have hEn : ∀ᵐ ω ∂P, 0 ≤ E (G ω) :=
    Filter.Eventually.of_forall (fun ω => cutoffEnergyAt_nonneg R hR L hL D hBD (G ω))
  have hmapG : (∫⁻ T, cmMixIntegrand (E T) ∂(P.map G)) =
      ∫⁻ ω, cmMixIntegrand (E (G ω)) ∂P := by
    change (∫⁻ T, (cmMixIntegrand ∘ E) T ∂(P.map G)) =
      ∫⁻ ω, (cmMixIntegrand ∘ E) (G ω) ∂P
    rw [lintegral_map (measurable_cmMixIntegrand.comp hEm) hGm]
  have hmean : (∫⁻ ω, ENNReal.ofReal (E (G ω)) ∂P) ≤
      C * ENNReal.ofReal (diskVarianceEnvelope L (2 * R + 4)) := by
    simpa only [E, cutoffEnergyAt] using
      (hC hh hGm hGeq D hDb hL hBD X hX hEq hind s 0 hsum hharm)
  have hCM := lintegral_cmMixIntegrand_le P (E ∘ G) (hEm.comp hGm) hEn hδ
  have hb2 : QuantumZipper.TV.tvDist
      (P.map (fun ω n => restrictTo D (hZ ω) (e n).1 + ∫ x, (f (G ω)).1 x * (e n).1 x))
      (P.map (fun ω n => restrictTo D (hZ ω) (e n).1)) ≤
      ∫⁻ ω, cmMixIntegrand (E (G ω)) ∂P := by
    change _ ≤ ∫⁻ T, cmMixIntegrand (E T) ∂(P.map G) at hbound
    exact hbound.trans_eq hmapG
  exact hb2.trans (hCM.trans (by
    simpa only [Function.comp_apply] using
      (add_le_add_right (mul_le_mul_of_nonneg_left hmean bot_le) (cmMixIntegrand δ))))

end SupercriticalConformalCovariance.GM24
