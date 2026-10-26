import SupercriticalConformalCovariance.TV.CMMixtureLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Metric Set LQGMetric QuantumZipper ProbabilityTheory Filter Topology
open scoped ENNReal

namespace SupercriticalConformalCovariance.TV

theorem exists_outside_circle_of_bounded
    (D : TopologicalSpace.Opens ℂ) (hDb : Bornology.IsBounded (D : Set ℂ)) :
    ∃ s : ℝ, 0 < s ∧ Disjoint (D : Set ℂ) (sphere (0 : ℂ) s) := by
  obtain ⟨r, hr⟩ := hDb.subset_closedBall (0 : ℂ)
  let s := max r 0 + 1
  refine ⟨s, by dsimp [s]; linarith [le_max_right r 0], ?_⟩
  rw [Set.disjoint_left]
  intro x hxD hxS
  have hxr : dist x 0 ≤ r := by
    exact mem_closedBall.1 (hr hxD)
  have hxs : dist x 0 = s := by
    simpa [mem_sphere, dist_comm] using hxS
  have hrs : r < s := by dsimp [s]; linarith [le_max_left r 0]
  linarith

def cutoffEnergyAt (R : ℝ) (hR : 0 < R) (L : ℝ)
    (hL : 2 * R + 6 < L) (D : TopologicalSpace.Opens ℂ)
    (hBD : ball (0 : ℂ) L ⊆ D) (T : DistC) : ℝ :=
  let hball : closedBall (0 : ℂ) (2 * R + 2) ⊆ D :=
    (closedBall_subset_ball_zero_of_norm_add_lt (y := (0 : ℂ)) (by
      simp only [norm_zero, zero_add]; linarith)).trans hBD
  dirichletEnergyOn D
    (canonicalShift R hR (1 / 4) (1 / 4) (by norm_num) (by norm_num)
      D hball T).1

theorem measurable_cutoffEnergyAt (R : ℝ) (hR : 0 < R) (L : ℝ)
    (hL : 2 * R + 6 < L) (D : TopologicalSpace.Opens ℂ)
    (hBD : ball (0 : ℂ) L ⊆ D) :
    Measurable (cutoffEnergyAt R hR L hL D hBD) :=
  measurable_canonicalShift_energy R hR (1 / 4) (1 / 4) (by norm_num)
    (by norm_num) D _

theorem cutoffEnergyAt_nonneg (R : ℝ) (hR : 0 < R) (L : ℝ)
    (hL : 2 * R + 6 < L) (D : TopologicalSpace.Opens ℂ)
    (hBD : ball (0 : ℂ) L ⊆ D) (T : DistC) :
    0 ≤ cutoffEnergyAt R hR L hL D hBD T :=
  QuantumZipper.K3.dirichletEnergyOn_nonneg_K3 D _

def ig4ZBLaw {Ω : Type} [MeasurableSpace Ω]
    (Ω' : ℕ → Type) [∀ n, MeasurableSpace (Ω' n)]
    (O : TopologicalSpace.Opens ℂ) (ρ : TestC)
    (hρO : tsupport (ρ : ℂ → ℝ) ⊆ O) (hρ1 : ∫ x, ρ x = 1)
    (h : Ω → DistC) (P : Measure Ω)
    (D : ℕ → TopologicalSpace.Opens ℂ)
    (g : ∀ n, Ω' n → DistOn (D n)) (Q : ∀ n, Measure (Ω' n))
    (n : ℕ) : Measure (ℕ → ℝ) := by
  classical
  exact if hOD : (O : Set ℂ) ⊆ D n then
    zbLocalCountableLaw O (D n) hOD ρ hρO hρ1 (g n) (Q n)
  else wpLocalCountableLaw O ρ hρO hρ1 h P


/-- Uniform finite-parameter total-variation estimate for a bounded domain. -/
theorem exists_ig4_tv_envelope (R : ℝ) (hR : 0 < R) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω']
        (O : TopologicalSpace.Opens ℂ)
        (hO : (O : Set ℂ) = ball (0 : ℂ) R)
        (ρ : TestC) (hρO : tsupport (ρ : ℂ → ℝ) ⊆ O)
        (hρ1 : ∫ x, ρ x = 1)
        (h : Ω → DistC) (P : Measure Ω) (hh : IsWholePlaneGFF h P)
        (D : TopologicalSpace.Opens ℂ) (hDb : Bornology.IsBounded (D : Set ℂ))
        (L : ℝ) (hL : 2 * R + 6 < L) (hBD : ball (0 : ℂ) L ⊆ D)
        (g : Ω' → DistOn D) (Q : Measure Ω') (hg : IsZeroBoundaryGFF D g Q)
        (δ : ℝ) (hδ : 0 < δ),
        QuantumZipper.TV.tvDist
          (zbLocalCountableLaw O D
            (by rw [hO]; exact (ball_subset_ball (by linarith)).trans hBD)
            ρ hρO hρ1 g Q)
          (wpLocalCountableLaw O ρ hρO hρ1 h P) ≤
          cmMixIntegrand δ + ENNReal.ofReal δ⁻¹ *
            (C * ENNReal.ofReal (diskVarianceEnvelope L (2 * R + 4))) := by
  obtain ⟨C, hCfinite, hC⟩ := exists_lintegral_cutoff_energy_le R hR
  refine ⟨C, hCfinite, ?_⟩
  intro Ω Ω' _ _ O hO ρ hρO hρ1 h P hh D hDb L hL hBD g Q hg δ hδ
  letI : IsProbabilityMeasure P := hh.gaussian.isProbabilityMeasure
  obtain ⟨s, hs, hDs⟩ := exists_outside_circle_of_bounded D hDb
  obtain ⟨hH, hZ, G, X, hsum, hharm, hGm, hGeq, hind, hzb, hX, hEq⟩ :=
    exists_markov_zb_measurable_version h hh D hDb hs 0 hDs
  have hOD : (O : Set ℂ) ⊆ D := by
    rw [hO]
    exact (ball_subset_ball (by linarith)).trans hBD
  have htv := tvDist_wp_markov_zb_le_shift_energy s 0 D hsum hharm
    hGm hGeq hind hzb (zbAdmissible_of_isBounded hDb) R L hR
    (by linarith) hBD O hO hOD ρ hρO hρ1
  have hzlaw := zbLocalCountableLaw_eq O D hOD ρ hρO hρ1 hzb hg
  rw [hzlaw] at htv
  let E : DistC → ℝ := cutoffEnergyAt R hR L hL D hBD
  have hEm : Measurable E := measurable_cutoffEnergyAt R hR L hL D hBD
  have hEn : ∀ᵐ ω ∂P, 0 ≤ E (G ω) :=
    Filter.Eventually.of_forall
      (fun ω => cutoffEnergyAt_nonneg R hR L hL D hBD (G ω))
  have hmap : (∫⁻ T, cmMixIntegrand (E T) ∂(P.map G)) =
      ∫⁻ ω, cmMixIntegrand (E (G ω)) ∂P := by
    change (∫⁻ T, (cmMixIntegrand ∘ E) T ∂(P.map G)) =
      ∫⁻ ω, (cmMixIntegrand ∘ E) (G ω) ∂P
    rw [lintegral_map (measurable_cmMixIntegrand.comp hEm) hGm]
  have hmean : (∫⁻ ω, ENNReal.ofReal (E (G ω)) ∂P) ≤
      C * ENNReal.ofReal (diskVarianceEnvelope L (2 * R + 4)) := by
    simpa only [E, cutoffEnergyAt] using
      (hC hh hGm hGeq D hDb hL hBD X hX hEq hind s 0 hsum hharm)
  have hCM := lintegral_cmMixIntegrand_le P (E ∘ G) (hEm.comp hGm) hEn hδ
  have hbound : QuantumZipper.TV.tvDist
      (wpLocalCountableLaw O ρ hρO hρ1 h P)
      (zbLocalCountableLaw O D hOD ρ hρO hρ1 g Q) ≤
      ∫⁻ ω, cmMixIntegrand (E (G ω)) ∂P := by
    change _ ≤ ∫⁻ T, cmMixIntegrand (E T) ∂(P.map G) at htv
    exact htv.trans_eq hmap
  rw [QuantumZipper.TV.tvDist_comm]
  exact hbound.trans (hCM.trans (by
    simpa only [Function.comp_apply] using
      (add_le_add_right (mul_le_mul_of_nonneg_left hmean bot_le)
        (cmMixIntegrand δ))))


/-- IG4 Proposition 2.10(i), repaired bounded-domain zero-boundary form:
far-away boundaries give TV convergence of the laws on the fixed determining
mean-zero carrier for distributions modulo additive constants on the ball. -/
theorem ig4_prop210_zeroBoundary_bounded
    {Ω : Type} [MeasurableSpace Ω]
    (Ω' : ℕ → Type) [∀ n, MeasurableSpace (Ω' n)]
    (O : TopologicalSpace.Opens ℂ) (R : ℝ)
    (hO : (O : Set ℂ) = ball (0 : ℂ) R) (hR : 0 < R)
    (ρ : TestC) (hρO : tsupport (ρ : ℂ → ℝ) ⊆ O)
    (hρ1 : ∫ x, ρ x = 1)
    (h : Ω → DistC) (P : Measure Ω) (hh : IsWholePlaneGFF h P)
    (D : ℕ → TopologicalSpace.Opens ℂ)
    (hDb : ∀ n, Bornology.IsBounded (D n : Set ℂ))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hBD : ∀ n, ball (0 : ℂ) (L n) ⊆ D n)
    (g : ∀ n, Ω' n → DistOn (D n)) (Q : ∀ n, Measure (Ω' n))
    (hg : ∀ n, IsZeroBoundaryGFF (D n) (g n) (Q n)) :
    Tendsto (fun n => QuantumZipper.TV.tvDist
      (ig4ZBLaw Ω' O ρ hρO hρ1 h P D g Q n)
      (wpLocalCountableLaw O ρ hρO hρ1 h P)) atTop (𝓝 0) := by
  obtain ⟨C, hCfinite, hC⟩ := exists_ig4_tv_envelope R hR
  have hbig : ∀ᶠ n in atTop, 2 * R + 6 < L n := by
    filter_upwards [(tendsto_atTop.1 hL) (2 * R + 7)] with n hn
    linarith
  have henv : Tendsto
      (fun n => ENNReal.ofReal (diskVarianceEnvelope (L n) (2 * R + 4)))
      atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal
      (diskVarianceEnvelope_tendsto_zero hL (2 * R + 4))
  refine ENNReal.tendsto_nhds_zero.2 fun ε hε => ?_
  have hcont : Continuous cmMixIntegrand := by
    unfold cmMixIntegrand
    exact continuous_const.min
      (ENNReal.continuous_ofReal.comp
        (Real.continuous_sqrt.comp (Real.continuous_exp.sub continuous_const)))
  have hzero : cmMixIntegrand 0 = 0 := by simp [cmMixIntegrand]
  have hlim : Tendsto cmMixIntegrand (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
    simpa only [hzero] using (hcont.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), cmMixIntegrand δ < ε :=
    hlim.eventually (Iio_mem_nhds hε)
  have hpos : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), 0 < δ := self_mem_nhdsWithin
  obtain ⟨δ, hδ, hδsmall⟩ : ∃ δ : ℝ, 0 < δ ∧ cmMixIntegrand δ < ε := by
    exact (hpos.and hev).exists
  have hmul : Tendsto
      (fun n => ENNReal.ofReal δ⁻¹ *
        (C * ENNReal.ofReal (diskVarianceEnvelope (L n) (2 * R + 4))))
      atTop (𝓝 0) := by
    have hfirst : Tendsto
        (fun n => C * ENNReal.ofReal (diskVarianceEnvelope (L n) (2 * R + 4)))
        atTop (𝓝 0) := by
      simpa only [mul_zero] using
        (ENNReal.Tendsto.const_mul henv (Or.inr hCfinite))
    simpa only [mul_zero] using
      (ENNReal.Tendsto.const_mul hfirst (Or.inr ENNReal.ofReal_ne_top))
  have hupper : Tendsto
      (fun n => cmMixIntegrand δ + ENNReal.ofReal δ⁻¹ *
        (C * ENNReal.ofReal (diskVarianceEnvelope (L n) (2 * R + 4))))
      atTop (𝓝 (cmMixIntegrand δ)) := by
    convert tendsto_const_nhds.add hmul using 1 <;> simp
  filter_upwards [hbig, hupper.eventually (Iio_mem_nhds hδsmall)] with n hn hu
  have hOD : (O : Set ℂ) ⊆ D n := by
    rw [hO]
    exact (ball_subset_ball (by linarith)).trans (hBD n)
  have htv := hC O hO ρ hρO hρ1 h P hh (D n) (hDb n)
    (L n) hn (hBD n) (g n) (Q n) (hg n) δ hδ
  have heq : ig4ZBLaw Ω' O ρ hρO hρ1 h P D g Q n =
      zbLocalCountableLaw O (D n) hOD ρ hρO hρ1 (g n) (Q n) := by
    simp [ig4ZBLaw, hOD]
  rw [heq]
  exact (htv.trans_lt hu).le


end SupercriticalConformalCovariance.TV
