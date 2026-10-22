import HigherDimLQGMetric.Markov.Pairing

/-! Covariance algebra for the projected exterior field. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric TopologicalSpace
open scoped RealInnerProductSpace
open HigherDimLFPP (Rd)

namespace HigherDimLQGMetric

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}

/-- `L²` inner products of LGF test pairings are their logarithmic covariances. -/
theorem markov_inner_pair_eq_logCovRd (hh : IsWholeSpaceLGF h P)
    (φ ψ : TestRd0 d) :
    ⟪(markov_memLp_pair hh φ).toLp (markovPair h φ),
      (markov_memLp_pair hh ψ).toLp (markovPair h ψ)⟫ =
      logCovRd φ.1 ψ.1 := by
  have hcov := hh.covariance_eq φ ψ
  change cov[markovPair h φ, markovPair h ψ; P] = logCovRd φ.1 ψ.1 at hcov
  have hmean : ∫ ω, markovPair h φ ω ∂P = 0 := hh.centered φ
  rw [covariance_eq_sub (markov_memLp_pair hh φ) (markov_memLp_pair hh ψ),
    hmean, zero_mul, sub_zero] at hcov
  simp only [Pi.mul_apply] at hcov
  calc
    _ = ∫ ω, markovPair h φ ω * markovPair h ψ ω ∂P := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [(markov_memLp_pair hh φ).coeFn_toLp,
        (markov_memLp_pair hh ψ).coeFn_toLp] with ω hφ hψ
      rw [hφ, hψ]
      simp [markovPair, mul_comm]
    _ = logCovRd φ.1 ψ.1 := hcov

/-- Symmetry of logarithmic covariance for smooth compact densities. -/
theorem markov_logCovRd_comm (hd : 1 ≤ d) (φ ψ : TestRd d) :
    logCovRd φ ψ = logCovRd ψ φ := by
  letI : NeZero d := ⟨by omega⟩
  obtain ⟨Mφ, Dφ, hφ⟩ := exists_isBddSupp_testOn φ
  obtain ⟨Mψ, Dψ, hψ⟩ := exists_isBddSupp_testOn ψ
  rw [logCovRd_eq_logCovF hφ hψ, logCovRd_eq_logCovF hψ hφ, logCovF_comm]

theorem markov_logCovF_const_mul_left (a : ℝ) (f g : Rd d → ℝ) :
    logCovF (fun x => a * f x) g = a * logCovF f g := by
  unfold logCovF
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ fun p => by ring

/-- Bilinearity in the first argument of the frozen iterated logarithmic covariance. -/
theorem markov_logCovRd_sub_const_mul_left (hd : 1 ≤ d)
    (φ ρ ψ : TestRd d) (a : ℝ) :
    logCovRd (φ - a • ρ) ψ = logCovRd φ ψ - a * logCovRd ρ ψ := by
  letI : NeZero d := ⟨by omega⟩
  obtain ⟨Mφ, Dφ, hφ⟩ := exists_isBddSupp_testOn φ
  obtain ⟨Mρ, Dρ, hρ⟩ := exists_isBddSupp_testOn ρ
  obtain ⟨Mψ, Dψ, hψ⟩ := exists_isBddSupp_testOn ψ
  obtain ⟨Msub, Dsub, hsubB⟩ := exists_isBddSupp_testOn (φ - a • ρ)
  have hρa : IsBddSupp (fun x => a * ρ x) (|a| * Mρ) Dρ := hρ.const_mul a
  have hsub : (fun x : Rd d => (φ - a • ρ) x) =
      (fun x => φ x - a * ρ x) := by funext x; simp [smul_eq_mul]
  have hmul : (fun x : Rd d => (a • ρ : TestRd d) x) =
      (fun x => a * ρ x) := by funext x; simp [smul_eq_mul]
  rw [logCovRd_eq_logCovF hsubB hψ]
  -- Work in the symmetric product integral, where subtraction and scalar multiplication are
  -- ordinary Bochner integral identities.
  rw [logCovRd_eq_logCovF hφ hψ, logCovRd_eq_logCovF hρ hψ]
  change logCovF ((fun x => φ x) - (fun x => a * ρ x)) (fun x => ψ x) =
    logCovF (fun x => φ x) (fun x => ψ x) - a * logCovF (fun x => ρ x) (fun x => ψ x)
  rw [logCovF_sub_left hφ hρa hψ, markov_logCovF_const_mul_left]

/-- The covariance with the normalizing test is integration against its smooth logarithmic
potential. -/
theorem markov_logCovRd_eq_integral_logPot (hd : 1 ≤ d)
    (ρ φ : TestRd d) :
    logCovRd ρ φ = ∫ y, markovLogPot ρ y * φ y := by
  rw [markov_logCovRd_comm hd ρ φ]
  unfold logCovRd
  apply integral_congr_ae
  refine ae_of_all _ fun y => ?_
  change (∫ x, φ y * (-Real.log ‖y - x‖) * ρ x) =
    markovLogPot ρ y * φ y
  rw [mul_comm (markovLogPot ρ y) (φ y)]
  unfold markovLogPot
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ fun x => by ring

/-- The logarithmic kernel at an exterior point is integrable against every compact test
supported in the interior. -/
theorem markov_integrable_pointLog_inside
    (V : Opens (Rd d)) (hVb : Bornology.IsBounded (V : Set (Rd d)))
    (φ : TestRd d) (hφV : tsupport (φ : Rd d → ℝ) ⊆ V)
    (x : Rd d) (hx : x ∈ extOpen V) :
    Integrable (fun y : Rd d => -Real.log ‖x - y‖ * φ y) := by
  obtain ⟨χ, hχ, _, hχ1, hχ0⟩ := markov_exists_cutoff V hVb hx
  have hcut : Integrable
      (fun y : Rd d => (χ y * (-Real.log ‖x - y‖)) * φ y) :=
    ((markov_contDiff_cutLog x hχ hχ0).continuous.mul φ.continuous)
      |>.integrable_of_hasCompactSupport φ.hasCompactSupport.mul_left
  apply hcut.congr
  refine ae_of_all _ fun y => ?_
  by_cases hy : y ∈ V
  · change χ y * (-Real.log ‖x - y‖) * φ y = -Real.log ‖x - y‖ * φ y
    rw [hχ1 y (subset_closure hy), one_mul]
  · have hφ0 : φ y = 0 :=
      image_eq_zero_of_notMem_tsupport (fun ht => hy (hφV ht))
    change χ y * (-Real.log ‖x - y‖) * φ y = -Real.log ‖x - y‖ * φ y
    simp [hφ0]

/-- Recentring an exterior test at `ρ` equals integrating its pointwise covariance after
subtracting the logarithmic potential of `ρ`. -/
theorem markov_logCovRd_recenter_outer (hd : 1 ≤ d)
    (ψ ρ φ : TestRd d) :
    logCovRd (ψ - (∫ x, ψ x) • ρ) φ =
      ∫ x, ψ x * (∫ y,
        (-Real.log ‖x - y‖ - markovLogPot ρ y) * φ y) := by
  letI : NeZero d := ⟨by omega⟩
  obtain ⟨Mψ, Dψ, hψ⟩ := exists_isBddSupp_testOn ψ
  obtain ⟨Mφ, Dφ, hφ⟩ := exists_isBddSupp_testOn φ
  let f : Rd d × Rd d → ℝ := fun p => ψ p.1 * φ p.2 * (-Real.log ‖p.1 - p.2‖)
  let g : Rd d × Rd d → ℝ := fun p => ψ p.1 *
    (markovLogPot ρ p.2 * φ p.2)
  have hf : Integrable f (volume.prod volume) := integrable_logKer hψ hφ
  have hpot : Integrable (fun y => markovLogPot ρ y * φ y) :=
    (((markov_contDiff_logPot hd ρ).continuous).mul φ.continuous)
      |>.integrable_of_hasCompactSupport φ.hasCompactSupport.mul_left
  have hg : Integrable g (volume.prod volume) := by
    have h : Integrable (fun x : Rd d => ψ x) volume :=
      ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport
    exact h.mul_prod hpot
  have hinner (x : Rd d) :
      ψ x * (∫ y, (-Real.log ‖x - y‖ - markovLogPot ρ y) * φ y) =
      ∫ y, f (x,y) - g (x,y) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun y => by
      change ψ x * ((-Real.log ‖x - y‖ - markovLogPot ρ y) * φ y) =
        f (x,y) - g (x,y)
      simp only [f, g]
      ring
  simp_rw [hinner]
  have hsplit : (∫ x, ∫ y, f (x,y) - g (x,y)) =
      ∫ x, (∫ y, f (x,y)) - (∫ y, g (x,y)) := by
    simpa only [id_eq] using (integral_fn_integral_sub (F := id) hf hg)
  rw [hsplit]
  rw [integral_sub hf.integral_prod_left hg.integral_prod_left]
  have hfCov : (∫ x, ∫ y, f (x,y)) = logCovRd ψ φ := by
    unfold logCovRd
    apply integral_congr_ae
    refine ae_of_all _ fun x => ?_
    apply integral_congr_ae
    exact ae_of_all _ fun y => by
      change f (x,y) = ψ x * (-Real.log ‖x - y‖) * φ y
      simp only [f]
      ring
  have hgPot : (∫ x, ∫ y, g (x,y)) =
      (∫ x, ψ x) * (∫ y, markovLogPot ρ y * φ y) := by
    have he (x : Rd d) : (∫ y, g (x,y)) =
        ψ x * (∫ y, markovLogPot ρ y * φ y) := by
      change (∫ y, ψ x * (markovLogPot ρ y * φ y)) = _
      exact integral_const_mul _ _
    simp_rw [he]
    exact integral_mul_const _ _
  rw [hfCov, hgPot, ← markov_logCovRd_eq_integral_logPot hd ρ φ]
  exact markov_logCovRd_sub_const_mul_left hd ψ ρ φ (∫ x, ψ x)

end HigherDimLQGMetric
