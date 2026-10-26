import HigherDimLQGMetric.Sec4.LocAnalysis
import HigherDimLQGMetric.ConvField.RadialAll

/-!
# The localized radial identity on one almost-sure event (packet F1b, MA3 P2.1)

For a normalized LGF `h`, almost surely, simultaneously for **every** kernel scale `ε > 0`, cutoff radius `s > 0` and
centre `z`, the pairing of `h` with the localized test function `w ↦ ψ((w − z)/(s/2)) K_ε(w − z)` (`locTest κ ε s z`)
has the polar form
`⟨h, locTest κ ε s z⟩ = |S^{d−1}| ∫_0^∞ r^{d−1} locKer κ ε s (r e₁) h_r(z) dr`.

The repository's `l2b_ae_radial_pairing` gives this almost surely for one fixed test and centre. The common event is
obtained by the standard argument (the template is the host's `l2b_ae_convTrunc_radial_all`): both sides are continuous
in `(ε, s, z)` on `{ε > 0, s > 0}`, so equality on a countable dense set of parameters (a countable intersection of
almost-sure events) extends to all parameters.
* The left side is continuous because `(ε, s, z) ↦ locTest κ ε s z` is continuous into `𝓓(ℝ^d)` and `h ω` is a
  continuous linear functional. The family is reparametrized by `(ε⁻¹, (s/2)⁻¹, z)`, in which the kernel
  `a^d K(a v) ψ(b v)` (`locKerP_F1b`) is jointly smooth (`continuousOn_locTest_F1b`).
* The right side is continuous by dominated convergence: the integrand is compactly supported in `r ≤ s`, bounded
  through the joint continuity of the sphere-average process and its logarithmic growth near `r = 0`
  (`continuousOn_locKer_radial_integral_F1b`).

Main results: `ae_locTest_radial_all_F1b` and its `locField` form `ae_locField_radial_all_F1b`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric TopologicalSpace
open HigherDimLFPP (Rd e₁)
open HigherDimLQGMetric

namespace HigherDimLFPPAS.Field

variable {d : ℕ} {κ : Rd d → ℝ}

/-- The localized kernel in the parameters `a = ε⁻¹`, `b = (s/2)⁻¹`: `v ↦ a^d K(a v) ψ(b v)` with the radial profile
`ψ = radBump 1 2` (`1` on the unit ball, `0` off the ball of radius `2`). Jointly smooth in `(a, b, v)`;
`locKer κ ε s = locKerP_F1b κ ε⁻¹ (s/2)⁻¹` for `ε, s > 0` (`locKer_eq_locKerP_F1b`). -/
def locKerP_F1b (κ : Rd d → ℝ) (a b : ℝ) (v : Rd d) : ℝ :=
  a ^ d * convKernel κ (a • v) * radBump 1 2 (b • v)

theorem locKer_eq_locKerP_F1b (κ : Rd d → ℝ) {ε s : ℝ} (hε : 0 < ε) (hs : 0 < s) (v : Rd d) :
    locKer κ ε s v = locKerP_F1b κ ε⁻¹ (s / 2)⁻¹ v := by
  have hs2 : s / (s / 2) = 2 / 1 := by field_simp
  unfold locKer convKernelEps locKerP_F1b radBump
  rw [hs2, Real.rpow_neg hε.le, Real.rpow_natCast, inv_pow, inv_one, one_smul]

theorem contDiff_locKerP_F1b (hK : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (convKernel κ)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : (ℝ × ℝ) × Rd d => locKerP_F1b κ p.1.1 p.1.2 p.2) := by
  have ha : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : (ℝ × ℝ) × Rd d => p.1.1) :=
    contDiff_fst.comp contDiff_fst
  have hb : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : (ℝ × ℝ) × Rd d => p.1.2) :=
    contDiff_snd.comp contDiff_fst
  have hv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : (ℝ × ℝ) × Rd d => p.2) := contDiff_snd
  exact ((ha.pow d).mul (hK.comp (ha.smul hv))).mul
    ((contDiff_radBump (d := d) one_pos one_lt_two).comp (hb.smul hv))

/-- The parameter set `{(ε, s, z) : ε > 0, s > 0}`. -/
theorem isOpen_posParams_F1b :
    IsOpen {q : (ℝ × ℝ) × Rd d | 0 < q.1.1 ∧ 0 < q.1.2} :=
  (isOpen_lt continuous_const (continuous_fst.comp continuous_fst)).inter
    (isOpen_lt continuous_const (continuous_snd.comp continuous_fst))

/-- Coordinate bounds on a closed ball of the parameter space. -/
private theorem param_bounds_F1b {q q₀ : (ℝ × ℝ) × Rd d} {ρ : ℝ} (hq : q ∈ closedBall q₀ ρ) :
    |q.1.1 - q₀.1.1| ≤ ρ ∧ |q.1.2 - q₀.1.2| ≤ ρ ∧ ‖q.2 - q₀.2‖ ≤ ρ := by
  rw [mem_closedBall, Prod.dist_eq] at hq
  have h1 : dist q.1 q₀.1 ≤ ρ := (le_max_left _ _).trans hq
  have h2 : dist q.2 q₀.2 ≤ ρ := (le_max_right _ _).trans hq
  rw [Prod.dist_eq] at h1
  have h11 : dist q.1.1 q₀.1.1 ≤ ρ := (le_max_left _ _).trans h1
  have h12 : dist q.1.2 q₀.1.2 ≤ ρ := (le_max_right _ _).trans h1
  rw [Real.dist_eq] at h11 h12
  rw [dist_eq_norm] at h2
  exact ⟨h11, h12, h2⟩

/-- `(ε, s, z) ↦ locTest κ ε s z` is continuous into `𝓓(ℝ^d)` on `{ε > 0, s > 0}`. -/
theorem continuousOn_locTest_F1b (hK : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (convKernel κ)) :
    ContinuousOn (fun q : (ℝ × ℝ) × Rd d => locTest κ q.1.1 q.1.2 q.2)
      {q | 0 < q.1.1 ∧ 0 < q.1.2} := by
  intro q₀ hq₀
  obtain ⟨hε₀, hs₀⟩ := hq₀
  set ρ : ℝ := min q₀.1.1 q₀.1.2 / 2 with hρ
  have hρ0 : 0 < ρ := by rw [hρ]; exact half_pos (lt_min hε₀ hs₀)
  have hρε : ρ ≤ q₀.1.1 / 2 := by
    rw [hρ]; exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hρs : ρ ≤ q₀.1.2 / 2 := by
    rw [hρ]; exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  let S : Set ((ℝ × ℝ) × Rd d) := closedBall q₀ ρ
  have : CompactSpace S := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  have hSε : ∀ q : S, 0 < (q : (ℝ × ℝ) × Rd d).1.1 := fun q => by
    have h := (param_bounds_F1b q.2).1
    rw [abs_le] at h
    linarith
  have hSs : ∀ q : S, 0 < (q : (ℝ × ℝ) × Rd d).1.2 := fun q => by
    have h := (param_bounds_F1b q.2).2.1
    rw [abs_le] at h
    linarith
  let K : Compacts (Rd d) := ⟨closedBall q₀.2 (q₀.1.2 + 2 * ρ), isCompact_closedBall _ _⟩
  let Ψ : S → Rd d → ℝ := fun q w =>
    locKer κ (q : (ℝ × ℝ) × Rd d).1.1 (q : (ℝ × ℝ) × Rd d).1.2 (w - (q : (ℝ × ℝ) × Rd d).2)
  have hs : ∀ q : S, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Ψ q) := fun q =>
    (contDiff_locKer hK _ (hSs q)).comp (contDiff_id.sub contDiff_const)
  have hKs : ∀ q : S, ∀ w ∉ (K : Set (Rd d)), Ψ q w = 0 := by
    intro q w hw
    have hw' : q₀.1.2 + 2 * ρ < ‖w - q₀.2‖ := by
      simpa [K, mem_closedBall, dist_eq_norm] using hw
    obtain ⟨-, h2, h3⟩ := param_bounds_F1b q.2
    rw [abs_le] at h2
    have htri : ‖w - q₀.2‖ ≤ ‖w - (q : (ℝ × ℝ) × Rd d).2‖ + ‖(q : (ℝ × ℝ) × Rd d).2 - q₀.2‖ := by
      calc ‖w - q₀.2‖ = ‖(w - (q : (ℝ × ℝ) × Rd d).2) + ((q : (ℝ × ℝ) × Rd d).2 - q₀.2)‖ := by
            congr 1; abel
        _ ≤ _ := norm_add_le _ _
    exact locKer_eq_zero κ _ (hSs q) (by linarith)
  -- the derivatives through the smooth reparametrization `(ε, s, z) ↦ (ε⁻¹, (s/2)⁻¹, z)`
  let Φ : (ℝ × ℝ) × Rd d → Rd d → ℝ := fun p w => locKerP_F1b κ p.1.1 p.1.2 (w - p.2)
  let θ : S → (ℝ × ℝ) × Rd d := fun q =>
    (((q : (ℝ × ℝ) × Rd d).1.1⁻¹, ((q : (ℝ × ℝ) × Rd d).1.2 / 2)⁻¹), (q : (ℝ × ℝ) × Rd d).2)
  have hΨΦ : ∀ q : S, Ψ q = Φ (θ q) := fun q => funext fun w =>
    locKer_eq_locKerP_F1b κ (hSε q) (hSs q) _
  have hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry Φ) := by
    have hmap : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : ((ℝ × ℝ) × Rd d) × Rd d => (((x.1.1.1, x.1.1.2), x.2 - x.1.2) : (ℝ × ℝ) × Rd d)) := by
      fun_prop
    exact (contDiff_locKerP_F1b hK).comp hmap
  have hθ : Continuous θ := by
    have hv : Continuous fun q : S => (q : (ℝ × ℝ) × Rd d) := continuous_subtype_val
    refine Continuous.prodMk (Continuous.prodMk ?_ ?_) hv.snd
    · exact hv.fst.fst.inv₀ fun q => (hSε q).ne'
    · exact (hv.fst.snd.div_const 2).inv₀ fun q => (half_pos (hSs q)).ne'
  have hD : ∀ i : ℕ, Continuous fun p : S × Rd d => iteratedFDeriv ℝ i (Ψ p.1) p.2 := by
    intro i
    have e : (fun p : S × Rd d => iteratedFDeriv ℝ i (Ψ p.1) p.2) =
        (fun p : ((ℝ × ℝ) × Rd d) × Rd d => iteratedFDeriv ℝ i (Φ p.1) p.2) ∘
          (fun p : S × Rd d => (θ p.1, p.2)) := by
      funext p
      simp only [Function.comp_apply, hΨΦ]
    rw [e]
    exact (l2b_continuous_iteratedFDeriv_snd hΦ i).comp ((hθ.comp continuous_fst).prodMk continuous_snd)
  have hc := continuous_testFamK K Ψ hs hKs hD
  have e : (fun q : S => locTest κ (q : (ℝ × ℝ) × Rd d).1.1 (q : (ℝ × ℝ) × Rd d).1.2
      (q : (ℝ × ℝ) × Rd d).2) = ofSuppRd K ∘ testFamK K Ψ hs hKs := by
    funext q
    refine TestFunction.ext fun y => ?_
    show locTest κ (q : (ℝ × ℝ) × Rd d).1.1 (q : (ℝ × ℝ) × Rd d).1.2 (q : (ℝ × ℝ) × Rd d).2 y = Ψ q y
    rw [locTest_apply hK (hSs q)]
  have h2 : Continuous fun q : S => locTest κ (q : (ℝ × ℝ) × Rd d).1.1 (q : (ℝ × ℝ) × Rd d).1.2
      (q : (ℝ × ℝ) × Rd d).2 := by
    rw [e]; exact (ofSuppRd K).continuous.comp hc
  exact ((continuousOn_iff_continuous_domRestrict.2 h2).continuousAt
    (closedBall_mem_nhds _ hρ0)).continuousWithinAt

/-- The axis values of the localized kernel are jointly continuous in `(ε, s, z, r)` on `{ε > 0, s > 0}`. -/
theorem continuousOn_locKer_axis_F1b (hK : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (convKernel κ)) :
    ContinuousOn (fun p : ((ℝ × ℝ) × Rd d) × ℝ => locKer κ p.1.1.1 p.1.1.2 (p.2 • e₁ d))
      {p | 0 < p.1.1.1 ∧ 0 < p.1.1.2} := by
  have hP : ContinuousOn (fun p : ((ℝ × ℝ) × Rd d) × ℝ =>
      locKerP_F1b κ p.1.1.1⁻¹ (p.1.1.2 / 2)⁻¹ (p.2 • e₁ d)) {p | 0 < p.1.1.1 ∧ 0 < p.1.1.2} := by
    have hmap : ContinuousOn (fun p : ((ℝ × ℝ) × Rd d) × ℝ =>
        (((p.1.1.1⁻¹, (p.1.1.2 / 2)⁻¹), p.2 • e₁ d) : (ℝ × ℝ) × Rd d))
        {p | 0 < p.1.1.1 ∧ 0 < p.1.1.2} := by
      refine ContinuousOn.prodMk (ContinuousOn.prodMk ?_ ?_) ?_
      · exact (continuous_fst.comp (continuous_fst.comp continuous_fst)).continuousOn.inv₀
          fun p hp => hp.1.ne'
      · exact ((continuous_snd.comp (continuous_fst.comp continuous_fst)).div_const 2).continuousOn.inv₀
          fun p hp => (half_pos hp.2).ne'
      · exact (continuous_snd.smul continuous_const).continuousOn
    exact (contDiff_locKerP_F1b hK).continuous.comp_continuousOn hmap
  refine hP.congr fun p hp => ?_
  exact locKer_eq_locKerP_F1b κ hp.1 hp.2 _

/-- The radial integral of the localized kernel against the sphere-average process is continuous in `(ε, s, z)` on
`{ε > 0, s > 0}`, for every distribution whose sphere averages are jointly continuous and of logarithmic growth. -/
theorem continuousOn_locKer_radial_integral_F1b (hd : 2 ≤ d)
    (hK : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (convKernel κ)) (T : DistRd d)
    (hcont : ContinuousOn (fun p : ℝ × Rd d => sphereAvg T p.1 p.2) (Ioi 0 ×ˢ univ))
    (hgrowth : ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ z ∈ closedBall (0 : Rd d) (N : ℝ), ∀ r : ℝ, 0 < r →
        |sphereAvg T r z| ≤ C * l2b_growthWeight r) :
    ContinuousOn (fun q : (ℝ × ℝ) × Rd d =>
      ∫ r in Ioi (0 : ℝ), r ^ (d - 1) * locKer κ q.1.1 q.1.2 (r • e₁ d) * sphereAvg T r q.2)
      {q | 0 < q.1.1 ∧ 0 < q.1.2} := by
  intro q₀ hq₀
  refine ContinuousAt.continuousWithinAt ?_
  obtain ⟨hε₀, hs₀⟩ := hq₀
  set ρ : ℝ := min q₀.1.1 q₀.1.2 / 2 with hρ
  have hρ0 : 0 < ρ := by rw [hρ]; exact half_pos (lt_min hε₀ hs₀)
  have hρε : ρ ≤ q₀.1.1 / 2 := by
    rw [hρ]; exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hρs : ρ ≤ q₀.1.2 / 2 := by
    rw [hρ]; exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  let V : Set ((ℝ × ℝ) × Rd d) := closedBall q₀ ρ
  have hVpos : ∀ q ∈ V, 0 < q.1.1 ∧ 0 < q.1.2 := fun q hq => by
    obtain ⟨h1, h2, -⟩ := param_bounds_F1b hq
    rw [abs_le] at h1 h2
    exact ⟨by linarith, by linarith⟩
  have hVs : ∀ q ∈ V, q.1.2 ≤ q₀.1.2 + ρ := fun q hq => by
    have h2 := (param_bounds_F1b hq).2.1
    rw [abs_le] at h2
    linarith
  -- the radial range and the centre range
  let R : ℝ := max (q₀.1.2 + ρ) 1
  have hR1 : 1 ≤ R := le_max_right _ _
  obtain ⟨N, hN⟩ := exists_nat_gt (‖q₀.2‖ + ρ)
  obtain ⟨C, hC0, hC⟩ := hgrowth N
  have hVz : ∀ q ∈ V, q.2 ∈ closedBall (0 : Rd d) (N : ℝ) := fun q hq => by
    have h3 := (param_bounds_F1b hq).2.2
    rw [mem_closedBall, dist_zero_right]
    have : ‖q.2‖ ≤ ‖q.2 - q₀.2‖ + ‖q₀.2‖ := by
      calc ‖q.2‖ = ‖(q.2 - q₀.2) + q₀.2‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
    linarith
  -- a uniform bound for the kernel factor
  have hKc : IsCompact (V ×ˢ Icc (0 : ℝ) R) := (isCompact_closedBall _ _).prod isCompact_Icc
  have hfac : ContinuousOn (fun p : ((ℝ × ℝ) × Rd d) × ℝ => |locKer κ p.1.1.1 p.1.1.2 (p.2 • e₁ d)|)
      (V ×ˢ Icc (0 : ℝ) R) :=
    ((continuousOn_locKer_axis_F1b hK).mono fun p hp => hVpos p.1 hp.1).abs
  obtain ⟨M₀, hM₀⟩ := hKc.bddAbove_image hfac
  let M : ℝ := max M₀ 0
  have hM0 : 0 ≤ M := le_max_right _ _
  have hM : ∀ q ∈ V, ∀ r ∈ Icc (0 : ℝ) R, |locKer κ q.1.1 q.1.2 (r • e₁ d)| ≤ M := by
    intro q hq r hr
    exact (hM₀ (mem_image_of_mem _ (show (q, r) ∈ V ×ˢ Icc 0 R from ⟨hq, hr⟩))).trans
      (le_max_left _ _)
  let B : ℝ := R ^ (d - 1) * max (Real.log R) 1 + 1
  let D : ℝ := M * C * B
  let bound : ℝ → ℝ := (Icc (0 : ℝ) R).indicator fun _ => D
  have hboundI : Integrable bound (volume.restrict (Ioi (0 : ℝ))) :=
    (integrableOn_const isCompact_Icc.measure_ne_top).integrable_indicator measurableSet_Icc
  have hVn : V ∈ 𝓝 q₀ := closedBall_mem_nhds _ hρ0
  have hd0 : 0 < d := by omega
  let F : (ℝ × ℝ) × Rd d → ℝ → ℝ := fun q r =>
    r ^ (d - 1) * locKer κ q.1.1 q.1.2 (r • e₁ d) * sphereAvg T r q.2
  change ContinuousAt (fun q => ∫ r in Ioi (0 : ℝ), F q r) q₀
  apply continuousAt_of_dominated (μ := volume.restrict (Ioi (0 : ℝ))) (F := F) (bound := bound)
  · filter_upwards [hVn] with q hq
    have hrad : ContinuousOn (fun r : ℝ => sphereAvg T r q.2) (Ioi 0) := by
      have hpc : Continuous fun r : ℝ => ((r, q.2) : ℝ × Rd d) :=
        continuous_id.prodMk continuous_const
      exact ContinuousOn.comp (f := fun r : ℝ => ((r, q.2) : ℝ × Rd d))
        (g := fun p : ℝ × Rd d => sphereAvg T p.1 p.2) hcont hpc.continuousOn
        (fun r hr => mk_mem_prod hr (mem_univ _))
    have hker : Continuous fun r : ℝ => locKer κ q.1.1 q.1.2 (r • e₁ d) :=
      (continuous_locKer hK _ (hVpos q hq).2).comp (continuous_id.smul continuous_const)
    have hF : ContinuousOn (F q) (Ioi 0) :=
      ((continuous_id.pow _).mul hker).continuousOn.mul hrad
    exact hF.aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [hVn] with q hq
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    have hr0 : 0 < r := hr
    by_cases hrR : r ≤ R
    · have hrK : r ∈ Icc (0 : ℝ) R := ⟨hr0.le, hrR⟩
      have hprod := l2b_polar_log_weight_bounded hd hR1 hr0 hrR
      have hgrow := hC q.2 (hVz q hq) r hr0
      have hp0 : 0 ≤ r ^ (d - 1) := pow_nonneg hr0.le _
      have hax := hM q hq r hrK
      have hmain : |F q r| ≤ D := by
        dsimp only [F, D, B]
        rw [abs_mul, abs_mul, abs_of_nonneg hp0]
        calc r ^ (d - 1) * |locKer κ q.1.1 q.1.2 (r • e₁ d)| * |sphereAvg T r q.2|
            ≤ r ^ (d - 1) * M * (C * l2b_growthWeight r) := by gcongr
          _ = M * C * (r ^ (d - 1) * l2b_growthWeight r) := by ring
          _ ≤ M * C * (R ^ (d - 1) * max (Real.log R) 1 + 1) := by
            apply mul_le_mul_of_nonneg_left _ (mul_nonneg hM0 hC0)
            exact hprod
      simpa only [Real.norm_eq_abs, bound, Set.indicator_of_mem hrK] using hmain
    · have hsr : q.1.2 ≤ ‖r • e₁ d‖ := by
        rw [norm_smul, HigherDimLFPP.norm_e₁ hd0, mul_one, Real.norm_eq_abs, abs_of_pos hr0]
        have := hVs q hq
        have : q₀.1.2 + ρ ≤ R := le_max_left _ _
        linarith [not_le.1 hrR]
      have hzero : locKer κ q.1.1 q.1.2 (r • e₁ d) = 0 := locKer_eq_zero κ _ (hVpos q hq).2 hsr
      have hnot : r ∉ Icc (0 : ℝ) R := fun hh => hrR hh.2
      simp [F, hzero, bound, Set.indicator_of_notMem hnot]
  · exact hboundI
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with r hr
    have hs : ContinuousAt (fun q : (ℝ × ℝ) × Rd d => sphereAvg T r q.2) q₀ := by
      have hmem : (r, q₀.2) ∈ Ioi 0 ×ˢ univ := ⟨hr, trivial⟩
      have hc : ContinuousAt (fun p : ℝ × Rd d => sphereAvg T p.1 p.2) (r, q₀.2) :=
        hcont.continuousAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds hmem)
      exact hc.comp₂ continuousAt_const continuousAt_snd
    have hfac' : ContinuousAt (fun q : (ℝ × ℝ) × Rd d => locKer κ q.1.1 q.1.2 (r • e₁ d)) q₀ := by
      have hopen : IsOpen {p : ((ℝ × ℝ) × Rd d) × ℝ | 0 < p.1.1.1 ∧ 0 < p.1.1.2} :=
        (isOpen_lt continuous_const (continuous_fst.comp (continuous_fst.comp continuous_fst))).inter
          (isOpen_lt continuous_const (continuous_snd.comp (continuous_fst.comp continuous_fst)))
      have hca := (continuousOn_locKer_axis_F1b hK).continuousAt
        (hopen.mem_nhds (show (q₀, r) ∈ {p : ((ℝ × ℝ) × Rd d) × ℝ | 0 < p.1.1.1 ∧ 0 < p.1.1.2}
          from ⟨hε₀, hs₀⟩))
      exact ContinuousAt.comp (f := fun q : (ℝ × ℝ) × Rd d => (q, r)) (x := q₀) hca
        (by fun_prop)
    exact (continuousAt_const.mul hfac').mul hs

/-- **The localized radial identity on one event** (MA3 P2.1 for the localized kernels): for a normalized LGF `h` and a
smooth kernel, almost surely, for **all** `ε > 0`, `s > 0` and `z`,
`⟨h, locTest κ ε s z⟩ = |S^{d−1}| ∫_0^∞ r^{d−1} (locTest κ ε s z)(z + r e₁) h_r(z) dr`. -/
theorem ae_locTest_radial_all_F1b (hd : 2 ≤ d)
    (hK : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (convKernel κ))
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hh : IsNormalizedLGF h P) :
    ∀ᵐ ω ∂P, ∀ ε s : ℝ, 0 < ε → 0 < s → ∀ z : Rd d,
      h ω (locTest κ ε s z) = sphArea d * ∫ r in Ioi (0 : ℝ),
        r ^ (d - 1) * locTest κ ε s z (z + r • e₁ d) * sphereAvg (h ω) r z := by
  let U : Set ((ℝ × ℝ) × Rd d) := {q | 0 < q.1.1 ∧ 0 < q.1.2}
  have hU : IsOpen U := isOpen_posParams_F1b
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense ((ℝ × ℝ) × Rd d)
  have : Countable S := hSc.to_subtype
  -- the per-parameter identity, on a countable intersection of events
  have hfix : ∀ᵐ ω ∂P, ∀ p : S, (p : (ℝ × ℝ) × Rd d) ∈ U →
      h ω (locTest κ (p : (ℝ × ℝ) × Rd d).1.1 (p : (ℝ × ℝ) × Rd d).1.2 (p : (ℝ × ℝ) × Rd d).2) =
        sphArea d * ∫ r in Ioi (0 : ℝ), r ^ (d - 1) *
          locKer κ (p : (ℝ × ℝ) × Rd d).1.1 (p : (ℝ × ℝ) × Rd d).1.2 (r • e₁ d) *
            sphereAvg (h ω) r (p : (ℝ × ℝ) × Rd d).2 := by
    rw [ae_all_iff]
    intro p
    by_cases hp : (p : (ℝ × ℝ) × Rd d) ∈ U
    · filter_upwards [l2b_ae_radial_pairing hd hh.1
        (locTest κ (p : (ℝ × ℝ) × Rd d).1.1 (p : (ℝ × ℝ) × Rd d).1.2 (p : (ℝ × ℝ) × Rd d).2)
        (p : (ℝ × ℝ) × Rd d).2 (locTest_radial (by omega) hK hp.2 _)] with ω hω
      intro _
      rw [hω]
      unfold sphArea
      congr 1
      refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
      simp only [locTest_axis hK hp.2]
    · exact Eventually.of_forall fun _ hmem => absurd hmem hp
  filter_upwards [hfix, hh.1.ae_continuousOn_sphereAvg hd, l2b_ae_growth_all hd hh]
    with ω hfix hcont hgrowth
  let lhs : (ℝ × ℝ) × Rd d → ℝ := fun q => h ω (locTest κ q.1.1 q.1.2 q.2)
  let rhs : (ℝ × ℝ) × Rd d → ℝ := fun q => sphArea d * ∫ r in Ioi (0 : ℝ),
    r ^ (d - 1) * locKer κ q.1.1 q.1.2 (r • e₁ d) * sphereAvg (h ω) r q.2
  have hlhs : ContinuousOn lhs U := (map_continuous (h ω)).comp_continuousOn (continuousOn_locTest_F1b hK)
  have hrhs : ContinuousOn rhs U :=
    continuousOn_const.mul (continuousOn_locKer_radial_integral_F1b hd hK (h ω) hcont.2 hgrowth)
  have hEq : EqOn lhs rhs (U ∩ S) := fun q hq => hfix ⟨q, hq.2⟩ hq.1
  have hall : EqOn lhs rhs U :=
    hEq.of_subset_closure hlhs hrhs inter_subset_left (hSd.open_subset_closure_inter hU)
  intro ε s hε hs z
  have h1 := hall (show ((ε, s), z) ∈ U from ⟨hε, hs⟩)
  simp only [lhs, rhs] at h1
  rw [h1]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
  simp only [locTest_axis hK hs]

/-- **The localized field in polar form, on one event**: almost surely, for every `ε > 0` with `locRad ε > 0` (i.e.
`ε ≠ 1`) and every `z`, `ĥ*_ε(z) = Z_ε⁻¹ |S^{d−1}| ∫_0^∞ r^{d−1} (ψ_ε K_ε)(r e₁) h_r(z) dr`. -/
theorem ae_locField_radial_all_F1b (hd : 2 ≤ d)
    (hK : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (convKernel κ))
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hh : IsNormalizedLGF h P) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → 0 < locRad ε → ∀ z : Rd d,
      locField κ ε (h ω) z = (locMass κ ε (locRad ε))⁻¹ * (sphArea d * ∫ r in Ioi (0 : ℝ),
        r ^ (d - 1) * locKer κ ε (locRad ε) (r • e₁ d) * sphereAvg (h ω) r z) := by
  filter_upwards [ae_locTest_radial_all_F1b hd hK hh] with ω hω
  intro ε hε hs z
  unfold locField
  rw [hω ε (locRad ε) hε hs z]
  congr 2
  refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
  simp only [locTest_axis hK hs]

end HigherDimLFPPAS.Field
