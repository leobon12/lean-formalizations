import SupercriticalConformalCovariance.Markov.GeneralRect
import LQGMetric.Field.MarkovVer2Fub

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric TopologicalSpace
open scoped RealInnerProductSpace

namespace SupercriticalConformalCovariance.Markov

open LQGMetric LQGMetric.MarkovZB LQGMetric.MarkovExt LQGMetric.MarkovVer2
  LQGMetric.GFFExist LQGMetric.Blueprint QuantumZipper QuantumZipper.K3

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistC} {V : Opens ℂ}

theorem integral_d12_inner_rieszFun_general (hh : IsWholePlaneGFF h P)
    (hV : ZBAdmissible V)
    (hpos : ∃ g ∈ zeroSpace V, 0 < dirichletEnergyOn V g)
    (β : TestOn V) (hβ : ∫ x, β x = 1)
    (φ : TestC) {f : ℂ → ℝ} (hf : f ∈ zeroSpace V) :
    ∫ x, d12 φ x * ⟪rieszFun V (rectDens V x), gradFeat V f⟫ =
      ⟪rieszFun V ((V : Set ℂ).indicator φ), gradFeat V f⟫ := by
  have hfc : Continuous f := hf.1.continuous
  obtain ⟨Cf, hCf⟩ := hfc.bounded_above_of_compact_support hf.2.1
  have hKm : Measurable ((V : Set ℂ).indicator f) :=
    hfc.measurable.indicator V.isOpen.measurableSet
  have hKb : ∀ u, |(V : Set ℂ).indicator f u| ≤ Cf := fun u => by
    by_cases hu : u ∈ (V : Set ℂ)
    · rw [indicator_of_mem hu, ← Real.norm_eq_abs]; exact hCf u
    · rw [indicator_of_notMem hu, abs_zero]; exact (norm_nonneg _).trans (hCf u)
  have e : ∀ x, ⟪rieszFun V (rectDens V x), gradFeat V f⟫ =
      ∫ u, rectInd x u * (V : Set ℂ).indicator f u := fun x => by
    rw [inner_rieszFun_bddSupp hh hV hpos β hβ
      (rectBdd V (T := |x.re| + |x.im| + 1) (by linarith))
      (rectZero V x) hf]
    congr 1
    funext u
    by_cases hu : u ∈ (V : Set ℂ)
    · simp [rectDens, indicator_of_mem hu]
    · simp [rectDens, indicator_of_notMem hu]
  simp_rw [e]
  rw [LQGMetric.MarkovVer2.integral_d12_mul_integral_rect φ hKm hKb,
    inner_rieszFun_indicator_gradFeat hh hV hpos φ hf]
  congr 1
  funext u
  by_cases hu : u ∈ (V : Set ℂ)
  · simp [indicator_of_mem hu, mul_comm]
  · have hf0 : f u = 0 := image_eq_zero_of_notMem_tsupport fun h => hu (hf.2.2 h)
    simp [indicator_of_notMem hu, hf0]

theorem continuous_rectVec_general (hh : IsWholePlaneGFF h P)
    (hV : ZBAdmissible V) : Continuous (rectVec hh V) := by
  by_cases hne : (V : Set ℂ).Nonempty
  · rw [continuous_iff_continuousAt]
    intro x0
    rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
    let A := ‖x0‖ + 1
    obtain ⟨C, hC, hbound⟩ := sq_norm_rectVec_sub_le_general hh hV hne A
    have hb : ∀ᶠ x in 𝓝 x0,
        ‖rectVec hh V x - rectVec hh V x0‖ ≤ √(C * ‖x - x0‖) := by
      filter_upwards [Metric.ball_mem_nhds x0 one_pos] with x hx
      rw [mem_ball, dist_eq_norm] at hx
      have hxA : ‖x‖ ≤ A := by
        have := norm_le_norm_add_norm_sub' x x0
        have : ‖x - x0‖ = ‖x0 - x‖ := norm_sub_rev _ _
        dsimp [A]
        linarith [norm_sub_norm_le x x0]
      have hx0A : ‖x0‖ ≤ A := by dsimp [A]; linarith
      have hs := hbound x x0 ((Complex.abs_re_le_norm x).trans hxA)
        ((Complex.abs_im_le_norm x).trans hxA)
        ((Complex.abs_re_le_norm x0).trans hx0A)
        ((Complex.abs_im_le_norm x0).trans hx0A)
      rw [← abs_of_nonneg (norm_nonneg (rectVec hh V x - rectVec hh V x0))]
      exact Real.abs_le_sqrt hs
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hb ?_
    have hc : Continuous fun x : ℂ => √(C * ‖x - x0‖) := by fun_prop
    simpa using hc.tendsto x0
  · have hVe : (V : Set ℂ) = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    have hzero : ∀ x, rectVec hh V x = 0 := by
      intro x
      have hρ : rectDens V x = 0 := by funext z; simp [rectDens, hVe]
      simp only [rectVec, hρ, extVec, rieszFun_zero]
      convert (cmIso hh V).map_zero using 1
      exact Subtype.ext rfl
    have he : rectVec hh V = fun _ => 0 := funext hzero
    rw [he]
    exact continuous_const

theorem continuous_rVec_general (hh : IsWholePlaneGFF h P)
    (hV : ZBAdmissible V) : Continuous (rVec V) :=
  (cmIso hh V).isometry.comp_continuous_iff.1 (continuous_rectVec_general hh hV)

/-- The rectangle antiderivative integrates back to the canonical extension in L². -/
theorem integral_d12_smul_rectVec_general (hh : IsWholePlaneGFF h P)
    (hV : ZBAdmissible V) (φ : TestC) :
    ∫ x, d12 φ x • rectVec hh V x =
      extVec hh V ((V : Set ℂ).indicator φ) := by
  set K := gradClosure (V : Set ℂ) (zeroSpace V)
  have hDN := isDNSpace_zeroSpace (V : Set ℂ)
  have hi : Integrable fun x => d12 φ x • rVec V x :=
    ((d12 φ).continuous.smul (continuous_rVec_general hh hV)).integrable_of_hasCompactSupport
      (d12 φ).hasCompactSupport.smul_right
  have hi' : Integrable fun x => d12 φ x • (rVec V x : GradSpace V) :=
    ((d12 φ).continuous.smul
      (continuous_subtype_val.comp (continuous_rVec_general hh hV))).integrable_of_hasCompactSupport
      (d12 φ).hasCompactSupport.smul_right
  have hcoe : ((∫ x, d12 φ x • rVec V x : K) : GradSpace V) =
      ∫ x, d12 φ x • (rVec V x : GradSpace V) := by
    have := (K.subtypeL).integral_comp_comm hi
    simpa using this.symm
  have key : (∫ x, d12 φ x • rVec V x : K) =
      ⟨rieszFun V ((V : Set ℂ).indicator φ), rieszFun_mem V _⟩ := by
    apply Subtype.ext
    refine LQGMetric.eq_of_mem_gradClosure (Subtype.mem _) (rieszFun_mem V _)
      fun f hf => ?_
    rw [hcoe, real_inner_comm, ← integral_inner hi']
    have e : ∫ x, ⟪gradFeat (V : Set ℂ) f, d12 φ x • (rVec V x : GradSpace V)⟫ =
        ∫ x, d12 φ x * ⟪rieszFun V (rectDens V x), gradFeat V f⟫ :=
      integral_congr_ae (Eventually.of_forall fun x => by
        simp only [real_inner_smul_right, rVec]
        rw [real_inner_comm])
    rw [e]
    by_cases hne : (V : Set ℂ).Nonempty
    · obtain ⟨β₀, hβV, hβ1⟩ := LQGMetric.HarmLoc.exists_unit_test V.isOpen hne
      let β : TestOn V := ⟨β₀, β₀.contDiff, β₀.hasCompactSupport, hβV⟩
      have hβ : ∫ x, β x = 1 := hβ1
      exact integral_d12_inner_rieszFun_general hh hV
        (exists_pos_energy_zeroSpace_m7d V.isOpen hne) β hβ φ hf
    · have hVe : (V : Set ℂ) = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      have hf0 : f = 0 := by
        funext z
        exact image_eq_zero_of_notMem_tsupport fun hz => by
          have hzV := hf.2.2 hz
          simpa [hVe] using hzV
      subst f
      rw [gradFeat_zero hDN]
      simp
  have hL := ((cmIso hh V).toContinuousLinearMap).integral_comp_comm hi
  simp only [LinearIsometry.coe_toContinuousLinearMap, map_smul] at hL
  rw [extVec, ← key, ← hL]
  rfl

/-- Stochastic Fubini recovers every smooth-test zero-extension pairing. -/
theorem ae_integral_d12_mul_Y_general (hh : IsWholePlaneGFF h P)
    (hV : ZBAdmissible V) {Y : ℂ → Ω → ℝ}
    (hYc : ∀ ω, Continuous fun x => Y x ω)
    (hYm : ∀ x, Measurable (Y x))
    (hY : ∀ x, (fun ω => Y x ω) =ᵐ[P] rectVec hh V x)
    (φ : TestC) :
    (fun ω => ∫ x, d12 φ x * Y x ω) =ᵐ[P]
      extVec hh V ((V : Set ℂ).indicator φ) := by
  have hYL2 : ∀ x, MemLp (Y x) 2 P := fun x => (Lp.memLp _).ae_eq (hY x).symm
  have hsq : ∀ x, ∫ ω, Y x ω ^ 2 ∂P = ‖rectVec hh V x‖ ^ 2 := fun x => by
    have := integral_mul_eq_inner (rectVec hh V x) (hY x) (hYL2 x)
    rw [MemLp.toLp_congr (hYL2 x) (Lp.memLp _) (hY x), Lp.toLp_coeFn,
      real_inner_self_eq_norm_sq] at this
    rw [← this]
    congr 1
    funext ω
    ring
  have hYb : ∀ L : ℝ, ∃ Ck, ∀ x : ℂ, ‖x‖ ≤ L →
      ∫ ω, Y x ω ^ 2 ∂P ≤ Ck := by
    intro L
    by_cases hne : (V : Set ℂ).Nonempty
    · obtain ⟨C, hC, hbound⟩ := sq_norm_rectVec_sub_le_general hh hV hne L
      refine ⟨C * L, fun x hx => ?_⟩
      have hL : 0 ≤ L := (norm_nonneg _).trans hx
      have hb := hbound x 0
        ((Complex.abs_re_le_norm x).trans hx)
        ((Complex.abs_im_le_norm x).trans hx)
        (by simpa using hL) (by simpa using hL)
      rw [rectVec_zero, sub_zero, sub_zero] at hb
      rw [hsq]
      exact hb.trans (mul_le_mul_of_nonneg_left hx hC)
    · have hVe : (V : Set ℂ) = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      have hzero : ∀ x, rectVec hh V x = 0 := by
        intro x
        have hρ : rectDens V x = 0 := by funext z; simp [rectDens, hVe]
        simp only [rectVec, hρ, extVec, rieszFun_zero]
        convert (cmIso hh V).map_zero using 1
        exact Subtype.ext rfl
      exact ⟨0, fun x _ => by rw [hsq, hzero x]; simp⟩
  let u := extVec hh V ((V : Set ℂ).indicator φ)
  let A : Ω → ℝ := fun ω => ∫ x, d12 φ x * Y x ω
  have hAL : MemLp A 2 P := memLp_A_gen hYc hYm hYL2 hYb φ
  have hAZ : ∀ {Z : Ω → ℝ} (hZ : MemLp Z 2 P),
      ∫ ω, A ω * Z ω ∂P = ∫ ω, u ω * Z ω ∂P := by
    intro Z hZ
    rw [integral_A_mul_gen hYc hYm hYL2 hYb φ hZ,
      integral_mul_eq_inner u EventuallyEq.rfl hZ]
    have e : ∀ x, ∫ ω, Y x ω * Z ω ∂P =
        ⟪rectVec hh V x, hZ.toLp Z⟫ := fun x =>
      integral_mul_eq_inner _ (hY x) hZ
    simp_rw [e]
    have hi : Integrable fun x => d12 φ x • rectVec hh V x :=
      ((d12 φ).continuous.smul (continuous_rectVec_general hh hV)).integrable_of_hasCompactSupport
        (d12 φ).hasCompactSupport.smul_right
    rw [show u = ∫ x, d12 φ x • rectVec hh V x from
      (integral_d12_smul_rectVec_general hh hV φ).symm,
      real_inner_comm, ← integral_inner hi]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [real_inner_smul_right]
    rw [real_inner_comm]
  have hD : MemLp (fun ω => A ω - u ω) 2 P := hAL.sub (Lp.memLp u)
  have h0 : ∫ ω, (A ω - u ω) ^ 2 ∂P = 0 := by
    have e : ∀ ω, (A ω - u ω) ^ 2 =
        A ω * (A ω - u ω) - u ω * (A ω - u ω) := fun ω => by ring
    simp_rw [e]
    have i1 : Integrable (fun ω => A ω * (A ω - u ω)) P := hAL.integrable_mul hD
    have i2 : Integrable (fun ω => u ω * (A ω - u ω)) P := (Lp.memLp u).integrable_mul hD
    rw [integral_sub i1 i2, hAZ hD, sub_self]
  have h1 := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg (A ω - u ω))
    hD.integrable_sq).mp h0
  filter_upwards [h1] with ω hω
  have : (A ω - u ω) ^ 2 = 0 := hω
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  linarith

/-- The canonical zero extension is a measurable distribution for every admissible domain. -/
theorem exists_dist_version_zbExt_general (hh : IsWholePlaneGFF h P)
    (hV : ZBAdmissible V) :
    ∃ hz : Ω → DistC, Measurable hz ∧
      (∀ φ : TestC, (fun ω => hz ω φ) =ᵐ[P] zbExt hh V φ) ∧
      ∀ ω, restrictTo
        (toOpens (closure (V : Set ℂ))ᶜ isClosed_closure.isOpen_compl)
        (hz ω) = 0 := by
  obtain ⟨Y, hYc, hYm, hY⟩ := exists_continuous_rectVec_general hh hV
  let hz : Ω → DistC := LQGMetric.GFFExist.gffOf Y hYc
  have hm : Measurable hz := LQGMetric.GFFExist.measurable_gffOf Y hYc hYm
  have hv : ∀ φ : TestC, (fun ω => hz ω φ) =ᵐ[P] zbExt hh V φ := by
    intro φ
    filter_upwards [ae_integral_d12_mul_Y_general hh hV hYc hYm hY φ,
      (zbExt_ae hh V φ).symm] with ω h1 h2
    rw [LQGMetric.GFFExist.gffOf_apply, h1]
    exact h2
  exact LQGMetric.MarkovVer.exists_vanishing_version_zbExt hh hm hv

end SupercriticalConformalCovariance.Markov
