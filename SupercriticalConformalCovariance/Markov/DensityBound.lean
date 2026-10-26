import SupercriticalConformalCovariance.Markov.AnchoredProcess
import LQGMetric.Field.ExistKernelL2

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric TopologicalSpace
open scoped RealInnerProductSpace

namespace SupercriticalConformalCovariance.Markov

open LQGMetric LQGMetric.GFFExist LQGMetric.MarkovZB LQGMetric.MarkovGermVer
  QuantumZipper QuantumZipper.K3

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistC} {V : Opens ℂ}

/-- Real Cauchy–Schwarz in the form needed for compactly supported densities. -/
theorem integral_mul_sq_le {a b : ℂ → ℝ} (ha : MemLp a 2 (volume : Measure ℂ))
    (hb : MemLp b 2 (volume : Measure ℂ)) :
    (∫ x, a x * b x) ^ 2 ≤ (∫ x, a x ^ 2) * (∫ x, b x ^ 2) := by
  let A : Lp ℝ 2 (volume : Measure ℂ) := ha.toLp a
  let B : Lp ℝ 2 (volume : Measure ℂ) := hb.toLp b
  have hab : ⟪A, B⟫ = ∫ x, a x * b x := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with x hax hbx
    rw [hax, hbx]
    simp [mul_comm]
  have haa : ‖A‖ ^ 2 = ∫ x, a x ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [ha.coeFn_toLp] with x hax
    rw [hax, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
  have hbb : ‖B‖ ^ 2 = ∫ x, b x ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hb.coeFn_toLp] with x hbx
    rw [hbx, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
  rw [← hab, ← haa, ← hbb]
  have hcs := real_inner_mul_inner_self_le A B
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hcs
  simpa only [pow_two] using hcs

lemma memLp_two_of_continuous_compact {g : ℂ → ℝ}
    (hg : Continuous g) (hgs : HasCompactSupport g) :
    MemLp g 2 (volume : Measure ℂ) := by
  rw [memLp_two_iff_integrable_sq hg.measurable.aestronglyMeasurable]
  exact ((hg.mul hg).integrable_of_hasCompactSupport hgs.mul_right).congr
    (Eventually.of_forall fun x => by simp [Pi.mul_apply, pow_two])

/-- The general Schur estimate controls local oscillation by the `V` Dirichlet energy. -/
theorem sq_dev_le_dirichlet (hh : IsWholePlaneGFF h P) {R : ℝ} (hR : 0 ≤ R)
    {ζ : ℂ → ℝ} (hζs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ζ)
    (hζ01 : ∀ x, 0 ≤ ζ x ∧ ζ x ≤ 1)
    (hζR : ∀ x, R < ‖x‖ → ζ x = 0)
    {f : ℂ → ℝ} (hf : f ∈ zeroSpace V) :
    ∫ x, (ζ x * (f x - LQGMetric.MarkovGermVer.zmean ζ f)) ^ 2 ≤
      schurLR R * dirichletEnergyOn V f := by
  let g : zsSub ⊤ := ⟨f, hf.1, hf.2.1, subset_univ _⟩
  have h := sq_dev_le_schur_general hh hR hζs hζ01 hζR g
  have hn : ‖cmLin hh ⊤ g‖ ^ 2 = dirichletEnergyOn V f := by
    rw [norm_cmLin hh ⊤]
    change ‖gradFeat (⊤ : Opens ℂ) f‖ ^ 2 = _
    rw [norm_gradFeat_sq (D := (↑(⊤ : Opens ℂ) : Set ℂ))
      ((isDNSpace_zeroSpace _).smooth f g.2)
      ((isDNSpace_zeroSpace _).energy f g.2),
      ← gradEnergy_eq_dirichletEnergyOn ⊤ g.2,
      gradEnergy_eq_dirichletEnergyOn V hf]
  simpa only [g, hn] using h

set_option maxHeartbeats 1000000 in
/-- The interior unit-mass test controls the otherwise free local constant. -/
theorem zmean_sq_le_dirichlet (hh : IsWholePlaneGFF h P)
    (hV : ZBAdmissible V)
    (hpos : ∃ g ∈ zeroSpace V, 0 < dirichletEnergyOn V g)
    (β : TestOn V) (hβ : ∫ x, β x = 1)
    {R : ℝ} (hR : 0 ≤ R) {ζ : ℂ → ℝ}
    (hζs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ζ)
    (hζ01 : ∀ x, 0 ≤ ζ x ∧ ζ x ≤ 1)
    (hζR : ∀ x, R < ‖x‖ → ζ x = 0)
    (hζβ : ∀ x ∈ tsupport β, ζ x = 1)
    {f : ℂ → ℝ} (hf : f ∈ zeroSpace V) :
    (zmean ζ f) ^ 2 ≤
      (2 * (∫ x, β x ^ 2) * schurLR R + 2 * ‖zbRiesz V β‖ ^ 2) *
        dirichletEnergyOn V f := by
  let c := zmean ζ f
  let F : ℂ → ℝ := fun x => ζ x * (f x - c)
  let X : ℝ := ∫ x, F x ^ 2
  let B : ℝ := ∫ x, β x ^ 2
  let d : ℝ := ∫ x, β x * F x
  let b : ℝ := ∫ x, β x * f x
  let E : ℝ := dirichletEnergyOn V f
  have hζc : HasCompactSupport ζ := hasCompactSupport_of_ball hR hζR
  have hFcont : Continuous F := hζs.continuous.mul (hf.1.continuous.sub continuous_const)
  have hFc : HasCompactSupport F := hζc.mul_right
  have hF2 : MemLp F 2 (volume : Measure ℂ) := memLp_two_of_continuous_compact hFcont hFc
  have hβ2 : MemLp (β : ℂ → ℝ) 2 (volume : Measure ℂ) :=
    memLp_two_of_continuous_compact β.continuous β.hasCompactSupport
  have hdcs : d ^ 2 ≤ B * X := integral_mul_sq_le hβ2 hF2
  have hX : X ≤ schurLR R * E := sq_dev_le_dirichlet hh hR hζs hζ01 hζR hf
  have hB0 : 0 ≤ B := integral_nonneg fun x => sq_nonneg _
  have hE0 : 0 ≤ E := energy_nonneg V f
  have hbE : b ^ 2 ≤ ‖zbRiesz V β‖ ^ 2 * E := by
    have hp := inner_zbRiesz_gradFeat hV hpos β hf
    have hcs := inner_sq_le (zbRiesz V β) (gradFeat V f)
    rw [hp, norm_gradFeat_sq ((isDNSpace_zeroSpace _).smooth f hf)
      ((isDNSpace_zeroSpace _).energy f hf)] at hcs
    have heq : b = ∫ x, f x * β x :=
      integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
    simpa only [b, E, ← heq] using hcs
  have hβi : Integrable (β : ℂ → ℝ) :=
    β.continuous.integrable_of_hasCompactSupport β.hasCompactSupport
  have hβfi : Integrable (fun x => β x * f x) :=
    (β.continuous.mul hf.1.continuous).integrable_of_hasCompactSupport
      β.hasCompactSupport.mul_right
  have hβF : ∀ x, β x * F x = β x * f x - c * β x := by
    intro x
    by_cases hx : x ∈ tsupport β
    · dsimp [F]
      rw [hζβ x hx]
      ring
    · have hb0 := image_eq_zero_of_notMem_tsupport hx
      simp [hb0]
  have hdb : d = b - c := by
    have e : (fun x => β x * F x) = fun x => β x * f x - c * β x := funext hβF
    change (∫ x, β x * F x) = b - c
    rw [e, integral_sub hβfi (hβi.const_mul c), integral_const_mul, hβ]
    change b - c * 1 = b - c
    ring
  have hdB : d ^ 2 ≤ B * schurLR R * E := by
    calc d ^ 2 ≤ B * X := hdcs
      _ ≤ B * (schurLR R * E) := mul_le_mul_of_nonneg_left hX hB0
      _ = B * schurLR R * E := by ring
  have hcbd : c ^ 2 ≤ 2 * d ^ 2 + 2 * b ^ 2 := by
    rw [hdb]
    nlinarith [sq_nonneg (2 * b - c)]
  calc
    c ^ 2 ≤ 2 * d ^ 2 + 2 * b ^ 2 := hcbd
    _ ≤ 2 * (B * schurLR R * E) + 2 * (‖zbRiesz V β‖ ^ 2 * E) := by
      gcongr
    _ = (2 * B * schurLR R + 2 * ‖zbRiesz V β‖ ^ 2) * E := by ring

set_option maxHeartbeats 1000000 in
/-- Any bounded compact density supported where the cutoff is one has finite dual energy. -/
theorem integral_density_sq_le_dirichlet (hh : IsWholePlaneGFF h P)
    (hV : ZBAdmissible V)
    (hpos : ∃ g ∈ zeroSpace V, 0 < dirichletEnergyOn V g)
    (β : TestOn V) (hβ : ∫ x, β x = 1)
    {R : ℝ} (hR : 0 ≤ R) {ζ : ℂ → ℝ}
    (hζs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ζ)
    (hζ01 : ∀ x, 0 ≤ ζ x ∧ ζ x ≤ 1)
    (hζR : ∀ x, R < ‖x‖ → ζ x = 0)
    (hζβ : ∀ x ∈ tsupport β, ζ x = 1)
    {ρ : ℂ → ℝ} {M Rρ : ℝ} (hρ : BddSupp ρ M Rρ)
    (hζρ : ∀ x, ρ x ≠ 0 → ζ x = 1)
    {f : ℂ → ℝ} (hf : f ∈ zeroSpace V) :
    (∫ x, ρ x * f x) ^ 2 ≤
      (2 * (∫ x, ρ x ^ 2) * schurLR R +
        2 * (2 * (∫ x, β x ^ 2) * schurLR R + 2 * ‖zbRiesz V β‖ ^ 2) *
          (∫ x, ρ x) ^ 2) * dirichletEnergyOn V f := by
  let c := zmean ζ f
  let F : ℂ → ℝ := fun x => ζ x * (f x - c)
  let X : ℝ := ∫ x, F x ^ 2
  let E : ℝ := dirichletEnergyOn V f
  let D : ℝ := ∫ x, ρ x * F x
  let A : ℝ := ∫ x, ρ x
  let B : ℝ := ∫ x, ρ x ^ 2
  let C : ℝ := 2 * (∫ x, β x ^ 2) * schurLR R + 2 * ‖zbRiesz V β‖ ^ 2
  have hζc : HasCompactSupport ζ := hasCompactSupport_of_ball hR hζR
  have hFcont : Continuous F := hζs.continuous.mul (hf.1.continuous.sub continuous_const)
  have hFc : HasCompactSupport F := hζc.mul_right
  have hF2 : MemLp F 2 (volume : Measure ℂ) := memLp_two_of_continuous_compact hFcont hFc
  have hρ2i : Integrable (fun x => ρ x ^ 2) := by
    have hi := hρ.integrable_mul_bdd (f := ρ) hρ.meas (K := M)
      (fun x _ => hρ.bdd x)
    exact hi.congr (Eventually.of_forall fun x => by simp [pow_two])
  have hρ2 : MemLp ρ 2 (volume : Measure ℂ) := by
    rw [memLp_two_iff_integrable_sq hρ.meas.aestronglyMeasurable]
    exact hρ2i
  have hf2 : MemLp f 2 (volume : Measure ℂ) :=
    memLp_two_of_continuous_compact hf.1.continuous hf.2.1
  have hDF : Integrable (fun x => ρ x * F x) := hρ2.integrable_mul hF2
  have hρfi : Integrable (fun x => ρ x * f x) := hρ2.integrable_mul hf2
  have hρi : Integrable ρ := hρ.integrable
  have hDcs : D ^ 2 ≤ B * X := integral_mul_sq_le hρ2 hF2
  have hX : X ≤ schurLR R * E := sq_dev_le_dirichlet hh hR hζs hζ01 hζR hf
  have hc : c ^ 2 ≤ C * E :=
    zmean_sq_le_dirichlet hh hV hpos β hβ hR hζs hζ01 hζR hζβ hf
  have hB0 : 0 ≤ B := integral_nonneg fun x => sq_nonneg _
  have hA20 : 0 ≤ A ^ 2 := sq_nonneg _
  have hρF : ∀ x, ρ x * F x = ρ x * f x - c * ρ x := by
    intro x
    by_cases hx : ρ x = 0
    · simp [hx]
    · dsimp [F]
      rw [hζρ x hx]
      ring
  have hρf : (∫ x, ρ x * f x) = D + c * A := by
    have e : (fun x => ρ x * F x) = fun x => ρ x * f x - c * ρ x := funext hρF
    have hD : D = (∫ x, ρ x * f x) - c * A := by
      change (∫ x, ρ x * F x) = _
      rw [e, integral_sub hρfi (hρi.const_mul c), integral_const_mul]
    linarith
  have hDA : D ^ 2 ≤ B * schurLR R * E := by
    calc D ^ 2 ≤ B * X := hDcs
      _ ≤ B * (schurLR R * E) := mul_le_mul_of_nonneg_left hX hB0
      _ = B * schurLR R * E := by ring
  rw [hρf]
  have hsq : (D + c * A) ^ 2 ≤ 2 * D ^ 2 + 2 * (c ^ 2 * A ^ 2) := by
    nlinarith [sq_nonneg (D - c * A)]
  calc
    (D + c * A) ^ 2 ≤ 2 * D ^ 2 + 2 * (c ^ 2 * A ^ 2) := hsq
    _ ≤ 2 * (B * schurLR R * E) + 2 * ((C * E) * A ^ 2) := by gcongr
    _ = (2 * B * schurLR R + 2 * C * A ^ 2) * E := by ring

/-- The new arbitrary-domain finite-dual-energy estimate for bounded compact densities. -/
theorem dualNormSq_bddSupp_pos_lt_top (hh : IsWholePlaneGFF h P)
    (hV : ZBAdmissible V)
    (hpos : ∃ g ∈ zeroSpace V, 0 < dirichletEnergyOn V g)
    (β : TestOn V) (hβ : ∫ x, β x = 1)
    {ρ : ℂ → ℝ} {M Rρ : ℝ} (hρ : BddSupp ρ M Rρ)
    (hρnonneg : ∀ x, 0 ≤ ρ x) :
    dualNormSq V (zeroSpace V) (testMeasPos ρ) < ⊤ := by
  let K : Set ℂ := closedBall 0 Rρ ∪ tsupport β
  have hK : IsCompact K := (isCompact_closedBall 0 Rρ).union β.hasCompactSupport.isCompact
  obtain ⟨R, ζ, hR, hζs, hζ01, hζR, hζK⟩ := exists_global_cutoff K hK
  have hζβ : ∀ x ∈ tsupport β, ζ x = 1 :=
    fun x hx => hζK x (Or.inr hx)
  have hζρ : ∀ x, ρ x ≠ 0 → ζ x = 1 := by
    intro x hx
    apply hζK x (Or.inl ?_)
    rw [mem_closedBall, dist_zero_right]
    exact le_of_not_gt fun h => hx (hρ.supp x h)
  let C : ℝ := 2 * (∫ x, ρ x ^ 2) * schurLR R +
    2 * (2 * (∫ x, β x ^ 2) * schurLR R + 2 * ‖zbRiesz V β‖ ^ 2) *
      (∫ x, ρ x) ^ 2
  have hbound : ∀ f ∈ zeroSpace V,
      (∫ x, f x ∂testMeasPos ρ) ^ 2 ≤ C * dirichletEnergyOn V f := by
    intro f hf
    have h := integral_density_sq_le_dirichlet hh hV hpos β hβ hR hζs
      hζ01 hζR hζβ hρ hζρ hf
    rw [integral_testMeasPos_K3 hρ.meas]
    have he : (∫ x, max (ρ x) 0 * f x) = ∫ x, ρ x * f x := by
      congr 1
      funext x
      rw [max_eq_left (hρnonneg x)]
    rwa [he]
  unfold dualNormSq
  refine lt_of_le_of_lt (b := ENNReal.ofReal C) ?_ ENNReal.ofReal_lt_top
  refine iSup₂_le fun f hf => ENNReal.ofReal_le_ofReal ?_
  exact (div_le_iff₀ hf.2).2 (hbound f hf.1)

/-- Positive bounded compact densities supported in `V` are admissible on any
`ZBAdmissible V`, without a circle in the complement. -/
theorem isAdmissibleDual_bddSupp_pos (hh : IsWholePlaneGFF h P)
    (hV : ZBAdmissible V)
    (hpos : ∃ g ∈ zeroSpace V, 0 < dirichletEnergyOn V g)
    (β : TestOn V) (hβ : ∫ x, β x = 1)
    {ρ : ℂ → ℝ} {M Rρ : ℝ} (hρ : BddSupp ρ M Rρ)
    (hρnonneg : ∀ x, 0 ≤ ρ x) (hρ0 : ∀ x ∉ (V : Set ℂ), ρ x = 0) :
    IsAdmissibleDual V (zeroSpace V) (testMeasPos ρ) := by
  have hbd : BddDens (fun x => ENNReal.ofReal (ρ x)) (ENNReal.ofReal M) Rρ :=
    { meas := ENNReal.measurable_ofReal.comp hρ.meas
      lt_top := ENNReal.ofReal_lt_top
      le := fun x => ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hρ.bdd x))
      zero := fun x hx => by
        have hr : Rρ < ‖x‖ := by simpa using hx
        rw [hρ.supp x hr, ENNReal.ofReal_zero] }
  have hfin : IsFiniteMeasure (testMeasPos ρ) :=
    isFiniteMeasure_withDensity_bdd hbd.lt_top hbd.le hbd.zero
  refine ⟨hfin, ⟨closure (V : Set ℂ) ∩ closedBall 0 Rρ,
    (isCompact_closedBall 0 Rρ).inter_left isClosed_closure, inter_subset_left, ?_⟩,
    dualNormSq_bddSupp_pos_lt_top hh hV hpos β hβ hρ hρnonneg⟩
  apply withDensity_compl_null (isClosed_closure.inter isClosed_closedBall).measurableSet
  intro x hx
  by_cases hxV : x ∈ (V : Set ℂ)
  · have hr : Rρ < ‖x‖ := by
      have hn : x ∉ closedBall (0 : ℂ) Rρ := fun h => hx ⟨subset_closure hxV, h⟩
      simpa using hn
    rw [hρ.supp x hr, ENNReal.ofReal_zero]
  · rw [hρ0 x hxV, ENNReal.ofReal_zero]

lemma bddSupp_posPart {ρ : ℂ → ℝ} {M R : ℝ} (hρ : BddSupp ρ M R) :
    BddSupp (fun x => max (ρ x) 0) M R := by
  refine ⟨hρ.meas.max measurable_const, fun x => ?_, fun x hx => ?_⟩
  · rw [abs_of_nonneg (le_max_right _ _)]
    exact max_le ((le_abs_self _).trans (hρ.bdd x)) (by
      have := hρ.bdd x
      linarith [abs_nonneg (ρ x)])
  · rw [hρ.supp x hx, max_self]

lemma bddSupp_negPart {ρ : ℂ → ℝ} {M R : ℝ} (hρ : BddSupp ρ M R) :
    BddSupp (fun x => max (-ρ x) 0) M R :=
  bddSupp_posPart ⟨hρ.meas.neg, fun x => by simpa only [abs_neg] using hρ.bdd x,
    fun x hx => by rw [hρ.supp x hx, neg_zero]⟩

lemma testMeasPos_eq_posPart (ρ : ℂ → ℝ) :
    testMeasPos ρ = testMeasPos (fun x => max (ρ x) 0) := by
  unfold testMeasPos
  congr 1
  funext x
  change ENNReal.ofReal (ρ x) = ENNReal.ofReal (max (ρ x) 0)
  rcases le_total 0 (ρ x) with hx | hx
  · rw [max_eq_left hx]
  · rw [max_eq_right hx, ENNReal.ofReal_eq_zero.2 hx, ENNReal.ofReal_zero]

lemma testMeasNeg_eq_negPart (ρ : ℂ → ℝ) :
    testMeasNeg ρ = testMeasPos (fun x => max (-ρ x) 0) := by
  rw [show testMeasNeg ρ = testMeasPos (-ρ) from rfl, testMeasPos_eq_posPart]
  rfl

/-- Both positive and negative measures of every bounded compact density supported in `V`
are admissible, with no restriction on the shape or boundedness of `V`. -/
theorem admissible_bddSupp (hh : IsWholePlaneGFF h P)
    (hV : ZBAdmissible V)
    (hpos : ∃ g ∈ zeroSpace V, 0 < dirichletEnergyOn V g)
    (β : TestOn V) (hβ : ∫ x, β x = 1)
    {ρ : ℂ → ℝ} {M R : ℝ} (hρ : BddSupp ρ M R)
    (hρ0 : ∀ x ∉ (V : Set ℂ), ρ x = 0) :
    IsAdmissibleDual V (zeroSpace V) (testMeasPos ρ) ∧
      IsAdmissibleDual V (zeroSpace V) (testMeasNeg ρ) := by
  rw [testMeasPos_eq_posPart, testMeasNeg_eq_negPart]
  constructor
  · exact isAdmissibleDual_bddSupp_pos hh hV hpos β hβ (bddSupp_posPart hρ)
      (fun x => le_max_right _ _) (fun x hx => by rw [hρ0 x hx, max_self])
  · exact isAdmissibleDual_bddSupp_pos hh hV hpos β hβ (bddSupp_negPart hρ)
      (fun x => le_max_right _ _) (fun x hx => by rw [hρ0 x hx, neg_zero, max_self])

/-- **New arbitrary-domain extension lemma.** Boundary-touching restrictions of all smooth
whole-plane tests have finite positive and negative Dirichlet dual energy on nonempty `V`. -/
theorem admissible_indicator_test_of_nonempty (hh : IsWholePlaneGFF h P)
    (hV : ZBAdmissible V) (hne : (V : Set ℂ).Nonempty) (φ : TestC) :
    IsAdmissibleDual V (zeroSpace V)
      (testMeasPos ((V : Set ℂ).indicator φ)) ∧
    IsAdmissibleDual V (zeroSpace V)
      (testMeasNeg ((V : Set ℂ).indicator φ)) := by
  obtain ⟨β, hβV, hβ1⟩ := LQGMetric.HarmLoc.exists_unit_test V.isOpen hne
  let βV : TestOn V := ⟨β, β.contDiff, β.hasCompactSupport, hβV⟩
  have hβ1' : ∫ x, βV x = 1 := hβ1
  obtain ⟨hm, ⟨C, hC⟩, h0⟩ := (extZeroTest V φ).2
  obtain ⟨R, hR⟩ := LQGMetric.MarkovAdm.exists_closedBall_of_test φ
  have hρ : BddSupp ((V : Set ℂ).indicator φ) C R :=
    ⟨hm, hC, fun z hz => by
      by_cases hzV : z ∈ (V : Set ℂ)
      · rw [indicator_of_mem hzV]
        exact hR z (by simpa using hz)
      · exact indicator_of_notMem hzV _⟩
  exact admissible_bddSupp hh hV
    (exists_pos_energy_zeroSpace_m7d V.isOpen hne) βV hβ1' hρ h0

lemma isAdmissibleDual_zero_measure (V : Opens ℂ) :
    IsAdmissibleDual V (zeroSpace V) (0 : Measure ℂ) := by
  refine ⟨inferInstance, ⟨∅, isCompact_empty, empty_subset _, by simp⟩, ?_⟩
  have he : dualNormSq V (zeroSpace V) (0 : Measure ℂ) = 0 := by
    rw [dualNormSq_eq_of_pairing (isDNSpace_zeroSpace (V : Set ℂ))
      (v := (0 : GradSpace V)) (by simp) (fun f hf => by simp)]
    simp
  rw [he]
  exact ENNReal.zero_lt_top

/-- Boundary-touching restrictions are admissible for every `ZBAdmissible` domain, including
the empty domain. This removes the normalization-circle hypothesis of the library lemma. -/
theorem admissible_indicator_test (hh : IsWholePlaneGFF h P)
    (hV : ZBAdmissible V) (φ : TestC) :
    IsAdmissibleDual V (zeroSpace V)
      (testMeasPos ((V : Set ℂ).indicator φ)) ∧
    IsAdmissibleDual V (zeroSpace V)
      (testMeasNeg ((V : Set ℂ).indicator φ)) := by
  by_cases hne : (V : Set ℂ).Nonempty
  · exact admissible_indicator_test_of_nonempty hh hV hne φ
  · have hVe : (V : Set ℂ) = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    have hρ : (V : Set ℂ).indicator (φ : ℂ → ℝ) = 0 := by
      rw [hVe]
      exact Set.indicator_empty _
    rw [hρ]
    have hp : testMeasPos (0 : ℂ → ℝ) = 0 := by simp [testMeasPos]
    have hn : testMeasNeg (0 : ℂ → ℝ) = 0 := by simp [testMeasNeg]
    rw [hp, hn]
    exact ⟨isAdmissibleDual_zero_measure V, isAdmissibleDual_zero_measure V⟩

end SupercriticalConformalCovariance.Markov
