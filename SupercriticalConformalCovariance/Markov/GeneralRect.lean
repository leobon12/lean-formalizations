import SupercriticalConformalCovariance.Markov.DensityRiesz
import LQGMetric.Field.MarkovVer2Rect

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric TopologicalSpace
open scoped ENNReal RealInnerProductSpace

namespace SupercriticalConformalCovariance.Markov

open LQGMetric LQGMetric.GFFExist LQGMetric.MarkovZB LQGMetric.MarkovExt
  LQGMetric.MarkovVer2 QuantumZipper QuantumZipper.K3

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {h : Ω → DistC} {V : Opens ℂ}

lemma rectBdd (V : Opens ℂ) {x : ℂ} {T : ℝ}
    (hx : |x.re| + |x.im| < T) :
    BddSupp (rectDens V x) 1 T := by
  have h := isBddDensOn_rectDens V hx
  refine ⟨h.meas, ?_, ?_⟩
  · intro z
    unfold rectDens
    by_cases hz : z ∈ (V : Set ℂ)
    · rw [indicator_of_mem hz]; exact (rectInd_bddSupp x).bdd z
    · rw [indicator_of_notMem hz, abs_zero]; norm_num
  · intro z hz
    exact h.ball z (by simpa [mem_ball, dist_zero_right] using not_lt.mpr (le_of_lt hz))

lemma rectZero (V : Opens ℂ) (x : ℂ) :
    ∀ z ∉ (V : Set ℂ), rectDens V x z = 0 :=
  fun z hz => indicator_of_notMem hz _

private lemma rectVec_sub_general (hh : IsWholePlaneGFF h P)
    (hV : ZBAdmissible V)
    (hpos : ∃ g ∈ zeroSpace V, 0 < dirichletEnergyOn V g)
    (β : TestOn V) (hβ : ∫ x, β x = 1)
    {x x' : ℂ} {T : ℝ}
    (hx : |x.re| + |x.im| < T) (hx' : |x'.re| + |x'.im| < T) :
    ‖rectVec hh V x - rectVec hh V x'‖ =
      ‖rieszFun V (rectDens V x - rectDens V x')‖ := by
  rw [rieszFun_sub_bddSupp hh hV hpos β hβ
      (rectBdd V hx) (rectBdd V hx') (rectZero V x) (rectZero V x'),
    rectVec, rectVec, extVec, extVec, ← map_sub, LinearIsometry.norm_map]
  rfl

private theorem rect_sq_integral_bound {x x' : ℂ} {A : ℝ}
    (h0 : |x.re| ≤ A) (h1 : |x.im| ≤ A)
    (h2 : |x'.re| ≤ A) (h3 : |x'.im| ≤ A)
    (V : Opens ℂ) :
    ∫ u, (rectDens V x - rectDens V x') u ^ 2 ≤
      2 * (4 * A * ‖x - x'‖) := by
  have hpt : ∀ u, (rectDens V x - rectDens V x') u ^ 2 ≤
      2 * |rectInd x u - rectInd x' u| := by
    intro u
    have hb : |rectInd x u - rectInd x' u| ≤ 2 := (abs_sub _ _).trans (by
      linarith [(rectInd_bddSupp x).bdd u, (rectInd_bddSupp x').bdd u])
    simp only [Pi.sub_apply, rectDens]
    by_cases hu : u ∈ (V : Set ℂ)
    · rw [indicator_of_mem hu, indicator_of_mem hu, ← sq_abs]
      nlinarith [abs_nonneg (rectInd x u - rectInd x' u)]
    · rw [indicator_of_notMem hu, indicator_of_notMem hu]
      simp only [sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      positivity
  have hint : Integrable fun u => |rectInd x u - rectInd x' u| :=
    (((rectInd_bddSupp x).integrable.sub (rectInd_bddSupp x').integrable)).abs
  have hm : Measurable fun u => (rectDens V x - rectDens V x') u ^ 2 :=
    (((measurable_rectInd x).indicator V.isOpen.measurableSet).sub
      ((measurable_rectInd x').indicator V.isOpen.measurableSet)).pow_const 2
  have hi2 : Integrable fun u => (rectDens V x - rectDens V x') u ^ 2 :=
    (hint.const_mul 2).mono' hm.aestronglyMeasurable (Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hpt u)
  calc
    ∫ u, (rectDens V x - rectDens V x') u ^ 2 ≤
        ∫ u, 2 * |rectInd x u - rectInd x' u| :=
      integral_mono hi2 (hint.const_mul 2) hpt
    _ = 2 * ∫ u, |rectInd x u - rectInd x' u| := integral_const_mul _ _
    _ ≤ _ := by gcongr; exact integral_abs_rectInd_sub_le h1 h2

/-- Uniform rectangle increment estimate on any nonempty admissible domain. -/
theorem sq_norm_rectVec_sub_le_general (hh : IsWholePlaneGFF h P)
    (hV : ZBAdmissible V)
    (hne : (V : Set ℂ).Nonempty)
    (A : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x x' : ℂ, |x.re| ≤ A → |x.im| ≤ A → |x'.re| ≤ A →
        |x'.im| ≤ A →
        ‖rectVec hh V x - rectVec hh V x'‖ ^ 2 ≤ C * ‖x - x'‖ := by
  obtain ⟨β₀, hβV, hβ1⟩ := LQGMetric.HarmLoc.exists_unit_test V.isOpen hne
  let β : TestOn V := ⟨β₀, β₀.contDiff, β₀.hasCompactSupport, hβV⟩
  have hβ : ∫ z, β z = 1 := hβ1
  let T := 2 * |A| + 1
  let K : Set ℂ := closedBall 0 T ∪ tsupport β
  have hK : IsCompact K := (isCompact_closedBall 0 T).union β.hasCompactSupport.isCompact
  obtain ⟨R, ζ, hR, hζs, hζ01, hζR, hζK⟩ := exists_global_cutoff K hK
  have hζβ : ∀ z ∈ tsupport β, ζ z = 1 := fun z hz => hζK z (Or.inr hz)
  let C₀ : ℝ := 2 * schurLR R +
    2 * (2 * (∫ z, β z ^ 2) * schurLR R + 2 * ‖zbRiesz V β‖ ^ 2) *
      (∫ z, ζ z ^ 2)
  have hC₀ : 0 ≤ C₀ := by
    have hβ2 : 0 ≤ ∫ z, β z ^ 2 := integral_nonneg fun z => sq_nonneg _
    have hζ2 : 0 ≤ ∫ z, ζ z ^ 2 := integral_nonneg fun z => sq_nonneg _
    have hs : 0 ≤ schurLR R := schurLR_nonneg hR
    dsimp [C₀]
    positivity
  refine ⟨C₀ * (2 * (4 * |A|)), mul_nonneg hC₀ (by positivity), ?_⟩
  intro x x' h0 h1 h2 h3
  have hx : |x.re| + |x.im| < T := by
    dsimp [T]
    linarith [le_abs_self A]
  have hx' : |x'.re| + |x'.im| < T := by
    dsimp [T]
    linarith [le_abs_self A]
  let ρ : ℂ → ℝ := rectDens V x - rectDens V x'
  have hρ : BddSupp ρ 2 T := by
    change BddSupp (fun z => rectDens V x z - rectDens V x' z) 2 T
    have ht := (rectBdd V hx).sub (rectBdd V hx')
    norm_num at ht
    simpa only [max_self] using ht
  have hρ0 : ∀ z ∉ (V : Set ℂ), ρ z = 0 := by
    intro z hz
    simp [ρ, rectZero V x z hz, rectZero V x' z hz]
  have hζρ : ∀ z, ρ z ≠ 0 → ζ z = 1 := by
    intro z hz
    apply hζK z (Or.inl ?_)
    rw [mem_closedBall, dist_zero_right]
    exact le_of_not_gt fun ht => hz (hρ.supp z ht)
  have hnorm : ‖rieszFun V ρ‖ ^ 2 ≤ C₀ * (∫ z, ρ z ^ 2) :=
    norm_rieszFun_sq_le_uniform hh hV
      (exists_pos_energy_zeroSpace_m7d V.isOpen hne) β hβ hR
      hζs hζ01 hζR hζβ hρ hρ0 hζρ
  have hsq := rect_sq_integral_bound
    (h0.trans (le_abs_self A)) (h1.trans (le_abs_self A))
    (h2.trans (le_abs_self A)) (h3.trans (le_abs_self A)) V
  rw [rectVec_sub_general hh hV (exists_pos_energy_zeroSpace_m7d V.isOpen hne)
      β hβ hx hx']
  calc
    ‖rieszFun V ρ‖ ^ 2 ≤ C₀ * (∫ z, ρ z ^ 2) := hnorm
    _ ≤ C₀ * (2 * (4 * |A| * ‖x - x'‖)) :=
      mul_le_mul_of_nonneg_left hsq hC₀
    _ = C₀ * (2 * (4 * |A|)) * ‖x - x'‖ := by ring

/-- A continuous rectangle antiderivative for the zero-boundary projection on every
admissible domain, with no normalization circle. -/
theorem exists_continuous_rectVec_general (hh : IsWholePlaneGFF h P)
    (hV : ZBAdmissible V) :
    ∃ Y : ℂ → Ω → ℝ, (∀ ω, Continuous fun x => Y x ω) ∧
      (∀ x, Measurable (Y x)) ∧
      ∀ x, (fun ω => Y x ω) =ᵐ[P] rectVec hh V x := by
  by_cases hne : (V : Set ℂ).Nonempty
  · have hv : ∀ A : ℝ, ∃ C, 0 ≤ C ∧ ∀ x x' : ℂ,
        |x.re| ≤ A → |x.im| ≤ A → |x'.re| ≤ A → |x'.im| ≤ A →
        ((‖rectVec hh V x - rectVec hh V x'‖ ^ 2).toNNReal : ℝ) ≤
          C * ‖x - x'‖ := by
      intro A
      obtain ⟨C, hC, hbound⟩ := sq_norm_rectVec_sub_le_general hh hV hne A
      refine ⟨C, hC, fun x x' h0 h1 h2 h3 => ?_⟩
      rw [Real.coe_toNNReal', max_le_iff]
      exact ⟨hbound x x' h0 h1 h2 h3, by positivity⟩
    obtain ⟨Y, hc, hm, hY⟩ := exists_continuous_modification_of_gauss
      (measurable_rectProc hh V)
      (fun x x' => (‖rectVec hh V x - rectVec hh V x'‖ ^ 2).toNNReal)
      (hasLaw_rectProc_sub hh V) hv
    exact ⟨Y, hc, hm, fun x => (hY x).trans (rectProc_ae hh V x)⟩
  · have hVe : (V : Set ℂ) = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    have hzero : ∀ x, rectVec hh V x = 0 := by
      intro x
      have hρ : rectDens V x = 0 := by
        funext z
        simp [rectDens, hVe]
      simp only [rectVec, hρ, extVec, rieszFun_zero]
      convert (cmIso hh V).map_zero using 1
      exact Subtype.ext rfl
    exact ⟨fun _ _ => 0, fun _ => continuous_const, fun _ => measurable_const,
      fun x => by
        rw [hzero x]
        exact (Lp.coeFn_zero ℝ 2 P).symm⟩

end SupercriticalConformalCovariance.Markov
