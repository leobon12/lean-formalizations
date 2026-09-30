import QuantumZipper.Proofs.LQG.BoundaryExistence
import QuantumZipper.Proofs.LQG.BoundaryVague

/-!
# M4-B3, part 2: almost sure existence of the boundary measure along `2^{-k}`

Blueprint `M4_BLUEPRINT.md`, node M4-B3 (dyadic part).

* `ae_tendsto_of_summable_integral_abs`, `integral_abs_sub_lim_le`: the Borel–Cantelli pattern
  (summable `L¹` increments give a.s. and `L¹` convergence, with the tail bound).
* `ae_bdryApprox_eq_smul`: a.s., for all `k`, `bdryApprox γ (X ω) k = e^{γ X(fc(0,R))/2} •
  bdryApprox γ (Z ω) k` (the additive constant multiplies the measures).
* `ae_isVagueLimitR_qBoundaryMeasure`: **a.s. `bdryApprox γ (X ω)` converges vaguely to
  `qBoundaryMeasure γ (X ω)`** for the free field (any additive-constant convention), and
  `ae_isVagueLimitR_qBoundaryMeasure_zField` the same for the normalized field.
* `integral_abs_bdryApprox_sub_qBoundaryMeasure_le`, `tendsto_integral_bdryApprox`: `L¹`
  convergence with rate `e^{-β k log 2}`, and `E ∫ f dν = lim E ∫ f dν_k`, for the normalized
  field `Z = zField X R` and `f ∈ C_c` supported where `|t| + 1 ≤ R`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Real Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace BdryExist

open BdryVague

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-! ### Borel–Cantelli pattern -/

theorem ae_tendsto_of_summable_integral_abs {G : ℕ → Ω → ℝ} (hG : ∀ k, Integrable (G k) P)
    (hsum : Summable (fun k => ∫ ω, |G k ω - G (k + 1) ω| ∂P)) :
    ∀ᵐ ω ∂P, Summable (fun k => |G k ω - G (k + 1) ω|) ∧
      ∃ l, Tendsto (fun k => G k ω) atTop (𝓝 l) := by
  have hDi : ∀ k, Integrable (fun ω => |G k ω - G (k + 1) ω|) P :=
    fun k => ((hG k).sub (hG (k + 1))).abs
  have hlin : ∫⁻ ω, ∑' k, ENNReal.ofReal |G k ω - G (k + 1) ω| ∂P =
      ∑' k, ENNReal.ofReal (∫ ω, |G k ω - G (k + 1) ω| ∂P) := by
    rw [lintegral_tsum (fun k => (hDi k).aemeasurable.ennreal_ofReal)]
    congr 1; funext k
    rw [ofReal_integral_eq_lintegral_ofReal (hDi k) (ae_of_all _ fun ω => abs_nonneg _)]
  have hfin : ∫⁻ ω, ∑' k, ENNReal.ofReal |G k ω - G (k + 1) ω| ∂P ≠ ∞ := by
    rw [hlin, ← ENNReal.ofReal_tsum_of_nonneg
      (fun k => integral_nonneg fun ω => abs_nonneg _) hsum]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_lt_top' (AEMeasurable.ennreal_tsum fun k =>
    (hDi k).aemeasurable.ennreal_ofReal) hfin] with ω hω
  have hs : Summable (fun k => |G k ω - G (k + 1) ω|) := by
    have := ENNReal.summable_toReal hω.ne
    simpa [ENNReal.toReal_ofReal (abs_nonneg _)] using this
  refine ⟨hs, cauchySeq_tendsto_of_complete (cauchySeq_of_summable_dist ?_)⟩
  simpa [Real.dist_eq] using hs

theorem integral_abs_sub_lim_le {G : ℕ → Ω → ℝ} (hG : ∀ k, Integrable (G k) P)
    (hsum : Summable (fun k => ∫ ω, |G k ω - G (k + 1) ω| ∂P)) {Gl : Ω → ℝ}
    (hl : ∀ᵐ ω ∂P, Tendsto (fun k => G k ω) atTop (𝓝 (Gl ω))) (k : ℕ) :
    Integrable (fun ω => G k ω - Gl ω) P ∧
      ∫ ω, |G k ω - Gl ω| ∂P ≤ ∑' m, ∫ ω, |G (k + m) ω - G (k + m + 1) ω| ∂P := by
  have hDi : ∀ k, Integrable (fun ω => |G k ω - G (k + 1) ω|) P :=
    fun k => ((hG k).sub (hG (k + 1))).abs
  have hsum' : Summable (fun m => ∫ ω, |G (k + m) ω - G (k + m + 1) ω| ∂P) := by
    have := (summable_nat_add_iff k).2 hsum
    simpa [add_comm, add_left_comm, add_assoc] using this
  have hGl : AEStronglyMeasurable Gl P :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun k => (hG k).aestronglyMeasurable) hl
  have hmeas : AEStronglyMeasurable (fun ω => G k ω - Gl ω) P :=
    (hG k).aestronglyMeasurable.sub hGl
  have hpt : ∀ᵐ ω ∂P, ENNReal.ofReal |G k ω - Gl ω| ≤
      ∑' m, ENNReal.ofReal |G (k + m) ω - G (k + m + 1) ω| := by
    filter_upwards [ae_tendsto_of_summable_integral_abs hG hsum, hl] with ω hω hlim
    have hle := dist_le_tsum_of_dist_le_of_tendsto (fun n => |G n ω - G (n + 1) ω|)
      (fun n => by rw [Real.dist_eq]) hω.1 hlim k
    rw [Real.dist_eq] at hle
    have hs' : Summable (fun m => |G (k + m) ω - G (k + m + 1) ω|) := by
      have := (summable_nat_add_iff k).2 hω.1
      simpa [add_comm, add_left_comm, add_assoc] using this
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => abs_nonneg _) hs']
    exact ENNReal.ofReal_le_ofReal (by simpa [add_assoc] using hle)
  have hlint : ∫⁻ ω, ENNReal.ofReal |G k ω - Gl ω| ∂P ≤
      ENNReal.ofReal (∑' m, ∫ ω, |G (k + m) ω - G (k + m + 1) ω| ∂P) := by
    refine (lintegral_mono_ae hpt).trans (le_of_eq ?_)
    rw [lintegral_tsum (fun m => (hDi (k + m)).aemeasurable.ennreal_ofReal),
      ENNReal.ofReal_tsum_of_nonneg (fun m => integral_nonneg fun ω => abs_nonneg _) hsum']
    congr 1; funext m
    rw [ofReal_integral_eq_lintegral_ofReal (hDi (k + m)) (ae_of_all _ fun ω => abs_nonneg _)]
  have hint : Integrable (fun ω => G k ω - Gl ω) P := by
    refine ⟨hmeas, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    simp only [Real.norm_eq_abs]
    exact hlint.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun ω => abs_nonneg _) hint.abs.1]
  refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top hlint).trans (le_of_eq ?_)
  exact ENNReal.toReal_ofReal (tsum_nonneg fun m => integral_nonneg fun ω => abs_nonneg _)

/-! ### The additive constant -/

variable {X : Ω → FieldSample}

theorem ae_bdryApprox_eq_smul (hX : IsFreeGFFModConstH X P) (γ R : ℝ) :
    ∀ᵐ ω ∂P, ∀ k, bdryApprox γ (X ω) k =
      ENNReal.ofReal (exp (γ / 2 * X ω (foldedCircle 0 R))) • bdryApprox γ (zField X R ω) k := by
  refine ae_all_iff.2 fun k => ?_
  filter_upwards [ae_avgReg_zField hX R k] with ω hω
  have e : (fun t : ℝ => ENNReal.ofReal (radius k ^ (γ ^ 2 / 4) * exp (γ / 2 * avgReg (X ω) k t)))
      = ENNReal.ofReal (exp (γ / 2 * X ω (foldedCircle 0 R))) • (fun t : ℝ =>
        ENNReal.ofReal (radius k ^ (γ ^ 2 / 4) * exp (γ / 2 * avgReg (zField X R ω) k t))) := by
    funext t
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← ENNReal.ofReal_mul (exp_pos _).le, hω (t : ℂ) (GaussTK.ofReal_mem_Hbar t)]
    congr 1
    rw [show γ / 2 * (avgReg (X ω) k t - X ω (foldedCircle 0 R)) =
      γ / 2 * avgReg (X ω) k t + -(γ / 2 * X ω (foldedCircle 0 R)) by ring, exp_add, exp_neg]
    field_simp
  unfold bdryApprox
  rw [e, withDensity_smul' _ _ ENNReal.ofReal_ne_top]

/-! ### Convergence on the countable family -/

theorem summable_of_le_geom {a : ℕ → ℝ} (ha : ∀ k, 0 ≤ a k) {γ C : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) (h : ∀ k : ℕ, a k ≤ C * exp (-bdryRate γ * (k * log 2))) : Summable a := by
  set q := exp (-bdryRate γ * log 2) with hq
  have hq1 : q < 1 := by
    rw [hq, exp_lt_one_iff]
    have := bdryRate_pos hγ hγ2
    have := log_pos one_lt_two
    nlinarith
  refine Summable.of_nonneg_of_le ha (fun k => (h k).trans (le_of_eq ?_))
    ((summable_geometric_of_lt_one (exp_pos _).le hq1).mul_left C)
  rw [← exp_nat_mul]; congr 2; ring

theorem testSet_bound (N : ℕ) : ∀ t ∈ Icc (-((N : ℝ) + 1)) ((N : ℝ) + 1),
    |t| + 1 ≤ (N : ℝ) + 2 := by
  intro t ht
  have := abs_le.2 ⟨ht.1, ht.2⟩
  linarith

theorem volume_testSet_lt_top (N : ℕ) : volume (Icc (-((N : ℝ) + 1)) ((N : ℝ) + 1)) < ∞ := by
  rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top

theorem bump_eq_zero_of_notMem {N : ℕ} {t : ℝ}
    (ht : t ∉ Icc (-((N : ℝ) + 1)) ((N : ℝ) + 1)) : bump N t = 0 := by
  apply bump_eq_zero
  simp only [mem_Icc, not_and_or, not_le] at ht
  rcases ht with h | h
  · rw [abs_of_neg (by linarith [(N.cast_nonneg : (0 : ℝ) ≤ N)])]; linarith
  · rw [abs_of_pos (by linarith [(N.cast_nonneg : (0 : ℝ) ≤ N)])]; linarith

theorem ae_tendsto_family_zField [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (N : ℕ) {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (hgS : ∀ t ∉ Icc (-((N : ℝ) + 1)) ((N : ℝ) + 1), g t = 0) :
    ∀ᵐ ω ∂P, ∃ l, Tendsto (fun k => ∫ t, g t ∂(bdryApprox γ (zField X ((N : ℝ) + 2) ω) k))
      atTop (𝓝 l) := by
  obtain ⟨M, hM⟩ := hg.bounded_above_of_compact_support hgc
  have hM' : ∀ t, |g t| ≤ M := fun t => by simpa [Real.norm_eq_abs] using hM t
  obtain ⟨C, -, hC⟩ := integral_abs_bdryApprox_step_le_rate hX hγ hγ2 measurableSet_Icc
    (volume_testSet_lt_top N) (testSet_bound N) hg.measurable hM' hgS
  have hint := integrable_integral_bdryApprox hX measurableSet_Icc (volume_testSet_lt_top N)
    (testSet_bound N) γ hg.measurable hM' hgS
  filter_upwards [ae_tendsto_of_summable_integral_abs hint
    (summable_of_le_geom (fun k => integral_nonneg fun ω => abs_nonneg _) hγ hγ2 hC)] with ω hω
  exact hω.2

theorem ae_bdryApprox_zField_Icc_lt_top [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    (γ : ℝ) (N k : ℕ) :
    ∀ᵐ ω ∂P, bdryApprox γ (zField X ((N : ℝ) + 2) ω) k
      (Icc (-((N : ℝ) + 1)) ((N : ℝ) + 1)) < ∞ := by
  filter_upwards [ae_integrableOn_bDens hX measurableSet_Icc (volume_testSet_lt_top N)
    (testSet_bound N) γ k] with ω hω
  unfold bdryApprox
  rw [withDensity_apply _ measurableSet_Icc]
  exact hω.lintegral_lt_top

/-! ### M4-B3: almost sure vague convergence -/

/-- **M4-B3 (existence along `2^{-k}`)**: for the free field, a.s. `bdryApprox γ (X ω)` has a
vague limit. -/
theorem ae_exists_isVagueLimitR [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ ω ∂P, ∃ ν, IsVagueLimitR (bdryApprox γ (X ω)) ν := by
  have h1 : ∀ᵐ ω ∂P, ∀ N : ℕ, ∀ k, bdryApprox γ (X ω) k =
      ENNReal.ofReal (exp (γ / 2 * X ω (foldedCircle 0 ((N : ℝ) + 2)))) •
        bdryApprox γ (zField X ((N : ℝ) + 2) ω) k :=
    ae_all_iff.2 fun N => ae_bdryApprox_eq_smul hX γ _
  have h2 : ∀ᵐ ω ∂P, ∀ N m : ℕ, ∃ l, Tendsto (fun k => ∫ t, testFam N m t
      ∂(bdryApprox γ (zField X ((N : ℝ) + 2) ω) k)) atTop (𝓝 l) :=
    ae_all_iff.2 fun N => ae_all_iff.2 fun m =>
      ae_tendsto_family_zField hX hγ hγ2 N (continuous_testFam N m)
        (hasCompactSupport_testFam N m)
        (fun t ht => by simp [testFam, bump_eq_zero_of_notMem ht])
  have h3 : ∀ᵐ ω ∂P, ∀ N : ℕ, ∃ l, Tendsto (fun k => ∫ t, bump N t
      ∂(bdryApprox γ (zField X ((N : ℝ) + 2) ω) k)) atTop (𝓝 l) :=
    ae_all_iff.2 fun N =>
      ae_tendsto_family_zField hX hγ hγ2 N (continuous_bump N) (hasCompactSupport_bump N)
        (fun t ht => bump_eq_zero_of_notMem ht)
  have h4 : ∀ᵐ ω ∂P, ∀ N k : ℕ, bdryApprox γ (zField X ((N : ℝ) + 2) ω) k
      (Icc (-((N : ℝ) + 1)) ((N : ℝ) + 1)) < ∞ :=
    ae_all_iff.2 fun N => ae_all_iff.2 fun k => ae_bdryApprox_zField_Icc_lt_top hX γ N k
  filter_upwards [h1, h2, h3, h4] with ω h1 h2 h3 h4
  refine exists_isVagueLimitR_of_testFam (fun k => ?_) (fun N m => ?_) (fun N => ?_)
  · refine isFiniteMeasureOnCompacts_of_Icc fun N => ?_
    rw [h1 N k, Measure.smul_apply, smul_eq_mul]
    refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      ((measure_mono (Icc_subset_Icc (by linarith) (by linarith))).trans_lt (h4 N k))
  · obtain ⟨l, hl⟩ := h2 N m
    refine ⟨(ENNReal.ofReal (exp (γ / 2 * X ω (foldedCircle 0 ((N : ℝ) + 2))))).toReal * l, ?_⟩
    simp_rw [h1 N, integral_smul_measure, smul_eq_mul]
    exact hl.const_mul _
  · obtain ⟨l, hl⟩ := h3 N
    refine ⟨(ENNReal.ofReal (exp (γ / 2 * X ω (foldedCircle 0 ((N : ℝ) + 2))))).toReal * l, ?_⟩
    simp_rw [h1 N, integral_smul_measure, smul_eq_mul]
    exact hl.const_mul _

/-- **M4-B3**: a.s. the approximating boundary measures of the free field converge vaguely to
`qBoundaryMeasure γ (X ω)`. -/
theorem ae_isVagueLimitR_qBoundaryMeasure [IsProbabilityMeasure P]
    (hX : IsFreeGFFModConstH X P) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ ω ∂P, IsVagueLimitR (bdryApprox γ (X ω)) (qBoundaryMeasure γ (X ω)) := by
  filter_upwards [ae_exists_isVagueLimitR hX hγ hγ2] with ω hω
  obtain ⟨ν, hν⟩ := hω
  rwa [qBoundaryMeasure_eq hν]

/-- The same for the normalized field `Z = X − X(fc(0,R))`. -/
theorem ae_isVagueLimitR_qBoundaryMeasure_zField [IsProbabilityMeasure P]
    (hX : IsFreeGFFModConstH X P) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (R : ℝ) :
    ∀ᵐ ω ∂P, IsVagueLimitR (bdryApprox γ (zField X R ω)) (qBoundaryMeasure γ (zField X R ω)) := by
  filter_upwards [ae_exists_isVagueLimitR hX hγ hγ2, ae_bdryApprox_eq_smul hX γ R] with ω hω hs
  obtain ⟨ν, hν⟩ := hω
  set c := ENNReal.ofReal (exp (γ / 2 * X ω (foldedCircle 0 R))) with hc
  have hc0 : c ≠ 0 := by rw [hc, Ne, ENNReal.ofReal_eq_zero, not_le]; exact exp_pos _
  have hcT : c ≠ ∞ := ENNReal.ofReal_ne_top
  have hZ : (fun k => c⁻¹ • bdryApprox γ (X ω) k) = bdryApprox γ (zField X R ω) := by
    funext k; rw [hs k, smul_smul, ENNReal.inv_mul_cancel hc0 hcT, one_smul]
  have hν' := BdryVague.IsVagueLimitR.const_smul hν (c := c⁻¹) (ENNReal.inv_ne_top.2 hc0)
  rw [hZ] at hν'
  rwa [qBoundaryMeasure_eq hν']

/-! ### `L¹` convergence with a rate -/

/-- **M4-B3 (`L¹` rate)**: `E|∫ f dν_k(Z) − ∫ f dν(Z)| ≤ C e^{-β k log 2}` for `f ∈ C_c`
vanishing off `S`, where `|t| + 1 ≤ R` on `S`. -/
theorem integral_abs_bdryApprox_sub_qBoundaryMeasure_le [IsProbabilityMeasure P]
    (hX : IsFreeGFFModConstH X P) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {R : ℝ} {S : Set ℝ}
    (hS : MeasurableSet S) (hSf : volume S < ∞) (hSR : ∀ t ∈ S, |t| + 1 ≤ R) {f : ℝ → ℝ}
    (hf : Continuous f) (hcs : HasCompactSupport f) (hfS : ∀ t ∉ S, f t = 0) :
    ∃ C, 0 ≤ C ∧ ∀ k : ℕ,
      Integrable (fun ω => ∫ t, f t ∂(bdryApprox γ (zField X R ω) k) -
        ∫ t, f t ∂(qBoundaryMeasure γ (zField X R ω))) P ∧
      ∫ ω, |∫ t, f t ∂(bdryApprox γ (zField X R ω) k) -
        ∫ t, f t ∂(qBoundaryMeasure γ (zField X R ω))| ∂P
        ≤ C * exp (-bdryRate γ * (k * log 2)) := by
  obtain ⟨M, hM⟩ := hf.bounded_above_of_compact_support hcs
  have hM' : ∀ t, |f t| ≤ M := fun t => by simpa [Real.norm_eq_abs] using hM t
  obtain ⟨C, hC0, hC⟩ :=
    integral_abs_bdryApprox_step_le_rate hX hγ hγ2 hS hSf hSR hf.measurable hM' hfS
  have hint := integrable_integral_bdryApprox hX hS hSf hSR γ hf.measurable hM' hfS
  have hsum := summable_of_le_geom (fun k => integral_nonneg fun ω => abs_nonneg _) hγ hγ2 hC
  have hl : ∀ᵐ ω ∂P, Tendsto (fun k => ∫ t, f t ∂(bdryApprox γ (zField X R ω) k)) atTop
      (𝓝 (∫ t, f t ∂(qBoundaryMeasure γ (zField X R ω)))) := by
    filter_upwards [ae_isVagueLimitR_qBoundaryMeasure_zField hX hγ hγ2 R] with ω hω
    exact hω.2 f hf hcs
  set q := exp (-bdryRate γ * log 2) with hq
  have hq0 : 0 < q := exp_pos _
  have hq1 : q < 1 := by
    rw [hq, exp_lt_one_iff]
    have := bdryRate_pos hγ hγ2
    have := log_pos one_lt_two
    nlinarith
  have hpow : ∀ j : ℕ, exp (-bdryRate γ * (j * log 2)) = q ^ j := by
    intro j; rw [hq, ← exp_nat_mul]; congr 1; ring
  refine ⟨C / (1 - q), div_nonneg hC0 (by linarith), fun k => ?_⟩
  obtain ⟨hI, hB⟩ := integral_abs_sub_lim_le hint hsum hl k
  refine ⟨hI, hB.trans ?_⟩
  have hsum' := (summable_nat_add_iff k).2 hsum
  simp only [add_assoc] at hsum'
  calc _ ≤ ∑' m, C * q ^ k * q ^ m := by
        refine Summable.tsum_le_tsum (fun m => (hC (k + m)).trans (le_of_eq ?_)) ?_
          ((summable_geometric_of_lt_one hq0.le hq1).mul_left _)
        · rw [hpow, pow_add]; ring
        · simpa [add_comm, add_left_comm, add_assoc] using hsum'
    _ = C * q ^ k * (1 - q)⁻¹ := by rw [tsum_mul_left, tsum_geometric_of_lt_one hq0.le hq1]
    _ = C / (1 - q) * exp (-bdryRate γ * (k * log 2)) := by rw [hpow]; ring

/-- **M4-B3 (convergence of first moments)**: `∫ f dν(Z)` is integrable and
`E ∫ f dν_k(Z) → E ∫ f dν(Z)`. -/
theorem tendsto_integral_bdryApprox [IsProbabilityMeasure P]
    (hX : IsFreeGFFModConstH X P) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {R : ℝ} {S : Set ℝ}
    (hS : MeasurableSet S) (hSf : volume S < ∞) (hSR : ∀ t ∈ S, |t| + 1 ≤ R) {f : ℝ → ℝ}
    (hf : Continuous f) (hcs : HasCompactSupport f) (hfS : ∀ t ∉ S, f t = 0) :
    Integrable (fun ω => ∫ t, f t ∂(qBoundaryMeasure γ (zField X R ω))) P ∧
      Tendsto (fun k => ∫ ω, ∫ t, f t ∂(bdryApprox γ (zField X R ω) k) ∂P) atTop
        (𝓝 (∫ ω, ∫ t, f t ∂(qBoundaryMeasure γ (zField X R ω)) ∂P)) := by
  obtain ⟨M, hM⟩ := hf.bounded_above_of_compact_support hcs
  have hM' : ∀ t, |f t| ≤ M := fun t => by simpa [Real.norm_eq_abs] using hM t
  have hint := integrable_integral_bdryApprox hX hS hSf hSR γ hf.measurable hM' hfS
  obtain ⟨C, -, hC⟩ :=
    integral_abs_bdryApprox_sub_qBoundaryMeasure_le hX hγ hγ2 hS hSf hSR hf hcs hfS
  have hGl : Integrable (fun ω => ∫ t, f t ∂(qBoundaryMeasure γ (zField X R ω))) P :=
    ((hint 0).sub (hC 0).1).congr (ae_of_all _ fun ω => by simp)
  refine ⟨hGl, ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun k : ℕ => C * exp (-bdryRate γ * (k * log 2))) atTop (𝓝 0) := by
    have hq1 : exp (-bdryRate γ * log 2) < 1 := by
      rw [exp_lt_one_iff]
      have := bdryRate_pos hγ hγ2
      have := log_pos one_lt_two
      nlinarith
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (exp_pos _).le hq1).const_mul C
    rw [mul_zero] at this
    refine this.congr fun k => ?_
    rw [← exp_nat_mul]; congr 2; ring
  refine squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_) hlim
  rw [Real.norm_eq_abs, ← integral_sub (hint k) hGl]
  exact (abs_integral_le_integral_abs).trans (hC k).2

end BdryExist
end QuantumZipper
