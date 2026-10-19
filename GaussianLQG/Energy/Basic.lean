import GaussianLQG.Energy.LogPotential

/-!
# Well-definedness of the energy (blueprint Lemma `lem:energy-finite`)

For regular measures `μ, ν` (blueprint Definition `def:regular`):

* `IsRegular.integrable_kernelG`: `G` is integrable for `μ ⊗ ν`;
* `IsRegular.prod_diagonal_eq_zero`: `μ ⊗ ν` gives no mass to the diagonal;
* `energy_eq_integral_prod`: `ℰ(μ, ν) = ∫ G d(μ ⊗ ν)`;
* `energy_comm`: `ℰ` is symmetric;
* `energy_sub_eq_logEnergy`: if `μ(ℂ) = ν(ℂ)`, then
  `ℰ(μ,μ) - 2ℰ(μ,ν) + ℰ(ν,ν) = L(μ,μ) - L(μ,ν) - L(ν,μ) + L(ν,ν)` with the logarithmic
  energy `L(μ,ν) = ∬ -log|x-y| dμ(x) dν(y)` (`logEnergy`), i.e. `ℰ(μ-ν, μ-ν) = ∬ -log|x-y|
  d(μ-ν)^{⊗2}` for the mass-zero signed measure `μ - ν`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal Real

namespace GaussianLQG

variable {μ ν : Measure ℂ}

/-! ## The kernel -/

theorem kernelG_comm (z w : ℂ) : kernelG z w = kernelG w z := by
  unfold kernelG
  rw [norm_sub_rev]
  ring

@[fun_prop]
theorem measurable_kernelG : Measurable fun p : ℂ × ℂ => kernelG p.1 p.2 := by
  unfold kernelG
  fun_prop

theorem log_max_one_nonneg (x : ℝ) : 0 ≤ Real.log (max 1 x) :=
  Real.log_nonneg (le_max_left _ _)

/-- `log max(1, |z|) ≤ |z|`. -/
theorem log_max_one_norm_le (z : ℂ) : Real.log (max 1 ‖z‖) ≤ ‖z‖ := by
  have h := Real.log_le_sub_one_of_pos (lt_of_lt_of_le one_pos (le_max_left 1 ‖z‖))
  have h2 : max 1 ‖z‖ ≤ ‖z‖ + 1 := max_le (by linarith [norm_nonneg z]) (by linarith)
  linarith

/-! ## Supports of products -/

/-- Two measures supported in `closedBall 0 R`: their product is supported in the product of the
balls. -/
theorem ae_prod_norm_le [SFinite μ] [SFinite ν] {R : ℝ} (hμ : μ (closedBall (0 : ℂ) R)ᶜ = 0)
    (hν : ν (closedBall (0 : ℂ) R)ᶜ = 0) : ∀ᵐ p ∂(μ.prod ν), ‖p.1‖ ≤ R ∧ ‖p.2‖ ≤ R := by
  have h1 := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae
    (ae_norm_le_of_compl_closedBall_eq_zero hμ)
  have h2 := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae
    (ae_norm_le_of_compl_closedBall_eq_zero hν)
  filter_upwards [h1, h2] with p hp1 hp2 using ⟨hp1, hp2⟩

/-- Two regular measures have a common support radius `R ≥ 1`. -/
theorem IsRegular.exists_common_support (hμ : IsRegular μ) (hν : IsRegular ν) :
    ∃ R : ℝ, 1 ≤ R ∧ μ (closedBall (0 : ℂ) R)ᶜ = 0 ∧ ν (closedBall (0 : ℂ) R)ᶜ = 0 := by
  obtain ⟨R, hR1, hR⟩ := hμ.exists_support
  obtain ⟨R', -, hR'⟩ := hν.exists_support
  refine ⟨max R R', hR1.trans (le_max_left _ _), measure_mono_null ?_ hR,
    measure_mono_null ?_ hR'⟩
  · exact compl_subset_compl.2 (closedBall_subset_closedBall (le_max_left _ _))
  · exact compl_subset_compl.2 (closedBall_subset_closedBall (le_max_right _ _))

/-! ## Integrability -/

/-- `log max(1, |z|)` is integrable for a finite measure with bounded support. -/
theorem integrable_log_max_one_norm [IsFiniteMeasure μ] {R : ℝ}
    (hR : μ (closedBall (0 : ℂ) R)ᶜ = 0) : Integrable (fun z : ℂ => Real.log (max 1 ‖z‖)) μ := by
  refine Integrable.of_bound
    (by fun_prop : Measurable fun z : ℂ => Real.log (max 1 ‖z‖)).aestronglyMeasurable R ?_
  filter_upwards [ae_norm_le_of_compl_closedBall_eq_zero hR] with z hz
  rw [Real.norm_of_nonneg (log_max_one_nonneg _)]
  exact (log_max_one_norm_le z).trans hz

theorem IsRegular.integrable_log_max_one_norm (hμ : IsRegular μ) :
    Integrable (fun z : ℂ => Real.log (max 1 ‖z‖)) μ := by
  have := hμ.1
  obtain ⟨R, -, hR⟩ := hμ.exists_support
  exact GaussianLQG.integrable_log_max_one_norm hR

/-- `log⁺(ρ/|x-y|)` is integrable on `μ ⊗ ν` for regular `μ, ν` and `0 < ρ ≤ 1`. -/
theorem IsRegular.integrable_posLog_div (hμ : IsRegular μ) (hν : IsRegular ν) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    Integrable (fun p : ℂ × ℂ => log⁺ (ρ / ‖p.1 - p.2‖)) (μ.prod ν) := by
  have := hμ.1
  have := hν.1
  obtain ⟨C, α, hα, hC, hb⟩ := hν.exists_ballBound
  exact (integrable_posLog_div_prod hρ hρ1 hα hC hb).1

/-- `log⁺|x-y|` is integrable on `μ ⊗ ν` for finite measures with bounded supports. -/
theorem integrable_posLog_norm_sub [IsFiniteMeasure μ] [IsFiniteMeasure ν] {R : ℝ}
    (hμ : μ (closedBall (0 : ℂ) R)ᶜ = 0) (hν : ν (closedBall (0 : ℂ) R)ᶜ = 0) :
    Integrable (fun p : ℂ × ℂ => log⁺ ‖p.1 - p.2‖) (μ.prod ν) := by
  refine Integrable.of_bound (by fun_prop) (2 * R) ?_
  filter_upwards [ae_prod_norm_le hμ hν] with p hp
  rw [Real.norm_of_nonneg Real.posLog_nonneg]
  refine (Real.posLog_le_abs _).trans ?_
  rw [abs_norm]
  calc ‖p.1 - p.2‖ ≤ ‖p.1‖ + ‖p.2‖ := norm_sub_le _ _
    _ ≤ 2 * R := by linarith [hp.1, hp.2]

/-- `-log|x-y| = log⁺(1/|x-y|) - log⁺|x-y|`. -/
theorem neg_log_eq_posLog_sub_posLog (x : ℝ) : -Real.log x = log⁺ (1 / x) - log⁺ x := by
  have := Real.posLog_sub_posLog_inv (x := x)
  rw [one_div]
  linarith

/-- `-log|x-y|` is integrable on `μ ⊗ ν` for regular `μ, ν`. -/
theorem IsRegular.integrable_neg_log_norm_sub (hμ : IsRegular μ) (hν : IsRegular ν) :
    Integrable (fun p : ℂ × ℂ => -Real.log ‖p.1 - p.2‖) (μ.prod ν) := by
  have := hμ.1
  have := hν.1
  obtain ⟨R, -, hRμ, hRν⟩ := hμ.exists_common_support hν
  refine ((hμ.integrable_posLog_div hν one_pos le_rfl).sub
    (integrable_posLog_norm_sub hRμ hRν)).congr (ae_of_all _ fun p => ?_)
  simp only [Pi.sub_apply]
  rw [neg_log_eq_posLog_sub_posLog]

/-- Blueprint Lemma `lem:energy-finite`: `G` is integrable for `μ ⊗ ν`, `μ, ν` regular. -/
theorem IsRegular.integrable_kernelG (hμ : IsRegular μ) (hν : IsRegular ν) :
    Integrable (Function.uncurry kernelG) (μ.prod ν) := by
  have := hμ.1
  have := hν.1
  refine (((hμ.integrable_neg_log_norm_sub hν).add
    (hμ.integrable_log_max_one_norm.comp_fst ν)).add
    (hν.integrable_log_max_one_norm.comp_snd μ)).congr (ae_of_all _ fun p => ?_)
  simp only [Pi.add_apply]
  rfl

/-- Blueprint Lemma `lem:energy-finite`: `μ ⊗ ν` gives no mass to the diagonal when `ν` is
regular. -/
theorem IsRegular.prod_diagonal_eq_zero [SFinite μ] (hν : IsRegular ν) :
    (μ.prod ν) (diagonal ℂ) = 0 := by
  have := hν.1
  rw [Measure.prod_apply isClosed_diagonal.measurableSet]
  have e : ∀ x : ℂ, Prod.mk x ⁻¹' diagonal ℂ = {x} := by
    intro x
    ext y
    simp [mem_diagonal_iff, eq_comm]
  simp only [e, hν.measure_singleton, lintegral_zero]

theorem IsRegular.ae_prod_ne [SFinite μ] (hν : IsRegular ν) : ∀ᵐ p ∂(μ.prod ν), p.1 ≠ p.2 := by
  rw [ae_iff]
  refine measure_mono_null (fun p hp => ?_) (hν.prod_diagonal_eq_zero (μ := μ))
  simp only [ne_eq, not_not, mem_ofPred_eq] at hp
  exact hp

/-! ## The energy as a product integral; symmetry and bilinearity -/

theorem energy_eq_integral_prod (hμ : IsRegular μ) (hν : IsRegular ν) :
    energy μ ν = ∫ p, kernelG p.1 p.2 ∂(μ.prod ν) := by
  have := hμ.1
  have := hν.1
  rw [energy, integral_prod (fun p : ℂ × ℂ => kernelG p.1 p.2) (hμ.integrable_kernelG hν)]

/-- `ℰ` is symmetric on regular measures. -/
theorem energy_comm (hμ : IsRegular μ) (hν : IsRegular ν) : energy μ ν = energy ν μ := by
  have := hμ.1
  have := hν.1
  rw [energy, integral_integral_swap (hμ.integrable_kernelG hν), energy]
  congr 1
  funext y
  congr 1
  funext x
  exact kernelG_comm x y

/-! ## Logarithmic energy and the mass-zero identity -/

/-- The logarithmic energy `L(μ, ν) = ∬ -log|x-y| dμ(x) dν(y)`. -/
def logEnergy (μ ν : Measure ℂ) : ℝ := ∫ x, ∫ y, -Real.log ‖x - y‖ ∂ν ∂μ

theorem logEnergy_eq_integral_prod (hμ : IsRegular μ) (hν : IsRegular ν) :
    logEnergy μ ν = ∫ p, -Real.log ‖p.1 - p.2‖ ∂(μ.prod ν) := by
  have := hμ.1
  have := hν.1
  rw [logEnergy, integral_prod (fun p : ℂ × ℂ => -Real.log ‖p.1 - p.2‖)
    (hμ.integrable_neg_log_norm_sub hν)]

theorem logEnergy_comm (hμ : IsRegular μ) (hν : IsRegular ν) :
    logEnergy μ ν = logEnergy ν μ := by
  have := hμ.1
  have := hν.1
  rw [logEnergy, integral_integral_swap (f := fun x y => -Real.log ‖x - y‖)
    (hμ.integrable_neg_log_norm_sub hν), logEnergy]
  congr 1
  funext y
  congr 1
  funext x
  rw [norm_sub_rev]

/-- `ℰ(μ,ν) = L(μ,ν) + ν(ℂ) ∫ log|x|₊ dμ + μ(ℂ) ∫ log|y|₊ dν`. -/
theorem energy_eq_logEnergy_add (hμ : IsRegular μ) (hν : IsRegular ν) :
    energy μ ν = logEnergy μ ν + ν.real univ * ∫ x, Real.log (max 1 ‖x‖) ∂μ +
      μ.real univ * ∫ y, Real.log (max 1 ‖y‖) ∂ν := by
  have := hμ.1
  have := hν.1
  have h1 := hμ.integrable_neg_log_norm_sub hν
  have h2 : Integrable (fun p : ℂ × ℂ => Real.log (max 1 ‖p.1‖)) (μ.prod ν) :=
    hμ.integrable_log_max_one_norm.comp_fst ν
  have h3 : Integrable (fun p : ℂ × ℂ => Real.log (max 1 ‖p.2‖)) (μ.prod ν) :=
    hν.integrable_log_max_one_norm.comp_snd μ
  have h12 : Integrable (fun p : ℂ × ℂ => -Real.log ‖p.1 - p.2‖ + Real.log (max 1 ‖p.1‖))
      (μ.prod ν) := h1.add h2
  have e2 : ∫ p, Real.log (max 1 ‖p.1‖) ∂(μ.prod ν) =
      ν.real univ * ∫ x, Real.log (max 1 ‖x‖) ∂μ :=
    integral_fun_fst (fun x : ℂ => Real.log (max 1 ‖x‖))
  have e3 : ∫ p, Real.log (max 1 ‖p.2‖) ∂(μ.prod ν) =
      μ.real univ * ∫ y, Real.log (max 1 ‖y‖) ∂ν :=
    integral_fun_snd (fun y : ℂ => Real.log (max 1 ‖y‖))
  rw [energy_eq_integral_prod hμ hν, logEnergy_eq_integral_prod hμ hν, ← e2, ← e3,
    ← integral_add h1 h2, ← integral_add h12 h3]
  rfl

/-- Blueprint Lemma `lem:energy-finite`, last claim, for the mass-zero signed measure `μ - ν`:
if `μ(ℂ) = ν(ℂ)`, then `ℰ(μ - ν, μ - ν)`, expanded by bilinearity, equals
`∬ -log|x-y| d(μ-ν)^{⊗2}`, expanded into its four positive cross terms. -/
theorem energy_sub_eq_logEnergy (hμ : IsRegular μ) (hν : IsRegular ν) (hm : μ univ = ν univ) :
    energy μ μ - 2 * energy μ ν + energy ν ν =
      logEnergy μ μ - logEnergy μ ν - logEnergy ν μ + logEnergy ν ν := by
  rw [energy_eq_logEnergy_add hμ hμ, energy_eq_logEnergy_add hμ hν,
    energy_eq_logEnergy_add hν hν, logEnergy_comm hν hμ]
  have : μ.real univ = ν.real univ := by rw [measureReal_def, measureReal_def, hm]
  rw [this]
  ring

end GaussianLQG
