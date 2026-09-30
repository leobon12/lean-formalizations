import QuantumZipper.Proofs.Thm18.G1FMVarDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-FM-KOLM5 (1): the clamped 5D block coordinates

Task G1-FM-KOLM5. Elementary facts on the clamped coordinates of `G1FMVarDefs.lean` (own
elementary bookkeeping, as in `D3PlusN2FMVarClamp.lean`): the scale clamp `fmSSq` lies in
`[1/(m+1), m+1]` and inverts `fmParam5` there; the projection `fmPr` inverts `fmParam5` to
`fmParam`; the clamped parameters are Lipschitz in `q`; the pushed measures keep the total mass;
and a continuous modification of a measurable process on `ℝ^d` can be chosen measurable (the
`d`-parameter copy of `WedgeTK.exists_measurable_modification4`).
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Real

namespace QuantumZipper
namespace Thm18Asm
namespace G1FM

open D3Plus

theorem fmSSq_mem (m n : ℕ) (q : Fin 5 → ℝ) :
    fmSSq m n q ∈ Icc (1 / ((m : ℝ) + 1)) ((m : ℝ) + 1) := by
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hx : (0 : ℝ) < 2 ^ n := by positivity
  have h2 := two_pow_inv_pos n
  have hR : (2 : ℝ) ^ n / ((m : ℝ) + 1) ≤ ((m : ℝ) + 1) * 2 ^ n := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : (1 : ℝ) ≤ ((m : ℝ) + 1) * ((m : ℝ) + 1) := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h1 hx.le]
  constructor
  · have h := fmCl_ge (2 ^ n / ((m : ℝ) + 1)) (((m : ℝ) + 1) * 2 ^ n) (q 4)
    calc 1 / ((m : ℝ) + 1) = (2 : ℝ)⁻¹ ^ n * (2 ^ n / ((m : ℝ) + 1)) := by
          rw [mul_div_assoc', two_pow_mul_inv_pow]
      _ ≤ _ := mul_le_mul_of_nonneg_left h h2.le
  · have h3 := fmCl_le hR (q 4)
    calc fmSSq m n q ≤ (2 : ℝ)⁻¹ ^ n * (((m : ℝ) + 1) * 2 ^ n) :=
          mul_le_mul_of_nonneg_left h3 h2.le
      _ = (m : ℝ) + 1 := by
          rw [mul_comm ((m : ℝ) + 1), ← mul_assoc, two_pow_mul_inv_pow, one_mul]

theorem fmSSq_pos (m n : ℕ) (q : Fin 5 → ℝ) : 0 < fmSSq m n q :=
  lt_of_lt_of_le (by positivity) (fmSSq_mem m n q).1

theorem fmPr_fmParam5 (n : ℕ) (w : ℂ) (τ s S : ℝ) :
    fmPr (G1FM.fmParam5 n w τ s S) = fmParam n w τ s := by
  funext i; fin_cases i <;> rfl

theorem fmSSq_fmParam5 {m n : ℕ} {w : ℂ} {τ s S : ℝ}
    (hS : S ∈ Icc (1 / ((m : ℝ) + 1)) ((m : ℝ) + 1)) :
    fmSSq m n (G1FM.fmParam5 n w τ s S) = S := by
  have hx : (0 : ℝ) < 2 ^ n := by positivity
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  unfold fmSSq
  rw [show G1FM.fmParam5 n w τ s S 4 = 2 ^ n * S from rfl, fmCl_of_mem, inv_pow_mul_cancel]
  · have h := hS.1
    rw [div_le_iff₀ hm1]
    rw [div_le_iff₀ hm1] at h
    nlinarith
  · have h := hS.2
    nlinarith

theorem norm_fmPr_sub_le (q q' : Fin 5 → ℝ) : ‖fmPr q - fmPr q'‖ ≤ ‖q - q'‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  exact norm_le_pi_norm (q - q') (Fin.castSucc i)

theorem abs_fmSSq_sub_le (m n : ℕ) (q q' : Fin 5 → ℝ) :
    |fmSSq m n q - fmSSq m n q'| ≤ (2 : ℝ)⁻¹ ^ n * ‖q - q'‖ := by
  have h2 := two_pow_inv_pos n
  unfold fmSSq
  rw [← mul_sub, abs_mul, abs_of_pos h2]
  refine mul_le_mul_of_nonneg_left ((abs_fmCl_sub_le _ _ _ _).trans ?_) h2.le
  have := norm_le_pi_norm (q - q') 4
  simpa [Real.norm_eq_abs] using this

/-- The clamped 5D parameters move by at most `5 · 2^{-n} ‖q − q'‖`. -/
theorem fmParams5_lip (m n : ℕ) (q q' : Fin 5 → ℝ) :
    ‖fmCq m n (fmPr q) - fmCq m n (fmPr q')‖ + |fmRq n (fmPr q) - fmRq n (fmPr q')| +
        |fmSq n (fmPr q) - fmSq n (fmPr q')| + |fmSSq m n q - fmSSq m n q'| ≤
      5 * (2 : ℝ)⁻¹ ^ n * ‖q - q'‖ := by
  have h1 := fmParams_lip m n (fmPr q) (fmPr q')
  have h2 := abs_fmSSq_sub_le m n q q'
  have h3 := norm_fmPr_sub_le q q'
  have h4 := two_pow_inv_pos n
  have h5 := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 4 * (2 : ℝ)⁻¹ ^ n)
  linarith

theorem pfmMeas_univ {ψ : ℂ → ℂ} (hψ : Measurable ψ) (S : ℝ) (w v : ℂ) (s : ℝ) :
    pfmMeas ψ S w v s univ = fmBase univ := by
  unfold pfmMeas
  rw [Measure.map_apply (by fun_prop : Measurable fun z => (S : ℂ) * ψ z) MeasurableSet.univ, preimage_univ,
    fmMeas_univ]

/-- A continuous modification of a measurable process on `ℝ^d` can be chosen measurable in `ω`
at every parameter (copy of `WedgeTK.exists_measurable_modification4` for any `d`). -/
theorem exists_measurable_modificationN {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Y V : (Fin d → ℝ) → Ω → ℝ}
    (hYc : ∀ ω, Continuous fun q => Y q ω) (hV : ∀ q, Measurable (V q))
    (hYV : ∀ q, (fun ω => Y q ω) =ᵐ[P] V q) :
    ∃ Y' : (Fin d → ℝ) → Ω → ℝ, (∀ ω, Continuous fun q => Y' q ω) ∧
      (∀ q, Measurable (Y' q)) ∧ (∀ᵐ ω ∂P, ∀ q, Y' q ω = Y q ω) := by
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense (Fin d → ℝ)
  have hall : ∀ᵐ ω ∂P, ∀ s ∈ S, Y s ω = V s ω :=
    (eventually_countable_ball hSc).2 fun s _ => hYV s
  set N := {ω | ¬ ∀ s ∈ S, Y s ω = V s ω} with hN_def
  have hN : P N = 0 := ae_iff.1 hall
  set Ω₁ := (toMeasurable P N)ᶜ with hΩ₁_def
  have hΩ₁m : MeasurableSet Ω₁ := (measurableSet_toMeasurable P N).compl
  have hΩ₁ : ∀ ω ∈ Ω₁, ∀ s ∈ S, Y s ω = V s ω := fun ω hω => by
    by_contra h; exact hω (subset_toMeasurable P N h)
  have hΩ₁ae : ∀ᵐ ω ∂P, ω ∈ Ω₁ := by
    rw [ae_iff]
    have : {a | ¬ a ∈ Ω₁} = toMeasurable P N := by ext; simp [Ω₁]
    rw [this, measure_toMeasurable, hN]
  refine ⟨fun q ω => Ω₁.indicator (fun ω => Y q ω) ω, fun ω => ?_, fun q => ?_, ?_⟩
  · by_cases hω : ω ∈ Ω₁
    · simp only [Set.indicator_of_mem hω]; exact hYc ω
    · simp only [hω, not_false_eq_true, Set.indicator_of_notMem]; exact continuous_const
  · have hq : q ∈ closure S := by rw [hSd.closure_eq]; exact Set.mem_univ q
    obtain ⟨u, huS, hu⟩ := mem_closure_iff_seq_limit.1 hq
    refine measurable_of_tendsto_metrizable (f := fun n ω => Ω₁.indicator (V (u n)) ω)
      (fun n => (hV (u n)).indicator hΩ₁m) ?_
    rw [tendsto_pi_nhds]; intro ω
    by_cases hω : ω ∈ Ω₁
    · simp only [Set.indicator_of_mem hω]
      have : ∀ n, V (u n) ω = Y (u n) ω := fun n => (hΩ₁ ω hω (u n) (huS n)).symm
      simp_rw [this]
      exact ((hYc ω).tendsto q).comp hu
    · simp only [hω, not_false_eq_true, Set.indicator_of_notMem]
      exact tendsto_const_nhds
  · filter_upwards [hΩ₁ae] with ω hω q
    simp only [Set.indicator_of_mem hω]

end G1FM
end Thm18Asm
end QuantumZipper
