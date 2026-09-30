import QuantumZipper.Proofs.GFF.Existence.GaussianSeries
import QuantumZipper.Proofs.GFF.K3.MixedM7AsmVer1

/-!
# K3-mixed M7-b, part 5: stochastic Fubini for a Gaussian process with a Hilbert curve

`procFubini_core`: let `Z : ℂ → Ω → ℝ` be a Gaussian process whose finite combinations
`∑ aᵢ Z(τᵢ)` are centred Gaussians of variance `‖∑ aᵢ v(τᵢ)‖²` for a bounded curve
`v : ℂ → E`, `ν` a finite measure, and `G` jointly measurable with `G(·, i) = Z i` a.s. If
`v z₀ = ∫ v dν` weakly, then `∫ G(ω, i) dν(i) = Z z₀ (ω)` a.s.

This is `Prop16Asm.gaussFubini_core` (`Prop16DomCoupleFubini.lean`, the standard `L²`
computation) with the isonormal process `W` on `E` replaced by the process `Z` indexed by `ℂ`
(only the second moments `E[Z a Z b] = ⟪v a, v b⟫` are used); the proofs are copies with this
substitution. Own write-up of the standard argument.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Function
open scoped RealInnerProductSpace

namespace QuantumZipper.K3

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {Z : ℂ → Ω → ℝ} {v : ℂ → E}
  (hW : ∀ {ι : Type} [Fintype ι] (τ : ι → ℂ) (a : ι → ℝ),
    HasLaw (fun ω => ∑ i, a i * Z (τ i) ω) (gaussianReal 0 (‖∑ i, a i • v (τ i)‖ ^ 2).toNNReal) P)
include hW

theorem procZ_law (x : ℂ) : HasLaw (Z x) (gaussianReal 0 (‖v x‖ ^ 2).toNNReal) P := by
  simpa using hW (fun _ : Fin 1 => x) (fun _ => 1)

theorem procZ_law_add (x y : ℂ) :
    HasLaw (fun ω => Z x ω + Z y ω) (gaussianReal 0 (‖v x + v y‖ ^ 2).toNNReal) P := by
  simpa [Fin.sum_univ_two] using hW ![x, y] ![1, 1]

/-- Second moments of an isonormal process. -/
theorem procZ_mul (x y : ℂ) :
    Integrable (fun ω => Z x ω * Z y ω) P ∧ ∫ ω, Z x ω * Z y ω ∂P = ⟪v x, v y⟫ := by
  have hx := (procZ_law hW x).hasGaussianLaw.memLp_two
  have hy := (procZ_law hW y).hasGaussianLaw.memLp_two
  have hcov : cov[Z x, Z y; P] = ⟪v x, v y⟫ :=
    GFFExist.gs_cov_eq (procZ_law hW x) (procZ_law hW y) (procZ_law_add hW x y)
  rw [covariance_eq_sub hx hy, GFFExist.gs_integral_eq_zero (procZ_law hW x),
    GFFExist.gs_integral_eq_zero (procZ_law hW y), mul_zero, sub_zero] at hcov
  exact ⟨hx.integrable_mul hy, hcov⟩

/-- `E|Z x · Z y| ≤ (‖v x‖² + ‖v y‖²)/2`. -/
theorem procZ_abs_mul_le (x y : ℂ) :
    ∫ ω, |Z x ω * Z y ω| ∂P ≤ (‖v x‖ ^ 2 + ‖v y‖ ^ 2) / 2 := by
  have hxx := procZ_mul hW x x
  have hyy := procZ_mul hW y y
  rw [real_inner_self_eq_norm_sq] at hxx hyy
  have hb : ∀ ω, |Z x ω * Z y ω| ≤ (Z x ω * Z x ω + Z y ω * Z y ω) / 2 := fun ω => by
    rw [abs_mul]
    nlinarith [sq_nonneg (|Z x ω| - |Z y ω|), sq_abs (Z x ω), sq_abs (Z y ω)]
  calc ∫ ω, |Z x ω * Z y ω| ∂P ≤ ∫ ω, (Z x ω * Z x ω + Z y ω * Z y ω) / 2 ∂P :=
        integral_mono (procZ_mul hW x y).1.abs ((hxx.1.add hyy.1).div_const 2) hb
    _ = (‖v x‖ ^ 2 + ‖v y‖ ^ 2) / 2 := by
        rw [integral_div, integral_add hxx.1 hyy.1, hxx.2, hyy.2]

/-- **Fubini for a pair of versions.** -/
theorem procZ_fubini_pair {α : Type*} [MeasurableSpace α] (ρ : Measure α) [IsFiniteMeasure ρ]
    {U V : α → ℂ} {M : ℝ} (hU : ∀ a, ‖v (U a)‖ ≤ M) (hV : ∀ a, ‖v (V a)‖ ≤ M)
    {A B : Ω → α → ℝ} (hAm : Measurable (uncurry A)) (hBm : Measurable (uncurry B))
    (hA : ∀ a, (fun ω => A ω a) =ᵐ[P] Z (U a)) (hB : ∀ a, (fun ω => B ω a) =ᵐ[P] Z (V a)) :
    Integrable (uncurry fun ω a => A ω a * B ω a) (P.prod ρ) ∧
      ∫ ω, ∫ a, A ω a * B ω a ∂ρ ∂P = ∫ a, ⟪v (U a), v (V a)⟫ ∂ρ := by
  have hF : Measurable (uncurry fun ω a => A ω a * B ω a) := hAm.mul hBm
  have hae : ∀ a, (fun ω => A ω a * B ω a) =ᵐ[P] fun ω => Z (U a) ω * Z (V a) ω := fun a => by
    filter_upwards [hA a, hB a] with ω h1 h2
    rw [h1, h2]
  have key : ∀ a, Integrable (fun ω => A ω a * B ω a) P ∧
      ∫ ω, A ω a * B ω a ∂P = ⟪v (U a), v (V a)⟫ ∧ ∫ ω, ‖A ω a * B ω a‖ ∂P ≤ M ^ 2 := by
    intro a
    have h := procZ_mul hW (U a) (V a)
    refine ⟨h.1.congr (hae a).symm, (integral_congr_ae (hae a)).trans h.2, ?_⟩
    have hn : (fun ω => ‖A ω a * B ω a‖) =ᵐ[P] fun ω => |Z (U a) ω * Z (V a) ω| := by
      filter_upwards [hae a] with ω h1
      rw [h1, Real.norm_eq_abs]
    rw [integral_congr_ae hn]
    refine (procZ_abs_mul_le hW (U a) (V a)).trans ?_
    have h0 : 0 ≤ M := (norm_nonneg _).trans (hU a)
    have hu := pow_le_pow_left₀ (norm_nonneg _) (hU a) 2
    have hv := pow_le_pow_left₀ (norm_nonneg _) (hV a) 2
    linarith
  have hInt : Integrable (uncurry fun ω a => A ω a * B ω a) (P.prod ρ) := by
    refine (integrable_prod_iff' hF.aestronglyMeasurable).2
      ⟨Filter.Eventually.of_forall fun a => (key a).1, ?_⟩
    refine Integrable.mono' (integrable_const (M ^ 2))
      hF.stronglyMeasurable.norm.integral_prod_left'.aestronglyMeasurable
      (Filter.Eventually.of_forall fun a => ?_)
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    exact (key a).2.2
  refine ⟨hInt, ?_⟩
  rw [integral_integral_swap hInt]
  exact integral_congr_ae (Filter.Eventually.of_forall fun a => (key a).2.1)

/-- **Stochastic Fubini for a Gaussian process with a Hilbert curve.** -/
theorem procFubini_core {ι : Type*} [MeasurableSpace ι] (ν : Measure ι) [IsFiniteMeasure ν]
    (h : ι → ℂ) {M : ℝ} (hM : ∀ i, ‖v (h i)‖ ≤ M)
    (hhh : Measurable fun p : ι × ι => ⟪v (h p.1), v (h p.2)⟫)
    (hhk : ∀ x, Measurable fun i => ⟪v (h i), x⟫)
    (G : Ω → ι → ℝ) (hGm : Measurable (uncurry G))
    (hGv : ∀ i, (fun ω => G ω i) =ᵐ[P] Z (h i)) (hWm : ∀ x, Measurable (Z x))
    (k : ℂ) (hk : ∀ x, ⟪v k, x⟫ = ∫ i, ⟪v (h i), x⟫ ∂ν) :
    ∀ᵐ ω ∂P, ∫ i, G ω i ∂ν = Z k ω := by
  set A : Ω → ℝ := fun ω => ∫ i, G ω i ∂ν with hAdef
  -- the double integral `E[A²]`
  have hG1 : Measurable (uncurry fun (ω : Ω) (p : ι × ι) => G ω p.1) :=
    hGm.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have hG2 : Measurable (uncurry fun (ω : Ω) (p : ι × ι) => G ω p.2) :=
    hGm.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  obtain ⟨hI1, hE1⟩ := procZ_fubini_pair hW (ν.prod ν) (U := fun p => h p.1)
    (V := fun p => h p.2) (fun p => hM p.1) (fun p => hM p.2) hG1 hG2 (fun p => hGv p.1)
    (fun p => hGv p.2)
  have hAA : ∀ ω, ∫ p, G ω p.1 * G ω p.2 ∂(ν.prod ν) = A ω * A ω := fun ω =>
    integral_prod_mul (G ω) (G ω)
  have hIAA : Integrable (fun ω => A ω * A ω) P := by
    refine hI1.integral_prod_left.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [uncurry_apply_pair]
    exact hAA ω
  have hbdd : Integrable (fun p : ι × ι => ⟪v (h p.1), v (h p.2)⟫) (ν.prod ν) :=
    Integrable.mono' (integrable_const (M * M)) hhh.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => by
        rw [Real.norm_eq_abs]
        exact (abs_real_inner_le_norm _ _).trans
          (mul_le_mul (hM p.1) (hM p.2) (norm_nonneg _) ((norm_nonneg _).trans (hM p.1))))
  have hinner : ∀ i, ∫ j, ⟪v (h i), v (h j)⟫ ∂ν = ⟪v k, v (h i)⟫ := fun i => by
    rw [hk (v (h i))]
    exact integral_congr_ae (Filter.Eventually.of_forall fun j => real_inner_comm _ _)
  have hkk : ∫ i, ⟪v k, v (h i)⟫ ∂ν = ⟪v k, v k⟫ := by
    rw [hk (v k)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun j => real_inner_comm _ _)
  have hEAA : ∫ ω, A ω * A ω ∂P = ⟪v k, v k⟫ := by
    rw [← integral_congr_ae (Filter.Eventually.of_forall fun ω => hAA ω), hE1,
      integral_prod _ hbdd]
    simp only [hinner]
    exact hkk
  -- the mixed moment `E[A·B]`
  have hB2 : Measurable (uncurry fun (ω : Ω) (_ : ι) => Z k ω) := (hWm k).comp measurable_fst
  obtain ⟨hI2, hE2⟩ := procZ_fubini_pair hW ν (U := h) (V := fun _ => k) (M := max M ‖v k‖)
    (fun i => (hM i).trans (le_max_left _ _)) (fun _ => le_max_right _ _) hGm hB2 hGv
    (fun _ => Filter.EventuallyEq.rfl)
  have hAB : ∀ ω, ∫ i, G ω i * Z k ω ∂ν = A ω * Z k ω := fun ω => integral_mul_const _ _
  have hIAB : Integrable (fun ω => A ω * Z k ω) P := by
    refine hI2.integral_prod_left.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [uncurry_apply_pair]
    exact hAB ω
  have hEAB : ∫ ω, A ω * Z k ω ∂P = ⟪v k, v k⟫ := by
    rw [← integral_congr_ae (Filter.Eventually.of_forall fun ω => hAB ω), hE2, hk (v k)]
  -- `E[(A − B)²] = 0`
  have hBB := procZ_mul hW k k
  have e : (fun ω => (A ω - Z k ω) ^ 2) =
      fun ω => A ω * A ω - 2 * (A ω * Z k ω) + Z k ω * Z k ω := by
    funext ω; ring
  have hI3 : Integrable (fun ω => A ω * A ω - 2 * (A ω * Z k ω)) P :=
    hIAA.sub (hIAB.const_mul 2)
  have hint : Integrable (fun ω => (A ω - Z k ω) ^ 2) P := by
    rw [e]; exact hI3.add hBB.1
  have hsq : ∫ ω, (A ω - Z k ω) ^ 2 ∂P = 0 := by
    rw [e, integral_add hI3 hBB.1,
      integral_sub hIAA (hIAB.const_mul 2), integral_const_mul, hEAA, hEAB, hBB.2]
    ring
  have h0 := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg (A ω - Z k ω)) hint).1 hsq
  filter_upwards [h0] with ω hω
  have hω' : (A ω - Z k ω) ^ 2 = 0 := hω
  exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hω')

end QuantumZipper.K3
