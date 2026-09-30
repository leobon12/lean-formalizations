import QuantumZipper.Proofs.GFF.Existence.GaussianSeries
import Mathlib.Probability.Moments.Covariance
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Proposition 1.6, node DOM-COUPLE (part 3): stochastic Fubini for isonormal processes

`gaussFubini_core`: let `W` be an isonormal process on a real inner product space `E` (all finite
combinations `∑ aᵢ W(xᵢ)` are centered Gaussians of variance `‖∑ aᵢ xᵢ‖²`), `h : ι → E` bounded,
`ν` a finite measure on `ι`, and `G : Ω → ι → ℝ` jointly measurable with `G(·, i) = W(h i)` a.s.
for every `i`. If `k = ∫ h dν` weakly (`⟪k, x⟫ = ∫ ⟪h i, x⟫ dν` for all `x`), then
`∫ G(ω, i) dν(i) = W(k)(ω)` for a.e. `ω`.

Proof (standard `L²` computation, own write-up): with `A = ∫ G dν`, `B = W k`, Fubini gives
`E[A²] = ∫∫ ⟪h i, h j⟫ = ‖k‖²`, `E[AB] = ∫ ⟪h i, k⟫ = ‖k‖²`, `E[B²] = ‖k‖²`, so
`E[(A − B)²] = 0`. This is the Fubini half of the sub-node `GaussContFubiniStmt`
(`Prop16DomCoupleNodes.lean`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Function
open scoped RealInnerProductSpace

namespace QuantumZipper

namespace Prop16Asm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {W : E → Ω → ℝ}
  (hW : ∀ {ι : Type} [Fintype ι] (τ : ι → E) (a : ι → ℝ),
    HasLaw (fun ω => ∑ i, a i * W (τ i) ω) (gaussianReal 0 (‖∑ i, a i • τ i‖ ^ 2).toNNReal) P)
include hW

theorem isoW_law (x : E) : HasLaw (W x) (gaussianReal 0 (‖x‖ ^ 2).toNNReal) P := by
  simpa using hW (fun _ : Fin 1 => x) (fun _ => 1)

theorem isoW_law_add (x y : E) :
    HasLaw (fun ω => W x ω + W y ω) (gaussianReal 0 (‖x + y‖ ^ 2).toNNReal) P := by
  simpa [Fin.sum_univ_two] using hW ![x, y] ![1, 1]

/-- Second moments of an isonormal process. -/
theorem isoW_mul (x y : E) :
    Integrable (fun ω => W x ω * W y ω) P ∧ ∫ ω, W x ω * W y ω ∂P = ⟪x, y⟫ := by
  have hx := (isoW_law hW x).hasGaussianLaw.memLp_two
  have hy := (isoW_law hW y).hasGaussianLaw.memLp_two
  have hcov : cov[W x, W y; P] = ⟪x, y⟫ :=
    GFFExist.gs_cov_eq (isoW_law hW x) (isoW_law hW y) (isoW_law_add hW x y)
  rw [covariance_eq_sub hx hy, GFFExist.gs_integral_eq_zero (isoW_law hW x),
    GFFExist.gs_integral_eq_zero (isoW_law hW y), mul_zero, sub_zero] at hcov
  exact ⟨hx.integrable_mul hy, hcov⟩

/-- `E|W x · W y| ≤ (‖x‖² + ‖y‖²)/2`. -/
theorem isoW_abs_mul_le (x y : E) :
    ∫ ω, |W x ω * W y ω| ∂P ≤ (‖x‖ ^ 2 + ‖y‖ ^ 2) / 2 := by
  have hxx := isoW_mul hW x x
  have hyy := isoW_mul hW y y
  rw [real_inner_self_eq_norm_sq] at hxx hyy
  have hb : ∀ ω, |W x ω * W y ω| ≤ (W x ω * W x ω + W y ω * W y ω) / 2 := fun ω => by
    rw [abs_mul]
    nlinarith [sq_nonneg (|W x ω| - |W y ω|), sq_abs (W x ω), sq_abs (W y ω)]
  calc ∫ ω, |W x ω * W y ω| ∂P ≤ ∫ ω, (W x ω * W x ω + W y ω * W y ω) / 2 ∂P :=
        integral_mono (isoW_mul hW x y).1.abs ((hxx.1.add hyy.1).div_const 2) hb
    _ = (‖x‖ ^ 2 + ‖y‖ ^ 2) / 2 := by
        rw [integral_div, integral_add hxx.1 hyy.1, hxx.2, hyy.2]

/-- **Fubini for a pair of versions.** -/
theorem isoW_fubini_pair {α : Type*} [MeasurableSpace α] (ρ : Measure α) [IsFiniteMeasure ρ]
    {U V : α → E} {M : ℝ} (hU : ∀ a, ‖U a‖ ≤ M) (hV : ∀ a, ‖V a‖ ≤ M)
    {A B : Ω → α → ℝ} (hAm : Measurable (uncurry A)) (hBm : Measurable (uncurry B))
    (hA : ∀ a, (fun ω => A ω a) =ᵐ[P] W (U a)) (hB : ∀ a, (fun ω => B ω a) =ᵐ[P] W (V a)) :
    Integrable (uncurry fun ω a => A ω a * B ω a) (P.prod ρ) ∧
      ∫ ω, ∫ a, A ω a * B ω a ∂ρ ∂P = ∫ a, ⟪U a, V a⟫ ∂ρ := by
  have hF : Measurable (uncurry fun ω a => A ω a * B ω a) := hAm.mul hBm
  have hae : ∀ a, (fun ω => A ω a * B ω a) =ᵐ[P] fun ω => W (U a) ω * W (V a) ω := fun a => by
    filter_upwards [hA a, hB a] with ω h1 h2
    rw [h1, h2]
  have key : ∀ a, Integrable (fun ω => A ω a * B ω a) P ∧
      ∫ ω, A ω a * B ω a ∂P = ⟪U a, V a⟫ ∧ ∫ ω, ‖A ω a * B ω a‖ ∂P ≤ M ^ 2 := by
    intro a
    have h := isoW_mul hW (U a) (V a)
    refine ⟨h.1.congr (hae a).symm, (integral_congr_ae (hae a)).trans h.2, ?_⟩
    have hn : (fun ω => ‖A ω a * B ω a‖) =ᵐ[P] fun ω => |W (U a) ω * W (V a) ω| := by
      filter_upwards [hae a] with ω h1
      rw [h1, Real.norm_eq_abs]
    rw [integral_congr_ae hn]
    refine (isoW_abs_mul_le hW (U a) (V a)).trans ?_
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

/-- **Stochastic Fubini for an isonormal process.** -/
theorem gaussFubini_core {ι : Type*} [MeasurableSpace ι] (ν : Measure ι) [IsFiniteMeasure ν]
    (h : ι → E) {M : ℝ} (hM : ∀ i, ‖h i‖ ≤ M)
    (hhh : Measurable fun p : ι × ι => ⟪h p.1, h p.2⟫)
    (hhk : ∀ x, Measurable fun i => ⟪h i, x⟫)
    (G : Ω → ι → ℝ) (hGm : Measurable (uncurry G))
    (hGv : ∀ i, (fun ω => G ω i) =ᵐ[P] W (h i)) (hWm : ∀ x, Measurable (W x))
    (k : E) (hk : ∀ x, ⟪k, x⟫ = ∫ i, ⟪h i, x⟫ ∂ν) :
    ∀ᵐ ω ∂P, ∫ i, G ω i ∂ν = W k ω := by
  set A : Ω → ℝ := fun ω => ∫ i, G ω i ∂ν with hAdef
  -- the double integral `E[A²]`
  have hG1 : Measurable (uncurry fun (ω : Ω) (p : ι × ι) => G ω p.1) :=
    hGm.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have hG2 : Measurable (uncurry fun (ω : Ω) (p : ι × ι) => G ω p.2) :=
    hGm.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  obtain ⟨hI1, hE1⟩ := isoW_fubini_pair hW (ν.prod ν) (U := fun p => h p.1)
    (V := fun p => h p.2) (fun p => hM p.1) (fun p => hM p.2) hG1 hG2 (fun p => hGv p.1)
    (fun p => hGv p.2)
  have hAA : ∀ ω, ∫ p, G ω p.1 * G ω p.2 ∂(ν.prod ν) = A ω * A ω := fun ω =>
    integral_prod_mul (G ω) (G ω)
  have hIAA : Integrable (fun ω => A ω * A ω) P := by
    refine hI1.integral_prod_left.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [uncurry_apply_pair]
    exact hAA ω
  have hbdd : Integrable (fun p : ι × ι => ⟪h p.1, h p.2⟫) (ν.prod ν) :=
    Integrable.mono' (integrable_const (M * M)) hhh.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => by
        rw [Real.norm_eq_abs]
        exact (abs_real_inner_le_norm _ _).trans
          (mul_le_mul (hM p.1) (hM p.2) (norm_nonneg _) ((norm_nonneg _).trans (hM p.1))))
  have hinner : ∀ i, ∫ j, ⟪h i, h j⟫ ∂ν = ⟪k, h i⟫ := fun i => by
    rw [hk (h i)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun j => real_inner_comm _ _)
  have hkk : ∫ i, ⟪k, h i⟫ ∂ν = ⟪k, k⟫ := by
    rw [hk k]
    exact integral_congr_ae (Filter.Eventually.of_forall fun j => real_inner_comm _ _)
  have hEAA : ∫ ω, A ω * A ω ∂P = ⟪k, k⟫ := by
    rw [← integral_congr_ae (Filter.Eventually.of_forall fun ω => hAA ω), hE1,
      integral_prod _ hbdd]
    simp only [hinner]
    exact hkk
  -- the mixed moment `E[A·B]`
  have hB2 : Measurable (uncurry fun (ω : Ω) (_ : ι) => W k ω) := (hWm k).comp measurable_fst
  obtain ⟨hI2, hE2⟩ := isoW_fubini_pair hW ν (U := h) (V := fun _ => k) (M := max M ‖k‖)
    (fun i => (hM i).trans (le_max_left _ _)) (fun _ => le_max_right _ _) hGm hB2 hGv
    (fun _ => Filter.EventuallyEq.rfl)
  have hAB : ∀ ω, ∫ i, G ω i * W k ω ∂ν = A ω * W k ω := fun ω => integral_mul_const _ _
  have hIAB : Integrable (fun ω => A ω * W k ω) P := by
    refine hI2.integral_prod_left.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [uncurry_apply_pair]
    exact hAB ω
  have hEAB : ∫ ω, A ω * W k ω ∂P = ⟪k, k⟫ := by
    rw [← integral_congr_ae (Filter.Eventually.of_forall fun ω => hAB ω), hE2, hk k]
  -- `E[(A − B)²] = 0`
  have hBB := isoW_mul hW k k
  have e : (fun ω => (A ω - W k ω) ^ 2) =
      fun ω => A ω * A ω - 2 * (A ω * W k ω) + W k ω * W k ω := by
    funext ω; ring
  have hI3 : Integrable (fun ω => A ω * A ω - 2 * (A ω * W k ω)) P :=
    hIAA.sub (hIAB.const_mul 2)
  have hint : Integrable (fun ω => (A ω - W k ω) ^ 2) P := by
    rw [e]; exact hI3.add hBB.1
  have hsq : ∫ ω, (A ω - W k ω) ^ 2 ∂P = 0 := by
    rw [e, integral_add hI3 hBB.1,
      integral_sub hIAA (hIAB.const_mul 2), integral_const_mul, hEAA, hEAB, hBB.2]
    ring
  have h0 := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg (A ω - W k ω)) hint).1 hsq
  filter_upwards [h0] with ω hω
  have hω' : (A ω - W k ω) ^ 2 = 0 := hω
  exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hω')

end Prop16Asm

end QuantumZipper
