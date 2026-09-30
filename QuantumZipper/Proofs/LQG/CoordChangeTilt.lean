import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# M4-T4, step 3: `L¹` comparison of exponentials of close Gaussians

For centred Gaussians `U, V` whose difference `V − U` is centred Gaussian of variance `v_D`,

  `E|e^{αU} − e^{αV}| ≤ α (M₄ v_D²)^{1/4} (e^{(2/3)α² Var U} + e^{(2/3)α² Var V})`,

with `M₄ = E N(0,1)⁴`. Proof: `|e^a − e^b| ≤ |a − b| (e^a + e^b)` and Hölder with exponents
`(4, 4/3)`. Only one-dimensional laws are used. Against the normalization `E e^{αU}` the loss is
`e^{(2/3 − 1/2)α² Var U}`, which the `O(r)` energy bound of the energy lemma absorbs for every
`γ ∈ (0, 2)` (with `α = γ/2`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

namespace QuantumZipper
namespace CoordChange

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `E N(0,1)⁴`. -/
def M4 : ℝ := ∫ x, x ^ 4 ∂(gaussianReal 0 1)

theorem integral_pow_four_gaussianReal' (v : ℝ≥0) :
    ∫ x, x ^ 4 ∂(gaussianReal 0 v) = (v : ℝ) ^ 2 * M4 := by
  have hv0 : (0 : ℝ) ≤ (v : ℝ) := v.coe_nonneg
  have hmap : gaussianReal (0 : ℝ) v = (gaussianReal (0 : ℝ) 1).map (fun x => √(v : ℝ) * x) := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · ring
    · apply NNReal.eq; push_cast; rw [Real.sq_sqrt hv0]; ring
  rw [hmap, integral_map (by fun_prop) (by fun_prop)]
  have hpt : ∀ x : ℝ, (√(v : ℝ) * x) ^ 4 = (v : ℝ) ^ 2 * x ^ 4 := by
    intro x
    have : √(v : ℝ) ^ 4 = (v : ℝ) ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hv0]
    rw [mul_pow, this]
  simp_rw [hpt]
  rw [integral_const_mul]; rfl

theorem M4_nonneg : 0 ≤ M4 := integral_nonneg fun x => by positivity

theorem abs_exp_sub_exp_le (a b : ℝ) : |exp a - exp b| ≤ |a - b| * (exp a + exp b) := by
  have key : ∀ x y : ℝ, x ≤ y → exp y - exp x ≤ (y - x) * exp y := by
    intro x y hxy
    have h1 := add_one_le_exp (x - y)
    have h2 : exp (x - y) * exp y = exp x := by rw [← exp_add]; ring_nf
    nlinarith [exp_pos y]
  rcases le_total a b with h | h
  · rw [abs_sub_comm (exp a), abs_of_nonneg (sub_nonneg.2 (exp_le_exp.2 h)), abs_sub_comm a b,
      abs_of_nonneg (sub_nonneg.2 h)]
    nlinarith [key a b h, exp_pos a]
  · rw [abs_of_nonneg (sub_nonneg.2 h), abs_of_nonneg (sub_nonneg.2 (exp_le_exp.2 h))]
    nlinarith [key b a h, exp_pos b]

/-- Hölder step: `E[|D| e^{αU}] ≤ (M₄ v_D²)^{1/4} e^{(2/3)α² v_U}`. -/
theorem integral_abs_mul_exp_le {P : Measure Ω} [IsProbabilityMeasure P] {U D : Ω → ℝ}
    (hU : AEMeasurable U P) (hD : AEMeasurable D P) {vU vD : ℝ≥0}
    (lU : HasLaw U (gaussianReal 0 vU) P) (lD : HasLaw D (gaussianReal 0 vD) P) (α : ℝ) :
    Integrable (fun ω => |D ω| * exp (α * U ω)) P ∧
      ∫ ω, |D ω| * exp (α * U ω) ∂P ≤
        (M4 * (vD : ℝ) ^ 2) ^ (1 / 4 : ℝ) * exp (2 / 3 * α ^ 2 * vU) := by
  have hpq : (4 : ℝ).HolderConjugate (4 / 3) := by
    rw [Real.holderConjugate_iff]; norm_num
  have hDm : AEStronglyMeasurable (fun ω => |D ω|) P :=
    (continuous_abs.measurable.comp_aemeasurable hD).aestronglyMeasurable
  have hEm : AEStronglyMeasurable (fun ω => exp (α * U ω)) P :=
    (measurable_exp.comp_aemeasurable (hU.const_mul α)).aestronglyMeasurable
  -- the two moments
  have iD : Integrable (fun ω => |D ω| ^ (4 : ℝ)) P := by
    have hg : Integrable (fun x : ℝ => |x| ^ (4 : ℝ)) (gaussianReal 0 vD) := by
      have hmem : MemLp (fun x : ℝ => x) ((4 : ℕ) : ℝ≥0) (gaussianReal 0 vD) :=
        memLp_id_gaussianReal _
      have := hmem.integrable_norm_pow'
      refine this.congr (ae_of_all _ fun x => ?_)
      simp only
      rw [Real.norm_eq_abs, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact lD.integrable_comp (f := fun x : ℝ => |x| ^ (4 : ℝ)) hg
  have vDmom : ∫ ω, |D ω| ^ (4 : ℝ) ∂P = (vD : ℝ) ^ 2 * M4 := by
    have h := lD.integral_comp (f := fun x : ℝ => |x| ^ (4 : ℝ))
      ((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 4)).comp
        continuous_abs).aestronglyMeasurable
    rw [Function.comp_def] at h
    rw [h, ← integral_pow_four_gaussianReal']
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact Even.pow_abs ⟨2, rfl⟩ x
  have iE : Integrable (fun ω => exp (α * U ω) ^ (4 / 3 : ℝ)) P := by
    have hg : Integrable (fun x : ℝ => exp (4 / 3 * α * x)) (gaussianReal 0 vU) :=
      integrable_exp_mul_gaussianReal _
    have := lU.integrable_comp (f := fun x : ℝ => exp (4 / 3 * α * x)) hg
    refine this.congr (ae_of_all _ fun ω => ?_)
    simp only [Function.comp]
    rw [← Real.exp_mul]; ring_nf
  have vUmom : ∫ ω, exp (α * U ω) ^ (4 / 3 : ℝ) ∂P = exp (vU * (4 / 3 * α) ^ 2 / 2) := by
    have e : (fun ω => exp (α * U ω) ^ (4 / 3 : ℝ)) = fun ω => exp (4 / 3 * α * U ω) := by
      funext ω; rw [← Real.exp_mul]; ring_nf
    rw [e]
    have h := lU.integral_comp (f := fun x : ℝ => exp (4 / 3 * α * x)) (by fun_prop)
    rw [Function.comp_def] at h
    rw [h]
    have := congrFun (mgf_fun_id_gaussianReal (μ := 0) (v := vU)) (4 / 3 * α)
    simp only [mgf] at this
    rw [show (fun x : ℝ => exp (4 / 3 * α * x)) = fun x => exp (4 / 3 * α * x) from rfl]
    simpa [mul_comm] using this
  have mD : MemLp (fun ω => |D ω|) (ENNReal.ofReal 4) P := by
    rw [← integrable_norm_rpow_iff hDm (by simp) (by simp)]
    refine iD.congr (ae_of_all _ fun ω => ?_)
    simp [Real.norm_eq_abs]
  have mE : MemLp (fun ω => exp (α * U ω)) (ENNReal.ofReal (4 / 3)) P := by
    rw [← integrable_norm_rpow_iff hEm (by simp) (by simp)]
    refine iE.congr (ae_of_all _ fun ω => ?_)
    dsimp only
    rw [Real.norm_of_nonneg (exp_pos _).le, ENNReal.toReal_ofReal (by norm_num)]
  have hint : Integrable (fun ω => |D ω| * exp (α * U ω)) P := by
    refine Integrable.mono' ((iD.div_const 4).add (iE.div_const (4 / 3))) (hDm.mul hEm)
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (exp_pos _).le)]
    exact Real.young_inequality_of_nonneg (abs_nonneg _) (exp_pos _).le hpq
  refine ⟨hint, ?_⟩
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg hpq (ae_of_all _ fun ω => abs_nonneg (D ω))
    (ae_of_all _ fun ω => (exp_pos _).le) mD mE
  refine hH.trans (le_of_eq ?_)
  rw [vDmom, vUmom, ← Real.exp_mul, mul_comm ((vD : ℝ) ^ 2) M4]
  congr 2
  ring

/-- **Tilted comparison** (M4-B1 in the form used by M4-T4). -/
theorem integral_abs_exp_sub_exp_le {P : Measure Ω} [IsProbabilityMeasure P] {U V : Ω → ℝ}
    (hU : AEMeasurable U P) (hV : AEMeasurable V P) {vU vV vD : ℝ≥0}
    (lU : HasLaw U (gaussianReal 0 vU) P) (lV : HasLaw V (gaussianReal 0 vV) P)
    (lD : HasLaw (fun ω => V ω - U ω) (gaussianReal 0 vD) P) {α : ℝ} (hα : 0 ≤ α) :
    Integrable (fun ω => |exp (α * U ω) - exp (α * V ω)|) P ∧
      ∫ ω, |exp (α * U ω) - exp (α * V ω)| ∂P ≤
        α * (M4 * (vD : ℝ) ^ 2) ^ (1 / 4 : ℝ) *
          (exp (2 / 3 * α ^ 2 * vU) + exp (2 / 3 * α ^ 2 * vV)) := by
  have hDm : AEMeasurable (fun ω => V ω - U ω) P := hV.sub hU
  obtain ⟨i1, b1⟩ := integral_abs_mul_exp_le hU hDm lU lD α
  obtain ⟨i2, b2⟩ := integral_abs_mul_exp_le hV hDm lV lD α
  have hdom : Integrable (fun ω => α * (|V ω - U ω| * exp (α * U ω) +
      |V ω - U ω| * exp (α * V ω))) P := (i1.add i2).const_mul α
  have hpt : ∀ ω, |exp (α * U ω) - exp (α * V ω)| ≤
      α * (|V ω - U ω| * exp (α * U ω) + |V ω - U ω| * exp (α * V ω)) := by
    intro ω
    refine (abs_exp_sub_exp_le _ _).trans (le_of_eq ?_)
    rw [show α * U ω - α * V ω = -(α * (V ω - U ω)) by ring, abs_neg, abs_mul,
      abs_of_nonneg hα]
    ring
  have hm : AEStronglyMeasurable (fun ω => |exp (α * U ω) - exp (α * V ω)|) P :=
    (continuous_abs.measurable.comp_aemeasurable ((measurable_exp.comp_aemeasurable
      (hU.const_mul α)).sub (measurable_exp.comp_aemeasurable (hV.const_mul α)))).aestronglyMeasurable
  have hi : Integrable (fun ω => |exp (α * U ω) - exp (α * V ω)|) P :=
    hdom.mono' hm (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_abs]; exact hpt ω)
  refine ⟨hi, ?_⟩
  calc ∫ ω, |exp (α * U ω) - exp (α * V ω)| ∂P
      ≤ ∫ ω, α * (|V ω - U ω| * exp (α * U ω) + |V ω - U ω| * exp (α * V ω)) ∂P :=
        integral_mono hi hdom hpt
    _ = α * (∫ ω, |V ω - U ω| * exp (α * U ω) ∂P + ∫ ω, |V ω - U ω| * exp (α * V ω) ∂P) := by
        rw [integral_const_mul, integral_add i1 i2]
    _ ≤ α * ((M4 * (vD : ℝ) ^ 2) ^ (1 / 4 : ℝ) * exp (2 / 3 * α ^ 2 * vU) +
          (M4 * (vD : ℝ) ^ 2) ^ (1 / 4 : ℝ) * exp (2 / 3 * α ^ 2 * vV)) :=
        mul_le_mul_of_nonneg_left (add_le_add b1 b2) hα
    _ = _ := by ring

end CoordChange
end QuantumZipper
