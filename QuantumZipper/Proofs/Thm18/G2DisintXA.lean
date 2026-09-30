import QuantumZipper.Proofs.Thm18.G2DisintXGeom
import QuantumZipper.Proofs.Thm18.G2DisintKer
import QuantumZipper.Proofs.Thm18.G2DisintBump
import QuantumZipper.Proofs.Thm18.G2DisintPos

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G2 disintegration, `x` side: the length as a function of the bump coefficient

Sheffield (arXiv:1012.4797, proof of Prop. 5.5, p. 66): given `h₀`, `ν_h = e^{(γ/2) α φ} ν_{h₀}`
on the bump, so the length `ν_h[x, 0]` is a smooth increasing function of `α`. Here:

* `g2ν₀ y` is the boundary measure of `𝔥₀ + y` (measurable in `y`), `g2xκW` its restriction to the
  window `[−δ, 0]` as an s-finite kernel;
* `g2xF y x a = ∫_{[x, 0]} e^{a g} d ν₀(y)`, `g = γφ/2`, and `g2xf` is `g2xF` on the good set
  (finite window mass, positive bump mass, `x` left of the bump), `a` elsewhere; it is jointly
  measurable, differentiable in `a` with positive derivative (`g2xf_deriv_pos`).
Own bookkeeping around `g2bump_hasDerivAt` / `g2bump_deriv_pos`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

local notation "Ω₀" => gffBase.Ω

/-- The boundary measure of `𝔥₀ + y`. -/
def g2ν₀ (γ : ℝ) (φ : ℂ → ℝ) (y : AdmIdx → ℝ) : Measure ℝ := bdryM γ (g2Field γ φ y 0)

theorem measurable_g2ν₀ (γ : ℝ) (φ : ℂ → ℝ) : Measurable (g2ν₀ γ φ) :=
  (measurable_bdryM γ).comp ((measurable_g2Field γ φ).comp (measurable_id.prodMk measurable_const))

/-- The window kernel `y ↦ ν₀(y)|_{[−δ, 0]}`. -/
def g2xκW (γ : ℝ) (i : G3Idx) (m : ℝ) : Kernel (AdmIdx → ℝ) ℝ :=
  g2FinKer (g2ν₀ γ (g2xφ i m)) (measurable_g2ν₀ γ _) (measurableSet_Icc (a := -i.δ) (b := 0))

instance g2xκW_sfinite (γ : ℝ) (i : G3Idx) (m : ℝ) : IsSFiniteKernel (g2xκW γ i m) := by
  unfold g2xκW; infer_instance

/-- The rate `g = γφ/2` on the line. -/
def g2xg (γ : ℝ) (i : G3Idx) (m : ℝ) (t : ℝ) : ℝ := γ / 2 * g2xφ i m (t : ℂ)

theorem measurable_g2xg (γ : ℝ) (i : G3Idx) (m : ℝ) : Measurable (g2xg γ i m) :=
  ((continuous_g2Phi _ _).comp Complex.continuous_ofReal).measurable.const_mul _

theorem abs_g2xg_le {γ : ℝ} (hγ : 0 < γ) (i : G3Idx) (m t : ℝ) : |g2xg γ i m t| ≤ γ / 2 := by
  unfold g2xg g2xφ
  rw [abs_mul, abs_of_pos (by positivity), abs_of_nonneg (g2Phi_nonneg _ _ _)]
  exact mul_le_of_le_one_right (by positivity) (g2Phi_le_one _ _ _)

theorem g2xg_nonneg {γ : ℝ} (hγ : 0 < γ) (i : G3Idx) (m t : ℝ) : 0 ≤ g2xg γ i m t :=
  mul_nonneg (by positivity) (g2Phi_nonneg _ _ _)

/-- The bump interval. -/
def g2xJ (i : G3Idx) (m : ℝ) : Set ℝ := Ioo (g2xP i m - g2xR i m) (g2xP i m + g2xR i m)

theorem g2xg_pos_iff {γ : ℝ} (hγ : 0 < γ) (i : G3Idx) {m : ℝ} (hm : 0 < m) (t : ℝ) :
    0 < g2xg γ i m t ↔ t ∈ g2xJ i m := by
  unfold g2xg g2xφ g2xJ
  rw [mul_pos_iff_of_pos_left (by positivity), g2Phi_pos_iff (g2xR_pos i hm).le,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_lt, mem_Ioo]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- The length as a function of the coefficient. -/
def g2xF (γ : ℝ) (i : G3Idx) (m : ℝ) (y : AdmIdx → ℝ) (x a : ℝ) : ℝ :=
  ∫ t, (Icc x 0).indicator (fun t => Real.exp (a * g2xg γ i m t)) t ∂(g2xκW γ i m y)

theorem measurable_g2xF (γ : ℝ) (i : G3Idx) (m : ℝ) :
    Measurable fun p : ((AdmIdx → ℝ) × ℝ) × ℝ => g2xF γ i m p.1.1 p.1.2 p.2 := by
  set κ' : Kernel (((AdmIdx → ℝ) × ℝ) × ℝ) ℝ := (g2xκW γ i m).comap (fun p => p.1.1)
    (measurable_fst.comp measurable_fst)
  have hS : MeasurableSet {q : (((AdmIdx → ℝ) × ℝ) × ℝ) × ℝ | q.2 ∈ Icc q.1.1.2 0} :=
    (measurableSet_le (measurable_snd.comp (measurable_fst.comp measurable_fst)) measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const)
  have hf : StronglyMeasurable fun q : (((AdmIdx → ℝ) × ℝ) × ℝ) × ℝ =>
      (Icc q.1.1.2 0).indicator (fun t => Real.exp (q.1.2 * g2xg γ i m t)) q.2 := by
    have : (fun q : (((AdmIdx → ℝ) × ℝ) × ℝ) × ℝ =>
        (Icc q.1.1.2 0).indicator (fun t => Real.exp (q.1.2 * g2xg γ i m t)) q.2) =
        {q : (((AdmIdx → ℝ) × ℝ) × ℝ) × ℝ | q.2 ∈ Icc q.1.1.2 0}.indicator
          (fun q => Real.exp (q.1.2 * g2xg γ i m q.2)) := by
      funext q; simp only [indicator, mem_setOf_eq]
    rw [this]
    exact ((Real.measurable_exp.comp ((measurable_snd.comp measurable_fst).mul
      ((measurable_g2xg γ i m).comp measurable_snd))).indicator hS).stronglyMeasurable
  exact (hf.integral_kernel_prod_right' (κ := κ')).measurable

open Classical in
/-- The good set of `(y, x)`. -/
def g2xGood (γ : ℝ) (i : G3Idx) (m : ℝ) : Set ((AdmIdx → ℝ) × ℝ) :=
  {ξ | g2ν₀ γ (g2xφ i m) ξ.1 (Icc (-i.δ) 0) < ⊤ ∧ 0 < g2ν₀ γ (g2xφ i m) ξ.1 (g2xJ i m) ∧
    -i.δ ≤ ξ.2 ∧ ξ.2 ≤ g2xP i m - g2xR i m}

theorem measurableSet_g2xGood (γ : ℝ) (i : G3Idx) (m : ℝ) : MeasurableSet (g2xGood γ i m) := by
  have h1 : Measurable fun ξ : (AdmIdx → ℝ) × ℝ => g2ν₀ γ (g2xφ i m) ξ.1 (Icc (-i.δ) 0) :=
    (Measure.measurable_coe (measurableSet_Icc (a := -i.δ) (b := 0))).comp
    ((measurable_g2ν₀ γ (g2xφ i m)).comp measurable_fst)
  have h2 : Measurable fun ξ : (AdmIdx → ℝ) × ℝ => g2ν₀ γ (g2xφ i m) ξ.1 (g2xJ i m) :=
    (Measure.measurable_coe (measurableSet_Ioo (a := g2xP i m - g2xR i m)
    (b := g2xP i m + g2xR i m))).comp ((measurable_g2ν₀ γ (g2xφ i m)).comp measurable_fst)
  exact (measurableSet_lt h1 measurable_const).inter ((measurableSet_lt measurable_const h2).inter
    ((measurableSet_le measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const)))

open Classical in
/-- **The length function** (`a` off the good set). -/
def g2xf (γ : ℝ) (i : G3Idx) (m : ℝ) (ξ : (AdmIdx → ℝ) × ℝ) (a : ℝ) : ℝ :=
  if ξ ∈ g2xGood γ i m then g2xF γ i m ξ.1 ξ.2 a else a

theorem measurable_g2xf (γ : ℝ) (i : G3Idx) (m : ℝ) :
    Measurable (Function.uncurry (g2xf γ i m)) := by
  classical
  refine Measurable.ite ((measurableSet_g2xGood γ i m).preimage measurable_fst)
    (measurable_g2xF γ i m) measurable_snd

theorem g2xκW_apply_good {γ : ℝ} {i : G3Idx} {m : ℝ} {ξ : (AdmIdx → ℝ) × ℝ}
    (hξ : ξ ∈ g2xGood γ i m) :
    g2xκW γ i m ξ.1 = (g2ν₀ γ (g2xφ i m) ξ.1).restrict (Icc (-i.δ) 0) := by
  rw [g2xκW, g2FinKer_apply, if_pos hξ.1]

theorem g2xF_eq_good {γ : ℝ} {i : G3Idx} {m : ℝ} {ξ : (AdmIdx → ℝ) × ℝ}
    (hξ : ξ ∈ g2xGood γ i m) (a : ℝ) :
    g2xF γ i m ξ.1 ξ.2 a = ∫ t, Real.exp (a * g2xg γ i m t)
      ∂((g2ν₀ γ (g2xφ i m) ξ.1).restrict (Icc (-i.δ) 0)).restrict (Icc ξ.2 0) := by
  rw [g2xF, g2xκW_apply_good hξ, integral_indicator measurableSet_Icc]

theorem g2xf_hasDerivAt {γ : ℝ} (hγ : 0 < γ) (i : G3Idx) {m : ℝ} (hm : 0 < m)
    (ξ : (AdmIdx → ℝ) × ℝ) (a : ℝ) :
    ∃ d, 0 < d ∧ HasDerivAt (g2xf γ i m ξ) d a := by
  by_cases hξ : ξ ∈ g2xGood γ i m
  · set μ := ((g2ν₀ γ (g2xφ i m) ξ.1).restrict (Icc (-i.δ) 0)).restrict (Icc ξ.2 0) with hμ
    have : IsFiniteMeasure μ := by
      refine ⟨?_⟩
      rw [hμ, Measure.restrict_apply_univ, Measure.restrict_apply measurableSet_Icc]
      exact (measure_mono inter_subset_right).trans_lt hξ.1
    have hfun : g2xf γ i m ξ = fun b => ∫ t, Real.exp (b * g2xg γ i m t) ∂μ := by
      funext b; simp only [g2xf, if_pos hξ]; exact g2xF_eq_good hξ b
    refine ⟨_, g2bump_deriv_pos (ν := μ) (measurable_g2xg γ i m) (abs_g2xg_le hγ i m)
      (g2xg_nonneg hγ i m) ?_ a, ?_⟩
    · have hJ : g2xJ i m ⊆ Icc (-i.δ) 0 ∩ Icc ξ.2 0 := by
        intro t ht
        have h0 := g2x_bump_neg i hm
        have := hξ.2.2.1; have := hξ.2.2.2
        exact ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩
      calc 0 < g2ν₀ γ (g2xφ i m) ξ.1 (g2xJ i m) := hξ.2.1
        _ = μ (g2xJ i m) := by
            have hJm : MeasurableSet (g2xJ i m) := measurableSet_Ioo
            rw [hμ, Measure.restrict_apply hJm,
              Measure.restrict_apply (hJm.inter measurableSet_Icc),
              inter_assoc, inter_comm (Icc ξ.2 0), inter_eq_left.2 hJ]
        _ ≤ μ {t | 0 < g2xg γ i m t} := measure_mono fun t ht => (g2xg_pos_iff hγ i hm t).2 ht
    · rw [hfun]; exact g2bump_hasDerivAt (measurable_g2xg γ i m) (abs_g2xg_le hγ i m) a
  · refine ⟨1, one_pos, ?_⟩
    have : g2xf γ i m ξ = id := by funext b; simp [g2xf, hξ]
    rw [this]; exact hasDerivAt_id a

theorem g2xf_differentiable {γ : ℝ} (hγ : 0 < γ) (i : G3Idx) {m : ℝ} (hm : 0 < m)
    (ξ : (AdmIdx → ℝ) × ℝ) : Differentiable ℝ (g2xf γ i m ξ) := fun a =>
  let ⟨_, _, h⟩ := g2xf_hasDerivAt hγ i hm ξ a
  h.differentiableAt

theorem g2xf_deriv_pos {γ : ℝ} (hγ : 0 < γ) (i : G3Idx) {m : ℝ} (hm : 0 < m)
    (ξ : (AdmIdx → ℝ) × ℝ) (a : ℝ) : 0 < deriv (g2xf γ i m ξ) a := by
  obtain ⟨d, hd, h⟩ := g2xf_hasDerivAt hγ i hm ξ a
  rw [h.deriv]; exact hd

end Thm18Asm
end QuantumZipper
