import QuantumZipper.Proofs.Thm18.G2DisintRGeom
import QuantumZipper.Proofs.Thm18.G2DisintXA
import QuantumZipper.Proofs.Thm18.G2DisintKer
import QuantumZipper.Proofs.Thm18.G2DisintBump
import QuantumZipper.Proofs.Thm18.G2DisintPos

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G2 disintegration, `R` side: the length as a function of the bump coefficient

Sheffield (arXiv:1012.4797, proof of Prop. 5.5, p. 66): given `h₀`, `ν_h = e^{(γ/2) α φ} ν_{h₀}`
on the bump, so the length `ν_h[x, 0]` is a smooth increasing function of `α`. Here:

* `g2ν₀ y` is the boundary measure of `𝔥₀ + y` (measurable in `y`), `g2rκW` its restriction to the
  window `[−δ, 0]` as an s-finite kernel;
* `g2rF y x a = ∫_{[0, x]} e^{a g} d ν₀(y)`, `g = γφ/2`, and `g2rf` is `g2rF` on the good set
  (finite window mass, positive bump mass, `x` left of the bump), `a` elsewhere; it is jointly
  measurable, differentiable in `a` with positive derivative (`g2rf_deriv_pos`).
Own bookkeeping around `g2bump_hasDerivAt` / `g2bump_deriv_pos`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

local notation "Ω₀" => gffBase.Ω

/-- The right end of the `R`-side window, strictly inside the fidelity window of
`ae_g3Fid_sets` (margin roots satisfy `y < t₂ + r₂ − m`). -/
def g2rW (i : G3Idx) (m : ℝ) : ℝ := i.t₂ + i.r₂ - g2rM' i m / 2

/-- The window kernel `y ↦ ν₀(y)|_{[−δ, 0]}`. -/
def g2rκW (γ : ℝ) (i : G3Idx) (m : ℝ) : Kernel (AdmIdx → ℝ) ℝ :=
  g2FinKer (g2ν₀ γ (g2rφ i m)) (measurable_g2ν₀ γ _) (measurableSet_Icc (a := 0) (b := g2rW i m))

instance g2rκW_sfinite (γ : ℝ) (i : G3Idx) (m : ℝ) : IsSFiniteKernel (g2rκW γ i m) := by
  unfold g2rκW; infer_instance

/-- The rate `g = γφ/2` on the line. -/
def g2rg (γ : ℝ) (i : G3Idx) (m : ℝ) (t : ℝ) : ℝ := γ / 2 * g2rφ i m (t : ℂ)

theorem measurable_g2rg (γ : ℝ) (i : G3Idx) (m : ℝ) : Measurable (g2rg γ i m) :=
  ((continuous_g2Phi _ _).comp Complex.continuous_ofReal).measurable.const_mul _

theorem abs_g2rg_le {γ : ℝ} (hγ : 0 < γ) (i : G3Idx) (m t : ℝ) : |g2rg γ i m t| ≤ γ / 2 := by
  unfold g2rg g2rφ
  rw [abs_mul, abs_of_pos (by positivity), abs_of_nonneg (g2Phi_nonneg _ _ _)]
  exact mul_le_of_le_one_right (by positivity) (g2Phi_le_one _ _ _)

theorem g2rg_nonneg {γ : ℝ} (hγ : 0 < γ) (i : G3Idx) (m t : ℝ) : 0 ≤ g2rg γ i m t :=
  mul_nonneg (by positivity) (g2Phi_nonneg _ _ _)

/-- The bump interval. -/
def g2rJ (i : G3Idx) (m : ℝ) : Set ℝ := Ioo (g2rP i m - g2rR i m) (g2rP i m + g2rR i m)

theorem g2rg_pos_iff {γ : ℝ} (hγ : 0 < γ) (i : G3Idx) {m : ℝ} (hm : 0 < m) (t : ℝ) :
    0 < g2rg γ i m t ↔ t ∈ g2rJ i m := by
  unfold g2rg g2rφ g2rJ
  rw [mul_pos_iff_of_pos_left (by positivity), g2Phi_pos_iff (g2rR_pos i hm).le,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_lt, mem_Ioo]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- The length as a function of the coefficient. -/
def g2rF (γ : ℝ) (i : G3Idx) (m : ℝ) (y : AdmIdx → ℝ) (x a : ℝ) : ℝ :=
  ∫ t, (Icc 0 x).indicator (fun t => Real.exp (a * g2rg γ i m t)) t ∂(g2rκW γ i m y)

theorem measurable_g2rF (γ : ℝ) (i : G3Idx) (m : ℝ) :
    Measurable fun p : ((AdmIdx → ℝ) × ℝ) × ℝ => g2rF γ i m p.1.1 p.1.2 p.2 := by
  set κ' : Kernel (((AdmIdx → ℝ) × ℝ) × ℝ) ℝ := (g2rκW γ i m).comap (fun p => p.1.1)
    (measurable_fst.comp measurable_fst)
  have hS : MeasurableSet {q : (((AdmIdx → ℝ) × ℝ) × ℝ) × ℝ | q.2 ∈ Icc 0 q.1.1.2} :=
    (measurableSet_le measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd (measurable_snd.comp (measurable_fst.comp measurable_fst)))
  have hf : StronglyMeasurable fun q : (((AdmIdx → ℝ) × ℝ) × ℝ) × ℝ =>
      (Icc 0 q.1.1.2).indicator (fun t => Real.exp (q.1.2 * g2rg γ i m t)) q.2 := by
    have : (fun q : (((AdmIdx → ℝ) × ℝ) × ℝ) × ℝ =>
        (Icc 0 q.1.1.2).indicator (fun t => Real.exp (q.1.2 * g2rg γ i m t)) q.2) =
        {q : (((AdmIdx → ℝ) × ℝ) × ℝ) × ℝ | q.2 ∈ Icc 0 q.1.1.2}.indicator
          (fun q => Real.exp (q.1.2 * g2rg γ i m q.2)) := by
      funext q; simp only [indicator, mem_setOf_eq]
    rw [this]
    exact ((Real.measurable_exp.comp ((measurable_snd.comp measurable_fst).mul
      ((measurable_g2rg γ i m).comp measurable_snd))).indicator hS).stronglyMeasurable
  exact (hf.integral_kernel_prod_right' (κ := κ')).measurable

open Classical in
/-- The good set of `(y, x)`. -/
def g2rGood (γ : ℝ) (i : G3Idx) (m : ℝ) : Set ((AdmIdx → ℝ) × ℝ) :=
  {ξ | g2ν₀ γ (g2rφ i m) ξ.1 (Icc 0 (g2rW i m)) < ⊤ ∧ 0 < g2ν₀ γ (g2rφ i m) ξ.1 (g2rJ i m) ∧
    ξ.2 ≤ g2rW i m ∧ g2rP i m + g2rR i m ≤ ξ.2}

theorem measurableSet_g2rGood (γ : ℝ) (i : G3Idx) (m : ℝ) : MeasurableSet (g2rGood γ i m) := by
  have h1 : Measurable fun ξ : (AdmIdx → ℝ) × ℝ => g2ν₀ γ (g2rφ i m) ξ.1 (Icc 0 (g2rW i m)) :=
    (Measure.measurable_coe (measurableSet_Icc (a := 0) (b := g2rW i m))).comp
    ((measurable_g2ν₀ γ (g2rφ i m)).comp measurable_fst)
  have h2 : Measurable fun ξ : (AdmIdx → ℝ) × ℝ => g2ν₀ γ (g2rφ i m) ξ.1 (g2rJ i m) :=
    (Measure.measurable_coe (measurableSet_Ioo (a := g2rP i m - g2rR i m)
    (b := g2rP i m + g2rR i m))).comp ((measurable_g2ν₀ γ (g2rφ i m)).comp measurable_fst)
  exact (measurableSet_lt h1 measurable_const).inter ((measurableSet_lt measurable_const h2).inter
    ((measurableSet_le measurable_snd measurable_const).inter
      (measurableSet_le measurable_const measurable_snd)))

open Classical in
/-- **The length function** (`a` off the good set). -/
def g2rf (γ : ℝ) (i : G3Idx) (m : ℝ) (ξ : (AdmIdx → ℝ) × ℝ) (a : ℝ) : ℝ :=
  if ξ ∈ g2rGood γ i m then g2rF γ i m ξ.1 ξ.2 a else a

theorem measurable_g2rf (γ : ℝ) (i : G3Idx) (m : ℝ) :
    Measurable (Function.uncurry (g2rf γ i m)) := by
  classical
  refine Measurable.ite ((measurableSet_g2rGood γ i m).preimage measurable_fst)
    (measurable_g2rF γ i m) measurable_snd

theorem g2rκW_apply_good {γ : ℝ} {i : G3Idx} {m : ℝ} {ξ : (AdmIdx → ℝ) × ℝ}
    (hξ : ξ ∈ g2rGood γ i m) :
    g2rκW γ i m ξ.1 = (g2ν₀ γ (g2rφ i m) ξ.1).restrict (Icc 0 (g2rW i m)) := by
  rw [g2rκW, g2FinKer_apply, if_pos hξ.1]

theorem g2rF_eq_good {γ : ℝ} {i : G3Idx} {m : ℝ} {ξ : (AdmIdx → ℝ) × ℝ}
    (hξ : ξ ∈ g2rGood γ i m) (a : ℝ) :
    g2rF γ i m ξ.1 ξ.2 a = ∫ t, Real.exp (a * g2rg γ i m t)
      ∂((g2ν₀ γ (g2rφ i m) ξ.1).restrict (Icc 0 (g2rW i m))).restrict (Icc 0 ξ.2) := by
  rw [g2rF, g2rκW_apply_good hξ, integral_indicator measurableSet_Icc]

theorem g2rf_hasDerivAt {γ : ℝ} (hγ : 0 < γ) (i : G3Idx) {m : ℝ} (hm : 0 < m)
    (ξ : (AdmIdx → ℝ) × ℝ) (a : ℝ) :
    ∃ d, 0 < d ∧ HasDerivAt (g2rf γ i m ξ) d a := by
  by_cases hξ : ξ ∈ g2rGood γ i m
  · set μ := ((g2ν₀ γ (g2rφ i m) ξ.1).restrict (Icc 0 (g2rW i m))).restrict (Icc 0 ξ.2) with hμ
    have : IsFiniteMeasure μ := by
      refine ⟨?_⟩
      rw [hμ, Measure.restrict_apply_univ, Measure.restrict_apply measurableSet_Icc]
      exact (measure_mono inter_subset_right).trans_lt hξ.1
    have hfun : g2rf γ i m ξ = fun b => ∫ t, Real.exp (b * g2rg γ i m t) ∂μ := by
      funext b; simp only [g2rf, if_pos hξ]; exact g2rF_eq_good hξ b
    refine ⟨_, g2bump_deriv_pos (ν := μ) (measurable_g2rg γ i m) (abs_g2rg_le hγ i m)
      (g2rg_nonneg hγ i m) ?_ a, ?_⟩
    · have hJ : g2rJ i m ⊆ Icc 0 (g2rW i m) ∩ Icc 0 ξ.2 := by
        intro t ht
        have h0 := g2r_bump_pos i hm
        have := hξ.2.2.1; have := hξ.2.2.2
        exact ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩
      calc 0 < g2ν₀ γ (g2rφ i m) ξ.1 (g2rJ i m) := hξ.2.1
        _ = μ (g2rJ i m) := by
            have hJm : MeasurableSet (g2rJ i m) := measurableSet_Ioo
            rw [hμ, Measure.restrict_apply hJm,
              Measure.restrict_apply (hJm.inter measurableSet_Icc),
              inter_assoc, inter_comm (Icc 0 ξ.2), inter_eq_left.2 hJ]
        _ ≤ μ {t | 0 < g2rg γ i m t} := measure_mono fun t ht => (g2rg_pos_iff hγ i hm t).2 ht
    · rw [hfun]; exact g2bump_hasDerivAt (measurable_g2rg γ i m) (abs_g2rg_le hγ i m) a
  · refine ⟨1, one_pos, ?_⟩
    have : g2rf γ i m ξ = id := by funext b; simp [g2rf, hξ]
    rw [this]; exact hasDerivAt_id a

theorem g2rf_differentiable {γ : ℝ} (hγ : 0 < γ) (i : G3Idx) {m : ℝ} (hm : 0 < m)
    (ξ : (AdmIdx → ℝ) × ℝ) : Differentiable ℝ (g2rf γ i m ξ) := fun a =>
  let ⟨_, _, h⟩ := g2rf_hasDerivAt hγ i hm ξ a
  h.differentiableAt

theorem g2rf_deriv_pos {γ : ℝ} (hγ : 0 < γ) (i : G3Idx) {m : ℝ} (hm : 0 < m)
    (ξ : (AdmIdx → ℝ) × ℝ) (a : ℝ) : 0 < deriv (g2rf γ i m ξ) a := by
  obtain ⟨d, hd, h⟩ := g2rf_hasDerivAt hγ i hm ξ a
  rw [h.deriv]; exact hd

end Thm18Asm
end QuantumZipper
