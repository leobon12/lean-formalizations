import HigherDimLQGMetric.LGF.BoxInd
import HigherDimLQGMetric.Field.Basic

/-!
# Integration by parts against box indicators (packet F2, target 1, part 3)

The antiderivative field `G(x) = ⟨h, 1_{[0,x]}⟩` of the LGF satisfies
`⟨h, φ⟩ = (−1)^d ∫ G ∂₁⋯∂_d φ`.
The deterministic identity behind it is the iterated fundamental theorem of calculus

  `∫ ∂₁⋯∂_d φ(x) 1_{[0,x]}(u) dx = (−1)^d φ(u)`   (`integral_iteratedFDeriv_mul_boxIndF_rd`)

for smooth compactly supported `φ` on `ℝ^d` (`1_{[0,x]} = boxIndF x`, the oriented box indicator).
Port of LQGMetric's `Field/ExistFTC.lean` (`integral_d12_mul_rectInd`, two coordinates in `ℂ`) to
`d` coordinates, by induction on the dimension with the volume-preserving splitting
`(Fin (n+1) → ℝ) ≃ ℝ × (Fin n → ℝ)` (Mathlib `measurePreserving_piFinSuccAbove`):

* `integral_deriv_mul_sgnInd`: one-dimensional FTC, `∫ ψ'(t) sgnInd t a dt = −ψ(a)`;
* `hasDerivAt_iteratedFDeriv_cons`, `iteratedFDeriv_comp_cons`: the chain rule along a coordinate
  line and along a coordinate hyperplane;
* `integral_iteratedFDeriv_mul_boxIndF`: the identity on `Fin n → ℝ`, with
  `∂₁⋯∂ₙ f = iteratedFDeriv ℝ n f · (eᵢ)ᵢ`;
* `iteratedLineDerivOp_apply`: Mathlib's iterated line derivative `∂^{m}` of test functions is
  `iteratedFDeriv` applied to `m`;
* `integral_iteratedFDeriv_mul_boxIndF_rd`: the identity on `ℝ^d = EuclideanSpace ℝ (Fin d)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-! ## One dimension -/

/-- **One-dimensional FTC against `sgnInd`**: `∫ ψ'(t) sgnInd t a dt = −ψ(a)` for compactly
supported `ψ` with integrable derivative `ψ'`. -/
theorem integral_deriv_mul_sgnInd {ψ ψ' : ℝ → ℝ} (hd : ∀ t, HasDerivAt ψ (ψ' t) t)
    (hψ' : Integrable ψ') (hψ : HasCompactSupport ψ) (a : ℝ) :
    ∫ t, ψ' t * sgnInd t a = -ψ a := by
  have htop : Tendsto ψ atTop (𝓝 0) := hψ.is_zero_at_infty.mono_left atTop_le_cocompact
  have hbot : Tendsto ψ atBot (𝓝 0) := hψ.is_zero_at_infty.mono_left atBot_le_cocompact
  have h0 : ∫ t, ψ' t = 0 := by
    rw [integral_of_hasDerivAt_of_tendsto hd hψ' hbot htop, sub_self]
  have hIoi : ∫ t in Ioi a, ψ' t = -ψ a := by
    rw [integral_Ioi_of_hasDerivAt_of_tendsto (hd a).continuousAt.continuousWithinAt
      (fun x _ => hd x) hψ'.integrableOn htop, zero_sub]
  have e : ∀ t, ψ' t * sgnInd t a = (Ici a).indicator ψ' t - (Iic 0).indicator 1 a * ψ' t := by
    intro t
    simp only [sgnInd, indicator, mem_Iic, mem_Ici, Pi.one_apply]
    split_ifs <;> ring
  simp_rw [e]
  rw [integral_sub ((integrable_indicator_iff measurableSet_Ici).2 hψ'.integrableOn)
    (hψ'.const_mul _), integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi, hIoi,
    integral_const_mul, h0, mul_zero, sub_zero]

/-! ## Calculus along coordinate lines and hyperplanes -/

/-- The embedding `y ↦ (0, y)` of `Fin k → ℝ` into `Fin (k+1) → ℝ` as a continuous linear map. -/
def consCLM (k : ℕ) : (Fin k → ℝ) →L[ℝ] (Fin (k + 1) → ℝ) :=
  ContinuousLinearMap.pi fun i =>
    Fin.cases (motive := fun _ => (Fin k → ℝ) →L[ℝ] ℝ) 0 (fun j => ContinuousLinearMap.proj j) i

theorem consCLM_apply {k : ℕ} (y : Fin k → ℝ) : consCLM k y = Fin.cons 0 y := by
  funext i
  cases i using Fin.cases with
  | zero => simp [consCLM]
  | succ j => simp [consCLM]

theorem cons_eq_consCLM_add {k : ℕ} (a : ℝ) (y : Fin k → ℝ) :
    (Fin.cons a y : Fin (k + 1) → ℝ) = consCLM k y + Fin.cons a 0 := by
  rw [consCLM_apply]
  funext i
  cases i using Fin.cases with
  | zero => simp
  | succ j => simp

theorem consCLM_single {k : ℕ} (i : Fin k) :
    consCLM k (Pi.single i 1) = (Pi.single i.succ 1 : Fin (k + 1) → ℝ) := by
  rw [consCLM_apply]
  funext j
  cases j using Fin.cases with
  | zero => simp
  | succ j => simp [Pi.single_apply]

/-- Chain rule along a coordinate hyperplane: the derivatives of `y ↦ f(a, y)` are those of `f` in
the directions `(0, w)`. -/
theorem iteratedFDeriv_comp_cons {k : ℕ} {f : (Fin (k + 1) → ℝ) → ℝ}
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (a : ℝ) (y : Fin k → ℝ) (w : Fin k → Fin k → ℝ) :
    iteratedFDeriv ℝ k (fun y' => f (Fin.cons a y')) y w =
      iteratedFDeriv ℝ k f (Fin.cons a y) fun i => consCLM k (w i) := by
  have e : (fun y' => f (Fin.cons a y')) = (fun z => f (z + Fin.cons a 0)) ∘ consCLM k := by
    funext y'
    simp only [Function.comp_apply, ← cons_eq_consCLM_add]
  have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun z => f (z + Fin.cons a 0) :=
    hf.comp (contDiff_id.add contDiff_const)
  rw [e, ContinuousLinearMap.iteratedFDeriv_comp_right (consCLM k) hg y
    (by exact_mod_cast le_top), iteratedFDeriv_comp_add_right, ← cons_eq_consCLM_add]
  rfl

/-- Chain rule along a coordinate line: `s ↦ D^k f(s, y)[w]` has derivative
`D^{k+1} f(t, y)[e₀, w]`. -/
theorem hasDerivAt_iteratedFDeriv_cons {k : ℕ} {f : (Fin (k + 1) → ℝ) → ℝ}
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (y : Fin k → ℝ)
    (w : Fin k → Fin (k + 1) → ℝ) (t : ℝ) :
    HasDerivAt (fun s => iteratedFDeriv ℝ k f (Fin.cons s y) w)
      (iteratedFDeriv ℝ (k + 1) f (Fin.cons t y) (Fin.cons (Pi.single 0 1) w)) t := by
  have hγ : HasDerivAt (fun s : ℝ => (Fin.cons s y : Fin (k + 1) → ℝ))
      (Pi.single 0 1 : Fin (k + 1) → ℝ) t := by
    rw [hasDerivAt_pi]
    intro i
    cases i using Fin.cases with
    | zero =>
      simp only [Fin.cons_zero, Pi.single_eq_same]
      convert hasDerivAt_id' t using 1
    | succ j =>
      simp only [Fin.cons_succ]
      convert hasDerivAt_const t (y j) using 1
      simp
  have hD : Differentiable ℝ (iteratedFDeriv ℝ k f) :=
    hf.differentiable_iteratedFDeriv (by exact_mod_cast ENat.natCast_lt_top k)
  have h1 := (hD (Fin.cons t y)).hasFDerivAt.comp_hasDerivAt t hγ
  have h2 := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Fin (k + 1) → ℝ) ℝ w).hasFDerivAt
    |>.comp_hasDerivAt t h1
  rw [iteratedFDeriv_succ_apply_left, Fin.cons_zero, Fin.tail_cons]
  exact h2

/-! ## The iterated FTC on `Fin n → ℝ` -/

/-- A function on `Fin n → ℝ` with compact support vanishes outside a sup-norm ball. -/
theorem exists_eq_zero_of_norm_gt {n : ℕ} {E : Type*} [NormedAddCommGroup E] {f : (Fin n → ℝ) → E}
    (hf : HasCompactSupport f) : ∃ ρ : ℝ, ∀ x, ρ < ‖x‖ → f x = 0 := by
  obtain ⟨ρ, hρ⟩ := hf.isCompact.isBounded.subset_closedBall 0
  refine ⟨ρ, fun x hx => image_eq_zero_of_notMem_tsupport fun h => ?_⟩
  have := hρ h
  rw [Metric.mem_closedBall, dist_zero_right] at this
  exact absurd hx (not_lt.2 this)

theorem norm_le_norm_cons {k : ℕ} (a : ℝ) (y : Fin k → ℝ) :
    ‖y‖ ≤ ‖(Fin.cons a y : Fin (k + 1) → ℝ)‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_
  have h := norm_le_pi_norm (Fin.cons a y : Fin (k + 1) → ℝ) j.succ
  simpa only [Fin.cons_succ] using h

theorem abs_le_norm_cons {k : ℕ} (a : ℝ) (y : Fin k → ℝ) :
    |a| ≤ ‖(Fin.cons a y : Fin (k + 1) → ℝ)‖ := by
  have h := norm_le_pi_norm (Fin.cons a y : Fin (k + 1) → ℝ) 0
  simpa only [Fin.cons_zero, Real.norm_eq_abs] using h

theorem hasCompactSupport_comp_cons {k : ℕ} {f : (Fin (k + 1) → ℝ) → ℝ}
    (hf : HasCompactSupport f) (a : ℝ) :
    HasCompactSupport fun y : Fin k → ℝ => f (Fin.cons a y) := by
  obtain ⟨ρ, hρ⟩ := exists_eq_zero_of_norm_gt hf
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Fin k → ℝ) ρ) fun y hy => hρ _ ?_
  rw [Metric.mem_closedBall, dist_zero_right, not_le] at hy
  exact hy.trans_le (norm_le_norm_cons a y)

/-- The standard basis of `Fin n → ℝ`. -/
abbrev stdBasis (n : ℕ) : Fin n → Fin n → ℝ := fun i => Pi.single i 1

theorem cons_single_stdBasis (k : ℕ) :
    (Fin.cons (Pi.single 0 1 : Fin (k + 1) → ℝ) fun i : Fin k => consCLM k (stdBasis k i)) =
      stdBasis (k + 1) := by
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ j => simp only [Fin.cons_succ, stdBasis, consCLM_single]

theorem continuous_iteratedFDeriv_apply {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (k : ℕ) (w : Fin k → Fin n → ℝ) :
    Continuous fun x => iteratedFDeriv ℝ k f x w :=
  (continuous_eval_const w).comp (hf.continuous_iteratedFDeriv (by exact_mod_cast le_top))

theorem hasCompactSupport_iteratedFDeriv_apply {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : HasCompactSupport f) (k : ℕ) (w : Fin k → Fin n → ℝ) :
    HasCompactSupport fun x => iteratedFDeriv ℝ k f x w :=
  (hf.iteratedFDeriv k).comp_left (g := fun L : ContinuousMultilinearMap ℝ (fun _ : Fin k =>
    Fin n → ℝ) ℝ => L w) (by simp)

theorem integrable_iteratedFDeriv_mul_boxIndF {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (hfc : HasCompactSupport f) (k : ℕ)
    (w : Fin k → Fin n → ℝ) (u : Fin n → ℝ) :
    Integrable fun x => iteratedFDeriv ℝ k f x w * boxIndF x u :=
  ((continuous_iteratedFDeriv_apply hf k w).integrable_of_hasCompactSupport
    (hasCompactSupport_iteratedFDeriv_apply hfc k w)).mul_bdd
    (measurable_boxIndF_left u).aestronglyMeasurable
    (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]
      exact abs_boxIndF_le_one x u)

theorem exists_iteratedFDeriv_eq_zero {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : HasCompactSupport f) :
    ∃ ρ : ℝ, ∀ (j : ℕ) (x : Fin n → ℝ), ρ < ‖x‖ → iteratedFDeriv ℝ j f x = 0 := by
  obtain ⟨ρ, hρ⟩ := hf.isCompact.isBounded.subset_closedBall 0
  refine ⟨ρ, fun j x hx => image_eq_zero_of_notMem_tsupport fun h => ?_⟩
  have := hρ (tsupport_iteratedFDeriv_subset j h)
  rw [Metric.mem_closedBall, dist_zero_right] at this
  exact absurd hx (not_lt.2 this)

theorem hasCompactSupport_iteratedFDeriv_cons {k : ℕ} {f : (Fin (k + 1) → ℝ) → ℝ}
    (hf : HasCompactSupport f) (j : ℕ) (y : Fin k → ℝ) (w : Fin j → Fin (k + 1) → ℝ) :
    HasCompactSupport fun t : ℝ => iteratedFDeriv ℝ j f (Fin.cons t y) w := by
  obtain ⟨ρ, hρ⟩ := exists_iteratedFDeriv_eq_zero hf
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) ρ) fun t ht => ?_
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, not_le] at ht
  rw [hρ j _ (ht.trans_le (abs_le_norm_cons t y))]
  rfl

theorem continuous_iteratedFDeriv_cons {k : ℕ} {f : (Fin (k + 1) → ℝ) → ℝ}
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (j : ℕ) (y : Fin k → ℝ)
    (w : Fin j → Fin (k + 1) → ℝ) :
    Continuous fun t : ℝ => iteratedFDeriv ℝ j f (Fin.cons t y) w := by
  have hγ : Continuous fun t : ℝ => (Fin.cons t y : Fin (k + 1) → ℝ) := by
    refine continuous_pi fun i => ?_
    cases i using Fin.cases with
    | zero => simpa using continuous_id'
    | succ i => simpa using continuous_const
  exact (continuous_iteratedFDeriv_apply hf j w).comp hγ

theorem boxIndF_cons {k : ℕ} (t : ℝ) (y : Fin k → ℝ) (u : Fin (k + 1) → ℝ) :
    boxIndF (Fin.cons t y) u = sgnInd t (u 0) * boxIndF y (Fin.tail u) := by
  simp only [boxIndF, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.tail]

/-- **Iterated FTC against box indicators** on `Fin n → ℝ`:
`∫ ∂₁⋯∂ₙ f(x) boxIndF x u dx = (−1)^n f(u)`. -/
theorem integral_iteratedFDeriv_mul_boxIndF : ∀ (n : ℕ) (f : (Fin n → ℝ) → ℝ),
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f → HasCompactSupport f → ∀ u : Fin n → ℝ,
    ∫ x, iteratedFDeriv ℝ n f x (stdBasis n) * boxIndF x u = (-1) ^ n * f u := by
  intro n
  induction n with
  | zero =>
    intro f _ _ u
    have hv : (volume : Measure (Fin 0 → ℝ)) univ = 1 := by
      rw [volume_pi, Measure.pi_univ]
      simp
    simp only [iteratedFDeriv_zero_apply, boxIndF, Finset.univ_eq_empty, Finset.prod_empty,
      mul_one, pow_zero, one_mul]
    rw [integral_unique, Measure.real, hv, ENNReal.toReal_one, one_smul]
    congr 1
    exact Subsingleton.elim _ _
  | succ k ih =>
    intro f hf hfc u
    have hint := integrable_iteratedFDeriv_mul_boxIndF hf hfc (k + 1) (stdBasis (k + 1)) u
    set F : (Fin (k + 1) → ℝ) → ℝ := fun x => iteratedFDeriv ℝ (k + 1) f x (stdBasis (k + 1)) *
      boxIndF x u with hF
    have hmp := (measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => (volume : Measure ℝ))
      0).symm
    have hsymm : ∀ p : ℝ × (Fin k → ℝ),
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) 0).symm p =
          Fin.cons p.1 p.2 := by
      intro p
      rw [MeasurableEquiv.piFinSuccAbove_symm_apply]
      exact Fin.insertNth_zero' p.1 p.2
    have h1 : ∫ x, F x = ∫ p : ℝ × (Fin k → ℝ), F (Fin.cons p.1 p.2) := by
      rw [volume_pi, ← hmp.integral_comp' F]
      simp only [hsymm]
      rfl
    have h2 : Integrable fun p : ℝ × (Fin k → ℝ) => F (Fin.cons p.1 p.2) := by
      have := (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _) (g := F)).2
        (by rw [← volume_pi]; exact hint)
      simp only [Function.comp_def, hsymm] at this
      exact this
    -- the slice functions
    set g : (Fin k → ℝ) → ℝ := fun y' => f (Fin.cons (u 0) y') with hg
    have hgs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g := by
      have : g = f ∘ fun y' => consCLM k y' + Fin.cons (u 0) 0 := by
        funext y'
        simp only [hg, Function.comp_apply, ← cons_eq_consCLM_add]
      rw [this]
      exact hf.comp ((consCLM k).contDiff.add contDiff_const)
    have hgc : HasCompactSupport g := hasCompactSupport_comp_cons hfc (u 0)
    have h4 : ∀ y : Fin k → ℝ, ∫ t, F (Fin.cons t y) =
        boxIndF y (Fin.tail u) * -iteratedFDeriv ℝ k g y (stdBasis k) := by
      intro y
      set ψ : ℝ → ℝ := fun s => iteratedFDeriv ℝ k f (Fin.cons s y)
        (fun i => consCLM k (stdBasis k i)) with hψ
      set ψ' : ℝ → ℝ := fun s => iteratedFDeriv ℝ (k + 1) f (Fin.cons s y) (stdBasis (k + 1))
        with hψ'
      have hder : ∀ t, HasDerivAt ψ (ψ' t) t := fun t => by
        have := hasDerivAt_iteratedFDeriv_cons hf y (fun i => consCLM k (stdBasis k i)) t
        rw [cons_single_stdBasis] at this
        exact this
      have hψ'i : Integrable ψ' :=
        (continuous_iteratedFDeriv_cons hf (k + 1) y _).integrable_of_hasCompactSupport
          (hasCompactSupport_iteratedFDeriv_cons hfc (k + 1) y _)
      have hψc : HasCompactSupport ψ := hasCompactSupport_iteratedFDeriv_cons hfc k y _
      have e : (fun t => F (Fin.cons t y)) =
          fun t => boxIndF y (Fin.tail u) * (ψ' t * sgnInd t (u 0)) := by
        funext t
        simp only [hF, hψ', boxIndF_cons]
        ring
      rw [e, integral_const_mul, integral_deriv_mul_sgnInd hder hψ'i hψc (u 0)]
      congr 2
      rw [hψ, iteratedFDeriv_comp_cons hf]
    rw [h1, Measure.volume_eq_prod,
      integral_prod_symm _ (by rw [← Measure.volume_eq_prod]; exact h2)]
    simp only
    simp_rw [h4]
    have hih := ih g hgs hgc (Fin.tail u)
    have e2 : (fun y => boxIndF y (Fin.tail u) * -iteratedFDeriv ℝ k g y (stdBasis k)) =
        fun y => -(iteratedFDeriv ℝ k g y (stdBasis k) * boxIndF y (Fin.tail u)) := by
      funext y; ring
    rw [e2, integral_neg, hih, hg]
    simp only [Fin.cons_self_tail]
    ring

/-! ## Test functions on `ℝ^d` -/

variable {d : ℕ}

/-- Mathlib's iterated line derivative `∂^{m}` of a test function is the iterated Fréchet derivative
applied to `m`. -/
theorem iteratedLineDerivOp_apply : ∀ (k : ℕ) (m : Fin k → Rd d) (φ : TestRd d) (x : Rd d),
    (LineDeriv.iteratedLineDerivOp m φ : TestRd d) x = iteratedFDeriv ℝ k (φ : Rd d → ℝ) x m := by
  intro k
  induction k with
  | zero =>
    intro m φ x
    rw [LineDeriv.iteratedLineDerivOp_fin_zero, iteratedFDeriv_zero_apply]
  | succ k ih =>
    intro m φ x
    rw [LineDeriv.iteratedLineDerivOp_succ_left, TestFunction.lineDerivOp_eq_lineDerivCLM ℝ,
      TestFunction.lineDerivCLM_apply, ite_eq_left le_top]
    set ψ : TestRd d := LineDeriv.iteratedLineDerivOp (Fin.tail m) φ with hψdef
    have hψ : (ψ : Rd d → ℝ) = fun y => iteratedFDeriv ℝ k (φ : Rd d → ℝ) y (Fin.tail m) :=
      funext (ih (Fin.tail m) φ)
    have hψd : DifferentiableAt ℝ (ψ : Rd d → ℝ) x :=
      (ψ.contDiff.differentiable (by simp)).differentiableAt
    rw [hψd.lineDeriv_eq_fderiv, hψ, fderiv_continuousMultilinear_apply_const_apply
      ((φ.contDiff.differentiable_iteratedFDeriv (by exact_mod_cast ENat.natCast_lt_top k))
        x) (Fin.tail m) (m 0), iteratedFDeriv_succ_apply_left]

/-- The standard basis of `ℝ^d`. -/
abbrev rdBasis (d : ℕ) : Fin d → Rd d := fun i => EuclideanSpace.single i (1 : ℝ)

/-- `∂₁ ⋯ ∂_d` on test functions (Mathlib's `iteratedLineDerivOpCLM` along the standard basis). -/
def boxDeriv (d : ℕ) : TestRd d →L[ℝ] TestRd d :=
  LineDeriv.iteratedLineDerivOpCLM ℝ (TestRd d) (rdBasis d)

theorem boxDeriv_apply (φ : TestRd d) (x : Rd d) :
    boxDeriv d φ x = iteratedFDeriv ℝ d (φ : Rd d → ℝ) x (rdBasis d) := by
  rw [boxDeriv, LineDeriv.iteratedLineDerivOpCLM_apply, iteratedLineDerivOp_apply]

/-- **Iterated FTC against box indicators on `ℝ^d`**:
`∫ ∂₁⋯∂_d φ(x) boxIndF x u dx = (−1)^d φ(u)` for smooth compactly supported `φ`. -/
theorem integral_iteratedFDeriv_mul_boxIndF_rd {φ : Rd d → ℝ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (hφc : HasCompactSupport φ) (u : Rd d) :
    ∫ x : Rd d, iteratedFDeriv ℝ d φ x (rdBasis d) * boxIndF x.ofLp u.ofLp = (-1) ^ d * φ u := by
  set e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ) with he
  set L : (Fin d → ℝ) →L[ℝ] Rd d := e.symm.toContinuousLinearMap with hL
  have hLq : ∀ q, L q = WithLp.toLp 2 q := fun q => rfl
  set f : (Fin d → ℝ) → ℝ := φ ∘ L with hfdef
  have hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f := hφ.comp L.contDiff
  have hfc : HasCompactSupport f := hφc.comp_homeomorph e.symm.toHomeomorph
  have hD : ∀ q : Fin d → ℝ, iteratedFDeriv ℝ d f q (stdBasis d) =
      iteratedFDeriv ℝ d φ (WithLp.toLp 2 q) (rdBasis d) := by
    intro q
    rw [hfdef, ContinuousLinearMap.iteratedFDeriv_comp_right L hφ q (by exact_mod_cast le_top)]
    rfl
  have hmp := PiLp.volume_preserving_toLp (Fin d)
  rw [← hmp.integral_comp (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurableEmbedding]
  have e2 : (fun q : Fin d → ℝ => iteratedFDeriv ℝ d φ (WithLp.toLp 2 q) (rdBasis d) *
      boxIndF (WithLp.toLp 2 q).ofLp u.ofLp) =
      fun q => iteratedFDeriv ℝ d f q (stdBasis d) * boxIndF q u.ofLp := by
    funext q
    rw [hD, WithLp.ofLp_toLp]
  rw [e2, integral_iteratedFDeriv_mul_boxIndF d f hf hfc u.ofLp, hfdef, Function.comp_apply,
    hLq, WithLp.toLp_ofLp]

/-- The FTC for test functions: `∫ ∂₁⋯∂_d φ(x) boxIndF x u dx = (−1)^d φ(u)`. -/
theorem integral_boxDeriv_mul_boxIndF (φ : TestRd d) (u : Rd d) :
    ∫ x : Rd d, boxDeriv d φ x * boxIndF x.ofLp u.ofLp = (-1) ^ d * φ u := by
  simp_rw [boxDeriv_apply]
  exact integral_iteratedFDeriv_mul_boxIndF_rd φ.contDiff φ.hasCompactSupport u

end HigherDimLQGMetric
