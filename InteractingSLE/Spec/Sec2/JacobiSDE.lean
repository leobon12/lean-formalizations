/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import Mathlib.Probability.Martingale.Basic
import InteractingSLE.Spec.Sec2.JacobiMoments

/-!
# The Jacobi diffusion in a filtration, and the algebra of compensated processes

Packet PROVE-SEC2-JAC3. The Jacobi diffusion of the proof of Theorem 2.2 (Specification p. 22,
`source/spec/p001-048.md` L498–L500) is a weak solution of
`dU = √((κ/2) U (1 - U)) dβ + ½ {a (1 - U) - b U} du`. In martingale-problem form (the form in
which the specification uses it: the two-sided process on the logarithmic clock `u ∈ ℝ`):

* `IsJacobiDiffusion κ a b P 𝓗 U`: `U` is `[0, 1]`-valued with continuous paths, adapted to the
  filtration `𝓗` indexed by `ℝ`, and for every monomial `f = x^n` and `w ≤ v`,
  `E[f(U_v) - f(U_w) - ∫_w^v L f(U_x) dx | 𝓗_w] = 0`, `L = Jacobi.gen κ a b`.

Every such process satisfies the landed polynomial martingale problem `IsJacobiMP`
(`IsJacobiDiffusion.isJacobiMP`), hence it is stationary with the beta law (`moment_eq`).

The second half is generic: `HasCompensator P 𝓗 X α` says that `X_x - X_r - ∫_r^x α` is orthogonal
to every bounded `𝓗_r`-measurable variable. Two closure properties are proved:

* `HasCompensator.mul_left`: multiplication by a deterministic `C¹` function `g`
  (`g X` is compensated by `g' X + g α`);
* `HasCompensator.sq_sub`: if `X` is compensated by `α` and `X²` by `γ`, then the squared
  martingale part `(X_x - X_w - ∫_w^x α)²` is compensated by `γ - 2 X α` (the quadratic variation),
  by an exact pathwise identity and Fubini (no stochastic integral is needed).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real

namespace InteractingSLE

namespace Sec2

namespace Jacobi

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **The Jacobi diffusion in the filtration `𝓗`** (indexed by the logarithmic clock `u ∈ ℝ`), in
martingale-problem form: values in `[0, 1]`, continuous paths, `𝓗`-adapted, and for every `n` and
`w ≤ v` the conditional expectation given `𝓗_w` of `U_v^n - U_w^n - ∫_w^v L(x^n)(U_x) dx`
vanishes, where `L f = (κ/4) x (1 - x) f'' + ½ (a (1 - x) - b x) f'`. -/
def IsJacobiDiffusion (κ a b : ℝ) (P : Measure Ω) (𝓗 : Filtration ℝ mΩ) (U : ℝ → Ω → ℝ) : Prop :=
  (∀ u ω, U u ω ∈ Icc (0 : ℝ) 1) ∧ (∀ ω, Continuous fun u => U u ω) ∧
    (∀ u, Measurable[𝓗 u] (U u)) ∧
    ∀ (n : ℕ) (w v : ℝ), w ≤ v →
      P[fun ω => U v ω ^ n - U w ω ^ n - ∫ x in w..v, gen κ a b (fun y => y ^ n) (U x ω) | 𝓗 w]
        =ᵐ[P] 0

/-- A process with continuous paths, measurable values, and bounded on bounded time sets uniformly
in `ω`. -/
def IsRegProc {Ω : Type*} [MeasurableSpace Ω] (X : ℝ → Ω → ℝ) : Prop :=
  (∀ ω, Continuous fun u => X u ω) ∧ (∀ u, Measurable (X u)) ∧
    ∀ T : ℝ, ∃ C, ∀ u ω, |u| ≤ T → |X u ω| ≤ C

/-- `X - ∫ α` has `𝓗`-martingale increments: `X_x - X_r - ∫_r^x α` is orthogonal to every bounded
`𝓗_r`-measurable variable. -/
def HasCompensator (P : Measure Ω) (𝓗 : Filtration ℝ mΩ) (X α : ℝ → Ω → ℝ) : Prop :=
  ∀ r x : ℝ, r ≤ x → ∀ Z : Ω → ℝ, StronglyMeasurable[𝓗 r] Z → (∃ C, ∀ ω, |Z ω| ≤ C) →
    ∫ ω, Z ω * (X x ω - X r ω - ∫ s in r..x, α s ω) ∂P = 0

/-! ### Regular processes -/

section Reg

variable {X Y : ℝ → Ω → ℝ}

theorem IsRegProc.continuous (hX : IsRegProc X) (ω : Ω) : Continuous fun u => X u ω := hX.1 ω

theorem IsRegProc.measurable (hX : IsRegProc X) (u : ℝ) : Measurable (X u) := hX.2.1 u

theorem IsRegProc.exists_bound (hX : IsRegProc X) (T : ℝ) : ∃ C, ∀ u ω, |u| ≤ T → |X u ω| ≤ C :=
  hX.2.2 T

theorem IsRegProc.measurable_uncurry (hX : IsRegProc X) :
    Measurable (Function.uncurry fun (u : ℝ) (ω : Ω) => X u ω) :=
  measurable_uncurry_of_continuous_of_measurable (fun ω => hX.continuous ω) hX.measurable

theorem IsRegProc.add (hX : IsRegProc X) (hY : IsRegProc Y) :
    IsRegProc fun u ω => X u ω + Y u ω := by
  refine ⟨fun ω => (hX.continuous ω).add (hY.continuous ω),
    fun u => (hX.measurable u).add (hY.measurable u), fun T => ?_⟩
  obtain ⟨C₁, h₁⟩ := hX.exists_bound T
  obtain ⟨C₂, h₂⟩ := hY.exists_bound T
  exact ⟨C₁ + C₂, fun u ω hu => (abs_add_le _ _).trans (add_le_add (h₁ u ω hu) (h₂ u ω hu))⟩

theorem IsRegProc.mul (hX : IsRegProc X) (hY : IsRegProc Y) :
    IsRegProc fun u ω => X u ω * Y u ω := by
  refine ⟨fun ω => (hX.continuous ω).mul (hY.continuous ω),
    fun u => (hX.measurable u).mul (hY.measurable u), fun T => ?_⟩
  obtain ⟨C₁, h₁⟩ := hX.exists_bound T
  obtain ⟨C₂, h₂⟩ := hY.exists_bound T
  refine ⟨C₁ * C₂, fun u ω hu => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (h₁ u ω hu) (h₂ u ω hu) (abs_nonneg _) ((abs_nonneg _).trans (h₁ u ω hu))

theorem IsRegProc.const_mul (hX : IsRegProc X) {g : ℝ → ℝ} (hg : Continuous g) :
    IsRegProc fun u ω => g u * X u ω := by
  refine IsRegProc.mul ⟨fun _ => hg, fun _ => measurable_const, fun T => ?_⟩ hX
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -T) (b := T)).exists_bound_of_continuousOn
    hg.continuousOn
  exact ⟨C, fun u _ hu => by simpa [Real.norm_eq_abs] using hC u (abs_le.1 hu)⟩

theorem IsRegProc.sub (hX : IsRegProc X) (hY : IsRegProc Y) :
    IsRegProc fun u ω => X u ω - Y u ω := by
  have h := hX.add (hY.const_mul (g := fun _ => -1) continuous_const)
  simp only [neg_one_mul, ← sub_eq_add_neg] at h
  exact h

theorem IsRegProc.comp {f : ℝ → ℝ} (hf : Continuous f) (hX : IsRegProc X) :
    IsRegProc fun u ω => f (X u ω) := by
  refine ⟨fun ω => hf.comp (hX.continuous ω), fun u => hf.measurable.comp (hX.measurable u),
    fun T => ?_⟩
  obtain ⟨C, hC⟩ := hX.exists_bound T
  obtain ⟨D, hD⟩ := (isCompact_Icc (a := -C) (b := C)).exists_bound_of_continuousOn
    hf.continuousOn
  exact ⟨D, fun u ω hu => by simpa [Real.norm_eq_abs] using hD _ (abs_le.1 (hC u ω hu))⟩

/-- The `T`-bound of a regular process, as an explicit function. -/
theorem IsRegProc.bound_of_le (hX : IsRegProc X) {r x : ℝ} :
    ∃ C, ∀ s ∈ uIcc r x, ∀ ω, |X s ω| ≤ C := by
  obtain ⟨C, hC⟩ := hX.exists_bound (|r| + |x|)
  refine ⟨C, fun s hs ω => hC s ω ?_⟩
  rcases uIcc_subset_Icc (left_mem_uIcc (a := r) (b := x)) right_mem_uIcc hs with ⟨h1, h2⟩
  rw [abs_le]
  constructor <;>
  · cases le_total r x <;>
    · simp_all only [min_def, max_def]
      split_ifs at h1 h2 <;> linarith [abs_nonneg r, abs_nonneg x, neg_abs_le r, neg_abs_le x,
        le_abs_self r, le_abs_self x]

theorem IsRegProc.intervalIntegrable (hX : IsRegProc X) (ω : Ω) (r x : ℝ) :
    IntervalIntegrable (fun s => X s ω) volume r x :=
  (hX.continuous ω).intervalIntegrable r x

/-- The time integral of a regular process is measurable in `ω`. -/
theorem IsRegProc.measurable_intervalIntegral (hX : IsRegProc X) (r x : ℝ) :
    Measurable fun ω => ∫ s in r..x, X s ω := by
  have hm : StronglyMeasurable (Function.uncurry fun (ω : Ω) (s : ℝ) => X s ω) :=
    (hX.measurable_uncurry.comp measurable_swap).stronglyMeasurable
  have h1 := (hm.integral_prod_right (ν := volume.restrict (Ioc r x))).measurable
  have h2 := (hm.integral_prod_right (ν := volume.restrict (Ioc x r))).measurable
  exact h1.sub h2

/-- Fubini for a bounded measurable variable times the time integral of a regular process. -/
theorem IsRegProc.integral_mul_intervalIntegral {P : Measure Ω} [IsFiniteMeasure P]
    (hX : IsRegProc X) {Z : Ω → ℝ} (hZ : Measurable Z) {C : ℝ} (hZC : ∀ ω, |Z ω| ≤ C) (r x : ℝ) :
    ∫ ω, Z ω * (∫ s in r..x, X s ω) ∂P = ∫ s in r..x, ∫ ω, Z ω * X s ω ∂P := by
  obtain ⟨D, hD⟩ := hX.bound_of_le (r := r) (x := x)
  have : IsFiniteMeasure (volume.restrict (uIoc r x)) := isFiniteMeasure_restrict.2 (by simp)
  have hmeas : Measurable (Function.uncurry fun (s : ℝ) (ω : Ω) => Z ω * X s ω) :=
    (hZ.comp measurable_snd).mul hX.measurable_uncurry
  have hmem : ∀ᵐ p ∂(volume.restrict (uIoc r x)).prod P, p.1 ∈ uIoc r x :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_uIoc)
  have hint : Integrable (Function.uncurry fun (s : ℝ) (ω : Ω) => Z ω * X s ω)
      ((volume.restrict (uIoc r x)).prod P) := by
    refine Integrable.of_bound hmeas.aestronglyMeasurable (C * D) ?_
    filter_upwards [hmem] with p hp
    rw [Real.norm_eq_abs, Function.uncurry_apply_pair, abs_mul]
    exact mul_le_mul (hZC p.2) (hD p.1 (uIoc_subset_uIcc hp) p.2) (abs_nonneg _)
      ((abs_nonneg _).trans (hZC p.2))
  rw [intervalIntegral_integral_swap hint]
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  simp only
  exact (intervalIntegral.integral_const_mul _ _).symm

theorem IsRegProc.integrable_mul {P : Measure Ω} [IsFiniteMeasure P] (hX : IsRegProc X)
    {Z : Ω → ℝ} (hZ : Measurable Z) {C : ℝ} (hZC : ∀ ω, |Z ω| ≤ C) (u : ℝ) :
    Integrable (fun ω => Z ω * X u ω) P := by
  obtain ⟨D, hD⟩ := hX.exists_bound |u|
  refine Integrable.of_bound (hZ.mul (hX.measurable u)).aestronglyMeasurable (C * D)
    (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (hZC ω) (hD u ω le_rfl) (abs_nonneg _) ((abs_nonneg _).trans (hZC ω))

theorem IsRegProc.integrable_mul_intervalIntegral {P : Measure Ω} [IsFiniteMeasure P]
    (hX : IsRegProc X) {Z : Ω → ℝ} (hZ : Measurable Z) {C : ℝ} (hZC : ∀ ω, |Z ω| ≤ C)
    (r x : ℝ) : Integrable (fun ω => Z ω * ∫ s in r..x, X s ω) P := by
  obtain ⟨D, hD⟩ := hX.bound_of_le (r := r) (x := x)
  refine Integrable.of_bound (hZ.mul (hX.measurable_intervalIntegral r x)).aestronglyMeasurable
    (C * (D * |x - r|)) (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  refine mul_le_mul (hZC ω) ?_ (abs_nonneg _) ((abs_nonneg _).trans (hZC ω))
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := r) (b := x)
    (f := fun s => X s ω) (C := D) fun s hs => by
      rw [Real.norm_eq_abs]; exact hD s (uIoc_subset_uIcc hs) ω
  simpa [Real.norm_eq_abs] using this

/-- `u ↦ E[Z X_u]` is continuous. -/
theorem IsRegProc.continuous_integral_mul {P : Measure Ω} [IsFiniteMeasure P]
    (hX : IsRegProc X) {Z : Ω → ℝ} (hZ : Measurable Z) {C : ℝ} (hZC : ∀ ω, |Z ω| ≤ C) :
    Continuous fun u => ∫ ω, Z ω * X u ω ∂P := by
  refine continuous_iff_continuousAt.2 fun u₀ => ?_
  obtain ⟨D, hD⟩ := hX.exists_bound (|u₀| + 1)
  refine continuousAt_of_dominated (bound := fun _ => C * D)
    (Eventually.of_forall fun u => (hZ.mul (hX.measurable u)).aestronglyMeasurable) ?_
    (integrable_const _) (ae_of_all _ fun ω => (continuous_const.mul (hX.continuous ω)).continuousAt)
  filter_upwards [Metric.ball_mem_nhds u₀ one_pos] with u hu
  refine ae_of_all _ fun ω => ?_
  rw [Real.norm_eq_abs, abs_mul]
  have hu' : |u| ≤ |u₀| + 1 := by
    rw [Metric.mem_ball, Real.dist_eq] at hu
    have := abs_sub_abs_le_abs_sub u u₀
    linarith
  exact mul_le_mul (hZC ω) (hD u ω hu') (abs_nonneg _) ((abs_nonneg _).trans (hZC ω))

end Reg

/-! ### From conditional expectations to test variables -/

theorem integral_mul_eq_zero_of_condExp {P : Measure Ω} [IsFiniteMeasure P] {m : MeasurableSpace Ω}
    (hm : m ≤ mΩ) {D Z : Ω → ℝ} (hD : Integrable D P) (hZ : StronglyMeasurable[m] Z) {C : ℝ}
    (hZC : ∀ ω, |Z ω| ≤ C) (h : P[D | m] =ᵐ[P] 0) : ∫ ω, Z ω * D ω ∂P = 0 := by
  have hZD : Integrable (Z * D) P := by
    refine hD.bdd_mul (c := C) (hZ.mono hm).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs]; exact hZC ω
  have h1 := condExp_mul_of_stronglyMeasurable_left hZ hZD hD
  calc ∫ ω, Z ω * D ω ∂P = ∫ ω, (Z * D) ω ∂P := rfl
    _ = ∫ ω, (P[Z * D | m]) ω ∂P := (integral_condExp hm).symm
    _ = ∫ ω, (Z * P[D | m]) ω ∂P := integral_congr_ae h1
    _ = 0 := by
      rw [← integral_zero Ω ℝ]
      refine integral_congr_ae ?_
      filter_upwards [h] with ω hω
      simp [hω]

/-! ### The Jacobi diffusion -/

section Diffusion

variable {κ a b : ℝ} {P : Measure Ω} {𝓗 : Filtration ℝ mΩ} {U : ℝ → Ω → ℝ}

theorem IsJacobiDiffusion.mem_Icc (hU : IsJacobiDiffusion κ a b P 𝓗 U) (u : ℝ) (ω : Ω) :
    U u ω ∈ Icc (0 : ℝ) 1 := hU.1 u ω

theorem IsJacobiDiffusion.continuous (hU : IsJacobiDiffusion κ a b P 𝓗 U) (ω : Ω) :
    Continuous fun u => U u ω := hU.2.1 ω

theorem IsJacobiDiffusion.adapted (hU : IsJacobiDiffusion κ a b P 𝓗 U) (u : ℝ) :
    Measurable[𝓗 u] (U u) := hU.2.2.1 u

theorem IsJacobiDiffusion.measurable (hU : IsJacobiDiffusion κ a b P 𝓗 U) (u : ℝ) :
    Measurable (U u) := (hU.adapted u).mono (𝓗.le u) le_rfl

theorem IsJacobiDiffusion.isRegProc (hU : IsJacobiDiffusion κ a b P 𝓗 U) : IsRegProc U :=
  ⟨hU.continuous, hU.measurable, fun _ => ⟨1, fun u ω _ => by
    rw [abs_of_nonneg (hU.mem_Icc u ω).1]; exact (hU.mem_Icc u ω).2⟩⟩

theorem IsJacobiDiffusion.isRegProc_comp (hU : IsJacobiDiffusion κ a b P 𝓗 U) {f : ℝ → ℝ}
    (hf : Continuous f) : IsRegProc fun u ω => f (U u ω) :=
  hU.isRegProc.comp hf

theorem continuous_gen_pow (κ a b : ℝ) (n : ℕ) : Continuous (gen κ a b fun y => y ^ n) := by
  have : (gen κ a b fun y => y ^ n) = fun x => dcoef κ a n * x ^ (n - 1) + ccoef κ a b n * x ^ n :=
    funext (gen_pow κ a b n)
  rw [this]; fun_prop

/-- **The martingale problem against test variables.** -/
theorem IsJacobiDiffusion.hasCompensator_pow [IsFiniteMeasure P]
    (hU : IsJacobiDiffusion κ a b P 𝓗 U) (n : ℕ) :
    HasCompensator P 𝓗 (fun u ω => U u ω ^ n) (fun u ω => gen κ a b (fun y => y ^ n) (U u ω)) := by
  intro r x hrx Z hZ ⟨C, hZC⟩
  have h1 := hU.isRegProc_comp (continuous_pow n)
  have h2 := hU.isRegProc_comp (continuous_gen_pow κ a b n)
  have hD : Integrable (fun ω => U x ω ^ n - U r ω ^ n -
      ∫ s in r..x, gen κ a b (fun y => y ^ n) (U s ω)) P := by
    have i1 := h1.integrable_mul (P := P) (Z := fun _ => 1) measurable_const (C := 1)
      (fun _ => by simp) x
    have i2 := h1.integrable_mul (P := P) (Z := fun _ => 1) measurable_const (C := 1)
      (fun _ => by simp) r
    have i3 := h2.integrable_mul_intervalIntegral (P := P) (Z := fun _ => 1) measurable_const (C := 1)
      (fun _ => by simp) r x
    simp only [one_mul] at i1 i2 i3
    exact (i1.sub i2).sub i3
  exact integral_mul_eq_zero_of_condExp (𝓗.le r) hD hZ hZC (hU.2.2.2 n r x hrx)

/-- A Jacobi diffusion solves the landed polynomial martingale problem. -/
theorem IsJacobiDiffusion.isJacobiMP [IsFiniteMeasure P] (hU : IsJacobiDiffusion κ a b P 𝓗 U) :
    IsJacobiMP κ a b P U := by
  refine ⟨hU.mem_Icc, hU.continuous, hU.measurable, fun m s k n w v hs hwv => ?_⟩
  refine hU.hasCompensator_pow n w v hwv _ ?_ ⟨1, fun ω => ?_⟩
  · refine (Finset.measurable_prod _ fun i _ => ?_).stronglyMeasurable
    exact ((hU.adapted (s i)).mono (𝓗.mono (hs i)) le_rfl).pow_const _
  · have h0 : 0 ≤ ∏ i, U (s i) ω ^ k i :=
      Finset.prod_nonneg fun i _ => pow_nonneg (hU.mem_Icc _ ω).1 _
    rw [abs_of_nonneg h0]
    exact Finset.prod_le_one₀ (fun i _ => pow_nonneg (hU.mem_Icc _ ω).1 _) fun i _ =>
      pow_le_one₀ (hU.mem_Icc _ ω).1 (hU.mem_Icc _ ω).2

end Diffusion

/-! ### Auxiliary regular processes and a pathwise identity -/

theorem isRegProc_const_time {Ω : Type*} [MeasurableSpace Ω] {X : ℝ → Ω → ℝ} (hX : IsRegProc X)
    (x : ℝ) : IsRegProc fun (_ : ℝ) ω => X x ω := by
  obtain ⟨D, hD⟩ := hX.exists_bound |x|
  exact ⟨fun _ => continuous_const, fun _ => hX.measurable x, fun _ => ⟨D, fun _ ω _ => hD x ω le_rfl⟩⟩

theorem IsRegProc.intervalIntegral_left {Ω : Type*} [MeasurableSpace Ω] {α : ℝ → Ω → ℝ}
    (hα : IsRegProc α) (x : ℝ) : IsRegProc fun r ω => ∫ s in r..x, α s ω := by
  refine ⟨fun ω => ?_, fun r => hα.measurable_intervalIntegral r x, fun T => ?_⟩
  · have h : (fun r => ∫ s in r..x, α s ω) = fun r => -∫ s in x..r, α s ω := by
      funext r; exact intervalIntegral.integral_symm _ _
    rw [h]
    exact (continuous_iff_continuousAt.2 fun r =>
      ((hα.continuous ω).integral_hasStrictDerivAt x r).hasDerivAt.continuousAt).neg
  · obtain ⟨D, hD⟩ := hα.exists_bound (T + |x|)
    refine ⟨D * (T + |x|), fun r ω hr => ?_⟩
    have h1 := intervalIntegral.norm_integral_le_of_norm_le_const (a := r) (b := x)
      (f := fun s => α s ω) (C := D) fun s hs => by
        rw [Real.norm_eq_abs]
        refine hD s ω ?_
        have hs' := uIoc_subset_uIcc hs
        rw [mem_uIcc] at hs'
        rw [abs_le] at hr ⊢
        constructor <;> rcases hs' with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
          linarith [abs_nonneg x, neg_abs_le x, le_abs_self x]
    rw [Real.norm_eq_abs] at h1
    refine h1.trans ?_
    have hD0 : 0 ≤ D := (abs_nonneg _).trans (hD x ω (by
      rw [abs_le]; constructor <;> linarith [abs_nonneg T, abs_nonneg x, neg_abs_le x,
        le_abs_self x, (abs_nonneg r).trans hr]))
    refine mul_le_mul_of_nonneg_left ?_ hD0
    rw [abs_le] at hr
    rw [abs_le]; constructor <;> linarith [abs_nonneg x, neg_abs_le x, le_abs_self x]

theorem integrable_mul_incr {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsFiniteMeasure P] {X α : ℝ → Ω → ℝ} (hX : IsRegProc X) (hα : IsRegProc α) {Z : Ω → ℝ}
    (hZm : Measurable Z) {C : ℝ} (hZC : ∀ ω, |Z ω| ≤ C) (r x : ℝ) :
    Integrable (fun ω => Z ω * (X x ω - X r ω - ∫ s in r..x, α s ω)) P := by
  have := ((hX.integrable_mul (P := P) hZm hZC x).sub (hX.integrable_mul hZm hZC r)).sub
    (hα.integrable_mul_intervalIntegral hZm hZC r x)
  refine this.congr (ae_of_all _ fun ω => ?_)
  show Z ω * X x ω - Z ω * X r ω - Z ω * ∫ s in r..x, α s ω = _
  ring

/-- The pathwise identity behind the quadratic compensator: with `A_r = ∫_w^r α`,
`(X_x - X_w - A_x)² - ∫_w^x (γ - 2Xα) = (X_x² - X_w² - ∫_w^x γ) - 2 X_w (X_x - X_w - A_x)
  - 2 ∫_w^x α_r (X_x - X_r - ∫_r^x α) dr`. -/
theorem sq_sub_identity {X α γ : ℝ → ℝ} (hX : Continuous X) (hα : Continuous α) (hγ : Continuous γ)
    (w x : ℝ) :
    (X x - X w - ∫ s in w..x, α s) ^ 2 - ∫ s in w..x, (γ s - 2 * X s * α s) =
      (X x ^ 2 - X w ^ 2 - ∫ s in w..x, γ s) - 2 * (X w * (X x - X w - ∫ s in w..x, α s)) -
        2 * ∫ r in w..x, α r * (X x - X r - ∫ s in r..x, α s) := by
  set A : ℝ → ℝ := fun r => ∫ s in w..r, α s with hA
  have hA' : ∀ r, HasDerivAt A (α r) r := fun r => (hα.integral_hasStrictDerivAt w r).hasDerivAt
  have hAc : Continuous A := continuous_iff_continuousAt.2 fun r => (hA' r).continuousAt
  have hsplit : ∀ r, ∫ s in r..x, α s = A x - A r := fun r =>
    (intervalIntegral.integral_interval_sub_left (hα.intervalIntegrable _ _)
      (hα.intervalIntegrable _ _)).symm
  have hsq : ∫ r in w..x, α r * A r = A x ^ 2 / 2 := by
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := w) (b := x)
      (f := fun r => A r * A r / 2) (f' := fun r => α r * A r)
      (fun r _ => (((hA' r).mul (hA' r)).div_const 2).congr_deriv (by ring))
      ((hα.mul hAc).intervalIntegrable _ _)
    rw [this]; simp [hA, pow_two]
  have hT3 : ∫ r in w..x, α r * (X x - X r - ∫ s in r..x, α s) =
      X x * A x - (∫ r in w..x, α r * X r) - A x * A x + A x ^ 2 / 2 := by
    simp_rw [hsplit]
    have e : (fun r => α r * (X x - X r - (A x - A r))) =
        fun r => (α r * X x - α r * X r - α r * A x) + α r * A r := by
      funext r; ring
    rw [e, intervalIntegral.integral_add, intervalIntegral.integral_sub, intervalIntegral.integral_sub,
      intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const, hsq]
    · ring
    all_goals first
      | exact (hα.mul continuous_const).intervalIntegrable _ _
      | exact (hα.mul hX).intervalIntegrable _ _
      | exact (hα.mul hAc).intervalIntegrable _ _
      | exact ((hα.mul continuous_const).sub (hα.mul hX)).intervalIntegrable _ _
      | exact (((hα.mul continuous_const).sub (hα.mul hX)).sub
          (hα.mul continuous_const)).intervalIntegrable _ _
  have hγX : ∫ s in w..x, (γ s - 2 * X s * α s) = (∫ s in w..x, γ s) - 2 * ∫ s in w..x, α s * X s := by
    have hi : IntervalIntegrable (fun s => 2 * X s * α s) volume w x :=
      ((continuous_const.mul hX).mul hα).intervalIntegrable _ _
    rw [intervalIntegral.integral_sub (hγ.intervalIntegrable _ _) hi,
      ← intervalIntegral.integral_const_mul]
    congr 1
    refine intervalIntegral.integral_congr fun s _ => ?_
    ring
  rw [hγX, hT3]
  simp only [hA]
  ring

/-! ### Compensators -/

section Compensator

variable {P : Measure Ω} [IsFiniteMeasure P] {𝓗 : Filtration ℝ mΩ} {X α γ : ℝ → Ω → ℝ}

/-- The compensator identity in integrated form: `E[Z X_x] - E[Z X_r] = ∫_r^x E[Z α]`. -/
theorem HasCompensator.integral_mul_sub (h : HasCompensator P 𝓗 X α) (hX : IsRegProc X)
    (hα : IsRegProc α) {r x : ℝ} (hrx : r ≤ x) {Z : Ω → ℝ} (hZ : StronglyMeasurable[𝓗 r] Z)
    {C : ℝ} (hZC : ∀ ω, |Z ω| ≤ C) :
    ∫ ω, Z ω * X x ω ∂P - ∫ ω, Z ω * X r ω ∂P = ∫ s in r..x, ∫ ω, Z ω * α s ω ∂P := by
  have hZm : Measurable Z := (hZ.mono (𝓗.le r)).measurable
  have h0 := h r x hrx Z hZ ⟨C, hZC⟩
  simp only [mul_sub] at h0
  have i12 : Integrable (fun ω => Z ω * X x ω - Z ω * X r ω) P :=
    (hX.integrable_mul hZm hZC x).sub (hX.integrable_mul hZm hZC r)
  rw [MeasureTheory.integral_sub i12 (hα.integrable_mul_intervalIntegral hZm hZC r x),
    MeasureTheory.integral_sub (hX.integrable_mul hZm hZC x) (hX.integrable_mul hZm hZC r),
    sub_eq_zero] at h0
  rw [h0, hα.integral_mul_intervalIntegral hZm hZC]

/-- Conversely, the integrated identity at every bounded test variable gives a compensator. -/
theorem hasCompensator_of_integral_sub (hX : IsRegProc X) (hα : IsRegProc α)
    (h : ∀ r x : ℝ, r ≤ x → ∀ Z : Ω → ℝ, StronglyMeasurable[𝓗 r] Z → ∀ C, (∀ ω, |Z ω| ≤ C) →
      ∫ ω, Z ω * X x ω ∂P - ∫ ω, Z ω * X r ω ∂P = ∫ s in r..x, ∫ ω, Z ω * α s ω ∂P) :
    HasCompensator P 𝓗 X α := by
  intro r x hrx Z hZ ⟨C, hZC⟩
  have hZm : Measurable Z := (hZ.mono (𝓗.le r)).measurable
  simp only [mul_sub]
  have i12 : Integrable (fun ω => Z ω * X x ω - Z ω * X r ω) P :=
    (hX.integrable_mul hZm hZC x).sub (hX.integrable_mul hZm hZC r)
  rw [MeasureTheory.integral_sub i12 (hα.integrable_mul_intervalIntegral hZm hZC r x),
    MeasureTheory.integral_sub (hX.integrable_mul hZm hZC x) (hX.integrable_mul hZm hZC r),
    h r x hrx Z hZ C hZC, hα.integral_mul_intervalIntegral hZm hZC, sub_self]

/-- **Deterministic `C¹` weights.** If `X` is compensated by `α` and `g` is `C¹`, then `g X` is
compensated by `g' X + g α`. -/
theorem HasCompensator.mul_left (h : HasCompensator P 𝓗 X α) (hX : IsRegProc X)
    (hα : IsRegProc α) {g g' : ℝ → ℝ} (hg : ∀ x, HasDerivAt g (g' x) x) (hg' : Continuous g') :
    HasCompensator P 𝓗 (fun x ω => g x * X x ω) (fun x ω => g' x * X x ω + g x * α x ω) := by
  have hgc : Continuous g := continuous_iff_continuousAt.2 fun x => (hg x).continuousAt
  refine hasCompensator_of_integral_sub (hX.const_mul hgc)
    ((hX.const_mul hg').add (hα.const_mul hgc)) fun r x hrx Z hZ C hZC => ?_
  have hZm : Measurable Z := (hZ.mono (𝓗.le r)).measurable
  set φ : ℝ → ℝ := fun y => ∫ ω, Z ω * X y ω ∂P with hφ_def
  set ψ : ℝ → ℝ := fun y => ∫ ω, Z ω * α y ω ∂P with hψ_def
  have hψc : Continuous ψ := hα.continuous_integral_mul hZm hZC
  set φt : ℝ → ℝ := fun y => φ r + ∫ s in r..y, ψ s with hφt_def
  have hφeq : ∀ y, r ≤ y → φ y = φt y := fun y hry => by
    have := h.integral_mul_sub hX hα hry hZ hZC
    simp only [hφt_def, hφ_def, hψ_def]
    linarith
  have hφt : ∀ y, HasDerivAt φt (ψ y) y := fun y =>
    ((hψc.integral_hasStrictDerivAt r y).hasDerivAt).const_add _
  have hφtc : Continuous φt := continuous_iff_continuousAt.2 fun y => (hφt y).continuousAt
  have hE : g x * φt x - g r * φt r = ∫ y in r..x, (g' y * φt y + g y * ψ y) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => (hg y).mul (hφt y))
      (((hg'.mul hφtc).add (hgc.mul hψc)).intervalIntegrable _ _)]
    rfl
  have hin : ∀ s, ∫ ω, Z ω * (g' s * X s ω + g s * α s ω) ∂P = g' s * φ s + g s * ψ s := by
    intro s
    have e : (fun ω => Z ω * (g' s * X s ω + g s * α s ω)) =
        fun ω => g' s * (Z ω * X s ω) + g s * (Z ω * α s ω) := by
      funext ω; ring
    rw [e, integral_add ((hX.integrable_mul hZm hZC s).const_mul _)
      ((hα.integrable_mul hZm hZC s).const_mul _), integral_const_mul, integral_const_mul]
  have hl : ∀ y, ∫ ω, Z ω * (g y * X y ω) ∂P = g y * φ y := fun y => by
    rw [← integral_const_mul]; congr 1; funext ω; ring
  simp only [hl, hin]
  rw [hφeq x hrx, hφeq r le_rfl, hE]
  refine intervalIntegral.integral_congr fun y hy => ?_
  rw [hφeq y (uIcc_of_le hrx ▸ hy).1]

/-- **The quadratic compensator.** If `X` is compensated by `α` and `X²` by `γ`, then for every
`w ≤ x` the square of the martingale part `M_x = X_x - X_w - ∫_w^x α` has
`E[Z (M_x² - ∫_w^x (γ - 2 X α))] = 0` for every bounded `𝓗_w`-measurable `Z`. -/
theorem HasCompensator.sq_sub (h : HasCompensator P 𝓗 X α)
    (h2 : HasCompensator P 𝓗 (fun x ω => X x ω ^ 2) γ) (hX : IsRegProc X) (hα : IsRegProc α)
    (hγ : IsRegProc γ) (hXa : ∀ u, StronglyMeasurable[𝓗 u] (X u))
    (hαa : ∀ u, StronglyMeasurable[𝓗 u] (α u)) {w x : ℝ} (hwx : w ≤ x) {Z : Ω → ℝ}
    (hZ : StronglyMeasurable[𝓗 w] Z)
    {C : ℝ} (hZC : ∀ ω, |Z ω| ≤ C) :
    ∫ ω, Z ω * ((X x ω - X w ω - ∫ s in w..x, α s ω) ^ 2 -
      ∫ s in w..x, (γ s ω - 2 * X s ω * α s ω)) ∂P = 0 := by
  have hZm : Measurable Z := (hZ.mono (𝓗.le w)).measurable
  obtain ⟨D, hD⟩ := hX.exists_bound |w|
  have hX2 : IsRegProc fun u ω => X u ω ^ 2 := by
    simpa only [pow_two] using hX.mul hX
  -- the three orthogonal pieces
  set T1 : Ω → ℝ := fun ω => X x ω ^ 2 - X w ω ^ 2 - ∫ s in w..x, γ s ω with hT1
  set T2 : Ω → ℝ := fun ω => X x ω - X w ω - ∫ s in w..x, α s ω with hT2
  set F : ℝ → Ω → ℝ := fun r ω => α r ω * (X x ω - X r ω - ∫ s in r..x, α s ω) with hF
  have hFreg : IsRegProc F :=
    hα.mul ((isRegProc_const_time hX x).sub hX |>.sub (hα.intervalIntegral_left x))
  set T3 : Ω → ℝ := fun ω => ∫ r in w..x, F r ω with hT3
  -- the pathwise identity
  have hpath : ∀ ω, (X x ω - X w ω - ∫ s in w..x, α s ω) ^ 2 -
      ∫ s in w..x, (γ s ω - 2 * X s ω * α s ω) = T1 ω - 2 * (X w ω * T2 ω) - 2 * T3 ω := by
    intro ω
    exact sq_sub_identity (hX.continuous ω) (hα.continuous ω) (hγ.continuous ω) w x
  have hZXw : Measurable fun ω => Z ω * X w ω := hZm.mul (hX.measurable w)
  have i1 : Integrable (fun ω => Z ω * T1 ω) P :=
    integrable_mul_incr hX2 hγ hZm hZC w x
  have i2 : Integrable (fun ω => (Z ω * X w ω) * T2 ω) P :=
    integrable_mul_incr hX hα hZXw (C := C * D) (fun ω => by
      rw [abs_mul]; exact mul_le_mul (hZC ω) (hD w ω le_rfl) (abs_nonneg _)
        ((abs_nonneg _).trans (hZC ω))) w x
  have i3 : Integrable (fun ω => Z ω * T3 ω) P := hFreg.integrable_mul_intervalIntegral hZm hZC w x
  have e1 : ∫ ω, Z ω * T1 ω ∂P = 0 := h2 w x hwx Z hZ ⟨C, hZC⟩
  have e2 : ∫ ω, (Z ω * X w ω) * T2 ω ∂P = 0 := by
    refine h w x hwx _ ?_ ⟨C * D, fun ω => ?_⟩
    · exact (hZ.measurable.mul ((hXa w).measurable)).stronglyMeasurable
    · rw [abs_mul]; exact mul_le_mul (hZC ω) (hD w ω le_rfl) (abs_nonneg _)
        ((abs_nonneg _).trans (hZC ω))
  have e3 : ∫ ω, Z ω * T3 ω ∂P = 0 := by
    rw [hT3, hFreg.integral_mul_intervalIntegral hZm hZC]
    refine (intervalIntegral.integral_congr fun r hr => ?_).trans intervalIntegral.integral_zero
    have hwr : w ≤ r := (uIcc_of_le hwx ▸ hr).1
    have hrx : r ≤ x := (uIcc_of_le hwx ▸ hr).2
    obtain ⟨Dα, hDα⟩ := hα.exists_bound |r|
    have := h r x hrx (fun ω => Z ω * α r ω) ?_ ⟨C * Dα, fun ω => ?_⟩
    · simp only [hF]
      rw [← this]; congr 1; funext ω; ring
    · exact ((hZ.mono (𝓗.mono hwr)).measurable.mul (hαa r).measurable).stronglyMeasurable
    · rw [abs_mul]; exact mul_le_mul (hZC ω) (hDα r ω le_rfl) (abs_nonneg _)
        ((abs_nonneg _).trans (hZC ω))
  have e : (fun ω => Z ω * ((X x ω - X w ω - ∫ s in w..x, α s ω) ^ 2 -
      ∫ s in w..x, (γ s ω - 2 * X s ω * α s ω))) =
      fun ω => Z ω * T1 ω - 2 * ((Z ω * X w ω) * T2 ω) - 2 * (Z ω * T3 ω) := by
    funext ω; rw [hpath ω]; ring
  have i2' : Integrable (fun ω => 2 * ((Z ω * X w ω) * T2 ω)) P := i2.const_mul 2
  have i3' : Integrable (fun ω => 2 * (Z ω * T3 ω)) P := i3.const_mul 2
  have i12 : Integrable (fun ω => Z ω * T1 ω - 2 * ((Z ω * X w ω) * T2 ω)) P := i1.sub i2'
  rw [e, integral_sub i12 i3', integral_sub i1 i2', integral_const_mul, integral_const_mul, e1, e2,
    e3]
  ring

end Compensator

end Jacobi

end Sec2

end InteractingSLE
