/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.TwoForceRatio
import InteractingSLE.Spec.Sec2.JacobiMoments
import InteractingSLE.Spec.Sec2.TwoSeedLaw
import InteractingSLE.Spec.Sec4.RepulsionNoncollision

/-!
# Recurrence of the two-seed gap ratio (Part B.3, (E13))

Packet PROVE-ZHAN-GT4-B. Source: Astra, *Follow-up proofs and dependency audit*, §B.3 L1266–L1273 (ruling R38):
"let `L = W − V_L`, `R = V_R − W`, `U = log(R/L)` … Both scale integrals diverge, and this clock is infinite … Thus `U`
hits any prescribed finite level." (Additional note, Lemma 1.7, (ZE.6), ruling R39.)

The project describes the two-seed law through the angle `L/(L+R)` in the logarithmic clock `u = log(L + R)`, a
stationary Jacobi diffusion given by its polynomial martingale problem (`Sec2.Jacobi.IsJacobiMP`,
`Sec2.isJacobiMP_angleG`). This file proves that such a process hits every level of `(0, 1)` after every time, using
only the martingale problem:

* **conditional moments converge to the beta moments, uniformly**: for every nonnegative bounded functional `F` in the
  span of products of powers of earlier values, `E[F U_v^k] → m_k E[F]` as `v → ∞`, at a rate independent of `F`
  (the moment system `φ_k' = c_k φ_k + d_k φ_{k−1}`, `c_k < 0`, solved by comparison);
* with `q(x) = 1 − x^m (x − α)/(1 − α) ≥ 1_{[0, α]}` (`m` large, so that `m_{m+1} > α m_m`), `E[F q(U_v)] ≤ (1 − c) E[F]`,
  hence `P(U ≤ α at u₀ + T, …, u₀ + NT) ≤ (1 − c)^N`: the angle exceeds `α` after every time; by the symmetry
  `U ↦ 1 − U` it also falls below `α`; by continuity it hits `α`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.ZhanGT4

open Sec2.Jacobi

/-! ### Past polynomial functionals and their moment system -/

section Moments

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {κ a b : ℝ} {U : ℝ → Ω → ℝ}

/-- The span of the products `∏ U_{s_i}^{k_i}` of powers of values at times `s_i ≤ w`. -/
def pastSpan (U : ℝ → Ω → ℝ) (w : ℝ) : Submodule ℝ (Ω → ℝ) :=
  Submodule.span ℝ {f | ∃ (m : ℕ) (s : Fin m → ℝ) (k : Fin m → ℕ), (∀ i, s i ≤ w) ∧ f = prodPow U s k}

/-- The moment function `x ↦ E[F U_x^n]`. -/
def mo (P : Measure Ω) (U : ℝ → Ω → ℝ) (F : Ω → ℝ) (n : ℕ) (x : ℝ) : ℝ := ∫ ω, F ω * U x ω ^ n ∂P

/-- A good past functional at time `w`: measurable, bounded, and its moment functions solve the moment system after
`w`. -/
def GoodPast (P : Measure Ω) (κ a b : ℝ) (U : ℝ → Ω → ℝ) (w : ℝ) (F : Ω → ℝ) : Prop :=
  Measurable F ∧ (∃ C, ∀ ω, |F ω| ≤ C) ∧
    ∀ (n : ℕ) (v' v : ℝ), w ≤ v' → v' ≤ v →
      mo P U F n v - mo P U F n v' =
        ∫ y in v'..v, (ccoef κ a b n * mo P U F n y + dcoef κ a n * mo P U F (n - 1) y)

variable [IsProbabilityMeasure P]

theorem jmp_integrable_mul_pow (hU : IsJacobiMP κ a b P U) {F : Ω → ℝ} (hF : Measurable F) {C : ℝ}
    (hC : ∀ ω, |F ω| ≤ C) (n : ℕ) (x : ℝ) : Integrable (fun ω => F ω * U x ω ^ n) P := by
  refine Integrable.of_bound (hF.mul ((hU.measurable x).pow_const n)).aestronglyMeasurable C
    (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  calc |F ω| * |U x ω ^ n| ≤ C * 1 :=
        mul_le_mul (hC ω) (abs_le_one_of_mem_Icc (hU.pow_mem_Icc x ω n)) (abs_nonneg _)
          ((abs_nonneg _).trans (hC ω))
    _ = C := mul_one C

theorem jmp_continuous_mo (hU : IsJacobiMP κ a b P U) {F : Ω → ℝ} (hF : Measurable F) {C : ℝ}
    (hC : ∀ ω, |F ω| ≤ C) (n : ℕ) : Continuous (mo P U F n) := by
  refine continuous_of_dominated (bound := fun _ => C)
    (fun x => (jmp_integrable_mul_pow hU hF hC n x).aestronglyMeasurable)
    (fun x => ae_of_all _ fun ω => ?_) (integrable_const _)
    (ae_of_all _ fun ω => continuous_const.mul ((hU.continuous ω).pow n))
  rw [Real.norm_eq_abs, abs_mul]
  calc |F ω| * |U x ω ^ n| ≤ C * 1 :=
        mul_le_mul (hC ω) (abs_le_one_of_mem_Icc (hU.pow_mem_Icc x ω n)) (abs_nonneg _)
          ((abs_nonneg _).trans (hC ω))
    _ = C := mul_one C

theorem jmp_goodPast_prodPow (hU : IsJacobiMP κ a b P U) {w : ℝ} {m : ℕ} {s : Fin m → ℝ}
    (k : Fin m → ℕ) (hs : ∀ i, s i ≤ w) : GoodPast P κ a b U w (prodPow U s k) :=
  ⟨hU.measurable_prodPow s k, ⟨1, fun ω => abs_le_one_of_mem_Icc (hU.prodPow_mem_Icc s k ω)⟩,
    fun n _ _ hwv' hv'v => hU.momF_sub s k n (fun i => (hs i).trans hwv') hv'v⟩

theorem jmp_goodPast_add (hU : IsJacobiMP κ a b P U) {w : ℝ} {F G : Ω → ℝ}
    (hF : GoodPast P κ a b U w F) (hG : GoodPast P κ a b U w G) : GoodPast P κ a b U w (F + G) := by
  obtain ⟨hFm, ⟨C₁, hC₁⟩, hFo⟩ := hF
  obtain ⟨hGm, ⟨C₂, hC₂⟩, hGo⟩ := hG
  have hadd : ∀ n x, mo P U (F + G) n x = mo P U F n x + mo P U G n x := fun n x => by
    simp only [mo, Pi.add_apply, add_mul]
    exact integral_add (jmp_integrable_mul_pow hU hFm hC₁ n x) (jmp_integrable_mul_pow hU hGm hC₂ n x)
  refine ⟨hFm.add hGm, ⟨C₁ + C₂, fun ω => (abs_add_le _ _).trans (add_le_add (hC₁ ω) (hC₂ ω))⟩,
    fun n v' v hwv' hv'v => ?_⟩
  have i1 : IntervalIntegrable (fun y => ccoef κ a b n * mo P U F n y + dcoef κ a n * mo P U F (n - 1) y)
      volume v' v :=
    (((jmp_continuous_mo hU hFm hC₁ n).const_mul _).add ((jmp_continuous_mo hU hFm hC₁ (n - 1)).const_mul _)
      ).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun y => ccoef κ a b n * mo P U G n y + dcoef κ a n * mo P U G (n - 1) y)
      volume v' v :=
    (((jmp_continuous_mo hU hGm hC₂ n).const_mul _).add ((jmp_continuous_mo hU hGm hC₂ (n - 1)).const_mul _)
      ).intervalIntegrable _ _
  simp only [hadd]
  rw [show mo P U F n v + mo P U G n v - (mo P U F n v' + mo P U G n v') =
      (mo P U F n v - mo P U F n v') + (mo P U G n v - mo P U G n v') by ring,
    hFo n v' v hwv' hv'v, hGo n v' v hwv' hv'v, ← intervalIntegral.integral_add i1 i2]
  congr 1
  funext y
  ring

omit [IsProbabilityMeasure P] in
theorem jmp_goodPast_smul {w : ℝ} {F : Ω → ℝ}
    (hF : GoodPast P κ a b U w F) (c : ℝ) : GoodPast P κ a b U w (c • F) := by
  obtain ⟨hFm, ⟨C, hC⟩, hFo⟩ := hF
  have hsm : ∀ n x, mo P U (c • F) n x = c * mo P U F n x := fun n x => by
    simp only [mo, Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact integral_const_mul c _
  refine ⟨hFm.const_mul c, ⟨|c| * C, fun ω => by
      rw [Pi.smul_apply, smul_eq_mul, abs_mul]
      exact mul_le_mul_of_nonneg_left (hC ω) (abs_nonneg c)⟩, fun n v' v hwv' hv'v => ?_⟩
  simp only [hsm]
  rw [← mul_sub, hFo n v' v hwv' hv'v, ← intervalIntegral.integral_const_mul]
  congr 1
  funext y
  ring

theorem jmp_goodPast_of_mem (hU : IsJacobiMP κ a b P U) {w : ℝ} {F : Ω → ℝ}
    (hF : F ∈ pastSpan U w) : GoodPast P κ a b U w F := by
  induction hF using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨m, s, k, hs, rfl⟩ := hf
    exact jmp_goodPast_prodPow hU k hs
  | zero =>
    have h0 : (0 : Ω → ℝ) = (0 : ℝ) • prodPow U (Fin.elim0 : Fin 0 → ℝ) Fin.elim0 := by simp
    rw [h0]
    exact jmp_goodPast_smul (jmp_goodPast_prodPow hU _ fun i => i.elim0) 0
  | add f g _ _ hf hg => exact jmp_goodPast_add hU hf hg
  | smul c f _ hf => exact jmp_goodPast_smul hf c

omit [MeasurableSpace Ω] in
theorem one_mem_pastSpan (w : ℝ) : (fun _ => (1 : ℝ)) ∈ pastSpan (Ω := Ω) U w := by
  refine Submodule.subset_span ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, ?_⟩
  funext ω
  simp [prodPow]

omit [MeasurableSpace Ω] in
/-- Multiplying by a power of an earlier value stays in the span. -/
theorem pow_mul_mem_pastSpan {w s : ℝ} (hs : s ≤ w) (j : ℕ) {F : Ω → ℝ} (hF : F ∈ pastSpan U w) :
    (fun ω => U s ω ^ j * F ω) ∈ pastSpan U w := by
  induction hF using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨m, s', k, hs', rfl⟩ := hf
    refine Submodule.subset_span ⟨m + 1, Fin.cons s s', Fin.cons j k, fun i => ?_, ?_⟩
    · refine Fin.cases hs (fun i => ?_) i
      simpa using hs' i
    · funext ω
      simp [prodPow, Fin.prod_univ_succ]
  | zero =>
    have h0 : (fun ω => U s ω ^ j * (0 : Ω → ℝ) ω) = 0 := by funext ω; simp
    rw [h0]; exact (pastSpan U w).zero_mem
  | add f g _ _ hf hg =>
    have : (fun ω => U s ω ^ j * (f + g) ω) = (fun ω => U s ω ^ j * f ω) + fun ω => U s ω ^ j * g ω := by
      funext ω; simp [mul_add]
    rw [this]; exact add_mem hf hg
  | smul c f _ hf =>
    have : (fun ω => U s ω ^ j * (c • f) ω) = c • fun ω => U s ω ^ j * f ω := by
      funext ω; simp only [Pi.smul_apply, smul_eq_mul]; ring
    rw [this]; exact Submodule.smul_mem _ c hf

omit [MeasurableSpace Ω] in
theorem pastSpan_mono {w w' : ℝ} (h : w ≤ w') : pastSpan (Ω := Ω) U w ≤ pastSpan U w' :=
  Submodule.span_mono fun _ ⟨m, s, k, hs, hf⟩ => ⟨m, s, k, fun i => (hs i).trans h, hf⟩

end Moments

/-! ### Comparison for the affine moment equations -/

section Comparison

/-- **Lower comparison.** If `ψ x − ψ w₁ = ∫_{w₁}^x (c ψ + f)` for `x ≥ w₁` (continuous `ψ, f`, `c ≠ 0`) and `f ≥ g₀`
on `[w₁, ∞)`, then `(ψ w₁ + g₀/c) e^{c (x − w₁)} ≤ ψ x + g₀/c` for `x ≥ w₁`. -/
theorem le_of_affine_integral {ψ f : ℝ → ℝ} (hψ : Continuous ψ) (hf : Continuous f) {c w₁ g₀ : ℝ} (hc : c ≠ 0)
    (hint : ∀ x, w₁ ≤ x → ψ x - ψ w₁ = ∫ y in w₁..x, (c * ψ y + f y))
    (hg : ∀ y, w₁ ≤ y → g₀ ≤ f y) {x : ℝ} (hx : w₁ ≤ x) :
    (ψ w₁ + g₀ / c) * Real.exp (c * (x - w₁)) ≤ ψ x + g₀ / c := by
  have hcont : Continuous fun y => c * ψ y + f y := (hψ.const_mul c).add hf
  set F : ℝ → ℝ := fun y => ψ w₁ + ∫ t in w₁..y, (c * ψ t + f t) with hFdef
  have hF : ∀ y, HasDerivAt F (c * ψ y + f y) y := fun y =>
    (intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable _ _)
      (hcont.stronglyMeasurableAtFilter _ _) hcont.continuousAt).const_add _
  have hFψ : ∀ y, w₁ ≤ y → F y = ψ y := fun y hy => by simp only [hFdef]; linarith [hint y hy]
  have hψd : ∀ y, w₁ < y → HasDerivAt ψ (c * ψ y + f y) y := fun y hy =>
    (hF y).congr_of_eventuallyEq (Filter.mem_of_superset (Ioi_mem_nhds hy) fun z hz => (hFψ z (le_of_lt hz)).symm)
  set N : ℝ → ℝ := fun y => (ψ y + g₀ / c) * Real.exp (-(c * (y - w₁))) with hNdef
  have hNd : ∀ y, w₁ < y → HasDerivAt N ((f y - g₀) * Real.exp (-(c * (y - w₁)))) y := fun y hy => by
    have h1 : HasDerivAt (fun y => -(c * (y - w₁))) (-(c * 1)) y :=
      (((hasDerivAt_id y).sub_const w₁).const_mul c).neg
    have := ((hψd y hy).add_const (g₀ / c)).mul h1.exp
    refine this.congr_deriv ?_
    field_simp
    ring
  have hNc : ContinuousOn N (Ici w₁) :=
    ((hψ.add continuous_const).mul (Real.continuous_exp.comp
      ((continuous_id.sub continuous_const).const_mul c).neg)).continuousOn
  have hmono : MonotoneOn N (Ici w₁) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici w₁) hNc (fun y hy => ?_) fun y hy => ?_
    · rw [interior_Ici] at hy
      exact (hNd y hy).differentiableAt.differentiableWithinAt
    · rw [interior_Ici] at hy
      rw [(hNd y hy).deriv]
      exact mul_nonneg (sub_nonneg.2 (hg y (le_of_lt hy))) (Real.exp_pos _).le
  have h := hmono (Set.mem_Ici.2 le_rfl) hx hx
  simp only [hNdef, sub_self, mul_zero, neg_zero, Real.exp_zero, mul_one] at h
  have he : Real.exp (-(c * (x - w₁))) * Real.exp (c * (x - w₁)) = 1 := by
    rw [← Real.exp_add]; simp
  calc (ψ w₁ + g₀ / c) * Real.exp (c * (x - w₁))
      ≤ (ψ x + g₀ / c) * Real.exp (-(c * (x - w₁))) * Real.exp (c * (x - w₁)) :=
        mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
    _ = ψ x + g₀ / c := by rw [mul_assoc, he, mul_one]

/-- **Upper comparison** (apply the lower one to `−ψ`, `−f`). -/
theorem ge_of_affine_integral {ψ f : ℝ → ℝ} (hψ : Continuous ψ) (hf : Continuous f) {c w₁ g₁ : ℝ} (hc : c ≠ 0)
    (hint : ∀ x, w₁ ≤ x → ψ x - ψ w₁ = ∫ y in w₁..x, (c * ψ y + f y))
    (hg : ∀ y, w₁ ≤ y → f y ≤ g₁) {x : ℝ} (hx : w₁ ≤ x) :
    ψ x + g₁ / c ≤ (ψ w₁ + g₁ / c) * Real.exp (c * (x - w₁)) := by
  have h := le_of_affine_integral (ψ := fun y => -ψ y) (f := fun y => -f y) hψ.neg hf.neg hc
    (g₀ := -g₁) (fun x hx => by
      rw [show -ψ x - -ψ w₁ = -(ψ x - ψ w₁) by ring, hint x hx, ← intervalIntegral.integral_neg]
      congr 1; funext y; ring) (fun y hy => neg_le_neg (hg y hy)) hx
  have e1 : (-ψ w₁ + -g₁ / c) = -(ψ w₁ + g₁ / c) := by ring
  have e2 : (-ψ x + -g₁ / c) = -(ψ x + g₁ / c) := by ring
  rw [e1, e2, neg_mul] at h
  linarith

end Comparison

/-! ### Uniform convergence of the moment system -/

section MomentConv

variable {κ a b : ℝ}

theorem dcoef_pos (hκ : 0 ≤ κ) (ha : 0 < a) {n : ℕ} (hn : 1 ≤ n) : 0 < dcoef κ a n := by
  rw [dcoef]
  have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have : 0 ≤ κ / 4 * (n * ((n : ℝ) - 1)) := mul_nonneg (by linarith) (mul_nonneg (by linarith) (by linarith))
  have : 0 < (n : ℝ) * a / 2 := by positivity
  linarith

theorem jacobiMoment_mem_Icc (hκ : 0 ≤ κ) (ha : 0 < a) (hb : 0 ≤ b) (n : ℕ) :
    jacobiMoment κ a b n ∈ Icc (0 : ℝ) 1 := by
  induction n with
  | zero => simp [jacobiMoment]
  | succ n ih =>
    rw [jacobiMoment]
    have hc := ccoef_neg hκ (by linarith : 0 < a + b) (Nat.le_add_left 1 n)
    have hd := dcoef_pos hκ ha (Nat.le_add_left 1 n)
    have hr : dcoef κ a (n + 1) / -ccoef κ a b (n + 1) ∈ Icc (0 : ℝ) 1 := by
      refine ⟨div_nonneg hd.le (by linarith), (div_le_one (by linarith)).2 ?_⟩
      simp only [dcoef, ccoef, neg_neg]
      have : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) * b / 2 := by positivity
      nlinarith
    exact ⟨mul_nonneg ih.1 hr.1, by nlinarith [ih.1, ih.2, hr.1, hr.2]⟩

/-- **Uniform convergence of the moment system to the beta moments.** For every `k` and `ε > 0` there is a time `T`
such that every family `φ_j` (continuous, `φ_0 ≡ A ≥ 0`, `0 ≤ φ_j ≤ A`) solving the moment system after `w` satisfies
`|φ_k x − m_k A| ≤ ε A` for `x ≥ w + T`. -/
theorem moment_system_conv (hκ : 0 ≤ κ) (ha : 0 < a) (hb : 0 ≤ b) (k : ℕ) :
    ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 0 ≤ T ∧ ∀ (φ : ℕ → ℝ → ℝ) (A w : ℝ), 0 ≤ A → (∀ j, Continuous (φ j)) →
      (∀ x, w ≤ x → φ 0 x = A) → (∀ j x, w ≤ x → 0 ≤ φ j x ∧ φ j x ≤ A) →
      (∀ j x' x, 1 ≤ j → w ≤ x' → x' ≤ x →
        φ j x - φ j x' = ∫ y in x'..x, (ccoef κ a b j * φ j y + dcoef κ a j * φ (j - 1) y)) →
      ∀ x, w + T ≤ x → |φ k x - jacobiMoment κ a b k * A| ≤ ε * A := by
  induction k with
  | zero =>
    intro ε hε
    refine ⟨0, le_rfl, fun φ A w hA _ h0 _ _ x hx => ?_⟩
    rw [h0 x (by linarith), jacobiMoment, one_mul, sub_self, abs_zero]
    positivity
  | succ k ih =>
    intro ε hε
    have hc := ccoef_neg hκ (by linarith : 0 < a + b) (Nat.le_add_left 1 k)
    have hd := dcoef_pos hκ ha (Nat.le_add_left 1 k)
    set c := ccoef κ a b (k + 1) with hcdef
    set d := dcoef κ a (k + 1) with hddef
    set M := jacobiMoment κ a b (k + 1) with hM
    have hMeq : c * M + d * jacobiMoment κ a b k = 0 := ccoef_mul_jacobiMoment_add hκ (by linarith) k
    have hM01 := jacobiMoment_mem_Icc hκ ha hb (k + 1)
    obtain ⟨T₁, hT₁, hT₁φ⟩ := ih (ε * (-c) / (2 * d)) (by
      have : 0 < -c := by linarith
      positivity)
    -- `e^{c T₂} ≤ ε/2`
    obtain ⟨T₂, hT₂, hT₂e⟩ : ∃ T₂ : ℝ, 0 ≤ T₂ ∧ Real.exp (c * T₂) ≤ ε / 2 := by
      refine ⟨max 0 (Real.log (ε / 2) / c), le_max_left _ _, ?_⟩
      have h1 : c * max 0 (Real.log (ε / 2) / c) ≤ Real.log (ε / 2) := by
        have : Real.log (ε / 2) / c ≤ max 0 (Real.log (ε / 2) / c) := le_max_right _ _
        have := mul_le_mul_of_nonpos_left this hc.le
        rwa [mul_div_cancel₀ _ hc.ne] at this
      calc Real.exp (c * max 0 (Real.log (ε / 2) / c)) ≤ Real.exp (Real.log (ε / 2)) := Real.exp_le_exp.2 h1
        _ = ε / 2 := Real.exp_log (by positivity)
    refine ⟨T₁ + T₂, by positivity, fun φ A w hA hcont h0 hbd hode x hx => ?_⟩
    set w₁ := w + T₁ with hw₁
    have hφk := hT₁φ φ A w hA hcont h0 hbd hode
    set mk := jacobiMoment κ a b k with hmk
    set ε' := ε * (-c) / (2 * d) with hε'
    have hint : ∀ x', w₁ ≤ x' → φ (k + 1) x' - φ (k + 1) w₁ =
        ∫ y in w₁..x', (c * φ (k + 1) y + d * φ k y) := fun x' hx' => by
      have := hode (k + 1) w₁ x' (Nat.le_add_left 1 k) (by linarith) hx'
      simpa using this
    have hlow : ∀ y, w₁ ≤ y → d * ((mk - ε') * A) ≤ d * φ k y := fun y hy => by
      have h := hφk y hy
      have h' : (mk - ε') * A ≤ φ k y := by rw [sub_mul]; linarith [(abs_le.1 h).1]
      exact mul_le_mul_of_nonneg_left h' hd.le
    have hupp : ∀ y, w₁ ≤ y → d * φ k y ≤ d * ((mk + ε') * A) := fun y hy => by
      have h := hφk y hy
      have h' : φ k y ≤ (mk + ε') * A := by rw [add_mul]; linarith [(abs_le.1 h).2]
      exact mul_le_mul_of_nonneg_left h' hd.le
    have hxw₁ : w₁ ≤ x := by linarith
    have hfc : Continuous fun y => d * φ k y := (hcont k).const_mul d
    have hL := le_of_affine_integral (hcont (k + 1)) hfc hc.ne hint hlow hxw₁
    have hU := ge_of_affine_integral (hcont (k + 1)) hfc hc.ne hint hupp hxw₁
    -- the exponential factor
    set e := Real.exp (c * (x - w₁)) with he
    have he0 : 0 < e := Real.exp_pos _
    have he1 : e ≤ ε / 2 := by
      refine le_trans (Real.exp_le_exp.2 ?_) hT₂e
      have : T₂ ≤ x - w₁ := by linarith
      nlinarith
    have hψ0 := (hbd (k + 1) w₁ (by linarith)).1
    have hψA := (hbd (k + 1) w₁ (by linarith)).2
    -- `d (m_k ∓ ε') A / c = −(M ∓ ε/2) A`
    have hdm : d * mk = -(c * M) := by linarith [hMeq]
    have hdε : d * ε' = ε * -c / 2 := by
      rw [hε']; field_simp
    have hg0 : d * ((mk - ε') * A) / c = -((M - ε / 2) * A) := by
      rw [div_eq_iff hc.ne]
      linear_combination A * hdm - A * hdε
    have hg1 : d * ((mk + ε') * A) / c = -((M + ε / 2) * A) := by
      rw [div_eq_iff hc.ne]
      linear_combination A * hdm + A * hdε
    rw [hg0] at hL
    rw [hg1] at hU
    set G := (M - ε / 2) * A with hG
    set H := (M + ε / 2) * A with hH
    have hψe : 0 ≤ φ (k + 1) w₁ * e := mul_nonneg hψ0 he0.le
    have hAe : A * e ≤ A * (ε / 2) := mul_le_mul_of_nonneg_left he1 hA
    have hAe0 : 0 ≤ A * e := mul_nonneg hA he0.le
    rw [abs_le]
    constructor
    · -- lower bound: `ψ x ≥ G + (ψ₁ − G) e ≥ G − A ε/2`
      have hL2 : φ (k + 1) w₁ * e - G * e ≤ φ (k + 1) x - G := by
        have := hL; rw [add_mul, neg_mul] at this; linarith
      have hGe : G * e ≤ A * (ε / 2) := by
        rcases le_total 0 G with hG0 | hG0
        · have hGA : G ≤ A := by
            rw [hG]; nlinarith [hM01.2, hA, hε]
          exact (mul_le_mul_of_nonneg_right hGA he0.le).trans hAe
        · have : G * e ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hG0 he0.le
          have : 0 ≤ A * (ε / 2) := by positivity
          linarith
      have hGd : G = M * A - ε / 2 * A := by rw [hG]; ring
      linarith
    · -- upper bound: `ψ x ≤ H + (ψ₁ − H) e ≤ H + A ε/2`
      have hU2 : φ (k + 1) x - H ≤ φ (k + 1) w₁ * e - H * e := by
        have := hU; rw [add_mul, neg_mul] at this; linarith
      have hH0 : 0 ≤ H * e := mul_nonneg (by rw [hH]; nlinarith [hM01.1, hA, hε]) he0.le
      have hψ1e : φ (k + 1) w₁ * e ≤ A * e := mul_le_mul_of_nonneg_right hψA he0.le
      have hHd : H = M * A + ε / 2 * A := by rw [hH]; ring
      linarith

theorem jacobiMoment_pos (hκ : 0 ≤ κ) (ha : 0 < a) (hb : 0 ≤ b) (n : ℕ) : 0 < jacobiMoment κ a b n := by
  induction n with
  | zero => simp [jacobiMoment]
  | succ n ih =>
    rw [jacobiMoment]
    have hc := ccoef_neg hκ (by linarith : 0 < a + b) (Nat.le_add_left 1 n)
    have hd := dcoef_pos hκ ha (Nat.le_add_left 1 n)
    exact mul_pos ih (div_pos hd (by linarith))

/-- The ratio `m_{n+1}/m_n = d_{n+1}/(−c_{n+1})` exceeds any `α < 1` for large `n` (`κ > 0`). -/
theorem exists_ratio_gt (hκ : 0 < κ) (ha : 0 < a) (hb : 0 ≤ b) {α : ℝ} (hα1 : α < 1) :
    ∃ m : ℕ, α * jacobiMoment κ a b m < jacobiMoment κ a b (m + 1) := by
  have h1α : 0 < 1 - α := by linarith
  have hk : 0 < (1 - α) * (κ / 4) := by positivity
  obtain ⟨m, hm⟩ := exists_nat_gt ((α * (a + b) / 2 - a / 2) / ((1 - α) * (κ / 4)))
  have hm' : α * (a + b) / 2 - a / 2 < m * ((1 - α) * (κ / 4)) := by rwa [div_lt_iff₀ hk] at hm
  refine ⟨m, ?_⟩
  have hc := ccoef_neg hκ.le (by linarith : 0 < a + b) (Nat.le_add_left 1 m)
  have hpos := jacobiMoment_pos hκ.le ha hb m
  have hratio : α < dcoef κ a (m + 1) / -ccoef κ a b (m + 1) := by
    rw [lt_div_iff₀ (by linarith)]
    simp only [dcoef, ccoef, neg_neg]
    push_cast
    have key := mul_lt_mul_of_pos_left hm' (show (0 : ℝ) < m + 1 by positivity)
    nlinarith [key]
  rw [jacobiMoment]
  calc α * jacobiMoment κ a b m < (dcoef κ a (m + 1) / -ccoef κ a b (m + 1)) * jacobiMoment κ a b m :=
        mul_lt_mul_of_pos_right hratio hpos
    _ = _ := mul_comm _ _

end MomentConv

/-! ### The angle exceeds every level after every time -/

section Exceed

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {κ a b : ℝ}
  {U : ℝ → Ω → ℝ}

/-- Conditional moments of a nonnegative past functional converge to the beta moments, uniformly. -/
theorem jmp_mo_conv (hU : IsJacobiMP κ a b P U) (hκ : 0 ≤ κ) (ha : 0 < a) (hb : 0 ≤ b) (k : ℕ) {ε : ℝ}
    (hε : 0 < ε) : ∃ T : ℝ, 0 ≤ T ∧ ∀ (w : ℝ) (F : Ω → ℝ), F ∈ pastSpan U w → (∀ ω, 0 ≤ F ω) →
      ∀ x, w + T ≤ x → |mo P U F k x - jacobiMoment κ a b k * ∫ ω, F ω ∂P| ≤ ε * ∫ ω, F ω ∂P := by
  obtain ⟨T, hT, hTφ⟩ := moment_system_conv hκ ha hb k ε hε
  refine ⟨T, hT, fun w F hF hF0 x hx => ?_⟩
  obtain ⟨hFm, ⟨C, hC⟩, hode⟩ := jmp_goodPast_of_mem hU hF
  refine hTφ (fun j => mo P U F j) (∫ ω, F ω ∂P) w (integral_nonneg hF0)
    (fun j => jmp_continuous_mo hU hFm hC j) (fun x _ => by simp [mo]) (fun j x _ => ⟨?_, ?_⟩)
    (fun j x' x _ hwx' hx'x => hode j x' x hwx' hx'x) x hx
  · exact integral_nonneg fun ω => mul_nonneg (hF0 ω) (hU.pow_mem_Icc x ω j).1
  · refine integral_mono (jmp_integrable_mul_pow hU hFm hC j x) (Integrable.of_bound hFm.aestronglyMeasurable C
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hC ω)) fun ω => ?_
    have := hU.pow_mem_Icc x ω j
    nlinarith [hF0 ω, this.1, this.2]

/-- The test polynomial `q(y) = 1 − y^m (y − α)/(1 − α)`: `≥ 1` on `[0, α]`, `≥ 0` on `[0, 1]`. -/
def qTest (m : ℕ) (α y : ℝ) : ℝ := 1 - y ^ m * (y - α) / (1 - α)

theorem one_le_qTest {m : ℕ} {α y : ℝ} (hα1 : α < 1) (hy0 : 0 ≤ y) (hyα : y ≤ α) : 1 ≤ qTest m α y := by
  have h1 : y ^ m * (y - α) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hy0 m) (by linarith)
  have h2 : y ^ m * (y - α) / (1 - α) ≤ 0 := div_nonpos_of_nonpos_of_nonneg h1 (by linarith)
  simp only [qTest]; linarith

theorem qTest_nonneg {m : ℕ} {α y : ℝ} (hα1 : α < 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    0 ≤ qTest m α y := by
  rcases le_total y α with hyα | hyα
  · exact zero_le_one.trans (one_le_qTest hα1 hy.1 hyα)
  · have h1 : y ^ m * (y - α) ≤ 1 * (1 - α) :=
      mul_le_mul (pow_le_one₀ hy.1 hy.2) (by linarith [hy.2]) (by linarith) zero_le_one
    have h2 : y ^ m * (y - α) / (1 - α) ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith
    simp only [qTest]; linarith

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
/-- `q(U_s) F` stays in the span. -/
theorem qTest_mul_mem_pastSpan {w s : ℝ} (hs : s ≤ w) (m : ℕ) (α : ℝ) {F : Ω → ℝ} (hF : F ∈ pastSpan U w) :
    (fun ω => qTest m α (U s ω) * F ω) ∈ pastSpan U w := by
  have e : (fun ω => qTest m α (U s ω) * F ω) =
      F - (1 / (1 - α)) • ((fun ω => U s ω ^ (m + 1) * F ω) - α • fun ω => U s ω ^ m * F ω) := by
    funext ω
    simp only [qTest, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, pow_succ]
    ring
  rw [e]
  exact sub_mem hF (Submodule.smul_mem _ _ (sub_mem (pow_mul_mem_pastSpan hs _ hF)
    (Submodule.smul_mem _ _ (pow_mul_mem_pastSpan hs _ hF))))

/-- **One crossing step.** There are `T ≥ 0` and `θ ∈ [0, 1)` such that `E[F q(U_x)] ≤ θ E[F]` for every nonnegative
past functional `F` at time `w` and every `x ≥ w + T`. -/
theorem jmp_crossing (hU : IsJacobiMP κ a b P U) (hκ : 0 < κ) (ha : 0 < a) (hb : 0 ≤ b) {α : ℝ} (hα0 : 0 < α)
    (hα1 : α < 1) : ∃ (m : ℕ) (T θ : ℝ), 0 ≤ T ∧ 0 ≤ θ ∧ θ < 1 ∧ ∀ (w : ℝ) (F : Ω → ℝ), F ∈ pastSpan U w →
      (∀ ω, 0 ≤ F ω) → ∀ x, w + T ≤ x →
        ∫ ω, qTest m α (U x ω) * F ω ∂P ≤ θ * ∫ ω, F ω ∂P := by
  obtain ⟨m, hm⟩ := exists_ratio_gt hκ ha hb hα1
  set δ := jacobiMoment κ a b (m + 1) - α * jacobiMoment κ a b m with hδ
  have hδ0 : 0 < δ := by linarith
  set ε := δ / (2 * (1 + α)) with hεdef
  have hε : 0 < ε := by positivity
  obtain ⟨T₁, hT₁, h₁⟩ := jmp_mo_conv hU hκ.le ha hb (m + 1) hε
  obtain ⟨T₂, hT₂, h₂⟩ := jmp_mo_conv hU hκ.le ha hb m hε
  set c₀ := δ / (2 * (1 - α)) with hc₀
  have hc₀0 : 0 < c₀ := by have : 0 < 1 - α := by linarith
                           positivity
  refine ⟨m, max T₁ T₂, max (1 - c₀) 0, le_max_of_le_left hT₁, le_max_right _ _,
    max_lt (by linarith) (by norm_num), fun w F hF hF0 x hx => ?_⟩
  obtain ⟨hFm, ⟨C, hC⟩, -⟩ := jmp_goodPast_of_mem hU hF
  set A := ∫ ω, F ω ∂P with hA
  have hA0 : 0 ≤ A := integral_nonneg hF0
  have i0 : Integrable F P := Integrable.of_bound hFm.aestronglyMeasurable C
    (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hC ω)
  have i1 := jmp_integrable_mul_pow hU hFm hC (m + 1) x
  have i2 := jmp_integrable_mul_pow hU hFm hC m x
  have hsplit : ∫ ω, qTest m α (U x ω) * F ω ∂P =
      A - (1 / (1 - α)) * (mo P U F (m + 1) x - α * mo P U F m x) := by
    have e : (fun ω => qTest m α (U x ω) * F ω) = fun ω =>
        F ω - (1 / (1 - α)) * (F ω * U x ω ^ (m + 1) - α * (F ω * U x ω ^ m)) := by
      funext ω; simp only [qTest]; ring
    have i2' : Integrable (fun ω => α * (F ω * U x ω ^ m)) P := i2.const_mul α
    have i3 : Integrable (fun ω => 1 / (1 - α) * (F ω * U x ω ^ (m + 1) - α * (F ω * U x ω ^ m))) P :=
      (i1.sub i2').const_mul _
    rw [e, integral_sub i0 i3, integral_const_mul, integral_sub i1 i2', integral_const_mul]
    rfl
  have hb₁ := h₁ w F hF hF0 x (le_trans (by linarith [le_max_left T₁ T₂]) hx)
  have hb₂ := h₂ w F hF hF0 x (le_trans (by linarith [le_max_right T₁ T₂]) hx)
  rw [abs_le] at hb₁ hb₂
  have hlow : (δ / 2) * A ≤ mo P U F (m + 1) x - α * mo P U F m x := by
    have e1 : (δ / 2) * A = jacobiMoment κ a b (m + 1) * A - ε * A -
        α * (jacobiMoment κ a b m * A + ε * A) := by
      rw [hεdef, hδ]; field_simp; ring
    rw [e1]
    have := mul_le_mul_of_nonneg_left hb₂.2 hα0.le
    linarith [hb₁.1]
  have hfac : (1 / (1 - α)) * ((δ / 2) * A) = c₀ * A := by
    rw [hc₀]; have : (1 - α) ≠ 0 := by linarith
    field_simp
  have h1α : 0 ≤ 1 / (1 - α) := by have : 0 < 1 - α := by linarith
                                   positivity
  rw [hsplit]
  have := mul_le_mul_of_nonneg_left hlow h1α
  rw [hfac] at this
  calc A - 1 / (1 - α) * (mo P U F (m + 1) x - α * mo P U F m x) ≤ (1 - c₀) * A := by linarith
    _ ≤ max (1 - c₀) 0 * A := mul_le_mul_of_nonneg_right (le_max_left _ _) hA0

/-- **The angle exceeds every level after every time.** For a solution of the Jacobi martingale problem
(`κ > 0`, `a > 0`, `b ≥ 0`), every `α ∈ (0, 1)` and every `u₀`, almost surely `U_u > α` for some `u ≥ u₀`. -/
theorem jmp_ae_exists_gt (hU : IsJacobiMP κ a b P U) (hκ : 0 < κ) (ha : 0 < a) (hb : 0 ≤ b) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (u₀ : ℝ) : ∀ᵐ ω ∂P, ∃ u, u₀ ≤ u ∧ α < U u ω := by
  obtain ⟨m, T, θ, hT, hθ0, hθ1, hcross⟩ := jmp_crossing hU hκ ha hb hα0 hα1
  set s : ℕ → ℝ := fun j => u₀ + ((j : ℝ) + 1) * T with hs
  set G : ℕ → Ω → ℝ := fun N ω => ∏ j ∈ Finset.range N, qTest m α (U (s j) ω) with hG
  have hGsucc : ∀ N, G (N + 1) = fun ω => qTest m α (U (s N) ω) * G N ω := fun N => by
    funext ω; simp only [hG, Finset.prod_range_succ, mul_comm]
  have hsN : ∀ N : ℕ, s N = u₀ + ((N : ℝ) * T) + T := fun N => by simp only [hs]; ring
  have hGmem : ∀ N : ℕ, G N ∈ pastSpan U (u₀ + (N : ℝ) * T) := by
    intro N
    induction N with
    | zero =>
      have : G 0 = fun _ => (1 : ℝ) := by funext ω; simp [hG]
      rw [this]; exact one_mem_pastSpan _
    | succ N ih =>
      rw [hGsucc N]
      have hle : u₀ + (N : ℝ) * T ≤ u₀ + ((N + 1 : ℕ) : ℝ) * T := by push_cast; nlinarith
      refine qTest_mul_mem_pastSpan (le_of_eq ?_) m α (pastSpan_mono hle ih)
      rw [hsN]; push_cast; ring
  have hG0 : ∀ N ω, 0 ≤ G N ω := fun N ω =>
    Finset.prod_nonneg fun j _ => qTest_nonneg hα1 (hU.mem_Icc _ _)
  have hGint : ∀ N, Integrable (G N) P := fun N => by
    obtain ⟨hm, ⟨C, hC⟩, -⟩ := jmp_goodPast_of_mem hU (hGmem N)
    exact Integrable.of_bound hm.aestronglyMeasurable C (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs]; exact hC ω)
  have hGθ : ∀ N, ∫ ω, G N ω ∂P ≤ θ ^ N := by
    intro N
    induction N with
    | zero => simp [hG]
    | succ N ih =>
      rw [hGsucc N]
      calc ∫ ω, qTest m α (U (s N) ω) * G N ω ∂P ≤ θ * ∫ ω, G N ω ∂P :=
            hcross _ (G N) (hGmem N) (hG0 N) (s N) (by rw [hsN])
        _ ≤ θ * θ ^ N := mul_le_mul_of_nonneg_left ih hθ0
        _ = θ ^ (N + 1) := by ring
  set E : ℕ → Set Ω := fun N => {ω | ∀ j < N, U (s j) ω ≤ α} with hE
  have hEG : ∀ N ω, ω ∈ E N → 1 ≤ G N ω := by
    intro N
    induction N with
    | zero => intro ω _; simp [hG]
    | succ N ih =>
      intro ω hω
      rw [hGsucc N]
      have h1 := one_le_qTest (m := m) hα1 (hU.mem_Icc (s N) ω).1 (hω N (Nat.lt_succ_self N))
      have h2 := ih ω fun j hj => hω j (Nat.lt_succ_of_lt hj)
      nlinarith
  have hPE : ∀ N, P (E N) ≤ ENNReal.ofReal (θ ^ N) := by
    intro N
    have h1 := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ (hG0 N)) (hGint N) 1
    rw [one_mul] at h1
    calc P (E N) ≤ P {ω | 1 ≤ G N ω} := measure_mono fun ω h => hEG N ω h
      _ = ENNReal.ofReal (P.real {ω | 1 ≤ G N ω}) := (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
      _ ≤ ENNReal.ofReal (θ ^ N) := ENNReal.ofReal_le_ofReal (h1.trans (hGθ N))
  have hnull : P (⋂ N, E N) = 0 := by
    have hlim : Tendsto (fun N => ENNReal.ofReal (θ ^ N)) atTop (𝓝 0) := by
      rw [← ENNReal.ofReal_zero]
      exact ENNReal.tendsto_ofReal (tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ1)
    exact le_antisymm (ge_of_tendsto' hlim fun N => (measure_mono (iInter_subset _ N)).trans (hPE N))
      bot_le
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with ω hω
  simp only [mem_iInter, not_forall, hE, mem_ofPred_eq, not_le] at hω
  obtain ⟨N, j, -, hj⟩ := hω
  refine ⟨s j, ?_, hj⟩
  simp only [hs]
  have : 0 ≤ ((j : ℝ) + 1) * T := by positivity
  linarith

end Exceed

/-! ### The two-seed gap ratio -/

section TwoSeed

open Sec2.TwoSeed

variable {κ : ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {ρL ρR : Fin 1 → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

/-- **One side of the recurrence**: for a two-seed evolution with weights `> −2` and infinite lifetime, and every
`r > 0`, almost surely `R_t < r L_t` at some time `t ≥ 1` (the log-clock angle `L/(L+R)` exceeds `1/(1+r)` after every
time, `jmp_ae_exists_gt`). -/
theorem ae_exists_ratio_lt [IsProbabilityMeasure P] (hκ : 0 < κ) (hρL : -2 < ρL 0) (hρR : -2 < ρR 0)
    (hE : IsIntegratedSLEEvolution κ (fun _ => 0) (fun _ => 0) ρL ρR P 𝓕 W VL VR B ζ)
    (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ ω ∂P, ∃ t : ℝ≥0, 1 ≤ t ∧ VR 0 t ω - W t ω < r * (W t ω - VL 0 t ω) := by
  obtain ⟨G, hGm, hGc, hgood⟩ := exists_good hE
  have hJ := isJacobiMP_angleG hE hρL hρR hGm hGc hgood hκ
  set α : ℝ := 1 / (1 + r) with hα
  have hα0 : 0 < α := by positivity
  have hα1 : α < 1 := by rw [hα, div_lt_one (by linarith)]; linarith
  have hρL' : ∀ i, -2 < ρL i := fun i => by rw [Fin.fin_one_eq_zero i]; exact hρL
  have hρR' : ∀ i, -2 < ρR i := fun i => by rw [Fin.fin_one_eq_zero i]; exact hρR
  have hrat : ∀ᵐ ω ∂P, ∀ q : ℚ, ∃ u, (q : ℝ) ≤ u ∧ α < angleG G W VL VR ζ u ω := by
    rw [ae_all_iff]; intro q
    exact jmp_ae_exists_gt hJ hκ (by linarith) (by linarith) hα0 hα1 q
  filter_upwards [hrat, hζ, ae_of_all _ fun ω (h : ω ∈ G) => h, measure_eq_zero_iff_ae_notMem.1 hGc]
    with ω hq hζω _ hGω
  have hωG : ω ∈ G := by simpa using hGω
  obtain ⟨hp, -, -⟩ := hgood ω hωG
  rw [hζω] at hp
  -- the separation at time `1` and a rational log-level above it
  have h1 : (((1 : ℝ≥0)) : ℝ≥0∞) < ⊤ := ENNReal.coe_lt_top
  have hsep1 := sepN_pos hp h1 one_pos
  obtain ⟨q, hq1⟩ := exists_rat_gt (Real.log (sepN (fun i t => VL i t ω) (fun i t => VR i t ω) 1))
  obtain ⟨u, hqu, hαu⟩ := hq q
  simp only [angleG, hωG, ↓reduceIte] at hαu
  rw [hζω] at hαu
  -- a time at which the separation is `e^u`
  obtain ⟨t₀, ht₀, hut₀⟩ := sepN_unbounded_of_top hp (Real.exp u)
  obtain ⟨hτt₀, hτ⟩ := hitTime_spec hp ht₀ hut₀
  set τ := hitTime (fun i t => VL i t ω) (fun i t => VR i t ω) ⊤ u with hτdef
  refine ⟨τ, ?_, ?_⟩
  · -- `τ ≥ 1`: otherwise the separation at `τ` would be below that at `1`
    by_contra hlt
    push Not at hlt
    have hlt' := sepN_lt_sepN hp (show ((1 : ℝ≥0) : ℝ≥0∞) < ⊤ from h1) hlt le_rfl
    rw [hτ] at hlt'
    have : Real.log (sepN (fun i t => VL i t ω) (fun i t => VR i t ω) 1) < u := lt_of_lt_of_le hq1 hqu
    have := Real.exp_lt_exp.2 this
    rw [Real.exp_log hsep1] at this
    linarith
  · -- `L > α e^u = α (L + R)`, so `R < r L`
    have hlog : α < (W τ ω - VL 0 τ ω) / Real.exp u := hαu
    rw [lt_div_iff₀ (Real.exp_pos u), ← hτ] at hlog
    simp only [sepN] at hlog
    have hrα : r * α = 1 - α := by rw [hα]; field_simp; ring
    have h3 := mul_lt_mul_of_pos_left hlog hr
    rw [← mul_assoc, hrα, sub_mul, one_mul] at h3
    linarith

/-- **Recurrence of the two-seed gap ratio** (B.3 (E13)): the named statement holds for every `κ > 0`. -/
theorem twoSeedRatioRecurrenceStatement (hκ : 0 < κ) : TwoSeedRatioRecurrenceStatement.{u} κ := by
  intro ρL ρR hadm Ω mΩ P _ 𝓕 W VL VR B ζ hE r hr
  have hκc : -2 < κ / 2 - 2 := by linarith
  obtain ⟨hwL, hwR⟩ : κ / 2 - 2 ≤ ρL 0 ∧ κ / 2 - 2 ≤ ρR 0 := by
    have h1 := hadm.1 (-1) (by norm_num) ⟨0, by norm_num⟩
    have h2 := hadm.2 0 le_rfl ⟨0, le_rfl⟩
    have hf1 : (Finset.univ.filter fun i : Fin 1 => (-1 : ℝ) < (fun _ => (0 : ℝ)) i) = Finset.univ := by
      ext i; simp
    have hf2 : (Finset.univ.filter fun i : Fin 1 => (fun _ => (0 : ℝ)) i ≤ 0) = Finset.univ := by
      ext i; simp
    rw [hf1, Fin.sum_univ_one] at h1
    rw [hf2, Fin.sum_univ_one] at h2
    exact ⟨h1, h2⟩
  have hρL : -2 < ρL 0 := by linarith
  have hρR : -2 < ρR 0 := by linarith
  have hζ : ∀ᵐ ω ∂P, ζ ω = ⊤ :=
    (Sec4.aux6Statement hκ _ _ ρL ρR P 𝓕 W VL VR B ζ Zhan.isOrderedForceWord_zero hadm hE).mono fun _ h => h.1
  -- the reflected evolution is a two-seed evolution with the weights exchanged
  have hEr := hE.reflect
  have hz : -(fun _ : Fin 1 => (0 : ℝ)) = fun _ => 0 := by funext i; simp
  rw [hz] at hEr
  have hlt := ae_exists_ratio_lt hκ hρL hρR hE hζ hr
  have hgt := ae_exists_ratio_lt hκ hρR hρL hEr hζ (inv_pos.2 hr)
  filter_upwards [hlt, hgt, hE.2.2.2.2, hζ] with ω ⟨t₁, ht₁, h₁⟩ ⟨t₂, ht₂, h₂⟩ hp hζω
  -- `h₂ : (−V_L) − (−W) < r⁻¹ ((−W) − (−V_R))`, i.e. `r L < R`
  simp only [Pi.neg_apply] at h₂
  have h₂' : r * (W t₂ ω - VL 0 t₂ ω) < VR 0 t₂ ω - W t₂ ω := by
    have := mul_lt_mul_of_pos_left h₂ hr
    rw [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul] at this
    linarith
  -- intermediate values of `R − r L`
  have hcont : ∀ {f : ℝ≥0 → ℝ}, ContinuousOn f {t | (t : ℝ≥0∞) < ζ ω} → Continuous f := fun hf =>
    continuousOn_univ.1 (hf.mono fun t _ => by
      show (t : ℝ≥0∞) < ζ ω
      rw [hζω]; exact ENNReal.coe_lt_top)
  have hY : Continuous fun t : ℝ≥0 => (VR 0 t ω - W t ω) - r * (W t ω - VL 0 t ω) :=
    ((hcont (hp.2.2.2.2.2.1 0)).sub (hcont hp.2.2.2.1)).sub
      (continuous_const.mul ((hcont hp.2.2.2.1).sub (hcont (hp.2.2.2.2.1 0))))
  have hY₁ : (VR 0 t₁ ω - W t₁ ω) - r * (W t₁ ω - VL 0 t₁ ω) ≤ 0 := by linarith
  have hY₂ : 0 ≤ (VR 0 t₂ ω - W t₂ ω) - r * (W t₂ ω - VL 0 t₂ ω) := by linarith
  rcases le_total t₁ t₂ with h12 | h21
  · obtain ⟨t, ht, hYt⟩ := intermediate_value_Icc h12 hY.continuousOn ⟨hY₁, hY₂⟩
    exact ⟨t, ht₁.trans ht.1, by linarith⟩
  · obtain ⟨t, ht, hYt⟩ := intermediate_value_Icc' h21 hY.continuousOn ⟨hY₁, hY₂⟩
    exact ⟨t, ht₂.trans ht.1, by linarith⟩

end TwoSeed

/-! ### Consequences: the two-force bases -/

section Bases

variable {κ : ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {xL xR ρL ρR : Fin 1 → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL VR : Fin 1 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

/-- **Separated two-force transience for `0 < κ ≤ 4`** (B.3; additional note Lemma 1.7), unconditionally: marks
`x_L < 0 < x_R`, weights `ρ_L, ρ_R ≥ κ/2 − 2`. -/
theorem IsIntegratedSLEEvolution.ae_tendsto_norm_trace_twoForce_le_four (hκ : 0 < κ) (hκ4 : κ ≤ 4)
    (hxL : xL 0 < 0) (hxR : 0 < xR 0) (hadm : Sec4.HasAdmissiblePartialSums κ ρL ρR xL xR)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η →
      Tendsto (fun t => ‖η t‖) atTop atTop :=
  IsIntegratedSLEEvolution.ae_tendsto_norm_trace_twoForce_of_le_four hκ hκ4
    (twoSeedRatioRecurrenceStatement hκ) hxL hxR hadm hE

/-- **Separated two-force transience for every `κ > 0` from Lemma 3.4 alone** (the absence of real terminal cluster
points for separated two-force laws, `SeparatedNoRealClusterStatement κ`). -/
theorem IsIntegratedSLEEvolution.ae_tendsto_norm_trace_twoForce_of_noCluster (hκ : 0 < κ)
    (hN : SeparatedNoRealClusterStatement.{0} κ) (hxL : xL 0 < 0) (hxR : 0 < xR 0)
    (hadm : Sec4.HasAdmissiblePartialSums κ ρL ρR xL xR)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η →
      Tendsto (fun t => ‖η t‖) atTop atTop :=
  IsIntegratedSLEEvolution.ae_tendsto_norm_trace_twoForce_of_separatedNoCluster hκ
    (twoSeedRatioRecurrenceStatement hκ) hN hxL hxR hadm hE

end Bases

end InteractingSLE.ZhanGT4
