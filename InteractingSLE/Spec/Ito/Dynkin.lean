import QuantumZipper.Proofs.ItoLite.Dynkin
import InteractingSLE.Frozen.Spec.IsFilteredBrownianReal
import InteractingSLE.Spec.Ito.ACChain

/-!
# Itô's formula for `F(Λ_t, B_t)` in an arbitrary filtration

Packet PROVE-T11-ITO. The integrated `SLE_κ(ρ)` evolution of Definition 2.1 is a *weak* solution: `B`
is a Brownian motion in some filtration `𝓕` to which `W, V^{i,q}` are adapted, and `W, V` need not be
functions of `B`. The vendored Itô calculus (`vendor/formal-mathfin`) is built on the natural filtration
of `B` only, so it does not apply. This file proves the case of Itô's formula that Section 3.3 uses,
for an arbitrary filtration and without a stochastic integral (Revuz–Yor IV.3.3, in the form of a
martingale problem; the proof follows the Taylor-expansion argument of QuantumZipper's
`Dynkin.dynkin_additive`):

**`martingale_itoDynkin`.** Let `B` be an `𝓕`-Brownian motion with every path continuous, let
`Λ : ℝ≥0 → Ω → E` (finite-dimensional `E`) be `𝓕`-adapted with absolutely continuous paths
`Λ_t = Λ_0 + ∫₀ᵗ λ_s ds` of uniformly bounded variation `∫ ‖λ‖ ≤ K`, and let `F : E × ℝ → ℝ` be `C³`
with compact support. Then

`F(Λ_t, B_t) − ∫₀ᵗ (∂_Λ F(Λ_s, B_s) λ_s + ½ ∂²_x F(Λ_s, B_s)) ds`

is an `𝓕`-martingale.

The density `λ` is only integrable (not continuous, not assumed measurable in `ω`); adaptedness of the
drift integral comes from its Riemann–Stieltjes sums (`tendsto_riemannSum_clm`), and the time-steps use
the chain rule for absolutely continuous paths (`comp_eq_add_integral_of_lipschitz`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE

/-! ### Brownian increments in a filtration -/

namespace IsFilteredBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {B : ℝ≥0 → Ω → ℝ}

theorem isProbabilityMeasure' (hB : IsFilteredBrownianReal 𝓕 B P) :
    IsProbabilityMeasure P :=
  hB.1.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure

theorem measurable' (hB : IsFilteredBrownianReal 𝓕 B P) (t : ℝ≥0) :
    Measurable (B t) :=
  (hB.2.1 t).mono (𝓕.le t) le_rfl

theorem incr_eq_shift {a b : ℝ≥0} (hab : a ≤ b) :
    (fun ω => B b ω - B a ω) = fun ω => B (a + (b - a)) ω - B a ω := by
  rw [add_tsub_cancel_of_le hab]

theorem integral_incr (hB : IsFilteredBrownianReal 𝓕 B P) {a b : ℝ≥0}
    (hab : a ≤ b) : ∫ ω, (B b ω - B a ω) ∂P = 0 := by
  rw [incr_eq_shift hab]
  exact QuantumZipper.integral_eq_zero (hB.1.toIsPreBrownianReal.shift a) (b - a)

theorem integral_incr_sq (hB : IsFilteredBrownianReal 𝓕 B P) {a b : ℝ≥0}
    (hab : a ≤ b) : ∫ ω, (B b ω - B a ω) ^ 2 ∂P = (b : ℝ) - a := by
  have h := QuantumZipper.integral_sq (hB.1.toIsPreBrownianReal.shift a) (b - a)
  rwa [add_tsub_cancel_of_le hab, NNReal.coe_sub hab] at h

theorem integrable_abs_incr_pow (hB : IsFilteredBrownianReal 𝓕 B P)
    {a b : ℝ≥0} (hab : a ≤ b) (n : ℕ) : Integrable (fun ω => |B b ω - B a ω| ^ n) P := by
  have h := QuantumZipper.integrable_pow (hB.1.toIsPreBrownianReal.shift a) (b - a) n
  rwa [add_tsub_cancel_of_le hab] at h

theorem integrable_incr (hB : IsFilteredBrownianReal 𝓕 B P) {a b : ℝ≥0}
    (hab : a ≤ b) : Integrable (fun ω => B b ω - B a ω) P := by
  have h := hB.integrable_abs_incr_pow hab 1
  simp only [pow_one] at h
  exact h.mono' ((hB.measurable' b).sub (hB.measurable' a)).aestronglyMeasurable
    (Eventually.of_forall fun ω => le_of_eq (Real.norm_eq_abs _))

theorem integrable_incr_sq (hB : IsFilteredBrownianReal 𝓕 B P)
    {a b : ℝ≥0} (hab : a ≤ b) : Integrable (fun ω => (B b ω - B a ω) ^ 2) P := by
  have h := hB.integrable_abs_incr_pow hab 2
  exact h.congr (Eventually.of_forall fun ω => by simp only [sq_abs])

theorem integral_abs_incr_pow_three_le
    (hB : IsFilteredBrownianReal 𝓕 B P) {a b : ℝ≥0} (hab : a ≤ b) :
    ∫ ω, |B b ω - B a ω| ^ 3 ∂P ≤
      QuantumZipper.gaussianAbsMoment 3 * (((b : ℝ) - a) * Real.sqrt ((b : ℝ) - a)) := by
  have h := QuantumZipper.integral_abs_pow_le (hB.1.toIsPreBrownianReal.shift a) (b - a) 3
  rw [add_tsub_cancel_of_le hab, NNReal.coe_sub hab] at h
  have hba : (0 : ℝ) ≤ (b : ℝ) - a := sub_nonneg.2 (NNReal.coe_le_coe.2 hab)
  rwa [show ((3 : ℕ) : ℝ) / 2 = ((3 : ℕ) : ℝ) / 2 from rfl,
    QuantumZipper.Dynkin.rpow_three_halves_eq hba] at h

/-- Independence of a Brownian increment from `𝓕_a`: `E[g φ(B_b − B_a)] = E[g] E[φ(B_b − B_a)]` for
`𝓕_a`-measurable `g`. -/
theorem integral_mul_incr (hB : IsFilteredBrownianReal 𝓕 B P)
    {a b : ℝ≥0} (hab : a ≤ b) {g : Ω → ℝ} (hg : Measurable[𝓕 a] g) {φ : ℝ → ℝ}
    (hφ : Measurable φ) :
    ∫ ω, g ω * φ (B b ω - B a ω) ∂P = (∫ ω, g ω ∂P) * ∫ ω, φ (B b ω - B a ω) ∂P := by
  have hY : Measurable[MeasurableSpace.comap (fun ω => B b ω - B a ω) inferInstance]
      (fun ω => φ (B b ω - B a ω)) :=
    hφ.comp (Measurable.of_comap_le le_rfl)
  have hind : IndepFun g (fun ω => φ (B b ω - B a ω)) P := by
    rw [IndepFun_iff_Indep]
    exact indep_of_indep_of_le (hB.2.2 a b hab).symm hg.comap_le hY.comap_le
  have hgm : Measurable g := hg.mono (𝓕.le a) le_rfl
  have hYm : Measurable (fun ω => φ (B b ω - B a ω)) :=
    hφ.comp ((hB.measurable' b).sub (hB.measurable' a))
  simpa only [Pi.mul_apply] using
    hind.integral_mul_eq_mul_integral hgm.aestronglyMeasurable hYm.aestronglyMeasurable

end IsFilteredBrownianReal

namespace Ito

/-! ### Bounds for a compactly supported `C³` function -/

section Bounds

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {F : G → ℝ}

/-- A `C³` function with compact support has bounded value, first and second derivatives, and
Lipschitz first and second derivatives (one constant for all). -/
theorem exists_bound_of_contDiff_three (hF : ContDiff ℝ 3 F) (hFc : HasCompactSupport F) :
    ∃ C, 0 ≤ C ∧ (∀ p, |F p| ≤ C) ∧ (∀ p, ‖fderiv ℝ F p‖ ≤ C) ∧
      (∀ p, ‖fderiv ℝ (fderiv ℝ F) p‖ ≤ C) ∧
      (∀ p q, ‖fderiv ℝ F p - fderiv ℝ F q‖ ≤ C * ‖p - q‖) ∧
      (∀ p q, ‖fderiv ℝ (fderiv ℝ F) p - fderiv ℝ (fderiv ℝ F) q‖ ≤ C * ‖p - q‖) ∧
      (∀ p q, ‖iteratedFDeriv ℝ 2 F p - iteratedFDeriv ℝ 2 F q‖ ≤ C * ‖p - q‖) := by
  have hF1 : ContDiff ℝ 2 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
  have hF2 : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ F)) := hF1.fderiv_right (by norm_num)
  have hc1 := hFc.fderiv ℝ
  have hc2 := hc1.fderiv ℝ
  have hc3 := hc2.fderiv ℝ
  obtain ⟨C0, hC0⟩ := hF.continuous.bounded_above_of_compact_support hFc
  obtain ⟨C1, hC1⟩ := (hF.continuous_fderiv (by norm_num)).bounded_above_of_compact_support hc1
  obtain ⟨C2, hC2⟩ := (hF1.continuous_fderiv (by norm_num)).bounded_above_of_compact_support hc2
  obtain ⟨C3, hC3⟩ := (hF2.continuous_fderiv (by norm_num)).bounded_above_of_compact_support hc3
  obtain ⟨C4, hC4⟩ := (hF.continuous_iteratedFDeriv (m := 3) (by norm_num)).bounded_above_of_compact_support
    (hFc.iteratedFDeriv 3)
  have h0 : ∀ p, 0 ≤ C0 := fun p => (norm_nonneg _).trans (hC0 p)
  refine ⟨|C0| + |C1| + |C2| + |C3| + |C4|, by positivity, fun p => ?_, fun p => ?_, fun p => ?_,
    fun p q => ?_, fun p q => ?_, fun p q => ?_⟩
  · have := hC0 p; rw [Real.norm_eq_abs] at this
    linarith [le_abs_self C0, abs_nonneg C1, abs_nonneg C2, abs_nonneg C3, abs_nonneg C4]
  · linarith [hC1 p, le_abs_self C1, abs_nonneg C0, abs_nonneg C2, abs_nonneg C3, abs_nonneg C4]
  · linarith [hC2 p, le_abs_self C2, abs_nonneg C0, abs_nonneg C1, abs_nonneg C3, abs_nonneg C4]
  · have h := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (s := Set.univ)
      (f := fderiv ℝ F) (C := C2) (fun x _ => (hF1.differentiable (by norm_num)) x)
      (fun x _ => hC2 x) convex_univ (Set.mem_univ q) (Set.mem_univ p)
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    linarith [le_abs_self C2, abs_nonneg C0, abs_nonneg C1, abs_nonneg C3, abs_nonneg C4]
  · have h := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (s := Set.univ)
      (f := fderiv ℝ (fderiv ℝ F)) (C := C3) (fun x _ => (hF2.differentiable (by norm_num)) x)
      (fun x _ => hC3 x) convex_univ (Set.mem_univ q) (Set.mem_univ p)
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    linarith [le_abs_self C3, abs_nonneg C0, abs_nonneg C1, abs_nonneg C2, abs_nonneg C4]
  · have h := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (s := Set.univ)
      (f := iteratedFDeriv ℝ 2 F) (C := C4)
      (fun x _ => (hF.differentiable_iteratedFDeriv (m := 2) (by norm_num)) x)
      (fun x _ => by rw [norm_fderiv_iteratedFDeriv]; exact hC4 x) convex_univ
      (Set.mem_univ q) (Set.mem_univ p)
    refine h.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    linarith [le_abs_self C4, abs_nonneg C0, abs_nonneg C1, abs_nonneg C2, abs_nonneg C3]

end Bounds

/-! ### Riemann–Stieltjes sums along an absolutely continuous path -/

section Riemann

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem intervalIntegrable_clm_apply {c : ℝ → E →L[ℝ] ℝ} {lam : ℝ → E} {a b : ℝ}
    (hc : ContinuousOn c (uIcc a b)) (hlam : IntervalIntegrable lam volume a b) :
    IntervalIntegrable (fun s => c s (lam s)) volume a b := by
  obtain ⟨C, hC⟩ := isCompact_uIcc.exists_bound_of_continuousOn hc
  refine (hlam.norm.const_mul C).mono_fun' ?_ ?_
  · have hm1 : AEStronglyMeasurable c (volume.restrict (uIoc a b)) :=
      (hc.mono uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
    have hm2 : AEStronglyMeasurable lam (volume.restrict (uIoc a b)) :=
      (intervalIntegrable_iff.1 hlam).aestronglyMeasurable
    exact (continuous_fst.clm_apply continuous_snd :
      Continuous fun p : (E →L[ℝ] ℝ) × E => p.1 p.2).comp_aestronglyMeasurable₂ hm1 hm2
  · refine (ae_restrict_iff' measurableSet_uIoc).2 (Eventually.of_forall fun s hs => ?_)
    exact ((c s).le_opNorm (lam s)).trans
      (mul_le_mul_of_nonneg_right (hC s (uIoc_subset_uIcc hs)) (norm_nonneg _))

/-- **Riemann–Stieltjes sums along an absolutely continuous path.** If `Λ s = Λ 0 + ∫₀ˢ λ` on
`[0, t]` with `λ` integrable and `c` is continuous on `[0, t]`, the left-point sums
`∑ₖ c(tₖ)(Λ(tₖ₊₁) − Λ(tₖ))` over the uniform partitions converge to `∫₀ᵗ c(s)(λ s) ds`. -/
theorem tendsto_riemannSum_clm {c : ℝ → E →L[ℝ] ℝ} {Λ lam : ℝ → E} {t : ℝ} (ht : 0 ≤ t)
    (hc : ContinuousOn c (Icc 0 t)) (hlam : IntervalIntegrable lam volume 0 t)
    (hΛ : ∀ s ∈ Icc 0 t, Λ s = Λ 0 + ∫ r in (0 : ℝ)..s, lam r) :
    Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n,
        c (t * k / n) (Λ (t * (k + 1) / n) - Λ (t * k / n))) atTop
      (𝓝 (∫ s in (0 : ℝ)..t, c s (lam s))) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set I := ∫ s in (0 : ℝ)..t, ‖lam s‖ with hI
  have hI0 : 0 ≤ I := intervalIntegral.integral_nonneg ht fun _ _ => norm_nonneg _
  set η := ε / (I + 1) with hη
  have hη0 : 0 < η := div_pos hε (by linarith)
  obtain ⟨δ, hδ0, hδ⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hc) η hη0
  obtain ⟨N, hN⟩ := exists_nat_gt (t / δ)
  refine ⟨N + 1, fun n hn => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (Nat.succ_pos N).trans_le hn
  set a : ℕ → ℝ := fun k => t * k / n with ha
  have ha_mem : ∀ k ≤ n, a k ∈ Icc 0 t := fun k hk => by
    refine ⟨by positivity, ?_⟩
    rw [ha, div_le_iff₀ hn0]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hk) ht
  have ha_succ : ∀ k, a (k + 1) = t * (k + 1) / n := fun k => by simp [ha]
  have hstep : ∀ k, a (k + 1) - a k = t / n := fun k => by rw [ha_succ]; simp only [ha]; ring
  have hmesh : t / n < δ := by
    rw [div_lt_iff₀ hn0]
    rw [div_lt_iff₀ hδ0] at hN
    have : (N : ℝ) < n := by exact_mod_cast Nat.lt_of_succ_le hn
    nlinarith
  have hsub : ∀ k < n, uIcc (a k) (a (k + 1)) ⊆ uIcc 0 t := fun k hk => by
    rw [uIcc_of_le ht]
    exact uIcc_subset_Icc (ha_mem k hk.le) (ha_mem (k + 1) hk)
  have hint_k : ∀ k < n, IntervalIntegrable lam volume (a k) (a (k + 1)) := fun k hk =>
    hlam.mono_set (by rw [uIcc_of_le ht] at *; exact hsub k hk)
  have hcI : ContinuousOn c (uIcc 0 t) := by rwa [uIcc_of_le ht]
  have hg := intervalIntegrable_clm_apply hcI hlam
  have hg_k : ∀ k < n, IntervalIntegrable (fun s => c s (lam s)) volume (a k) (a (k + 1)) :=
    fun k hk => hg.mono_set (hsub k hk)
  -- the increments of `Λ`
  have hΔ : ∀ k < n, Λ (a (k + 1)) - Λ (a k) = ∫ r in a k..a (k + 1), lam r := fun k hk => by
    rw [hΛ _ (ha_mem (k + 1) hk), hΛ _ (ha_mem k hk.le), add_sub_add_left_eq_sub,
      intervalIntegral.integral_interval_sub_left (hlam.mono_set (by
        rw [uIcc_of_le ht]; exact uIcc_subset_Icc (left_mem_Icc.2 ht) (ha_mem (k + 1) hk)))
        (hlam.mono_set (by
        rw [uIcc_of_le ht]; exact uIcc_subset_Icc (left_mem_Icc.2 ht) (ha_mem k hk.le)))]
  have hsum_eq : ∑ k ∈ Finset.range n, c (t * k / n) (Λ (t * (k + 1) / n) - Λ (t * k / n)) =
      ∑ k ∈ Finset.range n, ∫ r in a k..a (k + 1), c (a k) (lam r) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.1 hk
    rw [← ha_succ, show t * k / n = a k from rfl, hΔ k hk',
      (c (a k)).intervalIntegral_comp_comm (hint_k k hk')]
  have hI_eq : ∫ s in (0 : ℝ)..t, c s (lam s) =
      ∑ k ∈ Finset.range n, ∫ r in a k..a (k + 1), c r (lam r) := by
    rw [intervalIntegral.sum_integral_adjacent_intervals hg_k]
    simp only [ha, Nat.cast_zero, mul_zero, zero_div]
    rw [mul_div_assoc, div_self hn0.ne', mul_one]
  have hnorm_eq : I = ∑ k ∈ Finset.range n, ∫ r in a k..a (k + 1), ‖lam r‖ := by
    rw [intervalIntegral.sum_integral_adjacent_intervals fun k hk => (hint_k k hk).norm]
    simp only [ha, Nat.cast_zero, mul_zero, zero_div]
    rw [mul_div_assoc, div_self hn0.ne', mul_one]
  rw [dist_eq_norm, hsum_eq, hI_eq, ← Finset.sum_sub_distrib]
  have hterm : ∀ k ∈ Finset.range n,
      ‖(∫ r in a k..a (k + 1), c (a k) (lam r)) - ∫ r in a k..a (k + 1), c r (lam r)‖ ≤
        η * ∫ r in a k..a (k + 1), ‖lam r‖ := by
    intro k hk
    have hk' := Finset.mem_range.1 hk
    have hle : a k ≤ a (k + 1) := by linarith [hstep k, div_nonneg ht hn0.le]
    rw [← intervalIntegral.integral_sub (intervalIntegrable_clm_apply (c := fun _ => c (a k))
      continuousOn_const (hint_k k hk')) (hg_k k hk'), ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.norm_integral_le_of_norm_le hle ?_ ((hint_k k hk').norm.const_mul η)
    refine Eventually.of_forall fun r hr => ?_
    have hr1 : r ∈ Icc 0 t := hsub k hk' (by rw [uIcc_of_le hle]; exact Ioc_subset_Icc_self hr) |>
      fun h => by rwa [uIcc_of_le ht] at h
    have hdist : dist (a k) r < δ := by
      rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith [hr.1])]
      linarith [hr.2, hstep k]
    have hc' := (hδ (a k) (ha_mem k hk'.le) r hr1 hdist).le
    rw [dist_eq_norm] at hc'
    rw [← sub_apply]
    exact ((c (a k) - c r).le_opNorm (lam r)).trans
      (mul_le_mul_of_nonneg_right hc' (norm_nonneg _))
  calc ‖∑ k ∈ Finset.range n, ((∫ r in a k..a (k + 1), c (a k) (lam r)) -
          ∫ r in a k..a (k + 1), c r (lam r))‖
      ≤ ∑ k ∈ Finset.range n, η * ∫ r in a k..a (k + 1), ‖lam r‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum hterm)
    _ = η * I := by rw [← Finset.mul_sum, hnorm_eq]
    _ < ε := by
        rw [hη, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
        nlinarith

end Riemann


/-! ### Partial derivatives of `F : E × ℝ → ℝ` and the pathwise step -/

section Step

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- `∂_Λ F(p) = DF(p)(·, 0)`. -/
def partialFst (F : E × ℝ → ℝ) (p : E × ℝ) : E →L[ℝ] ℝ :=
  (fderiv ℝ F p).comp (ContinuousLinearMap.inl ℝ E ℝ)

/-- `∂_x F(p) = DF(p)(0, 1)`. -/
def partialSnd (F : E × ℝ → ℝ) (p : E × ℝ) : ℝ := fderiv ℝ F p (0, 1)

/-- `∂²_x F(p) = D²F(p)((0, 1), (0, 1))`. -/
def partialSndSnd (F : E × ℝ → ℝ) (p : E × ℝ) : ℝ := fderiv ℝ (fderiv ℝ F) p (0, 1) (0, 1)

/-- The Itô generator integrand `∂_Λ F(p) v + ½ ∂²_x F(p)`. -/
def itoGen (F : E × ℝ → ℝ) (p : E × ℝ) (v : E) : ℝ := partialFst F p v + 1 / 2 * partialSndSnd F p

omit [CompleteSpace E] in
theorem partialFst_apply (F : E × ℝ → ℝ) (p : E × ℝ) (v : E) :
    partialFst F p v = fderiv ℝ F p (v, 0) := rfl

omit [NormedSpace ℝ E] [CompleteSpace E] in
theorem norm_zero_one : ‖((0 : E), (1 : ℝ))‖ = 1 := by simp [Prod.norm_def]

omit [CompleteSpace E] in
theorem norm_partialFst_le {F : E × ℝ → ℝ} (p : E × ℝ) : ‖partialFst F p‖ ≤ ‖fderiv ℝ F p‖ :=
  (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_of_le_one_right (norm_nonneg _) (ContinuousLinearMap.norm_inl_le_one ℝ E ℝ))

omit [CompleteSpace E] in
theorem norm_partialFst_sub_le {F : E × ℝ → ℝ} (p q : E × ℝ) :
    ‖partialFst F p - partialFst F q‖ ≤ ‖fderiv ℝ F p - fderiv ℝ F q‖ := by
  rw [partialFst, partialFst, ← ContinuousLinearMap.sub_comp]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_of_le_one_right (norm_nonneg _) (ContinuousLinearMap.norm_inl_le_one ℝ E ℝ))

omit [CompleteSpace E] in
theorem abs_partialSndSnd_sub_le {F : E × ℝ → ℝ} (p q : E × ℝ) :
    |partialSndSnd F p - partialSndSnd F q| ≤
      ‖fderiv ℝ (fderiv ℝ F) p - fderiv ℝ (fderiv ℝ F) q‖ := by
  have h := ((fderiv ℝ (fderiv ℝ F) p - fderiv ℝ (fderiv ℝ F) q).le_opNorm ((0 : E), (1 : ℝ)))
  have h2 := ((fderiv ℝ (fderiv ℝ F) p - fderiv ℝ (fderiv ℝ F) q) ((0 : E), (1 : ℝ))).le_opNorm
    ((0 : E), (1 : ℝ))
  rw [norm_zero_one, mul_one] at h h2
  have e : partialSndSnd F p - partialSndSnd F q =
      ((fderiv ℝ (fderiv ℝ F) p - fderiv ℝ (fderiv ℝ F) q) ((0 : E), (1 : ℝ))) ((0 : E), (1 : ℝ)) := by
    simp only [partialSndSnd, sub_apply]
  rw [← Real.norm_eq_abs, e]
  exact h2.trans h

omit [CompleteSpace E] in
theorem abs_partialSndSnd_le {F : E × ℝ → ℝ} (p : E × ℝ) :
    |partialSndSnd F p| ≤ ‖fderiv ℝ (fderiv ℝ F) p‖ := by
  have h := (fderiv ℝ (fderiv ℝ F) p).le_opNorm ((0 : E), (1 : ℝ))
  have h2 := ((fderiv ℝ (fderiv ℝ F) p) ((0 : E), (1 : ℝ))).le_opNorm ((0 : E), (1 : ℝ))
  rw [norm_zero_one, mul_one] at h h2
  rw [← Real.norm_eq_abs]
  exact h2.trans h

/-- The pathwise remainder of one time step `[a, b]`. -/
def stepRemainder (F : E × ℝ → ℝ) (Λp lamp : ℝ → E) (Bp : ℝ → ℝ) (a b : ℝ) : ℝ :=
  (∫ r in a..b, ‖partialFst F (Λp r, Bp b) - partialFst F (Λp r, Bp r)‖ * ‖lamp r‖) +
    1 / 2 * ∫ r in a..b, |partialSndSnd F (Λp a, Bp a) - partialSndSnd F (Λp r, Bp r)|

variable {F : E × ℝ → ℝ} {C : ℝ}

/-- **The pathwise step.** Along an absolutely continuous `Λ` (density `λ`) and a continuous `x`,
`F(Λ_b, x_b) − F(Λ_a, x_a) − ∫_a^b itoGen F (Λ_r, x_r) λ_r dr` equals the first two Taylor terms in the
increment of `x`, `∂_xF Δx + ½ ∂²_xF (Δx² − (b − a))`, up to `C |Δx|³ + stepRemainder`. -/
theorem pathwise_step (hF : ContDiff ℝ 3 F) (hC0 : 0 ≤ C) (hD1 : ∀ p, ‖fderiv ℝ F p‖ ≤ C)
    (hLip2 : ∀ p q, ‖iteratedFDeriv ℝ 2 F p - iteratedFDeriv ℝ 2 F q‖ ≤ C * ‖p - q‖)
    {Λp lamp : ℝ → E} {Bp : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hlamp : IntervalIntegrable lamp volume a b)
    (hΛp : ∀ r ∈ uIcc a b, Λp r = Λp a + ∫ s in a..r, lamp s)
    (hΛc : ContinuousOn Λp (uIcc a b)) (hBc : ContinuousOn Bp (uIcc a b)) :
    |F (Λp b, Bp b) - F (Λp a, Bp a) - (∫ r in a..b, itoGen F (Λp r, Bp r) (lamp r))
        - partialSnd F (Λp a, Bp a) * (Bp b - Bp a)
        - 1 / 2 * partialSndSnd F (Λp a, Bp a) * ((Bp b - Bp a) ^ 2 - (b - a))|
      ≤ C * |Bp b - Bp a| ^ 3 + stepRemainder F Λp lamp Bp a b := by
  have hF1 : ContDiff ℝ 2 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
  have hDF : ∀ p, HasFDerivAt F (fderiv ℝ F p) p := fun p =>
    ((hF.differentiable (by norm_num)) p).hasFDerivAt
  have hDFc : Continuous (fderiv ℝ F) := hF.continuous_fderiv (by norm_num)
  have hD2c : Continuous (fderiv ℝ (fderiv ℝ F)) := hF1.continuous_fderiv (by norm_num)
  have hPFc : Continuous (partialFst F) :=
    hDFc.clm_comp continuous_const
  have hPSSc : Continuous (partialSndSnd F) :=
    (hD2c.clm_apply continuous_const).clm_apply continuous_const
  set xa := Bp a
  set xb := Bp b
  set Δ := xb - xa with hΔ
  -- (i) the absolutely continuous part at frozen `x = x_b`
  have hΦL : LipschitzWith ⟨C, hC0⟩ fun e : E => F (e, xb) := by
    refine LipschitzWith.of_dist_le_mul fun e e' => ?_
    have h := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (s := Set.univ) (f := F)
      (fun p _ => (hDF p).differentiableAt) (fun p _ => hD1 p) convex_univ
      (Set.mem_univ (e', xb)) (Set.mem_univ (e, xb))
    have hn : ‖((e, xb) : E × ℝ) - (e', xb)‖ = ‖e - e'‖ := by
      rw [Prod.mk_sub_mk, sub_self, Prod.norm_def]; simp
    rw [hn] at h
    rw [Real.dist_eq, dist_eq_norm, ← Real.norm_eq_abs]
    exact h
  have hΦd : ∀ e : E, HasFDerivAt (fun e : E => F (e, xb)) (partialFst F (e, xb)) e := fun e =>
    (hDF (e, xb)).comp e (hasFDerivAt_prodMk_left e xb)
  have hΦ'c : Continuous fun e : E => partialFst F (e, xb) :=
    hPFc.comp (continuous_id.prodMk continuous_const)
  have hAC := comp_eq_add_integral_of_lipschitz hΦd hΦL hΦ'c hlamp hΛp
  -- (ii) the second-order Taylor expansion in `x` at `Λ_a`
  have hLip2' := hLip2
  have hTay := QuantumZipper.Dynkin.taylor2_bound hF hC0 hLip2' (Λp a, xa) ((0 : E), Δ)
  have hw : ((Λp a, xa) + ((0 : E), Δ) : E × ℝ) = (Λp a, xb) := by
    simp only [Prod.mk_add_mk, add_zero, hΔ, add_sub_cancel]
  have hwn : ‖((0 : E), Δ)‖ = |Δ| := by simp [Prod.norm_def]
  have hlin : fderiv ℝ F (Λp a, xa) ((0 : E), Δ) = partialSnd F (Λp a, xa) * Δ := by
    have : ((0 : E), Δ) = Δ • ((0 : E), (1 : ℝ)) := by simp
    rw [this, map_smul, smul_eq_mul, partialSnd, mul_comm]
  have hquad : iteratedFDeriv ℝ 2 F (Λp a, xa) ![((0 : E), Δ), ((0 : E), Δ)] =
      partialSndSnd F (Λp a, xa) * Δ ^ 2 := by
    rw [QuantumZipper.Dynkin.iteratedFDeriv_two_vec]
    have : ((0 : E), Δ) = Δ • ((0 : E), (1 : ℝ)) := by simp
    rw [this, map_smul, map_smul, smul_apply, smul_eq_mul, smul_eq_mul,
      partialSndSnd]
    ring
  rw [hw, hlin, hquad, hwn] at hTay
  -- (iii) the drift integral splits
  have hlamI : IntervalIntegrable (fun r => partialFst F (Λp r, Bp r) (lamp r)) volume a b :=
    intervalIntegrable_clm_apply (hPFc.comp_continuousOn (hΛc.prodMk hBc)) hlamp
  have hSSI : IntervalIntegrable (fun r => partialSndSnd F (Λp r, Bp r)) volume a b :=
    (hPSSc.comp_continuousOn (hΛc.prodMk hBc)).intervalIntegrable
  have hsplit : ∫ r in a..b, itoGen F (Λp r, Bp r) (lamp r) =
      (∫ r in a..b, partialFst F (Λp r, Bp r) (lamp r)) +
        1 / 2 * ∫ r in a..b, partialSndSnd F (Λp r, Bp r) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add hlamI
      (hSSI.const_mul _)]
    rfl
  have hxbI : IntervalIntegrable (fun r => partialFst F (Λp r, xb) (lamp r)) volume a b :=
    intervalIntegrable_clm_apply ((hΦ'c.comp_continuousOn hΛc)) hlamp
  -- the remainder terms
  have hc12 : ContinuousOn (fun r => partialFst F (Λp r, xb) - partialFst F (Λp r, Bp r))
      (uIcc a b) :=
    (hΦ'c.comp_continuousOn hΛc).sub (hPFc.comp_continuousOn (hΛc.prodMk hBc))
  have hR1 : |(∫ r in a..b, partialFst F (Λp r, xb) (lamp r)) -
      ∫ r in a..b, partialFst F (Λp r, Bp r) (lamp r)| ≤
      ∫ r in a..b, ‖partialFst F (Λp r, xb) - partialFst F (Λp r, Bp r)‖ * ‖lamp r‖ := by
    rw [← intervalIntegral.integral_sub hxbI hlamI, ← Real.norm_eq_abs]
    refine (intervalIntegral.norm_integral_le_integral_norm hab).trans ?_
    refine intervalIntegral.integral_mono_on hab (hxbI.sub hlamI).norm
      (hlamp.norm.continuousOn_mul hc12.norm) fun r _ => ?_
    rw [← sub_apply]
    exact ContinuousLinearMap.le_opNorm _ _
  have hR2 : |(b - a) * partialSndSnd F (Λp a, xa) - ∫ r in a..b, partialSndSnd F (Λp r, Bp r)| ≤
      ∫ r in a..b, |partialSndSnd F (Λp a, xa) - partialSndSnd F (Λp r, Bp r)| := by
    have heq : (b - a) * partialSndSnd F (Λp a, xa) - ∫ r in a..b, partialSndSnd F (Λp r, Bp r) =
        ∫ r in a..b, (partialSndSnd F (Λp a, xa) - partialSndSnd F (Λp r, Bp r)) := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const hSSI,
        intervalIntegral.integral_const, smul_eq_mul]
    rw [heq]
    exact intervalIntegral.abs_integral_le_integral_abs hab
  have hkey : F (Λp b, xb) - F (Λp a, xa) - (∫ r in a..b, itoGen F (Λp r, Bp r) (lamp r))
        - partialSnd F (Λp a, xa) * Δ - 1 / 2 * partialSndSnd F (Λp a, xa) * (Δ ^ 2 - (b - a)) =
      (F (Λp a, xb) - F (Λp a, xa) - partialSnd F (Λp a, xa) * Δ
          - 1 / 2 * (partialSndSnd F (Λp a, xa) * Δ ^ 2)) +
        ((∫ r in a..b, partialFst F (Λp r, xb) (lamp r)) -
          ∫ r in a..b, partialFst F (Λp r, Bp r) (lamp r)) +
        1 / 2 * ((b - a) * partialSndSnd F (Λp a, xa) -
          ∫ r in a..b, partialSndSnd F (Λp r, Bp r)) := by
    rw [hAC, hsplit]; ring
  rw [hkey, stepRemainder]
  calc _ ≤ |F (Λp a, xb) - F (Λp a, xa) - partialSnd F (Λp a, xa) * Δ
          - 1 / 2 * (partialSndSnd F (Λp a, xa) * Δ ^ 2)| +
        |(∫ r in a..b, partialFst F (Λp r, xb) (lamp r)) -
          ∫ r in a..b, partialFst F (Λp r, Bp r) (lamp r)| +
        1 / 2 * |(b - a) * partialSndSnd F (Λp a, xa) -
          ∫ r in a..b, partialSndSnd F (Λp r, Bp r)| := by
        refine (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) ?_)
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    _ ≤ _ := by linarith [hTay, hR1, hR2]

omit [CompleteSpace E] in
theorem stepRemainder_nonneg {Λp lamp : ℝ → E} {Bp : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) :
    0 ≤ stepRemainder F Λp lamp Bp a b :=
  add_nonneg (intervalIntegral.integral_nonneg hab fun _ _ => mul_nonneg (norm_nonneg _)
    (norm_nonneg _)) (mul_nonneg (by norm_num)
      (intervalIntegral.integral_nonneg hab fun _ _ => abs_nonneg _))

omit [CompleteSpace E] in
/-- A bound for `stepRemainder` from pointwise bounds on the two integrands. -/
theorem stepRemainder_le (hF : ContDiff ℝ 3 F) {Λp lamp : ℝ → E} {Bp : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hlamp : IntervalIntegrable lamp volume a b)
    (hΛc : ContinuousOn Λp (uIcc a b)) (hBc : ContinuousOn Bp (uIcc a b)) {α β : ℝ}
    (hα : ∀ r ∈ Icc a b, ‖partialFst F (Λp r, Bp b) - partialFst F (Λp r, Bp r)‖ ≤ α)
    (hβ : ∀ r ∈ Icc a b, |partialSndSnd F (Λp a, Bp a) - partialSndSnd F (Λp r, Bp r)| ≤ β) :
    stepRemainder F Λp lamp Bp a b ≤ α * (∫ r in a..b, ‖lamp r‖) + 1 / 2 * (β * (b - a)) := by
  have hF1 : ContDiff ℝ 2 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
  have hPFc : Continuous (partialFst F) :=
    (hF.continuous_fderiv (by norm_num)).clm_comp continuous_const
  have hPSSc : Continuous (partialSndSnd F) :=
    ((hF1.continuous_fderiv (by norm_num)).clm_apply continuous_const).clm_apply continuous_const
  have hc12 : ContinuousOn (fun r => partialFst F (Λp r, Bp b) - partialFst F (Λp r, Bp r))
      (uIcc a b) :=
    (hPFc.comp_continuousOn (hΛc.prodMk continuousOn_const)).sub
      (hPFc.comp_continuousOn (hΛc.prodMk hBc))
  have hd : ContinuousOn (fun r => |partialSndSnd F (Λp a, Bp a) - partialSndSnd F (Λp r, Bp r)|)
      (uIcc a b) :=
    (continuousOn_const.sub (hPSSc.comp_continuousOn (hΛc.prodMk hBc))).abs
  unfold stepRemainder
  refine add_le_add ?_ (mul_le_mul_of_nonneg_left ?_ (by norm_num))
  · rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_mono_on hab (hlamp.norm.continuousOn_mul hc12.norm)
      (hlamp.norm.const_mul α) fun r hr => mul_le_mul_of_nonneg_right (hα r hr) (norm_nonneg _)
  · have := intervalIntegral.integral_mono_on hab hd.intervalIntegrable
      (intervalIntegrable_const : IntervalIntegrable (fun _ => β) volume a b) hβ
    rwa [intervalIntegral.integral_const, smul_eq_mul, mul_comm] at this

omit [CompleteSpace E] in
/-- **The summed remainders vanish.** Along the uniform partitions `aₖ = s + (t − s) k / n` of
`[s, t]`, `∑ₖ stepRemainder(aₖ, aₖ₊₁) → 0`, for `Λ` absolutely continuous and `x` continuous, when
`DF` and `D²F` are `C`-Lipschitz. -/
theorem tendsto_sum_stepRemainder (hF : ContDiff ℝ 3 F) (hC0 : 0 ≤ C)
    (hLip1 : ∀ p q, ‖fderiv ℝ F p - fderiv ℝ F q‖ ≤ C * ‖p - q‖)
    (hLipD2 : ∀ p q, ‖fderiv ℝ (fderiv ℝ F) p - fderiv ℝ (fderiv ℝ F) q‖ ≤ C * ‖p - q‖)
    {Λp lamp : ℝ → E} {Bp : ℝ → ℝ} {s t : ℝ} (hst : s ≤ t)
    (hlamp : IntervalIntegrable lamp volume s t)
    (hΛc : ContinuousOn Λp (Icc s t)) (hBc : ContinuousOn Bp (Icc s t)) :
    Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, stepRemainder F Λp lamp Bp
        (s + (t - s) * k / n) (s + (t - s) * (k + 1) / n)) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set I := ∫ r in s..t, ‖lamp r‖ with hI
  have hI0 : 0 ≤ I := intervalIntegral.integral_nonneg hst fun _ _ => norm_nonneg _
  set η := ε / (2 * (C + 1) * (I + (t - s) + 1)) with hη
  have hη0 : 0 < η := div_pos hε (by positivity)
  have hXc : ContinuousOn (fun r => (Λp r, Bp r)) (Icc s t) := hΛc.prodMk hBc
  obtain ⟨δ, hδ0, hδ⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hXc) η hη0
  obtain ⟨N, hN⟩ := exists_nat_gt ((t - s) / δ)
  refine ⟨N + 1, fun n hn => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (Nat.succ_pos N).trans_le hn
  set a : ℕ → ℝ := fun k => s + (t - s) * k / n with ha
  have hts : 0 ≤ t - s := sub_nonneg.2 hst
  have ha_mem : ∀ k ≤ n, a k ∈ Icc s t := fun k hk => by
    refine ⟨le_add_of_nonneg_right (by positivity), ?_⟩
    have : (t - s) * k / n ≤ t - s := by
      rw [div_le_iff₀ hn0]; exact mul_le_mul_of_nonneg_left (by exact_mod_cast hk) hts
    simp only [ha]; linarith
  have ha_succ : ∀ k, a (k + 1) = s + (t - s) * (k + 1) / n := fun k => by simp [ha]
  have hstep : ∀ k, a (k + 1) - a k = (t - s) / n := fun k => by
    rw [ha_succ]; simp only [ha]; ring
  have hmesh : (t - s) / n < δ := by
    rw [div_lt_iff₀ hn0]
    rw [div_lt_iff₀ hδ0] at hN
    have : (N : ℝ) < n := by exact_mod_cast Nat.lt_of_succ_le hn
    nlinarith
  have hle : ∀ k, a k ≤ a (k + 1) := fun k => by
    linarith [hstep k, div_nonneg hts hn0.le]
  have hsub : ∀ k < n, Icc (a k) (a (k + 1)) ⊆ Icc s t := fun k hk =>
    Icc_subset_Icc (ha_mem k hk.le).1 (ha_mem (k + 1) hk).2
  have huIcc : ∀ k < n, uIcc (a k) (a (k + 1)) ⊆ Icc s t := fun k hk => by
    rw [uIcc_of_le (hle k)]; exact hsub k hk
  have hint_k : ∀ k < n, IntervalIntegrable lamp volume (a k) (a (k + 1)) := fun k hk =>
    hlamp.mono_set (by rw [uIcc_of_le hst]; exact huIcc k hk)
  -- each step is small
  have hterm : ∀ k ∈ Finset.range n, stepRemainder F Λp lamp Bp (a k) (a (k + 1)) ≤
      C * η * (∫ r in a k..a (k + 1), ‖lamp r‖) + 1 / 2 * (C * η * (a (k + 1) - a k)) := by
    intro k hk
    have hk' := Finset.mem_range.1 hk
    have hclose : ∀ r ∈ Icc (a k) (a (k + 1)), ∀ r' ∈ Icc (a k) (a (k + 1)),
        ‖(Λp r, Bp r) - (Λp r', Bp r')‖ ≤ η := by
      intro r hr r' hr'
      have hd : dist r r' < δ := by
        rw [Real.dist_eq]
        have := hstep k
        rw [abs_lt]; constructor <;> linarith [hr.1, hr.2, hr'.1, hr'.2]
      have := hδ r (hsub k hk' hr) r' (hsub k hk' hr') hd
      rw [dist_eq_norm] at this
      exact this.le
    refine stepRemainder_le (α := C * η) (β := C * η) hF (hle k) (hint_k k hk')
      (hΛc.mono (huIcc k hk')) (hBc.mono (huIcc k hk')) (fun r hr => ?_) (fun r hr => ?_)
    · refine (norm_partialFst_sub_le _ _).trans ((hLip1 _ _).trans ?_)
      have h1 := hclose (a (k + 1)) (right_mem_Icc.2 (hle k)) r hr
      have h2 : ‖((Λp r, Bp (a (k + 1))) : E × ℝ) - (Λp r, Bp r)‖ ≤
          ‖((Λp (a (k + 1)), Bp (a (k + 1))) : E × ℝ) - (Λp r, Bp r)‖ := by
        simp only [Prod.mk_sub_mk, sub_self, Prod.norm_def, norm_zero]
        exact max_le ((norm_nonneg _).trans (le_max_left _ _)) (le_max_right _ _)
      exact mul_le_mul_of_nonneg_left (h2.trans h1) hC0
    · refine (abs_partialSndSnd_sub_le _ _).trans ((hLipD2 _ _).trans ?_)
      exact mul_le_mul_of_nonneg_left (hclose _ (left_mem_Icc.2 (hle k)) r hr) hC0
  have hsumI : ∑ k ∈ Finset.range n, ∫ r in a k..a (k + 1), ‖lamp r‖ = I := by
    rw [intervalIntegral.sum_integral_adjacent_intervals fun k hk => (hint_k k hk).norm]
    simp only [ha, Nat.cast_zero, mul_zero, zero_div, add_zero]
    rw [mul_div_assoc, div_self hn0.ne', mul_one, add_sub_cancel]
  have hsumL : ∑ k ∈ Finset.range n, (a (k + 1) - a k) = t - s := by
    rw [Finset.sum_range_sub (f := a)]
    simp only [ha, Nat.cast_zero, mul_zero, zero_div, add_zero]
    rw [mul_div_assoc, div_self hn0.ne', mul_one]
    ring
  have hnn : 0 ≤ ∑ k ∈ Finset.range n, stepRemainder F Λp lamp Bp (a k) (a (k + 1)) :=
    Finset.sum_nonneg fun k _ => stepRemainder_nonneg (hle k)
  have hbound : ∑ k ∈ Finset.range n, stepRemainder F Λp lamp Bp (a k) (a (k + 1)) ≤
      C * η * I + 1 / 2 * (C * η * (t - s)) := by
    refine (Finset.sum_le_sum hterm).trans_eq ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hsumI,
      hsumL]
  have hfold : (∑ k ∈ Finset.range n, stepRemainder F Λp lamp Bp
      (s + (t - s) * k / n) (s + (t - s) * (k + 1) / n)) =
      ∑ k ∈ Finset.range n, stepRemainder F Λp lamp Bp (a k) (a (k + 1)) :=
    Finset.sum_congr rfl fun k _ => by rw [ha_succ]
  rw [Real.dist_eq, sub_zero, hfold, abs_of_nonneg hnn]
  refine hbound.trans_lt ?_
  have hCη : C * η * (I + (t - s)) < ε := by
    have h1 : C * η * (I + (t - s)) ≤ (C + 1) * η * (I + (t - s) + 1) := by
      apply mul_le_mul (mul_le_mul_of_nonneg_right (by linarith) hη0.le) (by linarith)
        (by positivity) (by positivity)
    have h2 : (C + 1) * η * (I + (t - s) + 1) = ε / 2 := by
      rw [hη]; field_simp
    linarith
  nlinarith [mul_nonneg (mul_nonneg hC0 hη0.le) hts]

end Step

/-! ### The martingale -/

section Engine

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {B : ℝ≥0 → Ω → ℝ}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The process `F(Λ_t, B_t) − ∫₀ᵗ itoGen F (Λ_s, B_s) λ_s ds` of `martingale_itoDynkin`. -/
def itoDynkinProcess (F : E × ℝ → ℝ) (Λ : ℝ≥0 → Ω → E) (lam : ℝ → Ω → E) (B : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  F (Λ t ω, B t ω) - ∫ s in (0 : ℝ)..t, itoGen F (Λ s.toNNReal ω, B s.toNNReal ω) (lam s ω)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem abs_itoGen_le {F : E × ℝ → ℝ} {C : ℝ} (hD1 : ∀ p, ‖fderiv ℝ F p‖ ≤ C)
    (hD2 : ∀ p, ‖fderiv ℝ (fderiv ℝ F) p‖ ≤ C) (p : E × ℝ) (v : E) :
    |itoGen F p v| ≤ C * ‖v‖ + C / 2 := by
  unfold itoGen
  have h1 : |partialFst F p v| ≤ C * ‖v‖ := by
    rw [← Real.norm_eq_abs]
    exact ((partialFst F p).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right ((norm_partialFst_le p).trans (hD1 p)) (norm_nonneg _))
  have h2 : |partialSndSnd F p| ≤ C := (abs_partialSndSnd_le p).trans (hD2 p)
  calc |partialFst F p v + 1 / 2 * partialSndSnd F p|
      ≤ |partialFst F p v| + 1 / 2 * |partialSndSnd F p| := by
        refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    _ ≤ C * ‖v‖ + C / 2 := by linarith

variable {Λ : ℝ≥0 → Ω → E} {lam : ℝ → Ω → E}

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem continuous_of_eq_add_integral (hlam : ∀ ω, Integrable (fun s => lam s ω))
    (hΛ : ∀ ω (t : ℝ≥0), Λ t ω = Λ 0 ω + ∫ s in (0 : ℝ)..t, lam s ω) (ω : Ω) :
    Continuous fun t : ℝ≥0 => Λ t ω := by
  have h := (intervalIntegral.continuous_primitive (fun a b => (hlam ω).intervalIntegrable)
    0).comp NNReal.continuous_coe
  exact (continuous_const.add h).congr fun t => (hΛ ω t).symm

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem path_eq_add_integral (hlam : ∀ ω, Integrable (fun s => lam s ω))
    (hΛ : ∀ ω (t : ℝ≥0), Λ t ω = Λ 0 ω + ∫ s in (0 : ℝ)..t, lam s ω) (ω : Ω) {a r : ℝ}
    (ha : 0 ≤ a) (hr : 0 ≤ r) :
    Λ r.toNNReal ω = Λ a.toNNReal ω + ∫ s in a..r, lam s ω := by
  rw [hΛ ω r.toNNReal, hΛ ω a.toNNReal, Real.coe_toNNReal _ hr, Real.coe_toNNReal _ ha, add_assoc,
    intervalIntegral.integral_add_adjacent_intervals (hlam ω).intervalIntegrable
      (hlam ω).intervalIntegrable]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem continuous_itoGen {F : E × ℝ → ℝ} (hF : ContDiff ℝ 3 F) :
    Continuous fun q : (E × ℝ) × E => itoGen F q.1 q.2 := by
  have hF1 : ContDiff ℝ 2 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
  have hPFc : Continuous (partialFst F) :=
    (hF.continuous_fderiv (by norm_num)).clm_comp continuous_const
  have hPSSc : Continuous (partialSndSnd F) :=
    ((hF1.continuous_fderiv (by norm_num)).clm_apply continuous_const).clm_apply continuous_const
  exact ((hPFc.comp continuous_fst).clm_apply continuous_snd).add
    (continuous_const.mul (hPSSc.comp continuous_fst))

omit [MeasurableSpace E] [BorelSpace E] in
theorem intervalIntegrable_itoGen {F : E × ℝ → ℝ} (hF : ContDiff ℝ 3 F) {C : ℝ}
    (hD1 : ∀ p, ‖fderiv ℝ F p‖ ≤ C) (hD2 : ∀ p, ‖fderiv ℝ (fderiv ℝ F) p‖ ≤ C)
    {X : ℝ → E × ℝ} (hX : Continuous X) {l : ℝ → E} (hl : Integrable l) (a b : ℝ) :
    IntervalIntegrable (fun s => itoGen F (X s) (l s)) volume a b := by
  refine ((hl.intervalIntegrable (a := a) (b := b)).norm.const_mul C |>.add
    (intervalIntegrable_const (c := C / 2))).mono_fun' ?_ ?_
  · exact (continuous_itoGen hF).comp_aestronglyMeasurable
      (hX.aestronglyMeasurable.prodMk (hl.aestronglyMeasurable.restrict))
  · exact Eventually.of_forall fun s => by
      simp only [Real.norm_eq_abs]; exact abs_itoGen_le hD1 hD2 _ _

/-- Adaptedness of the first-order drift integral, from its Riemann–Stieltjes sums. -/
theorem measurable_integral_partialFst {F : E × ℝ → ℝ} (hF : ContDiff ℝ 3 F)
    (hBm : ∀ t, Measurable[𝓕 t] (B t)) (hBc : ∀ ω, Continuous (B · ω))
    (hΛm : ∀ t, Measurable[𝓕 t] (Λ t)) (hlam : ∀ ω, Integrable (fun s => lam s ω))
    (hΛ : ∀ ω (t : ℝ≥0), Λ t ω = Λ 0 ω + ∫ s in (0 : ℝ)..t, lam s ω) (t : ℝ≥0) :
    Measurable[𝓕 t] fun ω =>
      ∫ s in (0 : ℝ)..t, partialFst F (Λ s.toNNReal ω, B s.toNNReal ω) (lam s ω) := by
  have hPFc : Continuous (partialFst F) :=
    (hF.continuous_fderiv (by norm_num)).clm_comp continuous_const
  have happ : Continuous fun q : (E × ℝ) × E => partialFst F q.1 q.2 :=
    (hPFc.comp continuous_fst).clm_apply continuous_snd
  have hle : ∀ n k : ℕ, k ≤ n → (((t : ℝ) * k / n).toNNReal) ≤ t := by
    intro n k hk
    rw [Real.toNNReal_le_iff_le_coe]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [div_le_iff₀ (by exact_mod_cast hn)]
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hk) t.coe_nonneg
  have hle' : ∀ n k : ℕ, k + 1 ≤ n → (((t : ℝ) * (k + 1) / n).toNNReal) ≤ t := by
    intro n k hk
    have := hle n (k + 1) hk
    simpa only [Nat.cast_add, Nat.cast_one] using this
  set f : ℕ → Ω → ℝ := fun n ω => ∑ k ∈ Finset.range n,
    partialFst F (Λ ((t : ℝ) * k / n).toNNReal ω, B ((t : ℝ) * k / n).toNNReal ω)
      (Λ ((t : ℝ) * (k + 1) / n).toNNReal ω - Λ ((t : ℝ) * k / n).toNNReal ω) with hf
  have hfm : ∀ n, Measurable[𝓕 t] (f n) := by
    intro n
    refine Finset.measurable_sum _ fun k hk => ?_
    have hk := Finset.mem_range.1 hk
    have h1 := 𝓕.mono (hle n k hk.le)
    have h2 := 𝓕.mono (hle' n k hk)
    exact happ.measurable.comp ((((hΛm _).mono h1 le_rfl).prodMk ((hBm _).mono h1 le_rfl)).prodMk
      (((hΛm _).mono h2 le_rfl).sub ((hΛm _).mono h1 le_rfl)))
  refine @measurable_of_tendsto_metrizable Ω ℝ (𝓕 t) _ _ _ _ f _ hfm
    (tendsto_pi_nhds.2 fun ω => ?_)
  have hΛc := continuous_of_eq_add_integral hlam hΛ ω
  refine tendsto_riemannSum_clm (c := fun s => partialFst F (Λ s.toNNReal ω, B s.toNNReal ω))
    (Λ := fun s => Λ s.toNNReal ω) (lam := fun s => lam s ω) t.coe_nonneg
    (hPFc.comp (((hΛc.comp continuous_real_toNNReal).prodMk
      ((hBc ω).comp continuous_real_toNNReal)))).continuousOn
    (hlam ω).intervalIntegrable (fun r hr => ?_)
  have := path_eq_add_integral hlam hΛ ω (le_refl 0) hr.1
  simpa only [Real.toNNReal_zero] using this

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The bound `|∫_a^b itoGen| ≤ C ∫‖λ‖ + C (b − a)/2`. -/
theorem abs_integral_itoGen_le {F : E × ℝ → ℝ} {C : ℝ}
    (hD1 : ∀ p, ‖fderiv ℝ F p‖ ≤ C) (hD2 : ∀ p, ‖fderiv ℝ (fderiv ℝ F) p‖ ≤ C)
    {X : ℝ → E × ℝ} {l : ℝ → E} (hl : Integrable l) {K : ℝ}
    (hK : ∫ s, ‖l s‖ ≤ K) {a b : ℝ} (hab : a ≤ b) :
    |∫ s in a..b, itoGen F (X s) (l s)| ≤ C * K + C / 2 * (b - a) := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hD1 0)
  rw [← Real.norm_eq_abs]
  refine (intervalIntegral.norm_integral_le_of_norm_le hab
    (Eventually.of_forall fun s _ => by
      rw [Real.norm_eq_abs]; exact abs_itoGen_le hD1 hD2 (X s) (l s))
    ((hl.intervalIntegrable.norm.const_mul C).add intervalIntegrable_const)).trans ?_
  rw [intervalIntegral.integral_add (hl.intervalIntegrable.norm.const_mul C)
    intervalIntegrable_const, intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
    smul_eq_mul]
  have h1 : ∫ s in a..b, ‖l s‖ ≤ K := by
    rw [intervalIntegral.integral_of_le hab]
    exact (setIntegral_le_integral hl.norm (Eventually.of_forall fun _ => norm_nonneg _)).trans hK
  nlinarith

/-- **The martingale identity.** Under the hypotheses of `martingale_itoDynkin`,
`E[ξ (M_t − M_s)] = 0` for `𝓕_s`-measurable `|ξ| ≤ 1`. -/
theorem integral_mul_itoDynkinProcess_sub (hB : IsFilteredBrownianReal 𝓕 B P)
    (hBc : ∀ ω, Continuous (B · ω)) {F : E × ℝ → ℝ} (hF : ContDiff ℝ 3 F) {C : ℝ} (hC0 : 0 ≤ C)
    (hF0 : ∀ p, |F p| ≤ C) (hD1 : ∀ p, ‖fderiv ℝ F p‖ ≤ C)
    (hD2 : ∀ p, ‖fderiv ℝ (fderiv ℝ F) p‖ ≤ C)
    (hLip1 : ∀ p q, ‖fderiv ℝ F p - fderiv ℝ F q‖ ≤ C * ‖p - q‖)
    (hLipD2 : ∀ p q, ‖fderiv ℝ (fderiv ℝ F) p - fderiv ℝ (fderiv ℝ F) q‖ ≤ C * ‖p - q‖)
    (hLip2 : ∀ p q, ‖iteratedFDeriv ℝ 2 F p - iteratedFDeriv ℝ 2 F q‖ ≤ C * ‖p - q‖)
    (hΛm : ∀ t, Measurable[𝓕 t] (Λ t)) (hlam : ∀ ω, Integrable (fun s => lam s ω))
    (hΛ : ∀ ω (t : ℝ≥0), Λ t ω = Λ 0 ω + ∫ s in (0 : ℝ)..t, lam s ω) {K : ℝ}
    (hK : ∀ ω, ∫ s, ‖lam s ω‖ ≤ K)
    (hMm : ∀ t, Measurable[𝓕 t] (itoDynkinProcess F Λ lam B t))
    {s t : ℝ≥0} (hst : s ≤ t) {ξ : Ω → ℝ} (hξ : Measurable[𝓕 s] ξ) (hξb : ∀ ω, |ξ ω| ≤ 1) :
    ∫ ω, ξ ω * (itoDynkinProcess F Λ lam B t ω - itoDynkinProcess F Λ lam B s ω) ∂P = 0 := by
  have hP := hB.isProbabilityMeasure'
  set M := itoDynkinProcess F Λ lam B with hMdef
  have hBm : ∀ r, Measurable (B r) := hB.measurable'
  have hΛc := continuous_of_eq_add_integral hlam hΛ
  have hXc : ∀ ω, Continuous fun r : ℝ => (Λ r.toNNReal ω, B r.toNNReal ω) := fun ω =>
    ((hΛc ω).comp continuous_real_toNNReal).prodMk ((hBc ω).comp continuous_real_toNNReal)
  have hK0 : ∀ ω, 0 ≤ K := fun ω => (integral_nonneg fun _ => norm_nonneg _).trans (hK ω)
  -- `M` is bounded and integrable
  have hMb : ∀ (r : ℝ≥0) ω, |M r ω| ≤ C + (C * K + C / 2 * r) := by
    intro r ω
    have h1 := abs_integral_itoGen_le hD1 hD2 (X := fun x : ℝ => (Λ x.toNNReal ω, B x.toNNReal ω))
      (hlam ω) (hK ω) r.coe_nonneg
    rw [sub_zero] at h1
    calc |M r ω| ≤ |F (Λ r ω, B r ω)| + |∫ x in (0 : ℝ)..r,
          itoGen F (Λ x.toNNReal ω, B x.toNNReal ω) (lam x ω)| := abs_sub _ _
      _ ≤ _ := add_le_add (hF0 _) h1
  have hMi : ∀ r, Integrable (M r) P := fun r =>
    (integrable_const (C + (C * K + C / 2 * r))).mono'
      ((hMm r).mono (𝓕.le r) le_rfl).aestronglyMeasurable
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hMb r ω)
  have hξm : Measurable ξ := hξ.mono (𝓕.le s) le_rfl
  have hst' : (s : ℝ) ≤ t := hst
  have hts : (0 : ℝ) ≤ (t : ℝ) - s := sub_nonneg.2 hst'
  -- the uniform grids
  set gr : ℕ → ℕ → ℝ≥0 := fun n k =>
    ⟨(s : ℝ) + ((t : ℝ) - s) * k / n, add_nonneg s.coe_nonneg (by positivity)⟩ with hgr
  have hgr_coe : ∀ n k, (gr n k : ℝ) = (s : ℝ) + ((t : ℝ) - s) * k / n := fun _ _ => rfl
  have hgr0 : ∀ n, gr n 0 = s := fun n => NNReal.eq (by simp [hgr_coe])
  have hgrn : ∀ n, 0 < n → gr n n = t := fun n hn => NNReal.eq (by
    rw [hgr_coe, mul_div_assoc, div_self (by exact_mod_cast hn.ne'), mul_one]; ring)
  have hgr_step : ∀ n k, 0 < n → (gr n (k + 1) : ℝ) - gr n k = ((t : ℝ) - s) / n := by
    intro n k hn
    rw [hgr_coe, hgr_coe]; push_cast; ring
  have hgr_le : ∀ n k, 0 < n → gr n k ≤ gr n (k + 1) := fun n k hn => by
    have := hgr_step n k hn
    have : (0 : ℝ) ≤ ((t : ℝ) - s) / n := div_nonneg hts (Nat.cast_nonneg n)
    exact NNReal.coe_le_coe.1 (by linarith)
  have hgr_s : ∀ n k, s ≤ gr n k := fun n k => NNReal.coe_le_coe.1 (by
    rw [hgr_coe]; exact le_add_of_nonneg_right (by positivity))
  -- per-step quantities
  set ΔB : ℕ → ℕ → Ω → ℝ := fun n k ω => B (gr n (k + 1)) ω - B (gr n k) ω with hΔB
  set ρ : ℕ → ℕ → Ω → ℝ := fun n k ω => M (gr n (k + 1)) ω - M (gr n k) ω
    - partialSnd F (Λ (gr n k) ω, B (gr n k) ω) * ΔB n k ω
    - 1 / 2 * partialSndSnd F (Λ (gr n k) ω, B (gr n k) ω) *
      (ΔB n k ω ^ 2 - ((gr n (k + 1) : ℝ) - gr n k)) with hρ
  have hF1 : ContDiff ℝ 2 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
  have hPSc : Continuous (partialSnd F) :=
    (hF.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hPSSc : Continuous (partialSndSnd F) :=
    ((hF1.continuous_fderiv (by norm_num)).clm_apply continuous_const).clm_apply continuous_const
  have hPSb : ∀ p, |partialSnd F p| ≤ C := fun p => by
    rw [← Real.norm_eq_abs, partialSnd]
    exact ((fderiv ℝ F p).le_opNorm _).trans (by rw [norm_zero_one, mul_one]; exact hD1 p)
  have hPSSb : ∀ p, |partialSndSnd F p| ≤ C := fun p => (abs_partialSndSnd_le p).trans (hD2 p)
  have hXm : ∀ r, Measurable[𝓕 r] (fun ω => (Λ r ω, B r ω)) := fun r =>
    (hΛm r).prodMk (hB.2.1 r)
  -- the expectation of a step is that of its remainder
  have hstep_exp : ∀ n k, 0 < n →
      ∫ ω, ξ ω * (M (gr n (k + 1)) ω - M (gr n k) ω) ∂P = ∫ ω, ξ ω * ρ n k ω ∂P := by
    intro n k hn
    set a := gr n k
    set b := gr n (k + 1)
    have hab := hgr_le n k hn
    have hξa : Measurable[𝓕 a] ξ := hξ.mono (𝓕.mono (hgr_s n k)) le_rfl
    set g1 : Ω → ℝ := fun ω => ξ ω * partialSnd F (Λ a ω, B a ω)
    set g2 : Ω → ℝ := fun ω => ξ ω * (1 / 2 * partialSndSnd F (Λ a ω, B a ω))
    have hg1 : Measurable[𝓕 a] g1 := hξa.mul (hPSc.measurable.comp (hXm a))
    have hg2 : Measurable[𝓕 a] g2 :=
      hξa.mul (measurable_const.mul (hPSSc.measurable.comp (hXm a)))
    have hg1b : ∀ ω, ‖g1 ω‖ ≤ C := fun ω => by
      rw [Real.norm_eq_abs, abs_mul]
      exact (mul_le_of_le_one_left (abs_nonneg _) (hξb ω)).trans (hPSb _)
    have hg2b : ∀ ω, ‖g2 ω‖ ≤ C := fun ω => by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      refine (mul_le_of_le_one_left (by positivity) (hξb ω)).trans ?_
      linarith [hPSSb (Λ a ω, B a ω), abs_nonneg (partialSndSnd F (Λ a ω, B a ω))]
    have hi1 : Integrable (fun ω => g1 ω * (B b ω - B a ω)) P :=
      (hB.integrable_incr hab).bdd_mul (hg1.mono (𝓕.le a) le_rfl).aestronglyMeasurable
        (Eventually.of_forall hg1b)
    have hi2 : Integrable (fun ω => g2 ω * ((B b ω - B a ω) ^ 2 - ((b : ℝ) - a))) P :=
      ((hB.integrable_incr_sq hab).sub (integrable_const _)).bdd_mul
        (hg2.mono (𝓕.le a) le_rfl).aestronglyMeasurable (Eventually.of_forall hg2b)
    have hz1 : ∫ ω, g1 ω * (B b ω - B a ω) ∂P = 0 := by
      have := hB.integral_mul_incr hab hg1 (φ := id) measurable_id
      simp only [id] at this
      rw [this, hB.integral_incr hab, mul_zero]
    have hz2 : ∫ ω, g2 ω * ((B b ω - B a ω) ^ 2 - ((b : ℝ) - a)) ∂P = 0 := by
      have := hB.integral_mul_incr hab hg2 (φ := fun x => x ^ 2 - ((b : ℝ) - a))
        ((measurable_id.pow_const 2).sub measurable_const)
      rw [this, integral_sub (hB.integrable_incr_sq hab) (integrable_const _),
        hB.integral_incr_sq hab, integral_const, probReal_univ, one_smul, sub_self, mul_zero]
    have hiM : Integrable (fun ω => ξ ω * (M b ω - M a ω)) P :=
      ((hMi b).sub (hMi a)).bdd_mul hξm.aestronglyMeasurable
        (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hξb ω)
    have hsplit : (fun ω => ξ ω * (M b ω - M a ω)) = fun ω => ξ ω * ρ n k ω +
        (g1 ω * (B b ω - B a ω) + g2 ω * ((B b ω - B a ω) ^ 2 - ((b : ℝ) - a))) := by
      funext ω; simp only [hρ, hΔB, g1, g2, a, b]; ring
    have hiρ : Integrable (fun ω => ξ ω * ρ n k ω) P := by
      have : (fun ω => ξ ω * ρ n k ω) = fun ω => ξ ω * (M b ω - M a ω) -
          (g1 ω * (B b ω - B a ω) + g2 ω * ((B b ω - B a ω) ^ 2 - ((b : ℝ) - a))) := by
        funext ω; simp only [hρ, hΔB, g1, g2, a, b]; ring
      rw [this]; exact hiM.sub (hi1.add hi2)
    have hi12 : Integrable (fun ω => g1 ω * (B b ω - B a ω) +
        g2 ω * ((B b ω - B a ω) ^ 2 - ((b : ℝ) - a))) P := hi1.add hi2
    rw [hsplit, integral_add hiρ hi12, integral_add hi1 hi2, hz1, hz2]
    ring
  -- measurability and integrability of the remainders
  have hρm : ∀ n k, Measurable (ρ n k) := fun n k =>
    ((((hMm _).mono (𝓕.le _) le_rfl).sub ((hMm _).mono (𝓕.le _) le_rfl)).sub
      ((hPSc.measurable.comp ((hXm _).mono (𝓕.le _) le_rfl)).mul ((hBm _).sub (hBm _)))).sub
      ((measurable_const.mul (hPSSc.measurable.comp ((hXm _).mono (𝓕.le _) le_rfl))).mul
        ((((hBm _).sub (hBm _)).pow_const 2).sub measurable_const))
  have hρi : ∀ n k, 0 < n → Integrable (ρ n k) P := by
    intro n k hn
    have hab := hgr_le n k hn
    have hi1 : Integrable (fun ω => partialSnd F (Λ (gr n k) ω, B (gr n k) ω) * ΔB n k ω) P :=
      (hB.integrable_incr hab).bdd_mul
        ((hPSc.measurable.comp ((hXm _).mono (𝓕.le _) le_rfl))).aestronglyMeasurable
        (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hPSb _)
    have hi2 : Integrable (fun ω => 1 / 2 * partialSndSnd F (Λ (gr n k) ω, B (gr n k) ω) *
        (ΔB n k ω ^ 2 - ((gr n (k + 1) : ℝ) - gr n k))) P :=
      ((hB.integrable_incr_sq hab).sub (integrable_const _)).bdd_mul (c := C)
        (measurable_const.mul (hPSSc.measurable.comp ((hXm _).mono (𝓕.le _) le_rfl))).aestronglyMeasurable
        (Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
          linarith [hPSSb (Λ (gr n k) ω, B (gr n k) ω),
            abs_nonneg (partialSndSnd F (Λ (gr n k) ω, B (gr n k) ω))])
    exact (((hMi _).sub (hMi _)).sub hi1).sub hi2
  -- the pathwise bound on each remainder
  set Rk : ℕ → ℕ → Ω → ℝ := fun n k ω => stepRemainder F (fun r => Λ r.toNNReal ω)
    (fun r => lam r ω) (fun r => B r.toNNReal ω) (gr n k) (gr n (k + 1)) with hRk
  have hρ_bound : ∀ n k, 0 < n → ∀ ω, |ρ n k ω| ≤ C * |ΔB n k ω| ^ 3 + Rk n k ω := by
    intro n k hn ω
    have hab : ((gr n k : ℝ≥0) : ℝ) ≤ gr n (k + 1) := hgr_le n k hn
    have hpath : ∀ r ∈ uIcc ((gr n k : ℝ≥0) : ℝ) (gr n (k + 1)),
        Λ r.toNNReal ω = Λ (((gr n k : ℝ≥0) : ℝ)).toNNReal ω + ∫ x in ((gr n k : ℝ≥0) : ℝ)..r, lam x ω :=
      fun r hr => by
        rw [uIcc_of_le hab] at hr
        exact path_eq_add_integral hlam hΛ ω (gr n k).coe_nonneg ((gr n k).coe_nonneg.trans hr.1)
    have h := pathwise_step hF hC0 hD1 hLip2 (Λp := fun r => Λ r.toNNReal ω)
      (lamp := fun r => lam r ω) (Bp := fun r => B r.toNNReal ω) hab (hlam ω).intervalIntegrable
      hpath ((hΛc ω).comp continuous_real_toNNReal).continuousOn
      ((hBc ω).comp continuous_real_toNNReal).continuousOn
    simp only [Real.toNNReal_coe] at h
    have hM : M (gr n (k + 1)) ω - M (gr n k) ω = F (Λ (gr n (k + 1)) ω, B (gr n (k + 1)) ω)
        - F (Λ (gr n k) ω, B (gr n k) ω)
        - ∫ r in ((gr n k : ℝ≥0) : ℝ)..gr n (k + 1),
            itoGen F (Λ r.toNNReal ω, B r.toNNReal ω) (lam r ω) := by
      have hI := intervalIntegral.integral_interval_sub_left (a := 0)
        (b := ((gr n (k + 1) : ℝ≥0) : ℝ)) (c := ((gr n k : ℝ≥0) : ℝ))
        (intervalIntegrable_itoGen hF hD1 hD2 (hXc ω) (hlam ω) 0 _)
        (intervalIntegrable_itoGen hF hD1 hD2 (hXc ω) (hlam ω) 0 _)
      simp only [hMdef, itoDynkinProcess]
      rw [← hI]
      ring
    simp only [hρ, hΔB, hRk]
    rw [hM]
    exact h
  -- uniform bound on the summed remainders
  have hR_le : ∀ n, 0 < n → ∀ ω, ∑ k ∈ Finset.range n, Rk n k ω ≤ 2 * C * K + C * ((t : ℝ) - s) := by
    intro n hn ω
    have hstepk : ∀ k ∈ Finset.range n, Rk n k ω ≤
        2 * C * (∫ r in ((gr n k : ℝ≥0) : ℝ)..gr n (k + 1), ‖lam r ω‖) +
          1 / 2 * (2 * C * (((gr n (k + 1) : ℝ≥0) : ℝ) - gr n k)) := by
      intro k _
      refine stepRemainder_le hF (hgr_le n k hn) (hlam ω).intervalIntegrable
        ((hΛc ω).comp continuous_real_toNNReal).continuousOn
        ((hBc ω).comp continuous_real_toNNReal).continuousOn (fun r _ => ?_) (fun r _ => ?_)
      · exact (norm_partialFst_sub_le _ _).trans ((norm_sub_le _ _).trans
          ((add_le_add (hD1 _) (hD1 _)).trans_eq (by ring)))
      · exact (abs_sub _ _).trans ((add_le_add (hPSSb _) (hPSSb _)).trans_eq (by ring))
    have hsumI : ∑ k ∈ Finset.range n, ∫ r in ((gr n k : ℝ≥0) : ℝ)..gr n (k + 1), ‖lam r ω‖ =
        ∫ r in (s : ℝ)..t, ‖lam r ω‖ := by
      rw [intervalIntegral.sum_integral_adjacent_intervals (a := fun k => ((gr n k : ℝ≥0) : ℝ))
        fun k _ => (hlam ω).norm.intervalIntegrable, hgr0, hgrn n hn]
    have hsumL : ∑ k ∈ Finset.range n, (((gr n (k + 1) : ℝ≥0) : ℝ) - gr n k) = (t : ℝ) - s := by
      rw [Finset.sum_range_sub (f := fun k => ((gr n k : ℝ≥0) : ℝ)), hgr0, hgrn n hn]
    have hIK : ∫ r in (s : ℝ)..t, ‖lam r ω‖ ≤ K := by
      rw [intervalIntegral.integral_of_le hst']
      exact (setIntegral_le_integral (hlam ω).norm
        (Eventually.of_forall fun _ => norm_nonneg _)).trans (hK ω)
    refine (Finset.sum_le_sum hstepk).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hsumI, hsumL]
    nlinarith
  -- the sums and their limits
  set Sρ : ℕ → Ω → ℝ := fun n ω => ∑ k ∈ Finset.range n, |ρ n k ω| with hSρ
  set T : ℕ → Ω → ℝ := fun n ω => ∑ k ∈ Finset.range n, |ΔB n k ω| ^ 3 with hT
  set G : ℕ → Ω → ℝ := fun n ω => max (Sρ n ω - C * T n ω) 0 with hG
  have hRnn : ∀ n, 0 < n → ∀ ω, 0 ≤ ∑ k ∈ Finset.range n, Rk n k ω := fun n hn ω =>
    Finset.sum_nonneg fun k _ => stepRemainder_nonneg (hgr_le n k hn)
  have hG_le : ∀ n, 0 < n → ∀ ω, G n ω ≤ ∑ k ∈ Finset.range n, Rk n k ω := by
    intro n hn ω
    refine max_le ?_ (hRnn n hn ω)
    have h : Sρ n ω ≤ ∑ k ∈ Finset.range n, (C * |ΔB n k ω| ^ 3 + Rk n k ω) :=
      Finset.sum_le_sum fun k _ => hρ_bound n k hn ω
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at h
    simp only [hT]; linarith
  have hGnn : ∀ n ω, 0 ≤ G n ω := fun n ω => le_max_right _ _
  set Kb := 2 * C * K + C * ((t : ℝ) - s) with hKb
  have hKb0 : 0 ≤ Kb := by
    obtain ⟨ω⟩ : Nonempty Ω := by
      by_contra h
      rw [not_nonempty_iff] at h
      have := hP.measure_univ
      rw [Set.univ_eq_empty_iff.2 h, measure_empty] at this
      exact zero_ne_one this
    have := hK0 ω
    positivity
  have hG_bd : ∀ n ω, G n ω ≤ Kb := by
    intro n ω
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [hG, hSρ, hT, Finset.range_zero, Finset.sum_empty, mul_zero, sub_zero, max_self]
      exact hKb0
    · exact (hG_le n hn ω).trans (hR_le n hn ω)
  have hGm : ∀ n, Measurable (G n) := fun n =>
    ((Finset.measurable_sum _ fun k _ => continuous_abs.measurable.comp (hρm n k)).sub
      (measurable_const.mul (Finset.measurable_sum _ fun k _ =>
        (continuous_abs.measurable.comp ((hBm _).sub (hBm _))).pow_const 3))).max
      measurable_const
  have hR_tend : ∀ ω, Tendsto (fun n => ∑ k ∈ Finset.range n, Rk n k ω) atTop (𝓝 0) := by
    intro ω
    have h := tendsto_sum_stepRemainder hF hC0 hLip1 hLipD2 (Λp := fun r => Λ r.toNNReal ω)
      (lamp := fun r => lam r ω) (Bp := fun r => B r.toNNReal ω) hst' (hlam ω).intervalIntegrable
      ((hΛc ω).comp continuous_real_toNNReal).continuousOn
      ((hBc ω).comp continuous_real_toNNReal).continuousOn
    refine h.congr fun n => Finset.sum_congr rfl fun k _ => ?_
    simp only [hRk, hgr_coe, Nat.cast_add, Nat.cast_one]
  have hG_tend : ∀ ω, Tendsto (fun n => G n ω) atTop (𝓝 0) := fun ω =>
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hR_tend ω)
      (Eventually.of_forall fun n => hGnn n ω)
      ((eventually_gt_atTop 0).mono fun n hn => hG_le n hn ω)
  have hIG : Tendsto (fun n => ∫ ω, G n ω ∂P) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (fun _ => Kb)
      (fun n => (hGm n).aestronglyMeasurable) (integrable_const (μ := P) Kb)
      (fun n => Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hGnn n ω)]; exact hG_bd n ω)
      (Eventually.of_forall hG_tend)
    simpa only [integral_zero] using h
  set m3 := QuantumZipper.gaussianAbsMoment 3 with hm3
  have hT_int : ∀ n, 0 < n → ∫ ω, T n ω ∂P ≤
      n * (m3 * (((t : ℝ) - s) / n * Real.sqrt (((t : ℝ) - s) / n))) := by
    intro n hn
    rw [integral_finsetSum _ fun k _ => hB.integrable_abs_incr_pow (hgr_le n k hn) 3]
    have hk : ∀ k ∈ Finset.range n, ∫ ω, |ΔB n k ω| ^ 3 ∂P ≤
        m3 * (((t : ℝ) - s) / n * Real.sqrt (((t : ℝ) - s) / n)) := fun k _ => by
      have h := hB.integral_abs_incr_pow_three_le (hgr_le n k hn)
      rwa [hgr_step n k hn] at h
    refine (Finset.sum_le_sum hk).trans_eq ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hmain : ∀ n, 0 < n → |∫ ω, ξ ω * (M t ω - M s ω) ∂P| ≤
      ∫ ω, G n ω ∂P + C * (n * (m3 * (((t : ℝ) - s) / n * Real.sqrt (((t : ℝ) - s) / n)))) := by
    intro n hn
    have htel : ∀ ω, M t ω - M s ω =
        ∑ k ∈ Finset.range n, (M (gr n (k + 1)) ω - M (gr n k) ω) := fun ω => by
      rw [Finset.sum_range_sub (f := fun k => M (gr n k) ω), hgrn n hn, hgr0]
    have hint : ∀ k ∈ Finset.range n,
        Integrable (fun ω => ξ ω * (M (gr n (k + 1)) ω - M (gr n k) ω)) P := fun k _ =>
      ((hMi _).sub (hMi _)).bdd_mul hξm.aestronglyMeasurable
        (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hξb ω)
    have e1 : ∫ ω, ξ ω * (M t ω - M s ω) ∂P = ∑ k ∈ Finset.range n, ∫ ω, ξ ω * ρ n k ω ∂P := by
      simp_rw [htel, Finset.mul_sum]
      rw [integral_finsetSum _ hint]
      exact Finset.sum_congr rfl fun k _ => hstep_exp n k hn
    rw [e1]
    have e2 : ∀ k, |∫ ω, ξ ω * ρ n k ω ∂P| ≤ ∫ ω, |ρ n k ω| ∂P := fun k => by
      refine abs_integral_le_integral_abs.trans (integral_mono
        ((hρi n k hn).bdd_mul hξm.aestronglyMeasurable
          (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hξb ω)).abs
        (hρi n k hn).abs fun ω => ?_)
      simp only [abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) (hξb ω)
    have e3 : ∑ k ∈ Finset.range n, ∫ ω, |ρ n k ω| ∂P = ∫ ω, Sρ n ω ∂P :=
      (integral_finsetSum _ fun k _ => (hρi n k hn).abs).symm
    have hTi : Integrable (T n) P :=
      integrable_finsetSum _ fun k _ => hB.integrable_abs_incr_pow (hgr_le n k hn) 3
    have hGi : Integrable (G n) P := (integrable_const Kb).mono' (hGm n).aestronglyMeasurable
      (Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hGnn n ω)]; exact hG_bd n ω)
    have e4 : ∫ ω, Sρ n ω ∂P ≤ ∫ ω, G n ω ∂P + C * ∫ ω, T n ω ∂P := by
      rw [← integral_const_mul, ← integral_add hGi (hTi.const_mul C)]
      refine integral_mono (integrable_finsetSum _ fun k _ => (hρi n k hn).abs)
        (hGi.add (hTi.const_mul C)) fun ω => ?_
      have := le_max_left (Sρ n ω - C * T n ω) 0
      simp only [hG] at this ⊢
      linarith
    calc |∑ k ∈ Finset.range n, ∫ ω, ξ ω * ρ n k ω ∂P|
        ≤ ∑ k ∈ Finset.range n, |∫ ω, ξ ω * ρ n k ω ∂P| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range n, ∫ ω, |ρ n k ω| ∂P := Finset.sum_le_sum fun k _ => e2 k
      _ = ∫ ω, Sρ n ω ∂P := e3
      _ ≤ ∫ ω, G n ω ∂P + C * ∫ ω, T n ω ∂P := e4
      _ ≤ _ := by gcongr; exact hT_int n hn
  have hb : Tendsto (fun n : ℕ => ∫ ω, G n ω ∂P +
      C * (n * (m3 * (((t : ℝ) - s) / n * Real.sqrt (((t : ℝ) - s) / n))))) atTop (𝓝 0) := by
    have h0 := (tendsto_const_div_atTop_nhds_zero_nat ((t : ℝ) - s)).sqrt
    rw [Real.sqrt_zero] at h0
    have h1 : Tendsto (fun n : ℕ => C * (m3 * (((t : ℝ) - s) * Real.sqrt (((t : ℝ) - s) / n))))
        atTop (𝓝 0) := by
      simpa only [mul_zero] using ((h0.const_mul ((t : ℝ) - s)).const_mul m3).const_mul C
    have h2 : Tendsto (fun n : ℕ => C * (n * (m3 * (((t : ℝ) - s) / n *
        Real.sqrt (((t : ℝ) - s) / n))))) atTop (𝓝 0) := by
      refine h1.congr' ((eventually_gt_atTop 0).mono fun n hn => ?_)
      have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      field_simp
    simpa only [add_zero] using hIG.add h2
  have hle := ge_of_tendsto hb ((eventually_gt_atTop 0).mono fun n hn => hmain n hn)
  exact abs_nonpos_iff.1 hle

omit [MeasurableSpace E] [BorelSpace E] in
/-- Every path of the process of `martingale_itoDynkin` is continuous. -/
theorem continuous_itoDynkinProcess (hBc : ∀ ω, Continuous (B · ω)) {F : E × ℝ → ℝ}
    (hF : ContDiff ℝ 3 F) (hFc : HasCompactSupport F) (hlam : ∀ ω, Integrable (fun s => lam s ω))
    (hΛ : ∀ ω (t : ℝ≥0), Λ t ω = Λ 0 ω + ∫ s in (0 : ℝ)..t, lam s ω) (ω : Ω) :
    Continuous fun t => itoDynkinProcess F Λ lam B t ω := by
  obtain ⟨C, -, -, hD1, hD2, -⟩ := exists_bound_of_contDiff_three hF hFc
  have hΛc := continuous_of_eq_add_integral hlam hΛ ω
  have hXc : Continuous fun r : ℝ => (Λ r.toNNReal ω, B r.toNNReal ω) :=
    (hΛc.comp continuous_real_toNNReal).prodMk ((hBc ω).comp continuous_real_toNNReal)
  exact (hF.continuous.comp (hΛc.prodMk (hBc ω))).sub
    ((intervalIntegral.continuous_primitive
      (fun a b => intervalIntegrable_itoGen hF hD1 hD2 hXc (hlam ω) a b) 0).comp
      NNReal.continuous_coe)

/-- **Itô's formula for `F(Λ_t, B_t)` in an arbitrary filtration** (Revuz–Yor IV.3.3, martingale form).
Let `B` be an `𝓕`-Brownian motion (`IsFilteredBrownianReal`) with every path continuous, let `Λ` be an
`𝓕`-adapted process in a finite-dimensional space with `Λ_t = Λ_0 + ∫₀ᵗ λ_s ds` along every path,
`λ(·, ω)` integrable with `∫ ‖λ(·, ω)‖ ≤ K`, and let `F : E × ℝ → ℝ` be `C³` with compact support.
Then `F(Λ_t, B_t) − ∫₀ᵗ (∂_Λ F(Λ_s, B_s) λ_s + ½ ∂²_x F(Λ_s, B_s)) ds` is an `𝓕`-martingale. -/
theorem martingale_itoDynkin (hB : IsFilteredBrownianReal 𝓕 B P) (hBc : ∀ ω, Continuous (B · ω))
    {F : E × ℝ → ℝ} (hF : ContDiff ℝ 3 F) (hFc : HasCompactSupport F)
    (hΛm : ∀ t, Measurable[𝓕 t] (Λ t)) (hlam : ∀ ω, Integrable (fun s => lam s ω))
    (hΛ : ∀ ω (t : ℝ≥0), Λ t ω = Λ 0 ω + ∫ s in (0 : ℝ)..t, lam s ω) {K : ℝ}
    (hK : ∀ ω, ∫ s, ‖lam s ω‖ ≤ K) :
    Martingale (itoDynkinProcess F Λ lam B) 𝓕 P := by
  have hP := hB.isProbabilityMeasure'
  obtain ⟨C, hC0, hF0, hD1, hD2, hLip1, hLipD2, hLip2⟩ := exists_bound_of_contDiff_three hF hFc
  have hΛc := continuous_of_eq_add_integral hlam hΛ
  have hXm : ∀ t, Measurable[𝓕 t] (fun ω => (Λ t ω, B t ω)) := fun t => (hΛm t).prodMk (hB.2.1 t)
  have hXc : ∀ ω, Continuous fun t : ℝ≥0 => (Λ t ω, B t ω) := fun ω => (hΛc ω).prodMk (hBc ω)
  have hF1 : ContDiff ℝ 2 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
  have hPSSc : Continuous (partialSndSnd F) :=
    ((hF1.continuous_fderiv (by norm_num)).clm_apply continuous_const).clm_apply continuous_const
  have hPFc : Continuous (partialFst F) :=
    (hF.continuous_fderiv (by norm_num)).clm_comp continuous_const
  -- adaptedness
  have hMm : ∀ t, Measurable[𝓕 t] (itoDynkinProcess F Λ lam B t) := by
    intro t
    have h1 := measurable_integral_partialFst hF hB.2.1 hBc hΛm hlam hΛ (𝓕 := 𝓕) t
    have h2 := QuantumZipper.Dynkin.measurable_integral_adapted 𝓕 hXm hXc hPSSc t
    have heq : (itoDynkinProcess F Λ lam B t) = fun ω => F (Λ t ω, B t ω) -
        ((∫ s in (0 : ℝ)..t, partialFst F (Λ s.toNNReal ω, B s.toNNReal ω) (lam s ω)) +
          1 / 2 * ∫ s in (0 : ℝ)..t, partialSndSnd F (Λ s.toNNReal ω, B s.toNNReal ω)) := by
      funext ω
      have hXr : Continuous fun r : ℝ => (Λ r.toNNReal ω, B r.toNNReal ω) :=
        ((hΛc ω).comp continuous_real_toNNReal).prodMk ((hBc ω).comp continuous_real_toNNReal)
      have hi1 : IntervalIntegrable (fun s => partialFst F (Λ s.toNNReal ω, B s.toNNReal ω)
          (lam s ω)) volume 0 t :=
        intervalIntegrable_clm_apply (hPFc.comp hXr).continuousOn (hlam ω).intervalIntegrable
      have hi2 : IntervalIntegrable (fun s => partialSndSnd F (Λ s.toNNReal ω, B s.toNNReal ω))
          volume 0 t := (hPSSc.comp hXr).intervalIntegrable _ _
      simp only [itoDynkinProcess, itoGen]
      rw [intervalIntegral.integral_add hi1 (hi2.const_mul _), intervalIntegral.integral_const_mul]
    rw [heq]
    exact (hF.continuous.measurable.comp (hXm t)).sub (h1.add (measurable_const.mul h2))
  have hKey := fun s t (hst : s ≤ t) ξ (hξ : Measurable[𝓕 s] ξ) (hξb : ∀ ω, |ξ ω| ≤ 1) =>
    integral_mul_itoDynkinProcess_sub (P := P) hB hBc hF hC0 hF0 hD1 hD2 hLip1 hLipD2 hLip2 hΛm hlam
      hΛ hK hMm hst hξ hξb
  -- integrability
  have hK0 : 0 ≤ K := by
    obtain ⟨ω⟩ : Nonempty Ω := by
      by_contra h
      rw [not_nonempty_iff] at h
      have := hP.measure_univ
      rw [Set.univ_eq_empty_iff.2 h, measure_empty] at this
      exact zero_ne_one this
    exact (integral_nonneg fun _ => norm_nonneg _).trans (hK ω)
  have hMi : ∀ r, Integrable (itoDynkinProcess F Λ lam B r) P := by
    intro r
    refine (integrable_const (C + (C * K + C / 2 * r))).mono'
      ((hMm r).mono (𝓕.le r) le_rfl).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
    have h1 := abs_integral_itoGen_le hD1 hD2 (X := fun x : ℝ => (Λ x.toNNReal ω, B x.toNNReal ω))
      (hlam ω) (hK ω) r.coe_nonneg
    rw [sub_zero] at h1
    rw [Real.norm_eq_abs]
    exact (abs_sub _ _).trans (add_le_add (hF0 _) h1)
  refine ⟨fun t => (hMm t).stronglyMeasurable, fun s t hst => ?_⟩
  refine (ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le s) (hMi t)
    (fun A _ _ => (hMi s).integrableOn) (fun A hA _ => ?_)
    ((hMm s).stronglyMeasurable.aestronglyMeasurable)).symm
  have hAm : MeasurableSet A := 𝓕.le s A hA
  set ξ : Ω → ℝ := A.indicator (fun _ => (1 : ℝ)) with hξdef
  have hξm : Measurable[𝓕 s] ξ := measurable_const.indicator hA
  have hξb : ∀ ω, |ξ ω| ≤ 1 := fun ω => by by_cases hω : ω ∈ A <;> simp [hξdef, hω]
  have hξA : ∀ f : Ω → ℝ, ∫ ω, ξ ω * f ω ∂P = ∫ ω in A, f ω ∂P := by
    intro f
    rw [← integral_indicator hAm]
    congr 1
    funext ω
    by_cases hω : ω ∈ A <;> simp [hξdef, hω]
  have h0 := hKey s t hst ξ hξm hξb
  have hi : ∀ r, Integrable (fun ω => ξ ω * itoDynkinProcess F Λ lam B r ω) P := fun r =>
    (hMi r).bdd_mul (hξm.mono (𝓕.le s) le_rfl).aestronglyMeasurable
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hξb ω)
  have : ∫ ω, ξ ω * (itoDynkinProcess F Λ lam B t ω - itoDynkinProcess F Λ lam B s ω) ∂P =
      (∫ ω, ξ ω * itoDynkinProcess F Λ lam B t ω ∂P) - ∫ ω, ξ ω * itoDynkinProcess F Λ lam B s ω ∂P := by
    rw [← integral_sub (hi t) (hi s)]
    congr 1; funext ω; ring
  rw [this, sub_eq_zero, hξA, hξA] at h0
  exact h0.symm

end Engine

end Ito

end InteractingSLE
