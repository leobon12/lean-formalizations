/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.TwoForceMain2Riemann

/-!
# The left-endpoint freeze without a filtration inclusion (Aux. lemma 47, (GB4))

Packet PROVE-WHOLEFIELD3 (follow-up note C.2, `ig1_followup_proofs.txt` L1515–1527; additional note §7.4, Aux. 47,
`ig1_additional_proofs.txt` L3078–3092: "the sums `∑ k_{tᵢ}(z)⁻¹ (M_{tᵢ₊₁∧t}(z) − M_{tᵢ∧t}(z))` are enlarged-filtration
martingales and converge in `L²` on localizations to `B_t`").

`Sec7.martingale_of_bracket_freeze` assumes `𝓕 ≤ 𝒢`, where `𝓕` carries the brackets of (GB3). In the whole-field
identification the brackets live in the usual augmentation of the evolution's filtration, which is **not** contained
in the germ filtration `𝒢` (that one contains only the driving filtration). The inclusion is used in that proof for
one thing only: the frozen weights `k(tᵢ)⁻¹` must be `𝒢`-measurable. `martingale_of_bracket_freeze_of_adapted` is the
same statement with `𝓕 ≤ 𝒢` replaced by `𝒢`-adaptedness of the coefficient `k`; its proof is the landed one with
that single change (the `L²` computation of the defects is filtration-free; it runs in `𝓕`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace WholeField

open Sec7

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}

/-- **The left-endpoint freeze, with adapted weights instead of `𝓕 ≤ 𝒢`** (`Sec7.martingale_of_bracket_freeze`
with its inclusion hypothesis replaced by `hkaG`). Let `X, Y` be bounded `𝓕`-martingales with brackets
`⟨X⟩ = ∫ e k²`, `⟨X, Y⟩ = ∫ e k`, `⟨Y⟩ = ∫ e`, with a continuous coefficient `c ≤ |k| ≤ C` adapted to both `𝓕` and
`𝒢`, and a measurable weight `0 ≤ e ≤ 1`. If `X` is a `𝒢`-martingale and `Y` is `𝒢`-adapted, then `Y` is a
`𝒢`-martingale. -/
theorem martingale_of_bracket_freeze_of_adapted [IsProbabilityMeasure P] {𝒢 : Filtration ℝ≥0 mΩ}
    {X Y : ℝ≥0 → Ω → ℝ} {k e : ℝ → Ω → ℝ}
    (hX : Martingale X 𝓕 P) (hY : Martingale Y 𝓕 P)
    {K : ℝ} (hXb : ∀ t, ∀ᵐ ω ∂P, |X t ω| ≤ K) (hYb : ∀ t, ∀ᵐ ω ∂P, |Y t ω| ≤ K)
    (hXX : Martingale (fun t ω => X t ω ^ 2 - ∫ u in (0 : ℝ)..t, e u ω * k u ω ^ 2) 𝓕 P)
    (hXY : Martingale (fun t ω => X t ω * Y t ω - ∫ u in (0 : ℝ)..t, e u ω * k u ω) 𝓕 P)
    (hYY : Martingale (fun t ω => Y t ω ^ 2 - ∫ u in (0 : ℝ)..t, e u ω) 𝓕 P)
    (hkc : ∀ ω, Continuous fun u => k u ω) (hka : ∀ p : ℝ≥0, StronglyMeasurable[𝓕 p] (k p))
    (hkaG : ∀ p : ℝ≥0, StronglyMeasurable[𝒢 p] (k p))
    {c C : ℝ} (hc : 0 < c) (hkb : ∀ u ω, c ≤ |k u ω|) (hkC : ∀ u ω, |k u ω| ≤ C)
    (he : ∀ ω, Measurable fun u => e u ω) (he0 : ∀ u ω, 0 ≤ e u ω) (he1 : ∀ u ω, e u ω ≤ 1)
    (hXG : Martingale X 𝒢 P) (hYG : StronglyAdapted 𝒢 Y) :
    Martingale Y 𝒢 P := by
  refine ⟨hYG, fun s t hst => ?_⟩
  refine (ae_eq_condExp_of_forall_setIntegral_eq (𝒢.le s) (hY.integrable t)
    (fun A _ _ => (hY.integrable s).integrableOn) (fun A hA _ => ?_)
    (hYG s).aestronglyMeasurable).symm
  have hA' : MeasurableSet A := 𝒢.le s A hA
  -- notation for the partitions, weights, sums and defects
  set π : ℕ → ℕ → ℝ≥0 := fun n i => MathFin.unifPartIcc s t n i with hπ
  set l : ℕ → ℕ → Ω → ℝ := fun n i ω => (k (π n i) ω)⁻¹ with hl
  have hlm : ∀ n i, StronglyMeasurable[𝓕 (π n i)] (l n i) := fun n i =>
    (hka _).measurable.inv.stronglyMeasurable
  have hlb : ∀ n i ω, |l n i ω| ≤ c⁻¹ := fun n i ω => by
    simp only [hl, abs_inv]
    exact inv_anti₀ hc (hkb _ ω)
  set D : ℕ → ℕ → Ω → ℝ := fun n i ω => (Y (π n (i + 1)) ω - Y (π n i) ω)
    - l n i ω * (X (π n (i + 1)) ω - X (π n i) ω) with hD
  set R : ℕ → Ω → ℝ := fun n ω =>
    ∑ i ∈ Finset.range n, l n i ω * (X (π n (i + 1)) ω - X (π n i) ω) with hR
  have hπm : ∀ n, Monotone (π n) := fun n => MathFin.unifPartIcc_mono s t n
  have hsπ : ∀ n i, s ≤ π n i := fun n i => le_self_add
  -- (a) the Riemann sums have zero integral over `A`
  have hRA : ∀ n, ∫ ω in A, R n ω ∂P = 0 := by
    intro n
    rw [← integral_indicator hA']
    have hpt : A.indicator (R n) = fun ω => ∑ i ∈ Finset.range n,
        A.indicator (l n i) ω * (X (π n (i + 1)) ω - X (π n i) ω) := by
      funext ω
      by_cases hω : ω ∈ A
      · simp [hR, hω, Set.indicator_of_mem]
      · simp [hR, hω, Set.indicator_of_notMem]
    rw [hpt, integral_finsetSum]
    · refine Finset.sum_eq_zero fun i _ => ?_
      refine integral_mul_increment_eq_zero hXG (hπm n (Nat.le_succ i))
        (((hkaG _).measurable.inv.stronglyMeasurable).indicator (𝒢.mono (hsπ n i) A hA)) (C := c⁻¹)
        (Eventually.of_forall fun ω => ?_)
      by_cases hω : ω ∈ A
      · rw [Set.indicator_of_mem hω]; exact hlb n i ω
      · rw [Set.indicator_of_notMem hω, abs_zero]; exact inv_nonneg.2 hc.le
    · intro i _
      refine integrable_mul_increment hX _ _
        ((((hlm n i).mono (𝓕.le _)).indicator hA').aestronglyMeasurable) (C := c⁻¹)
        (Eventually.of_forall fun ω => ?_)
      by_cases hω : ω ∈ A
      · rw [Set.indicator_of_mem hω]; exact hlb n i ω
      · rw [Set.indicator_of_notMem hω, abs_zero]; exact inv_nonneg.2 hc.le
  -- measurability and bounds of the defects
  have hDm : ∀ n i, AEStronglyMeasurable (D n i) P := fun n i =>
    ((hY.integrable _).sub (hY.integrable _)).aestronglyMeasurable.sub
      (((hlm n i).mono (𝓕.le _)).aestronglyMeasurable.mul
        ((hX.integrable _).sub (hX.integrable _)).aestronglyMeasurable)
  have hDb : ∀ n i, ∀ᵐ ω ∂P, |D n i ω| ≤ 2 * K + c⁻¹ * (2 * K) := fun n i => by
    filter_upwards [hXb (π n i), hXb (π n (i + 1)), hYb (π n i), hYb (π n (i + 1))]
      with ω h1 h2 h3 h4
    calc |D n i ω| ≤ |Y (π n (i + 1)) ω - Y (π n i) ω|
          + |l n i ω| * |X (π n (i + 1)) ω - X (π n i) ω| := by
          simp only [hD]; rw [← abs_mul]; exact abs_sub _ _
      _ ≤ 2 * K + c⁻¹ * (2 * K) := by
          have a1 : |Y (π n (i + 1)) ω - Y (π n i) ω| ≤ 2 * K := (abs_sub _ _).trans (by linarith)
          have a2 : |X (π n (i + 1)) ω - X (π n i) ω| ≤ 2 * K := (abs_sub _ _).trans (by linarith)
          have := inv_nonneg.2 hc.le
          gcongr
          exact hlb n i ω
  set S : ℕ → Ω → ℝ := fun n ω => ∑ i ∈ Finset.range n, D n i ω with hS
  have hSm : ∀ n, AEStronglyMeasurable (S n) P := fun n =>
    Finset.aestronglyMeasurable_fun_sum _ fun i _ => hDm n i
  have hSb : ∀ n, ∀ᵐ ω ∂P, |S n ω| ≤ n * (2 * K + c⁻¹ * (2 * K)) := fun n => by
    filter_upwards [ae_all_iff.2 (hDb n)] with ω hω
    calc |S n ω| ≤ ∑ i ∈ Finset.range n, |D n i ω| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range n, (2 * K + c⁻¹ * (2 * K)) := Finset.sum_le_sum fun i _ => hω i
      _ = n * (2 * K + c⁻¹ * (2 * K)) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hSL2 : ∀ n, MemLp (S n) 2 P := fun n =>
    MemLp.of_bound (hSm n) _ ((hSb n).mono fun ω h => by rwa [Real.norm_eq_abs])
  -- (c) the increment of `Y` over `A` is the integral of the defect sum
  have hYA : ∀ n, n ≠ 0 → ∫ ω in A, (Y t ω - Y s ω) ∂P = ∫ ω in A, S n ω ∂P := by
    intro n hn
    have hpt : (fun ω => Y t ω - Y s ω) = fun ω => S n ω + R n ω := by
      funext ω
      have htel := Finset.sum_range_sub (fun i => Y (π n i) ω) n
      simp only [hπ, MathFin.unifPartIcc_zero, MathFin.unifPartIcc_self hst hn] at htel
      have hsum : S n ω + R n ω
          = ∑ i ∈ Finset.range n, (Y (π n (i + 1)) ω - Y (π n i) ω) := by
        simp only [hS, hR, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [hD]; ring
      rw [hsum]
      exact htel.symm
    have hRi : Integrable (R n) P := integrable_finsetSum _ fun i _ =>
      integrable_mul_increment hX _ _ ((hlm n i).mono (𝓕.le _)).aestronglyMeasurable
        (Eventually.of_forall (hlb n i))
    rw [hpt, integral_add ((hSL2 n).integrable one_le_two).integrableOn hRi.integrableOn, hRA n,
      add_zero]
  -- (b) the defect sums tend to zero in `L²`
  have hcell : ∀ n i, ∫ ω, D n i ω ^ 2 ∂P = ∫ ω, (((∫ u in (0 : ℝ)..(π n (i + 1) : ℝ), e u ω)
      - ∫ u in (0 : ℝ)..(π n i : ℝ), e u ω)
      - 2 * l n i ω * ((∫ u in (0 : ℝ)..(π n (i + 1) : ℝ), e u ω * k u ω)
        - ∫ u in (0 : ℝ)..(π n i : ℝ), e u ω * k u ω)
      + l n i ω ^ 2 * ((∫ u in (0 : ℝ)..(π n (i + 1) : ℝ), e u ω * k u ω ^ 2)
        - ∫ u in (0 : ℝ)..(π n i : ℝ), e u ω * k u ω ^ 2)) ∂P := fun n i =>
    integral_sq_cell_eq hX hY hXX hXY hYY hXb hYb (hπm n (Nat.le_succ i)) (hlm n i) (hlb n i)
  set F : ℕ → Ω → ℝ := fun n ω => ∑ i ∈ Finset.range n,
    ∫ u in (π n i : ℝ)..(π n (i + 1) : ℝ), e u ω * (1 - l n i ω * k u ω) ^ 2 with hF
  have hst' : (s : ℝ) ≤ t := by exact_mod_cast hst
  set Bd : ℝ := (1 + c⁻¹ * C) ^ 2 with hBd
  -- the frozen integrand is bounded
  have hfb : ∀ n i ω u, e u ω * (1 - l n i ω * k u ω) ^ 2 ≤ Bd := by
    intro n i ω u
    have h1 : |l n i ω * k u ω| ≤ c⁻¹ * C := by
      rw [abs_mul]
      exact mul_le_mul (hlb n i ω) (hkC u ω) (abs_nonneg _) (inv_nonneg.2 hc.le)
    have h2 : (1 - l n i ω * k u ω) ^ 2 ≤ Bd := by
      rw [hBd, ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) ((abs_sub _ _).trans (by rw [abs_one]; linarith)) 2
    calc e u ω * (1 - l n i ω * k u ω) ^ 2 ≤ 1 * (1 - l n i ω * k u ω) ^ 2 :=
          mul_le_mul_of_nonneg_right (he1 u ω) (sq_nonneg _)
      _ ≤ Bd := by rw [one_mul]; exact h2
  have hcellb : ∀ n i ω, 0 ≤ ∫ u in (π n i : ℝ)..(π n (i + 1) : ℝ),
        e u ω * (1 - l n i ω * k u ω) ^ 2 ∧
      ∫ u in (π n i : ℝ)..(π n (i + 1) : ℝ), e u ω * (1 - l n i ω * k u ω) ^ 2
        ≤ Bd * (((t : ℝ) - s) / n) := by
    intro n i ω
    have hpq : ((π n i : ℝ≥0) : ℝ) ≤ (π n (i + 1) : ℝ≥0) := by exact_mod_cast hπm n (Nat.le_succ i)
    have hii : IntervalIntegrable (fun u => e u ω * (1 - l n i ω * k u ω) ^ 2) volume
        (π n i : ℝ) (π n (i + 1) : ℝ) := by
      refine (intervalIntegrable_const (c := Bd)).mono_fun
        ((he ω).mul ((measurable_const.sub (measurable_const.mul (hkc ω).measurable)).pow_const
          2)).aestronglyMeasurable (Eventually.of_forall fun u => ?_)
      show ‖e u ω * (1 - l n i ω * k u ω) ^ 2‖ ≤ ‖Bd‖
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (he0 u ω) (sq_nonneg _)),
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ Bd)]
      exact hfb n i ω u
    refine ⟨intervalIntegral.integral_nonneg hpq fun u _ => mul_nonneg (he0 u ω) (sq_nonneg _),
      ?_⟩
    have h := intervalIntegral.integral_mono_on (μ := volume) hpq hii
      (intervalIntegrable_const (c := Bd)) fun u _ => hfb n i ω u
    simp only [intervalIntegral.integral_const, smul_eq_mul] at h
    have hw := coe_unifPartIcc_succ_sub s t hst n i
    simp only [hπ] at h
    rw [hw] at h
    linarith
  -- the bracket integrals are measurable in `ω`
  have hG0 : ∀ q : ℝ≥0, AEStronglyMeasurable (fun ω => ∫ u in (0 : ℝ)..(q : ℝ), e u ω) P := by
    intro q
    have h := ((hY.integrable q).aestronglyMeasurable.pow 2).sub
      (hYY.integrable q).aestronglyMeasurable
    exact h.congr (Eventually.of_forall fun ω => by simp)
  have hG1 : ∀ q : ℝ≥0, AEStronglyMeasurable
      (fun ω => ∫ u in (0 : ℝ)..(q : ℝ), e u ω * k u ω) P := by
    intro q
    have h := ((hX.integrable q).aestronglyMeasurable.mul (hY.integrable q).aestronglyMeasurable).sub
      (hXY.integrable q).aestronglyMeasurable
    exact h.congr (Eventually.of_forall fun ω => by simp)
  have hG2 : ∀ q : ℝ≥0, AEStronglyMeasurable
      (fun ω => ∫ u in (0 : ℝ)..(q : ℝ), e u ω * k u ω ^ 2) P := by
    intro q
    have h := ((hX.integrable q).aestronglyMeasurable.pow 2).sub
      (hXX.integrable q).aestronglyMeasurable
    exact h.congr (Eventually.of_forall fun ω => by simp)
  -- the cells in frozen form
  have hcellF : ∀ n i ω, (((∫ u in (0 : ℝ)..(π n (i + 1) : ℝ), e u ω)
      - ∫ u in (0 : ℝ)..(π n i : ℝ), e u ω)
      - 2 * l n i ω * ((∫ u in (0 : ℝ)..(π n (i + 1) : ℝ), e u ω * k u ω)
        - ∫ u in (0 : ℝ)..(π n i : ℝ), e u ω * k u ω)
      + l n i ω ^ 2 * ((∫ u in (0 : ℝ)..(π n (i + 1) : ℝ), e u ω * k u ω ^ 2)
        - ∫ u in (0 : ℝ)..(π n i : ℝ), e u ω * k u ω ^ 2))
      = ∫ u in (π n i : ℝ)..(π n (i + 1) : ℝ), e u ω * (1 - l n i ω * k u ω) ^ 2 :=
    fun n i ω => bracket_cell_eq (he ω) (fun u => he0 u ω) (fun u => he1 u ω) (hkc ω)
      (fun u => hkC u ω) _ _ _
  have hcm : ∀ n i, AEStronglyMeasurable (fun ω =>
      ∫ u in (π n i : ℝ)..(π n (i + 1) : ℝ), e u ω * (1 - l n i ω * k u ω) ^ 2) P := by
    intro n i
    have hlm' : AEStronglyMeasurable (l n i) P := ((hlm n i).mono (𝓕.le _)).aestronglyMeasurable
    have h := (((hG0 (π n (i + 1))).sub (hG0 (π n i))).sub
      (((aestronglyMeasurable_const (b := (2 : ℝ))).mul hlm').mul
        ((hG1 (π n (i + 1))).sub (hG1 (π n i))))).add
      ((hlm'.pow 2).mul ((hG2 (π n (i + 1))).sub (hG2 (π n i))))
    exact h.congr (Eventually.of_forall fun ω => hcellF n i ω)
  have hci : ∀ n i, Integrable (fun ω =>
      ∫ u in (π n i : ℝ)..(π n (i + 1) : ℝ), e u ω * (1 - l n i ω * k u ω) ^ 2) P := by
    intro n i
    refine Integrable.of_bound (hcm n i) (Bd * (((t : ℝ) - s) / n))
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hcellb n i ω).1]
    exact (hcellb n i ω).2
  -- `E[S n²] = E[F n]`
  have hSF : ∀ n, ∫ ω, S n ω ^ 2 ∂P = ∫ ω, F n ω ∂P := by
    intro n
    rw [integral_sq_sum_cells_eq hX hY hXb hYb (hπm n) (hlm n) (hlb n) n]
    simp only [hF]
    rw [integral_finsetSum _ fun i _ => hci n i]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hcell n i]
    exact integral_congr_ae (Eventually.of_forall fun ω => hcellF n i ω)
  -- dominated convergence for `F n`
  have hFlim : Tendsto (fun n => ∫ ω, F n ω ∂P) atTop (𝓝 0) := by
    have h0 : (0 : ℝ) = ∫ _ω : Ω, (0 : ℝ) ∂P := by simp
    rw [h0]
    refine tendsto_integral_of_dominated_convergence (fun _ => Bd * ((t : ℝ) - s))
      (fun n => Finset.aestronglyMeasurable_fun_sum _ fun i _ => hcm n i) (integrable_const _)
      (fun n => Eventually.of_forall fun ω => ?_) (Eventually.of_forall fun ω => ?_)
    · rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun i _ => (hcellb n i ω).1)]
      calc F n ω ≤ ∑ i ∈ Finset.range n, Bd * (((t : ℝ) - s) / n) :=
            Finset.sum_le_sum fun i _ => (hcellb n i ω).2
        _ ≤ Bd * ((t : ℝ) - s) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            rcases Nat.eq_zero_or_pos n with hn | hn
            · subst hn; simp only [Nat.cast_zero, zero_mul]; positivity
            · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
              exact le_of_eq (by field_simp)
    · exact tendsto_sum_integral_freeze (hkc ω) hc (fun u => hkb u ω) (he ω) (fun u => he0 u ω)
        (fun u => he1 u ω) hst
  have hSlim : Tendsto (fun n => ∫ ω, (S n ω - 0) ^ 2 ∂P) atTop (𝓝 0) := by
    simp only [sub_zero]
    exact hFlim.congr fun n => (hSF n).symm
  have hlimA := LocalSets.tendsto_setIntegral_of_tendsto_integral_sq (f := fun _ => (0 : ℝ))
    (integrable_const _) (fun n => (hSL2 n).integrable one_le_two)
    (fun n => (hSL2 n).sub (memLp_const 0)) hSlim A
  simp only [integral_zero] at hlimA
  have hzero : ∫ ω in A, (Y t ω - Y s ω) ∂P = 0 := by
    refine tendsto_nhds_unique (f := fun _ : ℕ => ∫ ω in A, (Y t ω - Y s ω) ∂P)
      tendsto_const_nhds (hlimA.congr' ?_)
    filter_upwards [eventually_ne_atTop 0] with n hn
    exact (hYA n hn).symm
  rw [integral_sub (hY.integrable t).integrableOn (hY.integrable s).integrableOn] at hzero
  linarith

end WholeField

end InteractingSLE
