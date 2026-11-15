/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PhaseContTilt

/-!
# Theorem 1.2's R.7: a lattice-valued phase with Gaussian mean increments is constant

Packet PROVE-PHASECONT. Astra's follow-up 5 §3.2 (R73, `source/external/AstraIG1/ig1_followup5.txt` L456–L483): "The
adopted mean continuity and the continuous Loewner coordinates make the quotient in (3.2) continuous in positive time.
It is lattice-valued, hence constant on the positive lifetime."

The pocket mean at a far test function is `μ_q = a_q + δ_q J_q` with `a`, `J > 0` continuous in `q` and `δ_q ∈ dℤ`.
Instead of a continuous version of the mean process (which would need a filtration of the retained σ-algebras), the
constancy of `δ` is proved from Gaussian tails of the two-time increments (`PhaseContTilt`): on a grid of `[s, t]` with
`n` steps, the first change of the phase is a mean jump of size about `|d| J`, an event of probability
`O(n e^{−cn}) → 0`.

## Main results

* `gridPt` and its lemmas, `exists_first_change`, `abs_step_le_of_lattice_ne`;
* **`ae_eq_of_increment_tail`**: `δ_s = δ_t` almost surely on the later live event;
* **`exists_const_of_pairwise`**: pairwise almost sure equality at positive times gives one constant phase.

Ruling R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any result taking
them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.PhaseCont

/-! ### The uniform grid of `[s, t]` -/

section Grid

/-- The `i`-th point of the uniform grid of `[s, t]` with `n` steps. -/
def gridPt (s t : ℝ≥0) (n i : ℕ) : ℝ≥0 := Real.toNNReal ((s : ℝ) + ((t : ℝ) - s) * i / n)

theorem coe_gridPt {s t : ℝ≥0} (hst : s ≤ t) (n i : ℕ) :
    (gridPt s t n i : ℝ) = (s : ℝ) + ((t : ℝ) - s) * i / n := by
  have hts : (0 : ℝ) ≤ (t : ℝ) - s := sub_nonneg.2 (NNReal.coe_le_coe.2 hst)
  rw [gridPt, Real.coe_toNNReal]
  have : 0 ≤ ((t : ℝ) - s) * i / n := by positivity
  linarith [s.coe_nonneg]

theorem gridPt_zero {s t : ℝ≥0} (hst : s ≤ t) (n : ℕ) : gridPt s t n 0 = s := by
  apply NNReal.coe_injective
  rw [coe_gridPt hst]; simp

theorem gridPt_self {s t : ℝ≥0} (hst : s ≤ t) {n : ℕ} (hn : n ≠ 0) : gridPt s t n n = t := by
  apply NNReal.coe_injective
  rw [coe_gridPt hst]
  have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  field_simp; ring

theorem gridPt_succ_sub {s t : ℝ≥0} (hst : s ≤ t) (n i : ℕ) :
    (gridPt s t n (i + 1) : ℝ) - gridPt s t n i = ((t : ℝ) - s) / n := by
  rw [coe_gridPt hst, coe_gridPt hst]; push_cast; ring

theorem gridPt_mem {s t : ℝ≥0} (hst : s ≤ t) {n i : ℕ} (hn : n ≠ 0) (hi : i ≤ n) :
    gridPt s t n i ∈ Icc s t := by
  have hts : (0 : ℝ) ≤ (t : ℝ) - s := sub_nonneg.2 (NNReal.coe_le_coe.2 hst)
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  have hin : (i : ℝ) ≤ n := Nat.cast_le.2 hi
  constructor
  · rw [← NNReal.coe_le_coe, coe_gridPt hst]
    have : 0 ≤ ((t : ℝ) - s) * i / n := by positivity
    linarith
  · rw [← NNReal.coe_le_coe, coe_gridPt hst]
    have : ((t : ℝ) - s) * i / n ≤ (t : ℝ) - s := by
      rw [div_le_iff₀ hn']; exact mul_le_mul_of_nonneg_left hin hts
    linarith

theorem gridPt_lt_succ {s t : ℝ≥0} (hst : s < t) {n : ℕ} (hn : n ≠ 0) (i : ℕ) :
    gridPt s t n i < gridPt s t n (i + 1) := by
  rw [← NNReal.coe_lt_coe, ← sub_pos, gridPt_succ_sub hst.le]
  have : (0 : ℝ) < (t : ℝ) - s := sub_pos.2 (NNReal.coe_lt_coe.2 hst)
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  positivity

/-- A property true at `0` and false at `n` changes at some step. -/
theorem exists_first_change (p : ℕ → Prop) (h0 : p 0) : ∀ n : ℕ, ¬ p n → ∃ i < n, p i ∧ ¬ p (i + 1) := by
  intro n
  induction n with
  | zero => intro h; exact absurd h0 h
  | succ n ih =>
    intro hn
    by_cases hp : p n
    · exact ⟨n, Nat.lt_succ_self n, hp, hn⟩
    · obtain ⟨i, hi, h1, h2⟩ := ih hp
      exact ⟨i, Nat.lt_succ_of_lt hi, h1, h2⟩

end Grid

/-! ### Two distinct lattice values differ by at least the step -/

theorem abs_step_le_of_lattice_ne {d x y : ℝ} (hx : ∃ m : ℤ, x = m * d) (hy : ∃ m : ℤ, y = m * d)
    (hxy : x ≠ y) : |d| ≤ |x - y| := by
  obtain ⟨m, rfl⟩ := hx
  obtain ⟨m', rfl⟩ := hy
  have hne : m - m' ≠ 0 := by
    intro h; apply hxy; rw [sub_eq_zero.1 h]
  have h1 : (1 : ℝ) ≤ |((m - m' : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hne
  rw [show (m : ℝ) * d - m' * d = ((m - m' : ℤ) : ℝ) * d by push_cast; ring, abs_mul]
  calc |d| = 1 * |d| := (one_mul _).symm
    _ ≤ |((m - m' : ℤ) : ℝ)| * |d| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)

/-! ### A lattice-valued phase with Gaussian mean increments does not jump -/

section NoJump

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem tendsto_mul_exp_neg {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun n : ℕ => (n : ℝ) * Real.exp (-(κ * n))) atTop (𝓝 0) := by
  have h1 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
    ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hκ)
  have h2 := h1.const_mul κ⁻¹
  rw [mul_zero] at h2
  refine h2.congr fun n => ?_
  simp only [Function.comp_apply, pow_one]
  field_simp

/-- The increment bound of `htail` summed over the grid. -/
theorem tendsto_grid_bound {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun n : ℕ => ENNReal.ofReal (2 * ((n : ℝ) * Real.exp (-(κ * n))))) atTop (𝓝 0) := by
  have h := (tendsto_mul_exp_neg hκ).const_mul 2
  rw [mul_zero] at h
  simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal h

/-- **A lattice-valued phase whose conditional means have Gaussian increments does not change.** On a time interval
`[s, t]`, let the means be `μ_q = a_q + δ_q J_q` (almost surely on the live events `L_q`, decreasing in `q`) with a
lattice-valued phase `δ_q ∈ dℤ`, and `a`, `J > 0` continuous on `[s, t]` along almost every path of `L_t`. If the mean
increments have the Gaussian tails `P(L_r, |μ_r − μ_q| ≥ b) ≤ 2 exp(−b²/(2C(r − q)))`, then `δ_s = δ_t` almost surely
on `L_t`. (Partition `[s, t]` into `n` steps; at the first change the mean jumps by about `|d| J`, an event of
probability `O(n e^{−cn})`.) -/
theorem ae_eq_of_increment_tail [IsProbabilityMeasure P] {d : ℝ} (hd : d ≠ 0) {L : ℝ≥0 → Set Ω}
    {μ a J δ : ℝ≥0 → Ω → ℝ} {s t : ℝ≥0} (hst : s < t) {C : ℝ} (hC : 0 < C)
    (hL : ∀ q r : ℝ≥0, q ≤ r → L r ⊆ L q)
    (hrep : ∀ q : ℝ≥0, s ≤ q → q ≤ t → ∀ᵐ ω ∂P, ω ∈ L q → μ q ω = a q ω + δ q ω * J q ω)
    (hlat : ∀ q : ℝ≥0, s ≤ q → q ≤ t → ∀ᵐ ω ∂P, ω ∈ L q → ∃ m : ℤ, δ q ω = m * d)
    (hcont : ∀ᵐ ω ∂P, ω ∈ L t → ContinuousOn (fun q => a q ω) (Icc s t) ∧
      ContinuousOn (fun q => J q ω) (Icc s t) ∧ ∀ q ∈ Icc s t, 0 < J q ω)
    (htail : ∀ q r : ℝ≥0, s ≤ q → q < r → r ≤ t → ∀ b : ℝ, 0 < b →
      P (L r ∩ {ω | b ≤ |μ r ω - μ q ω|}) ≤
        2 * ENNReal.ofReal (Real.exp (-(b ^ 2 / (2 * (C * ((r : ℝ) - q))))))) :
    ∀ᵐ ω ∂P, ω ∈ L t → δ s ω = δ t ω := by
  classical
  have hts : (0 : ℝ) < (t : ℝ) - s := sub_pos.2 (NNReal.coe_lt_coe.2 hst)
  set g : ℕ → ℕ → ℝ≥0 := gridPt s t with hg
  set Good : Ω → Prop := fun ω => ∀ n i : ℕ, n ≠ 0 → i ≤ n → ω ∈ L (g n i) →
      μ (g n i) ω = a (g n i) ω + δ (g n i) ω * J (g n i) ω ∧ ∃ m : ℤ, δ (g n i) ω = m * d with hGood
  have hgood : ∀ᵐ ω ∂P, Good ω := by
    simp only [hGood]
    rw [ae_all_iff]; intro n; rw [ae_all_iff]; intro i
    by_cases hn : n = 0
    · exact Eventually.of_forall fun ω h => absurd hn h
    by_cases hi : i ≤ n
    · have hm := gridPt_mem hst.le hn hi
      filter_upwards [hrep _ hm.1 hm.2, hlat _ hm.1 hm.2] with ω h1 h2 _ _ hω
      exact ⟨h1 hω, h2 hω⟩
    · exact Eventually.of_forall fun ω _ h => absurd h hi
  set Cont : Ω → Prop := fun ω => ContinuousOn (fun q => a q ω) (Icc s t) ∧
      ContinuousOn (fun q => J q ω) (Icc s t) ∧ ∀ q ∈ Icc s t, 0 < J q ω with hCont
  set B : Set Ω := {ω | ω ∈ L t ∧ δ s ω ≠ δ t ω ∧ Good ω ∧ Cont ω} with hB
  suffices hB0 : P B = 0 by
    have := measure_eq_zero_iff_ae_notMem.1 hB0
    filter_upwards [this, hgood, hcont] with ω hω hgω hcω hωL
    by_contra hne
    exact hω ⟨hωL, hne, hgω, hcω hωL⟩
  -- the pieces with a bounded phase and a lower bound for `J`
  have hpiece : ∀ R k : ℕ, P {ω | ω ∈ B ∧ |δ s ω| ≤ R ∧ ∀ q ∈ Icc s t, 1 / ((k : ℝ) + 1) ≤ J q ω} = 0 := by
    intro R k
    set j : ℝ := 1 / ((k : ℝ) + 1) with hj
    have hj0 : 0 < j := by positivity
    set b : ℝ := |d| * j / 2 with hb
    have hb0 : 0 < b := by have := abs_pos.2 hd; positivity
    set E : ℕ → Set Ω := fun n => {ω | |δ s ω| ≤ R ∧ (∀ q ∈ Icc s t, j ≤ J q ω) ∧
      ∀ i < n, |a (g n (i + 1)) ω - a (g n i) ω| + R * |J (g n (i + 1)) ω - J (g n i) ω| ≤ b} with hE
    set κ : ℝ := b ^ 2 / (2 * C * ((t : ℝ) - s)) with hκ
    have hκ0 : 0 < κ := by positivity
    -- one grid: the first change of the phase is a mean jump of size at least `b`
    have hcover : ∀ n : ℕ, n ≠ 0 → B ∩ E n ⊆
        ⋃ i ∈ Finset.range n, L (g n (i + 1)) ∩ {ω | b ≤ |μ (g n (i + 1)) ω - μ (g n i) ω|} := by
      rintro n hn ω ⟨⟨hωL, hne, hgω, -⟩, hR, hJ, hosc⟩
      have hp0 : δ (g n 0) ω = δ s ω := by rw [hg, gridPt_zero hst.le]
      have hpn : ¬ δ (g n n) ω = δ s ω := by rw [hg, gridPt_self hst.le hn]; exact fun h => hne h.symm
      obtain ⟨i, hi, hpi, hpi1⟩ := exists_first_change (fun i => δ (g n i) ω = δ s ω) hp0 n hpn
      have hm1 := gridPt_mem hst.le hn (Nat.succ_le_of_lt hi)
      have hm0 := gridPt_mem hst.le hn hi.le
      have hL1 : ω ∈ L (g n (i + 1)) := hL _ _ hm1.2 hωL
      have hL0 : ω ∈ L (g n i) := hL _ _ (gridPt_lt_succ hst hn i).le hL1
      obtain ⟨hr1, hl1⟩ := hgω n (i + 1) hn (Nat.succ_le_of_lt hi) hL1
      obtain ⟨hr0, hl0⟩ := hgω n i hn hi.le hL0
      refine mem_biUnion (Finset.mem_range.2 hi) ⟨hL1, ?_⟩
      show b ≤ |μ (g n (i + 1)) ω - μ (g n i) ω|
      have hjump : |d| ≤ |δ (g n (i + 1)) ω - δ s ω| :=
        abs_step_le_of_lattice_ne hl1 (hpi ▸ hl0) hpi1
      have hJ1 : j ≤ J (g n (i + 1)) ω := hJ _ hm1
      have hosci := hosc i hi
      rw [hr1, hr0, hpi]
      have e : a (g n (i + 1)) ω + δ (g n (i + 1)) ω * J (g n (i + 1)) ω -
          (a (g n i) ω + δ s ω * J (g n i) ω) =
          (δ (g n (i + 1)) ω - δ s ω) * J (g n (i + 1)) ω +
            ((a (g n (i + 1)) ω - a (g n i) ω) + δ s ω * (J (g n (i + 1)) ω - J (g n i) ω)) := by ring
      rw [e]
      have h1 : |d| * j ≤ |(δ (g n (i + 1)) ω - δ s ω) * J (g n (i + 1)) ω| := by
        rw [abs_mul, abs_of_pos (hj0.trans_le hJ1)]
        exact mul_le_mul hjump hJ1 hj0.le (abs_nonneg _)
      have h2 : |(a (g n (i + 1)) ω - a (g n i) ω) + δ s ω * (J (g n (i + 1)) ω - J (g n i) ω)| ≤ b := by
        calc _ ≤ |a (g n (i + 1)) ω - a (g n i) ω| + |δ s ω * (J (g n (i + 1)) ω - J (g n i) ω)| :=
              abs_add_le _ _
          _ = |a (g n (i + 1)) ω - a (g n i) ω| + |δ s ω| * |J (g n (i + 1)) ω - J (g n i) ω| := by
              rw [abs_mul]
          _ ≤ |a (g n (i + 1)) ω - a (g n i) ω| + R * |J (g n (i + 1)) ω - J (g n i) ω| := by
              gcongr
          _ ≤ b := hosci
      have h3 := abs_sub_abs_le_abs_add ((δ (g n (i + 1)) ω - δ s ω) * J (g n (i + 1)) ω)
        ((a (g n (i + 1)) ω - a (g n i) ω) + δ s ω * (J (g n (i + 1)) ω - J (g n i) ω))
      linarith
    -- the probability of one grid's event
    have hbound : ∀ n : ℕ, n ≠ 0 → P (B ∩ E n) ≤ ENNReal.ofReal (2 * ((n : ℝ) * Real.exp (-(κ * n)))) := by
      intro n hn
      have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
      refine (measure_mono (hcover n hn)).trans ((measure_biUnion_finset_le _ _).trans ?_)
      have hstep : ∀ i ∈ Finset.range n, P (L (g n (i + 1)) ∩ {ω | b ≤ |μ (g n (i + 1)) ω - μ (g n i) ω|}) ≤
          2 * ENNReal.ofReal (Real.exp (-(κ * n))) := by
        intro i hi
        have hi' := Finset.mem_range.1 hi
        have h := htail (g n i) (g n (i + 1)) (gridPt_mem hst.le hn hi'.le).1 (gridPt_lt_succ hst hn i)
          (gridPt_mem hst.le hn (Nat.succ_le_of_lt hi')).2 b hb0
        rw [gridPt_succ_sub hst.le] at h
        have e : b ^ 2 / (2 * (C * (((t : ℝ) - s) / n))) = κ * n := by
          rw [hκ]; field_simp
        rwa [e] at h
      refine (Finset.sum_le_sum hstep).trans (le_of_eq ?_)
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
        ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat]
      ring
    have hlim := tendsto_grid_bound hκ0
    -- along a path of the piece, the grid events hold eventually
    have hev : ∀ ω, ω ∈ B → |δ s ω| ≤ R → (∀ q ∈ Icc s t, j ≤ J q ω) → ∀ᶠ n in atTop, ω ∈ E n := by
      rintro ω ⟨-, -, -, hac, hJc, -⟩ hR hJ
      have hε : 0 < b / ((R : ℝ) + 1) := by positivity
      obtain ⟨ηa, hηa, ha⟩ := Metric.uniformContinuousOn_iff.1
        (isCompact_Icc.uniformContinuousOn_of_continuous hac) _ hε
      obtain ⟨ηJ, hηJ, hJu⟩ := Metric.uniformContinuousOn_iff.1
        (isCompact_Icc.uniformContinuousOn_of_continuous hJc) _ hε
      have hmesh : Tendsto (fun n : ℕ => ((t : ℝ) - s) / n) atTop (𝓝 0) :=
        tendsto_const_div_atTop_nhds_zero_nat _
      filter_upwards [hmesh.eventually (gt_mem_nhds (lt_min hηa hηJ)), eventually_ne_atTop 0] with n hn hn0
      refine ⟨hR, hJ, fun i hi => ?_⟩
      have hm1 := gridPt_mem hst.le hn0 (Nat.succ_le_of_lt hi)
      have hm0 := gridPt_mem hst.le hn0 hi.le
      have hdist : dist (g n (i + 1)) (g n i) < min ηa ηJ := by
        rw [NNReal.dist_eq, gridPt_succ_sub hst.le, abs_of_nonneg (by positivity)]
        exact hn
      have h1 := ha _ hm1 _ hm0 (hdist.trans_le (min_le_left _ _))
      have h2 := hJu _ hm1 _ hm0 (hdist.trans_le (min_le_right _ _))
      rw [Real.dist_eq] at h1 h2
      have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg R
      calc |a (g n (i + 1)) ω - a (g n i) ω| + R * |J (g n (i + 1)) ω - J (g n i) ω|
          ≤ b / ((R : ℝ) + 1) + R * (b / ((R : ℝ) + 1)) := by gcongr
        _ = b := by field_simp; ring
    -- conclude for the piece
    have hsub : {ω | ω ∈ B ∧ |δ s ω| ≤ R ∧ ∀ q ∈ Icc s t, j ≤ J q ω} ⊆
        ⋃ N : ℕ, ⋂ m : ℕ, B ∩ E (N + m + 1) := by
      rintro ω ⟨hωB, hR, hJ⟩
      obtain ⟨N, hN⟩ := eventually_atTop.1 (hev ω hωB hR hJ)
      exact mem_iUnion.2 ⟨N, mem_iInter.2 fun m => ⟨hωB, hN _ (by omega)⟩⟩
    refine measure_mono_null hsub (measure_iUnion_null fun N => ?_)
    refine le_antisymm (ge_of_tendsto ((tendsto_add_atTop_iff_nat (N + 1)).2 hlim)
      (Eventually.of_forall fun m => ?_)) (zero_le)
    refine (measure_mono (iInter_subset _ m)).trans ?_
    have := hbound (N + m + 1) (by omega)
    simpa only [show N + m + 1 = m + (N + 1) by omega] using this
  -- every path of `B` lies in a piece
  have hcov : B ⊆ ⋃ R : ℕ, ⋃ k : ℕ,
      {ω | ω ∈ B ∧ |δ s ω| ≤ R ∧ ∀ q ∈ Icc s t, 1 / ((k : ℝ) + 1) ≤ J q ω} := by
    intro ω hωB
    obtain ⟨-, -, -, -, hJc, hJpos⟩ := id hωB
    obtain ⟨q₀, hq₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hst.le) hJc
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (hJpos q₀ hq₀)
    refine mem_iUnion.2 ⟨⌈|δ s ω|⌉₊, mem_iUnion.2 ⟨k, hωB, Nat.le_ceil _, fun q hq => ?_⟩⟩
    exact hk.le.trans (hmin hq)
  exact measure_mono_null hcov (measure_iUnion_null fun R => measure_iUnion_null fun k => hpiece R k)

/-- **Pairwise almost sure equality at positive times gives one constant**: if `δ_s = δ_t` almost surely on
`A ∩ {t < T}` for all `0 < s < t`, and `T > 0` on `A`, then some `c` has `δ_q = c` almost surely on `A ∩ {q < T}` at
every `q > 0` (`c` is the value at the first time `1/(k+1) < T`). -/
theorem exists_const_of_pairwise {δ : ℝ≥0 → Ω → ℝ} {A : Set Ω} {T : Ω → ℝ≥0∞} (hT : ∀ ω ∈ A, 0 < T ω)
    (hpair : ∀ s t : ℝ≥0, 0 < s → s < t → ∀ᵐ ω ∂P, ω ∈ A → (t : ℝ≥0∞) < T ω → δ s ω = δ t ω) :
    ∃ c : Ω → ℝ, ∀ q : ℝ≥0, 0 < q → ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < T ω → δ q ω = c ω := by
  classical
  set r : ℕ → ℝ≥0 := fun k => (1 / ((k : ℝ) + 1)).toNNReal with hr
  have hr0 : ∀ k, 0 < r k := fun k => Real.toNNReal_pos.2 (by positivity)
  have hex : ∀ ω ∈ A, ∃ k, (r k : ℝ≥0∞) < T ω := by
    intro ω hω
    obtain ⟨x, hx0, hx⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 (hT ω hω)
    have hx0' : (0 : ℝ) < x := by exact_mod_cast hx0
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hx0'
    refine ⟨k, lt_trans (ENNReal.coe_lt_coe.2 ?_) hx⟩
    rw [hr]
    exact (Real.toNNReal_lt_iff_lt_coe (by positivity)).2 hk
  refine ⟨fun ω => if h : ∃ k, (r k : ℝ≥0∞) < T ω then δ (r (Nat.find h)) ω else 0, fun q hq => ?_⟩
  have hall : ∀ᵐ ω ∂P, ∀ k : ℕ, ω ∈ A → (q : ℝ≥0∞) < T ω → (r k : ℝ≥0∞) < T ω → δ q ω = δ (r k) ω := by
    rw [ae_all_iff]; intro k
    rcases lt_trichotomy q (r k) with h | h | h
    · filter_upwards [hpair q (r k) hq h] with ω hω hωA _ hk using hω hωA hk
    · exact Eventually.of_forall fun ω _ _ _ => by rw [h]
    · filter_upwards [hpair (r k) q (hr0 k) h] with ω hω hωA hq' _ using (hω hωA hq').symm
  filter_upwards [hall] with ω hω hωA hqT
  have h : ∃ k, (r k : ℝ≥0∞) < T ω := hex ω hωA
  simp only [h, ↓reduceDIte]
  exact hω (Nat.find h) hωA hqT (Nat.find_spec h)

end NoJump

end InteractingSLE.Sec7.PhaseCont
