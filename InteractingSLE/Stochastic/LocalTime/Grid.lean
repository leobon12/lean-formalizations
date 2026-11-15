/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import MathFin.Probability.Brownian.UnifPart
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.Instances.NNReal.Lemmas

/-!
# Uniform partitions stopped at a lifetime (deterministic layer)

Packet PROVE-TANAKA. Pathwise ingredients of `InteractingSLE.Stochastic.LocalTime.ItoExpectation`.
A path is followed on the uniform partition `t_k = unifPartIcc s t n k` of `[s, t]` (`k ≤ n`) as
long as an antitone "alive" predicate holds at the right end of a cell.

* `firstFail p n`: for an antitone predicate `p` on cells, the number of cells `k < n` with `p k`;
  `sum_ite_eq_sum_firstFail` rewrites indicator sums as sums over `k < firstFail p n`.
* `lifetimeOf A s t`: the supremum of the times `u ∈ [s, t]` at which an antitone event `A` holds
  (or `s`).
* `GridApprox s t ρ m`: `t_{m n} ≤ ρ ≤ t_{m n} + (t - s)/n`; `gridApprox_firstFail` produces it.
* Under `GridApprox`, for paths continuous on `[s, ρ]`: `tendsto_comp_grid` (endpoint values),
  `eventually_abs_sub_le` (uniformly small increments), `tendsto_riemann_sum` (Riemann sums),
  `tendsto_drift_sum` (sums against the increments of `∫ b`), `tendsto_singular_sum` (sums against
  a monotone function that moves only where the integrand takes a fixed value `G₀`).
-/

noncomputable section

open Set Filter Topology MeasureTheory MathFin
open scoped NNReal

namespace InteractingSLE.LocalTime

/-! ### Counting alive cells -/

section Count

open Classical

/-- The first `k ≤ n` at which the predicate `p` fails, or `n`. -/
def firstFail (p : ℕ → Prop) (n : ℕ) : ℕ :=
  Nat.find (p := fun k => n ≤ k ∨ ¬ p k) ⟨n, Or.inl le_rfl⟩

lemma firstFail_le (p : ℕ → Prop) (n : ℕ) : firstFail p n ≤ n :=
  Nat.find_min' _ (Or.inl le_rfl)

lemma of_lt_firstFail {p : ℕ → Prop} {n k : ℕ} (hk : k < firstFail p n) : p k := by
  have := Nat.find_min (p := fun k => n ≤ k ∨ ¬ p k) ⟨n, Or.inl le_rfl⟩ hk
  simp only [not_or, not_not] at this
  exact this.2

lemma not_of_firstFail_lt {p : ℕ → Prop} {n : ℕ} (h : firstFail p n < n) :
    ¬ p (firstFail p n) := by
  have := Nat.find_spec (p := fun k => n ≤ k ∨ ¬ p k) ⟨n, Or.inl le_rfl⟩
  rcases this with h' | h'
  · exact absurd h (not_lt.2 h')
  · exact h'

/-- For an antitone predicate, an indicator sum over `k < n` is a plain sum over
`k < firstFail p n`. -/
lemma sum_ite_eq_sum_firstFail {p : ℕ → Prop} (hp : ∀ k l, k ≤ l → p l → p k) (n : ℕ)
    (y : ℕ → ℝ) :
    ∑ k ∈ Finset.range n, (if p k then y k else 0) = ∑ k ∈ Finset.range (firstFail p n), y k := by
  have hle := firstFail_le p n
  rw [← Finset.sum_range_add_sum_Ico _ hle]
  have h2 : ∑ k ∈ Finset.Ico (firstFail p n) n, (if p k then y k else 0) = 0 := by
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [Finset.mem_Ico] at hk
    have hlt : firstFail p n < n := lt_of_le_of_lt hk.1 hk.2
    have : ¬ p k := fun hpk => not_of_firstFail_lt hlt (hp _ _ hk.1 hpk)
    simp [this]
  rw [h2, add_zero]
  refine Finset.sum_congr rfl fun k hk => ?_
  have : p k := of_lt_firstFail (Finset.mem_range.1 hk)
  simp [this]

end Count

/-! ### The lifetime of an antitone event -/

/-- The supremum of the times `u ≤ t` at which `A` holds, together with `s`. -/
def lifetimeOf (A : ℝ≥0 → Prop) (s t : ℝ≥0) : ℝ≥0 := sSup (insert s {u | u ≤ t ∧ A u})

lemma bddAbove_lifetime_set (A : ℝ≥0 → Prop) (s t : ℝ≥0) :
    BddAbove (insert s {u | u ≤ t ∧ A u}) :=
  ⟨max s t, by
    rintro u (rfl | hu)
    · exact le_max_left _ _
    · exact hu.1.trans (le_max_right _ _)⟩

lemma le_lifetimeOf (A : ℝ≥0 → Prop) (s t : ℝ≥0) : s ≤ lifetimeOf A s t :=
  le_csSup (bddAbove_lifetime_set A s t) (mem_insert _ _)

lemma lifetimeOf_le {A : ℝ≥0 → Prop} {s t : ℝ≥0} (hst : s ≤ t) : lifetimeOf A s t ≤ t :=
  csSup_le (insert_nonempty _ _) (by
    rintro u (rfl | hu)
    · exact hst
    · exact hu.1)

lemma le_lifetimeOf_of {A : ℝ≥0 → Prop} {s t u : ℝ≥0} (hu : u ≤ t) (hA : A u) :
    u ≤ lifetimeOf A s t :=
  le_csSup (bddAbove_lifetime_set A s t) (mem_insert_of_mem _ ⟨hu, hA⟩)

lemma of_lt_lifetimeOf {A : ℝ≥0 → Prop} (hA : ∀ u v, u ≤ v → A v → A u) {s t u : ℝ≥0}
    (hsu : s ≤ u) (hu : u < lifetimeOf A s t) : A u := by
  obtain ⟨v, hv, huv⟩ := exists_lt_of_lt_csSup (insert_nonempty _ _) hu
  rcases hv with rfl | hv
  · exact absurd hsu (not_le.2 huv)
  · exact hA _ _ huv.le hv.2

/-! ### Grid approximation of the lifetime -/

/-- `t_{m n}` approximates `ρ` from below within the mesh `(t - s)/n`, for every `n ≠ 0`. -/
def GridApprox (s t ρ : ℝ≥0) (m : ℕ → ℕ) : Prop :=
  ∀ n, n ≠ 0 → m n ≤ n ∧ unifPartIcc s t n (m n) ≤ ρ ∧
    (ρ : ℝ) ≤ unifPartIcc s t n (m n) + ((t : ℝ) - s) / n

lemma unifPartIcc_le {s t : ℝ≥0} (hst : s ≤ t) {n k : ℕ} (hk : k ≤ n) :
    unifPartIcc s t n k ≤ t := by
  unfold unifPartIcc
  calc s + unifPart (t - s) n k ≤ s + (t - s) := add_le_add le_rfl (unifPart_le_T hk)
    _ = t := add_tsub_cancel_of_le hst

lemma le_unifPartIcc (s t : ℝ≥0) (n k : ℕ) : s ≤ unifPartIcc s t n k := le_self_add

lemma coe_unifPartIcc_succ {s t : ℝ≥0} (hst : s ≤ t) (n k : ℕ) :
    (unifPartIcc s t n (k + 1) : ℝ) = unifPartIcc s t n k + ((t : ℝ) - s) / n := by
  linarith [unifPartIcc_succ_sub hst n k]

/-- The alive cells of the `n`-th partition, for an antitone event `A` with lifetime `ρ`, give a
`GridApprox` of `ρ`. -/
lemma gridApprox_firstFail {A : ℝ≥0 → Prop} (hA : ∀ u v, u ≤ v → A v → A u) {s t : ℝ≥0}
    (hst : s ≤ t) :
    GridApprox s t (lifetimeOf A s t) fun n => firstFail (fun k => A (unifPartIcc s t n (k + 1))) n := by
  intro n hn
  dsimp only
  set p : ℕ → Prop := fun k => A (unifPartIcc s t n (k + 1))
  set m := firstFail p n
  have hmn : m ≤ n := firstFail_le p n
  refine ⟨hmn, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos m with h0 | hpos
    · rw [h0, unifPartIcc_zero]; exact le_lifetimeOf A s t
    · obtain ⟨j, hj⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
      have hpj : p j := of_lt_firstFail (n := n) (by omega)
      rw [hj]
      exact le_lifetimeOf_of (unifPartIcc_le hst (by omega)) hpj
  · rcases lt_or_eq_of_le hmn with hlt | heq
    · have hnot : ¬ p m := not_of_firstFail_lt hlt
      have : ¬ (unifPartIcc s t n (m + 1) < lifetimeOf A s t) := fun h =>
        hnot (of_lt_lifetimeOf hA (le_unifPartIcc s t n _) h)
      rw [not_lt] at this
      rw [← coe_unifPartIcc_succ hst]
      exact_mod_cast this
    · have hρ : (lifetimeOf A s t : ℝ) ≤ t := by exact_mod_cast lifetimeOf_le hst
      have : (unifPartIcc s t n m : ℝ) = t := by rw [heq, unifPartIcc_self hst hn]
      have hnn : (0 : ℝ) ≤ ((t : ℝ) - s) / n := div_nonneg (by
        have : (s : ℝ) ≤ t := by exact_mod_cast hst
        linarith) (Nat.cast_nonneg n)
      linarith

/-! ### Limits along a grid approximation -/

lemma tendsto_of_forall_eventually_abs_le {a : ℕ → ℝ} {L : ℝ}
    (h : ∀ η > 0, ∀ᶠ n in atTop, |a n - L| ≤ η) : Tendsto a atTop (𝓝 L) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [h (ε / 2) (half_pos hε)] with n hn
  rw [Real.dist_eq]; linarith

lemma tendsto_mesh (s t : ℝ≥0) : Tendsto (fun n : ℕ => ((t : ℝ) - s) / n) atTop (𝓝 0) :=
  tendsto_const_div_atTop_nhds_zero_nat _

lemma mesh_nonneg {s t : ℝ≥0} (hst : s ≤ t) (n : ℕ) : 0 ≤ ((t : ℝ) - s) / n :=
  div_nonneg (sub_nonneg.2 (by exact_mod_cast hst)) (Nat.cast_nonneg n)

section GridLimits

variable {s t ρ : ℝ≥0} {m : ℕ → ℕ}

lemma GridApprox.le_grid_succ (hm : GridApprox s t ρ m) {n k : ℕ} (hn : n ≠ 0)
    (hk : k < m n) : unifPartIcc s t n (k + 1) ≤ ρ :=
  (unifPartIcc_mono s t n (Nat.succ_le_of_lt hk)).trans (hm n hn).2.1

lemma GridApprox.mem_Icc (hm : GridApprox s t ρ m) {n k : ℕ} (hn : n ≠ 0) (hk : k ≤ m n) :
    unifPartIcc s t n k ∈ Icc s ρ :=
  ⟨le_unifPartIcc s t n k, (unifPartIcc_mono s t n hk).trans (hm n hn).2.1⟩

lemma GridApprox.tendsto_grid (hm : GridApprox s t ρ m) :
    Tendsto (fun n => unifPartIcc s t n (m n)) atTop (𝓝[Icc s ρ] ρ) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · rw [← NNReal.tendsto_coe]
    refine tendsto_of_forall_eventually_abs_le fun η hη => ?_
    filter_upwards [(tendsto_mesh s t).eventually (gt_mem_nhds hη), eventually_ne_atTop 0]
      with n hn hn0
    have h1 := (hm n hn0).2.1
    have h2 := (hm n hn0).2.2
    have h1' : (unifPartIcc s t n (m n) : ℝ) ≤ ρ := by exact_mod_cast h1
    rw [abs_le]; constructor <;> linarith
  · filter_upwards [eventually_ne_atTop 0] with n hn0
    exact hm.mem_Icc hn0 le_rfl

lemma GridApprox.tendsto_comp (hm : GridApprox s t ρ m) {G : ℝ≥0 → ℝ}
    (hG : ContinuousOn G (Icc s ρ)) (hsρ : s ≤ ρ) :
    Tendsto (fun n => G (unifPartIcc s t n (m n))) atTop (𝓝 (G ρ)) :=
  (hG ρ ⟨hsρ, le_rfl⟩).tendsto.comp hm.tendsto_grid

lemma GridApprox.s_le (hm : GridApprox s t ρ m) : s ≤ ρ :=
  (hm.mem_Icc one_ne_zero (Nat.zero_le _)).1.trans (hm.mem_Icc one_ne_zero (Nat.zero_le _)).2

/-- Uniform continuity on `[s, ρ]`: eventually every increment over an alive cell is small. -/
lemma GridApprox.eventually_abs_sub_le (hm : GridApprox s t ρ m) (hst : s ≤ t) {G : ℝ≥0 → ℝ}
    (hG : ContinuousOn G (Icc s ρ)) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n in atTop, n ≠ 0 ∧ ∀ k < m n, ∀ u ∈ Icc (unifPartIcc s t n k) (unifPartIcc s t n (k + 1)),
      |G u - G (unifPartIcc s t n k)| ≤ η := by
  have hu := isCompact_Icc.uniformContinuousOn_of_continuous hG
  obtain ⟨δ, hδ, hδG⟩ := Metric.uniformContinuousOn_iff_le.1 hu η hη
  filter_upwards [(tendsto_mesh s t).eventually (ge_mem_nhds hδ), eventually_ne_atTop 0]
    with n hn hn0
  refine ⟨hn0, fun k hk u hu => ?_⟩
  have hk1 := hm.le_grid_succ hn0 hk
  have huρ : u ∈ Icc s ρ := ⟨(le_unifPartIcc s t n k).trans hu.1, hu.2.trans hk1⟩
  have hkρ : unifPartIcc s t n k ∈ Icc s ρ := hm.mem_Icc hn0 hk.le
  have hd : dist u (unifPartIcc s t n k) ≤ δ := by
    rw [NNReal.dist_eq]
    have h1 : (unifPartIcc s t n k : ℝ) ≤ u := by exact_mod_cast hu.1
    have h2 : (u : ℝ) ≤ unifPartIcc s t n (k + 1) := by exact_mod_cast hu.2
    rw [abs_of_nonneg (by linarith)]
    linarith [coe_unifPartIcc_succ hst n k]
  have := hδG u huρ _ hkρ hd
  rwa [Real.dist_eq] at this

lemma continuousOn_comp_toNNReal {G : ℝ≥0 → ℝ} {a b : ℝ≥0} (hG : ContinuousOn G (Icc a b)) :
    ContinuousOn (fun r : ℝ => G r.toNNReal) (Icc (a : ℝ) b) := by
  refine hG.comp continuous_real_toNNReal.continuousOn fun r hr => ⟨?_, ?_⟩
  · exact Real.le_toNNReal_iff_coe_le (a.2.trans hr.1) |>.2 hr.1
  · exact (Real.toNNReal_le_iff_le_coe).2 hr.2

lemma toNNReal_mem_Icc {a b : ℝ≥0} {r : ℝ} (hr : r ∈ Ioc (a : ℝ) b) :
    r.toNNReal ∈ Icc a b :=
  ⟨Real.le_toNNReal_iff_coe_le (a.2.trans hr.1.le) |>.2 hr.1.le,
    (Real.toNNReal_le_iff_le_coe).2 hr.2⟩

lemma GridApprox.coe_mem_Icc (hm : GridApprox s t ρ m) {n k : ℕ} (hn : n ≠ 0) (hk : k ≤ m n) :
    (unifPartIcc s t n k : ℝ) ∈ Icc (s : ℝ) ρ := by
  have := hm.mem_Icc hn hk
  exact ⟨by exact_mod_cast this.1, by exact_mod_cast this.2⟩

/-- Integral over `[s, t_m]` as the sum of the integrals over the alive cells. -/
lemma GridApprox.sum_integral_cells (hm : GridApprox s t ρ m) {F : ℝ → ℝ} {n : ℕ} (hn : n ≠ 0)
    (hF : ∀ u v, u ∈ Icc (s : ℝ) ρ → v ∈ Icc (s : ℝ) ρ → IntervalIntegrable F volume u v) :
    ∑ k ∈ Finset.range (m n), ∫ r in (unifPartIcc s t n k : ℝ)..(unifPartIcc s t n (k + 1)), F r
      = ∫ r in (s : ℝ)..(unifPartIcc s t n (m n)), F r := by
  rw [intervalIntegral.sum_integral_adjacent_intervals (a := fun k => (unifPartIcc s t n k : ℝ))
    fun k hk => hF _ _ (hm.coe_mem_Icc hn hk.le) (hm.coe_mem_Icc hn hk)]
  simp [unifPartIcc_zero]

/-- **Riemann sums** over the alive cells converge to `∫_s^ρ G`. -/
lemma GridApprox.tendsto_riemann (hm : GridApprox s t ρ m) (hst : s ≤ t) {G : ℝ≥0 → ℝ}
    (hG : ContinuousOn G (Icc s ρ)) :
    Tendsto (fun n => ∑ k ∈ Finset.range (m n), G (unifPartIcc s t n k) * (((t : ℝ) - s) / n))
      atTop (𝓝 (∫ r in (s : ℝ)..ρ, G r.toNNReal)) := by
  set F : ℝ → ℝ := fun r => G r.toNNReal
  have hF : ContinuousOn F (Icc (s : ℝ) ρ) := continuousOn_comp_toNNReal hG
  have hFi : ∀ u v, u ∈ Icc (s : ℝ) ρ → v ∈ Icc (s : ℝ) ρ → IntervalIntegrable F volume u v :=
    fun u v hu hv => (hF.intervalIntegrable_of_Icc (by exact_mod_cast hm.s_le)).mono_set
      (uIcc_subset_uIcc (by rwa [uIcc_of_le (by exact_mod_cast hm.s_le)])
        (by rwa [uIcc_of_le (by exact_mod_cast hm.s_le)]))
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hG
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM s ⟨le_rfl, hm.s_le⟩)
  have hts : (0 : ℝ) ≤ (t : ℝ) - s := sub_nonneg.2 (by exact_mod_cast hst)
  refine tendsto_of_forall_eventually_abs_le fun η hη => ?_
  have hη' : 0 < η / (2 * ((t : ℝ) - s + 1)) := by positivity
  filter_upwards [hm.eventually_abs_sub_le hst hG hη',
    (tendsto_mesh s t).eventually (ge_mem_nhds (show 0 < η / (2 * (M + 1)) by positivity))]
    with n ⟨hn0, hosc⟩ hmesh
  set h := ((t : ℝ) - s) / n
  have hh0 : 0 ≤ h := mesh_nonneg hst n
  have hcell : ∀ k < m n, |G (unifPartIcc s t n k) * h -
      ∫ r in (unifPartIcc s t n k : ℝ)..(unifPartIcc s t n (k + 1)), F r|
        ≤ η / (2 * ((t : ℝ) - s + 1)) * h := by
    intro k hk
    have hint := hFi _ _ (hm.coe_mem_Icc hn0 hk.le) (hm.coe_mem_Icc hn0 hk)
    have hsucc := coe_unifPartIcc_succ hst n k
    have : G (unifPartIcc s t n k) * h -
        ∫ r in (unifPartIcc s t n k : ℝ)..(unifPartIcc s t n (k + 1)), F r =
        ∫ r in (unifPartIcc s t n k : ℝ)..(unifPartIcc s t n (k + 1)),
          (G (unifPartIcc s t n k) - F r) := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const hint,
        intervalIntegral.integral_const, smul_eq_mul, hsucc]
      ring
    rw [this]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (unifPartIcc s t n k : ℝ)) (b := (unifPartIcc s t n (k + 1) : ℝ))
      (C := η / (2 * ((t : ℝ) - s + 1))) (f := fun r => G (unifPartIcc s t n k) - F r)
      (fun r hr => by
        rw [uIoc_of_le (by linarith)] at hr
        rw [Real.norm_eq_abs, abs_sub_comm]
        exact hosc k hk _ (toNNReal_mem_Icc hr))
    have hlen : |(unifPartIcc s t n (k + 1) : ℝ) - unifPartIcc s t n k| = h := by
      rw [unifPartIcc_succ_sub hst, abs_of_nonneg hh0]
    rw [Real.norm_eq_abs, hlen] at hb
    exact hb
  have hsplit : ∫ r in (s : ℝ)..ρ, F r = (∑ k ∈ Finset.range (m n),
      ∫ r in (unifPartIcc s t n k : ℝ)..(unifPartIcc s t n (k + 1)), F r) +
      ∫ r in (unifPartIcc s t n (m n) : ℝ)..ρ, F r := by
    rw [hm.sum_integral_cells hn0 hFi, intervalIntegral.integral_add_adjacent_intervals
      (hFi _ _ ⟨le_rfl, by exact_mod_cast hm.s_le⟩ (hm.coe_mem_Icc hn0 le_rfl))
      (hFi _ _ (hm.coe_mem_Icc hn0 le_rfl) ⟨by exact_mod_cast hm.s_le, le_rfl⟩)]
  have htail : |∫ r in (unifPartIcc s t n (m n) : ℝ)..ρ, F r| ≤ M * h := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (unifPartIcc s t n (m n) : ℝ)) (b := (ρ : ℝ)) (C := M) (f := F)
      (fun r hr => by
        have hle : (unifPartIcc s t n (m n) : ℝ) ≤ ρ := by exact_mod_cast (hm n hn0).2.1
        rw [uIoc_of_le hle] at hr
        have hmem := toNNReal_mem_Icc hr
        exact hM _ ⟨(le_unifPartIcc s t n _).trans hmem.1, hmem.2⟩)
    have hle : (unifPartIcc s t n (m n) : ℝ) ≤ ρ := by exact_mod_cast (hm n hn0).2.1
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hle)] at hb
    calc _ ≤ M * ((ρ : ℝ) - unifPartIcc s t n (m n)) := hb
      _ ≤ M * h := mul_le_mul_of_nonneg_left (by linarith [(hm n hn0).2.2]) hM0
  have hsum : |∑ k ∈ Finset.range (m n), (G (unifPartIcc s t n k) * h -
      ∫ r in (unifPartIcc s t n k : ℝ)..(unifPartIcc s t n (k + 1)), F r)|
        ≤ η / 2 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun k hk => hcell k (Finset.mem_range.1 hk)).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hmn : (m n : ℝ) ≤ n := by exact_mod_cast (hm n hn0).1
    have hnh : (n : ℝ) * h = (t : ℝ) - s := by
      simp only [h]; field_simp
    calc (m n : ℝ) * (η / (2 * ((t : ℝ) - s + 1)) * h)
        ≤ n * (η / (2 * ((t : ℝ) - s + 1)) * h) := by gcongr
      _ = η / 2 * (((t : ℝ) - s) / ((t : ℝ) - s + 1)) := by rw [← hnh]; field_simp
      _ ≤ η / 2 * 1 := by
          gcongr; rw [div_le_one (by linarith)]; linarith
      _ = η / 2 := mul_one _
  have hMh : M * h ≤ η / 2 := by
    calc M * h ≤ (M + 1) * (η / (2 * (M + 1))) := by gcongr; linarith
      _ = η / 2 := by field_simp
  rw [hsplit]
  have : ∑ k ∈ Finset.range (m n), G (unifPartIcc s t n k) * h -
      ((∑ k ∈ Finset.range (m n),
        ∫ r in (unifPartIcc s t n k : ℝ)..(unifPartIcc s t n (k + 1)), F r) +
        ∫ r in (unifPartIcc s t n (m n) : ℝ)..ρ, F r) =
      (∑ k ∈ Finset.range (m n), (G (unifPartIcc s t n k) * h -
        ∫ r in (unifPartIcc s t n k : ℝ)..(unifPartIcc s t n (k + 1)), F r)) -
        ∫ r in (unifPartIcc s t n (m n) : ℝ)..ρ, F r := by
    rw [Finset.sum_sub_distrib]; ring
  rw [this]
  calc _ ≤ |∑ k ∈ Finset.range (m n), (G (unifPartIcc s t n k) * h -
        ∫ r in (unifPartIcc s t n k : ℝ)..(unifPartIcc s t n (k + 1)), F r)| +
        |∫ r in (unifPartIcc s t n (m n) : ℝ)..ρ, F r| := abs_sub _ _
    _ ≤ η / 2 + η / 2 := add_le_add hsum (htail.trans hMh)
    _ = η := by ring

lemma intervalIntegrable_of_sub {f : ℝ → ℝ} {a b u v : ℝ} (hab : a ≤ b)
    (hf : IntervalIntegrable f volume a b) (hu : u ∈ Icc a b) (hv : v ∈ Icc a b) :
    IntervalIntegrable f volume u v :=
  hf.mono_set (uIcc_subset_uIcc (by rwa [uIcc_of_le hab]) (by rwa [uIcc_of_le hab]))

/-- **Drift sums**: `∑ G(t_k) ∫_{t_k}^{t_{k+1}} b → ∫_s^ρ G b`. -/
lemma GridApprox.tendsto_drift (hm : GridApprox s t ρ m) (hst : s ≤ t) {G : ℝ≥0 → ℝ}
    (hG : ContinuousOn G (Icc s ρ)) {b : ℝ → ℝ} (hb : IntervalIntegrable b volume s ρ) :
    Tendsto (fun n => ∑ k ∈ Finset.range (m n), G (unifPartIcc s t n k) *
        ∫ r in (unifPartIcc s t n k : ℝ)..(unifPartIcc s t n (k + 1)), b r)
      atTop (𝓝 (∫ r in (s : ℝ)..ρ, G r.toNNReal * b r)) := by
  set F : ℝ → ℝ := fun r => G r.toNNReal
  have hsρ : (s : ℝ) ≤ ρ := by exact_mod_cast hm.s_le
  have hF : ContinuousOn F (Icc (s : ℝ) ρ) := continuousOn_comp_toNNReal hG
  have hbi : ∀ u v, u ∈ Icc (s : ℝ) ρ → v ∈ Icc (s : ℝ) ρ → IntervalIntegrable b volume u v :=
    fun u v hu hv => intervalIntegrable_of_sub hsρ hb hu hv
  have hFb : IntervalIntegrable (fun r => F r * b r) volume s ρ :=
    hb.continuousOn_mul (by rwa [uIcc_of_le hsρ])
  have hFbi : ∀ u v, u ∈ Icc (s : ℝ) ρ → v ∈ Icc (s : ℝ) ρ →
      IntervalIntegrable (fun r => F r * b r) volume u v :=
    fun u v hu hv => intervalIntegrable_of_sub hsρ hFb hu hv
  have hab : ∀ u v, u ∈ Icc (s : ℝ) ρ → v ∈ Icc (s : ℝ) ρ →
      IntervalIntegrable (fun r => |b r|) volume u v :=
    fun u v hu hv => intervalIntegrable_of_sub hsρ hb.abs hu hv
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hG
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM s ⟨le_rfl, hm.s_le⟩)
  set I := ∫ r in (s : ℝ)..ρ, |b r|
  have hI0 : 0 ≤ I := intervalIntegral.integral_nonneg hsρ fun _ _ => abs_nonneg _
  -- the primitive of `|b|` along the grid
  set P : ℝ≥0 → ℝ := fun u => ∫ r in (s : ℝ)..u, |b r|
  have hP : ContinuousOn P (Icc s ρ) := by
    have h1 := intervalIntegral.continuousOn_primitive_interval (μ := volume)
      (f := fun r => |b r|) (a := (s : ℝ)) (b := (ρ : ℝ)) (by
        rw [uIcc_of_le hsρ]; exact (intervalIntegrable_iff_integrableOn_Icc_of_le hsρ).1 hb.abs)
    rw [uIcc_of_le hsρ] at h1
    exact h1.comp NNReal.continuous_coe.continuousOn fun u hu =>
      ⟨by exact_mod_cast hu.1, by exact_mod_cast hu.2⟩
  have hPt := hm.tendsto_comp hP hm.s_le
  refine tendsto_of_forall_eventually_abs_le fun η hη => ?_
  have hη' : 0 < η / (2 * (I + 1)) := by positivity
  filter_upwards [hm.eventually_abs_sub_le hst hG hη',
    (Metric.tendsto_nhds.1 hPt) (η / (2 * (M + 1))) (by positivity)]
    with n ⟨hn0, hosc⟩ hPn
  rw [Real.dist_eq] at hPn
  set tm : ℝ := (unifPartIcc s t n (m n) : ℝ)
  have htm : tm ∈ Icc (s : ℝ) ρ := hm.coe_mem_Icc hn0 le_rfl
  have hcell : ∀ k < m n, |G (unifPartIcc s t n k) *
      (∫ r in (unifPartIcc s t n k : ℝ)..(unifPartIcc s t n (k + 1)), b r) -
      ∫ r in (unifPartIcc s t n k : ℝ)..(unifPartIcc s t n (k + 1)), F r * b r|
        ≤ η / (2 * (I + 1)) * ∫ r in (unifPartIcc s t n k : ℝ)..(unifPartIcc s t n (k + 1)),
          |b r| := by
    intro k hk
    have hk0 := hm.coe_mem_Icc hn0 hk.le
    have hk1 := hm.coe_mem_Icc hn0 hk
    have hle : (unifPartIcc s t n k : ℝ) ≤ unifPartIcc s t n (k + 1) := by
      exact_mod_cast unifPartIcc_mono s t n (Nat.le_succ k)
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub
      ((hbi _ _ hk0 hk1).const_mul _) (hFbi _ _ hk0 hk1), ← intervalIntegral.integral_const_mul]
    have hb' := intervalIntegral.norm_integral_le_of_norm_le hle
      (f := fun r => G (unifPartIcc s t n k) * b r - F r * b r)
      (g := fun r => η / (2 * (I + 1)) * |b r|)
      (Eventually.of_forall fun r hr => by
        rw [Real.norm_eq_abs, ← sub_mul, abs_mul, abs_sub_comm]
        exact mul_le_mul_of_nonneg_right (hosc k hk _ (toNNReal_mem_Icc hr)) (abs_nonneg _))
      ((hab _ _ hk0 hk1).const_mul _)
    simpa [Real.norm_eq_abs] using hb'
  have hsplit : ∫ r in (s : ℝ)..ρ, F r * b r = (∑ k ∈ Finset.range (m n),
      ∫ r in (unifPartIcc s t n k : ℝ)..(unifPartIcc s t n (k + 1)), F r * b r) +
      ∫ r in tm..ρ, F r * b r := by
    rw [hm.sum_integral_cells hn0 hFbi, intervalIntegral.integral_add_adjacent_intervals
      (hFbi _ _ ⟨le_rfl, hsρ⟩ htm) (hFbi _ _ htm ⟨hsρ, le_rfl⟩)]
  have hsumb : ∑ k ∈ Finset.range (m n),
      ∫ r in (unifPartIcc s t n k : ℝ)..(unifPartIcc s t n (k + 1)), |b r| ≤ I := by
    rw [hm.sum_integral_cells hn0 hab]
    exact intervalIntegral.integral_mono_interval le_rfl htm.1 htm.2
      (Eventually.of_forall fun _ => abs_nonneg _) (hab _ _ ⟨le_rfl, hsρ⟩ ⟨hsρ, le_rfl⟩)
  have hsum : |∑ k ∈ Finset.range (m n), (G (unifPartIcc s t n k) *
      (∫ r in (unifPartIcc s t n k : ℝ)..(unifPartIcc s t n (k + 1)), b r) -
      ∫ r in (unifPartIcc s t n k : ℝ)..(unifPartIcc s t n (k + 1)), F r * b r)| ≤ η / 2 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun k hk => hcell k (Finset.mem_range.1 hk)).trans ?_
    rw [← Finset.mul_sum]
    calc η / (2 * (I + 1)) * _ ≤ η / (2 * (I + 1)) * I := by gcongr
      _ ≤ η / 2 := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  have htail : |∫ r in tm..ρ, F r * b r| ≤ η / 2 := by
    have hb' := intervalIntegral.norm_integral_le_of_norm_le htm.2
      (f := fun r => F r * b r) (g := fun r => M * |b r|)
      (Eventually.of_forall fun r hr => by
        rw [Real.norm_eq_abs, abs_mul]
        have hmem := toNNReal_mem_Icc hr
        exact mul_le_mul_of_nonneg_right
          (hM _ ⟨(le_unifPartIcc s t n _).trans hmem.1, hmem.2⟩) (abs_nonneg _))
      ((hab _ _ htm ⟨hsρ, le_rfl⟩).const_mul _)
    rw [Real.norm_eq_abs, intervalIntegral.integral_const_mul] at hb'
    have hPd : ∫ r in tm..ρ, |b r| = P ρ - P (unifPartIcc s t n (m n)) := by
      simp only [P]
      rw [intervalIntegral.integral_interval_sub_left (hab _ _ ⟨le_rfl, hsρ⟩ ⟨hsρ, le_rfl⟩)
        (hab _ _ ⟨le_rfl, hsρ⟩ htm)]
    rw [hPd] at hb'
    calc _ ≤ M * (P ρ - P (unifPartIcc s t n (m n))) := hb'
      _ ≤ M * (η / (2 * (M + 1))) := by
          gcongr; rw [abs_sub_comm] at hPn; exact (le_abs_self _).trans hPn.le
      _ ≤ (M + 1) * (η / (2 * (M + 1))) := by gcongr; linarith
      _ = η / 2 := by field_simp
  rw [hsplit]
  have : ∑ k ∈ Finset.range (m n), G (unifPartIcc s t n k) *
      (∫ r in (unifPartIcc s t n k : ℝ)..(unifPartIcc s t n (k + 1)), b r) -
      ((∑ k ∈ Finset.range (m n),
        ∫ r in (unifPartIcc s t n k : ℝ)..(unifPartIcc s t n (k + 1)), F r * b r) +
        ∫ r in tm..ρ, F r * b r) =
      (∑ k ∈ Finset.range (m n), (G (unifPartIcc s t n k) *
        (∫ r in (unifPartIcc s t n k : ℝ)..(unifPartIcc s t n (k + 1)), b r) -
        ∫ r in (unifPartIcc s t n k : ℝ)..(unifPartIcc s t n (k + 1)), F r * b r)) -
        ∫ r in tm..ρ, F r * b r := by
    rw [Finset.sum_sub_distrib]; ring
  rw [this]
  calc _ ≤ _ := abs_sub _ _
    _ ≤ η / 2 + η / 2 := add_le_add hsum htail
    _ = η := by ring

/-- Telescoping over the alive cells. -/
lemma sum_sub_grid (m : ℕ → ℕ) (j : ℝ≥0 → ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range (m n), (j (unifPartIcc s t n (k + 1)) - j (unifPartIcc s t n k)) =
      j (unifPartIcc s t n (m n)) - j s := by
  rw [Finset.sum_range_sub (fun k => j (unifPartIcc s t n k)), unifPartIcc_zero]

/-- **Singular sums**: if the monotone continuous `j` moves only across points where `G = G₀`,
then `∑ G(t_k) (j(t_{k+1}) - j(t_k)) → G₀ (j ρ - j s)`. -/
lemma GridApprox.tendsto_singular (hm : GridApprox s t ρ m) (hst : s ≤ t) {G j : ℝ≥0 → ℝ}
    {G₀ : ℝ} (hG : ContinuousOn G (Icc s ρ)) (hj : ContinuousOn j (Icc s ρ))
    (hjm : MonotoneOn j (Icc s ρ))
    (hsupp : ∀ u v, s ≤ u → u ≤ v → v ≤ ρ → j u ≠ j v → ∃ r ∈ Icc u v, G r = G₀) :
    Tendsto (fun n => ∑ k ∈ Finset.range (m n), G (unifPartIcc s t n k) *
        (j (unifPartIcc s t n (k + 1)) - j (unifPartIcc s t n k)))
      atTop (𝓝 (G₀ * (j ρ - j s))) := by
  have hjt := hm.tendsto_comp hj hm.s_le
  have hlim : Tendsto (fun n => G₀ * (j (unifPartIcc s t n (m n)) - j s)) atTop
      (𝓝 (G₀ * (j ρ - j s))) := (hjt.sub_const _).const_mul _
  set D := j ρ - j s
  have hD : 0 ≤ D := sub_nonneg.2 (hjm ⟨le_rfl, hm.s_le⟩ ⟨hm.s_le, le_rfl⟩ hm.s_le)
  refine tendsto_of_forall_eventually_abs_le fun η hη => ?_
  have hη' : 0 < η / (2 * (D + 1)) := by positivity
  filter_upwards [hm.eventually_abs_sub_le hst hG hη',
    (Metric.tendsto_nhds.1 hlim) (η / 2) (half_pos hη)] with n ⟨hn0, hosc⟩ hn
  rw [Real.dist_eq] at hn
  have hdecomp : ∑ k ∈ Finset.range (m n), G (unifPartIcc s t n k) *
      (j (unifPartIcc s t n (k + 1)) - j (unifPartIcc s t n k)) =
      (∑ k ∈ Finset.range (m n), (G (unifPartIcc s t n k) - G₀) *
        (j (unifPartIcc s t n (k + 1)) - j (unifPartIcc s t n k))) +
      G₀ * (j (unifPartIcc s t n (m n)) - j s) := by
    rw [← sum_sub_grid m j n, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hterm : ∀ k < m n, |(G (unifPartIcc s t n k) - G₀) *
      (j (unifPartIcc s t n (k + 1)) - j (unifPartIcc s t n k))| ≤
      η / (2 * (D + 1)) * (j (unifPartIcc s t n (k + 1)) - j (unifPartIcc s t n k)) := by
    intro k hk
    have hk0 := hm.mem_Icc hn0 hk.le
    have hk1 := hm.mem_Icc hn0 hk
    have hmono : j (unifPartIcc s t n k) ≤ j (unifPartIcc s t n (k + 1)) :=
      hjm hk0 hk1 (unifPartIcc_mono s t n (Nat.le_succ k))
    rw [abs_mul, abs_of_nonneg (sub_nonneg.2 hmono)]
    by_cases heq : j (unifPartIcc s t n k) = j (unifPartIcc s t n (k + 1))
    · rw [heq, sub_self, mul_zero, mul_zero]
    · obtain ⟨r, hr, hGr⟩ := hsupp _ _ hk0.1 (unifPartIcc_mono s t n (Nat.le_succ k)) hk1.2 heq
      refine mul_le_mul_of_nonneg_right ?_ (sub_nonneg.2 hmono)
      rw [← hGr, abs_sub_comm]
      exact hosc k hk r hr
  have hsum : |∑ k ∈ Finset.range (m n), (G (unifPartIcc s t n k) - G₀) *
      (j (unifPartIcc s t n (k + 1)) - j (unifPartIcc s t n k))| ≤ η / 2 := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun k hk => hterm k (Finset.mem_range.1 hk)).trans ?_
    rw [← Finset.mul_sum, sum_sub_grid m j n]
    have hjle : j (unifPartIcc s t n (m n)) - j s ≤ D :=
      sub_le_sub_right (hjm (hm.mem_Icc hn0 le_rfl) ⟨hm.s_le, le_rfl⟩ (hm n hn0).2.1) _
    have hjnn : 0 ≤ j (unifPartIcc s t n (m n)) - j s :=
      sub_nonneg.2 (hjm ⟨le_rfl, hm.s_le⟩ (hm.mem_Icc hn0 le_rfl) (le_unifPartIcc s t n _))
    calc η / (2 * (D + 1)) * (j (unifPartIcc s t n (m n)) - j s)
        ≤ η / (2 * (D + 1)) * (D + 1) := by gcongr; linarith
      _ = η / 2 := by field_simp
  rw [hdecomp]
  calc _ = |(∑ k ∈ Finset.range (m n), (G (unifPartIcc s t n k) - G₀) *
        (j (unifPartIcc s t n (k + 1)) - j (unifPartIcc s t n k))) +
        (G₀ * (j (unifPartIcc s t n (m n)) - j s) - G₀ * D)| := by congr 1; ring
    _ ≤ _ := abs_add_le _ _
    _ ≤ η / 2 + η / 2 := add_le_add hsum hn.le
    _ = η := by ring

end GridLimits

end InteractingSLE.LocalTime
