import HigherDimLFPP.Upper.TreeJensen
import HigherDimLFPP.Upper.PathTree
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# The deterministic tree inequality: Lemma 4.1 and (4.16) (`TreeInequality`)

Source: `source/higher-dimensional-lfpp-limit.pdf`, §4.1, Lemma 4.1 and the per-node bound (4.16),
in the generalized form of HA3 D2 (`planning/audits/HA3-section-4.md`): threshold `a₀ ≥ 0`,
`b_u = min(a_u, a₀)/δ²`, oscillation `ω` of the field on `closure U` at distance `5 ε`.

2D source: the second half of `LQGDimension/LFPP/TreeInequalityAux.lean` (`local_bound`,
`segAvg_sub_osc_le`, `deriv_intervalIntegrable`, `chord_le_arclength`, `Lnode_sum`,
`Lnode_leaf`) and `LQGDimension/LFPP/TreeInequality.lean` (`treeInequality`), for paths in
`Rd d`.  Differences from 2D: the oscillation is taken on `closure U` at distance `5 ε` (every
point of a leaf subpath is within `4 R_v` of `x_v` and every point of its chord within `R_v`,
and the root is never a leaf); chords lie in `U` by convexity of the cube; the per-node cost is
`b_u = min(a_u, a₀)/δ²` instead of the 2D bin `⌊min(A_u, 1)/δ²⌋`.

For a well-formed tree `T` of an admissible path `γ`, a continuous field `φ` and `ζ = δ^{3/2}`:

* the leaves' time intervals partition `[0,1]`, so the LFPP length is the sum of the leaf
  lengths (`Lnode_sum`);
* each leaf length is at least `R_v e^{ζ (H_v - ω(5ε))}` (chord ≤ arclength and the oscillation
  bound, `Lnode_leaf`);
* Jensen's inequality for `log`, applied node by node with the weights `p_{uv} = R_v / S_u`,
  gives `log L ≥ ζ H_root - ζ ω + Σ_v θ(v) Σ_{u ≺ v} (a_u + ζ Δ_u)` (`tree_jensen_root`);
* (4.16): `-(a_u + ζ Δ_u) ≤ δ² (δ^{-1/2} G_u - b_u)` (`local_bound`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set

namespace HigherDimLFPP.Upper

/-! ## The cube and the oscillation -/

section Cube

variable {d : ℕ}

/-- The cube `U = (-2,2)^d` is convex. -/
theorem convex_cube (d : ℕ) : Convex ℝ (cube d) := by
  intro z hz w hw a b ha hb hab i
  have h1 := abs_lt.1 (hz i)
  have h2 := abs_lt.1 (hw i)
  have e : (a • z + b • w).ofLp i = a * z.ofLp i + b * w.ofLp i := by
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  show |(a • z + b • w).ofLp i| < 2
  rw [e, abs_lt]
  have hM : max (z.ofLp i) (w.ofLp i) < 2 := max_lt h1.2 h2.2
  have hm : -2 < min (z.ofLp i) (w.ofLp i) := lt_min h1.1 h2.1
  have a1 := mul_le_mul_of_nonneg_left (le_max_left (z.ofLp i) (w.ofLp i)) ha
  have a2 := mul_le_mul_of_nonneg_left (le_max_right (z.ofLp i) (w.ofLp i)) hb
  have a3 := mul_le_mul_of_nonneg_left (min_le_left (z.ofLp i) (w.ofLp i)) ha
  have a4 := mul_le_mul_of_nonneg_left (min_le_right (z.ofLp i) (w.ofLp i)) hb
  have eM : a * max (z.ofLp i) (w.ofLp i) + b * max (z.ofLp i) (w.ofLp i) =
      max (z.ofLp i) (w.ofLp i) := by rw [← add_mul, hab, one_mul]
  have em : a * min (z.ofLp i) (w.ofLp i) + b * min (z.ofLp i) (w.ofLp i) =
      min (z.ofLp i) (w.ofLp i) := by rw [← add_mul, hab, one_mul]
  constructor <;> linarith

/-- Points of a chord between two points of `U` lie in `U`. -/
theorem segPt_mem_cube {a b : Rd d} (ha : a ∈ cube d) (hb : b ∈ cube d) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) : a + s • (b - a) ∈ cube d :=
  (convex_cube d).add_smul_sub_mem ha hb hs

/-- `closure U` is compact. -/
theorem isCompact_closure_cube (d : ℕ) : IsCompact (closure (cube d)) := by
  have hb : Bornology.IsBounded (cube d) :=
    (Metric.isBounded_closedBall (x := (0 : Rd d)) (r := 2 * Real.sqrt d)).subset
      fun z hz => mem_closedBall_zero_iff.2 (norm_le_of_mem_cube hz)
  exact Metric.isCompact_of_isClosed_isBounded isClosed_closure hb.closure

/-- The oscillation bounds the increments of a continuous field on `closure U`. -/
theorem abs_sub_le_osc {φ : Rd d → ℝ} (hφ : Continuous φ) {r : ℝ} {z w : Rd d}
    (hz : z ∈ closure (cube d)) (hw : w ∈ closure (cube d)) (hzw : ‖z - w‖ ≤ r) :
    |φ z - φ w| ≤ osc φ r := by
  obtain ⟨C, hC⟩ := (isCompact_closure_cube d).exists_bound_of_continuousOn hφ.continuousOn
  refine le_csSup ⟨2 * C, ?_⟩ ⟨z, w, hz, hw, hzw, rfl⟩
  rintro x ⟨z', w', hz', hw', -, rfl⟩
  have h1 := hC z' hz'
  have h2 := hC w' hw'
  rw [Real.norm_eq_abs] at h1 h2
  obtain ⟨a1, a2⟩ := abs_le.1 h1
  obtain ⟨b1, b2⟩ := abs_le.1 h2
  rw [abs_le]
  constructor <;> linarith

/-- A point of `closure U` within distance `r` of every point of a chord of `U` has
`φ ≥ ⟨φ, ν_chord⟩ - ω(r)`. -/
theorem segAvg_sub_osc_le {φ : Rd d → ℝ} (hφ : Continuous φ) {a b p : Rd d}
    (ha : a ∈ cube d) (hb : b ∈ cube d) (hp : p ∈ closure (cube d)) {r : ℝ}
    (hd : ∀ s ∈ Icc (0 : ℝ) 1, ‖p - (a + s • (b - a))‖ ≤ r) :
    segAvg φ a b - osc φ r ≤ φ p := by
  have hc : Continuous fun s : ℝ => φ (a + s • (b - a)) :=
    hφ.comp (continuous_const.add (continuous_id.smul continuous_const))
  have hle : segAvg φ a b ≤ ∫ _ in (0 : ℝ)..1, (φ p + osc φ r) := by
    unfold segAvg
    refine intervalIntegral.integral_mono_on zero_le_one (hc.intervalIntegrable _ _)
      intervalIntegrable_const fun s hs => ?_
    have := abs_sub_le_osc hφ hp (subset_closure (segPt_mem_cube ha hb hs)) (hd s hs)
    obtain ⟨h1, h2⟩ := abs_le.1 this
    linarith
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, one_mul] at hle
  linarith

end Cube

/-! ## Analytic lemmas on admissible paths -/

section Path

variable {d : ℕ} {γ : ℝ → Rd d}

theorem exists_piece {k : ℕ} {t : Fin (k + 1) → ℝ} (ht0 : t 0 = 0)
    (htk : t (Fin.last k) = 1) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hxt : x ∉ range t) :
    ∃ i : Fin k, t i.castSucc < x ∧ x < t i.succ := by
  obtain ⟨S, hS⟩ : ∃ S : Finset (Fin (k + 1)), S = Finset.univ.filter fun j => t j < x :=
    ⟨_, rfl⟩
  have hmem : ∀ j, j ∈ S ↔ t j < x := fun j => by simp [hS]
  have hne : S.Nonempty := ⟨0, (hmem 0).2 (by rw [ht0]; exact hx.1)⟩
  have hm : t (S.max' hne) < x := (hmem _).1 (S.max'_mem hne)
  have hml : S.max' hne ≠ Fin.last k := by
    intro h
    rw [h, htk] at hm
    linarith [hx.2]
  obtain ⟨i, hi⟩ := Fin.exists_castSucc_eq.2 hml
  refine ⟨i, by rw [hi]; exact hm, ?_⟩
  rcases lt_or_ge x (t i.succ) with h | h
  · exact h
  · exfalso
    rcases h.lt_or_eq with h | h
    · have : i.succ ≤ S.max' hne := S.le_max' _ ((hmem _).2 h)
      rw [← hi] at this
      exact absurd this (not_le.2 Fin.castSucc_lt_succ)
    · exact hxt ⟨_, h⟩

theorem hasDerivAt_of_piece {k : ℕ} {t : Fin (k + 1) → ℝ} (ht0 : t 0 = 0)
    (htk : t (Fin.last k) = 1)
    (hC : ∀ i : Fin k, ContDiffOn ℝ 1 γ (Icc (t i.castSucc) (t i.succ)))
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) (hxt : x ∉ range t) : HasDerivAt γ (deriv γ x) x := by
  obtain ⟨i, h1, h2⟩ := exists_piece ht0 htk hx hxt
  exact ((hC i).contDiffAt (Icc_mem_nhds h1 h2)).differentiableAt_one.hasDerivAt

theorem deriv_bound_piece {a b : ℝ} (hab : a < b) (hC : ContDiffOn ℝ 1 γ (Icc a b)) :
    ∃ C, 0 ≤ C ∧ ∀ x ∈ Ioo a b, ‖deriv γ x‖ ≤ C := by
  obtain ⟨C, hC'⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn
    (hC.continuousOn_derivWithin (uniqueDiffOn_Icc hab) le_rfl)
  refine ⟨max C 0, le_max_right _ _, fun x hx => ?_⟩
  rw [← derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)]
  exact (hC' x (Ioo_subset_Icc_self hx)).trans (le_max_left _ _)

/-- `γ'` is integrable on `[0,1]` for an admissible path. -/
theorem deriv_intervalIntegrable (hγ : IsAdmissiblePath d γ) :
    IntervalIntegrable (deriv γ) volume 0 1 := by
  obtain ⟨k, t, ht, ht0, htk, hC⟩ := hγ.piecewise_contDiff
  have hB : ∀ i : Fin k, ∃ C, 0 ≤ C ∧
      ∀ x ∈ Ioo (t i.castSucc) (t i.succ), ‖deriv γ x‖ ≤ C :=
    fun i => deriv_bound_piece (ht Fin.castSucc_lt_succ) (hC i)
  choose C hC0 hCb using hB
  have hbound : ∀ x ∈ Ioo (0 : ℝ) 1, x ∉ range t → ‖deriv γ x‖ ≤ ∑ i, C i := by
    intro x hx hxt
    obtain ⟨i, h1, h2⟩ := exists_piece ht0 htk hx hxt
    exact (hCb i x ⟨h1, h2⟩).trans
      (Finset.single_le_sum (fun j _ => hC0 j) (Finset.mem_univ i))
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  refine Measure.integrableOn_of_bounded (M := ∑ i, C i) measure_Ioc_lt_top.ne
    (measurable_deriv γ).aestronglyMeasurable ?_
  have hfin : (insert (1 : ℝ) (range t)).Countable := ((finite_range t).insert 1).countable
  rw [ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [hfin.ae_notMem volume] with x hx hxI
  rw [mem_insert_iff, not_or] at hx
  exact hbound x ⟨hxI.1, lt_of_le_of_ne hxI.2 hx.1⟩ hx.2

/-- The LFPP integrand `e^{ζ φ(γ t)} |γ'(t)|`. -/
def lenIntegrand (ζ : ℝ) (φ : Rd d → ℝ) (γ : ℝ → Rd d) (t : ℝ) : ℝ :=
  Real.exp (ζ * φ (γ t)) * ‖deriv γ t‖

theorem lenIntegrand_intervalIntegrable (hγ : IsAdmissiblePath d γ) {φ : Rd d → ℝ}
    (hφ : Continuous φ) (ζ : ℝ) : IntervalIntegrable (lenIntegrand ζ φ γ) volume 0 1 := by
  have hc : ContinuousOn (fun t => Real.exp (ζ * φ (γ t))) (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le zero_le_one]
    exact Real.continuous_exp.comp_continuousOn
      ((continuous_const.mul hφ).comp_continuousOn hγ.continuousOn)
  exact (deriv_intervalIntegrable hγ).norm.continuousOn_mul hc

theorem intervalIntegrable_of_sub {F : Type*} [NormedAddCommGroup F] {f : ℝ → F}
    (hf : IntervalIntegrable f volume 0 1) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    IntervalIntegrable f volume a b :=
  hf.mono_set (by
    rw [uIcc_of_le hab, uIcc_of_le zero_le_one]
    exact Icc_subset_Icc ha hb)

/-- Chord ≤ arclength on every subinterval of `[0, 1]` (HA3 F9). -/
theorem chord_le_arclength (hγ : IsAdmissiblePath d γ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b ≤ 1) : ‖γ b - γ a‖ ≤ ∫ t in a..b, ‖deriv γ t‖ := by
  obtain ⟨k, t, _, ht0, htk, hC⟩ := hγ.piecewise_contDiff
  have hI := intervalIntegrable_of_sub (deriv_intervalIntegrable hγ) ha hab hb
  have hFTC := integral_eq_of_hasDerivAt_off_countable_of_le γ (deriv γ) hab
    (countable_range t) (hγ.continuousOn.mono (Icc_subset_Icc ha hb))
    (fun x hx => hasDerivAt_of_piece ht0 htk hC
      ⟨lt_of_le_of_lt ha hx.1.1, lt_of_lt_of_le hx.1.2 hb⟩ hx.2) hI
  rw [← hFTC]
  exact intervalIntegral.norm_integral_le_integral_norm hab

/-! ### The LFPP length along the tree -/

variable {T : CutTree} {K : ℕ} {ε ρ₀ : ℝ}

open TreeJensen

/-- LFPP length of the subpath of node `u`. -/
def Lnode (T : CutTree) (ζ : ℝ) (φ : Rd d → ℝ) (γ : ℝ → Rd d) (u : List ℕ) : ℝ :=
  ∫ t in T.t₀ u..T.t₁ u, lenIntegrand ζ φ γ t

theorem Lnode_root (hT : T.WF γ K ε ρ₀) (ζ : ℝ) (φ : Rd d → ℝ) :
    Lnode T ζ φ γ [] = lfppLength ζ φ γ := by
  unfold Lnode lfppLength lenIntegrand
  rw [hT.root_time.1, hT.root_time.2]

/-- Additivity of the LFPP length over the children of an internal node. -/
theorem Lnode_sum (hT : T.WF γ K ε ρ₀) (hγ : IsAdmissiblePath d γ) {φ : Rd d → ℝ}
    (hφ : Continuous φ) (ζ : ℝ) {u : List ℕ} (hu : u ∈ T.nodes) (hn : 0 < T.nch u) :
    Lnode T ζ φ γ u = ∑ i ∈ Finset.range (T.nch u), Lnode T ζ φ γ (u ++ [i]) := by
  have hint := lenIntegrand_intervalIntegrable hγ hφ ζ
  have e : ∀ i ∈ Finset.range (T.nch u), Lnode T ζ φ γ (u ++ [i]) =
      ∫ t in ctime T u i..ctime T u (i + 1), lenIntegrand ζ φ γ t := by
    intro i hi
    rw [Lnode, t₀_child (Finset.mem_range.1 hi), t₁_child hT hu (Finset.mem_range.1 hi)]
  show ∫ t in T.t₀ u..T.t₁ u, lenIntegrand ζ φ γ t = _
  rw [Finset.sum_congr rfl e, intervalIntegral.sum_integral_adjacent_intervals
    (a := ctime T u) (f := lenIntegrand ζ φ γ) ?_, ctime_zero hT hu hn, ctime_nch]
  intro i hi
  obtain ⟨h0, -⟩ := ctime_mem hT hu hn hi.le
  obtain ⟨-, h1⟩ := ctime_mem hT hu hn (show i + 1 ≤ T.nch u by omega)
  exact intervalIntegrable_of_sub hint h0 (ctime_mono hT hu (Nat.le_succ i) (by omega)) h1

/-- The leaf bound: the LFPP length of a leaf subpath is at least `R_v e^{ζ (H_v - ω(5ε))}`
(HA3 D2, step 1; the root is internal, so every leaf satisfies the containment property). -/
theorem Lnode_leaf (hT : T.WF γ K ε ρ₀) (hγ : IsAdmissiblePath d γ) {φ : Rd d → ℝ}
    (hφ : Continuous φ) (hR0 : ε < T.R γ []) {ζ : ℝ} (hζ : 0 ≤ ζ) {v : List ℕ}
    (hv : v ∈ T.leaves) :
    T.R γ v * Real.exp (ζ * T.H γ φ v - ζ * osc φ (5 * ε)) ≤ Lnode T ζ φ γ v := by
  have hvn : v ∈ T.nodes := (Finset.mem_filter.1 hv).1
  have hnch : T.nch v = 0 := (Finset.mem_filter.1 hv).2
  have hvne : v ≠ [] := by
    rintro rfl
    have := (hT.internal_iff [] hvn).2 hR0
    omega
  obtain ⟨h0, hle, h1⟩ := times_mem hT hvn
  have hRε : T.R γ v ≤ ε := by
    by_contra h
    have := (hT.internal_iff v hvn).2 (not_le.1 h)
    omega
  have hint := intervalIntegrable_of_sub (lenIntegrand_intervalIntegrable hγ hφ ζ) h0 hle h1
  have hD := intervalIntegrable_of_sub (deriv_intervalIntegrable hγ) h0 hle h1
  have hU : ∀ s ∈ Icc (0 : ℝ) 1, γ s ∈ cube d := fun s hs => hγ.mapsTo hs
  have hx : T.x γ v ∈ cube d := hU _ ⟨h0, hle.trans h1⟩
  have hy : T.y γ v ∈ cube d := hU _ ⟨h0.trans hle, h1⟩
  have hpt : ∀ s ∈ Icc (T.t₀ v) (T.t₁ v),
      ζ * T.H γ φ v - ζ * osc φ (5 * ε) ≤ ζ * φ (γ s) := by
    intro s hs
    have hs01 : s ∈ Icc (0 : ℝ) 1 := ⟨h0.trans hs.1, hs.2.trans h1⟩
    have hball := hT.ball v hvn hvne s hs
    have key := segAvg_sub_osc_le hφ hx hy (subset_closure (hU s hs01)) (r := 5 * ε)
      (fun σ hσ => by
        have h2 : ‖σ • (T.y γ v - T.x γ v)‖ ≤ T.R γ v := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hσ.1]
          exact mul_le_of_le_one_left (norm_nonneg _) hσ.2
        calc ‖γ s - (T.x γ v + σ • (T.y γ v - T.x γ v))‖
            = ‖(γ s - T.x γ v) - σ • (T.y γ v - T.x γ v)‖ := by rw [sub_add_eq_sub_sub]
          _ ≤ ‖γ s - T.x γ v‖ + ‖σ • (T.y γ v - T.x γ v)‖ := norm_sub_le _ _
          _ ≤ 5 * ε := by linarith)
    have := mul_le_mul_of_nonneg_left key hζ
    unfold CutTree.H
    linarith
  calc T.R γ v * Real.exp (ζ * T.H γ φ v - ζ * osc φ (5 * ε))
      ≤ Real.exp (ζ * T.H γ φ v - ζ * osc φ (5 * ε)) *
          ∫ t in T.t₀ v..T.t₁ v, ‖deriv γ t‖ := by
        rw [mul_comm (T.R γ v)]
        exact mul_le_mul_of_nonneg_left (chord_le_arclength hγ h0 hle h1) (Real.exp_pos _).le
    _ = ∫ t in T.t₀ v..T.t₁ v, Real.exp (ζ * T.H γ φ v - ζ * osc φ (5 * ε)) * ‖deriv γ t‖ :=
        (intervalIntegral.integral_const_mul _ _).symm
    _ ≤ Lnode T ζ φ γ v :=
        intervalIntegral.integral_mono_on hle (hD.norm.const_mul _) hint fun s hs =>
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (hpt s hs)) (norm_nonneg _)

end Path

/-! ## The per-node bound (4.16) -/

section Local

variable {d : ℕ} {T : CutTree} {γ : ℝ → Rd d} {K : ℕ} {ε ρ₀ : ℝ}

open TreeJensen

/-- `G_u ≥ -Δ_u` for both kinds of nodes. -/
theorem neg_Delta_le_G (hT : TreeHyp T γ K ε ρ₀) {φ : Rd d → ℝ} (a₀ : ℝ) {u : List ℕ}
    (hu : u ∈ T.nodes) (hn : 0 < T.nch u) :
    T.H γ φ u - ∑ i ∈ Finset.range (T.nch u), T.R γ (u ++ [i]) / T.S γ u * T.H γ φ (u ++ [i]) ≤
      T.G γ a₀ φ u := by
  have hq_sum := q_sum hT hu hn
  rw [CutTree.G]
  split_ifs with hA1
  · exact le_rfl
  · have hbdd : BddAbove (Set.range fun i : Fin (T.nch u) =>
        T.H γ φ u - T.H γ φ (u ++ [(i : ℕ)])) := (Set.finite_range _).bddAbove
    have hle : ∀ i ∈ Finset.range (T.nch u), T.H γ φ u - T.H γ φ (u ++ [i]) ≤
        ⨆ j : Fin (T.nch u), (T.H γ φ u - T.H γ φ (u ++ [(j : ℕ)])) := fun i hi =>
      le_ciSup hbdd (⟨i, Finset.mem_range.1 hi⟩ : Fin (T.nch u))
    calc T.H γ φ u - ∑ i ∈ Finset.range (T.nch u),
          T.R γ (u ++ [i]) / T.S γ u * T.H γ φ (u ++ [i])
        = ∑ i ∈ Finset.range (T.nch u),
          T.R γ (u ++ [i]) / T.S γ u * (T.H γ φ u - T.H γ φ (u ++ [i])) := by
          simp only [mul_sub]
          rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hq_sum, one_mul]
      _ ≤ ∑ i ∈ Finset.range (T.nch u), T.R γ (u ++ [i]) / T.S γ u *
          ⨆ j : Fin (T.nch u), (T.H γ φ u - T.H γ φ (u ++ [(j : ℕ)])) :=
          Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hle i hi)
            (q_pos hT hu (Finset.mem_range.1 hi)).le
      _ = ⨆ j : Fin (T.nch u), (T.H γ φ u - T.H γ φ (u ++ [(j : ℕ)])) := by
          rw [← Finset.sum_mul, hq_sum, one_mul]

/-- **(4.16)**: `-(a_u + ζ Δ_u) ≤ δ² (δ^{-1/2} G_u - b_u)` at an internal node, with
`ζ = δ^{3/2}` and `b_u = min(a_u, a₀)/δ²`, written with the potential `F = ζ H - c` (the constant
`c` cancels because `Σ_i p_{u,i} = 1`).  Holds for every threshold `a₀` (HA3 D2, step 5). -/
theorem local_bound (hT : TreeHyp T γ K ε ρ₀) {φ : Rd d → ℝ} (a₀ : ℝ) {δ : ℝ} (hδ : 0 < δ)
    {u : List ℕ} (hu : u ∈ T.nodes) (hn : 0 < T.nch u) (c : ℝ) :
    -(δ ^ 2 * (δ ^ (-(1 / 2 : ℝ)) * T.G γ a₀ φ u - T.bcost γ a₀ δ u)) ≤ T.A γ u +
      (∑ i ∈ Finset.range (T.nch u), T.R γ (u ++ [i]) / T.S γ u *
          (δ ^ (3 / 2 : ℝ) * T.H γ φ (u ++ [i]) - c) - (δ ^ (3 / 2 : ℝ) * T.H γ φ u - c)) := by
  have hq_sum := q_sum hT hu hn
  have hζ : 0 ≤ δ ^ (3 / 2 : ℝ) := (Real.rpow_pos_of_pos hδ _).le
  have hδζ : δ ^ 2 * δ ^ (-(1 / 2 : ℝ)) = δ ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hδ]; norm_num
  have hsum : ∑ i ∈ Finset.range (T.nch u), T.R γ (u ++ [i]) / T.S γ u *
        (δ ^ (3 / 2 : ℝ) * T.H γ φ (u ++ [i]) - c) =
      δ ^ (3 / 2 : ℝ) * ∑ i ∈ Finset.range (T.nch u),
        T.R γ (u ++ [i]) / T.S γ u * T.H γ φ (u ++ [i]) - c := by
    calc _ = ∑ i ∈ Finset.range (T.nch u), (δ ^ (3 / 2 : ℝ) *
            (T.R γ (u ++ [i]) / T.S γ u * T.H γ φ (u ++ [i])) -
            T.R γ (u ++ [i]) / T.S γ u * c) :=
          Finset.sum_congr rfl fun i _ => by ring
      _ = δ ^ (3 / 2 : ℝ) * ∑ i ∈ Finset.range (T.nch u),
            T.R γ (u ++ [i]) / T.S γ u * T.H γ φ (u ++ [i]) -
            (∑ i ∈ Finset.range (T.nch u), T.R γ (u ++ [i]) / T.S γ u) * c := by
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
      _ = _ := by rw [hq_sum, one_mul]
  have hG := neg_Delta_le_G hT (φ := φ) a₀ hu hn
  -- `δ² b_u = min(a_u, a₀) ≤ a_u`
  have hb : δ ^ 2 * T.bcost γ a₀ δ u ≤ T.A γ u := by
    have hδ2 : δ ^ 2 ≠ 0 := by positivity
    rw [CutTree.bcost, mul_div_cancel₀ _ hδ2]
    exact min_le_left _ _
  have h4 : δ ^ 2 * (δ ^ (-(1 / 2 : ℝ)) * T.G γ a₀ φ u - T.bcost γ a₀ δ u) =
      δ ^ (3 / 2 : ℝ) * T.G γ a₀ φ u - δ ^ 2 * T.bcost γ a₀ δ u := by
    rw [mul_sub, ← mul_assoc, hδζ]
  rw [hsum, h4]
  have h3 := mul_le_mul_of_nonneg_left hG hζ
  linarith

end Local

/-! ## Lemma 4.1 + (4.16) -/

open TreeJensen in
/-- **Lemma 4.1 + (4.16), deterministic** (HA3 D2): for every admissible path, well-formed tree,
threshold `a₀ ≥ 0`, continuous field and `ζ = δ^{3/2}`,
`log ∫_P e^{ζφ} ≥ ζ H_root - ζ ω(5ε) - δ² Σ_v θ(v) Σ_{u ≺ v} (δ^{-1/2} G_u - b_u)`; the length
is positive and `θ` is a probability on the leaves. -/
theorem treeInequality (d : ℕ) [NeZero d] : TreeInequality d := by
  intro γ hγ K hK ε hε T hT a₀ _ha₀ φ hφ δ hδ
  have hroot : T.R γ [] = 1 := by
    simp only [CutTree.R, CutTree.x, CutTree.y, hT.root_time.1, hT.root_time.2]
    exact norm_target_sub_source hγ
  have hH : TreeHyp T γ K ε (2 * Real.sqrt d) := ⟨hT, hroot, by omega⟩
  have hR0 : ε < T.R γ [] := by rw [hroot]; exact hε.2
  have hζ : 0 ≤ δ ^ (3 / 2 : ℝ) := (Real.rpow_pos_of_pos hδ _).le
  obtain ⟨hs, hLpos, hineq⟩ := tree_jensen_root hH
    (L := Lnode T (δ ^ (3 / 2 : ℝ)) φ γ)
    (F := fun w => δ ^ (3 / 2 : ℝ) * T.H γ φ w - δ ^ (3 / 2 : ℝ) * osc φ (5 * ε))
    (Y := fun w => -(δ ^ 2 * (δ ^ (-(1 / 2 : ℝ)) * T.G γ a₀ φ w - T.bcost γ a₀ δ w)))
    (fun u hu hn => Lnode_sum hT hγ hφ _ hu hn)
    (fun v hv => Lnode_leaf hT hγ hφ hR0 hζ hv)
    (fun u hu hn => local_bound hH a₀ hδ hu hn _)
  rw [Lnode_root hT] at hLpos hineq
  refine ⟨hLpos, ?_, fun v hv => (flow_pos hH (Finset.mem_filter.1 hv).1).le, hs⟩
  have hineq' : (δ ^ (3 / 2 : ℝ) * T.H γ φ [] - δ ^ (3 / 2 : ℝ) * osc φ (5 * ε)) +
      ∑ v ∈ T.leaves, T.flow γ v * ∑ j ∈ Finset.range v.length,
        -(δ ^ 2 * (δ ^ (-(1 / 2 : ℝ)) * T.G γ a₀ φ (v.take j) - T.bcost γ a₀ δ (v.take j))) ≤
      Real.log (lfppLength (δ ^ (3 / 2 : ℝ)) φ γ) := hineq
  have e : ∑ v ∈ T.leaves, T.flow γ v * ∑ j ∈ Finset.range v.length,
        -(δ ^ 2 * (δ ^ (-(1 / 2 : ℝ)) * T.G γ a₀ φ (v.take j) - T.bcost γ a₀ δ (v.take j))) =
      -(δ ^ 2 * ∑ v ∈ T.leaves, T.flow γ v * ∑ j ∈ Finset.range v.length,
        (δ ^ (-(1 / 2 : ℝ)) * T.G γ a₀ φ (v.take j) - T.bcost γ a₀ δ (v.take j))) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.sum_neg_distrib, ← Finset.mul_sum]
    ring
  rw [e] at hineq'
  linarith

end HigherDimLFPP.Upper
