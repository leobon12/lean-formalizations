import HigherDimLQGMetric.Coord.UniformRealization

/-!
# Weighted-length algebra for path recovery

These are generic versions of the weighted length bounds for an arbitrary
coordinate distance function.  They are used in MA1 A6 and A7.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology BoundedContinuousFunction
open LQGMetric.MetricGeometry
open scoped ENNReal

namespace HigherDimLQGMetric

theorem ofReal_mul_curveLengthWith_le_weightedLengthWith
    {X : Type*} {δ : X → X → ℝ≥0∞} {w : X → ℝ} {P : ℝ → X}
    {a b m : ℝ} (hab : a ≤ b)
    (hm : ∀ t ∈ Icc a b, m ≤ w (P t)) :
    ENNReal.ofReal m * curveLengthWith δ P a b ≤
      weightedLengthWith δ w P a b := by
  calc
    ENNReal.ofReal m * curveLengthWith δ P a b
        ≤ infAlong w P a b * curveLengthWith δ P a b :=
          mul_le_mul' (ofReal_le_infAlong hm) le_rfl
    _ ≤ weightedLengthWith δ w P a b :=
      le_partitionSup_single (g := fun u v => infAlong w P u v * curveLengthWith δ P u v) hab

theorem weightedLengthWith_le_ofReal_mul_curveLengthWith
    {X : Type*} {δ : X → X → ℝ≥0∞} {w : X → ℝ} {P : ℝ → X}
    {a b M : ℝ} (hM : ∀ t ∈ Icc a b, w (P t) ≤ M) :
    weightedLengthWith δ w P a b ≤
      ENNReal.ofReal M * curveLengthWith δ P a b := by
  refine partitionSup_le fun p => ?_
  calc
    p.sum (fun u v => infAlong w P u v * curveLengthWith δ P u v)
        ≤ ∑ i ∈ Finset.range p.n,
            ENNReal.ofReal M * curveLengthWith δ P (p.t i) (p.t (i + 1)) := by
          refine Finset.sum_le_sum fun i hi => ?_
          obtain ⟨h1, h2, h3⟩ := p.step (Finset.mem_range.1 hi)
          exact mul_le_mul' (infAlong_le_ofReal h2
            (fun s hs => hM s ⟨h1.trans hs.1, hs.2.trans h3⟩)) le_rfl
    _ = ENNReal.ofReal M * ∑ i ∈ Finset.range p.n,
          curveLengthWith δ P (p.t i) (p.t (i + 1)) := by rw [Finset.mul_sum]
    _ ≤ ENNReal.ofReal M * curveLengthWith δ P a b := by
      gcongr
      have hmono : Monotone (fun i => p.t (min i p.n)) := fun i j hij =>
        p.le_t (min_le_min_right p.n hij) (min_le_right _ _)
      have hsum := sum_curveLengthWith_le (δ := δ) (P := P) hmono p.n
      rw [min_self, Nat.zero_min, p.zero, p.last] at hsum
      apply le_trans (le_of_eq ?_) hsum
      apply Finset.sum_congr rfl
      intro i hi
      have hii : i < p.n := Finset.mem_range.1 hi
      rw [min_eq_left hii.le, min_eq_left (by omega)]

theorem curveLengthWith_ne_top_of_weightedLengthWith_ne_top
    {X : Type*} {δ : X → X → ℝ≥0∞} {w : X → ℝ} {P : ℝ → X}
    {a b m : ℝ} (hab : a ≤ b) (hm : 0 < m)
    (hw : ∀ t ∈ Icc a b, m ≤ w (P t))
    (hfin : weightedLengthWith δ w P a b ≠ ∞) :
    curveLengthWith δ P a b ≠ ∞ := by
  intro htop
  have h := ofReal_mul_curveLengthWith_le_weightedLengthWith (δ := δ) hab hw
  rw [htop, ENNReal.mul_top (by simpa using hm)] at h
  exact hfin (top_unique h)

theorem curveLengthWith_comp_monotoneOn
    {X : Type*} (δ : X → X → ℝ≥0∞) (P : ℝ → X)
    {φ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hφc : ContinuousOn φ (Icc a b)) (hφm : MonotoneOn φ (Icc a b)) :
    curveLengthWith δ (P ∘ φ) a b = curveLengthWith δ P (φ a) (φ b) := by
  unfold curveLengthWith
  simpa only [Function.comp_apply] using
    (partitionSup_comp hab hφc hφm (fun u v => δ (P u) (P v)))

theorem weightedLengthWith_comp_monotoneOn
    {X : Type*} (δ : X → X → ℝ≥0∞) (w : X → ℝ) (P : ℝ → X)
    {φ : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hφc : ContinuousOn φ (Icc a b)) (hφm : MonotoneOn φ (Icc a b)) :
    weightedLengthWith δ w (P ∘ φ) a b =
      weightedLengthWith δ w P (φ a) (φ b) := by
  unfold weightedLengthWith
  rw [← partitionSup_comp hab hφc hφm]
  refine partitionSup_congr fun u v hu huv hv => ?_
  have hsub : Icc u v ⊆ Icc a b := Icc_subset_Icc hu hv
  rw [infAlong_comp_monotoneOn huv (hφc.mono hsub) (hφm.mono hsub),
    curveLengthWith_comp_monotoneOn δ P huv (hφc.mono hsub) (hφm.mono hsub)]

/-- Weighted length is additive along adjacent time intervals for a distance
function satisfying the triangle inequality. -/
theorem weightedLengthWith_add
    {X : Type*} {δ : X → X → ℝ≥0∞} {w : X → ℝ} {P : ℝ → X}
    {a b c : ℝ} (hδ : ∀ p q r, δ p r ≤ δ p q + δ q r)
    (hab : a ≤ b) (hbc : b ≤ c) :
    weightedLengthWith δ w P a b + weightedLengthWith δ w P b c =
      weightedLengthWith δ w P a c := by
  unfold weightedLengthWith
  refine partitionSup_add (fun u x v _ hux hxv _ => ?_) hab hbc
  have hlen := curveLengthWith_add (δ := δ) (P := P)
    (fun p q r _ _ _ _ => hδ (P p) (P q) (P r)) hux hxv
  rw [← hlen, mul_add]
  exact add_le_add (mul_le_mul' (infAlong_anti le_rfl hxv) le_rfl)
    (mul_le_mul' (infAlong_anti hux le_rfl) le_rfl)

/-- Every metric function gives a triangle inequality after conversion to `ℝ≥0∞`. -/
theorem ofReal_metric_triangle
    {X : Type*} {ρ : X × X → ℝ} (hρ : LQGMetric.MetricGeometry.IsMetricFun ρ)
    (p q r : X) :
    ENNReal.ofReal (ρ (p, r)) ≤
      ENNReal.ofReal (ρ (p, q)) + ENNReal.ofReal (ρ (q, r)) := by
  have hpq : 0 ≤ ρ (p, q) := by
    change 0 ≤ dist (LQGMetric.MetricGeometry.MetricFunSpace.pt ρ hρ p)
      (LQGMetric.MetricGeometry.MetricFunSpace.pt ρ hρ q)
    exact dist_nonneg
  rw [← ENNReal.ofReal_add hpq (by
    change 0 ≤ dist (LQGMetric.MetricGeometry.MetricFunSpace.pt ρ hρ q)
      (LQGMetric.MetricGeometry.MetricFunSpace.pt ρ hρ r)
    exact dist_nonneg)]
  exact ENNReal.ofReal_le_ofReal (hρ.triangle p q r)

/-- Convert coordinate weighted length to ordinary weighted length on the
metric-function space. -/
theorem weightedLengthWith_metricFunSpace
    {X : Type*} {ρ : X × X → ℝ} (hρ : LQGMetric.MetricGeometry.IsMetricFun ρ)
    (w : X → ℝ) (P : ℝ → X) (a b : ℝ) :
    weightedLengthWith (fun x y => ENNReal.ofReal (ρ (x, y))) w P a b =
      weightedLength (w ∘ LQGMetric.metricFunSpaceVal ρ hρ)
        (LQGMetric.MetricGeometry.MetricFunSpace.pt ρ hρ ∘ P) a b := by
  unfold weightedLengthWith weightedLength
  apply partitionSup_congr
  intro u v hu huv hv
  congr 1
  rw [← curveLengthWith_edist]
  unfold curveLengthWith
  apply partitionSup_congr
  intro s t hs hst ht
  rw [edist_dist]
  rfl

/-- Coordinate curve length is ordinary curve length in its metric-function space. -/
theorem curveLengthWith_metricFunSpace
    {X : Type*} {ρ : X × X → ℝ} (hρ : LQGMetric.MetricGeometry.IsMetricFun ρ)
    (P : ℝ → X) (a b : ℝ) :
    curveLengthWith (fun x y => ENNReal.ofReal (ρ (x, y))) P a b =
      curveLength (LQGMetric.MetricGeometry.MetricFunSpace.pt ρ hρ ∘ P) a b := by
  rw [← curveLengthWith_edist]
  unfold curveLengthWith
  apply partitionSup_congr
  intro u v hu huv hv
  rw [edist_dist]
  rfl

/-- Weighted length of a path. -/
def pathWeightedLength {X : Type*} [PseudoEMetricSpace X] (w : X → ℝ)
    {x y : X} (γ : Path x y) : ℝ≥0∞ :=
  weightedLength w γ.extend 0 1

/-- Weighted length adds under path concatenation. -/
theorem pathWeightedLength_trans
    {X : Type*} [PseudoEMetricSpace X] {x y z : X}
    (w : X → ℝ) (γ : Path x y) (γ' : Path y z) :
    pathWeightedLength w (γ.trans γ') =
      pathWeightedLength w γ + pathWeightedLength w γ' := by
  unfold pathWeightedLength
  rw [← weightedLength_add (w := w) (P := (γ.trans γ').extend)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)]
  have h1 : weightedLength w (γ.trans γ').extend 0 (1 / 2) =
      weightedLength w γ.extend 0 1 := by
    rw [weightedLength_congr (Q := γ.extend ∘ fun t => 2 * t)
      (fun t ht => Path.extend_trans_of_le_half _ _ ht.2)]
    rw [weightedLength_comp_monotoneOn (w := w) (P := γ.extend)
      (φ := fun t => 2 * t) (by norm_num) (by fun_prop)
      (fun s _ t _ hst => by linarith)]
    norm_num
  have h2 : weightedLength w (γ.trans γ').extend (1 / 2) 1 =
      weightedLength w γ'.extend 0 1 := by
    rw [weightedLength_congr (Q := γ'.extend ∘ fun t => 2 * t - 1)
      (fun t ht => Path.extend_trans_of_half_le _ _ ht.1)]
    rw [weightedLength_comp_monotoneOn (w := w) (P := γ'.extend)
      (φ := fun t => 2 * t - 1) (by norm_num) (by fun_prop)
      (fun s _ t _ hst => by linarith)]
    norm_num
  rw [h1, h2]

theorem pathWeightedLength_refl
    {X : Type*} [PseudoEMetricSpace X] (w : X → ℝ) (x : X) :
    pathWeightedLength w (Path.refl x) = 0 := by
  apply le_antisymm _ bot_le
  exact (weightedLength_le_ofReal_mul_curveLength
    (M := w x) (w := w) (P := (Path.refl x).extend)
    (fun s hs => by simp)).trans (by
      rw [show curveLength (Path.refl x).extend 0 1 = 0 from pathLength_refl x, mul_zero]
      exact bot_le)

/-- Concatenate an indexed finite chain of paths. -/
def pathJoin {X : Type*} [TopologicalSpace X] (z : ℕ → X)
    (step : ∀ i : ℕ, Path (z i) (z (i + 1))) :
    (n : ℕ) → Path (z 0) (z n)
  | 0 => Path.refl (z 0)
  | n + 1 => (pathJoin z step n).trans (step n)

theorem pathLength_pathJoin
    {X : Type*} [EMetricSpace X] (z : ℕ → X)
    (step : ∀ i : ℕ, Path (z i) (z (i + 1))) (n : ℕ) :
    pathLength (pathJoin z step n) =
      ∑ i ∈ Finset.range n, pathLength (step i) := by
  induction n with
  | zero => simp [pathJoin, pathLength_refl]
  | succ n ih => simp [pathJoin, pathLength_trans, ih, Finset.sum_range_succ]

theorem pathWeightedLength_pathJoin
    {X : Type*} [EMetricSpace X] (w : X → ℝ) (z : ℕ → X)
    (step : ∀ i : ℕ, Path (z i) (z (i + 1))) (n : ℕ) :
    pathWeightedLength w (pathJoin z step n) =
      ∑ i ∈ Finset.range n, pathWeightedLength w (step i) := by
  induction n with
  | zero => simp [pathJoin, pathWeightedLength_refl]
  | succ n ih => simp [pathJoin, pathWeightedLength_trans, ih, Finset.sum_range_succ]

/-- A finite path chain requiring pieces only before its final index. -/
def pathJoinFinite {X : Type*} [TopologicalSpace X] (z : ℕ → X) (N : ℕ)
    (step : ∀ i : ℕ, i < N → Path (z i) (z (i + 1))) :
    (i : ℕ) → i ≤ N → Path (z 0) (z i)
  | 0, _ => Path.refl (z 0)
  | i + 1, hi => (pathJoinFinite z N step i (by omega)).trans (step i hi)

theorem pathLength_pathJoinFinite
    {X : Type*} [EMetricSpace X] (z : ℕ → X) (N : ℕ)
    (step : ∀ i : ℕ, i < N → Path (z i) (z (i + 1))) :
    ∀ i (hi : i ≤ N),
      pathLength (pathJoinFinite z N step i hi) =
        ∑ j ∈ Finset.range i, if hj : j < N then pathLength (step j hj) else 0 := by
  intro i
  induction i with
  | zero => intro hi; simp [pathJoinFinite, pathLength_refl]
  | succ i ih =>
      intro hi
      rw [pathJoinFinite, pathLength_trans, ih (by omega), Finset.sum_range_succ]
      simp [show i < N by omega]

theorem pathWeightedLength_pathJoinFinite
    {X : Type*} [EMetricSpace X] (w : X → ℝ) (z : ℕ → X) (N : ℕ)
    (step : ∀ i : ℕ, i < N → Path (z i) (z (i + 1))) :
    ∀ i (hi : i ≤ N),
      pathWeightedLength w (pathJoinFinite z N step i hi) =
        ∑ j ∈ Finset.range i,
          if hj : j < N then pathWeightedLength w (step j hj) else 0 := by
  intro i
  induction i with
  | zero => intro hi; simp [pathJoinFinite, pathWeightedLength_refl]
  | succ i ih =>
      intro hi
      rw [pathJoinFinite, pathWeightedLength_trans, ih (by omega), Finset.sum_range_succ]
      simp [show i < N by omega]

/-- The scalar estimate behind MA1 Lemma 2.4's weighted error bound.
The lower weight `v - Ω` is allowed to be negative. -/
theorem weighted_recovery_piece_bound
    {v Ω M ℓ e : ℝ} {A B : ℝ≥0∞}
    (hv : 0 ≤ v) (hvM : v ≤ M) (hΩ : 0 ≤ Ω) (hΩM : Ω ≤ M)
    (hℓ : 0 ≤ ℓ) (he : 0 ≤ e)
    (hA : A ≤ ENNReal.ofReal ((v + Ω) * (ℓ + e)))
    (hB : ENNReal.ofReal ((v - Ω) * ℓ) ≤ B) :
    A ≤ B + ENNReal.ofReal (2 * Ω * ℓ + 2 * M * e) := by
  have herr : 0 ≤ 2 * Ω * ℓ + 2 * M * e := by
    have hM : 0 ≤ M := hv.trans hvM
    positivity
  by_cases hlow : 0 ≤ v - Ω
  · have hle : (v + Ω) * (ℓ + e) ≤
        (v - Ω) * ℓ + (2 * Ω * ℓ + 2 * M * e) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hvM) he,
        mul_nonneg (sub_nonneg.mpr hΩM) he]
    have hright : ENNReal.ofReal ((v + Ω) * (ℓ + e)) ≤
        ENNReal.ofReal ((v - Ω) * ℓ) +
          ENNReal.ofReal (2 * Ω * ℓ + 2 * M * e) := by
      rw [← ENNReal.ofReal_add (mul_nonneg hlow hℓ) herr]
      exact ENNReal.ofReal_le_ofReal hle
    exact hA.trans (hright.trans (by
      simpa [add_comm] using
        (add_le_add_right hB (ENNReal.ofReal (2 * Ω * ℓ + 2 * M * e)))))
  · have hle : (v + Ω) * (ℓ + e) ≤ 2 * Ω * ℓ + 2 * M * e := by
      have hvΩ : v ≤ Ω := by linarith [lt_of_not_ge hlow]
      nlinarith [mul_nonneg (sub_nonneg.mpr hvΩ) hℓ,
        mul_nonneg (sub_nonneg.mpr hvM) he,
        mul_nonneg (sub_nonneg.mpr hΩM) he]
    calc
      A ≤ ENNReal.ofReal ((v + Ω) * (ℓ + e)) := hA
      _ ≤ ENNReal.ofReal (2 * Ω * ℓ + 2 * M * e) := ENNReal.ofReal_le_ofReal hle
      _ ≤ B + ENNReal.ofReal (2 * Ω * ℓ + 2 * M * e) := by
        exact le_add_self

/-- Sum the piecewise recovery errors using the total old length and the
number of pieces. -/
theorem weighted_recovery_error_sum_le
    (N : ℕ) (ℓ : ℕ → ℝ) {L Ω M e : ℝ}
    (hℓ : ∀ i < N, 0 ≤ ℓ i)
    (hℓsum : (∑ i ∈ Finset.range N, ℓ i) ≤ L)
    (hΩ : 0 ≤ Ω) (hM : 0 ≤ M) (he : 0 ≤ e) :
    (∑ i ∈ Finset.range N,
      ENNReal.ofReal (2 * Ω * ℓ i + 2 * M * e)) ≤
      ENNReal.ofReal (2 * Ω * L + 2 * M * N * e) := by
  have hterm : ∀ i ∈ Finset.range N,
      0 ≤ 2 * Ω * ℓ i + 2 * M * e := by
    intro i hi
    have hi' : i < N := Finset.mem_range.1 hi
    have hi0 := hℓ i hi'
    positivity
  rw [← ENNReal.ofReal_sum_of_nonneg hterm]
  apply ENNReal.ofReal_le_ofReal
  have hsum : (∑ i ∈ Finset.range N, (2 * Ω * ℓ i + 2 * M * e)) =
      2 * Ω * (∑ i ∈ Finset.range N, ℓ i) + 2 * M * N * e := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  rw [hsum]
  have hmult : 2 * Ω * (∑ i ∈ Finset.range N, ℓ i) ≤ 2 * Ω * L :=
    mul_le_mul_of_nonneg_left hℓsum (by positivity)
  linarith

/-- Add piecewise recovery estimates over a finite chain. -/
theorem weighted_recovery_chain_bound
    {X : Type*} [EMetricSpace X] (w : X → ℝ)
    (z : ℕ → X) (N : ℕ)
    (step : ∀ i : ℕ, i < N → Path (z i) (z (i + 1)))
    (ℓ : ℕ → ℝ) (oldCost : ℕ → ℝ≥0∞)
    {L Ω M e : ℝ} {B : ℝ≥0∞}
    (hℓ : ∀ i < N, 0 ≤ ℓ i)
    (hℓsum : (∑ i ∈ Finset.range N, ℓ i) ≤ L)
    (hΩ : 0 ≤ Ω) (hM : 0 ≤ M) (he : 0 ≤ e)
    (hpiece : ∀ i (hi : i < N),
      pathWeightedLength w (step i hi) ≤
        oldCost i + ENNReal.ofReal (2 * Ω * ℓ i + 2 * M * e))
    (hcostsum : (∑ i ∈ Finset.range N, oldCost i) ≤ B) :
    pathWeightedLength w (pathJoinFinite z N step N le_rfl) ≤
      B + ENNReal.ofReal (2 * Ω * L + 2 * M * N * e) := by
  rw [pathWeightedLength_pathJoinFinite]
  have hsum : (∑ i ∈ Finset.range N,
      if hi : i < N then pathWeightedLength w (step i hi) else 0) ≤
      (∑ i ∈ Finset.range N, oldCost i) +
        (∑ i ∈ Finset.range N,
          ENNReal.ofReal (2 * Ω * ℓ i + 2 * M * e)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i hi
    simp only [dite_eq_left (Finset.mem_range.1 hi)]
    exact hpiece i (Finset.mem_range.1 hi)
  exact hsum.trans (add_le_add hcostsum
    (weighted_recovery_error_sum_le N ℓ hℓ hℓsum hΩ hM he))

/-- Every point of a curve is at coordinate distance at most its total length
from the initial point. -/
theorem coordinate_distance_le_length_bound
    {X : Type*} [MetricSpace X] (ρ : X × X → ℝ) (Q : Set.Icc (0 : ℝ) 1 →ᵇ X)
    {s : ℝ} (hs : 0 ≤ s)
    (hlen : curveLengthWith (fun x y => ENNReal.ofReal (ρ (x, y)))
      (Set.IccExtend zero_le_one Q) 0 1 ≤ ENNReal.ofReal s)
    (t : Set.Icc (0 : ℝ) 1) :
    ρ (Q 0, Q t) ≤ s := by
  let P := Set.IccExtend zero_le_one Q
  have hinc : ENNReal.ofReal (ρ (Q 0, Q t)) ≤
      curveLengthWith (fun x y => ENNReal.ofReal (ρ (x, y))) P 0 (t : ℝ) := by
    have h := le_curveLengthWith (δ := fun x y => ENNReal.ofReal (ρ (x, y)))
      (P := P) t.property.1
    simpa [P, Set.IccExtend_of_mem] using h
  have hsub : curveLengthWith (fun x y => ENNReal.ofReal (ρ (x, y))) P 0 (t : ℝ) ≤
      curveLengthWith (fun x y => ENNReal.ofReal (ρ (x, y))) P 0 1 :=
    curveLengthWith_mono_interval le_rfl t.property.1 t.property.2
  exact (ENNReal.ofReal_le_ofReal_iff hs).1 (hinc.trans (hsub.trans hlen))

end HigherDimLQGMetric
