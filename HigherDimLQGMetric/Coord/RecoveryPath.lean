import HigherDimLQGMetric.Coord.RecoveryPiece

/-! # Path operations for coordinate lengths -/

set_option autoImplicit false

noncomputable section

open Set Filter Topology LQGMetric.MetricGeometry unitInterval BoundedContinuousFunction
open scoped ENNReal

namespace HigherDimLQGMetric

def pathOfBounded {X : Type*} [MetricSpace X]
    {x y : X} (Q : I →ᵇ X) (h0 : Q 0 = x) (h1 : Q 1 = y) : Path x y :=
  { toContinuousMap := Q.toContinuousMap
    source' := h0
    target' := h1 }

theorem pathOfBounded_apply {X : Type*} [MetricSpace X]
    {x y : X} (Q : I →ᵇ X) (h0 : Q 0 = x) (h1 : Q 1 = y) (t : I) :
    pathOfBounded Q h0 h1 t = Q t := rfl

theorem pathOfBounded_extend {X : Type*} [MetricSpace X]
    {x y : X} (Q : I →ᵇ X) (h0 : Q 0 = x) (h1 : Q 1 = y) :
    (fun t => (pathOfBounded Q h0 h1).extend t) = Set.IccExtend zero_le_one Q := by
  rfl

def coordinatePathLength {X : Type*} [TopologicalSpace X]
    (δ : X → X → ℝ≥0∞) {x y : X} (γ : Path x y) : ℝ≥0∞ :=
  curveLengthWith δ γ.extend 0 1

def coordinatePathWeightedLength {X : Type*} [TopologicalSpace X]
    (δ : X → X → ℝ≥0∞) (w : X → ℝ) {x y : X} (γ : Path x y) : ℝ≥0∞ :=
  weightedLengthWith δ w γ.extend 0 1

theorem curveLengthWith_congr_path {X : Type*} {δ : X → X → ℝ≥0∞}
    {P Q : ℝ → X} {a b : ℝ} (h : EqOn P Q (Icc a b)) :
    curveLengthWith δ P a b = curveLengthWith δ Q a b := by
  apply partitionSup_congr
  intro u v hu huv hv
  rw [h ⟨hu, huv.trans hv⟩, h ⟨hu.trans huv, hv⟩]

theorem weightedLengthWith_congr_path {X : Type*} {δ : X → X → ℝ≥0∞}
    {w : X → ℝ} {P Q : ℝ → X} {a b : ℝ}
    (h : EqOn P Q (Icc a b)) :
    weightedLengthWith δ w P a b = weightedLengthWith δ w Q a b := by
  apply partitionSup_congr
  intro u v hu huv hv
  have hsub : Icc u v ⊆ Icc a b := Icc_subset_Icc hu hv
  rw [infAlong_congr (fun s hs => by rw [h (hsub hs)]),
    curveLengthWith_congr_path (h.mono hsub)]

theorem coordinatePathLength_trans {X : Type*} [TopologicalSpace X]
    {δ : X → X → ℝ≥0∞}
    (hδ : ∀ p q r, δ p r ≤ δ p q + δ q r)
    {x y z : X} (γ : Path x y) (γ' : Path y z) :
    coordinatePathLength δ (γ.trans γ') =
      coordinatePathLength δ γ + coordinatePathLength δ γ' := by
  unfold coordinatePathLength
  rw [← curveLengthWith_add (δ := δ) (P := (γ.trans γ').extend)
    (fun p q r _ _ _ _ => hδ ((γ.trans γ').extend p) ((γ.trans γ').extend q)
      ((γ.trans γ').extend r)) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) ≤ 1)]
  have h1 : curveLengthWith δ (γ.trans γ').extend 0 (1 / 2) =
      curveLengthWith δ γ.extend 0 1 := by
    rw [curveLengthWith_congr_path (Q := γ.extend ∘ fun t => 2 * t)
      (fun t ht => Path.extend_trans_of_le_half _ _ ht.2)]
    rw [curveLengthWith_comp_monotoneOn δ γ.extend (by norm_num) (by fun_prop)
      (fun s _ t _ hst => by linarith)]
    norm_num
  have h2 : curveLengthWith δ (γ.trans γ').extend (1 / 2) 1 =
      curveLengthWith δ γ'.extend 0 1 := by
    rw [curveLengthWith_congr_path (Q := γ'.extend ∘ fun t => 2 * t - 1)
      (fun t ht => Path.extend_trans_of_half_le _ _ ht.1)]
    rw [curveLengthWith_comp_monotoneOn δ γ'.extend (by norm_num) (by fun_prop)
      (fun s _ t _ hst => by linarith)]
    norm_num
  rw [h1, h2]

theorem coordinatePathWeightedLength_trans {X : Type*} [TopologicalSpace X]
    {δ : X → X → ℝ≥0∞}
    (hδ : ∀ p q r, δ p r ≤ δ p q + δ q r)
    (w : X → ℝ) {x y z : X} (γ : Path x y) (γ' : Path y z) :
    coordinatePathWeightedLength δ w (γ.trans γ') =
      coordinatePathWeightedLength δ w γ + coordinatePathWeightedLength δ w γ' := by
  unfold coordinatePathWeightedLength
  rw [← weightedLengthWith_add (δ := δ) (w := w) (P := (γ.trans γ').extend)
    hδ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)]
  have h1 : weightedLengthWith δ w (γ.trans γ').extend 0 (1 / 2) =
      weightedLengthWith δ w γ.extend 0 1 := by
    rw [weightedLengthWith_congr_path (Q := γ.extend ∘ fun t => 2 * t)
      (fun t ht => Path.extend_trans_of_le_half _ _ ht.2)]
    rw [weightedLengthWith_comp_monotoneOn δ w γ.extend (by norm_num) (by fun_prop)
      (fun s _ t _ hst => by linarith)]
    norm_num
  have h2 : weightedLengthWith δ w (γ.trans γ').extend (1 / 2) 1 =
      weightedLengthWith δ w γ'.extend 0 1 := by
    rw [weightedLengthWith_congr_path (Q := γ'.extend ∘ fun t => 2 * t - 1)
      (fun t ht => Path.extend_trans_of_half_le _ _ ht.1)]
    rw [weightedLengthWith_comp_monotoneOn δ w γ'.extend (by norm_num) (by fun_prop)
      (fun s _ t _ hst => by linarith)]
    norm_num
  rw [h1, h2]

theorem coordinatePathLength_refl {X : Type*} [TopologicalSpace X]
    (δ : X → X → ℝ≥0∞) (hself : ∀ x, δ x x = 0) (x : X) :
    coordinatePathLength δ (Path.refl x) = 0 := by
  unfold coordinatePathLength curveLengthWith
  simp [partitionSup, IccPartition.sum, hself]

theorem coordinatePathWeightedLength_refl {X : Type*} [TopologicalSpace X]
    (δ : X → X → ℝ≥0∞) (hself : ∀ x, δ x x = 0)
    (w : X → ℝ) (x : X) :
    coordinatePathWeightedLength δ w (Path.refl x) = 0 := by
  unfold coordinatePathWeightedLength
  apply le_antisymm _ bot_le
  exact (weightedLengthWith_le_ofReal_mul_curveLengthWith (M := w x)
    (fun s hs => by simp)).trans (by
      rw [show curveLengthWith δ (Path.refl x).extend 0 1 = 0 from
        coordinatePathLength_refl δ hself x, mul_zero]
      exact bot_le)

theorem coordinatePathLength_joinFinite
    {X : Type*} [TopologicalSpace X] (δ : X → X → ℝ≥0∞)
    (hself : ∀ x, δ x x = 0)
    (htri : ∀ p q r, δ p r ≤ δ p q + δ q r)
    (z : ℕ → X) (N : ℕ)
    (step : ∀ i : ℕ, i < N → Path (z i) (z (i + 1))) :
    ∀ i (hi : i ≤ N),
      coordinatePathLength δ (pathJoinFinite z N step i hi) =
        ∑ j ∈ Finset.range i,
          if hj : j < N then coordinatePathLength δ (step j hj) else 0 := by
  intro i
  induction i with
  | zero => intro hi; simp [pathJoinFinite, coordinatePathLength_refl δ hself]
  | succ i ih =>
      intro hi
      rw [pathJoinFinite, coordinatePathLength_trans htri, ih (by omega),
        Finset.sum_range_succ]
      simp [show i < N by omega]

theorem coordinatePathWeightedLength_joinFinite
    {X : Type*} [TopologicalSpace X] (δ : X → X → ℝ≥0∞)
    (hself : ∀ x, δ x x = 0)
    (htri : ∀ p q r, δ p r ≤ δ p q + δ q r)
    (w : X → ℝ) (z : ℕ → X) (N : ℕ)
    (step : ∀ i : ℕ, i < N → Path (z i) (z (i + 1))) :
    ∀ i (hi : i ≤ N),
      coordinatePathWeightedLength δ w (pathJoinFinite z N step i hi) =
        ∑ j ∈ Finset.range i,
          if hj : j < N then coordinatePathWeightedLength δ w (step j hj) else 0 := by
  intro i
  induction i with
  | zero => intro hi; simp [pathJoinFinite, coordinatePathWeightedLength_refl δ hself]
  | succ i ih =>
      intro hi
      rw [pathJoinFinite, coordinatePathWeightedLength_trans htri, ih (by omega),
        Finset.sum_range_succ]
      simp [show i < N by omega]

theorem pathJoinFinite_mem {X : Type*} [TopologicalSpace X]
    {S : Set X} (z : ℕ → X) (N : ℕ)
    (step : ∀ i : ℕ, i < N → Path (z i) (z (i + 1)))
    (h0 : z 0 ∈ S)
    (hstep : ∀ i (hi : i < N) (t : I), step i hi t ∈ S) :
    ∀ i (hi : i ≤ N) (t : I), pathJoinFinite z N step i hi t ∈ S := by
  intro i
  induction i with
  | zero => intro hi t; simpa [pathJoinFinite] using h0
  | succ i ih =>
      intro hi t
      simp only [pathJoinFinite, Path.trans_apply]
      split_ifs with ht
      · exact ih (by omega) _
      · exact hstep i (by omega) _

theorem weightedLengthWith_self {X : Type*} {δ : X → X → ℝ≥0∞}
    (hself : ∀ x, δ x x = 0) (w : X → ℝ) (P : ℝ → X) (a : ℝ) :
    weightedLengthWith δ w P a a = 0 := by
  apply le_antisymm _ bot_le
  have hlen : curveLengthWith δ P a a = 0 := by
    unfold curveLengthWith
    apply le_antisymm _ bot_le
    apply partitionSup_le
    intro p
    have ht (i : ℕ) (hi : i ≤ p.n) : p.t i = a := by
      exact le_antisymm (by simpa [p.last] using p.le_t hi le_rfl)
        (by simpa [p.zero] using p.le_t (Nat.zero_le i) hi)
    unfold IccPartition.sum
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro i hi
    rw [ht i (Finset.mem_range.1 hi).le,
      ht (i + 1) (Finset.mem_range.1 hi)]
    exact hself (P a)
  exact (weightedLengthWith_le_ofReal_mul_curveLengthWith
    (M := w (P a)) (fun s hs => by simpa using hs.1.antisymm hs.2 ▸ le_rfl)).trans
    (by rw [hlen, mul_zero]; exact le_rfl)

theorem sum_weightedLengthWith_eq
    {X : Type*} {δ : X → X → ℝ≥0∞}
    (hself : ∀ x, δ x x = 0)
    (htri : ∀ p q r, δ p r ≤ δ p q + δ q r)
    (w : X → ℝ) (P : ℝ → X) (t : ℕ → ℝ)
    (ht : Monotone t) (N : ℕ) :
    (∑ i ∈ Finset.range N, weightedLengthWith δ w P (t i) (t (i + 1))) =
      weightedLengthWith δ w P (t 0) (t N) := by
  induction N with
  | zero => simp [weightedLengthWith_self hself]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih]
      exact weightedLengthWith_add htri (ht (Nat.zero_le N))
        (ht (Nat.le_succ N))

end HigherDimLQGMetric
