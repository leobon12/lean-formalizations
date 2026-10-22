import HigherDimLQGContinuity.Core.Interfaces

/-!
# Cells and the covered-and-hit gate sandwich

The closed cells use the same coordinate convention as the lattice cubes of
`HigherDimLQGMetric.Topology.NonSepMesh`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open Set Metric
open HigherDimLFPP (Rd)

namespace HigherDimLQGContinuity

/-- The closed side-`μ` cell with lower lattice index `k` and origin `o`. -/
def cell {d : ℕ} (μ : ℝ) (o : Rd d) (k : Fin d → ℤ) : Set (Rd d) :=
  {x | ∀ i, o i + μ * (k i : ℝ) ≤ x i ∧
    x i ≤ o i + μ * ((k i : ℝ) + 1)}

/-- Centre of a cell. -/
irreducible_def cellCenter {d : ℕ} (μ : ℝ) (o : Rd d) (k : Fin d → ℤ) : Rd d :=
  WithLp.toLp 2 fun i => o i + μ * ((k i : ℝ) + 1 / 2)

/-- A finite family of cells covers `S`, and each selected cell meets `S`. -/
def CoveredHit {d : ℕ} (μ : ℝ) (o : Rd d) (Q : Finset (Fin d → ℤ))
    (S : Set (Rd d)) : Prop :=
  S ⊆ ⋃ k ∈ Q, cell μ o k ∧ ∀ k ∈ Q, (S ∩ cell μ o k).Nonempty

/-- Closed union of balls centred on the selected cells. -/
def ballUnion {d : ℕ} (μ : ℝ) (o : Rd d) (Q : Finset (Fin d → ℤ))
    (t : ℝ) : Set (Rd d) :=
  ⋃ k ∈ Q, closedBall (cellCenter μ o k) t

/-- Open core of the selected ball union. -/
def ballUnionOpen {d : ℕ} (μ : ℝ) (o : Rd d) (Q : Finset (Fin d → ℤ))
    (t : ℝ) : Set (Rd d) :=
  ⋃ k ∈ Q, ball (cellCenter μ o k) t

/-- The open balls form an open subset of the closed ball union. -/
theorem ballUnionOpen_subset_interior {d : ℕ} (μ : ℝ) (o : Rd d)
    (Q : Finset (Fin d → ℤ)) (t : ℝ) :
    ballUnionOpen μ o Q t ⊆ interior (ballUnion μ o Q t) := by
  have hOpen : IsOpen (ballUnionOpen μ o Q t) :=
    isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_ball
  calc
    ballUnionOpen μ o Q t = interior (ballUnionOpen μ o Q t) := hOpen.interior_eq.symm
    _ ⊆ interior (ballUnion μ o Q t) := by
      apply interior_mono
      intro x hx
      obtain ⟨k, hkQ, hxk⟩ := mem_iUnion₂.mp hx
      exact mem_iUnion₂.mpr ⟨k, hkQ, Metric.ball_subset_closedBall hxk⟩

private theorem cell_center_coord_le {d : ℕ} {μ : ℝ} (_hμ : 0 ≤ μ)
    (o : Rd d) (k : Fin d → ℤ) {x : Rd d} (hx : x ∈ cell μ o k)
    (i : Fin d) : |x i - (cellCenter μ o k) i| ≤ μ / 2 := by
  obtain ⟨hlo, hhi⟩ := hx i
  have hcenter : (cellCenter μ o k) i = o i + μ * (k i : ℝ) + μ / 2 := by
    simp only [cellCenter, PiLp.toLp_apply]
    ring
  rw [hcenter]
  apply abs_le.mpr
  constructor <;> linarith

/-- Euclidean distance bound from a uniform coordinate bound. -/
theorem q3_dist_le_sqrt_mul_of_coord_le {d : ℕ} (x y : Rd d) {r : ℝ}
    (hr : 0 ≤ r) (h : ∀ i : Fin d, |x i - y i| ≤ r) :
    dist x y ≤ Real.sqrt d * r := by
  rw [EuclideanSpace.dist_eq]
  have hsum : ∑ i : Fin d, dist (x i) (y i) ^ 2 ≤ (d : ℝ) * r ^ 2 := by
    calc
      _ ≤ ∑ _i : Fin d, r ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        rw [Real.dist_eq]
        exact pow_le_pow_left₀ (abs_nonneg _) (h i) 2
      _ = (d : ℝ) * r ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc
    _ ≤ Real.sqrt ((d : ℝ) * r ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt d * r := by
      rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq hr]

private theorem mul_half_eq (a b : ℝ) : a * (b / 2) = a / 2 * b := by ring

private theorem cell_center_dist_le {d : ℕ} {μ : ℝ} (hμ : 0 ≤ μ)
    (o : Rd d) (k : Fin d → ℤ) {x : Rd d} (hx : x ∈ cell μ o k) :
    dist x (cellCenter μ o k) ≤ Real.sqrt d / 2 * μ := by
  have h : dist x (cellCenter μ o k) ≤ Real.sqrt d * (μ / 2) :=
    q3_dist_le_sqrt_mul_of_coord_le x (cellCenter μ o k) (r := μ / 2) (by positivity)
      (cell_center_coord_le hμ o k hx)
  rw [mul_half_eq] at h
  exact h

/-- A cell lies in the closed ball of radius `√d μ/2` about its centre. -/
theorem cell_subset_closedBall {d : ℕ} {μ : ℝ} (hμ : 0 ≤ μ)
    (o : Rd d) (k : Fin d → ℤ) :
    cell μ o k ⊆ closedBall (cellCenter μ o k) (Real.sqrt d / 2 * μ) := by
  intro x hx
  rw [mem_closedBall]
  exact cell_center_dist_le hμ o k hx

/-- Equation (4.5): the covered-and-hit cell union sandwiches the compact target. -/
theorem gate_sandwich {d : ℕ} {μ t : ℝ} (hμ : 0 ≤ μ)
    (o : Rd d) (Q : Finset (Fin d → ℤ)) (S : Set (Rd d))
    (hS : IsCompact S) (hQ : CoveredHit μ o Q S)
    (ht : Real.sqrt d / 2 * μ < t) :
    Metric.cthickening (t - Real.sqrt d / 2 * μ) S ⊆ ballUnion μ o Q t ∧
    ballUnion μ o Q t ⊆ Metric.cthickening (t + Real.sqrt d / 2 * μ) S ∧
    S ⊆ ballUnionOpen μ o Q t ∧
    Metric.thickening (t - Real.sqrt d / 2 * μ) S ⊆
      interior (ballUnion μ o Q t) := by
  let c := Real.sqrt d / 2 * μ
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hrad : 0 ≤ t - c := by dsimp [c] at ht ⊢; linarith
  have hrep := hS.cthickening_eq_biUnion_closedBall hrad
  have hfirst : Metric.cthickening (t - c) S ⊆ ballUnion μ o Q t := by
    rw [hrep]
    intro x hx
    obtain ⟨y, hyS, hxy⟩ := mem_iUnion₂.mp hx
    obtain ⟨k, hkQ, hycell⟩ := mem_iUnion₂.mp (hQ.1 hyS)
    have hyc : dist y (cellCenter μ o k) ≤ c := cell_center_dist_le hμ o k hycell
    change x ∈ ⋃ k ∈ Q, closedBall (cellCenter μ o k) t
    apply mem_iUnion₂.mpr
    refine ⟨k, hkQ, ?_⟩
    rw [mem_closedBall]
    calc
      dist x (cellCenter μ o k) ≤ dist x y + dist y (cellCenter μ o k) := dist_triangle _ _ _
      _ ≤ (t - c) + c := add_le_add hxy hyc
      _ = t := by ring
  have hsecond : ballUnion μ o Q t ⊆ Metric.cthickening (t + c) S := by
    intro x hx
    obtain ⟨k, hkQ, hxc⟩ := mem_iUnion₂.mp hx
    obtain ⟨y, hyS, hycell⟩ := (hQ.2 k hkQ)
    have hyc : dist y (cellCenter μ o k) ≤ c := cell_center_dist_le hμ o k hycell
    apply Metric.mem_cthickening_of_dist_le x y (t + c) S hyS
    calc
      dist x y ≤ dist x (cellCenter μ o k) + dist (cellCenter μ o k) y := dist_triangle _ _ _
      _ ≤ t + c := add_le_add hxc (by simpa only [dist_comm] using hyc)
  have hopen : S ⊆ ballUnionOpen μ o Q t := by
    intro y hyS
    obtain ⟨k, hkQ, hycell⟩ := mem_iUnion₂.mp (hQ.1 hyS)
    apply mem_iUnion₂.mpr
    refine ⟨k, hkQ, ?_⟩
    rw [mem_ball]
    exact (cell_center_dist_le hμ o k hycell).trans_lt ht
  refine ⟨hfirst, hsecond, hopen, ?_⟩
  intro x hx
  rw [Metric.thickening_eq_biUnion_ball] at hx
  obtain ⟨y, hyS, hxy⟩ := mem_iUnion₂.mp hx
  obtain ⟨k, hkQ, hycell⟩ := mem_iUnion₂.mp (hQ.1 hyS)
  apply ballUnionOpen_subset_interior μ o Q t
  apply mem_iUnion₂.mpr
  refine ⟨k, hkQ, ?_⟩
  rw [mem_ball]
  have hyc : dist y (cellCenter μ o k) ≤ c := cell_center_dist_le hμ o k hycell
  calc
    dist x (cellCenter μ o k) ≤ dist x y + dist y (cellCenter μ o k) := dist_triangle _ _ _
    _ < (t - c) + c := add_lt_add_of_lt_of_le hxy hyc
    _ = t := by ring

end HigherDimLQGContinuity
