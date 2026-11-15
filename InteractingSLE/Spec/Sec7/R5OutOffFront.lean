/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5OutCert
import InteractingSLE.Spec.Sec7.R5OutTail

/-! # R97(a): the forbidden frontier is in every sufficiently late reference hull -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter Topology Metric
open QuantumZipper (H fwdHull)
open InteractingSLE.WangWu (negInv)
open scoped NNReal ENNReal
namespace InteractingSLE.Sec7.R5Out
open Sec6 PocketJordan WangWu Lemma71I R7StopIn R5Ref PocketStopSide

/-- The two certified-frontier attachments added to the finite physical exception set. -/
def certExc (M N : ℝ≥0 → ℂ) (η : ℝ → ℂ) (T : ℝ) : Set ℂ :=
  {certWall M (lastVisit (fun t => η '' Icc 0 t) (certWall M) T),
   certWall N (lastVisit (fun t => η '' Icc 0 t) (certWall N) T)}

theorem finite_certExc (M N : ℝ≥0 → ℂ) (η : ℝ → ℂ) (T : ℝ) : (certExc M N η T).Finite := by
  unfold certExc
  exact Set.toFinite _

/-- If the terminal trace avoids a ball, every point of the prefix in that ball
is already in the old hull. -/
theorem mem_old_hull_of_trace_near {W : ℝ → ℝ} {η : ℝ → ℂ}
    (hη : IsLoewnerTrace W η) {s T : ℝ} (hs : 0 ≤ s) {p z : ℂ} {r : ℝ}
    (hTail : Disjoint (η '' Icc s T) (closedBall p r))
    (hz : z ∈ η '' Icc 0 T) (hzB : z ∈ closedBall p r) (hzH : z ∈ H) : z ∈ fwdHull W s := by
  obtain ⟨t, ht, htz⟩ := hz
  have hts : t ≤ s := le_of_not_gt fun hst =>
    disjoint_left.1 hTail ⟨t, ⟨hst.le, ht.2⟩, htz⟩ hzB
  exact mem_fwdHull_of_mem_trace hη hs hzH ⟨t, ⟨ht.1, hts⟩, htz⟩

/-- A locally visited frontier is in every sufficiently late old hull, provided
the landing is not the current tip. -/
theorem exists_old_frontier_hull_interval {W : ℝ → ℝ} {η : ℝ → ℂ}
    (hη : IsLoewnerTrace W η) {F : Set ℂ} {T : ℝ} (hT : 0 < T) {p : ℂ}
    (hp : p ≠ η T) (hfr : ∃ r > 0, frontier F ∩ ball p r ∩ H ⊆ η '' Icc 0 T) :
    ∃ a : ℝ, 0 ≤ a ∧ a < T ∧ ∃ r > 0,
      ∀ s : ℝ, a ≤ s → frontier F ∩ ball p r ∩ H ⊆ fwdHull W s := by
  obtain ⟨r₁, hr₁, hfr₁⟩ := hfr
  obtain ⟨s, h0s, hsT, ρ, hρ, hTail⟩ := exists_rat_terminal_trace_avoids hη.2.1 (show (0 : ℝ) ≤ 0 from le_rfl) hT hp
  refine ⟨s, h0s.le, hsT, min r₁ ρ, lt_min hr₁ hρ, ?_⟩
  intro t hst z hz
  have hzR := hfr₁ ⟨⟨hz.1.1, ball_subset_ball (min_le_left _ _) hz.1.2⟩, hz.2⟩
  have hzK := mem_old_hull_of_trace_near hη h0s.le hTail hzR
    (ball_subset_closedBall (ball_subset_ball (min_le_right _ _) hz.1.2)) hz.2
  exact fwdHull_mono hst hzK

/-- R97(a), right certified frontier: adjoining its attachment to the exceptions
makes its local frontier belong to all sufficiently late old reference hulls. -/
theorem exists_old_forbidden_right_frontier_hull {W : ℝ → ℝ} {η : ℝ → ℂ}
    (hη : IsLoewnerTrace W η) {M : ℝ≥0 → ℂ} (hM : IsSimpleProper M)
    (hrev : IsWallReverseVisit M η) {T : ℝ} (hT : 0 < T) {p : ℂ}
    (hpR : p ∈ η '' Icc 0 T) (hp : p ≠ η T)
    (hAttach : p ≠ certWall M (lastVisit (fun t => η '' Icc 0 t) (certWall M) T)) :
    ∃ a : ℝ, 0 ≤ a ∧ a < T ∧ ∃ r > 0,
      ∀ s : ℝ, a ≤ s → frontier (negInv '' rightSideOf (range M)) ∩ ball p r ∩ H ⊆ fwdHull W s :=
  exists_old_frontier_hull_interval hη hT hp
    (exists_ball_forbidden_right_frontier_subset_trace hM hη.2.1 hη.1 hrev hT.le hpR hAttach)

/-- R97(a), left certified frontier. -/
theorem exists_old_forbidden_left_frontier_hull {W : ℝ → ℝ} {η : ℝ → ℂ}
    (hη : IsLoewnerTrace W η) {M : ℝ≥0 → ℂ} (hM : IsSimpleProper M)
    (hrev : IsWallReverseVisit M η) {T : ℝ} (hT : 0 < T) {p : ℂ}
    (hpR : p ∈ η '' Icc 0 T) (hp : p ≠ η T)
    (hAttach : p ≠ certWall M (lastVisit (fun t => η '' Icc 0 t) (certWall M) T)) :
    ∃ a : ℝ, 0 ≤ a ∧ a < T ∧ ∃ r > 0,
      ∀ s : ℝ, a ≤ s → frontier (negInv '' leftSideOf (range M)) ∩ ball p r ∩ H ⊆ fwdHull W s :=
  exists_old_frontier_hull_interval hη hT hp
    (exists_ball_forbidden_left_frontier_subset_trace hM hη.2.1 hη.1 hrev hT.le hpR hAttach)

end InteractingSLE.Sec7.R5Out
