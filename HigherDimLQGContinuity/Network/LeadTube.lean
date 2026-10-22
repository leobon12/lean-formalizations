import HigherDimLQGContinuity.Network.ArcBalls

/-! # Endpoints of sampled polygonal leads -/

set_option autoImplicit false

noncomputable section

open Set Metric
open HigherDimLFPP (Rd)

namespace HigherDimLQGContinuity

theorem leadSamples_start {d Kl N : ℕ} (P : LeadCode d Kl N)
    (ν ω : ℝ) (hlast : 0 < P.last.val) :
    P.point ν 0 ∈ leadSamples P ν ω := by
  classical
  let j : Fin N := ⟨0, by have := P.last.isLt; omega⟩
  have hj : j.val < P.last.val := hlast
  have hstart : j.castSucc = (0 : Fin (N + 1)) := Fin.ext rfl
  unfold leadSamples
  apply Finset.mem_biUnion.mpr
  refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩, ?_⟩
  simpa only [hstart] using
    (segmentSamples_start (P.point ν j.castSucc) (P.point ν j.succ) ω)

theorem leadSamples_end {d Kl N : ℕ} (P : LeadCode d Kl N)
    (ν ω : ℝ) (hlast : 0 < P.last.val) :
    P.point ν P.last ∈ leadSamples P ν ω := by
  classical
  let j : Fin N := ⟨P.last.val - 1, by have := P.last.isLt; omega⟩
  have hj : j.val < P.last.val := by dsimp [j]; omega
  have hsucc : j.succ = P.last := by
    apply Fin.ext
    dsimp [j]
    omega
  unfold leadSamples
  apply Finset.mem_biUnion.mpr
  refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩, ?_⟩
  simpa only [hsucc] using
    (segmentSamples_end (P.point ν j.castSucc) (P.point ν j.succ) ω)

/-- A padded lead with a nonzero final index gives a connected open tube. -/
theorem connected_leadSampleBalls {d Kl N : ℕ} (P : LeadCode d Kl N)
    (ν : ℝ) {ω : ℝ} (hω : 0 < ω) (hlast : 0 < P.last.val) :
    IsConnected (⋃ x ∈ leadSamples P ν ω, ball x ω) := by
  classical
  let B : ℕ → Set (Rd d) := fun j =>
    if hj : j < N then
      ⋃ x ∈ segmentSamples
        (P.point ν (Fin.castSucc ⟨j, hj⟩))
        (P.point ν (Fin.succ ⟨j, hj⟩)) ω, ball x ω
    else ∅
  have hB (j : ℕ) (hj : j < P.last.val) :
      B j = ⋃ x ∈ segmentSamples
        (P.point ν (Fin.castSucc ⟨j, by have := P.last.isLt; omega⟩))
        (P.point ν (Fin.succ ⟨j, by have := P.last.isLt; omega⟩)) ω,
          ball x ω := by
    have hN : j < N := by have := P.last.isLt; omega
    simp only [B, dite_eq_left hN]
  have hconn : ∀ j < P.last.val, IsConnected (B j) := by
    intro j hj
    rw [hB j hj]
    exact connected_segmentSampleBalls _ _ hω
  have hmeet : ∀ j, j + 1 < P.last.val →
      (B j ∩ B (j + 1)).Nonempty := by
    intro j hj
    rw [hB j (by omega), hB (j + 1) hj]
    let m : Fin (N + 1) := ⟨j + 1, by have := P.last.isLt; omega⟩
    have hmEnd :
        (Fin.succ (⟨j, by have := P.last.isLt; omega⟩ : Fin N)) = m :=
      Fin.ext (by simp [m])
    have hmStart :
        (Fin.castSucc (⟨j + 1, by have := P.last.isLt; omega⟩ : Fin N)) = m :=
      Fin.ext (by simp [m])
    have hend : P.point ν m ∈ segmentSamples
        (P.point ν (Fin.castSucc ⟨j, by have := P.last.isLt; omega⟩))
        (P.point ν (Fin.succ ⟨j, by have := P.last.isLt; omega⟩)) ω := by
      simpa only [hmEnd] using
        (segmentSamples_end
          (P.point ν (Fin.castSucc ⟨j, by have := P.last.isLt; omega⟩))
          (P.point ν (Fin.succ ⟨j, by have := P.last.isLt; omega⟩)) ω)
    have hstart : P.point ν m ∈ segmentSamples
        (P.point ν (Fin.castSucc ⟨j + 1, by have := P.last.isLt; omega⟩))
        (P.point ν (Fin.succ ⟨j + 1, by have := P.last.isLt; omega⟩)) ω := by
      simpa only [hmStart] using
        (segmentSamples_start
          (P.point ν (Fin.castSucc ⟨j + 1, by have := P.last.isLt; omega⟩))
          (P.point ν (Fin.succ ⟨j + 1, by have := P.last.isLt; omega⟩)) ω)
    exact ⟨P.point ν m,
      mem_iUnion₂.mpr ⟨_, hend, mem_ball_self hω⟩,
      mem_iUnion₂.mpr ⟨_, hstart, mem_ball_self hω⟩⟩
  have hchain := connected_range_chain B P.last.val hlast hconn hmeet
  have hEq : (⋃ x ∈ leadSamples P ν ω, ball x ω) =
      ⋃ j ∈ Finset.range P.last.val, B j := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp hx
      obtain ⟨k, hk, hy⟩ := Finset.mem_biUnion.mp hy
      have hk' : k.val < P.last.val := (Finset.mem_filter.mp hk).2
      apply mem_iUnion₂.mpr
      refine ⟨k.val, Finset.mem_range.mpr hk', ?_⟩
      rw [hB k.val hk']
      exact mem_iUnion₂.mpr ⟨y, by simpa using hy, hxy⟩
    · intro hx
      obtain ⟨j, hj, hx⟩ := mem_iUnion₂.mp hx
      have hj' : j < P.last.val := Finset.mem_range.mp hj
      rw [hB j hj'] at hx
      obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp hx
      let k : Fin N := ⟨j, by have := P.last.isLt; omega⟩
      apply mem_iUnion₂.mpr
      refine ⟨y, ?_, hxy⟩
      apply Finset.mem_biUnion.mpr
      exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj'⟩,
        by simpa only [k] using hy⟩
  rw [hEq]
  exact hchain

end HigherDimLQGContinuity
