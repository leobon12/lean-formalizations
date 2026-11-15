/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1ActiveRun
import InteractingSLE.Spec.Supplement.GW1

/-!
# A launch at a flow stage `ℓ + 2` of the boundary walk follows a launch at `ℓ`

Packet PROVE-SB2-CANON, round 9 (D86: the coverage of (P1)'s induction step). **`launch_of_launch_add_two`**: for
every driver sequence, if the boundary walk launches its flow instruction `ℓ + 2`, it launched instruction `ℓ`.
Stage `0` always launches (`GW1.launches_run_one_boundaryWalkSpec`). For `ℓ ≥ 2`, a flow step that launches nothing
leaves the state unchanged (`GW1W.flowStep_eq_self_of_noLaunch`). The state at `ℓ` comes out of the connector `ℓ - 1`,
so its status is an arc mark, done or dead (`GW1W.status_contStep`), and the connector `ℓ + 1` leaves it unchanged
(`GW1W.contStep_eq_self`). For those statuses, whether the flow step launches does not depend on the index or the
driver (**`flowStep_noLaunch_of_noLaunch`**).

No probabilistic input; R48 is vacuous here.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB.Cz

open Exist Exist.Staged Exist.StagedLaw

/-- **At an arc mark, done or dead status, whether a flow step launches does not depend on its index or driver.** -/
theorem flowStep_noLaunch_of_noLaunch {κ : ℝ} {b : ℝ → ℝ} (s : ExplState)
    (hs : (∃ r, stStatus s = GW1W.stArcM r) ∨ stStatus s = GW1Conn.stDone ∨ stStatus s = GW1Conn.stDead)
    {k k' : ℕ} {D D' : (ℝ≥0 → ℝ) × ℝ≥0∞} {θ : ℝ} {t : ℝ≥0∞} (hk' : s.2.2.2.1 k' = none)
    (hn : (ExplState.flowStep κ b false s k D θ t).2.2.2.1 k = none) :
    (ExplState.flowStep κ b false s k' D' θ t).2.2.2.1 k' = none := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL⟩ := s
  rcases hs with ⟨r, h⟩ | h | h <;> change status = _ at h <;> subst h
  · unfold ExplState.flowStep at hn ⊢
    dsimp only at hn ⊢
    simp only [Bool.false_eq_true, ↓reduceIte] at hn ⊢
    split_ifs at hn ⊢ with hadm
    · rw [launches_launch, Function.update_self] at hn
      exact absurd hn (by simp)
    · exact hk'
  · exact hk'
  · exact hk'

/-- **A launch at the flow stage `ℓ + 2` of the boundary walk follows a launch at `ℓ`** (every driver sequence). -/
theorem launch_of_launch_add_two {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {right : Bool}
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {ℓ : ℕ}
    (h2 : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (ℓ + 3)).2.2.2.1 (ℓ + 2) ≠ none) :
    (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (ℓ + 1)).2.2.2.1 ℓ ≠ none := by
  classical
  obtain ⟨hev2, hlen2⟩ := GW1W.even_of_launches_walk h2
  rcases Nat.eq_zero_or_pos ℓ with h0 | hpos
  · subst h0
    rw [GW1.launches_run_one_boundaryWalkSpec]
    exact Option.some_ne_none _
  obtain ⟨m, rfl⟩ : ∃ m, ℓ = m + 1 := ⟨ℓ - 1, by omega⟩
  intro hn
  set R := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D with hR
  have hf : R (m + 1 + 1) = ExplState.flowStep κ b false (R (m + 1)) (m + 1) (D (m + 1)) θ ⊤ :=
    GW1W.run_succ_walk_flow (by omega) (by omega)
  rw [hf] at hn
  have hs1 : R (m + 1 + 1) = R (m + 1) := by
    rw [hf]
    exact GW1W.flowStep_eq_self_of_noLaunch _ _ _ _ _ hn
  have hc0 : R (m + 1) = ExplState.contStep κ b jumps (R m) none right :=
    GW1W.run_succ_walk_cont (by omega) (by omega)
  have hst := GW1W.status_contStep (κ := κ) (b := b) (jumps := jumps) (R m) right
  rw [← hc0] at hst
  have hc2 : R (m + 1 + 2) = ExplState.contStep κ b jumps (R (m + 1 + 1)) none right :=
    GW1W.run_succ_walk_cont (by omega) (by omega)
  have hs2 : R (m + 1 + 2) = R (m + 1) := by
    rw [hc2, hs1, GW1W.contStep_eq_self _ _ hst]
  have hf2 : R (m + 1 + 3) =
      ExplState.flowStep κ b false (R (m + 1 + 2)) (m + 1 + 2) (D (m + 1 + 2)) θ ⊤ :=
    GW1W.run_succ_walk_flow (by omega) (by omega)
  apply h2
  rw [hf2, hs2]
  exact flowStep_noLaunch_of_noLaunch _ hst (launches_run_of_le _ _ (by omega)) hn

end InteractingSLE.Theorem14.SB.Cz
