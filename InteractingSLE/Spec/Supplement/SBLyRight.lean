/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBLxGen
import InteractingSLE.Spec.Supplement.GW1Later
import InteractingSLE.Spec.Supplement.GW1WalkExitD4
import InteractingSLE.Spec.Supplement.GW1WalkExitData
import InteractingSLE.Spec.Supplement.GW1WalkFinishTip
import InteractingSLE.Spec.Supplement.GW1Connector
import InteractingSLE.Spec.Supplement.GW1PieceRun
import InteractingSLE.Spec.Supplement.BW1DetPhys

/-!
# SB3's right additions from the left admissibility of the lower walk (ruling R95)

Packet PROVE-T14-SBLEAVES4. Ruling R95 gives SB3's induction statement the premise that the lower walk's thresholds
are right records. Its checkable form is the source's word condition on the negative real axis: every lower-walk left
cumulative weight there exceeds `−2`, i.e. `b t − (π/2)χ < λ` for `t < 0` (`GW1Conn.ambient_bounds` in the
counterflow setting; "All these old groups are admissible" in SB2(2)'s relative setting). Under it GW1's exit
classification works without a counterflow line:

* no piece of the lower walk ends at a new left record (`GW1W.ae_status_ne_left_right_walk`);
* every connector lies in `[0, ∞)` and every current point is `≥ 0` (`GW1Conn.rInv_run`);
* the launch chart sends the walk's current point to `0` (`GW1WalkExit.walk_recordGeometry`,
  `GW1WalkFinish.walkTipCoordinates_of_exteriorRecords`), so a piece of zero lifetime adds only that point.

Together: `WalkRightAdds` (input (I3) of SBLEAVES3's `SB3StageInputsStatement`) holds almost surely
(`ae_walkRightAdds_of_bound`). SB3: "At the end of an ordinary stage the lower endpoint `q` is a new right record.
Adding the next interval `[q, w]` preserves S1"; "If the lower seed is initially unavailable, its first real interval
lies on the real boundary to the right of the common seed."
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H Hbar)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Ly

open Lx Sec4 Exist.Staged Exist.StagedLaw
open PiecewiseConstantBoundaryData (leftLim)

/-- The left admissibility of the lower walk on the negative axis, in height form. -/
theorem height_lt_of_cumWeightLeft {κ : ℝ} (hκ : 0 < κ) {y : ℝ} (hy : -2 < cumWeightLeft κ y) :
    y < sleLambda κ := by
  have hl := sleLambda_pos hκ
  unfold cumWeightLeft at hy
  have h1 : -1 < -y / sleLambda κ := by linarith
  rw [lt_div_iff₀ hl] at h1
  linarith

/-- The root bound of the right walk from the bound on the negative axis. -/
theorem leftLim_zero_lt_of_bound {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hamb : ∀ t, t < 0 → t ∉ jumps → b t + -(Real.pi / 2) * chiC κ < sleLambda κ) :
    leftLim b 0 + -(Real.pi / 2) * chiC κ < sleLambda κ := by
  obtain ⟨t, -, ht0, htJ, hlt⟩ := Sec5.Aux22ChartE.exists_leftLim_eq hb (z := 0) (lo := -1) (by norm_num)
  rw [hlt]
  exact hamb t ht0 htJ

/-- A step past the end of the program changes nothing. -/
theorem run_succ_of_length_le {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} (spec : ExplSpec)
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {k : ℕ} (hk : spec.2.2.length ≤ k) :
    ExplState.run κ b jumps spec D (k + 1) = ExplState.run κ b jumps spec D k := by
  rw [run_succ, List.getElem?_eq_none hk]

/-- **Deterministic right additions of the right walk.** Without a left threshold, with the root bound and with the
launch charts sending the current point to `0` (the tip coordinates), a step that launches nothing or launches a piece
of zero lifetime adds only real points `≥ 0`. -/
theorem prefixPhysSet_succ_subset_of_rightRecords {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hroot : leftLim b 0 + -(Real.pi / 2) * chiC κ < sleLambda κ)
    (hno : ∀ k, (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) D (k + 1)).2.2.2.2.2.1 ≠
      stThr (some false))
    (htip : GW1WalkChain.WalkTipCoordinates κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) D)
    (k : ℕ)
    (hk : (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) D (k + 1)).2.2.2.1 k = none ∨
      (D k).2 = 0) :
    prefixPhysSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) D (k + 1) ⊆
      prefixPhysSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) D k ∪ ((↑) : ℝ → ℂ) '' Ici 0 := by
  set spec := boundaryWalkSpec b jumps (-(Real.pi / 2)) true with hspec
  set R := ExplState.run κ b jumps spec D with hR
  by_cases hlen : spec.2.2.length ≤ k
  · have e : R (k + 1) = R k := run_succ_of_length_le spec D hlen
    intro z hz
    left
    unfold prefixPhysSet at hz ⊢
    simp only [← hR] at hz ⊢
    rwa [e] at hz
  rw [not_le] at hlen
  -- the invariant: current points `≥ 0`, connectors in `[0, ∞)`
  have hinv : ∀ n, n ≤ spec.2.2.length → (∀ a ∈ (R n).2.1, a ⊆ Ici (0 : ℝ)) ∧ 0 ≤ stPt (R n) := by
    intro n hn
    obtain ⟨h0, h1⟩ := GW1Conn.rInv_run hroot D hno n hn
    rcases Nat.mod_two_eq_zero_or_one n with he | ho
    · exact ⟨(h0 he).1, (h0 he).2.1⟩
    · exact ⟨(h1 ho).1, (h1 ho).2.1⟩
  by_cases hl : (R (k + 1)).2.2.2.1 k = none
  · -- no launch: the pieces are unchanged and every connector is in `[0, ∞)`
    have hp : (R (k + 1)).1 = (R k).1 := GW1P.pieces_run_succ_of_noLaunch spec D hl
    have ha := (hinv (k + 1) hlen).1
    intro z hz
    unfold prefixPhysSet at hz ⊢
    simp only [← hR] at hz ⊢
    rw [hp] at hz
    rcases hz with (hz | hz) | hz
    · exact Or.inl (Or.inl (Or.inl hz))
    · exact Or.inl (Or.inl (Or.inr hz))
    · simp only [mem_iUnion, exists_prop] at hz
      obtain ⟨a, haR, hza⟩ := hz
      obtain ⟨x, hx, rfl⟩ := hza
      exact Or.inr ⟨x, ha a haR hx, rfl⟩
  · -- a launch of zero lifetime: the new piece is the current point
    have h0 : (D k).2 = 0 := by
      rcases hk with hk | hk
      · exact absurd hk hl
      · exact hk
    obtain ⟨⟨c, θ⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hl
    rw [BW1Det.prefixPhysSet_succ_of_launch hl]
    refine union_subset_union_right _ ?_
    rintro z ⟨t, ht, hz⟩
    have ht0 : t = 0 := by
      have : (t : ℝ≥0∞) ≤ 0 := by simpa [retOf, h0] using ht
      exact ENNReal.coe_eq_zero.1 (nonpos_iff_eq_zero.1 this)
    subst ht0
    obtain ⟨-, -, hc⟩ := eq_launch_of_launches spec D hcθ
    have htime : instrTime spec k = ⊤ := instrTime_boundaryWalk_of_launch hcθ
    have hz0 := (htip k c θ hcθ).1
    simp only [htime] at hz0
    rw [hc] at hz0
    have heq : z = (stPt (R k) : ℂ) := tendsto_nhds_unique hz hz0
    exact ⟨stPt (R k), (hinv k hlen.le).2, heq.symm⟩

/-- **Right additions of the lower walk, almost surely** (R95's premise in its checkable form). For a staged lower walk
with drivers regular at every sample, the bound `b t − (π/2)χ < λ` on the negative axis gives `WalkRightAdds`:
connectors and pieces of zero lifetime add only real points `≥ 0`. Theorem 1.3 supplies the regularity of the pieces
(`stagedPiecesRegular_of_regular`). -/
theorem ae_walkRightAdds_of_bound (h13 : Exist.Theorem13Statement.{u}) {κ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ}
    {jumps : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : IsStagedHistory κ b jumps P h (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)))
    (hreg : ∀ j ω, IsRegularDriver (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω))
    (hamb : ∀ t, t < 0 → t ∉ jumps → b t + -(Real.pi / 2) * chiC κ < sleLambda κ) :
    ∀ᵐ ω ∂P, WalkRightAdds κ b jumps E ω := by
  set spec := boundaryWalkSpec b jumps (-(Real.pi / 2)) true with hspec
  have hroot := leftLim_zero_lt_of_bound hb hamb
  have hR := stagedPiecesRegular_of_regular h13 hκ hb hS hreg
  filter_upwards [GW1W.ae_status_ne_left_right_walk hκ hb hh hS hreg hamb,
    GW1WalkExit.ae_walkStageData_right hκ hb hh hS hreg hamb, hR] with ω hno hst hr
  have hP : ∀ k c θ', (ExplState.run κ b jumps spec (fun j => E spec j ω) (k + 1)).2.2.2.1 k = some (c, θ') →
      GW1P.PieceRegular (E spec k ω).1 (min (instrTime spec k) (E spec k ω).2) := by
    intro k c θ' hl
    obtain ⟨hk, -, -⟩ := eq_launch_of_launches spec _ hl
    exact hr k θ' _ c hk hl
  have hgeo := GW1WalkExit.walk_recordGeometry hκ hb (fun j => E spec j ω) (fun j => hreg j ω) hst hP
  have htip := GW1WalkFinish.walkTipCoordinates_of_exteriorRecords (fun j => E spec j ω) hP hgeo.2
  intro k hk
  refine prefixPhysSet_succ_subset_of_rightRecords (fun j => E spec j ω) hroot (fun k => hno k) htip k ?_
  rcases hk with hk | hk
  · left
    unfold LowerLaunch lowerWalkState at hk
    exact not_not.1 hk
  · exact Or.inr hk

end InteractingSLE.Theorem14.SB.Ly
