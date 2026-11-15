/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBLyTop
import InteractingSLE.Spec.Supplement.WalkLaterSeed
import InteractingSLE.Spec.Supplement.GW2aConnMove

/-!
# SB3's input (I5): the run fact `WalkLaunchPrefixNontrivialStatement` is proved

Packet PROVE-T14-SBLEAVES5. PROVE-T14-SBLEAVES4 reduced SB3's path input (I5) in the counterflow setting to the named
deterministic run fact `Ly.WalkLaunchPrefixNontrivialStatement`: at a launch `k ≥ 1` of a boundary walk the retained
physical set is not the root alone. It is proved here, at every sample.

* A boundary continuation that records a connector records a nontrivial real interval: the rightward branch moves to
  a point `x > pt` or to the end (`GW2aConn.rMove_rBranch`), the leftward branch mirrors it
  (`exists_nontrivial_arc_contStep`).
* In a boundary walk, every state at an arc mark (`GW1W.stArcM`) has recorded a nontrivial connector: the status
  `stArcM` is produced only by a connector move, and every other step keeps the arcs or leaves the status
  (`exists_nontrivial_arc_of_arcM`, induction over the run).
* A later launch starts at an arc mark (`WalkLaterSeed.laterLaunch_mark_seed`), so its retained set contains two
  distinct real points (`prefixPhysSet_ne_root_of_launch`), hence **`walkLaunchPrefixNontrivialStatement`**.
* The consumers without the run fact: `ae_isPrefixPath_of_cf'`, `sb3StageInputsCfStatement_of_meas'`,
  `sb3InductionRegStatement_of_meas'`, `sb3InductionRegStatement_of_thms'`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lz

open Exist.Staged Exist.StagedLaw

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {right : Bool}

/-- The connectors after a move along the boundary. -/
theorem arcs_moveAlong_eq (s : ExplState) (r : Bool) (x : ℝ) (m : Bool) :
    (ExplState.moveAlong s r x m).2.1 = s.2.1 ++ [if r then Icc (stPt s) x else Icc x (stPt s)] := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, θ', recR, recL⟩ := s
  rfl

/-- The connectors after a move to the end of the boundary. -/
theorem arcs_moveToEnd_eq (s : ExplState) (r : Bool) :
    (ExplState.moveToEnd s r).2.1 = s.2.1 ++ [if r then Ici (stPt s) else Iic (stPt s)] := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, θ', recR, recL⟩ := s
  rfl

/-- **A boundary continuation that records a connector records a nontrivial real interval.** -/
theorem exists_nontrivial_arc_contStep (s : ExplState) (pref : Bool)
    (hne : (ExplState.contStep κ b jumps s none pref).2.1 ≠ s.2.1) :
    ∃ a ∈ (ExplState.contStep κ b jumps s none pref).2.1, a.Nontrivial := by
  rcases GW2aConn.contStep_arc_cases s none pref hne with ⟨-, he⟩ | ⟨-, he⟩
  · rw [he]
    rcases GW2aConn.rMove_rBranch (κ := κ) (b := b) (jumps := jumps) s none with
      ⟨x, mk, hm, hx, -⟩ | ⟨hm, -⟩
    · rw [hm, arcs_moveAlong_eq]
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _),
        ⟨stPt s, ⟨le_rfl, hx.le⟩, x, ⟨hx.le, le_rfl⟩, hx.ne⟩⟩
    · rw [hm, arcs_moveToEnd_eq]
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _),
        ⟨stPt s, mem_Ici.2 le_rfl, stPt s + 1, mem_Ici.2 (by linarith), fun h => by linarith⟩⟩
  · rw [he]
    rcases GW2aConn.lMove_lBranch (κ := κ) (b := b) (jumps := jumps) s none with
      ⟨x, mk, hm, hx, -⟩ | ⟨hm, -⟩
    · rw [hm, arcs_moveAlong_eq]
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _),
        ⟨x, ⟨le_rfl, hx.le⟩, stPt s, ⟨hx.le, le_rfl⟩, hx.ne⟩⟩
    · rw [hm, arcs_moveToEnd_eq]
      exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _),
        ⟨stPt s, mem_Iic.2 le_rfl, stPt s - 1, mem_Iic.2 (by linarith), fun h => by linarith⟩⟩


/-- A move to the end is not at an arc mark. -/
theorem stStatus_moveToEnd_ne_arcM (s : ExplState) (r r' : Bool) :
    stStatus (ExplState.moveToEnd s r) ≠ GW1W.stArcM r' := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, θ', recR, recL⟩ := s
  intro h
  cases h

/-- A dead state is not at an arc mark. -/
theorem stStatus_setDead_ne_arcM (s : ExplState) (r' : Bool) : stStatus (setDead s) ≠ GW1W.stArcM r' := by
  intro h
  cases h

/-- **In a boundary walk, a state at an arc mark has recorded a nontrivial connector.** -/
theorem exists_nontrivial_arc_of_arcM (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    ∀ m, m ≤ (boundaryWalkSpec b jumps θ right).2.2.length → ∀ r,
      stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D m) = GW1W.stArcM r →
      ∃ a ∈ (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D m).2.1, a.Nontrivial := by
  intro m
  induction m with
  | zero => intro _ r hr; cases hr
  | succ m ih =>
    intro hm r hr
    set R := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D with hRdef
    rcases Nat.mod_two_eq_zero_or_one m with hev | hodd
    · have hf : R (m + 1) = ExplState.flowStep κ b false (R m) m (D m) θ ⊤ :=
        GW1W.run_succ_walk_flow (by omega) hev
      rcases GW1W.flowStep_false_cases (κ := κ) (b := b) (R m) m (D m) θ ⊤ with he | he
      · rw [hf, he] at hr ⊢
        exact ih (by omega) r hr
      · rw [hf, he] at hr
        exact (WalkSeedFinite.launch_top_ne_arcM _ _ _ _ _ hr).elim
    · have hc : R (m + 1) = ExplState.contStep κ b jumps (R m) none right :=
        GW1W.run_succ_walk_cont (by omega) hodd
      rw [hc] at hr ⊢
      by_cases hne : (ExplState.contStep κ b jumps (R m) none right).2.1 = (R m).2.1
      · rcases contStep_cases (κ := κ) (b := b) (jumps := jumps) (R m) none right with
          he | he | ⟨r', x, mk, he⟩ | ⟨r', he⟩
        · rw [he] at hr ⊢
          exact ih (by omega) r hr
        · rw [he] at hr
          exact (stStatus_setDead_ne_arcM _ _ hr).elim
        · rw [he, arcs_moveAlong_eq] at hne
          exact absurd (congrArg List.length hne) (by simp)
        · rw [he] at hr
          exact (stStatus_moveToEnd_ne_arcM _ _ _ hr).elim
      · exact exists_nontrivial_arc_contStep _ _ hne

/-- **At a later launch of a boundary walk the retained physical set is not the root alone.** -/
theorem prefixPhysSet_ne_root_of_launch (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {k : ℕ} (hk0 : 0 < k)
    (hk : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (k + 1)).2.2.2.1 k ≠ none) :
    prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ right) D k ≠
      {(((boundaryWalkSpec b jumps θ right).1 : ℝ) : ℂ)} := by
  obtain ⟨⟨r, hs, -⟩, -⟩ := WalkLaterSeed.laterLaunch_mark_seed D hk0 hk
  obtain ⟨a, ha, x, hx, y, hy, hxy⟩ :=
    exists_nontrivial_arc_of_arcM D k (GW1W.even_of_launches_walk hk).2.le r hs
  intro hP
  have hsub : ∀ z ∈ a, ((z : ℝ) : ℂ) ∈ prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ right) D k :=
    fun z hz => Or.inr (mem_iUnion₂.2 ⟨a, ha, z, hz, rfl⟩)
  have hx' := hsub x hx
  have hy' := hsub y hy
  rw [hP, mem_singleton_iff] at hx' hy'
  exact hxy (Complex.ofReal_injective (hx'.trans hy'.symm))

/-- **The run fact `WalkLaunchPrefixNontrivialStatement` holds** (deterministically, at every sample). -/
theorem walkLaunchPrefixNontrivialStatement : Ly.WalkLaunchPrefixNontrivialStatement.{u} := by
  intro κ _ _ b jumps _ Ω _ _ P _ h _ W' ζ' _ _ E _ _ right
  exact Filter.Eventually.of_forall fun ω k hk hl =>
    prefixPhysSet_ne_root_of_launch (fun j => E (GW1Z.walkSpec b jumps right) j ω) hk hl


/-! ### The consumers without the run fact -/

/-- **SB3's input (I5) in the counterflow setting** without the run fact (`Ly.ae_isPrefixPath_of_cf` with
`walkLaunchPrefixNontrivialStatement`). -/
theorem ae_isPrefixPath_of_cf' (hSimple : GW1Z.GW1PieceSimpleStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h13₀ : Exist.Theorem13Statement.{0})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      IsStagedHistory κ b jumps P h spec (E spec))
    (hR : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      StagedPiecesRegular κ b jumps P spec (E spec))
    (hreg : ∀ spec j ω, IsRegularDriver (E spec j ω)) {u : ℝ} (hu : u ≤ 0) :
    ∀ k, 1 ≤ k → ∀ᵐ ω ∂P, Lx.LowerLaunch κ b jumps E k ω →
      ∃ p : ℝ → ℂ, Lx.IsPrefixPath p u (lowerPrefix κ b jumps E k u ω) :=
  Ly.ae_isPrefixPath_of_cf hSimple h13 h13₀ walkLaunchPrefixNontrivialStatement hκ hκ4 hb hh hcf hζ' hE hR hreg hu

/-- The stage inputs in the counterflow setting from GW1's piece simplicity, Theorem 1.3 and the two measurability
inputs (the run fact is proved). -/
theorem sb3StageInputsCfStatement_of_meas' (hSimple : GW1Z.GW1PieceSimpleStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h13₀ : Exist.Theorem13Statement.{0})
    (hM : Ly.SB3StageMeasCfStatement.{u}) : Ly.SB3StageInputsCfStatement.{u} :=
  Ly.sb3StageInputsCfStatement_of_meas hSimple h13 h13₀ walkLaunchPrefixNontrivialStatement hM

/-- SB3's induction in the counterflow setting from SB2(1) in that setting, SB1, S6, Theorem 1.3, GW1's piece
simplicity and the two measurability inputs (the run fact is proved). -/
theorem sb3InductionRegStatement_of_meas' (hSB2 : Ly.SB2UpperLaunchEntryLCfStatement.{u})
    (hSB1 : SB1Statement.{u}) (hS6 : S6Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h13₀ : Exist.Theorem13Statement.{0}) (hSimple : GW1Z.GW1PieceSimpleStatement.{u})
    (hM : Ly.SB3StageMeasCfStatement.{u}) : SB3InductionRegStatement.{u} :=
  Ly.sb3InductionRegStatement_of_meas hSB2 hSB1 hS6 h13 h13₀ hSimple walkLaunchPrefixNontrivialStatement hM

/-- **SB3's induction in Theorem 1.4's counterflow setting** (`SB.SB3InductionRegStatement`, R96) from SB2(1) in that
setting, Theorems 1.2–1.3, the small-gap fibre cover (SB1/S6) and the measurability inputs (I2), (I2′): the run fact
of `Ly.sb3InductionRegStatement_of_thms` is proved. -/
theorem sb3InductionRegStatement_of_thms' (hSB2 : Ly.SB2UpperLaunchEntryLCfStatement.{u})
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hDy : Sec5.Aux61Act.DyActFibreCoverOn.{u}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin)
    (hDy₀ : Sec5.Aux61Act.DyActFibreCoverOn.{0}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin)
    (hM : Ly.SB3StageMeasCfStatement.{u}) : SB3InductionRegStatement.{u} :=
  Ly.sb3InductionRegStatement_of_thms hSB2 h12 h13 h12₀ h13₀ hDy hDy₀ walkLaunchPrefixNontrivialStatement hM

end InteractingSLE.Theorem14.SB.Lz
