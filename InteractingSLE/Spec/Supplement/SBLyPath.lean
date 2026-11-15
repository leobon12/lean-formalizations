/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBLyGen
import InteractingSLE.Spec.Supplement.WalkIntRunChronRun
import InteractingSLE.Spec.Supplement.WalkIntRunChronSimple
import InteractingSLE.Spec.Supplement.GW1WalkExitParam
import InteractingSLE.Spec.Supplement.GW1WalkExitStatement
import InteractingSLE.Spec.Supplement.GW1PieceSimpleProof
import InteractingSLE.Spec.Supplement.SBLwPath

/-!
# SB3's stage input (I5) in the counterflow setting: retained prefixes are paths

Packet PROVE-T14-SBLEAVES4. Input (I5) of SB3's induction asks that every retained prefix at a launch `k ≥ 1` be the
image of a path with finite fibres from the upper seed `u` (`Lx.IsPrefixPath`). In Theorem 1.4's counterflow setting
(ruling R96) GW1's landed results give it:

* GW1's piece simplicity (`GW1Z.GW1PieceSimpleStatement`), the tip coordinates and the connector clearance (from GW1's
  exit classification and D.4 geometry, Theorem 1.3) make every live state a chronological arc history
  (`WalkIntRunChron.stateRepresented_run`);
* an arc history is a simple path from the root (`Lw.exists_path_of_arcHistory`); for `u < 0` the real bridge `[u, 0]`
  is prepended (`Lw.exists_bridge_path`); for `u = 0` the path itself works.

The one case not covered is a retained prefix equal to the root alone with `u = 0`; it cannot occur at a launch
`k ≥ 1` (the preceding connector moved to a new mark), and is kept as the deterministic named run fact
`WalkLaunchPrefixNontrivialStatement`.

* `exists_isPrefixPath_segment`, `exists_isPrefixPath_of_arcHistory` (deterministic);
* `ae_isPrefixPath_of_cf` (almost surely, counterflow setting);
* `SB3StageMeasCfStatement` (the two null-measurability inputs (I2), (I2′)), `sb3StageInputsCfStatement_of_meas`,
  `sb3InductionRegStatement_of_meas`.
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

open Lx Lv Lw Sec4 Exist.Staged Exist.StagedLaw GW1WalkChain GW1Bookkeep

/-- The real segment from `u < 0` to `0` is a prefix path. -/
theorem exists_isPrefixPath_segment {u : ℝ} (hu : u < 0) :
    ∃ p : ℝ → ℂ, IsPrefixPath p u (((↑) : ℝ → ℂ) '' Icc u 0) := by
  refine ⟨fun s => ((u * (1 - s) : ℝ) : ℂ), by fun_prop, by simp, fun z => ?_, fun s _ => by simp, ?_⟩
  · refine finite_fibre_of_injOn (fun s _ t _ hst => ?_) z
    have h := Complex.ofReal_injective hst
    have := mul_left_cancel₀ hu.ne h
    linarith
  · ext z
    simp only [mem_image, mem_Icc]
    constructor
    · rintro ⟨s, ⟨hs0, hs1⟩, rfl⟩
      exact ⟨u * (1 - s), ⟨by nlinarith, by nlinarith⟩, rfl⟩
    · rintro ⟨y, ⟨hy0, hy1⟩, rfl⟩
      refine ⟨1 - y / u, ⟨?_, ?_⟩, ?_⟩
      · have : y / u ≤ 1 := by rw [div_le_one_of_neg hu]; exact hy0
        linarith
      · have : 0 ≤ y / u := div_nonneg_of_nonpos hy1 hu.le
        linarith
      · have hu0 : u ≠ 0 := hu.ne
        congr 1
        rw [sub_sub_cancel]
        field_simp

/-- **An arc history from the root `0` gives a prefix path from the upper seed `u ≤ 0`** for its union with the bridge
`[u, 0]`, unless `u = 0` and the history is the root alone. -/
theorem exists_isPrefixPath_of_arcHistory {A : Set ℂ} {q : ℂ} (h : ArcHistory ((0 : ℝ) : ℂ) A q) {u : ℝ}
    (hu : u ≤ 0) (hnt : u = 0 → A ≠ {((0 : ℝ) : ℂ)}) :
    ∃ p : ℝ → ℂ, IsPrefixPath p u (A ∪ ((↑) : ℝ → ℂ) '' Icc u 0) := by
  rcases exists_path_of_arcHistory h with ⟨hA, -⟩ | ⟨p₀, hc, hinj, h0, -, himg, hH⟩
  · rcases hu.lt_or_eq with hu' | rfl
    · rw [hA, union_eq_right.2 (singleton_subset_iff.2
        (show ((0 : ℝ) : ℂ) ∈ ((↑) : ℝ → ℂ) '' Icc u 0 from ⟨0, ⟨hu'.le, le_rfl⟩, rfl⟩))]
      exact exists_isPrefixPath_segment hu'
    · exact absurd hA (hnt rfl)
  · have hH' : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p₀ s).im := by
      intro s hs
      by_cases hps : p₀ s = ((0 : ℝ) : ℂ)
      · rw [hps]; simp
      · exact hH s hs hps
    rcases hu.lt_or_eq with hu' | rfl
    · obtain ⟨p, hpc, hp0, hpf, hpimg, hpH⟩ :=
        exists_bridge_path hu' hc hinj (by rw [h0]; simp) himg hH'
      exact ⟨p, hpc, hp0, hpf, hpH, by rw [hpimg, union_comm]⟩
    · refine ⟨p₀, hc, h0, finite_fibre_of_injOn hinj, hH', ?_⟩
      have h0A : ((0 : ℝ) : ℂ) ∈ A := himg ▸ ⟨0, ⟨le_rfl, zero_le_one⟩, h0⟩
      rw [Icc_self, image_singleton, union_eq_left.2 (singleton_subset_iff.2 h0A), himg]

/-- **Named deterministic run fact**: at a launch `k ≥ 1` of a boundary walk the retained physical set is not the root
alone (the connector before the launch moved to a new original mark, `WalkLaterSeed.laterLaunch_mark_seed`,
`WalkMarkSeedRestart.restart_move_of_last_launch`). Stated almost surely in GW1's run setting. -/
def WalkLaunchPrefixNontrivialStatement : Prop :=
  GW1ParamEvery.WalkRunStatement.{u} (fun κ b jumps spec D =>
    ∀ k, 1 ≤ k → (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k ≠ none →
      prefixPhysSet κ b jumps spec D k ≠ {((spec.1 : ℝ) : ℂ)})

/-- **SB3's input (I5) in the counterflow setting**, almost surely: at every launch `k ≥ 1` of the lower walk the
retained prefix (with the bridge `[u, 0]`) is the image of a path with finite fibres from `u`. -/
theorem ae_isPrefixPath_of_cf (hSimple : GW1Z.GW1PieceSimpleStatement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h13₀ : Exist.Theorem13Statement.{0}) (hNT : WalkLaunchPrefixNontrivialStatement.{u})
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
    ∀ k, 1 ≤ k → ∀ᵐ ω ∂P, LowerLaunch κ b jumps E k ω →
      ∃ p : ℝ → ℂ, IsPrefixPath p u (lowerPrefix κ b jumps E k u ω) := by
  have hD4 := GW1WalkExit.walkD4GeometryStatement_of_theorem13 h13 h13₀
  have hTip := GW1WalkFinish.walkTipCoordinatesStatement_of_d4 h13 hD4
  have hClear := GW1WalkFinish.walkConnectorClearanceStatement_of_d4_and_exit
    (GW1WalkExit.walkExitClassificationStatement_of_theorem13 h13₀) hD4
  intro k hk
  filter_upwards [hSimple κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg hR true,
    hTip κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg true,
    hClear κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg true,
    hNT κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg true] with ω hs ht hc hnt hl
  have hrep := WalkIntRunChron.stateRepresented_run
    (fun j c θ' hlj hseed => WalkIntRunChron.pieceSimpleAt_at_launch _ _ hs ht hlj hseed) hc k
  rcases hrep with ⟨hdone, -⟩ | ⟨-, harc⟩
  · exact absurd (launches_eq_none_of_done _ _ hdone le_rfl) hl
  · exact exists_isPrefixPath_of_arcHistory harc hu fun _ => hnt k hk hl

/-- **The two null-measurability inputs (I2), (I2′) of SB3's induction, counterflow setting** (named open input;
supplement p. 577: S1 events are universally measurable; route: the analytic-set lemmas of
`Foundations/Measure/AnalyticUniversal`). -/
def SB3StageMeasCfStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
      (∀ spec j ω, IsRegularDriver (E spec j ω)) →
    ∀ u ψ : ℝ, u ≤ 0 → -(Real.pi / 2) < ψ →
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightRight κ (b x + ψ * chiC κ) ∨
        κ / 2 - 2 ≤ cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
    ∀ (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞), IsFlowLine κ b jumps u ψ P h η ζ → (∀ᵐ ω ∂P, 0 < ζ ω) →
      (∀ k, NullMeasurableSet {ω | SB3StageClaim κ b jumps E k u η ζ ω} P) ∧
      ∀ k, NullMeasurableSet {ω | SB3TruncClaim κ b jumps E k u η ζ ω} P

/-- **The stage inputs in the counterflow setting** from GW1's piece simplicity, Theorem 1.3, the run fact
`WalkLaunchPrefixNontrivialStatement` and the two measurability inputs: (I5) is `ae_isPrefixPath_of_cf`. -/
theorem sb3StageInputsCfStatement_of_meas (hSimple : GW1Z.GW1PieceSimpleStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h13₀ : Exist.Theorem13Statement.{0})
    (hNT : WalkLaunchPrefixNontrivialStatement.{u}) (hM : SB3StageMeasCfStatement.{u}) :
    SB3StageInputsCfStatement.{u} :=
  fun κ hκ hκ4 b jumps hb _ _ _ P _ h hh W' ζ' hcf hζ' E hE hR hreg u ψ hu hψ hL hH η ζ hη hζ =>
    ⟨ae_isPrefixPath_of_cf hSimple h13 h13₀ hNT hκ hκ4 hb hh hcf hζ' hE hR hreg hu,
      hM κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hR hreg u ψ hu hψ hL hH η ζ hη hζ⟩

/-- **SB3's induction in the counterflow setting** (`SB.SB3InductionRegStatement`) from SB2(1) in that setting, SB1,
S6, Theorem 1.3, GW1's piece simplicity, the run fact and the two measurability inputs. -/
theorem sb3InductionRegStatement_of_meas (hSB2 : SB2UpperLaunchEntryLCfStatement.{u}) (hSB1 : SB1Statement.{u})
    (hS6 : S6Statement.{u}) (h13 : Exist.Theorem13Statement.{u}) (h13₀ : Exist.Theorem13Statement.{0})
    (hSimple : GW1Z.GW1PieceSimpleStatement.{u}) (hNT : WalkLaunchPrefixNontrivialStatement.{u})
    (hM : SB3StageMeasCfStatement.{u}) : SB3InductionRegStatement.{u} :=
  sb3InductionRegStatement_of_cfInputs hSB2 hSB1 hS6 h13 h13₀
    (sb3StageInputsCfStatement_of_meas hSimple h13 h13₀ hNT hM)

end InteractingSLE.Theorem14.SB.Ly
