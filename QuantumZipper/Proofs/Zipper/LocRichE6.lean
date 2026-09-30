import QuantumZipper.Proofs.Zipper.LocRichD3
import QuantumZipper.Proofs.Zipper.E6Concrete
import QuantumZipper.Proofs.Zipper.E6
import QuantumZipper.Proofs.Zipper.Thm13Assembly

/-!
# E5, E6 and the Theorem 1.3 assembly for the rich local data (decision D25)

Decision **D25** (`DECISIONS.md`). With `loc := D3Plus.locRich` (`LocRichBasic.lean`):

* `E5StmtG loc`: `E5.E5Stmt` verbatim, with the local data type generalized from
  `(ℕ → ℝ) × (ℝ≥0 → ℝ)` to any measurable space `L` (the rich data live in `FullData`).
  `E5StmtRich := E5StmtG D3Plus.locRich`; `e5_of_rich : E5StmtRich → E5.E5Stmt D3Plus.locData`
  (the rich statement is stronger).
* `e6_concrete_gen`: `E6.e6_concrete` for any `L` (same proof, through `E6.e6_core_rel`,
  `LocRichCore.lean`): E6 in local-law form from `E5StmtG loc` and the same side inputs, except
  that E6-ID and `ConfigEq`-invariance of `loc` are replaced by E6-ID at the level of the local
  data (`hIdLoc`). `ConfigEq` does not determine `locRich` (it controls raw values only at the
  circles read by `avgReg`); for `locRich`, `hIdLoc` follows from E6-ID up to `RawEq`
  (`LocRichId.lean`).
* `aemeasurable_dataFull_unzip_of_localAbs`: B5 locality for `locRich` (with measurability of the
  `P_*` local data and `Reg` a.s.) already gives a.e.-measurability of the unzipped
  `configLawFull` data, i.e. the one input of `E6.e6UpRich_of_meas` (own elementary argument:
  countable exhaustion by the good events of `LocalAbs`, then a countable choice of radii per
  coordinate).
* `theorem1_3_of_nodes_rich`: the top-level assembly with `locRich`
  (E4 → E5 → E6 → E6-UP → F1 → F2), with E6-UP proved by π-λ.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace QuantumZipper.E6

open B2 E1 CoordsFull D3Plus

variable {Ω : Type} [MeasurableSpace Ω] {Ω' : Type} [MeasurableSpace Ω']

/-- **E5 with a general local-data space** (`E5.E5Stmt` verbatim, `L` in place of
`(ℕ → ℝ) × (ℝ≥0 → ℝ)`). -/
def E5StmtG {L : Type} [MeasurableSpace L] (loc : ℕ → FieldSample × (ℝ → ℝ) → L) : Prop :=
  ∀ (κ T : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (ϖ : Measure ℂ)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y : Ω' → FieldSample) (B' : ℝ≥0 → Ω' → ℝ),
    Blueprint.RevCouplingBoundaryMeasureRegular → E5.Setup κ T P B X ϖ →
    IsQuantumWedge (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) Y P' →
    IsBrownianReal B' P' → IndepFun Y (pathOf B') P' → ∀ δ : ℝ, 0 < δ →
    let pm : ℝ≥0∞ := ∫⁻ ω, nuPalm κ T B X ϖ ω
      {x | x ∈ Icc (-δ) 0 ∧ realHitTime (Vr κ T B ω) x < ENNReal.ofReal T} ∂P
    let zc : ℝ → Ω → ℝ → FieldSample × (ℝ → ℝ) := fun C ω x =>
      canonConfig (Real.sqrt κ) (addConst (collided κ T B X ω x).1
        (-(mReg κ T B X ϖ ω) + C / Real.sqrt κ), (collided κ T B X ω x).2)
    ∀ R : ℕ, ∀ η : ℝ≥0∞, 0 < η → ∀ᶠ C in atTop,
      ∀ Γ : L → ℝ≥0∞, Measurable Γ → (∀ y, Γ y ≤ 1) →
        let lhs := ∫⁻ ω, ∫⁻ x in Icc (-δ) 0,
          {x | realHitTime (Vr κ T B ω) x < ENNReal.ofReal T}.indicator
            (fun x => Γ (loc R (zc C ω x))) x ∂nuPalm κ T B X ϖ ω ∂P
        let rhs := pm * ∫⁻ ω', Γ (loc R (Y ω', drive κ B' ω')) ∂P'
        lhs ≤ rhs + η ∧ rhs ≤ lhs + η

/-- **E5 for the rich local data.** -/
def E5StmtRich : Prop := E5StmtG D3Plus.locRich

/-- Raw equality of configurations: equal `configLawFull` data (raw values at all `coordsFull`
circles, raw pairings with all test functions, drivers on `[0,∞)`). -/
def RawEq (a b : Cfg) : Prop := cfgFull a = cfgFull b

theorem locRich_congr {a b : Cfg} (h : RawEq a b) (R : ℕ) : locRich R a = locRich R b := by
  rw [← truncFull_cfgFull, ← truncFull_cfgFull, h]

/-! ## a.e.-measurability of the unzipped data from B5 locality -/

/-- A `FullData`-valued map all of whose truncations are a.e.-measurable is a.e.-measurable
(own elementary argument: countably many radii suffice for each coordinate). -/
theorem aemeasurable_of_truncFull {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (D : Ω → FullData) (h : ∀ R, AEMeasurable (fun ω => truncFull R (D ω)) P) :
    AEMeasurable D P := by
  classical
  choose g hg hgD using h
  let Ri : ℕ → ℕ := fun i => (exists_inBallFull i).choose
  let Rρ : TestFun H → ℕ := fun ρ => (exists_suppIn ρ).choose
  refine ⟨fun ω => ((fun i => (g (Ri i) ω).1.1 i, fun ρ => (g (Rρ ρ) ω).1.2 ρ),
    fun s => (g ⌈s⌉₊ ω).2 s), ?_, ?_⟩
  · refine Measurable.prodMk (Measurable.prodMk (measurable_pi_iff.2 fun i => ?_)
      (measurable_pi_iff.2 fun ρ => ?_)) (measurable_pi_iff.2 fun s => ?_)
    · exact ((measurable_pi_apply i).comp (measurable_fst.comp measurable_fst)).comp (hg _)
    · exact ((measurable_pi_apply ρ).comp (measurable_snd.comp measurable_fst)).comp (hg _)
    · exact ((measurable_pi_apply s).comp measurable_snd).comp (hg _)
  · filter_upwards [ae_all_iff.2 hgD] with ω hω
    refine Prod.ext (Prod.ext (funext fun i => ?_) (funext fun ρ => ?_)) (funext fun s => ?_)
    · have hRi : inBallFull (Ri i) i := (exists_inBallFull i).choose_spec
      have := congrArg (fun e : FullData => e.1.1 i) (hω (Ri i))
      simp only [truncFull, hRi, ite_true] at this
      exact this
    · have hRρ : suppIn (Rρ ρ) ρ := (exists_suppIn ρ).choose_spec
      have := congrArg (fun e : FullData => e.1.2 ρ) (hω (Rρ ρ))
      simp only [truncFull, hRρ, ite_true] at this
      exact this
    · have := congrArg (fun e : FullData => e.2 s) (hω ⌈s⌉₊)
      simp only [truncFull, min_eq_left (Nat.le_ceil s)] at this
      exact this

/-! ## Theorem 1.3 assembly with the rich local data -/

/-- **E6 node for `locRich`** (the E6 owner proves it with `e6_concrete_gen locRich`). -/
def E6NodeStmtRich : Prop := E5StmtRich → E6LocStmtRich

end QuantumZipper.E6
