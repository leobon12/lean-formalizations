/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1ExtTip
import InteractingSLE.Spec.Supplement.GW1WalkExitD4
import InteractingSLE.Spec.Supplement.GW1WalkExitData
import InteractingSLE.Spec.Supplement.StagedRegularize
import InteractingSLE.Spec.Supplement.WalkUnionLawMain
import InteractingSLE.Spec.Supplement.GW1ConnectorFirst
import InteractingSLE.Spec.Supplement.BR3Ref
import InteractingSLE.Spec.Supplement.SB2HWire

/-!
# GW1's `ExteriorRecord` at every launch of the actual lower walk, and SB2(1)'s clause `m ≤ 0`

Packet PROVE-GW1-EXTREC. GW1's exterior-record datum `GW1WalkFinish.ExteriorRecord` (the launch chart's inverse tends
at `0` to the walk's current point, which is the right record, with the inverse boundary correspondence on the
untouched outward ray) is the D.4 half of `GW1WalkFinish.WalkD4GeometryStatement`, proved pathwise by
`GW1WalkExit.walk_recordGeometry` from GW1's stage data (`GW1WalkExit.WalkStageData`). Those stage data hold almost
surely for a staged right walk regular at every sample whose boundary data satisfy GW1's ambient bound
`b − (π/2)χ < λ` on `(−∞, 0)` (`GW1WalkExit.ae_walkStageData_right`); in GW1's setting the bound comes from the
counterflow (`GW1Conn.ambient_bounds`, Theorem 1.3 at universe `0`).

* `rawRecordBound_of_launch`, `zero_le_stRecR_of_rawRecordBound`: at a launch the right record is `≥ 0`;
* **`ae_exteriorRecord_lowerWalk`**: for staged families that are `StagedPiecesRegular` (ruling R51; regularized
  through `StagedReg.regFam_spec`), almost surely at every launch of the lower walk the state has the exterior
  record, a nonnegative right record, and at a finite exit the post-piece exterior record;
* **`ae_launchEntry_nonpos_of_ambient`** / **`ae_launchEntry_nonpos_of_counterflow`**: SB2(1)'s clause `m ≤ 0`
  (clause (0) of `SB.Lv.SB2RelDriverStatement`) under the ambient bound / in the counterflow setting;
* `SB2EntryNonposStatement` (clause (0) in the full generality of `SB2RelDriverStatement`), `SB2RelDriverCoreStatement`
  (clauses (1)–(3)) and **`sb2RelDriverStatement_of_core`**: the named input splits into the two;
  `SB2EntryNonposAmbStatement` / **`sb2EntryNonposAmbStatement`**: clause (0) restricted to GW1's ambient bound, proved;
  `SB2RelDriverCfStatement` (the named input in GW1's counterflow setting, implied by it) and
  **`sb2RelDriverCfStatement_of_core`**: there clauses (1)–(3) suffice.

`SB2EntryNonposStatement` without the ambient bound is not proved: off GW1's setting the frozen lower walk may end a
piece at a left threshold (`b − (π/2)χ ≥ λ` somewhere on `(−∞, 0)`) and continue leftward, which GW1's one-sided
record induction (`walk_prefix_geometry`, `walk_recordGeometry`) does not cover; the source's lower walk is GW1's walk,
whose setting (a complete counterflow) supplies the bound.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.GW1Ext

open Exist Exist.Staged Exist.StagedLaw GW1WalkExit GW1WalkFinish GW1WalkChain GW1Bookkeep
open PiecewiseConstantBoundaryData (jumpSet)

/-- **At a launch of a boundary walk the outward record bounds the physical prefix** (from GW1's prefix geometry,
`GW1WalkExit.walk_prefix_geometry`, at the even index of the launch; the walk is not finished there). -/
theorem rawRecordBound_of_launch {κ θ : ℝ} (hκ : 0 < κ) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {right : Bool}
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (hreg : ∀ k, IsRegularDriver (D k))
    (hS : WalkStageData κ b jumps θ right D)
    (hP : ∀ k c θ',
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (k + 1)).2.2.2.1 k =
        some (c, θ') →
      GW1P.PieceRegular (D k).1 (min (instrTime (boundaryWalkSpec b jumps θ right) k) (D k).2))
    {k : ℕ} (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (k + 1)).2.2.2.1 k ≠ none) :
    RawRecordBound right 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D k) := by
  have hPrefix := walk_prefix_geometry hκ hb D hreg hS hP
  obtain ⟨hev, hk⟩ := GW1W.even_of_launches_walk hl
  have hn : k / 2 ≤ (jumpSet b jumps).card + 1 := by
    rw [boundaryWalk_length] at hk
    omega
  have heq : 2 * (k / 2) = k := by omega
  have hi : stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D k) = stDone ∨
      (LaunchReady κ b θ right (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D k) ∧
        RawRecordBound right 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D k) ∧
        ExteriorInverse right (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D k)) := by
    simpa only [heq] using hPrefix (k / 2) hn
  rcases hi with hd | ⟨-, hB, -⟩
  · exact False.elim ((hS k hl).2.1.not_done hd)
  · exact hB

/-- The root is part of the physical prefix, so a right record bounding the prefix is `≥ 0`. -/
theorem zero_le_stRecR_of_rawRecordBound {s : ExplState} (h : RawRecordBound true 0 s) : 0 ≤ stRecR s := by
  have h0 := h 0 (Or.inl (Or.inl (mem_singleton _)))
  simpa only [sideCoord, outwardRecord, ↓reduceIte] using h0

section Law

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **GW1's exterior record at every launch of the actual lower walk** (the datum `ExteriorRecord` of
`GW1WalkFinish.walkTipCoordinates_of_exteriorRecords`, for the walk of SB2(1)): for staged families that are
`StagedPiecesRegular` and boundary data with GW1's ambient bound `b − (π/2)χ < λ` on `(−∞, 0)`, almost surely, at
every launch `k` of the lower walk (angle `−π/2`, continuing right), the state before the launch has the exterior
record and a nonnegative right record, and after a finite exit the next state has the exterior record.

Proof: regularize the family (`StagedReg.regFam_spec`; same runs almost surely, still `StagedPiecesRegular` by
`WalkLaw.stagedPiecesRegular_regHist`), take GW1's stage data (`ae_walkStageData_right`) and apply the pathwise D.4
geometry (`walk_recordGeometry`) and the prefix record bound (`rawRecordBound_of_launch`). -/
theorem ae_exteriorRecord_lowerWalk (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hR : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    (hamb : ∀ t, t < 0 → t ∉ jumps → b t + -(Real.pi / 2) * chiC κ < sleLambda κ) :
    ∀ᵐ ω ∂P, ∀ k : ℕ,
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (k + 1)).2.2.2.1 k ≠ none →
      ExteriorRecord true (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) k) ∧
        0 ≤ stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) k) ∧
        ((E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω).2 ≠ ⊤ →
          ExteriorRecord true (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (k + 1))) := by
  have hprog := isBoundaryContinuedProgram_boundaryWalkSpec b jumps (θ := -(Real.pi / 2))
    ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  obtain ⟨hE', hreg', hrun⟩ := StagedReg.regFam_spec hb hE hR
  have hR₁ : StagedPiecesRegular κ b jumps P (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) :=
    WalkLaw.stagedPiecesRegular_regHist (hR _ hprog)
  filter_upwards [ae_walkStageData_right hκ hb hh (hE' _ hprog) (hreg' _) hamb, hR₁, hrun _ hprog]
    with ω hs hr hrω
  intro k hl
  rw [← hrω (k + 1)] at hl
  have hP : ∀ j c θ', (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun i => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) (j + 1)).2.2.2.1 j =
        some (c, θ') →
      GW1P.PieceRegular (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω).1
        (min (instrTime (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j)
          (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω).2) :=
    fun j c θ' hl' => hr j θ' _ c (eq_launch_of_launches _ _ hl').1 hl'
  have hX := ((walk_recordGeometry hκ hb _ (fun j => hreg' _ j ω) hs hP).2 k hl)
  have hB := rawRecordBound_of_launch hκ hb _ (fun j => hreg' _ j ω) hs hP hl
  rw [hrω k] at hX hB
  rw [hrω (k + 1), StagedReg.regFam, StagedReg.regHist_snd] at hX
  exact ⟨hX.1, zero_le_stRecR_of_rawRecordBound hB, hX.2⟩

/-- **SB2(1)'s clause `m ≤ 0` under GW1's ambient bound** (clause (0) of `SB.Lv.SB2RelDriverStatement`): almost surely
on the launch event of instruction `k` of the lower walk, the entry point `m = Lv.launchEntry …` of the launch chart is
`≤ 0`, for every upper seed `u ≤ 0` (`ae_exteriorRecord_lowerWalk` and `launchEntry_nonpos_of_exteriorRecord`). -/
theorem ae_launchEntry_nonpos_of_ambient (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hR : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    (hamb : ∀ t, t < 0 → t ∉ jumps → b t + -(Real.pi / 2) * chiC κ < sleLambda κ) (k : ℕ) {u : ℝ}
    (hu : u ≤ 0) :
    ∀ᵐ ω₀ ∂P, ω₀ ∈ SB.Lv.launchSet κ b jumps E k → SB.Lv.launchEntry κ b jumps E k u ω₀ ≤ 0 := by
  have hprog := isBoundaryContinuedProgram_boundaryWalkSpec b jumps (θ := -(Real.pi / 2))
    ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  filter_upwards [ae_exteriorRecord_lowerWalk hκ hb hh hE hR hamb, hR _ hprog] with ω₀ hX hr hF
  obtain ⟨hE0, h0, -⟩ := hX k hF
  exact launchEntry_nonpos_of_exteriorRecord
    (fun j c' θ' hl' => hr j θ' _ c' (eq_launch_of_launches _ _ hl').1 hl') hF hu hE0 h0

/-- **SB2(1)'s clause `m ≤ 0` in GW1's counterflow setting** (Theorem 1.4's setting): the ambient bound is supplied by
the complete centred counterflow (`GW1Conn.ambient_bounds`, with GW0's forward statement from Theorem 1.3 at universe
`0`, `BR3Ref.gw0ForwardStatement_of_theorem13`). -/
theorem ae_launchEntry_nonpos_of_counterflow (hT13₀ : Theorem13Statement.{0}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ')
    (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hR : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    (k : ℕ) {u : ℝ} (hu : u ≤ 0) :
    ∀ᵐ ω₀ ∂P, ω₀ ∈ SB.Lv.launchSet κ b jumps E k → SB.Lv.launchEntry κ b jumps E k u ω₀ ≤ 0 :=
  ae_launchEntry_nonpos_of_ambient hκ hb hh hE hR
    (GW1Conn.ambient_bounds (BR3Ref.gw0ForwardStatement_of_theorem13 hT13₀) hκ hκ4 hb hh hcf hζ').1 k hu

end Law

/-! ### Splitting SB2FIN3's named input -/

/-- **Clause (0) of `SB.Lv.SB2RelDriverStatement`, in its full generality** (no ambient bound on the boundary data):
almost surely on the launch event of instruction `k` of the lower walk, the entry point is `≤ 0`. Proved under GW1's
ambient bound (`ae_launchEntry_nonpos_of_ambient`, `sb2EntryNonposAmbStatement`) and in the counterflow setting
(`ae_launchEntry_nonpos_of_counterflow`); open without the bound. -/
def SB2EntryNonposStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
    ∀ (k : ℕ) (u : ℝ), u ≤ 0 →
      ∀ᵐ ω₀ ∂P, ω₀ ∈ SB.Lv.launchSet κ b jumps E k → SB.Lv.launchEntry κ b jumps E k u ω₀ ≤ 0

open SB SB.Lv Sec4 in
/-- **`SB.Lv.SB2RelDriverStatement` without its clause (0)**: exactly its setting and its clauses (1) K2's
conclusion in the recentred launch chart, (2) SB2(1)'s active word, (3) the link. -/
def SB2RelDriverCoreStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
    ∀ (k : ℕ) (u ψ : ℝ), u ≤ 0 → -(Real.pi / 2) < ψ →
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightRight κ (b x + ψ * chiC κ) ∨
        κ / 2 - 2 ≤ cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
    ∀ (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞), IsFlowLine κ b jumps u ψ P h η ζ →
      (∀ᵐ ω ∂P, ∀ a : ℝ≥0, (a : ℝ≥0∞) ≤ ζ ω → IsOneSided (lowerPrefix κ b jumps E k u ω) (η ω) a) →
    ∃ (bc : Ω → ℝ → ℝ) (jc : Ω → Finset ℝ) (W : ℝ≥0 → Ω → ℝ) (ζr : Ω → ℝ≥0∞),
      IsCondFlowLineDriverOn κ ψ (pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) k) P (launchSet κ b jumps E k) h
        (fun ω => (launchChart κ b jumps E k ω).recenter (launchEntry κ b jumps E k u ω)) bc jc W ζr ∧
      (∀ᵐ ω₀ ∂P, ω₀ ∈ launchSet κ b jumps E k →
        ∀ (b' : ℝ → ℝ) (jumps' : Finset ℝ) (h' : Ω → DistOn upperHalfPlaneOpens),
          IsPiecewiseConstantBoundaryData b' jumps' →
          (∀ ω, IsChartTransport (launchChart κ b jumps E k ω₀) 1 0 (chiC κ) (h ω) (h' ω)) →
          IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps
            (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) k) ω₀) h' b' jumps' →
          IsActiveLowWord κ b jumps u b' jumps' (launchEntry κ b jumps E k u ω₀)) ∧
      (∀ᵐ ω₀ ∂P, ω₀ ∈ launchSet κ b jumps E k →
        ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps
            (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) k) ω₀),
          IsRemainderLink (launchChart κ b jumps E k ω₀) (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E k u ω))
            (fun t => GW2aSingle.chosenTrace W ζr ω t + launchEntry κ b jumps E k u ω₀) (ζr ω))

/-- **SB2FIN3's named input splits**: clause (0) (`SB2EntryNonposStatement`) and clauses (1)–(3)
(`SB2RelDriverCoreStatement`) give `SB.Lv.SB2RelDriverStatement`. -/
theorem sb2RelDriverStatement_of_core (h0 : SB2EntryNonposStatement.{u}) (hC : SB2RelDriverCoreStatement.{u}) :
    SB.Lv.SB2RelDriverStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh E hE hER k u ψ hu hψ hL hH η ζ hη hone
  obtain ⟨bc, jc, W, ζr, hK, hword, hlink⟩ :=
    hC κ hκ hκ4 b jumps hb P h hh E hE hER k u ψ hu hψ hL hH η ζ hη hone
  exact ⟨bc, jc, W, ζr, h0 κ hκ hκ4 b jumps hb P h hh E hE hER k u hu, hK, hword, hlink⟩

/-- **Clause (0) of `SB.Lv.SB2RelDriverStatement` under GW1's ambient bound** (`SB2EntryNonposStatement` for boundary
data with `b − (π/2)χ < λ` on `(−∞, 0)`, the bound GW1's counterflow setting supplies). -/
def SB2EntryNonposAmbStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    (∀ t, t < 0 → t ∉ jumps → b t + -(Real.pi / 2) * chiC κ < sleLambda κ) →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
    ∀ (k : ℕ) (u : ℝ), u ≤ 0 →
      ∀ᵐ ω₀ ∂P, ω₀ ∈ SB.Lv.launchSet κ b jumps E k → SB.Lv.launchEntry κ b jumps E k u ω₀ ≤ 0

/-- **`SB2EntryNonposAmbStatement` is proved** (no named input; `ae_launchEntry_nonpos_of_ambient`). -/
theorem sb2EntryNonposAmbStatement : SB2EntryNonposAmbStatement.{u} := by
  intro κ hκ _ b jumps hb hamb Ω _ _ P _ h hh E hE hR k u hu
  exact ae_launchEntry_nonpos_of_ambient hκ hb hh hE hR hamb k hu

open SB SB.Lv Sec4 in
/-- **`SB.Lv.SB2RelDriverStatement` in GW1's counterflow setting** (the setting of the landed SB3 consumer
`SB.SB3InductionRegStatement`: a complete centred counterflow with infinite lifetime): exactly the named input with the
counterflow binder added after the field. -/
def SB2RelDriverCfStatement : Prop :=
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
    ∀ (k : ℕ) (u ψ : ℝ), u ≤ 0 → -(Real.pi / 2) < ψ →
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightRight κ (b x + ψ * chiC κ) ∨
        κ / 2 - 2 ≤ cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
    ∀ (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞), IsFlowLine κ b jumps u ψ P h η ζ →
      (∀ᵐ ω ∂P, ∀ a : ℝ≥0, (a : ℝ≥0∞) ≤ ζ ω → IsOneSided (lowerPrefix κ b jumps E k u ω) (η ω) a) →
    ∃ (bc : Ω → ℝ → ℝ) (jc : Ω → Finset ℝ) (W : ℝ≥0 → Ω → ℝ) (ζr : Ω → ℝ≥0∞),
      (∀ᵐ ω₀ ∂P, ω₀ ∈ launchSet κ b jumps E k → launchEntry κ b jumps E k u ω₀ ≤ 0) ∧
      IsCondFlowLineDriverOn κ ψ (pastSigma κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) k) P (launchSet κ b jumps E k) h
        (fun ω => (launchChart κ b jumps E k ω).recenter (launchEntry κ b jumps E k u ω)) bc jc W ζr ∧
      (∀ᵐ ω₀ ∂P, ω₀ ∈ launchSet κ b jumps E k →
        ∀ (b' : ℝ → ℝ) (jumps' : Finset ℝ) (h' : Ω → DistOn upperHalfPlaneOpens),
          IsPiecewiseConstantBoundaryData b' jumps' →
          (∀ ω, IsChartTransport (launchChart κ b jumps E k ω₀) 1 0 (chiC κ) (h ω) (h' ω)) →
          IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps
            (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) k) ω₀) h' b' jumps' →
          IsActiveLowWord κ b jumps u b' jumps' (launchEntry κ b jumps E k u ω₀)) ∧
      (∀ᵐ ω₀ ∂P, ω₀ ∈ launchSet κ b jumps E k →
        ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps
            (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) k) ω₀),
          IsRemainderLink (launchChart κ b jumps E k ω₀) (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E k u ω))
            (fun t => GW2aSingle.chosenTrace W ζr ω t + launchEntry κ b jumps E k u ω₀) (ζr ω))

/-- The counterflow form is implied by the named input (the binder is not used). -/
theorem sb2RelDriverCfStatement_of_relDriver (hrel : SB.Lv.SB2RelDriverStatement.{u}) :
    SB2RelDriverCfStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh _ _ _ _ E hE hER k u ψ hu hψ hL hH η ζ hη hone
  exact hrel κ hκ hκ4 b jumps hb P h hh E hE hER k u ψ hu hψ hL hH η ζ hη hone

/-- **In the counterflow setting clauses (1)–(3) suffice**: clause (0) is `ae_launchEntry_nonpos_of_counterflow`
(Theorem 1.3 at universe `0` for GW0's forward statement). -/
theorem sb2RelDriverCfStatement_of_core (hT13₀ : Theorem13Statement.{0}) (hC : SB2RelDriverCoreStatement.{u}) :
    SB2RelDriverCfStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hER k u ψ hu hψ hL hH η ζ hη hone
  obtain ⟨bc, jc, W, ζr, hK, hword, hlink⟩ :=
    hC κ hκ hκ4 b jumps hb P h hh E hE hER k u ψ hu hψ hL hH η ζ hη hone
  exact ⟨bc, jc, W, ζr, ae_launchEntry_nonpos_of_counterflow hT13₀ hκ hκ4 hb hh hcf hζ' hE hER k hu, hK, hword,
    hlink⟩

end InteractingSLE.Theorem14.GW1Ext
