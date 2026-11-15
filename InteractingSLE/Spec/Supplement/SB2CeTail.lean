/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CeEng
import InteractingSLE.Spec.Supplement.SB2CeJm
import InteractingSLE.Spec.Supplement.SB2CyF3
import InteractingSLE.Spec.Supplement.SB2CqGood
import InteractingSLE.Spec.Supplement.SB2CqHull
import InteractingSLE.Spec.Supplement.SB2YhAE
import InteractingSLE.Spec.Supplement.SB2CjK2

/-!
# K2 at the tails (D77 item 1)

Packet PROVE-SB2-CONDFIN, round 14 (decision D77, item 1). K2 at a tail stage `ℓ` (`Cj.ae_k2_stage`) for NOJUMP's tail
versions (`Cz.SB2LowerStageVersionStatement6`, typed over the JOINT second set `A₂J`, D51), the input of CANON's
`Cz.pkgTail_of_k2` and F3LAW's step. The root proofs, retyped for the tail version type:

* **`hmean_tail_obj`**: K2's `hmean` for the joint union at every version, word type, B-time and test function. At
  clock `0`: `Ci.ae_lineMean_zero` on the version's own (joint) union. At positive clock: B's own union mean by the
  engine `Ce.ae_lineMean_pos_tailG` in B's stage chart (LCMEAN's stage pull-back with finite fibres `Cy.hpull_cf`, the
  stop-word mean of `Cx.exists_rootLineFamily`, the record `Cx.stop_facts`, SB2LIFT's tail S2 clause
  `Sx.ae_isStageS2_tail`, F3's mean identity `Cy.hF3_of_premise`), then the joint transfer
  `Ce.hmean_joint_of_hmeanB_tail`. The tail S2 clause's hull facts come from CANON's `Cz.ae_stageGoodAt_retX` and
  `Cz.fillVer_first_eq`.
* **`ae_k2_tail`**: `Cj.ae_k2_stage`'s conclusion (stopped matches and the lifetime), the `hK2` of
  `Cz.pkgTail_of_k2`, for the line family `Cx.exists_rootLineFamily` (`hBm`, `hBc`, `hBl`, `hloc` by
  `Cx.k2Inputs_of_rootSets`) and Statement6's objects at `ℓ`, from the word's law and bound (F3LAW's).

Inputs besides Theorems 1.2–1.3: Statement6's objects and its F3 premise (`hP8`), the word's measurability `hc`,
sortedness and kernel law `hlaw` (F3LAW's law read at the offset).

R48: Theorems 1.2–1.3 appear only as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC fwdHull fwdMap logDerivFwd)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Ce

open Restart Exist Exist.Staged Exist.StagedLaw WalkSide LocalSets WholeField Mf Mk Om Lv Ms Cx
open Supp8.Q3Stop Sec7.PocketTraversal Restart.DomainMarkov
open Supp8.GB6.RelDrv (IsStopDrvMatch)

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- **K2's `hmean` at a tail stage, for the joint union** (Theorems 1.2–1.3; Statement6's objects, its F3 premise and
the word's law). -/
theorem hmean_tail_obj (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {u : ℝ} {l : List (ℝ × ℝ≥0)} {k ℓ : ℕ} (hu : u ≤ 0) (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2))
    (hleft : ∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k →
      upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅)
    (hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {𝓖 : Filtration ℝ≥0 mΩ} {A₁ A₂ A₂J : ℝ≥0 → Ω → Set ℂ}
    (h𝓖 : ∀ t : ℝ≥0, 𝓖 t = pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
      pastSigma κ b jumps
        (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2)) (t : ℝ≥0∞))
        (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1))
    (hfam : ∀ t : ℝ≥0, RootSetsAt κ b jumps P h E u l k ℓ t u₀ (A₁ t) (A₂ t) (A₂J t))
    {F : Set Ω} {K : Ω → Set ℂ} {x₀ : Ω → ℝ} {β₁ : Ω → BoundaryWord} {types : Set WordType}
    {pc : Ω → ℝ≥0 → ℂ} {tL : Ω → ℝ≥0} {relLife : Ω → ℝ≥0∞}
    (S : Na.StageVersionS κ (-(Real.pi / 2)) P F 𝓖 A₁ A₂J (fun ω => Mo.hullChart (fillH (K ω)) (x₀ ω))
      (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) types pc tL
      (fun ω => (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2) relLife)
    (hKm : @Restart.IsDyadicHitMeasurable Ω (lineFiltC P 𝓖 0) K) (hKc : ∀ ω, IsCompact (K ω))
    (hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf)) (hKF : ∀ᵐ ω ∂P, ω ∈ F → fillH (K ω) = A₁ 0 ω)
    (hx₀m : Measurable[lineFiltC P 𝓖 0] x₀) (hFm : MeasurableSet[lineFiltC P 𝓖 0] F)
    (hpc : ∀ ω, pc ω = Lk.pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) ℓ)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω))
    (htL : ∀ ω, tL ω = 0)
    (hent : ∀ᵐ ω ∂P, ω ∈ F → IsRightEntryChart (Nc.retX κ b jumps E u l k ℓ ω)
      (realMax (Nc.retX κ b jumps E u l k ℓ ω))
      ((Mo.hullChart (fillH (Nc.retX κ b jumps E u l k ℓ ω)) 0).recenter (x₀ ω)))
    (hFae : ∀ᵐ ω ∂P, ω ∈ F ↔ (ω ∈ stageEvent κ b jumps E u l k ℓ ∧
      Lk.relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) < ℓ ∧
      0 < (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2))
    (hc : Measurable[lineFiltC P 𝓖 0] fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω))
    (hsort : ∀ ω, (β₁ ω).IsSorted)
    (hlaw : ∀ᵐ ω₀ ∂P, ω₀ ∈ F → IsGFFWithBoundaryData (condExpKernel P (lineFiltC P 𝓖 0) ω₀)
      (fun ω => Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω))
      (BoundaryWord.shiftW (x₀ ω₀) (β₁ ω₀)).fn (BoundaryWord.shiftW (x₀ ω₀) (β₁ ω₀)).jumps)
    (hP8 : ∀ g₁ : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean (A₁ 0) (WholeField.centredField h u₀) P g₁ →
      ∀ᵐ ω ∂P, ω ∈ stageEvent κ b jumps E u l k ℓ →
        ∀ w₁ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₁ (H \ A₁ 0 ω) →
          (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₁ 0 ω → g₁ ω φ = ∫ z, w₁ z * φ z) →
          EqOn (fun z => w₁ z + u₀ z)
            (fun z => (β₁ ω).mean ((Mo.hullChart (A₁ 0 ω) 0).1 z) - chiC κ * (Mo.hullChart (A₁ 0 ω) 0).2.2 z)
            (H \ A₁ 0 ω)) :
    ∀ g : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens,
      (∀ t, IsLocalSetMean (fun ω => A₁ t ω ∪ A₂J t ω) (WholeField.centredField h u₀) P (g t)) →
      ∀ m, ∀ w ∈ types, ∀ (t : ℝ≥0) (φ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P,
        ω ∈ seedCell κ (-(Real.pi / 2)) (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) F w →
        (S.ver m).a t ω < (S.ver m).Λ w ω →
        Disjoint (tsupport φ) (fwdHull (fun s : ℝ => (S.ver m).W s.toNNReal ω) ((S.ver m).a t ω).toNNReal) →
        Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 (-(Real.pi / 2) * chiC κ) (chiC κ)
            (g t ω + (h ω - WholeField.centredField h u₀ ω)) φ =
          ∫ z, couplingMean κ (fun s : ℝ => (S.ver m).W s.toNNReal ω) ((S.ver m).a t ω).toNNReal
            (bheProc κ (typedRhoL w) (typedRhoR w) (S.ver m).W
              (geomLW (S.ver m).W (cellXL κ (-(Real.pi / 2)) (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) w))
              (geomRW (S.ver m).W (cellXR κ (-(Real.pi / 2)) (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) w)) ω
              ((S.ver m).a t ω).toNNReal) z * φ z := by
  classical
  intro g hg m w hw t φ
  have hsortc : ∀ ω, (BoundaryWord.shiftW (x₀ ω) (β₁ ω)).IsSorted := fun ω =>
    BoundaryWord.isSorted_shiftW (hsort ω) _
  have hh0 := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  obtain ⟨-, -, hrun⟩ := StagedReg.regFam_spec hb hE hER
  have hθ : -(Real.pi / 2) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hw' := isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ true
  have hsu := Lu.isBoundaryContinuedProgram_upperSpec (u := u) hlθ
  have hFS : ∀ᵐ ω ∂P, ω ∈ F → (ω ∈ stageEvent κ b jumps E u l k ℓ ∧
      Lk.relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) < ℓ ∧
      0 < (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2) := hFae.mono fun ω h hω => h.1 hω
  -- the live event's samples are NOJUMP-good for the retained union (CANON)
  have hgood := Cz.ae_stageGoodAt_retX h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k ℓ hleft hℓ hFS hent
  have hA₁K : ∀ t', ∀ᵐ ω ∂P, ω ∈ F → A₁ t' ω = fillH (K ω) := fun t' => by
    filter_upwards [(hfam t').2.2.2.2.2.2.2.2.2.2.1, (hfam 0).2.2.2.2.2.2.2.2.2.2.1, hKF, hgood]
      with ω h1 h0 hk hg' hω
    rw [h1.1, Cz.fillVer_first_eq (hg' hω), hk hω, h0.1, Cz.fillVer_first_eq (hg' hω)]
  have hK : ∀ᵐ ω ∂P, ω ∈ F → fillH (K ω) = fillH (upperPrefix κ b jumps E u l k ω ∪ SB.prefixPhysSet κ b jumps
      (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i
      ω) ℓ) := by
    filter_upwards [(hfam 0).2.2.2.2.2.2.2.2.2.2.1, hKF, hgood] with ω h0 hk hg' hω
    rw [hk hω, h0.1, Cz.fillVer_first_eq (hg' hω)]
    rfl
  have hFS2 : ∀ᵐ ω ∂P, ω ∈ F → ω ∈ stageEvent κ b jumps E u l k ℓ ∧
      Lk.relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) < ℓ :=
    hFS.mono fun ω h hω => ⟨(h hω).1, (h hω).2.1⟩
  -- SB2LIFT's tail S2 clause on the version's fields
  have hS2 := fun m' w' (hw' : w' ∈ types) t' => Sx.ae_isStageS2_tail h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER
    hu hlθ hleft (S.ver m') hFS2 hA₁K hK hent hpc htL w' hw' t'
  -- F3's mean identity in the version's chart (from Statement6's premise)
  have hF3 := Cy.hF3_of_premise (x₀ := x₀) (Fr := F) hh hℓ.le hu₀ (fun t' => (hfam t').1)
    (fun t' => (hfam t').2.2.2.2.2.2.2.2.1) (fun t' => (hfam t').2.2.2.1)
    (fun t' => (hfam t').2.2.2.2.2.2.2.2.2.2.1.mono fun ω h => h.1) (Eventually.of_forall fun ω h => h) hKF
    (hFS.mono fun ω h hω => (h hω).1) hP8
  -- B's own union mean (the engine in B's stage chart)
  obtain ⟨hA₁m0, hA₂m0, hd₁0, hl₁0, hl₂0, hlU0, hUm0, hUloc0, hc₁0, hc₂0, hform0, -, -, -, -, -, hformJ0, -, -, -,
    hJm0, hJc0, -, hJloc0⟩ := hfam t
  obtain ⟨hUmJ, hcUJ, -, hlocJ⟩ := Cx.k2Inputs_of_rootSets h𝓖 hfam
  have hUmΩ : ∀ t', Measurable[mΩ, hittingSigma] (fun ω => A₁ t' ω ∪ A₂ t' ω) := fun t' => by
    obtain ⟨-, -, -, -, -, -, hUm, -⟩ := hfam t'
    exact hUm.mono (by rw [← h𝓖 t']; exact 𝓖.le t') le_rfl
  have hcU : ∀ t', ∀ ω, A₁ t' ω ∪ A₂ t' ω ⊆ H ∧ IsOpen (H \ (A₁ t' ω ∪ A₂ t' ω)) := fun t' ω => by
    obtain ⟨-, -, -, -, -, -, -, -, hc₁, hc₂, -⟩ := hfam t'
    refine ⟨union_subset (hc₁ ω).1 (hc₂ ω).1, ?_⟩
    have e : H \ (A₁ t' ω ∪ A₂ t' ω) = (H \ A₁ t' ω) ∩ (H \ A₂ t' ω) := by
      ext z
      simp only [Set.mem_sdiff, mem_inter_iff, mem_union]
      tauto
    rw [e]
    exact (hc₁ ω).2.inter (hc₂ ω).2
  obtain ⟨gB, hgB⟩ : ∃ gB : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens,
      ∀ t', IsLocalSetMean (fun ω => A₁ t' ω ∪ A₂ t' ω) (WholeField.centredField h u₀) P (gB t') := by
    choose gB hgB using fun t' => IsLocalSet.exists_isLocalSetMean hh0 (hUmΩ t') (hfam t').2.2.2.2.2.1
    exact ⟨gB, hgB⟩
  set C : ℝ≥0 → Set Ω := fun t' => {ω | ω ∈ capEvent κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ t' ∧
    (ExplState.run κ b jumps (Lu.upperSpec u l)
      (fun j => StagedReg.regFam E (Lu.upperSpec u l) j ω) (k + 1)).2.2.2.1 k ≠ none} with hCdef
  have hC : ∀ m', ∀ w' ∈ types, ∀ t', ∀ᵐ ω ∂P,
      ω ∈ seedCell κ (-(Real.pi / 2)) (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) F w' →
      (S.ver m').a t' ω < (S.ver m').Λ w' ω → ω ∈ C t' := fun m' w' hw'' t' => by
    filter_upwards [(S.ver m').alive w' hw'' t', hFS, hrun _ hw', hrun _ hsu] with ω halω hFω hrw hru hcell hlt
    have hωF : ω ∈ F := hcell.1.1
    obtain ⟨⟨hup, hlaunch⟩, -, -⟩ := hFω hωF
    refine ⟨⟨?_, ?_⟩, by rw [hru (k + 1)]; exact hup⟩
    · show (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (fun j =>
        StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none
      rw [hrw (ℓ + 1)]
      exact hlaunch
    · have hsnd : (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 =
          (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 := StagedReg.regularize_snd _ _
      rw [hsnd]
      exact halω hcell hlt
  have hind₂ : ∀ t', ∀ g₂ : Ω → DistOn upperHalfPlaneOpens,
      IsLocalSetMean (A₂ t') (WholeField.centredField h u₀) P g₂ →
      ∃ βB : Ω → BoundaryWord, ∀ᵐ ω ∂P, ω ∈ C t' → ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ A₂ t' ω) →
        (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₂ t' ω → g₂ ω φ = ∫ z, v z * φ z) →
        EqOn (fun z => v z + u₀ z) (fun z => (stopWord κ (βB ω, -(Real.pi / 2), recOf (t' : ℝ≥0∞)
          (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω))).mean
            (fwdMap (Mi.sb2StopDrv E b jumps (-(Real.pi / 2)) true ℓ t' ω)
              (Mi.sb2StopTime E b jumps (-(Real.pi / 2)) true ℓ t' ω)
              ((Mi.sb2StageChart κ E b jumps (-(Real.pi / 2)) true ℓ ω).1 z)) -
          chiC κ * ((logDerivFwd (Mi.sb2StopDrv E b jumps (-(Real.pi / 2)) true ℓ t' ω)
              (Mi.sb2StopTime E b jumps (-(Real.pi / 2)) true ℓ t' ω)
              ((Mi.sb2StageChart κ E b jumps (-(Real.pi / 2)) true ℓ ω).1 z)).im +
            (Mi.sb2StageChart κ E b jumps (-(Real.pi / 2)) true ℓ ω).2.2 z)) (H \ A₂ t' ω) := by
    intro t' g₂ hg₂
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hmean₂, -⟩ := hfam t'
    obtain ⟨β, hβ⟩ := hmean₂ g₂ hg₂
    exact ⟨β, hβ.mono fun ω h hCω => h hCω.1⟩
  have hB := Ce.ae_lineMean_pos_tailG (κ := κ) hκ hh hu₀ S hKc hKp hsortc (fun t' => (hfam t').1)
    (fun t' => (hfam t').2.1) (fun t' => (hfam t').2.2.1) (fun t' => (hfam t').2.2.2.1)
    (fun t' => (hfam t').2.2.2.2.1) (fun t' => (hfam t').2.2.2.2.2.1)
    (fun t' => (hfam t').2.2.2.2.2.2.2.2.2.2.2.1) (fun t' => (hfam t').2.2.2.2.2.2.2.2.2.2.2.2.1)
    (c := fun ω => Mi.sb2StageChart κ E b jumps (-(Real.pi / 2)) true ℓ ω)
    (wB := fun t' ω => Mi.sb2StopDrv E b jumps (-(Real.pi / 2)) true ℓ t' ω)
    (sB := fun t' ω => Mi.sb2StopTime E b jumps (-(Real.pi / 2)) true ℓ t' ω)
    (recB := fun t' ω => recOf (t' : ℝ≥0∞) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω))
    (C := C) (fun t' => (Cy.hpull_cf h13 h13₀ hκ hκ4 hb hh hcf hζ' hE hER hfam t').mono fun ω h hCω => h hCω.1 hCω.2)
    (fun t' => Eventually.of_forall fun ω hCω =>
      (Cx.stop_facts (StagedReg.isRegularDriver_regHist ℓ ω) le_rfl hCω.1.2).2.2.2.2.2.2.1)
    (fun t' => Eventually.of_forall fun ω hCω =>
      (Cx.stop_facts (StagedReg.isRegularDriver_regHist ℓ ω) le_rfl hCω.1.2).2.2.2.2.2.2.2)
    hind₂ (fun t' => (hA₁K t').mono fun ω h hω => (h hω).symm) hF3 hC hS2 gB hgB m w hw t
  -- the transfer to the joint union
  have hXH : ∀ ω, (WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
      WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2))
        (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω) ⊆ H := fun ω =>
    union_subset (WalkLaw.stageSet_subset_H _ _ _ _ _ _ ω) (WalkLaw.stageSet_subset_H _ _ _ _ _ _ ω)
  have hYH : ∀ ω, WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
      (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1) ω ⊆
        H := fun ω => WalkLaw.stageSet_subset_H _ _ _ _ _ _ ω
  have hXY : (fun ω => (WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
      WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2))
        (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω) ∪
      WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
        (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
        (ℓ + 1) ω) =
      fun ω => WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2))
          (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1) ω := by
    funext ω
    have hsub := WalkLaw.stageSet_mono (κ := κ) (b := b) (jumps := jumps)
      (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2)) (t : ℝ≥0∞))
      (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ω (Nat.le_succ ℓ)
    rw [union_assoc, union_eq_right.2 hsub]
  have hJ := Ce.hmean_joint_of_hmeanB_tail hh0 hKc hKp (S.ver m) hw t hXH hYH
    (hform0.mono fun ω h => h.1) (hform0.mono fun ω h => h.2) (by rw [hXY]; exact hformJ0)
    (by rw [h𝓖 t]; exact hUm0) (by rw [h𝓖 t]; exact hJm0) (hcU t) hJc0 (by rw [h𝓖 t]; exact hUloc0)
    (by rw [h𝓖 t]; exact hJloc0) (hgB t) (hg t) (fun ω => h ω - WholeField.centredField h u₀ ω)
    (-(Real.pi / 2) * chiC κ) (chiC κ) (fun ω => ∫ z, couplingMean κ (fun s : ℝ => (S.ver m).W s.toNNReal ω)
      ((S.ver m).a t ω).toNNReal (bheProc κ (typedRhoL w) (typedRhoR w) (S.ver m).W
        (geomLW (S.ver m).W (cellXL κ (-(Real.pi / 2)) (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) w))
        (geomRW (S.ver m).W (cellXR κ (-(Real.pi / 2)) (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) w))
        ω ((S.ver m).a t ω).toNNReal) z * φ z) φ (by
      filter_upwards [hB] with ω h1 hcell hpos hlt hdis
      exact h1 hcell hlt hpos φ hdis)
  have hZ := Ci.ae_lineMean_zero hκ hh hu₀ S hKm hKc hKp hx₀m hc hFm hsortc hUmJ hcUJ hlocJ hlaw g hg m w hw t φ
  filter_upwards [hJ, hZ] with ω h1 h2 hcell hlt hdis
  rcases eq_zero_or_pos ((S.ver m).a t ω) with h0 | h0
  · exact h2 hcell hlt h0
  · exact h1 hcell h0 hlt hdis


/-- **K2 at a tail stage** (Theorems 1.2–1.3): `Cj.ae_k2_stage`'s conclusion — the stopped matches of every version
with the canonical code of `(shiftW x₀ β₁, Z)` and the canonical lifetime equal to the relative one — for NOJUMP's
tail versions over the line family `Cx.exists_rootLineFamily`, from Statement6's objects (`hle`, `hlife`, the cover)
and the word's law and bound. This is the `hK2` of `Cz.pkgTail_of_k2` (and of F3LAW's step). -/
theorem ae_k2_tail (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {u : ℝ} {l : List (ℝ × ℝ≥0)} {k ℓ : ℕ} (hu : u ≤ 0) (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2))
    (hleft : ∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k →
      upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅)
    (hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {𝓖 : Filtration ℝ≥0 mΩ} {A₁ A₂ A₂J : ℝ≥0 → Ω → Set ℂ}
    (h𝓖 : ∀ t : ℝ≥0, 𝓖 t = pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
      pastSigma κ b jumps
        (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2)) (t : ℝ≥0∞))
        (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1))
    (hfam : ∀ t : ℝ≥0, RootSetsAt κ b jumps P h E u l k ℓ t u₀ (A₁ t) (A₂ t) (A₂J t))
    {F : Set Ω} {K : Ω → Set ℂ} {x₀ : Ω → ℝ} {β₁ : Ω → BoundaryWord} {types : Set WordType}
    {pc : Ω → ℝ≥0 → ℂ} {tL : Ω → ℝ≥0} {relLife : Ω → ℝ≥0∞}
    (S : Na.StageVersionS κ (-(Real.pi / 2)) P F 𝓖 A₁ A₂J (fun ω => Mo.hullChart (fillH (K ω)) (x₀ ω))
      (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) types pc tL
      (fun ω => (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2) relLife)
    (hKm : @Restart.IsDyadicHitMeasurable Ω (lineFiltC P 𝓖 0) K) (hKc : ∀ ω, IsCompact (K ω))
    (hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf)) (hKF : ∀ᵐ ω ∂P, ω ∈ F → fillH (K ω) = A₁ 0 ω)
    (hx₀m : Measurable[lineFiltC P 𝓖 0] x₀) (hFm : MeasurableSet[lineFiltC P 𝓖 0] F)
    (hpc : ∀ ω, pc ω = Lk.pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) ℓ)
      (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω))
    (htL : ∀ ω, tL ω = 0)
    (hent : ∀ᵐ ω ∂P, ω ∈ F → IsRightEntryChart (Nc.retX κ b jumps E u l k ℓ ω)
      (realMax (Nc.retX κ b jumps E u l k ℓ ω))
      ((Mo.hullChart (fillH (Nc.retX κ b jumps E u l k ℓ ω)) 0).recenter (x₀ ω)))
    (hFae : ∀ᵐ ω ∂P, ω ∈ F ↔ (ω ∈ stageEvent κ b jumps E u l k ℓ ∧
      Lk.relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) < ℓ ∧
      0 < (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2))
    (hc : Measurable[lineFiltC P 𝓖 0] fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω))
    (hsort : ∀ ω, (β₁ ω).IsSorted)
    (hlaw : ∀ᵐ ω₀ ∂P, ω₀ ∈ F → IsGFFWithBoundaryData (condExpKernel P (lineFiltC P 𝓖 0) ω₀)
      (fun ω => Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω))
      (BoundaryWord.shiftW (x₀ ω₀) (β₁ ω₀)).fn (BoundaryWord.shiftW (x₀ ω₀) (β₁ ω₀)).jumps)
    (hP8 : ∀ g₁ : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean (A₁ 0) (WholeField.centredField h u₀) P g₁ →
      ∀ᵐ ω ∂P, ω ∈ stageEvent κ b jumps E u l k ℓ →
        ∀ w₁ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₁ (H \ A₁ 0 ω) →
          (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₁ 0 ω → g₁ ω φ = ∫ z, w₁ z * φ z) →
          EqOn (fun z => w₁ z + u₀ z)
            (fun z => (β₁ ω).mean ((Mo.hullChart (A₁ 0 ω) 0).1 z) - chiC κ * (Mo.hullChart (A₁ 0 ω) 0).2.2 z)
            (H \ A₁ 0 ω))
    (htypes : types.Countable)
    (hcover : ∀ᵐ ω ∂P, ω ∈ F → angleWordType κ (-(Real.pi / 2)) (BoundaryWord.shiftW (x₀ ω) (β₁ ω)) ∈ types)
    {M : ℝ} (hM0 : 0 ≤ M) (hMβ : ∀ ω, ∀ y ∉ (β₁ ω).jumps, |(β₁ ω).fn y| ≤ M)
    (hle : ∀ w ∈ types, ∀ᵐ ω ∂P,
      ω ∈ wordTypeCell κ (-(Real.pi / 2)) (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) F w →
      S.V 0 ω ≤ FCDet.thr (typedRhoL w) (typedRhoR w) (S.ver 0).W
        (cellXL κ (-(Real.pi / 2)) (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) w)
        (cellXR κ (-(Real.pi / 2)) (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) w) ω)
    (hlife : ∀ w ∈ types, ∀ Wc : ℝ≥0 → Ω → ℝ, (∀ ω, Continuous fun t => Wc t ω) →
      ∀ᵐ ω ∂P, ω ∈ seedCell κ (-(Real.pi / 2)) (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) F w → relLife ω < ⊤ →
        (∀ m, ∀ t : ℝ≥0, (t : ℝ≥0∞) < S.V m ω → Wc t ω = (S.ver m).W t ω) →
        FCDet.thr (typedRhoL w) (typedRhoR w) Wc
          (cellXL κ (-(Real.pi / 2)) (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) w)
          (cellXR κ (-(Real.pi / 2)) (fun ω => BoundaryWord.shiftW (x₀ ω) (β₁ ω)) w) ω ≤ relLife ω) :
    ∀ᵐ ω ∂P, ω ∈ F →
      (∀ m, IsStopDrvMatch (driverCode (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13) hκ
        (-(Real.pi / 2)) (BoundaryWord.shiftW (x₀ ω) (β₁ ω),
          Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω)))
        (fun t => (S.ver m).W t ω) (S.V m ω)) ∧
      (driverCode (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13) hκ (-(Real.pi / 2))
        (BoundaryWord.shiftW (x₀ ω) (β₁ ω),
          Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 0 (chiC κ) (h ω))).2 = relLife ω := by
  obtain ⟨hBm, hBc, hBl, hloc⟩ := Cx.k2Inputs_of_rootSets h𝓖 hfam
  have hM : ∀ ω, ∀ y ∉ (BoundaryWord.shiftW (x₀ ω) (β₁ ω)).jumps,
      |(BoundaryWord.shiftW (x₀ ω) (β₁ ω)).fn y| ≤ M := fun ω y hy => by
    rw [BoundaryWord.fn_shiftW]
    refine hMβ ω (y + x₀ ω) fun hm => hy ?_
    rw [BoundaryWord.jumps_shiftW]
    exact Finset.mem_image.2 ⟨y + x₀ ω, hm, by ring⟩
  exact Cj.ae_k2_stage (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13) h13 hκ hh hu₀ S hKm hKc hKp
    hx₀m hc hFm htypes hcover hBm hBc hBl hloc
    (hmean_tail_obj h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ hleft hℓ hu₀ h𝓖 hfam S hKm hKc hKp hKF
      hx₀m hFm hpc htL hent hFae hc hsort hlaw hP8) hlaw hM0 hM hle hlife


omit [StandardBorelSpace Ω] [IsProbabilityMeasure P] in
/-- **Statement6's set premises from the root's line family** (`A₁ t` and the joint set `A₂J t` as filled versions):
the family `Cx.exists_rootLineFamily` is fed to `Cz.SB2LowerStageVersionStatement6` with `A₂ := A₂J`. -/
theorem stmt6Sets_of_rootSets {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {u : ℝ} {l : List (ℝ × ℝ≥0)} {k ℓ : ℕ}
    {u₀ : ℂ → ℝ} {A₁ A₂ A₂J : ℝ≥0 → Ω → Set ℂ}
    (hfam : ∀ t : ℝ≥0, RootSetsAt κ b jumps P h E u l k ℓ t u₀ (A₁ t) (A₂ t) (A₂J t)) :
    ∀ t : ℝ≥0, ∀ᵐ ω ∂P, A₁ t ω = fillVer (fun ω =>
        WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
          (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ ω)
        ω ∧
      A₂J t ω = fillVer (fun ω =>
        WalkLaw.stageSet κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ω ∪
        WalkLaw.stageSet κ b jumps (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ
          (-(Real.pi / 2)) (t : ℝ≥0∞)) (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true))
          (ℓ + 1) ω) ω := fun t => by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hform, -, -, -, -, -, hformJ, -⟩ := hfam t
  filter_upwards [hform, hformJ] with ω h1 h2
  exact ⟨h1.1, h2⟩

end InteractingSLE.Theorem14.SB.Ce
