/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2CxRoot
import InteractingSLE.Spec.Supplement.SB2PqRoot

/-!
# The root's line mean with no open input (D74)

Packet PROVE-SB2-CONDFIN, round 13 (decision D74, item 1). NOTHR's post-head pull-back
(`Pq.ae_isStagePullback_postHead`, landed 38f7fab85) holds wherever an S2 configuration of the post-head chart
exists — on the cells at positive clock, not on all of B's capped launch. So:

* **`hmean_rootC`**: `Cx.hmean_root` with the stage data asked on any event `C t` inside B's capped launch with the
  entrance before `t` (same proof);
* **`hpull_cf`**: the stage-chart pull-back of the root's line family with the finite fibres discharged
  (`Ml.ae_finiteFibre_walk_cf`), NOTHR's `hpull`;
* **`hmean_root_obj`**: K2's `hmean` at the root (the JOINT union) for a root version over the root's line family,
  from Theorems 1.2–1.3, NOJUMP's root objects (`hF`, `hA₁`, `hK`, `hx₀`, `hpc`, `htL`, `hzero`: the inputs of SB2LIFT's
  landed `Sx.ae_isStageS2_root_of`) and F3's mean identity `hF3` (NOJUMP's Statement8 premise, read in the version's
  chart). The S2 clause (`Sx.ae_isStageS2_root_of` on the version's fields), the pull-back (NOTHR) and the cells'
  event are proved inside.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC fwdHull fwdMap logDerivFwd)
open QuantumZipper.RS (shiftDrive)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Cy

open Restart Exist Exist.Staged Exist.StagedLaw WalkSide LocalSets WholeField Mf Mk Cr Om Lv Ms Cx
open Supp8.Q3Stop Sec7.PocketTraversal Restart.DomainMarkov
open Supp8.Q3Chain (flowedData flowedJumps)

section Root

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- **The root's line mean on a chosen event** (`Cx.hmean_root` with the stage data asked on any event `C t` inside
B's capped launch with the entrance before `t`, which the cells at positive clock enter). -/
theorem hmean_rootC (h13 : Theorem13Statement.{u}) (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {u : ℝ} {l : List (ℝ × ℝ≥0)} {k ℓ : ℕ} {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {𝓖 : Filtration ℝ≥0 mΩ} {A₁ A₂ A₂J : ℝ≥0 → Ω → Set ℂ}
    (h𝓖 : ∀ t : ℝ≥0, 𝓖 t = pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
      pastSigma κ b jumps
        (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2)) (t : ℝ≥0∞))
        (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1))
    (hfam : ∀ t : ℝ≥0, RootSetsAt κ b jumps P h E u l k ℓ t u₀ (A₁ t) (A₂ t) (A₂J t))
    {Fr : Set Ω} {K : Ω → Set ℂ} {x₀ : Ω → ℝ} {β₁ : Ω → BoundaryWord} {types : Set WordType}
    {pc : Ω → ℝ≥0 → ℂ} {tL : Ω → ℝ≥0} {L relLife : Ω → ℝ≥0∞}
    (S : RootVersionS κ (-(Real.pi / 2)) P Fr 𝓖 A₁ A₂J (fun ω => Mo.hullChart (fillH (K ω)) (x₀ ω)) β₁ types pc tL
      L relLife)
    (hKc : ∀ ω, IsCompact (K ω)) (hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf))
    (hsort : ∀ ω, (β₁ ω).IsSorted)
    (hfill : ∀ t, ∀ᵐ ω ∂P, ω ∈ Fr → fillH (K ω) = A₁ t ω)
    (hF3 : ∀ t, ∀ g₁ : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean (A₁ t) (WholeField.centredField h u₀) P g₁ →
      ∀ᵐ ω ∂P, ω ∈ Fr → ∀ w₁ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₁ (H \ A₁ t ω) →
        (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₁ t ω → g₁ ω φ = ∫ z, w₁ z * φ z) →
        EqOn (fun z => w₁ z + u₀ z) (fun z => (β₁ ω).mean ((Mo.hullChart (fillH (K ω)) (x₀ ω)).1 z) -
          chiC κ * (Mo.hullChart (fillH (K ω)) (x₀ ω)).2.2 z) (H \ A₁ t ω))
    (τE : Ω → ℝ≥0) (C : ℝ≥0 → Set Ω)
    (hCsub : ∀ t ω, ω ∈ C t → ω ∈ capEvent κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ t ∧ τE ω ≤ t)
    (hC : ∀ m, ∀ w ∈ types, ∀ t, ∀ᵐ ω ∂P, ω ∈ seedCell κ (-(Real.pi / 2)) β₁ Fr w →
      (S.ver m).a t ω < (S.ver m).Λ w ω → 0 < (S.ver m).a t ω → ω ∈ C t)
    (hpb : ∀ t, ∀ᵐ ω ∂P, ω ∈ C t →
      ∃ gb : ℂ → ℂ, Ln.IsStagePullback (phChart κ E b jumps ℓ τE ω) gb (A₁ t ω) (A₂ t ω)
        {z | (phChart κ E b jumps ℓ τE ω).2.1 z ∈ A₁ t ω}
        (fwdHull (phDrv E b jumps ℓ τE t ω) (phTime E b jumps ℓ τE t ω)))
    (hS2 : ∀ m, ∀ w ∈ types, ∀ t, ∀ᵐ ω ∂P, ω ∈ seedCell κ (-(Real.pi / 2)) β₁ Fr w →
      (S.ver m).a t ω < (S.ver m).Λ w ω → 0 < (S.ver m).a t ω →
      IsStageS2 (phChart κ E b jumps ℓ τE ω) (Mo.hullChart (fillH (K ω)) (x₀ ω)) (A₁ t ω) (phDrv E b jumps ℓ τE t ω)
        (phTime E b jumps ℓ τE t ω) (fun s : ℝ => (S.ver m).W s.toNNReal ω) ((S.ver m).a t ω).toNNReal) :
    ∀ g : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens,
      (∀ t, IsLocalSetMean (fun ω => A₁ t ω ∪ A₂J t ω) (WholeField.centredField h u₀) P (g t)) →
      ∀ m, ∀ w ∈ types, ∀ (t : ℝ≥0) (φ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P,
        ω ∈ seedCell κ (-(Real.pi / 2)) β₁ Fr w → 0 < (S.ver m).a t ω → (S.ver m).a t ω < (S.ver m).Λ w ω →
        Disjoint (tsupport φ) (fwdHull (fun s : ℝ => (S.ver m).W s.toNNReal ω) ((S.ver m).a t ω).toNNReal) →
        Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 (-(Real.pi / 2) * chiC κ) (chiC κ)
            (g t ω + (h ω - WholeField.centredField h u₀ ω)) φ =
          ∫ z, couplingMean κ (fun s : ℝ => (S.ver m).W s.toNNReal ω) ((S.ver m).a t ω).toNNReal
            (bheProc κ (typedRhoL w) (typedRhoR w) (S.ver m).W (geomLW (S.ver m).W (cellXL κ (-(Real.pi / 2)) β₁ w))
              (geomRW (S.ver m).W (cellXR κ (-(Real.pi / 2)) β₁ w)) ω ((S.ver m).a t ω).toNNReal) z * φ z := by
  classical
  intro g hg m w hw t φ
  have hh0 := Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hh hu₀
  -- the stage charts of B's regularized walk are a.s. conformal
  obtain ⟨hE', hreg', -⟩ := StagedReg.regFam_spec hb hE hER
  have hθ : -(Real.pi / 2) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hw' := isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ true
  have hRw := stagedPiecesRegular_of_regular h13 hκ hb (hE' _ hw') (hreg' _)
  have hconf : ∀ᵐ ω ∂P, (Mi.sb2StageChart κ E b jumps (-(Real.pi / 2)) true ℓ ω).IsConformal := by
    filter_upwards [GW1W.regLaunches_of_stagedPiecesRegular hRw] with ω hω
    exact SB.LuM.isConformal_runChart_of_reg _ hω ℓ
  -- the explored mean of B's own set, read in the post-head chart
  have hind₂ : ∀ t', ∀ g₂ : Ω → DistOn upperHalfPlaneOpens,
      IsLocalSetMean (A₂ t') (WholeField.centredField h u₀) P g₂ →
      ∃ GE : Ω → ℂ → ℝ, ∀ᵐ ω ∂P, ω ∈ C t' →
        (∃ (nL' nR' : ℕ) (ρL' : Fin nL' → ℝ) (ρR' : Fin nR' → ℝ) (xL' : Fin nL' → ℝ) (xR' : Fin nR' → ℝ),
          (∀ i, xL' i ≤ 0) ∧ (∀ j, 0 ≤ xR' j) ∧
          ∀ G : ℂ → ℝ, IsBoundedHarmonicExtension
              (flowedData κ ρL' ρR' xL' xR' (phDrv E b jumps ℓ τE t' ω) (phTime E b jumps ℓ τE t' ω))
              (flowedJumps xL' xR' (phDrv E b jumps ℓ τE t' ω) (phTime E b jumps ℓ τE t' ω)) G →
            EqOn G (fun z => GE ω z + -(Real.pi / 2) * chiC κ) H) ∧
        ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ A₂ t' ω) →
          (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₂ t' ω → g₂ ω φ = ∫ z, v z * φ z) →
          EqOn (fun z => v z + u₀ z) (fun z => GE ω (fwdMap (phDrv E b jumps ℓ τE t' ω) (phTime E b jumps ℓ τE t' ω)
              ((phChart κ E b jumps ℓ τE ω).1 z)) -
            chiC κ * ((logDerivFwd (phDrv E b jumps ℓ τE t' ω) (phTime E b jumps ℓ τE t' ω)
              ((phChart κ E b jumps ℓ τE ω).1 z)).im + (phChart κ E b jumps ℓ τE ω).2.2 z)) (H \ A₂ t' ω) := by
    intro t' g₂ hg₂
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hcl, -, hmean₂, -⟩ := hfam t'
    obtain ⟨β, hβ⟩ := hmean₂ g₂ hg₂
    refine ⟨fun ω => (stopWord κ (β ω, -(Real.pi / 2), recOf (t' : ℝ≥0∞)
      (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω))).mean, ?_⟩
    filter_upwards [hβ, hcl, hconf] with ω hβω hclω hcω hCω
    obtain ⟨hcap, hτt⟩ := hCsub t' ω hCω
    obtain ⟨hWc, hW0, hVc, hVW, hτtime, htime, hrw, hrt⟩ :=
      stop_facts (StagedReg.isRegularDriver_regHist ℓ ω) hτt hcap.2
    obtain ⟨-, hcorr, hdom⟩ := hclω hcap
    have hτs : ((τE ω : ℝ≥0) : ℝ) ≤ Mi.sb2StopTime E b jumps (-(Real.pi / 2)) true ℓ t' ω := by
      exact (show ((τE ω : ℝ≥0) : ℝ) ≤ (t' : ℝ) by exact_mod_cast hτt).trans_eq htime.symm
    obtain ⟨hdata, hform⟩ := postHead_explored (κ := κ) (θ := -(Real.pi / 2)) (W :=
      Mi.sb2StopDrv E b jumps (-(Real.pi / 2)) true ℓ t' ω) (V := Mi.sb2StopDrv E b jumps (-(Real.pi / 2)) true ℓ
      (τE ω) ω) (s := Mi.sb2StopTime E b jumps (-(Real.pi / 2)) true ℓ t' ω) hWc hW0 hVc (τE ω).coe_nonneg hτs
      hVW hrw hrt hcω hdom hcorr
    have hph : phChart κ E b jumps ℓ τE ω = (Mi.sb2StageChart κ E b jumps (-(Real.pi / 2)) true ℓ ω).loewner
        (Mi.sb2StopDrv E b jumps (-(Real.pi / 2)) true ℓ (τE ω) ω) ((τE ω : ℝ≥0) : ℝ) := by
      unfold phChart
      rw [show Mi.sb2StopTime E b jumps (-(Real.pi / 2)) true ℓ (τE ω) ω = ((τE ω : ℝ≥0) : ℝ) from hτtime]
    refine ⟨hdata, fun v hv hvφ z hz => ?_⟩
    rw [hβω hcap v hv hvφ hz, hph]
    exact hform z hz
  -- B's own union mean (the engine in the post-head chart)
  obtain ⟨hA₁m0, hA₂m0, hd₁0, hl₁0, hl₂0, hlU0, hUm0, hUloc0, hc₁0, hc₂0, hform0, -, -, -, -, -, hformJ0, -, -, -,
    hJm0, hJc0, -, hJloc0⟩ := hfam t
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
  have hB := ae_lineMean_pos_rootG (κ := κ) hκ hh hu₀ S hKc hKp hsort (fun t' => (hfam t').1)
    (fun t' => (hfam t').2.1) (fun t' => (hfam t').2.2.1) (fun t' => (hfam t').2.2.2.1)
    (fun t' => (hfam t').2.2.2.2.1) (fun t' => (hfam t').2.2.2.2.2.1)
    (fun t' => (hfam t').2.2.2.2.2.2.2.2.2.2.2.1) (fun t' => (hfam t').2.2.2.2.2.2.2.2.2.2.2.2.1)
    (c := phChart κ E b jumps ℓ τE) (wB := phDrv E b jumps ℓ τE) (sB := phTime E b jumps ℓ τE)
    (C := C) hpb hind₂ hfill hF3 hC hS2 gB hgB m w hw t
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
  have hJ := Cs.hmean_joint_of_hmeanB hh0 hKc hKp (S.ver m) hw t hXH hYH
    (hform0.mono fun ω h => h.1) (hform0.mono fun ω h => h.2) (by rw [hXY]; exact hformJ0)
    (by rw [h𝓖 t]; exact hUm0) (by rw [h𝓖 t]; exact hJm0) (hcU t) hJc0 (by rw [h𝓖 t]; exact hUloc0)
    (by rw [h𝓖 t]; exact hJloc0) (hgB t) (hg t) (fun ω => h ω - WholeField.centredField h u₀ ω)
    (-(Real.pi / 2) * chiC κ) (chiC κ) (fun ω => ∫ z, couplingMean κ (fun s : ℝ => (S.ver m).W s.toNNReal ω)
      ((S.ver m).a t ω).toNNReal (bheProc κ (typedRhoL w) (typedRhoR w) (S.ver m).W
        (geomLW (S.ver m).W (cellXL κ (-(Real.pi / 2)) β₁ w)) (geomRW (S.ver m).W (cellXR κ (-(Real.pi / 2)) β₁ w))
        ω ((S.ver m).a t ω).toNNReal) z * φ z) φ (by
      filter_upwards [hB] with ω h1 hcell hpos hlt hdis
      exact h1 hcell hlt hpos φ hdis)
  exact hJ

open Mi in
/-- **The stage-chart pull-back of the root's line family**, the finite fibres of B's boundary maps discharged
(`Ml.ae_finiteFibre_walk_cf`): NOTHR's `hpull`. -/
theorem hpull_cf (h13 : Theorem13Statement.{u}) (h13₀ : Theorem13Statement.{0}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {u : ℝ} {l : List (ℝ × ℝ≥0)} {k ℓ : ℕ} {u₀ : ℂ → ℝ} {A₁ A₂ A₂J : ℝ≥0 → Ω → Set ℂ}
    (hfam : ∀ t : ℝ≥0, RootSetsAt κ b jumps P h E u l k ℓ t u₀ (A₁ t) (A₂ t) (A₂J t)) (t : ℝ≥0) :
    ∀ᵐ ω ∂P, ω ∈ capEvent κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ t →
      (ExplState.run κ b jumps (Lu.upperSpec u l)
        (fun j => StagedReg.regFam E (Lu.upperSpec u l) j ω) (k + 1)).2.2.2.1 k ≠ none →
      ∃ g : ℂ → ℂ, Ln.IsStagePullback (sb2StageChart κ E b jumps (-(Real.pi / 2)) true ℓ ω) g (A₁ t ω) (A₂ t ω)
        {w | (sb2StageChart κ E b jumps (-(Real.pi / 2)) true ℓ ω).2.1 w ∈ A₁ t ω}
        (fwdHull (sb2StopDrv E b jumps (-(Real.pi / 2)) true ℓ t ω)
          (sb2StopTime E b jumps (-(Real.pi / 2)) true ℓ t ω)) := by
  obtain ⟨hE', hreg', -⟩ := StagedReg.regFam_spec hb hE hER
  have hθ : -(Real.pi / 2) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hw := isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ true
  have hRw := stagedPiecesRegular_of_regular h13 hκ hb (hE' _ hw) (hreg' _)
  have hfib := Ml.ae_finiteFibre_walk_cf h13₀ hκ hκ4 hb hh hcf hζ' (hE' _ hw) (hreg' _) hRw
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hpull, -⟩ := hfam t
  filter_upwards [hpull, hfib] with ω hp hfω hcap hlu
  obtain ⟨g, hgc, hgi, hpb⟩ := hp hcap hlu
  obtain ⟨⟨c₀, θ₀⟩, hl⟩ := Option.ne_none_iff_exists'.1 hcap.1
  exact ⟨g, hpb (hfω ℓ (WalkIntRunChron.not_done_of_launch _ _ hl) g hgc hgi)⟩

/-- **K2's `hmean` at the root with no open input** (D74): for a root version over the root's line family
(`Cx.exists_rootLineFamily`), from Theorems 1.2–1.3, NOJUMP's root objects (the inputs of SB2LIFT's
`Sx.ae_isStageS2_root_of`) and F3's mean identity in the version's chart. -/
theorem hmean_root_obj (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {u : ℝ} {l : List (ℝ × ℝ≥0)} {k ℓ : ℕ} (hu : u ≤ 0) (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2))
    (hleft : ∀ᵐ ω ∂P, ω ∈ Lu.upperLaunchSet κ b jumps E u l k →
      upperPrefix κ b jumps E u l k ω ∩ rightSideOf (lowerWalkSet κ b jumps E ω) = ∅)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀)
    {𝓖 : Filtration ℝ≥0 mΩ} {A₁ A₂ A₂J : ℝ≥0 → Ω → Set ℂ}
    (h𝓖 : ∀ t : ℝ≥0, 𝓖 t = pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
      pastSigma κ b jumps
        (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2)) (t : ℝ≥0∞))
        (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1))
    (hfam : ∀ t : ℝ≥0, RootSetsAt κ b jumps P h E u l k ℓ t u₀ (A₁ t) (A₂ t) (A₂J t))
    {Fr : Set Ω} {K : Ω → Set ℂ} {x₀ : Ω → ℝ} {β₁ : Ω → BoundaryWord} {types : Set WordType}
    {pc : Ω → ℝ≥0 → ℂ} {tL : Ω → ℝ≥0} {relLife : Ω → ℝ≥0∞}
    (S : RootVersionS κ (-(Real.pi / 2)) P Fr 𝓖 A₁ A₂J (fun ω => Mo.hullChart (fillH (K ω)) (x₀ ω)) β₁ types pc tL
      (fun ω => (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2) relLife)
    (hKc : ∀ ω, IsCompact (K ω)) (hKp : ∀ ω, IsPreconnected (K ω ∪ Restart.lowerHalf))
    (hsort : ∀ ω, (β₁ ω).IsSorted)
    (hF : ∀ᵐ ω ∂P, ω ∈ Fr → ω ∈ stageEvent κ b jumps E u l k ℓ ∧
      Lk.relOff κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω)) (fun i => E (boundaryWalkSpec b
        jumps (-(Real.pi / 2)) true) i ω) = ℓ ∧
      ¬ Lk.ZeroRoot κ (-(Real.pi / 2)) b jumps (realMax (upperPrefix κ b jumps E u l k ω))
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω))
    (hA₁ : ∀ t, ∀ᵐ ω ∂P, ω ∈ Fr → A₁ t ω = fillH (K ω))
    (hK : ∀ᵐ ω ∂P, ω ∈ Fr → fillH (K ω) = fillH (upperPrefix κ b jumps E u l k ω ∪ SB.prefixPhysSet κ b jumps
      (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i
      ω) ℓ))
    (hx₀ : ∀ᵐ ω ∂P, ω ∈ Fr →
      IsRightEntryChart (upperPrefix κ b jumps E u l k ω ∪ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps
        (-(Real.pi / 2)) true) (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) ℓ) (realMax
        (upperPrefix κ b jumps E u l k ω ∪ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2))
        true) (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) ℓ)) ((Mo.hullChart (fillH
        (upperPrefix κ b jumps E u l k ω ∪ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2))
        true) (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) ℓ)) 0).recenter (x₀ ω)))
    (hpc : ∀ ω, pc ω = Lk.pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (fun i => E
      (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) ℓ) (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω))
    (htL : ∀ ω, tL ω = Na.rootEntry κ b jumps E u l k ℓ ω)
    (hzero : ∀ m, ∀ᵐ ω ∂P, ω ∈ Fr → (S.ver m).a (Na.rootEntry κ b jumps E u l k ℓ ω) ω = 0)
    (hF3 : ∀ t, ∀ g₁ : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean (A₁ t) (WholeField.centredField h u₀) P g₁ →
      ∀ᵐ ω ∂P, ω ∈ Fr → ∀ w₁ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₁ (H \ A₁ t ω) →
        (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₁ t ω → g₁ ω φ = ∫ z, w₁ z * φ z) →
        EqOn (fun z => w₁ z + u₀ z) (fun z => (β₁ ω).mean ((Mo.hullChart (fillH (K ω)) (x₀ ω)).1 z) -
          chiC κ * (Mo.hullChart (fillH (K ω)) (x₀ ω)).2.2 z) (H \ A₁ t ω)) :
    ∀ g : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens,
      (∀ t, IsLocalSetMean (fun ω => A₁ t ω ∪ A₂J t ω) (WholeField.centredField h u₀) P (g t)) →
      ∀ m, ∀ w ∈ types, ∀ (t : ℝ≥0) (φ : TestOn upperHalfPlaneOpens), ∀ᵐ ω ∂P,
        ω ∈ seedCell κ (-(Real.pi / 2)) β₁ Fr w → 0 < (S.ver m).a t ω → (S.ver m).a t ω < (S.ver m).Λ w ω →
        Disjoint (tsupport φ) (fwdHull (fun s : ℝ => (S.ver m).W s.toNNReal ω) ((S.ver m).a t ω).toNNReal) →
        Chart.chartTransport (Mu.isConformal_canon x₀ hKc hKp ω) 1 (-(Real.pi / 2) * chiC κ) (chiC κ)
            (g t ω + (h ω - WholeField.centredField h u₀ ω)) φ =
          ∫ z, couplingMean κ (fun s : ℝ => (S.ver m).W s.toNNReal ω) ((S.ver m).a t ω).toNNReal
            (bheProc κ (typedRhoL w) (typedRhoR w) (S.ver m).W (geomLW (S.ver m).W (cellXL κ (-(Real.pi / 2)) β₁ w))
              (geomRW (S.ver m).W (cellXR κ (-(Real.pi / 2)) β₁ w)) ω ((S.ver m).a t ω).toNNReal) z * φ z := by
  classical
  set τE : Ω → ℝ≥0 := fun ω => Na.rootEntry κ b jumps E u l k ℓ ω with hτEdef
  obtain ⟨-, -, hrun⟩ := StagedReg.regFam_spec hb hE hER
  have hθ : -(Real.pi / 2) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hw' := isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ true
  have hsu := Lu.isBoundaryContinuedProgram_upperSpec (u := u) hlθ
  -- SB2LIFT's post-head S2 clause on the version's fields
  have hS2 : ∀ m, ∀ w ∈ types, ∀ t, ∀ᵐ ω ∂P, ω ∈ seedCell κ (-(Real.pi / 2)) β₁ Fr w →
      (S.ver m).a t ω < (S.ver m).Λ w ω → 0 < (S.ver m).a t ω →
      IsStageS2 (phChart κ E b jumps ℓ τE ω) (Mo.hullChart (fillH (K ω)) (x₀ ω)) (A₁ t ω) (phDrv E b jumps ℓ τE t ω)
        (phTime E b jumps ℓ τE t ω) (fun s : ℝ => (S.ver m).W s.toNNReal ω) ((S.ver m).a t ω).toNNReal :=
    fun m w hw t => Sx.ae_isStageS2_root_of h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ hleft
      (C := seedCell κ (-(Real.pi / 2)) β₁ Fr w) (Λ := (S.ver m).Λ w) (S.ver m).W_cont (S.ver m).W_zero
      (S.ver m).clock_cont (S.ver m).clock_mono (S.ver m).clock_zero (fun _ hω => hω.1.1) (hzero m)
      ((S.ver m).trace w hw) ((S.ver m).alive w hw) hF hA₁ hK hx₀ hpc htL t
  -- the event of the stage data: B's capped launch, the entrance before `t`, the upper launch and an S2 configuration
  set C : ℝ≥0 → Set Ω := fun t => {ω | (ω ∈ capEvent κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ t ∧ τE ω ≤ t) ∧
    (ExplState.run κ b jumps (Lu.upperSpec u l)
      (fun j => StagedReg.regFam E (Lu.upperSpec u l) j ω) (k + 1)).2.2.2.1 k ≠ none ∧
    ∃ (Φ : Chart) (wB : ℝ → ℝ) (sB : ℝ) (W : ℝ → ℝ) (u' : ℝ),
      IsStageS2 (phChart κ E b jumps ℓ τE ω) Φ (A₁ t ω) wB sB W u' ∧ H \ A₁ t ω ⊆ Φ.2.1 '' H} with hCdef
  have hpb : ∀ t, ∀ᵐ ω ∂P, ω ∈ C t →
      ∃ gb : ℂ → ℂ, Ln.IsStagePullback (phChart κ E b jumps ℓ τE ω) gb (A₁ t ω) (A₂ t ω)
        {z | (phChart κ E b jumps ℓ τE ω).2.1 z ∈ A₁ t ω}
        (fwdHull (phDrv E b jumps ℓ τE t ω) (phTime E b jumps ℓ τE t ω)) := fun t => by
    have hG := Pq.ae_isStagePullback_postHead h13 h13₀ hκ hκ4 hb hh hcf hζ' hE hER ℓ t (A₁ := A₁ t) (A₂ := A₂ t)
      (G := {ω | ω ∈ capEvent κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ t ∧
        (ExplState.run κ b jumps (Lu.upperSpec u l)
          (fun j => StagedReg.regFam E (Lu.upperSpec u l) j ω) (k + 1)).2.2.2.1 k ≠ none})
      ((hpull_cf h13 h13₀ hκ hκ4 hb hh hcf hζ' hE hER hfam t).mono fun ω h hGω => h hGω.1 hGω.2) τE
    filter_upwards [hG] with ω h1 hC
    exact h1 ⟨hC.1.1, hC.2.1⟩ hC.1.1 hC.1.2 hC.2.2
  -- the cells at positive clock enter `C t`
  have hC : ∀ m, ∀ w ∈ types, ∀ t, ∀ᵐ ω ∂P, ω ∈ seedCell κ (-(Real.pi / 2)) β₁ Fr w →
      (S.ver m).a t ω < (S.ver m).Λ w ω → 0 < (S.ver m).a t ω → ω ∈ C t := fun m w hw t => by
    filter_upwards [hS2 m w hw t, (S.ver m).alive w hw t, hF, hA₁ t, hzero m, hrun _ hw', hrun _ hsu]
      with ω hS2ω halω hFω hA₁ω hzeroω hrw hru hcell hlt hpos
    have hωF : ω ∈ Fr := hcell.1.1
    obtain ⟨⟨hup, hlaunch⟩, -, -⟩ := hFω hωF
    have hcap : ω ∈ capEvent κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ t := by
      refine ⟨?_, ?_⟩
      · show (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (fun j =>
          StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none
        rw [hrw (ℓ + 1)]
        exact hlaunch
      · have hsnd : (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 =
            (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 := StagedReg.regularize_snd _ _
        rw [hsnd]
        exact halω hcell hlt
    have hτt : τE ω ≤ t := by
      by_contra hcon
      have h1 : (S.ver m).a t ω ≤ (S.ver m).a (τE ω) ω := (S.ver m).clock_mono ω (le_of_lt (not_le.1 hcon))
      rw [show (S.ver m).a (τE ω) ω = 0 from hzeroω hωF] at h1
      exact absurd (hpos.trans_le h1) (lt_irrefl _)
    refine ⟨⟨hcap, hτt⟩, by rw [hru (k + 1)]; exact hup, Mo.hullChart (fillH (K ω)) (x₀ ω), _, _, _, _,
      hS2ω hcell hlt hpos, ?_⟩
    rw [hA₁ω hωF]
    exact Pq.subset_image_hullChart (Mo.isHPHull_fillH hKc hKp ω) (x₀ ω)
  exact hmean_rootC h13 hκ hb hh hE hER hu₀ h𝓖 hfam S hKc hKp hsort
    (fun t => (hA₁ t).mono fun ω h hω => (h hω).symm) hF3 τE C (fun t ω hω => hω.1) hC hpb hS2

end Root

end InteractingSLE.Theorem14.SB.Cy
