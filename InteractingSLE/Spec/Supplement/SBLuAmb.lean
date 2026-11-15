/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBLuPath
import InteractingSLE.Spec.Supplement.SBLuWire
import InteractingSLE.Spec.Supplement.GW1WalkExitData
import InteractingSLE.Spec.Supplement.GW1WalkExitD4
import InteractingSLE.Spec.Supplement.GW1PieceSimpleMeas
import InteractingSLE.Spec.Sec4.Aux25Term

/-!
# SB3's stage input (I5) in the ambient setting, and R95's amended SB3

Packet PROVE-T14-SBLEAVES6. The almost-sure inputs of the deterministic `pinv_prefix_walk` for the lower walk of a
staged history, without the counterflow:

* `ae_injOn_trOf_walk`: the launched pieces' traces are injective through their lifetimes (Aux. lemma 25,
  `Theorem15.aux25Statement`, under the regular conditional law given the retained past; the event is Borel through
  GW1Z's separation at rational times `SepAt`);
* `ae_walkTipCoordinates_lower`: GW1's tip coordinates for the lower walk, from GW1's stage data on the right
  (`ae_walkStageData_right`, which needs only the left ambient bound — R95's `LowerLeftAdmissible` gives it), D.4's
  record geometry and `walkTipCoordinates_of_exteriorRecords`;
* **`sb3StagePathRStatement`**: (I5) holds, so **`sb3InductionGenRStatement_of_sb2`**: R95's amended SB3
  (Theorem 1.4's `hSB3`) from SB2(1) in GW1's ambient setting, Theorems 1.2–1.3 and the small-gap fibre cover.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H Hbar)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.LuM

open Lx Exist.Staged Exist.StagedLaw

section AE

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {right : Bool} {Ω : Type u} [mΩ : MeasurableSpace Ω]
  [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- **The launched pieces of a walk have injective traces** (Aux. lemma 25 under the conditional laws). -/
theorem ae_injOn_trOf_walk (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps)
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hS : IsStagedHistory κ b jumps P h (boundaryWalkSpec b jumps θ right) E)
    (hreg : ∀ k ω, IsRegularDriver (E k ω))
    (hR : StagedPiecesRegular κ b jumps P (boundaryWalkSpec b jumps θ right) E) (k : ℕ) :
    ∀ᵐ ω ∂P, (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) (fun j => E j ω) (k + 1)).2.2.2.1 k ≠
      none → InjOn (trOf (E k ω)) {t : ℝ≥0 | (t : ℝ≥0∞) ≤ (E k ω).2} := by
  set spec := boundaryWalkSpec b jumps θ right with hspec
  set L : Set Ω := {ω | (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k ≠ none} with hLdef
  have hL : MeasurableSet L := (runMeasStatement κ b jumps hb spec E hS.1 hreg k).1
  set Sep : Set Ω := {ω | GW1Z.SepAt (fun t => LP.traceAt t (E k ω).1) (E k ω).2} with hSep
  have hSepm : MeasurableSet Sep := measurableSet_setOfPred.2 (GW1Z.measurable_sepAt
    (A := fun t ω => LP.traceAt t (E k ω).1) (fun t => (LP.measurable_traceAt t).comp (measurable_fst.comp (hS.1 k)))
    (measurable_snd.comp (hS.1 k)))
  set G : Set Ω := Lᶜ ∪ Sep with hGdef
  have hG : MeasurableSet G := hL.compl.union hSepm
  have hRP := hR.ae_pieceRegular
  have hker : ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps spec E k) ω₀), ω ∈ G := by
    filter_upwards [ae_ae_run_eq (P := P) runMeasStatement hb spec (k := k) (fun j _ => hS.1 j)
      (fun j _ => hreg j), hS.2.2.2 k, KernelTower.ae_ae_condExpKernel_of_ae (hS.2.1 k) hRP]
      with ω₀ hrun hfl hreg₀
    rcases hl : (ExplState.run κ b jumps spec (fun j => E j ω₀) (k + 1)).2.2.2.1 k with _ | ⟨c, θ'⟩
    · filter_upwards [hrun] with ω hω
      refine Or.inl fun hωL => hωL ?_
      show (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k = none
      rw [congrFun (launches_run_succ_of_run_eq spec hω) k, hl]
    · obtain ⟨b', jumps', h', -, -, hfld⟩ := hfl c θ' hl
      obtain ⟨_, 𝓕, VL, VR, B, -, hC⟩ := hfld
      have hinj := Theorem15.aux25Statement κ hκ hκ4 _ _ _ _ (Theorem15.isOrderedForceWord_flowLine b' jumps' 0)
        _ 𝓕 _ VL VR B _ hC.1
      filter_upwards [hrun, hinj, hreg₀] with ω hω hinjω hregω
      have hlω : (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k = some (c, θ') := by
        rw [congrFun (launches_run_succ_of_run_eq spec hω) k, hl]
      have hPR := hregω k c θ' hlω
      rw [Lx.instrTime_boundaryWalk_of_launch hlω, min_top_left] at hPR
      have hα := isGeneratingTrace_trOf hPR
      exact Or.inr (show GW1Z.SepAt (fun t => LP.traceAt t (E k ω).1) (E k ω).2 from
        GW1Z.sepAt_of_injOn (A := fun t => LP.traceAt t (E k ω).1) hα.2.1
          (fun q hq => traceAt_eq_trOf (hreg k ω) hPR hq) (hinjω _ hα))
  filter_upwards [Sec5.Lemma56Stages.ae_of_ae_condExpKernel (hS.2.1 k) hG hker, hRP] with ω hω hregω hl
  obtain ⟨⟨c, θ'⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hl
  have hPR := hregω k c θ' hcθ
  rw [Lx.instrTime_boundaryWalk_of_launch hcθ, min_top_left] at hPR
  have hα := isGeneratingTrace_trOf hPR
  rcases hω with hω | hω
  · exact absurd hl hω
  · exact GW1Z.injOn_of_sepAt (A := fun t => LP.traceAt t (E k ω).1) hα.2.1
      (fun q hq => traceAt_eq_trOf (hreg k ω) hPR hq) hω

/-- **GW1's tip coordinates for the lower walk without the counterflow**: GW1's stage data on the right need only the
left ambient bound, which R95's premise gives. -/
theorem ae_walkTipCoordinates_lower (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) (hadm : Ly.LowerLeftAdmissible κ b jumps)
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : IsStagedHistory κ b jumps P h (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) E)
    (hreg : ∀ k ω, IsRegularDriver (E k ω))
    (hR : StagedPiecesRegular κ b jumps P (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) E) :
    ∀ᵐ ω ∂P, GW1WalkChain.WalkTipCoordinates κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => E j ω) := by
  have hamb : ∀ t, t < 0 → t ∉ jumps → b t + -(Real.pi / 2) * chiC κ < sleLambda κ :=
    fun t ht htJ => Ly.height_lt_of_cumWeightLeft hκ (hadm t ht htJ)
  filter_upwards [GW1WalkExit.ae_walkStageData_right hκ hb hh hS hreg hamb, hR.ae_pieceRegular] with ω hs hr
  have hgeo := GW1WalkExit.walk_recordGeometry hκ hb (fun j => E j ω) (fun j => hreg j ω) hs
    (fun k c θ' hl => hr k c θ' hl)
  exact GW1WalkFinish.walkTipCoordinates_of_exteriorRecords _ (fun k c θ' hl => hr k c θ' hl) hgeo.2

end AE

/-- **SB3's stage input (I5) in the ambient setting holds**: at every launch `k ≥ 1` of the lower walk the retained
prefix with the bridge `[u, 0]` is the image of a path with finite fibres from `u`. -/
theorem sb3StagePathRStatement : SB3StagePathRStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh hadm E hE hR hreg u ψ hu _ _ _ η ζ _ _ k hk
  have hspec := isBoundaryContinuedProgram_boundaryWalkSpec b jumps (θ := -(Real.pi / 2))
    ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  have hS := hE _ hspec
  have hRs := hR _ hspec
  filter_upwards [ae_walkTipCoordinates_lower hκ hb hh hadm hS (hreg _) hRs,
    ae_all_iff.2 fun j => ae_injOn_trOf_walk hκ hκ4 hb hS (hreg _) hRs j, hRs.ae_pieceRegular]
    with ω htip hinj hr hl
  have hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) := fun j c θ' hlj => hr j c θ' hlj
  obtain ⟨⟨c, θ'⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hl
  have hnot := WalkIntRunChron.not_done_of_launch _ _ hcθ
  obtain ⟨hpinv, -⟩ := pinv_prefix_walk hP (fun j hlj => hinj j hlj) htip hu k hnot
  rcases hpinv with h1 | h2
  · exfalso
    have hne := Lz.prefixPhysSet_ne_root_of_launch (κ := κ) (b := b) (jumps := jumps)
      (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (by omega) hl
    have h0 : (0 : ℂ) ∈ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) k :=
      Or.inl (Or.inl (by simp [boundaryWalkSpec]))
    have hsub : SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) k ⊆ {(u : ℂ)} :=
      h1 ▸ subset_union_left
    have hu0 : (u : ℂ) = 0 := (mem_singleton_iff.1 (hsub h0)).symm
    refine hne (Subset.antisymm ?_ ?_)
    · simpa [boundaryWalkSpec, hu0] using hsub
    · simpa [boundaryWalkSpec] using h0
  · exact h2

/-- **R95's amended SB3** (`Ly.SB3InductionGenRStatement`, Theorem 1.4's binder `hSB3`) from SB2(1) in GW1's
ambient setting, Theorems 1.2–1.3 and the small-gap fibre cover: the stage inputs (I2), (I2′), (I5) are proved. -/
theorem sb3InductionGenRStatement_of_sb2 (hSB2 : Ly.SB2UpperLaunchEntryLAmbStatement.{u})
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hDy : Sec5.Aux61Act.DyActFibreCoverOn.{u}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin)
    (hDy₀ : Sec5.Aux61Act.DyActFibreCoverOn.{0}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin) :
    Ly.SB3InductionGenRStatement.{u} :=
  sb3InductionGenRStatement_of_path hSB2 h12 h13 h12₀ h13₀ hDy hDy₀ sb3StagePathRStatement

end InteractingSLE.Theorem14.SB.LuM
