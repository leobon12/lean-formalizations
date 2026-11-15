/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2MkFib
import InteractingSLE.Spec.Supplement.SB2MkLine
import InteractingSLE.Spec.Supplement.GW1ConnectorFirst
import InteractingSLE.Spec.Supplement.BR3Ref

/-!
# SB2(2)'s stage pull-back in SB2(2)'s own setting: the finite fibres from the counterflow

Packet PROVE-SB2-LCMEAN, round 9. Round 8 proved `Ln.IsStagePullback` for SB2(2)'s sets except its finite-fibre clause
`gf`, outright only under R95's `Ly.LowerLeftAdmissible`. The landed path route (`LuM.pinv_prefix_walk`,
`Lk.finite_fibre_of_pinv`) uses that premise only through GW1's tip coordinates of the lower walk, which in turn need
only GW1's ambient bound `b t − (π/2)χ < λ` for `t < 0`. SB2(2)'s setting (`Lf.SB2LowerSetting`) carries the complete
centred counterflow (`ζ' = ⊤` almost surely), which supplies that bound (`GW1Conn.ambient_bounds`, with GW0's forward
statement from Theorem 1.3 at universe `0`):

* `ae_walkTipCoordinates_amb`: GW1's tip coordinates of the lower walk from the ambient bound alone;
* `ae_finiteFibre_walk_amb`, **`ae_finiteFibre_walk_cf`**: almost surely, at every unfinished stage of the lower walk,
  every continuous extension to `ℍ̄` of the inverse run chart has finite fibres — from the ambient bound, resp. in the
  counterflow setting;
* **`exists_sb2LineFamily_cf`**: round 8's line family (`Mk.exists_sb2LineFamily_fill`) in the counterflow setting,
  with the stage pull-back **outright**: almost surely on the capped launch event at an upper launch,
  `∃ g, Ln.IsStagePullback (sb2StageChart …) g (A₁ t ω) (A₂ t ω) {w | c.2.1 w ∈ A₁ t ω} (fwdHull …)`.

R48: Theorems 1.2–1.3 appear only as hypotheses (Theorem 1.4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar chiC fwdMap fwdHull logDerivFwd)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Ml

open Restart Exist Exist.Staged Exist.StagedLaw WalkSide LocalSets WholeField Mf Mk

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}

/-- **GW1's tip coordinates of the lower walk from the ambient bound alone** (`LuM.ae_walkTipCoordinates_lower` uses
`Ly.LowerLeftAdmissible` only through this bound). -/
theorem ae_walkTipCoordinates_amb (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hamb : ∀ t, t < 0 → t ∉ jumps → b t + -(Real.pi / 2) * chiC κ < sleLambda κ)
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : IsStagedHistory κ b jumps P h (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) E)
    (hreg : ∀ k ω, IsRegularDriver (E k ω))
    (hR : StagedPiecesRegular κ b jumps P (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) E) :
    ∀ᵐ ω ∂P, GW1WalkChain.WalkTipCoordinates κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun j => E j ω) := by
  filter_upwards [GW1WalkExit.ae_walkStageData_right hκ hb hh hS hreg hamb, hR.ae_pieceRegular] with ω hs hr
  have hgeo := GW1WalkExit.walk_recordGeometry hκ hb (fun j => E j ω) (fun j => hreg j ω) hs
    (fun k c θ' hl => hr k c θ' hl)
  exact GW1WalkFinish.walkTipCoordinates_of_exteriorRecords _ (fun k c θ' hl => hr k c θ' hl) hgeo.2

/-- **Finite fibres of the lower walk's boundary maps from the ambient bound.** -/
theorem ae_finiteFibre_walk_amb (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps)
    (hamb : ∀ t, t < 0 → t ∉ jumps → b t + -(Real.pi / 2) * chiC κ < sleLambda κ)
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : IsStagedHistory κ b jumps P h (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) E)
    (hreg : ∀ k ω, IsRegularDriver (E k ω))
    (hR : StagedPiecesRegular κ b jumps P (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) E) :
    ∀ᵐ ω ∂P, ∀ n : ℕ,
      stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (fun j => E j ω) n) ≠
        GW1Conn.stDone →
      ∀ g : ℂ → ℂ, ContinuousOn g Hbar →
        EqOn g (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun j => E j ω) n).2.2.2.2.1.2.1 H →
        ∀ z, (g ⁻¹' {z} ∩ Hbar).Finite := by
  filter_upwards [ae_walkTipCoordinates_amb hκ hb hh hamb hS hreg hR,
    ae_all_iff.2 fun j => LuM.ae_injOn_trOf_walk hκ hκ4 hb hS hreg hR j, hR.ae_pieceRegular]
    with ω htip hinj hr n hnot g hgc hgi
  obtain ⟨-, gc, C, hD, -, -, -, hgcc, hgci, ⟨C₁, C₂, hC₁, hgb⟩, -, -⟩ :=
    S3.Canon.runChart_package (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (fun j => E j ω) hr n hnot
  have hgg : EqOn g gc Hbar := eqOn_Hbar_of_eqOn_H hgc hgcc fun w hw => (hgi hw).trans (hgci hw).symm
  have hgb' : ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ ∀ w : ℂ, 0 ≤ w.im → ‖w‖ ≤ C₁ * ‖g w‖ + C₂ :=
    ⟨C₁, C₂, hC₁, fun w hw => by rw [hgg (show w ∈ Hbar from hw)]; exact hgb w hw⟩
  exact Lk.finite_fibre_of_pinv (LuM.pinv_prefix_walk (fun j c θ' hlj => hr j c θ' hlj)
    (fun j hlj => hinj j hlj) htip le_rfl n hnot).1 hD hgc hgi hgb'

/-- **Finite fibres of the lower walk's boundary maps in the counterflow setting** (Theorem 1.4's and SB2(2)'s): the
ambient bound from the complete centred counterflow. -/
theorem ae_finiteFibre_walk_cf (h13₀ : Theorem13Statement.{0}) (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsPiecewiseConstantBoundaryData b jumps) (hh : IsGFFWithBoundaryData P h b jumps)
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ P h W' ζ')
    (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤) {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hS : IsStagedHistory κ b jumps P h (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) E)
    (hreg : ∀ k ω, IsRegularDriver (E k ω))
    (hR : StagedPiecesRegular κ b jumps P (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) E) :
    ∀ᵐ ω ∂P, ∀ n : ℕ,
      stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (fun j => E j ω) n) ≠
        GW1Conn.stDone →
      ∀ g : ℂ → ℂ, ContinuousOn g Hbar →
        EqOn g (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun j => E j ω) n).2.2.2.2.1.2.1 H →
        ∀ z, (g ⁻¹' {z} ∩ Hbar).Finite :=
  ae_finiteFibre_walk_amb hκ hκ4 hb hh
    (GW1Conn.ambient_bounds (BR3Ref.gw0ForwardStatement_of_theorem13 h13₀) hκ hκ4 hb hh hcf hζ').1 hS hreg hR

open Mi in
/-- **SB2(2)'s line family with the stage pull-back outright, in SB2(2)'s counterflow setting**: round 8's
`Mk.exists_sb2LineFamily_fill` with the finite fibres of the boundary map supplied by `ae_finiteFibre_walk_cf`. -/
theorem exists_sb2LineFamily_cf (h12p : Theorem12ParamStatement.{u}) (h13 : Theorem13Statement.{u})
    (h13₀ : Theorem13Statement.{0})
    (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    {u : ℝ} {l : List (ℝ × ℝ≥0)} (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2)) (k ℓ : ℕ)
    (hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length)
    (hwℓ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤)))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) :
    ∃ (𝓖 : Filtration ℝ≥0 mΩ) (A₁ A₂ : ℝ≥0 → Ω → Set ℂ),
      (∀ t : ℝ≥0, 𝓖 t = pastSigma κ b jumps (Lu.upperSpec u l) (StagedReg.regFam E (Lu.upperSpec u l)) k ⊔
          pastSigma κ b jumps
            (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2)) (t : ℝ≥0∞))
            (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) (ℓ + 1)) ∧
      ∀ t : ℝ≥0,
        Measurable[mΩ, hittingSigma] (A₁ t) ∧ Measurable[mΩ, hittingSigma] (A₂ t) ∧
        Measurable[mΩ, hittingSigma] (fun ω => A₁ t ω ∪ A₂ t ω) ∧
        MeasurableSpace.comap (A₁ t) hittingSigma ≤
          aeSigma (MeasurableSpace.comap (centredField h u₀) inferInstance) P ∧
        (∀ ω, A₁ t ω ⊆ H ∧ IsOpen (H \ A₁ t ω)) ∧ (∀ ω, A₂ t ω ⊆ H ∧ IsOpen (H \ A₂ t ω)) ∧
        (∀ ω, A₁ t ω ∪ A₂ t ω ⊆ H ∧ IsOpen (H \ (A₁ t ω ∪ A₂ t ω))) ∧
        IsLocalSet (A₁ t) (centredField h u₀) P ∧ IsLocalSet (A₂ t) (centredField h u₀) P ∧
        IsLocalSet (fun ω => A₁ t ω ∪ A₂ t ω) (centredField h u₀) P ∧
        IsHistoryAvoidanceLocal (𝓖 t) (fun ω => A₁ t ω ∪ A₂ t ω) (centredField h u₀) P ∧
        (∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (A₁ t ω),
          ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (A₁ t ω)) z)) ∧
        (∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (A₂ t ω),
          ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (A₂ t ω)) z)) ∧
        (∀ᵐ ω ∂P, ω ∈ capEvent κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ t →
          (∀ v ∈ H, (sb2StageChart κ E b jumps (-(Real.pi / 2)) true ℓ ω).2.1 v ∈ A₂ t ω ↔
            v ∈ fwdHull (sb2StopDrv E b jumps (-(Real.pi / 2)) true ℓ t ω)
              (sb2StopTime E b jumps (-(Real.pi / 2)) true ℓ t ω)) ∧
          H \ ((sb2StageChart κ E b jumps (-(Real.pi / 2)) true ℓ ω).dom : Set ℂ) ⊆ A₂ t ω) ∧
        (∀ᵐ ω ∂P, ω ∈ capEvent κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ t →
          (ExplState.run κ b jumps (Lu.upperSpec u l)
            (fun j => StagedReg.regFam E (Lu.upperSpec u l) j ω) (k + 1)).2.2.2.1 k ≠ none →
          ∃ g : ℂ → ℂ,
            Ln.IsStagePullback (sb2StageChart κ E b jumps (-(Real.pi / 2)) true ℓ ω) g (A₁ t ω) (A₂ t ω)
              {w | (sb2StageChart κ E b jumps (-(Real.pi / 2)) true ℓ ω).2.1 w ∈ A₁ t ω}
              (fwdHull (sb2StopDrv E b jumps (-(Real.pi / 2)) true ℓ t ω)
                (sb2StopTime E b jumps (-(Real.pi / 2)) true ℓ t ω))) ∧
        ∀ g : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean (A₂ t) (centredField h u₀) P g →
          ∃ β : Ω → BoundaryWord, ∀ᵐ ω ∂P,
            ω ∈ capEvent κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
              (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ t →
            ∀ v : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd v (H \ A₂ t ω) →
              (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₂ t ω → g ω φ = ∫ z, v z * φ z) →
              EqOn (fun z => v z + u₀ z) (fun z => (stopWord κ (β ω, -(Real.pi / 2), recOf (t : ℝ≥0∞)
                (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω))).mean
                  (fwdMap (sb2StopDrv E b jumps (-(Real.pi / 2)) true ℓ t ω)
                    (sb2StopTime E b jumps (-(Real.pi / 2)) true ℓ t ω)
                    ((sb2StageChart κ E b jumps (-(Real.pi / 2)) true ℓ ω).1 z)) -
                chiC κ * ((logDerivFwd (sb2StopDrv E b jumps (-(Real.pi / 2)) true ℓ t ω)
                    (sb2StopTime E b jumps (-(Real.pi / 2)) true ℓ t ω)
                    ((sb2StageChart κ E b jumps (-(Real.pi / 2)) true ℓ ω).1 z)).im +
                  (sb2StageChart κ E b jumps (-(Real.pi / 2)) true ℓ ω).2.2 z)) (H \ A₂ t ω) := by
  obtain ⟨hE', hreg', -⟩ := StagedReg.regFam_spec hb hE hER
  have hθ : -(Real.pi / 2) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨le_rfl, by linarith [Real.pi_pos]⟩
  have hw := isBoundaryContinuedProgram_boundaryWalkSpec b jumps hθ true
  have hRw := stagedPiecesRegular_of_regular h13 hκ hb (hE' _ hw) (hreg' _)
  have hfib := ae_finiteFibre_walk_cf h13₀ hκ hκ4 hb hh hcf hζ' (hE' _ hw) (hreg' _) hRw
  obtain ⟨𝓖, A₁, A₂, h𝓖, hA⟩ := exists_sb2LineFamily_fill (u := u) h12p h13 hκ hκ4 hb hh hE hER hlθ k ℓ hℓ hwℓ hu₀
  refine ⟨𝓖, A₁, A₂, h𝓖, fun t => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13', h14, hpull, h16⟩ := hA t
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13', h14, ?_, h16⟩
  filter_upwards [hpull, hfib] with ω hp hfω hcap hlu
  obtain ⟨g, hgc, hgi, hpb⟩ := hp hcap hlu
  obtain ⟨⟨c₀, θ₀⟩, hl⟩ := Option.ne_none_iff_exists'.1 hcap.1
  exact ⟨g, hpb (hfω ℓ (WalkIntRunChron.not_done_of_launch _ _ hl) g hgc hgi)⟩

end InteractingSLE.Theorem14.SB.Ml
