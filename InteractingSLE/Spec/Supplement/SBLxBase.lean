/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBLxInduct

/-!
# SB3's induction: real additions and the first stage

Packet PROVE-T14-SBLEAVES3 (second round).

* `stageClaim_succ_of_adds`: a stage that adds only real points `≥ 0` (a connector, or a piece of zero lifetime, as
  the walk's right records give; `WalkRightAdds`) preserves the claim (S1 is unchanged by original real points right
  of the upper seed: SB3, "Every original positive-real point is on the closed right side of any proper simple
  completion").
* `ae_stageClaim_one`: the claim after the first instruction. The first piece is the original-field flow line from `0`
  (`IsStagedHistory.isFlowLineDriver_first`); SB1/S6 (the hybrid base, `Erase.ae_isOneSided_base_of_hybrid`) give S1
  for it with the bridge ("For the first nonempty lower flow with the common seed, W5 and S6 give this assertion
  through finite endpoints. With distinct seeds use SB1 instead."). A first piece of zero lifetime is a real addition.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H Hbar)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lx

open Lv Lw Sec4 Exist.Staged Exist.StagedLaw

/-- **The walk adds only real points `≥ 0` at its connectors and its pieces of zero lifetime** (the right records of
the lower walk, SB3: "At the end of an ordinary stage the lower endpoint `q` is a new right record. Adding the next
interval `[q, w]` preserves S1"). A pathwise property of the lower walk at `ω`. -/
def WalkRightAdds {Ω : Type u} (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ω : Ω) : Prop :=
  ∀ k : ℕ, (¬ LowerLaunch κ b jumps E k ω ∨ (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω).2 = 0) →
    prefixPhysSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (k + 1) ⊆
      prefixPhysSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) k ∪ ((↑) : ℝ → ℂ) '' Ici 0

/-- **A real addition right of the upper seed preserves the claim.** -/
theorem stageClaim_succ_of_adds {Ω : Type u} {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} {ω : Ω}
    (hu : u ≤ 0) (hη0 : η ω 0 = u) (hC : SB3StageClaim κ b jumps E k u η ζ ω)
    (hadd : prefixPhysSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) (k + 1) ⊆
      prefixPhysSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) k ∪ ((↑) : ℝ → ℂ) '' Ici 0) :
    SB3StageClaim κ b jumps E (k + 1) u η ζ ω := by
  intro hlive a ha
  have h1 := (hC hlive.of_succ a ha).union_right_real (T := Ici 0) (by rw [hη0]; simp)
    (fun x hx => by rw [hη0, Complex.ofReal_re]; exact hu.trans hx)
  refine h1.mono ?_
  unfold lowerPrefix
  intro z hz
  rcases hz with hz | hz
  · rcases hadd hz with hz' | hz'
    · exact Or.inl (Or.inl hz')
    · exact Or.inr hz'
  · exact Or.inl (Or.inr hz)

/-- The boundary walk's program starts with a flow of its angle. -/
theorem boundaryWalkSpec_prog_eq (b : ℝ → ℝ) (jumps : Finset ℝ) (θ : ℝ) (right : Bool) :
    ∃ rest : List Instr, (boundaryWalkSpec b jumps θ right).2.2 = Sum.inl (θ, ⊤) :: rest := by
  refine ⟨Sum.inr (Sum.inl right) :: (List.replicate (PiecewiseConstantBoundaryData.jumpSet b jumps).card
    [(Sum.inl (θ, ⊤) : Instr), Sum.inr (Sum.inl right)]).flatten, ?_⟩
  show (List.replicate ((PiecewiseConstantBoundaryData.jumpSet b jumps).card + 1)
    [(Sum.inl (θ, ⊤) : Instr), Sum.inr (Sum.inl right)]).flatten = _
  rw [List.replicate_succ, List.flatten_cons]
  rfl

/-- The physical prefix before any instruction is the root. -/
theorem prefixPhysSet_zero {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} (spec : ExplSpec)
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) : prefixPhysSet κ b jumps spec D 0 = {(spec.1 : ℂ)} := by
  simp [prefixPhysSet, ExplState.run, ExplState.init]

/-- **The claim after the first instruction** (SB3: "For the first nonempty lower flow with the common seed, W5 and S6
give this assertion through finite endpoints. With distinct seeds use SB1 instead."). The first piece is the
original-field flow line from `0`; when its lifetime is zero, the first instruction adds only the root. -/
theorem ae_stageClaim_one (hSB1 : SB1Statement.{u}) (hS6 : S6Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      IsStagedHistory κ b jumps P h spec (E spec))
    (hreg : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      StagedPiecesRegular κ b jumps P spec (E spec))
    {u ψ : ℝ} (hu : u ≤ 0) (hψ : -(Real.pi / 2) < ψ)
    (hL : ∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ))
    (hH : ∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightRight κ (b x + ψ * chiC κ) ∨
      κ / 2 - 2 ≤ cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ))
    {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} (hη : IsFlowLine κ b jumps u ψ P h η ζ) (hζ : ∀ᵐ ω ∂P, 0 < ζ ω)
    (hadd : ∀ᵐ ω ∂P, WalkRightAdds κ b jumps E ω) (hC0 : ∀ᵐ ω ∂P, SB3StageClaim κ b jumps E 0 u η ζ ω) :
    ∀ᵐ ω ∂P, SB3StageClaim κ b jumps E 1 u η ζ ω := by
  set spec := boundaryWalkSpec b jumps (-(Real.pi / 2)) true with hspec_def
  have hspec : IsBoundaryContinuedProgram spec.2.2 := isBoundaryContinuedProgram_boundaryWalkSpec b jumps
    (θ := -(Real.pi / 2)) ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  obtain ⟨rest, hp⟩ := boundaryWalkSpec_prog_eq b jumps (-(Real.pi / 2)) true
  have hfl := (hE spec hspec).isFlowLineDriver_first hκ hb hh rfl hp
  have hα := Sec7.StripWall.isFlowLine_of_isFlowLineDriver hfl
    ((GW2aSingle.ae_chosenTrace h13 hκ hfl).mono fun _ hω => hω.1)
  have hηreg := ae_flowLine_regular h13 hκ hη
  rcases ae_lifetime_eq_zero_or_ne_of_isFlowLine hα with h0 | hpos
  · filter_upwards [hC0, hadd, h0, hηreg] with ω hCω haddω h0ω hηω
    exact stageClaim_succ_of_adds hu hηω.2.1 hCω (haddω 0 (Or.inr h0ω))
  · have hbase := Erase.ae_isOneSided_base_of_hybrid hSB1 hS6 hκ hκ4 hb hh hu hψ hL hH hα hη
      (hpos.mono fun _ hω => pos_iff_ne_zero.2 hω) hζ
    filter_upwards [hbase, hreg spec hspec, ae_flowLine_regular h13 hκ hα] with ω hbω hregω hαω
    intro hlive a ha
    have hl := GW1.launches_run_one_of_cons κ b jumps spec hp (fun j => E spec j ω)
    have hlaunch : LowerLaunch κ b jumps E 0 ω := by
      unfold LowerLaunch lowerWalkState
      rw [hl]
      exact Option.some_ne_none _
    have hfin := hlive.ne_top_of_launch hlaunch
    obtain ⟨hW0, hWc, γ, hγ, hγt⟩ := hregω 0 (-(Real.pi / 2)) ⊤ _ (by rw [hp]; rfl) hl
    rw [min_top_left] at hWc hγ hγt
    have hgen := isGeneratingTrace_chosenTrace (W := fun t ω => (E spec 0 ω).1 t)
      (ζ := fun ω => (E spec 0 ω).2) ⟨γ, hγ, hγt⟩
    have hgi : EqOn (fun z : ℂ => z)
        (stChart (ExplState.run κ b jumps spec (fun j => E spec j ω) 0)).2.1 H := by
      intro w _
      simp [stChart, ExplState.run, ExplState.init, Chart.recenter, Chart.id, hspec_def, boundaryWalkSpec]
    have hphys := prefixPhysSet_succ_eq_image (κ := κ) (b := b) (jumps := jumps) (θ := -(Real.pi / 2))
      (right := true) (fun j => E spec j ω) (k := 0) (by rw [hl]; exact Option.some_ne_none _)
      continuousOn_id hgi hgen hWc hW0 hαω.2.2.1
    rw [setOf_coe_le_eq_Icc hfin] at hphys
    have hd : (((E spec 0 ω).2.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ (E spec 0 ω).2 := ENNReal.coe_toNNReal_le_self
    refine (hbω _ a hd ha).mono ?_
    unfold lowerPrefix
    rw [show (1 : ℕ) = 0 + 1 from rfl, hphys, prefixPhysSet_zero, image_id]
    intro z hz
    rcases hz with (hz | hz) | hz
    · refine Or.inr ⟨0, ⟨hu, le_rfl⟩, ?_⟩
      rw [hz]; simp [boundaryWalkSpec]
    · exact Or.inl hz
    · exact Or.inr hz

end InteractingSLE.Theorem14.SB.Lx
