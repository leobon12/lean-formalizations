/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBLxWalk

/-!
# SB3's stage induction: the claims, SB2(1) at launch samples, and the step

Packet PROVE-T14-SBLEAVES3 (second round). Lemma SB3's induction (specification p. 633, `source/spec/p625-671.md`
L159–L167) over the instructions of the lower walk. The claim at stage `k` (`SB3StageClaim`): at a live stage (every
earlier launched piece finite, `LowerLive`), S1 holds for the retained prefix `lowerPrefix k u` and every available
stop of the upper flow.

* `SB2UpperLaunchEntryLStatement`: SB2(1) in entry form (ruling R91) with its S1 premise required only where
  instruction `k` launches (finding F8: at samples where an earlier piece was infinite, `lowerPrefix k u` is the whole
  unbounded walk, which is not "a finite lower-walk prefix" as SB2(1) assumes, and S1 for it is not available). It
  implies the R91 form (`sb2UpperLaunchEntryStatement_of_L`).
* `ae_hasRelStageOrderingE_of_L`: the relative stage ordering from it.
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

open Lv Lw Sec4

/-- **The claim of SB3's induction at stage `k`**: at a live stage, S1 holds for the retained prefix (with the bridge)
and every available stop of the upper flow. -/
def SB3StageClaim {Ω : Type u} (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) (u : ℝ) (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞) (ω : Ω) : Prop :=
  LowerLive κ b jumps E k ω → ∀ a : ℝ≥0, (a : ℝ≥0∞) ≤ ζ ω → IsOneSided (lowerPrefix κ b jumps E k u ω) (η ω) a

/-- **Lemma SB2(1), entry form, S1 assumed at launch samples** (R91's form with the source's finite-prefix premise:
"Let `A` be a finite lower-walk prefix [...] Suppose the one-sided predicate S1 holds for `A`"). -/
def SB2UpperLaunchEntryLStatement : Prop :=
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
      (∀ᵐ ω ∂P, LowerLaunch κ b jumps E k ω → ∀ a : ℝ≥0, (a : ℝ≥0∞) ≤ ζ ω →
        IsOneSided (lowerPrefix κ b jumps E k u ω) (η ω) a) →
      ∀ᵐ ω₀ ∂P, ∀ (c : Chart) (θ : ℝ),
        (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω₀) (k + 1)).2.2.2.1 k =
            some (c, θ) →
        ∀ (b' : ℝ → ℝ) (jumps' : Finset ℝ) (h' : Ω → DistOn upperHalfPlaneOpens),
          IsPiecewiseConstantBoundaryData b' jumps' →
          (∀ ω, IsChartTransport c 1 0 (chiC κ) (h ω) (h' ω)) →
          IsGFFWithBoundaryData (condExpKernel P (pastSigma κ b jumps
            (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
            (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) k) ω₀) h' b' jumps' →
          ∃ (m : ℝ) (ηr : Ω → ℝ≥0 → ℂ) (ζr : Ω → ℝ≥0∞), m ≤ 0 ∧
            IsLeftEntryValue c (realMin (lowerPrefix κ b jumps E k u ω₀)) m ∧
            IsActiveLowWord κ b jumps u b' jumps' m ∧
            IsFlowLine κ b' jumps' m ψ (condExpKernel P (pastSigma κ b jumps
              (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
              (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) k) ω₀) h' ηr ζr ∧
            ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps
              (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
              (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) k) ω₀),
              IsRemainderLink c (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E k u ω)) (ηr ω) (ζr ω)

/-- The launch-sample form implies R91's entry form (its S1 premise is weaker). -/
theorem sb2UpperLaunchEntryStatement_of_L (hSB2 : SB2UpperLaunchEntryLStatement.{u}) :
    SB2UpperLaunchEntryStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh E hE hreg k u ψ hu hψ hL hH η ζ hη hS1
  exact hSB2 κ hκ hκ4 b jumps hb P h hh E hE hreg k u ψ hu hψ hL hH η ζ hη (hS1.mono fun _ hω _ => hω)

/-- **SB3's relative stage ordering from SB2(1) at launch samples** (`ae_hasRelStageOrderingE_of_sb2UpperLaunchEntry`
with the weaker S1 premise). -/
theorem ae_hasRelStageOrderingE_of_L (hSB2 : SB2UpperLaunchEntryLStatement.{u})
    (hSB1 : SB1Statement.{u}) (hS6 : S6Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P h b jumps) {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      IsStagedHistory κ b jumps P h spec (E spec))
    (hreg : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      StagedPiecesRegular κ b jumps P spec (E spec))
    (k : ℕ) {u ψ : ℝ} (hu : u ≤ 0) (hψ : -(Real.pi / 2) < ψ)
    (hL : ∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ))
    (hH : ∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightRight κ (b x + ψ * chiC κ) ∨
      κ / 2 - 2 ≤ cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ))
    {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} (hη : IsFlowLine κ b jumps u ψ P h η ζ)
    (hS1 : ∀ᵐ ω ∂P, LowerLaunch κ b jumps E k ω → ∀ a : ℝ≥0, (a : ℝ≥0∞) ≤ ζ ω →
      IsOneSided (lowerPrefix κ b jumps E k u ω) (η ω) a) :
    ∀ᵐ ω₀ ∂P, ∀ (c : Chart) (θ : ℝ),
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω₀) (k + 1)).2.2.2.1 k =
          some (c, θ) →
      HasRelStageOrderingE κ ψ (condExpKernel P (pastSigma κ b jumps
          (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) k) ω₀) h c η ζ
        (fun ω => realMin (lowerPrefix κ b jumps E k u ω)) (realMin (lowerPrefix κ b jumps E k u ω₀))
        (fun t ω => (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω).1 t)
        (fun ω => (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω).2) := by
  have hspec := isBoundaryContinuedProgram_boundaryWalkSpec b jumps
    (θ := -(Real.pi / 2)) ⟨le_rfl, by linarith [Real.pi_pos]⟩ true
  filter_upwards [hSB2 κ hκ hκ4 b jumps hb P h hh E hE hreg k u ψ hu hψ hL hH η ζ hη hS1,
    (hE _ hspec).2.2.2 k] with ω₀ hω₀ hlaunch
  intro c θ hcθ
  have hθ : θ = -(Real.pi / 2) := launch_angle_boundaryWalk hcθ
  obtain ⟨b', jumps', h', hb', hct, hfl⟩ := hlaunch c θ hcθ
  have hgff := GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver hκ hb' hfl
  obtain ⟨m, ηr, ζr, hm, hent, hword, hηr, hlink⟩ := hω₀ c θ hcθ b' jumps' h' hb' hct hgff
  subst hθ
  have hα := Sec7.StripWall.isFlowLine_of_isFlowLineDriver hfl
    ((GW2aSingle.ae_chosenTrace h13 hκ hfl).mono fun _ hω => hω.1)
  obtain ⟨hL', hH'⟩ := hybrid_of_activeLowWord hκ hκ4 hL hH hword
  have hord := fun hζα hζβ => Erase.ae_ordered_of_hybrid hSB1 hS6 hκ hκ4 hb' hgff hm hψ hL' hH' hα hηr hζα hζβ
  refine ⟨b', jumps', h', m, ηr, ζr, hb', hct, hgff, hm, hent, hα, hηr, hlink, ?_⟩
  rcases ae_lifetime_eq_zero_or_ne_of_isFlowLine hα with hL0 | hLp
  · filter_upwards [hL0] with ω hω hpos
    exact absurd hω hpos.ne'
  rcases ae_lifetime_eq_zero_or_ne_of_isFlowLine hηr with hr0 | hrp
  · filter_upwards [hr0] with ω hω _ hpos
    exact absurd hω hpos.ne'
  filter_upwards [hord (hLp.mono fun _ hω => pos_iff_ne_zero.2 hω) (hrp.mono fun _ hω => pos_iff_ne_zero.2 hω)]
    with ω hω _ _
  exact hω

/-! ### Helpers -/

/-- The retained prefix depends only on the walk's state. -/
theorem lowerPrefix_eq_of_run_eq {Ω : Type u} {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u : ℝ} {ω ω₀ : Ω}
    (h : lowerWalkState κ b jumps E k ω = lowerWalkState κ b jumps E k ω₀) :
    lowerPrefix κ b jumps E k u ω = lowerPrefix κ b jumps E k u ω₀ := by
  unfold lowerPrefix prefixPhysSet
  unfold lowerWalkState at h
  simp only [h]

/-- The chosen trace is a generating trace wherever a transient generating trace exists. -/
theorem isGeneratingTrace_chosenTrace {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {ω : Ω}
    (hex : ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η ∧
      (ζ ω = ⊤ → Tendsto (fun t => ‖η t‖) atTop atTop)) :
    IsGeneratingTrace (fun t => W t ω) (ζ ω) (GW2aSingle.chosenTrace W ζ ω) := by
  unfold GW2aSingle.chosenTrace
  split_ifs
  exact hex.choose_spec.1

/-- A finite lifetime: the available times are an interval. -/
theorem setOf_coe_le_eq_Icc {ζ : ℝ≥0∞} (hζ : ζ ≠ ⊤) : {t : ℝ≥0 | (t : ℝ≥0∞) ≤ ζ} = Icc 0 ζ.toNNReal := by
  ext t
  simp only [mem_Icc, zero_le, true_and]
  show (t : ℝ≥0∞) ≤ ζ ↔ t ≤ ζ.toNNReal
  conv_lhs => rw [← ENNReal.coe_toNNReal hζ]
  exact ENNReal.coe_le_coe

end InteractingSLE.Theorem14.SB.Lx
