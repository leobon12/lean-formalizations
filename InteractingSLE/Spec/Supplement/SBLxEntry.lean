/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBLwEntry
import InteractingSLE.Spec.Supplement.SBLwStage

/-!
# SB2(1)'s entry prime end, and the walk's launch chart as a left entry chart without a ball premise

Packet PROVE-T14-SBLEAVES3, item (1). `Lw.isLeftEntryChart_shift_of_runChart` needs a ball around
`L = min(A ∩ ℝ)` missing the fill of the walk's prefix. That premise fails whenever `L` is a point of the walk itself:
always when the seeds coincide (`u = 0`, `L = 0` is the walk's root), and whenever the lower walk touches `ℝ` at or
left of the upper seed. There the chart has no two-sided boundary value at `L`, and the boundary map can send several
real points to `L` (one for each access to `L` from the domain), so `g(m) = L` (all that `Lv.SB2UpperLaunchStatement`
says about its `m`) does not identify `m`.

The source identifies the access: SB2(1)'s relative portion starts "from the prime end over `L` incident to the
untouched original-real interval on its left" (`source/spec/p625-671.md` L117), i.e. at the limit from the left of the
chart's real boundary values on `(−∞, L)` (the entry `e_L = g_A(L⁻)`, L161). The launch form recorded this only in its
docstring ("`m ≤ 0` (the entry `e_L` read in `c`)"). This file:

* `IsLeftEntryValue c L m`: the chart's real boundary values left of `L` tend to `m` at `L⁻`;
* `SB2UpperLaunchEntryStatement`: `Lv.SB2UpperLaunchStatement` with this source clause (finding F7 of the handoff);
  it implies the landed form (`sb2UpperLaunchStatement_of_entry`);
* `HasRelStageOrderingE` and `ae_hasRelStageOrderingE_of_sb2UpperLaunchEntry(_dyCover)`: the corrected relative
  stage ordering (`Lw.HasRelStageOrderingP`) remembering the entry clause of its `m`;
* `isLeftEntryChart_shift_of_runChart_entry`: the walk's launch chart, read in S5's coordinates with SB2(1)'s `m`, is a
  left entry chart, with no ball premise.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (chiC H Hbar)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lx

open Lv Lw Sec4

/-- **The entry prime end over `L` incident to the untouched real interval on its left** (SB2(1), p. 631): the chart
`c` has real boundary values on `(−∞, L)`, and they tend to `m` at `L⁻`. -/
def IsLeftEntryValue (c : Chart) (L m : ℝ) : Prop :=
  ∃ e : ℝ → ℝ, (∀ x < L, Tendsto c.1 (𝓝[H] (x : ℂ)) (𝓝 (e x : ℂ))) ∧ Tendsto e (𝓝[<] L) (𝓝 m)

/-- **Lemma SB2(1), launch form, with its entry prime end** (supplement pp. 630–633, `source/spec/p625-671.md`
L113–L117, the entry L117 and L161). Exactly `Lv.SB2UpperLaunchStatement`, plus the source's identification of the
relative start: `m` is the entry `e_L = g_A(L⁻)` of the launch chart at `L = min(A ∩ ℝ)` ("from the prime end over `L`
incident to the untouched original-real interval on its left"). -/
def SB2UpperLaunchEntryStatement : Prop :=
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

/-- The entry form implies the landed launch form (forget the entry clause). -/
theorem sb2UpperLaunchStatement_of_entry (hSB2 : SB2UpperLaunchEntryStatement.{u}) :
    SB2UpperLaunchStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh E hE hreg k u ψ hu hψ hL hH η ζ hη hS1
  filter_upwards [hSB2 κ hκ hκ4 b jumps hb P h hh E hE hreg k u ψ hu hψ hL hH η ζ hη hS1] with ω₀ hω₀
  intro c θ hcθ b' jumps' h' hb' hct hgff
  obtain ⟨m, ηr, ζr, hm, -, hword, hηr, hlink⟩ := hω₀ c θ hcθ b' jumps' h' hb' hct hgff
  exact ⟨m, ηr, ζr, hm, hword, hηr, hlink⟩

/-! ### The relative stage ordering with the entry clause -/

/-- **`Lw.HasRelStageOrderingP` remembering SB2(1)'s entry**: the relative upper curve starts at the entry value `m`
of the chart `c` at `L₀`. -/
def HasRelStageOrderingE (κ ψ : ℝ) {Ω : Type u} [MeasurableSpace Ω] (Q : Measure Ω)
    (h : Ω → DistOn upperHalfPlaneOpens) (c : Chart) (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞) (L : Ω → ℝ) (L₀ : ℝ)
    (W : ℝ≥0 → Ω → ℝ) (ζL : Ω → ℝ≥0∞) : Prop :=
  ∃ (b' : ℝ → ℝ) (jumps' : Finset ℝ) (h' : Ω → DistOn upperHalfPlaneOpens) (m : ℝ)
    (ηr : Ω → ℝ≥0 → ℂ) (ζr : Ω → ℝ≥0∞),
    IsPiecewiseConstantBoundaryData b' jumps' ∧ (∀ ω, IsChartTransport c 1 0 (chiC κ) (h ω) (h' ω)) ∧
    IsGFFWithBoundaryData Q h' b' jumps' ∧ m ≤ 0 ∧ IsLeftEntryValue c L₀ m ∧
    IsFlowLine κ b' jumps' 0 (-(Real.pi / 2)) Q h' (GW2aSingle.chosenTrace W ζL) ζL ∧
    IsFlowLine κ b' jumps' m ψ Q h' ηr ζr ∧
    (∀ᵐ ω ∂Q, IsRemainderLink c (η ω) (ζ ω) (L ω) (ηr ω) (ζr ω)) ∧
    ∀ᵐ ω ∂Q, 0 < ζL ω → 0 < ζr ω → ∀ d a : ℝ≥0, (d : ℝ≥0∞) ≤ ζL ω → (a : ℝ≥0∞) ≤ ζr ω →
      HasOrderedProperCompletions (GW2aSingle.chosenTrace W ζL ω) d (ηr ω) a

/-- Forgetting the entry clause. -/
theorem HasRelStageOrderingE.hasRelStageOrderingP {κ ψ : ℝ} {Ω : Type u} [MeasurableSpace Ω] {Q : Measure Ω}
    {h : Ω → DistOn upperHalfPlaneOpens} {c : Chart} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞} {L : Ω → ℝ} {L₀ : ℝ}
    {W : ℝ≥0 → Ω → ℝ} {ζL : Ω → ℝ≥0∞} (hR : HasRelStageOrderingE κ ψ Q h c η ζ L L₀ W ζL) :
    HasRelStageOrderingP κ ψ Q h c η ζ L W ζL := by
  obtain ⟨b', jumps', h', m, ηr, ζr, hb', hct, hgff, hm, -, hα, hηr, hlink, hord⟩ := hR
  exact ⟨b', jumps', h', m, ηr, ζr, hb', hct, hgff, hm, hα, hηr, hlink, hord⟩

/-- **SB3's relative stage ordering with the entry clause**: `Lv.ae_hasRelStageOrdering_of_sb2UpperLaunch` and
`Lw.hasRelStageOrderingP_of_hasRelStageOrdering` for SB2(1)'s entry form. The proof is theirs, keeping the entry
clause of the `m` that SB2(1) supplies. -/
theorem ae_hasRelStageOrderingE_of_sb2UpperLaunchEntry (hSB2 : SB2UpperLaunchEntryStatement.{u})
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
    (hS1 : ∀ᵐ ω ∂P, ∀ a : ℝ≥0, (a : ℝ≥0∞) ≤ ζ ω → IsOneSided (lowerPrefix κ b jumps E k u ω) (η ω) a) :
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

/-- `ae_hasRelStageOrderingE_of_sb2UpperLaunchEntry` with SB1 and S6 discharged by the landed PROVE-SB-W5 results. -/
theorem ae_hasRelStageOrderingE_of_sb2UpperLaunchEntry_dyCover (hSB2 : SB2UpperLaunchEntryStatement.{u})
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hDy : Sec5.Aux61Act.DyActFibreCoverOn.{u}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin)
    (hDy₀ : Sec5.Aux61Act.DyActFibreCoverOn.{0}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin)
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
    (hS1 : ∀ᵐ ω ∂P, ∀ a : ℝ≥0, (a : ℝ≥0∞) ≤ ζ ω → IsOneSided (lowerPrefix κ b jumps E k u ω) (η ω) a) :
    ∀ᵐ ω₀ ∂P, ∀ (c : Chart) (θ : ℝ),
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun j => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω₀) (k + 1)).2.2.2.1 k =
          some (c, θ) →
      HasRelStageOrderingE κ ψ (condExpKernel P (pastSigma κ b jumps
          (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) k) ω₀) h c η ζ
        (fun ω => realMin (lowerPrefix κ b jumps E k u ω)) (realMin (lowerPrefix κ b jumps E k u ω₀))
        (fun t ω => (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω).1 t)
        (fun ω => (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω).2) :=
  ae_hasRelStageOrderingE_of_sb2UpperLaunchEntry hSB2
    (W5Assembly.sb1Statement_of_dyCover h12 h13 h12₀ h13₀ hDy hDy₀)
    (W5Assembly.s6Statement_of_dyCover h12 h13 h12₀ h13₀ hDy hDy₀) h13 hκ hκ4 hb hh hE hreg k hu hψ hL hH hη hS1

/-! ### The walk's launch chart as a left entry chart, with no ball premise -/

section Run

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- An entry value read in S5's coordinates: shifting the chart by `u` and its values by `m` sends the entry to `0`. -/
theorem IsLeftEntryValue.shift {c : Chart} {L m : ℝ} (h : IsLeftEntryValue c L m) (u : ℝ) :
    ∃ e : ℝ → ℝ, (∀ x < L - u, Tendsto (shiftChart c u m).1 (𝓝[H] (x : ℂ)) (𝓝 (e x : ℂ))) ∧
      Tendsto e (𝓝[<] (L - u)) (𝓝 0) := by
  obtain ⟨e, he, hlim⟩ := h
  refine ⟨fun x => e (x + u) - m, fun x hx => ?_, ?_⟩
  · have h0 := tendsto_add_real_nhdsWithin_H (x : ℂ) u
    have h2 : ((x : ℂ) + u) = ((x + u : ℝ) : ℂ) := by push_cast; ring
    rw [h2] at h0
    have h3 := ((he (x + u) (by linarith)).comp h0).sub_const (m : ℂ)
    push_cast
    exact h3
  · have hshift : Tendsto (fun x : ℝ => x + u) (𝓝[<] (L - u)) (𝓝[<] L) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have hc : Continuous (fun x : ℝ => x + u) := by fun_prop
        have := (hc.tendsto (L - u)).mono_left (nhdsWithin_le_nhds (s := Iio (L - u)))
        simpa using this
      · filter_upwards [self_mem_nhdsWithin] with x hx
        show x + u < L
        have : x < L - u := hx
        linarith
    have := (hlim.comp hshift).sub_const m
    simpa using this

open WalkIntCanon Exist.Staged Exist.StagedLaw in
/-- **The walk's launch chart is a left entry chart in S5's coordinates, with no ball premise.** As
`Lw.isLeftEntryChart_shift_of_runChart`, but the entry value `m` at `L` is given (SB2(1)'s entry prime end,
`IsLeftEntryValue`) instead of being computed from a ball around `L` missing the fill. So `L` may be a point of the
walk (its root when the seeds coincide, or a real contact of the walk at or left of the upper seed). -/
theorem isLeftEntryChart_shift_of_runChart_entry (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hreg : ∀ k c θ', (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = some (c, θ') →
      GW1P.PieceRegular (D k).1 (min (instrTime spec k) (D k).2)) (n : ℕ)
    (hnot : stStatus (ExplState.run κ b jumps spec D n) ≠ GW1Conn.stDone) {A : Set ℂ} (hAc : IsCompact A)
    (hAf : fillH A = fillH (SB.prefixPhysSet κ b jumps spec D n)) {L : ℝ} (hLA : ∀ y : ℝ, (y : ℂ) ∈ A → L ≤ y)
    {m : ℝ} (hent : IsLeftEntryValue (stChart (ExplState.run κ b jumps spec D n)) L m) (u : ℝ) :
    IsLeftEntryChart ((fun z => z - (u : ℂ)) '' A) (L - u)
      (shiftChart (stChart (ExplState.run κ b jumps spec D n)) u m) := by
  refine ⟨?_, hent.shift u, ?_, ?_⟩
  · -- clause 1
    have h1 := isDomainChart_shiftChart (hAf ▸ isDomainChart_runChart spec D hreg n hnot) u m
    rw [fillH_image_sub_real, ← image_sub_real_H u, ← image_sdiff (sub_left_injective (b := (u : ℂ)))]
    exact h1
  · -- clause 3
    have h1 := tendsto_runChart_cobounded spec D hreg n hnot
    rw [← hAf] at h1
    have hmaps : MapsTo (fun z : ℂ => z + u) (H \ fillH ((fun z => z - (u : ℂ)) '' A)) (H \ fillH A) := by
      intro z hz
      refine ⟨(add_real_mem_H_iff u).2 hz.1, fun hzA => hz.2 ?_⟩
      rw [fillH_image_sub_real]
      exact ⟨z + u, hzA, by simp⟩
    have h2 : Tendsto (fun z : ℂ => z + u) (Bornology.cobounded ℂ ⊓ 𝓟 (H \ fillH ((fun z => z - (u : ℂ)) '' A)))
        (Bornology.cobounded ℂ ⊓ 𝓟 (H \ fillH A)) :=
      tendsto_inf.2 ⟨tendsto_add_cobounded _ inf_le_left,
        (tendsto_principal_principal.2 hmaps).mono_left inf_le_right⟩
    have h3 := tendsto_add_cobounded (-(m : ℂ)) le_rfl
    exact (h3.comp (h1.comp h2)).congr fun z => by simp [shiftChart, sub_eq_add_neg]
  · -- clause 4
    intro x hx
    have h0 := tendsto_add_real_nhdsWithin_H (x : ℂ) u
    have h2 : ((x : ℂ) + u) = ((x + u : ℝ) : ℂ) := by push_cast; ring
    rw [h2] at h0
    exact (tendsto_runChart_lift_zero spec D hreg n hnot hAc hAf (x := x + u)
      (fun y hy => by linarith [hLA y hy])).comp h0

end Run

end InteractingSLE.Theorem14.SB.Lx
