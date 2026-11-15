/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBTail2EraseCompare
import InteractingSLE.Spec.Supplement.SBLeafLaunch
import InteractingSLE.Spec.Supplement.SBW5Assembly

/-!
# Lemma SB2(1) in launch form, and SB3's relative stage ordering from it

Packet PROVE-T14-SBLEAVES. Lemma SB3's induction step (specification p. 633, `source/spec/p625-671.md`
L159–L163) reads: "Otherwise SB2(1) gives its actual remaining upper flow from `e_L = g_A(L⁻)` in `D_A`. The next lower
piece starts at `g_A(w) ≥ e_L` in the same conditional field. [...] Hence SB1 gives the ordered proper completions
through all available endpoints". The landed `SB2UpperRegStatement` cannot be used for this step: its σ-algebra `𝒢 ≥
pastSigma` is existential (so the next lower piece's conditional law under `𝒢` is not controlled), it gives no height
on the exposed lower sides (SB1's hybrid word on the middle interval, (SB3.1)), and it restricts `ψ ≤ π/2`.

This file states SB2(1) in **launch form**: conditionally on the lower walk's own retained past at its next launch
(`pastSigma … k`, the kernel under which the frozen `IsStagedHistory` launch clause describes the next lower piece),
for every witness `(b', jumps', h')` of that launch clause, the upper flow's remainder is a flow line of the same
`h'` from a point `m ≤ 0` of the launch chart, the conditional data `b'` carry SB2(1)'s active word on `(m, 0)`, and the
remainder is tied pathwise to the actual upper flow. It is a named source input (Lemma SB2(1)), not proved here.

Proved: `ae_hasRelStageOrdering_of_sb2UpperLaunch` — from SB2(1) in launch form, SB1, S6 and Theorem 1.3, at every
stage `k` of the lower walk and almost every retained past, the next lower piece and the upper remainder are flow
lines of one conditional GFF, and they have ordered proper completions through all available endpoints (the
probabilistic half of SB3's step); `…_dyCover` discharges SB1 and S6 by the landed `W5Assembly` results.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lv

open Sec4

/-! ### Launch angles of a boundary walk -/

/-- Every instruction of a boundary-walk program is a flow of the walk's angle or a real move. -/
theorem mem_boundaryWalkSpec_prog {b : ℝ → ℝ} {jumps : Finset ℝ} {θ₀ : ℝ} {right : Bool}
    {i : Instr} (hi : i ∈ (boundaryWalkSpec b jumps θ₀ right).2.2) :
    i = Sum.inl (θ₀, ⊤) ∨ i = Sum.inr (Sum.inl right) := by
  simp only [boundaryWalkSpec, List.mem_flatten, List.mem_replicate] at hi
  obtain ⟨l, ⟨-, rfl⟩, hl⟩ := hi
  simpa using hl

/-- A launched instruction of a boundary walk carries the walk's angle. -/
theorem launch_angle_boundaryWalk {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {θ₀ : ℝ} {right : Bool}
    {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {c : Chart} {θ : ℝ}
    (h : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ₀ right) D (k + 1)).2.2.2.1 k =
      some (c, θ)) :
    θ = θ₀ := by
  obtain ⟨hi, -, -⟩ := Exist.StagedLaw.eq_launch_of_launches (κ := κ) (b := b) (jumps := jumps) _ D h
  rcases mem_boundaryWalkSpec_prog (List.mem_of_getElem? hi) with h1 | h1
  · simp only [Sum.inl.injEq, Prod.mk.injEq] at h1
    exact h1.1
  · simp at h1

/-! ### The two clauses of SB2(1) in launch form -/

/-- **SB2(1)'s pathwise identification** (p. 631: "Only on `{T_L < T}` is a nonempty post-`T_L` relative portion
asserted. That portion is the canonical upper flow of the conditional field in `D_A` [...] with its original stop
reconstructed"): if the upper flow `η` reaches `L` within its available range, then up to an increasing continuous clock
`σ` its post-`T_L` portion is the relative curve `ηr` read back through the chart inverse `c⁻¹`, and the relative
available lifetime `ζr` reconstructs the original one. -/
def IsRemainderLink (c : Chart) (η : ℝ≥0 → ℂ) (ζ : ℝ≥0∞) (L : ℝ) (ηr : ℝ≥0 → ℂ) (ζr : ℝ≥0∞) : Prop :=
  firstVisit η ζ L < ζ → ∃ σ : ℝ≥0 → ℝ≥0, σ 0 = 0 ∧ StrictMono σ ∧ Continuous σ ∧ ∀ s : ℝ≥0,
    ((s : ℝ≥0∞) < ζr ↔ (((firstVisit η ζ L).toNNReal + σ s : ℝ≥0) : ℝ≥0∞) < ζ) ∧
    ((s : ℝ≥0∞) < ζr → ηr s ∈ H → c.2.1 (ηr s) = η ((firstVisit η ζ L).toNNReal + σ s))

/-- **SB2(1)'s active word** on the relative middle interval `(m, 0)` (p. 632: "the active lower-flow sides before the
next seed have height `−λ − φχ = −Λ`. The exposed rightward connectors retain their original heights `H ≤ −Λ` [...]
Any still exposed initial bridge keeps its original height"): every height of `b'` there is at most `−Λ` or is an
original height of the bridge `(u, 0)`. -/
def IsActiveLowWord (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (u : ℝ) (b' : ℝ → ℝ) (jumps' : Finset ℝ)
    (m : ℝ) : Prop :=
  ∀ y ∈ Ioo m 0, y ∉ jumps' →
    b' y ≤ -sleLambda κ - -(Real.pi / 2) * chiC κ ∨ ∃ x ∈ Ioo u 0, x ∉ jumps ∧ b' y = b x

/-- **Lemma SB2(1), launch form** (supplement pp. 630–633, `source/spec/p625-671.md` L113–L117; the active word L127,
the identification L131–L133). SB3's setting (no counterflow, every upper angle `ψ > −π/2`, the bridge `[u, 0]` with
SB1's hybrid word). Let `A` be the lower-walk prefix through `k` instructions with the bridge, with S1 against every
available upper prefix, and let instruction `k` of the lower walk launch in the chart `c`. Then for almost every
retained past `ω₀` and every witness `(b', jumps', h')` of the launch clause (`h'` the field read in `c`, a GFF with
data `b'` under the retained kernel), there are `m ≤ 0` (the entry `e_L` read in `c`) and a flow line `ηr` of `h'` from
`m` with the upper angle `ψ` under the retained kernel, with SB2(1)'s active word on `(m, 0)` and, almost surely, the
pathwise identification with the actual upper flow. -/
def SB2UpperLaunchStatement : Prop :=
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
            IsActiveLowWord κ b jumps u b' jumps' m ∧
            IsFlowLine κ b' jumps' m ψ (condExpKernel P (pastSigma κ b jumps
              (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
              (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) k) ω₀) h' ηr ζr ∧
            ∀ᵐ ω ∂(condExpKernel P (pastSigma κ b jumps
              (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
              (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) k) ω₀),
              IsRemainderLink c (η ω) (ζ ω) (realMin (lowerPrefix κ b jumps E k u ω)) (ηr ω) (ζr ω)

/-! ### SB1's hybrid word on the relative middle interval -/

/-- (SB3.1) and the retained bridge: SB2(1)'s active word gives SB1's two middle-word hypotheses on `(m, 0)` for every
upper angle `ψ`. -/
theorem hybrid_of_activeLowWord {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ} {u ψ : ℝ}
    (hL : ∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ))
    (hH : ∀ x ∈ Ioo u 0, x ∉ jumps → -2 < cumWeightRight κ (b x + ψ * chiC κ) ∨
      κ / 2 - 2 ≤ cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ))
    {b' : ℝ → ℝ} {jumps' : Finset ℝ} {m : ℝ} (hw : IsActiveLowWord κ b jumps u b' jumps' m) :
    (∀ y ∈ Ioo m 0, y ∉ jumps' → -2 < cumWeightLeft κ (b' y + -(Real.pi / 2) * chiC κ)) ∧
      (∀ y ∈ Ioo m 0, y ∉ jumps' → -2 < cumWeightRight κ (b' y + ψ * chiC κ) ∨
        κ / 2 - 2 ≤ cumWeightLeft κ (b' y + -(Real.pi / 2) * chiC κ)) := by
  refine ⟨fun y hy hyj => ?_, fun y hy hyj => ?_⟩
  · rcases hw y hy hyj with hlow | ⟨x, hx, hxj, hbx⟩
    · exact (switch_hybrid_low (ψ := ψ) hκ hκ4 hlow).1
    · rw [hbx]
      exact hL x hx hxj
  · rcases hw y hy hyj with hlow | ⟨x, hx, hxj, hbx⟩
    · exact (switch_hybrid_low (ψ := ψ) hκ hκ4 hlow).2
    · rw [hbx]
      exact hH x hx hxj

/-! ### The relative stage ordering -/

/-- **The relative pair of SB3's step at one retained past.** Under the measure `Q`, for the chart `c`: the next lower
piece (the chosen trace of the staged driver `(W, ζL)`, from `0`, angle `−π/2`) and a relative upper curve `ηr` (from
`m ≤ 0`, angle `ψ`) are flow lines of one field `h'` (the field read in `c`) with one datum `b'`; `ηr` is linked
pathwise to the actual upper flow `η` after its first visit to `L`; and, when both lifetimes are positive, the two
curves have ordered proper completions through all available endpoints (W0). -/
def HasRelStageOrdering (κ ψ : ℝ) {Ω : Type u} [MeasurableSpace Ω] (Q : Measure Ω)
    (h : Ω → DistOn upperHalfPlaneOpens) (c : Chart) (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞) (L : Ω → ℝ)
    (W : ℝ≥0 → Ω → ℝ) (ζL : Ω → ℝ≥0∞) : Prop :=
  ∃ (b' : ℝ → ℝ) (jumps' : Finset ℝ) (h' : Ω → DistOn upperHalfPlaneOpens) (m : ℝ)
    (ηr : Ω → ℝ≥0 → ℂ) (ζr : Ω → ℝ≥0∞),
    IsPiecewiseConstantBoundaryData b' jumps' ∧ (∀ ω, IsChartTransport c 1 0 (chiC κ) (h ω) (h' ω)) ∧
    IsGFFWithBoundaryData Q h' b' jumps' ∧ m ≤ 0 ∧
    IsFlowLine κ b' jumps' 0 (-(Real.pi / 2)) Q h' (GW2aSingle.chosenTrace W ζL) ζL ∧
    IsFlowLine κ b' jumps' m ψ Q h' ηr ζr ∧
    (∀ᵐ ω ∂Q, IsRemainderLink c (η ω) (ζ ω) (L ω) (ηr ω) (ζr ω)) ∧
    ((∀ᵐ ω ∂Q, 0 < ζL ω) → (∀ᵐ ω ∂Q, 0 < ζr ω) →
      ∀ᵐ ω ∂Q, ∀ d a : ℝ≥0, (d : ℝ≥0∞) ≤ ζL ω → (a : ℝ≥0∞) ≤ ζr ω →
        HasOrderedProperCompletions (GW2aSingle.chosenTrace W ζL ω) d (ηr ω) a)

/-- **The probabilistic half of SB3's induction step.** SB2(1) in launch form, SB1, S6 and Theorem 1.3 give, at
every stage `k` of the lower walk with S1 for its prefix, for almost every retained past `ω₀` at which instruction `k`
launches: the relative pair of the step under the retained kernel, ordered through all available endpoints (the source:
"SB2(1) gives its actual remaining upper flow from `e_L` in `D_A`. The next lower piece starts at `g_A(w) ≥ e_L` in the
same conditional field. [...] Hence SB1 gives the ordered proper completions through all available endpoints"). -/
theorem ae_hasRelStageOrdering_of_sb2UpperLaunch (hSB2 : SB2UpperLaunchStatement.{u})
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
      HasRelStageOrdering κ ψ (condExpKernel P (pastSigma κ b jumps
          (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) k) ω₀) h c η ζ
        (fun ω => realMin (lowerPrefix κ b jumps E k u ω))
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
  obtain ⟨m, ηr, ζr, hm, hword, hηr, hlink⟩ := hω₀ c θ hcθ b' jumps' h' hb' hct hgff
  subst hθ
  have hα := Sec7.StripWall.isFlowLine_of_isFlowLineDriver hfl
    ((GW2aSingle.ae_chosenTrace h13 hκ hfl).mono fun _ hω => hω.1)
  obtain ⟨hL', hH'⟩ := hybrid_of_activeLowWord hκ hκ4 hL hH hword
  exact ⟨b', jumps', h', m, ηr, ζr, hb', hct, hgff, hm, hα, hηr, hlink, fun hζα hζβ =>
    Erase.ae_ordered_of_hybrid hSB1 hS6 hκ hκ4 hb' hgff hm hψ hL' hH' hα hηr hζα hζβ⟩

/-- `ae_hasRelStageOrdering_of_sb2UpperLaunch` with SB1 and S6 discharged by the landed PROVE-SB-W5 results: the only
inputs besides SB2(1) in launch form are Theorems 1.2–1.3 and the small-gap fibre cover (Theorem 1.2's own input). -/
theorem ae_hasRelStageOrdering_of_sb2UpperLaunch_dyCover (hSB2 : SB2UpperLaunchStatement.{u})
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
      HasRelStageOrdering κ ψ (condExpKernel P (pastSigma κ b jumps
          (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) k) ω₀) h c η ζ
        (fun ω => realMin (lowerPrefix κ b jumps E k u ω))
        (fun t ω => (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω).1 t)
        (fun ω => (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω).2) :=
  ae_hasRelStageOrdering_of_sb2UpperLaunch hSB2
    (W5Assembly.sb1Statement_of_dyCover h12 h13 h12₀ h13₀ hDy hDy₀)
    (W5Assembly.s6Statement_of_dyCover h12 h13 h12₀ h13₀ hDy hDy₀) h13 hκ hκ4 hb hh hE hreg k hu hψ hL hH hη hS1

end InteractingSLE.Theorem14.SB.Lv
