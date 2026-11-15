/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB4SewAssembly
import InteractingSLE.Spec.Supplement.SBLeafSB3
import InteractingSLE.Spec.Exist.StagedLaw4

/-!
# SB4's switch step: SB3 under the retained conditional law, then the actual-tail sewing

Packet PROVE-T14-SBTAIL. The proof of Theorem SB4 (specification pp. 634–635,
`source/spec/p625-671.md` L176–L186) handles one switch of the upper schedule as follows:
SB2(2) identifies the actual remaining lower tail, in the retained conditional field of the
schedule prefix, as a lower walk of that field; the new upper piece is a flow of the same
conditional field; *SB3 (distinct-seed form) applied to this relative pair* gives the one-sided
completions S1; the physical gluing (S5, here SBSEW's `HasActualTailSewing.avoids`) transports
them to the physical side of the actual walk.

This file proves the comparison and gluing part of that step:

* `IsRelSB3Instance`: under one probability measure `Q` (in the application, the conditional law
  `condExpKernel P 𝒢 ω₀`), the chart field is a GFF, the relative lower walk is a regular staged
  history of it, and the relative new piece is a flow line of it from `u' ≤ 0` with SB1's hybrid
  word on `(u', 0)` — exactly the hypotheses of Lemma SB3;
* `ae_isOneSided_of_relSB3Instance`: SB3 (`SB3InductionGenStatement`) gives S1 for that pair
  `Q`-almost surely; the other staged families SB3 quantifies over are supplied by Theorems
  1.2–1.3 (`exists_isStagedHistory_regular_of_thm12_thm13`, R48 permits them for Theorem 1.4);
* `HasRelTailGeometry`: the pathwise sewing data of `HasActualTailSewing` *without* the S1 clause,
  with the relative walk's proper parametrization tied to the staged relative walk;
* `hasConditionalActualTailSewing_of_relativeTail`: SBSEW's open `HasConditionalActualTailSewing`
  from the S1-free data `HasConditionalRelativeTail`, SB3 and Theorems 1.2–1.3.

The data `HasConditionalRelativeTail` are not asserted here: they contain SB2(2)'s
identification of the relative tail and the new piece's relative chart, not any comparison.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H)
open LQGMetric (DistOn)
open InteractingSLE.Supp9B

universe u

namespace InteractingSLE.Theorem14.SB.Leaf

open Sec4

/-- The physical set of the lower walk (angle `−π/2`, continuing right) of the data `b'` off
`jumps'`, run with the drivers `EL`; it is `lowerWalkSet` for any family whose lower-walk member is
`EL`. -/
def relWalkSet (κ : ℝ) (b' : ℝ → ℝ) (jumps' : Finset ℝ) {Ω : Type u}
    (EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ω : Ω) : Set ℂ :=
  ExplState.physSet κ b' jumps' (boundaryWalkSpec b' jumps' (-(Real.pi / 2)) true)
    (fun j => EL j ω)

theorem lowerWalkSet_update {κ : ℝ} {b' : ℝ → ℝ} {jumps' : Finset ℝ} {Ω : Type u}
    [DecidableEq ExplSpec] (E₀ : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ω : Ω) :
    lowerWalkSet κ b' jumps'
        (Function.update E₀ (boundaryWalkSpec b' jumps' (-(Real.pi / 2)) true) EL) ω =
      relWalkSet κ b' jumps' EL ω := by
  simp only [lowerWalkSet, relWalkSet, Function.update_self]

/-- **The relative pair is an instance of Lemma SB3** under the probability measure `Q`: the field
`hQ` (the conditional field read in the relative chart) is a GFF with data `b'` off `jumps'`; `EL`
is a regular staged lower walk of it; `η` is a flow line of angle `ψ > −π/2` of it from `u' ≤ 0`
with nonempty lifetime; and SB1's hybrid word holds on `(u', 0)`. -/
def IsRelSB3Instance (κ : ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (Q : Measure Ω) [IsProbabilityMeasure Q] (hQ : Ω → DistOn upperHalfPlaneOpens)
    (b' : ℝ → ℝ) (jumps' : Finset ℝ) (EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u' ψ : ℝ)
    (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞) : Prop :=
  IsPiecewiseConstantBoundaryData b' jumps' ∧ IsGFFWithBoundaryData Q hQ b' jumps' ∧
    (IsBoundaryContinuedProgram (boundaryWalkSpec b' jumps' (-(Real.pi / 2)) true).2.2 →
      IsStagedHistory κ b' jumps' Q hQ (boundaryWalkSpec b' jumps' (-(Real.pi / 2)) true) EL ∧
        StagedPiecesRegular κ b' jumps' Q (boundaryWalkSpec b' jumps' (-(Real.pi / 2)) true) EL) ∧
    u' ≤ 0 ∧ -(Real.pi / 2) < ψ ∧
    (∀ x ∈ Ioo u' 0, x ∉ jumps' → -2 < cumWeightLeft κ (b' x + -(Real.pi / 2) * chiC κ)) ∧
    (∀ x ∈ Ioo u' 0, x ∉ jumps' → -2 < cumWeightRight κ (b' x + ψ * chiC κ) ∨
      κ / 2 - 2 ≤ cumWeightLeft κ (b' x + -(Real.pi / 2) * chiC κ)) ∧
    IsFlowLine κ b' jumps' u' ψ Q hQ η ζ ∧ ∀ᵐ ω ∂Q, 0 < ζ ω

/-- **SB3 applied to a relative instance.** The remaining staged families of SB3's setting come
from Theorems 1.2–1.3; the lower-walk member is replaced by the given relative walk. -/
theorem ae_isOneSided_of_relSB3Instance (hSB3 : SB3InductionGenStatement.{u})
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {Q : Measure Ω} [IsProbabilityMeasure Q] {hQ : Ω → DistOn upperHalfPlaneOpens}
    {b' : ℝ → ℝ} {jumps' : Finset ℝ} {EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {u' ψ : ℝ}
    {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hI : IsRelSB3Instance κ Q hQ b' jumps' EL u' ψ η ζ) :
    ∀ᵐ ω ∂Q, ∀ γ : ℝ≥0 → ℂ, IsProperCurve γ → γ 0 = 0 →
      range γ = relWalkSet κ b' jumps' EL ω →
      ∀ s a : ℝ≥0, (a : ℝ≥0∞) ≤ ζ ω →
        IsOneSided (γ '' Icc 0 s ∪ ((↑) : ℝ → ℂ) '' Icc u' 0) (η ω) a := by
  classical
  obtain ⟨hb, hh, hL, hu, hψ, hA, hH, hη, hζ⟩ := hI
  obtain ⟨E₀, hE₀⟩ :=
    Exist.StagedLaw.exists_isStagedHistory_regular_of_thm12_thm13 h12 h13 hκ hκ4 hb hh
  have hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      IsStagedHistory κ b' jumps' Q hQ spec
          (Function.update E₀ (boundaryWalkSpec b' jumps' (-(Real.pi / 2)) true) EL spec) ∧
        StagedPiecesRegular κ b' jumps' Q spec
          (Function.update E₀ (boundaryWalkSpec b' jumps' (-(Real.pi / 2)) true) EL spec) := by
    intro spec hspec
    by_cases hs : spec = boundaryWalkSpec b' jumps' (-(Real.pi / 2)) true
    · subst hs
      rw [Function.update_self]
      exact hL hspec
    · rw [Function.update_of_ne hs]
      exact hE₀ spec hspec
  have hS := hSB3 κ hκ hκ4 b' jumps' hb Q hQ hh
    (Function.update E₀ (boundaryWalkSpec b' jumps' (-(Real.pi / 2)) true) EL)
    (fun s hs => (hE s hs).1) (fun s hs => (hE s hs).2) u' ψ hu hψ hA hH η ζ hη hζ
  filter_upwards [hS] with ω hω γ hγ hγ0 hr
  exact hω γ hγ hγ0 (by rw [lowerWalkSet_update]; exact hr)

/-- **The S1-free sewing data** for one new physical piece `A` and the forbidden side `S`: every
datum of `HasActualTailSewing` except its S1 clause, for the relative piece `η` from `u` with
available lifetime `ζ`; the reflected relative tail `reflectCurve γ` parametrizes the relative
walk `Wrel`. -/
def HasRelTailGeometry (A S Wrel : Set ℂ) (u : ℝ) (η : ℝ≥0 → ℂ) (ζ : ℝ≥0∞) : Prop :=
  ∃ (p : ℝ → ℂ) (β γ : ℝ≥0 → ℂ) (c : Chart) (g J : ℂ → ℂ) (tL : ℝ≥0),
    ContinuousOn p (Icc 0 1) ∧ p 0 = 0 ∧
    (∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p s).im) ∧
    IsProperCurve β ∧ β 0 = 0 ∧ p '' Icc 0 1 ⊆ closedRightSide β ∧
    IsLeftEntryChart (p '' Icc 0 1) (realMin (p '' Icc 0 1)) c ∧
    ContinuousOn g {z | 0 ≤ z.im} ∧ EqOn g c.2.1 H ∧
    β tL = realMin (p '' Icc 0 1) ∧ IsProperCurve γ ∧ γ 0 = 0 ∧
    (∀ s, g (γ s) = β (tL + s)) ∧
    (∃ x : ℝ, 0 < x ∧ realMax (p '' Icc 0 1) < x ∧ (x : ℂ) ∉ range β) ∧
    u ≤ 0 ∧ η 0 = u ∧
    (∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ → 0 ≤ (η t).im) ∧
    range (reflectCurve γ) = Wrel ∧
    Function.Injective J ∧
    A ⊆ J '' (Supp9B.refl '' (g '' (Supp9B.refl '' (η '' {t | (t : ℝ≥0∞) ≤ ζ})))) ∧
    S ⊆ J '' rightSideOf (range (reflectCurve β))

/-- The S1-free data and SB3's S1 conclusion for the relative walk give the sewing data. -/
theorem HasRelTailGeometry.hasActualTailSewing {A S Wrel : Set ℂ} {u : ℝ}
    {η : ℝ≥0 → ℂ} {ζ : ℝ≥0∞} (hg : HasRelTailGeometry A S Wrel u η ζ)
    (hS1 : ∀ γ : ℝ≥0 → ℂ, IsProperCurve γ → γ 0 = 0 → range γ = Wrel →
      ∀ s a : ℝ≥0, (a : ℝ≥0∞) ≤ ζ →
        IsOneSided (γ '' Icc 0 s ∪ ((↑) : ℝ → ℂ) '' Icc u 0) η a) :
    HasActualTailSewing A S := by
  obtain ⟨p, β, γ, c, g, J, tL, hp, hp0, hpH, hβ, hβ0, hA, hc, hgc, hgi, hentry, hγ, hγ0,
    htail, hfree, hu, hη0, hηH, hW, hJ, hnew, hS⟩ := hg
  have hγr0 : reflectCurve γ 0 = 0 := by
    simp only [reflectCurve, hγ0, Supp9B.refl, map_zero, neg_zero]
  exact ⟨p, β, γ, η, c, g, J, tL, ζ, u, hp, hp0, hpH, hβ, hβ0, hA, hc, hgc, hgi, hentry, hγ,
    hγ0, htail, hfree, hu, hη0, hηH,
    fun s a ha => hS1 (reflectCurve γ) (isProperCurve_reflectCurve hγ) hγr0 hW s a ha,
    hJ, hnew, hS⟩

/-- **The S1-free conditional data at one switch** (the input that remains after SB3 is taken
out of `HasConditionalActualTailSewing`): the measurable rational incidence and regularity of
SBSEW's form, and, for almost every retained realization `ω₀`, either the sewing certificate holds
conditionally almost surely on the launch event, or the relative pair is an SB3 instance under
`condExpKernel P 𝒢 ω₀` whose pathwise sewing geometry holds conditionally almost surely on the
launch event. The first
alternative (the sewing certificate given directly) covers a conditionally null launch event and
the degenerate launch with an inadmissible seed (the singleton seed, p. 634: "there is nothing to
add"), where SB3's positive-lifetime premise fails. -/
def HasConditionalRelativeTail (κ : ℝ) {Ω : Type u} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Set Ω) (A S : Ω → Set ℂ) : Prop :=
  ∃ (𝒢 : {m : MeasurableSpace Ω // m ≤ mΩ}) (a : Ω → ℝ≥0 → ℂ),
    NullMeasurableSet F P ∧
    (∀ q : ℚ, MeasurableSet {ω | a ω (q : ℝ).toNNReal ∈ S ω}) ∧
    (∀ᵐ ω ∂P, ω ∈ F → Continuous (a ω) ∧ IsOpen (S ω) ∧ A ω = range (a ω)) ∧
    ∀ᵐ ω₀ ∂P, (∀ᵐ ω ∂(condExpKernel P 𝒢.1 ω₀), ω ∈ F → HasActualTailSewing (A ω) (S ω)) ∨
      ∃ (hQ : Ω → DistOn upperHalfPlaneOpens) (b' : ℝ → ℝ) (jumps' : Finset ℝ)
        (EL : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u' ψ : ℝ) (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞),
        IsRelSB3Instance κ (condExpKernel P 𝒢.1 ω₀) hQ b' jumps' EL u' ψ η ζ ∧
        ∀ᵐ ω ∂(condExpKernel P 𝒢.1 ω₀), ω ∈ F →
          HasRelTailGeometry (A ω) (S ω) (relWalkSet κ b' jumps' EL ω) u' (η ω) (ζ ω)

/-- **The comparison step of SB4.** SBSEW's conditional actual-tail sewing follows from the
S1-free relative data, Lemma SB3 (source form) and Theorems 1.2–1.3. -/
theorem hasConditionalActualTailSewing_of_relativeTail (hSB3 : SB3InductionGenStatement.{u})
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {F : Set Ω} {A S : Ω → Set ℂ}
    (hrel : HasConditionalRelativeTail κ P F A S) : HasConditionalActualTailSewing P F A S := by
  obtain ⟨𝒢, a, hF, hm, hreg, hcond⟩ := hrel
  refine ⟨𝒢, a, hF, hm, hreg, ?_⟩
  filter_upwards [hcond] with ω₀ hω₀
  rcases hω₀ with hdir | ⟨hQ, b', jumps', EL, u', ψ, η, ζ, hI, hgeo⟩
  · exact hdir
  · filter_upwards [ae_isOneSided_of_relSB3Instance hSB3 h12 h13 hκ hκ4 hI, hgeo]
      with ω hS1 hg hωF
    exact (hg hωF).hasActualTailSewing (hS1 · · · ·)

end InteractingSLE.Theorem14.SB.Leaf
