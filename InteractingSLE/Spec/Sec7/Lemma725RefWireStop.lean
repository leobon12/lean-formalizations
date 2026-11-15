/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma725RefRecoveryPocket
import InteractingSLE.Spec.Sec7.Lemma725RefChartGen

/-!
# `PocketChartFieldStatement` at the pocket's stop, with the determination from the ambient recovery

Packet PROVE-LEMMA725REF5. Specification §7.4, Aux. lemmas 124–125 (`source/spec/p385-432.md` L171–L250,
pp. 393–398) and Lemma 7.25's proof (pp. 413–414); ruling R68.

REF4's `pocketChartFieldStatement_of_stop` concludes PROVE-LEMMA725REF3's named input
`Lemma725RefSafe.PocketChartFieldStatement κ r_L r_R` from one pocket on a `𝓦`-event `A`: the pocket's union law
`hU` (marks `𝓦`), the side limit `hside`, and the determination `hdet` of the killed relative history by a
`𝓦`-measurable record and the pocket field. **`pocketChartFieldStatement_of_stop_exteriorDecomp`** replaces `hdet`
by its proved ingredients (`pocketHistDet_of_exteriorDecomp`):

* Aux. lemma 124's exterior decomposition `PocketExteriorDecomp 𝓦 P A C (h₀ + u)` (named input; provided by
  `exists_pocketExteriorDecomp` for every `𝓦` between `σ(E) ∨ σ(h₁)` and `𝒜_E ∨ ℋ`, `E ⊇ ℍ ∖ C` a history-marked
  local set),
* a standard Borel record `E₀` generating `𝓦` up to null sets,
* Proposition 5.13 for the ambient counterflow (`h513`, PROVE-PROP513C's form),
* the measurable pocket erasure (`PocketErasure`, proved by REF4 for the strip pockets).

The ambient recovery itself is proved (`exists_recovery_of_condGFF`). Note (PROVE-LEMMA725REF5's finding on R68): the
decomposition needs `h_B` in `𝓦`, so `hU` is then the union law with the enlarged marks; the WALLS law
(`PocketStopWallsLaw`, local set `Γ ∪ F`) with `h_B` among the marks is false in general (a disc outside the pocket),
so the enlarged union law cannot be obtained through `pocketStopUnionLaw_of_wallsLaw` with the same `𝓦`.

Conditional helper; no source theorem is replaced. Ruling R48: nothing here uses Theorem 1.2/1.3,
`Theorem12ParamStatement`, `Theorem13Statement` or any result taking them as hypotheses.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H chiC fwdHull)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)
open SupercriticalConformalCovariance (IsConformalBijection)
open SupercriticalConformalCovariance.GM24 (smoothDist)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.Lemma725RefRecovery

open PocketTraversal Lemma71C LawUnique PocketStop PocketStopField Lemma725RefChart Lemma725RefSafe PocketCoupling

universe u

section Stop

variable {Ω : Type u} {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- **`PocketChartFieldStatement κ r_L r_R` from one pocket, with the determination from Aux. lemma 124's exterior
decomposition, Proposition 5.13 and the measurable pocket erasure**: REF4's `pocketChartFieldStatement_of_stop` with
`hdet` replaced by `hdec`, `hE₀`, `hgen`, `h513`, `hers` (`pocketHistDet_of_exteriorDecomp`). -/
theorem pocketChartFieldStatement_of_stop_exteriorDecomp [StandardBorelSpace Ω] [IsProbabilityMeasure P]
    {κ rL rR : ℝ} {nL nR : ℕ}
    {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ} (hρL : ρL 0 = rL) (hρR : ρR 0 = rR)
    (hsL : ∀ m : Fin (nL + 1), -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), ρL i)
    (hsR : ∀ m : Fin (nR + 1), -2 < ∑ i ∈ Finset.univ.filter (fun i => i ≤ m), ρR i)
    (h𝓦 : 𝓦 ≤ mΩ) {A : Set Ω} (hA : MeasurableSet[𝓦] A) (hPA : 0 < P A) {γ : Ω → ℝ → ℂ}
    (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω)) (hγm : ∀ u, 0 ≤ u → Measurable fun ω : A => γ ω u)
    (hunb : ∀ ω ∈ A, ∀ M : ℝ, ∃ u, 0 ≤ u ∧ γ ω u ∈ H ∧ M < ‖γ ω u‖)
    {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ}
    (hxLm : Measurable[MeasurableSpace.comap Subtype.val 𝓦] (fun ω : A => xL ω))
    (hxRm : Measurable[MeasurableSpace.comap Subtype.val 𝓦] (fun ω : A => xR ω))
    (hseedL : ∀ ω ∈ A, xL ω 0 = 0) (hseedR : ∀ ω ∈ A, xR ω 0 = 0)
    (hxLd : ∀ ω ∈ A, ∀ i : Fin nL, xL ω i.succ < 0) (hxRd : ∀ ω ∈ A, ∀ j : Fin nR, 0 < xR ω j.succ)
    (hxLi : ∀ ω ∈ A, Antitone (xL ω)) (hxRi : ∀ ω ∈ A, Monotone (xR ω))
    {C : Ω → Set ℂ} (hCo : ∀ ω ∈ A, IsOpen (C ω)) (hCH : ∀ ω ∈ A, C ω ⊆ H) {ψ : Ω → ℂ → ℂ}
    (hψ : ∀ ω ∈ A, IsConformalBijection (ψ ω) (C ω) H) (hCm : ∀ z, MeasurableSet[𝓦] {ω | ω ∈ A ∧ z ∈ C ω})
    (hψm : ∀ z, Measurable[𝓦] ({ω | ω ∈ A ∧ z ∈ C ω}.indicator fun ω => ψ ω z)) {F : ℝ≥0 → Ω → Set ℂ}
    (hFo : ∀ q : ℝ≥0, ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) → IsOpen (H \ F q ω))
    (hgeo : ∀ q : ℝ≥0, ∀ ω ∈ A, (q : ℝ≥0∞) < capLife (γ ω) →
      ψ ω '' (C ω ∩ (H \ F q ω)) = H \ fwdHull (fun s : ℝ => segDriver (γ ω) s.toNNReal) q)
    {h₀ : Ω → DistOn upperHalfPlaneOpens} (hh₀ : IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P) {u : ℂ → ℝ}
    (hu : InnerProductSpace.HarmonicOnNhd u H) (hub : ∃ M : ℝ, ∀ z ∈ H, |u z| ≤ M) {n : Ω → ℤ}
    (hn : Measurable[𝓦] n) {a : ℝ} (hU : ∀ q : ℝ≥0, PocketStopUnionLaw 𝓦 P A γ C (F q) h₀ q)
    (hside : ∀ q : ℝ≥0, PocketStopSideLimit κ ρL ρR P A γ xL xR (fun ω => shiftChart (pChart A C ψ ω) (n ω)) a h₀
      u (activeCompl A γ (fun ω => shiftChart (pChart A C ψ ω) (n ω)) q) q)
    (hdec : PocketExteriorDecomp 𝓦 P A C (fun ω => h₀ ω + smoothDist upperHalfPlaneOpens u))
    {ε₀ : Type u} [MeasurableSpace ε₀] [StandardBorelSpace ε₀] {E₀ : Ω → ε₀} (hE₀ : Measurable[𝓦] E₀)
    (hgen : 𝓦 ≤ MeasurableSpace.comap E₀ inferInstance ⊔ Ito.nullSets P) {η : Ω → ℝ → ℂ}
    (h513 : ∃ Γ' : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[MeasurableSpace.comap
      (fun ω => h₀ ω + smoothDist upperHalfPlaneOpens u) inferInstance] fun ω => Γ' ω t) ∧
      ∀ᵐ ω ∂P, Γ' ω = fun t : ℝ≥0 => η ω t)
    (hers : PocketErasure 𝓦 P A γ xL xR η) :
    PocketChartFieldStatement.{u} κ rL rR := by
  have hdet := pocketHistDet_of_exteriorDecomp (κ := κ) (γ := γ) (xL := xL) (xR := xR) h𝓦 hA hCo hCH hψ hCm hψm
    (measurable_add_smoothDist hh₀.measurable u) hdec hE₀ hgen h513 hers
  obtain ⟨ε, mε, hSBε, E, g, hEm, hg, hdetω⟩ := hdet n hn a
  exact pocketChartFieldStatement_of_stop hρL hρR hsL hsR h𝓦 hA hPA hγ hγm hunb hxLm hxRm hseedL hseedR hxLd hxRd
    hxLi hxRi hCo hCH hψ hCm hψm hFo hgeo hh₀ hu hub hn hU hside hEm hg hdetω

end Stop

end InteractingSLE.Sec7.Lemma725RefRecovery
