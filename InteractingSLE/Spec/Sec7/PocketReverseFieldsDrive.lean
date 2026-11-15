/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketReverseFields
import InteractingSLE.Spec.Sec7.PocketLife

/-!
# The erased counterflow traversal of the change pocket is a driven curve with large points (`hγ`, `hunb`)

Packet PROVE-STRIPSYS18 (specification §7.4.1, proof of Lemma 7.25, p. 414: "The erased counterflow is therefore a
complete continuous traversal of this actual Jordan pocket with a continuous relative driver"; Aux. lemmas 40–41,
pp. 203–206; proof of Aux. lemma 125, pp. 396–397: "`|X_C(s)| → ∞`").

For the change pocket `m(C)` of Aux. lemma 130 in the counterflow chart, with the counterflow `η` and its first visits
`τ = T(y₀)`, `σ = T(x₀)` (`firstHit`), the relative curve of the erased traversal in a Jordan coordinate `ψ` is

* `cfTraversal R L r η ψ = relCurve (ψ ∘ γ̂_C) ℓ(σ)` when the pocket is bounded in the counterflow chart, and
* `cfTraversalInf R L r η ψ = relCurve (ψ ∘ γ̂_C) ℓ(∞)` when it opens at the flow seed.

Combining this packet's `IsReversePocket(Inf)` for the change pocket (`isReversePocket(Inf)_of_counterflow`) with
PROVE-STRIPSYS10's driven relative curve and PROVE-STRIPSYS13's large points, both are **driven curves with points of
`ℍ` of arbitrarily large modulus** — the hypotheses `hγ`, `hunb` of `PocketPhaseMeans.pocketWordEvolution_of_charFun`
— under Aux. lemma 37's attachment constancy (and the counterflow's transience in the second case). The coordinate `ψ`
is a parameter, so that a measurable choice (PROVE-STRIPSYS17's `exists_measurable_cfJordanCoord(Inf)`) can be used.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric Function Bornology
open QuantumZipper (H Hbar)
open InteractingSLE.WangWu (negInv)
open scoped NNReal

namespace InteractingSLE.Sec7.PocketJordan

open WangWu PocketCoord Lemma71I PocketTraversal

/-- **The erased counterflow traversal of the change pocket** (bounded case) in the Jordan coordinate `ψ`, read on
`[0, ∞)` (`relCurve`), between the first visits of `m(y₀)` and `m(x₀)`. -/
def cfTraversal (R L : ℝ≥0 → ℂ) (r : ℝ≥0) (η : ℝ → ℂ) (ψ : ℂ → ℂ) : ℝ → ℂ :=
  relCurve (fun v => ψ (Sec6.erasedPath η (cfPocket R L r) (firstHit η (cfArcR R L r 1))
    (firstHit η (cfArcR R L r 0)) v))
    (Sec6.pocketClock η (cfPocket R L r) (firstHit η (cfArcR R L r 1)) (firstHit η (cfArcR R L r 0))
      (firstHit η (cfArcR R L r 0)))

/-- **The erased counterflow traversal of the change pocket opening at the flow seed** in the Jordan coordinate at
infinity `ψ`, after the first visit of `m(y₀)`. -/
def cfTraversalInf (R L : ℝ≥0 → ℂ) (r : ℝ≥0) (η : ℝ → ℂ) (ψ : ℂ → ℂ) : ℝ → ℂ :=
  relCurve (fun v => ψ (Sec6.erasedPathInf η (cfPocket R L r) (firstHit η (cfArcRInf R L r 0)) v))
    (Sec6.clockEnd η (cfPocket R L r) (firstHit η (cfArcRInf R L r 0)))

end InteractingSLE.Sec7.PocketJordan

namespace InteractingSLE.Sec7.PocketCoord.IsChangeConfigInc

open WangWu Lemma71I PocketJordan PocketTraversal

variable {R L : ℝ≥0 → ℂ} {r : ℝ≥0}

theorem cfArcR_zero : cfArcR R L r 0 = cfPt (openPt R L r) := by simp [cfArcR, openPt]

theorem cfArcR_one : cfArcR R L r 1 = cfPt (closePt R L r) := by simp [cfArcR, closePt]

theorem cfArcRInf_zero : cfArcRInf R L r 0 = cfPt (closePt R L r) := by simp [cfArcRInf, closePt]

/-- **The erased traversal of the change pocket is a driven curve with large points** (bounded case; Lemma 7.25's
proof, p. 414, and Aux. lemma 125): from the counterflow's trace, the reverse visit order of the two walls with their
points visited, Aux. lemma 37's attachment constancy, and a Jordan coordinate `ψ` of the pocket (`m(x₀) ↦ ∞`,
`m(y₀) ↦ 0`). -/
theorem isDrivenCurve_cfTraversal (h : IsChangeConfigInc R L r) (h0 : (0 : ℂ) ∉ closure (changePocket R L r))
    {W : ℝ → ℝ} {η : ℝ → ℂ} (trace : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hrevR : IsWallReverseVisit R η) (hrevL : IsWallReverseVisit L η) (hvisR : IsWallVisited R η)
    (hAC : Sec6.AttachmentConstancy η (cfPocket R L r) (cfArcR R L r) (cfArcL R L r)
      (firstHit η (cfArcR R L r 1)) (firstHit η (cfArcR R L r 0)))
    {ψ : ℂ → ℂ} (hψ : Sec6.IsJordanCoord (cfPocket R L r) (cfPt (openPt R L r)) (cfPt (closePt R L r)) ψ) :
    IsDrivenCurve (cfTraversal R L r η ψ) ∧
      ∀ M : ℝ, ∃ u, 0 ≤ u ∧ cfTraversal R L r η ψ u ∈ H ∧ M < ‖cfTraversal R L r η ψ u‖ := by
  have hP := h.isReversePocket_of_counterflow h0 trace hW hW0 hrevR hrevL hvisR
  have hψ' : Sec6.IsJordanCoord (cfPocket R L r) (cfArcR R L r 0) (cfArcR R L r 1) ψ := by
    rw [cfArcR_zero, cfArcR_one]
    exact hψ
  exact ⟨isDrivenCurve_relCurve_of_isReversePocket hP hAC hψ',
    PocketLife.exists_relCurve_mem_H_lt_norm_of_isReversePocket hP hAC hψ'⟩

/-- **The erased traversal of the change pocket opening at the flow seed is a driven curve with large points**: from
the counterflow's trace and transience, the reverse visit order of the two walls with their points visited, Aux. lemma
37's attachment constancy at infinity, and a Jordan coordinate at infinity `ψ` of the pocket (`m(y₀) ↦ 0`). -/
theorem isDrivenCurve_cfTraversalInf (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0)
    {W : ℝ → ℝ} {η : ℝ → ℂ} (trace : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (htr : Tendsto (fun t => ‖η t‖) atTop atTop)
    (hrevR : IsWallReverseVisit R η) (hrevL : IsWallReverseVisit L η) (hvisR : IsWallVisited R η)
    (hvisL : IsWallVisited L η)
    (hAC : Sec6.AttachmentConstancyInf η (cfPocket R L r) (cfArcRInf R L r) (cfArcLInf R L r)
      (firstHit η (cfArcRInf R L r 0)))
    {ψ : ℂ → ℂ} (hψ : Sec6.IsJordanCoordInf (cfPocket R L r) (cfPt (closePt R L r)) ψ) :
    IsDrivenCurve (cfTraversalInf R L r η ψ) ∧
      ∀ M : ℝ, ∃ u, 0 ≤ u ∧ cfTraversalInf R L r η ψ u ∈ H ∧ M < ‖cfTraversalInf R L r η ψ u‖ := by
  have hP := h.isReversePocketInf_of_counterflow h0 trace hW hW0 hrevR hrevL hvisR hvisL
  have hψ' : Sec6.IsJordanCoordInf (cfPocket R L r) (cfArcRInf R L r 0) ψ := by
    rw [cfArcRInf_zero]
    exact hψ
  exact ⟨isDrivenCurve_relCurve_of_isReversePocketInf hP hAC hψ',
    PocketLife.exists_relCurve_mem_H_lt_norm_of_isReversePocketInf hP hAC hψ' htr⟩

end InteractingSLE.Sec7.PocketCoord.IsChangeConfigInc
