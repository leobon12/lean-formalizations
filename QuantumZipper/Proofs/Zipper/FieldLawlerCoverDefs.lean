import QuantumZipper.Proofs.Zipper.FieldLawlerDefs
import QuantumZipper.Proofs.Thm18.LWExcDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL-THM-COVER: the two sub-nodes of `FieldLawler.FLCoverStmt`

**Source.** L. S. Field, G. F. Lawler, *Escape probability and transience for SLE*,
EJP 20 (2015) no. 10, arXiv:1407.3314 (`literature/1407.3314.pdf`).

`FLCoverStmt` (FieldLawlerDefs.lean) is reduced, in `FieldLawlerCover.lean`
(`flCover_of_imageSum_excLower`, proved there by the FL-THM-COVER agent), to the two nodes below.
The reduction itself is the elementary last step of FL's argument: a point under an image
crosscut `η'` with real endpoint `a` lies in `B̄(a, diam η')` (the half-plane outside that disk is
connected and unbounded), so the disks `B(aⱼ, 2 diam η'ⱼ)` cover, and
`2 diam η'ⱼ / |aⱼ| ≤ (2/c₁) ℰ_ℍ(η'ⱼ, opposite half-line)` by the lower bound.

* `FLImageCrosscutSumStmt` (open; for a helper): FL proof of **Prop. 3.4** (p. 9) transported to
  `ℍ` by `Z_t = fwdMap W t` (conformal invariance of excursion measure, Lawler, *Conformally
  invariant processes in the plane*, Prop. 5.8), together with the first inequality of the display
  in the proof of **Prop. 3.1** (p. 7, `ℰ_ℍ(η', γ̃') ≥ ℰ_ℍ(η', ℝ₋)`) and the topology that the image
  `Z_t(H_t ∩ B(0, ε))` lies under the image crosscuts `Z_t ηⱼ` of the components `ηⱼ` of
  `H_t ∩ {|z| = ε}`. Its analytic inputs are **Lemma 3.3** (p. 8, proof §4 pp. 10–12) and
  **(2.4)** (p. 6).
* `FLExcLowerStmt` (open; for a helper): the lower bound of the proof of **Prop. 3.1** (p. 7),
  `ℰ_ℍ(η, ℝ₋) ≥ c (diam η / dist(0, η) ∧ 1)` for a crosscut with both endpoints on `(0, ∞)`, which
  FL take from their **Corollary 5.2** (pp. 12–13). Here `dist(0, η)` is replaced by the distance
  `|a|` to the endpoint `a = η(0+)` (a weaker statement, since `dist(0, η) ≤ |a|`). In the regime
  `diam η ≤ |a|/2` this is **Lawler–Werness Lemma 4.3** (`lw43_holds`, proved) after the map
  `z ↦ -conj z / a` (resp. `z ↦ z / |a|`); the `∧ 1` regime needs FL Corollary 5.2 / Lemma 5.1.

Excursion measures are LW's `excR h J = ∫_J ∂_y h` with `h` the harmonic measure of the arc in
the unbounded component `hullComp η` of `ℍ \ η` (`Thm18/LWExcDefs.lean`).
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar

/-- **Image crosscut sum (FL proof of Prop. 3.4, p. 9, via conformal invariance, with the first
inequality of the Prop. 3.1 display, p. 7).** Under the hypotheses of `FLCoverStmt`, there is a
countable family (indexed by `S ⊆ ℕ`) of crosscuts `η j` of `ℍ` (the images `Z_t ηⱼ` of the
components of `H_t ∩ {|z| = ε}`), with real endpoints `a j`, `b j` on one side of `0`, harmonic
measures `h j` of `η j` in the unbounded component of `ℍ \ η j`, such that
`Σ_{j ∈ S} ℰ_ℍ(η j, opposite half-line) ≤ C ε / R` and every point of `Z_t(H_t ∩ B(0, ε))`
lies under (i.e. not in the unbounded component of `ℍ` minus) one of them. -/
def FLImageCrosscutSumStmt : Prop :=
  ∃ C δ₀ : ℝ, 0 ≤ C ∧ 0 < δ₀ ∧ ∀ (W : ℝ → ℝ), Continuous W → W 0 = 0 →
    ∀ t R ε : ℝ, 0 ≤ t → 0 < R → 0 < ε → ε ≤ δ₀ * R →
    trace W 0 = 0 → ContinuousOn (trace W) (Icc 0 t) → InjOn (trace W) (Icc 0 t) →
    (∀ s ∈ Ioc 0 t, trace W s ∈ H) →
    fwdHull W t = trace W '' Ioc 0 t →
    (∀ s ∈ Ico 0 t, ‖trace W s‖ < R) → ‖trace W t‖ = R →
    Tendsto (fun y : ℝ => fwdMapInv W t (y * Complex.I)) (𝓝[>] 0) (𝓝 (trace W t)) →
    ∃ (S : Set ℕ) (η : ℕ → ℝ → ℂ) (a b : ℕ → ℝ) (h : ℕ → ℂ → ℝ),
      (∀ j ∈ S, IsCrosscutH (η j) ∧ Tendsto (η j) (𝓝[>] 0) (𝓝 (a j : ℂ)) ∧
        Tendsto (η j) (𝓝[<] 1) (𝓝 (b j : ℂ)) ∧ 0 < a j * b j ∧
        IsHarmMeas (hullComp (η j)) (arcH (η j)) (h j)) ∧
      ∑' j, S.indicator (fun j => excR (h j) {x : ℝ | x * a j ≤ 0}) j ≤
        ENNReal.ofReal (C * (ε / R)) ∧
      ∀ p ∈ H, ‖fwdMapInv W t p‖ < ε → ∃ j ∈ S, p ∉ hullComp (η j)

/-- **Excursion lower bound (FL proof of Prop. 3.1, p. 7, via FL Corollary 5.2, pp. 12–13).**
For a crosscut `η` of `ℍ` with real endpoints `a = η(0+)`, `b = η(1−)` on the same side of `0`
and `h` the harmonic measure of `η` in the unbounded component of `ℍ \ η`,
`ℰ_ℍ(η, opposite half-line) ≥ c₁ (diam η / |a| ∧ 1)`. -/
def FLExcLowerStmt : Prop :=
  ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ (η : ℝ → ℂ) (a b : ℝ) (h : ℂ → ℝ),
    IsCrosscutH η → Tendsto η (𝓝[>] 0) (𝓝 (a : ℂ)) → Tendsto η (𝓝[<] 1) (𝓝 (b : ℂ)) →
    0 < a * b → IsHarmMeas (hullComp η) (arcH η) h →
    ENNReal.ofReal (c₁ * min (Metric.diam (arcH η) / |a|) 1) ≤ excR h {x : ℝ | x * a ≤ 0}

end FieldLawler
end QuantumZipper
