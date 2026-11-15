/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB4SewGermUnion
import InteractingSLE.Spec.Sec7.Lemma71OWall

/-!
# The boundary-hitting mean identification for relative explorations: the statement

Packet PROVE-BHMEAN. Astra's follow-up 3, Q3 §3.3 ("The mean at deterministic times: all incident sides and one
lift", `source/external/AstraIG1/ig1_followup3_audited.txt` L796–L872) and follow-up 5 §4.3 (L839–L842: "On each
positive-separation buffer, the transition chart reflects with positive derivative across the exposed counterflow
base. The one inherited logarithm has its initial zero phase and keeps that phase by continuity. The adopted collar
comparisons and finite-exception uniqueness identify the complete Poisson mean").

Both GB6 (Theorem 1.4: a counterflow explored relative to a stopped flow prefix, `GB6RelStopKernelStatement`) and
GW2's joint (Det) (a flow line explored relative to a stopped counterflow prefix, `GW2JointDetC2Statement`) need the
same deterministic fact, for curves that may hit the real line. It is stated here **once**, in the coordinates of the
explored curve (the physical coordinates of the field it is coupled with):

* the **retained set** `A ⊆ ℍ` (the stopped prefix of the other curve, read in these coordinates) has a conformal chart
  `Ψ : ℍ ∖ A → ℍ` with inverse `Ψi` and a logarithm `LΨ` of `Ψ'` (`IsRetainedChart`): for GB6 `Ψ = relMap Wα s`,
  for GW2 `Ψ = relMap W s` (`Supp8.GB6.relMap`), with the lift normalized to have zero imaginary part on the real
  interval `ℝ ∖ cl A` around the explored curve's seed;
* the **explored chain** (driver `w`, continuous trace `η`) at time `t` has a hull `K_t` with
  `cl K_t ∩ cl A = ∅` (before the first contact), and its image `Ψ(K_t)` is the hull `K̃_u` of the **relative chain**
  (driver `W̃`, trace `η̃`) at the relative time `u` (`Supp8.GB6.exists_glued_relChain`);
* the **individual means** are the explicit ones: the retained set's conditional mean is the bounded harmonic
  extension `G₀` of the retained word `β₀`, read through `Ψ` (`G₀ ∘ Ψ − χ Im LΨ`; for GB6 this is (R1),
  `gb6_condDet_r1`); the explored curve's is its coupling mean `GE ∘ f_t − χ Im log f_t'`;
* the **candidate** is the relative coupling mean read through `Ψ`:
  `v = G ∘ f̃_u ∘ Ψ − χ (Im log f̃_u' ∘ Ψ + Im LΨ)`, with `G` the bounded harmonic extension of the relative word
  `βu` at time `u`.

The three word facts used are the ones the canonical words satisfy: on the explored and on the relative hull image
(the real points whose inverse-map landing point lies in the closed hull) the words are the side heights `±λ`
(`IsSideWord`; the force points of a geometric word sit at the ends of the hull image); off the relative hull image
the relative word at time `u` is the retained word at the landing point (`IsFlowedWord`, the real Loewner flow of the
force points). The one geometric fact on the two chains beyond the hull identity is that the relative tip is the
image of the explored tip (`f_t ∘ Ψi ∘ f̃_u⁻¹ → 0` at `0`, the Schramm–Wilson coordinate-change identity
`W̃_{a(t)} = Φ_t(W_t)`).

The conclusion is the union prime-end classification `SB.SewGerm.HasUnionWordBoundary` with the joint chart
`f̃_u ∘ Ψ`: every prime end of the joint complement off finitely many is a side of the retained set or an original real
point (where the retained mean has the candidate's boundary value) or a side of the explored hull (where the explored
mean has it: the transition `f_t ∘ Ψi ∘ f̃_u⁻¹` reflects across the hull image with positive derivative and its one
integer lift is pinned to zero at the adjacent untouched real points). With
`SB.SewGerm.ae_survivingWordBoundary_union` and `SB.SewGerm.ae_eqOn_physicalMean_of_boundary` this identifies the
conditional mean of the field given both marked sets.

* **`IsRetainedChart`**, **`IsSideWord`**, **`IsFlowedWord`**;
* **`RelUnionWordBoundaryStatement`** (the statement);
* `HasUnionWordBoundary.swap`: the datum is symmetric in the two sets, so the statement serves both role
  assignments (GB6: retained = flow prefix; GW2: retained = counterflow prefix).

Conditional helpers with distinct names; they replace no source theorem. R48: GB6 and GW2 serve Theorem 1.4.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric Complex
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull logDerivFwd)
open SupercriticalConformalCovariance (IsConformalBijection)

namespace InteractingSLE.Supp8.BHMean

open Theorem14.SB.SewGerm (HasUnionWordBoundary)

/-- **The chart of the retained component**: `Ψ` maps `ℍ ∖ A` conformally onto `ℍ` with inverse `Ψi` (holomorphic on
`ℍ`) and a logarithm `LΨ` of `Ψ'`; `Ψi` lands at every real point; `Ψ` lands at a real point at every real point off
`cl A`, where the lift has zero imaginary part. -/
structure IsRetainedChart (A : Set ℂ) (Ψ Ψi LΨ : ℂ → ℂ) : Prop where
  isOpen : IsOpen (H \ A)
  conf : IsConformalBijection Ψ (H \ A) H
  inv_mem : ∀ v ∈ H, Ψi v ∈ H \ A
  fwd_inv : ∀ v ∈ H, Ψ (Ψi v) = v
  diff_inv : DifferentiableOn ℂ Ψi H
  log : IsDerivLog Ψ LΨ (H \ A)
  inv_lands : ∀ x : ℝ, ∃ p, Tendsto Ψi (𝓝[H] (x : ℂ)) (𝓝 p)
  fwd_lands : ∀ y : ℝ, (y : ℂ) ∉ closure A → ∃ x : ℝ, Tendsto Ψ (𝓝[H \ A] (y : ℂ)) (𝓝 (x : ℂ))
  lift_real : ∀ y : ℝ, (y : ℂ) ∉ closure A → Tendsto (fun z => (LΨ z).im) (𝓝[H \ A] (y : ℂ)) (𝓝 0)

/-- **The side word of a hull**: at every real point `x ≠ 0` off the jump set whose inverse-map landing point lies in
the closed hull `K` (the hull image), the word is the side height `λ` (right) or `−λ` (left). -/
def IsSideWord (β : ℝ → ℝ) (S : Finset ℝ) (F : ℂ → ℂ) (K : Set ℂ) (lam : ℝ) : Prop :=
  ∀ x : ℝ, x ∉ S → x ≠ 0 → extendFrom H F (x : ℂ) ∈ closure K → β x = if 0 < x then lam else -lam

/-- **The flowed word**: at every real point `x` off the jump set whose inverse-map landing point `y` lies off the
closed hull `K`, the word at `x` is the initial word `β₀` at `Re y` (when `Re y` is off its jump set). -/
def IsFlowedWord (β β₀ : ℝ → ℝ) (S S₀ : Finset ℝ) (F : ℂ → ℂ) (K : Set ℂ) : Prop :=
  ∀ x : ℝ, x ∉ S → extendFrom H F (x : ℂ) ∉ closure K → (extendFrom H F (x : ℂ)).re ∉ S₀ →
    β x = β₀ (extendFrom H F (x : ℂ)).re

/-- **The boundary-hitting mean identification for relative explorations** (deterministic; Astra Q3 §3.3 and
follow-up 5 §4.3; GB6, p. 519–520; GW2's joint (Det)). Retained set `A` with chart `(Ψ, Ψi, LΨ)`; explored chain
`(w, η)` at time `t`; relative chain `(Wr, ηr)` at time `u` with `Ψ(K_t) = K̃_u`; closed hulls disjoint; the relative
tip is the image of the explored tip; explicit individual means and candidate (module docstring). Then the joint
complement has the union word boundary datum of the two individual means, with the relative word `βu` at time `u`. -/
def RelUnionWordBoundaryStatement : Prop :=
  ∀ (A : Set ℂ) (Ψ Ψi LΨ : ℂ → ℂ) (w Wr : ℝ → ℝ) (η ηr : ℝ → ℂ) (t u χ lam : ℝ)
    (β₀ βE βu : ℝ → ℝ) (S₀ SE Su : Finset ℝ) (G₀ GE G u₀ w₁ w₂ v : ℂ → ℝ),
    IsRetainedChart A Ψ Ψi LΨ →
    Continuous w → w 0 = 0 → IsLoewnerTrace w η → 0 ≤ t →
    Continuous Wr → Wr 0 = 0 → IsLoewnerTrace Wr ηr → 0 ≤ u →
    Ψ '' fwdHull w t = fwdHull Wr u →
    Disjoint (closure (fwdHull w t)) (closure A) →
    Tendsto (fun y => fwdMap w t (Ψi (fwdMapInv Wr u y))) (𝓝[H] 0) (𝓝 0) →
    IsBoundedHarmonicExtension β₀ S₀ G₀ → IsBoundedHarmonicExtension βE SE GE →
    IsBoundedHarmonicExtension βu Su G →
    IsSideWord βE SE (fwdMapInv w t) (fwdHull w t) lam →
    IsSideWord βu Su (fwdMapInv Wr u) (fwdHull Wr u) lam →
    IsFlowedWord βu β₀ Su S₀ (fwdMapInv Wr u) (fwdHull Wr u) →
    EqOn (fun z => w₁ z + u₀ z) (fun z => G₀ (Ψ z) - χ * (LΨ z).im) (H \ A) →
    EqOn (fun z => w₂ z + u₀ z) (fun z => GE (fwdMap w t z) - χ * (logDerivFwd w t z).im) (H \ fwdHull w t) →
    (∀ z, v z = G (fwdMap Wr u (Ψ z)) - χ * ((logDerivFwd Wr u (Ψ z)).im + (LΨ z).im)) →
    HasUnionWordBoundary A (fwdHull w t) u₀ v w₁ w₂ χ βu Su

/-- **The union datum is symmetric in the two sets** (swap the sets, their means and the two alternatives). -/
theorem HasUnionWordBoundary.swap {A₁ A₂ : Set ℂ} {u₀ v w₁ w₂ : ℂ → ℝ} {χ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    (h : HasUnionWordBoundary A₁ A₂ u₀ v w₁ w₂ χ b jumps) : HasUnionWordBoundary A₂ A₁ u₀ v w₂ w₁ χ b jumps := by
  intro z₀ hz₀
  rw [union_comm] at hz₀ ⊢
  obtain ⟨f, φc, G, L, E, hf, hφc, hG, hL, hd, hE, hv, hlim⟩ := h z₀ hz₀
  exact ⟨f, φc, G, L, E, hf, hφc, hG, hL, hd, hE, hv, fun q hq hqE => (hlim q hq hqE).symm⟩

end InteractingSLE.Supp8.BHMean
