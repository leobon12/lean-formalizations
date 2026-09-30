import QuantumZipper.Proofs.Thm18.G1ProfileRed

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-PROFILE: split of the deterministic profile input into named parts

`G1RC.G1ProfileDetStmt` (`G1ProfileRed.lean`; it implies `G1RC.G1ProfileStmt` by
`G1RC.g1ProfileStmt_of_det'`) asks, for every continuous path `a` whose SLE_{γ²} trace is a
simple chord and each side, for the conclusion `ProfileConcl` about the pushed circles
`ν = ψ_* fc(d, r)`, `ψ = Ψ left a` (the inverse of a normalized uniformizer of the side component,
`G1PsiSel`). This file

* proves the **carry lemma** `ae_mem_Hbar_map_invFunOn` (first clause of `ProfileGood`) and its
  instance for the selected maps, `ae_mem_Hbar_map_psi`;
* names the remaining parts, all deterministic in the path:
  `G1ProfileGapStmt` (for large `k`, `ν` does not charge the circle `{‖w‖ = 2^{-k}}`),
  `G1ProfileIntStmt` (integrability of the free-field and profile parts),
  `G1ProfileConvStmt` (convergence of the profile part) and `G1ProfileContStmt` (continuity and
  smoothing symmetry of the resulting `D`);
* proves `g1ProfileDetStmt_of_parts` and `g1ProfileStmt_of_parts` (bookkeeping, own).

Sources for the split: Sheffield, arXiv:1012.4797, §5.4 (the profile part of the canonical
description); the gap clause is an own device of G1-RC (DEVIATIONS-QUEUE, G1-RC entry).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Metric Set Function Real
open scoped ENNReal NNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G1RC

open WedgeTK CircleFubini

/-- **Carry lemma**. Let `D ⊆ ℍ` be a side component with a normalized uniformizer `φ`, and let
`ψ` agree with `invFunOn φ D` on `ℍ`. Then the pushforward of any folded circle of positive
radius by `ψ` is carried by `Hbar`.

This is the first clause of `G1RC.ProfileGood` for the pushed circles of `G1`. Own elementary
argument: a.e. point of a folded circle lies in `ℍ` (`TwoPoint.foldedCircle_ae_mem_H`), where
`ψ = invFunOn φ D` takes values in `D ⊆ ℍ ⊆ Hbar` because `φ '' D = ℍ` (`Set.BijOn.surjOn`). -/
theorem ae_mem_Hbar_map_invFunOn {D : Set ℂ} {φ ψ : ℂ → ℂ} (hφ : IsNormalizedUniformizer D φ)
    (hDH : D ⊆ H) (heq : EqOn ψ (invFunOn φ D) H) {d : ℂ} {r : ℝ} (hr : 0 < r)
    (hm : AEMeasurable ψ (foldedCircle d r)) :
    ∀ᵐ w ∂(foldedCircle d r).map ψ, w ∈ Hbar := by
  refine (ae_map_iff hm isClosed_Hbar.measurableSet).2 ?_
  filter_upwards [TwoPoint.foldedCircle_ae_mem_H d hr] with z hz
  rw [heq hz]
  obtain ⟨z', hz'D, hz'⟩ := hφ.1.surjOn hz
  exact H_subset_Hbar (hDH (Function.invFunOn_mem (f := φ) (s := D) (b := z) ⟨z', hz'D, hz'⟩))

/-- The carry lemma for the selected maps on a continuous simple-chord path. -/
theorem ae_mem_Hbar_map_psi {γ : ℝ} {Ψ : Bool → (ℝ≥0 → ℝ) → ℂ → ℂ} (hΨ : G1PsiSel γ Ψ)
    {a : ℝ≥0 → ℝ} (hc : Continuous a) (hs : IsSimpleChord (pathTrace (γ ^ 2) a)) (left : Bool)
    {d : ℂ} {r : ℝ} (hr : 0 < r) :
    ∀ᵐ w ∂(foldedCircle d r).map (Ψ left a), w ∈ Hbar := by
  obtain ⟨φ, hφ, hΨa⟩ := hΨ.2.2 a hc hs left
  have hDH : sideDom (pathTrace (γ ^ 2) a) left ⊆ H := by
    cases left
    · exact rightComponent_subset_H _
    · exact leftComponent_subset_H _
  have hm : AEMeasurable (Ψ left a) (foldedCircle d r) :=
    ((hΨ.1 left).comp (measurable_const.prodMk measurable_id)).aemeasurable
  exact ae_mem_Hbar_map_invFunOn hφ hDH (by rw [hΨa]; exact eqOn_refl _ _) hr hm

/-- The common hypotheses of the deterministic parts: a selection `Ψ`, a continuous path `a`
with simple-chord trace, a side, and a regular version `G` of the free field. -/
def G1DetSetting (C : ∀ (_γ : ℝ) {Ω' : Type} [MeasurableSpace Ω'] (_P' : Measure Ω')
    (_X : Ω' → FieldSample) (_A : ℝ → Ω' → ℝ) (_ψ : ℂ → ℂ) (_G : Ω' → ℂ × ℝ → ℝ), Prop) :
    Prop :=
  G1RepSetting fun γ _ _ _ _ _ _ P' X A => ∀ Ψ, G1PsiSel γ Ψ →
    ∀ a : ℝ≥0 → ℝ, Continuous a → IsSimpleChord (pathTrace (γ ^ 2) a) → ∀ left : Bool,
      ∀ G, IsRegVersion X P' G → C γ P' X A (Ψ left a) G

/-- **Gap part.** For large `k` the pushed circle does not charge `{‖w‖ = 2^{-k}}` (an analytic
arc lies on at most one circle about `0` unless it is contained in it). Deterministic. -/
def G1ProfileGapStmt : Prop :=
  G1DetSetting fun _ _ _ _ _ _ ψ _ => ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r →
    ∀ᶠ k : ℕ in atTop, ∀ᵐ w ∂((foldedCircle d r).map ψ), ‖w‖ ≠ radius k

/-- **Integrability part**: the free-field part and the profile part along the pushed circle. -/
def G1ProfileIntStmt : Prop :=
  G1DetSetting fun γ _ _ P' X A ψ G => ∀ᵐ ω' ∂P', ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r →
    (∀ k : ℕ, Integrable (fun w => G ω' ((scaleParam γ (wedge0 γ X A ω') : ℂ) * w,
        scaleParam γ (wedge0 γ X A ω') * radius k)) ((foldedCircle d r).map ψ)) ∧
    (∀ k : ℕ, Integrable (fun w => ∫ u, WedgeCan.wedgeProfile (X ω') (fun t => A t ω')
        (Qc γ) u ∂foldedCircle ((scaleParam γ (wedge0 γ X A ω') : ℂ) * w)
          (scaleParam γ (wedge0 γ X A ω') * radius k)) ((foldedCircle d r).map ψ))

/-- **Convergence part**: the profile part along the pushed circle converges. -/
def G1ProfileConvStmt : Prop :=
  G1DetSetting fun γ _ _ P' X A ψ _ => ∀ᵐ ω' ∂P', ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r →
    ∃ Lp : ℝ, Tendsto (fun k : ℕ => ∫ w, (∫ u, WedgeCan.wedgeProfile (X ω')
        (fun t => A t ω') (Qc γ) u ∂foldedCircle ((scaleParam γ (wedge0 γ X A ω') : ℂ) * w)
          (scaleParam γ (wedge0 γ X A ω') * radius k)) ∂((foldedCircle d r).map ψ))
      atTop (𝓝 Lp)

/-- **Continuity part**: continuity and smoothing symmetry of `dPart` on `Hbar × (0,∞)`. -/
def G1ProfileContStmt : Prop :=
  G1DetSetting fun γ _ _ P' X A ψ _ => ∀ᵐ ω' ∂P',
    ContinuousOn (dPart γ X A ψ ω') (Hbar ×ˢ Ioi 0) ∧
    ∀ w ∈ Hbar, ∀ r ρ : ℝ, 0 < r → 0 < ρ →
      ∫ u, dPart γ X A ψ ω' (u, ρ) ∂foldedCircle w r =
        ∫ v, dPart γ X A ψ ω' (v, r) ∂foldedCircle w ρ

/-- **`G1ProfileDetStmt` from the four parts** (with the carry lemma). Own bookkeeping. -/
theorem g1ProfileDetStmt_of_parts (h1 : G1ProfileGapStmt) (h2 : G1ProfileIntStmt)
    (h3 : G1ProfileConvStmt) (h4 : G1ProfileContStmt) : G1ProfileDetStmt := by
  intro γ hγ hγ2 Ω _ P _ B hB Ω' _ P' _ X A hX hA hXA Ψ hΨ a hc hs left G hG
  have e1 := h1 γ hγ hγ2 P B hB P' X A hX hA hXA Ψ hΨ a hc hs left G hG
  filter_upwards [h2 γ hγ hγ2 P B hB P' X A hX hA hXA Ψ hΨ a hc hs left G hG,
    h3 γ hγ hγ2 P B hB P' X A hX hA hXA Ψ hΨ a hc hs left G hG,
    h4 γ hγ hγ2 P B hB P' X A hX hA hXA Ψ hΨ a hc hs left G hG] with ω' hω2 hω3 hω4
  exact ⟨fun d hd r hr => ⟨ae_mem_Hbar_map_psi hΨ hc hs left hr, e1 d hd r hr,
    (hω2 d hd r hr).1, (hω2 d hd r hr).2, hω3 d hd r hr⟩, hω4.1, hω4.2⟩

/-- **`G1ProfileStmt` from the four deterministic parts.** -/
theorem g1ProfileStmt_of_parts (h1 : G1ProfileGapStmt) (h2 : G1ProfileIntStmt)
    (h3 : G1ProfileConvStmt) (h4 : G1ProfileContStmt) : G1ProfileStmt :=
  g1ProfileStmt_of_det' (g1ProfileDetStmt_of_parts h1 h2 h3 h4)

end G1RC
end Thm18Asm
end QuantumZipper
