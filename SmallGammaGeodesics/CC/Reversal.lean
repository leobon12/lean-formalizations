import SmallGammaGeodesics.CC.ReversalLength
import SmallGammaGeodesics.CC.Coupling

/-!
# One-sided ⇒ two-sided conformal covariance by reversing the coupling (track CC, packet CC11, T1)

Source: `planning/audits/CC0-conformal-covariance-plan.md`, Details (a) **D16** (reversal) and
**D1.4** (coupling reversal), for Gwynne–Miller arXiv:1905.00384 ([3]), last paragraph of the proof
of Thm 1.3, with the sign erratum ER3 of CC0 §2.2 (`D_{h_U} = e^{−ξ g} D_{h|U}`, not `e^{ξ g}`).

**T1** `reversal_holds : IsStrongLQGMetric γ D → Reversal γ D`, i.e. `ConfCovLE γ D → ConfCov γ D`.

Let `IsConfNbhd ϕ W V`, `U = ϕ '' V`, `ψ = invFunOn ϕ W`, and let `(h, h̄, f)` be a coupling for
`(ϕ, W, V)`. The inequality `D^ϕ ≤ D_h(·,·;V)` is `ConfCovLE` for `ϕ`. For the converse:

1. CC1's `exists_reverse_coupling_measurable` gives a measurable `F` with `F f = −f ∘ ϕ` on `V` such
   that `(h̄, h, F f)` is a coupling for `(ψ, ϕ '' W, U)`; `IsConfNbhd ψ (ϕ '' W) U` is
   `IsConfNbhd.inv`, and `ψ '' U = V` is `IsConfNbhd.image_inv_image`.
2. `ConfCovLE` for `ψ` and this coupling gives a.s.
   `D_{h + F f}(ψ u, ψ v; V) ≤ D_{h̄}(u, v; U)` for `u, v ∈ U`.
3. Weyl scaling (Axiom III) for the GFF-plus-continuous fields `h + F f` and `h̄`: a.s.
   `D_h = e^{ξ (−F f)}·D_{h + F f}` and `D_{h̄ + f} = e^{ξ f}·D_{h̄}`, and `−F f = f ∘ ϕ` on `V`.
4. The deterministic step `internal_le_of_reverse` (`CC/ReversalLength.lean`: Weyl scaling by
   `e^{ξ f}` preserves the domination, because lengths compare) gives
   `D_h(z, w; V) ≤ D_{h̄ + f}(ϕ z, ϕ w; U) = D^ϕ(z, w)` for `z, w ∈ V`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace SmallGammaGeodesics.CC

open LQGMetric

/-- `(x + F) + (−F) = x`. -/
theorem addFun_add_neg_cancel_right (x : DistC) (F : C(ℂ, ℝ)) : addFun (addFun x F) (-F) = x := by
  refine DFunLike.ext _ _ fun φ => ?_
  show (x φ + ofCont F φ) + ofCont (-F) φ = x φ
  rw [ofCont_apply, ofCont_apply]
  have e : (fun y => φ y * (-F) y) = fun y => -(φ y * F y) := by
    funext y
    simp only [ContinuousMap.neg_apply, mul_neg]
  rw [e, integral_neg]
  ring

/-- **The reversed one-sided inequality** (CC0 D16): if `D` is a strong γ-LQG metric satisfying
the one-sided conformal covariance `ConfCovLE γ D`, then for every coupling `(h, h̄, f)` for
`(ϕ, W, V)`, a.s. `D_h(z, w; V) ≤ D^ϕ(z, w)` for all `z, w ∈ V`. -/
theorem ae_internal_le_confMetric {γ : ℝ} {D : DistC → ContMetric} (hD : IsStrongLQGMetric γ D)
    (hLE : ConfCovLE γ D) {ϕ : ℂ → ℂ} {W V : Set ℂ} (hϕ : IsConfNbhd ϕ W V)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {h hbar : Ω → DistC} {f : Ω → C(ℂ, ℝ)} (hh : IsWholePlaneGFF h P)
    (hhb : IsWholePlaneGFF hbar P) (hf : Measurable f)
    (hc : ∀ᵐ ω ∂P, IsConfCoupling γ ϕ W V (h ω) (hbar ω) (f ω)) :
    ∀ᵐ ω ∂P, ∀ z ∈ V, ∀ w ∈ V,
      (D (h ω)).internal V z w ≤ confMetric D ϕ V (hbar ω) (f ω) z w := by
  -- the inverse map and the reversed coupling (D1.4)
  set ψ : ℂ → ℂ := Function.invFunOn ϕ W with hψdef
  have hψ : ∀ z ∈ W, ψ (ϕ z) = z := fun z hz => hϕ.invFunOn_apply hz
  obtain ⟨F, hFm, hF, hFc⟩ := exists_reverse_coupling_measurable (γ := γ) hϕ
  have hψnb : IsConfNbhd ψ (ϕ '' W) (ϕ '' V) := hϕ.inv hψ
  have hψV : ψ '' (ϕ '' V) = V := hϕ.image_inv_image hψ
  have hFf : Measurable fun ω => F (f ω) := hFm.comp hf
  have hc' : ∀ᵐ ω ∂P, IsConfCoupling γ ψ (ϕ '' W) (ϕ '' V) (hbar ω) (h ω) (F (f ω)) :=
    hc.mono fun ω hω => hFc ψ hψ (h ω) (hbar ω) (f ω) hω
  -- `ConfCovLE` for `ψ` and the reversed coupling
  have hrev := hLE ψ (ϕ '' W) (ϕ '' V) hψnb P hbar h (fun ω => F (f ω)) hhb hh hFf hc'
  -- Weyl scaling for `h + F f` and for `h̄`
  have hW1 := hD.weyl P (fun ω => addFun (h ω) (F (f ω))) (isGFFPlusCont_addFun_of_wp hh hFf)
  have hW2 := hD.weyl P hbar (isGFFPlusCont_of_wp hhb)
  filter_upwards [hrev, hW1, hW2] with ω hrevω hW1ω hW2ω z hz w hw
  -- `D_h = e^{ξ (−F f)}·D_{h + F f}` and `D_{h̄ + f} = e^{ξ f}·D_{h̄}`
  have hA : ∀ x y : ℂ, ENNReal.ofReal ((D (h ω)).1 (x, y)) =
      weylScale (xiGamma γ) (-F (f ω)) (D (addFun (h ω) (F (f ω)))) x y := by
    intro x y
    rw [hW1ω (-F (f ω)) x y, addFun_add_neg_cancel_right]
  have hB : ∀ x y : ℂ, ENNReal.ofReal ((D (addFun (hbar ω) (f ω))).1 (x, y)) =
      weylScale (xiGamma γ) (f ω) (D (hbar ω)) x y := fun x y => (hW2ω (f ω) x y).symm
  -- `−F f = f ∘ ϕ` on `V`
  have hgf : ∀ x ∈ V, (-F (f ω)) x = f ω (ϕ x) := by
    intro x hx
    rw [ContinuousMap.neg_apply, hF (f ω) x hx, neg_neg]
  -- the reversed inequality, written on `V = ψ '' U`
  have hle : ∀ u ∈ ϕ '' V, ∀ v ∈ ϕ '' V, (D (addFun (h ω) (F (f ω)))).internal V (ψ u) (ψ v) ≤
      (D (hbar ω)).internal (ϕ '' V) u v := by
    intro u hu v hv
    have := hrevω u hu v hv
    rwa [confMetric_def, hψV] at this
  rw [confMetric_def]
  exact internal_le_of_reverse hA hB hϕ hψ hgf hle hz hw

/-- **T1: one-sided ⇒ two-sided conformal covariance** ([3], last paragraph of the proof of
Thm 1.3; CC0 D16). For a strong γ-LQG metric `D`, `ConfCovLE γ D` implies `ConfCov γ D`. -/
theorem reversal_holds {γ : ℝ} {D : DistC → ContMetric} (hD : IsStrongLQGMetric γ D) :
    Reversal γ D := by
  intro hLE ϕ W V hϕ Ω _ P _ h hbar f hh hhb hf hc
  filter_upwards [hLE ϕ W V hϕ P h hbar f hh hhb hf hc,
    ae_internal_le_confMetric hD hLE hϕ P hh hhb hf hc] with ω h1 h2 z hz w hw
  exact le_antisymm (h2 z hz w hw) (h1 z hz w hw)

end SmallGammaGeodesics.CC
