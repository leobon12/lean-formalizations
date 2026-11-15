/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCHG2aParts
import InteractingSLE.Spec.Supplement.RLCIOrder
import InteractingSLE.Spec.Exist.DetField
import InteractingSLE.Spec.Supplement.LPTrace

/-!
# Theorem 1.3 supplies the G2a parts

Theorem 1.3 gives transience for an infinite-lifetime integrated evolution. An angle flow line already
contains such an evolution and an a.e. generating trace, so uniqueness of generating traces transfers
that transience to the flow line. These parts, together with the remaining order inputs, give G2a.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace RLC

/-- Transfer Theorem 1.3's transience to an angle flow line with infinite lifetime. -/
theorem ae_tendsto_norm_of_thm13
    (h13 : Exist.Theorem13Statement.{u}) {κ : ℝ} (hκ : 0 < κ)
    {b : ℝ → ℝ} {J : Finset ℝ} {x θ : ℝ} {S : Type u}
    [MeasurableSpace S] {Q : Measure S} [IsProbabilityMeasure Q]
    {h : S → LQGMetric.DistOn upperHalfPlaneOpens} {α : S → ℝ≥0 → ℂ} {ζ : S → ℝ≥0∞}
    (hfl : IsFlowLine κ b J x θ Q h α ζ) (hlife : ∀ᵐ ω ∂Q, ζ ω = ⊤) :
    ∀ᵐ ω ∂Q, Tendsto (fun t => ‖α ω t‖) atTop atTop := by
  rcases hfl with ⟨h', 𝓕, W, VL, VR, B, _htranslate, hopt, hgen⟩
  have hevol := hopt.1
  have h13ae := h13 hκ (Theorem15.isOrderedForceWord_flowLine b J x) hevol
  filter_upwards [h13ae, hgen, hevol.2.2.2.2, hlife] with ω h13ω hgenω hpath hζ
  rcases h13ω.2 with ⟨γ, hγ, hγtrans⟩
  have hγeq : ∀ t : ℝ≥0, γ t = α ω t - (x : ℂ) := by
    intro t
    exact IsGeneratingTrace.eq_of_le hγ hgenω hpath.2.2.2.1 hpath.1 (by rw [hζ]; exact le_top)
  have hshift : Tendsto (fun t : ℝ≥0 => ‖α ω t - (x : ℂ)‖) atTop atTop := by
    simpa only [← hγeq] using hγtrans hζ
  apply Filter.tendsto_atTop.2
  intro R
  have hlarge := (Filter.tendsto_atTop.1 hshift) (R + ‖(x : ℂ)‖)
  filter_upwards [hlarge] with t ht
  have htriangle : ‖α ω t - (x : ℂ)‖ ≤ ‖α ω t‖ + ‖(x : ℂ)‖ := norm_sub_le _ _
  linarith [norm_nonneg (x : ℂ)]

/-- Theorem 1.3 gives the transience component of the exact G2a parts statement. -/
theorem g2aTransienceStatement_of_thm13 (h13 : Exist.Theorem13Statement.{u}) :
    G2aTransienceStatement.{u} := by
  intro κ hκ hκ4 θ₁ θ₂ w₂ w₁ hθ hw m Jm hJm hpc hnear₂ hnear₁ hmid
    S _ Q _ h hĤ α₁ α₂ ζ₁ ζ₂ hη₁ hη₂
  have hlife := ae_g2a_infiniteLifetimes hκ hκ4 hθ hw hpc hJm hnear₂ hnear₁ hmid
    Q h α₁ α₂ ζ₁ ζ₂ hη₁ hη₂
  have hlife₁ : ∀ᵐ ω ∂Q, ζ₁ ω = ⊤ := by
    filter_upwards [hlife] with ω hζ
    exact hζ.1
  have hlife₂ : ∀ᵐ ω ∂Q, ζ₂ ω = ⊤ := by
    filter_upwards [hlife] with ω hζ
    exact hζ.2
  have htrans₁ := ae_tendsto_norm_of_thm13 h13 hκ hη₁ hlife₁
  have htrans₂ := ae_tendsto_norm_of_thm13 h13 hκ hη₂ hlife₂
  filter_upwards [htrans₁, htrans₂] with ω hω₁ hω₂
  exact ⟨hω₁, hω₂⟩

/-- Prove the exact parts statement owned by RLCIOrder from Theorem 1.3. -/
theorem g2aPartsStatement_of_thm13 (h13 : Exist.Theorem13Statement.{u}) :
    G2aPartsStatement.{u} :=
  g2aPartsStatement_of_transience (g2aTransienceStatement_of_thm13 h13)

/-- Theorem 1.3 supplies G2a's parts; its order conclusion follows from Lemmas 7.5 and 7.7,
the first-contact word kernel, and the half-plane Proposition 5.5. -/
theorem g2aReferenceStatement_of_thm13
    (h13 : Exist.Theorem13Statement.{u})
    (hL75 : Theorem15.Lemma75Statement.{u})
    (hL77 : Supp10.Lemma77Statement.{u})
    (hW : Restart.FirstContactWordKernelStatement.{u})
    (h55 : Sec7.Lemma71H.Prop55HalfPlaneStatement.{0}) :
    G2aReferenceStatement.{u} := by
  let hP : G2aPartsStatement.{u} := g2aPartsStatement_of_thm13 h13
  exact g2aReferenceStatement_of_parts_order hP
    (g2aOrderStatement_of_parts hL75 hL77 hW h55 hP)

end RLC

end InteractingSLE
