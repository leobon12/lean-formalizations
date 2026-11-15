/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3Heights
import InteractingSLE.Spec.Sec7.Aux57

/-!
# Lemma S3: the analytic comparison through the union

Packet PROVE-T14-S3, continuation. Aux. 57 fixes each transition to a common
union chart; Proposition 3.8 compares both single-history means through the
union mean. These adapters keep the geometric transition-gap and marked-mean
hypotheses explicit, without assuming a relative driving law.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H chiC)
open LQGMetric (DistOn TestOn)
open InteractingSLE.Restart

namespace InteractingSLE.Theorem14.SB.S3

/-- Two canonical derivative lifts agree at a common protected approach when
both transitions to the union have an untouched real gap. -/
theorem tendsto_sub_lifts_of_union_gaps {A₁ A₂ B : Set ℂ}
    (hA₁ : IsHPHull A₁) (hA₂ : IsHPHull A₂) (hB : IsHPHull B)
    (h₁B : A₁ ⊆ B) (h₂B : A₂ ⊆ B)
    {g₁ g₂ gB L₁ L₂ LB : ℂ → ℂ}
    (hg₁ : IsMapOut A₁ g₁) (hg₂ : IsMapOut A₂ g₂) (hgB : IsMapOut B gB)
    (hL₁ : IsCanonicalDerivLog A₁ g₁ L₁)
    (hL₂ : IsCanonicalDerivLog A₂ g₂ L₂)
    (hLB : IsCanonicalDerivLog B gB LB)
    {p : ℂ} {x₁ x₂ r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hd₁ : Disjoint (ball (x₁ : ℂ) r₁) (g₁ '' (B \ A₁)))
    (hd₂ : Disjoint (ball (x₂ : ℂ) r₂) (g₂ '' (B \ A₂)))
    (hp₁ : Tendsto g₁ (𝓝[H \ B] p) (𝓝[H] (x₁ : ℂ)))
    (hp₂ : Tendsto g₂ (𝓝[H \ B] p) (𝓝[H] (x₂ : ℂ))) :
    Tendsto (fun z => (L₁ z).im - (L₂ z).im) (𝓝[H \ B] p) (𝓝 0) := by
  have h₁ := Sec7.tendsto_im_sub_canonDerivLog hA₁ hB h₁B hg₁ hgB hL₁ hLB hr₁ hd₁ hp₁
  have h₂ := Sec7.tendsto_im_sub_canonDerivLog hA₂ hB h₂B hg₂ hgB hL₂ hLB hr₂ hd₂ hp₂
  have h := h₂.sub h₁
  simp only [sub_self] at h
  exact h.congr fun z => by ring

/-- The nested union-mean comparison and exact lift comparison give S3's
contradiction. All four harmonic representatives refer to the same union mean. -/
theorem false_of_union_mean_comparison {κ ϑ v : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    {l : List (ℝ × ℝ≥0)} (hθ : ∀ p ∈ l, p.1 < ϑ) (hv : Lh.SideH κ l v)
    {O A₁ A₂ : Set ℂ} (hO : IsOpen O) (hO₁ : O ⊆ H \ A₁) (hO₂ : O ⊆ H \ A₂)
    {G G₁ G₂ : DistOn upperHalfPlaneOpens} {v₁ v₂ ua ub u₀ L₁ L₂ : ℂ → ℝ}
    (hv₁ : InnerProductSpace.HarmonicOnNhd v₁ (H \ A₁))
    (hv₁r : ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₁ →
      G₁ φ = ∫ z, v₁ z * φ z)
    (hv₂ : InnerProductSpace.HarmonicOnNhd v₂ (H \ A₂))
    (hv₂r : ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A₂ →
      G₂ φ = ∫ z, v₂ z * φ z)
    (hua : InnerProductSpace.HarmonicOnNhd ua O)
    (huar : ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ O →
      G φ - G₁ φ = ∫ z, ua z * φ z)
    (hub : InnerProductSpace.HarmonicOnNhd ub O)
    (hubr : ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ O →
      G φ - G₂ φ = ∫ z, ub z * φ z)
    {p : ℂ} (ha : Tendsto ua (𝓝[O] p) (𝓝 0)) (hb : Tendsto ub (𝓝[O] p) (𝓝 0))
    {F : Filter ℂ} [F.NeBot] (hF : F ≤ 𝓝[O] p)
    (hphase : Tendsto (fun z => L₁ z - L₂ z) F (𝓝 0))
    (hold : Tendsto (fun z => v₁ z + u₀ z + chiC κ * L₁ z) F (𝓝 v))
    (hupper : Tendsto (fun z => v₂ z + u₀ z + chiC κ * L₂ z) F
      (𝓝 (-sleLambda κ - ϑ * chiC κ))) : False := by
  have hmean := Sec7.tendsto_sub_of_union_means hO hO₁ hO₂ hv₁ hv₁r hv₂ hv₂r
    hua huar hub hubr ha hb
  exact false_of_side_limits hκ hκ4 hθ hv (hmean.mono_left hF) hphase hold hupper

end InteractingSLE.Theorem14.SB.S3
