/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6TrGrowth

/-!
# A fixed compact interval of same-time collars survives inner growth

PROVE-R6-TWO, Astra §5. The common-time face is built first. Only the
inner hull grows. Neither a physical neighbourhood of the force landing
nor a non-corner hypothesis occurs in this argument.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H Hbar fwdMapInv fwdHull)

namespace InteractingSLE.Sec7.R6Tr

/-- A compact family of old collars, whose physical landings avoid the
old tip, has one common interval of later real times. For each boundary
point the collar radius itself is also fixed throughout that interval. -/
theorem compact_collars_persist {V : Set ℂ} {ψ E₀ EO : ℂ → ℂ} {O : Chart}
    (hO : O.IsConformal) (hEO : EqOn EO O.2.1 H) (hEOc : ContinuousOn EO Hbar)
    (hψ : SupercriticalConformalCovariance.IsConformalBijection ψ V H)
    (hE₀ : EqOn E₀ (Function.invFunOn ψ V) H)
    {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {q₀ : ℝ} (hq₀ : 0 ≤ q₀)
    (hEc : ContinuousOn (fun z => E₀ (extendFrom H (fwdMapInv W q₀) z)) Hbar)
    {p : ℂ} (htip : E₀ (extendFrom H (fwdMapInv W q₀) 0) = p)
    (hIncl : V ∩ ψ ⁻¹' (H \ fwdHull W q₀) ⊆ O.dom)
    {K : Set ℝ} (hK : IsCompact K) (havoid : ∀ x ∈ K, EO (x : ℂ) ≠ p)
    (hcollars : ∀ x ∈ K, ∃ r > 0,
      H ∩ ball (x : ℂ) r ⊆ O.1 '' (V ∩ ψ ⁻¹' (H \ fwdHull W q₀))) :
    ∃ θ > 0, ∀ x ∈ K, ∃ r > 0, ∀ q : ℝ, q₀ ≤ q → q < q₀ + θ →
      H ∩ ball (x : ℂ) r ⊆ O.1 '' (V ∩ ψ ⁻¹' (H \ fwdHull W q)) := by
  have hEk : ContinuousOn (fun x : ℝ => EO (x : ℂ)) K :=
    hEOc.comp Complex.continuous_ofReal.continuousOn (fun x _ => R6Fc.real_mem_Hbar x)
  have hclosed : IsClosed ((fun x : ℝ => EO (x : ℂ)) '' K) :=
    (hK.image_of_continuousOn hEk).isClosed
  have hp : p ∉ (fun x : ℝ => EO (x : ℂ)) '' K := by
    rintro ⟨x, hx, hxp⟩
    exact havoid x hx hxp
  obtain ⟨e, he, hsep⟩ := Metric.isOpen_iff.1 hclosed.isOpen_compl p hp
  obtain ⟨θ, hθ, hfill⟩ := full_increment_localization hψ hE₀ hW hW0 hq₀ hEc htip (half_pos he)
  refine ⟨θ, hθ, fun x hx => ?_⟩
  obtain ⟨r₁, hr₁, hc₁⟩ := hcollars x hx
  obtain ⟨r₂, hr₂, hc₂⟩ := Metric.continuousWithinAt_iff.1
    (hEOc _ (R6Fc.real_mem_Hbar x)) (e / 2) (half_pos he)
  refine ⟨min r₁ r₂, lt_min hr₁ hr₂, fun q hq hqθ z hz => ?_⟩
  obtain ⟨w, hw, hwz⟩ := hc₁ ⟨hz.1, ball_subset_ball (min_le_left _ _) hz.2⟩
  have hEz : EO z = w := by rw [hEO hz.1, ← hwz, hO.inv_fwd (hIncl hw)]
  have hnear : dist w (EO (x : ℂ)) < e / 2 := by
    rw [← hEz]
    exact hc₂ (QuantumZipper.H_subset_Hbar hz.1)
      ((mem_ball.1 hz.2).trans_le (min_le_right _ _))
  have hwaway : w ∉ ball p (e / 2) := by
    intro hwb
    have hxb : EO (x : ℂ) ∈ ball p e := by
      rw [mem_ball]
      have ht := dist_triangle (EO (x : ℂ)) w p
      rw [dist_comm (EO (x : ℂ)) w] at ht
      linarith [mem_ball.1 hwb]
    exact hsep hxb ⟨x, hx, rfl⟩
  have hwnew : w ∈ V ∩ ψ ⁻¹' (H \ fwdHull W q) := by
    by_contra hnot
    exact hwaway (hfill q hq hqθ ⟨hw, hnot⟩)
  exact ⟨w, hwnew, hwz⟩

/-- The compact set may be any closed subinterval of the common-time
shared interval avoiding the driver, when the current tip fibre is
singleton. No fibre condition is imposed at its other landings. -/
theorem compact_collars_persist_of_singleton {V : Set ℂ} {ψ E₀ EO : ℂ → ℂ} {O : Chart}
    (hO : O.IsConformal) (hEO : EqOn EO O.2.1 H) (hEOc : ContinuousOn EO Hbar)
    (hψ : SupercriticalConformalCovariance.IsConformalBijection ψ V H)
    (hE₀ : EqOn E₀ (Function.invFunOn ψ V) H)
    {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {q₀ : ℝ} (hq₀ : 0 ≤ q₀)
    (hEc : ContinuousOn (fun z => E₀ (extendFrom H (fwdMapInv W q₀) z)) Hbar)
    {p : ℂ} (htip : E₀ (extendFrom H (fwdMapInv W q₀) 0) = p)
    (hfibre : ∀ x : ℝ, EO (x : ℂ) = p → x = 0)
    (hIncl : V ∩ ψ ⁻¹' (H \ fwdHull W q₀) ⊆ O.dom)
    {K : Set ℝ} (hK : IsCompact K) (hzero : 0 ∉ K)
    (hcollars : ∀ x ∈ K, ∃ r > 0,
      H ∩ ball (x : ℂ) r ⊆ O.1 '' (V ∩ ψ ⁻¹' (H \ fwdHull W q₀))) :
    ∃ θ > 0, ∀ x ∈ K, ∃ r > 0, ∀ q : ℝ, q₀ ≤ q → q < q₀ + θ →
      H ∩ ball (x : ℂ) r ⊆ O.1 '' (V ∩ ψ ⁻¹' (H \ fwdHull W q)) := by
  exact compact_collars_persist hO hEO hEOc hψ hE₀ hW hW0 hq₀ hEc htip hIncl hK
    (fun x hx heq => hzero (hfibre x heq ▸ hx)) hcollars

end InteractingSLE.Sec7.R6Tr
