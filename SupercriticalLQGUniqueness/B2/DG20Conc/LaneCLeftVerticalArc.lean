import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCNoLeftSourceArc
import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCOneSideCarrierDetour

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Metric
namespace SupercriticalLQGUniqueness.B2.DG20Conc
open LQGMetric LQGMetric.DDDF

 


theorem laneC_left_vertical_source_separator_arc
    (D : ContMetric) {c : ℂ} {r : ℝ}
    (hr0 : 0 < r) (hrSmall : 2 * r < 1 / 8)
    (hclo : 2 * r ≤ c.im) (hchi : c.im + 2 * r ≤ 1)
    (hcri : c.re + 2 * r ≤ 1)
    {ρ γ : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hρ : ContinuousOn ρ (Icc a b))
    (hρA : ∀ s ∈ Icc a b,
      r < dist (ρ s) c ∧ dist (ρ s) c < 2 * r)
    (hsep : LQGMetric.Disconnects (ρ '' Icc a b)
      (sphere c r) (sphere c (2 * r)))
    (hγ : ContinuousOn γ (Icc (0 : ℝ) 1))
    (hγsq : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ (rectAB 1 1).toSet)
    (hγside : γ 0 ∈ (rectAB 1 1).side₁)
    {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1)
    (hmid : dist (γ m) c ≤ r)
    (hend : 2 * r ≤ dist (γ 1) c) :
    ∃ (α : ℝ → ℂ) (t₀ t₁ : ℝ),
      t₀ ∈ Icc (0 : ℝ) 1 ∧ t₁ ∈ Icc (0 : ℝ) 1 ∧ t₀ ≤ t₁ ∧
      ContinuousOn α (Icc (0 : ℝ) 1) ∧
      (∀ s ∈ Icc (0 : ℝ) 1,
        r < dist (α s) c ∧ dist (α s) c < 2 * r ∧
          α s ∈ (rectAB 1 1).toSet) ∧
      ((γ t₀ = α 0 ∧ ∀ t ∈ Icc (0 : ℝ) t₀,
          r ≤ dist (γ t) c) ∨
        (t₀ = 0 ∧ α 0 ∈ (rectAB 1 1).side₁)) ∧
      γ t₁ = α 1 ∧
      (∀ t ∈ Icc t₁ (1 : ℝ), r ≤ dist (γ t) c) ∧
      D.len α 0 1 ≤ D.len ρ a b := by
  let X : Set ℂ := ρ '' Icc a b
  by_cases hside : (X ∩ (rectAB 1 1).side₁).Nonempty
  · have hsep' : LQGMetric.Disconnects X
        (closedBall c r) (ball c (2 * r))ᶜ :=
      LQGMetric.Disconnects.closedBall_compl_ball (by linarith) hsep
    obtain ⟨α, t₁, ht₁, hα, hαcar, hα0, hα1, hafter, hlen⟩ :=
      laneC_left_one_side_detour_in_image D hab hρ hsep'
        (Fr := {z | r ≤ dist z c})
        (fun s hs => (hρA s hs).1.le)
        (fun s hs => (hρA s hs).2)
        hside hclo hchi hcri hγ hγsq hm
        (by simpa only [mem_closedBall] using hmid)
        (by change ¬dist (γ 1) c < 2 * r; exact not_lt.mpr hend)
        (by intro t ht hnot
            change ¬r ≤ dist (γ t) c at hnot
            exact le_of_lt (not_le.mp hnot))
    refine ⟨α, 0, t₁, (by simp),
      ⟨hm.1.trans ht₁.1, ht₁.2⟩, hm.1.trans ht₁.1, hα, ?_,
      Or.inr ⟨rfl, hα0⟩, hα1, hafter, hlen⟩
    intro s hs
    obtain ⟨u, hu, hueq⟩ := (hαcar s hs).2.2
    have hA : r < dist (α s) c ∧ dist (α s) c < 2 * r := by
      rw [← hueq]
      exact hρA u hu
    exact ⟨hA.1, hA.2, (hαcar s hs).2.1⟩
  · obtain ⟨α, t₀, t₁, ht₀, ht₁, htord, hα, hαcar,
        hmeet₀, hmeet₁, hbefore, hafter, hlen⟩ :=
      laneC_no_left_source_separator_arc D hr0 hrSmall
        hclo hchi hcri hab hρ hρA hsep hside
        hγ hγsq hγside hm hmid hend
    exact ⟨α, t₀, t₁, ht₀, ht₁, htord, hα, hαcar,
      Or.inl ⟨hmeet₀, hbefore⟩, hmeet₁, hafter, hlen⟩

end SupercriticalLQGUniqueness.B2.DG20Conc
