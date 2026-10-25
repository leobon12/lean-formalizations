import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCNoSideSuffixDetourTrace
import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCNoRightSuffix
import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCSeparatorSquare

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Metric
namespace SupercriticalLQGUniqueness.B2.DG20Conc
open LQGMetric LQGMetric.DDDF

 


theorem laneC_no_right_source_separator_arc
    (D : ContMetric) {c : ℂ} {r : ℝ}
    (hr0 : 0 < r) (hrSmall : 2 * r < 1 / 8)
    (hclo : 2 * r ≤ c.im) (hchi : c.im + 2 * r ≤ 1)
    (hcle : 2 * r ≤ c.re)
    {ρ γ : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hρ : ContinuousOn ρ (Icc a b))
    (hρA : ∀ s ∈ Icc a b,
      r < dist (ρ s) c ∧ dist (ρ s) c < 2 * r)
    (hsep : LQGMetric.Disconnects (ρ '' Icc a b)
      (sphere c r) (sphere c (2 * r)))
    (hno : ¬((ρ '' Icc a b) ∩ (rectAB 1 1).side₂).Nonempty)
    (hγ : ContinuousOn γ (Icc (0 : ℝ) 1))
    (hγsq : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ (rectAB 1 1).toSet)
    (hγside : γ 1 ∈ (rectAB 1 1).side₂)
    {m : ℝ} (hm : m ∈ Icc (0 : ℝ) 1)
    (hstart : 2 * r ≤ dist (γ 0) c)
    (hmid : dist (γ m) c ≤ r) :
    ∃ (α : ℝ → ℂ) (t₀ t₁ : ℝ),
      t₀ ∈ Icc (0 : ℝ) 1 ∧ t₁ ∈ Icc (0 : ℝ) 1 ∧ t₀ ≤ t₁ ∧
      ContinuousOn α (Icc (0 : ℝ) 1) ∧
      (∀ s ∈ Icc (0 : ℝ) 1,
        r < dist (α s) c ∧ dist (α s) c < 2 * r ∧
          α s ∈ (rectAB 1 1).toSet) ∧
      γ t₀ = α 0 ∧ γ t₁ = α 1 ∧
      (∀ t ∈ Icc (0 : ℝ) t₀, r ≤ dist (γ t) c) ∧
      (∀ t ∈ Icc t₁ (1 : ℝ), r ≤ dist (γ t) c) ∧
      D.len α 0 1 ≤ D.len ρ a b := by
  have hhit : ((ρ '' Icc a b) ∩ (rectAB 1 1).toSet).Nonempty :=
    laneC_separator_of_visited_block_intersects_square hr0.le hrSmall
      hsep (hγsq m hm) hmid
  have hρsq : ∀ s ∈ Icc a b, ρ s ∈ (rectAB 1 1).toSet :=
    laneC_trace_square_of_no_right_side hab hρ
      (fun s hs => laneC_ball_horizontal_strip (hρA s hs).2 hclo hchi)
      (fun s hs => laneC_ball_re_nonneg (hρA s hs).2 hcle)
      hhit hno
  obtain ⟨y, hyFar, p, hp⟩ :=
    laneC_right_side_outer_path c (γ 1) hrSmall hγside
  have hsep' : LQGMetric.Disconnects (ρ '' Icc a b)
      (closedBall c r) (ball c (2 * r))ᶜ :=
    LQGMetric.Disconnects.closedBall_compl_ball (by linarith) hsep
  obtain ⟨α, t₀, t₁, ht₀, ht₁, htord, hα, hαcar,
      hmeet₀, hmeet₁, hbefore, hafter, hlen⟩ :=
    laneC_no_side_suffix_continuous_separator_arc D hab hρ hsep'
      (Fr := {z | r ≤ dist z c})
      (U := {z | r < dist z c ∧ dist z c < 2 * r} ∩ (rectAB 1 1).toSet)
      (fun s hs => (hρA s hs).1.le)
      (fun s hs => ⟨hρA s hs, hρsq s hs⟩)
      (Set.not_nonempty_iff_eq_empty.mp hno)
      (by change ¬dist y c < 2 * r; exact not_lt.mpr hyFar.le)
      p hp hγ hm
      (by change ¬dist (γ 0) c < 2 * r; exact not_lt.mpr hstart)
      (by simpa only [mem_closedBall] using hmid)
      (by intro t ht hnot
          change ¬r ≤ dist (γ t) c at hnot
          exact le_of_lt (not_le.mp hnot))
  refine ⟨α, t₀, t₁, ht₀, ht₁, htord, hα, ?_,
    hmeet₀, hmeet₁, hbefore, hafter, hlen⟩
  intro s hs
  exact ⟨(hαcar s hs).2.1.1, (hαcar s hs).2.1.2,
    (hαcar s hs).2.2⟩

end SupercriticalLQGUniqueness.B2.DG20Conc
