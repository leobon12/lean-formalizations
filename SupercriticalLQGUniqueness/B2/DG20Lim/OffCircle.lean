import SupercriticalLQGUniqueness.B2.DG20Lim.AroundLimit
import Mathlib.Analysis.Normed.Module.Connected

 





set_option autoImplicit false
noncomputable section

open Set Metric Filter Topology

namespace SupercriticalLQGUniqueness.B2.DG20Lim

 
def RatCircle.DisconnectsPoint (O : RatCircle) (z : ℂ) (P : RatCircle) : Prop :=
  z ∉ O.toSet ∧ Disconnects O.toSet {z} P.toSet

theorem RatCircle.disconnectsPoint_disconnects {O P : RatCircle} {z : ℂ}
    (h : O.DisconnectsPoint z P) : Disconnects O.toSet {z} P.toSet :=
  h.2

 

theorem disconnects_of_preconnected_neighborhood
    {K E C T : Set ℂ} {z : ℂ}
    (h : Disconnects K {z} E) (hC : IsPreconnected C)
    (hzC : z ∈ C) (hCK : C ⊆ Kᶜ) (hTC : T ⊆ C) :
    Disconnects K T E := by
  intro ⟨S, hS, hSK, hST, hSE⟩
  obtain ⟨p, hpS, hpT⟩ := hST
  apply h
  refine ⟨S ∪ C, hS.union p hpS (hTC hpT) hC, ?_, ?_, ?_⟩
  · exact union_subset hSK hCK
  · exact ⟨z, Or.inr hzC, mem_singleton z⟩
  · obtain ⟨q, hqS, hqE⟩ := hSE
    exact ⟨q, Or.inl hqS, hqE⟩

 

theorem RatCircle.eventually_closedDisk_subset_open {z : ℂ} {C : Set ℂ}
    (hC : IsOpen C) (hzC : z ∈ C) (O : ℕ → RatCircle)
    (hO : ∀ᶠ n in atTop, (O n).Surrounds z)
    (hr : Tendsto (fun n => ((O n).radius : ℝ)) atTop (nhds 0)) :
    ∀ᶠ n in atTop, (O n).closedDisk ⊆ C := by
  obtain ⟨ε, hε, hεC⟩ := Metric.isOpen_iff.mp hC z hzC
  have he := (tendsto_order.1 hr).2 (ε / 2) (half_pos hε)
  filter_upwards [hO, he] with n hn hsmall
  intro u hu
  apply hεC
  apply mem_ball.mpr
  have h₁ : dist u (O n).center ≤ ((O n).radius : ℝ) := mem_closedBall.mp hu
  have h₂ : dist (O n).center z < ((O n).radius : ℝ) := by
    simpa only [dist_comm] using (mem_ball.mp hn.2)
  have htri : dist u z ≤ dist u (O n).center + dist (O n).center z :=
    dist_triangle _ _ _
  linarith

 

theorem RatCircle.eventually_disconnects_shrinking
    {K P : RatCircle} {z : ℂ} (h : K.DisconnectsPoint z P)
    (O : ℕ → RatCircle) (hO : ∀ᶠ n in atTop, (O n).Surrounds z)
    (hr : Tendsto (fun n => ((O n).radius : ℝ)) atTop (nhds 0)) :
    ∀ᶠ n in atTop, Disconnects K.toSet (O n).toSet P.toSet := by
  have hOpen : IsOpen K.toSetᶜ := isClosed_sphere.isOpen_compl
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hOpen z h.1
  have he := RatCircle.eventually_closedDisk_subset_open
    (isOpen_ball : IsOpen (ball z ε)) (mem_ball_self hε) O hO hr
  filter_upwards [he] with n hn
  apply disconnects_of_preconnected_neighborhood h.2
    (isPreconnected_ball : IsPreconnected (ball z ε)) (mem_ball_self hε)
    hball
  exact (O n).toSet_subset_closedDisk.trans hn

 

theorem RatCircle.eventually_disjoint_fixed
    {K : RatCircle} {z : ℂ} (hz : z ∉ K.toSet)
    (O : ℕ → RatCircle) (hO : ∀ᶠ n in atTop, (O n).Surrounds z)
    (hr : Tendsto (fun n => ((O n).radius : ℝ)) atTop (nhds 0)) :
    ∀ᶠ n in atTop, Disjoint (O n).toSet K.toSet := by
  have he := RatCircle.eventually_closedDisk_subset_open
    isClosed_sphere.isOpen_compl hz O hO hr
  filter_upwards [he] with n hn
  apply disjoint_left.mpr
  intro u huO huK
  exact hn ((O n).toSet_subset_closedDisk huO) huK

end SupercriticalLQGUniqueness.B2.DG20Lim
