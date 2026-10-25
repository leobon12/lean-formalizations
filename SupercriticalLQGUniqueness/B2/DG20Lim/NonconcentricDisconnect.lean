import LQGMetric.Topo.Disconnect

 


set_option autoImplicit false
noncomputable section

open Set Metric

namespace SupercriticalLQGUniqueness.B2.DG20Lim

 

theorem disconnects_nested_closedBall_compl_ball
    {X : Set ℂ} {ci co : ℂ} {ri ro : ℝ}
    (hnest : closedBall ci ri ⊆ ball co ro)
    (h : LQGMetric.Disconnects X (sphere ci ri) (sphere co ro)) :
    LQGMetric.Disconnects X (closedBall ci ri) (ball co ro)ᶜ := by
  intro x y γ hx hy
  let fout : ℝ → ℝ := fun t => dist (γ.extend t) co
  have hfout : Continuous fout := γ.continuous_extend.dist continuous_const
  have hf0 : fout 0 ≤ ro := by simpa [fout] using (mem_ball.mp (hnest hx)).le
  have hf1 : ro ≤ fout 1 := by simpa [fout, not_lt] using hy
  obtain ⟨tout, htout, hftout⟩ :
      ∃ t ∈ Icc (0 : ℝ) 1, fout t = ro :=
    intermediate_value_Icc zero_le_one hfout.continuousOn ⟨hf0, hf1⟩
  let fin : ℝ → ℝ := fun t => dist (γ.extend t) ci
  have hfin : Continuous fin := γ.continuous_extend.dist continuous_const
  have hfi0 : fin 0 ≤ ri := by simpa [fin] using hx
  have hfit : ri ≤ fin tout := by
    by_contra hnot
    have hin : γ.extend tout ∈ closedBall ci ri :=
      mem_closedBall.mpr (le_of_not_ge hnot)
    have hout : γ.extend tout ∈ ball co ro := hnest hin
    have hlt : fout tout < ro := mem_ball.mp hout
    exact (ne_of_lt hlt) hftout
  obtain ⟨tin, htin, hftin⟩ :
      ∃ t ∈ Icc (0 : ℝ) tout, fin t = ri :=
    intermediate_value_Icc htout.1 hfin.continuousOn ⟨hfi0, hfit⟩
  obtain ⟨w, hw, hwX⟩ := h _ _ (γ.truncateOfLE htin.2)
    (mem_sphere.mpr hftin) (mem_sphere.mpr hftout)
  refine ⟨w, ?_, hwX⟩
  have hsub : range (γ.truncateOfLE htin.2) ⊆ range γ := by
    intro u ⟨s, hs⟩
    exact γ.truncate_range ⟨s, by rw [← hs]; rfl⟩
  exact hsub hw

end SupercriticalLQGUniqueness.B2.DG20Lim
