import SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionDyadic.DyadicComponents




 





set_option autoImplicit false
noncomputable section

open Set Metric
open Filter

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionMoments

theorem bounded_component_subset_ball_of_compact_at
    {K : Set ℂ} {x z : ℂ} {M : ℝ}
    (hK : IsCompact K) (hKM : K ⊆ closedBall z M) (hM : 0 ≤ M)
    (hV : Bornology.IsBounded (connectedComponentIn Kᶜ x)) :
    connectedComponentIn Kᶜ x ⊆ ball z M := by
  have hclosed : connectedComponentIn Kᶜ x ⊆ closedBall z M := by
    intro y hy
    by_contra hyM
    have hyU : y ∉ closedBall z M := hyM
    have hunb : ¬ Bornology.IsBounded
        (connectedComponentIn (closedBall z M)ᶜ y) :=
      LQGMetric.not_isBounded_connectedComponentIn_compl_of_convex
        (convex_closedBall z M) (mem_closedBall_self hM) hyU
    have hsub : connectedComponentIn (closedBall z M)ᶜ y ⊆
        connectedComponentIn Kᶜ x := by
      have hmono := connectedComponentIn_mono y (compl_subset_compl.mpr hKM)
      rw [← connectedComponentIn_eq hy] at hmono
      exact hmono
    exact hunb (hV.subset hsub)
  have hVo : IsOpen (connectedComponentIn Kᶜ x) :=
    hK.isClosed.isOpen_compl.connectedComponentIn
  intro y hy
  have hyi : y ∈ interior (closedBall z M) :=
    (interior_maximal hclosed hVo) hy
  simpa only [interior_closedBall'] using hyi

 

theorem annular_component_strict_outer
    {K : Set ℂ} {z : ℂ} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hK : IsCompact K)
    (hann : K ⊆ {y | r < dist y z ∧ dist y z < R})
    (hsep : LQGMetric.Disconnects K (sphere z r) (sphere z R)) :
    ∃ M : ℝ, 0 < M ∧ M < R ∧
      connectedComponentIn Kᶜ z ⊆ ball z M := by
  have hKR : K ⊆ ball z R := fun y hy => (hann hy).2
  obtain ⟨M, ⟨hMpos, hMlt⟩, hKM⟩ :=
    exists_pos_lt_subset_ball (hr.trans hrR) hK.isClosed hKR
  have hV := Toolkit.PlanarSeparation.annular_component_isBounded hr hrR hK hann hsep
  exact ⟨M, hMpos, hMlt,
    bounded_component_subset_ball_of_compact_at hK
      (hKM.trans ball_subset_closedBall) hMpos.le hV⟩

 

theorem eventually_not_mem_annular_component
    {K : Set ℂ} {z e : ℂ} {r R : ℝ} {u : ℕ → ℂ}
    (hr : 0 < r) (hrR : r < R) (hK : IsCompact K)
    (hann : K ⊆ {y | r < dist y z ∧ dist y z < R})
    (hsep : LQGMetric.Disconnects K (sphere z r) (sphere z R))
    (he : R ≤ dist e z) (hu : Filter.Tendsto u Filter.atTop (nhds e)) :
    ∀ᶠ n in Filter.atTop, u n ∉ connectedComponentIn Kᶜ z := by
  obtain ⟨M, _, hMlt, hV⟩ :=
    annular_component_strict_outer hr hrR hK hann hsep
  have heM : e ∈ (closedBall z M)ᶜ := by
    simp only [mem_compl_iff, mem_closedBall, not_le]
    simpa only [dist_comm] using hMlt.trans_le he
  filter_upwards [hu.eventually ((isOpen_compl_iff.mpr isClosed_closedBall).mem_nhds heM)] with n hn hv
  exact hn (ball_subset_closedBall (hV hv))

 

theorem selected_index_tendsto_atTop
    (V : ℕ × Bool → Set ℂ) (u : ℕ → ℂ) (i : ℕ → ℕ × Bool)
    (hsel : ∀ n, u n ∈ V (i n))
    (havoid : ∀ k b, ∀ᶠ n in atTop, u n ∉ V (k, b)) :
    Tendsto (fun n => (i n).1) atTop atTop := by
  apply Filter.tendsto_atTop.mpr
  intro N
  induction N with
  | zero => exact Eventually.of_forall (fun _ => Nat.zero_le _)
  | succ N ih =>
      filter_upwards [ih, havoid N false, havoid N true] with n hn hfalse htrue
      by_contra hnot
      have heq : (i n).1 = N := by omega
      rcases hpair : i n with ⟨k, b⟩
      have hk : k = N := by simpa only [hpair] using heq
      subst k
      cases b with
      | false => exact hfalse (by simpa only [hpair] using hsel n)
      | true => exact htrue (by simpa only [hpair] using hsel n)

end SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionMoments
