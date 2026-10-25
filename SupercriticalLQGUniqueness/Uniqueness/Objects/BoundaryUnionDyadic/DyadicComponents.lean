import SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionDyadic.DyadicGeometry
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.PlanarSeparation.Components




 




set_option autoImplicit false
noncomputable section

open Set Metric

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionDyadic

def dyadicQ (k : ℕ) : ℝ := (1 / 2 : ℝ) ^ (k + 1)

def dyadicCenter (w : ℂ) (i : ℕ × Bool) : ℂ :=
  if i.2 then (1 - dyadicQ i.1) • w else (dyadicQ i.1) • w

def dyadicOuter (w : ℂ) (i : ℕ × Bool) : ℝ := dyadicQ i.1 * ‖w‖

 

theorem dyadic_component_cover (w : ℂ) (hw : w ≠ 0)
    (K : ℕ × Bool → Set ℂ)
    (hcompact : ∀ i, IsCompact (K i))
    (hann : ∀ i, K i ⊆ {z | dyadicOuter w i / 2 <
      dist z (dyadicCenter w i) ∧ dist z (dyadicCenter w i) < dyadicOuter w i})
    (hsep : ∀ i, LQGMetric.Disconnects (K i)
      (sphere (dyadicCenter w i) (dyadicOuter w i / 2))
      (sphere (dyadicCenter w i) (dyadicOuter w i)))
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    ∃ i : ℕ × Bool, t • w ∈
      connectedComponentIn (K i)ᶜ (dyadicCenter w i) := by
  obtain ⟨k, hleft | hright⟩ := dyadic_twoEnd_inner_disk_cover w hw ht
  · let i : ℕ × Bool := (k, false)
    have hq : 0 < dyadicQ k := pow_pos (by norm_num) _
    have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
    have hrad : 0 < dyadicOuter w i / 2 := by
      dsimp [dyadicOuter, dyadicQ, i]
      positivity
    have hrad' : dyadicOuter w i / 2 < dyadicOuter w i := by
      dsimp [dyadicOuter, dyadicQ, i]
      have hp : 0 < (1 / 2 : ℝ) ^ (k + 1) * ‖w‖ := by
        simpa only [dyadicQ] using mul_pos hq hwpos
      linarith only [hp]
    have hinner := (Toolkit.PlanarSeparation.annular_component_bounds hrad hrad'
      (hcompact i) (hann i) (hsep i)).1
    refine ⟨i, hinner ?_⟩
    change t • w ∈ closedBall ((dyadicQ k) • w) (dyadicQ k * ‖w‖ / 2)
    exact ball_subset_closedBall hleft
  · let i : ℕ × Bool := (k, true)
    have hq : 0 < dyadicQ k := pow_pos (by norm_num) _
    have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
    have hrad : 0 < dyadicOuter w i / 2 := by
      dsimp [dyadicOuter, dyadicQ, i]
      positivity
    have hrad' : dyadicOuter w i / 2 < dyadicOuter w i := by
      dsimp [dyadicOuter, dyadicQ, i]
      have hp : 0 < (1 / 2 : ℝ) ^ (k + 1) * ‖w‖ := by
        simpa only [dyadicQ] using mul_pos hq hwpos
      linarith only [hp]
    have hinner := (Toolkit.PlanarSeparation.annular_component_bounds hrad hrad'
      (hcompact i) (hann i) (hsep i)).1
    refine ⟨i, hinner ?_⟩
    change t • w ∈ closedBall ((1 - dyadicQ k) • w) (dyadicQ k * ‖w‖ / 2)
    exact ball_subset_closedBall hright

 
theorem dyadic_finite_component_cover (w : ℂ) (hw : w ≠ 0)
    (K : ℕ × Bool → Set ℂ)
    (hcompact : ∀ i, IsCompact (K i))
    (hann : ∀ i, K i ⊆ {z | dyadicOuter w i / 2 <
      dist z (dyadicCenter w i) ∧ dist z (dyadicCenter w i) < dyadicOuter w i})
    (hsep : ∀ i, LQGMetric.Disconnects (K i)
      (sphere (dyadicCenter w i) (dyadicOuter w i / 2))
      (sphere (dyadicCenter w i) (dyadicOuter w i)))
    {a b : ℝ} (ha : 0 < a) (hb : b < 1) :
    ∃ F : Finset (ℕ × Bool),
      (fun t : ℝ => t • w) '' Icc a b ⊆
        ⋃ i ∈ F, connectedComponentIn (K i)ᶜ (dyadicCenter w i) := by
  let A : Set ℂ := (fun t : ℝ => t • w) '' Icc a b
  have hcont : Continuous (fun t : ℝ => t • w) :=
    continuous_id.smul continuous_const
  have hA : IsCompact A := isCompact_Icc.image hcont
  have hopen (i : ℕ × Bool) :
      IsOpen (connectedComponentIn (K i)ᶜ (dyadicCenter w i)) :=
    (hcompact i).isClosed.isOpen_compl.connectedComponentIn
  have hcover : A ⊆ ⋃ i : ℕ × Bool,
      connectedComponentIn (K i)ᶜ (dyadicCenter w i) := by
    intro z hz
    obtain ⟨t, ht, rfl⟩ := hz
    obtain ⟨i, hi⟩ := dyadic_component_cover w hw K hcompact hann hsep
      ⟨ha.trans_le ht.1, ht.2.trans_lt hb⟩
    exact Set.mem_iUnion_of_mem i hi
  exact hA.elim_finite_subcover _ hopen hcover

end SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionDyadic
