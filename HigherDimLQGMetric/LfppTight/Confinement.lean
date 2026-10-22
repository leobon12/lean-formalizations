import HigherDimLQGMetric.LfppTight.CoupledInternal
import HigherDimLQGMetric.DGZ.Crossing

/-! Confinement of near-minimizing LFPP paths by a sphere crossing gap. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l6a_lfppDistOn_eq_of_crossing {d : ℕ} (ξ : ℝ) (H : Rd d → ℝ)
    (hH : Continuous H) {r R : ℝ} (hrr : r < R)
    {x y : Rd d} (hx : x ∈ ball (0 : Rd d) r) (hy : y ∈ ball (0 : Rd d) r)
    (hcross : HigherDimLFPP.lfppDistOn ξ H univ x y <
      DGZ.lfppSetDist ξ H univ (sphere (0 : Rd d) r) (sphere 0 R)) :
    HigherDimLFPP.lfppDistOn ξ H (ball 0 R) x y =
      HigherDimLFPP.lfppDistOn ξ H univ x y := by
  have hxR : x ∈ ball (0 : Rd d) R :=
    ball_subset_ball hrr.le hx
  have hyR : y ∈ ball (0 : Rd d) R :=
    ball_subset_ball hrr.le hy
  have hj : HigherDimLFPP.PcwJoined (ball (0 : Rd d) R) x y :=
    HigherDimLFPP.PcwJoined.of_convex (convex_ball _ _) hxR hyR
  have hconf : ∀ γ : ℝ → Rd d, ∀ hγ : HigherDimLFPP.IsPcwC1Path γ x y,
      HigherDimLFPP.lfppLength ξ H γ <
        DGZ.lfppSetDist ξ H univ (sphere (0 : Rd d) r) (sphere 0 R) →
      MapsTo γ (Icc 0 1) (ball 0 R) := by
    intro γ hγ hlen t ht
    by_contra hout
    have hxc : γ 0 ∈ closedBall (0 : Rd d) r := by
      rw [hγ.source]
      exact ball_subset_closedBall hx
    have hcrossLen : DGZ.lfppSetDist ξ H univ (sphere (0 : Rd d) r) (sphere 0 R) ≤
        HigherDimLFPP.lfppLength ξ H γ := by
      rw [← DGZ.closedBall_sdiff_ball_eq (0 : Rd d) r,
        ← DGZ.closedBall_sdiff_ball_eq (0 : Rd d) R]
      have h1 := (DGZ.isShellPair_ball (0 : Rd d) hrr).lfppSetDist_le_integral
        (ξ := ξ) (V := univ) hH (subset_univ _) hγ
        (a := 0) (b := t) le_rfl ht.1 ht.2
        (Or.inl ⟨hxc, hout⟩)
      exact h1.trans (DGZ.integral_le_lfppLength hH hγ le_rfl ht.1 ht.2)
    exact (not_lt_of_ge hcrossLen) hlen
  apply le_antisymm
  · apply le_of_forall_gt
    intro b hb
    have hmin : HigherDimLFPP.lfppDistOn ξ H univ x y <
        min b (DGZ.lfppSetDist ξ H univ (sphere (0 : Rd d) r) (sphere 0 R)) :=
      lt_min hb hcross
    obtain ⟨γ, hγ, _, hlen⟩ :=
      HigherDimLFPP.exists_lfppLength_lt (DGZ.pcwJoined_univ x y) hmin
    have hmaps := hconf γ hγ (hlen.trans_le (min_le_right _ _))
    exact (HigherDimLFPP.lfppDistOn_le_lfppLength hγ hmaps).trans_lt
      (hlen.trans_le (min_le_left _ _))
  · exact HigherDimLFPP.lfppDistOn_mono (subset_univ _) hj

/-- On the finite-band confinement event, adding a field bounded in the
outer ball changes the global distances between inner points by a controlled
factor in the upper direction. -/
theorem l6a_global_coupled_upper {d : ℕ} (ξ M : ℝ)
    (H Ψ : Rd d → ℝ) (hH : Continuous H) (hΨ : Continuous Ψ)
    {r R : ℝ} (hrr : r < R)
    {x y : Rd d} (hx : x ∈ ball (0 : Rd d) r) (hy : y ∈ ball (0 : Rd d) r)
    (hcross : HigherDimLFPP.lfppDistOn ξ H univ x y <
      DGZ.lfppSetDist ξ H univ (sphere (0 : Rd d) r) (sphere 0 R))
    (hM : ∀ z ∈ ball (0 : Rd d) R, |Ψ z| ≤ M) :
    HigherDimLFPP.lfppDistOn ξ (fun z => H z + Ψ z) univ x y ≤
      Real.exp (|ξ| * M) * HigherDimLFPP.lfppDistOn ξ H univ x y := by
  have hxR : x ∈ ball (0 : Rd d) R := ball_subset_ball hrr.le hx
  have hyR : y ∈ ball (0 : Rd d) R := ball_subset_ball hrr.le hy
  have hj : HigherDimLFPP.PcwJoined (ball (0 : Rd d) R) x y :=
    HigherDimLFPP.PcwJoined.of_convex (convex_ball _ _) hxR hyR
  calc
    HigherDimLFPP.lfppDistOn ξ (fun z => H z + Ψ z) univ x y ≤
        HigherDimLFPP.lfppDistOn ξ (fun z => H z + Ψ z) (ball 0 R) x y :=
      HigherDimLFPP.lfppDistOn_mono (subset_univ _) hj
    _ ≤ Real.exp (|ξ| * M) * HigherDimLFPP.lfppDistOn ξ H (ball 0 R) x y :=
      HigherDimLFPP.lfppDistOn_le_exp_mul (ζ := ξ) (φ := fun z => H z + Ψ z)
        (ψ := H) (hH.add hΨ) hH (by
          intro z hz
          simpa only [show H z + Ψ z - H z = Ψ z by ring] using hM z hz)
    _ = Real.exp (|ξ| * M) * HigherDimLFPP.lfppDistOn ξ H univ x y := by
      rw [l6a_lfppDistOn_eq_of_crossing ξ H hH hrr hx hy hcross]

end HigherDimLQGMetric
