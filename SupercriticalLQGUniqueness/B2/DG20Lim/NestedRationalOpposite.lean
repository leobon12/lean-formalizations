import SupercriticalLQGUniqueness.B2.DG20Lim.AnnulusInnerRadius
import SupercriticalLQGUniqueness.B2.DG20Lim.RationalAgreementLimit

 


set_option autoImplicit false
noncomputable section

open Set Metric Filter Topology

namespace SupercriticalLQGUniqueness.B2.DG20Lim

private theorem RatCircle.toSet_outside_nested
    {O I : RatCircle} (h : O.SurroundsCircle I) :
    O.toSet ⊆ I.openDiskᶜ := by
  intro x hx hxi
  have hxo : x ∈ O.openDisk :=
    h.2 (I.openDisk_subset_closedDisk hxi)
  exact (ne_of_lt (mem_ball.mp hxo)) (mem_sphere.mp hx)

theorem eventually_nested_rational_opposite
    (Z W : RatCircle) (hZ : Z.radius = 0) (hW : W.radius = 0)
    (hZW : Z.center ≠ W.center)
    (Bz Bw : ℕ → RatAnnulus)
    (hz : ∀ n, (Bz n).inner.Surrounds Z.center)
    (hw : ∀ n, (Bw n).inner.Surrounds W.center)
    (hnz : ∀ n, (Bz n).inner.SurroundsCircle (Bz (n + 1)).outer)
    (hnw : ∀ n, (Bw n).inner.SurroundsCircle (Bw (n + 1)).outer)
    (hrz : Tendsto (fun n => (((Bz n).outer.radius : ℝ))) atTop (𝓝 0))
    (hrw : Tendsto (fun n => (((Bw n).outer.radius : ℝ))) atTop (𝓝 0)) :
    ∀ᶠ n in atTop,
      (Bz (n + 1)).OppositeSides Z (Bz n).outer ∧
      (Bz (n + 1)).OppositeSides (Bw (n + 1)).inner (Bz (n + 1)).inner ∧
      (Bw (n + 1)).OppositeSides Z (Bw (n + 1)).inner ∧
      (Bw (n + 1)).OppositeSides W (Bw n).outer := by
  have hrz' : Tendsto (fun n => (((Bz (n + 1)).outer.radius : ℝ)))
      atTop (𝓝 0) := (tendsto_add_atTop_iff_nat 1).mpr hrz
  have hrw' : Tendsto (fun n => (((Bw (n + 1)).outer.radius : ℝ)))
      atTop (𝓝 0) := (tendsto_add_atTop_iff_nat 1).mpr hrw
  have hdisj := eventually_disjoint_shrinking_disks hZW
    (fun n => (Bz (n + 1)).outer) (fun n => (Bw (n + 1)).outer)
    (Eventually.of_forall fun n => RatAnnulus.outer_surrounds_of_inner (hz (n + 1)))
    (Eventually.of_forall fun n => RatAnnulus.outer_surrounds_of_inner (hw (n + 1)))
    hrz' hrw'
  filter_upwards [hdisj] with n hd
  let Au := Bz (n + 1)
  let Av := Bw (n + 1)
  have hZin : Z.toSet ⊆ Au.inner.closedDisk := by
    rw [Z.toSet_eq_singleton_of_radius_zero hZ]
    exact singleton_subset_iff.mpr
      (Au.inner.openDisk_subset_closedDisk (hz (n + 1)).2)
  have hWin : W.toSet ⊆ Av.inner.closedDisk := by
    rw [W.toSet_eq_singleton_of_radius_zero hW]
    exact singleton_subset_iff.mpr
      (Av.inner.openDisk_subset_closedDisk (hw (n + 1)).2)
  have hUoin : (Bz n).outer.SurroundsCircle Au.outer :=
    (Bz n).nested.trans (hnz n)
  have hVoin : (Bw n).outer.SurroundsCircle Av.outer :=
    (Bw n).nested.trans (hnw n)
  have hVout : Av.inner.toSet ⊆ Au.outer.openDiskᶜ := by
    intro x hx hxAu
    have hxAv : x ∈ Av.outer.closedDisk :=
      Av.outer.openDisk_subset_closedDisk
        (Av.nested.2 (Av.inner.toSet_subset_closedDisk hx))
    exact (Set.disjoint_left.mp hd)
      (Au.outer.openDisk_subset_closedDisk hxAu) hxAv
  have hZout : Z.toSet ⊆ Av.outer.openDiskᶜ := by
    intro x hx hxAv
    have hxZ : x = Z.center := by
      simpa only [Z.toSet_eq_singleton_of_radius_zero hZ, mem_singleton_iff] using hx
    have hxAu : x ∈ Au.outer.closedDisk :=
      hxZ ▸ Au.outer.openDisk_subset_closedDisk
        (Au.nested.2 (Au.inner.openDisk_subset_closedDisk (hz (n + 1)).2))
    exact (Set.disjoint_left.mp hd) hxAu
      (Av.outer.openDisk_subset_closedDisk hxAv)
  refine ⟨Or.inl ⟨hZin, RatCircle.toSet_outside_nested hUoin⟩,
    Or.inr ⟨Au.inner.toSet_subset_closedDisk, hVout⟩,
    Or.inr ⟨Av.inner.toSet_subset_closedDisk, hZout⟩,
    Or.inl ⟨hWin, RatCircle.toSet_outside_nested hVoin⟩⟩

end SupercriticalLQGUniqueness.B2.DG20Lim
