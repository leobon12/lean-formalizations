import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCSquareLoop
import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPathDegree

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set QuantumZipper.CA.Topo

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF

theorem laneC_four_wide_open_loop {ξ : ℝ} {f : ℂ → ℝ}
    {top bot left right : ℝ → ℂ}
    (htop : AdmPath (laneCDoublePrimeWideRect 0).toSet
      (laneCDoublePrimeWideRect 0).side₁
      (laneCDoublePrimeWideRect 0).side₂ top)
    (hbot : AdmPath (laneCDoublePrimeWideRect 1).toSet
      (laneCDoublePrimeWideRect 1).side₁
      (laneCDoublePrimeWideRect 1).side₂ bot)
    (hleft : AdmPath (laneCDoublePrimeWideRect 2).toSet
      (laneCDoublePrimeWideRect 2).side₁
      (laneCDoublePrimeWideRect 2).side₂ left)
    (hright : AdmPath (laneCDoublePrimeWideRect 3).toSet
      (laneCDoublePrimeWideRect 3).side₁
      (laneCDoublePrimeWideRect 3).side₂ right)
    {d : ℝ} (hd : 0 < d) (hdsmall : d ≤ 1 / 1000) :
    ∃ ρ : ℝ → ℂ,
      IsPiecewiseC1Path ρ (ρ 0) (ρ 1) ∧
      ρ 0 = ρ 1 ∧
      MapsTo ρ (Icc (0 : ℝ) 1) laneCDoublePrimeAround ∧
      Disconnects (ρ '' Icc (0 : ℝ) 1)
        laneCDoublePrimeInner laneCDoublePrimeOuter := by
  obtain ⟨γ, hp, hc, hm, hdeg, _⟩ :=
    laneC_four_wide_closed_loop (ξ := ξ) (f := f) htop hbot hleft hright
  let ρ := laneCInwardPush d ∘ γ
  have hρp : IsPiecewiseC1Path ρ (ρ 0) (ρ 1) := by
    simpa [ρ, Function.comp] using laneC_inwardPush_piecewise d hp
  have hρc : ρ 0 = ρ 1 := by simp [ρ, hc]
  have hρm : MapsTo ρ (Icc (0 : ℝ) 1) laneCDoublePrimeAround :=
    laneC_inwardPush_path_open hd hdsmall hm
  let L : C(unitInterval, ℂ) :=
    ⟨fun u => ρ u,
      hρp.continuousOn.comp_continuous continuous_subtype_val (fun u => u.2)⟩
  let P : C(unitInterval, ℂ) :=
    ⟨fun u => γ u,
      hp.continuousOn.comp_continuous continuous_subtype_val (fun u => u.2)⟩
  have hP : ∀ u, P u ∈ laneCDoublePrimeCross := fun u => hm u.2
  have hPclosed : P 0 = P 1 := hc
  have hLopen : ∀ u, L u ∈ laneCDoublePrimeAround := fun u => hρm u.2
  have hLclosed : L 0 = L 1 := hρc
  have hpush := laneC_inwardPush_loopDeg_eq hd hdsmall P hP hPclosed
  have hLdeg : loopDeg
      ⟨fun u => L u - laneCSquareCenter, L.continuous.sub continuous_const⟩
      (by
        intro u hz
        have hcenter : laneCSquareCenter ∈ laneCInnerCluster := by
          norm_num [laneCSquareCenter, laneCInnerCluster, Complex.mem_reProdIm]
        exact (hLopen u).2 ((sub_eq_zero.mp hz) ▸ hcenter)) = 1 := by
    convert hpush.trans hdeg using 1
    congr 1
  have hsep := laneC_open_loop_disconnects L hLclosed hLopen (by
    rw [hLdeg]
    norm_num)
  have hrange : range L = ρ '' Icc (0 : ℝ) 1 := by
    ext z
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨u, u.2, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t, ht⟩, rfl⟩
  exact ⟨ρ, hρp, hρc, hρm, hrange ▸ hsep⟩

end SupercriticalLQGUniqueness.B2.DG20Conc
