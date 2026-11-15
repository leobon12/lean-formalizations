/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7GapEqFinCollar

/-!
# Local exterior connectivity of a Jordan pocket

PROVE-R7-GAPEQ continuation. Reuse the landed plane Schoenflies theorem. In the disc picture,
inversion identifies an exterior neighborhood with a punctured convex lens inside the disc.
Transport its preconnected relative neighborhoods back to the pocket exterior.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Filter Topology Bornology

namespace InteractingSLE.Sec7.R7GapEqFin

open Sec6 R7GapEq

/-- Local connectivity from within transfers through continuous inverse maps near the marked
point. The maps only need to be inverse on the approached set and at the marked point. -/
theorem isLocConnWithin_of_inverse {D E : Set ℂ} {p : ℂ} {f g : ℂ → ℂ}
    (hfc : ContinuousOn f E) (hfp : ContinuousAt f (g p)) (hgp : ContinuousAt g p)
    (hf : MapsTo f E D) (hg : MapsTo g D E) (hfg : ∀ z ∈ D, f (g z) = z)
    (hfgp : f (g p) = p) (hloc : IsLocConnWithin E (g p)) : IsLocConnWithin D p := by
  intro ε hε
  obtain ⟨δ, hδ, hδf⟩ := Metric.continuousAt_iff.1 hfp ε hε
  obtain ⟨S, hS, hSc, hSN⟩ := hloc δ hδ
  refine ⟨f '' S, ?_, hSc.image f (hfc.mono fun z hz => (hS hz).1), ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    refine ⟨hf (hS hz).1, ?_⟩
    rw [mem_ball, ← hfgp]
    exact hδf (hS hz).2
  · have hlim : Tendsto g (𝓝[D] p) (𝓝[E] (g p)) :=
      tendsto_nhdsWithin_iff.2 ⟨hgp.tendsto.mono_left nhdsWithin_le_nhds,
        (show ∀ᶠ z in 𝓝[D] p, z ∈ D from self_mem_nhdsWithin).mono fun z hz => hg hz⟩
    filter_upwards [hlim.eventually hSN, self_mem_nhdsWithin] with z hz hzD
    exact ⟨g z, hz, hfg z hzD⟩

/-- The open exterior of the unit disc is locally connected at every point of its circle. -/
theorem isLocConnWithin_outside_unitDisc {p : ℂ} (hp : ‖p‖ = 1) :
    IsLocConnWithin {z : ℂ | 1 < ‖z‖} p := by
  have hp0 : p ≠ 0 := norm_pos_iff.1 (by rw [hp]; exact zero_lt_one)
  have hip : ‖p⁻¹‖ = 1 := by rw [norm_inv, hp, inv_one]
  have hip0 : p⁻¹ ≠ 0 := inv_ne_zero hp0
  let E : Set ℂ := ball 0 1 \ {0}
  have hEinv : MapsTo (fun z : ℂ => z⁻¹) E {z : ℂ | 1 < ‖z‖} := by
    intro z hz
    have hz0 : z ≠ 0 := hz.2
    change 1 < ‖z⁻¹‖
    rw [norm_inv]
    exact (one_lt_inv₀ (norm_pos_iff.2 hz0)).2 (mem_ball_zero_iff.1 hz.1)
  have hDinv : MapsTo (fun z : ℂ => z⁻¹) {z : ℂ | 1 < ‖z‖} E := by
    intro z hz
    have hz0 : z ≠ 0 := norm_pos_iff.1 (zero_lt_one.trans hz)
    refine ⟨mem_ball_zero_iff.2 ?_, inv_ne_zero hz0⟩
    rw [norm_inv]
    exact (inv_lt_one₀ (norm_pos_iff.2 hz0)).2 hz
  apply isLocConnWithin_of_inverse (f := fun z : ℂ => z⁻¹) (g := fun z : ℂ => z⁻¹)
    (E := E) (fun z hz => (continuousAt_inv₀ (show z ≠ 0 from hz.2)).continuousWithinAt)
    (continuousAt_inv₀ hip0) (continuousAt_inv₀ hp0) hEinv hDinv
    (fun z _ => inv_inv z) (inv_inv p)
  intro ε hε
  let δ := min ε (1 / 2)
  have hδ : 0 < δ := lt_min hε (by norm_num)
  have hne : ∀ z ∈ ball (p⁻¹) δ, z ≠ 0 := by
    intro z hz he
    have hd : dist (0 : ℂ) p⁻¹ < δ := he ▸ hz
    rw [dist_zero_left, hip] at hd
    exact (not_lt.2 (min_le_right ε (1 / 2) |>.trans (by norm_num))) hd
  refine ⟨ball 0 1 ∩ ball (p⁻¹) δ, fun z hz => ⟨⟨hz.1, hne z hz.2⟩,
    (ball_subset_ball (min_le_left _ _)) hz.2⟩,
    ((convex_ball _ _).inter (convex_ball _ _)).isPreconnected, ?_⟩
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (p⁻¹) hδ)] with z hzE hzδ
  exact ⟨hzE.1, hzδ⟩

/-- **Jordan exterior local connectivity**, including every boundary point. This applies to
the actual bounded change pocket independently of either side's visit order. -/
theorem isLocConnWithin_compl_closure_jordan {C : Set ℂ} (hCo : IsOpen C)
    (hCc : IsConnected C) (hCb : IsBounded C)
    (hCJ : LQGMetric.JordanMap.IsJordanCurve (frontier C)) {p : ℂ} (hp : p ∈ frontier C) :
    IsLocConnWithin (closure C)ᶜ p := by
  obtain ⟨c, hc⟩ := hCc.nonempty
  have hCeq := connectedComponentIn_compl_frontier_eq hCo hCc hc
  have hcfr : c ∈ (frontier C)ᶜ := by
    rw [← hCeq] at hc
    exact connectedComponentIn_subset _ _ hc
  obtain ⟨e, hs, _hb, hout, -⟩ := Foundations.Schoenflies.schoenflies_plane hCJ hcfr
    (by rw [hCeq]; exact hCb)
  rw [hCeq] at hout
  have hDC : (closure C)ᶜ = (frontier C)ᶜ \ C := by
    ext z
    constructor
    · intro hz
      exact ⟨fun h => hz (frontier_subset_closure h), fun h => hz (subset_closure h)⟩
    · rintro ⟨hzf, hzC⟩ hzcl
      exact hzf ⟨hzcl, by rwa [hCo.interior_eq]⟩
  rw [← hDC] at hout
  obtain ⟨q, hq, hqp⟩ := hs.symm ▸ hp
  have hqn : ‖q‖ = 1 := mem_sphere_zero_iff_norm.1 hq
  have hpq : e.symm p = q := by rw [← hqp, e.symm_apply_apply]
  apply isLocConnWithin_of_inverse (f := e) (g := e.symm) e.continuous.continuousOn
    e.continuous.continuousAt e.symm.continuous.continuousAt
    (fun z hz => hout ▸ mem_image_of_mem e hz) ?_ (fun z _ => e.apply_symm_apply z)
    (e.apply_symm_apply p)
  · rw [hpq]
    exact isLocConnWithin_outside_unitDisc hqn
  · intro z hz
    obtain ⟨w, hw, hwz⟩ := hout.symm ▸ hz
    rwa [← hwz, e.symm_apply_apply]

/-- The exterior collar of a bounded Jordan pocket follows from the local inclusion of the
forbidden frontier in the closed pocket. The latter is the remaining ordered-arm geometry. -/
theorem hasExteriorCollar_of_jordan {C F K : Set ℂ} {p : ℂ}
    (hCo : IsOpen C) (hCc : IsConnected C) (hCb : IsBounded C)
    (hCJ : LQGMetric.JordanMap.IsJordanCurve (frontier C)) (hp : p ∈ frontier C)
    (hFo : IsOpen F) (hCF : Disjoint C F) (hfrK : frontier C ⊆ K)
    (hpF : p ∈ closure F) (hfr : ∃ ε > 0, frontier F ∩ ball p ε ⊆ closure C) :
    HasExteriorCollar C F K p :=
  hasExteriorCollar_of_locConn hCo hFo hCF hfrK hpF
    (isLocConnWithin_compl_closure_jordan hCo hCc hCb hCJ hp) hfr

end InteractingSLE.Sec7.R7GapEqFin
