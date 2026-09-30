import QuantumZipper.Proofs.Zipper.FieldLawler3UnifB
import QuantumZipper.Proofs.Complex.BasicsUnivalent

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL3-UNIF (C): the conformal map `F : H_η → ℍ` and its continuous extension to `closure H_η`

`fl3u_inverse` (generic): if `Φ` is holomorphic on `ℍ`, maps `ℍ` bijectively onto an open set
`U`, is continuous on `ℍ̄`, maps `ℝ` injectively onto `frontier U` and tends to `∞` at `∞`,
then `F = Φ⁻¹` (on `closure U = Φ(ℍ̄)`) is holomorphic on `U`, bijective `U → ℍ`, continuous on
`closure U`, real on `frontier U` and tends to `∞` at `∞`. Continuity of the inverse is the
standard compactness argument (a continuous injection of a compact set is a homeomorphism onto
its image), here through `IsCompact.tendsto_nhds_of_unique_mapClusterPt` on
`ℍ̄ ∩ B̄(0, R)`, with `R` from the behaviour at `∞`. Holomorphy of the inverse:
`CA.differentiableOn_univalentOPH_symm` (Burckel, *An Introduction to Classical Complex
Analysis*, Thm 5.8 in the repo's `BasicsUnivalent.lean`). Own routine arguments.

`fl3u_conformal_exists`: the conclusion for `U = hullComp η`, from `fl3u_unif_exists`.
-/

noncomputable section

open Filter Set Metric Complex
open scoped Topology

namespace QuantumZipper
namespace FieldLawler

open Thm18Asm.LWFar QuantumZipper.CA

lemma fl3u_isClosed_Hbar : IsClosed Hbar := isClosed_le continuous_const continuous_im

/-- **Inverse of a boundary-continuous uniformization.** -/
theorem fl3u_inverse {U : Set ℂ} {Φ : ℂ → ℂ} (hUo : IsOpen U) (hd : DifferentiableOn ℂ Φ H)
    (hbij : BijOn Φ H U) (hc : ContinuousOn Φ Hbar)
    (hinjR : Function.Injective (fun x : ℝ => Φ x))
    (hrange : range (fun x : ℝ => Φ x) = frontier U)
    (hinf : Tendsto Φ (Bornology.cobounded ℂ ⊓ 𝓟 Hbar) (Bornology.cobounded ℂ)) :
    ∃ F : ℂ → ℂ, BijOn F U H ∧ DifferentiableOn ℂ F U ∧ ContinuousOn F (closure U) ∧
      (∀ p ∈ closure U, F p ∈ Hbar ∧ Φ (F p) = p) ∧ (∀ z ∈ Hbar, F (Φ z) = z) ∧
      (∀ p ∈ frontier U, (F p).im = 0) ∧
      Tendsto F (Bornology.cobounded ℂ ⊓ 𝓟 (closure U)) (Bornology.cobounded ℂ) := by
  have hreal : ∀ z ∈ Hbar, z ∉ H → z = (z.re : ℂ) := fun z hz hzH =>
    Complex.ext (by simp) (by
      simp only [ofReal_im]
      exact le_antisymm (not_lt.1 hzH) hz)
  have hfr : ∀ x : ℝ, Φ x ∈ frontier U := fun x => hrange ▸ ⟨x, rfl⟩
  have hnotU : ∀ x : ℝ, Φ x ∉ U := fun x h => by
    have := hfr x
    rw [hUo.frontier_eq] at this
    exact this.2 h
  have hRH : ∀ x : ℝ, (x : ℂ) ∈ Hbar := fun x => show (0 : ℝ) ≤ ((x : ℂ)).im by simp
  have hinj : InjOn Φ Hbar := by
    intro z hz w hw h
    by_cases hzH : z ∈ H <;> by_cases hwH : w ∈ H
    · exact hbij.injOn hzH hwH h
    · have e := hreal w hw hwH
      exact absurd (show Φ (w.re : ℂ) ∈ U by rw [← e, ← h]; exact hbij.mapsTo hzH) (hnotU _)
    · have e := hreal z hz hzH
      exact absurd (show Φ (z.re : ℂ) ∈ U by rw [← e, h]; exact hbij.mapsTo hwH) (hnotU _)
    · rw [hreal z hz hzH, hreal w hw hwH] at h
      rw [hreal z hz hzH, hreal w hw hwH]
      exact congrArg _ (hinjR h)
  have himg : ∀ p ∈ closure U, ∃ z ∈ Hbar, Φ z = p := by
    intro p hp
    by_cases hpU : p ∈ U
    · obtain ⟨z, hz, rfl⟩ := hbij.surjOn hpU
      exact ⟨z, H_subset_Hbar hz, rfl⟩
    · have : p ∈ frontier U := by rw [hUo.frontier_eq]; exact ⟨hp, hpU⟩
      rw [← hrange] at this
      obtain ⟨x, rfl⟩ := this
      exact ⟨x, hRH x, rfl⟩
  set F := Function.invFunOn Φ Hbar with hFdef
  have hFr : ∀ p ∈ closure U, F p ∈ Hbar ∧ Φ (F p) = p := fun p hp => Function.invFunOn_pos (himg p hp)
  have hFl : ∀ z ∈ Hbar, F (Φ z) = z := fun z hz => hinj.leftInvOn_invFunOn hz
  have hFH : ∀ p ∈ U, F p ∈ H := by
    intro p hp
    have h1 := hFr p (subset_closure hp)
    by_contra hH
    have e := hreal _ h1.1 hH
    exact hnotU (F p).re (by rw [← e, h1.2]; exact hp)
  refine ⟨F, ⟨fun p hp => hFH p hp, fun p hp q hq h => ?_, fun z hz => ?_⟩, ?_, ?_, hFr, hFl,
    ?_, ?_⟩
  · rw [← (hFr p (subset_closure hp)).2, ← (hFr q (subset_closure hq)).2, h]
  · exact ⟨Φ z, hbij.mapsTo hz, hFl z (H_subset_Hbar hz)⟩
  · have hd' := differentiableOn_univalentOPH_symm isOpen_H hd hbij.injOn
    rw [hbij.image_eq] at hd'
    refine hd'.congr fun p hp => ?_
    obtain ⟨z, hz, rfl⟩ := hbij.surjOn hp
    rw [hFl z (H_subset_Hbar hz), univalentOPH_symm_apply_apply isOpen_H hd hbij.injOn hz]
  · intro p hp
    obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ z ∈ Hbar, R < ‖z‖ → ‖p‖ + 1 < ‖Φ z‖ := by
      have hmem := hinf (Bornology.isBounded_def.1
        (isBounded_closedBall (x := (0 : ℂ)) (r := ‖p‖ + 1)))
      rw [mem_map, mem_inf_principal] at hmem
      set S : Set ℂ := {z | z ∈ Hbar → z ∈ Φ ⁻¹' (closedBall 0 (‖p‖ + 1))ᶜ} with hS
      have hSb : Bornology.IsBounded Sᶜ := Bornology.isBounded_def.2 (by rwa [compl_compl])
      obtain ⟨R, hR⟩ := hSb.subset_closedBall 0
      refine ⟨R, fun z hz hzR => ?_⟩
      by_contra hcon
      have hzS : z ∈ Sᶜ := fun h => h hz (by
        rw [mem_closedBall, dist_zero_right]; exact not_lt.1 hcon)
      have := hR hzS
      rw [mem_closedBall, dist_zero_right] at this
      linarith
    have hKc : IsCompact (Hbar ∩ closedBall (0 : ℂ) R) :=
      (isCompact_closedBall 0 R).inter_left fl3u_isClosed_Hbar
    have hFK : ∀ᶠ q in 𝓝[closure U] p, F q ∈ Hbar ∩ closedBall (0 : ℂ) R := by
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds p one_pos)]
        with q hq hq'
      refine ⟨(hFr q hq).1, ?_⟩
      rw [mem_closedBall, dist_zero_right]
      by_contra hcon
      have h1 := hR _ (hFr q hq).1 (not_le.1 hcon)
      rw [(hFr q hq).2] at h1
      have h3 : ‖q - p‖ < 1 := by rw [← dist_eq_norm]; exact mem_ball.1 hq'
      have := norm_sub_norm_le q p
      linarith
    refine hKc.tendsto_nhds_of_unique_mapClusterPt hFK fun x hxK hx => ?_
    have hxH : x ∈ Hbar := hxK.1
    have hne : NeBot (𝓝 x ⊓ map F (𝓝[closure U] p)) := hx
    have hle : map F (𝓝[closure U] p) ≤ 𝓟 Hbar :=
      le_principal_iff.2 (mem_map.2 (eventually_nhdsWithin_of_forall fun q hq => (hFr q hq).1))
    have t1 : Tendsto Φ (𝓝 x ⊓ map F (𝓝[closure U] p)) (𝓝 (Φ x)) :=
      (hc x hxH).tendsto.mono_left (le_inf inf_le_left (inf_le_right.trans hle))
    have t2 : Tendsto Φ (𝓝 x ⊓ map F (𝓝[closure U] p)) (𝓝 p) := by
      refine Tendsto.mono_left ?_ inf_le_right
      rw [tendsto_map'_iff]
      refine (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with q hq
      exact ((hFr q hq).2).symm
    have e : Φ x = p := eq_of_nhds_neBot ((hne.map Φ).mono (tendsto_inf.2 ⟨t1, t2⟩))
    rw [← e, hFl x hxH]
  · intro p hp
    have h1 := hFr p (frontier_subset_closure hp)
    by_contra him
    have hH : F p ∈ H := lt_of_le_of_ne h1.1 (Ne.symm him)
    rw [hUo.frontier_eq] at hp
    exact hp.2 (h1.2 ▸ hbij.mapsTo hH)
  · intro s hs
    obtain ⟨R, hR⟩ := (Bornology.isBounded_def.2
      (by rwa [compl_compl] : sᶜᶜ ∈ Bornology.cobounded ℂ)).subset_closedBall 0
    have hKb : Bornology.IsBounded (Φ '' (Hbar ∩ closedBall 0 R)) :=
      (((isCompact_closedBall 0 R).inter_left fl3u_isClosed_Hbar).image_of_continuousOn
        (hc.mono inter_subset_left)).isBounded
    rw [mem_map, mem_inf_principal]
    refine mem_of_superset (Bornology.isBounded_def.1 hKb) fun p hp hpcl => ?_
    by_contra hps
    exact hp ⟨F p, ⟨(hFr p hpcl).1, hR hps⟩, (hFr p hpcl).2⟩

/-- **FL3-UNIF (U1, homeomorphism part).** For a crosscut `η` of `ℍ` with feet `a ≠ b` there are
`F`, a conformal map of `H_η = hullComp η` onto `ℍ` extending continuously to `closure H_η`, real
on `frontier H_η` and with `F(p) → ∞` as `p → ∞`, and its inverse `Φ`, continuous on `ℍ̄`, mapping
`ℝ` bijectively onto `frontier H_η`. -/
theorem fl3u_conformal_exists {η : ℝ → ℂ} (hη : IsCrosscutH η) {a b : ℝ}
    (ha : Tendsto η (𝓝[>] 0) (𝓝 (a : ℂ))) (hb : Tendsto η (𝓝[<] 1) (𝓝 (b : ℂ)))
    (hab : a ≠ b) :
    ∃ F Φ : ℂ → ℂ, BijOn F (hullComp η) H ∧ DifferentiableOn ℂ F (hullComp η) ∧
      ContinuousOn F (closure (hullComp η)) ∧
      (∀ p ∈ closure (hullComp η), F p ∈ Hbar ∧ Φ (F p) = p) ∧ (∀ z ∈ Hbar, F (Φ z) = z) ∧
      (∀ p ∈ frontier (hullComp η), (F p).im = 0) ∧
      Tendsto F (Bornology.cobounded ℂ ⊓ 𝓟 (closure (hullComp η))) (Bornology.cobounded ℂ) ∧
      DifferentiableOn ℂ Φ H ∧ ContinuousOn Φ Hbar ∧
      Function.Injective (fun x : ℝ => Φ x) ∧
      range (fun x : ℝ => Φ x) = frontier (hullComp η) ∧
      Tendsto Φ (Bornology.cobounded ℂ ⊓ 𝓟 Hbar) (Bornology.cobounded ℂ) := by
  obtain ⟨Φ, hd, hbij, hc, hinj, hrange, hinf⟩ := fl3u_unif_exists hη ha hb hab
  obtain ⟨F, h1, h2, h3, h4, h5, h6, h7⟩ :=
    fl3u_inverse (lwExc_hullComp_isOpen hη) hd hbij hc hinj hrange hinf
  exact ⟨F, Φ, h1, h2, h3, h4, h5, h6, h7, hd, hc, hinj, hrange, hinf⟩

end FieldLawler
end QuantumZipper
