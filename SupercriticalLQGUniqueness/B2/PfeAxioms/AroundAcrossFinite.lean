import SupercriticalLQGUniqueness.B2.Strong.Annulus
import SupercriticalLQGUniqueness.B2.DG20Lim.FiniteAnnulusCover
import SupercriticalLQGUniqueness.B2.PfeWeyl.W3CircleTools

 


set_option autoImplicit false
noncomputable section

open Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

private theorem radial_separation_scale (A : EuclideanAnnulus) :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1 / 2 ∧
      ∀ x ∈ B2.Strong.radialSeg A 1,
        ∀ y ∈ B2.Strong.radialSeg A (-1), d ≤ dist x y := by
  let K := B2.Strong.radialSeg A 1
  let J := B2.Strong.radialSeg A (-1)
  have hK := B2.Strong.isCompact_radialSeg A 1
  have hJ := B2.Strong.isCompact_radialSeg A (-1)
  have hneK : K.Nonempty := by
    refine ⟨A.center + ((A.innerRadius : ℝ) : ℂ), ?_⟩
    exact ⟨A.innerRadius, left_mem_Icc.mpr A.innerRadius_lt_outerRadius.le,
      by simp⟩
  have hneJ : J.Nonempty := by
    refine ⟨A.center - ((A.innerRadius : ℝ) : ℂ), ?_⟩
    refine ⟨A.innerRadius, left_mem_Icc.mpr A.innerRadius_lt_outerRadius.le, ?_⟩
    simp [← sub_eq_add_neg]
  obtain ⟨p, hp, hmin⟩ :=
    (hK.prod hJ).exists_isMinOn (hneK.prod hneJ)
      (continuous_fst.dist continuous_snd).continuousOn
  have hne : p.1 ≠ p.2 := by
    intro he
    exact Set.disjoint_left.mp (B2.Strong.disjoint_radialSeg A) hp.1 (he ▸ hp.2)
  have hpos : 0 < dist p.1 p.2 := dist_pos.mpr hne
  let d : ℝ := min (dist p.1 p.2 / 2) (1 / 2)
  have hd : 0 < d := by dsimp [d]; positivity
  refine ⟨d, hd, min_le_right _ _, ?_⟩
  intro x hx y hy
  have hle : dist p.1 p.2 ≤ dist x y :=
    hmin (show (x, y) ∈ K ×ˢ J from ⟨hx, hy⟩)
  exact (min_le_left _ _).trans (by linarith)

def radialCoverAnnulus (d : Ioi (0 : ℝ)) (z : ℂ) : EuclideanAnnulus :=
  ⟨(z, ((d : ℝ) / 16, 3 * (d : ℝ) / 4)),
    ⟨by have hd : 0 < (d : ℝ) := d.property; dsimp; positivity,
      by have hd : 0 < (d : ℝ) := d.property; dsimp; linarith⟩⟩

theorem exists_finite_across_bound_around (A : EuclideanAnnulus) :
    ∃ d : Ioi (0 : ℝ), (d : ℝ) ≤ 1 / 2 ∧
      ∃ q : Set ℂ, q.Finite ∧ q.Nonempty ∧
        q ⊆ B2.Strong.radialSeg A 1 ∧
        ∀ (D : LSCMetric), Continuous (B2.PfeWeyl.euclidForget D) →
          (⨅ z ∈ q, acrossDist D (radialCoverAnnulus d z)) ≤ aroundDist D A := by
  obtain ⟨d, hd, hd2, hSep⟩ := radial_separation_scale A
  obtain ⟨q, hqFin, hqSub, hcover⟩ :=
    B2.DG20Lim.finite_annulus_cover_of_separated_compact
      (B2.Strong.isCompact_radialSeg A 1) hd hSep
  have hqNe : q.Nonempty := by
    have hx : A.center + ((A.innerRadius : ℝ) : ℂ) ∈
        B2.Strong.radialSeg A 1 :=
      ⟨A.innerRadius, left_mem_Icc.mpr A.innerRadius_lt_outerRadius.le,
        by simp⟩
    have hy : A.center - ((A.innerRadius : ℝ) : ℂ) ∈
        B2.Strong.radialSeg A (-1) := by
      refine ⟨A.innerRadius, left_mem_Icc.mpr A.innerRadius_lt_outerRadius.le, ?_⟩
      simp [← sub_eq_add_neg]
    obtain ⟨z, hz, -, -⟩ := hcover _ hx _ hy
    exact ⟨z, hz⟩
  refine ⟨⟨d, hd⟩, hd2, q, hqFin, hqNe, hqSub, ?_⟩
  intro D hforget
  unfold aroundDist
  apply le_iInf
  intro P
  apply le_iInf
  intro a
  apply le_iInf
  intro b
  apply le_iInf
  intro hP
  apply le_iInf
  intro hRange
  apply le_iInf
  intro hdisc
  obtain ⟨_, ⟨s, hs, rfl⟩, hsK⟩ :=
    B2.Strong.disconnects_meets_radialSeg A (σ := 1) (by norm_num) hdisc
  obtain ⟨_, ⟨t, ht, rfl⟩, htJ⟩ :=
    B2.Strong.disconnects_meets_radialSeg A (σ := -1) (by norm_num) hdisc
  obtain ⟨z, hz, hnear, hfar⟩ := hcover (P s) hsK (P t) htJ
  let B : EuclideanAnnulus := radialCoverAnnulus ⟨d, hd⟩ z
  have hPc : ContinuousOn P (Icc a b) :=
    B2.PfeWeyl.continuousOn_of_isCurve_of_forget D hforget hP
  have hcross : acrossDist D B ≤ D.len P a b := by
    rcases le_total s t with hst | hts
    · have hpart := B2.PfeWeyl.acrossDist_le_len_of_crossing
        D B hst (hPc.mono (Icc_subset_Icc hs.1 ht.2)) hnear.le hfar.le
      exact hpart.trans (B2.PfeWeyl.len_mono_Icc D P hs.1 ht.2)
    · have hpart := B2.PfeWeyl.acrossDist_le_len_of_crossing_rev
        D B hts (hPc.mono (Icc_subset_Icc ht.1 hs.2)) hfar.le hnear.le
      exact hpart.trans (B2.PfeWeyl.len_mono_Icc D P ht.1 hs.2)
  exact (iInf_le_of_le z (iInf_le_of_le hz hcross))

end SupercriticalLQGUniqueness.B2.PfeAxioms
