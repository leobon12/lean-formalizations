/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3EntryPositive
import InteractingSLE.Spec.Supplement.SBS3CollarS2
import InteractingSLE.Spec.Supplement.SBS3CollarSide

/-!
# Lemma S3: the positive left collar of an actual S2 lift

Packet PROVE-T14-S3, specification p. 580. The positivity assumption in the
previous collar adapter is now supplied from the left-entry orientation.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped NNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.SB.S3

/-- S2's lift has a positive real contact coordinate and one common upper
collar which lies on its left side and maps into the joint unbounded domain.
The approach to the physical contact is explicitly nontrivial. -/
theorem exists_positive_left_joint_collar_of_s2 {p : ℝ → ℂ} {β : ℝ≥0 → ℂ}
    (hp : ContinuousOn p (Icc 0 1)) (hp0 : p 0 = 0)
    (hpH : ∀ s ∈ Icc (0 : ℝ) 1, 0 ≤ (p s).im)
    (hβ : Supp9B.IsProperCurve β) (hβ0 : β 0 = 0)
    (hA : p '' Icc 0 1 ⊆ Supp9B.closedRightSide β)
    {c : Chart} {g : ℂ → ℂ}
    (hc : IsLeftEntryChart (p '' Icc 0 1) (realMin (p '' Icc 0 1)) c)
    (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H)
    (hgf : ∀ z, (g ⁻¹' {z} ∩ {w | 0 ≤ w.im}).Finite) :
    ∃ (tL : ℝ≥0) (γ : ℝ≥0 → ℂ),
      β tL = realMin (p '' Icc 0 1) ∧ Supp9B.IsProperCurve γ ∧ γ 0 = 0 ∧
      (∀ s, g (γ s) = β (tL + s)) ∧
      ∀ a b t : ℝ≥0, t ∈ Ioo a b →
        β '' Icc (tL + a) (tL + b) ⊆ p '' Icc 0 1 →
        0 < (γ t).re ∧ ∃ ρ > 0,
          g '' (ball (γ t) ρ ∩ H) ⊆
            H \ fillH (p '' Icc 0 1 ∪ β '' Icc 0 (tL + b)) ∧
          ball (γ t) ρ ∩ H ⊆ Supp9B.leftSide γ ∧
          (𝓝[H] (γ t)).NeBot ∧
          Tendsto g (𝓝[H] (γ t))
            (𝓝[H \ fillH (p '' Icc 0 1 ∪ β '' Icc 0 (tL + b))] (β (tL + t))) := by
  obtain ⟨tL, γ, htL, hγ, hγ0, hlift, hcollars⟩ :=
    exists_lift_joint_collar_of_s2 hp hp0 hpH hβ hβ0 hA hc hgc hgi hgf
  refine ⟨tL, γ, htL, hγ, hγ0, hlift, fun a b t ht harc => ?_⟩
  have hreal : ∀ s ∈ Icc a b, (γ s).im = 0 := by
    intro s hs
    apply im_eq_zero_of_landing_mem hc.1 hgi (hγ.2.2.1 s)
    rw [hlift]
    exact harc ⟨tL + s, ⟨add_le_add_right hs.1 _, add_le_add_right hs.2 _⟩, rfl⟩
  have htA : g (γ t) ∈ p '' Icc 0 1 := by
    rw [hlift]
    exact harc ⟨tL + t, ⟨add_le_add_right ht.1.le _, add_le_add_right ht.2.le _⟩, rfl⟩
  have hpos := re_pos_of_lift_landing_mem_old hp hp0 hc hgc hgi hγ hγ0
    (lt_of_le_of_lt zero_le ht.1) htA
  obtain ⟨rJ, hrJ, hJ, hne, hlim⟩ := hcollars a b t ht.1 ht.2.le harc
  obtain ⟨rL, hrL, hL⟩ := exists_upper_collar_subset_leftSide hγ hγ0 ht
    (fun s hs => hreal s (Ioo_subset_Icc_self hs)) hpos
  refine ⟨hpos, min rJ rL, lt_min hrJ hrL, ?_, ?_, hne, hlim⟩
  · exact (image_mono (inter_subset_inter_left H
      (Metric.ball_subset_ball (min_le_left rJ rL)))).trans hJ
  · exact (inter_subset_inter_left H
      (Metric.ball_subset_ball (min_le_right rJ rL))).trans hL

end InteractingSLE.Theorem14.SB.S3
