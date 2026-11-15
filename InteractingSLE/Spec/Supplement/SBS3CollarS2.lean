/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3CollarTransport
import InteractingSLE.Spec.Supplement.SBS3Geometry

/-!
# Lemma S3: the joint collar from S2's proper witness

Packet PROVE-T14-S3, specification p. 580. A common arc lifts to the real
line. The unused proper tail and deterministic hull transport show that its
upper collar is in the joint unbounded domain. This construction precedes
the relative driving law and makes no relative-trace assumption.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped NNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.SB.S3

/-- S2 supplies a proper lift and, for every compact common arc after its
entrance, an upper collar in the joint unbounded domain up to a later cut
inside that arc. The displayed approach is nontrivial and lands at the
actual physical point. Identification with a marked second-left mean is
a separate analytic step. -/
theorem exists_lift_joint_collar_of_s2 {p : ℝ → ℂ} {β : ℝ≥0 → ℂ}
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
      ∀ a b t : ℝ≥0, a < t → t ≤ b →
        β '' Icc (tL + a) (tL + b) ⊆ p '' Icc 0 1 →
        ∃ ρ > 0,
          g '' (ball (γ t) ρ ∩ H) ⊆
            H \ fillH (p '' Icc 0 1 ∪ β '' Icc 0 (tL + b)) ∧
          (𝓝[H] (γ t)).NeBot ∧
          Tendsto g (𝓝[H] (γ t))
            (𝓝[H \ fillH (p '' Icc 0 1 ∪ β '' Icc 0 (tL + b))] (β (tL + t))) := by
  obtain ⟨-, tL, htL, -, hpre, -, -⟩ := s2HullStatement p β hp hp0 hpH hβ hβ0 hA
  obtain ⟨γ, hγ, hγ0, hlift⟩ :=
    s2LiftStatement p β hp hp0 hpH hβ hβ0 hA c g hc hgc hgi hgf tL htL
  have hAc : IsCompact (p '' Icc 0 1) := isCompact_Icc.image_of_continuousOn hp
  have hconn : IsPreconnected (p '' Icc 0 1 ∪ {z : ℂ | z.im ≤ 0}) :=
    IsPreconnected.union 0 ⟨0, left_mem_Icc.2 zero_le_one, hp0⟩
      (by simp) (isPreconnected_Icc.image p hp) isPreconnected_lowerHalf
  obtain ⟨C₁, C₂, hC₁, hbound⟩ := hc.exists_norm_fwd_le hAc.isBounded hconn
  have hgrow : ∀ w ∈ H, ‖w‖ ≤ C₁ * ‖c.2.1 w‖ + C₂ := by
    intro w hw
    simpa only [hc.1.fwd_inv hw] using hbound _ (hc.1.inv_mem hw)
  refine ⟨tL, γ, htL, hγ, hγ0, hlift, fun a b t hat htb harc => ?_⟩
  have hreal : ∀ s ∈ Icc a b, (γ s).im = 0 := by
    intro s hs
    apply im_eq_zero_of_landing_mem hc.1 hgi (hγ.2.2.1 s)
    rw [hlift]
    exact harc ⟨tL + s, ⟨add_le_add_right hs.1 _, add_le_add_right hs.2 _⟩, rfl⟩
  obtain ⟨ρ, hρ, hcollar⟩ := exists_joint_collar_of_lift hc.1 hgc hgi hC₁ hgrow
    hAc.isClosed hβ.1 hγ hpre hlift hat htb hreal
  have hne : (𝓝[H] (γ t)).NeBot := by
    apply mem_closure_iff_nhdsWithin_neBot.1
    rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]
    exact hγ.2.2.1 t
  have hlim : Tendsto g (𝓝[H] (γ t)) (𝓝 (β (tL + t))) := by
    rw [← hlift]
    exact ((hgc _ (hγ.2.2.1 t)).mono QuantumZipper.H_subset_Hbar).tendsto
  refine ⟨ρ, hρ, hcollar, hne, tendsto_nhdsWithin_iff.2 ⟨hlim, ?_⟩⟩
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (ball_mem_nhds (γ t) hρ)] with w hwH hwb
  exact hcollar ⟨w, ⟨hwb, hwH⟩, rfl⟩

end InteractingSLE.Theorem14.SB.S3
