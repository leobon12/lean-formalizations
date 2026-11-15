/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61CmpCfCollar
import InteractingSLE.Spec.Sec5.Aux61RestartComponent

/-! # A counterflow landing collar in the incident retained component

Continuity of the counterflow inverse gives a collar avoiding the own
prefix. Connectivity and incidence identify its retained component.
-/

set_option autoImplicit false
noncomputable section
open Complex Set Filter Topology Metric
open QuantumZipper (H Hbar fwdHull fwdMapInv)

namespace InteractingSLE.Sec5.Aux61GWindow20
open WangWu Aux61Cmp Aux61Restart

/-- A finite counterflow landing off a closed prefix has a whole collar
in any retained component visited arbitrarily near that prime end. -/
theorem exists_cfCollar_of_frequent {w : ℝ → ℝ} {γ η : ℝ → ℂ} {s r x : ℝ}
    (hw : Continuous w) (hw0 : w 0 = 0) (hγ : IsLoewnerTrace w γ) (hs : 0 ≤ s)
    {c : Chart} {b : ℂ}
    (hdom : (c.dom : Set ℂ) = restartComponent (negInv '' fwdHull w s) η r b)
    (hclosed : IsClosed (η '' Icc 0 r)) (hx : x ≠ 0)
    (hH : cfBdry w s x ∈ H) (hpre : cfBdry w s x ∉ η '' Icc 0 r)
    (hone : cfBdry w s x ≠ 1)
    (hfreq : ∃ᶠ z in 𝓝[H] (x : ℂ), revChartInv w s z ∈ (c.dom : Set ℂ)) :
    ∃ δ > 0, MapsTo (revChartInv w s) (H ∩ ball (x : ℂ) δ) c.dom ∧
      ∀ a : ℝ, (a : ℂ) ∈ ball (x : ℂ) δ →
        a ≠ 0 ∧ extendFrom H (fwdMapInv w s) (negInv (a : ℂ)) ≠ 0 ∧ cfBdry w s a ≠ 1 := by
  let B : ℂ → ℂ := fun z => negInv (extendFrom H (fwdMapInv w s) (negInv z))
  have hx' : (x : ℂ) ≠ 0 := ofReal_ne_zero.2 hx
  have hbar : negInv (x : ℂ) ∈ Hbar := mem_Hbar_of_im_eq_zero (negInv_ofReal_im x)
  have hF0 : extendFrom H (fwdMapInv w s) (negInv (x : ℂ)) ≠ 0 := by
    intro heq
    have hz : cfBdry w s x = 0 := by
      rw [cfBdry, heq]
      simp only [negInv, inv_zero, neg_zero]
    have : 0 < (cfBdry w s x).im := hH
    rw [hz, zero_im] at this
    exact lt_irrefl _ this
  have hN : Tendsto negInv (𝓝[Hbar] (x : ℂ)) (𝓝[Hbar] (negInv (x : ℂ))) :=
    tendsto_nhdsWithin_iff.2 ⟨(continuousAt_negInv hx').tendsto.mono_left nhdsWithin_le_nhds,
      eventually_nhdsWithin_of_forall fun z hz => Sec7.PocketJordan.negInv_mem_Hbar hz⟩
  have hB : Tendsto B (𝓝[Hbar] (x : ℂ)) (𝓝 (cfBdry w s x)) :=
    (continuousAt_negInv hF0).tendsto.comp
      (((hγ.hasBdryLimits hw hw0 hs).continuousOn _ hbar).tendsto.comp hN)
  let U : Set ℂ := (H ∩ (η '' Icc 0 r)ᶜ) ∩ {z | z ≠ 1}
  have hU : IsOpen U := (QuantumZipper.isOpen_H.inter hclosed.isOpen_compl).inter isOpen_ne
  have hBU : ∀ᶠ z in 𝓝[Hbar] (x : ℂ), B z ∈ U ∧ z ≠ 0 :=
    (hB.eventually (hU.mem_nhds ⟨⟨hH, hpre⟩, hone⟩)).and
      (mem_nhdsWithin_of_mem_nhds (isOpen_ne.mem_nhds hx'))
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhdsWithin_iff.1 hBU
  have hEq : ∀ z ∈ H, B z = revChartInv w s z := by
    intro z hz
    dsimp only [B, revChartInv]
    rw [extendFrom_fwdMapInv_eq hw hw0 hs (negInv_mem_H hz)]
  have hret : revChartInv w s '' (H ∩ ball (x : ℂ) δ) ⊆
      retainedDomain (negInv '' fwdHull w s) η r := by
    rintro _ ⟨z, hz, rfl⟩
    have hz' := hδsub ⟨hz.2, QuantumZipper.H_subset_Hbar hz.1⟩
    have hK := revChartInv_mem hw hw0 hs hz.1
    refine ⟨hK.1, ?_⟩
    rintro (h | h)
    · exact hK.2 h
    · rw [← hEq z hz.1] at h
      exact hz'.1.1.2 h
  have hconn : IsPreconnected (revChartInv w s '' (H ∩ ball (x : ℂ) δ)) :=
    ((convex_halfSpace_im_gt (r := 0)).inter (convex_ball (x : ℂ) δ)).isPreconnected.image _
      ((isConformalBijection_revChartInv hw hw0 hs).1.continuousOn.mono inter_subset_left)
  have hev : ∀ᶠ z in 𝓝[H] (x : ℂ), z ∈ H ∩ ball (x : ℂ) δ :=
    inter_mem_nhdsWithin H (ball_mem_nhds _ hδ)
  obtain ⟨z, hzD, hz⟩ := (hfreq.and_eventually hev).exists
  have hinc : revChartInv w s z ∈ connectedComponentIn
      (retainedDomain (negInv '' fwdHull w s) η r) b := by rw [← restartComponent, ← hdom]; exact hzD
  have hsub := hconn.subset_connectedComponentIn (mem_image_of_mem _ hz) hret
  rw [← connectedComponentIn_eq hinc, ← restartComponent, ← hdom] at hsub
  refine ⟨δ, hδ, fun z hz => hsub (mem_image_of_mem _ hz), ?_⟩
  intro a ha
  have htest := hδsub ⟨ha, mem_Hbar_of_im_eq_zero (ofReal_im a)⟩
  have haneq : a ≠ 0 := fun heq => htest.2 (by rw [heq, ofReal_zero])
  refine ⟨haneq, ?_, htest.1.2⟩
  intro heq
  have hz : B (a : ℂ) = 0 := by
    dsimp only [B]
    rw [heq]
    simp only [negInv, inv_zero, neg_zero]
  have hpos : 0 < (B (a : ℂ)).im := htest.1.1.1
  rw [hz, zero_im] at hpos
  exact lt_irrefl _ hpos

end InteractingSLE.Sec5.Aux61GWindow20
