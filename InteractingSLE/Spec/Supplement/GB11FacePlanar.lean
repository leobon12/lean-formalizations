/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB11OwnFutureFace

/-!
# GB11: two walls with additional real contacts bound a Jordan curve

The walls need only avoid the incident base arc except at their own gates. In
particular, their other contacts with the original real line are allowed. The
compactification `mu` treats finite and infinite current junctions in one plane.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Bornology
open QuantumZipper (H Hbar)
open InteractingSLE.Sec6

namespace InteractingSLE.Theorem14.GB11Chart

/-- Three simple arcs forming the two walls and their incident base form a Jordan
curve. No restriction on additional real contacts of the walls is imposed. -/
theorem isJordanCurve_walls_base {aR aL b : ℝ → ℂ}
    (hR : ContinuousOn aR (Icc 0 1)) (hL : ContinuousOn aL (Icc 0 1))
    (hb : ContinuousOn b (Icc 0 1)) (hRi : InjOn aR (Icc 0 1))
    (hLi : InjOn aL (Icc 0 1)) (hbi : InjOn b (Icc 0 1))
    (hb0 : b 0 = aR 0) (hb1 : b 1 = aL 0) (h1 : aR 1 = aL 1)
    (hRL : aR '' Icc 0 1 ∩ aL '' Icc 0 1 ⊆ {aR 1})
    (hRb : aR '' Icc 0 1 ∩ b '' Icc 0 1 ⊆ {aR 0})
    (hLb : aL '' Icc 0 1 ∩ b '' Icc 0 1 ⊆ {aL 0}) :
    LQGMetric.JordanMap.IsJordanCurve
      (aR '' Icc 0 1 ∪ aL '' Icc 0 1 ∪ b '' Icc 0 1) := by
  have hj : b 1 = aL 0 := hb1
  have hjoin : InjOn (arcJoin b aL) (Icc 0 1) :=
    injOn_arcJoin hbi hLi hj (by
      rintro w ⟨hwb, hwL⟩
      rw [mem_singleton_iff, hb1]
      exact hLb ⟨hwL, hwb⟩)
  have hJ := Sec7.isJordanCurve_image_union hR (continuousOn_arcJoin hb hL hj) hRi hjoin
    (by rw [arcJoin_zero, hb0]) (by rw [arcJoin_one, h1]) (by
      rw [image_arcJoin hj]
      rintro w ⟨hwR, hwb | hwL⟩
      · exact Or.inl (hRb ⟨hwR, hwb⟩)
      · exact Or.inr (hRL ⟨hwR, hwL⟩))
  rw [image_arcJoin hj, union_comm (b '' Icc 0 1), ← union_assoc] at hJ
  exact hJ

/-- The compactified incident real interval. -/
def gateBase (qR qL : ℝ) : Set ℂ := mu '' (Complex.ofReal '' Icc qR qL)

/-- The compactified incident real interval stays outside the compactified open
current domain, regardless of any additional contacts of its walls with the real line. -/
theorem gateBase_disjoint_ownDomain (W : ℝ → ℝ) (C : Set ℂ) (t qR qL : ℝ) :
    Disjoint (gateBase qR qL) (mu '' ownDomain W C t) := by
  refine disjoint_left.2 ?_
  rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩ ⟨w, hw, he⟩
  have hew : w = (x : ℂ) := mu_injective he
  have hH := hw.1
  rw [hew] at hH
  have h0 : (0 : ℝ) < (x : ℂ).im := hH
  rw [Complex.ofReal_im] at h0
  exact lt_irrefl _ h0

/-- The compactified real segment has a simple parametrization when its gates differ. -/
theorem exists_gateBase_arc {qR qL : ℝ} (hq : qR < qL) :
    ∃ b : ℝ → ℂ, ContinuousOn b (Icc 0 1) ∧ InjOn b (Icc 0 1) ∧
      b 0 = mu qR ∧ b 1 = mu qL ∧ b '' Icc 0 1 = gateBase qR qL := by
  set b : ℝ → ℂ := fun u => mu (segPath (qR : ℂ) (qL : ℂ) u)
  have hseg := image_segPath_ofReal hq.le
  refine ⟨b, continuousOn_mu_Hbar.comp (continuous_segPath _ _).continuousOn ?_,
    mu_injective.injOn.comp (injOn_segPath ?_) (mapsTo_image _ _), ?_, ?_, ?_⟩
  · intro u hu
    obtain ⟨x, -, hx⟩ := hseg ▸ mem_image_of_mem (segPath (qR : ℂ) (qL : ℂ)) hu
    rw [← hx]
    exact ofReal_mem_Hbar x
  · exact fun h => hq.ne (Complex.ofReal_injective h)
  · change mu (segPath (qR : ℂ) (qL : ℂ) 0) = mu qR
    rw [segPath_zero]
  · change mu (segPath (qR : ℂ) (qL : ℂ) 1) = mu qL
    rw [segPath_one]
  · change (mu ∘ segPath (qR : ℂ) (qL : ℂ)) '' Icc 0 1 = _
    rw [image_comp, hseg]
    rfl

/-- The current two-wall boundary is Jordan, with equal or distinct gates and with
additional real contacts away from the incident interval. The junction may be `mu(∞)=0`. -/
theorem isJordanCurve_walls_gateBase {qR qL : ℝ} (hq : qR ≤ qL) {z : ℂ}
    {aR aL : ℝ → ℂ} (hR : ContinuousOn aR (Icc 0 1))
    (hL : ContinuousOn aL (Icc 0 1)) (hRi : InjOn aR (Icc 0 1))
    (hLi : InjOn aL (Icc 0 1)) (hR0 : aR 0 = mu qR) (hL0 : aL 0 = mu qL)
    (hR1 : aR 1 = z) (hL1 : aL 1 = z)
    (hRL : aR '' Icc 0 1 ∩ aL '' Icc 0 1 ⊆ {aR 0, z})
    (hRb : aR '' Icc 0 1 ∩ gateBase qR qL ⊆ {aR 0})
    (hLb : aL '' Icc 0 1 ∩ gateBase qR qL ⊆ {aL 0}) :
    LQGMetric.JordanMap.IsJordanCurve
      (aR '' Icc 0 1 ∪ aL '' Icc 0 1 ∪ gateBase qR qL) := by
  rcases eq_or_lt_of_le hq with heq | hlt
  · have hbase : gateBase qR qL = {aR 0} := by
      rw [heq, gateBase, Icc_self, image_singleton, image_singleton, hR0, heq]
    have hJ := Sec7.isJordanCurve_image_union hR hL hRi hLi
      (by rw [hR0, hL0, heq]) (hR1.trans hL1.symm) (by rwa [hR1])
    rw [hbase, union_eq_left.2 (by
      intro w hw
      rw [mem_singleton_iff] at hw
      exact Or.inl ⟨0, ⟨le_rfl, zero_le_one⟩, hw.symm⟩)]
    exact hJ
  · obtain ⟨b, hbc, hbi, hb0, hb1, hbimg⟩ := exists_gateBase_arc hlt
    have hqne : aR 0 ≠ aL 0 := by
      rw [hR0, hL0]
      exact fun h => hlt.ne (Complex.ofReal_injective (mu_injective h))
    have hRL' : aR '' Icc 0 1 ∩ aL '' Icc 0 1 ⊆ {aR 1} := by
      intro w hw
      rcases hRL hw with he | he
      · have hbR : aR 0 ∈ gateBase qR qL := by
          rw [hR0]
          exact ⟨(qR : ℂ), ⟨qR, ⟨le_rfl, hq⟩, rfl⟩, rfl⟩
        have hwL := hLb ⟨hw.2, he ▸ hbR⟩
        exact False.elim (hqne (he.symm.trans hwL))
      · rw [mem_singleton_iff, hR1]
        exact he
    rw [← hbimg] at hRb hLb ⊢
    exact isJordanCurve_walls_base hR hL hbc hRi hLi hbi
      (hb0.trans hR0.symm) (hb1.trans hL0.symm) (hR1.trans hL1.symm) hRL' hRb hLb

end InteractingSLE.Theorem14.GB11Chart
