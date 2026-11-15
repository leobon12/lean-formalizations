/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB11GatePrefix

/-!
# GB11: lifts of globally selected finite wall prefixes

The global cut is attained when finite. Its physical endpoint is on the old
trace, so the previously proved real-contact lifting theorem applies directly.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Bornology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull)
open InteractingSLE.YuanSimpleApprox (trMap)

namespace InteractingSLE.Theorem14.GB11Chart

open GW4Traverse GW4Reg GB11Conn

/-- An old trace point cannot belong to the open active domain. This includes
real trace points, where membership in the open half-plane already fails. -/
theorem trace_image_disjoint_domain {W' : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ}
    (hγ : IsGeneratingTrace W' ⊤ γ) (t : ℝ≥0) :
    Disjoint (γ '' Icc 0 t) (H \ fwdHull (fun r : ℝ => W' r.toNNReal) t) := by
  refine disjoint_left.2 ?_
  rintro z ⟨u, hu, rfl⟩ hz
  exact hz.2 (mem_fwdHull_of_isGeneratingTrace hγ hu.2 hz.1)

/-- A finite global attachment cut gives a continuous simple incoming lift from
any positive unvisited starting parameter to its real gate. -/
theorem exists_lift_finite_wall_cut {W' : ℝ≥0 → ℝ} {γ α : ℝ≥0 → ℂ}
    (hW' : Continuous W') (hW'0 : W' 0 = 0) (hγ : IsGeneratingTrace W' ⊤ γ)
    (hα : GB11.IsCompleteSimpleFlow α)
    (hrev : ∀ a a' : ℝ≥0, 0 < a → a < a' →
      GB11.firstVisit γ (α a') < GB11.firstVisit γ (α a))
    {t a b : ℝ≥0} (ha : 0 < a) (hab : a < b)
    (hcut : ∀ v : ℝ≥0, v ∈ wallHitParameters γ α t ↔ (b : ℝ≥0∞) ≤ v) :
    ∃ (q : ℝ) (β : ℝ → ℂ), ContinuousOn β (Icc (a : ℝ) b) ∧
      InjOn β (Icc (a : ℝ) b) ∧ MapsTo β (Icc (a : ℝ) b) Hbar ∧
      (∀ u ∈ Icc (a : ℝ) b, trMap (fun r : ℝ => W' r.toNNReal) 0 t (β u) =
        -(α u.toNNReal)⁻¹) ∧ β b = (q : ℂ) ∧
      EqOn β (fun u => forwardExt (fun r : ℝ => W' r.toNNReal) t
        (-(α u.toNNReal)⁻¹)) (Ico (a : ℝ) b) := by
  have hW : Continuous (fun r : ℝ => W' r.toNNReal) :=
    hW'.comp continuous_real_toNNReal
  have hW0 : (fun r : ℝ => W' r.toNNReal) 0 = 0 := by
    simpa only [Real.toNNReal_zero] using hW'0
  have hαne : ∀ u ∈ Icc (a : ℝ) b, α u.toNNReal ≠ 0 := by
    intro u hu he
    have hu0 : 0 < u.toNNReal := Real.toNNReal_pos.2
      ((NNReal.coe_pos.2 ha).trans_le hu.1)
    exact hu0.ne' (hα.2.1 (he.trans hα.2.2.1.symm))
  have hc : ContinuousOn (fun u : ℝ => -(α u.toNNReal)⁻¹) (Icc (a : ℝ) b) :=
    (((hα.1.comp continuous_real_toNNReal).continuousOn).inv₀ hαne).neg
  have hi : InjOn (fun u : ℝ => -(α u.toNNReal)⁻¹) (Icc (a : ℝ) b) := by
    intro u hu v hv he
    have he' := hα.2.1 (negInv_injective he)
    exact (Real.toNNReal_eq_toNNReal_iff (a.2.trans hu.1) (a.2.trans hv.1)).1 he'
  have hfree : MapsTo (fun u : ℝ => -(α u.toNNReal)⁻¹) (Ico (a : ℝ) b)
      (freeUpper (fun r : ℝ => W' r.toNNReal) t) := by
    intro u hu
    refine negInv_mem_freeUpper_of_lt_cut hW' hW'0 hγ hα hrev hcut
      (Real.toNNReal_pos.2 ((NNReal.coe_pos.2 ha).trans_le hu.1)) ?_
    rw [ENNReal.coe_lt_coe]
    exact (Real.toNNReal_lt_iff_lt_coe (a.2.trans hu.1)).2 hu.2
  have hbA : -(α b)⁻¹ ∈ γ '' Icc 0 t := by
    have hb := (mem_wallHitParameters_iff (Sec5.continuous_of_isGeneratingTrace_top hγ)).1
      ((hcut b).2 le_rfl)
    exact negInv_mem_image_of_firstVisit_le (Sec5.continuous_of_isGeneratingTrace_top hγ)
      (lt_of_le_of_lt hb ENNReal.coe_lt_top) hb
  have hend : -(α ((b : ℝ).toNNReal))⁻¹ ∉ H \ fwdHull (fun r : ℝ => W' r.toNNReal) t := by
    rw [Real.toNNReal_coe]
    exact fun hz => (trace_image_disjoint_domain hγ t).le_bot ⟨hbA, hz⟩
  exact exists_continuous_lift_unvisited_arc (isLoewnerTrace_of_isGeneratingTrace hγ)
    hW hW0 t.2 (NNReal.coe_lt_coe.2 hab) hc hi hfree hend

/-- The entire inverted tail of a proper wall is a finite physical arc ending at
the original counterflow seed. This reuses the compact-arm parametrization. -/
theorem exists_inverted_wall_tail {α : ℝ≥0 → ℂ} (hα : GB11.IsCompleteSimpleFlow α)
    {a : ℝ≥0} (ha : 0 < a) :
    ∃ A : ℝ → ℂ, ContinuousOn A (Icc 0 1) ∧ InjOn A (Icc 0 1) ∧
      A 0 = -(α a)⁻¹ ∧ A 1 = 0 ∧
      A '' Icc 0 1 = (fun z : ℂ => -z⁻¹) '' (α '' Ici a) ∪ {0} := by
  let α₁ : ℝ → ℂ := fun v => α (a + v.toNNReal)
  have hc : ContinuousOn α₁ (Ici 0) :=
    (hα.1.comp (continuous_const.add continuous_real_toNNReal)).continuousOn
  have hi : InjOn α₁ (Ici 0) := by
    intro v hv w hw he
    exact (Real.toNNReal_eq_toNNReal_iff hv hw).1 (add_left_cancel (hα.2.1 he))
  have ht : Tendsto (fun v => ‖α₁ v‖) atTop atTop := hα.2.2.2.2.comp
    (tendsto_atTop_mono (fun v => le_add_self) tendsto_real_toNNReal_atTop)
  have hp : ∀ v ∈ Ici (0 : ℝ), α₁ v ≠ ((0 : ℝ) : ℂ) := by
    intro v _ he
    exact (ne_of_gt (lt_of_lt_of_le ha le_self_add))
      (hα.2.1 (he.trans hα.2.2.1.symm))
  obtain ⟨A, hAc, hAi, hA0, hA1, hAimg⟩ := Sec6.exists_compactArm hc hi ht hp
  have hpsi : ∀ v : ℝ, Sec6.psiMap 0 (α₁ v) = -(α (a + v.toNNReal))⁻¹ := by
    intro v
    simp [Sec6.psiMap, α₁]
  refine ⟨A, hAc, hAi, ?_, hA1, ?_⟩
  · rw [hA0, hpsi]
    simp
  · rw [hAimg]
    congr 1
    ext z
    constructor
    · rintro ⟨_, ⟨v, -, rfl⟩, rfl⟩
      exact ⟨α (a + v.toNNReal), ⟨a + v.toNNReal, mem_Ici.2 le_self_add, rfl⟩,
        (hpsi v).symm⟩
    · rintro ⟨_, ⟨r, hr, rfl⟩, rfl⟩
      refine ⟨α₁ ((r - a : ℝ≥0) : ℝ), ⟨((r - a : ℝ≥0) : ℝ),
        NNReal.coe_nonneg _, rfl⟩, ?_⟩
      rw [hpsi, Real.toNNReal_coe, add_tsub_cancel_of_le hr]

/-- If no finite wall parameter has yet been visited, the globally selected
incoming tail still lifts all the way to a real gate over physical `0`. -/
theorem exists_lift_infinite_wall_cut {W' : ℝ≥0 → ℝ} {γ α : ℝ≥0 → ℂ}
    (hW' : Continuous W') (hW'0 : W' 0 = 0) (hγ : IsGeneratingTrace W' ⊤ γ)
    (hα : GB11.IsCompleteSimpleFlow α)
    (hrev : ∀ a a' : ℝ≥0, 0 < a → a < a' →
      GB11.firstVisit γ (α a') < GB11.firstVisit γ (α a))
    {t a : ℝ≥0} (ha : 0 < a) (hcut : wallHitParameters γ α t = ∅) :
    ∃ (A β : ℝ → ℂ) (q : ℝ),
      ContinuousOn A (Icc 0 1) ∧ InjOn A (Icc 0 1) ∧
      A 0 = -(α a)⁻¹ ∧ A 1 = 0 ∧
      A '' Icc 0 1 = (fun z : ℂ => -z⁻¹) '' (α '' Ici a) ∪ {0} ∧
      ContinuousOn β (Icc 0 1) ∧ InjOn β (Icc 0 1) ∧ MapsTo β (Icc 0 1) Hbar ∧
      (∀ u ∈ Icc 0 1, trMap (fun r : ℝ => W' r.toNNReal) 0 t (β u) = A u) ∧
      β 1 = (q : ℂ) ∧ EqOn β (fun u => forwardExt
        (fun r : ℝ => W' r.toNNReal) t (A u)) (Ico 0 1) := by
  obtain ⟨A, hAc, hAi, hA0, hA1, hAimg⟩ := exists_inverted_wall_tail hα ha
  have hfree : MapsTo A (Ico 0 1) (freeUpper (fun r : ℝ => W' r.toNNReal) t) := by
    intro u hu
    have huC : u ∈ Icc (0 : ℝ) 1 := ⟨hu.1, hu.2.le⟩
    have hu0 : A u ≠ 0 := fun he => hu.2.ne (hAi huC ⟨zero_le_one, le_rfl⟩ (he.trans hA1.symm))
    have hmem := hAimg ▸ mem_image_of_mem A huC
    rcases hmem with ⟨_, ⟨r, hr, rfl⟩, he⟩ | he
    · rw [← he]
      refine negInv_mem_freeUpper_of_lt_cut hW' hW'0 hγ hα hrev (cut := ⊤)
        (fun v => ?_) (ha.trans_le hr) ENNReal.coe_lt_top
      rw [hcut]
      exact iff_of_false (notMem_empty _) (not_le.2 ENNReal.coe_lt_top)
    · exact False.elim (hu0 he)
  have hW : Continuous (fun r : ℝ => W' r.toNNReal) := hW'.comp continuous_real_toNNReal
  have hW0 : (fun r : ℝ => W' r.toNNReal) 0 = 0 := by
    simpa only [Real.toNNReal_zero] using hW'0
  have hend : A 1 ∉ H \ fwdHull (fun r : ℝ => W' r.toNNReal) t := by
    rw [hA1]
    exact fun hz => lt_irrefl (0 : ℝ) hz.1
  obtain ⟨q, β, hc, hi, hH, hF, hβ1, heq⟩ :=
    exists_continuous_lift_unvisited_arc (isLoewnerTrace_of_isGeneratingTrace hγ)
      hW hW0 t.2 zero_lt_one hAc hAi hfree hend
  exact ⟨A, β, q, hAc, hAi, hA0, hA1, hAimg, hc, hi, hH, hF, hβ1, heq⟩

end InteractingSLE.Theorem14.GB11Chart
