/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB11GateFinalFields

/-! # GB11: compactified heads at the original target -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter Topology Metric Bornology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)
open InteractingSLE.YuanSimpleApprox (trMap)

namespace InteractingSLE.Theorem14.GB11Chart
open GW4Traverse GW4Reg GB11Conn

/-- The compactified head from a positive unvisited parameter to the original
target is a simple arc. Uniform bounded displacement of the inverse chart forces
the forward lift to infinity; the existing compact-arm theorem then applies. -/
theorem exists_compactifiedPrefixHead {d : GateSetup} {α : ℝ≥0 → ℂ}
    (hα : GB11.IsCompleteSimpleFlow α)
    (hrev : ∀ r r' : ℝ≥0, 0 < r → r < r' →
      GB11.firstVisit d.γ (α r') < GB11.firstVisit d.γ (α r))
    {cut : ℝ≥0∞} (hcut : IsWallVisitCut d.γ α d.t cut)
    {a : ℝ≥0} (ha : 0 < a) (hacut : (a : ℝ≥0∞) < cut) :
    ∃ b : ℝ → ℂ, ContinuousOn b (Icc 0 1) ∧ InjOn b (Icc 0 1) ∧
      b 0 = mu (forwardExt d.driver d.t (-(α a)⁻¹)) ∧ b 1 = 0 ∧
      b '' Icc 0 1 = (fun r : ℝ≥0 => mu (forwardExt d.driver d.t (-(α r)⁻¹))) ''
        Ioc 0 a ∪ {0} := by
  let τ : ℝ → ℝ := fun v => (a : ℝ) / (1 + v)
  have hτpos : ∀ v ∈ Ici (0 : ℝ), 0 < τ v :=
    fun v hv => div_pos (NNReal.coe_pos.2 ha) (by linarith [show 0 ≤ v from hv])
  have hτle : ∀ v ∈ Ici (0 : ℝ), τ v ≤ a := by
    intro v hv
    change 0 ≤ v at hv
    exact (div_le_iff₀ (by linarith [hv] : 0 < 1 + v)).2 (by
      nlinarith [mul_nonneg a.2 hv])
  have hτc : ContinuousOn τ (Ici 0) := continuousOn_const.div
    (continuousOn_const.add continuousOn_id)
      (fun v hv => ne_of_gt (by linarith [show 0 ≤ v from hv]))
  have hτlim : Tendsto τ atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_left _ 1 tendsto_id)
  have hτnn : ∀ v ∈ Ici (0 : ℝ), ((τ v).toNNReal : ℝ) = τ v :=
    fun v hv => Real.coe_toNNReal _ (hτpos v hv).le
  have hτfree : ∀ v ∈ Ici (0 : ℝ), -(α (τ v).toNNReal)⁻¹ ∈ freeUpper d.driver d.t := by
    intro v hv
    apply negInv_mem_freeUpper_of_lt_cut d.continuous_driver d.driver_zero d.generating
      hα hrev hcut.2 (Real.toNNReal_pos.2 (hτpos v hv))
    exact (ENNReal.coe_le_coe.2 ((Real.toNNReal_le_iff_le_coe).2 (hτle v hv))).trans_lt hacut
  have hτne : ∀ v ∈ Ici (0 : ℝ), α (τ v).toNNReal ≠ 0 := by
    intro v hv he
    exact (Real.toNNReal_pos.2 (hτpos v hv)).ne'
      (hα.2.1 (he.trans hα.2.2.1.symm))
  have hphysc : ContinuousOn (fun v => -(α (τ v).toNNReal)⁻¹) (Ici 0) :=
    ((hα.1.continuousOn.comp (continuous_real_toNNReal.continuousOn.comp hτc
      (mapsTo_univ _ _)) (mapsTo_univ _ _)).inv₀ hτne).neg
  have hW : Continuous d.driver := d.continuous_driver.comp continuous_real_toNNReal
  have hW0 : d.driver 0 = 0 := by
    simpa only [GateSetup.driver, Real.toNNReal_zero] using d.driver_zero
  have hη : IsLoewnerTrace d.driver (fun r => d.γ r.toNNReal) :=
    isLoewnerTrace_of_isGeneratingTrace d.generating
  let β : ℝ → ℂ := fun v => forwardExt d.driver d.t (-(α (τ v).toNNReal)⁻¹)
  have hβc : ContinuousOn β (Ici 0) :=
    (continuousOn_forwardExt hη hW hW0 d.t.2).comp hphysc hτfree
  have hβH : ∀ v ∈ Ici (0 : ℝ), β v ∈ Hbar :=
    fun v hv => forwardExt_mem_Hbar hη hW hW0 d.t.2 (hτfree v hv)
  have hβF : ∀ v ∈ Ici (0 : ℝ), trMap d.driver 0 d.t (β v) = -(α (τ v).toNNReal)⁻¹ :=
    fun v hv => trMap_forwardExt hη hW hW0 d.t.2 (hτfree v hv)
  let ξ : ℝ → ℂ := fun v => β v + Complex.I
  have hξc : ContinuousOn ξ (Ici 0) := hβc.add continuousOn_const
  have hξi : InjOn ξ (Ici 0) := by
    intro v hv w hw he
    have hβeq : β v = β w := add_right_cancel he
    have hp := (hβF v hv).symm.trans ((congrArg (trMap d.driver 0 d.t) hβeq).trans (hβF w hw))
    have harg := congrArg (fun r : ℝ≥0 => (r : ℝ)) (hα.2.1 (negInv_injective hp))
    rw [hτnn v hv, hτnn w hw] at harg
    have heq := (div_eq_div_iff (ne_of_gt (by linarith [show 0 ≤ v from hv] : 0 < 1 + v))
      (ne_of_gt (by linarith [show 0 ≤ w from hw] : 0 < 1 + w))).1 harg
    nlinarith [NNReal.coe_pos.2 ha]
  have hξ0 : ∀ v ∈ Ici (0 : ℝ), ξ v ≠ ((0 : ℝ) : ℂ) := by
    intro v hv he
    have hi : (0 : ℝ) ≤ (β v).im := hβH v hv
    have hh := congrArg Complex.im he
    simp only [ξ, Complex.add_im, Complex.I_im, Complex.ofReal_im] at hh
    linarith
  have hαlim : Tendsto (fun v => α (τ v).toNNReal) atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · simpa only [Function.comp_def, Real.toNNReal_zero, hα.2.2.1] using
        (hα.1.continuousAt.tendsto.comp (continuous_real_toNNReal.tendsto 0 |>.comp hτlim))
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with v hv using hτne v hv
  have hpNorm : Tendsto (fun v => ‖-(α (τ v).toNNReal)⁻¹‖) atTop atTop := by
    simpa only [Function.comp_def, norm_neg] using tendsto_norm_inv_nhdsNE_zero_atTop.comp hαlim
  obtain ⟨M, hM⟩ := Sec6.exists_norm_trMap_zero_sub_le_Hbar hη hW hW0 d.t.2
  have hξlim : Tendsto (fun v => ‖ξ v‖) atTop atTop := by
    apply tendsto_atTop_mono' atTop (f₁ := fun v => ‖-(α (τ v).toNNReal)⁻¹‖ + (-(M + 1))) ?_
      (tendsto_atTop_add_const_right _ (-(M + 1)) hpNorm)
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with v hv
    have hm : ‖-(α (τ v).toNNReal)⁻¹ - β v‖ ≤ M :=
      (congrArg (fun z : ℂ => ‖z - β v‖) (hβF v hv)) ▸ hM (β v) (hβH v hv)
    have h1 := norm_sub_norm_le (-(α (τ v).toNNReal)⁻¹) (β v)
    have h2 := norm_sub_le (ξ v) Complex.I
    have he : ξ v - Complex.I = β v := add_sub_cancel_right _ _
    rw [he, Complex.norm_I] at h2
    linarith
  obtain ⟨b, hbc, hbi, hb0, hb1, hbimg⟩ := Sec6.exists_compactArm (p := 0) hξc hξi hξlim hξ0
  have hpsi : ∀ v : ℝ, Sec6.psiMap 0 (ξ v) = mu (β v) := by
    intro v
    simp only [Sec6.psiMap, Complex.ofReal_zero, sub_zero, ξ, mu]
  refine ⟨b, hbc, hbi, ?_, hb1, ?_⟩
  · rw [hb0, hpsi]
    simp only [β, τ, add_zero, div_one, Real.toNNReal_coe]
  · rw [hbimg]
    congr 1
    ext z
    constructor
    · rintro ⟨_, ⟨v, hv, rfl⟩, he⟩
      exact ⟨(τ v).toNNReal, ⟨Real.toNNReal_pos.2 (hτpos v hv),
        (Real.toNNReal_le_iff_le_coe).2 (hτle v hv)⟩, (hpsi v).symm.trans he⟩
    · rintro ⟨r, hr, rfl⟩
      let v : ℝ := (a : ℝ) / r - 1
      have hv : v ∈ Ici (0 : ℝ) := by
        dsimp [v]
        exact sub_nonneg.2 ((one_le_div (NNReal.coe_pos.2 hr.1)).2 (NNReal.coe_le_coe.2 hr.2))
      have hτv : τ v = r := by
        dsimp [τ, v]
        have hr0 : (r : ℝ) ≠ 0 := (NNReal.coe_pos.2 hr.1).ne'
        have ha0 : (a : ℝ) ≠ 0 := (NNReal.coe_pos.2 ha).ne'
        rw [show 1 + ((a : ℝ) / r - 1) = (a : ℝ) / r by ring]
        field_simp
      refine ⟨ξ v, ⟨v, hv, rfl⟩, ?_⟩
      rw [hpsi]
      simp only [β, hτv, Real.toNNReal_coe]

/-- A positive parameter strictly before its global cut has not been explored. -/
theorem negInv_notMem_trace_of_lt_cut {d : GateSetup} {α : ℝ≥0 → ℂ}
    (hα : GB11.IsCompleteSimpleFlow α) {cut : ℝ≥0∞}
    (hcut : IsWallVisitCut d.γ α d.t cut) {r : ℝ≥0} (hr0 : 0 < r)
    (hrcut : (r : ℝ≥0∞) < cut) : -(α r)⁻¹ ∉ d.γ '' Icc 0 d.t := by
  rintro ⟨v, hv, he⟩
  apply (not_le.2 hrcut) ((hcut.2 r).1 ?_)
  refine ⟨v, hv, ?_⟩
  rw [he]
  have hα0 : α r ≠ 0 := fun he0 => hr0.ne' (hα.2.1 (he0.trans hα.2.2.1.symm))
  field_simp

/-- At the original target, join an exact positive tail to its compactified
head. Their intersection is precisely the joining point, by wall simplicity and
the old-trace value of the tail's gate. -/
theorem exists_compactifiedPrefixArc_zero {d : GateSetup} {α : ℝ≥0 → ℂ}
    (hα : GB11.IsCompleteSimpleFlow α)
    (hrev : ∀ r r' : ℝ≥0, 0 < r → r < r' →
      GB11.firstVisit d.γ (α r') < GB11.firstVisit d.γ (α r))
    {cut : ℝ≥0∞} (hcut : IsWallVisitCut d.γ α d.t cut) :
    Nonempty (CompactifiedPrefixArc d α 0 cut) := by
  obtain ⟨a', ha', hacut'⟩ := exists_between hcut.1
  have hatop : a' ≠ ⊤ := (lt_of_lt_of_le hacut' le_top).ne
  let a : ℝ≥0 := a'.toNNReal
  have haeq : (a : ℝ≥0∞) = a' := ENNReal.coe_toNNReal hatop
  have ha : 0 < a := ENNReal.coe_pos.1 (haeq.symm ▸ ha')
  have hacut : (a : ℝ≥0∞) < cut := haeq.symm ▸ hacut'
  obtain ⟨tail⟩ := exists_compactifiedPrefixArc_of_pos hα hrev ha hacut hcut
  obtain ⟨head, hhc, hhi, hh0, hh1, hhimg⟩ := exists_compactifiedPrefixHead hα hrev hcut ha hacut
  have hjoin : tail.wall 1 = head 0 := by
    rw [tail.one, prefixJunction, ite_eq_right ha.ne', hh0]
  have hW : Continuous d.driver := d.continuous_driver.comp continuous_real_toNNReal
  have hW0 : d.driver 0 = 0 := by
    simpa only [GateSetup.driver, Real.toNNReal_zero] using d.driver_zero
  have hη : IsLoewnerTrace d.driver (fun r => d.γ r.toNNReal) :=
    isLoewnerTrace_of_isGeneratingTrace d.generating
  have hval : ∀ r : ℝ≥0, 0 < r → (r : ℝ≥0∞) < cut →
      trMap d.driver 0 d.t (forwardExt d.driver d.t (-(α r)⁻¹)) = -(α r)⁻¹ := by
    intro r hr0 hr
    exact trMap_forwardExt hη hW hW0 d.t.2
      (negInv_mem_freeUpper_of_lt_cut d.continuous_driver d.driver_zero d.generating
        hα hrev hcut.2 hr0 hr)
  have hnonzero : ∀ r : ℝ≥0, 0 < r → (r : ℝ≥0∞) < cut →
      mu (forwardExt d.driver d.t (-(α r)⁻¹)) ≠ 0 := by
    intro r hr0 hr
    exact mu_ne_zero_of_mem_Hbar (forwardExt_mem_Hbar hη hW hW0 d.t.2
      (negInv_mem_freeUpper_of_lt_cut d.continuous_driver d.driver_zero d.generating
        hα hrev hcut.2 hr0 hr))
  have hinter : tail.wall '' Icc 0 1 ∩ head '' Icc 0 1 ⊆ {tail.wall 1} := by
    rintro z ⟨ht, hh⟩
    rw [hhimg] at hh
    rcases hh with ⟨r, hr, rfl⟩ | hz
    · have hrcut : (r : ℝ≥0∞) < cut := (ENNReal.coe_le_coe.2 hr.2).trans_lt hacut
      obtain ⟨u, hu, he⟩ := ht
      have hne : tail.wall u ≠ 0 := he.symm ▸ hnonzero r hr.1 hrcut
      rcases tail.mem_cases hu hne with hgate | ⟨s, hs0, has, hscut, hes⟩
      · have hq : (tail.q : ℂ) = forwardExt d.driver d.t (-(α r)⁻¹) :=
          mu_injective (hgate.symm.trans he)
        have hOld := tail.gate_old hcut
        change trMap d.driver 0 d.t tail.q ∈ d.γ '' Icc 0 d.t at hOld
        rw [hq, hval r hr.1 hrcut] at hOld
        exact False.elim (negInv_notMem_trace_of_lt_cut hα hcut hr.1 hrcut hOld)
      · have heq : forwardExt d.driver d.t (-(α s)⁻¹) =
            forwardExt d.driver d.t (-(α r)⁻¹) := mu_injective (hes.symm.trans he)
        have hsr : s = r := hα.2.1 (negInv_injective
          ((hval s hs0 hscut).symm.trans ((congrArg (trMap d.driver 0 d.t) heq).trans
            (hval r hr.1 hrcut))))
        have hra : r = a := le_antisymm hr.2 (hsr ▸ has)
        rw [mem_singleton_iff, tail.one, prefixJunction, ite_eq_right ha.ne', hra]
    · have hz0 : z = 0 := hz
      rw [tail.image, selectedPrefixImage, ite_eq_right ha.ne', union_empty] at ht
      rcases ht with ht | ⟨r, hr, he⟩
      · exact False.elim ((mu_ne_zero_of_mem_Hbar (ofReal_mem_Hbar tail.q))
          ((mem_singleton_iff.1 ht).symm.trans hz0))
      · exact False.elim (hnonzero r hr.1 hr.2.2 (he.trans hz0))
  have hwhole : Sec6.arcJoin tail.wall head '' Icc 0 1 = selectedPrefixImage d α 0 cut tail.q := by
    rw [Sec6.image_arcJoin hjoin, tail.image, hhimg, selectedPrefixImage,
      selectedPrefixImage, ite_eq_right ha.ne', union_empty, ite_eq_left rfl]
    ext z
    simp only [mem_union, mem_image, mem_singleton_iff, mem_ofPred_eq, mem_Ioc]
    constructor
    · rintro ((h | ⟨r, hr, rfl⟩) | (⟨r, hr, rfl⟩ | h))
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr ⟨r, ⟨hr.1, zero_le, hr.2.2⟩, rfl⟩)
      · exact Or.inl (Or.inr ⟨r, ⟨hr.1, zero_le,
          (ENNReal.coe_le_coe.2 hr.2).trans_lt hacut⟩, rfl⟩)
      · exact Or.inr h
    · rintro ((h | ⟨r, hr, rfl⟩) | h)
      · exact Or.inl (Or.inl h)
      · rcases le_total a r with har | hra
        · exact Or.inl (Or.inr ⟨r, ⟨hr.1, har, hr.2.2⟩, rfl⟩)
        · exact Or.inr (Or.inl ⟨r, ⟨hr.1, hra⟩, rfl⟩)
      · exact Or.inr (Or.inr h)
  exact ⟨{
    q := tail.q, wall := Sec6.arcJoin tail.wall head,
    continuous := Sec6.continuousOn_arcJoin tail.continuous hhc hjoin,
    injective := Sec6.injOn_arcJoin tail.injective hhi hjoin hinter,
    zero := Sec6.arcJoin_zero.trans tail.zero,
    one := by rw [Sec6.arcJoin_one, hh1, prefixJunction, ite_eq_left rfl],
    image := hwhole, gate_value := tail.gate_value }⟩

/-- Every selected prefix has an exact compactified single arm, including an
exit at the original target and an unattained attachment cut at infinity. -/
theorem exists_compactifiedPrefixArc {d : GateSetup} {α : ℝ≥0 → ℂ}
    (hα : GB11.IsCompleteSimpleFlow α)
    (hrev : ∀ r r' : ℝ≥0, 0 < r → r < r' →
      GB11.firstVisit d.γ (α r') < GB11.firstVisit d.γ (α r))
    {exit : ℝ≥0} {cut : ℝ≥0∞} (hlt : (exit : ℝ≥0∞) < cut)
    (hcut : IsWallVisitCut d.γ α d.t cut) :
    Nonempty (CompactifiedPrefixArc d α exit cut) := by
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ exit) with he | hp
  · subst exit
    exact exists_compactifiedPrefixArc_zero hα hrev hcut
  · exact exists_compactifiedPrefixArc_of_pos hα hrev hp hlt hcut

end InteractingSLE.Theorem14.GB11Chart
