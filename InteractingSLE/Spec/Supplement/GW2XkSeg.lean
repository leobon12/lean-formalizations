/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootI30Disjoint
import InteractingSLE.Spec.Supplement.SB2VrVis
import InteractingSLE.Spec.Supplement.CounterflowRange
import InteractingSLE.Spec.Supplement.GW2aPieceChart
import InteractingSLE.Foundations.Loewner.YuanCharacterisationMarkov

/-!
# The root-`x` kernel port (D38): the real segment `(0, x]` before the counterflow's visit to `x`

Packet PROVE-GW2-GEOM2, round 11. At a root `x > 0` the launch geometry needs the counterflow's trace up to `s` to miss
the real segment `(0, x]` (in inverted coordinates `(−∞, −1/x]`), and the pole `−1/x` of the translation `M(w) =
w/(xw + 1)` to lie off the closed retained hull. ROOT2's cover gives both through the protected arc `x‖α‖ < 1`, which
is not almost sure. Here both follow from two almost-sure facts on the clock's range: the counterflow visits `x` (BR4a's
`hvR`, `GW2Cone.ae_mem_counterflowCompletedRange_of_theorem13`) and has not visited it by `s`.

* **`trace_ne_of_later_visit`**: a touch of `(−∞, p)` before a later first visit of `p < 0` would swallow `p` untouched
  (`YuanCharacterisation.mem_closure_fillH_of_lt_of_lt`), and a swallowed point is never visited later
  (`SB.Vr.trace_ne_of_mem_closure_hull`);
* **`seg_of_visit`**, **`pole_notMem_closure_of_visit`**: the segment and the pole of the Möbius translation at a root
  `x > 0`;
* **`exists_zero_carrier_seg`**, **`disjoint_closure_translated_hull_seg`**: ROOT2's zero-based carrier and closed-hull
  separation (`RootI30.exists_zero_carrier`, `RootI30.disjoint_closure_translated_hull`) with the segment in place of
  the arc.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Complex
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull)

namespace InteractingSLE.Theorem14.GW2Xk

open Supp8.GB6 Supp8.GB6.CoordB Sec5.CrossRestart ConformalImageFull

/-! ### Swallowing before a later visit -/

/-- **A trace visiting `p < 0` after `s`, and not before, has not touched `(−∞, p)` by `s`.** -/
theorem trace_ne_of_later_visit {W : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace W ⊤ γ) (hWc : Continuous W)
    (hW0 : W 0 = 0) {p : ℝ} (hp : p < 0) {s : ℝ≥0} (hnc : ∀ u ≤ s, γ u ≠ p) {τ : ℝ≥0} (hτ : γ τ = p) {u : ℝ≥0}
    (hu : u ≤ s) {q : ℝ} (hq : q < p) : γ u ≠ q := by
  intro hγu
  have hsτ : s < τ := lt_of_not_ge fun h => hnc τ h hτ
  set U : ℝ → ℝ := fun r => W r.toNNReal with hUdef
  have hUc : Continuous U := hWc.comp continuous_real_toNNReal
  have hU0 : U 0 = 0 := by simp only [hUdef, Real.toNNReal_zero, hW0]
  set η : ℝ → ℂ := fun r => γ r.toNNReal with hηdef
  have hLT : IsLoewnerTraceLT U ((τ + 1 : ℝ≥0) : ℝ) η :=
    CounterflowRange.isLoewnerTraceLT_of_isGeneratingTrace (hγ.mono_horizon le_top)
  have hγc : Continuous γ := continuousOn_univ.1 (hγ.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  have hηc : ContinuousOn η (Icc 0 (u : ℝ)) := (hγc.comp continuous_real_toNNReal).continuousOn
  have hηH : MapsTo η (Icc 0 (u : ℝ)) Hbar := fun r _ => GW2aPiece.trace_mem_Hbar hγ hWc hW0 _
  have hpA : (p : ℂ) ∉ η '' Icc 0 (u : ℝ) := by
    rintro ⟨r, hr, hr'⟩
    exact hnc r.toNNReal ((Real.toNNReal_le_iff_le_coe.2 hr.2).trans hu) hr'
  have hηu : η u = (q : ℂ) := by simp only [hηdef, Real.toNNReal_coe]; exact hγu
  have hη0 : η 0 = 0 := by simp only [hηdef, Real.toNNReal_zero]; exact hγ.1
  have hK := YuanCharacterisation.mem_closure_fillH_of_lt_of_lt hηc hηH (u₁ := u) (u₂ := 0)
    ⟨u.coe_nonneg, le_rfl⟩ ⟨le_rfl, u.coe_nonneg⟩ (by rw [hηu, ofReal_im]) (by rw [hη0, zero_im]) (r := p)
    (by rw [hηu, ofReal_re]; exact hq) (by rw [hη0, zero_re]; exact hp) hpA
  have huτ : (u : ℝ) < ((τ + 1 : ℝ≥0) : ℝ) := by
    have : u < τ + 1 := (hu.trans hsτ.le).trans_lt (lt_add_one τ)
    exact_mod_cast this
  rw [← hLT.2.2 u u.coe_nonneg huτ] at hK
  have hne := SB.Vr.trace_ne_of_mem_closure_hull hUc hU0 hLT u.coe_nonneg (t := (τ : ℝ))
    (by exact_mod_cast hu.trans hsτ.le) (by exact_mod_cast lt_add_one τ) hpA hK
  apply hne
  simp only [hηdef, Real.toNNReal_coe]
  exact hτ

/-! ### The segment, the denominator and the pole at a root `x > 0` -/

section Root

variable {W : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace W ⊤ γ) (hWc : Continuous W) (hW0 : W 0 = 0) {x : ℝ}
  (hx : 0 < x) {s : ℝ≥0} (hnc : ∀ u ≤ s, (x : ℂ) * γ u + 1 ≠ 0) {τ : ℝ≥0} (hτ : (x : ℂ) * γ τ + 1 = 0)
include hγ hWc hW0 hx hnc hτ

omit hγ hWc hW0 hnc hτ in
theorem eq_negInv_iff_den {v : ℂ} : v = ((-x⁻¹ : ℝ) : ℂ) ↔ (x : ℂ) * v + 1 = 0 := by
  have hx' : (x : ℂ) ≠ 0 := ofReal_ne_zero.2 hx.ne'
  push_cast
  constructor
  · rintro rfl; field_simp; ring
  · intro h; field_simp; linear_combination h

/-- **The inverted segment `(−∞, −1/x]` is untouched by `s`.** -/
theorem seg_of_visit : ∀ u ≤ s, ∀ y : ℝ, 0 < y → y ≤ x → γ u ≠ -((y : ℂ))⁻¹ := by
  intro u hu y hy hyx
  have hnc' : ∀ v ≤ s, γ v ≠ ((-x⁻¹ : ℝ) : ℂ) := fun v hv h => hnc v hv ((eq_negInv_iff_den hx).1 h)
  have hτ' : γ τ = ((-x⁻¹ : ℝ) : ℂ) := (eq_negInv_iff_den hx).2 hτ
  have e : -((y : ℂ))⁻¹ = ((-y⁻¹ : ℝ) : ℂ) := by push_cast; ring
  rw [e]
  rcases hyx.eq_or_lt with rfl | hlt
  · exact hnc' u hu
  · exact trace_ne_of_later_visit hγ hWc hW0 (neg_lt_zero.2 (inv_pos.2 hx)) hnc' hτ' hu
      (neg_lt_neg (inv_strictAnti₀ hy hlt))

/-- **The pole `−1/x` lies off the closed counterflow hull at `s`.** -/
theorem pole_notMem_closure_of_visit :
    ((mobPole x 1 : ℝ) : ℂ) ∉ closure (fwdHull (fun r : ℝ => W r.toNNReal) (s : ℝ)) := by
  have hpole : mobPole x 1 = -x⁻¹ := by simp only [mobPole, neg_div, one_div]
  rw [hpole]
  intro hK
  have hnc' : ∀ v ≤ s, γ v ≠ ((-x⁻¹ : ℝ) : ℂ) := fun v hv h => hnc v hv ((eq_negInv_iff_den hx).1 h)
  have hτ' : γ τ = ((-x⁻¹ : ℝ) : ℂ) := (eq_negInv_iff_den hx).2 hτ
  have hsτ : s < τ := lt_of_not_ge fun h => hnc' τ h hτ'
  set U : ℝ → ℝ := fun r => W r.toNNReal with hUdef
  have hUc : Continuous U := hWc.comp continuous_real_toNNReal
  have hU0 : U 0 = 0 := by simp only [hUdef, Real.toNNReal_zero, hW0]
  set η : ℝ → ℂ := fun r => γ r.toNNReal with hηdef
  have hLT : IsLoewnerTraceLT U ((τ + 1 : ℝ≥0) : ℝ) η :=
    CounterflowRange.isLoewnerTraceLT_of_isGeneratingTrace (hγ.mono_horizon le_top)
  have hpA : (((-x⁻¹ : ℝ)) : ℂ) ∉ η '' Icc 0 (s : ℝ) := by
    rintro ⟨r, hr, hr'⟩
    exact hnc' r.toNNReal (Real.toNNReal_le_iff_le_coe.2 hr.2) hr'
  have hne := SB.Vr.trace_ne_of_mem_closure_hull hUc hU0 hLT s.coe_nonneg (t := (τ : ℝ))
    (by exact_mod_cast hsτ.le) (by exact_mod_cast lt_add_one τ) hpA hK
  apply hne
  simp only [hηdef, Real.toNNReal_coe]
  exact hτ'

end Root

/-! ### ROOT2's carrier and separation with the segment in place of the arc -/

/-- **ROOT2's zero-based carrier** (`RootI30.exists_zero_carrier`) with the untouched inverted segment in place of the
protected arc. -/
theorem exists_zero_carrier_seg {α γ : ℝ≥0 → ℂ} {s v : ℝ≥0} {x : ℝ}
    (hx : 0 ≤ x) (hv : 0 < v) (hγ : ContinuousOn γ (Icc 0 v))
    (hγ0 : γ 0 = x) (hγH : MapsTo γ (Icc 0 v) Hbar)
    (hseg : ∀ u ∈ Icc 0 s, ∀ y : ℝ, 0 < y → y ≤ x → α u ≠ -((y : ℂ))⁻¹)
    (hsep : Disjoint (α '' Icc 0 s)
      ((fun z : ℂ => -z⁻¹) '' (γ '' Icc 0 v \ {0}))) :
    ∃ δ : ℝ≥0 → ℂ, ContinuousOn δ (Icc 0 1) ∧ δ 0 = 0 ∧
      MapsTo δ (Icc 0 1) Hbar ∧
      δ '' Icc 0 1 ∩ H = γ '' Icc 0 v ∩ H ∧
      Disjoint (α '' Icc 0 s)
        ((fun z : ℂ => -z⁻¹) '' (δ '' Icc 0 1 \ {0})) := by
  let A : Path (0 : ℂ) (x : ℂ) :=
    { toFun := fun r => ((r.val * x : ℝ) : ℂ)
      continuous_toFun := Complex.continuous_ofReal.comp
        (continuous_subtype_val.mul continuous_const)
      source' := by change ((0 * x : ℝ) : ℂ) = 0; rw [zero_mul, ofReal_zero]
      target' := by change ((1 * x : ℝ) : ℂ) = x; rw [one_mul] }
  have hpar : ∀ r : unitInterval, r.val.toNNReal * v ∈ Icc 0 v := fun r =>
    ⟨zero_le, mul_le_of_le_one_left (zero_le : (0 : ℝ≥0) ≤ v)
      (Real.toNNReal_le_one.mpr r.2.2)⟩
  let B : Path (x : ℂ) (γ v) :=
    { toFun := fun r => γ (r.val.toNNReal * v)
      continuous_toFun := hγ.comp_continuous
        ((continuous_real_toNNReal.comp continuous_subtype_val).mul continuous_const) hpar
      source' := by change γ ((0 : ℝ).toNNReal * v) = x
                    rw [Real.toNNReal_zero, zero_mul, hγ0]
      target' := by change γ ((1 : ℝ).toNNReal * v) = γ v
                    rw [Real.toNNReal_one, one_mul] }
  let C := A.trans B
  let δ : ℝ≥0 → ℂ := fun t => C.extend t
  have hδrange : δ '' Icc 0 1 = range C := by
    apply Subset.antisymm
    · rintro z ⟨t, _, rfl⟩
      rw [← C.extend_range]
      exact mem_range_self _
    · rintro z ⟨r, rfl⟩
      refine ⟨r.val.toNNReal, ⟨zero_le, Real.toNNReal_le_one.mpr r.2.2⟩, ?_⟩
      change C.extend (r.val.toNNReal : ℝ) = C r
      rw [Real.coe_toNNReal _ r.2.1]
      exact C.extend_extends' r
  have hBrange : range B = γ '' Icc 0 v := by
    apply Subset.antisymm
    · rintro z ⟨r, rfl⟩
      exact ⟨_, hpar r, rfl⟩
    · rintro z ⟨t, ht, rfl⟩
      let r : unitInterval := ⟨(t / v : ℝ≥0), by
        exact ⟨(t / v).coe_nonneg, by exact_mod_cast (div_le_one₀ hv).mpr ht.2⟩⟩
      refine ⟨r, ?_⟩
      change γ (Real.toNNReal ((t / v : ℝ≥0) : ℝ) * v) = γ t
      rw [Real.toNNReal_coe, div_mul_cancel₀ _ hv.ne']
  have hδset : δ '' Icc 0 1 = range A ∪ γ '' Icc 0 v := by
    rw [hδrange, Path.trans_range, hBrange]
  have hAH : ∀ z ∈ range A, z ∈ Hbar ∧ z ∉ H := by
    rintro _ ⟨r, rfl⟩
    constructor
    · change 0 ≤ (((r.val * x : ℝ) : ℂ)).im
      rw [ofReal_im]
    · change ¬0 < (((r.val * x : ℝ) : ℂ)).im
      rw [ofReal_im]
      exact lt_irrefl _
  refine ⟨δ, (C.continuous_extend.comp NNReal.continuous_coe).continuousOn,
    C.extend_zero, ?_, ?_, ?_⟩
  · intro t ht
    rcases hδset ▸ mem_image_of_mem δ ht with hz | ⟨q, hq, heq⟩
    · exact (hAH _ hz).1
    · exact heq ▸ hγH hq
  · rw [hδset, union_inter_distrib_right]
    have hempty : range A ∩ H = ∅ := eq_empty_iff_forall_notMem.mpr
      fun z hz => (hAH z hz.1).2 hz.2
    rw [hempty, empty_union]
  · apply disjoint_left.mpr
    rintro _ hα ⟨z, ⟨hz, hn⟩, rfl⟩
    rw [hδset] at hz
    rcases hz with ⟨r, rfl⟩ | hz
    · obtain ⟨u, hu, heq⟩ := hα
      change ((r.val * x : ℝ) : ℂ) ≠ 0 at hn
      have hy0 : 0 < r.val * x := lt_of_le_of_ne (mul_nonneg r.2.1 hx) fun h => hn (by rw [← h, ofReal_zero])
      change α u = -(((r.val * x : ℝ) : ℂ))⁻¹ at heq
      exact hseg u hu _ hy0 (mul_le_of_le_one_left hx r.2.2) heq
    · exact disjoint_left.mp hsep hα ⟨z, ⟨hz, hn⟩, rfl⟩

/-- **ROOT2's closed-hull separation** (`RootI30.disjoint_closure_translated_hull`) with the untouched inverted segment
in place of the protected arc. -/
theorem disjoint_closure_translated_hull_seg {wα w : ℝ≥0 → ℝ} {α γ : ℝ≥0 → ℂ}
    (hα : IsGeneratingTrace wα ⊤ α) (hwα : Continuous wα) (hwα0 : wα 0 = 0)
    (hγ : IsGeneratingTrace w ⊤ γ) (hw : Continuous w) (hw0 : w 0 = 0)
    {s v : ℝ≥0} (hv : 0 < v) {x : ℝ} (hx : 0 ≤ x)
    (hseg : ∀ u ∈ Icc 0 s, ∀ y : ℝ, 0 < y → y ≤ x → α u ≠ -((y : ℂ))⁻¹)
    (hsep : Disjoint (α '' Icc 0 s)
      ((fun z : ℂ => -z⁻¹) '' ((fun t => γ t + x) '' Icc 0 v \ {0}))) :
    Disjoint (closure (fwdHull (Ito.rpath wα) s))
      (closure ((fun z : ℂ => -z⁻¹) '' fwdHull (fun t => Ito.rpath w t + x) v)) := by
  have hγc : ContinuousOn γ (Icc 0 v) :=
    hγ.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top
  have hγH : MapsTo (fun t => γ t + x) (Icc 0 v) Hbar := by
    intro t _
    have ht := Sec7.IsGeneratingTrace.mem_Hbar hγ hw.continuousOn hw0
      (t := t) le_top
    change 0 ≤ (γ t).im at ht
    change 0 ≤ (γ t + x).im
    simpa only [add_im, ofReal_im, add_zero] using ht
  obtain ⟨δ, hδc, hδ0, hδH, hδeq, hδsep⟩ := exists_zero_carrier_seg
    (γ := fun t => γ t + x) hx hv
    (hγc.add continuousOn_const) (by rw [hγ.1, zero_add]) hγH hseg hsep
  obtain ⟨hAk, hAH, hAu, hKA⟩ := rangeData_of_isGeneratingTrace hα
    hwα.continuousOn hwα0 (s := s) ENNReal.coe_lt_top
  have hBk := isCompact_Icc.image_of_continuousOn hδc
  have hBu : ∀ c ∈ (fun z : ℂ => -z⁻¹) '' (δ '' Icc 0 1 \ {0}),
      ∃ P ⊆ (fun z : ℂ => -z⁻¹) '' (δ '' Icc 0 1 \ {0}),
        IsPreconnected P ∧ c ∈ P ∧ ¬ Bornology.IsBounded P := by
    rintro _ ⟨_, ⟨⟨t, ht, rfl⟩, hn⟩, rfl⟩
    exact exists_unbounded_inv_image hδc hδ0 ht hn
  have hK : IsHPHull (fwdHull (Ito.rpath w) v) :=
    isHPHull_fwdHull (hw.comp continuous_real_toNNReal) v.coe_nonneg
  have hfill := GW2TipSystem.RootI30.isFilling_image_add_full hK x (hγ.2.2 v ENNReal.coe_lt_top)
  rw [← fwdHull_add_const, image_image] at hfill
  have hfillδ : IsFilling (fwdHull (fun t => Ito.rpath w t + x) v) (δ '' Icc 0 1) :=
    (isFilling_congr_inter_H hδeq).2 hfill
  have hKB := fwdHull_eq_fillH_of_isFilling hBk hfillδ
  change fwdHull (Ito.rpath wα) s = fillH (α '' Icc 0 s) at hKA
  rw [hKA, hKB]
  exact disjoint_closure_fillH_inv_image hAk hBk hAH
    (by rintro _ ⟨t, ht, rfl⟩; exact hδH ht) hAu hBu hδsep

end InteractingSLE.Theorem14.GW2Xk
