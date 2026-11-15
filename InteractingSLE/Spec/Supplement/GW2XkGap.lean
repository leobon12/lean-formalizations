/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2XkUnion
import InteractingSLE.Spec.Supplement.GW2OmxGeo
import InteractingSLE.Spec.Supplement.GW2XkSeg

/-!
# The root-`x` kernel port (D38): the no-contact event at a root `x`

Packet PROVE-GW2-GEOM2, round 11 (STAGEMEAN's `GW2Omx.noContact` and `GW2OmxGeo` at a root `x`). At the root
`x = rootPt r.1` the explored physical trace is `x + η_e`, so the no-contact event compares the counterflow with the
translated explored reader:

* `noContactX` (STAGEMEAN's gap event with the explored reader shifted by `x`), **`measurableSet_noContactX`** (for
  RELDET's kernel marks);
* **`mem_noContactX_iff`**: for continuous traces, no `η t · (x + η_e u) + 1 = 0` on the boxes;
* `disjoint_closure_negInv_swap` (closure disjointness through the inversion, for bounded sets in `ℍ`),
  `fwdHull_zero_eq_empty`;
* `den_of_mem_noContactX` (no contact keeps the counterflow off the pole `−1/x` on `[0, s]`), `pole_of_mem_noContactX`
  (with the counterflow's visit to `x > 0`, the pole lies off the closed counterflow hull at `s`);
* **`disjoint_closure_of_mem_noContactX`**: no contact and the counterflow's visit to `x` separate the closures of the
  translated explored hull and of the retained hull (`GW2Xk.disjoint_closure_translated_hull_seg`, ROOT2's
  separation with the untouched segment `(0, x]` in place of the protected arc);
* **`mem_noContactX_iff_lt_firstTipTime`**: no contact is the datum's range condition with the translated explored
  trace image as retained prefix.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H fwdMap fwdMapInv fwdHull)

universe u

namespace InteractingSLE.Theorem14.GW2Xk

open GW2Omx GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2Rd Supp8.GB6 Exist.StagedLaw

/-! ### Two generic facts -/

/-- **Closure disjointness through the inversion** `R z = −1/z`, for a bounded set `A ⊆ ℍ`. -/
theorem disjoint_closure_negInv_swap {A B : Set ℂ} (hAH : A ⊆ H) (hAb : Bornology.IsBounded A)
    (h : Disjoint (closure A) (closure ((fun z : ℂ => -z⁻¹) '' B))) :
    Disjoint (closure B) (closure ((fun z : ℂ => -z⁻¹) '' A)) := by
  rw [Set.disjoint_left]
  intro y hyB hyA
  obtain ⟨M, hM⟩ := hAb.exists_norm_le
  set M' := max M 1 with hM'
  have hM'pos : 0 < M' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hy0 : y ≠ 0 := by
    intro h0
    have hsub : (fun z : ℂ => -z⁻¹) '' A ⊆ {v : ℂ | 1 / M' ≤ ‖v‖} := by
      rintro _ ⟨a, ha, rfl⟩
      have ha0 : a ≠ 0 := fun h => by
        have := hAH ha
        rw [h] at this
        exact lt_irrefl _ (show (0 : ℂ).im > 0 from this)
      have hapos : 0 < ‖a‖ := norm_pos_iff.2 ha0
      have hale : ‖a‖ ≤ M' := (hM a ha).trans (le_max_left _ _)
      show 1 / M' ≤ ‖-a⁻¹‖
      rw [norm_neg, norm_inv, one_div]
      exact inv_anti₀ hapos hale
    have := closure_minimal hsub (isClosed_le continuous_const continuous_norm) hyA
    rw [h0] at this
    simp only [mem_ofPred_eq, norm_zero] at this
    have : 0 < 1 / M' := by positivity
    linarith
  have hcont : ContinuousAt (fun z : ℂ => -z⁻¹) y := (continuousAt_inv₀ hy0).neg
  have h1 : -y⁻¹ ∈ closure ((fun z : ℂ => -z⁻¹) '' B) := hcont.continuousWithinAt.mem_closure_image hyB
  have h2 : -y⁻¹ ∈ closure ((fun z : ℂ => -z⁻¹) '' ((fun z : ℂ => -z⁻¹) '' A)) :=
    hcont.continuousWithinAt.mem_closure_image hyA
  have hRR : (fun z : ℂ => -z⁻¹) '' ((fun z : ℂ => -z⁻¹) '' A) = A := by
    rw [image_image]
    conv_rhs => rw [← image_id A]
    exact image_congr fun z _ => by simp only [inv_neg, inv_inv, neg_neg, id]
  rw [hRR] at h2
  exact Set.disjoint_left.1 h h2 h1

/-- The hull of a continuous driver from `0` at time `0` is empty. -/
theorem fwdHull_zero_eq_empty {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) : fwdHull W 0 = ∅ := by
  have h0 := hcap_fwdHull hW hW0 (le_refl 0)
  rw [mul_zero] at h0
  exact (HPHull.hcap_eq_zero_iff _).1 h0

/-! ### The root-`x` no-contact event -/

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
  (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)

/-- **The physical no-contact event at the root `x`**: STAGEMEAN's gap event with the explored reader translated to
the root. -/
def noContactX : Set Ω :=
  gapEvent (cfRead c) (fun ω q => (rootPt r.1 : ℂ) + explRead c r l a ω q) c.s (historyTime c r l)

theorem measurableSet_noContactX (t : ℝ≥0) : MeasurableSet[kerMarks c r l a t] (noContactX c r l a) := by
  unfold noContactX gapEvent gapAt
  refine MeasurableSet.iUnion fun n => MeasurableSet.iInter fun q₁ => MeasurableSet.iInter fun q₂ => ?_
  by_cases hq : 0 ≤ (q₁ : ℝ) ∧ (q₁ : ℝ) ≤ c.s ∧ 0 ≤ (q₂ : ℝ) ∧ (q₂ : ℝ) ≤ historyTime c r l
  · have e : {ω | (0 ≤ (q₁ : ℝ) ∧ (q₁ : ℝ) ≤ c.s ∧ 0 ≤ (q₂ : ℝ) ∧ (q₂ : ℝ) ≤ historyTime c r l) →
        1 / ((n : ℝ) + 1) ≤ ‖cfRead c ω (q₁ : ℝ).toNNReal *
          ((rootPt r.1 : ℂ) + explRead c r l a ω (q₂ : ℝ).toNNReal) + 1‖} =
        {ω | 1 / ((n : ℝ) + 1) ≤ ‖cfRead c ω (q₁ : ℝ).toNNReal *
          ((rootPt r.1 : ℂ) + explRead c r l a ω (q₂ : ℝ).toNNReal) + 1‖} := by
      ext ω
      simp only [mem_ofPred_eq, hq, and_self, true_implies]
    rw [e]
    have hle : (q₂ : ℝ).toNNReal ≤ historyTime c r l + t := by
      rw [Real.toNNReal_le_iff_le_coe]
      have := hq.2.2.2
      have h2 : (historyTime c r l : ℝ) ≤ ((historyTime c r l + t : ℝ≥0) : ℝ) := by
        exact_mod_cast le_add_of_nonneg_right zero_le
      linarith
    have hpair : Measurable[kerMarks c r l a t] (fun ω => (cfRead c ω (q₁ : ℝ).toNNReal,
        (rootPt r.1 : ℂ) + explRead c r l a ω (q₂ : ℝ).toNNReal)) :=
      (measurable_cfRead_kerMarks c r l a t _).prodMk
        (measurable_const.add (measurable_explRead_kerMarks c r l a t hle))
    have hcont : Continuous fun p : ℂ × ℂ => ‖p.1 * p.2 + 1‖ :=
      ((continuous_fst.mul continuous_snd).add continuous_const).norm
    exact (hcont.measurable.comp hpair) measurableSet_Ici
  · simp only [hq, false_implies, ofPred_true]
    exact MeasurableSet.univ

/-- **The root-`x` no-contact event, per sample**: separation of the counterflow trace from the translated explored
trace on the boxes. -/
theorem mem_noContactX_iff {ω : Ω} {η ηe : ℝ≥0 → ℂ} (hη : IsGeneratingTrace (fun u => c.W u ω) ⊤ η)
    (hc : Continuous fun u => c.W u ω) (h0 : c.W 0 ω = 0) (hs : (c.s : ℝ≥0∞) < c.ζ ω)
    (hηe : IsGeneratingTrace (fun u => schedW c r l a u ω) ⊤ ηe) (hce : Continuous fun u => schedW c r l a u ω)
    (h0e : schedW c r l a 0 ω = 0) :
    ω ∈ noContactX c r l a ↔
      ∀ t ∈ Icc 0 c.s, ∀ u ∈ Icc 0 (historyTime c r l), η t * ((rootPt r.1 : ℂ) + ηe u) + 1 ≠ 0 := by
  unfold noContactX
  rw [mem_gapEvent_congr (γ' := fun _ => η) (α' := fun _ u => (rootPt r.1 : ℂ) + ηe u)
    (fun q hq => cfRead_eq_of_trace c hη hc h0 hs hq)
    (fun q _ => by simp only [explRead_eq_of_trace c r l a hηe hce h0e q])]
  exact mem_gapEvent_iff (γ := fun _ => η) (α := fun _ u => (rootPt r.1 : ℂ) + ηe u)
    (continuousOn_univ.1 (hη.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top))
    (continuous_const.add (continuousOn_univ.1 (hηe.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top)))

/-- **No contact at the root `x` keeps the counterflow off the pole `−1/x` on `[0, s]`** (the explored trace starts at
`x`). -/
theorem den_of_mem_noContactX {ω : Ω} {η ηe : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace (fun u => c.W u ω) ⊤ η) (hc : Continuous fun u => c.W u ω) (h0 : c.W 0 ω = 0)
    (hs : (c.s : ℝ≥0∞) < c.ζ ω) (hηe : IsGeneratingTrace (fun u => schedW c r l a u ω) ⊤ ηe)
    (hce : Continuous fun u => schedW c r l a u ω) (h0e : schedW c r l a 0 ω = 0) (hω : ω ∈ noContactX c r l a) :
    ∀ u ≤ c.s, (rootPt r.1 : ℂ) * η u + 1 ≠ 0 := by
  intro u hu
  have h := (mem_noContactX_iff c r l a hη hc h0 hs hηe hce h0e).1 hω u ⟨zero_le, hu⟩ 0 ⟨le_rfl, zero_le⟩
  rw [hηe.1, add_zero, mul_comm] at h
  exact h

/-- **With the counterflow's visit to `x > 0`, no contact puts the pole `−1/x` off the closed counterflow hull at
`s`.** -/
theorem pole_of_mem_noContactX {ω : Ω} {η ηe : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace (fun u => c.W u ω) ⊤ η) (hc : Continuous fun u => c.W u ω) (h0 : c.W 0 ω = 0)
    (hs : (c.s : ℝ≥0∞) < c.ζ ω) (hηe : IsGeneratingTrace (fun u => schedW c r l a u ω) ⊤ ηe)
    (hce : Continuous fun u => schedW c r l a u ω) (h0e : schedW c r l a 0 ω = 0)
    (hvis : 0 < rootPt r.1 → ∃ τ, (rootPt r.1 : ℂ) * η τ + 1 = 0) (hω : ω ∈ noContactX c r l a) :
    0 < rootPt r.1 → ((Sec5.CrossRestart.mobPole (rootPt r.1) 1 : ℝ) : ℂ) ∉
      closure (fwdHull (fun u : ℝ => c.W u.toNNReal ω) (c.s : ℝ)) := by
  intro hx
  obtain ⟨τ, hτ⟩ := hvis hx
  exact pole_notMem_closure_of_visit hη hc h0 hx (den_of_mem_noContactX c r l a hη hc h0 hs hηe hce h0e hω) hτ

/-- **No contact at the root `x` separates the closures of the translated explored hull and of the retained hull**,
given the counterflow's visit to `x` (when `x > 0`). -/
theorem disjoint_closure_of_mem_noContactX (hx0 : 0 ≤ rootPt r.1) {ω : Ω} {η ηe : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace (fun u => c.W u ω) ⊤ η) (hc : Continuous fun u => c.W u ω) (h0 : c.W 0 ω = 0)
    (hs : (c.s : ℝ≥0∞) < c.ζ ω) (hηe : IsGeneratingTrace (fun u => schedW c r l a u ω) ⊤ ηe)
    (hce : Continuous fun u => schedW c r l a u ω) (h0e : schedW c r l a 0 ω = 0)
    (hvis : 0 < rootPt r.1 → ∃ τ, (rootPt r.1 : ℂ) * η τ + 1 = 0) (hω : ω ∈ noContactX c r l a) :
    Disjoint (closure ((fun z : ℂ => z + (rootPt r.1 : ℝ)) ''
        fwdHull (fun u : ℝ => schedW c r l a u.toNNReal ω) (historyTime c r l : ℝ)))
      (closure (Supp8.Q3Rel.invHull (fun u : ℝ => c.W u.toNNReal ω) (c.s : ℝ))) := by
  set x := rootPt r.1 with hx
  have hUe : Continuous fun u : ℝ => schedW c r l a u.toNNReal ω := hce.comp continuous_real_toNNReal
  have hUe0 : (fun u : ℝ => schedW c r l a u.toNNReal ω) 0 = 0 := by simpa using h0e
  have hU : Continuous fun u : ℝ => c.W u.toNNReal ω := hc.comp continuous_real_toNNReal
  rcases (historyTime c r l).coe_nonneg.eq_or_lt with hT0 | hTpos
  · rw [← hT0, fwdHull_zero_eq_empty hUe hUe0, image_empty, closure_empty]
    exact Set.empty_disjoint _
  have hsep : Disjoint (η '' Icc 0 c.s)
      ((fun z : ℂ => -z⁻¹) '' ((fun t => ηe t + x) '' Icc 0 (historyTime c r l) \ {0})) := by
    rw [Set.disjoint_left]
    rintro _ ⟨t, ht, rfl⟩ ⟨_, ⟨⟨u, hu, rfl⟩, hu0⟩, he⟩
    have hne : ηe u + x ≠ 0 := hu0
    have h := (mem_noContactX_iff c r l a hη hc h0 hs hηe hce h0e).1 hω t ht u hu
    apply h
    rw [← he]
    field_simp
    ring
  have hseg : ∀ u ∈ Icc 0 c.s, ∀ y : ℝ, 0 < y → y ≤ x → η u ≠ -((y : ℂ))⁻¹ := by
    intro u hu y hy hyx
    rcases hx0.eq_or_lt with hxz | hxp
    · exact absurd (hyx.trans hxz.symm.le) (not_le.2 hy)
    · obtain ⟨τ, hτ⟩ := hvis hxp
      exact seg_of_visit hη hc h0 hxp (den_of_mem_noContactX c r l a hη hc h0 hs hηe hce h0e hω) hτ u hu.2 y hy hyx
  have hd := disjoint_closure_translated_hull_seg hη hc h0 hηe hce h0e (NNReal.coe_pos.1 hTpos) hx0 hseg hsep
  have e : fwdHull (fun t => Ito.rpath (fun u => schedW c r l a u ω) t + x) (historyTime c r l : ℝ) =
      (fun z : ℂ => z + (x : ℝ)) '' fwdHull (fun u : ℝ => schedW c r l a u.toNNReal ω) (historyTime c r l : ℝ) :=
    ConformalImageFull.fwdHull_add_const _ x _
  rw [e] at hd
  have hAH : fwdHull (Ito.rpath fun u => c.W u ω) (c.s : ℝ) ⊆ H := (isHPHull_fwdHull hU c.s.coe_nonneg).1
  have hAb : Bornology.IsBounded (fwdHull (Ito.rpath fun u => c.W u ω) (c.s : ℝ)) :=
    (isHPHull_fwdHull hU c.s.coe_nonneg).2.1
  exact disjoint_closure_negInv_swap hAH hAb hd

/-- **No contact at the root `x` is the datum's range condition**: the retained time `s` is before the counterflow's
first tip in the translated explored trace image. -/
theorem mem_noContactX_iff_lt_firstTipTime {ω : Ω} {η ηe : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace (fun u => c.W u ω) ⊤ η) (hc : Continuous fun u => c.W u ω) (h0 : c.W 0 ω = 0)
    (hs : (c.s : ℝ≥0∞) < c.ζ ω) (hηe : IsGeneratingTrace (fun u => schedW c r l a u ω) ⊤ ηe)
    (hce : Continuous fun u => schedW c r l a u ω) (h0e : schedW c r l a 0 ω = 0) :
    ω ∈ noContactX c r l a ↔ (c.s : ℝ≥0∞) < firstTipTime infinitySourceChart (fun u => c.W u ω)
      ((fun z : ℂ => (rootPt r.1 : ℂ) + z) '' (ηe '' Icc 0 (historyTime c r l))) := by
  have hηec : Continuous ηe := continuousOn_univ.1 (hηe.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  rw [mem_noContactX_iff c r l a hη hc h0 hs hηe hce h0e]
  constructor
  · intro h
    refine lt_firstTipTime_of_noContact hη hc h0
      ((isCompact_Icc.image hηec).image (continuous_const.add continuous_id)) fun t ht hγt hmem => ?_
    obtain ⟨_, ⟨u, hu, rfl⟩, hue⟩ := hmem
    refine h t ⟨zero_le, ht⟩ u hu ?_
    have hue' : (rootPt r.1 : ℂ) + ηe u = -(η t)⁻¹ := hue
    rw [hue', mul_neg, mul_inv_cancel₀ hγt]
    ring
  · intro h t ht u hu hzero
    have hγt : η t ≠ 0 := by
      intro h0'
      rw [h0', zero_mul, zero_add] at hzero
      exact one_ne_zero hzero
    refine noContact_of_lt_firstTipTime hη hc h0 h ht.2 hγt ⟨ηe u, ⟨u, hu, rfl⟩, ?_⟩
    have e : η t * ((rootPt r.1 : ℂ) + ηe u) = -1 := eq_neg_of_add_eq_zero_left hzero
    calc (rootPt r.1 : ℂ) + ηe u = (η t)⁻¹ * (η t * ((rootPt r.1 : ℂ) + ηe u)) := by field_simp
      _ = -(η t)⁻¹ := by rw [e]; ring

end InteractingSLE.Theorem14.GW2Xk
