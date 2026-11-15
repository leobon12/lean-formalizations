/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossRestartKernelDrv
import InteractingSLE.Spec.Exist.Determine

/-!
# Partial solution codes and their drivers

Packet PROVE-CFRESTART, field side (A): the σ-algebra bridge. The conditional independence hypothesis of the strip
setting concerns the **traces**; Proposition 3.7 with both stopped records needs it for each curve's **own record**
(driver, force points, lifetime). The record is read from the trace in two steps: before the lifetime the driver is
the Loewner driver of the trace (`CrossRestartKernelDrv`), and the lifetime is the first continuation-threshold time of
that driver's force word. This file builds the Borel object for the second step, on the code space
`Sec2.Assembly.XCode` of Theorem 2.2's assembly.

* `PDet a xL xR ρL ρR r`: the **partial solution codes of lifetime `r`** — `Good`, Theorem 2.2's countable pre-lifetime
  conditions `MSet` (integrated equations, ordering, integrability, null collision sets, and no threshold before the
  lifetime), canonical (`Canon`), driving path frozen after the lifetime (`FrozenB`), lifetime `r`. No maximality
  (`LimThr`) is asked: a solution truncated at a time before its lifetime is a partial code. Borel
  (`measurableSet_pDet`).
* `preClauses_of_mem_mSet`: the pre-lifetime clauses of Definition 2.1 for a code of `Good ∩ MSet` (the half of
  `Sec2.Assembly.isIntegratedSLEPath_iff_mem_mSet` that does not use `LimThr`).
* **`injOn_dOf_pDet`**: on partial codes the **driver code** (`Exist.Staged.dOf`: lifetime and driving code) determines
  the code — the driver determines the force points (`Exist.eqOn_of_force_eq`), the driving equation the Brownian path
  before the lifetime, freezing it after (the argument of `Exist.injOn_traceOfCode` with the driver given).
* **`measurableSet_dOf_image_pDet`**: hence (Lusin–Souslin) the set of driver codes of partial codes of lifetime `r` is
  Borel.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CrossRestart

open Sec2.Assembly Exist Exist.Staged

variable {nL nR : ℕ} {a : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- **The partial solution codes of lifetime `r`**: Theorem 2.2's countable pre-lifetime conditions, canonical, with
the driving path frozen after the lifetime; no maximality of the lifetime. -/
def PDet (a : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (r : ℝ≥0∞) :
    Set (XCode nL nR) :=
  {x | Good x ∧ x ∈ MSet a xL xR ρL ρR ∧ Canon xL xR x ∧ FrozenB x ∧ cζ x = r}

theorem measurableSet_pDet (a : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (r : ℝ≥0∞) : MeasurableSet (PDet a xL xR ρL ρR r) := by
  have e : PDet a xL xR ρL ρR r = {x : XCode nL nR | Good x} ∩ MSet a xL xR ρL ρR ∩
      {x | Canon xL xR x} ∩ {x | FrozenB x} ∩ {x | cζ x = r} := by
    ext x
    simp only [PDet, mem_ofPred_eq, mem_inter_iff, and_assoc]
  rw [e]
  exact (((measurableSet_good.inter (measurableSet_mSet a xL xR ρL ρR)).inter
    (measurableSet_setOfPred.2 (measurable_canon xL xR))).inter (measurableSet_setOfPred.2 measurable_frozenB)).inter
    (measurableSet_eq_fun measurable_cζ measurable_const)

/-- **The pre-lifetime clauses of Definition 2.1 for a code of `Good ∩ MSet`** (side ordering, integrability of the
gaps, the integrated equations, null collision sets, no threshold before the lifetime). -/
theorem preClauses_of_mem_mSet {x : XCode nL nR} (hx : Good x) (hm : x ∈ MSet a xL xR ρL ρR) :
    (∀ t : ℝ≥0, (t : ℝ≥0∞) < cζ x → ∀ i, cvL x i t ≤ cw x t) ∧
    (∀ t : ℝ≥0, (t : ℝ≥0∞) < cζ x → ∀ j, cw x t ≤ cvR x j t) ∧
    (∀ t : ℝ≥0, (t : ℝ≥0∞) < cζ x → ∀ i,
      IntervalIntegrable (fun s : ℝ => (cw x s.toNNReal - cvL x i s.toNNReal)⁻¹) volume 0 t) ∧
    (∀ t : ℝ≥0, (t : ℝ≥0∞) < cζ x → ∀ j,
      IntervalIntegrable (fun s : ℝ => (cw x s.toNNReal - cvR x j s.toNNReal)⁻¹) volume 0 t) ∧
    (∀ t : ℝ≥0, (t : ℝ≥0∞) < cζ x → defect a xL xR ρL ρR x t = 0) ∧
    (∀ i, volume {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < cζ x ∧ cw x s.toNNReal = cvL x i s.toNNReal} = 0) ∧
    (∀ j, volume {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < cζ x ∧ cw x s.toNNReal = cvR x j s.toNNReal} = 0) ∧
    ∀ t : ℝ≥0, (t : ℝ≥0∞) < cζ x →
      ¬ ForceWord.ThresholdCondition ρL ρR (cw x t) (fun i => cvL x i t) fun j => cvR x j t := by
  obtain ⟨-, hord, hint, hdef, hcL, hcR, hN, -⟩ := hm
  have hInt : ∀ t : ℝ≥0, (t : ℝ≥0∞) < cζ x → IntAt x t := fun t ht =>
    ⟨fun i => forall_lt_intervalIntegrable (fun n k hk => (hint n k hk).1 i) ht,
      fun j => forall_lt_intervalIntegrable (fun n k hk => (hint n k hk).2 j) ht⟩
  have hOrd : ∀ t : ℝ≥0, (t : ℝ≥0∞) < cζ x → stateAt x t ∈ ordSet := fun t ht =>
    forall_lt_of_forall_dyad hx.continuousOn_stateAt isClosed_ordSet hord ht
  have hprimL : ∀ (c : ℝ) (i : Fin nL), ContinuousOn
      (fun t : ℝ≥0 => ∫ s in (0 : ℝ)..t, c / (cw x s.toNNReal - cvL x i s.toNNReal))
      {t | (t : ℝ≥0∞) < cζ x} := fun c i =>
    continuousOn_primitive fun t ht => by
      simpa only [div_eq_mul_inv, gapL] using ((hInt t ht).1 i).const_mul c
  have hprimR : ∀ (c : ℝ) (j : Fin nR), ContinuousOn
      (fun t : ℝ≥0 => ∫ s in (0 : ℝ)..t, c / (cw x s.toNNReal - cvR x j s.toNNReal))
      {t | (t : ℝ≥0∞) < cζ x} := fun c j =>
    continuousOn_primitive fun t ht => by
      simpa only [div_eq_mul_inv, gapR] using ((hInt t ht).2 j).const_mul c
  have hfL : ∀ i : Fin nL, ContinuousOn
      (fun t : ℝ≥0 => ∫ s in (0 : ℝ)..t, 2 / (cvL x i s.toNNReal - cw x s.toNNReal))
      {t | (t : ℝ≥0∞) < cζ x} := fun i =>
    continuousOn_primitive fun t ht => by
      simpa only [Sec2.two_div_sub_eq, gapL] using ((hInt t ht).1 i).const_mul (-2)
  have hfR : ∀ j : Fin nR, ContinuousOn
      (fun t : ℝ≥0 => ∫ s in (0 : ℝ)..t, 2 / (cvR x j s.toNNReal - cw x s.toNNReal))
      {t | (t : ℝ≥0∞) < cζ x} := fun j =>
    continuousOn_primitive fun t ht => by
      simpa only [Sec2.two_div_sub_eq, gapR] using ((hInt t ht).2 j).const_mul (-2)
  have hdefc : ContinuousOn (defect a xL xR ρL ρR x) {t | (t : ℝ≥0∞) < cζ x} := by
    unfold defect
    refine (hx.continuousOn_w.sub ((continuousOn_const.mul hx.continuous_b.continuousOn).add
      (continuousOn_finsetSum _ fun i _ => hprimL (ρL i) i) |>.add
      (continuousOn_finsetSum _ fun j _ => hprimR (ρR j) j))).prodMk
      ((continuousOn_pi.2 fun i => (hx.continuousOn_vL i).sub
        (continuousOn_const.add (hfL i))).prodMk
      (continuousOn_pi.2 fun j => (hx.continuousOn_vR j).sub
        (continuousOn_const.add (hfR j))))
  have hEq : ∀ t : ℝ≥0, (t : ℝ≥0∞) < cζ x → defect a xL xR ρL ρR x t = 0 := fun t ht =>
    forall_lt_of_forall_dyad hdefc isClosed_singleton hdef ht
  exact ⟨fun t ht => (hOrd t ht).2.1, fun t ht => (hOrd t ht).2.2.1, fun t ht => (hInt t ht).1,
    fun t ht => (hInt t ht).2, hEq, hcL, hcR, fun t ht => (not_threshold_iff_nThr hx).2 hN t ht⟩

/-- **On partial codes the driver code determines the code** (the argument of `Exist.injOn_traceOfCode` with the
driver given instead of read from the trace). -/
theorem injOn_dOf_pDet (ha : 0 < a) (r : ℝ≥0∞) :
    InjOn (dOf (nL := nL) (nR := nR)) (PDet a xL xR ρL ρR r) := by
  intro x hx x' hx' he
  have hζ : cζ x = cζ x' := by
    have h1 : (dOf x).1 = (dOf x').1 := by rw [he]
    exact h1
  have hcode : x.2.2.1 = x'.2.2.1 := by
    have h1 : (dOf x).2 = (dOf x').2 := by rw [he]
    exact h1
  have hw : ∀ t : ℝ≥0, (t : ℝ≥0∞) < cζ x → cw x t = cw x' t := fun t _ => by
    show dec x.2.2.1 t = dec x'.2.2.1 t
    rw [hcode]
  obtain ⟨hg, hm, hc, hfz, -⟩ := hx
  obtain ⟨hg', hm', hc', hfz', -⟩ := hx'
  obtain ⟨hvLw, hwvR, hintL, hintR, hdef, hnullL, hnullR, -⟩ := preClauses_of_mem_mSet hg hm
  obtain ⟨hvLw', hwvR', hintL', hintR', hdef', hnullL', hnullR', -⟩ := preClauses_of_mem_mSet hg' hm'
  have hweq : ∀ t : ℝ≥0, (t : ℝ≥0∞) < cζ x → _ := fun t ht => (defect_eq_zero_iff.1 (hdef t ht)).1
  have hvLeq : ∀ t : ℝ≥0, (t : ℝ≥0∞) < cζ x → _ := fun t ht => (defect_eq_zero_iff.1 (hdef t ht)).2.1
  have hvReq : ∀ t : ℝ≥0, (t : ℝ≥0∞) < cζ x → _ := fun t ht => (defect_eq_zero_iff.1 (hdef t ht)).2.2
  have hweq' : ∀ t : ℝ≥0, (t : ℝ≥0∞) < cζ x' → _ := fun t ht => (defect_eq_zero_iff.1 (hdef' t ht)).1
  have hvLeq' : ∀ t : ℝ≥0, (t : ℝ≥0∞) < cζ x' → _ := fun t ht => (defect_eq_zero_iff.1 (hdef' t ht)).2.1
  have hvReq' : ∀ t : ℝ≥0, (t : ℝ≥0∞) < cζ x' → _ := fun t ht => (defect_eq_zero_iff.1 (hdef' t ht)).2.2
  have mI := fun {t : ℝ≥0} (ht : (t : ℝ≥0∞) < cζ x) {s : ℝ} (hs : s ∈ uIcc (0 : ℝ) t) =>
    toNNReal_lt_of_mem_uIcc ht hs
  have mO := fun {t : ℝ≥0} (ht : (t : ℝ≥0∞) < cζ x) {s : ℝ} (hs : s ∈ uIoc (0 : ℝ) t) =>
    toNNReal_lt_of_mem_uIcc ht (uIoc_subset_uIcc hs)
  -- the force points
  have hR : ∀ t : ℝ≥0, (t : ℝ≥0∞) < cζ x → ∀ j, cvR x j t = cvR x' j t := by
    intro t ht j
    refine eqOn_of_force_eq (w := cw x) (T := cζ x) (x₀ := xR j)
      (fun t ht => Or.inl ⟨hwvR t ht j, by rw [hw t ht]; exact hwvR' t (hζ ▸ ht) j⟩)
      (fun t ht => hintR t ht j)
      (fun t ht => (hintR' t (hζ ▸ ht) j).congr fun s hs => by
        rw [hw _ (mO ht hs)])
      (fun t ht => hvReq t ht j)
      (fun t ht => by
        rw [hvReq' t (hζ ▸ ht) j]
        congr 1
        exact intervalIntegral.integral_congr fun s hs => by
          rw [hw _ (mI ht hs)])
      (hnullR j) ?_ t ht
    have e : {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < cζ x ∧ cw x s.toNNReal = cvR x' j s.toNNReal} =
        {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < cζ x' ∧ cw x' s.toNNReal = cvR x' j s.toNNReal} := by
      ext s
      simp only [mem_ofPred_eq]
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨h1, hζ ▸ h2, by rw [← hw _ h2]; exact h3⟩
      · rintro ⟨h1, h2, h3⟩
        have h2' : (s.toNNReal : ℝ≥0∞) < cζ x := hζ ▸ h2
        exact ⟨h1, h2', by rw [hw _ h2']; exact h3⟩
    rw [e]
    exact hnullR' j
  have hL : ∀ t : ℝ≥0, (t : ℝ≥0∞) < cζ x → ∀ i, cvL x i t = cvL x' i t := by
    intro t ht i
    refine eqOn_of_force_eq (w := cw x) (T := cζ x) (x₀ := xL i)
      (fun t ht => Or.inr ⟨hvLw t ht i, by rw [hw t ht]; exact hvLw' t (hζ ▸ ht) i⟩)
      (fun t ht => hintL t ht i)
      (fun t ht => (hintL' t (hζ ▸ ht) i).congr fun s hs => by
        rw [hw _ (mO ht hs)])
      (fun t ht => hvLeq t ht i)
      (fun t ht => by
        rw [hvLeq' t (hζ ▸ ht) i]
        congr 1
        exact intervalIntegral.integral_congr fun s hs => by
          rw [hw _ (mI ht hs)])
      (hnullL i) ?_ t ht
    have e : {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < cζ x ∧ cw x s.toNNReal = cvL x' i s.toNNReal} =
        {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < cζ x' ∧ cw x' s.toNNReal = cvL x' i s.toNNReal} := by
      ext s
      simp only [mem_ofPred_eq]
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨h1, hζ ▸ h2, by rw [← hw _ h2]; exact h3⟩
      · rintro ⟨h1, h2, h3⟩
        have h2' : (s.toNNReal : ℝ≥0∞) < cζ x := hζ ▸ h2
        exact ⟨h1, h2', by rw [hw _ h2']; exact h3⟩
    rw [e]
    exact hnullL' i
  -- the driving path before the lifetime
  have hb : ∀ t : ℝ≥0, (t : ℝ≥0∞) < cζ x → cb x t = cb x' t := by
    intro t ht
    have e1 := hweq t ht
    have e2 := hweq' t (hζ ▸ ht)
    have hsL : ∀ i, ∫ s in (0 : ℝ)..t, ρL i / (cw x s.toNNReal - cvL x i s.toNNReal) =
        ∫ s in (0 : ℝ)..t, ρL i / (cw x' s.toNNReal - cvL x' i s.toNNReal) := fun i =>
      intervalIntegral.integral_congr fun s hs => by
        rw [hw _ (mI ht hs), hL _ (mI ht hs) i]
    have hsR : ∀ j, ∫ s in (0 : ℝ)..t, ρR j / (cw x s.toNNReal - cvR x j s.toNNReal) =
        ∫ s in (0 : ℝ)..t, ρR j / (cw x' s.toNNReal - cvR x' j s.toNNReal) := fun j =>
      intervalIntegral.integral_congr fun s hs => by
        rw [hw _ (mI ht hs), hR _ (mI ht hs) j]
    rw [hw t ht, Finset.sum_congr rfl fun i _ => hsL i, Finset.sum_congr rfl fun j _ => hsR j] at e1
    have hsa : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
    have : Real.sqrt a * cb x t = Real.sqrt a * cb x' t := by linarith
    exact mul_left_cancel₀ hsa.ne' this
  -- the driving code
  have hb1 : x.1 = x'.1 := by
    funext n k
    by_cases hlt : (dyad n k : ℝ≥0∞) < cζ x
    · have hN : dyad n k ≤ ((⌈dyad n k⌉₊ : ℕ) : ℝ≥0) := Nat.le_ceil _
      rw [← (hg.1 _).dec_dyad hN, ← (hg'.1 _).dec_dyad hN]
      exact hb _ hlt
    · rw [hfz n k hlt, hfz' n k (hζ ▸ hlt), ← hζ]
      by_cases h0 : cζ x = 0
      · simp only [h0, ↓reduceIte]
      · simp only [h0, ↓reduceIte]
        have hfin : cζ x ≠ ⊤ := fun h => hlt (h ▸ ENNReal.coe_lt_top)
        have hpos : 0 < (cζ x).toNNReal := ENNReal.toNNReal_pos h0 hfin
        have : (𝓝[<] (cζ x).toNNReal).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hpos⟩
        have h1 := (hg.continuous_b.tendsto (cζ x).toNNReal).mono_left
          (nhdsWithin_le_nhds (s := Iio (cζ x).toNNReal))
        have h2 := (hg'.continuous_b.tendsto (cζ x).toNNReal).mono_left
          (nhdsWithin_le_nhds (s := Iio (cζ x).toNNReal))
        refine tendsto_nhds_unique h1 (h2.congr' ?_)
        filter_upwards [self_mem_nhdsWithin] with s hs
        refine (hb s ?_).symm
        rw [← ENNReal.coe_toNNReal hfin]
        exact ENNReal.coe_lt_coe.2 hs
  exact code_eq hg hg' hc hc' hb1 hζ hw hL hR

theorem measurable_dOf : Measurable (dOf (nL := nL) (nR := nR)) :=
  measurable_cζ.prodMk measurable_code_w

/-- **The driver codes of partial codes of lifetime `r` form a Borel set** (Lusin–Souslin). -/
theorem measurableSet_dOf_image_pDet (ha : 0 < a) (r : ℝ≥0∞) :
    MeasurableSet (dOf '' PDet a xL xR ρL ρR r) :=
  (measurableSet_pDet a xL xR ρL ρR r).image_of_measurable_injOn measurable_dOf (injOn_dOf_pDet ha r)

end InteractingSLE.Sec5.CrossRestart
