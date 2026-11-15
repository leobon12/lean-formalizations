/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossRestartKernelLife

/-!
# Driver codes that agree on a prefix of their traces

Packet PROVE-CFRESTART, the σ-algebra bridge of (A). PROVE-STAGED's `Exist.Staged.fwdHull_eq_of_dTrace_eq`,
`dec_eq_of_dTrace_eq` compare two good driver codes with **equal** trace codes (same lifetime). Reading a flow line's
record from its trace compares the driver code read from the trace at a horizon `r` (the trace may be junk after the
true lifetime `ζ`) with the true driver's code, whose trace values agree with it only at the dyadic times before
`min(r, ζ)`. The prefix versions (same arguments, the agreement asked only below `t₀`):

* `fwdHull_eq_of_traceAt_eq_prefix`: equal hulls before `t₀`;
* **`dec_eq_of_traceAt_eq_prefix`**: equal drivers before `t₀`.

The lifetime test: `trCodeOf η r` (the trace code read from a path `η` at the horizon `r`), the Borel event
**`LivesPast a xL xR ρL ρR η r`** ("the driver read from `η` up to `r` is a good driver code with this trace code and is
the driver of a partial solution of lifetime `r`"), and, for an integrated `SLE_a(ρ)` path `(w, vL, vR, b, ζ)`:

* `force_eq_of_cw_eq`: a partial code whose driver agrees with `w` before `T ≤ ζ` has the force points `vL`, `vR`
  before `T` (`Exist.eqOn_of_force_eq`);
* **`le_and_agree_of_mem_pDet`**: a partial code of lifetime `r > 0` whose driver agrees with `w` before `min r ζ` does
  not outlive the path (`r ≤ ζ`): otherwise its state at `ζ` would be a continuous left limit of the path's state,
  hence a threshold state by the maximality of `ζ`, while partial codes do not reach the threshold before their
  lifetime;
* `exists_of_livesPast`: the partial code read from a generating trace `η` at a horizon `r` has the driver `w` before
  `min r ζ` (junk of `η` after `ζ` does not matter: the prefix lemmas);
* **`le_of_livesPast`**: if the event holds at a horizon `r > 0`, then `r ≤ ζ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

open QuantumZipper (H)

namespace InteractingSLE.Sec5.CrossRestart

open Sec2.Assembly Exist Exist.Staged

variable {z z' : DCode}

/-- **Driver codes whose trace values agree before `t₀` have the same hulls before `t₀`.** -/
theorem fwdHull_eq_of_traceAt_eq_prefix (hz : z ∈ DSet) (hz' : z' ∈ DSet) {t₀ : ℝ≥0∞} (ht₀ : t₀ ≤ z.1)
    (ht₀' : t₀ ≤ z'.1)
    (hval : ∀ n k, (dyad n k : ℝ≥0∞) < t₀ → LP.traceAt (dyad n k) (dec z.2) = LP.traceAt (dyad n k) (dec z'.2))
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < t₀) :
    QuantumZipper.fwdHull (fun s : ℝ => dec z.2 s.toNNReal) t =
      QuantumZipper.fwdHull (fun s : ℝ => dec z'.2 s.toNNReal) t := by
  obtain ⟨n, k, htd, hdt₀⟩ := exists_dyad_btwn ht
  have hdζ : (dyad n k : ℝ≥0∞) < z.1 := lt_of_lt_of_le hdt₀ ht₀
  have hdζ' : (dyad n k : ℝ≥0∞) < z'.1 := lt_of_lt_of_le hdt₀ ht₀'
  obtain ⟨η, hη⟩ := exists_isGeneratingTrace_of_mem_DSet hz hdζ
  obtain ⟨η', hη'⟩ := exists_isGeneratingTrace_of_mem_DSet hz' hdζ'
  have hc : ∀ {y : DCode}, y ∈ DSet → (dyad n k : ℝ≥0∞) < y.1 →
      ContinuousOn (dec y.2) {s : ℝ≥0 | (s : ℝ≥0∞) < ((dyad n k : ℝ≥0) : ℝ≥0∞)} := fun hy hy' =>
    (continuousOn_of_mem_DSet hy).mono fun s hs => lt_trans hs hy'
  have h0 : ∀ {y : DCode}, y ∈ DSet → (dyad n k : ℝ≥0∞) < y.1 → dec y.2 0 = 0 := fun hy hy' =>
    dec_zero_of_mem_DSet hy (lt_of_le_of_lt zero_le hy')
  have hvalη : ∀ m j, dyad m j < dyad n k → η (dyad m j) = η' (dyad m j) := fun m j hmj => by
    have hmj' : ((dyad m j : ℝ≥0) : ℝ≥0∞) < ((dyad n k : ℝ≥0) : ℝ≥0∞) := ENNReal.coe_lt_coe.2 hmj
    rw [← LP.traceAt_eq_of_isGeneratingTrace hη (hc hz hdζ) (h0 hz hdζ) hmj',
      ← LP.traceAt_eq_of_isGeneratingTrace hη' (hc hz' hdζ') (h0 hz' hdζ') hmj']
    exact hval m j (lt_trans hmj' hdt₀)
  have heqη : ∀ s : ℝ≥0, s < dyad n k → η s = η' s := fun s hs => by
    have hu : Tendsto (fun m => dyad m (flr m s)) atTop
        (𝓝[{u : ℝ≥0 | (u : ℝ≥0∞) ≤ ((dyad n k : ℝ≥0) : ℝ≥0∞)}] s) :=
      tendsto_nhdsWithin_iff.2 ⟨tendsto_dyad_flr s, Eventually.of_forall fun m =>
        ENNReal.coe_le_coe.2 ((dyad_flr_le m s).trans hs.le)⟩
    have hs' : s ∈ {u : ℝ≥0 | (u : ℝ≥0∞) ≤ ((dyad n k : ℝ≥0) : ℝ≥0∞)} := ENNReal.coe_le_coe.2 hs.le
    have h1 := ((hη.2.1 s hs').tendsto).comp hu
    have h2 := ((hη'.2.1 s hs').tendsto).comp hu
    refine tendsto_nhds_unique h1 (h2.congr fun m => ?_)
    exact (hvalη m (flr m s) ((dyad_flr_le m s).trans_lt hs)).symm
  have htT : t < dyad n k := by exact_mod_cast htd
  have himg : η '' Icc 0 t = η' '' Icc 0 t :=
    image_congr fun s hs => heqη s (lt_of_le_of_lt hs.2 htT)
  have htT' : (t : ℝ≥0∞) < ((dyad n k : ℝ≥0) : ℝ≥0∞) := ENNReal.coe_lt_coe.2 htT
  have hA : IsCompact (η '' Icc 0 t) := isCompact_Icc.image_of_continuousOn
    (hη.2.1.mono fun s hs => ENNReal.coe_le_coe.2 (hs.2.trans htT.le))
  have hF := (isFilling_iff_inter_H_eq_fillH hA.isBounded hA.isClosed).1 (hη.2.2 t htT')
  have hF' := (isFilling_iff_inter_H_eq_fillH hA.isBounded hA.isClosed).1 (himg ▸ hη'.2.2 t htT')
  calc QuantumZipper.fwdHull (fun s : ℝ => dec z.2 s.toNNReal) t
      = QuantumZipper.fwdHull (fun s : ℝ => dec z.2 s.toNNReal) t ∩ H :=
        (inter_eq_left.2 (fwdHull_subset_H t.2)).symm
    _ = QuantumZipper.fwdHull (fun s : ℝ => dec z'.2 s.toNNReal) t ∩ H := by rw [hF, hF']
    _ = _ := inter_eq_left.2 (fwdHull_subset_H t.2)

/-- **Driver codes whose trace values agree before `t₀` have the same driver before `t₀`.** -/
theorem dec_eq_of_traceAt_eq_prefix (hz : z ∈ DSet) (hz' : z' ∈ DSet) {t₀ : ℝ≥0∞} (ht₀ : t₀ ≤ z.1)
    (ht₀' : t₀ ≤ z'.1)
    (hval : ∀ n k, (dyad n k : ℝ≥0∞) < t₀ → LP.traceAt (dyad n k) (dec z.2) = LP.traceAt (dyad n k) (dec z'.2))
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < t₀) : dec z.2 t = dec z'.2 t := by
  obtain ⟨n, k, htd, hdt₀⟩ := exists_dyad_btwn ht
  have hdζ : (dyad n k : ℝ≥0∞) < z.1 := lt_of_lt_of_le hdt₀ ht₀
  have hdζ' : (dyad n k : ℝ≥0∞) < z'.1 := lt_of_lt_of_le hdt₀ ht₀'
  set T : ℝ := ((dyad n k : ℝ≥0) : ℝ) with hT
  have hT0 : 0 ≤ T := (dyad n k).2
  have hcont : ∀ {y : DCode}, y ∈ DSet → (dyad n k : ℝ≥0∞) < y.1 →
      ContinuousOn (fun s : ℝ => dec y.2 s.toNNReal) (Icc 0 T) := fun hy hy' => by
    refine (continuousOn_of_mem_DSet hy).comp continuous_real_toNNReal.continuousOn fun s hs => ?_
    refine lt_of_le_of_lt (ENNReal.coe_le_coe.2 ?_) hy'
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs.1]
    exact hs.2
  set Wc := Ito.clampDrv (fun s : ℝ => dec z.2 s.toNNReal) T with hWc
  set Wc' := Ito.clampDrv (fun s : ℝ => dec z'.2 s.toNNReal) T with hWc'
  have hWcc : Continuous Wc := Ito.continuous_clampDrv hT0 (hcont hz hdζ)
  have hWcc' : Continuous Wc' := Ito.continuous_clampDrv hT0 (hcont hz' hdζ')
  have hpos : 0 < z.1 := lt_of_le_of_lt zero_le hdζ
  have hpos' : 0 < z'.1 := lt_of_le_of_lt zero_le hdζ'
  have hW0 : Wc 0 = 0 := by
    rw [hWc, Ito.clampDrv_eqOn ⟨le_rfl, hT0⟩]; simpa using dec_zero_of_mem_DSet hz hpos
  have hW0' : Wc' 0 = 0 := by
    rw [hWc', Ito.clampDrv_eqOn ⟨le_rfl, hT0⟩]; simpa using dec_zero_of_mem_DSet hz' hpos'
  have htT : (t : ℝ) < T := by exact_mod_cast htd
  have hhull : ∀ s ∈ Icc (0 : ℝ) t, QuantumZipper.fwdHull Wc s = QuantumZipper.fwdHull Wc' s := by
    intro s hs
    have hsT : s < T := lt_of_le_of_lt hs.2 htT
    rw [fwdHull_eq_of_eqOn hs.1 hsT fun r hr => Ito.clampDrv_eqOn hr,
      fwdHull_eq_of_eqOn (W := Wc') hs.1 hsT fun r hr => Ito.clampDrv_eqOn hr]
    have hst₀ : ((s.toNNReal : ℝ≥0) : ℝ≥0∞) < t₀ := by
      refine lt_of_le_of_lt (ENNReal.coe_le_coe.2 ?_) ht
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs.1]
      exact hs.2
    have h := fwdHull_eq_of_traceAt_eq_prefix hz hz' ht₀ ht₀' hval hst₀
    rwa [Real.coe_toNNReal _ hs.1] at h
  have heq := Sec6.eqOn_of_fwdHull_eq hWcc hWcc' hW0 hW0' t.2 hhull ⟨t.2, le_rfl⟩
  rw [hWc, hWc', Ito.clampDrv_eqOn ⟨t.2, htT.le⟩, Ito.clampDrv_eqOn ⟨t.2, htT.le⟩] at heq
  simpa using heq

/-! ### The lifetime test -/

/-- **The trace code read from a path at the horizon `r`**: the values at the dyadic times before `r`. -/
def trCodeOf (η : ℝ≥0 → ℂ) (r : ℝ≥0) : ℝ≥0∞ × (ℕ → ℕ → ℂ) :=
  ((r : ℝ≥0∞), fun n k => if (dyad n k : ℝ≥0∞) < r then η (dyad n k) else 0)

theorem measurable_trCodeOf (r : ℝ≥0) : Measurable fun η : ℝ≥0 → ℂ => trCodeOf η r := by
  refine measurable_const.prodMk (measurable_pi_iff.2 fun n => measurable_pi_iff.2 fun k => ?_)
  by_cases h : (dyad n k : ℝ≥0∞) < r
  · simp only [h, ↓reduceIte]
    exact measurable_pi_apply _
  · simp only [h, ↓reduceIte]
    exact measurable_const

variable {nL nR : ℕ}

/-- **The force word read from the path `η` survives past the horizon `r`**: the driver code read from `η` at `r`
(PROVE-STAGED's Borel inverse `dInv` of the trace code) is a good driver code with this trace code, and it is the
driver code of a partial solution code of lifetime `r`. -/
def LivesPast (a : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (η : ℝ≥0 → ℂ)
    (r : ℝ≥0) : Prop :=
  dInv (trCodeOf η r) ∈ DSet ∧ dTrace (dInv (trCodeOf η r)) = trCodeOf η r ∧
    dInv (trCodeOf η r) ∈ dOf '' PDet a xL xR ρL ρR r

theorem measurableSet_livesPast {a : ℝ} (ha : 0 < a) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ) (r : ℝ≥0) : MeasurableSet {η : ℝ≥0 → ℂ | LivesPast a xL xR ρL ρR η r} := by
  have hz : Measurable fun η : ℝ≥0 → ℂ => dInv (trCodeOf η r) := measurable_dInv.comp (measurable_trCodeOf r)
  exact (hz measurableSet_DSet).inter ((measurableSet_eq_fun (measurable_dTrace.comp hz)
    (measurable_trCodeOf r)).inter (hz (measurableSet_dOf_image_pDet (xL := xL) (xR := xR) (ρL := ρL) (ρR := ρR)
      ha r)))

variable {a : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {η : ℝ≥0 → ℂ}

/-- **The force points of a partial code agree with the path's while the drivers agree.** -/
theorem force_eq_of_cw_eq (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) {x : XCode nL nR} (hg : Good x)
    (hm : x ∈ MSet a xL xR ρL ρR) {T : ℝ≥0∞} (hTζ : T ≤ ζ) (hTx : T ≤ cζ x)
    (hcw : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T → cw x t = w t) :
    ∀ t : ℝ≥0, (t : ℝ≥0∞) < T → (∀ i, cvL x i t = vL i t) ∧ ∀ j, cvR x j t = vR j t := by
  obtain ⟨-, -, -, -, -, -, -, hvLw, hwvR, -, hintL, hintR, -, hvLeq, hvReq, hnullL, hnullR, -, -, -⟩ := hp
  obtain ⟨xvLw, xwvR, xintL, xintR, xdef, xnullL, xnullR, -⟩ := preClauses_of_mem_mSet hg hm
  have hζ' : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < T → (t : ℝ≥0∞) < ζ := fun ht => lt_of_lt_of_le ht hTζ
  have hx' : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < T → (t : ℝ≥0∞) < cζ x := fun ht => lt_of_lt_of_le ht hTx
  have mI := fun {t : ℝ≥0} (ht : (t : ℝ≥0∞) < T) {s : ℝ} (hs : s ∈ uIcc (0 : ℝ) t) =>
    toNNReal_lt_of_mem_uIcc ht hs
  have mO := fun {t : ℝ≥0} (ht : (t : ℝ≥0∞) < T) {s : ℝ} (hs : s ∈ uIoc (0 : ℝ) t) =>
    toNNReal_lt_of_mem_uIcc ht (uIoc_subset_uIcc hs)
  have hnT : ∀ {g : ℝ≥0 → ℝ}, volume {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < ζ ∧ w s.toNNReal = g s.toNNReal}
      = 0 → volume {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < T ∧ w s.toNNReal = g s.toNNReal} = 0 := by
    intro g h
    refine measure_mono_null (fun s hs => ?_) h
    exact ⟨hs.1, hζ' hs.2.1, hs.2.2⟩
  have hxn : ∀ {g : ℝ≥0 → ℝ}, volume {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < cζ x ∧
      cw x s.toNNReal = g s.toNNReal} = 0 →
      volume {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < T ∧ w s.toNNReal = g s.toNNReal} = 0 := by
    intro g h
    refine measure_mono_null (fun s hs => ?_) h
    exact ⟨hs.1, hx' hs.2.1, by rw [hcw _ hs.2.1]; exact hs.2.2⟩
  intro t ht
  refine ⟨fun i => ?_, fun j => ?_⟩
  · refine eqOn_of_force_eq (w := w) (T := T) (x₀ := xL i)
      (fun t ht => Or.inr ⟨by rw [← hcw t ht]; exact xvLw t (hx' ht) i, hvLw t (hζ' ht) i⟩)
      (fun t ht => (xintL t (hx' ht) i).congr fun s hs => by rw [hcw _ (mO ht hs)])
      (fun t ht => hintL t (hζ' ht) i)
      (fun t ht => by
        rw [(defect_eq_zero_iff.1 (xdef t (hx' ht))).2.1 i]
        congr 1
        exact intervalIntegral.integral_congr fun s hs => by rw [hcw _ (mI ht hs)])
      (fun t ht => hvLeq t (hζ' ht) i) (hxn (xnullL i)) (hnT (hnullL i)) t ht
  · refine eqOn_of_force_eq (w := w) (T := T) (x₀ := xR j)
      (fun t ht => Or.inl ⟨by rw [← hcw t ht]; exact xwvR t (hx' ht) j, hwvR t (hζ' ht) j⟩)
      (fun t ht => (xintR t (hx' ht) j).congr fun s hs => by rw [hcw _ (mO ht hs)])
      (fun t ht => hintR t (hζ' ht) j)
      (fun t ht => by
        rw [(defect_eq_zero_iff.1 (xdef t (hx' ht))).2.2 j]
        congr 1
        exact intervalIntegral.integral_congr fun s hs => by rw [hcw _ (mI ht hs)])
      (fun t ht => hvReq t (hζ' ht) j) (hxn (xnullR j)) (hnT (hnullR j)) t ht

/-- **A partial code whose driver agrees with the path's is the path, and does not outlive it.** If `x` is a partial
code of lifetime `r > 0` whose driver agrees with `w` before `min r ζ`, then `r ≤ ζ` and its force points agree with
`vL`, `vR` before `min r ζ`. (If `ζ < r`, the code's state at `ζ` is a continuous left limit of the path's state,
hence a threshold state by the maximality of `ζ`, while a partial code does not reach the threshold before its
lifetime.) -/
theorem le_and_agree_of_mem_pDet (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) {r : ℝ≥0} (hr : 0 < r)
    {x : XCode nL nR} (hx : x ∈ PDet a xL xR ρL ρR r)
    (hcw : ∀ t : ℝ≥0, (t : ℝ≥0∞) < min (r : ℝ≥0∞) ζ → cw x t = w t) :
    (r : ℝ≥0∞) ≤ ζ ∧ ∀ t : ℝ≥0, (t : ℝ≥0∞) < min (r : ℝ≥0∞) ζ →
      (∀ i, cvL x i t = vL i t) ∧ ∀ j, cvR x j t = vR j t := by
  obtain ⟨hg, hm, -, -, hxr⟩ := hx
  have hTx : min (r : ℝ≥0∞) ζ ≤ cζ x := hxr ▸ min_le_left _ _
  have hag := force_eq_of_cw_eq hp hg hm (min_le_right _ _) hTx hcw
  refine ⟨?_, hag⟩
  by_contra hlt
  push Not at hlt
  have hmin : min (r : ℝ≥0∞) ζ = ζ := min_eq_right hlt.le
  rw [hmin] at hcw hag
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hthr0, hthrT⟩ := hp
  obtain ⟨-, -, -, -, -, -, -, xthr⟩ := preClauses_of_mem_mSet hg hm
  rcases eq_or_ne ζ 0 with h0 | h0
  · have hthr := hthr0 h0
    have hx0 : (0 : ℝ≥0∞) < cζ x := by rw [hxr]; exact_mod_cast hr
    obtain ⟨⟨h0w, h0L, h0R⟩, -⟩ := hm
    apply xthr 0 hx0
    rw [h0w]
    have eL : (fun i => cvL x i 0) = xL := funext h0L
    have eR : (fun j => cvR x j 0) = xR := funext h0R
    rw [eL, eR]
    exact hthr
  · have hfin : ζ ≠ ⊤ := ne_top_of_lt hlt
    set T := ζ.toNNReal with hTdef
    have hTζ : (T : ℝ≥0∞) = ζ := ENNReal.coe_toNNReal hfin
    have hT0 : 0 < T := ENNReal.toNNReal_pos h0 hfin
    have hTx : (T : ℝ≥0∞) < cζ x := by rw [hTζ, hxr]; exact hlt
    have hcont : ContinuousAt (stateAt x) T := by
      have hopen : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < cζ x} := isOpen_lt ENNReal.continuous_coe continuous_const
      exact (hg.continuousOn_stateAt T hTx).continuousAt (hopen.mem_nhds hTx)
    have hlim : Tendsto (fun t => (w t, fun i => vL i t, fun j => vR j t)) (𝓝[<] T) (𝓝 (stateAt x T)) := by
      refine (hcont.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      have htζ : (t : ℝ≥0∞) < ζ := by rw [← hTζ]; exact ENNReal.coe_lt_coe.2 ht
      simp only [stateAt, hcw t htζ, Prod.mk.injEq, true_and]
      exact ⟨funext fun i => (hag t htζ).1 i, funext fun j => (hag t htζ).2 j⟩
    exact xthr T hTx (hthrT T hT0 hTζ _ _ _ hlim)

/-- **The partial code read from the trace at the horizon `r`** has the driver `w` before `min r ζ` (junk of `η` after
`ζ` does not matter: the prefix lemmas). -/
theorem exists_of_livesPast (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) (hη : IsGeneratingTrace w ζ η)
    {r : ℝ≥0} (hl : LivesPast a xL xR ρL ρR η r) :
    ∃ x ∈ PDet a xL xR ρL ρR r, dOf x = dInv (trCodeOf η r) ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < min (r : ℝ≥0∞) ζ → cw x t = w t := by
  obtain ⟨hzD, hzT, x, hx, hxz⟩ := hl
  set z := dInv (trCodeOf η r) with hzdef
  have hw0 := hp.1
  have hwc := hp.2.2.2.1
  have hk := killCode_mem_DSet hwc hw0 hη
  have hz1 : z.1 = r := congrArg Prod.fst hzT
  have hvalz : ∀ n k, (dyad n k : ℝ≥0∞) < r → LP.traceAt (dyad n k) (dec z.2) = η (dyad n k) := by
    intro n k hnk
    have h := congrFun (congrFun (congrArg Prod.snd hzT) n) k
    have hnk' : (dyad n k : ℝ≥0∞) < z.1 := hz1 ▸ hnk
    simp only [dTrace, trCodeOf, hnk, hnk', ↓reduceIte] at h
    exact h
  have hvalk : ∀ n k, (dyad n k : ℝ≥0∞) < ζ → LP.traceAt (dyad n k) (dec (killCode w ζ).2) = η (dyad n k) := by
    intro n k hnk
    have h := congrFun (congrFun (congrArg Prod.snd (dTrace_killCode hwc hw0 hη)) n) k
    have hnk' : (dyad n k : ℝ≥0∞) < (killCode w ζ).1 := hnk
    simp only [dTrace, hnk, hnk', ↓reduceIte] at h
    exact h
  refine ⟨x, hx, hxz, fun t ht => ?_⟩
  have hW : dec z.2 t = w t := by
    rw [dec_eq_of_traceAt_eq_prefix hzD hk (t₀ := min (r : ℝ≥0∞) ζ) (by rw [hz1]; exact min_le_left _ _)
      (min_le_right _ _) (fun n k hnk => by
        rw [hvalz n k (lt_of_lt_of_le hnk (min_le_left _ _)), hvalk n k (lt_of_lt_of_le hnk (min_le_right _ _))])
      ht]
    exact dec_killCode hwc (lt_of_lt_of_le ht (min_le_right _ _))
  have h2 : (dOf x).2 = z.2 := by rw [hxz]
  show dec x.2.2.1 t = w t
  rw [show x.2.2.1 = z.2 from h2]
  exact hW

/-- **The word read from the trace does not survive past the true lifetime.** -/
theorem le_of_livesPast (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) (hη : IsGeneratingTrace w ζ η)
    {r : ℝ≥0} (hr : 0 < r) (hl : LivesPast a xL xR ρL ρR η r) : (r : ℝ≥0∞) ≤ ζ := by
  obtain ⟨x, hx, -, hcw⟩ := exists_of_livesPast hp hη hl
  exact (le_and_agree_of_mem_pDet hp hr hx hcw).1

end InteractingSLE.Sec5.CrossRestart
