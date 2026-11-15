/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossRestartKernelLifeTest

/-!
# The lifetime and the record of an integrated path, read from its trace

Packet PROVE-CFRESTART, the σ-algebra bridge of (A). For an integrated `SLE_a(ρ)` path `(w, vL, vR, b, ζ)` (`a > 0`)
with generating trace `η` (arbitrary after `ζ`):

* `cutCode b w vL vR r`: the path **truncated at a horizon `r < ζ`** (state codes killed at `r`, driving path frozen
  at `r`); **`cutCode_mem_pDet`**: it is a partial code of lifetime `r` (`continuousOn_b`: the driving path is
  continuous before `ζ`, by the driving equation);
* **`livesPast_of_lt`**: the lifetime test `LivesPast` holds at every horizon `0 < r < ζ` (with `le_of_livesPast`:
  it fails at every horizon `r > ζ`);
* `lifeOf`, **`measurable_lifeOf`**, **`lifeOf_eq`**: the lifetime is a Borel function of the trace;
* `RecSet r A`, **`measurableSet_recSet`**, **`mem_recSet_iff`**: the generating events
  `{r < ζ, (w_r, vL_r, vR_r) ∈ A}` of the killed driving σ-algebra are Borel events of the trace.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CrossRestart

open Sec2.Assembly Exist Exist.Staged

variable {nL nR : ℕ} {a : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {η : ℝ≥0 → ℂ}

/-! ### The truncated code -/

/-- **The driving path of an integrated path is continuous before the lifetime** (`a > 0`; the driving equation). -/
theorem continuousOn_b (ha : 0 < a) (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) :
    ContinuousOn b {t : ℝ≥0 | (t : ℝ≥0∞) < ζ} := by
  obtain ⟨-, -, -, hwc, -, -, -, -, -, -, hintL, hintR, hweq, -⟩ := hp
  have hprimL : ∀ i, ContinuousOn (fun t : ℝ≥0 => ∫ s in (0 : ℝ)..t, ρL i / (w s.toNNReal - vL i s.toNNReal))
      {t | (t : ℝ≥0∞) < ζ} := fun i =>
    continuousOn_primitive fun t ht => by simpa only [div_eq_mul_inv] using (hintL t ht i).const_mul (ρL i)
  have hprimR : ∀ j, ContinuousOn (fun t : ℝ≥0 => ∫ s in (0 : ℝ)..t, ρR j / (w s.toNNReal - vR j s.toNNReal))
      {t | (t : ℝ≥0∞) < ζ} := fun j =>
    continuousOn_primitive fun t ht => by simpa only [div_eq_mul_inv] using (hintR t ht j).const_mul (ρR j)
  have hD : ContinuousOn (fun t : ℝ≥0 => (w t - ((∑ i, ∫ s in (0 : ℝ)..t, ρL i / (w s.toNNReal - vL i s.toNNReal))
      + (∑ j, ∫ s in (0 : ℝ)..t, ρR j / (w s.toNNReal - vR j s.toNNReal)))) / Real.sqrt a)
      {t | (t : ℝ≥0∞) < ζ} :=
    (hwc.sub ((continuousOn_finsetSum _ fun i _ => hprimL i).add
      (continuousOn_finsetSum _ fun j _ => hprimR j))).div_const _
  refine hD.congr fun t ht => ?_
  have hsa : Real.sqrt a ≠ 0 := (Real.sqrt_pos.2 ha).ne'
  dsimp only
  rw [hweq t ht, eq_div_iff hsa]
  ring

/-- The driving path frozen at the horizon `r`. -/
def cutB (b : ℝ≥0 → ℝ) (r : ℝ≥0) (t : ℝ≥0) : ℝ := b (min t r)

/-- **The truncated code** of a solution at the horizon `r`: the state codes killed at `r`, the driving path frozen
at `r`, lifetime `r`. -/
def cutCode (b w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) (r : ℝ≥0) : XCode nL nR :=
  (enc (cutB b r), (r : ℝ≥0∞), (killCode w r).2, fun i => (killCode (vL i) r).2, fun j => (killCode (vR j) r).2)

theorem continuous_cutB (ha : 0 < a) (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) {r : ℝ≥0}
    (hrζ : (r : ℝ≥0∞) < ζ) : Continuous (cutB b r) :=
  (continuousOn_b ha hp).comp_continuous (continuous_id.min continuous_const) fun _ =>
    lt_of_le_of_lt (ENNReal.coe_le_coe.2 (min_le_right _ _)) hrζ

/-- **The truncated code is a partial code of lifetime `r`** (`0 < r < ζ`). -/
theorem cutCode_mem_pDet (ha : 0 < a) (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) {r : ℝ≥0} (hr : 0 < r)
    (hrζ : (r : ℝ≥0∞) < ζ) : cutCode b w vL vR r ∈ PDet a xL xR ρL ρR r := by
  have hbc := continuous_cutB ha hp hrζ
  obtain ⟨hw0, hvL0, hvR0, hwc, hvLc, hvRc, hanti, hvLw, hwvR, hmono, hintL, hintR, hweq, hvLeq, hvReq, hnullL,
    hnullR, hnt, -, -⟩ := hp
  set x := cutCode b w vL vR r with hxdef
  have hsub : {t : ℝ≥0 | (t : ℝ≥0∞) < (r : ℝ≥0∞)} ⊆ {t : ℝ≥0 | (t : ℝ≥0∞) < ζ} := fun t ht => lt_trans ht hrζ
  have hwr := hwc.mono hsub
  have hLr := fun i => (hvLc i).mono hsub
  have hRr := fun j => (hvRc j).mono hsub
  have hdw : ∀ t : ℝ≥0, (t : ℝ≥0∞) < r → cw x t = w t := fun t ht => dec_killCode hwr ht
  have hdL : ∀ t : ℝ≥0, (t : ℝ≥0∞) < r → ∀ i, cvL x i t = vL i t := fun t ht i => dec_killCode (hLr i) ht
  have hdR : ∀ t : ℝ≥0, (t : ℝ≥0∞) < r → ∀ j, cvR x j t = vR j t := fun t ht j => dec_killCode (hRr j) ht
  have hcb : ∀ t : ℝ≥0, cb x t = cutB b r t := fun t => dec_enc hbc.continuousWithinAt
  have hstate : ∀ t : ℝ≥0, (t : ℝ≥0∞) < r → stateAt x t = (w t, fun i => vL i t, fun j => vR j t) := by
    intro t ht
    simp only [stateAt, hdw t ht, hdL t ht, hdR t ht]
  have hr0 : ((0 : ℝ≥0) : ℝ≥0∞) < r := by exact_mod_cast hr
  have hx0 : (r : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.2 hr.ne'
  have hgood : Good x := by
    refine ⟨fun T => uc_enc hbc.continuousOn, fun n k hd => ⟨?_, fun i => ?_, fun j => ?_⟩⟩
    · exact uc_enc (continuousOn_killDrv hwr hd)
    · exact uc_enc (continuousOn_killDrv (hLr i) hd)
    · exact uc_enc (continuousOn_killDrv (hRr j) hd)
  have mI : ∀ {t : ℝ≥0}, (t : ℝ≥0∞) < r → ∀ {s : ℝ}, s ∈ uIcc (0 : ℝ) t → (s.toNNReal : ℝ≥0∞) < r :=
    fun ht _ hs => toNNReal_lt_of_mem_uIcc ht hs
  refine ⟨hgood, ⟨⟨?_, fun i => ?_, fun j => ?_⟩, fun n k hk => ?_, fun n k hk => ?_, fun n k hk => ?_,
    fun i => ?_, fun j => ?_, ?_, fun h => absurd h hx0⟩, ?_, ?_, rfl⟩
  · rw [hdw 0 hr0]; exact hw0
  · rw [hdL 0 hr0 i]; exact hvL0 i
  · rw [hdR 0 hr0 j]; exact hvR0 j
  · -- the ordering
    have hk' : ((dyad n k : ℝ≥0) : ℝ≥0∞) < r := hk
    have hd := lt_trans hk' hrζ
    rw [hstate _ hk']
    exact ⟨fun i j hij => hanti _ hd hij, hvLw _ hd, hwvR _ hd, fun i j hij => hmono _ hd hij⟩
  · -- integrability of the gaps
    have hk' : ((dyad n k : ℝ≥0) : ℝ≥0∞) < r := hk
    have hd := lt_trans hk' hrζ
    refine ⟨fun i => (hintL _ hd i).congr fun s hs => ?_, fun j => (hintR _ hd j).congr fun s hs => ?_⟩
    · have h := mI hk' (uIoc_subset_uIcc hs)
      show _ = (cw x s.toNNReal - cvL x i s.toNNReal)⁻¹
      rw [hdw _ h, hdL _ h i]
    · have h := mI hk' (uIoc_subset_uIcc hs)
      show _ = (cw x s.toNNReal - cvR x j s.toNNReal)⁻¹
      rw [hdw _ h, hdR _ h j]
  · -- the integrated equations
    have hk' : ((dyad n k : ℝ≥0) : ℝ≥0∞) < r := hk
    have hd := lt_trans hk' hrζ
    refine defect_eq_zero_iff.2 ⟨?_, fun i => ?_, fun j => ?_⟩
    · have hsL : ∀ i, ∫ s in (0 : ℝ)..(dyad n k : ℝ≥0), ρL i / (cw x s.toNNReal - cvL x i s.toNNReal) =
          ∫ s in (0 : ℝ)..(dyad n k : ℝ≥0), ρL i / (w s.toNNReal - vL i s.toNNReal) := fun i =>
        intervalIntegral.integral_congr fun s hs => by rw [hdw _ (mI hk' hs), hdL _ (mI hk' hs) i]
      have hsR : ∀ j, ∫ s in (0 : ℝ)..(dyad n k : ℝ≥0), ρR j / (cw x s.toNNReal - cvR x j s.toNNReal) =
          ∫ s in (0 : ℝ)..(dyad n k : ℝ≥0), ρR j / (w s.toNNReal - vR j s.toNNReal) := fun j =>
        intervalIntegral.integral_congr fun s hs => by rw [hdw _ (mI hk' hs), hdR _ (mI hk' hs) j]
      have hbd : cb x (dyad n k) = b (dyad n k) := by
        rw [hcb, cutB, min_eq_left (ENNReal.coe_le_coe.1 hk'.le)]
      rw [Finset.sum_congr rfl fun i _ => hsL i, Finset.sum_congr rfl fun j _ => hsR j, hdw _ hk', hbd]
      exact hweq _ hd
    · rw [hdL _ hk' i, intervalIntegral.integral_congr fun s hs => by rw [hdw _ (mI hk' hs), hdL _ (mI hk' hs) i]]
      exact hvLeq _ hd i
    · rw [hdR _ hk' j, intervalIntegral.integral_congr fun s hs => by rw [hdw _ (mI hk' hs), hdR _ (mI hk' hs) j]]
      exact hvReq _ hd j
  · -- null collision sets
    refine measure_mono_null (fun s hs => ?_) (hnullL i)
    obtain ⟨h1, h2, h3⟩ := hs
    have h2' : (s.toNNReal : ℝ≥0∞) < r := h2
    exact ⟨h1, lt_trans h2' hrζ, by rw [← hdw _ h2', ← hdL _ h2' i]; exact h3⟩
  · refine measure_mono_null (fun s hs => ?_) (hnullR j)
    obtain ⟨h1, h2, h3⟩ := hs
    have h2' : (s.toNNReal : ℝ≥0∞) < r := h2
    exact ⟨h1, lt_trans h2' hrζ, by rw [← hdw _ h2', ← hdR _ h2' j]; exact h3⟩
  · -- no threshold before the horizon
    refine (not_threshold_iff_nThr hgood).1 fun t ht => ?_
    have ht' : (t : ℝ≥0∞) < r := ht
    simp only [hdw t ht', hdL t ht', hdR t ht']
    exact hnt t (lt_trans ht' hrζ)
  · -- canonical
    intro n k
    refine ⟨fun h0 => ?_, fun _ hlt => ?_⟩
    · have hlt : ((dyad n k : ℝ≥0) : ℝ≥0∞) < r := by rw [h0]; exact hr0
      refine ⟨?_, fun i => ?_, fun j => ?_⟩
      · show (if ((dyad n k : ℝ≥0) : ℝ≥0∞) < r then w (dyad n k) else 0) = 0
        simp only [hlt, ↓reduceIte]
        rw [h0]; exact hw0
      · show (if ((dyad n k : ℝ≥0) : ℝ≥0∞) < r then vL i (dyad n k) else 0) = xL i
        simp only [hlt, ↓reduceIte]
        rw [h0]; exact hvL0 i
      · show (if ((dyad n k : ℝ≥0) : ℝ≥0∞) < r then vR j (dyad n k) else 0) = xR j
        simp only [hlt, ↓reduceIte]
        rw [h0]; exact hvR0 j
    · have hlt' : ¬ ((dyad n k : ℝ≥0) : ℝ≥0∞) < r := hlt
      refine ⟨?_, fun i => ?_, fun j => ?_⟩
      · show (if ((dyad n k : ℝ≥0) : ℝ≥0∞) < r then w (dyad n k) else 0) = 0
        simp only [hlt', ↓reduceIte]
      · show (if ((dyad n k : ℝ≥0) : ℝ≥0∞) < r then vL i (dyad n k) else 0) = 0
        simp only [hlt', ↓reduceIte]
      · show (if ((dyad n k : ℝ≥0) : ℝ≥0∞) < r then vR j (dyad n k) else 0) = 0
        simp only [hlt', ↓reduceIte]
  · -- the driving path is frozen after the horizon
    intro n k hlt
    have hlt' : ¬ ((dyad n k : ℝ≥0) : ℝ≥0∞) < r := hlt
    have hle : r ≤ dyad n k := ENNReal.coe_le_coe.1 (not_lt.1 hlt')
    have hx0' : cζ x ≠ 0 := hx0
    simp only [hx0', ↓reduceIte]
    show cutB b r (dyad n k) = cb x (r : ℝ≥0∞).toNNReal
    rw [ENNReal.toNNReal_coe, hcb, cutB, cutB, min_eq_right hle, min_self]

/-- **The lifetime test holds at every horizon `0 < r < ζ`.** -/
theorem livesPast_of_lt (ha : 0 < a) (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ)
    (hη : IsGeneratingTrace w ζ η) {r : ℝ≥0} (hr : 0 < r) (hrζ : (r : ℝ≥0∞) < ζ) :
    LivesPast a xL xR ρL ρR η r := by
  have hwr : ContinuousOn w {t : ℝ≥0 | (t : ℝ≥0∞) < (r : ℝ≥0∞)} := hp.2.2.2.1.mono fun t ht => lt_trans ht hrζ
  have hηr : IsGeneratingTrace w (r : ℝ≥0∞) η := isGeneratingTrace_of_eqOn_of_lt hη (fun _ _ => rfl) hrζ
  have hk := killCode_mem_DSet hwr hp.1 hηr
  have htr : trCodeOf η r = dTrace (killCode w r) := (dTrace_killCode hwr hp.1 hηr).symm
  unfold LivesPast
  rw [htr, dInv_dTrace hk]
  exact ⟨hk, rfl, cutCode b w vL vR r, cutCode_mem_pDet ha hp hr hrζ, rfl⟩

/-! ### The lifetime read from the trace -/

/-- The event "the lifetime test holds at the positive dyadic horizon `dyad n k`". -/
def LiveSet (a : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (n k : ℕ) :
    Set (ℝ≥0 → ℂ) :=
  {η | 0 < dyad n k ∧ LivesPast a xL xR ρL ρR η (dyad n k)}

theorem measurableSet_liveSet (ha : 0 < a) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ) (n k : ℕ) : MeasurableSet (LiveSet a xL xR ρL ρR n k) :=
  (MeasurableSet.const _).inter (measurableSet_livesPast ha xL xR ρL ρR _)

/-- **The lifetime read from a path**: the supremum of the positive dyadic horizons passing the lifetime test. -/
def lifeOf (a : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (η : ℝ≥0 → ℂ) :
    ℝ≥0∞ :=
  ⨆ (n : ℕ) (k : ℕ), (LiveSet a xL xR ρL ρR n k).indicator (fun _ => ((dyad n k : ℝ≥0) : ℝ≥0∞)) η

theorem measurable_lifeOf (ha : 0 < a) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) :
    Measurable (lifeOf a xL xR ρL ρR) :=
  Measurable.iSup fun n => Measurable.iSup fun k =>
    measurable_const.indicator (measurableSet_liveSet ha xL xR ρL ρR n k)

/-- **The lifetime is read from the trace.** -/
theorem lifeOf_eq (ha : 0 < a) (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ)
    (hη : IsGeneratingTrace w ζ η) : lifeOf a xL xR ρL ρR η = ζ := by
  apply le_antisymm
  · refine iSup_le fun n => iSup_le fun k => ?_
    by_cases h : η ∈ LiveSet a xL xR ρL ρR n k
    · rw [indicator_of_mem h]
      exact le_of_livesPast hp hη h.1 h.2
    · rw [indicator_of_notMem h]
      exact zero_le
  · refine le_of_forall_lt fun c hc => ?_
    obtain ⟨t, rfl⟩ : ∃ t : ℝ≥0, (t : ℝ≥0∞) = c := ⟨c.toNNReal, ENNReal.coe_toNNReal (ne_top_of_lt hc)⟩
    obtain ⟨n, k, htd, hdζ⟩ := exists_dyad_btwn hc
    have hpos : 0 < dyad n k := lt_of_le_of_lt zero_le htd
    have hmem : η ∈ LiveSet a xL xR ρL ρR n k := ⟨hpos, livesPast_of_lt ha hp hη hpos hdζ⟩
    refine lt_of_lt_of_le ?_ (le_iSup_of_le n (le_iSup_of_le k (le_of_eq (indicator_of_mem hmem _).symm)))
    exact_mod_cast htd

/-! ### The killed driving events read from the trace -/

/-- **The record event read from a path**: some positive dyadic horizon `> r` passes the lifetime test, and the
partial code read at it has its state at `r` in `A`. -/
def RecSet (a : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (r : ℝ≥0)
    (A : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))) : Set (ℝ≥0 → ℂ) :=
  ⋃ (n : ℕ) (k : ℕ), {η | r < dyad n k ∧ LivesPast a xL xR ρL ρR η (dyad n k) ∧
    dInv (trCodeOf η (dyad n k)) ∈ dOf '' (PDet a xL xR ρL ρR (dyad n k) ∩ {x | stateAt x r ∈ A})}

theorem measurableSet_recSet (ha : 0 < a) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ) (r : ℝ≥0) {A : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))} (hA : MeasurableSet A) :
    MeasurableSet (RecSet a xL xR ρL ρR r A) := by
  refine MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun k => ?_
  have hz : Measurable fun η : ℝ≥0 → ℂ => dInv (trCodeOf η (dyad n k)) :=
    measurable_dInv.comp (measurable_trCodeOf _)
  have hI : MeasurableSet (dOf '' (PDet a xL xR ρL ρR (dyad n k) ∩ {x : XCode nL nR | stateAt x r ∈ A})) :=
    ((measurableSet_pDet a xL xR ρL ρR _).inter (measurable_stateAt r hA)).image_of_measurable_injOn
      measurable_dOf ((injOn_dOf_pDet ha _).mono inter_subset_left)
  exact (MeasurableSet.const _).inter ((measurableSet_livesPast ha xL xR ρL ρR _).inter (hz hI))

/-- **The killed driving events are events of the trace**: `η ∈ RecSet r A ↔ r < ζ ∧ (w_r, vL_r, vR_r) ∈ A`. -/
theorem mem_recSet_iff (ha : 0 < a) (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ)
    (hη : IsGeneratingTrace w ζ η) (r : ℝ≥0) (A : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))) :
    η ∈ RecSet a xL xR ρL ρR r A ↔ (r : ℝ≥0∞) < ζ ∧ (w r, fun i => vL i r, fun j => vR j r) ∈ A := by
  have hst : ∀ {d : ℝ≥0} {x : XCode nL nR}, (r : ℝ≥0∞) < min (d : ℝ≥0∞) ζ →
      (∀ t : ℝ≥0, (t : ℝ≥0∞) < min (d : ℝ≥0∞) ζ → cw x t = w t) →
      (∀ t : ℝ≥0, (t : ℝ≥0∞) < min (d : ℝ≥0∞) ζ → (∀ i, cvL x i t = vL i t) ∧ ∀ j, cvR x j t = vR j t) →
      stateAt x r = (w r, fun i => vL i r, fun j => vR j r) := by
    intro d x hrm hcw hag
    simp only [stateAt, hcw r hrm, Prod.mk.injEq, true_and]
    exact ⟨funext fun i => (hag r hrm).1 i, funext fun j => (hag r hrm).2 j⟩
  constructor
  · intro hm
    simp only [RecSet, mem_iUnion, mem_ofPred_eq] at hm
    obtain ⟨n, k, hrd, hl, x', ⟨hx', hxA⟩, hx'z⟩ := hm
    have hd0 : 0 < dyad n k := lt_of_le_of_lt zero_le hrd
    obtain ⟨x, hx, hxz, hcw⟩ := exists_of_livesPast hp hη hl
    obtain ⟨hle, hag⟩ := le_and_agree_of_mem_pDet hp hd0 hx hcw
    have hxx : x' = x := injOn_dOf_pDet ha _ hx' hx (hx'z.trans hxz.symm)
    have hrd' : (r : ℝ≥0∞) < ((dyad n k : ℝ≥0) : ℝ≥0∞) := by exact_mod_cast hrd
    have hrm : (r : ℝ≥0∞) < min ((dyad n k : ℝ≥0) : ℝ≥0∞) ζ := lt_min hrd' (lt_of_lt_of_le hrd' hle)
    refine ⟨lt_of_lt_of_le hrd' hle, ?_⟩
    have hxA' : stateAt x' r ∈ A := hxA
    rwa [hxx, hst hrm hcw hag] at hxA'
  · rintro ⟨hrζ, hA⟩
    obtain ⟨n, k, hrd, hdζ⟩ := exists_dyad_btwn hrζ
    have hd0 : 0 < dyad n k := lt_of_le_of_lt zero_le hrd
    have hl := livesPast_of_lt ha hp hη hd0 hdζ
    obtain ⟨x, hx, hxz, hcw⟩ := exists_of_livesPast hp hη hl
    obtain ⟨-, hag⟩ := le_and_agree_of_mem_pDet hp hd0 hx hcw
    have hrd' : (r : ℝ≥0∞) < ((dyad n k : ℝ≥0) : ℝ≥0∞) := by exact_mod_cast hrd
    have hrm : (r : ℝ≥0∞) < min ((dyad n k : ℝ≥0) : ℝ≥0∞) ζ := lt_min hrd' hrζ
    simp only [RecSet, mem_iUnion, mem_ofPred_eq]
    refine ⟨n, k, hrd, hl, x, ⟨hx, ?_⟩, hxz⟩
    show stateAt x r ∈ A
    rw [hst hrm hcw hag]
    exact hA

end InteractingSLE.Sec5.CrossRestart
