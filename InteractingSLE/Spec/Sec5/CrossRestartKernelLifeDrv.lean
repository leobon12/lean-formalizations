/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossRestartKernelLifeCut

/-!
# The lifetime and the record of an integrated path, read from its driver path

Packet PROVE-CFRESTART, the σ-algebra bridge of (A), counterflow side. The strip hypothesis sees the counterflow
through its driver path `W′` at all times (arbitrary after the lifetime `ζ′`). For an integrated `SLE_a(ρ)` path
`(w, vL, vR, b, ζ)` (`a > 0`), with `w` given at all times:

* `dec_killCode_of_lt`: the killed code of `w` at any horizon `U` decodes to `w` before `min U ζ` (no continuity of `w`
  after `ζ` is needed);
* `RecSetD r A`, **`measurableSet_recSetD`**, **`mem_recSetD_iff`**: the generating events
  `{r < ζ, (w_r, vL_r, vR_r) ∈ A}` of the killed driving σ-algebra are Borel events of the driver path (the partial
  code with the driver's killed code at a dyadic horizon, `CrossRestartKernelLifeTest.le_and_agree_of_mem_pDet`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CrossRestart

open Sec2.Assembly Exist Exist.Staged

variable {nL nR : ℕ} {a : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- **The killed code decodes to the driver before `min U ζ`**, for `w` continuous before `ζ` only. -/
theorem dec_killCode_of_lt (hw : ContinuousOn w {t : ℝ≥0 | (t : ℝ≥0∞) < ζ}) {U : ℝ≥0∞} {t : ℝ≥0}
    (htζ : (t : ℝ≥0∞) < ζ) (htU : (t : ℝ≥0∞) < U) : dec (killCode w U).2 t = w t := by
  have hopen : IsOpen {s : ℝ≥0 | (s : ℝ≥0∞) < ζ} := isOpen_lt ENNReal.continuous_coe continuous_const
  have hc : ContinuousWithinAt (killDrv w U) (Iic t) t :=
    ((hw t htζ).continuousAt (hopen.mem_nhds htζ)).continuousWithinAt.congr
      (fun s hs => killDrv_eqOn w U (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hs) htU)) (killDrv_eqOn w U htU)
  rw [killCode_snd, dec_enc hc, killDrv_eqOn w U htU]

theorem measurable_killCode (U : ℝ≥0∞) : Measurable fun w : ℝ≥0 → ℝ => killCode w U := by
  refine measurable_const.prodMk (measurable_pi_iff.2 fun n => measurable_pi_iff.2 fun k => ?_)
  by_cases h : (dyad n k : ℝ≥0∞) < U
  · simp only [h, ↓reduceIte]
    exact measurable_pi_apply _
  · simp only [h, ↓reduceIte]
    exact measurable_const

/-- **The record event read from a driver path**: at some dyadic horizon `> r`, the killed code of the path is the
driver code of a partial code whose state at `r` is in `A`. -/
def RecSetD (a : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (r : ℝ≥0)
    (A : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))) : Set (ℝ≥0 → ℝ) :=
  ⋃ (n : ℕ) (k : ℕ), {w | r < dyad n k ∧
    killCode w (dyad n k) ∈ dOf '' (PDet a xL xR ρL ρR (dyad n k) ∩ {x | stateAt x r ∈ A})}

theorem measurableSet_recSetD (ha : 0 < a) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ) (r : ℝ≥0) {A : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))} (hA : MeasurableSet A) :
    MeasurableSet (RecSetD a xL xR ρL ρR r A) := by
  refine MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun k => ?_
  have hI : MeasurableSet (dOf '' (PDet a xL xR ρL ρR (dyad n k) ∩ {x : XCode nL nR | stateAt x r ∈ A})) :=
    ((measurableSet_pDet a xL xR ρL ρR _).inter (measurable_stateAt r hA)).image_of_measurable_injOn
      measurable_dOf ((injOn_dOf_pDet ha _).mono inter_subset_left)
  exact (MeasurableSet.const _).inter (measurable_killCode _ hI)

/-- The state at `r` of a partial code with the path's killed driver code at a horizon `d > r`. -/
theorem stateAt_eq_of_dOf_eq_killCode (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) {d : ℝ≥0} (hd : 0 < d)
    {x : XCode nL nR} (hx : x ∈ PDet a xL xR ρL ρR d) (hxk : dOf x = killCode w d) :
    (d : ℝ≥0∞) ≤ ζ ∧ ∀ r : ℝ≥0, (r : ℝ≥0∞) < min (d : ℝ≥0∞) ζ →
      stateAt x r = (w r, fun i => vL i r, fun j => vR j r) := by
  have hcw : ∀ t : ℝ≥0, (t : ℝ≥0∞) < min (d : ℝ≥0∞) ζ → cw x t = w t := fun t ht => by
    have h2 : (dOf x).2 = (killCode w d).2 := by rw [hxk]
    show dec x.2.2.1 t = w t
    rw [show x.2.2.1 = (killCode w d).2 from h2]
    exact dec_killCode_of_lt hp.2.2.2.1 (lt_of_lt_of_le ht (min_le_right _ _))
      (lt_of_lt_of_le ht (min_le_left _ _))
  obtain ⟨hle, hag⟩ := le_and_agree_of_mem_pDet hp hd hx hcw
  refine ⟨hle, fun r hr => ?_⟩
  simp only [stateAt, hcw r hr, Prod.mk.injEq, true_and]
  exact ⟨funext fun i => (hag r hr).1 i, funext fun j => (hag r hr).2 j⟩

/-- **The killed driving events are events of the driver path**:
`w ∈ RecSetD r A ↔ r < ζ ∧ (w_r, vL_r, vR_r) ∈ A`. -/
theorem mem_recSetD_iff (ha : 0 < a) (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) (r : ℝ≥0)
    (A : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))) :
    w ∈ RecSetD a xL xR ρL ρR r A ↔ (r : ℝ≥0∞) < ζ ∧ (w r, fun i => vL i r, fun j => vR j r) ∈ A := by
  constructor
  · intro hm
    simp only [RecSetD, mem_iUnion, mem_ofPred_eq] at hm
    obtain ⟨n, k, hrd, x, ⟨hx, hxA⟩, hxk⟩ := hm
    have hd0 : 0 < dyad n k := lt_of_le_of_lt zero_le hrd
    obtain ⟨hle, hst⟩ := stateAt_eq_of_dOf_eq_killCode hp hd0 hx hxk
    have hrd' : (r : ℝ≥0∞) < ((dyad n k : ℝ≥0) : ℝ≥0∞) := by exact_mod_cast hrd
    have hrζ : (r : ℝ≥0∞) < ζ := lt_of_lt_of_le hrd' hle
    refine ⟨hrζ, ?_⟩
    have hxA' : stateAt x r ∈ A := hxA
    rwa [hst r (lt_min hrd' hrζ)] at hxA'
  · rintro ⟨hrζ, hA⟩
    obtain ⟨n, k, hrd, hdζ⟩ := exists_dyad_btwn hrζ
    have hd0 : 0 < dyad n k := lt_of_le_of_lt zero_le hrd
    have hx := cutCode_mem_pDet ha hp hd0 hdζ
    obtain ⟨-, hst⟩ := stateAt_eq_of_dOf_eq_killCode hp hd0 hx rfl
    have hrd' : (r : ℝ≥0∞) < ((dyad n k : ℝ≥0) : ℝ≥0∞) := by exact_mod_cast hrd
    simp only [RecSetD, mem_iUnion, mem_ofPred_eq]
    refine ⟨n, k, hrd, cutCode b w vL vR (dyad n k), ⟨hx, ?_⟩, rfl⟩
    show stateAt _ r ∈ A
    rw [hst r (lt_min hrd' hrζ)]
    exact hA

end InteractingSLE.Sec5.CrossRestart
