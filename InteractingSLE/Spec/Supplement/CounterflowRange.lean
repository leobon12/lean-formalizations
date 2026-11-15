/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Foundations.Loewner.TraceClose
import InteractingSLE.Spec.Sec7.ContinuityProb2Restart
import InteractingSLE.Spec.Sec7.ContinuityProbCollision
import InteractingSLE.Frozen.Spec.Chart_tipSet
import InteractingSLE.Frozen.Spec.Chart_recenter
import InteractingSLE.Frozen.Spec.Chart_id
import InteractingSLE.Frozen.Spec.Chart_loewner
import InteractingSLE.Frozen.Spec.counterflowCompletedRange
import InteractingSLE.Spec.Supplement.GB6Contact
import InteractingSLE.Frozen.Spec.ExplState_physSet
import InteractingSLE.Frozen.Spec.ExplState_run
import InteractingSLE.Spec.Supplement.GW6Reduction

/-!
# Theorem 1.4: the deterministic bridges for `Chart.tipSet`, `ExplState.physSet` and `counterflowCompletedRange`

Packet PROVE-T14-GW2, item (1) (`planning/handoffs/PROVE-T14-GW.md` §5 (B)(i)–(ii)). The frozen Theorem 1.4 surface
describes the physical points of an ordinary piece (`Chart.tipSet`) and of the counterflow
(`counterflowCompletedRange`) as radial limits `lim_{y ↓ 0} c.inv (F_t(iy))` of the inverse Loewner maps. This file
identifies them with the continuous generating traces of Theorem 1.3:

* **`tipSet_stopped_eq`** (bridge (i)): for a continuous generating trace `α` of `W` on `[0, S]` (`W` continuous on
  `[0, S]`, `W 0 = 0`), the tip set of the piece whose driver is stopped at `S` (the form stored by
  `ExplState.launch`) is `c.inv (α([0, S]))`, for a chart whose inverse is continuous on `ℂ` (the recentred identity
  charts of a root). At `S` itself the tip is the trace-closure fact of PROVE-TRACECLOSE
  (`TraceClose.tendsto_fwdMapInv_tip_of_isLoewnerTraceLT`). `tipSet_stopped_eq_of_tendsto` is the form for any chart
  whose inverse has limits from inside `ℍ` at the trace points (`f(α([0, S]))`); `tendsto_loewner_inv` supplies them
  for the Loewner charts `c.loewner W T` of later pieces from boundary limits of `F_T`, and
  `tendsto_loewner_stopped_inv` for the chart recorded after a stopped piece at a finite stop `S > 0` (at every point
  of `ℍ̄`).
* **`tipSet_infinitySourceChart_top`**, **`counterflowCompletedRange_eq_preimage_closure`** (bridge (ii)): for a
  continuous transient generating trace `γ` on `[0, ∞)`, the completed counterflow range is
  `{−1/γ(t) : γ(t) ≠ 0} ∪ {0}`, which is the set of points of `ℂ` in the closure, in the Riemann sphere, of the
  physical counterflow `R̂ ∘ γ` (GB6's form, `Supp8.GB6.sphereInv`); in particular it is closed
  (`isClosed_counterflowCompletedRange`).
* `physSet_single`: the physical set of a single ordinary instruction is the root and the tip set of the piece.
* `continuousOn_le_min`: the driver of a piece is continuous up to its stop `min t ζ` (at a finite positive lifetime
  from its left limit).
* **`mem_closure_of_dense_contacts`**: the finite-horizon form of GB6's final assertion — if a flow trace `α` on
  `[0, ζ]` has its interior points at rational own times `< ζ` on a path `η`, then `α([0, ζ])` lies in the closure
  of the range of `η`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)

namespace InteractingSLE
namespace Theorem14
namespace CounterflowRange

/-- The driver stopped at `S` is continuous when the driver is continuous on `[0, S]`. -/
theorem continuous_stopped {W : ℝ≥0 → ℝ} {S : ℝ≥0∞} (hW : ContinuousOn W {t | (t : ℝ≥0∞) ≤ S}) :
    Continuous fun r : ℝ≥0 => W (min (r : ℝ≥0∞) S).toNNReal := by
  have hne : ∀ r : ℝ≥0, min (r : ℝ≥0∞) S ≠ ⊤ := fun r =>
    (lt_of_le_of_lt (min_le_left _ _) ENNReal.coe_lt_top).ne
  have hφ : Continuous fun r : ℝ≥0 => (min (r : ℝ≥0∞) S).toNNReal :=
    ENNReal.continuousOn_toNNReal.comp_continuous (ENNReal.continuous_coe.min continuous_const) hne
  refine hW.comp_continuous hφ fun r => ?_
  show (((min (r : ℝ≥0∞) S).toNNReal : ℝ≥0) : ℝ≥0∞) ≤ S
  rw [ENNReal.coe_toNNReal (hne r)]
  exact min_le_right _ _

/-- The stopped driver agrees with the driver up to `S`. -/
theorem stopped_eq_of_lt {W : ℝ≥0 → ℝ} {S : ℝ≥0∞} {t : ℝ≥0} (ht : (t : ℝ≥0∞) ≤ S) :
    W (min (t : ℝ≥0∞) S).toNNReal = W t := by
  rw [min_eq_left ht, ENNReal.toNNReal_coe]

/-- A generating trace on `[0, S]` also generates the chain of the driver stopped at `S`. -/
theorem isGeneratingTrace_stopped {W : ℝ≥0 → ℝ} {S : ℝ≥0∞} {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace W S α) :
    IsGeneratingTrace (fun r : ℝ≥0 => W (min (r : ℝ≥0∞) S).toNNReal) S α :=
  Sec7.IsGeneratingTrace.congr_lt hα fun _ ht => stopped_eq_of_lt ht.le

/-- The frozen generating trace on `[0, σ]`, read on `ℝ`, is a continuous Loewner trace before `σ` (the driver itself,
not frozen after a later time). -/
theorem isLoewnerTraceLT_of_isGeneratingTrace {w : ℝ≥0 → ℝ} {σ : ℝ≥0} {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace w σ η) :
    IsLoewnerTraceLT (fun s : ℝ => w s.toNNReal) σ (fun s : ℝ => η s.toNNReal) := by
  refine ⟨by simpa using hη.1, ?_, fun t ht htσ => ?_⟩
  · refine hη.2.1.comp continuous_real_toNNReal.continuousOn fun s hs => ?_
    show ((s.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ σ
    exact ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hs.2.le)
  · have htT : ((t.toNNReal : ℝ≥0) : ℝ≥0∞) < σ :=
      ENNReal.coe_lt_coe.2 ((Real.toNNReal_lt_iff_lt_coe ht).2 htσ)
    have hfill := hη.2.2 t.toNNReal htT
    rw [Real.coe_toNNReal _ ht] at hfill
    have hA : IsCompact (η '' Icc 0 t.toNNReal) := isCompact_Icc.image_of_continuousOn
      (hη.2.1.mono fun r hr => (ENNReal.coe_le_coe.2 hr.2).trans htT.le)
    rw [image_toNNReal_Icc η ht]
    exact (fillH_eq_iff_isFilling_of_isClosed hA.isBounded hA.isClosed
      ((QuantumZipper.fwdHull_mono).2 _)).1 hfill

/-- **The radial tip at every time up to and including the horizon**, for a driver continuous on `[0, ∞)`: before `S`
by `IsGeneratingTrace.tendsto_fwdMapInv_mul_I`, at `S` by the trace-closure fact of PROVE-TRACECLOSE. -/
theorem tendsto_radial_of_le {w : ℝ≥0 → ℝ} {S : ℝ≥0∞} {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace w S η)
    (hw : Continuous w) (hw0 : w 0 = 0) {t : ℝ≥0} (ht : (t : ℝ≥0∞) ≤ S) :
    Tendsto (fun y : ℝ => fwdMapInv (fun s : ℝ => w s.toNNReal) t (y * I)) (𝓝[>] 0) (𝓝 (η t)) := by
  rcases ht.lt_or_eq with hlt | heq
  · exact hη.tendsto_fwdMapInv_mul_I hw.continuousOn hw0 hlt
  have hη' : IsGeneratingTrace w t η := heq ▸ hη
  have hW : Continuous fun s : ℝ => w s.toNNReal := hw.comp continuous_real_toNNReal
  have hW0 : (fun s : ℝ => w s.toNNReal) 0 = 0 := by simpa using hw0
  rcases eq_or_ne t 0 with h0 | h0
  · subst h0
    rw [hη'.1]
    have hlim : Tendsto (fun y : ℝ => (y : ℂ) * I) (𝓝[>] 0) (𝓝 0) :=
      tendsto_nhdsWithin_iff.1 tendsto_ofReal_mul_I_nhdsWithin_H |>.1
    refine hlim.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hyH : (y : ℂ) * I ∈ H := by
      show 0 < ((y : ℂ) * I).im
      simpa using hy
    exact (fwdMapInv_zero_time hW hW0 hyH).symm
  · have hσ : (0 : ℝ) < t := NNReal.coe_pos.2 (pos_iff_ne_zero.2 h0)
    have hc : ContinuousOn (fun s : ℝ => η s.toNNReal) (Icc 0 (t : ℝ)) :=
      hη'.2.1.comp continuous_real_toNNReal.continuousOn fun s hs =>
        ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hs.2)
    have h := TraceClose.tendsto_fwdMapInv_tip_of_isLoewnerTraceLT
      (isLoewnerTraceLT_of_isGeneratingTrace hη') hW hW0 hσ hc
    have h' := h.comp tendsto_ofReal_mul_I_nhdsWithin_H
    simp only [Real.toNNReal_coe] at h'
    exact h'


/-- The radial limit of an ordinary piece with stopped driver at each own time `t ≤ S`, read in a chart whose inverse
has the limit `f p` at every trace point `p` from inside `ℍ` (for a chart continuous on `ℂ`, `f = c.inv`; for a
Loewner chart, its boundary extension, `tendsto_loewner_inv`). -/
theorem tendsto_tip_stopped_of_tendsto {c : Chart} {f : ℂ → ℂ} {W : ℝ≥0 → ℝ} {S : ℝ≥0∞} {α : ℝ≥0 → ℂ}
    (hα : IsGeneratingTrace W S α) (hW : ContinuousOn W {t | (t : ℝ≥0∞) ≤ S}) (hW0 : W 0 = 0)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) ≤ S) (hc : Tendsto c.2.1 (𝓝[H] (α t)) (𝓝 (f (α t)))) :
    Tendsto (fun y : ℝ => c.2.1 (fwdMapInv (fun r : ℝ => W (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) S).toNNReal) t
      (y * I))) (𝓝[>] 0) (𝓝 (f (α t))) := by
  have h0 : W (min ((0 : ℝ≥0) : ℝ≥0∞) S).toNNReal = 0 := by
    rw [stopped_eq_of_lt (W := W) (t := 0) (by simp), hW0]
  have hU : Continuous fun r : ℝ => W (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) S).toNNReal :=
    (continuous_stopped hW).comp continuous_real_toNNReal
  have hU0 : (fun r : ℝ => W (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) S).toNNReal) 0 = 0 := by simpa using h0
  have hlim := tendsto_radial_of_le (isGeneratingTrace_stopped hα) (continuous_stopped hW) h0 ht
  have hH : Tendsto (fun y : ℝ => fwdMapInv (fun r : ℝ => W (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) S).toNNReal) t
      (y * I)) (𝓝[>] 0) (𝓝[H] (α t)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hlim, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hyH : (y : ℂ) * I ∈ H := by
      show 0 < ((y : ℂ) * I).im
      simpa using hy
    exact QuantumZipper.RS.fwdMapInv_mem_H hU hU0 (NNReal.coe_nonneg t) hyH
  exact hc.comp hH

/-- **Bridge (i), general chart**: the tip set of a piece with stopped driver, read in a chart whose inverse has the
limit `f p` from inside `ℍ` at every trace point `p = α(t)`, `t ≤ S`, is `f(α([0, S]))`. -/
theorem tipSet_stopped_eq_of_tendsto {c : Chart} {f : ℂ → ℂ} {W : ℝ≥0 → ℝ} {S : ℝ≥0∞} {α : ℝ≥0 → ℂ}
    (hα : IsGeneratingTrace W S α) (hW : ContinuousOn W {t | (t : ℝ≥0∞) ≤ S}) (hW0 : W 0 = 0)
    (hc : ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ S → Tendsto c.2.1 (𝓝[H] (α t)) (𝓝 (f (α t)))) :
    c.tipSet (fun r : ℝ≥0 => W (min (r : ℝ≥0∞) S).toNNReal) S = f '' (α '' {t | (t : ℝ≥0∞) ≤ S}) := by
  ext z
  constructor
  · rintro ⟨t, ht, hlim⟩
    exact ⟨α t, ⟨t, ht, rfl⟩,
      tendsto_nhds_unique (tendsto_tip_stopped_of_tendsto hα hW hW0 ht (hc t ht)) hlim⟩
  · rintro ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    exact ⟨t, ht, tendsto_tip_stopped_of_tendsto hα hW hW0 ht (hc t ht)⟩

/-- **Bridge (i)** (chart continuous on `ℂ`, e.g. a recentred identity chart): if `α` is a continuous generating trace
of `W` on `[0, S]` (`W` continuous on `[0, S]`, `W 0 = 0`), the frozen `Chart.tipSet` of the piece with the driver
stopped at `S` (the form stored by `ExplState.launch`) is the chart image of `α([0, S])`. -/
theorem tipSet_stopped_eq {c : Chart} (hc : Continuous c.2.1) {W : ℝ≥0 → ℝ} {S : ℝ≥0∞} {α : ℝ≥0 → ℂ}
    (hα : IsGeneratingTrace W S α) (hW : ContinuousOn W {t | (t : ℝ≥0∞) ≤ S}) (hW0 : W 0 = 0) :
    c.tipSet (fun r : ℝ≥0 => W (min (r : ℝ≥0∞) S).toNNReal) S = c.2.1 '' (α '' {t | (t : ℝ≥0∞) ≤ S}) :=
  tipSet_stopped_eq_of_tendsto hα hW hW0 fun t _ =>
    (hc.tendsto (α t)).mono_left nhdsWithin_le_nhds

/-- The inverse of a Loewner chart `c.loewner W T` (`c.inv ∘ F_T`) has boundary limits from inside `ℍ` wherever `F_T`
does and `c.inv` has them at the image point: `F_T` maps `ℍ` into `ℍ`. -/
theorem tendsto_loewner_inv {c : Chart} {f : ℂ → ℂ} {W : ℝ → ℝ} {T : ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    (hT : 0 ≤ T) {p q : ℂ} (hF : Tendsto (fwdMapInv W T) (𝓝[H] p) (𝓝 q))
    (hc : Tendsto c.2.1 (𝓝[H] q) (𝓝 (f q))) :
    Tendsto (c.loewner W T).2.1 (𝓝[H] p) (𝓝 (f q)) := by
  have hFH : Tendsto (fwdMapInv W T) (𝓝[H] p) (𝓝[H] q) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hF, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact QuantumZipper.RS.fwdMapInv_mem_H hW hW0 hT hz
  exact hc.comp hFH

/-- **The chart after a stopped piece has boundary limits.** At a finite stop `S > 0`, the inverse of the chart
`c.loewner Ws S` recorded by `ExplState.launch` (`Ws` the driver stopped at `S`, `c` with continuous inverse) has a
limit from inside `ℍ` at every point of `ℍ̄`: `F_S` extends continuously to `ℍ̄` because the piece's trace closes at
its horizon (PROVE-TRACECLOSE, `TraceClose.hasBdryLimits_of_isLoewnerTraceLT`). With
`tipSet_stopped_eq_of_tendsto` this reads off the tip set of the next piece. -/
theorem tendsto_loewner_stopped_inv {c : Chart} (hc : Continuous c.2.1) {W : ℝ≥0 → ℝ} {S : ℝ≥0}
    {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace W S α) (hW : ContinuousOn W {t | (t : ℝ≥0∞) ≤ S}) (hW0 : W 0 = 0)
    (hS : 0 < S) {p : ℂ} (hp : p ∈ Hbar) :
    Tendsto (c.loewner (fun r : ℝ => W (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) S).toNNReal) S).2.1 (𝓝[H] p)
      (𝓝 (c.2.1 (extendFrom H (fwdMapInv (fun r : ℝ => W (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) S).toNNReal) S)
        p))) := by
  have h0 : W (min ((0 : ℝ≥0) : ℝ≥0∞) S).toNNReal = 0 := by
    rw [stopped_eq_of_lt (W := W) (t := 0) (by simp), hW0]
  have hU : Continuous fun r : ℝ => W (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) S).toNNReal :=
    (continuous_stopped hW).comp continuous_real_toNNReal
  have hU0 : (fun r : ℝ => W (min ((r.toNNReal : ℝ≥0) : ℝ≥0∞) S).toNNReal) 0 = 0 := by simpa using h0
  have hη := isLoewnerTraceLT_of_isGeneratingTrace (isGeneratingTrace_stopped hα)
  have hησ : ContinuousOn (fun s : ℝ => α s.toNNReal) (Icc 0 (S : ℝ)) :=
    hα.2.1.comp continuous_real_toNNReal.continuousOn fun s hs =>
      ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hs.2)
  have hB := TraceClose.hasBdryLimits_of_isLoewnerTraceLT hη hU hU0 (NNReal.coe_pos.2 hS) hησ
  exact tendsto_loewner_inv hU hU0 (NNReal.coe_nonneg S) (hB.tendsto hp)
    ((hc.tendsto _).mono_left nhdsWithin_le_nhds)

/-- The inverse of the recentred identity chart is a translation. -/
theorem recenter_id_inv (x : ℝ) : (Chart.id.recenter x).2.1 = fun z : ℂ => z + (x : ℂ) := rfl

/-- The inverse of the recentred identity chart is continuous. -/
theorem continuous_recenter_id_inv (x : ℝ) : Continuous (Chart.id.recenter x).2.1 :=
  continuous_id.add continuous_const

/-! ### The completed counterflow range -/

theorem infinitySourceChart_inv : infinitySourceChart.2.1 = fun z => -z⁻¹ := rfl

/-- **Bridge (ii), the tip set of the counterflow.** For a continuous generating trace `γ` on `[0, ∞)` of a
continuous driver `W` (`W 0 = 0`), the physical points of the counterflow in the chart `R(z) = −1/z` are the points
`−1/γ(t)` with `γ(t) ≠ 0` (at `γ(t) = 0` the radial limit is `∞`, not a point of `ℂ`). -/
theorem tipSet_infinitySourceChart_top {W : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace W ⊤ γ)
    (hW : Continuous W) (hW0 : W 0 = 0) :
    infinitySourceChart.tipSet W ⊤ = {z | ∃ t, γ t ≠ 0 ∧ z = -(γ t)⁻¹} := by
  have hF : ∀ t : ℝ≥0, Tendsto (fun y : ℝ => fwdMapInv (fun s : ℝ => W s.toNNReal) t (y * I)) (𝓝[>] 0)
      (𝓝 (γ t)) := fun t => hγ.tendsto_fwdMapInv_mul_I hW.continuousOn hW0 ENNReal.coe_lt_top
  ext z
  constructor
  · rintro ⟨t, -, hlim⟩
    by_cases h0 : γ t = 0
    · exfalso
      have hU : Continuous fun s : ℝ => W s.toNNReal := hW.comp continuous_real_toNNReal
      have hU0 : (fun s : ℝ => W s.toNNReal) 0 = 0 := by simpa using hW0
      have hne : Tendsto (fun y : ℝ => fwdMapInv (fun s : ℝ => W s.toNNReal) t (y * I)) (𝓝[>] 0)
          (𝓝[≠] 0) := by
        refine tendsto_nhdsWithin_iff.2 ⟨h0 ▸ hF t, ?_⟩
        filter_upwards [self_mem_nhdsWithin] with y hy
        have hyH : (y : ℂ) * I ∈ H := by
          show 0 < ((y : ℂ) * I).im
          simpa using hy
        have hmem := QuantumZipper.RS.fwdMapInv_mem_H hU hU0 (NNReal.coe_nonneg t) hyH
        intro hz
        rw [mem_singleton_iff] at hz
        rw [hz] at hmem
        have him : (0 : ℝ) < (0 : ℂ).im := hmem
        simp at him
      have hcob : Tendsto (fun y : ℝ => -(fwdMapInv (fun s : ℝ => W s.toNNReal) t (y * I))⁻¹) (𝓝[>] 0)
          (Bornology.cobounded ℂ) := by
        have h1 := (tendsto_inv₀_nhdsNE_zero (α := ℂ)).comp hne
        rw [← tendsto_norm_atTop_iff_cobounded] at h1 ⊢
        simpa only [Function.comp_apply, norm_neg] using h1
      exact hcob.not_tendsto (Metric.disjoint_nhds_cobounded z).symm hlim
    · exact ⟨t, h0, tendsto_nhds_unique hlim ((hF t).inv₀ h0).neg⟩
  · rintro ⟨t, h0, rfl⟩
    exact ⟨t, le_top, ((hF t).inv₀ h0).neg⟩

/-- In the sphere, the closure of the range of a transient path read through the inversion adds only the point `0`
(the image of `∞`). -/
theorem closure_range_sphereInv_subset {γ : ℝ≥0 → ℂ} (hγ : Continuous γ)
    (htr : Tendsto (fun t => ‖γ t‖) atTop atTop) :
    closure (range fun t => Supp8.GB6.sphereInv (γ t : OnePoint ℂ)) ⊆
      insert ((0 : ℂ) : OnePoint ℂ) (range fun t => Supp8.GB6.sphereInv (γ t : OnePoint ℂ)) := by
  set η : ℝ≥0 → OnePoint ℂ := fun t => Supp8.GB6.sphereInv (γ t : OnePoint ℂ) with hηdef
  have hηc : Continuous η := Supp8.GB6.continuous_sphereInv.comp (OnePoint.continuous_coe.comp hγ)
  have hlim : Tendsto η atTop (𝓝 ((0 : ℂ) : OnePoint ℂ)) := Supp8.GB6.tendsto_sphereInv_of_tendsto_norm htr
  intro p hp
  by_contra hcon
  rw [mem_insert_iff, not_or] at hcon
  obtain ⟨hp0, hpr⟩ := hcon
  obtain ⟨U, V, hU, hV, hpU, h0V, hUV⟩ := t2_separation hp0
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hlim (hV.mem_nhds h0V))
  have hK : IsClosed (η '' Icc 0 N) := (isCompact_Icc.image hηc).isClosed
  have hsub : range η ⊆ η '' Icc 0 N ∪ V := by
    rintro _ ⟨t, rfl⟩
    rcases le_total t N with h | h
    · exact Or.inl ⟨t, ⟨zero_le, h⟩, rfl⟩
    · exact Or.inr (hN t h)
  have hp' : p ∈ η '' Icc 0 N ∪ closure V := by
    have := closure_mono hsub hp
    rwa [closure_union, hK.closure_eq] at this
  rcases hp' with ⟨t, -, rfl⟩ | hpV
  · exact hpr ⟨t, rfl⟩
  · obtain ⟨q, hqU, hqV⟩ := mem_closure_iff.1 hpV U hU hpU
    exact hUV.le_bot ⟨hqU, hqV⟩

/-- **Bridge (ii): the completed counterflow range is the trace of the closed physical range.** For a continuous
transient generating trace `γ` on `[0, ∞)` of a continuous driver `W` (`W 0 = 0`), the frozen
`counterflowCompletedRange W` is the set of points of `ℂ` in the closure, in the Riemann sphere, of the physical
counterflow `η = R̂ ∘ γ`. In particular it is closed in `ℂ`. -/
theorem counterflowCompletedRange_eq_preimage_closure {W : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ}
    (hγ : IsGeneratingTrace W ⊤ γ) (hW : Continuous W) (hW0 : W 0 = 0)
    (htr : Tendsto (fun t => ‖γ t‖) atTop atTop) :
    counterflowCompletedRange W =
      ((↑) : ℂ → OnePoint ℂ) ⁻¹' closure (range fun t => Supp8.GB6.sphereInv (γ t : OnePoint ℂ)) := by
  have hγc : Continuous γ := by
    have := hγ.2.1
    simp only [le_top, ofPred_true] at this
    exact continuousOn_univ.1 this
  unfold counterflowCompletedRange
  rw [tipSet_infinitySourceChart_top hγ hW hW0]
  ext z
  simp only [mem_union, mem_ofPred_eq, mem_singleton_iff, mem_preimage]
  constructor
  · rintro (⟨t, h0, rfl⟩ | rfl)
    · refine subset_closure ⟨t, ?_⟩
      exact Supp8.GB6.sphereInv_coe_of_ne h0
    · exact mem_closure_of_tendsto (Supp8.GB6.tendsto_sphereInv_of_tendsto_norm htr)
        (Eventually.of_forall fun t => ⟨t, rfl⟩)
  · intro hz
    rcases closure_range_sphereInv_subset hγc htr hz with h | ⟨t, ht⟩
    · exact Or.inr (OnePoint.coe_injective h)
    · change Supp8.GB6.sphereInv (γ t : OnePoint ℂ) = (z : OnePoint ℂ) at ht
      by_cases h0 : γ t = 0
      · simp [h0] at ht
      · rw [Supp8.GB6.sphereInv_coe_of_ne h0] at ht
        exact Or.inl ⟨t, h0, (OnePoint.coe_injective ht).symm⟩

theorem isClosed_counterflowCompletedRange {W : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ}
    (hγ : IsGeneratingTrace W ⊤ γ) (hW : Continuous W) (hW0 : W 0 = 0)
    (htr : Tendsto (fun t => ‖γ t‖) atTop atTop) : IsClosed (counterflowCompletedRange W) := by
  rw [counterflowCompletedRange_eq_preimage_closure hγ hW hW0 htr]
  exact isClosed_closure.preimage OnePoint.continuous_coe

/-! ### Single-instruction histories -/

/-- The ordinary pieces after a launch: the new piece (launch chart, stopped driver, stop) is appended. -/
theorem pieces_launch (s : ExplState) (k : ℕ) (D : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ) (t : ℝ≥0∞) :
    (ExplState.launch s k D θ t).1 =
      s.1 ++ [(s.2.2.2.2.1, fun r : ℝ≥0 => D.1 (min (r : ℝ≥0∞) (min t D.2)).toNNReal, min t D.2)] := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL⟩ := s
  unfold ExplState.launch
  dsimp only
  split_ifs <;> try rfl
  all_goals (rcases status with _ | _ | _ | _ | _ | _ <;> rfl)

/-- The run of a single ordinary instruction is the launch from the root. -/
theorem run_single (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (x₀ : ℝ) (gw2 : Bool) (θ : ℝ) (t : ℝ≥0∞)
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    ExplState.run κ b jumps (x₀, gw2, [Sum.inl (θ, t)]) D 1 =
      ExplState.launch (ExplState.init x₀) 0 (D 0) θ t := rfl

/-- **The physical set of a single ordinary instruction**: the root and the physical points of the piece, read in
the root chart with the driver stopped at `min t ζ`. -/
theorem physSet_single (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (x₀ : ℝ) (gw2 : Bool) (θ : ℝ) (t : ℝ≥0∞)
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    ExplState.physSet κ b jumps (x₀, gw2, [Sum.inl (θ, t)]) D =
      {(x₀ : ℂ)} ∪ (Chart.id.recenter x₀).tipSet
        (fun r : ℝ≥0 => (D 0).1 (min (r : ℝ≥0∞) (min t (D 0).2)).toNNReal) (min t (D 0).2) := by
  unfold ExplState.physSet
  simp only [List.length_singleton]
  rw [run_single, pieces_launch, Theorem14.arcs_launch]
  simp [ExplState.init]

/-! ### Continuity of a stopped driver up to its stop -/

/-- A driver continuous before `T` with left limit `w T` at `T` is continuous on `[0, T]`. -/
theorem continuousOn_le_of_tendsto {w : ℝ≥0 → ℝ} {T : ℝ≥0} (hw : ContinuousOn w {s | (s : ℝ≥0∞) < T})
    (hT : Tendsto w (𝓝[<] T) (𝓝 (w T))) : ContinuousOn w {s | (s : ℝ≥0∞) ≤ T} := by
  have hlt : {s : ℝ≥0 | (s : ℝ≥0∞) < T} = Iio T := by ext s; simp
  have hle : {s : ℝ≥0 | (s : ℝ≥0∞) ≤ T} = Iic T := by ext s; simp
  rw [hlt] at hw
  rw [hle]
  intro x hx
  rcases (show x ≤ T from hx).lt_or_eq with hxT | rfl
  · exact (hw.continuousAt (isOpen_Iio.mem_nhds hxT)).continuousWithinAt
  · exact continuousWithinAt_Iio_iff_Iic.1 hT

/-- **The driver of an ordinary piece is continuous up to its stop `min t ζ`**: before the lifetime `ζ` by the path
conditions, and at a finite positive lifetime by its left limit (`hend`). -/
theorem continuousOn_le_min {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (t : ℝ≥0∞) (hw : ContinuousOn w {s | (s : ℝ≥0∞) < ζ})
    (hend : ζ ≠ ⊤ → 0 < ζ → Tendsto w (𝓝[<] ζ.toNNReal) (𝓝 (w ζ.toNNReal))) :
    ContinuousOn w {s | (s : ℝ≥0∞) ≤ min t ζ} := by
  rcases lt_or_ge t ζ with htζ | hζt
  · exact hw.mono fun s hs => lt_of_le_of_lt (le_trans hs (min_le_left _ _)) htζ
  rw [min_eq_right hζt]
  rcases eq_or_ne ζ ⊤ with rfl | hζ
  · exact hw.mono fun s _ => ENNReal.coe_lt_top
  rcases eq_or_ne ζ 0 with rfl | hζ0
  · refine Set.Subsingleton.continuousOn ?_ w
    intro x hx y hy
    have hx' : x = 0 := by simpa using hx
    have hy' : y = 0 := by simpa using hy
    rw [hx', hy']
  have hT := ENNReal.coe_toNNReal hζ
  have h := continuousOn_le_of_tendsto (T := ζ.toNNReal) (by rwa [hT]) (hend hζ (pos_iff_ne_zero.2 hζ0))
  rwa [hT] at h

/-! ### Containment of a flow piece from first contacts at dense interior times -/

/-- Interior rational own times are dense before the horizon. -/
theorem exists_rat_mem_H_btwn {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {α : ℝ≥0 → ℂ} (hα : IsGeneratingTrace w ζ α)
    (hw : ContinuousOn w {s | (s : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0) {a b : ℝ≥0} (hab : a < b)
    (hb : (b : ℝ≥0∞) ≤ ζ) :
    ∃ q : ℚ, a < (q : ℝ).toNNReal ∧ (q : ℝ).toNNReal < b ∧ ((q : ℝ).toNNReal : ℝ≥0∞) < ζ ∧
      α (q : ℝ).toNNReal ∈ H := by
  obtain ⟨m, ham, hmb⟩ := exists_between hab
  have hm : (m : ℝ≥0∞) < ζ := lt_of_lt_of_le (ENNReal.coe_lt_coe.2 hmb) hb
  obtain ⟨z, hz, hzH⟩ := Supp9D.exists_mem_H_of_isGeneratingTrace hα hw hw0 ham hm
  have hαc : ContinuousOn α (Ioo a m) :=
    hα.2.1.mono fun s hs => (ENNReal.coe_le_coe.2 hs.2.le).trans hm.le
  have hopen : IsOpen (Ioo a m ∩ α ⁻¹' H) := hαc.isOpen_inter_preimage isOpen_Ioo QuantumZipper.isOpen_H
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen z ⟨hz, hzH⟩
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show (z : ℝ) < z + ε by linarith)
  have hq0 : (0 : ℝ) ≤ q := le_trans z.coe_nonneg hq1.le
  have hs : (((q : ℝ).toNNReal : ℝ≥0) : ℝ) = q := Real.coe_toNNReal _ hq0
  have hsU : (q : ℝ).toNNReal ∈ Ioo a m ∩ α ⁻¹' H := by
    refine hball ?_
    rw [Metric.mem_ball, NNReal.dist_eq, hs, abs_of_pos (by linarith)]
    linarith
  exact ⟨q, hsU.1.1, hsU.1.2.trans hmb, lt_trans (ENNReal.coe_lt_coe.2 hsU.1.2) hm, hsU.2⟩

/-- **Containment of a flow piece up to its horizon from first contacts.** Let `α` be a continuous generating trace
of `w` on `[0, ζ]` (`w` continuous before `ζ`, `w 0 = 0`) and `η` a path in the sphere whose range has `0` in its
closure. If every interior point `α(q)` at a rational own time `q < ζ` is visited by `η`, then every point `α(r)`,
`r ≤ ζ`, lies in the closure of the range of `η` (the finite-horizon form of GB6's final assertion). -/
theorem mem_closure_of_dense_contacts {η : ℝ≥0 → OnePoint ℂ} {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {α : ℝ≥0 → ℂ}
    (hα : IsGeneratingTrace w ζ α) (hw : ContinuousOn w {s | (s : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0)
    (h0 : ((0 : ℂ) : OnePoint ℂ) ∈ closure (range η))
    (hfc : ∀ q : ℚ, ((q : ℝ).toNNReal : ℝ≥0∞) < ζ → α (q : ℝ).toNNReal ∈ H →
      ((α (q : ℝ).toNNReal : ℂ) : OnePoint ℂ) ∈ range η)
    {r : ℝ≥0} (hr : (r : ℝ≥0∞) ≤ ζ) : ((α r : ℂ) : OnePoint ℂ) ∈ closure (range η) := by
  rcases eq_or_ne r 0 with rfl | hr0
  · rw [hα.1]
    exact h0
  set G : Set ℝ≥0 := {s | ∃ q : ℚ, (q : ℝ).toNNReal = s ∧ (s : ℝ≥0∞) < ζ ∧ α s ∈ H} with hG
  have hGsub : G ⊆ {s | (s : ℝ≥0∞) ≤ ζ} := fun s ⟨_, _, hs, _⟩ => hs.le
  have hrG : r ∈ closure G := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    set e : ℝ≥0 := ⟨ε / 2, by linarith⟩ with he_def
    have he : 0 < e := by
      rw [← NNReal.coe_pos]
      show (0 : ℝ) < ε / 2
      linarith
    obtain ⟨q, hq1, hq2, hq3, hq4⟩ :=
      exists_rat_mem_H_btwn hα hw hw0 (tsub_lt_self (pos_iff_ne_zero.2 hr0) he) hr
    refine ⟨_, ⟨q, rfl, hq3, hq4⟩, ?_⟩
    rw [NNReal.dist_eq]
    have h1 : (r : ℝ) - ε / 2 ≤ ((r - e : ℝ≥0) : ℝ) := by
      rw [NNReal.coe_sub_def]
      exact le_max_left _ _
    have h2 : (((q : ℝ).toNNReal : ℝ≥0) : ℝ) < r := hq2
    have h3 : ((r - e : ℝ≥0) : ℝ) < (((q : ℝ).toNNReal : ℝ≥0) : ℝ) := hq1
    rw [abs_of_pos (by linarith)]
    linarith
  have hcont : ContinuousWithinAt (fun s => ((α s : ℂ) : OnePoint ℂ)) G r :=
    ((OnePoint.continuous_coe.comp_continuousOn hα.2.1) r hr).mono hGsub
  refine closure_mono ?_ (hcont.mem_closure_image hrG)
  rintro _ ⟨s, ⟨q, rfl, hq, hqH⟩, rfl⟩
  exact hfc q hq hqH

end CounterflowRange
end Theorem14
end InteractingSLE
