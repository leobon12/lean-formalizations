/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BjImg
import InteractingSLE.Spec.Supplement.GB6HullIdRule

/-!
# The exit of the image state from an open buffer, as a path rule (near facts, the stop rule)

Packet PROVE-GW2-BUF (round 7, decision D12). The near stop is the first time the image state of the comparison
driver leaves the near buffer (an open set), capped at a deterministic time. For fixed marks and a fixed open buffer
`B`, with the comparison driver the scaled path `s ↦ b · w (s / a)` read at comparison time `a · u`:

* `scaledPath a b w`; `bufGauge xL xR B a b` (the distance of the read image state to `Bᶜ`): **`isCausal_bufGauge`**,
  **`measurable_bufGauge`**;
* `exitRule xL xR B a b c := hitRule (bufGauge …) 0 c`: **`isPathRule_exitRule`**, **`measurable_exitRule`**;
* `continuous_imgState` (the image state of a continuous driver is continuous in time);
* **`exitRule_spec`**: along a continuous path whose image state starts in `B`, the rule is the first exit capped at `c`
  (`gaugeStop`). It is positive, and when it is below the cap the image state is outside `B` there.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2Bh

open Exist.StagedLaw Supp8.GB6 Supp8.GB6.HullId Supp8.GB6.RelDrv.Version MartChar.RealFlow

variable {nL nR : ℕ}

/-- The comparison driver of a path: `s ↦ b · w (s / a)`. -/
def scaledPath (a : ℝ≥0) (b : ℝ) (w : ℝ≥0 → ℝ) : ℝ≥0 → ℝ := fun s => b * w (s / a)

theorem measurable_scaledPath (a : ℝ≥0) (b : ℝ) : Measurable (scaledPath a b) :=
  measurable_pi_iff.2 fun _ => measurable_const.mul (measurable_pi_apply _)

theorem continuous_scaledPath (a : ℝ≥0) (b : ℝ) {w : ℝ≥0 → ℝ} (hw : Continuous w) :
    Continuous (scaledPath a b w) :=
  continuous_const.mul (hw.comp (continuous_id.div_const a))

/-- **The buffer gauge**: the distance of the read image state of the comparison driver to the complement of `B`. -/
def bufGauge (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (B : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))) (a : ℝ≥0) (b : ℝ) :
    GaugeReadout :=
  fun u p => Metric.infDist (imgStateRead xL xR (a * u) (scaledPath a b p.2)) Bᶜ

theorem isCausal_bufGauge (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (B : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)))
    {a : ℝ≥0} (ha : 0 < a) (b : ℝ) : IsCausal (bufGauge xL xR B a b) := by
  intro u r w w' h
  unfold bufGauge
  rw [imgStateRead_congr xL xR (a * u) fun s hs => ?_]
  have hsu : s / a ≤ u := (div_le_iff₀ ha).2 (by rwa [mul_comm])
  simp only [scaledPath, h _ hsu]

theorem measurable_bufGauge (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (B : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)))
    (a : ℝ≥0) (b : ℝ) (u : ℝ≥0) : Measurable (bufGauge xL xR B a b u) :=
  (Metric.continuous_infDist_pt _).measurable.comp
    ((measurable_imgStateRead xL xR (a * u)).comp ((measurable_scaledPath a b).comp measurable_snd))

/-- **The exit rule**: the attained first time the buffer gauge vanishes, capped at `c`. -/
def exitRule (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (B : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))) (a : ℝ≥0) (b : ℝ)
    (c : ℝ≥0) : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞ :=
  hitRule (bufGauge xL xR B a b) (fun _ => 0) c

theorem isPathRule_exitRule (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (B : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)))
    {a : ℝ≥0} (ha : 0 < a) (b : ℝ) (c : ℝ≥0) : IsPathRule (exitRule xL xR B a b c) :=
  isPathRule_hitRule (isCausal_bufGauge xL xR B ha b)

theorem measurable_exitRule (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (B : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)))
    (a : ℝ≥0) (b : ℝ) (c : ℝ≥0) : Measurable (exitRule xL xR B a b c) :=
  measurable_hitRule (measurable_bufGauge xL xR B a b) measurable_const

/-- **The image state of a continuous driver is continuous in time.** -/
theorem continuous_imgState (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) {W : ℝ≥0 → ℝ} (hW : Continuous W) :
    Continuous fun t : ℝ≥0 => GW2Sdg.imgState xL xR W t := by
  refine continuous_iff_continuousAt.2 fun t₀ => ?_
  set V : ℝ≥0 := t₀ + 1
  have hV : ContinuousOn W (Iic V) := hW.continuousOn
  have hfr : Continuous (frozenDrive W V) := continuous_frozenDrive (by rwa [Real.toNNReal_coe])
  have hon : ContinuousOn (fun t : ℝ≥0 => GW2Sdg.imgState xL xR W t) (Iio V) := by
    have he : ∀ t ∈ Iio V, GW2Sdg.imgState xL xR W t =
        (W t, fun i => -rightImg (fun s => -frozenDrive W V s) (-xL i) t,
          fun j => rightImg (frozenDrive W V) (xR j) t) := by
      intro t ht
      unfold GW2Sdg.imgState
      have hk := fun x => GW2Sdg.rightImg_frozenDrive_eq hV (le_of_lt ht) x
      simp only [(hk _).1, (hk _).2]
    refine ContinuousOn.congr ?_ he
    have hci : ∀ (U : ℝ → ℝ), Continuous U → ∀ x, Continuous fun t : ℝ≥0 => rightImg U x t := by
      intro U hU x
      exact (continuousOn_rightImg hU x).comp_continuous NNReal.continuous_coe fun t => t.coe_nonneg
    refine (hW.continuousOn).prodMk ((continuous_pi fun i => ?_).continuousOn.prodMk
      (continuous_pi fun j => ?_).continuousOn)
    · exact (hci _ hfr.neg (-xL i)).neg
    · exact hci _ hfr (xR j)
  exact hon.continuousAt (Iio_mem_nhds (lt_add_one t₀))

/-- **The exit rule along a continuous path**: positive, the capped first exit, and outside the buffer at an exit
below the cap. -/
theorem exitRule_spec (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) {B : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))}
    (hB : IsOpen B) (hBc : (Bᶜ).Nonempty) (a : ℝ≥0) (b : ℝ) {c : ℝ≥0} (hc : 0 < c) (r : RecData)
    {w : ℝ≥0 → ℝ} (hw : Continuous w) (h0 : GW2Sdg.imgState xL xR (scaledPath a b w) 0 ∈ B) :
    ∃ τ : ℝ≥0, exitRule xL xR B a b c (r, w) = τ ∧ 0 < τ ∧ τ ≤ c ∧
      (τ < c → GW2Sdg.imgState xL xR (scaledPath a b w) (a * τ) ∉ B) := by
  have hsw := continuous_scaledPath a b hw
  set g : ℝ≥0 → ℝ := fun u => Metric.infDist (GW2Sdg.imgState xL xR (scaledPath a b w) (a * u)) Bᶜ with hg
  have hgc : Continuous g :=
    (Metric.continuous_infDist_pt _).comp ((continuous_imgState xL xR hsw).comp (continuous_const.mul continuous_id))
  have hcl : IsClosed (Bᶜ) := hB.isClosed_compl
  have hg0 : (fun _ : RecData => (0 : ℝ)) r < g 0 := by
    simp only [hg, mul_zero]
    exact (hcl.notMem_iff_infDist_pos hBc).1 fun h => h h0
  have hread : ∀ u ≤ gaugeStop g ((fun _ : RecData => (0 : ℝ)) r) c,
      bufGauge xL xR B a b u (r, w) = g u := fun u _ => by
    simp only [bufGauge, hg]
    rw [imgStateRead_eq xL xR hsw.continuousOn]
  refine ⟨gaugeStop g 0 c, hitRule_eq_gaugeStop hgc hc hg0 hread, gaugeStop_pos hgc hc hg0, gaugeStop_le _ _ _,
    fun hlt => ?_⟩
  have hm := gaugeStop_mem hgc hlt
  have hz : Metric.infDist (GW2Sdg.imgState xL xR (scaledPath a b w) (a * gaugeStop g 0 c)) Bᶜ = 0 :=
    le_antisymm hm Metric.infDist_nonneg
  have hmem := (Metric.mem_closure_iff_infDist_zero hBc).2 hz
  rw [hcl.closure_eq] at hmem
  exact hmem

end InteractingSLE.Theorem14.GW2Bh
