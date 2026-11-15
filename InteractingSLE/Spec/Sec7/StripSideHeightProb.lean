/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Exist.StagedLaw3Main
import InteractingSLE.Spec.Exist.StagedLawMain
import InteractingSLE.Spec.Sec7.StripSys
import InteractingSLE.Spec.Sec7.Lemma72BChart
import InteractingSLE.GFF.PushforwardLoewner
import InteractingSLE.Spec.Jordan.Transport
import InteractingSLE.Spec.Sec7.StripSideHeight
import InteractingSLE.Spec.Supplement.LPTrace
import InteractingSLE.Spec.Sec7.Lemma72DHull
import InteractingSLE.GFF.PushforwardLaw
import InteractingSLE.Spec.Restart.R1Glue
import InteractingSLE.Spec.Coupling.WholeField8Flow

/-!
# (S), probabilistic half, step 1: the composite chart after a stopped continuation

Packet PROVE-STRIPSYS16. Specification §7.4, proof of Aux. lemma 130, (RS13.3) (`source/spec/p385-432.md` L440–L456,
p. 411): "In each own chart the right-side height is `λ − θχ`, with its inherited derivative-logarithm lift", for the
angle-varying path `α = η^{1,∞}_{−π/2,θ₁}` after its change time. The staged history (frozen `IsStagedHistory`)
describes the continuation only through its conditional law given the retained past; its consequence at the level of
`P` is the landed single-stage law `Exist.StagedLaw.post_stage`: given the retained records of both pieces, the field
read in the chart **after** the stopped continuation is Gaussian with the stop word's mean.

That chart is the composite `(recChart r₀).trans (recChart r₁)` of the two record charts. This file proves that, on
the domain, it **is** the Loewner chart of the concatenated record driver (`catPath`), so that the landed measurability
of Loewner charts at random times (`Chart.loewnerChartAtTime`) applies to it:

* `catPath w₀ T₀ w₁`: `w₀` up to `T₀`, then `w₀ T₀ + w₁ (· − T₀)`; `continuous_catPath`, `restartDrv_catPath`;
* **`trans_loewner_inv_eq`**: the inverse maps agree on `ℍ` (QuantumZipper's flow property of the inverse maps);
* **`trans_loewner_fwd_eq`**, **`trans_loewner_lift_eq`**: the forward maps and the lifts agree on the domain
  (`StripSideHeight.restart_flow`);
* `IsChartTransport.congr_chart`: the frozen chart relation only reads the chart through its inverse on `ℍ` and its
  forward map and lift on the domain.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H fwdMap fwdMapInv fwdHull logDerivFwd chiC)
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec7

namespace StripSideHeightProb

open StripSideHeight

universe u

/-! ### The concatenated driver -/

section Cat

variable {w₀ w₁ : ℝ≥0 → ℝ} {T₀ : ℝ≥0}

/-- **The concatenated driver**: `w₀` up to `T₀`, then `w₀ T₀ + w₁ (· − T₀)`. -/
def catPath (w₀ : ℝ≥0 → ℝ) (T₀ : ℝ≥0) (w₁ : ℝ≥0 → ℝ) : ℝ≥0 → ℝ :=
  fun t => if t ≤ T₀ then w₀ t else w₀ T₀ + w₁ (t - T₀)

theorem catPath_of_le {t : ℝ≥0} (ht : t ≤ T₀) : catPath w₀ T₀ w₁ t = w₀ t := by
  simp only [catPath, ht, ↓reduceIte]

theorem catPath_zero (h0 : w₀ 0 = 0) : catPath w₀ T₀ w₁ 0 = 0 := by
  rw [catPath_of_le (zero_le (a := T₀)), h0]

theorem continuous_catPath (h₀ : Continuous w₀) (h₁ : Continuous w₁) (h10 : w₁ 0 = 0) :
    Continuous (catPath w₀ T₀ w₁) := by
  refine Continuous.if_le h₀ (continuous_const.add (h₁.comp (continuous_id.sub continuous_const)))
    continuous_id continuous_const ?_
  intro t ht
  rw [ht, tsub_self, h10, add_zero]

/-- After `T₀` the concatenation restarts with `w₁`. -/
theorem restartDrv_catPath (h10 : w₁ 0 = 0) : restartDrv (catPath w₀ T₀ w₁) T₀ = w₁ := by
  funext s
  unfold restartDrv
  rcases eq_or_ne s 0 with rfl | hs
  · rw [add_zero, sub_self, h10]
  · have hlt : ¬ T₀ + s ≤ T₀ := fun h => hs (le_antisymm (by simpa using h) (zero_le (a := s)))
    rw [catPath_of_le le_rfl]
    simp only [catPath, hlt, ↓reduceIte, add_tsub_cancel_left]

theorem rpath_catPath_eqOn : EqOn (Ito.rpath (catPath w₀ T₀ w₁)) (Ito.rpath w₀) (Icc 0 (T₀ : ℝ)) := by
  intro x hx
  simp only [Ito.rpath]
  exact catPath_of_le (Real.toNNReal_le_iff_le_coe.2 hx.2)

theorem shiftDrive_rpath_catPath_eqOn (h10 : w₁ 0 = 0) (T₁ : ℝ) :
    EqOn (QuantumZipper.RS.shiftDrive (Ito.rpath (catPath w₀ T₀ w₁)) T₀) (Ito.rpath w₁) (Icc 0 T₁) := by
  intro x hx
  have h := congrFun (restartDrv_catPath (w₀ := w₀) (T₀ := T₀) h10) x.toNNReal
  simp only [restartDrv] at h
  simp only [QuantumZipper.RS.shiftDrive, Ito.rpath]
  rw [Real.toNNReal_add T₀.coe_nonneg hx.1, Real.toNNReal_coe] at *
  rw [← h]

end Cat

/-! ### The composite chart is the Loewner chart of the concatenation -/

section Chart

variable {w₀ w₁ : ℝ≥0 → ℝ} {T₀ T₁ : ℝ≥0}

/-- The composite of the Loewner charts of `w₀` at `T₀` and of `w₁` at `T₁` (the chart after two stages). -/
abbrev twoChart (w₀ : ℝ≥0 → ℝ) (T₀ : ℝ≥0) (w₁ : ℝ≥0 → ℝ) (T₁ : ℝ≥0) : Chart :=
  (Chart.id.loewner (Ito.rpath w₀) T₀).trans (Chart.id.loewner (Ito.rpath w₁) T₁)

/-- The Loewner chart of the concatenated driver at `T₀ + T₁`. -/
abbrev catChart (w₀ : ℝ≥0 → ℝ) (T₀ : ℝ≥0) (w₁ : ℝ≥0 → ℝ) (T₁ : ℝ≥0) : Chart :=
  Chart.id.loewner (Ito.rpath (catPath w₀ T₀ w₁)) ((T₀ + T₁ : ℝ≥0) : ℝ)

theorem continuous_rpath_catPath (h₀ : Continuous w₀) (h₁ : Continuous w₁) (h10 : w₁ 0 = 0) :
    Continuous (Ito.rpath (catPath w₀ T₀ w₁)) :=
  (continuous_catPath h₀ h₁ h10).comp continuous_real_toNNReal

theorem rpath_catPath_zero (h00 : w₀ 0 = 0) : Ito.rpath (catPath w₀ T₀ w₁) 0 = 0 := by
  simp [Ito.rpath, catPath_zero (T₀ := T₀) (w₁ := w₁) h00]

/-- **The inverse maps agree on `ℍ`**: `f_{T₀}⁻¹ ∘ (f'_{T₁})⁻¹ = f_{T₀+T₁}⁻¹` for the concatenation. -/
theorem twoChart_inv_eq (h₀ : Continuous w₀) (h00 : w₀ 0 = 0) (h₁ : Continuous w₁) (h10 : w₁ 0 = 0)
    {w : ℂ} (hw : w ∈ H) : (twoChart w₀ T₀ w₁ T₁).2.1 w = (catChart w₀ T₀ w₁ T₁).2.1 w := by
  change fwdMapInv (Ito.rpath w₀) T₀ (fwdMapInv (Ito.rpath w₁) T₁ w) =
    fwdMapInv (Ito.rpath (catPath w₀ T₀ w₁)) ((T₀ + T₁ : ℝ≥0) : ℝ) w
  have hc := continuous_rpath_catPath (T₀ := T₀) h₀ h₁ h10
  have hc0 := rpath_catPath_zero (T₀ := T₀) (w₁ := w₁) h00
  have hr₀ : Continuous (Ito.rpath w₀) := h₀.comp continuous_real_toNNReal
  have hr₁ : Continuous (Ito.rpath w₁) := h₁.comp continuous_real_toNNReal
  have hr₀0 : Ito.rpath w₀ 0 = 0 := by simp [Ito.rpath, h00]
  have hr₁0 : Ito.rpath w₁ 0 = 0 := by simp [Ito.rpath, h10]
  rw [NNReal.coe_add, QuantumZipper.RS.fwdMapInv_add_shift hc hc0 T₀.coe_nonneg T₁.coe_nonneg hw]
  have e1 : fwdMapInv (QuantumZipper.RS.shiftDrive (Ito.rpath (catPath w₀ T₀ w₁)) T₀) T₁ w =
      fwdMapInv (Ito.rpath w₁) T₁ w :=
    LP.fwdMapInv_eq_of_eqOn_Icc (QuantumZipper.RS.continuous_shiftDrive hc _) hr₁
      (QuantumZipper.RS.shiftDrive_zero _ _) hr₁0 T₁.coe_nonneg (shiftDrive_rpath_catPath_eqOn h10 T₁) hw
  rw [e1]
  exact (LP.fwdMapInv_eq_of_eqOn_Icc hc hr₀ hc0 hr₀0 T₀.coe_nonneg rpath_catPath_eqOn
    (QuantumZipper.RS.fwdMapInv_mem_H hr₁ hr₁0 T₁.coe_nonneg hw)).symm

theorem mem_H_diff_fwdHull_of_mem_dom {w : ℝ → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {t : ℝ} (ht : 0 ≤ t)
    {z : ℂ} (hz : z ∈ (Chart.id.loewner w t).dom) : z ∈ H \ fwdHull w t := by
  rw [Chart.mem_dom_loewner_iff hw hw0 ht] at hz
  obtain ⟨hz, u, hu⟩ := hz
  exact ⟨hz, Ito.notMem_fwdHull_of_isForwardSol hw hz ht hu⟩

/-- **The forward maps and the lifts agree on the domain** of the concatenated chart. -/
theorem twoChart_fwd_lift_eq (h₀ : Continuous w₀) (h00 : w₀ 0 = 0) (h₁ : Continuous w₁) (h10 : w₁ 0 = 0)
    {z : ℂ} (hz : z ∈ (catChart w₀ T₀ w₁ T₁).dom) :
    (twoChart w₀ T₀ w₁ T₁).1 z = (catChart w₀ T₀ w₁ T₁).1 z ∧
      (twoChart w₀ T₀ w₁ T₁).2.2 z = (catChart w₀ T₀ w₁ T₁).2.2 z := by
  have hc := continuous_rpath_catPath (T₀ := T₀) h₀ h₁ h10
  have hc0 := rpath_catPath_zero (T₀ := T₀) (w₁ := w₁) h00
  have hz' := mem_H_diff_fwdHull_of_mem_dom hc hc0 (T₀ + T₁ : ℝ≥0).coe_nonneg hz
  have hcat : ContinuousOn (catPath w₀ T₀ w₁) {t | (t : ℝ≥0∞) < ⊤} :=
    (continuous_catPath h₀ h₁ h10).continuousOn
  obtain ⟨-, hf, hL⟩ := restart_flow hcat (catPath_zero h00) (ENNReal.coe_lt_top (r := T₀ + T₁)) hz'
  rw [restartDrv_catPath h10] at hf hL
  have hr₀ : EqOn (fun s : ℝ => catPath w₀ T₀ w₁ s.toNNReal) (Ito.rpath w₀) (Icc 0 (T₀ : ℝ)) :=
    rpath_catPath_eqOn
  have hf0 : fwdMap (fun s : ℝ => catPath w₀ T₀ w₁ s.toNNReal) T₀ z = fwdMap (Ito.rpath w₀) T₀ z :=
    Ito.fwdMap_congr_of_eqOn hr₀
  have hL0 : logDerivFwd (fun s : ℝ => catPath w₀ T₀ w₁ s.toNNReal) T₀ z = logDerivFwd (Ito.rpath w₀) T₀ z :=
    Ito.logDerivFwd_congr_of_eqOn hr₀ T₀.coe_nonneg le_rfl
  refine ⟨?_, ?_⟩
  · change fwdMap (Ito.rpath w₁) T₁ (fwdMap (Ito.rpath w₀) T₀ z) =
      fwdMap (Ito.rpath (catPath w₀ T₀ w₁)) ((T₀ + T₁ : ℝ≥0) : ℝ) z
    rw [← hf0]
    exact hf.symm
  · have key : logDerivFwd (Ito.rpath (catPath w₀ T₀ w₁)) ((T₀ + T₁ : ℝ≥0) : ℝ) z =
        logDerivFwd (Ito.rpath w₀) T₀ z + logDerivFwd (Ito.rpath w₁) T₁ (fwdMap (Ito.rpath w₀) T₀ z) := by
      change logDerivFwd (fun s : ℝ => catPath w₀ T₀ w₁ s.toNNReal) ((T₀ + T₁ : ℝ≥0) : ℝ) z = _
      rw [hL, hL0, hf0]
      rfl
    change (logDerivFwd (Ito.rpath w₁) T₁ (fwdMap (Ito.rpath w₀) T₀ z)).im + 0 +
        ((logDerivFwd (Ito.rpath w₀) T₀ z).im + 0) =
      (logDerivFwd (Ito.rpath (catPath w₀ T₀ w₁)) ((T₀ + T₁ : ℝ≥0) : ℝ) z).im + 0
    rw [key, Complex.add_im]
    ring

end Chart

/-! ### Measurability of the two-stage chart of random drivers -/

section Meas

variable {Ω : Type*} (𝓗 : MeasurableSpace Ω) {W0 W1 : Ω → ℝ≥0 → ℝ} {t₀ r : ℝ≥0}

omit 𝓗 in
theorem twoChart_dom_eq {w₀ w₁ : ℝ≥0 → ℝ} {T₀ T₁ : ℝ≥0} (h₀ : Continuous w₀) (h00 : w₀ 0 = 0)
    (h₁ : Continuous w₁) (h10 : w₁ 0 = 0) : (twoChart w₀ T₀ w₁ T₁).dom = (catChart w₀ T₀ w₁ T₁).dom := by
  have e : (twoChart w₀ T₀ w₁ T₁).2.1 '' H = (catChart w₀ T₀ w₁ T₁).2.1 '' H :=
    image_congr fun w hw => twoChart_inv_eq h₀ h00 h₁ h10 hw
  ext z
  change z ∈ interior ((twoChart w₀ T₀ w₁ T₁).2.1 '' H) ↔ z ∈ interior ((catChart w₀ T₀ w₁ T₁).2.1 '' H)
  rw [e]

omit 𝓗 in
theorem isConformal_twoChart {w₀ w₁ : ℝ≥0 → ℝ} {T₀ T₁ : ℝ≥0} (h₀ : Continuous w₀) (h00 : w₀ 0 = 0)
    (h₁ : Continuous w₁) (h10 : w₁ 0 = 0) : (twoChart w₀ T₀ w₁ T₁).IsConformal :=
  (Chart.isConformal_id.loewner (h₀.comp continuous_real_toNNReal) (by simp [h00]) T₀.coe_nonneg).trans
    (Chart.isConformal_id.loewner (h₁.comp continuous_real_toNNReal) (by simp [h10]) T₁.coe_nonneg)

omit 𝓗 in
theorem mem_dom_catChart_iff {w₀ w₁ : ℝ≥0 → ℝ} {T₀ T₁ : ℝ≥0} (h₀ : Continuous w₀) (h00 : w₀ 0 = 0)
    (h₁ : Continuous w₁) (h10 : w₁ 0 = 0) {z : ℂ} :
    z ∈ (catChart w₀ T₀ w₁ T₁).dom ↔ z ∈ H \ fwdHull (Ito.rpath (catPath w₀ T₀ w₁)) ((T₀ + T₁ : ℝ≥0) : ℝ) := by
  have hc := continuous_rpath_catPath (T₀ := T₀) h₀ h₁ h10
  have hc0 := rpath_catPath_zero (T₀ := T₀) (w₁ := w₁) h00
  refine ⟨mem_H_diff_fwdHull_of_mem_dom hc hc0 (T₀ + T₁ : ℝ≥0).coe_nonneg, fun hz => ?_⟩
  rw [Chart.mem_dom_loewner_iff hc hc0 (T₀ + T₁ : ℝ≥0).coe_nonneg]
  exact ⟨hz.1, Ito.exists_isForwardSol_of_mem (T₀ + T₁ : ℝ≥0).coe_nonneg hz⟩

variable (hW0c : ∀ ω, Continuous (W0 ω)) (hW00 : ∀ ω, W0 ω 0 = 0) (hW1c : ∀ ω, Continuous (W1 ω))
  (hW10 : ∀ ω, W1 ω 0 = 0) (hW0m : ∀ s, Measurable[𝓗] fun ω => W0 ω s)
  (hW1m : ∀ s, Measurable[𝓗] fun ω => W1 ω s)

/-- The concatenated driver family. -/
abbrev catW (W0 : Ω → ℝ≥0 → ℝ) (t₀ : ℝ≥0) (W1 : Ω → ℝ≥0 → ℝ) : ℝ≥0 → Ω → ℝ :=
  fun t ω => catPath (W0 ω) t₀ (W1 ω) t

include hW0m hW1m in
theorem measurable_catW_apply (s : ℝ≥0) : Measurable[𝓗] (catW W0 t₀ W1 s) := by
  by_cases hs : s ≤ t₀
  · have e : catW W0 t₀ W1 s = fun ω => W0 ω s := funext fun ω => catPath_of_le hs
    rw [e]
    exact hW0m s
  · have e : catW W0 t₀ W1 s = fun ω => W0 ω t₀ + W1 ω (s - t₀) := funext fun ω => by
      simp only [catW, catPath, hs, ↓reduceIte]
    rw [e]
    exact (hW0m t₀).add (hW1m _)

include hW0c hW00 hW1c hW10 hW0m hW1m

theorem measurableSet_mem_dom_catChart (z : ℂ) :
    MeasurableSet[𝓗] {ω | z ∈ (catChart (W0 ω) t₀ (W1 ω) r).dom} :=
  Chart.measurableSet_mem_dom_loewnerChartAtTime (W := catW W0 t₀ W1) (τ := fun _ => t₀ + r) le_rfl
    (fun ω => continuous_catPath (hW0c ω) (hW1c ω) (hW10 ω)) (fun ω => catPath_zero (hW00 ω))
    measurable_const (fun _ => measurable_catW_apply 𝓗 hW0m hW1m _) z

theorem measurable_indicator_fwd_catChart (z : ℂ) :
    Measurable[𝓗] ({ω | z ∈ (catChart (W0 ω) t₀ (W1 ω) r).dom}.indicator
      fun ω => (catChart (W0 ω) t₀ (W1 ω) r).1 z) :=
  Chart.measurable_indicator_fwd_loewnerChartAtTime (W := catW W0 t₀ W1) (τ := fun _ => t₀ + r) le_rfl
    (fun ω => continuous_catPath (hW0c ω) (hW1c ω) (hW10 ω)) (fun ω => catPath_zero (hW00 ω))
    measurable_const (fun _ => measurable_catW_apply 𝓗 hW0m hW1m _) z

theorem measurable_indicator_lift_catChart (z : ℂ) :
    Measurable[𝓗] ({ω | z ∈ (catChart (W0 ω) t₀ (W1 ω) r).dom}.indicator
      fun ω => (catChart (W0 ω) t₀ (W1 ω) r).2.2 z) :=
  Chart.measurable_indicator_lift_loewnerChartAtTime (W := catW W0 t₀ W1) (τ := fun _ => t₀ + r) le_rfl
    (fun ω => continuous_catPath (hW0c ω) (hW1c ω) (hW10 ω)) (fun ω => catPath_zero (hW00 ω))
    measurable_const (fun _ => measurable_catW_apply 𝓗 hW0m hW1m _) z

/-- **The domain events of the two-stage chart.** -/
theorem measurableSet_mem_dom_twoChart (z : ℂ) :
    MeasurableSet[𝓗] {ω | z ∈ (twoChart (W0 ω) t₀ (W1 ω) r).dom} := by
  have e : {ω | z ∈ (twoChart (W0 ω) t₀ (W1 ω) r).dom} = {ω | z ∈ (catChart (W0 ω) t₀ (W1 ω) r).dom} := by
    ext ω
    simp only [mem_ofPred_eq, twoChart_dom_eq (hW0c ω) (hW00 ω) (hW1c ω) (hW10 ω)]
  rw [e]
  exact measurableSet_mem_dom_catChart 𝓗 hW0c hW00 hW1c hW10 hW0m hW1m z

/-- **The masked forward maps of the two-stage chart.** -/
theorem measurable_indicator_fwd_twoChart (z : ℂ) :
    Measurable[𝓗] ({ω | z ∈ (twoChart (W0 ω) t₀ (W1 ω) r).dom}.indicator
      fun ω => (twoChart (W0 ω) t₀ (W1 ω) r).1 z) := by
  have e : ({ω | z ∈ (twoChart (W0 ω) t₀ (W1 ω) r).dom}.indicator
      fun ω => (twoChart (W0 ω) t₀ (W1 ω) r).1 z) = {ω | z ∈ (catChart (W0 ω) t₀ (W1 ω) r).dom}.indicator
      fun ω => (catChart (W0 ω) t₀ (W1 ω) r).1 z := by
    funext ω
    by_cases hz : z ∈ (catChart (W0 ω) t₀ (W1 ω) r).dom
    · have hz' : z ∈ (twoChart (W0 ω) t₀ (W1 ω) r).dom := by
        rw [twoChart_dom_eq (hW0c ω) (hW00 ω) (hW1c ω) (hW10 ω)]; exact hz
      rw [indicator_of_mem (show ω ∈ {ω | z ∈ (twoChart (W0 ω) t₀ (W1 ω) r).dom} from hz'),
        indicator_of_mem (show ω ∈ {ω | z ∈ (catChart (W0 ω) t₀ (W1 ω) r).dom} from hz)]
      exact (twoChart_fwd_lift_eq (hW0c ω) (hW00 ω) (hW1c ω) (hW10 ω) hz).1
    · have hz' : z ∉ (twoChart (W0 ω) t₀ (W1 ω) r).dom := by
        rw [twoChart_dom_eq (hW0c ω) (hW00 ω) (hW1c ω) (hW10 ω)]; exact hz
      rw [indicator_of_notMem (show ω ∉ {ω | z ∈ (twoChart (W0 ω) t₀ (W1 ω) r).dom} from hz'),
        indicator_of_notMem (show ω ∉ {ω | z ∈ (catChart (W0 ω) t₀ (W1 ω) r).dom} from hz)]
  rw [e]
  exact measurable_indicator_fwd_catChart 𝓗 hW0c hW00 hW1c hW10 hW0m hW1m z

/-- **The masked lifts of the two-stage chart.** -/
theorem measurable_indicator_lift_twoChart (z : ℂ) :
    Measurable[𝓗] ({ω | z ∈ (twoChart (W0 ω) t₀ (W1 ω) r).dom}.indicator
      fun ω => (twoChart (W0 ω) t₀ (W1 ω) r).2.2 z) := by
  have e : ({ω | z ∈ (twoChart (W0 ω) t₀ (W1 ω) r).dom}.indicator
      fun ω => (twoChart (W0 ω) t₀ (W1 ω) r).2.2 z) = {ω | z ∈ (catChart (W0 ω) t₀ (W1 ω) r).dom}.indicator
      fun ω => (catChart (W0 ω) t₀ (W1 ω) r).2.2 z := by
    funext ω
    by_cases hz : z ∈ (catChart (W0 ω) t₀ (W1 ω) r).dom
    · have hz' : z ∈ (twoChart (W0 ω) t₀ (W1 ω) r).dom := by
        rw [twoChart_dom_eq (hW0c ω) (hW00 ω) (hW1c ω) (hW10 ω)]; exact hz
      rw [indicator_of_mem (show ω ∈ {ω | z ∈ (twoChart (W0 ω) t₀ (W1 ω) r).dom} from hz'),
        indicator_of_mem (show ω ∈ {ω | z ∈ (catChart (W0 ω) t₀ (W1 ω) r).dom} from hz)]
      exact (twoChart_fwd_lift_eq (hW0c ω) (hW00 ω) (hW1c ω) (hW10 ω) hz).2
    · have hz' : z ∉ (twoChart (W0 ω) t₀ (W1 ω) r).dom := by
        rw [twoChart_dom_eq (hW0c ω) (hW00 ω) (hW1c ω) (hW10 ω)]; exact hz
      rw [indicator_of_notMem (show ω ∉ {ω | z ∈ (twoChart (W0 ω) t₀ (W1 ω) r).dom} from hz'),
        indicator_of_notMem (show ω ∉ {ω | z ∈ (catChart (W0 ω) t₀ (W1 ω) r).dom} from hz)]
  rw [e]
  exact measurable_indicator_lift_catChart 𝓗 hW0c hW00 hW1c hW10 hW0m hW1m z

omit hW0m hW1m in
/-- The lift of the two-stage chart is continuous on the domain. -/
theorem continuousOn_lift_twoChart (ω : Ω) :
    ContinuousOn (twoChart (W0 ω) t₀ (W1 ω) r).2.2 (twoChart (W0 ω) t₀ (W1 ω) r).dom := by
  have hc := continuous_rpath_catPath (T₀ := t₀) (hW0c ω) (hW1c ω) (hW10 ω)
  have hc0 := rpath_catPath_zero (T₀ := t₀) (w₁ := W1 ω) (hW00 ω)
  have hcont := Chart.continuousOn_lift_loewner hc hc0 (t₀ + r : ℝ≥0).coe_nonneg
  rw [twoChart_dom_eq (hW0c ω) (hW00 ω) (hW1c ω) (hW10 ω)]
  refine hcont.congr fun z hz => ?_
  exact (twoChart_fwd_lift_eq (hW0c ω) (hW00 ω) (hW1c ω) (hW10 ω) hz).2

/-- **Closed-disc events of the domain** (Lemma 7.2(D)'s avoidance events of a hull at a deterministic time). -/
theorem measurableSet_closedBall_subset_dom_twoChart (z : ℂ) (ε : ℝ) :
    MeasurableSet[𝓗] {ω | Metric.closedBall z ε ⊆ (twoChart (W0 ω) t₀ (W1 ω) r).dom} := by
  have e : {ω | Metric.closedBall z ε ⊆ (twoChart (W0 ω) t₀ (W1 ω) r).dom} =
      {ω | Metric.closedBall z ε ⊆ H ∧ Disjoint (Metric.closedBall z ε)
        (fwdHull (QuantumZipper.drive 1 (catW W0 t₀ W1) ω) ((t₀ + r : ℝ≥0) : ℝ))} := by
    ext ω
    have hdr : QuantumZipper.drive 1 (catW W0 t₀ W1) ω = Ito.rpath (catPath (W0 ω) t₀ (W1 ω)) := by
      funext s
      simp [QuantumZipper.drive, Ito.rpath]
    simp only [mem_ofPred_eq, twoChart_dom_eq (hW0c ω) (hW00 ω) (hW1c ω) (hW10 ω), hdr]
    constructor
    · intro hB
      refine ⟨fun y hy => ((mem_dom_catChart_iff (hW0c ω) (hW00 ω) (hW1c ω) (hW10 ω)).1 (hB hy)).1,
        Set.disjoint_left.2 fun y hy hK => ((mem_dom_catChart_iff (hW0c ω) (hW00 ω) (hW1c ω) (hW10 ω)).1
          (hB hy)).2 hK⟩
    · rintro ⟨hBH, hd⟩ y hy
      exact (mem_dom_catChart_iff (hW0c ω) (hW00 ω) (hW1c ω) (hW10 ω)).2
        ⟨hBH hy, Set.disjoint_left.1 hd hy⟩
  rw [e]
  rcases lt_or_ge ε 0 with hε | hε
  · have : Metric.closedBall z ε = ∅ := Metric.closedBall_eq_empty.2 hε
    convert MeasurableSet.univ using 1
    ext ω
    simp only [this, mem_ofPred_eq, mem_univ, iff_true]
    exact ⟨empty_subset _, disjoint_bot_left⟩
  rcases hε.eq_or_lt with rfl | hε
  · have hdom := measurableSet_mem_dom_catChart 𝓗 hW0c hW00 hW1c hW10 hW0m hW1m (t₀ := t₀) (r := r) z
    convert hdom using 1
    ext ω
    simp only [Metric.closedBall_zero, singleton_subset_iff, disjoint_singleton_left, mem_ofPred_eq,
      mem_dom_catChart_iff (hW0c ω) (hW00 ω) (hW1c ω) (hW10 ω)]
    have hdr : QuantumZipper.drive 1 (catW W0 t₀ W1) ω = Ito.rpath (catPath (W0 ω) t₀ (W1 ω)) := by
      funext s
      simp [QuantumZipper.drive, Ito.rpath]
    rw [hdr]
    rfl
  rcases lt_or_ge ε z.im with hz | hz
  · refine MeasurableSet.inter ?_ ?_
    · exact MeasurableSet.const _
    · exact Lemma72D.measurableSet_disjoint_closedBall_fwdHull_real
        (fun ω => continuous_catPath (hW0c ω) (hW1c ω) (hW10 ω)) (t₀ + r : ℝ≥0).coe_nonneg
        (fun _ _ => measurable_catW_apply 𝓗 hW0m hW1m _) hε hz
  · have hB : ¬ Metric.closedBall z ε ⊆ H := by
      intro hB
      have hmem : z - (ε : ℂ) * Complex.I ∈ Metric.closedBall z ε := by
        rw [Metric.mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_mul, Complex.norm_I,
          mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε]
      have := hB hmem
      simp only [H, mem_ofPred_eq, Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
        Complex.ofReal_im, Complex.I_re, mul_one, mul_zero, add_zero] at this
      linarith
    convert MeasurableSet.empty using 1
    ext ω
    simp only [hB, false_and, mem_ofPred_eq, mem_empty_iff_false]

end Meas

/-! ### The two-angle program stopped after the continuation -/

section Spec

open Exist Exist.Staged Exist.StagedLaw

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **The two-angle program with the continuation stopped at own time `r`**: angle `θ₀` for own time `t₀`, then
angle `θ` for own time `r` (the program `StripSys.twoAngleSpec θ₀ t₀ θ` with its second instruction stopped). -/
def stopSpec (θ₀ : ℝ) (t₀ : ℝ≥0) (θ : ℝ) (r : ℝ≥0) : ExplSpec :=
  (0, false, [Sum.inl (θ₀, (t₀ : ℝ≥0∞)), Sum.inl (θ, (r : ℝ≥0∞))])

theorem run_stopSpec_of_le_one (θ₀ : ℝ) (t₀ : ℝ≥0) (θ : ℝ) (r : ℝ≥0) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {k : ℕ}
    (hk : k ≤ 1) :
    ExplState.run κ b jumps (stopSpec θ₀ t₀ θ r) D k =
      ExplState.run κ b jumps (StripSys.twoAngleSpec θ₀ t₀ θ) D k := by
  interval_cases k <;> rfl

/-- The launch record of a flow step does not depend on the own time of the instruction. -/
theorem launches_flowStep_time (gw2 : Bool) (s : ExplState) (k : ℕ) (D : (ℝ≥0 → ℝ) × ℝ≥0∞) (θ : ℝ)
    (t t' : ℝ≥0∞) :
    (ExplState.flowStep κ b gw2 s k D θ t).2.2.2.1 = (ExplState.flowStep κ b gw2 s k D θ t').2.2.2.1 := by
  obtain ⟨pieces, arcs, retained, launches, chart, status, pt, angle, recR, recL⟩ := s
  unfold ExplState.flowStep
  dsimp only
  repeat' first
    | (rw [launches_launch, launches_launch])
    | rfl
    | split

theorem launches_run_two_stopSpec (θ₀ : ℝ) (t₀ : ℝ≥0) (θ : ℝ) (r : ℝ≥0) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    (ExplState.run κ b jumps (stopSpec θ₀ t₀ θ r) D 2).2.2.2.1 =
      (ExplState.run κ b jumps (StripSys.twoAngleSpec θ₀ t₀ θ) D 2).2.2.2.1 := by
  change (ExplState.step κ b jumps false D (ExplState.run κ b jumps (stopSpec θ₀ t₀ θ r) D 1)
      (Sum.inl (θ, (r : ℝ≥0∞)), 1)).2.2.2.1 = (ExplState.step κ b jumps false D
      (ExplState.run κ b jumps (StripSys.twoAngleSpec θ₀ t₀ θ) D 1) (Sum.inl (θ, ⊤), 1)).2.2.2.1
  rw [run_stopSpec_of_le_one θ₀ t₀ θ r D le_rfl]
  exact launches_flowStep_time (κ := κ) (b := b) false _ 1 (D 1) θ _ _

theorem pastSigma_stopSpec_of_le_one {Ω : Type*} (θ₀ : ℝ) (t₀ : ℝ≥0) (θ : ℝ) (r : ℝ≥0)
    (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) {k : ℕ} (hk : k ≤ 1) :
    pastSigma κ b jumps (stopSpec θ₀ t₀ θ r) E k = pastSigma κ b jumps (StripSys.twoAngleSpec θ₀ t₀ θ) E k := by
  unfold pastSigma
  congr 1
  funext ω i
  rw [run_stopSpec_of_le_one θ₀ t₀ θ r _ hk]

/-- **The first two stages of the staged history are stages of the stopped program.** -/
theorem stageOK_stopSpec {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {θ₀ : ℝ} {t₀ : ℝ≥0} {θ : ℝ}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hS : IsStagedHistory κ b jumps P h (StripSys.twoAngleSpec θ₀ t₀ θ) E)
    (r : ℝ≥0) {k : ℕ} (hk : k ≤ 1) : StageOK κ b jumps P h (stopSpec θ₀ t₀ θ r) E k := by
  have hl : ∀ D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞, (ExplState.run κ b jumps (stopSpec θ₀ t₀ θ r) D (k + 1)).2.2.2.1 k =
      (ExplState.run κ b jumps (StripSys.twoAngleSpec θ₀ t₀ θ) D (k + 1)).2.2.2.1 k := by
    intro D
    interval_cases k
    · rw [run_stopSpec_of_le_one θ₀ t₀ θ r D le_rfl]
    · rw [launches_run_two_stopSpec]
  filter_upwards [hS.2.2.2 k] with ω₀ hω₀ c θ' hcθ
  rw [hl] at hcθ
  rw [pastSigma_stopSpec_of_le_one θ₀ t₀ θ r E hk]
  exact hω₀ c θ' hcθ

/-- **The single-stage law with the explicit stop word** (the witness of the landed `stopCondLawStatement`). -/
theorem isStopLaw_stopWord {κ : ℝ} (hκ : 0 < κ) : IsStopLaw.{u} κ (stopWord κ) := by
  refine ⟨measurable_stopWord κ, isSorted_stopWord κ, fun c θ t Ω _ _ Q _ g E hE hreg hfl =>
    ⟨ae_isDrvGood_of_isFlowLineDriver hκ t hreg hfl, fun φ => ?_⟩⟩
  by_cases hseed : ForceWord.ThresholdCondition (flowLineRhoL κ c.fn c.jumps 0 θ) (flowLineRhoR κ c.fn c.jumps 0 θ) 0
      (flowLineXL c.fn c.jumps 0) (flowLineXR c.fn c.jumps 0)
  · filter_upwards [ae_condExp_recField_of_inadmissible hκ c θ t Q g E hE hreg hfl hseed φ] with ω h _ using h
  · exact ae_condExp_recField_of_admissible hκ c θ t Q g E hE hreg hfl hseed φ

end Spec

/-! ### The landed stage law after the stopped continuation -/

section Law

open Exist Exist.Staged Exist.StagedLaw Restart

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {θ₀ θ : ℝ}
  {t₀ : ℝ≥0} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- The launch event of the continuation (instruction `1`). -/
def launchOne (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (θ₀ : ℝ) (t₀ : ℝ≥0) (θ : ℝ) (r : ℝ≥0)
    (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) : Set Ω :=
  {ω | (ExplState.run κ b jumps (stopSpec θ₀ t₀ θ r) (fun j => E j ω) 2).2.2.2.1 1 ≠ none}

/-- The chart in which the continuation is launched (the state's chart after instruction `0`). -/
abbrev chartOne (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (θ₀ : ℝ) (t₀ : ℝ≥0) (θ : ℝ) (r : ℝ≥0)
    (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ω : Ω) : Chart :=
  (ExplState.run κ b jumps (stopSpec θ₀ t₀ θ r) (fun j => E j ω) 1).2.2.2.2.1

/-- **The stage law after the stopped continuation** (the landed `post_stage` for the stopped program): a word `β`
read off the past before the continuation and the field `Y` read in the launch chart such that, given the records of
both stopped pieces, the field read in the record chart of the continuation has the Gaussian characteristic functional
of the stop word `stopWord κ (β, θ, record)`. -/
theorem exists_stageLaw_stopSpec (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) (hS : IsStagedHistory κ b jumps P h (StripSys.twoAngleSpec θ₀ t₀ θ) E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) (r : ℝ≥0) :
    ∃ (β : Ω → BoundaryWord) (Y : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
      Measurable[pastSigma κ b jumps (stopSpec θ₀ t₀ θ r) E 1] β ∧ Measurable Y ∧
      (∀ᵐ ω ∂P, ω ∈ launchOne κ b jumps θ₀ t₀ θ r E →
        (chartOne κ b jumps θ₀ t₀ θ r E ω).IsConformal ∧
        ContinuousOn (fun w => (chartOne κ b jumps θ₀ t₀ θ r E ω).2.2 ((chartOne κ b jumps θ₀ t₀ θ r E ω).2.1 w))
          H ∧
        IsChartTransport (chartOne κ b jumps θ₀ t₀ θ r E ω) 1 0 (chiC κ) (h ω) (Y ω)) ∧
      ∀ ψ : LQGMetric.TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ launchOne κ b jumps θ₀ t₀ θ r E →
        P[fun ω' => Complex.exp (Complex.I *
            (recField κ (pastMap κ b jumps (stopSpec θ₀ t₀ θ r) E 2 ω' 1) (Y ω') ψ : ℂ)) |
          pastSigma κ b jumps (stopSpec θ₀ t₀ θ r) E 2] ω =
          gaussCF (stopWord κ (β ω, θ, pastMap κ b jumps (stopSpec θ₀ t₀ θ r) E 2 ω 1)) ψ := by
  have hβA := isStopLaw_stopWord.{u} hκ
  obtain ⟨β, Y, hβ, hY, hpath, hker⟩ := stageLaw (spec := stopSpec θ₀ t₀ θ r) (E := E) hβA runMeasStatement hκ
    hb hh 1 (fun j _ => hS.1 j) (fun j _ => hreg j) (fun j hj => stageOK_stopSpec hS r (by omega))
  have hpost := post_stage (spec := stopSpec θ₀ t₀ θ r) (E := E) (ℓ := 1) hβA runMeasStatement hκ hb hh
    (fun j _ => hS.1 j) (fun j _ => hreg j) (stageOK_stopSpec hS r le_rfl) hβ hY hpath hker
  refine ⟨β, Y, hβ, hY, hpath, fun ψ => ?_⟩
  filter_upwards [hpost.2 ψ] with ω hω hl
  have hfin : min (instrTime (stopSpec θ₀ t₀ θ r) 1) (E 1 ω).2 ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _)
  exact hω hl hfin

end Law

/-! ### The records and the launch chart -/

section Records

open Exist Exist.Staged Exist.StagedLaw Restart

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type*} {θ₀ θ : ℝ} {t₀ r : ℝ≥0}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- The driver read from a record (continuous, `0` at `0`). -/
abbrev recW (p : RecData) : ℝ≥0 → ℝ := LocalExt.histDrv (recHist p)

theorem launches_run_one_stopSpec (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    (ExplState.run κ b jumps (stopSpec θ₀ t₀ θ r) D 1).2.2.2.1 0 ≠ none := by
  change (ExplState.launch (ExplState.init 0) 0 (D 0) θ₀ (t₀ : ℝ≥0∞)).2.2.2.1 0 ≠ none
  rw [launches_launch, Function.update_self]
  exact Option.some_ne_none _

/-- **The first record** is the record of the first piece at its own time `t₀`. -/
theorem pastMap_two_zero (ω : Ω) :
    pastMap κ b jumps (stopSpec θ₀ t₀ θ r) E 2 ω 0 = recOf (t₀ : ℝ≥0∞) (E 0 ω) := by
  have h2 := congrFun (pastMap_succ (κ := κ) (b := b) (jumps := jumps) (stopSpec θ₀ t₀ θ r) E 1 ω) 0
  have h1 := congrFun (pastMap_succ (κ := κ) (b := b) (jumps := jumps) (stopSpec θ₀ t₀ θ r) E 0 ω) 0
  rw [h2]
  change Fin.snoc (α := fun _ => RecData) (pastMap κ b jumps (stopSpec θ₀ t₀ θ r) E 1 ω) _ (Fin.castSucc 0) = _
  rw [Fin.snoc_castSucc, h1]
  change Fin.snoc (α := fun _ => RecData) (pastMap κ b jumps (stopSpec θ₀ t₀ θ r) E 0 ω) _ (Fin.last 0) = _
  rw [Fin.snoc_last, readRec_retained_succ]
  split_ifs with hc
  · exact absurd hc (launches_run_one_stopSpec _)
  · rfl

/-- **The second record** is, on the launch of the continuation, its record at own time `r`. -/
theorem pastMap_two_one {ω : Ω} (hω : ω ∈ launchOne κ b jumps θ₀ t₀ θ r E) :
    pastMap κ b jumps (stopSpec θ₀ t₀ θ r) E 2 ω 1 = recOf (r : ℝ≥0∞) (E 1 ω) := by
  have h2 := congrFun (pastMap_succ (κ := κ) (b := b) (jumps := jumps) (stopSpec θ₀ t₀ θ r) E 1 ω) 1
  rw [h2]
  change Fin.snoc (α := fun _ => RecData) (pastMap κ b jumps (stopSpec θ₀ t₀ θ r) E 1 ω) _ (Fin.last 1) = _
  rw [Fin.snoc_last, readRec_retained_succ]
  have hω' : (ExplState.run κ b jumps (stopSpec θ₀ t₀ θ r) (fun i => E i ω) 2).2.2.2.1 1 ≠ none := hω
  simp only [hω', ↓reduceIte]
  rfl

/-- **The launch chart** after the first piece. -/
theorem chartOne_eq (ω : Ω) :
    chartOne κ b jumps θ₀ t₀ θ r E ω = Chart.id.loewner
      (fun x : ℝ => (E 0 ω).1 (min ((x.toNNReal : ℝ≥0) : ℝ≥0∞) (min (t₀ : ℝ≥0∞) (E 0 ω).2)).toNNReal)
      ((min (t₀ : ℝ≥0∞) (E 0 ω).2).toNNReal : ℝ) := by
  change (ExplState.launch (ExplState.init 0) 0 (E 0 ω) θ₀ (t₀ : ℝ≥0∞)).2.2.2.2.1 = _
  rw [chart_launch _ _ _ _ _ (ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _))]
  change (Chart.id.recenter 0).loewner _ _ = _
  rw [Chart.recenter_zero]

/-- On a good first record with the first piece alive at `t₀`, the launch chart is the Loewner chart of the record
driver. -/
theorem chartOne_eq_loewner_recW {ω : Ω} (hreg : IsRegularDriver (E 0 ω)) (ht₀ : (t₀ : ℝ≥0∞) < (E 0 ω).2)
    (hg : LocalExt.IsDrvGood (recHist (recOf (t₀ : ℝ≥0∞) (E 0 ω)))) :
    chartOne κ b jumps θ₀ t₀ θ r E ω =
      Chart.id.loewner (Ito.rpath (recW (pastMap κ b jumps (stopSpec θ₀ t₀ θ r) E 2 ω 0))) t₀ := by
  rw [chartOne_eq, pastMap_two_zero, min_eq_left ht₀.le, ENNReal.toNNReal_coe]
  congr 1
  funext x
  simp only [Ito.rpath, recW]
  rw [histDrv_recHist hreg hg]
  simp only [retOf, min_eq_left ht₀.le]

/-- On the continuation alive at `r`, the record chart of the continuation is the Loewner chart of its record driver
at the deterministic time `r`. -/
theorem recChart_eq_loewner_recW {ω : Ω} (hω : ω ∈ launchOne κ b jumps θ₀ t₀ θ r E)
    (hr : (r : ℝ≥0∞) < (E 1 ω).2) :
    recChart (pastMap κ b jumps (stopSpec θ₀ t₀ θ r) E 2 ω 1) =
      Chart.id.loewner (Ito.rpath (recW (pastMap κ b jumps (stopSpec θ₀ t₀ θ r) E 2 ω 1))) r := by
  change Chart.id.loewner (Ito.rpath (recW _)) (LocalExt.histTime (recHist _)) = _
  congr 2
  rw [pastMap_two_one hω]
  change ((min (r : ℝ≥0∞) (E 1 ω).2 : ℝ≥0∞) : WithTop ℝ≥0).untopD 0 = r
  rw [min_eq_left hr.le]
  rfl

end Records

/-! ### A measurable random chart: the support event, the inverse transport and the lift integral -/

section RandomChart

open Lemma72B

variable {Ω : Type*} [MeasurableSpace Ω] {c : Ω → Chart} (hc : ∀ ω, (c ω).IsConformal)
  (hdom : ∀ z, MeasurableSet {ω | z ∈ (c ω).dom})
  (hfwd : ∀ z, Measurable ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
  (hCm : ∀ (z : ℂ) (ε : ℝ), MeasurableSet {ω | Metric.closedBall z ε ⊆ (c ω).dom})

include hCm in
/-- The event that a test function is supported in the chart domain. -/
theorem measurableSet_tsupport_subset_dom (φ : LQGMetric.TestOn upperHalfPlaneOpens) :
    MeasurableSet {ω | tsupport φ ⊆ (c ω).dom} :=
  measurableSet_subset_of_closedBall (C := fun ω => ((c ω).dom : Set ℂ)) (fun ω => (c ω).dom.isOpen) hCm
    φ.hasCompactSupport

include hdom hfwd hCm in
/-- **The inverse transport is pointwise measurable.** -/
theorem measurable_rInvTest_apply (φ : LQGMetric.TestOn upperHalfPlaneOpens) (w : ℂ) :
    Measurable fun ω => rInvTest hc φ ω w := by
  classical
  set S : Set Ω := {ω | tsupport φ ⊆ (c ω).dom} with hSdef
  have hSm : MeasurableSet S := measurableSet_tsupport_subset_dom hCm φ
  by_cases hw : w ∈ H
  · have e : (fun ω => rInvTest hc φ ω w) = S.indicator fun ω => ‖deriv (c ω).2.1 w‖ ^ 2 * φ ((c ω).2.1 w) := by
      funext ω
      by_cases hω : ω ∈ S
      · rw [indicator_of_mem hω]
        simp only [rInvTest, show tsupport φ ⊆ (c ω).dom from hω, ↓reduceDIte]
        exact invTest_apply_of_mem (hc ω) φ hω hw
      · rw [indicator_of_notMem hω]
        simp only [rInvTest, show ¬ tsupport φ ⊆ (c ω).dom from hω, ↓reduceDIte]
        rfl
    rw [e]
    exact (((measurable_deriv_inv_apply hc hdom hfwd hw).norm.pow_const 2).mul
      (φ.continuous.measurable.comp (measurable_inv_apply hc hdom hfwd hw))).indicator hSm
  · have e : (fun ω => rInvTest hc φ ω w) = fun _ => 0 := by
      funext ω
      by_cases hω : ω ∈ S
      · simp only [rInvTest, show tsupport φ ⊆ (c ω).dom from hω, ↓reduceDIte]
        exact invTest_apply_of_notMem (hc ω) φ hω hw
      · simp only [rInvTest, show ¬ tsupport φ ⊆ (c ω).dom from hω, ↓reduceDIte]
        rfl
    rw [e]
    exact measurable_const

include hc hCm in
/-- **The lift integral is measurable on the support event.** -/
theorem measurable_indicator_integral_lift (hliftm : ∀ z, Measurable ({ω | z ∈ (c ω).dom}.indicator
      fun ω => (c ω).2.2 z)) (hliftc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom)
    (φ : LQGMetric.TestOn upperHalfPlaneOpens) :
    Measurable ({ω | tsupport φ ⊆ (c ω).dom}.indicator fun ω => ∫ z, (c ω).2.2 z * φ z) := by
  classical
  set S : Set Ω := {ω | tsupport φ ⊆ (c ω).dom} with hSdef
  have hSm : MeasurableSet S := measurableSet_tsupport_subset_dom hCm φ
  set G : ℂ → Ω → ℝ := fun z ω => S.indicator (fun ω => (c ω).2.2 z * φ z) ω with hGdef
  have hGc : ∀ ω, Continuous fun z => G z ω := by
    intro ω
    by_cases hω : ω ∈ S
    · have e : (fun z => G z ω) = fun z => (c ω).2.2 z * Chart.pushTest (hc ω) (invTest (hc ω) φ hω) z := by
        funext z
        change S.indicator (fun ω => (c ω).2.2 z * φ z) ω = _
        rw [indicator_of_mem hω, pushTest_invTest]
      rw [e]
      exact Chart.continuous_lift_mul_pushTest (hc ω) (hliftc ω) _
    · have e : (fun z => G z ω) = fun _ => 0 := by
        funext z
        change S.indicator (fun ω => (c ω).2.2 z * φ z) ω = _
        rw [indicator_of_notMem hω]
      rw [e]
      exact continuous_const
  have hGm : ∀ z, Measurable (G z) := by
    intro z
    have e : G z = S.indicator fun ω => ({ω | z ∈ (c ω).dom}.indicator (fun ω => (c ω).2.2 z) ω) * φ z := by
      funext ω
      change S.indicator (fun ω => (c ω).2.2 z * φ z) ω = _
      by_cases hω : ω ∈ S
      · rw [indicator_of_mem hω, indicator_of_mem hω]
        by_cases hφz : φ z = 0
        · rw [hφz, mul_zero, mul_zero]
        · have hz : z ∈ (c ω).dom := hω (subset_tsupport _ hφz)
          rw [indicator_of_mem (show ω ∈ {ω | z ∈ (c ω).dom} from hz)]
      · rw [indicator_of_notMem hω, indicator_of_notMem hω]
    rw [e]
    exact ((hliftm z).mul_const _).indicator hSm
  have hu : Measurable (Function.uncurry G) := measurable_uncurry_of_continuous_of_measurable hGc hGm
  have hI := (hu.stronglyMeasurable.integral_prod_left (μ := volume)).measurable
  have e : (S.indicator fun ω => ∫ z, (c ω).2.2 z * φ z) = fun ω => ∫ z, G z ω := by
    funext ω
    by_cases hω : ω ∈ S
    · rw [indicator_of_mem hω]
      exact integral_congr_ae (Eventually.of_forall fun z => by simp only [hGdef, indicator_of_mem hω])
    · rw [indicator_of_notMem hω]
      simp only [hGdef, indicator_of_notMem hω, integral_zero]
  rw [e]
  exact hI

end RandomChart

/-! ### The good event and the chart after the stopped continuation -/

section Good

open Exist Exist.Staged Exist.StagedLaw Restart

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} {θ₀ θ : ℝ} {t₀ r : ℝ≥0}
  {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- The retained σ-algebra after the stopped continuation: generated by the records of both pieces. -/
abbrev pastTwo (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (θ₀ : ℝ) (t₀ : ℝ≥0) (θ : ℝ) (r : ℝ≥0)
    (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) : MeasurableSpace Ω :=
  pastSigma κ b jumps (stopSpec θ₀ t₀ θ r) E 2

/-- The two retained records (the first piece at `t₀`, the continuation at `r`). -/
abbrev recsTwo (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (θ₀ : ℝ) (t₀ : ℝ≥0) (θ : ℝ) (r : ℝ≥0)
    (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) : Ω → PastData 2 :=
  pastMap κ b jumps (stopSpec θ₀ t₀ θ r) E 2

/-- **The chart after the stopped continuation**, read from the two retained records: the record chart of the first
piece at `t₀` followed by the record chart of the continuation at `r`. -/
abbrev stopChart (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (θ₀ : ℝ) (t₀ : ℝ≥0) (θ : ℝ) (r : ℝ≥0)
    (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ω : Ω) : Chart :=
  twoChart (recW (pastMap κ b jumps (stopSpec θ₀ t₀ θ r) E 2 ω 0)) t₀
    (recW (pastMap κ b jumps (stopSpec θ₀ t₀ θ r) E 2 ω 1)) r

/-- The record conditions of the good event: both pieces are alive at their stops and the first record is good. -/
def goodRec : Set (PastData 2) :=
  {u | (u 0).2.2 = false ∧ (u 1).2.2 = false ∧ LocalExt.IsDrvGood (recHist (u 0))}

theorem measurableSet_goodRec : MeasurableSet goodRec := by
  refine MeasurableSet.inter ?_ (MeasurableSet.inter ?_ ?_)
  · exact (measurable_snd.comp (measurable_snd.comp (measurable_pi_apply 0))) (measurableSet_singleton false)
  · exact (measurable_snd.comp (measurable_snd.comp (measurable_pi_apply 1))) (measurableSet_singleton false)
  · exact (measurable_recHist.comp (measurable_pi_apply 0)) LocalExt.measurableSet_isDrvGood

/-- **The good event**: the continuation is launched, both pieces are alive at their stops, the first record is good. -/
def goodEv (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (θ₀ : ℝ) (t₀ : ℝ≥0) (θ : ℝ) (r : ℝ≥0)
    (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) : Set Ω :=
  launchOne κ b jumps θ₀ t₀ θ r E ∩ pastMap κ b jumps (stopSpec θ₀ t₀ θ r) E 2 ⁻¹' goodRec

theorem recOf_flag_eq_false_iff {t : ℝ≥0∞} {e : (ℝ≥0 → ℝ) × ℝ≥0∞} : (recOf t e).2.2 = false ↔ t < e.2 := by
  change decide (e.2 ≤ t) = false ↔ _
  rw [decide_eq_false_iff_not, not_le]

theorem lt_zeta_zero_of_mem_goodEv {ω : Ω} (hω : ω ∈ goodEv κ b jumps θ₀ t₀ θ r E) : (t₀ : ℝ≥0∞) < (E 0 ω).2 := by
  have h := hω.2.1
  rw [pastMap_two_zero] at h
  exact recOf_flag_eq_false_iff.1 h

theorem lt_zeta_one_of_mem_goodEv {ω : Ω} (hω : ω ∈ goodEv κ b jumps θ₀ t₀ θ r E) : (r : ℝ≥0∞) < (E 1 ω).2 := by
  have h := hω.2.2.1
  rw [pastMap_two_one hω.1] at h
  exact recOf_flag_eq_false_iff.1 h

theorem isDrvGood_of_mem_goodEv {ω : Ω} (hω : ω ∈ goodEv κ b jumps θ₀ t₀ θ r E) :
    LocalExt.IsDrvGood (recHist (recOf (t₀ : ℝ≥0∞) (E 0 ω))) := by
  have h := hω.2.2.2
  rwa [pastMap_two_zero] at h

/-- **The good event is an event of the retained past.** -/
theorem measurableSet_goodEv [MeasurableSpace Ω] [StandardBorelSpace Ω] (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hEm : ∀ j, Measurable (E j)) (hreg : ∀ j ω, IsRegularDriver (E j ω)) :
    MeasurableSet[pastSigma κ b jumps (stopSpec θ₀ t₀ θ r) E 2] (goodEv κ b jumps θ₀ t₀ θ r E) := by
  refine MeasurableSet.inter ?_ ?_
  · have hLm : MeasurableSet (launchOne κ b jumps θ₀ t₀ θ r E) :=
      measurableSet_launch (k := 2) runMeasStatement hb (stopSpec θ₀ t₀ θ r) (fun j _ => hEm j)
        (fun j _ => hreg j) (n := 1) (by norm_num)
    have hL1 : MeasurableSet[pastSigma κ b jumps (stopSpec θ₀ t₀ θ r) E 1] (launchOne κ b jumps θ₀ t₀ θ r E) :=
      measurableSet_pastSigma_of_run runMeasStatement hb (stopSpec θ₀ t₀ θ r) (fun j _ => hEm j)
        (fun j _ => hreg j) hLm fun ω ω' he hω => by
          change (ExplState.run κ b jumps (stopSpec θ₀ t₀ θ r) (fun j => E j ω') 2).2.2.2.1 1 ≠ none
          rw [← launches_run_succ_of_run_eq (stopSpec θ₀ t₀ θ r) he]
          exact hω
    exact pastSigma_mono (stopSpec θ₀ t₀ θ r) E (by norm_num) _ hL1
  · rw [pastSigma_eq_comap]
    exact ⟨goodRec, measurableSet_goodRec, rfl⟩

end Good

/-! ### The law of the field given both records, in the original coordinate -/

section Main

open Exist Exist.Staged Exist.StagedLaw Restart Lemma72B

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {θ₀ θ : ℝ}
  {t₀ r : ℝ≥0} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}

omit [StandardBorelSpace Ω] in
/-- The retained σ-algebra after the stopped continuation is a sub-σ-algebra. -/
theorem pastTwo_le (hb : IsPiecewiseConstantBoundaryData b jumps) (hEm : ∀ j, Measurable (E j))
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) (r : ℝ≥0) : pastTwo κ b jumps θ₀ t₀ θ r E ≤ mΩ := by
  have hpm : Measurable (recsTwo κ b jumps θ₀ t₀ θ r E) :=
    measurable_pastMap runMeasStatement hb _ (fun j _ => hEm j) (fun j _ => hreg j) 2 le_rfl
  change pastSigma κ b jumps (stopSpec θ₀ t₀ θ r) E 2 ≤ mΩ
  rw [pastSigma_eq_comap]
  exact hpm.comap_le

omit [StandardBorelSpace Ω] in
/-- **The event that a test function is supported in the domain after the stopped continuation** is an event of
the retained past. -/
theorem measurableSet_tsupport_subset_stopChart (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hEm : ∀ j, Measurable (E j)) (hreg : ∀ j ω, IsRegularDriver (E j ω)) (r : ℝ≥0)
    (φ : LQGMetric.TestOn upperHalfPlaneOpens) :
    MeasurableSet[pastTwo κ b jumps θ₀ t₀ θ r E] {ω | tsupport φ ⊆ (stopChart κ b jumps θ₀ t₀ θ r E ω).dom} := by
  have hpm : Measurable (recsTwo κ b jumps θ₀ t₀ θ r E) :=
    measurable_pastMap runMeasStatement hb _ (fun j _ => hEm j) (fun j _ => hreg j) 2 le_rfl
  have hp𝓗 : Measurable[pastTwo κ b jumps θ₀ t₀ θ r E] (recsTwo κ b jumps θ₀ t₀ θ r E) := by
    change Measurable[pastSigma κ b jumps (stopSpec θ₀ t₀ θ r) E 2] (pastMap κ b jumps (stopSpec θ₀ t₀ θ r) E 2)
    rw [pastSigma_eq_comap]
    exact comap_measurable _
  have hrecW : ∀ (i : Fin 2) (s : ℝ≥0), Measurable fun u : PastData 2 => recW (u i) s := by
    intro i s
    have h1 : Measurable fun u : PastData 2 => recHist (u i) := measurable_recHist.comp (measurable_pi_apply i)
    exact (LocalExt.measurable_histDrv_apply (nL := 0) (nR := 0) s).comp h1
  have hW0m : ∀ s, Measurable[pastTwo κ b jumps θ₀ t₀ θ r E]
      fun ω => recW (recsTwo κ b jumps θ₀ t₀ θ r E ω 0) s := fun s => (hrecW 0 s).comp hp𝓗
  have hW1m : ∀ s, Measurable[pastTwo κ b jumps θ₀ t₀ θ r E]
      fun ω => recW (recsTwo κ b jumps θ₀ t₀ θ r E ω 1) s := fun s => (hrecW 1 s).comp hp𝓗
  have hWc : ∀ (i : Fin 2) ω, Continuous (recW (recsTwo κ b jumps θ₀ t₀ θ r E ω i)) := fun _ _ =>
    LocalExt.continuous_histDrv _
  have hW0 : ∀ (i : Fin 2) ω, recW (recsTwo κ b jumps θ₀ t₀ θ r E ω i) 0 = 0 := fun _ _ =>
    LocalExt.histDrv_zero _
  have hCm := measurableSet_closedBall_subset_dom_twoChart (pastTwo κ b jumps θ₀ t₀ θ r E) (t₀ := t₀) (r := r)
    (hWc 0) (hW0 0) (hWc 1) (hW0 1) hW0m hW1m
  exact @measurableSet_tsupport_subset_dom Ω (pastTwo κ b jumps θ₀ t₀ θ r E) _ hCm φ

/-- **The field given the records of both stopped pieces, in the original coordinate** (the probabilistic core of
(S); the landed `post_stage` read back through the two-stage chart). On the good event, for every test function `φ`
supported in the domain `D` left after the stopped continuation, conditionally on the retained records,
`(h, φ)` is Gaussian with mean `∫ (𝔤 ∘ F − χ ℓ) φ` and variance `‖φ‖²_{H⁻¹(D)}`, where `F` is the chart after the
stopped continuation, `ℓ` its lift and `𝔤` the bounded harmonic mean of the stop word `stopWord κ (β, θ, record)` of
the continuation (`β` the word of the conditional field at the launch, read off the past before it). -/
theorem ae_condExp_cexp_stopChart (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hh : IsGFFWithBoundaryData P h b jumps) (hS : IsStagedHistory κ b jumps P h (StripSys.twoAngleSpec θ₀ t₀ θ) E)
    (hreg : ∀ j ω, IsRegularDriver (E j ω)) (r : ℝ≥0) :
    ∃ β : Ω → BoundaryWord, Measurable[pastSigma κ b jumps (stopSpec θ₀ t₀ θ r) E 1] β ∧
      ∀ φ : LQGMetric.TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ goodEv κ b jumps θ₀ t₀ θ r E →
        tsupport φ ⊆ (stopChart κ b jumps θ₀ t₀ θ r E ω).dom →
        P[fun ω' => Complex.exp (Complex.I * (h ω' φ : ℂ)) | pastSigma κ b jumps (stopSpec θ₀ t₀ θ r) E 2] ω =
          Complex.exp (Complex.I * ((∫ z, ((stopWord κ (β ω, θ, pastMap κ b jumps (stopSpec θ₀ t₀ θ r) E 2 ω 1)).mean
              ((stopChart κ b jumps θ₀ t₀ θ r E ω).1 z) -
              chiC κ * (stopChart κ b jumps θ₀ t₀ θ r E ω).2.2 z) * φ z : ℝ) : ℂ) -
            (((1 / 2 : ℝ) * QuantumZipper.zeroGFFTestCov ((stopChart κ b jumps θ₀ t₀ θ r E ω).dom : Set ℂ) φ φ : ℝ) :
              ℂ)) := by
  classical
  obtain ⟨β, Y, hβ, hY, hpath, hlaw⟩ := exists_stageLaw_stopSpec hκ hb hh hS hreg r
  refine ⟨β, hβ, fun φ => ?_⟩
  -- the records and the retained σ-algebra
  have hpm : Measurable (recsTwo κ b jumps θ₀ t₀ θ r E) :=
    measurable_pastMap runMeasStatement hb _ (fun j _ => hS.1 j) (fun j _ => hreg j) 2 le_rfl
  have h𝓗 : pastTwo κ b jumps θ₀ t₀ θ r E ≤ mΩ := by
    change pastSigma κ b jumps (stopSpec θ₀ t₀ θ r) E 2 ≤ mΩ
    rw [pastSigma_eq_comap]
    exact hpm.comap_le
  have hp𝓗 : Measurable[pastTwo κ b jumps θ₀ t₀ θ r E] (recsTwo κ b jumps θ₀ t₀ θ r E) := by
    change Measurable[pastSigma κ b jumps (stopSpec θ₀ t₀ θ r) E 2] (pastMap κ b jumps (stopSpec θ₀ t₀ θ r) E 2)
    rw [pastSigma_eq_comap]
    exact comap_measurable _
  have hrecW : ∀ (i : Fin 2) (s : ℝ≥0), Measurable fun u : PastData 2 => recW (u i) s := by
    intro i s
    have h1 : Measurable fun u : PastData 2 => recHist (u i) := measurable_recHist.comp (measurable_pi_apply i)
    exact (LocalExt.measurable_histDrv_apply (nL := 0) (nR := 0) s).comp h1
  have hW0m : ∀ s, Measurable[pastTwo κ b jumps θ₀ t₀ θ r E]
      fun ω => recW (recsTwo κ b jumps θ₀ t₀ θ r E ω 0) s := fun s => (hrecW 0 s).comp hp𝓗
  have hW1m : ∀ s, Measurable[pastTwo κ b jumps θ₀ t₀ θ r E]
      fun ω => recW (recsTwo κ b jumps θ₀ t₀ θ r E ω 1) s := fun s => (hrecW 1 s).comp hp𝓗
  have hWc : ∀ (i : Fin 2) ω, Continuous (recW (recsTwo κ b jumps θ₀ t₀ θ r E ω i)) := fun _ _ =>
    LocalExt.continuous_histDrv _
  have hW0 : ∀ (i : Fin 2) ω, recW (recsTwo κ b jumps θ₀ t₀ θ r E ω i) 0 = 0 := fun _ _ =>
    LocalExt.histDrv_zero _
  have hc : ∀ ω, (stopChart κ b jumps θ₀ t₀ θ r E ω).IsConformal := fun ω =>
    isConformal_twoChart (hWc 0 ω) (hW0 0 ω) (hWc 1 ω) (hW0 1 ω)
  have hdom := measurableSet_mem_dom_twoChart (pastTwo κ b jumps θ₀ t₀ θ r E) (t₀ := t₀) (r := r)
    (hWc 0) (hW0 0) (hWc 1) (hW0 1) hW0m hW1m
  have hfwd := measurable_indicator_fwd_twoChart (pastTwo κ b jumps θ₀ t₀ θ r E) (t₀ := t₀) (r := r)
    (hWc 0) (hW0 0) (hWc 1) (hW0 1) hW0m hW1m
  have hliftm := measurable_indicator_lift_twoChart (pastTwo κ b jumps θ₀ t₀ θ r E) (t₀ := t₀) (r := r)
    (hWc 0) (hW0 0) (hWc 1) (hW0 1) hW0m hW1m
  have hliftc : ∀ ω, ContinuousOn (stopChart κ b jumps θ₀ t₀ θ r E ω).2.2 (stopChart κ b jumps θ₀ t₀ θ r E ω).dom :=
    continuousOn_lift_twoChart (hWc 0) (hW0 0) (hWc 1) (hW0 1)
  have hCm := measurableSet_closedBall_subset_dom_twoChart (pastTwo κ b jumps θ₀ t₀ θ r E) (t₀ := t₀) (r := r)
    (hWc 0) (hW0 0) (hWc 1) (hW0 1) hW0m hW1m
  -- the events
  have hG : MeasurableSet[pastTwo κ b jumps θ₀ t₀ θ r E] (goodEv κ b jumps θ₀ t₀ θ r E) :=
    measurableSet_goodEv hb hS.1 hreg
  have hSm : MeasurableSet[pastTwo κ b jumps θ₀ t₀ θ r E]
      {ω | tsupport φ ⊆ (stopChart κ b jumps θ₀ t₀ θ r E ω).dom} :=
    @measurableSet_tsupport_subset_dom Ω (pastTwo κ b jumps θ₀ t₀ θ r E) _ hCm φ
  have hGS : MeasurableSet[pastTwo κ b jumps θ₀ t₀ θ r E]
      (goodEv κ b jumps θ₀ t₀ θ r E ∩ {ω | tsupport φ ⊆ (stopChart κ b jumps θ₀ t₀ θ r E ω).dom}) := hG.inter hSm
  -- the field read in the record chart of the continuation
  have hp1 : Measurable fun ω => recsTwo κ b jumps θ₀ t₀ θ r E ω 1 := measurable_pi_iff.1 hpm 1
  have hpY : Measurable fun ω => (recsTwo κ b jumps θ₀ t₀ θ r E ω 1, Y ω) := hp1.prodMk hY
  have hXm : Measurable fun ω => recField κ (recsTwo κ b jumps θ₀ t₀ θ r E ω 1) (Y ω) :=
    Measurable.comp (g := fun q : RecData × LQGMetric.DistOn upperHalfPlaneOpens => recField κ q.1 q.2)
      (f := fun ω => (recsTwo κ b jumps θ₀ t₀ θ r E ω 1, Y ω)) (measurable_recField κ) hpY
  -- the chart relation on the good event
  have htr : ∀ᵐ ω ∂P, ω ∈ goodEv κ b jumps θ₀ t₀ θ r E → IsChartTransport (stopChart κ b jumps θ₀ t₀ θ r E ω) 1 0
      (chiC κ) (h ω) (recField κ (recsTwo κ b jumps θ₀ t₀ θ r E ω 1) (Y ω)) := by
    filter_upwards [hpath] with ω hpω hωG
    obtain ⟨hconf, hlift, hT⟩ := hpω hωG.1
    have hch1 := chartOne_eq_loewner_recW (κ := κ) (b := b) (jumps := jumps) (θ₀ := θ₀) (θ := θ) (r := r)
      (hreg 0 ω) (lt_zeta_zero_of_mem_goodEv hωG) (isDrvGood_of_mem_goodEv hωG)
    have hch2 := recChart_eq_loewner_recW hωG.1 (lt_zeta_one_of_mem_goodEv hωG)
    rw [hch1] at hconf hlift hT
    have hT2 := isChartTransport_recField κ (pastMap κ b jumps (stopSpec θ₀ t₀ θ r) E 2 ω 1) (Y ω)
    have hconf2 := isConformal_recChart (pastMap κ b jumps (stopSpec θ₀ t₀ θ r) E 2 ω 1)
    have hlift2 := continuousOn_recChart_lift (pastMap κ b jumps (stopSpec θ₀ t₀ θ r) E 2 ω 1)
    rw [hch2] at hT2 hconf2 hlift2
    exact IsChartTransport.trans hconf hconf2 hlift hlift2 hT hT2
  -- the random test: the inverse transport of `φ` on the good event
  obtain ⟨T, hT⟩ : ∃ T : Ω → LQGMetric.TestOn upperHalfPlaneOpens, T = fun ω =>
      if ω ∈ goodEv κ b jumps θ₀ t₀ θ r E then rInvTest hc φ ω else 0 := ⟨_, rfl⟩
  have hTm : ∀ w, Measurable[pastTwo κ b jumps θ₀ t₀ θ r E] fun ω => T ω w := by
    intro w
    have h1 := @measurable_rInvTest_apply Ω (pastTwo κ b jumps θ₀ t₀ θ r E) _ hc hdom hfwd hCm φ w
    have e : (fun ω => T ω w) = (goodEv κ b jumps θ₀ t₀ θ r E).piecewise (fun ω => rInvTest hc φ ω w)
        (fun _ => 0) := by
      funext ω
      by_cases hω : ω ∈ goodEv κ b jumps θ₀ t₀ θ r E
      · rw [piecewise_eq_of_mem _ _ _ hω, hT]
        simp only [hω, ↓reduceIte]
      · rw [piecewise_eq_of_notMem _ _ _ hω, hT]
        simp only [hω, ↓reduceIte]
        rfl
    rw [e]
    exact Measurable.piecewise hG h1 measurable_const
  -- the support-restricted law of the chart field
  obtain ⟨U', hU'⟩ : ∃ U' : Ω → Set ℂ, U' = fun ω => if ω ∈ goodEv κ b jumps θ₀ t₀ θ r E then H else ∅ :=
    ⟨_, rfl⟩
  obtain ⟨Ψ', hΨ'⟩ : ∃ Ψ' : Ω → LQGMetric.TestOn upperHalfPlaneOpens → ℂ, Ψ' = fun ω ψ =>
      if ω ∈ goodEv κ b jumps θ₀ t₀ θ r E then
        gaussCF (stopWord κ (β ω, θ, recsTwo κ b jumps θ₀ t₀ θ r E ω 1)) ψ else 1 := ⟨_, rfl⟩
  have hU'o : ∀ ω, IsOpen (U' ω) := fun ω => by
    rw [hU']
    dsimp only
    split_ifs
    exacts [QuantumZipper.isOpen_H, isOpen_empty]
  have hU'V : ∀ ω, U' ω ⊆ (upperHalfPlaneOpens : Set ℂ) := fun ω => by
    rw [hU']
    dsimp only
    split_ifs
    exacts [subset_rfl, empty_subset _]
  have hΨlaw : ∀ ω, ∃ μ : Measure (LQGMetric.DistOn upperHalfPlaneOpens), IsProbabilityMeasure μ ∧
      ∀ ψ : LQGMetric.TestOn upperHalfPlaneOpens, tsupport ψ ⊆ U' ω →
        ∫ u, Complex.exp (Complex.I * (u ψ : ℂ)) ∂μ = Ψ' ω ψ := by
    intro ω
    by_cases hω : ω ∈ goodEv κ b jumps θ₀ t₀ θ r E
    · refine ⟨(stopWord κ (β ω, θ, recsTwo κ b jumps θ₀ t₀ θ r E ω 1)).gffLaw, inferInstance, fun ψ _ => ?_⟩
      rw [hΨ']
      simp only [hω, ↓reduceIte]
      exact (gaussCF_eq_integral _ ψ).symm
    · refine ⟨Measure.dirac 0, inferInstance, fun ψ _ => ?_⟩
      rw [hΨ']
      simp only [hω, ↓reduceIte]
      rw [integral_dirac' _ _ (GFF.measurable_exp_I_mul (LQGMetric.measurable_distOn_apply ψ)).stronglyMeasurable]
      simp
  have hcond' : ∀ ψ : LQGMetric.TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, tsupport ψ ⊆ U' ω →
      P[fun ω => Complex.exp (Complex.I * (recField κ (recsTwo κ b jumps θ₀ t₀ θ r E ω 1) (Y ω) ψ : ℂ)) |
        pastTwo κ b jumps θ₀ t₀ θ r E] ω = Ψ' ω ψ := by
    intro ψ
    by_cases hψ : ψ = 0
    · subst hψ
      have hc1 : P[fun ω => Complex.exp (Complex.I * (recField κ (recsTwo κ b jumps θ₀ t₀ θ r E ω 1) (Y ω) 0 : ℂ)) |
          pastTwo κ b jumps θ₀ t₀ θ r E] = fun _ => (1 : ℂ) := by
        simp only [map_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero]
        exact condExp_const h𝓗 1
      refine Eventually.of_forall fun ω _ => ?_
      rw [hc1, hΨ']
      dsimp only
      split_ifs
      · rw [gaussCF_eq_integral]
        simp
      · rfl
    · filter_upwards [hlaw ψ] with ω h1 hsupp
      by_cases hω : ω ∈ goodEv κ b jumps θ₀ t₀ θ r E
      · rw [hΨ']
        simp only [hω, ↓reduceIte]
        exact h1 hω.1
      · rw [hU'] at hsupp
        simp only [hω, ↓reduceIte] at hsupp
        exact absurd (Restart.eq_zero_of_tsupport_subset_empty hsupp) hψ
  have hTU : ∀ ω, tsupport (T ω) ⊆ U' ω := fun ω => by
    rw [hT, hU']
    dsimp only
    split_ifs
    · exact (rInvTest hc φ ω).tsupport_subset
    · simp
  have key := RandomTest.condExp_cexp_apply_ae_eq_of_subset (P := P) h𝓗 hXm hU'o hU'V hΨlaw hcond' hTm hTU
  -- the lift term, an event-masked measurable variable
  obtain ⟨L, hL⟩ : ∃ L : Ω → ℝ, L = {ω | tsupport φ ⊆ (stopChart κ b jumps θ₀ t₀ θ r E ω).dom}.indicator
      fun ω => ∫ z, (stopChart κ b jumps θ₀ t₀ θ r E ω).2.2 z * φ z := ⟨_, rfl⟩
  have hLm : Measurable[pastTwo κ b jumps θ₀ t₀ θ r E] L := by
    rw [hL]
    exact @measurable_indicator_integral_lift Ω (pastTwo κ b jumps θ₀ t₀ θ r E) _ hc hCm hliftm hliftc φ
  obtain ⟨f, hf⟩ : ∃ f : Ω → ℂ, f = fun ω => Complex.exp (-(Complex.I * ((chiC κ * L ω : ℝ) : ℂ))) := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : Ω → ℂ, g = fun ω => Complex.exp (Complex.I *
      (recField κ (recsTwo κ b jumps θ₀ t₀ θ r E ω 1) (Y ω) (T ω) : ℂ)) := ⟨_, rfl⟩
  have hfm : StronglyMeasurable[pastTwo κ b jumps θ₀ t₀ θ r E] f := by
    rw [hf]
    exact (Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp
      (hLm.const_mul (chiC κ))).const_mul Complex.I).neg).stronglyMeasurable
  have hgm : Measurable g := by
    rw [hg]
    exact GFF.measurable_exp_I_mul (RandomTest.measurable_apply_of_forall_measurable hXm
      fun z => (hTm z).mono h𝓗 le_rfl)
  have hnorm : ∀ x : ℝ, ‖Complex.exp (Complex.I * (x : ℂ))‖ = 1 := Restart.norm_cexp_I_mul_ofReal
  have hgi : Integrable g P :=
    Integrable.of_bound hgm.aestronglyMeasurable 1 (Eventually.of_forall fun ω => by rw [hg]; exact (hnorm _).le)
  have hfg : ∀ ω, ‖ContinuousLinearMap.mul ℝ ℂ (f ω) (g ω)‖ ≤ 1 := fun ω => by
    rw [ContinuousLinearMap.mul_apply', norm_mul, hf, hg]
    simp only [← neg_mul]
    rw [Complex.norm_exp, Complex.norm_exp]
    simp
  have hfgi : Integrable (fun ω => ContinuousLinearMap.mul ℝ ℂ (f ω) (g ω)) P :=
    Integrable.of_bound ((hfm.mono h𝓗).measurable.mul hgm).aestronglyMeasurable 1 (Eventually.of_forall hfg)
  have hpull := condExp_bilin_of_stronglyMeasurable_left (B := ContinuousLinearMap.mul ℝ ℂ)
    (m := pastTwo κ b jumps θ₀ t₀ θ r E) (μ := P) hfm hfgi hgi
  -- on the good event with `supp φ` in the domain, `e^{i h(φ)} = f · g`
  have hhφ : Measurable fun ω => h ω φ := (LQGMetric.measurable_distOn_apply φ).comp hh.1
  have hloc := Restart.ae_condExp_congr_on (𝒦 := pastTwo κ b jumps θ₀ t₀ θ r E) (P := P) hGS
    (GFF.integrable_exp_I_mul hhφ) hfgi (X := fun ω => Complex.exp (Complex.I * (h ω φ : ℂ)))
    (Y := fun ω => ContinuousLinearMap.mul ℝ ℂ (f ω) (g ω)) (by
      filter_upwards [htr] with ω htrω hω
      obtain ⟨hωG, hωS⟩ := hω
      have hTω : T ω = invTest (hc ω) φ hωS := by
        rw [hT]
        simp only [hωG, ↓reduceIte, rInvTest,
          show tsupport φ ⊆ (stopChart κ b jumps θ₀ t₀ θ r E ω).dom from hωS, ↓reduceDIte]
      have hLω : L ω = ∫ z, (stopChart κ b jumps θ₀ t₀ θ r E ω).2.2 z * φ z := by
        rw [hL, indicator_of_mem (show ω ∈ {ω | tsupport φ ⊆ (stopChart κ b jumps θ₀ t₀ θ r E ω).dom} from hωS)]
      rw [ContinuousLinearMap.mul_apply', hf, hg]
      dsimp only
      rw [hTω, hLω, ← Complex.exp_add,
        apply_eq_of_isChartTransport (hc ω) (hliftc ω) (htrω hωG) φ hωS]
      congr 1
      push_cast
      ring)
  filter_upwards [hloc, hpull, key, htr] with ω h1 h2 h3 htrω hωG hωS
  rw [h1 ⟨hωG, hωS⟩, h2, ContinuousLinearMap.mul_apply']
  have hg' : P[g | pastTwo κ b jumps θ₀ t₀ θ r E] ω = Ψ' ω (T ω) := by rw [hg]; exact h3
  rw [hg']
  have hTω : T ω = invTest (hc ω) φ hωS := by
    rw [hT]
    simp only [hωG, ↓reduceIte, rInvTest,
      show tsupport φ ⊆ (stopChart κ b jumps θ₀ t₀ θ r E ω).dom from hωS, ↓reduceDIte]
  have hLω : L ω = ∫ z, (stopChart κ b jumps θ₀ t₀ θ r E ω).2.2 z * φ z := by
    rw [hL, indicator_of_mem (show ω ∈ {ω | tsupport φ ⊆ (stopChart κ b jumps θ₀ t₀ θ r E ω).dom} from hωS)]
  rw [hΨ', hf]
  dsimp only
  rw [hTω, hLω]
  simp only [hωG, ↓reduceIte]
  -- the mean, by the change of variables `w = F(z)`
  have hmean : ∫ w, (stopWord κ (β ω, θ, recsTwo κ b jumps θ₀ t₀ θ r E ω 1)).mean w * invTest (hc ω) φ hωS w =
      ∫ z, (stopWord κ (β ω, θ, recsTwo κ b jumps θ₀ t₀ θ r E ω 1)).mean ((stopChart κ b jumps θ₀ t₀ θ r E ω).1 z) *
        φ z := by
    have h1 := Chart.integral_mul_pushTest (hc ω) (invTest (hc ω) φ hωS)
      (fun z => (stopWord κ (β ω, θ, recsTwo κ b jumps θ₀ t₀ θ r E ω 1)).mean ((stopChart κ b jumps θ₀ t₀ θ r E ω).1 z))
    rw [pushTest_invTest] at h1
    rw [h1]
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    by_cases hw : w ∈ H
    · simp only [(hc ω).2.2 w hw]
    · simp only [invTest_apply_of_notMem (hc ω) φ hωS hw, mul_zero]
  -- the variance, by conformal invariance
  have hcov : QuantumZipper.zeroGFFTestCov (upperHalfPlaneOpens : Set ℂ) (invTest (hc ω) φ hωS)
      (invTest (hc ω) φ hωS) =
      QuantumZipper.zeroGFFTestCov ((stopChart κ b jumps θ₀ t₀ θ r E ω).dom : Set ℂ) φ φ := by
    have h1 := Chart.zeroGFFTestCov_pushTest (hc ω) (invTest (hc ω) φ hωS) (invTest (hc ω) φ hωS)
    rw [pushTest_invTest] at h1
    exact h1.symm
  have hsplit : ∫ z, ((stopWord κ (β ω, θ, recsTwo κ b jumps θ₀ t₀ θ r E ω 1)).mean
      ((stopChart κ b jumps θ₀ t₀ θ r E ω).1 z) - chiC κ * (stopChart κ b jumps θ₀ t₀ θ r E ω).2.2 z) * φ z =
      (∫ z, (stopWord κ (β ω, θ, recsTwo κ b jumps θ₀ t₀ θ r E ω 1)).mean
        ((stopChart κ b jumps θ₀ t₀ θ r E ω).1 z) * φ z) -
        chiC κ * ∫ z, (stopChart κ b jumps θ₀ t₀ θ r E ω).2.2 z * φ z := by
    have hm : ContinuousOn (fun z => (stopWord κ (β ω, θ, recsTwo κ b jumps θ₀ t₀ θ r E ω 1)).mean
        ((stopChart κ b jumps θ₀ t₀ θ r E ω).1 z)) (stopChart κ b jumps θ₀ t₀ θ r E ω).dom :=
      (BoundaryWord.continuousOn_mean _).comp (hc ω).differentiableOn_fwd.continuousOn fun z hz =>
        (hc ω).fwd_mem hz
    have hi1 := WholeField.integrable_mul_testOn hm φ hωS
    have hi2 := (WholeField.integrable_mul_testOn (hliftc ω) φ hωS).const_mul (chiC κ)
    rw [← integral_const_mul, ← integral_sub hi1 hi2]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    ring
  rw [gaussCF, hmean, hcov, hsplit, ← Complex.exp_add]
  congr 1
  push_cast
  ring

end Main

end StripSideHeightProb

end Sec7

end InteractingSLE
