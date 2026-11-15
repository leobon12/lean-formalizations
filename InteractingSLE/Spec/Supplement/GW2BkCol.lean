/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BjExit
import InteractingSLE.Spec.Supplement.CS3ProofCrossRight

/-!
# A collision of a gap-controlled label forces the exit strictly earlier (D12 items 1–2, the deterministic core)

Packet PROVE-GW2-BUF (round 8). The near buffer `InBuffer mL mR R g` keeps the gaps of the far right labels
(`mR ≤ j`) and of the far left labels (`mL ≤ i`) above `g > 0`. If such a label's image collides with the driver at
time `σ` (gap `0`), the continuous gap crosses `g` strictly before `σ`, and the state leaves the buffer there. This is
independent of where the labels sit (D12's item 3).

* **`exists_notMem_before_rightCollision`**, **`exists_notMem_before_leftCollision`** (for any continuous state
  path that starts in the buffer);
* **`exitRule_lt_of_rightCollision`**, **`exitRule_lt_of_leftCollision`**: the near exit rule along a continuous
  path whose image state starts in the buffer fires strictly before a collision of a controlled label at a stage time
  below the cap.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2Bh

open Exist.StagedLaw Supp8.GB6 Supp8.GB6.HullId Supp8.GB6.RelDrv.Version Supp12 Supp12.DSReach

variable {nL nR : ℕ}

/-- **A right collision of a controlled label is preceded by a time outside the buffer.** -/
theorem exists_notMem_before_rightCollision {mL mR : ℕ} {R g : ℝ} (hg : 0 < g)
    {p : ℝ≥0 → ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)} (hp : Continuous p) (h0 : InBuffer mL mR R g (p 0)) {σ : ℝ≥0}
    {j : Fin nR} (hj : mR ≤ (j : ℕ)) (hcol : (p σ).2.2 j = (p σ).1) :
    ∃ t < σ, ¬ InBuffer mL mR R g (p t) := by
  set f : ℝ≥0 → ℝ := fun t => (p t).2.2 j - (p t).1 with hf
  have hfc : Continuous f := ((continuous_apply j).comp (continuous_snd.comp (continuous_snd.comp hp))).sub
    (continuous_fst.comp hp)
  have hf0 : g < f 0 := h0.2.1 j hj
  have hfσ : f σ = 0 := by simp only [hf, hcol, sub_self]
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc' (zero_le : (0 : ℝ≥0) ≤ σ) hfc.continuousOn
    (show g ∈ Icc (f σ) (f 0) from ⟨by rw [hfσ]; exact hg.le, hf0.le⟩)
  refine ⟨t, lt_of_le_of_ne ht.2 fun h => ?_, fun hb => ?_⟩
  · rw [h, hfσ] at hft
    exact (lt_irrefl _) (hft ▸ hg)
  · have h1 := hb.2.1 j hj
    change g < f t at h1
    rw [hft] at h1
    exact lt_irrefl _ h1

/-- **A left collision of a controlled label is preceded by a time outside the buffer.** -/
theorem exists_notMem_before_leftCollision {mL mR : ℕ} {R g : ℝ} (hg : 0 < g)
    {p : ℝ≥0 → ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)} (hp : Continuous p) (h0 : InBuffer mL mR R g (p 0)) {σ : ℝ≥0}
    {i : Fin nL} (hi : mL ≤ (i : ℕ)) (hcol : (p σ).2.1 i = (p σ).1) :
    ∃ t < σ, ¬ InBuffer mL mR R g (p t) := by
  set f : ℝ≥0 → ℝ := fun t => (p t).1 - (p t).2.1 i with hf
  have hfc : Continuous f := (continuous_fst.comp hp).sub
    ((continuous_apply i).comp (continuous_fst.comp (continuous_snd.comp hp)))
  have hf0 : g < f 0 := h0.2.2 i hi
  have hfσ : f σ = 0 := by simp only [hf, hcol, sub_self]
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc' (zero_le : (0 : ℝ≥0) ≤ σ) hfc.continuousOn
    (show g ∈ Icc (f σ) (f 0) from ⟨by rw [hfσ]; exact hg.le, hf0.le⟩)
  refine ⟨t, lt_of_le_of_ne ht.2 fun h => ?_, fun hb => ?_⟩
  · rw [h, hfσ] at hft
    exact (lt_irrefl _) (hft ▸ hg)
  · have h1 := hb.2.2 i hi
    change g < f t at h1
    rw [hft] at h1
    exact lt_irrefl _ h1

/-- The exit rule fires no later than any stage time below the cap at which the image state is outside the buffer. -/
theorem exitRule_le_of_notMem (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) {B : Set (ℝ × (Fin nL → ℝ) × (Fin nR → ℝ))}
    (hB : IsOpen B) (hBc : (Bᶜ).Nonempty) (a : ℝ≥0) (b : ℝ) {c : ℝ≥0} (hc : 0 < c) (r : RecData)
    {w : ℝ≥0 → ℝ} (hw : Continuous w) (h0 : GW2Sdg.imgState xL xR (scaledPath a b w) 0 ∈ B) {t₁ : ℝ≥0}
    (ht₁ : t₁ ≤ c) (hout : GW2Sdg.imgState xL xR (scaledPath a b w) (a * t₁) ∉ B) :
    exitRule xL xR B a b c (r, w) ≤ t₁ := by
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
  have he : exitRule xL xR B a b c (r, w) = (gaugeStop g 0 c : ℝ≥0∞) := hitRule_eq_gaugeStop hgc hc hg0 hread
  rw [he]
  refine ENNReal.coe_le_coe.2 (gaugeStop_le_of_le ht₁ ?_)
  simp only [hg]
  exact le_of_eq (Metric.infDist_zero_of_mem hout)

/-- **The near exit fires strictly before a right collision of a controlled label** below the cap. -/
theorem exitRule_lt_of_rightCollision (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) {mL mR : ℕ} {Rb g : ℝ} (hg : 0 < g)
    (hB : IsOpen {p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) | InBuffer mL mR Rb g p})
    (hBc : ({p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) | InBuffer mL mR Rb g p}ᶜ).Nonempty)
    {a : ℝ≥0} (ha : 0 < a) (b : ℝ) {c : ℝ≥0} (hc : 0 < c) (r : RecData) {w : ℝ≥0 → ℝ} (hw : Continuous w)
    (h0 : InBuffer mL mR Rb g (GW2Sdg.imgState xL xR (scaledPath a b w) 0)) {σ : ℝ≥0} (hσc : σ ≤ c)
    {j : Fin nR} (hj : mR ≤ (j : ℕ))
    (hcol : (GW2Sdg.imgState xL xR (scaledPath a b w) (a * σ)).2.2 j =
      (GW2Sdg.imgState xL xR (scaledPath a b w) (a * σ)).1) :
    exitRule xL xR {p | InBuffer mL mR Rb g p} a b c (r, w) < σ := by
  have hp := continuous_imgState xL xR (continuous_scaledPath a b hw)
  obtain ⟨t, ht, hout⟩ := exists_notMem_before_rightCollision hg hp h0 hj hcol
  have ht₁ : t / a < σ := (div_lt_iff₀ ha).2 (by rwa [mul_comm])
  have heq : a * (t / a) = t := mul_div_cancel₀ t ha.ne'
  have hle := exitRule_le_of_notMem xL xR hB hBc a b hc r hw h0 (ht₁.le.trans hσc)
    (by rw [heq]; exact hout)
  exact hle.trans_lt (ENNReal.coe_lt_coe.2 ht₁)

/-- **The near exit fires strictly before a left collision of a controlled label** below the cap. -/
theorem exitRule_lt_of_leftCollision (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) {mL mR : ℕ} {Rb g : ℝ} (hg : 0 < g)
    (hB : IsOpen {p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) | InBuffer mL mR Rb g p})
    (hBc : ({p : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ) | InBuffer mL mR Rb g p}ᶜ).Nonempty)
    {a : ℝ≥0} (ha : 0 < a) (b : ℝ) {c : ℝ≥0} (hc : 0 < c) (r : RecData) {w : ℝ≥0 → ℝ} (hw : Continuous w)
    (h0 : InBuffer mL mR Rb g (GW2Sdg.imgState xL xR (scaledPath a b w) 0)) {σ : ℝ≥0} (hσc : σ ≤ c)
    {i : Fin nL} (hi : mL ≤ (i : ℕ))
    (hcol : (GW2Sdg.imgState xL xR (scaledPath a b w) (a * σ)).2.1 i =
      (GW2Sdg.imgState xL xR (scaledPath a b w) (a * σ)).1) :
    exitRule xL xR {p | InBuffer mL mR Rb g p} a b c (r, w) < σ := by
  have hp := continuous_imgState xL xR (continuous_scaledPath a b hw)
  obtain ⟨t, ht, hout⟩ := exists_notMem_before_leftCollision hg hp h0 hi hcol
  have ht₁ : t / a < σ := (div_lt_iff₀ ha).2 (by rwa [mul_comm])
  have heq : a * (t / a) = t := mul_div_cancel₀ t ha.ne'
  have hle := exitRule_le_of_notMem xL xR hB hBc a b hc r hw h0 (ht₁.le.trans hσc)
    (by rw [heq]; exact hout)
  exact hle.trans_lt (ENNReal.coe_lt_coe.2 ht₁)

end InteractingSLE.Theorem14.GW2Bh
