/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowStopIdentCMIConvWChart

/-! # The reference threshold cannot occur before the buffer exit -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
universe u
namespace InteractingSLE.Restart.FlowStopIdentCMI
open Sec7.PocketTraversal
open FlowStopIdentLL

/-- Centering the left geometric coordinate gives the chart-relative coordinate. -/
theorem geomL_rpath_eq_geomLW_sub {S : Type*} (W : ℝ≥0 → S → ℝ)
    {n : ℕ} (x : Fin n → ℝ) (i : Fin n) (t : ℝ≥0) (ω : S) :
    geomL (Ito.rpath (W · ω)) t (x i) = geomLW W (fun _ => x) i t ω - W t ω := by
  simp only [geomL, geomLW, Ito.rpath, Real.toNNReal_coe]
  rfl

/-- Centering the right geometric coordinate gives the chart-relative coordinate. -/
theorem geomR_rpath_eq_geomRW_sub {S : Type*} (W : ℝ≥0 → S → ℝ)
    {n : ℕ} (x : Fin n → ℝ) (i : Fin n) (t : ℝ≥0) (ω : S) :
    geomR (Ito.rpath (W · ω)) t (x i) = geomRW W (fun _ => x) i t ω - W t ω := by
  simp only [geomR, geomRW, Ito.rpath, Real.toNNReal_coe]
  rfl

namespace CMIVSetting
variable {S : Type u} [MeasurableSpace S] (D : CMIVSetting S)

/-- A continuous driver agreeing before the exit cannot meet the reference
word's continuation threshold earlier. This discharges the clock's threshold field. -/
theorem threshold_of_agree {e : S → ℝ≥0∞} {W : ℝ≥0 → S → ℝ}
    (he : e =ᵐ[D.Q₀] fun ω => RLC.exitTime D.V (D.Γ ω) (D.U ω))
    (hW0 : ∀ ω, W 0 ω = 0) (hWc : ∀ ω, Continuous (W · ω))
    (hag : ∀ᵐ ω ∂D.Q₀, ∀ t : ℝ≥0, (t : ℝ≥0∞) < e ω → W t ω = D.W₀ t ω) :
    ∀ᵐ ω ∂D.Q₀, e ω ≤ MartChar.thresholdTime
      (flowLineRhoL D.κ D.bR D.JR D.y D.θ) (flowLineRhoR D.κ D.bR D.JR D.y D.θ) (W · ω)
      (fun i t => geomLW W (fun _ => flowLineXL D.bR D.JR D.y) i t ω)
      (fun j t => geomRW W (fun _ => flowLineXR D.bR D.JR D.y) j t ω) := by
  classical
  filter_upwards [he, hag, D.coupling.1.ae_isIntegratedSLEPath, D.trace] with ω heω hagω hp hg
  have hag' : ∀ t : ℝ≥0, (t : ℝ≥0∞) < RLC.exitTime D.V (D.Γ ω) (D.U ω) →
      W t ω = D.W₀ t ω := fun t ht => hagω t (heω ▸ ht)
  have hnot : ∀ t : ℝ≥0, (t : ℝ≥0∞) < e ω →
      ¬ ForceWord.ThresholdCondition (flowLineRhoL D.κ D.bR D.JR D.y D.θ)
        (flowLineRhoR D.κ D.bR D.JR D.y D.θ) (W t ω)
        (fun i => geomLW W (fun _ => flowLineXL D.bR D.JR D.y) i t ω)
        (fun j => geomRW W (fun _ => flowLineXR D.bR D.JR D.y) j t ω) := by
    intro t ht
    have htexit : (t : ℝ≥0∞) < RLC.exitTime D.V (D.Γ ω) (D.U ω) := heω ▸ ht
    have htU := htexit.trans_le (min_le_left _ _)
    have hmem := FlowStopIdentG.mem_of_lt_exitTime htexit
    have hreal : (D.Γ ω t - D.y).im = 0 → D.y + (D.Γ ω t - D.y).re ∈ D.O := by
      intro hr
      have h := D.N_real (D.Γ ω t) (D.closureV_subset (subset_closure hmem))
        (by simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero] using hr)
      simpa only [Complex.sub_re, Complex.ofReal_re, add_sub_cancel] using h
    by_cases ht0 : t = 0
    · subst t
      have hy : D.y ∈ D.O := by
        have hz : D.Γ ω 0 = D.y := sub_eq_zero.1 hg.1
        have h := hreal (by rw [hz, sub_self]; rfl)
        simpa only [hz, sub_self, Complex.zero_re, add_zero] using h
      have hcuts := hasCommonCollisionCuts_initial (b := D.b) (J := D.J)
        (bR := D.bR) (JR := D.JR) D.O_open hy
      have hn := hp.isForcePath.not_threshold htU
      rw [hp.isForcePath.w_zero, funext hp.isForcePath.vL_zero, funext hp.isForcePath.vR_zero] at hn
      have hnR := (thresholdCondition_iff_of_commonCollisionCuts D.κ_pos D.b_pc D.bR_pc
        D.boundary_eq hcuts).not.mp hn
      have hzL : (fun i => geomLW W (fun _ => flowLineXL D.bR D.JR D.y) i 0 ω) =
          flowLineXL D.bR D.JR D.y := funext fun i => geomLW_zero hWc hW0
            (xL := fun _ => flowLineXL D.bR D.JR D.y) (flowLineXL_nonpos_seed D.bR D.JR D.y i)
      have hzR : (fun i => geomRW W (fun _ => flowLineXR D.bR D.JR D.y) i 0 ω) =
          flowLineXR D.bR D.JR D.y := funext fun i => geomRW_zero hWc hW0
            (xR := fun _ => flowLineXR D.bR D.JR D.y) (flowLineXR_nonneg_seed D.bR D.JR D.y i)
      simpa only [hW0, hzL, hzR] using hnR
    · have htpos : 0 < t := pos_iff_ne_zero.2 ht0
      have hwzero : Ito.rpath (W · ω) 0 = 0 := by
        simpa only [Ito.rpath, Real.toNNReal_zero] using hW0 ω
      have hagT : ∀ s : ℝ≥0, s < t → Ito.rpath (W · ω) s = D.W₀ s ω := by
        intro s hs
        simpa only [Ito.rpath, Real.toNNReal_coe] using hagω s ((ENNReal.coe_lt_coe.2 hs).trans ht)
      have hcuts := hasCommonCollisionCuts_terminal_images (b := D.b) (J := D.J)
        (bR := D.bR) (JR := D.JR) (D := Ito.rpath (W · ω)) D.O_open hg htpos htU.le
        ((hWc ω).comp continuous_real_toNNReal) hwzero hagT hreal
      obtain ⟨-, -, hL, hR, -, -⟩ := stopPathData_det D.V_bounded D.closureV_real D.hull_subset
        hp hg (hWc ω) hag' htexit
      have hVL : (fun i => D.VL₀ i t ω) =
          (fun i => geomLW W (fun _ => flowLineXL D.b D.J D.y) i t ω) := by
        funext i
        apply sub_left_inj.mp
        simpa only [geomL_rpath_eq_geomLW_sub, hagω t ht] using hL i
      have hVR : (fun i => D.VR₀ i t ω) =
          (fun i => geomRW W (fun _ => flowLineXR D.b D.J D.y) i t ω) := by
        funext i
        apply sub_left_inj.mp
        simpa only [geomR_rpath_eq_geomRW_sub, hagω t ht] using hR i
      have hr : Bessel.realPath W ω = Ito.rpath (W · ω) := rfl
      have hl : Bessel.realPath (fun t ω => -W t ω) ω = (fun s => -Ito.rpath (W · ω) s) := rfl
      have hcuts' : HasCommonCollisionCuts D.b D.J D.bR D.JR D.y D.O (W t ω)
        (fun i => geomLW W (fun _ => flowLineXL D.b D.J D.y) i t ω)
        (fun j => geomRW W (fun _ => flowLineXR D.b D.J D.y) j t ω) (W t ω)
        (fun i => geomLW W (fun _ => flowLineXL D.bR D.JR D.y) i t ω)
        (fun j => geomRW W (fun _ => flowLineXR D.bR D.JR D.y) j t ω) := by
        simpa only [geomLW, geomRW, hr, hl, Ito.rpath, Real.toNNReal_coe] using hcuts
      rw [← hVL, ← hVR, hagω t ht] at hcuts'
      have hn := (thresholdCondition_iff_of_commonCollisionCuts D.κ_pos D.b_pc D.bR_pc
        D.boundary_eq hcuts').not.mp (hp.isForcePath.not_threshold htU)
      simpa only [hagω t ht] using hn
  by_contra hle
  have hlt := lt_of_not_ge hle
  have hne := ne_top_of_lt hlt
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 hne
  have hte : (t : ℝ≥0∞) = MartChar.thresholdTime
      (flowLineRhoL D.κ D.bR D.JR D.y D.θ) (flowLineRhoR D.κ D.bR D.JR D.y D.θ) (W · ω)
      (fun i t => geomLW W (fun _ => flowLineXL D.bR D.JR D.y) i t ω)
      (fun j t => geomRW W (fun _ => flowLineXR D.bR D.JR D.y) j t ω) := ht
  have hmem := MartChar.thresholdTime_mem_thresholdSet (hWc ω)
    (fun i => (isForcePath_geomLW hWc (fun _ => flowLineXL D.bR D.JR D.y) ω i).1)
    (fun j => (isForcePath_geomRW hWc (fun _ => flowLineXR D.bR D.JR D.y) ω j).1)
    (fun i j s t hst => geomLW_merge hWc (fun _ => flowLineXL D.bR D.JR D.y) ω i j s t hst)
    (fun i j s t hst => geomRW_merge hWc (fun _ => flowLineXR D.bR D.JR D.y) ω i j s t hst) ht.symm
  exact hnot t (by rw [hte]; exact hlt) hmem

end CMIVSetting
end InteractingSLE.Restart.FlowStopIdentCMI
