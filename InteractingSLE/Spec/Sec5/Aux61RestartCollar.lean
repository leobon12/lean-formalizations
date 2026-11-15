import InteractingSLE.Spec.Sec5.Aux61RestartComponent
import InteractingSLE.Foundations.Loewner.YuanTrace

/-!
# Selecting the current restart component from an own-chart collar

Packet PROVE-AUX61-R1; ruling R71 and Astra follow-up 4, lines 109–114.
The own inverse chart tends to the current tip. A separated tip therefore has
a small half-disc whose image avoids the retained hull. This image determines
the current component using only the old chart and the retained boundary.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open QuantumZipper (H fwdMapInv fwdHull)

namespace InteractingSLE.Sec5.Aux61Restart

/-- A free half-disc in the old inverse chart determines the current component
without evaluating the future curve. The map `F` is the own inverse chart and
`F(0)` is represented by its actual limit `η r`. -/
theorem exists_restart_halfDisk_collar {K : Set ℂ} {η : ℝ → ℂ} {r : ℝ}
    {F : ℂ → ℂ} (hKo : IsOpen (H \ K)) (htip : η r ∈ H \ K)
    (hFc : ContinuousOn F H) (hFD : MapsTo F H (H \ η '' Icc 0 r))
    (hlim : Tendsto F (𝓝[H] 0) (𝓝 (η r))) :
    ∃ δ > 0, F ((δ / 2 : ℝ) * I) ∈ retainedDomain K η r ∧
      F '' (ball 0 δ ∩ H) ⊆
        restartComponent K η r (F ((δ / 2 : ℝ) * I)) := by
  obtain ⟨δ, hδ, hfree⟩ := Metric.mem_nhdsWithin_iff.1
    (hlim.eventually (hKo.mem_nhds htip))
  have hsubset : F '' (ball 0 δ ∩ H) ⊆ retainedDomain K η r := by
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨(hFD hz.2).1, fun h => h.elim (hfree hz).2 (hFD hz.2).2⟩
  have hpoint : ((δ / 2 : ℝ) : ℂ) * I ∈ ball 0 δ ∩ H := by
    constructor
    · rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (half_pos hδ), norm_I, mul_one]
      exact half_lt_self hδ
    · change 0 < (((δ / 2 : ℝ) : ℂ) * I).im
      simpa only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re,
        mul_zero, add_zero] using half_pos hδ
  have hc : IsPreconnected (ball (0 : ℂ) δ ∩ H) :=
    ((convex_ball (0 : ℂ) δ).inter
      (convex_halfSpace_gt (f := fun z : ℂ => z.im) Complex.imLm.isLinear 0)).isPreconnected
  refine ⟨δ, hδ, hsubset (mem_image_of_mem F hpoint), ?_⟩
  exact (hc.image F (hFc.mono inter_subset_right)).subset_connectedComponentIn
    (mem_image_of_mem F hpoint) hsubset

/-- The own inverse Loewner chart supplies the collar at every separated tip.
This is a deterministic statement about the retained past, without an
independence assumption on the histories. -/
theorem exists_restart_halfDisk_collar_of_trace {K : Set ℂ} {η : ℝ → ℂ}
    {W : ℝ → ℝ} {r : ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    (hr : 0 ≤ r) (hη : IsLoewnerTrace W η) (hKo : IsOpen (H \ K))
    (htip : η r ∈ H \ K) :
    ∃ δ > 0, fwdMapInv W r ((δ / 2 : ℝ) * I) ∈ retainedDomain K η r ∧
      fwdMapInv W r '' (ball 0 δ ∩ H) ⊆
        restartComponent K η r (fwdMapInv W r ((δ / 2 : ℝ) * I)) := by
  have hF := isConformalBijection_fwdMapInv hW hW0 hr
  refine exists_restart_halfDisk_collar hKo htip hF.1.continuousOn ?_
    (hη.tendsto_fwdMapInv_tip hW hW0 hr)
  intro z hz
  have hmem := hF.2.mapsTo hz
  refine ⟨hmem.1, ?_⟩
  rintro ⟨u, hu, hue⟩
  apply hmem.2
  rw [hη.2.2 r hr]
  exact mem_fillH_of_mem_closure hmem.1 (subset_closure ⟨u, hu, hue⟩)

/-- R71's positive-clearance hypothesis supplies the free own-chart collar. -/
theorem exists_restart_halfDisk_collar_of_pos_infDist {K : Set ℂ} {η : ℝ → ℂ}
    {W : ℝ → ℝ} {r : ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    (hr : 0 ≤ r) (hη : IsLoewnerTrace W η) (hKo : IsOpen (H \ K))
    (htipH : η r ∈ H) (hclear : 0 < infDist (η r) K) :
    ∃ δ > 0, fwdMapInv W r ((δ / 2 : ℝ) * I) ∈ retainedDomain K η r ∧
      fwdMapInv W r '' (ball 0 δ ∩ H) ⊆
        restartComponent K η r (fwdMapInv W r ((δ / 2 : ℝ) * I)) := by
  exact exists_restart_halfDisk_collar_of_trace hW hW0 hr hη hKo
    ⟨htipH, fun hmem => hclear.ne' (infDist_zero_of_mem hmem)⟩

end InteractingSLE.Sec5.Aux61Restart
