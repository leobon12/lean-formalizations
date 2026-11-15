/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossRestartKernelCfFinite
import InteractingSLE.Spec.Sec5.CrossCondGenLaw

/-!
# Surviving original-real collars in the relative image chart

PROVE-CROSSCOND-GEN. Extract the local part of the nonsimple restart proof: at
surviving real collars the inherited transition branch tends to zero. Only local
clearance from the three relevant hulls is used, so earlier real contacts elsewhere
are permitted. The existing generic restart mean-transfer theorem then transports
matching boundary heights. The global classification of surviving collars remains
separate from these pointwise results.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open QuantumZipper (H fwdHull fwdMap fwdMapInv logDerivFwd)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec5.CrossCond.Gen

open WangWu GlueImg

variable {WA UC WI : ℝ → ℝ} {t s T : ℝ}

/-- The normalized transition branch vanishes at a surviving original-real collar.
This is the local argument of `CrossRestartKernelCfReal`, with clearance at the
actual three points in place of a premise excluding every earlier real contact. -/
theorem tendsto_imgBranch_zero_of_clearance
    (hA : Continuous WA) (hA0 : WA 0 = 0) (ht : 0 ≤ t)
    (hC : Continuous UC) (hC0 : UC 0 = 0) (hs : 0 ≤ s)
    (hI : Continuous WI) (hI0 : WI 0 = 0) (hT : 0 ≤ T)
    {x p r : ℝ} (hp : p ≠ 0)
    (hPhi : Tendsto (fun y => revChartInv UC s (fwdMapInv WI T y))
      (𝓝[H] (x : ℂ)) (𝓝[H] (p : ℂ)))
    (hInv : Tendsto (fwdMapInv WI T) (𝓝[H] (x : ℂ)) (𝓝[H] (r : ℂ)))
    (hpA : (p : ℂ) ∉ closure (fwdHull WA t))
    (hrI : (r : ℂ) ∉ closure (fwdHull WI T))
    (hpC : ((-p⁻¹ : ℝ) : ℂ) ∉ closure (fwdHull UC s)) :
    Tendsto (imgBranch WA t UC s WI T) (𝓝[H] (x : ℂ)) (𝓝 0) := by
  obtain ⟨δA, hδA, hdA⟩ := exists_ball_disjoint_of_notMem_closure hpA
  have hLA := (Restart.IsCanonicalDerivLog.tendsto_im_nhdsWithin_zero (isHPHull_fwdHull hA ht)
    (Sec7.SideHeight.isCanonicalDerivLog_fwdMap hA hA0 ht) (isMapOut_fwdMap hA hA0 ht) hδA hdA).comp hPhi
  obtain ⟨δI, hδI, hdI⟩ := exists_ball_disjoint_of_notMem_closure hrI
  have hLI := (Restart.IsCanonicalDerivLog.tendsto_im_nhdsWithin_zero (isHPHull_fwdHull hI hT)
    (Sec7.SideHeight.isCanonicalDerivLog_fwdMap hI hI0 hT) (isMapOut_fwdMap hI hI0 hT) hδI hdI).comp hInv
  obtain ⟨δC, hδC, hdC⟩ := exists_ball_disjoint_of_notMem_closure hpC
  have hLC := (tendsto_im_logDerivPsi hC hC0 hs hp hδC hdC).comp hPhi
  simpa only [imgBranch, Function.comp_apply, add_zero, sub_zero] using hLA.sub (hLI.add hLC)

/-- Matching word heights at a protected original-real collar give the image mean
limit. The branch term is discharged by the preceding local clearance theorem;
mean transfer itself is the generic nonsimple restart theorem. -/
theorem tendsto_imageMean_of_clearance
    (hA : Continuous WA) (hA0 : WA 0 = 0) (ht : 0 ≤ t)
    (hC : Continuous UC) (hC0 : UC 0 = 0) (hs : 0 ≤ s)
    (hI : Continuous WI) (hI0 : WI 0 = 0) (hT : 0 ≤ T)
    (hK : fwdHull WI T = revChart UC s '' fwdHull WA t)
    {x p r q : ℝ} (hp : p ≠ 0)
    (hPhi : Tendsto (fun y => revChartInv UC s (fwdMapInv WI T y))
      (𝓝[H] (x : ℂ)) (𝓝[H] (p : ℂ)))
    (hInv : Tendsto (fwdMapInv WI T) (𝓝[H] (x : ℂ)) (𝓝[H] (r : ℂ)))
    (hpA : (p : ℂ) ∉ closure (fwdHull WA t))
    (hrI : (r : ℂ) ∉ closure (fwdHull WI T))
    (hpC : ((-p⁻¹ : ℝ) : ℂ) ∉ closure (fwdHull UC s))
    (hTheta : Tendsto (imgTheta WA t UC s WI T) (𝓝[H] (x : ℂ)) (𝓝 (q : ℂ)))
    {M uA u : ℂ → ℝ} {c χ dA dI : ℝ}
    (huA : Tendsto uA (𝓝[H] (q : ℂ)) (𝓝 dA))
    (hu : Tendsto u (𝓝[H] (x : ℂ)) (𝓝 dI)) (hdata : dI = dA)
    (hOwn : Tendsto (fun y => M (revChartInv UC s (fwdMapInv WI T y)) + c -
      (uA (imgTheta WA t UC s WI T y) -
        χ * (logDerivFwd WA t (revChartInv UC s (fwdMapInv WI T y))).im))
      (𝓝[H] (x : ℂ)) (𝓝 0)) :
    Tendsto (fun y => M (revChartInv UC s (fwdMapInv WI T y)) + c -
      (u y - χ * ((logDerivFwd WI T (fwdMapInv WI T y)).im +
        (logDerivPsi UC s (revChartInv UC s (fwdMapInv WI T y))).im)))
      (𝓝[H] (x : ℂ)) (𝓝 0) := by
  have harg := tendsto_imgBranch_zero_of_clearance hA hA0 ht hC hC0 hs hI hI0 hT
    hp hPhi hInv hpA hrI hpC
  have hThetaH : ∀ y ∈ H, imgTheta WA t UC s WI T y ∈ H := by
    intro y hy
    have hm := revChartInv_fwdMapInv_mem hC hC0 hs hI hI0 hT hK hy
    exact QuantumZipper.FwdHolo.mapsTo_fwdMap hA ht
      ⟨hm.1, fun h => hm.2 (Or.inl h)⟩
  exact CrossRestart.tendsto_imgChart_of_newChart hThetaH hTheta huA hu hdata harg hOwn

/-- The existing nonsimple restart setup excludes any positive-time real contact
of the new curve. This records the exact remaining restriction of that API. -/
theorem not_isCfImgSetup_of_boundary_contact {α η : ℝ → ℂ}
    {r : ℝ} (hr : r ∈ Ioc (0 : ℝ) t) (hreal : (α r).im = 0) :
    ¬ CrossRestart.IsCfImgSetup WA α t UC s WI η T := by
  intro hd
  have h := hd.hαH r hr
  change 0 < (α r).im at h
  rw [hreal] at h
  exact lt_irrefl 0 h

end InteractingSLE.Sec5.CrossCond.Gen
