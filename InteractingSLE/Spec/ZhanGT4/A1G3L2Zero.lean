/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A1G3L2Ident
import InteractingSLE.Spec.ZhanGT4.TwoTime2Other
import InteractingSLE.SLE8.TraceBridge
import InteractingSLE.Foundations.Loewner.FiniteEndpoint
import InteractingSLE.Spec.ZhanGT4.A1SeedFieldPath

/-!
# Zhan's A.1 under R83: the seeded image at own time `0`

Packet PROVE-A1-G3LAW2. Deterministic facts at own time `0` of an image chain (`OwnData`), used for the initial word of
the seeded capacity geometry (generic):

* **`continuousAt_fwdMap_of_isForwardSol`**: the Loewner map at an alive real point is continuous (holomorphic on the
  alive disc, TWOTIME2's `differentiableOn_fwdMap_aliveDisc`);
* **`isForwardSol_extPath_of_force`**: a force process of an integrated path is a real forward solution of the driver;
* **`imgStart_eq_of_ownData`**: the image chain starts at the boundary value of the frozen chart at the image curve's
  start (`W'(0) = Re φ(0)`, `φ` continuous at `0`);
* **`ownExt_zero_eq`**: at own time `0` the own map is the frozen chart at every real point off the closed frozen hull
  where the chart is continuous (`F₀(v) = φ(v)`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4.A1G3L2

open QuantumZipper (H fwdHull fwdMap IsForwardSol)
open A2X A1Ref

/-- **The Loewner map is continuous at an alive real point** (driver continuous on `[0, τ']`, `σ < τ'`). -/
theorem continuousAt_fwdMap_of_isForwardSol {w : ℝ → ℝ} {σ τ' : ℝ} (hστ : σ < τ') (hσ : 0 ≤ σ)
    (hw : ContinuousOn w (Icc 0 τ')) {p : ℂ} {u : ℝ → ℂ} (hu : IsForwardSol w p σ u) :
    ContinuousAt (fwdMap w σ) p := by
  set V := stopDrv w τ' with hVdef
  have hVc : Continuous V := continuous_stopDrv hw (hσ.trans hστ.le)
  have hVe : EqOn V w (Icc 0 σ) := fun r hr => stopDrv_eqOn w τ' ⟨hr.1, hr.2.trans hστ.le⟩
  have hfun : fwdMap V σ = fwdMap w σ := funext fun z => Ito.fwdMap_congr_of_eqOn hVe
  have hu' : IsForwardSol V p σ u := QuantumZipper.isForwardSol_congr_drive (fun r hr => (hVe hr).symm) hu
  obtain ⟨δ, hδ, hlow, hmem⟩ := exists_aliveDisc_self hu' hσ
  have hd := differentiableOn_fwdMap_aliveDisc hVc hu' hδ hlow (t := σ) ⟨hσ, le_rfl⟩
  rw [← hfun]
  exact (hd.differentiableAt (isOpen_ball.mem_nhds hmem)).continuousAt

/-- **A force process of a path is a real forward solution of the driver** up to a time before the lifetime at which
it has not met the driver. -/
theorem isForwardSol_extPath_of_force {w v : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hv : ContinuousOn v {t | (t : ℝ≥0∞) < ζ})
    (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) {p : ℝ}
    (hveq : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → v t = p + ∫ s in (0 : ℝ)..t, 2 / (v s.toNNReal - w s.toNNReal))
    {T : ℝ≥0} (hT : (T : ℝ≥0∞) < ζ) (hsep : ∀ r ≤ T, v r ≠ w r) :
    IsForwardSol (Strip.extPath w) (p : ℂ) T (fun s => ((Strip.extPath v s - Strip.extPath w s : ℝ) : ℂ)) := by
  have hvc : ContinuousOn (Strip.extPath v) (Icc 0 (T : ℝ)) :=
    A1Ref.continuousOn_extPath_Icc hv (by rw [ENNReal.ofReal_coe_nnreal]; exact hT)
  have hwc : ContinuousOn (Strip.extPath w) (Icc 0 (T : ℝ)) :=
    A1Ref.continuousOn_extPath_Icc hw (by rw [ENNReal.ofReal_coe_nnreal]; exact hT)
  refine ⟨continuous_ofReal.comp_continuousOn (hvc.sub hwc), fun s hs => ⟨?_, ?_⟩⟩
  · simp only [ne_eq, ofReal_eq_zero, sub_eq_zero, Strip.extPath]
    exact hsep _ (Real.toNNReal_le_iff_le_coe.2 hs.2)
  · have hint : ∫ r in (0 : ℝ)..s, (2 : ℂ) / ((Strip.extPath v r - Strip.extPath w r : ℝ) : ℂ) =
        ((∫ r in (0 : ℝ)..s, 2 / (v r.toNNReal - w r.toNNReal) : ℝ) : ℂ) := by
      rw [← intervalIntegral.integral_ofReal]
      refine intervalIntegral.integral_congr fun r _ => ?_
      simp only [Strip.extPath]
      push_cast
      rfl
    have hsT : (s.toNNReal : ℝ≥0∞) < ζ := by
      refine lt_of_le_of_lt (ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hs.2)) hT
    have hve := hveq s.toNNReal hsT
    rw [Real.coe_toNNReal s hs.1] at hve
    rw [hint]
    simp only [Strip.extPath]
    rw [hve]
    push_cast
    ring

/-- **The image chain starts at the boundary value of the frozen chart** at the image curve's start, when the chart is
continuous there. -/
theorem imgStart_eq_of_ownData {W W' a : ℝ → ℝ} {wk : ℝ → ℝ} {xk τ S : ℝ}
    (hown : OwnData W (physHull xk wk τ) (physMap xk wk τ) S a W')
    (hcont : ContinuousAt (physMap xk wk τ) ((0 : ℝ) : ℂ)) :
    W' 0 = (physMap xk wk τ ((0 : ℝ) : ℂ)).re := by
  have hIs := (isImgDrvOn_of_ownData hown).1
  have : (𝓝[H] ((0 : ℝ) : ℂ)).NeBot := FiniteEndpoint.neBot_nhdsWithin_H (by simp)
  have h1 : Tendsto (physMap xk wk τ) (𝓝[H] ((0 : ℝ) : ℂ)) (𝓝 (W' 0 : ℂ)) := hIs.2.1
  have h2 : Tendsto (physMap xk wk τ) (𝓝[H] ((0 : ℝ) : ℂ)) (𝓝 (physMap xk wk τ ((0 : ℝ) : ℂ))) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  have he := tendsto_nhds_unique h1 h2
  rw [← he, ofReal_re]

/-- **At own time `0` the own map is the frozen chart** at a real point off the closed frozen hull where the chart is
continuous. -/
theorem ownExt_zero_eq {W W' a : ℝ → ℝ} {A : Set ℂ} {φ : ℂ → ℂ} {T : ℝ} (h : OwnData W A φ T a W') {v : ℝ}
    (hvA : (v : ℂ) ∉ closure A) (hφ : ContinuousAt φ v) : ownExt W W' a φ 0 v = φ v := by
  have him : ((v : ℝ) : ℂ).im = 0 := ofReal_im v
  have : (𝓝[H] (v : ℂ)).NeBot := FiniteEndpoint.neBot_nhdsWithin_H him
  have hU : (closure A)ᶜ ∈ 𝓝 (v : ℂ) := isClosed_closure.isOpen_compl.mem_nhds hvA
  have hev : ∀ᶠ z in 𝓝[H] (v : ℂ), ownMap W W' a φ 0 z = φ z := by
    filter_upwards [nhdsWithin_le_nhds hU, self_mem_nhdsWithin] with z hzA hzH
    have hzA' : z ∉ A := fun hz => hzA (subset_closure hz)
    have hinv : invMap W 0 z = z := by
      unfold invMap
      rw [h.zero, ofReal_zero, sub_zero]
      exact SLE8.fwdMapInv_zero_eq_self h.cont h.zero hzH
    have hφH : φ z ∈ H := h.mapOut.1.2.mapsTo ⟨hzH, hzA'⟩
    have hne : φ z ≠ (W' 0 : ℂ) := fun he => by
      have h1 : (0 : ℝ) < (φ z).im := hφH
      rw [he, ofReal_im] at h1
      exact lt_irrefl 0 h1
    simp only [ownMap, hinv, h.a0, QuantumZipper.B5.fwdMap_zero_time W' hne]
    ring
  have ht : Tendsto (ownMap W W' a φ 0) (𝓝[H] (v : ℂ)) (𝓝 (φ v)) :=
    (hφ.tendsto.mono_left nhdsWithin_le_nhds).congr' (hev.mono fun z hz => hz.symm)
  unfold ownExt
  simp only [him, lt_irrefl, ↓reduceIte]
  exact ht.limUnder_eq

end InteractingSLE.ZhanGT4.A1G3L2
