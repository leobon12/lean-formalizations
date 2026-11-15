/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRKappaChart
import InteractingSLE.Spec.Supplement.GW4SafeREtaWord
import InteractingSLE.Spec.Supplement.GW4SafeRKappaRefCover

/-! # GW4: reading physical reference collars in component coordinates -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H fwdMap fwdMapInv fwdHull)

namespace InteractingSLE.Theorem14.GW4Fix

open Sec7.PocketStopSide MartChar RealFlow Restart Exist.StagedLaw
  Supp8.Q3Stop Supp8.GB6.RelDrv

/-- Pulling an incident collar back by a conformal initial chart loses
neither its half-disc inclusion nor its transition limit. -/
theorem own_collar_of_physical_collar {B : Chart} (hB : B.IsConformal)
    {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0)
    {p q x ξ r : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q)
    (hcol : (B.loewner W p).2.1 '' (H ∩ ball (x : ℂ) r) ⊆
      ((B.loewner W q).dom : Set ℂ))
    (htr : Tendsto (fun z => (B.loewner W p).1 ((B.loewner W q).2.1 z))
      (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ))) :
    (Chart.id.loewner W p).2.1 '' (H ∩ ball (x : ℂ) r) ⊆
      ((Chart.id.loewner W q).dom : Set ℂ) ∧
    Tendsto (fun z => (Chart.id.loewner W p).1 ((Chart.id.loewner W q).2.1 z))
      (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ)) := by
  have hpH : MapsTo (fwdMapInv W p) H H := fun _ hy =>
    QuantumZipper.RS.fwdMapInv_mem_H hW hW0 hp hy
  have hqH : MapsTo (fwdMapInv W q) H H := fun _ hy =>
    QuantumZipper.RS.fwdMapInv_mem_H hW hW0 (hp.trans hpq) hy
  refine ⟨?_, htr.congr' (eventually_nhdsWithin_of_forall fun z hz => ?_)⟩
  · rintro _ ⟨y, hy, rfl⟩
    have h := hcol ⟨y, hy, rfl⟩
    rw [dom_own_stage_as_initial_inverse_image hB hW hW0 (hp.trans hpq)] at h
    obtain ⟨v, hv, he⟩ := h
    have hev : v = fwdMapInv W p y := by
      have := congrArg B.1 he
      change B.1 (B.2.1 v) = B.1 (B.2.1 (fwdMapInv W p y)) at this
      rwa [hB.2.2 _ (sdiff_subset hv), hB.2.2 _ (hpH hy.1)] at this
    subst v
    have hDo : ((Chart.id.loewner W q).dom : Set ℂ) = H \ fwdHull W q := by
      rw [(Chart.isConformal_id.loewner hW hW0 (hp.trans hpq)).coe_dom]
      exact QuantumZipper.RS.image_fwdMapInv_H hW hW0 (hp.trans hpq)
    exact hDo.symm ▸ hv
  · change fwdMap W p (B.1 (B.2.1 (fwdMapInv W q z))) = fwdMap W p (fwdMapInv W q z)
    rw [hB.2.2 _ (hqH hz)]

/-- Before the component dies, all earlier physical line clocks equal
its actual capacity clock. -/
theorem component_lineClock_eq_rcap {Ω : Type*} {F : Frame} (hF : F.IsOk)
    {Wd R : ℝ≥0 → Ω → ℝ} {GT : Set Ω} {V : Ω → ℝ≥0∞}
    (hGT : ∀ ω ∈ GT, F.IsPathOk (fun r => Wd r ω)) {ω : Ω} (hω : ω ∈ GT)
    (hRc : Continuous (R · ω)) (hR0 : R 0 ω = 0)
    (hver : ∀ q : ℝ≥0, (q : ℝ≥0∞) < V ω →
      ∃ t, fwdHull (wpath R ω) q = F.hullAt (fun r => Wd r ω) t)
    {t : ℝ≥0} (hLive : lineClock F Wd GT V t ω < V ω) :
    ∀ s : ℝ≥0, s ≤ t →
      ((lineClock F Wd GT V s ω).toNNReal : ℝ) = F.rcap (fun r => Wd r ω) s := by
  have hex := CLoc.lt_exit_of_lineClock_lt hF hGT hω hRc hR0 hver hLive
  have hP : F.physClockG Wd GT t ω < V ω := by
    by_contra hnot
    exact (lt_irrefl _) (hLive.trans_le (le_min (not_lt.1 hnot) le_rfl))
  intro s hst
  have hPs := (Frame.monotone_physClockG hF hGT ω hst).trans_lt hP
  have hse := (ENNReal.coe_le_coe.2 hst).trans_lt hex
  rw [ENNReal.coe_toNNReal_eq_toReal, lineClock, min_eq_left hPs.le]
  change (F.physClockG Wd GT s ω).toReal = _
  rw [Frame.physClockG_eq_rcap hF hGT hω hse,
    ENNReal.toReal_ofReal (Frame.rcap_nonneg hF (hGT ω hω) hse)]

/-- The typed exposed interval is exactly the geometric open seed interval. -/
theorem component_seed_interval_eq {Ω : Type*} (k : ℝ) (c₀ : BoundaryWord)
    (X : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (R : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞)
    {ω : Ω} (hRc : Continuous (R · ω)) (hR0 : R 0 ω = 0) (q : ℝ≥0) :
    Ioo (componentVL k c₀ X R V (componentSeedL k c₀) q ω - R q ω)
      (componentVR k c₀ X R V (componentSeedR k c₀) q ω - R q ω) =
    Ioo (-rightImg (fun r : ℝ => -R r.toNNReal ω) 0 q - R q ω)
      (rightImg (wpath R ω) 0 q - R q ω) := by
  have hL : typedXL k (wordType k c₀) c₀ (componentSeedL k c₀) = 0 := by
    rw [typedXL_self_eq]
    exact Sec4.flowLineXL_zero _ _
  have hR : typedXR k (wordType k c₀) c₀ (componentSeedR k c₀) = 0 := by
    rw [typedXR_self_eq]
    exact Sec4.flowLineXR_zero _ _
  rw [componentVL_eq_geom k c₀ X R V hRc hR0, componentVR_eq_geom k c₀ X R V hRc hR0]
  change Ioo (-rightImg (fun r : ℝ => -R r.toNNReal ω) (-typedXL _ _ _ _) q - _)
    (rightImg (wpath R ω) (typedXR _ _ _ _) q - _) = _
  rw [hL, hR, neg_zero]

end InteractingSLE.Theorem14.GW4Fix
