/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRMuCollar
import InteractingSLE.Spec.Supplement.GW4SafeRLambdaPhaseLimit
import InteractingSLE.Spec.Supplement.GW4SafeRLambdaOwn

/-! # GW4: exposed component mean limits from the same protected reference -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter Topology Metric MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull fwdMapInv logDerivFwd chiC)
open LQGMetric (DistOn)
open SupercriticalConformalCovariance.GM24 (smoothDist)

namespace InteractingSLE.Theorem14.GW4Fix

open Restart LocalSets WholeField GW4Rel GW4Traverse MartChar RealFlow
open Sec7.PocketStopSide Sec7.Aux119Heights

/-- A protected ambient height, the actual transported reference mean and
the zero reference increment give the exposed component limit. The phase
is the previously selected common phase, not a new integer per access. -/
theorem exposed_component_limits_of_reference_heights
    {Ω : Type*} {κ : ℝ} (hκ : 0 < κ) {c₀ : BoundaryWord} {F : Frame} (hF : F.IsOk)
    {X : Ω → DistOn upperHalfPlaneOpens} {Wd R : ℝ≥0 → Ω → ℝ} {GT : Set Ω}
    {V : Ω → ℝ≥0∞} {ω : Ω} (hω : ω ∈ GT)
    (hGT : ∀ ω ∈ GT, F.IsPathOk (fun r => Wd r ω))
    (hRc : Continuous (R · ω)) (hR0 : R 0 ω = 0)
    (hVer : ∀ q : ℝ≥0, (q : ℝ≥0∞) < V ω →
      ∃ t, fwdHull ((fun r : ℝ => R r.toNNReal ω)) q = F.hullAt (fun r => Wd r ω) t)
    {A B : ℝ≥0 → Ω → Set ℂ} {M : ℝ≥0 → Ω → DistOn upperHalfPlaneOpens}
    {G : ℚ → Ω → DistOn upperHalfPlaneOpens} {g : Ω → DistOn upperHalfPlaneOpens}
    {u : ℂ → ℝ} (hu : InnerProductSpace.HarmonicOnNhd u H)
    {d : ℝ≥0 → Ω → ℝ} (hd : ∀ p q, d p ω = d q ω)
    {t q : ℝ≥0} (hLive : lineClock F Wd GT V t ω < V ω) (_hq : 0 < q)
    (hqt : q = (lineClock F Wd GT V t ω).toNNReal)
    (hAo : ∀ s, IsOpen (H \ A s ω))
    (hMh : ∀ s : ℚ, IsHarmonicDistOn (M (s : ℝ).toNNReal ω) (H \ A (s : ℝ).toNNReal ω))
    (hSet : ∀ s : ℚ, (s : ℝ).toNNReal ≤ t →
      H \ B (s : ℝ).toNNReal ω = H \ CLoc.chartSet F.c (A (s : ℝ).toNNReal ω))
    (hMean : ∀ s : ℚ, (s : ℝ).toNNReal ≤ t →
      G s ω = invField κ (Chart.chartTransport
        (GW3Law.isConformal_of_isComponentChart hF.2.2.2.1
          (Frame.isOpen_C hF (hGT ω hω)) (GW4Traverse.subset_H_of_mem_betweenComponents hF.2.1))
        1 0 (chiC κ) (M (s : ℝ).toNNReal ω)) - smoothDist upperHalfPlaneOpens u)
    (hShape : ∀ s : ℚ, (s : ℝ).toNNReal ≤ t →
      H \ B (s : ℝ).toNNReal ω = H \ fwdHull ((fun r : ℝ => R r.toNNReal ω))
        (lineClock F Wd GT V (s : ℝ).toNNReal ω).toNNReal)
    (hGerm : ∀ s : ℚ, (s : ℝ).toNNReal ≤ t → ∀ ξ x r : ℝ, 0 < r →
      (componentLineChart F Wd GT R V (s : ℝ).toNNReal ω).2.1 '' (H ∩ ball (x : ℂ) r) ⊆
        ((componentLineChart F Wd GT R V t ω).dom : Set ℂ) →
      Tendsto (fun y => (componentLineChart F Wd GT R V (s : ℝ).toNNReal ω).1
        ((componentLineChart F Wd GT R V t ω).2.1 y)) (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ)) →
      Tendsto (fun y => harmRep (g ω) (H \ B t ω)
          ((componentLineChart F Wd GT R V t ω).2.1 y) -
        harmRep (G s ω) (H \ B (s : ℝ).toNNReal ω)
          ((componentLineChart F Wd GT R V t ω).2.1 y)) (𝓝[H] (ξ : ℂ)) (𝓝 0))
    (hPhase : ∀ s p : ℝ≥0, F.ent (fun r => Wd r ω) ≤ s →
      (s : ℝ≥0∞) < F.exit (fun r => Wd r ω) → 0 < p → (p : ℝ≥0∞) < V ω →
      (p : ℝ) = F.rcap (fun r => Wd r ω) s → ∀ x ∈ Ioo
        (-rightImg (fun r : ℝ => -R r.toNNReal ω) 0 p - R p ω)
        (rightImg ((fun r : ℝ => R r.toNNReal ω)) 0 p - R p ω),
      Tendsto (fun y => chiC (16 / κ) *
        ((componentAmbientChart F.c ((fun r : ℝ => R r.toNNReal ω)) p).2.2
          ((componentAmbientChart F.c ((fun r : ℝ => R r.toNNReal ω)) p).2.1 y) -
        (logDerivFwd ((fun r : ℝ => Wd r.toNNReal ω)) s
          ((componentAmbientChart F.c ((fun r : ℝ => R r.toNNReal ω)) p).2.1 y)).im) +
        2 * Real.pi * chiC (16 / κ)) (𝓝[H] (x : ℂ)) (𝓝 (d p ω)))
    (hCover : let w := fun r => Wd r ω
      let R' := fun r => R r ω
      ∃ S : Set ℂ, S.Finite ∧ ∀ ξ ∈ Ioo
        (-rightImg (fun r : ℝ => -R' r.toNNReal) 0 q - R' q)
        (rightImg (fun r : ℝ => R' r.toNNReal) 0 q - R' q), ξ ≠ 0 → ∀ p : ℂ,
        Tendsto (componentAmbientChart F.c (fun r : ℝ => R' r.toNNReal) q).2.1
          (𝓝[H] (ξ : ℂ)) (𝓝 p) → p ∉ S →
        ∃ s : ℚ, (F.ent (fun r => w r) : ℝ) < s ∧ (s : ℝ) < t ∧
          0 < F.rcap (fun r => w r) (s : ℝ).toNNReal ∧
          F.rcap (fun r => w r) (s : ℝ).toNNReal < F.rcap (fun r => w r) t ∧
          ∃ x r : ℝ, x ∈ Ioo
            (-rightImg (fun u : ℝ => -R' u.toNNReal) 0
              (F.rcap (fun u => w u) (s : ℝ).toNNReal) -
              R' (F.rcap (fun u => w u) (s : ℝ).toNNReal).toNNReal)
            (rightImg (fun u : ℝ => R' u.toNNReal) 0
              (F.rcap (fun u => w u) (s : ℝ).toNNReal) -
              R' (F.rcap (fun u => w u) (s : ℝ).toNNReal).toNNReal) ∧ 0 < r ∧
          (componentAmbientChart F.c (fun u : ℝ => R' u.toNNReal)
            (F.rcap (fun u => w u) (s : ℝ).toNNReal)).2.1 '' (H ∩ Metric.ball (x : ℂ) r) ⊆
              ((componentAmbientChart F.c (fun u : ℝ => R' u.toNNReal) q).dom : Set ℂ) ∧
          Tendsto (fun y => (componentAmbientChart F.c (fun u : ℝ => R' u.toNNReal)
            (F.rcap (fun u => w u) (s : ℝ).toNNReal)).1
              ((componentAmbientChart F.c (fun u : ℝ => R' u.toNNReal) q).2.1 y))
            (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ)) ∧
          Tendsto (fun y => (componentAmbientChart F.c (fun u : ℝ => R' u.toNNReal) q).2.2
              ((componentAmbientChart F.c (fun u : ℝ => R' u.toNNReal) q).2.1 y) -
            (componentAmbientChart F.c (fun u : ℝ => R' u.toNNReal)
              (F.rcap (fun u => w u) (s : ℝ).toNNReal)).2.2
              ((componentAmbientChart F.c (fun u : ℝ => R' u.toNNReal) q).2.1 y))
            (𝓝[H] (ξ : ℂ)) (𝓝 0) ∧
          Tendsto (fun y => harmRep (invField κ (M (s : ℝ).toNNReal ω))
              (WangWu.negInv '' (H \ A (s : ℝ).toNNReal ω))
              ((componentAmbientChart F.c (fun r : ℝ => R' r.toNNReal) q).2.1 y) + chiC (16 / κ) *
              (logDerivFwd (fun r : ℝ => w r.toNNReal) (s : ℝ).toNNReal
                ((componentAmbientChart F.c (fun r : ℝ => R' r.toNNReal) q).2.1 y)).im)
            (𝓝[H] (ξ : ℂ))
            (𝓝 (if ξ < 0 then -(Real.pi / Real.sqrt (16 / κ)) else Real.pi / Real.sqrt (16 / κ))) ) :
    ∃ T : Set ℂ, T.Finite ∧ ∀ ξ : ℝ,
      ξ ∉ componentLineJumps (16 / κ) c₀ F X Wd GT R V t ω →
      ξ ∈ Ioo
        (componentVL (16 / κ) c₀ X R V (componentSeedL (16 / κ) c₀) q ω - R q ω)
        (componentVR (16 / κ) c₀ X R V (componentSeedR (16 / κ) c₀) q ω - R q ω) →
      extendFrom H (componentLineChart F Wd GT R V t ω).2.1 (ξ : ℂ) ∉ T →
      Tendsto (fun y => harmRep (g ω) (H \ B t ω) (fwdMapInv ((fun r : ℝ => R r.toNNReal ω)) q y) +
        u (fwdMapInv ((fun r : ℝ => R r.toNNReal ω)) q y) + chiC (16 / κ) *
          (logDerivFwd ((fun r : ℝ => R r.toNNReal ω)) q (fwdMapInv ((fun r : ℝ => R r.toNNReal ω)) q y)).im)
        (𝓝[H] (ξ : ℂ))
        (𝓝 (componentLinePhaseData (16 / κ) c₀ F X Wd GT R V d t ω ξ)) := by
  have hw := hGT ω hω
  have hCo := Frame.isOpen_C hF hw
  have hCH := GW4Traverse.subset_H_of_mem_betweenComponents hF.2.1
  have hB := (Chart.isConformal_infinitySourceChart.trans
    (GW3Law.isConformal_of_isComponentChart hF.2.2.2.1 hCo hCH)).trans
      Chart.isConformal_infinitySourceChart
  have hRR : Continuous ((fun r : ℝ => R r.toNNReal ω)) := hRc.comp continuous_real_toNNReal
  have hRR0 : (fun r : ℝ => R r.toNNReal ω) 0 = 0 := by simpa only [wpath, Real.toNNReal_zero] using hR0
  have hClock := component_lineClock_eq_rcap hF hGT hω hRc hR0 hVer hLive
  have hqtCap : (q : ℝ) = F.rcap (fun r => Wd r ω) t := hqt ▸ hClock t le_rfl
  have hqV : (q : ℝ≥0∞) < V ω := by
    rw [hqt, ENNReal.coe_toNNReal (ne_top_of_lt hLive)]
    exact hLive
  have htExit := CLoc.lt_exit_of_lineClock_lt hF hGT hω hRc hR0 hVer hLive
  obtain ⟨S, hS, hCoverS⟩ := hCover
  obtain ⟨T, hT, hAccess⟩ := Frame.exists_finite_own_access_exceptions hF hw hS
  obtain ⟨v, hv⟩ := hVer q hqV
  obtain ⟨Fb, hFb, hFbc⟩ := Frame.exists_inverse_extension_of_hullAt hF hw hRR hRR0 hv
  have hFbH : MapsTo Fb H H := fun y hy => hFb hy ▸
    QuantumZipper.RS.fwdMapInv_mem_H hRR hRR0 q.coe_nonneg hy
  refine ⟨T, hT, fun ξ hJ hSeed hξT => ?_⟩
  have hξ0 : ξ ≠ 0 := by
    intro he
    apply hJ
    simp only [componentLineJumps, forceJumpSet, he, mem_insert_iff, true_or]
  have hSeedGeom := (component_seed_interval_eq (16 / κ) c₀ X R V hRc hR0 q) ▸ hSeed
  obtain ⟨p, hpS, hland⟩ := hAccess ((fun r : ℝ => R r.toNNReal ω)) q Fb hFb hFbc hFbH ξ (by
    change extendFrom H (fwdMapInv ((fun r : ℝ => R r.toNNReal ω))
      (lineClock F Wd GT V t ω).toNNReal) (ξ : ℂ) ∉ T at hξT
    simpa only [← hqt] using hξT)
  obtain ⟨s, hsEnt, hst, hsCap0, hsCapLt, x, r, hx, hr, hCol, hTr, hLift, hHeight⟩ :=
    hCoverS ξ hSeedGeom hξ0 p hland hpS
  have hsn : (s : ℝ).toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.2 hst.le
  let v : ℝ≥0 := (lineClock F Wd GT V (s : ℝ).toNNReal ω).toNNReal
  have hvCap : (v : ℝ) = F.rcap (fun r => Wd r ω) (s : ℝ).toNNReal := hClock _ hsn
  have hvPos : 0 < v := NNReal.coe_pos.1 (hvCap ▸ hsCap0)
  have hvq : v ≤ q := NNReal.coe_le_coe.1 (by rw [hvCap, hqtCap]; exact hsCapLt.le)
  have hvV : (v : ℝ≥0∞) < V ω := (ENNReal.coe_le_coe.2 hvq).trans_lt hqV
  have hsExit := (ENNReal.coe_le_coe.2 hsn).trans_lt htExit
  have hsNonneg : 0 ≤ (s : ℝ) := (F.ent (fun r => Wd r ω)).coe_nonneg.trans hsEnt.le
  have hsEntN : F.ent (fun r => Wd r ω) ≤ (s : ℝ).toNNReal :=
    (Real.le_toNNReal_iff_coe_le hsNonneg).2 hsEnt.le
  have hxv : x ∈ Ioo (-rightImg (fun r => -(fun r : ℝ => R r.toNNReal ω) r) 0 v - R v ω)
      (rightImg ((fun r : ℝ => R r.toNNReal ω)) 0 v - R v ω) := by
    simpa only [wpath, ← hvCap, Real.toNNReal_coe] using hx
  have hColv : (componentAmbientChart F.c ((fun r : ℝ => R r.toNNReal ω)) v).2.1 '' (H ∩ ball (x : ℂ) r) ⊆
      ((componentAmbientChart F.c ((fun r : ℝ => R r.toNNReal ω)) q).dom : Set ℂ) := by
    simpa only [wpath, ← hvCap] using hCol
  have hTrv : Tendsto (fun y => (componentAmbientChart F.c ((fun r : ℝ => R r.toNNReal ω)) v).1
      ((componentAmbientChart F.c ((fun r : ℝ => R r.toNNReal ω)) q).2.1 y)) (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ)) := by
    simpa only [wpath, ← hvCap] using hTr
  obtain ⟨hOwnCol, hOwnTr⟩ := own_collar_of_physical_collar hB hRR hRR0 v.coe_nonneg
    (NNReal.coe_le_coe.2 hvq) hColv hTrv
  have hGermLim := hGerm s hsn ξ x r hr (by
      convert hOwnCol using 1 <;>
        simp only [componentLineChart, v, ← hqt] <;> rfl) (by
      convert hOwnTr using 1
      simp only [componentLineChart, v, ← hqt]
      rfl)
  have hOld := hB.loewner hRR hRR0 v.coe_nonneg
  have hCur := hB.loewner hRR hRR0 q.coe_nonneg
  have hdom : ∀ᶠ y in 𝓝[H] (ξ : ℂ),
      (componentAmbientChart F.c ((fun r : ℝ => R r.toNNReal ω)) q).2.1 y ∈
        (componentAmbientChart F.c ((fun r : ℝ => R r.toNNReal ω)) v).dom :=
    eventually_nhdsWithin_of_forall fun y hy =>
      Sec7.PocketStopSide.own_stage_dom_antitone hB hRR hRR0 v.coe_nonneg
        (NNReal.coe_le_coe.2 hvq) (hCur.inv_mem_dom hy)
  have hPhaseOld := hPhase (s : ℝ).toNNReal v hsEntN hsExit hvPos hvV hvCap x hxv
  rw [hd v q] at hPhaseOld
  have hPhaseCur := tendsto_reference_weighted_phase
    (A := fun z => (logDerivFwd (fun r : ℝ => Wd r.toNNReal ω) (s : ℝ).toNNReal z).im)
    (χ := chiC (16 / κ)) (c := 2 * Real.pi * chiC (16 / κ)) (δ := d q ω)
    (cur := componentAmbientChart F.c ((fun r : ℝ => R r.toNNReal ω)) q)
    (old := componentAmbientChart F.c ((fun r : ℝ => R r.toNNReal ω)) v) hOld hdom hTrv
    (by simpa only [wpath, ← hvCap] using hLift) hPhaseOld
  have hf : ∀ᶠ y in 𝓝[H] (ξ : ℂ),
      fwdMapInv ((fun r : ℝ => R r.toNNReal ω)) q y ∈ H \ CLoc.chartSet F.c (A (s : ℝ).toNNReal ω) := by
    refine eventually_nhdsWithin_of_forall fun y hy => ?_
    rw [← hSet s hsn, hShape s hsn]
    have hDo : ((Chart.id.loewner (fun r : ℝ => R r.toNNReal ω) q).dom : Set ℂ) =
        H \ fwdHull (fun r : ℝ => R r.toNNReal ω) q := by
      rw [(Chart.isConformal_id.loewner hRR hRR0 q.coe_nonneg).coe_dom]
      exact QuantumZipper.RS.image_fwdMapInv_H hRR hRR0 q.coe_nonneg
    have hyq : fwdMapInv (fun r : ℝ => R r.toNNReal ω) q y ∈
        H \ fwdHull (fun r : ℝ => R r.toNNReal ω) q := by
      rw [← hDo]
      exact (Chart.isConformal_id.loewner hRR hRR0 q.coe_nonneg).inv_mem_dom hy
    exact ⟨hyq.1, fun h => hyq.2 (QuantumZipper.fwdHull_mono.1
      (NNReal.coe_le_coe.2 hvq) h)⟩
  have hRefLim := tendsto_correctedMean_component_of_phased_ambient
    (Wrel := fun r : ℝ => R r.toNNReal ω) (Wamb := fun r : ℝ => Wd r.toNNReal ω)
    (q := (q : ℝ)) (t := ((s : ℝ).toNNReal : ℝ))
    (f := fwdMapInv (fun r : ℝ => R r.toNNReal ω) q)
    (h := if ξ < 0 then -(Real.pi / Real.sqrt (16 / κ)) else Real.pi / Real.sqrt (16 / κ))
    (δ := d q ω) hκ
    hF.2.2.2.1 hCo hCH (hAo _) (hMh s) hu hf hHeight hPhaseCur
  dsimp only at hRefLim
  rw [← hMean s hsn, ← hSet s hsn] at hRefLim
  have hWord := component_phaseData_exposed (16 / κ) c₀ X R V hRc hR0 q (d q ω) hSeed
  have hTarget : componentLinePhaseData (16 / κ) c₀ F X Wd GT R V d t ω ξ =
      (if ξ < 0 then -(Real.pi / Real.sqrt (16 / κ)) else Real.pi / Real.sqrt (16 / κ)) + d q ω := by
    simpa only [componentLinePhaseData, ← hqt] using hWord
  rw [hTarget]
  have hLim := hGermLim.add hRefLim
  simp only [zero_add] at hLim
  refine hLim.congr' (eventually_nhdsWithin_of_forall fun y _ => ?_)
  simp only [componentLineChart, ← hqt]
  dsimp only [Chart.loewner, Chart.id]
  unfold MartChar.wpath
  ring

end InteractingSLE.Theorem14.GW4Fix
