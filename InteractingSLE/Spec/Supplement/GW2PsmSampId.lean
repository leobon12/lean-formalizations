/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2PsmIdent
import InteractingSLE.Spec.Supplement.GW2PsmTraceS
import InteractingSLE.Spec.Supplement.GW2PsmLive
import InteractingSLE.Spec.Supplement.GW2OmxPhys
import InteractingSLE.Spec.Supplement.GW2OmxGeo
import InteractingSLE.Spec.Supplement.GW2TjGeo
import InteractingSLE.Spec.Supplement.GW2WmFar
import InteractingSLE.Spec.Supplement.GB6RestartProof

/-!
# GW2's open lines: the stage reading of the instance's mean at one sample (root `0`), from the launch forms

Packet PROVE-GW2-STAGEMEAN, R121 round (deterministic, one sample). The launch forms of `GW2Omx.ae_launch_form_pair`
evaluated at one sample, together with the sample's physical facts (no physical contact before `T + t`, an interior
counterflow tip at `s`), the instance's stage shape and its stage-start identity:

* **`sample_identity_root0`**: the harmonic representative `wP` of the instance's mean at `t`, read in the stage chart
  off the stage hull, is the canonical coupling mean. The premises of the launch forms are derived here: the clock
  reaches `s` (no contact with the explored set), the conditional counterflow's tip is interior
  (`trace_mem_H_of_tipAt`), no contact in the launch frame (`lt_firstContactTime_launch` with
  `sample_trace_corr`), and the kernel word's far-right height (`GW2Wm.farR_jointWordOfRec` with `gb6_rec_spec`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull logDerivFwd chiC)
open SupercriticalConformalCovariance.GM24 (smoothDist)

namespace InteractingSLE.Theorem14.GW2Psm

open GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2TipSystem.Swc GW2Schedule GW2Tip Exist Exist.Staged
  Exist.StagedLaw Sec5.Prop513Schedule GW2Omx Supp8.GB6LMean MartChar.RealFlow Restart Supp8.Q3Chain GW2Fb
  GW2JointKernel Restart.MarkovChart
open Supp8.GB6 (relMap gb6Rec relClock sphereInv firstContactTime)
open Supp8.Q3Rel (invHull relLog)

/-- **The stage reading of the instance's mean at one sample** (root `0`). -/
theorem sample_identity_root0 {Ω : Type*} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (hr0 : rootPt r.1 = 0)
    (hord : (historyProgram c r l).Pairwise (fun p q => p.2 < q.2)) (t : ℝ≥0) (htpos : 0 < t) (ω : Ω)
    (hold : oldSuccess c r l ω)
    (hgood : ∀ (j : ℕ) (hj : j < (futureProgram c r l a).length), LocalExt.IsDrvGood
      (recHist (programRecords c (rootPt r.1) (futureProgram c r l a) ω ⟨j, hj⟩)))
    {cL : Chart} {θ : ℝ} (hl : GW2Olm.curLaunch c r l a ω = some (cL, θ))
    (hc : ∀ j < GW2Olm.curIdx c r l + 1, Continuous (stopDrv (specDelta (GW2Olm.futSpec c r l a) j)
        (GW2Olm.futFam c r l a j ω)) ∧ stopDrv (specDelta (GW2Olm.futSpec c r l a) j) (GW2Olm.futFam c r l a j ω) 0 = 0)
    (hcL : IsDomainChart (cL.dom : Set ℂ) cL) (hext : GW1P.HasProperBdryExt cL) (htcap : t < candidateCap c r a)
    (htζ : (t : ℝ≥0∞) < (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).2)
    (hreg : IsRegularDriver (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω)) {α : ℝ≥0 → ℂ}
    (hα : IsGeneratingTrace (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).1
      (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).2 α)
    {Wk : ℝ≥0 → Ω → ℝ} {ζk : Ω → ℝ≥0∞} {γ : Ω → ℝ≥0 → ℂ} (hWk : Continuous fun q => Wk q ω) (hWk0 : Wk 0 ω = 0)
    (hζk : ζk ω = ⊤) (hγ : IsGeneratingTrace (fun q => Wk q ω) ⊤ (γ ω)) (hγ0 : ∀ q : ℝ≥0, 0 < q → γ ω q ≠ 0)
    (hW' : Continuous fun u => c.W u ω) (hW'0 : c.W 0 ω = 0) (hcα : IsGeneratingTrace (fun u => c.W u ω) ⊤ (c.α ω))
    (hcα0 : ∀ v : ℝ≥0, 0 < v → c.α ω v ≠ 0) (hsζ : (c.s : ℝ≥0∞) < c.ζ ω) (hs0 : 0 < c.s) (hαs : c.α ω c.s ∈ H)
    (hηe : IsGeneratingTrace (fun u => GW2Rd.schedW c r l a u ω) ⊤ (GW2Rd.schedTr c r l a ω))
    (hce : Continuous fun u => GW2Rd.schedW c r l a u ω) (h0e : GW2Rd.schedW c r l a 0 ω = 0)
    {ℓ : Ω → ℝ≥0 → ℝ≥0} (hℓc : Continuous (ℓ ω)) (hℓm : StrictMono (ℓ ω))
    (hℓr : range (ℓ ω) = {q : ℝ≥0 | (q : ℝ≥0∞) < firstTipTime infinitySourceChart (fun u => c.W u ω)
      (GW2Rd.schedTr c r l a ω '' Icc 0 (historyTime c r l))})
    (hiff : ∀ (q : ℝ≥0) (z : ℂ), (cL.trans infinitySourceChart).tipAt (fun q => Wk q ω) q z ↔
      infinitySourceChart.tipAt (fun u => c.W u ω) (ℓ ω q) z)
    (hnc : ∀ v ∈ Icc 0 c.s, ∀ u ≤ historyTime c r l + t, c.α ω v * GW2Rd.schedTr c r l a ω u + 1 ≠ 0)
    {R : ℝ≥0 → ℝ} (hR : Continuous R) (hR0 : R 0 = 0) {A : ℝ≥0 → ℝ≥0} {a₀ : ℝ≥0} (hA0 : A 0 = a₀)
    (hAa : ∀ u, a₀ ≤ A u) (hAc : Continuous A)
    (hshape : ∀ u ≤ t, H \ GW2Sdi.schedUnionS c r l a u ω =
      (Supp8.RelSafeS.relChart (gb6Rec c.s c.W c.ζ ω)).2.1 '' (H \ fwdHull (Ito.rpath R) (A u)))
    {b' : ℝ → ℝ} {J' : Finset ℝ} (hb' : IsPiecewiseConstantBoundaryData b' J') {u' uθ : ℂ → ℝ}
    (hu' : IsBoundedHarmonicExtension b' J' u')
    (huθ : IsBoundedHarmonicExtension (forceBoundaryData c.κ (flowLineRhoL c.κ b' J' 0 θ)
      (flowLineRhoR c.κ b' J' 0 θ) (flowLineXL b' J' 0) (flowLineXR b' J' 0))
      (forceJumpSet (flowLineXL b' J' 0) (flowLineXR b' J' 0)) uθ)
    (c' : BoundaryWord) {wP wP₀ u₀ : ℂ → ℝ} (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H) {σa : ℝ}
    {gt g0 : DistOn upperHalfPlaneOpens}
    (hwP : InnerProductSpace.HarmonicOnNhd wP (H \ GW2Sdi.schedUnionS c r l a t ω))
    (hgP : ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ GW2Sdi.schedUnionS c r l a t ω →
      gt φ = ∫ z, wP z * φ z)
    (hwP₀ : InnerProductSpace.HarmonicOnNhd wP₀ (H \ GW2Sdi.schedUnionS c r l a 0 ω))
    (hgP₀ : ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ GW2Sdi.schedUnionS c r l a 0 ω →
      g0 φ = ∫ z, wP₀ z * φ z)
    (hmainT : ∀ t₀ : ℝ≥0, ℓ ω t₀ = c.s →
      (t : ℝ≥0∞) < (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).2 → γ ω t₀ ∈ H → 0 < t →
      ((t : ℝ≥0) : ℝ≥0∞) < firstContactTime (fun u => (α u : OnePoint ℂ))
        ((fun u => sphereInv (γ ω u : OnePoint ℂ)) '' Icc 0 t₀) →
      ∀ w : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w (H \ GW2Olm.launchUnion c r l a cL t ω) →
        (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ GW2Olm.launchUnion c r l a cL t ω →
          (Chart.chartTransport hcL.isConformal 1 0 (chiC c.κ) (gt + smoothDist upperHalfPlaneOpens u₀) -
            smoothDist upperHalfPlaneOpens u') φ = ∫ z, w z * φ z) →
        UnionFormAt c.κ θ b' J' c' Wk ζk (fun t ω => (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).1 t) uθ ω t₀ t w
          (H \ GW2Olm.launchUnion c r l a cL t ω))
    (hmain0 : ∀ t₀ : ℝ≥0, ℓ ω t₀ = c.s → (0 : ℝ≥0∞) < (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).2 →
      ∀ w : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w (H \ GW2Olm.launchUnion c r l a cL 0 ω) →
        (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ GW2Olm.launchUnion c r l a cL 0 ω →
          (Chart.chartTransport hcL.isConformal 1 0 (chiC c.κ) (g0 + smoothDist upperHalfPlaneOpens u₀) -
            smoothDist upperHalfPlaneOpens u') φ = ∫ z, w z * φ z) →
        RetFormAt c.κ θ c' Wk ζk uθ ω t₀ w (H \ GW2Olm.launchUnion c r l a cL 0 ω))
    {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j) {U₀ U : ℂ → ℝ}
    (hU₀ : IsBoundedHarmonicExtension (forceBoundaryData c.κ ρL ρR xL xR) (forceJumpSet xL xR) U₀)
    (hinst0 : ∀ y ∈ ((GW2Rd.stgChart (Supp8.RelSafeS.relChart (gb6Rec c.s c.W c.ζ ω)) R a₀).dom : Set ℂ),
      wP₀ y + u₀ y + σa + chiC c.κ * (GW2Rd.stgChart (Supp8.RelSafeS.relChart (gb6Rec c.s c.W c.ζ ω)) R a₀).2.2 y =
        U₀ ((GW2Rd.stgChart (Supp8.RelSafeS.relChart (gb6Rec c.s c.W c.ζ ω)) R a₀).1 y))
    {hβ : ℝ} (hfarβ : ∃ B : ℝ, ∀ y, B < y → y ∉ forceJumpSet xL xR → forceBoundaryData c.κ ρL ρR xL xR y = hβ)
    (hfar : sleLambda (16 / c.κ) - Real.pi * chiC c.κ + θ * chiC c.κ = hβ)
    (hU : IsBoundedHarmonicExtension
      (forceBoundaryData c.κ ρL ρR
        (fun i => -rightImg (fun s => -Ito.rpath (GW2Rd.stgDrv R a₀) s) (-xL i) ((A t : ℝ) - a₀) -
          Ito.rpath (GW2Rd.stgDrv R a₀) ((A t : ℝ) - a₀))
        (fun j => rightImg (Ito.rpath (GW2Rd.stgDrv R a₀)) (xR j) ((A t : ℝ) - a₀) -
          Ito.rpath (GW2Rd.stgDrv R a₀) ((A t : ℝ) - a₀)))
      (forceJumpSet
        (fun i => -rightImg (fun s => -Ito.rpath (GW2Rd.stgDrv R a₀) s) (-xL i) ((A t : ℝ) - a₀) -
          Ito.rpath (GW2Rd.stgDrv R a₀) ((A t : ℝ) - a₀))
        (fun j => rightImg (Ito.rpath (GW2Rd.stgDrv R a₀)) (xR j) ((A t : ℝ) - a₀) -
          Ito.rpath (GW2Rd.stgDrv R a₀) ((A t : ℝ) - a₀))) U) :
    ∀ z ∈ H \ fwdHull (Ito.rpath (GW2Rd.stgDrv R a₀)) ((A t : ℝ) - a₀),
      wP ((GW2Rd.stgChart (Supp8.RelSafeS.relChart (gb6Rec c.s c.W c.ζ ω)) R a₀).2.1 z) +
          u₀ ((GW2Rd.stgChart (Supp8.RelSafeS.relChart (gb6Rec c.s c.W c.ζ ω)) R a₀).2.1 z) + σa +
          chiC c.κ * (GW2Rd.stgChart (Supp8.RelSafeS.relChart (gb6Rec c.s c.W c.ζ ω)) R a₀).2.2
            ((GW2Rd.stgChart (Supp8.RelSafeS.relChart (gb6Rec c.s c.W c.ζ ω)) R a₀).2.1 z) =
        couplingMean c.κ (Ito.rpath (GW2Rd.stgDrv R a₀)) ((A t : ℝ) - a₀) U z := by
  classical
  have hconf : cL.IsConformal := hcL.isConformal
  have hlc : ContinuousOn cL.2.2 cL.dom := hcL.continuousOn_lift
  have hlh : InnerProductSpace.HarmonicOnNhd cL.2.2 cL.dom := GW2Rd.harmonicOnNhd_lift_of_isDomainChart hcL
  -- the physical no-contact before `T`, and the clock reaching `s`
  have hnc0 : ω ∈ GW2Omx.noContact c r l a := by
    rw [mem_noContact_iff c r l a hcα hW' hW'0 hsζ hηe hce h0e]
    intro v hv u hu
    exact hnc v hv u (hu.2.trans (le_add_of_nonneg_right zero_le))
  have hsr : c.s ∈ range (ℓ ω) := by
    rw [hℓr]
    exact (mem_noContact_iff_lt_firstTipTime c r l a hcα hW' hW'0 hsζ hηe hce h0e).1 hnc0
  obtain ⟨t₀, ht₀⟩ := hsr
  have hℓ0 : ℓ ω 0 = 0 := GW2Sgk.clock_zero_of_range hℓm hℓr
  have ht₀pos : 0 < t₀ := by
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t₀) with h | h
    · rw [← h, hℓ0] at ht₀
      exact absurd ht₀.symm hs0.ne'
    · exact h
  -- the trace correspondence and the launch-frame contact
  obtain ⟨f, hf, htr⟩ := sample_trace_corr c r l a hr0 hord t ω hold hgood hl hc hext htcap htζ hreg hα hηe
  obtain ⟨t', htt', ht'ζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 htζ
  have htt'' : t < t' := by exact_mod_cast htt'
  have hαc : ContinuousOn α (Icc 0 t') := hα.2.1.mono fun u hu => (ENNReal.coe_le_coe.2 hu.2).trans ht'ζ.le
  have hphys : ∀ u ≤ t, ∀ v ≤ c.s, 0 < v →
      GW2Rd.schedTr c r l a ω (historyTime c r l + u) ≠ -(c.α ω v)⁻¹ := by
    intro u hu v hv hv0 heq
    apply hnc v ⟨zero_le, hv⟩ (historyTime c r l + u) (add_le_add le_rfl hu)
    rw [heq]
    field_simp [hcα0 v hv0]
    ring
  have hcontact := lt_firstContactTime_launch hf hWk hWk0 hγ hγ0 hW' hW'0 hcα hcα0 hℓm hℓ0 hiff ht₀ htt'' hαc htr
    hphys
  -- the interior kernel tip
  obtain ⟨hdomL, -⟩ := launch_dom_cont c r l a hr0 hord ω hold hgood hl hc hconf hext hWk hWk0 hγ hW' hW'0 hcα
    hℓc hℓm.monotone hℓ0 hiff
  have hαs0 : c.α ω c.s ≠ 0 := fun h => by
    have : (0 : ℝ) < (c.α ω c.s).im := hαs
    rw [h, Complex.zero_im] at this
    exact lt_irrefl 0 this
  have hαK : c.α ω c.s ∈ fwdHull (fun u : ℝ => c.W u.toNNReal ω) (c.s : ℝ) := by
    by_contra hn
    obtain ⟨⟨z₀, -, hcc⟩, -⟩ := hcα.2.2 c.s ENNReal.coe_lt_top
    have hin : c.α ω c.s ∈ H \ fwdHull (fun u : ℝ => c.W u.toNNReal ω) (c.s : ℝ) := ⟨hαs, hn⟩
    rw [← hcc] at hin
    exact (connectedComponentIn_subset _ _ hin).2 ⟨c.s, ⟨zero_le, le_rfl⟩, rfl⟩
  have hzI : -(c.α ω c.s)⁻¹ ∈ invHull (fun u : ℝ => c.W u.toNNReal ω) (c.s : ℝ) := ⟨_, hαK, rfl⟩
  have hdisj := disjoint_closure_of_mem_noContact c r l a hcα hW' hW'0 hsζ hηe hce h0e hnc0
  have hzH : -(c.α ω c.s)⁻¹ ∈ H := by
    show 0 < (-(c.α ω c.s)⁻¹).im
    have h1 : 0 < (c.α ω c.s).im := hαs
    rw [Complex.neg_im, Complex.inv_im, neg_div, neg_neg]
    exact div_pos h1 (Complex.normSq_pos.2 hαs0)
  have hz : -(c.α ω c.s)⁻¹ ∈ (cL.dom : Set ℂ) := by
    rw [hdomL]
    exact ⟨hzH, fun hK => Set.disjoint_left.1 hdisj (subset_closure hK) (subset_closure hzI)⟩
  have htip : (cL.trans infinitySourceChart).tipAt (fun q => Wk q ω) t₀ (-(c.α ω c.s)⁻¹) := by
    rw [hiff, ht₀]
    exact tipAt_infinitySourceChart_of_trace hW' hW'0 hcα hαs0
  have hγt₀ : γ ω t₀ ∈ H := trace_mem_H_of_tipAt hconf hf hWk hWk0 hγ (hγ0 t₀ ht₀pos) htip hz
  -- the kernel word's far-right height
  have hγ' : IsGeneratingTrace (fun t => Wk t ω) (ζk ω) (γ ω) := by rw [hζk]; exact hγ
  have hWkc' : ContinuousOn (fun t => Wk t ω) {t | (t : ℝ≥0∞) < ζk ω} := hWk.continuousOn
  have hneg := ((Supp8.GB6.gb6_rec_spec t₀ hWk0 hWkc' hγ' (by rw [hζk]; exact ENNReal.coe_lt_top)).2.2.2.2
    hγt₀).2
  have hfarK := GW2Wm.farR_jointWordOfRec c.hκ c' (cfRec t₀ Wk ζk ω) hneg
  -- the launch representatives
  have hcomp : ∀ u : ℝ≥0, H \ GW2Olm.launchUnion c r l a cL u ω = chartPre cL (H \ GW2Sdi.schedUnionS c r l a u ω) :=
    fun u => by
      change H \ cL.1 '' (GW2Sdi.schedUnionS c r l a u ω ∩ (cL.dom : Set ℂ)) = _
      rw [GW2Rd.launchUnion_eq hconf, sdiff_sdiff_cancel_left (chartPre_subset_H _ _)]
  obtain ⟨hw₀h, hw₀p⟩ := launch_rep hconf hlc hlh hwP₀ hgP₀ hu₀ hu'.1 (chiC c.κ)
  obtain ⟨hwh, hwp⟩ := launch_rep hconf hlc hlh hwP hgP hu₀ hu'.1 (chiC c.κ)
  have hpos0 : (0 : ℝ≥0∞) < (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).2 := lt_of_le_of_lt (zero_le) htζ
  have hform0 := hmain0 t₀ ht₀ hpos0 _ (by rw [hcomp 0]; exact hw₀h) (by rw [hcomp 0]; exact hw₀p)
  have hformT := hmainT t₀ ht₀ htζ hγt₀ htpos hcontact _ (by rw [hcomp t]; exact hwh) (by rw [hcomp t]; exact hwp)
  exact sample_stage_read c r l a hr0 hord t htpos ω hold hgood hl hc hcL hext htcap htζ hreg hα hWk hWk0 hγ
    hW' hW'0 hcα hsζ hηe hce h0e hℓc hℓm hℓr hiff ht₀ hcontact hR hR0 hA0 hAa hAc hshape hb' hu' huθ c' hform0
    hformT ρL ρR hxL hxR hU₀ hinst0 hfarK hfarβ hfar hU

end InteractingSLE.Theorem14.GW2Psm
