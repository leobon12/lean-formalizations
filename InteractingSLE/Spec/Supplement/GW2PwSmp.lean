/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2PsmSampId
import InteractingSLE.Spec.Supplement.GW2PwData
import InteractingSLE.Spec.Supplement.GW2PwWinS
import InteractingSLE.Spec.Supplement.GW2RdTop

/-!
# D46's export at one sample (root `0`)

Packet PROVE-GW2-STAGEMEAN, R122 round (D46, D49). At one sample of the actual schedule (root `0`):

* **`sample_geom0_root0`**: the stage-start dilation `λ` (`GW2Omx.sample_kernel_dilation` at a stage time below the
  cap) with the stage chart's domain `ℍ ∖ B 0`, inside the launch chart's domain and sent off the retained hull;
* **`sample_export_root0`**: the per-sample content of D46's export: the counterflow's time `t₀` with `ℓ t₀ = s`, an
  interior tip `γ t₀`, `λ > 0`, the data identity `β.fn y = (gw2Word κ θ cw (gb6Rec t₀ Wk ζk)).fn (λ y)` off a finite
  set (`stage_data_word` from the kernel's stage-start form and Claim(k) at the sample), and the window clause
  (`sample_window_root0`) for every stage time below the cap.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull logDerivFwd chiC)
open SupercriticalConformalCovariance.GM24 (smoothDist)

namespace InteractingSLE.Theorem14.GW2Pw

open GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2TipSystem.Swc GW2Schedule GW2Tip Exist Exist.Staged
  Exist.StagedLaw Sec5.Prop513Schedule GW2Omx Supp8.GB6LMean MartChar.RealFlow Restart Supp8.Q3Chain GW2Fb
  GW2JointKernel Restart.MarkovChart Sec5.CrossCond.StagedRepLater Supp8.Q3Stop GW2Psm
open Supp8.GB6 (relMap gb6Rec relClock sphereInv firstContactTime)
open Supp8.Q3Rel (invHull relLog)

/-- **The stage-start geometry at one sample, from a stage time below the cap** (root `0`). -/
theorem sample_geom0_root0 {Ω : Type*} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (hr0 : rootPt r.1 = 0)
    (hord : (historyProgram c r l).Pairwise (fun p q => p.2 < q.2)) (ω : Ω) (hold : oldSuccess c r l ω)
    (hgood : ∀ (j : ℕ) (hj : j < (futureProgram c r l a).length), LocalExt.IsDrvGood
      (recHist (programRecords c (rootPt r.1) (futureProgram c r l a) ω ⟨j, hj⟩)))
    {cL : Chart} {θ : ℝ} (hl : GW2Olm.curLaunch c r l a ω = some (cL, θ))
    (hc : ∀ j < GW2Olm.curIdx c r l + 1, Continuous (stopDrv (specDelta (GW2Olm.futSpec c r l a) j)
        (GW2Olm.futFam c r l a j ω)) ∧ stopDrv (specDelta (GW2Olm.futSpec c r l a) j) (GW2Olm.futFam c r l a j ω) 0 = 0)
    (hconf : cL.IsConformal) (hext : GW1P.HasProperBdryExt cL)
    {Wk : ℝ≥0 → ℝ} {γk : ℝ≥0 → ℂ} (hWk : Continuous Wk) (hWk0 : Wk 0 = 0) (hγk : IsGeneratingTrace Wk ⊤ γk)
    {γ' : ℝ≥0 → ℂ} (hW' : Continuous fun u => c.W u ω) (hW'0 : c.W 0 ω = 0)
    (hγ' : IsGeneratingTrace (fun u => c.W u ω) ⊤ γ') (hsζ : (c.s : ℝ≥0∞) < c.ζ ω) {ηe : ℝ≥0 → ℂ}
    (hηe : IsGeneratingTrace (fun u => GW2Rd.schedW c r l a u ω) ⊤ ηe)
    (hce : Continuous fun u => GW2Rd.schedW c r l a u ω) (h0e : GW2Rd.schedW c r l a 0 ω = 0)
    {ℓ : ℝ≥0 → ℝ≥0} (hℓc : Continuous ℓ) (hℓm : StrictMono ℓ)
    (hℓr : range ℓ = {q : ℝ≥0 | (q : ℝ≥0∞) < firstTipTime infinitySourceChart (fun u => c.W u ω)
      (ηe '' Icc 0 (historyTime c r l))})
    (hiff : ∀ (q : ℝ≥0) (z : ℂ), (cL.trans infinitySourceChart).tipAt Wk q z ↔
      infinitySourceChart.tipAt (fun u => c.W u ω) (ℓ q) z) {t₀ : ℝ≥0} (ht₀ : ℓ t₀ = c.s)
    {R : ℝ≥0 → ℝ} (hR : Continuous R) (hR0 : R 0 = 0) {A : ℝ≥0 → ℝ≥0} {a₀ : ℝ≥0} (hA0 : A 0 = a₀)
    (hAm : Monotone A) (hAc : Continuous A) {V : ℝ≥0∞} {τ : ℝ≥0} (hτ : V ≤ (A τ : ℝ≥0∞))
    (hSV : (a₀ : ℝ≥0∞) < V)
    (hstop : ∀ u : ℝ≥0, (A u : ℝ≥0∞) < V →
      u < candidateCap c r a ∧ (u : ℝ≥0∞) < (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).2)
    (hshape : ∀ u : ℝ≥0, (A u : ℝ≥0∞) < V → H \ GW2Sdi.schedUnionS c r l a u ω =
      (Supp8.RelSafeS.relChart (gb6Rec c.s c.W c.ζ ω)).2.1 '' (H \ fwdHull (Ito.rpath R) (A u))) :
    ∃ lam : ℝ, 0 < lam ∧
      (∀ x ∈ ((GW2Rd.stgChart (Supp8.RelSafeS.relChart (gb6Rec c.s c.W c.ζ ω)) R a₀).dom : Set ℂ),
        relMap (fun q : ℝ => Wk q.toNNReal) (t₀ : ℝ) (cL.1 x) =
          (lam : ℂ) * (GW2Rd.stgChart (Supp8.RelSafeS.relChart (gb6Rec c.s c.W c.ζ ω)) R a₀).1 x) ∧
      ((GW2Rd.stgChart (Supp8.RelSafeS.relChart (gb6Rec c.s c.W c.ζ ω)) R a₀).dom : Set ℂ) =
        H \ GW2Sdi.schedUnionS c r l a 0 ω ∧
      ((GW2Rd.stgChart (Supp8.RelSafeS.relChart (gb6Rec c.s c.W c.ζ ω)) R a₀).dom : Set ℂ) ⊆ cL.dom ∧
      (∀ y ∈ ((GW2Rd.stgChart (Supp8.RelSafeS.relChart (gb6Rec c.s c.W c.ζ ω)) R a₀).dom : Set ℂ),
        cL.1 y ∈ H \ invHull (fun q : ℝ => Wk q.toNNReal) t₀) := by
  classical
  set rec := gb6Rec c.s c.W c.ζ ω with hrec
  set c₀ := Supp8.RelSafeS.relChart rec with hc₀def
  set cs := GW2Rd.stgChart c₀ R a₀ with hcsdef
  set Uk : ℝ → ℝ := fun q : ℝ => Wk q.toNNReal with hUk
  have hc₀ : c₀.IsConformal := Supp8.RelSafeS.isConformal_relChart rec
  have hcs : cs.IsConformal := GW2Rd.isConformal_stgChart hc₀ hR hR0 a₀
  have hℓ0 : ℓ 0 = 0 := GW2Sgk.clock_zero_of_range hℓm hℓr
  -- a stage time below the cap
  have hVtop : V ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hτ
  set Vr : ℝ≥0 := V.toNNReal with hVrdef
  have hVr : (Vr : ℝ≥0∞) = V := ENNReal.coe_toNNReal hVtop
  have hSV' : a₀ < Vr := by rw [← ENNReal.coe_lt_coe, hVr]; exact hSV
  have hVrτ : Vr ≤ A τ := by rw [← ENNReal.coe_le_coe, hVr]; exact hτ
  set m : ℝ≥0 := (a₀ + Vr) / 2 with hm
  have hma : a₀ < m := by
    rw [hm, lt_div_iff₀ (by norm_num : (0 : ℝ≥0) < 2)]
    calc a₀ * 2 = a₀ + a₀ := by ring
      _ < a₀ + Vr := by gcongr
  have hmV : m < Vr := by
    rw [hm, div_lt_iff₀ (by norm_num : (0 : ℝ≥0) < 2)]
    calc a₀ + Vr < Vr + Vr := by gcongr
      _ = Vr * 2 := by ring
  obtain ⟨t, -, ht⟩ := intermediate_value_Icc (zero_le (a := τ)) hAc.continuousOn
    ⟨by rw [hA0]; exact hma.le, hmV.le.trans hVrτ⟩
  have htV : (A t : ℝ≥0∞) < V := by rw [← hVr, ht]; exact ENNReal.coe_lt_coe.2 hmV
  have htpos : 0 < t := by
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with h | h
    · rw [← h, hA0] at ht
      exact absurd hma (by rw [ht]; exact lt_irrefl _)
    · exact h
  obtain ⟨htcap, htζ⟩ := hstop t htV
  have hAa : ∀ v, a₀ ≤ A v := fun v => hA0 ▸ hAm (zero_le (a := v))
  have hshape' : ∀ v ≤ t, H \ GW2Sdi.schedUnionS c r l a v ω =
      (Supp8.RelSafeS.relChart (gb6Rec c.s c.W c.ζ ω)).2.1 '' (H \ fwdHull (Ito.rpath R) (A v)) :=
    fun v hv => hshape v (lt_of_le_of_lt (ENNReal.coe_le_coe.2 (hAm hv)) htV)
  obtain ⟨lam, hlam, hdil⟩ := sample_kernel_dilation c r l a hr0 hord t htpos ω hold hgood hl hc hconf hext htcap htζ
    hWk hWk0 hγk hW' hW'0 hγ' hsζ hηe hce h0e hℓc hℓm hℓr hiff ht₀ hR hR0 hA0 hAa
    ((hAc.tendsto 0).trans (by rw [hA0])) hshape'
  -- the launch domain and the retained hull through `cL`
  obtain ⟨hdomL, hcont⟩ := launch_dom_cont c r l a hr0 hord ω hold hgood hl hc hconf hext hWk hWk0 hγk hW' hW'0
    hγ' hℓc hℓm.monotone hℓ0 hiff
  have hdisjL : ∀ q : ℝ≥0, Disjoint (closure (fwdHull (fun u : ℝ => GW2Rd.schedW c r l a u.toNNReal ω)
      (historyTime c r l : ℝ))) (closure (invHull (fun u : ℝ => c.W u.toNNReal ω) (ℓ q : ℝ))) := by
    intro q
    have hq : ℓ q ∈ range ℓ := ⟨q, rfl⟩
    rw [hℓr] at hq
    exact disjoint_closure_of_lt_firstTipTime c r l a hγ' hW' hW'0 hηe hce h0e hq
  have hc0 : cL.2.1 '' invHull Uk (t₀ : ℝ) = invHull (fun u : ℝ => c.W u.toNNReal ω) c.s := by
    have h := hcont t₀ (hdisjL t₀)
    rw [ht₀] at h
    exact h
  have hRp : Continuous (Ito.rpath R) := hR.comp continuous_real_toNNReal
  have hRp0 : Ito.rpath R 0 = 0 := by simp [Ito.rpath, hR0]
  have hB0 : GW2Sdi.schedUnionS c r l a 0 ω =
      invHull (fun u : ℝ => c.W u.toNNReal ω) c.s ∪ fwdHull (fun u : ℝ => GW2Rd.schedW c r l a u.toNNReal ω)
        (historyTime c r l : ℝ) := by
    rw [GW2Sdi.schedUnionS_eq, Supp8.RelSafeS.invHull_record_eq hW'0 hW'.continuousOn hsζ]
    simp only [hold, ↓reduceIte, add_zero]
    rfl
  have hcsdom : (cs.dom : Set ℂ) = H \ GW2Sdi.schedUnionS c r l a 0 ω := by
    rw [hcs.coe_dom, hshape' 0 zero_le, hA0]
    change (fun w => c₀.2.1 (fwdMapInv (Ito.rpath R) (a₀ : ℝ) w)) '' H = _
    rw [← Set.image_image, QuantumZipper.RS.image_fwdMapInv_H hRp hRp0 a₀.coe_nonneg]
  have hsubL : (cs.dom : Set ℂ) ⊆ cL.dom := by
    rw [hcsdom, hB0, hdomL]
    exact fun z hz => ⟨hz.1, fun h => hz.2 (Or.inr h)⟩
  have hmaps : ∀ y ∈ (cs.dom : Set ℂ), cL.1 y ∈ H \ invHull Uk t₀ := by
    intro y hy
    have hyL := hsubL hy
    refine ⟨hconf.fwd_mem hyL, fun hmem => ?_⟩
    rw [hcsdom, hB0] at hy
    apply hy.2
    left
    rw [← hc0]
    exact ⟨cL.1 y, hmem, hconf.inv_fwd hyL⟩
  exact ⟨lam, hlam, hdil, hcsdom, hsubL, hmaps⟩

/-- **D46's export at one sample** (root `0`): the counterflow's time `t₀`, an interior tip, the dilation, the
stage-start data identity off a finite set and the window clause below the cap. -/
theorem sample_export_root0 {Ω : Type*} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (hr0 : rootPt r.1 = 0)
    (hord : (historyProgram c r l).Pairwise (fun p q => p.2 < q.2)) (hs0 : 0 < c.s) (ω : Ω)
    (hold : oldSuccess c r l ω)
    (hgood : ∀ (j : ℕ) (hj : j < (futureProgram c r l a).length), LocalExt.IsDrvGood
      (recHist (programRecords c (rootPt r.1) (futureProgram c r l a) ω ⟨j, hj⟩)))
    {cL : Chart} {θ : ℝ} (hl : GW2Olm.curLaunch c r l a ω = some (cL, θ))
    (hc : ∀ j < GW2Olm.curIdx c r l + 1, Continuous (stopDrv (specDelta (GW2Olm.futSpec c r l a) j)
        (GW2Olm.futFam c r l a j ω)) ∧ stopDrv (specDelta (GW2Olm.futSpec c r l a) j) (GW2Olm.futFam c r l a j ω) 0 = 0)
    (hcL : IsDomainChart (cL.dom : Set ℂ) cL) (hext : GW1P.HasProperBdryExt cL)
    (hreg : IsRegularDriver (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω)) {α : ℝ≥0 → ℂ}
    (hα : IsGeneratingTrace (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).1
      (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).2 α)
    {Wk : ℝ≥0 → Ω → ℝ} {ζk : Ω → ℝ≥0∞} {γ : Ω → ℝ≥0 → ℂ} (hWk : Continuous fun q => Wk q ω) (hWk0 : Wk 0 ω = 0)
    (hζk : ζk ω = ⊤) (hγ : IsGeneratingTrace (fun q => Wk q ω) ⊤ (γ ω)) (hγ0 : ∀ q : ℝ≥0, 0 < q → γ ω q ≠ 0)
    (hW' : Continuous fun u => c.W u ω) (hW'0 : c.W 0 ω = 0) (hcα : IsGeneratingTrace (fun u => c.W u ω) ⊤ (c.α ω))
    (hcα0 : ∀ v : ℝ≥0, 0 < v → c.α ω v ≠ 0) (hsζ : (c.s : ℝ≥0∞) < c.ζ ω) (hαs : c.α ω c.s ∈ H)
    (hηe : IsGeneratingTrace (fun u => GW2Rd.schedW c r l a u ω) ⊤ (GW2Rd.schedTr c r l a ω))
    (hce : Continuous fun u => GW2Rd.schedW c r l a u ω) (h0e : GW2Rd.schedW c r l a 0 ω = 0)
    {ℓ : Ω → ℝ≥0 → ℝ≥0} (hℓc : Continuous (ℓ ω)) (hℓm : StrictMono (ℓ ω))
    (hℓr : range (ℓ ω) = {q : ℝ≥0 | (q : ℝ≥0∞) < firstTipTime infinitySourceChart (fun u => c.W u ω)
      (GW2Rd.schedTr c r l a ω '' Icc 0 (historyTime c r l))})
    (hiff : ∀ (q : ℝ≥0) (z : ℂ), (cL.trans infinitySourceChart).tipAt (fun q => Wk q ω) q z ↔
      infinitySourceChart.tipAt (fun u => c.W u ω) (ℓ ω q) z)
    {b' : ℝ → ℝ} {J' : Finset ℝ} (hb' : IsPiecewiseConstantBoundaryData b' J') {u' uθ : ℂ → ℝ}
    (hu' : IsBoundedHarmonicExtension b' J' u')
    (huθ : IsBoundedHarmonicExtension (forceBoundaryData c.κ (flowLineRhoL c.κ b' J' 0 θ)
      (flowLineRhoR c.κ b' J' 0 θ) (flowLineXL b' J' 0) (flowLineXR b' J' 0))
      (forceJumpSet (flowLineXL b' J' 0) (flowLineXR b' J' 0)) uθ)
    (c' : BoundaryWord) {wP₀ u₀ : ℂ → ℝ} (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H) {σa : ℝ}
    {g0 : DistOn upperHalfPlaneOpens}
    (hwP₀ : InnerProductSpace.HarmonicOnNhd wP₀ (H \ GW2Sdi.schedUnionS c r l a 0 ω))
    (hgP₀ : ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ GW2Sdi.schedUnionS c r l a 0 ω →
      g0 φ = ∫ z, wP₀ z * φ z)
    (hmain0 : ∀ t₀ : ℝ≥0, ℓ ω t₀ = c.s → (0 : ℝ≥0∞) < (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).2 →
      ∀ w : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w (H \ GW2Olm.launchUnion c r l a cL 0 ω) →
        (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ GW2Olm.launchUnion c r l a cL 0 ω →
          (Chart.chartTransport hcL.isConformal 1 0 (chiC c.κ) (g0 + smoothDist upperHalfPlaneOpens u₀) -
            smoothDist upperHalfPlaneOpens u') φ = ∫ z, w z * φ z) →
        RetFormAt c.κ θ c' Wk ζk uθ ω t₀ w (H \ GW2Olm.launchUnion c r l a cL 0 ω))
    {w : WordType} {β : BoundaryWord} (hw : wordType c.κ β = w) {U₀ : ℂ → ℝ}
    (hU₀ : IsBoundedHarmonicExtension (forceBoundaryData c.κ (typedRhoL w) (typedRhoR w) (typedXL c.κ w β)
      (typedXR c.κ w β)) (forceJumpSet (typedXL c.κ w β) (typedXR c.κ w β)) U₀)
    {R : ℝ≥0 → ℝ} (hR : Continuous R) (hR0 : R 0 = 0) {A : ℝ≥0 → ℝ≥0} {a₀ : ℝ≥0} (hA0 : A 0 = a₀)
    (hAm : Monotone A) (hAc : Continuous A) {V : ℝ≥0∞} {τ : ℝ≥0} (hτ : V ≤ (A τ : ℝ≥0∞))
    (hSV : (a₀ : ℝ≥0∞) < V)
    (hstop : ∀ u : ℝ≥0, (A u : ℝ≥0∞) < V →
      u < candidateCap c r a ∧ (u : ℝ≥0∞) < (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).2)
    (hshape : ∀ u : ℝ≥0, (A u : ℝ≥0∞) < V → H \ GW2Sdi.schedUnionS c r l a u ω =
      (Supp8.RelSafeS.relChart (gb6Rec c.s c.W c.ζ ω)).2.1 '' (H \ fwdHull (Ito.rpath R) (A u)))
    (hnc : ∀ u : ℝ≥0, (A u : ℝ≥0∞) < V →
      ∀ v ∈ Icc 0 c.s, ∀ u' ≤ historyTime c r l + u, c.α ω v * GW2Rd.schedTr c r l a ω u' + 1 ≠ 0)
    (hinst0 : ∀ y ∈ ((GW2Rd.stgChart (Supp8.RelSafeS.relChart (gb6Rec c.s c.W c.ζ ω)) R a₀).dom : Set ℂ),
      wP₀ y + u₀ y + σa + chiC c.κ * (GW2Rd.stgChart (Supp8.RelSafeS.relChart (gb6Rec c.s c.W c.ζ ω)) R a₀).2.2 y =
        U₀ ((GW2Rd.stgChart (Supp8.RelSafeS.relChart (gb6Rec c.s c.W c.ζ ω)) R a₀).1 y))
    {hβ : ℝ} (hfarβ : ∃ B : ℝ, ∀ y, B < y → y ∉ forceJumpSet (typedXL c.κ w β) (typedXR c.κ w β) →
      forceBoundaryData c.κ (typedRhoL w) (typedRhoR w) (typedXL c.κ w β) (typedXR c.κ w β) y = hβ)
    (hfar : sleLambda (16 / c.κ) - Real.pi * chiC c.κ + θ * chiC c.κ = hβ)
    {wr : ℝ≥0 → ℝ≥0 → ℝ} {ηr : ℝ≥0 → ℝ≥0 → ℂ}
    (hregW : ∀ s : ℝ≥0, Continuous (wr s) ∧ wr s 0 = 0 ∧
      (∀ t : ℝ≥0, (t : ℝ≥0∞) < (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).2 →
        wr s t = (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).1 t) ∧
      IsGeneratingTrace (wr s) ⊤ (ηr s) ∧
      ∀ u : ℝ≥0, (u : ℝ≥0∞) ≤ (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).2 → ηr s u = α u) :
    ∃ t₀ : ℝ≥0, ℓ ω t₀ = c.s ∧ γ ω t₀ ∈ H ∧ ∃ lam : ℝ, 0 < lam ∧ ∃ F : Set ℝ, F.Finite ∧
      (∀ y, y ∉ F → β.fn y = (GW2Rd.gw2Word c.κ θ c' (gb6Rec t₀ Wk ζk ω)).fn (lam * y)) ∧
      ∀ u : ℝ≥0, ((a₀ + u : ℝ≥0) : ℝ≥0∞) < V →
        (∃ t : ℝ≥0, (t : ℝ≥0∞) < min (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).2
            (firstContactTime (fun v => (α v : OnePoint ℂ)) ((fun v => sphereInv (γ ω v : OnePoint ℂ)) '' Icc 0 t₀)) ∧
          lam ^ 2 * u < relClock (fun q : ℝ => Wk q.toNNReal ω) t₀
            (fun q : ℝ => (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).1 q.toNNReal) t) ∧
        ∀ t : ℝ≥0, (t : ℝ≥0∞) < firstContactTime (fun v => sphereInv (ηr t₀ v : OnePoint ℂ))
            ((fun v => (γ ω v : OnePoint ℂ)) '' Icc 0 t₀) →
          relClock (fun q : ℝ => Wk q.toNNReal ω) t₀ (fun q : ℝ => wr t₀ q.toNNReal) t ≤ lam ^ 2 * u →
          fwdHull (scD lam (Ito.rpath (GW2Rd.stgDrv R a₀)))
              (relClock (fun q : ℝ => Wk q.toNNReal ω) t₀ (fun q : ℝ => wr t₀ q.toNNReal) t) =
            relMap (fun q : ℝ => Wk q.toNNReal ω) t₀ '' fwdHull (fun q : ℝ => wr t₀ q.toNNReal) t := by
  classical
  have hconf : cL.IsConformal := hcL.isConformal
  have hlc : ContinuousOn cL.2.2 cL.dom := hcL.continuousOn_lift
  have hlh : InnerProductSpace.HarmonicOnNhd cL.2.2 cL.dom := GW2Rd.harmonicOnNhd_lift_of_isDomainChart hcL
  -- the physical no-contact before `T`, and the clock reaching `s`
  have hnc0 : ω ∈ GW2Omx.noContact c r l a := by
    rw [mem_noContact_iff c r l a hcα hW' hW'0 hsζ hηe hce h0e]
    intro v hv u hu
    exact hnc 0 (by rw [hA0]; exact hSV) v hv u (hu.2.trans (le_add_of_nonneg_right zero_le))
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
  -- the interior kernel tip
  obtain ⟨f, -, hf, -⟩ := id hext
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
  -- the stage-start geometry
  obtain ⟨lam, hlam, hdil, hcsdom, hsubL, hmaps⟩ := sample_geom0_root0 c r l a hr0 hord ω hold hgood hl hc hconf
    hext hWk hWk0 hγ hW' hW'0 hcα hsζ hηe hce h0e hℓc hℓm hℓr hiff ht₀ hR hR0 hA0 hAm hAc hτ hSV hstop hshape
  -- the kernel's stage-start form, read in the stage chart
  have hcomp0 : H \ GW2Olm.launchUnion c r l a cL 0 ω = chartPre cL (H \ GW2Sdi.schedUnionS c r l a 0 ω) := by
    change H \ cL.1 '' (GW2Sdi.schedUnionS c r l a 0 ω ∩ (cL.dom : Set ℂ)) = _
    rw [GW2Rd.launchUnion_eq hconf, sdiff_sdiff_cancel_left (chartPre_subset_H _ _)]
  obtain ⟨hw₀h, hw₀p⟩ := launch_rep hconf hlc hlh hwP₀ hgP₀ hu₀ hu'.1 (chiC c.κ)
  have hpos0 : (0 : ℝ≥0∞) < (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).2 := by
    have h := (hstop 0 (by rw [hA0]; exact hSV)).2
    exact h
  have hform0 := hmain0 t₀ ht₀ hpos0 _ (by rw [hcomp0]; exact hw₀h) (by rw [hcomp0]; exact hw₀p)
  have hoff : ∀ y ∈ (cL.dom : Set ℂ), y ∉ GW2Sdi.schedUnionS c r l a 0 ω →
      cL.1 y ∉ GW2Olm.launchUnion c r l a cL 0 ω := by
    rintro y hyL hyB ⟨y', ⟨hy'B, hy'L⟩, he⟩
    have : y' = y := by rw [← hcL.inv_fwd hy'L, he, hcL.inv_fwd hyL]
    exact hyB (this ▸ hy'B)
  set K := jointWordOfRec (specOffset c.κ) c.κ c' (cfRec t₀ Wk ζk ω) with hKdef
  set cs := GW2Rd.stgChart (Supp8.RelSafeS.relChart (gb6Rec c.s c.W c.ζ ω)) R a₀ with hcsdef
  have hret : ∀ G₀ : ℂ → ℝ, IsBoundedHarmonicExtension (cfData c.κ K.fn K.jumps) (cfJumps K.fn K.jumps) G₀ →
      ∀ y ∈ (cs.dom : Set ℂ), wP₀ y + u₀ y + chiC c.κ * cL.2.2 y - u' (cL.1 y) + (uθ (cL.1 y) - θ * chiC c.κ) =
        G₀ (relMap (fun q : ℝ => Wk q.toNNReal ω) t₀ (cL.1 y)) -
          chiC c.κ * (relLog (fun q : ℝ => Wk q.toNNReal ω) t₀ (cL.1 y)).im := by
    intro G₀ hG₀ y hy
    have hyL := hsubL hy
    have hyB : y ∉ GW2Sdi.schedUnionS c r l a 0 ω := by
      rw [hcsdom] at hy
      exact hy.2
    have h := hform0 G₀ hG₀ ⟨(hmaps y hy).1, hoff y hyL hyB⟩
    simp only [hcL.inv_fwd hyL] at h
    exact h
  have hcsD := isDomainChart_stgChart_relChart (gb6Rec c.s c.W c.ζ ω) hR hR0 a₀
  have huθ' := sub_eq_of_bhe_angle c.hκ hb' hu' huθ
  have hUkc : Continuous fun q : ℝ => Wk q.toNNReal ω := hWk.comp continuous_real_toNNReal
  have hUk0 : (fun q : ℝ => Wk q.toNNReal ω) 0 = 0 := by simp [hWk0]
  obtain ⟨F, hF, hdata⟩ := stage_data_word c.hκ hcL hcsD hsubL hUkc hUk0 t₀.coe_nonneg hmaps hlam hdil huθ' K hret
    hw hU₀ hinst0 hfarK hfarβ hfar
  obtain ⟨hwr, hwr0, hwrW, hηr, hηrα⟩ := hregW t₀
  refine ⟨t₀, ht₀, hγt₀, lam, hlam, F, hF, fun y hy => hdata y hy, fun u hu => ?_⟩
  exact sample_window_root0 c r l a hr0 hord hs0 ω hold hgood hl hc hconf hext hreg hα hWk hWk0 hγ hγ0 hW' hW'0
    hcα hcα0 hsζ hηe hce h0e hℓc hℓm hℓr hiff ht₀ hγt₀ hwr hwr0 hwrW hηr hηrα hR hR0 hA0 hAm hAc hτ hstop hshape
    hnc hlam hdil u hu

end InteractingSLE.Theorem14.GW2Pw
