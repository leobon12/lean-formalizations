/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2PsmGeom
import InteractingSLE.Spec.Supplement.GW2XkDil

/-!
# The stage-start geometry at one sample, at a root `x ≥ 0`

Packet PROVE-GW2-GEOM2, round 14 (D49). STAGEMEAN's `GW2Psm.sample_stage_geom` at a root `x = rootPt r.1 ≥ 0`, with
the root-`x` union `schedUnionX` (the explored hull translated by `x`) and the stage chart on `relChartX x s rec`
(D8's `chartX`). The dilation is round 11's `GW2Xk.sample_kernel_dilationX`, the union identity
`GW2Xk.launch_eq_of_clockX`, the launch domain and continuation `GW2Xk.launch_dom_contX`,
`GW2Xk.launch_cont_of_rangeX`; the driver relation is STAGEMEAN's chart-general `GW2Omx.sample_driver_scale`.

* **`sample_stage_geomX`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdMap fwdMapInv fwdHull)

namespace InteractingSLE.Theorem14.GW2Kx

open GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2TipSystem.Swc GW2Schedule GW2Tip Exist Exist.Staged
  Exist.StagedLaw Sec5.Prop513Schedule GW2Omx Supp8.GB6LMean GW2Xk
open Supp8.GB6 (relMap gb6Rec relClock)
open Supp8.Q3Rel (invHull)

/-- **The stage-start geometry at one sample** (root `x ≥ 0`). -/
theorem sample_stage_geomX {Ω : Type*} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (hx0 : 0 ≤ rootPt r.1)
    (hord : (historyProgram c r l).Pairwise (fun p q => p.2 < q.2)) (t : ℝ≥0) (htpos : 0 < t) (ω : Ω)
    (hold : oldSuccess c r l ω)
    (hgood : ∀ (j : ℕ) (hj : j < (futureProgram c r l a).length), LocalExt.IsDrvGood
      (recHist (programRecords c (rootPt r.1) (futureProgram c r l a) ω ⟨j, hj⟩)))
    {cL : Chart} {θ : ℝ} (hl : GW2Olm.curLaunch c r l a ω = some (cL, θ))
    (hc : ∀ j < GW2Olm.curIdx c r l + 1, Continuous (stopDrv (specDelta (GW2Olm.futSpec c r l a) j)
        (GW2Olm.futFam c r l a j ω)) ∧ stopDrv (specDelta (GW2Olm.futSpec c r l a) j) (GW2Olm.futFam c r l a j ω) 0 = 0)
    (hconf : cL.IsConformal) (hext : GW1P.HasProperBdryExt cL) (htcap : t < candidateCap c r a)
    (htζ : (t : ℝ≥0∞) < (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).2)
    {Wk : ℝ≥0 → ℝ} {γk : ℝ≥0 → ℂ} (hWk : Continuous Wk) (hWk0 : Wk 0 = 0) (hγk : IsGeneratingTrace Wk ⊤ γk)
    {γ' : ℝ≥0 → ℂ} (hW' : Continuous fun u => c.W u ω) (hW'0 : c.W 0 ω = 0)
    (hγ' : IsGeneratingTrace (fun u => c.W u ω) ⊤ γ') (hsζ : (c.s : ℝ≥0∞) < c.ζ ω) {ηe : ℝ≥0 → ℂ}
    (hηe : IsGeneratingTrace (fun u => GW2Rd.schedW c r l a u ω) ⊤ ηe)
    (hce : Continuous fun u => GW2Rd.schedW c r l a u ω) (h0e : GW2Rd.schedW c r l a 0 ω = 0)
    {ℓ : ℝ≥0 → ℝ≥0} (hℓc : Continuous ℓ) (hℓm : StrictMono ℓ)
    (hℓr : range ℓ = {q : ℝ≥0 | (q : ℝ≥0∞) < firstTipTime infinitySourceChart (fun u => c.W u ω)
      ((fun z : ℂ => (rootPt r.1 : ℂ) + z) '' (ηe '' Icc 0 (historyTime c r l)))})
    (hvis : 0 < rootPt r.1 → ∃ τ, (rootPt r.1 : ℂ) * γ' τ + 1 = 0)
    (hiff : ∀ (q : ℝ≥0) (z : ℂ), (cL.trans infinitySourceChart).tipAt Wk q z ↔
      infinitySourceChart.tipAt (fun u => c.W u ω) (ℓ q) z) {t₀ : ℝ≥0} (ht₀ : ℓ t₀ = c.s)
    {R : ℝ≥0 → ℝ} (hR : Continuous R) (hR0 : R 0 = 0) {A : ℝ≥0 → ℝ≥0} {a₀ : ℝ≥0} (hA0 : A 0 = a₀)
    (hAa : ∀ u, a₀ ≤ A u) (hAc : Continuous A)
    (hshape : ∀ u ≤ t, H \ GW2Rd.schedUnionX c r l a (historyTime c r l) u ω =
      (GW2Rz.relChartX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω)).2.1 '' (H \ fwdHull (Ito.rpath R) (A u)))
    {Rk : ℝ → ℝ} (hRk : Continuous Rk) (hRk0 : Rk 0 = 0)
    (hhull : HullsUpTo (fun q : ℝ => Wk q.toNNReal) t₀
      (fun q : ℝ => (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).1 q.toNNReal) Rk t)
    (hdisj : ∀ u : ℝ≥0, u ≤ t → fwdHull (fun q : ℝ => (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).1 q.toNNReal)
      u ⊆ H \ invHull (fun q : ℝ => Wk q.toNNReal) t₀) :
    ∃ lam : ℝ, 0 < lam ∧
      (∀ x ∈ ((GW2Rd.stgChart (GW2Rz.relChartX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω)) R a₀).dom : Set ℂ),
        relMap (fun q : ℝ => Wk q.toNNReal) (t₀ : ℝ) (cL.1 x) =
          (lam : ℂ) * (GW2Rd.stgChart (GW2Rz.relChartX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω)) R a₀).1 x) ∧
      ((GW2Rd.stgChart (GW2Rz.relChartX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω)) R a₀).dom : Set ℂ) =
        H \ GW2Rd.schedUnionX c r l a (historyTime c r l) 0 ω ∧
      ((GW2Rd.stgChart (GW2Rz.relChartX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω)) R a₀).dom : Set ℂ) ⊆ cL.dom ∧
      (∀ y ∈ ((GW2Rd.stgChart (GW2Rz.relChartX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω)) R a₀).dom : Set ℂ),
        cL.1 y ∈ H \ invHull (fun q : ℝ => Wk q.toNNReal) t₀) ∧
      EqOn (Ito.rpath (GW2Rd.stgDrv R a₀)) (fun s => Rk (lam ^ 2 * s) / lam) (Icc 0 ((A t : ℝ) - a₀)) ∧
      relClock (fun q : ℝ => Wk q.toNNReal) t₀
        (fun q : ℝ => (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).1 q.toNNReal) t = lam ^ 2 * ((A t : ℝ) - a₀) := by
  classical
  set rec := cfRec c.s c.W c.ζ ω with hrec
  set c₀ := GW2Rz.relChartX (rootPt r.1) c.s rec with hc₀def
  set cs := GW2Rd.stgChart c₀ R a₀ with hcsdef
  set k := GW2Olm.curIdx c r l with hk
  set D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun j => GW2Olm.futFam c r l a j ω with hD
  set Uk : ℝ → ℝ := fun q : ℝ => Wk q.toNNReal with hUk
  have hc₀ : c₀.IsConformal := GW2Rz.isConformal_relChartX _ _ rec
  have hcs : cs.IsConformal := GW2Rd.isConformal_stgChart hc₀ hR hR0 a₀
  have hUkc : Continuous Uk := hWk.comp continuous_real_toNNReal
  have hUk0 : Uk 0 = 0 := by simp [hUk, hWk0]
  have hℓ0 : ℓ 0 = 0 := GW2Sgk.clock_zero_of_range hℓm hℓr
  -- the dilation
  obtain ⟨lam, hlam, hdil⟩ := sample_kernel_dilationX c r l a hx0 hord t htpos ω hold hgood hl hc hconf hext htcap
    htζ hWk hWk0 hγk hW' hW'0 hγ' hsζ hηe hce h0e hℓc hℓm hℓr hvis hiff ht₀ hR hR0 hA0 hAa
    ((hAc.tendsto 0).trans (by rw [hA0])) hshape
  -- the union identity at every stage time `u ≤ t`
  have hU : ∀ u ≤ t, cL.1 '' (GW2Rd.schedUnionX c r l a (historyTime c r l) u ω ∩ (cL.dom : Set ℂ)) =
      invHull Uk (t₀ : ℝ) ∪ fwdHull (fun q : ℝ => (D k).1 q.toNNReal) (u : ℝ) := by
    intro u hu
    exact (launch_eq_of_clockX c r l a hx0 hord u ω hold hgood hl hc hconf hext (hu.trans_lt htcap)
      hWk hWk0 hγk hW' hW'0 hγ' hsζ hηe hce h0e hℓc hℓm hℓr hvis hiff ht₀
      ((ENNReal.coe_le_coe.2 hu).trans_lt htζ)).2
  -- the launch domain and the retained hull through `cL`
  obtain ⟨hdomL, -⟩ := launch_dom_contX c r l a hx0 hord ω hold hgood hl hc hconf hext hWk hWk0 hγk hW' hW'0
    hγ' hℓc hℓm.monotone hℓ0 hiff
  have hc0 : cL.2.1 '' invHull Uk (t₀ : ℝ) = invHull (fun u : ℝ => c.W u.toNNReal ω) c.s := by
    have h := launch_cont_of_rangeX c r l a hx0 hord ω hold hgood hl hc hconf hext hWk hWk0 hγk hW' hW'0 hγ' hηe
      hce h0e hℓc hℓm hℓr hvis hiff t₀
    rw [ht₀] at h
    exact h
  have hRp : Continuous (Ito.rpath R) := hR.comp continuous_real_toNNReal
  have hRp0 : Ito.rpath R 0 = 0 := by simp [Ito.rpath, hR0]
  have hB0 : GW2Rd.schedUnionX c r l a (historyTime c r l) 0 ω =
      invHull (fun u : ℝ => c.W u.toNNReal ω) c.s ∪ (fun z : ℂ => (rootPt r.1 : ℂ) + z) ''
        fwdHull (fun u : ℝ => GW2Rd.schedW c r l a u.toNNReal ω) (historyTime c r l : ℝ) := by
    rw [← Supp8.RelSafeS.invHull_record_eq hW'0 hW'.continuousOn hsζ]
    simp only [GW2Rd.schedUnionX, GW2Rd.schedHullX, hold, ↓reduceIte, GW2Rd.schedHull, add_zero]
  have hcsdom : (cs.dom : Set ℂ) = H \ GW2Rd.schedUnionX c r l a (historyTime c r l) 0 ω := by
    rw [hcs.coe_dom, hshape 0 zero_le, hA0]
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
  -- the driver relation
  have hKB : ∀ u ≤ t, (fun z : ℂ => (rootPt r.1 : ℂ) + z) ''
      fwdHull (fun u : ℝ => GW2Rd.schedW c r l a u.toNNReal ω) (historyTime c r l : ℝ) ⊆
        GW2Rd.schedUnionX c r l a (historyTime c r l) u ω := by
    intro u _ z hz
    simp only [GW2Rd.schedUnionX, GW2Rd.schedHullX, hold, ↓reduceIte, GW2Rd.schedHull]
    refine Or.inr (image_mono (WangWu.fwdHull_mono (by
      have : (historyTime c r l : ℝ) ≤ ((historyTime c r l + u : ℝ≥0) : ℝ) := by
        simp only [NNReal.coe_add]; linarith [u.coe_nonneg]
      exact this)) hz)
  obtain ⟨hS, hq⟩ := sample_driver_scale hconf hc₀ hR hR0 hUkc hUk0 hlam hdil hA0 hAa hAc.continuousOn hshape hdomL
    hKB hRk hRk0 (fun u hu => hhull u hu) hdisj (fun u hu => hU u hu)
  exact ⟨lam, hlam, hdil, hcsdom, hsubL, hmaps, hS, hq⟩

end InteractingSLE.Theorem14.GW2Kx
