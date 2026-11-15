/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2KxB0Dil
import InteractingSLE.Spec.Supplement.GW2KxRead
import InteractingSLE.Spec.Supplement.SB4RChart

/-!
# The root piece's stage reading from the root's start, at a root `x` (launch chart `recenter x`)

Packet PROVE-GW2-GEOM2, round 14 (D49). STAGEMEAN's `GW2Psm.sample_stage_read` for the root piece launched at index
`0` in `Chart.id.recenter x`, read in the root-`x` stage chart from the root's start: with the kernel forms at the
stage start (`RetFormAt`) and at `t ≤ T` (`UnionFormAt`), the stage-start identity `hinst0`, the far-right heights
and the geometry `sample_stage_geom0X`, the instance's representative read in the stage chart off the stage hull is
the canonical coupling mean (`GW2Psm.stage_step`).

* **`sample_stage_read0X`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdMap fwdMapInv fwdHull logDerivFwd chiC)

namespace InteractingSLE.Theorem14.GW2Kx

open GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2TipSystem.Swc GW2Schedule GW2Tip Exist Exist.Staged
  Exist.StagedLaw Sec5.Prop513Schedule GW2Omx Supp8.GB6LMean MartChar.RealFlow Restart Supp8.Q3Chain GW2Fb
  GW2JointKernel GW2Psm GW2Xk GW2Kb
open Supp8.GB6 (relMap gb6Rec relClock sphereInv firstContactTime)
open Supp8.Q3Rel (invHull relLog)

/-- **The root piece's stage reading from the root's start** (root `x ≥ 0`, launch chart `recenter x`, one sample). -/
theorem sample_stage_read0X {Ω : Type*} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (a : ℕ)
    (hx0 : 0 ≤ rootPt r.1) (t : ℝ≥0) (htpos : 0 < t) (htT : t ≤ historyTime c r []) (ω : Ω)
    (hold : oldSuccess c r [] ω)
    (hgood : ∀ (j : ℕ) (hj : j < (futureProgram c r [] a).length), LocalExt.IsDrvGood
      (recHist (programRecords c (rootPt r.1) (futureProgram c r [] a) ω ⟨j, hj⟩)))
    (hc0 : Continuous (stopDrv (specDelta (GW2Olm.futSpec c r [] a) 0) (GW2Olm.futFam c r [] a 0 ω)) ∧
      stopDrv (specDelta (GW2Olm.futSpec c r [] a) 0) (GW2Olm.futFam c r [] a 0 ω) 0 = 0)
    (htζ : (t : ℝ≥0∞) < (GW2Olm.futFam c r [] a 0 ω).2)
    (hreg : IsRegularDriver (GW2Olm.futFam c r [] a 0 ω)) {α : ℝ≥0 → ℂ}
    (hα : IsGeneratingTrace (GW2Olm.futFam c r [] a 0 ω).1 (GW2Olm.futFam c r [] a 0 ω).2 α)
    {Wk : ℝ≥0 → Ω → ℝ} {ζk : Ω → ℝ≥0∞} {γk : ℝ≥0 → ℂ} (hWk : Continuous fun q => Wk q ω) (hWk0 : Wk 0 ω = 0)
    (hγk : IsGeneratingTrace (fun q => Wk q ω) ⊤ γk)
    {γ' : ℝ≥0 → ℂ} (hW' : Continuous fun u => c.W u ω) (hW'0 : c.W 0 ω = 0)
    (hγ' : IsGeneratingTrace (fun u => c.W u ω) ⊤ γ') (hsζ : (c.s : ℝ≥0∞) < c.ζ ω)
    (hce : Continuous fun u => GW2Rd.schedW c r [] a u ω) (h0e : GW2Rd.schedW c r [] a 0 ω = 0)
    {ℓ : ℝ≥0 → ℝ≥0} (hℓc : Continuous ℓ) (hℓm : StrictMono ℓ)
    (hℓr : range ℓ = {q : ℝ≥0 | (q : ℝ≥0∞) < firstTipTime infinitySourceChart (fun u => c.W u ω)
      {((rootPt r.1 : ℝ) : ℂ)}})
    (hvis : 0 < rootPt r.1 → ∃ τ, (rootPt r.1 : ℂ) * γ' τ + 1 = 0)
    (hiff : ∀ (q : ℝ≥0) (z : ℂ), ((Chart.id.recenter (rootPt r.1)).trans infinitySourceChart).tipAt
      (fun q => Wk q ω) q z ↔ infinitySourceChart.tipAt (fun u => c.W u ω) (ℓ q) z) {t₀ : ℝ≥0} (ht₀ : ℓ t₀ = c.s)
    (hcontact : ((t : ℝ≥0) : ℝ≥0∞) < firstContactTime (fun u => (α u : OnePoint ℂ))
      ((fun u => sphereInv (γk u : OnePoint ℂ)) '' Icc 0 t₀)) {θ : ℝ}
    {R : ℝ≥0 → ℝ} (hR : Continuous R) (hR0 : R 0 = 0) {A : ℝ≥0 → ℝ≥0} {a₀ : ℝ≥0} (hA0 : A 0 = a₀)
    (hAa : ∀ u, a₀ ≤ A u) (hAc : Continuous A)
    (hshape : ∀ u ≤ t, H \ GW2Rd.schedUnionX c r [] a 0 u ω =
      (GW2Rz.relChartX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω)).2.1 '' (H \ fwdHull (Ito.rpath R) (A u)))
    {b' : ℝ → ℝ} {J' : Finset ℝ} (hb' : IsPiecewiseConstantBoundaryData b' J') {u' uθ : ℂ → ℝ}
    (hu' : IsBoundedHarmonicExtension b' J' u')
    (huθ : IsBoundedHarmonicExtension (forceBoundaryData c.κ (flowLineRhoL c.κ b' J' 0 θ)
      (flowLineRhoR c.κ b' J' 0 θ) (flowLineXL b' J' 0) (flowLineXR b' J' 0))
      (forceJumpSet (flowLineXL b' J' 0) (flowLineXR b' J' 0)) uθ)
    (c' : BoundaryWord) {wP wP₀ u₀ : ℂ → ℝ} {σa : ℝ}
    (hform0 : RetFormAt c.κ θ c' Wk ζk uθ ω t₀
      (fun z => wP₀ ((Chart.id.recenter (rootPt r.1)).2.1 z) + u₀ ((Chart.id.recenter (rootPt r.1)).2.1 z) +
        chiC c.κ * (Chart.id.recenter (rootPt r.1)).2.2 ((Chart.id.recenter (rootPt r.1)).2.1 z) - u' z)
      (H \ (Chart.id.recenter (rootPt r.1)).1 '' (GW2Rd.schedUnionX c r [] a 0 0 ω ∩
        ((Chart.id.recenter (rootPt r.1)).dom : Set ℂ))))
    (hformT : UnionFormAt c.κ θ b' J' c' Wk ζk (fun t ω => (GW2Olm.futFam c r [] a 0 ω).1 t) uθ
      ω t₀ t (fun z => wP ((Chart.id.recenter (rootPt r.1)).2.1 z) + u₀ ((Chart.id.recenter (rootPt r.1)).2.1 z) +
        chiC c.κ * (Chart.id.recenter (rootPt r.1)).2.2 ((Chart.id.recenter (rootPt r.1)).2.1 z) - u' z)
      (H \ (Chart.id.recenter (rootPt r.1)).1 '' (GW2Rd.schedUnionX c r [] a 0 t ω ∩
        ((Chart.id.recenter (rootPt r.1)).dom : Set ℂ))))
    {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j) {U₀ U : ℂ → ℝ}
    (hU₀ : IsBoundedHarmonicExtension (forceBoundaryData c.κ ρL ρR xL xR) (forceJumpSet xL xR) U₀)
    (hinst0 : ∀ y ∈ ((GW2Rd.stgChart (GW2Rz.relChartX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω)) R a₀).dom : Set ℂ),
      wP₀ y + u₀ y + σa + chiC c.κ * (GW2Rd.stgChart (GW2Rz.relChartX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω)) R
          a₀).2.2 y =
        U₀ ((GW2Rd.stgChart (GW2Rz.relChartX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω)) R a₀).1 y))
    {hK hβ : ℝ} (hfarK : ∃ B : ℝ, ∀ y, B < y →
      y ∉ (jointWordOfRec (specOffset c.κ) c.κ c' (cfRec t₀ Wk ζk ω)).jumps →
        (jointWordOfRec (specOffset c.κ) c.κ c' (cfRec t₀ Wk ζk ω)).fn y = hK)
    (hfarβ : ∃ B : ℝ, ∀ y, B < y → y ∉ forceJumpSet xL xR → forceBoundaryData c.κ ρL ρR xL xR y = hβ)
    (hfar : hK + θ * chiC c.κ = hβ)
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
      wP ((GW2Rd.stgChart (GW2Rz.relChartX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω)) R a₀).2.1 z) +
          u₀ ((GW2Rd.stgChart (GW2Rz.relChartX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω)) R a₀).2.1 z) + σa +
          chiC c.κ * (GW2Rd.stgChart (GW2Rz.relChartX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω)) R a₀).2.2
            ((GW2Rd.stgChart (GW2Rz.relChartX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω)) R a₀).2.1 z) =
        couplingMean c.κ (Ito.rpath (GW2Rd.stgDrv R a₀)) ((A t : ℝ) - a₀) U z := by
  classical
  set rec := cfRec c.s c.W c.ζ ω with hrec
  set c₀ := GW2Rz.relChartX (rootPt r.1) c.s rec with hc₀def
  set cL := Chart.id.recenter (rootPt r.1) with hcLdef
  have hcL : IsDomainChart (cL.dom : Set ℂ) cL := by
    rw [coe_dom_recenter_id]
    exact SB.Lf.isDomainChart_recenter isDomainChart_id (rootPt r.1)
  set cs := GW2Rd.stgChart c₀ R a₀ with hcsdef
  set Uk : ℝ → ℝ := fun q : ℝ => Wk q.toNNReal ω with hUk
  set Wc : ℝ → ℝ := fun q : ℝ => (GW2Olm.futFam c r [] a 0 ω).1 q.toNNReal with hWc
  set S : ℝ → ℝ := Ito.rpath (GW2Rd.stgDrv R a₀) with hSdef
  set Q : ℝ := (A t : ℝ) - a₀ with hQdef
  have hconf : cL.IsConformal := hcL.isConformal
  have hUkc : Continuous Uk := hWk.comp continuous_real_toNNReal
  have hUk0 : Uk 0 = 0 := by simp [hUk, hWk0]
  have hQ : 0 ≤ Q := sub_nonneg.2 (NNReal.coe_le_coe.2 (hAa t))
  -- the time-`t` form
  obtain ⟨p, G, hchain, hG, hEq⟩ := hformT
  obtain ⟨-, -, -, ⟨t₂, ht₂, hp1⟩, hRkc, hRk0, -, -, -, hHulls, -⟩ := hchain
  set Rk : ℝ → ℝ := p.2.2.1 with hRkdef
  set Wp : ℝ → ℝ := fun q : ℝ => p.1 q.toNNReal with hWp
  have hWpc : ∀ u : ℝ≥0, u ≤ t → fwdHull Wp (u : ℝ) = fwdHull Wc (u : ℝ) := by
    intro u hu
    refine LocalExt.fwdHull_congr_of_eqOn_of_lt u.coe_nonneg (t' := (t₂ : ℝ)) ?_ fun x hx => ?_
    · exact_mod_cast hu.trans_lt ht₂
    · have hxle : x.toNNReal ≤ t₂ := by
        rw [Real.toNNReal_le_iff_le_coe]
        exact hx.2
      simp only [hWp, hWc]
      exact hp1 _ hxle
  have hclock : ∀ u : ℝ≥0, u ≤ t → relClock Uk t₀ Wp u = relClock Uk t₀ Wc u := by
    intro u hu
    unfold relClock
    rw [hWpc u hu]
  have hhull : HullsUpTo Uk t₀ Wc Rk t := by
    intro u hu
    rw [← hWpc u hu, ← hclock u hu]
    exact hHulls u hu
  -- the piece's hulls miss the retained hull
  have hdisj : ∀ u : ℝ≥0, u ≤ t → fwdHull Wc u ⊆ H \ invHull Uk t₀ := by
    intro u hu x hx
    have hu' : (u : ℝ≥0∞) < (GW2Olm.futFam c r [] a 0 ω).2 :=
      (ENNReal.coe_le_coe.2 hu).trans_lt htζ
    have hD := Supp8.GB6.disjoint_closure_fwdHull_inv_image hα hreg.1 hreg.2.1 hγk hWk.continuousOn hWk0 hu'
      (show ((t₀ : ℝ≥0) : ℝ≥0∞) < ⊤ from ENNReal.coe_lt_top) (fun v hv hv0 hmem => by
        obtain ⟨u', hu'm, hu'e⟩ := hmem
        have hlt : ((u' : ℝ≥0) : ℝ≥0∞) < firstContactTime (fun u => (α u : OnePoint ℂ))
            ((fun u => sphereInv (γk u : OnePoint ℂ)) '' Icc 0 t₀) :=
          lt_of_le_of_lt (ENNReal.coe_le_coe.2 (hu'm.2.trans hu)) hcontact
        refine Supp8.GB6.notMem_of_lt_firstContactTime hlt ⟨v, hv, ?_⟩
        show sphereInv (γk v : OnePoint ℂ) = (α u' : OnePoint ℂ)
        rw [Supp8.GB6.sphereInv_coe_of_ne hv0, hu'e])
    refine ⟨hx.1, fun hxI => ?_⟩
    exact Set.disjoint_left.1 hD (subset_closure hx) (subset_closure hxI)
  -- the stage-start geometry
  have hWcK : ∀ u : ℝ≥0, u ≤ t →
      fwdHull Wc u = fwdHull (fun q : ℝ => GW2Rd.schedW c r [] a q.toNNReal ω) u := fun u hu =>
    fwdHull_root_eq c r a hold hgood hc0 hreg (hu.trans htT)
  obtain ⟨lam, hlam, hdil, hcsdom, hmaps, hS, hq⟩ := sample_stage_geom0X c r a hx0 t htpos ω hold hce h0e hWk hWk0
    hγk hW' hW'0 hγ' hsζ hℓc hℓm hℓr hvis hiff ht₀ hR hR0 hA0 hAa hAc hshape hWcK hRkc hRk0
    (fun u hu => hhull u hu) hdisj
  rw [← hcLdef] at hdil hmaps
  have hsubL : ((GW2Rd.stgChart c₀ R a₀).dom : Set ℂ) ⊆ (cL.dom : Set ℂ) := by
    intro z hz
    rw [coe_dom_recenter_id]
    rw [hcsdom] at hz
    exact hz.1
  have hqp : relClock Uk t₀ Wp t = lam ^ 2 * Q := (hclock t le_rfl).trans hq
  have hG' : IsBoundedHarmonicExtension
      (flowedData c.κ (flowLineRhoL c.κ (jointWordOfRec (specOffset c.κ) c.κ c' (cfRec t₀ Wk ζk ω)).fn
          (jointWordOfRec (specOffset c.κ) c.κ c' (cfRec t₀ Wk ζk ω)).jumps 0 θ)
        (flowLineRhoR c.κ (jointWordOfRec (specOffset c.κ) c.κ c' (cfRec t₀ Wk ζk ω)).fn
          (jointWordOfRec (specOffset c.κ) c.κ c' (cfRec t₀ Wk ζk ω)).jumps 0 θ)
        (flowLineXL (jointWordOfRec (specOffset c.κ) c.κ c' (cfRec t₀ Wk ζk ω)).fn
          (jointWordOfRec (specOffset c.κ) c.κ c' (cfRec t₀ Wk ζk ω)).jumps 0)
        (flowLineXR (jointWordOfRec (specOffset c.κ) c.κ c' (cfRec t₀ Wk ζk ω)).fn
          (jointWordOfRec (specOffset c.κ) c.κ c' (cfRec t₀ Wk ζk ω)).jumps 0) Rk (lam ^ 2 * Q))
      (flowedJumps (flowLineXL (jointWordOfRec (specOffset c.κ) c.κ c' (cfRec t₀ Wk ζk ω)).fn
          (jointWordOfRec (specOffset c.κ) c.κ c' (cfRec t₀ Wk ζk ω)).jumps 0)
        (flowLineXR (jointWordOfRec (specOffset c.κ) c.κ c' (cfRec t₀ Wk ζk ω)).fn
          (jointWordOfRec (specOffset c.κ) c.κ c' (cfRec t₀ Wk ζk ω)).jumps 0) Rk (lam ^ 2 * Q)) G := by
    rw [← hqp]
    exact hG
  have hcsD := isDomainChart_stgChart_relChartX (rootPt r.1) c.s rec hR hR0 a₀
  have huθ' := sub_eq_of_bhe_angle c.hκ hb' hu' huθ
  -- membership off the launch images of the unions
  have hoff : ∀ u : ℝ≥0, ∀ y ∈ (cL.dom : Set ℂ), y ∉ GW2Rd.schedUnionX c r [] a 0 u ω →
      cL.1 y ∉ cL.1 '' (GW2Rd.schedUnionX c r [] a 0 u ω ∩ (cL.dom : Set ℂ)) := by
    rintro u y hyL hyB ⟨y', ⟨hy'B, hy'L⟩, he⟩
    have : y' = y := by rw [← hcL.inv_fwd hy'L, he, hcL.inv_fwd hyL]
    exact hyB (this ▸ hy'B)
  have hret : ∀ G₀ : ℂ → ℝ, IsBoundedHarmonicExtension
      (cfData c.κ (jointWordOfRec (specOffset c.κ) c.κ c' (cfRec t₀ Wk ζk ω)).fn
        (jointWordOfRec (specOffset c.κ) c.κ c' (cfRec t₀ Wk ζk ω)).jumps)
      (cfJumps (jointWordOfRec (specOffset c.κ) c.κ c' (cfRec t₀ Wk ζk ω)).fn
        (jointWordOfRec (specOffset c.κ) c.κ c' (cfRec t₀ Wk ζk ω)).jumps) G₀ →
      ∀ y ∈ (cs.dom : Set ℂ), wP₀ y + u₀ y + chiC c.κ * cL.2.2 y - u' (cL.1 y) + (uθ (cL.1 y) - θ * chiC c.κ) =
        G₀ (relMap Uk t₀ (cL.1 y)) - chiC c.κ * (relLog Uk t₀ (cL.1 y)).im := by
    intro G₀ hG₀ y hy
    have hyL := hsubL hy
    have hyB : y ∉ GW2Rd.schedUnionX c r [] a 0 0 ω := by
      rw [hcsdom] at hy
      exact hy.2
    have h := hform0 G₀ hG₀ ⟨(hmaps y hy).1, hoff 0 y hyL hyB⟩
    simp only [hcL.inv_fwd hyL] at h
    exact h
  intro z hz
  have hy : cs.2.1 z ∈ (cs.dom : Set ℂ) := hcsD.inv_mem hz.1
  have hcz : cs.1 (cs.2.1 z) = z := hcsD.fwd_inv hz.1
  have hSc : Continuous S := (GW2Rd.continuous_stgDrv hR a₀).comp continuous_real_toNNReal
  have hyQ : fwdMap (fun s => Rk (lam ^ 2 * s) / lam) Q (cs.1 (cs.2.1 z)) ∈ H := by
    rw [hcz, ← QuantumZipper.CharFunRhs.fwdMap_eq_of_eqOn fun x hx => hS hx]
    exact QuantumZipper.FwdHolo.mapsTo_fwdMap hSc hQ hz
  have hyB : cs.2.1 z ∉ GW2Rd.schedUnionX c r [] a 0 t ω := by
    have h1 := GW2Rd.stgChart_inv_image c₀ hR hR0 a₀ (A t - a₀)
    have hsum : a₀ + (A t - a₀) = A t := add_tsub_cancel_of_le (hAa t)
    have hcoe : ((A t - a₀ : ℝ≥0) : ℝ) = Q := by rw [NNReal.coe_sub (hAa t)]
    rw [hsum, hcoe, ← hshape t le_rfl] at h1
    have hmem : cs.2.1 z ∈ cs.2.1 '' (H \ fwdHull S Q) := mem_image_of_mem _ hz
    rw [h1] at hmem
    exact hmem.2
  have ht := hEq ⟨(hmaps _ hy).1, hoff t _ (hsubL hy) hyB⟩
  simp only [hcL.inv_fwd (hsubL hy)] at ht
  rw [hqp] at ht
  have key := stage_step c.hκ hcL hcsD hsubL hUkc hUk0 t₀.coe_nonneg hmaps hlam hdil huθ'
    (jointWordOfRec (specOffset c.κ) c.κ c' (cfRec t₀ Wk ζk ω)) hret ρL ρR hxL hxR hU₀ hinst0 hfarK hfarβ hfar
    hRkc hRk0 hSc hQ hS hG' hU hy hyQ (by exact ht)
  rw [hcz] at key
  exact key

end InteractingSLE.Theorem14.GW2Kx
