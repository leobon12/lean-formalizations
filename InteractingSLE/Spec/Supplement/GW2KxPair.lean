/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2KxKer
import InteractingSLE.Spec.Supplement.GW2PsmPairP

/-!
# The pairing of the instance's mean at stage time `t > 0` from the stage start, at a root `x`

Packet PROVE-GW2-GEOM2, round 14 (D49). STAGEMEAN's `GW2Psm.pair_root0` at a root `x = rootPt r.1 ∈ {0} ∪
lowerArcRoots`, with the root-`x` union `schedUnionX` and the stage chart on `relChartX x s rec` (D8's `chartX`):

* **`stgMeanRX`**: the explicit stage mean of a relative driver read from the stage start in the root-`x` stage chart;
  `stgMeanRX_of_baseRead_zero`: at a record with `baseRead x s rec = 0` (e.g. the root `0`) it is `GW2Psm.stgMeanR`;
* **`pair_rootX`**: the kernel chain `GW2Omx.ae_of_kernel_curS` (root `x`) with the bundle `ae_kernel_identity_rootX`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull logDerivFwd chiC)
open SupercriticalConformalCovariance.GM24 (smoothDist)

universe u

namespace InteractingSLE.Theorem14.GW2Kx

open Restart Exist Exist.Staged Exist.StagedLaw WholeField LocalSets GW2TipSystem GW2TipSystem.RootC24
  GW2TipSystem.RootJ31 GW2Schedule GW2Tip GW2Sdi GW2Rd GW2Olm Supp8 Supp8.GB6 Restart.MarkovChart GW2Omx
  MartChar.RealFlow GW2Psm GW2Xk

/-- **The explicit stage mean at a root `x`** of a relative driver `R` read from the stage start `a₀` at clock `Q`, in
the root-`x` stage chart `stgChart (relChartX x s rec) R a₀`. -/
def stgMeanRX (κ x : ℝ) (s : ℝ≥0) (rec : RecData) (R : ℝ≥0 → ℝ) (a₀ : ℝ≥0) (Q : ℝ) (U u₀ : ℂ → ℝ) (σa : ℝ)
    (y : ℂ) : ℝ :=
  couplingMean κ (Ito.rpath (stgDrv R a₀)) Q U ((stgChart (GW2Rz.relChartX x s rec) R a₀).1 y) - u₀ y - σa -
    chiC κ * (stgChart (GW2Rz.relChartX x s rec) R a₀).2.2 y

/-- At a record read `0` at the root, the root-`x` stage mean is STAGEMEAN's `stgMeanR`. -/
theorem stgMeanRX_of_baseRead_zero (κ x : ℝ) (s : ℝ≥0) {rec : RecData} (h : GW2Rz.baseRead x s rec = 0)
    (R : ℝ≥0 → ℝ) (a₀ : ℝ≥0) (Q : ℝ) (U u₀ : ℂ → ℝ) (σa : ℝ) :
    stgMeanRX κ x s rec R a₀ Q U u₀ σa = stgMeanR κ rec R a₀ Q U u₀ σa := by
  unfold stgMeanRX stgMeanR
  rw [relChartX_of_baseRead_zero h]

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **The pairing at `t > 0` from the stage start** (root `x`). -/
theorem pair_rootX (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    (hroot : rootPt r.1 = 0 ∨ rootPt r.1 ∈ lowerArcRoots c.κ c.b c.jumps) (hord : (historyProgram c r l).Pairwise (fun
      p q => p.2 < q.2)) (hs0 : 0 < c.s)
    {u₀ : ℂ → ℝ} (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField c.h u₀) c.P) (t : ℝ≥0) (htpos : 0 < t)
    (htcap : t < candidateCap c r a)
    (hloc : IsHistoryAvoidanceLocal (stgF c r l a t) (schedUnionX c r l a (historyTime c r l) t) (centredField c.h u₀)
      c.P)
    (hloc₀ : IsHistoryAvoidanceLocal (stgF c r l a 0) (schedUnionX c r l a (historyTime c r l) 0) (centredField c.h
      u₀) c.P)
    {G : Set Ω} (hGm : MeasurableSet G) (hGs : ∀ ω ∈ G, oldSuccess c r l ω)
    {R : ℝ≥0 → Ω → ℝ} {A : ℝ≥0 → Ω → ℝ≥0} {a₀ : Ω → ℝ≥0} {σa : ℝ} {nL nR : ℕ} (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ) {xL : Ω → Fin nL → ℝ} {xR : Ω → Fin nR → ℝ} {U₀ U : Ω → ℂ → ℝ} {hβ : ℝ}
    (hθ : ∀ (ω₀ : Ω) (cL : Chart) (θ : ℝ), curLaunch c r l a ω₀ = some (cL, θ) →
      sleLambda (16 / c.κ) - Real.pi * chiC c.κ + θ * chiC c.κ = hβ)
    (hread : ∀ᵐ ω ∂c.P, ω ∈ G →
      (t : ℝ≥0∞) < (futFam c r l a (curIdx c r l) ω).2 ∧ c.α ω c.s ∈ H ∧
      (∀ v ∈ Icc 0 c.s, ∀ u ≤ historyTime c r l + t,
        c.α ω v * ((rootPt r.1 : ℂ) + schedTr c r l a ω u) + 1 ≠ 0) ∧
      Continuous (fun u => R u ω) ∧ R 0 ω = 0 ∧ A 0 ω = a₀ ω ∧ (∀ u, a₀ ω ≤ A u ω) ∧ Continuous (fun u => A u ω) ∧
      (∀ u ≤ t, H \ schedUnionX c r l a (historyTime c r l) u ω =
        (GW2Rz.relChartX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω)).2.1 '' (H \ fwdHull (Ito.rpath fun q => R q ω) (A u
          ω))) ∧
      (∀ i, xL ω i ≤ 0) ∧ (∀ j, 0 ≤ xR ω j) ∧
      IsBoundedHarmonicExtension (forceBoundaryData c.κ ρL ρR (xL ω) (xR ω)) (forceJumpSet (xL ω) (xR ω)) (U₀ ω) ∧
      (∃ B : ℝ, ∀ y, B < y → y ∉ forceJumpSet (xL ω) (xR ω) →
        forceBoundaryData c.κ ρL ρR (xL ω) (xR ω) y = hβ) ∧
      IsBoundedHarmonicExtension
        (forceBoundaryData c.κ ρL ρR
          (fun i => -rightImg (fun s => -Ito.rpath (stgDrv (fun q => R q ω) (a₀ ω)) s) (-xL ω i)
            ((A t ω : ℝ) - a₀ ω) - Ito.rpath (stgDrv (fun q => R q ω) (a₀ ω)) ((A t ω : ℝ) - a₀ ω))
          (fun j => rightImg (Ito.rpath (stgDrv (fun q => R q ω) (a₀ ω))) (xR ω j) ((A t ω : ℝ) - a₀ ω) -
            Ito.rpath (stgDrv (fun q => R q ω) (a₀ ω)) ((A t ω : ℝ) - a₀ ω)))
        (forceJumpSet
          (fun i => -rightImg (fun s => -Ito.rpath (stgDrv (fun q => R q ω) (a₀ ω)) s) (-xL ω i)
            ((A t ω : ℝ) - a₀ ω) - Ito.rpath (stgDrv (fun q => R q ω) (a₀ ω)) ((A t ω : ℝ) - a₀ ω))
          (fun j => rightImg (Ito.rpath (stgDrv (fun q => R q ω) (a₀ ω))) (xR ω j) ((A t ω : ℝ) - a₀ ω) -
            Ito.rpath (stgDrv (fun q => R q ω) (a₀ ω)) ((A t ω : ℝ) - a₀ ω))) (U ω) ∧
      InnerProductSpace.HarmonicOnNhd
        (stgMeanRX c.κ (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω) (fun q => R q ω) (a₀ ω) 0 (U₀ ω) u₀ σa)
        (H \ schedUnionX c r l a (historyTime c r l) 0 ω))
    (hclaim : ∀ g₀ : Ω → DistOn upperHalfPlaneOpens,
      IsLocalSetMean (schedUnionX c r l a (historyTime c r l) 0) (centredField c.h u₀) c.P g₀ → ∀ φ : TestOn
          upperHalfPlaneOpens,
      ∀ᵐ ω ∂c.P, ω ∈ G → tsupport φ ⊆ H \ schedUnionX c r l a (historyTime c r l) 0 ω →
        g₀ ω φ = ∫ z, stgMeanRX c.κ (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω) (fun q => R q ω) (a₀ ω) 0 (U₀ ω) u₀ σa z *
            φ z)
    {F : TestOn upperHalfPlaneOpens → Ω → ℝ} (hFm : ∀ φ : TestOn upperHalfPlaneOpens, Measurable (F φ))
    (hFeq : ∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂c.P, ω ∈ G → tsupport φ ⊆ H \ schedUnionX c r l a (historyTime c r
      l) t ω →
      F φ ω = ∫ z, stgMeanRX c.κ (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω) (fun q => R q ω) (a₀ ω) ((A t ω : ℝ) - a₀ ω)
          (U ω) u₀ σa z *
        φ z)
    (g : Ω → DistOn upperHalfPlaneOpens) (hg : IsLocalSetMean (schedUnionX c r l a (historyTime c r l) t)
      (centredField c.h u₀) c.P g)
    (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂c.P, ω ∈ G → tsupport φ ⊆ H \ schedUnionX c r l a (historyTime c r l) t ω →
      g ω φ = ∫ z, stgMeanRX c.κ (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω) (fun q => R q ω) (a₀ ω) ((A t ω : ℝ) - a₀ ω)
          (U ω) u₀ σa z *
        φ z := by
  classical
  obtain ⟨g', g₀', hg', hg₀', hK⟩ := ae_kernel_identity_rootX h12 h13 h13₀ c r l a hroot hord hs0 hu₀ hh0 t htpos
    htcap hloc hloc₀
  have hhm : Measurable (centredField c.h u₀) := measurable_centredField c.hh.1 u₀
  have hBm := measurable_schedUnionX c r l a (historyTime c r l) t
  have hBc : ∀ (u : ℝ≥0) (ω : Ω), schedUnionX c r l a (historyTime c r l) u ω ⊆ H ∧
      IsOpen (H \ schedUnionX c r l a (historyTime c r l) u ω) :=
    fun u ω => schedUnionX_subset_isOpen c r l a (historyTime c r l) u ω
  have hgg' := IsLocalSetMean.ae_apply_eq hBm hhm hg hg' φ
  -- Claim(k) for `g₀'`, at every test function on one event
  have hclaimAll : ∀ᵐ ω ∂c.P, ω ∈ G → ∀ φ' : TestOn upperHalfPlaneOpens,
      tsupport φ' ⊆ H \ schedUnionX c r l a (historyTime c r l) 0 ω →
        g₀' ω φ' = ∫ z, stgMeanRX c.κ (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω) (fun q => R q ω) (a₀ ω) 0 (U₀ ω) u₀ σa z
            * φ' z := by
    set A' : Ω → Set ℂ := fun ω => if ω ∈ G then schedUnionX c r l a (historyTime c r l) 0 ω else H with hA'
    set m : Ω → ℂ → ℝ := fun ω => if ω ∈ G then
      stgMeanRX c.κ (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω) (fun q => R q ω) (a₀ ω) 0 (U₀ ω) u₀ σa else 0 with hm
    have hφ' : ∀ φ' : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂c.P, tsupport φ' ⊆ H \ A' ω →
        g₀' ω φ' = ∫ z, m ω z * φ' z := by
      intro φ'
      filter_upwards [hclaim g₀' hg₀' φ'] with ω h1 hsupp
      by_cases hω : ω ∈ G
      · simp only [hA', hω, ↓reduceIte] at hsupp
        simp only [hm, hω, ↓reduceIte]
        exact h1 hω hsupp
      · simp only [hA', hω, ↓reduceIte, Set.sdiff_self] at hsupp
        have h0 : ∀ z, φ' z = 0 := fun z => image_eq_zero_of_notMem_tsupport fun hz => notMem_empty z (hsupp hz)
        have hφ0 : φ' = 0 := by
          ext z
          exact h0 z
        rw [hφ0, map_zero]
        have e : (fun z => m ω z * (0 : TestOn upperHalfPlaneOpens) z) = fun _ => 0 := by
          funext z
          rw [← hφ0, h0 z, mul_zero]
        rw [e, integral_zero]
    have hharm' : ∀ᵐ ω ∂c.P, IsHarmonicDistOn (g₀' ω) (H \ A' ω) := by
      filter_upwards [hg₀'.2.1] with ω h
      by_cases hω : ω ∈ G
      · simpa only [hA', hω, ↓reduceIte] using h
      · simp only [hA', hω, ↓reduceIte, Set.sdiff_self]
        exact GW2Scl.isHarmonicDistOn_empty _
    have hopen' : ∀ᵐ ω ∂c.P, IsOpen (H \ A' ω) := Eventually.of_forall fun ω => by
      by_cases hω : ω ∈ G
      · simpa only [hA', hω, ↓reduceIte] using (hBc 0 ω).2
      · simp only [hA', hω, ↓reduceIte, Set.sdiff_self, isOpen_empty]
    have hm' : ∀ᵐ ω ∂c.P, InnerProductSpace.HarmonicOnNhd (m ω) (H \ A' ω) := by
      filter_upwards [hread] with ω hrd
      by_cases hω : ω ∈ G
      · simp only [hA', hm, hω, ↓reduceIte]
        exact (hrd hω).2.2.2.2.2.2.2.2.2.2.2.2.2.2
      · simp only [hA', hω, ↓reduceIte, Set.sdiff_self]
        exact fun z hz => absurd hz (notMem_empty z)
    filter_upwards [WangWu.ae_forall_apply_eq_of_forall_ae hharm' hopen' hm' hφ'] with ω hω hωG φ' hsupp
    have h := hω φ' (by simpa only [hA', hωG, ↓reduceIte] using hsupp)
    simpa only [hm, hωG, ↓reduceIte] using h
  -- the chain
  set Aφ : Set Ω := {ω | ω ∈ G → tsupport φ ⊆ H \ schedUnionX c r l a (historyTime c r l) t ω → g' ω φ = F φ ω} with hAφ
  have hAm : MeasurableSet Aφ := by
    have h1 : MeasurableSet {ω | tsupport φ ⊆ H \ schedUnionX c r l a (historyTime c r l) t ω} :=
      GW2Spm.measurableSet_tsupport_subset_H_diff hBm (hBc t) φ
    have hg'm : Measurable fun ω => g' ω φ :=
      (Sobolev.measurable_distOn_apply φ).comp (hg'.1.mono (germSigma_le hBm hhm) le_rfl)
    have h2 : MeasurableSet {ω | g' ω φ = F φ ω} := measurableSet_eq_fun hg'm (hFm φ)
    have e : Aφ = Gᶜ ∪ ({ω | tsupport φ ⊆ H \ schedUnionX c r l a (historyTime c r l) t ω}ᶜ ∪ {ω | g' ω φ = F φ ω}) :=
        by
      ext ω
      simp only [hAφ, mem_ofPred_eq, mem_union, mem_compl_iff]
      tauto
    rw [e]
    exact hGm.compl.union (h1.compl.union h2)
  have hTO : Sec5.Prop513Schedule.TimeOrdered 0 (historyProgram c r l) := Gm.timeOrdered_of_pairwise_lt hord
  set spec := futSpec c r l a with hspec
  set E := futFam c r l a with hEdef
  set k := curIdx c r l with hkdef
  have hS : IsStagedHistory c.κ c.b c.jumps c.P c.h spec E := isStagedHistory_canonFam c.hκ c.h12p c.βA c.c₀
    (specAngle spec) (specDelta spec) h13 c.hβA c.hb c.hc₀J c.hc₀ c.hh (spec := spec) rfl
    (isFlowProg_spec (rootPt r.1) true (futureProgram c r l a)) (specDelta_ne_top _)
  have h𝒢 : pastG c r l a ≤ mΩ := hS.2.1 k
  have hchain := ae_of_kernel_curS h12 h13 h12₀ h13₀ c r l a hroot hord hAm (by
    filter_upwards [hK, ae_ae_not_oldSuccess h13 c r l a, KernelTower.ae_ae_condExpKernel_of_ae h𝒢 hread,
      KernelTower.ae_ae_condExpKernel_of_ae h𝒢 hclaimAll, KernelTower.ae_ae_condExpKernel_of_ae h𝒢 hg'.2.1,
      KernelTower.ae_ae_condExpKernel_of_ae h𝒢 (hFeq φ)] with ω₀ hKω hnot hreadν hclaimν hharmν hFν hcase
    by_cases hs : AllSucc (schedDelta 0 (futureProgram c r l a)) (fun j => futFam c r l a j ω₀) (curIdx c r l)
    · have hdat := hcase hs
      have hs' : AllSucc (specDelta spec) (fun j => E j ω₀) k := (allSucc_futSpec_iff c r l a ω₀).1 hs
      set L := futureProgram c r l a with hL
      have hlenL : L.length = k + 1 := by rw [hL, futureProgram, List.length_append, List.length_singleton]
      have hlen : spec.2.2.length = k + 1 := (GW2Schedule.length_scheduleProgram 0 L).trans hlenL
      have hl' := (launches_run_gw2 (κ := c.κ) (b := c.b) (jumps := c.jumps) (spec := spec) rfl
        (isFlowProg_spec (rootPt r.1) true L) (specDelta_ne_top _) (fun j => E j ω₀)
        (show k < spec.2.2.length by omega)).1 hs'
      have hl : curLaunch c r l a ω₀ = some (succChart spec.1 (specDelta spec) (fun j => E j ω₀) k,
          specAngle spec k) := hl'
      filter_upwards [hKω hdat _ _ hl, hreadν, hclaimν, hharmν, hFν] with ω hω hrd hcl hharm hF hωG hsupp
      obtain ⟨htζ, hαs, hnc, hRc, hR0, hA0, hAa, hAc, hshape, hxL, hxR, hU₀, hfarβ, hU, hM₀⟩ := hrd hωG
      obtain ⟨wP, hwP, hgP⟩ := hharm
      set cs := stgChart (GW2Rz.relChartX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω)) (fun q => R q ω) (a₀ ω) with hcs
      have hcsD := isDomainChart_stgChart_relChartX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω) hRc hR0 (a₀ ω)
      have hinst0 : ∀ y ∈ (cs.dom : Set ℂ),
          stgMeanRX c.κ (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω) (fun q => R q ω) (a₀ ω) 0 (U₀ ω) u₀ σa y + u₀ y + σa +
            chiC c.κ * cs.2.2 y = U₀ ω (cs.1 y) := by
        intro y hy
        have hy0 : cs.1 y ≠ 0 := fun h0 => by
          have := hcsD.fwd_mem hy
          rw [h0] at this
          have h' : (0 : ℝ) < (0 : ℂ).im := this
          simp at h'
        have hS0 : Ito.rpath (stgDrv (fun q => R q ω) (a₀ ω)) 0 = 0 := by simp [Ito.rpath, stgDrv_zero]
        simp only [stgMeanRX]
        rw [Coupling.MartMeans2.couplingMean_zero c.κ hS0 (U₀ ω) hy0]
        ring
      have hid := hω htζ hαs hnc (fun q => R q ω) (fun u => A u ω) (a₀ ω) hRc hR0 hA0 hAa hAc hshape wP
        (stgMeanRX c.κ (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω) (fun q => R q ω) (a₀ ω) 0 (U₀ ω) u₀ σa) σa hwP hgP hM₀
        (hcl hωG) ρL ρR (xL ω) (xR ω) (U₀ ω) (U ω) hβ hxL hxR hU₀ hinst0 hfarβ (hθ ω₀ _ _ hl) hU
      -- `wP` is the explicit stage mean off `B t`
      have hsh := GW2Rd.stgChart_inv_image (GW2Rz.relChartX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω)) hRc hR0
        (a₀ ω)
        (A t ω - a₀ ω)
      have hsum : a₀ ω + (A t ω - a₀ ω) = A t ω := add_tsub_cancel_of_le (hAa t)
      have hcoe : ((A t ω - a₀ ω : ℝ≥0) : ℝ) = (A t ω : ℝ) - a₀ ω := by rw [NNReal.coe_sub (hAa t)]
      rw [hsum, hcoe, ← hshape t le_rfl] at hsh
      have heq : ∀ y ∈ H \ schedUnionX c r l a (historyTime c r l) t ω,
          wP y = stgMeanRX c.κ (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω) (fun q => R q ω) (a₀ ω) ((A t ω : ℝ) - a₀ ω) (U
              ω) u₀ σa y := by
        intro y hy
        rw [← hsh] at hy
        obtain ⟨z, hz, rfl⟩ := hy
        have h1 := hid z hz
        have hcz : cs.1 (cs.2.1 z) = z := hcsD.fwd_inv hz.1
        simp only [stgMeanRX]
        rw [hcz]
        linarith
      rw [hgP φ hsupp, hF hωG hsupp]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      by_cases hz : z ∈ tsupport φ
      · simp only
        rw [heq z (hsupp hz)]
      · simp only
        rw [image_eq_zero_of_notMem_tsupport hz, mul_zero, mul_zero]
    · have hs' : ¬ AllSucc (specDelta spec) (fun j => E j ω₀) k := fun h => hs ((allSucc_futSpec_iff c r l a ω₀).2 h)
      filter_upwards [hnot hs'] with ω hω hωG
      exact absurd (hGs ω hωG) hω)
  filter_upwards [hchain, hgg', hFeq φ] with ω h1 h2 h3 hωG hsupp
  rw [h2, h1 hωG hsupp, h3 hωG hsupp]

end InteractingSLE.Theorem14.GW2Kx
