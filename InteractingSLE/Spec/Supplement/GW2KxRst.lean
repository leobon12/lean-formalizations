/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2KxUnion
import InteractingSLE.Spec.Supplement.GW2PsmStepC
import InteractingSLE.Spec.Supplement.GW2PsmConv
import InteractingSLE.Spec.Supplement.GW2PsmVer
import InteractingSLE.Spec.Supplement.GW2PsmCapL
import InteractingSLE.Spec.Supplement.GW2TqCond

/-!
# The Claim(k) step's restart, version conversion and domain at a root `x`

Packet PROVE-GW2-GEOM2, round 14 (D49). STAGEMEAN's deterministic stage-mean identities (`GW2PsmRestart`,
`GW2PsmConv`, `GW2PsmVer`) and the step's restart (`GW2PsmStepC`), domain (`GW2PsmCapL`) for the root-`x` stage
chart on `relChartX` and the root-`x` union:

* `stgMeanRX_restart`, `stgMeanRX_zero_add_const`, `stgMeanRX_zero_congr`, `integral_stgMeanRX_zero_conv`;
* `ae_compl_eq_dom_rootX`;
* **`claim_of_prefix_pairX`**: the prefix's pairing at the entry's end gives the history's stage-start pairing.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H chiC fwdMap fwdMapInv fwdHull logDerivFwd)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.GW2Kx

open LocalSets WholeField Restart Exist Exist.Staged Exist.StagedLaw GW2Schedule GW2Tip GW2TipSystem
  GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2Rd GW2Rz GW2Sde GW2JointKernel Supp8 Supp8.GB6 GW2Psm

/-- **The explicit stage mean restarted at a later stage start.** -/
theorem stgMeanRX_restart (κ x : ℝ) (s : ℝ≥0) (rec : RecData) {R : ℝ≥0 → ℝ} (hR : Continuous R) (hR0 : R 0 = 0)
    (a q : ℝ≥0) {U' U₀ u₀ : ℂ → ℝ} {σa' σa : ℝ} (hU : ∀ z ∈ H, U₀ z = U' z + (σa - σa')) {y : ℂ}
    (hy : y ∈ ((stgChart (GW2Rz.relChartX x s rec) R (a + q)).dom : Set ℂ)) :
    stgMeanRX κ x s rec R a (q : ℝ) U' u₀ σa' y = stgMeanRX κ x s rec R (a + q) 0 U₀ u₀ σa y := by
  set c := GW2Rz.relChartX x s rec with hc
  set w : ℝ → ℝ := Ito.rpath R with hw
  have hwc : Continuous w := hR.comp continuous_real_toNNReal
  have hw0 : w 0 = 0 := by simp [hw, Ito.rpath, hR0]
  have hcsD := isDomainChart_stgChart_relChartX x s rec hR hR0 (a + q)
  set z := c.1 y with hz
  -- `z` is not swallowed by `a + q`
  have hfwd := hcsD.fwd_mem hy
  have hzK : z ∈ H \ fwdHull w ((a + q : ℝ≥0) : ℝ) := by
    have hy' := hy
    rw [hcsD.coe_dom] at hy'
    have hdom := hcsD.isConformal
    rw [hdom.coe_dom] at hy'
    obtain ⟨v, hv, hvy⟩ := hy'
    have h1 : (stgChart c R (a + q)).2.1 v = c.2.1 (QuantumZipper.fwdMapInv w ((a + q : ℝ≥0) : ℝ) v) := rfl
    have hz' : z = QuantumZipper.fwdMapInv w ((a + q : ℝ≥0) : ℝ) v := by
      rw [hz, ← hvy, h1]
      exact (GW2Rz.isConformal_relChartX x s rec).2.2 _
        (QuantumZipper.RS.fwdMapInv_mem_H hwc hw0 (by positivity) hv)
    rw [hz']
    exact QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hwc hw0 (by positivity) hv
  have haq : ((a + q : ℝ≥0) : ℝ) = (a : ℝ) + q := NNReal.coe_add a q
  rw [haq] at hzK
  -- the restarted driver is the stage driver
  have hshift : ∀ r ∈ Icc (0 : ℝ) q, (fun r => w ((a : ℝ) + r) - w a) r = Ito.rpath (stgDrv R a) r :=
    fun r hr => (rpath_stgDrv_eq R a hr.1).symm
  have hF : fwdMap (fun r => w ((a : ℝ) + r) - w a) q = fwdMap (Ito.rpath (stgDrv R a)) q :=
    QuantumZipper.CharFunRhs.fwdMap_eq_of_eqOn hshift
  have hL : logDerivFwd (fun r => w ((a : ℝ) + r) - w a) q = logDerivFwd (Ito.rpath (stgDrv R a)) q :=
    QuantumZipper.CharFunRhs.logDerivFwd_eq_of_eqOn q.coe_nonneg hshift
  have hfa := QuantumZipper.fwdMap_add hwc hzK.1 a.coe_nonneg q.coe_nonneg
    (Ito.exists_isForwardSol_of_mem (by positivity) hzK)
  have hla := Sec5.Markov.logDerivFwd_add hwc a.coe_nonneg q.coe_nonneg hzK
  rw [hF] at hfa
  rw [hL] at hla
  -- both sides
  have hne : fwdMap w ((a : ℝ) + q) z ≠ 0 := by
    have h := hcsD.fwd_mem hy
    have e : (stgChart c R (a + q)).1 y = fwdMap w ((a : ℝ) + q) z := by
      show fwdMap w ((a + q : ℝ≥0) : ℝ) (c.1 y) = _
      rw [haq]
    rw [e] at h
    intro h0
    rw [h0] at h
    have h' : (0 : ℝ) < (0 : ℂ).im := h
    simp at h'
  have hS0 : Ito.rpath (stgDrv R (a + q)) 0 = 0 := by simp [Ito.rpath, stgDrv_zero]
  unfold stgMeanRX
  rw [Coupling.MartMeans2.couplingMean_zero κ hS0 U₀ (by
    show fwdMap w ((a + q : ℝ≥0) : ℝ) (c.1 y) ≠ 0
    rw [haq]
    exact hne)]
  have e1 : (stgChart c R a).1 y = fwdMap w a z := rfl
  have e2 : (stgChart c R (a + q)).1 y = fwdMap w ((a : ℝ) + q) z := by
    show fwdMap w ((a + q : ℝ≥0) : ℝ) (c.1 y) = _
    rw [haq]
  have e3 : (stgChart c R a).2.2 y = (logDerivFwd w a z).im + c.2.2 y := rfl
  have e4 : (stgChart c R (a + q)).2.2 y = (logDerivFwd w ((a : ℝ) + q) z).im + c.2.2 y := by
    show (logDerivFwd w ((a + q : ℝ≥0) : ℝ) (c.1 y)).im + c.2.2 y = _
    rw [haq]
  rw [e1, e2, e3, e4, hla, Complex.add_im, hU _ (by rw [← e2]; exact hcsD.fwd_mem hy)]
  unfold couplingMean
  rw [← hfa]
  ring


/-- **The stage-start mean of two relative drivers agreeing up to the stage start is the same.** -/
theorem stgMeanRX_zero_congr (κ x : ℝ) (s : ℝ≥0) (rec : RecData) {R R' : ℝ≥0 → ℝ} (hR : Continuous R) (hR0 : R 0 = 0)
    (hR' : Continuous R') {a : ℝ≥0} (h : ∀ u ≤ a, R u = R' u) (U u₀ : ℂ → ℝ) (σa : ℝ) {y : ℂ}
    (hy : y ∈ ((stgChart (GW2Rz.relChartX x s rec) R a).dom : Set ℂ)) :
    stgMeanRX κ x s rec R a 0 U u₀ σa y = stgMeanRX κ x s rec R' a 0 U u₀ σa y := by
  have hc := stgChart_congr (GW2Rz.relChartX x s rec) hR hR' h
  have hconf := isConformal_stgChart (GW2Rz.isConformal_relChartX x s rec) hR hR0 a
  have hH := hconf.fwd_mem hy
  have h0 : (stgChart (GW2Rz.relChartX x s rec) R a).1 y ≠ 0 := fun h0 => by
    rw [h0] at hH
    exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from hH)
  have hw : Ito.rpath (stgDrv R a) 0 = 0 := by simp [Ito.rpath, stgDrv_zero]
  have hw' : Ito.rpath (stgDrv R' a) 0 = 0 := by simp [Ito.rpath, stgDrv_zero]
  unfold stgMeanRX
  rw [Coupling.MartMeans2.couplingMean_zero κ hw U h0, ← hc,
    Coupling.MartMeans2.couplingMean_zero κ hw' U h0]


/-- **At clock `0`, raising the harmonic function and the offset by the same constant keeps the stage mean**, on the
stage chart's domain. -/
theorem stgMeanRX_zero_add_const (κ x : ℝ) (s : ℝ≥0) (rec : RecData) {R : ℝ≥0 → ℝ} (hR : Continuous R) (hR0 : R 0 = 0)
    (a₀ : ℝ≥0) {U U' u₀ : ℂ → ℝ} {σ k : ℝ} (hU : ∀ z ∈ H, U z = U' z + k) {y : ℂ}
    (hy : y ∈ ((stgChart (GW2Rz.relChartX x s rec) R a₀).dom : Set ℂ)) :
    stgMeanRX κ x s rec R a₀ 0 U u₀ (σ + k) y = stgMeanRX κ x s rec R a₀ 0 U' u₀ σ y := by
  have hconf := isConformal_stgChart (GW2Rz.isConformal_relChartX x s rec) hR hR0 a₀
  have hH := hconf.fwd_mem hy
  have h0 : (stgChart (GW2Rz.relChartX x s rec) R a₀).1 y ≠ 0 := fun h0 => by
    rw [h0] at hH
    exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from hH)
  have hw : Ito.rpath (stgDrv R a₀) 0 = 0 := by simp [Ito.rpath, stgDrv_zero]
  unfold stgMeanRX
  rw [Coupling.MartMeans2.couplingMean_zero κ hw U h0, Coupling.MartMeans2.couplingMean_zero κ hw U' h0, hU _ hH]
  ring

/-- **The prefix version's stage-start pairing is the current instance's.** -/
theorem integral_stgMeanRX_zero_conv (κ x : ℝ) (s : ℝ≥0) (rec : RecData) {R R' : ℝ≥0 → ℝ} (hR : Continuous R) (hR0 : R
    0 = 0)
    (hR' : Continuous R') {a₀ : ℝ≥0} (hRR : ∀ u ≤ a₀, R' u = R u) {U Uw u₀ : ℂ → ℝ} {σ k : ℝ}
    (hU : ∀ z ∈ H, U z = Uw z + k) (φ : LQGMetric.TestOn upperHalfPlaneOpens)
    (hφ : tsupport φ ⊆ ((stgChart (GW2Rz.relChartX x s rec) R a₀).dom : Set ℂ)) :
    ∫ z, stgMeanRX κ x s rec R' a₀ 0 Uw u₀ σ z * φ z = ∫ z, stgMeanRX κ x s rec R a₀ 0 U u₀ (σ + k) z * φ z := by
  congr 1
  funext z
  by_cases hz : z ∈ tsupport φ
  · have hz' := hφ hz
    rw [stgMeanRX_zero_add_const κ x s rec hR hR0 a₀ hU hz',
      stgMeanRX_zero_congr κ x s rec hR hR0 hR' (fun u hu => (hRR u hu).symm) Uw u₀ σ hz']
  · rw [image_eq_zero_of_notMem_tsupport hz, mul_zero, mul_zero]

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

/-- **The complement of the corrected union below the cap is the domain of the version's moved relative chart**
(root `x ≥ 0`, on the history's success and the good set). -/
theorem ae_compl_eq_dom_rootX (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    (hx : 0 ≤ rootPt r.1) (hs0 : 0 < c.s) {GT : Set Ω}
    (hGT : ∀ ω ∈ GT, PhysGoodX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α ω)
    {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hv : IsRelVersionX (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α R V) :
    ∀ᵐ ω ∂c.P, ω ∈ GT → oldSuccess c r l ω → ∀ u : ℝ≥0,
      min (physClockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT (historyTime c r l + u) ω) (V ω) < V ω →
      H \ schedUnionX c r l a (historyTime c r l) u ω =
        ((stgChart (relChartX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω)) (fun q => R q ω)
        (capA (rootPt r.1) c.s c.W c.ζ (schedW c r l a) GT V (historyTime c r l) u ω)).dom : Set ℂ) := by
  filter_upwards [ae_shape_rootX c r l a hx hs0 hGT hv] with ω h hωG hsucc u hlt
  rw [h hωG hsucc u hlt, GW2Rd.dom_stgChart (isConformal_relChartX _ _ _) (hv.2.1 ω) (hv.2.2.1 ω)]

variable [StandardBorelSpace Ω]

/-- **The Claim(k) step**: the prefix's pairing at the entry's end gives the history's stage-start pairing. -/
theorem claim_of_prefix_pairX (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (e : EntryIdx c.Θ c.Q) (l' : List (EntryIdx c.Θ c.Q))
    (a a' : ℕ)
    (hord : (historyProgram c r (e :: l')).Pairwise (fun p q => p.2 < q.2))
    (hord' : (historyProgram c r l').Pairwise (fun p q => p.2 < q.2))
    (hθ : candidateAngle c r a' = (e.1 : ℝ))
    (hcap : historyTime c r (e :: l') ≤ historyTime c r l' + candidateCap c r a')
    (δ : ℝ≥0) (hδ : historyTime c r l' + δ = historyTime c r (e :: l'))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension c.b c.jumps u₀)
    {G : Set Ω} (hGS : ∀ ω ∈ G, oldSuccess c r (e :: l') ω)
    {R : ℝ≥0 → Ω → ℝ} {a₀' q : Ω → ℝ≥0} {U' : Ω → ℂ → ℝ} {σa' : ℝ} {Wd : Ω → BoundaryWord}
    (hP : ∀ g : Ω → DistOn upperHalfPlaneOpens,
      IsLocalSetMean (schedUnionX c r l' a' (historyTime c r l') δ) (centredField c.h u₀) c.P g → ∀ φ : TestOn
          upperHalfPlaneOpens,
      ∀ᵐ ω ∂c.P, ω ∈ G → tsupport φ ⊆ H \ schedUnionX c r l' a' (historyTime c r l') δ ω →
        g ω φ = ∫ z, stgMeanRX c.κ (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω) (fun u => R u ω) (a₀' ω) (q ω : ℝ) (U' ω) u₀
            σa' z *
          φ z)
    (hsamp : ∀ᵐ ω ∂c.P, ω ∈ G → Continuous (fun u => R u ω) ∧ R 0 ω = 0 ∧
      (∀ z ∈ H, (Wd ω).mean z = U' ω z + (specOffset c.κ - σa')) ∧
      H \ schedUnionX c r (e :: l') a (historyTime c r (e :: l')) 0 ω ⊆
        ((stgChart (relChartX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω)) (fun u => R u ω)
          (a₀' ω + q ω)).dom : Set ℂ))
    (g₀ : Ω → DistOn upperHalfPlaneOpens)
    (hg₀ : IsLocalSetMean (schedUnionX c r (e :: l') a (historyTime c r (e :: l')) 0) (centredField c.h u₀) c.P g₀)
    (φ : TestOn upperHalfPlaneOpens) :
    ∀ᵐ ω ∂c.P, ω ∈ G → tsupport φ ⊆ H \ schedUnionX c r (e :: l') a (historyTime c r (e :: l')) 0 ω →
      g₀ ω φ = ∫ z, stgMeanRX c.κ (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω) (fun u => R u ω) (a₀' ω + q ω) 0
        (Wd ω).mean u₀ (specOffset c.κ) z * φ z := by
  obtain ⟨g, hg⟩ := exists_mean_schedUnionX h12 h13 c r l' a' hord' hu₀ δ
  have hX := ae_mean_eq_consX h12 h13 c r e l' a a' hord hord' hθ hcap δ hδ hu₀ hg hg₀
  filter_upwards [hP g hg φ, hX, hsamp, Gm.ae_futureJoined_trace h13 c r] with ω h1 h2 h3 h4 hG hsupp
  obtain ⟨hRc, hR0, hW, hdom⟩ := h3 hG
  have hS := hGS ω hG
  have hsub : H \ schedUnionX c r (e :: l') a (historyTime c r (e :: l')) 0 ω ⊆ H \ schedUnionX c r l' a' (historyTime
      c r l') δ ω := by
    refine sdiff_subset_sdiff_right (schedUnionX_cons_subset c r e l' a a' δ ω fun hs => ?_)
    exact schedUnionX_cons_eq c r e l' a a' ω hord hord' hs (h4 (e :: l') a hs).1
      (h4 l' a' (oldSuccess_of_cons c r e l' ω hs)).1 hθ hcap δ hδ
  rw [← h2 hS, h1 hG (hsupp.trans hsub)]
  congr 1
  funext z
  by_cases hz : z ∈ tsupport φ
  · rw [stgMeanRX_restart c.κ (rootPt r.1) c.s _ hRc hR0 (a₀' ω) (q ω) (U₀ := (Wd ω).mean) (σa := specOffset c.κ)
      (fun z hz => hW z hz) (hdom (hsupp hz))]
  · rw [image_eq_zero_of_notMem_tsupport hz, mul_zero, mul_zero]

end InteractingSLE.Theorem14.GW2Kx
