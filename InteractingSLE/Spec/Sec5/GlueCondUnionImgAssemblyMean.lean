/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.GlueCondUnionImgAssembly
import InteractingSLE.Spec.Sec5.GlueCondUnionImgInf
import InteractingSLE.Spec.Sec5.CrossCondMartWeights
import InteractingSLE.WangWu.ImgChartConstIdent
import InteractingSLE.WangWu.PrefixLocalMean
import InteractingSLE.Spec.Sec5.CrossCondMartMarks

/-!
# G3 (ii), Proposition 4.9 direction: the mean identification `MeanIdent49Statement cL6 cR6`

Packet PROVE-GLUECOND10 (PROVE-GLUECOND8's "What remains" 3; PROVE-GLUECOND7's named input). On the glued space of a
flow line and a counterflow line (`Prop411Q.CfGlueAE` setting), at a counterflow time `s > 0` and a flow time `t > 0`
before contact, the conditional mean of the centred field given the germ of `A_t ∪ G_s` and both stopped histories is
the chart mean of the killed image word at the image time `σ(t)`, with the junction weights `κ − 4 − Σρ_L`,
`κ/2 − 2 − Σρ_R` (ruling R57):

* `meanCan_img49_eq`: the explicit mean of the killed image word at `σ(t)` is the coupling mean of any continuous
  driver `W′` of the image hull, with the flowed image marks (the general-`κ` form of PROVE-WW-B19's
  `meanCan_img_eq_chartMean`);
* **`meanIdent49Statement`**: `MeanIdent49Statement cL6 cR6` — the local-set mean of `A_t ∪ G_s` is the conditional
  mean given the germs and the marks (`WangWu.IsLocalSetMean.ae_eq_condExp_germSigma_sup`), its harmonic
  representative has the boundary values of the image word in the image chart (`GlueImg.eqOn_imgChart`, from
  `GlueCond.ae_union_mean_cfGlue`, `GlueCond.ae_tendsto_union_sub_cfMean_cobounded` and
  `Sec6.ae_eqOn_component_of_tendsto_global`), and the chart mean integrates it against `φ`;
* **`imageWord49FiltCStatement`**: hence PROVE-GLUECOND7's `ImageWord49FiltCStatement` (the image word's martingale
  clause with the corrected junction weights, ruling R57).

R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any `*_of_param`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology Complex
open QuantumZipper (H fwdHull fwdMap fwdMapInv logDerivFwd chiC)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec5.CrossCond

open WangWu hiding ratPt exists_ratPt_dist_lt
open WangWu.ImgWord LawUnique GlueCond Cond44Ref CfRegQ Prop411Q WholeField LocalSets
open ImgDrv MartChar MartChar.RealFlow
open Sec7.Lemma71C (capClock)

namespace Word49

/-! ### The killed image word at the image time `σ(t)` -/

section Img

variable {Ω : Type*} {s : ℝ≥0} {ζ : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ} {E : Set (Ω × HistorySpace 0 0)}
  {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}

/-- **The explicit mean of the killed image word at `σ(t)` is the coupling mean of any driver of the image hull**:
if `W′` is a continuous driver with a simple proper trace whose hull at `T` is `γ((0, t])` (the image of the flow
prefix), then `T = σ(t)` and the mean `meanCan` of the image word at `T` is
`meanHarmonic(flowed image marks) ∘ f′_T − χ Im L′_T`. -/
theorem meanCan_img49_eq (hEg : ∀ p ∈ E, IsGood49 s ζ W p) {p : Ω × HistorySpace 0 0} (hp : p ∈ E) {t : ℝ}
    (ht : t ∈ gPre s ζ W E p) (ht0 : 0 < t) {W' : ℝ → ℝ} (hW' : Continuous W') (hW'0 : W' 0 = 0)
    {η' : ℝ → ℂ} (hη' : IsLoewnerTrace W' η') (hη'p : IsProperArc η') {T : ℝ} (hT : 0 < T)
    (hK : fwdHull W' T = gCurve s ζ W E p '' Ioc 0 t) (ρL' : Fin (nL + 1) → ℝ) (ρR' : Fin (nR + 1) → ℝ) :
    T = capClock (gCurve s ζ W E p) t ∧ ∀ y : ℂ,
      Coupling.meanCan κ ρL' ρR' (fun r => imgW s ζ W E r p) (fun i r => imgVL xL s ζ W E i r p)
        (fun j r => imgVR xR s ζ W E j r p) T.toNNReal y =
      Ito.meanHarmonic κ ρL' ρR'
        (fun i => -rightImg (fun r => -W' r) (-GlueImg.imgMarkL xL (cfDrv0 s p.2) s i) T - W' T)
        (fun j => rightImg W' (GlueImg.imgMarkR xR (cfDrv0 s p.2) s j) T - W' T) (fwdMap W' T y) -
        chiC κ * (logDerivFwd W' T y).im := by
  set γ := gCurve s ζ W E p with hγdef
  set P := gPre s ζ W E p with hPdef
  have hγ : IsKilledArc γ P := isKilledArc_gCurve hEg p
  obtain ⟨hTc, hEqW⟩ := hγ.eqOn_chainDrv_of_fwdHull_eq ht ht0 hW' hW'0 hη' hη'p hT hK
  refine ⟨hTc, fun y => ?_⟩
  have hT' : ((T.toNNReal : ℝ≥0) : ℝ) = T := Real.coe_toNNReal _ hT.le
  have hlt : ((T.toNNReal : ℝ≥0) : WithTop ℝ≥0) < kLife γ P := by
    have := hγ.lt_kLife ht
    rwa [← hTc] at this
  obtain ⟨-, hkW⟩ := hγ.kW_eq_chainDrv ht
  have hpath : EqOn (kPath γ P) W' (Icc 0 T) := fun r hr => by
    rw [kPath, hkW r (hTc ▸ hr), hEqW hr]
  have hpathn : EqOn (fun r => -kPath γ P r) (fun r => -W' r) (Icc 0 T) := fun r hr => by
    simp only [hpath hr]
  have hWT : imgW s ζ W E T.toNNReal p = W' T := hpath ⟨hT.le, le_rfl⟩
  have hVL : ∀ i, imgVL xL s ζ W E i T.toNNReal p - imgW s ζ W E T.toNNReal p =
      -rightImg (fun r => -W' r) (-GlueImg.imgMarkL xL (cfDrv0 s p.2) s i) T - W' T := fun i => by
    rw [imgVL, kVL_of_lt _ _ hlt, kVLr, kImg_eq (show Continuous fun r => -W' r from hW'.neg) hpathn hT'.le, hWT,
      hT', gXL_of_mem hp]
  have hVR : ∀ j, imgVR xR s ζ W E j T.toNNReal p - imgW s ζ W E T.toNNReal p =
      rightImg W' (GlueImg.imgMarkR xR (cfDrv0 s p.2) s j) T - W' T := fun j => by
    rw [imgVR, kVR_of_lt _ _ hlt, kVRr, kImg_eq hW' hpath hT'.le, hWT, hT', gXR_of_mem hp]
  have hrp : EqOn (Ito.rpath fun r => imgW s ζ W E r p) W' (Icc 0 T) := fun r hr => hpath hr
  have hfwd : fwdMap (Ito.rpath fun r => imgW s ζ W E r p) (T.toNNReal : ℝ) y = fwdMap W' T y := by
    rw [hT']
    exact Ito.fwdMap_congr_of_eqOn hrp
  have hlog : logDerivFwd (Ito.rpath fun r => imgW s ζ W E r p) (T.toNNReal : ℝ) y = logDerivFwd W' T y := by
    rw [hT']
    exact Ito.logDerivFwd_congr_of_eqOn hrp hT.le le_rfl
  rw [Coupling.meanCan, hfwd, hlog]
  congr 2
  · funext i; exact hVL i
  · funext j; exact hVR j

end Img

/-! ### Per-sample regularity -/

section Sample

/-- The hull of a continuous driver is relatively closed in `ℍ`. -/
theorem closure_inter_H_subset_fwdHull {w : ℝ → ℝ} (hw : Continuous w) {t : ℝ} (ht : 0 ≤ t) :
    closure (fwdHull w t) ∩ H ⊆ fwdHull w t := by
  rintro z ⟨hz, hzH⟩
  by_contra hzA
  obtain ⟨a, ⟨-, haA⟩, haA'⟩ := (_root_.mem_closure_iff.1 hz) (H \ fwdHull w t)
    (QuantumZipper.FwdHolo.isOpen_compl_fwdHull hw ht) ⟨hzH, hzA⟩
  exact haA haA'

/-- A simple proper trace avoids `ℝ ∖ {0}` up to closure. -/
theorem ofReal_notMem_closure_of_isProperArc {w : ℝ → ℝ} {α : ℝ → ℂ} (hα : IsLoewnerTrace w α)
    (hαp : IsProperArc α) {t : ℝ} (ht : 0 ≤ t) : ∀ x : ℝ, x ≠ 0 → (x : ℂ) ∉ closure (fwdHull w t) := by
  intro x hx hmem
  obtain ⟨ρ, hρ, hd⟩ := GlueImg.exists_ball_disjoint_fwdHull_of_isProperArc hα hαp ht hx
  obtain ⟨b, hb, hbd⟩ := Metric.mem_closure_iff.1 hmem ρ hρ
  exact disjoint_left.1 hd (show b ∈ ball (x : ℂ) ρ by rw [mem_ball, dist_comm]; exact hbd) hb

/-- **The closures of `K′_s` and `R(A)` are disjoint** when `A` and `R(K′_s)` are (`A` a hull avoiding `ℝ ∖ {0}` up to
closure, so `R(A)` is closed in `ℂ` and lies in `ℍ`, where `closure K′_s` is `K′_s`). -/
theorem disjoint_closure_fwdHull_negInv {Wα ω : ℝ → ℝ} (hWα : Continuous Wα) {t : ℝ} (ht : 0 ≤ t)
    (hKt : ∀ x : ℝ, x ≠ 0 → (x : ℂ) ∉ closure (fwdHull Wα t)) (hω : Continuous ω) {s : ℝ} (hs : 0 ≤ s)
    (hdisj : Disjoint (fwdHull Wα t) (negInv '' fwdHull ω s)) :
    Disjoint (closure (fwdHull ω s)) (closure (negInv '' fwdHull Wα t)) := by
  have hA := isHPHull_fwdHull hWα ht
  have hcl : IsClosed (negInv '' fwdHull Wα t) :=
    GlueCond.isClosed_image_negInv_of_closure hA.1 hA.2.1 (closure_inter_H_subset_fwdHull hWα ht) hKt
  rw [hcl.closure_eq]
  refine disjoint_left.2 fun z hz ⟨a, ha, e⟩ => ?_
  have hzH : z ∈ H := e ▸ negInv_mem_H (hA.1 ha)
  have hzK : z ∈ fwdHull ω s := closure_inter_H_subset_fwdHull hω hs ⟨hz, hzH⟩
  refine disjoint_left.1 hdisj ha ⟨z, hzK, ?_⟩
  rw [← e, WangWu.negInv_negInv]

variable {y : HistorySpace 0 0}

/-- On a good history the stopped driver read through `Ito.rpath ∘ regPath` is `cfDrv0`. -/
theorem rpath_regPath_cfStop_eq (hy : y ∈ goodCfSet) (s : ℝ≥0) :
    Ito.rpath (Sec4.regPath (cfStop s y)) = cfDrv0 s y := by
  have h0 := (CfRegQ.reg_of_mem_goodCfSet hy).2.2.1
  rw [CfRegQ.cfDrv_eq_hDrv] at h0
  simp only [Real.toNNReal_zero] at h0
  funext r
  simp only [cfDrv0, Ito.rpath, regPath_cfStop_of_mem_goodCfSet hy, Real.toNNReal_zero, zero_le, min_eq_left,
    h0, sub_zero]

theorem eqOn_cfDrv0_cfDrv (hy : y ∈ goodCfSet) (s : ℝ≥0) : ∀ r ∈ Icc (0 : ℝ) s, cfDrv0 s y r = cfDrv y r :=
  fun _ hr => cfDrv0_eq_cfDrv hy hr

theorem fwdHull_cfDrv0 (hy : y ∈ goodCfSet) (s : ℝ≥0) : fwdHull (cfDrv0 s y) s = fwdHull (cfDrv y) s :=
  YuanCorollary13.fwdHull_eq_of_eqOn_Icc (continuous_cfDrv0 s y) (CfRegQ.reg_of_mem_goodCfSet hy).2.1
    s.coe_nonneg (eqOn_cfDrv0_cfDrv hy s)

theorem revChart_cfDrv0 (hy : y ∈ goodCfSet) (s : ℝ≥0) : revChart (cfDrv0 s y) s = revChart (cfDrv y) s := by
  funext z
  simp only [revChart]
  rw [Ito.fwdMap_congr_of_eqOn (fun r hr => eqOn_cfDrv0_cfDrv hy s r hr)]

/-- The counterflow chart's inverse map at time `s` has boundary limits on a good history. -/
theorem hasBdryLimits_cfDrv0 (hy : y ∈ goodCfSet) (s : ℝ≥0) : HasBdryLimits (fwdMapInv (cfDrv0 s y) s) := by
  obtain ⟨-, hc, h0, htr⟩ := CfRegQ.reg_of_mem_goodCfSet hy
  have hB := htr.hasBdryLimits hc h0 s.coe_nonneg
  intro x hx
  obtain ⟨p, hp⟩ := hB x hx
  refine ⟨p, hp.congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact (LP.fwdMapInv_eq_of_eqOn_Icc (continuous_cfDrv0 s y) hc (cfDrv0_zero s y) h0 s.coe_nonneg
    (fun r hr => eqOn_cfDrv0_cfDrv hy s r hr) hz).symm

/-- On a good hitting history `closure K′_s` meets `ℝ` only at `0`. -/
theorem eq_zero_of_mem_closure_cfDrv0 (hy : y ∈ goodHitSet) (s : ℝ≥0) :
    ∀ z ∈ closure (fwdHull (cfDrv0 s y) s), z.im = 0 → z = 0 := by
  rw [fwdHull_cfDrv0 hy.1 s]
  exact (isClosed_negInv_fwdHull_of_mem_goodHitSet hy s.coe_nonneg).2

end Sample

/-! ### The chart mean on one good sample -/

section OneSample

open GlueImg (imgMarkL imgMarkR imgRhoL imgRhoR cfDataAt cfMarkL cfMarkR)
open Sec7.StripSysField

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {s : ℝ≥0} {E : Set (Ω × HistorySpace 0 0)}

/-- **The chart mean of the image word on one good sample** (deterministic). On a good glued sample `p` (the flow
line a simple proper arc, a good hitting counterflow history with strict junction gaps), at a flow time `t > 0` before
contact, given the image chain of `A_t` in the chart `Ψ` and a function `w` with the boundary limits of the union mean
(flow side, counterflow side, `∞`) and the uniqueness statement of Aux. 28 on `C = ℍ ∖ (A_t ∪ G_s)`: for every test
function `φ` supported in `C`, the chart mean of the killed image word at `σ(t)` (junction weights `cL6`, `cR6`) is
`∫ (w + 𝔥₀) φ`. -/
theorem chartMean_eq_integral_of_sample (hκ : 0 < κ) (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j)
    (hEg : ∀ p ∈ E, IsGood49 s ζ W p) {p : Ω × HistorySpace 0 0} (hp : p ∈ E) {t : ℝ≥0} (ht : 0 < t)
    (htP : (t : ℝ) ∈ gPre s ζ W E p) {Wα : ℝ → ℝ} (hα : IsLoewnerTrace Wα (seedLine ζ W p.1))
    (hWα : Continuous Wα) (hWα0 : Wα 0 = 0)
    (hA : hullAt t (killedHistory W VL VR ζ p.1) = seedLine ζ W p.1 '' Ioc 0 t) (hy : p.2 ∈ goodHitSet)
    (himg : ∀ s : ℝ, 0 ≤ s → ∀ t : ℝ, 0 < t →
      Disjoint (seedLine ζ W p.1 '' Ioc 0 t) (negInv '' fwdHull (cfDrv p.2) s) →
      ∃ W' : ℝ → ℝ, Continuous W' ∧ W' 0 = 0 ∧ ∃ T : ℝ, 0 < T ∧ ∃ η' : ℝ → ℂ, IsLoewnerTrace W' η' ∧
        IsProperArc η' ∧ fwdHull W' T = revChart (cfDrv p.2) s '' (seedLine ζ W p.1 '' Ioc 0 t) ∧
          η' T = revChart (cfDrv p.2) s (seedLine ζ W p.1 t))
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) u₀)
    {u' : ℂ → ℝ}
    (hu' : IsBoundedHarmonicExtension
      (cfWordData κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(π / 2 * chiC κ)) (forceJumpFinset xL xR))
      (cfWordJumps κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(π / 2 * chiC κ)) (forceJumpFinset xL xR)) u')
    {uA : ℂ → ℝ}
    (huA : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR
        (fun i => -rightImg (fun r => -Wα r) (-xL i) t - Wα t) (fun j => rightImg Wα (xR j) t - Wα t))
      (forceJumpSet (fun i => -rightImg (fun r => -Wα r) (-xL i) t - Wα t)
        (fun j => rightImg Wα (xR j) t - Wα t)) uA)
    {w : ℂ → ℝ}
    (hwFl : ∀ z₀ ∈ hullAt t (killedHistory W VL VR ζ p.1) ∪ {z : ℂ | z.im = 0},
      (∃ r > 0, cfHullQ s p.2 ∩ ball z₀ r ⊆ hullAt t (killedHistory W VL VR ζ p.1)) →
      Tendsto (fun z => w z - (couplingMean κ Wα t uA z - u₀ z))
        (𝓝[H \ (hullAt t (killedHistory W VL VR ζ p.1) ∪ cfHullQ s p.2)] z₀) (𝓝 0))
    (hwG : ∀ z₀ ∈ cfHullQ s p.2 ∪ {z : ℂ | z.im = 0},
      (∃ r > 0, hullAt t (killedHistory W VL VR ζ p.1) ∩ ball z₀ r ⊆ cfHullQ s p.2) →
      Tendsto (fun z => w z - cfMeanQ κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(π / 2 * chiC κ))
          (forceJumpFinset xL xR) u' s p.2 z)
        (𝓝[H \ (hullAt t (killedHistory W VL VR ζ p.1) ∪ cfHullQ s p.2)] z₀) (𝓝 0))
    (hwInf : Tendsto (fun z => w z - cfMeanQ κ (fun x => forceBoundaryData κ ρL ρR xL xR x + -(π / 2 * chiC κ))
          (forceJumpFinset xL xR) u' s p.2 z)
      (Bornology.cobounded ℂ ⊓ 𝓟 (H \ (hullAt t (killedHistory W VL VR ζ p.1) ∪ cfHullQ s p.2))) (𝓝 0))
    (huniq : ∀ z₀ ∈ H \ (hullAt t (killedHistory W VL VR ζ p.1) ∪ cfHullQ s p.2),
      ∀ (f φc : ℂ → ℂ) (G L : ℂ → ℝ) (E : Set ℂ),
      SupercriticalConformalCovariance.IsConformalBijection f (ball 0 1)
        (connectedComponentIn (H \ (hullAt t (killedHistory W VL VR ζ p.1) ∪ cfHullQ s p.2)) z₀) →
      SupercriticalConformalCovariance.IsConformalBijection φc
        (connectedComponentIn (H \ (hullAt t (killedHistory W VL VR ζ p.1) ∪ cfHullQ s p.2)) z₀)
        {w : ℂ | 0 < w.im} →
      InnerProductSpace.HarmonicOnNhd G {w : ℂ | 0 < w.im} →
      (∃ M, ∀ w : ℂ, 0 < w.im → |G w| ≤ M) →
      ContinuousOn L (connectedComponentIn (H \ (hullAt t (killedHistory W VL VR ζ p.1) ∪ cfHullQ s p.2)) z₀) →
      (∀ z ∈ connectedComponentIn (H \ (hullAt t (killedHistory W VL VR ζ p.1) ∪ cfHullQ s p.2)) z₀,
        deriv φc z = ‖deriv φc z‖ * exp (L z * I)) →
      E.Finite →
      (∀ q ∈ sphere (0 : ℂ) 1, q ∉ E →
        Tendsto (fun ζ => (w (f ζ) + u₀ (f ζ)) - (G (φc (f ζ)) - chiC κ * L (f ζ))) (𝓝[ball 0 1] q) (𝓝 0)) →
      ∀ z ∈ connectedComponentIn (H \ (hullAt t (killedHistory W VL VR ζ p.1) ∪ cfHullQ s p.2)) z₀,
        w z + u₀ z = G (φc z) - chiC κ * L z)
    {φ : TestOn upperHalfPlaneOpens}
    (hφ : tsupport φ ⊆ H \ (hullAt t (killedHistory W VL VR ζ p.1) ∪ cfHullQ s p.2)) :
    Sec7.Lemma71D.chartMean κ (jwL cL6 κ ρL) (jwR cR6 κ ρR) (fun r => imgW s ζ W E r p)
        (fun i r => imgVL xL s ζ W E i r p) (fun j r => imgVR xR s ζ W E j r p) (cfChart s p.2)
        (2 * π * chiC κ) (chiC κ) φ (capClock (gCurve s ζ W E p) t).toNNReal =
      ∫ z, (w z + u₀ z) * φ z := by
  set ω := cfDrv0 s p.2 with hωdef
  have hω : Continuous ω := continuous_cfDrv0 s p.2
  have hω0 : ω 0 = 0 := cfDrv0_zero s p.2
  have ht' : (0 : ℝ) < t := NNReal.coe_pos.2 ht
  obtain ⟨hαp, hGc, hjL, hjR, hGeq⟩ := hEg p hp
  have hAfwd : hullAt t (killedHistory W VL VR ζ p.1) = fwdHull Wα t := by
    rw [hA, fwdHull_eq_image_Ioc hα hαp t.coe_nonneg]
  have hpre : (t : ℝ) ∈ preContact (seedLine ζ W p.1) (cfHullQ s p.2) := gPre_of_mem hp ▸ htP
  have hdisj : Disjoint (fwdHull Wα t) (negInv '' fwdHull ω s) := by
    rw [fwdHull_eq_image_Ioc hα hαp t.coe_nonneg, ← hGeq]
    refine disjoint_left.2 ?_
    rintro _ ⟨u, hu, rfl⟩ hG
    exact hpre.2 u ⟨hu.1.le, hu.2⟩ hG
  have hKt := ofReal_notMem_closure_of_isProperArc hα hαp t.coe_nonneg
  have hdis := disjoint_closure_fwdHull_negInv hWα t.coe_nonneg hKt hω s.coe_nonneg hdisj
  have hB := hasBdryLimits_cfDrv0 hy.1 s
  have hKs := eq_zero_of_mem_closure_cfDrv0 hy s
  -- the image chain
  have hd' : Disjoint (seedLine ζ W p.1 '' Ioc 0 t) (negInv '' fwdHull (cfDrv p.2) s) := by
    rw [← fwdHull_cfDrv0 hy.1 s, ← fwdHull_eq_image_Ioc hα hαp t.coe_nonneg]; exact hdisj
  obtain ⟨W', hW', hW'0, T, hT, η', hη', hη'p, hK'', htip⟩ := himg s s.coe_nonneg t ht' hd'
  rw [← revChart_cfDrv0 hy.1 s] at hK'' htip
  have hK' : fwdHull W' T = revChart ω s '' fwdHull Wα t := by
    rw [hK'', fwdHull_eq_image_Ioc hα hαp t.coe_nonneg]
  -- the counterflow mean in the chart `Ψ`
  set bd : ℝ → ℝ := fun x => forceBoundaryData κ ρL ρR xL xR x + -(π / 2 * chiC κ) with hbd
  set v := cfU κ bd (forceJumpFinset xL xR) s (cfStop s p.2) with hvdef
  have hv : IsBoundedHarmonicExtension (cfDataAt κ bd (forceJumpFinset xL xR) ω s)
      (forceJumpSet (cfMarkL κ bd (forceJumpFinset xL xR) ω s) (cfMarkR κ bd (forceJumpFinset xL xR) ω s)) v := by
    have h1 := isBoundedHarmonicExtension_cfU κ bd (forceJumpFinset xL xR) s (cfStop s p.2)
    have e := rpath_regPath_cfStop_eq hy.1 s
    have hL : cfPosL κ bd (forceJumpFinset xL xR) (Sec4.regPath (cfStop s p.2)) s =
        cfMarkL κ bd (forceJumpFinset xL xR) ω s := by
      funext i; rw [hωdef, ← e]; simp [cfPosL, cfMarkL, Ito.rpath]
    have hR : cfPosR κ bd (forceJumpFinset xL xR) (Sec4.regPath (cfStop s p.2)) s =
        cfMarkR κ bd (forceJumpFinset xL xR) ω s := by
      funext i; rw [hωdef, ← e]; simp [cfPosR, cfMarkR, Ito.rpath]
    rw [hL, hR] at h1
    exact h1
  set mG : ℂ → ℝ := fun z => cfMeanQ κ bd (forceJumpFinset xL xR) u' s p.2 z + u₀ z - π / 2 * chiC κ with hmG
  set M : ℂ → ℝ := fun z => w z + u₀ z - π / 2 * chiC κ with hM
  have hId : ∀ z ∈ H \ negInv '' fwdHull ω s, mG z + chiC κ * (GlueImg.logDerivPsi ω s z).im =
      GlueImg.retMean κ v (revChart ω s z) := by
    intro z hz
    have h1 := cfMeanQ_add_eq_retMean_add hκ ρL ρR xL xR hu₀ hu' s p.2 (z := z) (hGeq ▸ hz)
    rw [rpath_regPath_cfStop_eq hy.1 s] at h1
    simp only [hmG]
    linarith
  rw [hAfwd, hGeq] at hwFl hwG hwInf huniq hφ
  have hG : ∀ z₀ ∈ negInv '' fwdHull ω s ∪ {z : ℂ | z.im = 0},
      (∃ r > 0, fwdHull Wα t ∩ ball z₀ r ⊆ negInv '' fwdHull ω s) →
      Tendsto (fun z => M z - mG z) (𝓝[H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s)] z₀) (𝓝 0) := by
    intro z₀ hz₀ hr
    refine (hwG z₀ hz₀ hr).congr fun z => ?_
    simp only [hM, hmG]; ring
  have hInf : Tendsto (fun z => M z - mG z)
      (Bornology.cobounded ℂ ⊓ 𝓟 (H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s))) (𝓝 0) := by
    refine hwInf.congr fun z => ?_
    simp only [hM, hmG]; ring
  have hFl : ∀ v : ℝ, 0 < v → v < t → Tendsto (fun z => M z + π / 2 * chiC κ -
      (uA (fwdMap Wα t z) - chiC κ * (logDerivFwd Wα t z).im))
      (𝓝[H \ (fwdHull Wα t ∪ negInv '' fwdHull ω s)] (seedLine ζ W p.1 v)) (𝓝 0) := by
    intro v hv0 hvt
    have hαv : seedLine ζ W p.1 v ∈ fwdHull Wα t := by
      rw [fwdHull_eq_image_Ioc hα hαp t.coe_nonneg]; exact ⟨v, ⟨hv0, hvt.le⟩, rfl⟩
    have hαvG : seedLine ζ W p.1 v ∉ negInv '' fwdHull ω s := fun h => disjoint_left.1 hdisj hαv h
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hGc.isOpen_compl _ hαvG
    refine (hwFl _ (Or.inl hαv) ⟨r, hr, fun z hz => absurd hz.1 (hball hz.2)⟩).congr fun z => ?_
    simp only [hM, couplingMean]; ring
  -- the bounded harmonic extension of the image word at `T`
  obtain ⟨u, hu⟩ := exists_isBoundedHarmonicExtension_forceBoundaryData κ (jwL cL6 κ ρL) (jwR cR6 κ ρR)
    (fun i => -rightImg (fun r => -W' r) (-imgMarkL xL ω s i) T - W' T)
    (fun j => rightImg W' (imgMarkR xR ω s j) T - W' T)
  have hid := GlueImg.eqOn_imgChart ρL ρR hα hαp hWα hWα0 ht' hKt hκ hω hω0 s.coe_nonneg hB hKs hjL hjR hGc hdisj
    hdis hxL hxR hv hG hInf hId hW' hW'0 hη' hη'p hT hK' htip hu huA hFl (w := w) (u₀ := u₀)
    (fun z => by simp only [hM]; ring) huniq
  -- the killed image word at `σ(t)`
  have hKγ : fwdHull W' T = gCurve s ζ W E p '' Ioc 0 t := by
    rw [gCurve_of_mem hp, hK', fwdHull_eq_image_Ioc hα hαp t.coe_nonneg, image_image]
    exact image_congr fun u hu => (imgCurve_of_pos hu.1).symm
  obtain ⟨hTc, hmc⟩ := meanCan_img49_eq (κ := κ) (xL := xL) (xR := xR) hEg hp htP ht' hW' hW'0 hη' hη'p hT hKγ
    (jwL cL6 κ ρL) (jwR cR6 κ ρR)
  have hmL : ∀ i, -rightImg (fun r => -W' r) (-imgMarkL xL ω s i) T - W' T ≤ 0 := fun i => by
    have := le_rightImg (show Continuous fun r => -W' r from hW'.neg) (-imgMarkL xL ω s i) hT.le
    linarith
  have hmR : ∀ j, 0 ≤ rightImg W' (imgMarkR xR ω s j) T - W' T := fun j => by
    have := le_rightImg hW' (imgMarkR xR ω s j) hT.le
    linarith
  have hAG : fwdHull Wα t ⊆ H \ negInv '' fwdHull ω s := fun z hz =>
    ⟨(isHPHull_fwdHull hWα t.coe_nonneg).1 hz, fun h => disjoint_left.1 hdisj hz h⟩
  have hmaps := GlueImg.revChart_mapsTo_H_diff hω hω0 s.coe_nonneg hAG
  rw [← hK'] at hmaps
  rw [← hTc, Sec7.Lemma71D.chartMean]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  by_cases hz : φ z = 0
  · simp only [hz, mul_zero]
  have hzC := hφ (subset_tsupport _ hz)
  have hfH : fwdMap W' T (revChart ω s z) ∈ H := QuantumZipper.FwdHolo.mapsTo_fwdMap hW' hT.le (hmaps hzC)
  show (Coupling.meanCan κ (jwL cL6 κ ρL) (jwR cR6 κ ρR) (fun r => imgW s ζ W E r p)
      (fun i r => imgVL xL s ζ W E i r p) (fun j r => imgVR xR s ζ W E j r p) T.toNNReal (revChart ω s z) -
      2 * π * chiC κ - chiC κ * (cfChart s p.2).2.2 z) * φ z = (w z + u₀ z) * φ z
  rw [hmc, ← Ito.eqOn_meanHarmonic hmL hmR hu hfH, hid z hzC]
  have := chart_shift_eq κ s p.2 z
  congr 1
  linarith

end OneSample

/-! ### The mean identification -/

section Main

open Sec7.StripSysField

/-- **`MeanIdent49Statement cL6 cR6`: the conditional mean of the field given both stopped histories, in the
counterflow chart** (G3 (ii) of Proposition 4.9 at general `κ`; PROVE-GLUECOND7's named input, with ruling R57's
junction weights). The union `A_t ∪ G_s` is a local set of the centred field on the glued space; its local-set mean is
the conditional mean given the germs and both stopped histories; almost surely its harmonic representative `w` has the
flow-side and counterflow-side boundary limits (`ae_union_mean_cfGlue`) and the limit at physical `∞`
(`ae_tendsto_union_sub_cfMean_cobounded`), so the uniqueness statement of Aux. 28 on the (connected) remaining domain
identifies `w + 𝔥₀` with the image word's mean in the image chart (`chartMean_eq_integral_of_sample`). -/
theorem meanIdent49Statement : MeanIdent49Statement.{u} cL6 cR6 := by
  intro κ hκ hκ4 nL nR xL xR ρL ρR hF h44 Ω mΩ P _ 𝓕 W VL VR B ζ h hC Ω₂ _mΩ₂ P₂ _ h₂ W₂ ζ₂ hcf hlaw k _ hk u₀
    hu₀ s hs t ht φ
  set μ := glueMeasure P k (fun ω => cfField κ (h ω)) ((measurable_cfField κ).comp hC.2.1) with hμ
  set E := glueGood μ s ζ W with hEdef
  have hEg : ∀ p ∈ E, IsGood49 s ζ W p := isGood49_of_mem_glueGood
  set U : Ω × HistorySpace 0 0 → Set ℂ := fun p => hullAt t (killedHistory W VL VR ζ p.1) ∪ cfHullQ s p.2
    with hUdef
  set Fd : Ω × HistorySpace 0 0 → DistOn upperHalfPlaneOpens := fun p => cenT κ u₀ (cfField κ (h p.1)) with hFdef
  have hX := hC.2.2.2.1
  have hXm : Measurable fun ω => cfField κ (h ω) := (measurable_cfField κ).comp hC.2.1
  have hYm : Measurable (killedHistory W VL VR ζ) := measurable_killedHistory hX
  have hFg := isZeroBoundaryGFF_cenT_glue (k := k) hC hu₀
  have hAm : Measurable[_, hittingSigma] U :=
    measurable_union_hitting (((measurable_hullAt t).comp hYm).comp measurable_fst)
      ((measurable_cfHullQ s).comp measurable_snd)
  have hAae := ae_hullAt_eq_image_seedLine hκ hκ4 hF h44 hC
  have hζ : ∀ᵐ ω ∂P, ζ ω = ⊤ := by
    filter_upwards [hAae] with ω hω using hω.1
  have hreg₂ := ae_cfReg hκ hκ4 hF h44 hC hcf hlaw
  have hmark := isHistoryAvoidanceLocal_cfGlue hC hκ hζ hcf hreg₂ hlaw hk hu₀ t s
  have hℋ := cfGlueMarks_le (Ω := Ω) t s hX
  have hloc := (isLocalSet_union_glue hC hζ hcf hreg₂ hlaw hk hu₀ t s).2.2
  obtain ⟨g, hg⟩ := LocalSets.IsLocalSet.exists_isLocalSetMean hFg hAm hloc
  have hce := WangWu.IsLocalSetMean.ae_eq_condExp_germSigma_sup hFg hAm hloc hℋ hmark hg φ
  -- the bounded harmonic extensions
  set bd : ℝ → ℝ := fun x => forceBoundaryData κ ρL ρR xL xR x + -(π / 2 * chiC κ) with hbd
  obtain ⟨u', hu'⟩ : ∃ u' : ℂ → ℝ, IsBoundedHarmonicExtension (cfWordData κ bd (forceJumpFinset xL xR))
      (cfWordJumps κ bd (forceJumpFinset xL xR)) u' := by
    obtain ⟨u', hu'⟩ := exists_isBoundedHarmonicExtension_forceBoundaryData (16 / κ)
      (flowLineRhoL (16 / κ) (counterflowData κ bd) (counterflowJumps (forceJumpFinset xL xR)) 0 0)
      (flowLineRhoR (16 / κ) (counterflowData κ bd) (counterflowJumps (forceJumpFinset xL xR)) 0 0)
      (flowLineXL (counterflowData κ bd) (counterflowJumps (forceJumpFinset xL xR)) 0)
      (flowLineXR (counterflowData κ bd) (counterflowJumps (forceJumpFinset xL xR)) 0)
    refine ⟨u', ?_⟩
    simp only [cfWordData, cfWordJumps, coe_forceJumpFinset]
    exact hu'
  choose uq huq using fun ω => exists_isBoundedHarmonicExtension_forceBoundaryData κ ρL ρR
    (fun i => VL i t ω - W t ω) (fun i => VR i t ω - W t ω)
  have hwA := ae_union_mean_cfGlue hC hκ hζ hcf hreg₂ hlaw hk hu₀ t s hu' huq hg
  obtain ⟨gG, hgG, hidG⟩ := exists_isLocalSetMean_cfHullQ_path hC hκ hcf hreg₂ hlaw hk hu₀ s hu'
  have hInf := ae_tendsto_union_sub_cfMean_cobounded hC hζ hcf hreg₂ hlaw hk hu₀ t s hg hgG
  have huniq := Sec6.ae_eqOn_component_of_tendsto_global hFg hAm hloc hg hu₀.1 hu₀.2.1 (chiC κ)
  -- almost-sure regularity
  have hgood := cfGlueAE_isGood49 s hs κ hκ hκ4 xL xR ρL ρR hF h44 P 𝓕 W VL VR B ζ h hC P₂ h₂ W₂ ζ₂ hcf hlaw k hk
  have himg := cfGlueAE_exists_imageTrace κ hκ hκ4 xL xR ρL ρR hF h44 P 𝓕 W VL VR B ζ h hC P₂ h₂ W₂ ζ₂ hcf hlaw k hk
  have hadm := Sec4.hasAdmissiblePartialSums_of_cond44 hκ4 hF h44
  have hline := ae_glue_fst (μ := P) k hXm (ae_seedLine_of_admissible hκ hκ4.le hF hadm hC.1)
  have hmarksP : ∀ᵐ ω ∂P, Continuous (fun r : ℝ => W r.toNNReal ω) ∧ W 0 ω = 0 ∧
      (fun i => VL i t ω - W t ω) =
        (fun i => -rightImg (fun r => -(fun r : ℝ => W r.toNNReal ω) r) (-xL i) t - (fun r : ℝ => W r.toNNReal ω) t) ∧
      (fun i => VR i t ω - W t ω) =
        (fun j => rightImg (fun r : ℝ => W r.toNNReal ω) (xR j) t - (fun r : ℝ => W r.toNNReal ω) t) := by
    filter_upwards [hC.1.2.2.2.2, hζ] with ω hp hζω
    have hw : Continuous fun t => W t ω := by
      have := hp.2.2.2.1
      rw [hζω] at this
      exact continuousOn_univ.1 (this.mono fun t _ => ENNReal.coe_lt_top)
    have hts : ((t : ℝ≥0) : ℝ≥0∞) < ζ ω := by rw [hζω]; exact ENNReal.coe_lt_top
    refine ⟨hw.comp continuous_real_toNNReal, hp.1, funext fun i => ?_, funext fun i => ?_⟩
    · rw [WangWu.vL_eq_neg_rightImg hp hw hts i]
      show _ = -rightImg (fun r => -W r.toNNReal ω) (-xL i) t - W (t : ℝ).toNNReal ω
      rw [Real.toNNReal_coe]
      rfl
    · rw [WangWu.vR_eq_rightImg hp hw hts i]
      show _ = rightImg (fun r : ℝ => W r.toNNReal ω) (xR i) t - W (t : ℝ).toNNReal ω
      rw [Real.toNNReal_coe]
      rfl
  have hmarks := ae_glue_fst (μ := P) k hXm hmarksP
  have hAae' := ae_glue_fst (μ := P) k hXm hAae
  filter_upwards [hce, hwA, hInf, huniq, hidG, hgood, himg, hline, hmarks, hAae'] with p hcep
    ⟨w, hwh, hwrep, hwFl, hwG⟩ hInfp huniqp hidGp ⟨_, hy⟩ himgp ⟨_, ⟨η, hη, hseq⟩, _⟩ ⟨hWα, hW0, hmL, hmR⟩ hAp hAv
  obtain ⟨hpE, htP, hav⟩ := hAv
  have hα : IsLoewnerTrace (fun r : ℝ => W r.toNNReal p.1) (seedLine ζ W p.1) := by
    rw [hseq]; exact isLoewnerTrace_of_isGeneratingTrace hη
  have hWα0 : (fun r : ℝ => W r.toNNReal p.1) 0 = 0 := by simp only [Real.toNNReal_zero, hW0]
  have hset := cfChart_inv_image_eq hEg hpE htP (hAp.2 t)
  have hφC : tsupport φ ⊆ H \ (hullAt t (killedHistory W VL VR ζ p.1) ∪ cfHullQ s p.2) := by
    have := hav.2
    rwa [hset] at this
  have huA := huq p.1
  rw [hmL, hmR] at huA
  have hwInf := hInfp w (cfMeanQ κ bd (forceJumpFinset xL xR) u' s p.2) hwh hwrep
    (harmonicOnNhd_cfMeanQ κ bd (forceJumpFinset xL xR) hu'.1 s p.2) hidGp
  have hmean := chartMean_eq_integral_of_sample hκ hF.2.1 hF.2.2.2 hEg hpE ht htP hα hWα hWα0 (hAp.2 t) hy.1 himgp
    hu₀ hu' huA hwFl hwG hwInf (fun z₀ hz₀ => huniqp z₀ hz₀ w hwh hwrep) hφC
  rw [hmean, ← hcep, hwrep φ hφC]
  have hwc : ContinuousOn w (H \ (hullAt t (killedHistory W VL VR ζ p.1) ∪ cfHullQ s p.2)) :=
    fun z hz => (hwh z hz).1.continuousAt.continuousWithinAt
  have hu₀c : ContinuousOn u₀ H := fun z hz => (hu₀.1 z hz).1.continuousAt.continuousWithinAt
  have hi1 := WholeField.integrable_mul_testOn hwc φ hφC
  have hi2 := WholeField.integrable_mul_testOn hu₀c φ φ.tsupport_subset
  rw [← integral_add hi1 hi2]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp only
  ring

/-- **G4, Proposition 4.9's direction: the image word's martingale clause with the corrected junction weights**
(ruling R57's `ImageWord49FiltCStatement`), from PROVE-GLUECOND7's reduction `imageWord49FiltCStatement_of_ident`
and `meanIdent49Statement`. -/
theorem imageWord49FiltCStatement : ImageWord49FiltCStatement.{u} :=
  imageWord49FiltCStatement_of_ident meanIdent49Statement

end Main

end Word49

end InteractingSLE.Sec5.CrossCond
