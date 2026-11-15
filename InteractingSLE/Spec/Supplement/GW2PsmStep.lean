/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2OmxStart
import InteractingSLE.Spec.Supplement.GW2OmxAlg
import InteractingSLE.Spec.Supplement.GW2OmxLift
import InteractingSLE.Spec.Supplement.GW2TmZero
import InteractingSLE.Spec.Sec5.RestartGenOne
import InteractingSLE.Spec.Sec5.CrossCondGenCloseMarks
import InteractingSLE.Spec.Sec4.Prob41Flow
import InteractingSLE.Spec.Supplement.Q3ChainWord

/-!
# GW2's open lines: from the stage-start identity to the stage mean at stage time `t` (one sample)

Packet PROVE-GW2-STAGEMEAN, R121 round (deterministic). At one sample, with the launch chart `cL`, the stage chart
`cs` (`relMap (Uk, t₀) ∘ cL.1 = λ · cs.1` on the stage domain), the kernel word `K` (time `0`: `RetFormAt`; time `t`:
the flowed data of `K` at angle `θ` along the kernel relative driver `Rk`) and the instance's stage-start data
(`U₀`, force data `ρ`, marks `x`):

* `lift_eq_add_of_derivLog`: a derivative log of `λ · cs.1` has imaginary part `cs.lift + 2πn`;
* **`stage_step`**: if the instance's mean at the stage start is the stage-start form, and the far-right heights
  match (`hK + θχ = hβ`), then at stage time `t` the physical representative is the canonical stage-chart coupling
  mean `couplingMean κ S Q U (cs.1 y) − σa − χ · cs.lift`.

The additive constant of the stage-start comparison is pinned by the far-right heights
(`GW2Omx.const_eq_far_of_bhe_dil`), so no lift normalization is needed; the data then agree exactly after the angle
shift (`Sec5.RestartGen.forceBoundaryData_flowLine_angle`) and flow to stage time `t`
(`GW2Omx.eqOn_bhe_dil_of_data_eq`); the per-point algebra is `GW2Omx.kernel_form_eq_stage_form`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open QuantumZipper (H fwdMap fwdHull logDerivFwd chiC)

namespace InteractingSLE.Theorem14.GW2Psm

open MartChar.RealFlow Restart Supp8.Q3Chain GW2Omx
open Supp8.GB6 (relMap)
open Supp8.Q3Rel (invHull relLog)
open Complex (I)

/-- **A derivative log of a dilation of a domain chart has imaginary part the chart's lift plus `2πn`.** -/
theorem lift_eq_add_of_derivLog {D : Set ℂ} {c : Chart} (hc : IsDomainChart D c) {f L : ℂ → ℂ}
    (hL : IsDerivLog f L D) {lam : ℝ} (hlam : 0 < lam) (hdil : ∀ x ∈ D, f x = (lam : ℂ) * c.1 x) :
    ∃ n : ℤ, ∀ x ∈ D, (L x).im = c.2.2 x + 2 * Real.pi * n := by
  have hDo : IsOpen D := hc.isOpen
  have hDc : IsPreconnected D := hc.isPreconnected
  have hcd := hc.differentiableOn_fwd
  obtain ⟨-, -, Lc, hLc, hcl⟩ := hc
  have hlam' : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam.ne'
  have hLc' : IsDerivLog f (fun z => Lc z + Complex.log lam) D := by
    refine ⟨hLc.1.add_const _, fun z hz => ?_⟩
    have heq : f =ᶠ[𝓝 z] fun x => (lam : ℂ) * c.1 x :=
      Filter.eventually_of_mem (hDo.mem_nhds hz) hdil
    have hdiff : DifferentiableAt ℂ c.1 z := (hcd z hz).differentiableAt (hDo.mem_nhds hz)
    rw [Complex.exp_add, hLc.2 z hz, Complex.exp_log hlam', heq.deriv_eq, deriv_const_mul _ hdiff]
    ring
  obtain ⟨n, hn⟩ := IsDerivLog.exists_int_eqOn hDo hDc hL hLc'
  refine ⟨n, fun x hx => ?_⟩
  rw [hcl hx]
  show (L x).im = (Lc x).im + 2 * Real.pi * n
  rw [hn hx]
  have hlog : (Complex.log (lam : ℂ)).im = 0 := by
    rw [← Complex.ofReal_log hlam.le]
    exact Complex.ofReal_im _
  have h2 : ((2 : ℂ) * (Real.pi : ℂ) * I * (n : ℂ)).im = 2 * Real.pi * n := by
    rw [show (2 : ℂ) * (Real.pi : ℂ) * I * (n : ℂ) = ((2 * Real.pi * n : ℝ) : ℂ) * I by push_cast; ring]
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  rw [Complex.add_im, Complex.add_im, hlog, h2, add_zero]

/-- **From the stage-start identity to the stage mean at stage time `t`** (one sample, deterministic). -/
theorem stage_step {κ θ σa : ℝ} (hκ : 0 < κ) {DL D : Set ℂ} {cL cs : Chart} (hcL : IsDomainChart DL cL)
    (hcs : IsDomainChart D cs) (hDL : D ⊆ DL) {Uk : ℝ → ℝ} (hUk : Continuous Uk) (hUk0 : Uk 0 = 0) {t₀ : ℝ}
    (ht₀ : 0 ≤ t₀)
    (hmaps : ∀ y ∈ D, cL.1 y ∈ H \ invHull Uk t₀) {lam : ℝ} (hlam : 0 < lam)
    (hdil : ∀ y ∈ D, relMap Uk t₀ (cL.1 y) = (lam : ℂ) * cs.1 y)
    {wP₀ wP u₀ u' uθ : ℂ → ℝ} (huθ : ∀ z ∈ H, uθ z - u' z = θ * chiC κ) (K : BoundaryWord)
    (hret : ∀ G₀ : ℂ → ℝ, IsBoundedHarmonicExtension (cfData κ K.fn K.jumps) (cfJumps K.fn K.jumps) G₀ →
      ∀ y ∈ D, wP₀ y + u₀ y + chiC κ * cL.2.2 y - u' (cL.1 y) + (uθ (cL.1 y) - θ * chiC κ) =
        G₀ (relMap Uk t₀ (cL.1 y)) - chiC κ * (relLog Uk t₀ (cL.1 y)).im)
    {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j) {U₀ : ℂ → ℝ}
    (hU₀ : IsBoundedHarmonicExtension (forceBoundaryData κ ρL ρR xL xR) (forceJumpSet xL xR) U₀)
    (hinst0 : ∀ y ∈ D, wP₀ y + u₀ y + σa + chiC κ * cs.2.2 y = U₀ (cs.1 y))
    {hK hβ : ℝ} (hfarK : ∃ B : ℝ, ∀ y, B < y → y ∉ K.jumps → K.fn y = hK)
    (hfarβ : ∃ B : ℝ, ∀ y, B < y → y ∉ forceJumpSet xL xR → forceBoundaryData κ ρL ρR xL xR y = hβ)
    (hfar : hK + θ * chiC κ = hβ)
    {Rk S : ℝ → ℝ} (hRk : Continuous Rk) (hRk0 : Rk 0 = 0) (hS : Continuous S) {Q : ℝ} (hQ : 0 ≤ Q)
    (hSS : EqOn S (fun s => Rk (lam ^ 2 * s) / lam) (Icc 0 Q)) {G U : ℂ → ℝ}
    (hG : IsBoundedHarmonicExtension
      (flowedData κ (flowLineRhoL κ K.fn K.jumps 0 θ) (flowLineRhoR κ K.fn K.jumps 0 θ)
        (flowLineXL K.fn K.jumps 0) (flowLineXR K.fn K.jumps 0) Rk (lam ^ 2 * Q))
      (flowedJumps (flowLineXL K.fn K.jumps 0) (flowLineXR K.fn K.jumps 0) Rk (lam ^ 2 * Q)) G)
    (hU : IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => -rightImg (fun s => -S s) (-xL i) Q - S Q)
        (fun j => rightImg S (xR j) Q - S Q))
      (forceJumpSet (fun i => -rightImg (fun s => -S s) (-xL i) Q - S Q) (fun j => rightImg S (xR j) Q - S Q)) U)
    {y : ℂ} (hy : y ∈ D) (hyQ : fwdMap (fun s => Rk (lam ^ 2 * s) / lam) Q (cs.1 y) ∈ H)
    (ht : wP y + u₀ y + chiC κ * cL.2.2 y - u' (cL.1 y) + uθ (cL.1 y) =
      G (fwdMap Rk (lam ^ 2 * Q) (relMap Uk t₀ (cL.1 y))) -
        chiC κ * ((logDerivFwd Rk (lam ^ 2 * Q) (relMap Uk t₀ (cL.1 y))).im + (relLog Uk t₀ (cL.1 y)).im)) :
    wP y + u₀ y + σa + chiC κ * cs.2.2 y = couplingMean κ S Q U (cs.1 y) := by
  classical
  have hDo : IsOpen D := hcs.isOpen
  have hj := Supp8.Q3Rel.isDomainChart_rel hUk hUk0 ht₀
  -- the constant of the stage-start comparison: `Im relLog (cL.1 y) + cL.lift y = cs.lift y + 2πn`
  have hcLd : DifferentiableOn ℂ cL.1 D := hcL.differentiableOn_fwd.mono hDL
  obtain ⟨-, -, Lc, hLc, hcLl⟩ := id hcL
  have hcomp : IsDerivLog (relMap Uk t₀ ∘ cL.1) (fun y => relLog Uk t₀ (cL.1 y) + Lc y) D :=
    IsDerivLog.comp hDo hj.isOpen hj.differentiableOn_fwd hcLd (fun y hy => hmaps y hy)
      (Supp8.Q3Rel.isDerivLog_relLog hUk ht₀) (hLc.mono hDL)
  obtain ⟨n, hn⟩ := lift_eq_add_of_derivLog hcs hcomp hlam fun y hy => hdil y hy
  have hlift : ∀ y ∈ D, (relLog Uk t₀ (cL.1 y)).im + cL.2.2 y = cs.2.2 y + 2 * Real.pi * n := by
    intro y hy
    have h1 := hn y hy
    have h5 : cL.2.2 y = (Lc y).im := hcLl (hDL hy)
    rw [Complex.add_im, ← h5] at h1
    exact h1
  set C : ℝ := chiC κ * (2 * Real.pi * n) - σa with hC
  -- the stage-start comparison on `ℍ`
  set G₀ : ℂ → ℝ := LocalExt.bheAt κ (flowLineRhoL κ K.fn K.jumps 0 0) (flowLineRhoR κ K.fn K.jumps 0 0)
    (flowLineXL K.fn K.jumps 0) (flowLineXR K.fn K.jumps 0) with hG₀def
  have hG₀ : IsBoundedHarmonicExtension (cfData κ K.fn K.jumps) (cfJumps K.fn K.jumps) G₀ := by
    unfold cfJumps
    rw [Supp8.Q3Chain.coe_initJumps]
    exact LocalExt.isBoundedHarmonicExtension_bheAt κ _ _ _ _
  have hrel : ∀ x ∈ H, G₀ ((lam : ℂ) * x) = U₀ x + C := by
    intro x hx
    have hy : cs.2.1 x ∈ D := hcs.inv_mem hx
    have hx' : cs.1 (cs.2.1 x) = x := hcs.fwd_inv hx
    have h1 := hret G₀ hG₀ _ hy
    have h2 := hinst0 _ hy
    have h3 := huθ _ (hmaps _ hy).1
    have h4 := hlift _ hy
    rw [hdil _ hy, hx'] at h1
    rw [hx'] at h2
    rw [hC]
    linear_combination (-1 : ℝ) * h1 + h2 + h3 + chiC κ * h4
  -- the constant is pinned by the far-right heights
  have hfarcf : ∃ B : ℝ, ∀ z, B < z → z ∉ ((cfJumps K.fn K.jumps : Finset ℝ) : Set ℝ) →
      cfData κ K.fn K.jumps z = hK := by
    obtain ⟨B₀, hB₀⟩ := hfarK
    refine ⟨max B₀ (∑ z ∈ K.jumps, |z|), fun z hz _ => ?_⟩
    have hz1 : B₀ < z := lt_of_le_of_lt (le_max_left _ _) hz
    have hz2 : ∑ z ∈ K.jumps, |z| < z := lt_of_le_of_lt (le_max_right _ _) hz
    have hzJ : z ∉ K.jumps := fun hzJ => by
      have := Finset.single_le_sum (f := fun z => |z|) (fun i _ => abs_nonneg i) hzJ
      have := le_abs_self z
      linarith
    have hz0 : z ≠ 0 := by
      have : 0 ≤ ∑ z ∈ K.jumps, |z| := Finset.sum_nonneg fun i _ => abs_nonneg i
      intro h
      rw [h] at hz2
      linarith
    unfold cfData
    rw [Sec4.forceBoundaryData_flowLine hκ (Restart.BoundaryWord.isPiecewiseConstantBoundaryData K) hz0 hzJ]
    exact hB₀ z hz1 hzJ
  have hCv : C = hK - hβ := const_eq_far_of_bhe_dil (Finset.finite_toSet _) (GW2Sdm.finite_forceJumpSet xL xR)
    hG₀ hU₀ hlam hrel hfarcf hfarβ
  -- the data agree exactly after the angle shift
  set T₀ : Finset ℝ := (cfJumps K.fn K.jumps).image (fun z => z / lam) ∪ Supp8.Q3Chain.initJumps xL xR with hT₀
  have h0 : ∀ x ∉ T₀, forceBoundaryData κ (flowLineRhoL κ K.fn K.jumps 0 θ) (flowLineRhoR κ K.fn K.jumps 0 θ)
      (flowLineXL K.fn K.jumps 0) (flowLineXR K.fn K.jumps 0) (lam * x) = forceBoundaryData κ ρL ρR xL xR x := by
    intro x hx
    have hx1 : lam * x ∉ ((cfJumps K.fn K.jumps : Finset ℝ) : Set ℝ) := fun h => hx (Finset.mem_union_left _
      (Finset.mem_image.2 ⟨lam * x, h, by field_simp⟩))
    have hx2 : x ∉ forceJumpSet xL xR := fun h => hx (Finset.mem_union_right _ (by
      rw [← Finset.mem_coe, Supp8.Q3Chain.coe_initJumps]; exact h))
    have e1 := data_eq_of_bhe_dil hG₀ hU₀ hlam hrel hx1 hx2
    rw [Sec5.RestartGen.forceBoundaryData_flowLine_angle hκ K.fn K.jumps θ 0 (lam * x)]
    unfold cfData at e1
    rw [e1, hCv]
    linarith
  -- the flowed data
  have hq : 0 ≤ lam ^ 2 * Q := mul_nonneg (sq_nonneg _) hQ
  have eL : (fun i => Exist.StagedLaw.markPosL Rk (lam ^ 2 * Q) (flowLineXL K.fn K.jumps 0 i)) =
      fun i => -rightImg (fun s => -Rk s) (-flowLineXL K.fn K.jumps 0 i) (lam ^ 2 * Q) - Rk (lam ^ 2 * Q) :=
    funext fun i => Sec5.CrossCond.Gen.markPosL_eq_rightImg_of_nonpos hRk hRk0 hq (GW2Rd.flowLineXL_nonpos _ _ i)
  have eR : (fun j => Exist.StagedLaw.markPos Rk (lam ^ 2 * Q) (flowLineXR K.fn K.jumps 0 j)) =
      fun j => rightImg Rk (flowLineXR K.fn K.jumps 0 j) (lam ^ 2 * Q) - Rk (lam ^ 2 * Q) :=
    funext fun j => Sec5.CrossCond.Gen.markPos_eq_rightImg_of_nonneg hRk hRk0 hq (GW2Rd.flowLineXR_nonneg _ _ j)
  have hG' := hG
  unfold flowedData flowedJumps at hG'
  rw [Supp8.Q3Chain.coe_initJumps, eL, eR] at hG'
  have hEq := eqOn_bhe_dil_of_data_eq hS hRk hlam hQ hSS ρL ρR (flowLineRhoL κ K.fn K.jumps 0 θ)
    (flowLineRhoR κ K.fn K.jumps 0 θ) hxL hxR (GW2Rd.flowLineXL_nonpos _ _) (GW2Rd.flowLineXR_nonneg _ _) h0 hG' hU
  -- the per-point algebra
  have hyH : cL.1 y ∈ H := (hmaps y hy).1
  refine kernel_form_eq_stage_form (θχ := θ * chiC κ) (cst := 0) (G := G) hlam hQ hSS ?_ (hdil y hy) ?_ (huθ _ hyH)
    (hcL.inv_fwd (hDL hy)) ?_
  · rw [add_zero]
    exact hEq hyQ
  · have h4 := hlift y hy
    have : C = -(θ * chiC κ) := by rw [hCv]; linarith
    rw [hC] at this
    linear_combination chiC κ * h4 + this
  · rw [hcL.inv_fwd (hDL hy)]
    linarith

end InteractingSLE.Theorem14.GW2Psm
