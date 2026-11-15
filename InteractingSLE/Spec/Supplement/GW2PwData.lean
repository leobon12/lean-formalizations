/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2PsmStep
import InteractingSLE.Spec.Supplement.SB2OmWord
import InteractingSLE.Spec.Supplement.Q3StopType
import InteractingSLE.Spec.Supplement.GW2RdShift

/-!
# The stage-start data identity of D46's export, one sample (deterministic)

Packet PROVE-GW2-STAGEMEAN, R122 round (D46). The first half of `GW2Psm.stage_step`, read as an identity of words:
with the kernel's retained form at the stage start (`hret`), the instance's stage-start identity (`hinst0`, Claim(k)
at the sample), the dilation `relMap (Uk, t₀) ∘ cL.1 = λ · cs.1` and the far-right heights, the stage word `β` of word
type `w` is the kernel word `K` raised by `θχ` and read at `λ y`, off a finite set:

* **`stage_data_word`**: `β.fn y = (upW (θχ) K).fn (λ y)` for `y` off a finite set.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open QuantumZipper (H fwdMap fwdHull logDerivFwd chiC)

namespace InteractingSLE.Theorem14.GW2Pw

open MartChar.RealFlow Restart Supp8.Q3Chain GW2Omx GW2Psm Supp8.Q3Stop
open Supp8.GB6 (relMap)
open Supp8.Q3Rel (invHull relLog)

/-- **The stage-start data identity as an identity of words** (one sample, deterministic). -/
theorem stage_data_word {κ θ σa : ℝ} (hκ : 0 < κ) {DL D : Set ℂ} {cL cs : Chart} (hcL : IsDomainChart DL cL)
    (hcs : IsDomainChart D cs) (hDL : D ⊆ DL) {Uk : ℝ → ℝ} (hUk : Continuous Uk) (hUk0 : Uk 0 = 0) {t₀ : ℝ}
    (ht₀ : 0 ≤ t₀)
    (hmaps : ∀ y ∈ D, cL.1 y ∈ H \ invHull Uk t₀) {lam : ℝ} (hlam : 0 < lam)
    (hdil : ∀ y ∈ D, relMap Uk t₀ (cL.1 y) = (lam : ℂ) * cs.1 y)
    {wP₀ u₀ u' uθ : ℂ → ℝ} (huθ : ∀ z ∈ H, uθ z - u' z = θ * chiC κ) (K : BoundaryWord)
    (hret : ∀ G₀ : ℂ → ℝ, IsBoundedHarmonicExtension (cfData κ K.fn K.jumps) (cfJumps K.fn K.jumps) G₀ →
      ∀ y ∈ D, wP₀ y + u₀ y + chiC κ * cL.2.2 y - u' (cL.1 y) + (uθ (cL.1 y) - θ * chiC κ) =
        G₀ (relMap Uk t₀ (cL.1 y)) - chiC κ * (relLog Uk t₀ (cL.1 y)).im)
    {w : WordType} {β : BoundaryWord} (hw : wordType κ β = w) {U₀ : ℂ → ℝ}
    (hU₀ : IsBoundedHarmonicExtension (forceBoundaryData κ (typedRhoL w) (typedRhoR w) (typedXL κ w β)
      (typedXR κ w β)) (forceJumpSet (typedXL κ w β) (typedXR κ w β)) U₀)
    (hinst0 : ∀ y ∈ D, wP₀ y + u₀ y + σa + chiC κ * cs.2.2 y = U₀ (cs.1 y))
    {hK hβ : ℝ} (hfarK : ∃ B : ℝ, ∀ y, B < y → y ∉ K.jumps → K.fn y = hK)
    (hfarβ : ∃ B : ℝ, ∀ y, B < y → y ∉ forceJumpSet (typedXL κ w β) (typedXR κ w β) →
      forceBoundaryData κ (typedRhoL w) (typedRhoR w) (typedXL κ w β) (typedXR κ w β) y = hβ)
    (hfar : hK + θ * chiC κ = hβ) :
    ∃ F : Set ℝ, F.Finite ∧ ∀ y, y ∉ F → β.fn y = (GW2Rd.upW (θ * chiC κ) K).fn (lam * y) := by
  classical
  set xL := typedXL κ w β with hxLdef
  set xR := typedXR κ w β with hxRdef
  set ρL := typedRhoL w with hρLdef
  set ρR := typedRhoR w with hρRdef
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
  -- the word form
  have hftK : FCDet.IsFlowType κ θ K (flowLineXL K.fn K.jumps 0) (flowLineXR K.fn K.jumps 0)
      (flowLineRhoL κ K.fn K.jumps 0 θ) (flowLineRhoR κ K.fn K.jumps 0 θ) :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hftβ : FCDet.IsFlowType κ 0 β xL xR ρL ρR := isFlowType_typed hw
  refine ⟨(T₀ : Set ℝ) ∪ ({0} ∪ ((β.jumps : Set ℝ) ∪ (fun z => z / lam) '' (K.jumps : Set ℝ))),
    (T₀.finite_toSet.union ((finite_singleton 0).union (β.jumps.finite_toSet.union
      (K.jumps.finite_toSet.image _)))), fun y hy => ?_⟩
  simp only [mem_union, mem_singleton_iff, Finset.mem_coe, mem_image, not_or] at hy
  obtain ⟨hyT, hy0, hyβ, hyK⟩ := hy
  have hlam0 : lam ≠ 0 := hlam.ne'
  have hly0 : lam * y ≠ 0 := mul_ne_zero hlam0 hy0
  have hlyK : lam * y ∉ K.jumps := fun h => hyK ⟨lam * y, h, by field_simp⟩
  have e := h0 y hyT
  rw [SB.Om.forceBoundaryData_eq_of_isFlowType hκ hftK hly0 hlyK,
    SB.Om.forceBoundaryData_eq_of_isFlowType hκ hftβ hy0 hyβ, zero_mul, add_zero] at e
  rw [GW2Rd.upW_fn]
  exact e.symm

end InteractingSLE.Theorem14.GW2Pw
