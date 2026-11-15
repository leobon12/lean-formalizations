/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtFStmt
import InteractingSLE.Spec.Exist.FlowField

/-!
# Aux. lemma 97's germ identification: one change of measure and one recoded field for all angles

Packet PROVE-AUX97G. Source: Aux. lemma 97's proof (`source/spec/p289-336.md` L553–L576, p. 327: "Use the same local
change of measure for all angles: it depends only on the distant marks"), with Aux. lemma 55's (HL1)–(HL8)
(`source/spec/p241-288.md` L134–L271).

Aux. lemma 55's Cameron–Martin measure `Q = srcMeasure` and recoding `recode` (PROVE-LOCEXT-A/A2/C) are built from the
**distant** marks of a word only: the harmonic function `qExt` of (HL5) sums over `distSetL`/`distSetR`. Two words with
the same positions whose weights agree on the distant marks therefore have the same cutoff, source, approximations,
fast subsequence, Borel pairing and recoding (`*_congr`). For the flow-line words of one boundary datum at different
angles only the seed weights differ, and the two fields differ by a constant; the densities then differ by a
deterministic factor almost surely, which is `1` because both measures are probability measures:

* **`srcMeasure_eq_of_shift`**: two couplings of words agreeing off the seed, whose fields differ by a constant
  multiple of `∫ ·`, have the same Cameron–Martin measure;
* **`recode_flowField`**: the recoding commutes with adding a constant;
* `flowLineRhoL_eq_of_ne`, `flowLineRhoR_eq_of_ne`: the flow-line weights off the seed do not depend on the angle.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace LocalExt

open LQGMetric (DistOn TestOn)
open QuantumZipper (H)

section Congr

variable {nL nR : ℕ} {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL ρL' : Fin nL → ℝ} {ρR ρR' : Fin nR → ℝ}
  {r : ℝ}

/-- `qExt` depends on the weights of the distant marks only. -/
theorem qExt_congr (hL : ∀ i ∈ distSetL xL, ρL i = ρL' i) (hR : ∀ j ∈ distSetR xR, ρR j = ρR' j) :
    qExt κ xL xR ρL ρR = qExt κ xL xR ρL' ρR' := by
  funext z
  unfold qExt
  have e1 : ∑ i ∈ distSetL xL, ρL i * Complex.arg (z - xL i) = ∑ i ∈ distSetL xL, ρL' i * Complex.arg (z - xL i) :=
    Finset.sum_congr rfl fun i hi => by rw [hL i hi]
  have e2 : ∑ j ∈ distSetR xR, ρR j * Complex.arg ((xR j : ℂ) - z) =
      ∑ j ∈ distSetR xR, ρR' j * Complex.arg ((xR j : ℂ) - z) :=
    Finset.sum_congr rfl fun j hj => by rw [hR j hj]
  rw [e1, e2]

theorem fCut_congr (hq : qExt κ xL xR ρL ρR = qExt κ xL xR ρL' ρR') :
    fCut κ xL xR ρL ρR r = fCut κ xL xR ρL' ρR' r := by
  unfold fCut
  rw [hq]

theorem vDens_congr (hq : qExt κ xL xR ρL ρR = qExt κ xL xR ρL' ρR') :
    vDens κ xL xR ρL ρR r = vDens κ xL xR ρL' ρR' r := by
  unfold vDens
  rw [fCut_congr hq]

theorem vSrc_congr (hq : qExt κ xL xR ρL ρR = qExt κ xL xR ρL' ρR') :
    vSrc κ xL xR ρL ρR r = vSrc κ xL xR ρL' ρR' r := by
  unfold vSrc
  rw [vDens_congr hq]

theorem vApprox_congr (hq : qExt κ xL xR ρL ρR = qExt κ xL xR ρL' ρR') :
    vApprox κ xL xR ρL ρR r = vApprox κ xL xR ρL' ρR' r := by
  funext n z
  unfold vApprox
  rw [vDens_congr hq]

theorem srcNorm_congr (hq : qExt κ xL xR ρL ρR = qExt κ xL xR ρL' ρR') :
    srcNorm κ xL xR ρL ρR r = srcNorm κ xL xR ρL' ρR' r := by
  unfold srcNorm
  rw [vSrc_congr hq, fCut_congr hq]

theorem recodeShift_congr (hq : qExt κ xL xR ρL ρR = qExt κ xL xR ρL' ρR') :
    recodeShift κ xL xR ρL ρR r = recodeShift κ xL xR ρL' ρR' r := by
  unfold recodeShift
  rw [fCut_congr hq, hq]

theorem recode_congr (hq : qExt κ xL xR ρL ρR = qExt κ xL xR ρL' ρR') :
    recode κ xL xR ρL ρR r = recode κ xL xR ρL' ρR' r := by
  funext T
  unfold recode
  rw [recodeShift_congr hq]

/-- `Classical.choose` only sees the predicate. -/
theorem choose_congr_pred {α : Sort*} {p q : α → Prop} (hp : ∃ a, p a) (hq : ∃ a, q a) (hpq : p = q) :
    Classical.choose hp = Classical.choose hq := by
  subst hpq
  rfl

theorem pairSeq_congr (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r)
    (hq : qExt κ xL xR ρL ρR = qExt κ xL xR ρL' ρR') :
    pairSeq κ ρL ρR hF hr = pairSeq κ ρL' ρR' hF hr := by
  unfold pairSeq
  refine choose_congr_pred _ _ ?_
  rw [vApprox_congr hq]

theorem srcTest_congr (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r)
    (hq : qExt κ xL xR ρL ρR = qExt κ xL xR ρL' ρR') (k : ℕ) :
    srcTest κ ρL ρR hF hr k = srcTest κ ρL' ρR' hF hr k := by
  ext z
  rw [srcTest_apply, srcTest_apply, pairSeq_congr hF hr hq, vApprox_congr hq]

theorem srcPair_congr (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r)
    (hq : qExt κ xL xR ρL ρR = qExt κ xL xR ρL' ρR') :
    srcPair κ ρL ρR hF hr = srcPair κ ρL' ρR' hF hr := by
  funext T
  unfold srcPair
  simp only [srcTest_congr hF hr hq]

end Congr

/-! ### Fields differing by a constant -/

section Shift

variable {nL nR : ℕ} {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL ρL' : Fin nL → ℝ} {ρR ρR' : Fin nR → ℝ}
  {r : ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- The pairings of a coupling field with the source approximations converge almost surely. -/
theorem ae_tendsto_srcPair_of_coupling [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    {h : Ω → DistOn upperHalfPlaneOpens} (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r) :
    ∀ᵐ ω ∂P, Tendsto (fun k => h ω (srcTest κ ρL ρR hF hr k)) atTop (𝓝 (srcPair κ ρL ρR hF hr (h ω))) := by
  have hu := isBoundedHarmonicExtension_bheAt κ ρL ρR xL xR
  obtain ⟨C, hCb⟩ := hu.2.1
  exact ae_tendsto_srcPair hF hr (continuousOn_of_isBoundedHarmonicExtension hu) hCb (hC.2.2.1 _ hu)

/-- **Aux. lemma 97's common measure**: two couplings (on one space, with one law `P`) of two words with the same
positions whose weights agree on the distant marks, whose fields differ by a constant multiple of `∫ ·`, and whose
seeds are admissible, have the same Cameron–Martin measure (HL3). -/
theorem srcMeasure_eq_of_shift (hκ : 0 < κ) [IsProbabilityMeasure P] {𝓕 𝓕' : Filtration ℝ≥0 mΩ}
    {W W' : ℝ≥0 → Ω → ℝ} {VL VL' : Fin nL → ℝ≥0 → Ω → ℝ} {VR VR' : Fin nR → ℝ≥0 → Ω → ℝ} {B B' : ℝ≥0 → Ω → ℝ}
    {ζ ζ' : Ω → ℝ≥0∞} {h h' : Ω → DistOn upperHalfPlaneOpens}
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h)
    (hC' : IsOptionalHullCoupling κ xL xR ρL' ρR' P 𝓕' W' VL' VR' B' ζ' h')
    (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r)
    (hseed : ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR) (hseed' : ¬ ForceWord.ThresholdCondition ρL' ρR' 0 xL xR)
    (hq : qExt κ xL xR ρL ρR = qExt κ xL xR ρL' ρR') {c : ℝ}
    (hsh : ∀ ω φ, h' ω φ = h ω φ + c * ∫ z, φ z) :
    srcMeasure κ ρL' ρR' P hF hr h' = srcMeasure κ ρL ρR P hF hr h := by
  have hQ := isProbabilityMeasure_srcMeasure hκ hC hF hr hseed
  have hQ' := isProbabilityMeasure_srcMeasure hκ hC' hF hr hseed'
  have hpair := srcPair_congr (r := r) hF hr hq
  -- the pairings differ by a deterministic constant
  set a : ℕ → ℝ := fun k => c * ∫ z, srcTest κ ρL ρR hF hr k z with ha
  have hconv := ae_tendsto_srcPair_of_coupling hC hF hr
  have hconv' := ae_tendsto_srcPair_of_coupling hC' hF hr
  have hboth : ∀ᵐ ω ∂P, Tendsto (fun k => h ω (srcTest κ ρL ρR hF hr k)) atTop
      (𝓝 (srcPair κ ρL ρR hF hr (h ω))) ∧ Tendsto (fun k => h' ω (srcTest κ ρL ρR hF hr k)) atTop
      (𝓝 (srcPair κ ρL ρR hF hr (h' ω))) := by
    filter_upwards [hconv, hconv'] with ω h1 h2
    refine ⟨h1, ?_⟩
    simp only [srcTest_congr hF hr hq, hpair] at h2 ⊢
    exact h2
  obtain ⟨ω₀, hω₀⟩ := hboth.exists
  set ℓ : ℝ := srcPair κ ρL ρR hF hr (h' ω₀) - srcPair κ ρL ρR hF hr (h ω₀) with hℓ
  have hdiff : ∀ ω, (Tendsto (fun k => h ω (srcTest κ ρL ρR hF hr k)) atTop (𝓝 (srcPair κ ρL ρR hF hr (h ω))) ∧
      Tendsto (fun k => h' ω (srcTest κ ρL ρR hF hr k)) atTop (𝓝 (srcPair κ ρL ρR hF hr (h' ω)))) →
      Tendsto a atTop (𝓝 (srcPair κ ρL ρR hF hr (h' ω) - srcPair κ ρL ρR hF hr (h ω))) := by
    intro ω hω
    refine (hω.2.sub hω.1).congr fun k => ?_
    simp only [ha, hsh]
    ring
  have ha₀ := hdiff ω₀ hω₀
  have hshift : ∀ᵐ ω ∂P, srcPair κ ρL' ρR' hF hr (h' ω) = srcPair κ ρL ρR hF hr (h ω) + ℓ := by
    filter_upwards [hboth] with ω hω
    have e := tendsto_nhds_unique (hdiff ω hω) ha₀
    rw [← hpair]
    linarith
  -- the densities differ by a constant factor
  set e : ℝ := Real.exp (-ℓ + srcCentre κ xL xR ρL' ρR' r - srcCentre κ xL xR ρL ρR r) with he
  have hdens : (fun ω => ENNReal.ofReal (srcDensity κ ρL' ρR' hF hr (h' ω))) =ᵐ[P]
      (ENNReal.ofReal e) • fun ω => ENNReal.ofReal (srcDensity κ ρL ρR hF hr (h ω)) := by
    filter_upwards [hshift] with ω hω
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    congr 1
    unfold srcDensity
    rw [hω, srcNorm_congr hq, ← Real.exp_add]
    congr 1
    ring
  have hrel : srcMeasure κ ρL' ρR' P hF hr h' = ENNReal.ofReal e • srcMeasure κ ρL ρR P hF hr h := by
    unfold srcMeasure
    rw [withDensity_congr_ae hdens, withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  have hone : ENNReal.ofReal e = 1 := by
    have h1 := congrArg (fun μ : Measure Ω => μ univ) hrel
    simp only [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one] at h1
    exact h1.symm
  rw [hrel, hone, one_smul]

/-- **The recoding commutes with adding a constant**: `recode (T + c ∫ ·) = recode T + c ∫ ·` (flow fields from `0`). -/
theorem recode_flowField (hF : IsOrderedForceWord xL xR) (hr : IsSeedRadius xL xR r) (c : ℝ)
    (T : DistOn upperHalfPlaneOpens) :
    recode κ xL xR ρL ρR r (Exist.flowField 0 c T) = Exist.flowField 0 c (recode κ xL xR ρL ρR r T) := by
  ext φ
  have hp : ∀ S : DistOn upperHalfPlaneOpens, Exist.flowField 0 c S φ = S φ + c * ∫ w, φ w := fun S => by
    rw [Exist.flowField_apply]
    congr 2
    ext z
    rw [Exist.pushTest_shiftChart_apply, Complex.ofReal_zero, sub_zero]
  rw [recode_apply hF hr, hp, hp, recode_apply hF hr]
  ring

end Shift

/-! ### The flow-line words at two angles -/

section FlowLine

variable {κ : ℝ} {b : ℝ → ℝ} {J : Finset ℝ} {x : ℝ}

/-- The left flow-line weights off the seed do not depend on the angle. -/
theorem flowLineRhoL_eq_of_ne (θ θ' : ℝ) {i : Fin (flowLineNL b J x)} (hi : flowLineXL b J x i ≠ 0) :
    flowLineRhoL κ b J x θ i = flowLineRhoL κ b J x θ' i := by
  revert hi
  refine Fin.cases (motive := fun i : Fin (flowLineNL b J x) =>
    flowLineXL b J x i ≠ 0 → flowLineRhoL κ b J x θ i = flowLineRhoL κ b J x θ' i) ?_ ?_ i
  · intro h
    exact absurd rfl h
  · intro j _
    rfl

/-- The right flow-line weights off the seed do not depend on the angle. -/
theorem flowLineRhoR_eq_of_ne (θ θ' : ℝ) {i : Fin (flowLineNR b J x)} (hi : flowLineXR b J x i ≠ 0) :
    flowLineRhoR κ b J x θ i = flowLineRhoR κ b J x θ' i := by
  revert hi
  refine Fin.cases (motive := fun i : Fin (flowLineNR b J x) =>
    flowLineXR b J x i ≠ 0 → flowLineRhoR κ b J x θ i = flowLineRhoR κ b J x θ' i) ?_ ?_ i
  · intro h
    exact absurd rfl h
  · intro j _
    rfl

/-- The distant harmonic function of the flow-line word does not depend on the angle. -/
theorem qExt_flowLine (θ θ' : ℝ) :
    qExt κ (flowLineXL b J x) (flowLineXR b J x) (flowLineRhoL κ b J x θ) (flowLineRhoR κ b J x θ) =
      qExt κ (flowLineXL b J x) (flowLineXR b J x) (flowLineRhoL κ b J x θ') (flowLineRhoR κ b J x θ') :=
  qExt_congr (fun _i hi => flowLineRhoL_eq_of_ne θ θ' (Finset.mem_filter.1 hi).2)
    (fun _j hj => flowLineRhoR_eq_of_ne θ θ' (Finset.mem_filter.1 hj).2)

end FlowLine

end LocalExt

end InteractingSLE
