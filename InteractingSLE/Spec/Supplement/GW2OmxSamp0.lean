/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2OmxSamp

/-!
# GW2's open lines: the launch mean of the current stage at its start, in the retained kernel form

Packet PROVE-GW2-STAGEMEAN, R120 round (the stage-start identity). `GW2Omx.kernel_launch_mean` at stage time `0`:
the kernel union is the conditional counterflow's retained hull alone, whose kernel mean is
`GW2Stm.exists_retained_gw2_stop` (now exported with marked locality, `RetMeanLocAt`):

* `RetFormAt`, `RetMeanLocAt.form`;
* **`kernel_launch_mean0`**: almost surely, wherever the clock reaches `s` at `t₀`, every harmonic representative
  of the launch mean off `L` satisfies the retained form `RetFormAt … t₀`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open LQGMetric (DistOn TestOn)
open QuantumZipper (H chiC)

universe u

namespace InteractingSLE.Theorem14.GW2Omx

open Restart Exist Exist.StagedLaw WholeField LocalSets Sec7.PocketTraversal Supp8 Supp8.GB6 Supp8.GB6LineL
  Supp8.GB6LMean Supp8.Q3Chain RelSafeS GW2JointKernel GW2TipSystem GW2Fb GW2JDetR8
open Supp8.Q3Rel (invHull relLog)
open QuantumZipper (fwdMap logDerivFwd)
open QuantumZipper (fwdHull)

/-- **The retained kernel form at the stop value `σv`.** -/
def RetFormAt {Ω : Type u} (κ θ : ℝ) (c' : BoundaryWord) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (u₀ : ℂ → ℝ) (ω : Ω)
    (σv : ℝ≥0) (w : ℂ → ℝ) (D : Set ℂ) : Prop :=
  ∀ G₀ : ℂ → ℝ, IsBoundedHarmonicExtension
      (cfData κ (jointWordOfRec (specOffset κ) κ c' (cfRec σv W ζ ω)).fn
        (jointWordOfRec (specOffset κ) κ c' (cfRec σv W ζ ω)).jumps)
      (cfJumps (jointWordOfRec (specOffset κ) κ c' (cfRec σv W ζ ω)).fn
        (jointWordOfRec (specOffset κ) κ c' (cfRec σv W ζ ω)).jumps) G₀ →
    EqOn (fun z => w z + (u₀ z - θ * chiC κ))
      (fun z => G₀ (relMap (fun r : ℝ => W r.toNNReal ω) σv z) -
        chiC κ * (relLog (fun r : ℝ => W r.toNNReal ω) σv z).im)
      D

/-- The mean clause of `RetMeanLocAt` in the form `RetFormAt`. -/
theorem RetMeanLocAt.form {Ω : Type u} [mΩ : MeasurableSpace Ω] {κ θ : ℝ} {P : Measure Ω}
    {X : Ω → DistOn upperHalfPlaneOpens} {c' : BoundaryWord} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    {σ : Ω → WithTop ℝ≥0} {u₀ : ℂ → ℝ} {𝓝 : {m : MeasurableSpace Ω // m ≤ mΩ}}
    (h : RetMeanLocAt κ θ P X c' W ζ σ u₀ 𝓝) :
    ∃ A : Ω → Set ℂ, Measurable[𝓝.1, hittingSigma] A ∧ (∀ ω, A ω ⊆ H ∧ IsOpen (H \ A ω)) ∧
      (∀ᵐ ω ∂P, A ω = invHull (fun r : ℝ => W r.toNNReal ω) ((σ ω).untopD 0 : ℝ≥0)) ∧
      WholeField.IsHistoryAvoidanceLocal 𝓝.1 A (centredField X u₀) P ∧
      𝓝.1 ≤ aeSigma (MeasurableSpace.comap (centredField X u₀) inferInstance) P ∧
      ∀ g₁ : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean A (centredField X u₀) P g₁ →
        ∀ᵐ ω ∂P, True → ∀ w₁ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₁ (H \ A ω) →
          (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω → g₁ ω φ = ∫ z, w₁ z * φ z) →
          RetFormAt κ θ c' W ζ u₀ ω ((σ ω).untopD 0) w₁ (H \ A ω) := by
  obtain ⟨A, hAm, hAc, hAe, hAl, hdet, hmean⟩ := h
  refine ⟨A, hAm, hAc, hAe, hAl, hdet, fun g hg => ?_⟩
  filter_upwards [hmean g hg] with ω hω _ w₁ hw hpair G₀ hG₀
  exact hω G₀ hG₀ w₁ hw hpair

/-- **The launch mean at the stage start in the retained kernel form** (one probability measure). -/
theorem kernel_launch_mean0 (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u}) {κ θ : ℝ}
    (hκ : 0 < κ) (hκ4 : κ < 4) {Ω : Type u} [mΩ : MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]
    {X : Ω → DistOn upperHalfPlaneOpens} {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J)
    (hG : IsGFFWithBoundaryData ν X b J) {u' : ℂ → ℝ} (hu' : IsBoundedHarmonicExtension b J u')
    {Wk : ℝ≥0 → Ω → ℝ} {ζk : Ω → ℝ≥0∞} (hcf : IsCenteredCounterflowDriver κ ν X Wk ζk) {W' : ℝ≥0 → Ω → ℝ}
    (hW' : ∀ᵐ ω ∂ν, Continuous (fun t => W' t ω) ∧ W' 0 ω = 0 ∧
      ∃ γ' : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W' t ω) ⊤ γ')
    {cL : Chart} (hpb : GW1P.HasProperBdryExt cL) {ℓ : Ω → ℝ≥0 → ℝ≥0} {Aset : Set ℂ}
    (hd : ∀ᵐ ω ∂ν, ζk ω = ⊤ ∧ Continuous (ℓ ω) ∧ StrictMono (ℓ ω) ∧
      range (ℓ ω) = {t : ℝ≥0 | (t : ℝ≥0∞) < firstTipTime infinitySourceChart (fun s => W' s ω) Aset} ∧
      ∀ (r : ℝ≥0) (z : ℂ), (cL.trans infinitySourceChart).tipAt (fun s => Wk s ω) r z ↔
        infinitySourceChart.tipAt (fun s => W' s ω) (ℓ ω r) z)
    (s : ℝ≥0) {Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} (hfl : IsFlowLineDriver κ b J θ ν X Wα ζα)
    {α : Ω → ℝ≥0 → ℂ} (hα : ∀ᵐ ω ∂ν, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω))
    (hseed : ¬ ForceWord.ThresholdCondition (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ) 0
      (flowLineXL b J 0) (flowLineXR b J 0)) {uθ : ℂ → ℝ}
    (huθ : IsBoundedHarmonicExtension (forceBoundaryData κ (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ)
      (flowLineXL b J 0) (flowLineXR b J 0)) (forceJumpSet (flowLineXL b J 0) (flowLineXR b J 0)) uθ)
    (𝓜 : {m : MeasurableSpace Ω // m ≤ mΩ}) {L : Ω → Set ℂ} (hLm : Measurable[𝓜.1, hittingSigma] L)
    (hLc : ∀ ω, L ω ⊆ H ∧ IsOpen (H \ L ω)) (hLl : IsHistoryAvoidanceLocal 𝓜.1 L (centredField X u') ν)
    {m : Ω → DistOn upperHalfPlaneOpens} (hmh : ∀ᵐ ω ∂ν, IsHarmonicDistOn (m ω) (H \ L ω))
    (hk : ∀ ψ : TestOn upperHalfPlaneOpens,
      ν[fun ω => Complex.exp (Complex.I * (centredField X u' ω ψ : ℂ)) | 𝓜.1] =ᵐ[ν]
        fun ω => rangeKerCF (m ω) (H \ L ω) ψ)
    {I : Set Ω} (hI : MeasurableSet[𝓜.1 ⊔ Ito.nullSets ν] I)
    (hsub : ∀ᵐ ω ∂ν, ω ∈ I → ∃ t₀ : ℝ≥0, ℓ ω t₀ = s ∧ ∀ v ≤ t₀,
      invHull (fun r : ℝ => Wk r.toNNReal ω) (v : ℝ) ⊆ L ω)
    (heq : ∀ᵐ ω ∂ν, ∀ t₀ : ℝ≥0, ℓ ω t₀ = s → ω ∈ I ∧ L ω = invHull (fun r : ℝ => Wk r.toNNReal ω) (t₀ : ℝ)) :
    ∃ (Xθ : Ω → DistOn upperHalfPlaneOpens) (c' : BoundaryWord) (γ : Ω → ℝ≥0 → ℂ),
      (∀ ω, IsTranslateAddConst 0 (θ * chiC κ) (X ω) (Xθ ω)) ∧
      (∀ᵐ ω ∂ν, ζk ω = ⊤ ∧ IsGeneratingTrace (fun t => Wk t ω) ⊤ (γ ω)) ∧
      ∀ᵐ ω ∂ν, ∀ t₀ : ℝ≥0, ℓ ω t₀ = s →
        ∀ w : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w (H \ L ω) →
          (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ L ω → m ω φ = ∫ z, w z * φ z) →
          RetFormAt κ θ c' Wk ζk uθ ω t₀ w (H \ L ω) := by
  classical
  obtain ⟨σ, Xθ, T, c', γ, htr, hzθ, -, -, hcomp, hN⟩ :=
    kernel_meansN h12 h13 hκ hκ4 hb hG hcf hW' hpb hd s hfl hα hseed huθ
  have hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField X u') ν :=
    Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hG hu'
  have hcent : centredField Xθ uθ = centredField X u' := centredField_translate_eq htr hzθ hh
  refine ⟨Xθ, c', γ, htr, hcomp, ?_⟩
  have key : ∀ N : ℕ, ∀ᵐ ω ∂ν, ω ∈ {ω | σ N ω < ((N : ℝ≥0) : WithTop ℝ≥0)} → True →
      ∀ w : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w (H \ L ω) →
        (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ L ω → m ω φ = ∫ z, w z * φ z) →
        RetFormAt κ θ c' Wk ζk uθ ω ((σ N ω).untopD 0) w (H \ L ω) := by
    intro N
    obtain ⟨hσN, hσeq, hσconv, hσlt, ⟨𝓝, hG1, hRet⟩, -⟩ := hN N
    obtain ⟨A, hAm, hAc, hAe, hAl, hdet, hmean⟩ := hRet.form
    rw [hcent] at hAl hdet hmean
    refine ae_eqOn_launchMean_of_kernel hh 𝓜.2 𝓝.2 hLm hLc hLl hmh hk hAm
      (Eventually.of_forall hAc) hAl hdet hI ?_ hG1 ?_ hmean
    · filter_upwards [hsub, hAe, hσeq] with ω hs hA hσe hωI
      obtain ⟨t₀, ht₀, hall⟩ := hs hωI
      rw [hA]
      refine hall _ ?_
      rcases lt_or_ge t₀ (N : ℝ≥0) with h | h
      · rw [hσe t₀ ht₀ h, WithTop.untopD_coe]
      · obtain ⟨v, hv⟩ : ∃ v : ℝ≥0, σ N ω = (v : WithTop ℝ≥0) :=
          WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top (hσN ω)) |>.imp fun _ h => h.symm
        rw [hv, WithTop.untopD_coe]
        have := hσN ω
        rw [hv, WithTop.coe_le_coe] at this
        exact this.trans h
    · filter_upwards [heq, hσconv, hσlt, hσeq, hAe, hd] with ω he hc hlt hσe hA hdω hωG
      obtain ⟨q, hq⟩ := hc hωG
      have hℓ0 : ℓ ω 0 = 0 := GW2Sgk.clock_zero_of_range hdω.2.2.1 hdω.2.2.2.1
      obtain ⟨t₀, -, ht₀⟩ := intermediate_value_Icc (zero_le (a := q)) hdω.2.1.continuousOn
        ⟨by rw [hℓ0]; exact zero_le, hq.le⟩
      have htN := hlt hωG t₀ ht₀
      have hσv := hσe t₀ ht₀ htN
      obtain ⟨hωI, hL⟩ := he t₀ ht₀
      refine ⟨hωI, ?_⟩
      rw [hL, hA, hσv, WithTop.untopD_coe]
  have hσeqAll : ∀ᵐ ω ∂ν, ∀ N : ℕ, ∀ t₀ : ℝ≥0, ℓ ω t₀ = s → t₀ < (N : ℝ≥0) → σ N ω = (t₀ : WithTop ℝ≥0) :=
    ae_all_iff.2 fun N => (hN N).2.1
  filter_upwards [ae_all_iff.2 fun N => key N, hσeqAll] with ω hall hσω
  intro t₀ ht₀ w hw hpair
  obtain ⟨N, hN'⟩ := exists_nat_gt t₀
  have hσv : σ N ω = (t₀ : WithTop ℝ≥0) := hσω N t₀ ht₀ hN'
  have hmem : ω ∈ {ω | σ N ω < ((N : ℝ≥0) : WithTop ℝ≥0)} := by
    show σ N ω < ((N : ℝ≥0) : WithTop ℝ≥0)
    rw [hσv]
    exact WithTop.coe_lt_coe.2 hN'
  have h := hall N hmem trivial w hw hpair
  rwa [hσv, WithTop.untopD_coe] at h

end InteractingSLE.Theorem14.GW2Omx
