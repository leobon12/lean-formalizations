/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2OmxSamp0

/-!
# GW2's open lines: the launch means at stage time `t` and at the stage start, with one kernel word

Packet PROVE-GW2-STAGEMEAN, R120 round. `GW2Omx.kernel_launch_mean` (time `t`) and `GW2Omx.kernel_launch_mean0`
(time `0`) under the same probability measure, with the SAME conditional counterflow word `c'` and trace `γ` (both
come from one call of `GW2Omx.kernel_meansN`), so that the two forms can be compared sample by sample:

* **`kernel_launch_mean_pair`**.
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

/-- **The launch means at stage time `t` and at the stage start, with one kernel word** (one probability measure). -/
theorem kernel_launch_mean_pair (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u}) {κ θ : ℝ}
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
    {I : Set Ω} (hI : MeasurableSet[𝓜.1 ⊔ Ito.nullSets ν] I) (t : ℝ≥0)
    (hsub : ∀ᵐ ω ∂ν, ω ∈ I → ∃ t₀ : ℝ≥0, ℓ ω t₀ = s ∧ ∀ v ≤ t₀, ∀ u ≤ t, (u : ℝ≥0∞) < ζα ω →
      invHull (fun r : ℝ => Wk r.toNNReal ω) (v : ℝ) ∪ fwdHull (fun r : ℝ => Wα r.toNNReal ω) (u : ℝ) ⊆ L ω)
    (heq : ∀ᵐ ω ∂ν, ∀ t₀ : ℝ≥0, ℓ ω t₀ = s → (t : ℝ≥0∞) < ζα ω → ω ∈ I ∧
      L ω = invHull (fun r : ℝ => Wk r.toNNReal ω) (t₀ : ℝ) ∪ fwdHull (fun r : ℝ => Wα r.toNNReal ω) (t : ℝ))
    (𝓜₀ : {m : MeasurableSpace Ω // m ≤ mΩ}) {L₀ : Ω → Set ℂ} (hL₀m : Measurable[𝓜₀.1, hittingSigma] L₀)
    (hL₀c : ∀ ω, L₀ ω ⊆ H ∧ IsOpen (H \ L₀ ω)) (hL₀l : IsHistoryAvoidanceLocal 𝓜₀.1 L₀ (centredField X u') ν)
    {m₀ : Ω → DistOn upperHalfPlaneOpens} (hm₀h : ∀ᵐ ω ∂ν, IsHarmonicDistOn (m₀ ω) (H \ L₀ ω))
    (hk₀ : ∀ ψ : TestOn upperHalfPlaneOpens,
      ν[fun ω => Complex.exp (Complex.I * (centredField X u' ω ψ : ℂ)) | 𝓜₀.1] =ᵐ[ν]
        fun ω => rangeKerCF (m₀ ω) (H \ L₀ ω) ψ)
    {I₀ : Set Ω} (hI₀ : MeasurableSet[𝓜₀.1 ⊔ Ito.nullSets ν] I₀)
    (hsub₀ : ∀ᵐ ω ∂ν, ω ∈ I₀ → ∃ t₀ : ℝ≥0, ℓ ω t₀ = s ∧ ∀ v ≤ t₀,
      invHull (fun r : ℝ => Wk r.toNNReal ω) (v : ℝ) ⊆ L₀ ω)
    (heq₀ : ∀ᵐ ω ∂ν, ∀ t₀ : ℝ≥0, ℓ ω t₀ = s → ω ∈ I₀ ∧ L₀ ω = invHull (fun r : ℝ => Wk r.toNNReal ω) (t₀ : ℝ)) :
    ∃ (Xθ : Ω → DistOn upperHalfPlaneOpens) (c' : BoundaryWord) (γ : Ω → ℝ≥0 → ℂ),
      (∀ ω, IsTranslateAddConst 0 (θ * chiC κ) (X ω) (Xθ ω)) ∧
      (∀ᵐ ω ∂ν, ζk ω = ⊤ ∧ IsGeneratingTrace (fun t => Wk t ω) ⊤ (γ ω)) ∧
      (∀ᵐ ω ∂ν, ∀ t₀ : ℝ≥0, ℓ ω t₀ = s → (t : ℝ≥0∞) < ζα ω → γ ω t₀ ∈ H → 0 < t →
        ((t : ℝ≥0) : ℝ≥0∞) < firstContactTime (fun u => (α ω u : OnePoint ℂ))
          ((fun u => sphereInv (γ ω u : OnePoint ℂ)) '' Icc 0 t₀) →
        ∀ w : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w (H \ L ω) →
          (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ L ω → m ω φ = ∫ z, w z * φ z) →
          UnionFormAt κ θ b J c' Wk ζk Wα uθ ω t₀ t w (H \ L ω)) ∧
      ∀ᵐ ω ∂ν, ∀ t₀ : ℝ≥0, ℓ ω t₀ = s →
        ∀ w : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w (H \ L₀ ω) →
          (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ L₀ ω → m₀ ω φ = ∫ z, w z * φ z) →
          RetFormAt κ θ c' Wk ζk uθ ω t₀ w (H \ L₀ ω) := by
  classical
  obtain ⟨σ, Xθ, T, c', γ, htr, hzθ, hcov, hTζ, hcomp, hN⟩ :=
    kernel_meansN h12 h13 hκ hκ4 hb hG hcf hW' hpb hd s hfl hα hseed huθ
  have hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField X u') ν :=
    Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hG hu'
  have hcent : centredField Xθ uθ = centredField X u' := centredField_translate_eq htr hzθ hh
  refine ⟨Xθ, c', γ, htr, hcomp, ?_, ?_⟩
  · have hmin : ∀ (a b : ℝ≥0), min (a : WithTop ℝ≥0) (b : WithTop ℝ≥0) = ((min a b : ℝ≥0) : WithTop ℝ≥0) :=
      fun a b => (WithTop.coe_min a b).symm
    have key : ∀ N n : ℕ, ∀ᵐ ω ∂ν, ω ∈ {ω | σ N ω < ((N : ℝ≥0) : WithTop ℝ≥0)} ∩
        {ω | (t : WithTop ℝ≥0) ≤ min (t : WithTop ℝ≥0) (T n ω)} →
        (γ ω ((σ N ω).untopD 0 : ℝ≥0) ∈ H ∧ 0 < (min (t : WithTop ℝ≥0) (T n ω)).untopD 0 ∧
          (((min (t : WithTop ℝ≥0) (T n ω)).untopD 0 : ℝ≥0) : ℝ≥0∞) <
            firstContactTime (fun u => (α ω u : OnePoint ℂ))
              ((fun u => sphereInv (γ ω u : OnePoint ℂ)) '' Icc 0 ((σ N ω).untopD 0 : ℝ≥0))) →
        ∀ w : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w (H \ L ω) →
          (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ L ω → m ω φ = ∫ z, w z * φ z) →
          UnionFormAt κ θ b J c' Wk ζk Wα uθ ω ((σ N ω).untopD 0) ((min (t : WithTop ℝ≥0) (T n ω)).untopD 0) w
            (H \ L ω) := by
      intro N n
      obtain ⟨hσN, hσeq, hσconv, hσlt, -, hU⟩ := hN N
      obtain ⟨𝓝, hG1, hG2, hUN⟩ := hU n t
      obtain ⟨A, K, hAm, hKm, hAe, hKe, hUc, hUl, hUm, hdet, hmean⟩ := hUN.form
      rw [hcent] at hUl hdet hmean
      refine ae_eqOn_launchMean_of_kernel hh 𝓜.2 𝓝.2 hLm hLc hLl hmh hk hUm hUc hUl hdet hI ?_ (hG1.inter hG2) ?_
        hmean
      · filter_upwards [hsub, hAe, hKe, hσeq, hTζ] with ω hs hA hK hσe hT hωI
        obtain ⟨t₀, ht₀, hall⟩ := hs hωI
        rw [hA, hK]
        refine hall _ ?_ _ ?_ ?_
        · rcases lt_or_ge t₀ (N : ℝ≥0) with h | h
          · rw [hσe t₀ ht₀ h, WithTop.untopD_coe]
          · obtain ⟨v, hv⟩ : ∃ v : ℝ≥0, σ N ω = (v : WithTop ℝ≥0) :=
              WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top (hσN ω)) |>.imp fun _ h => h.symm
            rw [hv, WithTop.untopD_coe]
            have := hσN ω
            rw [hv, WithTop.coe_le_coe] at this
            exact this.trans h
        · rw [hmin, WithTop.untopD_coe]
          exact min_le_left _ _
        · rw [hmin, WithTop.untopD_coe]
          exact (ENNReal.coe_le_coe.2 (min_le_right _ _)).trans_lt (hT n)
      · filter_upwards [heq, hσconv, hσlt, hσeq, hAe, hKe, hd, hTζ] with ω he hc hlt hσe hA hK hdω hT hωG
        obtain ⟨h1, h2⟩ := hωG
        obtain ⟨q, hq⟩ := hc h1
        have hℓ0 : ℓ ω 0 = 0 := GW2Sgk.clock_zero_of_range hdω.2.2.1 hdω.2.2.2.1
        obtain ⟨t₀, -, ht₀⟩ := intermediate_value_Icc (zero_le (a := q)) hdω.2.1.continuousOn
          ⟨by rw [hℓ0]; exact zero_le, hq.le⟩
        have htN := hlt h1 t₀ ht₀
        have hσv := hσe t₀ ht₀ htN
        have htT : t ≤ T n ω := by
          have h2' : (t : WithTop ℝ≥0) ≤ min (t : WithTop ℝ≥0) (T n ω) := h2
          rw [hmin, WithTop.coe_le_coe] at h2'
          exact h2'.trans (min_le_right _ _)
        have htζ : (t : ℝ≥0∞) < ζα ω := (ENNReal.coe_le_coe.2 htT).trans_lt (hT n)
        obtain ⟨hωI, hL⟩ := he t₀ ht₀ htζ
        refine ⟨hωI, ?_⟩
        rw [hL, hA, hK, hσv, WithTop.untopD_coe, hmin, WithTop.untopD_coe, min_eq_left htT]
    have hσeqAll : ∀ᵐ ω ∂ν, ∀ N : ℕ, ∀ t₀ : ℝ≥0, ℓ ω t₀ = s → t₀ < (N : ℝ≥0) → σ N ω = (t₀ : WithTop ℝ≥0) :=
      ae_all_iff.2 fun N => (hN N).2.1
    filter_upwards [ae_all_iff.2 fun N => ae_all_iff.2 fun n => key N n, hcov, hσeqAll] with ω hall hcovω hσω
    intro t₀ ht₀ htζ hγH ht0 hfc w hw hpair
    obtain ⟨N, hN'⟩ := exists_nat_gt t₀
    obtain ⟨n, hn⟩ := hcovω t htζ
    have hσv : σ N ω = (t₀ : WithTop ℝ≥0) := hσω N t₀ ht₀ hN'
    have hτv : min (t : WithTop ℝ≥0) (T n ω) = (t : WithTop ℝ≥0) := by rw [hmin, min_eq_left hn]
    have hmem : ω ∈ {ω | σ N ω < ((N : ℝ≥0) : WithTop ℝ≥0)} ∩
        {ω | (t : WithTop ℝ≥0) ≤ min (t : WithTop ℝ≥0) (T n ω)} := by
      refine ⟨?_, ?_⟩
      · show σ N ω < ((N : ℝ≥0) : WithTop ℝ≥0)
        rw [hσv]
        exact WithTop.coe_lt_coe.2 hN'
      · show (t : WithTop ℝ≥0) ≤ min (t : WithTop ℝ≥0) (T n ω)
        rw [hτv]
    have hcond : γ ω ((σ N ω).untopD 0 : ℝ≥0) ∈ H ∧ 0 < (min (t : WithTop ℝ≥0) (T n ω)).untopD 0 ∧
        (((min (t : WithTop ℝ≥0) (T n ω)).untopD 0 : ℝ≥0) : ℝ≥0∞) <
          firstContactTime (fun u => (α ω u : OnePoint ℂ))
            ((fun u => sphereInv (γ ω u : OnePoint ℂ)) '' Icc 0 ((σ N ω).untopD 0 : ℝ≥0)) := by
      rw [hσv, hτv, WithTop.untopD_coe, WithTop.untopD_coe]
      exact ⟨hγH, ht0, hfc⟩
    have h := hall N n hmem hcond w hw hpair
    rwa [hσv, hτv, WithTop.untopD_coe, WithTop.untopD_coe] at h
  · have key : ∀ N : ℕ, ∀ᵐ ω ∂ν, ω ∈ {ω | σ N ω < ((N : ℝ≥0) : WithTop ℝ≥0)} → True →
        ∀ w : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w (H \ L₀ ω) →
          (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ L₀ ω → m₀ ω φ = ∫ z, w z * φ z) →
          RetFormAt κ θ c' Wk ζk uθ ω ((σ N ω).untopD 0) w (H \ L₀ ω) := by
      intro N
      obtain ⟨hσN, hσeq, hσconv, hσlt, ⟨𝓝, hG1, hRet⟩, -⟩ := hN N
      obtain ⟨A, hAm, hAc, hAe, hAl, hdet, hmean⟩ := hRet.form
      rw [hcent] at hAl hdet hmean
      refine ae_eqOn_launchMean_of_kernel hh 𝓜₀.2 𝓝.2 hL₀m hL₀c hL₀l hm₀h hk₀ hAm
        (Eventually.of_forall hAc) hAl hdet hI₀ ?_ hG1 ?_ hmean
      · filter_upwards [hsub₀, hAe, hσeq] with ω hs hA hσe hωI
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
      · filter_upwards [heq₀, hσconv, hσlt, hσeq, hAe, hd] with ω he hc hlt hσe hA hdω hωG
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
