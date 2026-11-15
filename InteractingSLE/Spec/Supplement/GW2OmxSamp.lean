/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2OmxPackN
import InteractingSLE.Spec.Supplement.GW2OmxComb
import InteractingSLE.Spec.Supplement.GW2OmxCent

/-!
# GW2's open lines: the launch mean of the current stage in the kernel union's harmonic form

Packet PROVE-GW2-STAGEMEAN, R120 round (per-sample assembly). Under one probability measure `ν` (in use: the
conditional kernel given the earlier pieces): the launch field `X`, the launch union `L` with its Gaussian kernel of
mean `m` given marks `𝓜` and its marked locality, the launch datum (conditional counterflow `Wk`, clock `ℓ`), the
current piece (`Wα`), and a `𝓜 ⊔ nulls` event `I` on which the kernel unions lie in `L` and which contains the samples
where the clock reaches `s` before the piece dies (where `L` IS the kernel union at `t₀`, `t`).

* `UnionFormAt`: the kernel union's harmonic form at the stop values `σv`, `τv` (the mean clause of
  `UnionMeanLocAt`); `UnionMeanLocAt.form`;
* **`kernel_launch_mean`**: almost surely, wherever the clock reaches `s` at `t₀` and the piece is alive at `t`
  (and the form's own conditions hold), every harmonic representative `w` of `m` off `L` satisfies
  `UnionFormAt … t₀ t w (ℍ ∖ L)`.
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

/-- **The kernel union's harmonic form at the stop values** `σv` (conditional counterflow) and `τv` (piece). -/
def UnionFormAt {Ω : Type u} (κ θ : ℝ) (b : ℝ → ℝ) (J : Finset ℝ) (c' : BoundaryWord) (W : ℝ≥0 → Ω → ℝ)
    (ζ : Ω → ℝ≥0∞) (Wα : ℝ≥0 → Ω → ℝ) (u₀ : ℂ → ℝ) (ω : Ω) (σv τv : ℝ≥0) (w : ℂ → ℝ) (D : Set ℂ) : Prop :=
  ∃ (p : (ℝ≥0 → ℝ) × (ℝ≥0 → ℂ) × (ℝ → ℝ) × (ℝ → ℂ)) (G : ℂ → ℝ),
    IsRelChainStop κ (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ) (flowLineXL b J 0) (flowLineXR b J 0)
      (flowLineRhoL κ (jointWordOfRec (specOffset κ) κ c' (cfRec σv W ζ ω)).fn
        (jointWordOfRec (specOffset κ) κ c' (cfRec σv W ζ ω)).jumps 0 θ)
      (flowLineRhoR κ (jointWordOfRec (specOffset κ) κ c' (cfRec σv W ζ ω)).fn
        (jointWordOfRec (specOffset κ) κ c' (cfRec σv W ζ ω)).jumps 0 θ)
      (flowLineXL (jointWordOfRec (specOffset κ) κ c' (cfRec σv W ζ ω)).fn
        (jointWordOfRec (specOffset κ) κ c' (cfRec σv W ζ ω)).jumps 0)
      (flowLineXR (jointWordOfRec (specOffset κ) κ c' (cfRec σv W ζ ω)).fn
        (jointWordOfRec (specOffset κ) κ c' (cfRec σv W ζ ω)).jumps 0)
      (fun r : ℝ => W r.toNNReal ω) σv (fun t => Wα t ω) τv p ∧
    IsBoundedHarmonicExtension
      (flowedData κ
        (flowLineRhoL κ (jointWordOfRec (specOffset κ) κ c' (cfRec σv W ζ ω)).fn
          (jointWordOfRec (specOffset κ) κ c' (cfRec σv W ζ ω)).jumps 0 θ)
        (flowLineRhoR κ (jointWordOfRec (specOffset κ) κ c' (cfRec σv W ζ ω)).fn
          (jointWordOfRec (specOffset κ) κ c' (cfRec σv W ζ ω)).jumps 0 θ)
        (flowLineXL (jointWordOfRec (specOffset κ) κ c' (cfRec σv W ζ ω)).fn
          (jointWordOfRec (specOffset κ) κ c' (cfRec σv W ζ ω)).jumps 0)
        (flowLineXR (jointWordOfRec (specOffset κ) κ c' (cfRec σv W ζ ω)).fn
          (jointWordOfRec (specOffset κ) κ c' (cfRec σv W ζ ω)).jumps 0) p.2.2.1
        (relClock (fun r : ℝ => W r.toNNReal ω) σv (fun r : ℝ => p.1 r.toNNReal)
          τv))
      (flowedJumps
        (flowLineXL (jointWordOfRec (specOffset κ) κ c' (cfRec σv W ζ ω)).fn
          (jointWordOfRec (specOffset κ) κ c' (cfRec σv W ζ ω)).jumps 0)
        (flowLineXR (jointWordOfRec (specOffset κ) κ c' (cfRec σv W ζ ω)).fn
          (jointWordOfRec (specOffset κ) κ c' (cfRec σv W ζ ω)).jumps 0) p.2.2.1
        (relClock (fun r : ℝ => W r.toNNReal ω) σv (fun r : ℝ => p.1 r.toNNReal)
          τv)) G ∧
    EqOn (fun z => w z + u₀ z)
        (fun z => G (fwdMap p.2.2.1
            (relClock (fun r : ℝ => W r.toNNReal ω) σv (fun r : ℝ => p.1 r.toNNReal)
              τv) (relMap (fun r : ℝ => W r.toNNReal ω) σv z)) -
          chiC κ * ((logDerivFwd p.2.2.1
            (relClock (fun r : ℝ => W r.toNNReal ω) σv (fun r : ℝ => p.1 r.toNNReal)
              τv) (relMap (fun r : ℝ => W r.toNNReal ω) σv z)).im +
            (relLog (fun r : ℝ => W r.toNNReal ω) σv z).im))
        D

/-- The mean clause of `UnionMeanLocAt` in the form `UnionFormAt`. -/
theorem UnionMeanLocAt.form {Ω : Type u} [mΩ : MeasurableSpace Ω] {κ θ : ℝ} {P : Measure Ω}
    {X : Ω → DistOn upperHalfPlaneOpens} {b : ℝ → ℝ} {J : Finset ℝ} {c' : BoundaryWord} {W : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} {σ : Ω → WithTop ℝ≥0} {Wα : ℝ≥0 → Ω → ℝ} {α : Ω → ℝ≥0 → ℂ} {γ : Ω → ℝ≥0 → ℂ}
    {τ : Ω → WithTop ℝ≥0} {u₀ : ℂ → ℝ} {𝓝 : {m : MeasurableSpace Ω // m ≤ mΩ}}
    (h : UnionMeanLocAt κ θ P X b J c' W ζ σ Wα α γ τ u₀ 𝓝) :
    ∃ A K : Ω → Set ℂ, Measurable[mΩ, hittingSigma] A ∧ Measurable[mΩ, hittingSigma] K ∧
      (∀ᵐ ω ∂P, A ω = invHull (fun r : ℝ => W r.toNNReal ω) ((σ ω).untopD 0 : ℝ≥0)) ∧
      (∀ᵐ ω ∂P, K ω = fwdHull (fun r : ℝ => Wα r.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) ∧
      (∀ᵐ ω ∂P, A ω ∪ K ω ⊆ H ∧ IsOpen (H \ (A ω ∪ K ω))) ∧
      WholeField.IsHistoryAvoidanceLocal 𝓝.1 (fun ω => A ω ∪ K ω) (centredField X u₀) P ∧
      Measurable[𝓝.1, hittingSigma] (fun ω => A ω ∪ K ω) ∧
      𝓝.1 ≤ aeSigma (MeasurableSpace.comap (centredField X u₀) inferInstance) P ∧
      ∀ g : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean (fun ω => A ω ∪ K ω) (centredField X u₀) P g →
        ∀ᵐ ω ∂P, (γ ω ((σ ω).untopD 0 : ℝ≥0) ∈ H ∧ 0 < (τ ω).untopD 0 ∧
          (((τ ω).untopD 0 : ℝ≥0) : ℝ≥0∞) < firstContactTime (fun u => (α ω u : OnePoint ℂ))
            ((fun u => sphereInv (γ ω u : OnePoint ℂ)) '' Icc 0 ((σ ω).untopD 0 : ℝ≥0))) →
          ∀ wU : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd wU (H \ (A ω ∪ K ω)) →
            (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (A ω ∪ K ω) → g ω φ = ∫ z, wU z * φ z) →
            UnionFormAt κ θ b J c' W ζ Wα u₀ ω ((σ ω).untopD 0) ((τ ω).untopD 0) wU (H \ (A ω ∪ K ω)) := by
  obtain ⟨A, K, hAm, hKm, hAe, hKe, -, hUc, hUl, hUm, hdet, hmean⟩ := h
  refine ⟨A, K, hAm, hKm, hAe, hKe, hUc, hUl, hUm, hdet, fun g hg => ?_⟩
  filter_upwards [hmean g hg] with ω hω hc wU hw hpair
  obtain ⟨p, G, h1, h2, h3⟩ := hω hc.1 hc.2.1 hc.2.2
  exact ⟨p, G, h1, h2, h3 wU hw hpair⟩

/-- **The launch mean of the current stage in the kernel union's harmonic form** (one probability measure). -/
theorem kernel_launch_mean (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u}) {κ θ : ℝ}
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
      L ω = invHull (fun r : ℝ => Wk r.toNNReal ω) (t₀ : ℝ) ∪ fwdHull (fun r : ℝ => Wα r.toNNReal ω) (t : ℝ)) :
    ∃ (Xθ : Ω → DistOn upperHalfPlaneOpens) (c' : BoundaryWord) (γ : Ω → ℝ≥0 → ℂ),
      (∀ ω, IsTranslateAddConst 0 (θ * chiC κ) (X ω) (Xθ ω)) ∧
      (∀ᵐ ω ∂ν, ζk ω = ⊤ ∧ IsGeneratingTrace (fun t => Wk t ω) ⊤ (γ ω)) ∧
      ∀ᵐ ω ∂ν, ∀ t₀ : ℝ≥0, ℓ ω t₀ = s → (t : ℝ≥0∞) < ζα ω → γ ω t₀ ∈ H → 0 < t →
        ((t : ℝ≥0) : ℝ≥0∞) < firstContactTime (fun u => (α ω u : OnePoint ℂ))
          ((fun u => sphereInv (γ ω u : OnePoint ℂ)) '' Icc 0 t₀) →
        ∀ w : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w (H \ L ω) →
          (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ L ω → m ω φ = ∫ z, w z * φ z) →
          UnionFormAt κ θ b J c' Wk ζk Wα uθ ω t₀ t w (H \ L ω) := by
  classical
  obtain ⟨σ, Xθ, T, c', γ, htr, hzθ, hcov, hTζ, hcomp, hN⟩ :=
    kernel_meansN h12 h13 hκ hκ4 hb hG hcf hW' hpb hd s hfl hα hseed huθ
  have hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField X u') ν :=
    Restart.isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hG hu'
  have hcent : centredField Xθ uθ = centredField X u' := centredField_translate_eq htr hzθ hh
  refine ⟨Xθ, c', γ, htr, hcomp, ?_⟩
  have hmin : ∀ (a b : ℝ≥0), min (a : WithTop ℝ≥0) (b : WithTop ℝ≥0) = ((min a b : ℝ≥0) : WithTop ℝ≥0) :=
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

end InteractingSLE.Theorem14.GW2Omx
