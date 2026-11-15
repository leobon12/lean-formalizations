/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2OlmKer2
import InteractingSLE.Spec.Supplement.GW2OmxUloc
import InteractingSLE.Spec.Supplement.GW2OmxStop

/-!
# GW2's open lines: the kernel means of the current stage at time `0` and at positive times, from one unpacking

Packet PROVE-GW2-STAGEMEAN, R120 round. The stage induction compares the stage mean with the β-form at the stage START
(time `0`), where only the conditional counterflow is retained; `GW2OlmKer2.kernel_chart_mean_stop` gives the union
mean only at positive piece times. Both come from ONE unpacking of the launch datum, so that the stop `σ` of the
conditional counterflow, its word `c'`, its trace `γ` and the angle field `Xθ` are shared:

* **`kernel_means`**: `GW2OlmKer2.kernel_chart_mean_stop` together with the retained (time-`0`) mean at `σ`
  (`GW2Stm.exists_retained_gw2_stop`: the harmonic representative of any local-set mean of the retained set is the
  bounded harmonic extension of the counterflow data of the joint word read in `relMap Wk σ`, with the lift).
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

/-- **The retained (time-`0`) kernel mean at the stop `σ`** (the trimmed conclusion of
`GW2Stm.exists_retained_gw2_stop`). -/
def RetMeanAt {Ω : Type u} [mΩ : MeasurableSpace Ω] (κ θ : ℝ) (P : Measure Ω) (X : Ω → DistOn upperHalfPlaneOpens)
    (c' : BoundaryWord) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (σ : Ω → WithTop ℝ≥0) (u₀ : ℂ → ℝ) : Prop :=
  ∃ A : Ω → Set ℂ, Measurable[mΩ, hittingSigma] A ∧ (∀ ω, A ω ⊆ H ∧ IsOpen (H \ A ω)) ∧
    (∀ᵐ ω ∂P, A ω = invHull (fun r : ℝ => W r.toNNReal ω) ((σ ω).untopD 0 : ℝ≥0)) ∧
    IsLocalSet A (centredField X u₀) P ∧
    ∀ g₁ : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean A (centredField X u₀) P g₁ →
      ∀ᵐ ω ∂P, ∀ G₀ : ℂ → ℝ, IsBoundedHarmonicExtension
          (cfData κ (jointWordOfRec (specOffset κ) κ c' (cfRec ((σ ω).untopD 0 : ℝ≥0) W ζ ω)).fn
            (jointWordOfRec (specOffset κ) κ c' (cfRec ((σ ω).untopD 0 : ℝ≥0) W ζ ω)).jumps)
          (cfJumps (jointWordOfRec (specOffset κ) κ c' (cfRec ((σ ω).untopD 0 : ℝ≥0) W ζ ω)).fn
            (jointWordOfRec (specOffset κ) κ c' (cfRec ((σ ω).untopD 0 : ℝ≥0) W ζ ω)).jumps) G₀ →
        ∀ w₁ : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd w₁ (H \ A ω) →
          (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω → g₁ ω φ = ∫ z, w₁ z * φ z) →
          EqOn (fun z => w₁ z + (u₀ z - θ * chiC κ))
            (fun z => G₀ (relMap (fun r : ℝ => W r.toNNReal ω) ((σ ω).untopD 0 : ℝ≥0) z) -
              chiC κ * (relLog (fun r : ℝ => W r.toNNReal ω) ((σ ω).untopD 0 : ℝ≥0) z).im)
            (H \ A ω)

/-- **The union kernel mean at the stops `σ` and `τ`** (the conclusion of `GW2Stm.exists_unionMean_gw2_stop`). -/
def UnionMeanAt {Ω : Type u} [mΩ : MeasurableSpace Ω] (κ θ : ℝ) (P : Measure Ω)
    (X : Ω → DistOn upperHalfPlaneOpens) (b : ℝ → ℝ) (J : Finset ℝ) (c' : BoundaryWord) (W : ℝ≥0 → Ω → ℝ)
    (ζ : Ω → ℝ≥0∞) (σ : Ω → WithTop ℝ≥0) (Wα : ℝ≥0 → Ω → ℝ) (α : Ω → ℝ≥0 → ℂ) (γ : Ω → ℝ≥0 → ℂ)
    (τ : Ω → WithTop ℝ≥0) (u₀ : ℂ → ℝ) : Prop :=
  ∃ A K : Ω → Set ℂ, Measurable[mΩ, hittingSigma] A ∧ Measurable[mΩ, hittingSigma] K ∧
    (∀ᵐ ω ∂P, A ω = invHull (fun r : ℝ => W r.toNNReal ω) ((σ ω).untopD 0 : ℝ≥0)) ∧
    (∀ᵐ ω ∂P, K ω = fwdHull (fun r : ℝ => Wα r.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) ∧
    IsLocalSet (fun ω => A ω ∪ K ω) (centredField X u₀) P ∧
    ∀ g : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean (fun ω => A ω ∪ K ω) (centredField X u₀) P g →
      ∀ᵐ ω ∂P, γ ω ((σ ω).untopD 0 : ℝ≥0) ∈ H → 0 < (τ ω).untopD 0 →
        (((τ ω).untopD 0 : ℝ≥0) : ℝ≥0∞) < firstContactTime (fun u => (α ω u : OnePoint ℂ))
          ((fun u => sphereInv (γ ω u : OnePoint ℂ)) '' Icc 0 ((σ ω).untopD 0 : ℝ≥0)) →
        ∃ (p : (ℝ≥0 → ℝ) × (ℝ≥0 → ℂ) × (ℝ → ℝ) × (ℝ → ℂ)) (G : ℂ → ℝ),
          IsRelChainStop κ (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ) (flowLineXL b J 0) (flowLineXR b J 0)
            (flowLineRhoL κ (jointWordOfRec (specOffset κ) κ c' (cfRec ((σ ω).untopD 0 : ℝ≥0) W ζ ω)).fn
              (jointWordOfRec (specOffset κ) κ c' (cfRec ((σ ω).untopD 0 : ℝ≥0) W ζ ω)).jumps 0 θ)
            (flowLineRhoR κ (jointWordOfRec (specOffset κ) κ c' (cfRec ((σ ω).untopD 0 : ℝ≥0) W ζ ω)).fn
              (jointWordOfRec (specOffset κ) κ c' (cfRec ((σ ω).untopD 0 : ℝ≥0) W ζ ω)).jumps 0 θ)
            (flowLineXL (jointWordOfRec (specOffset κ) κ c' (cfRec ((σ ω).untopD 0 : ℝ≥0) W ζ ω)).fn
              (jointWordOfRec (specOffset κ) κ c' (cfRec ((σ ω).untopD 0 : ℝ≥0) W ζ ω)).jumps 0)
            (flowLineXR (jointWordOfRec (specOffset κ) κ c' (cfRec ((σ ω).untopD 0 : ℝ≥0) W ζ ω)).fn
              (jointWordOfRec (specOffset κ) κ c' (cfRec ((σ ω).untopD 0 : ℝ≥0) W ζ ω)).jumps 0)
            (fun r : ℝ => W r.toNNReal ω) ((σ ω).untopD 0 : ℝ≥0) (fun t => Wα t ω) ((τ ω).untopD 0) p ∧
          IsBoundedHarmonicExtension
            (flowedData κ
              (flowLineRhoL κ (jointWordOfRec (specOffset κ) κ c' (cfRec ((σ ω).untopD 0 : ℝ≥0) W ζ ω)).fn
                (jointWordOfRec (specOffset κ) κ c' (cfRec ((σ ω).untopD 0 : ℝ≥0) W ζ ω)).jumps 0 θ)
              (flowLineRhoR κ (jointWordOfRec (specOffset κ) κ c' (cfRec ((σ ω).untopD 0 : ℝ≥0) W ζ ω)).fn
                (jointWordOfRec (specOffset κ) κ c' (cfRec ((σ ω).untopD 0 : ℝ≥0) W ζ ω)).jumps 0 θ)
              (flowLineXL (jointWordOfRec (specOffset κ) κ c' (cfRec ((σ ω).untopD 0 : ℝ≥0) W ζ ω)).fn
                (jointWordOfRec (specOffset κ) κ c' (cfRec ((σ ω).untopD 0 : ℝ≥0) W ζ ω)).jumps 0)
              (flowLineXR (jointWordOfRec (specOffset κ) κ c' (cfRec ((σ ω).untopD 0 : ℝ≥0) W ζ ω)).fn
                (jointWordOfRec (specOffset κ) κ c' (cfRec ((σ ω).untopD 0 : ℝ≥0) W ζ ω)).jumps 0) p.2.2.1
              (relClock (fun r : ℝ => W r.toNNReal ω) ((σ ω).untopD 0 : ℝ≥0) (fun r : ℝ => p.1 r.toNNReal)
                ((τ ω).untopD 0 : ℝ≥0)))
            (flowedJumps
              (flowLineXL (jointWordOfRec (specOffset κ) κ c' (cfRec ((σ ω).untopD 0 : ℝ≥0) W ζ ω)).fn
                (jointWordOfRec (specOffset κ) κ c' (cfRec ((σ ω).untopD 0 : ℝ≥0) W ζ ω)).jumps 0)
              (flowLineXR (jointWordOfRec (specOffset κ) κ c' (cfRec ((σ ω).untopD 0 : ℝ≥0) W ζ ω)).fn
                (jointWordOfRec (specOffset κ) κ c' (cfRec ((σ ω).untopD 0 : ℝ≥0) W ζ ω)).jumps 0) p.2.2.1
              (relClock (fun r : ℝ => W r.toNNReal ω) ((σ ω).untopD 0 : ℝ≥0) (fun r : ℝ => p.1 r.toNNReal)
                ((τ ω).untopD 0 : ℝ≥0))) G ∧
          ∀ wU : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd wU (H \ (A ω ∪ K ω)) →
            (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (A ω ∪ K ω) →
              g ω φ = ∫ z, wU z * φ z) →
            EqOn (fun z => wU z + u₀ z)
              (fun z => G (fwdMap p.2.2.1
                  (relClock (fun r : ℝ => W r.toNNReal ω) ((σ ω).untopD 0 : ℝ≥0) (fun r : ℝ => p.1 r.toNNReal)
                    ((τ ω).untopD 0 : ℝ≥0)) (relMap (fun r : ℝ => W r.toNNReal ω) ((σ ω).untopD 0 : ℝ≥0) z)) -
                chiC κ * ((logDerivFwd p.2.2.1
                  (relClock (fun r : ℝ => W r.toNNReal ω) ((σ ω).untopD 0 : ℝ≥0) (fun r : ℝ => p.1 r.toNNReal)
                    ((τ ω).untopD 0 : ℝ≥0)) (relMap (fun r : ℝ => W r.toNNReal ω) ((σ ω).untopD 0 : ℝ≥0) z)).im +
                  (relLog (fun r : ℝ => W r.toNNReal ω) ((σ ω).untopD 0 : ℝ≥0) z).im))
              (H \ (A ω ∪ K ω))

/-- **The union kernel mean with the union's marked locality for the marks `𝓝`** (the conclusion of
`GW2Omx.exists_unionMean_gw2_stop_loc` for `𝓝 = F_σ ⊔ F_τ`). -/
def UnionMeanLocAt {Ω : Type u} [mΩ : MeasurableSpace Ω] (κ θ : ℝ) (P : Measure Ω)
    (X : Ω → DistOn upperHalfPlaneOpens) (b : ℝ → ℝ) (J : Finset ℝ) (c' : BoundaryWord) (W : ℝ≥0 → Ω → ℝ)
    (ζ : Ω → ℝ≥0∞) (σ : Ω → WithTop ℝ≥0) (Wα : ℝ≥0 → Ω → ℝ) (α : Ω → ℝ≥0 → ℂ) (γ : Ω → ℝ≥0 → ℂ)
    (τ : Ω → WithTop ℝ≥0) (u₀ : ℂ → ℝ) (𝓝 : {m : MeasurableSpace Ω // m ≤ mΩ}) : Prop :=
  ∃ A K : Ω → Set ℂ, Measurable[mΩ, hittingSigma] A ∧ Measurable[mΩ, hittingSigma] K ∧
    (∀ᵐ ω ∂P, A ω = invHull (fun r : ℝ => W r.toNNReal ω) ((σ ω).untopD 0 : ℝ≥0)) ∧
    (∀ᵐ ω ∂P, K ω = fwdHull (fun r : ℝ => Wα r.toNNReal ω) ((τ ω).untopD 0 : ℝ≥0)) ∧
    IsLocalSet (fun ω => A ω ∪ K ω) (centredField X u₀) P ∧
  (∀ᵐ ω ∂P, A ω ∪ K ω ⊆ H ∧ IsOpen (H \ (A ω ∪ K ω))) ∧
  WholeField.IsHistoryAvoidanceLocal 𝓝.1 (fun ω => A ω ∪ K ω) (centredField X u₀) P ∧
  Measurable[𝓝.1, hittingSigma] (fun ω => A ω ∪ K ω) ∧
  𝓝.1 ≤ aeSigma (MeasurableSpace.comap (centredField X u₀) inferInstance) P ∧
    ∀ g : Ω → DistOn upperHalfPlaneOpens, IsLocalSetMean (fun ω => A ω ∪ K ω) (centredField X u₀) P g →
      ∀ᵐ ω ∂P, γ ω ((σ ω).untopD 0 : ℝ≥0) ∈ H → 0 < (τ ω).untopD 0 →
        (((τ ω).untopD 0 : ℝ≥0) : ℝ≥0∞) < firstContactTime (fun u => (α ω u : OnePoint ℂ))
          ((fun u => sphereInv (γ ω u : OnePoint ℂ)) '' Icc 0 ((σ ω).untopD 0 : ℝ≥0)) →
        ∃ (p : (ℝ≥0 → ℝ) × (ℝ≥0 → ℂ) × (ℝ → ℝ) × (ℝ → ℂ)) (G : ℂ → ℝ),
          IsRelChainStop κ (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ) (flowLineXL b J 0) (flowLineXR b J 0)
            (flowLineRhoL κ (jointWordOfRec (specOffset κ) κ c' (cfRec ((σ ω).untopD 0 : ℝ≥0) W ζ ω)).fn
              (jointWordOfRec (specOffset κ) κ c' (cfRec ((σ ω).untopD 0 : ℝ≥0) W ζ ω)).jumps 0 θ)
            (flowLineRhoR κ (jointWordOfRec (specOffset κ) κ c' (cfRec ((σ ω).untopD 0 : ℝ≥0) W ζ ω)).fn
              (jointWordOfRec (specOffset κ) κ c' (cfRec ((σ ω).untopD 0 : ℝ≥0) W ζ ω)).jumps 0 θ)
            (flowLineXL (jointWordOfRec (specOffset κ) κ c' (cfRec ((σ ω).untopD 0 : ℝ≥0) W ζ ω)).fn
              (jointWordOfRec (specOffset κ) κ c' (cfRec ((σ ω).untopD 0 : ℝ≥0) W ζ ω)).jumps 0)
            (flowLineXR (jointWordOfRec (specOffset κ) κ c' (cfRec ((σ ω).untopD 0 : ℝ≥0) W ζ ω)).fn
              (jointWordOfRec (specOffset κ) κ c' (cfRec ((σ ω).untopD 0 : ℝ≥0) W ζ ω)).jumps 0)
            (fun r : ℝ => W r.toNNReal ω) ((σ ω).untopD 0 : ℝ≥0) (fun t => Wα t ω) ((τ ω).untopD 0) p ∧
          IsBoundedHarmonicExtension
            (flowedData κ
              (flowLineRhoL κ (jointWordOfRec (specOffset κ) κ c' (cfRec ((σ ω).untopD 0 : ℝ≥0) W ζ ω)).fn
                (jointWordOfRec (specOffset κ) κ c' (cfRec ((σ ω).untopD 0 : ℝ≥0) W ζ ω)).jumps 0 θ)
              (flowLineRhoR κ (jointWordOfRec (specOffset κ) κ c' (cfRec ((σ ω).untopD 0 : ℝ≥0) W ζ ω)).fn
                (jointWordOfRec (specOffset κ) κ c' (cfRec ((σ ω).untopD 0 : ℝ≥0) W ζ ω)).jumps 0 θ)
              (flowLineXL (jointWordOfRec (specOffset κ) κ c' (cfRec ((σ ω).untopD 0 : ℝ≥0) W ζ ω)).fn
                (jointWordOfRec (specOffset κ) κ c' (cfRec ((σ ω).untopD 0 : ℝ≥0) W ζ ω)).jumps 0)
              (flowLineXR (jointWordOfRec (specOffset κ) κ c' (cfRec ((σ ω).untopD 0 : ℝ≥0) W ζ ω)).fn
                (jointWordOfRec (specOffset κ) κ c' (cfRec ((σ ω).untopD 0 : ℝ≥0) W ζ ω)).jumps 0) p.2.2.1
              (relClock (fun r : ℝ => W r.toNNReal ω) ((σ ω).untopD 0 : ℝ≥0) (fun r : ℝ => p.1 r.toNNReal)
                ((τ ω).untopD 0 : ℝ≥0)))
            (flowedJumps
              (flowLineXL (jointWordOfRec (specOffset κ) κ c' (cfRec ((σ ω).untopD 0 : ℝ≥0) W ζ ω)).fn
                (jointWordOfRec (specOffset κ) κ c' (cfRec ((σ ω).untopD 0 : ℝ≥0) W ζ ω)).jumps 0)
              (flowLineXR (jointWordOfRec (specOffset κ) κ c' (cfRec ((σ ω).untopD 0 : ℝ≥0) W ζ ω)).fn
                (jointWordOfRec (specOffset κ) κ c' (cfRec ((σ ω).untopD 0 : ℝ≥0) W ζ ω)).jumps 0) p.2.2.1
              (relClock (fun r : ℝ => W r.toNNReal ω) ((σ ω).untopD 0 : ℝ≥0) (fun r : ℝ => p.1 r.toNNReal)
                ((τ ω).untopD 0 : ℝ≥0))) G ∧
          ∀ wU : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd wU (H \ (A ω ∪ K ω)) →
            (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ (A ω ∪ K ω) →
              g ω φ = ∫ z, wU z * φ z) →
            EqOn (fun z => wU z + u₀ z)
              (fun z => G (fwdMap p.2.2.1
                  (relClock (fun r : ℝ => W r.toNNReal ω) ((σ ω).untopD 0 : ℝ≥0) (fun r : ℝ => p.1 r.toNNReal)
                    ((τ ω).untopD 0 : ℝ≥0)) (relMap (fun r : ℝ => W r.toNNReal ω) ((σ ω).untopD 0 : ℝ≥0) z)) -
                chiC κ * ((logDerivFwd p.2.2.1
                  (relClock (fun r : ℝ => W r.toNNReal ω) ((σ ω).untopD 0 : ℝ≥0) (fun r : ℝ => p.1 r.toNNReal)
                    ((τ ω).untopD 0 : ℝ≥0)) (relMap (fun r : ℝ => W r.toNNReal ω) ((σ ω).untopD 0 : ℝ≥0) z)).im +
                  (relLog (fun r : ℝ => W r.toNNReal ω) ((σ ω).untopD 0 : ℝ≥0) z).im))
              (H \ (A ω ∪ K ω))

/-- **The kernel means of the current stage** (the retained mean at the stop `σ` and the union means at
`min t (T n)`), from one unpacking of the launch datum. -/
theorem kernel_means (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u}) {κ θ : ℝ}
    (hκ : 0 < κ) (hκ4 : κ < 4) {Ω : Type u} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → DistOn upperHalfPlaneOpens} {b : ℝ → ℝ} {J : Finset ℝ} (hb : IsPiecewiseConstantBoundaryData b J)
    (hG : IsGFFWithBoundaryData μ X b J) {Wk : ℝ≥0 → Ω → ℝ} {ζk : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ μ X Wk ζk) {W' : ℝ≥0 → Ω → ℝ}
    (hW' : ∀ᵐ ω ∂μ, Continuous (fun t => W' t ω) ∧ W' 0 ω = 0 ∧
      ∃ γ' : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W' t ω) ⊤ γ')
    {cL : Chart} (hpb : GW1P.HasProperBdryExt cL) {ℓ : Ω → ℝ≥0 → ℝ≥0} {Aset : Set ℂ}
    (hd : ∀ᵐ ω ∂μ, ζk ω = ⊤ ∧ Continuous (ℓ ω) ∧ StrictMono (ℓ ω) ∧
      range (ℓ ω) = {t : ℝ≥0 | (t : ℝ≥0∞) < firstTipTime infinitySourceChart (fun s => W' s ω) Aset} ∧
      ∀ (r : ℝ≥0) (z : ℂ), (cL.trans infinitySourceChart).tipAt (fun s => Wk s ω) r z ↔
        infinitySourceChart.tipAt (fun s => W' s ω) (ℓ ω r) z)
    (s N : ℝ≥0) {Wα : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} (hfl : IsFlowLineDriver κ b J θ μ X Wα ζα)
    {α : Ω → ℝ≥0 → ℂ} (hα : ∀ᵐ ω ∂μ, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω))
    (hseed : ¬ ForceWord.ThresholdCondition (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ) 0
      (flowLineXL b J 0) (flowLineXR b J 0)) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ)
      (flowLineXL b J 0) (flowLineXR b J 0)) (forceJumpSet (flowLineXL b J 0) (flowLineXR b J 0)) u₀) :
    ∃ (σ : Ω → WithTop ℝ≥0) (Xθ : Ω → DistOn upperHalfPlaneOpens) (T : ℕ → Ω → ℝ≥0) (c' : BoundaryWord)
      (γ : Ω → ℝ≥0 → ℂ), (∀ ω, σ ω ≤ (N : WithTop ℝ≥0)) ∧
      (∀ᵐ ω ∂μ, ∀ t₀ : ℝ≥0, ℓ ω t₀ = s → t₀ < N → σ ω = (t₀ : WithTop ℝ≥0)) ∧
      (∀ᵐ ω ∂μ, σ ω < (N : WithTop ℝ≥0) → ∃ q : ℝ≥0, s < ℓ ω q) ∧
      (∀ ω, IsTranslateAddConst 0 (θ * chiC κ) (X ω) (Xθ ω)) ∧
      (∀ᵐ ω ∂μ, ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζα ω → ∃ n, t ≤ T n ω) ∧
      (∀ᵐ ω ∂μ, ζk ω = ⊤ ∧ IsGeneratingTrace (fun t => Wk t ω) ⊤ (γ ω)) ∧
      RetMeanAt κ θ μ Xθ c' Wk ζk σ u₀ ∧
      ∀ (n : ℕ) (t : ℝ≥0), ∃ 𝓝 : {m : MeasurableSpace Ω // m ≤ mΩ},
        MeasurableSet[𝓝.1] {ω | σ ω < (N : WithTop ℝ≥0)} ∧
        MeasurableSet[𝓝.1] {ω | (t : WithTop ℝ≥0) ≤ min (t : WithTop ℝ≥0) (T n ω)} ∧
        UnionMeanLocAt κ θ μ Xθ b J c' Wk ζk σ Wα α γ (fun ω => min (t : WithTop ℝ≥0) (T n ω)) u₀ 𝓝 := by
  obtain ⟨h', h₁, c', 𝓕', VL', VR', B', γ, hX', hT, htr', hC', hcomp, hNR⟩ :=
    GW2Olm.counterflow_pack h13 hκ hκ4 hb hG hcf (hd.mono fun _ h => h.1)
  obtain ⟨σ, hσ, hσt, hσN, hσeq, hσconv⟩ := exists_stop_of_datum_ext h13 hκ μ hcf hX' hW' hpb hd s N
  obtain ⟨Xθ, 𝓕, VL, VR, B, hX, T, htr, hC, hTa⟩ := GW2Olm.flowLine_pack hκ hfl hseed
  have hσζ : ∀ᵐ ω ∂μ, (σ ω : ℝ≥0∞) < ζk ω := by
    filter_upwards [hcomp] with ω hc
    rw [hc.1]
    exact lt_top_iff_ne_top.2 (hσt ω)
  obtain ⟨A, hAm, hAG, hAe, -, -, -, hlA, hmeanA⟩ :=
    GW2Stm.exists_retained_gw2_stop h12 h13 hκ hb hG hT htr' hC' hX' hσ hσt hσζ htr hu₀
  refine ⟨σ, Xθ, T, c', γ, hσN, hσeq, hσconv, htr, hTa.2.2.2, hcomp, ⟨A, hAm, hAG, hAe, hlA, hmeanA⟩, fun n t => ?_⟩
  have hτ : IsStoppingTime (drivingFiltration μ hX) (fun ω => min (t : WithTop ℝ≥0) (T n ω)) :=
    (isStoppingTime_const _ t).min (hTa.1 n)
  have hτζ : ∀ᵐ ω ∂μ, ((min (t : WithTop ℝ≥0) (T n ω) : WithTop ℝ≥0) : ℝ≥0∞) < ζα ω :=
    (hTa.2.2.1 n).mono fun _ hω => (min_le_right _ _).trans_lt hω
  have hτt : ∀ ω, min (t : WithTop ℝ≥0) (T n ω) ≠ ⊤ :=
    fun _ => ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_left _ _)
  refine ⟨⟨hσ.measurableSpace ⊔ hτ.measurableSpace, sup_le hσ.measurableSpace_le hτ.measurableSpace_le⟩,
    le_sup_left (a := hσ.measurableSpace) _ (hσ.measurableSet_lt' N), ?_, ?_⟩
  · refine le_sup_right (a := hσ.measurableSpace) _ ?_
    have e : {ω | (t : WithTop ℝ≥0) ≤ min (t : WithTop ℝ≥0) (T n ω)} =
        {ω | min (t : WithTop ℝ≥0) (T n ω) < (t : WithTop ℝ≥0)}ᶜ := by
      ext ω
      simp only [mem_ofPred_eq, mem_compl_iff, not_lt]
    rw [e]
    exact (hτ.measurableSet_lt' t).compl
  · exact exists_unionMean_gw2_stop_loc h12 h13 hκ hb hG hT htr' hC' hX' hcomp hNR hσ hσt htr hC hα hX
      hτ hτζ hτt hu₀

end InteractingSLE.Theorem14.GW2Omx
