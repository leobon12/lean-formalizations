/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2StmRet
import InteractingSLE.Spec.Supplement.GW2FbLocal

/-!
# GW2's stage step, part 2: the union mean with the counterflow read at a stopping time

Packet PROVE-GW2-STAGEMEAN (ruling R106). GW2's union mean (`GW2Fb.ae_eqOn_unionMean_gw2`, GB9 p. 525) reads the
complete counterflow at a deterministic own time `s`. At stage `k + 1` the stage field's conditional counterflow (the
image of the original one after mapping out the earlier pieces; Lemma GW2a's proof, p. 623: "In the already established
complete conditional counterflow pair targeted at the current incoming tip, GB6 and BW1 apply to the next ordinary
piece") is read up to the own time `σ_k` at which it has exhausted the image of the original stopped hull: a stopping
time of its own driving filtration, not a deterministic time. This file proves the union mean at such a time:

* **`exists_unionMean_gw2_stop`**: for the complete counterflow of the transported field (its coupling explicit, so
  that its driving filtration is available), a finite stopping time `σ` of that filtration, and a flow line of `h` at
  any angle `θ` read at a finite stopping time `τ < ζα` of its own driving filtration: there are hitting-measurable
  versions `A` of `invHull W σ` and `K` of the flow hull at `τ` whose union is a local set of the centred coupling
  field, and for every local-set mean `g` of the union, almost surely on `{γ(σ) ∈ ℍ, 0 < τ < T_c}`, the harmonic
  representative of `g` is the canonical coupling mean of the relative flow line in the joint chart `relMap W σ`, for
  the angle-`θ` flow-line word of the joint word `jointWordOfRec (specOffset κ) κ c′ (cfRec σ W ζ)` flowed by the
  relative chain. This is `GW2Fb.ae_eqOn_unionMean_gw2` with `s` replaced by `σ`.

Inputs: Theorems 1.2–1.3 (R48: GW2 serves Theorem 1.4 only), the counterflow's no-return to its base at all positive
times (`Wire.counterflowNoReturnStatement_of_theorem13`). The retained half is `GW2Stm.exists_retMean_stop` at the dual
parameter; the engine is `GW2Fb.ae_eqOn_unionMean_invHull_stop` (which already allows a random retained time).
Conditional helper with a distinct name; it replaces no source theorem. No `κ < 4` hypothesis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdMap fwdMapInv fwdHull logDerivFwd chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.GW2Stm

open Restart Exist Exist.StagedLaw WholeField LocalSets
open Supp8.GB6 Supp8.GB6LineL Supp8.GB6LMean Supp8.Q3Chain
open Supp8.Q3Rel (invHull relLog relBad IsRelConfigOff)
open GW2JointKernel GW2TipSystem GW2Fb

/-- **The retained counterflow at a stopping time, in the flow line's frame** (the dual instance of
`exists_retMean_stop`): a version `A` of the inverted counterflow hull at `σ`, hitting-measurable and field-determined
for the stopped σ-algebra, history-marked local for it and a local set of the centred coupling field, with the joint
word's retained mean. -/
theorem exists_retained_gw2_stop (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    {κ θ : ℝ} (hκ : 0 < κ) {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h h' : Ω → DistOn upperHalfPlaneOpens} {b : ℝ → ℝ} {J : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) (hG : IsGFFWithBoundaryData P h b J)
    (hT : ∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC κ)) (chiC (16 / κ)) (h ω) (h' ω))
    {c' : BoundaryWord} {h₁ : Ω → DistOn upperHalfPlaneOpens} {𝓕' : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL' : Fin (flowLineNL c'.fn c'.jumps 0) → ℝ≥0 → Ω → ℝ} {VR' : Fin (flowLineNR c'.fn c'.jumps 0) → ℝ≥0 → Ω → ℝ}
    {B' : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (htr' : ∀ ω, IsTranslateAddConst 0 (0 * chiC (16 / κ)) (h' ω) (h₁ ω))
    (hC' : IsOptionalHullCoupling (16 / κ) (flowLineXL c'.fn c'.jumps 0) (flowLineXR c'.fn c'.jumps 0)
      (flowLineRhoL (16 / κ) c'.fn c'.jumps 0 0) (flowLineRhoR (16 / κ) c'.fn c'.jumps 0 0) P 𝓕' W VL' VR' B' ζ h₁)
    (hX' : IsMeasurableKilledDriving W VL' VR' ζ) {σ : Ω → WithTop ℝ≥0}
    (hσ : IsStoppingTime (drivingFiltration P hX') σ) (hσt : ∀ ω, σ ω ≠ ⊤)
    (hσζ : ∀ᵐ ω ∂P, (σ ω : ℝ≥0∞) < ζ ω)
    {X : Ω → DistOn upperHalfPlaneOpens} (htr : ∀ ω, IsTranslateAddConst 0 (θ * chiC κ) (h ω) (X ω)) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ)
      (flowLineXL b J 0) (flowLineXR b J 0)) (forceJumpSet (flowLineXL b J 0) (flowLineXR b J 0)) u₀) :
    ∃ A : Ω → Set ℂ, Measurable[mΩ, hittingSigma] A ∧ (∀ ω, A ω ⊆ H ∧ IsOpen (H \ A ω)) ∧
      (∀ᵐ ω ∂P, A ω = invHull (fun r : ℝ => W r.toNNReal ω) ((σ ω).untopD 0 : ℝ≥0)) ∧
      Measurable[hσ.measurableSpace, hittingSigma] A ∧
      hσ.measurableSpace ≤ aeSigma (MeasurableSpace.comap (centredField X u₀) inferInstance) P ∧
      WholeField.IsHistoryAvoidanceLocal hσ.measurableSpace A (centredField X u₀) P ∧
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
              (H \ A ω) := by
  have hk : (0 : ℝ) < 16 / κ := by positivity
  have e16 : 16 / (16 / κ) = κ := by field_simp
  have hcf : IsFlowLineDriver (16 / κ) c'.fn c'.jumps 0 P h' W ζ := ⟨h₁, 𝓕', VL', VR', B', htr', hC'⟩
  have hGc' : IsGFFWithBoundaryData P h' c'.fn c'.jumps :=
    Theorem14.GW2aPiece.isGFFWithBoundaryData_of_isFlowLineDriver hk c'.isPiecewiseConstantBoundaryData hcf
  have hdet : LP.HasFieldDeterminedHistories.{u} (16 / κ) (flowLineXL c'.fn c'.jumps 0)
      (flowLineXR c'.fn c'.jumps 0) (flowLineRhoL (16 / κ) c'.fn c'.jumps 0 0)
      (flowLineRhoR (16 / κ) c'.fn c'.jumps 0 0) :=
    Exist.Param12.hasFieldDeterminedHistories h12 h13 hk (Theorem15.isOrderedForceWord_flowLine c'.fn c'.jumps 0)
  have hT' : ∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC (16 / κ)))
      (chiC (16 / (16 / κ))) (h' ω) (h ω) := fun ω => isChartTransport_dual hκ (hT ω)
  obtain ⟨uh, huh⟩ := Sec7.StripSysField.exists_isBoundedHarmonicExtension_forceBoundaryData κ
    (flowLineRhoL κ b J 0 0) (flowLineRhoR κ b J 0 0) (flowLineXL b J 0) (flowLineXR b J 0)
  have huh' : IsBoundedHarmonicExtension (cfData κ b J)
      (forceJumpSet (flowLineXL b J 0) (flowLineXR b J 0)) uh := huh
  have huh'' : IsBoundedHarmonicExtension (cfData (16 / (16 / κ)) b J)
      (forceJumpSet (flowLineXL b J 0) (flowLineXR b J 0)) uh := by
    rw [e16]
    exact huh'
  obtain ⟨hrel, hcX⟩ := centredField_flow_eq hκ hb htr huh' hu₀
  obtain ⟨A, hAm, hAG, hAe, hAst, hd, hloc, hlA, hmean⟩ :=
    exists_retMean_stop (κ := 16 / κ) (θ := 0) hk hGc' hb hG hT' htr' hC' hX' hdet huh'' hσ hσt hσζ
  rw [hcX] at hd hloc hlA
  refine ⟨A, hAm, hAG, hAe, hAst, hd, hloc, hlA, fun g₁ hg₁ => ?_⟩
  have hg₁' : IsLocalSetMean A (centredField h uh) P g₁ := by
    rw [hcX]
    exact hg₁
  filter_upwards [hmean g₁ hg₁'] with ω hω G₀ hG₀ w₁ hw₁ hr₁ z hz
  rw [jointWordOfRec_specOffset hκ, cfRec_eq_gb6Rec] at hG₀
  simp only [e16] at hω
  have h1 := hω G₀ hG₀ w₁ hw₁ hr₁ hz
  have h2 : u₀ z = uh z + θ * chiC κ := hrel hz.1
  show w₁ z + (u₀ z - θ * chiC κ) = _
  rw [h2]
  linarith

/-- **GW2's union mean with the counterflow read at a stopping time** (the stage step's union mean; GB9, p. 525, and
Lemma GW2a's proof, p. 623). For the complete counterflow of the transported field with its coupling explicit, a
finite stopping time `σ` of its driving filtration, a flow line of `h` at any angle `θ` and a finite stopping time
`τ < ζα` of its driving filtration: there are hitting-measurable versions `A` of `invHull W σ` and `K` of the flow hull
at `τ` whose union is a local set of the centred coupling field, and for every local-set mean `g` of the union, almost
surely on `{γ(σ) ∈ ℍ, 0 < τ < T_c}`, the harmonic representative of `g` is the canonical coupling mean of the relative
flow line in the joint chart `relMap W σ` for the angle-`θ` flow-line word of the joint word at the record at `σ`.
`GW2Fb.ae_eqOn_unionMean_gw2` is the case of a deterministic `σ = s`. -/
theorem exists_unionMean_gw2_stop (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    {κ θ : ℝ} (hκ : 0 < κ) {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h h' : Ω → DistOn upperHalfPlaneOpens} {b : ℝ → ℝ} {J : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b J) (hG : IsGFFWithBoundaryData P h b J)
    (hT : ∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * chiC κ)) (chiC (16 / κ)) (h ω) (h' ω))
    {c' : BoundaryWord} {h₁ : Ω → DistOn upperHalfPlaneOpens} {𝓕' : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
    {VL' : Fin (flowLineNL c'.fn c'.jumps 0) → ℝ≥0 → Ω → ℝ} {VR' : Fin (flowLineNR c'.fn c'.jumps 0) → ℝ≥0 → Ω → ℝ}
    {B' : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {γ : Ω → ℝ≥0 → ℂ}
    (htr' : ∀ ω, IsTranslateAddConst 0 (0 * chiC (16 / κ)) (h' ω) (h₁ ω))
    (hC' : IsOptionalHullCoupling (16 / κ) (flowLineXL c'.fn c'.jumps 0) (flowLineXR c'.fn c'.jumps 0)
      (flowLineRhoL (16 / κ) c'.fn c'.jumps 0 0) (flowLineRhoR (16 / κ) c'.fn c'.jumps 0 0) P 𝓕' W VL' VR' B' ζ h₁)
    (hX' : IsMeasurableKilledDriving W VL' VR' ζ)
    (hcomp : ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω))
    (hNR : ∀ᵐ ω ∂P, ∀ v : ℝ≥0, 0 < v → γ ω v ≠ 0) {σ : Ω → WithTop ℝ≥0}
    (hσ : IsStoppingTime (drivingFiltration P hX') σ) (hσt : ∀ ω, σ ω ≠ ⊤)
    {X : Ω → DistOn upperHalfPlaneOpens} {𝓕 : Filtration ℝ≥0 mΩ} {Wα : ℝ≥0 → Ω → ℝ}
    {VL : Fin (flowLineNL b J 0) → ℝ≥0 → Ω → ℝ} {VR : Fin (flowLineNR b J 0) → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζα : Ω → ℝ≥0∞} {α : Ω → ℝ≥0 → ℂ}
    (htr : ∀ ω, IsTranslateAddConst 0 (θ * chiC κ) (h ω) (X ω))
    (hC : IsOptionalHullCoupling κ (flowLineXL b J 0) (flowLineXR b J 0) (flowLineRhoL κ b J 0 θ)
      (flowLineRhoR κ b J 0 θ) P 𝓕 Wα VL VR B ζα X)
    (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω))
    (hX : IsMeasurableKilledDriving Wα VL VR ζα) {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime (drivingFiltration P hX) τ) (hτζ : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζα ω)
    (hτt : ∀ ω, τ ω ≠ ⊤) {u₀ : ℂ → ℝ}
    (hu₀ : IsBoundedHarmonicExtension (forceBoundaryData κ (flowLineRhoL κ b J 0 θ) (flowLineRhoR κ b J 0 θ)
      (flowLineXL b J 0) (flowLineXR b J 0)) (forceJumpSet (flowLineXL b J 0) (flowLineXR b J 0)) u₀) :
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
                (H \ (A ω ∪ K ω)) := by
  classical
  have hh0 : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField X u₀) P :=
    isZeroBoundaryGFF_centredField hC hu₀
  have hσζ : ∀ᵐ ω ∂P, (σ ω : ℝ≥0∞) < ζ ω := by
    filter_upwards [hcomp] with ω hc
    rw [hc.1]
    exact lt_top_iff_ne_top.2 (hσt ω)
  -- the retained side
  obtain ⟨A, hAm, hAG, hAe, hAst, hAd, hlocA, hlA, hmean⟩ :=
    exists_retained_gw2_stop h12 h13 hκ hb hG hT htr' hC' hX' hσ hσt hσζ htr hu₀
  -- the explored side
  have hdetα := Exist.Param12.hasFieldDeterminedHistories h12 h13 hκ
    (Theorem15.isOrderedForceWord_flowLine b J 0) P 𝓕 Wα VL VR B ζα X hC
  obtain ⟨K, hKτ, hKe, hKc, hτd, hlocK⟩ := exists_flowHull_marks hκ hC hdetα hu₀ hh0 hX hτ hτζ hτt
  have hKm : Measurable[mΩ, hittingSigma] K := hKτ.mono hτ.measurableSpace_le le_rfl
  -- the union
  have hUloc := WalkLaw.isHistoryAvoidanceLocal_union_of_det hh0.measurable
    (fun U hUH => hAst (measurableSet_avoid U.isOpen hUH))
    (fun U hUH => hKτ (measurableSet_avoid U.isOpen hUH)) hAd hτd hlocA hlocK
  have hUm : Measurable[mΩ, hittingSigma] (fun ω => A ω ∪ K ω) := measurable_union_hitting hAm hKm
  have hUc : ∀ᵐ ω ∂P, A ω ∪ K ω ⊆ H ∧ IsOpen (H \ (A ω ∪ K ω)) := by
    filter_upwards [hKc] with ω hK
    refine ⟨union_subset (hAG ω).1 hK.1, ?_⟩
    have e : H \ (A ω ∪ K ω) = (H \ A ω) ∩ (H \ K ω) := by
      ext z
      simp only [Set.mem_sdiff, Set.mem_union, Set.mem_inter_iff]
      tauto
    rw [e]
    exact (hAG ω).2.inter hK.2
  have hlU : IsLocalSet (fun ω => A ω ∪ K ω) (centredField X u₀) P :=
    ((isLocalSet_tfae hh0 hUm hUc).out 4 1).2 hUloc.isAvoidanceLocal
  refine ⟨A, K, hAm, hKm, hAe, hKe, hlU, fun g hg => ?_⟩
  -- the two individual means
  have hAc : ∀ᵐ ω ∂P, A ω ⊆ H ∧ IsOpen (H \ A ω) := Eventually.of_forall hAG
  obtain ⟨g₁, hg₁⟩ := isGermConditionalLaw_iff.1
    (IsAvoidanceLocal.isGermConditionalLaw hh0 hAm hAc (((isLocalSet_tfae hh0 hAm hAc).out 4 1).1 hlA))
  obtain ⟨hX'', hker⟩ := hC.2.2.2
  have hlK : IsLocalSet K (centredField X u₀) P := by
    refine Coupling.IsLocalSet.congr_set
      (WholeField.IsLocalSet.sub_dist (hker τ hτ hτζ).1 (WholeField.isHarmonicDistOn_smoothDist hu₀.1)) ?_
    filter_upwards [hKe] with ω hω
    simp only [hω]
  obtain ⟨g₂, hg₂⟩ := isGermConditionalLaw_iff.1
    (IsAvoidanceLocal.isGermConditionalLaw hh0 hKm hKc (((isLocalSet_tfae hh0 hKm hKc).out 4 1).1 hlK))
  -- the two curves
  have hWα : ∀ᵐ ω ∂P, Wα 0 ω = 0 ∧ ContinuousOn (fun t => Wα t ω) {t | (t : ℝ≥0∞) < ζα ω} := by
    filter_upwards [hC.1.2.2.2.2] with ω hp
    exact ⟨hp.1, hp.2.2.2.1⟩
  have hcf : IsFlowLineDriver (16 / κ) c'.fn c'.jumps 0 P h' W ζ := ⟨h₁, 𝓕', VL', VR', B', htr', hC'⟩
  have hdrv := ae_driver_zero_continuousOn hcf
  have hW : ∀ᵐ ω ∂P, Continuous (fun t => W t ω) ∧ W 0 ω = 0 ∧ IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω) := by
    filter_upwards [hdrv, hcomp] with ω hω hc
    have hcont : ContinuousOn (fun t => W t ω) {t : ℝ≥0 | (t : ℝ≥0∞) < ζ ω} := hω.2
    rw [hc.1] at hcont
    exact ⟨continuousOn_univ.1 (hcont.mono fun t _ => ENNReal.coe_lt_top), hω.1, hc.2⟩
  have hNR' : ∀ᵐ ω ∂P, ∀ v : ℝ≥0, 0 < v → v ≤ (fun ω => (σ ω).untopD 0) ω → γ ω v ≠ 0 := by
    filter_upwards [hNR] with ω hω v hv _
    exact hω v hv
  have hunbA : ∀ᵐ ω ∂P, ∀ z ∈ lowerUnion (A ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (A ω)) z) := by
    filter_upwards [hAe, hW] with ω hω hWω
    rw [hω]
    exact Sec5.GlueCond.not_isBounded_lowerUnion_image_negInv
      (isHPHull_fwdHull (hWω.1.comp continuous_real_toNNReal) ((σ ω).untopD 0 : ℝ≥0).coe_nonneg)
  have hdA : MeasurableSpace.comap A hittingSigma ≤
      aeSigma (MeasurableSpace.comap (centredField X u₀) inferInstance) P :=
    (measurable_iff_comap_le.1 hAst).trans hAd
  have hmain := ae_eqOn_unionMean_invHull_stop hκ (Theorem14.GW3Word.flowLineXL_nonpos b J)
    (Theorem14.GW3Word.flowLineXR_nonneg b J) hC hWα hα hW (fun ω => (σ ω).untopD 0) hNR' hu₀ hh0 hX hτ hτζ univ
    (A := A) (by filter_upwards [hAe] with ω hω _; exact hω) hunbA hKe hAm hKm hdA hlA hlU hg hg₁ hg₂
    (nL' := fun ω => flowLineNL (jointWordOfRec (specOffset κ) κ c' (cfRec ((σ ω).untopD 0 : ℝ≥0) W ζ ω)).fn
      (jointWordOfRec (specOffset κ) κ c' (cfRec ((σ ω).untopD 0 : ℝ≥0) W ζ ω)).jumps 0)
    (nR' := fun ω => flowLineNR (jointWordOfRec (specOffset κ) κ c' (cfRec ((σ ω).untopD 0 : ℝ≥0) W ζ ω)).fn
      (jointWordOfRec (specOffset κ) κ c' (cfRec ((σ ω).untopD 0 : ℝ≥0) W ζ ω)).jumps 0)
    (ρL' := fun ω => flowLineRhoL κ (jointWordOfRec (specOffset κ) κ c' (cfRec ((σ ω).untopD 0 : ℝ≥0) W ζ ω)).fn
      (jointWordOfRec (specOffset κ) κ c' (cfRec ((σ ω).untopD 0 : ℝ≥0) W ζ ω)).jumps 0 θ)
    (ρR' := fun ω => flowLineRhoR κ (jointWordOfRec (specOffset κ) κ c' (cfRec ((σ ω).untopD 0 : ℝ≥0) W ζ ω)).fn
      (jointWordOfRec (specOffset κ) κ c' (cfRec ((σ ω).untopD 0 : ℝ≥0) W ζ ω)).jumps 0 θ)
    (yL := fun ω => flowLineXL (jointWordOfRec (specOffset κ) κ c' (cfRec ((σ ω).untopD 0 : ℝ≥0) W ζ ω)).fn
      (jointWordOfRec (specOffset κ) κ c' (cfRec ((σ ω).untopD 0 : ℝ≥0) W ζ ω)).jumps 0)
    (yR := fun ω => flowLineXR (jointWordOfRec (specOffset κ) κ c' (cfRec ((σ ω).untopD 0 : ℝ≥0) W ζ ω)).fn
      (jointWordOfRec (specOffset κ) κ c' (cfRec ((σ ω).untopD 0 : ℝ≥0) W ζ ω)).jumps 0)
    (fun ω => Theorem14.GW3Word.flowLineXL_nonpos _ _) (fun ω => Theorem14.GW3Word.flowLineXR_nonneg _ _)
    (by
      filter_upwards [hmean g₁ hg₁] with ω hω _ _ G₀ hG₀ w₁ hw₁ hr₁
      have hG₀' : IsBoundedHarmonicExtension
          (cfData κ (jointWordOfRec (specOffset κ) κ c' (cfRec ((σ ω).untopD 0 : ℝ≥0) W ζ ω)).fn
            (jointWordOfRec (specOffset κ) κ c' (cfRec ((σ ω).untopD 0 : ℝ≥0) W ζ ω)).jumps)
          (cfJumps (jointWordOfRec (specOffset κ) κ c' (cfRec ((σ ω).untopD 0 : ℝ≥0) W ζ ω)).fn
            (jointWordOfRec (specOffset κ) κ c' (cfRec ((σ ω).untopD 0 : ℝ≥0) W ζ ω)).jumps)
          (fun z => G₀ z - θ * chiC κ) :=
        isBoundedHarmonicExtension_sub_const' hG₀ fun x => by
          rw [cfData, Sec5.RestartGen.forceBoundaryData_flowLine_angle hκ _ _ θ 0 x]
          ring
      intro z hz
      have h1 := hω _ hG₀' w₁ hw₁ hr₁ hz
      simp only at h1 ⊢
      linarith)
  filter_upwards [hmain] with ω hω hsH hT0 hTc
  exact hω trivial hsH hT0 hTc

end InteractingSLE.Theorem14.GW2Stm
