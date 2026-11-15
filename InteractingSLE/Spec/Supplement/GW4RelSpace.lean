/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6RelDrv
import InteractingSLE.Spec.Supplement.GW4LawProofReg

/-!
# Theorem GW4's component (Det): the relative stopped coupling

Packet PROVE-GW4-RELLAW. `GW4Reg.GW4RelativeLawRegStatement` (Theorem GW4, "The full kernel and the one phase",
pp. 638–639) asks, conditionally on the two boundary walks, for a centred counterflow of the component field `h_C`,
with infinite lifetime, generating the relative hulls `A(t) = Φ(K'_t ∩ R⁻¹(C))` of the ambient counterflow. Its
proof (`GW4RelLaw.lean`) uses Aux. lemma 54, Theorems 1.2–1.3, GW3's word bounds and the pocket geometry; the one
probabilistic input left is the relative stopped coupling, which is the conclusion of Astra's follow-up 3, Q3, for the
selected GW4 component (R69: "proved for the GB6 and GW4 configurations once their relative continuous chain is
supplied"), stated here in the form of GB6's `RelDrv.GB6RelStopKernelStatement`:

* `relHullFam c C w t = Φ(K^w_t ∩ R⁻¹(C))`: the relative hull family of an ambient driver;
* `invField κ f = returnField (πχ) χ f`: the component field read in the inverted (counterflow) chart, the field of the
  centred counterflow (`BRLeaf.isCenteredCounterflowDriver_cfDrv`);
* `IsGW4RelVersion ν W' c C R V`: `R` is a measurable continuous driver from `0` and `V` a measurable stop such that,
  `ν`-almost surely, every hull of `R` before `V` is a relative hull `A(t)` of the ambient counterflow;
* **`GW4RelStopCouplingStatement`** (named input): in the setting of `GW4RelativeLawRegStatement`, for every word `c₀`
  of the counterflow data of the component, there are measurable versions `(R m, V m)` of the relative traversal whose
  stops exhaust it (every bounded relative hull is reached before some `V m`), and for each `m` the relative traversal
  is, under the conditional law `ν`, a coupling through the stop `V m` of the inverted component field with the
  counterflow word of `c₀` (`StoppedExtend.IsStoppedHullCoupling` at `16/κ`, angle `0`), read on GB6's canonical space
  `RelSpace` (with independent noise `P₀` for the Brownian motion after the stop);
* the GB6-style split of that input (`RelDrv.GB6RelVersionStatement` / `GB6RelStopKernelStatement`):
  `IsGW4RelStopVersion` (a version through a stopping time of the relative path's filtration),
  `GW4RelVersionStatement` (exhausting such versions exist; measurability only), `GW4RelStopKernelStatement` (every
  such version is a coupling through its stop), and `gw4RelStopCouplingStatement_of_version_kernel`.

Source: Astra's follow-up 3, Q3 §§3.1–3.7 (`source/external/AstraIG1/ig1_followup3_audited.txt` L639–L1047): "For
each `G`-stopping time `S < ζ`, the conditional field outside `K̃_S`, given `G_S`, is Gaussian with zero-boundary Green
covariance and canonical mean (Q3.3)", (Q3.6)–(Q3.9) with `δ_u = 0` by Aux. 122 for the GW4 seed bounds, and the
integrated equations (Q3.4); the specification's GW4 proof, p. 638–639 ("The marked union and optional local-set law
preserve the entire initial GW3 kernel … This proves the full active Poisson mean and covariance … That lemma forces
`δ_s = 0` and identifies the canonical integrated finite-word system").
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull chiC)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW4Rel

open GW4Traverse Supp8.GB6.RelDrv Restart Restart.StoppedExtend Sec7.StripSysField

/-- **The relative hull family** `A(t) = Φ(K^w_t ∩ R⁻¹(C))` of an ambient driver `w` in the component `C`, read in
the relative chart `Φ = relMapC c`. -/
def relHullFam (c : Chart) (C : Set ℂ) (w : ℝ≥0 → ℝ) (t : ℝ≥0) : Set ℂ :=
  relMapC c '' (fwdHull (fun r : ℝ => w r.toNNReal) t ∩ relDom C)

/-- The relative hull family is monotone in time. -/
theorem monotone_relHullFam (c : Chart) (C : Set ℂ) (w : ℝ≥0 → ℝ) : Monotone (relHullFam c C w) := by
  intro t₁ t₂ ht
  exact image_mono (inter_subset_inter_left _ (QuantumZipper.fwdHull_mono.1 (NNReal.coe_le_coe.2 ht)))

/-- **The component field in the inverted (counterflow) chart**: `returnField (πχ) χ f`, the field read by the
centred counterflow of `f` (the infinity-source transport with coefficients `(−1, −πχ, χ(16/κ))`,
`GW2JointKernel.isChartTransport_infinitySourceChart_returnField`). -/
def invField (κ : ℝ) (f : DistOn upperHalfPlaneOpens) : DistOn upperHalfPlaneOpens :=
  returnField (Real.pi * chiC κ) (chiC κ) f

theorem measurable_invField (κ : ℝ) : Measurable (invField κ) :=
  measurable_returnField _ _

/-- **A measurable version of the relative traversal through a stop** (under a measure `ν`): `R` is a measurable
continuous driver from `0`, `V` a measurable stop, and `ν`-almost surely every hull of `R` at a relative time before
`V` is one of the relative hulls `A(t) = Φ(K'_t ∩ R⁻¹(C))` of the ambient counterflow driver `W'`. -/
def IsGW4RelVersion {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) (W' : ℝ≥0 → Ω → ℝ) (c : Chart) (C : Set ℂ)
    (R : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞) : Prop :=
  (∀ t, Measurable (R t)) ∧ (∀ ω, Continuous fun t => R t ω) ∧ (∀ ω, R 0 ω = 0) ∧ Measurable V ∧
    ∀ᵐ ω ∂ν, ∀ s : ℝ≥0, (s : ℝ≥0∞) < V ω → ∃ t : ℝ≥0,
      fwdHull (fun r : ℝ => R r.toNNReal ω) s = relHullFam c C (fun u => W' u ω) t

/-- **Named input: Theorem GW4's relative stopped coupling** (Astra's follow-up 3, Q3, for the selected GW4
component; supplement pp. 638–639). Binders of `GW4Reg.GW4RelativeLawRegStatement` verbatim, then a sorted word `c₀`
of the counterflow data `(counterflowData κ bC, counterflowJumps jumpsC)` of the component field. There are measurable
versions `(R m, V m)` of the relative traversal (`IsGW4RelVersion`) such that `ν`-almost surely every bounded relative
hull `A(t)` is the hull of some `R m` at a relative time before `V m` (the stops exhaust the traversal), and for every
`m`, on GB6's canonical space `RelSpace × Ω₀` under `(ν.map (field, R m, V m)) ⊗ P₀`, the relative driver is a coupling
through the stop `V m` of the inverted component field with the counterflow word of `c₀`
(`StoppedExtend.IsStoppedHullCoupling` at `16/κ`, angle `0`). -/
def GW4RelStopCouplingStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
      let wR := boundaryWalkSpec b jumps (-(Real.pi / 2)) true
      let wL := boundaryWalkSpec b jumps (Real.pi / 2) false
      ∀ᵐ ω₀ ∂P,
        let R := ExplState.physSet κ b jumps wR (fun k => E wR k ω₀)
        let L := ExplState.physSet κ b jumps wL (fun k => E wL k ω₀)
        let ν := condExpKernel P
          (pastSigma κ b jumps wR (E wR) wR.2.2.length ⊔ pastSigma κ b jumps wL (E wL) wL.2.2.length) ω₀
        ∀ C ∈ betweenComponents R L, ∀ (c : Chart) (hC : Ω → LQGMetric.DistOn upperHalfPlaneOpens)
            (bC : ℝ → ℝ) (jumpsC : Finset ℝ),
          IsComponentChart R L C c →
          (∀ ω, IsChartTransport c 1 0 (QuantumZipper.chiC κ) (h ω) (hC ω)) →
          IsPiecewiseConstantBoundaryData bC jumpsC →
          IsComponentBoundaryData κ b (ExplState.ordinarySet κ b jumps wR (fun k => E wR k ω₀))
            (ExplState.ordinarySet κ b jumps wL (fun k => E wL k ω₀)) c.2.1 bC jumpsC →
          IsGFFWithBoundaryData ν hC bC jumpsC →
          ∀ c₀ : BoundaryWord, c₀.IsSorted → c₀.jumps = counterflowJumps jumpsC →
            (∀ y ∉ c₀.jumps, c₀.fn y = counterflowData κ bC y) →
          ∃ (Rv : ℕ → ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ≥0∞),
            (∀ m, IsGW4RelVersion ν W' c C (Rv m) (V m)) ∧
            (∀ᵐ ω ∂ν, ∀ t : ℝ≥0, Bornology.IsBounded (relHullFam c C (fun u => W' u ω) t) →
              ∃ m, ∃ s : ℝ≥0, (s : ℝ≥0∞) < V m ω ∧
                fwdHull (fun r : ℝ => Rv m r.toNNReal ω) s = relHullFam c C (fun u => W' u ω) t) ∧
            ∀ m, ∃ (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (P₀ : Measure Ω₀) (_ : IsProbabilityMeasure P₀)
              (𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (RelSpace × Ω₀)))
              (VL : Fin (flowLineNL c₀.fn c₀.jumps 0) → ℝ≥0 → RelSpace × Ω₀ → ℝ)
              (VR : Fin (flowLineNR c₀.fn c₀.jumps 0) → ℝ≥0 → RelSpace × Ω₀ → ℝ)
              (B : ℝ≥0 → RelSpace × Ω₀ → ℝ),
              IsStoppedHullCoupling (16 / κ) (flowLineXL c₀.fn c₀.jumps 0) (flowLineXR c₀.fn c₀.jumps 0)
                (flowLineRhoL (16 / κ) c₀.fn c₀.jumps 0 0) (flowLineRhoR (16 / κ) c₀.fn c₀.jumps 0 0)
                ((ν.map (relVar (fun ω => invField κ (hC ω)) (Rv m) (V m))).prod P₀) 𝓕
                (fun t p => relDrv t p.1) VL VR B (fun p => relStp p.1) (fun p => relFld p.1)

/-! ### The GB6-style split: measurable versions and the stopped kernel -/

/-- A set of paths determined by the path up to time `t`. -/
def IsPathDetUpTo (t : ℝ≥0) (B : Set (ℝ≥0 → ℝ)) : Prop :=
  ∀ w w' : ℝ≥0 → ℝ, (∀ u ≤ t, w u = w' u) → (w ∈ B ↔ w' ∈ B)

/-- **A measurable version of the relative traversal through a stopping time** (the GW4 form of GB6's
`RelDrv.IsGB6RelVersion`): `IsGW4RelVersion`, `R` frozen after `V`, and `V` a stopping time of the `ν`-completed
natural filtration of `R` (for every `t`, `ν`-almost surely `{V ≤ t}` is a measurable event of the path on `[0, t]`).
Under `ν` the walks are almost surely those of the conditioning sample, so this is the relative filtration of the
source (Astra's follow-up 3, (Q3.2)) up to null sets. -/
def IsGW4RelStopVersion {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) (W' : ℝ≥0 → Ω → ℝ) (c : Chart)
    (C : Set ℂ) (R : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞) : Prop :=
  IsGW4RelVersion ν W' c C R V ∧ (∀ ω (t : ℝ≥0), V ω ≤ t → R t ω = R (V ω).toNNReal ω) ∧
    ∀ t : ℝ≥0, ∃ B : Set (ℝ≥0 → ℝ), MeasurableSet B ∧ IsPathDetUpTo t B ∧
      ∀ᵐ ω ∂ν, (V ω ≤ t ↔ (fun u => R u ω) ∈ B)

/-- **Named input (measurability): exhausting measurable versions of the relative traversal exist** (the GW4 form of
GB6's `RelDrv.GB6RelVersionStatement`). Binders of `GW4RelStopCouplingStatement` up to the component data. -/
def GW4RelVersionStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
      let wR := boundaryWalkSpec b jumps (-(Real.pi / 2)) true
      let wL := boundaryWalkSpec b jumps (Real.pi / 2) false
      ∀ᵐ ω₀ ∂P,
        let R := ExplState.physSet κ b jumps wR (fun k => E wR k ω₀)
        let L := ExplState.physSet κ b jumps wL (fun k => E wL k ω₀)
        let ν := condExpKernel P
          (pastSigma κ b jumps wR (E wR) wR.2.2.length ⊔ pastSigma κ b jumps wL (E wL) wL.2.2.length) ω₀
        ∀ C ∈ betweenComponents R L, ∀ (c : Chart) (hC : Ω → LQGMetric.DistOn upperHalfPlaneOpens)
            (bC : ℝ → ℝ) (jumpsC : Finset ℝ),
          IsComponentChart R L C c →
          (∀ ω, IsChartTransport c 1 0 (QuantumZipper.chiC κ) (h ω) (hC ω)) →
          IsPiecewiseConstantBoundaryData bC jumpsC →
          IsComponentBoundaryData κ b (ExplState.ordinarySet κ b jumps wR (fun k => E wR k ω₀))
            (ExplState.ordinarySet κ b jumps wL (fun k => E wL k ω₀)) c.2.1 bC jumpsC →
          IsGFFWithBoundaryData ν hC bC jumpsC →
          ∃ (Rv : ℕ → ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ≥0∞),
            (∀ m, IsGW4RelStopVersion ν W' c C (Rv m) (V m)) ∧
            ∀ᵐ ω ∂ν, ∀ t : ℝ≥0, Bornology.IsBounded (relHullFam c C (fun u => W' u ω) t) →
              ∃ m, ∃ s : ℝ≥0, (s : ℝ≥0∞) < V m ω ∧
                fwdHull (fun r : ℝ => Rv m r.toNNReal ω) s = relHullFam c C (fun u => W' u ω) t

/-- **Named input: the relative stopped kernel** (the GW4 form of GB6's `RelDrv.GB6RelStopKernelStatement`; Astra's
follow-up 3, Q3): for every measurable version `(R, V)` of the relative traversal through a stopping time, the
relative driver is a coupling through the stop of the inverted component field with the counterflow word. -/
def GW4RelStopKernelStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
      let wR := boundaryWalkSpec b jumps (-(Real.pi / 2)) true
      let wL := boundaryWalkSpec b jumps (Real.pi / 2) false
      ∀ᵐ ω₀ ∂P,
        let R := ExplState.physSet κ b jumps wR (fun k => E wR k ω₀)
        let L := ExplState.physSet κ b jumps wL (fun k => E wL k ω₀)
        let ν := condExpKernel P
          (pastSigma κ b jumps wR (E wR) wR.2.2.length ⊔ pastSigma κ b jumps wL (E wL) wL.2.2.length) ω₀
        ∀ C ∈ betweenComponents R L, ∀ (c : Chart) (hC : Ω → LQGMetric.DistOn upperHalfPlaneOpens)
            (bC : ℝ → ℝ) (jumpsC : Finset ℝ),
          IsComponentChart R L C c →
          (∀ ω, IsChartTransport c 1 0 (QuantumZipper.chiC κ) (h ω) (hC ω)) →
          IsPiecewiseConstantBoundaryData bC jumpsC →
          IsComponentBoundaryData κ b (ExplState.ordinarySet κ b jumps wR (fun k => E wR k ω₀))
            (ExplState.ordinarySet κ b jumps wL (fun k => E wL k ω₀)) c.2.1 bC jumpsC →
          IsGFFWithBoundaryData ν hC bC jumpsC →
          ∀ c₀ : BoundaryWord, c₀.IsSorted → c₀.jumps = counterflowJumps jumpsC →
            (∀ y ∉ c₀.jumps, c₀.fn y = counterflowData κ bC y) →
          ∀ (Rv : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞), IsGW4RelStopVersion ν W' c C Rv V →
            ∃ (Ω₀ : Type) (_ : MeasurableSpace Ω₀) (P₀ : Measure Ω₀) (_ : IsProbabilityMeasure P₀)
              (𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace (RelSpace × Ω₀)))
              (VL : Fin (flowLineNL c₀.fn c₀.jumps 0) → ℝ≥0 → RelSpace × Ω₀ → ℝ)
              (VR : Fin (flowLineNR c₀.fn c₀.jumps 0) → ℝ≥0 → RelSpace × Ω₀ → ℝ)
              (B : ℝ≥0 → RelSpace × Ω₀ → ℝ),
              IsStoppedHullCoupling (16 / κ) (flowLineXL c₀.fn c₀.jumps 0) (flowLineXR c₀.fn c₀.jumps 0)
                (flowLineRhoL (16 / κ) c₀.fn c₀.jumps 0 0) (flowLineRhoR (16 / κ) c₀.fn c₀.jumps 0 0)
                ((ν.map (relVar (fun ω => invField κ (hC ω)) Rv V)).prod P₀) 𝓕
                (fun t p => relDrv t p.1) VL VR B (fun p => relStp p.1) (fun p => relFld p.1)

/-- **The merged input from the split**: exhausting versions through stopping times and the stopped kernel give
`GW4RelStopCouplingStatement`. -/
theorem gw4RelStopCouplingStatement_of_version_kernel (hV : GW4RelVersionStatement.{u})
    (hK : GW4RelStopKernelStatement.{u}) : GW4RelStopCouplingStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg wR wL
  filter_upwards [hV κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg,
    hK κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg] with ω₀ hVω hKω
  intro R L ν C hCm c hC bC jumpsC hch htr hpc hbd hgff c₀ hc₀s hc₀J hc₀
  obtain ⟨Rv, V, hver, hexh⟩ := hVω C hCm c hC bC jumpsC hch htr hpc hbd hgff
  exact ⟨Rv, V, fun m => (hver m).1, hexh, fun m =>
    hKω C hCm c hC bC jumpsC hch htr hpc hbd hgff c₀ hc₀s hc₀J hc₀ (Rv m) (V m) (hver m)⟩

end GW4Rel

end Theorem14

end InteractingSLE
