/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2JointKernelProofC
import InteractingSLE.Spec.Restart.DomainMarkovLocKer

/-!
# GW2's (Det) clause: the hull identity holds only before the flow's lifetime

Packet PROVE-T14-GW2DET. `GW2JointDetCStatement` (PROVE-T14-TIP10) asserts, almost surely on `{γ(s) ∈ ℍ}`, the hull
identity `K^F_{relClock t} = relMap(K^α_t)` for **every** `t` before the first contact of `α` with the inverted
counterflow prefix, with no restriction `t < ζα`. But `IsFlowLineDriver κ b J θ P h Wα ζα` constrains `Wα` only before
its lifetime `ζα` (`StagedReg.isFlowLineDriver_congr_ae`: every measurable process agreeing with `Wα` before `ζα` is
again a flow-line driver), and `IsGeneratingTrace (Wα · ω) (ζα ω) (α ω)` constrains `α` only on `[0, ζα]`. On the
event `{ζα = 0}` (an inadmissible seed, which GW2 allows: "If instead the lower extreme is immediately inadmissible",
p. 621; e.g. `b(0⁺) = −λ` at `θ = 0`) the statement therefore asserts the hull identity for an **arbitrary**
deterministic continuous driver `U` with `U 0 = 0` and the constant path `α ≡ 0` (whose first contact time is `⊤`):
`gw2JointDetC_forall_driver` proves exactly this consequence. Since the left side does not depend on `U` and is a
nested family (`fwdHull_mono`), two drivers whose hulls are not nested (e.g. `±r`, mirror images) contradict it, so
`GW2JointDetCStatement` is false as soon as `P(γ(s) ∈ ℍ, ζα = 0) > 0` for one admissible configuration. The same applies
to TIP10's `GW2JointKernelCStatement` (its last clause is the same hull identity).

**Fix (this file).** The corrected statements add `(t : ℝ≥0∞) < ζα ω` to the hull clause (the source's GB9 compares the
pieces only while they are alive: "Before a new flow prefix first meets the retained counterflow …", p. 525, for an
available flow prefix):

* **`GW2JointDetC2Statement`**, **`GW2JointKernelC2Statement`** (the corrected named statements);
* `gw2JointDetC2Statement_of_detC` (the corrected statement is weaker);
* **`gw2JointKernelC2Statement_of_detC2`** (TIP10's (R1) + (Det) wiring, re-run);
* **`exists_condExpKernel_jointFlowLineC2`** (TIP9's conditional-law form, re-run).

Conditional helpers with distinct names; they replace no source theorem. R48: serves Theorem 1.4 only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (TestOn DistOn)

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW2JointKernel

open Restart Exist.StagedLaw Sec7.StripSysField Supp8.GB6

/-! ### The corrected statements -/

/-- **Named input: the corrected (Det) clause** (`GW2JointDetCStatement` with the hull identity required only before
the flow's lifetime `ζα`; everything else verbatim). -/
def GW2JointDetC2Statement : Prop :=
  ∀ (κ θ : ℝ), 0 < κ → κ < 4 → -(Real.pi / 2) ≤ θ → θ ≤ Real.pi / 2 →
  ∀ (Ω : Type u) (_mΩ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (b : ℝ → ℝ) (J : Finset ℝ)
    (W Wα : ℝ≥0 → Ω → ℝ) (ζ ζα : Ω → ℝ≥0∞) (γ α : Ω → ℝ≥0 → ℂ)
    (b' : ℝ → ℝ) (J' : Finset ℝ) (h' : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
    IsPiecewiseConstantBoundaryData b J → IsGFFWithBoundaryData P h b J →
    IsPiecewiseConstantBoundaryData b' J' →
    (∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * QuantumZipper.chiC κ))
      (QuantumZipper.chiC (16 / κ)) (h ω) (h' ω)) →
    IsFlowLineDriver (16 / κ) b' J' 0 P h' W ζ →
    (∀ i : Fin (flowLineNL b' J' 0),
      -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ i), flowLineRhoL (16 / κ) b' J' 0 0 l) →
    (∀ i : Fin (flowLineNR b' J' 0),
      -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ i), flowLineRhoR (16 / κ) b' J' 0 0 l) →
    (∀ᵐ ω ∂P, ζ ω = ⊤ ∧ IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω) ∧
      Tendsto (fun t => ‖γ ω t‖) atTop atTop) →
    IsFlowLineDriver κ b J θ P h Wα ζα →
    (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω)) →
    ∀ (s : ℝ≥0) (Hc : Ω → LQGMetric.DistOn upperHalfPlaneOpens), Measurable Hc →
    (∀ᵐ ω ∂P, γ ω s ∈ H →
      IsChartTransport (jointChart (fun r : ℝ => W r.toNNReal ω) s) 1 (specOffset κ) (QuantumZipper.chiC κ)
        (h ω) (Hc ω)) →
    ∀ F : BoundaryWord × LQGMetric.DistOn upperHalfPlaneOpens → Sec2.Assembly.PCode × ℝ≥0∞,
      IsCanonicalDriverCode κ θ F →
    ∀ c' : BoundaryWord, c'.jumps = J' → (∀ y ∉ J', c'.fn y = b' y) →
      ∀ᵐ ω ∂P, γ ω s ∈ H →
        IsGoodDrvCode (F (jointWord (specOffset κ) κ c' s (fun t => W t ω), Hc ω)) ∧
        ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζα ω → (t : ℝ≥0∞) < firstContactTime (fun t => (α ω t : OnePoint ℂ))
            ((fun r => sphereInv (γ ω r : OnePoint ℂ)) '' Icc 0 s) →
          QuantumZipper.fwdHull
              (fun r : ℝ => drvDec (F (jointWord (specOffset κ) κ c' s (fun t => W t ω), Hc ω)) r.toNNReal)
              (relClock (fun r : ℝ => W r.toNNReal ω) s (fun r : ℝ => Wα r.toNNReal ω) t) =
            relMap (fun r : ℝ => W r.toNNReal ω) s '' QuantumZipper.fwdHull (fun r : ℝ => Wα r.toNNReal ω) t

/-- **Named input: the corrected pre-contact kernel** (`GW2JointKernelCStatement` with the hull identity required only
before the flow's lifetime `ζα`; everything else verbatim). -/
def GW2JointKernelC2Statement : Prop :=
  ∀ (κ θ : ℝ), 0 < κ → κ < 4 → -(Real.pi / 2) ≤ θ → θ ≤ Real.pi / 2 →
  ∀ (Ω : Type u) (mΩ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
  ∀ (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (b : ℝ → ℝ) (J : Finset ℝ)
    (W Wα : ℝ≥0 → Ω → ℝ) (ζ ζα : Ω → ℝ≥0∞) (γ α : Ω → ℝ≥0 → ℂ)
    (b' : ℝ → ℝ) (J' : Finset ℝ) (h' : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
    IsPiecewiseConstantBoundaryData b J → IsGFFWithBoundaryData P h b J →
    IsPiecewiseConstantBoundaryData b' J' →
    (∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * QuantumZipper.chiC κ))
      (QuantumZipper.chiC (16 / κ)) (h ω) (h' ω)) →
    IsFlowLineDriver (16 / κ) b' J' 0 P h' W ζ →
    (∀ i : Fin (flowLineNL b' J' 0),
      -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ i), flowLineRhoL (16 / κ) b' J' 0 0 l) →
    (∀ i : Fin (flowLineNR b' J' 0),
      -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ i), flowLineRhoR (16 / κ) b' J' 0 0 l) →
    (∀ᵐ ω ∂P, ζ ω = ⊤ ∧ IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω) ∧
      Tendsto (fun t => ‖γ ω t‖) atTop atTop) →
    IsFlowLineDriver κ b J θ P h Wα ζα →
    (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω)) →
    ∀ (s : ℝ≥0) (Hc : Ω → LQGMetric.DistOn upperHalfPlaneOpens), Measurable Hc →
    (∀ᵐ ω ∂P, γ ω s ∈ H →
      IsChartTransport (jointChart (fun r : ℝ => W r.toNNReal ω) s) 1 (specOffset κ) (QuantumZipper.chiC κ)
        (h ω) (Hc ω)) →
    ∀ F : BoundaryWord × LQGMetric.DistOn upperHalfPlaneOpens → Sec2.Assembly.PCode × ℝ≥0∞,
      IsCanonicalDriverCode κ θ F →
    ∃ (𝒢 : {m : MeasurableSpace Ω // m ≤ mΩ}) (M : Set Ω) (β : Ω → BoundaryWord),
      MeasurableSet[𝒢.1] M ∧ Measurable[𝒢.1] β ∧
      (∀ᵐ ω ∂P, ω ∈ M → (β ω).IsSorted ∧ IsGoodDrvCode (F (β ω, Hc ω))) ∧
      (∀ φ : LQGMetric.TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ M →
        P[fun ω' => Complex.exp (Complex.I * (Hc ω' φ : ℂ)) | 𝒢.1] ω = gaussCF (β ω) φ) ∧
      ∀ᵐ ω ∂P, γ ω s ∈ H →
        ω ∈ M ∧
        ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζα ω → (t : ℝ≥0∞) < firstContactTime (fun t => (α ω t : OnePoint ℂ))
            ((fun r => sphereInv (γ ω r : OnePoint ℂ)) '' Icc 0 s) →
          QuantumZipper.fwdHull (fun r : ℝ => drvDec (F (β ω, Hc ω)) r.toNNReal)
              (relClock (fun r : ℝ => W r.toNNReal ω) s (fun r : ℝ => Wα r.toNNReal ω) t) =
            relMap (fun r : ℝ => W r.toNNReal ω) s '' QuantumZipper.fwdHull (fun r : ℝ => Wα r.toNNReal ω) t

/-- The corrected (Det) clause is weaker than TIP10's. -/
theorem gw2JointDetC2Statement_of_detC (hD : GW2JointDetCStatement.{u}) : GW2JointDetC2Statement.{u} := by
  intro κ θ hκ hκ4 hθ₁ hθ₂ Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h' hb hh hb' hT hcf hpL hpR hreg hfl hα s Hc
    hHcm hHc F hF c' hc'J hc'b
  filter_upwards [hD κ θ hκ hκ4 hθ₁ hθ₂ Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h' hb hh hb' hT hcf hpL hpR hreg hfl hα
    s Hc hHcm hHc F hF c' hc'J hc'b] with ω hω hsH
  exact ⟨(hω hsH).1, fun t _ ht => (hω hsH).2 t ht⟩

/-- **The corrected pre-contact kernel from its corrected (Det) clause** (TIP10's `gw2JointKernelCStatement_of_detC`,
same proof: (R1) is `exists_jointKernel_r1` at the offset `specOffset κ`). -/
theorem gw2JointKernelC2Statement_of_detC2 (hD : GW2JointDetC2Statement.{u}) : GW2JointKernelC2Statement.{u} := by
  intro κ θ hκ hκ4 hθ₁ hθ₂ Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h' hb hh hb' hT hcf hpL hpR hreg hfl hα s Hc
    hHcm hHc F hF
  obtain ⟨c', hc'J, hc'b⟩ := BoundaryWord.exists_fn_eq hb'
  have hζ : ∀ᵐ ω ∂P, ζ ω = ⊤ := hreg.mono fun ω hω => hω.1
  have hγ : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω) := hreg.mono fun ω hω => hω.2.1
  obtain ⟨𝒢, M, β, hM, hβ, hsort, hR1, hev⟩ :=
    exists_jointKernel_r1 hκ (specOffset κ) hh.1 hb' hT hcf hζ hγ s hHcm hHc hc'b
  have hDω := hD κ θ hκ hκ4 hθ₁ hθ₂ Ω mΩ P hP h b J W Wα ζ ζα γ α b' J' h' hb hh hb' hT hcf hpL hpR hreg hfl hα
    s Hc hHcm hHc F hF c' hc'J hc'b
  refine ⟨𝒢, M, β, hM, hβ, ?_, hR1, ?_⟩
  · filter_upwards [hev, hDω] with ω hevω hDω hωM
    refine ⟨hsort ω, ?_⟩
    rw [hevω.2]
    exact (hDω (hevω.1.2 hωM)).1
  · filter_upwards [hev, hDω] with ω hevω hDω hsH
    refine ⟨hevω.1.1 hsH, ?_⟩
    rw [hevω.2]
    exact (hDω hsH).2

/-- **The corrected pre-contact kernel in conditional-law form** (TIP10's `exists_condExpKernel_jointFlowLineC`, same
proof, from `GW2JointKernelC2Statement`; the hull clause only before the lifetime `ζα`). -/
theorem exists_condExpKernel_jointFlowLineC2 (hD : GW2JointKernelC2Statement.{u}) {κ θ : ℝ} (hκ : 0 < κ)
    (hκ4 : κ < 4) (hθ₁ : -(Real.pi / 2) ≤ θ) (hθ₂ : θ ≤ Real.pi / 2) {Ω : Type u} [mΩ : MeasurableSpace Ω]
    [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    {b : ℝ → ℝ} {J : Finset ℝ} {W Wα : ℝ≥0 → Ω → ℝ} {ζ ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ} {b' : ℝ → ℝ}
    {J' : Finset ℝ} {h' : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hb : IsPiecewiseConstantBoundaryData b J) (hG : IsGFFWithBoundaryData P h b J)
    (hb' : IsPiecewiseConstantBoundaryData b' J')
    (htr : ∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * QuantumZipper.chiC κ))
      (QuantumZipper.chiC (16 / κ)) (h ω) (h' ω))
    (hcf : IsFlowLineDriver (16 / κ) b' J' 0 P h' W ζ)
    (hadmL : ∀ i : Fin (flowLineNL b' J' 0),
      -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ i), flowLineRhoL (16 / κ) b' J' 0 0 l)
    (hadmR : ∀ i : Fin (flowLineNR b' J' 0),
      -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ i), flowLineRhoR (16 / κ) b' J' 0 0 l)
    (hcomp : ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω) ∧
      Tendsto (fun t => ‖γ ω t‖) atTop atTop)
    (hfl : IsFlowLineDriver κ b J θ P h Wα ζα)
    (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω)) (s : ℝ≥0)
    {Hc : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hHcm : Measurable Hc)
    (hHc : ∀ᵐ ω ∂P, γ ω s ∈ H →
      IsChartTransport (jointChart (fun r : ℝ => W r.toNNReal ω) s) 1 (specOffset κ) (QuantumZipper.chiC κ)
        (h ω) (Hc ω))
    {F : BoundaryWord × LQGMetric.DistOn upperHalfPlaneOpens → Sec2.Assembly.PCode × ℝ≥0∞}
    (hF : IsCanonicalDriverCode κ θ F) :
    ∃ (𝒢 : {m : MeasurableSpace Ω // m ≤ mΩ}) (M : Set Ω) (β : Ω → BoundaryWord),
      MeasurableSet[𝒢.1] M ∧ Measurable[𝒢.1] β ∧
      (∀ᵐ ω₀ ∂P, ω₀ ∈ M → (β ω₀).IsSorted ∧
        (condExpKernel P 𝒢.1 ω₀).map (fun ω => (Hc ω, F (β ω, Hc ω))) =
          (β ω₀).gffLaw.map (fun g => (g, F (β ω₀, g))) ∧
        IsFlowLineDriver κ (β ω₀).fn (β ω₀).jumps θ (β ω₀).gffLaw id
          (fun t g => drvDec (F (β ω₀, g)) t) (fun g => (F (β ω₀, g)).2)) ∧
      ∀ᵐ ω ∂P, γ ω s ∈ H →
        ω ∈ M ∧
        ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζα ω → (t : ℝ≥0∞) < firstContactTime (fun t => (α ω t : OnePoint ℂ))
            ((fun r => sphereInv (γ ω r : OnePoint ℂ)) '' Icc 0 s) →
          QuantumZipper.fwdHull (fun r : ℝ => drvDec (F (β ω, Hc ω)) r.toNNReal)
              (relClock (fun r : ℝ => W r.toNNReal ω) s (fun r : ℝ => Wα r.toNNReal ω) t) =
            relMap (fun r : ℝ => W r.toNNReal ω) s '' QuantumZipper.fwdHull (fun r : ℝ => Wα r.toNNReal ω) t := by
  obtain ⟨𝒢, M, β, hM, hβ, hword, hR1, hdet⟩ :=
    hD κ θ hκ hκ4 hθ₁ hθ₂ Ω mΩ P inferInstance h b J W Wα ζ ζα γ α b' J' h' hb hG hb' htr hcf hadmL hadmR hcomp
      hfl hα s Hc hHcm hHc F hF
  refine ⟨𝒢, M, β, hM, hβ, ?_, hdet⟩
  have hβm : Measurable β := hβ.mono 𝒢.2 le_rfl
  have hpair := ae_map_condExpKernel_pair_eq (P := P) 𝒢.2 hβ hHcm hR1 hF.1
  -- the sorted word and the good code, carried to almost every conditional law
  have hgoodK : ∀ᵐ ω₀ ∂P, ∀ᵐ ω ∂(condExpKernel P 𝒢.1 ω₀), ω ∈ M → (β ω).IsSorted ∧
      IsGoodDrvCode (F (β ω, Hc ω)) :=
    Sec7.Aux122Disint.ae_ae_condExpKernel 𝒢.2 hword
  filter_upwards [hpair, hgoodK, Sec7.Aux122Disint.ae_ae_condExpKernel_mem 𝒢.2 hM,
    Sec7.Aux122Disint.ae_ae_condExpKernel_eq 𝒢.2 hβ, hword] with ω₀ hp hgω₀ hMω₀ hβeq hw₀ hω₀M
  have hsort : (β ω₀).IsSorted := (hw₀ hω₀M).1
  refine ⟨hsort, hp hω₀M, isFlowLineDriver_gffLaw hF hsort ?_⟩
  -- the good code under the word's GFF law, pushed forward from the conditional law
  have hFc : Measurable fun g : DistOn upperHalfPlaneOpens => F (β ω₀, g) :=
    hF.1.comp (measurable_const.prodMk measurable_id)
  have hmeas : MeasurableSet {g : DistOn upperHalfPlaneOpens | IsGoodDrvCode (F (β ω₀, g))} :=
    hFc measurableSet_isGoodDrvCode
  have hmap : (condExpKernel P 𝒢.1 ω₀).map Hc = (β ω₀).gffLaw := by
    have h1 : ((condExpKernel P 𝒢.1 ω₀).map (fun ω => (Hc ω, F (β ω, Hc ω)))).map Prod.fst =
        ((β ω₀).gffLaw.map (fun g => (g, F (β ω₀, g)))).map Prod.fst := by
      rw [hp hω₀M]
    have hm1 : Measurable fun ω => (Hc ω, F (β ω, Hc ω)) := hHcm.prodMk (hF.1.comp (hβm.prodMk hHcm))
    have hm2 : Measurable fun g : DistOn upperHalfPlaneOpens => (g, F (β ω₀, g)) := measurable_id.prodMk hFc
    rw [Measure.map_map measurable_fst hm1, Measure.map_map measurable_fst hm2] at h1
    have e1 : (Prod.fst ∘ fun ω => (Hc ω, F (β ω, Hc ω))) = Hc := rfl
    have e2 : (Prod.fst ∘ fun g : DistOn upperHalfPlaneOpens => (g, F (β ω₀, g))) = id := rfl
    rw [e1, e2, Measure.map_id] at h1
    exact h1
  rw [← hmap, ae_map_iff hHcm.aemeasurable hmeas]
  filter_upwards [hgω₀, hMω₀ hω₀M, hβeq] with ω hω hωM hωβ
  have h2 := (hω hωM).2
  rwa [hωβ] at h2

/-! ### Why `GW2JointDetCStatement` fails: on `{ζα = 0}` it constrains every driver -/

/-- The point `0` is not on the inverted counterflow prefix (`sphereInv` of a finite point is never `0`). -/
theorem zero_notMem_sphereInv_image (γ : ℝ≥0 → ℂ) (s : ℝ≥0) :
    ((0 : ℂ) : OnePoint ℂ) ∉ (fun r => sphereInv (γ r : OnePoint ℂ)) '' Icc 0 s := by
  rintro ⟨r, -, hr⟩
  simp only [sphereInv_coe] at hr
  split_ifs at hr with hz
  · exact OnePoint.infty_ne_coe _ hr
  · exact hz (inv_eq_zero.1 (neg_eq_zero.1 (OnePoint.coe_injective hr)))

/-- **`GW2JointDetCStatement` forces the hull identity for an arbitrary driver on `{ζα = 0}`.** For any configuration
satisfying its hypotheses and **any** deterministic driver `U` with `U 0 = 0`, almost surely on `{γ(s) ∈ ℍ, ζα = 0}`,
for every `t`, the `relMap` image of the hull of `U` at `t` is the hull of the decoded canonical code (which does not
depend on `U`) at the relative clock. Proof: kill `Wα` at its lifetime and continue it by `U`
(`isFlowLineDriver_congr_ae`: still a flow-line driver), replace `α` by the constant path `0` on `{ζα = 0}` (still a
generating trace on `[0, ζα] = {0}`, and its first contact time is `⊤`), and apply the statement. Two drivers with
non-nested hulls (e.g. `±r`) then contradict the monotonicity of the left side, so the statement is false whenever
`{γ(s) ∈ ℍ, ζα = 0}` has positive probability for one admissible configuration (an inadmissible seed). -/
theorem gw2JointDetC_forall_driver (hD : GW2JointDetCStatement.{u}) {κ θ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (hθ₁ : -(Real.pi / 2) ≤ θ) (hθ₂ : θ ≤ Real.pi / 2) {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {b : ℝ → ℝ} {J : Finset ℝ}
    {W Wα : ℝ≥0 → Ω → ℝ} {ζ ζα : Ω → ℝ≥0∞} {γ α : Ω → ℝ≥0 → ℂ} {b' : ℝ → ℝ} {J' : Finset ℝ}
    {h' : Ω → DistOn upperHalfPlaneOpens}
    (hb : IsPiecewiseConstantBoundaryData b J) (hh : IsGFFWithBoundaryData P h b J)
    (hb' : IsPiecewiseConstantBoundaryData b' J')
    (hT : ∀ ω, IsChartTransport infinitySourceChart (-1) (-(Real.pi * QuantumZipper.chiC κ))
      (QuantumZipper.chiC (16 / κ)) (h ω) (h' ω))
    (hcf : IsFlowLineDriver (16 / κ) b' J' 0 P h' W ζ)
    (hpL : ∀ i : Fin (flowLineNL b' J' 0),
      -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ i), flowLineRhoL (16 / κ) b' J' 0 0 l)
    (hpR : ∀ i : Fin (flowLineNR b' J' 0),
      -2 < ∑ l ∈ Finset.univ.filter (fun l => l ≤ i), flowLineRhoR (16 / κ) b' J' 0 0 l)
    (hreg : ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω) ∧
      Tendsto (fun t => ‖γ ω t‖) atTop atTop)
    (hfl : IsFlowLineDriver κ b J θ P h Wα ζα)
    (hα : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => Wα t ω) (ζα ω) (α ω)) (s : ℝ≥0)
    {Hc : Ω → DistOn upperHalfPlaneOpens} (hHcm : Measurable Hc)
    (hHc : ∀ᵐ ω ∂P, γ ω s ∈ H →
      IsChartTransport (jointChart (fun r : ℝ => W r.toNNReal ω) s) 1 (specOffset κ) (QuantumZipper.chiC κ)
        (h ω) (Hc ω))
    {F : BoundaryWord × DistOn upperHalfPlaneOpens → Sec2.Assembly.PCode × ℝ≥0∞} (hF : IsCanonicalDriverCode κ θ F)
    {c' : BoundaryWord} (hc'J : c'.jumps = J') (hc'b : ∀ y ∉ J', c'.fn y = b' y) (U : ℝ≥0 → ℝ) (hU0 : U 0 = 0) :
    ∀ᵐ ω ∂P, γ ω s ∈ H → ζα ω = 0 → ∀ t : ℝ≥0,
      QuantumZipper.fwdHull
          (fun r : ℝ => drvDec (F (jointWord (specOffset κ) κ c' s (fun t => W t ω), Hc ω)) r.toNNReal)
          (relClock (fun r : ℝ => W r.toNNReal ω) s (fun r : ℝ => U r.toNNReal) t) =
        relMap (fun r : ℝ => W r.toNNReal ω) s '' QuantumZipper.fwdHull (fun r : ℝ => U r.toNNReal) t := by
  obtain ⟨_h₀, 𝓕, _VL, _VR, _B, _htr, hC⟩ := id hfl
  have hWa : AdaptedBefore 𝓕 ζα Wα := hC.1.2.1
  have hζm : Measurable ζα := Sec2.Assembly.measurable_lifetime hWa
  have hw0 : ∀ᵐ ω ∂P, Wα 0 ω = 0 := hC.1.2.2.2.2.mono fun ω hω => hω.1
  -- `Wα` killed at its lifetime and continued by `U`
  set W' : ℝ≥0 → Ω → ℝ := fun t ω => if (t : ℝ≥0∞) < ζα ω then Wα t ω else U t with hW'def
  have hW'm : ∀ t, Measurable (W' t) := by
    intro t A hA
    have h1 : MeasurableSet {ω | (t : ℝ≥0∞) < ζα ω ∧ Wα t ω ∈ A} := 𝓕.le t _ (hWa t A hA)
    have h2 : MeasurableSet {ω | ¬ (t : ℝ≥0∞) < ζα ω} := (measurableSet_lt measurable_const hζm).compl
    have he : W' t ⁻¹' A =
        {ω | (t : ℝ≥0∞) < ζα ω ∧ Wα t ω ∈ A} ∪ ({ω | ¬ (t : ℝ≥0∞) < ζα ω} ∩ {_ω | U t ∈ A}) := by
      ext ω
      simp only [hW'def, mem_preimage, mem_union, mem_ofPred_eq, mem_inter_iff]
      split_ifs with hlt <;> tauto
    rw [he]
    exact h1.union (h2.inter (MeasurableSet.const _))
  have hfl' : IsFlowLineDriver κ b J θ P h W' ζα := by
    refine StagedReg.isFlowLineDriver_congr_ae hfl hW'm ?_
    filter_upwards [hw0] with ω hω0
    refine ⟨?_, fun t ht => by simp only [hW'def, ht, ↓reduceIte]⟩
    by_cases h0 : ((0 : ℝ≥0) : ℝ≥0∞) < ζα ω
    · simp only [hW'def, h0, ↓reduceIte]
    · simp only [hW'def, h0, ↓reduceIte, hω0, hU0]
  -- the constant path `0` on `{ζα = 0}`
  set α' : Ω → ℝ≥0 → ℂ := fun ω => if ζα ω = 0 then fun _ => 0 else α ω with hα'def
  have hα' : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W' t ω) (ζα ω) (α' ω) := by
    filter_upwards [hα] with ω hω
    by_cases h0 : ζα ω = 0
    · simp only [hα'def, h0, ↓reduceIte]
      exact ⟨rfl, continuousOn_const, fun t ht => absurd ht ENNReal.not_lt_zero⟩
    · simp only [hα'def, h0, ↓reduceIte]
      refine ⟨hω.1, hω.2.1, fun t ht => ?_⟩
      have hfill := hω.2.2 t ht
      rwa [DomainMarkov.fwdHull_rpath_congr_of_lt (w := fun t => Wα t ω) (w' := fun t => W' t ω)
        (fun r hr => by simp only [hW'def, hr, ↓reduceIte]) ht] at hfill
  have hDω := hD κ θ hκ hκ4 hθ₁ hθ₂ Ω mΩ P inferInstance h b J W W' ζ ζα γ α' b' J' h' hb hh hb' hT hcf hpL hpR
    hreg hfl' hα' s Hc hHcm hHc F hF c' hc'J hc'b
  filter_upwards [hDω] with ω hω hsH h0 t
  have hfc : firstContactTime (fun t => (α' ω t : OnePoint ℂ))
      ((fun r => sphereInv (γ ω r : OnePoint ℂ)) '' Icc 0 s) = ⊤ := by
    have hα'ω : α' ω = fun _ => 0 := by simp only [hα'def, h0, ↓reduceIte]
    unfold firstContactTime
    rw [hα'ω]
    exact iInf₂_eq_top.2 fun r hr => absurd hr (zero_notMem_sphereInv_image (γ ω) s)
  have hW'ω : (fun r : ℝ => W' r.toNNReal ω) = fun r : ℝ => U r.toNNReal :=
    funext fun r => by simp only [hW'def, h0, ENNReal.not_lt_zero, ↓reduceIte]
  have key := (hω hsH).2 t (by rw [hfc]; exact ENNReal.coe_lt_top)
  rwa [hW'ω] at key

end GW2JointKernel

end Theorem14

end InteractingSLE
