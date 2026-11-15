/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4FixVersion

/-!
# Theorem GW4's component (Det) on GB6's corrected route: announced versions and the relative safe law

Packet PROVE-T14-GW4FIX. PROVE-Q3-REL4 (§4, §5.3) found that `GW4Rel.GW4RelStopKernelStatement` (the relative stopped
coupling for EVERY version stop) is not reachable: the clause of `IsStoppedHullCoupling` at the stop needs the stop to
be announced. Moreover `GW4Rel.gw4RelStopMatchStatement_of_stopCoupling` / `_of_safeLaw` use the plain Aux. lemma 54
(`StoppedHullExtendStatement`, defective by R79). GB6's corrected route
(`Q3Stop.gb6HullDetStatement_of_liveReadout_relSafe`) avoids both: the stopped K2 runs on the canonical space with
record–path announcing rules and the proved R-form Aux. 54 (`Q3Stop.ae_isStopDrvMatch_of_hasRelSafe`). This file
takes that route for GW4 (record constant, `gw4Rec`):

* **`GW4RelSafeStatement`** (named input; Astra's follow-up 3, Q3 (Q3.3) at deterministic relative times and relative
  locality (§3.5) in the filtration (Q3.2) of the relative path, for the selected GW4 component): for every version of
  the relative traversal through a stopping time, the joint law of the relative variable (inverted component field,
  relative driver, stop) has K2's inputs `HasRelSafe` at `16/κ` for the counterflow word `c₀`;
* **`gw4RelStopMatchStatement_of_relSafe`**: announced versions and the safe law give the relative stopped match
  `GW4Rel.GW4RelStopMatchStatement` (no Aux. 54 input: the R-form is proved);
* **`gw4RelativeLawRegStatement_of_relSafe`**, **`gw4RelativeLawRegStatement_of_coord_relSafe`**: Theorem GW4's
  component (Det) `GW4Reg.GW4RelativeLawRegStatement` from the walks' barrier with its pocket shape, GW3's word bounds,
  Theorems 1.2–1.3 (R48 allows them for Theorem 1.4), the measurable relative coordinates
  (`GW4RelCoordStatement`) and the relative safe law.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.GW4Fix

open GW4Traverse GW4Rel Exist.StagedLaw Supp8.GB6 Supp8.GB6.RelDrv Supp8.GB6.HullId Supp8.Q3Stop Restart
  Sec7.StripSysField

/-- **Named input: GW4's relative safe law** (supplement pp. 638–639; Astra's follow-up 3, Q3: "For each `G`-stopping
time `S < ζ`, the conditional field outside `K̃_S`, given `G_S`, is Gaussian with zero-boundary Green covariance and
canonical mean (Q3.3)", relative locality (§3.5), in the filtration (Q3.2) of the walks and the relative path; under
the conditional law `ν` the walks are fixed, so the record is the constant `gw4Rec`). Binders of
`GW4Rel.GW4RelStopCouplingStatement` up to the sorted word `c₀` of the counterflow data of the component field, then a
version `(R, V)` of the relative traversal through a stopping time of the relative path (`IsGW4RelStopVersion`): the
joint law of `(gw4Rec, inverted component field, R, V)` has K2's inputs (S) and (L) at `16/κ` for the counterflow word
`c₀` with lifetime the stop, the stop is before the continuation threshold, and the field is integrable
(`Q3Stop.HasRelSafe` for the word type of `c₀`). -/
def GW4RelSafeStatement : Prop :=
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
            HasRelSafe (16 / κ) (wordType (16 / κ) c₀) (fun _ => c₀) univ
              (ν.map fun ω => (gw4Rec, relVar (fun ω => invField κ (hC ω)) Rv V ω))

/-- **The relative stopped match from announced versions and the relative safe law** (GB6's corrected route for GW4):
for every canonical driver code `F` at `16/κ`, each announced version matches the code of `(c₀, h_C)` (inverted) at
the dyadic times before its stop, `ν`-almost surely (`Q3Stop.ae_isStopDrvMatch_of_hasRelSafe` with the constant
record; the R-form Aux. 54 inside it is proved). -/
theorem gw4RelStopMatchStatement_of_relSafe (hV : GW4RelVersionAStatement.{u}) (hS : GW4RelSafeStatement.{u}) :
    GW4RelStopMatchStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg wR wL
  filter_upwards [hV κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg,
    hS κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg] with ω₀ hVω hSω
  intro R L ν C hCm c hC bC jumpsC hch htr hpc hbd hgff c₀ hc₀s hc₀J hc₀ F hF
  have hν : IsProbabilityMeasure ν := by
    show IsProbabilityMeasure (condExpKernel P _ ω₀)
    infer_instance
  obtain ⟨Rv, V, hver, hexh⟩ := hVω C hCm c hch
  refine ⟨Rv, V, fun m => (hver m).1.1, hexh, fun m => ?_⟩
  obtain ⟨hsv, hV0, ⟨ρ, hρm, hρ, hVρ⟩, ρs, hρsm, hρs, hρsfin, hρsmono, hann⟩ := hver m
  have hk : 0 < 16 / κ := sixteen_div_pos hκ
  have hm := ae_isStopDrvMatch_of_hasRelSafe (P := ν) hk hF (β := fun _ => c₀) measurable_const
    MeasurableSet.univ (wordType (16 / κ) c₀) (rec := fun _ => gw4Rec) measurable_const
    ((measurable_invField κ).comp hgff.1) hsv.1.1 hsv.1.2.1 hsv.1.2.2.1 hsv.1.2.2.2.1
    (hSω C hCm c hC bC jumpsC hch htr hpc hbd hgff c₀ hc₀s hc₀J hc₀ (Rv m) (V m) hsv)
    (hV0.mono fun ω h _ => h) (ρ := fun x => ρ x.2) (hρm.comp measurable_snd) (isPathRule_comp_snd hρ) hVρ
    (ρs := fun n x => ρs n x.2) (fun n => (hρsm n).comp measurable_snd) (fun n => isPathRule_comp_snd (hρs n))
    (fun n x => hρsfin n x.2) (fun x => hρsmono x.2) (hann.mono fun ω h _ => h.1) (hann.mono fun ω h _ => h.2)
  filter_upwards [hm] with ω hω using hω (mem_univ _) rfl

/-- **Theorem GW4's component (Det) from announced versions and the relative safe law** (conditional helper with a
distinct name): `GW4Reg.GW4RelativeLawRegStatement` from the walks' barrier with its pocket shape, GW3's word bounds,
Theorems 1.2–1.3, `GW4RelVersionAStatement` and `GW4RelSafeStatement` (no Aux. 54 input). -/
theorem gw4RelativeLawRegStatement_of_relSafe (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (hB : GW4Reg.GW4BarrierPocketRegStatement.{u})
    (hWB : GW4R51.GW3WordBoundRegStatement.{u}) (hV : GW4RelVersionAStatement.{u})
    (hS : GW4RelSafeStatement.{u}) : GW4Reg.GW4RelativeLawRegStatement.{u} :=
  gw4RelativeLawRegStatement_of_stopMatch h12 h13 h12₀ h13₀ hB hWB (gw4RelStopMatchStatement_of_relSafe hV hS)

/-- **Theorem GW4's component (Det) from measurable relative coordinates and the relative safe law** (conditional
helper with a distinct name; the GW4 form of `Q3Stop.gb6HullDetStatement_of_liveReadout_relSafe`): the running-maximum
gauge reads the coordinate versions back from the relative path itself, so no separate read-back input is needed. -/
theorem gw4RelativeLawRegStatement_of_coord_relSafe (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (hB : GW4Reg.GW4BarrierPocketRegStatement.{u})
    (hWB : GW4R51.GW3WordBoundRegStatement.{u}) (hC : GW4RelCoordStatement.{u})
    (hS : GW4RelSafeStatement.{u}) : GW4Reg.GW4RelativeLawRegStatement.{u} :=
  gw4RelativeLawRegStatement_of_relSafe h12 h13 h12₀ h13₀ hB hWB (gw4RelVersionAStatement_of_coord h13 hB hC) hS

end InteractingSLE.Theorem14.GW4Fix
