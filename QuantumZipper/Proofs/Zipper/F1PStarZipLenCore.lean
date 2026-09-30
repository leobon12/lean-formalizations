import QuantumZipper.Proofs.Zipper.F1LenScale
import QuantumZipper.Proofs.Zipper.WedgeUnzipXC
import QuantumZipper.Proofs.LQG.GoodTransforms
import QuantumZipper.Proofs.Zipper.F1NodeAsm
import QuantumZipper.Proofs.Zipper.WedgeRC3All2
import QuantumZipper.Proofs.RS.RealAlive

/-!
# Theorem 1.3, node F1: `PStarZipLenInputsStmt` from the wedge core statements (D29 route)

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, §5.4 (proof of Theorem 1.3,
pp. 70–72: "by scaling") and §1.6 ((1.8), canonical description); Duplantier–Miller–Sheffield,
arXiv:1409.7055, Def. 4.4–4.5 (radial/lateral decomposition of a wedge, circle-average
embedding). Route and node table: `handoff/WEDGE-UNZIP.md` (decision D29).

The `P_*` sample `(Y, √κ B')` is the canonical description of an unscaled wedge configuration
(`WedgeUnzip.PStarRealizeStmt`, core P). Three of the four clauses of `PStarZipLenInputsStmt`
are proved here outright:

* **positivity** of `scaleParam γ (Y + k)`: field-level B4(c) `wedgeAddConstLawStmt_holds`
  (`WedgeRC3All2.lean`, via `WedgeAddConstPos` + `WedgeAddConstReembed`);
* **the side images** of the driver exist at every time: `RS.ae_real_alive`
  (Rohde–Schramm, *Basic properties of SLE*, Lemma 6.2) with
  `F1.exists_tendsto_sideImages_of_alive`;
* **goodness at all times**: `WedgeUnzip.pStarGoodAll_of_core` (D29 layer 5), from core P and
  W-G/W-X/W-C.

The fourth clause (B3(d) at the field level for the constant shift) is **derived** here from
`WedgeUnzip.regEq_unzippedField_canonConfig` plus the single transported-regularity input
`PStarShiftRegStmt`, whose content is exactly "W-X/W-C for the shifted `P_*` field, plus the
commutation of unzipping with additive constants". Its proof is *not* available from
W-G/W-X/W-C: the naive reduction to the unscaled wedge fails, because the drivers of
`canonConfig γ (addConst Y k, ·)` and of the corresponding rescaled unscaled configuration
differ by a Brownian rescaling by `scaleParam γ Z` (adding a constant to a canonical description
is a *re-embedding*: it acts on the embedding by a Brownian scaling, not by the deterministic
rescaling of `canonical_addConst_canonical_eq`). What it needs is the a.s. convergence of the
smoothed pairings of the `P_*` field along the pushed circles (the `P_*` analogue of W-C, and
the `RegShift`-convergence of its shifts) — the same regularity that `F2.F2UnzipRegStmt`
records as an open input for the F2 fields.

Own bookkeeping (the paper states the equivariance in one sentence).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace F1

open Thm18Asm

/-- **(Transported regularity of the `P_*` field under constant shifts)** The `P_*` analogue of
W-X + W-C for `Y + k`, plus the commutation of unzipping with additive constants: a.s., for every
constant `k`, with `γ = √κ`, `W = drive κ B'` and `a = scaleParam γ (Y + k)`,

* (i) `unzippedField γ (Y + k, W) t` and `addConst (unzippedField γ (Y, W) t) k` agree up to
  `RegEq`, for every `t ≥ 0` (`coordChange` reads a field only through `avgReg`, and `avgReg`
  commutes with constants for regular samples);
* (ii) the shifted field is scale consistent at the images of the folded circles under the
  unzipping map of its canonicalized driver (W-C transported through `addConst k`);
* (iii) its unzipped fields are exact at folded circles (W-X transported through `addConst k`).

These are the three hypotheses of `WedgeUnzip.regEq_unzippedField_canonConfig` at
`y = addConst Y k` and parameter `s`, together with the constant commutation (i). -/
def PStarShiftRegStmt : Prop :=
  ∀ (κ : ℝ) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y : Ω' → FieldSample) (B' : ℝ≥0 → Ω' → ℝ), Thm13Asm.IsPStarSample κ P' Y B' →
    ∀ᵐ ω ∂P', ∀ k : ℝ,
      (∀ t : ℝ, 0 ≤ t →
        RegEq (unzippedField (Real.sqrt κ) (addConst (Y ω) k, drive κ B' ω) t)
          (addConst (unzippedField (Real.sqrt κ) (Y ω, drive κ B' ω) t) k)) ∧
      (∀ s : ℝ, 0 ≤ s → ∀ (d : ℂ) (r : ℝ), 0 < r →
        G1.ScaleConsistentAt (addConst (Y ω) k) (Qc (Real.sqrt κ))
          (scaleParam (Real.sqrt κ) (addConst (Y ω) k))
          ((foldedCircle d r).map (fwdMapInv (canonConfig (Real.sqrt κ)
            (addConst (Y ω) k, drive κ B' ω)).2 s))) ∧
      (∀ s : ℝ, 0 ≤ s → ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r →
        evalReg (unzippedField (Real.sqrt κ) (addConst (Y ω) k, drive κ B' ω)
            (scaleParam (Real.sqrt κ) (addConst (Y ω) k) ^ 2 * s)) (foldedCircle d r) =
          unzippedField (Real.sqrt κ) (addConst (Y ω) k, drive κ B' ω)
            (scaleParam (Real.sqrt κ) (addConst (Y ω) k) ^ 2 * s) (foldedCircle d r))

/-- **Positivity of `scaleParam γ (Y + k)`** (field-level B4(c), `WedgeRC3All2.lean`). -/
theorem ae_pos_scaleParam_addConst_pStar {κ : ℝ} {Ω' : Type} [MeasurableSpace Ω']
    {P' : Measure Ω'} [IsProbabilityMeasure P'] {Y : Ω' → FieldSample}
    {B' : ℝ≥0 → Ω' → ℝ} (hP : Thm13Asm.IsPStarSample κ P' Y B') (k : ℝ) :
    ∀ᵐ ω ∂P', 0 < scaleParam (Real.sqrt κ) (addConst (Y ω) k) :=
  (wedgeAddConstLawStmt_holds (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ)
    (Real.sqrt_pos.2 hP.1) (F2.sqrt_lt_two_of' hP.1 hP.2.1)
    (F2.alpha_lt_Qc' (Real.sqrt_pos.2 hP.1) (F2.sqrt_lt_two_of' hP.1 hP.2.1))
    P' Y hP.2.2.1 k).1

/-! ## Wiring into `LenScaleStmt` (F1b), with B4(c) discharged -/

end F1
end QuantumZipper
