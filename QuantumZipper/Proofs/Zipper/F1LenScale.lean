import QuantumZipper.Proofs.Zipper.F1ABJensen
import QuantumZipper.Proofs.Zipper.B3dLen

/-!
# Theorem 1.3, node F1: `LenScaleStmt` and `PStarUnzipGoodStmt` from the B3(d)/B4(c) inputs

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, §5.4, proof of Theorem 1.3
(p. 71, "by scaling"); blueprint `blueprint/E_BRANCH_BLUEPRINT.md` §F1 (F1b). With
`γ = √κ`, `n ≥ 1` and `C = −(2/γ) log n` (so `e^{γC/2} = 1/n`), the configuration
`c' = canonConfig γ (Y + C, √κ B')` satisfies `F_{c'}(s) = F_c(n s)/n`:
adding `C` multiplies the lengths by `1/n` (rule (5.1)), and the canonical re-normalization
rescales capacity time by `a² = scaleParam γ (Y + C)²` (B3(d), `unzipLengths_canon_addConst`),
which first-passage times absorb (`lenF_of_scaled`).

Two explicit inputs remain:

* `PStarCanonLawStmt` (law, B4(c) + Brownian scaling): `c'` has the `configLawFull` of the `P_*`
  configuration, with a.e.-measurable data. (The wedge is invariant in law, as a quantum surface,
  under adding a constant; given `Y`, `W(a²·)/a` is again `√κ` times a Brownian motion,
  independent of `Y`.)
* `PStarZipLenInputsStmt` (pathwise, B3(b)/B3(d) at the field level; the `P_*` analogue of
  `B3d.ZipLenInputsStmt`): for each constant `k`, a.s. `scaleParam γ (Y + k) > 0`, both side
  images of the driver exist at all times, the unzipped fields are good at all times, and the
  field unzipped from `canonConfig γ (Y + k, W)` in time `s` is the `a`-rescaling of the
  `k`-shifted field unzipped from `(Y, W)` in time `a² s`.

`PStarZipLenInputsStmt` (at `k = 0`, time `1`) also gives `PStarUnzipGoodStmt`
(`pStarUnzipGoodStmt_of_zipLenInputs`). Own bookkeeping (the paper states the scaling in one
sentence).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace F1

/-- The rescaled `P_*` configuration `canonConfig γ (Y + k, √κ B')`. -/
abbrev scCfg (κ k : ℝ) {Ω' : Type} (Y : Ω' → FieldSample) (B' : ℝ≥0 → Ω' → ℝ) (ω : Ω') :
    FieldSample × (ℝ → ℝ) :=
  canonConfig (Real.sqrt κ) (addConst (Y ω) k, drive κ B' ω)

/-- **B4(c) for `P_*` configurations** (open): adding a constant to the wedge field and
canonicalizing (with the Brownian rescaling of the driver) preserves the configuration law. -/
def PStarCanonLawStmt : Prop :=
  ∀ (κ : ℝ) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y : Ω' → FieldSample) (B' : ℝ≥0 → Ω' → ℝ), Thm13Asm.IsPStarSample κ P' Y B' →
    ∀ k : ℝ, configLawFull (scCfg κ k Y B') P' = configLawFull (pcfg κ Y B') P' ∧
      AEMeasurable (fun ω => cfgData (scCfg κ k Y B' ω)) P'

theorem drive_max (κ : ℝ) {Ω' : Type} (B' : ℝ≥0 → Ω' → ℝ) (ω : Ω') (s : ℝ) :
    drive κ B' ω (max s 0) = drive κ B' ω s := by
  simp only [drive]
  congr 2
  ext
  simp only [Real.coe_toNNReal', max_eq_left (le_max_right s 0)]

/-- `e^{γ C/2} = 1/n` for `C = −(2/γ) log n`. -/
theorem ofReal_exp_scale {γ : ℝ} (hγ : 0 < γ) {n : ℕ} (hn : 1 ≤ n) :
    ENNReal.ofReal (Real.exp (γ * (-(2 / γ) * Real.log n) / 2)) = (n : ℝ≥0∞)⁻¹ := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have e : γ * (-(2 / γ) * Real.log n) / 2 = -Real.log n := by field_simp
  rw [e, Real.exp_neg, Real.exp_log hn', ENNReal.ofReal_inv_of_pos hn', ENNReal.ofReal_natCast]

end F1
end QuantumZipper
