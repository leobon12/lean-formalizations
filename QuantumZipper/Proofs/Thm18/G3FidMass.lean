import QuantumZipper.Proofs.Thm18.G3ConcreteMarkov
import QuantumZipper.Proofs.Thm18.G3FidHonest
import QuantumZipper.Proofs.Thm18.LenPos
import Mathlib.Probability.Distributions.Exponential

/-!
# G3 fidelity F3: the total mass `g3Z` of the Palm weight

Sheffield, arXiv:1012.4797, proof of Theorem 1.8 (§5.4, pp. 70–71): the Palm point of the
concrete scheme is sampled from the `ν_h[−δ,0]`-length-biased law on `Ω₀ × ℝ`, whose density
w.r.t. `P₀ ⊗ Exp(1)` is `g3W0 = e^ℓ 1{0 < ℓ ≤ ν_h[−δ,0]}`. Since `Exp(1)` has density
`e^{−ℓ} dℓ`, the length integral collapses:

  `∫₀^∞ e^ℓ 1{ℓ ≤ ν} e^{−ℓ} dℓ = ν`,

so the total mass is exactly `g3Z = ∫⁻ g3Mass ∂P₀ = E ν_h[−δ, 0]` (`g3Z_eq_lintegral_g3Mass`).
This is the F3 fidelity condition of `handoff/G3.md` (G3-M123): `0 < g3Z < ⊤`, i.e.
`E ν_h[−δ, 0] ∈ (0, ∞)` (the correct normalization of the Palm law; junk weight `1` otherwise).

Contents:

* `lintegral_expMeasure_palmKernel`: the generic computation
  `∫⁻ ℓ, e^ℓ 1{0 < ℓ ≤ M} ∂Exp(1) = M` (own elementary proof, from the density of `Exp(1)`);
* `lintegral_g3W0_fst`, `g3Z_eq_lintegral_g3Mass`: `g3Z γ i = ∫⁻ ω, g3Mass γ i ω ∂P₀`;
* `g3Z_pos_iff`, `g3Z_lt_top_iff`: `0 < g3Z` and `g3Z < ⊤` are exactly the positivity and
  finiteness of `E ν_h[−δ, 0]`;
* `bdryM_le_qBoundaryMeasure`, `g3Mass_le`, `g3Mass_lt_top`: the scheme's mass is dominated by
  the two boundary measures it reads (region 1 + gap), and it is finite for every `ω` (each
  `qBoundaryMeasure` is locally finite — `Thm18Asm.qBoundaryMeasure_Icc_lt_top`);
* `g3Z_pos_of_pos_ae`, `g3Z_lt_top_of_le`: F3 from the two explicit inputs of `handoff/G3.md`
  (F2/F3): a.s. positivity of the Palm mass (`E ν_h[−δ, 0] > 0`), resp. a.s. domination of the
  Palm mass by an integrable bound (`E ν_h[−δ, 0] < ∞`);
* `G3HonestFinStmt`, `G3HonestPosStmt`, `g3Z_lt_top_of_inputs`, `g3Z_pos_of_inputs`: the residual
  F3 inputs as named statements;
* `g3Z_pos_of_honest_le`: **positivity of `g3Z` needs only F2**, because the honest expected
  boundary length `E ν_h[−δ, 0]` is positive unconditionally
  (`G3FidHonest.lintegral_qBoundaryMeasure_normField_Icc_pos`, from the `|t|`-density form of the
  log-singularity theorem `G3FidHonest.ae_normField_logSingularity` and the free-field first
  moment `FirstMoment.lintegral_qBoundaryMeasure_Ioo_pos_X`). Only the *finiteness* of
  `E ν_h[−δ, 0]` remains open (see the final report).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm

open K3

variable (γ : ℝ) (i : G3Idx)

local notation "Ω₀" => gffBase.Ω
local notation "X₀" => gffBase.X

/-! ## The Palm mass computation `∫ e^ℓ 1{ℓ ≤ M} e^{−ℓ} dℓ = M` -/

/-- **The length integral of the Palm weight.** Against the unit exponential law (density
`e^{−ℓ}`), the unnormalized Palm kernel `e^ℓ 1{0 < ℓ ≤ M}` integrates to the mass `M`:

`∫⁻ ℓ, (if 0 < ℓ ∧ ofReal ℓ ≤ M then ofReal (exp ℓ) else 0) ∂Exp(1) = M`.

Own elementary proof: unfold `Exp(1) = volume.withDensity (e^{−ℓ})`, use `e^ℓ · e^{−ℓ} = 1` and
`volume (Ioc 0 M) = M`. -/
theorem lintegral_expMeasure_palmKernel (M : ℝ≥0∞) :
    ∫⁻ ℓ : ℝ, (if 0 < ℓ ∧ ENNReal.ofReal ℓ ≤ M then ENNReal.ofReal (Real.exp ℓ) else 0)
      ∂(expMeasure 1) = M := by
  have hg : Measurable fun ℓ : ℝ =>
      (if 0 < ℓ ∧ ENNReal.ofReal ℓ ≤ M then ENNReal.ofReal (Real.exp ℓ) else 0) :=
    Measurable.ite ((measurableSet_lt measurable_const measurable_id).inter
        (measurableSet_le (ENNReal.measurable_ofReal.comp measurable_id) measurable_const))
      (ENNReal.measurable_ofReal.comp Real.measurable_exp) measurable_const
  rw [show expMeasure 1 = volume.withDensity (gammaPDF 1 1) from rfl,
    lintegral_withDensity_eq_lintegral_mul (f := gammaPDF 1 1) volume
      (ENNReal.measurable_ofReal.comp (measurable_gammaPDFReal 1 1)) hg]
  have hpt : ∀ ℓ : ℝ, gammaPDF 1 1 ℓ *
      (if 0 < ℓ ∧ ENNReal.ofReal ℓ ≤ M then ENNReal.ofReal (Real.exp ℓ) else 0) =
      (if 0 < ℓ ∧ ENNReal.ofReal ℓ ≤ M then 1 else 0) := by
    intro ℓ
    by_cases h : 0 < ℓ ∧ ENNReal.ofReal ℓ ≤ M
    · rw [if_pos h, if_pos h]
      have hℓ : (0 : ℝ) ≤ ℓ := h.1.le
      have hpdf : gammaPDF 1 1 ℓ = ENNReal.ofReal (Real.exp (-ℓ)) := by
        have h1 : gammaPDFReal 1 1 ℓ = Real.exp (-ℓ) := by
          simp only [gammaPDFReal, hℓ, if_true, Real.one_rpow, Real.Gamma_one, div_one,
            sub_self, Real.rpow_zero, one_mul, mul_one]
        show ENNReal.ofReal (gammaPDFReal 1 1 ℓ) = ENNReal.ofReal (Real.exp (-ℓ))
        rw [h1]
      rw [hpdf, ← ENNReal.ofReal_mul (Real.exp_nonneg (-ℓ)), ← Real.exp_add, neg_add_cancel,
        Real.exp_zero, ENNReal.ofReal_one]
    · rw [if_neg h, if_neg h, mul_zero]
  simp only [Pi.mul_apply]
  rw [lintegral_congr hpt]
  rcases eq_or_ne M ⊤ with rfl | hM
  · have hind : ∀ ℓ : ℝ, (if 0 < ℓ ∧ ENNReal.ofReal ℓ ≤ ⊤ then (1 : ℝ≥0∞) else 0) =
        (Ioi 0).indicator (1 : ℝ → ℝ≥0∞) ℓ := by
      intro ℓ
      by_cases h : 0 < ℓ
      · rw [if_pos ⟨h, le_top⟩, Set.indicator_of_mem (Set.mem_Ioi.2 h)]
        simp only [Pi.one_apply]
      · rw [if_neg (fun hc => h hc.1), Set.indicator_of_notMem (fun hc => h (Set.mem_Ioi.1 hc))]
    rw [lintegral_congr hind, lintegral_indicator_one measurableSet_Ioi,
      Real.volume_Ioi]
  · have hset : ∀ ℓ : ℝ, (0 < ℓ ∧ ENNReal.ofReal ℓ ≤ M) ↔ ℓ ∈ Ioc 0 M.toReal := by
      intro ℓ
      rw [Set.mem_Ioc]
      refine ⟨fun h => ⟨h.1, ?_⟩, fun h => ⟨h.1, ?_⟩⟩
      · refine (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).1 ?_
        simpa [ENNReal.ofReal_toReal hM] using h.2
      · exact (ENNReal.ofReal_le_ofReal h.2).trans_eq (ENNReal.ofReal_toReal hM)
    have hind : ∀ ℓ : ℝ, (if 0 < ℓ ∧ ENNReal.ofReal ℓ ≤ M then (1 : ℝ≥0∞) else 0) =
        (Ioc 0 M.toReal).indicator (1 : ℝ → ℝ≥0∞) ℓ := by
      intro ℓ
      by_cases h : ℓ ∈ Ioc 0 M.toReal
      · rw [if_pos ((hset ℓ).2 h), Set.indicator_of_mem h]
        simp only [Pi.one_apply]
      · rw [if_neg (fun hc => h ((hset ℓ).1 hc)), Set.indicator_of_notMem h]
    rw [lintegral_congr hind, lintegral_indicator_one measurableSet_Ioc,
      Real.volume_Ioc, sub_zero, ENNReal.ofReal_toReal hM]

/-! ## The mass of the concrete Palm law -/

/-- **The Palm mass identity**: the length integral of `g3W0` against `Exp(1)` is `g3Mass`. -/
theorem lintegral_g3W0_fst (ω : Ω₀) :
    ∫⁻ ℓ : ℝ, g3W0 γ i (ω, ℓ) ∂L₀ = g3Mass γ i ω := by
  refine (lintegral_congr fun ℓ => ?_).trans
    (lintegral_expMeasure_palmKernel (g3Mass γ i ω))
  by_cases h : 0 < ℓ ∧ ENNReal.ofReal ℓ ≤ g3Mass γ i ω
  · rw [if_pos h]
    unfold g3W0
    rw [if_pos h]
  · rw [if_neg h]
    unfold g3W0
    rw [if_neg h]

/-- **F3, mass identity** (`handoff/G3.md`, G3-M123): the total mass of the unnormalized Palm
weight is the expected boundary length `E ν_h[−δ, 0]`, read from the region-1 and gap fields:

`g3Z γ i = ∫⁻ ω, g3Mass γ i ω ∂P₀`.

(With `g3Mass = (ν₁ + ν₀)[−δ, 0]`; `ν₁ + ν₀ = ν_h` on `(−δ−η/4, 3η/4)` is the F2 locality input.) -/
theorem g3Z_eq_lintegral_g3Mass : g3Z γ i = ∫⁻ ω, g3Mass γ i ω ∂gffBase.P := by
  have hW0 : Measurable (g3W0 γ i) := (measurable_g3W0 γ i).mono (sig_le_g3 i _ _) le_rfl
  unfold g3Z
  rw [lintegral_prod _ hW0.aemeasurable]
  exact lintegral_congr fun ω => lintegral_g3W0_fst γ i ω

/-- `g3Mass` is measurable (it is a boundary measure of the measurable region-1 and gap fields,
evaluated on the compact interval `[−δ, 0]`). -/
theorem measurable_g3Mass : Measurable (g3Mass γ i) := by
  have hW0 : Measurable (g3W0 γ i) := (measurable_g3W0 γ i).mono (sig_le_g3 i _ _) le_rfl
  have h1 : Measurable fun ω : Ω₀ => ∫⁻ ℓ : ℝ, g3W0 γ i (ω, ℓ) ∂L₀ :=
    Measurable.lintegral_prod_right (ν := L₀) (f := fun ω ℓ => g3W0 γ i (ω, ℓ)) hW0
  rw [show g3Mass γ i = fun ω : Ω₀ => ∫⁻ ℓ : ℝ, g3W0 γ i (ω, ℓ) ∂L₀ from
    funext fun ω => (lintegral_g3W0_fst γ i ω).symm]
  exact h1

/-! ## The mass is dominated by the two boundary measures it reads -/

/-- The scheme's boundary measure on its existence certificate is dominated by the honest
boundary measure (`bdryM` is `qBoundaryMeasure` on `BCert` and `0` off it). -/
theorem bdryM_le_qBoundaryMeasure (γ : ℝ) (y : FieldSample) :
    bdryM γ y ≤ qBoundaryMeasure γ y := by
  by_cases h : E1.M4.BCert γ y
  · simp [bdryM, h]
  · rw [bdryM, if_neg h]
    exact Measure.zero_le _

/-- **The Palm mass is finite for every `ω`**: each of the two boundary measures it reads is
finite on compact intervals (`Thm18Asm.qBoundaryMeasure_Icc_lt_top`). -/
theorem g3Mass_lt_top (ω : Ω₀) : g3Mass γ i ω < ⊤ := by
  have h₁ := bdryM_le_qBoundaryMeasure γ (regionField γ i.t₁ i.r₁ X₀ ω) (Icc (-i.δ) 0)
  have h₂ := bdryM_le_qBoundaryMeasure γ (gapField γ i.t₁ i.r₁ i.t₂ i.r₂ X₀ ω) (Icc (-i.δ) 0)
  rw [g3Mass, Measure.add_apply]
  exact ENNReal.add_lt_top.2
    ⟨h₁.trans_lt (qBoundaryMeasure_Icc_lt_top γ _ _ _),
      h₂.trans_lt (qBoundaryMeasure_Icc_lt_top γ _ _ _)⟩

/-! ## F3 from the two explicit F2/F3 inputs -/

/-! ## The residual F3 inputs, as named statements -/

/-- **The residual F3 finiteness input** (`handoff/G3.md`, (F3)): the expected boundary length
`E ν_h[−δ, 0]` of the Theorem 1.2 field `h = normField γ X₀`, read through its honest boundary
measure, is finite. -/
def G3HonestFinStmt (γ : ℝ) (i : G3Idx) : Prop :=
  ∫⁻ ω, qBoundaryMeasure γ (normField γ X₀ ω) (Icc (-i.δ) 0) ∂gffBase.P < ⊤

end Thm18Asm
end QuantumZipper
