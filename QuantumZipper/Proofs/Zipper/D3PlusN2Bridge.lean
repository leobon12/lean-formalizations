import QuantumZipper.Proofs.Zipper.D3PlusN2CM
import QuantumZipper.Proofs.Zipper.D3PlusIRich

/-!
# D3⁺(i), node N2: from the fixed-correction zoom to `D3PlusIN2RichStmt`

Task D3P-N2. The N1 factorization (`D3PlusN1Core.lean`, `D3PlusIRich.lean`) freezes the
macroscopic data `macroF ω` (values `X(bal μ) − X(ρ₀) + ∫ (α(−log) + g ω) dμ` at the dyadic
circles `circSet r`) and asks (`D3PlusIN2RichStmt`) for the TV convergence of the law of
`TmRichN1 γ r R L (Z, macroF ω)`. This file reduces it to the fixed-correction statement
`D3PlusIN2FixRichStmt` (`D3PlusN2Stmt.lean`) plus

* `D3PlusIN2FixMacroStmt`: a.s. the frozen macroscopic data is the circle-average data of an
  admissible correction, `macroF ω μ = ∫ (α(−log) + φ_ω) dμ` on `circSet r` (the harmonic
  extension `z ↦ X(P_z) − X(ρ₀)` of the outside field, a continuous version on the open
  half-disc, plus `g ω`; half-disc Markov property, node L2);
* `D3PlusIN2FixScaleStmt` (the local scale tends to `0` in probability) and
  `D3PlusIN2FixMeasRichStmt` (measurability of the fixed-correction rich data).

Proof (own elementary argument): on the event `0 < scaleParamOn < r/(R+1)` the two readings
coincide (`agreeNear_n2`: the two fields agree at every circle of `circSet r`; then the locality
lemmas of `D3PlusN1Local` and `scaleSur_eq`), so their laws are at TV distance at most the
probability of the complement (coupling inequality `tvDist_map_le_of_ae_eq_off`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace D3Plus

/-- **The frozen macroscopic data is the data of an admissible correction** (a.s.). -/
def D3PlusIN2FixMacroStmt : Prop :=
  ∀ (γ α r : ℝ) (ρ₀ : Measure ℂ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → FieldSample) {E' : Type} [MeasurableSpace E'] (Ξ : Ω → E')
    (g : Ω → ℂ → ℝ), Setup γ α r ρ₀ P X Ξ g →
    ∀ᵐ ω ∂P, ∃ φ : ℂ → ℝ, AdmCorr r φ ∧ ∀ μ ∈ circSet r,
      Integrable (fun z => α * -Real.log ‖z‖ + φ z) μ ∧
        macroF α r ρ₀ X g ω μ = ∫ z, (α * -Real.log ‖z‖ + φ z) ∂μ

/-- Coupling inequality: laws of two maps that agree off `B` are at TV distance `≤ P B`. -/
theorem tvDist_map_le_of_ae_eq_off {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    {P : Measure Ω} {f f' : Ω → β} (hf : AEMeasurable f P) (hf' : AEMeasurable f' P)
    (B : Set Ω) (hB : ∀ᵐ ω ∂P, ω ∉ B → f ω = f' ω) :
    TV.tvDist (P.map f) (P.map f') ≤ P B := by
  have h := tvDist_map_le_of_local (G := id) (ρ := f') (ρ' := f') (B' := ∅) hf hf' hf' hf'
    measurable_id hB (Eventually.of_forall fun _ _ => rfl)
  simpa [TV.tvDist_self] using h

/-- The fixed-correction field and the N1 local model agree at the circles of `circSet r`. -/
theorem agreeNear_n2 {γ α L r : ℝ} {φ : ℂ → ℝ} {s : LocIdx r → ℝ} {f : FieldSample}
    (hf : ∀ μ ∈ circSet r, Integrable (fun z => α * -Real.log ‖z‖ + φ z) μ ∧
      f μ = ∫ z, (α * -Real.log ‖z‖ + φ z) ∂μ) :
    AgreeNear (extLoc r s + ofFun (n2Shift γ α L φ)) (locModel γ L r (s, f)) r := by
  classical
  intro n k z hz
  have hmem : foldedCircle (dyadicRoundC n z) (radius k) ∈ circSet r := ⟨n, k, z, hz, rfl⟩
  obtain ⟨hint, hfeq⟩ := hf _ hmem
  have hloc := isLocalH_of_mem_circSet hmem
  have e : ∫ w, n2Shift γ α L φ w ∂(foldedCircle (dyadicRoundC n z) (radius k)) =
      ∫ w, (α * -Real.log ‖w‖ + φ w) ∂(foldedCircle (dyadicRoundC n z) (radius k)) + L / γ := by
    simp only [n2Shift]
    rw [integral_add hint (integrable_const _), integral_const, Measure.real, measure_univ,
      ENNReal.toReal_one, one_smul]
  simp only [locModel, dif_pos hmem, extLoc, dif_pos hloc, ofFun, Pi.add_apply, e, hfeq]
  ring

/-- On the event of a small positive local scale, the fixed-correction rich data is `TmRichN1`. -/
theorem n2Canon_eq_TmRichN1 {γ α L r : ℝ} {R : ℕ} {φ : ℂ → ℝ} {s : LocIdx r → ℝ}
    {f : FieldSample}
    (hag : AgreeNear (extLoc r s + ofFun (n2Shift γ α L φ)) (locModel γ L r (s, f)) r)
    (h2 : 0 < scaleParamOn γ (extLoc r s + ofFun (n2Shift γ α L φ)) (halfDisc r))
    (h3 : scaleParamOn γ (extLoc r s + ofFun (n2Shift γ α L φ)) (halfDisc r) < r / (R + 1)) :
    locFieldFull R (n2Canon γ α L r φ (extLoc r s)) = TmRichN1 γ r R L (s, f) := by
  have hsc := scaleParamOn_halfDisc_congr (γ := γ) hag
  have hgood := mem_goodN1_of_pos (hsc ▸ h2)
  unfold TmRichN1 zoomN1 n2Canon canonicalOn
  rw [scaleSur_eq hgood, ← hsc]
  exact locFieldFull_rescale_congr hag h2 (mul_lt_of_lt_div_succ h2 h3)

end D3Plus
end QuantumZipper
