import QuantumZipper.Proofs.Zipper.D3PlusN2FirstModeBlock

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# N2Z-FIRSTMODE, step 4: moment bounds from Gaussian variance bounds

Task N2Z-FIRSTMODE. We reduce the moment node `N2ZFirstModeMomStmt`
(`D3PlusN2FirstModeBlock.lean`) to the **variance node** `N2ZFirstModeVarStmt`: the same
statement with the 16th-moment bounds replaced by the Gaussian facts

* `V q − V q'` is a centred Gaussian of variance `≤ c ‖q − q'‖` on the box `R + 1`;
* `V q` is a centred Gaussian of variance `≤ c` on the box `R`,

(rescaled coordinates, `c` depending only on `m`). The step is `E|N(0,v)|^16 = v^8 E|N(0,1)|^16`
(`RegSample.lintegral_pow16_of_map_eq`), as in `RegSample.momentBound_nuQ`.

Then `n2ZFirstMode_of_var : N2ZFirstModeVarStmt → N2ZFirstModeStmt`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped Real ENNReal NNReal

namespace QuantumZipper
namespace D3Plus

open KolmD KolmG

/-- **Node N2Z-FIRSTMODE-VAR** (Gaussian variance bounds for the rescaled first mode). -/
def N2ZFirstModeVarStmt : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → FieldSample), IsFreeGFFModConstH X P →
    ∃ G : Ω → ℂ × ℝ → ℝ, WedgeTK.IsRegVersion X P G ∧
      ∀ m : ℕ, ∃ c : ℝ, 0 ≤ c ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ k : Fin 2,
        ∃ V : (Fin 4 → ℝ) → Ω → ℝ, (∀ ω, Continuous fun q => V q ω) ∧
          (∀ q, Measurable (V q)) ∧
          (∀ q ∈ boxD (d := 4) ((m + 1) * 2 ^ n + 1), ∀ q' ∈ boxD (d := 4) ((m + 1) * 2 ^ n + 1),
            ∃ v : ℝ≥0, P.map (fun ω => V q ω - V q' ω) = gaussianReal 0 v ∧
              (v : ℝ) ≤ c * ‖q - q'‖) ∧
          (∀ q ∈ boxD (d := 4) ((m + 1) * 2 ^ n),
            ∃ v : ℝ≥0, P.map (V q) = gaussianReal 0 v ∧ (v : ℝ) ≤ c) ∧
          ∀ᵐ ω ∂P, ∀ w ∈ fmBox m, ∀ τ ∈ Ioc ((2 : ℝ)⁻¹ ^ (n + 1)) ((2 : ℝ)⁻¹ ^ n),
            ∀ s ∈ Ioo 0 τ, fmPart k (fmInt (G ω) w τ s) = V (fmParam n w τ s) ω

/-- **Reduction**: variance bounds give the moment node. -/
theorem n2ZFirstModeMom_of_var (hV : N2ZFirstModeVarStmt) : N2ZFirstModeMomStmt := by
  intro Ω _ P _ X hX
  obtain ⟨G, hG, hvar⟩ := hV P X hX
  refine ⟨G, hG, fun m => ?_⟩
  obtain ⟨c, hc, n₀, hn⟩ := hvar m
  have hg := gaussianAbsMoment_nonneg 16
  refine ⟨c ^ 8 * gaussianAbsMoment 16, by positivity, n₀, fun n hn₀ k => ?_⟩
  obtain ⟨V, hVc, hVm, hinc, hpt, hae⟩ := hn n hn₀ k
  refine ⟨V, hVc, fun q => (hVm q).aemeasurable, ?_, ?_, hae⟩
  · intro q hq q' hq'
    obtain ⟨v, hlaw, hv⟩ := hinc q hq q' hq'
    rw [RegSample.lintegral_pow16_of_map_eq (U := fun ω => V q ω - V q' ω)
      ((hVm q).sub (hVm q')) hlaw]
    apply ENNReal.ofReal_le_ofReal
    have h8 := pow_le_pow_left₀ (NNReal.coe_nonneg _) hv 8
    rw [show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    calc (v : ℝ) ^ 8 * gaussianAbsMoment 16 ≤ (c * ‖q - q'‖) ^ 8 * gaussianAbsMoment 16 :=
          mul_le_mul_of_nonneg_right h8 hg
      _ = c ^ 8 * gaussianAbsMoment 16 * ‖q - q'‖ ^ 8 := by ring
  · intro q hq
    obtain ⟨v, hlaw, hv⟩ := hpt q hq
    rw [RegSample.lintegral_pow16_of_map_eq (hVm q) hlaw]
    apply ENNReal.ofReal_le_ofReal
    have h8 := pow_le_pow_left₀ (NNReal.coe_nonneg _) hv 8
    exact mul_le_mul_of_nonneg_right h8 hg

/-- **N2Z-FIRSTMODE from the variance node.** -/
theorem n2ZFirstMode_of_var (hV : N2ZFirstModeVarStmt) : N2ZFirstModeStmt :=
  n2ZFirstMode_of_mom (n2ZFirstModeMom_of_var hV)

end D3Plus
end QuantumZipper
