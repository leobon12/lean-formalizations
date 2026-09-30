import QuantumZipper.Proofs.Zipper.E5Final5f
import QuantumZipper.Proofs.Zipper.E5Final5c

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# E5-REPR-FINAL, part g: the D3⁺ `Setup`s of the level zoom model, all inputs discharged

Task E5-REPR-FINAL (Theorem 1.3, node E5, decision D39); Sheffield, arXiv:1012.4797, §5.4,
pp. 66–72 (proof of Lemma 5.6); blueprint `E_BRANCH_BLUEPRINT.md` §4 E5 steps (1)–(2).

On the level space `(Ω₁, Q) = ((ℝ≥0 × NS(P)) × Ω', (𝐑 ⊗ P').withDensity (w ∘ fst))` with the D28
field `X' = regField ϖ ρ₀ ∘ X₁ ∘ snd` and `Ξ =` the level point, the D28 switch (on the radius
event `radiusBad ϖ_τ r'`, fallback `0`) of the collision correction `locCorr κ V τ ϖ ρ₀ X'` at
**any** measurable nonnegative level time `τ` satisfies the D3⁺ `Setup` with **no remaining
hypotheses** beyond the E5 setup, a free base field and an admissible `ρ₀` vanishing on
`ball 0 r'` (`setup_lvl_locCorr_time`). In particular:

* `setup_lvl_true`: the true correction (time `T − T_ℓ`), the `g` of the zoom model;
* `setup_lvl_germFree`: the germ-free correction at the clipped time `max (T − T_ℓ − u₀) 0`
  (`E5Final5d`: a function of `(T − T_ℓ, D^{+u₀}, X')`), the repaired `g₀` of the zoom model.

Inputs: `E5IncSwitch.setup_locCorr_switch_reg`, `E5Final2.base_setup_lvl` with the Q-law facts
of `E5Final5c`, `hν` from `E5Final5e`, `hdrv` from `E5Final5f`. Own bookkeeping.
-/

noncomputable section
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E5

open ESM LengthMarkov StrongMarkov B2 E1 D3Plus

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ T : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample} {ϖ : Measure ℂ}
  {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']

/-- **The D3⁺ `Setup` of the switched collision correction at a general level time** on the
level space. -/
theorem setup_lvl_locCorr_time (hS : E5.Setup κ T P B X ϖ) (hBc : ∀ ω, Continuous (B · ω))
    {ρ₀ : Measure ℂ} {X₁ : Ω' → FieldSample}
    (hY : IsFreeGFFModConstH (fun ω' => regField ϖ ρ₀ (X₁ ω')) P')
    {μ : Measure (ℝ≥0 × NullMeasurableSpace Ω P)} [IsProbabilityMeasure μ]
    {w : ℝ≥0 × NullMeasurableSpace Ω P → ℝ≥0∞} (hw : Measurable w) (hw1 : ∫⁻ a, w a ∂μ = 1)
    {r r' : ℝ} (hr : 0 < r) (hrr : r < r') (hρ₀ : IsAdmissibleH ρ₀) (hρ1 : ρ₀ Set.univ = 1)
    (hρr : ρ₀ (Metric.ball (0 : ℂ) r) = 0) (hρr' : ρ₀ (Metric.ball (0 : ℂ) r') = 0)
    {τ : ℝ≥0 × NullMeasurableSpace Ω P → ℝ} (hτm : Measurable τ) (hτ0 : ∀ z, 0 ≤ τ z) :
    D3Plus.Setup (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) r ρ₀
      ((μ.prod P').withDensity (fun z => w z.1)) (lvlField (Ω' := Ω') ϖ ρ₀ X₁)
      (lvlXi : lvl Ω P Ω' → ℝ≥0 × NullMeasurableSpace Ω P)
      (switchG (radiusBad (fun z : lvl Ω P Ω' => varpiT (lvlDrv κ T B P z.1) (τ z.1) ϖ) r')
        (fun z => locCorr κ (lvlDrv κ T B P z.1) (τ z.1) ϖ ρ₀ (lvlField ϖ ρ₀ X₁ z))
        (fun _ _ => 0)) := by
  obtain ⟨hκ, hκ4, _, _, _, _, hϖn⟩ := id hS
  have hbase := base_setup_lvl (Ω' := Ω') (κ := κ) (P := P) (ϖ := ϖ) (ρ₀ := ρ₀) (X₁ := X₁)
    (Rr₁ := μ.prod P') (w₁ := fun z => w z.1) hκ hκ4 hr (lvlField_isFreeGFF hY hw hw1)
    (lvlXi_indep_lvlField hY hw hw1) hρ₀ hρ1 hρr
  exact setup_locCorr_switch_reg (Ω₁ := lvl Ω P Ω') (E' := ℝ≥0 × NullMeasurableSpace Ω P)
    (X := fun z : lvl Ω P Ω' => X₁ z.2) hrr κ hbase hρr' hϖn
    (fun z : lvl Ω P Ω' => lvlDrv κ T B P z.1) (fun z => τ z.1)
    (fun z => continuous_Vr_e5 (hBc (ofCompl P z.1.2))) (fun z => hτ0 z.1)
    (fun A hA => measurable_varpiT_lvl_time hS hBc hτm hτ0 hA)
    (fun z => measurable_locCorrDrv_lvl_time hS hBc hτm hτ0 z)

/-- **`Setup` for the true correction** (level collision time `T − T_ℓ`): the `g` field of the
level zoom model. -/
theorem setup_lvl_true (hS : E5.Setup κ T P B X ϖ) (hBc : ∀ ω, Continuous (B · ω))
    {ρ₀ : Measure ℂ} {X₁ : Ω' → FieldSample}
    (hY : IsFreeGFFModConstH (fun ω' => regField ϖ ρ₀ (X₁ ω')) P')
    {μ : Measure (ℝ≥0 × NullMeasurableSpace Ω P)} [IsProbabilityMeasure μ]
    {w : ℝ≥0 × NullMeasurableSpace Ω P → ℝ≥0∞} (hw : Measurable w) (hw1 : ∫⁻ a, w a ∂μ = 1)
    {r r' : ℝ} (hr : 0 < r) (hrr : r < r') (hρ₀ : IsAdmissibleH ρ₀) (hρ1 : ρ₀ Set.univ = 1)
    (hρr : ρ₀ (Metric.ball (0 : ℂ) r) = 0) (hρr' : ρ₀ (Metric.ball (0 : ℂ) r') = 0) :
    D3Plus.Setup (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) r ρ₀
      ((μ.prod P').withDensity (fun z => w z.1)) (lvlField (Ω' := Ω') ϖ ρ₀ X₁)
      (lvlXi : lvl Ω P Ω' → ℝ≥0 × NullMeasurableSpace Ω P)
      (switchG (radiusBad (fun z : lvl Ω P Ω' =>
          varpiT (lvlDrv κ T B P z.1) (lvlTime κ T B X P z.1) ϖ) r')
        (fun z => locCorr κ (lvlDrv κ T B P z.1) (lvlTime κ T B X P z.1) ϖ ρ₀
          (lvlField ϖ ρ₀ X₁ z))
        (fun _ _ => 0)) :=
  setup_lvl_locCorr_time hS hBc hY hw hw1 hr hrr hρ₀ hρ1 hρr hρr' (measurable_lvlTime hS hBc)
    (fun p => (levelArg_mem_Icc (κ := κ) (B := B) (X := X) hS.2.2.1 p.1 (ofCompl P p.2)).1)

/-- **`Setup` for the germ-free correction** (clipped time `max (T − T_ℓ − u₀) 0`, a function
of `(T − T_ℓ, D^{+u₀}, X')` by `E5Final5d.locCorr_lvl_shift_eq_max`): the repaired `g₀` field
of the level zoom model. -/
theorem setup_lvl_germFree (hS : E5.Setup κ T P B X ϖ) (hBc : ∀ ω, Continuous (B · ω))
    {ρ₀ : Measure ℂ} {X₁ : Ω' → FieldSample}
    (hY : IsFreeGFFModConstH (fun ω' => regField ϖ ρ₀ (X₁ ω')) P')
    {μ : Measure (ℝ≥0 × NullMeasurableSpace Ω P)} [IsProbabilityMeasure μ]
    {w : ℝ≥0 × NullMeasurableSpace Ω P → ℝ≥0∞} (hw : Measurable w) (hw1 : ∫⁻ a, w a ∂μ = 1)
    {r r' : ℝ} (hr : 0 < r) (hrr : r < r') (hρ₀ : IsAdmissibleH ρ₀) (hρ1 : ρ₀ Set.univ = 1)
    (hρr : ρ₀ (Metric.ball (0 : ℂ) r) = 0) (hρr' : ρ₀ (Metric.ball (0 : ℂ) r') = 0)
    (u₀ : ℝ≥0) :
    D3Plus.Setup (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) r ρ₀
      ((μ.prod P').withDensity (fun z => w z.1)) (lvlField (Ω' := Ω') ϖ ρ₀ X₁)
      (lvlXi : lvl Ω P Ω' → ℝ≥0 × NullMeasurableSpace Ω P)
      (switchG (radiusBad (fun z : lvl Ω P Ω' =>
          varpiT (lvlDrv κ T B P z.1) (max (lvlTime κ T B X P z.1 - u₀) 0) ϖ) r')
        (fun z => locCorr κ (lvlDrv κ T B P z.1) (max (lvlTime κ T B X P z.1 - u₀) 0) ϖ ρ₀
          (lvlField ϖ ρ₀ X₁ z))
        (fun _ _ => 0)) :=
  setup_lvl_locCorr_time hS hBc hY hw hw1 hr hrr hρ₀ hρ1 hρr hρr'
    (((measurable_lvlTime hS hBc).sub_const _).max measurable_const) (fun _ => le_max_right _ _)

end E5
end QuantumZipper
