import QuantumZipper.Proofs.Zipper.E5PartsZoom
import QuantumZipper.Proofs.Zipper.E5Final5j

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# E5-PARTS, part 3: the level-zoom parts `E5LvlZoomParts3Stmt`

Task E5-PARTS (Theorem 1.3, node E5, decision D39; Sheffield, arXiv:1012.4797, §5.4,
pp. 66–72, proof of Lemma 5.6).

`E5LvlZoomParts3Stmt` has two conjuncts:
(a) everywhere-measurability of the local scale of the true level model field;
(b) a germ-independent measurable representation `(V, a, y)` of the germ-free model data.

Proved here:
* `measurable_lvl_zScale_lvlGT`: conjunct (a), from `LvlZoomVagueStmt` (the local area measure of
  the D3⁺ model field on `halfDisc r` exists for every good base sample). The level fields are good
  at *every* sample (hypothesis `hX'g`, D28), so the local area measure exists everywhere and the
  local scale is the measurable surrogate `D3Plus.scaleSur (localZ, macroF)` everywhere
  (`E5PartsMeas.measurable_zScale_of_goodAll_e5p`).
* `measurable_levelTime_complStop`: the stopping-time measurability (`hVT` of
  `E5Repair6.esm_germ_fields'`) of `T − T_ℓ`, for the natural choice
  `V z = ((T − T_ℓ, z.2), D^{+u₀})` in (b).
* `e5LvlZoomParts3Stmt_of_vague`: `E5LvlZoomParts3Stmt` from `LvlZoomVagueStmt` and conjunct (b)
  (`E5LvlZoomPartsBStmt`, verbatim); wiring `e5ReprG'_of_vague`, `theorem1_3_of_vague` (with
  `ZoomModelNonemptyStmt` proved, `E5PartsZoom.zoomModelNonempty_holds`).

`LvlZoomVagueStmt` is the local rule (the local quantum area of a good field plus a continuous
function is the exponential reweighting of its local area; `LocalRule.isVagueLimitOn_add_ofFun`,
as in `D3Plus.qAreaMeasureOn_zoomModel`); it is proved in `E5PartsVague.lvlZoomVague_holds`, so
`E5LvlZoomParts3Stmt` reduces to its conjunct (b) (`E5PartsVague.e5LvlZoomParts3Stmt_of_partsB`).
Own elementary bookkeeping otherwise.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E5

open ESM LengthMarkov LengthMarkov.GermDensity StrongMarkov B2 E1 E4Grid D3Plus

/-- **The local area measure of the D3⁺ model field exists for every good base sample**
(deterministic; `γ = √κ`, `α = γ − 2/γ`): if `x + ofFun(α(−log‖·‖))` is a good sample and `g` is
continuous, the area approximations of `zoomModel γ α C ρ₀ x g` have a vague limit on
`halfDisc r`. See the module docstring. -/
def LvlZoomVagueStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (x : FieldSample) (g : ℂ → ℝ) (ρ₀ : Measure ℂ) (C r : ℝ), 0 < r →
    Continuous g →
    IsLQGGood (Real.sqrt κ) (x + ofFun fun z => (Real.sqrt κ - 2 / Real.sqrt κ) * -Real.log ‖z‖) →
    ∃ m, IsVagueLimitOn (D3Plus.halfDisc r)
      (areaApprox (Real.sqrt κ) (D3Plus.zoomModel (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ)
        C ρ₀ x g)) m

/-- **Conjunct (a) of `E5LvlZoomParts3Stmt`**: the local scale of the true level model field is
measurable everywhere. -/
theorem measurable_lvl_zScale_lvlGT (hV : LvlZoomVagueStmt) {κ T : ℝ} {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    {X : Ω → FieldSample} {ϖ : Measure ℂ} (hBc : ∀ ω, Continuous (B · ω))
    (hS : E5.Setup κ T P B X ϖ) (hpos : esmMeas κ T B X P lvlMu univ ≠ 0)
    {w : ℝ≥0 × NullMeasurableSpace Ω P → ℝ≥0∞} (hw : Measurable w)
    (hw1 : ∫⁻ z, w z ∂esmRr κ T B X P lvlMu = 1)
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {X₁ : Ω' → FieldSample} {ρ₀ : Measure ℂ} (hX₁ : IsFreeGFFModConstH X₁ P')
    (hρ₀ : IsAdmissibleH ρ₀) (hρ1 : ρ₀ Set.univ = 1)
    (hX'g : ∀ ω', IsLQGGood (Real.sqrt κ) (regField ϖ ρ₀ (X₁ ω') +
      ofFun fun z => (Real.sqrt κ - 2 / Real.sqrt κ) * -Real.log ‖z‖))
    {r r' : ℝ} (hr : 0 < r) (hrr : r < r') (hρr' : ρ₀ (Metric.ball (0 : ℂ) r') = 0) (C : ℝ) :
    Measurable fun z : lvl Ω P Ω' =>
      zScale (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) r ρ₀ C (lvlField ϖ ρ₀ X₁ z)
        (lvlGT P Ω' κ T B X ϖ ρ₀ X₁ r' z) := by
  obtain ⟨hκ, hκ4, hT, hB, hX, hind, hϖ⟩ := id hS
  have hfin := esmMeas_lvlMu_ne_top (κ := κ) (T := T) (B := B) (X := X) (P := P)
  have hμp : IsProbabilityMeasure (esmRr κ T B X P lvlMu) :=
    isProbabilityMeasure_esmRr lvlMu hpos hfin
  have hρr : ρ₀ (Metric.ball (0 : ℂ) r) = 0 :=
    measure_mono_null (Metric.ball_subset_ball hrr.le) hρr'
  have hY := isFreeGFFModConstH_regField hX₁ hϖ hρ₀
  have hS1 : D3Plus.Setup (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) r ρ₀
      (((esmRr κ T B X P lvlMu).prod P').withDensity (fun z => w z.1))
      (lvlField (Ω' := Ω') ϖ ρ₀ X₁) (lvlXi : lvl Ω P Ω' → ℝ≥0 × NullMeasurableSpace Ω P)
      (lvlGT P Ω' κ T B X ϖ ρ₀ X₁ r') :=
    setup_lvl_true hS hBc hY hw hw1 hr hrr hρ₀ hρ1 hρr hρr'
  have hgood : ∀ z : lvl Ω P Ω', ∃ m, IsVagueLimitOn (D3Plus.halfDisc r)
      (areaApprox (Real.sqrt κ) (D3Plus.zoomModel (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ)
        C ρ₀ (lvlField ϖ ρ₀ X₁ z) (lvlGT P Ω' κ T B X ϖ ρ₀ X₁ r' z))) m := fun z =>
    hV κ hκ hκ4 _ _ ρ₀ C r hr (continuous_lvlGT hϖ hT hBc ρ₀ X₁ r' z) (hX'g z.2)
  generalize lvlGT P Ω' κ T B X ϖ ρ₀ X₁ r' = g at hS1 hgood ⊢
  exact measurable_zScale_of_goodAll_e5p hS1 hgood

/-- **`T − T_ℓ` is measurable for the stopped σ-algebra of `T_ℓ`** (the `hVT` input of
`E5Repair6.esm_germ_fields'` for `V (ℓ, ω) = T − T_ℓ(ω)`): a stopping time is measurable for its
own σ-algebra (`IsStoppingTime.measurableSet_le'`). -/
theorem measurable_levelTime_complStop {κ T : ℝ} {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}
    (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    (hBc : ∀ ω, Continuous (B · ω)) (ℓ : ℝ≥0) :
    Measurable[(complLevelStop hκ hκ4 hT hB hX hind hBc ℓ).measurableSpace]
      ((fun ω => T - ((levelTime (lenA κ T B X) T.toNNReal ℓ ω : ℝ≥0) : ℝ)) ∘ ofCompl P) := by
  set hτ := complLevelStop hκ hκ4 hT hB hX hind hBc ℓ with hτdef
  have key : ∀ x : ℝ≥0, MeasurableSet[hτ.measurableSpace]
      ((fun ω => (levelTime (lenA κ T B X) T.toNNReal ℓ (ofCompl P ω) : ℝ≥0)) ⁻¹' Iic x) := by
    intro x
    have h := hτ.measurableSet_le' x
    convert h using 1
    ext ω
    simp only [mem_preimage, mem_Iic, mem_ofPred_eq]
    exact WithTop.coe_le_coe.symm
  have hm := measurable_of_Iic (mδ := hτ.measurableSpace) key
  exact measurable_const.sub (NNReal.continuous_coe.measurable.comp hm)

/-- **Conjunct (b) of `E5LvlZoomParts3Stmt`, verbatim** (the germ-independent representation of
the germ-free model data; natural `V z = ((T − T_ℓ, z.2), D^{+u₀})`,
`E5Final5d.locCorr_lvl_shift_eq_max`, independence from `E5Repair6.esm_germ_fields'` with
`hVT = measurable_levelTime_complStop`). -/
def E5LvlZoomPartsBStmt : Prop :=
  ∀ (κ T : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (ϖ : Measure ℂ),
    (∀ ω, Continuous (B · ω)) → E5.Setup κ T P B X ϖ → (∀ ω, GoodVr κ T (Vr κ T B ω)) →
    esmMeas κ T B X P lvlMu univ ≠ 0 →
    ∀ (w : ℝ≥0 × NullMeasurableSpace Ω P → ℝ≥0∞), Measurable w →
      ∫⁻ z, w z ∂esmRr κ T B X P lvlMu = 1 →
    ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
      (X₁ : Ω' → FieldSample) (ρ₀ : Measure ℂ),
      IsFreeGFFModConstH X₁ P' → IsAdmissibleH ρ₀ → ρ₀ Set.univ = 1 →
      (∀ ω', IsLQGGood (Real.sqrt κ) (regField ϖ ρ₀ (X₁ ω') +
        ofFun fun z => (Real.sqrt κ - 2 / Real.sqrt κ) * -Real.log ‖z‖)) →
    ∀ (R : ℕ) (r r' : ℝ), 0 < r → r < r' → ρ₀ (Metric.ball (0 : ℂ) r') = 0 →
    ∀ u₀ : ℝ≥0, 0 < u₀ →
      ∃ (𝕍 : Type) (_ : MeasurableSpace 𝕍) (V : lvl Ω P Ω' → 𝕍), Measurable V ∧
        IndepFun V (fun z => pathRestr u₀ (esmGerm κ T B X P z.1))
          ((esmRr κ T B X P lvlMu).prod P') ∧
        ∃ (a : ℝ → 𝕍 → ℝ) (y : ℝ → 𝕍 → (ℕ → ℝ) × (TestFun H → ℝ)),
          (∀ C, Measurable (a C)) ∧ (∀ C, Measurable (y C)) ∧
          ∀ C z, zScale (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) r ρ₀ C
              (lvlField ϖ ρ₀ X₁ z) (lvlGF P Ω' κ T B X ϖ ρ₀ X₁ r' u₀ z) = a C (V z) ∧
            zLoc D3Plus.locFieldFull (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) r ρ₀ R C
              (lvlField ϖ ρ₀ X₁ z) (lvlGF P Ω' κ T B X ϖ ρ₀ X₁ r' u₀ z) = y C (V z)

/-- **`E5LvlZoomParts3Stmt` from `LvlZoomVagueStmt` and conjunct (b).** -/
theorem e5LvlZoomParts3Stmt_of_vague (hV : LvlZoomVagueStmt) (hB : E5LvlZoomPartsBStmt) :
    E5LvlZoomParts3Stmt := by
  intro κ T Ω _ P _ B X ϖ hBc hS hGv hpos w hw hw1 Ω' _ P' _ X₁ ρ₀ hX₁ hρ₀ hρ1 hX'g R r r' hr
    hrr hρr' u₀ hu₀
  exact ⟨fun C => measurable_lvl_zScale_lvlGT hV hBc hS hpos hw hw1 hX₁ hρ₀ hρ1 hX'g hr hrr
    hρr' C, hB κ T P B X ϖ hBc hS hGv hpos w hw hw1 P' X₁ ρ₀ hX₁ hρ₀ hρ1 hX'g R r r' hr hrr hρr'
    u₀ hu₀⟩

end E5
end QuantumZipper
