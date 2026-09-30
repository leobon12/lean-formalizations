import QuantumZipper.Proofs.Zipper.E5Final5i

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# E5-REPR-FINAL, part j: `condSigma`-measurability of the E5-G0 bad events

Task E5-REPR-FINAL (Theorem 1.3, node E5, decision D39); Sheffield, arXiv:1012.4797, §5.4;
blueprint `E_BRANCH_BLUEPRINT.md` §4 E5 step (2).

The field `hbadm` of the zoom model asks `gBad r g g₀ K = {¬ ∀ z ∈ ball 0 r ∩ Hbar,
|g − g₀| ≤ K}` to be measurable for `condSigma Ξ X' r`. When `z ↦ g ω z − g₀ ω z` is continuous
on `ball 0 r ∩ Hbar` and each `ω ↦ g ω z`, `ω ↦ g₀ ω z` is measurable (the `gmeas` field of the
two `Setup`s), the uncountable condition reduces to a countable dense subset
(`measurableSet_gBad_of_continuousOn`). For the level corrections the continuity holds at every
sample (`continuous_locCorr`: `k_{ϖ_t}` is continuous; `continuous_lvlGT`, `continuous_lvlGF`).
So `E5LvlZoomParts2Stmt` follows from `E5LvlZoomParts3Stmt` (the same without `hbadm`).
Own elementary argument (separability and density).
-/

noncomputable section
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E5

open ESM LengthMarkov LengthMarkov.GermDensity StrongMarkov B2 E1 E4Grid D3Plus

/-- **Measurability of `gBad` from pointwise measurability and continuity in `z`.** -/
theorem measurableSet_gBad_of_continuousOn {Ω₁ : Type} {m : MeasurableSpace Ω₁} {r K : ℝ}
    {g g₀ : Ω₁ → ℂ → ℝ} (hgm : ∀ z, Measurable[m] fun ω => g ω z)
    (hg₀m : ∀ z, Measurable[m] fun ω => g₀ ω z)
    (hc : ∀ ω, ContinuousOn (fun z => g ω z - g₀ ω z) (Metric.ball (0 : ℂ) r ∩ Hbar)) :
    MeasurableSet[m] (gBad r g g₀ K) := by
  set S : Set ℂ := Metric.ball (0 : ℂ) r ∩ Hbar with hSdef
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense S
  have e : gBad r g g₀ K = ⋃ z ∈ D, {ω | K < |g ω (z : ℂ) - g₀ ω (z : ℂ)|} := by
    ext ω
    simp only [gBad, Set.mem_ofPred_eq, mem_iUnion, exists_prop]
    constructor
    · intro h
      by_contra hn
      push Not at hn
      apply h
      have hcl : IsClosed {z : S | |g ω (z : ℂ) - g₀ ω (z : ℂ)| ≤ K} :=
        isClosed_le (continuous_abs.comp (hc ω).domRestrict) continuous_const
      have hsub : D ⊆ {z : S | |g ω (z : ℂ) - g₀ ω (z : ℂ)| ≤ K} := fun z hz => hn z hz
      have hall := closure_minimal hsub hcl
      rw [hDd.closure_eq] at hall
      intro z hz
      exact hall (mem_univ (⟨z, hz⟩ : S))
    · rintro ⟨z, -, hz⟩ h
      exact absurd (h z z.2) (not_le.2 hz)
  rw [e]
  refine MeasurableSet.biUnion hDc fun z _ => ?_
  exact measurableSet_lt measurable_const
    (continuous_abs.measurable.comp ((hgm (z : ℂ)).sub (hg₀m (z : ℂ))))

/-- **The collision correction is continuous** (for the pushed normalizer). -/
theorem continuous_locCorr {κ t : ℝ} {V : ℝ → ℝ} {ϖ : Measure ℂ} (ρ₀ : Measure ℂ)
    (x : FieldSample) (hϖ : IsNormalizer ϖ) (hV : Continuous V) (ht : 0 ≤ t) :
    Continuous (locCorr κ V t ϖ ρ₀ x) :=
  (continuous_const.mul (continuous_kPot_varpiT hϖ hV ht)).add continuous_const

theorem continuous_switchG_zero {O : Type} [MeasurableSpace O] {bad : Set O} {g : O → ℂ → ℝ}
    {ω : O} (h : Continuous (g ω)) : Continuous (switchG bad g (fun _ _ => 0) ω) := by
  classical
  by_cases hω : ω ∈ bad
  · rw [switchG_of_mem hω]; exact continuous_const
  · rw [switchG_of_not_mem hω]; exact h

section Level

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {κ T : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample} {ϖ : Measure ℂ}
  {Ω' : Type} [MeasurableSpace Ω']

theorem continuous_lvlGT (hϖ : IsNormalizer ϖ) (hT : 0 < T) (hBc : ∀ ω, Continuous (B · ω))
    (ρ₀ : Measure ℂ) (X₁ : Ω' → FieldSample) (r' : ℝ) (z : lvl Ω P Ω') :
    Continuous (lvlGT P Ω' κ T B X ϖ ρ₀ X₁ r' z) :=
  continuous_switchG_zero (continuous_locCorr ρ₀ _ hϖ (continuous_Vr_e5 (hBc (ofCompl P z.1.2)))
    (levelArg_mem_Icc (κ := κ) (B := B) (X := X) hT z.1.1 (ofCompl P z.1.2)).1)

theorem continuous_lvlGF (hϖ : IsNormalizer ϖ) (hBc : ∀ ω, Continuous (B · ω))
    (ρ₀ : Measure ℂ) (X₁ : Ω' → FieldSample) (r' : ℝ) (u₀ : ℝ≥0) (z : lvl Ω P Ω') :
    Continuous (lvlGF P Ω' κ T B X ϖ ρ₀ X₁ r' u₀ z) :=
  continuous_switchG_zero (continuous_locCorr ρ₀ _ hϖ (continuous_Vr_e5 (hBc (ofCompl P z.1.2)))
    (le_max_right _ _))

end Level

/-- **The remaining level-zoom parts without `hbad`, `hbadm`**: the local-scale measurability
`hm` of `lvlGT` and the germ-independent representation (`V`, `hind`, `a`, `y`, `hay`) of the
germ-free model data (as `E5LvlZoomPartsStmt` with the two E5-G0 conjuncts dropped). -/
def E5LvlZoomParts3Stmt : Prop :=
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
      (∀ C : ℝ, Measurable fun z : lvl Ω P Ω' =>
        zScale (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) r ρ₀ C (lvlField ϖ ρ₀ X₁ z)
          (lvlGT P Ω' κ T B X ϖ ρ₀ X₁ r' z)) ∧
      ∃ (𝕍 : Type) (_ : MeasurableSpace 𝕍) (V : lvl Ω P Ω' → 𝕍), Measurable V ∧
        IndepFun V (fun z => pathRestr u₀ (esmGerm κ T B X P z.1))
          ((esmRr κ T B X P lvlMu).prod P') ∧
        ∃ (a : ℝ → 𝕍 → ℝ) (y : ℝ → 𝕍 → (ℕ → ℝ) × (TestFun H → ℝ)),
          (∀ C, Measurable (a C)) ∧ (∀ C, Measurable (y C)) ∧
          ∀ C z, zScale (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) r ρ₀ C
              (lvlField ϖ ρ₀ X₁ z) (lvlGF P Ω' κ T B X ϖ ρ₀ X₁ r' u₀ z) = a C (V z) ∧
            zLoc D3Plus.locFieldFull (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) r ρ₀ R C
              (lvlField ϖ ρ₀ X₁ z) (lvlGF P Ω' κ T B X ϖ ρ₀ X₁ r' u₀ z) = y C (V z)

/-- **`hbadm` is automatic**: `E5LvlZoomParts3Stmt → E5LvlZoomParts2Stmt`. -/
theorem e5LvlZoomParts2Stmt_of_parts3 (h : E5LvlZoomParts3Stmt) : E5LvlZoomParts2Stmt := by
  intro κ T Ω _ P _ B X ϖ hBc hS hG hpos w hw hw1 Ω' _ P' _ X₁ ρ₀ hX₁ hρ₀ hρ1 hX'g R r r' hr
    hrr hρr' u₀ hu₀
  obtain ⟨hm, hrest⟩ :=
    h κ T P B X ϖ hBc hS hG hpos w hw hw1 P' X₁ ρ₀ hX₁ hρ₀ hρ1 hX'g R r r' hr hrr hρr' u₀ hu₀
  refine ⟨hm, fun K => ?_, hrest⟩
  obtain ⟨hκ, hκ4, hT, hB, hX, hind, hϖ⟩ := id hS
  have hfin := esmMeas_lvlMu_ne_top (κ := κ) (T := T) (B := B) (X := X) (P := P)
  have hμp : IsProbabilityMeasure (esmRr κ T B X P lvlMu) :=
    isProbabilityMeasure_esmRr lvlMu hpos hfin
  have hρr : ρ₀ (Metric.ball (0 : ℂ) r) = 0 :=
    measure_mono_null (Metric.ball_subset_ball hrr.le) hρr'
  have hY := isFreeGFFModConstH_regField hX₁ hϖ hρ₀
  have hS1 := setup_lvl_true hS hBc hY hw hw1 hr hrr hρ₀ hρ1 hρr hρr'
    (μ := esmRr κ T B X P lvlMu) (P' := P')
  have hS0 := setup_lvl_germFree hS hBc hY hw hw1 hr hrr hρ₀ hρ1 hρr hρr' u₀
    (μ := esmRr κ T B X P lvlMu) (P' := P')
  exact measurableSet_gBad_of_continuousOn hS1.gmeas hS0.gmeas fun z =>
    ((continuous_lvlGT hϖ hT hBc ρ₀ X₁ r' z).sub
      (continuous_lvlGF hϖ hBc ρ₀ X₁ r' u₀ z)).continuousOn

/-- **The repaired E5 representation input from the two remaining level-zoom parts.** -/
theorem e5ReprG'_of_parts3 (hP : E5LvlZoomParts3Stmt) (hN : ZoomModelNonemptyStmt) :
    E5ReprG' D3Plus.locFieldFull :=
  e5ReprG'_of_parts (e5LvlZoomPartsStmt_of_parts2 (e5LvlZoomParts2Stmt_of_parts3 hP)) hN

end E5
end QuantumZipper
