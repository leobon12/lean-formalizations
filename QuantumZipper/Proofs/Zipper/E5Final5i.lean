import QuantumZipper.Proofs.Zipper.E5Final5h

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# E5-REPR-FINAL, part i: E5-G0 tightness from pointwise boundedness

Task E5-REPR-FINAL (Theorem 1.3, node E5, decision D39); Sheffield, arXiv:1012.4797, §5.4;
blueprint `E_BRANCH_BLUEPRINT.md` §4 E5 step (2) ("`‖g − g₀‖ ≤ K` with probability `→ 1` as
`K → ∞`").

The field `hbad` of the zoom model (`∀ ε > 0, ∃ K ≥ 0, Q(gBad r g g₀ K) ≤ ε`) only needs the
measurability of the events `gBad r g g₀ K` and the **pointwise** finiteness of
`sup_{ball 0 r ∩ Hbar} |g − g₀|` (continuity of measure from above, `tight_gBad`). For the level
corrections `lvlGT`, `lvlGF` the pointwise bound holds at every sample: `k_{ϖ_t}` is continuous on
`ℂ` for the pushed normalizer (`E5LocA.continuous_kPot_varpiT`), hence bounded on the closed
ball (`bdd_locCorr`, `bdd_lvlGT_sub_lvlGF`). So `E5LvlZoomPartsStmt` follows from
`E5LvlZoomParts2Stmt` (the same without `hbad`). Own elementary argument (compactness and
continuity from above), no region hypotheses needed.
-/

noncomputable section
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E5

open ESM LengthMarkov LengthMarkov.GermDensity StrongMarkov B2 E1 E4Grid D3Plus

/-- **Tightness of `gBad` from pointwise boundedness** (continuity from above). -/
theorem tight_gBad {Ω₁ : Type} [MeasurableSpace Ω₁] {Q : Measure Ω₁} [IsFiniteMeasure Q]
    {r : ℝ} {g g₀ : Ω₁ → ℂ → ℝ} (hm : ∀ K, MeasurableSet (gBad r g g₀ K))
    (hb : ∀ ω, ∃ K, ∀ z ∈ Metric.ball (0 : ℂ) r ∩ Hbar, |g ω z - g₀ ω z| ≤ K) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℝ, 0 ≤ K ∧ Q (gBad r g g₀ K) ≤ ε := by
  intro ε hε
  set A : ℕ → Set Ω₁ := fun n => gBad r g g₀ n with hA
  have hanti : Antitone A := by
    intro n m hnm ω hω
    simp only [hA, gBad, Set.mem_ofPred_eq] at hω ⊢
    intro h
    exact hω fun z hz => (h z hz).trans (by exact_mod_cast hnm)
  have hnull : (⋂ n, A n) = ∅ := by
    ext ω
    simp only [mem_iInter, mem_empty_iff_false, iff_false, not_forall]
    obtain ⟨K, hK⟩ := hb ω
    obtain ⟨n, hn⟩ := exists_nat_ge K
    refine ⟨n, ?_⟩
    simp only [hA, gBad, Set.mem_ofPred_eq, not_not]
    exact fun z hz => (hK z hz).trans hn
  have hmA : ∀ n, NullMeasurableSet (A n) Q := fun n => (hm n).nullMeasurableSet
  have ht := tendsto_measure_iInter_atTop (μ := Q) hmA hanti ⟨0, measure_ne_top _ _⟩
  rw [hnull, measure_empty] at ht
  obtain ⟨n, hn⟩ := (ht.eventually (Iio_mem_nhds hε)).exists
  exact ⟨n, Nat.cast_nonneg n, le_of_lt hn⟩

/-- **The collision correction is bounded on every closed disc** (continuity of `k_{ϖ_t}`). -/
theorem bdd_locCorr {κ t : ℝ} {V : ℝ → ℝ} {ϖ : Measure ℂ} (ρ₀ : Measure ℂ) (x : FieldSample)
    (hϖ : IsNormalizer ϖ) (hV : Continuous V) (ht : 0 ≤ t) (r : ℝ) :
    ∃ K, ∀ z ∈ Metric.closedBall (0 : ℂ) r, |locCorr κ V t ϖ ρ₀ x z| ≤ K := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) r).exists_bound_of_continuousOn
    (continuous_kPot_varpiT hϖ hV ht).continuousOn
  set c : ℝ := x ρ₀ - (ofFun (PalmNorm.shiftFun (Real.sqrt κ) (h0rev κ) (varpiT V t ϖ) 0) + x)
    (varpiT V t ϖ) - qt κ V t ϖ with hc
  refine ⟨|Real.sqrt κ / 2| * C + |c|, fun z hz => ?_⟩
  have e : locCorr κ V t ϖ ρ₀ x z = -(Real.sqrt κ / 2) * PalmNorm.kPot (varpiT V t ϖ) z + c := rfl
  rw [e]
  have h1 : |PalmNorm.kPot (varpiT V t ϖ) z| ≤ C := by
    have := hC z hz
    rwa [Real.norm_eq_abs] at this
  calc |-(Real.sqrt κ / 2) * PalmNorm.kPot (varpiT V t ϖ) z + c|
      ≤ |-(Real.sqrt κ / 2) * PalmNorm.kPot (varpiT V t ϖ) z| + |c| := abs_add_le _ _
    _ = |Real.sqrt κ / 2| * |PalmNorm.kPot (varpiT V t ϖ) z| + |c| := by
        rw [abs_mul, abs_neg]
    _ ≤ |Real.sqrt κ / 2| * C + |c| := by gcongr

/-- A switched correction with fallback `0` is bounded wherever the correction is. -/
theorem abs_switchG_zero_le {O : Type} [MeasurableSpace O] {bad : Set O} {g : O → ℂ → ℝ} {ω : O} {z : ℂ} {K : ℝ}
    (h : |g ω z| ≤ K) : |switchG bad g (fun _ _ => 0) ω z| ≤ max K 0 := by
  classical
  by_cases hω : ω ∈ bad
  · rw [switchG_of_mem hω]; simp
  · rw [switchG_of_not_mem hω]; exact h.trans (le_max_left _ _)

section Level

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {κ T : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample} {ϖ : Measure ℂ}
  {Ω' : Type} [MeasurableSpace Ω']

/-- **Pointwise boundedness of `lvlGT − lvlGF` on the disc**, at every level sample. -/
theorem bdd_lvlGT_sub_lvlGF (hϖ : IsNormalizer ϖ) (hT : 0 < T) (hBc : ∀ ω, Continuous (B · ω))
    (ρ₀ : Measure ℂ) (X₁ : Ω' → FieldSample) (r r' : ℝ) (u₀ : ℝ≥0) (z : lvl Ω P Ω') :
    ∃ K, ∀ v ∈ Metric.ball (0 : ℂ) r ∩ Hbar,
      |lvlGT P Ω' κ T B X ϖ ρ₀ X₁ r' z v - lvlGF P Ω' κ T B X ϖ ρ₀ X₁ r' u₀ z v| ≤ K := by
  have hVc : Continuous (lvlDrv κ T B P z.1) := continuous_Vr_e5 (hBc (ofCompl P z.1.2))
  have ht : 0 ≤ lvlTime κ T B X P z.1 :=
    (levelArg_mem_Icc (κ := κ) (B := B) (X := X) hT z.1.1 (ofCompl P z.1.2)).1
  obtain ⟨K1, hK1⟩ := bdd_locCorr (κ := κ) ρ₀ (lvlField ϖ ρ₀ X₁ z) hϖ hVc ht r
  obtain ⟨K2, hK2⟩ := bdd_locCorr (κ := κ) ρ₀ (lvlField ϖ ρ₀ X₁ z) hϖ hVc
    (le_max_right (lvlTime κ T B X P z.1 - u₀) 0) r
  refine ⟨max K1 0 + max K2 0, fun v hv => ?_⟩
  have hvb : v ∈ Metric.closedBall (0 : ℂ) r := Metric.ball_subset_closedBall hv.1
  calc |lvlGT P Ω' κ T B X ϖ ρ₀ X₁ r' z v - lvlGF P Ω' κ T B X ϖ ρ₀ X₁ r' u₀ z v|
      ≤ |lvlGT P Ω' κ T B X ϖ ρ₀ X₁ r' z v| + |lvlGF P Ω' κ T B X ϖ ρ₀ X₁ r' u₀ z v| :=
        abs_sub _ _
    _ ≤ max K1 0 + max K2 0 :=
        add_le_add (abs_switchG_zero_le (hK1 v hvb)) (abs_switchG_zero_le (hK2 v hvb))

end Level

/-- **The remaining level-zoom parts without `hbad`** (as `E5LvlZoomPartsStmt`, the tightness
conjunct dropped: it follows from `hbadm`, `tight_gBad` and `bdd_lvlGT_sub_lvlGF`). -/
def E5LvlZoomParts2Stmt : Prop :=
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
      (∀ K : ℝ, MeasurableSet[condSigma (lvlXi : lvl Ω P Ω' → ℝ≥0 × NullMeasurableSpace Ω P)
        (lvlField ϖ ρ₀ X₁) r]
        (gBad r (lvlGT P Ω' κ T B X ϖ ρ₀ X₁ r') (lvlGF P Ω' κ T B X ϖ ρ₀ X₁ r' u₀) K)) ∧
      ∃ (𝕍 : Type) (_ : MeasurableSpace 𝕍) (V : lvl Ω P Ω' → 𝕍), Measurable V ∧
        IndepFun V (fun z => pathRestr u₀ (esmGerm κ T B X P z.1))
          ((esmRr κ T B X P lvlMu).prod P') ∧
        ∃ (a : ℝ → 𝕍 → ℝ) (y : ℝ → 𝕍 → (ℕ → ℝ) × (TestFun H → ℝ)),
          (∀ C, Measurable (a C)) ∧ (∀ C, Measurable (y C)) ∧
          ∀ C z, zScale (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) r ρ₀ C
              (lvlField ϖ ρ₀ X₁ z) (lvlGF P Ω' κ T B X ϖ ρ₀ X₁ r' u₀ z) = a C (V z) ∧
            zLoc D3Plus.locFieldFull (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) r ρ₀ R C
              (lvlField ϖ ρ₀ X₁ z) (lvlGF P Ω' κ T B X ϖ ρ₀ X₁ r' u₀ z) = y C (V z)

/-- **`hbad` is automatic**: `E5LvlZoomParts2Stmt → E5LvlZoomPartsStmt`. -/
theorem e5LvlZoomPartsStmt_of_parts2 (h : E5LvlZoomParts2Stmt) : E5LvlZoomPartsStmt := by
  intro κ T Ω _ P _ B X ϖ hBc hS hG hpos w hw hw1 Ω' _ P' _ X₁ ρ₀ hX₁ hρ₀ hρ1 hX'g R r r' hr
    hrr hρr' u₀ hu₀
  obtain ⟨hm, hbadm, hrest⟩ :=
    h κ T P B X ϖ hBc hS hG hpos w hw hw1 P' X₁ ρ₀ hX₁ hρ₀ hρ1 hX'g R r r' hr hrr hρr' u₀ hu₀
  refine ⟨hm, hbadm, ?_, hrest⟩
  obtain ⟨hκ, hκ4, hT, hB, hX, hind, hϖ⟩ := id hS
  have hfin := esmMeas_lvlMu_ne_top (κ := κ) (T := T) (B := B) (X := X) (P := P)
  have hμp : IsProbabilityMeasure (esmRr κ T B X P lvlMu) :=
    isProbabilityMeasure_esmRr lvlMu hpos hfin
  have hρr : ρ₀ (Metric.ball (0 : ℂ) r) = 0 :=
    measure_mono_null (Metric.ball_subset_ball hrr.le) hρr'
  have hY := isFreeGFFModConstH_regField hX₁ hϖ hρ₀
  have hS1 := setup_lvl_true hS hBc hY hw hw1 hr hrr hρ₀ hρ1 hρr hρr'
    (μ := esmRr κ T B X P lvlMu) (P' := P')
  have hw1' : ∫⁻ z, w z.1 ∂((esmRr κ T B X P lvlMu).prod P') = 1 := by
    have hm' : Measurable fun z : (ℝ≥0 × NullMeasurableSpace Ω P) × Ω' => w z.1 :=
      hw.comp measurable_fst
    rw [lintegral_prod _ hm'.aemeasurable]
    simp only [lintegral_const, measure_univ, mul_one]
    exact hw1
  have hQp := isProbMeas_withDensity_e5f5 hw1'
  exact tight_gBad (fun K => condSigma_le_ambient hS1 _ (hbadm K))
    (bdd_lvlGT_sub_lvlGF hϖ hT hBc ρ₀ X₁ r r' u₀)

end E5
end QuantumZipper
