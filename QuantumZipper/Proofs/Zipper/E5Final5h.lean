import QuantumZipper.Proofs.Zipper.E5Final5g
import QuantumZipper.Proofs.Zipper.E5Final5b

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# E5-REPR-FINAL, part h: the level zoom node from its remaining analytic parts

Task E5-REPR-FINAL (Theorem 1.3, node E5, decision D39); Sheffield, arXiv:1012.4797, §5.4,
pp. 66–72 (proof of Lemma 5.6); blueprint `E_BRANCH_BLUEPRINT.md` §4 E5 steps (1)–(3).

`E5Final5b.E5LvlZoomStmt` (a zoom model on the level space with the true correction off a small
set) is reduced here to `E5LvlZoomPartsStmt`, which asks, for every choice of radii `r < r'`
(with `ρ₀(ball 0 r') = 0`) and germ length `u₀ > 0`, only for the fields of the zoom model that
are not yet proved:

* `hm`: measurability of the local scale of the true (switched) correction `lvlGT`;
* `hbadm`, `hbad`: E5-G0 for the pair (`lvlGT`, `lvlGF`) — `condSigma`-measurability of `gBad`
  and tightness (the domination `E5Final1.e5G0_of_geometry_measurable_rt` is generic in the
  second correction);
* the germ-independent representation of the germ-free model data: `V ⊥ D|_{[0,u₀]}` under
  `𝐑 ⊗ P'` with the local scale/data of `lvlGF` functions `a C`, `y C` of `V` (`hay`; by
  `E5Final5d.locCorr_lvl_shift_eq_max` the natural choice is
  `V = ((T − T_ℓ, ω'), D^{+u₀})`).

Everything else is proved: the two D3⁺ `Setup`s (`E5Final5g`), the Q-law facts (`E5Final5c`),
the germ facts `hD`, `hDc`, `hDm` (`E5Final5d`) and `hDW` (E-SM(b), `E5Repair6.esm_germ_fields'`),
the Bayes form `Q = (𝐑 ⊗ P').withDensity (w ∘ fst)`, and the choice of the radius `r'` so that
the switch event has probability `≤ ε` (`E5LocB.exists_radius_bad_le`, `exists_radius_varpiT`);
the collision time of `zcfgTL` is the level time for the good version
(`E5HW0.palmTau_xL_eq_of`). Own bookkeeping.
-/

noncomputable section
set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E5

open ESM LengthMarkov LengthMarkov.GermDensity StrongMarkov B2 E1 E4Grid D3Plus

/-- The true switched level correction (level collision time `T − T_ℓ`). -/
def lvlGT {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (Ω' : Type) (κ T : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (ϖ ρ₀ : Measure ℂ) (X₁ : Ω' → FieldSample)
    (r' : ℝ) : lvl Ω P Ω' → ℂ → ℝ :=
  switchG (radiusBad (fun z : lvl Ω P Ω' =>
      varpiT (lvlDrv κ T B P z.1) (lvlTime κ T B X P z.1) ϖ) r')
    (fun z => locCorr κ (lvlDrv κ T B P z.1) (lvlTime κ T B X P z.1) ϖ ρ₀ (lvlField ϖ ρ₀ X₁ z))
    (fun _ _ => 0)

/-- The germ-free switched level correction (clipped time `max (T − T_ℓ − u₀) 0`). -/
def lvlGF {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (Ω' : Type) (κ T : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (ϖ ρ₀ : Measure ℂ) (X₁ : Ω' → FieldSample)
    (r' : ℝ) (u₀ : ℝ≥0) : lvl Ω P Ω' → ℂ → ℝ :=
  switchG (radiusBad (fun z : lvl Ω P Ω' =>
      varpiT (lvlDrv κ T B P z.1) (max (lvlTime κ T B X P z.1 - u₀) 0) ϖ) r')
    (fun z => locCorr κ (lvlDrv κ T B P z.1) (max (lvlTime κ T B X P z.1 - u₀) 0) ϖ ρ₀
      (lvlField ϖ ρ₀ X₁ z))
    (fun _ _ => 0)

/-- **The remaining analytic parts of the level zoom model** (hypotheses as in
`E5LvlZoomStmt`; for all radii `0 < r < r'` with `ρ₀(ball 0 r') = 0` and all `u₀ > 0`). -/
def E5LvlZoomPartsStmt : Prop :=
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
      (∀ ε : ℝ≥0∞, 0 < ε → ∃ K : ℝ, 0 ≤ K ∧
        (((esmRr κ T B X P lvlMu).prod P').withDensity (fun z => w z.1))
          (gBad r (lvlGT P Ω' κ T B X ϖ ρ₀ X₁ r') (lvlGF P Ω' κ T B X ϖ ρ₀ X₁ r' u₀) K) ≤ ε) ∧
      ∃ (𝕍 : Type) (_ : MeasurableSpace 𝕍) (V : lvl Ω P Ω' → 𝕍), Measurable V ∧
        IndepFun V (fun z => pathRestr u₀ (esmGerm κ T B X P z.1))
          ((esmRr κ T B X P lvlMu).prod P') ∧
        ∃ (a : ℝ → 𝕍 → ℝ) (y : ℝ → 𝕍 → (ℕ → ℝ) × (TestFun H → ℝ)),
          (∀ C, Measurable (a C)) ∧ (∀ C, Measurable (y C)) ∧
          ∀ C z, zScale (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) r ρ₀ C
              (lvlField ϖ ρ₀ X₁ z) (lvlGF P Ω' κ T B X ϖ ρ₀ X₁ r' u₀ z) = a C (V z) ∧
            zLoc D3Plus.locFieldFull (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) r ρ₀ R C
              (lvlField ϖ ρ₀ X₁ z) (lvlGF P Ω' κ T B X ϖ ρ₀ X₁ r' u₀ z) = y C (V z)

/-- **Reduction of the level zoom node to its remaining analytic parts.** -/
theorem e5LvlZoomStmt_of_parts (hP : E5LvlZoomPartsStmt) : E5LvlZoomStmt := by
  intro κ T Ω _ P _ B X ϖ hBc hS hG hpos w hw hw1 Ω' _ P' _ X₁ ρ₀ r₀ hX₁ hρ₀ hρ1 hr₀ hρB hX'g
    R W _ hW ε hε
  obtain ⟨hκ, hκ4, hT, hB, hX, hind, hϖ⟩ := id hS
  have hfin := esmMeas_lvlMu_ne_top (κ := κ) (T := T) (B := B) (X := X) (P := P)
  have hμp : IsProbabilityMeasure (esmRr κ T B X P lvlMu) :=
    isProbabilityMeasure_esmRr lvlMu hpos hfin
  set μ := esmRr κ T B X P lvlMu with hμ
  set Qm : Measure (lvl Ω P Ω') := (μ.prod P').withDensity (fun z => w z.1) with hQm
  have hw1' : ∫⁻ z, w z.1 ∂(μ.prod P') = 1 := by
    have hm : Measurable fun z : (ℝ≥0 × NullMeasurableSpace Ω P) × Ω' => w z.1 :=
      hw.comp measurable_fst
    rw [lintegral_prod _ hm.aemeasurable]
    simp only [lintegral_const, measure_univ, mul_one]
    exact hw1
  have hQp : IsProbabilityMeasure Qm := isProbMeas_withDensity_e5f5 hw1'
  -- the radius
  have htime : Measurable fun p : ℝ≥0 × NullMeasurableSpace Ω P => lvlTime κ T B X P p :=
    measurable_lvlTime hS hBc
  have ht0 : ∀ p : ℝ≥0 × NullMeasurableSpace Ω P, 0 ≤ lvlTime κ T B X P p := fun p =>
    (levelArg_mem_Icc (κ := κ) (B := B) (X := X) hT p.1 (ofCompl P p.2)).1
  set ν : lvl Ω P Ω' → Measure ℂ := fun z =>
    varpiT (lvlDrv κ T B P z.1) (lvlTime κ T B X P z.1) ϖ with hν
  have hνm : ∀ A : Set ℂ, MeasurableSet A → Measurable fun z => ν z A := fun A hA =>
    (measurable_varpiT_level_time hS hBc htime ht0 hA).comp measurable_fst
  have hνpos : ∀ᵐ z ∂Qm, ∃ r > 0, ν z (Metric.ball (0 : ℂ) r) = 0 :=
    ae_of_all _ fun z => exists_radius_varpiT hϖ (continuous_Vr_e5 (hBc (ofCompl P z.1.2)))
      (ht0 z.1)
  obtain ⟨rε, hrε, hQε⟩ := exists_radius_bad_le Qm ν hνm hνpos hε
  set r' := min rε r₀ with hr'
  have hr'0 : 0 < r' := lt_min hrε hr₀
  set r := r' / 2 with hr
  have hr0 : 0 < r := half_pos hr'0
  have hrr : r < r' := half_lt_self hr'0
  have hρr' : ρ₀ (Metric.ball (0 : ℂ) r') = 0 :=
    measure_mono_null (Metric.ball_subset_ball (min_le_right _ _)) hρB
  have hρr : ρ₀ (Metric.ball (0 : ℂ) r) = 0 :=
    measure_mono_null (Metric.ball_subset_ball hrr.le) hρr'
  have hY := isFreeGFFModConstH_regField hX₁ hϖ hρ₀
  obtain ⟨hm, hbadm, hbad, 𝕍, m𝕍, V, hV, hindV, a, y, ha, hy, hay⟩ :=
    hP κ T P B X ϖ hBc hS hG hpos w hw hw1 P' X₁ ρ₀ hX₁ hρ₀ hρ1 hX'g R r r' hr0 hrr hρr' 1
      one_pos
  -- the germ facts
  have hGF := esm_germ_fields' hκ hκ4 hT hB hX hind hBc lvlMu hpos hfin
    (V := fun _ : ℝ≥0 × Ω => (0 : ℝ)) measurable_const (fun _ => measurable_const) P'
    (Φ := fun _ => (0 : ℝ)) measurable_const 1 hW
  have hDW := hGF.2.2.1
  have hDmeas := hGF.2.2.2.1
  have hS1 := setup_lvl_true hS hBc hY hw hw1 hr0 hrr hρ₀ hρ1 hρr hρr' (μ := μ) (P' := P')
  have hS0 := setup_lvl_germFree hS hBc hY hw hw1 hr0 hrr hρ₀ hρ1 hρr hρr' 1 (μ := μ) (P' := P')
  let M : ZoomModel D3Plus.locFieldFull κ R W :=
    { Ω₁ := lvl Ω P Ω'
      mΩ₁ := inferInstance
      Q := Qm
      hQp := hQp
      X' := lvlField ϖ ρ₀ X₁
      E' := ℝ≥0 × NullMeasurableSpace Ω P
      mE' := inferInstance
      Ξ := lvlXi
      r := r
      ρ₀ := ρ₀
      g := lvlGT P Ω' κ T B X ϖ ρ₀ X₁ r'
      g₀ := lvlGF P Ω' κ T B X ϖ ρ₀ X₁ r' 1
      hS := hS1
      hS₀ := hS0
      hm := hm
      hm₀ := fun C => by
        convert (ha C).comp hV using 1
        funext z
        exact (hay C z).1
      hbadm := hbadm
      hbad := hbad
      Rr := μ.prod P'
      hRr := inferInstance
      w := fun z => w z.1
      hw1 := hw1'
      hQ := rfl
      𝕍 := 𝕍
      m𝕍 := m𝕍
      V := V
      hV := hV
      D := fun z => esmGerm κ T B X P z.1
      hD := hDmeas
      hDm := measurable_condSigma_lvlGerm hS hBc ρ₀ X₁ r
      hDc := fun z => continuous_esmGerm hBc z.1
      u₀ := 1
      hu₀ := one_pos
      hind := hindV
      hDW := hDW
      a := a
      ha := ha
      y := y
      hy := hy
      hay := hay }
  refine ⟨M, id, measurable_id, ?_, fun _ => rfl, fun _ => rfl, ?_⟩
  · show Qm.map id = (μ.withDensity w).prod P'
    rw [Measure.map_id, hQm, lvl_measure_eq hw]
  · show Qm {z | lvlGT P Ω' κ T B X ϖ ρ₀ X₁ r' z ≠ locCorr κ (lvlV κ T B P z)
      (lvlTau κ T B X P z) ϖ ρ₀ (lvlField ϖ ρ₀ X₁ z)} ≤ ε
    refine le_trans (measure_mono fun z hz => ?_) hQε
    by_contra hn
    apply hz
    have hn' : z ∉ radiusBad ν r' := fun h => hn (radiusBad_mono ν (min_le_left _ _) h)
    have htau : lvlTau κ T B X P z = lvlTime κ T B X P z.1 :=
      palmTau_xL_eq_of hT (hBc (ofCompl P z.1.2)) (hG (ofCompl P z.1.2)).1
        (hG (ofCompl P z.1.2)).2 z.1.1
    rw [htau]
    exact switchG_of_not_mem hn'

/-- **The repaired E5 representation input from the remaining level-zoom parts.** -/
theorem e5ReprG'_of_parts (hP : E5LvlZoomPartsStmt) (hN : ZoomModelNonemptyStmt) :
    E5ReprG' D3Plus.locFieldFull :=
  e5ReprG'_of_zoom (e5LvlZoomStmt_of_parts hP) hN

end E5
end QuantumZipper
