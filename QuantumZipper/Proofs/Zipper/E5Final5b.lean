import QuantumZipper.Proofs.Zipper.E5Final5a
import QuantumZipper.Proofs.Zipper.E5DrvWire

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# E5-REPR-FINAL, part b: the level-space model node from the zoom model with the true correction

Task E5-REPR-FINAL (Theorem 1.3, node E5, decision D39). Sheffield, arXiv:1012.4797, §5.4,
pp. 66–72 (proof of Lemma 5.6: the zoom at the collision point, "Lemma 5.6 … the field near
`η(τ)` looks like the field near the origin of an `α`-quantum wedge"); blueprint
`E_BRANCH_BLUEPRINT.md` §4 E5, steps (1)–(3).

`E5Final5a.E5LvlModelStmt` asks for a zoom model on the level space whose data agree with the
level configuration off a set of small outer measure. This file reduces it to
`E5LvlZoomStmt`: a zoom model on the level space (measurably identified with it) whose field is
the D28 field, whose germ is the E-SM germ, and whose correction `g` is the collision correction
`locCorr κ V τ ϖ ρ₀ X'` (`E5Model2`) off a set of small outer measure. The agreement off the
bad events is proved here from:

* **E5-LOC** (`E5LocB.locG_canonConfig_eq_data_of_good`, `E5Model2.locG_canonConfig_targetColl_eq_zLoc`,
  `E5DrvWire.drvIdentStmt_of_forall`): on `{0 < scale, scale·(R+1) < r}` with a quantum-area
  limit of the collision field, the rich local data of the canonicalized collision configuration
  is the zoom-model data (`locG_zcfgTL_eq_data_of_good`);
* `k_{ϖ_τ}` continuous (`E5LocA.continuous_kPot_varpiT`), the quantum-area limit a.s.
  (`E5LocB.ae_isVagueLimitOn_targetColl`, for the free field `M.X'` under `M.Q`);
* **D3⁺(iii)** (`E5Main3.tendsto_scaleBad`): the scale event `{¬(0 < scale < r/(R+1))}` has
  vanishing probability as `C → ∞` (`eventually_measure_scaleBad_le`).

Own bookkeeping otherwise.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E5

open ESM LengthMarkov LengthMarkov.GermDensity StrongMarkov B2 E1 CoordsFull E4Grid D3Plus

/-! ## 1. D3⁺(iii) in "eventually in `C`" form -/

/-- **The scale event of a zoom model has small probability eventually in `C`** (D3⁺(iii),
`tendsto_scaleBad`, turned from sequences into the `atTop` filter). -/
theorem ZoomModel.eventually_measure_scaleBad_le {F : Type} [MeasurableSpace F]
    {fr : ℕ → FieldSample → F} {κ : ℝ} {R : ℕ} {W : Measure (ℝ≥0 → ℝ)}
    (M : ZoomModel fr κ R W) {e : ℝ} (he : 0 < e) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∀ᶠ C in atTop, M.Q (scaleBad (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) M.r M.ρ₀ M.X'
      M.g e C) ≤ ε := by
  by_contra h
  rw [Filter.not_eventually] at h
  obtain ⟨Cs, hCs, hlt⟩ := Filter.exists_seq_forall_of_frequently h
  have ht := tendsto_scaleBad M.hS M.hm he Cs hCs
  obtain ⟨n, hn⟩ := (ht.eventually (Iio_mem_nhds hε)).exists
  exact hlt n (le_of_lt hn)

/-! ## 2. E5-LOC on the level space -/

section Level

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {κ T : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample} {ϖ : Measure ℂ}
  {Ω' : Type} [MeasurableSpace Ω']

/-- The level driver `V = Vr κ T B ω` at a level point. -/
def lvlV (κ T : ℝ) (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (z : (ℝ≥0 × NullMeasurableSpace Ω P) × Ω') :
    ℝ → ℝ :=
  Vr κ T B (ofCompl P z.1.2)

/-- The collision time `τ_{x(ℓ)}` at a level point (the time used by `zcfgTL`; it is the level
time `T − T_ℓ` for a good version, `E5HW0.palmTau_xL_eq_of`). -/
def lvlTau (κ T : ℝ) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (P : Measure Ω)
    (z : (ℝ≥0 × NullMeasurableSpace Ω P) × Ω') : ℝ :=
  palmTau κ T B (ofCompl P z.1.2) (xL κ T B X z.1.1 (ofCompl P z.1.2))

omit [MeasurableSpace Ω'] in
/-- **E5-LOC at a level point**: if the level field is `x`, the germ is `D`, `k_{ϖ_τ}` is
continuous on `ball 0 r`, the collision field has a quantum-area limit and the model scale `a`
of the collision correction satisfies `0 < a`, `a (R+1) < r`, then the rich local data of the
level configuration is the zoom-model data with correction `locCorr`. -/
theorem locG_zcfgTL_eq_data_of_good (X' : Ω' → FieldSample) (ρ₀ : Measure ℂ) (r C : ℝ) (R : ℕ)
    (z : (ℝ≥0 × NullMeasurableSpace Ω P) × Ω') (x : FieldSample) (hx : X' z.2 = x)
    (D : ℝ≥0 → ℝ) (hD : esmGerm κ T B X P z.1 = D)
    (hk : ContinuousOn (PalmNorm.kPot (varpiT (lvlV κ T B P z) (lvlTau κ T B X P z) ϖ))
      (Metric.ball (0 : ℂ) r))
    {μ : Measure ℂ} (hy : IsVagueLimitOn H (areaApprox (Real.sqrt κ)
      (addConst (Thm13Asm.targetColl κ (lvlV κ T B P z) (lvlTau κ T B X P z) ϖ x)
        (C / Real.sqrt κ))) μ)
    (hpos : 0 < zScale (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) r ρ₀ C x
      (locCorr κ (lvlV κ T B P z) (lvlTau κ T B X P z) ϖ ρ₀ x))
    (hlt : zScale (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) r ρ₀ C x
      (locCorr κ (lvlV κ T B P z) (lvlTau κ T B X P z) ϖ ρ₀ x) * ((R : ℝ) + 1) < r) :
    locG locFieldFull R (zcfgTL κ T B X P ϖ X' C z) =
      (zLoc locFieldFull (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) r ρ₀ R C x
          (locCorr κ (lvlV κ T B P z) (lvlTau κ T B X P z) ϖ ρ₀ x),
        drvWin κ R (LengthMarkov.GermDensity.rescale (R : ℝ≥0)
          (zScale (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) r ρ₀ C x
            (locCorr κ (lvlV κ T B P z) (lvlTau κ T B X P z) ϖ ρ₀ x)).toNNReal D)) := by
  have e : zcfgTL κ T B X P ϖ X' C z = canonConfig (Real.sqrt κ)
      (addConst (Thm13Asm.targetColl κ (lvlV κ T B P z) (lvlTau κ T B X P z) ϖ x)
        (C / Real.sqrt κ), drvMap κ D) := by
    rw [← hx, ← hD]; rfl
  rw [e]
  have hsc := (locG_canonConfig_targetColl_eq_zLoc κ (lvlV κ T B P z) (lvlTau κ T B X P z) ϖ ρ₀
    x C r R (drvMap κ D) hk hy hpos hlt).1
  exact locG_canonConfig_eq_data_of_good κ _ _ ϖ ρ₀ x C r R (drvMap κ D) D hk hy hpos hlt
    (drvIdentStmt_of_forall hpos.le hsc fun u => rfl)

end Level

/-! ## 3. The level-space zoom node and the reduction -/

/-- **The level-space zoom node with the true correction** (E5 steps (1)–(3), the remaining
construction). Hypotheses as in `E5LvlModelStmt`. Conclusion: a zoom model `M` and a measurable
map `φ` of its space to the level space carrying `M.Q` to `(𝐑.withDensity w) ⊗ P'`,
such that the model field is the D28 field `regField ϖ ρ₀ ∘ X₁ ∘ snd ∘ φ`, the model germ is the
E-SM germ `esmGerm ∘ fst ∘ φ`, and the model correction `M.g` is the collision correction
`locCorr κ V τ ϖ M.ρ₀ M.X'` (at the level driver `V` and collision time `τ`) off a set of outer
`M.Q`-measure `≤ ε`. -/
def E5LvlZoomStmt : Prop :=
  ∀ (κ T : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (ϖ : Measure ℂ),
    (∀ ω, Continuous (B · ω)) → E5.Setup κ T P B X ϖ → (∀ ω, GoodVr κ T (Vr κ T B ω)) →
    esmMeas κ T B X P lvlMu univ ≠ 0 →
    ∀ (w : ℝ≥0 × NullMeasurableSpace Ω P → ℝ≥0∞), Measurable w →
      ∫⁻ z, w z ∂esmRr κ T B X P lvlMu = 1 →
    ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
      (X₁ : Ω' → FieldSample) (ρ₀ : Measure ℂ) (r₀ : ℝ),
      IsFreeGFFModConstH X₁ P' → IsAdmissibleH ρ₀ → ρ₀ Set.univ = 1 → 0 < r₀ →
      ρ₀ (Metric.ball (0 : ℂ) r₀) = 0 →
      (∀ ω', IsLQGGood (Real.sqrt κ) (regField ϖ ρ₀ (X₁ ω') +
        ofFun fun z => (Real.sqrt κ - 2 / Real.sqrt κ) * -Real.log ‖z‖)) →
    ∀ (R : ℕ) (W : Measure (ℝ≥0 → ℝ)) [IsProbabilityMeasure W],
      IsPreBrownianReal (fun t (b : ℝ≥0 → ℝ) => b t) W →
    ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ (M : ZoomModel D3Plus.locFieldFull κ R W)
        (φ : M.Ω₁ → ((ℝ≥0 × NullMeasurableSpace Ω P) × Ω')), Measurable φ ∧
        M.Q.map φ = ((esmRr κ T B X P lvlMu).withDensity w).prod P' ∧
        (∀ ω, M.X' ω = regField ϖ ρ₀ (X₁ (φ ω).2)) ∧
        (∀ ω, M.D ω = esmGerm κ T B X P (φ ω).1) ∧
        M.Q {ω | M.g ω ≠ locCorr κ (lvlV κ T B P (φ ω)) (lvlTau κ T B X P (φ ω)) ϖ M.ρ₀
          (M.X' ω)} ≤ ε

/-- **Reduction of the level-space model node to the zoom node**: E5-LOC off the bad events
(correction switch, no quantum-area limit, scale event), the quantum-area limit a.s., and
D3⁺(iii) for the scale event. -/
theorem e5LvlModelStmt_of_zoom (h : E5LvlZoomStmt) : E5LvlModelStmt := by
  intro κ T Ω _ P _ B X ϖ hBc hS hG hpos w hw hw1 Ω' _ P' _ X₁ ρ₀ r₀ hX₁ hρ₀ hρ1 hr₀ hρB hX'g
    R W _ hW ε hε
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  obtain ⟨M, φ, hφm, hφ, hX', hD, hg⟩ :=
    h κ T P B X ϖ hBc hS hG hpos w hw hw1 P' X₁ ρ₀ r₀ hX₁ hρ₀ hρ1 hr₀ hρB hX'g R W hW (ε / 2) hε2
  refine ⟨M, φ, hφm, hφ, ?_⟩
  obtain ⟨-, -, -, -, -, -, hϖ⟩ := hS
  have hR1 : (0 : ℝ) < (R : ℝ) + 1 := by positivity
  have he : 0 < M.r / ((R : ℝ) + 1) := div_pos M.hS.hr hR1
  have hvag := ae_isVagueLimitOn_targetColl M.hS.hX M.hS.hγ M.hS.hγ2
  set N : Set M.Ω₁ := {ω | ¬ ∀ (κ' : ℝ) (V : ℝ → ℝ) (t : ℝ) (ϖ : Measure ℂ) (b : ℝ),
      Continuous (PalmNorm.kPot (varpiT V t ϖ)) →
      ∃ μ', IsVagueLimitOn H (areaApprox (Real.sqrt κ)
        (addConst (Thm13Asm.targetColl κ' V t ϖ (M.X' ω)) b)) μ'} with hN
  have hN0 : M.Q N = 0 := ae_iff.1 hvag
  set G : Set M.Ω₁ := {ω | M.g ω ≠ locCorr κ (lvlV κ T B P (φ ω)) (lvlTau κ T B X P (φ ω)) ϖ
    M.ρ₀ (M.X' ω)} with hGdef
  filter_upwards [M.eventually_measure_scaleBad_le he hε2] with C hC
  set S := scaleBad (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) M.r M.ρ₀ M.X' M.g
    (M.r / ((R : ℝ) + 1)) C with hSdef
  have hsub : {ω | locG D3Plus.locFieldFull R
      (zcfgTL κ T B X P ϖ (fun ω' => regField ϖ ρ₀ (X₁ ω')) C (φ ω)) ≠ M.data C ω} ⊆
      G ∪ N ∪ S := by
    intro ω hω
    by_contra hn
    simp only [mem_union, not_or] at hn
    obtain ⟨⟨hgω, hNω⟩, hSω⟩ := hn
    have hgω' : M.g ω = locCorr κ (lvlV κ T B P (φ ω)) (lvlTau κ T B X P (φ ω)) ϖ M.ρ₀
        (M.X' ω) := not_not.1 hgω
    have hNω' := not_not.1 hNω
    have hSω' := not_not.1 hSω
    rw [hgω'] at hSω'
    apply hω
    rw [M.data_eq, hgω']
    have hVc : Continuous (lvlV κ T B P (φ ω)) := continuous_Vr_e5 (hBc _)
    have ht : 0 ≤ lvlTau κ T B X P (φ ω) := ENNReal.toReal_nonneg
    have hk := continuous_kPot_varpiT hϖ hVc ht
    obtain ⟨μ, hμ⟩ := hNω' κ (lvlV κ T B P (φ ω)) (lvlTau κ T B X P (φ ω)) ϖ
      (C / Real.sqrt κ) hk
    exact locG_zcfgTL_eq_data_of_good (fun ω' => regField ϖ ρ₀ (X₁ ω')) M.ρ₀ M.r C R (φ ω)
      (M.X' ω) (hX' ω).symm (M.D ω) (hD ω).symm hk.continuousOn hμ hSω'.1
      ((lt_div_iff₀ hR1).1 hSω'.2)
  calc _ ≤ M.Q (G ∪ N ∪ S) := measure_mono hsub
    _ ≤ M.Q G + M.Q N + M.Q S :=
        (measure_union_le _ _).trans (by gcongr; exact measure_union_le _ _)
    _ ≤ ε / 2 + 0 + ε / 2 := by rw [hN0]; gcongr
    _ = ε := by rw [add_zero, ENNReal.add_halves]

/-- **E5 (repaired representation input) from the level-space zoom node.** -/
theorem e5ReprG'_of_zoom (hZ : E5LvlZoomStmt) (hN : ZoomModelNonemptyStmt) :
    E5ReprG' D3Plus.locFieldFull :=
  e5ReprG'_of_lvl (e5LvlModelStmt_of_zoom hZ) hN

end E5
end QuantumZipper
