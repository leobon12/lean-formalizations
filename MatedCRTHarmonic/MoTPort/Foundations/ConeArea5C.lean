/- Provenance: ported from an earlier mating-of-trees formalization; only imports and namespace names were changed. -/
import MatedCRTHarmonic.MoTPort.Foundations.ConeArea5B

/-!
# Cone area, part 12: (b3) and `ConeRefMeas` from the whole-plane sup-moment bound

The last input of (b3) is the whole-plane version at the origin of QZ's interior area
fractional-moment bound `AtomlessUncond.P3bBoundArea` (proved for the free-boundary GFF on `ℍ` by
QZ `AreaP3b.fracMoment_area_interior`; Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.3
and §3.2 (14)–(15)):

  `WPSupMoment γ`: for a whole-plane GFF `X` normalized by `X_1(0)` and `0 < p ≤ 1`,
  `E (sup_{k ≥ n} μ_{2^{-k}}(B̄(0,2^{-n})))^p ≤ C 2^{n(γ²p²/2 − p(2 + γ²/2))}`.

From it:

* `ae_tight_logFactor`: a.s. the approximations weighted by `max(2^{-k},|w|)^{−γc}`, `c < Q`, are
  tight at `0` (QZ `AtomlessUncond.ae_tsum_ne_top_of_moments` — Borel–Cantelli with a geometric
  rate — and `AtomlessUncond.tight_of_balls`, exactly as in QZ `AreaNoAtom`);
* **`b3_of_supMoment`**: the cone-area tightness statement (b3), by ConeArea5 (comparison) and ConeArea5B
  (growth of the cone shift with `c = α + η < Q`);
* **`coneRefMeas_of_supMoment`**, **`exists_isQuantumCone_of_supMoment`**: `ConeRefMeas γ W` and
  quantum cones of every weight `W > 0` (via `ConeArea4.coneRefMeas_of_tight`,
  `Cone.exists_isQuantumCone`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.MoTPort
namespace ConeArea5

open QuantumZipper LQGMetric ConeArea4

/-- **whole-plane interior sup-moment bound at `0`** (the whole-plane analogue of QZ
`AtomlessUncond.P3bBoundArea` at an interior point, for the field normalized by `X_1(0)`) -/
def WPSupMoment (γ : ℝ) : Prop :=
  ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (X : Ω → Field),
    IsProbabilityMeasure P → IsWholePlaneGFF X P →
    ∀ p : ℝ, 0 < p → p ≤ 1 → ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∫⁻ ω, (ENNReal.ofReal (Real.exp (-(γ * circleAvg (X ω) 1 0))) *
          AtomlessUncond.annTC (areaApproxC γ (X ω)) 0 n) ^ p ∂P ≤
        C * ENNReal.ofReal ((2 : ℝ) ^ ((n : ℝ) * (γ ^ 2 * p ^ 2 / 2 - p * (2 + γ ^ 2 / 2))))

/-- **weighted tightness at `0`** for a whole-plane GFF, from `WPSupMoment` -/
theorem ae_tight_logFactor {γ c : ℝ} (hγ : 0 < γ) (hM : WPSupMoment γ) (hc : c < Qc γ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → Field}
    (hX : IsWholePlaneGFF X P) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ᶠ k in atTop, (areaApproxC γ (X ω) k).withDensity
        (fun w => ENNReal.ofReal (AtomlessUncond.logFactorA γ c 0 k w)) (ball 0 δ) ≤
          ENNReal.ofReal ε := by
  set gap : ℝ := 2 + γ ^ 2 / 2 - max c 0 * γ with hgap
  have hgap0 : 0 < gap := by
    have hQ : Qc γ * γ = 2 + γ ^ 2 / 2 := by unfold Qc; field_simp
    rcases le_total c 0 with h | h
    · rw [hgap, max_eq_right h, zero_mul, sub_zero]; positivity
    · rw [hgap, max_eq_left h]; nlinarith
  have hγ2 : 0 < γ ^ 2 := by positivity
  set p : ℝ := min 1 (gap / γ ^ 2) with hp
  have hp0 : 0 < p := lt_min one_pos (div_pos hgap0 hγ2)
  have hp1 : p ≤ 1 := min_le_left _ _
  have hpg : γ ^ 2 * p ≤ gap := by
    have := min_le_right 1 (gap / γ ^ 2)
    rw [← hp, le_div_iff₀ hγ2] at this; linarith
  set b : ℝ := LogSing.expB (2 * γ) c with hb
  set e : ℝ := γ ^ 2 * p ^ 2 / 2 - p * (2 + γ ^ 2 / 2) with he
  have hneg : b * p + e < 0 := by
    have : b * p + e = p * (γ ^ 2 * p / 2 - gap) := by
      rw [hb, he, hgap, LogSing.expB]; ring
    rw [this]
    exact mul_neg_of_pos_of_neg hp0 (by linarith)
  obtain ⟨C, hC, n₀, hbd⟩ := hM Ω inferInstance P X inferInstance hX p hp0 hp1
  set T : ℕ → Ω → ℝ≥0∞ := fun n ω => ENNReal.ofReal (Real.exp (-(γ * circleAvg (X ω) 1 0))) *
    AtomlessUncond.annTC (areaApproxC γ (X ω)) 0 n with hT
  have hTm : ∀ n, Measurable (T n) := fun n => by
    refine (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (((measurable_circleAvg_left 1 0).comp hX.measurable).const_mul γ).neg)).mul ?_
    unfold AtomlessUncond.annTC
    exact Measurable.iSup fun j => (Measure.measurable_coe measurableSet_closedBall).comp
      ((ConeArea.measurable_areaApproxC γ (j + n)).comp hX.measurable)
  have hsum := AtomlessUncond.ae_tsum_ne_top_of_moments (P := P) hTm hp0 hp1 hneg hC
    (n₀ := n₀) fun n hn => hbd n hn
  filter_upwards [hsum] with ω ⟨N, hN⟩
  set a := γ * circleAvg (X ω) 1 0
  have h1 : ENNReal.ofReal (Real.exp a) * ENNReal.ofReal (Real.exp (-a)) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, add_neg_cancel, Real.exp_zero,
      ENNReal.ofReal_one]
  have hsum' : ∑' n, LogSing.annW (2 * γ) c (n + N) *
      AtomlessUncond.annTC (areaApproxC γ (X ω)) 0 (n + N) ≠ ⊤ := by
    have e : ∀ n, LogSing.annW (2 * γ) c (n + N) *
        AtomlessUncond.annTC (areaApproxC γ (X ω)) 0 (n + N) =
        ENNReal.ofReal (Real.exp a) *
          (ENNReal.ofReal (radius (n + N + 1) ^ (-b)) * T (n + N) ω) := fun n => by
      simp only [hT, LogSing.annW, hb]
      calc _ = ENNReal.ofReal (radius (n + N + 1) ^ (-LogSing.expB (2 * γ) c)) *
            AtomlessUncond.annTC (areaApproxC γ (X ω)) 0 (n + N) *
              (ENNReal.ofReal (Real.exp a) * ENNReal.ofReal (Real.exp (-a))) := by
            rw [h1, mul_one]
        _ = _ := by ring
    simp_rw [e]
    rw [ENNReal.tsum_mul_left]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hN
  exact AtomlessUncond.tight_of_balls (γ := γ) (α := c) hγ (z := 0)
    (νX := fun k => areaApproxC γ (X ω) k)
    (νY := fun k => (areaApproxC γ (X ω) k).withDensity
      (fun w => ENNReal.ofReal (AtomlessUncond.logFactorA γ c 0 k w)))
    (K1 := 0) (M1 := 0) (fun _ _ _ _ => rfl) hsum'

/-- **(b3)** from the whole-plane sup-moment bound -/
theorem b3_of_supMoment {γ W : ℝ} (hγ : 0 < γ) (hW : 0 < W) (hM : WPSupMoment γ) :
    ∀ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (X : Ω' → Field)
      (A : ℝ → Ω' → ℝ), IsProbabilityMeasure P' → IsWholePlaneGFF X P' →
      IsConeProcess (coneAlpha γ W) (Qc γ) A P' →
      IndepFun X (fun ω t => A t ω) P' →
      ∀ᵐ ω ∂P', ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ᶠ k in atTop, areaApproxC γ
          (coneField (lateralPartC (X ω)) (fun t => A t ω) (Qc γ)) k
            (Metric.ball 0 δ) ≤ ENNReal.ofReal ε := by
  intro Ω' _ P' X A hP hX hA _
  set α := coneAlpha γ W with hα
  have hαQ : α < Qc γ := by
    rw [hα, coneAlpha]; have : 0 < W / (2 * γ) := by positivity
    linarith
  set η := (Qc γ - α) / 2 with hη
  have hη0 : 0 < η := by rw [hη]; linarith
  have hc : α + η < Qc γ := by rw [hη]; linarith
  filter_upwards [ae_tight_logFactor hγ hM hc hX, ae_radial_R2 hX,
    ae_locallyIntegrable_coneProfile hA, ConeArea3.ae_hasCircleAvgs hX,
    (ConeMeas2.aemeasurable_conePath hA).2, ae_coneShift_le hX hA]
    with ω htight ⟨R, hRc, _, hxR, hRl⟩ hAl hcirc hAc hgrow
  obtain ⟨C, hC⟩ := hgrow R hRc hxR η hη0
  rw [ConeArea3.coneField_eq_add_ofFunC hxR hRl hAl]
  exact tight_add_ofFunC hγ one_pos hcirc (hAl.sub hRl)
    (ConeArea3.continuousOn_coneShift hAc _ hRc) hC htight

/-- **`ConeRefMeas γ W`** for `0 < γ < 2`, `W > 0`, from the whole-plane sup-moment bound -/
theorem coneRefMeas_of_supMoment {γ W : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hW : 0 < W)
    (hM : WPSupMoment γ) : ConeRefMeas γ W :=
  coneRefMeas_of_tight hγ hγ2 (b3_of_supMoment hγ hW hM)

/-- **quantum cones of every weight `W > 0` exist**, given the whole-plane sup-moment bound -/
theorem exists_isQuantumCone_of_supMoment {γ W : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hW : 0 < W)
    (hM : WPSupMoment γ) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (Y : Ω → Field),
      IsProbabilityMeasure P ∧ IsQuantumCone γ W Y P :=
  Cone.exists_isQuantumCone γ hW (coneRefMeas_of_supMoment hγ hγ2 hW hM)

end ConeArea5
end MatedCRTHarmonic.MoTPort
