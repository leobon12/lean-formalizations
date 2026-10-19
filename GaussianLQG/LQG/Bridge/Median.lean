import GaussianLQG.LQG.Bridge.Basic
import LQGMetric.Papers.GM.S1.NoGap
import LQGMetric.LFPP.Measurable

/-!
# Normalization of the canonical γ-LQG metric (blueprint (S5))

Blueprint property (S5) and Proposition `prop:metric-facts` (F4): for a canonical γ-LQG metric `D`
(`GaussianLQG.IsCanonicalLQGMetric`) and a whole-plane GFF `h` normalized by `h_1(0) = 0`, `1` is
a median (in the two-sided sense, `LQGMetric.IsMedian`) of the left–right crossing distance

  `C_γ = inf_{s,t ∈ [0,1]} D_h(is, 1 + it) = LQGMetric.GM.crossFn D_h`

(`IsCanonicalLQGMetric.isMedian_crossFn`, `IsCanonicalLQGMetric.isMedian_iInf`; in terms of
probabilities, `IsCanonicalLQGMetric.half_le_prob_crossFn`). The two expressions of `C_γ` agree
for every nonnegative function (`crossFn_eq_iInf`), and `C_γ` is measurable
(`IsCanonicalLQGMetric.measurable_crossFn`).

Proof: GM.S1.17b (`LQGMetric.GM.gm_S1_17b_of_measurable`, from GM Theorem 1.1 and the Portmanteau
lemma, since `𝔞_ε` is a median of the approximating crossing distances), applied along
`ε_n = 1/(n+1) → 0⁺`, with the measurability of the LFPP crossing distance under the law of the
normalized field (`LQGMetric.LFPP.aemeasurable_lfppCross_normGFFLaw`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set

namespace GaussianLQG

open LQGMetric

/-! ## The crossing distance as an infimum over the two sides -/

lemma I_mul_mem_leftSide {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    Complex.I * (s : ℂ) ∈ leftSide := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [hs.1, hs.2]

lemma one_add_I_mul_mem_rightSide {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    1 + Complex.I * (t : ℂ) ∈ rightSide := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [ht.1, ht.2]

lemma eq_I_mul_of_mem_leftSide {x : ℂ} (hx : x ∈ leftSide) : x = Complex.I * (x.im : ℂ) := by
  apply Complex.ext <;> simp [hx.1]

lemma eq_one_add_I_mul_of_mem_rightSide {x : ℂ} (hx : x ∈ rightSide) :
    x = 1 + Complex.I * (x.im : ℂ) := by
  apply Complex.ext <;> simp [hx.1]

/-- **The two expressions of the crossing distance agree**: for a nonnegative `d`,
`crossFn d = inf_{s,t ∈ [0,1]} d(is, 1 + it)`. -/
theorem crossFn_eq_iInf {d : ℂ × ℂ → ℝ} (hd : ∀ p, 0 ≤ d p) :
    GM.crossFn d = ⨅ s : Icc (0 : ℝ) 1, ⨅ t : Icc (0 : ℝ) 1,
      d (Complex.I * (s : ℂ), 1 + Complex.I * (t : ℂ)) := by
  have hne : Nonempty (Icc (0 : ℝ) 1) := ⟨⟨0, left_mem_Icc.2 zero_le_one⟩⟩
  have hin : ∀ s : Icc (0 : ℝ) 1, BddBelow (range fun t : Icc (0 : ℝ) 1 =>
      d (Complex.I * (s : ℂ), 1 + Complex.I * (t : ℂ))) :=
    fun s => ⟨0, by rintro _ ⟨t, rfl⟩; exact hd _⟩
  have hout : BddBelow (range fun s : Icc (0 : ℝ) 1 =>
      ⨅ t : Icc (0 : ℝ) 1, d (Complex.I * (s : ℂ), 1 + Complex.I * (t : ℂ))) :=
    ⟨0, by rintro _ ⟨s, rfl⟩; exact Real.iInf_nonneg fun t => hd _⟩
  refine le_antisymm (le_ciInf fun s => le_ciInf fun t => ?_) (GM.le_crossFn fun p hp => ?_)
  · exact GM.crossFn_le (GM.bddBelow_crossSet_of_nonneg hd)
      ⟨I_mul_mem_leftSide s.2, one_add_I_mul_mem_rightSide t.2⟩
  · obtain ⟨h1, h2⟩ := hp
    have hs : p.1.im ∈ Icc (0 : ℝ) 1 := ⟨h1.2.1, h1.2.2⟩
    have ht : p.2.im ∈ Icc (0 : ℝ) 1 := ⟨h2.2.1, h2.2.2⟩
    have e : p = (Complex.I * ((⟨p.1.im, hs⟩ : Icc (0 : ℝ) 1) : ℝ),
        1 + Complex.I * ((⟨p.2.im, ht⟩ : Icc (0 : ℝ) 1) : ℝ)) :=
      Prod.ext (eq_I_mul_of_mem_leftSide h1) (eq_one_add_I_mul_of_mem_rightSide h2)
    rw [e]
    exact (ciInf_le hout ⟨p.1.im, hs⟩).trans (ciInf_le (hin _) ⟨p.2.im, ht⟩)

/-! ## (S5) -/

/-- Convergence in probability (local uniform topology) along `ε → 0⁺` passes to sequences
`ε_n → 0⁺`. -/
lemma tendstoInProbLU_comp {Ω ι κ : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ι → Ω → ℂ × ℂ → ℝ} {Y : Ω → ℂ × ℂ → ℝ} {l : Filter ι} {l' : Filter κ} {ε : κ → ι}
    (hX : TendstoInProbLU P X l Y) (hε : Tendsto ε l' l) :
    TendstoInProbLU P (fun n => X (ε n)) l' Y :=
  fun R hR δ hδ => (hX R hR δ hδ).comp hε

lemma tendsto_one_div_add_one_nhdsGT :
    Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[>] 0) :=
  tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
    Eventually.of_forall fun n => by
      show (0 : ℝ) < 1 / ((n : ℝ) + 1)
      positivity⟩

variable {γ : ℝ} {D : DistC → ContMetric}

namespace IsCanonicalLQGMetric

/-- **Blueprint (S5)**: for a canonical γ-LQG metric `D` and a whole-plane GFF `h` normalized by
`h_1(0) = 0`, `1` is a median of the left–right crossing distance `crossFn D_h` of the unit
square. -/
theorem isMedian_crossFn (hD : IsCanonicalLQGMetric γ D) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsNormalizedWPGFF h P) :
    IsMedian (P.map fun ω => GM.crossFn (D (h ω)).1) 1 := by
  have hconv : ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
      (h' : Ω' → DistC), IsGFFPlusBddCont h' P' →
      TendstoInProbLU P'
        (fun (n : ℕ) ω => (aEps (xiGamma γ) (1 / ((n : ℝ) + 1)))⁻¹ •
          lfppDist (xiGamma γ) (1 / ((n : ℝ) + 1)) (h' ω))
        atTop (fun ω => (D (h' ω)).1) := by
    intro Ω' _ P' _ h' hh'
    have hc := tendstoInProbLU_comp (hD.2 P' h' hh') tendsto_one_div_add_one_nhdsGT
    exact hc
  have hpos : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  exact GM.gm_S1_17b_of_measurable (fun ξ ε hε => LFPP.aemeasurable_lfppCross_normGFFLaw ξ ε hε)
    D hD.1.measurable _ hpos hconv P h hh

/-- **Measurability of the crossing distance**: for a measurable field `h`,
`ω ↦ C_γ(ω) = crossFn D_{h(ω)}` is measurable (`d ↦ crossFn d` is continuous on `C(ℂ × ℂ, ℝ)`,
`LQGMetric.GM.continuous_crossFn`). -/
theorem measurable_crossFn (hD : IsCanonicalLQGMetric γ D) {Ω : Type*} [MeasurableSpace Ω]
    {h : Ω → DistC} (hh : Measurable h) : Measurable fun ω => GM.crossFn (D (h ω)).1 :=
  (GM.measurable_crossFn_contMetric.comp hD.1.measurable).comp hh

/-- **Blueprint (S5)**, probability form (blueprint Definition `def:median`):
`P[C_γ ≤ 1] ≥ 1/2` and `P[C_γ ≥ 1] ≥ 1/2`. -/
theorem half_le_prob_crossFn (hD : IsCanonicalLQGMetric γ D) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsNormalizedWPGFF h P) :
    2⁻¹ ≤ P {ω | GM.crossFn (D (h ω)).1 ≤ 1} ∧ 2⁻¹ ≤ P {ω | 1 ≤ GM.crossFn (D (h ω)).1} :=
  (isMedian_map_iff (hD.measurable_crossFn hh.1.measurable).aemeasurable).1
    (hD.isMedian_crossFn hh)

/-- **Blueprint (S5)**, with `C_γ = inf_{s,t ∈ [0,1]} D_h(is, 1 + it)` written as an infimum
over the two sides of the unit square. -/
theorem isMedian_iInf (hD : IsCanonicalLQGMetric γ D) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsNormalizedWPGFF h P) :
    IsMedian (P.map fun ω => ⨅ s : Icc (0 : ℝ) 1, ⨅ t : Icc (0 : ℝ) 1,
      (D (h ω)).1 (Complex.I * (s : ℂ), 1 + Complex.I * (t : ℂ))) 1 := by
  have e : (fun ω => ⨅ s : Icc (0 : ℝ) 1, ⨅ t : Icc (0 : ℝ) 1,
      (D (h ω)).1 (Complex.I * (s : ℂ), 1 + Complex.I * (t : ℂ))) =
      fun ω => GM.crossFn (D (h ω)).1 :=
    funext fun ω => (crossFn_eq_iInf (GM.cm_nonneg (D (h ω)))).symm
  rw [e]
  exact hD.isMedian_crossFn hh

end IsCanonicalLQGMetric

end GaussianLQG
