import HigherDimLQGMetric.Sec10.Lemma103Det
import HigherDimLQGMetric.CM.Holder
import HigherDimLQGMetric.Frozen.IsSharpWeakExpMetric
import HigherDimLQGMetric.Field.LGFPlusCont
import HigherDimLQGMetric.Field.Measurable

/-!
# [S] Lemma 10.3: full support of the normalized point distance; unique median

Packet S8b (MA4 Details (a) A20, shape `lemma103` of MA4 Details (c) section `Section10`;
blueprint Part A, Lemma `lem:10-3`; source l. 1547–1570).

For a weak metric assignment `D` (in particular a sharp one) and a normalized LGF `h`
(`h₁(0) = 0`), the law of `X = D_h(0, e₁)` charges every interval `(u, v)` with `0 < u < v`
(`lemma103_weak`, and `lemma103` in the exact MA4 shape). Proof (A20): on the a.s. event where
`D_h` is a length metric and Weyl scaling holds for all continuous functions,
`D_{h + t g}(0, e₁) = (e^{ξ t g}·D_h)(0, e₁)`, and the deterministic part
(`Sec10/Lemma103Det.lean`) gives a rational `q` with `D_{h + q g}(0, e₁) ∈ (u, v)`. Since
`h + q g = shiftNorm h (q f)`, countable additivity gives one `q` for which the shifted event has
positive probability, and the Cameron–Martin equivalence `map_shiftNorm_ac` (F4; `2 ≤ d`, ruling M25)
transfers it to `h`.

Consequences (the forms consumed by L10, with the median conventions of the frozen `aEps`:
`P[X ≤ m] ≥ 1/2` and `P[X ≥ m] ≥ 1/2`): for `m₁ < m₂` the two half-line events
`{X ≤ m₁}`, `{m₂ ≤ X}` cannot both have probability `≥ 1/2` (`lemma103_not_halves`); hence two
medians coincide (`lemma103_median_unique`), and the lower median `inf {m : P[X ≤ m] ≥ 1/2}` (the
convention of `aEps`) equals every median (`lemma103_lowerMedian_eq`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁)

variable {d : ℕ}

/-- The point distance `g ↦ D_g(0, e₁)` is measurable for a measurable assignment. -/
theorem s8b_measurable_pointDist {D : DistRd d → ContMetric d} (hD : Measurable D) :
    Measurable fun g : DistRd d => (D g).1 (0, e₁ d) :=
  ((continuous_eval_const (0, e₁ d)).comp continuous_subtype_val).measurable.comp hD

/-- The point distance `E(0, e₁)` is positive. -/
theorem s8b_pointDist_pos (hd : 1 ≤ d) (E : ContMetric d) : 0 < E.1 (0, e₁ d) :=
  E.apply_pos (s8b_zero_ne_e₁ hd)

/-- `IsCMBounded` for the shifts `q f` of the bump. -/
theorem s8b_exists_isCMBounded_smul (hd : 1 ≤ d) (s : ℝ) :
    ∃ C : ℝ, IsCMBounded (⇑(s • s8bBump d)) C := by
  obtain ⟨C, -, hC⟩ := exists_isCMBounded hd s8b_contDiff_bump s8b_hasCompactSupport_bump
  have hcoe : (⇑(s • s8bBump d) : Rd d → ℝ) = fun x => s * s8bBump d x := by
    funext x
    simp only [ContinuousMap.smul_apply, smul_eq_mul]
  exact ⟨|s| * C, by rw [hcoe]; exact hC.mul_const s⟩

/-- **[S] Lemma 10.3 for the weak class** (MA4 A20; blueprint `lem:10-3`: only (I), (III) and
measurability of `D` are used). For a weak assignment `D` with any normalizers and a normalized
LGF `h`, `P[D_h(0, e₁) ∈ (u, v)] > 0` for all `0 < u < v`. The dimension hypothesis `2 ≤ d` is
that of `map_shiftNorm_ac` (ruling M25). -/
theorem lemma103_weak (hd : 2 ≤ d) {ξ : ℝ} (hξ : 0 < ξ) {D : DistRd d → ContMetric d}
    {c : ℝ → ℝ} (hD : IsWeakExpMetric d ξ D c)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P) {u v : ℝ} (hu : 0 < u) (huv : u < v) :
    0 < P {ω | (D (h ω)).1 (0, e₁ d) ∈ Ioo u v} := by
  have hd1 : 1 ≤ d := by omega
  have hLGF : IsLGFPlusCont h P := hh.1.isLGFPlusCont
  -- the shifted events `{D_{h + q g}(0, e₁) ∈ (u, v)}`, `q ∈ ℚ`
  let S : ℚ → Set Ω := fun q =>
    {ω | (D (shiftNorm (h ω) ((q : ℝ) • s8bBump d))).1 (0, e₁ d) ∈ Ioo u v}
  -- on the Weyl event, some rational shift hits `(u, v)`
  have hgood : ∀ᵐ ω ∂P, ∃ q : ℚ, ω ∈ S q := by
    filter_upwards [hD.length P h hLGF, hD.weyl P h hLGF] with ω hlen hweyl
    obtain ⟨q, hq⟩ := s8b_exists_rat_psi_mem hd1 hξ hlen hu huv
    refine ⟨q, ?_⟩
    show (D (shiftNorm (h ω) ((q : ℝ) • s8bBump d))).1 (0, e₁ d) ∈ Ioo u v
    rw [s8b_shiftNorm_eq]
    rwa [s8bPsi, hweyl, ENNReal.toReal_ofReal (ContMetric.nonneg _ _ _)] at hq
  -- countable additivity: one shifted event has positive probability
  obtain ⟨q, hq⟩ : ∃ q : ℚ, P (S q) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hall : ∀ᵐ ω ∂P, ∀ q : ℚ, ω ∉ S q :=
      ae_all_iff.2 fun q => measure_eq_zero_iff_ae_notMem.1 (hcon q)
    obtain ⟨ω, ⟨q, hq⟩, hω⟩ := (hgood.and hall).exists
    exact hω q hq
  -- the Cameron–Martin equivalence transfers it to `h`
  let A : Set (DistRd d) := (fun g => (D g).1 (0, e₁ d)) ⁻¹' Ioo u v
  have hA : MeasurableSet A := s8b_measurable_pointDist hD.measurable measurableSet_Ioo
  obtain ⟨C, hF⟩ := s8b_exists_isCMBounded_smul hd1 (q : ℝ)
  have hmS : Measurable fun ω => shiftNorm (h ω) ((q : ℝ) • s8bBump d) :=
    (measurable_addConst_left _).comp ((measurable_addFun_left _).comp hh.1.measurable)
  have h1 : P.map (fun ω => shiftNorm (h ω) ((q : ℝ) • s8bBump d)) A ≠ 0 := by
    rw [Measure.map_apply hmS hA]
    exact hq
  have h2 : P.map h A ≠ 0 := fun h0 => h1 ((map_shiftNorm_ac hd hh _ hF).1 h0)
  rw [Measure.map_apply hh.1.measurable hA] at h2
  exact pos_iff_ne_zero.2 h2

set_option linter.unusedVariables false in
/-- **[S] Lemma 10.3** (full support of the normalized point distance), exactly the shape
`lemma103` of MA4 Details (c), section `Section10`. The hypothesis `hQ` belongs to that shape and
is not needed by the proof (only `2 ≤ d`, `0 < ξ` and the weak axioms are used). -/
theorem lemma103 (hd : 3 ≤ d) {ξ Q : ℝ} (hξ : 0 < ξ) (hQ : Real.sqrt (2 * d) < Q)
    {D : DistRd d → ContMetric d} (hD : IsSharpWeakExpMetric d ξ Q D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P) {u v : ℝ} (hu : 0 < u) (huv : u < v) :
    0 < P {ω | (D (h ω)).1 (0, e₁ d) ∈ Ioo u v} :=
  lemma103_weak (by omega) hξ hD P h hh hu huv

/-- **Unique median, half-line form** (consumed by L10). For a weak assignment `D` and a normalized
LGF `h`, and `m₁ < m₂`, the events `{D_h(0, e₁) ≤ m₁}` and `{m₂ ≤ D_h(0, e₁)}` cannot both have
probability at least `1/2`. In particular `m₁` and `m₂` are not both medians. -/
theorem lemma103_not_halves (hd : 2 ≤ d) {ξ : ℝ} (hξ : 0 < ξ) {D : DistRd d → ContMetric d}
    {c : ℝ → ℝ} (hD : IsWeakExpMetric d ξ D c)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P) {m₁ m₂ : ℝ} (hm : m₁ < m₂) :
    ¬ ((2 : ℝ≥0∞)⁻¹ ≤ P {ω | (D (h ω)).1 (0, e₁ d) ≤ m₁} ∧
      (2 : ℝ≥0∞)⁻¹ ≤ P {ω | m₂ ≤ (D (h ω)).1 (0, e₁ d)}) := by
  rintro ⟨h₁, h₂⟩
  have hd1 : 1 ≤ d := by omega
  have hX : Measurable fun ω => (D (h ω)).1 (0, e₁ d) :=
    (s8b_measurable_pointDist hD.measurable).comp hh.1.measurable
  -- a median of the positive variable `D_h(0, e₁)` is positive
  have hm₁ : 0 < m₁ := by
    by_contra hneg
    push Not at hneg
    have hempty : {ω | (D (h ω)).1 (0, e₁ d) ≤ m₁} = ∅ :=
      Set.eq_empty_of_forall_notMem fun ω hω =>
        not_le.2 (lt_of_le_of_lt hneg (s8b_pointDist_pos hd1 _)) hω
    rw [hempty, measure_empty] at h₁
    exact absurd h₁ (by simp)
  have hpos := lemma103_weak hd hξ hD P h hh hm₁ hm
  -- the three disjoint events `{X ≤ m₁}`, `{X ∈ (m₁, m₂)}`, `{m₂ ≤ X}`
  set A := {ω | (D (h ω)).1 (0, e₁ d) ≤ m₁} with hA
  set B := {ω | (D (h ω)).1 (0, e₁ d) ∈ Ioo m₁ m₂} with hB
  set C := {ω | m₂ ≤ (D (h ω)).1 (0, e₁ d)} with hC
  have hAB : Disjoint A B :=
    Set.disjoint_left.2 fun ω hωA hωB => not_lt.2 (show _ ≤ m₁ from hωA) hωB.1
  have hABC : Disjoint (A ∪ B) C := by
    refine Set.disjoint_left.2 fun ω hω hωC => ?_
    have hlt : (D (h ω)).1 (0, e₁ d) < m₂ := by
      rcases hω with hωA | hωB
      · exact lt_of_le_of_lt (show _ ≤ m₁ from hωA) hm
      · exact hωB.2
    exact not_le.2 hlt hωC
  have hBm : MeasurableSet B := hX measurableSet_Ioo
  have hCm : MeasurableSet C := hX measurableSet_Ici
  have hsum : P A + P B + P C ≤ 1 := by
    rw [← measure_union hAB hBm, ← measure_union hABC hCm]
    exact prob_le_one
  have hlt : (1 : ℝ≥0∞) < 1 :=
    calc (1 : ℝ≥0∞) < 1 + P B := ENNReal.lt_add_right ENNReal.one_ne_top hpos.ne'
      _ = 2⁻¹ + P B + 2⁻¹ := by rw [add_right_comm, ENNReal.inv_two_add_inv_two]
      _ ≤ P A + P B + P C := add_le_add (add_le_add h₁ le_rfl) h₂
      _ ≤ 1 := hsum
  exact lt_irrefl _ hlt

/-- **Unique median** (consumed by L10): two medians of `D_h(0, e₁)` (with the convention
`P[X ≤ m] ≥ 1/2`, `P[X ≥ m] ≥ 1/2` of the frozen `aEps`) coincide. -/
theorem lemma103_median_unique (hd : 2 ≤ d) {ξ : ℝ} (hξ : 0 < ξ) {D : DistRd d → ContMetric d}
    {c : ℝ → ℝ} (hD : IsWeakExpMetric d ξ D c)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P) {m₁ m₂ : ℝ}
    (hm₁ : (2 : ℝ≥0∞)⁻¹ ≤ P {ω | (D (h ω)).1 (0, e₁ d) ≤ m₁} ∧
      (2 : ℝ≥0∞)⁻¹ ≤ P {ω | m₁ ≤ (D (h ω)).1 (0, e₁ d)})
    (hm₂ : (2 : ℝ≥0∞)⁻¹ ≤ P {ω | (D (h ω)).1 (0, e₁ d) ≤ m₂} ∧
      (2 : ℝ≥0∞)⁻¹ ≤ P {ω | m₂ ≤ (D (h ω)).1 (0, e₁ d)}) :
    m₁ = m₂ := by
  rcases lt_trichotomy m₁ m₂ with hlt | heq | hgt
  · exact absurd ⟨hm₁.1, hm₂.2⟩ (lemma103_not_halves hd hξ hD P h hh hlt)
  · exact heq
  · exact absurd ⟨hm₂.1, hm₁.2⟩ (lemma103_not_halves hd hξ hD P h hh hgt)

/-- **The lower median is the median** (consumed by L10): if `m` is a median of `D_h(0, e₁)`, the
lower median `inf {m' : P[X ≤ m'] ≥ 1/2}` (the convention of the frozen `aEps`) equals `m`. -/
theorem lemma103_lowerMedian_eq (hd : 2 ≤ d) {ξ : ℝ} (hξ : 0 < ξ) {D : DistRd d → ContMetric d}
    {c : ℝ → ℝ} (hD : IsWeakExpMetric d ξ D c)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsNormalizedLGF h P) {m : ℝ}
    (hm : (2 : ℝ≥0∞)⁻¹ ≤ P {ω | (D (h ω)).1 (0, e₁ d) ≤ m} ∧
      (2 : ℝ≥0∞)⁻¹ ≤ P {ω | m ≤ (D (h ω)).1 (0, e₁ d)}) :
    sInf {m' : ℝ | (2 : ℝ≥0∞)⁻¹ ≤ P {ω | (D (h ω)).1 (0, e₁ d) ≤ m'}} = m := by
  refine IsLeast.csInf_eq ⟨hm.1, fun m' hm' => ?_⟩
  by_contra hlt
  push Not at hlt
  exact lemma103_not_halves hd hξ hD P h hh hlt ⟨hm', hm.2⟩

end HigherDimLQGMetric
