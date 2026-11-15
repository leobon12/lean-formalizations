/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.Prop418Det
import LQGMetric.Prob.CondCopies

/-!
# Wang–Wu Proposition 4.18: gluing a second curve conditionally independently given the field

Packet PROVE-WW-B9. Source: `source/external/WW17LP/wang_wu_lean_preprocessed.pdf` (ruling R31), proof of Proposition
4.18 (text dump L1604–1607, L1649–1653): "Conditionally on `h`, sample a forward line `α` and a reverse line `β`
independently. … Lemma 4.1 makes the oriented forward range a function of `h`. … To compare two forward couplings,
couple each conditionally independently with one reverse coupling given `h`".

This file is the measure-theoretic frame of that argument, for an arbitrary Markov kernel `κ` from the field space
(in the application: the regular conditional law of the reverse line's code given the field, on the space of a reverse
coupling).

* `glueMeasure μ κ X = μ ⊗ₘ (κ ∘ X)` on `Ω × β`: the first coordinate carries every random variable of `Ω`, the second
  a sample from `κ(X)` (LQGMetric's `condCopyMeasure` is the case `κ = condDistrib Y X μ`);
* `condIndepEv_glue_fst`: **`σ(fst) ⟂ σ(snd) | σ(X ∘ fst)`** (event form);
* `glueMeasure_map_snd`: if `κ` is the conditional law of `Y'` given `X'` on another space and `X`, `X'` have the same
  law, then `(X ∘ fst, snd)` has the law of `(X', Y')`;
* **`aeDeterminedBy_of_glue_ae_eq`** (Lemma 4.1 for a glued sample): a variable `D` of `Ω` (standard Borel values) that
  is almost surely a measurable function `L` of the glued sample is almost surely a measurable function of `X`;
* **`isFieldDeterminedHistory_of_glue`**: the killed driving history of an evolution (continuous before its lifetime)
  that is almost surely `L` of a glued sample from a kernel on the field space is field-determined
  (`LP.IsFieldDeterminedHistory`), through the dyadic history (`LawUnique.killedHistory`) and the reconstruction of
  continuous paths from dyadic values (`pathsOfHistory`);
* **`aeDeterminedSigma_comap_arcRange_of_glue`** (range form): a random curve whose hitting code (`hitCode`: which
  rational discs it meets at nonnegative rational times) is almost surely `L` of a glued sample has a field-determined
  range, in the form used by Lemma 4.5 and Propositions 4.19–4.21 (and by the side values of `Prop418Det.lean`);
* `hasFieldDeterminedHistories_four_of_nonneg_of_glue`: Proposition 4.18's determination for every coupling of a
  nonnegative word from one glued identity.

With `Prop418Det.lean` (`hasFieldDeterminedHistories_four_of_nonneg`), Proposition 4.18's determination for every
coupling of a nonnegative word follows once, for one forward coupling and one kernel `κ`, the forward history equals a
measurable function of the glued sample almost surely (the forward/reverse range identity).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.WangWu

open LQGMetric (CondIndepEv AEDeterminedBy)

/-! ### The glued measure -/

section Glue

variable {Ω α β : Type*} {mΩ : MeasurableSpace Ω} [mα : MeasurableSpace α] [mβ : MeasurableSpace β]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → α}

/-- **The glued measure** `μ ⊗ₘ (κ ∘ X)` on `Ω × β`: a sample of `κ(X)`, conditionally independent of `Ω` given `X`. -/
def glueMeasure (μ : Measure Ω) (κ : Kernel α β) (X : Ω → α) (hX : Measurable X) : Measure (Ω × β) :=
  μ ⊗ₘ κ.comap X hX

variable (κ : Kernel α β) [IsMarkovKernel κ]

instance (hX : Measurable X) : IsProbabilityMeasure (glueMeasure μ κ X hX) := by
  unfold glueMeasure; infer_instance

/-- The random variables of `Ω` keep their joint law on the glued space. -/
theorem glueMeasure_fst (hX : Measurable X) : (glueMeasure μ κ X hX).map Prod.fst = μ :=
  Measure.fst_compProd μ _

theorem glueMeasure_apply_prod (hX : Measurable X) {s : Set Ω} {t : Set β} (hs : MeasurableSet s)
    (ht : MeasurableSet t) : glueMeasure μ κ X hX (s ×ˢ t) = ∫⁻ ω in s, κ (X ω) t ∂μ := by
  rw [glueMeasure, Measure.compProd_apply_prod hs ht]
  simp only [Kernel.comap_apply]

theorem setIntegral_glue_fst (hX : Measurable X) {s₀ : Set Ω} (hs₀ : MeasurableSet s₀) {u : Set β}
    (hu : MeasurableSet u) :
    ∫ p in Prod.fst ⁻¹' s₀, (κ (X p.1)).real u ∂(glueMeasure μ κ X hX) =
      (∫⁻ ω in s₀, κ (X ω) u ∂μ).toReal := by
  have hku : Measurable fun x => (κ x).real u := (κ.measurable_coe hu).ennreal_toReal
  have h := setIntegral_map (μ := glueMeasure μ κ X hX) (f := fun ω => (κ (X ω)).real u) hs₀
    (hku.comp hX).aestronglyMeasurable measurable_fst.aemeasurable
  rw [glueMeasure_fst κ hX] at h
  rw [← h]
  exact integral_toReal ((κ.measurable_coe hu).comp hX).aemeasurable
    (Eventually.of_forall fun ω => measure_lt_top _ _)

/-- `P[snd ∈ u | G] = κ(X) u` for every σ-algebra `G` between `σ(X ∘ fst)` and `σ(fst)`. -/
theorem condExp_glue_snd (hX : Measurable X) {G : MeasurableSpace (Ω × β)}
    (hXG : mα.comap (fun p : Ω × β => X p.1) ≤ G) (hG : G ≤ mΩ.comap Prod.fst) {u : Set β}
    (hu : MeasurableSet u) :
    (fun p : Ω × β => (κ (X p.1)).real u) =ᵐ[glueMeasure μ κ X hX]
      (glueMeasure μ κ X hX)⟦Prod.snd ⁻¹' u | G⟧ := by
  set ν := glueMeasure μ κ X hX
  have hG0 : G ≤ (Prod.instMeasurableSpace : MeasurableSpace (Ω × β)) := fun s hs => by
    obtain ⟨s₀, hs₀, rfl⟩ := hG s hs
    exact measurable_fst hs₀
  have hku : Measurable fun x => (κ x).real u := (κ.measurable_coe hu).ennreal_toReal
  have hfm : Measurable[G] fun p : Ω × β => (κ (X p.1)).real u :=
    (hku.comp (comap_measurable (fun p : Ω × β => X p.1))).mono hXG le_rfl
  have hbd : ∀ p : Ω × β, ‖(κ (X p.1)).real u‖ ≤ 1 := fun p => by
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]; exact measureReal_le_one
  have hint : Integrable (fun p : Ω × β => (κ (X p.1)).real u) ν :=
    Integrable.of_bound (hfm.mono hG0 le_rfl).aestronglyMeasurable 1 (Eventually.of_forall hbd)
  refine ae_eq_condExp_of_forall_setIntegral_eq hG0
    ((integrable_const (1 : ℝ)).indicator (measurable_snd hu)) (fun _ _ _ => hint.integrableOn)
    (fun s hs _ => ?_) hfm.aestronglyMeasurable
  obtain ⟨s₀, hs₀, rfl⟩ := hG s hs
  rw [setIntegral_indicator (measurable_snd hu), integral_const, smul_eq_mul, mul_one,
    measureReal_def, Measure.restrict_apply_univ, ← Set.prod_eq,
    glueMeasure_apply_prod κ hX hs₀ hu]
  exact setIntegral_glue_fst κ hX hs₀ hu

/-- **The glued sample is conditionally independent of everything on `Ω` given `X`** (event form):
`σ(fst) ⟂ σ(snd) | σ(X ∘ fst)`. -/
theorem condIndepEv_glue_fst (hX : Measurable X) :
    CondIndepEv (mα.comap (fun p : Ω × β => X p.1)) (mΩ.comap (Prod.fst : Ω × β → Ω))
      (mβ.comap (Prod.snd : Ω × β → β)) (glueMeasure μ κ X hX) := by
  have hXm : Measurable fun p : Ω × β => X p.1 := hX.comp measurable_fst
  have hXf : mα.comap (fun p : Ω × β => X p.1) ≤ mΩ.comap Prod.fst := by
    rw [show (fun p : Ω × β => X p.1) = X ∘ Prod.fst from rfl, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono hX.comap_le
  refine (LQGMetric.condIndepEv_of_condExp_sup_eq hXm.comap_le measurable_snd.comap_le
    measurable_fst.comap_le ?_).symm
  rintro _ ⟨u, hu, rfl⟩
  exact (condExp_glue_snd κ hX le_sup_right (sup_le le_rfl hXf) hu).symm.trans
    (condExp_glue_snd κ hX le_rfl hXf hu)

/-- **The glued sample has the law of the second pair**: if `κ` is the regular conditional law of `Y'` given `X'` on
another probability space and `X`, `X'` have the same law, then `(X ∘ fst, snd)` has the law of `(X', Y')`. -/
theorem glueMeasure_map_snd {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    [StandardBorelSpace β] [Nonempty β] {X' : Ω' → α} {Y' : Ω' → β} (hX : Measurable X)
    (hX' : Measurable X') (hY' : Measurable Y') (hlaw : μ.map X = μ'.map X') :
    (glueMeasure μ (condDistrib Y' X' μ') X hX).map (fun p => (X p.1, p.2)) =
      μ'.map (fun ω => (X' ω, Y' ω)) := by
  set κ' := condDistrib Y' X' μ'
  have hm : Measurable fun p : Ω × β => (X p.1, p.2) := (hX.comp measurable_fst).prodMk measurable_snd
  refine Measure.ext_prod (fun {s t} hs ht => ?_)
  rw [Measure.map_apply hm (hs.prod ht)]
  have h1 : (fun p : Ω × β => (X p.1, p.2)) ⁻¹' (s ×ˢ t) = (X ⁻¹' s) ×ˢ t := by ext; simp
  have hjoint : μ'.map (fun ω => (X' ω, Y' ω)) = μ'.map X' ⊗ₘ κ' :=
    (compProd_map_condDistrib hX'.aemeasurable hY'.aemeasurable).symm
  rw [h1, glueMeasure_apply_prod κ' hX (hX hs) ht, hjoint, Measure.compProd_apply_prod hs ht, ← hlaw,
    setLIntegral_map hs (κ'.measurable_coe ht) hX]

/-- **Lemma 4.1 for a glued sample.** If a random variable `D` of `Ω` with standard Borel values is almost surely a
measurable function `L` of the glued sample, then `D` is almost surely a measurable function of `X`. -/
theorem aeDeterminedBy_of_glue_ae_eq {E : Type*} [mE : MeasurableSpace E] [StandardBorelSpace E] [Nonempty E]
    (hX : Measurable X) {D : Ω → E} (hD : Measurable D) {L : β → E} (hL : Measurable L)
    (heq : ∀ᵐ p ∂(glueMeasure μ κ X hX), D p.1 = L p.2) : AEDeterminedBy D X μ := by
  have hci : CondIndepEv (mα.comap (fun p : Ω × β => X p.1)) (mE.comap (fun p : Ω × β => D p.1))
      (mE.comap (fun p : Ω × β => L p.2)) (glueMeasure μ κ X hX) := by
    refine (condIndepEv_glue_fst κ hX).mono ?_ ?_
    · rw [show (fun p : Ω × β => D p.1) = D ∘ Prod.fst from rfl, ← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono hD.comap_le
    · rw [show (fun p : Ω × β => L p.2) = L ∘ Prod.snd from rfl, ← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono hL.comap_le
  obtain ⟨F, hF, hDF⟩ := LQGMetric.aeDeterminedBy_of_condIndepEv_of_ae_eq (hX.comp measurable_fst)
    (hD.comp measurable_fst) hci heq
  refine ⟨F, hF, ?_⟩
  rw [Filter.EventuallyEq, ← glueMeasure_fst κ hX (μ := μ),
    ae_map_iff measurable_fst.aemeasurable (measurableSet_eq_fun hD (hF.comp hX))]
  exact hDF

end Glue

/-! ### From the dyadic killed history to `LP.IsFieldDeterminedHistory` -/

section History

variable {nL nR : ℕ}

open LawUnique

/-- The paths read from a dyadic killed history: at each time the limit along the dyadic times below it. -/
def pathsOfHistory (y : HistorySpace nL nR) :
    ℝ≥0∞ × (ℝ≥0 → ℝ) × (Fin nL → ℝ≥0 → ℝ) × (Fin nR → ℝ≥0 → ℝ) :=
  (y.1, (fun t => limUnder atTop fun n => (y.2 (lowerDyadic t n)).1),
    (fun i t => limUnder atTop fun n => (y.2 (lowerDyadic t n)).2.1 i),
    fun i t => limUnder atTop fun n => (y.2 (lowerDyadic t n)).2.2 i)

theorem measurable_pathsOfHistory : Measurable (pathsOfHistory (nL := nL) (nR := nR)) := by
  have hlim : ∀ (f : ℕ → HistorySpace nL nR → ℝ), (∀ n, Measurable (f n)) →
      Measurable fun y => limUnder atTop fun n => f n y :=
    fun f hf => (StronglyMeasurable.limUnder fun n => (hf n).stronglyMeasurable).measurable
  have hev : ∀ p : ℕ × ℕ, Measurable fun y : HistorySpace nL nR => y.2 p :=
    fun p => (measurable_pi_apply p).comp measurable_snd
  refine measurable_fst.prodMk ((Measurable.of_eval fun t => hlim _ fun n => ?_).prodMk
    ((Measurable.of_eval fun i => Measurable.of_eval fun t => hlim _ fun n => ?_).prodMk
      (Measurable.of_eval fun i => Measurable.of_eval fun t => hlim _ fun n => ?_)))
  · exact measurable_fst.comp (hev _)
  · exact (measurable_pi_apply i).comp (measurable_fst.comp (measurable_snd.comp (hev _)))
  · exact (measurable_pi_apply i).comp (measurable_snd.comp (measurable_snd.comp (hev _)))

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **A field-determined dyadic history determines the paths**: if the dyadic killed history is almost surely a
measurable function of the field and the driving process is almost surely continuous before its lifetime, the killed
driving history is field-determined. -/
theorem isFieldDeterminedHistory_of_aeDeterminedBy_killedHistory
    (hdet : AEDeterminedBy (killedHistory W VL VR ζ) h P)
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧
      (∀ i, ContinuousOn (fun t => VL i t ω) {t | (t : ℝ≥0∞) < ζ ω}) ∧
      ∀ i, ContinuousOn (fun t => VR i t ω) {t | (t : ℝ≥0∞) < ζ ω}) :
    LP.IsFieldDeterminedHistory P h W VL VR ζ := by
  obtain ⟨G, hG, hK⟩ := hdet
  refine ⟨fun d => pathsOfHistory (G d), measurable_pathsOfHistory.comp hG, ?_⟩
  filter_upwards [hK, hcont] with ω hω hc
  have hζ : (G (h ω)).1 = ζ ω := (congrArg Prod.fst hω).symm
  have hdy : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → ∀ n, (G (h ω)).2 (lowerDyadic t n) =
      (W (dyadicTime (lowerDyadic t n)) ω, (fun i => VL i (dyadicTime (lowerDyadic t n)) ω),
        fun i => VR i (dyadicTime (lowerDyadic t n)) ω) := by
    intro t ht n
    have hlt : (dyadicTime (lowerDyadic t n) : ℝ≥0∞) < ζ ω :=
      lt_of_le_of_lt (ENNReal.coe_le_coe.2 (dyadicTime_lowerDyadic_le t n)) ht
    have e := congrFun (congrArg Prod.snd hω) (lowerDyadic t n)
    simp only [Function.comp_apply, killedHistory, hlt, ↓reduceIte] at e
    exact e.symm
  refine ⟨hζ, fun t ht => ⟨?_, fun i => ?_, fun i => ?_⟩⟩
  · refine Tendsto.limUnder_eq ((tendsto_lowerDyadic_of_continuousOn hc.1 ht).congr fun n => ?_)
    rw [hdy t ht n]
  · refine Tendsto.limUnder_eq ((tendsto_lowerDyadic_of_continuousOn (hc.2.1 i) ht).congr fun n => ?_)
    rw [hdy t ht n]
  · refine Tendsto.limUnder_eq ((tendsto_lowerDyadic_of_continuousOn (hc.2.2 i) ht).congr fun n => ?_)
    rw [hdy t ht n]

/-- **Proposition 4.18's determination step for a glued sample.** For an integrated evolution with a measurable
killed driving and a field `h` on a probability space, if for some Markov kernel `κ` from the field space the dyadic
killed history is almost surely a measurable function `L` of a glued sample of `κ(h)`, then the killed driving history
is field-determined. -/
theorem isFieldDeterminedHistory_of_glue [IsProbabilityMeasure P] {a : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {𝓕 : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}
    (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ) (hX : IsMeasurableKilledDriving W VL VR ζ)
    (hh : Measurable h) {β : Type*} [MeasurableSpace β] (κ : Kernel (LQGMetric.DistOn upperHalfPlaneOpens) β)
    [IsMarkovKernel κ] {L : β → HistorySpace nL nR} (hL : Measurable L)
    (heq : ∀ᵐ p ∂(glueMeasure P κ h hh), killedHistory W VL VR ζ p.1 = L p.2) :
    LP.IsFieldDeterminedHistory P h W VL VR ζ :=
  isFieldDeterminedHistory_of_aeDeterminedBy_killedHistory
    (aeDeterminedBy_of_glue_ae_eq κ hh (measurable_killedHistory hX) hL heq)
    (IsIntegratedSLEEvolution.ae_continuousOn_driving hE)

end History

/-! ### The range form: a field-determined hitting σ-algebra from a glued sample -/

section RangeForm

/-- The rational discs `B(a + b i, r)`, `a, b, r ∈ ℚ`. -/
def ratBall (i : ℚ × ℚ × ℚ) : Set ℂ := Metric.ball ((i.1 : ℂ) + (i.2.1 : ℂ) * Complex.I) (i.2.2 : ℝ)

/-- Every point of an open set lies in a rational disc inside it. -/
theorem exists_ratBall_subset {U : Set ℂ} (hU : IsOpen U) {z : ℂ} (hz : z ∈ U) :
    ∃ i, z ∈ ratBall i ∧ ratBall i ⊆ U := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU z hz
  obtain ⟨a, ha⟩ := exists_rat_btwn (show z.re - ε / 4 < z.re by linarith)
  obtain ⟨b, hb⟩ := exists_rat_btwn (show z.im - ε / 4 < z.im by linarith)
  set c : ℂ := (a : ℂ) + (b : ℂ) * Complex.I with hc
  have hcz : dist c z < ε / 2 := by
    rw [dist_eq_norm]
    refine lt_of_le_of_lt (Complex.norm_le_abs_re_add_abs_im _) ?_
    have hre : (c - z).re = (a : ℝ) - z.re := by simp [hc]
    have him : (c - z).im = (b : ℝ) - z.im := by simp [hc]
    rw [hre, him, abs_of_neg (by linarith [ha.2]), abs_of_neg (by linarith [hb.2])]
    linarith [ha.1, hb.1]
  obtain ⟨r, hr⟩ := exists_rat_btwn hcz
  refine ⟨(a, b, r), ?_, fun w hw => hball ?_⟩
  · rw [ratBall, Metric.mem_ball, dist_comm]
    exact hr.1
  · rw [ratBall, Metric.mem_ball] at hw
    rw [Metric.mem_ball]
    calc dist w z ≤ dist w c + dist c z := dist_triangle _ _ _
      _ < r + ε / 2 := add_lt_add hw hcz
      _ < ε / 2 + ε / 2 := by linarith [hr.2]
      _ = ε := by ring

open scoped Classical in
/-- **The hitting code of a curve**: for each rational disc, `1` if the curve meets it at a nonnegative rational time
and `0` otherwise. -/
def hitCode (γ : ℝ → ℂ) (i : ℚ × ℚ × ℚ) : ℝ :=
  if ∃ q : ℚ, 0 ≤ (q : ℝ) ∧ γ q ∈ ratBall i then 1 else 0

theorem measurable_hitCode : Measurable (hitCode : (ℝ → ℂ) → ℚ × ℚ × ℚ → ℝ) := by
  classical
  refine measurable_pi_iff.2 fun i => Measurable.ite ?_ measurable_const measurable_const
  have e : {γ : ℝ → ℂ | ∃ q : ℚ, 0 ≤ (q : ℝ) ∧ γ q ∈ ratBall i} =
      ⋃ q : ℚ, {γ : ℝ → ℂ | 0 ≤ (q : ℝ) ∧ γ q ∈ ratBall i} := by
    ext γ; simp only [mem_ofPred_eq, mem_iUnion]
  rw [e]
  refine MeasurableSet.iUnion fun q => ?_
  by_cases hq : (0 : ℝ) ≤ q
  · simp only [hq, true_and]
    exact (measurable_pi_apply (q : ℝ)) Metric.isOpen_ball.measurableSet
  · simp only [hq, false_and, ofPred_false, MeasurableSet.empty]

/-- For a curve continuous on `[0, ∞)`, the range meets an open set `U` iff the hitting code is `1` at some rational
disc inside `U`. -/
theorem arcRange_inter_nonempty_iff_hitCode {γ : ℝ → ℂ} (hγ : ContinuousOn γ (Ici 0)) {U : Set ℂ}
    (hU : IsOpen U) : (arcRange γ ∩ U).Nonempty ↔ ∃ i, ratBall i ⊆ U ∧ hitCode γ i = 1 := by
  classical
  constructor
  · rintro ⟨_, ⟨s, hs, rfl⟩, hsU⟩
    obtain ⟨i, hzi, hiU⟩ := exists_ratBall_subset hU hsU
    obtain ⟨q, hq0, -, hqi⟩ := exists_rat_mem_of_continuousOn hγ Metric.isOpen_ball (t := s + 1)
      ⟨mem_Ici.1 hs, by linarith⟩ (by linarith) hzi
    refine ⟨i, hiU, ?_⟩
    rw [hitCode]
    split_ifs with hex
    · rfl
    · exact absurd ⟨q, hq0, hqi⟩ hex
  · rintro ⟨i, hiU, hi⟩
    rw [hitCode] at hi
    split_ifs at hi with hex
    · obtain ⟨q, hq0, hqi⟩ := hex
      exact ⟨_, ⟨q, mem_Ici.2 hq0, rfl⟩, hiU hqi⟩
    · norm_num at hi

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

/-- **Proposition 4.18, range form, from a glued sample.** If a random curve (continuous on `[0, ∞)` for every `ω`,
measurable at each time) has a hitting code that is almost surely a measurable function `L` of a glued sample of
`κ(h)`, then the hitting σ-algebra of its range is almost surely determined by the field. This is the form of
"determined by the field" used by Lemma 4.5 (`Adapted.isLocalSet_union_of_aeDetermined`), by the side values
(`IsFullLevelLineCoupling.ae_hasSideLimits_seedLine_of_range`) and by Propositions 4.19–4.21. -/
theorem aeDeterminedSigma_comap_arcRange_of_glue {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}
    (hh : Measurable h) {γ : Ω → ℝ → ℂ} (hc : ∀ ω, ContinuousOn (γ ω) (Ici 0))
    (hm : ∀ s, Measurable fun ω => γ ω s) {β : Type*} [MeasurableSpace β]
    (κ : Kernel (LQGMetric.DistOn upperHalfPlaneOpens) β) [IsMarkovKernel κ]
    {L : β → ℚ × ℚ × ℚ → ℝ} (hL : Measurable L)
    (heq : ∀ᵐ p ∂(glueMeasure P κ h hh), hitCode (γ p.1) = L p.2) :
    LQGMetric.AEDeterminedSigma (MeasurableSpace.comap (fun ω => arcRange (γ ω)) hittingSigma)
      (MeasurableSpace.comap h inferInstance) P := by
  have hD : Measurable fun ω => hitCode (γ ω) := measurable_hitCode.comp (measurable_pi_iff.2 hm)
  obtain ⟨F, hF, hDF⟩ := aeDeterminedBy_of_glue_ae_eq κ hh hD hL heq
  refine aeDeterminedSigma_comap_hitting fun U hU _ => ?_
  refine ⟨h ⁻¹' ⋃ i : ℚ × ℚ × ℚ, {f | ratBall i ⊆ U ∧ F f i = 1}, ⟨_, ?_, rfl⟩, ?_⟩
  · refine MeasurableSet.iUnion fun i => ?_
    by_cases hi : ratBall i ⊆ U
    · simp only [hi, true_and]
      exact (measurable_pi_apply i).comp hF (measurableSet_singleton 1)
    · simp only [hi, false_and, ofPred_false, MeasurableSet.empty]
  · filter_upwards [hDF] with ω hω
    simp only [eq_iff_iff, mem_preimage, mem_ofPred_eq, mem_iUnion]
    rw [arcRange_inter_nonempty_iff_hitCode (hc ω) hU, hω]
    rfl

end RangeForm

/-! ### Proposition 4.18, determination, from one glued identity -/

section Reduction

universe u v

variable {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

open LawUnique

/-- **Proposition 4.18, determination, reduced to one glued identity.** For an ordered word with nonnegative cumulative
weights at `κ = 4`, suppose that for one coupling with the frozen optional hull specification (on a space of universe
`v`) and one Markov kernel `κ` from the field space (in Wang–Wu's proof: the conditional law of a reverse line given the
field), the dyadic killed history of the forward line is almost surely a measurable function `L` of the glued sample
of `κ(h)`. Then every coupling of the word with the frozen optional hull specification has a field-determined killed
history (and so has every full level-line coupling, `hasDeterminedFullCouplings_of_nonneg`). -/
theorem hasFieldDeterminedHistories_four_of_nonneg_of_glue (hxF : IsOrderedForceWord xL xR)
    (hcum : HasNonnegCumWeights ρL ρR)
    (hglue : ∃ (Ω : Type v) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
      (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens)
      (hC : IsOptionalHullCoupling 4 xL xR ρL ρR P 𝓕 W VL VR B ζ h)
      (β : Type v) (_ : MeasurableSpace β) (κ : Kernel (LQGMetric.DistOn upperHalfPlaneOpens) β)
      (_ : IsMarkovKernel κ) (L : β → HistorySpace nL nR),
      Measurable L ∧ ∀ᵐ p ∂(glueMeasure P κ h hC.2.1), killedHistory W VL VR ζ p.1 = L p.2) :
    LP.HasFieldDeterminedHistories.{u} 4 xL xR ρL ρR := by
  obtain ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, h, hC, β, mβ, κ, hκ, L, hL, heq⟩ := hglue
  obtain ⟨hX, -⟩ := hC.2.2.2
  exact hasFieldDeterminedHistories_four_of_nonneg.{u, v} hxF hcum
    ⟨Ω, mΩ, P, hP, 𝓕, W, VL, VR, B, ζ, h, hC, isFieldDeterminedHistory_of_glue hC.1 hX hC.2.1 κ hL heq⟩

end Reduction

end InteractingSLE.WangWu
