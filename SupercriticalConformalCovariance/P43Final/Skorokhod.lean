import SupercriticalConformalCovariance.Small.SkorokhodPathwise
import SupercriticalConformalCovariance.Small.SkorokhodCompact
import SupercriticalConformalCovariance.Small.LawTransfer
import SupercriticalConformalCovariance.Small.ConfinedLawGeometry

/-!
# Proposition 4.3, final step: Skorokhod representation and the pathwise contradiction

Paper l. 361–368: "By Lemma 4.2, on the failure event we may choose witnessing endpoints universally
measurably. Since the rescaled endpoints lie in a fixed compact annulus, their laws are automatically
tight. Apply a Skorokhod subsequence representation to the joint field/metric convergence of Lemma 3.3,
together with these selected endpoint variables on the event of failure. On any represented subsequence
along which failure persists ..., compactness of endpoint positions gives a further subsequence to which
Lemma 4.1 applies. That lemma rules out the failure."

`skorokhod_failure_contradiction` is this step for an arbitrary Polish field coordinate `S₀` and two
`LSCFun` metric coordinates: weak convergence of the joint laws to a limit whose two metric coordinates
coincide and are metrics, a.s. shape/regularity/comparison properties of the finite-index coordinates,
and a uniform positive lower bound on the failure probabilities give a contradiction.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace SupercriticalConformalCovariance.P43Final
open SupercriticalLQGUniqueness
open SupercriticalLQGUniqueness.B2.PfeAxioms (IsMetricLSCFun)
open SupercriticalConformalCovariance.Small (ambientMetricLift)

local instance p43fMeasurableSpaceLSCFun : MeasurableSpace LSCFun := borel LSCFun
local instance p43fBorelSpaceLSCFun : BorelSpace LSCFun := ⟨rfl⟩

/-- The metric shape required of each metric coordinate by the pathwise contradiction: a metric
`LSCFun` whose ambient metric is a length space in which finite-length curves are Euclidean
continuous. -/
def GoodShape (F : LSCFun) : Prop :=
  IsMetricLSCFun F ∧ (ambientMetricLift F).IsLengthSpace ∧
    ∀ (P : ℝ → ℂ) (a b : ℝ), (ambientMetricLift F).IsCurve P a b →
      (ambientMetricLift F).len P a b < ⊤ → ContinuousOn P (Icc a b)

/-- The failure relation of Proposition 4.3 at unit scale on the two ambient metric coordinates. -/
def FailAt (α θ m M η : ℝ) (p : LSCFun × LSCFun) (u v : ℂ) : Prop :=
  SupercriticalConformalCovariance.Regular.SourceFailure (ambientMetricLift p.1) (ambientMetricLift p.2) 0 u v 1 α θ m M
    (1 - α) η

/-- The compact endpoint carrier `B̄₁(0) × B̄₁(0)`. -/
abbrev EndPts : Type := {p : ℂ × ℂ // p ∈ Metric.closedBall (0 : ℂ) 1 ×ˢ Metric.closedBall (0 : ℂ) 1}

theorem isClosed_endPts :
    IsClosed (Metric.closedBall (0 : ℂ) 1 ×ˢ Metric.closedBall (0 : ℂ) 1) :=
  Metric.isClosed_closedBall.prod Metric.isClosed_closedBall

theorem isCompact_endPts :
    IsCompact (Metric.closedBall (0 : ℂ) 1 ×ˢ Metric.closedBall (0 : ℂ) 1) :=
  (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)

instance endPts_compactSpace : CompactSpace EndPts :=
  isCompact_iff_compactSpace.mp isCompact_endPts

instance endPts_polishSpace : PolishSpace EndPts := isClosed_endPts.polishSpace

theorem um_failAt_exists (α θ m M η : ℝ) :
    LQGMetric.UMeasurableSet {p : LSCFun × LSCFun | ∃ u v : ℂ, FailAt α θ m M η p u v} := by
  -- `∃ u v` is the projection of the Borel witness relation with the path included.
  let A : Set ((LSCFun × LSCFun) × ((ℂ × ℂ) × SupercriticalConformalCovariance.Regular.Path)) :=
    {p | SupercriticalConformalCovariance.Regular.FailureWitness 0 1 α θ m M (1 - α) η
      ((ambientMetricLift p.1.1, ambientMetricLift p.1.2), (p.2.2, p.2.1))}
  have hmap : Measurable (fun p : (LSCFun × LSCFun) × ((ℂ × ℂ) × SupercriticalConformalCovariance.Regular.Path) =>
      ((ambientMetricLift p.1.1, ambientMetricLift p.1.2), (p.2.2, p.2.1))) := by
    exact ((SupercriticalConformalCovariance.Small.ambientMetricLift_measurable.comp
      (measurable_fst.comp measurable_fst)).prodMk
      (SupercriticalConformalCovariance.Small.ambientMetricLift_measurable.comp
        (measurable_snd.comp measurable_fst))).prodMk
      ((measurable_snd.comp measurable_snd).prodMk (measurable_fst.comp measurable_snd))
  have hA : MeasurableSet A :=
    (SupercriticalConformalCovariance.Regular.failureWitness_borel 0 1 α θ m M (1 - α) η).preimage hmap
  have h := LQGMetric.UMeasurableSet.setOf_exists hA
  convert h using 1
  ext p
  simp only [A, Set.mem_setOf_eq, FailAt]
  constructor
  · rintro ⟨u, v, huv⟩
    obtain ⟨Q, hQ⟩ := (SupercriticalConformalCovariance.Regular.sourceFailure_iff_witness _ _ 0 u v 1 α θ m M (1 - α) η).mp huv
    exact ⟨((u, v), Q), hQ⟩
  · rintro ⟨⟨⟨u, v⟩, Q⟩, hQ⟩
    exact ⟨u, v, (SupercriticalConformalCovariance.Regular.sourceFailure_iff_witness _ _ 0 u v 1 α θ m M (1 - α) η).mpr
      ⟨Q, hQ⟩⟩

theorem um_failAt_endpoints (α θ m M η : ℝ) :
    LQGMetric.UMeasurableSet {q : (LSCFun × LSCFun) × (ℂ × ℂ) |
      FailAt α θ m M η q.1 q.2.1 q.2.2} :=
  SupercriticalConformalCovariance.Small.um_source_failure_endpoints 0 1 α θ m M (1 - α) η

/-- A positive-measure set meets every conull set. -/
theorem exists_mem_of_pos_of_ae {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {S : Set Ω}
    (hS : 0 < P S) {p : Ω → Prop} (hp : ∀ᵐ ω ∂P, p ω) : ∃ ω ∈ S, p ω := by
  by_contra hcon
  push_neg at hcon
  have hsub : S ⊆ {ω | ¬ p ω} := fun ω hω => hcon ω hω
  have h0 : P {ω | ¬ p ω} = 0 := by
    rw [ae_iff] at hp
    exact hp
  exact (lt_irrefl (0 : ℝ≥0∞)) (hS.trans_le ((measure_mono hsub).trans h0.le))

/-- **The Skorokhod step of Proposition 4.3** (paper l. 361–368). -/
theorem skorokhod_failure_contradiction
    {S₀ : Type} [TopologicalSpace S₀] [PolishSpace S₀] [MeasurableSpace S₀] [BorelSpace S₀]
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → S₀ × (LSCFun × LSCFun)) (hX : ∀ n, Measurable (X n))
    (Xlim : Ω → S₀ × (LSCFun × LSCFun)) (hXlim : Measurable Xlim)
    (hconv : ∀ F : BoundedContinuousFunction (S₀ × (LSCFun × LSCFun)) ℝ,
      Tendsto (fun n => ∫ ω, F (X n ω) ∂P) atTop (𝓝 (∫ ω, F (Xlim ω) ∂P)))
    (hlim : ∀ᵐ ω ∂P, (Xlim ω).2.1 = (Xlim ω).2.2 ∧ IsMetricLSCFun (Xlim ω).2.1)
    (A B : ℕ → Set LSCFun) (hA : ∀ n, LQGMetric.UMeasurableSet (A n))
    (hB : ∀ n, LQGMetric.UMeasurableSet (B n))
    (hAgood : ∀ n F, F ∈ A n → GoodShape F) (hBgood : ∀ n F, F ∈ B n → GoodShape F)
    (hshape : ∀ n, ∀ᵐ ω ∂P, (X n ω).2.1 ∈ A n ∧ (X n ω).2.2 ∈ B n)
    (c : NNReal) (hc : 0 < c)
    (hcomp : ∀ n, ∀ᵐ ω ∂P, ∀ x y : ℂ,
      ambientMetricLift (X n ω).2.1 (x, y) ≤ (c : ℝ≥0∞) * ambientMetricLift (X n ω).2.2 (x, y) ∧
      ambientMetricLift (X n ω).2.2 (x, y) ≤ (c : ℝ≥0∞) * ambientMetricLift (X n ω).2.1 (x, y))
    (α θ m : ℝ) (hα0 : 0 ≤ α) (hα : α < 1) (hθ : 0 < θ) (M : NNReal) (η : ℝ) (hη : 0 < η)
    (ε : ℝ≥0∞) (hε : 0 < ε)
    (hbad : ∀ n, ε ≤ P {ω | ∃ u v : ℂ, FailAt α θ m M η (X n ω).2 u v}) :
    False := by
  classical
  -- universally measurable failure events and Borel flags
  have hFailUM : ∀ n, LQGMetric.UMeasurableSet {ω | ∃ u v : ℂ, FailAt α θ m M η (X n ω).2 u v} :=
    fun n => (um_failAt_exists α θ m M η).preimage (measurable_snd.comp (hX n))
  choose flag hflagm hflag using fun n => SupercriticalConformalCovariance.Small.measurable_bool_flag_of_um P _ (hFailUM n)
  -- selected endpoints (Lemma 4.2 + Jankov–von Neumann)
  choose V hVm hVK hVsel using fun n =>
    SupercriticalConformalCovariance.Small.selected_compact_endpoints_of_ambient_joint P (X n) (hX n) α θ m M η hα.le
  let T : Type := EndPts × Bool
  let mark : ℕ → Ω → T := fun n ω => (⟨V n ω, hVK n ω⟩, flag n ω)
  have hmark : ∀ n, Measurable (mark n) := fun n =>
    ((hVm n).subtype_mk).prodMk (hflagm n)
  -- laws
  let μn : ℕ → ProbabilityMeasure (S₀ × (LSCFun × LSCFun)) := fun n =>
    ⟨P.map (X n), (Measure.isProbabilityMeasure_map_iff (hX n).aemeasurable).2 inferInstance⟩
  let μ : ProbabilityMeasure (S₀ × (LSCFun × LSCFun)) :=
    ⟨P.map Xlim, (Measure.isProbabilityMeasure_map_iff hXlim.aemeasurable).2 inferInstance⟩
  have hμ : Tendsto μn atTop (𝓝 μ) := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro F
    have e : ∀ n, ∫ x, F x ∂(μn n : Measure (S₀ × (LSCFun × LSCFun))) = ∫ ω, F (X n ω) ∂P :=
      fun n => integral_map (hX n).aemeasurable F.continuous.measurable.aestronglyMeasurable
    have e' : ∫ x, F x ∂(μ : Measure (S₀ × (LSCFun × LSCFun))) = ∫ ω, F (Xlim ω) ∂P :=
      integral_map hXlim.aemeasurable F.continuous.measurable.aestronglyMeasurable
    simp only [e, e']
    exact hconv F
  obtain ⟨ψ, hψ, ρ, hρlim, hρmarg, Ω', _, _, Pr, hPr, Y, Ylim, hYm, hYLm, hYlaw, hYLlaw, hYconv⟩ :=
    SupercriticalConformalCovariance.Small.exists_skorokhod_compact_mark_with_tendsto P X hX mark hmark μn μ hμ (fun n => rfl)
  -- the flag survives in the limit with probability at least `ε`
  have hflagLaw : ∀ n, ε ≤ (P.map (fun ω => (X (ψ n) ω, mark (ψ n) ω)))
      {x : (S₀ × (LSCFun × LSCFun)) × T | x.2.2 = true} := by
    intro n
    have hmeas : MeasurableSet {x : (S₀ × (LSCFun × LSCFun)) × T | x.2.2 = true} :=
      (measurableSet_singleton true).preimage (measurable_snd.comp measurable_snd)
    rw [Measure.map_apply ((hX (ψ n)).prodMk (hmark (ψ n))) hmeas]
    refine (hbad (ψ n)).trans (measure_mono_ae ?_)
    filter_upwards [hflag (ψ n)] with ω hω hfail
    exact hω.mpr hfail
  have hρflag : ε ≤ ρ.toMeasure {x : (S₀ × (LSCFun × LSCFun)) × T | x.2.2 = true} :=
    SupercriticalConformalCovariance.Small.lower_bound_limit_flag _ ρ hρlim (fun x => x.2.2)
      (continuous_snd.comp continuous_snd) ε (fun n => hflagLaw n)
  have hPrflag : 0 < Pr {ω' | (Ylim ω').2.2 = true} := by
    have hmeas : MeasurableSet {x : (S₀ × (LSCFun × LSCFun)) × T | x.2.2 = true} :=
      (measurableSet_singleton true).preimage (measurable_snd.comp measurable_snd)
    have : Pr {ω' | (Ylim ω').2.2 = true} =
        ρ.toMeasure {x : (S₀ × (LSCFun × LSCFun)) × T | x.2.2 = true} := by
      rw [← hYLlaw, Measure.map_apply hYLm hmeas]
      rfl
    rw [this]
    exact hε.trans_le hρflag
  -- a.s. properties at each finite index, transferred by the exact finite-index laws
  have hgood : ∀ n, ∀ᵐ ω' ∂Pr,
      (Y n ω').1.2.1 ∈ A (ψ n) ∧ (Y n ω').1.2.2 ∈ B (ψ n) ∧
      (∀ x y : ℂ,
        ambientMetricLift (Y n ω').1.2.1 (x, y) ≤
            (c : ℝ≥0∞) * ambientMetricLift (Y n ω').1.2.2 (x, y) ∧
        ambientMetricLift (Y n ω').1.2.2 (x, y) ≤
            (c : ℝ≥0∞) * ambientMetricLift (Y n ω').1.2.1 (x, y)) ∧
      ((Y n ω').2.2 = true →
        FailAt α θ m M η (Y n ω').1.2 (Y n ω').2.1.1.1 (Y n ω').2.1.1.2) := by
    intro n
    let k := ψ n
    let Z : Set ((S₀ × (LSCFun × LSCFun)) × T) :=
      {x | x.1.2.1 ∈ A k ∧ x.1.2.2 ∈ B k ∧
        (∀ x' y' : ℂ,
          ambientMetricLift x.1.2.1 (x', y') ≤ (c : ℝ≥0∞) * ambientMetricLift x.1.2.2 (x', y') ∧
          ambientMetricLift x.1.2.2 (x', y') ≤ (c : ℝ≥0∞) * ambientMetricLift x.1.2.1 (x', y')) ∧
        (x.2.2 = true → FailAt α θ m M η x.1.2 x.2.1.1.1 x.2.1.1.2)}
    have hp21 : Measurable fun x : (S₀ × (LSCFun × LSCFun)) × T => x.1.2.1 :=
      measurable_fst.comp (measurable_snd.comp measurable_fst)
    have hp22 : Measurable fun x : (S₀ × (LSCFun × LSCFun)) × T => x.1.2.2 :=
      measurable_snd.comp (measurable_snd.comp measurable_fst)
    have hZ : LQGMetric.UMeasurableSet Z := by
      have h1 := (hA k).preimage hp21
      have h2 := (hB k).preimage hp22
      have h3 := (SupercriticalConformalCovariance.Small.um_two_sided_comparison c).preimage
        (measurable_snd.comp measurable_fst :
          Measurable fun x : (S₀ × (LSCFun × LSCFun)) × T => x.1.2)
      have hend : Measurable fun x : (S₀ × (LSCFun × LSCFun)) × T =>
          ((x.1.2), ((x.2.1 : ℂ × ℂ).1, (x.2.1 : ℂ × ℂ).2)) := by
        refine (measurable_snd.comp measurable_fst).prodMk ?_
        have hv : Measurable fun x : (S₀ × (LSCFun × LSCFun)) × T => (x.2.1 : ℂ × ℂ) :=
          measurable_subtype_coe.comp (measurable_fst.comp measurable_snd)
        exact (measurable_fst.comp hv).prodMk (measurable_snd.comp hv)
      have h4 := (um_failAt_endpoints α θ m M η).preimage hend
      have hfl : MeasurableSet {x : (S₀ × (LSCFun × LSCFun)) × T | x.2.2 = true} :=
        (measurableSet_singleton true).preimage (measurable_snd.comp measurable_snd)
      have h4' := (LQGMetric.UMeasurableSet.of_measurableSet hfl.compl).union h4
      convert h1.inter (h2.inter (h3.inter h4')) using 1
      ext x
      simp only [Z, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_union,
        Set.mem_compl_iff]
      constructor
      · rintro ⟨a1, a2, a3, a4⟩
        refine ⟨a1, a2, a3, ?_⟩
        by_cases hx : x.2.2 = true
        · exact Or.inr (a4 hx)
        · exact Or.inl hx
      · rintro ⟨a1, a2, a3, a4⟩
        refine ⟨a1, a2, a3, fun hx => ?_⟩
        rcases a4 with a4 | a4
        · exact absurd hx a4
        · exact a4
    have hP : ∀ᵐ ω ∂P, (X k ω, mark k ω) ∈ Z := by
      filter_upwards [hshape k, hcomp k, hflag k, hVsel k] with ω hs hc' hf hsel
      refine ⟨hs.1, hs.2, hc', fun hfl => ?_⟩
      exact hsel (hf.mp hfl)
    have ht := SupercriticalConformalCovariance.Small.ae_of_equal_law_um P Pr (fun ω => (X k ω, mark k ω)) (Y n)
      ((hX k).prodMk (hmark k)) (hYm n) (hYlaw n).symm Z hZ hP
    exact ht
  have hgoodAll := ae_all_iff.2 hgood
  -- the limit metric coordinates coincide and are metrics
  have hlimPr : ∀ᵐ ω' ∂Pr, (Ylim ω').1.2.1 = (Ylim ω').1.2.2 ∧ IsMetricLSCFun (Ylim ω').1.2.1 := by
    let Z : Set (S₀ × (LSCFun × LSCFun)) := {x | x.2.1 = x.2.2 ∧ IsMetricLSCFun x.2.1}
    have hdiag : MeasurableSet {p : LSCFun × LSCFun | p.1 = p.2} := by
      haveI : SecondCountableTopology LSCFun := by
        letI := TopologicalSpace.metrizableSpaceMetric LSCFun
        infer_instance
      exact (isClosed_diagonal (X := LSCFun)).measurableSet
    have hZ : MeasurableSet Z := by
      refine (hdiag.preimage measurable_snd).inter ?_
      exact SupercriticalLQGUniqueness.B2.PfeAxioms.measurableSet_isMetricLSCFun.preimage
        (measurable_fst.comp measurable_snd)
    have hfst : Measurable fun x : (S₀ × (LSCFun × LSCFun)) × T => x.1 := measurable_fst
    have hZ' : MeasurableSet ((fun x : (S₀ × (LSCFun × LSCFun)) × T => x.1) ⁻¹' Z) :=
      hZ.preimage hfst
    have h0 : (μ : Measure (S₀ × (LSCFun × LSCFun))) Zᶜ = 0 := by
      change (P.map Xlim) Zᶜ = 0
      rw [Measure.map_apply hXlim hZ.compl]
      rw [ae_iff] at hlim
      simpa only [Z, Set.preimage, Set.mem_compl_iff, Set.mem_setOf_eq] using hlim
    have h1 : Pr (Ylim ⁻¹' ((fun x : (S₀ × (LSCFun × LSCFun)) × T => x.1) ⁻¹' Zᶜ)) = 0 := by
      rw [← Measure.map_apply hYLm (hZ.compl.preimage hfst), hYLlaw,
        ← Measure.map_apply hfst hZ.compl, hρmarg]
      exact h0
    rw [ae_iff]
    simpa only [Z, Set.preimage, Set.mem_compl_iff, Set.mem_setOf_eq] using h1
  -- one represented sample on which everything holds and the limiting flag is up
  obtain ⟨ω', hω'flag, hω'⟩ := exists_mem_of_pos_of_ae hPrflag (hgoodAll.and hlimPr)
  obtain ⟨hgω, hlω⟩ := hω'
  simp only [Set.mem_setOf_eq] at hω'flag
  set d : LSCMetric := ambientMetricLift (Ylim ω').1.2.1 with hd
  have hlimD : (Ylim ω').1.2.1 = d.toLSCFun :=
    (SupercriticalConformalCovariance.Small.ambientMetricLift_toLSCFun _ hlω.2).symm
  have hlimE : (Ylim ω').1.2.2 = d.toLSCFun := hlω.1 ▸ hlimD
  have hYt : Tendsto (fun n => Y n ω') atTop (𝓝 (Ylim ω')) := hYconv ω'
  exact SupercriticalConformalCovariance.Small.no_flagged_skorokhod_sample (X := S₀) (T := T)
    (fun n => Y n ω') (Ylim ω') hYt d hlimD hlimE c hc
    (fun n => (hAgood _ _ (hgω n).1).1) (fun n => (hBgood _ _ (hgω n).2.1).1)
    (fun n => (hAgood _ _ (hgω n).1).2.1) (fun n => (hBgood _ _ (hgω n).2.1).2.1)
    (fun n => (hAgood _ _ (hgω n).1).2.2) (fun n => (hBgood _ _ (hgω n).2.1).2.2)
    (fun n => (hgω n).2.2.1)
    (fun t => (t.1 : ℂ × ℂ).1) (fun t => (t.1 : ℂ × ℂ).2) (Metric.closedBall 0 1)
    (isCompact_closedBall _ _) (fun t => ⟨t.1.2.1, t.1.2.2⟩)
    (fun t => t.2) continuous_snd hω'flag α θ m hα hθ M η hη
    (fun n hn => (hgω n).2.2.2 hn)

end SupercriticalConformalCovariance.P43Final
