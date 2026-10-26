import LQGMetric.Papers.DFGPS.L2_17CoreC
import LQGMetric.Papers.DFGPS.L2_17Core3B
import LQGMetric.Papers.DFGPS.L2_13

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BoundedContinuousFunction
open scoped ENNReal
namespace SupercriticalConformalCovariance.Small

/-- Joint compact-mark subsequence for a convergent Polish coordinate.
The mark can contain selected endpoints and a failure flag. -/
theorem exists_joint_law_subseq_compact_mark
    {Ω S T : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    [TopologicalSpace S] [PolishSpace S] [MeasurableSpace S] [BorelSpace S]
    [TopologicalSpace T] [PolishSpace T] [MeasurableSpace T] [BorelSpace T]
    [CompactSpace T]
    (X : ℕ → Ω → S) (hX : ∀ n, Measurable (X n))
    (V : ℕ → Ω → T) (hV : ∀ n, Measurable (V n))
    (μn : ℕ → ProbabilityMeasure S) (μ : ProbabilityMeasure S)
    (hμ : Tendsto μn atTop (𝓝 μ))
    (hXlaw : ∀ n, P.map (X n) = (μn n : Measure S)) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ ρ : ProbabilityMeasure (S × T),
      Tendsto (β := ProbabilityMeasure (S × T)) (fun n => (⟨P.map (fun ω => (X (ψ n) ω, V (ψ n) ω)),
        (Measure.isProbabilityMeasure_map_iff
          ((hX (ψ n)).prodMk (hV (ψ n))).aemeasurable).2 inferInstance⟩ :
        ProbabilityMeasure (S × T))) atTop (𝓝 ρ) ∧
      (ρ : Measure (S × T)).map Prod.fst = (μ : Measure S) := by
  let law : ℕ → ProbabilityMeasure (S × T) := fun n =>
    ⟨P.map (fun ω => (X n ω, V n ω)),
      (Measure.isProbabilityMeasure_map_iff
        ((hX n).prodMk (hV n)).aemeasurable).2 inferInstance⟩
  have hmarg (n : ℕ) :
      (P.map (fun ω => (X n ω, V n ω))).map Prod.fst =
        (μn n : Measure S) := by
    rw [Measure.map_map measurable_fst ((hX n).prodMk (hV n))]
    simpa only [Function.comp_def] using hXlaw n
  have hcl : closure (range μn) ⊆ insert μ (range μn) :=
    hμ.isCompact_insert_range.isClosed.closure_subset_iff.mpr (subset_insert μ _)
  have hc : IsCompact (closure (range μn)) :=
    hμ.isCompact_insert_range.of_isClosed_subset isClosed_closure hcl
  have hTightS : IsTightMeasureSet
      {((ν : ProbabilityMeasure S) : Measure S) | ν ∈ range μn} :=
    LQGMetric.DFGPS.L213.isTight_of_isCompact_closure hc
  have hTight : IsTightMeasureSet
      {((ν : ProbabilityMeasure (S × T)) : Measure (S × T)) | ν ∈ range law} := by
    refine IsTightMeasureSet.prodMk ?_ IsTightMeasureSet.of_compactSpace
    refine hTightS.subset ?_
    rintro _ ⟨_, ⟨_, ⟨n, rfl⟩, rfl⟩, rfl⟩
    change (P.map (fun ω => (X n ω, V n ω))).map Prod.fst ∈ _
    rw [hmarg n]
    exact ⟨μn n, ⟨n, rfl⟩, rfl⟩
  obtain ⟨ρ, -, ψ, hψ, hlim⟩ :=
    (isCompact_closure_of_isTightMeasureSet hTight).tendsto_subseq
      (x := law) fun n => subset_closure ⟨n, rfl⟩
  refine ⟨ψ, hψ, ρ, hlim, ?_⟩
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun g => ?_
  have key := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hlim)
    (g.compContinuous ⟨Prod.fst, continuous_fst⟩)
  have keyμ := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hμ) g
  have hgm : Measurable fun x => g x := g.continuous.measurable
  have e : ∀ n, ∫ p, (g.compContinuous ⟨Prod.fst, continuous_fst⟩) p
      ∂((law (ψ n) : Measure (S × T))) =
      ∫ x, g x ∂((μn (ψ n) : ProbabilityMeasure S) : Measure S) := fun n => by
    show ∫ p, g p.1 ∂(P.map fun ω => (X (ψ n) ω, V (ψ n) ω)) = _
    rw [← hmarg (ψ n)]
    rw [integral_map measurable_fst.aemeasurable hgm.aestronglyMeasurable]
  simp only [Function.comp_apply, e] at key
  rw [integral_map measurable_fst.aemeasurable hgm.aestronglyMeasurable]
  exact tendsto_nhds_unique key (keyμ.comp hψ.tendsto_atTop)


universe uΩ uS uT
/-- Polish Skorokhod coupling with a compact mark, retaining its entire joint
law and giving pointwise convergence of the field, metrics, endpoints and flag. -/
theorem exists_skorokhod_compact_mark
    {Ω : Type uΩ} {S : Type uS} {T : Type uT}
    [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    [TopologicalSpace S] [PolishSpace S] [MeasurableSpace S] [BorelSpace S]
    [TopologicalSpace T] [PolishSpace T] [MeasurableSpace T] [BorelSpace T]
    [CompactSpace T]
    (X : ℕ → Ω → S) (hX : ∀ n, Measurable (X n))
    (V : ℕ → Ω → T) (hV : ∀ n, Measurable (V n))
    (μn : ℕ → ProbabilityMeasure S) (μ : ProbabilityMeasure S)
    (hμ : Tendsto μn atTop (𝓝 μ))
    (hXlaw : ∀ n, P.map (X n) = (μn n : Measure S)) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ ρ : ProbabilityMeasure (S × T),
      (ρ : Measure (S × T)).map Prod.fst = (μ : Measure S) ∧
      ∃ (Ω' : Type (max uS uT)) (_ : MeasurableSpace Ω') (_ : StandardBorelSpace Ω')
        (Pr : Measure Ω'), IsProbabilityMeasure Pr ∧
        ∃ (Y : ℕ → Ω' → S × T) (Ylim : Ω' → S × T),
          (∀ n, Measurable (Y n)) ∧ Measurable Ylim ∧
          (∀ n, Pr.map (Y n) =
            P.map (fun ω => (X (ψ n) ω, V (ψ n) ω))) ∧
          Pr.map Ylim = (ρ : Measure (S × T)) ∧
          ∀ ω, Tendsto (fun n => Y n ω) atTop (𝓝 (Ylim ω)) := by
  obtain ⟨ψ, hψ, ρ, hlim, hmarg⟩ :=
    exists_joint_law_subseq_compact_mark P X hX V hV μn μ hμ hXlaw
  let μs : ℕ → ProbabilityMeasure (S × T) := fun n =>
    ⟨P.map (fun ω => (X (ψ n) ω, V (ψ n) ω)),
      (Measure.isProbabilityMeasure_map_iff
        ((hX (ψ n)).prodMk (hV (ψ n))).aemeasurable).2 inferInstance⟩
  have hlim' : Tendsto μs atTop (𝓝 ρ) := hlim
  obtain ⟨Ω', _, _, Pr, hPr, Y, Ylim, hY, hYL, hYlaw, hYLlaw, hYconv⟩ :=
    LQGMetric.DFGPS.L217.exists_skorokhod_representation_sb hlim'
  refine ⟨ψ, hψ, ρ, hmarg, Ω', inferInstance, inferInstance,
    Pr, hPr, Y, Ylim, hY, hYL, ?_, hYLlaw, hYconv⟩
  intro n
  exact hYlaw n


/-- The same representation, retaining weak convergence of the full joint
laws for Portmanteau on the Boolean mark. -/
theorem exists_skorokhod_compact_mark_with_tendsto
    {Ω : Type uΩ} {S : Type uS} {T : Type uT}
    [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    [TopologicalSpace S] [PolishSpace S] [MeasurableSpace S] [BorelSpace S]
    [TopologicalSpace T] [PolishSpace T] [MeasurableSpace T] [BorelSpace T]
    [CompactSpace T]
    (X : ℕ → Ω → S) (hX : ∀ n, Measurable (X n))
    (V : ℕ → Ω → T) (hV : ∀ n, Measurable (V n))
    (μn : ℕ → ProbabilityMeasure S) (μ : ProbabilityMeasure S)
    (hμ : Tendsto μn atTop (𝓝 μ))
    (hXlaw : ∀ n, P.map (X n) = (μn n : Measure S)) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ ρ : ProbabilityMeasure (S × T),
      Tendsto (β := ProbabilityMeasure (S × T))
        (fun n => (⟨P.map (fun ω => (X (ψ n) ω, V (ψ n) ω)),
        (Measure.isProbabilityMeasure_map_iff
          ((hX (ψ n)).prodMk (hV (ψ n))).aemeasurable).2 inferInstance⟩ :
        ProbabilityMeasure (S × T))) atTop (𝓝 ρ) ∧
      (ρ : Measure (S × T)).map Prod.fst = (μ : Measure S) ∧
      ∃ (Ω' : Type (max uS uT)) (_ : MeasurableSpace Ω') (_ : StandardBorelSpace Ω')
        (Pr : Measure Ω'), IsProbabilityMeasure Pr ∧
        ∃ (Y : ℕ → Ω' → S × T) (Ylim : Ω' → S × T),
          (∀ n, Measurable (Y n)) ∧ Measurable Ylim ∧
          (∀ n, Pr.map (Y n) =
            P.map (fun ω => (X (ψ n) ω, V (ψ n) ω))) ∧
          Pr.map Ylim = (ρ : Measure (S × T)) ∧
          ∀ ω, Tendsto (fun n => Y n ω) atTop (𝓝 (Ylim ω)) := by
  obtain ⟨ψ, hψ, ρ, hlim, hmarg⟩ :=
    exists_joint_law_subseq_compact_mark P X hX V hV μn μ hμ hXlaw
  let μs : ℕ → ProbabilityMeasure (S × T) := fun n =>
    ⟨P.map (fun ω => (X (ψ n) ω, V (ψ n) ω)),
      (Measure.isProbabilityMeasure_map_iff
        ((hX (ψ n)).prodMk (hV (ψ n))).aemeasurable).2 inferInstance⟩
  obtain ⟨Ω', _, _, Pr, hPr, Y, Ylim, hY, hYL, hYlaw, hYLlaw, hYconv⟩ :=
    LQGMetric.DFGPS.L217.exists_skorokhod_representation_sb
      (show Tendsto μs atTop (𝓝 ρ) from hlim)
  exact ⟨ψ, hψ, ρ, hlim, hmarg, Ω', inferInstance, inferInstance,
    Pr, hPr, Y, Ylim, hY, hYL, hYlaw, hYLlaw, hYconv⟩


/-- A positive lower bound for a continuously marked failure flag survives
weak convergence. This is the positive-probability event needed after the
Skorokhod representation. -/
theorem lower_bound_limit_flag
    {Z : Type*} [TopologicalSpace Z] [PolishSpace Z]
    [MeasurableSpace Z] [BorelSpace Z]
    (μn : ℕ → ProbabilityMeasure Z) (μ : ProbabilityMeasure Z)
    (hμ : Tendsto μn atTop (𝓝 μ))
    (flag : Z → Bool) (hflag : Continuous flag)
    (δ : ℝ≥0∞)
    (hδ : ∀ n, δ ≤ (μn n : Measure Z) {x | flag x = true}) :
    δ ≤ (μ : Measure Z) {x | flag x = true} := by
  have hclosed : IsClosed {x : Z | flag x = true} :=
    isClosed_singleton.preimage hflag
  have hport :=
    ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hμ hclosed
  exact (le_limsup_of_frequently_le (Frequently.of_forall hδ)).trans hport


end SupercriticalConformalCovariance.Small
