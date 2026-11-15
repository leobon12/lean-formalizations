import InteractingSLE.Spec.Sec5.Aux61RestartPrepChart

/-!
# Countable clearance localization of the geometric restart event

Packet PROVE-AUX61-R1. At a fixed rational original own time, the full
configuration is covered by measurable pieces with uniform positive tip
height and counterflow clearance. Each piece carries the inherited chart.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology MeasureTheory
open QuantumZipper (H)
open scoped NNReal

namespace InteractingSLE.Sec5.Aux61Restart

open WangWu LawUnique GlueCond CrossCond.Word49

/-- A retained configuration with quantitative rational lower bounds on tip
clearance and tip height. -/
def restartClearancePiece {Ω : Type*} (s r : ℝ≥0) (q : ℚ)
    (Y : Ω → HistorySpace 0 0) (η : Ω → ℝ → ℂ) (U : ℝ≥0 → Ω → ℝ) (n : ℕ) : Set Ω :=
  restartConfigurationEvent s r q Y η U ∩ {ω |
    1 / ((n : ℝ) + 1) ≤ infDist (η ω q) (historyHull s Y ω) ∧
    1 / ((n : ℝ) + 1) ≤ (η ω q).im}

/-- The quantitative pieces are measured from the same retained records. -/
theorem measurableSet_restartClearancePiece
    {Ω : Type*} [MeasurableSpace Ω] {s r : ℝ≥0} {q : ℚ}
    {Y : Ω → HistorySpace 0 0} {η : Ω → ℝ → ℂ} {U : ℝ≥0 → Ω → ℝ}
    (hE : MeasurableSet (restartConfigurationEvent s r q Y η U))
    (hY : Measurable fun ω => cfStop s (Y ω))
    (hm : Measurable fun ω => η ω q) (n : ℕ) :
    MeasurableSet (restartClearancePiece s r q Y η U n) :=
  hE.inter ((measurableSet_le measurable_const (measurable_infDist_historyHull hY hm)).inter
    (measurableSet_le measurable_const (Complex.measurable_im.comp hm)))

/-- Every separated interior configuration has both positive margins at
some rational scale, so the countable cover is exact. -/
theorem restartConfigurationEvent_eq_iUnion_clearancePiece
    {Ω : Type*} {s r : ℝ≥0} {q : ℚ} (hq : 0 < (q : ℝ))
    {Y : Ω → HistorySpace 0 0} {η : Ω → ℝ → ℂ} {U : ℝ≥0 → Ω → ℝ} :
    restartConfigurationEvent s r q Y η U = ⋃ n : ℕ,
      restartClearancePiece s r q Y η U n := by
  ext ω
  rw [mem_iUnion]
  constructor
  · intro hω
    have hclear := hω.1.2.2
    have hheight : 0 < (η ω q).im := hω.1.2.1 ⟨hq, le_rfl⟩
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (lt_min hclear hheight)
    exact ⟨n, hω, hn.le.trans (min_le_left _ _), hn.le.trans (min_le_right _ _)⟩
  · rintro ⟨n, hω⟩
    exact hω.1

/-- A countable measurable clearance cover of the complete geometric
configuration, with the full inherited chart on every piece. This localizes
the geometry at the fixed rational restart; it asserts no field-kernel law. -/
theorem has_countable_charted_clearance_cover
    {Ω : Type*} [MeasurableSpace Ω] {s r : ℝ≥0} {q : ℚ}
    (hrq : (r : ℝ) = q) (hq : 0 < (q : ℝ)) {Y : Ω → HistorySpace 0 0}
    (hY : Measurable fun ω => cfStop s (Y ω))
    {η : Ω → ℝ → ℂ} {U : ℝ≥0 → Ω → ℝ}
    (hUc : ∀ ω, Continuous fun t => U t ω) (hU0 : ∀ ω, U 0 ω = 0)
    (hUm : ∀ t ≤ r, Measurable (U t))
    (hη : ∀ ω, IsLoewnerTrace (Ito.rpath (U · ω)) (η ω))
    (hm : ∀ t ∈ Icc (0 : ℝ) q, Measurable fun ω => η ω t)
    {e : ℕ → ℂ} (he : DenseRange e) :
    (restartConfigurationEvent s r q Y η U = ⋃ n : ℕ,
      restartClearancePiece s r q Y η U n) ∧
    ∀ n : ℕ, MeasurableSet (restartClearancePiece s r q Y η U n) ∧
      HasOriginalTargetRestartChart s r q
        (fun ω : restartClearancePiece s r q Y η U n => Y ω.1)
        (fun ω : restartClearancePiece s r q Y η U n => η ω.1)
        (fun t (ω : restartClearancePiece s r q Y η U n) => U t ω.1) e := by
  have hE := (has_original_target_restart_chart_on_configuration
    hrq hq hY hUc hU0 hUm hη hm he).1
  refine ⟨restartConfigurationEvent_eq_iUnion_clearancePiece hq, fun n => ⟨?_, ?_⟩⟩
  · exact measurableSet_restartClearancePiece hE hY (hm q ⟨hq.le, le_rfl⟩) n
  · exact has_original_target_restart_chart_of_protection hrq hq
      (hY.comp measurable_subtype_coe) (fun ω => hUc ω.1) (fun ω => hU0 ω.1)
      (fun t ht => (hUm t ht).comp measurable_subtype_coe)
      (fun ω => hη ω.1) (fun ω => ω.2.1.1.1) (fun ω => ω.2.1.1.2.1)
      (fun t ht => (hm t ht).comp measurable_subtype_coe)
      (fun ω => ω.2.1.1.2.2) (fun ω => ω.2.1.2.1) (fun ω => ω.2.1.2.2) he

end InteractingSLE.Sec5.Aux61Restart
