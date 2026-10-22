import HigherDimLQGMetric.Select.GeodLex

/-!
# Borel scalar-invariant geodesic selector (SF1)

Packet M3a. The partial Borel graph from `GeodLex` has one point above each metric
admitting a constant-speed geodesic. Lusin–Souslin extends it to a measurable
function on metrics, then the measurable subtype embedding extends it to all
continuous two-point functions.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Topology unitInterval

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ}

private abbrev PathSpace' (d : ℕ) := C(unitInterval, Rd d)

local instance : PolishSpace C(Rd d × Rd d, ℝ) :=
  LQGMetric.polishSpace_continuousMap _ _
local instance : PolishSpace (PathSpace' d) :=
  LQGMetric.polishSpace_continuousMap _ _
local instance : Nonempty (PathSpace' d) := ⟨ContinuousMap.const _ 0⟩

/-- Existence of a bounded geodesic expressed as a nonempty fiber. -/
theorem geodExistsSet_iff (D : ContMetric d) (x y : Rd d) (n : ℕ) :
    D ∈ geodExistsSet x y n ↔ ∃ η : PathSpace' d,
      η ∈ geodBoundFiber D x y n := by
  constructor
  · rintro ⟨p, hp, hpD⟩
    obtain ⟨D', η⟩ := p
    change D' = D at hpD
    subst D'
    exact ⟨η, (metricGeodRel_fiber D x y n η).mp hp⟩
  · rintro ⟨η, hη⟩
    exact ⟨(D, η), (metricGeodRel_fiber D x y n η).mpr hη, rfl⟩

theorem geodExistsSet_smul_iff (D : ContMetric d) (x y : Rd d) (n : ℕ)
    (c : ℝ) (hc : 0 < c) :
    (D.smul c hc) ∈ geodExistsSet x y n ↔ D ∈ geodExistsSet x y n := by
  simp only [geodExistsSet_iff, geodBoundFiber_smul D x y n c hc]

theorem metricLexRel_smul_iff (D : ContMetric d) (x y : Rd d) (n : ℕ)
    (η : PathSpace' d) (c : ℝ) (hc : 0 < c) :
    (D.smul c hc, η) ∈ metricLexRel x y n ↔ (D, η) ∈ metricLexRel x y n := by
  change (η ∈ geodBoundFiber (D.smul c hc) x y n ∧
    IsLexMin (geodBoundFiber (D.smul c hc) x y n) geodCoord η) ↔
    (η ∈ geodBoundFiber D x y n ∧ IsLexMin (geodBoundFiber D x y n) geodCoord η)
  rw [geodBoundFiber_smul D x y n c hc]

/-- The canonical partial graph is unchanged by multiplying the metric by a positive scalar. -/
theorem geodMinGraph_smul_iff (D : ContMetric d) (x y : Rd d)
    (η : PathSpace' d) (c : ℝ) (hc : 0 < c) :
    (D.smul c hc, η) ∈ geodMinGraph x y ↔ (D, η) ∈ geodMinGraph x y := by
  constructor
  · rintro ⟨n, hη, hno⟩
    refine ⟨n, (metricLexRel_smul_iff D x y n η c hc).mp hη, ?_⟩
    intro m hm hmem
    exact hno m hm ((geodExistsSet_smul_iff D x y m c hc).mpr hmem)
  · rintro ⟨n, hη, hno⟩
    refine ⟨n, (metricLexRel_smul_iff D x y n η c hc).mpr hη, ?_⟩
    intro m hm hmem
    exact hno m hm ((geodExistsSet_smul_iff D x y m c hc).mp hmem)

theorem isConstSpeedGeod_of_geodMinGraph (D : ContMetric d) (x y : Rd d)
    (η : PathSpace' d) (hη : (D, η) ∈ geodMinGraph x y) :
    IsConstSpeedGeod D x y η := by
  obtain ⟨n, hlex, -⟩ := hη
  have h := hlex.1
  change IsConstSpeedGeodFn D.1 x y η ∧ ∀ t, ‖η t‖ ≤ n at h
  exact h.1

theorem geodMinGraph_partial (x y : Rd d) (D : ContMetric d)
    (η ζ : PathSpace' d) (hη : (D, η) ∈ geodMinGraph x y)
    (hζ : (D, ζ) ∈ geodMinGraph x y) : η = ζ := by
  have hex : ∃ γ, IsConstSpeedGeod D x y γ :=
    ⟨η, isConstSpeedGeod_of_geodMinGraph D x y η hη⟩
  obtain ⟨γ, -, hu⟩ := existsUnique_geodMinGraph x y D hex
  exact (hu η hη).trans (hu ζ hζ).symm

/-- SF1 (MA1 A10): Borel scalar-invariant selector of constant-speed geodesics. -/
theorem exists_measurable_geodSelector (x y : Rd d) :
    ∃ sel : C(Rd d × Rd d, ℝ) → C(unitInterval, Rd d), Measurable sel ∧
      ∀ D : ContMetric d, (∃ η, IsConstSpeedGeod D x y η) →
        IsConstSpeedGeod D x y (sel D.1) ∧
        ∀ c : ℝ, 0 < c → sel (c • D.1) = sel D.1 := by
  obtain ⟨F, hFm, hFG⟩ := LQGMetric.exists_measurable_of_partialGraph'
    (measurableSet_geodMinGraph x y)
    (fun D η ζ hη hζ => geodMinGraph_partial x y D η ζ hη hζ)
  have hM : MeasurableSet {g : C(Rd d × Rd d, ℝ) | IsContinuousMetric g} :=
    measurableSet_isContinuousMetric_select d
  have hEmb : MeasurableEmbedding
      ((↑) : ContMetric d → C(Rd d × Rd d, ℝ)) :=
    MeasurableEmbedding.subtype_coe hM
  obtain ⟨sel, hselm, hselF⟩ := hEmb.exists_measurable_extend hFm
    (fun _ => inferInstance)
  refine ⟨sel, hselm, ?_⟩
  intro D hex
  obtain ⟨η, hη, -⟩ := existsUnique_geodMinGraph x y D hex
  have hselD : sel D.1 = η := by
    have h := congrFun hselF D
    change sel D.1 = F D at h
    rw [h, hFG (D, η) hη]
  constructor
  · rw [hselD]
    exact isConstSpeedGeod_of_geodMinGraph D x y η hη
  · intro c hc
    have hηc : (D.smul c hc, η) ∈ geodMinGraph x y :=
      (geodMinGraph_smul_iff D x y η c hc).mpr hη
    have hselDc : sel (D.smul c hc).1 = η := by
      have h := congrFun hselF (D.smul c hc)
      change sel (D.smul c hc).1 = F (D.smul c hc) at h
      rw [h, hFG (D.smul c hc, η) hηc]
    calc sel (c • D.1) = sel (D.smul c hc).1 := rfl
      _ = η := hselDc
      _ = sel D.1 := hselD.symm

end HigherDimLQGMetric
