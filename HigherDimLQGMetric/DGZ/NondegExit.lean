import HigherDimLQGMetric.DGZ.NondegCompactObs

/-!
# First-exit inequalities in joint DGZ weak limits

The prelimit path decomposition was proved in `DGZ/Crossing`. Compact endpoint
sets make the corresponding metric inequalities closed, so portmanteau transfers
them to the joint limit law.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP HigherDimLFPP.Perc

variable {d : ℕ}

theorem nd_isCompact_frontier_domain (r : ℝ) (i : nd_DomainIndex d r) :
    IsCompact (frontier (nd_domain r i)) :=
  Metric.isCompact_of_isClosed_isBounded isClosed_frontier
    ((nd_isBounded_domain r i).closure.subset frontier_subset_closure)

/-- A fixed-point exit inequality, expressed as a closed relation on the joint state. -/
def nd_insideExitSet (r : ℝ) (i : nd_DomainIndex d r)
    (A : Set (nd_domain r i)) (x : nd_domain r i) : Set (nd_Joint d r) :=
  {s | min
      (nd_internalSetInf {x} A (s.2 (i, 0)))
      (nd_setInf (frontier (nd_domain r i)) ((↑) '' A) s.1) ≤
        nd_setInf {x.1} ((↑) '' A) s.1}

theorem nd_isClosed_insideExitSet (r : ℝ) (i : nd_DomainIndex d r)
    {A : Set (nd_domain r i)} (hA : IsCompact A) (x : nd_domain r i) :
    IsClosed (nd_insideExitSet r i A x) := by
  letI : LocallyCompactSpace (nd_domain r i) :=
    (nd_isOpen_domain r i).locallyCompactSpace
  have hA' : IsCompact (((↑) '' A) : Set (Rd d)) := hA.image continuous_subtype_val
  have hlocal : Continuous (fun s : nd_Joint d r =>
      nd_internalSetInf {x} A (s.2 (i, 0))) :=
    (nd_continuous_internalSetInf isCompact_singleton hA).comp
      ((continuous_apply (i, 0)).comp continuous_snd)
  have hfront : Continuous (fun s : nd_Joint d r =>
      nd_setInf (frontier (nd_domain r i)) ((↑) '' A) s.1) :=
    (nd_continuous_setInf (nd_isCompact_frontier_domain r i) hA').comp continuous_fst
  have hpoint : Continuous (fun s : nd_Joint d r =>
      nd_setInf {x.1} ((↑) '' A) s.1) :=
    (nd_continuous_setInf isCompact_singleton hA').comp continuous_fst
  exact isClosed_le (hlocal.min hfront) hpoint

theorem nd_jointSample_mem_insideExitSet_of_zero {κ : Rd d → ℝ} {ξ Q : ℝ}
    (h : DGZHyp d κ ξ Q) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
    (hH : IsDyadicRealization κ P W H) {q : ℝ≥0∞} (hq0 : 0 < q) (hq1 : q < 1)
    (r : ℝ) (n : ℕ) (i : nd_DomainIndex d r)
    (A : Set (nd_domain r i)) (hA : A.Nonempty) (x : nd_domain r i)
    (ω : Ω) (hω : ∀ z, H 0 z ω = 0) :
    nd_jointSample P H ξ q r n ω ∈ nd_insideExitSet r i A x := by
  let U := nd_domain r i
  let A₀ : Set (Rd d) := (↑) '' A
  have hAU : A₀ ⊆ U := by
    rintro z ⟨u, -, rfl⟩
    exact u.2
  have hA₀ : A₀.Nonempty := hA.image _
  have hφ : Continuous fun z => H n z ω := (hH.band n).continuous ω
  have hφ0 : (fun z => H n z ω - H 0 z ω) = (fun z => H n z ω) :=
    funext fun z => by rw [hω z, sub_zero]
  have ha0 : 0 ≤ (aQ P H ξ n q)⁻¹ :=
    inv_nonneg.2 (tight_aQ_pos (by have := h.dim; omega : 0 < d)
      hH ξ n hq0 hq1).le
  have ha : 0 < aQ P H ξ n q :=
    tight_aQ_pos (by have := h.dim; omega : 0 < d) hH ξ n hq0 hq1
  have hexit := lfppMetric_ge_min (ξ := ξ) (φ := fun z => H n z ω)
    (U := U) (A := A₀) (x := x.1) hφ (nd_isOpen_domain r i) hAU hA₀ x.2
  have hscaled := mul_le_mul_of_nonneg_left hexit ha0
  rw [mul_min_of_nonneg _ _ ha0] at hscaled
  change min
      (nd_internalSetInf {x} A
        (internalMetricC ξ (fun z => H n z ω - H 0 z ω) U (aQ P H ξ n q)))
      (nd_setInf (frontier U) A₀
        (normMetricC ξ (fun z => H n z ω) (aQ P H ξ n q))) ≤
      nd_setInf {x.1} A₀
        (normMetricC ξ (fun z => H n z ω) (aQ P H ξ n q))
  rw [hφ0,
    nd_internalSetInf_apply hφ (nd_isOpen_domain r i)
      (nd_isConnected_domain r i).isPreconnected ξ _ {x} A ha0,
    nd_setInf_normMetricC hφ ha ξ (frontier U) A₀,
    nd_setInf_normMetricC hφ ha ξ {x.1} A₀]
  simpa only [Set.image_singleton] using hscaled

theorem nd_jointSample_mem_insideExitSet {κ : Rd d → ℝ} {ξ Q : ℝ}
    (h : DGZHyp d κ ξ Q) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
    (hH : IsDyadicRealization κ P W H) {q : ℝ≥0∞} (hq0 : 0 < q) (hq1 : q < 1)
    (r : ℝ) (n : ℕ) (i : nd_DomainIndex d r)
    (A : Set (nd_domain r i)) (hA : A.Nonempty) (x : nd_domain r i) :
    ∀ᵐ ω ∂P, nd_jointSample P H ξ q r n ω ∈ nd_insideExitSet r i A x := by
  have hzero := ae_forall_eq_zero_of_isBandVersion_self h.kernel hH.whiteNoise one_pos
    ((hH.band 0).congr_band (pow_zero _) rfl)
  filter_upwards [hzero] with ω hω
  exact nd_jointSample_mem_insideExitSet_of_zero h hH hq0 hq1 r n i A hA x ω hω

/-- First-exit decomposition survives every joint weak limit. -/
theorem nd_ae_insideExitSet_of_tendsto {κ : Rd d → ℝ} {ξ Q : ℝ}
    (h : DGZHyp d κ ξ Q) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
    (hH : IsDyadicRealization κ P W H) {q : ℝ≥0∞} (hq0 : 0 < q) (hq1 : q < 1)
    (r : ℝ) (ns : ℕ → ℕ) {μ : ProbabilityMeasure (nd_Joint d r)}
    (hlim : Tendsto
      (fun k => nd_jointLaw P hH.whiteNoise.isProbabilityMeasure H ξ q r (ns k))
      atTop (𝓝 μ)) (i : nd_DomainIndex d r)
    {A : Set (nd_domain r i)} (hA : IsCompact A) (hAne : A.Nonempty)
    (x : nd_domain r i) :
    ∀ᵐ s ∂(μ : Measure (nd_Joint d r)), s ∈ nd_insideExitSet r i A x := by
  apply LQGMetric.DFGPS.ae_mem_of_isClosed_of_forall hlim
    (nd_isClosed_insideExitSet r i hA x)
  intro k
  change (P.map (nd_jointSample P H ξ q r (ns k)))
    (nd_insideExitSet r i A x) = 1
  rw [Measure.map_apply (nd_measurable_jointSample hH ξ q r (ns k))
    (nd_isClosed_insideExitSet r i hA x).measurableSet]
  exact (measure_congr (eventuallyEqSet_univ.2
    (nd_jointSample_mem_insideExitSet h hH hq0 hq1 r (ns k) i A hAne x))).trans
      (@IsProbabilityMeasure.measure_univ Ω _ P hH.whiteNoise.isProbabilityMeasure)

/-- A point outside `U` pays at least the boundary-to-target cost. -/
def nd_outsideExitSet (r : ℝ) (i : nd_DomainIndex d r)
    (A : Set (nd_domain r i)) (x : Rd d) : Set (nd_Joint d r) :=
  {s | nd_setInf (frontier (nd_domain r i)) ((↑) '' A) s.1 ≤
    nd_setInf {x} ((↑) '' A) s.1}

theorem nd_isClosed_outsideExitSet (r : ℝ) (i : nd_DomainIndex d r)
    {A : Set (nd_domain r i)} (hA : IsCompact A) (x : Rd d) :
    IsClosed (nd_outsideExitSet r i A x) := by
  have hA' : IsCompact (((↑) '' A) : Set (Rd d)) := hA.image continuous_subtype_val
  exact isClosed_le
    ((nd_continuous_setInf (nd_isCompact_frontier_domain r i) hA').comp continuous_fst)
    ((nd_continuous_setInf isCompact_singleton hA').comp continuous_fst)

theorem nd_jointSample_mem_outsideExitSet {κ : Rd d → ℝ} {ξ Q : ℝ}
    (h : DGZHyp d κ ξ Q) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
    (hH : IsDyadicRealization κ P W H) {q : ℝ≥0∞} (hq0 : 0 < q) (hq1 : q < 1)
    (r : ℝ) (n : ℕ) (i : nd_DomainIndex d r)
    (A : Set (nd_domain r i)) (hA : A.Nonempty)
    (x : Rd d) (hx : x ∉ nd_domain r i) :
    nd_jointSample P H ξ q r n ⁻¹' nd_outsideExitSet r i A x = Set.univ := by
  ext ω
  simp only [Set.mem_preimage, Set.mem_univ, iff_true]
  let U := nd_domain r i
  let A₀ : Set (Rd d) := (↑) '' A
  have hAU : A₀ ⊆ U := by
    rintro z ⟨u, -, rfl⟩
    exact u.2
  have hA₀ : A₀.Nonempty := hA.image _
  have hφ : Continuous fun z => H n z ω := (hH.band n).continuous ω
  have ha : 0 < aQ P H ξ n q :=
    tight_aQ_pos (by have := h.dim; omega : 0 < d) hH ξ n hq0 hq1
  have hexit := lfppSetDist_frontier_le (ξ := ξ) (φ := fun z => H n z ω)
    (U := U) (A := A₀) (x := x) hφ (nd_isOpen_domain r i) hAU hA₀ hx
  have hscaled := mul_le_mul_of_nonneg_left hexit (inv_nonneg.2 ha.le)
  change nd_setInf (frontier U) A₀
      (normMetricC ξ (fun z => H n z ω) (aQ P H ξ n q)) ≤
    nd_setInf {x} A₀
      (normMetricC ξ (fun z => H n z ω) (aQ P H ξ n q))
  rw [nd_setInf_normMetricC hφ ha ξ (frontier U) A₀,
    nd_setInf_normMetricC hφ ha ξ {x} A₀]
  exact hscaled

theorem nd_ae_outsideExitSet_of_tendsto {κ : Rd d → ℝ} {ξ Q : ℝ}
    (h : DGZHyp d κ ξ Q) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
    (hH : IsDyadicRealization κ P W H) {q : ℝ≥0∞} (hq0 : 0 < q) (hq1 : q < 1)
    (r : ℝ) (ns : ℕ → ℕ) {μ : ProbabilityMeasure (nd_Joint d r)}
    (hlim : Tendsto
      (fun k => nd_jointLaw P hH.whiteNoise.isProbabilityMeasure H ξ q r (ns k))
      atTop (𝓝 μ)) (i : nd_DomainIndex d r)
    {A : Set (nd_domain r i)} (hA : IsCompact A) (hAne : A.Nonempty)
    (x : Rd d) (hx : x ∉ nd_domain r i) :
    ∀ᵐ s ∂(μ : Measure (nd_Joint d r)), s ∈ nd_outsideExitSet r i A x := by
  apply LQGMetric.DFGPS.ae_mem_of_isClosed_of_forall hlim
    (nd_isClosed_outsideExitSet r i hA x)
  intro k
  change (P.map (nd_jointSample P H ξ q r (ns k)))
    (nd_outsideExitSet r i A x) = 1
  rw [Measure.map_apply (nd_measurable_jointSample hH ξ q r (ns k))
    (nd_isClosed_outsideExitSet r i hA x).measurableSet,
    nd_jointSample_mem_outsideExitSet h hH hq0 hq1 r (ns k) i A hAne x hx]
  exact @IsProbabilityMeasure.measure_univ Ω _ P hH.whiteNoise.isProbabilityMeasure

/-- The inside inequality holds simultaneously for every point of a domain. -/
def nd_allInsideExitSet (r : ℝ) (i : nd_DomainIndex d r)
    (A : Set (nd_domain r i)) : Set (nd_Joint d r) :=
  ⋂ x : nd_domain r i, nd_insideExitSet r i A x

theorem nd_isClosed_allInsideExitSet (r : ℝ) (i : nd_DomainIndex d r)
    {A : Set (nd_domain r i)} (hA : IsCompact A) :
    IsClosed (nd_allInsideExitSet r i A) :=
  isClosed_iInter fun x => nd_isClosed_insideExitSet r i hA x

theorem nd_ae_allInsideExitSet_of_tendsto {κ : Rd d → ℝ} {ξ Q : ℝ}
    (h : DGZHyp d κ ξ Q) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
    (hH : IsDyadicRealization κ P W H) {q : ℝ≥0∞} (hq0 : 0 < q) (hq1 : q < 1)
    (r : ℝ) (ns : ℕ → ℕ) {μ : ProbabilityMeasure (nd_Joint d r)}
    (hlim : Tendsto
      (fun k => nd_jointLaw P hH.whiteNoise.isProbabilityMeasure H ξ q r (ns k))
      atTop (𝓝 μ)) (i : nd_DomainIndex d r)
    {A : Set (nd_domain r i)} (hA : IsCompact A) (hAne : A.Nonempty) :
    ∀ᵐ s ∂(μ : Measure (nd_Joint d r)), s ∈ nd_allInsideExitSet r i A := by
  apply LQGMetric.DFGPS.ae_mem_of_isClosed_of_forall hlim
    (nd_isClosed_allInsideExitSet r i hA)
  intro k
  change (P.map (nd_jointSample P H ξ q r (ns k)))
    (nd_allInsideExitSet r i A) = 1
  rw [Measure.map_apply (nd_measurable_jointSample hH ξ q r (ns k))
    (nd_isClosed_allInsideExitSet r i hA).measurableSet]
  have hzero := ae_forall_eq_zero_of_isBandVersion_self h.kernel hH.whiteNoise one_pos
    ((hH.band 0).congr_band (pow_zero _) rfl)
  have hmem : ∀ᵐ ω ∂P,
      nd_jointSample P H ξ q r (ns k) ω ∈ nd_allInsideExitSet r i A := by
    filter_upwards [hzero] with ω hω
    exact Set.mem_iInter.2 fun x =>
      nd_jointSample_mem_insideExitSet_of_zero h hH hq0 hq1 r (ns k) i A hAne x ω hω
  exact (measure_congr (eventuallyEqSet_univ.2 hmem)).trans
    (@IsProbabilityMeasure.measure_univ Ω _ P hH.whiteNoise.isProbabilityMeasure)

/-- The outside inequality holds simultaneously for all points outside a domain. -/
def nd_allOutsideExitSet (r : ℝ) (i : nd_DomainIndex d r)
    (A : Set (nd_domain r i)) : Set (nd_Joint d r) :=
  ⋂ x : {x : Rd d // x ∉ nd_domain r i}, nd_outsideExitSet r i A x.1

theorem nd_isClosed_allOutsideExitSet (r : ℝ) (i : nd_DomainIndex d r)
    {A : Set (nd_domain r i)} (hA : IsCompact A) :
    IsClosed (nd_allOutsideExitSet r i A) :=
  isClosed_iInter fun x => nd_isClosed_outsideExitSet r i hA x.1

theorem nd_ae_allOutsideExitSet_of_tendsto {κ : Rd d → ℝ} {ξ Q : ℝ}
    (h : DGZHyp d κ ξ Q) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
    (hH : IsDyadicRealization κ P W H) {q : ℝ≥0∞} (hq0 : 0 < q) (hq1 : q < 1)
    (r : ℝ) (ns : ℕ → ℕ) {μ : ProbabilityMeasure (nd_Joint d r)}
    (hlim : Tendsto
      (fun k => nd_jointLaw P hH.whiteNoise.isProbabilityMeasure H ξ q r (ns k))
      atTop (𝓝 μ)) (i : nd_DomainIndex d r)
    {A : Set (nd_domain r i)} (hA : IsCompact A) (hAne : A.Nonempty) :
    ∀ᵐ s ∂(μ : Measure (nd_Joint d r)), s ∈ nd_allOutsideExitSet r i A := by
  apply LQGMetric.DFGPS.ae_mem_of_isClosed_of_forall hlim
    (nd_isClosed_allOutsideExitSet r i hA)
  intro k
  change (P.map (nd_jointSample P H ξ q r (ns k)))
    (nd_allOutsideExitSet r i A) = 1
  rw [Measure.map_apply (nd_measurable_jointSample hH ξ q r (ns k))
    (nd_isClosed_allOutsideExitSet r i hA).measurableSet]
  have heq : (nd_jointSample P H ξ q r (ns k)) ⁻¹' nd_allOutsideExitSet r i A =
      (Set.univ : Set Ω) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_univ, iff_true, nd_allOutsideExitSet,
      Set.mem_iInter]
    intro x
    have hx := nd_jointSample_mem_outsideExitSet h hH hq0 hq1 r (ns k) i
      A hAne x.1 x.2
    change ω ∈ (nd_jointSample P H ξ q r (ns k)) ⁻¹' nd_outsideExitSet r i A x.1
    rw [hx]
    trivial
  rw [heq]
  exact @IsProbabilityMeasure.measure_univ Ω _ P hH.whiteNoise.isProbabilityMeasure

end HigherDimLQGMetric.DGZ
