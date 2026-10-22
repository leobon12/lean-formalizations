import HigherDimLQGMetric.DGZ.NondegCompare

/-!
# Comparison relations in a joint DGZ weak limit

Closed-set portmanteau transfers the uniform coarse-field comparison estimate to
every joint subsequential law.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP HigherDimLFPP.Perc

variable {d : ℕ}

/-- Nonnegativity of one local coordinate is a closed property of the joint state. -/
def nd_nonnegLocalSet (r : ℝ) (i : nd_DomainIndex d r) (m : ℕ) :
    Set (nd_Joint d r) :=
  {x | ∀ p : nd_domain r i × nd_domain r i, 0 ≤ x.2 (i, m) p}

theorem nd_isClosed_nonnegLocalSet (r : ℝ) (i : nd_DomainIndex d r) (m : ℕ) :
    IsClosed (nd_nonnegLocalSet r i m) := by
  have e : nd_nonnegLocalSet r i m = ⋂ p : nd_domain r i × nd_domain r i,
      {x : nd_Joint d r | 0 ≤ x.2 (i, m) p} := by
    ext x
    simp [nd_nonnegLocalSet]
  rw [e]
  exact isClosed_iInter fun p => isClosed_le continuous_const
    ((continuous_eval_const p).comp ((continuous_apply (i, m)).comp continuous_snd))

theorem nd_jointSample_mem_nonnegLocalSet {κ : Rd d → ℝ} {ξ Q : ℝ}
    (h : DGZHyp d κ ξ Q) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
    (hH : IsDyadicRealization κ P W H) {q : ℝ≥0∞} (hq0 : 0 < q) (hq1 : q < 1)
    (r : ℝ) (n : ℕ) (i : nd_DomainIndex d r) (m : ℕ) (ω : Ω) :
    nd_jointSample P H ξ q r n ω ∈ nd_nonnegLocalSet r i m := by
  intro p
  change 0 ≤ internalMetricC ξ (fun z => H n z ω - H m z ω)
    (nd_domain r i) (aQ P H ξ n q) p
  have hnm : Continuous fun z => H n z ω - H m z ω :=
    ((hH.band n).continuous ω).sub ((hH.band m).continuous ω)
  rw [internalMetricC_apply hnm
    (nd_isOpen_domain r i) (nd_isConnected_domain r i).isPreconnected]
  exact mul_nonneg
    (inv_nonneg.2 (tight_aQ_pos (by have := h.dim; omega : 0 < d)
      hH ξ n hq0 hq1).le)
    (lfppDistOn_nonneg ξ (fun z => H n z ω - H m z ω)
      (nd_domain r i) p.1.1 p.2.1)

theorem nd_ae_nonnegLocalSet_of_tendsto {κ : Rd d → ℝ} {ξ Q : ℝ}
    (h : DGZHyp d κ ξ Q) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
    (hH : IsDyadicRealization κ P W H) {q : ℝ≥0∞} (hq0 : 0 < q) (hq1 : q < 1)
    (r : ℝ) (ns : ℕ → ℕ) {μ : ProbabilityMeasure (nd_Joint d r)}
    (hlim : Tendsto
      (fun k => nd_jointLaw P hH.whiteNoise.isProbabilityMeasure H ξ q r (ns k))
      atTop (𝓝 μ)) (i : nd_DomainIndex d r) (m : ℕ) :
    ∀ᵐ x ∂(μ : Measure (nd_Joint d r)), x ∈ nd_nonnegLocalSet r i m := by
  apply LQGMetric.DFGPS.ae_mem_of_isClosed_of_forall hlim
    (nd_isClosed_nonnegLocalSet r i m)
  intro k
  change (P.map (nd_jointSample P H ξ q r (ns k)))
    (nd_nonnegLocalSet r i m) = 1
  rw [Measure.map_apply (nd_measurable_jointSample hH ξ q r (ns k))
    (nd_isClosed_nonnegLocalSet r i m).measurableSet]
  have heq : (nd_jointSample P H ξ q r (ns k)) ⁻¹' nd_nonnegLocalSet r i m =
      (Set.univ : Set Ω) := by
    ext ω
    simp [nd_jointSample_mem_nonnegLocalSet h hH hq0 hq1 r (ns k) i m ω]
  rw [heq]
  exact @IsProbabilityMeasure.measure_univ Ω _ P hH.whiteNoise.isProbabilityMeasure

/-- Every joint weak limit gives arbitrarily high probability to a finite comparison
constant between its local zero-scale and `m`-scale coordinates. -/
theorem nd_limit_compSet_prob {κ : Rd d → ℝ} {ξ Q : ℝ}
    (h : DGZHyp d κ ξ Q) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
    (hH : IsDyadicRealization κ P W H) {q : ℝ≥0∞} (hq0 : 0 < q) (hq1 : q < 1)
    (r : ℝ) (ns : ℕ → ℕ) {μ : ProbabilityMeasure (nd_Joint d r)}
    (hlim : Tendsto
      (fun k => nd_jointLaw P hH.whiteNoise.isProbabilityMeasure H ξ q r (ns k))
      atTop (𝓝 μ)) (i : nd_DomainIndex d r) (m : ℕ) {θ : ℝ} (hθ : 0 < θ) :
    ∃ R : ℝ, 1 ≤ R ∧
      (1 : ℝ≥0∞) - ENNReal.ofReal θ ≤
        (μ : Measure (nd_Joint d r)) (nd_compSet r i m R) := by
  obtain ⟨R, hR, hbound⟩ := nd_prelimit_compSet_prob h hH hq0 hq1 r i m hθ
  exact ⟨R, hR, LQGMetric.DFGPS.le_measure_of_isClosed hlim
    (nd_isClosed_compSet r i m R) (Filter.Eventually.of_forall fun k => hbound (ns k))⟩

/-- Countable measurable form of the finite random comparison constant. -/
def nd_finiteCompSet (r : ℝ) (i : nd_DomainIndex d r) (m : ℕ) :
    Set (nd_Joint d r) :=
  ⋃ n : ℕ, nd_compSet r i m ((n : ℝ) + 1)

theorem nd_measurableSet_finiteCompSet (r : ℝ) (i : nd_DomainIndex d r) (m : ℕ) :
    MeasurableSet (nd_finiteCompSet r i m) :=
  MeasurableSet.iUnion fun n => (nd_isClosed_compSet r i m ((n : ℝ) + 1)).measurableSet

theorem nd_mem_finiteCompSet_of_compSet (r : ℝ) (i : nd_DomainIndex d r)
    (m : ℕ) {R : ℝ} (_hR : 1 ≤ R) {x : nd_Joint d r}
    (hx : x ∈ nd_compSet r i m R)
    (h0 : x ∈ nd_nonnegLocalSet r i 0)
    (hm : x ∈ nd_nonnegLocalSet r i m) :
    x ∈ nd_finiteCompSet r i m := by
  obtain ⟨n, hn⟩ := exists_nat_gt R
  refine Set.mem_iUnion.2 ⟨n, ?_⟩
  intro p
  obtain ⟨hxm, hx0⟩ := hx p
  have hRn : R ≤ (n : ℝ) + 1 := by linarith
  constructor
  · exact hxm.trans (mul_le_mul_of_nonneg_right hRn (hm p))
  · exact hx0.trans (mul_le_mul_of_nonneg_right hRn (h0 p))

/-- The zero and `m` internal metrics have the same zero sets in a joint weak limit. -/
theorem nd_ae_finiteCompSet_of_tendsto {κ : Rd d → ℝ} {ξ Q : ℝ}
    (h : DGZHyp d κ ξ Q) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
    (hH : IsDyadicRealization κ P W H) {q : ℝ≥0∞} (hq0 : 0 < q) (hq1 : q < 1)
    (r : ℝ) (ns : ℕ → ℕ) {μ : ProbabilityMeasure (nd_Joint d r)}
    (hlim : Tendsto
      (fun k => nd_jointLaw P hH.whiteNoise.isProbabilityMeasure H ξ q r (ns k))
      atTop (𝓝 μ)) (i : nd_DomainIndex d r) (m : ℕ) :
    ∀ᵐ x ∂(μ : Measure (nd_Joint d r)), x ∈ nd_finiteCompSet r i m := by
  let F := nd_finiteCompSet r i m
  have hF : MeasurableSet F := nd_measurableSet_finiteCompSet r i m
  have h0 := nd_ae_nonnegLocalSet_of_tendsto h hH hq0 hq1 r ns hlim i 0
  have hm := nd_ae_nonnegLocalSet_of_tendsto h hH hq0 hq1 r ns hlim i m
  have hfull : (μ : Measure (nd_Joint d r)) F = 1 := by
    apply le_antisymm prob_le_one
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    obtain ⟨R, hR, hbound⟩ := nd_limit_compSet_prob h hH hq0 hq1
      r ns hlim i m (show 0 < (ε : ℝ) by exact_mod_cast hε)
    have hmeasure : (μ : Measure (nd_Joint d r)) (nd_compSet r i m R) ≤
        (μ : Measure (nd_Joint d r)) F := by
      apply measure_mono_ae
      filter_upwards [h0, hm] with x hx0 hxm hx
      exact nd_mem_finiteCompSet_of_compSet r i m hR hx hx0 hxm
    have heps : ENNReal.ofReal (ε : ℝ) = (ε : ℝ≥0∞) := by simp
    rw [heps] at hbound
    exact (tsub_le_iff_right.mp hbound).trans
      (add_le_add hmeasure le_rfl)
  change ∀ᵐ x ∂(μ : Measure (nd_Joint d r)), x ∈ F
  exact (ae_mem_iff_measure_eq hF.nullMeasurableSet).2 (by rw [hfull, measure_univ])

/-- The comparison relation identifies zeros pointwise on a local domain. -/
theorem nd_localZero_iff_of_finiteCompSet (r : ℝ) (i : nd_DomainIndex d r)
    (m : ℕ) {x : nd_Joint d r} (hx : x ∈ nd_finiteCompSet r i m)
    (h0 : x ∈ nd_nonnegLocalSet r i 0)
    (hm : x ∈ nd_nonnegLocalSet r i m)
    (p : nd_domain r i × nd_domain r i) :
    x.2 (i, 0) p = 0 ↔ x.2 (i, m) p = 0 := by
  obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hx
  obtain ⟨h0m, hm0⟩ := hn p
  constructor
  · intro hz
    have : x.2 (i, m) p ≤ 0 := by simpa [hz] using hm0
    exact le_antisymm this (hm p)
  · intro hz
    have : x.2 (i, 0) p ≤ 0 := by simpa [hz] using h0m
    exact le_antisymm this (h0 p)

end HigherDimLQGMetric.DGZ
