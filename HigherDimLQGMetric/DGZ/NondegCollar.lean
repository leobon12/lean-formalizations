import HigherDimLQGMetric.DGZ.NondegExit

/-!
# Collar inequalities in joint DGZ weak limits

The compact level set of a continuous collar function gives a closed relation
between a global boundary distance and an internal distance.
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

/-- A level set inside an indexed domain, written in its subtype. -/
def nd_levelCollar (r : ℝ) (i : nd_DomainIndex d r) (g : Rd d → ℝ)
    (ρ : ℝ) : Set (nd_domain r i) := {z | g z.1 = ρ}

theorem nd_levelCollar_image (r : ℝ) (i : nd_DomainIndex d r)
    (g : Rd d → ℝ) (ρ : ℝ) :
    ((↑) '' nd_levelCollar r i g ρ : Set (Rd d)) =
      {z | z ∈ nd_domain r i ∧ g z = ρ} := by
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u.2, hu⟩
  · rintro ⟨hzU, hzg⟩
    exact ⟨⟨z, hzU⟩, hzg, rfl⟩

theorem nd_isCompact_levelCollar (r : ℝ) (i : nd_DomainIndex d r)
    {g : Rd d → ℝ} (hg : Continuous g) {ρ : ℝ} (hρ : 0 < ρ)
    (hgU : ∀ z, z ∉ nd_domain r i → g z ≤ 0) :
    IsCompact (nd_levelCollar r i g ρ) := by
  have hsub : {z : Rd d | g z = ρ} ⊆ nd_domain r i := by
    intro z hz
    by_contra hzU
    have := hgU z hzU
    change g z = ρ at hz
    linarith
  have hcompact : IsCompact {z : Rd d | g z = ρ} :=
    Metric.isCompact_of_isClosed_isBounded (isClosed_eq hg continuous_const)
      ((nd_isBounded_domain r i).subset hsub)
  apply Subtype.isCompact_iff.2
  rw [nd_levelCollar_image]
  have heq : {z : Rd d | z ∈ nd_domain r i ∧ g z = ρ} = {z | g z = ρ} := by
    ext z
    exact ⟨fun hz => hz.2, fun hz => ⟨hsub hz, hz⟩⟩
  rw [heq]
  exact hcompact

/-- Closed collar relation for a fixed compact outer set `F` and internal target `A`. -/
def nd_collarSet (r : ℝ) (i : nd_DomainIndex d r)
    (g : Rd d → ℝ) (ρ : ℝ) (F : Set (Rd d))
    (A : Set (nd_domain r i)) : Set (nd_Joint d r) :=
  {s | nd_internalSetInf (nd_levelCollar r i g ρ) A (s.2 (i, 0)) ≤
    nd_setInf F ((↑) '' A) s.1}

theorem nd_isClosed_collarSet (r : ℝ) (i : nd_DomainIndex d r)
    {g : Rd d → ℝ} (hg : Continuous g) {ρ : ℝ} (hρ : 0 < ρ)
    (hgU : ∀ z, z ∉ nd_domain r i → g z ≤ 0)
    {F : Set (Rd d)} (hF : IsCompact F)
    {A : Set (nd_domain r i)} (hA : IsCompact A) :
    IsClosed (nd_collarSet r i g ρ F A) := by
  letI : LocallyCompactSpace (nd_domain r i) :=
    (nd_isOpen_domain r i).locallyCompactSpace
  have hA' : IsCompact (((↑) '' A) : Set (Rd d)) := hA.image continuous_subtype_val
  exact isClosed_le
    ((nd_continuous_internalSetInf
      (nd_isCompact_levelCollar r i hg hρ hgU) hA).comp
        ((continuous_apply (i, 0)).comp continuous_snd))
    ((nd_continuous_setInf hF hA').comp continuous_fst)

theorem nd_jointSample_mem_collarSet {κ : Rd d → ℝ} {ξ Q : ℝ}
    (h : DGZHyp d κ ξ Q) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
    (hH : IsDyadicRealization κ P W H) {q : ℝ≥0∞} (hq0 : 0 < q) (hq1 : q < 1)
    (r : ℝ) (n : ℕ) (i : nd_DomainIndex d r)
    {g : Rd d → ℝ} (hg : Continuous g) {ρ : ℝ} (hρ : 0 < ρ)
    (hgU : ∀ z, z ∉ nd_domain r i → g z ≤ 0)
    {F : Set (Rd d)} (hF : F.Nonempty)
    {A : Set (nd_domain r i)} (hA : A.Nonempty)
    (hgF : ∀ z ∈ F, g z ≤ ρ)
    (hgA : ∀ z ∈ ((↑) '' A : Set (Rd d)), ρ ≤ g z) :
    ∀ᵐ ω ∂P, nd_jointSample P H ξ q r n ω ∈ nd_collarSet r i g ρ F A := by
  have hzero := ae_forall_eq_zero_of_isBandVersion_self h.kernel hH.whiteNoise one_pos
    ((hH.band 0).congr_band (pow_zero _) rfl)
  filter_upwards [hzero] with ω hω
  let U := nd_domain r i
  let A₀ : Set (Rd d) := (↑) '' A
  have hA₀ : A₀.Nonempty := hA.image _
  have hφ : Continuous fun z => H n z ω := (hH.band n).continuous ω
  have hφ0 : (fun z => H n z ω - H 0 z ω) = (fun z => H n z ω) :=
    funext fun z => by rw [hω z, sub_zero]
  have ha : 0 < aQ P H ξ n q :=
    tight_aQ_pos (by have := h.dim; omega : 0 < d) hH ξ n hq0 hq1
  have ha0 : 0 ≤ (aQ P H ξ n q)⁻¹ := inv_nonneg.2 ha.le
  have hcollar := lfppSetDist_level_le (ξ := ξ) (φ := fun z => H n z ω)
    (U := U) (F := F) (A := A₀) hφ hg hρ hgU hgF hgA hF hA₀
  have hscaled := mul_le_mul_of_nonneg_left hcollar ha0
  change nd_internalSetInf (nd_levelCollar r i g ρ) A
      (internalMetricC ξ (fun z => H n z ω - H 0 z ω) U (aQ P H ξ n q)) ≤
    nd_setInf F A₀ (normMetricC ξ (fun z => H n z ω) (aQ P H ξ n q))
  rw [hφ0, nd_internalSetInf_apply hφ (nd_isOpen_domain r i)
    (nd_isConnected_domain r i).isPreconnected ξ _ (nd_levelCollar r i g ρ) A ha0,
    nd_setInf_normMetricC hφ ha ξ F A₀, nd_levelCollar_image]
  exact hscaled

theorem nd_ae_collarSet_of_tendsto {κ : Rd d → ℝ} {ξ Q : ℝ}
    (h : DGZHyp d κ ξ Q) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
    (hH : IsDyadicRealization κ P W H) {q : ℝ≥0∞} (hq0 : 0 < q) (hq1 : q < 1)
    (r : ℝ) (ns : ℕ → ℕ) {μ : ProbabilityMeasure (nd_Joint d r)}
    (hlim : Tendsto
      (fun k => nd_jointLaw P hH.whiteNoise.isProbabilityMeasure H ξ q r (ns k))
      atTop (𝓝 μ)) (i : nd_DomainIndex d r)
    {g : Rd d → ℝ} (hg : Continuous g) {ρ : ℝ} (hρ : 0 < ρ)
    (hgU : ∀ z, z ∉ nd_domain r i → g z ≤ 0)
    {F : Set (Rd d)} (hF : IsCompact F) (hFne : F.Nonempty)
    {A : Set (nd_domain r i)} (hA : IsCompact A) (hAne : A.Nonempty)
    (hgF : ∀ z ∈ F, g z ≤ ρ)
    (hgA : ∀ z ∈ ((↑) '' A : Set (Rd d)), ρ ≤ g z) :
    ∀ᵐ s ∂(μ : Measure (nd_Joint d r)), s ∈ nd_collarSet r i g ρ F A := by
  apply LQGMetric.DFGPS.ae_mem_of_isClosed_of_forall hlim
    (nd_isClosed_collarSet r i hg hρ hgU hF hA)
  intro k
  change (P.map (nd_jointSample P H ξ q r (ns k)))
    (nd_collarSet r i g ρ F A) = 1
  rw [Measure.map_apply (nd_measurable_jointSample hH ξ q r (ns k))
    (nd_isClosed_collarSet r i hg hρ hgU hF hA).measurableSet]
  exact (measure_congr (eventuallyEqSet_univ.2
    (nd_jointSample_mem_collarSet h hH hq0 hq1 r (ns k) i hg hρ hgU
      hFne hAne hgF hgA))).trans
      (@IsProbabilityMeasure.measure_univ Ω _ P hH.whiteNoise.isProbabilityMeasure)

end HigherDimLQGMetric.DGZ
