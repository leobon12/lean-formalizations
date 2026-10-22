import HigherDimLQGMetric.DGZ.NondegBounded

/-!
# A positive crossing in the joint weak limit

The distance-to-infinity estimate gives a high-probability lower bound by one
for the normalized crossing at a sufficiently large radius. This is a closed
event and survives weak convergence.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP HigherDimLFPP.Perc

variable {d : ℕ}

def nd_crossGeOneSet (rGrid R r : ℝ) : Set (nd_Joint d rGrid) :=
  {s | 1 ≤ nd_crossPhi 0 R r s.1}

theorem nd_isClosed_crossGeOneSet (rGrid R r : ℝ) :
    IsClosed (nd_crossGeOneSet (d := d) rGrid R r) :=
  isClosed_le continuous_const ((nd_continuous_crossPhi 0 R r).comp continuous_fst)

/-- Every realization has a uniformly high probability of a normalized crossing
of cost at least one, for a large enough outer radius. -/
theorem nd_prelimit_crossGeOne_prob {κ : Rd d → ℝ} {ξ Q : ℝ}
    (h : DGZHyp d κ ξ Q) :
    ∃ q₂ : ℝ≥0∞, 0 < q₂ ∧ q₂ < 1 ∧ ∀ q : ℝ≥0∞, q₂ ≤ q → q < 1 →
      ∀ rGrid r θ : ℝ, 0 < r → 0 < θ → ∃ R : ℝ, r < R ∧
        ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
          (W : WN d → Ω → ℝ) (H : ℕ → Rd d → Ω → ℝ),
          ∀ hH : IsDyadicRealization κ P W H, ∀ n : ℕ,
            (1 : ℝ≥0∞) - ENNReal.ofReal θ ≤
              (nd_jointLaw P hH.whiteNoise.isProbabilityMeasure H ξ q rGrid n :
                Measure (nd_Joint d rGrid)) (nd_crossGeOneSet rGrid R r) := by
  obtain ⟨q₂, hq₂0, hq₂1, htail⟩ := distInf_aq_pert (cor52Shape d κ ξ Q) h
  refine ⟨q₂, hq₂0, hq₂1, ?_⟩
  intro q hq hq1 rGrid r θ hr hθ
  obtain ⟨R, hR, hbad⟩ := htail q hq hq1 r 1 θ hr hθ
  refine ⟨R, hR, ?_⟩
  intro Ω _ P W H hH n
  let F := nd_crossGeOneSet (d := d) rGrid R r
  let X := nd_jointSample P H ξ q rGrid n
  have hX : Measurable X := nd_measurable_jointSample hH ξ q rGrid n
  have hF : MeasurableSet F := (nd_isClosed_crossGeOneSet rGrid R r).measurableSet
  have hG := isBandVersion_zero_self h.kernel hH.whiteNoise one_pos
  have hbad' : P {ω | acrossDist ξ (fun z => H n z ω) 0 R r ≤ aQ P H ξ n q} ≤
      ENNReal.ofReal θ := by
    simpa only [add_zero, one_mul] using
      hbad Ω P W H hH 1 le_rfl (by norm_num : (1 : ℝ) ≤ 2)
        (fun _ _ => (0 : ℝ)) hG n
  have ha : 0 < aQ P H ξ n q :=
    tight_aQ_pos (by have := h.dim; omega : 0 < d) hH ξ n
      (hq₂0.trans_le hq) hq1
  have hsub : (X ⁻¹' F)ᶜ ⊆
      {ω | acrossDist ξ (fun z => H n z ω) 0 R r ≤ aQ P H ξ n q} := by
    intro ω hω
    have hlt : nd_crossPhi 0 R r (X ω).1 < 1 := lt_of_not_ge hω
    change nd_crossPhi 0 R r
      (normMetricC ξ (fun z => H n z ω) (aQ P H ξ n q)) < 1 at hlt
    rw [nd_crossPhi_normMetricC ((hH.band n).continuous ω) ha ξ 0 R r] at hlt
    change acrossDist ξ (fun z => H n z ω) 0 R r ≤ aQ P H ξ n q
    simpa only [mul_one] using ((inv_mul_lt_iff₀ ha).1 hlt).le
  have hcompl : P (X ⁻¹' F)ᶜ ≤ ENNReal.ofReal θ :=
    (measure_mono hsub).trans hbad'
  change (1 : ℝ≥0∞) - ENNReal.ofReal θ ≤ (P.map X) F
  rw [Measure.map_apply hX hF]
  apply tsub_le_iff_right.2
  calc
    1 = P (X ⁻¹' F) + P (X ⁻¹' F)ᶜ :=
      (@prob_add_prob_compl Ω _ P _ hH.whiteNoise.isProbabilityMeasure (hX hF)).symm
    _ ≤ P (X ⁻¹' F) + ENNReal.ofReal θ := add_le_add le_rfl hcompl

/-- Closed-set portmanteau carries the crossing lower bound to any joint limit. -/
theorem nd_limit_crossGeOne_prob {κ : Rd d → ℝ} {ξ Q : ℝ}
    (h : DGZHyp d κ ξ Q) :
    ∃ q₂ : ℝ≥0∞, 0 < q₂ ∧ q₂ < 1 ∧ ∀ q : ℝ≥0∞, q₂ ≤ q → q < 1 →
      ∀ rGrid r θ : ℝ, 0 < r → 0 < θ → ∃ R : ℝ, r < R ∧
        ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
          (W : WN d → Ω → ℝ) (H : ℕ → Rd d → Ω → ℝ),
          ∀ hH : IsDyadicRealization κ P W H, ∀ (ns : ℕ → ℕ)
            (μ : ProbabilityMeasure (nd_Joint d rGrid)),
            Tendsto
              (fun k => nd_jointLaw P hH.whiteNoise.isProbabilityMeasure H ξ q rGrid (ns k))
              atTop (𝓝 μ) →
              (1 : ℝ≥0∞) - ENNReal.ofReal θ ≤
                (μ : Measure (nd_Joint d rGrid)) (nd_crossGeOneSet rGrid R r) := by
  obtain ⟨q₂, hq₂0, hq₂1, hpre⟩ := nd_prelimit_crossGeOne_prob h
  refine ⟨q₂, hq₂0, hq₂1, ?_⟩
  intro q hq hq1 rGrid r θ hr hθ
  obtain ⟨R, hR, hbound⟩ := hpre q hq hq1 rGrid r θ hr hθ
  refine ⟨R, hR, ?_⟩
  intro Ω _ P W H hH ns μ hlim
  exact LQGMetric.DFGPS.le_measure_of_isClosed hlim
    (nd_isClosed_crossGeOneSet rGrid R r)
    (Filter.Eventually.of_forall fun k => hbound Ω P W H hH (ns k))

/-- Every point at zero distance from the inner sphere lies in some bounded box. -/
def nd_boundedZeroEvent (rGrid r : ℝ) : Set (nd_Joint d rGrid) :=
  {s | ∃ R : ℝ, r < R ∧ ∀ x : Rd d, x ∉ HigherDimLFPP.DGZ.obox 0 R →
    0 < nd_setInf {x} (lsph 0 r) s.1}

/-- The closed crossing lower bounds and the global exit barrier imply the
almost sure boundedness statement of DGZ Lemma 6.8. -/
theorem nd_ae_boundedZeroEvent_of_tendsto {κ : Rd d → ℝ} {ξ Q : ℝ}
    (h : DGZHyp d κ ξ Q) :
    ∃ q₂ : ℝ≥0∞, 0 < q₂ ∧ q₂ < 1 ∧ ∀ q : ℝ≥0∞, q₂ ≤ q → q < 1 →
      ∀ rGrid r : ℝ, 0 < r →
        ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω)
          (W : WN d → Ω → ℝ) (H : ℕ → Rd d → Ω → ℝ),
          ∀ hH : IsDyadicRealization κ P W H, ∀ (ns : ℕ → ℕ)
            (μ : ProbabilityMeasure (nd_Joint d rGrid)),
            Tendsto
              (fun k => nd_jointLaw P hH.whiteNoise.isProbabilityMeasure H ξ q rGrid (ns k))
              atTop (𝓝 μ) →
              ∀ᵐ s ∂(μ : Measure (nd_Joint d rGrid)),
                s ∈ nd_boundedZeroEvent rGrid r := by
  obtain ⟨q₂, hq₂0, hq₂1, hcross⟩ := nd_limit_crossGeOne_prob h
  refine ⟨q₂, hq₂0, hq₂1, ?_⟩
  intro q hq hq1 rGrid r hr Ω _ P W H hH ns μ hlim
  rw [ae_iff]
  have hzero : (μ : Measure (nd_Joint d rGrid))
      {s | ¬s ∈ nd_boundedZeroEvent rGrid r} ≤ 0 := by
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    obtain ⟨R, hR, hbound⟩ := hcross q hq hq1 rGrid r (ε : ℝ) hr
      (by exact_mod_cast hε)
    let F := nd_crossGeOneSet (d := d) rGrid R r
    have hF : MeasurableSet F := (nd_isClosed_crossGeOneSet rGrid R r).measurableSet
    have hbarrier := nd_ae_globalOutsideBarrierSet_of_tendsto h hH
      (hq₂0.trans_le hq) hq1 rGrid r hr R hR ns hlim
    have hle : (μ : Measure (nd_Joint d rGrid))
        {s | ¬s ∈ nd_boundedZeroEvent rGrid r} ≤
          (μ : Measure (nd_Joint d rGrid)) Fᶜ := by
      apply measure_mono_ae
      filter_upwards [hbarrier] with s hs hbad hFs
      apply hbad
      refine ⟨R, hR, fun x hx => ?_⟩
      have h1 : 1 ≤ nd_crossPhi 0 R r s.1 := hFs
      have h2 : nd_crossPhi 0 R r s.1 ≤ nd_setInf {x} (lsph 0 r) s.1 := hs x hx
      exact lt_of_lt_of_le one_pos (h1.trans h2)
    have hcomp : (μ : Measure (nd_Joint d rGrid)) Fᶜ ≤ (ε : ℝ≥0∞) := by
      rw [prob_compl_eq_one_sub hF]
      have hsum := (tsub_le_iff_right.mp (hbound Ω P W H hH ns μ hlim))
      apply tsub_le_iff_right.2
      simpa only [F, ENNReal.ofReal_coe_nnreal, add_comm] using hsum
    simpa only [zero_add] using hle.trans hcomp
  exact le_antisymm hzero bot_le

end HigherDimLQGMetric.DGZ
