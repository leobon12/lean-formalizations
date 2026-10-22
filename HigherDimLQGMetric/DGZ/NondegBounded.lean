import HigherDimLQGMetric.DGZ.NondegCollar

/-!
# Bounded zero sets from distance-to-infinity bounds

The global first-exit barrier is closed under weak convergence. A positive shell
crossing then confines every point at zero distance from the inner sphere.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (cbox obox)

variable {d : ℕ}

theorem nd_frontier_obox_subset_lsph (R : ℝ) :
    frontier (obox (0 : Rd d) R) ⊆ lsph 0 R := by
  intro z hz
  rw [(HigherDimLFPP.DGZ.isOpen_obox 0 R).frontier_eq] at hz
  exact ⟨(closure_minimal (HigherDimLFPP.DGZ.obox_subset_cbox 0 R)
    (HigherDimLFPP.DGZ.isClosed_cbox 0 R)) hz.1, hz.2⟩

theorem nd_frontier_obox_nonempty (hd : 0 < d) {R : ℝ} (hR : 0 < R) :
    (frontier (obox (0 : Rd d) R)).Nonempty := by
  apply nonempty_frontier_iff.2
  constructor
  · exact ⟨0, HigherDimLFPP.DGZ.mem_obox_self 0 hR⟩
  · intro heq
    obtain ⟨z, hz⟩ := lsph_nonempty hd (0 : Rd d) hR.le
    exact hz.2 (by rw [heq]; trivial)

/-- All points outside the outer box pay at least the crossing cost. -/
def nd_globalOutsideBarrierSet (rGrid R r : ℝ) : Set (nd_Joint d rGrid) :=
  {s | ∀ x : Rd d, x ∉ obox 0 R →
    nd_crossPhi 0 R r s.1 ≤ nd_setInf {x} (lsph 0 r) s.1}

theorem nd_isClosed_globalOutsideBarrierSet (rGrid R r : ℝ) :
    IsClosed (nd_globalOutsideBarrierSet (d := d) rGrid R r) := by
  have e : nd_globalOutsideBarrierSet (d := d) rGrid R r =
      ⋂ x : Rd d, ⋂ (_hx : x ∉ obox 0 R),
        {s : nd_Joint d rGrid | nd_crossPhi 0 R r s.1 ≤
          nd_setInf {x} (lsph 0 r) s.1} := by
    ext s
    simp [nd_globalOutsideBarrierSet]
  rw [e]
  exact isClosed_iInter fun x => isClosed_iInter fun _ =>
    isClosed_le ((nd_continuous_crossPhi 0 R r).comp continuous_fst)
      ((nd_continuous_setInf isCompact_singleton (tn_isCompact_lsph 0 r)).comp
        continuous_fst)

theorem nd_jointSample_mem_globalOutsideBarrierSet {κ : Rd d → ℝ} {ξ Q : ℝ}
    (h : DGZHyp d κ ξ Q) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
    (hH : IsDyadicRealization κ P W H) {q : ℝ≥0∞} (hq0 : 0 < q) (hq1 : q < 1)
    (rGrid : ℝ) {R r : ℝ} (hr : 0 < r) (hrr : r < R) (n : ℕ) (ω : Ω) :
    nd_jointSample P H ξ q rGrid n ω ∈ nd_globalOutsideBarrierSet rGrid R r := by
  intro x hx
  let U := obox (0 : Rd d) R
  let A := lsph (0 : Rd d) r
  have hA : A.Nonempty := lsph_nonempty (by have := h.dim; omega : 0 < d) 0 hr.le
  have hAU : A ⊆ U :=
    (lsph_subset_cbox 0 r).trans (cbox_subset_obox hrr)
  have hF : (frontier U).Nonempty :=
    nd_frontier_obox_nonempty (by have := h.dim; omega : 0 < d) (hr.trans hrr)
  have hφ : Continuous fun z => H n z ω := (hH.band n).continuous ω
  have ha : 0 < aQ P H ξ n q :=
    tight_aQ_pos (by have := h.dim; omega : 0 < d) hH ξ n hq0 hq1
  have hsmall : acrossDist ξ (fun z => H n z ω) 0 R r ≤
      lfppSetDist ξ (fun z => H n z ω) univ (frontier U) A := by
    calc
      acrossDist ξ (fun z => H n z ω) 0 R r =
          lfppSetDist ξ (fun z => H n z ω) univ (lsph 0 R) A := by
            exact lfppSetDist_comm ξ (fun z => H n z ω) univ A (lsph 0 R)
      _ ≤ _ := lfppSetDist_anti hF hA (nd_frontier_obox_subset_lsph R) Subset.rfl
  have hexit := lfppSetDist_frontier_le (ξ := ξ) (φ := fun z => H n z ω)
    (U := U) (A := A) (x := x) hφ (HigherDimLFPP.DGZ.isOpen_obox 0 R)
    hAU hA hx
  have hscaled := mul_le_mul_of_nonneg_left (hsmall.trans hexit) (inv_nonneg.2 ha.le)
  change nd_crossPhi 0 R r
      (normMetricC ξ (fun z => H n z ω) (aQ P H ξ n q)) ≤
    nd_setInf {x} A (normMetricC ξ (fun z => H n z ω) (aQ P H ξ n q))
  rw [nd_crossPhi_normMetricC hφ ha ξ 0 R r,
    nd_setInf_normMetricC hφ ha ξ {x} A]
  exact hscaled

theorem nd_ae_globalOutsideBarrierSet_of_tendsto {κ : Rd d → ℝ} {ξ Q : ℝ}
    (h : DGZHyp d κ ξ Q) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WN d → Ω → ℝ} {H : ℕ → Rd d → Ω → ℝ}
    (hH : IsDyadicRealization κ P W H) {q : ℝ≥0∞} (hq0 : 0 < q) (hq1 : q < 1)
    (rGrid r : ℝ) (hr : 0 < r) (R : ℝ) (hrr : r < R)
    (ns : ℕ → ℕ) {μ : ProbabilityMeasure (nd_Joint d rGrid)}
    (hlim : Tendsto
      (fun k => nd_jointLaw P hH.whiteNoise.isProbabilityMeasure H ξ q rGrid (ns k))
      atTop (𝓝 μ)) :
    ∀ᵐ s ∂(μ : Measure (nd_Joint d rGrid)),
      s ∈ nd_globalOutsideBarrierSet rGrid R r := by
  apply LQGMetric.DFGPS.ae_mem_of_isClosed_of_forall hlim
    (nd_isClosed_globalOutsideBarrierSet rGrid R r)
  intro k
  change (P.map (nd_jointSample P H ξ q rGrid (ns k)))
    (nd_globalOutsideBarrierSet rGrid R r) = 1
  rw [Measure.map_apply (nd_measurable_jointSample hH ξ q rGrid (ns k))
    (nd_isClosed_globalOutsideBarrierSet rGrid R r).measurableSet]
  have heq : (nd_jointSample P H ξ q rGrid (ns k)) ⁻¹'
      nd_globalOutsideBarrierSet rGrid R r =
      (Set.univ : Set Ω) := by
    ext ω
    simp [nd_jointSample_mem_globalOutsideBarrierSet h hH hq0 hq1 rGrid hr hrr (ns k) ω]
  rw [heq]
  exact @IsProbabilityMeasure.measure_univ Ω _ P hH.whiteNoise.isProbabilityMeasure

end HigherDimLQGMetric.DGZ
