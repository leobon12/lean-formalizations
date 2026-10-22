import HigherDimLQGMetric.DGZ.TightCompact
import HigherDimLQGMetric.B3.Interfaces

/-! A countable connected relatively compact exhaustion of any open set.
It uses the compact exhaustion already present in the DGZ library. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Set Metric Topology TopologicalSpace
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- An index selects the component of the interior of a compact exhaustion
stage that contains a fixed point of the countable dense sequence. -/
def l7a_CompIndex (V : TopologicalSpace.Opens (Rd d)) : Type :=
  {p : ℕ × ℕ // TopologicalSpace.denseSeq (Rd d) p.2 ∈
    interior (DGZ.tcExhaust V p.1)}

instance (V : TopologicalSpace.Opens (Rd d)) :
    Countable (l7a_CompIndex V) := by
  unfold l7a_CompIndex
  infer_instance

def l7a_compDomain (V : TopologicalSpace.Opens (Rd d))
    (i : l7a_CompIndex V) : TopologicalSpace.Opens (Rd d) :=
  ⟨connectedComponentIn (interior (DGZ.tcExhaust V i.1.1))
    (TopologicalSpace.denseSeq (Rd d) i.1.2),
    isOpen_interior.connectedComponentIn⟩

theorem l7a_compDomain_connected (V : TopologicalSpace.Opens (Rd d))
    (i : l7a_CompIndex V) : IsConnected (l7a_compDomain V i : Set (Rd d)) := by
  exact isConnected_connectedComponentIn_iff.mpr i.2

theorem l7a_compDomain_closure_subset (V : TopologicalSpace.Opens (Rd d))
    (i : l7a_CompIndex V) : closure (l7a_compDomain V i : Set (Rd d)) ⊆
      (V : Set (Rd d)) := by
  have hsub : (l7a_compDomain V i : Set (Rd d)) ⊆
      DGZ.tcExhaust (V : Set (Rd d)) i.1.1 :=
    (connectedComponentIn_subset _ _).trans interior_subset
  have hclosed : IsClosed (DGZ.tcExhaust (V : Set (Rd d)) i.1.1) :=
    (DGZ.tcExhaust_isCompact (V : Set (Rd d)) i.1.1).isClosed
  exact (closure_minimal hsub hclosed).trans
    (DGZ.tcExhaust_subset (V : Set (Rd d)) i.1.1)

theorem l7a_compDomain_closure_compact (V : TopologicalSpace.Opens (Rd d))
    (i : l7a_CompIndex V) : IsCompact (closure (l7a_compDomain V i : Set (Rd d))) := by
  have hsub : (l7a_compDomain V i : Set (Rd d)) ⊆ DGZ.tcExhaust V i.1.1 :=
    (connectedComponentIn_subset _ _).trans interior_subset
  have hK := DGZ.tcExhaust_isCompact (V : Set (Rd d)) i.1.1
  exact hK.of_isClosed_subset isClosed_closure (closure_minimal hsub hK.isClosed)

/-- Every compact subset of an open set fits in the interior of one DGZ
compact exhaustion stage. -/
theorem l7a_compact_subset_interior_exhaust
    (V : TopologicalSpace.Opens (Rd d)) {K : Set (Rd d)}
    (hK : IsCompact K) (hKV : K ⊆ V) :
    ∃ j : ℕ, K ⊆ interior (DGZ.tcExhaust (V : Set (Rd d)) j) := by
  have hcover : K ⊆ ⋃ j : ℕ,
      interior (DGZ.tcExhaust (V : Set (Rd d)) j) := by
    intro x hx
    obtain ⟨j, hj⟩ := DGZ.tcExhaust_mem_nhds V.isOpen (hKV hx)
    exact mem_iUnion.mpr ⟨j, mem_interior_iff_mem_nhds.mpr hj⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover
    (fun j => interior (DGZ.tcExhaust (V : Set (Rd d)) j))
    (fun _ => isOpen_interior) hcover
  refine ⟨s.sup id, fun x hx => ?_⟩
  obtain ⟨j, hjs, hxj⟩ := mem_iUnion₂.mp (hs hx)
  exact interior_mono (DGZ.tcExhaust_mono (V : Set (Rd d))
    (Finset.le_sup (f := id) hjs)) hxj

/-- A compact connected set inside `V` lies in one member of the countable
family of connected relatively compact subdomains. -/
theorem l7a_exists_compDomain_of_compact_connected
    (V : TopologicalSpace.Opens (Rd d)) {K : Set (Rd d)}
    (hK : IsCompact K) (hKconn : IsConnected K) (hKV : K ⊆ V) :
    ∃ i : l7a_CompIndex V, K ⊆ l7a_compDomain V i := by
  obtain ⟨j, hj⟩ := l7a_compact_subset_interior_exhaust V hK hKV
  obtain ⟨x, hx⟩ := hKconn.nonempty
  let A : Set (Rd d) := interior (DGZ.tcExhaust (V : Set (Rd d)) j)
  have hxA : x ∈ A := hj hx
  have hKC : K ⊆ connectedComponentIn A x :=
    hKconn.isPreconnected.subset_connectedComponentIn hx hj
  have hopen : IsOpen (connectedComponentIn A x) := isOpen_interior.connectedComponentIn
  obtain ⟨n, hn⟩ := (TopologicalSpace.denseRange_denseSeq (Rd d)).exists_mem_open
    hopen ⟨x, mem_connectedComponentIn hxA⟩
  let i : l7a_CompIndex V := ⟨(j, n), connectedComponentIn_subset A x hn⟩
  refine ⟨i, ?_⟩
  change K ⊆ connectedComponentIn A (TopologicalSpace.denseSeq (Rd d) n)
  rw [← connectedComponentIn_eq hn]
  exact hKC

/-- Internal distance on an open set is the infimum of internal distances on
the countable connected relatively compact subdomains. -/
theorem l7a_internal_eq_iInf_compDomain (D : ContMetric d)
    (V : TopologicalSpace.Opens (Rd d)) (u v : Rd d) :
    D.internal V u v =
      ⨅ i : l7a_CompIndex V, D.internal (l7a_compDomain V i) u v := by
  refine le_antisymm (le_iInf fun i =>
    LQGMetric.MetricGeometry.internalEDist_anti
      (image_mono (subset_closure.trans (l7a_compDomain_closure_subset V i))) _ _) ?_
  unfold ContMetric.internal LQGMetric.MetricGeometry.internalEDist
  refine le_iInf fun γ => ?_
  let K : Set (Rd d) := range (D.unpt ∘ γ.1)
  have hKc : IsConnected K :=
    isConnected_range (D.continuous_unpt.comp γ.1.continuous)
  have hKV : K ⊆ V := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨y, hy, hyt⟩ := γ.2 t
    simp only [Function.comp_apply, ← hyt, ContMetric.unpt_pt]
    exact hy
  obtain ⟨i, hKi⟩ := l7a_exists_compDomain_of_compact_connected V
    (isCompact_range (D.continuous_unpt.comp γ.1.continuous)) hKc hKV
  refine iInf_le_of_le i (iInf_le_of_le ⟨γ.1, fun t => ⟨D.unpt (γ.1 t),
    hKi ⟨t, rfl⟩, ContMetric.pt_unpt _ _⟩⟩ le_rfl)

/-- The internal metric on `V` is measurable from the countable family of
internal metrics on relatively compact connected subdomains. -/
theorem l7a_famSigma_le_iSup_compDomain
    {Ω : Type} (D : Ω → ContMetric d)
    (V : TopologicalSpace.Opens (Rd d)) :
    famSigmaRd (internalFamRd D) V ≤
      ⨆ i : l7a_CompIndex V,
        famSigmaRd (internalFamRd D) (l7a_compDomain V i) := by
  let M := ⨆ i : l7a_CompIndex V,
    famSigmaRd (internalFamRd D) (l7a_compDomain V i)
  have hW : ∀ i : l7a_CompIndex V,
      Measurable[M] (fun ω => internalFamRd D ω (l7a_compDomain V i)) := by
    intro i
    exact (comap_measurable _).mono (le_iSup (fun i =>
      famSigmaRd (internalFamRd D) (l7a_compDomain V i)) i) le_rfl
  have he : (fun ω => internalFamRd D ω V) =
      fun ω u v => ⨅ i : l7a_CompIndex V,
        internalFamRd D ω (l7a_compDomain V i) u v := by
    funext ω u v
    exact l7a_internal_eq_iInf_compDomain (D ω) V u v
  have hm : Measurable[M] (fun ω => internalFamRd D ω V) := by
    rw [he]
    refine measurable_pi_iff.2 fun u => measurable_pi_iff.2 fun v => ?_
    refine Measurable.iInf fun i => ?_
    exact (measurable_pi_apply v).comp ((measurable_pi_apply u).comp (hW i))
  exact hm.comap_le

/-- The same countable exhaustion identity holds after the positive random
normalization used in ξ-additive locality. -/
theorem l7a_rescFam_eq_iInf_compDomain {Ω : Type}
    (ξ : ℝ) (h : Ω → DistRd d) (D : Ω → ContMetric d)
    (z : Rd d) (r : ℝ) (V : TopologicalSpace.Opens (Rd d))
    (ω : Ω) (u v : Rd d) :
    rescFam ξ h D z r ω V u v =
      ⨅ i : l7a_CompIndex V,
        rescFam ξ h D z r ω (l7a_compDomain V i) u v := by
  let c : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-ξ * sphereAvg (h ω) r z))
  have hc0 : c ≠ 0 := (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  have hct : c ≠ ⊤ := ENNReal.ofReal_ne_top
  change c * (D ω).internal V u v =
    ⨅ i : l7a_CompIndex V, c * (D ω).internal (l7a_compDomain V i) u v
  rw [l7a_internal_eq_iInf_compDomain]
  exact ENNReal.mul_iInf_of_ne hc0 hct

/-- The scaled internal metric on `V` is measurable from the scaled metrics
on the countable connected subdomains. -/
theorem l7a_rescFamSigma_le_iSup_compDomain {Ω : Type}
    (ξ : ℝ) (h : Ω → DistRd d) (D : Ω → ContMetric d)
    (z : Rd d) (r : ℝ) (V : TopologicalSpace.Opens (Rd d)) :
    famSigmaRd (rescFam ξ h D z r) V ≤
      ⨆ i : l7a_CompIndex V,
        famSigmaRd (rescFam ξ h D z r) (l7a_compDomain V i) := by
  let M := ⨆ i : l7a_CompIndex V,
    famSigmaRd (rescFam ξ h D z r) (l7a_compDomain V i)
  have hW : ∀ i : l7a_CompIndex V,
      Measurable[M] (fun ω => rescFam ξ h D z r ω (l7a_compDomain V i)) := by
    intro i
    exact (comap_measurable _).mono (le_iSup (fun i =>
      famSigmaRd (rescFam ξ h D z r) (l7a_compDomain V i)) i) le_rfl
  have he : (fun ω => rescFam ξ h D z r ω V) =
      fun ω u v => ⨅ i : l7a_CompIndex V,
        rescFam ξ h D z r ω (l7a_compDomain V i) u v := by
    funext ω u v
    exact l7a_rescFam_eq_iInf_compDomain ξ h D z r V ω u v
  have hm : Measurable[M] (fun ω => rescFam ξ h D z r ω V) := by
    rw [he]
    refine measurable_pi_iff.2 fun u => measurable_pi_iff.2 fun v => ?_
    refine Measurable.iInf fun i => ?_
    exact (measurable_pi_apply v).comp ((measurable_pi_apply u).comp (hW i))
  exact hm.comap_le

end HigherDimLQGMetric
