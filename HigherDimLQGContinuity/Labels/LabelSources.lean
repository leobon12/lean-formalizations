import HigherDimLQGContinuity.Labels.Realizable
import HigherDimLQGContinuity.Routing.Leads

/-!
# Source labels fit the finite catalogue cutoffs

The lead theorem supplies finite `ν`-grid sequences in reserved boxes. The
cell sets supplied by a source arc are likewise contained in its reserved box.
Both therefore have finite codes used by `labelCatalogue`.
-/

set_option autoImplicit false

noncomputable section

open Set Metric
open HigherDimLFPP (Rd)

namespace HigherDimLQGContinuity

/-- Extract the integer index of a point of the grid based at zero. -/
private def gridIndex {d : ℕ} {ν : ℝ} (z : Rd d)
    (hz : Routing.OnGrid ν 0 z) : Fin d → ℤ := Classical.choose hz

private theorem gridIndex_point {d : ℕ} {ν : ℝ} (z : Rd d)
    (hz : Routing.OnGrid ν 0 z) :
    (WithLp.toLp 2 fun i => ν * (gridIndex z hz i : ℝ) : Rd d) = z := by
  ext i
  have hi := Classical.choose_spec hz i
  simpa only [gridIndex, PiLp.toLp_apply, PiLp.zero_apply, zero_add] using hi.symm

/-- Encode a bounded lead sequence in the finite index box, padding after its
last vertex. -/
def leadCodeOfBox {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    {ν : ℝ} (hν : 0 < ν) (e : S.Edge) (N n : ℕ) (hn : n ≤ N)
    (y : ℕ → Rd d)
    (hgrid : ∀ j ≤ n, Routing.OnGrid ν 0 (y j))
    (hbox : ∀ j ≤ n, y j ∈ S.box e) :
    LeadCode d (labelLeadCutoff ν) N := by
  let last : Fin (N + 1) := ⟨n, by omega⟩
  let grid : Fin (N + 1) → LabelIndex d (labelLeadCutoff ν) := fun j =>
    if hj : j.val ≤ n then
      ⟨gridIndex (y j.val) (hgrid j.val hj), by
        apply grid_index_mem_labelCutoff S hd hν e
        rw [gridIndex_point (y j.val) (hgrid j.val hj)]
        exact hbox j.val hj⟩
    else ⟨0, by simp [labelIndexFinset]⟩
  exact ⟨last, grid⟩

theorem leadCodeOfBox_point {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    {ν : ℝ} (hν : 0 < ν) (e : S.Edge) (N n : ℕ) (hn : n ≤ N)
    (y : ℕ → Rd d)
    (hgrid : ∀ j ≤ n, Routing.OnGrid ν 0 (y j))
    (hbox : ∀ j ≤ n, y j ∈ S.box e)
    (j : Fin (N + 1)) (hj : j.val ≤ n) :
    (leadCodeOfBox S hd hν e N n hn y hgrid hbox).point ν j = y j.val := by
  unfold leadCodeOfBox LeadCode.point
  simp only [dite_eq_left hj]
  exact gridIndex_point (y j.val) (hgrid j.val hj)

/-- A lead supplied by `b:lem-leads` fits the catalogue and its code satisfies
the deterministic conditions (L3)–(L4). -/
theorem leadCodeOfBox_geometry {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    {ν r : ℝ} (hν : 0 < ν) (e : S.Edge) (N n : ℕ) (hn : n ≤ N)
    (y : ℕ → Rd d)
    (hgrid : ∀ j ≤ n, Routing.OnGrid ν 0 (y j))
    (hbox : ∀ j ≤ n, y j ∈ S.box e)
    (p : Rd d) (hstart : y 0 = p) (htwo : 2 ≤ n)
    (hmargin : ∀ j, 1 ≤ j → j ≤ n → ∀ i,
      |y j i - (S.edgeCenter e) i| + r / (4 * √(d : ℝ)) ≤ S.boxHalfSide)
    (hinj : ∀ j ≤ n, ∀ j' ≤ n, y j = y j' → j = j')
    (hsep : ∀ j j', j + 2 ≤ j' → j' < n →
      ∀ x ∈ segment ℝ (y j) (y (j + 1)),
      ∀ x' ∈ segment ℝ (y j') (y (j' + 1)),
        Routing.gpC1 4 * ν ^ 3 ≤ dist x x')
    (hinc : ∀ j, j + 1 < n →
      segment ℝ (y j) (y (j + 1)) ∩
        segment ℝ (y (j + 1)) (y (j + 2)) = {y (j + 1)}) :
    (leadCodeOfBox S hd hν e N n hn y hgrid hbox).Geometry
      ν r (Routing.gpC1 4) (S.edgeCenter e) S.boxHalfSide p := by
  let P := leadCodeOfBox S hd hν e N n hn y hgrid hbox
  have hlast : P.last.val = n := rfl
  have hpoint (j : Fin (N + 1)) (hj : j.val ≤ n) : P.point ν j = y j.val :=
    leadCodeOfBox_point S hd hν e N n hn y hgrid hbox j hj
  change 2 ≤ P.last.val ∧ P.point ν 0 = p ∧
    (∀ j : Fin (N + 1), j ≤ P.last →
      (∀ i, |(P.point ν j) i - (S.edgeCenter e) i| ≤ S.boxHalfSide) ∧
      (1 ≤ j.val → ∀ i,
        |(P.point ν j) i - (S.edgeCenter e) i| + r / (4 * √(d : ℝ)) ≤ S.boxHalfSide)) ∧
    (∀ j j' : Fin (N + 1), j ≤ P.last → j' ≤ P.last →
      P.point ν j = P.point ν j' → j = j') ∧
    (∀ j j' : Fin N, j.val + 2 ≤ j'.val → j'.val < P.last.val →
      ∀ x ∈ segment ℝ (P.point ν j.castSucc) (P.point ν j.succ),
      ∀ x' ∈ segment ℝ (P.point ν j'.castSucc) (P.point ν j'.succ),
        Routing.gpC1 4 * ν ^ 3 ≤ dist x x') ∧
    (∀ j : Fin N, ∀ h : j.val + 1 < P.last.val,
      segment ℝ (P.point ν j.castSucc) (P.point ν j.succ) ∩
        segment ℝ (P.point ν j.succ)
          (P.point ν ⟨j.val + 2, by have := P.last.isLt; omega⟩) =
            {P.point ν j.succ})
  refine ⟨by simpa [hlast] using htwo, ?_, ?_, ?_, ?_, ?_⟩
  · have h0n : (0 : Fin (N + 1)).val ≤ n := by simp
    rw [hpoint 0 h0n]
    exact hstart
  · intro j hj
    have hjn : j.val ≤ n := by simpa only [Fin.le_def, hlast] using hj
    rw [hpoint j hjn]
    constructor
    · exact hbox j.val hjn
    · intro h1 i
      exact hmargin j.val h1 hjn i
  · intro j j' hj hj' heq
    have hjn : j.val ≤ n := by simpa only [Fin.le_def, hlast] using hj
    have hjn' : j'.val ≤ n := by simpa only [Fin.le_def, hlast] using hj'
    rw [hpoint j hjn, hpoint j' hjn'] at heq
    exact Fin.ext (hinj j.val hjn j'.val hjn' heq)
  · intro j j' hjj' hj'last x hx x' hx'
    have hj'lt : j'.val < n := by simpa [hlast] using hj'last
    have hjn : j.val + 1 ≤ n := by omega
    have hj'n : j'.val + 1 ≤ n := by omega
    rw [hpoint j.castSucc (by simpa using (show j.val ≤ n by omega)),
      hpoint j.succ (by simpa using hjn)] at hx
    rw [hpoint j'.castSucc (by simpa using (show j'.val ≤ n by omega)),
      hpoint j'.succ (by simpa using hj'n)] at hx'
    exact hsep j.val j'.val hjj' hj'lt x hx x' hx'
  · intro j hj
    have hjlt : j.val + 1 < n := by simpa [hlast] using hj
    have hjn : j.val + 2 ≤ n := by omega
    rw [hpoint j.castSucc (by simpa using (show j.val ≤ n by omega)),
      hpoint j.succ (by simpa using (show j.val + 1 ≤ n by omega)),
      hpoint ⟨j.val + 2, by have := P.last.isLt; omega⟩ hjn]
    exact hinc j.val hjlt

/-- The code extracted from one source lead. -/
def leadCodeOfIsLead {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    {ν r : ℝ} (hν : 0 < ν) (e : S.Edge) (p g : Rd d) (I : Set ℝ)
    (γ : ℝ → Rd d) (N n : ℕ) (y : ℕ → Rd d)
    (h : Routing.IsLead (S.edgeCenter e) S.boxHalfSide p g I γ r ν 0 N n y) :
    LeadCode d (labelLeadCutoff ν) N :=
  leadCodeOfBox S hd hν e N n h.le_N y h.onGrid h.mem_box

theorem leadCodeOfIsLead_geometry {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    {ν r : ℝ} (hν : 0 < ν) (e : S.Edge) (p g : Rd d) (I : Set ℝ)
    (γ : ℝ → Rd d) (N n : ℕ) (y : ℕ → Rd d)
    (h : Routing.IsLead (S.edgeCenter e) S.boxHalfSide p g I γ r ν 0 N n y) :
    (leadCodeOfIsLead S hd hν e p g I γ N n y h).Geometry
      ν r (Routing.gpC1 4) (S.edgeCenter e) S.boxHalfSide p :=
  leadCodeOfBox_geometry S hd hν e N n h.le_N y h.onGrid h.mem_box p
    h.start h.two_le h.margin h.injOn h.sep h.inc

theorem leadCodeOfIsLead_point {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    {ν r : ℝ} (hν : 0 < ν) (e : S.Edge) (p g : Rd d) (I : Set ℝ)
    (γ : ℝ → Rd d) (N n : ℕ) (y : ℕ → Rd d)
    (h : Routing.IsLead (S.edgeCenter e) S.boxHalfSide p g I γ r ν 0 N n y)
    (j : Fin (N + 1)) (hj : j.val ≤ n) :
    (leadCodeOfIsLead S hd hν e p g I γ N n y h).point ν j = y j.val :=
  leadCodeOfBox_point S hd hν e N n h.le_N y h.onGrid h.mem_box j hj

/-- Every point of the coded trace lies on one of the source lead's actual
segments. -/
theorem leadCodeOfIsLead_trace {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    {ν r : ℝ} (hν : 0 < ν) (e : S.Edge) (p g : Rd d) (I : Set ℝ)
    (γ : ℝ → Rd d) (N n : ℕ) (y : ℕ → Rd d)
    (h : Routing.IsLead (S.edgeCenter e) S.boxHalfSide p g I γ r ν 0 N n y)
    {x : Rd d}
    (hx : x ∈ (leadCodeOfIsLead S hd hν e p g I γ N n y h).trace ν) :
    ∃ j < n, x ∈ segment ℝ (y j) (y (j + 1)) := by
  let P := leadCodeOfIsLead S hd hν e p g I γ N n y h
  have hlast : P.last.val = n := rfl
  change x ∈ P.trace ν at hx
  unfold LeadCode.trace at hx
  obtain ⟨j, hj⟩ := mem_iUnion.mp hx
  split_ifs at hj with hjn
  · have hjlt : j.val < n := by simpa [hlast] using hjn
    have hj0 : j.val ≤ n := by omega
    have hj1 : j.val + 1 ≤ n := by omega
    rw [leadCodeOfIsLead_point S hd hν e p g I γ N n y h
        j.castSucc (by simpa using hj0),
      leadCodeOfIsLead_point S hd hν e p g I γ N n y h
        j.succ (by simpa using hj1)] at hj
    exact ⟨j.val, hjlt, hj⟩
  · simp at hj

/-- Every source edge constructed from cell sets and two leads has an edge
label in the finite catalogue with exactly those cell sets. -/
theorem edgeLabel_of_source_leads {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    {μ ν r : ℝ} (hμ : 0 < μ) (hν : 0 < ν)
    (e : S.Edge) (trial : Fin S.Ntr)
    (Qch Q0 Q1 : Finset (Fin d → ℤ))
    (hch : ∀ k ∈ Qch, cell μ (S.edgeCenter e) k ⊆ S.box e)
    (hQ0 : ∀ k ∈ Q0, cell μ (S.edgeCenter e) k ⊆ S.box e)
    (hQ1 : ∀ k ∈ Q1, cell μ (S.edgeCenter e) k ⊆ S.box e)
    (γ : ℝ → Rd d) (t₀ : ℝ) (N n0 n1 : ℕ) (y0 y1 : ℕ → Rd d)
    (h0 : Routing.IsLead (S.edgeCenter e) S.boxHalfSide (S.port e 0) (γ 0)
      (Icc t₀ 1) γ r ν 0 N n0 y0)
    (h1 : Routing.IsLead (S.edgeCenter e) S.boxHalfSide (S.port e 1) (γ 1)
      (Icc 0 (1 - t₀)) γ r ν 0 N n1 y1)
    (hcross : ∀ j < n0, ∀ j' < n1,
      ∀ x ∈ segment ℝ (y0 j) (y0 (j + 1)),
      ∀ x' ∈ segment ℝ (y1 j') (y1 (j' + 1)),
        Routing.gpC1 4 * ν ^ 3 ≤ dist x x') :
    ∃ E : EdgeLabel S e (labelCellCutoff S μ) (labelLeadCutoff ν) N
      μ ν r (Routing.gpC1 4),
      E.1.trial = trial ∧ labelCellIndices E.1.chamber = Qch ∧
      labelCellIndices E.1.gate0 = Q0 ∧ labelCellIndices E.1.gate1 = Q1 ∧
      E.1.lead0 = leadCodeOfIsLead S hd hν e (S.port e 0) (γ 0)
        (Icc t₀ 1) γ N n0 y0 h0 ∧
      E.1.lead1 = leadCodeOfIsLead S hd hν e (S.port e 1) (γ 1)
        (Icc 0 (1 - t₀)) γ N n1 y1 h1 := by
  let hchK : ∀ k ∈ Qch, k ∈ labelIndexFinset d (labelCellCutoff S μ) :=
    fun k hk => cell_index_mem_labelCutoff S hμ e k (hch k hk)
  let h0K : ∀ k ∈ Q0, k ∈ labelIndexFinset d (labelCellCutoff S μ) :=
    fun k hk => cell_index_mem_labelCutoff S hμ e k (hQ0 k hk)
  let h1K : ∀ k ∈ Q1, k ∈ labelIndexFinset d (labelCellCutoff S μ) :=
    fun k hk => cell_index_mem_labelCutoff S hμ e k (hQ1 k hk)
  let P0 := leadCodeOfIsLead S hd hν e (S.port e 0) (γ 0) (Icc t₀ 1) γ N n0 y0 h0
  let P1 := leadCodeOfIsLead S hd hν e (S.port e 1) (γ 1) (Icc 0 (1 - t₀)) γ N n1 y1 h1
  let C : EdgeLabelCode S (labelCellCutoff S μ) (labelLeadCutoff ν) N :=
    ⟨trial, encodeLabelIndices Qch hchK, encodeLabelIndices Q0 h0K,
      encodeLabelIndices Q1 h1K, P0, P1⟩
  have hgeom : C.Geometry S e μ ν r (Routing.gpC1 4) := by
    change (∀ k ∈ labelCellIndices C.chamber, cell μ (S.edgeCenter e) k ⊆ S.box e) ∧
      (∀ k ∈ labelCellIndices C.gate0, cell μ (S.edgeCenter e) k ⊆ S.box e) ∧
      (∀ k ∈ labelCellIndices C.gate1, cell μ (S.edgeCenter e) k ⊆ S.box e) ∧
      C.lead0.Geometry ν r (Routing.gpC1 4) (S.edgeCenter e) S.boxHalfSide (S.port e 0) ∧
      C.lead1.Geometry ν r (Routing.gpC1 4) (S.edgeCenter e) S.boxHalfSide (S.port e 1) ∧
      (∀ j j' : Fin N, j.val < C.lead0.last.val → j'.val < C.lead1.last.val →
        ∀ x ∈ segment ℝ (C.lead0.point ν j.castSucc) (C.lead0.point ν j.succ),
        ∀ x' ∈ segment ℝ (C.lead1.point ν j'.castSucc) (C.lead1.point ν j'.succ),
          Routing.gpC1 4 * ν ^ 3 ≤ dist x x')
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [C, labelCellIndices_encode] using hch
    · simpa only [C, labelCellIndices_encode] using hQ0
    · simpa only [C, labelCellIndices_encode] using hQ1
    · exact leadCodeOfIsLead_geometry S hd hν e (S.port e 0) (γ 0) (Icc t₀ 1) γ N n0 y0 h0
    · exact leadCodeOfIsLead_geometry S hd hν e (S.port e 1) (γ 1) (Icc 0 (1 - t₀)) γ N n1 y1 h1
    · intro j j' hj hj' x hx x' hx'
      have hj0 : j.val < n0 := hj
      have hj1 : j'.val < n1 := hj'
      rw [leadCodeOfIsLead_point S hd hν e (S.port e 0) (γ 0) (Icc t₀ 1) γ N n0 y0 h0
          j.castSucc (by simpa using (show j.val ≤ n0 by omega)),
        leadCodeOfIsLead_point S hd hν e (S.port e 0) (γ 0) (Icc t₀ 1) γ N n0 y0 h0
          j.succ (by simpa using (show j.val + 1 ≤ n0 by omega))] at hx
      rw [leadCodeOfIsLead_point S hd hν e (S.port e 1) (γ 1) (Icc 0 (1 - t₀)) γ N n1 y1 h1
          j'.castSucc (by simpa using (show j'.val ≤ n1 by omega)),
        leadCodeOfIsLead_point S hd hν e (S.port e 1) (γ 1) (Icc 0 (1 - t₀)) γ N n1 y1 h1
          j'.succ (by simpa using (show j'.val + 1 ≤ n1 by omega))] at hx'
      exact hcross j.val hj0 j'.val hj1 x hx x' hx'
  refine ⟨⟨C, hgeom⟩, rfl, ?_, ?_, ?_, rfl, rfl⟩
  · exact labelCellIndices_encode Qch hchK
  · exact labelCellIndices_encode Q0 h0K
  · exact labelCellIndices_encode Q1 h1K

/-- The source arc and the two Q2 leads realize the encoded finite edge
label. This is the deterministic bridge used in source exhaustion. -/
theorem edgeLabel_of_source_leads_realizable {d : ℕ} (S : SiteData d)
    (hd : 2 ≤ d) {μ ν r : ℝ} (hμ : 0 < μ) (hν : 0 < ν) (hr : 0 < r)
    (e : S.Edge) (trial : Fin S.Ntr)
    (Qch Q0 Q1 : Finset (Fin d → ℤ))
    (hch : ∀ k ∈ Qch, cell μ (S.edgeCenter e) k ⊆ S.box e)
    (hQ0 : ∀ k ∈ Q0, cell μ (S.edgeCenter e) k ⊆ S.box e)
    (hQ1 : ∀ k ∈ Q1, cell μ (S.edgeCenter e) k ⊆ S.box e)
    (γ : ℝ → Rd d) (A α β t₀ : ℝ)
    (hmod : Topology.ArcModuli γ A α β)
    (hseed : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ S.seedK e trial)
    (hcoveredCh : CoveredHit μ (S.edgeCenter e) Qch (γ '' Icc 0 1))
    (hcovered0 : CoveredHit μ (S.edgeCenter e) Q0 (γ '' Icc 0 (2 * t₀)))
    (hcovered1 : CoveredHit μ (S.edgeCenter e) Q1 (γ '' Icc (1 - 2 * t₀) 1))
    (N n0 n1 : ℕ) (y0 y1 : ℕ → Rd d)
    (h0 : Routing.IsLead (S.edgeCenter e) S.boxHalfSide (S.port e 0) (γ 0)
      (Icc t₀ 1) γ r ν 0 N n0 y0)
    (h1 : Routing.IsLead (S.edgeCenter e) S.boxHalfSide (S.port e 1) (γ 1)
      (Icc 0 (1 - t₀)) γ r ν 0 N n1 y1)
    (hcross : ∀ j < n0, ∀ j' < n1,
      ∀ x ∈ segment ℝ (y0 j) (y0 (j + 1)),
      ∀ x' ∈ segment ℝ (y1 j') (y1 (j' + 1)),
        Routing.gpC1 4 * ν ^ 3 ≤ dist x x') :
    ∃ E : EdgeLabel S e (labelCellCutoff S μ) (labelLeadCutoff ν) N
      μ ν r (Routing.gpC1 4),
      E.IsRealizable S e A α β t₀ ∧
      E.1.trial = trial ∧ labelCellIndices E.1.chamber = Qch ∧
      labelCellIndices E.1.gate0 = Q0 ∧ labelCellIndices E.1.gate1 = Q1 := by
  obtain ⟨E, htrial, hCh, h0Q, h1Q, hP0, hP1⟩ :=
    edgeLabel_of_source_leads S hd hμ hν e trial Qch Q0 Q1 hch hQ0 hQ1
      γ t₀ N n0 n1 y0 y1 h0 h1 hcross
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hsqrt : √(d : ℝ) ≤ d := (Real.sqrt_le_self_iff).2 (Or.inr hdR)
  have hattachBound : √(d : ℝ) * (ν / 2) ≤ d * ν := by
    nlinarith [mul_le_mul_of_nonneg_right hsqrt (by positivity : (0 : ℝ) ≤ ν / 2)]
  have hreal : E.IsRealizable S e A α β t₀ := by
    refine ⟨γ, hmod, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [htrial] using hseed
    · simpa only [hCh] using hcoveredCh
    · simpa only [h0Q] using hcovered0
    · simpa only [h1Q] using hcovered1
    · intro x hx t ht
      rw [hP0] at hx
      obtain ⟨j, hj, hxj⟩ := leadCodeOfIsLead_trace S hd hν e
        (S.port e 0) (γ 0) (Icc t₀ 1) γ N n0 y0 h0 hx
      have hclear := h0.clear j hj x hxj t ht
      nlinarith
    · intro x hx t ht
      rw [hP1] at hx
      obtain ⟨j, hj, hxj⟩ := leadCodeOfIsLead_trace S hd hν e
        (S.port e 1) (γ 1) (Icc 0 (1 - t₀)) γ N n1 y1 h1 hx
      have hclear := h1.clear j hj x hxj t ht
      nlinarith
    · rw [hP0]
      let P := leadCodeOfIsLead S hd hν e (S.port e 0) (γ 0)
        (Icc t₀ 1) γ N n0 y0 h0
      have hn : P.last.val = n0 := rfl
      rw [leadCodeOfIsLead_point S hd hν e (S.port e 0) (γ 0)
        (Icc t₀ 1) γ N n0 y0 h0 P.last (by simp [hn])]
      change ‖y0 n0 - γ 0‖ ≤ d * ν
      exact h0.attach.trans hattachBound
    · rw [hP1]
      let P := leadCodeOfIsLead S hd hν e (S.port e 1) (γ 1)
        (Icc 0 (1 - t₀)) γ N n1 y1 h1
      have hn : P.last.val = n1 := rfl
      rw [leadCodeOfIsLead_point S hd hν e (S.port e 1) (γ 1)
        (Icc 0 (1 - t₀)) γ N n1 y1 h1 P.last (by simp [hn])]
      change ‖y1 n1 - γ 1‖ ≤ d * ν
      exact h1.attach.trans hattachBound
  exact ⟨E, hreal, htrial, hCh, h0Q, h1Q⟩

end HigherDimLQGContinuity
