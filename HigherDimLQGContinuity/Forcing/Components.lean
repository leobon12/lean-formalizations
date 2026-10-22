import HigherDimLQGContinuity.Forcing.Excursion

/-! # Connected visited nodes in the site forcing certificate -/

set_option autoImplicit false

noncomputable section

open Set Topology Metric Filter
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open LQGMetric.MetricGeometry
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- The metric modification vanishes along the two tails before the first and after the last
visit to the closed collar. -/
theorem q6_V_tail_lengths {D E D' : ContMetric d} {f : C(Rd d, ℝ)}
    {ξ M θ h δsep ε₀ εnet εatt aout H b v d₀ : ℝ}
    (cert : ForcingCert D E f ξ M θ h δsep ε₀ εnet εatt aout H b v d₀)
    (hW : IsWeylInternal ξ (-f) D D')
    {P : ℝ → Rd d} {u w : ℝ}
    (hP : ContinuousOn P (Icc u w))
    (hvisit : ∃ t ∈ Icc u w, P t ∈ cthickening h cert.U) :
    let σ₁ := firstVisit P u w (cthickening h cert.U)
    let σ₂ := lastVisit P u w (cthickening h cert.U)
    D'.len P u σ₁ = D.len P u σ₁ ∧ D'.len P σ₂ w = D.len P σ₂ w := by
  dsimp
  obtain ⟨hσ₁, _, hσ₂, _, _⟩ :=
    q6_visit_times hP isClosed_cthickening hvisit
  constructor
  · by_cases heq : u = firstVisit P u w (cthickening h cert.U)
    · rw [← heq]
      change curveLength (D'.pt ∘ P) u u = curveLength (D.pt ∘ P) u u
      rw [curveLength_self, curveLength_self]
    · have hlt : u < firstVisit P u w (cthickening h cert.U) :=
        hσ₁.1.lt_of_ne heq
      apply q6_weyl_len_zero hW hlt.le
        (hP.mono (Icc_subset_Icc le_rfl hσ₁.2))
      apply q6_f_zero_on_gap cert hlt (hP.mono (Icc_subset_Icc le_rfl hσ₁.2))
      intro r hr hrV
      have hrset : r ∈ {z | z ∈ Icc u w ∧ P z ∈ cthickening h cert.U} :=
        ⟨⟨hr.1.le, hr.2.le.trans hσ₁.2⟩, hrV⟩
      have hbl : BddBelow {z | z ∈ Icc u w ∧ P z ∈ cthickening h cert.U} :=
        ⟨u, fun z hz => hz.1.1⟩
      exact (not_le_of_gt hr.2) (csInf_le hbl hrset)
  · by_cases heq : lastVisit P u w (cthickening h cert.U) = w
    · rw [heq]
      change curveLength (D'.pt ∘ P) w w = curveLength (D.pt ∘ P) w w
      rw [curveLength_self, curveLength_self]
    · have hlt : lastVisit P u w (cthickening h cert.U) < w :=
        hσ₂.2.lt_of_ne heq
      apply q6_weyl_len_zero hW hlt.le
        (hP.mono (Icc_subset_Icc hσ₂.1 le_rfl))
      apply q6_f_zero_on_gap cert hlt (hP.mono (Icc_subset_Icc hσ₂.1 le_rfl))
      intro r hr hrV
      have hrset : r ∈ {z | z ∈ Icc u w ∧ P z ∈ cthickening h cert.U} :=
        ⟨⟨hσ₂.1.trans hr.1.le, hr.2.le⟩, hrV⟩
      have hba : BddAbove {z | z ∈ Icc u w ∧ P z ∈ cthickening h cert.U} :=
        ⟨w, fun z hz => hz.1.2⟩
      exact (not_le_of_gt hr.1) (le_csSup hba hrset)

/-- The nodes whose enlarged sets are met by the collector subpath induce a connected graph. -/
theorem q6_visited_nodes_connected {D E D' : ContMetric d} {f : C(Rd d, ℝ)}
    {ξ M θ h δsep ε₀ εnet εatt aout H b v d₀ : ℝ}
    (cert : ForcingCert D E f ξ M θ h δsep ε₀ εnet εatt aout H b v d₀)
    (hW : IsWeylInternal ξ (-f) D D') (hξ : 0 ≤ ξ)
    (hH : 0 < H) (hb : 0 ≤ b) (hsep : 4 * h ≤ δsep)
    (hbudget : 2 * εatt + εnet < H⁻¹ * (δsep / 2) ^ b)
    {P : ℝ → Rd d} {a c u w : ℝ} (hgeo : IsGeodSeg D' P a c)
    (hau : a ≤ u) (hwc : w ≤ c)
    (hA : ∀ t ∈ Icc u w, P t ∈ siteA d)
    (hvisit : ∃ t ∈ Icc u w, P t ∈ cthickening h cert.U) :
    (cert.adj.induce {n | ∃ t ∈ Icc u w,
      P t ∈ cthickening h cert.U ∩ cthickening h (cert.N n)}).Connected := by
  classical
  let _ : Fintype cert.Node := cert.node_fin
  let V : Set (Rd d) := cthickening h cert.U
  let S : Set cert.Node := {n | ∃ t ∈ Icc u w, P t ∈ V ∩ cthickening h (cert.N n)}
  let G : SimpleGraph S := cert.adj.induce S
  change G.Connected
  obtain ⟨τ, hτ, hτV⟩ := hvisit
  obtain ⟨n₀, hτn⟩ := q6_V_node_cover cert hτV
  have hn₀ : n₀ ∈ S := ⟨τ, hτ, hτV, hτn⟩
  let K : G.ConnectedComponent := G.connectedComponentMk ⟨n₀, hn₀⟩
  let F₁ : Set (Rd d) := V ∩ ⋃ n : S,
    if n ∈ K.supp then cthickening h (cert.N n.1) else ∅
  let F₂ : Set (Rd d) := V ∩ ⋃ n : S,
    if n ∈ K.supp then ∅ else cthickening h (cert.N n.1)
  have hVclosed : IsClosed V := isClosed_cthickening
  have hF₁ : IsClosed F₁ := hVclosed.inter <| isClosed_iUnion_of_finite fun n => by
    split_ifs <;> simp only [isClosed_cthickening, isClosed_empty]
  have hF₂ : IsClosed F₂ := hVclosed.inter <| isClosed_iUnion_of_finite fun n => by
    split_ifs <;> simp only [isClosed_cthickening, isClosed_empty]
  have hδpos : 0 < δsep / 2 := by linarith only [cert.h_pos, hsep]
  have hfar : ∀ x ∈ F₁, ∀ y ∈ F₂, δsep / 2 ≤ dist x y := by
    intro x hx y hy
    obtain ⟨_, hxn⟩ := hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp hxn
    obtain ⟨_, hym⟩ := hy
    obtain ⟨m, hm⟩ := mem_iUnion.mp hym
    have hnK : n ∈ K.supp := by
      by_contra hnot
      simp only [hnot, ↓reduceIte, mem_empty_iff_false] at hn
    have hmK : m ∉ K.supp := by
      intro hmem
      simp only [hmem, ↓reduceIte, mem_empty_iff_false] at hm
    have hnm : n.1 ≠ m.1 := by
      intro heq
      exact hmK (Subtype.ext heq ▸ hnK)
    have hnotadj : ¬ cert.adj.Adj n.1 m.1 := by
      intro hadj
      have hGadj : G.Adj n m := hadj
      exact hmK ((K.mem_supp_congr_adj hGadj).mp hnK)
    exact q6_nonadjacent_sep cert hsep hnm hnotadj
      (by simpa [hnK] using hn) (by simpa [hmK] using hm)
  have hdis : Disjoint F₁ F₂ := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    have := hfar x hx x hy
    rw [dist_self] at this
    exact (not_le_of_gt hδpos) this
  have hcover : ∀ r ∈ Icc u w, P r ∈ V → P r ∈ F₁ ∨ P r ∈ F₂ := by
    intro r hr hrV
    obtain ⟨n, hn⟩ := q6_V_node_cover cert hrV
    have hnS : n ∈ S := ⟨r, hr, hrV, hn⟩
    by_cases hnK : (⟨n, hnS⟩ : S) ∈ K.supp
    · left
      exact ⟨hrV, mem_iUnion.mpr ⟨⟨n, hnS⟩, by simpa [hnK] using hn⟩⟩
    · right
      exact ⟨hrV, mem_iUnion.mpr ⟨⟨n, hnS⟩, by simpa [hnK] using hn⟩⟩
  have hτF₁ : P τ ∈ F₁ := by
    refine ⟨hτV, mem_iUnion.mpr ⟨⟨n₀, hn₀⟩, ?_⟩⟩
    simpa [K] using hτn
  have hEvery : ∀ n : S, n ∈ K.supp := by
    intro n
    by_contra hnK
    obtain ⟨t, ht, htV, htn⟩ := n.2
    have htF₂ : P t ∈ F₂ :=
      ⟨htV, mem_iUnion.mpr ⟨n, by simpa [hnK] using htn⟩⟩
    have hτt : τ ≠ t := by
      intro heq
      exact (Set.disjoint_left.mp hdis) hτF₁ (heq ▸ htF₂)
    have hP : ContinuousOn P (Icc u w) :=
      hgeo.2.1.mono (Icc_subset_Icc hau hwc)
    have hcontra : ∀ {p q : ℝ}, p ∈ Icc u w → q ∈ Icc u w → p < q →
        P p ∈ F₁ → P q ∈ F₂ → False := by
      intro p q hp hq hpq hpF hqF
      obtain ⟨s, t, hps, hst, htq, hsF, htF, hgap⟩ :=
        q6_first_switch_gap hP hF₁ hF₂ hdis hcover hp hq hpq hpF hqF
      have hshort := q6_excursion_short cert hW hξ hH hb hsep hbudget hgeo
        hau (hp.1.trans hps) hst (htq.trans hq.2) hwc hA hsF.1 htF.1 hgap
      have hsep' := hfar (P s) hsF (P t) htF
      rw [dist_eq_norm] at hsep'
      exact (not_le_of_gt hshort) hsep'
    rcases lt_or_gt_of_ne hτt with hlt | hgt
    · exact hcontra hτ ht hlt hτF₁ htF₂
    · obtain ⟨s, t', hts, hst, htτ, hsF, htF, hgap⟩ :=
        q6_first_switch_gap hP hF₂ hF₁ hdis.symm
          (fun r hr hrV => (hcover r hr hrV).symm) ht hτ hgt htF₂ hτF₁
      have hshort := q6_excursion_short cert hW hξ hH hb hsep hbudget hgeo
        hau (ht.1.trans hts) hst (htτ.trans hτ.2) hwc hA hsF.1 htF.1 hgap
      have hsep' := hfar (P t') htF (P s) hsF
      rw [dist_comm, dist_eq_norm] at hsep'
      exact (not_le_of_gt hshort) hsep'
  let _ : Nonempty S := ⟨⟨n₀, hn₀⟩⟩
  refine ⟨?_⟩
  intro n m
  have hnK := hEvery n
  have hmK := hEvery m
  exact SimpleGraph.ConnectedComponent.exact (hnK.trans hmK.symm)

/-- The trigger and star bound force visits to both gates of one chamber. -/
theorem q6_opposite_gates_visited {D E D' : ContMetric d} {f : C(Rd d, ℝ)}
    {ξ M θ h δsep ε₀ εnet εatt aout H b v d₀ btrig : ℝ}
    (cert : ForcingCert D E f ξ M θ h δsep ε₀ εnet εatt aout H b v d₀)
    (hW : IsWeylInternal ξ (-f) D D') (hξ : 0 ≤ ξ)
    (hH : 0 < H) (hb : 0 ≤ b) (hsep : 4 * h ≤ δsep)
    (hbudget : 2 * εatt + εnet < H⁻¹ * (δsep / 2) ^ b)
    (hnet : εnet ≤ ε₀) (htrig : 7 * ε₀ < btrig)
    {P : ℝ → Rd d} {a c u w : ℝ} (hgeo : IsGeodSeg D' P a c)
    (hau : a ≤ u) (huw : u ≤ w) (hwc : w ≤ c)
    (hu : P u ∈ siteC d) (hw : P w ∈ siteC d)
    (hA : ∀ t ∈ Icc u w, P t ∈ siteA d)
    (htrigger : ENNReal.ofReal btrig ≤ D.internal (siteB d) (P u) (P w)) :
    ∃ e : cert.Ch, (∃ s ∈ Icc u w, P s ∈ cthickening h cert.U ∩
      cthickening h (cert.N (cert.gate0 e))) ∧
      (∃ t ∈ Icc u w, P t ∈ cthickening h cert.U ∩
      cthickening h (cert.N (cert.gate1 e))) := by
  classical
  let _ : Fintype cert.Node := cert.node_fin
  let V : Set (Rd d) := cthickening h cert.U
  let S : Set cert.Node := {n | ∃ t ∈ Icc u w, P t ∈ V ∩ cthickening h (cert.N n)}
  have hvisit : ∃ t ∈ Icc u w, P t ∈ V :=
    q6_V_visited cert hW hξ hnet htrig hgeo hau huw hwc hu hw hA htrigger
  have hconn : (cert.adj.induce S).Connected :=
    q6_visited_nodes_connected cert hW hξ hH hb hsep hbudget hgeo hau hwc hA hvisit
  by_contra hno
  have hno' : ∀ e : cert.Ch, ¬ (cert.gate0 e ∈ S ∧ cert.gate1 e ∈ S) := by
    intro e he
    apply hno
    exact ⟨e, he.1, he.2⟩
  obtain ⟨W, hWcover, hdiam⟩ := cert.star S hconn hno'
  have hP : ContinuousOn P (Icc u w) :=
    hgeo.2.1.mono (Icc_subset_Icc hau hwc)
  let σ₁ := firstVisit P u w V
  let σ₂ := lastVisit P u w V
  obtain ⟨hσ₁, hσ₁V, hσ₂, hσ₂V, hσ₁₂⟩ :=
    q6_visit_times hP isClosed_cthickening hvisit
  have hσW : ∀ t ∈ Icc u w, P t ∈ V → P t ∈ W := by
    intro t ht htV
    obtain ⟨n, hn⟩ := q6_V_node_cover cert htV
    have hnS : n ∈ S := ⟨t, ht, htV, hn⟩
    apply hWcover
    exact mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨hnS, hn⟩⟩
  have hmid : D.internal (siteB d) (P σ₁) (P σ₂) ≤ ENNReal.ofReal ε₀ := by
    calc
      D.internal (siteB d) (P σ₁) (P σ₂) ≤
          D.internal (siteA d) (P σ₁) (P σ₂) :=
        D.internal_anti (q6_siteA_subset_B d) _ _
      _ ≤ diamIn D (siteA d) W := by
        unfold diamIn
        exact le_iSup_of_le (P σ₁) <| le_iSup_of_le (hσW σ₁ hσ₁ hσ₁V) <|
          le_iSup_of_le (P σ₂) <| le_iSup_of_le (hσW σ₂ hσ₂ hσ₂V) le_rfl
      _ ≤ ENNReal.ofReal ε₀ := hdiam
  have ⟨htail₁, htail₂⟩ := q6_V_tail_lengths cert hW hP hvisit
  have htailbound₁ : D.internal (siteB d) (P u) (P σ₁) ≤ ENNReal.ofReal (3 * ε₀) := by
    calc
      D.internal (siteB d) (P u) (P σ₁) ≤ D.len P u σ₁ :=
        D.internal_le_len hσ₁.1 (hP.mono (Icc_subset_Icc le_rfl hσ₁.2))
          (fun r hr => q6_siteA_subset_B d (hA r ⟨hr.1, hr.2.trans hσ₁.2⟩))
      _ = D'.len P u σ₁ := htail₁.symm
      _ ≤ D'.len P u w := curveLength_mono _ le_rfl hσ₁.2
      _ ≤ ENNReal.ofReal (3 * ε₀) :=
        q6_geod_collector_short cert hW hξ hnet
          (q6_eps0_pos cert (q6_dim_pos_of_mem_C hu)).le hgeo hau huw hwc hu hw
  have htailbound₂ : D.internal (siteB d) (P σ₂) (P w) ≤ ENNReal.ofReal (3 * ε₀) := by
    calc
      D.internal (siteB d) (P σ₂) (P w) ≤ D.len P σ₂ w :=
        D.internal_le_len hσ₂.2 (hP.mono (Icc_subset_Icc hσ₂.1 le_rfl))
          (fun r hr => q6_siteA_subset_B d (hA r ⟨hσ₂.1.trans hr.1, hr.2⟩))
      _ = D'.len P σ₂ w := htail₂.symm
      _ ≤ D'.len P u w := curveLength_mono _ hσ₂.1 le_rfl
      _ ≤ ENNReal.ofReal (3 * ε₀) :=
        q6_geod_collector_short cert hW hξ hnet
          (q6_eps0_pos cert (q6_dim_pos_of_mem_C hu)).le hgeo hau huw hwc hu hw
  have hε : 0 ≤ ε₀ := (q6_eps0_pos cert (q6_dim_pos_of_mem_C hu)).le
  have hcost : D.internal (siteB d) (P u) (P w) ≤ ENNReal.ofReal (7 * ε₀) := by
    calc
      D.internal (siteB d) (P u) (P w) ≤
          D.internal (siteB d) (P u) (P σ₁) +
            D.internal (siteB d) (P σ₁) (P σ₂) +
            D.internal (siteB d) (P σ₂) (P w) := by
        exact (D.internal_triangle _ _ _ _).trans
          (add_le_add (D.internal_triangle _ _ _ _) le_rfl)
      _ ≤ ENNReal.ofReal (3 * ε₀) + ENNReal.ofReal ε₀ +
          ENNReal.ofReal (3 * ε₀) := by
        exact add_le_add (add_le_add htailbound₁ hmid) htailbound₂
      _ = ENNReal.ofReal (7 * ε₀) := by
        rw [← ENNReal.ofReal_add (by positivity : 0 ≤ 3 * ε₀) hε,
          ← ENNReal.ofReal_add (by positivity : 0 ≤ 3 * ε₀ + ε₀)
            (by positivity : 0 ≤ 3 * ε₀)]
        congr 1
        ring
  have hstrict : ENNReal.ofReal (7 * ε₀) < ENNReal.ofReal btrig :=
    (ENNReal.ofReal_lt_ofReal_iff (by linarith only [htrig, hε])).2 htrig
  exact (not_le_of_gt hstrict) (htrigger.trans hcost)

end HigherDimLQGContinuity
