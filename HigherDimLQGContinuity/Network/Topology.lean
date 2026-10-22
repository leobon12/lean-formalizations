import HigherDimLQGContinuity.Network.Defs

/-! # Topology of the finite ball network -/

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open Set Metric
open HigherDimLFPP (Rd)

namespace HigherDimLQGContinuity

theorem openBallSpecs_isOpen {d : ℕ} (F : Finset (Rd d × ℝ)) :
    IsOpen (openBallSpecs F) := by
  unfold openBallSpecs
  exact isOpen_biUnion fun p _ => isOpen_ball

theorem closedBallSpecs_isClosed {d : ℕ} (F : Finset (Rd d × ℝ)) :
    IsClosed (closedBallSpecs F) := by
  unfold closedBallSpecs
  exact isClosed_biUnion_finset fun p _ => isClosed_closedBall

theorem openBallSpecs_subset_closed {d : ℕ} (F : Finset (Rd d × ℝ)) :
    openBallSpecs F ⊆ closedBallSpecs F := by
  intro x hx
  obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.mp hx
  exact mem_iUnion₂.mpr ⟨p, hp, ball_subset_closedBall hxp⟩

theorem openBallSpecs_union {d : ℕ} (F G : Finset (Rd d × ℝ)) :
    openBallSpecs (F ∪ G) = openBallSpecs F ∪ openBallSpecs G := by
  ext x
  simp only [openBallSpecs, mem_iUnion, Finset.mem_union]
  aesop

theorem openBallSpecs_image {d : ℕ} {ι : Type*} (Q : Finset ι)
    (c : ι → Rd d) (g : ℝ) :
    openBallSpecs (Q.image fun i => (c i, g)) =
      ⋃ i ∈ Q, ball (c i) g := by
  ext x
  simp only [openBallSpecs, mem_iUnion, Finset.mem_image]
  aesop

theorem openBallSpecs_biUnion {d : ℕ} {ι : Type*} (Q : Finset ι)
    (F : ι → Finset (Rd d × ℝ)) :
    openBallSpecs (Q.biUnion F) = ⋃ i ∈ Q, openBallSpecs (F i) := by
  ext x
  simp only [openBallSpecs, mem_iUnion, Finset.mem_biUnion]
  aesop

theorem closedBallSpecs_union {d : ℕ} (F G : Finset (Rd d × ℝ)) :
    closedBallSpecs (F ∪ G) = closedBallSpecs F ∪ closedBallSpecs G := by
  ext x
  simp only [closedBallSpecs, mem_iUnion, Finset.mem_union]
  aesop

theorem closedBallSpecs_image {d : ℕ} {ι : Type*} (Q : Finset ι)
    (c : ι → Rd d) (g : ℝ) :
    closedBallSpecs (Q.image fun i => (c i, g)) =
      ⋃ i ∈ Q, closedBall (c i) g := by
  ext x
  simp only [closedBallSpecs, mem_iUnion, Finset.mem_image]
  aesop

theorem closedBallSpecs_biUnion {d : ℕ} {ι : Type*} (Q : Finset ι)
    (F : ι → Finset (Rd d × ℝ)) :
    closedBallSpecs (Q.biUnion F) = ⋃ i ∈ Q, closedBallSpecs (F i) := by
  ext x
  simp only [closedBallSpecs, mem_iUnion, Finset.mem_biUnion]
  aesop

theorem closure_openBallSpecs {d : ℕ} (F : Finset (Rd d × ℝ))
    (hF : ∀ p ∈ F, 0 < p.2) :
    closure (openBallSpecs F) = closedBallSpecs F := by
  unfold openBallSpecs closedBallSpecs
  rw [F.closure_biUnion]
  ext x
  constructor
  · intro hx
    obtain ⟨p, hp, hx⟩ := mem_iUnion₂.mp hx
    rw [closure_ball p.1 (ne_of_gt (hF p hp))] at hx
    exact mem_iUnion₂.mpr ⟨p, hp, hx⟩
  · intro hx
    obtain ⟨p, hp, hx⟩ := mem_iUnion₂.mp hx
    have hx' : x ∈ closure (ball p.1 p.2) := by
      rw [closure_ball p.1 (ne_of_gt (hF p hp))]
      exact hx
    exact mem_iUnion₂.mpr ⟨p, hp, hx'⟩

theorem labelNet_isOpen {d : ℕ} (S : SiteData d) (C : SiteConsts)
    {Kc Kl : ℕ}
    (ℓ : SiteLabel S Kc Kl C.N C.μ C.ν C.r (Routing.gpC1 4)) :
    IsOpen (labelNet S C ℓ).Uo :=
  openBallSpecs_isOpen _

theorem labelNet_isClosed {d : ℕ} (S : SiteData d) (C : SiteConsts)
    {Kc Kl : ℕ}
    (ℓ : SiteLabel S Kc Kl C.N C.μ C.ν C.r (Routing.gpC1 4)) :
    IsClosed (labelNet S C ℓ).U :=
  closedBallSpecs_isClosed _

theorem labelNet_Uo_subset_U {d : ℕ} (S : SiteData d) (C : SiteConsts)
    {Kc Kl : ℕ}
    (ℓ : SiteLabel S Kc Kl C.N C.μ C.ν C.r (Routing.gpC1 4)) :
    (labelNet S C ℓ).Uo ⊆ (labelNet S C ℓ).U :=
  openBallSpecs_subset_closed _

theorem edgeBallSpecs_radius {d Kc Kl N : ℕ} {S : SiteData d}
    {μ ν r c₁ g ω : ℝ} (ℓ : SiteLabel S Kc Kl N μ ν r c₁)
    (e : S.Edge) {p : Rd d × ℝ} (hp : p ∈ edgeBallSpecs ℓ e g ω) :
    p.2 = g ∨ p.2 = ω := by
  simp only [edgeBallSpecs, Finset.mem_union, Finset.mem_image] at hp
  aesop

theorem labelBallSpecs_radius_pos {d Kc Kl N : ℕ} {S : SiteData d}
    {μ ν r c₁ g ω : ℝ} (ℓ : SiteLabel S Kc Kl N μ ν r c₁)
    (hg : 0 < g) (hω : 0 < ω) :
    ∀ p ∈ labelBallSpecs ℓ g ω, 0 < p.2 := by
  intro p hp
  simp only [labelBallSpecs, Finset.mem_biUnion] at hp
  obtain ⟨e, _, hpe⟩ := hp
  rcases edgeBallSpecs_radius ℓ e hpe with h | h
  · simpa only [h] using hg
  · simpa only [h] using hω

theorem labelNet_closure {d : ℕ} (S : SiteData d) (C : SiteConsts)
    {Kc Kl : ℕ}
    (ℓ : SiteLabel S Kc Kl C.N C.μ C.ν C.r (Routing.gpC1 4))
    (hg : 0 < C.g) (hω : 0 < C.ω) :
    closure (labelNet S C ℓ).Uo = (labelNet S C ℓ).U := by
  exact closure_openBallSpecs _ (labelBallSpecs_radius_pos ℓ hg hω)

/-- A point in the closed `h` collar of the closure of an open core is less
than `2h` from an interior point. -/
theorem near_open_core_of_closure {d : ℕ}
    {Uo U : Set (Rd d)} {h : ℝ} (hh : 0 < h)
    (hclosure : closure Uo = U)
    {x : Rd d} (hx : x ∈ Metric.cthickening h U) :
    ∃ y ∈ Uo, dist x y ≤ 2 * h := by
  have hbig : h < 3 * h / 2 := by linarith
  have hbigpos : 0 < 3 * h / 2 := by linarith
  obtain ⟨u, hu, hxu⟩ := mem_iUnion₂.mp
    (Metric.cthickening_subset_iUnion_closedBall_of_lt U hbigpos hbig hx)
  have hucl : u ∈ closure Uo := by simpa only [hclosure] using hu
  obtain ⟨y, hy, huy⟩ := Metric.mem_closure_iff.mp hucl (h / 2) (by linarith)
  refine ⟨y, hy, ?_⟩
  have htri := dist_triangle x u y
  have hxu' : dist x u ≤ 3 * h / 2 := mem_closedBall.mp hxu
  linarith

theorem labelNet_near_Uo {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    (Cnet v : ℝ) (hCnet : 0 < Cnet) (hv : 0 < v) (hv1 : v ≤ 1)
    {Kc Kl : ℕ}
    (ℓ : SiteLabel S Kc Kl (siteConsts S Cnet v).N
      (siteConsts S Cnet v).μ (siteConsts S Cnet v).ν
      (siteConsts S Cnet v).r (Routing.gpC1 4))
    {x : Rd d}
    (hx : x ∈ Metric.cthickening (siteConsts S Cnet v).ς
      (labelNet S (siteConsts S Cnet v) ℓ).U) :
    ∃ y ∈ (labelNet S (siteConsts S Cnet v) ℓ).Uo,
      dist x y ≤ 2 * (siteConsts S Cnet v).ς := by
  let C := siteConsts S Cnet v
  have hν : 0 < C.ν := siteConsts_ν_pos S hd Cnet v
  have hω : 0 < C.ω := by
    change 0 < siteOmegaCoeff d * C.ν ^ 4
    exact mul_pos (siteOmegaCoeff_pos d (by omega)) (pow_pos hν _)
  have hg : 0 < C.g := by
    change 0 < 100 * d * C.ν
    positivity
  exact near_open_core_of_closure
    (siteConsts_varsigma_pos S hd Cnet v hCnet hv hv1)
    (labelNet_closure S C ℓ hg hω) hx

/-- A connected skeleton covered by the balls, with each ball meeting it,
makes the finite open-ball union connected. This avoids enumerating edges of
the overlap graph. -/
theorem connected_openBallSpecs_of_skeleton {d : ℕ}
    (F : Finset (Rd d × ℝ)) (S : Set (Rd d))
    (hS : IsConnected S) (hcover : S ⊆ openBallSpecs F)
    (hpos : ∀ p ∈ F, 0 < p.2)
    (hmeet : ∀ p ∈ F, (S ∩ ball p.1 p.2).Nonempty) :
    IsConnected (openBallSpecs F) := by
  have haux : ∀ F' : Finset (Rd d × ℝ), F' ⊆ F →
      IsConnected (S ∪ openBallSpecs F') := by
    intro F'
    induction F' using Finset.induction_on with
    | empty =>
        intro _
        simpa [openBallSpecs] using hS
    | @insert p T hp ih =>
        intro hTF
        have hpF : p ∈ F := hTF (Finset.mem_insert_self _ _)
        have hsub : T ⊆ F := (Finset.subset_insert _ _).trans hTF
        have hT := ih hsub
        have hinter : ((S ∪ openBallSpecs T) ∩ ball p.1 p.2).Nonempty := by
          obtain ⟨x, hxS, hxB⟩ := hmeet p hpF
          exact ⟨x, ⟨Or.inl hxS, hxB⟩⟩
        have hconn := IsConnected.union hinter hT (isConnected_ball (hpos p hpF))
        simpa only [openBallSpecs, Finset.set_biUnion_insert,
          union_assoc, union_left_comm, union_comm] using hconn
  have hEq : S ∪ openBallSpecs F = openBallSpecs F := union_eq_self_of_subset_left hcover
  rw [← hEq]
  exact haux F (Finset.Subset.refl F)

/-- Topological connectedness of a finite open-ball union implies graph
connectedness of its overlap graph. -/
theorem overlapGraph_connected_of_openBallSpecs_connected {d : ℕ}
    (F : Finset (Rd d × ℝ)) (hF : F.Nonempty)
    (hpos : ∀ p ∈ F, 0 < p.2)
    (hconn : IsConnected (openBallSpecs F)) :
    (SimpleGraph.fromRel (fun p q : F =>
      (ball p.1.1 p.1.2 ∩ ball q.1.1 q.1.2).Nonempty)).Connected := by
  let s : F → Set (Rd d) := fun p => ball p.1.1 p.1.2
  let G : SimpleGraph F := SimpleGraph.fromRel
    (fun p q : F => (s p ∩ s q).Nonempty)
  have hU : (⋃ p : F, s p) = openBallSpecs F := by
    ext x
    simp only [s, openBallSpecs, mem_iUnion, Subtype.exists]
  have hpre : IsPreconnected (⋃ p : F, s p) := by
    rw [hU]
    exact hconn.isPreconnected
  have hstep : ∀ p q : F, (s p ∩ s q).Nonempty → G.Reachable p q := by
    intro p q hpq
    by_cases heq : p = q
    · subst q
      rfl
    · exact ⟨SimpleGraph.Walk.cons
        ((SimpleGraph.fromRel_adj _ _ _).2 ⟨heq, Or.inl hpq⟩)
          SimpleGraph.Walk.nil⟩
  have hreach : ∀ p q : F, G.Reachable p q := by
    intro p q
    have hp : (s p).Nonempty := nonempty_ball.mpr (hpos p p.2)
    have hq : (s q).Nonempty := nonempty_ball.mpr (hpos q q.2)
    have hpath := hpre.transGen_of_iUnion (fun _ => isOpen_ball) p q hp hq
    induction hpath with
    | single h => exact hstep _ _ h
    | tail _ h ih =>
        exact (ih ⟨h.choose, h.choose_spec.1⟩).trans (hstep _ _ h)
  haveI : Nonempty F := ⟨⟨hF.choose, hF.choose_spec⟩⟩
  exact ⟨hreach⟩

/-- Indexed version of the connected-skeleton criterion. -/
theorem connected_indexed_ballUnion_of_skeleton {d : ℕ} {ι : Type*}
    (Q : Finset ι) (c : ι → Rd d) (g : ℝ) (S : Set (Rd d))
    (hS : IsConnected S)
    (hcover : S ⊆ ⋃ i ∈ Q, ball (c i) g)
    (hg : 0 < g)
    (hmeet : ∀ i ∈ Q, (S ∩ ball (c i) g).Nonempty) :
    IsConnected (⋃ i ∈ Q, ball (c i) g) := by
  classical
  let F : Finset (Rd d × ℝ) := Q.image fun i => (c i, g)
  have hEq : openBallSpecs F = ⋃ i ∈ Q, ball (c i) g := by
    ext x
    simp only [openBallSpecs, F, mem_iUnion, Finset.mem_image]
    aesop
  have hpos : ∀ p ∈ F, 0 < p.2 := by
    intro p hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    exact hg
  have hmeetF : ∀ p ∈ F, (S ∩ ball p.1 p.2).Nonempty := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    exact hmeet i hi
  rw [← hEq] at hcover ⊢
  exact connected_openBallSpecs_of_skeleton F S hS hcover hpos hmeetF

end HigherDimLQGContinuity
