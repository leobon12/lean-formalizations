import HigherDimLQGContinuity.Network.Star
import HigherDimLQGContinuity.Labels.LeadChamber

/-! # Geometric separation of thickened pieces -/

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open Set Metric
open HigherDimLFPP (Rd)

namespace HigherDimLQGContinuity

variable {μ ν r c₁ : ℝ}

theorem dist_ge_of_two_cthickenings {d : ℕ} {A B : Set (Rd d)}
    {r ε η : ℝ} (hε : 0 ≤ ε) (hη : 0 ≤ η)
    (hsep : ∀ a ∈ A, ∀ b ∈ B, r ≤ dist a b)
    {x y : Rd d}
    (hx : x ∈ cthickening ε A) (hy : y ∈ cthickening η B) :
    r - ε - η ≤ dist x y := by
  apply le_of_forall_pos_le_add
  intro δ hδ
  have hδ2 : 0 < δ / 2 := by linarith
  have hnearA : x ∈ ⋃ a ∈ A, closedBall a (ε + δ / 2) :=
    (cthickening_subset_iUnion_closedBall_of_lt A (by linarith) (by linarith)) hx
  have hnearB : y ∈ ⋃ b ∈ B, closedBall b (η + δ / 2) :=
    (cthickening_subset_iUnion_closedBall_of_lt B (by linarith) (by linarith)) hy
  obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.mp hnearA
  obtain ⟨b, hb, hyb⟩ := mem_iUnion₂.mp hnearB
  have hax : dist a x ≤ ε + δ / 2 := by
    rw [dist_comm]; exact mem_closedBall.mp hxa
  have hyb' : dist y b ≤ η + δ / 2 := mem_closedBall.mp hyb
  have htri : dist a b ≤ dist a x + dist x y + dist y b := by
    calc
      dist a b ≤ dist a x + dist x b := dist_triangle _ _ _
      _ ≤ dist a x + (dist x y + dist y b) :=
        by linarith [dist_triangle x y b]
      _ = dist a x + dist x y + dist y b := by ring
  linarith [hsep a ha b hb]

theorem closedBallSpecs_image_subset_cthickening {d : ℕ}
    (Q : Finset (Rd d)) (r : ℝ) :
    closedBallSpecs (Q.image fun z => (z, r)) ⊆
      cthickening r (↑Q : Set (Rd d)) := by
  intro x hx
  obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.mp hx
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hp
  exact mem_cthickening_of_dist_le x z r _ hz (mem_closedBall.mp hxp)

theorem leadSamples_subset_trace {d Kl N : ℕ}
    (P : LeadCode d Kl N) (ν ω : ℝ) :
    (↑(leadSamples P ν ω) : Set (Rd d)) ⊆ P.trace ν := by
  intro x hx
  obtain ⟨j, hj, hxj⟩ := Finset.mem_biUnion.mp hx
  have hj' := (Finset.mem_filter.mp hj).2
  have hseg := segmentSamples_subset_segment
    (P.point ν j.castSucc) (P.point ν j.succ) ω hxj
  exact mem_iUnion.mpr ⟨j, by simpa [LeadCode.trace, hj'] using hseg⟩

theorem edgeLeadClosed_subset_trace_thickening {d Kc Kl N : ℕ}
    {S : SiteData d} (ℓ : SiteLabel S Kc Kl N μ ν r c₁)
    (e : S.Edge) (i : Fin 2) (ω : ℝ) :
    edgeLeadClosed ℓ e i ω ⊆
      cthickening ω
        (if i = 0 then (ℓ e).1.lead0.trace ν else (ℓ e).1.lead1.trace ν) := by
  have hbase := closedBallSpecs_image_subset_cthickening
    (edgeLeadSamples ℓ e i ω) ω
  have htrace : (↑(edgeLeadSamples ℓ e i ω) : Set (Rd d)) ⊆
      (if i = 0 then (ℓ e).1.lead0.trace ν else (ℓ e).1.lead1.trace ν) := by
    fin_cases i
    · exact leadSamples_subset_trace (ℓ e).1.lead0 ν ω
    · exact leadSamples_subset_trace (ℓ e).1.lead1 ν ω
  simpa only [edgeLeadClosed, closedBallSpecs_image] using
    hbase.trans (cthickening_subset_of_subset ω htrace)

theorem edgeRetainedClosed_subset_retained_thickening {d Kc Kl N : ℕ}
    {S : SiteData d} (ℓ : SiteLabel S Kc Kl N μ ν r c₁)
    (e : S.Edge) (i : Fin 2) (ω : ℝ) :
    edgeRetainedClosed ℓ e i ω ⊆ cthickening ω (S.retained e i) := by
  have hbase := closedBallSpecs_image_subset_cthickening
    (edgeRetainedSamples ℓ e i ω) ω
  have hret : (↑(edgeRetainedSamples ℓ e i ω) : Set (Rd d)) ⊆
      S.retained e i := by
    intro x hx
    have hseg := segmentSamples_subset_segment
      (S.vertexPoint (S.retainedVertex e i)) (S.port e i) ω hx
    fin_cases i
    · simpa [SiteData.retained, SiteData.retainedVertex] using hseg
    · simpa [SiteData.retained, SiteData.retainedVertex, segment_symm] using hseg
  simpa only [edgeRetainedClosed, closedBallSpecs_image] using
    hbase.trans (cthickening_subset_of_subset ω hret)

theorem edgeChamberClosed_subset_box_thickening {d Kc Kl N : ℕ}
    {S : SiteData d} {μ ν r c₁ ω : ℝ} (hμ : 0 ≤ μ)
    (ℓ : SiteLabel S Kc Kl N μ ν r c₁) (e : S.Edge) :
    edgeChamberClosed ℓ ω e ⊆ cthickening ω (S.box e) := by
  have hbase := closedBallSpecs_image_subset_cthickening
    (edgeChamberSites ℓ e) ω
  have hbox := (edgeCellSites_subset_box hμ ℓ e).1
  simpa only [edgeChamberClosed] using
    hbase.trans (cthickening_subset_of_subset ω hbox)

theorem edgeGateClosed_subset_box_thickening {d Kc Kl N : ℕ}
    {S : SiteData d} {μ ν r c₁ g : ℝ} (hμ : 0 ≤ μ)
    (ℓ : SiteLabel S Kc Kl N μ ν r c₁) (e : S.Edge) (i : Fin 2) :
    edgeGateClosed ℓ e i g ⊆ cthickening g (S.box e) := by
  have hbase := closedBallSpecs_image_subset_cthickening
    (edgeGateSites ℓ e i) g
  have hbox := (edgeCellSites_subset_box hμ ℓ e).2 i
  simpa only [edgeGateClosed, ballUnion, edgeGateSites,
    closedBallSpecs_image, Finset.image_image, Function.comp_def] using
    hbase.trans (cthickening_subset_of_subset g hbox)

theorem edgeLeadClosed_subset_box_thickening {d Kc Kl N : ℕ}
    {S : SiteData d} (ℓ : SiteLabel S Kc Kl N μ ν r c₁)
    (e : S.Edge) (i : Fin 2) (ω : ℝ) :
    edgeLeadClosed ℓ e i ω ⊆ cthickening ω (S.box e) := by
  have hbase := closedBallSpecs_image_subset_cthickening
    (edgeLeadSamples ℓ e i ω) ω
  have hbox := edgeLeadSamples_subset_box ℓ e i ω
  simpa only [edgeLeadClosed, closedBallSpecs_image] using
    hbase.trans (cthickening_subset_of_subset ω hbox)

/-- A covered gate or chamber ball is close to a point of its realizing arc. -/
theorem ballUnion_subset_hit_thickening {d : ℕ} {μ g : ℝ}
    (hμ : 0 ≤ μ) (o : Rd d) (Q : Finset (Fin d → ℤ))
    (A : Set (Rd d)) (hQ : CoveredHit μ o Q A) :
    ballUnion μ o Q g ⊆
      cthickening (g + Real.sqrt d / 2 * μ) A := by
  intro x hx
  obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp hx
  obtain ⟨z, hzA, hzk⟩ := hQ.2 k hk
  have hzc : dist z (cellCenter μ o k) ≤ Real.sqrt d / 2 * μ :=
    mem_closedBall.mp (cell_subset_closedBall hμ o k hzk)
  have htri := dist_triangle x (cellCenter μ o k) z
  have hxc := mem_closedBall.mp hxk
  apply mem_cthickening_of_dist_le x z _ _ hzA
  rw [dist_comm z (cellCenter μ o k)] at hzc
  linarith

end HigherDimLQGContinuity
