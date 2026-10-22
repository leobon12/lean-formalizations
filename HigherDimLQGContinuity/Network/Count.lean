import HigherDimLQGContinuity.Network.Bounds
import HigherDimLQGContinuity.Network.Catalogue

/-! # Counting the balls in a site network -/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 400000

noncomputable section

open Set Metric
open HigherDimLFPP (Rd)
open HigherDimLQGMetric (annCl)

namespace HigherDimLQGContinuity

theorem segmentSamples_card_le {d : ℕ} (a b : Rd d) (ω : ℝ) :
    (segmentSamples a b ω).card ≤ segmentSampleCount a b ω + 1 := by
  classical
  unfold segmentSamples
  exact Finset.card_image_le.trans_eq (Finset.card_range _)

theorem segmentSampleCount_le_of_dist_le {d : ℕ} {a b : Rd d}
    {ω R : ℝ} (hω : 0 < ω)
    (hab : dist a b ≤ R) :
    segmentSampleCount a b ω ≤ max 1 ⌈100 * R / ω⌉₊ := by
  unfold segmentSampleCount
  exact max_le_max le_rfl (Nat.ceil_mono (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hab (by norm_num)) hω.le))

theorem segmentSamples_card_le_of_dist_le {d : ℕ} {a b : Rd d}
    {ω R : ℝ} (hω : 0 < ω)
    (hab : dist a b ≤ R) :
    (segmentSamples a b ω).card ≤ max 1 ⌈100 * R / ω⌉₊ + 1 :=
  (segmentSamples_card_le a b ω).trans
    (Nat.add_le_add_right (segmentSampleCount_le_of_dist_le hω hab) 1)

theorem siteC_dist_le_five {d : ℕ} {x y : Rd d}
    (hx : x ∈ siteC d) (hy : y ∈ siteC d) : dist x y ≤ 5 := by
  have hxnorm : ‖x‖ ≤ 5 / 2 := by
    simpa only [siteC, annCl, mem_ofPred_eq, sub_zero] using hx.2
  have hynorm : ‖y‖ ≤ 5 / 2 := by
    simpa only [siteC, annCl, mem_ofPred_eq, sub_zero] using hy.2
  calc
    dist x y = ‖x - y‖ := dist_eq_norm x y
    _ ≤ ‖x‖ + ‖y‖ := norm_sub_le x y
    _ ≤ 5 := by linarith

theorem leadSamples_card_le {d Kl N : ℕ} (P : LeadCode d Kl N)
    {ν ω R : ℝ} (hω : 0 < ω)
    (hbound : ∀ j : Fin N, j.val < P.last.val →
      dist (P.point ν j.castSucc) (P.point ν j.succ) ≤ R) :
    (leadSamples P ν ω).card ≤
      N * (max 1 ⌈100 * R / ω⌉₊ + 1) := by
  classical
  let Q := Finset.univ.filter fun j : Fin N => j.val < P.last.val
  let M := max 1 ⌈100 * R / ω⌉₊ + 1
  change (Q.biUnion fun j =>
    segmentSamples (P.point ν j.castSucc) (P.point ν j.succ) ω).card ≤ N * M
  calc
    _ ≤ ∑ j ∈ Q,
        (segmentSamples (P.point ν j.castSucc) (P.point ν j.succ) ω).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _j ∈ Q, M := by
      apply Finset.sum_le_sum
      intro j hj
      exact segmentSamples_card_le_of_dist_le hω
        (hbound j (Finset.mem_filter.mp hj).2)
    _ = Q.card * M := by simp
    _ ≤ N * M := by
      exact Nat.mul_le_mul_right M (by
        simpa [Q] using
          (Finset.card_filter_le (Finset.univ : Finset (Fin N))
            (fun j => j.val < P.last.val)))

theorem vertexPoint_mem_siteC {d : ℕ} (S : SiteData d)
    (hd : 2 ≤ d) (v : S.Vertex) : S.vertexPoint v ∈ siteC d := by
  have hb := (siteMesh_geometry S hd).vertex_bounds v
  simp only [siteC, annCl, mem_ofPred_eq, sub_zero]
  have hδ : 0 ≤ Real.sqrt d * S.mesh.δm :=
    mul_nonneg (Real.sqrt_nonneg _) S.mesh.δm_pos.le
  constructor <;> linarith

theorem leadSamples_card_le_site {d Kl N : ℕ} (S : SiteData d)
    (hd : 2 ≤ d) (e : S.Edge) (P : LeadCode d Kl N)
    {ν r c₁ ω : ℝ} {p : Rd d}
    (hω : 0 < ω)
    (hP : P.Geometry ν r c₁ (S.edgeCenter e) S.boxHalfSide p) :
    (leadSamples P ν ω).card ≤
      N * (max 1 ⌈500 / ω⌉₊ + 1) := by
  convert leadSamples_card_le (R := 5) P hω ?_ using 1 <;> norm_num
  intro j hj
  have hj₀ : j.castSucc ≤ P.last :=
    Fin.le_def.mpr (by simpa using Nat.le_of_lt hj)
  have hj₁ : j.succ ≤ P.last :=
    Fin.le_def.mpr (by simpa using hj)
  have ha : P.point ν j.castSucc ∈ siteC d :=
    interior_subset (S.box_subset_interior_C hd e (hP.2.2.1 j.castSucc hj₀).1)
  have hb : P.point ν j.succ ∈ siteC d :=
    interior_subset (S.box_subset_interior_C hd e (hP.2.2.1 j.succ hj₁).1)
  exact siteC_dist_le_five ha hb

theorem edgeRetainedSamples_card_le_site {d Kc Kl N : ℕ}
    (S : SiteData d) (hd : 2 ≤ d)
    {μ ν r c₁ ω : ℝ} (hω : 0 < ω)
    (ℓ : SiteLabel S Kc Kl N μ ν r c₁) (e : S.Edge) (i : Fin 2) :
    (edgeRetainedSamples ℓ e i ω).card ≤
      max 1 ⌈500 / ω⌉₊ + 1 := by
  have ha : S.vertexPoint (S.retainedVertex e i) ∈ siteC d :=
    vertexPoint_mem_siteC S hd _
  have hb : S.port e i ∈ siteC d :=
    interior_subset (S.box_subset_interior_C hd e (S.port_mem_box hd e i))
  simpa only [edgeRetainedSamples,
    show (100 : ℝ) * 5 = 500 by norm_num] using
    segmentSamples_card_le_of_dist_le hω (siteC_dist_le_five ha hb)

theorem q4_card_seven_union_le {α : Type*} [DecidableEq α]
    (A B C D E F G : Finset α) :
    (A ∪ B ∪ C ∪ D ∪ E ∪ F ∪ G).card ≤
      A.card + B.card + C.card + D.card + E.card + F.card + G.card := by
  have h1 := Finset.card_union_le A B
  have h2 := Finset.card_union_le (A ∪ B) C
  have h3 := Finset.card_union_le (A ∪ B ∪ C) D
  have h4 := Finset.card_union_le (A ∪ B ∪ C ∪ D) E
  have h5 := Finset.card_union_le (A ∪ B ∪ C ∪ D ∪ E) F
  have h6 := Finset.card_union_le (A ∪ B ∪ C ∪ D ∪ E ∪ F) G
  omega

theorem labelCellIndices_card_le {d K : ℕ}
    (Q : Finset (LabelIndex d K)) :
    (labelCellIndices Q).card ≤ (2 * K + 1) ^ d := by
  classical
  calc
    (labelCellIndices Q).card ≤ Q.card := Finset.card_image_le
    _ ≤ Fintype.card (LabelIndex d K) := Finset.card_le_univ Q
    _ = (2 * K + 1) ^ d := by
      exact labelIndex_card d K

theorem edgeBallSpecs_card_le {d Kc Kl N : ℕ}
    (S : SiteData d) (hd : 2 ≤ d)
    {μ ν r c₁ g ω : ℝ} (hω : 0 < ω)
    (ℓ : SiteLabel S Kc Kl N μ ν r c₁) (e : S.Edge) :
    (edgeBallSpecs ℓ e g ω).card ≤
      3 * (2 * Kc + 1) ^ d + (2 + 2 * N) * (max 1 ⌈500 / ω⌉₊ + 1) := by
  classical
  let M := max 1 ⌈500 / ω⌉₊ + 1
  let B := (2 * Kc + 1) ^ d
  have hch : (edgeChamberSites ℓ e).card ≤ B := by
    exact Finset.card_image_le.trans
      (labelCellIndices_card_le (ℓ e).1.chamber)
  have hg0 : (edgeGateSites ℓ e 0).card ≤ B := by
    exact Finset.card_image_le.trans
      (labelCellIndices_card_le (ℓ e).1.gate0)
  have hg1 : (edgeGateSites ℓ e 1).card ≤ B := by
    exact Finset.card_image_le.trans
      (labelCellIndices_card_le (ℓ e).1.gate1)
  have hr0 := edgeRetainedSamples_card_le_site S hd hω ℓ e 0
  have hr1 := edgeRetainedSamples_card_le_site S hd hω ℓ e 1
  have hl0 := leadSamples_card_le_site S hd e (ℓ e).1.lead0
    hω (ℓ e).2.2.2.2.1
  have hl1 := leadSamples_card_le_site S hd e (ℓ e).1.lead1
    hω (ℓ e).2.2.2.2.2.1
  change (edgeLeadSamples ℓ e 0 ω).card ≤ N * M at hl0
  change (edgeLeadSamples ℓ e 1 ω).card ≤ N * M at hl1
  have hsum := q4_card_seven_union_le
    ((edgeChamberSites ℓ e).image fun x => (x, ω))
    ((edgeGateSites ℓ e 0).image fun x => (x, g))
    ((edgeGateSites ℓ e 1).image fun x => (x, g))
    ((edgeRetainedSamples ℓ e 0 ω).image fun x => (x, ω))
    ((edgeRetainedSamples ℓ e 1 ω).image fun x => (x, ω))
    ((edgeLeadSamples ℓ e 0 ω).image fun x => (x, ω))
    ((edgeLeadSamples ℓ e 1 ω).image fun x => (x, ω))
  have himage := Finset.card_image_le
    (s := edgeChamberSites ℓ e) (f := fun x => (x, ω))
  have himage0 := Finset.card_image_le
    (s := edgeGateSites ℓ e 0) (f := fun x => (x, g))
  have himage1 := Finset.card_image_le
    (s := edgeGateSites ℓ e 1) (f := fun x => (x, g))
  have hir0 := Finset.card_image_le
    (s := edgeRetainedSamples ℓ e 0 ω) (f := fun x => (x, ω))
  have hir1 := Finset.card_image_le
    (s := edgeRetainedSamples ℓ e 1 ω) (f := fun x => (x, ω))
  have hil0 := Finset.card_image_le
    (s := edgeLeadSamples ℓ e 0 ω) (f := fun x => (x, ω))
  have hil1 := Finset.card_image_le
    (s := edgeLeadSamples ℓ e 1 ω) (f := fun x => (x, ω))
  change (edgeBallSpecs ℓ e g ω).card ≤ _ at hsum
  have hcount : (edgeBallSpecs ℓ e g ω).card ≤
      3 * B + 2 * M + 2 * (N * M) := by omega
  calc
    (edgeBallSpecs ℓ e g ω).card ≤ 3 * B + 2 * M + 2 * (N * M) := hcount
    _ = 3 * B + (2 + 2 * N) * M := by ring

theorem labelBallSpecs_card_le {d Kc Kl N : ℕ}
    (S : SiteData d) (hd : 2 ≤ d)
    {μ ν r c₁ g ω : ℝ} (hω : 0 < ω)
    (ℓ : SiteLabel S Kc Kl N μ ν r c₁) :
    (labelBallSpecs ℓ g ω).card ≤
      Nat.card S.Edge *
        (3 * (2 * Kc + 1) ^ d +
          (2 + 2 * N) * (max 1 ⌈500 / ω⌉₊ + 1)) := by
  classical
  letI : Fintype S.Vertex := (siteMesh_vertices_finite S.mesh.δm_pos).fintype
  letI : Fintype S.Edge := Fintype.ofFinite S.Edge
  let B := 3 * (2 * Kc + 1) ^ d +
    (2 + 2 * N) * (max 1 ⌈500 / ω⌉₊ + 1)
  change (Finset.univ.biUnion fun e : S.Edge => edgeBallSpecs ℓ e g ω).card ≤
    Nat.card S.Edge * B
  calc
    _ ≤ ∑ e : S.Edge, (edgeBallSpecs ℓ e g ω).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _e : S.Edge, B := by
      apply Finset.sum_le_sum
      intro e _
      exact edgeBallSpecs_card_le S hd hω ℓ e
    _ = Nat.card S.Edge * B := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Nat.card_eq_fintype_card]
      rfl

/-- A ceiling cutoff controlled by an inverse power of the mesh scale. -/
theorem q4_cutoff_le_invpow {B a c ν : ℝ} {k : ℕ}
    (hB : 0 ≤ B) (hc : 0 < c) (hν : 0 < ν) (hν1 : ν ≤ 1)
    (ha : c * ν ^ k ≤ a) :
    ((⌈B / a⌉₊ + 2 : ℕ) : ℝ) ≤
      (B / c + 3) * (ν⁻¹) ^ k := by
  have hνk : 0 < ν ^ k := pow_pos hν _
  have ha0 : 0 < a := lt_of_lt_of_le (mul_pos hc hνk) ha
  have hx : 1 ≤ ν⁻¹ := (one_le_inv₀ hν).2 hν1
  have hxk : 1 ≤ (ν⁻¹) ^ k := one_le_pow₀ hx
  have hceil : (⌈B / a⌉₊ : ℝ) < B / a + 1 :=
    Nat.ceil_lt_add_one (div_nonneg hB ha0.le)
  have hInv : a⁻¹ ≤ c⁻¹ * (ν⁻¹) ^ k := by
    have hraw : a⁻¹ ≤ (c * ν ^ k)⁻¹ := by
      simpa only [one_div] using
        (one_div_le_one_div_of_le (mul_pos hc hνk) ha)
    rw [mul_inv_rev, ← inv_pow] at hraw
    simpa only [mul_comm] using hraw
  have hBdiv : B / a ≤ (B / c) * (ν⁻¹) ^ k := by
    calc
      B / a = B * a⁻¹ := by ring
      _ ≤ B * (c⁻¹ * (ν⁻¹) ^ k) :=
        mul_le_mul_of_nonneg_left hInv hB
      _ = (B / c) * (ν⁻¹) ^ k := by ring
  push_cast
  nlinarith

end HigherDimLQGContinuity
