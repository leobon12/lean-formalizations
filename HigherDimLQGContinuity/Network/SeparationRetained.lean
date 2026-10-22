import HigherDimLQGContinuity.Network.SeparationGate

/-! # Projection bound at the face of an axis aligned reserved box -/

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open Set Metric
open HigherDimLFPP (Rd)

namespace HigherDimLQGContinuity

/-- On a radial segment outside a coordinate box, the port is closer to
every point of the box than the segment point is along the face normal. -/
theorem q4_retained_face_distance {d : ℕ} {v m p u x y : Rd d}
    {a L : ℝ} (ha : L < a) (hu : ‖u‖ = 1)
    (haxis : ∃ i : Fin d, u i = 1 ∨ u i = -1)
    (hm : m - v = a • u) (hp : p - v = (a - L) • u)
    (hx : x ∈ segment ℝ v p)
    (hy : ∀ i, |y i - m i| ≤ L) : dist x p ≤ dist x y := by
  rw [segment_eq_image'] at hx
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hx
  have hrad : 0 ≤ (1 - t) * (a - L) :=
    mul_nonneg (by linarith) (sub_nonneg.mpr ha.le)
  have hpx : p - (v + t • (p - v)) = ((1 - t) * (a - L)) • u := by
    calc
      p - (v + t • (p - v)) = (1 - t) • (p - v) := by module
      _ = ((1 - t) * (a - L)) • u := by rw [hp, smul_smul]
  have hdist : dist (v + t • (p - v)) p = (1 - t) * (a - L) := by
    rw [dist_comm, dist_eq_norm, hpx, norm_smul, hu, mul_one,
      Real.norm_eq_abs, abs_of_nonneg hrad]
  obtain ⟨i, hi⟩ := haxis
  have hcoord : (v + t • (p - v)) i - m i =
      (t * (a - L) - a) * u i := by
    have hvec : (v + t • (p - v)) - m = (t * (a - L) - a) • u := by
      calc
        _ = t • (p - v) - (m - v) := by abel
        _ = t • ((a - L) • u) - a • u := by rw [hp, hm]
        _ = (t * (a - L) - a) • u := by rw [smul_smul, sub_smul]
    have hi' := congrArg (fun z : Rd d => z i) hvec
    simpa only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] using hi'
  have hxycoord : (v + t • (p - v)) i - y i =
      (t * (a - L) - a) * u i - (y i - m i) := by
    rw [← hcoord]
    ring
  have hcoordle : (1 - t) * (a - L) ≤
      |(v + t • (p - v)) i - y i| := by
    rcases hi with hi | hi
    · have hlow := (abs_le.mp (hy i)).1
      have hneg : (1 - t) * (a - L) ≤
          -((v + t • (p - v)) i - y i) := by
        rw [hxycoord, hi]
        nlinarith
      exact hneg.trans (neg_le_abs _)
    · have hhigh := (abs_le.mp (hy i)).2
      have hpos : (1 - t) * (a - L) ≤
          (v + t • (p - v)) i - y i := by
        rw [hxycoord, hi]
        nlinarith
      exact hpos.trans (le_abs_self _)
  have hcoordnorm := Routing.abs_coord_sub_le_norm
    (v + t • (p - v)) y i
  rw [hdist, dist_eq_norm]
  exact hcoordle.trans hcoordnorm

/-- The port of a retained half-edge is closer to every point of the edge's
reserved box than a point farther out on that half-edge, in the face-normal
direction. -/
theorem SiteData.retained_face_distance {d : ℕ} (S : SiteData d)
    (hd : 2 ≤ d) (e : S.Edge) (i : Fin 2)
    {x y : Rd d} (hx : x ∈ S.retained e i) (hy : y ∈ S.box e) :
    dist x (S.port e i) ≤ dist x y := by
  have ha : S.boxHalfSide < S.mesh.δm / 2 := by
    have hdiag := S.box_halfDiagonal_le hd
    have hroot : 1 ≤ Real.sqrt d := Real.one_le_sqrt.mpr
      (by exact_mod_cast (show 1 ≤ d by omega))
    nlinarith [S.mesh.δm_pos, S.boxHalfSide_pos hd]
  fin_cases i
  · change x ∈ segment ℝ (S.vertexPoint (S.edgeLeft e)) (S.port e 0) at hx
    apply q4_retained_face_distance ha (S.edgeUnit_norm e)
      (S.edgeUnit_axis e) (S.edgeCenter_sub_left_vec e)
      (S.port_left_sub e) hx hy
  · change x ∈ segment ℝ (S.port e 1) (S.vertexPoint (S.edgeRight e)) at hx
    rw [segment_symm ℝ] at hx
    have haxis : ∃ j : Fin d,
        (-S.edgeUnit e) j = 1 ∨ (-S.edgeUnit e) j = -1 := by
      obtain ⟨j, hj | hj⟩ := S.edgeUnit_axis e
      · exact ⟨j, Or.inr (by simp [hj])⟩
      · exact ⟨j, Or.inl (by simp [hj])⟩
    have hp : S.port e 1 - S.vertexPoint (S.edgeRight e) =
        (S.mesh.δm / 2 - S.boxHalfSide) • (-S.edgeUnit e) := by
      rw [S.port_right_sub e, smul_neg, ← neg_smul]
      congr 1
      ring
    apply q4_retained_face_distance ha (by simp [S.edgeUnit_norm e])
      haxis (S.edgeCenter_sub_right_vec e) hp hx hy

theorem LeadCode.first_mem_trace {d K N : ℕ} (P : LeadCode d K N)
    (ν : ℝ) (hlast : 0 < P.last.val) :
    P.point ν 0 ∈ P.trace ν := by
  have hN : 0 < N := by have := P.last.isLt; omega
  let j : Fin N := ⟨0, hN⟩
  unfold LeadCode.trace
  apply mem_iUnion.mpr
  refine ⟨j, ?_⟩
  have hj : (j : ℕ) < P.last.val := hlast
  simp only [hj, ite_true]
  have h0 : P.point ν j.castSucc = P.point ν 0 := rfl
  rw [h0]
  exact left_mem_segment (𝕜 := ℝ) _ _

theorem SiteLabel.port_mem_lead_trace {d Kc Kl N : ℕ}
    {S : SiteData d} {μ ν r c₁ : ℝ}
    (ℓ : SiteLabel S Kc Kl N μ ν r c₁) (e : S.Edge) (i : Fin 2) :
    S.port e i ∈
      (if i = 0 then (ℓ e).1.lead0.trace ν else (ℓ e).1.lead1.trace ν) := by
  fin_cases i
  · have hg := (ℓ e).2.2.2.2.1
    have hlast : 0 < (ℓ e).1.lead0.last.val := by
      have := hg.1
      omega
    exact hg.2.1 ▸ (ℓ e).1.lead0.first_mem_trace ν hlast
  · have hg := (ℓ e).2.2.2.2.2.1
    have hlast : 0 < (ℓ e).1.lead1.last.val := by
      have := hg.1
      omega
    exact hg.2.1 ▸ (ℓ e).1.lead1.first_mem_trace ν hlast

theorem edgeReal_arc_subset_box {d Kc Kl N : ℕ}
    {S : SiteData d} {μ ν r c₁ : ℝ}
    (ℓ : SiteLabel S Kc Kl N μ ν r c₁) (e : S.Edge)
    (γ : ℝ → Rd d)
    (hstar : CoveredHit μ (S.edgeCenter e)
      (labelCellIndices (ℓ e).1.chamber) (γ '' Icc 0 1)) :
    γ '' Icc 0 1 ⊆ S.box e := by
  intro x hx
  obtain ⟨k, hk, hxcell⟩ := mem_iUnion₂.mp (hstar.1 hx)
  exact (ℓ e).2.1 k hk hxcell

/-- For points on a retained segment, port clearance loses at most a factor
of two. The arc itself lies inside the reserved box by chamber coverage. -/
theorem retained_arc_clearance {d Kc Kl N : ℕ}
    {S : SiteData d} (hd : 2 ≤ d)
    {μ ν r c₁ : ℝ}
    (ℓ : SiteLabel S Kc Kl N μ ν r c₁) (e : S.Edge)
    (i : Fin 2) (γ : ℝ → Rd d)
    (hstar : CoveredHit μ (S.edgeCenter e)
      (labelCellIndices (ℓ e).1.chamber) (γ '' Icc 0 1))
    (A : Set ℝ) (hA : A ⊆ Icc (0 : ℝ) 1)
    (hclear : ∀ p ∈ (if i = 0 then (ℓ e).1.lead0.trace ν
      else (ℓ e).1.lead1.trace ν), ∀ t ∈ A, r ≤ dist p (γ t))
    {x : Rd d} (hx : x ∈ S.retained e i) (t : ℝ) (ht : t ∈ A) :
    r / 2 ≤ dist x (γ t) := by
  have hport := SiteLabel.port_mem_lead_trace ℓ e i
  have hbox : γ t ∈ S.box e :=
    edgeReal_arc_subset_box ℓ e γ hstar ⟨t, hA ht, rfl⟩
  have hrad := S.retained_face_distance hd e i hx hbox
  have hclr := hclear (S.port e i) hport t ht
  have htri := dist_triangle (S.port e i) x (γ t)
  rw [dist_comm (S.port e i) x] at htri
  linarith

theorem siteConsts_sep_retained_margins {d : ℕ} (S : SiteData d)
    (hd : 2 ≤ d) (Cnet v : ℝ) (hv : 0 < v)
    (hA : SiteConstsA S (siteConsts S Cnet v)) :
    let C := siteConsts S Cnet v
    C.δsep + 3 * C.ω ≤ C.r / 2 ∧
    C.δsep + C.g + Real.sqrt d / 2 * C.μ + C.ω ≤ C.r / 2 := by
  let C := siteConsts S Cnet v
  have hr : 0 < C.r := siteConsts_r_pos S hd Cnet v hv
  have hω : 0 < C.ω := by
    change 0 < siteOmegaCoeff d * C.ν ^ 4
    exact mul_pos (siteOmegaCoeff_pos d (by omega))
      (pow_pos (siteConsts_ν_pos S hd Cnet v) _)
  have hδg : C.δsep ≤ C.g / 2 :=
    (le_min_iff.mp (le_min_iff.mp hA.2.2.2.2.2.1).2).1
  have hgr : C.g ≤ C.r / 8 := hA.2.2.1
  have hcμ : Real.sqrt d / 2 * C.μ ≤ C.ω / 4 := hA.2.2.2.2.1
  have hωr : C.ω ≤ C.r / 8 := by
    have hroot : 1 ≤ Real.sqrt d := Real.one_le_sqrt.mpr
      (by exact_mod_cast (show 1 ≤ d by omega))
    have hraw := (le_min_iff.mp hA.2.2.2.1).1
    have hmul := (le_div_iff₀ (by positivity : 0 < 8 * Real.sqrt d)).mp hraw
    nlinarith [mul_nonneg (sub_nonneg.mpr hroot) hω.le]
  constructor
  · change C.δsep + 3 * C.ω ≤ C.r / 2
    linarith
  · change C.δsep + C.g + Real.sqrt d / 2 * C.μ + C.ω ≤ C.r / 2
    linarith

end HigherDimLQGContinuity
