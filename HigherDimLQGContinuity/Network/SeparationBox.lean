import HigherDimLQGContinuity.Network.SeparationCore

/-! # Quantitative separation away from a shared edge -/

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open Set Metric
open HigherDimLFPP (Rd)

namespace HigherDimLQGContinuity

variable {μ ν r c₁ : ℝ}

/-- All the labelled parts whose sample centres lie in the reserved box. -/
def edgeBoxPieces {d Kc Kl N : ℕ} {S : SiteData d}
    (ℓ : SiteLabel S Kc Kl N μ ν r c₁) (e : S.Edge) (g ω : ℝ) :
    Set (Rd d) :=
  edgeChamberClosed ℓ ω e ∪ edgeGateClosed ℓ e 0 g ∪
    edgeGateClosed ℓ e 1 g ∪ edgeLeadClosed ℓ e 0 ω ∪
      edgeLeadClosed ℓ e 1 ω

theorem edgeBoxPieces_subset_box_thickening {d Kc Kl N : ℕ}
    {S : SiteData d} {μ ν r c₁ g ω : ℝ} (hμ : 0 ≤ μ)
    (hωg : ω ≤ g)
    (ℓ : SiteLabel S Kc Kl N μ ν r c₁) (e : S.Edge) :
    edgeBoxPieces ℓ e g ω ⊆ cthickening g (S.box e) := by
  have hmono := cthickening_mono hωg (S.box e)
  intro x hx
  simp only [edgeBoxPieces, mem_union] at hx
  rcases hx with (((hch | hg0) | hg1) | hl0) | hl1
  · exact hmono (edgeChamberClosed_subset_box_thickening hμ ℓ e hch)
  · exact edgeGateClosed_subset_box_thickening hμ ℓ e 0 hg0
  · exact edgeGateClosed_subset_box_thickening hμ ℓ e 1 hg1
  · exact hmono (edgeLeadClosed_subset_box_thickening ℓ e 0 ω hl0)
  · exact hmono (edgeLeadClosed_subset_box_thickening ℓ e 1 ω hl1)

/-- All mesh-scale margins needed for distinct reserved boxes, distinct
retained segments, and a reserved box against another edge's segment. -/
theorem siteConsts_sep_mesh_margins {d : ℕ} (S : SiteData d)
    (hd : 2 ≤ d) (Cnet v : ℝ) (hv : 0 < v)
    (hA : SiteConstsA S (siteConsts S Cnet v)) :
    let C := siteConsts S Cnet v
    0 < C.g ∧ 0 < C.ω ∧ C.ω ≤ C.g ∧
    C.δsep + 2 * C.g ≤ S.mesh.δm / 2 ∧
    C.δsep + C.g + C.ω ≤ S.mesh.δm / 4 ∧
    C.δsep + 2 * C.ω ≤ 2 * S.boxHalfSide := by
  let C := siteConsts S Cnet v
  have hr := siteConsts_r_pos S hd Cnet v hv
  have hν := siteConsts_ν_pos S hd Cnet v
  have hω : 0 < C.ω := by
    change 0 < siteOmegaCoeff d * C.ν ^ 4
    exact mul_pos (siteOmegaCoeff_pos d (by omega)) (pow_pos hν _)
  have hg : 0 < C.g := by
    change 0 < 100 * d * C.ν
    positivity
  have hωg : C.ω ≤ C.g := by
    have hων := siteConsts_omega_le_nu S hd Cnet v
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
    have hνg : C.ν ≤ C.g := by
      change C.ν ≤ 100 * d * C.ν
      nlinarith
    exact hων.trans hνg
  have hδL : C.δsep ≤ S.boxHalfSide / 2 :=
    (le_min_iff.mp (le_min_iff.mp (le_min_iff.mp hA.2.2.2.2.2.1).2).2).2
  have hgr : C.g ≤ C.r / 8 := hA.2.2.1
  have hrL := siteConsts_r_le_box S hd Cnet v hv
  have hLδ : S.boxHalfSide ≤ S.mesh.δm / 16 := by
    have hdiag := S.box_halfDiagonal_le hd
    have hroot : 1 ≤ Real.sqrt d := Real.one_le_sqrt.mpr
      (by exact_mod_cast (show 1 ≤ d by omega))
    have hL := S.boxHalfSide_pos hd
    nlinarith [mul_nonneg (sub_nonneg.mpr hroot) hL.le]
  refine ⟨hg, hω, hωg, ?_, ?_, ?_⟩ <;> linarith

theorem edgeBoxPieces_sep_other_box {d : ℕ} (S : SiteData d)
    (hd : 2 ≤ d) (Cnet v : ℝ) (hv : 0 < v)
    (hA : SiteConstsA S (siteConsts S Cnet v))
    {Kc Kl : ℕ}
    (ℓ : SiteLabel S Kc Kl (siteConsts S Cnet v).N
      (siteConsts S Cnet v).μ (siteConsts S Cnet v).ν
      (siteConsts S Cnet v).r (Routing.gpC1 4))
    (e f : S.Edge) (hef : e ≠ f) {x y : Rd d}
    (hx : x ∈ edgeBoxPieces ℓ e (siteConsts S Cnet v).g
      (siteConsts S Cnet v).ω)
    (hy : y ∈ edgeBoxPieces ℓ f (siteConsts S Cnet v).g
      (siteConsts S Cnet v).ω) :
    (siteConsts S Cnet v).δsep ≤ dist x y := by
  let C := siteConsts S Cnet v
  obtain ⟨hg, _, hωg, hmargin, _, _⟩ :=
    siteConsts_sep_mesh_margins S hd Cnet v hv hA
  have hμ : 0 ≤ C.μ := by
    change 0 ≤ C.ω ^ 2 / (2 * Real.sqrt d)
    positivity
  have hx' := edgeBoxPieces_subset_box_thickening hμ hωg ℓ e hx
  have hy' := edgeBoxPieces_subset_box_thickening hμ hωg ℓ f hy
  have hsep : S.mesh.δm / 2 - C.g - C.g ≤ dist x y :=
    dist_ge_of_two_cthickenings hg.le hg.le
      ((siteMesh_geometry S hd).box_pair e f hef) hx' hy'
  linarith

theorem edgeBoxPieces_sep_other_retained {d : ℕ} (S : SiteData d)
    (hd : 2 ≤ d) (Cnet v : ℝ) (hv : 0 < v)
    (hA : SiteConstsA S (siteConsts S Cnet v))
    {Kc Kl : ℕ}
    (ℓ : SiteLabel S Kc Kl (siteConsts S Cnet v).N
      (siteConsts S Cnet v).μ (siteConsts S Cnet v).ν
      (siteConsts S Cnet v).r (Routing.gpC1 4))
    (e f : S.Edge) (hef : e ≠ f) (i : Fin 2) {x y : Rd d}
    (hx : x ∈ edgeBoxPieces ℓ e (siteConsts S Cnet v).g
      (siteConsts S Cnet v).ω)
    (hy : y ∈ edgeRetainedClosed ℓ f i (siteConsts S Cnet v).ω) :
    (siteConsts S Cnet v).δsep ≤ dist x y := by
  let C := siteConsts S Cnet v
  obtain ⟨hg, hω, hωg, _, hmargin, _⟩ :=
    siteConsts_sep_mesh_margins S hd Cnet v hv hA
  have hμ : 0 ≤ C.μ := by
    change 0 ≤ C.ω ^ 2 / (2 * Real.sqrt d)
    positivity
  have hx' := edgeBoxPieces_subset_box_thickening hμ hωg ℓ e hx
  have hy' := edgeRetainedClosed_subset_retained_thickening ℓ f i C.ω hy
  have hsep : S.mesh.δm / 4 - C.g - C.ω ≤ dist x y :=
    dist_ge_of_two_cthickenings hg.le hω.le
      ((siteMesh_geometry S hd).box_other e f hef i) hx' hy'
  linarith

theorem edgeRetainedClosed_sep_other_vertex {d : ℕ} (S : SiteData d)
    (hd : 2 ≤ d) (Cnet v : ℝ) (hv : 0 < v)
    (hA : SiteConstsA S (siteConsts S Cnet v))
    {Kc Kl : ℕ}
    (ℓ : SiteLabel S Kc Kl (siteConsts S Cnet v).N
      (siteConsts S Cnet v).μ (siteConsts S Cnet v).ν
      (siteConsts S Cnet v).r (Routing.gpC1 4))
    (e f : S.Edge) (i j : Fin 2)
    (hvert : S.retainedVertex e i ≠ S.retainedVertex f j)
    {x y : Rd d}
    (hx : x ∈ edgeRetainedClosed ℓ e i (siteConsts S Cnet v).ω)
    (hy : y ∈ edgeRetainedClosed ℓ f j (siteConsts S Cnet v).ω) :
    (siteConsts S Cnet v).δsep ≤ dist x y := by
  let C := siteConsts S Cnet v
  obtain ⟨_, hω, _, _, _, hmargin⟩ :=
    siteConsts_sep_mesh_margins S hd Cnet v hv hA
  have hx' := edgeRetainedClosed_subset_retained_thickening ℓ e i C.ω hx
  have hy' := edgeRetainedClosed_subset_retained_thickening ℓ f j C.ω hy
  have hsep : 2 * S.boxHalfSide - C.ω - C.ω ≤ dist x y :=
    dist_ge_of_two_cthickenings hω.le hω.le
      ((siteMesh_geometry S hd).retained_pair e f i j hvert) hx' hy'
  linarith

end HigherDimLQGContinuity
