import HigherDimLQGContinuity.Network.SeparationNodes

/-! # Separation of two distinct vertex tubes -/

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open Set Metric
open HigherDimLFPP (Rd)

namespace HigherDimLQGContinuity

variable {μ ν r c₁ : ℝ}

theorem edgeLeadClosed_subset_boxPieces {d Kc Kl N : ℕ}
    {S : SiteData d} (ℓ : SiteLabel S Kc Kl N μ ν r c₁)
    (e : S.Edge) (i : Fin 2) (g ω : ℝ) :
    edgeLeadClosed ℓ e i ω ⊆ edgeBoxPieces ℓ e g ω := by
  fin_cases i
  · intro x hx
    exact Or.inl (Or.inr hx)
  · intro x hx
    exact Or.inr hx

theorem edgeGateClosed_subset_boxPieces {d Kc Kl N : ℕ}
    {S : SiteData d} (ℓ : SiteLabel S Kc Kl N μ ν r c₁)
    (e : S.Edge) (i : Fin 2) (g ω : ℝ) :
    edgeGateClosed ℓ e i g ⊆ edgeBoxPieces ℓ e g ω := by
  fin_cases i
  · intro x hx
    exact Or.inl (Or.inl (Or.inl (Or.inr hx)))
  · intro x hx
    exact Or.inl (Or.inl (Or.inr hx))

theorem edgeChamberClosed_subset_boxPieces {d Kc Kl N : ℕ}
    {S : SiteData d} (ℓ : SiteLabel S Kc Kl N μ ν r c₁)
    (e : S.Edge) (g ω : ℝ) :
    edgeChamberClosed ℓ ω e ⊆ edgeBoxPieces ℓ e g ω := by
  intro x hx
  exact Or.inl (Or.inl (Or.inl (Or.inl hx)))

/-- The four tube-piece combinations for different vertex nodes. -/
theorem edgeTubePieces_sep_distinct_vertex {d : ℕ} (S : SiteData d)
    (hd : 2 ≤ d) (Cnet v : ℝ) (hv : 0 < v)
    (hA : SiteConstsA S (siteConsts S Cnet v))
    {Kc Kl : ℕ}
    (ℓ : SiteLabel S Kc Kl (siteConsts S Cnet v).N
      (siteConsts S Cnet v).μ (siteConsts S Cnet v).ν
      (siteConsts S Cnet v).r (Routing.gpC1 4))
    (e f : S.Edge) (i j : Fin 2)
    (hvert : S.retainedVertex e i ≠ S.retainedVertex f j)
    {x y : Rd d}
    (hx : x ∈ edgeRetainedClosed ℓ e i (siteConsts S Cnet v).ω ∪
      edgeLeadClosed ℓ e i (siteConsts S Cnet v).ω)
    (hy : y ∈ edgeRetainedClosed ℓ f j (siteConsts S Cnet v).ω ∪
      edgeLeadClosed ℓ f j (siteConsts S Cnet v).ω) :
    (siteConsts S Cnet v).δsep ≤ dist x y := by
  let C := siteConsts S Cnet v
  rcases hx with hxR | hxL
  · rcases hy with hyR | hyL
    · exact edgeRetainedClosed_sep_other_vertex S hd Cnet v hv hA ℓ
        e f i j hvert hxR hyR
    · by_cases hef : e = f
      · subst f
        fin_cases i <;> fin_cases j
        · exact False.elim (hvert rfl)
        · exact edgeRetained0_lead1_sep S hd Cnet v hv hA ℓ e hxR hyL
        · exact edgeRetained1_lead0_sep S hd Cnet v hv hA ℓ e hxR hyL
        · exact False.elim (hvert rfl)
      · have h := edgeBoxPieces_sep_other_retained S hd Cnet v hv hA ℓ
          f e (Ne.symm hef) i (edgeLeadClosed_subset_boxPieces ℓ f j C.g C.ω hyL) hxR
        rw [dist_comm] at h
        exact h
  · rcases hy with hyR | hyL
    · by_cases hef : e = f
      · subst f
        fin_cases i <;> fin_cases j
        · exact False.elim (hvert rfl)
        · have h := edgeRetained1_lead0_sep S hd Cnet v hv hA ℓ e hyR hxL
          rw [dist_comm] at h
          exact h
        · have h := edgeRetained0_lead1_sep S hd Cnet v hv hA ℓ e hyR hxL
          rw [dist_comm] at h
          exact h
        · exact False.elim (hvert rfl)
      · exact edgeBoxPieces_sep_other_retained S hd Cnet v hv hA ℓ
          e f hef j (edgeLeadClosed_subset_boxPieces ℓ e i C.g C.ω hxL) hyR
    · by_cases hef : e = f
      · subst f
        fin_cases i <;> fin_cases j
        · exact False.elim (hvert rfl)
        · exact edgeLeadClosed_cross_sep S hd Cnet v hv hA ℓ e hxL hyL
        · have h := edgeLeadClosed_cross_sep S hd Cnet v hv hA ℓ e hyL hxL
          rw [dist_comm] at h
          exact h
        · exact False.elim (hvert rfl)
      · exact edgeBoxPieces_sep_other_box S hd Cnet v hv hA ℓ e f hef
          (edgeLeadClosed_subset_boxPieces ℓ e i C.g C.ω hxL)
          (edgeLeadClosed_subset_boxPieces ℓ f j C.g C.ω hyL)

theorem labelNet_vertex_vertex_sep {d : ℕ} (S : SiteData d)
    (hd : 2 ≤ d) (Cnet v : ℝ) (hv : 0 < v)
    (hA : SiteConstsA S (siteConsts S Cnet v))
    {Kc Kl : ℕ}
    (ℓ : SiteLabel S Kc Kl (siteConsts S Cnet v).N
      (siteConsts S Cnet v).μ (siteConsts S Cnet v).ν
      (siteConsts S Cnet v).r (Routing.gpC1 4))
    (u w : S.Vertex) (huw : u ≠ w) {x y : Rd d}
    (hx : x ∈ (labelNet S (siteConsts S Cnet v) ℓ).Node (Sum.inl u))
    (hy : y ∈ (labelNet S (siteConsts S Cnet v) ℓ).Node (Sum.inl w)) :
    (siteConsts S Cnet v).δsep ≤ dist x y := by
  obtain ⟨e, i, heu, hxe, _⟩ :=
    labelNet_vertex_mem_piece S (siteConsts S Cnet v) ℓ u hx
  obtain ⟨f, j, hfw, hyf, _⟩ :=
    labelNet_vertex_mem_piece S (siteConsts S Cnet v) ℓ w hy
  have hvert : S.retainedVertex e i ≠ S.retainedVertex f j := by
    intro h
    exact huw (heu ▸ h ▸ hfw)
  exact edgeTubePieces_sep_distinct_vertex S hd Cnet v hv hA
    ℓ e f i j hvert hxe hyf

end HigherDimLQGContinuity
