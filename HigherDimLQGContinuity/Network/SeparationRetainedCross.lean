import HigherDimLQGContinuity.Network.SeparationRetainedLocal

/-! # A retained tube versus the opposite lead tube -/

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open Set Metric
open HigherDimLFPP (Rd)

namespace HigherDimLQGContinuity

variable {μ ν r c₁ : ℝ}

theorem leadTrace_subset_box {d Kc Kl N : ℕ} {S : SiteData d}
    (ℓ : SiteLabel S Kc Kl N μ ν r c₁) (e : S.Edge) (i : Fin 2) :
    (if i = 0 then (ℓ e).1.lead0.trace ν else (ℓ e).1.lead1.trace ν) ⊆
      S.box e := by
  fin_cases i
  · intro x hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    have hjlast : j.val < (ℓ e).1.lead0.last.val := by
      by_contra h
      simp [h] at hj
    have hseg : x ∈ segment ℝ ((ℓ e).1.lead0.point ν j.castSucc)
        ((ℓ e).1.lead0.point ν j.succ) := by
      simpa [LeadCode.trace, hjlast] using hj
    have hg := (ℓ e).2.2.2.2.1
    have hj₀ : j.castSucc ≤ (ℓ e).1.lead0.last :=
      Fin.le_def.mpr (by simpa using Nat.le_of_lt hjlast)
    have hj₁ : j.succ ≤ (ℓ e).1.lead0.last :=
      Fin.le_def.mpr (by simpa using hjlast)
    exact (Routing.convex_resBox (S.edgeCenter e) S.boxHalfSide).segment_subset
      (hg.2.2.1 j.castSucc hj₀).1 (hg.2.2.1 j.succ hj₁).1 hseg
  · intro x hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    have hjlast : j.val < (ℓ e).1.lead1.last.val := by
      by_contra h
      simp [h] at hj
    have hseg : x ∈ segment ℝ ((ℓ e).1.lead1.point ν j.castSucc)
        ((ℓ e).1.lead1.point ν j.succ) := by
      simpa [LeadCode.trace, hjlast] using hj
    have hg := (ℓ e).2.2.2.2.2.1
    have hj₀ : j.castSucc ≤ (ℓ e).1.lead1.last :=
      Fin.le_def.mpr (by simpa using Nat.le_of_lt hjlast)
    have hj₁ : j.succ ≤ (ℓ e).1.lead1.last :=
      Fin.le_def.mpr (by simpa using hjlast)
    exact (Routing.convex_resBox (S.edgeCenter e) S.boxHalfSide).segment_subset
      (hg.2.2.1 j.castSucc hj₀).1 (hg.2.2.1 j.succ hj₁).1 hseg

theorem edgeLeadTrace_cross_sep {d Kc Kl N : ℕ} {S : SiteData d}
    (ℓ : SiteLabel S Kc Kl N μ ν r c₁) (e : S.Edge)
    {a b : Rd d}
    (ha : a ∈ (ℓ e).1.lead0.trace ν)
    (hb : b ∈ (ℓ e).1.lead1.trace ν) :
    c₁ * ν ^ 3 ≤ dist a b := by
  obtain ⟨j, hj⟩ := mem_iUnion.mp ha
  obtain ⟨k, hk⟩ := mem_iUnion.mp hb
  have hj' : j.val < (ℓ e).1.lead0.last.val := by
    by_contra h
    simp [h] at hj
  have hk' : k.val < (ℓ e).1.lead1.last.val := by
    by_contra h
    simp [h] at hk
  have hja : a ∈ segment ℝ ((ℓ e).1.lead0.point ν j.castSucc)
      ((ℓ e).1.lead0.point ν j.succ) := by
    simpa [LeadCode.trace, hj'] using hj
  have hkb : b ∈ segment ℝ ((ℓ e).1.lead1.point ν k.castSucc)
      ((ℓ e).1.lead1.point ν k.succ) := by
    simpa [LeadCode.trace, hk'] using hk
  exact (ℓ e).2.2.2.2.2.2 j k hj' hk' a hja b hkb

theorem retained_opposite_trace_sep {d Kc Kl N : ℕ}
    (S : SiteData d) (hd : 2 ≤ d)
    (ℓ : SiteLabel S Kc Kl N μ ν r c₁) (e : S.Edge)
    (i : Fin 2) {a b : Rd d}
    (ha : a ∈ S.retained e i)
    (hb : b ∈ (if i = 0 then (ℓ e).1.lead1.trace ν
      else (ℓ e).1.lead0.trace ν)) :
    c₁ * ν ^ 3 / 2 ≤ dist a b := by
  have hport := SiteLabel.port_mem_lead_trace ℓ e i
  have htri := dist_triangle (S.port e i) a b
  have hbox : b ∈ S.box e := by
    fin_cases i
    · exact leadTrace_subset_box ℓ e 1 hb
    · exact leadTrace_subset_box ℓ e 0 hb
  have hrad := S.retained_face_distance hd e i ha hbox
  have hcross : c₁ * ν ^ 3 ≤ dist (S.port e i) b := by
    fin_cases i
    · exact edgeLeadTrace_cross_sep ℓ e hport hb
    · rw [dist_comm]
      exact edgeLeadTrace_cross_sep ℓ e hb hport
  rw [dist_comm (S.port e i) a] at htri
  linarith

theorem edgeRetained0_lead1_sep {d : ℕ} (S : SiteData d)
    (hd : 2 ≤ d) (Cnet v : ℝ) (_hv : 0 < v)
    (hA : SiteConstsA S (siteConsts S Cnet v))
    {Kc Kl : ℕ}
    (ℓ : SiteLabel S Kc Kl (siteConsts S Cnet v).N
      (siteConsts S Cnet v).μ (siteConsts S Cnet v).ν
      (siteConsts S Cnet v).r (Routing.gpC1 4))
    (e : S.Edge) {x y : Rd d}
    (hx : x ∈ edgeRetainedClosed ℓ e 0 (siteConsts S Cnet v).ω)
    (hy : y ∈ edgeLeadClosed ℓ e 1 (siteConsts S Cnet v).ω) :
    (siteConsts S Cnet v).δsep ≤ dist x y := by
  let C := siteConsts S Cnet v
  have hω : 0 < C.ω := by
    change 0 < siteOmegaCoeff d * C.ν ^ 4
    exact mul_pos (siteOmegaCoeff_pos d (by omega))
      (pow_pos (siteConsts_ν_pos S hd Cnet v) _)
  have hbase : ∀ a ∈ S.retained e 0,
      ∀ b ∈ (ℓ e).1.lead1.trace C.ν,
        Routing.gpC1 4 * C.ν ^ 3 / 2 ≤ dist a b := by
    intro a ha b hb
    exact retained_opposite_trace_sep S hd ℓ e 0 ha hb
  have hx' := edgeRetainedClosed_subset_retained_thickening ℓ e 0 C.ω hx
  have hy' := edgeLeadClosed_subset_trace_thickening ℓ e 1 C.ω hy
  have hsep : Routing.gpC1 4 * C.ν ^ 3 / 2 - C.ω - C.ω ≤ dist x y :=
    dist_ge_of_two_cthickenings hω.le hω.le hbase hx' hy'
  have hωc : C.ω ≤ Routing.gpC1 4 * C.ν ^ 3 / 8 :=
    (le_min_iff.mp hA.2.2.2.1).2
  have hδ : C.δsep = Routing.gpC1 4 * C.ν ^ 3 / 4 := rfl
  linarith

theorem edgeRetained1_lead0_sep {d : ℕ} (S : SiteData d)
    (hd : 2 ≤ d) (Cnet v : ℝ) (_hv : 0 < v)
    (hA : SiteConstsA S (siteConsts S Cnet v))
    {Kc Kl : ℕ}
    (ℓ : SiteLabel S Kc Kl (siteConsts S Cnet v).N
      (siteConsts S Cnet v).μ (siteConsts S Cnet v).ν
      (siteConsts S Cnet v).r (Routing.gpC1 4))
    (e : S.Edge) {x y : Rd d}
    (hx : x ∈ edgeRetainedClosed ℓ e 1 (siteConsts S Cnet v).ω)
    (hy : y ∈ edgeLeadClosed ℓ e 0 (siteConsts S Cnet v).ω) :
    (siteConsts S Cnet v).δsep ≤ dist x y := by
  let C := siteConsts S Cnet v
  have hω : 0 < C.ω := by
    change 0 < siteOmegaCoeff d * C.ν ^ 4
    exact mul_pos (siteOmegaCoeff_pos d (by omega))
      (pow_pos (siteConsts_ν_pos S hd Cnet v) _)
  have hbase : ∀ a ∈ S.retained e 1,
      ∀ b ∈ (ℓ e).1.lead0.trace C.ν,
        Routing.gpC1 4 * C.ν ^ 3 / 2 ≤ dist a b := by
    intro a ha b hb
    exact retained_opposite_trace_sep S hd ℓ e 1 ha hb
  have hx' := edgeRetainedClosed_subset_retained_thickening ℓ e 1 C.ω hx
  have hy' := edgeLeadClosed_subset_trace_thickening ℓ e 0 C.ω hy
  have hsep : Routing.gpC1 4 * C.ν ^ 3 / 2 - C.ω - C.ω ≤ dist x y :=
    dist_ge_of_two_cthickenings hω.le hω.le hbase hx' hy'
  have hωc : C.ω ≤ Routing.gpC1 4 * C.ν ^ 3 / 8 :=
    (le_min_iff.mp hA.2.2.2.1).2
  have hδ : C.δsep = Routing.gpC1 4 * C.ν ^ 3 / 4 := rfl
  linarith

end HigherDimLQGContinuity
