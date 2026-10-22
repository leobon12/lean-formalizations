import HigherDimLQGContinuity.Network.SeparationBox

/-! # Local separation within one reserved box -/

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open Set Metric
open HigherDimLFPP (Rd)

namespace HigherDimLQGContinuity

variable {μ ν r c₁ : ℝ}

theorem edgeChamberClosed_eq_ballUnion {d Kc Kl N : ℕ}
    {S : SiteData d} (ℓ : SiteLabel S Kc Kl N μ ν r c₁)
    (e : S.Edge) (ω : ℝ) :
    edgeChamberClosed ℓ ω e =
      ballUnion μ (S.edgeCenter e) (labelCellIndices (ℓ e).1.chamber) ω := by
  simp only [edgeChamberClosed, edgeChamberSites, closedBallSpecs_image,
    ballUnion]
  ext x
  simp only [mem_iUnion, Finset.mem_image]
  aesop

/-- Scalar margins for the lead/chamber and lead/opposite-gate cases. -/
theorem siteConsts_sep_local_margins {d : ℕ} (S : SiteData d)
    (hd : 2 ≤ d) (Cnet v : ℝ) (hv : 0 < v)
    (hA : SiteConstsA S (siteConsts S Cnet v)) :
    let C := siteConsts S Cnet v
    C.δsep + 3 * C.ω ≤ C.r ∧
    C.δsep + Real.sqrt d / 2 * C.μ + 2 * C.ω ≤ C.g ∧
    C.δsep + C.g + Real.sqrt d / 2 * C.μ + C.ω ≤ C.r := by
  let C := siteConsts S Cnet v
  have hr : 0 < C.r := siteConsts_r_pos S hd Cnet v hv
  have hδr : C.δsep ≤ C.r / 2 :=
    (le_min_iff.mp hA.2.2.2.2.2.1).1
  have hδg : C.δsep ≤ C.g / 2 :=
    (le_min_iff.mp (le_min_iff.mp hA.2.2.2.2.2.1).2).1
  have hgr : C.g ≤ C.r / 8 := hA.2.2.1
  have hcμ : Real.sqrt d / 2 * C.μ ≤ C.ω / 4 :=
    hA.2.2.2.2.1
  have hωr : C.ω ≤ C.r / 8 := by
    have hroot : 1 ≤ Real.sqrt d := Real.one_le_sqrt.mpr
      (by exact_mod_cast (show 1 ≤ d by omega))
    have hraw := (le_min_iff.mp hA.2.2.2.1).1
    have hmul := (le_div_iff₀ (by positivity : 0 < 8 * Real.sqrt d)).mp hraw
    nlinarith [siteConsts_omega_le_nu S hd Cnet v]
  have hων : C.ω ≤ C.ν := siteConsts_omega_le_nu S hd Cnet v
  have hωg : 100 * C.ω ≤ C.g := by
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
    change 100 * C.ω ≤ 100 * d * C.ν
    nlinarith [siteConsts_ν_pos S hd Cnet v]
  have hg : 0 < C.g := by
    change 0 < 100 * d * C.ν
    have hdR : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
    exact mul_pos (mul_pos (by norm_num) hdR)
      (siteConsts_ν_pos S hd Cnet v)
  constructor
  · change C.δsep + 3 * C.ω ≤ C.r
    linarith
  constructor
  · change C.δsep + Real.sqrt d / 2 * C.μ + 2 * C.ω ≤ C.g
    linarith
  · change C.δsep + C.g + Real.sqrt d / 2 * C.μ + C.ω ≤ C.r
    linarith

/-- A lead tube and its own chamber are separated after the shared gate
interior is removed. -/
theorem edgeLead0_chamber_sep {d : ℕ} (S : SiteData d)
    (hd : 2 ≤ d) (Cnet v : ℝ) (hv : 0 < v)
    (hA : SiteConstsA S (siteConsts S Cnet v))
    {Kc Kl : ℕ}
    (ℓ : SiteLabel S Kc Kl (siteConsts S Cnet v).N
      (siteConsts S Cnet v).μ (siteConsts S Cnet v).ν
      (siteConsts S Cnet v).r (Routing.gpC1 4))
    (hreal : IsRealizable S ℓ S.seed.A S.seed.α S.seed.β
      (siteConsts S Cnet v).t₀)
    (e : S.Edge) {x y : Rd d}
    (hx : x ∈ edgeLeadClosed ℓ e 0 (siteConsts S Cnet v).ω \
      interior (edgeGateClosed ℓ e 0 (siteConsts S Cnet v).g))
    (hy : y ∈ edgeChamberClosed ℓ (siteConsts S Cnet v).ω e \
      interior (edgeGateClosed ℓ e 0 (siteConsts S Cnet v).g)) :
    (siteConsts S Cnet v).δsep ≤ dist x y := by
  let C := siteConsts S Cnet v
  obtain ⟨γ, _, _, hstar, hgate0, _, hclear0, _, _, _⟩ := hreal e
  have hμ : 0 ≤ C.μ := by
    change 0 ≤ C.ω ^ 2 / (2 * Real.sqrt d)
    positivity
  have hω : 0 < C.ω := by
    change 0 < siteOmegaCoeff d * C.ν ^ 4
    exact mul_pos (siteOmegaCoeff_pos d (by omega))
      (pow_pos (siteConsts_ν_pos S hd Cnet v) _)
  have ht₀ : 0 ≤ C.t₀ := (siteConsts_t₀_pos S Cnet v hv).le
  have hx' : x ∈ cthickening C.ω ((ℓ e).1.lead0.trace C.ν) \
      interior (ballUnion C.μ (S.edgeCenter e)
        (labelCellIndices (ℓ e).1.gate0) C.g) :=
    ⟨edgeLeadClosed_subset_trace_thickening ℓ e 0 C.ω hx.1, hx.2⟩
  have hy' : y ∈ ballUnion C.μ (S.edgeCenter e)
      (labelCellIndices (ℓ e).1.chamber) C.ω \
      interior (ballUnion C.μ (S.edgeCenter e)
        (labelCellIndices (ℓ e).1.gate0) C.g) := by
    exact ⟨(edgeChamberClosed_eq_ballUnion ℓ e C.ω) ▸ hy.1, hy.2⟩
  have hsep := lead_chamber_sep hμ hω ht₀ (S.edgeCenter e) γ
    (labelCellIndices (ℓ e).1.chamber)
    (labelCellIndices (ℓ e).1.gate0)
    ((ℓ e).1.lead0.trace C.ν) hstar hgate0
      (by linarith [hA.2.2.2.2.1]) hclear0 hx' hy'
  obtain ⟨hmargin1, hmargin2, _⟩ :=
    siteConsts_sep_local_margins S hd Cnet v hv hA
  have hδ1 : C.δsep ≤ C.r - 3 * C.ω := by linarith
  have hδ2 : C.δsep ≤ C.g - Real.sqrt d / 2 * C.μ - 2 * C.ω := by
    linarith
  exact (le_min hδ1 hδ2).trans hsep

theorem image_reverse_Icc {d : ℕ} (γ : ℝ → Rd d) (a b : ℝ) :
    (fun t => γ (1 - t)) '' Icc a b = γ '' Icc (1 - b) (1 - a) := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    refine ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, ?_⟩
    simp

theorem edgeLead1_chamber_sep {d : ℕ} (S : SiteData d)
    (hd : 2 ≤ d) (Cnet v : ℝ) (hv : 0 < v)
    (hA : SiteConstsA S (siteConsts S Cnet v))
    {Kc Kl : ℕ}
    (ℓ : SiteLabel S Kc Kl (siteConsts S Cnet v).N
      (siteConsts S Cnet v).μ (siteConsts S Cnet v).ν
      (siteConsts S Cnet v).r (Routing.gpC1 4))
    (hreal : IsRealizable S ℓ S.seed.A S.seed.α S.seed.β
      (siteConsts S Cnet v).t₀)
    (e : S.Edge) {x y : Rd d}
    (hx : x ∈ edgeLeadClosed ℓ e 1 (siteConsts S Cnet v).ω \
      interior (edgeGateClosed ℓ e 1 (siteConsts S Cnet v).g))
    (hy : y ∈ edgeChamberClosed ℓ (siteConsts S Cnet v).ω e \
      interior (edgeGateClosed ℓ e 1 (siteConsts S Cnet v).g)) :
    (siteConsts S Cnet v).δsep ≤ dist x y := by
  let C := siteConsts S Cnet v
  obtain ⟨γ, _, _, hstar, _, hgate1, _, hclear1, _, _⟩ := hreal e
  have hμ : 0 ≤ C.μ := by
    change 0 ≤ C.ω ^ 2 / (2 * Real.sqrt d)
    positivity
  have hω : 0 < C.ω := by
    change 0 < siteOmegaCoeff d * C.ν ^ 4
    exact mul_pos (siteOmegaCoeff_pos d (by omega))
      (pow_pos (siteConsts_ν_pos S hd Cnet v) _)
  have ht₀ : 0 ≤ C.t₀ := (siteConsts_t₀_pos S Cnet v hv).le
  have hstar' : CoveredHit C.μ (S.edgeCenter e)
      (labelCellIndices (ℓ e).1.chamber)
      ((fun t => γ (1 - t)) '' Icc (0 : ℝ) 1) := by
    simpa only [image_reverse_Icc, sub_self, sub_zero] using hstar
  have hgate1' : CoveredHit C.μ (S.edgeCenter e)
      (labelCellIndices (ℓ e).1.gate1)
      ((fun t => γ (1 - t)) '' Icc (0 : ℝ) (2 * C.t₀)) := by
    simpa only [image_reverse_Icc, sub_zero] using hgate1
  have hclear' : ∀ l ∈ (ℓ e).1.lead1.trace C.ν,
      ∀ t ∈ Icc C.t₀ 1, C.r ≤ dist l (γ (1 - t)) := by
    intro l hl t ht
    exact hclear1 l hl (1 - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hx' : x ∈ cthickening C.ω ((ℓ e).1.lead1.trace C.ν) \
      interior (ballUnion C.μ (S.edgeCenter e)
        (labelCellIndices (ℓ e).1.gate1) C.g) :=
    ⟨edgeLeadClosed_subset_trace_thickening ℓ e 1 C.ω hx.1, hx.2⟩
  have hy' : y ∈ ballUnion C.μ (S.edgeCenter e)
      (labelCellIndices (ℓ e).1.chamber) C.ω \
      interior (ballUnion C.μ (S.edgeCenter e)
        (labelCellIndices (ℓ e).1.gate1) C.g) := by
    exact ⟨(edgeChamberClosed_eq_ballUnion ℓ e C.ω) ▸ hy.1, hy.2⟩
  have hsep := lead_chamber_sep hμ hω ht₀ (S.edgeCenter e)
    (fun t => γ (1 - t))
    (labelCellIndices (ℓ e).1.chamber)
    (labelCellIndices (ℓ e).1.gate1)
    ((ℓ e).1.lead1.trace C.ν) hstar' hgate1'
      (by linarith [hA.2.2.2.2.1]) hclear' hx' hy'
  obtain ⟨hmargin1, hmargin2, _⟩ :=
    siteConsts_sep_local_margins S hd Cnet v hv hA
  have hδ1 : C.δsep ≤ C.r - 3 * C.ω := by linarith
  have hδ2 : C.δsep ≤ C.g - Real.sqrt d / 2 * C.μ - 2 * C.ω := by
    linarith
  exact (le_min hδ1 hδ2).trans hsep

theorem edgeLeadClosed_cross_sep {d : ℕ} (S : SiteData d)
    (hd : 2 ≤ d) (Cnet v : ℝ) (_hv : 0 < v)
    (hA : SiteConstsA S (siteConsts S Cnet v))
    {Kc Kl : ℕ}
    (ℓ : SiteLabel S Kc Kl (siteConsts S Cnet v).N
      (siteConsts S Cnet v).μ (siteConsts S Cnet v).ν
      (siteConsts S Cnet v).r (Routing.gpC1 4))
    (e : S.Edge) {x y : Rd d}
    (hx : x ∈ edgeLeadClosed ℓ e 0 (siteConsts S Cnet v).ω)
    (hy : y ∈ edgeLeadClosed ℓ e 1 (siteConsts S Cnet v).ω) :
    (siteConsts S Cnet v).δsep ≤ dist x y := by
  let C := siteConsts S Cnet v
  have hω : 0 < C.ω := by
    change 0 < siteOmegaCoeff d * C.ν ^ 4
    exact mul_pos (siteOmegaCoeff_pos d (by omega))
      (pow_pos (siteConsts_ν_pos S hd Cnet v) _)
  have hx' := edgeLeadClosed_subset_trace_thickening ℓ e 0 C.ω hx
  have hy' := edgeLeadClosed_subset_trace_thickening ℓ e 1 C.ω hy
  have hcross : ∀ a ∈ (ℓ e).1.lead0.trace C.ν,
      ∀ b ∈ (ℓ e).1.lead1.trace C.ν,
        Routing.gpC1 4 * C.ν ^ 3 ≤ dist a b := by
    intro a ha b hb
    obtain ⟨j, hj⟩ := mem_iUnion.mp ha
    obtain ⟨k, hk⟩ := mem_iUnion.mp hb
    have hj' : j.val < (ℓ e).1.lead0.last.val := by
      by_contra h
      simp [h] at hj
    have hk' : k.val < (ℓ e).1.lead1.last.val := by
      by_contra h
      simp [h] at hk
    have hja : a ∈ segment ℝ ((ℓ e).1.lead0.point C.ν j.castSucc)
        ((ℓ e).1.lead0.point C.ν j.succ) := by
      simpa [LeadCode.trace, hj'] using hj
    have hkb : b ∈ segment ℝ ((ℓ e).1.lead1.point C.ν k.castSucc)
        ((ℓ e).1.lead1.point C.ν k.succ) := by
      simpa [LeadCode.trace, hk'] using hk
    exact (ℓ e).2.2.2.2.2.2 j k hj' hk' a hja b hkb
  have hsep : Routing.gpC1 4 * C.ν ^ 3 - C.ω - C.ω ≤ dist x y :=
    dist_ge_of_two_cthickenings hω.le hω.le hcross hx' hy'
  have hωc : C.ω ≤ Routing.gpC1 4 * C.ν ^ 3 / 8 :=
    (le_min_iff.mp hA.2.2.2.1).2
  have hδc : C.δsep ≤ Routing.gpC1 4 * C.ν ^ 3 / 2 :=
    (le_min_iff.mp (le_min_iff.mp (le_min_iff.mp hA.2.2.2.2.2.1).2).2).1
  linarith

end HigherDimLQGContinuity
