import HigherDimLQGContinuity.Network.SeparationRetained

/-! # Retained segments versus chambers and opposite gates -/

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open Set Metric
open HigherDimLFPP (Rd)

namespace HigherDimLQGContinuity

theorem edgeRetained0_chamber_sep {d : ℕ} (S : SiteData d)
    (hd : 2 ≤ d) (Cnet v : ℝ) (hv : 0 < v)
    (hA : SiteConstsA S (siteConsts S Cnet v))
    {Kc Kl : ℕ}
    (ℓ : SiteLabel S Kc Kl (siteConsts S Cnet v).N
      (siteConsts S Cnet v).μ (siteConsts S Cnet v).ν
      (siteConsts S Cnet v).r (Routing.gpC1 4))
    (hreal : IsRealizable S ℓ S.seed.A S.seed.α S.seed.β
      (siteConsts S Cnet v).t₀)
    (e : S.Edge) {x y : Rd d}
    (hx : x ∈ edgeRetainedClosed ℓ e 0 (siteConsts S Cnet v).ω \
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
  have hclear : ∀ z ∈ S.retained e 0, ∀ t ∈ Icc C.t₀ 1,
      C.r / 2 ≤ dist z (γ t) := by
    intro z hz t ht
    exact retained_arc_clearance hd ℓ e 0 γ hstar
      (Icc C.t₀ 1) (fun _ hs => ⟨le_trans ht₀ hs.1, hs.2⟩)
      hclear0 hz t ht
  have hx' : x ∈ cthickening C.ω (S.retained e 0) \
      interior (ballUnion C.μ (S.edgeCenter e)
        (labelCellIndices (ℓ e).1.gate0) C.g) :=
    ⟨edgeRetainedClosed_subset_retained_thickening ℓ e 0 C.ω hx.1, hx.2⟩
  have hy' : y ∈ ballUnion C.μ (S.edgeCenter e)
      (labelCellIndices (ℓ e).1.chamber) C.ω \
      interior (ballUnion C.μ (S.edgeCenter e)
        (labelCellIndices (ℓ e).1.gate0) C.g) := by
    exact ⟨(edgeChamberClosed_eq_ballUnion ℓ e C.ω) ▸ hy.1, hy.2⟩
  have hsep := lead_chamber_sep hμ hω ht₀ (S.edgeCenter e) γ
    (labelCellIndices (ℓ e).1.chamber)
    (labelCellIndices (ℓ e).1.gate0)
    (S.retained e 0) hstar hgate0
      (by linarith [hA.2.2.2.2.1]) hclear hx' hy'
  have hm1 := (siteConsts_sep_retained_margins S hd Cnet v hv hA).1
  have hm2 := (siteConsts_sep_local_margins S hd Cnet v hv hA).2.1
  have hδ1 : C.δsep ≤ C.r / 2 - 3 * C.ω := by linarith
  have hδ2 : C.δsep ≤ C.g - Real.sqrt d / 2 * C.μ - 2 * C.ω := by
    linarith
  exact (le_min hδ1 hδ2).trans hsep

theorem edgeRetained1_chamber_sep {d : ℕ} (S : SiteData d)
    (hd : 2 ≤ d) (Cnet v : ℝ) (hv : 0 < v)
    (hA : SiteConstsA S (siteConsts S Cnet v))
    {Kc Kl : ℕ}
    (ℓ : SiteLabel S Kc Kl (siteConsts S Cnet v).N
      (siteConsts S Cnet v).μ (siteConsts S Cnet v).ν
      (siteConsts S Cnet v).r (Routing.gpC1 4))
    (hreal : IsRealizable S ℓ S.seed.A S.seed.α S.seed.β
      (siteConsts S Cnet v).t₀)
    (e : S.Edge) {x y : Rd d}
    (hx : x ∈ edgeRetainedClosed ℓ e 1 (siteConsts S Cnet v).ω \
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
  have hclear : ∀ z ∈ S.retained e 1, ∀ t ∈ Icc C.t₀ 1,
      C.r / 2 ≤ dist z (γ (1 - t)) := by
    intro z hz t ht
    have ht' : 1 - t ∈ Icc (0 : ℝ) (1 - C.t₀) :=
      ⟨by linarith [ht.2], by linarith [ht.1]⟩
    exact retained_arc_clearance hd ℓ e 1 γ hstar
      (Icc (0 : ℝ) (1 - C.t₀))
      (fun _ hs => ⟨hs.1, by linarith [ht₀, hs.2]⟩)
      hclear1 hz (1 - t) ht'
  have hx' : x ∈ cthickening C.ω (S.retained e 1) \
      interior (ballUnion C.μ (S.edgeCenter e)
        (labelCellIndices (ℓ e).1.gate1) C.g) :=
    ⟨edgeRetainedClosed_subset_retained_thickening ℓ e 1 C.ω hx.1, hx.2⟩
  have hy' : y ∈ ballUnion C.μ (S.edgeCenter e)
      (labelCellIndices (ℓ e).1.chamber) C.ω \
      interior (ballUnion C.μ (S.edgeCenter e)
        (labelCellIndices (ℓ e).1.gate1) C.g) := by
    exact ⟨(edgeChamberClosed_eq_ballUnion ℓ e C.ω) ▸ hy.1, hy.2⟩
  have hsep := lead_chamber_sep hμ hω ht₀ (S.edgeCenter e)
    (fun t => γ (1 - t))
    (labelCellIndices (ℓ e).1.chamber)
    (labelCellIndices (ℓ e).1.gate1)
    (S.retained e 1) hstar' hgate1'
      (by linarith [hA.2.2.2.2.1]) hclear hx' hy'
  have hm1 := (siteConsts_sep_retained_margins S hd Cnet v hv hA).1
  have hm2 := (siteConsts_sep_local_margins S hd Cnet v hv hA).2.1
  have hδ1 : C.δsep ≤ C.r / 2 - 3 * C.ω := by linarith
  have hδ2 : C.δsep ≤ C.g - Real.sqrt d / 2 * C.μ - 2 * C.ω := by
    linarith
  exact (le_min hδ1 hδ2).trans hsep

theorem edgeRetained0_gate1_sep {d : ℕ} (S : SiteData d)
    (hd : 2 ≤ d) (Cnet v : ℝ) (hv : 0 < v) (hv1 : v ≤ 1)
    (hA : SiteConstsA S (siteConsts S Cnet v))
    {Kc Kl : ℕ}
    (ℓ : SiteLabel S Kc Kl (siteConsts S Cnet v).N
      (siteConsts S Cnet v).μ (siteConsts S Cnet v).ν
      (siteConsts S Cnet v).r (Routing.gpC1 4))
    (hreal : IsRealizable S ℓ S.seed.A S.seed.α S.seed.β
      (siteConsts S Cnet v).t₀)
    (e : S.Edge) {x y : Rd d}
    (hx : x ∈ edgeRetainedClosed ℓ e 0 (siteConsts S Cnet v).ω)
    (hy : y ∈ edgeGateClosed ℓ e 1 (siteConsts S Cnet v).g) :
    (siteConsts S Cnet v).δsep ≤ dist x y := by
  let C := siteConsts S Cnet v
  obtain ⟨γ, _, _, hstar, _, hgate1, hclear0, _, _, _⟩ := hreal e
  have hω : 0 < C.ω := by
    change 0 < siteOmegaCoeff d * C.ν ^ 4
    exact mul_pos (siteOmegaCoeff_pos d (by omega))
      (pow_pos (siteConsts_ν_pos S hd Cnet v) _)
  have hg : 0 < C.g := by
    change 0 < 100 * d * C.ν
    have hdR : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
    exact mul_pos (mul_pos (by norm_num) hdR) (siteConsts_ν_pos S hd Cnet v)
  have hμ : 0 ≤ C.μ := by
    change 0 ≤ C.ω ^ 2 / (2 * Real.sqrt d)
    positivity
  have hcμ : 0 ≤ Real.sqrt d / 2 * C.μ := by positivity
  have ht₀ : C.t₀ ≤ 1 / 6 := siteConsts_t₀_le_sixth S Cnet v hv hv1
  have hclear : ∀ a ∈ S.retained e 0,
      ∀ b ∈ γ '' Icc (1 - 2 * C.t₀) 1,
        C.r / 2 ≤ dist a b := by
    intro a ha b hb
    obtain ⟨t, ht, rfl⟩ := hb
    have ht' : t ∈ Icc C.t₀ 1 := ⟨by linarith [ht.1], ht.2⟩
    exact retained_arc_clearance hd ℓ e 0 γ hstar
      (Icc C.t₀ 1)
      (fun _ hs => ⟨le_trans (siteConsts_t₀_pos S Cnet v hv).le hs.1, hs.2⟩)
      hclear0 ha t ht'
  have hx' := edgeRetainedClosed_subset_retained_thickening ℓ e 0 C.ω hx
  have hy' := ballUnion_subset_hit_thickening hμ (S.edgeCenter e)
    (labelCellIndices (ℓ e).1.gate1) (γ '' Icc (1 - 2 * C.t₀) 1)
    hgate1 hy
  have hsep : C.r / 2 - C.ω - (C.g + Real.sqrt d / 2 * C.μ) ≤ dist x y :=
    dist_ge_of_two_cthickenings hω.le (by linarith :
      0 ≤ C.g + Real.sqrt d / 2 * C.μ) hclear hx' hy'
  have hm := (siteConsts_sep_retained_margins S hd Cnet v hv hA).2
  linarith

theorem edgeRetained1_gate0_sep {d : ℕ} (S : SiteData d)
    (hd : 2 ≤ d) (Cnet v : ℝ) (hv : 0 < v) (hv1 : v ≤ 1)
    (hA : SiteConstsA S (siteConsts S Cnet v))
    {Kc Kl : ℕ}
    (ℓ : SiteLabel S Kc Kl (siteConsts S Cnet v).N
      (siteConsts S Cnet v).μ (siteConsts S Cnet v).ν
      (siteConsts S Cnet v).r (Routing.gpC1 4))
    (hreal : IsRealizable S ℓ S.seed.A S.seed.α S.seed.β
      (siteConsts S Cnet v).t₀)
    (e : S.Edge) {x y : Rd d}
    (hx : x ∈ edgeRetainedClosed ℓ e 1 (siteConsts S Cnet v).ω)
    (hy : y ∈ edgeGateClosed ℓ e 0 (siteConsts S Cnet v).g) :
    (siteConsts S Cnet v).δsep ≤ dist x y := by
  let C := siteConsts S Cnet v
  obtain ⟨γ, _, _, hstar, hgate0, _, _, hclear1, _, _⟩ := hreal e
  have hω : 0 < C.ω := by
    change 0 < siteOmegaCoeff d * C.ν ^ 4
    exact mul_pos (siteOmegaCoeff_pos d (by omega))
      (pow_pos (siteConsts_ν_pos S hd Cnet v) _)
  have hg : 0 < C.g := by
    change 0 < 100 * d * C.ν
    have hdR : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
    exact mul_pos (mul_pos (by norm_num) hdR) (siteConsts_ν_pos S hd Cnet v)
  have hμ : 0 ≤ C.μ := by
    change 0 ≤ C.ω ^ 2 / (2 * Real.sqrt d)
    positivity
  have hcμ : 0 ≤ Real.sqrt d / 2 * C.μ := by positivity
  have ht₀ : C.t₀ ≤ 1 / 6 := siteConsts_t₀_le_sixth S Cnet v hv hv1
  have hclear : ∀ a ∈ S.retained e 1,
      ∀ b ∈ γ '' Icc 0 (2 * C.t₀),
        C.r / 2 ≤ dist a b := by
    intro a ha b hb
    obtain ⟨t, ht, rfl⟩ := hb
    have ht' : t ∈ Icc 0 (1 - C.t₀) := ⟨ht.1, by linarith [ht.2]⟩
    exact retained_arc_clearance hd ℓ e 1 γ hstar
      (Icc (0 : ℝ) (1 - C.t₀))
      (fun _ hs => ⟨hs.1, by linarith [(siteConsts_t₀_pos S Cnet v hv).le, hs.2]⟩)
      hclear1 ha t ht'
  have hx' := edgeRetainedClosed_subset_retained_thickening ℓ e 1 C.ω hx
  have hy' := ballUnion_subset_hit_thickening hμ (S.edgeCenter e)
    (labelCellIndices (ℓ e).1.gate0) (γ '' Icc 0 (2 * C.t₀))
    hgate0 hy
  have hsep : C.r / 2 - C.ω - (C.g + Real.sqrt d / 2 * C.μ) ≤ dist x y :=
    dist_ge_of_two_cthickenings hω.le (by linarith :
      0 ≤ C.g + Real.sqrt d / 2 * C.μ) hclear hx' hy'
  have hm := (siteConsts_sep_retained_margins S hd Cnet v hv hA).2
  linarith

end HigherDimLQGContinuity
