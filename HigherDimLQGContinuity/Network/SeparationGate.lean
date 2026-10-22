import HigherDimLQGContinuity.Network.SeparationLocal
import HigherDimLQGContinuity.Routing.ArcModuli

/-! # A lead versus its opposite gate -/

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open Set Metric
open HigherDimLFPP (Rd)

namespace HigherDimLQGContinuity

theorem edgeLead0_gate1_sep {d : ℕ} (S : SiteData d)
    (hd : 2 ≤ d) (Cnet v : ℝ) (hv : 0 < v) (hv1 : v ≤ 1)
    (hA : SiteConstsA S (siteConsts S Cnet v))
    {Kc Kl : ℕ}
    (ℓ : SiteLabel S Kc Kl (siteConsts S Cnet v).N
      (siteConsts S Cnet v).μ (siteConsts S Cnet v).ν
      (siteConsts S Cnet v).r (Routing.gpC1 4))
    (hreal : IsRealizable S ℓ S.seed.A S.seed.α S.seed.β
      (siteConsts S Cnet v).t₀)
    (e : S.Edge) {x y : Rd d}
    (hx : x ∈ edgeLeadClosed ℓ e 0 (siteConsts S Cnet v).ω)
    (hy : y ∈ edgeGateClosed ℓ e 1 (siteConsts S Cnet v).g) :
    (siteConsts S Cnet v).δsep ≤ dist x y := by
  let C := siteConsts S Cnet v
  obtain ⟨γ, _, _, _, _, hgate1, hclear0, _, _, _⟩ := hreal e
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
  have ht₀ := siteConsts_t₀_le_sixth S Cnet v hv hv1
  change C.t₀ ≤ 1 / 6 at ht₀
  have hx' := edgeLeadClosed_subset_trace_thickening ℓ e 0 C.ω hx
  have hy' := ballUnion_subset_hit_thickening hμ (S.edgeCenter e)
    (labelCellIndices (ℓ e).1.gate1) (γ '' Icc (1 - 2 * C.t₀) 1)
    hgate1 hy
  have hclear : ∀ a ∈ (ℓ e).1.lead0.trace C.ν,
      ∀ b ∈ γ '' Icc (1 - 2 * C.t₀) 1, C.r ≤ dist a b := by
    intro a ha b hb
    obtain ⟨t, ht, rfl⟩ := hb
    have hlow : C.t₀ ≤ t := by linarith [ht.1]
    exact hclear0 a ha t ⟨hlow, ht.2⟩
  have hsep : C.r - C.ω - (C.g + Real.sqrt d / 2 * C.μ) ≤ dist x y :=
    dist_ge_of_two_cthickenings hω.le (by linarith :
      0 ≤ C.g + Real.sqrt d / 2 * C.μ) hclear hx' hy'
  have hmargin := (siteConsts_sep_local_margins S hd Cnet v hv hA).2.2
  linarith

theorem edgeLead1_gate0_sep {d : ℕ} (S : SiteData d)
    (hd : 2 ≤ d) (Cnet v : ℝ) (hv : 0 < v) (hv1 : v ≤ 1)
    (hA : SiteConstsA S (siteConsts S Cnet v))
    {Kc Kl : ℕ}
    (ℓ : SiteLabel S Kc Kl (siteConsts S Cnet v).N
      (siteConsts S Cnet v).μ (siteConsts S Cnet v).ν
      (siteConsts S Cnet v).r (Routing.gpC1 4))
    (hreal : IsRealizable S ℓ S.seed.A S.seed.α S.seed.β
      (siteConsts S Cnet v).t₀)
    (e : S.Edge) {x y : Rd d}
    (hx : x ∈ edgeLeadClosed ℓ e 1 (siteConsts S Cnet v).ω)
    (hy : y ∈ edgeGateClosed ℓ e 0 (siteConsts S Cnet v).g) :
    (siteConsts S Cnet v).δsep ≤ dist x y := by
  let C := siteConsts S Cnet v
  obtain ⟨γ, _, _, _, hgate0, _, _, hclear1, _, _⟩ := hreal e
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
  have ht₀ := siteConsts_t₀_le_sixth S Cnet v hv hv1
  change C.t₀ ≤ 1 / 6 at ht₀
  have hx' := edgeLeadClosed_subset_trace_thickening ℓ e 1 C.ω hx
  have hy' := ballUnion_subset_hit_thickening hμ (S.edgeCenter e)
    (labelCellIndices (ℓ e).1.gate0) (γ '' Icc 0 (2 * C.t₀))
    hgate0 hy
  have hclear : ∀ a ∈ (ℓ e).1.lead1.trace C.ν,
      ∀ b ∈ γ '' Icc 0 (2 * C.t₀), C.r ≤ dist a b := by
    intro a ha b hb
    obtain ⟨t, ht, rfl⟩ := hb
    have hupp : t ≤ 1 - C.t₀ := by linarith [ht.2]
    exact hclear1 a ha t ⟨ht.1, hupp⟩
  have hsep : C.r - C.ω - (C.g + Real.sqrt d / 2 * C.μ) ≤ dist x y :=
    dist_ge_of_two_cthickenings hω.le (by linarith :
      0 ≤ C.g + Real.sqrt d / 2 * C.μ) hclear hx' hy'
  have hmargin := (siteConsts_sep_local_margins S hd Cnet v hv hA).2.2
  linarith

/-- The clearance radius is far smaller than the distance between the two
parameter tails of a realizing arc. -/
theorem siteConsts_r_le_arc_tail {d : ℕ} (S : SiteData d)
    (hd : 2 ≤ d) (Cnet v : ℝ) (hv : 0 < v) (hv1 : v ≤ 1) :
    let C := siteConsts S Cnet v
    C.r ≤ ((1 - 4 * C.t₀) / S.seed.A) ^ S.seed.β⁻¹ := by
  let C := siteConsts S Cnet v
  have hA : 0 < S.seed.A := by linarith [S.seed.A_ge]
  have hβ : 0 < S.seed.β := S.seed.β_pos
  have ht₀ : 0 < C.t₀ := siteConsts_t₀_pos S Cnet v hv
  have ht₀six : C.t₀ ≤ 1 / 6 := siteConsts_t₀_le_sixth S Cnet v hv hv1
  have hL : 0 < S.boxHalfSide := S.boxHalfSide_pos hd
  have hL1 : S.boxHalfSide ≤ 1 := S.boxHalfSide_le_one hd
  have hlead := Routing.ten_leadR_le S.seed.A_ge
    S.seed.α_pos S.seed.α_le S.seed.β_pos S.seed.β_le
    ht₀ hL hL1
  have hrU : C.r ≤ Routing.leadU S.seed.A S.seed.β S.boxHalfSide C.t₀ / 20 := by
    change 10 * C.r ≤ Routing.leadU S.seed.A S.seed.β S.boxHalfSide C.t₀ / 2 at hlead
    linarith
  have hUle := Routing.leadU_le_pow
    (A := S.seed.A) (β := S.seed.β) (L := S.boxHalfSide) (t₀ := C.t₀)
  have hbase : C.t₀ / (2 * S.seed.A) ≤ (1 - 4 * C.t₀) / S.seed.A := by
    have hnum : C.t₀ / 2 ≤ 1 - 4 * C.t₀ := by linarith
    have h := div_le_div_of_nonneg_right hnum hA.le
    calc
      C.t₀ / (2 * S.seed.A) = (C.t₀ / 2) / S.seed.A := by ring
      _ ≤ (1 - 4 * C.t₀) / S.seed.A := h
  have hpow : (C.t₀ / (2 * S.seed.A)) ^ S.seed.β⁻¹ ≤
      ((1 - 4 * C.t₀) / S.seed.A) ^ S.seed.β⁻¹ :=
    Real.rpow_le_rpow (by positivity) hbase (inv_nonneg.mpr hβ.le)
  have hpow0 : 0 ≤ (C.t₀ / (2 * S.seed.A)) ^ S.seed.β⁻¹ := by positivity
  exact (hrU.trans (by linarith [hUle])).trans hpow

/-- The two closed gate nodes of one edge have a positive gap. -/
theorem edgeGateClosed_cross_sep {d : ℕ} (S : SiteData d)
    (hd : 2 ≤ d) (Cnet v : ℝ) (hv : 0 < v) (hv1 : v ≤ 1)
    (hA : SiteConstsA S (siteConsts S Cnet v))
    {Kc Kl : ℕ}
    (ℓ : SiteLabel S Kc Kl (siteConsts S Cnet v).N
      (siteConsts S Cnet v).μ (siteConsts S Cnet v).ν
      (siteConsts S Cnet v).r (Routing.gpC1 4))
    (hreal : IsRealizable S ℓ S.seed.A S.seed.α S.seed.β
      (siteConsts S Cnet v).t₀)
    (e : S.Edge) {x y : Rd d}
    (hx : x ∈ edgeGateClosed ℓ e 0 (siteConsts S Cnet v).g)
    (hy : y ∈ edgeGateClosed ℓ e 1 (siteConsts S Cnet v).g) :
    (siteConsts S Cnet v).δsep ≤ dist x y := by
  let C := siteConsts S Cnet v
  obtain ⟨γ, hmod, _, _, hgate0, hgate1, _, _, _, _⟩ := hreal e
  have hμ : 0 ≤ C.μ := by
    change 0 ≤ C.ω ^ 2 / (2 * Real.sqrt d)
    positivity
  have hcμ : 0 ≤ Real.sqrt d / 2 * C.μ := by positivity
  have hg : 0 < C.g := by
    change 0 < 100 * d * C.ν
    have hdR : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
    exact mul_pos (mul_pos (by norm_num) hdR) (siteConsts_ν_pos S hd Cnet v)
  have hgate0' := ballUnion_subset_hit_thickening hμ (S.edgeCenter e)
    (labelCellIndices (ℓ e).1.gate0) (γ '' Icc 0 (2 * C.t₀)) hgate0 hx
  have hgate1' := ballUnion_subset_hit_thickening hμ (S.edgeCenter e)
    (labelCellIndices (ℓ e).1.gate1) (γ '' Icc (1 - 2 * C.t₀) 1) hgate1 hy
  let ρ := ((1 - 4 * C.t₀) / S.seed.A) ^ S.seed.β⁻¹
  have hρ : ∀ a ∈ γ '' Icc 0 (2 * C.t₀),
      ∀ b ∈ γ '' Icc (1 - 2 * C.t₀) 1, ρ ≤ dist a b := by
    intro a ha b hb
    obtain ⟨t, ht, rfl⟩ := ha
    obtain ⟨u, hu, rfl⟩ := hb
    have ht₀ : C.t₀ ≤ 1 / 4 := by
      have := siteConsts_t₀_le_sixth S Cnet v hv hv1
      linarith
    have h := Routing.arcModuli_tails_sep hmod
      (by linarith [S.seed.A_ge]) S.seed.β_pos ht₀ ht hu
    simpa only [ρ, dist_eq_norm] using h
  have hsep : ρ - (C.g + Real.sqrt d / 2 * C.μ) -
      (C.g + Real.sqrt d / 2 * C.μ) ≤ dist x y :=
    dist_ge_of_two_cthickenings (by linarith) (by linarith) hρ hgate0' hgate1'
  have hrρ := siteConsts_r_le_arc_tail S hd Cnet v hv hv1
  change C.r ≤ ρ at hrρ
  have hr : 0 < C.r := siteConsts_r_pos S hd Cnet v hv
  have hδr : C.δsep ≤ C.r / 2 :=
    (le_min_iff.mp hA.2.2.2.2.2.1).1
  have hgr : C.g ≤ C.r / 8 := hA.2.2.1
  have hcμω : Real.sqrt d / 2 * C.μ ≤ C.ω / 4 := hA.2.2.2.2.1
  have hωr : C.ω ≤ C.r / 8 := by
    have hroot : 1 ≤ Real.sqrt d := Real.one_le_sqrt.mpr
      (by exact_mod_cast (show 1 ≤ d by omega))
    have hraw := (le_min_iff.mp hA.2.2.2.1).1
    have hmul := (le_div_iff₀ (by positivity : 0 < 8 * Real.sqrt d)).mp hraw
    nlinarith
  linarith

end HigherDimLQGContinuity
