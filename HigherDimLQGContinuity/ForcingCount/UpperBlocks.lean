import HigherDimLQGContinuity.ForcingCount.Lower
import HigherDimLQGContinuity.Forcing.Forcing
import HigherDimLQGContinuity.Discharge.Lemma43Confine

/-!
# One output geodesic: the forcing block and the collector interval of an active site

Packet Q9, Part B `b:lem-upcount` step (1) ([C] p. 19–20, l. 973–993; NA2 items 22–23, R13). Let `h` be a good field
and `Z` a selection with `h + f_Z ∈ A_Z` (only the site clauses are used here). For `(i, ℓ) ∈ Z`, the single-site
source `H* = h + f_i` reproduces the validity, the unit and the trigger of `i` (locality of the source predicate,
Weyl scaling, `f_Z = f_i` on `B̄_{4s}(z_i)`, sphere averages unchanged); the certificate of `ℓ` at `H*`, the Weyl
relations to `h` and Lemma 4.3 (`lemma43_forcing_holds`, `lemma43_confine_holds`) give, along the canonical geodesic
`P_h`, a block `[σ, τ]` inside the inspection with `ρ^D_h(P σ, P τ) ≥ c_seed Q` and secondary cost
`≤ (1 + 6v) e^{2Ω} ρ^D_h(P σ, P τ)` in `B_{4s}(z_i)`, and the first-to-last collector interval inside the inspection.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd e₁)

variable {d : ℕ}

section Blocks

variable {K : CountData d} {𝔆 : Catalogue d} {Hup sR Hlo b mc A0 d₀ Ap kp v θ ς δsep εnet εatt : ℝ}

theorem q9_bump_zero_on_sphere {ψ : C(Rd d, ℝ)} {M : ℝ} {z : Rd d} {s : ℝ} (hs : 0 < s)
    (hψ : tsupport ψ ⊆ siteC d) : ∀ x ∈ sphere z s, q9Bump ψ M z s x = 0 :=
  fun _ hx => q9Bump_eq_zero_of_notMem hs hψ (q9_sphere_disjoint_annCl hs hx)

theorem q9_ann_subset_closedBall {z : Rd d} {s : ℝ} (hs : 0 < s) :
    ann z (s / 2) (7 * s / 2) ⊆ closedBall z (4 * s) := by
  intro x hx
  simp only [ann, mem_ofPred_eq] at hx
  rw [mem_closedBall, dist_eq_norm]
  linarith [hx.2]

/-- **Step (1) of the upper count** for one labelled site of an active selection. -/
theorem q9_site_block (hK : CountHyp K 𝔆 Hup sR Hlo b mc A0 d₀ Ap kp v θ ς δsep εnet εatt)
    {h : DistRd d} (hG : CountGood K 𝔆 h) {Z : Finset (Rd d × K.cat.Label)} (hZsel : IsSelection 𝔆 Z)
    (hZsub : Z ⊆ countUnivSites K 𝔆) {p : Rd d × K.cat.Label} (hp : p ∈ Z)
    (hsrc : K.cat.Source p.2 (countSiteD K 𝔆.s p.1 (addFun h (selBump K 𝔆.s Z)))
      (countSiteE K 𝔆.s p.1 (addFun h (selBump K 𝔆.s Z))))
    (hunit : countUnit K 𝔆.s p.1 (addFun h (selBump K 𝔆.s Z)) ∈ Icc 𝔆.Q (2 * 𝔆.Q))
    (htrig : PassesTrigger (countSiteD K 𝔆.s p.1 (addFun h (selBump K 𝔆.s Z)))
      (q9SitePath (q9Path K.D K.x K.y h) p.1 𝔆.s) 0 1 K.btrig) :
    (∃ σ τ : ℝ, 0 ≤ σ ∧ σ ≤ τ ∧ τ ≤ 1 ∧
      (∀ t ∈ Icc σ τ, q9Path K.D K.x K.y h t ∈ ann p.1 (𝔆.s / 2) (7 * 𝔆.s / 2)) ∧
      θ * d₀ / 2 * 𝔆.Q ≤ (rho K.D h).1 (q9Path K.D K.x K.y h σ, q9Path K.D K.x K.y h τ) ∧
      (rho K.E h).internal (ball p.1 (4 * 𝔆.s)) (q9Path K.D K.x K.y h σ) (q9Path K.D K.x K.y h τ) ≤
        ENNReal.ofReal ((1 + 6 * v) * Real.exp (2 * (v / 100)) *
          (rho K.D h).1 (q9Path K.D K.x K.y h σ, q9Path K.D K.x K.y h τ))) ∧
    (∃ u₀ v₀ : ℝ, 0 ≤ u₀ ∧ u₀ ≤ v₀ ∧ v₀ ≤ 1 ∧
      q9Path K.D K.x K.y h u₀ ∈ annCl p.1 (3 * 𝔆.s / 2) (5 * 𝔆.s / 2) ∧
      q9Path K.D K.x K.y h v₀ ∈ annCl p.1 (3 * 𝔆.s / 2) (5 * 𝔆.s / 2) ∧
      (∀ t ∈ Icc u₀ v₀, q9Path K.D K.x K.y h t ∈ ann p.1 (𝔆.s / 2) (7 * 𝔆.s / 2)) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, q9Path K.D K.x K.y h t ∈ annCl p.1 (3 * 𝔆.s / 2) (5 * 𝔆.s / 2) →
        u₀ ≤ t ∧ t ≤ v₀) := by
  have hs := hK.s_pos
  obtain ⟨z, ℓ⟩ := p
  simp only at hsrc hunit htrig ⊢
  have hzZ : z ∈ 𝔆.Z := hZsel.1 _ hp
  set fZ := selBump K 𝔆.s Z with hfZ
  set fi := q9Bump (K.cat.prof ℓ) K.M z 𝔆.s with hfi
  have hh0 := hG.base
  have hH₁ : q9GoodInput K (addFun h fZ) := hG.pos hZsub
  have hsingle : ({(z, ℓ)} : Finset (Rd d × K.cat.Label)) ⊆ countUnivSites K 𝔆 :=
    Finset.singleton_subset_iff.2 (hZsub hp)
  have hHs : q9GoodInput K (addFun h fi) := by
    have := hG.pos hsingle
    rwa [selBump_singleton] at this
  obtain ⟨a, ha⟩ := hG.2 z hzZ
  -- (1a) units
  have hSZ : countUnit K 𝔆.s z (addFun h fZ) = countUnit K 𝔆.s z h :=
    q9_scaleS_addFun_eq hs ha (fun x hx => selBump_zero_on_sphere hK.valid hK.prof_tsupport hZsel hzZ hx)
  have hSi : countUnit K 𝔆.s z (addFun h fi) = countUnit K 𝔆.s z h :=
    q9_scaleS_addFun_eq hs ha (q9_bump_zero_on_sphere hs (hK.prof_tsupport ℓ))
  set S := countUnit K 𝔆.s z h with hSdef
  have hS : 0 < S := countUnit_pos K hs z h
  -- (1b) the two sources agree in `B_{4s}(z)`
  have heqball : ∀ x ∈ ball z (4 * 𝔆.s), fZ x = fi x := fun x hx =>
    selBump_eq_on_ball hK.valid hK.prof_tsupport hZsel hp (ball_subset_closedBall hx)
  have hintD : ∀ u w, (rho K.D (addFun h fZ)).internal (ball z (4 * 𝔆.s)) u w =
      (rho K.D (addFun h fi)).internal (ball z (4 * 𝔆.s)) u w := by
    intro u w
    rw [hh0.weylD fZ _ isOpen_ball, hh0.weylD fi _ isOpen_ball]
    exact weylScaleOn_congr fun x hx => by rw [heqball x hx]
  have hintE : ∀ u w, (rho K.E (addFun h fZ)).internal (ball z (4 * 𝔆.s)) u w =
      (rho K.E (addFun h fi)).internal (ball z (4 * 𝔆.s)) u w := by
    intro u w
    rw [hh0.weylE fZ _ isOpen_ball, hh0.weylE fi _ isOpen_ball]
    exact weylScaleOn_congr fun x hx => by rw [heqball x hx]
  have hDB : ∀ u w, (countSiteD K 𝔆.s z (addFun h fZ)).internal (siteB d) u w =
      (countSiteD K 𝔆.s z (addFun h fi)).internal (siteB d) u w := by
    intro u w
    simp only [countSiteD, hSZ, hSi]
    exact q9SiteNorm_internal_siteB_congr hs hS hintD u w
  have hEB : ∀ u w, (countSiteE K 𝔆.s z (addFun h fZ)).internal (siteB d) u w =
      (countSiteE K 𝔆.s z (addFun h fi)).internal (siteB d) u w := by
    intro u w
    simp only [countSiteE, hSZ, hSi]
    exact q9SiteNorm_internal_siteB_congr hs hS hintE u w
  -- (1c), (1d) validity and trigger at the single-site source
  have hsrc' : K.cat.Source ℓ (countSiteD K 𝔆.s z (addFun h fi)) (countSiteE K 𝔆.s z (addFun h fi)) :=
    (hK.contract.local_ ℓ _ _ _ _ hDB hEB).1 hsrc
  have htrig' : PassesTrigger (countSiteD K 𝔆.s z (addFun h fi)) (q9SitePath (q9Path K.D K.x K.y h) z 𝔆.s)
      0 1 K.btrig := (q9_passesTrigger_congr hDB _ _ _ _).1 htrig
  -- (1e) the certificate
  have hDlen : (countSiteD K 𝔆.s z (addFun h fi)).IsLength := q9SiteNorm_isLength hHs.1 _ _ _
  obtain ⟨cert⟩ := hK.cert_fun ℓ hDlen hsrc'
  -- (1f) Weyl relations to the field `h`
  have hback : addFun (addFun h fi) (-fi) = h := addFun_neg h fi
  have hWD : IsWeylInternal K.ξ (-(K.M • K.cat.prof ℓ)) (countSiteD K 𝔆.s z (addFun h fi))
      (q9SiteNorm (rho K.D h) z 𝔆.s S) := by
    have h1 := isWeylInternal_q9SiteNorm (G := rho K.D (addFun h fi)) (G' := rho K.D h) (F := -fi)
      (fun U hU u w => by have := hHs.weylD (-fi) U hU u w; rwa [hback] at this) (z := z) hs hS
    rw [hfi, q9_neg_bump_comp_aff _ _ _ hs] at h1
    simp only [countSiteD, hSi]
    exact h1
  have hWE : IsWeylInternal K.η (-(K.M • K.cat.prof ℓ)) (countSiteE K 𝔆.s z (addFun h fi))
      (q9SiteNorm (rho K.E h) z 𝔆.s S) := by
    have h1 := isWeylInternal_q9SiteNorm (G := rho K.E (addFun h fi)) (G' := rho K.E h) (F := -fi)
      (fun U hU u w => by have := hHs.weylE (-fi) U hU u w; rwa [hback] at this) (z := z) hs hS
    rw [hfi, q9_neg_bump_comp_aff _ _ _ hs] at h1
    simp only [countSiteE, hSi]
    exact h1
  -- (1g) the geodesic in site coordinates
  obtain ⟨h0, h1, hgeo⟩ := hh0.path
  set P := q9Path K.D K.x K.y h with hPdef
  have hgeo' : IsGeodSeg (q9SiteNorm (rho K.D h) z 𝔆.s S) (q9SitePath P z 𝔆.s) 0 1 :=
    isGeodSeg_q9SiteNorm hs hS hgeo
  have hx := (hK.valid.2.2.2.1 z hzZ).2.1
  have hy := (hK.valid.2.2.2.1 z hzZ).2.2
  have h0' : q9SitePath P z 𝔆.s 0 ∉ siteB d := by
    rw [q9SitePath_mem_iff hs, q9Aff_image_siteB hs, h0]
    exact fun hm => hx (ball_subset_closedBall hm)
  have h1' : q9SitePath P z 𝔆.s 1 ∉ siteB d := by
    rw [q9SitePath_mem_iff hs, q9Aff_image_siteB hs, h1]
    exact fun hm => hy (ball_subset_closedBall hm)
  have hF2 := q9_siteF2 hK.mc_pos hK.Hlo_ge
  have htrig'' : PassesTrigger (countSiteD K 𝔆.s z (addFun h fi)) (q9SitePath P z 𝔆.s) 0 1
      (siteBtrig mc Hlo) := by rw [← hK.btrig_eq]; exact htrig'
  -- (1h) Lemma 4.3(b)
  obtain ⟨σ, τ, hσ0, hστ, hτ1, hA, hlen, hcost⟩ := lemma43_forcing_holds d cert hWD hWE
    hK.ξ_pos.le hK.η_pos.le hK.d₀_pos hK.mismatch hK.v_pos hK.v_le le_rfl hF2.2.1 hK.contract.net
    hF2.2.2.1 hK.contract.sep hK.contract.budget (q9SitePath P z 𝔆.s) 0 1 hgeo' h0' h1' htrig''
  -- (1j) Lemma 4.3(a)
  have hvisit : ∃ t ∈ Icc (0 : ℝ) 1, q9SitePath P z 𝔆.s t ∈ siteC d := htrig''.1
  obtain ⟨hu0, hv0, -, hconf⟩ := lemma43_confine_holds d cert hWD hWE hK.ξ_pos.le hK.η_pos.le hK.d₀_pos
    hK.mismatch hK.v_pos hK.v_le le_rfl hF2.2.1 hK.contract.net hK.contract.sep hK.contract.budget
    (q9SitePath P z 𝔆.s) 0 1 hgeo' h0' h1' hvisit
  obtain ⟨hfirst, hPfirst, hlast, hPlast, hfl⟩ :=
    q6_visit_times (continuousOn_q9SitePath hgeo.2.1) (q6_siteC_closed d) hvisit
  refine ⟨⟨σ, τ, hσ0, hστ, hτ1, fun t ht => (q9_sitePath_mem_siteA_iff hs t).1 (hA t ht), ?_, ?_⟩,
    ⟨firstVisit (q9SitePath P z 𝔆.s) 0 1 (siteC d), lastVisit (q9SitePath P z 𝔆.s) 0 1 (siteC d),
      hfirst.1, hfl, hlast.2, (q9_sitePath_mem_siteC_iff hs _).1 hPfirst,
      (q9_sitePath_mem_siteC_iff hs _).1 hPlast, fun t ht => (q9_sitePath_mem_siteA_iff hs t).1
        (hconf t ht), fun t ht hPt => ?_⟩⟩
  · -- block length
    rw [q9SiteNorm_len_sitePath hs hS, q6_geod_subsegment hgeo hσ0 hστ hτ1,
      ← ENNReal.ofReal_mul (inv_nonneg.2 hS.le)] at hlen
    have hlen' := (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (inv_nonneg.2 hS.le)
      ((rho K.D h).nonneg _ _))).1 hlen
    have hmul := mul_le_mul_of_nonneg_left hlen' hS.le
    rw [← mul_assoc, mul_inv_cancel₀ hS.ne', one_mul] at hmul
    have hSQ : 𝔆.Q ≤ S := by rw [← hSZ]; exact hunit.1
    have hθ : 0 ≤ θ * d₀ / 2 := by have := hK.θ_pos; have := hK.d₀_pos; positivity
    nlinarith
  · -- secondary cost
    rw [q9SiteNorm_internal hs hS, q9Aff_image_siteB hs, q9Aff_apply_sitePath hs, q9Aff_apply_sitePath hs,
      q9SiteNorm_len_sitePath hs hS, q6_geod_subsegment hgeo hσ0 hστ hτ1] at hcost
    have hc0 : 0 ≤ (1 + 6 * v) * Real.exp (2 * (v / 100)) := by
      have := hK.v_pos
      positivity
    calc (rho K.E h).internal (ball z (4 * 𝔆.s)) (P σ) (P τ)
        = ENNReal.ofReal S * (ENNReal.ofReal S⁻¹ * (rho K.E h).internal (ball z (4 * 𝔆.s)) (P σ) (P τ)) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hS.le, mul_inv_cancel₀ hS.ne', ENNReal.ofReal_one,
            one_mul]
      _ ≤ ENNReal.ofReal S * (ENNReal.ofReal ((1 + 6 * v) * Real.exp (2 * (v / 100))) *
            (ENNReal.ofReal S⁻¹ * ENNReal.ofReal ((rho K.D h).1 (P σ, P τ)))) := by gcongr
      _ = ENNReal.ofReal ((1 + 6 * v) * Real.exp (2 * (v / 100)) * (rho K.D h).1 (P σ, P τ)) := by
          rw [← ENNReal.ofReal_mul (inv_nonneg.2 hS.le), ← ENNReal.ofReal_mul hc0,
            ← ENNReal.ofReal_mul hS.le]
          congr 1
          field_simp
  · -- every collector visit lies in the collector interval
    have hmem : t ∈ {t | t ∈ Icc (0 : ℝ) 1 ∧ q9SitePath P z 𝔆.s t ∈ siteC d} :=
      ⟨ht, (q9_sitePath_mem_siteC_iff hs t).2 hPt⟩
    exact ⟨csInf_le ⟨0, fun _ h => h.1.1⟩ hmem, le_csSup ⟨1, fun _ h => h.1.2⟩ hmem⟩

end Blocks

end HigherDimLQGContinuity
