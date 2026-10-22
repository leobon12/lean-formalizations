import HigherDimLQGContinuity.ForcingCount.Hyp
import HigherDimLQGContinuity.ForcingCount.Chain
import HigherDimLQGContinuity.Restore.Geometry
import HigherDimLQGContinuity.Forcing.Weights
import HigherDimLQGContinuity.Forcing.Shortcut

/-!
# The three inputs of the pruning (Part B `b:lem-lowmult`, (h1)–(h3))

Packet Q9 (deterministic, on good inputs). For a field `H` and a set `t` of eligible sites with valid labels:

* (h1) `q9_saving`: `ρ^D_{H - f_t}(x, y) + a₀ ∑_{i ∈ t} S_i ≤ ρ^D_H(x, y)`, from the single-site network saving
  (Q8a's `network_saving`) on the exit intervals of `P_H` from the full inspections, the monotonicity of the Weyl
  discount and the chain bound;
* (h2) `q9_trigger_removal`: a failing trigger at a site costs at most `btrig S_i` (Q8a's `trigger_removal`);
* (h3) `q9_restoration`: `ρ^D_H(x, y) ≤ ρ^D_{H - f_Z}(x, y) + A₀ ∑_{i ∈ Z} S_i` (Q8a's
  `chronological_restoration` with the collector diameters (R4)).
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

theorem q9GoodInput.weylD {K : CountData d} {X : DistRd d} (hX : q9GoodInput K X) (g : C(Rd d, ℝ)) :
    IsWeylInternal K.ξ g (rho K.D X) (rho K.D (addFun X g)) :=
  fun U hU u v => hX.2.2.2.1 g U hU u v

theorem q9GoodInput.weylE {K : CountData d} {X : DistRd d} (hX : q9GoodInput K X) (g : C(Rd d, ℝ)) :
    IsWeylInternal K.η g (rho K.E X) (rho K.E (addFun X g)) :=
  fun U hU u v => hX.2.2.2.2 g U hU u v

/-- A larger nonnegative discount gives a smaller distance (both modified metrics length metrics). -/
theorem q9_rho_le_of_discount {K : CountData d} {X : DistRd d} (hX : q9GoodInput K X) (hξ : 0 ≤ K.ξ)
    {f₁ f₂ : C(Rd d, ℝ)} (h12 : ∀ x, f₂ x ≤ f₁ x) (hl₁ : (rho K.D (addFun X (-f₁))).IsLength)
    (hl₂ : (rho K.D (addFun X (-f₂))).IsLength) (u v : Rd d) :
    (rho K.D (addFun X (-f₁))).1 (u, v) ≤ (rho K.D (addFun X (-f₂))).1 (u, v) := by
  have h₁ : ENNReal.ofReal ((rho K.D (addFun X (-f₁))).1 (u, v)) = weylScale K.ξ (-f₁) (rho K.D X) u v := by
    rw [← ContMetric.internal_univ_of_isLength _ hl₁, hX.weylD (-f₁) univ isOpen_univ, weylScaleOn_univ]
  have h₂ : ENNReal.ofReal ((rho K.D (addFun X (-f₂))).1 (u, v)) = weylScale K.ξ (-f₂) (rho K.D X) u v := by
    rw [← ContMetric.internal_univ_of_isLength _ hl₂, hX.weylD (-f₂) univ isOpen_univ, weylScaleOn_univ]
  have hle : weylScale K.ξ (-f₁) (rho K.D X) u v ≤ weylScale K.ξ (-f₂) (rho K.D X) u v :=
    weylScale_mono_of_le hξ fun x => by simpa only [ContinuousMap.neg_apply, neg_le_neg_iff] using h12 x
  rw [← h₁, ← h₂] at hle
  exact (ENNReal.ofReal_le_ofReal_iff ((rho K.D (addFun X (-f₂))).nonneg u v)).1 hle

theorem q9_neg_bump_comp_aff (ψ : C(Rd d, ℝ)) (M : ℝ) (z : Rd d) {s : ℝ} (hs : 0 < s) :
    (-q9Bump ψ M z s).comp (ContMetric.affineMap s z) = -(M • ψ) := by
  rw [← q9Bump_comp_aff ψ M z hs]
  ext u
  simp only [ContinuousMap.comp_apply, ContinuousMap.neg_apply]

theorem q9_tsupport_smul (c : ℝ) (g : C(Rd d, ℝ)) : tsupport ⇑(c • g) ⊆ tsupport ⇑g := by
  have h : ⇑(c • g) = fun x => (fun _ => c) x • g x := by
    funext x
    rfl
  rw [h]
  exact tsupport_smul_subset_right _ _

theorem q9_smul_prof_nonneg {c : ℝ} (hc : 0 ≤ c) {g : C(Rd d, ℝ)} (hg : ∀ x, 0 ≤ g x) (x : Rd d) :
    0 ≤ (c • g) x := by
  rw [ContinuousMap.smul_apply, smul_eq_mul]
  exact mul_nonneg hc (hg x)

section Steps

variable {K : CountData d} {𝔆 : Catalogue d} {Hup sR Hlo b mc A0 d₀ Ap kp v θ ς δsep εnet εatt : ℝ}

/-- **Single-site saving** on an exit interval of a geodesic from the full inspection of a site. -/
theorem q9_site_saving (hK : CountHyp K 𝔆 Hup sR Hlo b mc A0 d₀ Ap kp v θ ς δsep εnet εatt)
    {X : DistRd d} (hX : q9GoodInput K X) {z : Rd d} {ℓ : K.cat.Label}
    (hsrc : K.cat.Source ℓ (countSiteD K 𝔆.s z X) (countSiteE K 𝔆.s z X))
    {P : ℝ → Rd d} {u w : ℝ} (hgeo : IsGeodSeg (rho K.D X) P u w)
    (hu : P u ∉ ball z (4 * 𝔆.s)) (hw : P w ∉ ball z (4 * 𝔆.s))
    (hcore : ∃ t ∈ Icc u w, P t ∈ closedBall z (3 * 𝔆.s / 2)) :
    (rho K.D (addFun X (-q9Bump (K.cat.prof ℓ) K.M z 𝔆.s))).1 (P u, P w) +
      q9SiteA0 mc Hlo * countUnit K 𝔆.s z X ≤ (rho K.D X).1 (P u, P w) := by
  have hs := hK.s_pos
  set S := countUnit K 𝔆.s z X with hSdef
  have hS : 0 < S := countUnit_pos K hs z X
  set f := q9Bump (K.cat.prof ℓ) K.M z 𝔆.s with hfdef
  have hDlen : (countSiteD K 𝔆.s z X).IsLength := q9SiteNorm_isLength hX.1 _ _ _
  obtain ⟨cert⟩ := hK.cert_fun ℓ hDlen hsrc
  have hW : IsWeylInternal K.ξ (-(K.M • K.cat.prof ℓ)) (countSiteD K 𝔆.s z X)
      (q9SiteNorm (rho K.D (addFun X (-f))) z 𝔆.s S) := by
    have h := isWeylInternal_q9SiteNorm (G := rho K.D X) (G' := rho K.D (addFun X (-f)))
      (fun U hU u v => hX.weylD (-f) U hU u v) (z := z) hs hS
    rwa [hfdef, q9_neg_bump_comp_aff _ _ _ hs] at h
  have hgeo' : IsGeodSeg (countSiteD K 𝔆.s z X) (q9SitePath P z 𝔆.s) u w :=
    isGeodSeg_q9SiteNorm hs hS hgeo
  have hu' : q9SitePath P z 𝔆.s u ∉ siteB d := by
    rw [q9SitePath_mem_iff hs, q9Aff_image_siteB hs]
    exact hu
  have hw' : q9SitePath P z 𝔆.s w ∉ siteB d := by
    rw [q9SitePath_mem_iff hs, q9Aff_image_siteB hs]
    exact hw
  have hcore' : ∃ t ∈ Icc u w, ‖q9SitePath P z 𝔆.s t‖ ≤ 3 / 2 := by
    obtain ⟨t, ht, hPt⟩ := hcore
    refine ⟨t, ht, ?_⟩
    have hmem : q9SitePath P z 𝔆.s t ∈ closedBall (0 : Rd d) (3 / 2) := by
      rw [q9SitePath_mem_iff hs, q9Aff_image_closedBall hs]
      convert hPt using 2
      ring
    simpa only [mem_closedBall, dist_zero_right] using hmem
  have hsave := network_saving cert hW hK.ξ_pos.le hK.contract.net _ u w hgeo' hu' hw' hcore'
  have ha₀ := hK.a0_pos
  change ENNReal.ofReal ((q9SiteNorm (rho K.D (addFun X (-f))) z 𝔆.s S).1
      (q9SitePath P z 𝔆.s u, q9SitePath P z 𝔆.s w)) + ENNReal.ofReal (q9SiteA0 mc Hlo) ≤
    ENNReal.ofReal ((q9SiteNorm (rho K.D X) z 𝔆.s S).1
      (q9SitePath P z 𝔆.s u, q9SitePath P z 𝔆.s w)) at hsave
  rw [q9SiteNorm_apply_sitePath hs hS, q9SiteNorm_apply_sitePath hs hS] at hsave
  have hn1 : 0 ≤ S⁻¹ * (rho K.D (addFun X (-f))).1 (P u, P w) :=
    mul_nonneg (inv_nonneg.2 hS.le) ((rho K.D _).nonneg _ _)
  have hn2 : 0 ≤ S⁻¹ * (rho K.D X).1 (P u, P w) :=
    mul_nonneg (inv_nonneg.2 hS.le) ((rho K.D _).nonneg _ _)
  rw [← ENNReal.ofReal_add hn1 ha₀.le, ENNReal.ofReal_le_ofReal_iff hn2] at hsave
  have hmul := mul_le_mul_of_nonneg_left hsave hS.le
  rw [mul_add, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hS.ne', one_mul, one_mul] at hmul
  linarith

/-- The canonical geodesic of a good input. -/
theorem q9GoodInput.path {X : DistRd d} (hX : q9GoodInput K X) :
    q9Path K.D K.x K.y X 0 = K.x ∧ q9Path K.D K.x K.y X 1 = K.y ∧
      IsGeodSeg (rho K.D X) (q9Path K.D K.x K.y X) 0 1 :=
  q9Path_spec hX.2.2.1

open Classical in
/-- **(h2) Trigger removal.** -/
theorem q9_trigger_removal (hK : CountHyp K 𝔆 Hup sR Hlo b mc A0 d₀ Ap kp v θ ς δsep εnet εatt)
    {H : DistRd d} (hH : q9GoodInput K H) {Z : Finset (Rd d × K.cat.Label)} (hZ : IsSelection 𝔆 Z)
    {p : Rd d × K.cat.Label} (hp : p ∈ Z)
    (hX₁ : q9GoodInput K (addFun H (-selBump K 𝔆.s (Z.erase p))))
    (hX₂ : q9GoodInput K (addFun H (-selBump K 𝔆.s Z)))
    (hnot : ¬ PassesTrigger (countSiteD K 𝔆.s p.1 H)
      (q9SitePath (q9Path K.D K.x K.y (addFun H (-selBump K 𝔆.s Z))) p.1 𝔆.s) 0 1 K.btrig) :
    (rho K.D (addFun H (-selBump K 𝔆.s (Z.erase p)))).1 (K.x, K.y) ≤
      (rho K.D (addFun H (-selBump K 𝔆.s Z))).1 (K.x, K.y) + K.btrig * countUnit K 𝔆.s p.1 H := by
  have hs := hK.s_pos
  have hS : 0 < countUnit K 𝔆.s p.1 H := countUnit_pos K hs p.1 H
  replace hnot : ¬ PassesTrigger (q9SiteNorm (rho K.D H) p.1 𝔆.s (countUnit K 𝔆.s p.1 H))
      (q9SitePath (q9Path K.D K.x K.y (addFun H (-selBump K 𝔆.s Z))) p.1 𝔆.s) 0 1 K.btrig := hnot
  generalize hSdef : countUnit K 𝔆.s p.1 H = S at hS hnot ⊢
  generalize hX₁def : addFun H (-selBump K 𝔆.s (Z.erase p)) = X₁ at hX₁ ⊢
  generalize hX₂def : addFun H (-selBump K 𝔆.s Z) = X₂ at hX₂ hnot ⊢
  generalize hfpdef : q9Bump (K.cat.prof p.2) K.M p.1 𝔆.s = fp
  have hX₁₂ : addFun X₁ (-fp) = X₂ := by
    rw [← hX₁def, ← hX₂def, ← hfpdef, addFun_addFun, selBump_erase_add hp]
    congr 1
    abel
  have hW : IsWeylInternal K.ξ (-(K.M • K.cat.prof p.2)) (q9SiteNorm (rho K.D X₁) p.1 𝔆.s S)
      (q9SiteNorm (rho K.D X₂) p.1 𝔆.s S) := by
    have h := isWeylInternal_q9SiteNorm (G := rho K.D X₁) (G' := rho K.D X₂)
      (fun U hU u v => by rw [← hX₁₂]; exact hX₁.weylD (-fp) U hU u v) (z := p.1) hs hS
    rwa [← hfpdef, q9_neg_bump_comp_aff _ _ _ hs] at h
  obtain ⟨h0, h1, hgeo⟩ := hX₂.path
  have hgeo' : IsGeodSeg (q9SiteNorm (rho K.D X₂) p.1 𝔆.s S)
      (q9SitePath (q9Path K.D K.x K.y X₂) p.1 𝔆.s) 0 1 := isGeodSeg_q9SiteNorm hs hS hgeo
  -- the other bumps vanish on the full inspection of `p`
  have hzero : ∀ x ∈ ball p.1 (4 * 𝔆.s), selBump K 𝔆.s (Z.erase p) x = 0 := by
    intro x hx
    refine selBump_eq_zero_of_notMem hs hK.prof_tsupport fun q hq hxq => ?_
    have hqZ := Finset.mem_of_mem_erase hq
    have hqp : q ≠ p := Finset.ne_of_mem_erase hq
    have hne : q.1 ≠ p.1 := fun h => hqp (hZ.2 q hqZ p hp h)
    have hdisj := hK.valid.2.2.2.2 q.1 (hZ.1 q hqZ) p.1 (hZ.1 p hp) hne
    exact Set.disjoint_left.1 hdisj (q9_annCl_subset_closedBall hs hxq) (ball_subset_closedBall hx)
  have hint : ∀ u w, (rho K.D X₁).internal (ball p.1 (4 * 𝔆.s)) u w =
      (rho K.D H).internal (ball p.1 (4 * 𝔆.s)) u w := fun u w => by
    rw [← hX₁def]
    exact q6_weyl_internal_zero (hH.weylD _) isOpen_ball hzero u w
  have hnot' : ¬ PassesTrigger (q9SiteNorm (rho K.D X₁) p.1 𝔆.s S)
      (q9SitePath (q9Path K.D K.x K.y X₂) p.1 𝔆.s) 0 1 K.btrig := by
    rw [q9_passesTrigger_congr (q9SiteNorm_internal_siteB_congr hs hS hint)]
    exact hnot
  have hf0 : ∀ x, 0 ≤ (K.M • K.cat.prof p.2) x :=
    q9_smul_prof_nonneg hK.M_pos.le (hK.prof_nonneg p.2)
  have hfC : tsupport (K.M • K.cat.prof p.2) ⊆ siteC d :=
    (q9_tsupport_smul _ _).trans (hK.prof_tsupport p.2)
  have hrem := trigger_removal (D := q9SiteNorm (rho K.D X₁) p.1 𝔆.s S)
    (D' := q9SiteNorm (rho K.D X₂) p.1 𝔆.s S) (f := K.M • K.cat.prof p.2) (ξ := K.ξ) (btrig := K.btrig)
    hW hK.ξ_pos.le hf0 hfC (q9SitePath (q9Path K.D K.x K.y X₂) p.1 𝔆.s) 0 1 hgeo' hK.btrig_pos.le hnot'
  rw [q9SiteNorm_apply_sitePath hs hS, q9SiteNorm_apply_sitePath hs hS, h0, h1] at hrem
  have hn1 : 0 ≤ S⁻¹ * (rho K.D X₂).1 (K.x, K.y) :=
    mul_nonneg (inv_nonneg.2 hS.le) ((rho K.D _).nonneg _ _)
  rw [← ENNReal.ofReal_add hn1 hK.btrig_pos.le,
    ENNReal.ofReal_le_ofReal_iff (add_nonneg hn1 hK.btrig_pos.le)] at hrem
  have hmul := mul_le_mul_of_nonneg_left hrem hS.le
  rw [mul_add, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hS.ne', one_mul, one_mul] at hmul
  linarith

/-- **(h3) Restoration.** -/
theorem q9_restoration (hK : CountHyp K 𝔆 Hup sR Hlo b mc A0 d₀ Ap kp v θ ς δsep εnet εatt)
    {H : DistRd d} (hH : q9GoodInput K H) {Z : Finset (Rd d × K.cat.Label)}
    (hX : q9GoodInput K (addFun H (-selBump K 𝔆.s Z)))
    (hsrc : ∀ p ∈ Z, K.cat.Source p.2 (countSiteD K 𝔆.s p.1 H) (countSiteE K 𝔆.s p.1 H)) :
    (rho K.D H).1 (K.x, K.y) ≤
      (rho K.D (addFun H (-selBump K 𝔆.s Z))).1 (K.x, K.y) +
        A0 * ∑ p ∈ Z, countUnit K 𝔆.s p.1 H := by
  classical
  have hs := hK.s_pos
  set X := addFun H (-selBump K 𝔆.s Z) with hXdef
  obtain ⟨h0, h1, hgeo⟩ := hX.path
  let C : Rd d × K.cat.Label → Set (Rd d) := fun p => annCl p.1 (3 * 𝔆.s / 2) (5 * 𝔆.s / 2)
  let W : Rd d × K.cat.Label → Set (Rd d) := fun p => ann p.1 (𝔆.s / 2) (7 * 𝔆.s / 2)
  let cost : Rd d × K.cat.Label → ℝ := fun p => A0 * countUnit K 𝔆.s p.1 H
  have hcost : ∀ p ∈ Z, 0 ≤ cost p := fun p _ =>
    mul_nonneg hK.A0_pos.le (countUnit_pos K hs p.1 H).le
  have hrepl : ∀ p ∈ Z, ∀ u ∈ C p, ∀ w ∈ C p,
      (rho K.D H).internal (W p) u w ≤ ENNReal.ofReal (cost p) := by
    intro p hp u hu w hw
    set S := countUnit K 𝔆.s p.1 H
    have hS : 0 < S := countUnit_pos K hs p.1 H
    have hrefs := hK.contract.refs p.2 _ _ (hsrc p hp)
    have hdiam := hrefs.2.2.2.2
    have hu' : q9SitePath (fun _ => u) p.1 𝔆.s 0 ∈ siteC d := by
      rw [q9SitePath_mem_iff hs, q9Aff_image_siteC hs]
      exact hu
    have hw' : q9SitePath (fun _ => w) p.1 𝔆.s 0 ∈ siteC d := by
      rw [q9SitePath_mem_iff hs, q9Aff_image_siteC hs]
      exact hw
    have hle := (q6_internal_le_diamIn (countSiteD K 𝔆.s p.1 H) (A := siteA d) hu' hw').trans hdiam
    change (q9SiteNorm (rho K.D H) p.1 𝔆.s S).internal (siteA d) _ _ ≤ _ at hle
    rw [q9SiteNorm_internal hs hS, q9Aff_image_siteA hs] at hle
    have hu'' : q9Aff p.1 𝔆.s (q9SitePath (fun _ => u) p.1 𝔆.s 0) = u := q9Aff_sitePath hs 0
    have hw'' : q9Aff p.1 𝔆.s (q9SitePath (fun _ => w) p.1 𝔆.s 0) = w := q9Aff_sitePath hs 0
    rw [hu'', hw''] at hle
    have hW' : W p = ann p.1 (𝔆.s / 2) (7 * 𝔆.s / 2) := rfl
    rw [hW']
    calc (rho K.D H).internal (ann p.1 (𝔆.s / 2) (7 * 𝔆.s / 2)) u w
        = ENNReal.ofReal S * (ENNReal.ofReal S⁻¹ *
            (rho K.D H).internal (ann p.1 (𝔆.s / 2) (7 * 𝔆.s / 2)) u w) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hS.le, mul_inv_cancel₀ hS.ne', ENNReal.ofReal_one,
            one_mul]
      _ ≤ ENNReal.ofReal S * ENNReal.ofReal A0 := by gcongr
      _ = ENNReal.ofReal (cost p) := by
          rw [← ENNReal.ofReal_mul hS.le, mul_comm]
  have hagree : ∀ (P : ℝ → Rd d) (s t : ℝ), s ≤ t → ContinuousOn P (Icc s t) →
      (∀ τ ∈ Icc s t, ∀ p ∈ Z, P τ ∉ C p) → (rho K.D H).len P s t = (rho K.D X).len P s t := by
    intro P s t hst hP havoid
    rcases hst.lt_or_eq with hlt | heq
    · symm
      refine q6_weyl_len_off_tsupport (hH.weylD (-selBump K 𝔆.s Z)) hlt hP fun τ hτ hmem => ?_
      have := tsupport_selBump_subset hs hK.prof_tsupport Z hmem
      simp only [mem_iUnion] at this
      obtain ⟨p, hp, hpC⟩ := this
      exact havoid τ (Ioo_subset_Icc_self hτ) p hp hpC
    · subst heq
      rw [ContMetric.len_of_ge _ _ le_rfl, ContMetric.len_of_ge _ _ le_rfl]
  have hres := chronological_restoration Z C W (fun p => isClosed_annCl _ _ _) cost hcost hrepl
    hagree (q9Path K.D K.x K.y X) 0 1 zero_le_one hgeo.2.1
  rw [hgeo.2.2, h0, h1] at hres
  have hsum : ∑ p ∈ Z, cost p = A0 * ∑ p ∈ Z, countUnit K 𝔆.s p.1 H := by
    simp only [cost, Finset.mul_sum]
  rw [hsum, ← ENNReal.ofReal_add ((rho K.D X).nonneg _ _)
    (mul_nonneg hK.A0_pos.le (Finset.sum_nonneg fun p _ => (countUnit_pos K hs p.1 H).le)),
    ENNReal.ofReal_le_ofReal_iff (add_nonneg ((rho K.D X).nonneg _ _)
      (mul_nonneg hK.A0_pos.le (Finset.sum_nonneg fun p _ => (countUnit_pos K hs p.1 H).le)))] at hres
  exact hres

end Steps

end HigherDimLQGContinuity
