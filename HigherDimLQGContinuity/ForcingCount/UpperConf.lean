import HigherDimLQGContinuity.ForcingCount.UpperBlocks

/-!
# The upper count: active selections, collector costs, confinement by the barrier

Packet Q9, Part B `b:lem-upcount` steps (3)–(4) ingredients. `countActiveAt K 𝔆 h Z` collects the clauses of
`h + f_Z ∈ A_Z` used by the upper count (`(h + f_Z) - f_Z = h`, so every active selection tests its triggers on the
one geodesic `P_h`); `countEventA_activeAt` derives it from the event. The collector cost (R4) in physical units
(`q9_collector_cost`), the confinement of `P_h` to `B̄_{Rsrc}` from the barrier (`q9_path_confined`, step (3)) and the
exponential estimate `(1 + 6v) e^{2Ω} ≤ 1 + 7v` for `Ω = v/100` follow.
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

/-- The clauses of `h + f_Z ∈ A_Z` used by the upper count. -/
def countActiveAt (K : CountData d) (𝔆 : Catalogue d) (h : DistRd d) (Z : Finset (Rd d × K.cat.Label)) :
    Prop :=
  CompOn (rho K.E (addFun h (selBump K 𝔆.s Z))) (rho K.D (addFun h (selBump K 𝔆.s Z))) K.c K.ηloc
      K.Rsrc ∧
    (K.c - K.gΔ) * (rho K.D (addFun h (selBump K 𝔆.s Z))).1 (K.x, K.y) ≤
      (rho K.E (addFun h (selBump K 𝔆.s Z))).1 (K.x, K.y) ∧
    (rho K.D (addFun h (selBump K 𝔆.s Z))).1 (K.x, K.y) ≤ K.U₀ ∧
    ENNReal.ofReal (2 * K.U₀) <
      setDistIn (rho K.D (addFun h (selBump K 𝔆.s Z))) univ (sphere (0 : Rd d) 8)
        (sphere (0 : Rd d) K.Rsrc) ∧
    ∀ p ∈ Z, K.cat.Source p.2 (countSiteD K 𝔆.s p.1 (addFun h (selBump K 𝔆.s Z)))
        (countSiteE K 𝔆.s p.1 (addFun h (selBump K 𝔆.s Z))) ∧
      countUnit K 𝔆.s p.1 (addFun h (selBump K 𝔆.s Z)) ∈ Icc 𝔆.Q (2 * 𝔆.Q) ∧
      PassesTrigger (countSiteD K 𝔆.s p.1 (addFun h (selBump K 𝔆.s Z)))
        (q9SitePath (q9Path K.D K.x K.y h) p.1 𝔆.s) 0 1 K.btrig

theorem countEventA_activeAt {K : CountData d} {𝔆 : Catalogue d} {h : DistRd d}
    {Z : Finset (Rd d × K.cat.Label)} (hA : addFun h (selBump K 𝔆.s Z) ∈ countEventA K 𝔆 Z) :
    countActiveAt K 𝔆 h Z := by
  obtain ⟨⟨h1, h2, h3, h4, -⟩, h5⟩ := hA
  refine ⟨h1, h2, h3, h4, fun p hp => ?_⟩
  obtain ⟨h6, h7, h8⟩ := h5 p hp
  rw [addFun_neg] at h8
  exact ⟨h6, h7, h8⟩

section Conf

variable {K : CountData d} {𝔆 : Catalogue d} {Hup sR Hlo b mc A0 d₀ Ap kp v θ ς δsep εnet εatt : ℝ}

/-- **The collector cost (R4)** in physical units: a valid label bounds the inspection-internal distance of two
collector points by `A₀ S`. -/
theorem q9_collector_cost (hK : CountHyp K 𝔆 Hup sR Hlo b mc A0 d₀ Ap kp v θ ς δsep εnet εatt)
    {X : DistRd d} {z : Rd d} {ℓ : K.cat.Label}
    (hsrc : K.cat.Source ℓ (countSiteD K 𝔆.s z X) (countSiteE K 𝔆.s z X)) {u w : Rd d}
    (hu : u ∈ annCl z (3 * 𝔆.s / 2) (5 * 𝔆.s / 2)) (hw : w ∈ annCl z (3 * 𝔆.s / 2) (5 * 𝔆.s / 2)) :
    (rho K.D X).internal (ann z (𝔆.s / 2) (7 * 𝔆.s / 2)) u w ≤
      ENNReal.ofReal (A0 * countUnit K 𝔆.s z X) := by
  have hs := hK.s_pos
  set S := countUnit K 𝔆.s z X
  have hS : 0 < S := countUnit_pos K hs z X
  have hdiam := (hK.contract.refs ℓ _ _ hsrc).2.2.2.2
  have hu' : q9SitePath (fun _ => u) z 𝔆.s 0 ∈ siteC d := by
    rw [q9SitePath_mem_iff hs, q9Aff_image_siteC hs]
    exact hu
  have hw' : q9SitePath (fun _ => w) z 𝔆.s 0 ∈ siteC d := by
    rw [q9SitePath_mem_iff hs, q9Aff_image_siteC hs]
    exact hw
  have hle := (q6_internal_le_diamIn (countSiteD K 𝔆.s z X) (A := siteA d) hu' hw').trans hdiam
  change (q9SiteNorm (rho K.D X) z 𝔆.s S).internal (siteA d) _ _ ≤ _ at hle
  rw [q9SiteNorm_internal hs hS, q9Aff_image_siteA hs, q9Aff_apply_sitePath hs,
    q9Aff_apply_sitePath hs] at hle
  calc (rho K.D X).internal (ann z (𝔆.s / 2) (7 * 𝔆.s / 2)) u w
      = ENNReal.ofReal S * (ENNReal.ofReal S⁻¹ *
          (rho K.D X).internal (ann z (𝔆.s / 2) (7 * 𝔆.s / 2)) u w) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hS.le, mul_inv_cancel₀ hS.ne', ENNReal.ofReal_one, one_mul]
    _ ≤ ENNReal.ofReal S * ENNReal.ofReal A0 := by gcongr
    _ = ENNReal.ofReal (A0 * S) := by rw [← ENNReal.ofReal_mul hS.le, mul_comm]

/-- **Step (3): confinement.** For an active selection `Z₀`, `D_h ≤ D_{H₀}` at the endpoints and the canonical
geodesic `P_h` stays in `B̄_{Rsrc}` (the crossing of `{8 ≤ |w| ≤ Rsrc}` costs more than `2 U₀`). -/
theorem q9_path_confined (hK : CountHyp K 𝔆 Hup sR Hlo b mc A0 d₀ Ap kp v θ ς δsep εnet εatt)
    {h : DistRd d} (hG : CountGood K 𝔆 h) {Z : Finset (Rd d × K.cat.Label)} (hZsub : Z ⊆ countUnivSites K 𝔆)
    (hZsel : IsSelection 𝔆 Z)
    (hU : (rho K.D (addFun h (selBump K 𝔆.s Z))).1 (K.x, K.y) ≤ K.U₀)
    (hbar : ENNReal.ofReal (2 * K.U₀) <
      setDistIn (rho K.D (addFun h (selBump K 𝔆.s Z))) univ (sphere (0 : Rd d) 8)
        (sphere (0 : Rd d) K.Rsrc))
    (hU0 : 0 ≤ K.U₀) (hR : 8 < K.Rsrc) (hx2 : ‖K.x‖ ≤ 2) :
    (rho K.D h).1 (K.x, K.y) ≤ (rho K.D (addFun h (selBump K 𝔆.s Z))).1 (K.x, K.y) ∧
      ∀ τ ∈ Icc (0 : ℝ) 1, q9Path K.D K.x K.y h τ ∈ closedBall (0 : Rd d) K.Rsrc := by
  have hh0 := hG.base
  have hH₀ : q9GoodInput K (addFun h (selBump K 𝔆.s Z)) := hG.pos hZsub
  set fZ := selBump K 𝔆.s Z with hfZ
  have hback : addFun (addFun h fZ) (-fZ) = h := addFun_neg h fZ
  have hf0 : ∀ x, 0 ≤ fZ x := selBump_nonneg hK.M_pos.le hK.prof_nonneg 𝔆.s Z
  -- `D_h ≤ D_{H₀}`
  have hle : (rho K.D h).1 (K.x, K.y) ≤ (rho K.D (addFun h fZ)).1 (K.x, K.y) := by
    have h1 := q9_rho_le_of_discount hH₀ hK.ξ_pos.le (f₁ := fZ) (f₂ := 0) (fun x => by simpa using hf0 x)
      (by rw [hback]; exact hh0.1) (by rw [neg_zero, addFun_zero]; exact hH₀.1) K.x K.y
    rwa [hback, neg_zero, addFun_zero] at h1
  refine ⟨hle, ?_⟩
  obtain ⟨h0, h1, hgeo⟩ := hh0.path
  set P := q9Path K.D K.x K.y h with hPdef
  have hW : IsWeylInternal K.ξ (-fZ) (rho K.D (addFun h fZ)) (rho K.D h) := by
    intro U hU u w
    have := hH₀.weylD (-fZ) U hU u w
    rwa [hback] at this
  intro τ hτ
  by_contra hout
  have hτR : K.Rsrc ≤ ‖P τ‖ := by
    rw [mem_closedBall, dist_zero_right, not_le] at hout
    exact hout.le
  have hg : ContinuousOn (fun t => ‖P t‖) (Icc 0 τ) :=
    continuous_norm.comp_continuousOn (hgeo.2.1.mono (Icc_subset_Icc le_rfl hτ.2))
  obtain ⟨p, q, hp0, hpq, hqτ, hgp, hgq, hband⟩ := q6_upcross_times hτ.1 hg hR
    (show ‖P 0‖ ≤ 8 by rw [h0]; linarith) hτR
  -- the crossing has the same length for `D_h` and `D_{H₀}`
  have hlen_eq : (rho K.D h).len P p q = (rho K.D (addFun h fZ)).len P p q := by
    refine q6_weyl_len_off_tsupport hW hpq (hgeo.2.1.mono (Icc_subset_Icc hp0 (hqτ.trans hτ.2)))
      fun t ht hmem => ?_
    have hball := tsupport_selBump_ball hK.valid hK.prof_tsupport hZsel hmem
    rw [mem_ball, dist_zero_right] at hball
    have := (hband t (Ioo_subset_Icc_self ht)).1
    linarith
  have hcross : ENNReal.ofReal (2 * K.U₀) < (rho K.D (addFun h fZ)).len P p q := by
    refine hbar.trans_le ?_
    have hint := (rho K.D (addFun h fZ)).internal_le_len hpq.le
      (hgeo.2.1.mono (Icc_subset_Icc hp0 (hqτ.trans hτ.2))) (mapsTo_univ _ _)
    refine le_trans ?_ hint
    unfold setDistIn
    refine iInf₂_le_of_le (P p) (by simpa [mem_sphere, dist_zero_right] using hgp) ?_
    exact iInf₂_le_of_le (P q) (by simpa [mem_sphere, dist_zero_right] using hgq) le_rfl
  have hmono : (rho K.D h).len P p q ≤ (rho K.D h).len P 0 1 :=
    (rho K.D h).len_mono P hp0 (hqτ.trans hτ.2)
  rw [hgeo.2.2, h0, h1, hlen_eq] at hmono
  have hfin : ENNReal.ofReal ((rho K.D h).1 (K.x, K.y)) ≤ ENNReal.ofReal (2 * K.U₀) :=
    ENNReal.ofReal_le_ofReal (by linarith)
  exact absurd (hcross.trans_le (hmono.trans hfin)) (lt_irrefl _)

/-- The exponential allowance: `(1 + 6v) e^{2 v/100} ≤ 1 + 7v` for `0 < v ≤ 1/100`. -/
theorem q9_exp_allowance {v : ℝ} (hv : 0 < v) (hv1 : v ≤ 1 / 100) :
    (1 + 6 * v) * Real.exp (2 * (v / 100)) ≤ 1 + 7 * v := by
  have hx0 : 0 ≤ 2 * (v / 100) := by positivity
  have hx1 : 2 * (v / 100) < 1 := by linarith
  have hexp := Real.exp_bound_div_one_sub_of_interval hx0 hx1
  have hden : 0 < 1 - 2 * (v / 100) := by linarith
  calc (1 + 6 * v) * Real.exp (2 * (v / 100)) ≤ (1 + 6 * v) * (1 / (1 - 2 * (v / 100))) :=
        mul_le_mul_of_nonneg_left hexp (by linarith)
    _ ≤ 1 + 7 * v := by
        rw [mul_one_div, div_le_iff₀ hden]
        nlinarith

end Conf

end HigherDimLQGContinuity
