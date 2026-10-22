import HigherDimLQGContinuity.SiteCert.Certificate
import HigherDimLQGContinuity.SiteCert.Count
import HigherDimLQGContinuity.SiteCert.LabelBump

/-!
# The site certificate from the label networks (packet Q7b; Part B `b:thm-sitecert`)

Source: blueprint Part B Theorem `b:thm-sitecert` with `b:def-sitedata`, `b:def-order`, `b:lem-order`, `b:lem-bump`,
`b:lem-catalogue`, `b:lem-src-meas`, `b:lem-label-exists` and the frozen interface `SiteCertOfLabel` (IA1's
version 2, ruling N20), in Part B's order of constants: (F1) → mesh, tree, boxes (`Edge`, `centre = m_e`,
`L = δ_m/(64 d)`) → (`N_tr`, F6) → (`d₀`, `v_site`, the polynomial constants) → `v` → catalogue and scales.

`q7b_siteCert_of_net` proves `SiteCertOfLabel d` from two inputs about Part B's concrete label objects, which are
proved in packet Q4's modules and discharged in `SiteCert/Holds.lean`:
* `hcount` — the exact product bound of the catalogue ((4.9), Q4's `labelCatalogue_card_le` with `labelIndex_card`);
* `hnet` — for the site data, a network constant `C_net ≥ 1` such that at every tolerance whose constants satisfy
  `Q7bConstOK`, every realizable label has a network `Q7bNet` (`b:def-net`, `b:lem-net`, `b:lem-sep`, `b:lem-star`).
The catalogue consists of the **realizable** labels of Q3's site-label type at `siteConsts S C_net v` (`b:def-label`;
every label accepted by a source event is realizable, Q5's `isRealizable_of_labelSource`, so exhaustion is unaffected
and the catalogue bound only improves), the profile of a label is `labelBump U_ℓ ς` with the plateau of its network,
the source predicate is Q5's `labelSource`, the scales are those of `siteConsts`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric
open scoped ENNReal
open HigherDimLFPP (Rd)

namespace HigherDimLQGContinuity

open HigherDimLQGMetric

variable {d : ℕ}

/-- `siteEps0 mc Hlo > 0`. -/
theorem q7b_siteEps0_pos {mc Hlo : ℝ} (hmc : 0 < mc) (hHlo : 1 ≤ Hlo) : 0 < siteEps0 mc Hlo := by
  have hinv : 0 < Hlo⁻¹ := inv_pos.mpr (by linarith)
  unfold siteEps0 siteBtrig siteAout
  have : 0 < min mc Hlo⁻¹ := lt_min hmc hinv
  positivity

/-- **The site certificate from the label networks** (Part B `b:thm-sitecert`; see the module docstring for the two
inputs `hcount`, `hnet`, which are statements about Part B's concrete label objects). -/
theorem q7b_siteCert_of_net (hd : 3 ≤ d)
    (hcount : ∀ (S : SiteData d) (Kc Kl N : ℕ) (μ ν r c₁ : ℝ),
      Nat.card (SiteLabel S Kc Kl N μ ν r c₁) ≤
        (S.Ntr * (2 ^ ((2 * Kc + 1) ^ d)) ^ 3 * ((N + 1) * ((2 * Kl + 1) ^ d) ^ (N + 1)) ^ 2) ^
          Nat.card S.Edge)
    (hnet : ∀ S : SiteData d, ∃ Cnet : ℝ, 1 ≤ Cnet ∧ ∀ v : ℝ, Q7bConstOK S (siteConsts S Cnet v) v →
      ∀ ℓ : q7bLabel S Cnet v, IsRealizable S ℓ S.seed.A S.seed.α S.seed.β (siteConsts S Cnet v).t₀ →
        Nonempty (Q7bNet S (siteConsts S Cnet v) ℓ)) :
    SiteCertOfLabel d := by
  intro Hup s Hlo b mc A0 hHup hs hs1 hHlo hb hmc hA0
  have hd2 : 2 ≤ d := by omega
  have hd1 : 1 ≤ d := by omega
  obtain ⟨mesh⟩ := exists_siteMeshData hd2 Hup s (siteEps0 mc Hlo) hs (q7b_siteEps0_pos hmc hHlo)
  -- the fixed geometry depends on the mesh only; it is read off a site data with this mesh
  let seed₀ : SiteSeedData := q7bSeed 1 (1 / 2) 2 1 2 1 1 1 (q7bSeedMin mesh 0) le_rfl (by norm_num)
    (by norm_num) (by norm_num) one_pos (by norm_num) le_rfl one_pos le_rfl le_rfl
    (q7bSeedMin_pos hd1 mesh 0) (q7bSeedMin_le_one hd1 mesh 0)
  let S₀ : SiteData d := q7bSiteData Hup s Hlo b mc A0 hHup hs hs1 hHlo hb hmc hA0 mesh 0 seed₀
  have := q7b_finite_edge S₀
  refine ⟨S₀.Edge, Fintype.ofFinite _, fun e => S₀.edgeCenter e, S₀.boxHalfSide, S₀.boxHalfSide_pos hd2,
    fun e => S₀.center_ball_interior_C hd2 e, ?_⟩
  intro Ntr H₀ σ₀ β₀ m M Hsd σsd Λ hH₀ hσ₀ hσ₀1 hβ₀ hm hmM hHsd hσsd hσsd1 hΛ
  -- the site data with the seed constants (F6)
  let seed : SiteSeedData := q7bSeed H₀ σ₀ β₀ m M Hsd σsd Λ (q7bSeedMin mesh Ntr) hH₀ hσ₀ hσ₀1 hβ₀ hm hmM
    hHsd hσsd hσsd1 hΛ (q7bSeedMin_pos hd1 mesh Ntr) (q7bSeedMin_le_one hd1 mesh Ntr)
  let S : SiteData d := q7bSiteData Hup s Hlo b mc A0 hHup hs hs1 hHlo hb hmc hA0 mesh Ntr seed
  obtain ⟨Cnet, hCnet, hnetS⟩ := hnet S
  obtain ⟨vsite, c, Cmax, K, hvsite, hvsite1, hc, hCmax, hK, -, -, -, -, hspec⟩ :=
    siteConsts_spec S hd2 Cnet (by linarith)
  obtain ⟨Cb, hCb, hprof⟩ := labelBump_spec (d := d) hd1
  -- the polynomial constants (fixed before `v`)
  set kd : ℝ := 2 * ((d / 2 : ℕ) + 1 : ℝ) with hkd
  have hkd0 : 0 ≤ kd := by positivity
  set E : ℕ := Nat.card S.Edge with hE
  set A1 : ℝ := |Real.log c| + K with hA1
  set A2 : ℝ := Cb * c ^ (-kd) with hA2
  set A3 : ℝ := E * (Ntr + 3 * (2 * (S.boxHalfSide / c + 3) + 1) ^ d + 2 * (Cmax + 1) +
    2 * (Cmax + 1) * (2 * (5 / 2 / c + 3) + 1) ^ d) with hA3
  have hA1_0 : 0 ≤ A1 := by positivity
  have hA2_0 : 0 ≤ A2 := mul_nonneg hCb.le (Real.rpow_nonneg hc.le _)
  have hA3_0 : 0 ≤ A3 := by
    have hL := S.boxHalfSide_pos hd2
    positivity
  set Ap : ℝ := max A1 (max A2 A3) with hAp
  set kp : ℝ := max 1 (max (K * kd) (K * (d + 1))) with hkp
  refine ⟨S.seed.d₀, vsite, Ap, kp, S.seed.d₀_pos, hvsite, hvsite1, ?_⟩
  rintro v ⟨hv0, hv⟩
  obtain ⟨hA, hB, hC, hpoly⟩ := hspec v hv0 hv
  have hok := q7bConstOK_of_spec S hd2 hCnet hv0 (hv.trans hvsite1) hA hB hC
  have hfin := q7b_finite_label S Cnet v
  have hnetv := hnetS v hok
  -- the realizable labels and their networks
  let Real' : Type := {ℓ : q7bLabel S Cnet v //
    IsRealizable S ℓ S.seed.A S.seed.α S.seed.β (siteConsts S Cnet v).t₀}
  let net : ∀ ℓ : Real', Q7bNet S (siteConsts S Cnet v) ℓ.1 := fun ℓ => (hnetv ℓ.1 ℓ.2).some
  have hς := hok.ς_pos
  have hς1 : (siteConsts S Cnet v).ς ≤ 1 := hpoly.ς.2
  let cat : SiteCatalogue d :=
    { Label := Real'
      fintypeLabel := Fintype.ofFinite _
      prof := fun ℓ => labelBump (net ℓ).U (siteConsts S Cnet v).ς hς
      Source := fun ℓ D E => labelSource S (siteConsts S Cnet v).t₀ v ℓ.1 D E }
  -- (i) the catalogue size
  have hcard : Real.log (@Fintype.card cat.Label cat.fintypeLabel) ≤ polyB Ap kp 0 v⁻¹ := by
    have hJ := hcount S (labelCellCutoff S (siteConsts S Cnet v).μ) (labelLeadCutoff (siteConsts S Cnet v).ν)
      (siteConsts S Cnet v).N (siteConsts S Cnet v).μ (siteConsts S Cnet v).ν (siteConsts S Cnet v).r
      (Routing.gpC1 4)
    rw [← @Nat.card_eq_fintype_card _ cat.fintypeLabel]
    have hJ' : Nat.card cat.Label ≤ _ := (Finite.card_subtype_le _).trans hJ
    refine (q7b_log_card_le hJ').trans ?_
    have h := q7b_count_le_polyB (d := d) (E := E) (Ntr := Ntr) (L := S.boxHalfSide)
      (S.boxHalfSide_pos hd2).le hc hCmax.le hK.le hv0 hpoly.μ.1 hpoly.ν.1 hpoly.N
    refine le_trans (le_of_eq ?_) (h.trans (q7b_polyB_mono hv0 hA3_0
      ((le_max_right _ _).trans (le_max_right _ _)) ((le_max_right _ _).trans (le_max_right _ _))))
    rfl
  refine ⟨cat, (siteConsts S Cnet v).θ, (siteConsts S Cnet v).ς, (siteConsts S Cnet v).δsep,
    (siteConsts S Cnet v).enet, (siteConsts S Cnet v).eatt, ?_, hok.θ_lt, hς, hC.2.1, hC.1, hC.2.2.2.1,
    hcard, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the exponential lower bound for `θ`
    have h1 := q7b_exp_neg_polyB_le hc hK.le hv0 hpoly.θ.1
    refine le_trans (Real.exp_le_exp.2 ?_) h1
    exact neg_le_neg (q7b_polyB_mono hv0 hA1_0 (le_max_left _ _) (le_max_left _ _))
  · -- (i) the profiles
    intro ℓ
    obtain ⟨h1, h2, h3⟩ := hprof (net ℓ).U _ hς hς1 (net ℓ).thick_subset
    refine ⟨h1, h2, ?_⟩
    refine (labelBump_cm_polyB hς hCb.le hc hK.le hv0 hpoly.ς.1 h3).mono
      (q7b_polyB_mono hv0 hA2_0 ((le_max_left _ _).trans (le_max_right _ _))
        ((le_max_left _ _).trans (le_max_right _ _)))
  · -- (ii) Borel validity on pairs of length metrics
    intro ℓ
    exact labelSource_borel S hd2 _ v ℓ.1
  · -- (ii) locality in `B`
    intro ℓ D E D₂ E₂ hD hE
    exact labelSource_local S hd2 _ v ℓ.1 hD hE
  · -- (ii) validity contains the primary references
    intro ℓ D E h
    exact siteRefs_of_labelSource S h
  · -- (iii) exhaustion
    intro D E hD hE hR hfav
    obtain ⟨ℓ, hℓ⟩ := exists_label_of_seedFav S hd rfl rfl rfl rfl rfl rfl rfl rfl Cnet hv0 (by linarith) hD hE hR
      (by
        intro e
        obtain ⟨j, hj⟩ := hfav e
        refine ⟨j, ?_⟩
        have hr : S.seedRadius j = S.boxHalfSide / 4 * (8 : ℝ)⁻¹ ^ ((j : ℕ) + 1) := q5_seedRadius_eq S j
        rw [hr]
        exact hj)
    exact ⟨⟨ℓ, isRealizable_of_labelSource S hℓ⟩, hℓ⟩
  · -- (iv) the forcing certificate of every valid label
    intro ξ hξ ℓ D E hD hsrc
    exact q7b_forcingCert hd2 hok (net ℓ) _ (fun x => labelBump_apply _ _ _ x) hξ hD hsrc

end HigherDimLQGContinuity
