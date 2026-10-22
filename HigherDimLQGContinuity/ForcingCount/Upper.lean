import HigherDimLQGContinuity.ForcingCount.UpperConf
import HigherDimLQGContinuity.Restore.Arithmetic
import HigherDimLQGMetric.Sec8b.SmallSubsets

/-!
# The upper count (4.19)–(4.20): one output geodesic, one source comparison

Packet Q9, Part B `b:lem-upcount` ([C] p. 19–20, l. 973–1022; NA2 items 22–23, R13). On the good event, the
selections `Z` with `m ≤ #Z ≤ k` that are active at `h` (`h + f_Z ∈ A_Z`) number at most
`(k + 1) (K₁ (k + 1) J + 1)^k`, `K₁ = c_g + 4 + 2 C_b A₀/(v c_seed)`, `c_seed = θ d₀/2`, `J = #Λ`:

1. every active site carries a forcing block and a collector interval along the one geodesic `P_h` (`UpperBlocks`);
2. intervals of different sites are disjoint (disjoint inspections);
3. `P_h ⊆ B̄_{Rsrc}` (`q9_path_confined`);
4. the chain bound along `P_h` for the secondary metric of one fixed active source `H₀` gives (4.19), hence
   `12 v c_seed m Q ≤ g_Δ U₀ + 2 C_b A₀ k Q + (m + 2k + 1) η_loc` for the number `m` of extra sites, and Q8a's
   `active_sites_bound`;
5. the library's `s7b_card_small_subsets_le`.
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

/-- Distances along a geodesic segment are additive. -/
theorem q9_geod_dist_add {D : ContMetric d} {P : ℝ → Rd d} {a c : ℝ} (hgeo : IsGeodSeg D P a c)
    {u v w : ℝ} (hu : a ≤ u) (huv : u ≤ v) (hvw : v ≤ w) (hw : w ≤ c) :
    D.1 (P u, P v) + D.1 (P v, P w) = D.1 (P u, P w) := by
  have h := D.len_add P huv hvw
  rw [q6_geod_subsegment hgeo hu huv (hvw.trans hw), q6_geod_subsegment hgeo (hu.trans huv) hvw hw,
    q6_geod_subsegment hgeo hu (huv.trans hvw) hw, ← ENNReal.ofReal_add (D.nonneg _ _) (D.nonneg _ _)] at h
  exact (ENNReal.ofReal_eq_ofReal_iff (add_nonneg (D.nonneg _ _) (D.nonneg _ _)) (D.nonneg _ _)).1 h

section Upper

variable {K : CountData d} {𝔆 : Catalogue d} {Hup sR Hlo b mc A0 d₀ Ap kp v θ ς δsep εnet εatt : ℝ}

open Classical in
/-- **The upper count (4.20)** (deterministic form, on the good event). -/
theorem active_count_le_det (hK : CountHyp K 𝔆 Hup sR Hlo b mc A0 d₀ Ap kp v θ ς δsep εnet εatt)
    {h : DistRd d} (hG : CountGood K 𝔆 h) {Cb cg cη : ℝ}
    (hc : 1 + 20 * v ≤ K.c) (hcb : K.c ≤ Cb) (hgΔ : 0 ≤ K.gΔ) (hη0 : 0 ≤ K.ηloc) (hcg : 0 ≤ cg)
    (hcη0 : 0 ≤ cη) (hcη1 : cη ≤ 1)
    (hgU : K.gΔ * K.U₀ ≤ cg * v * (θ * d₀ / 2) * 𝔆.Q) (hηQ : K.ηloc ≤ cη * v * (θ * d₀ / 2) * 𝔆.Q)
    (hU0 : 0 < K.U₀) (hR : 8 < K.Rsrc) (hx2 : ‖K.x‖ ≤ 2) {m k : ℕ}
    (A : Finset (Finset (Rd d × K.cat.Label))) (hA : A ⊆ countSelIdx K 𝔆 m k)
    (hact : ∀ Z ∈ A, countActiveAt K 𝔆 h Z) :
    (A.card : ℝ) ≤ (k + 1) * ((cg + 4 + 2 * Cb * A0 / (v * (θ * d₀ / 2))) * (k + 1) *
      (@Fintype.card K.cat.Label K.cat.fintypeLabel) + 1) ^ k := by
  have hK₁0 : 0 ≤ cg + 4 + 2 * Cb * A0 / (v * (θ * d₀ / 2)) := by
    have := hK.θ_pos; have := hK.d₀_pos; have := hK.v_pos; have := hK.A0_pos
    have hCb : 0 ≤ Cb := by linarith [hK.v_pos]
    positivity
  rcases A.eq_empty_or_nonempty with hAe | ⟨Z₀, hZ₀⟩
  · subst hAe
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  have hs := hK.s_pos
  set cseed := θ * d₀ / 2 with hcseed
  have hcs : 0 < cseed := by have := hK.θ_pos; have := hK.d₀_pos; positivity
  have hv := hK.v_pos
  have hQ := hK.valid.2.2.1
  have hc0 : 0 ≤ K.c := by linarith
  have hCb : 0 ≤ Cb := by linarith
  have hA0 := hK.A0_pos
  obtain ⟨hZ₀sub, hZ₀sel, -, hZ₀k⟩ := mem_countSelIdx.1 (hA hZ₀)
  obtain ⟨hCmp, hgap, hUb, hbar, hsites₀⟩ := hact Z₀ hZ₀
  obtain ⟨hle0, hconf⟩ := q9_path_confined hK hG hZ₀sub hZ₀sel hUb hbar hU0.le hR hx2
  obtain ⟨h0, h1, hgeo⟩ := hG.base.path
  have hH₀ : q9GoodInput K (addFun h (selBump K 𝔆.s Z₀)) := hG.pos hZ₀sub
  set fZ := selBump K 𝔆.s Z₀ with hfZ
  set H₀ := addFun h fZ with hH₀def
  have hback : addFun H₀ (-fZ) = h := addFun_neg h fZ
  set P := q9Path K.D K.x K.y h with hPdef
  -- the active sites
  set V := A.biUnion fun Z => Z.image Prod.fst with hVdef
  have hVmem : ∀ i, i ∈ V ↔ ∃ Z ∈ A, ∃ ℓ, (i, ℓ) ∈ Z := by
    intro i
    simp only [hVdef, Finset.mem_biUnion, Finset.mem_image]
    constructor
    · rintro ⟨Z, hZ, p, hp, rfl⟩
      exact ⟨Z, hZ, p.2, hp⟩
    · rintro ⟨Z, hZ, ℓ, hℓ⟩
      exact ⟨Z, hZ, (i, ℓ), hℓ, rfl⟩
  have hVZ : V ⊆ 𝔆.Z := by
    intro i hi
    obtain ⟨Z, hZ, ℓ, hℓ⟩ := (hVmem i).1 hi
    exact (mem_countSelIdx.1 (hA hZ)).2.1.1 _ hℓ
  have hwit : ∀ i ∈ V, ∃ Z ∈ A, ∃ ℓ, (i, ℓ) ∈ Z := fun i hi => (hVmem i).1 hi
  choose! Zof hZof labof hlabof using hwit
  have hblk : ∀ i ∈ V, (∃ σ τ : ℝ, 0 ≤ σ ∧ σ ≤ τ ∧ τ ≤ 1 ∧
        (∀ t ∈ Icc σ τ, P t ∈ ann i (𝔆.s / 2) (7 * 𝔆.s / 2)) ∧
        θ * d₀ / 2 * 𝔆.Q ≤ (rho K.D h).1 (P σ, P τ) ∧
        (rho K.E h).internal (ball i (4 * 𝔆.s)) (P σ) (P τ) ≤
          ENNReal.ofReal ((1 + 6 * v) * Real.exp (2 * (v / 100)) * (rho K.D h).1 (P σ, P τ))) ∧
      (∃ u₀ v₀ : ℝ, 0 ≤ u₀ ∧ u₀ ≤ v₀ ∧ v₀ ≤ 1 ∧
        P u₀ ∈ annCl i (3 * 𝔆.s / 2) (5 * 𝔆.s / 2) ∧ P v₀ ∈ annCl i (3 * 𝔆.s / 2) (5 * 𝔆.s / 2) ∧
        (∀ t ∈ Icc u₀ v₀, P t ∈ ann i (𝔆.s / 2) (7 * 𝔆.s / 2)) ∧
        ∀ t ∈ Icc (0 : ℝ) 1, P t ∈ annCl i (3 * 𝔆.s / 2) (5 * 𝔆.s / 2) → u₀ ≤ t ∧ t ≤ v₀) := by
    intro i hi
    have hZm := mem_countSelIdx.1 (hA (hZof i hi))
    obtain ⟨-, -, -, -, hsites⟩ := hact (Zof i) (hZof i hi)
    obtain ⟨hh1, hh2, hh3⟩ := hsites _ (hlabof i hi)
    have hb := q9_site_block hK hG hZm.2.1 hZm.1 (hlabof i hi) hh1 hh2 hh3
    simp only at hb
    exact hb
  have hblk1 := fun i hi => (hblk i hi).1
  have hblk2 := fun i hi => (hblk i hi).2
  choose! σ τ hσ0 hστ hτ1 hστA hLlow hLcost using hblk1
  choose! u₀ v₀ hu0 huv hv1 hPu hPv huvA hvisit using hblk2
  -- the sites of `Z₀`
  set sZ := Z₀.image Prod.fst with hsZdef
  have hsZV : sZ ⊆ V := by
    intro i hi
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hi
    exact (hVmem _).2 ⟨Z₀, hZ₀, p.2, hp⟩
  have hsZcard : sZ.card ≤ k := Finset.card_image_le.trans hZ₀k
  set V₀ := V \ sZ with hV₀def
  -- the special intervals
  let s : Rd d → ℝ := fun i => if i ∈ sZ then u₀ i else σ i
  let t : Rd d → ℝ := fun i => if i ∈ sZ then v₀ i else τ i
  let L : Rd d → ℝ := fun i => (rho K.D h).1 (P (σ i), P (τ i))
  set e := (1 + 6 * v) * Real.exp (2 * (v / 100)) with he
  let costR : Rd d → ℝ := fun i => if i ∈ sZ then K.c * (A0 * (2 * 𝔆.Q)) + K.ηloc else e * L i
  have hstA : ∀ i ∈ V, 0 ≤ s i ∧ s i ≤ t i ∧ t i ≤ 1 ∧
      ∀ τ' ∈ Icc (s i) (t i), P τ' ∈ ann i (𝔆.s / 2) (7 * 𝔆.s / 2) := by
    intro i hi
    by_cases his : i ∈ sZ
    · simp only [s, t, his, ↓reduceIte]
      exact ⟨hu0 i hi, huv i hi, hv1 i hi, huvA i hi⟩
    · simp only [s, t, his, ↓reduceIte]
      exact ⟨hσ0 i hi, hστ i hi, hτ1 i hi, hστA i hi⟩
  have hW : IsWeylInternal K.ξ (-fZ) (rho K.D H₀) (rho K.D h) := by
    intro U hU u w
    have := hH₀.weylD (-fZ) U hU u w
    rwa [hback] at this
  have hWE : IsWeylInternal K.η (-fZ) (rho K.E H₀) (rho K.E h) := by
    intro U hU u w
    have := hH₀.weylE (-fZ) U hU u w
    rwa [hback] at this
  have hchain := q9_chain_real (rho K.E H₀) P (fun a c => K.c * (rho K.D h).1 (P a, P c)) K.ηloc s t costR
    V 0 1 zero_le_one (fun i hi => ⟨(hstA i hi).1, (hstA i hi).2.1, (hstA i hi).2.2.1⟩)
    (fun i hi j hj hij => q9_interval_disjoint (hstA i hi).2.1 (hstA j hj).2.1
      ((hK.valid.2.2.2.2 i (hVZ hi) j (hVZ hj) hij).mono (q9_ann_subset_closedBall hs)
        (q9_ann_subset_closedBall hs)) (hstA i hi).2.2.2 (hstA j hj).2.2.2)
    (fun a b c ha hab hbc hc1 => by
      rw [← mul_add, q9_geod_dist_add hgeo ha hab hbc hc1])
    (fun i hi => by
      by_cases his : i ∈ sZ
      · simp only [s, t, costR, his, ↓reduceIte]
        obtain ⟨p, hp, hpi⟩ := Finset.mem_image.1 his
        obtain ⟨hsrc₀, hunit₀, -⟩ := hsites₀ p hp
        rw [hpi] at hsrc₀ hunit₀
        have hcost := q9_collector_cost hK hsrc₀ (hPu i hi) (hPv i hi)
        have hD : (rho K.D H₀).1 (P (u₀ i), P (v₀ i)) ≤ A0 * (2 * 𝔆.Q) := by
          have h1 := ((rho K.D H₀).ofReal_le_internal _ _ _).trans hcost
          rw [ENNReal.ofReal_le_ofReal_iff (mul_nonneg hA0.le (countUnit_pos K hs _ _).le)] at h1
          refine h1.trans ?_
          exact mul_le_mul_of_nonneg_left hunit₀.2 hA0.le
        have hcmp := hCmp _ (hconf _ ⟨hu0 i hi, (huv i hi).trans (hv1 i hi)⟩) _
          (hconf _ ⟨(hu0 i hi).trans (huv i hi), hv1 i hi⟩)
        nlinarith
      · simp only [s, t, costR, his, ↓reduceIte]
        have hzero : ∀ x ∈ ball i (4 * 𝔆.s), fZ x = 0 := by
          intro x hx
          refine selBump_eq_zero_of_notMem hs hK.prof_tsupport fun q hq hxq => ?_
          have hne : q.1 ≠ i := fun hqi => his (Finset.mem_image.2 ⟨q, hq, hqi⟩)
          have hdisj := hK.valid.2.2.2.2 q.1 (hZ₀sel.1 q hq) i (hVZ hi) hne
          exact Set.disjoint_left.1 hdisj (q9_annCl_subset_closedBall hs hxq) (ball_subset_closedBall hx)
        have h1 := (rho K.E H₀).ofReal_le_internal (ball i (4 * 𝔆.s)) (P (σ i)) (P (τ i))
        rw [← q6_weyl_internal_zero hWE isOpen_ball hzero] at h1
        have h2 := h1.trans (hLcost i hi)
        exact (ENNReal.ofReal_le_ofReal_iff (by
          have := hK.v_pos; have := (rho K.D h).nonneg (P (σ i)) (P (τ i)); positivity)).1 h2)
    (fun a c ha hac hc1 havoid => by
      have hcmp := hCmp _ (hconf _ ⟨ha, hac.trans hc1⟩) _ (hconf _ ⟨ha.trans hac, hc1⟩)
      have hD : (rho K.D H₀).1 (P a, P c) ≤ (rho K.D h).1 (P a, P c) := by
        rcases hac.lt_or_eq with hlt | heq
        · have hlen : (rho K.D h).len P a c = (rho K.D H₀).len P a c := by
            refine q6_weyl_len_off_tsupport hW hlt (hgeo.2.1.mono (Icc_subset_Icc ha hc1))
              fun τ' hτ' hmem => ?_
            have hU := tsupport_selBump_subset hs hK.prof_tsupport Z₀ hmem
            simp only [mem_iUnion] at hU
            obtain ⟨q, hq, hqC⟩ := hU
            have hjsZ : q.1 ∈ sZ := Finset.mem_image_of_mem _ hq
            have hjV := hsZV hjsZ
            have hin := hvisit q.1 hjV τ' ⟨ha.trans hτ'.1.le, hτ'.2.le.trans hc1⟩ hqC
            refine havoid q.1 hjV τ' hτ' ?_
            simp only [s, t, hjsZ, ↓reduceIte]
            exact hin
          have h1 := (rho K.D H₀).ofReal_le_len P hac
          rw [← hlen, q6_geod_subsegment hgeo ha hac hc1] at h1
          exact (ENNReal.ofReal_le_ofReal_iff ((rho K.D h).nonneg _ _)).1 h1
        · subst heq
          rw [(rho K.D H₀).apply_self, (rho K.D h).apply_self]
      nlinarith)
  rw [h0, h1] at hchain
  -- split the sums over `V = V₀ ∪ sZ`
  have hsplit : ∀ f : Rd d → ℝ, ∑ i ∈ V, f i = ∑ i ∈ V₀, f i + ∑ i ∈ sZ, f i :=
    fun f => (Finset.sum_sdiff hsZV).symm
  have hcardV : V.card = V₀.card + sZ.card := (Finset.card_sdiff_add_card_eq_card hsZV).symm
  rw [hsplit, hsplit] at hchain
  have hsV₀ : ∀ i ∈ V₀, s i = σ i ∧ t i = τ i ∧ costR i = e * L i := by
    intro i hi
    have his : i ∉ sZ := (Finset.mem_sdiff.1 hi).2
    simp only [s, t, costR, his, ↓reduceIte, and_self]
  have hsZc : ∀ i ∈ sZ, costR i = K.c * (A0 * (2 * 𝔆.Q)) + K.ηloc := by
    intro i hi
    simp only [costR, hi, ↓reduceIte]
  rw [Finset.sum_congr rfl (fun i hi => by rw [(hsV₀ i hi).1, (hsV₀ i hi).2.1]),
    Finset.sum_congr rfl (fun i hi => (hsV₀ i hi).2.2), Finset.sum_congr rfl hsZc,
    Finset.sum_const, nsmul_eq_mul, hcardV] at hchain
  have hnn : 0 ≤ ∑ i ∈ sZ, K.c * (rho K.D h).1 (P (s i), P (t i)) :=
    Finset.sum_nonneg fun i _ => mul_nonneg hc0 ((rho K.D h).nonneg _ _)
  -- the lower bound on the blocks
  set m' := V₀.card with hm'
  have hLsum : (m' : ℝ) * (cseed * 𝔆.Q) ≤ ∑ i ∈ V₀, L i := by
    have h := Finset.card_nsmul_le_sum V₀ L (cseed * 𝔆.Q) (fun i hi => by
      have := hLlow i (Finset.mem_sdiff.1 hi).1
      rw [← hcseed] at this
      simp only [L]
      linarith)
    rwa [nsmul_eq_mul] at h
  have hL0 : 0 ≤ ∑ i ∈ V₀, L i := Finset.sum_nonneg fun i _ => (rho K.D h).nonneg _ _
  have he7 : e ≤ 1 + 7 * v := q9_exp_allowance hK.v_pos hK.v_le
  have hsum_mul : ∑ i ∈ V₀, K.c * L i = K.c * ∑ i ∈ V₀, L i := (Finset.mul_sum _ _ _).symm
  have hsum_mulE : ∑ i ∈ V₀, e * L i = e * ∑ i ∈ V₀, L i := (Finset.mul_sum _ _ _).symm
  simp only [L] at hsum_mul hsum_mulE hLsum hL0
  rw [hsum_mul, hsum_mulE] at hchain
  -- (ii) at `H₀`
  have hρ₀0 := (rho K.D H₀).nonneg K.x K.y
  have hgap' : K.c * (rho K.D h).1 (K.x, K.y) - K.gΔ * K.U₀ ≤ (rho K.E H₀).1 (K.x, K.y) := by
    have h1 : K.c * (rho K.D h).1 (K.x, K.y) ≤ K.c * (rho K.D H₀).1 (K.x, K.y) :=
      mul_le_mul_of_nonneg_left hle0 hc0
    have h2 : K.gΔ * (rho K.D H₀).1 (K.x, K.y) ≤ K.gΔ * K.U₀ := mul_le_mul_of_nonneg_left hUb hgΔ
    nlinarith
  -- (4.19) ⇒ the active-site inequality
  have hsZk : (sZ.card : ℝ) ≤ k := by exact_mod_cast hsZcard
  have h419 : 12 * v * cseed * m' * 𝔆.Q ≤
      K.gΔ * K.U₀ + 2 * Cb * A0 * k * 𝔆.Q + (m' + 2 * k + 1) * K.ηloc := by
    have hbr : 13 * v * ∑ i ∈ V₀, (rho K.D h).1 (P (σ i), P (τ i)) ≤
        K.c * ∑ i ∈ V₀, (rho K.D h).1 (P (σ i), P (τ i)) -
          e * ∑ i ∈ V₀, (rho K.D h).1 (P (σ i), P (τ i)) := by
      rw [← sub_mul]
      exact mul_le_mul_of_nonneg_right (by linarith) hL0
    have hjump : (sZ.card : ℝ) * (K.c * (A0 * (2 * 𝔆.Q)) + K.ηloc) ≤
        k * (Cb * (A0 * (2 * 𝔆.Q)) + K.ηloc) := by
      apply mul_le_mul hsZk _ (by positivity) (by positivity)
      have : K.c * (A0 * (2 * 𝔆.Q)) ≤ Cb * (A0 * (2 * 𝔆.Q)) :=
        mul_le_mul_of_nonneg_right hcb (by positivity)
      linarith
    have hpush : (13 : ℝ) * v * (m' * (cseed * 𝔆.Q)) ≤ 13 * v * ∑ i ∈ V₀, (rho K.D h).1 (P (σ i), P (τ i)) :=
      mul_le_mul_of_nonneg_left hLsum (by positivity)
    have hpos : 0 ≤ v * cseed * m' * 𝔆.Q := by positivity
    have hjη : (sZ.card : ℝ) * K.ηloc ≤ k * K.ηloc := mul_le_mul_of_nonneg_right hsZk hη0
    push_cast at hchain
    linarith
  have hm'bound := active_sites_bound hv hcs hQ hU0 hcg hcη0 hcη1 hCb hA0.le hgU hηQ h419
  -- the count
  have hsub : ∀ Z ∈ A, Z ⊆ V ×ˢ (@Finset.univ K.cat.Label K.cat.fintypeLabel) ∧ Z.card ≤ k := by
    intro Z hZ
    refine ⟨fun p hp => ?_, (mem_countSelIdx.1 (hA hZ)).2.2.2⟩
    rw [Finset.mem_product]
    exact ⟨(hVmem p.1).2 ⟨Z, hZ, p.2, hp⟩, @Finset.mem_univ _ K.cat.fintypeLabel _⟩
  have hcount := s7b_card_small_subsets_le (V ×ˢ (@Finset.univ K.cat.Label K.cat.fintypeLabel)) A k hsub
  rw [Finset.card_product, @Finset.card_univ _ K.cat.fintypeLabel] at hcount
  generalize hJdef : @Fintype.card K.cat.Label K.cat.fintypeLabel = J at hcount ⊢
  have hcount' : (A.card : ℝ) ≤ (k + 1) * ((V.card : ℝ) * J + 1) ^ k := by
    have hc : ((A.card : ℕ) : ℝ) ≤ (((k + 1) * (V.card * J + 1) ^ k : ℕ) : ℝ) := Nat.cast_le.2 hcount
    push_cast at hc
    exact hc
  have hVcard : (V.card : ℝ) ≤ (cg + 4 + 2 * Cb * A0 / (v * cseed)) * (k + 1) := by
    rw [hcardV]
    push_cast
    have : (m' : ℝ) ≤ (cg + 3 + 2 * Cb * A0 / (v * cseed)) * (k + 1) := hm'bound
    linarith
  have hb : (V.card : ℝ) * J + 1 ≤ (cg + 4 + 2 * Cb * A0 / (v * cseed)) * (k + 1) * J + 1 := by
    have := mul_le_mul_of_nonneg_right hVcard (Nat.cast_nonneg J)
    linarith
  have hb0 : (0 : ℝ) ≤ (V.card : ℝ) * J + 1 := by
    have h1 : (0 : ℝ) ≤ (V.card : ℝ) * J := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    linarith
  have hpow := pow_le_pow_left₀ hb0 hb k
  have hk1 : (0 : ℝ) ≤ k + 1 := by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  exact hcount'.trans (mul_le_mul_of_nonneg_left hpow hk1)

end Upper

end HigherDimLQGContinuity
