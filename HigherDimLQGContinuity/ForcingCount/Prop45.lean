import HigherDimLQGContinuity.ForcingCount.Upper
import HigherDimLQGContinuity.ForcingCount.Meas
import HigherDimLQGContinuity.ForcingCount.Poly
import HigherDimLQGContinuity.Overlap.Counts
import HigherDimLQGContinuity.Param.Interval

/-!
# Proposition 4.5: the forcing count for a fixed endpoint pair

Packet Q9, Part B `b:prop45` ([C] Prop. 4.5, p. 17–18, l. 900–932; NA2 items 20–24, R13; ruling N9).

`prop45_of_contract`: fix the reference constants (F1) of the site certificate, `d₀`, the polynomial `polyB A_p k_p`
of its part (i), `C_b > 1`, `μ ≥ 0`, `U₀ ≥ 1`, `R_src ≥ 16`, `C_cat, D₀ > 0`, `c_g ≥ 0`, `0 ≤ c_η ≤ 1`. There is a
polynomial `P₄₅ = polyB A₄₅ k₄₅` such that for every `ξ̄` subcritical, `a ∈ (0, ξ̄]`, `v ∈ (0, 1/100]`, every label
catalogue with the contract (i), (ii), (iv) of the site certificate (`SiteContract`), `ξ, η ∈ [a, ξ̄]` with
`|η - ξ| M_ξ ≤ v/100`, strong `D, E`, `c ∈ [1 + 20v, C_b]`, `Δ ∈ (0, 1)` with `log Δ⁻¹ ≥ P₄₅(a⁻¹, v⁻¹)`,
`g_Δ, η_loc ≥ 0`, distinct `x, y ∈ B̄₂` and every valid catalogue `𝔆 = (s, 𝒵, Q)` with `#𝒵 ≤ C_cat Δ^{-D₀}`,
`g_Δ U₀ ≤ c_g v c_seed Q`, `η_loc ≤ c_η v c_seed Q` (`c_seed = θ d₀/2`): `P₁₀(B_𝔆) ≤ Δ^{2μ+2}`.

`prop45`: the same from the interface `SiteCertOfLabel d` (with its existential data re-exported).

Proof: the frozen `Prop45OfCounts` (Q8b's `prop45_of_counts_holds`) with the index set of selections
`m₀ ≤ #Z ≤ k`, the Borel events `countEventABor` (`Meas`), the shifts `f_Z` (`Bumps`), the lower multiplicity
(`Lower`) and the upper count (`Upper`) on the full-measure good event (`Good`), and the depth polynomial (`Poly`).
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

/-- The data of Proposition 4.5 (`M = ξ⁻¹ log θ⁻¹`, `btrig = aout/32`). -/
def prop45Data (cat : SiteCatalogue d) (D E : DistRd d → ContMetric d) (ξ η θ mc Hlo : ℝ) (x y : Rd d)
    (c gΔ ηloc U₀ Rsrc Δ : ℝ) : CountData d :=
  ⟨cat, D, E, ξ, η, ξ⁻¹ * Real.log θ⁻¹, siteBtrig mc Hlo, x, y, c, gΔ, ηloc, U₀, Rsrc, Δ⟩

open Classical in
theorem card_countSelIdx_le (K : CountData d) (𝔆 : Catalogue d) (m k : ℕ) :
    ((countSelIdx K 𝔆 m k).card : ℝ) ≤
      (k + 1) * ((𝔆.Z.card : ℝ) * (@Fintype.card K.cat.Label K.cat.fintypeLabel) + 1) ^ k := by
  have h := s7b_card_small_subsets_le (countUnivSites K 𝔆) (countSelIdx K 𝔆 m k) k
    (fun Z hZ => ⟨(mem_countSelIdx.1 hZ).1, (mem_countSelIdx.1 hZ).2.2.2⟩)
  simp only [countUnivSites] at h
  rw [Finset.card_product, @Finset.card_univ _ K.cat.fintypeLabel] at h
  have hc : (((countSelIdx K 𝔆 m k).card : ℕ) : ℝ) ≤
      (((k + 1) * (𝔆.Z.card * @Fintype.card K.cat.Label K.cat.fintypeLabel + 1) ^ k : ℕ) : ℝ) :=
    Nat.cast_le.2 h
  push_cast at hc
  exact hc

theorem q9_rpow_neg_eq_exp_log_inv {Δ D₀ : ℝ} (hΔ : 0 < Δ) :
    Δ ^ (-D₀) = Real.exp (D₀ * Real.log Δ⁻¹) := by
  rw [Real.rpow_def_of_pos hΔ, Real.log_inv]
  congr 1
  ring

open Classical in
/-- **Proposition 4.5** (Part B `b:prop45`) for a label catalogue with the site-certificate contract. -/
theorem prop45_of_contract (hd : 3 ≤ d) {Hup sR Hlo b mc A0 d₀ Ap kp : ℝ}
    (hHlo : 1 ≤ Hlo) (hmc : 0 < mc) (hA0 : Hlo⁻¹ ≤ A0) (hd₀ : 0 < d₀)
    {Cb μ U₀ Rsrc Ccat D₀ cg cη : ℝ} (hCb : 1 < Cb) (hμ : 0 ≤ μ) (hU₀ : 1 ≤ U₀) (hR : 16 ≤ Rsrc)
    (hCcat : 0 < Ccat) (hD₀ : 0 < D₀) (hcg : 0 ≤ cg) (hcη0 : 0 ≤ cη) (hcη1 : cη ≤ 1) :
    ∃ A₄₅ k₄₅ : ℝ, ∀ ξbar a v : ℝ, 0 < ξbar → Real.sqrt (2 * d) < distExp d ξbar → 0 < a → a ≤ ξbar →
      0 < v → v ≤ 1 / 100 →
      ∀ (cat : SiteCatalogue d) (θ ς δsep εnet εatt : ℝ),
        SiteContract cat Hup sR Hlo b mc A0 d₀ Ap kp v θ ς δsep εnet εatt →
      ∀ (ξ η : ℝ) (D E : DistRd d → ContMetric d), ξ ∈ Icc a ξbar → η ∈ Icc a ξbar →
        |η - ξ| * (ξ⁻¹ * Real.log θ⁻¹) ≤ v / 100 →
        IsStrongExpMetric d ξ (distExp d ξ) D → IsStrongExpMetric d η (distExp d η) E →
      ∀ c Δ gΔ ηloc : ℝ, c ∈ Icc (1 + 20 * v) Cb → Δ ∈ Ioo 0 1 →
        polyB A₄₅ k₄₅ a⁻¹ v⁻¹ ≤ Real.log Δ⁻¹ → 0 ≤ gΔ → 0 ≤ ηloc →
      ∀ x y : Rd d, x ≠ y → x ∈ closedBall (0 : Rd d) 2 → y ∈ closedBall (0 : Rd d) 2 →
      ∀ 𝔆 : Catalogue d, 𝔆.Valid x y → (𝔆.Z.card : ℝ) ≤ Ccat * Δ ^ (-D₀) →
        gΔ * U₀ ≤ cg * v * (θ * d₀ / 2) * 𝔆.Q → ηloc ≤ cη * v * (θ * d₀ / 2) * 𝔆.Q →
        pinLaw d 10 (countEventB (prop45Data cat D E ξ η θ mc Hlo x y c gΔ ηloc U₀ Rsrc Δ) 𝔆) ≤
          ENNReal.ofReal (Δ ^ (2 * μ + 2)) := by
  have hd2 : 2 ≤ d := by omega
  have hF2 := q9_siteF2 hmc hHlo
  set κ := q9SiteA0 mc Hlo / (4 * A0) with hκdef
  have hA0pos : 0 < A0 := (inv_pos.2 (by linarith)).trans_le hA0
  have hκ : 0 < κ := div_pos hF2.2.2.2.2.2.2.1 (by positivity)
  set k := ⌈(8 * μ + 8) / κ⌉₊ with hkdef
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.2 (by
    rw [hkdef]
    exact (Nat.ceil_pos.2 (div_pos (by linarith) hκ)).ne')
  set m₀ := ⌈κ * k⌉₊ with hm₀def
  set C₁ := cg + 4 + 4 * Cb * A0 / d₀ with hC₁def
  have hC₁ : 1 ≤ C₁ := by
    have : 0 ≤ 4 * Cb * A0 / d₀ := by have := hA0pos; positivity
    linarith
  obtain ⟨A₄₅, k₄₅, hpoly⟩ := q9_depth_poly (κ := κ) (D₀ := D₀) (Ccat := Ccat) (C₁ := C₁) (Ap := Ap)
    (kp := kp) hκ hD₀ hk1 hC₁
  refine ⟨A₄₅, k₄₅, ?_⟩
  intro ξbar a v hξbar hQbar ha haξ hv hv1 cat θ ς δsep εnet εatt hC ξ η D E hξ hη hmis hD hE c Δ gΔ ηloc
    hc hΔ hℓpoly hgΔ hηloc x y _hxy hx hy 𝔆 h𝔆 h𝔆card hgU hηQ
  set K := prop45Data cat D E ξ η θ mc Hlo x y c gΔ ηloc U₀ Rsrc Δ with hKdef
  have hs := h𝔆.1
  have hθ : 0 < θ := (Real.exp_pos _).trans_le hC.θ_lower
  have hK : CountHyp K 𝔆 Hup sR Hlo b mc A0 d₀ Ap kp v θ ς δsep εnet εatt :=
    ⟨hC, ha.trans_le hξ.1, ha.trans_le hη.1, rfl, rfl, hHlo, hmc, hA0, hd₀, hv, hv1, hmis, h𝔆⟩
  -- subcriticality of `ξ`
  have hQξ : Real.sqrt (2 * d) < distExp d ξ := by
    have hsub := subcritSet_eq_Ioo (d := d) hd2
    have hbar : ξbar ∈ subcritSet d := ⟨hξbar, hQbar⟩
    rw [hsub] at hbar
    have hξs : ξ ∈ subcritSet d := by
      rw [hsub]
      exact ⟨ha.trans_le hξ.1, hξ.2.trans_lt hbar.2⟩
    exact hξs.2
  have hKQ : Real.sqrt (2 * d) < distExp d K.ξ := hQξ
  have hKD : IsStrongExpMetric d K.ξ (distExp d K.ξ) K.D := hD
  have hKE : IsStrongExpMetric d K.η (distExp d K.η) K.E := hE
  have hKξ : K.ξ = ξ := rfl
  have hKΔ : K.Δ = Δ := rfl
  have hKc : K.c ∈ Icc (1 + 20 * v) Cb := hc
  have hKgΔ : 0 ≤ K.gΔ := hgΔ
  have hKηloc : 0 ≤ K.ηloc := hηloc
  have hKgU : K.gΔ * K.U₀ ≤ cg * v * (θ * d₀ / 2) * 𝔆.Q := hgU
  have hKηQ : K.ηloc ≤ cη * v * (θ * d₀ / 2) * 𝔆.Q := hηQ
  have hKU₀ : K.U₀ = U₀ := rfl
  have hKR : K.Rsrc = Rsrc := rfl
  have hKx : ‖K.x‖ ≤ 2 := by
    show ‖x‖ ≤ 2
    simpa [mem_closedBall, dist_zero_right] using hx
  clear_value K
  clear hC hD hE hc hgΔ hηloc hgU hηQ hx hy hmis
  have hgood := ae_countGood hd K 𝔆 hs hK.ξ_pos hKQ hKD hKE hK.M_pos.le
    (fun ℓ x => (hK.contract.prof ℓ).1 x)
  -- the depth
  set ℓ := Real.log Δ⁻¹ with hℓdef
  have hΔ0 := hΔ.1
  set J : ℝ := (@Fintype.card K.cat.Label K.cat.fintypeLabel : ℝ) with hJdef
  have hJ0 : 0 ≤ J := Nat.cast_nonneg _
  set cseed := θ * d₀ / 2 with hcseed
  have hcs : 0 < cseed := by positivity
  set K₁ := cg + 4 + 2 * Cb * A0 / (v * cseed) with hK₁def
  have hCbpos : 0 < Cb := by linarith
  have hK₁1 : 1 ≤ K₁ := by
    have : 0 ≤ 2 * Cb * A0 / (v * cseed) := by positivity
    linarith
  have hK₁le : K₁ ≤ C₁ * v⁻¹ * θ⁻¹ := by
    have hvθ : 1 ≤ v⁻¹ * θ⁻¹ := by
      have h1 : 1 ≤ v⁻¹ := one_le_inv_iff₀.2 ⟨hv, by linarith⟩
      have h2 : 1 ≤ θ⁻¹ := one_le_inv_iff₀.2 ⟨hθ, hK.contract.θ_lt_one.le⟩
      exact one_le_mul_of_one_le_of_one_le h1 h2
    have heq : 2 * Cb * A0 / (v * cseed) = 4 * Cb * A0 / d₀ * (v⁻¹ * θ⁻¹) := by
      rw [hcseed]
      field_simp
      ring
    rw [hK₁def, heq, hC₁def]
    have h0 : 0 ≤ cg + 4 := by linarith
    have h4 : cg + 4 ≤ (cg + 4) * (v⁻¹ * θ⁻¹) := le_mul_of_one_le_right h0 hvθ
    have h5 : (cg + 4 + 4 * Cb * A0 / d₀) * v⁻¹ * θ⁻¹ =
        (cg + 4) * (v⁻¹ * θ⁻¹) + 4 * Cb * A0 / d₀ * (v⁻¹ * θ⁻¹) := by ring
    rw [h5]
    linarith
  have hdepth := hpoly a v J θ K₁ ℓ ha hv (by linarith) hJ0 hK.contract.card hθ hK.contract.θ_lower
    hK.contract.θ_lt_one hK₁1 hK₁le
    hℓpoly
  set Pv := max (polyB Ap kp 0 v⁻¹) 0 with hPv
  set M₀ := max (a⁻¹ * Pv * Pv) 1 with hM₀def
  have hM₀1 : 1 ≤ M₀ := le_max_right _ _
  have hlogk2 : 2 * Real.log k ≤ ℓ := (le_max_right _ _).trans ((le_max_right _ _).trans hdepth)
  -- the Borel validity sets
  choose S hSm hSspec using hK.contract.borel
  set A := countEventABor K 𝔆 S with hAdef
  have hAm : ∀ Z, MeasurableSet (A Z) := fun Z =>
    measurableSet_countEventABor hKD.measurable hKE.measurable hs hSm Z
  -- the shifts
  let F : Finset (Rd d × K.cat.Label) → C(Rd d, ℝ) := fun Z =>
    if IsSelection 𝔆 Z then selBump K 𝔆.s Z else 0
  have hFsel : ∀ Z, IsSelection 𝔆 Z → F Z = selBump K 𝔆.s Z := fun Z hZ => ite_eq_left hZ
  have hsupp : ∀ Z, tsupport (F Z) ⊆ ball (0 : Rd d) 4 := by
    intro Z
    by_cases hZ : IsSelection 𝔆 Z
    · rw [hFsel Z hZ]
      exact tsupport_selBump_ball hK.valid hK.prof_tsupport hZ
    · simp only [F, hZ, ↓reduceIte, ContinuousMap.coe_zero, tsupport_zero, empty_subset]
  -- the Cameron–Martin level of the shifts
  have hMle : K.M ≤ a⁻¹ * Pv := by
    have h1 : Real.log θ⁻¹ ≤ Pv := by
      have h2 : -polyB Ap kp 0 v⁻¹ ≤ Real.log θ := by
        have := Real.log_le_log (Real.exp_pos _) hK.contract.θ_lower
        rwa [Real.log_exp] at this
      rw [Real.log_inv]
      exact (neg_le.1 h2).trans (le_max_left _ _)
    have h0 : 0 ≤ Real.log θ⁻¹ := Real.log_nonneg (one_le_inv_iff₀.2 ⟨hθ, hK.contract.θ_lt_one.le⟩)
    have hξinv : ξ⁻¹ ≤ a⁻¹ := inv_anti₀ ha hξ.1
    rw [hK.M_eq, hKξ]
    exact mul_le_mul hξinv h1 h0 (inv_pos.2 ha).le
  have hCM : ∀ Z ∈ countSelIdx K 𝔆 m₀ k, IsCMBounded (F Z) (k * M₀) := by
    intro Z hZ
    obtain ⟨-, hZsel, -, hZk⟩ := mem_countSelIdx.1 hZ
    rw [hFsel Z hZsel]
    have h1 := isCMBounded_selBump (fun ℓ => (hK.contract.prof ℓ).2.2) hs Z (K := K)
    refine h1.mono ?_
    have hMC : |K.M| * polyB Ap kp 0 v⁻¹ ≤ M₀ := by
      rw [abs_of_pos hK.M_pos]
      calc K.M * polyB Ap kp 0 v⁻¹ ≤ K.M * Pv :=
            mul_le_mul_of_nonneg_left (le_max_left _ _) hK.M_pos.le
        _ ≤ a⁻¹ * Pv * Pv := mul_le_mul_of_nonneg_right hMle (le_max_right _ _)
        _ ≤ M₀ := le_max_left _ _
    have hZk' : (Z.card : ℝ) ≤ k := by exact_mod_cast hZk
    calc (Z.card : ℝ) * (|K.M| * polyB Ap kp 0 v⁻¹) ≤ Z.card * M₀ :=
          mul_le_mul_of_nonneg_left hMC (Nat.cast_nonneg _)
      _ ≤ k * M₀ := mul_le_mul_of_nonneg_right hZk' (by linarith)
  -- the index count
  have hcard : ((countSelIdx K 𝔆 m₀ k).card : ℝ) ≤ (4 * max Ccat 1 * max J 1 * Real.exp (D₀ * ℓ)) ^ k := by
    have h1 := card_countSelIdx_le K 𝔆 m₀ k
    have hZ : (𝔆.Z.card : ℝ) ≤ max Ccat 1 * Real.exp (D₀ * ℓ) := by
      rw [q9_rpow_neg_eq_exp_log_inv hΔ0] at h𝔆card
      exact h𝔆card.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
    have hY : (𝔆.Z.card : ℝ) * J ≤ max Ccat 1 * max J 1 * Real.exp (D₀ * ℓ) := by
      calc (𝔆.Z.card : ℝ) * J ≤ (max Ccat 1 * Real.exp (D₀ * ℓ)) * max J 1 :=
            mul_le_mul hZ (le_max_left _ _) hJ0 (by positivity)
        _ = max Ccat 1 * max J 1 * Real.exp (D₀ * ℓ) := by ring
    have hW : 1 ≤ max Ccat 1 * max J 1 * Real.exp (D₀ * ℓ) := by
      have h2 : 1 ≤ Real.exp (D₀ * ℓ) := Real.one_le_exp (by
        have : 0 ≤ ℓ := Real.log_nonneg (one_le_inv_iff₀.2 ⟨hΔ0, hΔ.2.le⟩)
        positivity)
      have h3 : 1 ≤ max Ccat 1 * max J 1 :=
        one_le_mul_of_one_le_of_one_le (le_max_right _ _) (le_max_right _ _)
      exact one_le_mul_of_one_le_of_one_le h3 h2
    have h4 := q9_count_arith k (by positivity) hY hW
    calc ((countSelIdx K 𝔆 m₀ k).card : ℝ) ≤ (k + 1) * ((𝔆.Z.card : ℝ) * J + 1) ^ k := h1
      _ ≤ (4 * (max Ccat 1 * max J 1 * Real.exp (D₀ * ℓ))) ^ k := h4
      _ = (4 * max Ccat 1 * max J 1 * Real.exp (D₀ * ℓ)) ^ k := by ring
  -- the lower multiplicity
  have hlower : ∀ᵐ g ∂(pinLaw d 10), g ∈ countEventB K 𝔆 →
      Real.exp (m₀ * ℓ / 2) / (k : ℝ) ^ k ≤
        (((countSelIdx K 𝔆 m₀ k).filter fun Z => g ∈ A Z).card : ℝ) := by
    filter_upwards [hgood] with g hG hB
    have hH0 := hG.base
    have helig := hB.2.2.2.2
    have hexp : K.Δ ^ (-(1 / 2 : ℝ)) = Real.exp (ℓ / 2) := by
      rw [hKΔ, q9_rpow_neg_eq_exp_log_inv hΔ0]
      congr 1
      rw [hℓdef]
      ring
    rw [hexp] at helig
    set N := ((𝔆.Z.filter fun z => IsEligible K 𝔆 z g).card : ℝ) with hNdef
    have hkN : (k : ℝ) ≤ N := by
      have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
      calc (k : ℝ) = Real.exp (Real.log k) := (Real.exp_log hk0).symm
        _ ≤ Real.exp (ℓ / 2) := Real.exp_le_exp.2 (by linarith)
        _ ≤ N := helig
    have hkN' : k ≤ (𝔆.Z.filter fun z => IsEligible K 𝔆 z g).card := by
      have h := hkN
      rw [hNdef] at h
      exact_mod_cast h
    have hmult := lower_multiplicity_det hK hG hB (m := m₀) le_rfl hkN'
    have hsubA : (((countSelIdx K 𝔆 m₀ k).filter fun Z => g ∈ countEventA K 𝔆 Z).card : ℝ) ≤
        (((countSelIdx K 𝔆 m₀ k).filter fun Z => g ∈ A Z).card : ℝ) := by
      refine Nat.cast_le.2 (Finset.card_le_card fun Z hZ => ?_)
      rw [Finset.mem_filter] at hZ ⊢
      exact ⟨hZ.1, (countEventA_iff_bor hs hSspec (by rw [hKU₀]; linarith) hH0.1 hH0.2.1).1 hZ.2⟩
    refine le_trans ?_ (hmult.trans hsubA)
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
    have hm₀k : m₀ ≤ k := by
      have hκ1 : κ ≤ 1 := by
        rw [hκdef, div_le_one (by positivity)]
        linarith [hF2.2.2.2.2.2.2.2]
      refine Nat.ceil_le.2 ?_
      calc κ * (k : ℝ) ≤ 1 * k := mul_le_mul_of_nonneg_right hκ1 hk0.le
        _ = k := one_mul _
    calc Real.exp (m₀ * ℓ / 2) / (k : ℝ) ^ k ≤ Real.exp (m₀ * ℓ / 2) / (k : ℝ) ^ m₀ := by
          apply div_le_div_of_nonneg_left (Real.exp_pos _).le (by positivity)
          exact pow_le_pow_right₀ (by exact_mod_cast hk1) hm₀k
      _ = (Real.exp (ℓ / 2) / k) ^ m₀ := by
          rw [div_pow, ← Real.exp_nat_mul]
          ring_nf
      _ ≤ (N / k) ^ m₀ := by
          apply pow_le_pow_left₀ (by positivity)
          exact div_le_div_of_nonneg_right helig hk0.le
  -- the upper count
  have hupper : ∀ᵐ g ∂(pinLaw d 10),
      (((countSelIdx K 𝔆 m₀ k).filter fun Z => addFun g (F Z) ∈ A Z).card : ℝ) ≤
        (4 * K₁ * max J 1) ^ k * (k + 1 : ℝ) ^ k := by
    filter_upwards [hgood] with h hG
    set 𝒜 := (countSelIdx K 𝔆 m₀ k).filter fun Z => addFun h (F Z) ∈ A Z with h𝒜def
    have hact : ∀ Z ∈ 𝒜, countActiveAt K 𝔆 h Z := by
      intro Z hZ
      obtain ⟨hZidx, hZA⟩ := Finset.mem_filter.1 hZ
      obtain ⟨hZsub, hZsel, -, -⟩ := mem_countSelIdx.1 hZidx
      rw [hFsel Z hZsel] at hZA
      have hgi := hG.pos hZsub
      exact countEventA_activeAt ((countEventA_iff_bor hs hSspec (by rw [hKU₀]; linarith) hgi.1 hgi.2.1).2 hZA)
    have hcount := active_count_le_det hK hG (Cb := Cb) hKc.1 hKc.2 hKgΔ hKηloc hcg hcη0 hcη1 hKgU hKηQ
      (by rw [hKU₀]; linarith) (by rw [hKR]; linarith) hKx 𝒜
      (Finset.filter_subset _ _) hact
    have hY : K₁ * (k + 1) * J ≤ K₁ * (k + 1) * max J 1 :=
      mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
    have hW : 1 ≤ K₁ * (k + 1) * max J 1 := by
      have h1 : 1 ≤ K₁ * ((k : ℝ) + 1) := one_le_mul_of_one_le_of_one_le hK₁1 (by linarith [Nat.cast_nonneg (α := ℝ) k])
      exact one_le_mul_of_one_le_of_one_le h1 (le_max_right _ _)
    have h4 := q9_count_arith k (by positivity) hY hW
    calc (𝒜.card : ℝ) ≤ (k + 1) * (K₁ * (k + 1) * J + 1) ^ k := hcount
      _ ≤ (4 * (K₁ * (k + 1) * max J 1)) ^ k := h4
      _ = (4 * K₁ * max J 1) ^ k * (k + 1 : ℝ) ^ k := by rw [← mul_pow]; ring
  -- Proposition 4.5 from its counts
  have hM₀pos : 0 < M₀ := by linarith
  have hCJ : 1 ≤ 4 * max Ccat 1 * max J 1 := by
    have h1 : 1 ≤ max Ccat 1 * max J 1 :=
      one_le_mul_of_one_le_of_one_le (le_max_right _ _) (le_max_right _ _)
    have h2 : 4 * max Ccat 1 * max J 1 = 4 * (max Ccat 1 * max J 1) := by ring
    rw [h2]
    linarith
  have hCKJ : 1 ≤ 4 * K₁ * max J 1 := by
    have h1 : 1 ≤ K₁ * max J 1 := one_le_mul_of_one_le_of_one_le hK₁1 (le_max_right _ _)
    have h2 : 4 * K₁ * max J 1 = 4 * (K₁ * max J 1) := by ring
    rw [h2]
    linarith
  have hkμ : (4 * μ + 4) / (κ / 2) ≤ (k : ℝ) := by
    have h1 : (4 * μ + 4) / (κ / 2) = (8 * μ + 8) / κ := by
      rw [div_div_eq_mul_div]
      ring
    rw [h1]
    exact Nat.le_ceil _
  have hκk : κ * (k : ℝ) ≤ (m₀ : ℝ) := Nat.le_ceil _
  have hres := prop45_of_counts_holds hd (countSelIdx K 𝔆 m₀ k) A hAm F (k := k) (m₀ := m₀) (κ := κ) (μ := μ)
    (D₀ := D₀) (M₀ := M₀) (CJ := 4 * max Ccat 1 * max J 1) (CKJ := 4 * K₁ * max J 1) (ℓ := ℓ) hκ hD₀
    hM₀pos hCJ hCKJ hkμ hκk hdepth hCM hsupp hcard (countEventB K 𝔆) hlower hupper
  have hexp : Real.exp (-(2 * μ + 2) * ℓ) = Δ ^ (2 * μ + 2) := by
    rw [Real.rpow_def_of_pos hΔ0, hℓdef, Real.log_inv]
    congr 1
    ring
  rw [hexp] at hres
  exact hres

/-! ## Proposition 4.5 from the interface `SiteCertOfLabel` -/

/-- The conclusion of Proposition 4.5 for one label catalogue at the tolerance `v` (with the polynomial
`polyB A₄₅ k₄₅`). -/
def Prop45Concl (cat : SiteCatalogue d) (θ mc Hlo d₀ Cb μ U₀ Rsrc Ccat D₀ cg cη A₄₅ k₄₅ v : ℝ) : Prop :=
  ∀ ξbar a : ℝ, 0 < ξbar → Real.sqrt (2 * d) < distExp d ξbar → 0 < a → a ≤ ξbar →
  ∀ (ξ η : ℝ) (D E : DistRd d → ContMetric d), ξ ∈ Icc a ξbar → η ∈ Icc a ξbar →
    |η - ξ| * (ξ⁻¹ * Real.log θ⁻¹) ≤ v / 100 →
    IsStrongExpMetric d ξ (distExp d ξ) D → IsStrongExpMetric d η (distExp d η) E →
  ∀ c Δ gΔ ηloc : ℝ, c ∈ Icc (1 + 20 * v) Cb → Δ ∈ Ioo 0 1 →
    polyB A₄₅ k₄₅ a⁻¹ v⁻¹ ≤ Real.log Δ⁻¹ → 0 ≤ gΔ → 0 ≤ ηloc →
  ∀ x y : Rd d, x ≠ y → x ∈ closedBall (0 : Rd d) 2 → y ∈ closedBall (0 : Rd d) 2 →
  ∀ 𝔆 : Catalogue d, 𝔆.Valid x y → (𝔆.Z.card : ℝ) ≤ Ccat * Δ ^ (-D₀) →
    gΔ * U₀ ≤ cg * v * (θ * d₀ / 2) * 𝔆.Q → ηloc ≤ cη * v * (θ * d₀ / 2) * 𝔆.Q →
    pinLaw d 10 (countEventB (prop45Data cat D E ξ η θ mc Hlo x y c gΔ ηloc U₀ Rsrc Δ) 𝔆) ≤
      ENNReal.ofReal (Δ ^ (2 * μ + 2))

/-- `prop45_of_contract` with the tolerance before the catalogue (the order of the site certificate). -/
theorem prop45_of_contract' (hd : 3 ≤ d) {Hup sR Hlo b mc A0 d₀ Ap kp : ℝ}
    (hHlo : 1 ≤ Hlo) (hmc : 0 < mc) (hA0 : Hlo⁻¹ ≤ A0) (hd₀ : 0 < d₀)
    {Cb μ U₀ Rsrc Ccat D₀ cg cη : ℝ} (hCb : 1 < Cb) (hμ : 0 ≤ μ) (hU₀ : 1 ≤ U₀) (hR : 16 ≤ Rsrc)
    (hCcat : 0 < Ccat) (hD₀ : 0 < D₀) (hcg : 0 ≤ cg) (hcη0 : 0 ≤ cη) (hcη1 : cη ≤ 1) :
    ∃ A₄₅ k₄₅ : ℝ, ∀ v : ℝ, 0 < v → v ≤ 1 / 100 →
      ∀ (cat : SiteCatalogue d) (θ ς δsep εnet εatt : ℝ),
        SiteContract cat Hup sR Hlo b mc A0 d₀ Ap kp v θ ς δsep εnet εatt →
        Prop45Concl cat θ mc Hlo d₀ Cb μ U₀ Rsrc Ccat D₀ cg cη A₄₅ k₄₅ v := by
  obtain ⟨A₄₅, k₄₅, h⟩ := prop45_of_contract hd (Hup := Hup) (sR := sR) (b := b) (Ap := Ap) (kp := kp)
    hHlo hmc hA0 hd₀ hCb hμ hU₀ hR hCcat hD₀ hcg hcη0 hcη1
  exact ⟨A₄₅, k₄₅, fun v hv hv1 cat θ ς δsep εnet εatt hC ξbar a hξbar hQbar ha haξ =>
    h ξbar a v hξbar hQbar ha haξ hv hv1 cat θ ς δsep εnet εatt hC⟩

/-- The site-certificate data of one tolerance give the contract of the count. -/
theorem siteContract_of {cat : SiteCatalogue d} {Hup sR Hlo b mc A0 d₀ Ap kp v θ ς δsep εnet εatt : ℝ}
    (h1 : Real.exp (-polyB Ap kp 0 v⁻¹) ≤ θ) (h2 : θ < 1) (h3 : 0 < ς) (h4 : 4 * ς ≤ δsep)
    (h5 : εnet ≤ siteEps0 mc Hlo) (h6 : 2 * εatt + εnet < Hlo⁻¹ * (δsep / 2) ^ b)
    (h7 : Real.log (@Fintype.card cat.Label cat.fintypeLabel) ≤ polyB Ap kp 0 v⁻¹)
    (h8 : ∀ ℓ, (∀ x, 0 ≤ cat.prof ℓ x ∧ cat.prof ℓ x ≤ 1) ∧ tsupport (cat.prof ℓ) ⊆ interior (siteC d) ∧
      IsCMBounded (cat.prof ℓ) (polyB Ap kp 0 v⁻¹))
    (h9 : ∀ ℓ, ∃ S : Set (ContMetric d × ContMetric d), MeasurableSet S ∧
      ∀ D E : ContMetric d, D.IsLength → E.IsLength → ((D, E) ∈ S ↔ cat.Source ℓ D E))
    (h10 : ∀ ℓ (D E D₂ E₂ : ContMetric d), (∀ x y, D.internal (siteB d) x y = D₂.internal (siteB d) x y) →
      (∀ x y, E.internal (siteB d) x y = E₂.internal (siteB d) x y) →
      (cat.Source ℓ D E ↔ cat.Source ℓ D₂ E₂))
    (h11 : ∀ ℓ (D E : ContMetric d), cat.Source ℓ D E → SiteRefs Hup sR Hlo b mc A0 D)
    (h12 : ∀ ξ : ℝ, 0 < ξ → ∀ ℓ (D E : ContMetric d), D.IsLength → cat.Source ℓ D E →
      Nonempty (ForcingCert D E ((ξ⁻¹ * Real.log θ⁻¹) • cat.prof ℓ) ξ (ξ⁻¹ * Real.log θ⁻¹) θ ς δsep
        (siteEps0 mc Hlo) εnet εatt (siteAout mc Hlo) Hlo b v d₀)) :
    SiteContract cat Hup sR Hlo b mc A0 d₀ Ap kp v θ ς δsep εnet εatt :=
  ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

/-- **Proposition 4.5** (Part B `b:prop45`) from the interface `SiteCertOfLabel d`: the site certificate's data are
re-exported with, for every tolerance `v ∈ (0, v_site]`, the forcing count bound `P₁₀(B_𝔆) ≤ Δ^{2μ+2}` for its label
catalogue, the polynomial `polyB A₄₅ k₄₅` being fixed before `v`. -/
theorem prop45 (hd : 3 ≤ d) (hcert : SiteCertOfLabel d) :
    ∀ Hup sR Hlo b mc A0 : ℝ, 1 ≤ Hup → 0 < sR → sR ≤ 1 → 1 ≤ Hlo → 1 ≤ b → 0 < mc → Hlo⁻¹ ≤ A0 →
    ∃ (Edge : Type) (_ : Fintype Edge) (centre : Edge → Rd d) (L : ℝ), 0 < L ∧
      (∀ e, closedBall (centre e) L ⊆ interior (siteC d)) ∧
    ∀ (Ntr : ℕ) (H₀ σ₀ β₀ m M Hsd σsd Λ : ℝ), 1 ≤ H₀ → 0 < σ₀ → σ₀ < 1 → 1 < β₀ → 0 < m → m < M →
      1 ≤ Hsd → 0 < σsd → σsd ≤ 1 → 1 ≤ Λ →
    ∃ d₀ vsite Ap kp : ℝ, 0 < d₀ ∧ 0 < vsite ∧ vsite ≤ 1 / 100 ∧
    ∀ Cb μ U₀ Rsrc Ccat D₀ cg cη : ℝ, 1 < Cb → 0 ≤ μ → 1 ≤ U₀ → 16 ≤ Rsrc → 0 < Ccat → 0 < D₀ →
      0 ≤ cg → 0 ≤ cη → cη ≤ 1 →
    ∃ A₄₅ k₄₅ : ℝ, ∀ v ∈ Ioc (0 : ℝ) vsite, ∃ (cat : SiteCatalogue d) (θ ς δsep εnet εatt : ℝ),
      (Real.exp (-polyB Ap kp 0 v⁻¹) ≤ θ ∧ θ < 1 ∧ 0 < ς ∧ 4 * ς ≤ δsep ∧ εnet ≤ siteEps0 mc Hlo ∧
      2 * εatt + εnet < Hlo⁻¹ * (δsep / 2) ^ b ∧
      Real.log (@Fintype.card cat.Label cat.fintypeLabel) ≤ polyB Ap kp 0 v⁻¹ ∧
      (∀ ℓ, (∀ x, 0 ≤ cat.prof ℓ x ∧ cat.prof ℓ x ≤ 1) ∧ tsupport (cat.prof ℓ) ⊆ interior (siteC d) ∧
        IsCMBounded (cat.prof ℓ) (polyB Ap kp 0 v⁻¹)) ∧
      (∀ ℓ, ∃ S : Set (ContMetric d × ContMetric d), MeasurableSet S ∧
        ∀ D E : ContMetric d, D.IsLength → E.IsLength → ((D, E) ∈ S ↔ cat.Source ℓ D E)) ∧
      (∀ ℓ (D E D₂ E₂ : ContMetric d), (∀ x y, D.internal (siteB d) x y = D₂.internal (siteB d) x y) →
        (∀ x y, E.internal (siteB d) x y = E₂.internal (siteB d) x y) →
        (cat.Source ℓ D E ↔ cat.Source ℓ D₂ E₂)) ∧
      (∀ ℓ (D E : ContMetric d), cat.Source ℓ D E → SiteRefs Hup sR Hlo b mc A0 D) ∧
      (∀ D E : ContMetric d, D.IsLength → E.IsLength → SiteRefs Hup sR Hlo b mc A0 D →
        (∀ e : Edge, ∃ j : Fin Ntr, SeedFav H₀ σ₀ β₀ m M Hsd σsd Λ v D E (centre e)
          (L / 4 * (8 : ℝ)⁻¹ ^ ((j : ℕ) + 1))) →
        ∃ ℓ, cat.Source ℓ D E) ∧
      (∀ ξ : ℝ, 0 < ξ → ∀ ℓ (D E : ContMetric d), D.IsLength → cat.Source ℓ D E →
        Nonempty (ForcingCert D E ((ξ⁻¹ * Real.log θ⁻¹) • cat.prof ℓ) ξ (ξ⁻¹ * Real.log θ⁻¹) θ ς δsep
          (siteEps0 mc Hlo) εnet εatt (siteAout mc Hlo) Hlo b v d₀))) ∧
      Prop45Concl cat θ mc Hlo d₀ Cb μ U₀ Rsrc Ccat D₀ cg cη A₄₅ k₄₅ v := by
  intro Hup sR Hlo b mc A0 hHup hsR hsR1 hHlo hb hmc hA0
  obtain ⟨Edge, hEdge, centre, L, hL, hball, hrest⟩ := hcert Hup sR Hlo b mc A0 hHup hsR hsR1 hHlo hb hmc hA0
  refine ⟨Edge, hEdge, centre, L, hL, hball, ?_⟩
  intro Ntr H₀ σ₀ β₀ m M Hsd σsd Λ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  obtain ⟨d₀, vsite, Ap, kp, hd₀, hvs, hvs1, hv⟩ := hrest Ntr H₀ σ₀ β₀ m M Hsd σsd Λ h1 h2 h3 h4 h5 h6 h7 h8
    h9 h10
  refine ⟨d₀, vsite, Ap, kp, hd₀, hvs, hvs1, ?_⟩
  intro Cb μ U₀ Rsrc Ccat D₀ cg cη hCb hμ hU₀ hR hCcat hD₀ hcg hcη0 hcη1
  obtain ⟨A₄₅, k₄₅, hP⟩ := prop45_of_contract' hd (Hup := Hup) (sR := sR) (b := b) (Ap := Ap) (kp := kp)
    hHlo hmc hA0 hd₀ hCb hμ hU₀ hR hCcat hD₀ hcg hcη0 hcη1
  refine ⟨A₄₅, k₄₅, fun v hvmem => ?_⟩
  obtain ⟨cat, θ, ς, δsep, εnet, εatt, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13⟩ :=
    hv v hvmem
  exact ⟨cat, θ, ς, δsep, εnet, εatt,
    ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13⟩,
    hP v hvmem.1 (hvmem.2.trans hvs1) cat θ ς δsep εnet εatt
      (siteContract_of hc1 hc2 hc3 hc4 hc5 hc6 hc7 hc8 hc9 hc10 hc11 hc13)⟩

end HigherDimLQGContinuity
