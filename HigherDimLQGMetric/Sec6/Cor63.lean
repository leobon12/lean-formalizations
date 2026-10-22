import HigherDimLQGMetric.Sec6.Defs
import HigherDimLQGMetric.Sec6.Collar
import HigherDimLQGMetric.Freq.Defs
import HigherDimLQGMetric.Freq.ScaleCount
import HigherDimLQGMetric.Events.ConfigLocal

/-!
# [S] Corollary 6.3: dense trap scales below a lower-good scale

Packet S6b. Source: MA3 Details (a) **D-H (v)** and **D-6.3** (`planning/audits/MA3-sections-5-6.md`),
blueprint Part A §6 (`cor:63`), source l. 1120–1129.

* `s6b_internal_eq_of_collar`: for a length metric, a point `x` of a closed core `I ⊆ O` whose
  internal `W`-distances to `∂O` are at least `κ` has `D(x, y; O) = D(x, y)` whenever `D(x, y) < κ`
  (the collar argument of D-H (i)–(ii)).
* `s6b_witEvent_subset_gEvent` (**D-H (v)**): the witness event `H_{0,r}(t)` of an ordered pair
  `(A, B)` with `B ≤ U A`, both length metrics, lies in the ratio event `G_r(t, β)` for every
  `0 < β ≤ min(β₀, ℓ/2, ℓ⁻¹)`.
* `s6b_shift_count`: shifting the exponents of an integer interval by `m` loses at most `m` of them
  (MA3 E12).
* `cor63_of_frequency`: **[S] Corollary 6.3** (`Cor63 … m`, every `m`) from Proposition 5.4 for the
  lower pair `(D̃, D)` with `(U, t, u) = (c_*⁻¹, c₁⁻¹, c₀⁻¹)` and condition (10).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Set
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

/-! ### The collar argument -/

/-- **Collar localization.** Let `D` be a length metric, `O` open with `closure O ⊆ W`, and `I ⊆ O`
closed such that every internal `W`-distance from `I` to `∂O` is at least `κ`. If `x ∈ I`, `y ∈ O`
and `D(x, y) < κ`, then `D(x, y; O) = D(x, y)`. -/
theorem s6b_internal_eq_of_collar (D : ContMetric d) (hD : D.IsLength) {O W I : Set (Rd d)}
    (hO : IsOpen O) (hI : IsClosed I) (hIO : I ⊆ O) (hOW : closure O ⊆ W) {κ : ℝ≥0∞}
    (hcol : ∀ x ∈ I, ∀ y ∈ frontier O, κ ≤ D.internal W x y) {x y : Rd d} (hx : x ∈ I)
    (hxy : ENNReal.ofReal (D.1 (x, y)) < κ) :
    D.internal O x y = ENNReal.ofReal (D.1 (x, y)) := by
  refine le_antisymm ?_ (D.ofReal_le_internal O x y)
  have hcolI : ∀ x ∈ closure I, ∀ y ∈ frontier O, κ ≤ D.internal W x y := by
    rw [hI.closure_eq]
    exact hcol
  have hIO' : closure I ⊆ O := by rw [hI.closure_eq]; exact hIO
  obtain ⟨e, he, hlt⟩ := ENNReal.lt_iff_exists_add_pos_lt.1 hxy
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  -- a near-optimal curve of length `< D(x, y) + min(ε, e)`
  set ε' : ℝ := min (ε : ℝ) (e : ℝ) / 2 with hε'
  have h1 : 0 < (ε : ℝ) := by exact_mod_cast hε
  have h2 : 0 < (e : ℝ) := by exact_mod_cast he
  have hε'pos : 0 < ε' := by positivity
  have hε'ε : ENNReal.ofReal ε' ≤ (ε : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_coe_nnreal]
    apply ENNReal.ofReal_le_ofReal
    have : min (ε : ℝ) (e : ℝ) ≤ ε := min_le_left _ _
    linarith
  have hε'e : ENNReal.ofReal ε' ≤ (e : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_coe_nnreal]
    apply ENNReal.ofReal_le_ofReal
    have : min (ε : ℝ) (e : ℝ) ≤ e := min_le_right _ _
    linarith
  obtain ⟨P, hPc, hP0, hP1, hPlen⟩ := (D.isLength_iff_curves.1 hD) x y ε' hε'pos
  by_cases hstay : MapsTo P (Icc 0 1) O
  · calc D.internal O x y = D.internal O (P 0) (P 1) := by rw [hP0, hP1]
      _ ≤ D.len P 0 1 := D.internal_le_len zero_le_one hPc hstay
      _ ≤ ENNReal.ofReal (D.1 (x, y)) + ENNReal.ofReal ε' := hPlen
      _ ≤ ENNReal.ofReal (D.1 (x, y)) + ε := add_le_add le_rfl hε'ε
  · exfalso
    simp only [MapsTo, not_forall] at hstay
    obtain ⟨t, ht, htO⟩ := hstay
    have hP0I : P 0 ∈ closure I := by rw [hP0]; exact subset_closure hx
    have hk := S6a.collar_le_len D hO hIO' hOW hcolI hPc hP0I ht htO
    have : κ < κ :=
      calc κ ≤ D.len P 0 1 := hk
        _ ≤ ENNReal.ofReal (D.1 (x, y)) + ENNReal.ofReal ε' := hPlen
        _ ≤ ENNReal.ofReal (D.1 (x, y)) + e := add_le_add le_rfl hε'e
        _ < κ := hlt
    exact lt_irrefl _ this

/-! ### Annulus frontier -/

theorem s6b_frontier_ann_subset (z : Rd d) (a b : ℝ) :
    frontier (ann z a b) ⊆ Metric.sphere z a ∪ Metric.sphere z b := by
  intro x hx
  have hcl : x ∈ annCl z a b := closure_minimal (ann_subset_annCl z a b) (isClosed_annCl z a b)
    (frontier_subset_closure hx)
  have hnot : x ∉ ann z a b := by
    have := hx.2
    rwa [(isOpen_ann z a b).interior_eq] at this
  simp only [ann, annCl, mem_ofPred_eq, not_and_or, not_lt] at hcl hnot
  rw [mem_union, Metric.mem_sphere, Metric.mem_sphere, dist_eq_norm]
  rcases hnot with h | h
  · exact Or.inl (le_antisymm h hcl.1)
  · exact Or.inr (le_antisymm hcl.2 h)

/-! ### D-H (v): the witness event lies in a ratio event -/

/-- **D-H (v).** For an ordered pair `(A, B)` of length metrics at `g` with `B ≤ U A`, the witness
event `H_{0,r}(t)` lies in the ratio event `G_r(t, β)` whenever `0 < β ≤ min(β₀, ℓ/2, ℓ⁻¹)`. -/
theorem s6b_witEvent_subset_gEvent {A B : DistRd d → ContMetric d} {ξ Q U a A₀ ℓ β₀ t r β : ℝ}
    {g : DistRd d} (hr : 0 < r) (hℓ : 0 < ℓ) (hAl : (A g).IsLength) (hBl : (B g).IsLength)
    (hBA : ∀ x y : Rd d, (B g).1 (x, y) ≤ U * (A g).1 (x, y))
    (hβ : 0 < β) (hββ₀ : β ≤ β₀) (hβℓ : β ≤ ℓ / 2) (hβℓ' : β ≤ ℓ⁻¹)
    (hg : g ∈ WitEvent A B ξ Q U a A₀ ℓ β₀ t r 0) :
    g ∈ GEvent A B ξ Q t β r := by
  obtain ⟨⟨-, -, hR2, hR3⟩, P, hPI, hgeo, hlo, hhi, hrat⟩ := hg
  set s := sNorm ξ Q g r 0 with hs_def
  have hs : 0 < s := sNorm_pos ξ Q g hr 0
  set O : Set (Rd d) := ann 0 (3 * r / 4) (3 * r) with hO_def
  set W : Set (Rd d) := ann 0 (r / 2) (5 * r) with hW_def
  set I : Set (Rd d) := annCl 0 r (2 * r) with hI_def
  have hx : P 0 ∈ I := hPI 0 ⟨le_rfl, zero_le_one⟩
  have hy : P 1 ∈ I := hPI 1 ⟨zero_le_one, le_rfl⟩
  have hIO : I ⊆ O := by
    intro u hu
    simp only [hI_def, hO_def, annCl, ann, mem_ofPred_eq] at hu ⊢
    constructor <;> linarith [hu.1, hu.2]
  have hOW : closure O ⊆ W := by
    refine (closure_minimal (ann_subset_annCl _ _ _) (isClosed_annCl _ _ _)).trans ?_
    intro u hu
    simp only [hW_def, annCl, ann, mem_ofPred_eq] at hu ⊢
    constructor <;> linarith [hu.1, hu.2]
  set κ : ℝ≥0∞ := ENNReal.ofReal (4 * max 1 U * ℓ * s) with hκ_def
  have hcolA : ∀ u ∈ I, ∀ v ∈ frontier O, κ ≤ (A g).internal W u v := by
    intro u hu v hv
    rcases s6b_frontier_ann_subset 0 (3 * r / 4) (3 * r) hv with hv' | hv'
    · exact (hR2 (3 * r / 4) (by simp)).1.le.trans
        (iInf₂_le_of_le u hu (iInf₂_le v hv'))
    · exact (hR2 (3 * r) (by simp)).1.le.trans
        (iInf₂_le_of_le u hu (iInf₂_le v hv'))
  have hcolB : ∀ u ∈ I, ∀ v ∈ frontier O, κ ≤ (B g).internal W u v := by
    intro u hu v hv
    rcases s6b_frontier_ann_subset 0 (3 * r / 4) (3 * r) hv with hv' | hv'
    · exact (hR2 (3 * r / 4) (by simp)).2.le.trans
        (iInf₂_le_of_le u hu (iInf₂_le v hv'))
    · exact (hR2 (3 * r) (by simp)).2.le.trans
        (iInf₂_le_of_le u hu (iInf₂_le v hv'))
  -- the witness length is the internal distance
  have hL : (A g).len P 0 1 = (A g).internal O (P 0) (P 1) := hgeo.2.2
  have hℓs : 0 < ℓ * s := mul_pos hℓ hs
  have hmax : 1 ≤ max 1 U := le_max_left _ _
  have hκbig : ℓ * s < 4 * max 1 U * ℓ * s := by nlinarith
  -- (i) global equals internal for `A`
  have hAle : ENNReal.ofReal ((A g).1 (P 0, P 1)) ≤ ENNReal.ofReal (ℓ * s) :=
    ((A g).ofReal_le_internal O _ _).trans (hL ▸ hhi)
  have hAlt : ENNReal.ofReal ((A g).1 (P 0, P 1)) < κ :=
    hAle.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 hκbig)
  have hAeq := s6b_internal_eq_of_collar (A g) hAl (isOpen_ann _ _ _) (isClosed_annCl _ _ _) hIO
    hOW hcolA hx hAlt
  have hAval : (A g).len P 0 1 = ENNReal.ofReal ((A g).1 (P 0, P 1)) := hL.trans hAeq
  have hAnn : 0 ≤ (A g).1 (P 0, P 1) := (A g).nonneg _ _
  have hAlow : ℓ / 2 * s ≤ (A g).1 (P 0, P 1) := by
    rw [hAval] at hlo
    exact (ENNReal.ofReal_le_ofReal_iff hAnn).1 hlo
  have hAhigh : (A g).1 (P 0, P 1) ≤ ℓ * s := by
    rw [hAval] at hhi
    exact (ENNReal.ofReal_le_ofReal_iff hℓs.le).1 hhi
  -- (ii) global equals internal for `B`
  have hBlt : ENNReal.ofReal ((B g).1 (P 0, P 1)) < κ := by
    rw [hκ_def, ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    have h1 := hBA (P 0) (P 1)
    have h2 : U * (A g).1 (P 0, P 1) ≤ max 1 U * (ℓ * s) :=
      (mul_le_mul_of_nonneg_right (le_max_right 1 U) hAnn).trans
        (mul_le_mul_of_nonneg_left hAhigh (by linarith))
    nlinarith
  have hBeq := s6b_internal_eq_of_collar (B g) hBl (isOpen_ann _ _ _) (isClosed_annCl _ _ _) hIO
    hOW hcolB hx hBlt
  -- (iii) Euclidean separation from (R3)
  have hsep : β₀ * r < ‖P 0 - P 1‖ := by
    by_contra hcon
    have h3 := hR3 (P 0) hx (P 1) hy (le_of_not_gt hcon)
    rw [← hL] at h3
    have h4 : ENNReal.ofReal (ℓ / 4 * s) < ENNReal.ofReal (ℓ / 2 * s) :=
      (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by nlinarith)
    exact absurd (h3.trans (h4.trans_le hlo)) (lt_irrefl _)
  -- assemble the ratio event
  have hnormx : ‖P 0‖ ≤ 2 * r := by simpa only [hI_def, annCl, sub_zero] using hx.2
  have hnormy : ‖P 1‖ ≤ 2 * r := by simpa only [hI_def, annCl, sub_zero] using hy.2
  refine ⟨P 0, by simpa only [Metric.mem_closedBall, dist_zero_right] using hnormx,
    P 1, by simpa only [Metric.mem_closedBall, dist_zero_right] using hnormy, ?_, ?_, ?_, ?_⟩
  · nlinarith
  · calc β * s ≤ ℓ / 2 * s := mul_le_mul_of_nonneg_right hβℓ hs.le
      _ ≤ (A g).1 (P 0, P 1) := hAlow
  · have hinv : ℓ ≤ β⁻¹ := by
      rw [le_inv_comm₀ hℓ hβ]
      exact hβℓ'
    calc (A g).1 (P 0, P 1) ≤ ℓ * s := hAhigh
      _ ≤ β⁻¹ * s := mul_le_mul_of_nonneg_right hinv hs.le
  · rw [hAval, hBeq, ← ENNReal.ofReal_mul' hAnn] at hrat
    exact ((ENNReal.ofReal_lt_ofReal_iff'.1 hrat).1)

/-! ### Shift counting (MA3 E12) -/

/-- Shifting the exponents of an integer interval by `m` loses at most `m` of a given set. -/
theorem s6b_shift_count (lo hi : ℤ) (G : Set ℤ) (m : ℕ) :
    ((Icc lo hi ∩ G).ncard : ℝ) ≤ (({j ∈ Icc lo hi | j - m ∈ G} : Set ℤ).ncard : ℝ) + m := by
  set W : Set ℤ := Icc lo hi with hW
  set T : Set ℤ := {j ∈ W | j - m ∈ G} with hT
  set A : Set ℤ := {j ∈ W ∩ G | j + m ∈ W} with hA
  set B : Set ℤ := {j ∈ W ∩ G | j + m ∉ W} with hB
  have hWfin : W.Finite := Set.finite_Icc lo hi
  have hTfin : T.Finite := hWfin.subset (fun j hj => hj.1)
  have hsplit : W ∩ G ⊆ A ∪ B := by
    intro j hj
    by_cases h : j + m ∈ W
    · exact Or.inl ⟨hj, h⟩
    · exact Or.inr ⟨hj, h⟩
  have hAT : A.ncard ≤ T.ncard := by
    refine Set.ncard_le_ncard_of_injOn (fun j => j + m) ?_ ?_ hTfin
    · intro j hj
      refine ⟨hj.2, ?_⟩
      simpa only [add_sub_cancel_right] using hj.1.2
    · intro j _ k _ hjk
      simpa using hjk
  have hBsub : B ⊆ Ioc (hi - m) hi := by
    intro j hj
    obtain ⟨⟨⟨hlo, hhi⟩, -⟩, hnot⟩ := hj
    refine ⟨?_, hhi⟩
    by_contra hcon
    apply hnot
    refine ⟨by omega, by omega⟩
  have hBcard : B.ncard ≤ m := by
    calc B.ncard ≤ (Ioc (hi - m) hi).ncard := Set.ncard_le_ncard hBsub (Set.finite_Ioc _ _)
      _ = m := by
        rw [Set.ncard_eq_toFinset_card' (Ioc (hi - (m : ℤ)) hi), Set.toFinset_Ioc,
          Int.card_Ioc]
        omega
  have hUcard : (W ∩ G).ncard ≤ A.ncard + B.ncard :=
    (Set.ncard_le_ncard hsplit ((hWfin.subset (fun j hj => hj.1.1)).union
      (hWfin.subset (fun j hj => hj.1.1)))).trans (Set.ncard_union_le A B)
  have hnat : (W ∩ G).ncard ≤ T.ncard + m := by omega
  exact_mod_cast hnat

/-! ### Corollary 6.3 -/

theorem s6b_scale_shift (m : ℕ) (j : ℤ) :
    (64 : ℝ)⁻¹ ^ m * (64 : ℝ) ^ j = (64 : ℝ) ^ (j - m) := by
  rw [zpow_sub₀ (by norm_num : (64 : ℝ) ≠ 0), inv_pow, zpow_natCast]
  ring

/-- **[S] Corollary 6.3** (MA3 D-6.3), for every shift `m`. Hypotheses: Proposition 5.4 for the
lower pair `(D̃, D)` with upper constant `c_*⁻¹` at `pstar`, condition (10), `c_* < c₁`, and the
comparison `c_* D ≤ D̃` almost surely for every LGF. -/
theorem cor63_of_frequency {D Dt : DistRd d → ContMetric d} {ξ Q : ℝ}
    (hD : IsSharpWeakExpMetric d ξ Q D) (hDt : IsSharpWeakExpMetric d ξ Q Dt)
    {cs c0 c1 aL A₀L ℓL β₀L pstar : ℝ} (hcs : 0 < cs) (hcs1 : cs < c1)
    (hℓL : 0 < ℓL) (hβ₀L : 0 < β₀L) (hpstar : 0 < pstar)
    (h10 : cs⁻¹ - aL / A₀L * (cs⁻¹ - c1⁻¹) < c0⁻¹)
    (hfreq : FrequencyLemma d ξ Q Dt D cs⁻¹ aL A₀L ℓL β₀L pstar)
    (hcomp : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistRd d), IsWholeSpaceLGF h P →
        ∀ᵐ ω ∂P, ∀ u v : Rd d, cs * (D (h ω)).1 (u, v) ≤ (Dt (h ω)).1 (u, v))
    (m : ℕ) : Cor63 d ξ Q D Dt cs c0 c1 aL A₀L ℓL β₀L pstar m := by
  have hc1 : 0 < c1 := hcs.trans hcs1
  set β : ℝ := min (min β₀L (ℓL / 2)) (min ℓL⁻¹ pstar) with hβ_def
  have hβ : 0 < β := by positivity
  have hββ₀ : β ≤ β₀L := (min_le_left _ _).trans (min_le_left _ _)
  have hβℓ : β ≤ ℓL / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hβℓ' : β ≤ ℓL⁻¹ := (min_le_right _ _).trans (min_le_left _ _)
  have hβp : β ≤ pstar := (min_le_right _ _).trans (min_le_right _ _)
  have ht0 : 0 < c1⁻¹ := inv_pos.2 hc1
  have htU : c1⁻¹ < cs⁻¹ := inv_strictAnti₀ hcs hcs1
  obtain ⟨ε₀, hε₀, hF⟩ := hfreq c1⁻¹ c0⁻¹ β ht0 htU h10 hβ
  set εm : ℝ := ((64 : ℝ) ^ (12 * m + 2))⁻¹ with hεm_def
  have hεm : 0 < εm := by positivity
  refine ⟨min ε₀ εm, lt_min hε₀ hεm, ?_⟩
  intro Ω _ P _ h hh R hR hW ε hε hεlt
  have hεε₀ : ε < ε₀ := hεlt.trans_le (min_le_left _ _)
  have hεεm : ε < εm := hεlt.trans_le (min_le_right _ _)
  -- the witness event lies in the ratio event almost surely
  have hGprob : ENNReal.ofReal β ≤ P (h ⁻¹' GEvent Dt D ξ Q c0⁻¹ β R) := by
    have hsub : h ⁻¹' WitEvent Dt D ξ Q cs⁻¹ aL A₀L ℓL β₀L c0⁻¹ R 0 ≤ᵐ[P]
        h ⁻¹' GEvent Dt D ξ Q c0⁻¹ β R := by
      filter_upwards [hD.length P h hh.isLGFPlusCont, hDt.length P h hh.isLGFPlusCont,
        hcomp P h hh] with ω hl hlt hc hω
      refine s6b_witEvent_subset_gEvent hR hℓL hlt hl ?_ hβ hββ₀ hβℓ hβℓ' hω
      intro x y
      have := hc x y
      rw [le_inv_mul_iff₀ hcs]
      linarith
    calc ENNReal.ofReal β ≤ ENNReal.ofReal pstar := ENNReal.ofReal_le_ofReal hβp
      _ ≤ _ := hW
      _ ≤ _ := measure_mono_ae hsub
  have hcount := hF P h hh R hR hGprob ε hε hεε₀
  -- the window is an integer interval with at least `12 m` elements
  have hε64 : ε < (1 / 64 : ℝ) := by
    refine hεεm.trans_le ?_
    rw [hεm_def, one_div]
    apply inv_anti₀ (by norm_num)
    calc (64 : ℝ) = 64 ^ 1 := (pow_one _).symm
      _ ≤ 64 ^ (12 * m + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hWcount := s4c_scaleWin_count hε hε64 hR
  have hlog : (12 * m + 2 : ℝ) < Real.logb 64 ε⁻¹ := by
    have hεinv : (64 : ℝ) ^ (12 * m + 2) < ε⁻¹ := by
      rw [hεm_def] at hεεm
      have h64 : (0 : ℝ) < (64 : ℝ) ^ (12 * m + 2) := by positivity
      exact (lt_inv_comm₀ hε h64).1 hεεm
    rw [Real.lt_logb_iff_rpow_lt (by norm_num) (inv_pos.2 hε)]
    have : (64 : ℝ) ^ ((12 * m + 2 : ℕ) : ℝ) = (64 : ℝ) ^ (12 * m + 2) := Real.rpow_natCast _ _
    push_cast at this
    rw [this]
    exact hεinv
  have hWbig : (12 * m : ℝ) ≤ ((scaleWin ε R).ncard : ℝ) := by linarith
  -- shift count
  set G : Set ℤ := {j | ENNReal.ofReal pstar ≤
    P (h ⁻¹' WitEvent Dt D ξ Q cs⁻¹ aL A₀L ℓL β₀L c1⁻¹ ((64 : ℝ) ^ j) 0)} with hG_def
  rw [s4c_scaleWin_eq_Icc hε hR] at hcount hWbig ⊢
  set lo : ℤ := ⌈Real.logb 64 (ε ^ 2 * R)⌉
  set hi : ℤ := ⌊Real.logb 64 (ε * R)⌋
  have hshift := s6b_shift_count lo hi G m
  have hset1 : ({j ∈ Icc lo hi | ENNReal.ofReal pstar ≤
      P (h ⁻¹' WitEvent Dt D ξ Q cs⁻¹ aL A₀L ℓL β₀L c1⁻¹ ((64 : ℝ) ^ j) 0)} : Set ℤ) =
      Icc lo hi ∩ G := rfl
  have hset2 : ({j ∈ Icc lo hi | ENNReal.ofReal pstar ≤
      P (h ⁻¹' WitEvent Dt D ξ Q cs⁻¹ aL A₀L ℓL β₀L c1⁻¹ ((64 : ℝ)⁻¹ ^ m * (64 : ℝ) ^ j) 0)} :
        Set ℤ) = {j ∈ Icc lo hi | j - m ∈ G} := by
    ext j
    simp only [mem_ofPred_eq, hG_def, s6b_scale_shift]
  rw [hset1] at hcount
  rw [hset2]
  linarith

/-! ### Locality of configuration events -/

/-- **ConfigLocal** (MA3 D-LOC; blueprint Prop. 6.2 (L)) for two sharp weak assignments, `d ≥ 2`. -/
theorem configLocal_of_sharp (hd : 2 ≤ d) {ξ Q : ℝ} {D Dt : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D) (hDt : IsSharpWeakExpMetric d ξ Q Dt) :
    ConfigLocal d ξ Q D Dt := by
  intro Ω _ P _ h hh r z hr S hS
  exact aeEventIn_config hD hDt hd hh z hr S hS

end HigherDimLQGMetric
