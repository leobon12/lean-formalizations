import HigherDimLFPPAS.Coarse.Lemma44
import HigherDimLQGMetric.Sec4.Lemma45

/-!
# Lemma 4.5′: good ratios for signed seeds (packet C27; MA3 P10)

`c27_lemma45`: there are `C ≥ 1` and `ε₁ > 0` such that for every `ε ∈ (0, ε₁)` at least half of the radii
`r = 2^{-k}`, `k ∈ N^ε`, satisfy `C⁻¹ ≤ c_ε(r) = r 𝔞_{ε/r}/(r^{ξQ} 𝔞_ε) ≤ C`.

[3]'s contradiction argument, verbatim the host's `HigherDimLQGMetric.ref1_lemma45` with the inputs replaced: on the
canonical space, if at least `|N^ε|/10` ratios were `< c`, Lemma 4.4′ (`c27_lemma44`, (4.9) with `z = 0`, `w = 2e₁`,
`U = B_4(0)`; failure probability `≤ 15^d ε ≤ 1/8` for small `ε`) would give, with probability `≥ 7/8`,
`𝔞_ε⁻¹ D̂(B(0), B(2e₁); B(B_4)) ≤ C₄ c D(0, 2e₁; B_4)`, while with probability `≥ 1 − 3/8` the left side is `≥ C₃⁻¹`
(event (3) of Lemma 4.3′ at `(0, 1)`, `c27_lemma43_compl`; `ε / 1 < δ₀` for small `ε`) and `D(0, 2e₁; B_4) ≤ C₃ M`
(event (2) at `(e₁, 1)` and `e^{ξ h_1(e₁)} ≤ M`); impossible for `c` small. Symmetrically for ratios `> c⁻¹` with
(4.10). The tightness input of [3] (MA3 S2) enters only through Lemma 4.3′, i.e. through (1.6).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace HigherDimLFPPAS.Coarse

open HigherDimLQGMetric HigherDimLFPPAS.Signed
open HigherDimLFPP (Rd e₁ lfppDistOn PcwJoined)

variable {d : ℕ}

/-- **Lemma 4.5′** (MA3 P10; [3] Lemma 4.5 for signed seeds, small `ε`). -/
theorem c27_lemma45 (hd : 3 ≤ d) {ξ Q : ℝ} {D : DistRd d → ContMetric d}
    (hD : IsSharpWeakExpMetric d ξ Q D) {κ : Rd d → ℝ} (hκ : IsAdmissibleSeed κ)
    (hconv : TendstoInProbLU (normLGFLaw d) (fun δ g => (aEps κ ξ δ)⁻¹ • lfppDist κ ξ δ g)
      (𝓝[>] 0) (fun g => (D g).1))
    {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε ∈ Ioo (0 : ℝ) ε₁,
      (nIdx ζ ε).card ≤ 2 * ((nIdx ζ ε).filter fun k =>
        C⁻¹ ≤ l9bRatio κ ξ (fun r => r ^ (ξ * Q)) ε (dyad k) ∧
          l9bRatio κ ξ (fun r => r ^ (ξ * Q)) ε (dyad k) ≤ C).card := by
  have hd2 : 2 ≤ d := by omega
  have hK := convKernel_contDiff_seed (d := d) (by omega) hκ
  have hprob := l9b_normLGFLaw_prob hd2
  have hN := l9b_normLGFLaw_normalized hd2
  set e := HigherDimLFPP.e₁ d with he
  set θ : ℝ≥0∞ := ENNReal.ofReal (1 / 8) with hθ
  have hθ0 : 0 < θ := ENNReal.ofReal_pos.2 (by norm_num)
  obtain ⟨C₄, hC₄, ε₄, hε₄, H44⟩ := c27_lemma44 hd hD hκ hconv hζ0 hζ1 one_pos
  obtain ⟨C₃, hC₃, δ₃, hδ₃, ε₃, hε₃, H3⟩ := c27_lemma43_compl hd2 hD hκ hconv (p := 7 / 8)
    (by norm_num)
  set c : ℝ → ℝ := fun r => r ^ (ξ * Q) with hcdef
  have hDw : IsWeakExpMetric d ξ D c := hD
  obtain ⟨M, hM, HM⟩ := l9b_exists_tail (P := normLGFLaw d)
    (X := fun g => Real.exp (ξ * sphereAvg g 1 e))
    (Real.measurable_exp.comp (measurable_const.mul (measurable_sphereAvg_left 1 e))) hθ0
  have hc₁ := hDw.c_pos 1 one_pos
  have hC₃0 : 0 < C₃ := by linarith
  set cc : ℝ := min 1 (min (1 / (2 * C₃ ^ 2 * C₄ * c 1 * M)) (c 1 / (2 * C₃ ^ 2 * C₄ * M)))
    with hcc
  have hcc0 : 0 < cc := lt_min one_pos (lt_min (by positivity) (by positivity))
  have hcc1 : cc ≤ 1 := min_le_left _ _
  have hccA : cc ≤ 1 / (2 * C₃ ^ 2 * C₄ * c 1 * M) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hccB : cc ≤ c 1 / (2 * C₃ ^ 2 * C₄ * M) := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨cc⁻¹, one_le_inv₀ hcc0 |>.2 hcc1, ?_⟩
  -- eventual conditions
  have hrpow : Tendsto (fun ε : ℝ => ε ^ (1 - ζ)) (𝓝[>] 0) (𝓝 0) := by
    have h := (Real.continuousAt_rpow_const (0 : ℝ) (1 - ζ) (Or.inr (by linarith))).tendsto
    rw [Real.zero_rpow (by linarith)] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hlin : Tendsto (fun ε : ℝ => (2 * 4 + 7 : ℝ) ^ d * ε) (𝓝[>] 0) (𝓝 0) :=
    ((continuous_const.mul continuous_id).tendsto' (0 : ℝ) 0 (by simp)).mono_left
      nhdsWithin_le_nhds
  have hev := (l9b_eventually_locHyp_seed hd2 hκ).and ((eventually_mCnt_ge hζ0).and
    ((tendsto_log_inv_nhdsGT_zero.eventually (eventually_gt_atTop 0)).and
      ((hrpow.eventually (ge_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))).and
        ((hlin.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 8 by norm_num))).and
          (Ioo_mem_nhdsGT hδ₃)))))
  obtain ⟨ε₅, hε₅, H5⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  refine ⟨min (min ε₄ ε₃) ε₅, lt_min (lt_min hε₄ hε₃) hε₅, fun ε hε => ?_⟩
  have hε4 : ε < ε₄ := hε.2.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hε3 : ε < ε₃ := hε.2.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  obtain ⟨⟨hε0, hε1, hrad, -, -⟩, hm, hL0, hδ, hlinε, hεδ⟩ :=
    H5 ⟨hε.1, hε.2.trans_le (min_le_right _ _)⟩
  have hθε : ENNReal.ofReal ((2 * 4 + 7 : ℝ) ^ d * ε ^ (1 : ℝ)) ≤ θ := by
    rw [Real.rpow_one, hθ]
    exact ENNReal.ofReal_le_ofReal hlinε.le
  have hε1' : ε < 1 := by
    by_contra hge
    push Not at hge
    have : ε = 1 := le_antisymm hε1 hge
    rw [this, inv_one, Real.log_one] at hL0
    exact lt_irrefl 0 hL0
  set N := nIdx ζ ε with hNdef
  have hNcard : 0 < N.card := by
    rw [card_nIdx]
    have : (0 : ℝ) < mCnt ζ ε := lt_of_lt_of_le (by positivity) hm
    exact_mod_cast this
  set ρ : ℕ → ℝ := fun k => l9bRatio κ ξ c ε (dyad k) with hρ
  have hρpos : ∀ k, 0 < ρ k := by
    intro k
    have h1 := l10a_aEps_pos_seed hd2 hκ ξ (div_pos hε0 (dyad_pos k))
    have h2 := l10a_aEps_pos_seed hd2 hκ ξ hε0
    have h3 := hDw.c_pos (dyad k) (dyad_pos k)
    simp only [hρ, l9bRatio]
    have := dyad_pos k
    positivity
  set a := aEps κ ξ ε with ha
  have ha0 : 0 < a := l10a_aEps_pos_seed hd2 hκ ξ hε0
  set δ' := ε ^ (1 - ζ) with hδ'
  have hδ'0 : 0 < δ' := Real.rpow_pos_of_pos hε0 _
  -- the four events at `(0, 1)` and `(e₁, 1)`, the tail of `e^{ξ h_1(e₁)}`, the normalization
  have hεδ' : ε / 1 < δ₃ := by rw [div_one]; exact hεδ.2
  have hG0 := H3 (normLGFLaw d) id hN ε ⟨hε0, hε3⟩ 1 hε1' le_rfl hεδ' 0
  have hGe := H3 (normLGFLaw d) id hN ε ⟨hε0, hε3⟩ 1 hε1' le_rfl hεδ' e
  have hnorm : (normLGFLaw d) {g | sphereAvg g 1 0 ≠ 0} = 0 := by
    have := hN.2
    rwa [ae_iff] at this
  have he2 : (2 : ℝ) • e ∈ ball (0 : Rd d) 4 := by
    rw [mem_ball, dist_zero_right, he, l9b_norm_two_e₁ hd2]; norm_num
  have h0B : (0 : Rd d) ∈ ball (0 : Rd d) 4 := mem_ball_self (by norm_num)
  have hAball : ∀ x ∈ ball (0 : Rd d) δ', ‖x‖ ≤ 1 / 2 := fun x hx => by
    rw [mem_ball, dist_zero_right] at hx; linarith
  have hBball : ∀ y ∈ ball ((2 : ℝ) • e) δ', 1 ≤ ‖y‖ := by
    intro y hy
    rw [mem_ball, dist_eq_norm] at hy
    have h1 : ‖(2 : ℝ) • e‖ ≤ ‖y‖ + ‖y - (2 : ℝ) • e‖ := by
      calc ‖(2 : ℝ) • e‖ = ‖y - (y - (2 : ℝ) • e)‖ := by congr 1; abel
        _ ≤ _ := norm_sub_le _ _
    rw [he, l9b_norm_two_e₁ hd2] at h1
    linarith
  -- a good sample
  have hgood : ∀ (B : Set (DistRd d)), (normLGFLaw d) B ≤ θ →
      ∃ g, g ∉ B ∧ shellGood κ ξ D c ε C₃ 0 1 g ∧ shellGood κ ξ D c ε C₃ e 1 g ∧
        Real.exp (ξ * sphereAvg g 1 e) ≤ M ∧ sphereAvg g 1 0 = 0 := by
    intro B hB
    by_contra hall
    push Not at hall
    have hcover : (univ : Set (DistRd d)) ⊆ B ∪ {g | shellGood κ ξ D c ε C₃ 0 1 g}ᶜ ∪
        {g | shellGood κ ξ D c ε C₃ e 1 g}ᶜ ∪ {g | M < Real.exp (ξ * sphereAvg g 1 e)} ∪
        {g | sphereAvg g 1 0 ≠ 0} := by
      intro g _
      by_cases hgB : g ∈ B
      · exact Or.inl (Or.inl (Or.inl (Or.inl hgB)))
      by_cases h0 : shellGood κ ξ D c ε C₃ 0 1 g
      · by_cases h1 : shellGood κ ξ D c ε C₃ e 1 g
        · by_cases h2 : Real.exp (ξ * sphereAvg g 1 e) ≤ M
          · exact Or.inr (hall g hgB h0 h1 h2)
          · exact Or.inl (Or.inr (not_le.1 h2))
        · exact Or.inl (Or.inl (Or.inr h1))
      · exact Or.inl (Or.inl (Or.inl (Or.inr h0)))
    have h1 := measure_mono (μ := normLGFLaw d) hcover
    rw [measure_univ] at h1
    have h2 : (1 : ℝ≥0∞) ≤ θ + θ + θ + θ + 0 := by
      refine h1.trans ?_
      refine (measure_union_le _ _).trans (add_le_add ?_ hnorm.le)
      refine (measure_union_le _ _).trans (add_le_add ?_ HM)
      refine (measure_union_le _ _).trans (add_le_add ?_ ?_)
      · refine (measure_union_le _ _).trans (add_le_add hB ?_)
        exact hG0.trans (by rw [hθ]; norm_num)
      · exact hGe.trans (by rw [hθ]; norm_num)
    have h3 : θ + θ + θ + θ + 0 = ENNReal.ofReal (1 / 2) := by
      rw [hθ, add_zero, ← ENNReal.ofReal_add (by norm_num) (by norm_num),
        ← ENNReal.ofReal_add (by norm_num) (by norm_num),
        ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
      norm_num
    rw [h3] at h2
    have : ENNReal.ofReal (1 / 2) < 1 := by
      rw [← ENNReal.ofReal_one]; exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 (by norm_num)
    exact absurd h2 (not_le.2 this)
  -- the low ratios
  have hlow : 10 * (N.filter fun k => ρ k < cc).card < N.card := by
    by_contra hcon
    push Not at hcon
    set R := N.filter fun k => ρ k < cc
    have hRne : R.Nonempty := by
      rw [← Finset.card_pos]; omega
    set m₀ := R.inf' hRne ρ
    have hm₀ : 0 < m₀ := by
      obtain ⟨k, -, hk⟩ := Finset.exists_mem_eq_inf' hRne ρ
      have : m₀ = ρ k := hk
      rw [this]; exact hρpos k
    have hratio : ∀ k ∈ R, m₀ ≤ ρ k ∧ ρ k ≤ cc := fun k hk =>
      ⟨Finset.inf'_le _ hk, (Finset.mem_filter.1 hk).2.le⟩
    have hbad := (H44 4 (by norm_num) (ball (0 : Rd d) 4) ball_subset_closedBall (normLGFLaw d) id
      hN ε ⟨hε0, hε4⟩ R (Finset.filter_subset _ _) hcon m₀ cc hm₀ hcc0 hratio).trans hθε
    obtain ⟨g, hgB, hg0, hge, hgM, hgn⟩ := hgood _ hbad
    simp only [mem_ofPred_eq, not_not, id] at hgB
    have h49 := (hgB 0 h0B ((2 : ℝ) • e) he2).1
    have hψ : Continuous (locField κ ε g) := continuous_locField hK hrad g
    -- lower bound of the left side
    have hL : ENNReal.ofReal C₃⁻¹ ≤ ENNReal.ofReal a⁻¹ * fieldSetDistIn ξ (locField κ ε g)
        (thickening δ' (ball 0 4)) (ball 0 δ') (ball ((2 : ℝ) • e) δ') := by
      have h3 := hg0.2.2.1
      rw [hgn, mul_zero, Real.exp_zero, mul_one, one_mul, div_one,
        show (3 : ℝ) * 1 = 3 by norm_num] at h3
      have := l9b_lfppSetDist_le_fieldSetDistIn (ξ := ξ) hψ (thickening δ' (ball 0 4))
        (ball 0 δ') (ball ((2 : ℝ) • e) δ') hAball hBball
      calc ENNReal.ofReal C₃⁻¹ = ENNReal.ofReal a⁻¹ * ENNReal.ofReal (C₃⁻¹ * a) := by
            rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; field_simp
        _ ≤ _ := by gcongr; exact (ENNReal.ofReal_le_ofReal h3).trans this
    -- upper bound of the right side
    have hR : (D g).internal (ball 0 4) 0 ((2 : ℝ) • e) ≤ ENNReal.ofReal (C₃ * c 1 * M) := by
      have h2 := hge.2.1
      calc (D g).internal (ball 0 4) 0 ((2 : ℝ) • e) ≤ sphereDiam (D g) e 1 :=
            l9b_internal_le_sphereDiam (D g) (l9b_ann_e₁_subset_ball4 hd2)
              (l9b_zero_mem_sphere_e₁ hd2) (l9b_two_e₁_mem_sphere_e₁ hd2)
        _ ≤ ENNReal.ofReal (C₃ * c 1 * Real.exp (ξ * sphereAvg g 1 e)) := h2
        _ ≤ ENNReal.ofReal (C₃ * c 1 * M) := ENNReal.ofReal_le_ofReal (by gcongr)
    have hcomb := hL.trans (h49.trans (show ENNReal.ofReal (C₄ * cc) *
      (D g).internal (ball 0 4) 0 ((2 : ℝ) • e) ≤ ENNReal.ofReal (C₄ * cc) *
        ENNReal.ofReal (C₃ * c 1 * M) by gcongr))
    rw [← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_le_ofReal_iff (by positivity)] at hcomb
    have : C₄ * cc * (C₃ * c 1 * M) ≤ C₃⁻¹ / 2 := by
      calc C₄ * cc * (C₃ * c 1 * M) ≤ C₄ * (1 / (2 * C₃ ^ 2 * C₄ * c 1 * M)) * (C₃ * c 1 * M) := by
            gcongr
        _ = C₃⁻¹ / 2 := by field_simp
    have hC₃i : 0 < C₃⁻¹ := inv_pos.2 hC₃0
    linarith
  -- the high ratios
  have hhigh : 10 * (N.filter fun k => cc⁻¹ < ρ k).card < N.card := by
    by_contra hcon
    push Not at hcon
    set R := N.filter fun k => cc⁻¹ < ρ k
    have hRne : R.Nonempty := by
      rw [← Finset.card_pos]; omega
    set M₀ := R.sup' hRne ρ
    have hM₀ : 0 < M₀ := by
      obtain ⟨k, hk⟩ := hRne
      exact (hρpos k).trans_le (Finset.le_sup' _ hk)
    have hratio : ∀ k ∈ R, cc⁻¹ ≤ ρ k ∧ ρ k ≤ M₀ := fun k hk =>
      ⟨(Finset.mem_filter.1 hk).2.le, Finset.le_sup' _ hk⟩
    have hbad := (H44 4 (by norm_num) (ball (0 : Rd d) 4) ball_subset_closedBall (normLGFLaw d) id
      hN ε ⟨hε0, hε4⟩ R (Finset.filter_subset _ _) hcon cc⁻¹ M₀ (inv_pos.2 hcc0) hM₀ hratio).trans
        hθε
    obtain ⟨g, hgB, hg0, hge, hgM, hgn⟩ := hgood _ hbad
    simp only [mem_ofPred_eq, not_not, id] at hgB
    have h410 := (hgB 0 h0B ((2 : ℝ) • e) he2).2
    have hψ : Continuous (locField κ ε g) := continuous_locField hK hrad g
    have hL : ENNReal.ofReal (C₃⁻¹ * c 1) ≤ setDistIn (D g) (thickening δ' (ball 0 4))
        (ball 0 δ') (ball ((2 : ℝ) • e) δ') := by
      have h1 := hg0.1
      rw [hgn, mul_zero, Real.exp_zero, mul_one] at h1
      refine h1.trans (l9b_acrossDist_le_setDistIn (D g) _ (fun x hx => ?_) fun y hy => ?_)
      · rw [sub_zero]; have := hAball x hx
        rw [mem_ball, dist_zero_right] at hx; linarith
      · rw [sub_zero]; exact hBball y hy
    have hR : fieldDistIn ξ (locField κ ε g) (ball 0 4) 0 ((2 : ℝ) • e) ≤
        ENNReal.ofReal (C₃ * a * M) := by
      have h4 := hge.2.2.2
      rw [one_mul, div_one] at h4
      calc fieldDistIn ξ (locField κ ε g) (ball 0 4) 0 ((2 : ℝ) • e)
          ≤ ENNReal.ofReal (DGZ.lfppDiam ξ (locField κ ε g) (sphere e 1) (ann e (1 / 2) (2 * 1))) :=
            l9b_fieldDistIn_le_lfppDiam hd2 hψ one_pos (l9b_ann_e₁_subset_ball4 hd2)
              (l9b_zero_mem_sphere_e₁ hd2) (l9b_two_e₁_mem_sphere_e₁ hd2)
        _ ≤ ENNReal.ofReal (C₃ * a * Real.exp (ξ * sphereAvg g 1 e)) := ENNReal.ofReal_le_ofReal h4
        _ ≤ ENNReal.ofReal (C₃ * a * M) := ENNReal.ofReal_le_ofReal (by gcongr)
    have hcomb := hL.trans (h410.trans (show ENNReal.ofReal (C₄ * cc⁻¹⁻¹) *
      (ENNReal.ofReal a⁻¹ * fieldDistIn ξ (locField κ ε g) (ball 0 4) 0 ((2 : ℝ) • e)) ≤
        ENNReal.ofReal (C₄ * cc⁻¹⁻¹) * (ENNReal.ofReal a⁻¹ * ENNReal.ofReal (C₃ * a * M)) by
      gcongr))
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_le_ofReal_iff (by positivity)] at hcomb
    have : C₄ * cc⁻¹⁻¹ * (a⁻¹ * (C₃ * a * M)) ≤ C₃⁻¹ * c 1 / 2 := by
      rw [inv_inv]
      calc C₄ * cc * (a⁻¹ * (C₃ * a * M)) = C₄ * cc * (C₃ * M) := by field_simp
        _ ≤ C₄ * (c 1 / (2 * C₃ ^ 2 * C₄ * M)) * (C₃ * M) := by gcongr
        _ = C₃⁻¹ * c 1 / 2 := by field_simp
    have hpos : 0 < C₃⁻¹ * c 1 := by positivity
    linarith
  -- counting
  set G := N.filter fun k => cc⁻¹⁻¹ ≤ ρ k ∧ ρ k ≤ cc⁻¹
  have hsplit : N ⊆ G ∪ (N.filter fun k => ρ k < cc) ∪ (N.filter fun k => cc⁻¹ < ρ k) := by
    intro k hk
    by_cases h1 : ρ k < cc
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hk, h1⟩))
    by_cases h2 : cc⁻¹ < ρ k
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hk, h2⟩)
    · refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hk, ?_⟩))
      rw [inv_inv]
      exact ⟨not_lt.1 h1, not_lt.1 h2⟩
  have hcardle := (Finset.card_le_card hsplit).trans
    ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  show N.card ≤ 2 * G.card
  omega

end HigherDimLFPPAS.Coarse
