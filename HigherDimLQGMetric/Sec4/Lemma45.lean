import HigherDimLQGMetric.Sec4.Lemma45Geom

/-!
# [1] Lemma 4.5: good ratios (packet L9b; MA6 P10)

`ref1_lemma45`: there are `C ≥ 1` and `ε₁ > 0` such that for every `ε ∈ (0, ε₁)` at least half of the radii
`r = 2^{-k}`, `k ∈ N^ε`, satisfy `C⁻¹ ≤ r 𝔞_{ε/r}/(c_r 𝔞_ε) ≤ C`.

[1]'s contradiction argument, on the canonical space `(DistRd d, normLGFLaw d)`: if at least `|N^ε|/10` ratios were
`< c`, Lemma 4.4 (4.9) with `z = 0`, `w = 2e₁`, `U = B_4(0)` and that set of radii would give, with probability
`≥ 7/8`, `𝔞_ε⁻¹ D̂(B(0), B(2e₁); B(B_4)) ≤ C₄ c D(0, 2e₁; B_4)`, while with probability `≥ 1 - 3/8` the left side
is `≥ C₃⁻¹` (event (3) of Lemma 4.3 at `(0, 1)`) and `D(0, 2e₁; B_4) ≤ diam_{A_{1/2,2}(e₁)} ∂B_1(e₁) ≤ C₃ c_1 M`
(event (2) at `(e₁, 1)` and `e^{ξ h_1(e₁)} ≤ M`); this is impossible for `c` small. Symmetrically for ratios
`> c⁻¹` with (4.10), events (1) at `(0, 1)` and (4) at `(e₁, 1)`. The proof covers `ε < ε₁`, which is what
Prop 4.2 uses (for `ε ∈ [ε₁, 1)` [1] would need the local boundedness of `c_r` and `𝔞_δ`, MA6 P11).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁ lfppDistOn PcwJoined)

variable {d : ℕ}

/-- a real random variable is bounded in probability -/
theorem l9b_exists_tail {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hX : Measurable X) {θ : ℝ≥0∞} (hθ : 0 < θ) :
    ∃ M : ℝ, 0 < M ∧ P {ω | M < X ω} ≤ θ := by
  let s : ℕ → Set Ω := fun n => {ω | (n : ℝ) + 1 < X ω}
  have hsm : ∀ n, MeasurableSet (s n) := fun n => measurableSet_lt measurable_const hX
  have hsa : Antitone s := by
    intro m n hmn ω hω
    show (m : ℝ) + 1 < X ω
    have : (m : ℝ) ≤ n := by exact_mod_cast hmn
    exact lt_of_le_of_lt (by linarith) hω
  have hI : (⋂ n, s n) = ∅ := by
    ext ω
    simp only [mem_iInter, mem_empty_iff_false, iff_false, not_forall]
    obtain ⟨n, hn⟩ := exists_nat_gt (X ω)
    exact ⟨n, fun h => by
      have : (n : ℝ) + 1 < X ω := h
      linarith⟩
  have ht := tendsto_measure_iInter_atTop (μ := P) (fun n => (hsm n).nullMeasurableSet) hsa
    ⟨0, measure_ne_top _ _⟩
  rw [hI, measure_empty] at ht
  obtain ⟨n, hn⟩ := (ht.eventually (ge_mem_nhds hθ)).exists
  exact ⟨n + 1, by positivity, hn⟩

theorem l9b_norm_two_e₁ (hd : 2 ≤ d) : ‖(2 : ℝ) • HigherDimLFPP.e₁ d‖ = 2 := by
  rw [norm_smul, HigherDimLFPP.norm_e₁ (by omega), Real.norm_eq_abs, abs_two, mul_one]

theorem l9b_zero_mem_sphere_e₁ (hd : 2 ≤ d) : (0 : Rd d) ∈ sphere (HigherDimLFPP.e₁ d) 1 := by
  rw [mem_sphere, dist_eq_norm, zero_sub, norm_neg, HigherDimLFPP.norm_e₁ (by omega)]

theorem l9b_two_e₁_mem_sphere_e₁ (hd : 2 ≤ d) :
    (2 : ℝ) • HigherDimLFPP.e₁ d ∈ sphere (HigherDimLFPP.e₁ d) 1 := by
  rw [mem_sphere, dist_eq_norm, show (2 : ℝ) • HigherDimLFPP.e₁ d - HigherDimLFPP.e₁ d =
    HigherDimLFPP.e₁ d by rw [two_smul, add_sub_cancel_right], HigherDimLFPP.norm_e₁ (by omega)]

theorem l9b_ann_e₁_subset_ball4 (hd : 2 ≤ d) :
    ann (HigherDimLFPP.e₁ d) (1 / 2) (2 * 1) ⊆ ball (0 : Rd d) 4 := by
  intro x hx
  rw [mem_ball, dist_zero_right]
  have h1 : ‖x‖ ≤ ‖x - HigherDimLFPP.e₁ d‖ + ‖HigherDimLFPP.e₁ d‖ := by
    calc ‖x‖ = ‖(x - HigherDimLFPP.e₁ d) + HigherDimLFPP.e₁ d‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  rw [HigherDimLFPP.norm_e₁ (by omega)] at h1
  have := hx.2
  linarith

/-- **[1] Lemma 4.5** (MA6 P10; small `ε`). -/
theorem ref1_lemma45 (hL6a : ∀ (d : ℕ) (ξ : ℝ) (κ : Rd d → ℝ), L6a_tight d ξ κ)
    (hB2 : ∀ (d : ℕ) (κ : Rd d → ℝ) (ξ Q : ℝ), DGZ.RealEpsAdapterShape d κ ξ Q)
    (hd : 3 ≤ d) {ξ : ℝ} (hξ : 0 < ξ) (hsub : Real.sqrt (2 * d) < distExp d ξ)
    {κ : Rd d → ℝ} (hκ : HigherDimLFPP.IsLFPPKernel κ) {D : DistRd d → ContMetric d} {c : ℝ → ℝ}
    (hD : IsWeakExpMetric d ξ D c) {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ ε ∈ Ioo (0 : ℝ) ε₁,
      (nIdx ζ ε).card ≤ 2 * ((nIdx ζ ε).filter fun k =>
        C⁻¹ ≤ l9bRatio κ ξ c ε (dyad k) ∧ l9bRatio κ ξ c ε (dyad k) ≤ C).card := by
  have hd2 : 2 ≤ d := by omega
  have hK := convKernel_contDiff (d := d) (by omega) hκ
  have hprob := l9b_normLGFLaw_prob hd2
  have hN := l9b_normLGFLaw_normalized hd2
  set e := HigherDimLFPP.e₁ d with he
  set θ : ℝ≥0∞ := ENNReal.ofReal (1 / 8) with hθ
  have hθ0 : 0 < θ := ENNReal.ofReal_pos.2 (by norm_num)
  obtain ⟨C₄, hC₄, H44⟩ := ref1_lemma44 hL6a hB2 hd hξ hsub hκ hD hζ0 hζ1
  obtain ⟨ε₄, hε₄, H4⟩ := H44 (ball (0 : Rd d) 4) isBounded_ball θ hθ0
  obtain ⟨C₃, hC₃, ε₃, hε₃, H3⟩ := ref1_lemma43_compl hL6a hB2 hd hξ hsub hκ hD (p := 7 / 8)
    (by norm_num)
  obtain ⟨M, hM, HM⟩ := l9b_exists_tail (P := normLGFLaw d)
    (X := fun g => Real.exp (ξ * sphereAvg g 1 e))
    (Real.measurable_exp.comp (measurable_const.mul (measurable_sphereAvg_left 1 e))) hθ0
  have hc₁ := hD.c_pos 1 one_pos
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
  have hev := (l9b_eventually_locHyp hd2 hκ).and ((eventually_mCnt_ge hζ0).and
    ((tendsto_log_inv_nhdsGT_zero.eventually (eventually_gt_atTop 0)).and
      (hrpow.eventually (ge_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num)))))
  obtain ⟨ε₅, hε₅, H5⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  refine ⟨min (min ε₄ ε₃) ε₅, lt_min (lt_min hε₄ hε₃) hε₅, fun ε hε => ?_⟩
  have hε4 : ε < ε₄ := hε.2.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hε3 : ε < ε₃ := hε.2.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  obtain ⟨⟨hε0, hε1, hrad, -, -⟩, hm, hL0, hδ⟩ := H5 ⟨hε.1, hε.2.trans_le (min_le_right _ _)⟩
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
    have h1 := l10a_aEps_pos hd2 hκ ξ (div_pos hε0 (dyad_pos k))
    have h2 := l10a_aEps_pos hd2 hκ ξ hε0
    have h3 := hD.c_pos (dyad k) (dyad_pos k)
    simp only [hρ, l9bRatio]
    have := dyad_pos k
    positivity
  set a := aEps κ ξ ε with ha
  have ha0 : 0 < a := l10a_aEps_pos hd2 hκ ξ hε0
  set δ' := ε ^ (1 - ζ) with hδ'
  have hδ'0 : 0 < δ' := Real.rpow_pos_of_pos hε0 _
  -- the four events at `(0, 1)` and `(e₁, 1)`, the tail of `e^{ξ h_1(e₁)}`, the normalization
  have hG0 := H3 (normLGFLaw d) id hN ε ⟨hε0, hε3⟩ 1 hε1' le_rfl 0
  have hGe := H3 (normLGFLaw d) id hN ε ⟨hε0, hε3⟩ 1 hε1' le_rfl e
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
    have hbad := H4 (normLGFLaw d) id hN ε ⟨hε0, hε4⟩ R (Finset.filter_subset _ _) hcon m₀ cc
      hm₀ hcc0 hratio
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
    have hbad := H4 (normLGFLaw d) id hN ε ⟨hε0, hε4⟩ R (Finset.filter_subset _ _) hcon cc⁻¹ M₀
      (inv_pos.2 hcc0) hM₀ hratio
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

end HigherDimLQGMetric
