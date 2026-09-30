import QuantumZipper.Proofs.Complex.JSShadowACL6

/-!
# EXT-JS node B1: `e` is absolutely continuous on almost every horizontal line

Blueprint `blueprint/EXT_JS_BLUEPRINT.md`, §2 "(C0: SH ⇒ removable.)", step 5 (conclusion), and
§3 node B1 `acl_horizontal_of_shadow`.

Source: P. W. Jones and S. K. Smirnov, *Removability theorems for Sobolev functions and
quasiconformal maps*, Ark. Mat. 38 (2000) 263–279, §2, proof of Proposition 1, pp. 270–272:
estimate (11) holds with only cubes of size `≤ Λ` charged, for every `Λ`, and the charged sum tends
to `0` on almost every line; hence on almost every line the variation of `f` is carried by `Kᶜ`.

Here, for a height `y` at which the slice of `γ = 1_{Kᶜ} e'` is locally integrable
(`ae_forall_lintegral_sliceH_lt_top`, step 2) and every line shadow function tends to `0`
(`ae_tendsto_lineShadow`, step 5), the chain estimate `norm_line_sub_le` (step 4) is applied with
`n` large and `δ` small: the oscillation term tends to `0` with `n`, the tent image diameters are
`≤ √(level-n shadow sum) → 0`, and `∫_{(a,b] ∩ {t + iy ∈ N_δ(K)}} ‖γ‖ → 0` as `δ → 0` by dominated
convergence, because `γ = 0` on `K` (so, unlike the blueprint, the zero area of `K` is not used).

Main results: `line_identity_of_good`, `acl_horizontal_of_shadow`.
-/

noncomputable section

open MeasureTheory Set Complex Metric Filter Topology
open scoped ENNReal

namespace QuantumZipper.JS

/-- **The line identity at a good height.** -/
theorem line_identity_of_good {K : Set ℂ} (hK : IsCompact K) {ι : Type*} [Fintype ι] {R : ℝ}
    {F : ι → ℂ → ℂ} (hF : ∀ i, IsChart K R (F i)) (hSH : ∀ i, shadowSum R (F i) < ⊤)
    (hcov : K ⊆ ⋃ i, F i '' ((↑) '' Set.Icc (-R) R)) (e : ℂ ≃ₜ ℂ)
    (he : DifferentiableOn ℂ e Kᶜ) {y : ℝ}
    (hG1 : ∀ M : ℕ, ∫⁻ t in uIoc (-(M : ℝ)) (M : ℝ),
      ‖sliceH (Kᶜ.indicator (deriv e)) y t‖ₑ < ⊤)
    (hG2 : ∀ i, Tendsto (fun n => lineShadow R (e ∘ F i) (F i) n y) atTop (𝓝 0)) (a b : ℝ) :
    e (b + y * I) - e (a + y * I) = ∫ t in a..b, Kᶜ.indicator (deriv e) (t + y * I) := by
  set γ : ℝ → ℂ := fun t => Kᶜ.indicator (deriv e) ((t : ℂ) + y * I) with hγdef
  have hline : Continuous fun t : ℝ => (t : ℂ) + y * I := by fun_prop
  have hmeas : Measurable γ :=
    ((measurable_deriv e).indicator hK.isClosed.isOpen_compl.measurableSet).comp
      hline.measurable
  have hint : ∀ a b : ℝ, IntegrableOn γ (Icc a b) := by
    intro a b
    obtain ⟨M, hM⟩ := exists_nat_gt (max |a| |b|)
    have hsub : Icc a b ⊆ uIoc (-(M : ℝ)) (M : ℝ) := by
      rw [uIoc_of_le (by linarith [le_max_left |a| |b|, abs_nonneg a])]
      intro t ht
      have h1 := le_max_left |a| |b|
      have h2 := le_max_right |a| |b|
      exact ⟨by linarith [neg_abs_le a, ht.1], by linarith [le_abs_self b, ht.2]⟩
    exact (show IntegrableOn γ (uIoc (-(M : ℝ)) (M : ℝ)) volume from
      ⟨hmeas.aestronglyMeasurable, hG1 M⟩).mono_set hsub
  -- the case `a ≤ b`
  have hmain : ∀ a b : ℝ, a ≤ b →
      e (b + y * I) - e (a + y * I) = ∫ t in a..b, Kᶜ.indicator (deriv e) (t + y * I) := by
    intro a b hab
    set X := e (b + y * I) - e (a + y * I) - ∫ t in a..b, Kᶜ.indicator (deriv e) (t + y * I)
      with hX
    suffices hkey : ∀ η > 0, ‖X‖ < η by
      by_contra hne
      have := hkey ‖X‖ (norm_pos_iff.2 (sub_ne_zero.2 hne))
      exact lt_irrefl _ this
    intro η hη
    -- small neighbourhoods of `K` carry little of `‖γ‖`
    set A : ℝ → Set ℝ := fun δ => {t : ℝ | (t : ℂ) + y * I ∈ cthickening δ K} with hA
    have hAm : ∀ δ, MeasurableSet (A δ) := fun δ =>
      (isClosed_cthickening.preimage hline).measurableSet
    have hJ : Tendsto (fun δ => ∫ t in Ioc a b, (A δ).indicator (fun t => ‖γ t‖) t)
        (𝓝 (0 : ℝ)) (𝓝 (∫ t in Ioc a b, (0 : ℝ))) := by
      refine tendsto_integral_filter_of_dominated_convergence (fun t => ‖γ t‖)
        (Eventually.of_forall fun δ => (hmeas.norm.indicator (hAm δ)).aestronglyMeasurable)
        (Eventually.of_forall fun δ => Eventually.of_forall fun t => ?_)
        ((show IntegrableOn (fun t => ‖γ t‖) (Icc a b) volume from (hint a b).norm).mono_set
          Ioc_subset_Icc_self)
        (Eventually.of_forall fun t => ?_)
      · exact (norm_indicator_le_norm_self _ _).trans (norm_norm _).le
      · by_cases htK : (t : ℂ) + y * I ∈ K
        · have hγ0 : γ t = 0 := indicator_of_notMem (show (t : ℂ) + y * I ∉ Kᶜ from fun h => h htK) _
          refine tendsto_const_nhds.congr fun δ => ?_
          by_cases htA : t ∈ A δ
          · simp [indicator_of_mem htA, hγ0]
          · simp [indicator_of_notMem htA]
        · have hev := eventually_notMem_cthickening_of_infEDist_pos
            (E := K) (x := (t : ℂ) + y * I) (by rwa [hK.isClosed.closure_eq])
          refine tendsto_const_nhds.congr' (hev.mono fun δ hδ => ?_)
          exact (indicator_of_notMem (show t ∉ A δ from hδ) _).symm
    rw [integral_zero] at hJ
    obtain ⟨δ, hδJ, hδ⟩ := ((((hJ.eventually (gt_mem_nhds (half_pos hη))).filter_mono
      nhdsWithin_le_nhds).and (self_mem_nhdsWithin (s := Ioi (0 : ℝ))))).exists
    have hδJ' : ∫ t in Ioc a b ∩ {t : ℝ | (t : ℂ) + y * I ∈ cthickening δ K},
        ‖Kᶜ.indicator (deriv e) ((t : ℂ) + y * I)‖ < η / 2 := by
      rw [integral_indicator (hAm δ), Measure.restrict_restrict (hAm δ), inter_comm] at hδJ
      exact hδJ
    -- a level `n` with small oscillation terms and small tent images
    have hD : Tendsto (fun n => ∑ i, 3 * (lineShadow R (e ∘ F i) (F i) n y).toReal) atTop
        (𝓝 0) := by
      have := tendsto_finsetSum (Finset.univ : Finset ι) fun i _ =>
        ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hG2 i)).const_mul 3
      simpa using this
    have ev1 := hD.eventually (gt_mem_nhds (half_pos hη))
    have ev2 : ∀ᶠ n in atTop, ∀ i, lineShadow R (e ∘ F i) (F i) n y ≠ ⊤ :=
      eventually_all.2 fun i => ((hG2 i).eventually (gt_mem_nhds zero_lt_one)).mono
        fun n hn => ne_top_of_lt hn
    have ev3 : ∀ᶠ n in atTop, ∀ i, ∀ j < 2 ^ n,
        ediam (F i '' tent R n j) ≤ ENNReal.ofReal δ := by
      refine eventually_all.2 fun i => ?_
      have hc : (0 : ℝ≥0∞) < ENNReal.ofReal δ ^ 2 :=
        ENNReal.pow_pos (ENNReal.ofReal_pos.2 (show (0 : ℝ) < δ from hδ)) 2
      have hlev : Tendsto (ShadowNull.shadowLevel R (F i)) atTop (𝓝 0) :=
        ENNReal.tendsto_atTop_zero_of_tsum_ne_top (hSH i).ne
      refine (hlev.eventually (gt_mem_nhds hc)).mono fun n hn j hj => ?_
      by_contra hcon
      have h1 : ENNReal.ofReal δ ^ 2 ≤ ediam (F i '' tent R n j) ^ 2 :=
        pow_le_pow_left₀ zero_le (not_le.1 hcon).le 2
      have h2 : ediam (F i '' tent R n j) ^ 2 ≤ ShadowNull.shadowLevel R (F i) n :=
        Finset.single_le_sum (f := fun j => ediam (F i '' tent R n j) ^ 2)
          (fun _ _ => zero_le) (Finset.mem_range.2 hj)
      exact absurd (h1.trans h2) (not_le.2 hn)
    obtain ⟨n, hn1, hn2, hn3⟩ := (ev1.and (ev2.and ev3)).exists
    have hbound := norm_line_sub_le hK hF hcov e he hab (hint a b) (le_of_lt hδ) hn3 hn2
    calc ‖X‖ ≤ _ := hbound
      _ < η / 2 + η / 2 := add_lt_add hn1 hδJ'
      _ = η := add_halves η
  rcases le_total a b with hab | hba
  · exact hmain a b hab
  · have h := hmain b a hba
    rw [intervalIntegral.integral_symm] at h
    linear_combination -h

/-- **EXT-JS node B1 (`acl_horizontal_of_shadow`).** If `K` is covered by finitely many charts
with finite shadow sums and `e : ℂ ≃ₜ ℂ` is holomorphic off `K`, then on almost every horizontal
line `e` is the integral of `1_{Kᶜ} e'`. This is hypothesis `hh` of A4
(`differentiable_of_acl`, `JSMorera.lean`). -/
theorem acl_horizontal_of_shadow {K : Set ℂ} (hK : IsCompact K) {ι : Type*} [Fintype ι] {R : ℝ}
    {F : ι → ℂ → ℂ} (hF : ∀ i, IsChart K R (F i)) (hSH : ∀ i, shadowSum R (F i) < ⊤)
    (hcov : K ⊆ ⋃ i, F i '' ((↑) '' Set.Icc (-R) R)) (e : ℂ ≃ₜ ℂ)
    (he : DifferentiableOn ℂ e Kᶜ) :
    ∀ᵐ y : ℝ, ∀ a b : ℝ,
      e (b + y * Complex.I) - e (a + y * Complex.I)
        = ∫ t in a..b, Kᶜ.indicator (deriv e) (t + y * Complex.I) := by
  have h1 := ae_forall_lintegral_sliceH_lt_top hK he
  have h2 : ∀ᵐ y : ℝ, ∀ i, Tendsto (fun n => lineShadow R (e ∘ F i) (F i) n y) atTop (𝓝 0) :=
    ae_all_iff.2 fun i => ae_tendsto_lineShadow (hF i) (hSH i) (isChart_comp (hF i) e he)
  filter_upwards [h1, h2] with y hy1 hy2
  exact fun a b => line_identity_of_good hK hF hSH hcov e he hy1 hy2 a b

end QuantumZipper.JS
