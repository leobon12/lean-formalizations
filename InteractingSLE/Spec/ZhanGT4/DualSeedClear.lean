/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.D9Clear

/-!
# Zhan's A.1.6, the conformal part I: the far obstacle keeps a uniform distance from every omitted real point

Packet PROVE-ZHAN-GT4-A19. Source: Astra, *Follow-up proofs*, §A.1.3 (`source/external/AstraIG1/ig1_followup_proofs.txt`
L314–L330, R38): "Consequently the real image interval of `K_j` has a neighborhood, of uniform positive width in the
`g_j`-chart, disjoint from `g_j(H_k)`", and §A.1.6 (L495–L497): "The opposite-hull map `h_j` is analytic across the
entire relevant real interval, with positive derivative."

A6's `exists_le_norm_fwdMap_uniform` gives the uniform clearance at the driver `W_t`. The seed factors (D13)–(D15)
evaluate `h_j` at the seed coordinates `V^m_t`, which lie on the image interval of the hull but need not be near the
driver. A6's proof only uses that the reflection of `g_t` across a far real disc omits `W_t`; it omits every real value
`v` that is not the image of an alive real point. So the same constant `r` works for every such `v`:

* `real_not_mem_image_of_refl`: the reflection omits `v` if no alive real point of the disc is mapped to `v`;
* **`exists_le_norm_fwdMap_sub_uniform`**: there is `r > 0` (depending only on the enclosure `H₁`, the far set `S₂` and
  `δ`) such that for every continuous driver with hull in `H₁` up to `T`, every `t ≤ T`, `a ∈ S₂` and every real `v`
  that is not `g_t(y)` for an alive real `y ≠ W_0`: `r ≤ |g_t(a) − v|`. For `v = W_t` this is A6's lemma.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric
open scoped ComplexConjugate

namespace InteractingSLE.ZhanGT4

open QuantumZipper (H IsForwardSol fwdMap fwdHull)

/-- If `B(x, δ)` misses `K_t`, no real point of `B(x, δ/2)` is the starting point `W 0`, and no alive real point `y` is
mapped to `v` (`g_t(y) = u_t + W_t ≠ v`), then the Schwarz reflection `G` of `g_t` across `B(x, δ/2) ∩ ℝ` omits `v`
(A6's `driver_not_mem_image_of_refl` with `W_t` replaced by `v`). -/
theorem real_not_mem_image_of_refl {W : ℝ → ℝ} (hW : Continuous W) {t : ℝ} (ht : 0 ≤ t)
    {x δ : ℝ} (hδ : 0 < δ) (hd : Disjoint (ball (x : ℂ) δ) (fwdHull W t))
    (h0 : ∀ y : ℝ, (y : ℂ) ∈ ball (x : ℂ) (δ / 2) → y ≠ W 0) {v : ℝ}
    (hv : ∀ (y : ℝ) (u : ℝ → ℂ), y ≠ W 0 → IsForwardSol W (y : ℂ) t u → u t + (W t : ℂ) ≠ (v : ℂ)) {G : ℂ → ℂ}
    (hGd : DifferentiableOn ℂ G (ball (x : ℂ) (δ / 2)))
    (hGg : EqOn G (fun z => fwdMap W t z + W t) (ball (x : ℂ) (δ / 2) ∩ H))
    (hup : ∀ z ∈ ball (x : ℂ) (δ / 2), 0 < z.im → 0 < (G z).im)
    (hlow : ∀ z ∈ ball (x : ℂ) (δ / 2), z.im < 0 → (G z).im < 0) :
    (v : ℂ) ∉ G '' ball (x : ℂ) (δ / 2) := by
  rintro ⟨z, hz, hzW⟩
  rcases lt_trichotomy z.im 0 with hneg | hzero | hpos
  · have := hlow z hz hneg
    rw [hzW] at this; simp at this
  · -- a real point of the disc
    set y : ℝ := z.re with hy
    have hzy : z = (y : ℂ) := by
      apply Complex.ext <;> simp [hy, hzero]
    rw [hzy] at hz hzW
    have hy0 := h0 y hz
    have hdy : Disjoint (ball (y : ℂ) (δ / 2)) (fwdHull W t) := by
      refine hd.mono_left (ball_subset_ball' ?_)
      have := mem_ball.1 hz
      linarith
    obtain ⟨u, hu⟩ := exists_isForwardSol_of_disjoint_ball_gen hW hy0 ht (by linarith) hdy
    have hlim := tendsto_fwdMap_of_isForwardSol hW ht hu
    have hlim' : Tendsto (fun w => fwdMap W t w + W t) (𝓝[H] (y : ℂ)) (𝓝 (u t + W t)) :=
      hlim.add tendsto_const_nhds
    have hGc : Tendsto G (𝓝[H] (y : ℂ)) (𝓝 (G y)) :=
      ((hGd.continuousOn.continuousAt (isOpen_ball.mem_nhds hz)).tendsto).mono_left
        nhdsWithin_le_nhds
    have hev : ∀ᶠ w in 𝓝[H] (y : ℂ), G w = fwdMap W t w + W t := by
      filter_upwards [inter_mem_nhdsWithin H (isOpen_ball.mem_nhds hz)] with w hw
      exact hGg ⟨hw.2, hw.1⟩
    have hne : (𝓝[H] (y : ℂ)).NeBot := FiniteEndpoint.neBot_nhdsWithin_H (by simp)
    have heq : G y = u t + W t := tendsto_nhds_unique (hGc.congr' hev) hlim'
    rw [heq] at hzW
    exact hv y u hy0 hu hzW
  · have := hup z hz hpos
    rw [hzW] at this; simp at this

/-- **(D9), uniform clearance of a far set from every omitted real point** (A6's `exists_le_norm_fwdMap_uniform` with
the driver value replaced by any real `v` that no alive real point is mapped to). -/
theorem exists_le_norm_fwdMap_sub_uniform {H₁ S₂ : Set ℂ} (hH₁ : IsHPHull H₁)
    (hS₂ : Bornology.IsBounded S₂) (hS₂H : S₂ ⊆ H) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ a ∈ S₂, ∀ z ∈ H₁, 2 * δ ≤ ‖a - z‖) :
    ∃ r > 0, ∀ W : ℝ → ℝ, Continuous W → ((W 0 : ℝ) : ℂ) ∈ closure H₁ → ∀ T : ℝ, fwdHull W T ⊆ H₁ →
      ∀ t ∈ Icc (0 : ℝ) T, ∀ a ∈ S₂, ∀ v : ℝ,
        (∀ (y : ℝ) (u : ℝ → ℂ), y ≠ W 0 → IsForwardSol W (y : ℂ) t u → u t + (W t : ℂ) ≠ (v : ℂ)) →
        r ≤ ‖fwdMap W t a + W t - v‖ := by
  obtain ⟨g₁, hg₁⟩ := hH₁.exists_isMapOut
  obtain ⟨R₀, hR₀⟩ := hS₂.exists_norm_le
  set η : ℝ := δ / 8 with hη
  set Q : Set ℂ := {z : ℂ | η ≤ z.im ∧ ‖z‖ ≤ R₀ + δ ∧ ∀ w ∈ H₁, δ / 2 ≤ ‖z - w‖} with hQ
  have hQc : IsCompact Q := by
    refine (isCompact_closedBall (0 : ℂ) (R₀ + δ)).of_isClosed_subset ?_ ?_
    · refine (isClosed_le continuous_const continuous_im).inter
        ((isClosed_le continuous_norm continuous_const).inter ?_)
      have : {z : ℂ | ∀ w ∈ H₁, δ / 2 ≤ ‖z - w‖} = ⋂ w ∈ H₁, {z : ℂ | δ / 2 ≤ ‖z - w‖} := by
        ext z; simp
      have hcl : IsClosed {z : ℂ | ∀ w ∈ H₁, δ / 2 ≤ ‖z - w‖} := by
        rw [this]
        exact isClosed_biInter fun w _ =>
          isClosed_le continuous_const (continuous_id.sub continuous_const).norm
      exact hcl
    · intro z hz; rw [mem_closedBall_zero_iff]; exact hz.2.1
  have hQH : Q ⊆ H \ H₁ := fun z hz => ⟨show 0 < z.im by linarith [hz.1], fun hz1 => by
    have := hz.2.2 z hz1; rw [sub_self, norm_zero] at this; linarith⟩
  obtain ⟨m₁, hm₁, hm₁le⟩ : ∃ m₁ > 0, ∀ q ∈ Q, m₁ ≤ (g₁ q).im := by
    rcases Q.eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, fun q hq => by rw [he] at hq; exact absurd hq (notMem_empty q)⟩
    · have hc : ContinuousOn (fun q => (g₁ q).im) Q :=
        continuous_im.comp_continuousOn (hg₁.1.1.continuousOn.mono hQH)
      obtain ⟨q₀, hq₀, hmin⟩ := hQc.exists_isMinOn hne hc
      exact ⟨(g₁ q₀).im, hg₁.1.2.mapsTo (hQH hq₀), fun q hq => hmin hq⟩
  set M := QuantumZipper.CA.Koebe.koebeGrowthConst with hMdef
  set C₂ := QuantumZipper.CA.Koebe.koebeDistExp with hC₂def
  have hM : 0 < M := QuantumZipper.CA.Koebe.koebeGrowthConst_pos
  have hC₂ : 0 < C₂ := QuantumZipper.CA.Koebe.koebeDistExp_pos
  set c : ℝ := (1 / 2 : ℝ) ^ C₂ with hc
  have hcpos : 0 < c := Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨min m₁ (m₁ * c / (32 * M)), lt_min hm₁ (by positivity), ?_⟩
  intro W hW hW0 T hKH t ht a ha v hvom
  have haH : a ∈ H := hS₂H ha
  have haH₁ : a ∉ H₁ := fun h => by
    have := hsep a ha a h; rw [sub_self, norm_zero] at this; linarith
  by_cases hhigh : η ≤ a.im
  · -- a high point
    have haQ : a ∈ Q := ⟨hhigh, by linarith [hR₀ a ha], fun w hw => by linarith [hsep a ha w hw]⟩
    have h1 := hm₁le a haQ
    have h2 := im_le_im_fwdMap hW ht hH₁ hKH hg₁ ⟨haH, haH₁⟩
    calc min m₁ (m₁ * c / (32 * M)) ≤ m₁ := min_le_left _ _
      _ ≤ (fwdMap W t a).im := h1.trans h2
      _ = (fwdMap W t a + W t - v).im := by simp
      _ ≤ |(fwdMap W t a + W t - v).im| := le_abs_self _
      _ ≤ ‖fwdMap W t a + W t - v‖ := abs_im_le_norm _
  · -- a low point
    rw [not_le] at hhigh
    have ha0 : 0 < a.im := haH
    set x : ℝ := a.re with hx
    have hax_eq : a - (x : ℂ) = (a.im : ℂ) * I := by
      apply Complex.ext <;> simp [hx]
    have hax : ‖a - x‖ = a.im := by
      rw [hax_eq, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos ha0]
    have hxH₁ : ∀ w ∈ H₁, δ < ‖(x : ℂ) - w‖ := by
      intro w hw
      have h1 := hsep a ha w hw
      have h2 : ‖a - w‖ ≤ ‖a - x‖ + ‖(x : ℂ) - w‖ := by
        calc ‖a - w‖ = ‖(a - x) + ((x : ℂ) - w)‖ := by ring_nf
          _ ≤ _ := norm_add_le _ _
      linarith
    have ht0 : 0 ≤ t := ht.1
    have hKt : fwdHull W t ⊆ H₁ := ((QuantumZipper.fwdHull_mono).1 ht.2).trans hKH
    have hd : Disjoint (ball (x : ℂ) δ) (fwdHull W t) := by
      rw [Set.disjoint_left]
      intro z hz hzK
      have := hxH₁ z (hKt hzK)
      rw [mem_ball, dist_eq_norm, ← norm_neg, neg_sub] at hz
      linarith
    obtain ⟨G, hGd, hGg, -, -, -, hGinj, hup, hlow, hreal⟩ :=
      ConformalImageFull.IsMapOut.exists_reflection_full (isHPHull_fwdHull hW ht0)
        (isMapOut_fwdMap_gen hW ht0) hδ hd
    have hδ2 : 0 < δ / 2 := by linarith
    have h0' : ∀ y : ℝ, (y : ℂ) ∈ ball (x : ℂ) (δ / 2) → y ≠ W 0 := by
      intro y hy hy0
      obtain ⟨w, hw, hdw⟩ := Metric.mem_closure_iff.1 hW0 (δ / 2) hδ2
      have h1 := hxH₁ w hw
      rw [← hy0] at hdw
      rw [mem_ball, dist_eq_norm] at hy
      rw [dist_eq_norm] at hdw
      have := norm_sub_le_norm_sub_add_norm_sub (x : ℂ) (y : ℂ) w
      rw [norm_sub_rev (x : ℂ) (y : ℂ)] at this
      linarith
    have hWnot := real_not_mem_image_of_refl hW ht0 hδ hd h0' hvom hGd hGg hup hlow
    have haB : a ∈ ball (x : ℂ) (δ / 2) := by rw [mem_ball, dist_eq_norm, hax]; linarith
    set a' : ℂ := (x : ℂ) + (η : ℂ) * I with ha'
    have ha'x : ‖a' - x‖ = η := by
      rw [ha', add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by positivity)]
    have haa' : dist a a' = η - a.im := by
      have : a - a' = ((a.im - η : ℝ) : ℂ) * I := by
        apply Complex.ext <;> simp [ha', hx]
      rw [dist_eq_norm, this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_neg (by linarith), neg_sub]
    have hsub : ball a' (δ / 4) ⊆ ball (x : ℂ) (δ / 2) :=
      ball_subset_ball' (by rw [dist_eq_norm, ha'x]; linarith)
    have ha'B : a' ∈ ball (x : ℂ) (δ / 2) := hsub (mem_ball_self (by linarith))
    have ha'H : a' ∈ H := show 0 < a'.im by simp [ha']; linarith
    -- the height of `G a'`
    have ha'Q : a' ∈ Q := by
      refine ⟨by simp [ha'], ?_, fun w hw => ?_⟩
      · have h1 : ‖a'‖ ≤ ‖a‖ + ‖a' - a‖ := by
          calc ‖a'‖ = ‖a + (a' - a)‖ := by ring_nf
            _ ≤ _ := norm_add_le _ _
        have h2 : ‖a' - a‖ = η - a.im := by rw [← dist_eq_norm, dist_comm, haa']
        linarith [hR₀ a ha]
      · have h1 : ‖(x : ℂ) - w‖ ≤ ‖(x : ℂ) - a'‖ + ‖a' - w‖ := by
          calc ‖(x : ℂ) - w‖ = ‖((x : ℂ) - a') + (a' - w)‖ := by ring_nf
            _ ≤ _ := norm_add_le _ _
        rw [norm_sub_rev (x : ℂ) a', ha'x] at h1
        linarith [hxH₁ w hw]
    have hGa' : G a' = fwdMap W t a' + W t := hGg ⟨ha'B, ha'H⟩
    have him : m₁ ≤ (G a').im := by
      rw [hGa']
      simpa using (hm₁le a' ha'Q).trans (im_le_im_fwdMap hW ht hH₁ hKH hg₁ (hQH ha'Q))
    have hGx : (G x).im = 0 := hreal x (mem_ball_self hδ2) (by simp)
    -- growth at `a'`
    have hgrowth := QuantumZipper.CA.Koebe.norm_sub_le_growth (hGd.mono hsub) (hGinj.mono hsub)
      (by linarith : (0 : ℝ) < δ / 4) (w := (x : ℂ))
      (by rw [dist_eq_norm, ← norm_neg, neg_sub, ha'x]; linarith)
    have h1 : m₁ ≤ M * (δ / 4) * ‖deriv G a'‖ := by
      refine le_trans ?_ hgrowth
      calc m₁ ≤ (G a').im := him
        _ = -((G x - G a').im) := by simp [hGx]
        _ ≤ |(G x - G a').im| := neg_le_abs _
        _ ≤ ‖G x - G a'‖ := abs_im_le_norm _
    -- distortion from `a'` to `a`
    have haB' : a ∈ ball a' (δ / 4) := by rw [mem_ball, haa']; linarith
    have hdist := QuantumZipper.CA.Koebe.distortion_le_norm_deriv (hGd.mono hsub) (hGinj.mono hsub) haB'
    have hratio : (1 / 2 : ℝ) ≤ 1 - dist a a' / (δ / 4) := by
      rw [haa']
      have : (η - a.im) / (δ / 4) ≤ 1 / 2 := by
        rw [div_le_iff₀ (by linarith)]; linarith
      linarith
    have h2 : c * ‖deriv G a'‖ ≤ ‖deriv G a‖ := by
      refine le_trans ?_ hdist
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by norm_num) hratio hC₂.le) (norm_nonneg _)
    -- Koebe at `a`
    have hkoebe := QuantumZipper.CA.Koebe.koebeCovConst_mul_le_infDist_of_mem hGd hGinj haB
    have hinf : infDist (G a) (G '' ball (x : ℂ) (δ / 2))ᶜ ≤ dist (G a) (v : ℂ) :=
      infDist_le_dist_of_mem hWnot
    have hGa : G a = fwdMap W t a + W t := hGg ⟨haB, haH⟩
    have hdGa : dist (G a) (v : ℂ) = ‖fwdMap W t a + W t - v‖ := by rw [hGa, dist_eq_norm]
    have hax' : dist a x = a.im := by rw [dist_eq_norm, hax]
    have h3 : δ / 128 * ‖deriv G a‖ ≤ ‖fwdMap W t a + W t - v‖ := by
      have hk : QuantumZipper.CA.Koebe.koebeCovConst = 1 / 48 := rfl
      rw [hk, hax'] at hkoebe
      have hle : δ / 128 * ‖deriv G a‖ ≤ 1 / 48 * (δ / 2 - a.im) * ‖deriv G a‖ := by
        rw [show 1 / 48 * (δ / 2 - a.im) * ‖deriv G a‖ = (δ / 2 - a.im) / 48 * ‖deriv G a‖ by ring]
        exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
      linarith [hle.trans hkoebe, hdGa ▸ hinf]
    -- combine
    have hD' : 4 * m₁ / (M * δ) ≤ ‖deriv G a'‖ := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    calc min m₁ (m₁ * c / (32 * M)) ≤ m₁ * c / (32 * M) := min_le_right _ _
      _ = δ / 128 * (c * (4 * m₁ / (M * δ))) := by field_simp; ring
      _ ≤ δ / 128 * (c * ‖deriv G a'‖) := by gcongr
      _ ≤ δ / 128 * ‖deriv G a‖ := by gcongr
      _ ≤ ‖fwdMap W t a + W t - v‖ := h3

end InteractingSLE.ZhanGT4
