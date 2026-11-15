import InteractingSLE.Spec.Sec5.Aux61RestartFinTarget

/-!
# Current access after changing to the original right target

Packet PROVE-AUX61-R1. The inverse own chart need not have hydrodynamic target
infinity. Comparing it with a mapping-out function gives a half-plane
automorphism. Its access at zero is finite because the physical tip is finite
and a mapping-out function differs boundedly from the identity. A Möbius
change then puts its free collar into the landed nested-hull access theorem.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open QuantumZipper (H)
open SupercriticalConformalCovariance (IsConformalBijection)

namespace InteractingSLE.Sec5.Aux61Restart

/-- A finite physical tip has a finite real access in its hydrodynamic own
chart, even when the given inverse chart has a different target. -/
theorem exists_realMobius_finite_access {A : Set ℂ} (hA : IsHPHull A)
    {g F : ℂ → ℂ} (hg : IsMapOut A g)
    (hF : IsConformalBijection F H (H \ A)) {z₀ : ℂ}
    (hF₀ : Tendsto F (𝓝[H] 0) (𝓝 z₀)) :
    ∃ a b c d x : ℝ, 0 < a * d - b * c ∧
      EqOn (g ∘ F) (QuantumZipper.CA.realMobius a b c d) H ∧
      mobiusBdry a b c d (0 : ℝ) = (x : OnePoint ℝ) ∧
      Tendsto (g ∘ F) (𝓝[H] 0) (𝓝[H] (x : ℂ)) := by
  have hm := isConformalBijection_comp hg.1 hF
  obtain ⟨a, b, c, d, hd, heq⟩ := QuantumZipper.CA.exists_realMobius_of_bijOn_H hm.1 hm.2
  have hH₀ : ∀ᶠ w : ℂ in 𝓝[H] 0, w ∈ H := self_mem_nhdsWithin
  have hp := (PrimeEnd.tendsto_realMobius_approachH hd (0 : ℝ)).congr'
    (hH₀.mono fun w hw => (heq hw).symm)
  obtain ⟨C, hC⟩ := hg.exists_norm_le hA
  have hb : ∀ᶠ w in 𝓝[H] 0, ‖g (F w)‖ ≤ ‖z₀‖ + 1 + C := by
    filter_upwards [self_mem_nhdsWithin,
      hF₀.norm.eventually (Iio_mem_nhds (by linarith : ‖z₀‖ < ‖z₀‖ + 1))] with w hw hwF
    exact (hC _ (hF.2.mapsTo hw)).trans (by linarith)
  cases hbdry : mobiusBdry a b c d (0 : ℝ) with
  | infty =>
    rw [hbdry, PrimeEnd.approachH_infty] at hp
    have hnorm := tendsto_norm_cobounded_atTop.comp (hp.mono_right inf_le_left)
    have : (𝓝[H] (0 : ℂ)).NeBot := PrimeEnd.approachH_neBot (0 : ℝ)
    obtain ⟨w, hw₁, hw₂⟩ := (hb.and (hnorm.eventually_gt_atTop (‖z₀‖ + 1 + C))).exists
    exact False.elim (not_lt_of_ge hw₁ hw₂)
  | coe x =>
    rw [hbdry, PrimeEnd.approachH_coe] at hp
    exact ⟨a, b, c, d, x, hd, heq, hbdry, hp⟩

/-- The actual additional filled hull misses a real ball around the current
own access. This is the collar needed by Aux. 57, rather than an assumed
canonical phase value. -/
theorem exists_current_transition_collar {A B : Set ℂ}
    (hA : IsHPHull A) (hB : IsHPHull B) {g F : ℂ → ℂ}
    (hg : IsMapOut A g) (hF : IsConformalBijection F H (H \ A)) {z₀ : ℂ}
    (hF₀ : Tendsto F (𝓝[H] 0) (𝓝 z₀))
    (hcollar : ∃ δ > 0, MapsTo F (ball 0 δ ∩ H) (H \ B)) :
    ∃ u ρ : ℝ, 0 < ρ ∧ Disjoint (ball (u : ℂ) ρ) (g '' (B \ A)) ∧
      Tendsto (g ∘ F) (𝓝[H] 0) (𝓝[H] (u : ℂ)) := by
  obtain ⟨a, b, c, d, u, hd, heq, hbdry, hlim⟩ :=
    exists_realMobius_finite_access hA hg hF hF₀
  let mi := QuantumZipper.CA.realMobius d (-b) (-c) a
  have hdi : 0 < d * a - (-b) * (-c) := by nlinarith only [hd]
  have hmiH : MapsTo mi H H := (isConformalBijection_realMobius_of_pos_det hdi).2.mapsTo
  have hmi : Tendsto mi (𝓝[H] (u : ℂ)) (𝓝[H] 0) := by
    have h := PrimeEnd.tendsto_realMobius_approachH hdi (u : OnePoint ℝ)
    rw [← hbdry, mobiusBdry_inv_apply hd.ne', hbdry] at h
    simpa only [PrimeEnd.approachH_coe, ofReal_zero] using h
  obtain ⟨ρ, hρ, hsafe⟩ := Metric.mem_nhdsWithin_iff.1
    (hmi.eventually (eventually_mem_of_collar hcollar))
  refine ⟨u, ρ, hρ, ?_, hlim⟩
  rw [Set.disjoint_left]
  rintro w hw ⟨y, hy, hgy⟩
  have hwH : w ∈ H := hgy ▸ hg.1.2.mapsTo ⟨hB.1 hy.1, hy.2⟩
  have hFm := hsafe ⟨hw, hwH⟩
  have hm : g (F (mi w)) = w := by
    change (g ∘ F) (mi w) = w
    rw [heq (hmiH hwH)]
    simpa only [mi, neg_neg] using QuantumZipper.CA.realMobius_inv_apply hdi hwH
  have hFy : F (mi w) = y := hg.1.2.injOn (hF.2.mapsTo (hmiH hwH))
    ⟨hB.1 hy.1, hy.2⟩ (hm.trans hgy.symm)
  exact hFm.2 (hFy ▸ hy.1)

/-- The free current collar yields its prime-end approach in the retained
hydrodynamic chart. This removes the prime-end comparison premise for this
nested-hull configuration; the inverse own chart may have any original target. -/
theorem exists_chart_access_of_finite_inverse {A B : Set ℂ}
    (hA : IsHPHull A) (hB : IsHPHull B) (hAB : A ⊆ B) {g F : ℂ → ℂ}
    (hg : IsMapOut A g) (hF : IsConformalBijection F H (H \ A)) {z₀ : ℂ}
    (hF₀ : Tendsto F (𝓝[H] 0) (𝓝 z₀))
    (hcollar : ∃ δ > 0, MapsTo F (ball 0 δ ∩ H) (H \ B)) :
    ∃ (ψ : HChart (H \ B)) (x : ℝ), IsMapOut B ψ.1 ∧
      Tendsto (ψ.1 ∘ F) (𝓝[H] 0) (PrimeEnd.approachH (x : OnePoint ℝ)) := by
  obtain ⟨a, b, c, d, u, hd, heq, hbdry, hlim⟩ :=
    exists_realMobius_finite_access hA hg hF hF₀
  let mi := QuantumZipper.CA.realMobius d (-b) (-c) a
  have hdi : 0 < d * a - (-b) * (-c) := by nlinarith only [hd]
  have hmiH : MapsTo mi H H := (isConformalBijection_realMobius_of_pos_det hdi).2.mapsTo
  have hmi : Tendsto mi (𝓝[H] (u : ℂ)) (𝓝[H] 0) := by
    have h := PrimeEnd.tendsto_realMobius_approachH hdi (u : OnePoint ℝ)
    rw [← hbdry, mobiusBdry_inv_apply hd.ne', hbdry] at h
    simpa only [PrimeEnd.approachH_coe, ofReal_zero] using h
  have hplus : Tendsto (fun w : ℂ => w + (u : ℂ)) (𝓝[H] 0) (𝓝[H] (u : ℂ)) := by
    apply tendsto_nhdsWithin_iff.2
    constructor
    · simpa only [id_eq, zero_add] using
        ((continuous_id.add_const (u : ℂ)).tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with w hw
      change 0 < (w + (u : ℂ)).im
      simpa only [add_im, ofReal_im, add_zero] using (show 0 < w.im from hw)
  let F' : ℂ → ℂ := fun w => F (mi (w + (u : ℂ)))
  have hF'H : MapsTo F' H (H \ A) := fun w hw =>
    hF.2.mapsTo (hmiH (by
      change 0 < (w + (u : ℂ)).im
      simpa only [add_im, ofReal_im, add_zero] using (show 0 < w.im from hw)))
  have hF'inv : ∀ w ∈ H, g (F' w) = w + (u : ℂ) := by
    intro w hw
    have hw' : w + (u : ℂ) ∈ H := by
      change 0 < (w + (u : ℂ)).im
      simpa only [add_im, ofReal_im, add_zero] using (show 0 < w.im from hw)
    change (g ∘ F) (mi (w + (u : ℂ))) = _
    rw [heq (hmiH hw')]
    simpa only [mi, neg_neg] using QuantumZipper.CA.realMobius_inv_apply hdi hw'
  have hF'collar : ∃ δ > 0, MapsTo F' (ball 0 δ ∩ H) (H \ B) := by
    have hev := (hmi.comp hplus).eventually (eventually_mem_of_collar hcollar)
    obtain ⟨δ, hδ, hfree⟩ := Metric.mem_nhdsWithin_iff.1 hev
    exact ⟨δ, hδ, hfree⟩
  obtain ⟨ψ, x, hψ, hx⟩ := exists_chart_access_of_nested_hulls hA hB hAB hg
    hF'H hF'inv hF'collar
  have hminus : Tendsto (fun w => g (F w) - (u : ℂ)) (𝓝[H] 0) (𝓝[H] 0) := by
    apply tendsto_nhdsWithin_iff.2
    constructor
    · change Tendsto (fun w => (g ∘ F) w - (u : ℂ)) (𝓝[H] 0) (𝓝 0)
      simpa only [sub_self] using (hlim.mono_right nhdsWithin_le_nhds).sub_const (u : ℂ)
    · filter_upwards [self_mem_nhdsWithin] with w hw
      change 0 < (g (F w) - (u : ℂ)).im
      simpa only [sub_im, ofReal_im, sub_zero] using
        (show 0 < (g (F w)).im from hg.1.2.mapsTo (hF.2.mapsTo hw))
  refine ⟨ψ, x, hψ, (hx.comp hminus).congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin] with w hw
  change ψ.1 (F (mi (g (F w) - (u : ℂ) + (u : ℂ)))) = ψ.1 (F w)
  apply congrArg ψ.1
  apply congrArg F
  change mi ((g ∘ F) w - (u : ℂ) + (u : ℂ)) = w
  rw [sub_add_cancel, heq hw]
  exact QuantumZipper.CA.realMobius_inv_apply hd hw

end InteractingSLE.Sec5.Aux61Restart
