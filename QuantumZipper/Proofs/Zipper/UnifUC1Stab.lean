import QuantumZipper.Proofs.Zipper.UnifRC3MixStab

/-!
# UNIF-RC3-RSTAB (decision D33): stability of the second unzip map in both time parameters

`R_{u,s} = revMap (vrev W (u+s)) s` (`RUS`). `UnifRC3MixStab.norm_RUS_s_le` treats the horizon
direction `s`. This file adds the **`u`-direction** and the two-parameter bound:

* `norm_RUS_u_le`: for `u ≤ u'`, `u' + s ≤ T`, `g = u' − u`, and oscillation of `W` at scale `g`
  at most `ε`, `‖R_{u',s} z − R_{u,s} z‖ ≤ (ε + 2g/τ)(1 + √(R² + 8T)/τ)` (`Im z ≥ τ`, `‖z‖ ≤ R`).
  Flow decomposition: the cocycle gives `R_{u,g} ∘ R_{u',s} = R_{u,s+g}`, so with
  `w = R_{u',s} z`, `‖w − R_{u,s} z‖ ≤ ‖w − R_{u,g} w‖ + ‖R_{u,s+g} z − R_{u,s} z‖`: the first term is a
  displacement of a `g`-step of the reverse flow (`norm_revMap_vrev_sub_self_le`), the second is the
  horizon direction.
* `norm_RUS_sub_le`: for `p, p' ∈ tri T` with coordinates within `δ` and oscillation of `W` at
  scale `δ` at most `ε`: `‖R_p z − R_{p'} z‖ ≤ 4(ε + 2δ/τ)(1 + √(R² + 8T)/τ)` (through the corner
  `(min u u', min s s') ∈ tri T`).
* `norm_RUS_sub_le_holder`: for an `a`-Hölder driver (`HolderDrv`), `τ ≤ 1`, `dist p p' ≤ 1/2`:
  `‖R_p z − R_{p'} z‖ ≤ 4(CH + 2)(1 + √(R² + 8T))·dist(p, p')^a / τ²` — polynomial in `1/τ`, no
  Gronwall factor `exp(2T/τ²)`.

Sources: the flow decomposition of D33 (`handoff/REG-UNIF.md`); the Loewner estimates used are
`RegCont.norm_revMap_sub_self_le` and `TwoPoint.norm_revMap_sub_mul_le_upper`. Own elementary
argument (no published source treats the two-parameter stability of the double unzip map).
-/

noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology Real

namespace QuantumZipper
namespace RegUnif

open RegCont TwoPoint B2

variable {W : ℝ → ℝ}

/-- **RSTAB, `u`-direction.** -/
theorem norm_RUS_u_le (hW : Continuous W) {T τ R u u' s ε : ℝ} (hT : 0 ≤ T) (hτ : 0 < τ)
    (hu : 0 ≤ u) (hs : 0 ≤ s) (huu : u ≤ u') (hus : u' + s ≤ T)
    (hosc : ∀ t ∈ Icc (0 : ℝ) T, ∀ t' ∈ Icc (0 : ℝ) T, |t - t'| ≤ u' - u → |W t - W t'| ≤ ε)
    {z : ℂ} (hz : z ∈ H) (hzim : τ ≤ z.im) (hzR : ‖z‖ ≤ R) :
    ‖RUS W (u', s) z - RUS W (u, s) z‖ ≤
      (ε + 2 * (u' - u) / τ) * (1 + Real.sqrt (R ^ 2 + 8 * T) / τ) := by
  set g := u' - u with hg
  have hg0 : 0 ≤ g := sub_nonneg.2 huu
  have hu' : 0 ≤ u' := hu.trans huu
  set w := RUS W (u', s) z with hw
  have hwH : w ∈ H := im_revMap_pos (continuous_vrev hW _) hz hs
  have hwτ : τ ≤ w.im := hzim.trans (im_le_im_revMap _ (continuous_vrev hW _) z hz hs)
  -- cocycle: `R_{u,g} w = R_{u,s+g} z`
  have hc : revMap (vrev W (u + g)) g w = RUS W (u, s + g) z := by
    have h := revMap_vrev_split (W := W) hW hu' hg0 hs (by linarith : g ≤ u') hz
    rw [show u + g = u' by ring]
    simp only [RUS_apply]
    rw [show u + (s + g) = u' + s by ring, show s + g = g + s by ring, h]
    rfl
  -- the displacement of the `g`-step
  have hd : ‖revMap (vrev W (u + g)) g w - w‖ ≤ ε + 2 * g / τ := by
    refine (norm_revMap_vrev_sub_self_le hW hu hg0 (fun t ht t' ht' => ?_) hwH).trans
      (add_le_add le_rfl (div_le_div_of_nonneg_left (by linarith) hτ hwτ))
    exact hosc t ⟨by linarith [ht.1], by linarith [ht.2]⟩ t' ⟨by linarith [ht'.1], by linarith [ht'.2]⟩
      (by rw [abs_sub_le_iff]; constructor <;> linarith [ht.1, ht.2, ht'.1, ht'.2])
  -- the horizon direction
  have hh := norm_RUS_s_le (W := W) hW hT hτ hu hs (by linarith : s ≤ s + g) (by linarith)
    (fun t ht t' ht' h => hosc t ht t' ht' (by linarith)) hz hzim hzR
  rw [show s + g - s = g by ring] at hh
  rw [hc] at hd
  calc ‖w - RUS W (u, s) z‖ ≤ ‖RUS W (u, s + g) z - w‖ + ‖RUS W (u, s + g) z - RUS W (u, s) z‖ := by
        rw [norm_sub_rev (RUS W (u, s + g) z) w]; exact norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ (ε + 2 * g / τ) + (ε + 2 * g / τ) * Real.sqrt (R ^ 2 + 8 * T) / τ := add_le_add hd hh
    _ = (ε + 2 * g / τ) * (1 + Real.sqrt (R ^ 2 + 8 * T) / τ) := by ring

/-- One step in each direction, to the corner `(min u u', min s s')`. -/
theorem norm_RUS_sub_corner_le (hW : Continuous W) {T τ R ε δ : ℝ} (hT : 0 ≤ T) (hτ : 0 < τ)
    {u s u₀ s₀ : ℝ} (hu₀ : 0 ≤ u₀) (hs₀ : 0 ≤ s₀) (hu : u₀ ≤ u) (hs : s₀ ≤ s) (hus : u + s ≤ T)
    (hdu : u - u₀ ≤ δ) (hds : s - s₀ ≤ δ)
    (hosc : ∀ t ∈ Icc (0 : ℝ) T, ∀ t' ∈ Icc (0 : ℝ) T, |t - t'| ≤ δ → |W t - W t'| ≤ ε)
    {z : ℂ} (hz : z ∈ H) (hzim : τ ≤ z.im) (hzR : ‖z‖ ≤ R) :
    ‖RUS W (u, s) z - RUS W (u₀, s₀) z‖ ≤
      2 * ((ε + 2 * δ / τ) * (1 + Real.sqrt (R ^ 2 + 8 * T) / τ)) := by
  have hε0 : 0 ≤ ε := by
    have h0 := hosc 0 ⟨le_rfl, hT⟩ 0 ⟨le_rfl, hT⟩ (by simp; linarith)
    simpa using h0
  have hS : 0 ≤ Real.sqrt (R ^ 2 + 8 * T) / τ := by positivity
  have h1 := norm_RUS_u_le (W := W) hW hT hτ hu₀ (hs₀.trans hs) hu hus
    (fun t ht t' ht' h => hosc t ht t' ht' (h.trans hdu)) hz hzim hzR
  have h2 := norm_RUS_s_le (W := W) hW hT hτ hu₀ hs₀ hs (by linarith)
    (fun t ht t' ht' h => hosc t ht t' ht' (h.trans hds)) hz hzim hzR
  have m1 : (ε + 2 * (u - u₀) / τ) * (1 + Real.sqrt (R ^ 2 + 8 * T) / τ) ≤
      (ε + 2 * δ / τ) * (1 + Real.sqrt (R ^ 2 + 8 * T) / τ) := by
    gcongr
  have m2 : (ε + 2 * (s - s₀) / τ) * Real.sqrt (R ^ 2 + 8 * T) / τ ≤
      (ε + 2 * δ / τ) * (1 + Real.sqrt (R ^ 2 + 8 * T) / τ) := by
    have hδ0 : 0 ≤ ε + 2 * δ / τ := by
      have : 0 ≤ δ := (sub_nonneg.2 hs).trans hds
      positivity
    calc (ε + 2 * (s - s₀) / τ) * Real.sqrt (R ^ 2 + 8 * T) / τ
        = (ε + 2 * (s - s₀) / τ) * (Real.sqrt (R ^ 2 + 8 * T) / τ) := by ring
      _ ≤ (ε + 2 * δ / τ) * (Real.sqrt (R ^ 2 + 8 * T) / τ) := by gcongr
      _ ≤ (ε + 2 * δ / τ) * (1 + Real.sqrt (R ^ 2 + 8 * T) / τ) := by nlinarith
  calc ‖RUS W (u, s) z - RUS W (u₀, s₀) z‖
      ≤ ‖RUS W (u, s) z - RUS W (u₀, s) z‖ + ‖RUS W (u₀, s) z - RUS W (u₀, s₀) z‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := by linarith

/-- **RSTAB (both directions), oscillation form.** -/
theorem norm_RUS_sub_le (hW : Continuous W) {T τ R ε δ : ℝ} (hT : 0 ≤ T) (hτ : 0 < τ)
    {p p' : ℝ × ℝ} (hp : p ∈ tri T) (hp' : p' ∈ tri T) (hd1 : |p.1 - p'.1| ≤ δ)
    (hd2 : |p.2 - p'.2| ≤ δ)
    (hosc : ∀ t ∈ Icc (0 : ℝ) T, ∀ t' ∈ Icc (0 : ℝ) T, |t - t'| ≤ δ → |W t - W t'| ≤ ε)
    {z : ℂ} (hz : z ∈ H) (hzim : τ ≤ z.im) (hzR : ‖z‖ ≤ R) :
    ‖RUS W p z - RUS W p' z‖ ≤ 4 * ((ε + 2 * δ / τ) * (1 + Real.sqrt (R ^ 2 + 8 * T) / τ)) := by
  obtain ⟨u, s⟩ := p
  obtain ⟨u', s'⟩ := p'
  obtain ⟨hu, hs, hus⟩ := hp
  obtain ⟨hu', hs', hus'⟩ := hp'
  simp only at hd1 hd2 hu hs hus hu' hs' hus'
  have a1 := abs_le.1 hd1
  have a2 := abs_le.1 hd2
  have c1 := norm_RUS_sub_corner_le (W := W) hW hT hτ (le_min hu hu') (le_min hs hs')
    (min_le_left u u') (min_le_left s s') hus
    (by have := min_le_right u u'; rcases min_choice u u' with h | h <;> rw [h] <;> linarith)
    (by rcases min_choice s s' with h | h <;> rw [h] <;> linarith) hosc hz hzim hzR
  have c2 := norm_RUS_sub_corner_le (W := W) hW hT hτ (le_min hu hu') (le_min hs hs')
    (min_le_right u u') (min_le_right s s') hus'
    (by rcases min_choice u u' with h | h <;> rw [h] <;> linarith)
    (by rcases min_choice s s' with h | h <;> rw [h] <;> linarith) hosc hz hzim hzR
  calc ‖RUS W (u, s) z - RUS W (u', s') z‖
      ≤ ‖RUS W (u, s) z - RUS W (min u u', min s s') z‖ +
          ‖RUS W (u', s') z - RUS W (min u u', min s s') z‖ := by
        rw [norm_sub_rev (RUS W (u', s') z)]; exact norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ _ := by linarith

/-- **RSTAB for Hölder drivers**: polynomial in `1/τ`. -/
theorem norm_RUS_sub_le_holder {T a CH : ℝ} (hWH : HolderDrv W T a CH) (hT : 0 ≤ T)
    {τ R : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) {p p' : ℝ × ℝ} (hp : p ∈ tri T) (hp' : p' ∈ tri T)
    (hpp : dist p p' ≤ 1 / 2) {z : ℂ} (hz : z ∈ H) (hzim : τ ≤ z.im) (hzR : ‖z‖ ≤ R) :
    ‖RUS W p z - RUS W p' z‖ ≤
      4 * (CH + 2) * (1 + Real.sqrt (R ^ 2 + 8 * T)) * dist p p' ^ a / τ ^ 2 := by
  obtain ⟨hW, -, ha, ha1, hCH, hH⟩ := hWH
  set δ := dist p p' with hδ
  have hδ0 : 0 ≤ δ := dist_nonneg
  have hδ1 : δ ≤ 1 := by linarith
  have hd1 : |p.1 - p'.1| ≤ δ := by
    rw [← Real.dist_eq, hδ, Prod.dist_eq]; exact le_max_left _ _
  have hd2 : |p.2 - p'.2| ≤ δ := by
    rw [← Real.dist_eq, hδ, Prod.dist_eq]; exact le_max_right _ _
  have h := norm_RUS_sub_le (W := W) (ε := CH * δ ^ a) hW hT hτ hp hp' hd1 hd2
    (fun t ht t' ht' htt => (hH t ht t' ht' (htt.trans (by linarith))).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg _) htt ha.le) hCH)) hz hzim hzR
  refine h.trans ?_
  set S := Real.sqrt (R ^ 2 + 8 * T) with hS
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hδa : δ ≤ δ ^ a := by
    have := Real.rpow_le_rpow_of_exponent_ge' hδ0 hδ1 ha.le ha1
    rwa [Real.rpow_one] at this
  have hpa : 0 ≤ δ ^ a := Real.rpow_nonneg hδ0 _
  have e1 : CH * δ ^ a + 2 * δ / τ ≤ (CH + 2) * δ ^ a / τ := by
    rw [le_div_iff₀ hτ]
    have : CH * δ ^ a * τ ≤ CH * δ ^ a := mul_le_of_le_one_right (by positivity) hτ1
    have ex : (CH * δ ^ a + 2 * δ / τ) * τ = CH * δ ^ a * τ + 2 * δ := by field_simp
    rw [ex]
    nlinarith
  have e2 : 1 + S / τ ≤ (1 + S) / τ := by
    rw [le_div_iff₀ hτ, add_mul, div_mul_cancel₀ _ hτ.ne']
    nlinarith
  have e3 : 0 ≤ CH * δ ^ a + 2 * δ / τ := by positivity
  calc 4 * ((CH * δ ^ a + 2 * δ / τ) * (1 + S / τ))
      ≤ 4 * (((CH + 2) * δ ^ a / τ) * ((1 + S) / τ)) := by gcongr
    _ = 4 * (CH + 2) * (1 + S) * δ ^ a / τ ^ 2 := by field_simp

end RegUnif
end QuantumZipper
