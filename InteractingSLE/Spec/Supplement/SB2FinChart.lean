/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2FinConfig
import InteractingSLE.Spec.Supplement.Q3RelBHChart

/-!
# SB2(1)'s retained chart: the left entry chart as a retained chart landing everywhere

Packet PROVE-T14-SB2FIN. The field `chart : Supp8.Q3Rel.IsRetainedChartOff A Ψ Ψi LΨ Sb` of `SB.Union.IsRelConfigJ`
(PROVE-T14-SB2UNION) for SB2(1)'s retained set: the filled lower prefix `fill A` with its left entry chart `c` at
`L` (`IsLeftEntryChart`, the chart of SB2(1)'s conclusion), whose inverse has the continuous boundary extension `g`
of Lemma S2. Here:

* the inverse lands at every real point (`Sb = ∅`): `g` is continuous on `closure ℍ` and equals the inverse on `ℍ`;
* **`exists_tendsto_fwd_of_notMem_closure`** (`fwd_lands`): the chart has a real boundary value at every real point
  off `closure (fill A)` — the landed cluster-set lemma `exists_tendsto_of_tendsto_comp` (Yuan's fibre lemma) applied
  to `g` and the chart composed with a radial retraction into a half-disc of `D_A`;
* **`exists_isRetainedChartOff`**: the chart is `IsRetainedChartOff (fill A) c.fwd c.inv L ∅` (with `c.lift = Im L` on
  `D_A`), given the chart lift's boundary value `0` at every real point `y ≠ 0` off `closure (fill A)` — the field
  `lift_real`; `IsLeftEntryChart` supplies it to the left of `L` (`lift_real_of_lt`), the remaining free real points
  (right of the retained set) are the named premise `hlift`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open scoped NNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.FinRel

/-! ### A radial retraction of `ℍ` into a half-disc -/

/-- The radial retraction of `ℂ` onto the closed disc of radius `r` about `y`. -/
def radRetract (y : ℂ) (r : ℝ) (z : ℂ) : ℂ := y + (z - y) * ((min 1 (r / ‖z - y‖) : ℝ) : ℂ)

theorem radRetract_of_le {y z : ℂ} {r : ℝ} (hz : ‖z - y‖ ≤ r) (hzy : z ≠ y) : radRetract y r z = z := by
  have hpos : 0 < ‖z - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hzy)
  have h1 : 1 ≤ r / ‖z - y‖ := by rw [le_div_iff₀ hpos]; linarith
  simp only [radRetract, min_eq_left h1, ofReal_one, mul_one, add_sub_cancel]

theorem norm_radRetract_sub_le {y : ℂ} {r : ℝ} (hr : 0 ≤ r) (z : ℂ) : ‖radRetract y r z - y‖ ≤ r := by
  simp only [radRetract, add_sub_cancel_left, norm_mul, norm_real, Real.norm_eq_abs]
  have hm0 : 0 ≤ min 1 (r / ‖z - y‖) := le_min zero_le_one (div_nonneg hr (norm_nonneg _))
  rw [abs_of_nonneg hm0]
  rcases (norm_nonneg (z - y)).lt_or_eq with hpos | h0
  · calc ‖z - y‖ * min 1 (r / ‖z - y‖) ≤ ‖z - y‖ * (r / ‖z - y‖) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) (norm_nonneg _)
      _ = r := by field_simp
  · rw [← h0, zero_mul]
    exact hr

theorem radRetract_mem_H {y : ℂ} (hy : y.im = 0) {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : z ∈ H) :
    radRetract y r z ∈ H := by
  have hzy : z ≠ y := fun h => by
    have : (0 : ℝ) < z.im := hz
    rw [h, hy] at this
    exact lt_irrefl _ this
  have hpos : 0 < ‖z - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hzy)
  have hm : 0 < min 1 (r / ‖z - y‖) := lt_min one_pos (div_pos hr hpos)
  show 0 < (radRetract y r z).im
  simp only [radRetract, add_im, mul_im, sub_im, ofReal_im, mul_zero, ofReal_re, sub_re, hy, zero_add, sub_zero]
  exact mul_pos (show 0 < z.im from hz) hm

theorem continuousOn_radRetract {y : ℂ} (hy : y.im = 0) (r : ℝ) : ContinuousOn (radRetract y r) H := by
  have hne : ∀ z ∈ H, ‖z - y‖ ≠ 0 := fun z hz h => by
    have hzy : z = y := sub_eq_zero.1 (norm_eq_zero.1 h)
    have : (0 : ℝ) < z.im := hz
    rw [hzy, hy] at this
    exact lt_irrefl _ this
  unfold radRetract
  refine continuousOn_const.add ((continuousOn_id.sub continuousOn_const).mul ?_)
  refine Complex.continuous_ofReal.comp_continuousOn (ContinuousOn.inf continuousOn_const ?_)
  exact continuousOn_const.div (continuous_norm.comp_continuousOn (continuousOn_id.sub continuousOn_const)) hne

/-! ### The chart lands at the free real points -/

section Land

variable {A : Set ℂ} {L : ℝ} {c : Chart} {g : ℂ → ℂ}

/-- **The left entry chart has a real boundary value at every real point off `closure (fill A)`** (`fwd_lands`). -/
theorem exists_tendsto_fwd_of_notMem_closure (hAb : IsBounded A) (hAc : IsPreconnected (A ∪ {z : ℂ | z.im ≤ 0}))
    (hc : IsLeftEntryChart A L c) (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H) {y : ℝ}
    (hy : (y : ℂ) ∉ closure (fillH A)) : ∃ x : ℝ, Tendsto c.1 (𝓝[H \ fillH A] (y : ℂ)) (𝓝 (x : ℂ)) := by
  have hD := hc.1
  obtain ⟨C₁, C₂, hC₁, hbd⟩ := hc.exists_norm_fwd_le hAb hAc
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl _ hy
  have hyim : ((y : ℂ)).im = 0 := by simp
  -- the retraction into the half-disc of radius `ρ/2`
  set ψ := radRetract (y : ℂ) (ρ / 2) with hψdef
  have hψD : ∀ z ∈ H, ψ z ∈ H \ fillH A := fun z hz => by
    refine ⟨radRetract_mem_H hyim (by positivity) hz, fun hF => ?_⟩
    have hd : dist (ψ z) (y : ℂ) < ρ := by
      rw [dist_eq_norm]
      exact lt_of_le_of_lt (norm_radRetract_sub_le (by positivity) z) (by linarith)
    exact hball hd (subset_closure hF)
  set G := fun z => c.1 (ψ z) with hGdef
  have hGc : ContinuousOn G H :=
    hD.differentiableOn_fwd.continuousOn.comp (continuousOn_radRetract hyim _) hψD
  have hGH : MapsTo G H Hbar := fun z hz => le_of_lt (show 0 < (c.1 (ψ z)).im from hD.fwd_mem (hψD z hz))
  have hGR : ∀ᶠ w in 𝓝[H] (y : ℂ), ‖G w‖ ≤ C₁ * (‖(y : ℂ)‖ + ρ / 2) + C₂ :=
    eventually_nhdsWithin_of_forall fun w hw => by
      refine (hbd _ (hψD w hw)).trans ?_
      have h1 : ‖ψ w‖ ≤ ‖(y : ℂ)‖ + ρ / 2 := by
        have := norm_radRetract_sub_le (y := (y : ℂ)) (by positivity : (0 : ℝ) ≤ ρ / 2) w
        calc ‖ψ w‖ = ‖(ψ w - y) + y‖ := by rw [sub_add_cancel]
          _ ≤ ‖ψ w - y‖ + ‖(y : ℂ)‖ := norm_add_le _ _
          _ ≤ ‖(y : ℂ)‖ + ρ / 2 := by linarith
      nlinarith
  -- near `y` the retraction is the identity
  have hnear : ∀ᶠ w in 𝓝[H] (y : ℂ), ψ w = w := by
    have hmem : ball (y : ℂ) (ρ / 2) ∈ 𝓝[H] (y : ℂ) := mem_nhdsWithin_of_mem_nhds (ball_mem_nhds _ (by positivity))
    filter_upwards [hmem, self_mem_nhdsWithin] with w hw hwH
    refine radRetract_of_le (le_of_lt (by rwa [mem_ball, dist_eq_norm] at hw)) fun h => ?_
    have : (0 : ℝ) < w.im := hwH
    rw [h, hyim] at this
    exact lt_irrefl _ this
  have hFG : Tendsto (fun w => g (G w)) (𝓝[H] (y : ℂ)) (𝓝 (y : ℂ)) := by
    refine (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).congr' ?_
    filter_upwards [hnear, self_mem_nhdsWithin] with w hw hwH
    have hwD : w ∈ H \ fillH A := hw ▸ hψD w hwH
    simp only [hGdef, hw, id]
    rw [hgi (hD.fwd_mem hwD), hD.inv_fwd hwD]
  have hgd : DifferentiableOn ℂ g H := hD.1.1.congr fun w hw => hgi hw
  have hginj : InjOn g H := fun w₁ h₁ w₂ h₂ he => hD.1.injOn h₁ h₂ (by rwa [hgi h₁, hgi h₂] at he)
  have hgR : ∀ x : ℂ, x.im = 0 → g x ∉ g '' H := by
    rintro x hx ⟨w, hw, he⟩
    have hxr : x = (x.re : ℂ) := Complex.ext (by simp) (by simp [hx])
    have h1 := SB.g_ofReal_notMem hD hgc hgi x.re
    rw [← hxr, ← he, hgi hw] at h1
    exact h1 (hD.inv_mem hw)
  have hgcb : ContinuousOn g Hbar := hgc
  obtain ⟨ξ, hξ, hgξ, hGξ⟩ := exists_tendsto_of_tendsto_comp hgd hgcb hginj hgR
    (show (y : ℂ) ∈ Hbar from show (0 : ℝ) ≤ ((y : ℂ)).im by simp) hGc hGH hGR hFG
  have hξim : ξ.im = 0 := by
    refine le_antisymm (not_lt.1 fun hpos => ?_) hξ
    have h1 : g ξ ∈ H := by rw [hgi hpos]; exact (hD.inv_mem hpos).1
    rw [hgξ] at h1
    have h2 : (0 : ℝ) < ((y : ℂ)).im := h1
    rw [hyim] at h2
    exact lt_irrefl _ h2
  refine ⟨ξ.re, ?_⟩
  have hξr : ξ = (ξ.re : ℂ) := Complex.ext (by simp) (by simp [hξim])
  rw [← hξr]
  refine (hGξ.mono_left (nhdsWithin_mono _ sdiff_subset)).congr' ?_
  filter_upwards [hnear.filter_mono (nhdsWithin_mono _ sdiff_subset)] with w hw
  simp only [hGdef, hw]

/-- The inverse lands at every real point. -/
theorem exists_tendsto_inv (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H) (x : ℝ) :
    ∃ p, Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 p) := by
  refine ⟨g x, ?_⟩
  have h1 : Tendsto g (𝓝[H] (x : ℂ)) (𝓝 (g x)) :=
    (hgc (x : ℂ) (show (0 : ℝ) ≤ ((x : ℂ)).im by simp)).tendsto.mono_left
      (nhdsWithin_mono _ fun z (hz : 0 < z.im) => show 0 ≤ z.im from hz.le)
  exact h1.congr' (eventually_nhdsWithin_of_forall fun z hz => hgi hz)

/-- **`IsLeftEntryChart` supplies the lift's boundary value `0` to the left of `L`.** -/
theorem lift_real_of_lt (hc : IsLeftEntryChart A L c) {y : ℝ} (hyL : y < L) :
    Tendsto c.2.2 (𝓝[H \ fillH A] (y : ℂ)) (𝓝 0) :=
  (hc.2.2.2 y hyL).mono_left (nhdsWithin_mono _ sdiff_subset)

/-- **The left entry chart is a retained chart landing everywhere** (`IsRetainedChartOff (fill A) c.fwd c.inv L ∅`,
with `c.lift = Im L` on `D_A`), given the lift's boundary value `0` at the free real points `y ≠ 0` (`hlift`; to the
left of `L` this is `lift_real_of_lt`). -/
theorem exists_isRetainedChartOff (hAb : IsBounded A) (hAc : IsPreconnected (A ∪ {z : ℂ | z.im ≤ 0}))
    (hc : IsLeftEntryChart A L c) (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g c.2.1 H)
    (hlift : ∀ y : ℝ, y ≠ 0 → (y : ℂ) ∉ closure (fillH A) → Tendsto c.2.2 (𝓝[H \ fillH A] (y : ℂ)) (𝓝 0)) :
    ∃ LΨ : ℂ → ℂ, Supp8.Q3Rel.IsRetainedChartOff (fillH A) c.1 c.2.1 LΨ ∅ ∧
      EqOn c.2.2 (fun z => (LΨ z).im) (H \ fillH A) := by
  have hD := hc.1
  obtain ⟨LΨ, hlog, hlifteq⟩ := hD.2.2
  refine ⟨LΨ, ⟨hD.isOpen, hD.isConformalBijection, fun v hv => hD.inv_mem hv, fun v hv => hD.fwd_inv hv,
    hD.1.1, hlog, fun x _ => exists_tendsto_inv hgc hgi x,
    fun y hy => exists_tendsto_fwd_of_notMem_closure hAb hAc hc hgc hgi hy, fun y hy0 hy => ?_⟩, hlifteq⟩
  exact (hlift y hy0 hy).congr' (eventually_nhdsWithin_of_forall fun z hz => hlifteq hz)

end Land

end InteractingSLE.Theorem14.SB.FinRel
