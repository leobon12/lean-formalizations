/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2OlmLaw

/-!
# GW2's open lines: two charts of one domain sending the same points to `0` and `∞` differ by a dilation

Packet PROVE-GW2-STAGEMEAN, R117(b) round. The stage chart `cs` and the kernel-route chart `ca` map the same domain
`ℍ ∖ (retained ∪ past)` conformally onto `ℍ`, so `ca ∘ cs⁻¹` is a real Möbius map `M`
(`GW2Spm.exists_realMobius_of_same_dom`).
`M` is a dilation as soon as SOME family of points of the domain is sent near `0` by both charts and SOME family is sent
to `∞` by both — no boundary correspondence at a prime end is needed. On the stage route these are points of the
current piece's hull at small stage times (both charts send it into a small hull at `0`) and points of the
counterflow's hull increment just after its retained time (both charts send it to a neighbourhood of `∞`).

* `realMobius_b_eq_zero_of_tendsto`, `realMobius_e_eq_zero_of_tendsto`: the filter forms of
  `GW2Sdl.realMobius_b_eq_zero`, `GW2Sdl.realMobius_e_eq_zero`;
* **`exists_dilation_of_tendsto`**: two conformal charts with the same domain, a nontrivial filter along which both
  charts tend to `0` and one along which both tend to `∞`: `d.1 = λ · c.1` on the domain, `λ > 0`.

Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Complex
open QuantumZipper (H)
open QuantumZipper.CA (realMobius)

namespace InteractingSLE.Theorem14.GW2Olm

/-- **`b = 0`**: a real Möbius map of `ℍ` tending to `0` along a nontrivial filter of points of `ℍ` tending to `0`. -/
theorem realMobius_b_eq_zero_of_tendsto {a b e f : ℝ} (hdet : 0 < a * f - b * e) {ι : Type*} {l : Filter ι}
    [l.NeBot] {w : ι → ℂ} (hwH : ∀ᶠ i in l, w i ∈ H) (hw : Tendsto w l (𝓝 0))
    (hM : Tendsto (fun i => realMobius a b e f (w i)) l (𝓝 0)) : b = 0 := by
  have hid : ∀ᶠ i in l, realMobius a b e f (w i) * ((e : ℂ) * w i + f) = (a : ℂ) * w i + b := by
    filter_upwards [hwH] with i hi
    unfold realMobius
    exact div_mul_cancel₀ _ (GW2Sdl.realMobius_den_ne_zero hdet hi)
  have hcont : ∀ p q : ℂ, Tendsto (fun i => p * w i + q) l (𝓝 (p * 0 + q)) := fun p q =>
    ((continuous_const.mul continuous_id).add continuous_const).continuousAt.tendsto.comp hw
  have hL := hM.mul (hcont e f)
  have heq := tendsto_nhds_unique (hL.congr' hid) (hcont a b)
  simp only [zero_mul, mul_zero, zero_add] at heq
  exact_mod_cast heq.symm

/-- **`e = 0`**: a real Möbius map `aw/(ew + f)` tending to `∞` along a filter tending to `∞`. -/
theorem realMobius_e_eq_zero_of_tendsto {a e f : ℝ} {ι : Type*} {l : Filter ι} [l.NeBot] {w : ι → ℂ}
    (hw : Tendsto (fun i => ‖w i‖) l atTop) (hM : Tendsto (fun i => ‖realMobius a 0 e f (w i)‖) l atTop) :
    e = 0 := by
  by_contra he
  have heabs : 0 < |e| := abs_pos.2 he
  obtain ⟨i, hi, hbig⟩ := ((hM.eventually_gt_atTop (2 * |a| / |e|)).and
    (hw.eventually_ge_atTop (2 * |f| / |e| + 1))).exists
  have hwpos : 0 < ‖w i‖ := lt_of_lt_of_le (by positivity) hbig
  have hden : |e| * ‖w i‖ / 2 ≤ ‖(e : ℂ) * w i + f‖ := by
    have h1 : ‖(e : ℂ) * w i‖ - ‖(f : ℂ)‖ ≤ ‖(e : ℂ) * w i + f‖ := by
      have := norm_sub_norm_le ((e : ℂ) * w i) (-(f : ℂ))
      simpa [sub_neg_eq_add, norm_neg] using this
    rw [norm_mul, norm_real, norm_real, Real.norm_eq_abs, Real.norm_eq_abs] at h1
    have h2 : 2 * |f| ≤ |e| * ‖w i‖ := by
      have := (div_le_iff₀ heabs).1 (le_trans (le_add_of_nonneg_right zero_le_one) hbig)
      linarith
    linarith
  have hdpos : 0 < |e| * ‖w i‖ / 2 := by positivity
  have hle : ‖realMobius a 0 e f (w i)‖ ≤ 2 * |a| / |e| := by
    unfold realMobius
    rw [norm_div, ofReal_zero, add_zero, norm_mul, norm_real, Real.norm_eq_abs]
    calc |a| * ‖w i‖ / ‖(e : ℂ) * w i + f‖ ≤ |a| * ‖w i‖ / (|e| * ‖w i‖ / 2) :=
          div_le_div_of_nonneg_left (by positivity) hdpos hden
      _ = 2 * |a| / |e| := by field_simp
  exact absurd hi (not_lt.2 hle)

/-- **Two conformal charts of one domain that agree on sending a family to `0` and a family to `∞` differ by a
positive dilation.** -/
theorem exists_dilation_of_tendsto {c d : Chart} (hc : c.IsConformal) (hd : d.IsConformal)
    (hdom : (c.dom : Set ℂ) = d.dom) {ι₀ ι₁ : Type*} {l₀ : Filter ι₀} {l₁ : Filter ι₁} [l₀.NeBot] [l₁.NeBot]
    {z₀ : ι₀ → ℂ} {z₁ : ι₁ → ℂ} (hz₀ : ∀ᶠ i in l₀, z₀ i ∈ (c.dom : Set ℂ))
    (hz₁ : ∀ᶠ i in l₁, z₁ i ∈ (c.dom : Set ℂ)) (hc₀ : Tendsto (fun i => c.1 (z₀ i)) l₀ (𝓝 0))
    (hd₀ : Tendsto (fun i => d.1 (z₀ i)) l₀ (𝓝 0)) (hc₁ : Tendsto (fun i => ‖c.1 (z₁ i)‖) l₁ atTop)
    (hd₁ : Tendsto (fun i => ‖d.1 (z₁ i)‖) l₁ atTop) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ x ∈ (c.dom : Set ℂ), d.1 x = (lam : ℂ) * c.1 x := by
  obtain ⟨a, b, e, f, hdet, hM⟩ := GW2Spm.exists_realMobius_of_same_dom hc hd hdom
  have hread : ∀ x ∈ (c.dom : Set ℂ), d.1 x = realMobius a b e f (c.1 x) := fun x hx => by
    have h := hM (hc.fwd_mem hx)
    simp only at h
    rw [hc.inv_fwd hx] at h
    exact h
  have hb : b = 0 := by
    refine realMobius_b_eq_zero_of_tendsto hdet (l := l₀) (w := fun i => c.1 (z₀ i))
      (hz₀.mono fun i hi => hc.fwd_mem hi) hc₀ ?_
    refine hd₀.congr' ?_
    filter_upwards [hz₀] with i hi
    exact hread _ hi
  subst hb
  have he : e = 0 := by
    refine realMobius_e_eq_zero_of_tendsto (a := a) (f := f) (l := l₁) (w := fun i => c.1 (z₁ i)) hc₁ ?_
    refine hd₁.congr' ?_
    filter_upwards [hz₁] with i hi
    rw [hread _ hi]
  subst he
  have haf : 0 < a * f := by simpa using hdet
  have hf : f ≠ 0 := fun h => by rw [h, mul_zero] at haf; exact lt_irrefl 0 haf
  have hlam : 0 < a / f := by
    have hf2 : 0 < f ^ 2 := by positivity
    have e : a / f = a * f / f ^ 2 := by field_simp
    rw [e]
    exact div_pos haf hf2
  refine ⟨a / f, hlam, fun x hx => ?_⟩
  rw [hread x hx, GW2Sdl.realMobius_eq_dilation hf]

end InteractingSLE.Theorem14.GW2Olm
