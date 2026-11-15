/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2YeExt

/-!
# The free real line `(R, ∞)` of a domain chart and its boundary extension

Packet PROVE-T14-SB2LIFT (round 32; `IsStageS2` at a tail stage). `SB2YeLine` with the free line `(R, ∞)` in place of
`(0, ∞)`. For a domain chart `Ψ` of `ℍ ∖ D` whose forward map has real boundary values `e x` at the untouched points
`x > R`, with `e x → 0` as `x → R⁺`, and whose inverse extends continuously (`g`) to `ℍ̄` within distance `C` of the
identity:

* `g_eR`: `g (e x) = x`; `eq_e_of_gR`: `g p = x > R` only at `p = e x`; **`g_zeroR`**: `g 0 = R`;
* `continuousOn_eR`: `e` is continuous on `(R, ∞)`; `e_posR`: `e x > 0`; `exists_e_eqR`: every `y > 0` is some `e x`;
* **`g_pos_of_posR`**: `g` maps `(0, ∞)` into `(R, ∞)`; **`tendsto_g_re_right`**: `Re g y → R⁺` as `y → 0⁺`.

For B's stage chart at its seed `R` (the run chart is continuous from `ℍ` there and reads `0`) this says that the
stage coordinates' free line `(0, ∞)` is the physical free line `(R, ∞)`, and `0` is the seed. Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Sx

variable {D : Set ℂ} {Ψ : Chart} {e : ℝ → ℝ} {g : ℂ → ℂ} {C R : ℝ}

section Line

variable (hΨD : IsDomainChart (H \ D) Ψ) (he : ∀ x : ℝ, R < x → Tendsto Ψ.1 (𝓝[H] (x : ℂ)) (𝓝 (e x : ℂ)))
  (hfree : ∀ x : ℝ, R < x → ∃ ρ > 0, Disjoint (ball (x : ℂ) ρ) D)
  (hg : ∀ p ∈ Hbar, Tendsto Ψ.2.1 (𝓝[H] p) (𝓝 (g p)))

include hΨD he hfree hg in
/-- `g (e x) = x` at an untouched point `x > R`. -/
theorem g_eR {x : ℝ} (hx : R < x) : g (e x) = x := by
  obtain ⟨ρ, hρ, hd⟩ := hfree x hx
  have hxH : (x : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (x : ℂ).im by simp
  have : (𝓝[H] (x : ℂ)).NeBot := GW1P.neBot_nhdsWithin_H hxH
  have hev : ∀ᶠ w in 𝓝[H] (x : ℂ), w ∈ H \ D := by
    filter_upwards [inter_mem_nhdsWithin H (ball_mem_nhds (x : ℂ) hρ)] with w hw
    exact ⟨hw.1, fun hwD => disjoint_left.1 hd hw.2 hwD⟩
  have h1 : Tendsto Ψ.1 (𝓝[H] (x : ℂ)) (𝓝[H] (e x : ℂ)) :=
    tendsto_nhdsWithin_iff.2 ⟨he x hx, hev.mono fun w hw => hΨD.fwd_mem hw⟩
  have heH : ((e x : ℝ) : ℂ) ∈ Hbar := show (0 : ℝ) ≤ ((e x : ℝ) : ℂ).im by simp
  have h2 := (hg _ heH).comp h1
  have h3 : Tendsto (fun w => Ψ.2.1 (Ψ.1 w)) (𝓝[H] (x : ℂ)) (𝓝 (x : ℂ)) :=
    (tendsto_id.mono_left nhdsWithin_le_nhds).congr' (hev.mono fun w hw => (hΨD.inv_fwd hw).symm)
  exact tendsto_nhds_unique h2 h3

include hΨD he hg in
/-- `g p = x > R` only at `p = e x`. -/
theorem eq_e_of_gR {x : ℝ} (hx : R < x) {p : ℂ} (hp : p ∈ Hbar) (hgp : g p = x) : p = e x := by
  have : (𝓝[H] p).NeBot := GW1P.neBot_nhdsWithin_H hp
  have h1 : Tendsto Ψ.2.1 (𝓝[H] p) (𝓝[H] (x : ℂ)) := by
    rw [← hgp]
    exact tendsto_nhdsWithin_iff.2 ⟨hg p hp, eventually_nhdsWithin_of_forall fun y hy =>
      (hΨD.inv_mem hy).1⟩
  have h2 := (he x hx).comp h1
  have h3 : Tendsto (fun y => Ψ.1 (Ψ.2.1 y)) (𝓝[H] p) (𝓝 p) :=
    (tendsto_id.mono_left nhdsWithin_le_nhds).congr'
      (eventually_nhdsWithin_of_forall fun y hy => (hΨD.fwd_inv hy).symm)
  exact tendsto_nhds_unique h3 h2

include hΨD he hfree hg in
/-- `g 0 = R` when `e x → 0` as `x → R⁺`. -/
theorem g_zeroR (he0 : Tendsto e (𝓝[>] R) (𝓝 0)) (hgc : ContinuousOn g Hbar) : g 0 = R := by
  have h0H : (0 : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (0 : ℂ).im by simp
  have h1 : Tendsto (fun x : ℝ => ((e x : ℝ) : ℂ)) (𝓝[>] R) (𝓝[Hbar] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun x => show (0 : ℝ) ≤ ((e x : ℝ) : ℂ).im by simp⟩
    have := (Complex.continuous_ofReal.tendsto 0).comp he0
    rw [Complex.ofReal_zero] at this
    exact this
  have h2 := ((hgc 0 h0H).tendsto).comp h1
  have h3 : Tendsto (fun x : ℝ => g (e x)) (𝓝[>] R) (𝓝 ((R : ℝ) : ℂ)) := by
    refine ((Complex.continuous_ofReal.tendsto R).mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx using (g_eR hΨD he hfree hg hx).symm
  exact tendsto_nhds_unique h2 h3

include hΨD he hfree hg in
/-- `e` stays within `C` of the identity. -/
theorem abs_e_sub_leR (hgb : ∀ p ∈ Hbar, ‖g p - p‖ ≤ C) {x : ℝ} (hx : R < x) : |e x - x| ≤ C := by
  have h := hgb (e x) (show (0 : ℝ) ≤ ((e x : ℝ) : ℂ).im by simp)
  rw [g_eR hΨD he hfree hg hx, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm] at h
  exact h

include hΨD he hfree hg in
/-- **`e` is continuous on `(R, ∞)`**: bounded near each point, with `e x₀` the only cluster value. -/
theorem continuousOn_eR (hgc : ContinuousOn g Hbar) (hgb : ∀ p ∈ Hbar, ‖g p - p‖ ≤ C) :
    ContinuousOn e (Ioi R) := by
  intro x₀ hx₀
  have hx₀' : R < x₀ := hx₀
  refine (tendsto_of_subseq_tendsto fun ns hns => ?_).mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ n in atTop, ns n ∈ Ioo ((R + x₀) / 2) (x₀ + 1) :=
    hns.eventually (Ioo_mem_nhds (by linarith) (by linarith))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  set y : ℕ → ℝ := fun n => ns (n + N) with hy
  have hy' : ∀ n, y n ∈ Ioo ((R + x₀) / 2) (x₀ + 1) := fun n => hN _ (by omega)
  have hbd : ∀ n, e (y n) ∈ closedBall (0 : ℝ) (|(R + x₀) / 2| + |x₀ + 1| + C) := by
    intro n
    have h1 := abs_e_sub_leR hΨD he hfree hg hgb (show R < y n by linarith [(hy' n).1])
    rw [mem_closedBall, Real.dist_eq, sub_zero, abs_le]
    have := hy' n
    have ha := neg_abs_le ((R + x₀) / 2)
    have hb := le_abs_self (x₀ + 1)
    have ha' := abs_nonneg (x₀ + 1)
    have hb' := abs_nonneg ((R + x₀) / 2)
    constructor <;> [linarith [(abs_le.1 h1).1, this.1]; linarith [(abs_le.1 h1).2, this.2]]
  obtain ⟨z, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded isBounded_closedBall hbd
  refine ⟨fun n => φ n + N, ?_⟩
  have hyφ : Tendsto (fun n => y (φ n)) atTop (𝓝 x₀) :=
    hns.comp (tendsto_atTop_mono (fun n => Nat.le_add_right (φ n) N) hφ.tendsto_atTop)
  have hzH : (z : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (z : ℂ).im by simp
  have hlimC : Tendsto (fun n => ((e (y (φ n)) : ℝ) : ℂ)) atTop (𝓝[Hbar] (z : ℂ)) :=
    tendsto_nhdsWithin_iff.2 ⟨(Complex.continuous_ofReal.tendsto z).comp hlim,
      Eventually.of_forall fun n => show (0 : ℝ) ≤ ((e (y (φ n)) : ℝ) : ℂ).im by simp⟩
  have h1 := ((hgc _ hzH).tendsto).comp hlimC
  have h2 : Tendsto (fun n => g (e (y (φ n)))) atTop (𝓝 ((x₀ : ℝ) : ℂ)) := by
    refine ((Complex.continuous_ofReal.tendsto x₀).comp hyφ).congr fun n => ?_
    exact (g_eR hΨD he hfree hg (show R < y (φ n) by linarith [(hy' (φ n)).1])).symm
  have hgz : g z = x₀ := tendsto_nhds_unique h1 h2
  have hz : (z : ℂ) = e x₀ := eq_e_of_gR hΨD he hg hx₀' hzH hgz
  have hz' : z = e x₀ := Complex.ofReal_injective hz
  rw [← hz']
  exact hlim

include hΨD he hfree hg in
/-- **`e` is positive on `(R, ∞)`** (`g 0 = R`, `e x ≥ x − C` and the intermediate value theorem). -/
theorem e_posR (he0 : Tendsto e (𝓝[>] R) (𝓝 0)) (hgc : ContinuousOn g Hbar) (hgb : ∀ p ∈ Hbar, ‖g p - p‖ ≤ C)
    {x : ℝ} (hx : R < x) : 0 < e x := by
  have hg0 := g_zeroR hΨD he hfree hg he0 hgc
  have hzero : ∀ x' : ℝ, R < x' → e x' ≠ 0 := fun x' hx' h => by
    have := g_eR hΨD he hfree hg hx'
    rw [h, Complex.ofReal_zero, hg0] at this
    exact hx'.ne (Complex.ofReal_injective this)
  by_contra hle
  push Not at hle
  rcases hle.lt_or_eq with hlt | heq
  · set b := max x C + 1 with hb
    have hxb : x ≤ b := by rw [hb]; linarith [le_max_left x C]
    have hRb : R < b := by linarith
    have heb : 0 < e b := by
      have := abs_e_sub_leR hΨD he hfree hg hgb hRb
      linarith [(abs_le.1 this).1, le_max_right x C]
    have hc : ContinuousOn e (Icc x b) :=
      (continuousOn_eR hΨD he hfree hg hgc hgb).mono fun t ht => show R < t by linarith [ht.1]
    obtain ⟨t, ht, het⟩ := intermediate_value_Icc hxb hc ⟨hlt.le, heb.le⟩
    exact hzero t (by linarith [ht.1]) het
  · exact hzero x hx heq

include hΨD he hfree hg in
/-- **Every `y > 0` is some `e x` with `x > R`.** -/
theorem exists_e_eqR (he0 : Tendsto e (𝓝[>] R) (𝓝 0)) (hgc : ContinuousOn g Hbar)
    (hgb : ∀ p ∈ Hbar, ‖g p - p‖ ≤ C) {y : ℝ} (hy : 0 < y) : ∃ x, R < x ∧ e x = y := by
  have hev : ∀ᶠ a in 𝓝[>] R, e a < y ∧ R < a :=
    (he0.eventually (gt_mem_nhds hy)).and self_mem_nhdsWithin
  obtain ⟨a, hay, ha⟩ := hev.exists
  set b := max a (y + C) + 1 with hb
  have hab : a ≤ b := by rw [hb]; linarith [le_max_left a (y + C)]
  have hRb : R < b := by linarith
  have heb : y ≤ e b := by
    have := abs_e_sub_leR hΨD he hfree hg hgb hRb
    linarith [(abs_le.1 this).1, le_max_right a (y + C)]
  have hc : ContinuousOn e (Icc a b) :=
    (continuousOn_eR hΨD he hfree hg hgc hgb).mono fun t ht => show R < t by linarith [ht.1]
  obtain ⟨t, ht, het⟩ := intermediate_value_Icc hab hc ⟨hay.le, heb⟩
  exact ⟨t, by linarith [ht.1], het⟩

include hΨD he hfree hg in
/-- **`g` maps `(0, ∞)` into `(R, ∞)`.** -/
theorem g_pos_of_posR (he0 : Tendsto e (𝓝[>] R) (𝓝 0)) (hgc : ContinuousOn g Hbar)
    (hgb : ∀ p ∈ Hbar, ‖g p - p‖ ≤ C) {y : ℝ} (hy : 0 < y) : ∃ x : ℝ, R < x ∧ g y = x := by
  obtain ⟨x, hx, hex⟩ := exists_e_eqR hΨD he hfree hg he0 hgc hgb hy
  exact ⟨x, hx, by rw [← hex]; exact g_eR hΨD he hfree hg hx⟩

include hΨD he hfree hg in
/-- **`Re g y → R⁺` as `y → 0⁺`** (`g` is continuous at `0` with `g 0 = R`, and real `> R` on `(0, ∞)`). -/
theorem tendsto_g_re_right (he0 : Tendsto e (𝓝[>] R) (𝓝 0)) (hgc : ContinuousOn g Hbar)
    (hgb : ∀ p ∈ Hbar, ‖g p - p‖ ≤ C) :
    Tendsto (fun y : ℝ => (g (y : ℂ)).re) (𝓝[>] 0) (𝓝[>] R) := by
  have h0H : (0 : ℂ) ∈ Hbar := show (0 : ℝ) ≤ (0 : ℂ).im by simp
  have hg0 := g_zeroR hΨD he hfree hg he0 hgc
  have h1 : Tendsto (fun y : ℝ => (y : ℂ)) (𝓝[>] 0) (𝓝[Hbar] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun y => show (0 : ℝ) ≤ (y : ℂ).im by simp⟩
    have := (Complex.continuous_ofReal.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    rwa [Complex.ofReal_zero] at this
  have h2 := ((hgc 0 h0H).tendsto).comp h1
  rw [hg0] at h2
  have h3 := (Complex.continuous_re.tendsto _).comp h2
  rw [Complex.ofReal_re] at h3
  refine tendsto_nhdsWithin_iff.2 ⟨h3, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with y hy
  obtain ⟨x, hx, hgx⟩ := g_pos_of_posR hΨD he hfree hg he0 hgc hgb hy
  show R < (g (y : ℂ)).re
  rw [hgx, Complex.ofReal_re]
  exact hx

end Line

end InteractingSLE.Theorem14.SB.Sx
