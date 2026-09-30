import QuantumZipper.Proofs.Zipper.SWCoreDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-B5 (1): uniform deterministic data of a boundary map class

Task SWC-B5 (`handoff/SW-CORE.md`). Every map of the boundary class `SWCore.BdryClass a b ρ M m`
carries, on every inner interval `[a',b'] ⊂ (a,b)`, the uniform local data
`CoordChange.Data ψ a' b' δ m C` of M4-T4 with constants **depending only on the class and on
`[a',b']`** (`data_of_class`): Cauchy's estimates (mathlib
`Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`) applied twice bound `ψ''` on the
`ρ/4`-thickening by `32 M / ρ²`. Also: `‖ψ'‖ ≤ 4M/ρ` on `[a,b]` and the inverse Lipschitz bound
`m (t' − t) ≤ Re ψ t' − Re ψ t` on `[a',b']` (mean value theorem).

This is the uniform-in-the-class version of `CoordChange.exists_data` (same proof, with the
compactness constants replaced by the class constants; the Schwarz reflection step is copied).
Own elementary bookkeeping (Cauchy estimates: standard, e.g. Ahlfors, *Complex Analysis*, Ch. 4,
§2.3).
-/

noncomputable section

open MeasureTheory Filter Set Metric ComplexConjugate
open scoped Topology ENNReal

namespace QuantumZipper
namespace SWCore

variable {a b ρ M m : ℝ} {ψ : ℂ → ℂ}

theorem ofReal_mem_segC {a b t : ℝ} (ht : t ∈ Icc a b) : (t : ℂ) ∈ segC a b := ⟨t, ht, rfl⟩

/-- Cauchy estimate for `ψ'` on the `ρ/2`-thickening. -/
theorem norm_deriv_le_of_class (hψ : ψ ∈ BdryClass a b ρ M m) (hρ : 0 < ρ) {w : ℂ}
    (hw : w ∈ thickening (ρ / 2) (segC a b)) : ‖deriv ψ w‖ ≤ 4 * M / ρ := by
  obtain ⟨y, hy, hwy⟩ := mem_thickening_iff.1 hw
  have hsub : closedBall w (ρ / 4) ⊆ thickening ρ (segC a b) := fun v hv =>
    mem_thickening_iff.2 ⟨y, hy, by
      have := dist_triangle v w y; rw [mem_closedBall] at hv; linarith⟩
  have hd : DiffContOnCl ℂ ψ (ball w (ρ / 4)) :=
    (hψ.1.mono (closure_ball_subset_closedBall.trans hsub)).diffContOnCl
  have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity : 0 < ρ / 4) hd
    fun z hz => hψ.2.1 z (hsub (sphere_subset_closedBall hz))
  calc ‖deriv ψ w‖ ≤ M / (ρ / 4) := this
    _ = 4 * M / ρ := by field_simp

/-- Cauchy estimate for `ψ''` on the `ρ/4`-thickening. -/
theorem norm_deriv2_le_of_class (hψ : ψ ∈ BdryClass a b ρ M m) (hρ : 0 < ρ) {z : ℂ}
    (hz : z ∈ thickening (ρ / 4) (segC a b)) : ‖deriv (deriv ψ) z‖ ≤ 32 * M / ρ ^ 2 := by
  obtain ⟨y, hy, hzy⟩ := mem_thickening_iff.1 hz
  have hsub : closedBall z (ρ / 8) ⊆ thickening (ρ / 2) (segC a b) := fun v hv =>
    mem_thickening_iff.2 ⟨y, hy, by
      have := dist_triangle v z y; rw [mem_closedBall] at hv; linarith⟩
  have hdiff : DifferentiableOn ℂ (deriv ψ) (thickening (ρ / 2) (segC a b)) :=
    (hψ.1.mono (thickening_mono (by linarith) _)).deriv isOpen_thickening
  have hd : DiffContOnCl ℂ (deriv ψ) (ball z (ρ / 8)) :=
    (hdiff.mono (closure_ball_subset_closedBall.trans hsub)).diffContOnCl
  have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity : 0 < ρ / 8) hd
    fun v hv => norm_deriv_le_of_class hψ hρ (hsub (sphere_subset_closedBall hv))
  calc ‖deriv (deriv ψ) z‖ ≤ 4 * M / ρ / (ρ / 8) := this
    _ = 32 * M / ρ ^ 2 := by field_simp; ring

/-- `‖ψ'‖ ≤ 4M/ρ` on `[a,b]`. -/
theorem norm_deriv_le_of_class' (hψ : ψ ∈ BdryClass a b ρ M m) (hρ : 0 < ρ) {t : ℝ}
    (ht : t ∈ Icc a b) : ‖deriv ψ t‖ ≤ 4 * M / ρ :=
  norm_deriv_le_of_class hψ hρ (self_subset_thickening (by positivity) _ (ofReal_mem_segC ht))

/-- `ψ'` is real and `≥ m` in real part at interior points of `[a,b]`. -/
theorem deriv_facts_of_class (hψ : ψ ∈ BdryClass a b ρ M m) (hρ : 0 < ρ) {t : ℝ}
    (ht : t ∈ Ioo a b) : (deriv ψ t).im = 0 ∧ m ≤ (deriv ψ t).re := by
  have hJU : ∀ s ∈ Icc a b, (s : ℂ) ∈ thickening ρ (segC a b) := fun s hs =>
    self_subset_thickening hρ _ (ofReal_mem_segC hs)
  have him := F1.deriv_im_eq_zero isOpen_thickening hJU hψ.1 hψ.2.2.1 ht
  have htI : t ∈ Icc a b := Ioo_subset_Icc_self ht
  have hd : HasDerivAt ψ (deriv ψ t) (t : ℂ) :=
    (hψ.1.differentiableAt (isOpen_thickening.mem_nhds (hJU t htI))).hasDerivAt
  have hreD : HasDerivAt (fun x : ℝ => (ψ x).re) (deriv ψ t).re t := hd.real_of_complex
  have hnhds : Icc a b ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
  have hacc : AccPt t (𝓟 (Icc a b)) := by
    have h1 : AccPt t (𝓟 (univ : Set ℝ)) := by
      rw [accPt_principal_iff_nhdsWithin, ← compl_eq_univ_sdiff]; infer_instance
    have := h1.nhds_inter hnhds
    rwa [inter_univ] at this
  have hnn := hreD.hasDerivWithinAt.nonneg_of_monotoneOn hacc hψ.2.2.2.1.monotoneOn
  refine ⟨him, ?_⟩
  have hn : ‖deriv ψ t‖ = (deriv ψ t).re := by
    rw [← Complex.abs_re_eq_norm.2 him, abs_of_nonneg hnn]
  rw [← hn]; exact hψ.2.2.2.2 t htI

/-- **Uniform local data of the class** on an inner interval. -/
theorem data_of_class (hψ : ψ ∈ BdryClass a b ρ M m) (hρ : 0 < ρ) (hm : 0 < m) {a' b' : ℝ}
    (ha : a < a') (hb : b' < b) :
    CoordChange.Data ψ a' b' (min (ρ / 8) (min ((a' - a) / 4) ((b - b') / 4))) m
      (32 * M / ρ ^ 2) := by
  set δ := min (ρ / 8) (min ((a' - a) / 4) ((b - b') / 4)) with hδdef
  have hδ : 0 < δ := lt_min (by positivity) (lt_min (by linarith) (by linarith))
  have hδρ : 2 * δ ≤ ρ / 4 := by have := min_le_left (ρ / 8) (min ((a' - a) / 4) ((b - b') / 4)); linarith
  have hδa : 2 * δ ≤ (a' - a) / 2 := by
    have := min_le_right (ρ / 8) (min ((a' - a) / 4) ((b - b') / 4))
    have := min_le_left ((a' - a) / 4) ((b - b') / 4); linarith
  have hδb : 2 * δ ≤ (b - b') / 2 := by
    have := min_le_right (ρ / 8) (min ((a' - a) / 4) ((b - b') / 4))
    have := min_le_right ((a' - a) / 4) ((b - b') / 4); linarith
  have hsubI : ∀ t ∈ Icc a' b', t ∈ Icc a b := fun t ht => ⟨ha.le.trans ht.1, ht.2.trans hb.le⟩
  have hball4 : ∀ t ∈ Icc a' b', ball (t : ℂ) (2 * δ) ⊆ thickening (ρ / 4) (segC a b) :=
    fun t ht z hz => mem_thickening_iff.2 ⟨t, ofReal_mem_segC (hsubI t ht), by
      rw [mem_ball] at hz; linarith⟩
  have hballU : ∀ t ∈ Icc a' b', ball (t : ℂ) (2 * δ) ⊆ thickening ρ (segC a b) :=
    fun t ht => (hball4 t ht).trans (thickening_mono (by linarith) _)
  have hreal : ∀ t ∈ Icc a' b', ∀ x : ℝ, (x : ℂ) ∈ ball (t : ℂ) (2 * δ) → x ∈ Icc a b := by
    intro t ht x hx
    rw [mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs] at hx
    have := abs_lt.1 hx
    constructor <;> linarith [ht.1, ht.2]
  refine ⟨hδ, hm, fun t ht => hψ.1.mono (hballU t ht), ?_,
    fun t ht z hz => norm_deriv2_le_of_class hψ hρ (hball4 t ht hz),
    fun t ht => (deriv_facts_of_class hψ hρ ⟨ha.trans_le ht.1, ht.2.trans_lt hb⟩).2,
    fun t ht => (deriv_facts_of_class hψ hρ ⟨ha.trans_le ht.1, ht.2.trans_lt hb⟩).1⟩
  -- Schwarz reflection by the identity theorem (copied from `CoordChange.exists_data`)
  intro t ht z hz
  set B := ball (t : ℂ) (2 * δ)
  have hBo : IsOpen B := isOpen_ball
  have hψB : DifferentiableOn ℂ ψ B := hψ.1.mono (hballU t ht)
  have hg : DifferentiableOn ℂ (fun w => conj (ψ (conj w))) B := by
    intro w hw
    have hw' : conj w ∈ B := CoordChange.conj_mem_ball_real hw
    have h1 : DifferentiableAt ℂ ψ (conj w) := (hψB _ hw').differentiableAt (hBo.mem_nhds hw')
    have h2 := h1.conj_conj
    rw [Complex.conj_conj] at h2
    exact h2.differentiableWithinAt
  have hfreq : ∃ᶠ w in 𝓝[≠] (t : ℂ), ψ w = conj (ψ (conj w)) := by
    have hT : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] t) (𝓝[≠] (t : ℂ)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (Complex.continuous_ofReal.continuousAt.mono_left nhdsWithin_le_nhds) ?_
      exact eventually_nhdsWithin_of_forall fun x hx => by
        simpa using hx
    refine hT.frequently (Eventually.frequently ?_)
    have hB : ∀ᶠ x : ℝ in 𝓝[≠] t, (x : ℂ) ∈ B :=
      (Complex.continuous_ofReal.continuousAt.mono_left nhdsWithin_le_nhds).eventually
        (hBo.mem_nhds (mem_ball_self (by linarith)))
    filter_upwards [hB] with x hx
    have hxr := hψ.2.2.1 x (hreal t ht x hx)
    rw [Complex.conj_ofReal]
    exact (Complex.conj_eq_iff_im.2 hxr).symm
  have heq := (hψB.analyticOnNhd hBo).eqOn_of_preconnected_of_frequently_eq
    (hg.analyticOnNhd hBo) (convex_ball _ _).isPreconnected
    (mem_ball_self (by linarith)) hfreq
  have := heq (CoordChange.conj_mem_ball_real hz)
  simp only [Complex.conj_conj] at this
  exact this

/-- **Inverse Lipschitz bound** on `[a',b'] ⊂ (a,b)`: `m (t' − t) ≤ Re ψ t' − Re ψ t`. -/
theorem mul_sub_le_re_sub_of_class (hψ : ψ ∈ BdryClass a b ρ M m) (hρ : 0 < ρ) {t t' : ℝ}
    (ht : t ∈ Icc a b) (ht' : t' ∈ Icc a b) (htt : t ≤ t') :
    m * (t' - t) ≤ (ψ t').re - (ψ t).re := by
  rcases htt.eq_or_lt with h | h
  · subst h; simp
  have hJU : ∀ s ∈ Icc a b, (s : ℂ) ∈ thickening ρ (segC a b) := fun s hs =>
    self_subset_thickening hρ _ (ofReal_mem_segC hs)
  have hsub : Icc t t' ⊆ Icc a b := Icc_subset_Icc ht.1 ht'.2
  have hcont : ContinuousOn (fun s : ℝ => (ψ s).re) (Icc t t') :=
    Complex.continuous_re.comp_continuousOn (hψ.1.continuousOn.comp
      Complex.continuous_ofReal.continuousOn fun s hs => hJU s (hsub hs))
  have hder : ∀ s ∈ Ioo t t', HasDerivAt (fun s : ℝ => (ψ s).re) (deriv ψ s).re s :=
    fun s hs => ((hψ.1.differentiableAt (isOpen_thickening.mem_nhds
      (hJU s (hsub (Ioo_subset_Icc_self hs))))).hasDerivAt).real_of_complex
  obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope (fun s : ℝ => (ψ s).re)
    (fun s => (deriv ψ s).re) h hcont hder
  have hcI : c ∈ Ioo a b := ⟨ht.1.trans_lt hc.1, hc.2.trans_le ht'.2⟩
  have hmc := (deriv_facts_of_class hψ hρ hcI).2
  rw [hceq, le_div_iff₀ (by linarith)] at hmc
  linarith

end SWCore
end QuantumZipper
