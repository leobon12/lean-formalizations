/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.Aux10FullLocal
import InteractingSLE.Foundations.Loewner.ConformalImageSmallHull
import QuantumZipper.Proofs.Complex.BasicsUnivalent

/-!
# Aux. lemma 10: reflection of a conformal map across a protected real interval

Packet PROVE-T14-BR9. Specification Aux. lemma 10, (TD1)–(TD2): the comparison map "reflects conformally across the
real interval representing the old filled hull". Abstract form (`exists_reflect`): let `R` map an open `Ω ⊆ ℍ`
conformally onto `ℍ`, let `Ω` contain the upper half of the `r`-neighbourhood of a real segment `[y_a, y_b]`, let `R` be
bounded there, and let a real point `π < y_a − r` keep a positive distance from `ℍ \ Ω`. Then on a thin rectangle
`rect y_a y_b ρ` around the segment, `R` extends to a holomorphic `G`, symmetric under conjugation and real on the
real axis. Proof: `R = M ∘ g_B ∘ m_π` with `B = m_π(ℍ \ Ω)` a compact hull (`exists_factorization`), and
`G = M ∘ ĝ_B ∘ m_π` with `ĝ_B = reflectMapOut g_B` (Schwarz reflection, `IsMapOut.exists_reflection`); the pole of `M`
is avoided because `R` is bounded.

`deriv_pos_of_reflect`: such a `G`, injective on the upper half, has `G' > 0` on the real axis (`G'` is real by the
symmetry, `Re G' ≥ 0` because `G` maps the upper half into `ℍ`, and `G' ≠ 0` because `G` is injective on the whole
rectangle: on the real axis by monotonicity and the identity theorem).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped ComplexConjugate
open QuantumZipper (H)
open QuantumZipper.CA (realMobius)

namespace InteractingSLE

namespace Aux10

open ConformalImage Sec5.CrossRestart

/-- The thin rectangle `(a − ρ, b + ρ) × (−ρ, ρ)` around the real segment `[a, b]`. -/
def rect (a b ρ : ℝ) : Set ℂ := {w | a - ρ < w.re ∧ w.re < b + ρ ∧ |w.im| < ρ}

theorem isOpen_rect (a b ρ : ℝ) : IsOpen (rect a b ρ) :=
  (isOpen_lt continuous_const continuous_re).inter ((isOpen_lt continuous_re continuous_const).inter
    (isOpen_lt (continuous_abs.comp continuous_im) continuous_const))

theorem convex_rect (a b ρ : ℝ) : Convex ℝ (rect a b ρ) := by
  have h1 : Convex ℝ {w : ℂ | a - ρ < w.re} := convex_halfSpace_gt Complex.reLm.isLinear _
  have h2 : Convex ℝ {w : ℂ | w.re < b + ρ} := convex_halfSpace_lt Complex.reLm.isLinear _
  have h3 : Convex ℝ {w : ℂ | |w.im| < ρ} := by
    have : {w : ℂ | |w.im| < ρ} = {w : ℂ | -ρ < w.im} ∩ {w : ℂ | w.im < ρ} := by
      ext w; simp [abs_lt]
    rw [this]
    exact (convex_halfSpace_gt Complex.imLm.isLinear _).inter (convex_halfSpace_lt Complex.imLm.isLinear _)
  exact h1.inter (h2.inter h3)

theorem conj_mem_rect {a b ρ : ℝ} {w : ℂ} (hw : w ∈ rect a b ρ) : conj w ∈ rect a b ρ := by
  obtain ⟨h1, h2, h3⟩ := hw
  exact ⟨by simpa using h1, by simpa using h2, by simpa [abs_neg] using h3⟩

theorem re_mem_rect {a b ρ : ℝ} {w : ℂ} (hw : w ∈ rect a b ρ) : ((w.re : ℝ) : ℂ) ∈ rect a b ρ := by
  obtain ⟨h1, h2, h3⟩ := hw
  exact ⟨by simpa using h1, by simpa using h2, by simpa using (abs_nonneg w.im).trans_lt h3⟩

theorem rect_mono {a b ρ ρ' : ℝ} (h : ρ ≤ ρ') : rect a b ρ ⊆ rect a b ρ' := fun _ ⟨h1, h2, h3⟩ =>
  ⟨by linarith, by linarith, by linarith⟩

/-- A point of the rectangle is within `2ρ` of a point of the segment. -/
theorem exists_near_of_mem_rect {a b ρ : ℝ} (hab : a ≤ b) {w : ℂ} (hw : w ∈ rect a b ρ) :
    ∃ y ∈ Icc a b, ‖w - y‖ < 2 * ρ := by
  obtain ⟨h1, h2, h3⟩ := hw
  have hρ' : 0 < ρ := (abs_nonneg _).trans_lt h3
  set y := max a (min b w.re) with hy
  refine ⟨y, ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩, ?_⟩
  have hre : |w.re - y| < ρ := by
    rw [abs_lt]
    constructor
    · rcases le_total w.re b with h | h
      · rw [hy, min_eq_right h]; rcases le_total a w.re with h' | h'
        · rw [max_eq_right h']; linarith
        · rw [max_eq_left h']; linarith
      · rw [hy, min_eq_left h, max_eq_right hab]; linarith
    · rcases le_total w.re b with h | h
      · rw [hy, min_eq_right h]; linarith [le_max_right a w.re]
      · rw [hy, min_eq_left h, max_eq_right hab]; linarith
  have : ‖w - y‖ ≤ |w.re - y| + |w.im| := by
    have := Complex.norm_le_abs_re_add_abs_im (w - y)
    simpa using this
  linarith

/-- The real Möbius maps commute with conjugation. -/
theorem realMobius_conj (a b c d : ℝ) (z : ℂ) : realMobius a b c d (conj z) = conj (realMobius a b c d z) := by
  simp [realMobius, map_div₀]

/-- A real Möbius map sends real points to real points. -/
theorem im_realMobius_ofReal (a b c d x : ℝ) : (realMobius a b c d x).im = 0 := by
  simp only [realMobius]
  rw [show ((a : ℂ) * x + b) / ((c : ℂ) * x + d) = ((((a * x + b) / (c * x + d) : ℝ)) : ℂ) by push_cast; ring]
  exact ofReal_im _

/-- **Schwarz reflection of a mapping-out function on a disc** around a real point away from the hull, as an equality
for `reflectMapOut`. -/
theorem eqOn_reflectMapOut_ball {L : Set ℂ} {g : ℂ → ℂ} (hL : IsHPHull L) (hg : IsMapOut L g) {y ρ : ℝ}
    (hd : Disjoint (ball (y : ℂ) ρ) L) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (ball (y : ℂ) (ρ / 2)) ∧
      EqOn (reflectMapOut g) G (ball (y : ℂ) (ρ / 2)) ∧
      (∀ z ∈ ball (y : ℂ) (ρ / 2), G (conj z) = conj (G z)) ∧
      (∀ z ∈ ball (y : ℂ) (ρ / 2), z.im = 0 → (G z).im = 0) := by
  obtain ⟨G, hGd, hGS, hGsymm, hGreal, -, hGlim⟩ := hg.exists_reflection hL hd
  refine ⟨G, hGd, fun z hz => ?_, hGsymm, hGreal⟩
  rcases lt_trichotomy z.im 0 with hneg | hzero | hpos
  · rw [reflectMapOut_of_neg g hneg]
    have hcz : conj z ∈ ball (y : ℂ) (ρ / 2) ∩ H := by
      refine ⟨?_, show 0 < (conj z).im by simp; linarith⟩
      have hcy : conj (y : ℂ) = y := conj_ofReal y
      rw [mem_ball, ← hcy, dist_conj_conj]
      exact hz
    rw [← hGS hcz, hGsymm z hz, conj_conj]
  · rw [reflectMapOut_of_eq g hzero]
    have h := hGlim z hz hzero
    have hn : 𝓝[ball (y : ℂ) (ρ / 2) ∩ H] z = 𝓝[H] z :=
      nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds hz))
    rw [hn] at h
    have : (𝓝[H] z).NeBot := by
      refine mem_closure_iff_nhdsWithin_neBot.1 ?_
      have := subset_closure_ball_inter_H z 1 ⟨mem_ball_self one_pos, show 0 ≤ z.im from hzero.ge⟩
      exact closure_mono inter_subset_right this
    exact h.limUnder_eq
  · rw [reflectMapOut_of_pos g hpos]
    exact (hGS ⟨hz, hpos⟩).symm

/-- `m_π` sends a real point `x ≠ π` to the real point `−1/(x − π)`. -/
theorem mobAt_ofReal (π x : ℝ) : mobAt π x = ((-1 / (x - π) : ℝ) : ℂ) := by
  rw [mobAt_apply]
  push_cast
  ring

theorem mobAt_conj (π : ℝ) (z : ℂ) : mobAt π (conj z) = conj (mobAt π z) := realMobius_conj _ _ _ _ z

/-- **Reflection of a conformal map across a protected real interval.** -/
theorem exists_reflect {Ω : Set ℂ} {R : ℂ → ℂ} (hΩo : IsOpen Ω) (hΩH : Ω ⊆ H) (hRd : DifferentiableOn ℂ R Ω)
    (hRinj : InjOn R Ω) (hRim : R '' Ω = H) {ya yb r : ℝ} (hab : ya ≤ yb) (hr : 0 < r)
    (hN : ∀ w ∈ H, (∃ y ∈ Icc ya yb, ‖w - y‖ < r) → w ∈ Ω) {C : ℝ}
    (hRb : ∀ w ∈ H, (∃ y ∈ Icc ya yb, ‖w - y‖ < r) → ‖R w‖ ≤ C)
    {π : ℝ} (hπ : π < ya - r) {δ : ℝ} (hδ : 0 < δ) (hsep : ∀ z ∈ H \ Ω, δ ≤ ‖z - π‖) :
    ∃ ρ > 0, ∃ G : ℂ → ℂ, rect ya yb ρ ∩ H ⊆ Ω ∧ DifferentiableOn ℂ G (rect ya yb ρ) ∧
      EqOn G R (rect ya yb ρ ∩ H) ∧ (∀ w ∈ rect ya yb ρ, G (conj w) = conj (G w)) ∧
      (∀ w ∈ rect ya yb ρ, w.im = 0 → (G w).im = 0) := by
  obtain ⟨hB, hcompl, g, a, b, c, d, hg, hdet, hfac⟩ :=
    exists_factorization hΩo hΩH hRd hRinj hRim hδ hsep
  set m := mobAt π with hm
  set B := m '' (H \ Ω) with hBdef
  set M := realMobius a b c d with hM
  set Cπ : ℝ := yb - π + r with hCπ
  have hCπpos : 0 < Cπ := by rw [hCπ]; linarith
  set η : ℝ := (r / 2) / ((r / 2 + Cπ) * Cπ) with hη
  have hηpos : 0 < η := by positivity
  set ρ : ℝ := min (r / 4) (η * (r / 2) ^ 2 / 2) with hρdef
  have hρ : 0 < ρ := by positivity
  have hρr : ρ ≤ r / 4 := min_le_left _ _
  have hρη : ρ ≤ η * (r / 2) ^ 2 / 2 := min_le_right _ _
  have hwπ : ∀ w ∈ rect ya yb ρ, r / 2 ≤ ‖w - π‖ ∧ ‖w - π‖ ≤ Cπ := by
    intro w hw
    obtain ⟨h1, h2, h3⟩ := hw
    constructor
    · have : r / 2 ≤ (w - π).re := by simp only [sub_re, ofReal_re]; linarith
      exact this.trans (re_le_norm _)
    · have h4 := Complex.norm_le_abs_re_add_abs_im (w - π)
      simp only [sub_re, ofReal_re, sub_im, ofReal_im, sub_zero] at h4
      rw [abs_of_pos (by linarith)] at h4
      rw [hCπ]
      linarith
  have hnear : ∀ w ∈ rect ya yb ρ, ∃ y ∈ Icc ya yb, ‖w - y‖ < r := fun w hw => by
    obtain ⟨y, hy, h⟩ := exists_near_of_mem_rect hab hw
    exact ⟨y, hy, by linarith⟩
  have hΩrect : ∀ w ∈ rect ya yb ρ ∩ H, w ∈ Ω := fun w hw => hN w hw.2 (hnear w hw.1)
  have hw0 : ∀ w ∈ rect ya yb ρ, w - π ≠ 0 := fun w hw => norm_pos_iff.1 (by linarith [(hwπ w hw).1])
  -- the separation of `B` from `m(rect)`
  have hsepB : ∀ z ∈ H \ Ω, ∀ w ∈ rect ya yb ρ, η ≤ ‖m z - m w‖ := by
    intro z hz w hw
    obtain ⟨y, hy, hwy⟩ := exists_near_of_mem_rect hab hw
    have hzy : r ≤ ‖z - y‖ := by
      by_contra h
      push Not at h
      exact hz.2 (hN z hz.1 ⟨y, hy, h⟩)
    have hzw : r / 2 ≤ ‖z - w‖ := by
      have : ‖z - y‖ ≤ ‖z - w‖ + ‖w - y‖ := by
        calc ‖z - y‖ = ‖(z - w) + (w - y)‖ := by ring_nf
          _ ≤ _ := norm_add_le _ _
      linarith
    obtain ⟨-, hw2⟩ := hwπ w hw
    have hz0 : z - π ≠ 0 := sub_ne_zero_of_mem_H hz.1 π
    rw [hm, mobAt_sub_mobAt hz0 (hw0 w hw), norm_div, norm_mul]
    have hzπ : ‖z - π‖ ≤ ‖z - w‖ + Cπ := by
      calc ‖z - π‖ = ‖(z - w) + (w - π)‖ := by ring_nf
        _ ≤ ‖z - w‖ + ‖w - π‖ := norm_add_le _ _
        _ ≤ _ := by linarith
    have hzx0 : 0 < ‖z - π‖ := norm_pos_iff.2 hz0
    have hwx0 : 0 < ‖w - π‖ := norm_pos_iff.2 (hw0 w hw)
    have h1 : ‖z - π‖ * ‖w - π‖ ≤ (‖z - w‖ + Cπ) * Cπ := mul_le_mul hzπ hw2 hwx0.le (by positivity)
    calc η = (r / 2) / ((r / 2 + Cπ) * Cπ) := rfl
      _ ≤ ‖z - w‖ / ((‖z - w‖ + Cπ) * Cπ) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [mul_le_mul_of_nonneg_right hzw (mul_pos hCπpos hCπpos).le]
      _ ≤ ‖z - w‖ / (‖z - π‖ * ‖w - π‖) :=
          div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) h1
  -- the local reflections
  have hloc : ∀ w ∈ rect ya yb ρ, ∃ v : ℝ, m w ∈ ball (v : ℂ) (η / 2) ∧
      ∃ Gv : ℂ → ℂ, DifferentiableOn ℂ Gv (ball (v : ℂ) (η / 2)) ∧
        EqOn (reflectMapOut g) Gv (ball (v : ℂ) (η / 2)) ∧
        (∀ z ∈ ball (v : ℂ) (η / 2), Gv (conj z) = conj (Gv z)) ∧
        (∀ z ∈ ball (v : ℂ) (η / 2), z.im = 0 → (Gv z).im = 0) := by
    intro w hw
    have hwr := re_mem_rect hw
    refine ⟨-1 / (w.re - π), ?_, ?_⟩
    · rw [mem_ball, ← mobAt_ofReal, dist_eq_norm, hm, mobAt_sub_mobAt (hw0 w hw) (hw0 _ hwr), norm_div,
        norm_mul]
      have hnum : ‖w - (w.re : ℂ)‖ < ρ := by
        have : w - (w.re : ℂ) = (w.im : ℂ) * I := by
          apply Complex.ext <;> simp
        rw [this, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
        exact hw.2.2
      have hd1 := (hwπ w hw).1
      have hd2 := (hwπ _ hwr).1
      have hprod : (r / 2) ^ 2 ≤ ‖w - π‖ * ‖(w.re : ℂ) - π‖ := by
        rw [sq]; exact mul_le_mul hd1 hd2 (by positivity) (norm_nonneg _)
      rw [div_lt_iff₀ (mul_pos (by linarith) (by linarith))]
      have h3 := mul_le_mul_of_nonneg_left hprod (by positivity : (0 : ℝ) ≤ η / 2)
      have h4 : η * (r / 2) ^ 2 / 2 = η / 2 * (r / 2) ^ 2 := by ring
      linarith
    · have hdisj : Disjoint (ball ((-1 / (w.re - π) : ℝ) : ℂ) η) B := by
        rw [Set.disjoint_left]
        rintro u hu ⟨z, hz, rfl⟩
        have := hsepB z hz _ hwr
        rw [← mobAt_ofReal, ← hm, mem_ball, dist_eq_norm] at hu
        linarith
      exact eqOn_reflectMapOut_ball hB hg hdisj
  -- the denominator of `M` does not vanish on the reflected values
  have hdetM : c = 0 → d ≠ 0 := fun hc0 hd0 => by simp [hc0, hd0] at hdet
  have hden_im : ∀ s : ℂ, s.im ≠ 0 → (c : ℂ) * s + d ≠ 0 := by
    intro s hs h
    by_cases hc0 : c = 0
    · simp [hc0] at h
      exact hdetM hc0 h
    · have := congrArg Complex.im h
      simp at this
      rcases this with h' | h'
      · exact hc0 h'
      · exact hs h'
  have hgH : ∀ w ∈ rect ya yb ρ ∩ H, reflectMapOut g (m w) ∈ H ∧ M (reflectMapOut g (m w)) = R w := by
    intro w hw
    have hwΩ := hΩrect w hw
    have hmw : m w ∈ H \ B := by rw [hcompl]; exact ⟨w, hwΩ, rfl⟩
    rw [reflectMapOut_of_pos g hmw.1]
    exact ⟨hg.1.2.mapsTo hmw, (hfac w hwΩ).symm⟩
  have hsymm : ∀ w ∈ rect ya yb ρ, reflectMapOut g (m (conj w)) = conj (reflectMapOut g (m w)) := by
    intro w hw
    obtain ⟨v, hmv, Gv, -, hGeq, hGsymm, -⟩ := hloc w hw
    have hmv' : conj (m w) ∈ ball (v : ℂ) (η / 2) := by
      rw [mem_ball, ← conj_ofReal, dist_conj_conj]
      exact hmv
    rw [hm, mobAt_conj, ← hm, hGeq hmv', hGeq hmv, hGsymm _ hmv]
  have hden : ∀ w ∈ rect ya yb ρ, (c : ℂ) * reflectMapOut g (m w) + d ≠ 0 := by
    intro w hw
    rcases lt_trichotomy w.im 0 with hneg | hzero | hpos
    · have hcw : conj w ∈ rect ya yb ρ ∩ H := ⟨conj_mem_rect hw, show 0 < (conj w).im by simp; linarith⟩
      have h1 := (hgH _ hcw).1
      rw [hsymm w hw] at h1
      refine hden_im _ fun h => ?_
      have : (conj (reflectMapOut g (m w))).im = 0 := by rw [conj_im, h, neg_zero]
      have h1' : 0 < (conj (reflectMapOut g (m w))).im := h1
      rw [this] at h1'
      exact lt_irrefl _ h1'
    · intro h0
      have hc0 : c ≠ 0 := fun hc0 => by
        rw [hc0, ofReal_zero, zero_mul, zero_add] at h0
        exact hdetM hc0 (by exact_mod_cast h0)
      obtain ⟨v, hmv, Gv, hGd, hGeq, -, -⟩ := hloc w hw
      set s := reflectMapOut g (m w) with hs
      have hnum : (a : ℂ) * s + b ≠ 0 := by
        intro hn
        have hc' : (c : ℂ) ≠ 0 := ofReal_ne_zero.2 hc0
        have hs' : s = -(d : ℂ) / c := by
          rw [eq_div_iff hc']
          linear_combination h0
        have h3 : ((-(a * d - b * c) : ℝ) : ℂ) = c * ((a : ℂ) * s + b) := by
          rw [hs']
          field_simp
          push_cast
          ring
        rw [hn, mul_zero] at h3
        have h4 : -(a * d - b * c) = 0 := by exact_mod_cast h3
        linarith
      -- along `w + iε`, the values of `R` blow up
      have hcm : ContinuousAt (fun z => reflectMapOut g (m z)) w := by
        have h1 : ContinuousAt m w := continuousAt_realMobius (by
          simp only [ofReal_one, one_mul, ofReal_neg]; rw [← sub_eq_add_neg]; exact hw0 w hw)
        have h2 : ContinuousAt (reflectMapOut g) (m w) :=
          ((hGd.continuousOn.continuousAt (isOpen_ball.mem_nhds hmv)).congr
            (Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hmv) fun z hz => (hGeq hz).symm))
        exact h2.comp h1
      have hpath : Tendsto (fun ε : ℝ => w + ε * I) (𝓝[>] 0) (𝓝 w) := by
        have : Tendsto (fun ε : ℝ => w + ε * I) (𝓝 0) (𝓝 (w + (0 : ℝ) * I)) :=
          ((continuous_const.add (continuous_ofReal.mul continuous_const)).tendsto 0)
        simpa using this.mono_left nhdsWithin_le_nhds
      have hu := hcm.tendsto.comp hpath
      have hden0 : Tendsto (fun ε : ℝ => (c : ℂ) * reflectMapOut g (m (w + ε * I)) + d) (𝓝[>] 0) (𝓝 0) := by
        have hcont : Continuous (fun u : ℂ => (c : ℂ) * u + d) := by fun_prop
        have := hcont.continuousAt.tendsto.comp hu
        have h0' : (c : ℂ) * reflectMapOut g (m w) + d = 0 := h0
        rw [h0'] at this
        exact this
      have hnum0 : Tendsto (fun ε : ℝ => (a : ℂ) * reflectMapOut g (m (w + ε * I)) + b) (𝓝[>] 0)
          (𝓝 ((a : ℂ) * s + b)) :=
        ((by fun_prop : Continuous (fun u : ℂ => (a : ℂ) * u + b)).continuousAt.tendsto.comp hu)
      set κ := ‖(a : ℂ) * s + b‖ with hκ
      have hκpos : 0 < κ := norm_pos_iff.2 hnum
      have hev1 : ∀ᶠ ε : ℝ in 𝓝[>] 0, ‖(c : ℂ) * reflectMapOut g (m (w + ε * I)) + d‖ < κ / (2 * (|C| + 1)) :=
        hden0.norm.eventually (gt_mem_nhds (by rw [norm_zero]; positivity))
      have hev2 : ∀ᶠ ε : ℝ in 𝓝[>] 0, κ / 2 < ‖(a : ℂ) * reflectMapOut g (m (w + ε * I)) + b‖ :=
        hnum0.norm.eventually (lt_mem_nhds (by linarith))
      have hev3 : ∀ᶠ ε : ℝ in 𝓝[>] 0, w + ε * I ∈ rect ya yb ρ :=
        hpath.eventually ((isOpen_rect ya yb ρ).mem_nhds hw)
      have hev4 : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε := self_mem_nhdsWithin
      obtain ⟨ε, h1, h2, h3, h4⟩ := (hev1.and (hev2.and (hev3.and hev4))).exists
      have hεH : w + ε * I ∈ H := by
        show 0 < (w + ε * I).im
        simp [hzero, h4]
      obtain ⟨hgH1, hgH2⟩ := hgH _ ⟨h3, hεH⟩
      have hb := hRb _ hεH (hnear _ h3)
      rw [← hgH2, hM, realMobius, norm_div] at hb
      have hdpos : 0 < ‖(c : ℂ) * reflectMapOut g (m (w + ε * I)) + d‖ :=
        norm_pos_iff.2 (hden_im _ (ne_of_gt hgH1))
      rw [div_le_iff₀ hdpos] at hb
      have e1 : C * ‖(c : ℂ) * reflectMapOut g (m (w + ε * I)) + d‖ ≤
          |C| * ‖(c : ℂ) * reflectMapOut g (m (w + ε * I)) + d‖ :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (norm_nonneg _)
      have e2 : |C| * ‖(c : ℂ) * reflectMapOut g (m (w + ε * I)) + d‖ ≤ |C| * (κ / (2 * (|C| + 1))) :=
        mul_le_mul_of_nonneg_left h1.le (abs_nonneg C)
      have e3 : |C| * (κ / (2 * (|C| + 1))) < κ / 2 := by
        rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by positivity)]
        nlinarith [abs_nonneg C]
      linarith
    · exact hden_im _ (ne_of_gt (hgH w ⟨hw, hpos⟩).1)
  refine ⟨ρ, hρ, fun w => M (reflectMapOut g (m w)), hΩrect, ?_, fun w hw => (hgH w hw).2, ?_, ?_⟩
  · intro w hw
    obtain ⟨v, hmv, Gv, hGd, hGeq, -, -⟩ := hloc w hw
    have h1 : DifferentiableAt ℂ m w := by
      simp only [hm, mobAt]
      refine (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => ((0 : ℝ) : ℂ) * z + ((-1 : ℝ) : ℂ)) w).div
        (by fun_prop) ?_
      simp only [ofReal_one, one_mul, ofReal_neg]; rw [← sub_eq_add_neg]; exact hw0 w hw
    have h2 : DifferentiableAt ℂ (reflectMapOut g) (m w) :=
      (hGd.differentiableAt (isOpen_ball.mem_nhds hmv)).congr_of_eventuallyEq
        (Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hmv) fun z hz => hGeq hz)
    have h3 : DifferentiableAt ℂ M (reflectMapOut g (m w)) := by
      simp only [hM]
      exact (by fun_prop : DifferentiableAt ℂ (fun z : ℂ => (a : ℂ) * z + b) _).div (by fun_prop) (hden w hw)
    exact (h3.comp w (h2.comp w h1)).differentiableWithinAt
  · intro w hw
    simp only
    rw [hsymm w hw, hM, realMobius_conj]
  · intro w hw hw0'
    have hwr : w = ((w.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hw0'])
    obtain ⟨v, hmv, Gv, -, hGeq, -, hGreal⟩ := hloc w hw
    have hmr : (m w).im = 0 := by rw [hwr, hm, mobAt_ofReal]; exact ofReal_im _
    have hs : (reflectMapOut g (m w)).im = 0 := by rw [hGeq hmv]; exact hGreal _ hmv hmr
    simp only
    rw [show reflectMapOut g (m w) = (((reflectMapOut g (m w)).re : ℝ) : ℂ) from
      Complex.ext (by simp) (by simp [hs])]
    exact im_realMobius_ofReal _ _ _ _ _

/-- **The derivative of the reflected map is positive on the real axis.** A holomorphic `G` on the rectangle,
symmetric under conjugation, real on the real axis, mapping the upper half into `ℍ` and injective there, has real
positive derivative at every real point of the rectangle. -/
theorem deriv_pos_of_reflect {a b ρ : ℝ} {G : ℂ → ℂ} (hGd : DifferentiableOn ℂ G (rect a b ρ))
    (hGsymm : ∀ w ∈ rect a b ρ, G (conj w) = conj (G w))
    (hGreal : ∀ w ∈ rect a b ρ, w.im = 0 → (G w).im = 0)
    (hGH : ∀ w ∈ rect a b ρ ∩ H, G w ∈ H) (hGinj : InjOn G (rect a b ρ ∩ H)) :
    ∀ w ∈ rect a b ρ, w.im = 0 → (deriv G w).im = 0 ∧ 0 < (deriv G w).re := by
  set U := rect a b ρ with hU
  have hUo : IsOpen U := isOpen_rect a b ρ
  have hder : ∀ w ∈ U, HasDerivAt G (deriv G w) w := fun w hw =>
    ((hGd.differentiableAt (hUo.mem_nhds hw))).hasDerivAt
  -- (i) the derivative is real on the real axis
  have him : ∀ w ∈ U, w.im = 0 → (deriv G w).im = 0 := by
    intro w hw hw0
    have hcw : conj w = w := conj_eq_iff_im.2 hw0
    have h1 := (hder w hw).conj_conj
    rw [hcw] at h1
    have h2 : (conj ∘ G ∘ conj) =ᶠ[𝓝 w] G := by
      filter_upwards [hUo.mem_nhds hw] with z hz
      simp only [Function.comp, hGsymm z hz, conj_conj]
    have h3 := (h1.congr_of_eventuallyEq h2.symm).unique (hder w hw)
    have := congrArg Complex.im h3
    rw [conj_im] at this
    linarith
  -- (ii) its real part is nonnegative
  have hre : ∀ w ∈ U, w.im = 0 → 0 ≤ (deriv G w).re := by
    intro w hw hw0
    have hslope := (hasDerivAt_iff_tendsto_slope.1 (hder w hw))
    have hpath : Tendsto (fun ε : ℝ => w + ε * I) (𝓝[>] 0) (𝓝[≠] w) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : Tendsto (fun ε : ℝ => w + ε * I) (𝓝 0) (𝓝 (w + (0 : ℝ) * I)) :=
          ((continuous_const.add (continuous_ofReal.mul continuous_const)).tendsto 0)
        simpa using this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with ε hε
        simp only [mem_compl_iff, mem_singleton_iff, add_eq_left, mul_eq_zero, ofReal_eq_zero, I_ne_zero,
          or_false]
        exact ne_of_gt hε
    have hlim := (continuous_re.tendsto _).comp (hslope.comp hpath)
    refine ge_of_tendsto hlim ?_
    have hev : ∀ᶠ ε : ℝ in 𝓝[>] 0, w + ε * I ∈ U :=
      (hpath.mono_right nhdsWithin_le_nhds).eventually (hUo.mem_nhds hw)
    filter_upwards [hev, self_mem_nhdsWithin] with ε hεU hε
    have hεH : w + ε * I ∈ H := by show 0 < (w + ε * I).im; simp [hw0, mem_Ioi.1 hε]
    have hG := hGH _ ⟨hεU, hεH⟩
    have hGw := hGreal w hw hw0
    simp only [Function.comp, slope_def_field, add_sub_cancel_left]
    have hε0 : (ε : ℂ) ≠ 0 := ofReal_ne_zero.2 (ne_of_gt hε)
    rw [show (G (w + ε * I) - G w) / (ε * I) = -I * (G (w + ε * I) - G w) / ε by
      field_simp; ring_nf; rw [I_sq]; ring]
    rw [div_ofReal_re]
    simp only [mul_re, neg_re, I_re, neg_im, I_im, sub_re, sub_im, hGw]
    have : 0 < (G (w + ε * I)).im := hG
    exact div_nonneg (by nlinarith) (le_of_lt hε)
  -- (iii) `G` is injective on the rectangle
  have hlow : ∀ w ∈ U, w.im < 0 → (G w).im < 0 := by
    intro w hw hneg
    have hcw : conj w ∈ U ∩ H := ⟨conj_mem_rect hw, show 0 < (conj w).im by simp; linarith⟩
    have h1 := hGH _ hcw
    rw [hGsymm w hw] at h1
    have h1' : 0 < (conj (G w)).im := h1
    rw [conj_im] at h1'
    linarith
  have hmono : ∀ s₁ s₂ : ℝ, (s₁ : ℂ) ∈ U → (s₂ : ℂ) ∈ U → s₁ < s₂ → G s₁ ≠ G s₂ := by
    intro s₁ s₂ hs₁ hs₂ hlt heq
    set F : ℝ → ℝ := fun s => (G s).re with hF
    have hIoo : ∀ s ∈ Ioo s₁ s₂, (s : ℂ) ∈ U := fun s hs =>
      ⟨by simpa using hs₁.1.trans hs.1, by simpa using hs.2.trans hs₂.2.1, by simpa using hs₁.2.2⟩
    have hIcc : ∀ s ∈ Icc s₁ s₂, (s : ℂ) ∈ U := fun s hs =>
      ⟨by simpa using hs₁.1.trans_le hs.1, by simpa using hs.2.trans_lt hs₂.2.1, by simpa using hs₁.2.2⟩
    have hFd : ∀ s ∈ Icc s₁ s₂, HasDerivAt F (deriv G s).re s := fun s hs =>
      (hder _ (hIcc s hs)).real_of_complex
    have hFmono : MonotoneOn F (Icc s₁ s₂) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc s₁ s₂) (fun s hs => (hFd s hs).continuousAt.continuousWithinAt)
        (fun s hs => ?_) (fun s hs => ?_)
      · rw [interior_Icc] at hs
        exact (hFd s (Ioo_subset_Icc_self hs)).differentiableAt.differentiableWithinAt
      · rw [interior_Icc] at hs
        rw [(hFd s (Ioo_subset_Icc_self hs)).deriv]
        exact hre _ (hIoo s hs) (by simp)
    have hF12 : F s₁ = F s₂ := by simp only [hF, heq]
    have hconst : ∀ s ∈ Icc s₁ s₂, G s = G s₁ := by
      intro s hs
      have h1 := hFmono ⟨le_rfl, hlt.le⟩ hs hs.1
      have h2 := hFmono hs ⟨hlt.le, le_rfl⟩ hs.2
      have h2' : F s ≤ F s₁ := hF12 ▸ h2
      have hre' : (G s).re = (G s₁).re := le_antisymm h2' h1
      exact Complex.ext hre' (by rw [hGreal _ (hIcc s hs) (by simp), hGreal _ hs₁ (by simp)])
    have hana : AnalyticOnNhd ℂ G U := hGd.analyticOnNhd hUo
    have hfreq : ∃ᶠ z in 𝓝[≠] (s₁ : ℂ), G z = (fun _ => G s₁) z := by
      have hT : Tendsto (fun t : ℝ => ((s₁ + t : ℝ) : ℂ)) (𝓝[>] 0) (𝓝[≠] (s₁ : ℂ)) := by
        refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
        · have : Tendsto (fun t : ℝ => ((s₁ + t : ℝ) : ℂ)) (𝓝 0) (𝓝 ((s₁ + 0 : ℝ) : ℂ)) :=
            (continuous_ofReal.comp (continuous_const.add continuous_id)).tendsto 0
          simpa using this.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with t ht
          simp only [mem_compl_iff, mem_singleton_iff, ofReal_inj]
          linarith [mem_Ioi.1 ht]
      refine hT.frequently (Eventually.frequently ?_)
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < s₂ - s₁ by linarith)] with t ht
      exact hconst _ ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hEq := hana.eqOn_of_preconnected_of_frequently_eq analyticOnNhd_const
      ((convex_rect a b ρ).isPreconnected) hs₁ hfreq
    have hρ : 0 < ρ := (abs_nonneg _).trans_lt hs₁.2.2
    have hp₁ : (s₁ : ℂ) + (ρ / 2 : ℝ) * I ∈ U ∩ H :=
      ⟨⟨by simpa using hs₁.1, by simpa using hs₁.2.1, by simp [abs_of_pos (half_pos hρ)]; linarith⟩,
        show 0 < ((s₁ : ℂ) + (ρ / 2 : ℝ) * I).im by simp; linarith⟩
    have hp₂ : (s₂ : ℂ) + (ρ / 2 : ℝ) * I ∈ U ∩ H :=
      ⟨⟨by simpa using hs₂.1, by simpa using hs₂.2.1, by simp [abs_of_pos (half_pos hρ)]; linarith⟩,
        show 0 < ((s₂ : ℂ) + (ρ / 2 : ℝ) * I).im by simp; linarith⟩
    have h12 := hGinj hp₁ hp₂ (by rw [hEq hp₁.1, hEq hp₂.1])
    have := congrArg Complex.re h12
    simp at this
    linarith
  have hinj : InjOn G U := by
    intro w₁ hw₁ w₂ hw₂ heq
    rcases lt_trichotomy w₁.im 0 with h1 | h1 | h1 <;> rcases lt_trichotomy w₂.im 0 with h2 | h2 | h2
    · have hc1 : conj w₁ ∈ U ∩ H := ⟨conj_mem_rect hw₁, show 0 < (conj w₁).im by simp; linarith⟩
      have hc2 : conj w₂ ∈ U ∩ H := ⟨conj_mem_rect hw₂, show 0 < (conj w₂).im by simp; linarith⟩
      have := hGinj hc1 hc2 (by rw [hGsymm _ hw₁, hGsymm _ hw₂, heq])
      simpa using congrArg conj this
    · have := hlow w₁ hw₁ h1; rw [heq, hGreal w₂ hw₂ h2] at this; exact absurd this (lt_irrefl _)
    · have := hlow w₁ hw₁ h1; have h' := hGH w₂ ⟨hw₂, h2⟩; rw [← heq] at h'
      exact absurd (show 0 < (G w₁).im from h') (not_lt.2 this.le)
    · have := hlow w₂ hw₂ h2; rw [← heq, hGreal w₁ hw₁ h1] at this; exact absurd this (lt_irrefl _)
    · have hw₁r : w₁ = ((w₁.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [h1])
      have hw₂r : w₂ = ((w₂.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [h2])
      rcases lt_trichotomy w₁.re w₂.re with h | h | h
      · exact absurd (by rw [← hw₁r, ← hw₂r]; exact heq) (hmono _ _ (hw₁r ▸ hw₁) (hw₂r ▸ hw₂) h)
      · rw [hw₁r, hw₂r, h]
      · exact absurd (by rw [← hw₁r, ← hw₂r]; exact heq.symm) (hmono _ _ (hw₂r ▸ hw₂) (hw₁r ▸ hw₁) h)
    · have h' : 0 < (G w₂).im := hGH w₂ ⟨hw₂, h2⟩
      rw [← heq, hGreal w₁ hw₁ h1] at h'; exact absurd h' (lt_irrefl _)
    · have := hlow w₂ hw₂ h2; have h' := hGH w₁ ⟨hw₁, h1⟩; rw [heq] at h'
      exact absurd (show 0 < (G w₂).im from h') (not_lt.2 this.le)
    · have h' : 0 < (G w₁).im := hGH w₁ ⟨hw₁, h1⟩
      rw [heq, hGreal w₂ hw₂ h2] at h'; exact absurd h' (lt_irrefl _)
    · exact hGinj ⟨hw₁, h1⟩ ⟨hw₂, h2⟩ heq
  intro w hw hw0
  refine ⟨him w hw hw0, lt_of_le_of_ne (hre w hw hw0) fun h0 => ?_⟩
  have := QuantumZipper.CA.deriv_ne_zero_of_injOn hUo hGd hinj hw
  exact this (Complex.ext h0.symm (him w hw hw0))

/-- **A logarithm of `G'` near the segment.** If `G` is holomorphic on the rectangle with real positive derivative on
the real segment, then on a thinner rectangle `Log ∘ G'` is a holomorphic logarithm of `G'`, real on the real axis. -/
theorem exists_log_deriv {a b ρ : ℝ} (hab : a ≤ b) (hρ : 0 < ρ) {G : ℂ → ℂ}
    (hGd : DifferentiableOn ℂ G (rect a b ρ))
    (hpos : ∀ w ∈ rect a b ρ, w.im = 0 → (deriv G w).im = 0 ∧ 0 < (deriv G w).re) :
    ∃ ρ' > 0, ρ' ≤ ρ ∧ DifferentiableOn ℂ (fun w => Complex.log (deriv G w)) (rect a b ρ') ∧
      (∀ w ∈ rect a b ρ', Complex.exp (Complex.log (deriv G w)) = deriv G w) ∧
      ∀ w ∈ rect a b ρ', w.im = 0 → (Complex.log (deriv G w)).im = 0 := by
  have hUo := isOpen_rect a b ρ
  have hdd : DifferentiableOn ℂ (deriv G) (rect a b ρ) := (hGd.analyticOnNhd hUo).deriv.differentiableOn
  set S := {w | w ∈ rect a b ρ ∧ 0 < (deriv G w).re} with hS
  have hSo : IsOpen S := hdd.continuousOn.isOpen_inter_preimage hUo (isOpen_lt continuous_const continuous_re)
  have hK : IsCompact (((↑) : ℝ → ℂ) '' Icc a b) := isCompact_Icc.image continuous_ofReal
  have hKS : ((↑) : ℝ → ℂ) '' Icc a b ⊆ S := by
    rintro _ ⟨y, hy, rfl⟩
    have hyU : (y : ℂ) ∈ rect a b ρ := ⟨by simp; linarith [hy.1], by simp; linarith [hy.2], by simpa using hρ⟩
    exact ⟨hyU, (hpos _ hyU (by simp)).2⟩
  obtain ⟨δ, hδ, hδS⟩ := hK.exists_thickening_subset_open hSo hKS
  refine ⟨min (δ / 2) ρ, by positivity, min_le_right _ _, ?_, ?_, ?_⟩
  · have hsub : rect a b (min (δ / 2) ρ) ⊆ S := by
      intro w hw
      obtain ⟨y, hy, hwy⟩ := exists_near_of_mem_rect hab hw
      refine hδS (Metric.mem_thickening_iff.2 ⟨y, ⟨y, hy, rfl⟩, ?_⟩)
      rw [dist_eq_norm]
      linarith [min_le_left (δ / 2) ρ]
    intro w hw
    have hwS := hsub hw
    have hd : DifferentiableAt ℂ (deriv G) w := hdd.differentiableAt (hUo.mem_nhds hwS.1)
    exact (hd.clog (Or.inl hwS.2)).differentiableWithinAt
  · intro w hw
    have hwU : w ∈ rect a b ρ := rect_mono (min_le_right _ _) hw
    refine Complex.exp_log fun h0 => ?_
    obtain ⟨y, hy, hwy⟩ := exists_near_of_mem_rect hab hw
    have hwS : w ∈ S := hδS (Metric.mem_thickening_iff.2 ⟨y, ⟨y, hy, rfl⟩, by
      rw [dist_eq_norm]; linarith [min_le_left (δ / 2) ρ]⟩)
    have := hwS.2
    rw [h0, zero_re] at this
    exact lt_irrefl _ this
  · intro w hw hw0
    have hwU : w ∈ rect a b ρ := rect_mono (min_le_right _ _) hw
    obtain ⟨him, hre⟩ := hpos w hwU hw0
    rw [Complex.log_im, show deriv G w = (((deriv G w).re : ℝ) : ℂ) from
      Complex.ext (by simp) (by simp [him])]
    exact Complex.arg_ofReal_of_nonneg hre.le

end Aux10

end InteractingSLE
