/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import QuantumZipper.Proofs.Thm18.LWExc2Refl
import QuantumZipper.Proofs.Zipper.FieldLawlerSubExcGeo

/-!
# Odd reflection of real harmonic functions across the real axis

The local existence theorem is QuantumZipper's `harmReflectStmt_holds` (Ahlfors,
*Complex Analysis*, third edition, Chapter 4, §6.5, Theorem 24). We adapt its
extension to the explicit odd reflection `lwOddExt`, then localize on open sets.
The adapter uses Mathlib's harmonic conjugate on a ball and QuantumZipper's
holomorphic Schwarz reflection; no boundary regularity of a conjugate is assumed.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology Complex InnerProductSpace
open scoped ComplexConjugate

namespace InteractingSLE.Analysis.SchwarzHarmonic

open QuantumZipper (H Hbar)
open QuantumZipper.Thm18Asm.LWFar (lwOddExt harmReflectStmt_holds)

/-- QuantumZipper's odd reflection, with a short name for downstream cutoffs. -/
def oddReflection (u : ℂ → ℝ) : ℂ → ℝ := lwOddExt u

theorem oddReflection_of_nonneg {u : ℂ → ℝ} {z : ℂ} (hz : 0 ≤ z.im) :
    oddReflection u z = u z := by
  exact ite_eq_left hz

theorem oddReflection_of_neg {u : ℂ → ℝ} {z : ℂ} (hz : z.im < 0) :
    oddReflection u z = -u (conj z) := by
  exact ite_eq_right (not_le.mpr hz)

/-- A local harmonic extension can be chosen odd, using a holomorphic conjugate
of the already extended function and holomorphic Schwarz reflection. -/
theorem exists_odd_harmonic_extension_ball {u : ℂ → ℝ} {x r : ℝ} (hr : 0 < r)
    (hu : HarmonicOnNhd u (H ∩ ball (x : ℂ) r))
    (hc : ContinuousOn u (Hbar ∩ ball (x : ℂ) r))
    (hzero : ∀ z ∈ ball (x : ℂ) r, z.im = 0 → u z = 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ r ∧ ∃ v : ℂ → ℝ,
      HarmonicOnNhd v (ball (x : ℂ) ρ) ∧
      EqOn v u (Hbar ∩ ball (x : ℂ) ρ) ∧
      ∀ z ∈ ball (x : ℂ) ρ, v (conj z) = -v z := by
  obtain ⟨ρ, hρ, hρr, v, hv, hveq⟩ := harmReflectStmt_holds u x r hr hu hc hzero
  obtain ⟨F, hF, hFre⟩ := hv.exists_analyticOnNhd_ball_re_eq
  have hIF : AnalyticOnNhd ℂ (fun z => I * F z) (ball (x : ℂ) ρ) :=
    analyticOnNhd_const.mul hF
  obtain ⟨G, hG, hGeq, hGconj⟩ := QuantumZipper.CA.exists_reflection_extension
    (hIF.differentiableOn.mono inter_subset_right)
    (hIF.continuousOn.mono inter_subset_right) (fun z hz hzi => by
      simp only [mul_im, I_re, zero_mul, I_im, one_mul, zero_add]
      exact (hFre hz).trans ((hveq ⟨hzi.ge, hz⟩).trans
        (hzero z (ball_subset_ball hρr hz) hzi)))
  refine ⟨ρ, hρ, hρr, fun z => (G z).im, ?_, ?_, ?_⟩
  · intro z hz
    exact (hG.analyticOnNhd isOpen_ball z hz).harmonicAt_im
  · intro z hz
    change (G z).im = u z
    rw [hGeq hz]
    simp only [mul_im, I_re, zero_mul, I_im, one_mul, zero_add]
    exact (hFre hz.2).trans (hveq hz)
  · intro z hz
    change (G (conj z)).im = -(G z).im
    rw [hGconj z hz, conj_im]

/-- The explicit odd reflection is harmonic near the centre of a half-disc. -/
theorem exists_harmonicOnNhd_oddReflection_ball {u : ℂ → ℝ} {x r : ℝ} (hr : 0 < r)
    (hu : HarmonicOnNhd u (H ∩ ball (x : ℂ) r))
    (hc : ContinuousOn u (Hbar ∩ ball (x : ℂ) r))
    (hzero : ∀ z ∈ ball (x : ℂ) r, z.im = 0 → u z = 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ r ∧ HarmonicOnNhd (oddReflection u) (ball (x : ℂ) ρ) := by
  obtain ⟨ρ, hρ, hρr, v, hv, hveq, hvodd⟩ :=
    exists_odd_harmonic_extension_ball hr hu hc hzero
  have heq : EqOn v (oddReflection u) (ball (x : ℂ) ρ) := by
    intro z hz
    by_cases hzi : 0 ≤ z.im
    · rw [oddReflection_of_nonneg hzi]
      exact hveq ⟨hzi, hz⟩
    · have hcz : conj z ∈ Hbar ∩ ball (x : ℂ) ρ :=
        ⟨by change 0 ≤ (conj z).im; rw [conj_im]; exact neg_nonneg.mpr (not_le.mp hzi).le,
          QuantumZipper.CA.conj_mem_ball_ofReal hz⟩
      rw [oddReflection_of_neg (not_le.mp hzi), ← hveq hcz, hvodd z hz, neg_neg]
  refine ⟨ρ, hρ, hρr, fun z hz => ?_⟩
  apply (harmonicAt_congr_nhds (heq.eventuallyEq_of_mem (isOpen_ball.mem_nhds hz))).mp
  exact hv z hz

/-- Oddness at a point only uses the zero boundary value when the point is real. -/
theorem oddReflection_conj {u : ℂ → ℝ} {z : ℂ} (hzero : z.im = 0 → u z = 0) :
    oddReflection u (conj z) = -oddReflection u z := by
  rcases lt_trichotomy z.im 0 with hneg | heq | hpos
  · rw [oddReflection_of_neg hneg,
      oddReflection_of_nonneg (by rw [conj_im]; exact neg_nonneg.mpr hneg.le), neg_neg]
  · rw [conj_eq_iff_im.mpr heq, oddReflection_of_nonneg heq.ge, hzero heq, neg_zero]
  · rw [oddReflection_of_nonneg hpos.le,
      oddReflection_of_neg (by rw [conj_im]; exact neg_neg_of_pos hpos), conj_conj]

/-- Schwarz reflection on a conjugation-invariant open set. The input is harmonic
above the real axis, continuous up to it, and zero on its real part. -/
theorem harmonicOnNhd_oddReflection {u : ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U)
    (hconj : ∀ z ∈ U, conj z ∈ U) (hu : HarmonicOnNhd u (U ∩ H))
    (hc : ContinuousOn u (U ∩ Hbar)) (hzero : ∀ z ∈ U, z.im = 0 → u z = 0) :
    HarmonicOnNhd (oddReflection u) U := by
  intro z hz
  rcases lt_trichotomy z.im 0 with hneg | heq | hpos
  · have hcz : conj z ∈ U ∩ H :=
      ⟨hconj z hz, by change 0 < (conj z).im; rw [conj_im]; exact neg_pos.mpr hneg⟩
    have hh : HarmonicAt (fun w => -u (conj w)) z :=
      (QuantumZipper.FieldLawler.fl_harmonicAt_conj (hu _ hcz)).neg
    refine (harmonicAt_congr_nhds ?_).mpr hh
    filter_upwards [(isOpen_lt continuous_im continuous_const).mem_nhds hneg] with w hw
    exact oddReflection_of_neg hw
  · obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hU z hz
    have hzx : (z.re : ℂ) = z := Complex.ext (by simp only [ofReal_re])
      (by simp only [ofReal_im, heq])
    have hsub' : ball (z.re : ℂ) r ⊆ U := by rwa [hzx]
    obtain ⟨ρ, hρ, _, hρharm⟩ := exists_harmonicOnNhd_oddReflection_ball hr
      (hu.mono fun w hw => ⟨hsub' hw.2, hw.1⟩)
      (hc.mono fun w hw => ⟨hsub' hw.2, hw.1⟩)
      (fun w hw => hzero w (hsub' hw))
    exact hρharm z (by rw [← hzx]; exact mem_ball_self hρ)
  · refine (harmonicAt_congr_nhds ?_).mpr (hu z ⟨hz, hpos⟩)
    filter_upwards [QuantumZipper.isOpen_H.mem_nhds hpos] with w hw
    exact oddReflection_of_nonneg (show 0 ≤ w.im from hw.le)

/-- Odd reflection with value zero on the real axis, independently of the input's
values outside the upper half-plane. -/
def oddExtension (u : ℂ → ℝ) : ℂ → ℝ :=
  oddReflection (fun z => if 0 < z.im then u z else 0)

theorem oddExtension_of_pos {u : ℂ → ℝ} {z : ℂ} (hz : 0 < z.im) :
    oddExtension u z = u z := by
  rw [oddExtension, oddReflection_of_nonneg hz.le]
  exact ite_eq_left hz

theorem oddExtension_of_neg {u : ℂ → ℝ} {z : ℂ} (hz : z.im < 0) :
    oddExtension u z = -u (conj z) := by
  rw [oddExtension, oddReflection_of_neg hz]
  rw [ite_eq_left (by rw [conj_im]; exact neg_pos.mpr hz)]

theorem oddExtension_of_im_eq_zero {u : ℂ → ℝ} {z : ℂ} (hz : z.im = 0) :
    oddExtension u z = 0 := by
  rw [oddExtension, oddReflection_of_nonneg hz.ge]
  exact ite_eq_right (by rw [hz]; exact lt_irrefl 0)

theorem oddExtension_conj (u : ℂ → ℝ) (z : ℂ) :
    oddExtension u (conj z) = -oddExtension u z := by
  apply oddReflection_conj
  intro hz
  exact ite_eq_right (by rw [hz]; exact lt_irrefl 0)

/-- Schwarz reflection from boundary limits. No value or smoothness of `u` is
required on the real axis. -/
theorem harmonicOnNhd_oddExtension {u : ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U)
    (hconj : ∀ z ∈ U, conj z ∈ U) (hu : HarmonicOnNhd u (U ∩ H))
    (hlim : ∀ x : ℝ, (x : ℂ) ∈ U → Tendsto u (𝓝[U ∩ H] (x : ℂ)) (𝓝 0)) :
    HarmonicOnNhd (oddExtension u) U := by
  let v : ℂ → ℝ := fun z => if 0 < z.im then u z else 0
  have hvharm : HarmonicOnNhd v (U ∩ H) := by
    intro z hz
    apply (harmonicAt_congr_nhds ?_).mpr (hu z hz)
    filter_upwards [QuantumZipper.isOpen_H.mem_nhds hz.2] with w hw
    exact ite_eq_left (show 0 < w.im from hw)
  have hvzero : ∀ z : ℂ, z.im = 0 → v z = 0 := by
    intro z hz
    exact ite_eq_right (by rw [hz]; exact lt_irrefl 0)
  have hvc : ContinuousOn v (U ∩ Hbar) := by
    intro z hz
    by_cases hpos : 0 < z.im
    · exact (hvharm z ⟨hz.1, hpos⟩).1.continuousAt.continuousWithinAt
    · have hzi : z.im = 0 := le_antisymm (not_lt.mp hpos) hz.2
      have hzx : (z.re : ℂ) = z := Complex.ext (by simp only [ofReal_re])
        (by simp only [ofReal_im, hzi])
      have ht := hlim z.re (by rw [hzx]; exact hz.1)
      rw [hzx, Metric.tendsto_nhdsWithin_nhds] at ht
      rw [ContinuousWithinAt, hvzero z hzi, Metric.tendsto_nhdsWithin_nhds]
      intro ε hε
      obtain ⟨δ, hδ, hδu⟩ := ht ε hε
      refine ⟨δ, hδ, fun w hw hd => ?_⟩
      by_cases hwpos : 0 < w.im
      · change dist (if 0 < w.im then u w else 0) 0 < ε
        rw [ite_eq_left hwpos]
        exact hδu ⟨hw.1, hwpos⟩ hd
      · change dist (if 0 < w.im then u w else 0) 0 < ε
        rw [ite_eq_right hwpos, dist_self]
        exact hε
  exact harmonicOnNhd_oddReflection hU hconj hvharm hvc (fun z _ => hvzero z)

/-- The two half-planes joined through an open subset of the real axis. -/
def reflectionDomain (O : Set ℝ) : Set ℂ := {z | z.im ≠ 0 ∨ z.re ∈ O}

theorem isOpen_reflectionDomain {O : Set ℝ} (hO : IsOpen O) :
    IsOpen (reflectionDomain O) :=
  (isOpen_ne.preimage continuous_im).union (hO.preimage continuous_re)

theorem conj_mem_reflectionDomain {O : Set ℝ} {z : ℂ} (hz : z ∈ reflectionDomain O) :
    conj z ∈ reflectionDomain O := by
  change (conj z).im ≠ 0 ∨ (conj z).re ∈ O
  simpa only [reflectionDomain, mem_ofPred_eq, conj_im, ne_eq, neg_eq_zero, conj_re] using hz

theorem ofReal_mem_reflectionDomain {O : Set ℝ} {x : ℝ} :
    (x : ℂ) ∈ reflectionDomain O ↔ x ∈ O := by
  change (x : ℂ).im ≠ 0 ∨ (x : ℂ).re ∈ O ↔ x ∈ O
  simp only [ofReal_im, ne_self_iff_false, false_or, ofReal_re]

theorem upperHalfPlane_union_real_subset_reflectionDomain (O : Set ℝ) :
    H ∪ Complex.ofReal '' O ⊆ reflectionDomain O := by
  intro z hz
  rcases hz with hz | ⟨x, hx, rfl⟩
  · exact Or.inl (ne_of_gt hz)
  · exact ofReal_mem_reflectionDomain.mpr hx

/-- The half-plane form needed for an odd cutoff: any real open window with
zero boundary limits admits the explicit harmonic odd extension across it. -/
theorem harmonicOnNhd_oddExtension_halfPlane {u : ℂ → ℝ} {O : Set ℝ}
    (hO : IsOpen O) (hu : HarmonicOnNhd u H)
    (hlim : ∀ x ∈ O, Tendsto u (𝓝[H] (x : ℂ)) (𝓝 0)) :
    HarmonicOnNhd (oddExtension u) (reflectionDomain O) := by
  apply harmonicOnNhd_oddExtension (isOpen_reflectionDomain hO)
    (fun _ hz => conj_mem_reflectionDomain hz) (hu.mono inter_subset_right)
  intro x hx
  exact (hlim x (ofReal_mem_reflectionDomain.mp hx)).mono_left
    (nhdsWithin_mono _ inter_subset_right)

/-- An open harmonic neighbourhood of the half-plane and its zero-boundary
window, together with one globally odd extension agreeing with the original
function on the half-plane. -/
theorem exists_harmonic_odd_extension {u : ℂ → ℝ} {O : Set ℝ}
    (hO : IsOpen O) (hu : HarmonicOnNhd u H)
    (hlim : ∀ x ∈ O, Tendsto u (𝓝[H] (x : ℂ)) (𝓝 0)) :
    ∃ (U : Set ℂ) (v : ℂ → ℝ), IsOpen U ∧ H ∪ Complex.ofReal '' O ⊆ U ∧
      HarmonicOnNhd v U ∧ EqOn v u H ∧ ∀ z, v (conj z) = -v z := by
  refine ⟨reflectionDomain O, oddExtension u, isOpen_reflectionDomain hO,
    upperHalfPlane_union_real_subset_reflectionDomain O,
    harmonicOnNhd_oddExtension_halfPlane hO hu hlim, ?_, oddExtension_conj u⟩
  intro z hz
  exact oddExtension_of_pos hz

end InteractingSLE.Analysis.SchwarzHarmonic
