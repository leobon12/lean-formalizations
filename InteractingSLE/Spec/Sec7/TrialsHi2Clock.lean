/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.ContinuityProb7Clock
import InteractingSLE.Spec.Sec7.TrialsHiBand
import InteractingSLE.Stochastic.Martingale.OptionalSampling

/-!
# Aux. lemma 101 for the bands: the finite angular clock on an infinite one-sided phase

Packet PROVE-TRIALS-HI2. Specification pp. 346–348, Aux. lemma 101: "On an interval during which the driver stays
on one side of that midpoint, the angular clock `∫ D^{-2}` has finite terminal value almost surely. No restriction on
the two total weights is needed."

The proof replaces the source's Brownian increments by PROVE-SEC7-C7's Lyapunov method. On the band `U ≤ 7/8` the
drift term `b/(1 − U)` of `U` is bounded by `8|b|`, so for `f = −cosh(λ(u − c))` (`c ∈ {0, 1}` according to the sign of
`a = 2 + Σρ^L`) and `λ` large, `f'(a/u − b/(1 − u)) + (κ/2) f'' ≤ −λ` there (`exists_lyap_low`; the band `U ≥ 1/8` by
the reflection `lyapGen_reflect`). The localized Itô martingale of `f(U)` (`Clock.martingale_angLoc`) is sampled at the
constant time `q` and at the first band exit after `q` (`bandExit`, a first meeting time), by optional sampling for
continuous martingales; with the pathwise error bound (P4) this bounds `E ∫_q^{exit ∧ σ_n} D^{-2}` uniformly in `n`, and
Fatou's lemma concludes on the event that the band is never left after `q` (`ae_bddAbove_clock_of_band`). A countable
union over `q` gives Aux. lemma 101 for eventual bands (`aux101BandClockStatement`).

## Main results

* `lyapGen_reflect`, `exists_lyap_low`, `exists_lyap_high`;
* `bandLevTest`, `bandExit`, `isStoppingTime_bandExit`;
* `ae_bddAbove_clock_of_band`;
* **`aux101BandClockStatement`**: `TrialsHi.Aux101BandClockStatement κ` for every `κ > 0`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Sec7

namespace TrialsHi2

open Zhan Clock ZhanGT4

/-! ### The Lyapunov inequality on a band -/

section Lyap

/-- The Lyapunov generator is invariant under the reflection `u ↦ 1 − u`, `c ↦ 1 − c`, `(a, b) ↦ (b, a)`. -/
theorem lyapGen_reflect (κ a b lam c u : ℝ) :
    lyapGen κ a b lam c u = lyapGen κ b a lam (1 - c) (1 - u) := by
  have h1 : lam * (1 - u - (1 - c)) = -(lam * (u - c)) := by ring
  simp only [lyapGen, lyapF', lyapF'', angDrift, h1, Real.sinh_neg, Real.cosh_neg]
  ring

/-- **The Lyapunov inequality on the band `u ≤ 7/8`** (every `a, b`): there are `λ ≥ 0`, `c ∈ [0, 1]`, `c₀ > 0` with
`f'(u)(a/u − b/(1 − u)) + (κ/2) f''(u) ≤ −c₀` for `0 < u ≤ 7/8`. -/
theorem exists_lyap_low {κ : ℝ} (hκ : 0 < κ) (a b : ℝ) :
    ∃ lam c c₀ : ℝ, 0 ≤ lam ∧ c ∈ Icc (0 : ℝ) 1 ∧ 0 < c₀ ∧
      ∀ u ∈ Ioo (0 : ℝ) 1, u ≤ 7 / 8 → lyapGen κ a b lam c u ≤ -c₀ := by
  set lam := (16 * |b| + 2) / κ with hlamdef
  have hlam0 : 0 < lam := by positivity
  have hkl : κ / 2 * lam = 8 * |b| + 1 := by rw [hlamdef]; field_simp; ring
  -- the bound of the `b`-term on the band
  have hbt : ∀ u : ℝ, u ≤ 7 / 8 → ∀ S : ℝ, |S * (b / (1 - u))| ≤ 8 * |b| * |S| := by
    intro u hu S
    have hu1 : 1 / 8 ≤ 1 - u := by linarith
    rw [abs_mul, abs_div, abs_of_pos (by linarith : (0 : ℝ) < 1 - u)]
    have : |b| / (1 - u) ≤ 8 * |b| := by
      rw [div_le_iff₀ (by linarith)]; nlinarith [abs_nonneg b]
    nlinarith [abs_nonneg S, mul_le_mul_of_nonneg_left this (abs_nonneg S)]
  rcases le_total 0 a with ha | ha
  · refine ⟨lam, 0, lam, hlam0.le, ⟨le_rfl, zero_le_one⟩, hlam0, fun u hu hu8 => ?_⟩
    set S := Real.sinh (lam * (u - 0))
    set C := Real.cosh (lam * (u - 0))
    have hS : 0 ≤ S := Real.sinh_nonneg_iff.2 (mul_nonneg hlam0.le (by linarith [hu.1]))
    have hC := Real.one_le_cosh (lam * (u - 0))
    have hSC : |S| ≤ C := abs_sinh_le_cosh _
    have hau : 0 ≤ a / u := div_nonneg ha hu.1.le
    have hb := hbt u hu8 S
    have hb' : S * (b / (1 - u)) ≤ 8 * |b| * C :=
      (le_abs_self _).trans (hb.trans (mul_le_mul_of_nonneg_left hSC (by positivity)))
    simp only [lyapGen, lyapF', lyapF'', angDrift]
    have h2 : κ / 2 * -(lam ^ 2 * C) = -(lam * C * (8 * |b| + 1)) := by rw [← hkl]; ring
    rw [h2]
    nlinarith [mul_nonneg hS hau, mul_le_mul_of_nonneg_left hb' hlam0.le, mul_le_mul_of_nonneg_left hC hlam0.le]
  · refine ⟨lam, 1, lam, hlam0.le, ⟨zero_le_one, le_rfl⟩, hlam0, fun u hu hu8 => ?_⟩
    set S := Real.sinh (lam * (u - 1))
    set C := Real.cosh (lam * (u - 1))
    have hS : S ≤ 0 := by
      have : ¬ 0 < S := fun h => absurd (Real.sinh_pos_iff.1 h)
        (not_lt.2 (mul_nonpos_of_nonneg_of_nonpos hlam0.le (by linarith [hu.2])))
      linarith [not_lt.1 this]
    have hC := Real.one_le_cosh (lam * (u - 1))
    have hSC : |S| ≤ C := abs_sinh_le_cosh _
    have hau : a / u ≤ 0 := div_nonpos_of_nonpos_of_nonneg ha hu.1.le
    have hb := hbt u hu8 S
    have hb' : S * (b / (1 - u)) ≤ 8 * |b| * C :=
      (le_abs_self _).trans (hb.trans (mul_le_mul_of_nonneg_left hSC (by positivity)))
    simp only [lyapGen, lyapF', lyapF'', angDrift]
    have h2 : κ / 2 * -(lam ^ 2 * C) = -(lam * C * (8 * |b| + 1)) := by rw [← hkl]; ring
    rw [h2]
    nlinarith [mul_nonneg (neg_nonneg.2 hS) (neg_nonneg.2 hau), mul_le_mul_of_nonneg_left hb' hlam0.le,
      mul_le_mul_of_nonneg_left hC hlam0.le]

/-- **The Lyapunov inequality on the band `u ≥ 1/8`** (every `a, b`), by reflection. -/
theorem exists_lyap_high {κ : ℝ} (hκ : 0 < κ) (a b : ℝ) :
    ∃ lam c c₀ : ℝ, 0 ≤ lam ∧ c ∈ Icc (0 : ℝ) 1 ∧ 0 < c₀ ∧
      ∀ u ∈ Ioo (0 : ℝ) 1, 1 / 8 ≤ u → lyapGen κ a b lam c u ≤ -c₀ := by
  obtain ⟨lam, c, c₀, hlam, hc, hc₀, h⟩ := exists_lyap_low hκ b a
  refine ⟨lam, 1 - c, c₀, hlam, ⟨by linarith [hc.2], by linarith [hc.1]⟩, hc₀, fun u hu hu8 => ?_⟩
  rw [lyapGen_reflect]
  have e : 1 - (1 - c) = c := by ring
  rw [e]
  exact h (1 - u) ⟨by linarith [hu.2], by linarith [hu.1]⟩ (by linarith)

end Lyap

/-! ### The first band exit after a deterministic time -/

section Exit

variable {nL nR : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **The band test after `q`**: `max(lev(W, V^{L,0}, V^{R,0}), q − t)`, nonpositive exactly when `t ≥ q` and the band
level is `≤ 0`. -/
def bandLevTest (lev : ℝ × ℝ × ℝ → ℝ) (q : ℝ≥0) (W : ℝ≥0 → Ω → ℝ) (VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ)
    (VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ) : ℝ≥0 → Ω → ℝ :=
  fun t ω => max (lev (W t ω, VL 0 t ω, VR 0 t ω)) ((q : ℝ) - t)

/-- **The first band exit after `q`**: the first time `t ≥ q` before the lifetime with `lev ≤ 0` (the lifetime if
there is none), `0` on the set `N`. -/
def bandExit (N : Set Ω) (ζ : Ω → ℝ≥0∞) (lev : ℝ × ℝ × ℝ → ℝ) (q : ℝ≥0) (W : ℝ≥0 → Ω → ℝ)
    (VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ) (VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ≥0∞ :=
  zeroOn N (firstMeet zeroProc (bandLevTest lev q W VL VR) ζ) ω

variable {N : Set Ω} {ζ : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ} {VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ}
  {VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ} {lev : ℝ × ℝ × ℝ → ℝ}

theorem continuousOn_bandLevTest (hlev : Continuous lev) {ω : Ω}
    (hW : ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hL : ContinuousOn (fun t => VL 0 t ω) {t | (t : ℝ≥0∞) < ζ ω})
    (hR : ContinuousOn (fun t => VR 0 t ω) {t | (t : ℝ≥0∞) < ζ ω}) (q : ℝ≥0) :
    ContinuousOn (fun t => bandLevTest lev q W VL VR t ω - zeroProc t ω) {t | (t : ℝ≥0∞) < ζ ω} := by
  simp only [bandLevTest, zeroProc, sub_zero]
  exact continuous_max.comp_continuousOn ((hlev.comp_continuousOn (hW.prodMk (hL.prodMk hR))).prodMk
    (continuousOn_const.sub NNReal.continuous_coe.continuousOn))

/-- **The band exit is a stopping time** (in a filtration where `N` is measurable at every time). -/
theorem isStoppingTime_bandExit {𝓖 : Filtration ℝ≥0 mΩ} (hlev : Continuous lev) (hW : AdaptedBefore 𝓖 ζ W)
    (hL : AdaptedBefore 𝓖 ζ (VL 0)) (hR : AdaptedBefore 𝓖 ζ (VR 0)) (hN : ∀ t, MeasurableSet[𝓖 t] N)
    (hc : ∀ ω ∉ N, ContinuousOn (fun t => W t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧
      ContinuousOn (fun t => VL 0 t ω) {t | (t : ℝ≥0∞) < ζ ω} ∧
      ContinuousOn (fun t => VR 0 t ω) {t | (t : ℝ≥0∞) < ζ ω}) (q : ℝ≥0) :
    IsStoppingTime 𝓖 fun ω => (bandExit N ζ lev q W VL VR ω : WithTop ℝ≥0) := by
  have hYa : AdaptedBefore 𝓖 ζ (bandLevTest lev q W VL VR) :=
    adaptedBefore_of_eq (fun t p => max (lev p) ((q : ℝ) - t)) (fun t => by fun_prop) hW hL hR fun t ω => rfl
  have hZa : AdaptedBefore 𝓖 ζ (zeroProc (Ω := Ω)) :=
    adaptedBefore_of_eq (fun _ _ => 0) (fun _ => measurable_const) hW hL hR fun _ _ => rfl
  exact isStoppingTime_firstMeet_off hZa hYa hN fun ω hω =>
    continuousOn_bandLevTest hlev (hc ω hω).1 (hc ω hω).2.1 (hc ω hω).2.2 q

/-- Before the band exit and after `q`, the band level is positive. -/
theorem pos_of_lt_bandExit {ω : Ω} (hω : ω ∉ N) {q t : ℝ≥0} (hqt : q ≤ t)
    (ht : (t : ℝ≥0∞) < bandExit N ζ lev q W VL VR ω) : 0 < lev (W t ω, VL 0 t ω, VR 0 t ω) := by
  rw [bandExit, zeroOn_of_notMem hω] at ht
  have h := (lt_of_lt_firstMeet ht).2
  simp only [bandLevTest, zeroProc, lt_max_iff] at h
  rcases h with h | h
  · exact h
  · exact absurd h (not_lt.2 (sub_nonpos.2 (NNReal.coe_le_coe.2 hqt)))

/-- If the band level stays positive after `q`, the band exit is the lifetime. -/
theorem bandExit_eq_of_pos {ω : Ω} (hω : ω ∉ N) {q : ℝ≥0}
    (h : ∀ t : ℝ≥0, q ≤ t → 0 < lev (W t ω, VL 0 t ω, VR 0 t ω)) : bandExit N ζ lev q W VL VR ω = ζ ω := by
  rw [bandExit, zeroOn_of_notMem hω]
  refine le_antisymm firstMeet_le_lifetime (le_inf le_rfl (le_iInf₂ fun t ht => absurd ht.2 (not_le.2 ?_)))
  simp only [bandLevTest, zeroProc, lt_max_iff]
  by_cases hqt : q ≤ t
  · exact Or.inl (h t hqt)
  · exact Or.inr (sub_pos.2 (NNReal.coe_lt_coe.2 (not_le.1 hqt)))

end Exit

/-- The sampling time `max(q, min(x, n))` is finite, at least `q`, at most `n`, and below `x` after `q`. -/
theorem max_min_eq_coe (x : WithTop ℝ≥0) {q n : ℝ≥0} (hqn : q ≤ n) :
    ∃ r : ℝ≥0, max (min x (n : WithTop ℝ≥0)) (q : WithTop ℝ≥0) = r ∧ q ≤ r ∧ r ≤ n ∧
      (∀ s : ℝ≥0, q ≤ s → s < r → (s : WithTop ℝ≥0) < x) ∧ (x = ⊤ → r = n) := by
  induction x using WithTop.recTopCoe with
  | top =>
    refine ⟨n, ?_, hqn, le_rfl, fun s _ _ => WithTop.coe_lt_top s, fun _ => rfl⟩
    rw [min_eq_right le_top, max_eq_left (by exact_mod_cast hqn)]
  | coe y =>
    refine ⟨max (min y n) q, ?_, le_max_right _ _, max_le (min_le_right _ _) hqn, fun s hqs hsr => ?_,
      fun h => absurd h WithTop.coe_ne_top⟩
    · push_cast; rfl
    · have hs : s < min y n := by
        rcases lt_max_iff.1 hsr with h | h
        · exact h
        · exact absurd hqs (not_le.2 h)
      exact_mod_cast hs.trans_le (min_le_left _ _)

/-! ### The generator bound on a band, along one path -/

section Path

variable {nL nR : ℕ} {κ : ℝ} {xL : Fin (nL + 1) → ℝ} {xR : Fin (nR + 1) → ℝ} {ρL : Fin (nL + 1) → ℝ}
  {ρR : Fin (nR + 1) → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin (nL + 1) → ℝ≥0 → ℝ} {vR : Fin (nR + 1) → ℝ≥0 → ℝ}
  {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- **The pathwise generator bound at a band time** (PROVE-SEC7-C7's `Clock.genExpr_le`, with the Lyapunov inequality
assumed at the current angular coordinate only). -/
theorem genExpr_le_of_lyapGen (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ) (hx : 0 < xR 0 - xL 0)
    {lam c c₀ : ℝ} (hlam : 0 ≤ lam) (hc : c ∈ Icc (0 : ℝ) 1) {s : ℝ} (hs : (s.toNNReal : ℝ≥0∞) < ζ)
    (hL0 : vL 0 s.toNNReal < w s.toNNReal) (hR0 : w s.toNNReal < vR 0 s.toNNReal)
    (hlg : lyapGen κ (2 + ∑ i, ρL i) (2 + ∑ j, ρR j) lam c (angAt w vL vR s.toNNReal) ≤ -c₀) :
    genExpr κ ρL ρR (lyapF' lam c) (lyapF'' lam c) w vL vR s ≤
      -c₀ * (vR 0 s.toNNReal - vL 0 s.toNNReal)⁻¹ ^ 2 +
        lam * Real.cosh lam / (xR 0 - xL 0) * errAbs ρL ρR w vL vR s := by
  have hF := hp.isForcePath
  set t := s.toNNReal
  have hD : 0 < gapAt vL vR t := sub_pos.2 (hL0.trans hR0)
  have hDx : xR 0 - xL 0 ≤ gapAt vL vR t := le_gapAt hp hs
  have hU : angAt w vL vR t ∈ Ioo (0 : ℝ) 1 := by
    refine ⟨div_pos (sub_pos.2 hL0) hD, (div_lt_one hD).2 ?_⟩
    simp only [gapAt]; linarith
  have hnum : numAt ρL ρR w vL vR t / gapAt vL vR t =
      angDrift (2 + ∑ i, ρL i) (2 + ∑ j, ρR j) (angAt w vL vR t) / gapAt vL vR t ^ 2 +
        angErr ρL ρR (w t) (fun i => vL i t) (fun j => vR j t) / gapAt vL vR t := by
    have h := drift_angU_eq ρL ρR (w := w t) (vL := fun i => vL i t) (vR := fun j => vR j t) hL0 hR0 0
    rw [driftLin₀_angDens] at h
    simpa only [numAt, angAt, gapAt, angDens] using h
  have hE := abs_angErr_le (ρL := ρL) (ρR := ρR) hL0 hR0 (hF.antitone_vL hs) (hF.monotone_vR hs)
  have hEn := errAbs_nonneg (ρL := ρL) (ρR := ρR) hL0 hR0 (hF.antitone_vL hs) (hF.monotone_vR hs)
  have hf' := abs_lyapF'_le hlam hc ⟨hU.1.le, hU.2.le⟩
  simp only [genExpr]
  rw [hnum]
  set U := angAt w vL vR t
  set D := gapAt vL vR t
  set E := angErr ρL ρR (w t) (fun i => vL i t) (fun j => vR j t)
  have herr : errAbs ρL ρR w vL vR s = (∑ i, |ρL i| * ((w t - vL 0 t)⁻¹ - (w t - vL i t)⁻¹)) +
      ∑ j, |ρR j| * ((vR 0 t - w t)⁻¹ - (vR j t - w t)⁻¹) := rfl
  rw [herr]
  set A := (∑ i, |ρL i| * ((w t - vL 0 t)⁻¹ - (w t - vL i t)⁻¹)) +
      ∑ j, |ρR j| * ((vR 0 t - w t)⁻¹ - (vR j t - w t)⁻¹)
  have hDinv : (vR 0 t - vL 0 t)⁻¹ ^ 2 = 1 / D ^ 2 := by simp only [D, gapAt]; rw [inv_pow, one_div]
  rw [hDinv]
  have hmain : lyapF' lam c U * (angDrift (2 + ∑ i, ρL i) (2 + ∑ j, ρR j) U / D ^ 2) +
      κ / 2 * lyapF'' lam c U / D ^ 2 = lyapGen κ (2 + ∑ i, ρL i) (2 + ∑ j, ρR j) lam c U / D ^ 2 := by
    simp only [lyapGen]; ring
  have hmain' : lyapGen κ (2 + ∑ i, ρL i) (2 + ∑ j, ρR j) lam c U / D ^ 2 ≤ -c₀ * (1 / D ^ 2) := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_right hlg (by positivity)
  have herr' : lyapF' lam c U * (E / D) ≤ lam * Real.cosh lam / (xR 0 - xL 0) * A := by
    calc lyapF' lam c U * (E / D) ≤ |lyapF' lam c U * (E / D)| := le_abs_self _
      _ = |lyapF' lam c U| * |E| / D := by rw [abs_mul, abs_div, abs_of_pos hD]; ring
      _ ≤ lam * Real.cosh lam * A / (xR 0 - xL 0) := by
          rw [div_le_div_iff₀ hD hx]
          have h1 : |lyapF' lam c U| * |E| ≤ lam * Real.cosh lam * A :=
            mul_le_mul hf' hE (abs_nonneg _) (by positivity)
          nlinarith [mul_le_mul_of_nonneg_left hDx (by positivity : (0 : ℝ) ≤ lam * Real.cosh lam * A),
            abs_nonneg (lyapF' lam c U), abs_nonneg E]
      _ = lam * Real.cosh lam / (xR 0 - xL 0) * A := by ring
  have hsplit : lyapF' lam c U * (angDrift (2 + ∑ i, ρL i) (2 + ∑ j, ρR j) U / D ^ 2 + E / D) +
      κ / 2 * lyapF'' lam c U / D ^ 2 = (lyapF' lam c U * (angDrift (2 + ∑ i, ρL i) (2 + ∑ j, ρR j) U / D ^ 2) +
      κ / 2 * lyapF'' lam c U / D ^ 2) + lyapF' lam c U * (E / D) := by ring
  rw [hsplit, hmain]
  linarith

/-- **The integrated generator bound on a band interval** `[s₁, s₂]`, `s₂ < ζ`: if the Lyapunov inequality holds at
the non-collision times of `(s₁, s₂)`, then `∫_{s₁}^{s₂} genExpr ≤ −c₀ ∫_{s₁}^{s₂} D^{-2} + (λ cosh λ / D₀) K₁`. -/
theorem integral_genExpr_le_band (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ) (hx : 0 < xR 0 - xL 0)
    {lam c c₀ : ℝ} (hlam : 0 ≤ lam) (hc : c ∈ Icc (0 : ℝ) 1) {s₁ s₂ : ℝ≥0} (h12 : s₁ ≤ s₂)
    (hs₂ : (s₂ : ℝ≥0∞) < ζ)
    (hband : ∀ s : ℝ, (s₁ : ℝ) < s → s < s₂ → vL 0 s.toNNReal < w s.toNNReal → w s.toNNReal < vR 0 s.toNNReal →
      lyapGen κ (2 + ∑ i, ρL i) (2 + ∑ j, ρR j) lam c (angAt w vL vR s.toNNReal) ≤ -c₀) :
    ∫ s in (s₁ : ℝ)..s₂, genExpr κ ρL ρR (lyapF' lam c) (lyapF'' lam c) w vL vR s ≤
      -c₀ * (∫ s in (s₁ : ℝ)..s₂, (vR 0 s.toNNReal - vL 0 s.toNNReal)⁻¹ ^ 2) +
        lam * Real.cosh lam / (xR 0 - xL 0) * errK xL xR ρL ρR := by
  have hF := hp.isForcePath
  have h12' : (s₁ : ℝ) ≤ s₂ := by exact_mod_cast h12
  have hcont' : Continuous (lyapF' lam c) := continuous_iff_continuousAt.2 fun u =>
    (hasDerivAt_lyapF' lam c u).continuousAt
  have hcont'' : Continuous (lyapF'' lam c) := by unfold lyapF''; fun_prop
  have hsub : uIcc (s₁ : ℝ) s₂ ⊆ uIcc 0 (s₂ : ℝ) := by
    rw [uIcc_of_le h12', uIcc_of_le s₂.coe_nonneg]; exact Icc_subset_Icc_left s₁.coe_nonneg
  have hgi0 := intervalIntegrable_genExpr hp hx hcont' hcont'' hs₂ (ρL := ρL) (ρR := ρR)
  have hci0 := intervalIntegrable_clockRate hp hx hs₂
  have hei0 := intervalIntegrable_errAbs hp hs₂ (ρL := ρL) (ρR := ρR)
  have hgi := hgi0.mono_set hsub
  have hci := hci0.mono_set hsub
  have hei := hei0.mono_set hsub
  have hK : 0 ≤ lam * Real.cosh lam / (xR 0 - xL 0) := by
    have := Real.cosh_pos lam; positivity
  have hnc := ae_not_collision hF hs₂
  -- nonnegativity of the error rate at non-collision times
  have hpos : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Ioc 0 (s₂ : ℝ) → 0 ≤ errAbs ρL ρR w vL vR s := by
    filter_upwards [hnc] with s hs hsI
    obtain ⟨hL, hR⟩ := hs hsI
    have hsζ := Sec2.toNNReal_lt_of_mem_Icc hs₂ (Ioc_subset_Icc_self hsI)
    exact errAbs_nonneg (ρL := ρL) (ρR := ρR) (lt_of_le_of_ne (hF.vL_le_w hsζ 0) (hL 0))
      (lt_of_le_of_ne (hF.w_le_vR hsζ 0) (Ne.symm (hR 0))) (hF.antitone_vL hsζ) (hF.monotone_vR hsζ)
  have herr : ∫ s in (s₁ : ℝ)..s₂, errAbs ρL ρR w vL vR s ≤ errK xL xR ρL ρR := by
    have hsum := intervalIntegral.integral_add_adjacent_intervals (hei0.mono_set (by
      rw [uIcc_of_le s₁.coe_nonneg, uIcc_of_le s₂.coe_nonneg]; exact Icc_subset_Icc_right h12')) hei
    have h0 : 0 ≤ ∫ s in (0 : ℝ)..s₁, errAbs ρL ρR w vL vR s := by
      refine intervalIntegral.integral_nonneg_of_ae_restrict s₁.coe_nonneg ?_
      rw [EventuallyLE, ae_restrict_iff' measurableSet_Icc]
      have h0' : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ 0 := Measure.ae_ne volume 0
      filter_upwards [hpos, h0'] with s hs hs0 hsI
      exact hs ⟨lt_of_le_of_ne hsI.1 (Ne.symm hs0), hsI.2.trans h12'⟩
    linarith [integral_errAbs_le hp hs₂ (ρL := ρL) (ρR := ρR)]
  calc ∫ s in (s₁ : ℝ)..s₂, genExpr κ ρL ρR (lyapF' lam c) (lyapF'' lam c) w vL vR s
      ≤ ∫ s in (s₁ : ℝ)..s₂, (-c₀ * (vR 0 s.toNNReal - vL 0 s.toNNReal)⁻¹ ^ 2 +
          lam * Real.cosh lam / (xR 0 - xL 0) * errAbs ρL ρR w vL vR s) := by
        refine intervalIntegral.integral_mono_ae_restrict h12' hgi ((hci.const_mul _).add (hei.const_mul _)) ?_
        rw [EventuallyLE, ae_restrict_iff' measurableSet_Icc]
        have h1 : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ (s₁ : ℝ) := Measure.ae_ne volume _
        have h2 : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ (s₂ : ℝ) := Measure.ae_ne volume _
        have h0 : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ 0 := Measure.ae_ne volume 0
        filter_upwards [hnc, h0, h1, h2] with s hs hs0 hs1 hs2 hsI
        have hs1' : (s₁ : ℝ) < s := lt_of_le_of_ne hsI.1 (Ne.symm hs1)
        have hs2' : s < s₂ := lt_of_le_of_ne hsI.2 hs2
        have hsI' : s ∈ Ioc 0 (s₂ : ℝ) := ⟨s₁.coe_nonneg.trans_lt hs1', hsI.2⟩
        obtain ⟨hL, hR⟩ := hs hsI'
        have hsζ := Sec2.toNNReal_lt_of_mem_Icc hs₂ (Ioc_subset_Icc_self hsI')
        have hL0 := lt_of_le_of_ne (hF.vL_le_w hsζ 0) (hL 0)
        have hR0 := lt_of_le_of_ne (hF.w_le_vR hsζ 0) (Ne.symm (hR 0))
        exact genExpr_le_of_lyapGen hp hx hlam hc hsζ hL0 hR0 (hband s hs1' hs2' hL0 hR0)
    _ = -c₀ * (∫ s in (s₁ : ℝ)..s₂, (vR 0 s.toNNReal - vL 0 s.toNNReal)⁻¹ ^ 2) +
          lam * Real.cosh lam / (xR 0 - xL 0) * ∫ s in (s₁ : ℝ)..s₂, errAbs ρL ρR w vL vR s := by
        rw [intervalIntegral.integral_add (hci.const_mul _) (hei.const_mul _),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    _ ≤ _ := by nlinarith

end Path

/-! ### The localized Lyapunov martingale -/

section Mart

variable {nL nR : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {κ : ℝ}
  {xL : Fin (nL + 1) → ℝ} {xR : Fin (nR + 1) → ℝ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ} {VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {G : Set Ω} {T : ℕ → Ω → ℝ≥0}

/-- **The localized Lyapunov martingale** `f(U_{t∧σ_n}) − ∫₀^{t∧σ_n} itoGen (f ∘ U)` (no extra coordinate). -/
def lyapMart (κ : ℝ) (xL : Fin (nL + 1) → ℝ) (xR : Fin (nR + 1) → ℝ) (ρL : Fin (nL + 1) → ℝ)
    (ρR : Fin (nR + 1) → ℝ) (G : Set Ω) (T : ℕ → Ω → ℝ≥0) (W : ℝ≥0 → Ω → ℝ) (VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ)
    (VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (lam c : ℝ) (n : ℕ) (t : ℝ≥0)
    (ω : Ω) : ℝ :=
  (fun p => lyapF lam c (angU κ xL xR ρL ρR p))
      (coordA xL xR G VL VR (fun _ _ => 0) (min t (angLoc G T W VL VR B ζ n ω)) ω,
        Sec2.TwoSeed.brownG G B (min t (angLoc G T W VL VR B ζ n ω)) ω) -
    ∫ s in (0 : ℝ)..(min t (angLoc G T W VL VR B ζ n ω) : ℝ≥0),
      Ito.itoGen (fun p => lyapF lam c (angU κ xL xR ρL ρR p))
        (coordA xL xR G VL VR (fun _ _ => 0) s.toNNReal ω, Sec2.TwoSeed.brownG G B s.toNNReal ω)
        (densA G W VL VR (fun _ _ => 0) s ω)

section Facts

variable (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hGm : MeasurableSet G)
  (hGc : P Gᶜ = 0) (hgood : ∀ ω ∈ G, IsAngGood κ xL xR ρL ρR W VL VR B ζ T ω)
  (hT : Coupling.IsAnnouncingSeq (usualAugmentation 𝓕 P) P ζ T) (hx : 0 < xR 0 - xL 0)

include hE hGm hGc hgood hT hx in
theorem martingale_lyapMart (lam c : ℝ) (n : ℕ) :
    Martingale (lyapMart κ xL xR ρL ρR G T W VL VR B ζ lam c n) (usualAugmentation 𝓕 P) P :=
  martingale_angLoc hE hGm hGc hgood hT hx (contDiffOn_comp_angU κ xL xR ρL ρR (contDiff_lyapF lam c)) n
    (I := fun _ _ => 0) (c := fun _ _ => 0) (KI := 0) (Kc := 0) (fun _ _ _ _ => by simp)
    (fun _ _ => intervalIntegrable_const) (fun _ _ => by simp) (fun _ _ _ _ => by simp)
    ⟨fun _ _ => 0, fun _ => measurable_const, fun _ _ _ _ => rfl⟩ (fun _ _ => continuousOn_const)

include hgood hx in
/-- **The martingale along a good path**: `f(U_r) − ∫₀^r genExpr`, `r = t ∧ σ_n`. -/
theorem lyapMart_eq (hκ : 0 ≤ κ) (lam c : ℝ) (n : ℕ) {ω : Ω} (hω : ω ∈ G) (t : ℝ≥0) :
    lyapMart κ xL xR ρL ρR G T W VL VR B ζ lam c n t ω =
      lyapF lam c (angAt (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω)
          (min t (angLoc G T W VL VR B ζ n ω))) -
        ∫ s in (0 : ℝ)..(min t (angLoc G T W VL VR B ζ n ω) : ℝ≥0),
          genExpr κ ρL ρR (lyapF' lam c) (lyapF'' lam c) (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) s := by
  have hω' := hgood ω hω
  have hp := hω'.1
  set σ := angLoc G T W VL VR B ζ n ω
  have hσζ : (σ : ℝ≥0∞) < ζ ω := angLoc_lt_lifetime hω'
  have hrζ : ((min t σ : ℝ≥0) : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (by exact_mod_cast min_le_right _ _) hσζ
  have hc0 : (coordA xL xR G VL VR (fun _ _ => 0) (min t σ) ω, Sec2.TwoSeed.brownG G B (min t σ) ω) =
      pathCoord (fun i t => VL i t ω) (fun j t => VR j t ω) (B · ω) 0 (min t σ) := by
    simp only [coordA, Sec2.TwoSeed.brownG, hω, ↓reduceIte]; rfl
  simp only [lyapMart]
  rw [hc0, angU_pathCoord hp 0 hrζ]
  congr 1
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [uIcc_of_le (min t σ).coe_nonneg] at hs
  have hsζ := Sec2.toNNReal_lt_of_mem_Icc hrζ hs
  have h := itoGen_pathCoord_eq hp hκ hx (contDiff_lyapF lam c) (hasDerivAt_lyapF lam c)
    (hasDerivAt_lyapF' lam c) 0 0 hsζ
  simp only [coordA, densA, Sec2.TwoSeed.brownG, hω, ↓reduceIte]
  refine h.trans ?_
  simp only [genExpr, Real.toNNReal_coe]

/-- Off the good event the martingale is constant. -/
theorem lyapMart_of_not_mem (lam c : ℝ) (n : ℕ) {ω : Ω} (hω : ω ∉ G) (t : ℝ≥0) :
    lyapMart κ xL xR ρL ρR G T W VL VR B ζ lam c n t ω = lyapMart κ xL xR ρL ρR G T W VL VR B ζ lam c n 0 ω := by
  have h0 : angLoc G T W VL VR B ζ n ω = 0 := angLoc_of_not_mem hω n
  simp only [lyapMart, h0, min_zero]

include hgood hx in
theorem continuous_lyapMart (hκ : 0 ≤ κ) (lam c : ℝ) (n : ℕ) (ω : Ω) :
    Continuous fun t => lyapMart κ xL xR ρL ρR G T W VL VR B ζ lam c n t ω := by
  by_cases hω : ω ∈ G
  · have hω' := hgood ω hω
    have hp := hω'.1
    set σ := angLoc G T W VL VR B ζ n ω with hσdef
    have hσζ : (σ : ℝ≥0∞) < ζ ω := angLoc_lt_lifetime hω'
    have hcont' : Continuous (lyapF' lam c) := continuous_iff_continuousAt.2 fun u =>
      (hasDerivAt_lyapF' lam c u).continuousAt
    have hcont'' : Continuous (lyapF'' lam c) := by unfold lyapF''; fun_prop
    have hgi := intervalIntegrable_genExpr hp hx hcont' hcont'' hσζ (ρL := ρL) (ρR := ρR)
    have hinner : Continuous fun t : ℝ≥0 => ((min t σ : ℝ≥0) : ℝ) :=
      NNReal.continuous_coe.comp (continuous_id.min continuous_const)
    have hmaps : ∀ t : ℝ≥0, ((min t σ : ℝ≥0) : ℝ) ∈ Icc 0 (σ : ℝ) := fun t =>
      ⟨(min t σ).coe_nonneg, by exact_mod_cast min_le_right t σ⟩
    have hA : ContinuousOn (fun s : ℝ => lyapF lam c (angAt (W · ω) (fun i t => VL i t ω)
        (fun j t => VR j t ω) s.toNNReal)) (Icc 0 (σ : ℝ)) :=
      (contDiff_lyapF lam c (n := 0)).continuous.comp_continuousOn (continuousOn_angAt hp hx hσζ)
    have hI : ContinuousOn (fun x : ℝ => ∫ s in (0 : ℝ)..x, genExpr κ ρL ρR (lyapF' lam c) (lyapF'' lam c)
        (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) s) (Icc 0 (σ : ℝ)) := by
      have h := intervalIntegral.continuousOn_primitive_interval ((intervalIntegrable_iff').1 hgi)
      rwa [uIcc_of_le σ.coe_nonneg] at h
    have hcomp := (hA.sub hI).comp_continuous hinner hmaps
    refine hcomp.congr fun t => ?_
    rw [lyapMart_eq hgood hx hκ lam c n hω t]
    simp only [Function.comp_apply, Pi.sub_apply, Real.toNNReal_coe, σ]
  · have h := lyapMart_of_not_mem lam c n hω (κ := κ) (xL := xL) (xR := xR) (ρL := ρL) (ρR := ρR) (T := T) (W := W)
      (VL := VL) (VR := VR) (B := B) (ζ := ζ)
    simp only [h]
    exact continuous_const

end Facts

end Mart

/-! ### The finite clock on a band after `q` -/

section Band

variable {nL nR : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {κ : ℝ}
  {xL : Fin (nL + 1) → ℝ} {xR : Fin (nR + 1) → ℝ} {ρL : Fin (nL + 1) → ℝ} {ρR : Fin (nR + 1) → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ} {VR : Fin (nR + 1) → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {G : Set Ω} {T : ℕ → Ω → ℝ≥0}

variable (hκ : 0 < κ) (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hGm : MeasurableSet G)
  (hGc : P Gᶜ = 0) (hgood : ∀ ω ∈ G, IsAngGood κ xL xR ρL ρR W VL VR B ζ T ω)
  (hT : Coupling.IsAnnouncingSeq (usualAugmentation 𝓕 P) P ζ T) (hx : 0 < xR 0 - xL 0)

include hκ hE hGm hGc hgood hT hx in
/-- **The finite angular clock on a band after `q`.** If the Lyapunov inequality holds wherever the band level `lev`
of the state is positive, then almost surely, on an infinite lifetime with `lev > 0` at every time `t ≥ q`, the
angular clock `∫₀ᵗ D^{-2}` is bounded. -/
theorem ae_bddAbove_clock_of_band {lev : ℝ × ℝ × ℝ → ℝ} (hlev : Continuous lev) {lam c c₀ : ℝ} (hlam : 0 ≤ lam)
    (hc : c ∈ Icc (0 : ℝ) 1) (hc₀ : 0 < c₀)
    (hgen : ∀ wt l r : ℝ, l < wt → wt < r → 0 < lev (wt, l, r) →
      lyapGen κ (2 + ∑ i, ρL i) (2 + ∑ j, ρR j) lam c ((wt - l) / (r - l)) ≤ -c₀) (q : ℝ≥0) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ → (∀ t : ℝ≥0, q ≤ t → 0 < lev (W t ω, VL 0 t ω, VR 0 t ω)) →
      ∃ M : ℝ, ∀ t : ℝ≥0, ∫ s in (0 : ℝ)..t, (VR 0 s.toNNReal ω - VL 0 s.toNNReal ω)⁻¹ ^ 2 ≤ M := by
  have hP := hE.1.isProbabilityMeasure'
  have hEa := Ito.isIntegratedSLEEvolution_usualAugmentation hE
  -- the band exit and the sampling times
  have hτ : IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (bandExit Gᶜ ζ lev q W VL VR ω : WithTop ℝ≥0) :=
    isStoppingTime_bandExit hlev hEa.2.1 (hEa.2.2.1 0) (hEa.2.2.2.1 0)
      (fun t => (measurableSet_good_usual hGm hGc t).compl) (fun ω hω => by
        have hF := (hgood ω (not_not.1 hω)).1.isForcePath
        exact ⟨hF.continuousOn_w, hF.continuousOn_vL 0, hF.continuousOn_vR 0⟩) q
  set ρs : ℕ → Ω → WithTop ℝ≥0 := fun n ω =>
    max (min (bandExit Gᶜ ζ lev q W VL VR ω : WithTop ℝ≥0) ((n : ℝ≥0) : WithTop ℝ≥0)) (q : WithTop ℝ≥0)
    with hρsdef
  have hρs : ∀ n : ℕ, IsStoppingTime (usualAugmentation 𝓕 P) (ρs n) := fun n =>
    (hτ.min_const (n : ℝ≥0)).max_const q
  have hρsle : ∀ n : ℕ, ∀ ω, ρs n ω ≤ ((max (n : ℝ≥0) q : ℝ≥0) : WithTop ℝ≥0) := fun n ω => by
    simp only [hρsdef, WithTop.coe_max]
    exact max_le_max (min_le_right _ _) le_rfl
  -- the martingales
  set Mn : ℕ → ℝ≥0 → Ω → ℝ := fun n => lyapMart κ xL xR ρL ρR G T W VL VR B ζ lam c n with hMndef
  have hM : ∀ n, Martingale (Mn n) (usualAugmentation 𝓕 P) P := fun n =>
    martingale_lyapMart hE hGm hGc hgood hT hx lam c n
  have hMrc : ∀ n ω t, ContinuousWithinAt (Mn n · ω) (Ici t) t := fun n ω t =>
    (continuous_lyapMart hgood hx hκ.le lam c n ω).continuousWithinAt
  have hMi : ∀ n, Integrable (stoppedValue (Mn n) (ρs n)) P := fun n =>
    (tendsto_lintegral_stoppedValue_dyadicUpperTime (hM n).supermartingale (hMrc n) (hρs n) (hρsle n)).2.1
  -- optional sampling between `q` and `ρ_n`
  have hos : ∀ n : ℕ, q ≤ n → ∫ ω, Mn n q ω ∂P = ∫ ω, stoppedValue (Mn n) (ρs n) ω ∂P := by
    intro n hqn
    have h := setIntegral_stoppedValue_eq_of_rightContinuous (hM n) (hMrc n)
      (isStoppingTime_const (usualAugmentation 𝓕 P) q) (hρs n) (fun ω => le_max_right _ _)
      (T := n) (fun ω => (hρsle n ω).trans (by exact_mod_cast max_le le_rfl hqn)) MeasurableSet.univ
    simpa only [setIntegral_univ, stoppedValue_const] using h
  -- the constants
  obtain ⟨ω₀, hω₀⟩ : G.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    rw [h, compl_empty, measure_univ] at hGc
    exact one_ne_zero hGc
  have h00 : ((0 : ℝ≥0) : ℝ≥0∞) < ζ ω₀ := lt_of_le_of_lt bot_le ((hgood ω₀ hω₀).2.2.2.1 0)
  set K := 2 * Real.cosh lam + lam * Real.cosh lam / (xR 0 - xL 0) * errK xL xR ρL ρR with hKdef
  have hK0 : 0 ≤ K := by
    have h1 := errK_nonneg (hgood ω₀ hω₀).1 h00 (ρL := ρL) (ρR := ρR)
    have := Real.cosh_pos lam
    positivity
  set Zr : ℕ → Ω → ℝ := fun n ω => (K + stoppedValue (Mn n) (ρs n) ω - Mn n q ω) / c₀ with hZrdef
  -- the pathwise bound
  have hpath : ∀ n : ℕ, q ≤ n → ∀ ω ∈ G, ∀ r : ℝ≥0, ρs n ω = r →
      ∫ s in ((min q (angLoc G T W VL VR B ζ n ω) : ℝ≥0) : ℝ)..((min r (angLoc G T W VL VR B ζ n ω) : ℝ≥0) : ℝ),
        (VR 0 s.toNNReal ω - VL 0 s.toNNReal ω)⁻¹ ^ 2 ≤ Zr n ω := by
    intro n hqn ω hω r hr
    obtain ⟨r', hr', hqr, hrn, hlt, -⟩ := max_min_eq_coe (bandExit Gᶜ ζ lev q W VL VR ω : WithTop ℝ≥0)
      (by exact_mod_cast hqn : q ≤ (n : ℝ≥0))
    have hrr : r' = r := WithTop.coe_injective (hr'.symm.trans hr)
    subst hrr
    have hω' := hgood ω hω
    have hp := hω'.1
    set σ := angLoc G T W VL VR B ζ n ω with hσdef
    have hσζ : (σ : ℝ≥0∞) < ζ ω := angLoc_lt_lifetime hω'
    set s₁ := min q σ with hs₁
    set s₂ := min r' σ with hs₂
    have h12 : s₁ ≤ s₂ := min_le_min hqr le_rfl
    have hs₂ζ : (s₂ : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (by exact_mod_cast min_le_right _ _) hσζ
    have hs₁ζ : (s₁ : ℝ≥0∞) < ζ ω := lt_of_le_of_lt (by exact_mod_cast min_le_right _ _) hσζ
    have hM1 : Mn n q ω = lyapF lam c (angAt (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) s₁) -
        ∫ s in (0 : ℝ)..s₁, genExpr κ ρL ρR (lyapF' lam c) (lyapF'' lam c) (W · ω) (fun i t => VL i t ω)
          (fun j t => VR j t ω) s := lyapMart_eq hgood hx hκ.le lam c n hω q
    have hM2 : stoppedValue (Mn n) (ρs n) ω =
        lyapF lam c (angAt (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) s₂) -
        ∫ s in (0 : ℝ)..s₂, genExpr κ ρL ρR (lyapF' lam c) (lyapF'' lam c) (W · ω) (fun i t => VL i t ω)
          (fun j t => VR j t ω) s := by
      simp only [stoppedValue, hr, WithTop.untopD_coe]
      exact lyapMart_eq hgood hx hκ.le lam c n hω r'
    have hcont' : Continuous (lyapF' lam c) := continuous_iff_continuousAt.2 fun u =>
      (hasDerivAt_lyapF' lam c u).continuousAt
    have hcont'' : Continuous (lyapF'' lam c) := by unfold lyapF''; fun_prop
    have hg2 := intervalIntegrable_genExpr hp hx hcont' hcont'' hs₂ζ (ρL := ρL) (ρR := ρR)
    have hg1 := intervalIntegrable_genExpr hp hx hcont' hcont'' hs₁ζ (ρL := ρL) (ρR := ρR)
    have hsub := intervalIntegral.integral_interval_sub_left hg2 hg1
    -- the band on `(s₁, s₂)`
    have hband : ∀ s : ℝ, (s₁ : ℝ) < s → s < s₂ → VL 0 s.toNNReal ω < W s.toNNReal ω →
        W s.toNNReal ω < VR 0 s.toNNReal ω →
        lyapGen κ (2 + ∑ i, ρL i) (2 + ∑ j, ρR j) lam c
          (angAt (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) s.toNNReal) ≤ -c₀ := by
      intro s hs1 hs2 hL0 hR0
      have hs0 : 0 ≤ s := s₁.coe_nonneg.trans hs1.le
      have hqσ : q < σ := by
        by_contra hle
        have e1 : s₁ = σ := min_eq_right (not_lt.1 hle)
        have : (s₂ : ℝ) ≤ s₁ := by rw [e1]; exact_mod_cast min_le_right _ _
        linarith
      have e1 : s₁ = q := min_eq_left hqσ.le
      have hqs : q ≤ s.toNNReal := by
        rw [← Real.toNNReal_coe (r := q)]
        exact Real.toNNReal_le_toNNReal (by rw [← e1]; exact hs1.le)
      have hsr : s.toNNReal < r' := by
        have h2 : s < (r' : ℝ) := hs2.trans_le (by exact_mod_cast min_le_left _ _)
        exact (Real.toNNReal_lt_iff_lt_coe hs0).2 h2
      have hex := hlt s.toNNReal hqs hsr
      have hpos := pos_of_lt_bandExit (N := Gᶜ) (not_not.2 hω) hqs hex
      exact hgen _ _ _ hL0 hR0 hpos
    have hle := integral_genExpr_le_band hp hx hlam hc h12 hs₂ζ hband
    have hΦ1 := abs_lyapF_le hlam hc (angAt_mem_Icc hp hx hs₁ζ)
    have hΦ2 := abs_lyapF_le hlam hc (angAt_mem_Icc hp hx hs₂ζ)
    rw [hZrdef, le_div_iff₀ hc₀, hM1, hM2, hKdef]
    have e := hsub
    linarith [(abs_le.1 hΦ1).2, (abs_le.1 hΦ2).1]
  -- nonnegativity and expectation of `Zr`
  have hZnn : ∀ n : ℕ, q ≤ n → ∀ ω, ω ∈ G → 0 ≤ Zr n ω := by
    intro n hqn ω hω
    obtain ⟨r, hr, hqr, -, -, -⟩ := max_min_eq_coe (bandExit Gᶜ ζ lev q W VL VR ω : WithTop ℝ≥0)
      (by exact_mod_cast hqn : q ≤ (n : ℝ≥0))
    refine le_trans ?_ (hpath n hqn ω hω r hr)
    exact intervalIntegral.integral_nonneg (by exact_mod_cast min_le_min hqr le_rfl) fun _ _ => by positivity
  have hZi : ∀ n, Integrable (Zr n) P := fun n =>
    (((integrable_const K).add (hMi n)).sub ((hM n).integrable q)).div_const c₀
  have hZint : ∀ n : ℕ, q ≤ n → ∫ ω, Zr n ω ∂P = K / c₀ := by
    intro n hqn
    simp only [hZrdef]
    rw [integral_div, integral_sub (f := fun ω => K + stoppedValue (Mn n) (ρs n) ω) (g := Mn n q)
      ((integrable_const K).add (hMi n)) ((hM n).integrable q),
      integral_add (f := fun _ => K) (g := stoppedValue (Mn n) (ρs n)) (integrable_const K) (hMi n),
      integral_const, ← hos n hqn]
    simp only [probReal_univ, smul_eq_mul, one_mul, add_sub_cancel_right]
  have hqn_of : ∀ n : ℕ, ⌈q⌉₊ ≤ n → q ≤ n := fun n hn =>
    (Nat.le_ceil q).trans (by exact_mod_cast hn)
  -- Fatou
  set f : ℕ → Ω → ℝ≥0∞ := fun n ω => ENNReal.ofReal (Zr n ω) with hfdef
  have hfm : ∀ n, AEMeasurable (f n) P := fun n => (hZi n).aemeasurable.ennreal_ofReal
  set g : ℕ → Ω → ℝ≥0∞ := fun n => (hfm n).mk (f n) with hgdef
  have hgm : ∀ n, Measurable (g n) := fun n => (hfm n).measurable_mk
  have hfg : ∀ᵐ ω ∂P, ∀ n, f n ω = g n ω := ae_all_iff.2 fun n => (hfm n).ae_eq_mk
  have hfl : ∀ n : ℕ, q ≤ n → ∫⁻ ω, g n ω ∂P = ENNReal.ofReal (K / c₀) := by
    intro n hqn
    have hnn : 0 ≤ᵐ[P] Zr n := by
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 hGc] with ω hω
      exact hZnn n hqn ω (by simpa using hω)
    rw [← lintegral_congr_ae (hfm n).ae_eq_mk, ← hZint n hqn, ofReal_integral_eq_lintegral_ofReal (hZi n) hnn]
  have hlim : ∫⁻ ω, liminf (fun n => g n ω) atTop ∂P ≤ ENNReal.ofReal (K / c₀) := by
    refine (lintegral_liminf_le' fun n => (hgm n).aemeasurable).trans (liminf_le_of_frequently_le' ?_)
    exact (eventually_atTop.2 ⟨⌈q⌉₊, fun n hn => (hfl n (hqn_of n hn)).le⟩).frequently
  have hfin : ∀ᵐ ω ∂P, liminf (fun n => g n ω) atTop < ⊤ :=
    ae_lt_top (Measurable.liminf hgm) (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hlim)
  -- the conclusion on the band event
  filter_upwards [hfin, hfg, measure_eq_zero_iff_ae_notMem.1 hGc] with ω hω hωfg hωG' hζ hb
  have hωG : ω ∈ G := by simpa using hωG'
  have hω' := hgood ω hωG
  have hp := hω'.1
  have hfgω : (fun n => f n ω) = fun n => g n ω := funext hωfg
  rw [← hfgω] at hω
  have hex : bandExit Gᶜ ζ lev q W VL VR ω = ⊤ := (bandExit_eq_of_pos (not_not.2 hωG) hb).trans hζ
  have hρn : ∀ n : ℕ, q ≤ n → ρs n ω = ((n : ℝ≥0) : WithTop ℝ≥0) := fun n hqn => by
    obtain ⟨r, hr, -, -, -, htop⟩ := max_min_eq_coe (bandExit Gᶜ ζ lev q W VL VR ω : WithTop ℝ≥0)
      (by exact_mod_cast hqn : q ≤ (n : ℝ≥0))
    rw [← htop hex]
    exact hr
  refine ⟨(q : ℝ) * ((xR 0 - xL 0) ^ 2)⁻¹ + (liminf (fun n => f n ω) atTop).toReal, fun t => ?_⟩
  set t' := max t q with ht'def
  have ht'ζ : (t' : ℝ≥0∞) < ζ ω := by rw [hζ]; exact ENNReal.coe_lt_top
  have hqζ : (q : ℝ≥0∞) < ζ ω := by rw [hζ]; exact ENNReal.coe_lt_top
  obtain ⟨n₀, hn₀⟩ := exists_forall_le_angLoc hω' hgood hωG (hT.2.1 ω) ht'ζ
  have hev : ∀ᶠ n in atTop, ENNReal.ofReal (∫ s in (q : ℝ)..t',
      (VR 0 s.toNNReal ω - VL 0 s.toNNReal ω)⁻¹ ^ 2) ≤ f n ω := by
    refine eventually_atTop.2 ⟨max n₀ ⌈q⌉₊, fun n hn => ENNReal.ofReal_le_ofReal ?_⟩
    have hqn := hqn_of n (le_of_max_le_right hn)
    have hσn := hn₀ n (le_of_max_le_left hn)
    have h := hpath n hqn ω hωG n (hρn n hqn)
    have e1 : min q (angLoc G T W VL VR B ζ n ω) = q := min_eq_left ((le_max_right t q).trans hσn)
    have e2 : min (n : ℝ≥0) (angLoc G T W VL VR B ζ n ω) = angLoc G T W VL VR B ζ n ω :=
      min_eq_right (angLoc_le_n n ω)
    rw [e1, e2] at h
    refine le_trans ?_ h
    have hσζ := angLoc_lt_lifetime (G := G) (n := n) hω'
    refine intervalIntegral.integral_mono_interval le_rfl (by exact_mod_cast le_max_right t q)
      (by exact_mod_cast hσn) (ae_of_all _ fun s => by positivity)
      ((intervalIntegrable_clockRate hp hx hσζ).mono_set ?_)
    rw [uIcc_of_le (by exact_mod_cast (le_max_right t q).trans hσn), uIcc_of_le (angLoc G T W VL VR B ζ n ω).coe_nonneg]
    exact Icc_subset_Icc_left q.coe_nonneg
  have hle := le_liminf_of_le (by isBoundedDefault) hev
  have hq' := (ENNReal.ofReal_le_iff_le_toReal hω.ne).1 hle
  have hcl := intervalIntegrable_clockRate hp hx ht'ζ
  have hcl0 := intervalIntegrable_clockRate hp hx hqζ
  have hqt' : (q : ℝ) ≤ t' := by exact_mod_cast le_max_right t q
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hcl0 (hcl.mono_set (by
    rw [uIcc_of_le hqt', uIcc_of_le t'.coe_nonneg]; exact Icc_subset_Icc_left q.coe_nonneg))
  have h0q : ∫ s in (0 : ℝ)..q, (VR 0 s.toNNReal ω - VL 0 s.toNNReal ω)⁻¹ ^ 2 ≤
      (q : ℝ) * ((xR 0 - xL 0) ^ 2)⁻¹ := by
    calc ∫ s in (0 : ℝ)..q, (VR 0 s.toNNReal ω - VL 0 s.toNNReal ω)⁻¹ ^ 2
        ≤ ∫ s in (0 : ℝ)..q, ((xR 0 - xL 0) ^ 2)⁻¹ := by
          refine intervalIntegral.integral_mono_on q.coe_nonneg hcl0 intervalIntegrable_const fun s hs => ?_
          have hsζ := Sec2.toNNReal_lt_of_mem_Icc hqζ hs
          have hD := le_gapAt hp hsζ
          rw [inv_pow]
          exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hx.le hD 2)
      _ = (q : ℝ) * ((xR 0 - xL 0) ^ 2)⁻¹ := by simp
  have htt' : ∫ s in (0 : ℝ)..t, (VR 0 s.toNNReal ω - VL 0 s.toNNReal ω)⁻¹ ^ 2 ≤
      ∫ s in (0 : ℝ)..t', (VR 0 s.toNNReal ω - VL 0 s.toNNReal ω)⁻¹ ^ 2 :=
    intervalIntegral.integral_mono_interval le_rfl t.coe_nonneg (by exact_mod_cast le_max_left t q)
      (ae_of_all _ fun s => by positivity) hcl
  linarith

end Band

/-! ### Aux. lemma 101 for eventual bands -/

section Statement

/-- The band level `8(V^{R,0} − W) − D` of a state `(W, V^{L,0}, V^{R,0})`: positive exactly on `U < 7/8`. -/
def levLow (p : ℝ × ℝ × ℝ) : ℝ := 8 * (p.2.2 - p.1) - (p.2.2 - p.2.1)

/-- The band level `8(W − V^{L,0}) − D`: positive exactly on `U > 1/8`. -/
def levHigh (p : ℝ × ℝ × ℝ) : ℝ := 8 * (p.1 - p.2.1) - (p.2.2 - p.2.1)

theorem continuous_levLow : Continuous levLow := by unfold levLow; fun_prop

theorem continuous_levHigh : Continuous levHigh := by unfold levHigh; fun_prop

/-- **Aux. lemma 101 for the bands `U < 3/4`, `U > 1/4`** (Specification pp. 346–348), every `κ > 0`, all weights:
on an infinite lifetime with an eventual band the angular clock is finite. -/
theorem aux101BandClockStatement {κ : ℝ} (hκ : 0 < κ) : TrialsHi.Aux101BandClockStatement.{u} κ := by
  intro nL nR xL xR ρL ρR hF hsep Ω mΩ P _ 𝓕 W VL VR B ζ hE
  by_cases hthr : ForceWord.ThresholdCondition ρL ρR 0 xL xR
  · filter_upwards [ae_ne_top_of_thresholdCondition hE hthr] with ω hω hζ
    exact absurd hζ hω
  obtain ⟨T, G, hT, hGm, hGc, hgood⟩ := exists_setup hκ hE hthr
  have hx : 0 < xR 0 - xL 0 := sub_pos.2 (hsep 0 0)
  obtain ⟨lam₁, c₁, c₁₀, hlam₁, hc₁, hc₁₀, hgen₁⟩ := exists_lyap_low hκ (2 + ∑ i, ρL i) (2 + ∑ j, ρR j)
  obtain ⟨lam₂, c₂, c₂₀, hlam₂, hc₂, hc₂₀, hgen₂⟩ := exists_lyap_high hκ (2 + ∑ i, ρL i) (2 + ∑ j, ρR j)
  have hlow : ∀ wt l r : ℝ, l < wt → wt < r → 0 < levLow (wt, l, r) →
      lyapGen κ (2 + ∑ i, ρL i) (2 + ∑ j, ρR j) lam₁ c₁ ((wt - l) / (r - l)) ≤ -c₁₀ := by
    intro wt l r hl hr hlev
    simp only [levLow] at hlev
    have hD : 0 < r - l := by linarith
    refine hgen₁ _ ⟨div_pos (by linarith) hD, (div_lt_one hD).2 (by linarith)⟩ ?_
    rw [div_le_iff₀ hD]; linarith
  have hhigh : ∀ wt l r : ℝ, l < wt → wt < r → 0 < levHigh (wt, l, r) →
      lyapGen κ (2 + ∑ i, ρL i) (2 + ∑ j, ρR j) lam₂ c₂ ((wt - l) / (r - l)) ≤ -c₂₀ := by
    intro wt l r hl hr hlev
    simp only [levHigh] at hlev
    have hD : 0 < r - l := by linarith
    refine hgen₂ _ ⟨div_pos (by linarith) hD, (div_lt_one hD).2 (by linarith)⟩ ?_
    rw [le_div_iff₀ hD]; linarith
  have hb1 := fun q : ℕ => ae_bddAbove_clock_of_band hκ hE hGm hGc hgood hT hx continuous_levLow hlam₁ hc₁
    hc₁₀ hlow (q : ℝ≥0)
  have hb2 := fun q : ℕ => ae_bddAbove_clock_of_band hκ hE hGm hGc hgood hT hx continuous_levHigh hlam₂ hc₂
    hc₂₀ hhigh (q : ℝ≥0)
  filter_upwards [ae_all_iff.2 hb1, ae_all_iff.2 hb2, hE.2.2.2.2] with ω h1 h2 hp hζ hband
  have hD : ∀ t : ℝ≥0, 0 < VR 0 t ω - VL 0 t ω := fun t =>
    hx.trans_le (le_gapAt hp (by rw [hζ]; exact ENNReal.coe_lt_top))
  rcases hband with ⟨T₀, hT₀⟩ | ⟨T₀, hT₀⟩
  · refine h1 ⌈T₀⌉₊ hζ fun t ht => ?_
    have h := hT₀ t ((Nat.le_ceil T₀).trans ht)
    simp only [levLow]
    linarith [hD t]
  · refine h2 ⌈T₀⌉₊ hζ fun t ht => ?_
    have h := hT₀ t ((Nat.le_ceil T₀).trans ht)
    simp only [levHigh]
    linarith [hD t]

end Statement

end TrialsHi2

end Sec7

end InteractingSLE
