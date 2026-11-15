/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.TwoTime2Drive

/-!
# The image clock is `C¹`, and the integrated Schwarzian identity (D4)–(D5)

Packet PROVE-ZHAN-GT4-A4. Source: Astra, *Follow-up proofs and dependency audit*, Part A.1.2, (D4)–(D5)
(`source/external/AstraIG1/ig1_followup_proofs.txt` L276–L289, ruling R38): `F(s, t) = exp ∫₀ˢ∫₀ᵗ 2A²_{1,1}A²_{2,1}/E⁴`,
"differentiation of (D1) in the other time gives `∂_{t_k} 𝒮h_j(W_j) = −12A²_{1,1}A²_{2,1}/E⁴`,
`∂_{t_j} log F = −(1/6)𝒮h_j(W_j)`."

With `OwnData` for the growing curve (driver `W`, frozen hull `A`, image clock `a`, image driver `W̃`):

* `OwnData.hasDerivWithinAt_clock`: `ȧ(t) = A₁(t)²`, `A₁(t) = F_t'(W_t)` real and positive (`F_t = ownExt … t`);
* `OwnData.continuousOn_A1`: `t ↦ A₁(t)` is continuous on `[0, T]` (so the clock is `C¹`);
* `OwnData.schwarzFwd_eq_integral`: for a point `ζ` alive for the image chain (the frozen curve's driving point),
  `𝒮h_frozen(ζ)(t) = −∫₀ᵗ 12 A₁(v)² A_{frozen,1}(v)²/E(v)⁴ dv`, i.e. `∫₀ᵗ 2A²A²/E⁴ = −(1/6)𝒮h(ζ)(t)`, which is
  (D5)'s `∂ log F = −(1/6)𝒮h` with (D4)'s `F`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric

namespace InteractingSLE.ZhanGT4

open QuantumZipper (H Hbar IsForwardSol fwdMap fwdMapInv fwdHull logDerivFwd)

namespace OwnData

variable {W : ℝ → ℝ} {A : Set ℂ} {φ : ℂ → ℂ} {T : ℝ} {a W' : ℝ → ℝ} (h : OwnData W A φ T a W')
include h

/-- **The clock rate**: `ȧ(t) = A₁(t)²` with `A₁(t) = F_t'(W_t)` real and positive. -/
theorem hasDerivWithinAt_clock {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    HasDerivWithinAt a ((deriv (ownExt W W' a φ t) (W t)).re ^ 2) (Icc 0 T) t ∧
      0 < (deriv (ownExt W W' a φ t) (W t)).re ∧ (deriv (ownExt W W' a φ t) (W t)).im = 0 := by
  obtain ⟨ρ, hρ, hcl⟩ := h.exists_clearance
  obtain ⟨hFd, -, -, -, -, hFR⟩ := h.ownExt_props ht (hcl t ht)
  obtain ⟨R, hR⟩ := (h.isHPHull_E ht).exists_isMapOut
  obtain ⟨-, -, -, hrate⟩ := h.rate t ht R hR
  obtain ⟨hpos, him, hder⟩ := hrate (ρ / 2) (by positivity) _ hFd (hFR R hR)
  exact ⟨hder, hpos, him⟩

/-- **`A₁(t) = F_t'(W_t)` is continuous on `[0, T]`.** -/
theorem continuousOn_A1 : ContinuousOn (fun t => deriv (ownExt W W' a φ t) (W t)) (Icc 0 T) := by
  intro t₀ ht₀
  obtain ⟨η, hη, r, hr, hdisj, hWm, -⟩ := h.exists_box ht₀
  have hJ : Icc (max 0 (t₀ - η)) (min T (t₀ + η)) ⊆ Icc 0 T := fun t ht => (mem_box_of_abs_lt ht).1
  have hdc := continuousOn_deriv_of_holo (F := fun t => ownExt W W' a φ t)
    (fun t ht => (h.box_props hJ hdisj ht).1) (h.continuousOn_box hJ hdisj)
  have hcl : Continuous fun t : ℝ => (t, (W t : ℂ)) := continuous_id.prodMk (continuous_ofReal.comp h.cont)
  have hc := hdc.comp hcl.continuousOn (fun t ht => (⟨ht, hWm t ht⟩ :
    (t, (W t : ℂ)) ∈ Icc (max 0 (t₀ - η)) (min T (t₀ + η)) ×ˢ ball (W t₀ : ℂ) r))
  simp only [Function.comp_def] at hc
  exact (hc t₀ (mem_box_self hη ht₀)).mono_of_mem_nhdsWithin (box_mem_nhds hη)

theorem continuousOn_clockRate :
    ContinuousOn (fun t => (deriv (ownExt W W' a φ t) (W t)).re ^ 2) (Icc 0 T) :=
  (continuous_re.comp_continuousOn h.continuousOn_A1).pow 2

theorem mapsTo_clock : MapsTo a (Icc 0 T) (Icc 0 (a T)) := fun s hs => by
  have hTm : T ∈ Icc (0 : ℝ) T := ⟨h.pos.le, le_rfl⟩
  refine ⟨?_, h.mono.monotoneOn hs hTm hs.2⟩
  rw [← h.a0]; exact h.mono.monotoneOn ⟨le_rfl, h.pos.le⟩ hs hs.1

/-- **The integrated Schwarzian identity (D4)–(D5).** For `ζ` alive for the image chain on `[0, a(T)]`:
`𝒮g̃_{a(t)}(ζ) = ∫₀ᵗ A₁(v)² · (−12 g̃'_{a(v)}(ζ)²/(g̃_{a(v)}(ζ) − W̃(a(v)))⁴) dv`. -/
theorem schwarzFwd_eq_integral {ζ : ℂ} {v : ℝ → ℂ} (hv : IsForwardSol W' ζ (a T) v) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) :
    schwarzFwd W' (a t) ζ = ∫ s in (0 : ℝ)..t, (((deriv (ownExt W W' a φ s) (W s)).re ^ 2 : ℝ) : ℂ) *
      -(12 * Complex.exp (logDerivFwd W' (a s) ζ) ^ 2 / fwdMap W' (a s) ζ ^ 4) := by
  have haT : 0 ≤ a T := (h.mapsTo_clock ⟨h.pos.le, le_rfl⟩).1
  obtain ⟨ε, hε, hlow, hζ⟩ := exists_aliveDisc_self hv haT
  have hder : ∀ s ∈ Icc (0 : ℝ) T, HasDerivWithinAt (fun s => schwarzFwd W' (a s) ζ)
      ((((deriv (ownExt W W' a φ s) (W s)).re ^ 2 : ℝ) : ℂ) *
        -(12 * Complex.exp (logDerivFwd W' (a s) ζ) ^ 2 / fwdMap W' (a s) ζ ^ 4)) (Icc 0 T) s := fun s hs =>
    hasDerivWithinAt_schwarzFwd_clock h.contW' hv h.mapsTo_clock hs (h.hasDerivWithinAt_clock hs).1
  -- continuity of the derivative
  have hcl : ContinuousOn (fun s => (a s, ζ)) (Icc 0 T) := (h.contA.prodMk continuousOn_const)
  have hmaps : MapsTo (fun s => (a s, ζ)) (Icc 0 T) (Icc 0 (a T) ×ˢ ball ζ (aliveRad (a T) ε)) :=
    fun s hs => ⟨h.mapsTo_clock hs, hζ⟩
  have hL := (continuousOn_logDerivFwd_aliveDisc h.contW' hv hε hlow).comp hcl hmaps
  have hf := (continuousOn_fwdMap_aliveDisc h.contW' hv hε hlow).comp hcl hmaps
  simp only [Function.comp_def] at hL hf
  have hne : ∀ s ∈ Icc (0 : ℝ) T, fwdMap W' (a s) ζ ^ 4 ≠ 0 := fun s hs =>
    pow_ne_zero 4 (fwdMap_ne_zero_aliveDisc h.contW' hv hε hlow hζ (h.mapsTo_clock hs))
  have hdc : ContinuousOn (fun s => (((deriv (ownExt W W' a φ s) (W s)).re ^ 2 : ℝ) : ℂ) *
      -(12 * Complex.exp (logDerivFwd W' (a s) ζ) ^ 2 / fwdMap W' (a s) ζ ^ 4)) (Icc 0 T) := by
    refine (continuous_ofReal.comp_continuousOn h.continuousOn_clockRate (f := fun t => (deriv (ownExt W W' a φ t) (W t)).re ^ 2)).mul ?_
    exact ((continuousOn_const.mul ((continuous_exp.comp_continuousOn hL).pow 2)).div (hf.pow 4) hne).neg
  have hsub : Icc 0 t ⊆ Icc (0 : ℝ) T := Icc_subset_Icc_right ht.2
  have key := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht.1
    (fun s hs => (hder s (hsub hs)).continuousWithinAt.mono hsub) (fun s hs => ?_)
    ((hdc.mono hsub).intervalIntegrable_of_Icc ht.1)
  · rw [key, h.a0]
    simp [schwarzFwd, logDeriv1, logDeriv2]
  · exact (hder s (hsub (Ioo_subset_Icc_self hs))).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGT_of_mem ⟨hs.1.le, lt_of_lt_of_le hs.2 ht.2⟩)

end OwnData

end InteractingSLE.ZhanGT4
