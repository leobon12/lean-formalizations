import QuantumZipper.Proofs.Zipper.SWCoreB7bFlowBall
import QuantumZipper.Proofs.Zipper.UnifACFlowDetFam

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-B7b-FLOW (2): restart of complex solutions and the time-Lipschitz bound

For the reversed drivers `vrev W s` (`B2Defs`), a complex solution of horizon `s` restarted at
time `h` is a solution for the driver `vrev W (s - h)` started from its value at `h`
(`isCRevSol_vrev_restart`). Consequently, in **uncentered** coordinates (`y = z₀ - W s`) the maps
`ψ_s = revMapExt (vrev W s) (s - q)` are Lipschitz in `s` (`norm_revMapExt_vrev_time_sub_le`):
the restart point differs from `z₀ - W s'` only by `∫₀ʰ 2/u`, of size `≤ 2h/c`.

Note: in the *centered* coordinates `ψ_s(z)` is **not** Lipschitz in `s` for a general continuous
`W`: `ψ_s(z) = z + W s - W q - ∫…`, so `ψ_s(z) - ψ_{s'}(z)` contains `W s - W s'`.

Own elementary arguments (restart of an integral equation, Grönwall via
`RevMapExtension.norm_revMapExt_sub_le`).
-/

noncomputable section

open Complex Filter MeasureTheory intervalIntegral Set
open scoped Topology NNReal ENNReal ComplexConjugate

namespace QuantumZipper
namespace SWCore

open RevMapExtension B2

theorem b7bf_vrev_sub {W : ℝ → ℝ} {s h r : ℝ} (hh : 0 ≤ h) (hr : 0 ≤ r) (hhr : h + r ≤ s) :
    vrev W s (h + r) - vrev W s h = vrev W (s - h) r := by
  have e1 : min (max (h + r) 0) s = h + r := by
    rw [max_eq_left (by linarith), min_eq_left hhr]
  have e2 : min (max h 0) s = h := by rw [max_eq_left hh, min_eq_left (by linarith)]
  have e3 : min (max r 0) (s - h) = r := by rw [max_eq_left hr, min_eq_left (by linarith)]
  simp only [vrev, e1, e2, e3]
  rw [show s - (h + r) = s - h - r by ring]
  ring

/-- **Restart.** A solution for `vrev W s` restarted at time `h` solves the equation for
`vrev W (s - h)` from its value at `h`. -/
theorem isCRevSol_vrev_restart {W : ℝ → ℝ} {s L h : ℝ} {z : ℂ} {u : ℝ → ℂ}
    (hu : IsCRevSol (vrev W s) z L u) (hh : 0 ≤ h) (hhL : h ≤ L) (hLs : L ≤ s) :
    IsCRevSol (vrev W (s - h)) (u h) (L - h) (fun r => u (h + r)) := by
  have hcont : ContinuousOn (fun r => u (h + r)) (Icc 0 (L - h)) := by
    refine hu.1.comp (continuous_const.add continuous_id).continuousOn ?_
    intro r hr; exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
  refine ⟨hcont, fun r hr => ⟨(hu.2 (h + r) ⟨by linarith [hr.1], by linarith [hr.2]⟩).1, ?_⟩⟩
  have hint : ∀ a b, a ∈ Icc (0 : ℝ) L → b ∈ Icc (0 : ℝ) L →
      IntervalIntegrable (fun t => (2 : ℂ) / u t) volume a b := by
    intro a b ha hb
    apply ContinuousOn.intervalIntegrable
    have hsub : uIcc a b ⊆ Icc 0 L := uIcc_subset_Icc ha hb
    exact continuousOn_const.div (hu.1.mono hsub) fun t ht => (hu.2 t (hsub ht)).1
  have h1 := (hu.2 (h + r) ⟨by linarith [hr.1], by linarith [hr.2]⟩).2
  have h2 := (hu.2 h ⟨hh, hhL⟩).2
  have hadd := integral_add_adjacent_intervals (hint 0 h ⟨le_rfl, by linarith⟩ ⟨hh, hhL⟩)
    (hint h (h + r) ⟨hh, hhL⟩ ⟨by linarith [hr.1], by linarith [hr.2]⟩)
  have hcomp : (∫ ρ in (0 : ℝ)..r, (2 : ℂ) / u (h + ρ)) = ∫ t in h..(h + r), (2 : ℂ) / u t := by
    rw [intervalIntegral.integral_comp_add_left (fun t => (2 : ℂ) / u t) h, add_zero]
  have hv := b7bf_vrev_sub (W := W) hh hr.1 (by linarith [hr.2])
  have hv' : ((vrev W (s - h) r : ℝ) : ℂ) = (vrev W s (h + r) : ℂ) - (vrev W s h : ℂ) := by
    rw [← hv]; push_cast; ring
  show u (h + r) = u h - (vrev W (s - h) r : ℂ) - ∫ ρ in (0 : ℝ)..r, 2 / u (h + ρ)
  rw [hcomp, hv', h1, h2, ← hadd]
  ring

/-- **Time-Lipschitz bound in uncentered coordinates.** For `0 ≤ q ≤ s' ≤ s` and good solutions
(clearance `c`) from `z₀ - W s` (horizon `s`) and `z₀ - W s'` (horizon `s'`),
`‖ψ_s(z₀ - W s) - ψ_{s'}(z₀ - W s')‖ ≤ 2 (s - s')/c · exp (2 (s' - q)/c²)`. -/
theorem norm_revMapExt_vrev_time_sub_le {W : ℝ → ℝ} {q s s' c : ℝ} (hc : 0 < c) (hq : 0 ≤ q)
    (hqs' : q ≤ s') (hs's : s' ≤ s) {z₀ : ℂ} {u u' : ℝ → ℂ}
    (hu : IsCRevSol (vrev W s) (z₀ - W s) (s - q) u) (hub : ∀ r ∈ Icc (0 : ℝ) (s - q), c ≤ ‖u r‖)
    (hu' : IsCRevSol (vrev W s') (z₀ - W s') (s' - q) u')
    (hub' : ∀ r ∈ Icc (0 : ℝ) (s' - q), c ≤ ‖u' r‖) :
    ‖revMapExt (vrev W s) (s - q) (z₀ - W s) - revMapExt (vrev W s') (s' - q) (z₀ - W s')‖ ≤
      2 * (s - s') / c * Real.exp (2 / c ^ 2 * (s' - q)) := by
  have hh : 0 ≤ s - s' := by linarith
  have hr := isCRevSol_vrev_restart hu hh (by linarith) (by linarith)
  rw [show s - (s - s') = s' by ring, show s - q - (s - s') = s' - q by ring] at hr
  have hrb : ∀ r ∈ Icc (0 : ℝ) (s' - q), c ≤ ‖u (s - s' + r)‖ := fun r hr' =>
    hub _ ⟨by linarith [hr'.1], by linarith [hr'.2]⟩
  have e1 : revMapExt (vrev W s) (s - q) (z₀ - W s) =
      revMapExt (vrev W s') (s' - q) (u (s - s')) := by
    rw [revMapExt_eq hu (by linarith), revMapExt_eq hr (by linarith)]
    congr 1; ring
  rw [e1]
  have hmain := norm_revMapExt_sub_le (by linarith) hc hu' hr hub' hrb
  refine hmain.trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
  have h2 := (hu.2 (s - s') ⟨hh, by linarith⟩).2
  have hv : vrev W s (s - s') = W s' - W s := by
    have e2 : min (max (s - s') 0) s = s - s' := by
      rw [max_eq_left hh, min_eq_left (by linarith)]
    simp only [vrev, e2]; rw [show s - (s - s') = s' by ring]
  rw [hv] at h2
  have e3 : u (s - s') - (z₀ - (W s' : ℂ)) = -∫ r in (0 : ℝ)..(s - s'), 2 / u r := by
    rw [h2]; push_cast; ring
  rw [e3, norm_neg]
  have hb : ∀ t ∈ uIoc (0 : ℝ) (s - s'), ‖(2 : ℂ) / u t‖ ≤ 2 / c := by
    intro t ht
    rw [uIoc_of_le hh] at ht
    have hct := hub t ⟨ht.1.le, by linarith [ht.2]⟩
    rw [norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]
    exact div_le_div_of_nonneg_left (by norm_num) hc hct
  have := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [sub_zero, abs_of_nonneg hh] at this
  calc _ ≤ 2 / c * (s - s') := this
    _ = 2 * (s - s') / c := by ring

end SWCore
end QuantumZipper
