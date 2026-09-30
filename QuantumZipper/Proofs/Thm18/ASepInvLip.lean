import QuantumZipper.Proofs.Thm18.ASepCentre
import QuantumZipper.Proofs.RS.GenerationBasic
import QuantumZipper.Proofs.Loewner.ForwardFlow

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Lipschitz bound for the inverse forward map near a good trajectory (task ASEP, piece C3)

`norm_fwdMapInv_sub_le`: if the forward trajectory of `z₀` stays at distance `≥ m` from the
singularity on `[0,T]`, and `ζ ∈ ℍ` is within `(m/2) e^{-8T/m²}` of `ζ₀ = f_t(z₀)`, then
`‖f_t⁻¹(ζ) - z₀‖ ≤ e^{8T/m²} ‖ζ - ζ₀‖`.

Proof (**own elementary argument**, the mirror of `ASepCentre`; standard Loewner ODE
regularity, Lawler, *Conformally invariant processes in the plane*, §4.1): with
`w = f_t⁻¹(ζ)` (which is not swallowed by time `t`, so has a forward solution `v` on `[0,t]`
with `v t = ζ`, `RS.fwdMapInv_mem_compl_fwdHull`, `RS.fwdMap_fwdMapInv`), the difference
`v - u` of the two forward trajectories is run *backwards* from time `t` by Grönwall
(`norm_sol_sub_le_gronwall_back`); a first-exit-time continuation argument keeps
`‖v - u‖ < 3m/4`, hence `‖v‖ ≥ m/4`, on the whole of `[0,t]`.
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped Topology

namespace QuantumZipper
namespace ASep

/-- **Backward Grönwall comparison.** Two forward solutions on `[0,t]`, with `‖u‖ ≥ a`,
`‖v‖ ≥ b` on `(t - x, t]`, satisfy
`‖v (t-x) - u (t-x)‖ ≤ ‖v t - u t‖ e^{2x/(ab)}`. -/
theorem norm_sol_sub_le_gronwall_back {W : ℝ → ℝ} {z z' : ℂ} {t : ℝ} {u v : ℝ → ℂ}
    (hu : IsForwardSol W z t u) (hv : IsForwardSol W z' t v) {x a b : ℝ}
    (hx : x ∈ Icc (0 : ℝ) t) (ha : 0 < a) (hb : 0 < b)
    (hab : ∀ y ∈ Ico (0 : ℝ) x, a ≤ ‖u (t - y)‖ ∧ b ≤ ‖v (t - y)‖) :
    ‖v (t - x) - u (t - x)‖ ≤ ‖v t - u t‖ * Real.exp (2 / (a * b) * x) := by
  set g : ℝ → ℂ := fun r => (v r + (W r : ℂ)) - (u r + (W r : ℂ)) with hgdef
  have hg : ∀ r, g r = v r - u r := fun r => by simp only [hgdef]; ring
  set f : ℝ → ℂ := fun y => g (t - y) with hfdef
  have hmaps : MapsTo (fun y : ℝ => t - y) (Icc 0 t) (Icc 0 t) :=
    fun s hs => ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have hsub : Icc (0 : ℝ) x ⊆ Icc 0 t := Icc_subset_Icc_right hx.2
  have hgc : ContinuousOn g (Icc 0 t) := (hv.1.sub hu.1).congr fun r _ => hg r
  have hcont : ContinuousOn f (Icc 0 x) :=
    (hgc.comp (continuousOn_const.sub continuousOn_id) hmaps).mono hsub
  have hder : ∀ y ∈ Ico (0 : ℝ) x,
      HasDerivWithinAt f (-(2 / v (t - y) - 2 / u (t - y))) (Ici y) y := by
    intro y hy
    have hyt : y ∈ Icc (0 : ℝ) t := hsub (Ico_subset_Icc_self hy)
    have hg' : HasDerivWithinAt g (2 / v (t - y) - 2 / u (t - y)) (Icc 0 t) (t - y) :=
      (FwdHolo.hasDerivWithinAt_shift hv (hmaps hyt)).sub
        (FwdHolo.hasDerivWithinAt_shift hu (hmaps hyt))
    have hh : HasDerivWithinAt (fun y : ℝ => t - y) (-1) (Icc 0 t) y :=
      ((hasDerivAt_id' y).const_sub t).hasDerivWithinAt
    have h2 := hg'.scomp y hh hmaps
    have hyt' : y ∈ Ico (0 : ℝ) t := ⟨hy.1, lt_of_lt_of_le hy.2 hx.2⟩
    have h3 := h2.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hyt')
    have h4 : HasDerivWithinAt f ((-1 : ℝ) • (2 / v (t - y) - 2 / u (t - y))) (Ici y) y := h3
    rwa [neg_one_smul] at h4
  have h0 : ‖f 0‖ ≤ ‖v t - u t‖ := by
    simp only [hfdef, sub_zero, hg, le_refl]
  have hbound : ∀ y ∈ Ico (0 : ℝ) x,
      ‖-(2 / v (t - y) - 2 / u (t - y))‖ ≤ 2 / (a * b) * ‖f y‖ + 0 := by
    intro y hy
    have hyt : t - y ∈ Icc (0 : ℝ) t := hmaps (hsub (Ico_subset_Icc_self hy))
    have hu0 : u (t - y) ≠ 0 := (hu.2 _ hyt).1
    have hv0 : v (t - y) ≠ 0 := (hv.2 _ hyt).1
    obtain ⟨hA, hB⟩ := hab y hy
    have hfy : f y = v (t - y) - u (t - y) := hg _
    have hid : 2 / v (t - y) - 2 / u (t - y) = -(2 * f y) / (u (t - y) * v (t - y)) := by
      rw [hfy]; field_simp; ring
    rw [hid, norm_neg, norm_div, norm_neg, norm_mul, norm_mul, add_zero]
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h2, show 2 / (a * b) * ‖f y‖ = 2 * ‖f y‖ / (a * b) by ring]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (mul_le_mul hA hB hb.le (norm_nonneg _))
  have key := norm_le_gronwallBound_of_norm_deriv_right_le hcont hder h0 hbound x
    ⟨hx.1, le_rfl⟩
  rw [gronwallBound_ε0, sub_zero] at key
  have hfx : f x = v (t - x) - u (t - x) := hg _
  rw [hfx] at key
  exact key

/-- **(C3) Lipschitz bound for the inverse map near a good trajectory.** -/
theorem norm_fwdMapInv_sub_le {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T m : ℝ}
    (hT : 0 ≤ T) (hm : 0 < m)
    {z₀ : ℂ} (hz₀ : 0 < z₀.im) (hsol : ∃ u, IsForwardSol W z₀ T u)
    (hlow : ∀ s ∈ Set.Icc (0 : ℝ) T, m ≤ ‖fwdMap W s z₀‖) {t : ℝ} (ht : t ∈ Set.Icc 0 T)
    {ζ : ℂ} (hζ : 0 < ζ.im)
    (hclose : ‖ζ - fwdMap W t z₀‖ ≤ m / 2 * Real.exp (-(8 * T / m ^ 2))) :
    ‖fwdMapInv W t ζ - z₀‖ ≤ Real.exp (8 * T / m ^ 2) * ‖ζ - fwdMap W t z₀‖ := by
  clear hz₀
  obtain ⟨u, huT⟩ := hsol
  have hu : IsForwardSol W z₀ t u := isForwardSol_restrict huT ht.1 ht.2
  have hul : ∀ r ∈ Icc (0 : ℝ) t, m ≤ ‖u r‖ := fun r hr => by
    have hrT : r ∈ Icc (0 : ℝ) T := ⟨hr.1, hr.2.trans ht.2⟩
    rw [← fwdMap_eq_any huT hrT]; exact hlow r hrT
  have htt : t ∈ Icc (0 : ℝ) t := ⟨ht.1, le_rfl⟩
  have hζ₀ : fwdMap W t z₀ = u t := fwdMap_eq_any hu htt
  have hwH := RS.fwdMapInv_mem_compl_fwdHull hW hW0 ht.1 (show ζ ∈ H from hζ)
  set w := fwdMapInv W t ζ with hwdef
  obtain ⟨v, hv⟩ := exists_isForwardSol_of_not_mem_fwdHull ht.1 hwH.1 hwH.2
  have hvt : v t = ζ := by
    rw [← fwdMap_eq_any hv htt, hwdef]
    exact RS.fwdMap_fwdMapInv hW hW0 ht.1 (show ζ ∈ H from hζ)
  rw [hζ₀] at hclose ⊢
  have hmaps : MapsTo (fun y : ℝ => t - y) (Icc 0 t) (Icc 0 t) :=
    fun s hs => ⟨by linarith [hs.2], by linarith [hs.1]⟩
  set c : ℝ := 8 * T / m ^ 2 with hc
  have hexpc : ∀ y ∈ Icc (0 : ℝ) t, Real.exp (2 / (m * (m / 4)) * y) ≤ Real.exp c := by
    intro y hy
    apply Real.exp_le_exp.mpr
    rw [hc, show 2 / (m * (m / 4)) * y = 8 * y / m ^ 2 by field_simp; ring]
    gcongr
    exact hy.2.trans ht.2
  have hsmall : ‖ζ - u t‖ * Real.exp c ≤ m / 2 := by
    calc ‖ζ - u t‖ * Real.exp c ≤ m / 2 * Real.exp (-c) * Real.exp c :=
          mul_le_mul_of_nonneg_right hclose (Real.exp_pos _).le
      _ = m / 2 := by rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
  have hm4 : 0 < m / 4 := by positivity
  -- continuation: `‖v - u‖ < 3m/4` on `[0,t]`
  have claim : ∀ x ∈ Icc (0 : ℝ) t, ‖v (t - x) - u (t - x)‖ < 3 * m / 4 := by
    by_contra hcon
    push_neg at hcon
    set F : ℝ → ℝ := fun x => ‖v (t - x) - u (t - x)‖ with hF
    have hFc : ContinuousOn F (Icc 0 t) :=
      continuous_norm.comp_continuousOn
        ((hv.1.sub hu.1).comp (continuousOn_const.sub continuousOn_id) hmaps)
    set S : Set ℝ := Icc (0 : ℝ) t ∩ F ⁻¹' Ici (3 * m / 4) with hS
    have hSc : IsClosed S := hFc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
    obtain ⟨r0, hr0, hr0'⟩ := hcon
    have hSne : S.Nonempty := ⟨r0, hr0, hr0'⟩
    have hSb : BddBelow S := ⟨0, fun x hx => hx.1.1⟩
    have hmem := hSc.csInf_mem hSne hSb
    set x := sInf S with hx
    have hbefore : ∀ y ∈ Ico (0 : ℝ) x, m ≤ ‖u (t - y)‖ ∧ m / 4 ≤ ‖v (t - y)‖ := by
      intro y hy
      have hyt : y ∈ Icc (0 : ℝ) t := ⟨hy.1, (hy.2.le).trans hmem.1.2⟩
      have hyS : y ∉ S := fun h => absurd (csInf_le hSb h) (not_le.mpr hy.2)
      have hlt : F y < 3 * m / 4 := by
        by_contra h'
        exact hyS ⟨hyt, not_lt.mp h'⟩
      have hur := hul (t - y) (hmaps hyt)
      have := norm_sub_norm_le (u (t - y)) (u (t - y) - v (t - y))
      rw [sub_sub_cancel, norm_sub_rev] at this
      exact ⟨hur, by simp only [hF] at hlt; linarith⟩
    have hg := norm_sol_sub_le_gronwall_back hu hv hmem.1 hm hm4 hbefore
    rw [hvt] at hg
    have h1 := hg.trans (mul_le_mul_of_nonneg_left (hexpc x hmem.1) (norm_nonneg _))
    have hge : 3 * m / 4 ≤ F x := hmem.2
    simp only [hF] at hge
    linarith
  have hfin := norm_sol_sub_le_gronwall_back hu hv htt hm hm4 (fun y hy => by
    have hyt : y ∈ Icc (0 : ℝ) t := ⟨hy.1, hy.2.le⟩
    have hlt := claim y hyt
    have hur := hul (t - y) (hmaps hyt)
    have := norm_sub_norm_le (u (t - y)) (u (t - y) - v (t - y))
    rw [sub_sub_cancel, norm_sub_rev] at this
    exact ⟨hur, by linarith⟩)
  rw [sub_self, hvt, FwdHolo.sol_zero hv ht.1, FwdHolo.sol_zero hu ht.1,
    sub_sub_sub_cancel_right] at hfin
  rw [mul_comm]
  exact hfin.trans (mul_le_mul_of_nonneg_left (hexpc t htt) (norm_nonneg _))

end ASep
end QuantumZipper
