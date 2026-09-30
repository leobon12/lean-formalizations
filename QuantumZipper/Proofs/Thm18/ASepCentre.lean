import QuantumZipper.Proofs.Loewner.ForwardHolo

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Centre modulus of the forward Loewner maps away from the hull (task ASEP-C)

Deterministic regularity of the centred forward Loewner flow
`u_t = z - W t + ∫_0^t 2/u_s ds` (`IsForwardSol`, `fwdMap` in `QuantumZipper/Loewner/Forward.lean`)
on a compact set of points that are not swallowed before time `T`:

* `exists_fwdMap_lower` (C1): a uniform positive lower bound for `‖fwdMap W s z‖`,
  `z ∈ K`, `s ∈ [0,T]`;
* `norm_fwdMap_sub_le` (C2): the joint modulus
  `‖f_s z - f_{s'} z'‖ ≤ e^{2T/m²}‖z - z'‖ + |W s - W s'| + 2|s - s'|/m`.

Sources. This is the standard regularity of the Loewner ODE away from the hull
(G. F. Lawler, *Conformally invariant processes in the plane*, AMS 2005, §4.1; cf. the
differential inequalities in the proof of A. Kemppainen, *Schramm–Loewner Evolution*,
SpringerBriefs 2017, Lemma 6.7, p. 110). Neither source writes out these two estimates, so the
proofs here are an **own elementary argument**: Grönwall's inequality (mathlib
`norm_le_gronwallBound_of_norm_deriv_right_le`) for the difference of two solutions, whose
derivative is `2/u - 2/v = -2(u - v)/(uv)`; the time increment read off the integral
equation; and, for (C1), a first-exit-time continuation argument plus a finite subcover.
As a by-product we get uniqueness of forward solutions for *every* starting point `z ∈ ℂ`
(`isForwardSol_unique_any`; the repository version `isForwardSol_unique` needs `0 < z.im`).
Neither continuity of `W` nor `W 0 = 0` is needed; the stated theorems keep those hypotheses.
-/

noncomputable section

open MeasureTheory Set Filter Metric
open scoped Topology

namespace QuantumZipper
namespace ASep

/-- **Grönwall comparison of two forward solutions.** If `u` solves from `z` and `v` from `z'`
on `[0,T]`, and `‖u‖ ≥ a`, `‖v‖ ≥ b` on `[0,t)`, then `‖u t - v t‖ ≤ ‖z - z'‖ e^{2t/(ab)}`. -/
theorem norm_sol_sub_le_gronwall {W : ℝ → ℝ} {z z' : ℂ} {T : ℝ} {u v : ℝ → ℂ}
    (hu : IsForwardSol W z T u) (hv : IsForwardSol W z' T v) {t a b : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) (ha : 0 < a) (hb : 0 < b)
    (hab : ∀ r ∈ Ico (0 : ℝ) t, a ≤ ‖u r‖ ∧ b ≤ ‖v r‖) :
    ‖u t - v t‖ ≤ ‖z - z'‖ * Real.exp (2 / (a * b) * t) := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hsub : Icc (0 : ℝ) t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
  set e : ℝ → ℂ := fun r => (u r + (W r : ℂ)) - (v r + (W r : ℂ)) with he
  have he' : ∀ r, e r = u r - v r := fun r => by simp only [he]; ring
  have hcont : ContinuousOn e (Icc 0 t) := by
    refine ((hu.1.sub hv.1).mono hsub).congr ?_
    intro r _
    exact he' r
  have hder : ∀ r ∈ Ico (0 : ℝ) t, HasDerivWithinAt e (2 / u r - 2 / v r) (Ici r) r := by
    intro r hr
    have hrT : r ∈ Icc (0 : ℝ) T := hsub (Ico_subset_Icc_self hr)
    have h1 := (FwdHolo.hasDerivWithinAt_shift hu hrT).sub (FwdHolo.hasDerivWithinAt_shift hv hrT)
    have hrT' : r ∈ Ico (0 : ℝ) T := ⟨hr.1, lt_of_lt_of_le hr.2 ht.2⟩
    exact h1.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem hrT')
  have h0 : ‖e 0‖ ≤ ‖z - z'‖ := by
    rw [he', FwdHolo.sol_zero hu hT, FwdHolo.sol_zero hv hT]
    simp
  have hbound : ∀ r ∈ Ico (0 : ℝ) t, ‖2 / u r - 2 / v r‖ ≤ 2 / (a * b) * ‖e r‖ + 0 := by
    intro r hr
    have hrT : r ∈ Icc (0 : ℝ) T := hsub (Ico_subset_Icc_self hr)
    have hu0 : u r ≠ 0 := (hu.2 r hrT).1
    have hv0 : v r ≠ 0 := (hv.2 r hrT).1
    obtain ⟨hA, hB⟩ := hab r hr
    have hid : 2 / u r - 2 / v r = -(2 * e r) / (u r * v r) := by
      rw [he']; field_simp; ring
    rw [hid, norm_div, norm_neg, norm_mul, norm_mul, add_zero]
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h2, show 2 / (a * b) * ‖e r‖ = 2 * ‖e r‖ / (a * b) by ring]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (mul_le_mul hA hB hb.le (norm_nonneg _))
  have key := norm_le_gronwallBound_of_norm_deriv_right_le hcont hder h0 hbound t
    ⟨ht.1, le_rfl⟩
  rw [gronwallBound_ε0, sub_zero, he'] at key
  exact key

/-- A solution on `[0,T]` is bounded away from `0` there. -/
theorem exists_pos_lower_of_isForwardSol {W : ℝ → ℝ} {z : ℂ} {T : ℝ} {u : ℝ → ℂ}
    (hu : IsForwardSol W z T u) (hT : 0 ≤ T) :
    ∃ a > 0, ∀ r ∈ Icc (0 : ℝ) T, a ≤ ‖u r‖ := by
  obtain ⟨x, hx, hmin⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_isMinOn
    ⟨0, le_rfl, hT⟩ (continuous_norm.comp_continuousOn hu.1)
  exact ⟨‖u x‖, norm_pos_iff.mpr (hu.2 x hx).1, fun r hr => hmin hr⟩

/-- **Uniqueness of forward solutions for every starting point.** -/
theorem isForwardSol_unique_any {W : ℝ → ℝ} {z : ℂ} {T : ℝ} {u v : ℝ → ℂ}
    (hu : IsForwardSol W z T u) (hv : IsForwardSol W z T v) : EqOn u v (Icc 0 T) := by
  intro t ht
  have hT : 0 ≤ T := ht.1.trans ht.2
  obtain ⟨a, ha, hua⟩ := exists_pos_lower_of_isForwardSol hu hT
  obtain ⟨b, hb, hvb⟩ := exists_pos_lower_of_isForwardSol hv hT
  have hsub : Ico (0 : ℝ) t ⊆ Icc 0 T := fun r hr => ⟨hr.1, (hr.2.le).trans ht.2⟩
  have h := norm_sol_sub_le_gronwall hu hv ht ha hb
    (fun r hr => ⟨hua r (hsub hr), hvb r (hsub hr)⟩)
  rw [sub_self, norm_zero, zero_mul] at h
  exact sub_eq_zero.mp (norm_le_zero_iff.mp h)

/-- `fwdMap` agrees with any solution, for every starting point. -/
theorem fwdMap_eq_any {W : ℝ → ℝ} {z : ℂ} {T : ℝ} {u : ℝ → ℂ}
    (hu : IsForwardSol W z T u) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    fwdMap W t z = u t := by
  have hut : IsForwardSol W z t u := isForwardSol_restrict hu ht.1 ht.2
  have hex : ∃ u', IsForwardSol W z t u' := ⟨u, hut⟩
  simp only [fwdMap, dif_pos hex]
  exact isForwardSol_unique_any hex.choose_spec hut (right_mem_Icc.mpr ht.1)

/-- **Time increment.** Read off the integral equation. -/
theorem norm_sol_time_sub_le {W : ℝ → ℝ} {z : ℂ} {T m : ℝ} {u : ℝ → ℂ}
    (hu : IsForwardSol W z T u) (hm : 0 < m) (hlow : ∀ r ∈ Icc (0 : ℝ) T, m ≤ ‖u r‖)
    {s s' : ℝ} (hs : s ∈ Icc (0 : ℝ) T) (hs' : s' ∈ Icc (0 : ℝ) T) :
    ‖u s - u s'‖ ≤ |W s - W s'| + 2 * |s - s'| / m := by
  have hg : ContinuousOn (fun r => (2 : ℂ) / u r) (Icc 0 T) :=
    ContinuousOn.div continuousOn_const hu.1 (fun r hr => (hu.2 r hr).1)
  have hint : ∀ x ∈ Icc (0 : ℝ) T, IntervalIntegrable (fun r => (2 : ℂ) / u r) volume 0 x := by
    intro x hx
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hx.1]
    exact hg.mono (Icc_subset_Icc_right hx.2)
  have hdiff : u s - u s' = -(((W s - W s' : ℝ)) : ℂ) + ∫ r in s'..s, (2 : ℂ) / u r := by
    rw [(hu.2 s hs).2, (hu.2 s' hs').2,
      ← intervalIntegral.integral_interval_sub_left (hint s hs) (hint s' hs')]
    push_cast; ring
  rw [hdiff]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_neg, Complex.norm_real, Real.norm_eq_abs]
  · have hI : ∀ x ∈ Set.uIoc s' s, ‖(2 : ℂ) / u x‖ ≤ 2 / m := by
      intro x hx
      have hxT : x ∈ Icc (0 : ℝ) T := uIcc_subset_Icc hs' hs (uIoc_subset_uIcc hx)
      rw [norm_div]
      have h2 : ‖(2 : ℂ)‖ = 2 := by simp
      rw [h2]
      exact div_le_div_of_nonneg_left (by norm_num) hm (hlow x hxT)
    refine (intervalIntegral.norm_integral_le_of_norm_le_const hI).trans (le_of_eq ?_)
    rw [abs_sub_comm]; ring

/-- **(C2) Joint modulus of the forward maps.** -/
theorem norm_fwdMap_sub_le {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T m : ℝ}
    (hT : 0 ≤ T) (hm : 0 < m)
    {K : Set ℂ} (hsol : ∀ z ∈ K, ∃ u, IsForwardSol W z T u)
    (hlow : ∀ z ∈ K, ∀ s ∈ Set.Icc (0 : ℝ) T, m ≤ ‖fwdMap W s z‖)
    {z z' : ℂ} (hz : z ∈ K) (hz' : z' ∈ K) {s s' : ℝ} (hs : s ∈ Set.Icc 0 T)
    (hs' : s' ∈ Set.Icc 0 T) :
    ‖fwdMap W s z - fwdMap W s' z'‖ ≤
      Real.exp (2 * T / m ^ 2) * ‖z - z'‖ + |W s - W s'| + 2 * |s - s'| / m := by
  clear hW hW0 hT
  obtain ⟨u, hu⟩ := hsol z hz
  obtain ⟨v, hv⟩ := hsol z' hz'
  have hul : ∀ r ∈ Icc (0 : ℝ) T, m ≤ ‖u r‖ := fun r hr => by
    rw [← fwdMap_eq_any hu hr]; exact hlow z hz r hr
  have hvl : ∀ r ∈ Icc (0 : ℝ) T, m ≤ ‖v r‖ := fun r hr => by
    rw [← fwdMap_eq_any hv hr]; exact hlow z' hz' r hr
  rw [fwdMap_eq_any hu hs, fwdMap_eq_any hv hs']
  have hsub : Ico (0 : ℝ) s ⊆ Icc 0 T := fun r hr => ⟨hr.1, (hr.2.le).trans hs.2⟩
  have h1 := norm_sol_sub_le_gronwall hu hv hs hm hm
    (fun r hr => ⟨hul r (hsub hr), hvl r (hsub hr)⟩)
  have h2 := norm_sol_time_sub_le hv hm hvl hs hs'
  have hexp : Real.exp (2 / (m * m) * s) ≤ Real.exp (2 * T / m ^ 2) := by
    apply Real.exp_le_exp.mpr
    rw [show 2 / (m * m) * s = 2 * s / m ^ 2 by ring]
    gcongr
    exact hs.2
  have h1' : ‖u s - v s‖ ≤ Real.exp (2 * T / m ^ 2) * ‖z - z'‖ := by
    rw [mul_comm]
    exact h1.trans (mul_le_mul_of_nonneg_left hexp (norm_nonneg _))
  calc ‖u s - v s'‖ = ‖(u s - v s) + (v s - v s')‖ := by ring_nf
    _ ≤ ‖u s - v s‖ + ‖v s - v s'‖ := norm_add_le _ _
    _ ≤ _ := by linarith

/-- **Local lower bound (continuation argument).** Solutions started close to `z` stay at
distance `≥ a/2` from `0`, where `a` is the minimum of `‖u‖` on `[0,T]`. -/
theorem local_lower_of_isForwardSol {W : ℝ → ℝ} {z : ℂ} {T : ℝ} {u : ℝ → ℂ}
    (hu : IsForwardSol W z T u) (hT : 0 ≤ T) :
    ∃ μ > 0, ∃ δ > 0, ∀ z' : ℂ, ∀ v : ℝ → ℂ, IsForwardSol W z' T v → ‖z' - z‖ < δ →
      ∀ s ∈ Icc (0 : ℝ) T, μ ≤ ‖v s‖ := by
  obtain ⟨a, ha, hua⟩ := exists_pos_lower_of_isForwardSol hu hT
  have ha2 : 0 < a / 2 := by positivity
  set K : ℝ := 2 / (a * (a / 2)) with hK
  refine ⟨a / 2, ha2, a / 2 / Real.exp (K * T), by positivity, ?_⟩
  intro z' v hv hzz s hs
  -- claim: `‖u r - v r‖ < a/2` on `[0,T]`
  have claim : ∀ r ∈ Icc (0 : ℝ) T, ‖u r - v r‖ < a / 2 := by
    by_contra hcon
    push_neg at hcon
    set S : Set ℝ := Icc (0 : ℝ) T ∩ (fun r => ‖u r - v r‖) ⁻¹' Ici (a / 2) with hS
    have hSc : IsClosed S :=
      (continuous_norm.comp_continuousOn (hu.1.sub hv.1)).preimage_isClosed_of_isClosed
        isClosed_Icc isClosed_Ici
    obtain ⟨r0, hr0, hr0'⟩ := hcon
    have hSne : S.Nonempty := ⟨r0, hr0, hr0'⟩
    have hSb : BddBelow S := ⟨0, fun x hx => hx.1.1⟩
    have hmem := hSc.csInf_mem hSne hSb
    set t := sInf S with ht
    have hbefore : ∀ r ∈ Ico (0 : ℝ) t, a ≤ ‖u r‖ ∧ a / 2 ≤ ‖v r‖ := by
      intro r hr
      have hrT : r ∈ Icc (0 : ℝ) T := ⟨hr.1, (hr.2.le).trans hmem.1.2⟩
      have hrS : r ∉ S := fun h => absurd (csInf_le hSb h) (not_le.mpr hr.2)
      have hlt : ‖u r - v r‖ < a / 2 := by
        by_contra h'
        exact hrS ⟨hrT, not_lt.mp h'⟩
      have hur := hua r hrT
      have := norm_sub_norm_le (u r) (u r - v r)
      rw [sub_sub_cancel] at this
      exact ⟨hur, by linarith⟩
    have hg := norm_sol_sub_le_gronwall hu hv hmem.1 ha ha2 hbefore
    have hexp : Real.exp (2 / (a * (a / 2)) * t) ≤ Real.exp (K * T) := by
      apply Real.exp_le_exp.mpr
      rw [hK]
      exact mul_le_mul_of_nonneg_left hmem.1.2 (by positivity)
    have hEpos : 0 < Real.exp (K * T) := Real.exp_pos _
    have hlt : ‖z - z'‖ * Real.exp (K * T) < a / 2 := by
      rw [norm_sub_rev]
      calc ‖z' - z‖ * Real.exp (K * T) < a / 2 / Real.exp (K * T) * Real.exp (K * T) :=
            mul_lt_mul_of_pos_right hzz hEpos
        _ = a / 2 := div_mul_cancel₀ _ hEpos.ne'
    have hge : a / 2 ≤ ‖u t - v t‖ := hmem.2
    have := hg.trans (mul_le_mul_of_nonneg_left hexp (norm_nonneg _))
    linarith
  have h1 := claim s hs
  have h2 := hua s hs
  have := norm_sub_norm_le (u s) (u s - v s)
  rw [sub_sub_cancel] at this
  linarith

/-- **(C1) Uniform lower bound on a compact set of non-swallowed points.** -/
theorem exists_fwdMap_lower {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {T : ℝ}
    (hT : 0 ≤ T) {K : Set ℂ} (hK : IsCompact K) (hsol : ∀ z ∈ K, ∃ u, IsForwardSol W z T u) :
    ∃ m : ℝ, 0 < m ∧ ∀ z ∈ K, ∀ s ∈ Set.Icc (0 : ℝ) T, m ≤ ‖fwdMap W s z‖ := by
  clear hW hW0
  have hloc : ∀ z ∈ K, ∃ μ > 0, ∃ δ > 0, ∀ z' ∈ K, dist z' z < δ →
      ∀ s ∈ Icc (0 : ℝ) T, μ ≤ ‖fwdMap W s z'‖ := by
    intro z hz
    obtain ⟨u, hu⟩ := hsol z hz
    obtain ⟨μ, hμ, δ, hδ, h⟩ := local_lower_of_isForwardSol hu hT
    refine ⟨μ, hμ, δ, hδ, fun z' hz' hd s hs => ?_⟩
    obtain ⟨v, hv⟩ := hsol z' hz'
    rw [fwdMap_eq_any hv hs]
    exact h z' v hv (by rwa [← dist_eq_norm]) s hs
  choose! μ hμ δ hδ hh using hloc
  obtain ⟨t, htK, hcover⟩ :=
    hK.elim_nhds_subcover (fun z => ball z (δ z)) (fun z hz => ball_mem_nhds z (hδ z hz))
  rcases t.eq_empty_or_nonempty with h | h
  · refine ⟨1, one_pos, fun z hz => ?_⟩
    have := hcover hz
    simp [h] at this
  · obtain ⟨z0, hz0, hmin⟩ := t.exists_min_image μ h
    refine ⟨μ z0, hμ z0 (htK z0 hz0), fun z' hz' s hs => ?_⟩
    have hc := hcover hz'
    rw [mem_iUnion₂] at hc
    obtain ⟨x, hx, hxz⟩ := hc
    exact (hmin x hx).trans (hh x (htK x hx) z' hz' (mem_ball.mp hxz) s hs)

end ASep
end QuantumZipper
