import QuantumZipper.Proofs.Thm11.ForwardClock

/-!
# Force points are boundary values of the centered Loewner map

Design `planning/INFRA-GEO.md` §3–§4, packet GEO-LOEW. If `u` solves QuantumZipper's centered
forward flow (`QuantumZipper.IsForwardSol`, the integral form of (1.7)) from a point `p` on
`[0, T]` — in particular from a real force point `x` before its collision with the driver, which
is Specification (1.11) with `V̂_t = V_t − W_t = u t` — then `f_T = QuantumZipper.fwdMap W T`
extends continuously from `ℍ` to `p` with value `u T`.

## Proof

`u` stays at distance `≥ 2δ` from `0` on `[0, T]` (compactness). The vector field
`y ↦ 2/(y − W_t)` of the uncentered flow `g = f + W` is `2/δ²`-Lipschitz on `{‖y − W_t‖ ≥ δ}`, so
Grönwall (Mathlib `dist_le_of_trajectories_ODE_of_mem`) and a first-exit argument give, for
`‖z − p‖ e^{2T/δ²} < δ`, `‖f_r(z) − u_r‖ ≤ ‖z − p‖ e^{2r/δ²} < δ` for as long as the solution from
`z` exists. Hence `‖f_r(z)‖ ≥ δ`, the clock `∫ ‖f_r(z)‖⁻²` stays `≤ T/δ²`, and `z` is not swallowed
by time `T` (QuantumZipper's `FwdClock.mem_fwdHull_iff_clock`: swallowing makes the clock blow
up). No reflection principle is needed.

## Main results

* `tendsto_fwdMap_of_isForwardSol`: the boundary limit, for any starting point;
* `tendsto_fwdMap_of_isForwardSol_real`: the design statement (real starting point);
* `eqOn_of_isForwardSol`: uniqueness of solutions from any starting point (QuantumZipper's
  `isForwardSol_unique` assumes `0 < Im p`);
* `isForwardSol_conj`, `im_eq_zero_of_isForwardSol_real`: a solution from a real point is real
  (so `V̂_t = u t` is a real process).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped ComplexConjugate

open QuantumZipper (H)

namespace InteractingSLE

variable {W : ℝ → ℝ}

/-- A solution of the centered flow stays at distance `≥ 2δ` from `0` on `[0, T]`. -/
theorem exists_two_mul_le_norm_of_isForwardSol {p : ℂ} {T : ℝ} {u : ℝ → ℂ} (hT : 0 ≤ T)
    (hu : QuantumZipper.IsForwardSol W p T u) :
    ∃ δ > 0, ∀ t ∈ Icc (0 : ℝ) T, 2 * δ ≤ ‖u t‖ := by
  obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hT) hu.1.norm
  refine ⟨‖u t₀‖ / 2, div_pos (norm_pos_iff.2 (hu.2 t₀ ht₀).1) two_pos, fun t ht => ?_⟩
  have : ‖u t₀‖ ≤ ‖u t‖ := hmin ht
  linarith

/-- The Loewner vector field `y ↦ 2/(y − c)` is `2/δ²`-Lipschitz on `{‖y − c‖ ≥ δ}`. -/
theorem lipschitzOnWith_two_div_sub {δ : ℝ} (hδ : 0 < δ) (c : ℝ) :
    LipschitzOnWith (Real.toNNReal (2 / δ ^ 2)) (fun y : ℂ => 2 / (y - c))
      {y : ℂ | δ ≤ ‖y - c‖} := by
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  have hx' : δ ≤ ‖x - c‖ := hx
  have hy' : δ ≤ ‖y - c‖ := hy
  have hx0 : x - c ≠ 0 := norm_pos_iff.1 (hδ.trans_le hx')
  have hy0 : y - c ≠ 0 := norm_pos_iff.1 (hδ.trans_le hy')
  rw [Real.coe_toNNReal _ (by positivity), dist_eq_norm, dist_eq_norm]
  have heq : 2 / (x - c) - 2 / (y - c) = 2 * (y - x) / ((x - c) * (y - c)) := by
    field_simp
    ring
  rw [heq, norm_div, norm_mul, norm_mul, Complex.norm_ofNat, norm_sub_rev y x,
    div_le_iff₀ (by positivity)]
  have hxy : δ ^ 2 ≤ ‖x - c‖ * ‖y - c‖ := by
    rw [sq]
    exact mul_le_mul hx' hy' hδ.le (norm_nonneg _)
  calc 2 * ‖x - y‖ = 2 / δ ^ 2 * ‖x - y‖ * δ ^ 2 := by field_simp
    _ ≤ 2 / δ ^ 2 * ‖x - y‖ * (‖x - c‖ * ‖y - c‖) := by gcongr

/-- **Grönwall comparison** of two solutions that both stay at distance `≥ δ` from `0`. -/
theorem norm_sub_le_of_isForwardSol_of_le_norm (hW : Continuous W) {p z : ℂ} {T s δ : ℝ}
    {u v : ℝ → ℂ}
    (hu : QuantumZipper.IsForwardSol W p T u) (hv : QuantumZipper.IsForwardSol W z s v)
    (hδ : 0 < δ) (hs : 0 ≤ s) (hsT : s ≤ T)
    (hu_low : ∀ r ∈ Ico (0 : ℝ) s, δ ≤ ‖u r‖) (hv_low : ∀ r ∈ Ico (0 : ℝ) s, δ ≤ ‖v r‖) :
    ∀ r ∈ Icc (0 : ℝ) s, ‖v r - u r‖ ≤ ‖z - p‖ * Real.exp (2 / δ ^ 2 * r) := by
  have hWc : Continuous fun r => (W r : ℂ) := Complex.continuous_ofReal.comp hW
  have hT : 0 ≤ T := hs.trans hsT
  have key := dist_le_of_trajectories_ODE_of_mem (v := fun t (y : ℂ) => 2 / (y - W t))
    (s := fun t => {y : ℂ | δ ≤ ‖y - W t‖}) (K := Real.toNNReal (2 / δ ^ 2))
    (f := fun r => v r + W r) (g := fun r => u r + W r) (a := 0) (b := s) (δ := ‖z - p‖)
    (fun t _ => lipschitzOnWith_two_div_sub hδ (W t))
    (hv.1.add hWc.continuousOn)
    (fun t ht => ((QuantumZipper.FwdHolo.hasDerivWithinAt_shift hv
        (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)).congr_deriv
        (by simp only [add_sub_cancel_right]))
    (fun t ht => by
      show δ ≤ ‖v t + W t - W t‖
      rw [add_sub_cancel_right]
      exact hv_low t ht)
    ((hu.1.mono (Icc_subset_Icc_right hsT)).add hWc.continuousOn)
    (fun t ht => ((QuantumZipper.FwdHolo.hasDerivWithinAt_shift hu
        ⟨ht.1, ht.2.le.trans hsT⟩).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ⟨ht.1, ht.2.trans_le hsT⟩)).congr_deriv
        (by simp only [add_sub_cancel_right]))
    (fun t ht => by
      show δ ≤ ‖u t + W t - W t‖
      rw [add_sub_cancel_right]
      exact hu_low t ht)
    (by
      rw [dist_eq_norm, QuantumZipper.FwdHolo.sol_zero hv hs, QuantumZipper.FwdHolo.sol_zero hu hT]
      simp)
  intro r hr
  have h := key r hr
  rw [dist_eq_norm, Real.coe_toNNReal _ (by positivity), sub_zero] at h
  simpa using h

/-- **Stability up to the first exit**: if `u` stays at distance `≥ 2δ` from `0` on `[0, T]` and
`‖z − p‖ e^{2T/δ²} < δ`, any solution from `z` on `[0, s] ⊆ [0, T]` stays within
`‖z − p‖ e^{2r/δ²}` of `u`. -/
theorem norm_sub_le_of_isForwardSol (hW : Continuous W) {p z : ℂ} {T s δ : ℝ} {u v : ℝ → ℂ}
    (hu : QuantumZipper.IsForwardSol W p T u) (hv : QuantumZipper.IsForwardSol W z s v)
    (hδ : 0 < δ) (hs : 0 ≤ s) (hsT : s ≤ T) (hu_low : ∀ r ∈ Icc (0 : ℝ) T, 2 * δ ≤ ‖u r‖)
    (hzp : ‖z - p‖ * Real.exp (2 / δ ^ 2 * T) < δ) :
    ∀ r ∈ Icc (0 : ℝ) s, ‖v r - u r‖ ≤ ‖z - p‖ * Real.exp (2 / δ ^ 2 * r) := by
  have hexp : ∀ r ≤ T, ‖z - p‖ * Real.exp (2 / δ ^ 2 * r) < δ := fun r hr =>
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2
      (mul_le_mul_of_nonneg_left hr (by positivity))) (norm_nonneg _)) hzp
  have hvlow : ∀ r ∈ Icc (0 : ℝ) s, ‖v r - u r‖ < δ → δ ≤ ‖v r‖ := fun r hr h => by
    have h1 := hu_low r ⟨hr.1, hr.2.trans hsT⟩
    have h2 := norm_sub_norm_le (u r) (v r)
    rw [norm_sub_rev] at h2
    linarith
  have hulow : ∀ r ∈ Icc (0 : ℝ) s, δ ≤ ‖u r‖ := fun r hr => by
    have := hu_low r ⟨hr.1, hr.2.trans hsT⟩
    linarith
  have hlt : ∀ r ∈ Icc (0 : ℝ) s, ‖v r - u r‖ < δ := by
    by_contra hcon
    simp only [not_forall, not_lt] at hcon
    obtain ⟨r, hr, hge⟩ := hcon
    set E := Icc (0 : ℝ) s ∩ (fun q => ‖v q - u q‖) ⁻¹' Ici δ with hE
    have hEc : IsClosed E :=
      (hv.1.sub (hu.1.mono (Icc_subset_Icc_right hsT))).norm.preimage_isClosed_of_isClosed
        isClosed_Icc isClosed_Ici
    have hEne : E.Nonempty := ⟨r, hr, hge⟩
    have hEbdd : BddBelow E := ⟨0, fun x hx => hx.1.1⟩
    have hr₁ : sInf E ∈ E := hEc.csInf_mem hEne hEbdd
    have hbefore : ∀ q ∈ Ico (0 : ℝ) (sInf E), ‖v q - u q‖ < δ := fun q hq => by
      by_contra h
      have : sInf E ≤ q := csInf_le hEbdd ⟨⟨hq.1, hq.2.le.trans hr₁.1.2⟩, not_lt.1 h⟩
      linarith [hq.2]
    have hb := norm_sub_le_of_isForwardSol_of_le_norm hW hu
      (QuantumZipper.isForwardSol_restrict hv hr₁.1.1 hr₁.1.2) hδ hr₁.1.1 (hr₁.1.2.trans hsT)
      (fun q hq => hulow q ⟨hq.1, hq.2.le.trans hr₁.1.2⟩)
      (fun q hq => hvlow q ⟨hq.1, hq.2.le.trans hr₁.1.2⟩ (hbefore q hq))
      (sInf E) ⟨hr₁.1.1, le_rfl⟩
    have := hexp (sInf E) (hr₁.1.2.trans hsT)
    have h3 : δ ≤ ‖v (sInf E) - u (sInf E)‖ := hr₁.2
    linarith
  exact norm_sub_le_of_isForwardSol_of_le_norm hW hu hv hδ hs hsT
    (fun q hq => hulow q (Ico_subset_Icc_self hq))
    (fun q hq => hvlow q (Ico_subset_Icc_self hq) (hlt q (Ico_subset_Icc_self hq)))

/-- **No swallowing near a solution**: if `u` stays at distance `≥ 2δ` from `0` on `[0, T]` and
`z ∈ ℍ` satisfies `‖z − p‖ e^{2T/δ²} < δ`, then `z ∉ K_T`. -/
theorem not_mem_fwdHull_of_isForwardSol (hW : Continuous W) {p z : ℂ} {T δ : ℝ} {u : ℝ → ℂ}
    (hu : QuantumZipper.IsForwardSol W p T u) (hδ : 0 < δ)
    (hu_low : ∀ r ∈ Icc (0 : ℝ) T, 2 * δ ≤ ‖u r‖) (hz : 0 < z.im)
    (hzp : ‖z - p‖ * Real.exp (2 / δ ^ 2 * T) < δ) :
    z ∉ QuantumZipper.fwdHull W T := by
  intro hK
  obtain ⟨-, σ, hσT, hσ, hcl⟩ := (QuantumZipper.FwdClock.mem_fwdHull_iff_clock hW).1 hK
  obtain ⟨t, ht0, htσ, hM⟩ := hcl (T / δ ^ 2)
  have hzt : z ∉ QuantumZipper.fwdHull W t := by
    rintro ⟨-, hle⟩
    rw [hσ, ENNReal.ofReal_le_ofReal_iff ht0] at hle
    linarith
  obtain ⟨v, hv⟩ := QuantumZipper.exists_isForwardSol_of_not_mem_fwdHull ht0 hz hzt
  have htT : t ≤ T := htσ.le.trans hσT
  have hb := norm_sub_le_of_isForwardSol hW hu hv hδ ht0 htT hu_low hzp
  have hvlow : ∀ r ∈ Icc (0 : ℝ) t, δ ≤ ‖QuantumZipper.fwdMap W r z‖ := by
    intro r hr
    rw [QuantumZipper.fwdMap_eq hW hz hv hr]
    have h1 := hu_low r ⟨hr.1, hr.2.trans htT⟩
    have h2 := norm_sub_norm_le (u r) (v r)
    rw [norm_sub_rev] at h2
    have h3 := (hb r hr).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2
      (mul_le_mul_of_nonneg_left (hr.2.trans htT) (by positivity))) (norm_nonneg _))
    linarith
  have hclock : QuantumZipper.FwdClock.fwdClock W t z ≤ T / δ ^ 2 := by
    have hI := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t)
      (C := 1 / δ ^ 2) (f := fun r => 1 / ‖QuantumZipper.fwdMap W r z‖ ^ 2) (fun r hr => by
        rw [uIoc_of_le ht0] at hr
        have h := hvlow r ⟨hr.1.le, hr.2⟩
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hδ.le h 2))
    calc QuantumZipper.FwdClock.fwdClock W t z
        ≤ ‖∫ r in (0 : ℝ)..t, 1 / ‖QuantumZipper.fwdMap W r z‖ ^ 2‖ := Real.le_norm_self _
      _ ≤ 1 / δ ^ 2 * |t - 0| := hI
      _ ≤ T / δ ^ 2 := by
        rw [sub_zero, abs_of_nonneg ht0, one_div_mul_eq_div]
        gcongr
  linarith

/-- **Boundary values of `f_T`** at the starting point of any solution of the centered flow on
`[0, T]`: `f_T(z) → u T` as `z → p` inside `ℍ`. -/
theorem tendsto_fwdMap_of_isForwardSol (hW : Continuous W) {p : ℂ} {T : ℝ} {u : ℝ → ℂ}
    (hT : 0 ≤ T) (hu : QuantumZipper.IsForwardSol W p T u) :
    Tendsto (QuantumZipper.fwdMap W T) (𝓝[H] p) (𝓝 (u T)) := by
  obtain ⟨δ, hδ, hlow⟩ := exists_two_mul_le_norm_of_isForwardSol hT hu
  set E := Real.exp (2 / δ ^ 2 * T) with hEdef
  have hE : 0 < E := Real.exp_pos _
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have hm : 0 < min δ ε := lt_min hδ hε
  refine ⟨min δ ε / (2 * E), by positivity, fun z hz hzd => ?_⟩
  rw [dist_eq_norm] at hzd ⊢
  have hzp : ‖z - p‖ * E < min δ ε / 2 := by
    have := mul_lt_mul_of_pos_right hzd hE
    rwa [div_mul_eq_mul_div, mul_comm 2 E, ← div_div, mul_div_assoc, div_self hE.ne',
      mul_one] at this
  have hzp' : ‖z - p‖ * E < δ := hzp.trans_le (by linarith [min_le_left δ ε])
  have hz0 : 0 < z.im := hz
  have hzK := not_mem_fwdHull_of_isForwardSol hW hu hδ hlow hz0 hzp'
  obtain ⟨v, hv⟩ := QuantumZipper.exists_isForwardSol_of_not_mem_fwdHull hT hz0 hzK
  rw [QuantumZipper.fwdMap_eq hW hz0 hv ⟨hT, le_rfl⟩]
  have hb := norm_sub_le_of_isForwardSol hW hu hv hδ hT le_rfl hlow hzp' T ⟨hT, le_rfl⟩
  linarith [min_le_right δ ε]

/-- **Force points are boundary values** (design statement; Specification (1.11)): if `u` solves
the centered flow from a real point `x` on `[0, T]` (before its collision with the driver), then
`f_T` extends continuously to `x` with value `u T`; this identifies `V̂_t = V_t − W_t` with
`f_t(x)`. -/
theorem tendsto_fwdMap_of_isForwardSol_real {W : ℝ → ℝ} (hW : Continuous W) (_hW0 : W 0 = 0)
    {x T : ℝ} {u : ℝ → ℂ} (hT : 0 ≤ T) (hu : QuantumZipper.IsForwardSol W x T u) :
    Tendsto (QuantumZipper.fwdMap W T) (𝓝[H] (x : ℂ)) (𝓝 (u T)) :=
  tendsto_fwdMap_of_isForwardSol hW hT hu

/-- **Uniqueness** of solutions of the centered flow from any starting point (QuantumZipper's
`isForwardSol_unique` assumes `0 < Im p`). -/
theorem eqOn_of_isForwardSol (hW : Continuous W) {p : ℂ} {T : ℝ} {u v : ℝ → ℂ}
    (hu : QuantumZipper.IsForwardSol W p T u) (hv : QuantumZipper.IsForwardSol W p T v) :
    EqOn u v (Icc 0 T) := by
  intro r hr
  have hT : 0 ≤ T := hr.1.trans hr.2
  obtain ⟨δ, hδ, hlow⟩ := exists_two_mul_le_norm_of_isForwardSol hT hu
  have h := norm_sub_le_of_isForwardSol hW hu hv hδ hT le_rfl hlow (by simpa using hδ) r hr
  rw [sub_self, norm_zero, zero_mul] at h
  exact (sub_eq_zero.1 (norm_le_zero_iff.1 h)).symm

/-- The complex conjugate of a solution is a solution from the conjugate point. -/
theorem isForwardSol_conj {p : ℂ} {T : ℝ} {u : ℝ → ℂ}
    (hu : QuantumZipper.IsForwardSol W p T u) :
    QuantumZipper.IsForwardSol W (conj p) T (fun r => conj (u r)) := by
  refine ⟨Complex.continuous_conj.comp_continuousOn hu.1, fun t ht => ⟨?_, ?_⟩⟩
  · exact (map_ne_zero _).2 (hu.2 t ht).1
  · show conj (u t) = conj p - W t + ∫ s in (0 : ℝ)..t, 2 / conj (u s)
    rw [(hu.2 t ht).2, map_add, map_sub, Complex.conj_ofReal, intervalIntegral.integral_of_le ht.1,
      intervalIntegral.integral_of_le ht.1, ← integral_conj]
    simp only [map_div₀, map_ofNat]

/-- A solution of the centered flow from a **real** point is real on `[0, T]` (so the force-point
process `V̂_t = u t` of (1.11) is real-valued). -/
theorem im_eq_zero_of_isForwardSol_real (hW : Continuous W) {x T : ℝ} {u : ℝ → ℂ}
    (hu : QuantumZipper.IsForwardSol W x T u) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    (u t).im = 0 := by
  have hc := isForwardSol_conj hu
  rw [Complex.conj_ofReal] at hc
  have h := eqOn_of_isForwardSol hW hu hc ht
  have := congrArg Complex.im h
  simp only [Complex.conj_im] at this
  linarith

end InteractingSLE
