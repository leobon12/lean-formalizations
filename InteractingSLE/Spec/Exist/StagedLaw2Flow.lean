/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import QuantumZipper.Proofs.Loewner.ForwardFlow
import QuantumZipper.Proofs.Loewner.ForwardHolo
import QuantumZipper.Proofs.Zipper.F1Side
import InteractingSLE.Foundations.Loewner.RealPoints
import InteractingSLE.Spec.Ito.Loewner

/-!
# The forward Loewner map is Borel in the driver, the time and the starting point

Packet PROVE-STAGEDLAW2 (`RunMeasStatement`, the deterministic measurability of a staged run). The chart of a
staged history composes forward Loewner maps `f_T = QuantumZipper.fwdMap W T` at **arbitrary** complex points (real
points, swallowed points, junk values), with random drivers and random times. This file shows that
`(W, T, y) ↦ f_T(y)` and the event "a solution exists on `[0, T]`" are measurable, for every starting point `y ∈ ℂ`.

* `continuousOn_driver_of_isForwardSol`: a solution on `[0, T]` forces the driver to be continuous there;
* `isForwardSol_scale`, `fwdMap_scale`: Brownian scaling `u ↦ u(c ·)/√c` reduces every time to `1`;
* `norm_sub_le_of_isForwardSol_two`: Grönwall comparison of two solutions with different drivers and starting points;
* `isClosed_solSet`, `continuousOn_fwdMap_solSet`: the pairs (path on `[0, T]`, starting point) with a solution
  staying at distance `≥ c` from `0` form a closed set, on which `f_T` is continuous; hence
  `measurableSet_aliveSet'`, `measurable_fwdMap_path` (an `F_σ` set and a piecewise continuous map);
* **`measurable_fwdMap_param`**: for a family of continuous drivers `W a` (vanishing at `0`, measurable at each
  time), a measurable time `τ a ≥ 0` and a measurable starting point `y a`, the map `a ↦ f_{τ a}(y a)` and the event
  "a solution exists" are measurable.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Exist

namespace StagedLaw

open QuantumZipper

/-! ### Elementary facts -/

section Basic

variable {W : ℝ → ℝ} {y : ℂ} {T : ℝ} {u : ℝ → ℂ}

/-- **A solution forces a continuous driver**: `W = y − u + ∫ 2/u` on `[0, T]`. -/
theorem continuousOn_driver_of_isForwardSol (hu : IsForwardSol W y T u) : ContinuousOn W (Icc 0 T) := by
  intro t ht
  have h1 := (FwdHolo.hasDerivWithinAt_shift hu ht).continuousWithinAt
  have h3 : ContinuousWithinAt (fun s => ((u s + (W s : ℂ)) - u s).re) (Icc 0 T) t :=
    Complex.continuous_re.continuousAt.comp_continuousWithinAt (h1.sub (hu.1 t ht))
  simpa using h3

/-- At time `0` a solution exists iff `y ≠ W 0`. -/
theorem exists_isForwardSol_zero_iff : (∃ u, IsForwardSol W y 0 u) ↔ y ≠ W 0 := by
  constructor
  · rintro ⟨u, hu⟩
    have h := hu.2 0 ⟨le_rfl, le_rfl⟩
    rw [intervalIntegral.integral_same, add_zero] at h
    intro hy
    exact h.1 (by rw [h.2, hy, sub_self])
  · intro hy
    refine ⟨fun _ => y - W 0, continuousOn_const, fun t ht => ?_⟩
    have ht0 : t = 0 := le_antisymm ht.2 ht.1
    subst ht0
    rw [intervalIntegral.integral_same, add_zero]
    exact ⟨sub_ne_zero.2 hy, rfl⟩

/-- The forward map vanishes when no solution exists (junk value). -/
theorem fwdMap_of_not (h : ¬ ∃ u, IsForwardSol W y T u) : fwdMap W T y = 0 := by
  simp only [fwdMap, h, ↓reduceDIte]

/-- **At time `0` the forward map is the identity** when `W 0 = 0`. -/
theorem fwdMap_zero_time (hW0 : W 0 = 0) (y : ℂ) : fwdMap W 0 y = y := by
  by_cases hy : y = 0
  · subst hy
    exact fwdMap_of_not fun h => absurd (exists_isForwardSol_zero_iff.1 h) (by rw [hW0]; simp)
  · have hex : ∃ u, IsForwardSol W y 0 u := exists_isForwardSol_zero_iff.2 (by rw [hW0]; exact_mod_cast hy)
    obtain ⟨u, hu⟩ := hex
    rw [F1.fwdMap_eq_of_isForwardSol hu ⟨le_rfl, le_rfl⟩]
    have h := hu.2 0 ⟨le_rfl, le_rfl⟩
    rw [intervalIntegral.integral_same, add_zero, hW0] at h
    rw [h.2]
    simp

end Basic

/-! ### Brownian scaling -/

section Scale

/-- **Brownian scaling of the forward flow**: a solution on `[0, c S]` gives the solution `u(c ·)/√c` on `[0, S]`
for the driver `W(c ·)/√c` from `y/√c`. -/
theorem isForwardSol_scale {W : ℝ → ℝ} {y : ℂ} {c S : ℝ} (hc : 0 < c) {u : ℝ → ℂ}
    (hu : IsForwardSol W y (c * S) u) :
    IsForwardSol (fun s => W (c * s) / Real.sqrt c) (y / Real.sqrt c) S (fun s => u (c * s) / Real.sqrt c) := by
  have hsq : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have hsq' : (Real.sqrt c : ℂ) ≠ 0 := by exact_mod_cast hsq.ne'
  have hmaps : MapsTo (fun s => c * s) (Icc 0 S) (Icc 0 (c * S)) := fun s hs =>
    ⟨mul_nonneg hc.le hs.1, mul_le_mul_of_nonneg_left hs.2 hc.le⟩
  refine ⟨(hu.1.comp (continuousOn_const.mul continuousOn_id) hmaps).div_const _, fun s hs => ⟨?_, ?_⟩⟩
  · exact div_ne_zero (hu.2 _ (hmaps hs)).1 hsq'
  · have h : u (c * s) = y - W (c * s) + ∫ r in (0 : ℝ)..c * s, 2 / u r := (hu.2 _ (hmaps hs)).2
    have hint : ∫ σ in (0 : ℝ)..s, (2 : ℂ) / (u (c * σ) / Real.sqrt c) =
        (Real.sqrt c : ℂ) * ((c : ℂ)⁻¹ * ∫ r in (0 : ℝ)..c * s, (2 : ℂ) / u r) := by
      have e : (fun σ => (2 : ℂ) / (u (c * σ) / Real.sqrt c)) =
          fun σ => (Real.sqrt c : ℂ) * ((2 : ℂ) / u (c * σ)) := by
        funext σ
        field_simp
      rw [e, intervalIntegral.integral_const_mul]
      congr 1
      have h2 := intervalIntegral.integral_comp_mul_left (fun r => (2 : ℂ) / u r) hc.ne' (a := 0) (b := s)
      simp only [mul_zero] at h2
      rw [h2, Complex.real_smul]
      push_cast
      ring
    show u (c * s) / Real.sqrt c = y / Real.sqrt c - ((W (c * s) / Real.sqrt c : ℝ) : ℂ) +
      ∫ σ in (0 : ℝ)..s, (2 : ℂ) / (u (c * σ) / Real.sqrt c)
    rw [hint, h]
    have hcc : (c : ℂ) = (Real.sqrt c : ℂ) * (Real.sqrt c : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hc.le]
    push_cast
    rw [hcc]
    field_simp

theorem sqrt_inv_mul_sqrt {c : ℝ} (hc : 0 < c) : Real.sqrt c⁻¹ * Real.sqrt c = 1 := by
  rw [Real.sqrt_inv, inv_mul_cancel₀ (Real.sqrt_pos.2 hc).ne']

/-- **Scaling of the forward map**: `f_T(y) = √T · f̃_1(y/√T)` for the scaled driver `W̃ = W(T ·)/√T`. -/
theorem fwdMap_scale (W : ℝ → ℝ) {T : ℝ} (hT : 0 < T) (y : ℂ) :
    fwdMap W T y = Real.sqrt T * fwdMap (fun s => W (T * s) / Real.sqrt T) 1 (y / Real.sqrt T) ∧
      ((∃ u, IsForwardSol W y T u) ↔
        ∃ u, IsForwardSol (fun s => W (T * s) / Real.sqrt T) (y / Real.sqrt T) 1 u) := by
  have hsq : 0 < Real.sqrt T := Real.sqrt_pos.2 hT
  have hsq' : (Real.sqrt T : ℂ) ≠ 0 := by exact_mod_cast hsq.ne'
  have hiff : (∃ u, IsForwardSol W y T u) ↔
      ∃ u, IsForwardSol (fun s => W (T * s) / Real.sqrt T) (y / Real.sqrt T) 1 u := by
    constructor
    · rintro ⟨u, hu⟩
      rw [← mul_one T] at hu
      exact ⟨_, isForwardSol_scale hT hu⟩
    · rintro ⟨v, hv⟩
      have hT' : 0 < T⁻¹ := inv_pos.2 hT
      have h1 : (1 : ℝ) = T⁻¹ * T := (inv_mul_cancel₀ hT.ne').symm
      rw [h1] at hv
      have h2 := isForwardSol_scale hT' hv
      refine ⟨fun s => v (T⁻¹ * s) / Real.sqrt T⁻¹, ?_⟩
      have eW : (fun s => (fun s => W (T * s) / Real.sqrt T) (T⁻¹ * s) / Real.sqrt T⁻¹) = W := by
        funext s
        simp only
        rw [← mul_assoc, mul_inv_cancel₀ hT.ne', one_mul, div_div, mul_comm, sqrt_inv_mul_sqrt hT, div_one]
      have ey : y / Real.sqrt T / Real.sqrt T⁻¹ = y := by
        rw [div_div, ← Complex.ofReal_mul, mul_comm, sqrt_inv_mul_sqrt hT, Complex.ofReal_one, div_one]
      rw [eW, ey] at h2
      exact h2
  refine ⟨?_, hiff⟩
  by_cases hex : ∃ u, IsForwardSol W y T u
  · obtain ⟨u, hu⟩ := hex
    have hu' := hu
    rw [← mul_one T] at hu'
    have hs := isForwardSol_scale hT hu'
    rw [F1.fwdMap_eq_of_isForwardSol hu ⟨hT.le, le_rfl⟩, F1.fwdMap_eq_of_isForwardSol hs ⟨zero_le_one, le_rfl⟩,
      mul_one]
    field_simp
  · rw [fwdMap_of_not hex, fwdMap_of_not (fun h => hex (hiff.2 h)), mul_zero]

end Scale


/-! ### Grönwall comparison with two drivers -/

section Gronwall

/-- `w ↦ 2/w` is `2/δ²`-Lipschitz on `{‖w‖ ≥ δ}`. -/
theorem norm_two_div_sub_two_div_le {a b : ℂ} {δ : ℝ} (hδ : 0 < δ) (ha : δ ≤ ‖a‖) (hb : δ ≤ ‖b‖) :
    ‖2 / a - 2 / b‖ ≤ 2 / δ ^ 2 * ‖a - b‖ := by
  have ha0 : a ≠ 0 := norm_pos_iff.1 (hδ.trans_le ha)
  have hb0 : b ≠ 0 := norm_pos_iff.1 (hδ.trans_le hb)
  have heq : 2 / a - 2 / b = 2 * (b - a) / (a * b) := by field_simp
  rw [heq, norm_div, norm_mul, norm_mul, Complex.norm_ofNat, norm_sub_rev b a, div_le_iff₀ (by positivity)]
  have hab : δ ^ 2 ≤ ‖a‖ * ‖b‖ := by rw [sq]; exact mul_le_mul ha hb hδ.le (norm_nonneg _)
  calc 2 * ‖a - b‖ = 2 / δ ^ 2 * ‖a - b‖ * δ ^ 2 := by field_simp
    _ ≤ 2 / δ ^ 2 * ‖a - b‖ * (‖a‖ * ‖b‖) := by gcongr

/-- **Grönwall comparison of two solutions with different drivers and starting points**, both at distance `≥ 2δ`
from `0`, the drivers `ε`-close on `[0, T]` with `ε ≤ δ`. -/
theorem norm_sub_le_of_isForwardSol_two {W₁ W₂ : ℝ → ℝ} {y₁ y₂ : ℂ} {T δ ε : ℝ} {u₁ u₂ : ℝ → ℂ}
    (h₁ : IsForwardSol W₁ y₁ T u₁) (h₂ : IsForwardSol W₂ y₂ T u₂) (hδ : 0 < δ)
    (hl₁ : ∀ t ∈ Icc (0 : ℝ) T, 2 * δ ≤ ‖u₁ t‖) (hl₂ : ∀ t ∈ Icc (0 : ℝ) T, 2 * δ ≤ ‖u₂ t‖)
    (hε : ∀ t ∈ Icc (0 : ℝ) T, |W₁ t - W₂ t| ≤ ε) (hεδ : ε ≤ δ) :
    ∀ t ∈ Icc (0 : ℝ) T, ‖u₁ t - u₂ t‖ ≤ (‖y₁ - y₂‖ + ε) * Real.exp (2 / δ ^ 2 * T) + ε := by
  rcases lt_or_ge T 0 with hT | hT
  · intro t ht
    exact absurd (ht.1.trans ht.2) (not_le.2 hT)
  have hW₁c : ContinuousOn (fun r => (W₁ r : ℂ)) (Icc 0 T) :=
    Complex.continuous_ofReal.comp_continuousOn (continuousOn_driver_of_isForwardSol h₁)
  have hW₂c : ContinuousOn (fun r => (W₂ r : ℂ)) (Icc 0 T) :=
    Complex.continuous_ofReal.comp_continuousOn (continuousOn_driver_of_isForwardSol h₂)
  have hWε : ∀ t ∈ Icc (0 : ℝ) T, ‖(W₁ t : ℂ) - W₂ t‖ ≤ ε := fun t ht => by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]; exact hε t ht
  have hK : ((Real.toNNReal (2 / δ ^ 2) : ℝ≥0) : ℝ) = 2 / δ ^ 2 := Real.coe_toNNReal _ (by positivity)
  have key := dist_le_of_approx_trajectories_ODE_of_mem (v := fun t (w : ℂ) => 2 / (w - W₁ t))
    (s := fun t => {w : ℂ | δ ≤ ‖w - W₁ t‖}) (K := Real.toNNReal (2 / δ ^ 2))
    (f := fun r => u₁ r + W₁ r) (g := fun r => u₂ r + W₂ r) (f' := fun r => 2 / u₁ r)
    (g' := fun r => 2 / u₂ r) (a := 0) (b := T) (δ := ‖y₁ - y₂‖) (εf := 0) (εg := 2 / δ ^ 2 * ε)
    (fun t _ => lipschitzOnWith_two_div_sub hδ (W₁ t)) (h₁.1.add hW₁c)
    (fun t ht => (FwdHolo.hasDerivWithinAt_shift h₁ (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht))
    (fun t _ => by simp only [add_sub_cancel_right, dist_self, le_refl])
    (fun t ht => by
      show δ ≤ ‖u₁ t + W₁ t - W₁ t‖
      rw [add_sub_cancel_right]
      linarith [hl₁ t (Ico_subset_Icc_self ht), norm_nonneg (u₁ t)])
    (h₂.1.add hW₂c)
    (fun t ht => (FwdHolo.hasDerivWithinAt_shift h₂ (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht))
    (fun t ht => by
      have ht' := Ico_subset_Icc_self ht
      have h1 : δ ≤ ‖u₂ t‖ := by linarith [hl₂ t ht', norm_nonneg (u₂ t)]
      have h2 : δ ≤ ‖u₂ t + W₂ t - W₁ t‖ := by
        have := norm_sub_norm_le (u₂ t) ((W₁ t : ℂ) - W₂ t)
        have e : u₂ t + W₂ t - W₁ t = u₂ t - ((W₁ t : ℂ) - W₂ t) := by ring
        rw [e]
        linarith [hl₂ t ht', hWε t ht']
      rw [dist_eq_norm]
      refine (norm_two_div_sub_two_div_le hδ h1 h2).trans ?_
      have e : u₂ t - (u₂ t + W₂ t - W₁ t) = (W₁ t : ℂ) - W₂ t := by ring
      rw [e]
      exact mul_le_mul_of_nonneg_left (hWε t ht') (by positivity))
    (fun t ht => by
      show δ ≤ ‖u₂ t + W₂ t - W₁ t‖
      have ht' := Ico_subset_Icc_self ht
      have := norm_sub_norm_le (u₂ t) ((W₁ t : ℂ) - W₂ t)
      have e : u₂ t + W₂ t - W₁ t = u₂ t - ((W₁ t : ℂ) - W₂ t) := by ring
      rw [e]
      linarith [hl₂ t ht', hWε t ht'])
    (by
      rw [dist_eq_norm, FwdHolo.sol_zero h₁ hT, FwdHolo.sol_zero h₂ hT]
      simp)
  intro t ht
  have h := key t ht
  rw [hK, zero_add, sub_zero, dist_eq_norm] at h
  have hgb : gronwallBound ‖y₁ - y₂‖ (2 / δ ^ 2) (2 / δ ^ 2 * ε) t ≤
      (‖y₁ - y₂‖ + ε) * Real.exp (2 / δ ^ 2 * T) := by
    have hK0 : (2 / δ ^ 2 : ℝ) ≠ 0 := by positivity
    rw [gronwallBound_of_K_ne_0 hK0]
    have hε0 : 0 ≤ ε := (abs_nonneg _).trans (hε t ht)
    have he : Real.exp (2 / δ ^ 2 * t) ≤ Real.exp (2 / δ ^ 2 * T) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ht.2 (by positivity))
    have he1 : 1 ≤ Real.exp (2 / δ ^ 2 * t) := Real.one_le_exp (by have := ht.1; positivity)
    simp only
    rw [mul_div_cancel_left₀ _ hK0]
    nlinarith [norm_nonneg (y₁ - y₂)]
  calc ‖u₁ t - u₂ t‖ = ‖(u₁ t + W₁ t - (u₂ t + W₂ t)) - ((W₁ t : ℂ) - W₂ t)‖ := by ring_nf
    _ ≤ ‖u₁ t + W₁ t - (u₂ t + W₂ t)‖ + ‖(W₁ t : ℂ) - W₂ t‖ := norm_sub_le _ _
    _ ≤ _ := add_le_add (h.trans hgb) (hWε t ht)

end Gronwall


/-! ### The solution sets on path space -/

section PathSpace

variable {T : ℝ} (hT : 0 ≤ T)

/-- Pairs (driver path on `[0, T]`, starting point) with a solution on `[0, T]` that stays at distance `≥ c`
from `0`. -/
def solSet (c : ℝ) : Set (C(Icc (0 : ℝ) T, ℝ) × ℂ) :=
  {p | ∃ u, IsForwardSol (extIccPath hT p.1) p.2 T u ∧ ∀ t ∈ Icc (0 : ℝ) T, c ≤ ‖u t‖}

theorem abs_extIccPath_sub_le (g g' : C(Icc (0 : ℝ) T, ℝ)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    |extIccPath hT g t - extIccPath hT g' t| ≤ dist g g' := by
  rw [extIccPath_of_mem hT g ht, extIccPath_of_mem hT g' ht, ← Real.dist_eq]
  exact ContinuousMap.dist_apply_le_dist _

/-- The comparison bound on `solSet (2δ)`. -/
theorem norm_sub_le_of_solSet {δ : ℝ} (hδ : 0 < δ) {p p' : C(Icc (0 : ℝ) T, ℝ) × ℂ} {u u' : ℝ → ℂ}
    (hu : IsForwardSol (extIccPath hT p.1) p.2 T u) (hl : ∀ t ∈ Icc (0 : ℝ) T, 2 * δ ≤ ‖u t‖)
    (hu' : IsForwardSol (extIccPath hT p'.1) p'.2 T u') (hl' : ∀ t ∈ Icc (0 : ℝ) T, 2 * δ ≤ ‖u' t‖)
    (hd : dist p.1 p'.1 ≤ δ) : ∀ t ∈ Icc (0 : ℝ) T,
      ‖u t - u' t‖ ≤ (‖p.2 - p'.2‖ + dist p.1 p'.1) * Real.exp (2 / δ ^ 2 * T) + dist p.1 p'.1 :=
  norm_sub_le_of_isForwardSol_two hu hu' hδ hl hl' (fun _ ht => abs_extIccPath_sub_le hT p.1 p'.1 ht) hd

/-- **The solution sets are closed** (uniform limits of solutions bounded away from `0` are solutions). -/
theorem isClosed_solSet {c : ℝ} (hc : 0 < c) : IsClosed (solSet hT c) := by
  refine isClosed_of_closure_subset fun p hp => ?_
  obtain ⟨q, hq, hlim⟩ := mem_closure_iff_seq_limit.1 hp
  choose u hu hl using hq
  set δ := c / 2 with hδdef
  have hδ : 0 < δ := half_pos hc
  have hl2 : ∀ n, ∀ t ∈ Icc (0 : ℝ) T, 2 * δ ≤ ‖u n t‖ := fun n t ht => by
    rw [hδdef, mul_div_cancel₀ _ two_ne_zero]; exact hl n t ht
  set E := Real.exp (2 / δ ^ 2 * T) with hE
  have hE0 : 0 < E := Real.exp_pos _
  -- the distance of `q n` to `p`
  set e : ℕ → ℝ := fun n => ‖(q n).2 - p.2‖ + dist (q n).1 p.1 with hedef
  have he0 : ∀ n, 0 ≤ e n := fun n => by positivity
  have he : Tendsto e atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => ‖(q n).2 - p.2‖) atTop (𝓝 0) := by
      have := ((continuous_snd.tendsto p).comp hlim).sub_const p.2
      rw [sub_self] at this
      simpa using this.norm
    have h2 : Tendsto (fun n => dist (q n).1 p.1) atTop (𝓝 0) := by
      have := (continuous_fst.tendsto p).comp hlim
      exact (tendsto_iff_dist_tendsto_zero.1 this)
    simpa using h1.add h2
  -- pairwise bound
  have hpair : ∀ n m, e n + e m ≤ δ → ∀ t ∈ Icc (0 : ℝ) T,
      ‖u n t - u m t‖ ≤ (e n + e m) * (2 * E + 1) := by
    intro n m hnm t ht
    have hd : dist (q n).1 (q m).1 ≤ e n + e m := by
      have := dist_triangle_right (q n).1 (q m).1 p.1
      simp only [hedef]; linarith [norm_nonneg ((q n).2 - p.2), norm_nonneg ((q m).2 - p.2)]
    have hy : ‖(q n).2 - (q m).2‖ ≤ e n + e m := by
      have := norm_sub_le_norm_sub_add_norm_sub (q n).2 p.2 (q m).2
      rw [norm_sub_rev p.2] at this
      simp only [hedef]; linarith [dist_nonneg (x := (q n).1) (y := p.1), dist_nonneg (x := (q m).1) (y := p.1)]
    have h := norm_sub_le_of_solSet hT hδ (hu n) (hl2 n) (hu m) (hl2 m) (hd.trans hnm) t ht
    calc _ ≤ _ := h
      _ ≤ ((e n + e m) + (e n + e m)) * E + (e n + e m) := by gcongr
      _ = (e n + e m) * (2 * E + 1) := by ring
  -- eventually small
  have hev : ∀ η > 0, ∀ᶠ n in atTop, e n < η := fun η hη => (he.eventually (gt_mem_nhds hη))
  -- pointwise Cauchy
  have hcauchy : ∀ t ∈ Icc (0 : ℝ) T, CauchySeq fun n => u n t := by
    intro t ht
    rw [Metric.cauchySeq_iff']
    intro η hη
    have hη' : 0 < min (η / (2 * (2 * E + 1))) (δ / 2) := lt_min (by positivity) (half_pos hδ)
    obtain ⟨N, hN⟩ := (hev _ hη').exists_forall_of_atTop
    refine ⟨N, fun n hn => ?_⟩
    have h1 := hN n hn
    have h2 := hN N le_rfl
    have hsum : e n + e N ≤ δ := by linarith [min_le_right (η / (2 * (2 * E + 1))) (δ / 2)]
    rw [dist_eq_norm]
    calc _ ≤ (e n + e N) * (2 * E + 1) := hpair n N hsum t ht
      _ < (η / (2 * (2 * E + 1)) + η / (2 * (2 * E + 1))) * (2 * E + 1) := by
        gcongr
        · linarith [min_le_left (η / (2 * (2 * E + 1))) (δ / 2)]
        · linarith [min_le_left (η / (2 * (2 * E + 1))) (δ / 2)]
      _ = η := by field_simp; ring
  choose v hv using fun t (ht : t ∈ Icc (0 : ℝ) T) => cauchySeq_tendsto_of_complete (hcauchy t ht)
  set ū : ℝ → ℂ := fun t => if ht : t ∈ Icc (0 : ℝ) T then v t ht else 0 with hūdef
  have hū : ∀ t (ht : t ∈ Icc (0 : ℝ) T), Tendsto (fun n => u n t) atTop (𝓝 (ū t)) := fun t ht => by
    simp only [hūdef, ht, ↓reduceDIte]; exact hv t ht
  -- the uniform bound
  have hunif : ∀ n, e n ≤ δ / 2 → ∀ t ∈ Icc (0 : ℝ) T, ‖u n t - ū t‖ ≤ e n * (2 * E + 1) := by
    intro n hn t ht
    have hlim1 : Tendsto (fun m => ‖u n t - u m t‖) atTop (𝓝 ‖u n t - ū t‖) :=
      ((hū t ht).const_sub (u n t)).norm
    have hlim2 : Tendsto (fun m => (e n + e m) * (2 * E + 1)) atTop (𝓝 ((e n + 0) * (2 * E + 1))) :=
      ((he.const_add (e n)).mul_const _)
    rw [add_zero] at hlim2
    refine le_of_tendsto_of_tendsto hlim1 hlim2 ?_
    filter_upwards [hev (δ / 2) (half_pos hδ)] with m hm
    exact hpair n m (by linarith) t ht
  have hunif' : TendstoUniformlyOn u ū atTop (Icc 0 T) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro η hη
    have hη' : 0 < min (η / (2 * (2 * E + 1))) (δ / 2) := lt_min (by positivity) (half_pos hδ)
    filter_upwards [hev _ hη'] with n hn t ht
    rw [dist_eq_norm, norm_sub_rev]
    calc _ ≤ e n * (2 * E + 1) := hunif n (hn.le.trans (min_le_right _ _)) t ht
      _ ≤ η / (2 * (2 * E + 1)) * (2 * E + 1) := by gcongr; exact hn.le.trans (min_le_left _ _)
      _ < η := by rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]; nlinarith
  have hūc : ContinuousOn ū (Icc 0 T) :=
    hunif'.continuousOn (Eventually.of_forall fun n => (hu n).1).frequently
  have hūl : ∀ t ∈ Icc (0 : ℝ) T, c ≤ ‖ū t‖ := fun t ht =>
    ge_of_tendsto (hū t ht).norm (Eventually.of_forall fun n => hl n t ht)
  refine ⟨ū, ⟨hūc, fun t ht => ⟨fun h0 => ?_, ?_⟩⟩, hūl⟩
  · have := hūl t ht
    rw [h0, norm_zero] at this
    linarith
  -- the integral equation in the limit
  have ht' : Icc (0 : ℝ) t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
  have hcl : ∀ n, ContinuousOn (fun s => (2 : ℂ) / u n s) (Icc 0 T) := fun n =>
    continuousOn_const.div (hu n).1 fun s hs => ((hu n).2 s hs).1
  have hcū : ContinuousOn (fun s => (2 : ℂ) / ū s) (Icc 0 T) :=
    continuousOn_const.div hūc fun s hs h0 => by
      have := hūl s hs; rw [h0, norm_zero] at this; linarith
  have hint : ∀ n, IntervalIntegrable (fun s => (2 : ℂ) / u n s) volume 0 t := fun n =>
    ((hcl n).mono (by rw [uIcc_of_le ht.1]; exact ht')).intervalIntegrable
  have hintū : IntervalIntegrable (fun s => (2 : ℂ) / ū s) volume 0 t :=
    (hcū.mono (by rw [uIcc_of_le ht.1]; exact ht')).intervalIntegrable
  have hI : Tendsto (fun n => ∫ s in (0 : ℝ)..t, (2 : ℂ) / u n s) atTop
      (𝓝 (∫ s in (0 : ℝ)..t, (2 : ℂ) / ū s)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hb : Tendsto (fun n => 2 / δ ^ 2 * (e n * (2 * E + 1)) * |t - 0|) atTop (𝓝 0) := by
      have := ((he.mul_const (2 * E + 1)).const_mul (2 / δ ^ 2)).mul_const |t - 0|
      simpa using this
    refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hb
    filter_upwards [hev (δ / 2) (half_pos hδ)] with n hn
    rw [← intervalIntegral.integral_sub (hint n) hintū]
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun s hs => ?_
    have hs' : s ∈ Icc (0 : ℝ) T := ht' (by rw [uIoc_of_le ht.1] at hs; exact ⟨hs.1.le, hs.2⟩)
    have hδc : δ ≤ c := by rw [hδdef]; linarith
    refine (norm_two_div_sub_two_div_le hδ ((hδc.trans (hl n s hs'))) (hδc.trans (hūl s hs'))).trans ?_
    exact mul_le_mul_of_nonneg_left (hunif n hn.le s hs') (by positivity)
  have hW : Tendsto (fun n => ((extIccPath hT (q n).1 t : ℝ) : ℂ)) atTop (𝓝 ((extIccPath hT p.1 t : ℝ) : ℂ)) := by
    simp only [extIccPath_of_mem hT _ ht]
    have := ((continuous_eval_const (⟨t, ht⟩ : Icc (0 : ℝ) T)).tendsto p.1).comp
      ((continuous_fst.tendsto p).comp hlim)
    exact (Complex.continuous_ofReal.tendsto _).comp this
  have hy : Tendsto (fun n => (q n).2) atTop (𝓝 p.2) := (continuous_snd.tendsto p).comp hlim
  have hrhs := (hy.sub hW).add hI
  have hlhs : Tendsto (fun n => u n t) atTop _ := hū t ht
  have heq : (fun n => u n t) = fun n => (q n).2 - extIccPath hT (q n).1 t + ∫ s in (0 : ℝ)..t, (2 : ℂ) / u n s :=
    funext fun n => ((hu n).2 t ht).2
  rw [heq] at hlhs
  exact tendsto_nhds_unique hlhs hrhs

/-- **On `solSet c` the forward map is continuous.** -/
theorem continuousOn_fwdMap_solSet {c : ℝ} (hc : 0 < c) :
    ContinuousOn (fun p : C(Icc (0 : ℝ) T, ℝ) × ℂ => fwdMap (extIccPath hT p.1) T p.2) (solSet hT c) := by
  set δ := c / 2 with hδdef
  have hδ : 0 < δ := half_pos hc
  rw [Metric.continuousOn_iff]
  intro p hp η hη
  obtain ⟨u, hu, hl⟩ := hp
  set E := Real.exp (2 / δ ^ 2 * T) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hl2 : ∀ (v : ℝ → ℂ), (∀ t ∈ Icc (0 : ℝ) T, c ≤ ‖v t‖) → ∀ t ∈ Icc (0 : ℝ) T, 2 * δ ≤ ‖v t‖ :=
    fun v hv t ht => by rw [hδdef, mul_div_cancel₀ _ two_ne_zero]; exact hv t ht
  refine ⟨min δ (η / (2 * E + 2)), lt_min hδ (by positivity), fun p' hp' hd => ?_⟩
  obtain ⟨u', hu', hl'⟩ := hp'
  have hd' : dist p'.1 p.1 < min δ (η / (2 * E + 2)) ∧ dist p'.2 p.2 < min δ (η / (2 * E + 2)) := by
    rw [Prod.dist_eq, max_lt_iff] at hd; exact hd
  rw [F1.fwdMap_eq_of_isForwardSol hu' ⟨hT, le_rfl⟩, F1.fwdMap_eq_of_isForwardSol hu ⟨hT, le_rfl⟩, dist_eq_norm]
  have h := norm_sub_le_of_solSet hT hδ hu' (hl2 u' hl') hu (hl2 u hl) (hd'.1.le.trans (min_le_left _ _))
    T ⟨hT, le_rfl⟩
  have h1 : dist p'.1 p.1 < η / (2 * E + 2) := hd'.1.trans_le (min_le_right _ _)
  have h2 : ‖p'.2 - p.2‖ < η / (2 * E + 2) := by rw [← dist_eq_norm]; exact hd'.2.trans_le (min_le_right _ _)
  calc _ ≤ _ := h
    _ ≤ (η / (2 * E + 2) + η / (2 * E + 2)) * E + η / (2 * E + 2) := by gcongr
    _ = η * (2 * E + 1) / (2 * E + 2) := by field_simp; ring
    _ < η := by rw [div_lt_iff₀ (by positivity)]; nlinarith

theorem aliveSet_eq_iUnion_solSet :
    {p : C(Icc (0 : ℝ) T, ℝ) × ℂ | ∃ u, IsForwardSol (extIccPath hT p.1) p.2 T u} =
      ⋃ n : ℕ, solSet hT (1 / ((n : ℝ) + 1)) := by
  ext p
  simp only [mem_ofPred_eq, mem_iUnion]
  constructor
  · rintro ⟨u, hu⟩
    obtain ⟨δ, hδ, hlow⟩ := exists_two_mul_le_norm_of_isForwardSol hT hu
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (by positivity : 0 < 2 * δ)
    exact ⟨n, u, hu, fun t ht => hn.le.trans (hlow t ht)⟩
  · rintro ⟨n, u, hu, -⟩
    exact ⟨u, hu⟩

variable [MeasurableSpace C(Icc (0 : ℝ) T, ℝ)] [BorelSpace C(Icc (0 : ℝ) T, ℝ)]

/-- **The alive event is Borel on path space** (an `F_σ` set). -/
theorem measurableSet_aliveSet_path :
    MeasurableSet {p : C(Icc (0 : ℝ) T, ℝ) × ℂ | ∃ u, IsForwardSol (extIccPath hT p.1) p.2 T u} := by
  rw [aliveSet_eq_iUnion_solSet hT]
  exact MeasurableSet.iUnion fun n => (isClosed_solSet hT (by positivity)).measurableSet

/-- **The forward map is Borel on path space.** -/
theorem measurable_fwdMap_path :
    Measurable fun p : C(Icc (0 : ℝ) T, ℝ) × ℂ => fwdMap (extIccPath hT p.1) T p.2 := by
  set F := fun p : C(Icc (0 : ℝ) T, ℝ) × ℂ => fwdMap (extIccPath hT p.1) T p.2 with hF
  set A := {p : C(Icc (0 : ℝ) T, ℝ) × ℂ | ∃ u, IsForwardSol (extIccPath hT p.1) p.2 T u} with hA
  refine measurable_of_isOpen fun U hU => ?_
  have e : F ⁻¹' U = (⋃ n : ℕ, F ⁻¹' U ∩ solSet hT (1 / ((n : ℝ) + 1))) ∪ (Aᶜ ∩ {_p | (0 : ℂ) ∈ U}) := by
    ext p
    simp only [mem_preimage, mem_union, mem_iUnion, mem_inter_iff, mem_compl_iff, mem_ofPred_eq]
    constructor
    · intro hp
      by_cases hpA : p ∈ A
      · rw [hA, aliveSet_eq_iUnion_solSet hT, mem_iUnion] at hpA
        obtain ⟨n, hn⟩ := hpA
        exact Or.inl ⟨n, hp, hn⟩
      · refine Or.inr ⟨hpA, ?_⟩
        have : F p = 0 := fwdMap_of_not hpA
        rwa [this] at hp
    · rintro (⟨n, hp, -⟩ | ⟨hpA, h0⟩)
      · exact hp
      · have : F p = 0 := fwdMap_of_not hpA
        rw [this]; exact h0
  rw [e]
  refine MeasurableSet.union (MeasurableSet.iUnion fun n => ?_) ?_
  · obtain ⟨V, hV, hVe⟩ := continuousOn_iff'.1 (continuousOn_fwdMap_solSet hT (c := 1 / ((n : ℝ) + 1))
      (by positivity)) U hU
    rw [hVe]
    exact hV.measurableSet.inter (isClosed_solSet hT (by positivity)).measurableSet
  · exact (measurableSet_aliveSet_path hT).compl.inter (MeasurableSet.const _)

end PathSpace

/-! ### Random drivers, times and starting points -/

section Param

/-- **The forward map is measurable in the driver, the time and the starting point.** For continuous drivers
`W a` with `W a 0 = 0`, measurable at each time, a measurable time `τ a ≥ 0` and a measurable starting point
`y a ∈ ℂ`, the value `f_{τ a}(y a)` and the event that a solution exists on `[0, τ a]` are measurable. -/
theorem measurable_fwdMap_param {α : Type*} [MeasurableSpace α] {W : α → ℝ → ℝ}
    (hWc : ∀ a, Continuous (W a)) (hWm : ∀ t, Measurable fun a => W a t) (hW0 : ∀ a, W a 0 = 0)
    {τ : α → ℝ} (hτ : Measurable τ) (hτ0 : ∀ a, 0 ≤ τ a) {y : α → ℂ} (hy : Measurable y) :
    Measurable (fun a => fwdMap (W a) (τ a) (y a)) ∧
      MeasurableSet {a | ∃ u, IsForwardSol (W a) (y a) (τ a) u} := by
  let _ : MeasurableSpace C(Icc (0 : ℝ) 1, ℝ) := borel _
  have _ : BorelSpace C(Icc (0 : ℝ) 1, ℝ) := ⟨rfl⟩
  have hWj : Measurable fun q : α × ℝ => W q.1 q.2 := by
    have h := measurable_uncurry_of_continuous_of_measurable (u := fun t a => W a t) (fun a => hWc a) hWm
    exact h.comp measurable_swap
  set Ψ : α → C(Icc (0 : ℝ) 1, ℝ) := fun a =>
    ⟨fun s => W a (τ a * s) / Real.sqrt (τ a),
      ((hWc a).comp (continuous_const.mul continuous_subtype_val)).div_const _⟩ with hΨ
  have hΨm : Measurable Ψ := by
    refine measurable_to_continuousMap_Icc Ψ fun s => ?_
    have := (hWj.comp (measurable_id.prodMk (hτ.mul_const (s : ℝ)))).div (hτ.sqrt)
    exact this
  have hpair : Measurable fun a => (Ψ a, y a / Real.sqrt (τ a)) :=
    hΨm.prodMk (hy.div (Complex.measurable_ofReal.comp hτ.sqrt))
  set S := {a | 0 < τ a} with hS
  have hSm : MeasurableSet S := measurableSet_lt measurable_const hτ
  have hcongr : ∀ a, EqOn (fun s => W a (τ a * s) / Real.sqrt (τ a)) (extIccPath zero_le_one (Ψ a)) (Icc 0 1) :=
    fun a s hs => by rw [extIccPath_of_mem zero_le_one _ hs]; rfl
  have hval : ∀ a ∈ S, fwdMap (W a) (τ a) (y a) =
      Real.sqrt (τ a) * fwdMap (extIccPath zero_le_one (Ψ a)) 1 (y a / Real.sqrt (τ a)) := fun a ha => by
    rw [(fwdMap_scale (W a) ha (y a)).1, Ito.fwdMap_congr_of_eqOn (hcongr a)]
  have halive : ∀ a ∈ S, (∃ u, IsForwardSol (W a) (y a) (τ a) u) ↔
      ∃ u, IsForwardSol (extIccPath zero_le_one (Ψ a)) (y a / Real.sqrt (τ a)) 1 u := fun a ha => by
    rw [(fwdMap_scale (W a) ha (y a)).2]
    exact exists_congr fun u => Ito.isForwardSol_iff_of_eqOn (hcongr a) u
  have hzero : ∀ a ∉ S, τ a = 0 := fun a ha => le_antisymm (not_lt.1 ha) (hτ0 a)
  constructor
  · have e : (fun a => fwdMap (W a) (τ a) (y a)) = S.piecewise
        (fun a => Real.sqrt (τ a) * fwdMap (extIccPath zero_le_one (Ψ a)) 1 (y a / Real.sqrt (τ a))) y := by
      funext a
      by_cases ha : a ∈ S
      · rw [piecewise_eq_of_mem _ _ _ ha, hval a ha]
      · rw [piecewise_eq_of_notMem _ _ _ ha, hzero a ha, fwdMap_zero_time (hW0 a)]
    rw [e]
    refine Measurable.piecewise hSm ?_ hy
    exact (Complex.measurable_ofReal.comp hτ.sqrt).mul ((measurable_fwdMap_path zero_le_one).comp hpair)
  · have e : {a | ∃ u, IsForwardSol (W a) (y a) (τ a) u} = (S ∩ (fun a => (Ψ a, y a / Real.sqrt (τ a))) ⁻¹'
        {p : C(Icc (0 : ℝ) 1, ℝ) × ℂ | ∃ u, IsForwardSol (extIccPath zero_le_one p.1) p.2 1 u}) ∪
          (Sᶜ ∩ {a | y a ≠ 0}) := by
      ext a
      simp only [mem_ofPred_eq, mem_union, mem_inter_iff, mem_preimage, mem_compl_iff]
      by_cases ha : a ∈ S
      · rw [halive a ha]; simp [ha]
      · rw [hzero a ha, exists_isForwardSol_zero_iff, hW0 a]; simp [ha]
    rw [e]
    exact (hSm.inter (hpair (measurableSet_aliveSet_path zero_le_one))).union
      (hSm.compl.inter (measurableSet_eq_fun hy measurable_const).compl)

end Param

end StagedLaw

end Exist

end InteractingSLE
