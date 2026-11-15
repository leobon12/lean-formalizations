/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.OneForcePath
import InteractingSLE.Stochastic.Bessel.Regularized

/-!
# One force point with weight `ρ ≤ −2`: the killed solution up to its first zero

Packet PROVE-SEC2-ONE. Specification p. 19 (`source/spec/p001-048.md` L433: "standard SDE results
imply that (2.2) has a unique solution up until the first time `t` that `X_t = 0`"; L437: "we only
consider the process up to the first time that `X` reaches zero"). With `c = (ρ + 2)/κ ≤ 0` the
equation `X_t = x + b_t + ∫₀ᵗ c / X_s ds` is solved pathwise up to its first zero.

* `lipSol f x w`: the global solution of `X t = x + w t + ∫₀ᵗ f (X s) ds` for a bounded Lipschitz
  `f` and a continuous `w` (Picard–Lindelöf on every `[0, T]`, as `Bessel.regSol`, whose drift
  needs `c ≥ 0`); `lipSol_eq`, `continuousOn_lipSol`, and uniqueness `eqOn_lipSol`.
* `killSeq c x w n = lipSol (regDrift c εₙ) x w` with `εₙ = x / (n + 2)`, `KillAlive c x w n t`
  (`killSeq n` stays above `εₙ` on `[0, t]`), the lifetime `killTime` and the path `killPath`.
* `isKilledPath_killPath`: the killed path solves the equation before `killTime`, is positive
  there, and `killPath → 0` at a finite `killTime` (`tendsto_killPath`).
* `eqOn_killSeq`: every positive killed path coincides with `killSeq n` while it stays above `εₙ`
  (pathwise uniqueness before the first zero).

Everything is deterministic: `w : ℝ → ℝ` is a continuous path in real time.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace OneForce

/-! ### Global solutions for a bounded Lipschitz drift -/

section LipSol

variable {f : ℝ → ℝ} {K : ℝ≥0} {M : ℝ} {w : ℝ → ℝ}

theorem lipschitzWith_shift (hf : LipschitzWith K f) (a : ℝ) :
    LipschitzWith K (fun v => f (v + a)) := by
  refine LipschitzWith.of_dist_le_mul fun v u => ?_
  have := hf.dist_le_mul (v + a) (u + a)
  rwa [dist_add_right] at this

/-- Global existence for `v' = f (v + w t)`, `v 0 = x`, on `[0, T]`. -/
theorem exists_lipUnc_sol (hf : LipschitzWith K f) (hM : ∀ y, |f y| ≤ M) (hw : Continuous w)
    {T : ℝ} (hT : 0 ≤ T) (x : ℝ) :
    ∃ v : ℝ → ℝ, v 0 = x ∧
      ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt v (f (v t + w t)) (Icc 0 T) t := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_refl 0, hT⟩
  set t0 : Icc (0 : ℝ) T := ⟨0, h0mem⟩ with ht0_def
  have ht0_coe : (t0 : ℝ) = 0 := rfl
  have hf : IsPicardLindelof (fun t v => f (v + w t)) t0 x
      (Real.toNNReal (M * T)) 0 (Real.toNNReal M) K := by
    refine ⟨fun t _ => (lipschitzWith_shift hf _).lipschitzOnWith, fun v _ => ?_, ?_, ?_⟩
    · exact (hf.continuous.comp (continuous_const.add hw)).continuousOn
    · intro t _ v _
      rw [Real.coe_toNNReal _ hM0, Real.norm_eq_abs]
      exact hM _
    · simp only [ht0_coe, sub_zero, NNReal.coe_zero, max_eq_left hT,
        Real.coe_toNNReal _ hM0, Real.coe_toNNReal _ (mul_nonneg hM0 hT), le_refl]
  have hx : x ∈ Metric.closedBall x ((0 : ℝ≥0) : ℝ) := Metric.mem_closedBall_self (le_refl _)
  obtain ⟨α, hα⟩ := ODE.FunSpace.exists_isFixedPt_next hf hx
  refine ⟨α.compProj, ?_, ?_⟩
  · show α.compProj (t0 : ℝ) = x
    rw [ODE.FunSpace.compProj_val, ← hα, ODE.FunSpace.next_apply₀]
  · intro t ht
    apply (ODE.hasDerivWithinAt_picard_Icc t0.2 hf.continuousOn_uncurry
      α.continuous_compProj.continuousOn (fun _ ht' ↦ α.compProj_mem_closedBall hf.mul_max_le)
      x ht).congr_of_mem _ ht
    intro t' ht'
    nth_rw 1 [← hα]
    rw [ODE.FunSpace.compProj_of_mem ht', ODE.FunSpace.next_apply]

/-- The hypotheses under which `lipSol` is the solution. -/
def LipData (f : ℝ → ℝ) (w : ℝ → ℝ) : Prop :=
  (∃ K, LipschitzWith K f) ∧ (∃ M, ∀ y, |f y| ≤ M) ∧ Continuous w

open Classical in
/-- The solution `v = X − w` of `X = x + w + ∫ f (X)` (junk `0` unless `LipData f w`). -/
def lipUnc (f : ℝ → ℝ) (x : ℝ) (w : ℝ → ℝ) (t : ℝ) : ℝ :=
  if h : LipData f w then
    Classical.choose (exists_lipUnc_sol h.1.choose_spec h.2.1.choose_spec h.2.2
      (le_max_right t 0) x) t
  else 0

/-- **The global solution** of `X t = x + w t + ∫₀ᵗ f (X s) ds` (`lipSol_eq`). -/
def lipSol (f : ℝ → ℝ) (x : ℝ) (w : ℝ → ℝ) (t : ℝ) : ℝ := lipUnc f x w t + w t

theorem lipUnc_eq_of_sol (h : LipData f w) {x T : ℝ} {V : ℝ → ℝ} (hV0 : V 0 = x)
    (hV : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt V (f (V t + w t)) (Icc 0 T) t) :
    ∀ t ∈ Icc (0 : ℝ) T, lipUnc f x w t = V t := by
  intro t ht
  rw [lipUnc, dite_eq_left_of_eq_true (eq_true h)]
  obtain ⟨hv0, hvd⟩ := Classical.choose_spec (exists_lipUnc_sol h.1.choose_spec
    h.2.1.choose_spec h.2.2 (le_max_right t 0) x)
  set v := Classical.choose (exists_lipUnc_sol h.1.choose_spec h.2.1.choose_spec h.2.2
    (le_max_right t 0) x) with hvdef
  have hsub : Icc (0 : ℝ) t ⊆ Icc 0 (max t 0) := Icc_subset_Icc_right (le_max_left _ _)
  have hsubT : Icc (0 : ℝ) t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
  have key := ODE_solution_unique (v := fun s v => f (v + w s))
    (fun s => lipschitzWith_shift h.1.choose_spec _) (f := v) (g := V) (a := 0) (b := t)
    (fun s hs => (hvd s (hsub hs)).continuousWithinAt.mono hsub)
    (fun s hs => Bessel.hasDerivWithinAt_Ici_of_Icc
      ((hvd s (hsub (Ico_subset_Icc_self hs))).mono hsub) hs)
    (fun s hs => (hV s (hsubT hs)).continuousWithinAt.mono hsubT)
    (fun s hs => Bessel.hasDerivWithinAt_Ici_of_Icc
      ((hV s (hsubT (Ico_subset_Icc_self hs))).mono hsubT) hs)
    (by rw [hv0, hV0])
  exact key ⟨ht.1, le_rfl⟩

theorem lipUnc_zero (h : LipData f w) (x : ℝ) : lipUnc f x w 0 = x := by
  rw [lipUnc, dite_eq_left_of_eq_true (eq_true h)]
  exact (Classical.choose_spec (exists_lipUnc_sol h.1.choose_spec h.2.1.choose_spec h.2.2
    (le_max_right 0 0) x)).1

theorem lipUnc_hasDerivWithinAt (h : LipData f w) {T : ℝ} (hT : 0 ≤ T) (x : ℝ) :
    ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (lipUnc f x w) (f (lipSol f x w t)) (Icc 0 T) t := by
  obtain ⟨v, hv0, hvd⟩ := exists_lipUnc_sol h.1.choose_spec h.2.1.choose_spec h.2.2 hT x
  have heq := lipUnc_eq_of_sol h hv0 hvd
  intro t ht
  have e : lipSol f x w t = v t + w t := by rw [lipSol, heq t ht]
  rw [e]
  exact (hvd t ht).congr_of_mem heq ht

theorem continuousOn_lipSol (h : LipData f w) {T : ℝ} (hT : 0 ≤ T) (x : ℝ) :
    ContinuousOn (lipSol f x w) (Icc 0 T) := by
  have hu : ContinuousOn (lipUnc f x w) (Icc 0 T) := fun t ht =>
    (lipUnc_hasDerivWithinAt h hT x t ht).continuousWithinAt
  exact hu.add h.2.2.continuousOn

/-- `lipSol` is continuous on `[0, ∞)`. -/
theorem continuousOn_lipSol_Ici (h : LipData f w) (x : ℝ) :
    ContinuousOn (lipSol f x w) (Ici 0) := by
  intro t ht
  have hc := continuousOn_lipSol h (T := t + 1) (by linarith [mem_Ici.1 ht]) x
  have hmem : Icc (0 : ℝ) (t + 1) ∈ 𝓝[Ici 0] t := by
    rw [← Ici_inter_Iic]
    exact inter_mem_nhdsWithin _ (Iic_mem_nhds (by linarith))
  exact (hc t ⟨ht, by linarith⟩).mono_of_mem_nhdsWithin hmem

/-- **Integral equation** of `lipSol`. -/
theorem lipSol_eq (h : LipData f w) (x : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    lipSol f x w t = x + w t + ∫ s in (0 : ℝ)..t, f (lipSol f x w s) := by
  have hcont : ContinuousOn (lipUnc f x w) (Icc 0 t) := fun s hs =>
    (lipUnc_hasDerivWithinAt h ht x s hs).continuousWithinAt
  have hderiv : ∀ s ∈ Ioo (0 : ℝ) t,
      HasDerivAt (lipUnc f x w) (f (lipSol f x w s)) s := fun s hs =>
    (lipUnc_hasDerivWithinAt h ht x s (Ioo_subset_Icc_self hs)).hasDerivAt
      (Icc_mem_nhds hs.1 hs.2)
  have hint : IntervalIntegrable (fun s => f (lipSol f x w s)) volume 0 t := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le ht]
    exact h.1.choose_spec.continuous.comp_continuousOn (continuousOn_lipSol h ht x)
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht hcont hderiv hint
  rw [lipUnc_zero h] at key
  rw [lipSol, key]
  ring

theorem lipSol_zero (h : LipData f w) (x : ℝ) : lipSol f x w 0 = x + w 0 := by
  rw [lipSol_eq h x le_rfl, intervalIntegral.integral_same, add_zero]

/-- **Uniqueness**: a continuous solution of the integral equation on `[0, T]` is `lipSol`. -/
theorem eqOn_lipSol (h : LipData f w) {x T : ℝ} (hT : 0 ≤ T) {Z : ℝ → ℝ}
    (hZc : ContinuousOn Z (Icc 0 T))
    (hZ : ∀ s ∈ Icc (0 : ℝ) T, Z s = x + w s + ∫ r in (0 : ℝ)..s, f (Z r)) :
    EqOn (lipSol f x w) Z (Icc 0 T) := by
  have hfc : Continuous f := h.1.choose_spec.continuous
  set g : ℝ → ℝ := fun r => f (Z (projIcc 0 T hT r : ℝ)) with hgdef
  have hg : Continuous g :=
    hfc.comp (hZc.comp_continuous (continuous_subtype_val.comp continuous_projIcc)
      fun r => (projIcc 0 T hT r).2)
  have hgZ : ∀ r ∈ Icc (0 : ℝ) T, g r = f (Z r) := fun r hr => by
    simp only [hgdef, projIcc_of_mem hT hr]
  have hint : ∀ s ∈ Icc (0 : ℝ) T,
      ∫ r in (0 : ℝ)..s, f (Z r) = ∫ r in (0 : ℝ)..s, g r := fun s hs =>
    intervalIntegral.integral_congr fun r hr => by
      rw [uIcc_of_le hs.1] at hr
      exact (hgZ r ⟨hr.1, hr.2.trans hs.2⟩).symm
  set V : ℝ → ℝ := fun s => Z s - w s with hVdef
  have hV0 : V 0 = x := by
    simp only [hVdef, hZ 0 ⟨le_rfl, hT⟩, intervalIntegral.integral_same]
    ring
  have hVd : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt V (f (V t + w t)) (Icc 0 T) t := by
    intro t ht
    have hd : HasDerivWithinAt (fun s => x + ∫ r in (0 : ℝ)..s, g r) (g t) (Icc 0 T) t :=
      ((hg.integral_hasStrictDerivAt 0 t).hasDerivAt.hasDerivWithinAt).const_add x
    have hVt : V t + w t = Z t := by simp only [hVdef, sub_add_cancel]
    rw [hVt, ← hgZ t ht]
    refine hd.congr_of_mem (fun s hs => ?_) ht
    simp only [hVdef, hZ s hs, hint s hs]
    ring
  have key := lipUnc_eq_of_sol h hV0 hVd
  intro t ht
  simp only [lipSol, key t ht, hVdef, sub_add_cancel]

end LipSol


/-! ### The killed solution for `c ≤ 0` -/

section Killed

variable {c x : ℝ} {w : ℝ → ℝ}

/-- The cut-off levels `εₙ = x / (n + 2)`. -/
def killEps (x : ℝ) (n : ℕ) : ℝ := x / (n + 2)

theorem killEps_pos (hx : 0 < x) (n : ℕ) : 0 < killEps x n := by
  unfold killEps; positivity

theorem killEps_lt (hx : 0 < x) (n : ℕ) : killEps x n < x := by
  unfold killEps
  rw [div_lt_iff₀ (by positivity)]
  nlinarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]

theorem killEps_anti (hx : 0 ≤ x) {n m : ℕ} (h : n ≤ m) : killEps x m ≤ killEps x n := by
  unfold killEps
  have : (n : ℝ) ≤ m := by exact_mod_cast h
  exact div_le_div_of_nonneg_left hx (by positivity) (by linarith)

theorem exists_killEps_lt {δ : ℝ} (hδ : 0 < δ) : ∃ n, killEps x n < δ := by
  obtain ⟨n, hn⟩ := exists_nat_gt (x / δ)
  refine ⟨n, ?_⟩
  unfold killEps
  rw [div_lt_iff₀ (by positivity)]
  rw [div_lt_iff₀ hδ] at hn
  nlinarith

/-- For `c ≤ 0`, the drift `c / max y ε` is bounded and Lipschitz. -/
theorem lipData_regDrift (hc : c ≤ 0) {ε : ℝ} (hε : 0 < ε) (hw : Continuous w) :
    LipData (Bessel.regDrift c ε) w := by
  have hneg : Bessel.regDrift c ε = fun y => -Bessel.regDrift (-c) ε y := funext fun y => by
    simp only [Bessel.regDrift, neg_div, neg_neg]
  have hc' : 0 ≤ -c := by linarith
  refine ⟨⟨Real.toNNReal (-c / ε ^ 2), ?_⟩, ⟨-c / ε, fun y => ?_⟩, hw⟩
  · rw [hneg]
    exact (Bessel.lipschitzWith_regDrift hc' hε).neg
  · rw [hneg, abs_neg]
    exact Bessel.abs_regDrift_le hc' hε y

/-- The regularized solutions `X = x + w + ∫ c / max X εₙ`. -/
def killSeq (c x : ℝ) (w : ℝ → ℝ) (n : ℕ) : ℝ → ℝ :=
  lipSol (Bessel.regDrift c (killEps x n)) x w

/-- `killSeq n` stays above `εₙ` on `[0, t]` (so it solves the unregularized equation there). -/
def KillAlive (c x : ℝ) (w : ℝ → ℝ) (n : ℕ) (t : ℝ≥0) : Prop :=
  ∀ s ∈ Icc (0 : ℝ) t, killEps x n < killSeq c x w n s

/-- The lifetime: the supremum of the times `t` at which some `killSeq n` is alive. -/
def killTime (c x : ℝ) (w : ℝ → ℝ) : ℝ≥0∞ :=
  ⨆ (n : ℕ) (t : ℝ≥0) (_ : KillAlive c x w n t), (t : ℝ≥0∞)

open Classical in
/-- **The killed solution** before `killTime` (junk `x` afterwards). -/
def killPath (c x : ℝ) (w : ℝ → ℝ) (t : ℝ≥0) : ℝ :=
  if h : ∃ n, KillAlive c x w n t then killSeq c x w (Nat.find h) t else x

theorem killSeq_eq (hc : c ≤ 0) (hx : 0 < x) (hw : Continuous w) (n : ℕ) {t : ℝ}
    (ht : 0 ≤ t) :
    killSeq c x w n t
      = x + w t + ∫ s in (0 : ℝ)..t, Bessel.regDrift c (killEps x n) (killSeq c x w n s) :=
  lipSol_eq (lipData_regDrift hc (killEps_pos hx n) hw) x ht

theorem continuousOn_killSeq (hc : c ≤ 0) (hx : 0 < x) (hw : Continuous w) (n : ℕ) :
    ContinuousOn (killSeq c x w n) (Ici 0) :=
  continuousOn_lipSol_Ici (lipData_regDrift hc (killEps_pos hx n) hw) x

theorem continuous_killSeq_coe (hc : c ≤ 0) (hx : 0 < x) (hw : Continuous w) (n : ℕ) :
    Continuous fun t : ℝ≥0 => killSeq c x w n t :=
  (continuousOn_killSeq hc hx hw n).comp_continuous NNReal.continuous_coe fun t => t.coe_nonneg

/-- **Uniqueness against `killSeq`**: a continuous solution of `Z = x + w + ∫ c / Z` on `[0, T]`
that stays above `εₙ` is `killSeq n` there. -/
theorem eqOn_killSeq (hc : c ≤ 0) (hx : 0 < x) (hw : Continuous w) {n : ℕ} {T : ℝ}
    (hT : 0 ≤ T) {Z : ℝ → ℝ} (hZc : ContinuousOn Z (Icc 0 T))
    (hZε : ∀ s ∈ Icc (0 : ℝ) T, killEps x n ≤ Z s)
    (hZ : ∀ s ∈ Icc (0 : ℝ) T, Z s = x + w s + ∫ r in (0 : ℝ)..s, c / Z r) :
    EqOn (killSeq c x w n) Z (Icc 0 T) := by
  refine eqOn_lipSol (lipData_regDrift hc (killEps_pos hx n) hw) hT hZc fun s hs => ?_
  rw [hZ s hs]
  congr 1
  refine intervalIntegral.integral_congr fun r hr => ?_
  rw [uIcc_of_le hs.1] at hr
  exact (Bessel.regDrift_of_le (hZε r ⟨hr.1, hr.2.trans hs.2⟩)).symm

theorem KillAlive.mono {n : ℕ} {t t' : ℝ≥0} (h : KillAlive c x w n t) (htt : t' ≤ t) :
    KillAlive c x w n t' := fun s hs => h s ⟨hs.1, hs.2.trans (by exact_mod_cast htt)⟩

/-- While alive, `killSeq n` solves the unregularized equation. -/
theorem KillAlive.eq (hc : c ≤ 0) (hx : 0 < x) (hw : Continuous w) {n : ℕ} {t : ℝ≥0}
    (h : KillAlive c x w n t) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) t) :
    killSeq c x w n s = x + w s + ∫ r in (0 : ℝ)..s, c / killSeq c x w n r := by
  rw [killSeq_eq hc hx hw n hs.1]
  congr 1
  refine intervalIntegral.integral_congr fun r hr => ?_
  rw [uIcc_of_le hs.1] at hr
  exact Bessel.regDrift_of_le (h r ⟨hr.1, hr.2.trans hs.2⟩).le

/-- **Consistency**: while `killSeq n` is alive, every later `killSeq m` agrees with it. -/
theorem KillAlive.eqOn (hc : c ≤ 0) (hx : 0 < x) (hw : Continuous w) {n m : ℕ} (hnm : n ≤ m)
    {t : ℝ≥0} (h : KillAlive c x w n t) :
    EqOn (killSeq c x w m) (killSeq c x w n) (Icc 0 t) :=
  eqOn_killSeq hc hx hw t.coe_nonneg
    ((continuousOn_killSeq hc hx hw n).mono fun _ hs => hs.1)
    (fun s hs => (killEps_anti hx.le hnm).trans (h s hs).le) fun _ hs => h.eq hc hx hw hs

theorem KillAlive.mono_n (hc : c ≤ 0) (hx : 0 < x) (hw : Continuous w) {n m : ℕ} (hnm : n ≤ m)
    {t : ℝ≥0} (h : KillAlive c x w n t) : KillAlive c x w m t := fun s hs => by
  rw [h.eqOn hc hx hw hnm hs]
  exact (killEps_anti hx.le hnm).trans_lt (h s hs)

/-- Alive at `t` implies alive slightly after `t`. -/
theorem KillAlive.exists_gt (hc : c ≤ 0) (hx : 0 < x) (hw : Continuous w) {n : ℕ} {t : ℝ≥0}
    (h : KillAlive c x w n t) : ∃ t' : ℝ≥0, t < t' ∧ KillAlive c x w n t' := by
  have hcont : ContinuousWithinAt (killSeq c x w n) (Ici (t : ℝ)) t :=
    ((continuousOn_killSeq hc hx hw n) t t.coe_nonneg).mono fun s hs =>
      t.coe_nonneg.trans hs
  have hev : ∀ᶠ s in 𝓝[≥] (t : ℝ), killEps x n < killSeq c x w n s :=
    hcont (lt_mem_nhds (h t ⟨t.coe_nonneg, le_rfl⟩))
  obtain ⟨u, hu, hsub⟩ := (mem_nhdsGE_iff_exists_Ico_subset).1 hev
  have hu' : (t : ℝ) < (t + u) / 2 := by linarith [mem_Ioi.1 hu]
  set t' : ℝ≥0 := ⟨(t + u) / 2, by linarith [t.coe_nonneg]⟩ with ht'def
  have ht'c : (t' : ℝ) = (t + u) / 2 := rfl
  refine ⟨t', by rw [← NNReal.coe_lt_coe, ht'c]; exact hu', fun s hs => ?_⟩
  rcases le_or_gt s t with hst | hst
  · exact h s ⟨hs.1, hst⟩
  · exact hsub ⟨hst.le, lt_of_le_of_lt hs.2 (by rw [ht'c]; linarith [mem_Ioi.1 hu])⟩

theorem lt_killTime_iff (hc : c ≤ 0) (hx : 0 < x) (hw : Continuous w) {t : ℝ≥0} :
    (t : ℝ≥0∞) < killTime c x w ↔ ∃ n, KillAlive c x w n t := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := lt_iSup_iff.1 h
    obtain ⟨t', ht'⟩ := lt_iSup_iff.1 hn
    obtain ⟨halive, hlt⟩ := lt_iSup_iff.1 ht'
    exact ⟨n, halive.mono (by exact_mod_cast hlt.le)⟩
  · rintro ⟨n, hn⟩
    obtain ⟨t', htt', ht'⟩ := hn.exists_gt hc hx hw
    exact lt_of_lt_of_le (by exact_mod_cast htt')
      (le_iSup_of_le n (le_iSup_of_le t' (le_iSup_of_le ht' le_rfl)))

theorem killPath_eq (hc : c ≤ 0) (hx : 0 < x) (hw : Continuous w) {n : ℕ} {t : ℝ≥0}
    (h : KillAlive c x w n t) : killPath c x w t = killSeq c x w n t := by
  classical
  have hex : ∃ n, KillAlive c x w n t := ⟨n, h⟩
  rw [killPath, dite_eq_left_of_eq_true (eq_true hex)]
  exact ((Nat.find_spec hex).eqOn hc hx hw (Nat.find_min' hex h) ⟨t.coe_nonneg, le_rfl⟩).symm

/-- While `killSeq n` is alive on `[0, t]`, it is the killed path there. -/
theorem killPath_eqOn (hc : c ≤ 0) (hx : 0 < x) (hw : Continuous w) {n : ℕ} {t : ℝ≥0}
    (h : KillAlive c x w n t) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) t) :
    killPath c x w s.toNNReal = killSeq c x w n s := by
  rw [killPath_eq hc hx hw (h.mono (Real.toNNReal_le_iff_le_coe.2 hs.2)),
    Real.coe_toNNReal s hs.1]

theorem killAlive_zero (hx : 0 < x) (hc : c ≤ 0) (hw : Continuous w) (hw0 : w 0 = 0) :
    KillAlive c x w 0 0 := fun s hs => by
  have hs0 : s = 0 := le_antisymm (by simpa using hs.2) hs.1
  rw [hs0, killSeq, lipSol_zero (lipData_regDrift hc (killEps_pos hx 0) hw), hw0, add_zero]
  exact killEps_lt hx 0

theorem killTime_pos (hx : 0 < x) (hc : c ≤ 0) (hw : Continuous w) (hw0 : w 0 = 0) :
    0 < killTime c x w := by
  have := (lt_killTime_iff hc hx hw (t := 0)).2 ⟨0, killAlive_zero hx hc hw hw0⟩
  simpa using this

theorem killPath_pos (hc : c ≤ 0) (hx : 0 < x) (hw : Continuous w) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < killTime c x w) : 0 < killPath c x w t := by
  obtain ⟨n, hn⟩ := (lt_killTime_iff hc hx hw).1 ht
  rw [killPath_eq hc hx hw hn]
  exact (killEps_pos hx n).trans (hn t ⟨t.coe_nonneg, le_rfl⟩)

/-- **The killed path is a killed Bessel-type path** with lifetime `killTime`. -/
theorem isKilledPath_killPath (hc : c ≤ 0) (hx : 0 < x) (hw : Continuous w) (hw0 : w 0 = 0) :
    IsKilledPath c x (fun t : ℝ≥0 => w t) (killPath c x w) (killTime c x w) where
  zero := by
    rw [killPath_eq hc hx hw (killAlive_zero hx hc hw hw0), killSeq, NNReal.coe_zero,
      lipSol_zero (lipData_regDrift hc (killEps_pos hx 0) hw), hw0, add_zero]
  continuousOn := by
    intro t₀ ht₀
    obtain ⟨n, hn⟩ := (lt_killTime_iff hc hx hw).1 ht₀
    obtain ⟨t₁, ht₁, hn₁⟩ := hn.exists_gt hc hx hw
    have heq : killPath c x w =ᶠ[𝓝 t₀] fun t : ℝ≥0 => killSeq c x w n t := by
      filter_upwards [Iic_mem_nhds ht₁] with t ht
      exact killPath_eq hc hx hw (hn₁.mono ht)
    exact ((continuous_killSeq_coe hc hx hw n).continuousAt.congr heq.symm).continuousWithinAt
  nonneg t ht := (killPath_pos hc hx hw ht).le
  volume_zero := by
    refine measure_mono_null (fun s hs => ?_) (measure_empty (μ := (volume : Measure ℝ)))
    exact absurd hs.2.2 (killPath_pos hc hx hw hs.2.1).ne'
  integrable t ht := by
    obtain ⟨n, hn⟩ := (lt_killTime_iff hc hx hw).1 ht
    have hcont : ContinuousOn (fun s => (killSeq c x w n s)⁻¹) (uIcc 0 t) := by
      rw [uIcc_of_le t.coe_nonneg]
      exact ((continuousOn_killSeq hc hx hw n).mono fun _ hs => hs.1).inv₀ fun s hs =>
        ((killEps_pos hx n).trans (hn s hs)).ne'
    refine hcont.intervalIntegrable.congr fun s hs => ?_
    rw [uIoc_of_le t.coe_nonneg] at hs
    rw [killPath_eqOn hc hx hw hn ⟨hs.1.le, hs.2⟩]
  eq t ht := by
    obtain ⟨n, hn⟩ := (lt_killTime_iff hc hx hw).1 ht
    rw [killPath_eq hc hx hw hn, hn.eq hc hx hw ⟨t.coe_nonneg, le_rfl⟩]
    congr 1
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le t.coe_nonneg] at hr
    rw [killPath_eqOn hc hx hw hn hr]

end Killed


/-! ### Uniqueness of positive killed paths and the limit at a finite lifetime -/

section KilledUnique

variable {c x : ℝ} {w : ℝ → ℝ} {X : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- A killed path coincides with `killSeq n` on `[0, t]` (`t` before its lifetime) as long as it
stays above `εₙ` there. -/
theorem IsKilledPath.eqOn_killSeq (hc : c ≤ 0) (hx : 0 < x) (hw : Continuous w)
    (hX : IsKilledPath c x (fun t : ℝ≥0 => w t) X ζ) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) {n : ℕ}
    (hXε : ∀ s ∈ Icc (0 : ℝ) t, killEps x n ≤ X s.toNNReal) :
    ∀ s ∈ Icc (0 : ℝ) t, killSeq c x w n s = X s.toNNReal := by
  refine OneForce.eqOn_killSeq hc hx hw t.coe_nonneg (hX.continuousOn_real ht) hXε fun s hs => ?_
  rw [hX.eq _ (IsKilledPath.toNNReal_lt ht hs), Real.coe_toNNReal s hs.1]

/-- **Pathwise uniqueness before the first zero** (`c ≤ 0`): a killed path that does not vanish
before its lifetime `ζ` equals `killPath` before `ζ`, and `ζ ≤ killTime`. -/
theorem IsKilledPath.eq_killPath (hc : c ≤ 0) (hx : 0 < x) (hw : Continuous w)
    (hX : IsKilledPath c x (fun t : ℝ≥0 => w t) X ζ)
    (hpos : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → X t ≠ 0) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < ζ) :
    X t = killPath c x w t ∧ (t : ℝ≥0∞) < killTime c x w := by
  have hpos' : ∀ s ∈ Icc (0 : ℝ) t, 0 < X s.toNNReal := fun s hs => by
    have hs' := IsKilledPath.toNNReal_lt ht hs
    exact lt_of_le_of_ne (hX.nonneg _ hs') (hpos _ hs').symm
  obtain ⟨s₀, hs₀, hmin⟩ := isCompact_Icc.exists_isMinOn
    (nonempty_Icc.2 t.coe_nonneg) (hX.continuousOn_real ht)
  obtain ⟨n, hn⟩ := exists_killEps_lt (x := x) (hpos' s₀ hs₀)
  have hε : ∀ s ∈ Icc (0 : ℝ) t, killEps x n < X s.toNNReal := fun s hs =>
    hn.trans_le (hmin hs)
  have heq := hX.eqOn_killSeq hc hx hw ht fun s hs => (hε s hs).le
  have halive : KillAlive c x w n t := fun s hs => by rw [heq s hs]; exact hε s hs
  refine ⟨?_, (lt_killTime_iff hc hx hw).2 ⟨n, halive⟩⟩
  rw [killPath_eq hc hx hw halive, heq t ⟨t.coe_nonneg, le_rfl⟩, Real.toNNReal_coe]

/-- **At a finite lifetime the killed path tends to `0`.** -/
theorem tendsto_killPath (hc : c ≤ 0) (hx : 0 < x) (hw : Continuous w) (hw0 : w 0 = 0)
    {T : ℝ≥0} (hT : (T : ℝ≥0∞) = killTime c x w) (hT0 : 0 < T) :
    Tendsto (killPath c x w) (𝓝[<] T) (𝓝 0) := by
  have hK := isKilledPath_killPath hc hx hw hw0
  have hlt : ∀ t : ℝ≥0, t < T → (t : ℝ≥0∞) < killTime c x w := fun t h => by
    rw [← hT]; exact_mod_cast h
  have hNe : (𝓝[<] T).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hT0⟩
  set X := killPath c x w with hXdef
  -- `Z = X − w` is antitone before `T` and bounded below
  set Z : ℝ≥0 → ℝ := fun t => X t - w t with hZdef
  have hZeq : ∀ t : ℝ≥0, t < T → Z t = x + ∫ s in (0 : ℝ)..t, c / X s.toNNReal := fun t ht => by
    simp only [hZdef]
    rw [hK.eq t (hlt t ht)]
    ring
  have hanti : AntitoneOn Z (Iio T) := by
    intro s hs t ht hst
    rw [hZeq t ht, hZeq s hs]
    have key := intervalIntegral.integral_interval_sub_left (hK.intervalIntegrable_div (hlt t ht))
      (hK.intervalIntegrable_div (hlt s hs))
    have hneg : ∫ r in (s : ℝ)..t, c / X r.toNNReal ≤ 0 := by
      have h0 : 0 ≤ ∫ r in (s : ℝ)..t, -(c / X r.toNNReal) :=
        intervalIntegral.integral_nonneg (by exact_mod_cast hst) fun u hu => by
          have hu' : u ∈ Icc (0 : ℝ) t := ⟨s.coe_nonneg.trans hu.1, hu.2⟩
          have hXu := killPath_pos hc hx hw (IsKilledPath.toNNReal_lt (hlt t ht) hu')
          exact neg_nonneg.2 (div_nonpos_of_nonpos_of_nonneg hc hXu.le)
      rw [intervalIntegral.integral_neg] at h0
      exact neg_nonneg.1 h0
    linarith
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    hw.continuousOn
  have hbdd : BddBelow (Z '' Iio T) := by
    refine ⟨-C, ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    have h1 := (killPath_pos hc hx hw (hlt t ht)).le
    have h2 := hC t ⟨t.coe_nonneg, by exact_mod_cast (mem_Iio.1 ht).le⟩
    rw [Real.norm_eq_abs] at h2
    simp only [hZdef]
    linarith [le_abs_self (w t)]
  have hZlim := hanti.tendsto_nhdsLT hbdd
  have hwlim : Tendsto (fun t : ℝ≥0 => w t) (𝓝[<] T) (𝓝 (w T)) :=
    ((hw.comp NNReal.continuous_coe).tendsto T).mono_left nhdsWithin_le_nhds
  set L := sInf (Z '' Iio T) + w T with hLdef
  have hXlim : Tendsto X (𝓝[<] T) (𝓝 L) :=
    (hZlim.add hwlim).congr fun t => by simp only [hZdef, sub_add_cancel]
  have hL0 : 0 ≤ L := ge_of_tendsto hXlim
    (mem_of_superset self_mem_nhdsWithin fun t ht => (killPath_pos hc hx hw (hlt t ht)).le)
  suffices hL : L = 0 by rwa [hL] at hXlim
  by_contra hLne
  have hLpos : 0 < L := lt_of_le_of_ne hL0 (Ne.symm hLne)
  -- `X` stays above a positive level before `T`
  have hev : ∀ᶠ t in 𝓝[<] T, L / 2 < X t := hXlim.eventually (eventually_gt_nhds (by linarith))
  obtain ⟨t₀, ht₀T, hsub⟩ := (mem_nhdsLT_iff_exists_Ioo_subset' hT0).1 hev
  obtain ⟨n₀, hn₀⟩ := (lt_killTime_iff hc hx hw).1 (hlt t₀ ht₀T)
  set δ := min (L / 2) (killEps x n₀) with hδdef
  have hδ : 0 < δ := lt_min (by linarith) (killEps_pos hx n₀)
  have hXδ : ∀ t : ℝ≥0, t < T → δ ≤ X t := fun t ht => by
    rcases le_or_gt t t₀ with htt | htt
    · rw [hXdef, killPath_eq hc hx hw (hn₀.mono htt)]
      exact (min_le_right _ _).trans (hn₀ t ⟨t.coe_nonneg, by exact_mod_cast htt⟩).le
    · exact (min_le_left _ _).trans (hsub ⟨htt, ht⟩).le
  obtain ⟨n, hn⟩ := exists_killEps_lt (x := x) hδ
  have heq : ∀ t : ℝ≥0, t < T → ∀ s ∈ Icc (0 : ℝ) t, killSeq c x w n s = X s.toNNReal :=
    fun t ht => hK.eqOn_killSeq hc hx hw (hlt t ht) fun s hs => hn.le.trans
      (hXδ _ (lt_of_le_of_lt (Real.toNNReal_le_iff_le_coe.2 hs.2) ht))
  -- `killSeq n` reaches `T` with value `L`
  have hseqX : ∀ t : ℝ≥0, t < T → killSeq c x w n t = X t := fun t ht => by
    rw [heq t ht t ⟨t.coe_nonneg, le_rfl⟩, Real.toNNReal_coe]
  have hseqT : killSeq c x w n T = L := by
    have h1 : Tendsto (fun t : ℝ≥0 => killSeq c x w n t) (𝓝[<] T) (𝓝 (killSeq c x w n T)) :=
      (continuous_killSeq_coe hc hx hw n).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun t : ℝ≥0 => killSeq c x w n t) (𝓝[<] T) (𝓝 L) :=
      hXlim.congr' (mem_of_superset self_mem_nhdsWithin fun t ht => (hseqX t ht).symm)
    exact tendsto_nhds_unique h1 h2
  have halive : KillAlive c x w n T := by
    intro s hs
    rcases hs.2.lt_or_eq with hsT | hsT
    · have hsT' : s.toNNReal < T := (Real.toNNReal_lt_iff_lt_coe hs.1).2 hsT
      rw [heq s.toNNReal hsT' s ⟨hs.1, (Real.le_coe_toNNReal s)⟩]
      exact hn.trans_le (hXδ _ hsT')
    · rw [hsT, hseqT]
      linarith [min_le_left (L / 2) (killEps x n₀)]
  have := (lt_killTime_iff hc hx hw).2 ⟨n, halive⟩
  rw [← hT] at this
  exact lt_irrefl _ this

end KilledUnique

end OneForce

end InteractingSLE
