/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.TargetChangeProcessBrownianStmt
import InteractingSLE.Spec.Sec7.ContinuityProb7Loc

/-!
# `b̃` is a Brownian motion, part 1: coordinates and localization before the separation time

Packet PROVE-SEC7-C9. Along a path, the coordinates of the retargeting are `Λ = (V^L, V^R, α, β, S)`
(`rCoordAt`; `α, β` the coefficients of the retargeting family, `S = C(t)` the new clock) with density
`λ = dens(Λ, b)` (`rDensAt`, PROVE-SEC7-C8's `dens`): `Λ_t = Λ_0 + ∫₀ᵗ λ` while the target stays right of the driver
(`rCoordAt_eq_add_integral`).

The localizing times are

  `σ_n = n ∧ T_n ∧ (exit of the box: ‖V‖ ≤ n, V_k − W ≥ δ_n, |V_k − V_i| ≥ δ_n for i ≠ k) ∧ (exit of |B| from (−n, n))`

(`rLoc`, `δ_n = 1/(n+1)`), with `T_n` an announcing sequence of the lifetime (C7's pattern). Up to `σ_n` the
coordinates and the Brownian path stay in a compact subset `rKc` of the observable's region (`mem_rKc`); the integral
of `‖λ‖` is bounded (`integral_norm_rDensAt_le`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Zhan

namespace Retarget

variable {nL nR : ℕ}

/-! ### Coordinates along a path -/

/-- The retargeting coordinates `(V^L, V^R, α, β, S)` along a path at time `t`. -/
def rCoordAt (xk : ℝ) (k : Fin nR) (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ)
    (t : ℝ≥0) : RCoord nL nR :=
  (fun i => vL i t, fun i => vR i t, alpha xk w (vR k) t, beta xk w (vR k) t, clk (rate xk w (vR k)) t)

/-- Their density at real time `s`. -/
def rDensAt (κ : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (k : Fin nR)
    (xk : ℝ) (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) (b : ℝ≥0 → ℝ) (s : ℝ) :
    RCoord nL nR :=
  dens κ xL xR ρL ρR k (rCoordAt xk k w vL vR s.toNNReal, b s.toNNReal)

/-- The initial coordinates `((x^L, x^R, x_k, −1, 0), 0)`. -/
def rInit (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (xk : ℝ) : RCoord nL nR × ℝ := ((xL, xR, xk, -1, 0), 0)

theorem rCoordAt_zero {xk : ℝ} {k : Fin nR} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} (hL : ∀ i, vL i 0 = xL i) (hR : ∀ i, vR i 0 = xR i) :
    rCoordAt xk k w vL vR 0 = (xL, xR, xk, -1, 0) := by
  simp only [rCoordAt, NNReal.coe_zero, alpha_zero, beta_zero, clk_zero]
  exact Prod.ext (funext hL) (Prod.ext (funext hR) rfl)

/-! ### Integrals of `RCoord`-valued functions -/

theorem intervalIntegrable_rcoord {g : ℝ → RCoord nL nR} {a b : ℝ}
    (h1 : ∀ i, IntervalIntegrable (fun s => (g s).1 i) volume a b)
    (h2 : ∀ i, IntervalIntegrable (fun s => (g s).2.1 i) volume a b)
    (h3 : IntervalIntegrable (fun s => (g s).2.2.1) volume a b)
    (h4 : IntervalIntegrable (fun s => (g s).2.2.2.1) volume a b)
    (h5 : IntervalIntegrable (fun s => (g s).2.2.2.2) volume a b) :
    IntervalIntegrable g volume a b := by
  rw [intervalIntegrable_iff] at h3 h4 h5 ⊢
  have h1' : IntegrableOn (fun s => (g s).1) (uIoc a b) :=
    integrable_pi_iff.2 fun i => intervalIntegrable_iff.1 (h1 i)
  have h2' : IntegrableOn (fun s => (g s).2.1) (uIoc a b) :=
    integrable_pi_iff.2 fun i => intervalIntegrable_iff.1 (h2 i)
  exact h1'.prodMk (h2'.prodMk (h3.prodMk (h4.prodMk h5)))

section IntegralComp

variable {g : ℝ → RCoord nL nR} {a b : ℝ} (hg : IntervalIntegrable g volume a b)
include hg

theorem integral_rcoord_L (i : Fin nL) : (∫ s in a..b, g s).1 i = ∫ s in a..b, (g s).1 i :=
  (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin nL => ℝ) i).comp
    (ContinuousLinearMap.fst ℝ (Fin nL → ℝ) ((Fin nR → ℝ) × ℝ × ℝ × ℝ))).intervalIntegral_comp_comm hg).symm

theorem integral_rcoord_R (i : Fin nR) : (∫ s in a..b, g s).2.1 i = ∫ s in a..b, (g s).2.1 i :=
  (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin nR => ℝ) i).comp
    ((ContinuousLinearMap.fst ℝ (Fin nR → ℝ) (ℝ × ℝ × ℝ)).comp
      (ContinuousLinearMap.snd ℝ (Fin nL → ℝ) ((Fin nR → ℝ) × ℝ × ℝ × ℝ)))).intervalIntegral_comp_comm hg).symm

theorem integral_rcoord_α : (∫ s in a..b, g s).2.2.1 = ∫ s in a..b, (g s).2.2.1 :=
  (((ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)).comp ((ContinuousLinearMap.snd ℝ (Fin nR → ℝ) (ℝ × ℝ × ℝ)).comp
      (ContinuousLinearMap.snd ℝ (Fin nL → ℝ) ((Fin nR → ℝ) × ℝ × ℝ × ℝ)))).intervalIntegral_comp_comm hg).symm

theorem integral_rcoord_β : (∫ s in a..b, g s).2.2.2.1 = ∫ s in a..b, (g s).2.2.2.1 :=
  (((ContinuousLinearMap.fst ℝ ℝ ℝ).comp ((ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)).comp
    ((ContinuousLinearMap.snd ℝ (Fin nR → ℝ) (ℝ × ℝ × ℝ)).comp
      (ContinuousLinearMap.snd ℝ (Fin nL → ℝ) ((Fin nR → ℝ) × ℝ × ℝ × ℝ))))).intervalIntegral_comp_comm hg).symm

theorem integral_rcoord_S : (∫ s in a..b, g s).2.2.2.2 = ∫ s in a..b, (g s).2.2.2.2 :=
  (((ContinuousLinearMap.snd ℝ ℝ ℝ).comp ((ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)).comp
    ((ContinuousLinearMap.snd ℝ (Fin nR → ℝ) (ℝ × ℝ × ℝ)).comp
      (ContinuousLinearMap.snd ℝ (Fin nL → ℝ) ((Fin nR → ℝ) × ℝ × ℝ × ℝ))))).intervalIntegral_comp_comm hg).symm

end IntegralComp

theorem norm_rcoord_le (p : RCoord nL nR) :
    ‖p‖ ≤ ∑ i, |p.1 i| + ∑ i, |p.2.1 i| + |p.2.2.1| + |p.2.2.2.1| + |p.2.2.2.2| := by
  have h1 := norm_pi_le_sum' p.1
  have h2 := norm_pi_le_sum' p.2.1
  have h0 : 0 ≤ ∑ i, |p.1 i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have h0' : 0 ≤ ∑ i, |p.2.1 i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have a1 := abs_nonneg p.2.2.1
  have a2 := abs_nonneg p.2.2.2.1
  have a3 := abs_nonneg p.2.2.2.2
  simp only [Prod.norm_def, Real.norm_eq_abs]
  refine max_le (h1.trans (by linarith)) (max_le (h2.trans (by linarith))
    (max_le (by linarith) (max_le (by linarith) (by linarith))))

/-! ### The coordinates along a local path before separation -/

/-- Every right index other than the target is before it (`castAdd ∘ castSucc`) or after it (`natAdd (j+1)`). -/
theorem retargetIdx_cases {j m : ℕ} (i : Fin (j + 1 + m)) (hi : i ≠ LP.retargetIdx j m) :
    (∃ i' : Fin j, i = Fin.castAdd m i'.castSucc) ∨ ∃ l : Fin m, i = Fin.natAdd (j + 1) l := by
  have hk : ((LP.retargetIdx j m : Fin (j + 1 + m)) : ℕ) = j := rfl
  have hne : (i : ℕ) ≠ j := fun h => hi (Fin.ext (h.trans hk.symm))
  have hlt := i.isLt
  rcases lt_or_gt_of_ne hne with h | h
  · exact Or.inl ⟨⟨i, h⟩, Fin.ext rfl⟩
  · refine Or.inr ⟨⟨(i : ℕ) - (j + 1), by omega⟩, Fin.ext ?_⟩
    simp only [Fin.val_natAdd]
    omega

section Path

variable {κ : ℝ} {nL j m : ℕ} {xL : Fin nL → ℝ} {xR : Fin (j + 1 + m) → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin (j + 1 + m) → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin (j + 1 + m) → ℝ≥0 → ℝ}
  {b : ℝ≥0 → ℝ} {T : ℝ≥0∞}

/-- Before `T`, every right mark other than the target is away from it. -/
theorem RetargetData.vR_ne (hd : RetargetData xL xR w vL vR T) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < T)
    (i : Fin (j + 1 + m)) (hi : i ≠ LP.retargetIdx j m) : vR (LP.retargetIdx j m) t - vR i t ≠ 0 := by
  rcases retargetIdx_cases i hi with ⟨i', rfl⟩ | ⟨l, rfl⟩
  · exact (sub_pos.2 (hd.ltR i' t ht)).ne'
  · exact (sub_neg.2 (hd.ltA l t ht)).ne

variable (hp : Sec2.IsSLEPathUpTo κ xL xR ρL ρR w vL vR b T) (hd : RetargetData xL xR w vL vR T)

include hp in
/-- (N1) along the path: the driver is `drv` of the coordinates. -/
theorem drv_rCoordAt {t : ℝ≥0} (ht : (t : ℝ≥0∞) < T) :
    drv κ xL xR ρL ρR (rCoordAt (LP.retargetPos xR) (LP.retargetIdx j m) w vL vR t, b t) = w t :=
  (w_eq_drv_of_upTo hp ht _ _ _).symm

include hp hd in
/-- Along the path before `T`, the coordinates are in the observable's region. -/
theorem mem_obsRegion {t : ℝ≥0} (ht : (t : ℝ≥0∞) < T) :
    (rCoordAt (LP.retargetPos xR) (LP.retargetIdx j m) w vL vR t, b t) ∈
      obsRegion κ xL xR ρL ρR (LP.retargetIdx j m) := by
  have hq : w t < vR (LP.retargetIdx j m) t := by
    have := (hd.sep.isSep_of_lt ht).pos t ⟨t.coe_nonneg, le_rfl⟩
    simpa [gap] using this
  refine ⟨?_, fun i => ?_, fun i hi => hd.vR_ne ht i hi⟩
  · simp only [qOf, drv_rCoordAt hp ht]
    exact sub_pos.2 hq
  · exact (sub_pos.2 ((hp.vL_le_w ht i).trans_lt hq)).ne'

include hp in
theorem drv_rCoordAt_real {t : ℝ≥0} (ht : (t : ℝ≥0∞) < T) {s : ℝ} (hs : s ∈ uIcc (0 : ℝ) t) :
    drv κ xL xR ρL ρR (rCoordAt (LP.retargetPos xR) (LP.retargetIdx j m) w vL vR s.toNNReal, b s.toNNReal) =
      w s.toNNReal := by
  rw [uIcc_of_le t.coe_nonneg] at hs
  exact drv_rCoordAt hp (lt_of_mem_Icc (by rwa [Real.toNNReal_coe]) hs)

include hp in
theorem qOf_rCoordAt_real {t : ℝ≥0} (ht : (t : ℝ≥0∞) < T) {s : ℝ} (hs : s ∈ uIcc (0 : ℝ) t) :
    qOf κ xL xR ρL ρR (LP.retargetIdx j m)
      (rCoordAt (LP.retargetPos xR) (LP.retargetIdx j m) w vL vR s.toNNReal, b s.toNNReal) =
        gap w (vR (LP.retargetIdx j m)) s := by
  simp only [qOf, drv_rCoordAt_real hp ht hs, gap]
  rfl

theorem alpha_toNNReal_of_mem {xk : ℝ} {vk : ℝ≥0 → ℝ} {t : ℝ≥0} {s : ℝ} (hs : s ∈ uIcc (0 : ℝ) t) :
    alpha xk w vk (s.toNNReal : ℝ) = alpha xk w vk s := by
  rw [uIcc_of_le t.coe_nonneg] at hs
  rw [Real.coe_toNNReal _ hs.1]

include hp hd in
/-- The density's components are interval integrable on `[0, t]`, `t < T`. -/
theorem intervalIntegrable_rDensAt {t : ℝ≥0} (ht : (t : ℝ≥0∞) < T) :
    IntervalIntegrable (rDensAt κ xL xR ρL ρR (LP.retargetIdx j m) (LP.retargetPos xR) w vL vR b) volume 0 t := by
  have hS := hd.sep.isSep_of_lt ht
  have hdrv := fun s (hs : s ∈ uIcc (0 : ℝ) t) => drv_rCoordAt_real hp ht (b := b) hs
  have hq := fun s (hs : s ∈ uIcc (0 : ℝ) t) => qOf_rCoordAt_real hp ht (b := b) hs
  have hα := fun s (hs : s ∈ uIcc (0 : ℝ) t) =>
    alpha_toNNReal_of_mem (w := w) (xk := LP.retargetPos xR) (vk := vR (LP.retargetIdx j m)) hs
  have hc : ∀ {f : ℝ → ℝ}, ContinuousOn f (Icc 0 (t : ℝ)) → IntervalIntegrable f volume 0 t := fun hf =>
    hf.intervalIntegrable_of_Icc t.coe_nonneg
  refine intervalIntegrable_rcoord (fun i => ?_) (fun i => ?_) ?_ ?_ ?_
  · refine ((hp.integrable_gapL ht i).const_mul (-2)).congr fun s hs => ?_
    simp only [rDensAt, dens]
    rw [hdrv s (uIoc_subset_uIcc hs)]
    simp only [rCoordAt]
    rw [div_eq_mul_inv, ← neg_sub (w s.toNNReal), inv_neg]
    ring
  · refine ((hp.integrable_gapR ht i).const_mul (-2)).congr fun s hs => ?_
    simp only [rDensAt, dens]
    rw [hdrv s (uIoc_subset_uIcc hs)]
    simp only [rCoordAt]
    rw [div_eq_mul_inv, ← neg_sub (w s.toNNReal), inv_neg]
    ring
  · refine (hc (((hS.continuousOn_alpha (xk := LP.retargetPos xR)).const_mul (-2)).div (hS.continuousOn_gap.pow 2)
      fun s hs => pow_ne_zero 2 (hS.gap_ne hs))).congr fun s hs => ?_
    simp only [rDensAt, dens]
    rw [hq s (uIoc_subset_uIcc hs)]
    simp only [rCoordAt, Pi.div_apply, Pi.pow_apply]
    rw [hα s (uIoc_subset_uIcc hs)]
  · refine (hc (((hS.continuousOn_alpha (xk := LP.retargetPos xR)).const_mul (-2)).div (hS.continuousOn_gap.pow 3)
      fun s hs => pow_ne_zero 3 (hS.gap_ne hs))).congr fun s hs => ?_
    simp only [rDensAt, dens]
    rw [hq s (uIoc_subset_uIcc hs)]
    simp only [rCoordAt, Pi.div_apply, Pi.pow_apply]
    rw [hα s (uIoc_subset_uIcc hs)]
  · refine (hc (hS.continuousOn_rate (xk := LP.retargetPos xR))).congr fun s hs => ?_
    simp only [rDensAt, dens, rate]
    rw [hq s (uIoc_subset_uIcc hs)]
    simp only [rCoordAt]
    rw [hα s (uIoc_subset_uIcc hs)]

include hp hd in
/-- **The coordinates are absolutely continuous**: `Λ_t = Λ_0 + ∫₀ᵗ λ` before `T`. -/
theorem rCoordAt_eq_add_integral {t : ℝ≥0} (ht : (t : ℝ≥0∞) < T) :
    rCoordAt (LP.retargetPos xR) (LP.retargetIdx j m) w vL vR t =
      rCoordAt (LP.retargetPos xR) (LP.retargetIdx j m) w vL vR 0 +
        ∫ s in (0 : ℝ)..t, rDensAt κ xL xR ρL ρR (LP.retargetIdx j m) (LP.retargetPos xR) w vL vR b s := by
  have hint := intervalIntegrable_rDensAt hp hd ht
  have hS := hd.sep.isSep_of_lt ht
  refine Prod.ext (funext fun i => ?_) (Prod.ext (funext fun i => ?_) (Prod.ext ?_ (Prod.ext ?_ ?_)))
  · rw [Prod.fst_add, Pi.add_apply, integral_rcoord_L hint]
    simp only [rCoordAt, hp.vL_zero]
    rw [hp.vL_eq ht i]
    congr 1
    refine intervalIntegral.integral_congr fun s hs => ?_
    simp only [rDensAt, dens]
    rw [drv_rCoordAt_real hp ht hs]
    rfl
  · rw [Prod.snd_add, Prod.fst_add, Pi.add_apply, integral_rcoord_R hint]
    simp only [rCoordAt, hp.vR_zero]
    rw [hp.vR_eq ht i]
    congr 1
    refine intervalIntegral.integral_congr fun s hs => ?_
    simp only [rDensAt, dens]
    rw [drv_rCoordAt_real hp ht hs]
    rfl
  · rw [Prod.snd_add, Prod.snd_add, Prod.fst_add, integral_rcoord_α hint]
    simp only [rCoordAt, NNReal.coe_zero]
    rw [eq_add_integral_of_ae_hasDerivAt t.coe_nonneg (hS.ac_alpha (xk := LP.retargetPos xR))
      (Eventually.of_forall fun s hs => hS.hasDerivAt_alpha hs)]
    congr 1
    refine intervalIntegral.integral_congr fun s hs => ?_
    simp only [rDensAt, dens]
    rw [qOf_rCoordAt_real hp ht hs]
    simp only [rCoordAt]
    rw [alpha_toNNReal_of_mem hs, div_eq_mul_inv]
  · rw [Prod.snd_add, Prod.snd_add, Prod.snd_add, Prod.fst_add, integral_rcoord_β hint]
    simp only [rCoordAt, NNReal.coe_zero, beta_zero]
    rw [beta, sub_eq_add_neg, ← neg_mul, ← intervalIntegral.integral_const_mul]
    congr 1
    refine intervalIntegral.integral_congr fun s hs => ?_
    simp only [rDensAt, dens]
    rw [qOf_rCoordAt_real hp ht hs]
    simp only [rCoordAt]
    rw [alpha_toNNReal_of_mem hs]
    ring
  · rw [Prod.snd_add, Prod.snd_add, Prod.snd_add, Prod.snd_add, integral_rcoord_S hint]
    simp only [rCoordAt, NNReal.coe_zero, clk, intervalIntegral.integral_same, zero_add]
    refine intervalIntegral.integral_congr fun s hs => ?_
    simp only [rDensAt, dens]
    rw [qOf_rCoordAt_real hp ht hs]
    simp only [rCoordAt, rate]
    rw [alpha_toNNReal_of_mem hs]

include hp hd in
/-- **Along the path the generator of an observable with vanishing drift vanishes at almost every time** (no mark
at the driver). -/
theorem ae_itoGen_eq_zero {F : RCoord nL (j + 1 + m) × ℝ → ℝ}
    (hF : ∀ p ∈ obsRegion κ xL xR ρL ρR (LP.retargetIdx j m), (∀ i, p.1.1 i ≠ drv κ xL xR ρL ρR p) →
      (∀ i, p.1.2.1 i ≠ drv κ xL xR ρL ρR p) →
        Ito.itoGen F p (dens κ xL xR ρL ρR (LP.retargetIdx j m) p) = 0)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < T) :
    ∀ᵐ s ∂volume, s ∈ Ioc 0 (t : ℝ) →
      Ito.itoGen F (rCoordAt (LP.retargetPos xR) (LP.retargetIdx j m) w vL vR s.toNNReal, b s.toNNReal)
        (rDensAt κ xL xR ρL ρR (LP.retargetIdx j m) (LP.retargetPos xR) w vL vR b s) = 0 := by
  have hL : ∀ i, ∀ᵐ s ∂volume, s ∉ {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < T ∧
      w s.toNNReal = vL i s.toNNReal} := fun i => by
    rw [ae_iff]; simpa using hp.volume_collisionL i
  have hR : ∀ i, ∀ᵐ s ∂volume, s ∉ {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < T ∧
      w s.toNNReal = vR i s.toNNReal} := fun i => by
    rw [ae_iff]; simpa using hp.volume_collisionR i
  filter_upwards [ae_all_iff.2 hL, ae_all_iff.2 hR] with s hsL hsR hs
  have hsT : ((s.toNNReal : ℝ≥0) : ℝ≥0∞) < T :=
    lt_of_mem_Icc (S := t) (by rwa [Real.toNNReal_coe]) ⟨hs.1.le, hs.2⟩
  have hdrv := drv_rCoordAt hp hsT (b := b)
  refine hF _ (mem_obsRegion hp hd hsT) (fun i => ?_) (fun i => ?_)
  · rw [hdrv]
    exact fun h => hsL i ⟨hs.1.le, hsT, h.symm⟩
  · rw [hdrv]
    exact fun h => hsR i ⟨hs.1.le, hsT, h.symm⟩

end Path

/-! ### The compact box -/

section Box

variable (κ : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (k : Fin nR) (xk : ℝ)

/-- The level-`n` bound on `|β|`. -/
def betaBd (xk : ℝ) (n : ℕ) : ℝ := 1 + 2 * n * xk * ((n : ℝ) + 1) ^ 3

/-- The level-`n` bound on `|S|`. -/
def clkBd (xk : ℝ) (n : ℕ) : ℝ := n * xk ^ 2 * ((n : ℝ) + 1) ^ 4

/-- The level-`n` box: `‖V^L‖, ‖V^R‖, |b| ≤ n`, `q ≥ δ_n`, every mark at distance `≥ δ_n` from the target,
`|α| ≤ x_k`, `|β| ≤ betaBd`, `|S| ≤ clkBd`. -/
def rBox (n : ℕ) : Set (RCoord nL nR × ℝ) :=
  {p | ‖p.1.1‖ ≤ n ∧ ‖p.1.2.1‖ ≤ n ∧ |p.2| ≤ n ∧ 1 / ((n : ℝ) + 1) ≤ qOf κ xL xR ρL ρR k p ∧
    (∀ i, 1 / ((n : ℝ) + 1) ≤ |p.1.2.1 k - p.1.1 i|) ∧
    (∀ i, i ≠ k → 1 / ((n : ℝ) + 1) ≤ |p.1.2.1 k - p.1.2.1 i|) ∧
    |p.1.2.2.1| ≤ xk ∧ |p.1.2.2.2.1| ≤ betaBd xk n ∧ |p.1.2.2.2.2| ≤ clkBd xk n}

/-- The box together with the initial point. -/
def rKc (n : ℕ) : Set (RCoord nL nR × ℝ) := insert (rInit xL xR xk) (rBox κ xL xR ρL ρR k xk n)

theorem isCompact_rKc (n : ℕ) : IsCompact (rKc κ xL xR ρL ρR k xk n) := by
  refine IsCompact.insert ?_ _
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · have hq : Continuous (qOf κ xL xR ρL ρR k) := contDiff_qOf (n := 0) κ xL xR ρL ρR k |>.continuous
    have hL : IsClosed {p : RCoord nL nR × ℝ | ∀ i, 1 / ((n : ℝ) + 1) ≤ |p.1.2.1 k - p.1.1 i|} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun i => isClosed_le continuous_const (by fun_prop)
    have hR : IsClosed {p : RCoord nL nR × ℝ | ∀ i, i ≠ k → 1 / ((n : ℝ) + 1) ≤ |p.1.2.1 k - p.1.2.1 i|} := by
      simp only [Set.ofPred_forall]
      exact isClosed_iInter fun i => isClosed_iInter fun _ => isClosed_le continuous_const (by fun_prop)
    have c1 : Continuous fun p : RCoord nL nR × ℝ => ‖p.1.1‖ := by fun_prop
    have c2 : Continuous fun p : RCoord nL nR × ℝ => ‖p.1.2.1‖ := by fun_prop
    have c3 : Continuous fun p : RCoord nL nR × ℝ => |p.2| := by fun_prop
    have c4 : Continuous fun p : RCoord nL nR × ℝ => |p.1.2.2.1| := by fun_prop
    have c5 : Continuous fun p : RCoord nL nR × ℝ => |p.1.2.2.2.1| := by fun_prop
    have c6 : Continuous fun p : RCoord nL nR × ℝ => |p.1.2.2.2.2| := by fun_prop
    exact (isClosed_le c1 continuous_const).inter ((isClosed_le c2 continuous_const).inter
      ((isClosed_le c3 continuous_const).inter ((isClosed_le continuous_const hq).inter (hL.inter (hR.inter
        ((isClosed_le c4 continuous_const).inter ((isClosed_le c5 continuous_const).inter
          (isClosed_le c6 continuous_const))))))))
  · refine (Metric.isBounded_iff_subset_closedBall 0).2
      ⟨max (max n xk) (max (betaBd xk n) (clkBd xk n)), fun p hp => ?_⟩
    obtain ⟨h1, h2, h3, -, -, -, h4, h5, h6⟩ := hp
    rw [Metric.mem_closedBall, dist_zero_right]
    simp only [Prod.norm_def, Real.norm_eq_abs]
    refine max_le (max_le ?_ (max_le ?_ (max_le ?_ (max_le ?_ ?_)))) ?_
    · exact h1.trans ((le_max_left _ _).trans (le_max_left _ _))
    · exact h2.trans ((le_max_left _ _).trans (le_max_left _ _))
    · exact h4.trans ((le_max_right _ _).trans (le_max_left _ _))
    · exact h5.trans ((le_max_left _ _).trans (le_max_right _ _))
    · exact h6.trans ((le_max_right _ _).trans (le_max_right _ _))
    · exact h3.trans ((le_max_left _ _).trans (le_max_left _ _))

theorem rBox_subset_obsRegion (n : ℕ) : rBox κ xL xR ρL ρR k xk n ⊆ obsRegion κ xL xR ρL ρR k := by
  intro p hp
  have hδ : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  refine ⟨hδ.trans_le hp.2.2.2.1, fun i => ?_, fun i hi => ?_⟩
  · exact abs_pos.1 (hδ.trans_le (hp.2.2.2.2.1 i))
  · exact abs_pos.1 (hδ.trans_le (hp.2.2.2.2.2.1 i hi))

theorem rKc_subset_obsRegion (h0 : rInit xL xR xk ∈ obsRegion κ xL xR ρL ρR k) (n : ℕ) :
    rKc κ xL xR ρL ρR k xk n ⊆ obsRegion κ xL xR ρL ρR k :=
  insert_subset h0 (rBox_subset_obsRegion κ xL xR ρL ρR k xk n)

end Box

/-- The initial point of a retargeted distinct word is in the observable's region. -/
theorem rInit_mem_obsRegion {κ : ℝ} {nL j m : ℕ} {xL : Fin nL → ℝ} {xR : Fin (j + 1 + m) → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin (j + 1 + m) → ℝ} (hD : LP.IsDistinctForceWord xL xR) (hj : 1 ≤ j) (xk : ℝ) :
    rInit xL xR xk ∈ obsRegion κ xL xR ρL ρR (LP.retargetIdx j m) := by
  obtain ⟨⟨-, hL0, -, hR0⟩, -, hmono⟩ := hD
  have hpos : 0 < LP.retargetPos xR := LP.retargetPos_pos hmono hR0 hj
  have hdrv : drv κ xL xR ρL ρR (rInit xL xR xk) = 0 := by simp [drv, rInit]
  refine ⟨?_, fun i => ?_, fun i hi => ?_⟩
  · simp only [qOf, hdrv, sub_zero]; exact hpos
  · exact (sub_pos.2 ((hL0 i).trans_lt hpos)).ne'
  · exact sub_ne_zero.2 fun h => hi (hmono.injective h).symm

/-! ### Good paths and the localizing times -/

section Loc

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **Good paths**: the frozen pathwise conditions, a continuous Brownian path started at `0`, and an announcing
sequence `T` of the lifetime. -/
def IsRGood (κ : ℝ) (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
    (ζ : Ω → ℝ≥0∞) (T : ℕ → Ω → ℝ≥0) (ω : Ω) : Prop :=
  IsIntegratedSLEPath κ xL xR ρL ρR (W · ω) (fun i t => VL i t ω) (fun j t => VR j t ω) (B · ω) (ζ ω) ∧
    Continuous (B · ω) ∧ B 0 ω = 0 ∧ (∀ n, (T n ω : ℝ≥0∞) < ζ ω) ∧
    ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ ω → ∃ n, t ≤ T n ω

/-- A measurable full-measure event of good paths. -/
theorem exists_good_r {P : Measure Ω} {𝓕 𝓖 : Filtration ℝ≥0 mΩ} {κ : ℝ} {xL : Fin nL → ℝ}
    {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ}
    {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
    {ζ : Ω → ℝ≥0∞} {T : ℕ → Ω → ℝ≥0} (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hT : Coupling.IsAnnouncingSeq 𝓖 P ζ T) :
    ∃ G : Set Ω, MeasurableSet G ∧ P Gᶜ = 0 ∧ ∀ ω ∈ G, IsRGood κ xL xR ρL ρR W VL VR B ζ T ω := by
  have hae : ∀ᵐ ω ∂P, IsRGood κ xL xR ρL ρR W VL VR B ζ T ω := by
    filter_upwards [hE.2.2.2.2, hE.1.1.cont, hE.1.1.eval_zero_ae_eq_zero, ae_all_iff.2 hT.2.2.1, hT.2.2.2]
      with ω h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  refine ⟨(toMeasurable P {ω | ¬ IsRGood κ xL xR ρL ρR W VL VR B ζ T ω})ᶜ,
    (measurableSet_toMeasurable _ _).compl, ?_, fun ω hω => ?_⟩
  · rw [compl_compl, measure_toMeasurable]; exact ae_iff.1 hae
  · by_contra h
    exact hω (subset_toMeasurable _ _ h)

/-- The box level of a state `(W, V^L, V^R)`: nonnegative iff `‖V‖ ≤ n`, `V_k − W ≥ δ_n` and every other right mark
is at distance `≥ δ_n` from the target. -/
def rLev (k : Fin nR) (n : ℕ) (st : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)) : ℝ :=
  min (min ((n : ℝ) - ‖st.2‖) (st.2.2 k - st.1 - 1 / ((n : ℝ) + 1)))
    (-∑ i ∈ Finset.univ.erase k, max 0 (1 / ((n : ℝ) + 1) - |st.2.2 k - st.2.2 i|))

theorem continuous_rLev (k : Fin nR) (n : ℕ) : Continuous (rLev (nL := nL) k n) := by
  unfold rLev; fun_prop

theorem rLev_nonneg_iff {k : Fin nR} {n : ℕ} {st : ℝ × (Fin nL → ℝ) × (Fin nR → ℝ)} :
    0 ≤ rLev k n st ↔ ‖st.2‖ ≤ n ∧ 1 / ((n : ℝ) + 1) ≤ st.2.2 k - st.1 ∧
      ∀ i, i ≠ k → 1 / ((n : ℝ) + 1) ≤ |st.2.2 k - st.2.2 i| := by
  have hsum : 0 ≤ -∑ i ∈ Finset.univ.erase k, max 0 (1 / ((n : ℝ) + 1) - |st.2.2 k - st.2.2 i|) ↔
      ∀ i, i ≠ k → 1 / ((n : ℝ) + 1) ≤ |st.2.2 k - st.2.2 i| := by
    rw [neg_nonneg]
    have hnn : ∀ i ∈ Finset.univ.erase k, 0 ≤ max 0 (1 / ((n : ℝ) + 1) - |st.2.2 k - st.2.2 i|) :=
      fun _ _ => le_max_left _ _
    constructor
    · intro h i hi
      have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1
        (le_antisymm h (Finset.sum_nonneg hnn)) i (Finset.mem_erase.2 ⟨hi, Finset.mem_univ i⟩)
      have := le_max_right 0 (1 / ((n : ℝ) + 1) - |st.2.2 k - st.2.2 i|)
      linarith
    · intro h
      refine le_of_eq (Finset.sum_eq_zero fun i hi => ?_)
      exact max_eq_left (by linarith [h i (Finset.ne_of_mem_erase hi)])
  simp only [rLev, le_min_iff, hsum]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨by linarith, by linarith, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨by linarith, by linarith⟩, h3⟩

open scoped Classical in
/-- The first time before `ζ` at which the state leaves the level-`n` box, on the good event (`0` off it). -/
def rHit (k : Fin nR) (G : Set Ω) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (n : ℕ) (ω : Ω) : WithTop ℝ≥0 :=
  if ω ∈ G then Coupling.hitBelow (fun s => rLev k n (Coupling.stateAt W VL VR s ω)) (ζ ω) 0 else 0

/-- **The localizing times** `σ_n = n ∧ T_n ∧ (exit of the box) ∧ (exit of |B| from (−n, n))`, `0` off the good
event. -/
def rLoc (k : Fin nR) (G : Set Ω) (T : ℕ → Ω → ℝ≥0) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
    (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (n : ℕ) (ω : Ω) : ℝ≥0 :=
  Sec2.TwoSeed.capTime (fun ω => min (n : ℝ≥0) (T n ω))
    (fun ω => min (rHit k G W VL VR ζ n ω) (MathFin.exitTime (Sec2.TwoSeed.brownG G B) n ω)) ω

variable {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
  {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {G : Set Ω} {T : ℕ → Ω → ℝ≥0}
  {k : Fin nR}

theorem rLoc_le_n (n : ℕ) (ω : Ω) : rLoc k G T W VL VR B ζ n ω ≤ n :=
  (Sec2.TwoSeed.capTime_le _ _ ω).trans (min_le_left _ _)

theorem rLoc_le_T (n : ℕ) (ω : Ω) : rLoc k G T W VL VR B ζ n ω ≤ T n ω :=
  (Sec2.TwoSeed.capTime_le _ _ ω).trans (min_le_right _ _)

theorem rLoc_le_rHit (n : ℕ) (ω : Ω) : (rLoc k G T W VL VR B ζ n ω : WithTop ℝ≥0) ≤ rHit k G W VL VR ζ n ω :=
  (Sec2.TwoSeed.capTime_le_right _ _ ω).trans (min_le_left _ _)

theorem rLoc_le_exitTime (n : ℕ) (ω : Ω) :
    (rLoc k G T W VL VR B ζ n ω : WithTop ℝ≥0) ≤ MathFin.exitTime (Sec2.TwoSeed.brownG G B) n ω :=
  (Sec2.TwoSeed.capTime_le_right _ _ ω).trans (min_le_right _ _)

theorem rLoc_of_not_mem {ω : Ω} (hω : ω ∉ G) (n : ℕ) : rLoc k G T W VL VR B ζ n ω = 0 := by
  have h := rLoc_le_rHit (k := k) (G := G) (T := T) (W := W) (VL := VL) (VR := VR) (B := B) (ζ := ζ) n ω
  simp only [rHit, hω, ↓reduceIte] at h
  exact le_antisymm (by exact_mod_cast h) bot_le

section StoppingTime

variable (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hGm : MeasurableSet G)
  (hGc : P Gᶜ = 0) (hgood : ∀ ω ∈ G, IsRGood κ xL xR ρL ρR W VL VR B ζ T ω)

include hgood in
theorem continuous_brownG_r (ω : Ω) : Continuous (Sec2.TwoSeed.brownG G B · ω) := by
  by_cases hω : ω ∈ G
  · simpa only [Sec2.TwoSeed.brownG, hω, ↓reduceIte] using (hgood ω hω).2.1
  · simp only [Sec2.TwoSeed.brownG, hω, ↓reduceIte]; exact continuous_const

include hE hGm hGc hgood in
theorem isFilteredBrownianReal_brownG_r :
    IsFilteredBrownianReal (usualAugmentation 𝓕 P) (Sec2.TwoSeed.brownG G B) P := by
  have := (Ito.isFilteredBrownianReal_modify (Ito.isFilteredBrownianReal_usualAugmentation hE.1) hGm hGc
    fun ω hω => (hgood ω hω).2.1).1
  rwa [Ito.nullAugmented_usualAugmentation] at this

include hgood in
theorem continuousOn_stateAt_r {ω : Ω} (hω : ω ∈ G) :
    ContinuousOn (fun s => Coupling.stateAt W VL VR s ω) {s : ℝ≥0 | (s : ℝ≥0∞) < ζ ω} := by
  have hF := (hgood ω hω).1.isForcePath
  exact hF.continuousOn_w.prodMk ((continuousOn_pi.2 hF.continuousOn_vL).prodMk
    (continuousOn_pi.2 hF.continuousOn_vR))

include hE hGm hGc hgood in
theorem isStoppingTime_rHit (n : ℕ) :
    IsStoppingTime (usualAugmentation 𝓕 P) fun ω => rHit k G W VL VR ζ n ω := by
  classical
  obtain ⟨-, hWa, hVLa, hVRa, -⟩ := Ito.isIntegratedSLEEvolution_usualAugmentation hE
  have hG0 := measurableSet_good_usual hGm hGc (𝓕 := 𝓕) 0
  have hτ := Coupling.isStoppingTime_hitBelow_state hWa hVLa hVRa hG0
    (fun ω hω => continuousOn_stateAt_r hgood hω) (continuous_rLev k n) 0
  intro t
  have e : {ω | rHit k G W VL VR ζ n ω ≤ (t : WithTop ℝ≥0)} = Gᶜ ∪ {ω | (if ω ∈ G then Coupling.hitBelow
      (fun s => rLev k n (Coupling.stateAt W VL VR s ω)) (ζ ω) 0 else ⊤) ≤ t} := by
    ext ω
    by_cases hω : ω ∈ G
    · simp [rHit, hω]
    · simp only [rHit, hω, ↓reduceIte, mem_ofPred_eq, mem_union, mem_compl_iff, not_false_eq_true,
        true_or, iff_true]
      exact_mod_cast (zero_le (a := t))
  rw [e]
  exact ((usualAugmentation 𝓕 P).mono (zero_le (a := t)) _ hG0).compl.union (hτ t)

include hE hGm hGc hgood in
/-- **The localizing times are stopping times of the usual augmentation.** -/
theorem isStoppingTime_rLoc (hT : Coupling.IsAnnouncingSeq (usualAugmentation 𝓕 P) P ζ T) (n : ℕ) :
    IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (rLoc k G T W VL VR B ζ n ω : WithTop ℝ≥0) := by
  refine Sec2.TwoSeed.isStoppingTime_capTime ?_
    ((isStoppingTime_rHit hE hGm hGc hgood n).min
      (MathFin.isStoppingTime_exitTime_of_measurable
        (isFilteredBrownianReal_brownG_r hE hGm hGc hgood).2.1 (continuous_brownG_r hgood) n))
  have h := (isStoppingTime_const (usualAugmentation 𝓕 P) (n : ℝ≥0)).min (hT.1 n)
  convert h using 2 with ω
  push_cast
  rfl

end StoppingTime

end Loc

end Retarget

end Zhan

end InteractingSLE
