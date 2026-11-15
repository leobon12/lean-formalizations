/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.TargetChangeProcessWord
import InteractingSLE.Spec.Zhan.TargetChangeProcessObs

/-!
# The transformed Brownian path is the retargeted observable read in the new clock

Packet PROVE-SEC7-C8. Along a local integrated path, at a new time `u` before the new horizon with original time
`s = C⁻¹(u)`, the transformed Brownian path of LP9's word is the Itô observable `Ψ = obs` of
`TargetChangeProcessObs.lean` evaluated at the coordinates `Λ(s) = (V^L_s, V^R_s, α_s, β_s, C(s))` and the Brownian
value `b_s`, up to an explicit constant (`sqrt_mul_newB_eq`):

  `√κ b̃(u) = Ψ(Λ(s), b_s) − X̃`,   `X̃ = ½ Σ ρ̃^L x̃^L + ½ Σ ρ̃^R x̃^R`.

The driver is recovered from `(Λ, b)` by (N1) (`w_eq_drv`); the coefficient of `β` vanishes because the old target
carries the charge `κ − 6 − Σρ` (`LP.sum_retargetρL`), and the `α`-terms match after splitting the right marks at the
target. This identifies the (time-changed) Itô martingale of `obs` with `√κ b̃`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Finset
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Zhan

namespace Retarget

variable {κ : ℝ} {nL j m : ℕ} {xL : Fin nL → ℝ} {xR : Fin (j + 1 + m) → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin (j + 1 + m) → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin (j + 1 + m) → ℝ≥0 → ℝ}
  {b : ℝ≥0 → ℝ} {T : ℝ≥0∞}

/-- **(N1) along a local path**: `w_t = √κ b_t − ½ Σ ρ (V_t − x)` before `T`. -/
theorem w_eq_drv_of_upTo {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
    {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
    (hp : Sec2.IsSLEPathUpTo κ xL xR ρL ρR w vL vR b T) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < T)
    (α β S : ℝ) :
    w t = drv κ xL xR ρL ρR (((fun i => vL i t), (fun i => vR i t), α, β, S), b t) := by
  have hL : ∀ i, ∫ s in (0 : ℝ)..t, ρL i / (w s.toNNReal - vL i s.toNNReal) = -(ρL i / 2) * (vL i t - xL i) := by
    intro i
    have hfun : (fun s : ℝ => ρL i / (w s.toNNReal - vL i s.toNNReal)) =
        fun s => -(ρL i / 2) * (2 / (vL i s.toNNReal - w s.toNNReal)) :=
      funext fun s => Sec2.div_sub_eq_neg_half_mul _ _ _
    rw [hfun, intervalIntegral.integral_const_mul, hp.vL_eq ht i]
    ring
  have hR : ∀ i, ∫ s in (0 : ℝ)..t, ρR i / (w s.toNNReal - vR i s.toNNReal) = -(ρR i / 2) * (vR i t - xR i) := by
    intro i
    have hfun : (fun s : ℝ => ρR i / (w s.toNNReal - vR i s.toNNReal)) =
        fun s => -(ρR i / 2) * (2 / (vR i s.toNNReal - w s.toNNReal)) :=
      funext fun s => Sec2.div_sub_eq_neg_half_mul _ _ _
    rw [hfun, intervalIntegral.integral_const_mul, hp.vR_eq ht i]
    ring
  rw [hp.w_eq ht, Finset.sum_congr rfl fun i _ => hL i, Finset.sum_congr rfl fun i _ => hR i, drv]
  simp only
  have e1 : ∑ i, -(ρL i / 2) * (vL i t - xL i) = -((1 / 2) * ∑ i, ρL i * (vL i t - xL i)) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ i, -(ρR i / 2) * (vR i t - xR i) = -((1 / 2) * ∑ i, ρR i * (vR i t - xR i)) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [e1, e2]
  ring

/-- Splitting a sum over the right marks other than the target into the marks before and after it. -/
theorem sum_erase_retargetIdx (f : Fin (j + 1 + m) → ℝ) :
    ∑ i ∈ univ.erase (LP.retargetIdx j m), f i =
      (∑ i : Fin j, f (Fin.castAdd m i.castSucc)) + ∑ l : Fin m, f (Fin.natAdd (j + 1) l) := by
  have h := Finset.add_sum_erase univ f (mem_univ (LP.retargetIdx j m))
  rw [Fin.sum_univ_add, Fin.sum_univ_castSucc] at h
  have : f (LP.retargetIdx j m) = f (Fin.castAdd m (Fin.last j)) := rfl
  linarith

/-- The left sum of the transformed word, split into the original left marks, the old target, and the later right
marks. -/
theorem sum_retarget_left (g : Fin (nL + (m + 1)) → ℝ) :
    ∑ i, g i = (∑ i : Fin nL, g (Fin.castAdd (m + 1) i)) + g (Fin.natAdd nL 0) +
      ∑ l : Fin m, g (Fin.natAdd nL l.succ) := by
  rw [Fin.sum_univ_add, Fin.sum_univ_succ]
  ring

/-- **The transformed Brownian path is the observable**: `√κ b̃(u) = Ψ(Λ(s), b_s) − X̃` at `s = C⁻¹(u)`. -/
theorem sqrt_mul_newB_eq (hp : Sec2.IsSLEPathUpTo κ xL xR ρL ρR w vL vR b T) (hd : RetargetData xL xR w vL vR T)
    (hκ : 0 < κ) {u : ℝ≥0} (hu : (u : ℝ≥0∞) < newHorizon (LP.retargetPos xR) w (vR (LP.retargetIdx j m)) T) :
    Real.sqrt κ * newB κ xL xR ρL ρR w vL vR u =
      obs κ xL xR ρL ρR (LP.retargetIdx j m)
        (((fun i => vL i (invClk (rate (LP.retargetPos xR) w (vR (LP.retargetIdx j m))) u).toNNReal),
          (fun i => vR i (invClk (rate (LP.retargetPos xR) w (vR (LP.retargetIdx j m))) u).toNNReal),
          alpha (LP.retargetPos xR) w (vR (LP.retargetIdx j m))
            (invClk (rate (LP.retargetPos xR) w (vR (LP.retargetIdx j m))) u),
          beta (LP.retargetPos xR) w (vR (LP.retargetIdx j m))
            (invClk (rate (LP.retargetPos xR) w (vR (LP.retargetIdx j m))) u),
          clk (rate (LP.retargetPos xR) w (vR (LP.retargetIdx j m)))
            (invClk (rate (LP.retargetPos xR) w (vR (LP.retargetIdx j m))) u)),
          b (invClk (rate (LP.retargetPos xR) w (vR (LP.retargetIdx j m))) u).toNNReal)
        - ((1 / 2) * (∑ i, LP.retargetρL κ ρL ρR i * LP.retargetXL xL xR i)
          + (1 / 2) * (∑ i, LP.retargetρR ρR i * LP.retargetXR xR i)) := by
  obtain ⟨-, hsT, -⟩ := orig_spec hd hu
  generalize hs : invClk (rate (LP.retargetPos xR) w (vR (LP.retargetIdx j m))) u = s at hsT
  have hW : newW xR w vR u = beta (LP.retargetPos xR) w (vR (LP.retargetIdx j m)) s +
      alpha (LP.retargetPos xR) w (vR (LP.retargetIdx j m)) s /
        (vR (LP.retargetIdx j m) s.toNNReal - w s.toNNReal) := by
    simp only [newW, newPath, mobPath, mob, hs]
  have hVL : ∀ i, newVL xR w vL vR (Fin.castAdd (m + 1) i) u = beta (LP.retargetPos xR) w (vR (LP.retargetIdx j m)) s +
      alpha (LP.retargetPos xR) w (vR (LP.retargetIdx j m)) s /
        (vR (LP.retargetIdx j m) s.toNNReal - vL i s.toNNReal) := by
    intro i; simp only [newVL_castAdd, newPath, mobPath, mob, hs]
  have hV0 : newVL xR w vL vR (Fin.natAdd nL (0 : Fin (m + 1))) u =
      beta (LP.retargetPos xR) w (vR (LP.retargetIdx j m)) s := by
    simp only [newVL_natAdd_zero, newPath, hs]
  have hVA : ∀ l : Fin m, newVL xR w vL vR (Fin.natAdd nL l.succ) u =
      beta (LP.retargetPos xR) w (vR (LP.retargetIdx j m)) s + alpha (LP.retargetPos xR) w (vR (LP.retargetIdx j m)) s /
        (vR (LP.retargetIdx j m) s.toNNReal - vR (Fin.natAdd (j + 1) l.rev) s.toNNReal) := by
    intro l; simp only [newVL_natAdd_succ, newPath, mobPath, mob, hs]
  have hVR : ∀ i, newVR xR w vR i u = beta (LP.retargetPos xR) w (vR (LP.retargetIdx j m)) s +
      alpha (LP.retargetPos xR) w (vR (LP.retargetIdx j m)) s /
        (vR (LP.retargetIdx j m) s.toNNReal - vR (Fin.castAdd m i.castSucc) s.toNNReal) := by
    intro i; simp only [newVR, newPath, mobPath, mob, hs]
  -- the driver from (N1)
  have hdrv := w_eq_drv_of_upTo hp hsT (alpha (LP.retargetPos xR) w (vR (LP.retargetIdx j m)) s)
    (beta (LP.retargetPos xR) w (vR (LP.retargetIdx j m)) s) (clk (rate (LP.retargetPos xR) w (vR (LP.retargetIdx j m))) s)
  generalize alpha (LP.retargetPos xR) w (vR (LP.retargetIdx j m)) s = α at *
  generalize beta (LP.retargetPos xR) w (vR (LP.retargetIdx j m)) s = β at *
  rw [newB, mul_div_cancel₀ _ (Real.sqrt_ne_zero'.2 hκ), obs, qOf, ← hdrv, hW]
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [sum_retarget_left (fun i => LP.retargetρL κ ρL ρR i * newVL xR w vL vR i u)]
  simp only [hVL, hV0, hVA, hVR]
  have hρc : ∀ i, LP.retargetρL κ ρL ρR (Fin.castAdd (m + 1) i) = ρL i := fun i => by simp [LP.retargetρL]
  have hρ0 : LP.retargetρL κ ρL ρR (Fin.natAdd nL (0 : Fin (m + 1))) = κ - 6 - ((∑ i, ρL i) + ∑ i, ρR i) := by
    simp [LP.retargetρL]
  have hρs : ∀ l : Fin m, LP.retargetρL κ ρL ρR (Fin.natAdd nL l.succ) = ρR (Fin.natAdd (j + 1) l.rev) := fun l => by
    simp [LP.retargetρL]
  simp only [hρc, hρ0, hρs, LP.retargetρR]
  rw [sum_erase_retargetIdx (fun i => ρR i * (α / (vR (LP.retargetIdx j m) s.toNNReal - vR i s.toNNReal))),
    LP.sum_rev_eq (fun l => ρR (Fin.natAdd (j + 1) l) * (β + α / (vR (LP.retargetIdx j m) s.toNNReal -
      vR (Fin.natAdd (j + 1) l) s.toNNReal)))]
  have hsplit := LP.sum_right_split ρR
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul] at *
  rw [hsplit]
  simp only [cBeta, LP.retargetIdx]
  ring

end Retarget

end Zhan

end InteractingSLE
