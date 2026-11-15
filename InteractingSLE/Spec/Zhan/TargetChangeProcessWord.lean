/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.TargetChangeProcessTime
import InteractingSLE.Spec.Supplement.LPProbRetarget
import InteractingSLE.Spec.Sec2.AddMarksPath

/-!
# The retargeted word: the image of a local integrated path in the new clock

Packet PROVE-SEC7-C8 (Specification §7.3, (C1)–(C2), pp. 378–379; supplement Lemma LP9, p. 485). For a local
integrated `SLE_κ(ρ)` path (`Sec2.IsSLEPathUpTo`) of a word with right list of length `j + 1 + m` whose mark of Lean
index `j` (the new target, at `x_j > 0`) stays strictly right of the driver before `T`, the images under the
retargeting family `M_t` read in the new clock form a local integrated path of LP9's transformed word
(`LP.retargetXL`, `LP.retargetXR`, `LP.retargetρL`, `LP.retargetρR`) before the new horizon
(`isSLEPathUpTo_retarget`), with the new Brownian path `b̃` given by (N1) of the transformed word (`newB`). That
`b̃` is a Brownian motion is the stochastic half (Itô's formula and the time change), not proved here.

* `lt_of_forceEq`: two force points keep a strict order (linear ODE for the gap, `Zhan.eq_mul_exp_neg_integral`);
* `mob_le_mob_left`, `mob_le_mob_right`, `beta_lt_mob`, `mob_lt_beta`: the real Möbius map is increasing on each
  side of its pole, above `β` on the left and below on the right;
* `newW`, `newVL`, `newVR`, `newB`: the transformed driver, marks (original left marks, the old target, the later right
  marks reversed; the earlier right marks) and Brownian path.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Zhan

namespace Retarget

/-! ### Strict order of two force points -/

/-- **Two force points keep a strict order.** If `u = y + ∫ 2/(u − w)`, `v = x + ∫ 2/(v − w)` on `[0, S]`, `x < y`,
both velocities are integrable, almost every time is a non-collision for both, and the coefficient
`c = 2/((w − u)(w − v))` is integrable, then `v < u` on `[0, S]`. -/
theorem lt_of_forceEq {w u v : ℝ → ℝ} {x y S : ℝ} (hS : 0 ≤ S) (hxy : x < y)
    (hu : ∀ s ∈ Icc 0 S, u s = y + ∫ r in (0 : ℝ)..s, 2 / (u r - w r))
    (hv : ∀ s ∈ Icc 0 S, v s = x + ∫ r in (0 : ℝ)..s, 2 / (v r - w r))
    (hui : IntervalIntegrable (fun r => 2 / (u r - w r)) volume 0 S)
    (hvi : IntervalIntegrable (fun r => 2 / (v r - w r)) volume 0 S)
    (hc : IntervalIntegrable (fun r => 2 / ((w r - u r) * (w r - v r))) volume 0 S)
    (hne : ∀ᵐ r, r ∈ Icc 0 S → u r ≠ w r ∧ v r ≠ w r) : ∀ s ∈ Icc 0 S, v s < u s := by
  have hu0 : u 0 = y := by simpa using hu 0 ⟨le_rfl, hS⟩
  have hv0 : v 0 = x := by simpa using hv 0 ⟨le_rfl, hS⟩
  have hy : ∀ r ∈ Icc 0 S, (u r - v r) = (u 0 - v 0) +
      ∫ s in (0 : ℝ)..r, (2 / (u s - w s) - 2 / (v s - w s)) := by
    intro r hr
    have hsub : uIcc (0 : ℝ) r ⊆ uIcc 0 S := by
      rw [uIcc_of_le hr.1, uIcc_of_le hS]; exact Icc_subset_Icc le_rfl hr.2
    rw [intervalIntegral.integral_sub (hui.mono_set hsub) (hvi.mono_set hsub), hu r hr, hv r hr, hu0, hv0]
    ring
  have hfc : ∀ᵐ r ∂volume, r ∈ Icc 0 S → (2 / (u r - w r) - 2 / (v r - w r)) =
      -(2 / ((w r - u r) * (w r - v r)) * (u r - v r)) := by
    filter_upwards [hne] with r hr hrI
    exact Sec2.IsForcePath.two_div_sub_sub_two_div_sub (hr hrI).1 (hr hrI).2
  have he := Zhan.eq_mul_exp_neg_integral (y := fun r => u r - v r) hS (hui.sub hvi) hc hy hfc
  intro s hs
  have := he s hs
  rw [hu0, hv0] at this
  have hpos : 0 < u s - v s := by rw [this]; exact mul_pos (sub_pos.2 hxy) (Real.exp_pos _)
  linarith

/-! ### The real Möbius map on each side of its pole -/

section Mono

variable {xk : ℝ} {w vk : ℝ≥0 → ℝ} {t x y : ℝ}

theorem mob_le_mob_left (hxk : 0 < xk) (hxy : x ≤ y) (hy : y < vk t.toNNReal) :
    mob xk w vk t x ≤ mob xk w vk t y := by
  have hα := alpha_pos hxk w vk t
  simp only [mob]
  gcongr

theorem mob_le_mob_right (hxk : 0 < xk) (hxy : x ≤ y) (hx : vk t.toNNReal < x) :
    mob xk w vk t x ≤ mob xk w vk t y := by
  have hα := alpha_pos hxk w vk t
  simp only [mob, add_le_add_iff_left]
  rw [← neg_sub x, ← neg_sub y, div_neg, div_neg, neg_le_neg_iff]
  exact div_le_div_of_nonneg_left hα.le (by linarith) (by linarith)

theorem beta_lt_mob (hxk : 0 < xk) (hx : x < vk t.toNNReal) : beta xk w vk t < mob xk w vk t x := by
  have hα := alpha_pos hxk w vk t
  simp only [mob, lt_add_iff_pos_right]
  exact div_pos hα (by linarith)

theorem mob_lt_beta (hxk : 0 < xk) (hx : vk t.toNNReal < x) : mob xk w vk t x < beta xk w vk t := by
  have hα := alpha_pos hxk w vk t
  simp only [mob, add_lt_iff_neg_left]
  exact div_neg_of_pos_of_neg hα (by linarith)

theorem mob_injOn_left (hxk : 0 < xk) (hx : x < vk t.toNNReal) (hy : y < vk t.toNNReal)
    (h : mob xk w vk t x = mob xk w vk t y) : x = y := by
  have hα := (alpha_pos hxk w vk t).ne'
  simp only [mob, add_right_inj] at h
  rw [div_eq_div_iff (by linarith) (by linarith)] at h
  have := mul_left_cancel₀ hα h
  linarith

end Mono

/-! ### Appending antitone tuples -/

theorem antitone_fin_append {a b : ℕ} {f : Fin a → ℝ} {g : Fin b → ℝ} (hf : Antitone f) (hg : Antitone g)
    (hfg : ∀ i k, g k ≤ f i) : Antitone (Fin.append f g) := by
  intro i i' h
  induction i using Fin.addCases with
  | left i =>
    induction i' using Fin.addCases with
    | left i' =>
      simp only [Fin.append_left]
      refine hf ?_
      rw [Fin.le_def] at h ⊢; simpa only [Fin.val_castAdd] using h
    | right k => simp only [Fin.append_left, Fin.append_right]; exact hfg i k
  | right k =>
    induction i' using Fin.addCases with
    | left i' =>
      exfalso; rw [Fin.le_def, Fin.val_natAdd, Fin.val_castAdd] at h; have := i'.2; omega
    | right k' =>
      simp only [Fin.append_right]
      refine hg ?_
      rw [Fin.le_def] at h ⊢; rw [Fin.val_natAdd, Fin.val_natAdd] at h; omega

theorem antitone_fin_cons {b : ℕ} {a : ℝ} {g : Fin b → ℝ} (hg : Antitone g) (h : ∀ k, g k ≤ a) :
    Antitone (Fin.cons a g : Fin (b + 1) → ℝ) := by
  intro i i' hii
  induction i using Fin.cases with
  | zero =>
    induction i' using Fin.cases with
    | zero => exact le_rfl
    | succ k => simp only [Fin.cons_zero, Fin.cons_succ]; exact h k
  | succ k =>
    induction i' using Fin.cases with
    | zero => exact absurd hii (not_le.2 (Fin.succ_pos k))
    | succ k' =>
      simp only [Fin.cons_succ]
      exact hg (Fin.succ_le_succ_iff.1 hii)

/-! ### The retargeted word of Lemma LP9 -/

section Word

variable {κ : ℝ} {nL j m : ℕ} {xL : Fin nL → ℝ} {xR : Fin (j + 1 + m) → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin (j + 1 + m) → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin (j + 1 + m) → ℝ≥0 → ℝ}
  {b : ℝ≥0 → ℝ} {T : ℝ≥0∞}

variable (xR w vR) in
/-- The transformed driver `W̃ = M(w)` in the new clock. -/
def newW : ℝ≥0 → ℝ :=
  newPath (LP.retargetPos xR) w (vR (LP.retargetIdx j m))
    (mobPath (LP.retargetPos xR) w (vR (LP.retargetIdx j m)) w)

variable (xR w vL vR) in
/-- The transformed left marks: the images of the original left marks, the old target `β`, and the images of the
right marks after the target in reversed order (LP9's left list). -/
def newVL : Fin (nL + (m + 1)) → ℝ≥0 → ℝ := fun i u =>
  Fin.append (fun i => newPath (LP.retargetPos xR) w (vR (LP.retargetIdx j m))
      (mobPath (LP.retargetPos xR) w (vR (LP.retargetIdx j m)) (vL i)) u)
    (Fin.cons (newPath (LP.retargetPos xR) w (vR (LP.retargetIdx j m))
        (beta (LP.retargetPos xR) w (vR (LP.retargetIdx j m))) u)
      fun l : Fin m => newPath (LP.retargetPos xR) w (vR (LP.retargetIdx j m))
        (mobPath (LP.retargetPos xR) w (vR (LP.retargetIdx j m)) (vR (Fin.natAdd (j + 1) l.rev))) u) i

variable (xR w vR) in
/-- The transformed right marks: the images of the right marks before the target (LP9's right list). -/
def newVR : Fin j → ℝ≥0 → ℝ := fun i =>
  newPath (LP.retargetPos xR) w (vR (LP.retargetIdx j m))
    (mobPath (LP.retargetPos xR) w (vR (LP.retargetIdx j m)) (vR (Fin.castAdd m i.castSucc)))

variable (κ xL xR ρL ρR w vL vR) in
/-- The transformed Brownian path, from (N1) of the transformed word:
`√κ b̃ = W̃ + ½ Σ ρ̃ (Ṽ − x̃)`. -/
def newB : ℝ≥0 → ℝ := fun u =>
  (newW xR w vR u + (1 / 2) * (∑ i, LP.retargetρL κ ρL ρR i * (newVL xR w vL vR i u - LP.retargetXL xL xR i))
    + (1 / 2) * (∑ i, LP.retargetρR ρR i * (newVR xR w vR i u - LP.retargetXR xR i))) / Real.sqrt κ

/-- The facts of the original local path used by the retargeting: separation, the target's equation, and the
force-point facts of every other mark. -/
structure RetargetData (xL : Fin nL → ℝ) (xR : Fin (j + 1 + m) → ℝ) (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ)
    (vR : Fin (j + 1 + m) → ℝ≥0 → ℝ) (T : ℝ≥0∞) : Prop where
  pos : 0 < LP.retargetPos xR
  sep : SepUpTo w (vR (LP.retargetIdx j m)) T
  target : TargetEq w (vR (LP.retargetIdx j m)) (LP.retargetPos xR) T
  markL : ∀ i, IsMarkUpTo w (vR (LP.retargetIdx j m)) (vL i) (xL i) T
  markR : ∀ i : Fin j, IsMarkUpTo w (vR (LP.retargetIdx j m)) (vR (Fin.castAdd m i.castSucc))
    (xR (Fin.castAdd m i.castSucc)) T
  markA : ∀ l : Fin m, IsMarkUpTo w (vR (LP.retargetIdx j m)) (vR (Fin.natAdd (j + 1) l))
    (xR (Fin.natAdd (j + 1) l)) T
  ltR : ∀ i : Fin j, ∀ t : ℝ≥0, (t : ℝ≥0∞) < T → vR (Fin.castAdd m i.castSucc) t < vR (LP.retargetIdx j m) t
  ltA : ∀ l : Fin m, ∀ t : ℝ≥0, (t : ℝ≥0∞) < T → vR (LP.retargetIdx j m) t < vR (Fin.natAdd (j + 1) l) t

end Word

/-! ### The data from a local integrated path -/

/-- `2/(v − w)` is integrable when `(w − v)⁻¹` is. -/
theorem intervalIntegrable_two_div_of_inv {w v : ℝ → ℝ} {t : ℝ}
    (h : IntervalIntegrable (fun s => (w s - v s)⁻¹) volume 0 t) :
    IntervalIntegrable (fun s => 2 / (v s - w s)) volume 0 t :=
  (h.const_mul (-2)).congr fun s _ => by
    rw [div_eq_mul_inv, ← neg_sub (w s), inv_neg]
    ring

/-- **Strict order of two force points before `T`**, in the frozen path form. -/
theorem lt_of_marks {w u v : ℝ≥0 → ℝ} {x y : ℝ} {T : ℝ≥0∞} (hxy : x < y)
    (hu : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T → u t = y + ∫ s in (0 : ℝ)..t, 2 / (u s.toNNReal - w s.toNNReal))
    (hv : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T → v t = x + ∫ s in (0 : ℝ)..t, 2 / (v s.toNNReal - w s.toNNReal))
    (hui : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T →
      IntervalIntegrable (fun s : ℝ => (w s.toNNReal - u s.toNNReal)⁻¹) volume 0 t)
    (hvi : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T →
      IntervalIntegrable (fun s : ℝ => (w s.toNNReal - v s.toNNReal)⁻¹) volume 0 t)
    (hc : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T → IntervalIntegrable
      (fun s : ℝ => 2 / ((w s.toNNReal - u s.toNNReal) * (w s.toNNReal - v s.toNNReal))) volume 0 t)
    (hcu : volume {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < T ∧ w s.toNNReal = u s.toNNReal} = 0)
    (hcv : volume {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < T ∧ w s.toNNReal = v s.toNNReal} = 0)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < T) : v t < u t := by
  have htT : (((t : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < T := by rwa [Real.toNNReal_coe]
  have hreal : ∀ {f : ℝ≥0 → ℝ} {z : ℝ}, (∀ t : ℝ≥0, (t : ℝ≥0∞) < T →
      f t = z + ∫ s in (0 : ℝ)..t, 2 / (f s.toNNReal - w s.toNNReal)) →
      ∀ s ∈ Icc 0 (t : ℝ), f s.toNNReal = z + ∫ r in (0 : ℝ)..s, 2 / (f r.toNNReal - w r.toNNReal) := by
    intro f z hf s hs
    rw [hf _ (lt_of_mem_Icc htT hs), Real.coe_toNNReal _ hs.1]
  have hne : ∀ᵐ r, r ∈ Icc 0 (t : ℝ) → u r.toNNReal ≠ w r.toNNReal ∧ v r.toNNReal ≠ w r.toNNReal := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hcu, measure_eq_zero_iff_ae_notMem.1 hcv]
      with r h1 h2 hr
    exact ⟨fun he => h1 ⟨hr.1, lt_of_mem_Icc htT hr, he.symm⟩,
      fun he => h2 ⟨hr.1, lt_of_mem_Icc htT hr, he.symm⟩⟩
  have := lt_of_forceEq (w := fun s => w s.toNNReal) (u := fun s => u s.toNNReal) (v := fun s => v s.toNNReal)
    t.coe_nonneg hxy (hreal hu) (hreal hv) (intervalIntegrable_two_div_of_inv (hui t ht))
    (intervalIntegrable_two_div_of_inv (hvi t ht)) (hc t ht) hne t ⟨t.coe_nonneg, le_rfl⟩
  simpa using this

/-- **The retargeting data of a local integrated path** whose target (Lean index `j ≥ 1` of a distinct word) stays
strictly right of the driver before `T`. -/
theorem retargetData_of_isSLEPathUpTo {κ : ℝ} {nL j m : ℕ} {xL : Fin nL → ℝ} {xR : Fin (j + 1 + m) → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin (j + 1 + m) → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ}
    {vR : Fin (j + 1 + m) → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {T : ℝ≥0∞}
    (hp : Sec2.IsSLEPathUpTo κ xL xR ρL ρR w vL vR b T) (hD : LP.IsDistinctForceWord xL xR) (hj : 1 ≤ j)
    (hq : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T → w t < vR (LP.retargetIdx j m) t) :
    RetargetData xL xR w vL vR T := by
  obtain ⟨⟨-, -, -, hR0⟩, -, hmono⟩ := hD
  set k := LP.retargetIdx j m with hk
  have hsep : SepUpTo w (vR k) T := fun S hS0 hST =>
    ⟨hS0, continuousOn_real_of_lt hp.continuousOn_w hST, continuousOn_real_of_lt (hp.continuousOn_vR k) hST,
      fun s hs => sub_pos.2 (hq _ (lt_of_mem_Icc hST hs))⟩
  -- `2/(w − V)` is continuous before `T`
  have hcont : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T →
      ContinuousOn (fun s : ℝ => 2 / (w s.toNNReal - vR k s.toNNReal)) (uIcc 0 (t : ℝ)) := by
    intro t ht
    have htT : (((t : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < T := by rwa [Real.toNNReal_coe]
    have hs := hsep t t.coe_nonneg htT
    rw [uIcc_of_le t.coe_nonneg]
    refine continuousOn_const.div (hs.cont_w.sub hs.cont_vk) fun s hs' => ?_
    have := hs.pos s hs'
    simp only [gap] at this
    linarith
  have hltR : ∀ i : Fin j, ∀ t : ℝ≥0, (t : ℝ≥0∞) < T → vR (Fin.castAdd m i.castSucc) t < vR k t := by
    intro i t ht
    refine lt_of_marks (LP.xR_castAdd_castSucc_lt hmono i) (fun t ht => hp.vR_eq ht k)
      (fun t ht => hp.vR_eq ht _) (fun t ht => hp.integrable_gapR ht k) (fun t ht => hp.integrable_gapR ht _)
      (fun t ht => ((hp.integrable_gapR ht (Fin.castAdd m i.castSucc)).continuousOn_mul (hcont t ht)).congr
        fun s _ => ?_) (hp.volume_collisionR k) (hp.volume_collisionR _) ht
    simp only [div_eq_mul_inv, mul_inv]
    ring
  have hltA : ∀ l : Fin m, ∀ t : ℝ≥0, (t : ℝ≥0∞) < T → vR k t < vR (Fin.natAdd (j + 1) l) t := by
    intro l t ht
    refine lt_of_marks (LP.retargetPos_lt_xR_natAdd hmono l) (fun t ht => hp.vR_eq ht _)
      (fun t ht => hp.vR_eq ht k) (fun t ht => hp.integrable_gapR ht _) (fun t ht => hp.integrable_gapR ht k)
      (fun t ht => ((hp.integrable_gapR ht (Fin.natAdd (j + 1) l)).continuousOn_mul (hcont t ht)).congr
        fun s _ => ?_) (hp.volume_collisionR _) (hp.volume_collisionR k) ht
    simp only [div_eq_mul_inv, mul_inv]
    ring
  refine ⟨LP.retargetPos_pos hmono hR0 hj, hsep, fun t ht => hp.vR_eq ht k, fun i => ?_, fun i => ?_,
    fun l => ?_, hltR, hltA⟩
  · exact ⟨fun t ht => hp.vL_eq ht i, hp.continuousOn_vL i, fun t ht => hp.integrable_gapL ht i,
      hp.volume_collisionL i, fun t ht => ne_of_lt ((hp.vL_le_w ht i).trans_lt (hq t ht))⟩
  · exact ⟨fun t ht => hp.vR_eq ht _, hp.continuousOn_vR _, fun t ht => hp.integrable_gapR ht _,
      hp.volume_collisionR _, fun t ht => (hltR i t ht).ne⟩
  · exact ⟨fun t ht => hp.vR_eq ht _, hp.continuousOn_vR _, fun t ht => hp.integrable_gapR ht _,
      hp.volume_collisionR _, fun t ht => (hltA l t ht).ne'⟩

/-! ### The transformed word: values at each index -/

section Values

variable {nL j m : ℕ} (xR : Fin (j + 1 + m) → ℝ) (w : ℝ≥0 → ℝ) (vL : Fin nL → ℝ≥0 → ℝ)
  (vR : Fin (j + 1 + m) → ℝ≥0 → ℝ) (u : ℝ≥0)

@[simp] theorem newVL_castAdd (i : Fin nL) :
    newVL xR w vL vR (Fin.castAdd (m + 1) i) u = newPath (LP.retargetPos xR) w (vR (LP.retargetIdx j m))
      (mobPath (LP.retargetPos xR) w (vR (LP.retargetIdx j m)) (vL i)) u := by
  simp [newVL]

@[simp] theorem newVL_natAdd_zero :
    newVL xR w vL vR (Fin.natAdd nL (0 : Fin (m + 1))) u =
      newPath (LP.retargetPos xR) w (vR (LP.retargetIdx j m)) (beta (LP.retargetPos xR) w (vR (LP.retargetIdx j m)))
        u := by
  simp [newVL]

@[simp] theorem newVL_natAdd_succ (l : Fin m) :
    newVL xR w vL vR (Fin.natAdd nL l.succ) u = newPath (LP.retargetPos xR) w (vR (LP.retargetIdx j m))
      (mobPath (LP.retargetPos xR) w (vR (LP.retargetIdx j m)) (vR (Fin.natAdd (j + 1) l.rev))) u := by
  simp [newVL]

variable (xL : Fin nL → ℝ)

@[simp] theorem retargetXL_castAdd (i : Fin nL) :
    LP.retargetXL xL xR (Fin.castAdd (m + 1) i) = Sec7.targetChangeReal (LP.retargetPos xR) (xL i) := by
  simp [LP.retargetXL]

@[simp] theorem retargetXL_natAdd_zero : LP.retargetXL xL xR (Fin.natAdd nL (0 : Fin (m + 1))) = -1 := by
  simp [LP.retargetXL]

@[simp] theorem retargetXL_natAdd_succ (l : Fin m) :
    LP.retargetXL xL xR (Fin.natAdd nL l.succ) =
      Sec7.targetChangeReal (LP.retargetPos xR) (xR (Fin.natAdd (j + 1) l.rev)) := by
  simp [LP.retargetXL]

end Values

/-- `M_0(x) = ψ(x)` (`Sec7.targetChangeReal`) when the target starts at `x_k ≠ x`. -/
theorem mob_zero_eq_targetChangeReal {xk : ℝ} {w vk : ℝ≥0 → ℝ} (h0 : vk 0 = xk) {x : ℝ} (hx : x ≠ xk) :
    mob xk w vk 0 x = Sec7.targetChangeReal xk x := by
  rw [mob_zero h0 (sub_ne_zero.2 (Ne.symm hx)), Sec7.targetChangeReal]

/-! ### The fields of the transformed local path -/

section Fields

variable {κ : ℝ} {nL j m : ℕ} {xL : Fin nL → ℝ} {xR : Fin (j + 1 + m) → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin (j + 1 + m) → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin (j + 1 + m) → ℝ≥0 → ℝ}
  {b : ℝ≥0 → ℝ} {T : ℝ≥0∞}

/-- The original time of a new time before `T̃`, and the facts there. -/
theorem orig_spec (hd : RetargetData xL xR w vL vR T) {u : ℝ≥0}
    (hu : (u : ℝ≥0∞) < newHorizon (LP.retargetPos xR) w (vR (LP.retargetIdx j m)) T) :
    0 ≤ invClk (rate (LP.retargetPos xR) w (vR (LP.retargetIdx j m))) u ∧
      (((invClk (rate (LP.retargetPos xR) w (vR (LP.retargetIdx j m))) u).toNNReal : ℝ≥0) : ℝ≥0∞) < T ∧
      w (invClk (rate (LP.retargetPos xR) w (vR (LP.retargetIdx j m))) u).toNNReal <
        vR (LP.retargetIdx j m) (invClk (rate (LP.retargetPos xR) w (vR (LP.retargetIdx j m))) u).toNNReal := by
  obtain ⟨S, hST, -, -, hmem, -⟩ := newTime_spec hd.sep hd.pos hu
  refine ⟨hmem.1, invClk_lt hd.sep hd.pos hu, ?_⟩
  have := (hd.sep.isSep_of_lt hST).pos _ hmem
  simp only [gap] at this
  linarith

theorem vk_zero (hp : Sec2.IsSLEPathUpTo κ xL xR ρL ρR w vL vR b T) :
    vR (LP.retargetIdx j m) 0 = LP.retargetPos xR := hp.vR_zero _

theorem newW_zero (hp : Sec2.IsSLEPathUpTo κ xL xR ρL ρR w vL vR b T) (hd : RetargetData xL xR w vL vR T) :
    newW xR w vR 0 = 0 := by
  simp only [newW, newPath_zero, mobPath, Real.toNNReal_zero, hp.w_zero]
  rw [mob_zero_eq_targetChangeReal (vk_zero hp) hd.pos.ne, Sec7.targetChangeReal, zero_div]

theorem newVL_zero (hp : Sec2.IsSLEPathUpTo κ xL xR ρL ρR w vL vR b T) (hd : RetargetData xL xR w vL vR T)
    (hD : LP.IsDistinctForceWord xL xR) (i : Fin (nL + (m + 1))) :
    newVL xR w vL vR i 0 = LP.retargetXL xL xR i := by
  obtain ⟨⟨-, hL0, -, -⟩, -, hmono⟩ := hD
  induction i using Fin.addCases with
  | left i =>
    simp only [newVL_castAdd, retargetXL_castAdd, newPath_zero, mobPath, Real.toNNReal_zero, hp.vL_zero]
    exact mob_zero_eq_targetChangeReal (vk_zero hp) (ne_of_lt (lt_of_le_of_lt (hL0 i) hd.pos))
  | right k =>
    induction k using Fin.cases with
    | zero => simp
    | succ l =>
      simp only [newVL_natAdd_succ, retargetXL_natAdd_succ, newPath_zero, mobPath, Real.toNNReal_zero,
        hp.vR_zero]
      exact mob_zero_eq_targetChangeReal (vk_zero hp) (LP.retargetPos_lt_xR_natAdd hmono _).ne'

theorem newVR_zero (hp : Sec2.IsSLEPathUpTo κ xL xR ρL ρR w vL vR b T) (hD : LP.IsDistinctForceWord xL xR)
    (i : Fin j) : newVR xR w vR i 0 = LP.retargetXR xR i := by
  obtain ⟨-, -, hmono⟩ := hD
  simp only [newVR, LP.retargetXR, newPath_zero, mobPath, Real.toNNReal_zero, hp.vR_zero]
  exact mob_zero_eq_targetChangeReal (vk_zero hp) (LP.xR_castAdd_castSucc_lt hmono i).ne

/-- The image of a mark is continuous in the new clock. -/
theorem continuousOn_newPath_mark (hd : RetargetData xL xR w vL vR T) {v : ℝ≥0 → ℝ} {x : ℝ}
    (hv : IsMarkUpTo w (vR (LP.retargetIdx j m)) v x T) :
    ContinuousOn (newPath (LP.retargetPos xR) w (vR (LP.retargetIdx j m))
      (mobPath (LP.retargetPos xR) w (vR (LP.retargetIdx j m)) v))
      {u | (u : ℝ≥0∞) < newHorizon (LP.retargetPos xR) w (vR (LP.retargetIdx j m)) T} :=
  continuousOn_newPath hd.sep hd.pos fun _ hS => (hd.sep.isSep_of_lt hS).continuousOn_mobPath
    (continuousOn_real_of_lt hv.cont (by rwa [Real.toNNReal_coe]))
    fun s hs => sub_ne_zero.2 (hv.ne _ (lt_of_mem_Icc (by rwa [Real.toNNReal_coe]) hs)).symm

theorem continuousOn_newW (hd : RetargetData xL xR w vL vR T) :
    ContinuousOn (newW xR w vR)
      {u | (u : ℝ≥0∞) < newHorizon (LP.retargetPos xR) w (vR (LP.retargetIdx j m)) T} :=
  continuousOn_newPath hd.sep hd.pos fun _ hS => (hd.sep.isSep_of_lt hS).continuousOn_mobPath_w

theorem continuousOn_newVL (hd : RetargetData xL xR w vL vR T) (i : Fin (nL + (m + 1))) :
    ContinuousOn (newVL xR w vL vR i)
      {u | (u : ℝ≥0∞) < newHorizon (LP.retargetPos xR) w (vR (LP.retargetIdx j m)) T} := by
  induction i using Fin.addCases with
  | left i =>
    have e : newVL xR w vL vR (Fin.castAdd (m + 1) i) = newPath (LP.retargetPos xR) w (vR (LP.retargetIdx j m))
        (mobPath (LP.retargetPos xR) w (vR (LP.retargetIdx j m)) (vL i)) := funext fun u => newVL_castAdd _ _ _ _ _ _
    rw [e]; exact continuousOn_newPath_mark hd (hd.markL i)
  | right k =>
    induction k using Fin.cases with
    | zero =>
      have e : newVL xR w vL vR (Fin.natAdd nL (0 : Fin (m + 1))) = newPath (LP.retargetPos xR) w
          (vR (LP.retargetIdx j m)) (beta (LP.retargetPos xR) w (vR (LP.retargetIdx j m))) :=
        funext fun u => newVL_natAdd_zero _ _ _ _ _
      rw [e]
      exact continuousOn_newPath hd.sep hd.pos fun _ hS => (hd.sep.isSep_of_lt hS).continuousOn_beta
    | succ l =>
      have e : newVL xR w vL vR (Fin.natAdd nL l.succ) = newPath (LP.retargetPos xR) w (vR (LP.retargetIdx j m))
          (mobPath (LP.retargetPos xR) w (vR (LP.retargetIdx j m)) (vR (Fin.natAdd (j + 1) l.rev))) :=
        funext fun u => newVL_natAdd_succ _ _ _ _ _ _
      rw [e]; exact continuousOn_newPath_mark hd (hd.markA _)

theorem continuousOn_newVR (hd : RetargetData xL xR w vL vR T) (i : Fin j) :
    ContinuousOn (newVR xR w vR i)
      {u | (u : ℝ≥0∞) < newHorizon (LP.retargetPos xR) w (vR (LP.retargetIdx j m)) T} :=
  continuousOn_newPath_mark hd (hd.markR i)

end Fields

section Order

variable {κ : ℝ} {nL j m : ℕ} {xL : Fin nL → ℝ} {xR : Fin (j + 1 + m) → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin (j + 1 + m) → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin (j + 1 + m) → ℝ≥0 → ℝ}
  {b : ℝ≥0 → ℝ} {T : ℝ≥0∞} (hp : Sec2.IsSLEPathUpTo κ xL xR ρL ρR w vL vR b T)
  (hd : RetargetData xL xR w vL vR T) {u : ℝ≥0}
  (hu : (u : ℝ≥0∞) < newHorizon (LP.retargetPos xR) w (vR (LP.retargetIdx j m)) T)
include hp hd hu

theorem antitone_newVL : Antitone fun i => newVL xR w vL vR i u := by
  obtain ⟨-, hsT, hwk⟩ := orig_spec hd hu
  have hpos := hd.pos
  unfold newVL
  refine antitone_fin_append ?_ (antitone_fin_cons ?_ ?_) ?_
  · intro i i' hii
    exact mob_le_mob_left hpos (hp.antitone_vL hsT hii) ((hp.vL_le_w hsT i).trans_lt hwk)
  · intro l l' hll
    refine mob_le_mob_right hpos (hp.monotone_vR hsT ?_) (hd.ltA _ _ hsT)
    rw [Fin.le_def, Fin.val_natAdd, Fin.val_natAdd, Fin.val_rev, Fin.val_rev]
    have := Fin.le_def.1 hll
    omega
  · intro l
    exact (mob_lt_beta hpos (hd.ltA _ _ hsT)).le
  · intro i k
    induction k using Fin.cases with
    | zero => exact (beta_lt_mob hpos ((hp.vL_le_w hsT i).trans_lt hwk)).le
    | succ l =>
      exact ((mob_lt_beta hpos (hd.ltA _ _ hsT)).trans (beta_lt_mob hpos ((hp.vL_le_w hsT i).trans_lt hwk))).le

theorem newVL_le_newW (i : Fin (nL + (m + 1))) : newVL xR w vL vR i u ≤ newW xR w vR u := by
  obtain ⟨-, hsT, hwk⟩ := orig_spec hd hu
  have hpos := hd.pos
  induction i using Fin.addCases with
  | left i =>
    rw [newVL_castAdd]
    exact mob_le_mob_left hpos (hp.vL_le_w hsT i) hwk
  | right k =>
    induction k using Fin.cases with
    | zero =>
      rw [newVL_natAdd_zero]
      exact (beta_lt_mob hpos hwk).le
    | succ l =>
      rw [newVL_natAdd_succ]
      exact ((mob_lt_beta hpos (hd.ltA _ _ hsT)).trans (beta_lt_mob hpos hwk)).le

theorem newW_le_newVR (i : Fin j) : newW xR w vR u ≤ newVR xR w vR i u := by
  obtain ⟨-, hsT, -⟩ := orig_spec hd hu
  exact mob_le_mob_left hd.pos (hp.w_le_vR hsT _) (hd.ltR i _ hsT)

theorem monotone_newVR : Monotone fun i => newVR xR w vR i u := by
  obtain ⟨-, hsT, -⟩ := orig_spec hd hu
  intro i i' hii
  refine mob_le_mob_left hd.pos (hp.monotone_vR hsT ?_) (hd.ltR i' _ hsT)
  rw [Fin.le_def]
  simpa using Fin.le_def.1 hii

omit hp in
/-- The driver meets no transformed left mark coming from the old target or the later right marks. -/
theorem newVL_natAdd_ne (k : Fin (m + 1)) : newVL xR w vL vR (Fin.natAdd nL k) u ≠ newW xR w vR u := by
  obtain ⟨-, hsT, hwk⟩ := orig_spec hd hu
  have hpos := hd.pos
  induction k using Fin.cases with
  | zero =>
    rw [newVL_natAdd_zero]
    exact (beta_lt_mob hpos hwk).ne
  | succ l =>
    rw [newVL_natAdd_succ]
    exact ((mob_lt_beta hpos (hd.ltA _ _ hsT)).trans (beta_lt_mob hpos hwk)).ne

end Order

section Equations

variable {κ : ℝ} {nL j m : ℕ} {xL : Fin nL → ℝ} {xR : Fin (j + 1 + m) → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin (j + 1 + m) → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin (j + 1 + m) → ℝ≥0 → ℝ}
  {b : ℝ≥0 → ℝ} {T : ℝ≥0∞} (hp : Sec2.IsSLEPathUpTo κ xL xR ρL ρR w vL vR b T)
  (hd : RetargetData xL xR w vL vR T) (hD : LP.IsDistinctForceWord xL xR)
include hp hd hD

theorem newVL_eq {u : ℝ≥0} (hu : (u : ℝ≥0∞) < newHorizon (LP.retargetPos xR) w (vR (LP.retargetIdx j m)) T)
    (i : Fin (nL + (m + 1))) : newVL xR w vL vR i u = LP.retargetXL xL xR i +
      ∫ r in (0 : ℝ)..u, 2 / (newVL xR w vL vR i r.toNNReal - newW xR w vR r.toNNReal) := by
  obtain ⟨⟨-, hL0, -, -⟩, -, hmono⟩ := hD
  induction i using Fin.addCases with
  | left i =>
    simp only [newVL_castAdd, retargetXL_castAdd]
    rw [newPath_mob_eq hd.sep hd.pos hd.target (hd.markL i) hu,
      mob_zero_eq_targetChangeReal (vk_zero hp) (ne_of_lt (lt_of_le_of_lt (hL0 i) hd.pos))]
    rfl
  | right k =>
    induction k using Fin.cases with
    | zero =>
      simp only [newVL_natAdd_zero, retargetXL_natAdd_zero]
      rw [newPath_beta_eq hd.sep hd.pos hu]
      rfl
    | succ l =>
      simp only [newVL_natAdd_succ, retargetXL_natAdd_succ]
      rw [newPath_mob_eq hd.sep hd.pos hd.target (hd.markA _) hu,
        mob_zero_eq_targetChangeReal (vk_zero hp) (LP.retargetPos_lt_xR_natAdd hmono _).ne']
      rfl

theorem newVR_eq {u : ℝ≥0} (hu : (u : ℝ≥0∞) < newHorizon (LP.retargetPos xR) w (vR (LP.retargetIdx j m)) T)
    (i : Fin j) : newVR xR w vR i u = LP.retargetXR xR i +
      ∫ r in (0 : ℝ)..u, 2 / (newVR xR w vR i r.toNNReal - newW xR w vR r.toNNReal) := by
  obtain ⟨-, -, hmono⟩ := hD
  simp only [newVR, LP.retargetXR]
  rw [newPath_mob_eq hd.sep hd.pos hd.target (hd.markR i) hu,
    mob_zero_eq_targetChangeReal (vk_zero hp) (LP.xR_castAdd_castSucc_lt hmono i).ne]
  rfl

omit hp hD in
theorem integrable_newGapL {u : ℝ≥0}
    (hu : (u : ℝ≥0∞) < newHorizon (LP.retargetPos xR) w (vR (LP.retargetIdx j m)) T) (i : Fin (nL + (m + 1))) :
    IntervalIntegrable (fun s : ℝ => (newW xR w vR s.toNNReal - newVL xR w vL vR i s.toNNReal)⁻¹) volume 0 u := by
  induction i using Fin.addCases with
  | left i =>
    simp only [newVL_castAdd]
    exact intervalIntegrable_newPath_inv hd.sep hd.pos (hd.markL i) hu
  | right k =>
    induction k using Fin.cases with
    | zero =>
      simp only [newVL_natAdd_zero]
      exact intervalIntegrable_newPath_beta_inv hd.sep hd.pos hu
    | succ l =>
      simp only [newVL_natAdd_succ]
      exact intervalIntegrable_newPath_inv hd.sep hd.pos (hd.markA _) hu

omit hp hD in
theorem integrable_newGapR {u : ℝ≥0}
    (hu : (u : ℝ≥0∞) < newHorizon (LP.retargetPos xR) w (vR (LP.retargetIdx j m)) T) (i : Fin j) :
    IntervalIntegrable (fun s : ℝ => (newW xR w vR s.toNNReal - newVR xR w vR i s.toNNReal)⁻¹) volume 0 u :=
  intervalIntegrable_newPath_inv hd.sep hd.pos (hd.markR i) hu

omit hp hD in
theorem volume_newCollisionL (i : Fin (nL + (m + 1))) :
    volume {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < newHorizon (LP.retargetPos xR) w (vR (LP.retargetIdx j m)) T ∧
      newW xR w vR s.toNNReal = newVL xR w vL vR i s.toNNReal} = 0 := by
  induction i using Fin.addCases with
  | left i =>
    simp only [newVL_castAdd]
    exact volume_newCollision hd.sep hd.pos (hd.markL i)
  | right k =>
    induction k using Fin.cases with
    | zero =>
      simp only [newVL_natAdd_zero]
      refine measure_mono_null (fun s hs => ?_) measure_empty
      exact absurd hs.2.2 (newPath_w_ne_beta hd.sep hd.pos hs.2.1)
    | succ l =>
      simp only [newVL_natAdd_succ]
      exact volume_newCollision hd.sep hd.pos (hd.markA _)

omit hp hD in
theorem volume_newCollisionR (i : Fin j) :
    volume {s : ℝ | 0 ≤ s ∧ (s.toNNReal : ℝ≥0∞) < newHorizon (LP.retargetPos xR) w (vR (LP.retargetIdx j m)) T ∧
      newW xR w vR s.toNNReal = newVR xR w vR i s.toNNReal} = 0 :=
  volume_newCollision hd.sep hd.pos (hd.markR i)

end Equations

section Assembly

variable {κ : ℝ} {nL j m : ℕ} {xL : Fin nL → ℝ} {xR : Fin (j + 1 + m) → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin (j + 1 + m) → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin (j + 1 + m) → ℝ≥0 → ℝ}
  {b : ℝ≥0 → ℝ} {T : ℝ≥0∞} (hp : Sec2.IsSLEPathUpTo κ xL xR ρL ρR w vL vR b T)
  (hd : RetargetData xL xR w vL vR T) (hD : LP.IsDistinctForceWord xL xR)
include hp hd hD

/-- **(N1) of the transformed word**: the transformed driver is `√κ b̃` plus the integrated force drift. -/
theorem newW_eq (hκ : 0 < κ) {u : ℝ≥0}
    (hu : (u : ℝ≥0∞) < newHorizon (LP.retargetPos xR) w (vR (LP.retargetIdx j m)) T) :
    newW xR w vR u = Real.sqrt κ * newB κ xL xR ρL ρR w vL vR u
      + (∑ i, ∫ s in (0 : ℝ)..u, LP.retargetρL κ ρL ρR i / (newW xR w vR s.toNNReal - newVL xR w vL vR i s.toNNReal))
      + (∑ i, ∫ s in (0 : ℝ)..u, LP.retargetρR ρR i / (newW xR w vR s.toNNReal - newVR xR w vR i s.toNNReal)) := by
  have hL : ∀ i, ∫ s in (0 : ℝ)..u, LP.retargetρL κ ρL ρR i /
      (newW xR w vR s.toNNReal - newVL xR w vL vR i s.toNNReal) =
      -(LP.retargetρL κ ρL ρR i / 2) * (newVL xR w vL vR i u - LP.retargetXL xL xR i) := by
    intro i
    have hfun : (fun s : ℝ => LP.retargetρL κ ρL ρR i / (newW xR w vR s.toNNReal - newVL xR w vL vR i s.toNNReal)) =
        fun s => -(LP.retargetρL κ ρL ρR i / 2) * (2 / (newVL xR w vL vR i s.toNNReal - newW xR w vR s.toNNReal)) :=
      funext fun s => Sec2.div_sub_eq_neg_half_mul _ _ _
    rw [hfun, intervalIntegral.integral_const_mul, newVL_eq hp hd hD hu i]
    ring
  have hR : ∀ i, ∫ s in (0 : ℝ)..u, LP.retargetρR ρR i / (newW xR w vR s.toNNReal - newVR xR w vR i s.toNNReal) =
      -(LP.retargetρR ρR i / 2) * (newVR xR w vR i u - LP.retargetXR xR i) := by
    intro i
    have hfun : (fun s : ℝ => LP.retargetρR ρR i / (newW xR w vR s.toNNReal - newVR xR w vR i s.toNNReal)) =
        fun s => -(LP.retargetρR ρR i / 2) * (2 / (newVR xR w vR i s.toNNReal - newW xR w vR s.toNNReal)) :=
      funext fun s => Sec2.div_sub_eq_neg_half_mul _ _ _
    rw [hfun, intervalIntegral.integral_const_mul, newVR_eq hp hd hD hu i]
    ring
  rw [Finset.sum_congr rfl fun i _ => hL i, Finset.sum_congr rfl fun i _ => hR i]
  have e1 : ∑ i, -(LP.retargetρL κ ρL ρR i / 2) * (newVL xR w vL vR i u - LP.retargetXL xL xR i) =
      -((1 / 2) * ∑ i, LP.retargetρL κ ρL ρR i * (newVL xR w vL vR i u - LP.retargetXL xL xR i)) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ i, -(LP.retargetρR ρR i / 2) * (newVR xR w vR i u - LP.retargetXR xR i) =
      -((1 / 2) * ∑ i, LP.retargetρR ρR i * (newVR xR w vR i u - LP.retargetXR xR i)) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e1, e2, newB, mul_div_cancel₀ _ (Real.sqrt_ne_zero'.2 hκ)]
  ring

omit hD in
/-- **The transformed state is not at a threshold before `T̃`**: its colliding sums are those of the original
state at the original time. -/
theorem not_threshold_new {u : ℝ≥0}
    (hu : (u : ℝ≥0∞) < newHorizon (LP.retargetPos xR) w (vR (LP.retargetIdx j m)) T) :
    ¬ ForceWord.ThresholdCondition (LP.retargetρL κ ρL ρR) (LP.retargetρR ρR) (newW xR w vR u)
      (fun i => newVL xR w vL vR i u) (fun i => newVR xR w vR i u) := by
  obtain ⟨-, hsT, hwk⟩ := orig_spec hd hu
  set s := invClk (rate (LP.retargetPos xR) w (vR (LP.retargetIdx j m))) u with hsdef
  have hpos := hd.pos
  have eL : (∑ i ∈ Finset.univ.filter (fun i => newVL xR w vL vR i u = newW xR w vR u), LP.retargetρL κ ρL ρR i) =
      ∑ i ∈ Finset.univ.filter (fun i => vL i s.toNNReal = w s.toNNReal), ρL i := by
    rw [Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_add]
    have h2 : ∑ k : Fin (m + 1), (if newVL xR w vL vR (Fin.natAdd nL k) u = newW xR w vR u then
        LP.retargetρL κ ρL ρR (Fin.natAdd nL k) else 0) = 0 :=
      Finset.sum_eq_zero fun k _ => ite_eq_right (newVL_natAdd_ne hd hu k)
    rw [h2, add_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hρ : LP.retargetρL κ ρL ρR (Fin.castAdd (m + 1) i) = ρL i := by simp [LP.retargetρL]
    have hiff : newVL xR w vL vR (Fin.castAdd (m + 1) i) u = newW xR w vR u ↔ vL i s.toNNReal = w s.toNNReal :=
      ⟨fun h => mob_injOn_left hpos ((hp.vL_le_w hsT i).trans_lt hwk) hwk (by rw [newVL_castAdd] at h; exact h),
        fun h => by rw [newVL_castAdd]; simp only [newW, newPath, mobPath]; rw [h]⟩
    rw [if_congr hiff hρ rfl]
  have eR : (∑ i ∈ Finset.univ.filter (fun i => newVR xR w vR i u = newW xR w vR u), LP.retargetρR ρR i) =
      ∑ i ∈ Finset.univ.filter (fun i => vR i s.toNNReal = w s.toNNReal), ρR i := by
    rw [Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_add, Fin.sum_univ_castSucc]
    have h2 : ∑ l : Fin m, (if vR (Fin.natAdd (j + 1) l) s.toNNReal = w s.toNNReal then
        ρR (Fin.natAdd (j + 1) l) else 0) = 0 :=
      Finset.sum_eq_zero fun l _ => ite_eq_right (ne_of_gt (hwk.trans (hd.ltA l _ hsT)))
    have h3 : (if vR (Fin.castAdd m (Fin.last j)) s.toNNReal = w s.toNNReal then
        ρR (Fin.castAdd m (Fin.last j)) else 0) = 0 := ite_eq_right (ne_of_gt hwk)
    rw [h2, h3, add_zero, add_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hiff : newVR xR w vR i u = newW xR w vR u ↔ vR (Fin.castAdd m i.castSucc) s.toNNReal = w s.toNNReal :=
      ⟨fun h => mob_injOn_left hpos (hd.ltR i _ hsT) hwk h,
        fun h => by simp only [newVR, newW, newPath, mobPath]; rw [h]⟩
    rw [if_congr hiff rfl rfl]
    rfl
  intro hthr
  refine hp.not_threshold hsT ?_
  unfold ForceWord.ThresholdCondition at hthr ⊢
  rwa [eL, eR] at hthr

/-- **The retargeted local path** (Specification §7.3, (C1)–(C2); Lemma LP9): the images of a local integrated
`SLE_κ(ρ)` path under the retargeting family, read in the new clock, form a local integrated `SLE_κ(ρ̃)` path of
LP9's transformed word before the new horizon, with the Brownian path `b̃` of (N1). -/
theorem isSLEPathUpTo_retarget (hκ : 0 < κ) :
    Sec2.IsSLEPathUpTo κ (LP.retargetXL xL xR) (LP.retargetXR xR) (LP.retargetρL κ ρL ρR) (LP.retargetρR ρR)
      (newW xR w vR) (newVL xR w vL vR) (newVR xR w vR) (newB κ xL xR ρL ρR w vL vR)
      (newHorizon (LP.retargetPos xR) w (vR (LP.retargetIdx j m)) T) where
  w_zero := newW_zero hp hd
  vL_zero := newVL_zero hp hd hD
  vR_zero := newVR_zero hp hD
  continuousOn_w := continuousOn_newW hd
  continuousOn_vL := continuousOn_newVL hd
  continuousOn_vR := continuousOn_newVR hd
  antitone_vL := fun ht => antitone_newVL hp hd ht
  vL_le_w := fun ht => newVL_le_newW hp hd ht
  w_le_vR := fun ht => newW_le_newVR hp hd ht
  monotone_vR := fun ht => monotone_newVR hp hd ht
  integrable_gapL := fun ht => integrable_newGapL hd ht
  integrable_gapR := fun ht => integrable_newGapR hd ht
  w_eq := fun ht => newW_eq hp hd hD hκ ht
  vL_eq := fun ht => newVL_eq hp hd hD ht
  vR_eq := fun ht => newVR_eq hp hd hD ht
  volume_collisionL := volume_newCollisionL hd
  volume_collisionR := volume_newCollisionR hd
  not_threshold := fun ht => not_threshold_new hp hd ht

end Assembly

end Retarget

end Zhan

end InteractingSLE
