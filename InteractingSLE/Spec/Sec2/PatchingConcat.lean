/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec2.PatchingNonaccum
import InteractingSLE.Spec.Sec2.CriticalExtension

/-!
# Concatenation of local solutions at a time

Packet PROVE-SEC2-TERM2. Specification, proof of Theorem 2.2 (`source/spec/p001-048.md`
L490–L494): "When this happens, one can use this other force point in place of `V^{1,R}` … and
continue until a force point other than this new one is hit. Iterating this process …". The
pathwise content of one restart: if `(w, v)` is a local solution before `τ₁` and `σ < τ₁`, and
`(w', v')` is a local solution before `τ₂` of the same force word started from the state at `σ`
seen from the driver (`x' = v_σ − w_σ`), driven by the increments `b'_t = b_{σ+t} − b_σ`, then
the concatenation (`w` before `σ`, `w_σ + w'_{t−σ}` from `σ` on) is a local solution before
`σ + τ₂` (`IsSLEPathUpTo.concat`).

* `concatAt σ f c g`: `f t` for `t < σ`, `c + g (t − σ)` from `σ` on;
* `integral_concatAt_eq`, `intervalIntegrable_concatAt`: integrals over `[0, t]` split at `σ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec2

/-- The concatenation at time `σ` of `f` (before `σ`) with `g` started at `σ` from the value `c`. -/
def concatAt (σ : ℝ≥0) (f : ℝ≥0 → ℝ) (c : ℝ) (g : ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ :=
  if t < σ then f t else c + g (t - σ)

theorem concatAt_of_lt {σ t : ℝ≥0} {f g : ℝ≥0 → ℝ} {c : ℝ} (ht : t < σ) :
    concatAt σ f c g t = f t := by
  simp [concatAt, ht]

theorem concatAt_of_le {σ t : ℝ≥0} {f g : ℝ≥0 → ℝ} {c : ℝ} (ht : σ ≤ t) :
    concatAt σ f c g t = c + g (t - σ) := by
  simp [concatAt, not_lt.2 ht]

/-- With the compatibility `c + g 0 = f σ`, the concatenation is `f` up to and including `σ`. -/
theorem concatAt_of_le' {σ t : ℝ≥0} {f g : ℝ≥0 → ℝ} {c : ℝ} (hc : c + g 0 = f σ) (ht : t ≤ σ) :
    concatAt σ f c g t = f t := by
  rcases lt_or_eq_of_le ht with h | rfl
  · exact concatAt_of_lt h
  · rw [concatAt_of_le le_rfl, tsub_self, hc]

/-- `(σ + u).toNNReal − σ = u.toNNReal` for `u ≥ 0`. -/
theorem toNNReal_add_sub {σ : ℝ≥0} {u : ℝ} (hu : 0 ≤ u) :
    ((σ : ℝ) + u).toNNReal - σ = u.toNNReal := by
  rw [Real.toNNReal_add (NNReal.coe_nonneg σ) hu, Real.toNNReal_coe, add_tsub_cancel_left]

/-- Integrability over `[σ, t]` of a function of the concatenation from the shifted integrability
over `[0, t − σ]`. -/
theorem intervalIntegrable_shift {σ t : ℝ≥0} (hσt : σ ≤ t) {G : ℝ≥0 → ℝ}
    (hG : IntervalIntegrable (fun s : ℝ => G s.toNNReal) volume 0 ((t - σ : ℝ≥0) : ℝ)) :
    IntervalIntegrable (fun s : ℝ => G (s.toNNReal - σ)) volume σ t := by
  have h1 := hG.comp_add_left (-(σ : ℝ))
  have e1 : (0 : ℝ) - -(σ : ℝ) = σ := by ring
  have e2 : ((t - σ : ℝ≥0) : ℝ) - -(σ : ℝ) = t := by
    rw [NNReal.coe_sub hσt]; ring
  rw [e1, e2] at h1
  refine h1.congr ?_
  rw [uIoc_of_le (show (σ : ℝ) ≤ t from hσt)]
  intro s hs
  have hs0 : 0 ≤ -(σ : ℝ) + s := by linarith [hs.1]
  show G (-(σ : ℝ) + s).toNNReal = G (s.toNNReal - σ)
  congr 1
  rw [← toNNReal_add_sub (σ := σ) hs0]
  congr 2
  ring

/-- The integral over `[σ, t]` of a function of the shifted time is the integral over
`[0, t − σ]`. -/
theorem integral_shift {σ t : ℝ≥0} (hσt : σ ≤ t) (G : ℝ≥0 → ℝ) :
    ∫ s in (σ : ℝ)..t, G (s.toNNReal - σ) =
      ∫ s in (0 : ℝ)..((t - σ : ℝ≥0) : ℝ), G s.toNNReal := by
  have h := intervalIntegral.integral_comp_add_left (fun s : ℝ => G (s.toNNReal - σ)) (σ : ℝ)
    (a := 0) (b := ((t - σ : ℝ≥0) : ℝ))
  rw [add_zero, NNReal.coe_sub hσt, add_sub_cancel] at h
  rw [← h, NNReal.coe_sub hσt]
  refine intervalIntegral.integral_congr fun u hu => ?_
  rw [uIcc_of_le (sub_nonneg.2 (show (σ : ℝ) ≤ t from hσt))] at hu
  rw [toNNReal_add_sub hu.1]

/-- **Integrals of a concatenation split at `σ`**: if `H = G₁` up to `σ` and `H = G₂ (· − σ)`
from `σ` on, then `H` is integrable on `[0, t]` and `∫₀ᵗ H = ∫₀^σ G₁ + ∫₀^{t−σ} G₂`. -/
theorem integral_concat_split {σ t : ℝ≥0} (hσt : σ ≤ t) {H G₁ G₂ : ℝ≥0 → ℝ}
    (h1 : ∀ s : ℝ≥0, s ≤ σ → H s = G₁ s) (h2 : ∀ s : ℝ≥0, σ ≤ s → H s = G₂ (s - σ))
    (hi1 : IntervalIntegrable (fun s : ℝ => G₁ s.toNNReal) volume 0 σ)
    (hi2 : IntervalIntegrable (fun s : ℝ => G₂ s.toNNReal) volume 0 ((t - σ : ℝ≥0) : ℝ)) :
    IntervalIntegrable (fun s : ℝ => H s.toNNReal) volume 0 t ∧
      ∫ s in (0 : ℝ)..t, H s.toNNReal = (∫ s in (0 : ℝ)..σ, G₁ s.toNNReal) +
        ∫ s in (0 : ℝ)..((t - σ : ℝ≥0) : ℝ), G₂ s.toNNReal := by
  have hσ0 : (0 : ℝ) ≤ σ := NNReal.coe_nonneg σ
  have hσt' : (σ : ℝ) ≤ t := hσt
  have e1 : EqOn (fun s : ℝ => G₁ s.toNNReal) (fun s : ℝ => H s.toNNReal) (uIcc 0 (σ : ℝ)) :=
    fun s hs => by
      rw [uIcc_of_le hσ0] at hs
      exact (h1 _ (Real.toNNReal_le_iff_le_coe.2 hs.2)).symm
  have e2 : EqOn (fun s : ℝ => G₂ (s.toNNReal - σ)) (fun s : ℝ => H s.toNNReal)
      (uIcc (σ : ℝ) t) := fun s hs => by
    rw [uIcc_of_le hσt'] at hs
    have hs0 : 0 ≤ s := hσ0.trans hs.1
    exact (h2 _ ((Real.le_toNNReal_iff_coe_le hs0).2 hs.1)).symm
  have hA : IntervalIntegrable (fun s : ℝ => H s.toNNReal) volume 0 σ :=
    hi1.congr (e1.mono Ioc_subset_Icc_self)
  have hB : IntervalIntegrable (fun s : ℝ => H s.toNNReal) volume σ t :=
    (intervalIntegrable_shift hσt hi2).congr (e2.mono Ioc_subset_Icc_self)
  refine ⟨hA.trans hB, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals hA hB,
    ← intervalIntegral.integral_congr e1, ← intervalIntegral.integral_congr e2,
    integral_shift hσt]

/-- `↑(t − σ) < τ₂` for `σ ≤ t` and `↑t < ↑σ + τ₂`. -/
theorem coe_sub_lt_of_lt_add {σ t : ℝ≥0} {τ₂ : ℝ≥0∞} (hσt : σ ≤ t)
    (ht : (t : ℝ≥0∞) < (σ : ℝ≥0∞) + τ₂) : ((t - σ : ℝ≥0) : ℝ≥0∞) < τ₂ := by
  rw [ENNReal.coe_sub]
  exact ENNReal.sub_lt_of_lt_add (by exact_mod_cast hσt) (by rwa [add_comm] at ht)

/-- **Continuity of a concatenation** on `[0, σ + τ₂)`: `f` continuous before `τ₁ > σ`, `g`
continuous before `τ₂`, and `c + g 0 = f σ`. -/
theorem continuousOn_concatAt {σ : ℝ≥0} {τ₁ τ₂ : ℝ≥0∞} (hσ : (σ : ℝ≥0∞) < τ₁)
    {f g : ℝ≥0 → ℝ} {c : ℝ} (hf : ContinuousOn f {t | (t : ℝ≥0∞) < τ₁})
    (hg : ContinuousOn g {t | (t : ℝ≥0∞) < τ₂}) (hc : c + g 0 = f σ) :
    ContinuousOn (concatAt σ f c g) {t | (t : ℝ≥0∞) < (σ : ℝ≥0∞) + τ₂} := by
  have hfσ : ContinuousAt f σ := hf.continuousAt ((isOpen_setOf_coe_lt τ₁).mem_nhds hσ)
  -- the second piece is continuous at every `t ≥ σ` of the domain
  have hg' : ∀ t : ℝ≥0, σ ≤ t → (t : ℝ≥0∞) < (σ : ℝ≥0∞) + τ₂ →
      ContinuousAt (fun s : ℝ≥0 => c + g (s - σ)) t := fun t hσt ht => by
    have hgt : ContinuousAt g (t - σ) :=
      hg.continuousAt ((isOpen_setOf_coe_lt τ₂).mem_nhds (coe_sub_lt_of_lt_add hσt ht))
    have hsub : Continuous fun s : ℝ≥0 => s - σ := by fun_prop
    exact continuousAt_const.add (ContinuousAt.comp (g := g) (f := fun s : ℝ≥0 => s - σ)
      (x := t) hgt hsub.continuousAt)
  refine (isOpen_setOf_coe_lt _).continuousOn_iff.2 fun t ht => ?_
  rcases lt_trichotomy t σ with htσ | rfl | htσ
  · have hft : ContinuousAt f t :=
      hf.continuousAt ((isOpen_setOf_coe_lt τ₁).mem_nhds (lt_trans (by exact_mod_cast htσ) hσ))
    refine hft.congr ?_
    filter_upwards [Iio_mem_nhds htσ] with s hs using (concatAt_of_lt hs).symm
  · rw [continuousAt_iff_continuous_left_right]
    constructor
    · refine (hfσ.continuousWithinAt).congr (fun s hs => concatAt_of_le' hc hs)
        (concatAt_of_le' hc le_rfl)
    · refine ((hg' t le_rfl ht).continuousWithinAt).congr (fun s hs => concatAt_of_le hs)
        (concatAt_of_le le_rfl)
  · refine (hg' t htσ.le ht).congr ?_
    filter_upwards [Ioi_mem_nhds htσ] with s hs using (concatAt_of_le hs.le).symm

theorem eqOn_toNNReal_of_lt {σ t : ℝ≥0} (ht : t < σ) {H F : ℝ≥0 → ℝ}
    (hH : ∀ s : ℝ≥0, s < σ → H s = F s) :
    EqOn (fun s : ℝ => H s.toNNReal) (fun s : ℝ => F s.toNNReal) (uIcc 0 (t : ℝ)) := fun s hs => by
  rw [uIcc_of_le (NNReal.coe_nonneg t)] at hs
  exact hH _ ((Real.toNNReal_le_iff_le_coe.2 hs.2).trans_lt ht)

namespace IsSLEPathUpTo

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ}
  {b : ℝ≥0 → ℝ} {τ₁ τ₂ : ℝ≥0∞} {σ : ℝ≥0} {w' : ℝ≥0 → ℝ} {vL' : Fin nL → ℝ≥0 → ℝ}
  {vR' : Fin nR → ℝ≥0 → ℝ} {b' : ℝ≥0 → ℝ}

theorem intervalIntegrable_div_gap {τ : ℝ≥0∞} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ}
    (h : IsSLEPathUpTo a xL xR ρL ρR w vL vR b τ) {t : ℝ≥0} (ht : (t : ℝ≥0∞) < τ) :
    (∀ i (c : ℝ), IntervalIntegrable (fun s : ℝ => c / (w s.toNNReal - vL i s.toNNReal))
      volume 0 t) ∧
    ∀ j (c : ℝ), IntervalIntegrable (fun s : ℝ => c / (w s.toNNReal - vR j s.toNNReal))
      volume 0 t :=
  ⟨fun i c => by simpa only [div_eq_mul_inv] using (h.integrable_gapL ht i).const_mul c,
    fun j c => by simpa only [div_eq_mul_inv] using (h.integrable_gapR ht j).const_mul c⟩

/-- **Concatenation of local solutions** (Specification p. 22, the restart at a collision time):
a local solution before `τ₁`, followed at a time `σ < τ₁` by a local solution before `τ₂` of the same
force word started from the state at `σ` seen from the driver and driven by `b_{σ+·} − b_σ`, is a
local solution before `σ + τ₂`. -/
theorem concat (h₁ : IsSLEPathUpTo a xL xR ρL ρR w vL vR b τ₁) (hσ : (σ : ℝ≥0∞) < τ₁)
    (h₂ : IsSLEPathUpTo a (fun i => vL i σ - w σ) (fun j => vR j σ - w σ) ρL ρR w' vL' vR' b' τ₂)
    (hb' : ∀ t, b' t = b (σ + t) - b σ) :
    IsSLEPathUpTo a xL xR ρL ρR (concatAt σ w (w σ) w')
      (fun i => concatAt σ (vL i) (w σ) (vL' i)) (fun j => concatAt σ (vR j) (w σ) (vR' j)) b
      ((σ : ℝ≥0∞) + τ₂) := by
  have cw : w σ + w' 0 = w σ := by rw [h₂.w_zero, add_zero]
  have cL : ∀ i, w σ + vL' i 0 = vL i σ := fun i => by rw [h₂.vL_zero i]; ring
  have cR : ∀ j, w σ + vR' j 0 = vR j σ := fun j => by rw [h₂.vR_zero j]; ring
  have hlt1 : ∀ {t : ℝ≥0}, t < σ → (t : ℝ≥0∞) < τ₁ := fun ht =>
    lt_trans (by exact_mod_cast ht) hσ
  have hlt2 : ∀ {t : ℝ≥0}, σ ≤ t → (t : ℝ≥0∞) < (σ : ℝ≥0∞) + τ₂ →
      ((t - σ : ℝ≥0) : ℝ≥0∞) < τ₂ := fun hσt ht => coe_sub_lt_of_lt_add hσt ht
  -- integrals of translation-invariant functions of `(w, v)`, split at `σ`
  have hsplit : ∀ (F : ℝ → ℝ → ℝ), (∀ c x y, F (c + x) (c + y) = F x y) →
      ∀ (v v' : ℝ≥0 → ℝ), w σ + v' 0 = v σ → ∀ {t : ℝ≥0}, σ ≤ t →
      IntervalIntegrable (fun s : ℝ => F (w s.toNNReal) (v s.toNNReal)) volume 0 σ →
      IntervalIntegrable (fun s : ℝ => F (w' s.toNNReal) (v' s.toNNReal)) volume 0
        ((t - σ : ℝ≥0) : ℝ) →
      IntervalIntegrable (fun s : ℝ => F (concatAt σ w (w σ) w' s.toNNReal)
        (concatAt σ v (w σ) v' s.toNNReal)) volume 0 t ∧
      ∫ s in (0 : ℝ)..t, F (concatAt σ w (w σ) w' s.toNNReal) (concatAt σ v (w σ) v' s.toNNReal) =
        (∫ s in (0 : ℝ)..σ, F (w s.toNNReal) (v s.toNNReal)) +
          ∫ s in (0 : ℝ)..((t - σ : ℝ≥0) : ℝ), F (w' s.toNNReal) (v' s.toNNReal) :=
    fun F hF v v' cv t hσt hi1 hi2 => integral_concat_split hσt
      (H := fun s => F (concatAt σ w (w σ) w' s) (concatAt σ v (w σ) v' s))
      (G₁ := fun s => F (w s) (v s)) (G₂ := fun s => F (w' s) (v' s))
      (fun s hs => by simp only [concatAt_of_le' cw hs, concatAt_of_le' cv hs])
      (fun s hs => by simp only [concatAt_of_le hs, hF]) hi1 hi2
  have hbefore : ∀ (F : ℝ → ℝ → ℝ) (v v' : ℝ≥0 → ℝ) {t : ℝ≥0}, t < σ →
      EqOn (fun s : ℝ => F (concatAt σ w (w σ) w' s.toNNReal) (concatAt σ v (w σ) v' s.toNNReal))
        (fun s : ℝ => F (w s.toNNReal) (v s.toNNReal)) (uIcc 0 (t : ℝ)) :=
    fun F v v' t ht => eqOn_toNNReal_of_lt ht
      (H := fun s => F (concatAt σ w (w σ) w' s) (concatAt σ v (w σ) v' s))
      (F := fun s => F (w s) (v s)) fun s hs => by simp only [concatAt_of_lt hs]
  have hinvF : ∀ c x y : ℝ, ((c + x) - (c + y))⁻¹ = (x - y)⁻¹ := fun c x y => by
    rw [add_sub_add_left_eq_sub]
  have hdivF : ∀ ρ c x y : ℝ, ρ / ((c + x) - (c + y)) = ρ / (x - y) := fun ρ c x y => by
    rw [add_sub_add_left_eq_sub]
  have hforceF : ∀ c x y : ℝ, 2 / ((c + y) - (c + x)) = 2 / (y - x) := fun c x y => by
    rw [add_sub_add_left_eq_sub]
  refine
    { w_zero := ?_, vL_zero := ?_, vR_zero := ?_, continuousOn_w := ?_, continuousOn_vL := ?_,
      continuousOn_vR := ?_, antitone_vL := ?_, vL_le_w := ?_, w_le_vR := ?_, monotone_vR := ?_,
      integrable_gapL := ?_, integrable_gapR := ?_, w_eq := ?_, vL_eq := ?_, vR_eq := ?_,
      volume_collisionL := ?_, volume_collisionR := ?_, not_threshold := ?_ }
  · rw [concatAt_of_le' cw (zero_le : (0 : ℝ≥0) ≤ σ)]; exact h₁.w_zero
  · intro i; rw [concatAt_of_le' (cL i) (zero_le : (0 : ℝ≥0) ≤ σ)]; exact h₁.vL_zero i
  · intro j; rw [concatAt_of_le' (cR j) (zero_le : (0 : ℝ≥0) ≤ σ)]; exact h₁.vR_zero j
  · exact continuousOn_concatAt hσ h₁.continuousOn_w h₂.continuousOn_w cw
  · exact fun i => continuousOn_concatAt hσ (h₁.continuousOn_vL i) (h₂.continuousOn_vL i) (cL i)
  · exact fun j => continuousOn_concatAt hσ (h₁.continuousOn_vR j) (h₂.continuousOn_vR j) (cR j)
  · intro t ht
    rcases lt_or_ge t σ with h | h
    · simp only [concatAt_of_lt h]; exact h₁.antitone_vL (hlt1 h)
    · simp only [concatAt_of_le h]
      exact fun i j hij => (add_le_add_iff_left (w σ)).2 (h₂.antitone_vL (hlt2 h ht) hij)
  · intro t ht i
    rcases lt_or_ge t σ with h | h
    · simp only [concatAt_of_lt h]; exact h₁.vL_le_w (hlt1 h) i
    · simp only [concatAt_of_le h]; exact (add_le_add_iff_left (w σ)).2 (h₂.vL_le_w (hlt2 h ht) i)
  · intro t ht j
    rcases lt_or_ge t σ with h | h
    · simp only [concatAt_of_lt h]; exact h₁.w_le_vR (hlt1 h) j
    · simp only [concatAt_of_le h]; exact (add_le_add_iff_left (w σ)).2 (h₂.w_le_vR (hlt2 h ht) j)
  · intro t ht
    rcases lt_or_ge t σ with h | h
    · simp only [concatAt_of_lt h]; exact h₁.monotone_vR (hlt1 h)
    · simp only [concatAt_of_le h]
      exact fun i j hij => (add_le_add_iff_left (w σ)).2 (h₂.monotone_vR (hlt2 h ht) hij)
  · intro t ht i
    rcases lt_or_ge t σ with h | h
    · exact (h₁.integrable_gapL (hlt1 h) i).congr
        ((hbefore (fun x y => (x - y)⁻¹) (vL i) (vL' i) h).symm.mono uIoc_subset_uIcc)
    · exact (hsplit (fun x y => (x - y)⁻¹) hinvF (vL i) (vL' i) (cL i) h
        (h₁.integrable_gapL hσ i) (h₂.integrable_gapL (hlt2 h ht) i)).1
  · intro t ht j
    rcases lt_or_ge t σ with h | h
    · exact (h₁.integrable_gapR (hlt1 h) j).congr
        ((hbefore (fun x y => (x - y)⁻¹) (vR j) (vR' j) h).symm.mono uIoc_subset_uIcc)
    · exact (hsplit (fun x y => (x - y)⁻¹) hinvF (vR j) (vR' j) (cR j) h
        (h₁.integrable_gapR hσ j) (h₂.integrable_gapR (hlt2 h ht) j)).1
  · intro t ht
    rcases lt_or_ge t σ with h | h
    · rw [concatAt_of_lt h, h₁.w_eq (hlt1 h)]
      rw [Finset.sum_congr rfl fun i _ => intervalIntegral.integral_congr
          (hbefore (fun x y => ρL i / (x - y)) (vL i) (vL' i) h),
        Finset.sum_congr rfl fun j _ => intervalIntegral.integral_congr
          (hbefore (fun x y => ρR j / (x - y)) (vR j) (vR' j) h)]
    · have eL : ∀ i, ∫ s in (0 : ℝ)..t, ρL i / (concatAt σ w (w σ) w' s.toNNReal -
          concatAt σ (vL i) (w σ) (vL' i) s.toNNReal) =
          (∫ s in (0 : ℝ)..σ, ρL i / (w s.toNNReal - vL i s.toNNReal)) +
            ∫ s in (0 : ℝ)..((t - σ : ℝ≥0) : ℝ), ρL i / (w' s.toNNReal - vL' i s.toNNReal) :=
        fun i => (hsplit (fun x y => ρL i / (x - y)) (hdivF (ρL i)) (vL i) (vL' i) (cL i) h
          ((intervalIntegrable_div_gap h₁ hσ).1 i (ρL i))
          ((intervalIntegrable_div_gap h₂ (hlt2 h ht)).1 i (ρL i))).2
      have eR : ∀ j, ∫ s in (0 : ℝ)..t, ρR j / (concatAt σ w (w σ) w' s.toNNReal -
          concatAt σ (vR j) (w σ) (vR' j) s.toNNReal) =
          (∫ s in (0 : ℝ)..σ, ρR j / (w s.toNNReal - vR j s.toNNReal)) +
            ∫ s in (0 : ℝ)..((t - σ : ℝ≥0) : ℝ), ρR j / (w' s.toNNReal - vR' j s.toNNReal) :=
        fun j => (hsplit (fun x y => ρR j / (x - y)) (hdivF (ρR j)) (vR j) (vR' j) (cR j) h
          ((intervalIntegrable_div_gap h₁ hσ).2 j (ρR j))
          ((intervalIntegrable_div_gap h₂ (hlt2 h ht)).2 j (ρR j))).2
      rw [concatAt_of_le h, Finset.sum_congr rfl fun i _ => eL i,
        Finset.sum_congr rfl fun j _ => eR j, Finset.sum_add_distrib, Finset.sum_add_distrib,
        h₂.w_eq (hlt2 h ht), hb', add_tsub_cancel_of_le h]
      nth_rewrite 1 [h₁.w_eq hσ]
      ring
  · intro t ht i
    rcases lt_or_ge t σ with h | h
    · rw [concatAt_of_lt h, h₁.vL_eq (hlt1 h) i, intervalIntegral.integral_congr
        (hbefore (fun x y => 2 / (y - x)) (vL i) (vL' i) h)]
    · have e := (hsplit (fun x y => 2 / (y - x)) hforceF (vL i) (vL' i) (cL i) h
        (h₁.intervalIntegrable_forceL hσ i) (h₂.intervalIntegrable_forceL (hlt2 h ht) i)).2
      beta_reduce at e
      rw [concatAt_of_le h, e, h₂.vL_eq (hlt2 h ht) i, h₁.vL_eq hσ i]
      ring
  · intro t ht j
    rcases lt_or_ge t σ with h | h
    · rw [concatAt_of_lt h, h₁.vR_eq (hlt1 h) j, intervalIntegral.integral_congr
        (hbefore (fun x y => 2 / (y - x)) (vR j) (vR' j) h)]
    · have e := (hsplit (fun x y => 2 / (y - x)) hforceF (vR j) (vR' j) (cR j) h
        (h₁.intervalIntegrable_forceR hσ j) (h₂.intervalIntegrable_forceR (hlt2 h ht) j)).2
      beta_reduce at e
      rw [concatAt_of_le h, e, h₂.vR_eq (hlt2 h ht) j, h₁.vR_eq hσ j]
      ring
  · intro i
    refine measure_mono_null (fun s hs => ?_) (measure_union_null (h₁.volume_collisionL i)
      ((measure_preimage_add_right volume (-(σ : ℝ)) _).trans (h₂.volume_collisionL i)))
    obtain ⟨hs0, hsτ, he⟩ := hs
    rcases lt_or_ge s.toNNReal σ with h | h
    · rw [concatAt_of_lt h, concatAt_of_lt h] at he
      exact Or.inl ⟨hs0, hlt1 h, he⟩
    · rw [concatAt_of_le h, concatAt_of_le h, add_right_inj] at he
      have hσs : (σ : ℝ) ≤ s := (Real.le_toNNReal_iff_coe_le hs0).1 h
      have hu : 0 ≤ s + -(σ : ℝ) := by linarith
      have e : (s + -(σ : ℝ)).toNNReal = s.toNNReal - σ := by
        have := toNNReal_add_sub (σ := σ) hu
        rw [show (σ : ℝ) + (s + -(σ : ℝ)) = s by ring] at this
        exact this.symm
      refine Or.inr ⟨hu, ?_, ?_⟩
      · rw [e]; exact hlt2 h hsτ
      · rw [e]; exact he
  · intro j
    refine measure_mono_null (fun s hs => ?_) (measure_union_null (h₁.volume_collisionR j)
      ((measure_preimage_add_right volume (-(σ : ℝ)) _).trans (h₂.volume_collisionR j)))
    obtain ⟨hs0, hsτ, he⟩ := hs
    rcases lt_or_ge s.toNNReal σ with h | h
    · rw [concatAt_of_lt h, concatAt_of_lt h] at he
      exact Or.inl ⟨hs0, hlt1 h, he⟩
    · rw [concatAt_of_le h, concatAt_of_le h, add_right_inj] at he
      have hσs : (σ : ℝ) ≤ s := (Real.le_toNNReal_iff_coe_le hs0).1 h
      have hu : 0 ≤ s + -(σ : ℝ) := by linarith
      have e : (s + -(σ : ℝ)).toNNReal = s.toNNReal - σ := by
        have := toNNReal_add_sub (σ := σ) hu
        rw [show (σ : ℝ) + (s + -(σ : ℝ)) = s by ring] at this
        exact this.symm
      refine Or.inr ⟨hu, ?_, ?_⟩
      · rw [e]; exact hlt2 h hsτ
      · rw [e]; exact he
  · intro t ht
    rcases lt_or_ge t σ with h | h
    · simp only [concatAt_of_lt h]; exact h₁.not_threshold (hlt1 h)
    · simp only [concatAt_of_le h]
      have := h₂.not_threshold (hlt2 h ht)
      simpa only [ForceWord.ThresholdCondition, add_right_inj] using this

end IsSLEPathUpTo

end Sec2

end InteractingSLE
