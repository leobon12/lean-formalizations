/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.ContinuityProb9Prefix
import InteractingSLE.Spec.Supplement.LP1Seed
import InteractingSLE.Spec.Sec4.ZeroMarks
import InteractingSLE.Spec.Sec7.Aux99StoppedStrip

/-!
# The target change for a single mark (`j = 0`): low weights of one right mark

Packet PROVE-SEC7-C10, scope addition (PROVE-ZHAN-A8, "What remains" 1: the `hlow` of
`aux99StoppedStatement_of_seed_of_low`). Wang–Wu's Lemma 5.1 proof targets the single mark `x > 0` by
`ψ(z) = z/(x − z)`; the retargeted word is the end-mark word, one left mark at `−1` of weight `κ − 6 − ρ`.

The landed process-level target change (`Zhan.Retarget.RetargetEvolutionStatement`, PROVE-SEC7-C9) has `1 ≤ j`
threaded through all its files. Instead of a `j = 0` copy, the single mark is reduced to `j = 1`:

* add a **passive mark at `0⁺` of weight `0`** before `x` (`augX`, `augρ`): the augmented word `(0, x)` is distinct
  and ordered, LP9's retargeting of its second mark applies, and its transformed word is the end-mark word with an
  added right mark at `ψ(0) = 0` of weight `0`, complete as soon as the end-mark word is (zero-weight deletion,
  `IsIntegratedSLEEvolution.compEmb`) and with a separated start (`retarget_sep_of_left_empty`);
* for `ρ ≤ −2` the first meeting of the driver with `x` is a continuation threshold of the augmented word (the
  colliding group `{0⁺, x}` has weight `ρ`), so the separation time is the lifetime (`sepTime_aug_eq`) and R5 + R6
  (`ae_newW_trace`, `exists_trace_of_path`) give a transient generating trace through the lifetime — no closing
  input is needed;
* deleting the passive mark gives an evolution of the one-mark word with that trace, and one such evolution suffices
  (`LP.isCompleteForceWord_of_ae_traceEvent`, uniqueness of the coded trace law at a separated start).

**Main result** `isCompleteForceWord_oneRight_low`: for `ρ ≤ −2`, completeness of the end-mark word of weight
`κ − 6 − ρ` implies completeness of the one-mark word. With `ρ ≤ κ/2 − 4` the end-mark weight is `≥ κ/2 − 2`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Sec7

open Zhan.Retarget

/-! ### R6 along one path without the closing -/

section Path

variable {κ : ℝ} {nL j m : ℕ} {xL : Fin nL → ℝ} {xR : Fin (j + 1 + m) → ℝ} {ρL : Fin nL → ℝ}
  {ρR : Fin (j + 1 + m) → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin (j + 1 + m) → ℝ≥0 → ℝ}
  {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- **The pulled-back trace up to the separation time** (R6 along one path; `prefix_of_path` without its count and
closing clauses). -/
theorem exists_trace_of_path (hD : LP.IsDistinctForceWord xL xR) (hj : 1 ≤ j)
    (hp : IsIntegratedSLEPath κ xL xR ρL ρR w vL vR b ζ)
    (hlim : ∀ T : ℝ≥0, 0 < T → (T : ℝ≥0∞) = ζ → ∃ (w₀ : ℝ) (vL₀ : Fin nL → ℝ) (vR₀ : Fin (j + 1 + m) → ℝ),
      Tendsto (fun t => (w t, fun i => vL i t, fun i => vR i t)) (𝓝[<] T) (𝓝 (w₀, vL₀, vR₀)) ∧
        ForceWord.ThresholdCondition ρL ρR w₀ vL₀ vR₀)
    (htr : ∃ η' : ℝ≥0 → ℂ, IsGeneratingTrace (newW xR w vR)
        (newHorizon (LP.retargetPos xR) w (vR (LP.retargetIdx j m)) (sepTime w (vR (LP.retargetIdx j m)) ζ)) η' ∧
      (newHorizon (LP.retargetPos xR) w (vR (LP.retargetIdx j m)) (sepTime w (vR (LP.retargetIdx j m)) ζ) = ⊤ →
        Tendsto (fun t => ‖η' t‖) atTop atTop)) :
    ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace w (sepTime w (vR (LP.retargetIdx j m)) ζ) η ∧
      (sepTime w (vR (LP.retargetIdx j m)) ζ = ⊤ → Tendsto (fun t => ‖η t‖) atTop atTop) := by
  set τ := sepTime w (vR (LP.retargetIdx j m)) ζ with hτdef
  have hτζ : τ ≤ ζ := sepTime_le w _ ζ
  have hrd := retargetData_of_isSLEPathUpTo (hp.isSLEPathUpTo hτζ) hD hj fun t ht => lt_of_lt_sepTime ht
  have hdd : PullData w (vR (LP.retargetIdx j m)) (LP.retargetPos xR) τ :=
    ⟨hrd.pos, hp.1, hrd.sep, hrd.target⟩
  obtain ⟨η', hη', htr'⟩ := htr
  exact hdd.exists_trace hη' htr' fun hτ =>
    exists_bound_before hp.isForcePath.continuousOn_w hτζ hτ fun T hT hTζ => by
      obtain ⟨w₀, vL₀, vR₀, hl, -⟩ := hlim T hT hTζ
      exact ⟨w₀, (continuous_fst.tendsto _).comp hl⟩

end Path

/-! ### The augmented word -/

/-- The augmented right list `(0, x)`: a passive mark at `0⁺` before the mark `x`. -/
def augX (x : ℝ) : Fin (1 + 1 + 0) → ℝ := fun i => if (i : ℕ) = 0 then 0 else x

/-- The augmented right weights `(0, ρ)`. -/
def augρ (ρ : ℝ) : Fin (1 + 1 + 0) → ℝ := fun i => if (i : ℕ) = 0 then 0 else ρ

theorem isDistinctForceWord_aug {xL : Fin 0 → ℝ} {x : ℝ} (hx : 0 < x) : LP.IsDistinctForceWord xL (augX x) := by
  have hmono : StrictMono (augX x) := by
    intro i i' h
    have h1 : (i : ℕ) < i' := h
    have h2 : (i' : ℕ) < 1 + 1 + 0 := i'.isLt
    have hi : (i : ℕ) = 0 := by omega
    have hi' : (i' : ℕ) ≠ 0 := by omega
    simp only [augX, hi, hi', ↓reduceIte]
    exact hx
  refine ⟨⟨fun i => i.elim0, fun i => i.elim0, hmono.monotone, fun i => ?_⟩, fun i => i.elim0, hmono⟩
  simp only [augX]
  split_ifs
  · exact le_rfl
  · exact hx.le

/-- **For `ρ ≤ −2` the separation time of the augmented word is its lifetime**: at a first meeting before the
lifetime the group `{0⁺, x}` collides with the driver with total weight `ρ`, a continuation threshold. -/
theorem sepTime_aug_eq {κ : ℝ} {xL ρL : Fin 0 → ℝ} {x ρ : ℝ} {w : ℝ≥0 → ℝ} {vL : Fin 0 → ℝ≥0 → ℝ}
    {vR : Fin (1 + 1 + 0) → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    (hp : IsIntegratedSLEPath κ xL (augX x) ρL (augρ ρ) w vL vR b ζ) (hρ : ρ ≤ -2) :
    sepTime w (vR (LP.retargetIdx 1 0)) ζ = ζ := by
  refine le_antisymm (sepTime_le w _ ζ) (not_lt.1 fun hlt => ?_)
  have hc : ContinuousOn (fun t => vR (LP.retargetIdx 1 0) t - w t) {t | (t : ℝ≥0∞) < ζ} :=
    (hp.isForcePath.continuousOn_vR _).sub hp.isForcePath.continuousOn_w
  rw [sepTime_eq_firstMeet] at hlt
  obtain ⟨t₀, -, ht₀ζ, hle⟩ := exists_eq_firstMeet (W := fun t (_ : Unit) => w t)
    (V := fun t _ => vR (LP.retargetIdx 1 0) t) (ζ := fun _ => ζ) (ω := ()) hc hlt
  have hk : vR (LP.retargetIdx 1 0) t₀ = w t₀ := le_antisymm hle (hp.isForcePath.w_le_vR ht₀ζ _)
  have hall : ∀ i, vR i t₀ = w t₀ := by
    intro i
    have hik : i ≤ LP.retargetIdx 1 0 := by
      rw [Fin.le_def]; simp only [LP.retargetIdx, Fin.val_castAdd, Fin.val_last]; have := i.isLt; omega
    exact le_antisymm ((hp.isForcePath.monotone_vR ht₀ζ hik).trans hk.le) (hp.isForcePath.w_le_vR ht₀ζ i)
  have hthr : ForceWord.ThresholdCondition ρL (augρ ρ) (w t₀) (fun i => vL i t₀) (fun i => vR i t₀) := by
    right
    rw [Finset.filter_true_of_mem fun i _ => hall i, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_zero]
    simp [augρ, hρ]
  exact (hp.isSLEPathUpTo le_rfl).not_threshold ht₀ζ hthr

/-- The transformed word of the augmented word is complete when the end-mark word is (delete the zero-weight right
mark at `ψ(0) = 0`). -/
theorem isCompleteForceWord_retarget_aug {κ : ℝ} {xL ρL : Fin 0 → ℝ} {x ρ : ℝ}
    (hEM : LP.IsCompleteForceWord.{u} κ (fun _ : Fin 1 => (-1 : ℝ)) (fun i : Fin 0 => i.elim0)
      (fun _ : Fin 1 => κ - 6 - ρ) (fun i : Fin 0 => i.elim0)) :
    LP.IsCompleteForceWord.{u} κ (LP.retargetXL xL (augX x)) (LP.retargetXR (augX x))
      (LP.retargetρL κ ρL (augρ ρ)) (LP.retargetρR (augρ ρ)) := by
  intro Ω mΩ P _ 𝓕 W VL VR B ζ hE
  have h := hE.compEmb (RelEmbedding.refl (· ≤ ·)) (OrderEmbedding.ofIsEmpty : Fin 0 ↪o Fin 1)
    (fun i hi => absurd ⟨i, rfl⟩ hi) fun i _ => by
      have hi : ((Fin.castAdd 0 i.castSucc : Fin (1 + 1 + 0)) : ℕ) = 0 := by
        simp only [Fin.val_castAdd, Fin.val_castSucc]; omega
      simp only [LP.retargetρR, augρ, hi, ↓reduceIte]
  have e1 : (fun j => LP.retargetXL xL (augX x) ((RelEmbedding.refl (· ≤ ·) : Fin (0 + (0 + 1)) ↪o _) j)) =
      fun _ : Fin 1 => (-1 : ℝ) := by
    funext j
    have hj : j = Fin.natAdd 0 (0 : Fin (0 + 1)) :=
      Fin.ext (by simp only [Fin.val_natAdd, Fin.val_zero]; have := j.isLt; omega)
    rw [hj, RelEmbedding.refl_apply, LP.retargetXL, Fin.append_right, Fin.cons_zero]
  have e2 : (fun j => LP.retargetρL κ ρL (augρ ρ) ((RelEmbedding.refl (· ≤ ·) : Fin (0 + (0 + 1)) ↪o _) j)) =
      fun _ : Fin 1 => κ - 6 - ρ := by
    funext j
    have hj : j = Fin.natAdd 0 (0 : Fin (0 + 1)) :=
      Fin.ext (by simp only [Fin.val_natAdd, Fin.val_zero]; have := j.isLt; omega)
    rw [hj, RelEmbedding.refl_apply, LP.retargetρL, Fin.append_right, Fin.cons_zero]
    simp [Fin.sum_univ_succ, augρ]
  have e3 : (fun j : Fin 0 => LP.retargetXR (augX x) ((OrderEmbedding.ofIsEmpty : Fin 0 ↪o Fin 1) j)) =
      fun i : Fin 0 => i.elim0 := funext fun i => i.elim0
  have e4 : (fun j : Fin 0 => LP.retargetρR (augρ ρ) ((OrderEmbedding.ofIsEmpty : Fin 0 ↪o Fin 1) j)) =
      fun i : Fin 0 => i.elim0 := funext fun i => i.elim0
  rw [e1, e2, e3, e4] at h
  exact hEM P 𝓕 W _ _ B ζ h

/-- The order embedding of the mark `x` into the augmented list. -/
def augEmb : Fin 1 ↪o Fin (1 + 1 + 0) :=
  OrderEmbedding.ofStrictMono (fun _ => ⟨1, by omega⟩) fun a b h => absurd h (by
    have : a = b := Subsingleton.elim _ _
    rw [this]; exact lt_irrefl _)

/-- **Low weights of one right mark from the end-mark word** (PROVE-ZHAN-A8's `hlow` route; Wang–Wu Lemma 5.1's
target change at `x`). For `κ > 0`, one right mark at `x > 0` with weight `ρ ≤ −2`: if the end-mark word (one left mark
at `−1` of weight `κ − 6 − ρ`) is complete, so is the one-mark word. -/
theorem isCompleteForceWord_oneRight_low {κ : ℝ} (hκ : 0 < κ) {xL ρL : Fin 0 → ℝ} {xR ρR : Fin 1 → ℝ}
    (hx : 0 < xR 0) (hρ : ρR 0 ≤ -2)
    (hEM : LP.IsCompleteForceWord.{u} κ (fun _ : Fin 1 => (-1 : ℝ)) (fun i : Fin 0 => i.elim0)
      (fun _ : Fin 1 => κ - 6 - ρR 0) (fun i : Fin 0 => i.elim0)) :
    LP.IsCompleteForceWord.{u} κ xL xR ρL ρR := by
  have hD := isDistinctForceWord_aug (xL := xL) hx
  have hcT : LP.IsCompleteForceWord.{u} κ (LP.retargetXL xL (augX (xR 0))) (LP.retargetXR (augX (xR 0)))
      (LP.retargetρL κ ρL (augρ (ρR 0))) (LP.retargetρR (augρ (ρR 0))) :=
    isCompleteForceWord_retarget_aug hEM
  obtain ⟨Ω₀, m₀, P₀, hP₀, 𝓕₀, W₀, VL₀, VR₀, B₀, ζ₀, hE₀⟩ :=
    LP.exists_isIntegratedSLEEvolution_ulift.{u} hκ (xL := xL) (xR := augX (xR 0)) (ρL := ρL)
      (ρR := augρ (ρR 0)) hD.1
  have htrA := ae_newW_trace hκ hD le_rfl hE₀ (retarget_sep_of_left_empty hD) hcT
  have hTr : LP.HasTransientGeneratingTrace P₀ W₀ ζ₀ := by
    filter_upwards [htrA, hE₀.ae_tendsto_threshold hκ, hE₀.2.2.2.2] with ω htr hlim hp
    obtain ⟨η, hη, hηt⟩ := exists_trace_of_path hD le_rfl hp hlim htr
    rw [sepTime_aug_eq hp hρ] at hη hηt
    exact ⟨η, hη, hηt⟩
  -- delete the passive mark
  have hE₁ := hE₀.compEmb (RelEmbedding.refl (· ≤ ·)) augEmb (fun i hi => absurd ⟨i, rfl⟩ hi) fun i hi => by
    have hi0 : (i : ℕ) = 0 := by
      by_contra h0
      exact hi ⟨0, Fin.ext (by simp [augEmb]; have := i.isLt; omega)⟩
    simp only [augρ, hi0, ↓reduceIte]
  have e1 : (fun j : Fin 1 => augX (xR 0) (augEmb j)) = xR := funext fun j => by
    have : j = 0 := Subsingleton.elim _ _
    subst this
    simp [augX, augEmb]
  have e2 : (fun j : Fin 1 => augρ (ρR 0) (augEmb j)) = ρR := funext fun j => by
    have : j = 0 := Subsingleton.elim _ _
    subst this
    simp [augρ, augEmb]
  have e0 : (fun j : Fin 0 => xL ((RelEmbedding.refl (· ≤ ·) : Fin 0 ↪o Fin 0) j)) = xL := rfl
  have e0' : (fun j : Fin 0 => ρL ((RelEmbedding.refl (· ≤ ·) : Fin 0 ↪o Fin 0) j)) = ρL := rfl
  rw [e1, e2, e0, e0'] at hE₁
  have hfin : LP.IsCompleteForceWord.{u} κ xL xR ρL ρR :=
    LP.isCompleteForceWord_of_ae_traceEvent hκ (fun i => i.elim0) hE₁ hTr
  intro Ω mΩ P _ 𝓕 W VL VR B ζ hE
  exact hfin P 𝓕 W VL VR B ζ hE

/-- **PROVE-ZHAN-A8's `hlow` from the seed one-force theorem.** The end-mark word of weight `c = κ − 6 − ρ ≥ κ/2 − 2 > −2`
is the reflection of one right mark at `1` of weight `c`, complete by Wang–Wu's Lemma 5.1 from the seed word
(`WangWu.Lemma51.isCompleteForceWord_oneRight_of_seed`); then `isCompleteForceWord_oneRight_low`. -/
theorem oneRightLow_of_seed {κ : ℝ} (hκ : 0 < κ)
    (hseed : ∀ (xL ρL : Fin 0 → ℝ) (ρR : Fin 1 → ℝ), -2 < ρR 0 →
      LP.IsCompleteForceWord.{u} κ xL (fun _ => 0) ρL ρR) :
    ∀ (xL ρL : Fin 0 → ℝ) (xR ρR : Fin 1 → ℝ), 0 < xR 0 → ρR 0 ≤ -2 → ρR 0 ≤ κ / 2 - 4 →
      LP.IsCompleteForceWord.{u} κ xL xR ρL ρR := by
  intro xL ρL xR ρR hx hρ hρ'
  set c := κ - 6 - ρR 0 with hc
  have hc2 : -2 < c := by rw [hc]; linarith
  have h1 : LP.IsCompleteForceWord.{u} κ (fun i : Fin 0 => i.elim0) (fun _ : Fin 1 => (1 : ℝ))
      (fun i : Fin 0 => i.elim0) (fun _ : Fin 1 => c) :=
    WangWu.Lemma51.isCompleteForceWord_oneRight_of_seed hκ one_pos hc2
      (hseed (fun i => i.elim0) (fun i => i.elim0) (fun _ => c) hc2)
  have h2 : LP.IsCompleteForceWord.{u} κ (-(fun _ : Fin 1 => (1 : ℝ))) (-(fun i : Fin 0 => (i.elim0 : ℝ)))
      (fun _ : Fin 1 => c) (fun i : Fin 0 => i.elim0) := LP.IsCompleteForceWord.reflect h1
  have e1 : (-(fun _ : Fin 1 => (1 : ℝ))) = fun _ : Fin 1 => (-1 : ℝ) := by funext i; simp
  have e2 : (-(fun i : Fin 0 => (i.elim0 : ℝ))) = fun i : Fin 0 => i.elim0 := funext fun i => i.elim0
  rw [e1, e2] at h2
  have hfin : LP.IsCompleteForceWord.{u} κ xL xR ρL ρR := isCompleteForceWord_oneRight_low hκ hx hρ h2
  intro Ω mΩ P _ 𝓕 W VL VR B ζ hE
  exact hfin P 𝓕 W VL VR B ζ hE

/-- **Aux. lemma 99 stopped from the seed one-force theorem alone** (PROVE-ZHAN-A8's
`aux99StoppedStatement_of_seed_of_low` with `hlow = oneRightLow_of_seed`). -/
theorem aux99StoppedStatement_of_seed {κ : ℝ} (hκ : 0 < κ)
    (hseed : ∀ (xL ρL : Fin 0 → ℝ) (ρR : Fin 1 → ℝ), -2 < ρR 0 →
      LP.IsCompleteForceWord.{u} κ xL (fun _ => 0) ρL ρR) :
    Aux99StoppedStatement.{u} κ :=
  aux99StoppedStatement_of_seed_of_low hκ hseed (oneRightLow_of_seed hκ hseed)

end Sec7

end InteractingSLE
