/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71PJunction

/-!
# Lemma 7.1's (CS), geometric half: CS-branch and the seed values

Packet PROVE-LEMMA71P. In the setting `IsTSetting` at capacity time `t`:

* `IsTSetting.wallInt_zero_left`, **`IsTSetting.wallInt_zero`**: the middle-curve integer of
  `Im (log g^γ_T′ − log ψ_t′)` is `0` at every middle chart point — on the left side by the junction with the left
  wall at `L_t − W_t` and constancy; on the right side by the tip corner when the left side is nonempty, and by the
  junction at `0 = L_t − W_t` otherwise;
* **`IsTSetting.tendsto_pocketLift_sub`** (CS-branch): at every middle chart point `x ≠ 0` landing at `γ(s)`, for every
  `q ∈ (s, T]`, `pocketLift ∘ pocketInv − Im log g^γ_q′ ∘ pocketInv → 0` (in the frozen coordinates of
  `Lemma71N.PocketCurveSideStatement`: the shifted chart `shiftLift c n`, the canonical driver of the mapped segment);
* **`tendsto_pocketG_mid`** (CS-G): the seed function `pocketG` (one left and one right mark) tends to `−λ` on
  `(V^L_t − W_t, 0)` and to `λ` on `(0, V^R_t − W_t)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.Lemma71P

open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull logDerivFwd)
open Lemma71N (IsPocketFrame IsPocketBranch)
open Lemma71O (land WallInt)
open Lemma71C (IsSegCurve capLife capInv segDriver)
open MartChar.RealFlow

namespace IsTSetting

variable {β α γ : ℝ≥0 → ℂ} {C : Set ℂ} {c : Chart} {Ψ : ℂ → ℂ} {a b : ℝ} {γ' : ℝ → ℂ} {κ : ℝ → ℝ} {n : ℤ}
  {W : ℝ → ℝ} {η : ℝ → ℂ} {t : ℝ≥0}

/-- **The integer is `0` on the left side of the slit** (junction at `L_t − W_t`, then constancy). -/
theorem wallInt_zero_left (hS : IsTSetting β α γ C c Ψ a b γ' κ n W η t) {Wβ Wα Wγ : ℝ≥0 → ℝ}
    (htrβ : IsGeneratingTrace Wβ ⊤ β) (htrα : IsGeneratingTrace Wα ⊤ α) (htrγ : IsGeneratingTrace Wγ ⊤ γ)
    {Lt : ℂ → ℂ} (hLt : IsDerivLog (tChart c n W t).1 Lt (tChart c n W t).dom)
    (hLte : ∀ z ∈ ((tChart c n W t).dom : Set ℂ), (tChart c n W t).2.2 z = (Lt z).im) {x : ℝ}
    (hxL : midL W t < x) (hx0 : x < 0) : WallInt (tChart c n W t) Lt Wγ hS.capT x 0 := by
  have hmR := midR_nonneg hS.hW hS.ht0
  obtain ⟨z, hz, h0⟩ := hS.exists_wallInt_zero_junction htrβ htrα htrγ hLt hLte (x₁ := 0) (by linarith)
    fun z hz => ⟨by linarith [hz.2], hz.2.ne⟩
  exact hS.wallInt_of_mem htrγ hLt isPreconnected_Ioo (fun z hz => ⟨hz.1, by linarith [hz.2], hz.2.ne⟩) hz
    ⟨hxL, hx0⟩ h0

/-- **The middle-curve integer is `0` at every middle chart point.** -/
theorem wallInt_zero (hS : IsTSetting β α γ C c Ψ a b γ' κ n W η t) {Wβ Wα Wγ : ℝ≥0 → ℝ}
    (htrβ : IsGeneratingTrace Wβ ⊤ β) (htrα : IsGeneratingTrace Wα ⊤ α) (htrγ : IsGeneratingTrace Wγ ⊤ γ)
    {Lt : ℂ → ℂ} (hLt : IsDerivLog (tChart c n W t).1 Lt (tChart c n W t).dom)
    (hLte : ∀ z ∈ ((tChart c n W t).dom : Set ℂ), (tChart c n W t).2.2 z = (Lt z).im) {x : ℝ}
    (hxL : midL W t < x) (hxR : x < midR W t) (hx0 : x ≠ 0) :
    WallInt (tChart c n W t) Lt Wγ hS.capT x 0 := by
  rcases lt_or_gt_of_ne hx0 with hneg | hpos
  · exact hS.wallInt_zero_left htrβ htrα htrγ hLt hLte hxL hneg
  · have hmL := midL_nonpos hS.hW hS.ht0
    have hR0 : 0 < midR W t := hpos.trans hxR
    by_cases hL0 : midL W t < 0
    · obtain ⟨m, ε, hε, hεL, hεR, hm⟩ := hS.exists_wallInt_tip htrγ hLt hL0 hR0
      have hzL := hS.wallInt_zero_left htrβ htrα htrγ hLt hLte (x := -(ε / 2)) (by linarith) (by linarith)
      have hmzL := hm (-(ε / 2)) (by rw [abs_neg, abs_of_pos (by linarith)]; linarith)
      have hm0 : m = 0 := Lemma71O.WallInt.unique hmzL hzL
      have hzR := hm (ε / 2) (by rw [abs_of_pos (by linarith)]; linarith)
      rw [hm0] at hzR
      exact hS.wallInt_of_mem htrγ hLt (I := Ioo 0 (midR W t)) isPreconnected_Ioo
        (fun z hz => ⟨by linarith [hz.1], hz.2, hz.1.ne'⟩) ⟨by linarith, by linarith⟩ ⟨hpos, hxR⟩ hzR
    · have hL0' : midL W t = 0 := le_antisymm hmL (not_lt.1 hL0)
      obtain ⟨z, hz, h0⟩ := hS.exists_wallInt_zero_junction htrβ htrα htrγ hLt hLte (x₁ := midR W t)
        (by linarith) fun z hz => ⟨hz.2, (show (0 : ℝ) < z by linarith [hz.1]).ne'⟩
      exact hS.wallInt_of_mem htrγ hLt isPreconnected_Ioo
        (fun z hz => ⟨hz.1, hz.2, (show (0 : ℝ) < z by linarith [hz.1]).ne'⟩) hz ⟨by linarith, hxR⟩ h0

/-- **CS-branch** (the inherited branch along the middle curve): at every middle chart point `x ≠ 0` at which the
inverse chart of the active component lands at `γ(s)`, for every `q` with `s < q ≤ T` (`T` the curve time of the
capacity stop), `pocketLift ∘ pocketInv − Im log g^γ_q′ ∘ pocketInv → 0`. -/
theorem tendsto_pocketLift_sub (hS : IsTSetting β α γ C c Ψ a b γ' κ n W η t) {Wβ Wα Wγ : ℝ≥0 → ℝ}
    (htrβ : IsGeneratingTrace Wβ ⊤ β) (htrα : IsGeneratingTrace Wα ⊤ α) (htrγ : IsGeneratingTrace Wγ ⊤ γ)
    {x : ℝ} (hxL : midL W t < x) (hxR : x < midR W t) (hx0 : x ≠ 0) {s q : ℝ≥0}
    (hland : Tendsto (Lemma71M.pocketInv (Lemma71E.shiftLift c n) (fun s => segDriver γ' s) t) (𝓝[H] (x : ℂ))
      (𝓝 (γ s)))
    (hsq : s < q) (hqT : q ≤ hS.capT) :
    Tendsto (fun y => Lemma71M.pocketLift (Lemma71E.shiftLift c n) (fun s => segDriver γ' s) t
        (Lemma71M.pocketInv (Lemma71E.shiftLift c n) (fun s => segDriver γ' s) t y) -
      (logDerivFwd (fun r : ℝ => Wγ r.toNNReal) q
        (Lemma71M.pocketInv (Lemma71E.shiftLift c n) (fun s => segDriver γ' s) t y)).im) (𝓝[H] (x : ℂ))
      (𝓝 0) := by
  have hF := hS.seg.frame
  obtain ⟨L, hL, hlift⟩ := hS.seg.log
  obtain ⟨Lt, hLt, hLte⟩ := exists_isDerivLog_tChart (t := t) hF.hc hF.hdom hL hlift hS.hW hS.hW0 n
  obtain ⟨-, -, hinv, hlift'⟩ := tChart_facts hF.hc hS.seg.seg hS.ht hS.hW hS.hW0 hS.hWe n
  have hland' : Tendsto (tChart c n W t).2.1 (𝓝[H] (x : ℂ)) (𝓝 (γ s)) :=
    hland.congr' (eventually_nhdsWithin_of_forall fun y hy => hinv y hy)
  have h0 := hS.wallInt_zero htrβ htrα htrγ hLt hLte hxL hxR hx0
  unfold WallInt at h0
  rw [Int.cast_zero, mul_zero] at h0
  have hd := tendsto_logDerivFwd_sub_of_le' htrγ (Lemma71O.continuous_of_isGeneratingTrace_top htrγ)
    (SideHeight.w_zero_of_isGeneratingTrace htrγ (by simp)) hS.seg.hγ hS.hc' (hS.subset_H_diff_fillH_prefix hqT)
    (hS.subset_H_diff_fillH_prefix le_rfl) (mem_Hbar_of_im_eq_zero (by simp)) hsq hqT hland'
  have h := hd.sub h0
  rw [sub_zero] at h
  refine h.congr' (eventually_nhdsWithin_of_forall fun y hy => ?_)
  show _ = Lemma71M.pocketLift (Lemma71E.shiftLift c n) (fun s => segDriver γ' s) t
      (Lemma71M.pocketInv (Lemma71E.shiftLift c n) (fun s => segDriver γ' s) t y) -
    (logDerivFwd (fun r : ℝ => Wγ r.toNNReal) q
      (Lemma71M.pocketInv (Lemma71E.shiftLift c n) (fun s => segDriver γ' s) t y)).im
  rw [hinv y hy, hlift', hLte _ (hS.inv_mem_dom hy)]
  simp only [Complex.sub_im]
  ring

end IsTSetting

/-! ### The seed values (CS-G) -/

section Seed

/-- **CS-G: the seed values of the active component's chart function between the marks**: with one left mark at
`V^L_t − W_t ≤ 0` and one right mark at `V^R_t − W_t ≥ 0`, the bounded harmonic function `pocketG` (with `a' = 0`)
tends to `−λ` at the real points of `(V^L_t − W_t, 0)` and to `λ` at those of `(0, V^R_t − W_t)`. -/
theorem tendsto_pocketG_mid (κ ρL ρR : ℝ) (w : ℝ≥0 → ℝ) (vL vR : Fin 1 → ℝ≥0 → ℝ) (t : ℝ≥0)
    (hvL : vL 0 t - w t ≤ 0) (hvR : 0 ≤ vR 0 t - w t) {x : ℝ}
    (hx : (vL 0 t - w t < x ∧ x < 0) ∨ (0 < x ∧ x < vR 0 t - w t)) :
    Tendsto (Lemma71M.pocketG κ (fun _ : Fin 1 => ρL) (fun _ : Fin 1 => ρR) w vL vR t 0) (𝓝[H] (x : ℂ))
      (𝓝 (if x < 0 then -sleLambda κ else sleLambda κ)) := by
  have hx0 : x ≠ 0 := by rcases hx with h | h <;> [exact h.2.ne; exact h.1.ne']
  have hxL : ∀ i : Fin 1, x ≠ vL i t - w t := fun i => by
    rw [Fin.fin_one_eq_zero i]
    rcases hx with h | h <;> [exact h.1.ne'; exact (by linarith [h.1] : vL 0 t - w t < x).ne']
  have hxR : ∀ i : Fin 1, x ≠ vR i t - w t := fun i => by
    rw [Fin.fin_one_eq_zero i]
    rcases hx with h | h <;> [exact (by linarith [h.2] : x < vR 0 t - w t).ne; exact h.2.ne]
  have hlim := Lemma71N.tendsto_meanHarmonic κ (fun _ : Fin 1 => ρL) (fun _ : Fin 1 => ρR)
    (fun i => vL i t - w t) (fun i => vR i t - w t) hx0 hxL hxR
  have hval : Ito.meanHarmonic κ (fun _ : Fin 1 => ρL) (fun _ : Fin 1 => ρR) (fun i => vL i t - w t)
      (fun i => vR i t - w t) (x : ℂ) = if x < 0 then -sleLambda κ else sleLambda κ := by
    unfold Ito.meanHarmonic sleLambda
    simp only [Fin.sum_univ_one]
    have e1 : (x : ℂ) - ((vL 0 t - w t : ℝ) : ℂ) = ((x - (vL 0 t - w t) : ℝ) : ℂ) := by push_cast; ring
    have e2 : (x : ℂ) - ((vR 0 t - w t : ℝ) : ℂ) = ((x - (vR 0 t - w t) : ℝ) : ℂ) := by push_cast; ring
    rw [e1, e2]
    rcases hx with h | h
    · simp only [h.2, ↓reduceIte]
      rw [Complex.arg_ofReal_of_neg h.2, Complex.arg_ofReal_of_nonneg (by linarith [h.1]),
        Complex.arg_ofReal_of_neg (by linarith [h.2])]
      field_simp
      ring
    · simp only [not_lt.2 h.1.le, ↓reduceIte]
      rw [Complex.arg_ofReal_of_nonneg h.1.le,
        Complex.arg_ofReal_of_nonneg (by linarith [h.1]), Complex.arg_ofReal_of_neg (by linarith [h.2])]
      field_simp
      ring
  rw [← hval]
  have e : Lemma71M.pocketG κ (fun _ : Fin 1 => ρL) (fun _ : Fin 1 => ρR) w vL vR t 0 =
      Ito.meanHarmonic κ (fun _ : Fin 1 => ρL) (fun _ : Fin 1 => ρR) (fun i => vL i t - w t)
        (fun i => vR i t - w t) := by
    funext y; simp only [Lemma71M.pocketG, sub_zero]
  rw [e]
  exact hlim

end Seed

end InteractingSLE.Sec7.Lemma71P
