/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Foundations.Strip.SLE
import InteractingSLE.Spec.Sec4.RepulsionNoncollision
import InteractingSLE.Spec.Sec4.Prob41Lemmas

/-!
# Constant strip drift at and beyond the critical value `σ = 1`

Packet PROVE-ZHAN-A. Astra §3, "Constant drift at and beyond the critical values" (`ig1_formalization_proofs.txt`
L1500–L1515): "For `σ ≥ 1`, map the strip by `F(z) = e^z − 1`. Covariance gives a chordal process with one force at
`−1` of weight `ρ = κ/2 − 3 + σ ≥ c`, `u'(t) = e^{2(ξ_t − t)}`. … The preceding one-force transience theorem therefore
gives `F(η(t)) → ∞`, so `η(t) → +∞`."

In the R36 form this covariance is the definition: the constant-drift strip `SLE_κ` (no lower marks) with endpoint
charges `q₋ = τ₋`, `q₊ = κ − 6 − τ₋` has `σ = (q₋ − q₊)/2 = τ₋ − κ/2 + 3`, and is the chordal `SLE_κ(τ₋)` with one
force point at `−1` (`IsStripSLEEvolution κ ![] ![] ![] ![] τ₋`); the chordal clock is `u'(t) = e^{2(ξ_t − t)}`
(`IsSepMark.hasDerivAt_chordalTime_eq_exp`). For `σ ≥ 1`, i.e. `τ₋ ≥ κ/2 − 2 = c`:

* the end mark never collides with the driver and the chordal lifetime is infinite (Aux. lemma 6, proved:
  `Sec4.aux6Statement`), so every chordal time lies in the strip life (`isStripLife_of_aux6`);
* with the one-force transience theorem (Aux. lemma 7, the named input `Sec4.Aux7Statement`, discharged for
  `κ ≤ 4` by packet PROVE-ZHAN-B), every continuous generating trace tends to `∞`, so the strip trace
  `log(1 + η)` has real part tending to `+∞`: the strip endpoint is the end `+∞`
  (`ae_tendsto_re_log_one_add_of_aux7`).

The case `σ ≤ −1` is the reflection; in the R36 form its target is the end mark itself (a different chart) and it
is not treated here.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Zhan

open Strip

variable {κ τm : ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : MeasureTheory.Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin (0 + 1) → ℝ≥0 → Ω → ℝ}
  {VR : Fin 0 → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- The one-force chordal word of the constant-drift strip evolution is ordered. -/
theorem isOrderedForceWord_oneForce :
    IsOrderedForceWord (wordXL (Fin.elim0 : Fin 0 → ℝ)) (wordXR (Fin.elim0 : Fin 0 → ℝ)) :=
  (show IsOrderedStripWord (Fin.elim0 : Fin 0 → ℝ) (Fin.elim0 : Fin 0 → ℝ) from
    ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩).isOrderedForceWord

/-- For `τ₋ ≥ κ/2 − 2` the one-force word has admissible partial sums. -/
theorem hasAdmissiblePartialSums_oneForce (hτ : κ / 2 - 2 ≤ τm) :
    Sec4.HasAdmissiblePartialSums κ (wordRhoL (Fin.elim0 : Fin 0 → ℝ) τm) (Fin.elim0 : Fin 0 → ℝ)
      (wordXL (Fin.elim0 : Fin 0 → ℝ)) (wordXR (Fin.elim0 : Fin 0 → ℝ)) := by
  refine ⟨fun x _ ⟨i, hi⟩ => ?_, fun x _ ⟨i, _⟩ => i.elim0⟩
  have hlast : ∀ j : Fin (0 + 1), j = Fin.last 0 := fun j => Fin.ext (by have := j.2; simp)
  have hx : x < -1 := by rw [hlast i, wordXL_last] at hi; exact hi
  have hfilter : (Finset.univ.filter fun j : Fin (0 + 1) => x < wordXL (Fin.elim0 : Fin 0 → ℝ) j) =
      Finset.univ := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    rw [hlast j, wordXL_last]; exact hx
  rw [hfilter, Fin.sum_univ_castSucc, Fin.sum_univ_zero, zero_add, wordRhoL_last]
  exact hτ

/-- **The strip life is the whole chordal life** for `σ ≥ 1` (`τ₋ ≥ κ/2 − 2`): almost surely `ζ = ∞` and the end
mark stays strictly left of the driver at all times (Aux. lemma 6). -/
theorem ae_isStripLife_of_aux6 (hκ : 0 < κ) (hτ : κ / 2 - 2 ≤ τm)
    (hE : IsStripSLEEvolution κ (Fin.elim0 : Fin 0 → ℝ) (Fin.elim0 : Fin 0 → ℝ) (Fin.elim0 : Fin 0 → ℝ)
      (Fin.elim0 : Fin 0 → ℝ) τm P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ ∀ s : ℝ≥0, IsStripLife (W · ω) (VL (Fin.last 0) · ω) (ζ ω) s := by
  have h6 := Sec4.aux6Statement.{u} hκ _ _ _ _ P 𝓕 W VL VR B ζ isOrderedForceWord_oneForce
    (hasAdmissiblePartialSums_oneForce hτ) hE
  filter_upwards [h6, hE.2.2.2.2] with ω h6ω hp
  refine ⟨h6ω.1, fun s => ⟨by rw [h6ω.1]; exact ENNReal.coe_lt_top, fun r _ => ?_⟩⟩
  rcases eq_zero_or_pos r with hr | hr
  · have e1 : W 0 ω = 0 := hp.1
    have e2 : VL (Fin.last 0) 0 ω = wordXL (Fin.elim0 : Fin 0 → ℝ) (Fin.last 0) := hp.2.1 (Fin.last 0)
    show VL (Fin.last 0) r ω < W r ω
    rw [hr, e1, e2, wordXL_last]; norm_num
  · exact (h6ω.2 r hr).1 (Fin.last 0)

/-- `Re log(1 + η) → +∞` when `|η| → ∞`. -/
theorem tendsto_re_log_one_add {η : ℝ≥0 → ℂ} (hη : Tendsto (fun t => ‖η t‖) atTop atTop) :
    Tendsto (fun t => (log (1 + η t)).re) atTop atTop := by
  have h1 : Tendsto (fun t => ‖1 + η t‖) atTop atTop := by
    refine tendsto_atTop_mono (fun t => ?_) (tendsto_atTop_add_const_right _ (-1) hη)
    have := norm_sub_norm_le (η t) (-1)
    rw [sub_neg_eq_add, norm_neg, norm_one, add_comm] at this
    linarith
  simp only [log_re]
  exact Real.tendsto_log_atTop.comp h1

/-- **Constant strip drift `σ ≥ 1` (including the critical value)**, from the one-force transience theorem
(Aux. lemma 7, named input): almost surely the strip life is the whole chordal life, a continuous generating trace
exists, and every such trace `η` has strip trace `log(1 + η)` with real part tending to `+∞`, i.e. the strip trace
ends at the end `+∞`. -/
theorem ae_tendsto_re_log_one_add_of_aux7 (h7 : Sec4.Aux7Statement.{u} κ) (hκ : 0 < κ)
    (hτ : κ / 2 - 2 ≤ τm)
    (hE : IsStripSLEEvolution κ (Fin.elim0 : Fin 0 → ℝ) (Fin.elim0 : Fin 0 → ℝ) (Fin.elim0 : Fin 0 → ℝ)
      (Fin.elim0 : Fin 0 → ℝ) τm P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ (∀ s : ℝ≥0, IsStripLife (W · ω) (VL (Fin.last 0) · ω) (ζ ω) s) ∧
      (∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (W · ω) ⊤ η) ∧
      ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (W · ω) ⊤ η →
        Tendsto (fun t => (log (1 + η t)).re) atTop atTop := by
  have h7ω := h7 _ _ _ _ P 𝓕 W VL VR B ζ isOrderedForceWord_oneForce
    (hasAdmissiblePartialSums_oneForce hτ) hE
  filter_upwards [h7ω, ae_isStripLife_of_aux6 hκ hτ hE] with ω h1 h2
  exact ⟨h2.1, h2.2, h1.2.1, fun η hη => tendsto_re_log_one_add (h1.2.2 η hη)⟩

end Zhan

end InteractingSLE
