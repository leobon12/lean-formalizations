/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.A2Part1Main
import InteractingSLE.Spec.ZhanGT4.CrosscutA2

/-!
# A.2, part 1: the small curve is a simple crosscut (both regimes)

Packet PROVE-ZHAN-A2P1. Source: Astra, *Follow-up proofs*, §A.2 L524–L536, with §A.3.2 L702–L705 (the (G3) setup) and
§A.3.1 L666–L670 (the (Eight) setup). The small `SLE_{κ̂}` with seeds, `κ̂ = 16/κ`, is the evolution of the words
`A2X.smallG3RhoL/R` (source `y`, seed `y⁻` weight `3κ̂/2 − 4`, seed `y⁺` weight `2 − κ̂/2`, mark `x` weight `κ̂ − 4`,
large tip `0` weight `−κ̂/2`) and `A2X.smallEightRhoL/R` (source `x`, seed `x⁻` weight `−κ̂/2`, seed `x⁺` weight
`κ̂/2 − 2`, large tip `0` weight `−κ̂/2`). After the reflection `z ↦ −z̄`, the large tip is the last left mark, the
only non-admissible weight; the theorem `ae_exit_trace` (A2Part1Main) gives the simple trace with a real endpoint
beyond it, which is the positive point of the source after reflecting back.

## Main results

* `exists_isSmallCrosscut_of_trace`: the pathwise assembly of the crosscut from a simple trace with a real endpoint;
* **`a2SmallCrosscutG3Statement`**: `A2X.A2SmallCrosscutG3Statement κ` for every `κ`;
* **`a2SmallCrosscutEightStatement`**: `A2X.A2SmallCrosscutEightStatement κ` for every `κ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.ZhanGT4.A2P1

open QuantumZipper (H)

/-! ### The crosscut from a simple trace with a real endpoint -/

/-- **The pathwise assembly.** A generating trace on `[0, ζ]`, `0 < ζ < ∞`, injective on `[0, ζ]`, in `ℍ` on
`(0, ζ)`, with real endpoint `p` and `0 < p + x₁`, reparametrized by `s ↦ η(sζ) + x₁` on `[0, 1]`, is a small
crosscut from `x₁`. -/
theorem exists_isSmallCrosscut_of_trace {x₁ : ℝ} {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hζ0 : 0 < ζ) (hζ : ζ ≠ ⊤)
    {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace w ζ η) (hinj : InjOn η {t | (t : ℝ≥0∞) ≤ ζ})
    (hH : ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < ζ → η t ∈ H) {p : ℝ} (hp : 0 < p + x₁)
    (hend : η ζ.toNNReal = p) : ∃ γ : ℝ → ℂ, A2X.IsSmallCrosscut x₁ w ζ γ := by
  set Z : ℝ≥0 := ζ.toNNReal with hZdef
  have hZζ : (Z : ℝ≥0∞) = ζ := ENNReal.coe_toNNReal hζ
  have hZ0 : 0 < (Z : ℝ) := by
    have : (0 : ℝ≥0∞) < (Z : ℝ≥0∞) := by rw [hZζ]; exact hζ0
    exact_mod_cast this
  set φ : ℝ → ℝ≥0 := fun s => (s * Z).toNNReal with hφ
  have hφc : Continuous φ := continuous_real_toNNReal.comp (continuous_id.mul continuous_const)
  have hφcoe : ∀ s, 0 ≤ s → ((φ s : ℝ≥0) : ℝ) = s * Z := fun s hs =>
    Real.coe_toNNReal _ (mul_nonneg hs hZ0.le)
  have hφle : ∀ s ∈ Icc (0 : ℝ) 1, ((φ s : ℝ≥0) : ℝ≥0∞) ≤ ζ := fun s hs => by
    rw [← hZζ, ENNReal.coe_le_coe, ← NNReal.coe_le_coe, hφcoe s hs.1]
    nlinarith [hs.2]
  have hφlt : ∀ s ∈ Ioo (0 : ℝ) 1, 0 < φ s ∧ ((φ s : ℝ≥0) : ℝ≥0∞) < ζ := fun s hs => by
    refine ⟨Real.toNNReal_pos.2 (mul_pos hs.1 hZ0), ?_⟩
    rw [← hZζ, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, hφcoe s hs.1.le]
    nlinarith [hs.2]
  have hφ0 : φ 0 = 0 := by simp [hφ]
  have hφ1 : φ 1 = Z := by simp [hφ]
  set γ : ℝ → ℂ := fun s => η (φ s) + x₁ with hγ
  have hη0 : η 0 = 0 := hη.1
  refine ⟨γ, ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, η, hη, ?_⟩⟩
  · -- continuity on `[0, 1]`
    refine ContinuousOn.add ?_ continuousOn_const
    exact hη.2.1.comp hφc.continuousOn fun s hs => hφle s hs
  · -- injectivity on `[0, 1]`
    intro s hs s' hs' h
    have h' : η (φ s) = η (φ s') := by simpa [hγ] using h
    have he := hinj (hφle s hs) (hφle s' hs') h'
    have := congrArg (fun t : ℝ≥0 => (t : ℝ)) he
    simp only [hφcoe s hs.1, hφcoe s' hs'.1] at this
    exact mul_right_cancel₀ hZ0.ne' this
  · -- the open part lies in `ℍ`
    rintro z ⟨s, hs, rfl⟩
    have hmem := hH (φ s) (hφlt s hs).1 (hφlt s hs).2
    show (0 : ℝ) < (η (φ s) + x₁).im
    rw [Complex.add_im, Complex.ofReal_im, add_zero]
    exact hmem
  · show (η (φ 0) + x₁).im = 0
    rw [hφ0, hη0]; simp
  · show (η (φ 1) + x₁).im = 0
    rw [hφ1, hend]; simp
  · show (η (φ 0) + x₁).re = x₁
    rw [hφ0, hη0]; simp
  · show 0 < (η (φ 1) + x₁).re
    rw [hφ1, hend]; simpa using hp
  · -- the open part is the translated trace over the open lifetime
    ext z
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨η (φ s), ⟨φ s, hφlt s hs, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨t, ⟨ht0, htζ⟩, rfl⟩, rfl⟩
      have htZ : (t : ℝ) < Z := by
        have : t < Z := by rw [← hZζ] at htζ; exact_mod_cast htζ
        exact_mod_cast this
      have ht0' : (0 : ℝ) < t := by exact_mod_cast ht0
      refine ⟨(t : ℝ) / Z, ⟨div_pos ht0' hZ0, (div_lt_one hZ0).2 htZ⟩, ?_⟩
      have : φ ((t : ℝ) / Z) = t := by
        rw [← NNReal.coe_inj, hφcoe _ (div_pos ht0' hZ0).le, div_mul_cancel₀ _ hZ0.ne']
      show η (φ ((t : ℝ) / Z)) + x₁ = η t + x₁
      rw [this]

/-- **Reflecting the trace back.** If `η` is a simple generating trace of the reflected driver `−w` on `[0, ζ]` with
real endpoint `x`, then `z ↦ −z̄` maps it to a simple generating trace of `w` with endpoint `−x`, and the small crosscut
of `w` from `x₁` exists as soon as `0 < −x + x₁`. -/
theorem exists_isSmallCrosscut_of_reflect {x₁ : ℝ} {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} (hζ0 : 0 < ζ) (hζ : ζ ≠ ⊤)
    {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace (fun t => -w t) ζ η) (hinj : InjOn η {t | (t : ℝ≥0∞) ≤ ζ})
    (hH : ∀ t : ℝ≥0, 0 < t → (t : ℝ≥0∞) < ζ → η t ∈ H) {x : ℝ} (hx : 0 < -x + x₁)
    (hend : η ζ.toNNReal = x) : ∃ γ : ℝ → ℂ, A2X.IsSmallCrosscut x₁ w ζ γ := by
  have hη' := LP.isGeneratingTrace_reflect hη
  have e : (-fun t => -w t) = w := by funext t; simp
  rw [e] at hη'
  refine exists_isSmallCrosscut_of_trace hζ0 hζ hη' (fun t ht t' ht' h => hinj ht ht' ?_)
    (fun t ht0 ht => LP.reflectC_mem_H_iff.2 (hH t ht0 ht)) hx ?_
  · have := congrArg LP.reflectC h
    simpa using this
  · show LP.reflectC (η ζ.toNNReal) = ((-x : ℝ) : ℂ)
    rw [hend, LP.reflectC]
    simp

/-! ### The reflected small words -/

section Words

variable {k x y : ℝ}

/-- The reflected (G3) left word `0⁻, y − x, y` (the reflected seed `y⁺`, mark `x`, large tip). -/
theorem g3_strictAnti (hyx : y < x) (hx : x < 0) : StrictAnti (-![0, x - y, -y] : Fin 3 → ℝ) := by
  rw [Fin.strictAnti_iff_succ_lt]
  intro i
  fin_cases i <;> simp <;> linarith

theorem g3_ordered (hyx : y < x) (hx : x < 0) :
    IsOrderedForceWord (-![0, x - y, -y] : Fin 3 → ℝ) (-![(0 : ℝ)]) := by
  refine ⟨(g3_strictAnti hyx hx).antitone, fun i => ?_, fun a b _ => le_of_eq (by rw [Subsingleton.elim a b]),
    fun i => by simp⟩
  fin_cases i <;> simp <;> linarith

theorem g3_last (y x : ℝ) : (-![0, x - y, -y] : Fin 3 → ℝ) (Fin.last 2) = y := by simp

theorem g3_adm (hk2 : 2 ≤ k) (hk4 : k ≤ 4) (hx : x < 0) :
    Sec4.HasAdmissiblePartialSums k ![2 - k / 2, k - 4, 0] ![3 * k / 2 - 4] (-![0, x - y, -y] : Fin 3 → ℝ)
      (-![(0 : ℝ)]) := by
  refine ⟨fun z hz _ => ?_, fun z hz _ => ?_⟩
  · rw [Finset.sum_filter, Fin.sum_univ_three]
    simp only [Fin.isValue, Pi.neg_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, neg_zero, neg_sub, neg_neg]
    split_ifs <;> linarith
  · rw [Finset.sum_filter, Fin.sum_univ_one]
    simp only [Fin.isValue, Pi.neg_apply, Matrix.cons_val_zero, neg_zero]
    split_ifs <;> linarith

theorem g3_sum (k : ℝ) : ∑ i, (![2 - k / 2, k - 4, -(k / 2)] : Fin 3 → ℝ) i ≤ -2 := by
  rw [Fin.sum_univ_three]
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  linarith

theorem g3_preL (hk0 : 0 < k) (hk4 : k < 4) : ∀ m : Fin (2 + 1), m ≠ Fin.last 2 →
    -2 < ∑ i ∈ Finset.Iic m, (![2 - k / 2, k - 4, -(k / 2)] : Fin 3 → ℝ) i := by
  intro m hm
  fin_cases m
  · have e : Finset.Iic (0 : Fin 3) = {0} := by decide
    simp only [Fin.zero_eta, e, Finset.sum_singleton, Matrix.cons_val_zero]
    linarith
  · have e : Finset.Iic (1 : Fin 3) = {0, 1} := by decide
    simp only [Fin.mk_one, e, Finset.sum_insert (by decide : (0 : Fin 3) ∉ ({1} : Finset (Fin 3))),
      Finset.sum_singleton, Matrix.cons_val_zero, Matrix.cons_val_one]
    linarith
  · exact absurd rfl hm

theorem one_preR {r : ℝ} (hr : -2 < r) : ∀ m : Fin 1, -2 < ∑ i ∈ Finset.Iic m, (![r] : Fin 1 → ℝ) i := by
  intro m
  have e : Finset.Iic m = {0} := by
    rw [Subsingleton.elim m 0]; decide
  rw [e, Finset.sum_singleton]
  simpa using hr

theorem g3_pre (hk2 : 2 ≤ k) (hk4 : k ≤ 4) :
    Strip.HasStripPrefixSums k (Fin.init (![2 - k / 2, k - 4, -(k / 2)] : Fin 3 → ℝ)) ![3 * k / 2 - 4] := by
  refine ⟨fun m => ?_, fun m => ?_⟩
  · fin_cases m
    · have e : Finset.Iic (0 : Fin 2) = {0} := by decide
      simp only [Fin.zero_eta, e, Finset.sum_singleton, Fin.init, Fin.castSucc_zero, Matrix.cons_val_zero]
      linarith
    · have e : Finset.Iic (1 : Fin 2) = {0, 1} := by decide
      simp only [Fin.mk_one, e, Finset.sum_insert (by decide : (0 : Fin 2) ∉ ({1} : Finset (Fin 2))),
        Finset.sum_singleton, Fin.init, Fin.castSucc_zero, Fin.castSucc_one, Matrix.cons_val_zero,
        Matrix.cons_val_one]
      linarith
  · have e : Finset.Iic m = {0} := by rw [Subsingleton.elim m 0]; decide
    rw [e, Finset.sum_singleton]
    simp only [Fin.isValue, Matrix.cons_val_zero]
    linarith

theorem g3_q (hk0 : 0 < k) (hk4 : k < 4) :
    |Strip.chargePlus k (Fin.init (![2 - k / 2, k - 4, -(k / 2)] : Fin 3 → ℝ)) ![3 * k / 2 - 4]
        ((![2 - k / 2, k - 4, -(k / 2)] : Fin 3 → ℝ) (Fin.last 2)) -
      Strip.chargeMinus (Fin.init (![2 - k / 2, k - 4, -(k / 2)] : Fin 3 → ℝ))
        ((![2 - k / 2, k - 4, -(k / 2)] : Fin 3 → ℝ) (Fin.last 2))| < 2 := by
  simp only [Strip.chargePlus, Strip.tauPlus, Strip.chargeMinus, Fin.sum_univ_two, Fin.sum_univ_one, Fin.init,
    Fin.castSucc_zero, Fin.castSucc_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
  have e : (![2 - k / 2, k - 4, -(k / 2)] : Fin 3 → ℝ) (Fin.last 2) = -(k / 2) := rfl
  rw [e, abs_lt]
  constructor <;> linarith

/-- The reflected (Eight) left word `0⁻, x` (the reflected seed `x⁺` and the large tip). -/
theorem e8_strictAnti (hx : x < 0) : StrictAnti (-![0, -x] : Fin 2 → ℝ) := by
  rw [Fin.strictAnti_iff_succ_lt]
  intro i
  fin_cases i
  simpa using hx

theorem e8_ordered (hx : x < 0) : IsOrderedForceWord (-![0, -x] : Fin 2 → ℝ) (-![(0 : ℝ)]) := by
  refine ⟨(e8_strictAnti hx).antitone, fun i => ?_, fun a b _ => le_of_eq (by rw [Subsingleton.elim a b]),
    fun i => by simp⟩
  fin_cases i <;> simp [hx.le]

theorem e8_last (x : ℝ) : (-![0, -x] : Fin 2 → ℝ) (Fin.last 1) = x := by simp

theorem e8_adm (hk2 : k ≤ 2) :
    Sec4.HasAdmissiblePartialSums k ![k / 2 - 2, 0] ![-(k / 2)] (-![0, -x] : Fin 2 → ℝ) (-![(0 : ℝ)]) := by
  refine ⟨fun z hz _ => ?_, fun z hz _ => ?_⟩
  · rw [Finset.sum_filter, Fin.sum_univ_two]
    simp only [Fin.isValue, Pi.neg_apply, Matrix.cons_val_zero, Matrix.cons_val_one, neg_zero, neg_neg]
    split_ifs <;> linarith
  · rw [Finset.sum_filter, Fin.sum_univ_one]
    simp only [Fin.isValue, Pi.neg_apply, Matrix.cons_val_zero, neg_zero]
    split_ifs <;> linarith

theorem e8_sum (k : ℝ) : ∑ i, (![k / 2 - 2, -(k / 2)] : Fin 2 → ℝ) i ≤ -2 := by
  rw [Fin.sum_univ_two]
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
  linarith

theorem e8_preL (hk0 : 0 < k) : ∀ m : Fin (1 + 1), m ≠ Fin.last 1 →
    -2 < ∑ i ∈ Finset.Iic m, (![k / 2 - 2, -(k / 2)] : Fin 2 → ℝ) i := by
  intro m hm
  fin_cases m
  · have e : Finset.Iic (0 : Fin 2) = {0} := by decide
    simp only [Fin.zero_eta, e, Finset.sum_singleton, Matrix.cons_val_zero]
    linarith
  · exact absurd rfl hm

theorem e8_pre (hk2 : k ≤ 2) :
    Strip.HasStripPrefixSums k (Fin.init (![k / 2 - 2, -(k / 2)] : Fin 2 → ℝ)) ![-(k / 2)] := by
  refine ⟨fun m => ?_, fun m => ?_⟩
  · have e : Finset.Iic m = {0} := by rw [Subsingleton.elim m 0]; decide
    rw [e, Finset.sum_singleton]
    simp only [Fin.init, Fin.isValue, Fin.castSucc_zero, Matrix.cons_val_zero, le_refl]
  · have e : Finset.Iic m = {0} := by rw [Subsingleton.elim m 0]; decide
    rw [e, Finset.sum_singleton]
    simp only [Fin.isValue, Matrix.cons_val_zero]
    linarith

theorem e8_q (hk0 : 0 < k) (hk4 : k < 4) :
    |Strip.chargePlus k (Fin.init (![k / 2 - 2, -(k / 2)] : Fin 2 → ℝ)) ![-(k / 2)]
        ((![k / 2 - 2, -(k / 2)] : Fin 2 → ℝ) (Fin.last 1)) -
      Strip.chargeMinus (Fin.init (![k / 2 - 2, -(k / 2)] : Fin 2 → ℝ))
        ((![k / 2 - 2, -(k / 2)] : Fin 2 → ℝ) (Fin.last 1))| < 2 := by
  simp only [Strip.chargePlus, Strip.tauPlus, Strip.chargeMinus, Fin.sum_univ_one, Fin.init,
    Fin.castSucc_zero, Fin.isValue, Matrix.cons_val_zero]
  have e : (![k / 2 - 2, -(k / 2)] : Fin 2 → ℝ) (Fin.last 1) = -(k / 2) := rfl
  rw [e, abs_lt]
  constructor <;> linarith

end Words

/-! ### The two statements -/

/-- **A.2, part 1, (G3)** (L524–L536 with §A.3.2 L702–L705): for `4 < κ < 8`, every integrated `SLE_{κ̂}` evolution of
the (G3) small word is almost surely a simple crosscut from `y` to a positive point. -/
theorem a2SmallCrosscutG3Statement (κ : ℝ) : A2X.A2SmallCrosscutG3Statement.{u} κ := by
  intro hκ4 hκ8 y x hyx hx Ω mΩ P _ 𝓕 W VL VR B ζ hE
  obtain ⟨hk2, hk4⟩ := A2X.kh_bounds_G3 hκ4 hκ8
  have hk0 : 0 < A2X.kh κ := by linarith
  have h := ae_exit_trace (ρL' := ![2 - A2X.kh κ / 2, A2X.kh κ - 4, 0]) hk0 hk4.le (g3_ordered hyx hx)
    (g3_strictAnti hyx hx) (by rw [g3_last]; linarith)
    (fun i hi => by fin_cases i <;> first | rfl | exact absurd rfl hi)
    (g3_adm hk2.le hk4.le hx) (g3_sum _) (g3_preL hk0 hk4) (one_preR (by linarith)) (g3_pre hk2.le hk4.le)
    (g3_q hk0 hk4) hE.reflect
  filter_upwards [h] with ω ⟨hζ0, hζ, η, hη, hinj, hH, x₀, hx₀, hend⟩
  rw [g3_last] at hx₀
  exact exists_isSmallCrosscut_of_reflect hζ0 hζ hη hinj hH (by linarith) hend

/-- **A.2, part 1, (Eight)** (L524–L536 with §A.3.1 L666–L670): for `κ ≥ 8`, every integrated `SLE_{κ̂}` evolution of
the (Eight) small word is almost surely a simple crosscut from `x` to a positive point. -/
theorem a2SmallCrosscutEightStatement (κ : ℝ) : A2X.A2SmallCrosscutEightStatement.{u} κ := by
  intro hκ8 x hx Ω mΩ P _ 𝓕 W VL VR B ζ hE
  obtain ⟨hk0, hk2⟩ := A2X.kh_bounds_eight hκ8
  have h := ae_exit_trace (ρL' := ![A2X.kh κ / 2 - 2, 0]) hk0 (by linarith) (e8_ordered hx) (e8_strictAnti hx)
    (by rw [e8_last]; exact hx) (fun i hi => by fin_cases i <;> first | rfl | exact absurd rfl hi)
    (e8_adm hk2) (e8_sum _) (e8_preL hk0) (one_preR (by linarith)) (e8_pre hk2) (e8_q hk0 (by linarith))
    hE.reflect
  filter_upwards [h] with ω ⟨hζ0, hζ, η, hη, hinj, hH, x₀, hx₀, hend⟩
  rw [e8_last] at hx₀
  exact exists_isSmallCrosscut_of_reflect hζ0 hζ hη hinj hH (by linarith) hend

end InteractingSLE.ZhanGT4.A2P1
