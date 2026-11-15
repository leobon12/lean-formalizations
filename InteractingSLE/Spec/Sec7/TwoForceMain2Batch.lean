/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

/-!
# Finite-batch pasting of birth kernels (Aux. lemma 49, (PF1)–(PF4))

Packet PROVE-SEC7-A3 (specification §7.1, Aux. lemma 49, `source/spec/p193-240.md` L766–L810,
pp. 233–235; reused in Aux. lemma 50, "Forgetting the germs", `p241-288.md` L17, p. 241). Pocket batches
are born at ordered recorded times. At each birth the newborn fields have a conditional kernel given the
announced pre-birth information (PF1), and future driving does not change the law of observables of the
already revealed germ (hypothesis (i) of Aux. lemma 49, the freezing identity (GB5)). The tower
calculation (PF2) then gives, by induction, the product formula (PF3) given the recorded history, and
with the active-field kernel (iv) the full finite-component factorization (PF4):

* `condExp_prod_eq_prod_of_batches` — (PF1)–(PF3);
* `condExp_mul_prod_eq_of_active` — (PF4).

Observables are complex and bounded by `1` (characteristic-function factors, as in Aux. lemma 50, or
bounded field tests). The single pasting step with real observables is `aux49_pasting_step`
(`TwoForceMainKernel`, PROVE-SEC7-A2).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set

namespace InteractingSLE

namespace Sec7

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- Pull-out for complex products (left factor measurable). -/
lemma condExp_mul_of_aestronglyMeasurable_left_complex {m : MeasurableSpace Ω} {f g : Ω → ℂ}
    (hf : AEStronglyMeasurable[m] f P) (hfg : Integrable (f * g) P) (hg : Integrable g P) :
    P[f * g | m] =ᵐ[P] f * P[g | m] :=
  condExp_bilin_of_aestronglyMeasurable_left (ContinuousLinearMap.mul ℝ ℂ) hf hfg hg

/-- Pull-out for complex products (right factor measurable). -/
lemma condExp_mul_of_aestronglyMeasurable_right_complex {m : MeasurableSpace Ω} {f g : Ω → ℂ}
    (hg : AEStronglyMeasurable[m] g P) (hfg : Integrable (f * g) P) (hf : Integrable f P) :
    P[f * g | m] =ᵐ[P] P[f | m] * g :=
  condExp_bilin_of_aestronglyMeasurable_right (ContinuousLinearMap.mul ℝ ℂ) hg hfg hf

lemma norm_prod_le_of_norm_le_one {ι : Type*} (s : Finset ι) (Y : ι → ℂ) (hY : ∀ i, ‖Y i‖ ≤ 1) :
    ‖∏ i ∈ s, Y i‖ ≤ 1 := by
  rw [norm_prod]
  exact Finset.prod_le_one₀ (fun i _ => norm_nonneg _) fun i _ => hY i

/-- **(PF1)–(PF3): finite-batch pasting** (Aux. lemma 49, p. 234–235; also "Forgetting the germs" in
Aux. lemma 50, p. 241). Batches `j = 0, 1, …` are born at ordered times; `ℋ (j + 1)` is the recorded
history at the `j`-th birth, `Pa j` its announced pre-birth `σ`-algebra (it contains that history and
the full germ `𝒢 j` at the previous birth, which already holds the earlier batches' fields), and
`𝒢 (j + 1)` the full germ at the birth. If the `j`-th batch observable `Y j` (bounded by `1`, a product
of characteristic-function factors) is `𝒢 (j + 1)`-measurable with kernel expectation
`E[Y j | Pa j] = q j` measurable from the recorded history (PF1), and future driving does not change the
law of germ observables, `E[Z | ℋ (j + 1)] = E[Z | ℋ j]` for bounded `𝒢 j`-measurable `Z` (hypothesis
(i), the freezing identity (GB5)), then `E[∏_{j<n} Y j | ℋ n] = ∏_{j<n} q j` (PF3), by induction on (PF2). -/
theorem condExp_prod_eq_prod_of_batches [IsFiniteMeasure P] {ℋ 𝒢 Pa : ℕ → MeasurableSpace Ω}
    {Y q : ℕ → Ω → ℂ} (hℋ : ∀ j, ℋ j ≤ mΩ) (hPa : ∀ j, Pa j ≤ mΩ) (hℋPa : ∀ j, ℋ (j + 1) ≤ Pa j)
    (h𝒢Pa : ∀ j, 𝒢 j ≤ Pa j) (h𝒢 : Monotone 𝒢)
    (hY : ∀ j, StronglyMeasurable[𝒢 (j + 1)] (Y j)) (hYb : ∀ j ω, ‖Y j ω‖ ≤ 1)
    (hq : ∀ j, StronglyMeasurable[ℋ (j + 1)] (q j)) (hqb : ∀ j ω, ‖q j ω‖ ≤ 1)
    (hPF1 : ∀ j, P[Y j | Pa j] =ᵐ[P] q j)
    (hfreeze : ∀ j (Z : Ω → ℂ), StronglyMeasurable[𝒢 j] Z → (∀ ω, ‖Z ω‖ ≤ 1) →
      P[Z | ℋ (j + 1)] =ᵐ[P] P[Z | ℋ j]) (n : ℕ) :
    P[fun ω => ∏ j ∈ Finset.range n, Y j ω | ℋ n] =ᵐ[P] fun ω => ∏ j ∈ Finset.range n, q j ω := by
  -- the partial products are measurable from the germ at the last birth
  have hprod : ∀ n, StronglyMeasurable[𝒢 n] fun ω => ∏ j ∈ Finset.range n, Y j ω := by
    intro n
    have h := Finset.stronglyMeasurable_prod (Finset.range n) fun j hj =>
      (hY j).mono (h𝒢 (Nat.succ_le_of_lt (Finset.mem_range.1 hj)))
    convert h using 1
    funext ω
    rw [Finset.prod_apply]
  have hprodb : ∀ n ω, ‖∏ j ∈ Finset.range n, Y j ω‖ ≤ 1 := fun n ω =>
    norm_prod_le_of_norm_le_one _ (fun j => Y j ω) fun j => hYb j ω
  have hint : ∀ (m : MeasurableSpace Ω) (f : Ω → ℂ), m ≤ mΩ → StronglyMeasurable[m] f →
      (∀ ω, ‖f ω‖ ≤ 1) → Integrable f P := fun m f hm hf hb =>
    Integrable.of_bound (hf.mono hm).aestronglyMeasurable 1 (Eventually.of_forall hb)
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.prod_empty]
    rw [condExp_const (hℋ 0) (1 : ℂ)]
  | succ n ih =>
    set Qn : Ω → ℂ := fun ω => ∏ j ∈ Finset.range n, Y j ω with hQn
    have hQs : StronglyMeasurable[𝒢 n] Qn := hprod n
    have hQi : Integrable Qn P := hint _ _ ((h𝒢Pa n).trans (hPa n)) hQs (hprodb n)
    have hYi : Integrable (Y n) P :=
      hint _ _ ((h𝒢Pa (n + 1)).trans (hPa (n + 1))) (hY n) (hYb n)
    have hqi : Integrable (q n) P := hint _ _ ((hℋPa n).trans (hPa n)) (hq n) (hqb n)
    have hQY : Integrable (Qn * Y n) P :=
      Integrable.of_bound (hQi.aestronglyMeasurable.mul hYi.aestronglyMeasurable) 1
        (Eventually.of_forall fun ω => by
          rw [Pi.mul_apply, norm_mul]
          nlinarith [hprodb n ω, hYb n ω, norm_nonneg (Qn ω), norm_nonneg (Y n ω)])
    have hQq : Integrable (Qn * q n) P :=
      Integrable.of_bound (hQi.aestronglyMeasurable.mul hqi.aestronglyMeasurable) 1
        (Eventually.of_forall fun ω => by
          rw [Pi.mul_apply, norm_mul]
          nlinarith [hprodb n ω, hqb n ω, norm_nonneg (Qn ω), norm_nonneg (q n ω)])
    have heq : (fun ω => ∏ j ∈ Finset.range (n + 1), Y j ω) = Qn * Y n := by
      funext ω; simp only [hQn, Pi.mul_apply, Finset.prod_range_succ]
    rw [heq]
    calc P[Qn * Y n | ℋ (n + 1)]
        =ᵐ[P] P[P[Qn * Y n | Pa n] | ℋ (n + 1)] := (condExp_condExp_of_le (hℋPa n) (hPa n)).symm
      _ =ᵐ[P] P[Qn * q n | ℋ (n + 1)] := by
          refine condExp_congr_ae ?_
          refine (condExp_mul_of_aestronglyMeasurable_left_complex
            (hQs.mono (h𝒢Pa n)).aestronglyMeasurable hQY hYi).trans ?_
          filter_upwards [hPF1 n] with ω hω
          simp only [Pi.mul_apply, hω]
      _ =ᵐ[P] P[Qn | ℋ (n + 1)] * q n :=
          condExp_mul_of_aestronglyMeasurable_right_complex (hq n).aestronglyMeasurable hQq hQi
      _ =ᵐ[P] P[Qn | ℋ n] * q n := by
          filter_upwards [hfreeze n Qn hQs (hprodb n)] with ω hω
          simp only [Pi.mul_apply, hω]
      _ =ᵐ[P] fun ω => ∏ j ∈ Finset.range (n + 1), q j ω := by
          filter_upwards [ih] with ω hω
          simp only [Pi.mul_apply, hω, Finset.prod_range_succ]

/-- **(PF4): the active field.** If, conditionally on the full germ `𝒢t` at the horizon, the active-field
observable `Z` has kernel expectation `qact` measurable from the recorded history `ℋt ≤ 𝒢t` (hypothesis (iv)
of Aux. lemma 49), and the pocket observables `Y` (`𝒢t`-measurable) have `E[Y | ℋt] = q` (PF3), then
`E[Z Y | ℋt] = qact q`. -/
theorem condExp_mul_prod_eq_of_active [IsFiniteMeasure P] {ℋt 𝒢t : MeasurableSpace Ω}
    (hℋ𝒢 : ℋt ≤ 𝒢t) (h𝒢 : 𝒢t ≤ mΩ) {Z Y qact q : Ω → ℂ} (hZ : AEStronglyMeasurable[mΩ] Z P)
    (hZb : ∀ ω, ‖Z ω‖ ≤ 1) (hY : StronglyMeasurable[𝒢t] Y) (hYb : ∀ ω, ‖Y ω‖ ≤ 1)
    (hqact : StronglyMeasurable[ℋt] qact) (hqactb : ∀ ω, ‖qact ω‖ ≤ 1)
    (hZk : P[Z | 𝒢t] =ᵐ[P] qact) (hYk : P[Y | ℋt] =ᵐ[P] q) :
    P[Z * Y | ℋt] =ᵐ[P] qact * q := by
  have hYi : Integrable Y P :=
    Integrable.of_bound (hY.mono h𝒢).aestronglyMeasurable 1 (Eventually.of_forall hYb)
  have hZi : Integrable Z P := Integrable.of_bound hZ 1 (Eventually.of_forall hZb)
  have hqi : Integrable qact P :=
    Integrable.of_bound (hqact.mono (hℋ𝒢.trans h𝒢)).aestronglyMeasurable 1
      (Eventually.of_forall hqactb)
  have hb : ∀ (f g : Ω → ℂ), AEStronglyMeasurable[mΩ] f P → AEStronglyMeasurable[mΩ] g P →
      (∀ ω, ‖f ω‖ ≤ 1) → (∀ ω, ‖g ω‖ ≤ 1) → Integrable (f * g) P := fun f g hf hg hfb hgb =>
    Integrable.of_bound (hf.mul hg) 1 (Eventually.of_forall fun ω => by
      rw [Pi.mul_apply, norm_mul]
      nlinarith [hfb ω, hgb ω, norm_nonneg (f ω), norm_nonneg (g ω)])
  calc P[Z * Y | ℋt]
      =ᵐ[P] P[P[Z * Y | 𝒢t] | ℋt] := (condExp_condExp_of_le hℋ𝒢 h𝒢).symm
    _ =ᵐ[P] P[qact * Y | ℋt] := by
        refine condExp_congr_ae ?_
        refine (condExp_mul_of_aestronglyMeasurable_right_complex hY.aestronglyMeasurable
          (hb Z Y hZ hYi.aestronglyMeasurable hZb hYb) hZi).trans ?_
        filter_upwards [hZk] with ω hω
        simp only [Pi.mul_apply, hω]
    _ =ᵐ[P] qact * P[Y | ℋt] :=
        condExp_mul_of_aestronglyMeasurable_left_complex hqact.aestronglyMeasurable
          (hb qact Y hqi.aestronglyMeasurable hYi.aestronglyMeasurable hqactb hYb) hYi
    _ =ᵐ[P] qact * q := by
        filter_upwards [hYk] with ω hω
        simp only [Pi.mul_apply, hω]

end Sec7

end InteractingSLE
