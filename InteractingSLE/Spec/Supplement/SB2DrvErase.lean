/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2DrvIter
import InteractingSLE.Spec.Sec7.TwoForceMainKernel

/-!
# Erasure: extra marks that add nothing on an event of the smaller σ-algebra

Packet PROVE-T14-SB2DRV (round 3), the conditional-expectation core of clause (E2) (supplement p. 632: "even the full
erased history, its entry germ and stopping flags leave the same conditional field in `D_A`"). Generic facts:

* **`ae_condExp_eq_of_le_of_sup`**: for `𝒢 ≤ 𝓜 ≤ 𝓚` and an event `S ∈ 𝒢`, if `E[X | 𝓚] = E[X | 𝒢]` a.s. on `S`, then
  `E[X | 𝓜] = E[X | 𝒢]` a.s. on `S` (tower property; `𝓚` will be the germs of the union with its marks);
* **`ae_condExp_iSup_eq_of_forall`**: if `E[X | 𝓜 n] = E[X | 𝒢]` a.s. on `S` for every member of an increasing family,
  the same holds for `⨆ n, 𝓜 n` (Lévy's upward theorem, `Sec7.condExp_iSup_eq_on_iUnion`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB.Lv

variable {Ω : Type*} {𝒢 𝓜 𝓚 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]

/-- **Extra marks that add nothing at the top add nothing in between.** -/
theorem ae_condExp_eq_of_le_of_sup (h𝒢𝓜 : 𝒢 ≤ 𝓜) (h𝓜𝓚 : 𝓜 ≤ 𝓚) (h𝓚 : 𝓚 ≤ mΩ) {S : Set Ω}
    (hS : MeasurableSet[𝒢] S) {X : Ω → ℂ} (hX : Integrable X P)
    (htop : ∀ᵐ ω ∂P, ω ∈ S → P[X | 𝓚] ω = P[X | 𝒢] ω) :
    ∀ᵐ ω ∂P, ω ∈ S → P[X | 𝓜] ω = P[X | 𝒢] ω := by
  have h𝓜 : 𝓜 ≤ mΩ := h𝓜𝓚.trans h𝓚
  have h𝒢 : 𝒢 ≤ mΩ := h𝒢𝓜.trans h𝓜
  have hS𝓜 : MeasurableSet[𝓜] S := h𝒢𝓜 _ hS
  have hS𝓚 : MeasurableSet[𝓚] S := h𝓜𝓚 _ hS𝓜
  have h1 : P[S.indicator X | 𝓜] =ᵐ[P] S.indicator (P[X | 𝓜]) := condExp_indicator hX hS𝓜
  have h2 : P[P[S.indicator X | 𝓚] | 𝓜] =ᵐ[P] P[S.indicator X | 𝓜] := condExp_condExp_of_le h𝓜𝓚 h𝓚
  have h3 : P[S.indicator X | 𝓚] =ᵐ[P] S.indicator (P[X | 𝓚]) := condExp_indicator hX hS𝓚
  have h4 : S.indicator (P[X | 𝓚]) =ᵐ[P] S.indicator (P[X | 𝒢]) := by
    filter_upwards [htop] with ω hω
    by_cases hωS : ω ∈ S
    · rw [indicator_of_mem hωS, indicator_of_mem hωS, hω hωS]
    · rw [indicator_of_notMem hωS, indicator_of_notMem hωS]
  have hsm : StronglyMeasurable[𝓜] (S.indicator (P[X | 𝒢])) :=
    ((stronglyMeasurable_condExp (m := 𝒢)).mono h𝒢𝓜).indicator hS𝓜
  have hint : Integrable (S.indicator (P[X | 𝒢])) P := integrable_condExp.indicator (h𝒢 _ hS)
  have h5 : P[S.indicator (P[X | 𝒢]) | 𝓜] = S.indicator (P[X | 𝒢]) :=
    condExp_of_stronglyMeasurable h𝓜 hsm hint
  have key : S.indicator (P[X | 𝓜]) =ᵐ[P] S.indicator (P[X | 𝒢]) := by
    refine h1.symm.trans (h2.symm.trans ?_)
    refine (condExp_congr_ae (h3.trans h4)).trans ?_
    rw [h5]
  filter_upwards [key] with ω hω hωS
  rwa [indicator_of_mem hωS, indicator_of_mem hωS] at hω

/-- **Passage to the supremum of an increasing family of marks.** -/
theorem ae_condExp_iSup_eq_of_forall (M : Filtration ℕ mΩ) {S : Set Ω} {X : Ω → ℂ} (hX : Integrable X P)
    (hn : ∀ n, ∀ᵐ ω ∂P, ω ∈ S → P[X | M n] ω = P[X | 𝒢] ω) :
    ∀ᵐ ω ∂P, ω ∈ S → P[X | ⨆ n, M n] ω = P[X | 𝒢] ω := by
  have h := Sec7.condExp_iSup_eq_on_iUnion (𝓖 := M) hX (E := fun _ => S) (fun _ _ _ => le_rfl)
    (Ψ := fun _ => P[X | 𝒢]) (Ψ' := P[X | 𝒢]) hn (Eventually.of_forall fun _ _ => tendsto_const_nhds)
  filter_upwards [h] with ω hω hωS
  exact hω (mem_iUnion.2 ⟨0, hωS⟩)

end InteractingSLE.Theorem14.SB.Lv
