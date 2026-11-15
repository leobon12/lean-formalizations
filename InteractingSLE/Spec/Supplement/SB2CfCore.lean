/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NzDrv
import InteractingSLE.Spec.Supplement.SB2CfMeas

/-!
# A record read off a random index, known to increasing marks: the abstract version step

Packet PROVE-SB2-CONDFIN (Target 1, steps 3–4 of the root-record route). Let `EL0` be a measurable, everywhere regular
driver, `off` a random index and `A n` measurable events such that, under the regular conditional laws given `𝓜 n`,
the event `A n` and, on it, the record of `EL0` are frozen, while off `A (off ω)` the driver is `zeroDrv`. Then
there are regular drivers `Dr₀ n`, measurable for `𝓜 n`, with the record of `EL0` equal almost surely to that of
`Dr₀ (off ω)` (**`exists_rootRec_of_frozen`**): mask the record by `A n`, take its `𝓜 n`-measurable version
(`Nz.exists_version_of_frozen_rec`) and read the regular driver off it (`Nz.recDrv`, `Nz.recOf_recDrv`).

Standard (no input).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB.Cf

open Exist Exist.Staged Exist.StagedLaw

/-- **The abstract version step**: a frozen masked record has regular versions known to the marks. -/
theorem exists_rootRec_of_frozen {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] {Q : Measure Ω}
    [IsProbabilityMeasure Q] {𝓜 : ℕ → MeasurableSpace Ω} {EL0 : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (hELm : Measurable EL0)
    (hELr : ∀ ω, IsRegularDriver (EL0 ω)) {off : Ω → ℕ} {A : ℕ → Set Ω} (hA : ∀ n, MeasurableSet (A n))
    (hfr : ∀ n, ∀ᵐ ω₁ ∂Q, ∀ᵐ ω ∂(condExpKernel Q (𝓜 n) ω₁),
      (ω ∈ A n ↔ ω₁ ∈ A n) ∧ (ω₁ ∈ A n → recOf ⊤ (EL0 ω) = recOf ⊤ (EL0 ω₁)))
    (hoff : ∀ᵐ ω ∂Q, ω ∉ A (off ω) → EL0 ω = Lk.zeroDrv)
    (hc : ∀ᵐ ω ∂Q, ContinuousOn (EL0 ω).1 {s | (s : ℝ≥0∞) ≤ min ⊤ (EL0 ω).2}) :
    ∃ Dr₀ : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞, (∀ n, Measurable[𝓜 n] (Dr₀ n)) ∧ (∀ n ω, IsRegularDriver (Dr₀ n ω)) ∧
      ∀ᵐ ω ∂Q, recOf ⊤ (EL0 ω) = recOf ⊤ (Dr₀ (off ω) ω) := by
  classical
  set f : ℕ → Ω → RecData := fun n ω => if ω ∈ A n then recOf ⊤ (EL0 ω) else recOf ⊤ Lk.zeroDrv with hf
  have hfm : ∀ n, Measurable (f n) := fun n =>
    Measurable.ite (hA n) (measurable_recOf hELm hELr ⊤) measurable_const
  have hfz : ∀ n, ∀ᵐ ω₁ ∂Q, ∀ᵐ ω ∂(condExpKernel Q (𝓜 n) ω₁), f n ω = f n ω₁ := by
    intro n
    filter_upwards [hfr n] with ω₁ h₁
    filter_upwards [h₁] with ω ⟨hiff, hrec⟩
    by_cases hω₁ : ω₁ ∈ A n
    · have hω : ω ∈ A n := hiff.2 hω₁
      simp only [hf, hω, hω₁, ↓reduceIte]
      exact hrec hω₁
    · have hω : ω ∉ A n := fun h => hω₁ (hiff.1 h)
      simp only [hf, hω, hω₁, ↓reduceIte]
  have hver : ∀ n, ∃ g : Ω → RecData, Measurable[𝓜 n] g ∧ f n =ᵐ[Q] g := fun n =>
    Nz.exists_version_of_frozen_rec (hfm n) (hfz n)
  choose g hgm hge using hver
  refine ⟨fun n ω => Nz.recDrv (g n ω), fun n => Nz.measurable_recDrv.comp (hgm n),
    fun n ω => Nz.isRegularDriver_recDrv _, ?_⟩
  filter_upwards [ae_all_iff.2 hge, hoff, hc] with ω hω hoffω hcω
  have hfo : f (off ω) ω = recOf ⊤ (EL0 ω) := by
    by_cases hA' : ω ∈ A (off ω)
    · simp only [hf, hA', ↓reduceIte]
    · simp only [hf, hA', ↓reduceIte, hoffω hA']
  show recOf ⊤ (EL0 ω) = recOf ⊤ (Nz.recDrv (g (off ω) ω))
  rw [← hω (off ω), hfo, Nz.recOf_recDrv (hELr ω) hcω]

end InteractingSLE.Theorem14.SB.Cf
