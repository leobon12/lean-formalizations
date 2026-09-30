import QuantumZipper.Proofs.Section5.Prop16ActRegBasic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Proposition 1.6, node B′-MOM: law transfer of boundary masses between mixed GFFs

* `lintegral_eq_of_isMixedGFF_bdryMom`: a measurable `[0,∞]`-valued functional of the field that
  only reads a countable admissible family has the same expectation under any two mixed GFFs
  (same `D`, `S`). The family laws agree (`locGood_map_eq_of_isMixedGFF`, Gaussian f.d.d.); the
  functional factors through the family via a measurable "projection" of the field.
* `bdryApprox_congr_bdryMom`: `bdryApprox γ (h0 + x) k K` reads `x` only on the eventual dyadic
  circles `foldedCircle (dyadicRoundC j s) (radius k)`, `s ∈ K` (`avgReg` is a `limUnder`, which
  only depends on the tail of the sequence).

Own elementary arguments (bookkeeping for the transfer step of the proof of Prop. 1.6,
Sheffield arXiv:1012.4797 p. 25).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

namespace QuantumZipper

namespace Prop16Asm

/-- **Law transfer along a countable admissible family.** -/
theorem lintegral_eq_of_isMixedGFF_bdryMom {Ω Ω₀ : Type} [MeasurableSpace Ω]
    [MeasurableSpace Ω₀] {P : Measure Ω} {P₀ : Measure Ω₀} [IsProbabilityMeasure P]
    [IsProbabilityMeasure P₀] {D S : Set ℂ} {X : Ω → FieldSample} {Y : Ω₀ → FieldSample}
    (hX : IsMixedGFF D S X P) (hY : IsMixedGFF D S Y P₀) (A : Set (Measure ℂ))
    (hA : A.Countable) (hAadm : ∀ μ ∈ A, IsAdmissibleDual D (mixedSpace D S) μ)
    {F : FieldSample → ℝ≥0∞} (hF : Measurable F)
    (hFA : ∀ x x' : FieldSample, (∀ μ ∈ A, x μ = x' μ) → F x = F x') :
    ∫⁻ ω, F (X ω) ∂P = ∫⁻ ω, F (Y ω) ∂P₀ := by
  classical
  rcases A.eq_empty_or_nonempty with hAe | hAne
  · have hc : ∀ x, F x = F 0 := fun x => hFA x 0 (by simp [hAe])
    simp only [hc, lintegral_const, measure_univ]
  obtain ⟨m, hm⟩ := hA.exists_eq_range hAne
  have hmA : ∀ i, m i ∈ A := fun i => hm ▸ mem_range_self i
  have hmadm : ∀ i, IsAdmissibleDual D (mixedSpace D S) (m i) := fun i => hAadm _ (hmA i)
  -- an index for every member of `A`
  have hidx : ∀ μ ∈ A, ∃ i, m i = μ := fun μ hμ => by rw [hm] at hμ; exact hμ
  set Ψ : (ℕ → ℝ) → FieldSample := fun y μ =>
    if h : μ ∈ A then y (Classical.choose (hidx μ h)) else 0 with hΨ
  have hΨm : Measurable Ψ := by
    refine measurable_pi_iff.2 fun μ => ?_
    by_cases h : μ ∈ A
    · simp only [hΨ, dif_pos h]; exact measurable_pi_apply _
    · simp only [hΨ, dif_neg h]; exact measurable_const
  set fam : FieldSample → (ℕ → ℝ) := fun x i => x (m i) with hfam
  have hFΨ : ∀ x, F (Ψ (fam x)) = F x := fun x => by
    refine hFA _ _ fun μ hμ => ?_
    simp only [hΨ, hfam, dif_pos hμ]
    rw [Classical.choose_spec (hidx μ hμ)]
  have hXm : Measurable fun ω i => X ω (m i) :=
    measurable_pi_iff.2 fun i => hX.measurable_coord _
  have hYm : Measurable fun ω i => Y ω (m i) :=
    measurable_pi_iff.2 fun i => hY.measurable_coord _
  have hlaw := locGood_map_eq_of_isMixedGFF hX hY m hmadm
  calc ∫⁻ ω, F (X ω) ∂P = ∫⁻ ω, F (Ψ (fun i => X ω (m i))) ∂P :=
        lintegral_congr fun ω => (hFΨ (X ω)).symm
    _ = ∫⁻ y, F (Ψ y) ∂(P.map fun ω i => X ω (m i)) :=
        (lintegral_map (hF.comp hΨm) hXm).symm
    _ = ∫⁻ y, F (Ψ y) ∂(P₀.map fun ω i => Y ω (m i)) := by rw [hlaw]
    _ = ∫⁻ ω, F (Ψ (fun i => Y ω (m i))) ∂P₀ := lintegral_map (hF.comp hΨm) hYm
    _ = ∫⁻ ω, F (Y ω) ∂P₀ := lintegral_congr fun ω => hFΨ (Y ω)

/-- `avgReg` only reads the eventual dyadic circles. -/
theorem avgReg_congr_bdryMom {k : ℕ} {z : ℂ} {x x' : FieldSample}
    (h : ∀ᶠ j in atTop, x (foldedCircle (dyadicRoundC j z) (radius k)) =
      x' (foldedCircle (dyadicRoundC j z) (radius k))) :
    avgReg x k z = avgReg x' k z := by
  unfold avgReg limUnder
  rw [Filter.map_congr h]

/-- **`bdryApprox` of `h0 + x` on `K` reads `x` only on the eventual dyadic circles about `K`.** -/
theorem bdryApprox_congr_bdryMom (γ : ℝ) (h0 : ℂ → ℝ) (k : ℕ) {K : Set ℝ}
    (hK : MeasurableSet K) {Cs : Set ℂ}
    (hC : ∀ s ∈ K, ∀ᶠ j in Filter.atTop, dyadicRoundC j (s : ℂ) ∈ Cs) {x x' : FieldSample}
    (hxx : ∀ c ∈ Cs, x (foldedCircle c (radius k)) = x' (foldedCircle c (radius k))) :
    bdryApprox γ (ofFun h0 + x) k K = bdryApprox γ (ofFun h0 + x') k K := by
  unfold bdryApprox
  rw [withDensity_apply _ hK, withDensity_apply _ hK]
  refine setLIntegral_congr_fun hK fun s hs => ?_
  rw [avgReg_congr_bdryMom (x' := ofFun h0 + x') ((hC s hs).mono fun j hj => ?_)]
  simp only [Pi.add_apply, hxx _ hj]

end Prop16Asm

end QuantumZipper
