import QuantumZipper.Proofs.Zipper.E4LimMain

/-!
# E4-MC tool: a Dynkin (π-λ) argument for identities of iterated lower integrals

`handoff/E4.md`, item E4 (monotone class). The identity `∫⁻ ω ∫⁻_S F dν_ω dP = ∫⁻ ω ∫⁻_S G dν_ω dP`
for set-indexed integrands `F C, G C` (`C ⊆ E` measurable, values in `[0,1]`, additive in `C`)
propagates from a generating π-system to all measurable `C` (`goodEq_of_pi`), **provided the
a.e.-measurability of the integrands is tracked** (`GoodEq` = identity ∧ `GoodPair`): lower
integrals of non-measurable functions are neither additive nor subtractive. Complements use the
finiteness `∫⁻ ω, ν_ω S dP < ∞` (Z-FIN); disjoint unions use `lintegral_tsum`.

Standard Dynkin π-λ theorem (mathlib `MeasurableSpace.induction_on_inter`); own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped ENNReal

namespace QuantumZipper
namespace E4Grid

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ν : Ω → Measure ℝ} {S : Set ℝ}

/-- The identity together with the a.e.-measurability of both sides. -/
def GoodEq (P : Measure Ω) (ν : Ω → Measure ℝ) (S : Set ℝ) (F G : Ω → ℝ → ℝ≥0∞) : Prop :=
  (∫⁻ ω, ∫⁻ x in S, F ω x ∂ν ω ∂P = ∫⁻ ω, ∫⁻ x in S, G ω x ∂ν ω ∂P) ∧ GoodPair P ν S F G

theorem setLIntegral_le_of_le_one {μ : Measure ℝ} {a : ℝ → ℝ≥0∞} (h : ∀ x, a x ≤ 1) :
    ∫⁻ x in S, a x ∂μ ≤ μ S :=
  (lintegral_mono h).trans_eq (by rw [lintegral_one, Measure.restrict_apply_univ])

/-- One side, differences. -/
theorem side_sub (hfin : ∀ ω, ν ω S < ⊤) (hint : ∫⁻ ω, ν ω S ∂P ≠ ⊤)
    {a b : Ω → ℝ → ℝ≥0∞} (hba : ∀ ω x, b ω x ≤ a ω x) (ha1 : ∀ ω x, a ω x ≤ 1)
    (ha : AEMeasurable (fun ω => ∫⁻ x in S, a ω x ∂ν ω) P)
    (hb : AEMeasurable (fun ω => ∫⁻ x in S, b ω x ∂ν ω) P)
    (hai : ∀ᵐ ω ∂P, AEMeasurable (a ω) ((ν ω).restrict S))
    (hbi : ∀ᵐ ω ∂P, AEMeasurable (b ω) ((ν ω).restrict S)) :
    (∫⁻ ω, ∫⁻ x in S, (a ω x - b ω x) ∂ν ω ∂P =
      ∫⁻ ω, ∫⁻ x in S, a ω x ∂ν ω ∂P - ∫⁻ ω, ∫⁻ x in S, b ω x ∂ν ω ∂P) ∧
    AEMeasurable (fun ω => ∫⁻ x in S, (a ω x - b ω x) ∂ν ω) P ∧
    ∀ᵐ ω ∂P, AEMeasurable (fun x => a ω x - b ω x) ((ν ω).restrict S) := by
  have hbS : ∀ ω, ∫⁻ x in S, b ω x ∂ν ω ≤ ν ω S := fun ω =>
    setLIntegral_le_of_le_one fun x => (hba ω x).trans (ha1 ω x)
  have hinner : ∀ᵐ ω ∂P, ∫⁻ x in S, (a ω x - b ω x) ∂ν ω =
      ∫⁻ x in S, a ω x ∂ν ω - ∫⁻ x in S, b ω x ∂ν ω := by
    filter_upwards [hbi] with ω hb'
    exact lintegral_sub' hb' (ne_top_of_le_ne_top (hfin ω).ne (hbS ω))
      (Eventually.of_forall (hba ω))
  refine ⟨?_, (ha.sub hb).congr (hinner.mono fun ω h => h.symm), ?_⟩
  · rw [lintegral_congr_ae hinner]
    exact lintegral_sub' hb (ne_top_of_le_ne_top hint (lintegral_mono hbS))
      (Eventually.of_forall fun ω => lintegral_mono (hba ω))
  · filter_upwards [hai, hbi] with ω h1 h2
    exact h1.sub h2

/-- One side, countable sums. -/
theorem side_tsum {a : ℕ → Ω → ℝ → ℝ≥0∞}
    (ha : ∀ i, AEMeasurable (fun ω => ∫⁻ x in S, a i ω x ∂ν ω) P)
    (hai : ∀ i, ∀ᵐ ω ∂P, AEMeasurable (a i ω) ((ν ω).restrict S)) :
    (∫⁻ ω, ∫⁻ x in S, ∑' i, a i ω x ∂ν ω ∂P = ∑' i, ∫⁻ ω, ∫⁻ x in S, a i ω x ∂ν ω ∂P) ∧
    AEMeasurable (fun ω => ∫⁻ x in S, ∑' i, a i ω x ∂ν ω) P ∧
    ∀ᵐ ω ∂P, AEMeasurable (fun x => ∑' i, a i ω x) ((ν ω).restrict S) := by
  have hinner : ∀ᵐ ω ∂P, ∫⁻ x in S, ∑' i, a i ω x ∂ν ω = ∑' i, ∫⁻ x in S, a i ω x ∂ν ω := by
    filter_upwards [ae_all_iff.2 hai] with ω h
    exact lintegral_tsum h
  refine ⟨?_, (AEMeasurable.ennreal_tsum ha).congr (hinner.mono fun ω h => h.symm), ?_⟩
  · rw [lintegral_congr_ae hinner, lintegral_tsum ha]
  · filter_upwards [ae_all_iff.2 hai] with ω h
    exact AEMeasurable.ennreal_tsum h

/-- **Dynkin step.** `GoodEq` for set-indexed `[0,1]`-valued additive integrands propagates from
a generating π-system (and `univ`) to all measurable sets. -/
theorem goodEq_of_pi {E : Type*} [mE : MeasurableSpace E] (hfin : ∀ ω, ν ω S < ⊤)
    (hint : ∫⁻ ω, ν ω S ∂P ≠ ⊤) (F G : Set E → Ω → ℝ → ℝ≥0∞)
    (hF1 : ∀ C ω x, F C ω x ≤ 1) (hG1 : ∀ C ω x, G C ω x ≤ 1)
    (hF0 : ∀ ω x, F ∅ ω x = 0) (hG0 : ∀ ω x, G ∅ ω x = 0)
    (hFle : ∀ C, MeasurableSet C → ∀ ω x, F C ω x ≤ F univ ω x)
    (hGle : ∀ C, MeasurableSet C → ∀ ω x, G C ω x ≤ G univ ω x)
    (hFc : ∀ C, MeasurableSet C → ∀ ω x, F Cᶜ ω x = F univ ω x - F C ω x)
    (hGc : ∀ C, MeasurableSet C → ∀ ω x, G Cᶜ ω x = G univ ω x - G C ω x)
    (hFu : ∀ f : ℕ → Set E, Pairwise (Disjoint on f) → (∀ i, MeasurableSet (f i)) →
      ∀ ω x, F (⋃ i, f i) ω x = ∑' i, F (f i) ω x)
    (hGu : ∀ f : ℕ → Set E, Pairwise (Disjoint on f) → (∀ i, MeasurableSet (f i)) →
      ∀ ω x, G (⋃ i, f i) ω x = ∑' i, G (f i) ω x)
    {𝒢 : Set (Set E)} (hgen : mE = MeasurableSpace.generateFrom 𝒢) (hπ : IsPiSystem 𝒢)
    (huniv : GoodEq P ν S (F univ) (G univ)) (hbasic : ∀ C ∈ 𝒢, GoodEq P ν S (F C) (G C)) :
    ∀ C, MeasurableSet C → GoodEq P ν S (F C) (G C) := by
  refine MeasurableSpace.induction_on_inter (C := fun C _ => GoodEq P ν S (F C) (G C)) hgen hπ
    ?_ (fun t ht => hbasic t ht) ?_ ?_
  · have h1 : F ∅ = fun _ _ => 0 := funext₂ hF0
    have h2 : G ∅ = fun _ _ => 0 := funext₂ hG0
    simp only [h1, h2]
    refine ⟨rfl, ?_, ?_, ?_, ?_⟩ <;> simp
  · intro t htm ⟨heq, hLo, hLi, hRo, hRi⟩
    obtain ⟨hU, hULo, hULi, hURo, hURi⟩ := huniv
    have h1 : F tᶜ = fun ω x => F univ ω x - F t ω x := funext₂ (hFc t htm)
    have h2 : G tᶜ = fun ω x => G univ ω x - G t ω x := funext₂ (hGc t htm)
    obtain ⟨eL, mLo, mLi⟩ := side_sub hfin hint (hFle t htm) (hF1 univ) hULo hLo hULi hLi
    obtain ⟨eR, mRo, mRi⟩ := side_sub hfin hint (hGle t htm) (hG1 univ) hURo hRo hURi hRi
    rw [h1, h2]
    exact ⟨by rw [eL, eR, hU, heq], mLo, mLi, mRo, mRi⟩
  · intro f hd hfm hf
    have h1 : F (⋃ i, f i) = fun ω x => ∑' i, F (f i) ω x := funext₂ (hFu f hd hfm)
    have h2 : G (⋃ i, f i) = fun ω x => ∑' i, G (f i) ω x := funext₂ (hGu f hd hfm)
    obtain ⟨eL, mLo, mLi⟩ := side_tsum (fun i => (hf i).2.1) (fun i => (hf i).2.2.1)
    obtain ⟨eR, mRo, mRi⟩ := side_tsum (fun i => (hf i).2.2.2.1) (fun i => (hf i).2.2.2.2)
    rw [h1, h2]
    exact ⟨by rw [eL, eR]; exact tsum_congr fun i => (hf i).1, mLo, mLi, mRo, mRi⟩

end E4Grid
end QuantumZipper
