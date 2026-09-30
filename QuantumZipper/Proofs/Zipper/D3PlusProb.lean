import QuantumZipper.Proofs.Zipper.D3PlusIII

/-!
# D3⁺(iii) in probability (the form consumed by E5a)

`LengthMarkov.GermDensity.germDensity` / `E5.germDensity_withDensity` (E5 step (4)) take the zoom
scales `a_n` with `P {ε ≤ a_n} → 0`. `D3Plus.d3PlusIII_holds` gives the almost-sure form; this file
converts it (own elementary argument: `P (A n) ≤ P (⋃_{m ≥ n} A m) → P (limsup A) = 0`).
Measurability of the events is an explicit hypothesis (it is needed: for non-measurable events the
outer measure need not go to `0`); E5 has to supply the measurability of its scale anyway
(`ha` of `germDensity`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace D3Plus

/-- Almost-sure eventual avoidance of null-measurable events gives convergence of their
probabilities to `0`. -/
theorem tendsto_measure_of_ae_eventually_notMem {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {A : ℕ → Set Ω} (hA : ∀ n, NullMeasurableSet (A n) P)
    (h : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∉ A n) :
    Tendsto (fun n => P (A n)) atTop (𝓝 0) := by
  set B : ℕ → Set Ω := fun n => ⋃ m, ⋃ (_ : n ≤ m), A m with hBdef
  have hB : ∀ n, NullMeasurableSet (B n) P := fun n =>
    NullMeasurableSet.iUnion fun m => NullMeasurableSet.iUnion fun _ => hA m
  have hanti : Antitone B := fun n n' hnn' ω hω => by
    simp only [hBdef, mem_iUnion] at hω ⊢
    obtain ⟨m, hm, hωm⟩ := hω
    exact ⟨m, hnn'.trans hm, hωm⟩
  have hlim := tendsto_measure_iInter_atTop hB hanti ⟨0, measure_ne_top _ _⟩
  have h0 : P (⋂ n, B n) = 0 := by
    refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 h)
    show ¬ _
    intro hev
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev
    have := mem_iInter.1 hω N
    simp only [hBdef, mem_iUnion] at this
    obtain ⟨m, hm, hωm⟩ := this
    exact hN m hm hωm
  rw [h0] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => bot_le)
    fun n => measure_mono ?_
  intro ω hω
  simp only [hBdef, mem_iUnion]
  exact ⟨n, le_rfl, hω⟩

/-- **D3⁺(iii) in probability.** Along any levels `L_n → ∞`, the probability that the local scale
of the model field is not in `(0, ε)` tends to `0` (given measurability of these events). -/
theorem d3PlusIII_tendsto_prob {γ α r : ℝ} {ρ₀ : Measure ℂ} {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → FieldSample} {E' : Type}
    [MeasurableSpace E'] {Ξ : Ω → E'} {g : Ω → ℂ → ℝ} (hS : Setup γ α r ρ₀ P X Ξ g)
    {Ls : ℕ → ℝ} (hLs : Tendsto Ls atTop atTop) {ε : ℝ} (hε : 0 < ε)
    (hmeas : ∀ n, NullMeasurableSet {ω | ¬ (0 < scaleParamOn γ (zoomModel γ α (Ls n) ρ₀ (X ω) (g ω))
      (halfDisc r) ∧ scaleParamOn γ (zoomModel γ α (Ls n) ρ₀ (X ω) (g ω)) (halfDisc r) < ε)} P) :
    Tendsto (fun n => P {ω | ¬ (0 < scaleParamOn γ (zoomModel γ α (Ls n) ρ₀ (X ω) (g ω))
      (halfDisc r) ∧ scaleParamOn γ (zoomModel γ α (Ls n) ρ₀ (X ω) (g ω)) (halfDisc r) < ε)})
      atTop (𝓝 0) := by
  refine tendsto_measure_of_ae_eventually_notMem hmeas ?_
  filter_upwards [d3PlusIII_holds γ α r ρ₀ P X Ξ g hS] with ω hω
  filter_upwards [hLs.eventually (hω ε hε)] with n hn
  exact fun h => h hn

end D3Plus
end QuantumZipper
