import QuantumZipper.Proofs.Section5.Prop16DomCoupleRect

/-!
# Proposition 1.6, node DOM-COUPLE (part 7): the continuous-version sub-node, proved

`gaussContVersion_holds : GaussContVersionStmt`: for an isonormal process `W` and a curve `H`
Lipschitz on the compact subsets of `O ∩ Hbar` (`O` open), `z ↦ W(H z)` has a version with
continuous paths on `O ∩ Hbar` for every `ω` and measurable coordinates.

Proof (Kolmogorov's criterion, Revuz–Yor Ch. I Thm (2.1), localised; the localisation is an own
elementary argument): for each rational rectangle `R ⊆ O ∩ Hbar` apply the global version
`isoW_contVersion_global` to `H ∘ clamp_R` (globally Lipschitz); on a measurable full-measure
event the countably many versions agree at the rational points of every intersection
`R ∩ R'`, hence on the whole intersection (`eq_on_inter_of_rat`); every point of `O ∩ Hbar` has a
rectangle that is a neighbourhood within `Hbar` (`exists_rectQ_nhdsWithin`); glue.

Consequences: `GaussContFubiniStmt` (DOM-b) holds, and `Prop16MixedFreeLocCouplingStmt`, hence
`theorem1_6` (with the weak TV node), follows from the Hilbert sub-node `DomMarkovCurveStmt`
(DOM-a) alone.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal

namespace QuantumZipper

namespace Prop16Asm

/-- **Sub-node DOM-b1, proved.** -/
theorem gaussContVersion_holds : GaussContVersionStmt := by
  intro E _ _ _ Ω _ P _ W O H hO hWm hW hLip
  classical
  let good : ℚ × ℚ × ℚ × ℚ → Prop := fun p =>
    (p.1 : ℝ) ≤ p.2.1 ∧ (p.2.2.1 : ℝ) ≤ p.2.2.2 ∧ (0 : ℝ) ≤ p.2.2.1 ∧ rectQ p ⊆ O
  let I := {p // good p}
  have hsubOH : ∀ p : I, rectQ p.1 ⊆ O ∩ Hbar := fun p w hw => by
    refine ⟨p.2.2.2.2 hw, ?_⟩
    have h1 := (mem_rectQ.1 hw).2.1
    have h2 : (0 : ℝ) ≤ p.1.2.2.1 := p.2.2.2.1
    show 0 ≤ w.im
    linarith
  have hLp : ∀ p : I, ∃ C : ℝ≥0, LipschitzWith C (fun w => H (clampQ p.1 w)) := by
    intro p
    obtain ⟨C, hC⟩ := hLip _ (isCompact_rectQ p.1) (hsubOH p)
    refine ⟨C * 2, LipschitzWith.of_dist_le_mul fun w w' => ?_⟩
    have h1 := hC.dist_le_mul _ (clampQ_mem p.2.1 p.2.2.1 w) _ (clampQ_mem p.2.1 p.2.2.1 w')
    have h2 := (lipschitzWith_clampQ p.1).dist_le_mul w w'
    calc dist (H (clampQ p.1 w)) (H (clampQ p.1 w')) ≤ C * dist (clampQ p.1 w) (clampQ p.1 w') := h1
      _ ≤ C * (2 * dist w w') := by gcongr; exact_mod_cast h2
      _ = ((C * 2 : ℝ≥0) : ℝ) * dist w w' := by push_cast; ring
  choose Cp hCp using hLp
  have hY : ∀ p : I, ∃ Y : Ω → ℂ → ℝ, (∀ ω, Continuous (Y ω)) ∧
      (∀ z, Measurable fun ω => Y ω z) ∧ ∀ z, (fun ω => Y ω z) =ᵐ[P] W (H (clampQ p.1 z)) :=
    fun p => isoW_contVersion_global hW hWm (hCp p)
  choose Y hYc hYm hYae using hY
  have hYae' : ∀ p : I, ∀ w ∈ rectQ p.1, (fun ω => Y p ω w) =ᵐ[P] W (H w) := fun p w hw => by
    simpa [clampQ_eq hw] using hYae p w
  let Good := {ω | ∀ (p p' : I) (r : ℚ × ℚ), (⟨r.1, r.2⟩ : ℂ) ∈ rectQ p.1 ∩ rectQ p'.1 →
    Y p ω ⟨r.1, r.2⟩ = Y p' ω ⟨r.1, r.2⟩}
  have hGood : ∀ᵐ ω ∂P, ω ∈ Good := by
    simp only [Good, Set.mem_ofPred_eq]
    rw [ae_all_iff]; intro p; rw [ae_all_iff]; intro p'; rw [ae_all_iff]; intro r
    by_cases hr : (⟨r.1, r.2⟩ : ℂ) ∈ rectQ p.1 ∩ rectQ p'.1
    · filter_upwards [hYae' p _ hr.1, hYae' p' _ hr.2] with ω h1 h2 _
      rw [h1, h2]
    · exact ae_of_all _ fun ω h => absurd h hr
  set T := (toMeasurable P Goodᶜ)ᶜ with hT
  have hTm : MeasurableSet T := (measurableSet_toMeasurable P _).compl
  have hTsub : ∀ ω ∈ T, ω ∈ Good := fun ω hω => by
    by_contra h
    exact hω (subset_toMeasurable P _ h)
  have hTae : ∀ᵐ ω ∂P, ω ∈ T := by
    have h0 : P Goodᶜ = 0 := ae_iff.1 hGood
    rw [ae_iff]
    simp only [hT, mem_compl_iff, not_not]
    rw [show {a | a ∈ toMeasurable P Goodᶜ} = toMeasurable P Goodᶜ from rfl,
      measure_toMeasurable, h0]
  have hagree : ∀ ω ∈ T, ∀ p p' : I, ∀ w ∈ rectQ p.1 ∩ rectQ p'.1, Y p ω w = Y p' ω w :=
    fun ω hω p p' w hw =>
      eq_on_inter_of_rat (hYc p ω) (hYc p' ω) (fun r hr => hTsub ω hω p p' r hr) hw
  have hch : ∀ z ∈ O ∩ Hbar, ∃ p : I, rectQ p.1 ∈ 𝓝[Hbar] z := fun z hz => by
    obtain ⟨p, h1, h2, h3, h4, h5⟩ := exists_rectQ_nhdsWithin hO hz
    exact ⟨⟨p, h1, h2, h3, h4⟩, h5⟩
  have hmemch : ∀ (z : ℂ) (hz : z ∈ O ∩ Hbar), z ∈ rectQ (Classical.choose (hch z hz)).1 :=
    fun z hz => mem_of_mem_nhdsWithin hz.2 (Classical.choose_spec (hch z hz))
  let G : Ω → ℂ → ℝ := fun ω z => if hz : z ∈ O ∩ Hbar then
    T.indicator (fun ω => Y (Classical.choose (hch z hz)) ω z) ω else 0
  refine ⟨G, fun ω => ?_, fun z => ?_, fun z hz => ?_⟩
  · by_cases hω : ω ∈ T
    · intro z hz
      set p := Classical.choose (hch z hz) with hpdef
      have hp : rectQ p.1 ∈ 𝓝[Hbar] z := Classical.choose_spec (hch z hz)
      have hev : G ω =ᶠ[𝓝[O ∩ Hbar] z] Y p ω := by
        have h1 : rectQ p.1 ∈ 𝓝[O ∩ Hbar] z := nhdsWithin_mono _ inter_subset_right hp
        filter_upwards [h1, self_mem_nhdsWithin] with w hw hwOH
        simp only [G, hwOH, ↓reduceDIte, indicator_of_mem hω]
        exact hagree ω hω _ p w ⟨hmemch w hwOH, hw⟩
      have hzG : G ω z = Y p ω z := by simp only [G, hz, ↓reduceDIte, indicator_of_mem hω, hpdef]
      exact ((hYc p ω).continuousWithinAt).congr_of_eventuallyEq hev hzG
    · have : G ω = fun _ => 0 := funext fun z => by
        by_cases hz : z ∈ O ∩ Hbar <;> simp [G, hω]
      rw [this]; exact continuousOn_const
  · by_cases hz : z ∈ O ∩ Hbar
    · simp only [G, hz, ↓reduceDIte]; exact (hYm _ z).indicator hTm
    · simp only [G, hz, ↓reduceDIte]; exact measurable_const
  · filter_upwards [hTae, hYae' (Classical.choose (hch z hz)) z (hmemch z hz)] with ω hω h
    simp only [G, hz, ↓reduceDIte, indicator_of_mem hω]
    exact h

/-- **Sub-node DOM-b, proved** (continuous version + stochastic Fubini). -/
theorem gaussContFubini_holds : GaussContFubiniStmt :=
  gaussContFubini_of_version gaussContVersion_holds

end Prop16Asm

end QuantumZipper
