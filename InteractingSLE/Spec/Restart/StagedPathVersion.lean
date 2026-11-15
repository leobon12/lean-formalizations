import InteractingSLE.Foundations.Loewner.Concat
import InteractingSLE.Spec.Supplement.LPTrace
import InteractingSLE.Spec.Sec7.StripDetPath

/-!
# Measurable continuous versions of two-piece Loewner paths

The joined path is reconstructed from the measurable driver by `LP.traceAt`. On a measurable
conull subset where it is a continuous generating trace we keep this reconstruction; elsewhere
we use the constant zero curve. No determination or stochastic SLE theorem is used.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdMapInv)
open InteractingSLE.Sec7.StripSideHeightProb

namespace InteractingSLE.Restart.StagedPathVersion

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Measurability of concatenating two path coordinates at a deterministic time. -/
theorem measurable_catPath {W₀ W₁ : Ω → ℝ≥0 → ℝ}
    (h₀ : ∀ t, Measurable (fun ω => W₀ ω t))
    (h₁ : ∀ t, Measurable (fun ω => W₁ ω t)) (a : ℝ≥0) :
    Measurable (fun ω => catPath (W₀ ω) a (W₁ ω)) :=
  (Sec7.StripDet.measurable_catPath a).comp
    ((measurable_pi_iff.2 h₀).prodMk (measurable_pi_iff.2 h₁))

/-- A measurable driver that almost surely has a continuous generating trace admits a
coordinate-measurable version of that trace continuous at every sample, starting at zero. -/
theorem exists_continuous_version {W : Ω → ℝ≥0 → ℝ}
    (hWm : Measurable W)
    (hW : ∀ᵐ ω ∂P, Continuous (W ω) ∧ W ω 0 = 0 ∧
      ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (W ω) ⊤ η) :
    ∃ αc : Ω → ℝ≥0 → ℂ, (∀ ω, Continuous (αc ω)) ∧
      (∀ t, Measurable (fun ω => αc ω t)) ∧ (∀ ω, αc ω 0 = 0) ∧
      ∀ᵐ ω ∂P, IsGeneratingTrace (W ω) ⊤ (αc ω) ∧
        ∀ η, IsGeneratingTrace (W ω) ⊤ η → ∀ t, αc ω t = η t := by
  classical
  let good : Set Ω := {ω | Continuous (W ω) ∧ W ω 0 = 0 ∧
    ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (W ω) ⊤ η}
  let G : Set Ω := (toMeasurable P goodᶜ)ᶜ
  have hGm : MeasurableSet G := (measurableSet_toMeasurable P goodᶜ).compl
  have hG : ∀ ω ∈ G, ω ∈ good := by
    intro ω hω
    by_contra hn
    exact hω (subset_toMeasurable P goodᶜ hn)
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by
    have hnull : P goodᶜ = 0 := ae_iff.1 hW
    have hnull' : P (toMeasurable P goodᶜ) = 0 := by rw [measure_toMeasurable, hnull]
    apply ae_iff.2
    have heq : {ω | ω ∉ G} = toMeasurable P goodᶜ := by
      ext ω
      simp only [G, mem_compl_iff, not_not, mem_ofPred_eq]
    rw [heq]
    exact hnull'
  have hread : ∀ ω ∈ G, ∀ η, IsGeneratingTrace (W ω) ⊤ η →
      ∀ t, LP.traceAt t (W ω) = η t := by
    intro ω hω η hη t
    exact LP.traceAt_eq_of_isGeneratingTrace hη (hG ω hω).1.continuousOn
      (hG ω hω).2.1 ENNReal.coe_lt_top
  refine ⟨fun ω t => if ω ∈ G then LP.traceAt t (W ω) else 0,
    fun ω => ?_, fun t => ?_, fun ω => ?_, ?_⟩
  · by_cases hω : ω ∈ G
    · obtain ⟨η, hη⟩ := (hG ω hω).2.2
      have heq : (fun t => if ω ∈ G then LP.traceAt t (W ω) else 0) = η := by
        funext t
        simp only [hω, ↓reduceIte, hread ω hω η hη t]
      change Continuous (fun t => if ω ∈ G then LP.traceAt t (W ω) else 0)
      rw [heq]
      exact continuousOn_univ.1
        (hη.2.1.mono (fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top))
    · simp only [hω, ↓reduceIte]
      exact continuous_const
  · exact Measurable.ite hGm ((LP.measurable_traceAt t).comp hWm) measurable_const
  · by_cases hω : ω ∈ G
    · obtain ⟨η, hη⟩ := (hG ω hω).2.2
      simp only [hω, ↓reduceIte, hread ω hω η hη 0, hη.1]
    · simp only [hω, ↓reduceIte]
  · filter_upwards [hGae] with ω hω
    simp only [hω, ↓reduceIte]
    obtain ⟨η, hη⟩ := (hG ω hω).2.2
    refine ⟨?_, hread ω hω⟩
    have hpath : (fun t => LP.traceAt t (W ω)) = η := funext (hread ω hω η hη)
    rw [hpath]
    exact hη

/-- **The continuous version of a two-piece staged path.** Its positive-time second piece
is the inverse-prefix image of the continuation, and its first piece is the supplied prefix.
The supplied traces need no separate measurability hypothesis. -/
theorem exists_continuous_version_catPath {W₀ W₁ : Ω → ℝ≥0 → ℝ}
    {η₀ η₁ : Ω → ℝ≥0 → ℂ} (a : ℝ≥0)
    (h₀m : ∀ t, Measurable (fun ω => W₀ ω t))
    (h₁m : ∀ t, Measurable (fun ω => W₁ ω t))
    (hgood : ∀ᵐ ω ∂P, Continuous (W₀ ω) ∧ W₀ ω 0 = 0 ∧
      Continuous (W₁ ω) ∧ W₁ ω 0 = 0 ∧ IsGeneratingTrace (W₀ ω) a (η₀ ω) ∧
      IsGeneratingTrace (W₁ ω) ⊤ (η₁ ω) ∧ ∀ s, 0 < s → η₁ ω s ∈ H) :
    ∃ αc : Ω → ℝ≥0 → ℂ, (∀ ω, Continuous (αc ω)) ∧
      (∀ t, Measurable (fun ω => αc ω t)) ∧ (∀ ω, αc ω 0 = 0) ∧
      ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (W₀ ω) a (W₁ ω)) ⊤ (αc ω) ∧
        (∀ t ≤ a, αc ω t = η₀ ω t) ∧
        (∀ s, 0 < s → αc ω (a + s) =
          extendFrom H (fwdMapInv (Ito.rpath (W₀ ω)) a) (η₁ ω s)) := by
  have hcat : ∀ᵐ ω ∂P, IsGeneratingTrace (catPath (W₀ ω) a (W₁ ω)) ⊤
      (LoewnerConcat.joinedTrace (W₀ ω) (η₀ ω) a (η₁ ω)) := by
    filter_upwards [hgood] with ω hω
    exact LoewnerConcat.isGeneratingTrace_catPath hω.1 hω.2.1 hω.2.2.1
      hω.2.2.2.1 hω.2.2.2.2.1 hω.2.2.2.2.2.1 hω.2.2.2.2.2.2
  have hW : ∀ᵐ ω ∂P, Continuous (catPath (W₀ ω) a (W₁ ω)) ∧
      catPath (W₀ ω) a (W₁ ω) 0 = 0 ∧
      ∃ η, IsGeneratingTrace (catPath (W₀ ω) a (W₁ ω)) ⊤ η := by
    filter_upwards [hgood, hcat] with ω hω hη
    exact ⟨continuous_catPath hω.1 hω.2.2.1 hω.2.2.2.1,
      catPath_zero hω.2.1, _, hη⟩
  obtain ⟨αc, hc, hm, h0, hα⟩ := exists_continuous_version (measurable_catPath h₀m h₁m a) hW
  refine ⟨αc, hc, hm, h0, ?_⟩
  filter_upwards [hcat, hα] with ω hη hω
  have heq := hω.2 _ hη
  exact ⟨hω.1, fun t ht => (heq t).trans (LoewnerConcat.joinedTrace_of_le ht),
    fun s hs => (heq (a + s)).trans (LoewnerConcat.joinedTrace_add hs)⟩

end InteractingSLE.Restart.StagedPathVersion
