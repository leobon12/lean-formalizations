import QuantumZipper.Proofs.Thm18.G1RegRepRed

/-!
# G1 package: the measurable selection `G1PsiSelStmt`, split into a trace part and a chord part

`G1PsiSelStmt` (G1RegRepRed.lean) asks for maps `Ψ left a`, jointly measurable in the driving
path `a : ℝ≥0 → ℝ` (product σ-algebra) and `z`, with measurable `log ‖(Ψ left a)'‖`, that are
inverse normalized uniformizers of the side domains of the trace whenever `a` is continuous and
its trace is a simple chord. It factors through the chord:

* `G1TraceSelStmt` (trace part): the Loewner trace has a version `Tr a`, measurable in the path
  (into the product σ-algebra of `ℝ → ℂ`), equal to `pathTrace κ a` on `[0,∞)` for every
  continuous path whose trace is a simple chord (`0 < κ < 4`). This is the path-space form of
  EXT-RS TR6 (`RS.exists_measurable_sleTrace`, which is the a.s. form on a probability space).
* `G1ChordUnifSelStmt` (chord part): inverse normalized uniformizers of the two side domains,
  jointly measurable in the chord `η : ℝ → ℂ` (product σ-algebra) and `z`, with measurable
  `log ‖ψ'‖`. KT2 (`CA.Kernel.chordKernelTheoremLeft/Right`) gives the continuity in the chord
  (sphere-uniform metric) on which a proof would rest.

`g1PsiSelStmt_of_parts : G1TraceSelStmt → G1ChordUnifSelStmt → G1PsiSelStmt`: take
`Ψ left a := U left (Tr a)`; the side domains and the simple-chord property only read the chord
on `[0,∞)` (`sideDom_congr`, `isSimpleChord_congr`).

Own argument (bookkeeping).
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped NNReal

namespace QuantumZipper
namespace Thm18Asm

/-- **Trace part**: a path-measurable version of the Loewner trace. -/
def G1TraceSelStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
    ∃ Tr : (ℝ≥0 → ℝ) → ℝ → ℂ, Measurable Tr ∧
      ∀ a : ℝ≥0 → ℝ, Continuous a → IsSimpleChord (pathTrace κ a) →
        EqOn (Tr a) (pathTrace κ a) (Ici 0)

/-- **Chord part**: chord-measurable inverse normalized uniformizers of the side domains. -/
def G1ChordUnifSelStmt : Prop :=
  ∃ U : Bool → (ℝ → ℂ) → ℂ → ℂ,
    (∀ left, Measurable fun p : (ℝ → ℂ) × ℂ => U left p.1 p.2) ∧
    (∀ left, Measurable fun p : (ℝ → ℂ) × ℂ => Real.log ‖deriv (U left p.1) p.2‖) ∧
    ∀ η : ℝ → ℂ, IsSimpleChord η → ∀ left : Bool,
      ∃ φ : ℂ → ℂ, IsNormalizedUniformizer (sideDom η left) φ ∧
        U left η = invFunOn φ (sideDom η left)

namespace G1Pkg

theorem sideDom_congr {η η' : ℝ → ℂ} (h : EqOn η η' (Ici 0)) (left : Bool) :
    sideDom η left = sideDom η' left := by
  have himg : η '' Ici (0 : ℝ) = η' '' Ici 0 := h.image_eq
  cases left
  · show rightComponent η = rightComponent η'
    unfold rightComponent; rw [himg]
  · show leftComponent η = leftComponent η'
    unfold leftComponent; rw [himg]

theorem isSimpleChord_congr {η η' : ℝ → ℂ} (h : EqOn η η' (Ici 0)) (hη : IsSimpleChord η) :
    IsSimpleChord η' := by
  obtain ⟨h0, hc, hi, hH, hT⟩ := hη
  refine ⟨(h (Set.mem_Ici.2 (le_refl (0 : ℝ)))).symm.trans h0, hc.congr fun t ht => (h ht).symm,
    hi.congr h, fun t ht => (h (le_of_lt ht : (0 : ℝ) ≤ t)) ▸ hH t ht, ?_⟩
  refine hT.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  rw [h ht]

end G1Pkg

/-- **`G1PsiSelStmt` from its trace and chord parts.** -/
theorem g1PsiSelStmt_of_parts (hT : G1TraceSelStmt) (hU : G1ChordUnifSelStmt) :
    G1PsiSelStmt := by
  intro γ hγ hγ2
  have hκ : 0 < γ ^ 2 := by positivity
  have hκ4 : γ ^ 2 < 4 := by nlinarith
  obtain ⟨Tr, hTm, hTeq⟩ := hT (γ ^ 2) hκ hκ4
  obtain ⟨U, hUm, hUd, hUeq⟩ := hU
  have hpair : Measurable fun p : (ℝ≥0 → ℝ) × ℂ => (Tr p.1, p.2) :=
    (hTm.comp measurable_fst).prodMk measurable_snd
  refine ⟨fun left a => U left (Tr a), fun left => (hUm left).comp hpair,
    fun left => (hUd left).comp hpair, ?_⟩
  intro a ha hs left
  have heq := hTeq a ha hs
  obtain ⟨φ, hφ, hU'⟩ := hUeq (Tr a) (G1Pkg.isSimpleChord_congr heq.symm hs) left
  rw [G1Pkg.sideDom_congr heq left] at hφ hU'
  exact ⟨φ, hφ, hU'⟩

end Thm18Asm
end QuantumZipper
