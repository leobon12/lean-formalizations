/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.RealContact.PocketMain
import InteractingSLE.Spec.Restart.CondDet
import InteractingSLE.Spec.Exist.Param12Canonical

/-!
# The terminal retained pair: the kernel carrier from the conditional field and the determination identity

Packet PROVE-RC-POCKET (ruling R124). `PocketMain.lean` proves the pocket-corner exclusion from the kernel carrier
`TerminalRetainedPairStatement` (Lemma G7 at the retained pair `(0, ζ₂)`). As for the landed Lemma G7
(`Restart.retainedKernelClockStatement_of_condDet`), the kernel part of that carrier is the general restart kernel
(`Restart.exists_isMarkovKernel_map_eq_compProd`, `Restart.ae_isGFFWithBoundaryData_of_condExp_word`,
`Restart.ae_isFlowLine_of_codeMatch_canonical`). What remains is a statement about `P` only, with no kernel:

**`TerminalRetainedCondDetStatement`** (named input, **not proved in Lean**). For every canonical flow code `F` of the
angle `θ₁` there are a sub-σ-algebra `𝒢` (the completed second path), a `𝒢`-event `M`, a `𝒢`-measurable datum
`β = (word, chart position of the first seed)` and a measurable chart field `Hc` such that
* on `M` the word is sorted and the seed position is positive;
* (R1) on `M`, conditionally on `𝒢`, the chart field has the Gaussian characteristic functional of the word;
* (Det) almost surely on the trigger event (`η₂` ends at a real point `e < x₂`, and `η₁` visits a real point `y ≤ e`
  before its lifetime): `ω ∈ M`, and `IsTerminalRetainedContinuation` holds with the chart field `Hc ω` and with the
  chart path and lifetime of the **decoded canonical flow code** of the chart field from the seed position.

## Main results

* **`terminalRetainedPairStatement_of_condDet`**: the kernel carrier from canonical flow codes and the input;
* `terminalRetainedPairStatement_of_condDet'`: the same with the canonical flow codes supplied by the closed
  Theorems 1.2–1.3 (used inline, rulings R48 and R123);
* **`pocketCorner_of_terminalCondDet`**, `g7GB7aFirstHitReal_of_terminalCondDet`: the pocket-corner exclusion and the
  real first-hit exclusion from the single input `TerminalRetainedCondDetStatement`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.RealContact

open Restart LQGMetric Sec2.Assembly

/-- **Named input: the completed second path's conditional field and the determination identity for the first
path** (Lemma G7, supplement pp. 497–498, at the retained pair `(0, ζ₂)`; Lemma SB2(2), p. 631, at the first stage).
See the module docstring. A statement about `P` only. **Not proved in Lean.** -/
def TerminalRetainedCondDetStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ ≤ x₁ →
    κ / 2 - 2 ≤
      Sec4.cumWeightRight κ ((-sleLambda κ - θ₁ * QuantumZipper.chiC κ) + θ₂ * QuantumZipper.chiC κ) →
    ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
    ∀ F : (BoundaryWord × ℝ) × DistOn upperHalfPlaneOpens → (PCode × PCode) × ℝ≥0∞,
      IsCanonicalFlowCode κ θ₁ F →
    ∃ (𝒢 : {m : MeasurableSpace Ω // m ≤ mΩ}) (M : Set Ω) (β : Ω → BoundaryWord × ℝ)
      (Hc : Ω → DistOn upperHalfPlaneOpens),
      MeasurableSet[𝒢.1] M ∧ Measurable[𝒢.1] β ∧ Measurable Hc ∧
      (∀ᵐ ω ∂P, ω ∈ M → (β ω).1.IsSorted ∧ 0 < (β ω).2) ∧
      (∀ φ : TestOn upperHalfPlaneOpens, ∀ᵐ ω ∂P, ω ∈ M →
        P[fun ω' => Complex.exp (Complex.I * (Hc ω' φ : ℂ)) | 𝒢.1] ω = gaussCF (β ω).1 φ) ∧
      ∀ᵐ ω ∂P, ∀ (T : ℝ≥0) (e : ℝ), (T : ℝ≥0∞) = ζ₂ ω → η₂ ω T = e → e < x₂ →
        (∃ (s : ℝ≥0) (y : ℝ), (s : ℝ≥0∞) < ζ₁ ω ∧ η₁ ω s = y ∧ y ≤ e) →
        ω ∈ M ∧ IsTerminalRetainedContinuation κ b (h ω) (Hc ω) (η₁ ω) (ζ₁ ω) (η₂ ω) T (β ω).1
          (decPath (F (β ω, Hc ω))) (F (β ω, Hc ω)).2

/-- **The kernel carrier of the terminal retained pair from the general restart kernel**: canonical flow codes, the
conditional field (R1) and the determination identity (Det) give `TerminalRetainedPairStatement`. The restart
variable is the chart field together with its canonical flow code from the seed position; the kernel is its
conditional law given the datum on `M`. -/
theorem terminalRetainedPairStatement_of_condDet (hF : CanonicalFlowCodeStatement)
    (hD : TerminalRetainedCondDetStatement.{u}) : TerminalRetainedPairStatement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hwt Ω mΩ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂
  obtain ⟨F, hF₁⟩ := hF κ θ₁ hκ hκ4
  obtain ⟨𝒢, M, β, Hc, hM, hβ, hHcm, hsort, hR1, hpath⟩ :=
    hD κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hwt P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ F hF₁
  have hβm : Measurable β := hβ.mono 𝒢.2 le_rfl
  have hMm : MeasurableSet M := 𝒢.2 _ hM
  have hFm : Measurable fun ω => F (β ω, Hc ω) := hF₁.1.comp (hβm.prodMk hHcm)
  set X : Ω → RestartSpace := fun ω => (Hc ω, F (β ω, Hc ω), F (β ω, Hc ω)) with hXdef
  have hXm : Measurable X := hHcm.prodMk (hFm.prodMk hFm)
  obtain ⟨K, hK, hlaw⟩ := exists_isMarkovKernel_map_eq_compProd P M hβm hXm
  have hco := isRestartCoordinates_restartSpace
  -- (R1) under the kernel
  have hgff := ae_isGFFWithBoundaryData_of_condExp_word 𝒢.2 hM hβ measurable_fst
    (by filter_upwards [hsort] with ω hω hωM; exact (hω hωM).1) hXm (H := RestartSpace.field)
    measurable_fst hlaw hR1
  -- the chart path is the canonical flow of the chart field, by construction
  have hfl := ae_isFlowLine_of_codeMatch_canonical hMm hβm hXm hlaw measurable_fst measurable_snd
    (H := RestartSpace.field) measurable_fst (Γ := RestartSpace.path₁) hco.2.2.2.1 hco.2.1
    hco.2.2.2.2.2.1 hF₁ hgff (Eventually.of_forall fun ω _ => ⟨rfl, fun t _ => rfl⟩)
  have hpos : ∀ᵐ c ∂(P.restrict M).map β, 0 < c.2 :=
    (ae_map_iff (p := fun c : BoundaryWord × ℝ => 0 < c.2) hβm.aemeasurable
      (measurableSet_lt measurable_const measurable_snd)).2
      ((ae_restrict_iff' hMm).2 (by filter_upwards [hsort] with ω hω hωM; exact (hω hωM).2))
  refine ⟨RestartSpace, inferInstance, RestartSpace.field, RestartSpace.path₁, RestartSpace.life₁, M, β, X, K,
    hco.1, hco.2.1, hco.2.2.2.1, hco.2.2.2.2.2.1, hMm, hβm, hXm, hK, hlaw, ?_, ?_⟩
  · filter_upwards [hgff, hfl, hpos] with c hcg h1 hc
    exact ⟨hc, hcg.2, h1⟩
  · filter_upwards [hpath] with ω hω T e hT he hex hvis
    exact hω T e hT he hex hvis

/-- The kernel carrier of the terminal retained pair from the single input `TerminalRetainedCondDetStatement`; the
canonical flow codes come from the closed Theorems 1.2–1.3 (used inline: rulings R48 and R123). -/
theorem terminalRetainedPairStatement_of_condDet' (hD : TerminalRetainedCondDetStatement.{u}) :
    TerminalRetainedPairStatement.{u} :=
  terminalRetainedPairStatement_of_condDet
    (canonicalFlowCodeStatement_of_param
      (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 AuditFix.ContactInputs.theorem12
        AuditFix.ContactInputs.theorem13) AuditFix.ContactInputs.theorem13) hD

/-- **The pocket-corner exclusion from the completed second path's conditional field and the determination
identity.** -/
theorem pocketCorner_of_terminalCondDet (hD : TerminalRetainedCondDetStatement.{u}) :
    PocketCornerStatement.{u} :=
  pocketCorner_of_terminalRetained (terminalRetainedPairStatement_of_condDet' hD)

/-- **The real first-hit exclusion from the same input.** -/
theorem g7GB7aFirstHitReal_of_terminalCondDet (hD : TerminalRetainedCondDetStatement.{u}) :
    G7GB7aFirstHitRealStatement.{u} :=
  g7GB7aFirstHitReal_of_pocketCorner (pocketCorner_of_terminalCondDet hD)

end InteractingSLE.RealContact
