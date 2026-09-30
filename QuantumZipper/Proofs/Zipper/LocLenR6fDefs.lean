import QuantumZipper.Proofs.Zipper.LocLenPairCfgDefs
import QuantumZipper.Proofs.Zipper.LocLenStmtsF2
import QuantumZipper.Proofs.Zipper.LogShiftLen

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D75, task R6f (1): the log-shift transfer `Γ⁰ → unscaled wedge` with open arcs

Open-arc copies (substitution rule of `handoff/FOLLOW-PAPER-13.md` §1: `unzipLengths ↦
unzipLengthsArc`) of the D29 log-shift statements of `UnscaledResample.lean` and
`LogShiftLen.lean`, and of their deterministic consumers:

* `LogShiftLenWeightArcStmt` (copy of `F1.LogShiftLenWeightStmt`, LogShiftLen.lean:140): the
  weight `w(r) = e^{γ f(η(r))/2}` transports the `Γ⁰` open-arc lengths to the open-arc lengths of
  the log-shifted field `Z = (h⁰ + X) + f`, `f = −γ log|·| + G`. On the open arcs `f` is continuous,
  so this is the local rule of Sheffield arXiv:1012.4797 §1.4 and §5.4 pp. 71–72 (adding a
  continuous function multiplies the boundary measure by `e^{γ f/2}`) read off the tip and off
  the root images (Berestycki–Powell arXiv:2404.16642 Def 6.41 p. 229); no tip estimate.
* `LenRegCfgArcStmt` (copy of `F1.LenRegCfgStmt`, F1LenInReg.lean:99, with `RegPairArc`): the
  `Γ⁰` open-arc lengths are finite, continuous and vanish at `0` (Sheffield p. 70).
* `LogShiftLenDensityArcStmt`, `LogShiftLenFlowMeasArcStmt`, `LogShiftLenFiniteArcStmt`
  (copies of UnscaledResample.lean:61, :98, :82) and their proofs
  `logShiftLenDensityArc_of_weight`, `logShiftLenFlowMeasArc_of_weight` (copies of
  LogShiftLen.lean:163, :174).
* the unscaled wedge statements `LenPairCocycleUnscaledArcStmt'`,
  `LenStrictMonoUnscaledArcStmt'` (copies of F1KappaGuard.lean:77, :60) and their proofs from
  the log-shift statements (copies of UnscaledResample.lean:206, :154).

Own bookkeeping (copies); the mathematics is the cited local rule.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace LocLen

open F1

/-! ## 1. Statements -/

/-- Open-arc copy of `F1.RegPair`, with finiteness (the open-arc lengths are not a priori
finite): both open-arc lengths are finite, continuous on `[0,∞)` and vanish at `0`. -/
def RegPairArc (γ : ℝ) (c : FieldSample × (ℝ → ℝ)) : Prop :=
  (∀ t : ℝ, 0 ≤ t → (unzipLengthsArc γ c t).1 ≠ ⊤ ∧ (unzipLengthsArc γ c t).2 ≠ ⊤) ∧
  ContinuousOn (fun t => (unzipLengthsArc γ c t).1.toReal) (Ici 0) ∧
    (unzipLengthsArc γ c 0).1 = 0 ∧
  ContinuousOn (fun t => (unzipLengthsArc γ c t).2.toReal) (Ici 0) ∧
    (unzipLengthsArc γ c 0).2 = 0

/-- Open-arc copy of `F1.LenRegCfgStmt` (`Γ⁰` picture). -/
def LenRegCfgArcStmt : Prop :=
  ∀ (κ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample), 0 < κ → κ < 4 → IsBrownianReal B P →
    IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    ∀ᵐ ω ∂P, RegPairArc (Real.sqrt κ) (B2.cfg κ B X ω)

/-- Open-arc copy of `F1.LenStrictMonoCfgStmt` (`Γ⁰` picture). -/
def LenStrictMonoCfgArcStmt : Prop :=
  ∀ (κ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample), 0 < κ → κ < 4 → IsBrownianReal B P →
    IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    ∀ᵐ ω ∂P, StrictMonoOn (fun t => (unzipLengthsArc (Real.sqrt κ) (B2.cfg κ B X ω) t).1)
      (Ici 0)

/-- Open-arc copy of `F1.LogShiftLenWeightStmt` (LogShiftLen.lean:140). -/
def LogShiftLenWeightArcStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (G : Ω → ℂ → ℝ) (Z : Ω → FieldSample),
    IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    (∀ᵐ ω ∂P, Continuous (G ω) ∧ ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r →
      Z ω (foldedCircle d r) = (X ω + F2.logSingField κ + ofFun (G ω)) (foldedCircle d r)) →
    ∀ᵐ ω ∂P, ∃ w : ℝ → ℝ≥0∞, Measurable w ∧ (∀ s : ℝ, 0 < s → w s ≠ 0) ∧
      (∀ μm μp : Measure ℝ,
        (∀ t : ℝ, 0 ≤ t →
          unzipLengthsArc (Real.sqrt κ) (B2.cfg κ B X ω) t = (μm (Ioc 0 t), μp (Ioc 0 t))) →
        ∀ t : ℝ, 0 ≤ t →
          unzipLengthsArc (Real.sqrt κ) (Z ω, drive κ B ω) t =
            (∫⁻ r in Ioc 0 t, w r ∂μm, ∫⁻ r in Ioc 0 t, w r ∂μp)) ∧
      ∀ u : ℝ, 0 ≤ u → ∀ μm μp : Measure ℝ,
        (∀ s : ℝ, 0 ≤ s →
          unzipLengthsArc (Real.sqrt κ) (zipCapDown (Real.sqrt κ) u (B2.cfg κ B X ω)) s =
            (μm (Ioc u (u + s)), μp (Ioc u (u + s)))) →
        ∀ s : ℝ, 0 ≤ s →
          unzipLengthsArc (Real.sqrt κ) (zipCapDown (Real.sqrt κ) u (Z ω, drive κ B ω)) s =
            (∫⁻ r in Ioc u (u + s), w r ∂μm, ∫⁻ r in Ioc u (u + s), w r ∂μp)

/-- Open-arc copy of `F1.LogShiftLenFlowMeasStmt` (UnscaledResample.lean:98). -/
def LogShiftLenFlowMeasArcStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) (G : Ω → ℂ → ℝ) (Z : Ω → FieldSample),
    IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    (∀ᵐ ω ∂P, Continuous (G ω) ∧ ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r →
      Z ω (foldedCircle d r) = (X ω + F2.logSingField κ + ofFun (G ω)) (foldedCircle d r)) →
    ∀ᵐ ω ∂P, ∃ νm νp : Measure ℝ, ∀ u s : ℝ, 0 ≤ u → 0 ≤ s →
      unzipLengthsArc (Real.sqrt κ) (Z ω, drive κ B ω) u = (νm (Ioc 0 u), νp (Ioc 0 u)) ∧
      unzipLengthsArc (Real.sqrt κ) (zipCapDown (Real.sqrt κ) u (Z ω, drive κ B ω)) s =
        (νm (Ioc u (u + s)), νp (Ioc u (u + s)))

/-- Open-arc copy of `F1.LenPairCocycleUnscaledStmt'` (F1KappaGuard.lean:77). -/
def LenPairCocycleUnscaledArcStmt' : Prop :=
  ∀ (κ : ℝ), 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X' : Ω → FieldSample) (A : ℝ → Ω → ℝ) (B'' : ℝ≥0 → Ω → ℝ),
    IsFreeGFFModConstH X' P →
    IsWedgeProcess (Real.sqrt κ - 2 / Real.sqrt κ) (Qc (Real.sqrt κ)) A P →
    IndepFun X' (fun ω t => A t ω) P → IsBrownianReal B'' P →
    IndepFun (fun ω => (X' ω, fun t => A t ω)) (pathOf B'') P →
    ∀ᵐ ω ∂P, PairCocycleArc (Real.sqrt κ) (F2.zU (Real.sqrt κ) X' A ω, drive κ B'' ω)

/-! ## 2. `Γ⁰` representation and the log-shift consumers -/

section Gamma

variable {κ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

/-- A finite, monotone, continuous length vanishing at `0` is a Stieltjes measure of `(0,t]`
(`F1.lsl_exists_Ioc_rep`, with finiteness only on `[0,∞)`). -/
theorem exists_Ioc_rep_arc {L : ℝ → ℝ≥0∞} (hfin : ∀ t, 0 ≤ t → L t ≠ ⊤)
    (hmono : MonotoneOn L (Ici 0)) (hc : ContinuousOn (fun t => (L t).toReal) (Ici 0))
    (h0 : L 0 = 0) :
    ∃ μ : Measure ℝ, IsFiniteMeasureOnCompacts μ ∧ ∀ t : ℝ, 0 ≤ t → L t = μ (Ioc 0 t) := by
  have hmax : ∀ t : ℝ, 0 ≤ t → L (max t 0) = L t := fun t ht => by rw [max_eq_left ht]
  obtain ⟨μ, hμ, e⟩ := lsl_exists_Ioc_rep (L := fun t => L (max t 0))
    (fun t => hfin _ (le_max_right _ _))
    (fun a ha b hb hab => by
      simp only [hmax a ha, hmax b hb]; exact hmono ha hb hab)
    (hc.congr fun t ht => by simp only [hmax t ht]) (by simp [h0])
  exact ⟨μ, hμ, fun t ht => by rw [← e t ht, hmax t ht]⟩

/-- **The `Γ⁰` open-arc lengths are Stieltjes measures of capacity time** (copy of
`F1.ae_gammaZero_rep`, LogShiftLen.lean:103). -/
theorem ae_gammaZeroArc_rep (hP : LenPairCocycleCfgArcStmt) (hR : LenRegCfgArcStmt)
    (hκ : 0 < κ) (hκ4 : κ < 4) (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P)
    (hI : IndepFun (pathOf B) X P) :
    ∀ᵐ ω ∂P, ∃ μm μp : Measure ℝ, IsFiniteMeasureOnCompacts μm ∧ IsFiniteMeasureOnCompacts μp ∧
      ∀ t : ℝ, 0 ≤ t →
        unzipLengthsArc (Real.sqrt κ) (B2.cfg κ B X ω) t = (μm (Ioc 0 t), μp (Ioc 0 t)) := by
  filter_upwards [hP κ P B X hκ hκ4 hB hX hI, hR κ P B X hκ hκ4 hB hX hI] with ω hc hr
  obtain ⟨hfin, c1, z1, c2, z2⟩ := hr
  obtain ⟨μm, hm, em⟩ := exists_Ioc_rep_arc
    (L := fun t => (unzipLengthsArc (Real.sqrt κ) (B2.cfg κ B X ω) t).1)
    (fun t ht => (hfin t ht).1)
    (lsl_monotoneOn_of_cocycle fun u s hu hs => (hc u s hu hs).1) c1 z1
  obtain ⟨μp, hp, ep⟩ := exists_Ioc_rep_arc
    (L := fun t => (unzipLengthsArc (Real.sqrt κ) (B2.cfg κ B X ω) t).2)
    (fun t ht => (hfin t ht).2)
    (lsl_monotoneOn_of_cocycle fun u s hu hs => (hc u s hu hs).2) c2 z2
  exact ⟨μm, μp, hm, hp, fun t ht => Prod.ext (em t ht) (ep t ht)⟩

end Gamma

/-- **`LogShiftLenFlowMeasArcStmt` from the weight input and the `Γ⁰` nodes**, with
`ν∓ = w · μ∓` (copy of `F1.logShiftLenFlowMeasStmt_of_weight`). -/
theorem logShiftLenFlowMeasArc_of_weight (hP : LenPairCocycleCfgArcStmt)
    (hR : LenRegCfgArcStmt) (hW : LogShiftLenWeightArcStmt) : LogShiftLenFlowMeasArcStmt := by
  intro κ hκ hκ4 Ω _ P _ B X G Z hB hX hI hGZ
  filter_upwards [ae_gammaZeroArc_rep hP hR hκ hκ4 hB hX hI, hP κ P B X hκ hκ4 hB hX hI,
    hR κ P B X hκ hκ4 hB hX hI, hW κ hκ hκ4 P B X G Z hB hX hI hGZ] with ω h1 hc hr h2
  obtain ⟨μm, μp, -, -, e⟩ := h1
  obtain ⟨w, -, -, hZ, hZu⟩ := h2
  have eu : ∀ u : ℝ, 0 ≤ u → ∀ s : ℝ, 0 ≤ s →
      unzipLengthsArc (Real.sqrt κ) (zipCapDown (Real.sqrt κ) u (B2.cfg κ B X ω)) s =
        (μm (Ioc u (u + s)), μp (Ioc u (u + s))) := by
    intro u hu s hs
    obtain ⟨c1, c2⟩ := hc u s hu hs
    have fm := (hr.1 u hu).1
    have fp := (hr.1 u hu).2
    rw [e (u + s) (by linarith), e u hu] at c1 c2
    rw [e u hu] at fm fp
    simp only at c1 c2 fm fp
    rw [ursmp_cocycle μm hu hs] at c1
    rw [ursmp_cocycle μp hu hs] at c2
    exact Prod.ext ((ENNReal.cancel_of_ne fm).inj_right.1 c1).symm
      ((ENNReal.cancel_of_ne fp).inj_right.1 c2).symm
  refine ⟨μm.withDensity w, μp.withDensity w, fun u s hu hs => ⟨?_, ?_⟩⟩
  · rw [hZ μm μp e u hu, withDensity_apply _ measurableSet_Ioc,
      withDensity_apply _ measurableSet_Ioc]
  · rw [hZu u hu μm μp (eu u hu) s hs, withDensity_apply _ measurableSet_Ioc,
      withDensity_apply _ measurableSet_Ioc]

/-! ## 3. The unscaled wedge statements -/

/-- **Open-arc pair cocycle of the unscaled wedge from the flow representation** (copy of
`F1.ae_pairCocycle_unscaled_of_logShift` and `F1.lenPairCocycleUnscaledStmt'_of_logShift`). -/
theorem lenPairCocycleUnscaledArc'_of_logShift (hM : LogShiftLenFlowMeasArcStmt) :
    LenPairCocycleUnscaledArcStmt' := by
  intro κ hκ hκ4 Ω _ P _ X' A B'' hX hA hI hB hIB
  refine ae_unscaled_of_logShift hκ hκ4 (fun c => PairCocycleArc (Real.sqrt κ) c) ?_
    hX hA hI hB hIB
  intro Ω₁ _ P₁ _ B X G Z hB1 hX1 hI1 hGZ
  filter_upwards [hM κ hκ hκ4 P₁ B X G Z hB1 hX1 hI1 hGZ] with ω h
  obtain ⟨νm, νp, hrep⟩ := h
  intro u s hu hs
  have hus := (hrep (u + s) 0 (by linarith) le_rfl).1
  have hu' := (hrep u s hu hs).1
  have hf := (hrep u s hu hs).2
  rw [hus, hu', hf]
  exact ⟨ursmp_cocycle νm hu hs, ursmp_cocycle νp hu hs⟩

end LocLen
end QuantumZipper
