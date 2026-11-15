/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondStagedCandComp
import InteractingSLE.Spec.Sec5.Prop59PiecesExp

/-!
# Proposition 5.9: the stage law of the root experiment from the per-candidate laws

Packet PROVE-STAGED7. PROVE-PROP59-PIECES' root experiment runs `histSys (rootCand … q) ratGrid … (rootStart … q)
univ base` on `Ω × Ωa`. This file instantiates the reduction of `CrossCondStagedCandTree`/`CrossCondStagedCandComp`
for it: the candidates are regular (`isRegFam_rootCand`), the root start is measurable (`measurable_rootStart`), so
any comparison-form stage law for the root experiment follows from the laws of the fixed candidates `rootCand … q j t`
for their canonical pasts, reached events and starts alone (`isCompLaw_rootCand`). The killed law of ruling R75 is
`CrossCondStagedCandFar.prop59StageLawFarStatement_rootCand`.

Conditional helpers with distinct names; they replace no source theorem. R48: nothing here uses Theorem 1.2/1.3;
`Theorem12ParamCond44Statement` (R74) enters only through PROVE-PROP59-PIECES' code drivers.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CrossCond.StagedCand

open Prop59Stage Prop59System StagedAdapt Prop59Pieces Prop513TreeExtract Prop513Target Sec7.AdmCode Restart Sec4

section Root

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b')
  {Ω Ωa : Type} [mΩ : MeasurableSpace Ω] [MeasurableSpace Ωa] {P : Measure Ω} {Pa : Measure Ωa}
  {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
  {lam : ℚ → Ω → ℝ} {xL0 : ℚ → Ω → Fin (rootNL (sourceWord (x₀ := x₀) hκ hb)) → ℝ}
  {xR0 : ℚ → Ω → Fin (rootNR (sourceWord (x₀ := x₀) hκ hb)) → ℝ}
  {noise : ℚ → (j : ℕ) → (Fin j → ℝ≥0) → ℝ≥0 → Ω → ℝ}

include h44 hκ4 in
/-- The concrete candidates of the root experiment are regular. -/
theorem isRegFam_rootCand (hhm : Measurable h)
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (Real.pi * x₀)) P h W ζ) (hlam : ∀ q, Measurable (lam q))
    (hpos : ∀ q ω, 0 < lam q ω) (hxL : ∀ q, Measurable (xL0 q)) (hxR : ∀ q, Measurable (xR0 q)) (q : ℚ) :
    IsRegFam (rootCand x₀ h44 hκ hκ4 hb P h W ζ lam xL0 xR0 noise (Ωa := Ωa) q) :=
  isRegFam_liftFam (isRegFam_rootData x₀ h44 hκ hκ4 hb hhm hcf (hlam q) (hpos q) (hxL q) (hxR q))

/-- The root start of the root experiment is measurable. -/
theorem measurable_rootStart (hxL : ∀ q, Measurable (xL0 q)) (hxR : ∀ q, Measurable (xR0 q)) (q : ℚ) :
    Measurable (rootStart x₀ hκ hb xL0 xR0 (Ωa := Ωa) q) :=
  measurable_const.prodMk (((hxL q).comp measurable_fst).prodMk ((hxR q).comp measurable_fst))

include h44 hκ4 in
/-- **The generic comparison-form law for the root experiment** from the per-candidate laws (`isCompLaw_histSys_canon`
instantiated; covers stage laws killed at the first far contact). -/
theorem isCompLaw_rootCand {X : ℕ → Type*} [∀ j, MeasurableSpace (X j)]
    {Φ : (j : ℕ) → StageRec (rootNL (sourceWord (x₀ := x₀) hκ hb) + j) (rootNR (sourceWord (x₀ := x₀) hκ hb) + j) →
      Prop}
    {g : (j : ℕ) → StageRec (rootNL (sourceWord (x₀ := x₀) hκ hb) + j) (rootNR (sourceWord (x₀ := x₀) hκ hb) + j) →
      X j}
    {Prem : (j : ℕ) → Set (X j) → ℝ≥0∞ → Prop} (hhm : Measurable h)
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (Real.pi * x₀)) P h W ζ) (hlam : ∀ q, Measurable (lam q))
    (hpos : ∀ q ω, 0 < lam q ω) (hxL : ∀ q, Measurable (xL0 q)) (hxR : ∀ q, Measurable (xR0 q)) (q : ℚ)
    (base : ℚ → MeasurableSpace (Ω × Ωa))
    (hlaw : ∀ j t, IsCompLaw (P.prod Pa)
      (canonQ (base q) (rootCand x₀ h44 hκ hκ4 hb P h W ζ lam xL0 xR0 noise (Ωa := Ωa) q) ratGrid
        (rootNL_pos _) (rootNR_pos _) (rootStart x₀ hκ hb xL0 xR0 q) j t)
      (canonR (rootCand x₀ h44 hκ hκ4 hb P h W ζ lam xL0 xR0 noise (Ωa := Ωa) q) ratGrid
        (rootNL_pos _) (rootNR_pos _) (rootStart x₀ hκ hb xL0 xR0 q) univ j t) (Φ j) (g j) (Prem j)
      (stageRec (canonY (rootCand x₀ h44 hκ hκ4 hb P h W ζ lam xL0 xR0 noise (Ωa := Ωa) q)
          (rootStart x₀ hκ hb xL0 xR0 q) j t)
        (rootCand x₀ h44 hκ hκ4 hb P h W ζ lam xL0 xR0 noise (Ωa := Ωa) q j t).W
        (rootCand x₀ h44 hκ hκ4 hb P h W ζ lam xL0 xR0 noise (Ωa := Ωa) q j t).VL
        (rootCand x₀ h44 hκ hκ4 hb P h W ζ lam xL0 xR0 noise (Ωa := Ωa) q j t).VR
        (rootCand x₀ h44 hκ hκ4 hb P h W ζ lam xL0 xR0 noise (Ωa := Ωa) q j t).B
        (rootCand x₀ h44 hκ hκ4 hb P h W ζ lam xL0 xR0 noise (Ωa := Ωa) q j t).ζ))
    (r : ℕ → ℕ) (j : ℕ) :
    IsCompLaw (P.prod Pa)
      (histSys (rootCand x₀ h44 hκ hκ4 hb P h W ζ lam xL0 xR0 noise (Ωa := Ωa) q) ratGrid (rootNL_pos _)
        (rootNR_pos _) (rootStart x₀ hκ hb xL0 xR0 q) univ (base q) r j).past
      (histSys (rootCand x₀ h44 hκ hκ4 hb P h W ζ lam xL0 xR0 noise (Ωa := Ωa) q) ratGrid (rootNL_pos _)
        (rootNR_pos _) (rootStart x₀ hκ hb xL0 xR0 q) univ (base q) r j).R (Φ j) (g j) (Prem j)
      (stageRec
        (histSys (rootCand x₀ h44 hκ hκ4 hb P h W ζ lam xL0 xR0 noise (Ωa := Ωa) q) ratGrid (rootNL_pos _)
          (rootNR_pos _) (rootStart x₀ hκ hb xL0 xR0 q) univ (base q) r j).y
        (histSys (rootCand x₀ h44 hκ hκ4 hb P h W ζ lam xL0 xR0 noise (Ωa := Ωa) q) ratGrid (rootNL_pos _)
          (rootNR_pos _) (rootStart x₀ hκ hb xL0 xR0 q) univ (base q) r j).W
        (histSys (rootCand x₀ h44 hκ hκ4 hb P h W ζ lam xL0 xR0 noise (Ωa := Ωa) q) ratGrid (rootNL_pos _)
          (rootNR_pos _) (rootStart x₀ hκ hb xL0 xR0 q) univ (base q) r j).VL
        (histSys (rootCand x₀ h44 hκ hκ4 hb P h W ζ lam xL0 xR0 noise (Ωa := Ωa) q) ratGrid (rootNL_pos _)
          (rootNR_pos _) (rootStart x₀ hκ hb xL0 xR0 q) univ (base q) r j).VR
        (histSys (rootCand x₀ h44 hκ hκ4 hb P h W ζ lam xL0 xR0 noise (Ωa := Ωa) q) ratGrid (rootNL_pos _)
          (rootNR_pos _) (rootStart x₀ hκ hb xL0 xR0 q) univ (base q) r j).B
        (histSys (rootCand x₀ h44 hκ hκ4 hb P h W ζ lam xL0 xR0 noise (Ωa := Ωa) q) ratGrid (rootNL_pos _)
          (rootNR_pos _) (rootStart x₀ hκ hb xL0 xR0 q) univ (base q) r j).ζ) :=
  isCompLaw_histSys_canon (isRegFam_rootCand x₀ h44 hκ hκ4 hb hhm hcf hlam hpos hxL hxR q)
    (measurable_rootStart x₀ hκ hb hxL hxR q) MeasurableSet.univ hlaw r j

end Root

end InteractingSLE.Sec5.CrossCond.StagedCand
