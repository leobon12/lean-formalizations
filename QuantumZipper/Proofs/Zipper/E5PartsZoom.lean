import QuantumZipper.Proofs.Zipper.E5PartsMeas
import QuantumZipper.Proofs.Zipper.E5Final5a
import QuantumZipper.Proofs.Zipper.E5Final5c
import QuantumZipper.Proofs.Zipper.F1Embed
import QuantumZipper.Proofs.Zipper.F2Unscaled
import QuantumZipper.Proofs.Section5.Prop16MarkovMask2Agree

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# E5-PARTS, part 2: a zoom model exists (`ZoomModelNonemptyStmt`, proved)

Task E5-PARTS (Theorem 1.3, node E5; Sheffield, arXiv:1012.4797, §5.4, pp. 66–72). E5 only uses
`ZoomModelNonemptyStmt` when the Palm mass vanishes, so any zoom model will do. We take the
product `(Ω_B × NS(Ω_X), stdP ⊗ P_X.completion)` of a Brownian space and the *completion* of a
free-field space (`BMExist.exists_isBrownianReal_stdP` with the continuous version
`F1.exists_meas_brownian_version`, `exists_freeGFF`), the field `X' = X ∘ snd`, the conditioning
map `Ξ = fst`, the corrections `g = g₀ = 0`, radius `r = 1`, `ρ₀ = foldedCircle 0 2` (as in
`D3Plus.exists_setup`), the driver `D = pathOf b ∘ fst`, weight `w = 1`, and `V = snd`,
`a C = zScale(X ·, 0)`, `y C = zLoc(X ·, 0)`. `V` is independent of `D` because the two coordinates
of a product measure are. The local scale is a.e.-measurable
(`Prop16Asm.aemeasurable_scaleParamOn_zoomModel_mm`), hence so are the rich local data
(`E5PartsMeas.aemeasurable_zLoc_of_scale_e5p`), and a.e.-measurable maps are measurable on the
completion (`AEMeasurable.nullMeasurable`); this is why the free-field factor is completed.

Own elementary bookkeeping (no new mathematics).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace E5

open LengthMarkov.GermDensity

/-- **A zoom model exists.** -/
theorem zoomModelNonempty_holds : ZoomModelNonemptyStmt := by
  intro κ hκ hκ4 R W _ hW
  obtain ⟨Ωg, mg, Pg, Xg, hPg, hXg⟩ := QuantumZipper.exists_freeGFF
  obtain ⟨B₀, hB₀⟩ := BMExist.exists_isBrownianReal_stdP
  obtain ⟨b, hbm, hbc, hb, -⟩ := F1.exists_meas_brownian_version hB₀
  have hγ : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hγ2 : Real.sqrt κ < 2 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt hκ.le hκ4
  have hα : Real.sqrt κ - 2 / Real.sqrt κ < Qc (Real.sqrt κ) := F2.alpha_lt_Qc' hγ hγ2
  have hbpath : Measurable (pathOf b) := measurable_pi_iff.2 hbm
  have hXm : Measurable Xg := measurable_pi_iff.2 hXg.measurable_coord
  -- the free field on the completed space
  have hYc : IsFreeGFFModConstH (fun v : NullMeasurableSpace Ωg Pg => Xg (ESM.ofCompl Pg v))
      Pg.completion :=
    Cor15Group.isFreeGFFModConstH_of_map_eq
      (fun μ => (hXg.measurable_coord μ).comp ESM.measurable_ofCompl)
      (ESM.map_completion hXm.aemeasurable) hXg
  -- the D3⁺ setup on the raw free-field space (for the a.e. measurability of the scale)
  have hS0 : D3Plus.Setup (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) 1 (foldedCircle 0 2)
      Pg Xg (fun _ => ()) (fun _ _ => (0 : ℝ)) :=
    { hγ := hγ
      hγ2 := hγ2
      hα := hα
      hr := one_pos
      hX := hXg
      hΞ := measurable_const
      hind := by
        rw [MeasurableSpace.comap_const]
        exact indep_bot_left _
      hρ := isAdmissibleH_foldedCircle (by simp [Hbar]) (by norm_num)
      hρ1 := measure_univ
      hρB := LateralGerm.foldedCircle_ball_eq_zero one_pos (by norm_num)
      harm := fun _ => by simp
      gmeas := fun _ => measurable_const }
  have hsae : ∀ C : ℝ, AEMeasurable (fun v : Ωg =>
      zScale (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) 1 (foldedCircle 0 2) C (Xg v)
        ((fun _ _ => (0 : ℝ)) v)) Pg := fun C =>
    Prop16Asm.aemeasurable_scaleParamOn_zoomModel_mm hS0 C
  have hZ : ∀ C : ℝ, Measurable fun v : Ωg => Factorization.coords
      (D3Plus.zoomModel (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) C (foldedCircle 0 2)
        (Xg v) ((fun _ _ => (0 : ℝ)) v)) := fun C =>
    measurable_coords_zoomModel_e5p _ _ C _ hXg.measurable_coord measurable_const
  have ha : ∀ C : ℝ, Measurable fun v : NullMeasurableSpace Ωg Pg =>
      zScale (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) 1 (foldedCircle 0 2) C
        (Xg (ESM.ofCompl Pg v)) ((fun _ _ => (0 : ℝ)) v) := fun C =>
    fun _ hs => (hsae C).nullMeasurable hs
  have hy : ∀ C : ℝ, Measurable fun v : NullMeasurableSpace Ωg Pg =>
      zLoc D3Plus.locFieldFull (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) 1
        (foldedCircle 0 2) R C (Xg (ESM.ofCompl Pg v)) ((fun _ _ => (0 : ℝ)) v) := fun C =>
    fun _ hs => (aemeasurable_zLoc_of_scale_e5p (μ := Pg) R (hZ C) (hsae C)).nullMeasurable hs
  have hS : D3Plus.Setup (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) 1 (foldedCircle 0 2)
      (LQGDimension.ExistAsm.stdP.prod Pg.completion)
      (fun z : (ℕ → ℝ) × NullMeasurableSpace Ωg Pg => Xg (ESM.ofCompl Pg z.2))
      (Prod.fst : (ℕ → ℝ) × NullMeasurableSpace Ωg Pg → ℕ → ℝ) (fun _ _ => (0 : ℝ)) :=
    { hγ := hγ
      hγ2 := hγ2
      hα := hα
      hr := one_pos
      hX := isFreeGFFModConstH_snd_prod hYc
      hΞ := measurable_fst
      hind := indep_fst_freeIncrSigma_snd hYc
      hρ := isAdmissibleH_foldedCircle (by simp [Hbar]) (by norm_num)
      hρ1 := measure_univ
      hρB := LateralGerm.foldedCircle_ball_eq_zero one_pos (by norm_num)
      harm := fun _ => by simp
      gmeas := fun _ => measurable_const }
  have hmS : ∀ C : ℝ, Measurable fun z : (ℕ → ℝ) × NullMeasurableSpace Ωg Pg =>
      zScale (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) 1 (foldedCircle 0 2) C
        (Xg (ESM.ofCompl Pg z.2)) ((fun _ _ => (0 : ℝ)) z) := fun C =>
    (ha C).comp measurable_snd
  have hD : Measurable fun z : (ℕ → ℝ) × NullMeasurableSpace Ωg Pg => pathOf b z.1 :=
    hbpath.comp measurable_fst
  have hDm : Measurable[D3Plus.condSigma
      (Prod.fst : (ℕ → ℝ) × NullMeasurableSpace Ωg Pg → ℕ → ℝ)
      (fun z : (ℕ → ℝ) × NullMeasurableSpace Ωg Pg => Xg (ESM.ofCompl Pg z.2)) 1]
      fun z : (ℕ → ℝ) × NullMeasurableSpace Ωg Pg => pathOf b z.1 :=
    (hbpath.comp (comap_measurable
      (Prod.fst : (ℕ → ℝ) × NullMeasurableSpace Ωg Pg → ℕ → ℝ))).mono le_sup_left le_rfl
  have hind : IndepFun (Prod.snd : (ℕ → ℝ) × NullMeasurableSpace Ωg Pg → _)
      (fun z : (ℕ → ℝ) × NullMeasurableSpace Ωg Pg => pathRestr 1 (pathOf b z.1))
      (LQGDimension.ExistAsm.stdP.prod Pg.completion) := by
    have h0 := indepFun_prod (μ := LQGDimension.ExistAsm.stdP) (ν := Pg.completion)
      (X := (id : (ℕ → ℝ) → ℕ → ℝ)) (Y := (id : NullMeasurableSpace Ωg Pg → _))
      measurable_id measurable_id
    exact (h0.comp ((measurable_pathRestr 1).comp hbpath) measurable_id).symm
  have hDW : (LQGDimension.ExistAsm.stdP.prod Pg.completion).map
      (fun z : (ℕ → ℝ) × NullMeasurableSpace Ωg Pg => pathRestr 1 (pathOf b z.1)) =
        W.map (pathRestr 1) := by
    have e : (fun z : (ℕ → ℝ) × NullMeasurableSpace Ωg Pg => pathRestr 1 (pathOf b z.1)) =
        (pathRestr 1 ∘ pathOf b) ∘ Prod.fst := rfl
    rw [e, ← Measure.map_map ((measurable_pathRestr 1).comp hbpath) measurable_fst,
      Measure.map_fst_prod, measure_univ, one_smul, wiener_eq_map hW hb,
      Measure.map_map (measurable_pathRestr 1) hbpath]
  exact ⟨
    { Ω₁ := (ℕ → ℝ) × NullMeasurableSpace Ωg Pg
      Q := LQGDimension.ExistAsm.stdP.prod Pg.completion
      X' := fun z => Xg (ESM.ofCompl Pg z.2)
      E' := ℕ → ℝ
      Ξ := Prod.fst
      r := 1
      ρ₀ := foldedCircle 0 2
      g := fun _ _ => 0
      g₀ := fun _ _ => 0
      hS := hS
      hS₀ := hS
      hm := hmS
      hm₀ := hmS
      hbadm := fun K => MeasurableSet.const _
      hbad := fun ε _ => ⟨0, le_rfl, by simp [gBad]⟩
      Rr := LQGDimension.ExistAsm.stdP.prod Pg.completion
      w := 1
      hw1 := by simp
      hQ := (withDensity_one).symm
      𝕍 := NullMeasurableSpace Ωg Pg
      V := Prod.snd
      hV := measurable_snd
      D := fun z => pathOf b z.1
      hD := hD
      hDm := hDm
      hDc := fun z => hbc z.1
      u₀ := 1
      hu₀ := one_pos
      hind := hind
      hDW := hDW
      a := fun C v => zScale (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) 1 (foldedCircle 0 2) C
        (Xg (ESM.ofCompl Pg v)) ((fun _ _ => (0 : ℝ)) v)
      ha := ha
      y := fun C v => zLoc D3Plus.locFieldFull (Real.sqrt κ) (Real.sqrt κ - 2 / Real.sqrt κ) 1
        (foldedCircle 0 2) R C (Xg (ESM.ofCompl Pg v)) ((fun _ _ => (0 : ℝ)) v)
      hy := hy
      hay := fun _ _ => ⟨rfl, rfl⟩ }⟩

end E5
end QuantumZipper
