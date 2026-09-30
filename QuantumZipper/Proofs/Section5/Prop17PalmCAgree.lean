import QuantumZipper.Proofs.Section5.Prop17PalmCField
import QuantumZipper.Proofs.Zipper.D3PlusProb
import QuantumZipper.Proofs.LQG.LogSingGood
import QuantumZipper.Proofs.LQG.IndepParams
import QuantumZipper.Proofs.Section5.Prop16LocalRule
import QuantumZipper.Proofs.Zipper.D3PlusIRich

/-!
# Proposition 1.7, Palm-zoom node C: the identification node from regularity and measurability

`prop17PalmCAgree_of`: the identification node `Prop17PalmCAgreeStmt γ` follows from

* `Prop17PalmCRegStmt γ` (**regularity**): a.s. the Palm-shifted field `N_ϖ(s + X)` is regular
  (`evalReg = raw value`) at every translated dyadic folded circle `fc(dyadicRoundC n z, radius k)(· − x)`;
* `Prop17PalmCMeasStmt γ` (**measurability**): the Palm zoom coordinates at `x` and the local scale
  of the D3⁺ model field are a.e.-measurable.

Route (own bookkeeping, the E5-LOC switch `canonical ↔ canonicalOn` of `E5Model2`):
on the regularity event the zoomed Palm field `y` agrees with the D3⁺ model field `y'` and with the
split field `(X' + γ(−log‖·‖)) + (g + const)` at all dyadic folded circles
(`zoomField_palm_eq_zoomModel`, `zoomField_palm_eq_split`); the split field is a.s. good
(`LogSingGood.logSingGoodAS_holds` for the translated free field, `α = γ < Q`, plus a continuous
function, `IndepParams.ae_isLQGGood_add_ofFun`), so `y` has a global area limit; when the local
scale of `y'` lies in `(0, 1/(R+1))`, `E5.locFieldFull_canonical_eq_canonicalOn` identifies the
global canonical data of `y` with the local canonical data of `y'` inside `closedBall 0 R`. The
bad-scale probability tends to `0` by D3⁺(iii) (`D3Plus.d3PlusIII_tendsto_prob`, proved).

`prop17FreeFixedZoom_of_D3PlusI` is node C for all `0 < γ < 2` from D3⁺(i) (rich form) and the two
nodes above.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal ComplexConjugate

namespace QuantumZipper
namespace S5
namespace FieldLaw
namespace Raw

open WedgeMeas Factorization CoordsFull TV PalmShift FieldShift PalmNorm

/-- **Regularity node.** A.s. the Palm-shifted field is regular at every translated dyadic folded
circle. -/
def Prop17PalmCRegStmt (γ : ℝ) : Prop :=
  ∀ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (X : Ω' → FieldSample),
    IsProbabilityMeasure P' → IsFreeGFFModConstH X P' → ∀ x ∈ Icc (0 : ℝ) 1,
      ∀ᵐ ω ∂P', ∀ (n k : ℕ) (z : ℂ),
        evalReg (palmFreeField γ (foldedCircle 0 3) X x ω)
          ((foldedCircle (dyadicRoundC n z) (radius k)).map (· + (x : ℂ))) =
        palmFreeField γ (foldedCircle 0 3) X x ω
          ((foldedCircle (dyadicRoundC n z) (radius k)).map (· + (x : ℂ)))

/-- **Measurability node.** The Palm zoom coordinates at `x` and the local scale of the D3⁺
model field are a.e.-measurable. -/
def Prop17PalmCMeasStmt (γ : ℝ) : Prop :=
  ∀ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (X : Ω' → FieldSample),
    IsProbabilityMeasure P' → IsFreeGFFModConstH X P' → ∀ x ∈ Icc (0 : ℝ) 1,
      (∀ C : ℝ, AEMeasurable (fun ω => palmZoomCoords γ C (foldedCircle 0 3) X (ω, x)) P') ∧
      ∀ C : ℝ, AEMeasurable (fun ω => scaleParamOn γ
        (D3Plus.zoomModel γ γ C (palmCRho (foldedCircle 0 3) x) (palmCField X x ω)
          (palmCCorr γ (foldedCircle 0 3) x)) (D3Plus.halfDisc 1)) P'

/-- **The identification node from regularity and measurability.** -/
theorem prop17PalmCAgree_of {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hReg : Prop17PalmCRegStmt γ)
    (hMeas : Prop17PalmCMeasStmt γ) : Prop17PalmCAgreeStmt γ := by
  intro Ω' _ P' X hP hX x hx
  have := hP
  obtain ⟨hA, hSc⟩ := hMeas Ω' _ P' X hP hX x hx
  refine ⟨hA, fun R => ?_⟩
  set ϖ : Measure ℂ := foldedCircle 0 3 with hϖ
  set sc : ℝ → Ω' → ℝ := fun C ω => scaleParamOn γ
    (D3Plus.zoomModel γ γ C (palmCRho ϖ x) (palmCField X x ω) (palmCCorr γ ϖ x))
    (D3Plus.halfDisc 1) with hsc
  have hε : (0 : ℝ) < 1 / ((R : ℝ) + 1) := by positivity
  have hS0 := palmC_setup hγ hγ2 hX hx
  have hbad : Tendsto (fun C => P' {ω | ¬ (0 < sc C ω ∧ sc C ω < 1 / ((R : ℝ) + 1))}) atTop
      (𝓝 0) := by
    refine tendsto_of_seq_tendsto fun Cs hCs => ?_
    exact D3Plus.d3PlusIII_tendsto_prob hS0 hCs hε fun n =>
      (hSc (Cs n)).nullMeasurable measurableSet_Ioo.compl
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbad
    (fun _ => bot_le) fun C => measure_mono_ae ?_
  have hgood := LogSingGood.logSingGoodAS_holds hγ hγ2 (gamma_lt_Qc' hγ hγ2) Ω' _ P'
    (palmCField X x) hP (isFreeGFFModConstH_translate hX x)
  have hgood2 := IndepParams.ae_isLQGGood_add_ofFun (γ := γ) hgood
    (g := fun ω z => palmCCorr γ ϖ x z + (C / γ - X ω ϖ))
    fun ω => ((continuous_palmCCorr γ x).add continuous_const).continuousOn
  filter_upwards [hReg Ω' _ P' X hP hX x hx, hgood2] with ω hreg hg hE
  by_contra hb
  obtain ⟨hpos, hlt⟩ := hb
  apply hE
  set y := zoomField γ C (palmFreeField γ ϖ X x ω) x with hy
  set y' := D3Plus.zoomModel γ γ C (palmCRho ϖ x) (palmCField X x ω) (palmCCorr γ ϖ x)
    with hy'
  have hag : D3Plus.AgreeNear y y' 1 := fun n k z _ =>
    zoomField_palm_eq_zoomModel (radius_pos k) (hreg n k z)
  have hArea : areaApprox γ y = areaApprox γ (palmCSplit γ C x X ω) :=
    areaApprox_eq_of_agree fun n k z => zoomField_palm_eq_split (radius_pos k) (hreg n k z)
  have hvag : IsVagueLimitOn H (areaApprox γ y) (qAreaMeasure γ (palmCSplit γ C x X ω)) := by
    rw [hArea]
    exact Prop16Area.G.isVagueLimitOn_H_of_good hg.1
  have hlt' : scaleParamOn γ y' (D3Plus.halfDisc 1) * ((R : ℝ) + 1) < 1 := by
    have hR1 : (0 : ℝ) < (R : ℝ) + 1 := by positivity
    have := (lt_div_iff₀ hR1).1 hlt
    simpa [hsc] using this
  obtain ⟨-, hloc⟩ := E5.locFieldFull_canonical_eq_canonicalOn hag hvag hpos hlt'
  show locFull R (coordsFull (canonical γ y)) =
    (D3Plus.locFieldFull R (canonicalOn γ y' (D3Plus.halfDisc 1))).1
  rw [← palmC_locFieldFull_fst, hloc]

/-- **Node C (Prop. 1.7) from D3⁺(i) (rich form), regularity and measurability.** -/
theorem prop17FreeFixedZoom_of_D3PlusI (hI : D3Plus.D3PlusIStmtRich)
    (hReg : ∀ γ : ℝ, 0 < γ → γ < 2 → Prop17PalmCRegStmt γ)
    (hMeas : ∀ γ : ℝ, 0 < γ → γ < 2 → Prop17PalmCMeasStmt γ) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → Prop17FreeFixedZoomStmt γ (foldedCircle 0 3) 0 1 :=
  fun γ hγ hγ2 => prop17FreeFixedZoom_of_agree hγ hγ2 hI
    (prop17PalmCAgree_of hγ hγ2 (hReg γ hγ hγ2) (hMeas γ hγ hγ2))

end Raw
end FieldLaw
end S5
end QuantumZipper
