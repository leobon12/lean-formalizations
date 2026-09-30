import QuantumZipper.Proofs.Thm18.G3ZcCore
import QuantumZipper.Proofs.Zipper.D3PlusN1Scale
import QuantumZipper.Proofs.Zipper.MeasUnzipZip

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZOOM-C (c)/(d): the local canonical data are a measurable function of countably many circles

For the two-point decorrelation (`twoPoint_of_agree`, G3ZcCore) the second zoom's functional must
be measurable for the conditioning σ-algebra of the first point, and for the transfer of the
one-point cores between free fields the zoom functionals must be functions of countably many
coordinates. Both follow from:

`locFieldFull_canonicalOn_eq_dyad`: for every field `y` whose local scale on `halfDisc r` lies in
`(0, r/R)`,

  `locFieldFull R (canonicalOn γ y (halfDisc r)) = dyadT γ r R (dyadData r y)`,

where `dyadData r y` are the values of `y` at the countably many dyadic folded circles inside
`ball 0 r` (the circles read by `AgreeNear`) and `dyadT γ r R` is a **measurable** map
(`measurable_dyadT`). Construction: a field `dyadField r ξ` with the prescribed dyadic values
(junk `0` elsewhere) agrees with `y` near `0`, so it has the same local area measure and scale
(`scaleParamOn_halfDisc_congr`) and the same local canonical data
(`locFieldFull_canonicalOn_congr`); its scale is the measurable surrogate `dyadScale` (an `sInf`
over rationals of bump-function integrals, as `D3Plus.scaleSur`), which equals `scaleParamOn` on
good samples (`Prop16Area.Meas.measure_eq_M`).

Own bookkeeping (AGENT_GUIDE cost rule) on the measurability machinery of Prop. 1.6
(`Prop16MeasScale`, `D3PlusN1Scale`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace G3Cv

open D3Plus

/-- Indices of the dyadic folded circles: `(n, k, p, q)` ↦ circle of radius `2^{-k}` centred at
`(p + i q)/2^n`. -/
abbrev DyIdx : Type := ℕ × ℕ × ℤ × ℤ

/-- The centre of the dyadic circle `i`. -/
def dyC (i : DyIdx) : ℂ := ⟨(i.2.2.1 : ℝ) / (2 : ℝ) ^ i.1, (i.2.2.2 : ℝ) / (2 : ℝ) ^ i.1⟩

/-- The dyadic circle `i`. -/
def dyCirc (i : DyIdx) : Measure ℂ := foldedCircle (dyC i) (radius i.2.1)

/-- The dyadic circles inside `ball 0 r`. -/
abbrev DyIdxIn (r : ℝ) : Type := {i : DyIdx // ‖dyC i‖ + radius i.2.1 < r}

/-- The dyadic data of a field near `0`. -/
def dyadData (r : ℝ) (y : FieldSample) : DyIdxIn r → ℝ := fun i => y (dyCirc i.1)

open Classical in
/-- A field with prescribed dyadic data near `0` (junk `0` elsewhere). -/
def dyadField (r : ℝ) (ξ : DyIdxIn r → ℝ) : FieldSample := fun μ =>
  if h : ∃ i : DyIdxIn r, dyCirc i.1 = μ then ξ h.choose else 0

theorem measurable_dyadField (r : ℝ) : Measurable (dyadField r) := by
  classical
  refine measurable_pi_iff.2 fun μ => ?_
  unfold dyadField
  by_cases h : ∃ i : DyIdxIn r, dyCirc i.1 = μ
  · simp only [h, dite_true]; exact measurable_pi_apply _
  · simp only [h, dite_false]; exact measurable_const

theorem measurable_dyadData (r : ℝ) : Measurable (dyadData r) :=
  measurable_pi_iff.2 fun i => measurable_pi_apply _

/-- The reconstructed field agrees with `y` near `0`. -/
theorem agreeNear_dyadField (r : ℝ) (y : FieldSample) :
    AgreeNear y (dyadField r (dyadData r y)) r := by
  classical
  intro n k z hz
  set i : DyIdx := (n, k, ⌊(2 : ℝ) ^ n * z.re⌋, ⌊(2 : ℝ) ^ n * z.im⌋) with hi
  have hc : dyC i = dyadicRoundC n z := rfl
  have hin : ‖dyC i‖ + radius i.2.1 < r := by rw [hc]; exact hz
  have hex : ∃ j : DyIdxIn r, dyCirc j.1 = foldedCircle (dyadicRoundC n z) (radius k) :=
    ⟨⟨i, hin⟩, by rw [dyCirc, hc]⟩
  simp only [dyadField, hex, dite_true, dyadData]
  exact congrArg y hex.choose_spec.symm

/-- The bump family exhausting `halfDisc r`, over the dyadic data space. -/
def dyBump (r : ℝ) : ℕ → (DyIdxIn r → ℝ) → ℂ → ℝ := fun n _ z =>
  LQGMeas.openBump (halfDisc r) n z

theorem isBumpFamily_dyBump (r : ℝ) :
    Prop16Area.Meas.IsBumpFamily (fun _ : DyIdxIn r → ℝ => halfDisc r) (dyBump r) :=
  Prop16Area.Meas.isBumpFamily_comp (isOpen_halfDisc r) ⟨0, fun h => by simpa [H] using h.2⟩
    (g := fun _ z => z) measurable_snd (fun _ => continuous_id)

/-- The measurable surrogate of the local scale of the reconstructed field. -/
def dyadScale (γ r : ℝ) (ξ : DyIdxIn r → ℝ) : ℝ :=
  sInf {a : ℝ | ∃ q : ℚ, 0 < (q : ℝ) ∧ (q : ℝ) ≤ a ∧
    1 ≤ Prop16Area.Meas.M γ (dyadField r) (dyBump r) ξ q}

theorem measurable_dyadScale (γ r : ℝ) : Measurable (dyadScale γ r) := by
  refine LQGMeas.measurable_sInf_upClosed _ (fun q' => ?_)
    (fun p a b ⟨q, h0, hqa, h1⟩ hab => ⟨q, h0, hqa.trans hab, h1⟩)
    (fun p a ⟨q, h0, hqa, _⟩ => h0.trans_le hqa)
  have e : {p : DyIdxIn r → ℝ | ((q' : ℚ) : ℝ) ∈ {a : ℝ | ∃ q : ℚ, 0 < (q : ℝ) ∧ (q : ℝ) ≤ a ∧
      1 ≤ Prop16Area.Meas.M γ (dyadField r) (dyBump r) p q}} =
      ⋃ q : ℚ, {_p : DyIdxIn r → ℝ | 0 < (q : ℝ) ∧ (q : ℝ) ≤ q'} ∩
        {p | 1 ≤ Prop16Area.Meas.M γ (dyadField r) (dyBump r) p q} := by
    ext p
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff, and_assoc]
  rw [e]
  exact MeasurableSet.iUnion fun q => (MeasurableSet.const _).inter
    (measurableSet_le measurable_const (Prop16Area.Meas.measurable_M (γ := γ)
      (measurable_dyadField r) (isBumpFamily_dyBump r) q))

theorem dyadScale_eq {γ r : ℝ} {ξ : DyIdxIn r → ℝ}
    (hp : ξ ∈ Prop16Area.Meas.goodSet γ (dyadField r) (fun _ => halfDisc r)) :
    dyadScale γ r ξ = scaleParamOn γ (dyadField r ξ) (halfDisc r) := by
  have hM : ∀ q : ℝ, Prop16Area.Meas.M γ (dyadField r) (dyBump r) ξ q =
      qAreaMeasureOn γ (dyadField r ξ) (halfDisc r) (Metric.ball 0 q ∩ H) := fun q =>
    (Prop16Area.Meas.measure_eq_M (isBumpFamily_dyBump r) hp q).symm
  have hmono : Monotone fun a : ℝ =>
      qAreaMeasureOn γ (dyadField r ξ) (halfDisc r) (Metric.ball 0 a ∩ H) := fun a b h =>
    measure_mono (inter_subset_inter_left _ (Metric.ball_subset_ball h))
  simp only [dyadScale, scaleParamOn, hM]
  exact sInf_rat_eq hmono

/-- The measurable factorization map of the local canonical data. -/
def dyadT (γ r : ℝ) (R : ℕ) (ξ : DyIdxIn r → ℝ) : (ℕ → ℝ) × (TestFun H → ℝ) :=
  locFieldFull R (rescale (dyadField r ξ) (Qc γ) (dyadScale γ r ξ))

theorem measurable_dyadT (γ r : ℝ) (R : ℕ) : Measurable (dyadT γ r R) := by
  have h1 : Measurable fun ξ : DyIdxIn r → ℝ => (ξ, dyadScale γ r ξ) :=
    measurable_id.prodMk (measurable_dyadScale γ r)
  have h2 : Measurable fun q : (DyIdxIn r → ℝ) × ℝ =>
      locFieldFull R (rescale (dyadField r q.1) (Qc γ) q.2) :=
    MeasUnzip.measurable_locFieldFull_rescale (measurable_dyadField r) (Qc γ) R
  exact Measurable.comp (g := fun q : (DyIdxIn r → ℝ) × ℝ =>
      locFieldFull R (rescale (dyadField r q.1) (Qc γ) q.2))
    (f := fun ξ : DyIdxIn r → ℝ => (ξ, dyadScale γ r ξ)) h2 h1

/-- **The local canonical data factor measurably through the dyadic data** (when the local scale
is in `(0, r/R)`). -/
theorem locFieldFull_canonicalOn_eq_dyad {γ r : ℝ} {R : ℕ} {y : FieldSample}
    (ha : 0 < scaleParamOn γ y (halfDisc r)) (haR : scaleParamOn γ y (halfDisc r) * R < r) :
    locFieldFull R (canonicalOn γ y (halfDisc r)) = dyadT γ r R (dyadData r y) := by
  have hag := agreeNear_dyadField r y
  have hs := scaleParamOn_halfDisc_congr (γ := γ) hag
  have ha' : 0 < scaleParamOn γ (dyadField r (dyadData r y)) (halfDisc r) := by
    rw [← hs]; exact ha
  have haR' : scaleParamOn γ (dyadField r (dyadData r y)) (halfDisc r) * R < r := by
    rw [← hs]; exact haR
  have hgood : dyadData r y ∈
      Prop16Area.Meas.goodSet γ (dyadField r) (fun _ => halfDisc r) := by
    by_contra hp
    rw [Prop16Area.Meas.scaleParamOn_of_not hp] at ha'
    exact lt_irrefl _ ha'
  rw [locFieldFull_canonicalOn_congr hag ha' haR']
  unfold dyadT canonicalOn
  rw [dyadScale_eq hgood]

end G3Cv
end QuantumZipper
