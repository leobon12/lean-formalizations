import QuantumZipper.Proofs.LQG.WedgeToolkit
import QuantumZipper.Proofs.LQG.WedgeMeasurable
import QuantumZipper.Proofs.LQG.ZoomRadialFinal
import QuantumZipper.Proofs.LQG.CoordChangeW
import QuantumZipper.Proofs.LQG.WedgeCanonical4

/-!
# B4(d) for the reference wedge: the law part

Theorem 1.3, node F1d input (c) (Sheffield, arXiv:1012.4797, §1.6 and §5.4 p. 72: "by
symmetry"). Let `W = h† + Q(−log|·|) + A_{−log|·|}` be the (uncanonicalized) reference wedge
field built from a free-boundary GFF `X` and an independent wedge radial process `A`, and let
`Wσ` be the same field built from the reflected GFF `X(−·̄)` (same `A`). This file proves that the
data `fieldLawFull H` of `canonical γ Wσ` has the law of the data of `canonical γ W`:

* `coords_wedgeField_eq`: for a continuous radial path `a`, the dyadic coordinates of
  `wedgeField y a Q` are a *measurable* function `coordsW Q` of the full circle coordinates of `y`
  and the path `a` (the path is read through its dyadic values, `pathExt`).
* `map_coords_wedgeField_reflect`: `coords Wσ` has the law of `coords W` (independence of the
  lateral part and `A`, and B4(d) for the lateral part, `WedgeTK.fieldLawFull_lateralPart_reflect`).
* `map_dataFull_canonical_eq`: equal coordinate laws give equal canonical data laws (the
  canonical data is a measurable function of the coordinates on good samples, and goodness is a
  measurable event of the coordinates).

All arguments are own elementary arguments (the paper only says "by symmetry").
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ComplexConjugate

namespace QuantumZipper
namespace F1
namespace B4d

open Factorization CoordsFull

/-! ## 1. Continuous paths are read through their dyadic values -/

theorem measurable_dyadicRound' (n : ℕ) : Measurable (dyadicRound n) := by
  unfold dyadicRound
  exact ((measurable_from_top : Measurable (Int.cast : ℤ → ℝ)).div_const ((2 : ℝ) ^ n)).comp
    (Measurable.floor (measurable_id.const_mul ((2 : ℝ) ^ n)))

theorem countable_range_dyadicRound (n : ℕ) : (Set.range (dyadicRound n)).Countable :=
  (Set.countable_range (fun k : ℤ => (k : ℝ) / (2 : ℝ) ^ n)).mono (by
    rintro _ ⟨t, rfl⟩; exact ⟨⌊(2 : ℝ) ^ n * t⌋, rfl⟩)

theorem measurable_eval_dyadicRound (n : ℕ) :
    Measurable fun p : (ℝ → ℝ) × ℝ => p.1 (dyadicRound n p.2) := by
  have : Countable (Set.range (dyadicRound n)) := (countable_range_dyadicRound n).to_subtype
  intro T hT
  have key : (fun p : (ℝ → ℝ) × ℝ => p.1 (dyadicRound n p.2)) ⁻¹' T =
      ⋃ d : Set.range (dyadicRound n),
        {a : ℝ → ℝ | a d ∈ T} ×ˢ (dyadicRound n ⁻¹' {(d : ℝ)}) := by
    ext ⟨a, t⟩
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_prod, Set.mem_ofPred_eq,
      Set.mem_singleton_iff]
    constructor
    · intro h; exact ⟨⟨dyadicRound n t, Set.mem_range_self t⟩, h, rfl⟩
    · rintro ⟨d, h, hd⟩; rwa [hd]
  rw [key]
  exact MeasurableSet.iUnion fun d =>
    (measurable_pi_apply (d : ℝ) hT).prod (measurable_dyadicRound' n (measurableSet_singleton _))

/-- A path read through its values at dyadic times (the limit of `a` along the dyadic
roundings; junk `0` if it does not exist). -/
def pathExt (a : ℝ → ℝ) (t : ℝ) : ℝ := limUnder atTop fun n => a (dyadicRound n t)

theorem measurable_pathExt : Measurable fun p : (ℝ → ℝ) × ℝ => pathExt p.1 p.2 :=
  (StronglyMeasurable.limUnder fun n =>
    (measurable_eval_dyadicRound n).stronglyMeasurable).measurable

theorem pathExt_of_continuous {a : ℝ → ℝ} (ha : Continuous a) : pathExt a = a := by
  funext t
  exact ((ha.tendsto t).comp (CoordChange.tendsto_dyadicRound t)).limUnder_eq

/-! ## 2. The dyadic coordinates of a wedge field -/

/-- The radial contribution of a path to the dyadic coordinates of a wedge field. -/
def radCoords (Q : ℝ) (a : ℝ → ℝ) : ℕ → ℝ := fun i =>
  ∫ z, (Q * (-Real.log ‖z‖) + pathExt a (-Real.log ‖z‖))
    ∂foldedCircle (dyadicIndex i).1 (radius (dyadicIndex i).2)

theorem measurable_radCoords (Q : ℝ) : Measurable (radCoords Q) := by
  refine measurable_pi_iff.2 fun i => ?_
  have hl : Measurable fun q : (ℝ → ℝ) × ℂ => -Real.log ‖q.2‖ :=
    (Real.measurable_log.comp (measurable_norm.comp measurable_snd)).neg
  have hf : Measurable fun q : (ℝ → ℝ) × ℂ =>
      Q * (-Real.log ‖q.2‖) + pathExt q.1 (-Real.log ‖q.2‖) :=
    (measurable_const.mul hl).add (measurable_pathExt.comp (measurable_fst.prodMk hl))
  exact (StronglyMeasurable.integral_prod_right'
    (ν := foldedCircle (dyadicIndex i).1 (radius (dyadicIndex i).2)) hf.stronglyMeasurable).measurable

/-- The dyadic coordinates of `wedgeField y a Q`, from the full coordinates of `y` and `a`. -/
def coordsW (Q : ℝ) (p : (ℕ → ℝ) × (ℝ → ℝ)) : ℕ → ℝ := WedgeCan4.piC p.1 + radCoords Q p.2

theorem measurable_coordsW (Q : ℝ) : Measurable (coordsW Q) :=
  (WedgeCan4.measurable_piC.comp measurable_fst).add ((measurable_radCoords Q).comp measurable_snd)

theorem coords_wedgeField_eq (y : FieldSample) {a : ℝ → ℝ} (ha : Continuous a) (Q : ℝ) :
    coords (wedgeField y a Q) = coordsW Q (coordsFull y, a) := by
  funext i
  have h := congrFun (WedgeCan4.piC_coordsFull y) i
  simp only [coordsW, radCoords, Pi.add_apply, h, pathExt_of_continuous ha]
  rfl

/-! ## 3. The lateral coordinates of `X` and of its reflection -/

/-- Full coordinates of the lateral part. -/
def latId (x : FieldSample) : ℕ → ℝ := coordsFull (lateralPart x)

/-- Full coordinates of the lateral part of the reflection `x(−·̄)`. -/
def latRefl (x : FieldSample) : ℕ → ℝ := coordsFull (lateralPart (RegClosure.reflectH x))

theorem measurable_latId : Measurable latId :=
  measurable_pi_iff.2 fun _ => WedgeTK.measurable_lateralPart_apply _

theorem measurable_latRefl : Measurable latRefl := by
  have hY : ∀ μ : Measure ℂ, IsFiniteMeasure μ →
      Measurable fun x : FieldSample => RegClosure.reflectH x μ := fun μ hμ => by
    have := hμ
    exact measurable_evalReg (μ.map fun z => -conj z)
  exact measurable_pi_iff.2 fun _ => WedgeTK.measurable_lateral_of hY _

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem measurable_latData {Y : Ω → FieldSample}
    (hY : ∀ μ : Measure ℂ, IsFiniteMeasure μ → Measurable fun ω => Y ω μ) :
    Measurable fun ω => (coordsFull (lateralPart (Y ω)),
      fun ρ : TestFun H => pairRaw (lateralPart (Y ω)) ρ.1) :=
  (MeasurableEquiv.sumPiEquivProdPi fun _ : WedgeTK.LatIdx => ℝ).measurable.comp
    (WedgeTK.measurable_latCoords hY)

theorem map_latRefl_eq [IsProbabilityMeasure P] {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P) :
    P.map (fun ω => latRefl (X ω)) = P.map (fun ω => latId (X ω)) := by
  have h := congrArg (fun m => m.map Prod.fst) (WedgeTK.fieldLawFull_lateralPart_reflect hX)
  simp only [fieldLawFull] at h
  rw [Measure.map_map measurable_fst (measurable_latData (WedgeTK.hY_reflect hX)),
    Measure.map_map measurable_fst (measurable_latData (WedgeTK.hY_X hX))] at h
  exact h

/-! ## 4. The coordinate law of the reflected reference wedge -/

theorem coords_wedgeField_ae_eq {Y : Ω → FieldSample} {A : ℝ → Ω → ℝ} {α Q : ℝ}
    (hA : IsWedgeProcess α Q A P) :
    (fun ω => coords (wedgeField (lateralPart (Y ω)) (fun t => A t ω) Q)) =ᵐ[P]
      fun ω => coordsW Q (coordsFull (lateralPart (Y ω)), fun t => A t ω) := by
  filter_upwards [WedgeCan4.ae_continuous_wedgeProcess hA] with ω hω
  exact coords_wedgeField_eq _ hω Q

theorem aemeasurable_coords_wedgeField_reflect [IsProbabilityMeasure P] {X : Ω → FieldSample} {A : ℝ → Ω → ℝ} {α Q : ℝ}
    (hX : IsFreeGFFModConstH X P) (hA : IsWedgeProcess α Q A P) :
    AEMeasurable (fun ω =>
      coords (wedgeField (lateralPart (RegClosure.reflectH (X ω))) (fun t => A t ω) Q)) P :=
  ((measurable_coordsW Q).comp_aemeasurable
    ((measurable_latRefl.comp (WedgeTK.measurable_X_pi hX)).aemeasurable.prodMk
      (ZoomRadial.aemeasurable_wedgePath hA))).congr
    (coords_wedgeField_ae_eq (Y := fun ω => RegClosure.reflectH (X ω)) hA).symm

/-- **The coordinate law of the reflected reference wedge.** Building the wedge field from the
reflected GFF `X(−·̄)` instead of `X` (same radial process `A`) does not change the law of its
dyadic coordinates. -/
theorem map_coords_wedgeField_reflect [IsProbabilityMeasure P] {X : Ω → FieldSample} {A : ℝ → Ω → ℝ} {α Q : ℝ}
    (hX : IsFreeGFFModConstH X P) (hA : IsWedgeProcess α Q A P)
    (hI : IndepFun X (fun ω t => A t ω) P) :
    P.map (fun ω =>
        coords (wedgeField (lateralPart (RegClosure.reflectH (X ω))) (fun t => A t ω) Q)) =
      P.map (fun ω => coords (wedgeField (lateralPart (X ω)) (fun t => A t ω) Q)) := by
  have hXm := WedgeTK.measurable_X_pi hX
  have hAm : AEMeasurable (fun ω t => A t ω) P := ZoomRadial.aemeasurable_wedgePath hA
  have c1 : (fun ω =>
      coords (wedgeField (lateralPart (RegClosure.reflectH (X ω))) (fun t => A t ω) Q)) =ᵐ[P]
      fun ω => coordsW Q (coordsFull (lateralPart (RegClosure.reflectH (X ω))), fun t => A t ω) :=
    coords_wedgeField_ae_eq (Y := fun ω => RegClosure.reflectH (X ω)) hA
  have c2 : (fun ω => coords (wedgeField (lateralPart (X ω)) (fun t => A t ω) Q)) =ᵐ[P]
      fun ω => coordsW Q (coordsFull (lateralPart (X ω)), fun t => A t ω) :=
    coords_wedgeField_ae_eq hA
  rw [Measure.map_congr c1, Measure.map_congr c2]
  have hr : AEMeasurable (fun ω => latRefl (X ω)) P := (measurable_latRefl.comp hXm).aemeasurable
  have hi : AEMeasurable (fun ω => latId (X ω)) P := (measurable_latId.comp hXm).aemeasurable
  have e1 : (fun ω => coordsW Q (coordsFull (lateralPart (RegClosure.reflectH (X ω))),
      fun t => A t ω)) = coordsW Q ∘ fun ω => (latRefl (X ω), fun t => A t ω) := rfl
  have e2 : (fun ω => coordsW Q (coordsFull (lateralPart (X ω)), fun t => A t ω)) =
      coordsW Q ∘ fun ω => (latId (X ω), fun t => A t ω) := rfl
  rw [e1, e2, ← AEMeasurable.map_map_of_aemeasurable (measurable_coordsW Q).aemeasurable
      (hr.prodMk hAm),
    ← AEMeasurable.map_map_of_aemeasurable (measurable_coordsW Q).aemeasurable (hi.prodMk hAm)]
  have hi1 : IndepFun (fun ω => latRefl (X ω)) (fun ω t => A t ω) P :=
    (hI.comp measurable_latRefl measurable_id :)
  have hi2 : IndepFun (fun ω => latId (X ω)) (fun ω t => A t ω) P :=
    (hI.comp measurable_latId measurable_id :)
  rw [(indepFun_iff_map_prod_eq_prod_map_map hr hAm).1 hi1,
    (indepFun_iff_map_prod_eq_prod_map_map hi hAm).1 hi2, map_latRefl_eq hX]

/-! ## 5. Equal coordinate laws give equal canonical data laws -/

/-- The canonical data as a measurable function of the dyadic coordinates (on good samples). -/
def phiC (γ : ℝ) (c : ℕ → ℝ) : (ℕ → ℝ) × (TestFun H → ℝ) :=
  WedgeMeas.dataFull H (WedgeMeas.resc (Qc γ) (c, WedgeMeas.scaleG γ c))

theorem measurable_phiC (γ : ℝ) : Measurable (phiC γ) :=
  (WedgeMeas.measurable_dataFull_resc H (Qc γ)).comp
    (measurable_id.prodMk (WedgeMeas.measurable_scaleG γ))

theorem dataFull_canonical_eq {γ : ℝ} {x : FieldSample} (hx : IsLQGGood γ x) :
    WedgeMeas.dataFull H (canonical γ x) = phiC γ (coords x) := by
  simp only [phiC, WedgeMeas.canonical_eq_resc, WedgeMeas.scaleG_coords hx]

/-- The good event, read on the dyadic coordinates. -/
def goodSet (γ : ℝ) : Set (ℕ → ℝ) := {c | IsLQGGood γ (reconstruct c)}

theorem measurableSet_goodSet (γ : ℝ) : MeasurableSet (goodSet γ) :=
  measurable_reconstruct (GoodMeas.measurableSet_isLQGGood γ)

theorem coords_mem_goodSet_iff (γ : ℝ) (x : FieldSample) :
    coords x ∈ goodSet γ ↔ IsLQGGood γ x :=
  GoodSample.isLQGGood_iff_reconstruct γ x

theorem ae_good_of_map_coords_eq {γ : ℝ} {W₁ W₂ : Ω → FieldSample}
    (h1 : AEMeasurable (fun ω => coords (W₁ ω)) P) (h2 : AEMeasurable (fun ω => coords (W₂ ω)) P)
    (hlaw : P.map (fun ω => coords (W₁ ω)) = P.map (fun ω => coords (W₂ ω)))
    (hg : ∀ᵐ ω ∂P, IsLQGGood γ (W₂ ω)) : ∀ᵐ ω ∂P, IsLQGGood γ (W₁ ω) := by
  have hg' : ∀ᵐ c ∂P.map (fun ω => coords (W₂ ω)), c ∈ goodSet γ :=
    (ae_map_iff h2 (measurableSet_goodSet γ)).2
      (hg.mono fun ω h => (coords_mem_goodSet_iff γ _).2 h)
  rw [← hlaw] at hg'
  exact ((ae_map_iff h1 (measurableSet_goodSet γ)).1 hg').mono fun ω h =>
    (coords_mem_goodSet_iff γ _).1 h

theorem map_dataFull_canonical_eq {γ : ℝ} {W₁ W₂ : Ω → FieldSample}
    (h1 : AEMeasurable (fun ω => coords (W₁ ω)) P) (h2 : AEMeasurable (fun ω => coords (W₂ ω)) P)
    (hlaw : P.map (fun ω => coords (W₁ ω)) = P.map (fun ω => coords (W₂ ω)))
    (hg : ∀ᵐ ω ∂P, IsLQGGood γ (W₂ ω)) :
    P.map (fun ω => WedgeMeas.dataFull H (canonical γ (W₁ ω))) =
      P.map (fun ω => WedgeMeas.dataFull H (canonical γ (W₂ ω))) := by
  have hg1 := ae_good_of_map_coords_eq h1 h2 hlaw hg
  rw [Measure.map_congr (hg1.mono fun ω h => dataFull_canonical_eq h),
    Measure.map_congr (hg.mono fun ω h => dataFull_canonical_eq h)]
  have e1 : (fun ω => phiC γ (coords (W₁ ω))) = phiC γ ∘ fun ω => coords (W₁ ω) := rfl
  have e2 : (fun ω => phiC γ (coords (W₂ ω))) = phiC γ ∘ fun ω => coords (W₂ ω) := rfl
  rw [e1, e2, ← AEMeasurable.map_map_of_aemeasurable (measurable_phiC γ).aemeasurable h1,
    ← AEMeasurable.map_map_of_aemeasurable (measurable_phiC γ).aemeasurable h2, hlaw]

end B4d
end F1
end QuantumZipper
