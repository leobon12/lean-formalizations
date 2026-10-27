/- Provenance: ported from an earlier mating-of-trees formalization; only imports and namespace names were changed. -/
import MatedCRTHarmonic.MoTPort.Foundations.ConeArea
import MatedCRTHarmonic.MoTPort.Foundations.Params
import QuantumZipper.LQG.WedgeProcess
import QuantumZipper.Proofs.NonVacuity
import QuantumZipper.Proofs.Probability.BMExistence
import LQGMetric.Field.ExistGFF
import LQGMetric.Papers.DFGPS.L2_17Core2H

/-!
# Quantum cones (DMS Def 4.10)

DMS (arXiv:1409.7055v4) Def `def::quantum_cone` (L2198–2201): for `α < Q`, the
`α`-quantum cone is the field `h` on `ℂ` whose average on `∂B(0,e^{-s})` is `A_s`, with `A_s` as
in Def 4.5 (L2071) "except with `B_{2s}` and `B̂_{2s}` replaced by `B_s` and `B̂_s`", and whose
lateral part (projection onto `H₂(ℂ)`, Lemma `lem::c_spaces_orthogonal` L2187) is that of a
whole-plane GFF. Weight `W = 2γ(Q − α)` (Table 1.2, DMS (1.?) `eqn::quantum_cone_weight`; our
`coneAlpha γ W = Q − W/(2γ)`, Params.lean).

* `conePath α Q b b'` is a thin layer over QuantumZipper's `wedgePath` (QZ/LQG/WedgeProcess.lean)
  by Brownian scaling: `wedgePath (Q + 2(α−Q)) Q (b(2·)/√2) (b'(2·)/√2) (t/2)`. In QZ's convention
  (`t = −log|z|`, circle average at radius `e^{-t}` equal to `Q t + A_t`) it is `b_t + (α−Q)t` for
  `t ≥ 0` (`conePath_of_nonneg`; so `Q t + A_t = b_t + α t`, DMS's `B_s + αs`) and the
  last-zero-normalized path `b'_s + (Q−α)s` for `t < 0` (`conePath_of_neg`).
* `IsConeProcess` copies the shape of QZ's `IsWedgeProcess`; `isWedgeProcess_of_isConeProcess`:
  a cone process run at twice the speed is a QZ wedge process with `α' = Q + 2(α−Q)` (mathlib
  `IsBrownianReal.smul`).
* `coneField y A Q = y + (Q(−log|·|) + A_{−log|·|})` (the `Field` analogue of QZ `wedgeField`).
* `IsQuantumCone γ W Y P`: the law of `Y` up to dilation and rotation (`surfLawC`, ConeArea.lean)
  is that of `coneField (lateralPartC X) A Q` with `X` a whole-plane GFF (LM `IsWholePlaneGFF`)
  and `A` an independent cone process. The same canonicalization makes DMS's choice of embedding
  (circle-average embedding) irrelevant, exactly as for QZ's `IsQuantumWedge`.
* `exists_isQuantumCone`: for every `W > 0` there is a quantum cone, given the open node C.meas
  (`ConeRefMeas`, needed for the measurability guards of `IsQuantumCone`) (construction as in
  WedgeExist.lean / QZ `NonVacuity`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal Pointwise

namespace MatedCRTHarmonic.MoTPort

open QuantumZipper LQGMetric

/-- the cone radial path (DMS Def 4.10: Def 4.5 with `B_{2s}` replaced by `B_s`), QZ convention:
`QZ.wedgePath` of the Brownian-rescaled paths, run at half speed -/
def conePath (α Q : ℝ) (b b' : ℝ≥0 → ℝ) : ℝ → ℝ :=
  fun t => wedgePath (Q + 2 * (α - Q)) Q (fun s => (√2)⁻¹ * b (2 * s))
    (fun s => (√2)⁻¹ * b' (2 * s)) (t / 2)

/-- the `∞`-side path `b'_s − (α−Q)s` of the cone, before the last-zero shift -/
def coneTail (α Q : ℝ) (b' : ℝ≥0 → ℝ) : ℝ → ℝ := fun s => b' s.toNNReal - (α - Q) * s

/-- `A` is the radial process of an `α`-quantum cone: `conePath` of two independent standard
Brownian motions (shape of QZ `IsWedgeProcess`) -/
def IsConeProcess {Ω : Type*} [MeasurableSpace Ω] (α Q : ℝ) (A : ℝ → Ω → ℝ) (P : Measure Ω) :
    Prop :=
  ∃ B B' : ℝ≥0 → Ω → ℝ, IsBrownianReal B P ∧ IsBrownianReal B' P ∧
    IndepFun (pathOf B) (pathOf B') P ∧
    ∀ ω t, A t ω = conePath α Q (fun s => B s ω) (fun s => B' s ω) t

/-- the cone field on `ℂ`: `y + Q(−log|·|) + A_{−log|·|}` (the `Field` analogue of QZ `wedgeField`) -/
def coneField (y : Field) (A : ℝ → ℝ) (Q : ℝ) : Field :=
  y + ofFunC fun z => Q * (-Real.log ‖z‖) + A (-Real.log ‖z‖)

/-- the map whose law is `surfLawC γ Y P`: `(ω, θ) ↦ rotateField θ (canonicalC γ (Y ω))` -/
def surfMapC (γ : ℝ) {Ω : Type*} (Y : Ω → Field) : Ω × ℝ → Field :=
  fun p => rotateField p.2 (canonicalC γ (Y p.1))

theorem surfLawC_eq_map (γ : ℝ) {Ω : Type*} [MeasurableSpace Ω] (Y : Ω → Field) (P : Measure Ω) :
    surfLawC γ Y P = (P.prod unifAngle).map (surfMapC γ Y) := rfl

/-- **`α`-quantum cone of weight `W > 0`** (DMS Def 4.10, `α = coneAlpha γ W`), as a plane-like
surface: its law up to dilation and rotation is that of the cone field built from the lateral part
of a whole-plane GFF and an independent cone radial process.

Measurability guards: `Measure.map` of a non-a.e.-measurable
map is a Dirac mass in this mathlib pin, so the law equality is only meaningful when both compared
maps `surfMapC γ Y` and `surfMapC γ (cone field)` are a.e.-measurable; until node C.meas
(`ConeRefMeas`) is proved the two conditions are explicit conjuncts. They are not a strengthening
of DMS: a quantum cone is a random variable and its law up to rotation and dilation is a law. -/
def IsQuantumCone (γ W : ℝ) {Ω : Type*} [MeasurableSpace Ω] (Y : Ω → Field) (P : Measure Ω) :
    Prop :=
  0 < W ∧ ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (X : Ω' → Field)
    (A : ℝ → Ω' → ℝ), IsProbabilityMeasure P' ∧ IsWholePlaneGFF X P' ∧
    IsConeProcess (coneAlpha γ W) (Qc γ) A P' ∧ IndepFun X (fun ω t => A t ω) P' ∧
    AEMeasurable (surfMapC γ Y) (P.prod unifAngle) ∧
    AEMeasurable (surfMapC γ fun ω => coneField (lateralPartC (X ω)) (fun t => A t ω) (Qc γ))
      (P'.prod unifAngle) ∧
    surfLawC γ Y P = surfLawC γ (fun ω => coneField (lateralPartC (X ω)) (fun t => A t ω) (Qc γ)) P'

/-- **Measurability of the cone reference law**: the reference law map of the cone is
a.e.-measurable. Needed for `exists_isQuantumCone` now that `IsQuantumCone` carries measurability
guards. Inputs still missing: C.area-exist (a.s. vague limit defining `qAreaC` for whole-plane GFF
plus continuous fields) and joint measurability of dilation/rotation of distributions; the
generic a.e.-measurability of `qAreaC`/`scaleC` given those is `ConeMeas` (ConeMeas.lean). -/
def ConeRefMeas (γ W : ℝ) : Prop :=
  ∀ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (X : Ω' → Field) (A : ℝ → Ω' → ℝ),
    IsProbabilityMeasure P' → IsWholePlaneGFF X P' → IsConeProcess (coneAlpha γ W) (Qc γ) A P' →
    IndepFun X (fun ω t => A t ω) P' →
    AEMeasurable (surfMapC γ fun ω => coneField (lateralPartC (X ω)) (fun t => A t ω) (Qc γ))
      (P'.prod unifAngle)

namespace Cone

lemma two_mul_toNNReal (s : ℝ) : (2 : ℝ≥0) * s.toNNReal = (2 * s).toNNReal := by
  rw [Real.toNNReal_mul zero_le_two]; simp

lemma two_mul_toNNReal_half (t : ℝ) : (2 : ℝ≥0) * (t / 2).toNNReal = t.toNNReal := by
  rw [two_mul_toNNReal]; congr 1; ring

/-- for `t ≥ 0` (inside the unit disc): `A_t = b_t + (α − Q) t` -/
theorem conePath_of_nonneg (α Q : ℝ) (b b' : ℝ≥0 → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    conePath α Q b b' t = b t.toNNReal + (α - Q) * t := by
  have ht2 : 0 ≤ t / 2 := by positivity
  simp only [conePath, wedgePath, if_pos ht2, two_mul_toNNReal_half]
  have : Real.sqrt 2 * (√2)⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
  rw [← mul_assoc, this, one_mul]; ring

/-- DMS's form inside the unit disc: the circle average `Q t + A_t` at radius `e^{-t}` is `b_t + α t`
(DMS Def 4.10 with Def 4.5: `B_s + αs`) -/
theorem circleValue_of_nonneg (α Q : ℝ) (b b' : ℝ≥0 → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    Q * t + conePath α Q b b' t = b t.toNNReal + α * t := by
  rw [conePath_of_nonneg α Q b b' ht]; ring

/-- the rescaled tail used by `wedgePath` is `coneTail` at twice the time -/
lemma wedgeTail_eq (α Q : ℝ) (b' : ℝ≥0 → ℝ) :
    (fun s : ℝ => Real.sqrt 2 * ((√2)⁻¹ * b' (2 * s.toNNReal)) - (Q + 2 * (α - Q) - Q) * s) =
      fun s => coneTail α Q b' (2 * s) := by
  funext s
  have : Real.sqrt 2 * (√2)⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
  rw [← mul_assoc, this, one_mul, two_mul_toNNReal, coneTail]; ring

lemma lastZero_comp_two_mul (C : ℝ → ℝ) :
    lastZero (fun s => C (2 * s)) = lastZero C / 2 := by
  unfold lastZero
  have e : {s : ℝ | 0 ≤ s ∧ C (2 * s) = 0} = (2⁻¹ : ℝ) • {u : ℝ | 0 ≤ u ∧ C u = 0} := by
    ext s
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ (by norm_num)]
    simp only [Set.mem_setOf_eq, inv_inv, smul_eq_mul]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨by positivity, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨by linarith, h2⟩
  rw [e, Real.sSup_smul_of_nonneg (by norm_num), smul_eq_mul]; ring

/-- for `t < 0` (outside the unit disc): `A_t = C(−t + s₀)` with `C_s = b'_s + (Q − α)s` and `s₀`
the last zero of `C` (DMS Def 4.10 with Def 4.5: the conditioned side, realized after the last
zero as in QZ `wedgePath`) -/
theorem conePath_of_neg (α Q : ℝ) (b b' : ℝ≥0 → ℝ) {t : ℝ} (ht : t < 0) :
    conePath α Q b b' t =
      coneTail α Q b' (-t + lastZero (coneTail α Q b')) := by
  have ht2 : ¬ 0 ≤ t / 2 := by intro h; linarith
  simp only [conePath, wedgePath, if_neg ht2]
  rw [wedgeTail_eq, lastZero_comp_two_mul]
  have key := congrFun (wedgeTail_eq α Q b') (-(t / 2) + lastZero (coneTail α Q b') / 2)
  rw [key]
  congr 1; ring

/-! ## Cone processes are wedge processes at twice the speed (Brownian scaling) -/

lemma measurable_scaleTwo :
    Measurable fun (p : ℝ≥0 → ℝ) (s : ℝ≥0) => (√2)⁻¹ * p (2 * s) :=
  measurable_pi_iff.mpr fun s => (measurable_pi_apply (2 * s)).const_mul _

lemma isBrownianReal_scaleTwo {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    IsBrownianReal (fun s ω => (√2)⁻¹ * B (2 * s) ω) P := by
  have := hB.smul (c := 2) two_ne_zero
  simpa using this

/-- **Brownian scaling**: `t ↦ A_{2t}` of a cone process is QZ's wedge process with
`α' = Q + 2(α − Q)` (so all a.s. path facts of `QZ.IsWedgeProcess` transfer to cones) -/
theorem isWedgeProcess_of_isConeProcess {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {α Q : ℝ} {A : ℝ → Ω → ℝ} (hA : IsConeProcess α Q A P) :
    IsWedgeProcess (Q + 2 * (α - Q)) Q (fun t ω => A (2 * t) ω) P := by
  obtain ⟨B, B', hB, hB', hI, hA⟩ := hA
  refine ⟨fun s ω => (√2)⁻¹ * B (2 * s) ω, fun s ω => (√2)⁻¹ * B' (2 * s) ω,
    isBrownianReal_scaleTwo hB, isBrownianReal_scaleTwo hB', ?_, fun ω t => ?_⟩
  · exact hI.comp measurable_scaleTwo measurable_scaleTwo
  · show A (2 * t) ω = _
    rw [hA, conePath, mul_div_cancel_left₀ t two_ne_zero]

/-! ## Existence -/

/-- independence of two random variables survives passing to a product space through the first
coordinate (two-variable form of `Wedge.iIndepFun_comp_fst`) -/
theorem indepFun_comp_fst {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSpace δ] {f : α → γ} {g : α → δ} {μ : Measure α}
    {ν : Measure β} [SFinite μ] [IsProbabilityMeasure ν] (h : IndepFun f g μ) :
    IndepFun (fun p : α × β => f p.1) (fun p => g p.1) (μ.prod ν) := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul] at h ⊢
  intro s t hs ht
  have e1 : (fun p : α × β => f p.1) ⁻¹' s = (f ⁻¹' s) ×ˢ (univ : Set β) := by ext; simp
  have e2 : (fun p : α × β => g p.1) ⁻¹' t = (g ⁻¹' t) ×ˢ (univ : Set β) := by ext; simp
  rw [e1, e2, Set.prod_inter_prod, Set.inter_self, Measure.prod_prod, Measure.prod_prod,
    Measure.prod_prod, h s t hs ht, measure_univ]
  simp

/-- the reference space: two independent Brownian motions and an independent whole-plane GFF -/
theorem exists_twoBM_wpGFF :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (B B' : ℝ≥0 → Ω → ℝ) (X : Ω → Field),
      IsProbabilityMeasure P ∧ IsBrownianReal B P ∧ IsBrownianReal B' P ∧
      IndepFun (pathOf B) (pathOf B') P ∧ IsWholePlaneGFF X P ∧
      ∀ (E : Type) [MeasurableSpace E] (F : (ℝ≥0 → ℝ) → (ℝ≥0 → ℝ) → E),
        IndepFun X (fun ω => F (pathOf B ω) (pathOf B' ω)) P := by
  obtain ⟨Ω₁, _, P₁, Bm, hP₁, hB⟩ := brownianMotionExists
  obtain ⟨Ω₂, _, P₂, g, hP₂, hg⟩ := GFFExist.exists_wholePlaneGFF
  have hfst : MeasurePreserving (fun p : (Ω₁ × Ω₁) × Ω₂ => p.1.1) ((P₁.prod P₁).prod P₂) P₁ :=
    measurePreserving_fst.comp measurePreserving_fst
  have hsnd : MeasurePreserving (fun p : (Ω₁ × Ω₁) × Ω₂ => p.1.2) ((P₁.prod P₁).prod P₂) P₁ :=
    measurePreserving_snd.comp measurePreserving_fst
  have hlaw : ((P₁.prod P₁).prod P₂).map (fun p : (Ω₁ × Ω₁) × Ω₂ => g p.2) = P₂.map g := by
    rw [show (fun p : (Ω₁ × Ω₁) × Ω₂ => g p.2) = g ∘ Prod.snd from rfl,
      ← Measure.map_map hg.measurable measurable_snd, Measure.map_snd_prod, measure_univ, one_smul]
  refine ⟨(Ω₁ × Ω₁) × Ω₂, inferInstance, (P₁.prod P₁).prod P₂, fun t ω => Bm t ω.1.1,
    fun t ω => Bm t ω.1.2, fun ω => g ω.2, inferInstance, NonVacuity.nv_isBrownianReal hfst hB,
    NonVacuity.nv_isBrownianReal hsnd hB, ?_,
    DFGPS.L217.isWholePlaneGFF_of_map_eq (hg.measurable.comp measurable_snd) hg hlaw, ?_⟩
  · exact indepFun_comp_fst (f := fun ω : Ω₁ × Ω₁ => pathOf Bm ω.1)
      (g := fun ω : Ω₁ × Ω₁ => pathOf Bm ω.2) (NonVacuity.nv_indepFun_prod _ _)
  · intro E _ F
    exact (NonVacuity.nv_indepFun_prod (μ := P₁.prod P₁) (ν := P₂)
      (fun ω : Ω₁ × Ω₁ => F (pathOf Bm ω.1) (pathOf Bm ω.2)) g).symm

/-- **existence of quantum cones of every weight `W > 0`** (DMS Def 4.10 is non-vacuous), given
the open measurability node C.meas (`ConeRefMeas`) -/
theorem exists_isQuantumCone (γ : ℝ) {W : ℝ} (hW : 0 < W) (hmeas : ConeRefMeas γ W) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (Y : Ω → Field),
      IsProbabilityMeasure P ∧ IsQuantumCone γ W Y P := by
  obtain ⟨Ω, _, P, B, B', X, hP, hB, hB', hI, hX, hXI⟩ := exists_twoBM_wpGFF
  let A : ℝ → Ω → ℝ := fun t ω =>
    conePath (coneAlpha γ W) (Qc γ) (fun s => B s ω) (fun s => B' s ω) t
  have hA : IsConeProcess (coneAlpha γ W) (Qc γ) A P := ⟨B, B', hB, hB', hI, fun ω t => rfl⟩
  have hXA : IndepFun X (fun ω t => A t ω) P :=
    hXI (ℝ → ℝ) fun p p' t => conePath (coneAlpha γ W) (Qc γ) p p' t
  have hm := hmeas Ω inferInstance P X A hP hX hA hXA
  exact ⟨Ω, inferInstance, P, fun ω => coneField (lateralPartC (X ω)) (fun t => A t ω) (Qc γ),
    hP, hW, Ω, inferInstance, P, X, A, hP, hX, hA, hXA, hm, hm, rfl⟩

/-- `coneAlpha γ W < Q` exactly when `W > 0` (DMS L2209: "the constraint `α < Q` corresponds to
`W > 0`") -/
theorem coneAlpha_lt_Qc_iff {γ W : ℝ} (hγ : 0 < γ) : coneAlpha γ W < Qc γ ↔ 0 < W := by
  unfold coneAlpha
  constructor
  · intro h
    have : 0 < W / (2 * γ) := by linarith
    exact (div_pos_iff_of_pos_right (by positivity)).mp this
  · intro h
    have : 0 < W / (2 * γ) := by positivity
    linarith

end Cone

end MatedCRTHarmonic.MoTPort
