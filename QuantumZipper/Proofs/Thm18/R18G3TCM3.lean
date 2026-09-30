import QuantumZipper.Proofs.Thm18.R18G3TCM2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18-G3 (R-a), part 3: Palm integrals of scheme `B` as tilted integrals of scheme `A`

Berestycki–Powell, arXiv:2004.04720, Lemma 3.12 (Cameron–Martin for the GFF); Sheffield,
arXiv:1012.4797, p. 72, Remark 5.7. The Palm objects of both schemes are the same functionals
(`sW0`, `sX`, `sR`, `zoomLaw`) of the field, read only on folded circles (`FcEq`). An event
`G` measurable for the field outside both half-discs and the Palm length is a function of the
outside increments of `X₀` (`outside_repr`); under `X₀ ↦ X₀ + φ` these move by constants, so
`G` becomes another outside event `G'`. Hence (`lintegral_B_eq_tilt`)
`∫⁻_{S_B ∩ G} W0_B = ∫⁻_{S_A ∩ G'} W0_A · cmTilt`. Own bookkeeping on top of the cited
Cameron–Martin formula.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal NNReal ComplexConjugate

namespace QuantumZipper
namespace R18

open Thm18Asm

local notation "Ω₀" => gffBase.Ω
local notation "X₀" => gffBase.X

/-! ## The Palm functionals of a field -/

section Fun

variable (γ : ℝ) (i : G3Idx)

def sν₁ (y : FieldSample) : Measure ℝ := bdryM γ (restrictField (circIn i.t₁ i.r₁) y)
def sν₂ (y : FieldSample) : Measure ℝ := bdryM γ (restrictField (circIn i.t₂ i.r₂) y)
def sν₀ (y : FieldSample) : Measure ℝ :=
  bdryM γ (restrictField (circOut i.t₁ i.r₁ i.t₂ i.r₂) y)
def sMass (y : FieldSample) : ℝ≥0∞ := (sν₁ γ i y + sν₀ γ i y) (Icc (-i.δ) 0)

open Classical in
def sW0 (q : FieldSample × ℝ) : ℝ≥0∞ :=
  if 0 < q.2 ∧ ENNReal.ofReal q.2 ≤ sMass γ i q.1 then ENNReal.ofReal (Real.exp q.2) else 0

def sX (q : FieldSample × ℝ) : ℝ := lenLeft (sν₁ γ i q.1 + sν₀ γ i q.1) q.2
def sR (q : FieldSample × ℝ) : ℝ := lenRight (sν₀ γ i q.1 + sν₂ γ i q.1) q.2

def sMX (m : ℝ) : Set (FieldSample × ℝ) := {q | |sX γ i q - i.t₁| + m < i.r₁}
def sMR (m : ℝ) : Set (FieldSample × ℝ) := {q | |sR γ i q - i.t₂| + m < i.r₂}

theorem g3pW0_eq (g : ℂ → ℝ) (p : Ω₀ × ℝ) : g3pW0 γ g i p = sW0 γ i (g3pField γ g p.1, p.2) := rfl
theorem g3W0_eq (p : Ω₀ × ℝ) : g3W0 γ i p = sW0 γ i (normField γ X₀ p.1, p.2) := rfl

theorem measurable_restrictField_y (A : Set (Measure ℂ)) :
    Measurable (restrictField A) := by
  refine measurable_pi_iff.2 fun μ => ?_
  by_cases h : μ ∈ A
  · simp only [restrictField, if_pos h]; exact measurable_pi_apply μ
  · simp only [restrictField, if_neg h]; exact measurable_const

theorem measurable_sν₁ : Measurable (sν₁ γ i) :=
  (measurable_bdryM γ).comp (measurable_restrictField_y _)
theorem measurable_sν₂ : Measurable (sν₂ γ i) :=
  (measurable_bdryM γ).comp (measurable_restrictField_y _)
theorem measurable_sν₀ : Measurable (sν₀ γ i) :=
  (measurable_bdryM γ).comp (measurable_restrictField_y _)

theorem measurable_sW0 : Measurable (sW0 γ i) := by
  have hM : Measurable (sMass γ i) :=
    (Measure.measurable_coe measurableSet_Icc).comp
      (measurable_measure_add (measurable_sν₁ γ i) (measurable_sν₀ γ i))
  have hset : MeasurableSet {q : FieldSample × ℝ | 0 < q.2 ∧ ENNReal.ofReal q.2 ≤ sMass γ i q.1} :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le (ENNReal.measurable_ofReal.comp measurable_snd) (hM.comp measurable_fst))
  exact Measurable.ite hset (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    measurable_snd)) measurable_const

theorem measurable_sX : Measurable (sX γ i) := by
  have h : Measurable fun q : FieldSample × ℝ => (sν₁ γ i q.1 + sν₀ γ i q.1, q.2) :=
    ((measurable_measure_add (measurable_sν₁ γ i) (measurable_sν₀ γ i)).comp
      measurable_fst).prodMk measurable_snd
  unfold sX
  exact Measurable.comp (g := fun p : Measure ℝ × ℝ => lenLeft p.1 p.2)
    (f := fun q : FieldSample × ℝ => (sν₁ γ i q.1 + sν₀ γ i q.1, q.2)) measurable_lenLeft h
theorem measurable_sR : Measurable (sR γ i) := by
  have h : Measurable fun q : FieldSample × ℝ => (sν₀ γ i q.1 + sν₂ γ i q.1, q.2) :=
    ((measurable_measure_add (measurable_sν₀ γ i) (measurable_sν₂ γ i)).comp
      measurable_fst).prodMk measurable_snd
  unfold sR
  exact Measurable.comp (g := fun p : Measure ℝ × ℝ => lenRight p.1 p.2)
    (f := fun q : FieldSample × ℝ => (sν₀ γ i q.1 + sν₂ γ i q.1, q.2)) measurable_lenRight h

theorem measurableSet_sMX (m : ℝ) : MeasurableSet (sMX γ i m) :=
  measurableSet_lt ((continuous_abs.measurable.comp ((measurable_sX γ i).sub_const _)).add_const _)
    measurable_const
theorem measurableSet_sMR (m : ℝ) : MeasurableSet (sMR γ i m) :=
  measurableSet_lt ((continuous_abs.measurable.comp ((measurable_sR γ i).sub_const _)).add_const _)
    measurable_const

end Fun

/-! ## Locality: the functionals read the field only on folded circles -/

/-- Agreement on all folded circles of positive radius. -/
def FcEq (x x' : FieldSample) : Prop :=
  ∀ (c : ℂ) (ρ : ℝ), 0 < ρ → x (foldedCircle c ρ) = x' (foldedCircle c ρ)

section Loc

variable {x x' : FieldSample} (h : FcEq x x')
include h

theorem restrictField_circIn_fc (t r : ℝ) :
    restrictField (circIn t r) x = restrictField (circIn t r) x' := by
  funext μ
  unfold restrictField
  split_ifs with hμ
  · obtain ⟨d, ρ, hρ, rfl, -⟩ := hμ
    exact h d ρ hρ
  · rfl

theorem restrictField_circOut_fc (t₁ r₁ t₂ r₂ : ℝ) :
    restrictField (circOut t₁ r₁ t₂ r₂) x = restrictField (circOut t₁ r₁ t₂ r₂) x' := by
  funext μ
  unfold restrictField
  split_ifs with hμ
  · obtain ⟨d, ρ, hρ, rfl, -⟩ := hμ
    exact h d ρ hρ
  · rfl

theorem avgReg_fc : avgReg x = avgReg x' := by
  funext k z
  unfold avgReg
  congr 1
  funext n
  exact h _ _ (radius_pos k)

theorem sν_fc (γ : ℝ) (i : G3Idx) :
    sν₁ γ i x = sν₁ γ i x' ∧ sν₂ γ i x = sν₂ γ i x' ∧ sν₀ γ i x = sν₀ γ i x' := by
  simp only [sν₁, sν₂, sν₀, restrictField_circIn_fc h, restrictField_circOut_fc h, and_self]

theorem sW0_fc (γ : ℝ) (i : G3Idx) (ℓ : ℝ) : sW0 γ i (x, ℓ) = sW0 γ i (x', ℓ) := by
  obtain ⟨h1, -, h0⟩ := sν_fc h γ i
  unfold sW0 sMass
  rw [h1, h0]

theorem sX_fc (γ : ℝ) (i : G3Idx) (ℓ : ℝ) : sX γ i (x, ℓ) = sX γ i (x', ℓ) := by
  obtain ⟨h1, -, h0⟩ := sν_fc h γ i
  simp only [sX, h1, h0]

theorem sR_fc (γ : ℝ) (i : G3Idx) (ℓ : ℝ) : sR γ i (x, ℓ) = sR γ i (x', ℓ) := by
  obtain ⟨-, h2, h0⟩ := sν_fc h γ i
  simp only [sR, h2, h0]

end Loc

/-- A set of `(field, length)` pairs that only sees the field on folded circles. -/
def IsLocS (S : Set (FieldSample × ℝ)) : Prop :=
  ∀ x x' : FieldSample, FcEq x x' → ∀ ℓ : ℝ, ((x, ℓ) ∈ S ↔ (x', ℓ) ∈ S)

theorem isLocS_sMX (γ : ℝ) (i : G3Idx) (m : ℝ) : IsLocS (sMX γ i m) :=
  fun x x' h ℓ => by simp only [sMX, mem_setOf_eq, sX_fc h γ i ℓ]
theorem isLocS_sMR (γ : ℝ) (i : G3Idx) (m : ℝ) : IsLocS (sMR γ i m) :=
  fun x x' h ℓ => by simp only [sMR, mem_setOf_eq, sR_fc h γ i ℓ]

theorem fcEq_normField_recon (γ : ℝ) {Ω : Type*} (Y : Ω → FieldSample) (ω : Ω) :
    FcEq (normField γ Y ω) (g3recon γ (CMTV.incr (Y ω))) := fun c ρ hρ =>
  normField_eq_g3recon γ Y ω (D3Plus.isAdmissibleH_foldedCircle' c hρ) measure_univ

/-! ## The cut-off profile vanishes on the unit circle -/

theorem g3wCut_unit (γ η : ℝ) (z : ℂ) (hz : ‖z‖ = 1) : g3wCut γ η z = 0 := by
  simp only [g3wCut, hz, sub_self, zero_mul, Real.smoothTransition.zero, mul_zero]

/-! ## Outside events are functions of the outside increments -/

/-- The outside increments. -/
def oInc (i : G3Idx) (y : K3.BalIdx → ℝ) : OutIdx2 i.t₁ i.r₁ i.t₂ i.r₂ → ℝ :=
  fun q => y ⟨q.1, q.2.1, q.2.2.1, q.2.2.2.1⟩

theorem outside_repr (i : G3Idx) {G : Set (Ω₀ × ℝ)}
    (hG : MeasurableSet[outsideSigmaPalm ℝ X₀ i.t₁ i.r₁ i.t₂ i.r₂] G) :
    ∃ G₀ : Set ((OutIdx2 i.t₁ i.r₁ i.t₂ i.r₂ → ℝ) × ℝ), MeasurableSet G₀ ∧
      G = (fun p : Ω₀ × ℝ => (oInc i (CMTV.incr (X₀ p.1)), p.2)) ⁻¹' G₀ := by
  set F : Ω₀ × ℝ → (OutIdx2 i.t₁ i.r₁ i.t₂ i.r₂ → ℝ) × ℝ :=
    fun p => (oInc i (CMTV.incr (X₀ p.1)), p.2) with hF
  have hle : outsideSigmaPalm ℝ X₀ i.t₁ i.r₁ i.t₂ i.r₂ ≤ MeasurableSpace.comap F inferInstance := by
    refine sup_le ?_ ?_
    · have hfst : Measurable[MeasurableSpace.comap F inferInstance,
          outsideSigma2 X₀ i.t₁ i.r₁ i.t₂ i.r₂] Prod.fst := by
        rw [measurable_iff_comap_le]
        unfold outsideSigma2
        rw [MeasurableSpace.comap_iSup]
        refine iSup_le fun q => ?_
        rw [MeasurableSpace.comap_comp]
        exact measurable_iff_comap_le.1
          ((measurable_pi_apply q).comp (measurable_fst.comp (comap_measurable F)))
      exact measurable_iff_comap_le.1 hfst
    · have hs : Measurable[MeasurableSpace.comap F inferInstance] (fun p : Ω₀ × ℝ => (F p).2) :=
        measurable_snd.comp (comap_measurable F)
      exact measurable_iff_comap_le.1 hs
  obtain ⟨s', hs', he⟩ := MeasurableSpace.measurableSet_comap.1 (hle _ hG)
  exact ⟨s', hs', he.symm⟩

theorem measurable_oInc_shift (i : G3Idx) (c : OutIdx2 i.t₁ i.r₁ i.t₂ i.r₂ → ℝ) :
    Measurable[outsideSigmaPalm ℝ X₀ i.t₁ i.r₁ i.t₂ i.r₂]
      (fun p : Ω₀ × ℝ => (oInc i (CMTV.incr (X₀ p.1)) - c, p.2)) := by
  have hfst : Measurable[outsideSigmaPalm ℝ X₀ i.t₁ i.r₁ i.t₂ i.r₂,
      outsideSigma2 X₀ i.t₁ i.r₁ i.t₂ i.r₂] Prod.fst := by
    unfold outsideSigmaPalm; exact Measurable.of_comap_le le_sup_left
  have hsnd : Measurable[outsideSigmaPalm ℝ X₀ i.t₁ i.r₁ i.t₂ i.r₂] (Prod.snd : Ω₀ × ℝ → ℝ) := by
    unfold outsideSigmaPalm; exact Measurable.of_comap_le le_sup_right
  have h1 : Measurable[outsideSigmaPalm ℝ X₀ i.t₁ i.r₁ i.t₂ i.r₂]
      (fun p : Ω₀ × ℝ => oInc i (CMTV.incr (X₀ p.1)) - c) := by
    letI : MeasurableSpace (Ω₀ × ℝ) := outsideSigmaPalm ℝ X₀ i.t₁ i.r₁ i.t₂ i.r₂
    refine measurable_pi_iff.2 fun q => ?_
    exact ((measurable_outsideSigma2 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2).comp
        hfst).sub_const _
  exact h1.prodMk hsnd

end R18
end QuantumZipper
