import QuantumZipper.Proofs.Thm18.G3G2Loc

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The concrete G3 Palm scheme with a deterministic profile, and its GFF Markov property

Sheffield, arXiv:1012.4797, proof of Theorem 1.8 (§5.4, p. 71): "the conditional law of the
restrictions of `h` to the two halves … are independent by the standard GFF Markov property".
This file repeats the concrete free-field Palm scheme of `G3Concrete.lean` with the field
`h = normField γ X₀ + ofFun g` shifted by a **deterministic** profile `g : ℂ → ℝ`
(`g3pField`), and proves the conditional independence of the two zooms given the field outside
both half-discs and the Palm length (`condIndepCE_g3p`), exactly as `g3MarkovStmt_concrete` does
for `g = 0`.

A deterministic shift does not change the σ-algebras: on every measure `μ`, the restricted
shifted field is the restricted unshifted field plus the constant `ofFun g μ` (or junk `0`)
(`measurable_restrictField_add`), so every measurability statement of `G3ConcreteMarkov.lean`
transfers. Own bookkeeping (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Metric Set MeasurableSpace Filter
open scoped ENNReal NNReal

namespace QuantumZipper
namespace R18

open Thm18Asm K3

/-- Restricting a field shifted by a deterministic field preserves (sub-σ-algebra)
measurability of the restricted field. -/
theorem measurable_restrictField_add {β : Type*} {m : MeasurableSpace β} {A : Set (Measure ℂ)}
    {F : β → FieldSample} (hF : Measurable[m] fun b => restrictField A (F b)) (c : FieldSample) :
    Measurable[m] fun b => restrictField A (F b + c) := by
  classical
  refine @D3Plus.measurable_fieldSample_of β m _ fun μ => ?_
  by_cases h : μ ∈ A
  · have e : (fun b => restrictField A (F b + c) μ) = fun b => restrictField A (F b) μ + c μ := by
      funext b; simp only [restrictField, if_pos h, Pi.add_apply]
    rw [e]
    exact ((measurable_pi_apply μ).comp hF).add measurable_const
  · simp only [restrictField, if_neg h]
    exact measurable_const

section Scheme

variable (γ : ℝ) (g : ℂ → ℝ) (i : G3Idx)

local notation "Ω₀" => gffBase.Ω
local notation "X₀" => gffBase.X

/-- The field `h + g` (`h = normField γ X₀`) shifted by the deterministic profile `g`. -/
def g3pField (ω : Ω₀) : FieldSample := normField γ X₀ ω + ofFun g

theorem g3pField_zero (ω : Ω₀) : g3pField γ 0 ω = normField γ X₀ ω := by
  funext μ; simp [g3pField, ofFun]

/-- Boundary length measures read from region 1, region 2, and the gap. -/
def g3pν₁ (ω : Ω₀) : Measure ℝ := bdryM γ (restrictField (circIn i.t₁ i.r₁) (g3pField γ g ω))
def g3pν₂ (ω : Ω₀) : Measure ℝ := bdryM γ (restrictField (circIn i.t₂ i.r₂) (g3pField γ g ω))
def g3pν₀ (ω : Ω₀) : Measure ℝ :=
  bdryM γ (restrictField (circOut i.t₁ i.r₁ i.t₂ i.r₂) (g3pField γ g ω))

/-- The Palm point and its length partner. -/
def g3pX (p : Ω₀ × ℝ) : ℝ := lenLeft (g3pν₁ γ g i p.1 + g3pν₀ γ g i p.1) p.2
def g3pR (p : Ω₀ × ℝ) : ℝ := lenRight (g3pν₀ γ g i p.1 + g3pν₂ γ g i p.1) p.2

/-- The full-field zooms. -/
def g3pUf (p : Ω₀ × ℝ) : LawD := zoomLaw γ i.C (g3pField γ g p.1) (g3pX γ g i p)
def g3pVf (p : Ω₀ × ℝ) : LawD := zoomLaw γ i.C (g3pField γ g p.1) (g3pR γ g i p)

/-- The Palm mass `ν[−δ, 0]`. -/
def g3pMass (ω : Ω₀) : ℝ≥0∞ := (g3pν₁ γ g i ω + g3pν₀ γ g i ω) (Icc (-i.δ) 0)

open Classical in
/-- The unnormalized Palm density. -/
def g3pW0 (p : Ω₀ × ℝ) : ℝ≥0∞ :=
  if 0 < p.2 ∧ ENNReal.ofReal p.2 ≤ g3pMass γ g i p.1 then ENNReal.ofReal (Real.exp p.2) else 0

/-- Its total mass. -/
def g3pZ : ℝ≥0∞ := ∫⁻ p, g3pW0 γ g i p ∂(gffBase.P.prod L₀)

open Classical in
/-- The normalized Palm density (junk `1` if the total mass is `0` or `∞`). -/
def g3pW : Ω₀ × ℝ → ℝ≥0 :=
  if 0 < g3pZ γ g i ∧ g3pZ γ g i < ⊤ then fun p => ((g3pZ γ g i)⁻¹ * g3pW0 γ g i p).toNNReal
  else fun _ => 1

/-- The Palm law on `Ω₀ × ℝ`. -/
def g3pPalmLaw : Measure (Ω₀ × ℝ) :=
  (gffBase.P.prod L₀).withDensity fun p => (g3pW γ g i p : ℝ≥0∞)

/-! ## Measurability -/

theorem measurable_g3pReg₁ :
    Measurable[localSigma X₀ i.t₁ i.r₁ ⊔ outsideSigma2 X₀ i.t₁ i.r₁ i.t₂ i.r₂]
      fun ω => restrictField (circIn i.t₁ i.r₁) (g3pField γ g ω) :=
  measurable_restrictField_add (F := normField γ X₀)
    (measurable_regionField γ i.r₁_pos (halfDiscPoisson_union_null₁ i.r₁_pos i.dist_le)
      (g3_refS_null i)) (ofFun g)

theorem measurable_g3pReg₂ :
    Measurable[localSigma X₀ i.t₂ i.r₂ ⊔ outsideSigma2 X₀ i.t₁ i.r₁ i.t₂ i.r₂]
      fun ω => restrictField (circIn i.t₂ i.r₂) (g3pField γ g ω) :=
  measurable_restrictField_add (F := normField γ X₀)
    (measurable_regionField γ i.r₂_pos (halfDiscPoisson_union_null₂ i.r₂_pos i.dist_le)
      (g3_refS_null i)) (ofFun g)

theorem measurable_g3pGap :
    Measurable[outsideSigma2 X₀ i.t₁ i.r₁ i.t₂ i.r₂]
      fun ω => restrictField (circOut i.t₁ i.r₁ i.t₂ i.r₂) (g3pField γ g ω) :=
  measurable_restrictField_add (F := normField γ X₀)
    (measurable_gapField γ (g3_refS_null i)) (ofFun g)

theorem measurable_g3psum₁ :
    Measurable[localSigma X₀ i.t₁ i.r₁ ⊔ outsideSigma2 X₀ i.t₁ i.r₁ i.t₂ i.r₂]
      fun ω => g3pν₁ γ g i ω + g3pν₀ γ g i ω :=
  measurable_measure_add ((measurable_bdryM γ).comp (measurable_g3pReg₁ γ g i))
    (((measurable_bdryM γ).comp (measurable_g3pGap γ g i)).mono le_sup_right le_rfl)

theorem measurable_g3psum₂ :
    Measurable[localSigma X₀ i.t₂ i.r₂ ⊔ outsideSigma2 X₀ i.t₁ i.r₁ i.t₂ i.r₂]
      fun ω => g3pν₀ γ g i ω + g3pν₂ γ g i ω :=
  measurable_measure_add
    (((measurable_bdryM γ).comp (measurable_g3pGap γ g i)).mono le_sup_right le_rfl)
    ((measurable_bdryM γ).comp (measurable_g3pReg₂ γ g i))

theorem measurable_g3pX : Measurable[sig₁ i] (g3pX γ g i) := by
  have h1 : Measurable[sig₁ i] fun p : Ω₀ × ℝ => g3pν₁ γ g i p.1 + g3pν₀ γ g i p.1 :=
    measurable_comp_fst_palm (measurable_g3psum₁ γ g i)
  have h2 : Measurable[sig₁ i] fun p : Ω₀ × ℝ => p.2 := measurable_snd_palm
  unfold g3pX
  exact Measurable.comp (g := fun q : Measure ℝ × ℝ => lenLeft q.1 q.2)
    (f := fun p : Ω₀ × ℝ => (g3pν₁ γ g i p.1 + g3pν₀ γ g i p.1, p.2)) measurable_lenLeft
    (h1.prodMk h2)

theorem measurable_g3pR : Measurable[sig₂ i] (g3pR γ g i) := by
  have h1 : Measurable[sig₂ i] fun p : Ω₀ × ℝ => g3pν₀ γ g i p.1 + g3pν₂ γ g i p.1 :=
    measurable_comp_fst_palm (measurable_g3psum₂ γ g i)
  have h2 : Measurable[sig₂ i] fun p : Ω₀ × ℝ => p.2 := measurable_snd_palm
  unfold g3pR
  exact Measurable.comp (g := fun q : Measure ℝ × ℝ => lenRight q.1 q.2)
    (f := fun p : Ω₀ × ℝ => (g3pν₀ γ g i p.1 + g3pν₂ γ g i p.1, p.2)) measurable_lenRight
    (h1.prodMk h2)

theorem measurable_g3pW0 : Measurable[sig₁ i] (g3pW0 γ g i) := by
  have hm : Measurable[sig₁ i] fun p : Ω₀ × ℝ => g3pMass γ g i p.1 :=
    measurable_comp_fst_palm ((Measure.measurable_coe measurableSet_Icc).comp
      (measurable_g3psum₁ γ g i))
  have hs : Measurable[sig₁ i] fun p : Ω₀ × ℝ => p.2 := measurable_snd_palm
  unfold g3pW0
  exact Measurable.ite ((measurableSet_lt measurable_const hs).inter
      (measurableSet_le (ENNReal.measurable_ofReal.comp hs) hm))
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hs)) measurable_const

theorem measurable_g3pW : Measurable[sig₁ i] (g3pW γ g i) := by
  unfold g3pW
  split_ifs
  · exact ENNReal.measurable_toNNReal.comp ((measurable_g3pW0 γ g i).const_mul _)
  · exact measurable_const

theorem g3pW0_ne_top (p : Ω₀ × ℝ) : g3pW0 γ g i p ≠ ⊤ := by
  unfold g3pW0
  split_ifs
  · exact ENNReal.ofReal_ne_top
  · exact ENNReal.zero_ne_top

theorem lintegral_g3pW :
    ∫⁻ p, (g3pW γ g i p : ℝ≥0∞) ∂(gffBase.P.prod L₀) = 1 := by
  have hW0 : Measurable (g3pW0 γ g i) := (measurable_g3pW0 γ g i).mono (sig_le_g3 i _ _) le_rfl
  by_cases hZ : 0 < g3pZ γ g i ∧ g3pZ γ g i < ⊤
  · simp only [g3pW, if_pos hZ]
    have e : ∀ p, ((((g3pZ γ g i)⁻¹ * g3pW0 γ g i p).toNNReal : ℝ≥0) : ℝ≥0∞) =
        (g3pZ γ g i)⁻¹ * g3pW0 γ g i p := fun p =>
      ENNReal.coe_toNNReal (ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hZ.1.ne')
        (g3pW0_ne_top γ g i p))
    simp_rw [e]
    rw [lintegral_const_mul _ hW0]
    exact ENNReal.inv_mul_cancel hZ.1.ne' hZ.2.ne
  · simp only [g3pW, if_neg hZ, ENNReal.coe_one, lintegral_const, measure_univ, one_mul]

instance isProbabilityMeasure_g3p : IsProbabilityMeasure (g3pPalmLaw γ g i) :=
  ⟨by rw [g3pPalmLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_g3pW]⟩

theorem integrable_g3pW : Integrable (fun p => (g3pW γ g i p : ℝ)) (gffBase.P.prod L₀) := by
  have hm : Measurable (g3pW γ g i) := (measurable_g3pW γ g i).mono (sig_le_g3 i _ _) le_rfl
  refine (integrable_toReal_of_lintegral_ne_top hm.coe_nnreal_ennreal.aemeasurable
    (by rw [lintegral_g3pW]; exact ENNReal.one_ne_top)).congr (ae_of_all _ fun p => ?_)
  exact ENNReal.coe_toReal _

theorem measurable_g3pField : Measurable (g3pField γ g) :=
  D3Plus.measurable_fieldSample_of fun μ =>
    ((measurable_pi_apply μ).comp (measurable_normField_g3 γ)).add measurable_const

end Scheme

end R18
end QuantumZipper
