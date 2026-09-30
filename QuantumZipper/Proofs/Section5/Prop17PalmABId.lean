import QuantumZipper.Proofs.Section5.Prop17PalmABRep
import QuantumZipper.Proofs.Zipper.E1Window2
import QuantumZipper.Proofs.LQG.WedgeGood
import QuantumZipper.Proofs.LQG.IndepParams
import QuantumZipper.Proofs.Section5.Prop17ShiftDetWire

/-!
# Proposition 1.7, node D4⁺ (Palm zoom), node B: the Palm identity for the zoom coordinates

`Prop17FreePalmIdStmt γ ϖ a b` (node B of `handoff/PROP17-STAT.md`, PALMZOOM section) is proved
for every admissible probability normalizer `ϖ` and window `[a, b]`
(`prop17FreePalmIdStmt_of_adm`), in particular for `ϖ = foldedCircle 0 3`, `[a, b] = [0, 1]`
(`prop17FreePalmIdStmt_holds`).

Source: the rooted-measure (Palm) formula for the boundary measure, Duplantier–Sheffield,
*Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011), arXiv:0808.1560, §3.3 (p. 22), in
the normalized form `PalmNorm.palm_formula_norm`, with the indicator weight of `(a, b)`
(`E1.palm_formula_Ioo`, monotone convergence). It is applied to the test function
`φ(c, x) = 1_E(zoomRep γ C (c, x))` of the raw dyadic coordinates `c` (the folded circles
`WedgeGood.fcC j` are admissible), using the representation of node A
(`zoomCoords_eq_zoomRep`, valid on good fields).

Goodness of the Palm-shifted field (`ae_palmFreeField_good`): for Lebesgue-a.e. `x ∈ (a, b)`,
a.s. `N_ϖ(X + (γ/2)(neumannH x · − k_ϖ))` is good. Own argument: apply the same Palm formula to
`φ(c, x) = 1{reconstruct c is not good}`; the left side vanishes because the free field is a.s.
good, and `ρ_ϖ > 0`. (This is the standard remark that `P`-a.s. properties hold under the rooted
measure.) Endpoints `a, b` are null for the atomless boundary measure (`ae_freeFieldN_bdry`) and
for Lebesgue measure. The rest is own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace S5
namespace FieldLaw
namespace Raw

open WedgeMeas Factorization CoordsFull PalmNorm PalmShift

section
variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- The jointly measurable version of `palmZoomCoords` (through the raw coordinates). -/
def palmRep (γ C : ℝ) (ϖ : Measure ℂ) (X : Ω → FieldSample) (p : Ω × ℝ) : ℕ → ℝ :=
  zoomRep γ C (coords (palmFreeField γ ϖ X p.2 p.1), p.2)

theorem measurable_coords_palmFreeField (hX : IsFreeGFFModConstH X P) (γ : ℝ) (ϖ : Measure ℂ)
    [SFinite ϖ] : Measurable fun p : Ω × ℝ => coords (palmFreeField γ ϖ X p.2 p.1) := by
  refine measurable_pi_iff.2 fun i => ?_
  set μ := foldedCircle (dyadicIndex i).1 (radius (dyadicIndex i).2) with hμ
  have e : (fun p : Ω × ℝ => coords (palmFreeField γ ϖ X p.2 p.1) i) = fun p =>
      (ofFun (shiftFun γ 0 ϖ p.2) μ + X p.1 μ) +
        -(ofFun (shiftFun γ 0 ϖ p.2) ϖ + X p.1 ϖ) * (μ univ).toReal := rfl
  rw [e]
  have hs : Measurable (Prod.snd : Ω × ℝ → ℝ) := measurable_snd
  have h1 := (E1.measurable_ofFun_shiftFun (γ := γ) (h := (0 : ℂ → ℝ)) measurable_const ϖ
    μ).comp hs
  have h2 := (E1.measurable_ofFun_shiftFun (γ := γ) (h := (0 : ℂ → ℝ)) measurable_const ϖ
    ϖ).comp hs
  exact (h1.add ((hX.measurable_coord μ).comp measurable_fst)).add
    ((h2.add ((hX.measurable_coord ϖ).comp measurable_fst)).neg.mul measurable_const)

theorem measurable_palmRep (hX : IsFreeGFFModConstH X P) (γ C : ℝ) (ϖ : Measure ℂ) [SFinite ϖ] :
    Measurable (palmRep γ C ϖ X) :=
  (measurable_zoomRep γ C).comp
    ((measurable_coords_palmFreeField hX γ ϖ).prodMk measurable_snd)

theorem measurable_palmK [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) (γ : ℝ)
    (ϖ : Measure ℂ) [SFinite ϖ] {φ : (ℕ → ℝ) → ℝ → ℝ≥0∞}
    (hφ : Measurable (Function.uncurry φ)) :
    Measurable fun x => ∫⁻ ω, φ (coords (palmFreeField γ ϖ X x ω)) x ∂P :=
  Measurable.lintegral_prod_left'
    (f := fun p : Ω × ℝ => φ (coords (palmFreeField γ ϖ X p.2 p.1)) p.2)
    (hφ.comp ((measurable_coords_palmFreeField hX γ ϖ).prodMk measurable_snd))

/-- **The Palm formula on `(a, b)` for the normalized free field, in raw coordinates**
(`E1.palm_formula_Ioo` with `h = 0`, `μ = fcC`). -/
theorem palm_free_Ioo [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {ϖ : Measure ℂ} (hϖ : IsAdmissibleH ϖ) (hϖ1 : ϖ univ = 1)
    {a b : ℝ} {N : ℕ} (hab : Icc a b ⊆ Icc (-(N : ℝ)) N) {φ : (ℕ → ℝ) → ℝ → ℝ≥0∞}
    (hφ : Measurable (Function.uncurry φ)) :
    ∫⁻ ω, ∫⁻ x in Ioo a b, φ (coords (freeFieldN ϖ X ω)) x
        ∂(qBoundaryMeasure γ (freeFieldN ϖ X ω)) ∂P =
      ∫⁻ x in Ioo a b, ENNReal.ofReal (rhoNorm γ 0 ϖ x) *
        ∫⁻ ω, φ (coords (palmFreeField γ ϖ X x ω)) x ∂P := by
  haveI : IsProbabilityMeasure ϖ := ⟨hϖ1⟩
  have hex : ∀ᵐ ω ∂P, ∃ ν, IsVagueLimitR (bdryApprox γ (normAt ϖ (ofFun 0 + X ω))) ν := by
    filter_upwards [ae_freeFieldN_bdry hX hγ hγ2 ϖ] with ω hω
    exact ⟨_, hω.1.qBoundaryMeasure_spec.1,
      fun f hf hfc => LQGMeas.tendsto_bdryApprox_of_good hω.1 hf hfc⟩
  exact E1.palm_formula_Ioo (h := 0) (h' := 0) (μ := WedgeGood.fcC) hX hγ hγ2 hab
    continuous_const isOpen_univ (fun _ _ => mem_univ _) (fun _ _ => rfl) hϖ hϖ1
    WedgeGood.fcC_admissible (integrable_zero _ _ _) (fun _ => integrable_zero _ _ _) hex hφ
    (E1.measurable_rhoNorm measurable_const ϖ) (measurable_palmK hX γ ϖ hφ)

/-- Raw coordinates of bad samples. -/
def badSet (γ : ℝ) : Set (ℕ → ℝ) := {c | IsLQGGood γ (reconstruct c)}ᶜ

theorem measurableSet_badSet (γ : ℝ) : MeasurableSet (badSet γ) :=
  (IndepParams.measurableSet_good_coords γ).compl

theorem coords_mem_badSet_iff {γ : ℝ} (y : FieldSample) :
    coords y ∈ badSet γ ↔ ¬ IsLQGGood γ y := by
  rw [badSet, mem_compl_iff, mem_setOf_eq, GoodSample.isLQGGood_iff_reconstruct]

/-- The bad-event test function. -/
def badφ (γ : ℝ) (c : ℕ → ℝ) (_ : ℝ) : ℝ≥0∞ := (badSet γ).indicator 1 c

theorem measurable_badφ (γ : ℝ) : Measurable (Function.uncurry (badφ γ)) :=
  (measurable_one.indicator (measurableSet_badSet γ)).comp measurable_fst

theorem palm_bad_zero [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {ϖ : Measure ℂ} (hϖ : IsAdmissibleH ϖ) (hϖ1 : ϖ univ = 1)
    {a b : ℝ} {N : ℕ} (hab : Icc a b ⊆ Icc (-(N : ℝ)) N) :
    ∫⁻ x in Ioo a b, ENNReal.ofReal (rhoNorm γ 0 ϖ x) *
      ∫⁻ ω, badφ γ (coords (palmFreeField γ ϖ X x ω)) x ∂P = 0 := by
  rw [← palm_free_Ioo hX hγ hγ2 hϖ hϖ1 hab (measurable_badφ γ)]
  refine (lintegral_congr_ae ?_).trans lintegral_zero
  filter_upwards [ae_freeFieldN_bdry hX hγ hγ2 ϖ] with ω hω
  have hn : coords (freeFieldN ϖ X ω) ∉ badSet γ := fun h => (coords_mem_badSet_iff _).1 h hω.1
  have h0 : ∀ x, badφ γ (coords (freeFieldN ϖ X ω)) x = 0 := fun x => indicator_of_notMem hn _
  simp only [h0, lintegral_zero, Pi.zero_apply]

/-- **Goodness of the Palm-shifted field** for a.e. Palm point. -/
theorem ae_palmFreeField_good [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {ϖ : Measure ℂ} (hϖ : IsAdmissibleH ϖ) (hϖ1 : ϖ univ = 1)
    {a b : ℝ} {N : ℕ} (hab : Icc a b ⊆ Icc (-(N : ℝ)) N) :
    ∀ᵐ x ∂(volume.restrict (Icc a b)), ∀ᵐ ω ∂P, IsLQGGood γ (palmFreeField γ ϖ X x ω) := by
  haveI : IsProbabilityMeasure ϖ := ⟨hϖ1⟩
  have hKm := measurable_palmK (P := P) hX γ ϖ (measurable_badφ γ)
  have hmR : Measurable fun x => ENNReal.ofReal (rhoNorm γ 0 ϖ x) *
      ∫⁻ ω, badφ γ (coords (palmFreeField γ ϖ X x ω)) x ∂P :=
    (E1.measurable_rhoNorm measurable_const ϖ).ennreal_ofReal.mul hKm
  have H2 := (lintegral_eq_zero_iff hmR).1 (palm_bad_zero hX hγ hγ2 hϖ hϖ1 hab)
  rw [Measure.restrict_congr_set Ioo_ae_eq_Icc.symm]
  filter_upwards [H2] with x hx
  have hρ : ENNReal.ofReal (rhoNorm γ 0 ϖ x) ≠ 0 := (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  have hx' : ENNReal.ofReal (rhoNorm γ 0 ϖ x) *
      ∫⁻ ω, badφ γ (coords (palmFreeField γ ϖ X x ω)) x ∂P = 0 := hx
  have hK0 := (mul_eq_zero.1 hx').resolve_left hρ
  have hmx : Measurable fun ω => badφ γ (coords (palmFreeField γ ϖ X x ω)) x :=
    (measurable_badφ γ).comp (((measurable_coords_palmFreeField hX γ ϖ).comp
      (measurable_id.prodMk (measurable_const : Measurable fun _ : Ω => x))).prodMk
      (measurable_const : Measurable fun _ : Ω => x))
  rw [lintegral_eq_zero_iff hmx] at hK0
  filter_upwards [hK0] with ω hω
  by_contra hng
  have hm : coords (palmFreeField γ ϖ X x ω) ∈ badSet γ := (coords_mem_badSet_iff _).2 hng
  have h1 : badφ γ (coords (palmFreeField γ ϖ X x ω)) x = 1 := indicator_of_mem hm _
  have h2 : badφ γ (coords (palmFreeField γ ϖ X x ω)) x = 0 := hω
  rw [h1] at h2
  exact one_ne_zero h2

end

end Raw
end FieldLaw
end S5
end QuantumZipper
