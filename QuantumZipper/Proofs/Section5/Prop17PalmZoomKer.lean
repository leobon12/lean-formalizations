import QuantumZipper.Proofs.Section5.Prop17PalmZoomReg
import QuantumZipper.Proofs.LQG.FirstMoment
import QuantumZipper.Proofs.Zipper.E6Concrete

/-!
# Proposition 1.7, node D4⁺ (Palm zoom): the boundary-measure kernel of the free field (PALMZOOM)

Part of node 1 (`Prop17FreeRegStmt`) for the normalizer `ϖ = foldedCircle 0 R` (so that
`N_ϖ X = zField X R`, the normalization of `BdryExist`/`FirstMoment`): an s-finite kernel `ν`
with `ν ω = qBoundaryMeasure γ (N_ϖ X ω)` a.s. and `0 < E ν[a,b] < ∞` for `a < b`,
`[a,b] ⊆ [−N,N]`, `N + 2 ≤ R`. Inputs: `PalmFree.aemeasurable_qBoundaryMeasure_free`,
`E6.exists_sfinite_version`, first moment `FirstMoment.lintegral_qBoundaryMeasure_Icc_lt_top`
/ `_Icc_pos` (Kahane first-moment formula, S5-B3(f)). Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace S5
namespace FieldLaw
namespace Raw

open PalmNorm PalmShift

theorem freeFieldN_foldedCircle_eq_zField {Ω : Type*} (X : Ω → FieldSample) (R : ℝ) (ω : Ω) :
    freeFieldN (foldedCircle 0 R) X ω = BdryExist.zField X R ω := by
  rw [freeFieldN_eq_addConst]; rfl

/-- **The boundary-measure kernel of the normalized free field.** -/
theorem exists_freeKernel {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) {N : ℕ} {R : ℝ} (hR : (N : ℝ) + 2 ≤ R) {a b : ℝ} (hab : a < b)
    (habN : Icc a b ⊆ Icc (-(N : ℝ)) N) :
    ∃ ν : Kernel Ω ℝ, IsSFiniteKernel ν ∧
      (∀ᵐ ω ∂P, ν ω = qBoundaryMeasure γ (freeFieldN (foldedCircle 0 R) X ω)) ∧
      palmMass P ν a b ≠ 0 ∧ palmMass P ν a b ≠ ∞ := by
  have h0 : ∀ ω, ofFun (fun _ : ℂ => (0 : ℝ)) + BdryExist.zField X R ω = BdryExist.zField X R ω :=
    fun ω => AreaCircles.ofFun_zero_add' _
  have hm : AEMeasurable (fun ω => qBoundaryMeasure γ (BdryExist.zField X R ω)) P := by
    have := PalmFree.aemeasurable_qBoundaryMeasure_free (m := fun _ => (0 : ℝ)) hX hγ hγ2 R
      continuousOn_const
    simpa only [h0] using this
  set K : Kernel Ω ℝ := ⟨hm.mk _, hm.measurable_mk⟩ with hK
  have hKae : ∀ᵐ ω ∂P, K ω = qBoundaryMeasure γ (BdryExist.zField X R ω) :=
    hm.ae_eq_mk.mono fun ω hω => hω.symm
  obtain ⟨K', hK', hK'ae⟩ := E6.exists_sfinite_version (P := P) K (by
    filter_upwards [hKae, FirstMoment.ae_qBoundaryMeasure_Icc_lt_top_zField hX hγ hγ2 R]
      with ω h1 h2 u v
    rw [h1]; exact (h2 u v).ne)
  have hmass : palmMass P K' a b =
      ∫⁻ ω, qBoundaryMeasure γ (ofFun (fun _ : ℂ => (0 : ℝ)) + BdryExist.zField X R ω)
        (Icc a b) ∂P := by
    unfold palmMass
    refine lintegral_congr_ae ?_
    filter_upwards [hK'ae, hKae] with ω h1 h2
    rw [h1, h2, h0]
  refine ⟨K', hK', ?_, ?_, ?_⟩
  · filter_upwards [hK'ae, hKae] with ω h1 h2
    rw [h1, h2, freeFieldN_foldedCircle_eq_zField]
  · rw [hmass]
    exact (FirstMoment.lintegral_qBoundaryMeasure_Icc_pos hX hγ hγ2 hR hab habN
      continuous_const).ne'
  · rw [hmass]
    exact (FirstMoment.lintegral_qBoundaryMeasure_Icc_lt_top hX hγ hγ2 hR habN
      continuousOn_const).ne

/-- **Rest of node 1 (hypothesis).** For the free field normalized by `ϖ`: a.s. every zoom of
`N_ϖ X` has a positive scale parameter (needs a.s. infinite total quantum area of `ℍ` and local
finiteness of the area measure, as in `scaleParam_translate_pos`), and `N_ϖ X` has a modification
`h` whose zoom coordinates are measurable in `(ω, x)` for every `C`. -/
def Prop17FreeRegRestStmt (γ : ℝ) (ϖ : Measure ℂ) : Prop :=
  ∀ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (X : Ω → FieldSample),
    IsProbabilityMeasure P → IsFreeGFFModConstH X P →
    (∀ᵐ ω ∂P, ∀ C x : ℝ, 0 < scaleParam γ (zoomField γ C (freeFieldN ϖ X ω) x)) ∧
    ∃ h : Ω → FieldSample, (∀ᵐ ω ∂P, h ω = freeFieldN ϖ X ω) ∧
      ∀ C : ℝ, Measurable (zoomCoords γ C h)

/-- **Node 1 from its remaining part** (normalizer `foldedCircle 0 R`). -/
theorem prop17FreeRegStmt_of_rest {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {N : ℕ} {R : ℝ}
    (hR : (N : ℝ) + 2 ≤ R) {a b : ℝ} (hab : a < b) (habN : Icc a b ⊆ Icc (-(N : ℝ)) N)
    (hrest : Prop17FreeRegRestStmt γ (foldedCircle 0 R)) :
    Prop17FreeRegStmt γ (foldedCircle 0 R) a b := by
  intro Ω _ P X hP hX
  obtain ⟨hsc, h, hh, hmeas⟩ := hrest Ω _ P X hP hX
  obtain ⟨ν, hν, hνae, h0, htop⟩ := exists_freeKernel hX hγ hγ2 hR hab habN
  refine ⟨h, ν, hh, hν, h0, htop, ?_, hmeas⟩
  filter_upwards [hh, hνae, hsc, ae_freeFieldN_bdry hX hγ hγ2 (foldedCircle 0 R)]
    with ω h1 h2 h3 h4
  obtain ⟨hg, hat, hpos, hinf⟩ := h4
  rw [h1, h2]
  exact ⟨rfl, hg, hat, hpos, hinf, h3⟩

/-- **D4⁺ (Palm zoom) from the three remaining free-field nodes**, with the normalizer
`foldedCircle 0 3` and the Palm window `[0, 1]`. -/
theorem prop17PalmZoomStmt_of_freeNodes {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hrest : Prop17FreeRegRestStmt γ (foldedCircle 0 3))
    (hId : Prop17FreePalmIdStmt γ (foldedCircle 0 3) 0 1)
    (hFix : Prop17FreeFixedZoomStmt γ (foldedCircle 0 3) 0 1) : Prop17PalmZoomStmt γ := by
  have hR : ((1 : ℕ) : ℝ) + 2 ≤ 3 := by norm_num
  have habN : Icc (0 : ℝ) 1 ⊆ Icc (-((1 : ℕ) : ℝ)) ((1 : ℕ) : ℝ) := by
    intro t ht; simp only [Nat.cast_one, mem_Icc] at ht ⊢; constructor <;> linarith [ht.1, ht.2]
  exact prop17PalmZoomStmt_of_free hγ hγ2
    (prop17FreeRegStmt_of_rest hγ hγ2 hR one_pos habN hrest) hId hFix

end Raw
end FieldLaw
end S5
end QuantumZipper
