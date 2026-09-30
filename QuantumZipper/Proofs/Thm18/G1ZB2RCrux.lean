import QuantumZipper.Proofs.Thm18.G1ZB2RShift
import QuantumZipper.Proofs.Thm18.G1ZB2RMeas
import QuantumZipper.Proofs.Zipper.F1PStarShiftReg
import QuantumZipper.Proofs.Zipper.WedgeAddConstReDet

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1Z-B2R (4): `canonical (y + C) = canonical (canonical y + C)` at the data level

Theorem 1.8, G1 zoom, node B2-R. Sheffield, arXiv:1012.4797, definition (1.8) of the canonical
description and the proof of Proposition 1.7, pp. 25–26 (add a constant, re-embed by the
unit-area radius).

* `g1zB2r_crux_abs`: for a regular `t'` with an area limit, positive scale parameter and
  scale-consistent pairings, and `W` regular with `avgReg W = avgReg (rescale t b₀)` and the
  compatibility `avgReg (addConst (rescale t s) C) = avgReg (rescale t' s)`: the data of
  `canonical (W + C)` are `g1zB2rPhi γ C` of the circle coordinates of `canonical W`. Both sides
  are the data of `canonical t'` (area-only choice independence, `g1za1b_dataFull_canonical_rescale`,
  and `coordsFull_rescale_rescale`).
* `g1zB2r_const_data`: the instance for a field `Z` that is `RegEq` to a dilation of a packaged
  field `x`, for `Z` itself and all its real translates (`t = translate x p`,
  `t' = translate (x + C) p`).

Own bookkeeping on top of the cited lemmas.
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm

open D3Plus Factorization CoordsFull

/-- `rescale` reads its argument only through `avgReg`. -/
theorem g1zB2r_rescale_congr {y y' : FieldSample} (h : avgReg y = avgReg y') (Q s : ℝ) :
    rescale y Q s = rescale y' Q s := by
  funext μ
  unfold rescale coordChange
  rw [evalReg_congr h]

/-- Constants commute with real translations, on regularized averages. -/
theorem g1zB2r_avgReg_translate_addConst {x : FieldSample} {F : ℂ × ℝ → ℝ}
    (hF : IsRegularWith x F) (p C : ℝ) :
    avgReg (addConst (translate x (p : ℂ)) C) = avgReg (translate (addConst x C) (p : ℂ)) := by
  funext k z
  rw [F1.avgReg_addConst_eq_witness (hF.translate' p) C k z,
    F1.avgReg_eq_witness_foldH ((hF.addConst' C).translate' p) k z]

/-- Translation by `0` does not change regularized averages. -/
theorem g1zB2r_avgReg_translate_zero {x : FieldSample} {F : ℂ × ℝ → ℝ}
    (hF : IsRegularWith x F) : avgReg (translate x ((0 : ℝ) : ℂ)) = avgReg x := by
  funext k z
  rw [F1.avgReg_eq_witness_foldH (hF.translate' 0) k z, F1.avgReg_eq_witness_foldH hF k z]
  simp

/-- The compatibility of rescaling, translating and adding a constant. -/
theorem g1zB2r_hcomm {x : FieldSample} {F : ℂ × ℝ → ℝ} (hF : IsRegularWith x F) (p C Q : ℝ)
    {s : ℝ} (hs : 0 < s) :
    avgReg (addConst (rescale (translate x (p : ℂ)) Q s) C) =
      avgReg (rescale (translate (addConst x C) (p : ℂ)) Q s) := by
  rw [F1.avgReg_addConst_rescale (hF.translate' p) Q C hs,
    g1zB2r_rescale_congr (g1zB2r_avgReg_translate_addConst hF p C) Q s]

/-- **The crux, abstract form.** -/
theorem g1zB2r_crux_abs {γ : ℝ} (hγ : 0 < γ) (C : ℝ) {t t' W : FieldSample} {b0 : ℝ}
    (hb0 : 0 < b0) (ht : IsRegularSample t) (htμ : ∃ μ, HasAreaLimit γ t μ)
    (hts : 0 < scaleParam γ t) (ht'r : IsRegularSample t')
    (ht'μ : ∃ μ, HasAreaLimit γ t' μ) (ht's : 0 < scaleParam γ t')
    (ht'sc : ∀ b : ℝ, 0 < b → ∀ c : ℝ, 0 < c → ∀ ρ : TestFun H, ∀ σ : ℂ → ℝ,
      (σ = ρ.1 ∨ σ = fun z => -ρ.1 z) →
      G1.ScaleConsistentAt t' (Qc γ) b ((G1.tmeas σ).map fun z => (c : ℂ) * z))
    (hW : IsRegularSample W) (hWt : avgReg W = avgReg (rescale t (Qc γ) b0))
    (hcomm : ∀ s : ℝ, 0 < s →
      avgReg (addConst (rescale t (Qc γ) s) C) = avgReg (rescale t' (Qc γ) s)) :
    WedgeMeas.dataFull H (canonical γ (addConst W C)) =
      g1zB2rPhi γ C (coordsFull (canonical γ W)) := by
  obtain ⟨F, hF⟩ := ht
  obtain ⟨F', hF'⟩ := ht'r
  obtain ⟨μ', hμ'⟩ := ht'μ
  obtain ⟨μ, hμ⟩ := htμ
  -- choice independence for `t'`
  have CI : ∀ b : ℝ, 0 < b → WedgeMeas.dataFull H (canonical γ (rescale t' (Qc γ) b)) =
      WedgeMeas.dataFull H (canonical γ t') := fun b hb =>
    G1ZA1b.g1za1b_dataFull_canonical_rescale hγ ⟨F', hF'⟩ hμ' hb ht's
      (fun ρ σ hσ => ht'sc b hb _ (div_pos ht's hb) ρ σ hσ)
  -- left-hand side
  have h1 : avgReg (addConst W C) = avgReg (rescale t' (Qc γ) b0) :=
    (F1.avgReg_addConst_congr_of_isRegularSample hW ⟨_, hF.rescale' (Qc γ) hb0⟩ hWt C).trans
      (hcomm b0 hb0)
  rw [canonical_congr h1 γ, CI b0 hb0]
  -- right-hand side
  have hcoords : coordsFull (canonical γ (rescale t (Qc γ) b0)) = coordsFull (canonical γ t) := by
    unfold canonical
    rw [g1z2_scaleParam_rescale ⟨F, hF⟩ hγ hμ hb0]
    have := S5.FieldShift.coordsFull_rescale_rescale ⟨F, hF⟩ (Qc γ) hb0 (div_pos hts hb0)
    rwa [mul_div_cancel₀ _ hb0.ne'] at this
  rw [canonical_congr hWt γ, hcoords, g1zB2rPhi_coordsFull]
  have hav : avgReg (addConst (canonical γ t) C) = avgReg (rescale t' (Qc γ) (scaleParam γ t)) :=
    hcomm _ hts
  have harea : ∃ μ, IsVagueLimitOn H (areaApprox γ (addConst (canonical γ t) C)) μ := by
    have har : areaApprox γ (addConst (canonical γ t) C) =
        areaApprox γ (rescale t' (Qc γ) (scaleParam γ t)) := by
      funext k; unfold areaApprox; rw [hav]
    rw [har]
    exact ⟨_, g1z2_isVagueLimitOn_of_hasAreaLimit (hF'.rescale' (Qc γ) hts)
      (GoodTransforms.hasAreaLimit_rescale ⟨F', hF'⟩ hγ hμ' hts)⟩
  rw [canonProxy_eq_canonical harea, canonical_congr hav γ]
  exact (CI _ hts).symm

/-- **The crux for a field `RegEq` to a dilation of a packaged field**, for the field itself and
all its real translates. -/
theorem g1zB2r_const_data {γ : ℝ} (hγ : 0 < γ) (C : ℝ) {x Z : FieldSample}
    (hx : IsRegularSample x) (hp : G1ZB2RPair x) (ha : G1ZB2RArea γ x)
    (hZ : IsRegularSample Z) {b0 : ℝ} (hb0 : 0 < b0) (hZx : RegEq Z (rescale x (Qc γ) b0)) :
    WedgeMeas.dataFull H (canonical γ (addConst Z C)) =
        g1zB2rPhi γ C (coordsFull (canonical γ Z)) ∧
      ∀ b : ℝ, WedgeMeas.dataFull H (canonical γ (addConst (translate Z (b : ℂ)) C)) =
        g1zB2rPhi γ C (coordsFull (canonical γ (translate Z (b : ℂ)))) := by
  obtain ⟨hx', hp', ha'⟩ := g1zB2r_shift_pack C hx hp ha
  obtain ⟨F, hF⟩ := hx
  have havg : avgReg Z = avgReg (rescale x (Qc γ) b0) := funext fun k => funext fun z => hZx k z
  have pack : ∀ p : ℝ,
      (IsRegularSample (translate x (p : ℂ)) ∧ (∃ μ, HasAreaLimit γ (translate x (p : ℂ)) μ) ∧
        0 < scaleParam γ (translate x (p : ℂ)) ∧ _) ∧
      (IsRegularSample (translate (addConst x C) (p : ℂ)) ∧
        (∃ μ, HasAreaLimit γ (translate (addConst x C) (p : ℂ)) μ) ∧
        0 < scaleParam γ (translate (addConst x C) (p : ℂ)) ∧ _) :=
    fun p => ⟨g1zB2r_tpack ⟨F, hF⟩ hp ha p, g1zB2r_tpack hx' hp' ha' p⟩
  refine ⟨?_, fun b => ?_⟩
  · obtain ⟨⟨h1, h2, h3, -⟩, ⟨h4, h5, h6, h7⟩⟩ := pack 0
    refine g1zB2r_crux_abs hγ C hb0 h1 h2 h3 h4 h5 h6 h7 hZ ?_
      (fun s hs => g1zB2r_hcomm hF 0 C (Qc γ) hs)
    rw [havg, g1zB2r_rescale_congr (g1zB2r_avgReg_translate_zero hF) (Qc γ) b0]
  · obtain ⟨⟨h1, h2, h3, -⟩, ⟨h4, h5, h6, h7⟩⟩ := pack (b0 * b)
    refine g1zB2r_crux_abs hγ C hb0 h1 h2 h3 h4 h5 h6 h7 (hZ.translate' b) ?_
      (fun s hs => g1zB2r_hcomm hF (b0 * b) C (Qc γ) hs)
    have e : translate Z (b : ℂ) = translate (rescale x (Qc γ) b0) (b : ℂ) := by
      funext μ; unfold translate; rw [evalReg_congr havg]
    have hb : ((b0 * b / b0 : ℝ)) = b := mul_div_cancel_left₀ b hb0.ne'
    have := g1z2_regEq_translate_rescale hF (Qc γ) hb0 (b0 * b)
    rw [hb] at this
    rw [e]
    exact funext fun k => funext fun z => this k z

end Thm18Asm
end QuantumZipper
