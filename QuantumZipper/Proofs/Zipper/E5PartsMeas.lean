import QuantumZipper.Proofs.Zipper.E5Main3
import QuantumZipper.Proofs.Zipper.D3PlusN1Scale
import QuantumZipper.Proofs.Zipper.D3PlusN1Core
import QuantumZipper.Proofs.Section5.Prop16MeasCoords

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# E5-PARTS, part 1: Borel measurability of the local scale and the local data of a zoom field

Task E5-PARTS (Theorem 1.3, node E5; Sheffield, arXiv:1012.4797, §5.4, pp. 66–72). The zoom
model of E5 needs, *everywhere* (not only a.e.), measurability of
`ω ↦ zScale … C (X ω) (g ω)` (the local scale `scaleParamOn γ · (halfDisc r)` of the model field)
and of `ω ↦ zLoc locFieldFull … C (X ω) (g ω)` (its rich local canonical data).

Proved here (own elementary bookkeeping, no new mathematics):
* `measurable_zScale_of_goodAll_e5p`: under a D3⁺ `Setup`, if the local area measure of the model
  field on `halfDisc r` exists at *every* sample, the local scale is the measurable surrogate
  `D3Plus.scaleSur` of `(localZ, macroF)` at every sample (the a.e. argument of
  `Prop16Asm.aemeasurable_scaleParamOn_zoomModel_mm`, run pointwise), hence measurable;
* `zLoc_eq_locRescale_e5p`, `measurable_zLoc_of_scale_e5p`, `aemeasurable_zLoc_of_scale_e5p`: the
  rich local data are a jointly measurable function (`measurable_locRescale_e5p`, via
  `Prop16Area.measurable_rescale_apply_joint`) of the dyadic coordinates of the model field and
  of its local scale, so they are (a.e.-)measurable whenever the scale is;
* `measurable_coords_zoomModel_e5p`: the coordinates of the D3⁺ model field are measurable for a
  jointly measurable correction `g`.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E5

open Factorization LQGMeas

/-! ## Factorization through the dyadic coordinates -/

/-- The rich local data of a rescaled reconstructed field are jointly measurable in the
coordinates and the scale. -/
theorem measurable_locRescale_e5p (Q : ℝ) (R : ℕ) :
    Measurable fun p : (ℕ → ℝ) × ℝ => D3Plus.locFieldFull R (rescale (reconstruct p.1) Q p.2) := by
  classical
  have hr : ∀ (ν : Measure ℂ) [SFinite ν],
      Measurable fun p : (ℕ → ℝ) × ℝ => rescale (reconstruct p.1) Q p.2 ν := fun ν _ =>
    (Prop16Area.measurable_rescale_apply_joint Q ν).comp
      (f := fun p : (ℕ → ℝ) × ℝ => (reconstruct p.1, p.2))
      ((measurable_reconstruct.comp measurable_fst).prodMk measurable_snd)
  unfold D3Plus.locFieldFull
  refine Measurable.prodMk (measurable_pi_iff.2 fun i => ?_) (measurable_pi_iff.2 fun ρ => ?_)
  · split_ifs
    · simp only [CoordsFull.coordsFull]
      exact hr _
    · exact measurable_const
  · split_ifs
    · simp only [pairRaw]
      exact (hr _).sub (hr _)
    · exact measurable_const

/-! ## The zoom field -/

section Zoom

variable {Ω : Type*} [MeasurableSpace Ω] {γ α r : ℝ} {ρ₀ : Measure ℂ} {C : ℝ}
  {X : Ω → FieldSample} {g : Ω → ℂ → ℝ}

/-- `zLoc` is the rich local data of the reconstructed zoom field rescaled by `zScale`. -/
theorem zLoc_eq_locRescale_e5p (R : ℕ) (x : FieldSample) (g' : ℂ → ℝ) :
    zLoc D3Plus.locFieldFull γ α r ρ₀ R C x g' =
      D3Plus.locFieldFull R (rescale (reconstruct (coords (D3Plus.zoomModel γ α C ρ₀ x g')))
        (Qc γ) (zScale γ α r ρ₀ C x g')) := by
  unfold zLoc canonicalOn zScale
  rw [Prop16Area.rescale_reconstruct_coords]

/-- **The rich local data of the zoom field are measurable** once its coordinates and its local
scale are. -/
theorem measurable_zLoc_of_scale_e5p (R : ℕ)
    (hZ : Measurable fun ω => coords (D3Plus.zoomModel γ α C ρ₀ (X ω) (g ω)))
    (hs : Measurable fun ω => zScale γ α r ρ₀ C (X ω) (g ω)) :
    Measurable fun ω => zLoc D3Plus.locFieldFull γ α r ρ₀ R C (X ω) (g ω) := by
  have e : (fun ω => zLoc D3Plus.locFieldFull γ α r ρ₀ R C (X ω) (g ω)) =
      (fun p : (ℕ → ℝ) × ℝ => D3Plus.locFieldFull R (rescale (reconstruct p.1) (Qc γ) p.2)) ∘
        (fun ω => (coords (D3Plus.zoomModel γ α C ρ₀ (X ω) (g ω)),
          zScale γ α r ρ₀ C (X ω) (g ω))) :=
    funext fun ω => zLoc_eq_locRescale_e5p R (X ω) (g ω)
  rw [e]
  exact (measurable_locRescale_e5p (Qc γ) R).comp (hZ.prodMk hs)

/-- A.e. version of `measurable_zLoc_of_scale_e5p`. -/
theorem aemeasurable_zLoc_of_scale_e5p {μ : Measure Ω} (R : ℕ)
    (hZ : Measurable fun ω => coords (D3Plus.zoomModel γ α C ρ₀ (X ω) (g ω)))
    (hs : AEMeasurable (fun ω => zScale γ α r ρ₀ C (X ω) (g ω)) μ) :
    AEMeasurable (fun ω => zLoc D3Plus.locFieldFull γ α r ρ₀ R C (X ω) (g ω)) μ := by
  have e : (fun ω => zLoc D3Plus.locFieldFull γ α r ρ₀ R C (X ω) (g ω)) =
      (fun p : (ℕ → ℝ) × ℝ => D3Plus.locFieldFull R (rescale (reconstruct p.1) (Qc γ) p.2)) ∘
        (fun ω => (coords (D3Plus.zoomModel γ α C ρ₀ (X ω) (g ω)),
          zScale γ α r ρ₀ C (X ω) (g ω))) :=
    funext fun ω => zLoc_eq_locRescale_e5p R (X ω) (g ω)
  rw [e]
  exact (measurable_locRescale_e5p (Qc γ) R).comp_aemeasurable (hZ.aemeasurable.prodMk hs)

/-- **The local scale of a D3⁺ model field is measurable everywhere** as soon as the local area
measure on `halfDisc r` exists at every sample (then it is the measurable surrogate `scaleSur`
of `(localZ, macroF)`, as in `Prop16Asm.aemeasurable_scaleParamOn_zoomModel_mm`). -/
theorem measurable_zScale_of_goodAll_e5p {E' : Type*} [MeasurableSpace E'] {Q : Measure Ω}
    {Ξ : Ω → E'} (hS : D3Plus.Setup γ α r ρ₀ Q X Ξ g)
    (hgood : ∀ ω, ∃ m, IsVagueLimitOn (D3Plus.halfDisc r)
      (areaApprox γ (D3Plus.zoomModel γ α C ρ₀ (X ω) (g ω))) m) :
    Measurable fun ω => zScale γ α r ρ₀ C (X ω) (g ω) := by
  have e : (fun ω => zScale γ α r ρ₀ C (X ω) (g ω)) = fun ω =>
      D3Plus.scaleSur γ C r (D3Plus.localZ X r ω, D3Plus.macroF α r ρ₀ X g ω) := by
    funext ω
    have hag := D3Plus.agreeNear_zoomModel_locModel hS C ω
    have hg := (D3Plus.exists_isVagueLimitOn_halfDisc_iff hag).1 (hgood ω)
    exact ((D3Plus.scaleSur_eq hg).trans (D3Plus.scaleParamOn_halfDisc_congr hag).symm).symm
  rw [e]
  exact (D3Plus.measurable_scaleSur γ C r).comp (D3Plus.measurable_localZ_macroF hS)

/-- **The coordinates of the D3⁺ model field are measurable** for a field with measurable
coordinates and a jointly measurable correction. -/
theorem measurable_coords_zoomModel_e5p (γ α C : ℝ) (ρ₀ : Measure ℂ)
    (hX : ∀ μ : Measure ℂ, Measurable fun ω => X ω μ)
    (hg : Measurable fun q : Ω × ℂ => g q.1 q.2) :
    Measurable fun ω => coords (D3Plus.zoomModel γ α C ρ₀ (X ω) (g ω)) := by
  refine measurable_pi_iff.2 fun i => ?_
  simp only [coords, D3Plus.zoomModel, Pi.add_apply, ofFun]
  refine (hX _).add ?_
  have hf : Measurable fun q : Ω × ℂ =>
      α * -Real.log ‖q.2‖ + g q.1 q.2 + (C / γ - X q.1 ρ₀) :=
    ((measurable_const.mul (Real.measurable_log.comp measurable_snd.norm).neg).add hg).add
      (measurable_const.sub ((hX ρ₀).comp measurable_fst))
  exact (hf.stronglyMeasurable.integral_prod_right'
    (ν := foldedCircle (dyadicIndex i).1 (radius (dyadicIndex i).2))).measurable

end Zoom

end E5
end QuantumZipper
