import QuantumZipper.Proofs.Section5.Prop16LocCoupleAnnJ

/-!
# DOM-a by annulus features (decision D34), AN5: the assembly

`domMarkovCurveAnn_holds : DomMarkovCurveAnnStmt`: the general DOM-a (`DomMarkovCurveEStmt`) from
AN2 (`FreeAnnRepStmt`), AN3 (`FreeAnnLipStmt`) and AN4 (`Prop16UnifLocalStmt`).

Construction (own, see `Prop16LocCoupleAnnNodes.lean`): `E = WithLp 2 (HkE × GradSpace D)`,
`ι = inlL2`, `e = annE J` (`Prop16LocCoupleAnnJ.lean`), `ρ₀` the unit folded circle of radius `1`
around `(|M| + 2) i` (outside `closure D ⊆ closedBall 0 M`), and
`H z = (P_M̂ᗮ (v̂_{fold_{z,s_z}} − v̂_{ρ₀}), −remVec D S (fold_{z,s_z}))`, `s_z` half of a chosen
local radius at `z` (`locRad`). On a compact `K` with uniform local radius `2R`, both components
equal their radius-`R` versions (mean-value properties), which gives the Lipschitz bound
(`K3.exists_abs_inner_remVec_sub_le`, AN3) and the weak identity
(`K3.inner_rieszVec_eq_integral_of_mem_orthogonal`, AN2, `sub_annJ_mem_orthogonal`).
-/

noncomputable section

open MeasureTheory Set Metric
open scoped RealInnerProductSpace NNReal

namespace QuantumZipper

namespace Prop16Asm

open GFFExist K3

variable {D S : Set ℂ}

theorem freeFold_eq {z : ℂ} {s : ℝ} (hz : z ∈ Hbar) (hs : 0 < s) :
    freeFold z s = freeVec ⟨foldedCircle z s, isAdmissibleH_foldedCircle hz hs⟩ := by
  simp [freeFold, hz, hs]

/-- For `g ∈ K`, `⟪g, x⟫ = ⟪g, P_K x⟫`. -/
theorem inner_eq_inner_starProjection_an {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {K : Submodule ℝ E} [K.HasOrthogonalProjection] {g : E}
    (hg : g ∈ K) (x : E) : ⟪g, x⟫ = ⟪g, K.starProjection x⟫ := by
  rw [← K.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.2 hg]

/-- `‖u‖ ≤ C` from `‖u‖² ≤ C ‖u‖`, `0 ≤ C`. -/
theorem norm_le_of_sq_le_an {a C : ℝ} (ha : 0 ≤ a) (hC : 0 ≤ C) (h : a ^ 2 ≤ C * a) : a ≤ C := by
  rcases ha.lt_or_eq with ha | ha
  · nlinarith
  · rw [← ha]; exact hC

/-- **Mean value, free side.** -/
theorem freeFold_orth_eq {z : ℂ} {s s' R0 : ℝ} (hloc : LocalBall D S z R0) (hs : 0 < s)
    (hs' : 0 < s') (hsR : s < R0) (hs'R : s' < R0) :
    (freeAnnSpan D S)ᗮ.starProjection (freeFold z s) =
      (freeAnnSpan D S)ᗮ.starProjection (freeFold z s') := by
  have key : ∀ {a b : ℝ}, 0 < a → a < b → b < R0 →
      (freeAnnSpan D S)ᗮ.starProjection (freeFold z a) =
        (freeAnnSpan D S)ᗮ.starProjection (freeFold z b) := by
    intro a b ha hab hbR
    have hz := hloc.1
    have hmem : freeFold z a - freeFold z b ∈ freeAnnSpan D S := by
      rw [freeFold_eq hz ha, freeFold_eq hz (ha.trans hab), ← freeAnnFeat_eq hz ha (ha.trans hab)]
      exact annFree_mem (D := D) (S := S) ⟨(z, a, b, R0), hloc, ha, hab, hbR⟩
    rw [← sub_eq_zero, ← map_sub, Submodule.starProjection_apply_eq_zero_iff]
    exact (freeAnnSpan D S).le_orthogonal_orthogonal hmem
  rcases lt_trichotomy s s' with h | rfl | h
  · exact key hs h hs'R
  · rfl
  · exact (key hs' h hsR).symm

/-- **Mean value, mixed side.** -/
theorem remVec_fold_eq_an (h : AnnGeom D S) {z : ℂ} {s s' R0 : ℝ} (hloc : LocalBall D S z R0)
    (hs : 0 < s) (hs' : 0 < s') (hsR : s < R0) (hs'R : s' < R0) :
    remVec D S (foldedCircle z s) = remVec D S (foldedCircle z s') := by
  rcases lt_trichotomy s s' with h' | rfl | h'
  · exact remVec_foldedCircle_eq h.isOpen h.subset_H h.bounded h.free_real hloc hs h' hs'R
  · rfl
  · exact (remVec_foldedCircle_eq h.isOpen h.subset_H h.bounded h.free_real hloc hs' h' hsR).symm

open Classical in
/-- A chosen local radius at `z` (`1` if there is none). -/
def locRad (D S : Set ℂ) (z : ℂ) : ℝ :=
  if h : ∃ R, LocalBall D S z R then Classical.choose h else 1

theorem localBall_locRad {z : ℂ} {R : ℝ} (h : LocalBall D S z R) :
    LocalBall D S z (locRad D S z) := by
  have hex : ∃ R, LocalBall D S z R := ⟨R, h⟩
  rw [locRad, dite_eq_left_of_eq_true (eq_true hex)]
  exact Classical.choose_spec hex

/-- A local ball at the larger of two local radii. -/
theorem localBall_max_an {z : ℂ} {R R' : ℝ} (h : LocalBall D S z R) (h' : LocalBall D S z R') :
    LocalBall D S z (max R R') := by
  rcases max_choice R R' with e | e <;> rw [e] <;> assumption

/-- The free component of the curve. -/
def annHf (D S : Set ℂ) (ρ₀ : AdmT) (z : ℂ) : HkE :=
  (freeAnnSpan D S)ᗮ.starProjection (freeFold z (locRad D S z / 2) - freeVec ρ₀)

/-- The mixed component of the curve. -/
def annHm (D S : Set ℂ) (z : ℂ) : GradSpace D :=
  remVec D S (foldedCircle z (locRad D S z / 2))

/-- **The curve** `H z = (annHf z, −annHm z)`. -/
def annH (D S : Set ℂ) (ρ₀ : AdmT) (z : ℂ) : WithLp 2 (HkE × GradSpace D) :=
  WithLp.toLp 2 (annHf D S ρ₀ z, -annHm D S z)

theorem annHf_eq {ρ₀ : AdmT} {z : ℂ} {R : ℝ} (hR : 0 < R) (hloc : LocalBall D S z (2 * R)) :
    annHf D S ρ₀ z = (freeAnnSpan D S)ᗮ.starProjection (freeFold z R - freeVec ρ₀) := by
  have h1 := localBall_locRad hloc
  have hpos : 0 < locRad D S z := h1.2.1
  have hm := localBall_max_an hloc h1
  rw [annHf, map_sub, map_sub, freeFold_orth_eq hm (by positivity) hR
    ((by linarith : locRad D S z / 2 < locRad D S z).trans_le (le_max_right _ _))
    ((by linarith : R < 2 * R).trans_le (le_max_left _ _))]

theorem annHm_eq (h : AnnGeom D S) {z : ℂ} {R : ℝ} (hR : 0 < R)
    (hloc : LocalBall D S z (2 * R)) : annHm D S z = remVec D S (foldedCircle z R) := by
  have h1 := localBall_locRad hloc
  have hpos : 0 < locRad D S z := h1.2.1
  have hm := localBall_max_an hloc h1
  exact remVec_fold_eq_an h hm (by positivity) hR
    ((by linarith : locRad D S z / 2 < locRad D S z).trans_le (le_max_right _ _))
    ((by linarith : R < 2 * R).trans_le (le_max_left _ _))

/-- The inclusion of the free space into the product. -/
def inlL2 (D : Set ℂ) : HkE →ₗᵢ[ℝ] WithLp 2 (HkE × GradSpace D) where
  toFun x := WithLp.toLp 2 (x, 0)
  map_add' x y := by
    rw [← WithLp.toLp_add]; simp
  map_smul' c x := by
    rw [← WithLp.toLp_smul]; simp
  norm_map' x := by
    rw [WithLp.prod_norm_eq_of_L2]
    simp

theorem norm_toLp_le_an (a : HkE) (b : GradSpace D) :
    ‖(WithLp.toLp 2 (a, b) : WithLp 2 (HkE × GradSpace D))‖ ≤ ‖a‖ + ‖b‖ := by
  rw [WithLp.prod_norm_eq_of_L2]
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  change ‖a‖ ^ 2 + ‖b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2
  nlinarith [norm_nonneg a, norm_nonneg b]

end Prop16Asm

end QuantumZipper
