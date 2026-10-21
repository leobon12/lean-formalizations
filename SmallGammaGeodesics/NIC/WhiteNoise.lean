import SmallGammaGeodesics.NIC.Sqrt
import LQGMetric.Field.ExistGFF

/-!
# NIC, part 2 (steps 1–3): the GFF of a white noise and the isometry `O = U_τ ⊕ 1`

Packet P-G2; design D-P2 of `planning/handoffs/P-G1.md` (steps 1–3), GA2 D5 Step 6,
blueprint `lem:nic` Step D.

* `exists_gff_of_whiteNoise`: for **any** white noise `W` on any probability space, the
  construction of `LQGMetric.GFFExist.exists_wholePlaneGFF` (a continuous version of the
  antiderivative field and `gffOf`) gives a whole-plane GFF `h` with `⟨h, φ⟩ = W(J φ)` a.s. for
  every test function `φ` (`J = testL2`).
* `isWhiteNoise_comp_linearIsometry`: `W ∘ O` is a white noise for every linear isometry `O` of
  `L²(ℝ × ℂ)`; `wn_sub_ae`: `W (f − g) = W f − W g` a.s.; `wn_integral_sq`: `E (W f)² = ‖f‖²`.
* `NearIdPair.wnIsom`: `O := U_τ ⊕ 1` on `L² = H_* ⊕ H_*^⊥`,
  `O v = U_τ (P v) + (v − P v)` with `P` the orthogonal projection onto `H_*`; it is a linear
  isometry (Pythagoras twice), and `O (J g) = U_τ (J g)` for mean-zero `g` (`wnIsom_testL2`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped RealInnerProductSpace

namespace SmallGammaGeodesics
namespace NIC

open LQGMetric LQGMetric.GFFExist LQGMetric.WhiteNoise

section Generic

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **Step 1: the GFF of a white noise.** For any white noise `W`, there is a whole-plane GFF `h`
with `⟨h, φ⟩ = W(J φ)` almost surely, for every test function `φ`. (The proof of
`GFFExist.exists_wholePlaneGFF`, generic in the white noise.) -/
theorem exists_gff_of_whiteNoise (hW : IsWhiteNoise P W) :
    ∃ h : Ω → DistC, IsWholePlaneGFF h P ∧
      ∀ φ : TestC, (fun ω => h ω φ) =ᵐ[P] W (testL2 φ) := by
  have hP := hW.isProbabilityMeasure
  obtain ⟨Y, hYc, hYm, hYW⟩ := exists_continuous_rectField hW
  have hae : ∀ φ : TestC, (fun ω => gffOf Y hYc ω φ) =ᵐ[P] W (testL2 φ) := fun φ => by
    simpa only [gffOf_apply] using ae_integral_d12_mul_eq hW hYc hYm hYW φ
  have hmean : ∀ φ : TestC, ∫ ω, gffOf Y hYc ω φ ∂P = 0 := fun φ => by
    rw [integral_congr_ae (hae φ),
      QuantumZipper.GFFExist.gs_integral_eq_zero (hW.hasLaw_single _)]
  refine ⟨gffOf Y hYc, ⟨measurable_gffOf Y hYc hYm, ?_, fun φ => hmean φ.1, ?_⟩, hae⟩
  · exact (hW.isGaussianProcess_comp (fun φ : TestC0 => testL2 φ.1)).congr
      (fun φ => (hae φ.1).symm)
  · intro φ ψ
    have hm1 := (wn_memLp hW (testL2 φ.1)).ae_eq (hae φ.1).symm
    have hm2 := (wn_memLp hW (testL2 ψ.1)).ae_eq (hae ψ.1).symm
    rw [covariance_eq_sub hm1 hm2, hmean φ.1, zero_mul, sub_zero,
      integral_congr_ae ((hae φ.1).mul (hae ψ.1))]
    have := wn_integral_mul hW (testL2 φ.1) (testL2 ψ.1)
    simp only [Pi.mul_apply]
    rw [this, inner_testL2_testL2 φ.1 ψ.1 φ.2 ψ.2]

/-- **Step 2**: a white noise composed with a linear isometry of `L²(ℝ × ℂ)` is a white noise:
`∑ cᵢ W(O fᵢ)` is centred Gaussian with variance `‖O ∑ cᵢ fᵢ‖² = ‖∑ cᵢ fᵢ‖²`. -/
theorem isWhiteNoise_comp_linearIsometry (hW : IsWhiteNoise P W)
    (O : WNSpace →ₗᵢ[ℝ] WNSpace) : IsWhiteNoise P (fun f => W (O f)) where
  measurable f := hW.measurable (O f)
  hasLaw {ι} _ f c := by
    have h := hW.hasLaw (fun i => O (f i)) c
    have e : ∑ i, c i • O (f i) = O (∑ i, c i • f i) := by
      rw [map_sum]
      simp only [map_smul]
    rw [e, O.norm_map] at h
    exact h

/-- a.s. subtraction `W (f − g) = W f − W g` -/
theorem wn_sub_ae (hW : IsWhiteNoise P W) (f g : WNSpace) :
    W (f - g) =ᵐ[P] fun ω => W f ω - W g ω := by
  have h := hW.ae_eq_zero_of_norm_eq_zero ![f - g, f, g] ![1, -1, 1] (by
    simp [Fin.sum_univ_three]; abel)
  filter_upwards [h] with ω hω
  simp only [Fin.sum_univ_three, Pi.zero_apply] at hω
  simp at hω
  linarith

/-- `E (W f)² = ‖f‖²` -/
theorem wn_integral_sq (hW : IsWhiteNoise P W) (f : WNSpace) :
    ∫ ω, W f ω ^ 2 ∂P = ‖f‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← wn_integral_mul hW]
  simp only [sq]

end Generic

/-! ## Step 3: the isometry `O = U_τ ⊕ 1` -/

/-- the orthogonal projection onto `H_*` and the complementary part are orthogonal -/
lemma inner_Hstar_sub_starProjection (u : Hstar) (v : WNSpace) :
    ⟪(u : WNSpace), v - Hstar.starProjection v⟫ = 0 :=
  Submodule.inner_right_of_mem_orthogonal u.2 (Submodule.sub_starProjection_mem_orthogonal v)

/-- Pythagoras for `u ∈ H_*` and the complement `v − P v` -/
lemma norm_sq_add_sub_starProjection (u : Hstar) (v : WNSpace) :
    ‖(u : WNSpace) + (v - Hstar.starProjection v)‖ ^ 2 =
      ‖u‖ ^ 2 + ‖v - Hstar.starProjection v‖ ^ 2 := by
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℝ) (u : WNSpace)
    (v - Hstar.starProjection v) (inner_Hstar_sub_starProjection u v)
  rw [sq, sq, sq, h, Submodule.norm_coe]

namespace NearIdPair

variable (D : NearIdPair)

/-- the underlying linear map of `O := U_τ ⊕ 1`: `O v = U_τ (P v) + (v − P v)` -/
def wnIsomₗ : WNSpace →ₗ[ℝ] WNSpace :=
  Hstar.subtype ∘ₗ (D.polar.toLinearEquiv : Hstar →ₗ[ℝ] Hstar) ∘ₗ
      (Hstar.orthogonalProjectionOnto : WNSpace →ₗ[ℝ] Hstar) +
    (LinearMap.id - (Hstar.starProjection : WNSpace →ₗ[ℝ] WNSpace))

lemma wnIsomₗ_apply (v : WNSpace) :
    D.wnIsomₗ v = ((D.polar (Hstar.orthogonalProjectionOnto v) : Hstar) : WNSpace) +
      (v - Hstar.starProjection v) := rfl

lemma norm_wnIsomₗ (v : WNSpace) : ‖D.wnIsomₗ v‖ = ‖v‖ := by
  have h1 := norm_sq_add_sub_starProjection (D.polar (Hstar.orthogonalProjectionOnto v)) v
  have h2 := norm_sq_add_sub_starProjection (Hstar.orthogonalProjectionOnto v) v
  rw [LinearIsometryEquiv.norm_map] at h1
  rw [Submodule.coe_orthogonalProjectionOnto_apply, add_sub_cancel] at h2
  have h : ‖D.wnIsomₗ v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [wnIsomₗ_apply, h1, ← h2]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

/-- **Step 3: the isometry `O := U_τ ⊕ 1`** of `L²(ℝ × ℂ) = H_* ⊕ H_*^⊥` -/
def wnIsom : WNSpace →ₗᵢ[ℝ] WNSpace where
  toLinearMap := D.wnIsomₗ
  norm_map' := D.norm_wnIsomₗ

lemma wnIsom_apply (v : WNSpace) :
    D.wnIsom v = ((D.polar (Hstar.orthogonalProjectionOnto v) : Hstar) : WNSpace) +
      (v - Hstar.starProjection v) := rfl

/-- `O = U_τ` on `H_*` -/
lemma wnIsom_coe (u : Hstar) : D.wnIsom u = (D.polar u : WNSpace) := by
  rw [wnIsom_apply, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,
    Submodule.starProjection_mem_subspace_eq_self, sub_self, add_zero]

/-- `O (J g) = U_τ (J g)` for mean-zero test functions `g` -/
lemma wnIsom_testL2 (g : testC0Sub) : D.wnIsom (testL2 g) = (D.polar (jH g) : WNSpace) := by
  rw [← coe_jH, wnIsom_coe]

end NearIdPair

end NIC
end SmallGammaGeodesics
