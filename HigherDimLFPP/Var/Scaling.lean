import HigherDimLFPP.Var.Ag
import LQGDimension.Section2.Bounds

/-!
# The scaling identity (2.5)

For `a, b > 0` and every `n` (paper Lemma 2.1, (2.5); HA1 D4):

`E sup_{f ∈ V_n(E)} {a G(f) - b E(f)} = a^{4/3} b^{-1/3} A_n(E)`,

in finite-subfamily form, in `[0, ∞]` (`scaling25`).  The finite-family identity behind it
(`gEM_scaling`): with `λ = (a/b)^{2/3}` and `s = a^{4/3} b^{-1/3}`, the dilation `f ↦ λ f` maps a
finite family `F` to `λF` with `a² gCov(λf, λg) = s² gCov(f, g)` and `b E(λf) = s E(f)`, so
`𝕄_{λF}(a² gCov, -b E) = s 𝕄_F(gCov, -E)` (HA1 (T5), (T7)).

Ported from `LQGDimension/Section2/Bounds.lean` (`dilate`, `dilation_pointwise`, `aDilation`),
generalized from the drift multiplier `b` alone to the pair `(a, b)` and to `E`-valued profiles.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped RealInnerProductSpace

namespace HigherDimLFPP.Var

open LQGDimension (gaussianExpectedMax vecExpectedMax PSDOn)

/-! ## Scaling a finite Gaussian family (HA1 (T7)) -/

lemma psdOn_const_mul {ι : Type*} {F : Finset ι} {C : ι → ι → ℝ} (hC : PSDOn F C) {c : ℝ}
    (hc : 0 ≤ c) : PSDOn F (fun i j => c * C i j) := by
  unfold PSDOn at *
  have e : (Matrix.of fun i j : F => c * C i j) = c • Matrix.of fun i j : F => C i j := by
    ext i j
    simp
  rw [e]
  exact hC.smul hc

/-- `𝕄_F(s² C, s b) = s 𝕄_F(C, b)` for `s ≥ 0` and `C` PSD on `F` (HA1 (T7)). -/
theorem gEM_smul {ι : Type*} (F : Finset ι) (C : ι → ι → ℝ) (hC : PSDOn F C) (b : ι → ℝ)
    {s : ℝ} (hs : 0 ≤ s) :
    gaussianExpectedMax F (fun i j => s ^ 2 * C i j) (fun i => s * b i) =
      s * gaussianExpectedMax F C b := by
  obtain ⟨T, hT⟩ := LQGDimension.exists_gram_of_psdOn F C hC
  have h1 : gaussianExpectedMax F (fun i j => s ^ 2 * C i j) (fun i => s * b i) =
      vecExpectedMax F (fun i => s • T i) (fun i => s * b i) := by
    rw [← LQGDimension.gaussianExpectedMax_gram_eq_vecExpectedMax]
    refine LQGDimension.gaussianExpectedMax_congr F _ fun i hi j hj => ?_
    rw [real_inner_smul_left, real_inner_smul_right, hT i hi j hj]
    ring
  have h2 : gaussianExpectedMax F C b = vecExpectedMax F T b := by
    rw [← LQGDimension.gaussianExpectedMax_gram_eq_vecExpectedMax]
    exact LQGDimension.gaussianExpectedMax_congr F b fun i hi j hj => (hT i hi j hj).symm
  rw [h1, h2, LQGDimension.Subadd.vecEM_smul F T b hs]

/-! ## Dilations of `Vg E n` -/

section Dilate

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `f ↦ c f` on `Vg E n`. -/
def dilate (n : ℕ) (c : ℝ) (f : Vg E n) : Vg E n := ⟨c • (f : ℝ → E), smul_mem_Vg f.2 c⟩

@[simp] lemma dilate_coe (n : ℕ) (c : ℝ) (f : Vg E n) :
    (dilate n c f : ℝ → E) = c • (f : ℝ → E) := rfl

lemma dilate_dilate_inv (n : ℕ) {c : ℝ} (hc : c ≠ 0) (f : Vg E n) :
    dilate n c (dilate n c⁻¹ f) = f := by
  apply Subtype.ext
  show c • (c⁻¹ • (f : ℝ → E)) = (f : ℝ → E)
  rw [smul_smul, mul_inv_cancel₀ hc, one_smul]

lemma image_dilate_dilate (n : ℕ) [DecidableEq (Vg E n)] {c : ℝ} (hc : c ≠ 0)
    (F : Finset (Vg E n)) : (F.image (dilate n c⁻¹)).image (dilate n c) = F := by
  rw [Finset.image_image,
    show (dilate n c) ∘ (dilate n c⁻¹) = id from funext (dilate_dilate_inv n hc)]
  exact Finset.image_id

end Dilate

/-! ## (2.5) -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The constants of (2.5): with `λ = (a/b)^{2/3}` and `s = a^{4/3} b^{-1/3}`,
`a² λ = s²` and `b λ² = s`. -/
lemma scaling_consts {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    a ^ 2 * (a / b) ^ (2 / 3 : ℝ) = (a ^ (4 / 3 : ℝ) * b ^ (-1 / 3 : ℝ)) ^ 2 ∧
      b * ((a / b) ^ (2 / 3 : ℝ)) ^ 2 = a ^ (4 / 3 : ℝ) * b ^ (-1 / 3 : ℝ) := by
  have hab : (a / b) ^ (2 / 3 : ℝ) = a ^ (2 / 3 : ℝ) * b ^ (-2 / 3 : ℝ) := by
    rw [Real.div_rpow ha.le hb.le, div_eq_mul_inv, ← Real.rpow_neg hb.le]
    norm_num
  have ha2 : a ^ 2 = a ^ (2 : ℝ) := (Real.rpow_natCast a 2).symm
  constructor
  · rw [hab, mul_pow, ← Real.rpow_natCast (a ^ (4 / 3 : ℝ)), ← Real.rpow_natCast (b ^ _),
      ← Real.rpow_mul ha.le, ← Real.rpow_mul hb.le, ha2, ← mul_assoc,
      ← Real.rpow_add ha]
    norm_num
  · rw [hab, mul_pow, ← Real.rpow_natCast (a ^ (2 / 3 : ℝ)), ← Real.rpow_natCast (b ^ _),
      ← Real.rpow_mul ha.le, ← Real.rpow_mul hb.le]
    rw [show b * (a ^ ((2 / 3 : ℝ) * ((2 : ℕ) : ℝ)) * b ^ ((-2 / 3 : ℝ) * ((2 : ℕ) : ℝ))) =
        a ^ ((2 / 3 : ℝ) * ((2 : ℕ) : ℝ)) * (b ^ (1 : ℝ) * b ^ ((-2 / 3 : ℝ) * ((2 : ℕ) : ℝ)))
        by rw [Real.rpow_one]; ring, ← Real.rpow_add hb]
    norm_num

/-- **(2.5) on finite subfamilies**: for `a, b > 0`, `λ = (a/b)^{2/3}` and any finite `F ⊆ V_n(E)`,
`𝕄_{λF}(a² gCov, -b E) = a^{4/3} b^{-1/3} 𝕄_F(gCov, -E)`. -/
theorem gEM_scaling (n : ℕ) [DecidableEq (Vg E n)] (F : Finset (Vg E n)) {a b : ℝ} (ha : 0 < a)
    (hb : 0 < b) :
    gaussianExpectedMax (F.image (dilate n ((a / b) ^ (2 / 3 : ℝ))))
        (fun f g => a ^ 2 * gCov (f : ℝ → E) g) (fun f => -(b * energy (f : ℝ → E))) =
      a ^ (4 / 3 : ℝ) * b ^ (-1 / 3 : ℝ) *
        gaussianExpectedMax F (fun f g => gCov (f : ℝ → E) g) (fun f => -energy (f : ℝ → E)) := by
  set lam := (a / b) ^ (2 / 3 : ℝ) with hlam
  set s := a ^ (4 / 3 : ℝ) * b ^ (-1 / 3 : ℝ) with hs
  have hlam0 : 0 ≤ lam := Real.rpow_nonneg (div_nonneg ha.le hb.le) _
  have hs0 : 0 ≤ s := mul_nonneg (Real.rpow_nonneg ha.le _) (Real.rpow_nonneg hb.le _)
  obtain ⟨h1, h2⟩ := scaling_consts ha hb
  rw [gEM_image F (dilate n lam) _ _
    (psdOn_const_mul (gCov_psdOn_Vg n _) (sq_nonneg a))]
  rw [← gEM_smul F (fun f g => gCov (f : ℝ → E) g) (gCov_psdOn_Vg n F)
    (fun f => -energy (f : ℝ → E)) hs0]
  refine LQGDimension.Subadd.gEM_congr F (fun f _ g _ => ?_) (fun f _ => ?_)
  · simp only [dilate_coe]
    rw [gCov_smul hlam0, ← mul_assoc, h1]
  · simp only [dilate_coe]
    rw [energy_smul f.2, ← mul_assoc, h2]
    ring

/-- **(2.5)**: `E sup_{f ∈ V_n(E)} {a G(f) - b E(f)} = a^{4/3} b^{-1/3} A_n(E)` for `a, b > 0`, in
`[0, ∞]` (finite-subfamily form; HA1 D4, template `Scaling25` of HA1 Details (c)). -/
theorem scaling25 (n : ℕ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (⨆ F : Finset (Vg E n), ((gaussianExpectedMax F (fun f g => a ^ 2 * gCov (f : ℝ → E) g)
      (fun f => -(b * energy (f : ℝ → E))) : ℝ) : EReal)) =
      ((a ^ (4 / 3 : ℝ) * b ^ (-1 / 3 : ℝ) : ℝ) : EReal) * Ag E n := by
  classical
  set lam := (a / b) ^ (2 / 3 : ℝ) with hlam
  set s := a ^ (4 / 3 : ℝ) * b ^ (-1 / 3 : ℝ) with hs
  have hlampos : 0 < lam := Real.rpow_pos_of_pos (div_pos ha hb) _
  have hspos : 0 < s := mul_pos (Real.rpow_pos_of_pos ha _) (Real.rpow_pos_of_pos hb _)
  apply le_antisymm
  · refine iSup_le fun G => ?_
    have hG : G = (G.image (dilate n lam⁻¹)).image (dilate n lam) :=
      (image_dilate_dilate n hlampos.ne' G).symm
    rw [hG, gEM_scaling n _ ha hb, EReal.coe_mul]
    exact mul_le_mul_of_nonneg_left (le_Ag _) (EReal.coe_nonneg.2 hspos.le)
  · have h : Ag E n = ⨆ F : Finset (Vg E n),
        ((gaussianExpectedMax F (fun f g => gCov (f : ℝ → E) g)
          (fun f => -energy (f : ℝ → E)) : ℝ) : EReal) := rfl
    rw [h, LQGDimension.Bounds.EReal_coe_mul_iSup hspos]
    refine iSup_le fun F => ?_
    rw [← EReal.coe_mul, ← gEM_scaling n F ha hb]
    exact le_iSup (fun F : Finset (Vg E n) => ((gaussianExpectedMax F
      (fun f g => a ^ 2 * gCov (f : ℝ → E) g) (fun f => -(b * energy (f : ℝ → E))) : ℝ) :
        EReal)) (F.image (dilate n lam))

end HigherDimLFPP.Var
