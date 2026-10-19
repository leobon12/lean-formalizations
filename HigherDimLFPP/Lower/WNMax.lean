import HigherDimLFPP.Field.WhiteNoise
import GaussianLQG.Probability.Gaussian

/-!
# Expected maxima of white-noise pairings (lower comparison, source §5.1–§5.2)

Packet P-L3 (audit HA4, "Details for later use" D5 steps 1–6, D6 Step 4).  For a finite family
of vectors `x : ι → L²(ℝ × ℝ^d)` the expected maximum of the white-noise pairings `W(x_i)` is the
Gaussian expected maximum of the Gram matrix (P-F1's `integral_iSup_eq_gaussianExpectedMax`).
We fix one white noise `W₀` (P-F1's `exists_isWhiteNoise`) to compare families jointly:

* `emaxAbs x = E max_i |W₀(x_i)|`, with `emaxAbs_le` (`≤ s √(2 log 2|ι|)` when all `‖x_i‖ ≤ s`,
  no joint Gaussianity needed), `emaxAbs_add` (subadditivity), `emaxAbs_smul`;
* `gEM_gram_ge`: `𝕄(x) ≥ 𝕄(y) - E max_i |W₀(x_i - y_i)|`, the integrated form of
  `max (a + r) ≥ max a - max |r|` (HA4 D5);
* `abs_gEM_gram_sub_le`: `|𝕄(x) - 𝕄(y)| ≤ s √(2 log 2|ι|)` if `‖x_i - y_i‖ ≤ s`.

Here `𝕄(x) = gaussianExpectedMax univ (⟪x_i, x_j⟫) 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace

namespace HigherDimLFPP.Lower

open LQGDimension (gaussianExpectedMax)

variable {d : ℕ}

theorem iSup_finset_univ {ι : Type*} [Fintype ι] (g : ι → ℝ) :
    ⨆ i : (Finset.univ : Finset ι), g i = ⨆ i, g i :=
  (Equiv.subtypeUnivEquiv Finset.mem_univ).iSup_comp (g := g)

/-- A finite maximum of integrable functions is integrable. -/
theorem integrable_iSup_fintype {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ι : Type*}
    [Fintype ι] {Z : ι → Ω → ℝ} (h : ∀ i, Integrable (Z i) P) :
    Integrable (fun ω => ⨆ i, Z i ω) P := by
  refine Integrable.mono' (integrable_finsetSum Finset.univ fun i _ => (h i).abs) ?_ ?_
  · exact (AEMeasurable.iSup fun i => (h i).aemeasurable).aestronglyMeasurable
  · filter_upwards with ω
    rcases isEmpty_or_nonempty ι with hι | hι
    · simp
    · obtain ⟨j, hj⟩ := exists_eq_ciSup_of_finite (f := fun i => Z i ω)
      rw [← hj, Real.norm_eq_abs]
      exact Finset.single_le_sum (f := fun i => |Z i ω|) (fun i _ => abs_nonneg _)
        (Finset.mem_univ j)

section WN

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ}

theorem integrable_W (hW : IsWhiteNoise P W) (f : WN d) : Integrable (W f) P :=
  memLp_one_iff_integrable.1 (hW.memLp f 1 ENNReal.one_ne_top)

/-- `E max_i W(x_i) = 𝕄(x)` for a finite index type. -/
theorem integral_iSup_W_eq_gEM (hW : IsWhiteNoise P W) {ι : Type*} [Fintype ι] (x : ι → WN d) :
    ∫ ω, (⨆ i, W (x i) ω) ∂P =
      gaussianExpectedMax (Finset.univ : Finset ι) (fun i j => ⟪x i, x j⟫) 0 := by
  rw [← hW.integral_iSup_eq_gaussianExpectedMax]
  congr 1
  funext ω
  simp only [Pi.zero_apply, add_zero]
  exact (iSup_finset_univ fun i => W (x i) ω).symm

/-- **Finite Gaussian maximum** for white-noise pairings (no joint law needed). -/
theorem integral_iSup_abs_W_le (hW : IsWhiteNoise P W) {ι : Type*} [Fintype ι] (x : ι → WN d)
    {s : ℝ} (hs : 0 ≤ s) (hx : ∀ i, ‖x i‖ ≤ s) :
    ∫ ω, (⨆ i, |W (x i) ω|) ∂P ≤ s * Real.sqrt (2 * Real.log (2 * Fintype.card ι)) :=
  GaussianLQG.integral_iSup_abs_le (fun i => hW.hasLaw_single (x i)) hs fun i => by
    rw [Real.coe_toNNReal _ (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hx i) 2

end WN

/-! ## A fixed white noise -/

/-- A fixed white noise on `L²(ℝ × ℝ^d)` (P-F1's `exists_isWhiteNoise`, on `stdP`). -/
def W₀ (d : ℕ) : WN d → (ℕ → ℝ) → ℝ := (exists_isWhiteNoise d).choose

theorem isWhiteNoise_W₀ (d : ℕ) : IsWhiteNoise LQGDimension.ExistAsm.stdP (W₀ d) :=
  (exists_isWhiteNoise d).choose_spec

/-- `E max_i |W₀(x_i)|`. -/
def emaxAbs {ι : Type*} [Fintype ι] (x : ι → WN d) : ℝ :=
  ∫ ω, (⨆ i, |W₀ d (x i) ω|) ∂LQGDimension.ExistAsm.stdP

theorem integrable_iSup_abs_W₀ {ι : Type*} [Fintype ι] (x : ι → WN d) :
    Integrable (fun ω => ⨆ i, |W₀ d (x i) ω|) LQGDimension.ExistAsm.stdP :=
  integrable_iSup_fintype fun i => (integrable_W (isWhiteNoise_W₀ d) (x i)).abs

theorem emaxAbs_nonneg {ι : Type*} [Fintype ι] (x : ι → WN d) : 0 ≤ emaxAbs x := by
  refine integral_nonneg fun ω => ?_
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  · obtain ⟨j⟩ := hι
    exact (abs_nonneg _).trans
      (le_ciSup (f := fun i => |W₀ d (x i) ω|) (Finite.bddAbove_range _) j)

theorem emaxAbs_le {ι : Type*} [Fintype ι] (x : ι → WN d) {s : ℝ} (hs : 0 ≤ s)
    (hx : ∀ i, ‖x i‖ ≤ s) :
    emaxAbs x ≤ s * Real.sqrt (2 * Real.log (2 * Fintype.card ι)) :=
  integral_iSup_abs_W_le (isWhiteNoise_W₀ d) x hs hx

/-- Pointwise: `max_i |a_i + b_i| ≤ max_i |a_i| + max_i |b_i|`. -/
theorem iSup_abs_add_le {ι : Type*} [Fintype ι] (a b : ι → ℝ) :
    ⨆ i, |a i + b i| ≤ (⨆ i, |a i|) + ⨆ i, |b i| := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  · refine ciSup_le fun i => (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · exact le_ciSup (f := fun i => |a i|) (Finite.bddAbove_range _) i
    · exact le_ciSup (f := fun i => |b i|) (Finite.bddAbove_range _) i

theorem emaxAbs_add {ι : Type*} [Fintype ι] (x y : ι → WN d) :
    emaxAbs (fun i => x i + y i) ≤ emaxAbs x + emaxAbs y := by
  have hW := isWhiteNoise_W₀ d
  have := hW.isProbabilityMeasure
  have hae : ∀ᵐ ω ∂LQGDimension.ExistAsm.stdP, ∀ i,
      W₀ d (x i + y i) ω = W₀ d (x i) ω + W₀ d (y i) ω := by
    rw [ae_all_iff]
    exact fun i => hW.add_ae (x i) (y i)
  unfold emaxAbs
  rw [← integral_add (integrable_iSup_abs_W₀ x) (integrable_iSup_abs_W₀ y)]
  refine integral_mono_ae (integrable_iSup_abs_W₀ _)
    ((integrable_iSup_abs_W₀ x).add (integrable_iSup_abs_W₀ y)) ?_
  filter_upwards [hae] with ω hω
  simp only [hω]
  exact iSup_abs_add_le _ _

theorem emaxAbs_smul {ι : Type*} [Fintype ι] (c : ℝ) (x : ι → WN d) :
    emaxAbs (fun i => c • x i) = |c| * emaxAbs x := by
  have hW := isWhiteNoise_W₀ d
  have hae : ∀ᵐ ω ∂LQGDimension.ExistAsm.stdP, ∀ i, W₀ d (c • x i) ω = c * W₀ d (x i) ω := by
    rw [ae_all_iff]
    exact fun i => hW.smul_ae c (x i)
  unfold emaxAbs
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hae] with ω hω
  simp only [hω, abs_mul]
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  · exact (Real.mul_iSup_of_nonneg (abs_nonneg c) _).symm

theorem emaxAbs_neg {ι : Type*} [Fintype ι] (x : ι → WN d) :
    emaxAbs (fun i => -x i) = emaxAbs x := by
  have h := emaxAbs_smul (-1) x
  simp only [neg_smul, one_smul, abs_neg, abs_one, one_mul] at h
  exact h

/-- **The integrated form of `max (a + r) ≥ max a - max |r|`**:
`𝕄(x) ≥ 𝕄(y) - E max_i |W₀(x_i - y_i)|`. -/
theorem gEM_gram_ge {ι : Type*} [Fintype ι] (x y : ι → WN d) :
    gaussianExpectedMax (Finset.univ : Finset ι) (fun i j => ⟪y i, y j⟫) 0 -
        emaxAbs (fun i => x i - y i) ≤
      gaussianExpectedMax (Finset.univ : Finset ι) (fun i j => ⟪x i, x j⟫) 0 := by
  have hW := isWhiteNoise_W₀ d
  have := hW.isProbabilityMeasure
  rw [← integral_iSup_W_eq_gEM hW x, ← integral_iSup_W_eq_gEM hW y, emaxAbs,
    ← integral_sub (integrable_iSup_fintype fun i => integrable_W hW (y i))
      (integrable_iSup_abs_W₀ _)]
  have hae : ∀ᵐ ω ∂LQGDimension.ExistAsm.stdP, ∀ i,
      W₀ d (x i) ω = W₀ d (y i) ω + W₀ d (x i - y i) ω := by
    rw [ae_all_iff]
    intro i
    have h := hW.add_ae (y i) (x i - y i)
    rwa [add_sub_cancel] at h
  refine integral_mono_ae ((integrable_iSup_fintype fun i => integrable_W hW (y i)).sub
    (integrable_iSup_abs_W₀ _)) (integrable_iSup_fintype fun i => integrable_W hW (x i)) ?_
  filter_upwards [hae] with ω hω
  simp only [hω]
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  · rw [sub_le_iff_le_add]
    refine ciSup_le fun i => ?_
    have h1 : W₀ d (y i) ω + W₀ d (x i - y i) ω ≤ ⨆ j, (W₀ d (y j) ω + W₀ d (x j - y j) ω) :=
      le_ciSup (Finite.bddAbove_range (fun j => W₀ d (y j) ω + W₀ d (x j - y j) ω)) i
    have h2 : -W₀ d (x i - y i) ω ≤ ⨆ j, |W₀ d (x j - y j) ω| :=
      (neg_le_abs _).trans (le_ciSup (Finite.bddAbove_range (fun j => |W₀ d (x j - y j) ω|)) i)
    linarith

/-- **Perturbation of expected maxima** by vector perturbations of size `≤ s`. -/
theorem abs_gEM_gram_sub_le {ι : Type*} [Fintype ι] (x y : ι → WN d) {s : ℝ} (hs : 0 ≤ s)
    (hxy : ∀ i, ‖x i - y i‖ ≤ s) :
    |gaussianExpectedMax (Finset.univ : Finset ι) (fun i j => ⟪x i, x j⟫) 0 -
        gaussianExpectedMax (Finset.univ : Finset ι) (fun i j => ⟪y i, y j⟫) 0| ≤
      s * Real.sqrt (2 * Real.log (2 * Fintype.card ι)) := by
  have h1 := gEM_gram_ge x y
  have h2 := gEM_gram_ge y x
  have e1 := emaxAbs_le (fun i => x i - y i) hs hxy
  have e2 := emaxAbs_le (fun i => y i - x i) hs fun i => by rw [norm_sub_rev]; exact hxy i
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- The Gram matrix, hence `𝕄`, is invariant under a global sign. -/
theorem gEM_gram_neg {ι : Type*} [Fintype ι] (x : ι → WN d) :
    gaussianExpectedMax (Finset.univ : Finset ι) (fun i j => ⟪-x i, -x j⟫) 0 =
      gaussianExpectedMax (Finset.univ : Finset ι) (fun i j => ⟪x i, x j⟫) 0 := by
  simp only [inner_neg_neg]

end HigherDimLFPP.Lower
