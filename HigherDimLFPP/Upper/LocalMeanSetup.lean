import HigherDimLFPP.Field.PolygonLimit
import HigherDimLFPP.Field.Similarity
import HigherDimLFPP.Var.Theorem11
import HigherDimLFPP.Var.Blocks
import HigherDimLFPP.Upper.GoodNode
import LQGDimension.Gaussian.ChainingBox
import LQGDimension.Gaussian.Concentration
import LQGDimension.LFPP.ExpectedSupLimit

/-!
# Lemma 4.3, set-up: finite Gaussian tools, the Brownian kernel, similarities

Source: `source/higher-dimensional-lfpp-limit.pdf`, §4.2, Lemma 4.3 (text lines 692–803), as
completed by the planning audit HA3 (`planning/audits/HA3-section-4.md`), Details D5 (Steps 1c,
2a–2c) and finding F16; packet P-U4.

This file collects the generic ingredients of Lemma 4.3 that do not involve the polygon
geometry of Step 1.

* **Comparison with an independent sum** (`gEM_le_add_of_dist`, HA3 D5 Step 2c): if the
  canonical distance of a Gaussian family is dominated by the sum of the canonical distances of
  two Gaussian families on the same index set, then its penalized expected maximum is at most the
  sum of theirs.  Sudakov–Fernique with drift (`LQGDimension.sudakovFernique`) against the
  orthogonal sum of Gram vectors, then "a maximum of a sum is at most the sum of the maxima".
* **Shells** (`vecEM_le_add_sum_shells`, `integral_max_zero_iSup_sub_le`; HA3 D5 Step 1c with the
  fix F6): with a reference element of value `0` in the compact part,
  `max_F ≤ max_{F'} + Σ_k (max_{F_k} X - λ_k)₊`, and each positive part has mean at most
  `exp(E max_{F_k} X - λ_k - 1 + π²σ²/8)` (`x₊ ≤ e^{x-1}` and Gaussian concentration
  `LQGDimension.MaxConc.integral_exp_max_le`).
* **The Brownian kernel** (`bmCov`, HA3 D5 Step 2c): `B(p) = Σ_j β_j(p_j)` for independent
  two-sided Brownian motions, with covariance `½ Σ_j (|p_j| + |q_j| - |p_j - q_j|)` and canonical
  distance `Σ_j |p_j - q_j|`; it is positive semidefinite (`psdOn_bmCov`) and its expected maximum
  over a box of sup-diameter `a` in `ℝ^D` is at most `20 √5 √D √((D+1) a)`
  (`gEM_bmCov_le`, chaining on a box).
* **Rotations and similarities** (HA3 F16): `rotE e` is the reflection in the line `ℝ (e₁ + e)`;
  it is a linear isometry with `rotE e e₁ = e` for unit `e ≠ -e₁`, and it is Lipschitz in `e`
  (`norm_rotE_sub_le`).  `simOf x y = x + |y - x| rotE((y-x)/|y-x|)` carries `0, e₁` to `x, y`
  (`simOf_zero`, `simOf_e₁`) and depends Lipschitz-continuously on the endpoints
  (`norm_simOf_sub_le`, the estimate (4.14)).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped RealInnerProductSpace Matrix

namespace HigherDimLFPP.Upper

open LQGDimension (gaussianExpectedMax vecExpectedMax PSDOn)

/-! ## Finite Gaussian families -/

section Gaussian

/-- The canonical squared distance of a Gram family. -/
theorem norm_sub_sq_eq_of_gram {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {F : Finset ι} {C : ι → ι → ℝ} {v : ι → E} (hv : ∀ i ∈ F, ∀ j ∈ F, ⟪v i, v j⟫ = C i j)
    {i j : ι} (hi : i ∈ F) (hj : j ∈ F) :
    ‖v i - v j‖ ^ 2 = C i i + C j j - 2 * C i j := by
  rw [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, inner_sub_right,
    hv i hi i hi, hv i hi j hj, hv j hj i hi, hv j hj j hj]
  have hsym : C j i = C i j := by rw [← hv j hj i hi, ← hv i hi j hj, real_inner_comm]
  rw [hsym]
  ring

/-- The two-block orthogonal sum `(a, b) ↦ (a, b) ∈ E ⊕₂ E`. -/
theorem norm_toLp_pair_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (a b : E) :
    ‖(WithLp.toLp 2 ![a, b] : PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]
  rfl

theorem inner_toLp_pair {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (a b a' b' : E) :
    ⟪(WithLp.toLp 2 ![a, b] : PiLp 2 (fun _ : Fin 2 => E)), WithLp.toLp 2 ![a', b']⟫ =
      ⟪a, a'⟫ + ⟪b, b'⟫ := by
  rw [PiLp.inner_apply, Fin.sum_univ_two]
  rfl

/-- **Comparison with an independent sum** (HA3 D5, Step 2c): if the canonical distance of the
centered Gaussian family with covariance `C` is dominated by the sum of the canonical distances
for `C₁` and `C₂` (all PSD on `F`), then
`E max_F (X + b₁ + b₂) ≤ E max_F (X₁ + b₁) + E max_F (X₂ + b₂)`. -/
theorem gEM_le_add_of_dist {ι : Type} (F : Finset ι) {C C₁ C₂ : ι → ι → ℝ}
    (hC : PSDOn F C) (hC₁ : PSDOn F C₁) (hC₂ : PSDOn F C₂) (b₁ b₂ : ι → ℝ)
    (hdist : ∀ i ∈ F, ∀ j ∈ F, C i i + C j j - 2 * C i j ≤
      (C₁ i i + C₁ j j - 2 * C₁ i j) + (C₂ i i + C₂ j j - 2 * C₂ i j)) :
    gaussianExpectedMax F C (fun i => b₁ i + b₂ i) ≤
      gaussianExpectedMax F C₁ b₁ + gaussianExpectedMax F C₂ b₂ := by
  classical
  obtain ⟨v, hv, hvE⟩ := LQGDimension.exists_vecExpectedMax_eq_gaussianExpectedMax F C hC
  obtain ⟨v₁, hv₁, hv₁E⟩ := LQGDimension.exists_vecExpectedMax_eq_gaussianExpectedMax F C₁ hC₁
  obtain ⟨v₂, hv₂, hv₂E⟩ := LQGDimension.exists_vecExpectedMax_eq_gaussianExpectedMax F C₂ hC₂
  let w₁ : ι → PiLp 2 (fun _ : Fin 2 => EuclideanSpace ℝ F) := fun i => WithLp.toLp 2 ![v₁ i, 0]
  let w₂ : ι → PiLp 2 (fun _ : Fin 2 => EuclideanSpace ℝ F) := fun i => WithLp.toLp 2 ![0, v₂ i]
  have hsum : ∀ i, w₁ i + w₂ i = WithLp.toLp 2 ![v₁ i, v₂ i] := by
    intro i
    ext k : 1
    fin_cases k <;> simp [w₁, w₂]
  have hsub : ∀ i j, (w₁ i + w₂ i) - (w₁ j + w₂ j) =
      WithLp.toLp 2 ![v₁ i - v₁ j, v₂ i - v₂ j] := by
    intro i j
    rw [hsum, hsum]
    ext k : 1
    fin_cases k <;> simp
  -- Step 1: Sudakov–Fernique against the orthogonal sum
  have hSF : vecExpectedMax F v (fun i => b₁ i + b₂ i) ≤
      vecExpectedMax F (fun i => w₁ i + w₂ i) (fun i => b₁ i + b₂ i) := by
    refine LQGDimension.sudakovFernique ι (EuclideanSpace ℝ F)
      (PiLp 2 (fun _ : Fin 2 => EuclideanSpace ℝ F)) F v (fun i => w₁ i + w₂ i)
      (fun i => b₁ i + b₂ i) fun i hi j hj => ?_
    rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sub_sq_eq_of_gram hv hi hj, hsub,
      norm_toLp_pair_sq, norm_sub_sq_eq_of_gram hv₁ hi hj, norm_sub_sq_eq_of_gram hv₂ hi hj]
    exact hdist i hi j hj
  -- Step 2: a maximum of a sum is at most the sum of the maxima
  have hadd := LQGDimension.Subadd.vecEM_add_le LQGDimension.maxIntegrable F w₁ w₂ b₁ b₂
  -- Step 3: each block has the Gram matrix of its own family
  have e₁ : vecExpectedMax F w₁ b₁ = vecExpectedMax F v₁ b₁ :=
    LQGDimension.vecExpectedMax_eq_of_gram_eq F w₁ v₁ b₁ fun i _ j _ => by
      simp only [w₁, inner_toLp_pair, inner_zero_left, add_zero]
  have e₂ : vecExpectedMax F w₂ b₂ = vecExpectedMax F v₂ b₂ :=
    LQGDimension.vecExpectedMax_eq_of_gram_eq F w₂ v₂ b₂ fun i _ j _ => by
      simp only [w₂, inner_toLp_pair, inner_zero_left, zero_add]
  rw [hvE, hv₁E, hv₂E]
  exact hSF.trans (hadd.trans (le_of_eq (by rw [e₁, e₂])))

/-- `gaussianExpectedMax` is monotone in the drift, up to a constant (`F` nonempty). -/
theorem gEM_le_of_drift_le {ι : Type*} (F : Finset ι) (hF : F.Nonempty) {C : ι → ι → ℝ}
    (hC : PSDOn F C) {b b' : ι → ℝ} {γ : ℝ} (h : ∀ i ∈ F, b i ≤ b' i + γ) :
    gaussianExpectedMax F C b ≤ gaussianExpectedMax F C b' + γ := by
  obtain ⟨v, -, hvE⟩ := LQGDimension.exists_vecExpectedMax_eq_gaussianExpectedMax F C hC
  rw [hvE b, hvE b']
  exact LQGDimension.ESLimit.vecExpectedMax_le_of_drift_le F hF v b b' h

/-- `x₊ ≤ e^{x - 1}`. -/
theorem max_zero_le_exp_sub_one (x : ℝ) : max 0 x ≤ Real.exp (x - 1) := by
  rcases le_total x 0 with h | h
  · rw [max_eq_left h]; exact (Real.exp_pos _).le
  · rw [max_eq_right h]
    linarith [Real.add_one_le_exp (x - 1)]

section Vec

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Mean of a positive part of a Gaussian maximum** (HA3 D5, Step 1c): if `‖v i‖ ≤ σ` on `G`,
then `E (max_G (X + b) - c)₊ ≤ exp(E max_G (X + b) - c - 1 + π² σ² / 8)`. -/
theorem integral_max_zero_iSup_sub_le (G : Finset ι) (v : ι → E) (b : ι → ℝ) {σ : ℝ}
    (hσ : ∀ i ∈ G, ‖v i‖ ≤ σ) (c : ℝ) :
    ∫ x, max 0 ((⨆ i : G, ⟪v i, x⟫ + b i) - c) ∂(stdGaussian E) ≤
      Real.exp (vecExpectedMax G v b - c - 1 + Real.pi ^ 2 / 8 * σ ^ 2) := by
  set M : E → ℝ := fun x => ⨆ i : G, ⟪v i, x⟫ + b i with hM
  set EM := vecExpectedMax G v b with hEM
  have hMi : Integrable M (stdGaussian E) := LQGDimension.integrable_iSup_inner_add G v b
  have hexp := LQGDimension.MaxConc.integrable_exp_max G v b hσ 1
  have hexp' := LQGDimension.MaxConc.integral_exp_max_le G v b hσ 1
  simp only [one_mul, one_pow, mul_one] at hexp hexp'
  have hpt : ∀ x, max 0 (M x - c) ≤ Real.exp (EM - c - 1) * Real.exp (M x - EM) := by
    intro x
    refine (max_zero_le_exp_sub_one _).trans (le_of_eq ?_)
    rw [← Real.exp_add]
    congr 1
    ring
  have hint1 : Integrable (fun x => max 0 (M x - c)) (stdGaussian E) := by
    have := (hMi.sub (integrable_const c)).pos_part
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply, max_comm]
  calc ∫ x, max 0 (M x - c) ∂(stdGaussian E)
      ≤ ∫ x, Real.exp (EM - c - 1) * Real.exp (M x - EM) ∂(stdGaussian E) :=
        integral_mono hint1 (hexp.const_mul _) hpt
    _ = Real.exp (EM - c - 1) * ∫ x, Real.exp (M x - EM) ∂(stdGaussian E) := integral_const_mul _ _
    _ ≤ Real.exp (EM - c - 1) * Real.exp (Real.pi ^ 2 / 8 * σ ^ 2) :=
        mul_le_mul_of_nonneg_left hexp' (Real.exp_pos _).le
    _ = Real.exp (EM - c - 1 + Real.pi ^ 2 / 8 * σ ^ 2) := (Real.exp_add _ _).symm

/-- **Shell decomposition** (HA3 D5, Step 1c, with the fix F6).  Let `F' ⊆ ι` contain an element
`i₀` of value `0` (`v i₀ = 0`, `b i₀ ≥ 0`), and let every `i ∈ F \ F'` lie in a shell
`sh i ∈ S` with `b i ≤ -λ(sh i)`.  Then
`E max_F (X + b) ≤ E max_{F'} (X + b) + Σ_{k ∈ S} E (max_{F_k} X - λ_k)₊`, where
`F_k = {i ∈ F \ F' : sh i = k}`. -/
theorem vecEM_le_add_sum_shells [DecidableEq ι] (F F' : Finset ι) (v : ι → E) (b : ι → ℝ)
    {i₀ : ι} (hi₀ : i₀ ∈ F') (hv₀ : v i₀ = 0) (hb₀ : 0 ≤ b i₀) (S : Finset ℕ) (sh : ι → ℕ)
    (lev : ℕ → ℝ) (hcov : ∀ i ∈ F, i ∉ F' → sh i ∈ S ∧ b i ≤ -lev (sh i)) :
    vecExpectedMax F v b ≤ vecExpectedMax F' v b +
      ∑ k ∈ S, ∫ x, max 0 ((⨆ i : F.filter (fun i => i ∉ F' ∧ sh i = k),
        ⟪v i, x⟫ + (fun _ => (0 : ℝ)) i) - lev k) ∂(stdGaussian E) := by
  set Fk : ℕ → Finset ι := fun k => F.filter (fun i => i ∉ F' ∧ sh i = k) with hFk
  have hpt : ∀ x : E, (⨆ i : F, ⟪v i, x⟫ + b i) ≤ (⨆ i : F', ⟪v i, x⟫ + b i) +
      ∑ k ∈ S, max 0 ((⨆ i : Fk k, ⟪v i, x⟫ + (fun _ => (0 : ℝ)) i) - lev k) := by
    intro x
    have hM' : 0 ≤ ⨆ i : F', ⟪v i, x⟫ + b i := by
      have h1 : ⟪v i₀, x⟫ + b i₀ ≤ ⨆ i : F', ⟪v i, x⟫ + b i :=
        le_ciSup (f := fun i : F' => ⟪v i, x⟫ + b i) (Finite.bddAbove_range _) ⟨i₀, hi₀⟩
      rw [hv₀, inner_zero_left, zero_add] at h1
      linarith
    have hsum0 : 0 ≤ ∑ k ∈ S, max 0 ((⨆ i : Fk k, ⟪v i, x⟫ + (fun _ => (0 : ℝ)) i) - lev k) :=
      Finset.sum_nonneg fun k _ => le_max_left _ _
    rcases isEmpty_or_nonempty F with hE | hne
    · rw [Real.iSup_of_isEmpty]
      linarith
    refine ciSup_le fun i => ?_
    by_cases hi : (i : ι) ∈ F'
    · have h1 : ⟪v i, x⟫ + b i ≤ ⨆ i : F', ⟪v i, x⟫ + b i :=
        le_ciSup (f := fun i : F' => ⟪v i, x⟫ + b i) (Finite.bddAbove_range _) ⟨i, hi⟩
      linarith
    · obtain ⟨hk, hb⟩ := hcov i i.2 hi
      have hmem : (i : ι) ∈ Fk (sh i) := Finset.mem_filter.2 ⟨i.2, hi, rfl⟩
      have h1 : ⟪v i, x⟫ + (fun _ => (0 : ℝ)) (i : ι) ≤
          ⨆ j : Fk (sh i), ⟪v j, x⟫ + (fun _ => (0 : ℝ)) (j : ι) :=
        le_ciSup (f := fun j : Fk (sh i) => ⟪v j, x⟫ + (fun _ => (0 : ℝ)) (j : ι))
          (Finite.bddAbove_range _) ⟨i, hmem⟩
      have h2 : max 0 ((⨆ j : Fk (sh i), ⟪v j, x⟫ + (fun _ => (0 : ℝ)) (j : ι)) - lev (sh i)) ≤
          ∑ k ∈ S, max 0 ((⨆ j : Fk k, ⟪v j, x⟫ + (fun _ => (0 : ℝ)) (j : ι)) - lev k) :=
        Finset.single_le_sum (f := fun k => max 0 ((⨆ j : Fk k, ⟪v j, x⟫ +
          (fun _ => (0 : ℝ)) (j : ι)) - lev k)) (fun k _ => le_max_left _ _) hk
      simp only [add_zero] at h1 h2 ⊢
      have h3 := le_max_right (0 : ℝ) ((⨆ j : Fk (sh i), ⟪v j, x⟫) - lev (sh i))
      linarith
  have hint : ∀ k, Integrable (fun x => max 0 ((⨆ i : Fk k, ⟪v i, x⟫ + (fun _ => (0 : ℝ)) i) -
      lev k)) (stdGaussian E) := by
    intro k
    have := ((LQGDimension.integrable_iSup_inner_add (Fk k) v (fun _ => 0)).sub
      (integrable_const (lev k))).pos_part
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply, max_comm]
  have hF' := LQGDimension.integrable_iSup_inner_add F' v b
  unfold vecExpectedMax
  calc ∫ x, (⨆ i : F, ⟪v i, x⟫ + b i) ∂(stdGaussian E)
      ≤ ∫ x, ((⨆ i : F', ⟪v i, x⟫ + b i) + ∑ k ∈ S, max 0 ((⨆ i : Fk k, ⟪v i, x⟫ +
          (fun _ => (0 : ℝ)) i) - lev k)) ∂(stdGaussian E) :=
        integral_mono (LQGDimension.integrable_iSup_inner_add F v b)
          (hF'.add (integrable_finsetSum S fun k _ => hint k)) hpt
    _ = _ := by
        rw [integral_add hF' (integrable_finsetSum S fun k _ => hint k),
          integral_finsetSum S fun k _ => hint k]

end Vec

end Gaussian

/-! ## The Brownian kernel -/

section Brownian

/-- Covariance of `B(p) = Σ_j β_j(p_j)` for independent two-sided standard Brownian motions:
`½ Σ_j (|p_j| + |q_j| - |p_j - q_j|)` (HA3 D5, Step 2c). -/
def bmCov {D : ℕ} (p q : Fin D → ℝ) : ℝ := ∑ j, (|p j| + |q j| - |p j - q j|) / 2

theorem bmCov_comm {D : ℕ} (p q : Fin D → ℝ) : bmCov p q = bmCov q p := by
  unfold bmCov
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [abs_sub_comm (p j)]
  ring

/-- The canonical distance of `B` is `Σ_j |p_j - q_j|`. -/
theorem bmCov_dist {D : ℕ} (p q : Fin D → ℝ) :
    bmCov p p + bmCov q q - 2 * bmCov p q = ∑ j, |p j - q j| := by
  unfold bmCov
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [sub_self, abs_zero]
  ring

/-- **The Brownian kernel is positive semidefinite** (sum over coordinates of the kernel
`|a| + |b| - |a - b|`, `HigherDimLFPP.Var.kernelR_sum_nonneg`). -/
theorem psdOn_bmCov {ι : Type*} {D : ℕ} (F : Finset ι) (P : ι → Fin D → ℝ) :
    PSDOn F (fun i j => bmCov (P i) (P j)) := by
  rw [LQGDimension.PSDOn, Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨Matrix.IsHermitian.ext fun i j => ?_, fun c => ?_⟩
  · simp only [Matrix.of_apply, star_trivial]
    exact bmCov_comm _ _
  · have hsum : star c ⬝ᵥ ((Matrix.of fun i j : F => bmCov (P i) (P j)) *ᵥ c)
        = ∑ i : F, ∑ j : F, c i * c j * bmCov (P i) (P j) := by
      simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, star_trivial]
      exact Finset.sum_congr rfl fun i _ => by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
    have hsum2 : ∑ i : F, ∑ j : F, c i * c j * bmCov (P i) (P j)
        = ∑ k : Fin D, (1 / 2 : ℝ) * ∑ i : F, ∑ j : F, c i * c j *
          (|P i k| + |P j k| - |P i k - P j k|) := by
      calc ∑ i : F, ∑ j : F, c i * c j * bmCov (P i) (P j)
          = ∑ i : F, ∑ j : F, ∑ k : Fin D, (1 / 2 : ℝ) * (c i * c j *
              (|P i k| + |P j k| - |P i k - P j k|)) := by
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
            rw [bmCov, Finset.mul_sum]
            exact Finset.sum_congr rfl fun k _ => by ring
        _ = ∑ i : F, ∑ k : Fin D, ∑ j : F, (1 / 2 : ℝ) * (c i * c j *
              (|P i k| + |P j k| - |P i k - P j k|)) :=
            Finset.sum_congr rfl fun i _ => Finset.sum_comm
        _ = ∑ k : Fin D, ∑ i : F, ∑ j : F, (1 / 2 : ℝ) * (c i * c j *
              (|P i k| + |P j k| - |P i k - P j k|)) := Finset.sum_comm
        _ = _ := by simp only [Finset.mul_sum]
    rw [hsum, hsum2]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (by norm_num)
      (HigherDimLFPP.Var.kernelR_sum_nonneg Finset.univ (fun i : F => P i k) c)

/-- **The expected maximum of `B` over a box** (HA3 D5, Step 2c): if the parameters have
sup-diameter at most `a` on `F`, then `E max_F B ≤ 20 √5 √D √((D + 1) a)` (chaining on a box,
`LQGDimension.ChainBox.chainingBox_bound`, with canonical metric `Σ_j |p_j - q_j| ≤ D ‖p - q‖`). -/
theorem gEM_bmCov_le {ι : Type} {D : ℕ} (F : Finset ι) (P : ι → Fin D → ℝ) {a : ℝ}
    (hP : ∀ i ∈ F, ∀ j ∈ F, ‖P i - P j‖ ≤ a) :
    gaussianExpectedMax F (fun i j => bmCov (P i) (P j)) (fun _ => 0) ≤
      20 * Real.sqrt 5 * Real.sqrt D * Real.sqrt ((D + 1) * a) := by
  rcases F.eq_empty_or_nonempty with rfl | ⟨i₀, hi₀⟩
  · rw [HigherDimLFPP.Var.gEM_empty]
    positivity
  obtain ⟨v, hv, hvE⟩ := LQGDimension.exists_vecExpectedMax_eq_gaussianExpectedMax F _
    (psdOn_bmCov F P)
  rw [hvE]
  have hvv : ∀ i ∈ F, ∀ j ∈ F, ‖v i - v j‖ ^ 2 ≤ Real.sqrt D ^ 2 * ‖P i - P j‖ := by
    intro i hi j hj
    rw [norm_sub_sq_eq_of_gram hv hi hj, bmCov_dist, Real.sq_sqrt (Nat.cast_nonneg _)]
    calc ∑ k, |P i k - P j k| ≤ ∑ _k : Fin D, ‖P i - P j‖ :=
          Finset.sum_le_sum fun k _ => by
            rw [← Real.norm_eq_abs]
            exact norm_le_pi_norm (P i - P j) k
      _ = D * ‖P i - P j‖ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hSF : vecExpectedMax F v (fun _ => 0) ≤ vecExpectedMax F (fun i => v i - v i₀) (fun _ => 0) :=
    LQGDimension.sudakovFernique ι (EuclideanSpace ℝ F) (EuclideanSpace ℝ F) F v
      (fun i => v i - v i₀) (fun _ => 0) (fun i _ j _ => by rw [sub_sub_sub_cancel_right])
  have hch := LQGDimension.ChainBox.chainingBox_bound F P v (Real.sqrt_nonneg _) hP hvv hi₀
  exact hSF.trans hch

end Brownian

/-! ## Rotations and similarities (HA3 F16 and D5, Step 2a) -/

section Similarity

/-- `‖w/|w| - w'/|w'|‖ ≤ 2 |w - w'| / |w|` for `w ≠ 0`. -/
theorem norm_normalize_sub_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {w : E}
    (hw : w ≠ 0) (w' : E) : ‖‖w‖⁻¹ • w - ‖w'‖⁻¹ • w'‖ ≤ 2 * ‖w - w'‖ / ‖w‖ := by
  have hw0 : 0 < ‖w‖ := norm_pos_iff.2 hw
  have e : ‖w‖⁻¹ • w - ‖w'‖⁻¹ • w' = ‖w‖⁻¹ • (w - w') + (‖w‖⁻¹ - ‖w'‖⁻¹) • w' := by
    rw [smul_sub, sub_smul]; abel
  have h1 : ‖‖w‖⁻¹ • (w - w')‖ = ‖w - w'‖ / ‖w‖ := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_eq_div]
  have h2 : ‖(‖w‖⁻¹ - ‖w'‖⁻¹) • w'‖ ≤ ‖w - w'‖ / ‖w‖ := by
    rcases eq_or_ne w' 0 with rfl | hw'
    · rw [smul_zero, norm_zero]; positivity
    · have hw'0 : 0 < ‖w'‖ := norm_pos_iff.2 hw'
      rw [norm_smul, Real.norm_eq_abs]
      have key : |‖w‖⁻¹ - ‖w'‖⁻¹| * ‖w'‖ = |‖w'‖ - ‖w‖| / ‖w‖ := by
        rw [show ‖w‖⁻¹ - ‖w'‖⁻¹ = (‖w'‖ - ‖w‖) / (‖w‖ * ‖w'‖) by field_simp, abs_div,
          abs_of_pos (mul_pos hw0 hw'0)]
        field_simp
      rw [key, norm_sub_rev w w']
      exact div_le_div_of_nonneg_right (abs_norm_sub_norm_le w' w) hw0.le
  rw [e]
  calc ‖‖w‖⁻¹ • (w - w') + (‖w‖⁻¹ - ‖w'‖⁻¹) • w'‖
      ≤ ‖‖w‖⁻¹ • (w - w')‖ + ‖(‖w‖⁻¹ - ‖w'‖⁻¹) • w'‖ := norm_add_le _ _
    _ ≤ ‖w - w'‖ / ‖w‖ + ‖w - w'‖ / ‖w‖ := add_le_add h1.le h2
    _ = 2 * ‖w - w'‖ / ‖w‖ := by ring

/-- `‖|w|⁻¹ w‖ = 1` for `w ≠ 0`. -/
theorem norm_inv_norm_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {w : E}
    (hw : w ≠ 0) : ‖‖w‖⁻¹ • w‖ = 1 := by
  rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hw)]

variable {d : ℕ}

/-- The reflection in the line `ℝ (e₁ + e)` (HA3 F16): a linear isometry of `ℝ^d` carrying `e₁`
to `e` for every unit vector `e ≠ -e₁` (`rotE_e₁`), depending Lipschitz-continuously on `e` near
`e₁` (`norm_rotE_sub_le`).  (The product `H_{e₁+e} ∘ H_{e₁}` of HA3 F16 is `-rotE e`; any isometry
works since `Λ` and `G_K` are invariant under all isometries.) -/
def rotE (e : Rd d) : Rd d ≃ₗᵢ[ℝ] Rd d := (ℝ ∙ (e₁ d + e)).reflection

theorem rotE_apply (e z : Rd d) :
    rotE e z = (2 * (⟪e₁ d + e, z⟫ / ‖e₁ d + e‖ ^ 2)) • (e₁ d + e) - z := by
  rw [rotE, Submodule.reflection_singleton_apply]
  simp only [RCLike.ofReal_real_eq_id, id, two_nsmul, two_mul, add_smul]

/-- `rotE e` in terms of the unit vector `ŵ = (e₁ + e)/|e₁ + e|`: `z ↦ 2 ⟪ŵ, z⟫ ŵ - z`. -/
theorem rotE_apply' (e z : Rd d) :
    rotE e z = (2 * ⟪‖e₁ d + e‖⁻¹ • (e₁ d + e), z⟫) • (‖e₁ d + e‖⁻¹ • (e₁ d + e)) - z := by
  rw [rotE_apply, smul_smul, real_inner_smul_left]
  congr 2
  rw [div_eq_mul_inv, sq, mul_inv]
  ring

theorem rotE_e₁ (hd : 0 < d) {e : Rd d} (he : ‖e‖ = 1) (hne : e₁ d + e ≠ 0) :
    rotE e (e₁ d) = e := by
  have h1 : ⟪e₁ d + e, e₁ d⟫ = 1 + ⟪e₁ d, e⟫ := by
    rw [inner_add_left, Lower.inner_e₁_self hd, real_inner_comm]
  have h2 : ‖e₁ d + e‖ ^ 2 = 2 * (1 + ⟪e₁ d, e⟫) := by
    rw [norm_add_sq_real, Lower.norm_e₁ hd, he]
    ring
  have h3 : ‖e₁ d + e‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hne)
  have h5 : 1 + ⟪e₁ d, e⟫ ≠ 0 := fun h => h3 (by rw [h2, h, mul_zero])
  have h4 : 2 * (⟪e₁ d + e, e₁ d⟫ / ‖e₁ d + e‖ ^ 2) = 1 := by
    rw [h1, h2]
    field_simp
  rw [rotE_apply, h4, one_smul]
  abel

/-- **Lipschitz dependence of the rotation** (HA3 F16): if `|e₁ + e|, |e₁ + e'| ≥ 1`, then
`|rotE e z - rotE e' z| ≤ 8 |e - e'| |z|`. -/
theorem norm_rotE_sub_le {e e' : Rd d} (h : 1 ≤ ‖e₁ d + e‖) (h' : 1 ≤ ‖e₁ d + e'‖) (z : Rd d) :
    ‖rotE e z - rotE e' z‖ ≤ 8 * ‖e - e'‖ * ‖z‖ := by
  set w := e₁ d + e with hw
  set w' := e₁ d + e' with hw'
  have hw0 : w ≠ 0 := norm_ne_zero_iff.1 (by linarith)
  have hw'0 : w' ≠ 0 := norm_ne_zero_iff.1 (by linarith)
  set u := ‖w‖⁻¹ • w with hu
  set u' := ‖w'‖⁻¹ • w' with hu'
  have hu1 : ‖u‖ = 1 := norm_inv_norm_smul hw0
  have hu1' : ‖u'‖ = 1 := norm_inv_norm_smul hw'0
  have huu : ‖u - u'‖ ≤ 2 * ‖e - e'‖ := by
    have := norm_normalize_sub_le hw0 w'
    have e1 : w - w' = e - e' := by rw [hw, hw']; abel
    rw [e1] at this
    refine this.trans ?_
    rw [div_le_iff₀ (by linarith)]
    nlinarith [norm_nonneg (e - e')]
  have e2 : rotE e z - rotE e' z = (2 : ℝ) • (⟪u - u', z⟫ • u + ⟪u', z⟫ • (u - u')) := by
    rw [rotE_apply', rotE_apply', ← hw, ← hw', ← hu, ← hu', inner_sub_left, sub_smul,
      smul_sub, mul_smul, mul_smul]
    module
  rw [e2, norm_smul, Real.norm_two]
  have e3 : ‖⟪u - u', z⟫ • u + ⟪u', z⟫ • (u - u')‖ ≤ 2 * ‖u - u'‖ * ‖z‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul (⟪u - u', z⟫) u, norm_smul (⟪u', z⟫) (u - u'), hu1, mul_one, Real.norm_eq_abs,
      Real.norm_eq_abs]
    have a1 := abs_real_inner_le_norm (u - u') z
    have a2 := abs_real_inner_le_norm u' z
    rw [hu1', one_mul] at a2
    nlinarith [norm_nonneg (u - u'), norm_nonneg z]
  nlinarith [norm_nonneg z, norm_nonneg (u - u'), norm_nonneg (e - e')]

/-- The similarity `z ↦ x + |y - x| rotE((y - x)/|y - x|) z` carrying `0, e₁` to `x, y`
(HA3 D5, Step 2a). -/
def simOf (x y : Rd d) : Rd d → Rd d :=
  simAffine x ‖y - x‖ (rotE (‖y - x‖⁻¹ • (y - x)))

/-- The inverse similarity `z ↦ |y - x|⁻¹ rotE(…)⁻¹ (z - x)`. -/
def simInv (x y : Rd d) : Rd d → Rd d :=
  simAffine (-(‖y - x‖⁻¹ • (rotE (‖y - x‖⁻¹ • (y - x))).symm x)) ‖y - x‖⁻¹
    (rotE (‖y - x‖⁻¹ • (y - x))).symm

theorem simOf_zero (x y : Rd d) : simOf x y 0 = x := by
  simp only [simOf, simAffine, map_zero, smul_zero, add_zero]

theorem simOf_e₁ (hd : 0 < d) {x y : Rd d} (hxy : x ≠ y)
    (hne : e₁ d + ‖y - x‖⁻¹ • (y - x) ≠ 0) : simOf x y (e₁ d) = y := by
  have hv : y - x ≠ 0 := sub_ne_zero.2 (Ne.symm hxy)
  have hR : ‖y - x‖ ≠ 0 := norm_ne_zero_iff.2 hv
  rw [simOf, simAffine, rotE_e₁ hd (norm_inv_norm_smul hv) hne, smul_smul,
    mul_inv_cancel₀ hR, one_smul]
  abel

theorem simOf_simInv {x y : Rd d} (hxy : x ≠ y) (z : Rd d) : simOf x y (simInv x y z) = z := by
  have hR : ‖y - x‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 (Ne.symm hxy))
  simp only [simOf, simInv, simAffine, map_add, map_neg, map_smul,
    LinearIsometryEquiv.apply_symm_apply, smul_add, smul_neg, smul_smul, mul_inv_cancel₀ hR,
    one_smul]
  abel

theorem simInv_simOf {x y : Rd d} (hxy : x ≠ y) (z : Rd d) : simInv x y (simOf x y z) = z := by
  have hR : ‖y - x‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 (Ne.symm hxy))
  simp only [simOf, simInv, simAffine, map_add, map_smul, LinearIsometryEquiv.symm_apply_apply,
    smul_add, smul_smul, inv_mul_cancel₀ hR, one_smul]
  abel

/-- **The endpoint estimate (4.14)**: for chords of length in `[1/2, 2]` whose directions `u, u'`
satisfy `|e₁ + u|, |e₁ + u'| ≥ 1`, and `|z| ≤ 2`,
`|simOf x y z - simOf x' y' z| ≤ 200 (|x - x'| + |y - y'|)`. -/
theorem norm_simOf_sub_le {x y x' y' z : Rd d} (hr : 1 / 2 ≤ ‖y - x‖) (hr' : ‖y' - x'‖ ≤ 2)
    (hu : 1 ≤ ‖e₁ d + ‖y - x‖⁻¹ • (y - x)‖) (hu' : 1 ≤ ‖e₁ d + ‖y' - x'‖⁻¹ • (y' - x')‖)
    (hz : ‖z‖ ≤ 2) :
    ‖simOf x y z - simOf x' y' z‖ ≤ 200 * (‖x - x'‖ + ‖y - y'‖) := by
  set Δ := ‖x - x'‖ + ‖y - y'‖ with hΔ
  have hv : y - x ≠ 0 := norm_ne_zero_iff.1 (by linarith)
  have hdv : ‖(y - x) - (y' - x')‖ ≤ Δ := by
    calc ‖(y - x) - (y' - x')‖ = ‖(y - y') - (x - x')‖ := by congr 1; abel
      _ ≤ ‖y - y'‖ + ‖x - x'‖ := norm_sub_le _ _
      _ = Δ := by rw [hΔ]; ring
  have hdr : |‖y - x‖ - ‖y' - x'‖| ≤ Δ := (abs_norm_sub_norm_le _ _).trans hdv
  have hdu : ‖‖y - x‖⁻¹ • (y - x) - ‖y' - x'‖⁻¹ • (y' - x')‖ ≤ 4 * Δ := by
    refine (norm_normalize_sub_le hv _).trans ?_
    rw [div_le_iff₀ (by linarith)]
    nlinarith [norm_nonneg ((y - x) - (y' - x'))]
  have hrot := norm_rotE_sub_le hu hu' z
  obtain ⟨O, hO⟩ : ∃ O, O = rotE (‖y - x‖⁻¹ • (y - x)) := ⟨_, rfl⟩
  obtain ⟨O', hO'⟩ : ∃ O', O' = rotE (‖y' - x'‖⁻¹ • (y' - x')) := ⟨_, rfl⟩
  rw [← hO, ← hO'] at hrot
  have alg : ∀ (a b : Rd d) (r r' : ℝ), (x + r • a) - (x' + r' • b) =
      (x - x') + (r - r') • a + r' • (a - b) := fun a b r r' => by module
  have e1 : simOf x y z - simOf x' y' z =
      (x - x') + (‖y - x‖ - ‖y' - x'‖) • O z + ‖y' - x'‖ • (O z - O' z) := by
    simp only [simOf, simAffine, ← hO, ← hO']
    exact alg _ _ _ _
  rw [e1]
  have hOz : ‖O z‖ = ‖z‖ := O.norm_map z
  have hΔ0 : 0 ≤ Δ := by positivity
  have hx : ‖x - x'‖ ≤ Δ := by rw [hΔ]; linarith [norm_nonneg (y - y')]
  calc ‖(x - x') + (‖y - x‖ - ‖y' - x'‖) • O z + ‖y' - x'‖ • (O z - O' z)‖
      ≤ ‖x - x'‖ + |‖y - x‖ - ‖y' - x'‖| * ‖z‖ + ‖y' - x'‖ * ‖O z - O' z‖ := by
        refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add le_rfl
          (le_of_eq ?_))) (le_of_eq ?_))
        · rw [norm_smul, Real.norm_eq_abs, hOz]
        · rw [norm_smul, Real.norm_of_nonneg (norm_nonneg _)]
    _ ≤ Δ + Δ * 2 + 2 * (8 * (4 * Δ) * 2) := by
        gcongr
        · exact hrot.trans (by nlinarith [norm_nonneg z, norm_nonneg (‖y - x‖⁻¹ • (y - x) -
            ‖y' - x'‖⁻¹ • (y' - x'))])
    _ ≤ 200 * Δ := by nlinarith

end Similarity

/-! ## Polygons under similarities -/

section PolySim

variable {d : ℕ}

theorem edges_map (T : Rd d → Rd d) (z : List (Rd d)) :
    edges (z.map T) = (edges z).map (fun e => (T e.1, T e.2)) := by
  rw [edges, edges, ← List.map_tail, List.zip_map]
  rfl

theorem polyLen_map_simAffine (c : Rd d) {r : ℝ} (hr : 0 < r) (O : Rd d ≃ₗᵢ[ℝ] Rd d)
    (z : List (Rd d)) : polyLen (z.map (simAffine c r O)) = r * polyLen z := by
  rw [polyLen, polyLen, edges_map, List.map_map, ← List.sum_map_mul_left]
  congr 1
  refine List.map_congr_left fun e _ => ?_
  exact norm_simAffine_sub c hr O e.2 e.1

/-- A similarity maps segment measures to segment measures. -/
theorem segMeasure_map_simAffine (c : Rd d) (r : ℝ) (O : Rd d ≃ₗᵢ[ℝ] Rd d) (a b : Rd d) :
    segMeasure (simAffine c r O a) (simAffine c r O b) = (segMeasure a b).map (simAffine c r O) := by
  rw [segMeasure_eq, segMeasure_eq, Measure.map_map (measurable_simAffine c r O) (measurable_lin a b)]
  congr 1
  funext s
  simp only [Function.comp, lin, simAffine, map_add, map_sub, map_smul]
  module

theorem map_list_sum_measure {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {f : α → β}
    (hf : Measurable f) (l : List (Measure α)) : l.sum.map f = (l.map fun μ => μ.map f).sum := by
  induction l with
  | nil => simp
  | cons μ l ih => rw [List.sum_cons, Measure.map_add _ _ hf, ih, List.map_cons, List.sum_cons]

/-- **A similarity maps normalized arclength to normalized arclength.** -/
theorem polyMeasure_map_simAffine (c : Rd d) {r : ℝ} (hr : 0 < r) (O : Rd d ≃ₗᵢ[ℝ] Rd d)
    (z : List (Rd d)) :
    polyMeasure (z.map (simAffine c r O)) = (polyMeasure z).map (simAffine c r O) := by
  rw [polyMeasure, polyMeasure, edges_map, polyLen_map_simAffine c hr O, List.map_map,
    map_list_sum_measure (measurable_simAffine c r O), List.map_map]
  congr 1
  refine List.map_congr_left fun e _ => ?_
  simp only [Function.comp]
  rw [norm_simAffine_sub c hr O e.2 e.1, mul_div_mul_left _ _ hr.ne',
    segMeasure_map_simAffine c r O e.1 e.2, Measure.map_smul]
  exact (measurable_simAffine c r O).aemeasurable

/-- **A similarity maps good families to good families** (the similarity invariance of `G_K`
used in HA3 D5, Step 2a). -/
theorem goodFamily_map_simAffine (c : Rd d) {r : ℝ} (hr : 0 < r) (O : Rd d ≃ₗᵢ[ℝ] Rd d)
    {K : ℕ} {a : ℝ} {x y : Rd d} {z : List (Rd d)} (hz : z ∈ goodFamily K a x y) :
    z.map (simAffine c r O) ∈ goodFamily K a (simAffine c r O x) (simAffine c r O y) := by
  obtain ⟨hlen, hhead, hlast, hreg, hfwd, hpoly⟩ := hz
  have hyx : ‖simAffine c r O y - simAffine c r O x‖ = r * ‖y - x‖ := norm_simAffine_sub c hr O y x
  refine ⟨by rw [List.length_map, hlen], by rw [List.head?_map, hhead]; rfl,
    by rw [List.getLast?_map, hlast]; rfl, ?_, ?_, ?_⟩
  · intro e' he'
    rw [edges_map, ← List.map_dropLast] at he'
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 he'
    rw [norm_simAffine_sub c hr O e.2 e.1, hreg e he, hyx]
    ring
  · intro e' he'
    rw [edges_map] at he'
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 he'
    simp only
    rw [norm_simAffine_sub c hr O e.2 e.1, hyx, simAffine_sub, simAffine_sub,
      real_inner_smul_left, real_inner_smul_right, LinearIsometryEquiv.inner_map_map]
    have h := hfwd e he
    have hr2 : 0 ≤ r * r := by positivity
    nlinarith
  · rw [polyLen_map_simAffine c hr O, hyx]
    nlinarith [Real.exp_pos a]

/-- `simInv x y` is the similarity `simAffine (…) |y - x|⁻¹ rotE(…)⁻¹`. -/
theorem simInv_eq (x y : Rd d) : simInv x y = simAffine (-(‖y - x‖⁻¹ •
    (rotE (‖y - x‖⁻¹ • (y - x))).symm x)) ‖y - x‖⁻¹ (rotE (‖y - x‖⁻¹ • (y - x))).symm := rfl

theorem simInv_self (x y : Rd d) : simInv x y x = 0 := by
  simp only [simInv, simAffine]
  rw [neg_add_cancel]

/-- **Normal form of a good polygon** (HA3 D5, Step 2a): if `simOf x y` carries `e₁` to `y`, then
`Q₀ = simInv x y Q ∈ G_K(0, e₁)` and `Q = simOf x y Q₀`. -/
theorem goodFamily_simInv {K : ℕ} {a : ℝ} {x y : Rd d} {z : List (Rd d)}
    (hz : z ∈ goodFamily K a x y) (hxy : x ≠ y) (hy : simOf x y (e₁ d) = y) :
    z.map (simInv x y) ∈ goodFamily K a 0 (e₁ d) ∧ (z.map (simInv x y)).map (simOf x y) = z := by
  have hR : 0 < ‖y - x‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hxy))
  have h := goodFamily_map_simAffine (-(‖y - x‖⁻¹ • (rotE (‖y - x‖⁻¹ • (y - x))).symm x))
    (inv_pos.2 hR) (rotE (‖y - x‖⁻¹ • (y - x))).symm hz
  rw [← simInv_eq, simInv_self] at h
  have hy' : simInv x y y = e₁ d := by
    have h1 := simInv_simOf hxy (e₁ d)
    rwa [hy] at h1
  rw [hy'] at h
  refine ⟨h, ?_⟩
  rw [List.map_map]
  conv_rhs => rw [← List.map_id z]
  refine List.map_congr_left fun w _ => ?_
  exact simOf_simInv hxy w

end PolySim

end HigherDimLFPP.Upper
