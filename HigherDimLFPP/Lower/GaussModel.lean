import LQGDimension.Gaussian.Basic
import LQGDimension.Gaussian.MaxInequality
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

/-!
# Finite Gaussian fields with a prescribed covariance kernel (lower comparison, source §5.3)

Packet P-L2a, target T1 (ruling H6; audit HA4, "Details for later use" D7, "Finite model").
Kernel-agnostic port of `LQGDimension/LFPP/BlockConstructionAux3.lean`: the index type `Tri` and
the heat-kernel covariance `kap` of the 2D file are replaced by an arbitrary index type `ι` and an
arbitrary kernel `C : ι → ι → ℝ`.

For a family of vectors `β : ι → E` (`E` finite dimensional) and `x ∼ stdGaussian E`, the field
`Yf β x i = ⟪β i, x⟫` is a centered Gaussian field on `ι` with covariance `⟪β i, β j⟫`.

* `IsLoc F Φ`: the functional `Φ` reads only the coordinates in the finite set `F`.
* `gLawOn C F`: the canonical law on `ι → ℝ` of a centered Gaussian field with covariance `C`
  on `F` (and `0` off `F`).
* `transfer_integral`, `transfer_integrable`: if `β` realizes `C` on `F`, then for every
  measurable `F`-local `Φ`, `E Φ(Yf β x) = ∫ Φ d(gLawOn C F)`, and integrability transfers.
* `indepFun_orth`, `integral_mul_of_orth`: functionals of two mutually orthogonal groups of
  Gram vectors are independent.
* `integrable_of_le_exp`, `integral_exp_inner`: exponential moments.
* `gram_eq_sum_of_rel`: linear relations of the kernel hold exactly for the Gram vectors.
* Law-level consequences (statements about `gLawOn` only, for a kernel that is positive
  semidefinite on the ambient set): `integral_gLawOn_eq_of_subset` and
  `integrable_gLawOn_iff_of_subset` (the law of an `F`-local functional does not depend on the
  ambient finite set), `integral_gLawOn_comp` (invariance under index maps preserving the
  kernel), `integral_mul_gLawOn_of_orth` (independence of orthogonal groups),
  `integral_exp_gLawOn` (`E e^{c Y i} = e^{c² C(i,i)/2}`), and `ae_gLawOn_eq_sum` (linear
  relations of the kernel hold almost surely).

2D source: `LQGDimension/LFPP/BlockConstructionAux3.lean` (`Yf`, `IsLoc`, `extQ`, `extF`,
`gLaw`, `gLaw_eq_map`, `transfer_integral`, `transfer_integrable`, `cov_inner_stdGaussian`,
`indepFun_orth`, `integral_mul_of_orth`, `integrable_of_le_exp`, `integral_exp_inner`) and
`BlockConstructionAux2.lean` (`gram_eq_sum_of_kap`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace

namespace HigherDimLFPP.Lower

/-! ## Locality -/

section Loc

variable {ι : Type*}

/-- `Φ` only reads the coordinates in the finite set `F`. -/
def IsLoc {β : Sort*} (F : Finset ι) (Φ : (ι → ℝ) → β) : Prop :=
  ∀ Y Y' : ι → ℝ, (∀ i ∈ F, Y i = Y' i) → Φ Y = Φ Y'

theorem IsLoc.mono {β : Sort*} {F G : Finset ι} {Φ : (ι → ℝ) → β} (h : IsLoc F Φ)
    (hFG : F ⊆ G) : IsLoc G Φ := fun Y Y' hY => h Y Y' fun i hi => hY i (hFG hi)

theorem IsLoc.comp {β γ : Sort*} {F : Finset ι} {Φ : (ι → ℝ) → β} (h : IsLoc F Φ)
    (g : β → γ) : IsLoc F fun Y => g (Φ Y) := fun Y Y' hY => congrArg g (h Y Y' hY)

theorem isLoc_eval {F : Finset ι} {i : ι} (hi : i ∈ F) : IsLoc F fun Y : ι → ℝ => Y i :=
  fun _ _ hY => hY i hi

theorem isLoc_const {β : Sort*} (F : Finset ι) (b : β) : IsLoc F fun _ : ι → ℝ => b :=
  fun _ _ _ => rfl

theorem IsLoc.comp₂ {β γ δ : Sort*} {F : Finset ι} {Φ : (ι → ℝ) → β} {Ψ : (ι → ℝ) → γ}
    (hΦ : IsLoc F Φ) (hΨ : IsLoc F Ψ) (g : β → γ → δ) : IsLoc F fun Y => g (Φ Y) (Ψ Y) :=
  fun Y Y' hY => by
    show g (Φ Y) (Ψ Y) = g (Φ Y') (Ψ Y')
    rw [hΦ Y Y' hY, hΨ Y Y' hY]

end Loc

/-! ## Gram fields -/

section Gram

variable {ι : Type*} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Gaussian field of a family of vectors: `Y_x(i) = ⟪β i, x⟫`. -/
def Yf (β : ι → E) (x : E) : ι → ℝ := fun i => ⟪β i, x⟫

theorem Yf_apply (β : ι → E) (x : E) (i : ι) : Yf β x i = ⟪β i, x⟫ := rfl

theorem measurable_Yf [MeasurableSpace E] [OpensMeasurableSpace E] (β : ι → E) :
    Measurable (Yf β) :=
  Measurable.of_eval fun _ => (continuous_const.inner continuous_id).measurable

/-- **Linear relations of the kernel hold for its Gram vectors**: if `β` realizes `C` on `F`
and `C j i = Σ_k C j (is k)` for every `j ∈ F`, then `β i = Σ_k β (is k)`. -/
theorem gram_eq_sum_of_rel (F : Finset ι) (C : ι → ι → ℝ) (β : ι → E)
    (hβ : ∀ i ∈ F, ∀ j ∈ F, ⟪β i, β j⟫ = C i j) {κ : Type*} (s : Finset κ) (i : ι)
    (is : κ → ι) (hi : i ∈ F) (his : ∀ k ∈ s, is k ∈ F)
    (hrel : ∀ j ∈ F, C j i = ∑ k ∈ s, C j (is k)) : β i = ∑ k ∈ s, β (is k) := by
  obtain ⟨v, hv⟩ : ∃ v, v = β i - ∑ k ∈ s, β (is k) := ⟨_, rfl⟩
  have h0 : ∀ j ∈ F, ⟪β j, v⟫ = 0 := by
    intro j hj
    rw [hv, inner_sub_right, inner_sum, hβ j hj i hi, hrel j hj, sub_eq_zero]
    exact Finset.sum_congr rfl fun k hk => (hβ j hj _ (his k hk)).symm
  have hvv : ⟪v, v⟫ = 0 := by
    calc ⟪v, v⟫ = ⟪β i - ∑ k ∈ s, β (is k), v⟫ := by rw [← hv]
      _ = ⟪β i, v⟫ - ∑ k ∈ s, ⟪β (is k), v⟫ := by rw [inner_sub_left, sum_inner]
      _ = 0 := by
        rw [h0 i hi, Finset.sum_eq_zero fun k hk => h0 _ (his k hk), sub_zero]
  have hv0 : v = 0 := inner_self_eq_zero.1 hvv
  rw [hv, sub_eq_zero] at hv0
  exact hv0

/-- Two-term version of `gram_eq_sum_of_rel`. -/
theorem gram_eq_add_of_rel (F : Finset ι) (C : ι → ι → ℝ) (β : ι → E)
    (hβ : ∀ i ∈ F, ∀ j ∈ F, ⟪β i, β j⟫ = C i j) {i i₁ i₂ : ι} (hi : i ∈ F) (hi₁ : i₁ ∈ F)
    (hi₂ : i₂ ∈ F) (hrel : ∀ j ∈ F, C j i = C j i₁ + C j i₂) : β i = β i₁ + β i₂ := by
  have h := gram_eq_sum_of_rel F C β hβ (Finset.univ : Finset (Fin 2)) i ![i₁, i₂] hi
    (fun k _ => by fin_cases k <;> simpa) (fun j hj => by
      rw [hrel j hj, Fin.sum_univ_two]
      rfl)
  rw [h, Fin.sum_univ_two]
  rfl

end Gram

/-! ## The canonical law -/

section Law

variable {ι : Type*} [DecidableEq ι]

/-- Extension by zero of a vector indexed by `F` (Euclidean version). -/
def extQ (F : Finset ι) (y : EuclideanSpace ℝ F) : ι → ℝ :=
  fun i => if h : i ∈ F then y ⟨i, h⟩ else 0

theorem extQ_of_mem (F : Finset ι) (y : EuclideanSpace ℝ F) {i : ι} (hi : i ∈ F) :
    extQ F y i = y ⟨i, hi⟩ := by
  simp only [extQ, hi, dite_true]

theorem measurable_extQ (F : Finset ι) : Measurable (extQ F) := by
  refine Measurable.of_eval fun i => ?_
  by_cases h : i ∈ F
  · simp only [extQ, h, dite_true]
    exact (PiLp.continuous_apply 2 (fun _ : F => ℝ) ⟨i, h⟩).measurable
  · simp only [extQ, h, dite_false]
    exact measurable_const

/-- Extension by zero of a vector indexed by `F` (plain function version). -/
def extF (F : Finset ι) (y : F → ℝ) : ι → ℝ :=
  fun i => if h : i ∈ F then y ⟨i, h⟩ else 0

theorem extF_of_mem (F : Finset ι) (y : F → ℝ) {i : ι} (hi : i ∈ F) : extF F y i = y ⟨i, hi⟩ := by
  simp only [extF, hi, dite_true]

theorem measurable_extF (F : Finset ι) : Measurable (extF F) := by
  refine Measurable.of_eval fun i => ?_
  by_cases h : i ∈ F
  · simp only [extF, h, dite_true]
    exact measurable_pi_apply _
  · simp only [extF, h, dite_false]
    exact measurable_const

/-- An `F`-local functional factors through the restriction to `F`. -/
theorem IsLoc.eq_extF {β : Sort*} {F : Finset ι} {Φ : (ι → ℝ) → β} (h : IsLoc F Φ)
    (Y : ι → ℝ) : Φ Y = Φ (extF F fun i : F => Y i) :=
  h _ _ fun i hi => by rw [extF_of_mem F _ hi]

theorem IsLoc.union_left {β : Sort*} {F G : Finset ι} {Φ : (ι → ℝ) → β} (h : IsLoc F Φ) :
    IsLoc (F ∪ G) Φ := h.mono Finset.subset_union_left

theorem IsLoc.union_right {β : Sort*} {F G : Finset ι} {Φ : (ι → ℝ) → β} (h : IsLoc G Φ) :
    IsLoc (F ∪ G) Φ := h.mono Finset.subset_union_right

/-- The canonical centered Gaussian law on `ι → ℝ` with covariance `C` on the finite set `F`
(and `0` off `F`). -/
def gLawOn (C : ι → ι → ℝ) (F : Finset ι) : Measure (ι → ℝ) :=
  (multivariateGaussian 0 (Matrix.of fun i j : F => C i j)).map (extQ F)

instance isProbabilityMeasure_gLawOn (C : ι → ι → ℝ) (F : Finset ι) :
    IsProbabilityMeasure (gLawOn C F) := by
  unfold gLawOn
  infer_instance

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- `gLawOn C F` is the law of `Yf β` (extended by zero off `F`) for any Gram realization `β`
of `C` on `F`. -/
theorem gLawOn_eq_map (C : ι → ι → ℝ) (F : Finset ι) (β : ι → E)
    (hβ : ∀ i ∈ F, ∀ j ∈ F, ⟪β i, β j⟫ = C i j) :
    gLawOn C F = (stdGaussian E).map (extQ F ∘ LQGDimension.gramMap F β) := by
  rw [← Measure.map_map (measurable_extQ F) (LQGDimension.gramMap F β).continuous.measurable,
    LQGDimension.map_gramMap_stdGaussian]
  unfold gLawOn
  congr 2
  ext i j
  simp [hβ i i.2 j j.2]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem Yf_eq_extQ (F : Finset ι) (β : ι → E) (x : E) :
    ∀ i ∈ F, Yf β x i = extQ F (LQGDimension.gramMap F β x) i := by
  intro i hi
  rw [extQ_of_mem F _ hi, LQGDimension.gramMap_apply]
  rfl

/-- **Transfer of laws** from the Gram space to `gLawOn`. -/
theorem transfer_integral (C : ι → ι → ℝ) (F : Finset ι) (β : ι → E)
    (hβ : ∀ i ∈ F, ∀ j ∈ F, ⟪β i, β j⟫ = C i j) {Φ : (ι → ℝ) → ℝ} (hΦ : Measurable Φ)
    (hloc : IsLoc F Φ) : ∫ x, Φ (Yf β x) ∂stdGaussian E = ∫ Y, Φ Y ∂gLawOn C F := by
  rw [gLawOn_eq_map C F β hβ, integral_map ((measurable_extQ F).comp
    (LQGDimension.gramMap F β).continuous.measurable).aemeasurable hΦ.aestronglyMeasurable]
  congr 1
  funext x
  exact hloc _ _ (Yf_eq_extQ F β x)

/-- **Transfer of integrability** from the Gram space to `gLawOn`. -/
theorem transfer_integrable (C : ι → ι → ℝ) (F : Finset ι) (β : ι → E)
    (hβ : ∀ i ∈ F, ∀ j ∈ F, ⟪β i, β j⟫ = C i j) {Φ : (ι → ℝ) → ℝ} (hΦ : Measurable Φ)
    (hloc : IsLoc F Φ) :
    Integrable (fun x => Φ (Yf β x)) (stdGaussian E) ↔ Integrable Φ (gLawOn C F) := by
  rw [gLawOn_eq_map C F β hβ, integrable_map_measure hΦ.aestronglyMeasurable
    ((measurable_extQ F).comp (LQGDimension.gramMap F β).continuous.measurable).aemeasurable]
  have : (fun x => Φ (Yf β x)) = Φ ∘ (extQ F ∘ LQGDimension.gramMap F β) := by
    funext x
    exact hloc _ _ (Yf_eq_extQ F β x)
  rw [this]

/-- Transfer of probabilities of `F`-local events. -/
theorem transfer_measure (C : ι → ι → ℝ) (F : Finset ι) (β : ι → E)
    (hβ : ∀ i ∈ F, ∀ j ∈ F, ⟪β i, β j⟫ = C i j) {A : Set (ι → ℝ)} (hA : MeasurableSet A)
    (hloc : IsLoc F fun Y => Y ∈ A) :
    stdGaussian E {x | Yf β x ∈ A} = gLawOn C F A := by
  rw [gLawOn_eq_map C F β hβ, Measure.map_apply ((measurable_extQ F).comp
    (LQGDimension.gramMap F β).continuous.measurable) hA]
  congr 1
  ext x
  simp only [mem_ofPred_eq, mem_preimage, Function.comp_apply]
  exact iff_of_eq (hloc _ _ (Yf_eq_extQ F β x))

end Law

/-! ## Independence of orthogonal groups -/

section Indep

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem cov_inner_stdGaussian (u v : E) :
    cov[fun x => ⟪u, x⟫, fun x => ⟪v, x⟫; stdGaussian E] = ⟪u, v⟫ := by
  rw [← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id, covarianceBilin_stdGaussian,
    innerSL_apply_apply]

theorem indepFun_orth {ι κ : Type*} [Fintype ι] [Fintype κ] (v : ι → E) (w : κ → E)
    (h : ∀ i j, ⟪v i, w j⟫ = 0) :
    IndepFun (fun x i => ⟪v i, x⟫) (fun x j => ⟪w j, x⟫) (stdGaussian E) := by
  set L : E →L[ℝ] (ι → ℝ) × (κ → ℝ) :=
    (ContinuousLinearMap.pi fun i => innerSL ℝ (v i)).prod
      (ContinuousLinearMap.pi fun j => innerSL ℝ (w j)) with hL
  have hG : HasGaussianLaw (fun x => (fun i => ⟪v i, x⟫, fun j => ⟪w j, x⟫))
      (stdGaussian E) := by
    have := (IsGaussian.hasGaussianLaw_id (μ := stdGaussian E)).map_fun L
    exact this
  exact HasGaussianLaw.indepFun_of_covariance_eval (X := fun i x => ⟪v i, x⟫)
    (Y := fun j x => ⟪w j, x⟫) hG fun i j => by rw [cov_inner_stdGaussian, h]

variable {ι : Type*} [DecidableEq ι]

/-- **Independence**: functionals of two orthogonal groups of Gram vectors. -/
theorem integral_mul_of_orth (β : ι → E) (A B : Finset ι)
    (horth : ∀ i ∈ A, ∀ j ∈ B, ⟪β i, β j⟫ = 0) {Φ Ψ : (ι → ℝ) → ℝ} (hΦ : Measurable Φ)
    (hΨ : Measurable Ψ) (hΦl : IsLoc A Φ) (hΨl : IsLoc B Ψ) :
    ∫ x, Φ (Yf β x) * Ψ (Yf β x) ∂stdGaussian E =
      (∫ x, Φ (Yf β x) ∂stdGaussian E) * ∫ x, Ψ (Yf β x) ∂stdGaussian E := by
  have hind := indepFun_orth (fun i : A => β i) (fun j : B => β j)
    (fun i j => horth i i.2 j j.2)
  have hA : ∀ x, Φ (Yf β x) = (Φ ∘ extF A) (fun i : A => ⟪β i, x⟫) := fun x =>
    hΦl.eq_extF (Yf β x)
  have hB : ∀ x, Ψ (Yf β x) = (Ψ ∘ extF B) (fun j : B => ⟪β j, x⟫) := fun x =>
    hΨl.eq_extF (Yf β x)
  simp_rw [hA, hB]
  have hmA : Measurable fun x : E => fun i : A => ⟪β i, x⟫ :=
    Measurable.of_eval fun _ => (continuous_const.inner continuous_id).measurable
  have hmB : Measurable fun x : E => fun j : B => ⟪β j, x⟫ :=
    Measurable.of_eval fun _ => (continuous_const.inner continuous_id).measurable
  exact hind.integral_fun_comp_mul_comp hmA.aemeasurable hmB.aemeasurable
    (hΦ.comp (measurable_extF A)).aestronglyMeasurable
    (hΨ.comp (measurable_extF B)).aestronglyMeasurable

end Indep

/-! ## Integrability and exponential moments -/

section Moments

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

theorem integrable_of_le_exp {F : E → ℝ} (hF : AEStronglyMeasurable F (stdGaussian E))
    (c t : ℝ) (v : E) (hb : ∀ x, |F x| ≤ c * Real.exp (t * ⟪v, x⟫)) :
    Integrable F (stdGaussian E) :=
  Integrable.mono' ((LQGDimension.GaussianMax.integrable_exp_mul_inner v t).const_mul c) hF
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hb x)

theorem integral_exp_inner (v : E) (t : ℝ) :
    ∫ x, Real.exp (t * ⟪v, x⟫) ∂stdGaussian E = Real.exp (‖v‖ ^ 2 * t ^ 2 / 2) :=
  LQGDimension.GaussianMax.integral_exp_mul_inner v t

end Moments

/-! ## Law-level consequences -/

section LawLevel

variable {ι : Type*} [DecidableEq ι] (C : ι → ι → ℝ)

/-- **The law of an `F`-local functional does not depend on the ambient finite set**. -/
theorem integral_gLawOn_eq_of_subset {F G : Finset ι} (hFG : F ⊆ G)
    (hG : LQGDimension.PSDOn G C) {Φ : (ι → ℝ) → ℝ} (hΦ : Measurable Φ) (hloc : IsLoc F Φ) :
    ∫ Y, Φ Y ∂gLawOn C F = ∫ Y, Φ Y ∂gLawOn C G := by
  obtain ⟨β, hβ⟩ := LQGDimension.exists_gram_of_psdOn G C hG
  rw [← transfer_integral C F β (fun i hi j hj => hβ i (hFG hi) j (hFG hj)) hΦ hloc,
    ← transfer_integral C G β hβ hΦ (hloc.mono hFG)]

theorem integrable_gLawOn_iff_of_subset {F G : Finset ι} (hFG : F ⊆ G)
    (hG : LQGDimension.PSDOn G C) {Φ : (ι → ℝ) → ℝ} (hΦ : Measurable Φ) (hloc : IsLoc F Φ) :
    Integrable Φ (gLawOn C F) ↔ Integrable Φ (gLawOn C G) := by
  obtain ⟨β, hβ⟩ := LQGDimension.exists_gram_of_psdOn G C hG
  rw [← transfer_integrable C F β (fun i hi j hj => hβ i (hFG hi) j (hFG hj)) hΦ hloc,
    ← transfer_integrable C G β hβ hΦ (hloc.mono hFG)]

theorem measure_gLawOn_eq_of_subset {F G : Finset ι} (hFG : F ⊆ G)
    (hG : LQGDimension.PSDOn G C) {A : Set (ι → ℝ)} (hA : MeasurableSet A)
    (hloc : IsLoc F fun Y => Y ∈ A) : gLawOn C F A = gLawOn C G A := by
  obtain ⟨β, hβ⟩ := LQGDimension.exists_gram_of_psdOn G C hG
  rw [← transfer_measure C F β (fun i hi j hj => hβ i (hFG hi) j (hFG hj)) hA hloc,
    ← transfer_measure C G β hβ hA (hloc.mono hFG)]

/-- **Invariance in law under index maps preserving the kernel**: if `τ` maps `F` into `G` and
`C (τ i) (τ j) = C i j` on `F`, then `Y ∘ τ` under `gLawOn C G` has the law `gLawOn C F` on
`F`-local functionals. -/
theorem integral_gLawOn_comp {F G : Finset ι} (τ : ι → ι) (hτ : ∀ i ∈ F, τ i ∈ G)
    (hC : ∀ i ∈ F, ∀ j ∈ F, C (τ i) (τ j) = C i j) (hG : LQGDimension.PSDOn G C)
    {Φ : (ι → ℝ) → ℝ} (hΦ : Measurable Φ) (hloc : IsLoc F Φ) :
    ∫ Y, Φ (fun i => Y (τ i)) ∂gLawOn C G = ∫ Y, Φ Y ∂gLawOn C F := by
  obtain ⟨β, hβ⟩ := LQGDimension.exists_gram_of_psdOn G C hG
  have hβτ : ∀ i ∈ F, ∀ j ∈ F, ⟪β (τ i), β (τ j)⟫ = C i j := fun i hi j hj => by
    rw [hβ _ (hτ i hi) _ (hτ j hj), hC i hi j hj]
  have hmτ : Measurable fun Y : ι → ℝ => fun i => Y (τ i) :=
    Measurable.of_eval fun i => measurable_pi_apply (τ i)
  have hlocG : IsLoc G fun Y : ι → ℝ => Φ fun i => Y (τ i) :=
    fun Y Y' hY => hloc _ _ fun i hi => hY _ (hτ i hi)
  rw [← transfer_integral C F (fun i => β (τ i)) hβτ hΦ hloc,
    ← transfer_integral (Φ := fun Y => Φ fun i => Y (τ i)) C G β hβ (hΦ.comp hmτ) hlocG]
  rfl

/-- **Independence** at the level of laws: functionals of two groups of coordinates with
vanishing cross-covariance are independent. -/
theorem integral_mul_gLawOn_of_orth {F A B : Finset ι} (hA : A ⊆ F) (hB : B ⊆ F)
    (hF : LQGDimension.PSDOn F C) (horth : ∀ i ∈ A, ∀ j ∈ B, C i j = 0)
    {Φ Ψ : (ι → ℝ) → ℝ} (hΦ : Measurable Φ) (hΨ : Measurable Ψ) (hΦl : IsLoc A Φ)
    (hΨl : IsLoc B Ψ) :
    ∫ Y, Φ Y * Ψ Y ∂gLawOn C F = (∫ Y, Φ Y ∂gLawOn C F) * ∫ Y, Ψ Y ∂gLawOn C F := by
  obtain ⟨β, hβ⟩ := LQGDimension.exists_gram_of_psdOn F C hF
  have hΦF := hΦl.mono hA
  have hΨF := hΨl.mono hB
  rw [← transfer_integral (Φ := fun Y => Φ Y * Ψ Y) C F β hβ (hΦ.mul hΨ)
      (hΦF.comp₂ hΨF fun a b => a * b),
    ← transfer_integral C F β hβ hΦ hΦF, ← transfer_integral C F β hβ hΨ hΨF]
  exact integral_mul_of_orth β A B (fun i hi j hj => by rw [hβ i (hA hi) j (hB hj),
    horth i hi j hj]) hΦ hΨ hΦl hΨl

/-- **Exponential moments**: `E e^{c Y i} = e^{c² C(i,i)/2}`. -/
theorem integral_exp_gLawOn {F : Finset ι} (hF : LQGDimension.PSDOn F C) {i : ι} (hi : i ∈ F)
    (c : ℝ) : ∫ Y, Real.exp (c * Y i) ∂gLawOn C F = Real.exp (c ^ 2 * C i i / 2) := by
  obtain ⟨β, hβ⟩ := LQGDimension.exists_gram_of_psdOn F C hF
  rw [← transfer_integral C F β hβ ((measurable_pi_apply i).const_mul c).exp
    ((isLoc_eval hi).comp fun y => Real.exp (c * y))]
  simp only [Yf_apply]
  rw [integral_exp_inner, ← real_inner_self_eq_norm_sq, hβ i hi i hi]
  ring_nf

theorem integrable_exp_gLawOn {F : Finset ι} (hF : LQGDimension.PSDOn F C) {i : ι} (hi : i ∈ F)
    (c : ℝ) : Integrable (fun Y : ι → ℝ => Real.exp (c * Y i)) (gLawOn C F) := by
  obtain ⟨β, hβ⟩ := LQGDimension.exists_gram_of_psdOn F C hF
  rw [← transfer_integrable C F β hβ ((measurable_pi_apply i).const_mul c).exp
    ((isLoc_eval hi).comp fun y => Real.exp (c * y))]
  exact LQGDimension.GaussianMax.integrable_exp_mul_inner (β i) c

/-- **Linear relations hold almost surely**: if `C j i = Σ_k C j (is k)` for all `j ∈ F`, then
`Y i = Σ_k Y (is k)` almost surely under `gLawOn C F`. -/
theorem ae_gLawOn_eq_sum {F : Finset ι} (hF : LQGDimension.PSDOn F C) {κ : Type*}
    (s : Finset κ) (i : ι) (is : κ → ι) (hi : i ∈ F) (his : ∀ k ∈ s, is k ∈ F)
    (hrel : ∀ j ∈ F, C j i = ∑ k ∈ s, C j (is k)) :
    ∀ᵐ Y ∂gLawOn C F, Y i = ∑ k ∈ s, Y (is k) := by
  obtain ⟨β, hβ⟩ := LQGDimension.exists_gram_of_psdOn F C hF
  have hrelβ := gram_eq_sum_of_rel F C β hβ s i is hi his hrel
  rw [gLawOn_eq_map C F β hβ]
  have hm : Measurable (extQ F ∘ LQGDimension.gramMap F β) :=
    (measurable_extQ F).comp (LQGDimension.gramMap F β).continuous.measurable
  have hset : MeasurableSet {Y : ι → ℝ | Y i = ∑ k ∈ s, Y (is k)} :=
    measurableSet_eq_fun (measurable_pi_apply i)
      (Finset.measurable_sum _ fun k _ => measurable_pi_apply (is k))
  rw [ae_map_iff hm.aemeasurable hset]
  refine ae_of_all _ fun x => ?_
  simp only [Function.comp_apply]
  rw [← Yf_eq_extQ F β x i hi, Yf_apply, hrelβ, sum_inner]
  exact Finset.sum_congr rfl fun k hk => (Yf_eq_extQ F β x _ (his k hk))

end LawLevel

end HigherDimLFPP.Lower
