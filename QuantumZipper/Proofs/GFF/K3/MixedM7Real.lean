import QuantumZipper.Proofs.GFF.K3.MixedM7Joint
import QuantumZipper.Proofs.GFF.K3.DualExistence

/-!
# K3-mixed M7-c, step 3: Gaussian realization of the joint Hilbert data

One isonormal process (`gs_process_hilbert`) on the joint space `WithLp 2 (GradSpace D × HkE)`
(`MixedM7Joint.lean`), indexed by `CIdx = MixIdx ⊕ AdmT ⊕ XiIdx`, realizes simultaneously

* the mixed field `realY` (vectors `jointMixed μ`, `μ` `V`-admissible): `IsMixedGFF`;
* the free field `realX` (vectors `jointFree (v̂_μ)`, `μ` admissible): `IsFreeGFFModConstH`;
* the variables `Ξ u` (vectors `(u, 0)`, `u` orthogonal to the mixed local generators).

For any process `Z` with the isonormal laws this file proves: `realY_isMixedGFF`,
`realX_isFree` (following `exists_dualGFF` and `exists_freeGFF`), `real_indep` (the `Ξ`-coordinates
are independent of `freeIncrSigma X`, via `IsGaussianProcess.indepFun_of_covariance_eq_zero` and
`inner_xi_jointFree`), and `real_local` (the a.s. local identity
`Y μ − (X μ − X ρ) = Ξ(v_{bal μ}) − (X(bal μ) − X ρ)`, a zero-variance combination by
`jointMixed_sub_jointFree_local`). Own construction.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped RealInnerProductSpace

namespace QuantumZipper.K3

open GFFExist LQGDimension.ExistAsm

variable {D : Set ℂ} {c d t r r' : ℝ}

/-- `V`-admissible measures for the mixed space. -/
abbrev MixIdx (D : Set ℂ) (c d : ℝ) :=
  {μ : Measure ℂ // IsAdmissibleDual D (mixedSpace D (realSet (Set.Icc c d))) μ}

/-- Vectors of `GradSpace D` orthogonal to the mixed local generators. -/
abbrev XiIdx (D : Set ℂ) (c d t r r' : ℝ) :=
  {u : GradSpace D // ∀ ν : LocIdx t r', ⟪u, mixedLocVec D c d t r ν.1⟫ = 0}

/-- The index type of the joint process. -/
abbrev CIdx (D : Set ℂ) (c d t r r' : ℝ) := MixIdx D c d ⊕ AdmT ⊕ XiIdx D c d t r r'

/-- The vectors of the joint process. -/
def cVec (hr : 0 < r) (hr'r : r' < r) (J : freeLocSpace (t := t) hr hr'r →ₗᵢ[ℝ] GradSpace D) :
    CIdx D c d t r r' → WithLp 2 (GradSpace D × HkE) :=
  Sum.elim (fun μ => jointMixed D c d μ.1)
    (Sum.elim (fun μ => jointFree hr hr'r J (freeVec μ)) fun u => WithLp.toLp 2 (u.1, 0))

instance instSeparableJoint (D : Set ℂ) :
    TopologicalSpace.SeparableSpace (WithLp 2 (GradSpace D × HkE)) :=
  (WithLp.homeomorphProd 2 (GradSpace D) HkE).symm.isQuotientMap.separableSpace

/-- `jointFree` is linear. -/
theorem jointFree_add_smul {hr : 0 < r} {hr'r : r' < r}
    (J : freeLocSpace (t := t) hr hr'r →ₗᵢ[ℝ] GradSpace D) (a b : ℝ) (x y : HkE) :
    jointFree hr hr'r J (a • x + b • y) =
      a • jointFree hr hr'r J x + b • jointFree hr hr'r J y := by
  simp only [jointFree, map_add, map_smul]
  rw [← WithLp.toLp_smul, ← WithLp.toLp_smul, ← WithLp.toLp_add, Prod.smul_mk, Prod.smul_mk,
    Prod.mk_add_mk]
  refine congrArg (WithLp.toLp 2) (Prod.ext rfl ?_)
  simp only [smul_sub]
  abel

/-- A balanced pair of admissible measures carried outside `ball t r` has free vector difference
orthogonal to the free local part. -/
theorem freeVec_sub_mem_orthogonal (hr : 0 < r) (hr'r : r' < r) {ρ ρ' : Measure ℂ}
    (hρ : IsAdmissibleH ρ) (hρ' : IsAdmissibleH ρ') (hm : ρ Set.univ = ρ' Set.univ)
    (hρB : ρ (ball (t : ℂ) r) = 0) (hρ'B : ρ' (ball (t : ℂ) r) = 0) :
    freeVec ⟨ρ, hρ⟩ - freeVec ⟨ρ', hρ'⟩ ∈ (freeLocSpace (t := t) hr hr'r)ᗮ := by
  rw [Submodule.mem_orthogonal']
  intro u hu
  exact inner_eq_zero_of_mem_closure_span_of_forall (fun ν =>
    inner_freeVec_sub_freeLocVec_eq_zero hr hr'r hρ hρ' hm hρB hρ'B ν) hu

/-- On the orthogonal complement of the free local part, `jointFree x = (0, x)`. -/
theorem jointFree_of_mem_orthogonal {hr : 0 < r} {hr'r : r' < r}
    (J : freeLocSpace (t := t) hr hr'r →ₗᵢ[ℝ] GradSpace D) {x : HkE}
    (hx : x ∈ (freeLocSpace (t := t) hr hr'r)ᗮ) :
    jointFree hr hr'r J x = WithLp.toLp 2 ((0 : GradSpace D), x) := by
  have h0 := Submodule.orthogonalProjectionOnto_eq_zero_iff.2 hx
  simp only [jointFree, Submodule.starProjection_apply, h0, map_zero, Submodule.coe_zero, sub_zero]

section Real

variable {hr : 0 < r} {hr'r : r' < r} {J : freeLocSpace (t := t) hr hr'r →ₗᵢ[ℝ] GradSpace D}
  {Z : CIdx D c d t r r' → (ℕ → ℝ) → ℝ}

open Classical in
/-- The realized mixed field. -/
def realY (Z : CIdx D c d t r r' → (ℕ → ℝ) → ℝ) : (ℕ → ℝ) → FieldSample := fun ω μ =>
  if h : IsAdmissibleDual D (mixedSpace D (realSet (Set.Icc c d))) μ then Z (Sum.inl ⟨μ, h⟩) ω
  else 0

open Classical in
/-- The realized free field. -/
def realX (Z : CIdx D c d t r r' → (ℕ → ℝ) → ℝ) : (ℕ → ℝ) → FieldSample := fun ω μ =>
  if h : IsAdmissibleH μ then Z (Sum.inr (Sum.inl ⟨μ, h⟩)) ω else 0

theorem realY_eq (μ : Measure ℂ)
    (h : IsAdmissibleDual D (mixedSpace D (realSet (Set.Icc c d))) μ) :
    (fun ω => realY Z ω μ) = Z (Sum.inl ⟨μ, h⟩) := by
  funext ω; simp [realY, h]

theorem realX_apply (μ : Measure ℂ) (h : IsAdmissibleH μ) (ω : ℕ → ℝ) :
    realX Z ω μ = Z (Sum.inr (Sum.inl ⟨μ, h⟩)) ω := by
  simp [realX, h]

theorem realX_eq (μ : Measure ℂ) (h : IsAdmissibleH μ) :
    (fun ω => realX Z ω μ) = Z (Sum.inr (Sum.inl ⟨μ, h⟩)) := by
  funext ω; simp [realX, h]

variable (hZm : ∀ i, Measurable (Z i))
  (hZ : ∀ {ι : Type} [Fintype ι] (τ : ι → CIdx D c d t r r') (a : ι → ℝ),
    HasLaw (fun ω => ∑ i, a i * Z (τ i) ω)
      (gaussianReal 0 (‖∑ i, a i • cVec hr hr'r J (τ i)‖ ^ 2).toNNReal) stdP)
include hZm hZ

theorem real_isGaussianProcess : IsGaussianProcess Z stdP :=
  gs_isGaussianProcess (fun i => (hZm i).aemeasurable)
    fun I a => ⟨_, hZ (fun i : I => (i : CIdx D c d t r r')) a⟩

omit hZm in
theorem real_hasLaw_single (i : CIdx D c d t r r') :
    HasLaw (Z i) (gaussianReal 0 (‖cVec hr hr'r J i‖ ^ 2).toNNReal) stdP :=
  gs_comb4 hZ ![i, i, i, i] ![1, 0, 0, 0] _ (fun ω => by simp [Fin.sum_univ_four]) _
    (by simp [Fin.sum_univ_four])

omit hZm in
theorem real_cov (i j : CIdx D c d t r r') :
    cov[Z i, Z j; stdP] = ⟪cVec hr hr'r J i, cVec hr hr'r J j⟫ :=
  gs_cov_eq (real_hasLaw_single hZ i) (real_hasLaw_single hZ j)
    (gs_comb4 hZ ![i, j, i, i] ![1, 1, 0, 0] _ (fun ω => by simp [Fin.sum_univ_four]) _
      (by simp [Fin.sum_univ_four]))

/-- The realized mixed field is a mixed GFF. -/
theorem realY_isMixedGFF : IsMixedGFF D (realSet (Set.Icc c d)) (realY Z) stdP := by
  refine ⟨fun μ => ?_, ?_, fun μ hμ => ?_, fun μ ν hμ hν => ?_⟩
  · by_cases h : IsAdmissibleDual D (mixedSpace D (realSet (Set.Icc c d))) μ
    · rw [realY_eq μ h]; exact hZm _
    · have : (fun ω => realY Z ω μ) = fun _ => 0 := by funext ω; simp [realY, h]
      rw [this]; exact measurable_const
  · have e : (fun (μ : MixIdx D c d) ω => realY Z ω μ.1) = fun μ => Z (Sum.inl μ) := by
      funext μ ω; exact congrFun (realY_eq μ.1 μ.2) ω
    rw [e]
    exact (real_isGaussianProcess hZm hZ).comp_right Sum.inl
  · rw [realY_eq μ hμ]
    exact gs_integral_eq_zero (real_hasLaw_single hZ _)
  · rw [realY_eq μ hμ, realY_eq ν hν, real_cov hZ,
      dualCov_eq_inner_rieszVec (isDNSpace_mixedSpace D _) hμ hν]
    exact inner_jointMixed D c d μ ν

/-- The realized free field is a free GFF modulo constants. -/
theorem realX_isFree : IsFreeGFFModConstH (realX Z) stdP := by
  set W : AdmT → (ℕ → ℝ) → ℝ := fun μ => Z (Sum.inr (Sum.inl μ)) with hW
  have hdiff : ∀ (μ ν : Measure ℂ) (hμ : IsAdmissibleH μ) (hν : IsAdmissibleH ν),
      (fun ω => realX Z ω μ - realX Z ω ν) = fun ω => W ⟨μ, hμ⟩ ω - W ⟨ν, hν⟩ ω := by
    intro μ ν hμ hν; funext ω
    rw [realX_apply (Z := Z) μ hμ ω, realX_apply (Z := Z) ν hν ω]
  have hlaw2 : ∀ μ ν : AdmT, HasLaw (fun ω => W μ ω - W ν ω)
      (gaussianReal 0 (‖jointFree hr hr'r J (freeVec μ) - jointFree hr hr'r J (freeVec ν)‖ ^ 2).toNNReal)
      stdP := fun μ ν =>
    gs_comb4 hZ ![Sum.inr (Sum.inl μ), Sum.inr (Sum.inl ν), Sum.inr (Sum.inl μ),
      Sum.inr (Sum.inl μ)] ![1, -1, 0, 0] _ (fun ω => by simp [hW, Fin.sum_univ_four]; ring) _
      (by simp [Fin.sum_univ_four, cVec, sub_eq_add_neg])
  refine ⟨fun μ => ?_, ?_, fun μ ν hμ hν _ => ?_, fun p q hp1 hp2 hp hq1 hq2 hq => ?_,
    fun μ ν hμ hν a b => ?_⟩
  · by_cases h : IsAdmissibleH μ
    · rw [realX_eq μ h]; exact hZm _
    · have : (fun ω => realX Z ω μ) = fun _ => 0 := by funext ω; simp [realX, h]
      rw [this]; exact measurable_const
  · refine gs_isGaussianProcess (fun p => ?_) fun I a => ?_
    · rw [hdiff _ _ p.2.1 p.2.2.1]
      exact ((hZm _).sub (hZm _)).aemeasurable
    · set τ : I ⊕ I → CIdx D c d t r r' := Sum.elim
        (fun i => Sum.inr (Sum.inl ⟨i.1.1.1, i.1.2.1⟩))
        (fun i => Sum.inr (Sum.inl ⟨i.1.1.2, i.1.2.2.1⟩)) with hτ
      set a' : I ⊕ I → ℝ := Sum.elim a (fun i => -a i) with ha'
      have e : (fun ω => ∑ i : I, a i * (realX Z ω i.1.1.1 - realX Z ω i.1.1.2)) =
          fun ω => ∑ j, a' j * Z (τ j) ω := by
        funext ω
        rw [Fintype.sum_sum_type, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [hτ, ha', Sum.elim_inl, Sum.elim_inr]
        rw [realX_apply (Z := Z) _ i.1.2.1 ω, realX_apply (Z := Z) _ i.1.2.2.1 ω]
        ring
      exact ⟨_, e ▸ hZ τ a'⟩
  · rw [hdiff μ ν hμ hν]
    exact gs_integral_eq_zero (hlaw2 ⟨μ, hμ⟩ ⟨ν, hν⟩)
  · rw [hdiff _ _ hp1 hp2, hdiff _ _ hq1 hq2]
    have hinner := freeVec_inner ⟨p.1, hp1⟩ ⟨p.2, hp2⟩ ⟨q.1, hq1⟩ ⟨q.2, hq2⟩ hp hq
    simp only [Prod.mk.eta] at hinner
    rw [← hinner, ← inner_jointFree hr hr'r J, ← jointFree_sub, ← jointFree_sub]
    refine gs_cov_eq (hlaw2 _ _) (hlaw2 _ _) ?_
    exact gs_comb4 hZ ![Sum.inr (Sum.inl ⟨p.1, hp1⟩), Sum.inr (Sum.inl ⟨p.2, hp2⟩),
      Sum.inr (Sum.inl ⟨q.1, hq1⟩), Sum.inr (Sum.inl ⟨q.2, hq2⟩)] ![1, -1, 1, -1] _
      (fun ω => by simp [hW, Fin.sum_univ_four]; ring) _
      (by simp [Fin.sum_univ_four, cVec]; abel)
  · have hw := gffEx_admissible_comb hμ hν a b
    have hvec : jointFree hr hr'r J (freeVec ⟨_, hw⟩) =
        (a : ℝ) • jointFree hr hr'r J (freeVec ⟨μ, hμ⟩) +
          (b : ℝ) • jointFree hr hr'r J (freeVec ⟨ν, hν⟩) := by
      rw [freeVec_comb ⟨μ, hμ⟩ ⟨ν, hν⟩ a b ⟨_, hw⟩ rfl, jointFree_add_smul]
    have hlaw := gs_comb4 hZ ![Sum.inr (Sum.inl ⟨_, hw⟩), Sum.inr (Sum.inl ⟨μ, hμ⟩),
      Sum.inr (Sum.inl ⟨ν, hν⟩), Sum.inr (Sum.inl ⟨μ, hμ⟩)] ![1, -(a : ℝ), -(b : ℝ), 0]
      (fun ω => W ⟨_, hw⟩ ω - ((a : ℝ) * W ⟨μ, hμ⟩ ω + (b : ℝ) * W ⟨ν, hν⟩ ω))
      (fun ω => by simp [hW, Fin.sum_univ_four]; ring) (0 : WithLp 2 (GradSpace D × HkE))
      (by
        simp only [Fin.sum_univ_four, cVec]
        simp [hvec]
        try module)
    have h0 : (‖(0 : WithLp 2 (GradSpace D × HkE))‖ ^ 2).toNNReal = 0 := by simp
    have hae : ∀ᵐ ω ∂stdP,
        W ⟨_, hw⟩ ω - ((a : ℝ) * W ⟨μ, hμ⟩ ω + (b : ℝ) * W ⟨ν, hν⟩ ω) = 0 := by
      refine ae_of_ae_map (p := fun y : ℝ => y = 0) hlaw.aemeasurable ?_
      rw [hlaw.map_eq, h0, gaussianReal_zero_var, ae_dirac_eq]
      exact Filter.eventually_pure.2 rfl
    filter_upwards [hae] with ω hω
    rw [realX_apply (Z := Z) _ hw ω, realX_apply (Z := Z) μ hμ ω,
      realX_apply (Z := Z) ν hν ω]
    simp only [hW] at hω
    linarith

/-- **Independence** of the `Ξ`-coordinates from the realized free field. -/
theorem real_indep
    (hJ2 : ∀ k, J k ∈ (Submodule.span ℝ (Set.range fun μ : LocIdx t r' =>
        mixedLocVec D c d t r μ.1)).topologicalClosure) :
    Indep (MeasurableSpace.comap (fun ω (u : XiIdx D c d t r r') => Z (Sum.inr (Sum.inr u)) ω)
      inferInstance) (freeIncrSigma (realX Z)) stdP := by
  have hXf := realX_isFree hZm hZ
  set Xi : XiIdx D c d t r r' → (ℕ → ℝ) → ℝ := fun u => Z (Sum.inr (Sum.inr u)) with hXi
  set Of : BalIdx → (ℕ → ℝ) → ℝ := fun p ω => realX Z ω p.1.1 - realX Z ω p.1.2 with hOf
  have hOfZ : ∀ p : BalIdx, Of p = fun ω => Z (Sum.inr (Sum.inl ⟨p.1.1, p.2.1⟩)) ω -
      Z (Sum.inr (Sum.inl ⟨p.1.2, p.2.2.1⟩)) ω := fun p => by
    funext ω; simp only [hOf, realX_apply (Z := Z) _ p.2.1 ω, realX_apply (Z := Z) _ p.2.2.1 ω]
  let fst : XiIdx D c d t r r' ⊕ BalIdx → CIdx D c d t r r' :=
    Sum.elim (fun u => Sum.inr (Sum.inr u)) fun p => Sum.inr (Sum.inl ⟨p.1.1, p.2.1⟩)
  let snd : XiIdx D c d t r r' ⊕ BalIdx → CIdx D c d t r r' :=
    Sum.elim (fun u => Sum.inr (Sum.inr u)) fun p => Sum.inr (Sum.inl ⟨p.1.2, p.2.2.1⟩)
  let sgn : XiIdx D c d t r r' ⊕ BalIdx → ℝ := Sum.elim (fun _ => 0) fun _ => -1
  have hW : ∀ k ω, Sum.elim Xi Of k ω = Z (fst k) ω + sgn k * Z (snd k) ω := by
    rintro (u | p) ω
    · simp [hXi, fst, sgn]
    · simp only [Sum.elim_inr, hOfZ p, fst, snd, sgn]; ring
  have hG : IsGaussianProcess (Sum.elim Xi Of) stdP := by
    refine gs_isGaussianProcess (fun k => ?_) fun I a => ?_
    · rcases k with u | p
      · exact (hZm _).aemeasurable
      · rw [Sum.elim_inr, hOfZ p]; exact ((hZm _).sub (hZm _)).aemeasurable
    · set τ : I ⊕ I → CIdx D c d t r r' := Sum.elim (fun i => fst i.1) fun i => snd i.1 with hτ
      set a' : I ⊕ I → ℝ := Sum.elim a fun i => a i * sgn i.1 with ha'
      have e : (fun ω => ∑ i : I, a i * Sum.elim Xi Of i.1 ω) =
          fun ω => ∑ j, a' j * Z (τ j) ω := by
        funext ω
        rw [Fintype.sum_sum_type, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [hτ, ha', Sum.elim_inl, Sum.elim_inr, hW]
        ring
      exact ⟨_, e ▸ hZ τ a'⟩
  have hcov : ∀ u p, cov[Xi u, Of p; stdP] = 0 := by
    intro u p
    rw [hOfZ p]
    have hu : ∀ k, ⟪u.1, J k⟫ = 0 := fun k =>
      inner_eq_zero_of_mem_closure_span_mixedLocVec u.2 (hJ2 k)
    have h1 := real_hasLaw_single hZ (Sum.inr (Sum.inr u))
    have h2 := gs_comb4 hZ ![Sum.inr (Sum.inl ⟨p.1.1, p.2.1⟩), Sum.inr (Sum.inl ⟨p.1.2, p.2.2.1⟩),
      Sum.inr (Sum.inr u), Sum.inr (Sum.inr u)] ![1, -1, 0, 0]
      (fun ω => Z (Sum.inr (Sum.inl ⟨p.1.1, p.2.1⟩)) ω - Z (Sum.inr (Sum.inl ⟨p.1.2, p.2.2.1⟩)) ω)
      (fun ω => by simp [Fin.sum_univ_four]; ring)
      (cVec hr hr'r J (Sum.inr (Sum.inl ⟨p.1.1, p.2.1⟩)) -
        cVec hr hr'r J (Sum.inr (Sum.inl ⟨p.1.2, p.2.2.1⟩)))
      (by simp [Fin.sum_univ_four, sub_eq_add_neg] <;> rfl)
    have h3 := gs_comb4 hZ ![Sum.inr (Sum.inr u), Sum.inr (Sum.inl ⟨p.1.1, p.2.1⟩),
      Sum.inr (Sum.inl ⟨p.1.2, p.2.2.1⟩), Sum.inr (Sum.inr u)] ![1, 1, -1, 0]
      (fun ω => Xi u ω + (Z (Sum.inr (Sum.inl ⟨p.1.1, p.2.1⟩)) ω -
        Z (Sum.inr (Sum.inl ⟨p.1.2, p.2.2.1⟩)) ω))
      (fun ω => by simp [hXi, Fin.sum_univ_four]; ring)
      (cVec hr hr'r J (Sum.inr (Sum.inr u)) + (cVec hr hr'r J (Sum.inr (Sum.inl ⟨p.1.1, p.2.1⟩)) -
        cVec hr hr'r J (Sum.inr (Sum.inl ⟨p.1.2, p.2.2.1⟩))))
      (by simp [Fin.sum_univ_four, sub_eq_add_neg, add_assoc] <;> rfl)
    rw [gs_cov_eq h1 h2 h3]
    simp only [cVec, Sum.elim_inr, Sum.elim_inl]
    rw [jointFree_sub]
    exact inner_xi_jointFree hr hr'r J hu _
  have hind := hG.indepFun_of_covariance_eq_zero (fun u => (hZm _).aemeasurable)
    (fun p => by rw [hOfZ p]; exact ((hZm _).sub (hZm _)).aemeasurable) hcov
  exact hind

omit hZm in
/-- **Local coupling identity** (random form): for local `μ`, an admissible `ρ` of the same mass
giving no mass to `ball t r`, and `u = v_{bal μ}` (orthogonal to the mixed local part),
a.s. `Y μ − (X μ − X ρ) = Ξ u − (X (bal μ) − X ρ)`. -/
theorem real_local
    (hJ : ∀ μ : LocIdx t r', J ⟨freeLocVec hr hr'r μ,
        Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨μ, rfl⟩)⟩ =
          mixedLocVec D c d t r μ.1)
    (μ : LocIdx t r') (hμA : IsAdmissibleDual D (mixedSpace D (realSet (Set.Icc c d))) μ.1)
    {ρ : Measure ℂ} (hρ : IsAdmissibleH ρ) (hρB : ρ (ball (t : ℂ) r) = 0)
    (hm : μ.1 Set.univ = ρ Set.univ) (u : XiIdx D c d t r r')
    (hu : u.1 = rieszVec D (mixedSpace D (realSet (Set.Icc c d))) (bal t r μ.1)) :
    ∀ᵐ ω ∂stdP, realY Z ω μ.1 - (realX Z ω μ.1 - realX Z ω ρ) =
      Z (Sum.inr (Sum.inr u)) ω - (realX Z ω (bal t r μ.1) - realX Z ω ρ) := by
  have hb := μ.bal_adm hr hr'r
  have hbal : bal t r μ.1 Set.univ = ρ Set.univ := by rw [bal_univ hr hr'r μ.2.2]; exact hm
  set τ : Fin 6 → CIdx D c d t r r' := ![Sum.inl ⟨μ.1, hμA⟩, Sum.inr (Sum.inl ⟨μ.1, μ.2.1⟩),
    Sum.inr (Sum.inl ⟨ρ, hρ⟩), Sum.inr (Sum.inr u), Sum.inr (Sum.inl ⟨bal t r μ.1, hb⟩),
    Sum.inr (Sum.inl ⟨ρ, hρ⟩)] with hτ
  set a : Fin 6 → ℝ := ![1, -1, 1, -1, 1, -1] with ha
  have hlaw := hZ τ a
  have hvec : ∑ i, a i • cVec hr hr'r J (τ i) = 0 := by
    have e1 := jointMixed_sub_jointFree_local (c := c) (d := d) hr hr'r J hJ μ hρ hρB hm
    have e2 : jointFree hr hr'r J (freeVec ⟨bal t r μ.1, hb⟩) -
        jointFree hr hr'r J (freeVec ⟨ρ, hρ⟩) = WithLp.toLp 2 ((0 : GradSpace D),
          freeVec ⟨bal t r μ.1, hb⟩ - freeVec ⟨ρ, hρ⟩) := by
      rw [jointFree_sub]
      exact jointFree_of_mem_orthogonal J
        (freeVec_sub_mem_orthogonal hr hr'r hb hρ hbal (bal_ball hr) hρB)
    have hsum : ∑ i, a i • cVec hr hr'r J (τ i) =
        (jointMixed D c d μ.1 - (jointFree hr hr'r J (freeVec ⟨μ.1, μ.2.1⟩) -
          jointFree hr hr'r J (freeVec ⟨ρ, hρ⟩))) - WithLp.toLp 2 (u.1, (0 : HkE)) +
        (jointFree hr hr'r J (freeVec ⟨bal t r μ.1, hb⟩) -
          jointFree hr hr'r J (freeVec ⟨ρ, hρ⟩)) := by
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, hτ, ha, cVec]
      simp
      abel
    rw [hsum, e1, e2, hu, ← WithLp.toLp_sub, ← WithLp.toLp_add, Prod.mk_sub_mk, Prod.mk_add_mk]
    simp
  rw [hvec] at hlaw
  have h0 : (‖(0 : WithLp 2 (GradSpace D × HkE))‖ ^ 2).toNNReal = 0 := by simp
  have hae : ∀ᵐ ω ∂stdP, ∑ i, a i * Z (τ i) ω = 0 := by
    refine ae_of_ae_map (p := fun y : ℝ => y = 0) hlaw.aemeasurable ?_
    rw [hlaw.map_eq, h0, gaussianReal_zero_var, ae_dirac_eq]
    exact Filter.eventually_pure.2 rfl
  filter_upwards [hae] with ω hω
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, hτ, ha] at hω
  simp at hω
  rw [show realY Z ω μ.1 = Z (Sum.inl ⟨μ.1, hμA⟩) ω from congrFun (realY_eq μ.1 hμA) ω,
    realX_apply (Z := Z) _ μ.2.1 ω, realX_apply (Z := Z) _ hρ ω, realX_apply (Z := Z) _ hb ω]
  linarith

end Real

end QuantumZipper.K3
