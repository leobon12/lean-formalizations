import QuantumZipper.Proofs.Thm18.G3CvIso
import QuantumZipper.Proofs.GFF.K3.MixedM7Real

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3-CURVE, piece 1e: Gaussian realization of the pulled-back coupling

On the joint space `WithLp 2 (HkE × HkE)` one isonormal process (`gs_process_hilbert`), indexed
by `PIdx = AdmT ⊕ AdmT ⊕ PXiIdx`, realizes simultaneously

* a free field `realWP` (vectors `(v̂_μ, 0)`): the field `X` that is pulled back by `Φ`;
* a free field `realXP` (vectors `jointFreeP (v̂_μ) = (J (P̂ v̂_μ), v̂_μ − P̂ v̂_μ)`, with the
  isometry `J` of `exists_pullIsometry`);
* variables `Ξ u` (vectors `(u, 0)`, `u ⊥` the pulled-back local generators).

For any process `Z` with the isonormal laws: `realWP_isFree`, `realXP_isFree`,
`realP_indep` (`Ξ` is independent of `freeIncrSigma realXP`), and `realP_local`: for a local `μ`,
a.s. `W(Φ_*μ) − W(Φ_*bal μ) = X'(μ) − X'(bal μ)`: **the local part of the pulled-back field is
the local part of the free field `X'`** (Sheffield (2007) Thm. 2.17, Hilbert form; the M7-c
construction of MixedM7Joint/MixedM7Real with the mixed space replaced by the pulled-back free
field). `exists_pullCoupling` packages the realization. Own adaptation.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Metric Filter Set
open scoped RealInnerProductSpace

namespace QuantumZipper
namespace G3Cv

open K3 GFFExist LQGDimension.ExistAsm

variable {Φ : ℂ → ℂ} {b r₀ ρ r₁ m M : ℝ}

/-- The free field's vector in the joint space (first factor). -/
def jointW (μ : AdmT) : WithLp 2 (HkE × HkE) := WithLp.toLp 2 (freeVec μ, 0)

/-- The coupled free field's vector. -/
def jointFreeP {hρ : 0 < ρ} {hr₁ : r₁ < ρ}
    (J : freeLocSpace (t := b) hρ hr₁ →ₗᵢ[ℝ] HkE) (x : HkE) : WithLp 2 (HkE × HkE) :=
  WithLp.toLp 2 (J ((freeLocSpace (t := b) hρ hr₁).orthogonalProjectionOnto x),
    x - (freeLocSpace (t := b) hρ hr₁).starProjection x)

theorem inner_jointFreeP {hρ : 0 < ρ} {hr₁ : r₁ < ρ}
    (J : freeLocSpace (t := b) hρ hr₁ →ₗᵢ[ℝ] HkE) (x y : HkE) :
    ⟪jointFreeP J x, jointFreeP J y⟫ = ⟪x, y⟫ := by
  rw [inner_eq_inner_proj_add_inner_sub_proj (freeLocSpace (t := b) hρ hr₁) x y]
  simp only [jointFreeP, WithLp.prod_inner_apply, LinearIsometry.inner_map_map]

theorem jointFreeP_sub {hρ : 0 < ρ} {hr₁ : r₁ < ρ}
    (J : freeLocSpace (t := b) hρ hr₁ →ₗᵢ[ℝ] HkE) (x y : HkE) :
    jointFreeP J x - jointFreeP J y = jointFreeP J (x - y) := by
  simp only [jointFreeP, map_sub]
  rw [← WithLp.toLp_sub, Prod.mk_sub_mk]
  refine congrArg (WithLp.toLp 2) (Prod.ext rfl ?_)
  simp only
  abel

theorem jointFreeP_add_smul {hρ : 0 < ρ} {hr₁ : r₁ < ρ}
    (J : freeLocSpace (t := b) hρ hr₁ →ₗᵢ[ℝ] HkE) (a c : ℝ) (x y : HkE) :
    jointFreeP J (a • x + c • y) = a • jointFreeP J x + c • jointFreeP J y := by
  simp only [jointFreeP, map_add, map_smul]
  rw [← WithLp.toLp_smul, ← WithLp.toLp_smul, ← WithLp.toLp_add, Prod.smul_mk, Prod.smul_mk,
    Prod.mk_add_mk]
  refine congrArg (WithLp.toLp 2) (Prod.ext rfl ?_)
  simp only [smul_sub]
  abel

/-- Vectors of `HkE` orthogonal to the pulled-back local generators. -/
abbrev PXiIdx (Φ : ℂ → ℂ) (b ρ r₁ : ℝ) :=
  {u : HkE // ∀ ν : LocIdx b r₁, ⟪u, pullLocVec Φ b ρ ν.1⟫ = 0}

/-- The index type of the joint process. -/
abbrev PIdx (Φ : ℂ → ℂ) (b ρ r₁ : ℝ) := AdmT ⊕ AdmT ⊕ PXiIdx Φ b ρ r₁

/-- The vectors of the joint process. -/
def pVec {hρ : 0 < ρ} {hr₁ : r₁ < ρ} (J : freeLocSpace (t := b) hρ hr₁ →ₗᵢ[ℝ] HkE) :
    PIdx Φ b ρ r₁ → WithLp 2 (HkE × HkE) :=
  Sum.elim (fun μ => jointW μ) (Sum.elim (fun μ => jointFreeP J (freeVec μ))
    fun u => WithLp.toLp 2 (u.1, 0))

instance instSeparablePJoint : TopologicalSpace.SeparableSpace (WithLp 2 (HkE × HkE)) :=
  (WithLp.homeomorphProd 2 HkE HkE).symm.isQuotientMap.separableSpace

open Classical in
/-- The realized field that is pulled back. -/
def realWP (Z : PIdx Φ b ρ r₁ → (ℕ → ℝ) → ℝ) : (ℕ → ℝ) → FieldSample := fun ω μ =>
  if h : IsAdmissibleH μ then Z (Sum.inl ⟨μ, h⟩) ω else 0

open Classical in
/-- The realized coupled free field. -/
def realXP (Z : PIdx Φ b ρ r₁ → (ℕ → ℝ) → ℝ) : (ℕ → ℝ) → FieldSample := fun ω μ =>
  if h : IsAdmissibleH μ then Z (Sum.inr (Sum.inl ⟨μ, h⟩)) ω else 0

section Real

variable {hρ : 0 < ρ} {hr₁ : r₁ < ρ} {J : freeLocSpace (t := b) hρ hr₁ →ₗᵢ[ℝ] HkE}
  {Z : PIdx Φ b ρ r₁ → (ℕ → ℝ) → ℝ}

theorem realWP_apply (μ : Measure ℂ) (h : IsAdmissibleH μ) (ω : ℕ → ℝ) :
    realWP Z ω μ = Z (Sum.inl ⟨μ, h⟩) ω := by simp [realWP, h]

theorem realXP_apply (μ : Measure ℂ) (h : IsAdmissibleH μ) (ω : ℕ → ℝ) :
    realXP Z ω μ = Z (Sum.inr (Sum.inl ⟨μ, h⟩)) ω := by simp [realXP, h]

variable (hZm : ∀ i, Measurable (Z i))
  (hZ : ∀ {ι : Type} [Fintype ι] (τ : ι → PIdx Φ b ρ r₁) (a : ι → ℝ),
    HasLaw (fun ω => ∑ i, a i * Z (τ i) ω)
      (gaussianReal 0 (‖∑ i, a i • pVec J (τ i)‖ ^ 2).toNNReal) stdP)
include hZm hZ

omit hZm in
theorem realP_hasLaw_single (i : PIdx Φ b ρ r₁) :
    HasLaw (Z i) (gaussianReal 0 (‖pVec J i‖ ^ 2).toNNReal) stdP :=
  gs_comb4 hZ ![i, i, i, i] ![1, 0, 0, 0] _ (fun ω => by simp [Fin.sum_univ_four]) _
    (by simp [Fin.sum_univ_four])

/-- A realized field with vectors `F μ` depending linearly and isometrically on `v̂_μ` is free. -/
theorem realP_isFree_of (sel : AdmT → PIdx Φ b ρ r₁) (F : HkE → WithLp 2 (HkE × HkE))
    (hsel : ∀ μ, pVec J (sel μ) = F (freeVec μ))
    (hF : ∀ x y, ⟪F x, F y⟫ = ⟪x, y⟫)
    (hFsub : ∀ x y, F x - F y = F (x - y))
    (hFlin : ∀ (a c : ℝ) x y, F (a • x + c • y) = a • F x + c • F y)
    (X : (ℕ → ℝ) → FieldSample)
    (hX : ∀ μ (h : IsAdmissibleH μ) ω, X ω μ = Z (sel ⟨μ, h⟩) ω)
    (hX0 : ∀ μ, ¬ IsAdmissibleH μ → ∀ ω, X ω μ = 0) :
    IsFreeGFFModConstH X stdP := by
  set W : AdmT → (ℕ → ℝ) → ℝ := fun μ => Z (sel μ) with hW
  have hdiff : ∀ (μ ν : Measure ℂ) (hμ : IsAdmissibleH μ) (hν : IsAdmissibleH ν),
      (fun ω => X ω μ - X ω ν) = fun ω => W ⟨μ, hμ⟩ ω - W ⟨ν, hν⟩ ω := by
    intro μ ν hμ hν; funext ω; rw [hX μ hμ ω, hX ν hν ω]
  have hlaw2 : ∀ μ ν : AdmT, HasLaw (fun ω => W μ ω - W ν ω)
      (gaussianReal 0 (‖F (freeVec μ) - F (freeVec ν)‖ ^ 2).toNNReal) stdP := fun μ ν =>
    gs_comb4 hZ ![sel μ, sel ν, sel μ, sel μ] ![1, -1, 0, 0] _
      (fun ω => by simp [hW, Fin.sum_univ_four]; ring) _
      (by simp [Fin.sum_univ_four, hsel, sub_eq_add_neg])
  refine ⟨fun μ => ?_, ?_, fun μ ν hμ hν _ => ?_, fun p q hp1 hp2 hp hq1 hq2 hq => ?_,
    fun μ ν hμ hν a c => ?_⟩
  · by_cases h : IsAdmissibleH μ
    · have : (fun ω => X ω μ) = Z (sel ⟨μ, h⟩) := funext fun ω => hX μ h ω
      rw [this]; exact hZm _
    · have : (fun ω => X ω μ) = fun _ => 0 := funext fun ω => hX0 μ h ω
      rw [this]; exact measurable_const
  · refine gs_isGaussianProcess (fun p => ?_) fun I a => ?_
    · rw [hdiff _ _ p.2.1 p.2.2.1]
      exact ((hZm _).sub (hZm _)).aemeasurable
    · set τ : I ⊕ I → PIdx Φ b ρ r₁ := Sum.elim
        (fun i => sel ⟨i.1.1.1, i.1.2.1⟩) (fun i => sel ⟨i.1.1.2, i.1.2.2.1⟩) with hτ
      set a' : I ⊕ I → ℝ := Sum.elim a (fun i => -a i) with ha'
      have e : (fun ω => ∑ i : I, a i * (X ω i.1.1.1 - X ω i.1.1.2)) =
          fun ω => ∑ j, a' j * Z (τ j) ω := by
        funext ω
        rw [Fintype.sum_sum_type, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [hτ, ha', Sum.elim_inl, Sum.elim_inr]
        rw [hX _ i.1.2.1 ω, hX _ i.1.2.2.1 ω]
        ring
      exact ⟨_, e ▸ hZ τ a'⟩
  · rw [hdiff μ ν hμ hν]
    exact gs_integral_eq_zero (hlaw2 ⟨μ, hμ⟩ ⟨ν, hν⟩)
  · rw [hdiff _ _ hp1 hp2, hdiff _ _ hq1 hq2]
    have hinner := freeVec_inner ⟨p.1, hp1⟩ ⟨p.2, hp2⟩ ⟨q.1, hq1⟩ ⟨q.2, hq2⟩ hp hq
    simp only [Prod.mk.eta] at hinner
    rw [← hinner, ← hF, ← hFsub, ← hFsub]
    refine gs_cov_eq (hlaw2 _ _) (hlaw2 _ _) ?_
    exact gs_comb4 hZ ![sel ⟨p.1, hp1⟩, sel ⟨p.2, hp2⟩, sel ⟨q.1, hq1⟩, sel ⟨q.2, hq2⟩]
      ![1, -1, 1, -1] _ (fun ω => by simp [hW, Fin.sum_univ_four]; ring) _
      (by simp [Fin.sum_univ_four, hsel]; abel)
  · have hw := gffEx_admissible_comb hμ hν a c
    have hvec : F (freeVec ⟨_, hw⟩) =
        (a : ℝ) • F (freeVec ⟨μ, hμ⟩) + (c : ℝ) • F (freeVec ⟨ν, hν⟩) := by
      rw [freeVec_comb ⟨μ, hμ⟩ ⟨ν, hν⟩ a c ⟨_, hw⟩ rfl, hFlin]
    have hlaw := gs_comb4 hZ ![sel ⟨_, hw⟩, sel ⟨μ, hμ⟩, sel ⟨ν, hν⟩, sel ⟨μ, hμ⟩]
      ![1, -(a : ℝ), -(c : ℝ), 0]
      (fun ω => W ⟨_, hw⟩ ω - ((a : ℝ) * W ⟨μ, hμ⟩ ω + (c : ℝ) * W ⟨ν, hν⟩ ω))
      (fun ω => by simp [hW, Fin.sum_univ_four]; ring) (0 : WithLp 2 (HkE × HkE))
      (by
        simp [Fin.sum_univ_four]
        rw [hsel, hsel, hsel, hvec]
        abel)
    have h0 : (‖(0 : WithLp 2 (HkE × HkE))‖ ^ 2).toNNReal = 0 := by simp
    have hae : ∀ᵐ ω ∂stdP,
        W ⟨_, hw⟩ ω - ((a : ℝ) * W ⟨μ, hμ⟩ ω + (c : ℝ) * W ⟨ν, hν⟩ ω) = 0 := by
      refine ae_of_ae_map (p := fun y : ℝ => y = 0) hlaw.aemeasurable ?_
      rw [hlaw.map_eq, h0, gaussianReal_zero_var, ae_dirac_eq]
      exact Filter.eventually_pure.2 rfl
    filter_upwards [hae] with ω hω
    rw [hX _ hw ω, hX μ hμ ω, hX ν hν ω]
    simp only [hW] at hω
    linarith

theorem realWP_isFree : IsFreeGFFModConstH (realWP Z) stdP :=
  realP_isFree_of hZm hZ (fun μ => Sum.inl μ) (fun x => WithLp.toLp 2 (x, (0 : HkE)))
    (fun μ => rfl) (fun x y => by simp) (fun x y => by rw [← WithLp.toLp_sub]; simp)
    (fun a c x y => by
      rw [← WithLp.toLp_smul, ← WithLp.toLp_smul, ← WithLp.toLp_add]; simp)
    _ (fun μ h ω => realWP_apply μ h ω) (fun μ h ω => by simp [realWP, h])

theorem realXP_isFree : IsFreeGFFModConstH (realXP Z) stdP :=
  realP_isFree_of hZm hZ (fun μ => Sum.inr (Sum.inl μ)) (jointFreeP J)
    (fun μ => rfl) (inner_jointFreeP J) (jointFreeP_sub J) (jointFreeP_add_smul J)
    _ (fun μ h ω => realXP_apply μ h ω) (fun μ h ω => by simp [realXP, h])

/-- **Independence** of the `Ξ`-coordinates from the coupled free field. -/
theorem realP_indep
    (hJ2 : ∀ k, J k ∈ (Submodule.span ℝ (Set.range fun μ : LocIdx b r₁ =>
        pullLocVec Φ b ρ μ.1)).topologicalClosure) :
    Indep (MeasurableSpace.comap (fun ω (u : PXiIdx Φ b ρ r₁) => Z (Sum.inr (Sum.inr u)) ω)
      inferInstance) (freeIncrSigma (realXP Z)) stdP := by
  set Xi : PXiIdx Φ b ρ r₁ → (ℕ → ℝ) → ℝ := fun u => Z (Sum.inr (Sum.inr u)) with hXi
  set Of : BalIdx → (ℕ → ℝ) → ℝ := fun p ω => realXP Z ω p.1.1 - realXP Z ω p.1.2 with hOf
  have hOfZ : ∀ p : BalIdx, Of p = fun ω => Z (Sum.inr (Sum.inl ⟨p.1.1, p.2.1⟩)) ω -
      Z (Sum.inr (Sum.inl ⟨p.1.2, p.2.2.1⟩)) ω := fun p => by
    funext ω; simp only [hOf, realXP_apply (Z := Z) _ p.2.1 ω, realXP_apply (Z := Z) _ p.2.2.1 ω]
  let fst : PXiIdx Φ b ρ r₁ ⊕ BalIdx → PIdx Φ b ρ r₁ :=
    Sum.elim (fun u => Sum.inr (Sum.inr u)) fun p => Sum.inr (Sum.inl ⟨p.1.1, p.2.1⟩)
  let snd : PXiIdx Φ b ρ r₁ ⊕ BalIdx → PIdx Φ b ρ r₁ :=
    Sum.elim (fun u => Sum.inr (Sum.inr u)) fun p => Sum.inr (Sum.inl ⟨p.1.2, p.2.2.1⟩)
  let sgn : PXiIdx Φ b ρ r₁ ⊕ BalIdx → ℝ := Sum.elim (fun _ => 0) fun _ => -1
  have hW : ∀ k ω, Sum.elim Xi Of k ω = Z (fst k) ω + sgn k * Z (snd k) ω := by
    rintro (u | p) ω
    · simp [hXi, fst, sgn]
    · simp only [Sum.elim_inr, hOfZ p, fst, snd, sgn]; ring
  have hG : IsGaussianProcess (Sum.elim Xi Of) stdP := by
    refine gs_isGaussianProcess (fun k => ?_) fun I a => ?_
    · rcases k with u | p
      · exact (hZm _).aemeasurable
      · rw [Sum.elim_inr, hOfZ p]; exact ((hZm _).sub (hZm _)).aemeasurable
    · set τ : I ⊕ I → PIdx Φ b ρ r₁ := Sum.elim (fun i => fst i.1) fun i => snd i.1 with hτ
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
      inner_eq_zero_of_mem_closure_span_of_forall u.2 (hJ2 k)
    have h1 := realP_hasLaw_single hZ (Sum.inr (Sum.inr u))
    have h2 := gs_comb4 hZ ![Sum.inr (Sum.inl ⟨p.1.1, p.2.1⟩), Sum.inr (Sum.inl ⟨p.1.2, p.2.2.1⟩),
      Sum.inr (Sum.inr u), Sum.inr (Sum.inr u)] ![1, -1, 0, 0]
      (fun ω => Z (Sum.inr (Sum.inl ⟨p.1.1, p.2.1⟩)) ω - Z (Sum.inr (Sum.inl ⟨p.1.2, p.2.2.1⟩)) ω)
      (fun ω => by simp [Fin.sum_univ_four]; ring)
      (pVec J (Sum.inr (Sum.inl ⟨p.1.1, p.2.1⟩)) - pVec J (Sum.inr (Sum.inl ⟨p.1.2, p.2.2.1⟩)))
      (by simp [Fin.sum_univ_four, sub_eq_add_neg] <;> rfl)
    have h3 := gs_comb4 hZ ![Sum.inr (Sum.inr u), Sum.inr (Sum.inl ⟨p.1.1, p.2.1⟩),
      Sum.inr (Sum.inl ⟨p.1.2, p.2.2.1⟩), Sum.inr (Sum.inr u)] ![1, 1, -1, 0]
      (fun ω => Xi u ω + (Z (Sum.inr (Sum.inl ⟨p.1.1, p.2.1⟩)) ω -
        Z (Sum.inr (Sum.inl ⟨p.1.2, p.2.2.1⟩)) ω))
      (fun ω => by simp [hXi, Fin.sum_univ_four]; ring)
      (pVec J (Sum.inr (Sum.inr u)) + (pVec J (Sum.inr (Sum.inl ⟨p.1.1, p.2.1⟩)) -
        pVec J (Sum.inr (Sum.inl ⟨p.1.2, p.2.2.1⟩))))
      (by simp [Fin.sum_univ_four, sub_eq_add_neg, add_assoc] <;> rfl)
    rw [gs_cov_eq h1 h2 h3]
    simp only [pVec, Sum.elim_inr, Sum.elim_inl]
    rw [jointFreeP_sub]
    simp [jointFreeP, inner_sub_right, hu]
  exact hG.indepFun_of_covariance_eq_zero (fun u => (hZm _).aemeasurable)
    (fun p => by rw [hOfZ p]; exact ((hZm _).sub (hZm _)).aemeasurable) hcov

omit hZm in
/-- **Local coupling identity**: a.s. `W(Φ_*μ) − W(Φ_*bal μ) = X'(μ) − X'(bal μ)` for local `μ`. -/
theorem realP_local (hD : PullData Φ b r₀ ρ r₁ m M)
    (hJ : ∀ μ : LocIdx b r₁, J ⟨freeLocVec hρ hr₁ μ,
        Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨μ, rfl⟩)⟩ =
          pullLocVec Φ b ρ μ.1)
    (μ : LocIdx b r₁) :
    ∀ᵐ ω ∂stdP, realWP Z ω (μ.1.map Φ) - realWP Z ω ((bal b ρ μ.1).map Φ) =
      realXP Z ω μ.1 - realXP Z ω (bal b ρ μ.1) := by
  obtain ⟨a1, a2, -⟩ := hD.local_adm μ
  have hb := μ.bal_adm hρ hr₁
  have hmem : freeLocVec hρ hr₁ μ ∈ freeLocSpace (t := b) hρ hr₁ :=
    Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨μ, rfl⟩)
  have hP : (freeLocSpace (t := b) hρ hr₁).orthogonalProjectionOnto (freeLocVec hρ hr₁ μ) =
      ⟨_, hmem⟩ :=
    Submodule.orthogonalProjectionOnto_mem_subspace_eq_self
      (K := freeLocSpace (t := b) hρ hr₁) ⟨_, hmem⟩
  have hPs : (freeLocSpace (t := b) hρ hr₁).starProjection (freeLocVec hρ hr₁ μ) = freeLocVec hρ hr₁ μ := by
    rw [Submodule.starProjection_apply, hP]
  have hJF : jointFreeP J (freeLocVec hρ hr₁ μ) =
      WithLp.toLp 2 (pullLocVec Φ b ρ μ.1, (0 : HkE)) := by
    unfold jointFreeP
    rw [hP, hPs, hJ μ, sub_self]
  set τ : Fin 4 → PIdx Φ b ρ r₁ := ![Sum.inl ⟨_, a1⟩, Sum.inl ⟨_, a2⟩,
    Sum.inr (Sum.inl ⟨μ.1, μ.2.1⟩), Sum.inr (Sum.inl ⟨_, hb⟩)] with hτ
  set a : Fin 4 → ℝ := ![1, -1, -1, 1] with ha
  have hlaw := hZ τ a
  have hvec : ∑ i, a i • pVec J (τ i) = 0 := by
    have e : ∑ i, a i • pVec J (τ i) = (jointW ⟨_, a1⟩ - jointW ⟨_, a2⟩) -
        (jointFreeP J (freeVec ⟨μ.1, μ.2.1⟩) - jointFreeP J (freeVec ⟨_, hb⟩)) := by
      simp [Fin.sum_univ_four, hτ, ha, pVec]; abel
    rw [e, jointFreeP_sub]
    have e2 : freeVec ⟨μ.1, μ.2.1⟩ - freeVec ⟨_, hb⟩ = freeLocVec hρ hr₁ μ := rfl
    rw [e2, hJF, jointW, jointW, ← WithLp.toLp_sub, ← WithLp.toLp_sub, Prod.mk_sub_mk,
      Prod.mk_sub_mk]
    simp [pullLocVec, fvM_eq a1, fvM_eq a2]
  rw [hvec] at hlaw
  have h0 : (‖(0 : WithLp 2 (HkE × HkE))‖ ^ 2).toNNReal = 0 := by simp
  have hae : ∀ᵐ ω ∂stdP, ∑ i, a i * Z (τ i) ω = 0 := by
    refine ae_of_ae_map (p := fun y : ℝ => y = 0) hlaw.aemeasurable ?_
    rw [hlaw.map_eq, h0, gaussianReal_zero_var, ae_dirac_eq]
    exact Filter.eventually_pure.2 rfl
  filter_upwards [hae] with ω hω
  simp [Fin.sum_univ_four, hτ, ha] at hω
  rw [realWP_apply (Z := Z) _ a1 ω, realWP_apply (Z := Z) _ a2 ω,
    realXP_apply (Z := Z) _ μ.2.1 ω, realXP_apply (Z := Z) _ hb ω]
  linarith

end Real

end G3Cv
end QuantumZipper
