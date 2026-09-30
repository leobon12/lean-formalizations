import QuantumZipper.Proofs.GFF.K3.MixedM7Local
import QuantumZipper.Proofs.GFF.K3.MixedLocal
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.ReImTopology

/-!
# K3-mixed M7-a: the Hilbert-space reduction of the mixed half-disc Markov property

Source. S. Sheffield, *Gaussian free fields for mathematicians*, PTRF 139 (2007), §2.6,
Thm. 2.17 (`literature/math_0312099.pdf`, PDF p. 14): for `U ⊆ D` open, the Dirichlet space
splits orthogonally, `H(D) = H_supp(U) ⊕ H_harm(U)`, into the closure of the functions
supported in `U` and the functions harmonic in `U`. Here `U = ball t r ∩ H` is a half-disc on
the free arc of the mixed space `V = mixedSpace D (realSet (Icc c d))`, and

* `localClosure D V t r` is `H_supp(U)`: the closed span of the gradient features of the
  elements of `V` with `tsupport ⊆ ball t r` (they need not vanish on `ℝ`: Neumann condition on
  the diameter);
* `inner_rieszVec_localClosure_eq_zero`: the Riesz vector of any `V`-admissible `ρ` with
  `ρ (ball t r) = 0` lies in `H_supp(U)ᗮ` (in particular `v_{bal μ}`, `v_{P_z}`);
* `isAdmissibleDual_mixed_halfDisc_local`: local admissible measures (carried by
  `closedBall t r'`, `r' < r`) are `V`-admissible (from M4, `isAdmissibleDual_mixed_of_local`);
* `mixedHalfDiscMarkovCov_of_nodes`: **M7-a** follows from three sub-nodes, stated as `Prop`s
  and **not assumed anywhere**:
  - `MixedPoissonBoundStmt` (M7-a1): a uniform bound `(∫ f dP_z)² ≤ C (f,f)_∇` on `V`
    (the trace of `V` on the semicircle, uniformly in `z ∈ closedBall t r' ∩ Hbar`);
  - `MixedLocalMemStmt` (M7-a2): `v_μ − v_{bal μ} ∈ H_supp(U)` for local `μ`, i.e. the
    projection of `v_μ` onto `H_harm(U)` is `v_{bal μ}` (Sheffield Thm 2.17 plus the Poisson
    reproduction of Neumann-harmonic elements; this is where Weyl's lemma enters);
  - `MixedLocalGramStmt` (M7-a3): the local Gram matrix is `kernelCov (halfDiscGreen t r)`.

Given the nodes, the proof of M7-a is Sheffield's orthogonality argument: with
`m_μ = v_μ − v_{bal μ} ∈ H_supp(U)` and `v_{bal μ}, v_ρ ⊥ H_supp(U)`,
`⟪v_μ, v_ρ⟫ = ⟪v_{bal μ}, v_ρ⟫` and `⟪v_μ, v_ν⟫ = ⟪v_{bal μ}, v_{bal ν}⟫ + ⟪m_μ, m_ν⟫`.
The admissibility of `bal μ` from M7-a1 is Jensen for `bal μ = ∫ P_z dμ(z)` (own elementary
argument).
-/

noncomputable section

open MeasureTheory Set Metric
open scoped RealInnerProductSpace

namespace QuantumZipper.K3

/-! ## Geometry of the half-disc -/

/-- The closed half-disc is the closure of the open half-disc (convexity). -/
theorem closedBall_inter_Hbar_subset_closure_m7a {t r : ℝ} (hr : 0 < r) :
    closedBall (t : ℂ) r ∩ Hbar ⊆ closure (ball (t : ℂ) r ∩ H) := by
  have hconv : Convex ℝ (closedBall (t : ℂ) r ∩ Hbar) :=
    (convex_closedBall _ _).inter (convex_halfSpace_im_ge 0)
  have hint : interior (closedBall (t : ℂ) r ∩ Hbar) = ball (t : ℂ) r ∩ H := by
    rw [interior_inter, interior_closedBall _ hr.ne']
    congr 1
    exact Complex.interior_setOfPred_le_im 0
  have hne : (interior (closedBall (t : ℂ) r ∩ Hbar)).Nonempty := by
    rw [hint]
    refine ⟨(t : ℂ) + ((r / 2 : ℝ) : ℂ) * Complex.I, ?_, ?_⟩
    · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
      linarith
    · show 0 < ((t : ℂ) + ((r / 2 : ℝ) : ℂ) * Complex.I).im
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_re, Complex.I_im]
      linarith
  rw [← hint, hconv.closure_interior_eq_closure_of_nonempty_interior hne]
  exact subset_closure

theorem halfDisc_subset_closure_m7a {D : Set ℂ} {t r : ℝ} (hr : 0 < r)
    (hsub : ball (t : ℂ) r ∩ H ⊆ D) : closedBall (t : ℂ) r ∩ Hbar ⊆ closure D :=
  (closedBall_inter_Hbar_subset_closure_m7a hr).trans (closure_mono hsub)

/-- Inside the half-disc, the frontier of `D` lies on the free arc. -/
theorem frontier_inter_ball_subset_m7a {D : Set ℂ} {c d t r : ℝ}
    (hgeom : Prop16Geometry D c d) (hsub : ball (t : ℂ) r ∩ H ⊆ D) :
    frontier D ∩ ball (t : ℂ) r ⊆ realSet (Icc c d) := by
  obtain ⟨hD, -, -, hDH, -, hfr, -⟩ := hgeom
  rintro p ⟨hpf, hpb⟩
  rw [← hfr]
  refine ⟨hpf, ?_⟩
  have hcl : 0 ≤ p.im := by
    have h := closure_mono hDH (frontier_subset_closure hpf)
    rw [show H = {z : ℂ | 0 < z.im} from rfl, Complex.closure_setOfPred_lt_im 0] at h
    exact h
  have hnD : p ∉ D := by
    have h := hpf
    rw [hD.frontier_eq] at h
    exact h.2
  show p.im = 0
  by_contra hne
  exact hnD (hsub ⟨hpb, lt_of_le_of_ne hcl (Ne.symm hne)⟩)

/-- Points of the closed local half-disc carry local discs of `(D, realSet (Icc c d))`. -/
theorem localBall_of_halfDisc_m7a {D : Set ℂ} {c d t r r' : ℝ} (hgeom : Prop16Geometry D c d)
    (hr'r : r' < r) (hsub : ball (t : ℂ) r ∩ H ⊆ D) {z : ℂ}
    (hz : z ∈ closedBall (t : ℂ) r' ∩ Hbar) :
    LocalBall D (realSet (Icc c d)) z (2 * ((r - r') / 4)) := by
  have hr' : 0 ≤ r' := le_trans dist_nonneg (mem_closedBall.1 hz.1)
  have hr : 0 < r := lt_of_le_of_lt hr' hr'r
  have hball : closedBall z (2 * ((r - r') / 4)) ⊆ ball (t : ℂ) r := by
    intro x hx
    rw [mem_closedBall] at hx
    rw [mem_ball]
    have := mem_closedBall.1 hz.1
    calc dist x t ≤ dist x z + dist z t := dist_triangle _ _ _
      _ < r := by linarith
  refine ⟨hz.2, by linarith, hgeom.2.2.2.1, ?_, ?_⟩
  · intro x hx
    exact halfDisc_subset_closure_m7a hr hsub ⟨ball_subset_closedBall (hball hx.1), hx.2⟩
  · intro x hx
    exact frontier_inter_ball_subset_m7a hgeom hsub ⟨hx.2, hball hx.1⟩

/-- **Local admissibility**: admissible measures carried by `closedBall t r'` are
`V`-admissible for the mixed space (M4). -/
theorem isAdmissibleDual_mixed_halfDisc_local {D : Set ℂ} {c d t r r' : ℝ}
    (hgeom : Prop16Geometry D c d) (hr'r : r' < r) (hsub : ball (t : ℂ) r ∩ H ⊆ D)
    {μ : Measure ℂ} (hμ : IsAdmissibleH μ) (hμK : μ (closedBall (t : ℂ) r')ᶜ = 0) :
    IsAdmissibleDual D (mixedSpace D (realSet (Icc c d))) μ := by
  have hS : realSet (Icc c d) ⊆ {z : ℂ | z.im = 0} := by
    rintro _ ⟨s, -, rfl⟩
    simp
  have hHbar : μ Hbarᶜ = 0 := by
    obtain ⟨-, ⟨K, -, hKH, hK⟩, -⟩ := hμ
    exact measure_mono_null (compl_subset_compl.2 hKH) hK
  by_cases hr' : 0 ≤ r'
  · refine isAdmissibleDual_mixed_of_local hgeom.1 hgeom.2.2.2.1 hgeom.2.2.1 hS
      ((isCompact_closedBall _ _).inter_right isClosed_Hbar) (R := (r - r') / 4)
      (by linarith) (fun z hz => localBall_of_halfDisc_m7a hgeom hr'r hsub hz) hμ ?_
    rw [compl_inter]
    exact measure_union_null hμK hHbar
  · -- `closedBall t r' = ∅`, so `μ = 0` is carried by any local set
    have hE : closedBall (t : ℂ) r' = ∅ := closedBall_eq_empty.2 (lt_of_not_ge hr')
    rw [hE, compl_empty] at hμK
    refine isAdmissibleDual_mixed_of_local hgeom.1 hgeom.2.2.2.1 hgeom.2.2.1 hS
      (isCompact_empty (X := ℂ)) (R := 1) one_pos (fun z hz => absurd hz (notMem_empty z)) hμ ?_
    rw [compl_empty]
    exact hμK

/-! ## The local closure `H_supp(U)` -/

/-- `H_supp(U)` for `U = ball t r ∩ H`: the closed span of the gradient features of the test
functions of `V` supported in `ball t r` (Sheffield 2007, §2.6). -/
def localClosure (D : Set ℂ) (V : Set (ℂ → ℝ)) (t r : ℝ) : Submodule ℝ (GradSpace D) :=
  (Submodule.span ℝ (gradFeat D '' {f | f ∈ V ∧ tsupport f ⊆ ball (t : ℂ) r})).topologicalClosure

/-- **Measures outside the half-disc are harmonic there**: the Riesz vector of a `V`-admissible
`ρ` with `ρ (ball t r) = 0` is orthogonal to `H_supp(U)`. -/
theorem inner_rieszVec_localClosure_eq_zero {D : Set ℂ} {V : Set (ℂ → ℝ)} (hV : IsDNSpace D V)
    {t r : ℝ} {ρ : Measure ℂ} (hρ : IsAdmissibleDual D V ρ) (hρB : ρ (ball (t : ℂ) r) = 0)
    {u : GradSpace D} (hu : u ∈ localClosure D V t r) : ⟪rieszVec D V ρ, u⟫ = 0 := by
  by_cases hpos : ∃ g ∈ V, 0 < dirichletEnergyOn D g
  swap
  · rw [eq_zero_of_mem_gradClosure_of_nopos hV hpos rieszVec_mem, inner_zero_left]
  have hle : localClosure D V t r ≤ (Submodule.span ℝ {rieszVec D V ρ})ᗮ := by
    refine Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_orthogonal _)
    rw [Submodule.span_le]
    rintro _ ⟨f, ⟨hf, hfs⟩, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right,
      pair_rieszVec hV hρ hpos f hf]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hρB] with x hx
    exact image_eq_zero_of_notMem_tsupport fun h => hx (hfs h)
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.1 (hle hu)

/-- A bound `(∫ f dρ)² ≤ C (f,f)_∇` on `V` gives `V`-admissibility. -/
theorem isAdmissibleDual_of_sq_le_m7a {D : Set ℂ} {V : Set (ℂ → ℝ)} {ρ : Measure ℂ}
    [IsFiniteMeasure ρ] {K : Set ℂ} (hK : IsCompact K) (hKD : K ⊆ closure D) (hρK : ρ Kᶜ = 0)
    {C : ℝ} (hC : ∀ f ∈ V, (∫ x, f x ∂ρ) ^ 2 ≤ C * dirichletEnergyOn D f) :
    IsAdmissibleDual D V ρ := by
  refine ⟨inferInstance, ⟨K, hK, hKD, hρK⟩, ?_⟩
  unfold dualNormSq
  refine lt_of_le_of_lt (iSup₂_le fun f hf => ENNReal.ofReal_le_ofReal ?_)
    (ENNReal.ofReal_lt_top (r := C))
  rw [div_le_iff₀ hf.2]
  exact hC f hf.1

/-! ## The sub-nodes of M7-a -/

/-- **M7-a1 (sub-node, not proved):** the pairing with the folded Poisson measure `P_z` is
bounded by the Dirichlet energy, uniformly in `z ∈ closedBall t r' ∩ Hbar` (a trace inequality
on the semicircle `∂B(t,r) ∩ Hbar`). -/
def MixedPoissonBoundStmt (D : Set ℂ) (c d t r r' : ℝ) : Prop :=
  Prop16Geometry D c d → t ∈ Set.Ioo c d → 0 < r' → r' < r → ball (t : ℂ) r ∩ H ⊆ D →
    ∃ C : ℝ, ∀ z ∈ closedBall (t : ℂ) r' ∩ Hbar, ∀ f ∈ mixedSpace D (realSet (Icc c d)),
      (∫ x, f x ∂halfDiscPoisson t r z) ^ 2 ≤ C * dirichletEnergyOn D f

/-- **M7-a2 (sub-node, not proved):** for local `μ`, `v_μ − v_{bal μ} ∈ H_supp(U)`
(Sheffield 2007 Thm 2.17 for the mixed space: the `H_harm(U)`-component of `v_μ` is
`v_{bal μ}`). -/
def MixedLocalMemStmt (D : Set ℂ) (c d t r r' : ℝ) : Prop :=
  Prop16Geometry D c d → t ∈ Set.Ioo c d → 0 < r' → r' < r → ball (t : ℂ) r ∩ H ⊆ D →
    ∀ μ : Measure ℂ, IsAdmissibleH μ → μ (closedBall (t : ℂ) r')ᶜ = 0 →
      mixedLocVec D c d t r μ ∈ localClosure D (mixedSpace D (realSet (Icc c d))) t r

/-- **M7-a3 (sub-node, not proved):** the Gram matrix of the local parts `v_μ − v_{bal μ}` is
the half-disc Green kernel (Neumann on the diameter, Dirichlet on the semicircle). -/
def MixedLocalGramStmt (D : Set ℂ) (c d t r r' : ℝ) : Prop :=
  Prop16Geometry D c d → t ∈ Set.Ioo c d → 0 < r' → r' < r → ball (t : ℂ) r ∩ H ⊆ D →
    ∀ μ ν : Measure ℂ, IsAdmissibleH μ → μ (closedBall (t : ℂ) r')ᶜ = 0 →
      IsAdmissibleH ν → ν (closedBall (t : ℂ) r')ᶜ = 0 →
        ⟪mixedLocVec D c d t r μ, mixedLocVec D c d t r ν⟫ = kernelCov (halfDiscGreen t r) μ ν

/-! ## The reduction -/

/-- Admissibility of the balayage from the uniform Poisson bound (Jensen for
`∫ f d(bal μ) = ∫ (∫ f dP_z) dμ(z)`; own elementary argument). -/
theorem isAdmissibleDual_bal_of_bound_m7a {D : Set ℂ} {V : Set (ℂ → ℝ)} (hV : IsDNSpace D V)
    {t r r' : ℝ} (hr : 0 < r) (hr'r : r' < r) (hsub : ball (t : ℂ) r ∩ H ⊆ D) {C : ℝ}
    (hC : ∀ z ∈ closedBall (t : ℂ) r' ∩ Hbar, ∀ f ∈ V,
      (∫ x, f x ∂halfDiscPoisson t r z) ^ 2 ≤ C * dirichletEnergyOn D f)
    {μ : Measure ℂ} (hμ : IsAdmissibleH μ) (hμK : μ (closedBall (t : ℂ) r')ᶜ = 0) :
    IsAdmissibleDual D V (bal t r μ) := by
  have := hμ.1
  have := isFiniteMeasure_bal hr hr'r hμK
  have hKc : IsCompact (sphere (t : ℂ) r ∩ Hbar) :=
    (isCompact_sphere _ _).inter_right isClosed_Hbar
  have hKD : sphere (t : ℂ) r ∩ Hbar ⊆ closure D := fun x hx =>
    halfDisc_subset_closure_m7a hr hsub ⟨sphere_subset_closedBall hx.1, hx.2⟩
  have hbK : bal t r μ (sphere (t : ℂ) r ∩ Hbar)ᶜ = 0 :=
    bal_null_of_forall (isClosed_sphere.measurableSet.inter isClosed_Hbar.measurableSet).compl
      fun z => halfDiscPoisson_compl_eq_zero hr z
  have hHbar : μ Hbarᶜ = 0 := by
    obtain ⟨-, ⟨K, -, hKH, hK⟩, -⟩ := hμ
    exact measure_mono_null (compl_subset_compl.2 hKH) hK
  have hae : ∀ᵐ z ∂μ, z ∈ closedBall (t : ℂ) r' ∩ Hbar := by
    rw [ae_iff]
    refine measure_mono_null (fun z hz => ?_) (measure_union_null hμK hHbar)
    by_contra h
    exact hz (by simpa [not_or] using h)
  refine isAdmissibleDual_of_sq_le_m7a hKc hKD hbK (C := μ.real univ ^ 2 * max C 0)
    fun f hf => ?_
  have hE := energy_nonneg D f
  have hfi : Integrable f (bal t r μ) := integrable_of_mem hV ⟨_, hKc, hbK⟩ hf
  rw [(integral_bal hfi).2]
  have hs : 0 ≤ max C 0 * dirichletEnergyOn D f := mul_nonneg (le_max_right _ _) hE
  have hb : ∀ᵐ z ∂μ, ‖∫ x, f x ∂halfDiscPoisson t r z‖ ≤
      Real.sqrt (max C 0 * dirichletEnergyOn D f) := by
    filter_upwards [hae] with z hz
    rw [Real.norm_eq_abs]
    refine Real.abs_le_sqrt ((hC z hz f hf).trans ?_)
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hE
  have h1 := norm_integral_le_of_norm_le_const hb
  rw [Real.norm_eq_abs] at h1
  calc (∫ z, ∫ x, f x ∂halfDiscPoisson t r z ∂μ) ^ 2
      = |∫ z, ∫ x, f x ∂halfDiscPoisson t r z ∂μ| ^ 2 := (sq_abs _).symm
    _ ≤ (Real.sqrt (max C 0 * dirichletEnergyOn D f) * μ.real univ) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h1 2
    _ = μ.real univ ^ 2 * max C 0 * dirichletEnergyOn D f := by
        rw [mul_pow, Real.sq_sqrt hs]; ring

/-- **M7-a from its three sub-nodes** (Sheffield 2007, Thm 2.17: orthogonality of
`H_supp(U)` and `H_harm(U)`). -/
theorem mixedHalfDiscMarkovCov_of_nodes {D : Set ℂ} {c d t r r' : ℝ}
    (h1 : MixedPoissonBoundStmt D c d t r r') (h2 : MixedLocalMemStmt D c d t r r')
    (h3 : MixedLocalGramStmt D c d t r r') : MixedHalfDiscMarkovCovStmt D c d t r r' := by
  intro hgeom ht hr' hr'r hsub
  have hr : 0 < r := hr'.trans hr'r
  set V := mixedSpace D (realSet (Icc c d)) with hV
  have hDN : IsDNSpace D V := isDNSpace_mixedSpace D _
  obtain ⟨C, hC⟩ := h1 hgeom ht hr' hr'r hsub
  have hKc : IsCompact (sphere (t : ℂ) r ∩ Hbar) :=
    (isCompact_sphere _ _).inter_right isClosed_Hbar
  have hKD : sphere (t : ℂ) r ∩ Hbar ⊆ closure D := fun x hx =>
    halfDisc_subset_closure_m7a hr hsub ⟨sphere_subset_closedBall hx.1, hx.2⟩
  have hP : ∀ z ∈ closedBall (t : ℂ) r' ∩ Hbar, IsAdmissibleDual D V (halfDiscPoisson t r z) := by
    intro z hz
    have := isProbabilityMeasure_halfDiscPoisson hr
      (mem_ball_of_le_k3 hr'r (mem_closedBall_iff_norm.1 hz.1))
    exact isAdmissibleDual_of_sq_le_m7a hKc hKD (halfDiscPoisson_compl_eq_zero hr z) (hC z hz)
  have hbA : ∀ μ : Measure ℂ, IsAdmissibleH μ → μ (closedBall (t : ℂ) r')ᶜ = 0 →
      IsAdmissibleDual D V (bal t r μ) := fun μ hμ hμK =>
    isAdmissibleDual_bal_of_bound_m7a hDN hr hr'r hsub hC hμ hμK
  have hlA : ∀ μ : Measure ℂ, IsAdmissibleH μ → μ (closedBall (t : ℂ) r')ᶜ = 0 →
      IsAdmissibleDual D V μ := fun μ hμ hμK =>
    isAdmissibleDual_mixed_halfDisc_local hgeom hr'r hsub hμ hμK
  refine ⟨hP, fun μ hμ hμK => ⟨hlA μ hμ hμK, hbA μ hμ hμK, fun ρ hρ hρB => ?_,
    fun ν hν hνK => ?_⟩⟩
  · rw [dualCov_eq_inner_rieszVec hDN (hlA μ hμ hμK) hρ,
      dualCov_eq_inner_rieszVec hDN (hbA μ hμ hμK) hρ]
    have h0 := inner_rieszVec_localClosure_eq_zero hDN hρ hρB (h2 hgeom ht hr' hr'r hsub μ hμ hμK)
    simp only [mixedLocVec, inner_sub_right] at h0
    rw [← hV] at h0
    have e1 := real_inner_comm (rieszVec D V μ) (rieszVec D V ρ)
    have e2 := real_inner_comm (rieszVec D V (bal t r μ)) (rieszVec D V ρ)
    linarith
  · rw [dualCov_eq_inner_rieszVec hDN (hlA μ hμ hμK) (hlA ν hν hνK),
      dualCov_eq_inner_rieszVec hDN (hbA μ hμ hμK) (hbA ν hν hνK)]
    have hm := h3 hgeom ht hr' hr'r hsub μ ν hμ hμK hν hνK
    have c1 := inner_rieszVec_localClosure_eq_zero hDN (hbA μ hμ hμK) (bal_ball hr)
      (h2 hgeom ht hr' hr'r hsub ν hν hνK)
    have c2 := inner_rieszVec_localClosure_eq_zero hDN (hbA ν hν hνK) (bal_ball hr)
      (h2 hgeom ht hr' hr'r hsub μ hμ hμK)
    simp only [mixedLocVec, inner_sub_left, inner_sub_right] at hm c1 c2
    rw [← hV] at hm c1 c2
    have e3 := real_inner_comm (rieszVec D V μ) (rieszVec D V (bal t r ν))
    have e4 := real_inner_comm (rieszVec D V (bal t r μ)) (rieszVec D V (bal t r ν))
    linarith

end QuantumZipper.K3
