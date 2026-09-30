import QuantumZipper.Proofs.GFF.K3.MixedM7A3

/-!
# K3-mixed M7-a3, step 1: domain independence of the local Gram matrix

For a half-disc `U = ball t r ∩ H ⊆ D` on the free arc of `(D, c, d)`, the local part
`H_supp(U)` of the mixed Dirichlet space (`localClosure D V t r`, `V = mixedSpace D (realSet
(Icc c d))`) depends only on `U`: the test functions of `V` supported in `ball t r` are exactly
those of the half-disc problem `V₀ = mixedSpace U (realSet (Icc (t - r) (t + r)))`
(`mem_mixedSpace_iff_halfDisc_m7c`), and their Dirichlet inner products on `D` and on `U`
coincide. The Gram isometry (`exists_linearIsometry_closure_of_gram`) then identifies the two
local closures, and the local generators `v_μ − v_{bal μ}` correspond, since both are the
representers in `H_supp(U)` of `f ↦ ∫ f dμ` (given membership, M7-a2).

Main result: `mixedLocalGram_of_localMem_halfDisc`: M7-a3 for `D` follows from M7-a2 for `D`
and M7-a2, M7-a3 for the half-disc `U` itself (with `c = t − r`, `d = t + r`).

Source. S. Sheffield, *Gaussian free fields for mathematicians*, PTRF 139 (2007), §2.6,
Thm. 2.17 (`literature/math_0312099.pdf`, PDF p. 14): `H_supp(U)` is the closure of the
functions supported in `U`, and the projection of the Riesz vector of `μ` (carried by `U`) onto
it is the Riesz vector of `μ` for the Dirichlet space of `U` alone. The identification through the
Gram isometry is our own formalization of that remark.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped RealInnerProductSpace

namespace QuantumZipper.K3

/-! ## The half-disc as a Proposition 1.6 domain -/

theorem prop16Geometry_halfDisc_m7c {t r : ℝ} (hr : 0 < r) :
    Prop16Geometry (ball (t : ℂ) r ∩ H) (t - r) (t + r) := by
  have hne : (ball (t : ℂ) r ∩ H).Nonempty := by
    refine ⟨(t : ℂ) + ((r / 2 : ℝ) : ℂ) * Complex.I, ?_, ?_⟩
    · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
      linarith
    · show 0 < ((t : ℂ) + ((r / 2 : ℝ) : ℂ) * Complex.I).im
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_re, Complex.I_im]
      linarith
  have hopen : IsOpen (ball (t : ℂ) r ∩ H) := isOpen_ball.inter isOpen_H
  refine ⟨hopen, ((convex_ball _ _).inter (convex_halfSpace_im_gt 0)).isConnected hne,
    isBounded_ball.subset inter_subset_left, inter_subset_right, by linarith, ?_, ?_⟩
  · ext p
    constructor
    · rintro ⟨hpf, hp0⟩
      have hcl : p ∈ closedBall (t : ℂ) r :=
        closure_ball_subset_closedBall (closure_mono inter_subset_left
          (frontier_subset_closure hpf))
      have hp : p = (p.re : ℂ) := Complex.ext (by simp) (by simpa using hp0)
      refine ⟨p.re, ?_, hp.symm⟩
      rw [hp, mem_closedBall, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs, abs_le] at hcl
      constructor <;> linarith [hcl.1, hcl.2]
    · rintro ⟨s, hs, rfl⟩
      refine ⟨?_, by simp⟩
      rw [hopen.frontier_eq]
      refine ⟨closedBall_inter_Hbar_subset_closure_m7a hr ⟨?_, by simp [Hbar]⟩, fun h => ?_⟩
      · rw [mem_closedBall, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real,
          Real.norm_eq_abs, abs_le]
        constructor <;> linarith [hs.1, hs.2]
      · have := h.2
        simp [H] at this
  · intro s hs
    refine ⟨r - |s - t|, by
      have := abs_lt.2 (show -r < s - t ∧ s - t < r by constructor <;> linarith [hs.1, hs.2])
      show 0 < r - |s - t|
      linarith, ?_⟩
    rintro z ⟨hz, hzH⟩
    refine ⟨?_, hzH⟩
    rw [mem_ball] at hz ⊢
    have h1 : dist (s : ℂ) (t : ℂ) = |s - t| := by
      rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    calc dist z t ≤ dist z s + dist (s : ℂ) t := dist_triangle _ _ _
      _ < r := by rw [h1]; linarith

/-! ## Test functions supported in the half-disc -/

/-- A smooth function supported in `ball t r` lies in `mixedSpace E S` as soon as the frontier of
`E` meets `ball t r` only inside `S`. -/
theorem mem_mixedSpace_of_tsupport_m7c {E S : Set ℂ} {t r : ℝ}
    (hE : frontier E ∩ ball (t : ℂ) r ⊆ S) {f : ℂ → ℝ}
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) (hs : tsupport f ⊆ ball (t : ℂ) r) :
    f ∈ mixedSpace E S := by
  have hcs : HasCompactSupport f :=
    (isCompact_closedBall (t : ℂ) r).of_isClosed_subset (isClosed_tsupport f)
      (hs.trans ball_subset_closedBall)
  have hc : Continuous fun z => ‖fderiv ℝ f z‖ ^ 2 :=
    ((hf.continuous_fderiv smooth_ne_zero).norm).pow 2
  have hcs' : HasCompactSupport fun z => ‖fderiv ℝ f z‖ ^ 2 :=
    (hcs.fderiv (𝕜 := ℝ)).comp_left (g := fun L => ‖L‖ ^ 2) (by simp)
  refine ⟨hf, (hc.integrable_of_hasCompactSupport hcs').integrableOn, (tsupport f)ᶜ,
    (isClosed_tsupport f).isOpen_compl, fun z hz hzs => hz.2 (hE ⟨hz.1, hs hzs⟩),
    fun z hz => image_eq_zero_of_notMem_tsupport hz⟩

/-- **The local test functions of `D` and of the half-disc coincide.** -/
theorem mem_mixedSpace_iff_halfDisc_m7c {D : Set ℂ} {c d t r : ℝ}
    (hgeom : Prop16Geometry D c d) (hr : 0 < r) (hsub : ball (t : ℂ) r ∩ H ⊆ D) (f : ℂ → ℝ) :
    (f ∈ mixedSpace D (realSet (Icc c d)) ∧ tsupport f ⊆ ball (t : ℂ) r) ↔
      (f ∈ mixedSpace (ball (t : ℂ) r ∩ H) (realSet (Icc (t - r) (t + r))) ∧
        tsupport f ⊆ ball (t : ℂ) r) := by
  constructor
  · rintro ⟨hf, hs⟩
    exact ⟨mem_mixedSpace_of_tsupport_m7c
      (frontier_inter_ball_subset_m7a (prop16Geometry_halfDisc_m7c hr) subset_rfl) hf.1 hs, hs⟩
  · rintro ⟨hf, hs⟩
    exact ⟨mem_mixedSpace_of_tsupport_m7c (frontier_inter_ball_subset_m7a hgeom hsub) hf.1 hs, hs⟩

/-- For `f` supported in `ball t r`, the Dirichlet energy on `D` equals that on the half-disc. -/
theorem dirichletEnergyOn_eq_halfDisc_m7c {D : Set ℂ} {c d t r : ℝ}
    (hgeom : Prop16Geometry D c d) (hsub : ball (t : ℂ) r ∩ H ⊆ D) {f : ℂ → ℝ}
    (hs : tsupport f ⊆ ball (t : ℂ) r) :
    dirichletEnergyOn D f = dirichletEnergyOn (ball (t : ℂ) r ∩ H) f := by
  unfold dirichletEnergyOn
  congr 1
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hgeom.1.measurableSet hsub
    fun z hz => ?_
  have hzt : z ∉ tsupport f := fun h => hz.2 ⟨hs h, hgeom.2.2.2.1 hz.1⟩
  rw [fderiv_of_notMem_tsupport ℝ hzt, norm_zero]
  ring

/-! ## The Gram isometry between the two local closures -/

/-- The local test functions of `(D, c, d)` supported in `ball t r` (common index set). -/
abbrev LocTest (D : Set ℂ) (c d t r : ℝ) :=
  {f : ℂ → ℝ // f ∈ mixedSpace D (realSet (Icc c d)) ∧ tsupport f ⊆ ball (t : ℂ) r}

/-- The gradient features in `GradSpace E` of the local test functions. -/
def locFeat (E D : Set ℂ) (c d t r : ℝ) (i : LocTest D c d t r) : GradSpace E := gradFeat E i.1

theorem norm_gradFeat_eq_halfDisc_m7c {D : Set ℂ} {c d t r : ℝ}
    (hgeom : Prop16Geometry D c d) (hr : 0 < r) (hsub : ball (t : ℂ) r ∩ H ⊆ D) {f : ℂ → ℝ}
    (hf : f ∈ mixedSpace D (realSet (Icc c d))) (hs : tsupport f ⊆ ball (t : ℂ) r) :
    ‖gradFeat D f‖ = ‖gradFeat (ball (t : ℂ) r ∩ H) f‖ := by
  have hf₀ := ((mem_mixedSpace_iff_halfDisc_m7c hgeom hr hsub f).1 ⟨hf, hs⟩).1
  have h1 := norm_gradFeat_sq (hf.1.of_le one_le_smooth) hf.2.1 (D := D)
  have h2 := norm_gradFeat_sq (hf₀.1.of_le one_le_smooth) hf₀.2.1
    (D := ball (t : ℂ) r ∩ H)
  rw [dirichletEnergyOn_eq_halfDisc_m7c hgeom hsub hs] at h1
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 (h1.trans h2.symm)

/-- The local test functions have the same Gram matrix in `GradSpace D` and in the gradient space
of the half-disc. -/
theorem inner_locFeat_eq_halfDisc_m7c {D : Set ℂ} {c d t r : ℝ}
    (hgeom : Prop16Geometry D c d) (hr : 0 < r) (hsub : ball (t : ℂ) r ∩ H ⊆ D)
    (i j : LocTest D c d t r) :
    ⟪locFeat (ball (t : ℂ) r ∩ H) D c d t r i, locFeat (ball (t : ℂ) r ∩ H) D c d t r j⟫ =
      ⟪locFeat D D c d t r i, locFeat D D c d t r j⟫ := by
  have hDN := isDNSpace_mixedSpace D (realSet (Icc c d))
  have hDN₀ := isDNSpace_mixedSpace (ball (t : ℂ) r ∩ H) (realSet (Icc (t - r) (t + r)))
  have hi₀ := ((mem_mixedSpace_iff_halfDisc_m7c hgeom hr hsub i.1).1 i.2).1
  have hj₀ := ((mem_mixedSpace_iff_halfDisc_m7c hgeom hr hsub j.1).1 j.2).1
  have hij : i.1 + j.1 ∈ mixedSpace D (realSet (Icc c d)) := hDN.add_mem _ i.2.1 _ j.2.1
  have hijs : tsupport (i.1 + j.1) ⊆ ball (t : ℂ) r :=
    (tsupport_add i.1 j.1).trans (union_subset i.2.2 j.2.2)
  simp only [locFeat]
  rw [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two,
    real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two,
    ← gradFeat_add hDN₀ hi₀ hj₀, ← gradFeat_add hDN i.2.1 j.2.1,
    norm_gradFeat_eq_halfDisc_m7c hgeom hr hsub hij hijs,
    norm_gradFeat_eq_halfDisc_m7c hgeom hr hsub i.2.1 i.2.2,
    norm_gradFeat_eq_halfDisc_m7c hgeom hr hsub j.2.1 j.2.2]

theorem localClosure_eq_span_locFeat_m7c (D : Set ℂ) (c d t r : ℝ) :
    localClosure D (mixedSpace D (realSet (Icc c d))) t r =
      (Submodule.span ℝ (Set.range (locFeat D D c d t r))).topologicalClosure := by
  unfold localClosure
  rw [Set.image_eq_range]
  rfl

theorem localClosure_halfDisc_eq_span_locFeat_m7c {D : Set ℂ} {c d t r : ℝ}
    (hgeom : Prop16Geometry D c d) (hr : 0 < r) (hsub : ball (t : ℂ) r ∩ H ⊆ D) :
    localClosure (ball (t : ℂ) r ∩ H) (mixedSpace (ball (t : ℂ) r ∩ H)
        (realSet (Icc (t - r) (t + r)))) t r =
      (Submodule.span ℝ (Set.range (locFeat (ball (t : ℂ) r ∩ H) D c d t r))).topologicalClosure := by
  unfold localClosure
  have e : {f | f ∈ mixedSpace (ball (t : ℂ) r ∩ H) (realSet (Icc (t - r) (t + r))) ∧
      tsupport f ⊆ ball (t : ℂ) r} =
      {f | f ∈ mixedSpace D (realSet (Icc c d)) ∧ tsupport f ⊆ ball (t : ℂ) r} :=
    Set.ext fun f => (mem_mixedSpace_iff_halfDisc_m7c hgeom hr hsub f).symm
  rw [e, Set.image_eq_range]
  rfl

/-- The local generator `v_μ − v_{bal μ}` represents `f ↦ ∫ f dμ` on the local test functions
(of positive energy). -/
theorem inner_mixedLocVec_gradFeat_m7c {E : Set ℂ} {a b t r r' : ℝ}
    (hg : Prop16Geometry E a b) (ht : t ∈ Ioo a b) (hr' : 0 < r') (hr'r : r' < r)
    (hsub : ball (t : ℂ) r ∩ H ⊆ E) {ρ : Measure ℂ} (hρ : IsAdmissibleH ρ)
    (hρK : ρ (closedBall (t : ℂ) r')ᶜ = 0) {f : ℂ → ℝ}
    (hf : f ∈ mixedSpace E (realSet (Icc a b))) (hs : tsupport f ⊆ ball (t : ℂ) r)
    (hpos : 0 < dirichletEnergyOn E f) :
    ⟪mixedLocVec E a b t r ρ, gradFeat E f⟫ = ∫ x, f x ∂ρ := by
  have hr : 0 < r := hr'.trans hr'r
  have hDN := isDNSpace_mixedSpace E (realSet (Icc a b))
  have hρA := isAdmissibleDual_mixed_halfDisc_local hg hr'r hsub hρ hρK
  obtain ⟨C, hC⟩ := mixedPoissonBound_holds E a b t r r' hg ht hr' hr'r hsub
  have hbA := isAdmissibleDual_bal_of_bound_m7a hDN hr hr'r hsub hC hρ hρK
  rw [mixedLocVec, inner_sub_left, pair_rieszVec hDN hρA ⟨f, hf, hpos⟩ f hf,
    inner_rieszVec_localClosure_eq_zero hDN hbA (bal_ball hr)
      (Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨f, ⟨hf, hs⟩, rfl⟩)), sub_zero]

/-- **M7-a3 by domain independence**: the local Gram matrix of `(D, c, d)` is that of the
half-disc `ball t r ∩ H` (with free diameter), given the membership node M7-a2 for both. -/
theorem mixedLocalGram_of_localMem_halfDisc {D : Set ℂ} {c d t r r' : ℝ}
    (h2 : MixedLocalMemStmt D c d t r r')
    (h2₀ : MixedLocalMemStmt (ball (t : ℂ) r ∩ H) (t - r) (t + r) t r r')
    (h3₀ : MixedLocalGramStmt (ball (t : ℂ) r ∩ H) (t - r) (t + r) t r r') :
    MixedLocalGramStmt D c d t r r' := by
  intro hgeom ht hr' hr'r hsub μ ν hμ hμK hν hνK
  have hr : 0 < r := hr'.trans hr'r
  have hg₀ := prop16Geometry_halfDisc_m7c (t := t) hr
  have ht₀ : t ∈ Ioo (t - r) (t + r) := ⟨by linarith, by linarith⟩
  obtain ⟨J, hJ, hJmem⟩ := exists_linearIsometry_closure_of_gram
    (locFeat (ball (t : ℂ) r ∩ H) D c d t r) (locFeat D D c d t r)
    (inner_locFeat_eq_halfDisc_m7c hgeom hr hsub)
  have hmem₀ : ∀ ρ : Measure ℂ, IsAdmissibleH ρ → ρ (closedBall (t : ℂ) r')ᶜ = 0 →
      mixedLocVec (ball (t : ℂ) r ∩ H) (t - r) (t + r) t r ρ ∈
        (Submodule.span ℝ (Set.range (locFeat (ball (t : ℂ) r ∩ H) D c d t r))).topologicalClosure :=
    fun ρ hρ hρK => by
      rw [← localClosure_halfDisc_eq_span_locFeat_m7c hgeom hr hsub]
      exact h2₀ hg₀ ht₀ hr' hr'r subset_rfl ρ hρ hρK
  have hJρ : ∀ (ρ : Measure ℂ) (hρ : IsAdmissibleH ρ) (hρK : ρ (closedBall (t : ℂ) r')ᶜ = 0),
      J ⟨_, hmem₀ ρ hρ hρK⟩ = mixedLocVec D c d t r ρ := by
    intro ρ hρ hρK
    have hm : mixedLocVec D c d t r ρ ∈
        (Submodule.span ℝ (Set.range (locFeat D D c d t r))).topologicalClosure := by
      rw [← localClosure_eq_span_locFeat_m7c]
      exact h2 hgeom ht hr' hr'r hsub ρ hρ hρK
    set u := J ⟨_, hmem₀ ρ hρ hρK⟩ - mixedLocVec D c d t r ρ with hu
    have hperp : ∀ i, ⟪u, locFeat D D c d t r i⟫ = 0 := by
      intro i
      by_cases h0 : dirichletEnergyOn D i.1 = 0
      · have hn := norm_gradFeat_sq (i.2.1.1.of_le one_le_smooth) i.2.1.2.1 (D := D)
        rw [h0, sq_eq_zero_iff, norm_eq_zero] at hn
        simp only [locFeat, hn, inner_zero_right]
      · have hpos : 0 < dirichletEnergyOn D i.1 :=
          lt_of_le_of_ne (energy_nonneg D _) (Ne.symm h0)
        have hi₀ := (mem_mixedSpace_iff_halfDisc_m7c hgeom hr hsub i.1).1 i.2
        have hpos₀ : 0 < dirichletEnergyOn (ball (t : ℂ) r ∩ H) i.1 := by
          rwa [← dirichletEnergyOn_eq_halfDisc_m7c hgeom hsub i.2.2]
        have e1 : ⟪J ⟨_, hmem₀ ρ hρ hρK⟩, locFeat D D c d t r i⟫ =
            ⟪mixedLocVec (ball (t : ℂ) r ∩ H) (t - r) (t + r) t r ρ,
              gradFeat (ball (t : ℂ) r ∩ H) i.1⟫ := by
          rw [← hJ i, LinearIsometry.inner_map_map]
          rfl
        rw [hu, inner_sub_left, e1]
        change _ - ⟪mixedLocVec D c d t r ρ, gradFeat D i.1⟫ = 0
        rw [inner_mixedLocVec_gradFeat_m7c hg₀ ht₀ hr' hr'r subset_rfl hρ hρK hi₀.1 hi₀.2 hpos₀,
          inner_mixedLocVec_gradFeat_m7c hgeom ht hr' hr'r hsub hρ hρK i.2.1 i.2.2 hpos, sub_self]
    have huu : ⟪u, u⟫ = 0 :=
      inner_eq_zero_of_mem_closure_span_of_forall hperp (sub_mem (hJmem _) hm)
    exact sub_eq_zero.1 (inner_self_eq_zero.1 huu)
  rw [← hJρ μ hμ hμK, ← hJρ ν hν hνK, LinearIsometry.inner_map_map]
  exact h3₀ hg₀ ht₀ hr' hr'r subset_rfl μ ν hμ hμK hν hνK

end QuantumZipper.K3
