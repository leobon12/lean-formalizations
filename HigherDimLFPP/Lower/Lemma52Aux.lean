import HigherDimLFPP.Lower.Lemma52Setup
import HigherDimLFPP.Field.BandsSup
import HigherDimLFPP.Field.ExpectedSupDrift

/-!
# Auxiliary results for Lemma 5.2 (source §5.1; HA4 D5)

Packet P-L3.

* Band algebra: `isPairable_trans`, `bandVecM_trans` (`⟨H_S, μ - ν⟩ = ⟨H_S, μ - ρ⟩ + ⟨H_S, ρ - ν⟩`),
  `bandVecM_congr_set` (null changes of the scale set), and `bandVecM_Ioi_split`: on
  `(0, ∞) = (0, a) ∪ (a, b) ∪ (b, ∞)` up to a null set, the all-scale pairing splits into fine,
  band and coarse scales (HA4 D5: "disjoint scale sets").
* `gEM_euclid_le`: expected maxima of Gram families in a finite-dimensional space are
  `s √(2 log 2|ι|)`-Lipschitz under perturbations of size `s` (HA4 D5 step 4).
* `LowerData.gem_le_gem_prof₀`: **the padding loss** (5.9):
  `E max_j G(f_j) ≤ E max_j G(g_j) + √(2π√(2E₀)/K) √(2 log 2(J+1))`, `g_j = f_j + a_j ψ_K v`.
* `emaxAbs_coarse_le`: **Lemma 3.4(b)** in the form used here: for every finite family of
  profiles in `V_n` of energy `≤ E₀`, `E max |δ^{-1/2} ⟨H_{δL,∞}, μ_{δg} - μ₀⟩| ≤ C √(E₀/L)`
  (P-F3b's `bandLemma34b_sup_wn`, transported to P-F3a's `graphMeasure`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped RealInnerProductSpace ENNReal

namespace HigherDimLFPP.Lower

open LQGDimension (gaussianExpectedMax)

variable {d : ℕ} {κ : Rd d → ℝ}

/-! ## Band algebra -/

theorem isPairable_trans {S : Set ℝ} {μ ρ ν : Measure (Rd d)} (h₁ : IsPairable κ S μ ρ)
    (h₂ : IsPairable κ S ρ ν) : IsPairable κ S μ ν := by
  have e : bandFun κ S μ - bandFun κ S ν =
      (bandFun κ S μ - bandFun κ S ρ) + (bandFun κ S ρ - bandFun κ S ν) := by abel
  rw [IsPairable, e]
  exact MemLp.add h₁ h₂

/-- `⟨H_S, μ - ν⟩ = ⟨H_S, μ - ρ⟩ + ⟨H_S, ρ - ν⟩`. -/
theorem bandVecM_trans {S : Set ℝ} {μ ρ ν : Measure (Rd d)} (h₁ : IsPairable κ S μ ρ)
    (h₂ : IsPairable κ S ρ ν) :
    bandVecM κ S μ ν = bandVecM κ S μ ρ + bandVecM κ S ρ ν := by
  refine Lp.ext ?_
  filter_upwards [coeFn_bandVecM (isPairable_trans h₁ h₂),
    Lp.coeFn_add (bandVecM κ S μ ρ) (bandVecM κ S ρ ν), coeFn_bandVecM h₁,
    coeFn_bandVecM h₂] with p hp1 hp2 hp3 hp4
  rw [hp1, hp2, Pi.add_apply, hp3, hp4]
  simp only [Pi.sub_apply]
  abel

theorem bandFun_sub_ae_congr_set {S T : Set ℝ} (hST : S =ᵐ[volume] T) (μ ν : Measure (Rd d)) :
    bandFun κ S μ - bandFun κ S ν =ᵐ[volume] bandFun κ T μ - bandFun κ T ν := by
  have h1 : ∀ᵐ t : ℝ ∂volume, (t ∈ S ↔ t ∈ T) := hST.mem_iff
  have h : ∀ᵐ p : ℝ × Rd d ∂(volume.prod volume), (p.1 ∈ S ↔ p.1 ∈ T) :=
    (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure ℝ))
      (ν := (volume : Measure (Rd d)))).ae h1
  filter_upwards [h] with p hp
  simp only [Pi.sub_apply, bandFun_apply]
  by_cases hS : p.1 ∈ S
  · rw [indicator_of_mem hS, indicator_of_mem (hp.1 hS), indicator_of_mem hS,
      indicator_of_mem (hp.1 hS)]
  · have hT : p.1 ∉ T := fun h => hS (hp.2 h)
    rw [indicator_of_notMem hS, indicator_of_notMem hT, indicator_of_notMem hS,
      indicator_of_notMem hT]

/-- Null changes of the scale set change neither pairability nor the kernel vector. -/
theorem bandVecM_congr_set {S T : Set ℝ} (hST : S =ᵐ[volume] T) {μ ν : Measure (Rd d)}
    (h : IsPairable κ T μ ν) : IsPairable κ S μ ν ∧ bandVecM κ S μ ν = bandVecM κ T μ ν := by
  have hae := bandFun_sub_ae_congr_set (κ := κ) hST μ ν
  have hS : IsPairable κ S μ ν := MemLp.ae_eq hae.symm h
  exact ⟨hS, bandVecM_congr hS h hae⟩

/-- **Fine, band and coarse scales** (HA4 D5): for `0 < a < b`,
`⟨h, μ - ν⟩ = ⟨H_{0,a}, μ - ν⟩ + ⟨H_{a,b}, μ - ν⟩ + ⟨H_{b,∞}, μ - ν⟩`. -/
theorem bandVecM_Ioi_split {a b : ℝ} (ha : 0 < a) (hab : a < b) {μ ν : Measure (Rd d)}
    (h : IsPairable κ (Ioi 0) μ ν) :
    bandVecM κ (Ioi 0) μ ν =
      bandVecM κ (Ioo 0 a) μ ν + bandVecM κ (Ioo a b) μ ν + bandVecM κ (Ioi b) μ ν := by
  have hset : (Ioo 0 a ∪ Ioo a b ∪ Ioi b : Set ℝ) =ᵐ[volume] Ioi 0 := by
    rw [ae_eq_set]
    constructor
    · have hsub : (Ioo 0 a ∪ Ioo a b ∪ Ioi b : Set ℝ) ⊆ Ioi 0 :=
        union_subset (union_subset Ioo_subset_Ioi_self fun x hx => lt_trans ha hx.1)
          (Ioi_subset_Ioi (ha.trans hab).le)
      rw [sdiff_eq_empty.2 hsub, measure_empty]
    · refine measure_mono_null (t := ({a, b} : Set ℝ)) ?_ ((Set.toFinite _).measure_zero _)
      rintro x ⟨hx0, hxU⟩
      have hx0' : 0 < x := hx0
      by_contra hne
      have hxa : x ≠ a := fun h => hne (Or.inl h)
      have hxb : x ≠ b := fun h => hne (Or.inr h)
      rcases lt_or_gt_of_ne hxa with h1 | h1
      · exact hxU (Or.inl (Or.inl ⟨hx0', h1⟩))
      · rcases lt_or_gt_of_ne hxb with h2 | h2
        · exact hxU (Or.inl (Or.inr ⟨h1, h2⟩))
        · exact hxU (Or.inr h2)
  obtain ⟨hU, hUe⟩ := bandVecM_congr_set hset h
  have hm12 : MeasurableSet (Ioo 0 a ∪ Ioo a b : Set ℝ) := measurableSet_Ioo.union measurableSet_Ioo
  have hd1 : Disjoint (Ioo 0 a ∪ Ioo a b : Set ℝ) (Ioi b) := by
    refine Set.disjoint_left.2 fun x hx hy => ?_
    rcases hx with hx | hx
    · linarith [hx.2, (mem_Ioi.1 hy)]
    · linarith [hx.2, (mem_Ioi.1 hy)]
  have hd2 : Disjoint (Ioo 0 a : Set ℝ) (Ioo a b) :=
    Set.disjoint_left.2 fun x hx hy => by linarith [hx.2, hy.1]
  rw [← hUe, bandVecM_union hm12 measurableSet_Ioi hd1 hU,
    bandVecM_union measurableSet_Ioo measurableSet_Ioo hd2
      (hU.mono_set hm12 subset_union_left)]

/-! ## Perturbation of Gram expected maxima in finite dimension -/

theorem gEM_euclid_le {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (x y : ι → E) {s : ℝ}
    (hs : 0 ≤ s) (hxy : ∀ i, ‖x i - y i‖ ≤ s) :
    gaussianExpectedMax (Finset.univ : Finset ι) (fun i j => ⟪x i, x j⟫) 0 ≤
      gaussianExpectedMax (Finset.univ : Finset ι) (fun i j => ⟪y i, y j⟫) 0 +
        s * Real.sqrt (2 * Real.log (2 * Fintype.card ι)) := by
  classical
  rw [LQGDimension.gaussianExpectedMax_gram_eq_vecExpectedMax,
    LQGDimension.gaussianExpectedMax_gram_eq_vecExpectedMax]
  refine (vecExpectedMax_le_add_sign Finset.univ x y 0).trans (add_le_add le_rfl ?_)
  rw [← LQGDimension.gaussianExpectedMax_gram_eq_vecExpectedMax]
  have hgram : ∀ p ∈ (Finset.univ : Finset ι) ×ˢ (Finset.univ : Finset Bool),
      ∀ q ∈ (Finset.univ : Finset ι) ×ˢ (Finset.univ : Finset Bool),
      ⟪(if p.2 = true then x p.1 - y p.1 else y p.1 - x p.1),
          (if q.2 = true then x q.1 - y q.1 else y q.1 - x q.1)⟫ =
        Bands.signK p.2 q.2 * ⟪x p.1 - y p.1, x q.1 - y q.1⟫ := by
    intro p _ q _
    rcases p with ⟨i, pi⟩
    rcases q with ⟨j, pj⟩
    have ei : y i - x i = -(x i - y i) := (neg_sub _ _).symm
    have ej : y j - x j = -(x j - y j) := (neg_sub _ _).symm
    cases pi <;> cases pj <;>
      simp only [Bands.signK, Bool.false_eq_true, ite_false, ite_true, ei, ej, inner_neg_left,
        inner_neg_right, neg_neg, one_mul, neg_one_mul, reduceCtorEq]
  rw [LQGDimension.gaussianExpectedMax_congr _ 0 hgram]
  have h := Bands.gEM_signK_le (Finset.univ : Finset ι) (fun i j => ⟪x i - y i, x j - y j⟫)
    (by unfold LQGDimension.PSDOn; exact LQGDimension.posSemidef_gramOn _ fun i => x i - y i)
    hs fun i _ => by
      rw [real_inner_self_eq_norm_sq]
      exact pow_le_pow_left₀ (norm_nonneg _) (hxy i) 2
  rwa [Finset.card_univ] at h

/-! ## The padding loss (5.9) -/

namespace LowerData

variable (D : LowerData d)

theorem norm_f_sub_prof₀_le (hv : ‖D.v‖ = 1) (j : Fin (D.J + 1)) (x : ℝ) :
    ‖D.f j x - D.prof₀ j x‖ ≤ √(2 * (D.e + 1)) / D.K := by
  have ha0 : 0 ≤ aLim D.e (D.f j) := Real.sqrt_nonneg _
  rw [prof₀, padProf, sub_add_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg ha0, hv, mul_one]
  calc aLim D.e (D.f j) * |psiK D.K x| ≤ √(2 * (D.e + 1)) * (1 / D.K) :=
        mul_le_mul (aLim_le _ _) (abs_psiK_le _ _) (abs_nonneg _) (Real.sqrt_nonneg _)
    _ = √(2 * (D.e + 1)) / D.K := by rw [mul_one_div]

/-- **The padding loss** (5.9):
`E max_j G(f_j) ≤ E max_j G(g_j) + √(2π√(2E₀)/K) √(2 log 2(J+1))`. -/
theorem gem_le_gem_prof₀ (hv : ‖D.v‖ = 1) (hmem : ∀ j, D.f j ∈ Vg (Rd (d - 1)) D.n)
    (hg : 1 ≤ D.g) :
    gaussianExpectedMax (Finset.univ : Finset (Fin (D.J + 1)))
        (fun j k => gCov (D.f j) (D.f k)) (fun _ => 0) ≤
      gaussianExpectedMax (Finset.univ : Finset (Fin (D.J + 1)))
          (fun j k => gCov (D.prof₀ j) (D.prof₀ k)) 0 +
        √(2 * Real.pi * (√(2 * (D.e + 1)) / D.K)) *
          Real.sqrt (2 * Real.log (2 * ((D.J : ℝ) + 1))) := by
  classical
  set φ : Fin (D.J + 1) × Bool → ℝ → Rd (d - 1) :=
    fun p => if p.2 then D.f p.1 else D.prof₀ p.1 with hφ
  have hcont : ∀ p, Continuous (φ p) := by
    intro p
    rcases p with ⟨j, _ | _⟩
    · exact Var.Vg_continuous (padProf_mem_Vg hg (hmem j) D.v _)
    · exact Var.Vg_continuous (hmem j)
  obtain ⟨T, hT⟩ := LQGDimension.exists_gram_of_psdOn (Finset.univ : Finset (Fin (D.J + 1) × Bool))
    (fun p q => gCov (φ p) (φ q))
    (Var.gCov_psdOn _ φ fun p _ => (hcont p).intervalIntegrable 0 1)
  set x : Fin (D.J + 1) → EuclideanSpace ℝ (Finset.univ : Finset (Fin (D.J + 1) × Bool)) :=
    fun j => T (j, true) with hx
  set y : Fin (D.J + 1) → EuclideanSpace ℝ (Finset.univ : Finset (Fin (D.J + 1) × Bool)) :=
    fun j => T (j, false) with hy
  have e1 : gaussianExpectedMax (Finset.univ : Finset (Fin (D.J + 1)))
      (fun j k => gCov (D.f j) (D.f k)) (fun _ => 0) =
      gaussianExpectedMax (Finset.univ : Finset (Fin (D.J + 1))) (fun j k => ⟪x j, x k⟫) 0 :=
    LQGDimension.gaussianExpectedMax_congr _ _ fun j _ k _ => by
      rw [hx, hT _ (Finset.mem_univ _) _ (Finset.mem_univ _)]
      rfl
  have e2 : gaussianExpectedMax (Finset.univ : Finset (Fin (D.J + 1)))
      (fun j k => gCov (D.prof₀ j) (D.prof₀ k)) 0 =
      gaussianExpectedMax (Finset.univ : Finset (Fin (D.J + 1))) (fun j k => ⟪y j, y k⟫) 0 :=
    LQGDimension.gaussianExpectedMax_congr _ _ fun j _ k _ => by
      rw [hy, hT _ (Finset.mem_univ _) _ (Finset.mem_univ _)]
      rfl
  rw [e1, e2]
  have hK : (0 : ℝ) < D.K := D.K_cast_pos
  have hs0 : 0 ≤ 2 * Real.pi * (√(2 * (D.e + 1)) / D.K) := by positivity
  have h := gEM_euclid_le x y (Real.sqrt_nonneg (2 * Real.pi * (√(2 * (D.e + 1)) / D.K)))
    fun j => ?_
  · rwa [Fintype.card_fin, Nat.cast_add, Nat.cast_one] at h
  · have hsq := Var.norm_sub_sq_of_gram φ T (a := (j, true)) (b := (j, false)) (hcont _) (hcont _)
      (hT _ (Finset.mem_univ _) _ (Finset.mem_univ _))
      (hT _ (Finset.mem_univ _) _ (Finset.mem_univ _))
      (hT _ (Finset.mem_univ _) _ (Finset.mem_univ _))
    have hint : ∫ t in (0 : ℝ)..1, ‖φ (j, true) t - φ (j, false) t‖ ≤ √(2 * (D.e + 1)) / D.K := by
      have h1 : ∫ t in (0 : ℝ)..1, ‖φ (j, true) t - φ (j, false) t‖ ≤
          ∫ _t in (0 : ℝ)..1, √(2 * (D.e + 1)) / D.K :=
        intervalIntegral.integral_mono_on zero_le_one
          (((hcont _).sub (hcont _)).norm.intervalIntegrable 0 1) intervalIntegrable_const
          fun t _ => D.norm_f_sub_prof₀_le hv j t
      rwa [intervalIntegral.integral_const, sub_zero, one_smul] at h1
    rw [← Real.sqrt_sq (norm_nonneg (x j - y j))]
    refine Real.sqrt_le_sqrt ?_
    rw [hx, hy, hsq]
    exact mul_le_mul_of_nonneg_left hint (by positivity)

end LowerData

/-! ## Lemma 3.4(b) for P-F3a's graph measures -/

theorem graphMeasure_eq_bands (m : ℕ) (δ : ℝ) (f : ℝ → Rd m) :
    graphMeasure (m + 1) δ f = Bands.graphMeasure δ f := by
  unfold graphMeasure Bands.graphMeasure
  congr 1
  funext x
  rw [graphPt, Bands.lift_eq]

/-- **Lemma 3.4(b)** (P-F3b's `bandLemma34b_sup_wn`) for every finite family of profiles of
`V_n(ℝ^{d-1})` with energy `≤ E₀`: `E max_i |δ^{-1/2} ⟨H_{δL,∞}, μ_{δ g_i} - μ₀⟩| ≤ C √(E₀/L)`. -/
theorem emaxAbs_coarse_le (hd : 1 ≤ d) (hκ : IsLFPPKernel κ) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ (δ L : ℝ), 0 < δ → 0 < L → ∀ (E₀ : ℝ) (n : ℕ) {ι : Type*} [Fintype ι]
      (g : ι → ℝ → Rd (d - 1)), (∀ i, g i ∈ Vg (Rd (d - 1)) n ∧ energy (g i) ≤ E₀) →
      emaxAbs (fun i => (Real.sqrt δ)⁻¹ • bandVecM κ (Ioi (δ * L)) (graphMeasure d δ (g i))
        (graphMeasure d δ 0)) ≤ Cb * Real.sqrt (E₀ / L) := by
  obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
  obtain ⟨C, hC0, hC⟩ := bandLemma34b_sup_wn (m := m) hκ
  refine ⟨C, hC0, fun δ L hδ hL E₀ n ι _ g hg => ?_⟩
  classical
  set F : Finset (ℝ → Rd m) := Finset.univ.image g with hF
  have hFmem : ∀ f ∈ F, f ∈ Vg (Rd m) n ∧ energy f ≤ E₀ := by
    intro f hf
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hf
    exact hg i
  have h := hC LQGDimension.ExistAsm.stdP (W₀ (m + 1)) (isWhiteNoise_W₀ (m + 1)) δ L hδ hL E₀ n
    F hFmem
  refine le_trans ?_ h
  unfold emaxAbs
  have hW := isWhiteNoise_W₀ (m + 1)
  have hae : ∀ᵐ ω ∂LQGDimension.ExistAsm.stdP, ∀ i,
      W₀ (m + 1) ((Real.sqrt δ)⁻¹ • bandVecM κ (Ioi (δ * L)) (graphMeasure (m + 1) δ (g i))
        (graphMeasure (m + 1) δ 0)) ω =
      (Real.sqrt δ)⁻¹ * W₀ (m + 1) (bandVecM κ (Ioi (δ * L)) (graphMeasure (m + 1) δ (g i))
        (graphMeasure (m + 1) δ 0)) ω :=
    ae_all_iff.2 fun i => hW.smul_ae _ _
  refine integral_mono_ae (integrable_iSup_abs_W₀ _)
    (integrable_iSup_fintype fun f => ((integrable_W hW _).const_mul _).abs) ?_
  filter_upwards [hae] with ω hω
  simp only [hω]
  rcases isEmpty_or_nonempty ι with hι | hι
  · rw [Real.iSup_of_isEmpty]
    exact Real.iSup_nonneg fun f => abs_nonneg _
  · refine ciSup_le fun i => ?_
    have hi : g i ∈ F := Finset.mem_image_of_mem g (Finset.mem_univ i)
    refine le_trans (le_of_eq ?_) (le_ciSup (f := fun f : ↥F => |(Real.sqrt δ)⁻¹ *
      W₀ (m + 1) (bandVecM κ (Ioi (δ * L)) (Bands.graphMeasure δ (f : ℝ → Rd m))
        (Bands.graphMeasure δ 0)) ω|) (Finite.bddAbove_range _) ⟨g i, hi⟩)
    simp only
    rw [graphMeasure_eq_bands, graphMeasure_eq_bands]

end HigherDimLFPP.Lower
