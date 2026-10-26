import SupercriticalConformalCovariance.GM24.CInf
import SupercriticalConformalCovariance.Univalent.KoebeCore
import SmallGammaGeodesics.CC.LocalPull
import SmallGammaGeodesics.CC.PullbackConv

/-!
# Gwynne–Miller Lemma 2.4, display (2.5)

Source: Gwynne–Miller 1905.00384v2, `coord-change-final.tex` l. 512–545 (Lemma 2.4 `lem-tv-conv`, with
the hypotheses of Lemma 2.3 `lem-field-metric-converge`, l. 498–503): `φ_n : U_n → φ_n(U_n)` conformal,
`φ_n(0) = 0`, `φ_n'(0) → 1/α ≠ 0`, every compact set eventually in `U_n`. Then for every compact `K`,
`h ∘ φ_n⁻¹|_K → h(α ·)|_K` in the distributional sense, from
`(h ∘ φ_n⁻¹, f) = (h, |φ_n'|² (f ∘ φ_n)) → (h, |α|⁻² f(α⁻¹ ·)) = (h(α ·), f)`.

The convergence is **deterministic, for every distribution `h`** (the source's "almost surely" is not
needed): the transported test functions converge in `𝓓_K(ℂ)` for one fixed compact `K`.

* `eventually_closedBall_subset_image`: every compact set lies in `φ_n(U_n)` eventually (Koebe 1/4);
* `confPullFun_tendsto_linPull`: supports in one ball and uniform convergence of every real derivative
  of `|φ_n'|² (f ∘ φ_n)` to that of `|α|⁻² f(α⁻¹ ·)` (`linPull α⁻¹ f`);
* `tendsto_invPullPair`: display (2.5), `(h ∘ φ_n⁻¹, f) → (h(α ·), f)` for every `h : DistC`;
* `tendsto_invPullDist`: the restricted form on any bounded open `O` (`DistOn O`);
* `tendsto_smoothAvg_invPull`: the normalizing constants `(h ∘ φ_n⁻¹)_{𝐟,r}(0) → (h(α ·))_{𝐟,r}(0)`;
* `dilDist_smoothAvg_inv_norm`: `(h(α ·))_{𝐟,1/|α|}(0) = h_{𝐟,1}(0)` for a rotation-invariant `𝐟`, and
  `dilDist_smoothAvg_norm`: the printed `(h(α ·))_{𝐟,|α|}(0)` equals `h_{𝐟,|α|²}(0)` (SOURCE_GAP).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric Function TopologicalSpace
open scoped ContDiff Distributions

namespace SupercriticalConformalCovariance.GM24

open LQGMetric
open SmallGammaGeodesics.CC (confPullFun confPullFun_of_mem confPullFun_eq_zero confPullTest
  coe_confPullTest contDiff_confPullFun confPullOnCLM confPullOnCLM_apply coe_confPullOnCLM linPull
  confPullFun_mul_left)

/-! ## The linear pullback `h(α ·)` -/

theorem differentiableOn_mul_left (a : ℂ) : DifferentiableOn ℂ (fun w : ℂ => a * w) univ :=
  (differentiable_id.const_mul a).differentiableOn

theorem injOn_mul_left {a : ℂ} (ha : a ≠ 0) : InjOn (fun w : ℂ => a * w) univ :=
  fun _ _ _ _ h => mul_left_cancel₀ ha h

theorem image_mul_left_univ {a : ℂ} (ha : a ≠ 0) : (fun w : ℂ => a * w) '' univ = univ :=
  eq_univ_of_forall fun y => ⟨a⁻¹ * y, mem_univ _, by
    show a * (a⁻¹ * y) = y
    rw [← mul_assoc, mul_inv_cancel₀ ha, one_mul]⟩

/-- `f ↦ |a|² f(a ·)` on `𝓓(ℂ)`, the conformal pullback by `w ↦ a w` (`a ≠ 0`). -/
def linPullCLM {a : ℂ} (ha : a ≠ 0) : TestC →L[ℝ] TestC :=
  confPullOnCLM isOpen_univ (differentiableOn_mul_left a) (injOn_mul_left ha) ⊤
    (by rw [image_mul_left_univ ha]; exact subset_univ _)

theorem coe_linPullCLM {a : ℂ} (ha : a ≠ 0) (f : TestC) : ⇑(linPullCLM ha f) = linPull a f := by
  rw [linPullCLM, coe_confPullOnCLM, confPullFun_mul_left]

/-- **`h(α ·)`** for a distribution `h` and `α ≠ 0`: `(h(α ·), f) = (h, |α|⁻² f(α⁻¹ ·))`
(substitution `w = α z`, Jacobian `|α|²`), GM l. 544. -/
def dilDist {α : ℂ} (hα : α ≠ 0) (h : DistC) : DistC := h.comp (linPullCLM (inv_ne_zero hα))

theorem dilDist_apply {α : ℂ} (hα : α ≠ 0) (h : DistC) (f : TestC) :
    dilDist hα h f = h (linPullCLM (inv_ne_zero hα) f) := rfl

/-! ## The field `h ∘ φ⁻¹` -/

/-- The pairing `(h ∘ φ⁻¹, f) = (h, |φ'|² (f ∘ φ))` (GM l. 544) for `φ` holomorphic and injective on
the open set `W` and `f` supported in `φ(W)`; junk value `0` otherwise. -/
def invPullPair (W : Set ℂ) (φ : ℂ → ℂ) (h : DistC) (f : TestC) : ℝ :=
  haveI := Classical.propDecidable
  if H : IsOpen W ∧ DifferentiableOn ℂ φ W ∧ InjOn φ W ∧ tsupport (f : ℂ → ℝ) ⊆ φ '' W then
    h (confPullTest H.1 H.2.1 H.2.2.1 f H.2.2.2)
  else 0

theorem invPullPair_eq {W : Set ℂ} {φ : ℂ → ℂ} (hW : IsOpen W) (hd : DifferentiableOn ℂ φ W)
    (hi : InjOn φ W) (h : DistC) {f : TestC} (hf : tsupport (f : ℂ → ℝ) ⊆ φ '' W) :
    invPullPair W φ h f = h (confPullTest hW hd hi f hf) := by
  rw [invPullPair, dite_eq_left_of_eq_true (eq_true ⟨hW, hd, hi, hf⟩)]

/-- `h ∘ φ⁻¹` restricted to an open `O ⊆ φ(W)`, as a distribution on `O`. -/
def invPullDist {W : Set ℂ} {φ : ℂ → ℂ} (hW : IsOpen W) (hd : DifferentiableOn ℂ φ W)
    (hi : InjOn φ W) (O : Opens ℂ) (hO : (O : Set ℂ) ⊆ φ '' W) (h : DistC) : DistOn O :=
  h.comp (confPullOnCLM hW hd hi O hO)

/-- The restricted distribution pairs with `g ∈ 𝓓(O)` as `invPullPair` with `g` viewed in `𝓓(ℂ)`. -/
theorem invPullDist_apply {W : Set ℂ} {φ : ℂ → ℂ} (hW : IsOpen W) (hd : DifferentiableOn ℂ φ W)
    (hi : InjOn φ W) (O : Opens ℂ) (hO : (O : Set ℂ) ⊆ φ '' W) (h : DistC) (g : TestOn O) :
    invPullDist hW hd hi O hO h g =
      invPullPair W φ h (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := O) (Ω₂ := ⊤) g) := by
  have hcoe : ⇑(TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := O) (Ω₂ := ⊤) g) = ⇑g := by
    rw [TestFunction.monoCLM_apply, ite_cond_eq_true _ _ (eq_true ⟨le_rfl, le_top⟩)]
  have hg : tsupport (⇑(TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := O) (Ω₂ := ⊤) g)) ⊆
      φ '' W := by
    rw [hcoe]; exact (g.tsupport_subset : tsupport (g : ℂ → ℝ) ⊆ O).trans hO
  rw [invPullPair_eq hW hd hi h hg]
  show h (confPullOnCLM hW hd hi O hO g) = _
  congr 1
  ext x
  rw [coe_confPullOnCLM, coe_confPullTest, hcoe]

/-! ## Koebe covering: compact sets are eventually in `φ_n(U_n)` -/

section Seq

variable {U : ℕ → Set ℂ} {φ : ℕ → ℂ → ℂ} {α : ℂ}

theorem eventually_closedBall_subset_image
    (hopen : ∀ n, IsOpen (U n)) (hzeroU : ∀ n, (0 : ℂ) ∈ U n)
    (hexhaust : ∀ K : Set ℂ, IsCompact K → ∀ᶠ n in atTop, K ⊆ U n)
    (hd : ∀ n, DifferentiableOn ℂ (φ n) (U n)) (hinj : ∀ n, InjOn (φ n) (U n))
    (hzero : ∀ n, φ n 0 = 0) (hα : α ≠ 0)
    (hder : Tendsto (fun n => deriv (φ n) 0) atTop (𝓝 α⁻¹)) (ρ : ℝ) :
    ∀ᶠ n in atTop, closedBall (0 : ℂ) ρ ⊆ φ n '' U n := by
  obtain ⟨r, hrpos, hrLarge, hrsub⟩ := SupercriticalConformalCovariance.Univalent.exhaustion_radii hopen hzeroU hexhaust
  set c : ℕ → ℝ := fun n => QuantumZipper.CA.Koebe.koebeCovConst * r n * ‖deriv (φ n) 0‖
  have hnorm : Tendsto (fun n => ‖deriv (φ n) 0‖) atTop (𝓝 ‖α⁻¹‖) := hder.norm
  have hcLarge : Tendsto c atTop atTop := by
    have hprod := (hrLarge.const_mul_atTop QuantumZipper.CA.Koebe.koebeCovConst_pos).atTop_mul_pos
      (norm_pos_iff.2 (inv_ne_zero hα)) hnorm
    exact hprod
  filter_upwards [hcLarge.eventually_gt_atTop ρ] with n hn y hy
  have hk := QuantumZipper.CA.Koebe.ball_subset_image_koebe ((hd n).mono (hrsub n))
    ((hinj n).mono (hrsub n))
  rw [hzero n] at hk
  have hy' : y ∈ ball (0 : ℂ) (c n) := mem_ball.2 ((mem_closedBall.1 hy).trans_lt hn)
  exact image_mono (hrsub n) (hk hy')

/-! ## Convergence of the transported test functions -/

private theorem deriv_mul_left (a w : ℂ) : deriv (fun w : ℂ => a * w) w = a := by simp

theorem tendstoUniformlyOn_of_locally {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {S : ℝ}
    (h : TendstoLocallyUniformlyOn F f atTop (ball 0 S)) :
    ∀ K : Set ℂ, IsCompact K → K ⊆ ball 0 S → TendstoUniformlyOn F f atTop K :=
  fun K hK hKs => (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_ball).1 h K hKs hK

/-- **Test functions converge in `𝓓`** (GM l. 539–543): with `R` fixed, eventually
`|φ_n'|² (f ∘ φ_n)` and `|α|⁻² f(α⁻¹ ·)` vanish off `B̄_R`, and every real derivative converges
uniformly on `ℂ`. -/
theorem confPullFun_tendsto_linPull
    (hopen : ∀ n, IsOpen (U n)) (hzeroU : ∀ n, (0 : ℂ) ∈ U n)
    (hexhaust : ∀ K : Set ℂ, IsCompact K → ∀ᶠ n in atTop, K ⊆ U n)
    (hd : ∀ n, DifferentiableOn ℂ (φ n) (U n)) (hinj : ∀ n, InjOn (φ n) (U n))
    (hzero : ∀ n, φ n 0 = 0) (hα : α ≠ 0)
    (hder : Tendsto (fun n => deriv (φ n) 0) atTop (𝓝 α⁻¹)) (f : TestC) :
    (∀ᶠ n in atTop, tsupport (f : ℂ → ℝ) ⊆ φ n '' U n) ∧
    ∃ R : ℝ, 0 ≤ R ∧ (∀ᶠ n in atTop, ∀ x : ℂ, R < ‖x‖ → confPullFun (φ n) (U n) f x = 0) ∧
      (∀ x : ℂ, R < ‖x‖ → linPull α⁻¹ f x = 0) ∧
      ∀ k : ℕ, TendstoUniformly (fun n => iteratedFDeriv ℝ k (confPullFun (φ n) (U n) f))
        (iteratedFDeriv ℝ k (linPull α⁻¹ f)) atTop := by
  obtain ⟨ρ', hρ'⟩ := f.hasCompactSupport.isCompact.isBounded.subset_closedBall (0 : ℂ)
  set ρ : ℝ := max ρ' 0
  have hρ0 : 0 ≤ ρ := le_max_right _ _
  have hfρ : tsupport (f : ℂ → ℝ) ⊆ closedBall 0 ρ :=
    hρ'.trans (closedBall_subset_closedBall (le_max_left _ _))
  have himg := eventually_closedBall_subset_image hopen hzeroU hexhaust hd hinj hzero hα hder ρ
  have hsupp : ∀ᶠ n in atTop, tsupport (f : ℂ → ℝ) ⊆ φ n '' U n := by
    filter_upwards [himg] with n hn
    exact hfρ.trans hn
  refine ⟨hsupp, ?_⟩
  set R : ℝ := ‖α‖ * ρ + 1
  have hR0 : 0 ≤ R := by positivity
  have hsuppn : ∀ᶠ n in atTop, ∀ x : ℂ, R < ‖x‖ → confPullFun (φ n) (U n) f x = 0 := by
    -- supports of the transported functions, from the convergence of the inverses
    have hinv := (SupercriticalConformalCovariance.Univalent.exhausting_inverse_core hopen hzeroU hexhaust hd hinj hzero hder
      (inv_ne_zero hα)).1
    have hinvK := (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).1 hinv
      (closedBall 0 ρ) (subset_univ _) (isCompact_closedBall 0 ρ)
    filter_upwards [Metric.tendstoUniformlyOn_iff.1 hinvK 1 one_pos] with n hn x hx
    refine confPullFun_eq_zero (fun z hz => (hinj n).leftInvOn_invFunOn hz) ?_
    rintro ⟨y, hy, rfl⟩
    have hyρ : y ∈ closedBall (0 : ℂ) ρ := hfρ hy
    have h1 := hn y hyρ
    rw [inv_inv, dist_eq_norm] at h1
    have h2 : ‖Function.invFunOn (φ n) (U n) y‖ < R := by
      have h3 : ‖Function.invFunOn (φ n) (U n) y‖ ≤ ‖α * y‖ +
          ‖α * y - Function.invFunOn (φ n) (U n) y‖ := by
        have := norm_sub_norm_le (Function.invFunOn (φ n) (U n) y) (α * y)
        rw [norm_sub_rev] at this
        linarith
      have h4 : ‖α * y‖ ≤ ‖α‖ * ρ := by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.1 hyρ) (norm_nonneg _)
      linarith
    linarith
  have hlin : ∀ x : ℂ, R < ‖x‖ → linPull α⁻¹ f x = 0 := by
    intro x hx
    have hpos : 0 < ‖α‖ := norm_pos_iff.2 hα
    have hx' : ρ < ‖α⁻¹ * x‖ := by
      rw [norm_mul, norm_inv, inv_mul_eq_div, lt_div_iff₀ hpos]
      linarith [mul_comm ρ ‖α‖]
    have : (f : ℂ → ℝ) (α⁻¹ * x) = 0 := image_eq_zero_of_notMem_tsupport fun h =>
      (not_le.2 hx') (mem_closedBall_zero_iff.1 (hfρ h))
    rw [linPull, this, mul_zero]
  refine ⟨R, hR0, hsuppn, hlin, ?_⟩
  · -- `C^∞` convergence on the ball `s = B_{R+1}`
    set s : Set ℂ := ball (0 : ℂ) (R + 1)
    have hs : IsOpen s := isOpen_ball
    have hsU : ∀ᶠ n in atTop, s ⊆ U n := by
      filter_upwards [hexhaust (closedBall 0 (R + 1)) (isCompact_closedBall 0 (R + 1))] with n hn
      exact ball_subset_closedBall.trans hn
    set φ₀ : ℂ → ℂ := fun z => α⁻¹ * z
    have hφs : ∀ᶠ n in atTop, DifferentiableOn ℂ (φ n) s := by
      filter_upwards [hsU] with n hn
      exact (hd n).mono hn
    have hφ₀ : DifferentiableOn ℂ φ₀ s := (differentiable_id.const_mul α⁻¹).differentiableOn
    have hiter : ∀ k : ℕ, ∀ K : Set ℂ, IsCompact K → K ⊆ s →
        TendstoUniformlyOn (fun n => iteratedDeriv k (φ n)) (iteratedDeriv k φ₀) atTop K :=
      fun k => tendstoUniformlyOn_of_locally
        (SupercriticalConformalCovariance.Univalent.exhausting_maps_iteratedDeriv_tendsto (R + 1) k hopen hzeroU hexhaust hd
          hinj hzero hder)
    have hc : ∀ k, UConv φ φ₀ s k := fun k => uconv_of_holo hs hφs hφ₀ k (hiter k)
    have hdc : ∀ k, UConv (fun n => deriv (φ n)) (deriv φ₀) s k := by
      intro k
      refine uconv_of_holo hs ?_ (hφ₀.deriv hs) k ?_
      · filter_upwards [hφs] with n hn
        exact hn.deriv hs
      · intro K hK hKs
        simpa only [← iteratedDeriv_succ'] using hiter (k + 1) K hK hKs
    have hreal : ∀ {g : ℂ → ℂ}, DifferentiableOn ℂ g s → ContDiffOn ℝ ∞ g s :=
      fun hg => (hg.contDiffOn hs).restrict_scalars ℝ
    have hJ := uconv_comp hs (by filter_upwards [hφs] with n hn; exact hreal (hn.deriv hs))
      (hreal (hφ₀.deriv hs)) hdc
    have hF := uconv_comp hs (by filter_upwards [hφs] with n hn; exact hreal hn) (hreal hφ₀) hc
    have hfs : ContDiff ℝ ∞ (f : ℂ → ℝ) := f.contDiff
    have hnsq : ContDiff ℝ ∞ (fun z : ℂ => ‖z‖ ^ 2) := contDiff_norm_sq ℝ
    have hprod : ∀ k, UConv (fun n y => ContinuousLinearMap.mul ℝ ℝ
          (((fun z : ℂ => ‖z‖ ^ 2) ∘ deriv (φ n)) y) (((f : ℂ → ℝ) ∘ φ n) y))
        (fun y => ContinuousLinearMap.mul ℝ ℝ (((fun z : ℂ => ‖z‖ ^ 2) ∘ deriv φ₀) y)
          (((f : ℂ → ℝ) ∘ φ₀) y)) s k := by
      intro k
      refine uconv_bilin (ContinuousLinearMap.mul ℝ ℝ) hs ?_ ?_ ?_ ?_ k
        (hJ k _ hnsq) (hF k _ hfs)
      · filter_upwards [hφs] with n hn
        exact hnsq.comp_contDiffOn (hreal (hn.deriv hs))
      · exact hnsq.comp_contDiffOn (hreal (hφ₀.deriv hs))
      · filter_upwards [hφs] with n hn
        exact hfs.comp_contDiffOn (hreal hn)
      · exact hfs.comp_contDiffOn (hreal hφ₀)
    have hconv : ∀ k, UConv (fun n => confPullFun (φ n) (U n) f) (linPull α⁻¹ f) s k := by
      intro k
      refine uconv_congr hs (hprod k) ?_ ?_
      · filter_upwards [hsU] with n hn y hy
        simp only [Function.comp_apply, ContinuousLinearMap.mul_apply']
        rw [confPullFun_of_mem (hn hy)]
      · intro y _
        simp only [Function.comp_apply, ContinuousLinearMap.mul_apply', φ₀, deriv_mul_left, linPull]
    -- off `B̄_R` both functions vanish near each point, hence so do all derivatives
    have hzeroD : ∀ {g : ℂ → ℝ}, (∀ x : ℂ, R < ‖x‖ → g x = 0) → ∀ k : ℕ, ∀ x : ℂ, R < ‖x‖ →
        iteratedFDeriv ℝ k g x = 0 := by
      intro g hg k x hx
      have hopenR : IsOpen {y : ℂ | R < ‖y‖} := isOpen_lt continuous_const continuous_norm
      have he : g =ᶠ[𝓝 x] fun _ => (0 : ℝ) :=
        Filter.eventuallyEq_of_mem (hopenR.mem_nhds hx) fun y hy => hg y hy
      rw [(he.iteratedFDeriv ℝ k).eq_of_nhds, iteratedFDeriv_fun_zero]
      rfl
    intro k
    have hK := hconv k (closedBall 0 R) (isCompact_closedBall 0 R)
      (closedBall_subset_ball (by linarith))
    rw [Metric.tendstoUniformly_iff]
    rw [Metric.tendstoUniformlyOn_iff] at hK
    intro ε hε
    filter_upwards [hK ε hε, hsuppn] with n hn hn' x
    by_cases hx : ‖x‖ ≤ R
    · exact hn x (mem_closedBall_zero_iff.2 hx)
    · push Not at hx
      rw [hzeroD hlin k x hx, hzeroD hn' k x hx, dist_self]
      exact hε

/-! ## Convergence in `𝓓` and display (2.5) -/

/-- Convergence in `𝓓_K` is uniform convergence of every derivative (Mathlib's structure maps). -/
theorem tendsto_supportedIn_of_uniform {K : Compacts ℂ} {G : ℕ → 𝓓^{⊤}_{K}(ℂ, ℝ)}
    {G₀ : 𝓓^{⊤}_{K}(ℂ, ℝ)}
    (h : ∀ i : ℕ, TendstoUniformly (fun n => iteratedFDeriv ℝ i (G n)) (iteratedFDeriv ℝ i G₀)
      atTop) :
    Tendsto G atTop (𝓝 G₀) := by
  have hemb := (ContDiffMapSupportedIn.isUniformEmbedding_pi_structureMapCLM (𝕜 := ℝ) (n := ⊤)
    (K := K) (E := ℂ) (F := ℝ)).isUniformInducing.isInducing
  rw [hemb.tendsto_nhds_iff, tendsto_pi_nhds]
  intro i
  rw [BoundedContinuousFunction.tendsto_iff_tendstoUniformly]
  simpa only [Function.comp_apply, ContinuousLinearMap.pi_apply,
    ContDiffMapSupportedIn.structureMapCLM_top_apply] using h i

/-- A sequence of test functions vanishing off one ball `B̄_R`, with every derivative converging
uniformly, converges in `𝓓(ℂ)`. -/
theorem tendsto_testC_of_uniform {G : ℕ → TestC} {G₀ : TestC} {R : ℝ}
    (hsupp : ∀ᶠ n in atTop, ∀ x : ℂ, R < ‖x‖ → G n x = 0)
    (hsupp₀ : ∀ x : ℂ, R < ‖x‖ → G₀ x = 0)
    (hconv : ∀ k : ℕ, TendstoUniformly (fun n => iteratedFDeriv ℝ k (G n))
      (iteratedFDeriv ℝ k G₀) atTop) :
    Tendsto G atTop (𝓝 G₀) := by
  classical
  let K : Compacts ℂ := ⟨closedBall 0 R, isCompact_closedBall 0 R⟩
  have hcompl : ∀ {g : TestC}, (∀ x : ℂ, R < ‖x‖ → g x = 0) → EqOn g 0 (K : Set ℂ)ᶜ :=
    fun hg x hx => hg x (lt_of_not_ge fun h => hx (mem_closedBall_zero_iff.2 h))
  let toK : (g : TestC) → (∀ x : ℂ, R < ‖x‖ → g x = 0) → 𝓓^{⊤}_{K}(ℂ, ℝ) := fun g hg =>
    { toFun := g
      contDiff' := g.contDiff
      zero_on_compl' := hcompl hg }
  let G' : ℕ → 𝓓^{⊤}_{K}(ℂ, ℝ) := fun n =>
    if H : ∀ x : ℂ, R < ‖x‖ → G n x = 0 then toK (G n) H else 0
  have hG' : ∀ᶠ n in atTop, ⇑(G' n) = ⇑(G n) := by
    filter_upwards [hsupp] with n hn
    simp only [G', dif_pos hn]
    rfl
  have hT : Tendsto G' atTop (𝓝 (toK G₀ hsupp₀)) := by
    refine tendsto_supportedIn_of_uniform fun i => ?_
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    filter_upwards [Metric.tendstoUniformly_iff.1 (hconv i) ε hε, hG'] with n hn hn' x
    rw [hn']
    exact hn x
  have hKU : (K : Set ℂ) ⊆ ((⊤ : Opens ℂ) : Set ℂ) := subset_univ _
  have hc := ((TestFunction.continuous_ofSupportedIn hKU).tendsto _).comp hT
  have e₀ : TestFunction.ofSupportedIn hKU (toK G₀ hsupp₀) = G₀ := by
    ext x; rfl
  rw [e₀] at hc
  refine hc.congr' ?_
  filter_upwards [hG'] with n hn
  ext x
  exact congrFun hn x

variable {U : ℕ → Set ℂ} {φ : ℕ → ℂ → ℂ} {α : ℂ}

/-- **GM Lemma 2.4, display (2.5)**, for every distribution `h`:
`(h ∘ φ_n⁻¹, f) = (h, |φ_n'|² (f ∘ φ_n)) → (h, |α|⁻² f(α⁻¹ ·)) = (h(α ·), f)`. -/
theorem tendsto_invPullPair
    (hopen : ∀ n, IsOpen (U n)) (hzeroU : ∀ n, (0 : ℂ) ∈ U n)
    (hexhaust : ∀ K : Set ℂ, IsCompact K → ∀ᶠ n in atTop, K ⊆ U n)
    (hd : ∀ n, DifferentiableOn ℂ (φ n) (U n)) (hinj : ∀ n, InjOn (φ n) (U n))
    (hzero : ∀ n, φ n 0 = 0) (hα : α ≠ 0)
    (hder : Tendsto (fun n => deriv (φ n) 0) atTop (𝓝 α⁻¹)) (h : DistC) (f : TestC) :
    Tendsto (fun n => invPullPair (U n) (φ n) h f) atTop (𝓝 (dilDist hα h f)) := by
  classical
  obtain ⟨hsupp, R, -, hsn, hlin, hk⟩ :=
    confPullFun_tendsto_linPull hopen hzeroU hexhaust hd hinj hzero hα hder f
  let G : ℕ → TestC := fun n =>
    if H : tsupport (f : ℂ → ℝ) ⊆ φ n '' U n then confPullTest (hopen n) (hd n) (hinj n) f H else 0
  have hG : ∀ᶠ n in atTop, ⇑(G n) = confPullFun (φ n) (U n) f := by
    filter_upwards [hsupp] with n hn
    simp only [G, dif_pos hn, coe_confPullTest]
  have hG₀ : ⇑(linPullCLM (inv_ne_zero hα) f) = linPull α⁻¹ f := coe_linPullCLM _ f
  have hT : Tendsto G atTop (𝓝 (linPullCLM (inv_ne_zero hα) f)) := by
    refine tendsto_testC_of_uniform (R := R) ?_ (by rw [hG₀]; exact hlin) fun k => ?_
    · filter_upwards [hG, hsn] with n hn hn' x hx
      rw [hn]; exact hn' x hx
    · rw [hG₀, Metric.tendstoUniformly_iff]
      intro ε hε
      filter_upwards [Metric.tendstoUniformly_iff.1 (hk k) ε hε, hG] with n hn hn' x
      rw [hn']; exact hn x
  have hc := ((map_continuous h).tendsto _).comp hT
  refine hc.congr' ?_
  filter_upwards [hsupp] with n hn
  simp only [Function.comp_apply, G, dif_pos hn]
  exact (invPullPair_eq (hopen n) (hd n) (hinj n) h hn).symm

open scoped Classical in
/-- **(2.5), restricted form** ("`h ∘ φ_n⁻¹|_K → h(α ·)|_K` in the distributional sense"): for a
bounded open `O`, eventually `O ⊆ φ_n(U_n)`, and the restrictions `(h ∘ φ_n⁻¹)|_O` (`invPullDist`)
converge to `h(α ·)|_O` against every `g ∈ 𝓓(O)`. -/
theorem tendsto_invPullDist
    (hopen : ∀ n, IsOpen (U n)) (hzeroU : ∀ n, (0 : ℂ) ∈ U n)
    (hexhaust : ∀ K : Set ℂ, IsCompact K → ∀ᶠ n in atTop, K ⊆ U n)
    (hd : ∀ n, DifferentiableOn ℂ (φ n) (U n)) (hinj : ∀ n, InjOn (φ n) (U n))
    (hzero : ∀ n, φ n 0 = 0) (hα : α ≠ 0)
    (hder : Tendsto (fun n => deriv (φ n) 0) atTop (𝓝 α⁻¹)) (h : DistC) (O : Opens ℂ)
    (hO : Bornology.IsBounded (O : Set ℂ)) :
    (∀ᶠ n in atTop, (O : Set ℂ) ⊆ φ n '' U n) ∧
    ∀ g : TestOn O, Tendsto (fun n => if hn : (O : Set ℂ) ⊆ φ n '' U n then
        invPullDist (hopen n) (hd n) (hinj n) O hn h g else 0) atTop
      (𝓝 (restrictTo O (dilDist hα h) g)) := by
  obtain ⟨ρ, hρ⟩ := hO.subset_closedBall (0 : ℂ)
  have hsub : ∀ᶠ n in atTop, (O : Set ℂ) ⊆ φ n '' U n := by
    filter_upwards [eventually_closedBall_subset_image hopen hzeroU hexhaust hd hinj hzero hα hder ρ]
      with n hn
    exact hρ.trans hn
  refine ⟨hsub, fun g => ?_⟩
  refine (tendsto_invPullPair hopen hzeroU hexhaust hd hinj hzero hα hder h _).congr' ?_
  filter_upwards [hsub] with n hn
  rw [dif_pos hn, invPullDist_apply]
  rfl

/-! ## The normalizing constants -/

/-- The smooth test function `r⁻² 𝐟(r⁻¹ ·)` (GM (2.1) at `z = 0`, `eqn-smooth-normalize`), `r > 0`. -/
def smoothTest {r : ℝ} (hr : 0 < r) (f : TestC) : TestC :=
  linPullCLM (inv_ne_zero (Complex.ofReal_ne_zero.2 hr.ne')) f

/-- **The smooth average** `h_{𝐟,r}(0) = (h, r⁻² 𝐟(r⁻¹ ·))` (GM l. 452–454). -/
def smoothAvg (h : DistC) (f : TestC) {r : ℝ} (hr : 0 < r) : ℝ := h (smoothTest hr f)

/-- The smooth average of `h ∘ φ⁻¹`: `(h ∘ φ⁻¹)_{𝐟,r}(0) = (h ∘ φ⁻¹, r⁻² 𝐟(r⁻¹ ·))`. -/
def invPullSmoothAvg (W : Set ℂ) (φ : ℂ → ℂ) (h : DistC) (f : TestC) {r : ℝ} (hr : 0 < r) : ℝ :=
  invPullPair W φ h (smoothTest hr f)

/-- **The normalizing constants converge** (deterministically, every `h`, every `r > 0`):
`(h ∘ φ_n⁻¹)_{𝐟,r}(0) → (h(α ·))_{𝐟,r}(0)`. -/
theorem tendsto_invPullSmoothAvg
    (hopen : ∀ n, IsOpen (U n)) (hzeroU : ∀ n, (0 : ℂ) ∈ U n)
    (hexhaust : ∀ K : Set ℂ, IsCompact K → ∀ᶠ n in atTop, K ⊆ U n)
    (hd : ∀ n, DifferentiableOn ℂ (φ n) (U n)) (hinj : ∀ n, InjOn (φ n) (U n))
    (hzero : ∀ n, φ n 0 = 0) (hα : α ≠ 0)
    (hder : Tendsto (fun n => deriv (φ n) 0) atTop (𝓝 α⁻¹)) (h : DistC) (f : TestC) {r : ℝ}
    (hr : 0 < r) :
    Tendsto (fun n => invPullSmoothAvg (U n) (φ n) h f hr) atTop
      (𝓝 (smoothAvg (dilDist hα h) f hr)) :=
  tendsto_invPullPair hopen hzeroU hexhaust hd hinj hzero hα hder h (smoothTest hr f)

/-- For a rotation-invariant `𝐟`, `(h(α ·))_{𝐟,r}(0) = h_{𝐟,r|α|}(0)`. -/
theorem dilDist_smoothAvg {α : ℂ} (hα : α ≠ 0) (h : DistC) {f : TestC}
    (hrot : ∀ u : ℂ, ‖u‖ = 1 → ∀ z : ℂ, f (u * z) = f z) {r : ℝ} (hr : 0 < r) :
    smoothAvg (dilDist hα h) f hr = smoothAvg h f (mul_pos hr (norm_pos_iff.2 hα)) := by
  rw [smoothAvg, smoothAvg, dilDist_apply]
  congr 1
  ext x
  have hn : (0 : ℝ) < ‖α‖ := norm_pos_iff.2 hα
  have hαc : ((‖α‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hn.ne'
  have hrc : ((r : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  simp only [smoothTest, coe_linPullCLM, linPull]
  set u : ℂ := (‖α‖ : ℂ) * α⁻¹ with hu
  have hu1 : ‖u‖ = 1 := by
    rw [hu, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn, norm_inv,
      mul_inv_cancel₀ hn.ne']
  have harg : (r : ℂ)⁻¹ * (α⁻¹ * x) = u * (((r * ‖α‖ : ℝ) : ℂ)⁻¹ * x) := by
    rw [hu]; push_cast; field_simp
  rw [harg, hrot u hu1]
  have hnorm : ‖α⁻¹‖ ^ 2 * ‖((r : ℝ) : ℂ)⁻¹‖ ^ 2 = ‖((r * ‖α‖ : ℝ) : ℂ)⁻¹‖ ^ 2 := by
    simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
      abs_of_pos (mul_pos hr hn)]
    field_simp
  rw [← hnorm]
  ring

/-- **The correct normalization** (SOURCE_GAP repair of GM l. 549–553): for a rotation-invariant `𝐟`,
`(h(α ·))_{𝐟,1/|α|}(0) = h_{𝐟,1}(0)`. So `h(α ·)` is normalized at scale `|α|⁻¹`. -/
theorem dilDist_smoothAvg_inv_norm {α : ℂ} (hα : α ≠ 0) (h : DistC) {f : TestC}
    (hrot : ∀ u : ℂ, ‖u‖ = 1 → ∀ z : ℂ, f (u * z) = f z) :
    smoothAvg (dilDist hα h) f (inv_pos.2 (norm_pos_iff.2 hα)) = smoothAvg h f one_pos := by
  rw [dilDist_smoothAvg hα h hrot]
  congr 1
  exact inv_mul_cancel₀ (norm_pos_iff.2 hα).ne'

/-- **The printed normalization** (GM l. 549: "`h(α ·)` is normalized so that `(h(α ·))_{𝐟,|α|}(0)` is
zero"): in fact `(h(α ·))_{𝐟,|α|}(0) = h_{𝐟,|α|²}(0)`, which is not `h_{𝐟,1}(0)` unless `|α| = 1`. -/
theorem dilDist_smoothAvg_norm {α : ℂ} (hα : α ≠ 0) (h : DistC) {f : TestC}
    (hrot : ∀ u : ℂ, ‖u‖ = 1 → ∀ z : ℂ, f (u * z) = f z) :
    smoothAvg (dilDist hα h) f (norm_pos_iff.2 hα) =
      smoothAvg h f (pow_pos (norm_pos_iff.2 hα) 2) := by
  rw [dilDist_smoothAvg hα h hrot]
  congr 1
  ring

/-- `h_{𝐟,1}(0) = (h, 𝐟)`. -/
theorem smoothAvg_one (h : DistC) (f : TestC) : smoothAvg h f one_pos = h f := by
  rw [smoothAvg]
  congr 1
  ext x
  simp [smoothTest, coe_linPullCLM, linPull]

end Seq

end SupercriticalConformalCovariance.GM24
