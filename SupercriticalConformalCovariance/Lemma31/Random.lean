import SupercriticalConformalCovariance.Domain.Axioms
import SupercriticalConformalCovariance.Lemma31.Retract
import SupercriticalConformalCovariance.Lemma31.Sandwich
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.InternalMetrics.InternalOfInternal
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Lemma 3.1, random statement, repaired form `lem-3.1#repaired`

Paper l. 163–176, in the repaired form
accepted by the orchestrator:

> Fix closed disks `K ⊂ int K′` and a deterministic open `U` with `K ⊂ U ⊂ int K′`. On one
> probability space let `g_n, g` be whole-plane GFFs plus continuous functions. Assume
> `P[g_n|_U = g|_U] → 1`. Let `f_n, f` be random continuous functions on `K′` with
> `‖f_n − f‖_{C(K′)} → 0` in probability. Then the intrinsic metrics on `K` of `g_n + f_n` converge
> in probability, in the epigraph topology on `ℂ²` (∞ outside `K × K`), jointly with the restrictions
> to `U` of the fields, to the intrinsic metric on `K` and the restriction for `g + f`.

The intrinsic metric on `K` of `g + f` (`f ∈ C(K′)`) is `SupercriticalConformalCovariance.Domain.confined ξ (D g) hKK' f`:
`(e^{ξ f}·D_g)(x, y; K)` for `x, y ∈ K` (candidate `weylScaleOn`, curves in `K`), `∞` otherwise.
Convergence in probability is stated in subsequence form, as the frozen
`SupercriticalLQGUniqueness.LSCTendstoInProbability` (DG l. 326; ruling RN-3): every subsequence has
a further subsequence along which, almost surely, the confined metrics converge in the sense of DG
Definition 1.2 **and** the restricted fields are eventually equal to the limit's (stronger than
convergence of `g_n|_U` in any topology).

Route (paper l. 170–176):
1. one locality functional on `U` for the countably many fields `g_n + F`, `g + F` (coin mixture,
   `SupercriticalConformalCovariance.Domain.universalLocality_lsc`), where `F` is the radial extension of `f|_K` (measurable);
2. on `{g_n|_U = g|_U}` the internal metrics on `U` of `D_{g_n+F}`, `D_{g+F}` agree, hence those on
   `K` (`internal_eq_of_internal_eq`), hence the `K`-metrics with weight `f|_K`
   (`SupercriticalConformalCovariance.Domain.ae_weylScaleOn_eq_internal`);
3. domain Weyl bounds (`weylScaleOn_add_le`, `le_weylScaleOn_add`) give the sandwich
   `e^{−ξ s_n} d ≤ d_n ≤ e^{ξ s_n} d`, `s_n = ‖f_n − f‖_{C(K)}`, also where `d = ∞`;
4. lower semicontinuity of `d` (closed-disk path infimum, `SupercriticalConformalCovariance.Compact.closed_disk_intrinsic_lsc`);
5. the subsequence criterion (Mathlib `TendstoInMeasure.exists_seq_tendsto_ae`, twice) and the
   eventual sandwich lemma.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set TopologicalSpace Metric
open scoped ENNReal

namespace SupercriticalConformalCovariance.Lemma31

open LQGMetric (DistC DistOn restrictTo IsGFFPlusCont addFun ofCont)
open SupercriticalLQGUniqueness (LSCMetric IsStrongLQGMetric LSCTendsto)
open SupercriticalConformalCovariance (weylScaleOn)
open SupercriticalConformalCovariance.Domain (confined resC universalLocality_lsc ae_weylScaleOn_eq_internal
  isGFFPlusCont_addFun_of_measurable weylScaleOn_add_le le_weylScaleOn_add)

/-! ## The confined metric as a closed-disk path infimum -/

/-- On a sample where the domain metrics are the internal metrics of Weyl-scaled whole-plane
metrics (the event of `ae_weylScaleOn_eq_internal`), the confined metric on `K = closedBall c R` of
`f ∈ C(K′)` is the closed-disk path infimum of `D_{h + F}`, `F` the radial extension of `f|_K`. -/
theorem confined_eq_closedBallPathInf {ξ : ℝ} {D : DistC → LSCMetric} {x : DistC}
    (hx : ∀ (K : Set ℂ) (f : C(K, ℝ)) (F : C(ℂ, ℝ)), (∀ z (hz : z ∈ K), F z = f ⟨z, hz⟩) →
      ∀ p : K × K, weylScaleOn ξ f (D x) p = (D (addFun x F)).internal K p)
    (c : ℂ) {R : ℝ} (hR : 0 < R) {K' : Set ℂ} (hKK' : closedBall c R ⊆ K') (f : C(K', ℝ)) :
    confined ξ (D x) hKK' f = fun q =>
      SupercriticalLQGUniqueness.Uniqueness.Toolkit.MovingEndpoints.closedBallPathInf
        (D (addFun x (diskExt c hR (resC hKK' f)))) c R q.1 q.2 := by
  funext q
  unfold confined
  split_ifs with hq
  · rw [hx _ (resC hKK' f) (diskExt c hR (resC hKK' f)) (fun z hz => diskExt_eq c hR _ z hz)]
    rfl
  · symm
    refine eq_top_iff.2 (le_iInf fun P => le_iInf fun a => le_iInf fun b => le_iInf fun hP =>
      le_iInf fun hK => le_iInf fun ha => le_iInf fun hb => ?_)
    exfalso
    refine hq ⟨?_, ?_⟩
    · rw [← ha]; exact hK a (left_mem_Icc.2 hP.1)
    · rw [← hb]; exact hK b (right_mem_Icc.2 hP.1)

/-- **Lower semicontinuity** (paper l. 174–175, via Lemma 1.2): a.s., for every `f ∈ C(K′)`, the
confined metric on the closed disk is lower semicontinuous on `ℂ × ℂ`, values `∞` included. -/
theorem ae_confined_lsc_disk {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}
    (hD : IsStrongLQGMetric ξ Q D) (c : ℂ) {R : ℝ} (hR : 0 < R) {K' : Set ℂ}
    (hKK' : closedBall c R ⊆ K') {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsGFFPlusCont h P) :
    ∀ᵐ ω ∂P, ∀ f : C(K', ℝ), LowerSemicontinuous (confined (ξ : ℝ) (D (h ω)) hKK' f) := by
  filter_upwards [ae_weylScaleOn_eq_internal hD P hh] with ω hω f
  rw [confined_eq_closedBallPathInf hω c hR hKK' f]
  exact SupercriticalConformalCovariance.Compact.closed_disk_intrinsic_lsc _ c R

/-! ## The samplewise sandwich -/

/-- The sup distance on `K = closedBall c R` of two functions on `K′ ⊇ K`. -/
def supDistK (c : ℂ) (R : ℝ) {K' : Set ℂ} (hKK' : closedBall c R ⊆ K') (f₁ f₂ : C(K', ℝ)) : ℝ :=
  ‖resC hKK' f₁ - resC hKK' f₂‖

/-- **Samplewise multiplicative sandwich** (paper l. 170–173). On a sample where (a) one functional
`Φ` gives the internal metrics on `U` of `D_{g₁+F}` and `D_{g₂+F}` from the restrictions to `U`,
(b) both `D_{g₁}`, `D_{g₂}` satisfy the consistency of `ae_weylScaleOn_eq_internal`, and
(c) `g₁|_U = g₂|_U`, the confined metrics of `g₁ + f₁` and `g₂ + f₂` on `K ⊆ U` satisfy
`e^{−ξ s} d₂ ≤ d₁ ≤ e^{ξ s} d₂` on all of `ℂ × ℂ`, `s = ‖f₁ − f₂‖_{C(K)}`; here `F` is the radial
extension of `f₂|_K`. -/
theorem confined_sandwich {ξ : ℝ} (hξ : 0 ≤ ξ) {D : DistC → LSCMetric} (c : ℂ) {R : ℝ}
    (hR : 0 < R) {K' : Set ℂ} (hKK' : closedBall c R ⊆ K') (U : Opens ℂ)
    (hKU : closedBall c R ⊆ U) {g₁ g₂ : DistC} (f₁ f₂ : C(K', ℝ))
    (Φ : DistOn U → (↥(U : Set ℂ) × ↥(U : Set ℂ) → ℝ≥0∞))
    (hΦ₁ : (D (addFun g₁ (diskExt c hR (resC hKK' f₂)))).internal (U : Set ℂ) =
      Φ (restrictTo U (addFun g₁ (diskExt c hR (resC hKK' f₂)))))
    (hΦ₂ : (D (addFun g₂ (diskExt c hR (resC hKK' f₂)))).internal (U : Set ℂ) =
      Φ (restrictTo U (addFun g₂ (diskExt c hR (resC hKK' f₂)))))
    (hW₁ : ∀ (K : Set ℂ) (f : C(K, ℝ)) (F : C(ℂ, ℝ)), (∀ z (hz : z ∈ K), F z = f ⟨z, hz⟩) →
      ∀ p : K × K, weylScaleOn ξ f (D g₁) p = (D (addFun g₁ F)).internal K p)
    (hW₂ : ∀ (K : Set ℂ) (f : C(K, ℝ)) (F : C(ℂ, ℝ)), (∀ z (hz : z ∈ K), F z = f ⟨z, hz⟩) →
      ∀ p : K × K, weylScaleOn ξ f (D g₂) p = (D (addFun g₂ F)).internal K p)
    (hU : restrictTo U g₁ = restrictTo U g₂) (q : ℂ × ℂ) :
    ENNReal.ofReal (Real.exp (ξ * -supDistK c R hKK' f₁ f₂)) * confined ξ (D g₂) hKK' f₂ q ≤
        confined ξ (D g₁) hKK' f₁ q ∧
      confined ξ (D g₁) hKK' f₁ q ≤
        ENNReal.ofReal (Real.exp (ξ * supDistK c R hKK' f₁ f₂)) * confined ξ (D g₂) hKK' f₂ q := by
  set F := diskExt c hR (resC hKK' f₂) with hFdef
  have hext : ∀ z (hz : z ∈ closedBall c R), F z = resC hKK' f₂ ⟨z, hz⟩ :=
    fun z hz => diskExt_eq c hR _ z hz
  -- locality on `U`, then on `K`
  have hres : restrictTo U (addFun g₁ F) = restrictTo U (addFun g₂ F) := by
    ext φ
    have e := congrArg (fun T : DistOn U => T φ) hU
    show (g₁ + ofCont F) _ = (g₂ + ofCont F) _
    rw [add_apply, add_apply]
    exact congrArg (· + _) e
  have hint : (D (addFun g₁ F)).internal (U : Set ℂ) = (D (addFun g₂ F)).internal (U : Set ℂ) := by
    rw [hΦ₁, hΦ₂, hres]
  have hK : (D (addFun g₁ F)).internal (closedBall c R) =
      (D (addFun g₂ F)).internal (closedBall c R) :=
    SupercriticalLQGUniqueness.Uniqueness.Toolkit.InternalMetrics.internal_eq_of_internal_eq
      _ _ hKU hint
  set s := supDistK c R hKK' f₁ f₂ with hsdef
  have hb0 : ENNReal.ofReal (Real.exp (ξ * s)) ≠ 0 := (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  unfold confined
  split_ifs with hq
  · set p : closedBall c R × closedBall c R := (⟨q.1, hq.1⟩, ⟨q.2, hq.2⟩)
    have e1 : weylScaleOn ξ (resC hKK' f₂) (D g₁) p = weylScaleOn ξ (resC hKK' f₂) (D g₂) p := by
      rw [hW₁ _ _ F hext p, hW₂ _ _ F hext p, hK]
    have hdec : resC hKK' f₁ = resC hKK' f₂ + (resC hKK' f₁ - resC hKK' f₂) :=
      (add_sub_cancel _ _).symm
    have hbd : ∀ z, |(resC hKK' f₁ - resC hKK' f₂) z| ≤ s := fun z => by
      have := ContinuousMap.norm_coe_le_norm (resC hKK' f₁ - resC hKK' f₂) z
      rwa [Real.norm_eq_abs] at this
    rw [hdec, ← e1]
    exact ⟨le_weylScaleOn_add hξ _ _ (fun z => (abs_le.1 (hbd z)).1) p,
      weylScaleOn_add_le hξ _ _ (fun z => (le_abs_self _).trans (hbd z)) p⟩
  · exact ⟨le_top, by rw [ENNReal.mul_top hb0]⟩

/-! ## Convergence in measure helpers -/

theorem tendstoInMeasure_of_abs {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : ℕ → Ω → ℝ}
    (h : ∀ ε : ℝ, 0 < ε → Tendsto (fun n => P {ω | ε ≤ |X n ω|}) atTop (𝓝 0)) :
    TendstoInMeasure P X atTop (fun _ => 0) := by
  intro ε hε
  by_cases hεtop : ε = ⊤
  · have : ∀ n, {ω | ε ≤ edist (X n ω) 0} = ∅ := fun n => by
      ext ω
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, hεtop, top_le_iff]
      exact edist_ne_top _ _
    simp only [this, measure_empty]
    exact tendsto_const_nhds
  · have : ∀ n, {ω | ε ≤ edist (X n ω) 0} = {ω | ε.toReal ≤ |X n ω|} := fun n => by
      ext ω
      simp only [mem_ofPred_eq]
      rw [edist_dist, Real.dist_eq, sub_zero, ENNReal.le_ofReal_iff_toReal_le hεtop (abs_nonneg _)]
    simp only [this]
    exact h _ (ENNReal.toReal_pos hε.ne' hεtop)

/-! ## Lemma 3.1, random form -/

/-- **Lemma 3.1, core form with coupling events.** As `confinedConvergence_subseq`, with the
coupling given by events `E n`: `P (E n)ᶜ → 0`, and a.s., for every `n`, `ω ∈ E n` implies
`g_n|_U = g∞|_U`. Conclusion: every subsequence has a further subsequence along which, a.s., the
confined metrics converge (DG Definition 1.2) and `ω ∈ E n` eventually. -/
theorem confinedConvergence_subseq_of_events {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ}
    {D : DistC → LSCMetric} (hD : IsStrongLQGMetric ξ Q D) (c : ℂ) {R : ℝ} (hR : 0 < R)
    {K' : Set ℂ} (hKK' : closedBall c R ⊆ K') (U : Opens ℂ) (hKU : closedBall c R ⊆ U)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (g : ℕ → Ω → DistC) (gL : Ω → DistC) (hg : ∀ n, IsGFFPlusCont (g n) P)
    (hgL : IsGFFPlusCont gL P) (f : ℕ → Ω → C(K', ℝ)) (fL : Ω → C(K', ℝ))
    (hfL : Measurable fL) (E : ℕ → Set Ω)
    (hE : Tendsto (fun n => P (E n)ᶜ) atTop (𝓝 0))
    (hEU : ∀ᵐ ω ∂P, ∀ n, ω ∈ E n → restrictTo U (g n ω) = restrictTo U (gL ω))
    (hconv : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => P {ω | ∃ x : K', ε < |f n ω x - fL ω x|}) atTop (𝓝 0)) :
    ∀ ns : ℕ → ℕ, StrictMono ns → ∃ ms : ℕ → ℕ, StrictMono ms ∧ ∀ᵐ ω ∂P,
      LSCTendsto
        (fun k q => (confined (ξ : ℝ) (D (g (ns (ms k)) ω)) hKK' (f (ns (ms k)) ω) q : EReal))
        (fun q => (confined (ξ : ℝ) (D (gL ω)) hKK' (fL ω) q : EReal)) ∧
      ∀ᶠ k in atTop, ω ∈ E (ns (ms k)) := by
  intro ns hns
  -- the common correction `F = ext (fL|_K)` and the countable family of fields
  set F : Ω → C(ℂ, ℝ) := fun ω => diskExt c hR (resC hKK' (fL ω)) with hFdef
  have hFm : Measurable F :=
    (measurable_diskExt c hR).comp ((ContinuousMap.continuous_precomp _).measurable.comp hfL)
  set G : Option ℕ → Ω → DistC := fun i ω => addFun (i.elim (gL ω) fun n => g n ω) (F ω)
    with hGdef
  have hG : ∀ i, IsGFFPlusCont (G i) P := by
    rintro (_ | n)
    · exact isGFFPlusCont_addFun_of_measurable hgL hFm
    · exact isGFFPlusCont_addFun_of_measurable (hg n) hFm
  obtain ⟨Φ, -, hΦ⟩ := universalLocality_lsc hD U (Option ℕ) (fun _ => Ω) (fun _ => P) G hG
  -- the samplewise sandwich on the coupling events
  set s : ℕ → Ω → ℝ := fun n ω => supDistK c R hKK' (f n ω) (fL ω) with hsdef
  have key : ∀ᵐ ω ∂P, ∀ n, ω ∈ E n → ∀ q,
      ENNReal.ofReal (Real.exp (ξ * -s n ω)) * confined (ξ : ℝ) (D (gL ω)) hKK' (fL ω) q ≤
          confined (ξ : ℝ) (D (g n ω)) hKK' (f n ω) q ∧
        confined (ξ : ℝ) (D (g n ω)) hKK' (f n ω) q ≤
          ENNReal.ofReal (Real.exp (ξ * s n ω)) * confined (ξ : ℝ) (D (gL ω)) hKK' (fL ω) q := by
    filter_upwards [ae_all_iff.2 hΦ, ae_weylScaleOn_eq_internal hD P hgL,
      ae_all_iff.2 fun n => ae_weylScaleOn_eq_internal hD P (hg n), hEU]
      with ω hΦω hWL hWn hEω n hn q
    exact confined_sandwich (le_of_lt ξ.2) c hR hKK' U hKU (f n ω) (fL ω) Φ (hΦω (some n))
      (hΦω none) (hWn n) hWL (hEω n hn) q
  -- first subsequence: `s → 0` a.s.
  have hs : TendstoInMeasure P (fun k => s (ns k)) atTop (fun _ => 0) := by
    refine tendstoInMeasure_of_abs fun ε hε => ?_
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      ((hconv (ε / 2) (half_pos hε)).comp hns.tendsto_atTop) (fun _ => zero_le) fun k => ?_
    refine measure_mono fun ω hω => ?_
    simp only [mem_ofPred_eq] at hω ⊢
    by_contra hall
    push Not at hall
    have hle : supDistK c R hKK' (f (ns k) ω) (fL ω) ≤ ε / 2 := by
      refine (ContinuousMap.norm_le _ (half_pos hε).le).2 fun z => ?_
      rw [Real.norm_eq_abs]
      exact hall _
    have h0 : 0 ≤ supDistK c R hKK' (f (ns k) ω) (fL ω) := norm_nonneg _
    have : |s (ns k) ω| = supDistK c R hKK' (f (ns k) ω) (fL ω) := abs_of_nonneg h0
    linarith
  obtain ⟨ms₁, hms₁, hae₁⟩ := hs.exists_seq_tendsto_ae
  -- second subsequence: eventually in the coupling events, a.s.
  have hind : TendstoInMeasure P
      (fun k ω => (E (ns (ms₁ k)))ᶜ.indicator (fun _ => (1 : ℝ)) ω) atTop (fun _ => 0) := by
    refine tendstoInMeasure_of_abs fun ε hε => ?_
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (hE.comp (hns.comp hms₁).tendsto_atTop) (fun _ => zero_le) fun k => ?_
    refine measure_mono fun ω hω => ?_
    by_contra hω'
    have : (E (ns (ms₁ k)))ᶜ.indicator (fun _ => (1 : ℝ)) ω = 0 :=
      Set.indicator_of_notMem hω' _
    simp only [mem_ofPred_eq, this, abs_zero] at hω
    linarith
  obtain ⟨ms₂, hms₂, hae₂⟩ := hind.exists_seq_tendsto_ae
  refine ⟨ms₁ ∘ ms₂, hms₁.comp hms₂, ?_⟩
  filter_upwards [hae₁, hae₂, key, ae_confined_lsc_disk hD c hR hKK' P hgL] with ω h1 h2 hk hl
  have h1' : Tendsto (fun k => s (ns (ms₁ (ms₂ k))) ω) atTop (𝓝 0) :=
    h1.comp hms₂.tendsto_atTop
  have hEk : ∀ᶠ k in atTop, ω ∈ E (ns (ms₁ (ms₂ k))) := by
    filter_upwards [h2.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with k hk'
    by_contra hne
    have : (E (ns (ms₁ (ms₂ k))))ᶜ.indicator (fun _ => (1 : ℝ)) ω = 1 :=
      Set.indicator_of_mem hne _
    simp only [this] at hk'
    norm_num at hk'
  refine ⟨?_, hEk⟩
  have hcont : ∀ t : ℝ, Continuous fun x : ℝ => ENNReal.ofReal (Real.exp (ξ * (t * x))) :=
    fun t => ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp
      (continuous_const.mul (continuous_const.mul continuous_id)))
  have hlim : ∀ t : ℝ, Tendsto (fun k => ENNReal.ofReal (Real.exp (ξ * (t * s (ns (ms₁ (ms₂ k))) ω))))
      atTop (𝓝 1) := fun t => by
    have := ((hcont t).tendsto 0).comp h1'
    simp only [mul_zero, Real.exp_zero, ENNReal.ofReal_one] at this
    exact this
  refine lscTendsto_of_eventually_multiplicative_sandwich _ (hl (fL ω)) _
    (fun k => ENNReal.ofReal (Real.exp (ξ * -s (ns (ms₁ (ms₂ k))) ω)))
    (fun k => ENNReal.ofReal (Real.exp (ξ * s (ns (ms₁ (ms₂ k))) ω)))
    (by simpa using hlim (-1)) (by simpa using hlim 1) ?_
  filter_upwards [hEk] with k hk'
  exact hk (ns (ms₁ (ms₂ k))) hk'

/-- **Lemma 3.1 (paper l. 163–176), repaired form `lem-3.1#repaired`, subsequence form of convergence in
probability.**

Data: a strong LQG metric `D` (`IsStrongLQGMetric ξ Q D`); a closed disk `K = closedBall c R`
(`R > 0`); a set `K′ ⊇ K` carrying the corrections; a deterministic open `U ⊇ K`; on one probability
space whole-plane GFFs plus continuous functions `g n`, `gL`; random continuous functions `f n`, `fL`
on `K′` (only `fL` needs to be measurable).
Hypotheses: `P[g_n|_U ≠ gL|_U] → 0`, and `sup_{K′} |f_n − fL| → 0` in probability.
Conclusion: every subsequence `ns` has a further subsequence `ms` such that almost surely
* the intrinsic metrics on `K` of `g_{ns(ms k)} + f_{ns(ms k)}` (∞ off `K × K`) converge, in the
  epigraph sense of DG Definition 1.2 on `ℂ × ℂ`, to the intrinsic metric on `K` of `gL + fL`; and
* `g_{ns(ms k)}|_U = gL|_U` for all large `k`. -/
theorem confinedConvergence_subseq {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ} {D : DistC → LSCMetric}
    (hD : IsStrongLQGMetric ξ Q D) (c : ℂ) {R : ℝ} (hR : 0 < R) {K' : Set ℂ}
    (hKK' : closedBall c R ⊆ K') (U : Opens ℂ) (hKU : closedBall c R ⊆ U)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (g : ℕ → Ω → DistC) (gL : Ω → DistC) (hg : ∀ n, IsGFFPlusCont (g n) P)
    (hgL : IsGFFPlusCont gL P) (f : ℕ → Ω → C(K', ℝ)) (fL : Ω → C(K', ℝ))
    (hfL : Measurable fL)
    (hcoup : Tendsto (fun n => P {ω | restrictTo U (g n ω) ≠ restrictTo U (gL ω)}) atTop (𝓝 0))
    (hconv : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => P {ω | ∃ x : K', ε < |f n ω x - fL ω x|}) atTop (𝓝 0)) :
    ∀ ns : ℕ → ℕ, StrictMono ns → ∃ ms : ℕ → ℕ, StrictMono ms ∧ ∀ᵐ ω ∂P,
      LSCTendsto
        (fun k q => (confined (ξ : ℝ) (D (g (ns (ms k)) ω)) hKK' (f (ns (ms k)) ω) q : EReal))
        (fun q => (confined (ξ : ℝ) (D (gL ω)) hKK' (fL ω) q : EReal)) ∧
      ∀ᶠ k in atTop, restrictTo U (g (ns (ms k)) ω) = restrictTo U (gL ω) :=
  confinedConvergence_subseq_of_events hD c hR hKK' U hKU P g gL hg hgL f fL hfL
    (fun n => {ω | restrictTo U (g n ω) = restrictTo U (gL ω)}) hcoup
    (Eventually.of_forall fun _ _ h => h) hconv

end SupercriticalConformalCovariance.Lemma31
