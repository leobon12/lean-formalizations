/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCK2Term
import InteractingSLE.Spec.Coupling.ResampleProjCore
import QuantumZipper.Proofs.GFF.K3.MixedM7D2

/-!
# The forward member kernels of `FCK2CapForwardInputs` force null protected events

Packet PROVE-T15-FCKER2. The forward-kernel interface `HasFCK2CapForwardKernel P m S X G` asks that `G` be an almost
sure limit, along the strict upper dyadic times of `τ`, of conditional expectations `P[X | 𝓜 t]`. Besides the first
moment identity `∫_D X = ∫_D G` (`setIntegral_eq_of_fcCapForwardKernel`) this forces the **second moment identity**
`∫_D conj G · X = ∫_D conj G · G` on every censored event `D ⊆ S` (`setIntegral_conj_mul_eq_of_fcCapForwardKernel`):
on each dyadic piece `conj K · X` integrates like `conj K · E[X | 𝓜] = |K|²`.

For the member pairings of `FCK2CapForwardInputs` the limit `G = projFactor V f Ξ · e^{i X(Ξ)}` contains the full field
`X(Ξ)`, not only its conditional mean. Taking `Ξ = 0` and `Ξ = −Δf/2π` (both are instances of the same field), the
two identities give `exp(−‖∇f‖²/2) P(D) = exp(−3‖∇f‖²/2) P(D)`, so every censored event inside the member protected
set is null as soon as `V` carries a function of positive Dirichlet energy
(`measure_eq_zero_of_fcCapForwardInputs`). At capacity `0` the protected set is the whole meeting branch, which is a
retained event: `FCK2CapForwardInputs` forces `P (meetSet d) = 0` (`measure_meetSet_eq_zero_of_fcCapForwardInputs`),
and `FirstContactK2ForwardKernelsStatement` forces every first contact with two nonempty continuations to be null
(`measure_meetSet_eq_zero_of_forwardKernels`). The member identity itself (`HasSafeMembers`) is a first-moment
statement and is not affected; `FCKerLawC` restates the member part of the forward inputs in that form.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal RealInnerProductSpace
open LQGMetric (DistOn TestOn)
open QuantumZipper (chiC)

namespace InteractingSLE.Restart.FCPlumb.FCKerLaw

open LQGMetric LQGMetric.MarkovZB WangWu.ChartConst DomainMarkov DomainMarkov.K2 Coupling LocalSets
open QuantumZipper.K3 QuantumZipper.Thm11Asm

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-! ### The pull-out identity on an event of the conditioning σ-algebra -/

/-- `∫_B g X = ∫_B g E[X | 𝓜]` for a bounded `𝓜`-measurable complex factor `g` and `B ∈ 𝓜`. -/
theorem setIntegral_mul_condExp [IsFiniteMeasure P] {𝓜 : MeasurableSpace Ω} (h𝓜 : 𝓜 ≤ mΩ)
    {X g : Ω → ℂ} (hX : Integrable X P) (hXb : ∀ᵐ ω ∂P, ‖X ω‖ ≤ 1) (hg : StronglyMeasurable[𝓜] g)
    (hgi : Integrable g P) {B : Set Ω} (hB : MeasurableSet[𝓜] B) :
    ∫ ω in B, g ω * X ω ∂P = ∫ ω in B, g ω * P[X | 𝓜] ω ∂P := by
  have : IsFiniteMeasure (P.trim h𝓜) := isFiniteMeasure_trim h𝓜
  have hgX : Integrable (fun ω => g ω * X ω) P := by
    have := hgi.bdd_mul (c := 1) hX.aestronglyMeasurable hXb
    refine this.congr (Eventually.of_forall fun ω => ?_)
    exact mul_comm _ _
  have hpull := condExp_bilin_of_aestronglyMeasurable_left (ContinuousLinearMap.mul ℝ ℂ)
    hg.aestronglyMeasurable (f := g) (g := X) (μ := P) (m := 𝓜)
    (by simpa only [ContinuousLinearMap.mul_apply'] using hgX) hX
  simp only [ContinuousLinearMap.mul_apply'] at hpull
  rw [← setIntegral_condExp h𝓜 hgX hB]
  exact setIntegral_congr_ae (h𝓜 _ hB) (by filter_upwards [hpull] with ω hω _ using hω)

/-! ### The second moment identity of the forward-kernel interface -/

/-- **Second moment identity of a forward kernel.** If `HasFCK2CapForwardKernel P m S X G` and `‖X‖ ≤ 1`, then
`∫_D conj G · X = ∫_D conj G · G` for every `m`-event `D` inside `S`. -/
theorem setIntegral_conj_mul_eq_of_fcCapForwardKernel [IsFiniteMeasure P]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {S : Set Ω} {X G : Ω → ℂ}
    (hX : Integrable X P) (hXb : ∀ᵐ ω ∂P, ‖X ω‖ ≤ 1)
    (h : HasFCK2CapForwardKernel (mΩ := mΩ) P m S X G) {D : Set Ω}
    (hD : MeasurableSet[m] D) (hs : ∀ᵐ ω ∂P, ω ∈ D → ω ∈ S) :
    ∫ ω in D, starRingEnd ℂ (G ω) * X ω ∂P = ∫ ω in D, starRingEnd ℂ (G ω) * G ω ∂P := by
  classical
  let _ : MeasurableSpace Ω := mΩ
  obtain ⟨𝓜, Av, K, τ, h𝓜, hτ, hKb, hdet, hread, hlim⟩ := h
  have hDm : MeasurableSet D := hm _ hD
  have hlimD : ∀ᵐ ω ∂P, ω ∈ D → (∀ᶠ n in atTop, ω ∈ Av (dyF n (τ ω))) ∧
      Tendsto (fun n => K (dyF n (τ ω)) ω) atTop (𝓝 (G ω)) := by
    filter_upwards [hs, hlim] with ω hsω hl hωD using hl (hsω hωD)
  have hmeas := hread D hD hs
  have hidx : ∀ n, Measurable fun ω => dyIdx n (τ ω) := fun n => (measurable_dyIdx n).comp hτ
  set Dk : ℕ → ℕ → Set Ω := fun n k => D ∩ {ω | dyIdx n (τ ω) = k} ∩ Av (dyq n k) with hDk_def
  have hDk : ∀ n k, NullMeasurableSet (Dk n k) P := fun n k => by
    obtain ⟨B, hBm, hBeq⟩ := hmeas n k
    exact (h𝓜 _ _ hBm).nullMeasurableSet.congr hBeq
  set Dn : ℕ → Set Ω := fun n => ⋃ k, Dk n k with hDn_def
  have hDn : ∀ n, NullMeasurableSet (Dn n) P := fun n => NullMeasurableSet.iUnion (hDk n)
  have hmemDn : ∀ n ω, ω ∈ Dn n ↔ ω ∈ D ∧ ω ∈ Av (dyF n (τ ω)) := fun n ω => by
    simp only [hDn_def, hDk_def, mem_iUnion, mem_inter_iff, mem_ofPred_eq, dyF]
    constructor
    · rintro ⟨k, ⟨hD', rfl⟩, hA⟩
      exact ⟨hD', hA⟩
    · rintro ⟨hD', hA⟩
      exact ⟨_, ⟨hD', rfl⟩, hA⟩
  have hdisj : ∀ n, Pairwise (Function.onFun (AEDisjoint P) (Dk n)) := fun n k l hkl => by
    refine Disjoint.aedisjoint (Set.disjoint_left.2 fun ω hk hl => hkl ?_)
    exact hk.1.2.symm.trans hl.1.2
  obtain ⟨C, hC_def⟩ : ∃ C : ℕ → ℕ → Ω → ℂ, C = fun n k => P[X | 𝓜 (dyq n k)] := ⟨_, rfl⟩
  have hCs : ∀ n k, StronglyMeasurable[𝓜 (dyq n k)] (C n k) := fun n k => by
    rw [hC_def]
    exact stronglyMeasurable_condExp
  have hCm : ∀ n k, Measurable (C n k) := fun n k => ((hCs n k).mono (h𝓜 _)).measurable
  obtain ⟨f, hf_def⟩ : ∃ f : ℕ → Ω → ℂ, f = fun n ω => C n (dyIdx n (τ ω)) ω := ⟨_, rfl⟩
  have hfm : ∀ n, Measurable (f n) := fun n => by
    have h' := measurable_from_prod_countable_left (f := fun p : Ω × ℕ => C n p.2 p.1)
      (fun k => hCm n k)
    rw [hf_def]
    exact h'.comp (measurable_id.prodMk (hidx n))
  have hall : ∀ᵐ ω ∂P, ∀ n k, ω ∈ Av (dyq n k) → C n k ω = K (dyq n k) ω := by
    rw [hC_def]
    exact ae_all_iff.2 fun n => ae_all_iff.2 fun k => hdet (dyq n k)
  have hZF : ∀ᵐ ω ∂P, ∀ n, ω ∈ Dn n → f n ω = K (dyF n (τ ω)) ω := by
    filter_upwards [hall] with ω hω n hn
    rw [hf_def]
    exact hω n _ ((hmemDn n ω).1 hn).2
  have hfb : ∀ᵐ ω ∂P, ∀ n, ω ∈ Dn n → ‖f n ω‖ ≤ 1 := by
    filter_upwards [hZF] with ω hω n hn
    rw [hω n hn]
    exact hKb _ _ ((hmemDn n ω).1 hn).2
  -- the two integrands
  set g₁ : ℕ → Ω → ℂ := fun n ω => starRingEnd ℂ (f n ω) * X ω with hg₁_def
  set g₂ : ℕ → Ω → ℂ := fun n ω => starRingEnd ℂ (f n ω) * f n ω with hg₂_def
  have hcm : ∀ n, Measurable fun ω => starRingEnd ℂ (f n ω) := fun n =>
    Complex.continuous_conj.measurable.comp (hfm n)
  have hg₁m : ∀ n, AEStronglyMeasurable (g₁ n) P := fun n =>
    (hcm n).aestronglyMeasurable.mul hX.aestronglyMeasurable
  have hg₂m : ∀ n, AEStronglyMeasurable (g₂ n) P := fun n =>
    (hcm n).aestronglyMeasurable.mul (hfm n).aestronglyMeasurable
  have hg₁b : ∀ᵐ ω ∂P, ∀ n, ω ∈ Dn n → ‖g₁ n ω‖ ≤ 1 := by
    filter_upwards [hfb, hXb] with ω hω hXω n hn
    simp only [hg₁_def, norm_mul, Complex.norm_conj]
    calc ‖f n ω‖ * ‖X ω‖ ≤ 1 * 1 := mul_le_mul (hω n hn) hXω (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hg₂b : ∀ᵐ ω ∂P, ∀ n, ω ∈ Dn n → ‖g₂ n ω‖ ≤ 1 := by
    filter_upwards [hfb] with ω hω n hn
    simp only [hg₂_def, norm_mul, Complex.norm_conj]
    calc ‖f n ω‖ * ‖f n ω‖ ≤ 1 * 1 := mul_le_mul (hω n hn) (hω n hn) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hion : ∀ n (g : Ω → ℂ), AEStronglyMeasurable g P → (∀ᵐ ω ∂P, ω ∈ Dn n → ‖g ω‖ ≤ 1) →
      IntegrableOn g (Dn n) P := fun n g hgm hgb => by
    refine Integrable.of_bound hgm.restrict 1 ?_
    rw [ae_restrict_iff'₀ (hDn n)]
    exact hgb
  -- step (a): the identity on the pieces and on their union
  have hpiece : ∀ n k, ∫ ω in Dk n k, g₁ n ω ∂P = ∫ ω in Dk n k, g₂ n ω ∂P := by
    intro n k
    obtain ⟨B, hBm, hBeq⟩ := hmeas n k
    have e₁ : ∫ ω in Dk n k, g₁ n ω ∂P = ∫ ω in Dk n k, starRingEnd ℂ (C n k ω) * X ω ∂P :=
      setIntegral_congr_fun₀ (hDk n k) fun ω hω => by
        simp only [hg₁_def, hf_def]
        rw [hω.1.2]
    have e₂ : ∫ ω in Dk n k, g₂ n ω ∂P = ∫ ω in Dk n k, starRingEnd ℂ (C n k ω) * C n k ω ∂P :=
      setIntegral_congr_fun₀ (hDk n k) fun ω hω => by
        simp only [hg₂_def, hf_def]
        rw [hω.1.2]
    have hconj : StronglyMeasurable[𝓜 (dyq n k)] fun ω => starRingEnd ℂ (C n k ω) :=
      Complex.continuous_conj.comp_stronglyMeasurable (hCs n k)
    have hCi : Integrable (C n k) P := by
      rw [hC_def]
      exact integrable_condExp
    have hconji : Integrable (fun ω => starRingEnd ℂ (C n k ω)) P :=
      hCi.mono (hconj.mono (h𝓜 _)).aestronglyMeasurable
        (Eventually.of_forall fun ω => by rw [Complex.norm_conj])
    rw [e₁, e₂, ← setIntegral_congr_set hBeq, ← setIntegral_congr_set hBeq]
    have hpull := setIntegral_mul_condExp (h𝓜 (dyq n k)) hX hXb hconj hconji hBm
    rw [hpull, hC_def]
  have hunion : ∀ n, ∫ ω in Dn n, g₁ n ω ∂P = ∫ ω in Dn n, g₂ n ω ∂P := fun n => by
    rw [integral_iUnion_ae (hDk n) (hdisj n) (hion n _ (hg₁m n) (by
        filter_upwards [hg₁b] with ω hω using hω n)),
      integral_iUnion_ae (hDk n) (hdisj n) (hion n _ (hg₂m n) (by
        filter_upwards [hg₂b] with ω hω using hω n))]
    exact tsum_congr fun k => hpiece n k
  -- step (b): the two limits
  have hlimit : ∀ (g : ℕ → Ω → ℂ) (L : Ω → ℂ), (∀ n, AEStronglyMeasurable (g n) P) →
      (∀ᵐ ω ∂P, ∀ n, ω ∈ Dn n → ‖g n ω‖ ≤ 1) →
      (∀ᵐ ω ∂P, ω ∈ D → Tendsto (fun n => (Dn n).indicator (g n) ω) atTop (𝓝 (L ω))) →
      Tendsto (fun n => ∫ ω in Dn n, g n ω ∂P) atTop (𝓝 (∫ ω in D, L ω ∂P)) := by
    intro g L hgm hgb hgl
    simp only [← integral_indicator₀ (hDn _), ← integral_indicator hDm]
    refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
      (fun n => (hgm n).indicator₀ (hDn n)) (integrable_const 1) (fun n => ?_) ?_
    · filter_upwards [hgb] with ω hω
      by_cases hn : ω ∈ Dn n
      · rw [indicator_of_mem hn]; exact hω n hn
      · rw [indicator_of_notMem hn, norm_zero]; exact zero_le_one
    · filter_upwards [hgl] with ω hω
      by_cases hωD : ω ∈ D
      · rw [indicator_of_mem hωD]
        exact hω hωD
      · rw [indicator_of_notMem hωD]
        refine tendsto_const_nhds.congr' (Eventually.of_forall fun n => ?_)
        change 0 = (Dn n).indicator (g n) ω
        rw [indicator_of_notMem fun h => hωD ((hmemDn n ω).1 h).1]
  have hconv : ∀ᵐ ω ∂P, ω ∈ D → (∀ᶠ n in atTop, ω ∈ Dn n) ∧
      Tendsto (fun n => f n ω) atTop (𝓝 (G ω)) := by
    filter_upwards [hlimD, hZF] with ω hω hωF hωD
    obtain ⟨hev, hK⟩ := hω hωD
    have hevD : ∀ᶠ n in atTop, ω ∈ Dn n := hev.mono fun n hn => (hmemDn n ω).2 ⟨hωD, hn⟩
    refine ⟨hevD, hK.congr' ?_⟩
    filter_upwards [hevD] with n hn
    exact (hωF n hn).symm
  have hL₁ := hlimit g₁ (fun ω => starRingEnd ℂ (G ω) * X ω) hg₁m hg₁b (by
    filter_upwards [hconv] with ω hω hωD
    obtain ⟨hev, hf⟩ := hω hωD
    have ht : Tendsto (fun n => g₁ n ω) atTop (𝓝 (starRingEnd ℂ (G ω) * X ω)) :=
      ((Complex.continuous_conj.tendsto _).comp hf).mul_const (X ω)
    refine ht.congr' ?_
    filter_upwards [hev] with n hn
    rw [indicator_of_mem hn])
  have hL₂ := hlimit g₂ (fun ω => starRingEnd ℂ (G ω) * G ω) hg₂m hg₂b (by
    filter_upwards [hconv] with ω hω hωD
    obtain ⟨hev, hf⟩ := hω hωD
    have ht : Tendsto (fun n => g₂ n ω) atTop (𝓝 (starRingEnd ℂ (G ω) * G ω)) :=
      ((Complex.continuous_conj.tendsto _).comp hf).mul hf
    refine ht.congr' ?_
    filter_upwards [hev] with n hn
    rw [indicator_of_mem hn])
  exact tendsto_nhds_unique (hL₁.congr fun n => hunion n) hL₂

/-! ### The member kernels force null protected events -/

section Members

omit mΩ in
theorem conj_exp_ofReal (r : ℝ) : starRingEnd ℂ (Complex.exp (r : ℂ)) = Complex.exp (r : ℂ) := by
  rw [← Complex.exp_conj, Complex.conj_ofReal]

omit mΩ in
theorem conj_exp_I_mul (y : ℝ) :
    starRingEnd ℂ (Complex.exp (Complex.I * (y : ℂ))) = Complex.exp (-(Complex.I * (y : ℂ))) := by
  rw [← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal, neg_mul]

variable [IsProbabilityMeasure P] {κ θ : ℝ} {d : PairData Ω} {β : Ω → BoundaryWord}
  {Hc : Ω → DistOn upperHalfPlaneOpens} {U : Ω → ℝ≥0∞} {W : ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}

/-- **The member kernels force zero energy or a null protected event.** If `FCK2CapForwardInputs` holds, then for
every capacity `q`, every family of rational balls `Fb` in `ℍ`, every `f ∈ C_c^∞(⋃ Fb)` and every `𝓕_q`-event `D`
inside the member protected set, either `∇f = 0` or `P D = 0`. The instances `Ξ = 0` (first moment) and
`Ξ = −Δf/2π` (second moment) give `exp(−‖∇f‖²/2) P(D) = exp(−3‖∇f‖²/2) P(D)`. -/
theorem norm_gradFeat_eq_zero_of_fcCapForwardInputs (hHc : Measurable Hc)
    (h : FCK2CapForwardInputs P κ θ d β Hc U W 𝓕) {q : ℝ≥0} {Fb : Finset (ℚ × ℚ × ℚ)}
    (hFb : ballsK Fb ⊆ QuantumZipper.H)
    (f : zsSub ((ballsOpen Fb : TopologicalSpace.Opens ℂ) : Set ℂ)) {D : Set Ω}
    (hD : MeasurableSet[𝓕 q] D)
    (hDS : ∀ᵐ ω ∂P, ω ∈ D → ω ∈ meetSet d ∧ (q : ℝ≥0∞) < U ω ∧
      Disjoint (ballsK Fb) (QuantumZipper.fwdHull (fun r : ℝ => W r.toNNReal ω) q))
    (hPD : P D ≠ 0) : ‖gradFeat ((ballsOpen Fb : TopologicalSpace.Opens ℂ) : Set ℂ) f.1‖ = 0 := by
  have hVH : ((ballsOpen Fb : TopologicalSpace.Opens ℂ) : Set ℂ) ⊆ QuantumZipper.H := (ballsU_subset_ballsK Fb).trans hFb
  have hVo : IsOpen ((ballsOpen Fb : TopologicalSpace.Opens ℂ) : Set ℂ) := (ballsOpen Fb).isOpen
  have hHfm : ∀ φ : TestOn upperHalfPlaneOpens,
      Measurable fun ω => Exist.flowField 0 (θ * chiC κ) (Hc ω) φ := fun φ =>
    (LQGMetric.measurable_distOn_apply φ).comp ((Exist.measurable_flowField 0 _).comp hHc)
  set L : TestOn upperHalfPlaneOpens := lapTest (ballsOpen Fb) f with hL
  set a : ℝ := ‖gradFeat ((ballsOpen Fb : TopologicalSpace.Opens ℂ) : Set ℂ) f.1‖ ^ 2 with ha
  have hp₀ : projFactor (ballsOpen Fb) f 0 = Complex.exp ((-(1 / 2) * a : ℝ) : ℂ) := by
    have h0 : covVec ((ballsOpen Fb : TopologicalSpace.Opens ℂ) : Set ℂ) ⇑(0 : TestOn upperHalfPlaneOpens) = 0 := by
      have := covVec_sub hVo hVH (0 : TestOn upperHalfPlaneOpens) 0
      rwa [sub_zero, sub_self] at this
    rw [projFactor, h0, inner_zero_right, sub_zero]
  have hp₁ : projFactor (ballsOpen Fb) f L = Complex.exp ((-(1 / 2) * a - a : ℝ) : ℂ) := by
    rw [projFactor, hL, covVec_lapTest_self hVH f, real_inner_self_eq_norm_sq]
  have hDm : MeasurableSet D := 𝓕.le q _ hD
  have hPDr : P.real D ≠ 0 := by
    rw [measureReal_def]
    exact ENNReal.toReal_ne_zero.2 ⟨hPD, measure_ne_top P D⟩
  -- first moment at `Ξ = 0`
  have hI₀ := setIntegral_eq_of_fcCapForwardKernel (𝓕.le q)
    (GFF.integrable_exp_I_mul (hHfm (L + 0)))
    (ae_of_all P (fun ω => by rw [Complex.norm_exp_I_mul_ofReal])) (h.members q Fb hFb f 0) hD hDS
  have e₀ : ∀ ω, projFactor (ballsOpen Fb) f 0 *
      Complex.exp (Complex.I * (Exist.flowField 0 (θ * chiC κ) (Hc ω) 0 : ℂ)) =
      Complex.exp ((-(1 / 2) * a : ℝ) : ℂ) := fun ω => by
    rw [map_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one, hp₀]
  simp only [e₀, add_zero, setIntegral_const, Complex.real_smul] at hI₀
  -- second moment at `Ξ = −Δf/2π`
  have hI₁ := setIntegral_conj_mul_eq_of_fcCapForwardKernel (𝓕.le q)
    (GFF.integrable_exp_I_mul (hHfm (L + L)))
    (ae_of_all P (fun ω => by rw [Complex.norm_exp_I_mul_ofReal])) (h.members q Fb hFb f L) hD hDS
  have e₁ : ∀ ω, starRingEnd ℂ (projFactor (ballsOpen Fb) f L *
      Complex.exp (Complex.I * (Exist.flowField 0 (θ * chiC κ) (Hc ω) L : ℂ))) *
      Complex.exp (Complex.I * (Exist.flowField 0 (θ * chiC κ) (Hc ω) (L + L) : ℂ)) =
      Complex.exp ((-(1 / 2) * a - a : ℝ) : ℂ) *
        Complex.exp (Complex.I * (Exist.flowField 0 (θ * chiC κ) (Hc ω) L : ℂ)) := fun ω => by
    rw [map_mul, hp₁, conj_exp_ofReal, conj_exp_I_mul, map_add, mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have e₂ : ∀ ω, starRingEnd ℂ (projFactor (ballsOpen Fb) f L *
      Complex.exp (Complex.I * (Exist.flowField 0 (θ * chiC κ) (Hc ω) L : ℂ))) *
      (projFactor (ballsOpen Fb) f L *
        Complex.exp (Complex.I * (Exist.flowField 0 (θ * chiC κ) (Hc ω) L : ℂ))) =
      Complex.exp ((-(1 / 2) * a - a : ℝ) : ℂ) * Complex.exp ((-(1 / 2) * a - a : ℝ) : ℂ) := fun ω => by
    rw [map_mul, hp₁, conj_exp_ofReal, conj_exp_I_mul]
    calc Complex.exp ((-(1 / 2) * a - a : ℝ) : ℂ) * Complex.exp (-(Complex.I *
          (Exist.flowField 0 (θ * chiC κ) (Hc ω) L : ℂ))) *
        (Complex.exp ((-(1 / 2) * a - a : ℝ) : ℂ) * Complex.exp (Complex.I *
          (Exist.flowField 0 (θ * chiC κ) (Hc ω) L : ℂ)))
        = Complex.exp ((-(1 / 2) * a - a : ℝ) : ℂ) * Complex.exp ((-(1 / 2) * a - a : ℝ) : ℂ) *
          (Complex.exp (-(Complex.I * (Exist.flowField 0 (θ * chiC κ) (Hc ω) L : ℂ))) *
            Complex.exp (Complex.I * (Exist.flowField 0 (θ * chiC κ) (Hc ω) L : ℂ))) := by ring
      _ = _ := by
        rw [← Complex.exp_add (-(Complex.I * (Exist.flowField 0 (θ * chiC κ) (Hc ω) L : ℂ))),
          neg_add_cancel, Complex.exp_zero, mul_one]
  simp only [e₁, e₂, setIntegral_const, Complex.real_smul] at hI₁
  rw [integral_const_mul, hI₀] at hI₁
  -- compare the two Gaussian factors
  have hne : Complex.exp ((-(1 / 2) * a - a : ℝ) : ℂ) * (P.real D : ℂ) ≠ 0 :=
    mul_ne_zero (Complex.exp_ne_zero _) (Complex.ofReal_ne_zero.2 hPDr)
  have hfac : Complex.exp ((-(1 / 2) * a : ℝ) : ℂ) = Complex.exp ((-(1 / 2) * a - a : ℝ) : ℂ) := by
    have h' : Complex.exp ((-(1 / 2) * a - a : ℝ) : ℂ) * (P.real D : ℂ) *
        Complex.exp ((-(1 / 2) * a : ℝ) : ℂ) = Complex.exp ((-(1 / 2) * a - a : ℝ) : ℂ) * (P.real D : ℂ) *
        Complex.exp ((-(1 / 2) * a - a : ℝ) : ℂ) := by
      calc _ = Complex.exp ((-(1 / 2) * a - a : ℝ) : ℂ) * ((P.real D : ℂ) *
            Complex.exp ((-(1 / 2) * a : ℝ) : ℂ)) := by ring
        _ = (P.real D : ℂ) * (Complex.exp ((-(1 / 2) * a - a : ℝ) : ℂ) *
            Complex.exp ((-(1 / 2) * a - a : ℝ) : ℂ)) := hI₁
        _ = _ := by ring
    exact mul_left_cancel₀ hne h'
  rw [← Complex.ofReal_exp, ← Complex.ofReal_exp, Complex.ofReal_inj, Real.exp_eq_exp] at hfac
  have ha0 : a = 0 := by linarith
  have hn := sq_eq_zero_iff.1 ha0.symm.symm
  exact hn

/-- A nonempty open set carries `f ∈ C_c^∞` with `∇f ≠ 0`. -/
theorem exists_norm_gradFeat_ne_zero {V : Set ℂ} (hV : IsOpen V) (hne : V.Nonempty) :
    ∃ f : zsSub V, ‖gradFeat V f.1‖ ≠ 0 := by
  obtain ⟨g, hg, hpos⟩ := exists_pos_energy_zeroSpace_m7d hV hne
  refine ⟨⟨g, hg⟩, fun h0 => ?_⟩
  have hsq := norm_gradFeat_sq (D := V) ((isDNSpace_zeroSpace V).smooth g hg)
    ((isDNSpace_zeroSpace V).energy g hg)
  simp only at h0
  rw [h0] at hsq
  linarith [hsq]

/-- **The member kernels force every protected censored event to be null** (when the balls are nonempty). -/
theorem measure_eq_zero_of_fcCapForwardInputs (hHc : Measurable Hc)
    (h : FCK2CapForwardInputs P κ θ d β Hc U W 𝓕) {q : ℝ≥0} {Fb : Finset (ℚ × ℚ × ℚ)}
    (hFb : ballsK Fb ⊆ QuantumZipper.H) (hne : (ballsU Fb).Nonempty) {D : Set Ω}
    (hD : MeasurableSet[𝓕 q] D)
    (hDS : ∀ᵐ ω ∂P, ω ∈ D → ω ∈ meetSet d ∧ (q : ℝ≥0∞) < U ω ∧
      Disjoint (ballsK Fb) (QuantumZipper.fwdHull (fun r : ℝ => W r.toNNReal ω) q)) :
    P D = 0 := by
  by_contra hPD
  obtain ⟨f, hf⟩ := exists_norm_gradFeat_ne_zero (ballsOpen Fb).isOpen hne
  exact hf (norm_gradFeat_eq_zero_of_fcCapForwardInputs hHc h hFb f hD hDS hPD)

/-- One rational ball in `ℍ`: the closed unit ball around `2i`. -/
def unitBallAt2I : Finset (ℚ × ℚ × ℚ) := {((0 : ℚ), (2 : ℚ), (1 : ℚ))}

theorem ballsK_unitBallAt2I_subset : ballsK unitBallAt2I ⊆ QuantumZipper.H := by
  intro z hz
  simp only [unitBallAt2I, ballsK, Finset.mem_singleton, iUnion_iUnion_eq_left, Metric.mem_closedBall,
    ratCentre] at hz
  have him := Complex.abs_im_le_norm (z - ⟨((0 : ℚ) : ℝ), ((2 : ℚ) : ℝ)⟩)
  rw [← dist_eq_norm] at him
  have h1 := him.trans hz
  simp only [Complex.sub_im, Rat.cast_ofNat, Rat.cast_one] at h1
  show 0 < z.im
  have := neg_abs_le (z.im - 2)
  linarith

theorem ballsU_unitBallAt2I_nonempty : (ballsU unitBallAt2I).Nonempty := by
  refine ⟨ratCentre ((0 : ℚ), (2 : ℚ), (1 : ℚ)), ?_⟩
  simp only [unitBallAt2I, ballsU, Finset.mem_singleton, iUnion_iUnion_eq_left]
  exact Metric.mem_ball_self (by norm_num)

/-- **At capacity zero the member kernels force the meeting branch to be null.** If the forward inputs hold for a
filtration containing the retained σ-algebra at time `0`, a continuous driver, and a lifetime positive on the meeting
branch, then `P (meetSet d) = 0`. -/
theorem measure_meetSet_eq_zero_of_fcCapForwardInputs (hHc : Measurable Hc)
    (h : FCK2CapForwardInputs P κ θ d β Hc U W 𝓕) (hd : d.IsMeasGood)
    (h𝓕 : retSigma d P ≤ 𝓕 0) (hW : ∀ ω, Continuous (W · ω))
    (hU : ∀ᵐ ω ∂P, ω ∈ meetSet d → 0 < U ω) : P (meetSet d) = 0 := by
  refine measure_eq_zero_of_fcCapForwardInputs (q := 0) hHc h ballsK_unitBallAt2I_subset
    ballsU_unitBallAt2I_nonempty (h𝓕 _ (hd.measurableSet_meetSet P)) ?_
  filter_upwards [hU] with ω hω hM
  refine ⟨hM, by simpa using hω hM, ?_⟩
  have hc : Continuous fun r : ℝ => W r.toNNReal ω := (hW ω).comp continuous_real_toNNReal
  rw [NNReal.coe_zero, QuantumZipper.RS.fwdHull_zero_eq_empty hc]
  exact disjoint_empty _

end Members

/-! ### The forward-kernel statement forces the meeting branch to be null -/

section Statement

universe u

/-- **`FirstContactK2ForwardKernelsStatement` forces every first contact with two nonempty continuations to be
null.** In every instance of its hypotheses, together with Theorems 1.2–1.3 and Lemma 7.6 (through Lemma 7.7, which
makes the first canonical lifetime positive on the meeting branch), the statement implies `P (meetSet d) = 0`. -/
theorem measure_meetSet_eq_zero_of_forwardKernels (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h76 : Sec7.Lemma76Statement.{u})
    (hF : FirstContactK2ForwardKernelsStatement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {b : ℝ → ℝ} {jumps : Finset ℝ}
    (hb : IsPiecewiseConstantBoundaryData b jumps) {x₁ x₂ θ₁ θ₂ : ℝ} (hx : x₂ < x₁)
    (hθ : θ₁ < θ₂ + Real.pi) {Ω₀ : Type u} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀}
    [IsProbabilityMeasure P₀] {h : Ω₀ → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P₀ h b jumps) {η₁ η₂ : Ω₀ → ℝ≥0 → ℂ} {ζ₁ ζ₂ : Ω₀ → ℝ≥0∞}
    (hη₁ : IsFlowLine κ b jumps x₁ θ₁ P₀ h η₁ ζ₁) (hη₂ : IsFlowLine κ b jumps x₂ θ₂ P₀ h η₂ ζ₂)
    {d : PairData Ω₀} (hd : d.IsMeasGood) (hζ₁ : d.ζ₁ = ζ₁) (hζ₂ : d.ζ₂ = ζ₂)
    (hae : ∀ᵐ ω ∂P₀, ω ∈ d.G ∧ (∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₁ ω → d.η₁ ω s = η₁ ω s) ∧
      ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ ζ₂ ω → d.η₂ ω s = η₂ ω s)
    {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension b jumps u₀) {β : Ω₀ → BoundaryWord}
    (hβ : Measurable[retSigma d P₀] β) (hsort : ∀ᵐ ω ∂P₀, ω ∈ meetSet d → (β ω).IsSorted)
    (hmean : IsBoxMeanIdentification κ P₀ h η₁ η₂ ζ₁ ζ₂ u₀ hd β)
    {γ₁ γ₂ : Ω₀ → ℝ≥0 → ℂ} {U₁ U₂ : Ω₀ → ℝ≥0∞} (hγ₁ : ∀ t, Measurable fun ω => γ₁ ω t)
    (hγ₂ : ∀ t, Measurable fun ω => γ₂ ω t) (hU₁ : Measurable U₁) (hU₂ : Measurable U₂)
    (hcanon : d.IsCanonClock P₀ γ₁ γ₂ U₁ U₂) {W₁ W₂ : ℝ≥0 → Ω₀ → ℝ}
    (hm₁ : ∀ t, Measurable (W₁ t)) (hm₂ : ∀ t, Measurable (W₂ t))
    (hc₁ : ∀ ω, Continuous (W₁ · ω)) (hc₂ : ∀ ω, Continuous (W₂ · ω))
    (hz₁ : ∀ ω, W₁ 0 ω = 0) (hz₂ : ∀ ω, W₂ 0 ω = 0)
    (hg : ∀ᵐ ω ∂P₀, ω ∈ meetSet d →
      IsGeneratingTrace (W₁ · ω) (U₁ ω) (γ₁ ω) ∧ IsGeneratingTrace (W₂ · ω) (U₂ ω) (γ₂ ω)) :
    P₀ (meetSet d) = 0 := by
  obtain ⟨K₁, -⟩ := hF κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P₀ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ d hd hζ₁ hζ₂
    hae u₀ hu₀ β hβ hsort hmean γ₁ γ₂ U₁ U₂ hγ₁ hγ₂ hU₁ hU₂ hcanon W₁ W₂ hm₁ hm₂ hc₁ hc₂ hz₁ hz₂ hg
  have hT := ae_canon_terminal_bad_incident_on_chart_side
    (lemma77Statement_of_thm12_thm13_lemma76 h12 h13 h76) hκ hκ4 hb hx hθ hh hη₁ hη₂ hd hζ₁ hζ₂ hae
    hcanon hc₁ hc₂ hz₁ hz₂ hg
  have hpos : ∀ᵐ ω ∂P₀, ω ∈ meetSet d → 0 < U₁ ω := by
    filter_upwards [hT] with ω hω hM
    by_cases htop : U₁ ω = ⊤
    · rw [htop]
      exact ENNReal.zero_lt_top
    · have he : ((U₁ ω).toNNReal : ℝ≥0∞) = U₁ ω := ENNReal.coe_toNNReal htop
      rw [← he]
      exact ENNReal.coe_pos.2 ((hω hM).1 _ he).1
  exact measure_meetSet_eq_zero_of_fcCapForwardInputs (hd.measurable_chartField κ hh.1) K₁ hd
    (retSigma_le_fcRetainedDriverFiltration P₀ hd W₁ hm₁ 0) hc₁ hpos

end Statement

end InteractingSLE.Restart.FCPlumb.FCKerLaw
