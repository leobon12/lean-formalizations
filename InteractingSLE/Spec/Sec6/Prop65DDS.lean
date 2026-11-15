/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec6.Prop65DDSLimit
import InteractingSLE.Spec.Sec6.Prop65DDSProd
import MathFin.Probability.Martingales.UnifIntegrableL2

/-!
# Proposition 6.5, Brownian representation, part 6: the abstract Dambis–Dubins–Schwarz theorem

Packet PROVE-SEC6-E (specification §6.1, `source/spec/p145-192.md`, `#prop-6.5`, p. 158:
"Consequently it is a standard Brownian motion run at the clock `a_t(z)`, up to the lifetime of that
clock. If the clock has a finite terminal value, the Brownian motion may be completed on an enlarged
probability space").

`IsDDSLevels.exists_isBrownianReal`: for a consistent sequence of localized conditionally Gaussian
explorations (`IsDDSLevels`, global clock `a`, global process `M`), there are an enlarged probability
space `Ω'` with a measure-preserving projection `π : Ω' → Ω` and a standard Brownian motion `β` on `Ω'`
(every path continuous) such that almost surely `M_t = β_{a_t}` at every time `t` of every
localization.

**Proof.** Along the subsequence of `Prop65DDSLimit` the time-changed means `N^{φ k}` converge, locally
uniformly in `u` and almost surely, to a continuous `N̄`; the clocks `ℓ^{φ k}_u` increase to
`ℓ̄_u = min(u, ℓ̄_∞)`. The exponential martingale identities of the levels pass to the limit by
uniform integrability (`E[(e^{aN − a²ℓ/2})²] ≤ e^{a² u}`, MathFin's
`tendsto_setIntegral_of_subseq_ae_of_sq_bound`) on the generating π-system `⋃_k 𝓕_{σ^{φ k}_s}` of
`𝓗_s = ⨆_k 𝓕_{σ^{φ k}_s}`, then to all `𝓗_s`-events (π-λ) and all `𝓗_s`-measurable weights
(`Measurable.ennreal_induction`). `IsTCExpMartingale.exists_isBrownianReal_completion` builds `β`; at
`u = a_t` the levels are eventually constant (`ℓ^{φ k}_u = u`, `N^{φ k}_u = M_t` by flatness), so
`β_{a_t} = N̄_{a_t} = M_t`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal

namespace InteractingSLE.Sec6.Prop65

section General

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- From equal set integrals over an `m`-measurable sets to equal weighted integrals with any
`m`-measurable weight `W ≥ 0`. -/
theorem lintegral_mul_eq_of_forall_setLIntegral_eq {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {f g : Ω → ℝ≥0∞} (hf : Measurable[mΩ] f) (hg : Measurable[mΩ] g)
    (h : ∀ B, MeasurableSet[m] B → ∫⁻ ω in B, f ω ∂P = ∫⁻ ω in B, g ω ∂P) {W : Ω → ℝ≥0∞}
    (hW : Measurable[m] W) : ∫⁻ ω, W ω * f ω ∂P = ∫⁻ ω, W ω * g ω ∂P := by
  refine @Measurable.ennreal_induction Ω m (fun W => ∫⁻ ω, W ω * f ω ∂P = ∫⁻ ω, W ω * g ω ∂P)
    ?_ ?_ ?_ W hW
  · intro c s hs
    have e : ∀ F : Ω → ℝ≥0∞, (fun ω => s.indicator (fun _ => c) ω * F ω) =
        s.indicator fun ω => c * F ω := fun F => by
      funext ω; by_cases hω : ω ∈ s <;> simp [hω]
    rw [e, e, lintegral_indicator (hm _ hs), lintegral_indicator (hm _ hs),
      lintegral_const_mul c hf, lintegral_const_mul c hg, h s hs]
  · intro F₁ F₂ _ hF₁ hF₂ h₁ h₂
    simp only [Pi.add_apply, add_mul]
    rw [lintegral_add_left (f := fun ω => F₁ ω * f ω) ((hF₁.mono hm le_rfl).mul hf),
      lintegral_add_left (f := fun ω => F₁ ω * g ω) ((hF₁.mono hm le_rfl).mul hg), h₁, h₂]
  · intro F hF hmono hF'
    simp only [ENNReal.iSup_mul]
    rw [lintegral_iSup (f := fun n ω => F n ω * f ω) (fun n => ((hF n).mono hm le_rfl).mul hf)
        (fun n k hnk ω => mul_le_mul_left (hmono hnk ω) _),
      lintegral_iSup (f := fun n ω => F n ω * g ω) (fun n => ((hF n).mono hm le_rfl).mul hg)
        (fun n k hnk ω => mul_le_mul_left (hmono hnk ω) _)]
    simp only [hF']

/-- π-λ for an increasing sequence of σ-algebras: equal set integrals on each `m j` (with finite
total) give equal set integrals on `⨆ j, m j`. -/
theorem setLIntegral_eq_of_iSup {m : ℕ → MeasurableSpace Ω} (hmono : Monotone m)
    (hm : ∀ j, m j ≤ mΩ) {f g : Ω → ℝ≥0∞} (htot : ∫⁻ ω, g ω ∂P ≠ ∞)
    (h : ∀ j B, MeasurableSet[m j] B → ∫⁻ ω in B, f ω ∂P = ∫⁻ ω in B, g ω ∂P) :
    ∀ B, MeasurableSet[⨆ j, m j] B → ∫⁻ ω in B, f ω ∂P = ∫⁻ ω in B, g ω ∂P := by
  have hsup : (⨆ j, m j) ≤ mΩ := iSup_le hm
  have huniv : ∫⁻ ω, f ω ∂P = ∫⁻ ω, g ω ∂P := by
    simpa using h 0 univ (@MeasurableSet.univ _ (m 0))
  intro B hB
  refine MeasurableSpace.induction_on_inter (m := ⨆ j, m j)
    (C := fun B _ => ∫⁻ ω in B, f ω ∂P = ∫⁻ ω in B, g ω ∂P)
    (MeasurableSpace.generateFrom_iUnion_measurableSet m).symm
    (isPiSystem_iUnion_of_monotone (fun j => {t | MeasurableSet[m j] t})
      (fun j => @MeasurableSpace.isPiSystem_measurableSet Ω (m j)) fun i j hij t ht => hmono hij t ht)
    ?_ ?_ ?_ ?_ B hB
  · simp
  · intro t ht
    obtain ⟨j, hj⟩ := mem_iUnion.1 ht
    exact h j t hj
  · intro t ht hC
    have htm : MeasurableSet t := hsup _ ht
    have h1 := lintegral_add_compl (μ := P) f htm
    have h2 := lintegral_add_compl (μ := P) g htm
    have hfin : ∫⁻ ω in t, g ω ∂P ≠ ∞ := ne_top_of_le_ne_top htot (h2 ▸ le_self_add)
    rw [hC, huniv] at h1
    exact (ENNReal.add_right_inj hfin).1 (h1.trans h2.symm)
  · intro F hdisj hFm hC
    have hFm' : ∀ i, MeasurableSet (F i) := fun i => hsup _ (hFm i)
    rw [lintegral_iUnion hFm' hdisj, lintegral_iUnion hFm' hdisj]
    exact tsum_congr hC

end General

section Limit

universe u

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}

theorem IsGaussianExploration.continuous_tcN {X : Ω → ℝ} {v : ℝ≥0 → Ω → ℝ} {ρ : Ω → ℝ≥0} {K : ℝ}
    (h : IsGaussianExploration P 𝓕 X v ρ K) {Y : ℝ≥0 → Ω → ℝ} (hY : IsMeanVersion P 𝓕 X ρ Y)
    (G : Set Ω) {ω : Ω}
    (hflat : ∀ s t, s ≤ t → clockA v ρ s ω = clockA v ρ t ω → Y s ω = Y t ω) :
    Continuous fun u => tcN G Y v ρ u ω := by
  by_cases hω : ω ∈ G
  · simp only [tcN, indicator_of_mem hω]
    exact (continuous_comp_lvl (h.isClockAt ω) (hY.cont ω) hflat).sub continuous_const
  · simp only [tcN, indicator_of_notMem hω]
    exact continuous_const

namespace IsDDSLevels

variable {X : ℕ → Ω → ℝ} {v : ℕ → ℝ≥0 → Ω → ℝ} {ρ : ℕ → Ω → ℝ≥0} {K : ℕ → ℝ} {G : ℕ → Set Ω}
  {Y : ℕ → ℝ≥0 → Ω → ℝ} {a : ℝ≥0 → Ω → ℝ} {M : ℝ≥0 → Ω → ℝ}

/-- `⨆ k, min s (x k) = min s (⨆ k, x k)` for a bounded family in `ℝ≥0`. -/
lemma iSup_min_eq {x : ℕ → ℝ≥0} (hx : BddAbove (range x)) (s : ℝ≥0) :
    ⨆ k, min s (x k) = min s (⨆ k, x k) := by
  refine le_antisymm (ciSup_le fun k => min_le_min le_rfl (le_ciSup hx k)) ?_
  have hb : BddAbove (range fun k => min s (x k)) := ⟨s, by rintro _ ⟨k, rfl⟩; exact min_le_left _ _⟩
  by_cases hs : (⨆ k, x k) ≤ s
  · rw [min_eq_right hs]
    exact ciSup_le fun k => (le_of_eq (min_eq_right ((le_ciSup hx k).trans hs)).symm).trans
      (le_ciSup hb k)
  · push Not at hs
    obtain ⟨k, hk⟩ := exists_lt_of_lt_ciSup hs
    exact (min_le_left _ _).trans ((le_of_eq (min_eq_left hk.le).symm).trans (le_ciSup hb k))

/-- **The Dambis–Dubins–Schwarz representation** (abstract form of the Brownian clause of
Proposition 6.5). -/
theorem exists_isBrownianReal [IsProbabilityMeasure P] (L : IsDDSLevels P 𝓕 X v ρ K G Y a M)
    (hnull : ∀ s, MeasurableSet s → P s = 0 → MeasurableSet[𝓕 0] s) :
    ∃ (Ω' : Type u) (_ : MeasurableSpace Ω') (P' : Measure Ω') (π : Ω' → Ω)
      (β : ℝ≥0 → Ω' → ℝ), IsProbabilityMeasure P' ∧ Measurable π ∧ P'.map π = P ∧
        IsBrownianReal β P' ∧ (∀ ω', Continuous fun u => β u ω') ∧
          ∀ᵐ ω' ∂P', ∀ n, π ω' ∈ G n → ∀ t, t ≤ ρ n (π ω') →
            M t (π ω') = β (a t (π ω')).toNNReal ω' := by
  obtain ⟨φ, hφm, hφk, hcauchy⟩ := L.exists_subseq_ae_cauchy hnull
  have hflat : ∀ᵐ ω ∂P, ∀ n, FlatAt v ρ Y n ω :=
    ae_all_iff.2 fun n => (L.gauss n).ae_flat (L.version n)
  obtain ⟨Γ, hΓm, hΓ0, hΓ⟩ := exists_measurableSet_zero_of_ae hnull (hcauchy.and hflat)
  set Nk : ℕ → ℝ≥0 → Ω → ℝ := fun k => tcN (G (φ k)) (Y (φ k)) (v (φ k)) (ρ (φ k)) with hNk
  set Lk : ℕ → ℝ≥0 → Ω → ℝ := fun k => tcL (v (φ k)) (ρ (φ k)) with hLk
  set Nb : ℝ≥0 → Ω → ℝ := fun u ω => Γ.indicator (fun ω => limUnder atTop fun k => Nk k u ω) ω
    with hNb
  set Lb : ℝ≥0 → Ω → ℝ≥0 := fun u ω => ⨆ k, (Lk k u ω).toNNReal with hLb
  -- convergence and continuity of the limit
  have hunif : ∀ ω ∈ Γ, ∀ U : ℕ,
      (∀ u ∈ Icc (0 : ℝ≥0) U, Tendsto (fun k => Nk k u ω) atTop
        (𝓝 (limUnder atTop fun k => Nk k u ω))) ∧
      TendstoUniformlyOn (fun k u => Nk k u ω) (fun u => limUnder atTop fun k => Nk k u ω) atTop
        (Icc (0 : ℝ≥0) U) := fun ω hω U =>
    tendstoUniformlyOn_limUnder_of_geometric (by
      filter_upwards [(hΓ ω hω).1 U] with k hk u hu using hk u hu.2)
  have hconv : ∀ ω ∈ Γ, ∀ u, Tendsto (fun k => Nk k u ω) atTop (𝓝 (Nb u ω)) := by
    intro ω hω u
    obtain ⟨U, hU⟩ := exists_nat_ge u
    simp only [hNb, indicator_of_mem hω]
    exact (hunif ω hω U).1 u ⟨zero_le, hU⟩
  have hNbc : ∀ ω, Continuous fun u => Nb u ω := by
    intro ω
    by_cases hω : ω ∈ Γ
    · simp only [hNb, indicator_of_mem hω]
      refine continuous_iff_continuousAt.2 fun u => ?_
      obtain ⟨U, hU⟩ := exists_nat_gt u
      have hcont : ContinuousOn (fun u => limUnder atTop fun k => Nk k u ω) (Icc 0 U) :=
        (hunif ω hω U).2.continuousOn (Frequently.of_forall fun k =>
          ((L.gauss (φ k)).continuous_tcN (L.version (φ k)) _ ((hΓ ω hω).2 (φ k))).continuousOn)
      exact hcont.continuousAt (mem_of_superset (Iic_mem_nhds hU) fun x hx => ⟨zero_le, hx⟩)
    · simp only [hNb, indicator_of_notMem hω]
      exact continuous_const
  -- the filtration `𝓗_u = ⨆_k 𝓕_{σ^{φ k}_u}`
  set 𝓗 : Filtration ℝ≥0 mΩ :=
    { seq := fun u => ⨆ k, (L.gauss (φ k)).tcFilt u
      mono' := fun _ _ hsu => iSup_mono fun k => (L.gauss (φ k)).tcFilt.mono hsu
      le' := fun u => iSup_le fun k => (L.gauss (φ k)).tcFilt.le u } with h𝓗
  have hk_le : ∀ k u, (L.gauss (φ k)).tcFilt u ≤ 𝓗 u := fun k u =>
    le_iSup (fun k => ((L.gauss (φ k)).tcFilt u : MeasurableSpace Ω)) k
  have hmono_k : ∀ u, Monotone fun k => ((L.gauss (φ k)).tcFilt u : MeasurableSpace Ω) :=
    fun u i j hij => L.tcFilt_mono_level (hφm hij) u
  have hΓ𝓗 : ∀ u, MeasurableSet[𝓗 u] Γ := fun u => hk_le 0 u _
    (IsGaussianExploration.zero_le_measurableSpace ((L.gauss (φ 0)).isStoppingTime_lvlTime u) _ hΓm)
  -- the clocks
  have hLk_le : ∀ k u ω, Lk k u ω ≤ u := fun k u ω => (L.gauss (φ k)).tcL_le u ω
  have hLk_nn : ∀ k u ω, 0 ≤ Lk k u ω := fun k u ω => (L.gauss (φ k)).tcL_nonneg u ω
  have hLk_mono : ∀ u ω, Monotone fun k => Lk k u ω := fun u ω i j hij =>
    L.tcL_mono_level (hφm hij) u ω
  have hLbdd : ∀ u ω, BddAbove (range fun k => (Lk k u ω).toNNReal) := fun u ω =>
    ⟨u, by rintro _ ⟨k, rfl⟩; exact Real.toNNReal_le_iff_le_coe.2 (hLk_le k u ω)⟩
  have hLconv : ∀ u ω, Tendsto (fun k => Lk k u ω) atTop (𝓝 (Lb u ω : ℝ)) := by
    intro u ω
    have h1 : Tendsto (fun k => (Lk k u ω).toNNReal) atTop (𝓝 (Lb u ω)) :=
      tendsto_atTop_ciSup (fun i j hij => Real.toNNReal_le_toNNReal (hLk_mono u ω hij))
        (hLbdd u ω)
    exact (NNReal.tendsto_coe.2 h1).congr fun k => Real.coe_toNNReal _ (hLk_nn k u ω)
  have hNkm : ∀ k u, Measurable[𝓗 u] (Nk k u) := fun k u =>
    ((L.gauss (φ k)).measurable_tcN hnull (L.version _) (L.measurableSet_G _) u).mono
      (hk_le k u) le_rfl
  have hLkm : ∀ k u, Measurable[𝓗 u] (Lk k u) := fun k u =>
    ((L.gauss (φ k)).measurable_tcL u).mono (hk_le k u) le_rfl
  have hNbm : ∀ u, Measurable[𝓗 u] (Nb u) := fun u =>
    (@measurable_limUnder ℕ Ω ℝ (𝓗 u) _ _ _ _ _ atTop _ (fun k ω => Nk k u ω) _
      fun k => hNkm k u).indicator (hΓ𝓗 u)
  have hLbm : ∀ u, Measurable[𝓗 u] (Lb u) := fun u =>
    Measurable.iSup fun k => (hLkm k u).real_toNNReal
  have hΓae : ∀ᵐ ω ∂P, ω ∈ Γ := ae_iff.2 hΓ0
  -- the exponential martingale of the limit
  have hexp : ∀ (a' : ℝ) (s u : ℝ≥0), s ≤ u → ∀ W : Ω → ℝ≥0∞, Measurable[𝓗 s] W →
      ∫⁻ ω, W ω * ENNReal.ofReal (Real.exp (a' * Nb u ω - a' ^ 2 * (Lb u ω : ℝ) / 2)) ∂P =
        ∫⁻ ω, W ω * ENNReal.ofReal (Real.exp (a' * Nb s ω - a' ^ 2 * (Lb s ω : ℝ) / 2)) ∂P := by
    intro a' s u hsu W hW
    set F : ℕ → ℝ≥0 → Ω → ℝ := fun k r ω => Real.exp (a' * Nk k r ω - a' ^ 2 * Lk k r ω / 2)
      with hF
    set Fb : ℝ≥0 → Ω → ℝ := fun r ω => Real.exp (a' * Nb r ω - a' ^ 2 * (Lb r ω : ℝ) / 2)
      with hFb
    have hFm : ∀ k r, Measurable (F k r) := fun k r => Real.measurable_exp.comp
      ((((hNkm k r).mono (𝓗.le r) le_rfl).const_mul a').sub
        ((((hLkm k r).mono (𝓗.le r) le_rfl).const_mul _).div_const 2))
    have hFbm : ∀ r, Measurable (Fb r) := fun r => Real.measurable_exp.comp
      ((((hNbm r).mono (𝓗.le r) le_rfl).const_mul a').sub
        (((((hLbm r).mono (𝓗.le r) le_rfl).coe_nnreal_real).const_mul _).div_const 2))
    have hFae : ∀ r, ∀ᵐ ω ∂P, Tendsto (fun k => F k r ω) atTop (𝓝 (Fb r ω)) := fun r => by
      filter_upwards [hΓae] with ω hω
      exact (Real.continuous_exp.tendsto _).comp (((hconv ω hω r).const_mul a').sub
        (((hLconv r ω).const_mul (a' ^ 2)).div_const 2))
    have hlint1 : ∀ k r, ∫⁻ ω, ENNReal.ofReal (F k r ω) ∂P = 1 := fun k r =>
      (L.gauss (φ k)).lintegral_exp_tc_eq_zero (L.version _) (L.measurableSet_G _)
        (L.v_off (φ k)) a' r
    have hsqk : ∀ k r, ∫⁻ ω, ENNReal.ofReal (F k r ω ^ 2) ∂P ≤
        ENNReal.ofReal (Real.exp (a' ^ 2 * r)) := fun k r => by
      have := (L.gauss (φ k)).lintegral_exp_tc_sq_le (L.version _) (L.measurableSet_G _)
        (L.v_off (φ k)) a' r
      refine le_trans (le_of_eq ?_) this
      refine lintegral_congr fun ω => ?_
      rw [ENNReal.ofReal_pow (Real.exp_pos _).le]
    have hsqi : ∀ k r, Integrable (fun ω => F k r ω ^ 2) P := fun k r =>
      ⟨((hFm k r).pow_const 2).aestronglyMeasurable,
        (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ω => sq_nonneg _)).2
          ((hsqk k r).trans_lt ENNReal.ofReal_lt_top)⟩
    have hmemLp2 : ∀ k r, MemLp (F k r) 2 P := fun k r =>
      (memLp_two_iff_integrable_sq (hFm k r).aestronglyMeasurable).2 (hsqi k r)
    have hsq : ∀ k r, ∫ ω, F k r ω ^ 2 ∂P ≤ Real.exp (a' ^ 2 * r) := fun k r => by
      rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun ω => sq_nonneg _)
        ((hFm k r).pow_const 2).aestronglyMeasurable]
      exact ENNReal.toReal_le_of_le_ofReal (Real.exp_pos _).le (hsqk k r)
    have hFb_le : ∀ r, ∫⁻ ω, ENNReal.ofReal (Fb r ω) ∂P ≤ 1 := fun r => by
      have hli : (fun ω => ENNReal.ofReal (Fb r ω)) =ᵐ[P]
          fun ω => liminf (fun k => ENNReal.ofReal (F k r ω)) atTop := by
        filter_upwards [hFae r] with ω hω
        exact ((ENNReal.continuous_ofReal.tendsto _).comp hω).liminf_eq.symm
      rw [lintegral_congr_ae hli]
      refine (lintegral_liminf_le (f := fun k ω => ENNReal.ofReal (F k r ω))
        fun k => ENNReal.measurable_ofReal.comp (hFm k r)).trans (le_of_eq ?_)
      simp only [hlint1, liminf_const]
    have hFbi : ∀ r, Integrable (Fb r) P := fun r =>
      ⟨(hFbm r).aestronglyMeasurable,
        (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ω => (Real.exp_pos _).le)).2
          ((hFb_le r).trans_lt ENNReal.one_lt_top)⟩
    have hlimit : ∀ r (B : Set Ω), Tendsto (fun k => ∫ ω in B, F k r ω ∂P) atTop
        (𝓝 (∫ ω in B, Fb r ω ∂P)) := fun r B =>
      MathFin.tendsto_setIntegral_of_subseq_ae_of_sq_bound (fun k => hmemLp2 k r) (fun k => hsq k r)
        (memLp_one_iff_integrable.2 (hFbi r))
        (fun ns hns => ⟨id, by filter_upwards [hFae r] with ω hω using hω.comp hns⟩) B
    have hset : ∀ j B, MeasurableSet[(L.gauss (φ j)).tcFilt s] B →
        ∫⁻ ω in B, ENNReal.ofReal (Fb u ω) ∂P = ∫⁻ ω in B, ENNReal.ofReal (Fb s ω) ∂P := by
      intro j B hB
      have hBm : MeasurableSet B := (L.gauss (φ j)).tcFilt.le s _ hB
      have hlev : ∀ k, j ≤ k → ∫ ω in B, F k u ω ∂P = ∫ ω in B, F k s ω ∂P := by
        intro k hjk
        have hBk : MeasurableSet[(L.gauss (φ k)).tcFilt s] B := hmono_k s hjk B hB
        have h1 := (L.gauss (φ k)).lintegral_exp_tc (L.version _) (L.measurableSet_G _)
          (L.v_off (φ k)) a' hsu (W := B.indicator fun _ => 1) (measurable_const.indicator hBk)
        have e : ∀ r, ∫⁻ ω, B.indicator (fun _ => (1 : ℝ≥0∞)) ω * ENNReal.ofReal (F k r ω) ∂P =
            ∫⁻ ω in B, ENNReal.ofReal (F k r ω) ∂P := fun r => by
          rw [← lintegral_indicator hBm]
          refine lintegral_congr fun ω => ?_
          by_cases hω : ω ∈ B <;> simp [hω]
        have h2 : ∫⁻ ω in B, ENNReal.ofReal (F k u ω) ∂P =
            ∫⁻ ω in B, ENNReal.ofReal (F k s ω) ∂P := by
          rw [← e, ← e]
          exact h1
        rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun ω => (Real.exp_pos _).le)
          (hFm k u).aestronglyMeasurable,
          integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun ω => (Real.exp_pos _).le)
          (hFm k s).aestronglyMeasurable, h2]
      have heq : ∫ ω in B, Fb u ω ∂P = ∫ ω in B, Fb s ω ∂P :=
        tendsto_nhds_unique (hlimit u B) ((hlimit s B).congr' (by
          filter_upwards [eventually_ge_atTop j] with k hk using (hlev k hk).symm))
      rw [← ofReal_integral_eq_lintegral_ofReal (hFbi u).integrableOn
          (Eventually.of_forall fun ω => (Real.exp_pos _).le),
        ← ofReal_integral_eq_lintegral_ofReal (hFbi s).integrableOn
          (Eventually.of_forall fun ω => (Real.exp_pos _).le), heq]
    have hset' := setLIntegral_eq_of_iSup (P := P) (hmono_k s)
      (fun j => (L.gauss (φ j)).tcFilt.le s) ((hFb_le s).trans_lt ENNReal.one_lt_top).ne hset
    exact lintegral_mul_eq_of_forall_setLIntegral_eq (𝓗.le s)
      (ENNReal.measurable_ofReal.comp (hFbm u)) (ENNReal.measurable_ofReal.comp (hFbm s))
      hset' hW
  have hTC : IsTCExpMartingale P 𝓗 Nb Lb := by
    refine ⟨hNbm, hLbm, fun u ω => ciSup_le fun k => Real.toNNReal_le_iff_le_coe.2
      (hLk_le k u ω), fun s u ω hsu => ?_, hNbc, fun ω => ?_, hexp⟩
    · have e : ∀ k, (Lk k s ω).toNNReal = min s (Lk k u ω).toNNReal := by
        intro k
        apply NNReal.coe_injective
        rw [Real.coe_toNNReal _ (hLk_nn k s ω), NNReal.coe_min, Real.coe_toNNReal _ (hLk_nn k u ω)]
        simp only [hLk, (L.gauss (φ k)).tcL_eq]
        rw [← min_assoc, min_eq_left (NNReal.coe_le_coe.2 hsu)]
      simp only [hLb, e]
      exact iSup_min_eq (hLbdd u ω) s
    · by_cases hω : ω ∈ Γ
      · simp only [hNb, indicator_of_mem hω, hNk, (L.gauss _).tcN_zero]
        exact tendsto_const_nhds.limUnder_eq
      · simp only [hNb, indicator_of_notMem hω]
  obtain ⟨Ω', mΩ', P', π, β, hP', hπ, hmap, hβ, hβc, hid⟩ :=
    hTC.exists_isBrownianReal_completion
  refine ⟨Ω', mΩ', P', π, β, hP', hπ, hmap, hβ, hβc, ?_⟩
  have hpath : ∀ᵐ ω ∂P, ∀ n, ω ∈ G n → ∀ t, t ≤ ρ n ω → M t ω = Y n t ω - Y n 0 ω :=
    ae_all_iff.2 L.path
  have hΩ : ∀ᵐ ω ∂P, ∀ n, ω ∈ G n → ∀ t, t ≤ ρ n ω →
      Lb (a t ω).toNNReal ω = (a t ω).toNNReal ∧ Nb (a t ω).toNNReal ω = M t ω := by
    filter_upwards [hpath, hΓae] with ω hpω hΓω n hGn t ht
    have hflatω := (hΓ ω hΓω).2
    set u := (a t ω).toNNReal with hudef
    have hat : 0 ≤ a t ω := by
      have := ((L.gauss n).isClockAt ω).nonneg t
      rwa [L.clockA_eq hGn, min_eq_left ht] at this
    have hu : (u : ℝ) = a t ω := Real.coe_toNNReal _ hat
    have hk : ∀ k, n ≤ k → Lk k u ω = u ∧ Nk k u ω = M t ω := by
      intro k hk
      have hnn' : n ≤ φ k := hk.trans (hφk k)
      have hGn' : ω ∈ G (φ k) := L.mono_G hnn' hGn
      have htρ' : t ≤ ρ (φ k) ω := ht.trans (L.mono_ρ ω hnn')
      have hAt : clockA (v (φ k)) (ρ (φ k)) t ω = u := by
        rw [L.clockA_eq hGn', min_eq_left htρ', hu]
      have hAρ : (u : ℝ) ≤ clockA (v (φ k)) (ρ (φ k)) (ρ (φ k) ω) ω :=
        hAt ▸ ((L.gauss (φ k)).isClockAt ω).mono htρ'
      have hL : Lk k u ω = u := by
        simp only [hLk]
        rw [(L.gauss (φ k)).tcL_eq, min_eq_left hAρ]
      refine ⟨hL, ?_⟩
      have hσ : clockA (v (φ k)) (ρ (φ k)) (lvlTime (v (φ k)) (ρ (φ k)) u ω) ω =
          clockA (v (φ k)) (ρ (φ k)) t ω := hL.trans hAt.symm
      have hY : Y (φ k) (lvlTime (v (φ k)) (ρ (φ k)) u ω) ω = Y (φ k) t ω := by
        rcases le_total (lvlTime (v (φ k)) (ρ (φ k)) u ω) t with h | h
        · exact hflatω (φ k) _ _ h hσ
        · exact (hflatω (φ k) _ _ h hσ.symm).symm
      simp only [hNk, tcN, indicator_of_mem hGn']
      rw [hY, ← hpω (φ k) hGn' t htρ']
    constructor
    · refine le_antisymm (ciSup_le fun k => Real.toNNReal_le_iff_le_coe.2 (hLk_le k u ω)) ?_
      refine le_trans (le_of_eq ?_) (le_ciSup (hLbdd u ω) n)
      rw [(hk n le_rfl).1, Real.toNNReal_coe]
    · simp only [hNb, indicator_of_mem hΓω]
      refine (tendsto_const_nhds.congr' ?_).limUnder_eq
      filter_upwards [eventually_ge_atTop n] with k hkn
      exact ((hk k hkn).2).symm
  rw [← hmap] at hΩ
  have hΩ' := ae_of_ae_map hπ.aemeasurable hΩ
  filter_upwards [hΩ'] with ω' hω' n hGn t ht
  obtain ⟨h1, h2⟩ := hω' n hGn t ht
  rw [hid ω' _ h1, h2]

end IsDDSLevels

end Limit

end InteractingSLE.Sec6.Prop65
