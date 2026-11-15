import InteractingSLE.WangWu.CouplingMean
import InteractingSLE.Stochastic.Martingale.OptionalSampling
import BrownianMotion.StochasticIntegral.DoobLp

/-!
# Wang–Wu at `κ = 4`: the frozen mean of one point (Lemma 3.5, one-point part)

Packet PROVE-WW-A. Source: `source/external/WW17LP/wang_wu_lean_preprocessed.pdf`, §3, Lemma 3.5 ("For each
deterministic `z`, its frozen process has a bounded continuous martingale version, with its terminal limit
included") and Definition 1.5 ("freeze the harmonic mean at its disconnection time"), ruling R31.

For a deterministic `z ∈ ℍ` and a bounded stopping time `σ₀ < T` of the usual augmentation:

* **the frozen value exists**: almost surely, on `{s(z) ≤ σ₀}` the mean `η_r(z)` has a limit as `r ↑ s(z)`
  (`ae_tendsto_meanAt_swallowTime`);
* **the frozen process is a martingale**: `t ↦ η̄_{t ∧ σ₀}(z)` (the document's frozen mean, `frozenMean`) agrees
  almost surely with a martingale of the usual augmentation (`exists_martingale_frozenMean`).

The proof localizes by Lemma 3.1 (`exists_localizing_meanAt`, stopping times `ρ_n ↑ s(z) ∧ σ₀`), and controls the
oscillation of `η(z)` on `[ρ_n, ρ_∞)` by Doob's weak-type maximal inequality for the martingale
`η_{·∧ρ_m}(z) − η_{·∧ρ_n}(z)`, whose `L²` norm is `E η_{ρ_m}² − E η_{ρ_n}²` by optional sampling.

The pathwise part is in this file's first section: continuity of the mean along a path before swallowing
(`continuousOn_meanAt`) and the oscillation criterion for a left limit (`exists_tendsto_nhdsLT_of_osc`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology QuantumZipper
open scoped NNReal ENNReal

namespace InteractingSLE

namespace WangWu

variable {nL nR : ℕ}

/-! ### Pathwise facts -/

section Pathwise

/-- **Oscillation criterion for a left limit**: if `ρ n < s` and the oscillation of `f` on `[ρ n, s)` is
eventually small, `f` has a limit from the left at `s`. -/
theorem exists_tendsto_nhdsLT_of_osc {f : ℝ≥0 → ℝ} {ρ : ℕ → ℝ≥0} {s : ℝ≥0} (hρs : ∀ n, ρ n < s)
    (hosc : ∀ ε > 0, ∃ n, ∀ r, ρ n ≤ r → r < s → |f r - f (ρ n)| ≤ ε) :
    ∃ L, Tendsto f (𝓝[<] s) (𝓝 L) := by
  have : NeBot (𝓝[<] s) := nhdsLT_neBot_of_exists_lt ⟨ρ 0, hρs 0⟩
  have hc : Cauchy (map f (𝓝[<] s)) := by
    refine Metric.cauchy_iff.2 ⟨inferInstance, fun ε hε => ?_⟩
    obtain ⟨n, hn⟩ := hosc (ε / 3) (by positivity)
    refine ⟨f '' Ioo (ρ n) s, image_mem_map (Ioo_mem_nhdsLT (hρs n)), ?_⟩
    rintro _ ⟨r, hr, rfl⟩ _ ⟨r', hr', rfl⟩
    have h1 := hn r hr.1.le hr.2
    have h2 := hn r' hr'.1.le hr'.2
    rw [Real.dist_eq]
    calc |f r - f r'| ≤ |f r - f (ρ n)| + |f r' - f (ρ n)| := by
          rw [abs_sub_comm (f r') _]; exact abs_sub_le _ _ _
      _ < ε := by linarith
  obtain ⟨L, hL⟩ := CompleteSpace.complete hc
  exact ⟨L, hL⟩

variable {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ}
  {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

theorem continuousOn_coe_Icc (T : ℝ≥0) :
    ContinuousOn (fun r : ℝ≥0 => (r : ℝ)) (Icc 0 T) := NNReal.continuous_coe.continuousOn

/-- **The mean is continuous in time before swallowing**: along a path of the chain, for `T < ζ` and `z` alive
at `T`, `r ↦ η_r(z)` is continuous on `[0, T]`. -/
theorem continuousOn_meanAt (hP : IsIntegratedSLEPath 4 xL xR ρL ρR w vL vR b ζ) {T : ℝ≥0}
    (hT : (T : ℝ≥0∞) < ζ) {z : ℂ} (hz : 0 < z.im) (hsol : ∃ v, IsForwardSol (Ito.rpath w) z T v) :
    ContinuousOn (fun r => meanAt ρL ρR w vL vR r z) (Icc 0 T) := by
  obtain ⟨hwc, hpos, hfc, -⟩ := Ito.fwdMap_facts hP hT hz hsol
  have hsub : Icc (0 : ℝ≥0) T ⊆ {t | (t : ℝ≥0∞) < ζ} := fun r hr =>
    lt_of_le_of_lt (by exact_mod_cast hr.2) hT
  have hw : ContinuousOn w (Icc 0 T) := hP.2.2.2.1.mono hsub
  have hvL : ∀ i, ContinuousOn (vL i) (Icc 0 T) := fun i => (hP.2.2.2.2.1 i).mono hsub
  have hvR : ∀ i, ContinuousOn (vR i) (Icc 0 T) := fun i => (hP.2.2.2.2.2.1 i).mono hsub
  have hmaps : MapsTo (fun r : ℝ≥0 => (r : ℝ)) (Icc 0 T) (Icc 0 (T : ℝ)) := fun r hr =>
    ⟨r.coe_nonneg, by exact_mod_cast hr.2⟩
  -- the image point
  have hF : ContinuousOn (fun r : ℝ≥0 => fwdMap (Ito.rpath w) r z) (Icc 0 T) :=
    hfc.comp (continuousOn_coe_Icc T) hmaps
  have hFpos : ∀ r ∈ Icc (0 : ℝ≥0) T, 0 < (fwdMap (Ito.rpath w) r z).im := fun r hr =>
    hpos r (hmaps hr)
  -- each argument is continuous: its argument stays in the upper half-plane
  have harg : ∀ g : ℝ≥0 → ℝ, ContinuousOn g (Icc 0 T) →
      ContinuousOn (fun r : ℝ≥0 => Complex.arg (fwdMap (Ito.rpath w) (r : ℝ) z - (g r : ℂ)))
        (Icc 0 T) := by
    intro g hg r hr
    have hin : fwdMap (Ito.rpath w) (r : ℝ) z - (g r : ℂ) ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      right
      simp only [Complex.sub_im, Complex.ofReal_im, sub_zero]
      exact (hFpos r hr).ne'
    have hcw : ContinuousWithinAt (fun r : ℝ≥0 => fwdMap (Ito.rpath w) (r : ℝ) z - (g r : ℂ))
        (Icc 0 T) r :=
      (hF r hr).sub (Complex.continuous_ofReal.continuousAt.comp_continuousWithinAt (hg r hr))
    exact (show ContinuousWithinAt
      (Complex.arg ∘ fun r : ℝ≥0 => fwdMap (Ito.rpath w) (r : ℝ) z - (g r : ℂ)) (Icc 0 T) r from
        ContinuousAt.comp_continuousWithinAt (g := Complex.arg) (Complex.continuousAt_arg hin) hcw)
  have harg0 : ContinuousOn (fun r : ℝ≥0 => Complex.arg (fwdMap (Ito.rpath w) (r : ℝ) z))
      (Icc 0 T) := by
    have := harg (fun _ => 0) continuousOn_const
    simpa using this
  have hL : ∀ i, ContinuousOn (fun r : ℝ≥0 =>
      ρL i * Complex.arg (fwdMap (Ito.rpath w) (r : ℝ) z - ((vL i r - w r : ℝ) : ℂ))) (Icc 0 T) :=
    fun i => continuousOn_const.mul (harg (fun r => vL i r - w r) ((hvL i).sub hw))
  have hR : ∀ i, ContinuousOn (fun r : ℝ≥0 =>
      ρR i * Complex.arg (fwdMap (Ito.rpath w) (r : ℝ) z - ((vR i r - w r : ℝ) : ℂ))) (Icc 0 T) :=
    fun i => continuousOn_const.mul (harg (fun r => vR i r - w r) ((hvR i).sub hw))
  have hsum := (continuousOn_finsetSum Finset.univ fun i _ => hL i).add
    (continuousOn_finsetSum Finset.univ fun i _ => hR i)
  have htot := (continuousOn_const (c := wwLambda * (1 + ∑ i, ρR i))).sub harg0 |>.sub
    ((continuousOn_const (c := (1 / 2 : ℝ))).mul hsum)
  exact htot.congr fun r _ => rfl

/-- A point alive at `T` under a driver continuous on `[0, T']`, `T < T'`, is swallowed strictly after `T`. -/
theorem lt_swallowTime_of_isForwardSol {W : ℝ → ℝ} {z : ℂ} {T T' : ℝ} (hT : 0 ≤ T) (hTT' : T < T')
    (hW : ContinuousOn W (Icc 0 T')) (hz : 0 < z.im) (hsol : ∃ u, IsForwardSol W z T u) :
    ENNReal.ofReal T < swallowTime W z := by
  have hT' : 0 ≤ T' := hT.trans hTT'.le
  have hW'c : Continuous (Ito.clampDrv W T') := Ito.continuous_clampDrv hT' hW
  have heq : EqOn (Ito.clampDrv W T') W (Icc 0 T') := Ito.clampDrv_eqOn
  obtain ⟨u, hu⟩ := hsol
  have hu' : IsForwardSol (Ito.clampDrv W T') z T u :=
    (Ito.isForwardSol_iff_of_eqOn (heq.mono (Icc_subset_Icc_right hTT'.le)) u).2 hu
  have hnot := Ito.notMem_fwdHull_of_isForwardSol hW'c hz hT hu'
  have hlt : ENNReal.ofReal T < swallowTime (Ito.clampDrv W T') z := by
    by_contra hc
    exact hnot ⟨hz, not_lt.1 hc⟩
  obtain ⟨_, ⟨T'', ⟨-, u'', hu''⟩, rfl⟩, hlt'⟩ := lt_sSup_iff.mp hlt
  have hTT'' : T < T'' := (ENNReal.ofReal_lt_ofReal_iff'.mp hlt').1
  have hm : T < min T'' T' := lt_min hTT'' hTT'
  have hsolm : IsForwardSol W z (min T'' T') u'' :=
    (Ito.isForwardSol_iff_of_eqOn (heq.mono (Icc_subset_Icc_right (min_le_right _ _))) u'').1
      (isForwardSol_of_le hu'' (min_le_left _ _))
  calc ENNReal.ofReal T < ENNReal.ofReal (min T'' T') := (ENNReal.ofReal_lt_ofReal_iff
        (hT.trans_lt hm)).2 hm
    _ ≤ swallowTime W z := ofReal_le_swallowTime (hT.trans hm.le) ⟨u'', hsolm⟩

/-- Along a path of the chain, a point alive at `T < ζ` is swallowed strictly after `T`. -/
theorem lt_swallowTime_of_path (hP : IsIntegratedSLEPath 4 xL xR ρL ρR w vL vR b ζ) {T : ℝ≥0}
    (hT : (T : ℝ≥0∞) < ζ) {z : ℂ} (hz : 0 < z.im) (hsol : ∃ v, IsForwardSol (Ito.rpath w) z T v) :
    ((T : ℝ≥0) : ℝ≥0∞) < swallowTime (Ito.rpath w) z := by
  -- a slightly later time still before `ζ`
  obtain ⟨T', hTT', hT'ζ⟩ : ∃ T' : ℝ≥0, T < T' ∧ (T' : ℝ≥0∞) < ζ := by
    obtain ⟨c, hc1, hc2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hT
    exact ⟨c, by exact_mod_cast hc1, hc2⟩
  have hwc : ContinuousOn (Ito.rpath w) (Icc 0 (T' : ℝ)) := Ito.continuousOn_rpath hP.2.2.2.1 hT'ζ
  have := lt_swallowTime_of_isForwardSol T.coe_nonneg (by exact_mod_cast hTT') hwc hz hsol
  rwa [ENNReal.ofReal_coe_nnreal] at this

/-- **The frozen value along one path** (deterministic). Let `ρ_n < S` (the swallowing time) be nondecreasing
times `≤ σ` exhausting every alive time `≤ σ`, with oscillation of `f` on `[ρ_n, ρ_m]` eventually small. Then
`f` has a left limit at `S` when `S ≤ σ`, and `f(t ∧ ρ_n)` converges to the frozen value at `t ∧ σ` (`f` before
`S`, the left limit afterwards). -/
theorem tendsto_frozen_of_osc {f : ℝ≥0 → ℝ} {ρ : ℕ → ℝ≥0} {σ : ℝ≥0} {S : ℝ≥0∞}
    (hρS : ∀ n, (ρ n : ℝ≥0∞) < S) (hρσ : ∀ n, ρ n ≤ σ)
    (hexh : ∀ t : ℝ≥0, t ≤ σ → (t : ℝ≥0∞) < S → ∀ᶠ n in atTop, t ≤ ρ n)
    (hosc : ∀ ε > 0, ∃ n, ∀ m r, ρ n ≤ r → r ≤ ρ m → |f r - f (ρ n)| < ε) :
    (S ≤ σ → Tendsto f (𝓝[<] S.toNNReal) (𝓝 (limUnder (𝓝[<] S.toNNReal) f))) ∧
    ∀ t : ℝ≥0, Tendsto (fun n => f (min t (ρ n))) atTop
      (𝓝 (if ((min t σ : ℝ≥0) : ℝ≥0∞) < S then f (min t σ) else limUnder (𝓝[<] S.toNNReal) f)) := by
  -- the left limit at a finite `S ≤ σ`
  have hlim : S ≤ σ → Tendsto f (𝓝[<] S.toNNReal) (𝓝 (limUnder (𝓝[<] S.toNNReal) f)) := by
    intro hS
    have hSt : S ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hS
    have hSc : ((S.toNNReal : ℝ≥0) : ℝ≥0∞) = S := ENNReal.coe_toNNReal hSt
    have hρs : ∀ n, ρ n < S.toNNReal := fun n => by
      have := hρS n; rw [← hSc] at this; exact_mod_cast this
    obtain ⟨L, hL⟩ := exists_tendsto_nhdsLT_of_osc (f := f) hρs fun ε hε => by
      obtain ⟨n, hn⟩ := hosc ε hε
      refine ⟨n, fun r hr hrs => ?_⟩
      have hrσ : r ≤ σ := by
        have : (r : ℝ≥0∞) ≤ σ := by
          have h1 : (r : ℝ≥0∞) < S := by rw [← hSc]; exact_mod_cast hrs
          exact h1.le.trans hS
        exact_mod_cast this
      have hrS : (r : ℝ≥0∞) < S := by rw [← hSc]; exact_mod_cast hrs
      obtain ⟨m, hm⟩ := (hexh r hrσ hrS).exists
      exact (hn m r hr hm).le
    have : NeBot (𝓝[<] S.toNNReal) := nhdsLT_neBot_of_exists_lt ⟨ρ 0, hρs 0⟩
    rwa [hL.limUnder_eq]
  refine ⟨hlim, fun t => ?_⟩
  split_ifs with hts
  · -- alive at `t ∧ σ`: eventually `t ∧ ρ_n = t ∧ σ`
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hexh (min t σ) (min_le_right _ _) hts] with n hn
    congr 1
    rcases le_total t σ with h | h
    · rw [min_eq_left h] at hn ⊢; exact (min_eq_left hn).symm
    · rw [min_eq_right h] at hn ⊢
      have : ρ n = σ := le_antisymm (hρσ n) hn
      rw [this, min_eq_right h]
  · -- swallowed by `t ∧ σ`
    push Not at hts
    have hSσ : S ≤ σ := hts.trans (by exact_mod_cast min_le_right t σ)
    have hSt : S ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hSσ
    have hSc : ((S.toNNReal : ℝ≥0) : ℝ≥0∞) = S := ENNReal.coe_toNNReal hSt
    have hρs : ∀ n, ρ n < S.toNNReal := fun n => by
      have := hρS n; rw [← hSc] at this; exact_mod_cast this
    have hSt' : S.toNNReal ≤ t := by
      have : S ≤ t := hts.trans (by exact_mod_cast min_le_left t σ)
      rw [← hSc] at this; exact_mod_cast this
    have hmin : ∀ n, min t (ρ n) = ρ n := fun n => min_eq_right ((hρs n).le.trans hSt')
    simp only [hmin]
    refine (hlim hSσ).comp (tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall hρs⟩)
    refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => Eventually.of_forall fun n => (hρs n).trans ha⟩
    obtain ⟨r, har, hrS⟩ := exists_between ha
    have hrσ : r ≤ σ := (hrS.le.trans (by
      have : S ≤ σ := hSσ; rw [← hSc] at this; exact_mod_cast this))
    have hrS' : (r : ℝ≥0∞) < S := by rw [← hSc]; exact_mod_cast hrS
    filter_upwards [hexh r hrσ hrS'] with n hn
    exact har.trans_le hn

end Pathwise

/-! ### Martingale helpers -/

section Helpers

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}

/-- Changing a martingale of the usual augmentation off a co-null set (`(toMeasurable P Gᶜ)ᶜ ⊆ G`) gives a
martingale. -/
theorem martingale_indicator_compl_toMeasurable [IsFiniteMeasure P] {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M (usualAugmentation 𝓕 P) P) {G : Set Ω} (hG : ∀ᵐ ω ∂P, ω ∈ G) :
    Martingale (fun t => (toMeasurable P Gᶜ)ᶜ.indicator (M t)) (usualAugmentation 𝓕 P) P := by
  set N := toMeasurable P Gᶜ with hNdef
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  have hN0 : P N = 0 := by rw [hNdef, measure_toMeasurable]; exact ae_iff.1 hG
  have hNc : ∀ t, MeasurableSet[usualAugmentation 𝓕 P t] Nᶜ := fun t =>
    (Ito.measurableSet_usualAugmentation_of_null hNm hN0 t).compl
  have hae : ∀ t, (fun ω => Nᶜ.indicator (M t) ω) =ᵐ[P] M t := fun t => by
    filter_upwards [(measure_eq_zero_iff_ae_notMem.1 hN0)] with ω hω
    exact Set.indicator_of_mem hω _
  refine ⟨fun t => (hM.1 t).indicator (hNc t), fun s t hst => ?_⟩
  filter_upwards [condExp_congr_ae (m := usualAugmentation 𝓕 P s) (hae t), hM.2 s t hst, hae s]
    with ω h1 h2 h3
  rw [h1, h2, h3]

/-- **`L²` orthogonality of a martingale and its stopped version** (optional sampling): if `Z_N = Y_{N ∧ ρ}`,
then `E (Y_N − Z_N)² = E Y_N² − E Z_N²`. -/
theorem integral_sq_sub_eq_of_stopped [IsProbabilityMeasure P] {𝓖 : Filtration ℝ≥0 mΩ}
    {Y : ℝ≥0 → Ω → ℝ} (hY : Martingale Y 𝓖 P) (hYrc : ∀ ω t, ContinuousWithinAt (Y · ω) (Ici t) t)
    {C : ℝ} (hYb : ∀ t ω, |Y t ω| ≤ C) {ρ : Ω → ℝ≥0}
    (hρ : IsStoppingTime 𝓖 fun ω => (ρ ω : WithTop ℝ≥0)) {N : ℝ≥0} {Z : Ω → ℝ}
    (hZ : ∀ ω, Z ω = Y (min N (ρ ω)) ω) :
    ∫ ω, (Y N ω - Z ω) ^ 2 ∂P = ∫ ω, Y N ω ^ 2 ∂P - ∫ ω, Z ω ^ 2 ∂P := by
  have hτ : IsStoppingTime 𝓖 fun ω => ((min N (ρ ω) : ℝ≥0) : WithTop ℝ≥0) := by
    have := (isStoppingTime_const 𝓖 N).min hρ
    simpa only [WithTop.coe_min] using this
  have hσ : IsStoppingTime 𝓖 fun _ : Ω => ((N : ℝ≥0) : WithTop ℝ≥0) := isStoppingTime_const 𝓖 N
  have hos := Martingale.stoppedValue_ae_eq_condExp_of_rightContinuous hY hYrc hτ hσ
    (fun ω => WithTop.coe_le_coe.2 (min_le_left N (ρ ω))) (T := N) (fun _ => le_rfl)
  have hmle : hτ.measurableSpace ≤ mΩ := hτ.measurableSpace_le
  set g := P[Y N | hτ.measurableSpace] with hg
  have hsv : ∀ ω, stoppedValue Y (fun ω => ((min N (ρ ω) : ℝ≥0) : WithTop ℝ≥0)) ω = Z ω := fun ω => by
    rw [hZ]; rfl
  have hsvN : stoppedValue Y (fun _ : Ω => ((N : ℝ≥0) : WithTop ℝ≥0)) = Y N := rfl
  rw [hsvN] at hos
  have hZg : Z =ᵐ[P] g := by
    filter_upwards [hos] with ω h
    rw [← hsv ω, h]
  have hYm : StronglyMeasurable[mΩ] (Y N) := (hY.1 N).mono (𝓖.le N)
  have hYi : Integrable (Y N) P :=
    Integrable.of_bound hYm.aestronglyMeasurable C (Eventually.of_forall fun ω => hYb N ω)
  have hZb : ∀ ω, |Z ω| ≤ C := fun ω => by rw [hZ]; exact hYb _ _
  have hZi : Integrable Z P :=
    Integrable.of_bound (integrable_condExp.aestronglyMeasurable.congr hZg.symm) C
      (Eventually.of_forall hZb)
  have hgm : StronglyMeasurable[hτ.measurableSpace] g := stronglyMeasurable_condExp
  have hgi : Integrable g P := integrable_condExp
  have hYg : Integrable (Y N * g) P := hgi.bdd_mul hYm.aestronglyMeasurable
    (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hYb N ω)
  -- `E[Y_N g] = E[g²]`
  have hpull : ∫ ω, (Y N * g) ω ∂P = ∫ ω, (g * g) ω ∂P := by
    rw [← integral_condExp hmle (f := Y N * g)]
    refine integral_congr_ae ?_
    filter_upwards [condExp_mul_of_stronglyMeasurable_right hgm hYg hYi] with ω h
    rw [h]
  have hYZ : ∫ ω, Y N ω * Z ω ∂P = ∫ ω, Z ω ^ 2 ∂P := by
    have e1 : ∫ ω, Y N ω * Z ω ∂P = ∫ ω, (Y N * g) ω ∂P := integral_congr_ae (by
      filter_upwards [hZg] with ω h; simp [h])
    have e2 : ∫ ω, Z ω ^ 2 ∂P = ∫ ω, (g * g) ω ∂P := integral_congr_ae (by
      filter_upwards [hZg] with ω h; simp [h, sq])
    rw [e1, e2, hpull]
  have hi1 : Integrable (fun ω => Y N ω ^ 2) P := by
    refine Integrable.of_bound (hYm.aestronglyMeasurable.pow 2) (C ^ 2) (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hYb N ω) 2
  have hi2 : Integrable (fun ω => Z ω ^ 2) P := by
    refine Integrable.of_bound (hZi.aestronglyMeasurable.pow 2) (C ^ 2) (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hZb ω) 2
  have hi3 : Integrable (fun ω => Y N ω * Z ω) P := hZi.bdd_mul hYm.aestronglyMeasurable
    (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hYb N ω)
  have hexp : (fun ω => (Y N ω - Z ω) ^ 2) = fun ω => Y N ω ^ 2 - 2 * (Y N ω * Z ω) + Z ω ^ 2 := by
    funext ω; ring
  have e1 : ∫ ω, (Y N ω ^ 2 - 2 * (Y N ω * Z ω) + Z ω ^ 2) ∂P =
      ∫ ω, (Y N ω ^ 2 - 2 * (Y N ω * Z ω)) ∂P + ∫ ω, Z ω ^ 2 ∂P :=
    integral_add (hi1.sub (hi3.const_mul 2)) hi2
  have e2 : ∫ ω, (Y N ω ^ 2 - 2 * (Y N ω * Z ω)) ∂P =
      ∫ ω, Y N ω ^ 2 ∂P - ∫ ω, 2 * (Y N ω * Z ω) ∂P := integral_sub hi1 (hi3.const_mul 2)
  have e3 : ∫ ω, 2 * (Y N ω * Z ω) ∂P = 2 * ∫ ω, Y N ω * Z ω ∂P := integral_const_mul _ _
  rw [hexp, e1, e2, e3, hYZ]
  ring

/-- **Weak-type maximal bound in `L²` form**: for a right-continuous martingale `D` and `δ > 0`,
`P(ε ≤ sup_{t ≤ N} |D_t|) ≤ (E D_N² / δ + δ) / (2ε)`. -/
theorem measureReal_iSup_ge_le [IsProbabilityMeasure P] {𝓖 : Filtration ℝ≥0 mΩ}
    {D : ℝ≥0 → Ω → ℝ} (hD : Martingale D 𝓖 P) (hDrc : ∀ ω, IsRightContinuous (D · ω)) (N : ℝ≥0)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hint : Integrable (fun ω => D N ω ^ 2) P) :
    P.real {ω | ε ≤ ⨆ i : Iic N, ‖D i ω‖} ≤ ((∫ ω, D N ω ^ 2 ∂P) / δ + δ) / (2 * ε) := by
  have hmax := ProbabilityTheory.maximal_ineq_norm hD ε N hDrc
  have hDi : Integrable (D N) P := hD.integrable N
  have h1 : ∫ ω in {ω | ε ≤ ⨆ i : Iic N, ‖D i ω‖}, ‖D N ω‖ ∂P ≤ ∫ ω, ‖D N ω‖ ∂P :=
    setIntegral_le_integral hDi.norm (Eventually.of_forall fun ω => norm_nonneg _)
  have h2 : ∫ ω, ‖D N ω‖ ∂P ≤ ∫ ω, (D N ω ^ 2 / δ + δ) / 2 ∂P := by
    refine integral_mono hDi.norm ((hint.div_const δ).add (integrable_const δ) |>.div_const 2)
      fun ω => ?_
    have h := sq_nonneg (|D N ω| - δ)
    rw [Real.norm_eq_abs]
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    have hsq : |D N ω| ^ 2 = D N ω ^ 2 := sq_abs _
    have : 2 * δ * |D N ω| ≤ D N ω ^ 2 + δ ^ 2 := by nlinarith
    have hdiv : D N ω ^ 2 / δ + δ = (D N ω ^ 2 + δ ^ 2) / δ := by field_simp
    rw [hdiv, le_div_iff₀ hδ]
    nlinarith
  have h3 : ∫ ω, (D N ω ^ 2 / δ + δ) / 2 ∂P = ((∫ ω, D N ω ^ 2 ∂P) / δ + δ) / 2 := by
    rw [integral_div, integral_add (hint.div_const δ) (integrable_const δ), integral_div,
      integral_const, probReal_univ, one_smul]
  rw [smul_eq_mul] at hmax
  rw [le_div_iff₀ (by positivity)]
  have := hmax.trans (h1.trans (h2.trans h3.le))
  nlinarith

end Helpers

/-! ### The frozen mean of one point is a martingale -/

section Frozen

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

theorem meanBound_nonneg (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) : 0 ≤ meanBound ρL ρR :=
  (abs_nonneg _).trans (abs_condMean_le ρL ρR 0 0 0)

/-- **Lemma 3.5 (one point): the frozen mean.** For a deterministic `z ∈ ℍ` and a bounded stopping time
`σ₀ < T` of the usual augmentation: almost surely, on `{s(z) ≤ σ₀}` the mean `η_r(z)` converges as `r ↑ s(z)`
to the frozen value `η̄_{σ₀}(z)`; and `t ↦ η̄_{t ∧ σ₀}(z)` agrees almost surely with a martingale. -/
theorem exists_martingale_frozenMean [IsProbabilityMeasure P]
    (hE : IsMarkedChain xL xR ρL ρR P 𝓕 W VL VR B ζ) {z : ℂ} (hz : 0 < z.im) {σ₀ : Ω → ℝ≥0}
    (hσ₀ : IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (σ₀ ω : WithTop ℝ≥0))
    (hσ₀ζ : ∀ᵐ ω ∂P, (σ₀ ω : ℝ≥0∞) < ζ ω) {N : ℝ≥0} (hσ₀N : ∀ ω, σ₀ ω ≤ N) :
    (∀ᵐ ω ∂P, swallowTime (Ito.rpath (W · ω)) z ≤ σ₀ ω →
      Tendsto (fun r => meanAt ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) r z)
        (𝓝[<] (swallowTime (Ito.rpath (W · ω)) z).toNNReal)
        (𝓝 (frozenMean ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) (σ₀ ω) z))) ∧
    ∃ M : ℝ≥0 → Ω → ℝ, Martingale M (usualAugmentation 𝓕 P) P ∧ ∀ᵐ ω ∂P, ∀ t,
      M t ω = frozenMean ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω))
        (min t (σ₀ ω)) z := by
  set η : Ω → ℝ≥0 → ℝ := fun ω r =>
    meanAt ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) r z with hηdef
  set C := meanBound ρL ρR with hCdef
  have hC0 : 0 ≤ C := meanBound_nonneg ρL ρR
  have hηb : ∀ ω r, |η ω r| ≤ C := fun ω r => abs_condMean_le _ _ _ _ _
  obtain ⟨ρ, hst, hle, hmono, hprot, hex, hM⟩ := exists_localizing_meanAt hE hz
    (σ₀ := fun _ => σ₀) (fun _ => hσ₀) (fun ω => monotone_const) (fun _ => hσ₀ζ)
  choose M hMm hMe using fun n => (hM n).1
  -- the good set of paths
  set G : Set Ω := {ω | IsIntegratedSLEPath 4 xL xR ρL ρR (W · ω) (fun i => (VL i · ω))
      (fun i => (VR i · ω)) (B · ω) (ζ ω) ∧
    (∀ n, (ρ n ω : ℝ≥0∞) < ζ ω ∧ ∃ v, IsForwardSol (Ito.rpath (W · ω)) z (ρ n ω) v) ∧
    (∀ (j : ℕ) (t : ℝ≥0), t ≤ σ₀ ω → (∃ v, IsForwardSol (Ito.rpath (W · ω)) z t v) →
      ∀ᶠ n in atTop, t ≤ ρ n ω) ∧
    ∀ n t, M n t ω = η ω (min t (ρ n ω))} with hGdef
  have hG : ∀ᵐ ω ∂P, ω ∈ G := by
    filter_upwards [hE.2.2.2.2, ae_all_iff.2 hprot, hex, ae_all_iff.2 hMe] with ω h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  set N0 := toMeasurable P Gᶜ with hN0def
  have hN0c : ∀ ω, ω ∉ N0 → ω ∈ G := fun ω hω => by
    by_contra h
    exact hω (subset_toMeasurable _ _ h)
  have hN00 : P N0 = 0 := by rw [hN0def, measure_toMeasurable]; exact ae_iff.1 hG
  -- continuous versions
  set Y : ℕ → ℝ≥0 → Ω → ℝ := fun n t => N0ᶜ.indicator (M n t) with hYdef
  have hYmart : ∀ n, Martingale (Y n) (usualAugmentation 𝓕 P) P := fun n =>
    martingale_indicator_compl_toMeasurable (hMm n) hG
  have hYval : ∀ n t ω, ω ∉ N0 → Y n t ω = η ω (min t (ρ n ω)) := fun n t ω hω => by
    simp only [hYdef, Set.indicator_of_mem (show ω ∈ N0ᶜ from hω)]
    exact (hN0c ω hω).2.2.2 n t
  have hYzero : ∀ n t ω, ω ∈ N0 → Y n t ω = 0 := fun n t ω hω =>
    Set.indicator_of_notMem (by simpa using hω) _
  have hYb : ∀ n t ω, |Y n t ω| ≤ C := fun n t ω => by
    by_cases hω : ω ∈ N0
    · rw [hYzero n t ω hω, abs_zero]; exact hC0
    · rw [hYval n t ω hω]; exact hηb _ _
  have hYc : ∀ n ω, Continuous fun t => Y n t ω := by
    intro n ω
    by_cases hω : ω ∈ N0
    · simp only [hYzero n _ ω hω]; exact continuous_const
    · have hg := hN0c ω hω
      simp only [hYval n _ ω hω]
      have hcont := continuousOn_meanAt (ρL := ρL) (ρR := ρR) hg.1 (hg.2.1 n).1 hz (hg.2.1 n).2
      exact hcont.comp_continuous (continuous_id.min continuous_const)
        fun t => ⟨bot_le, min_le_right _ _⟩
  have hYrc : ∀ n ω t, ContinuousWithinAt (Y n · ω) (Ici t) t := fun n ω t =>
    (hYc n ω).continuousWithinAt
  have hconsist : ∀ n m, n ≤ m → ∀ t ω, Y n t ω = Y m (min t (ρ n ω)) ω := by
    intro n m hnm t ω
    by_cases hω : ω ∈ N0
    · rw [hYzero _ _ _ hω, hYzero _ _ _ hω]
    · rw [hYval _ _ _ hω, hYval _ _ _ hω, min_assoc, min_eq_left (hmono ω hnm)]
  have hstab : ∀ n m, n ≤ m → ∀ t ω, Y n (min t (ρ m ω)) ω = Y n t ω := by
    intro n m hnm t ω
    by_cases hω : ω ∈ N0
    · rw [hYzero _ _ _ hω, hYzero _ _ _ hω]
    · rw [hYval _ _ _ hω, hYval _ _ _ hω, min_assoc, min_eq_right (hmono ω hnm)]
  -- the `L²` norms at the horizon `N`
  set a : ℕ → ℝ := fun n => ∫ ω, Y n N ω ^ 2 ∂P with hadef
  have horth : ∀ n m, n ≤ m → ∫ ω, (Y m N ω - Y n N ω) ^ 2 ∂P = a m - a n := fun n m hnm =>
    integral_sq_sub_eq_of_stopped (hYmart m) (hYrc m) (hYb m) (hst n) (hconsist n m hnm N)
  have hsqb : ∀ n ω, Y n N ω ^ 2 ≤ C ^ 2 := fun n ω => by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hYb n N ω) 2
  have ha_le : ∀ n, a n ≤ C ^ 2 := fun n => by
    have : ∫ ω, Y n N ω ^ 2 ∂P ≤ ∫ _ω, C ^ 2 ∂P :=
      integral_mono_of_nonneg (Eventually.of_forall fun ω => sq_nonneg _) (integrable_const _)
        (Eventually.of_forall (hsqb n))
    simpa using this
  have ha_mono : Monotone a := fun n m hnm => by
    have h := horth n m hnm
    have : 0 ≤ ∫ ω, (Y m N ω - Y n N ω) ^ 2 ∂P := integral_nonneg fun ω => sq_nonneg _
    linarith
  have ha_bdd : BddAbove (range a) := ⟨C ^ 2, by rintro _ ⟨n, rfl⟩; exact ha_le n⟩
  have ha_tend : Tendsto a atTop (𝓝 (⨆ n, a n)) := tendsto_atTop_ciSup ha_mono ha_bdd
  -- the oscillations
  set osc : ℕ → ℕ → Ω → ℝ := fun n m ω => ⨆ i : Iic N, ‖Y m i ω - Y n i ω‖ with hoscdef
  have hosc_bdd : ∀ n m ω, BddAbove (range fun i : Iic N => ‖Y m i ω - Y n i ω‖) := fun n m ω =>
    ⟨2 * C, by
      rintro _ ⟨i, rfl⟩
      show ‖Y m i ω - Y n i ω‖ ≤ 2 * C
      rw [Real.norm_eq_abs]
      have := abs_sub (Y m i ω) (Y n i ω)
      linarith [hYb m i ω, hYb n i ω]⟩
  have hosc_mono : ∀ n m m' ω, n ≤ m → m ≤ m' → osc n m ω ≤ osc n m' ω := by
    intro n m m' ω hnm hmm'
    refine ciSup_le fun i => ?_
    refine le_ciSup_of_le (hosc_bdd n m' ω)
      ⟨min i (ρ m ω), Set.mem_Iic.2 ((min_le_left _ _).trans (Set.mem_Iic.1 i.2))⟩ ?_
    show ‖Y m i ω - Y n i ω‖ ≤ ‖Y m' (min i (ρ m ω)) ω - Y n (min i (ρ m ω)) ω‖
    rw [← hconsist m m' hmm' i ω, hstab n m hnm i ω]
  have hprob : ∀ n m, n ≤ m → ∀ ε δ : ℝ, 0 < ε → 0 < δ →
      P.real {ω | ε ≤ osc n m ω} ≤ ((a m - a n) / δ + δ) / (2 * ε) := by
    intro n m hnm ε δ hε hδ
    have hD := (hYmart m).sub (hYmart n)
    have hDrc : ∀ ω, IsRightContinuous ((Y m - Y n) · ω) := fun ω t =>
      (((hYc m ω).sub (hYc n ω)).continuousAt (x := t)).continuousWithinAt
    have hDb : ∀ ω, |(Y m - Y n) N ω| ≤ 2 * C := fun ω => by
      simp only [Pi.sub_apply]
      have := abs_sub (Y m N ω) (Y n N ω)
      linarith [hYb m N ω, hYb n N ω]
    have hDint : Integrable (fun ω => (Y m - Y n) N ω ^ 2) P := by
      refine Integrable.of_bound ((((hYmart m).1 N).mono (Filtration.le _ N)).aestronglyMeasurable.sub
        (((hYmart n).1 N).mono (Filtration.le _ N)).aestronglyMeasurable |>.pow 2) ((2 * C) ^ 2)
        (Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hDb ω) 2
    have h := measureReal_iSup_ge_le hD hDrc N hε hδ hDint
    simp only [Pi.sub_apply] at h
    rwa [horth n m hnm] at h
  -- almost surely the oscillations are eventually small
  have hosc_ae : ∀ᵐ ω ∂P, ∀ k : ℕ, ∃ n, ∀ m, n ≤ m → osc n m ω < 1 / ((k : ℝ) + 1) := by
    rw [ae_all_iff]
    intro k
    set ε : ℝ := 1 / ((k : ℝ) + 1) with hεdef
    have hε : 0 < ε := by positivity
    set Bad : Set Ω := ⋂ n, ⋃ j, {ω | ε ≤ osc n (n + j) ω} with hBad
    have hBadle : ∀ n δ, 0 < δ → P.real Bad ≤ (((⨆ n, a n) - a n) / δ + δ) / (2 * ε) := by
      intro n δ hδ
      have hmonoS : Monotone fun j => {ω | ε ≤ osc n (n + j) ω} := fun j j' hjj' ω hω =>
        le_trans hω (hosc_mono n (n + j) (n + j') ω (Nat.le_add_right _ _) (by omega))
      have hbound : 0 ≤ (((⨆ n, a n) - a n) / δ + δ) / (2 * ε) := by
        have : a n ≤ ⨆ n, a n := le_ciSup ha_bdd n
        have : 0 ≤ (⨆ n, a n) - a n := by linarith
        positivity
      have hU : P (⋃ j, {ω | ε ≤ osc n (n + j) ω}) ≤
          ENNReal.ofReal ((((⨆ n, a n) - a n) / δ + δ) / (2 * ε)) := by
        rw [hmonoS.measure_iUnion]
        refine iSup_le fun j => ?_
        rw [← ofReal_measureReal (measure_ne_top _ _)]
        refine ENNReal.ofReal_le_ofReal ((hprob n (n + j) (Nat.le_add_right _ _) ε δ hε hδ).trans ?_)
        have : a (n + j) ≤ ⨆ n, a n := le_ciSup ha_bdd _
        gcongr
      have h1 : P.real Bad ≤ P.real (⋃ j, {ω | ε ≤ osc n (n + j) ω}) :=
        measureReal_mono (iInter_subset _ n)
      exact h1.trans (ENNReal.toReal_le_of_le_ofReal hbound hU)
    have hBad0 : P.real Bad ≤ 0 := by
      by_contra hpos
      push Not at hpos
      set p := P.real Bad
      have hδ : 0 < ε * p := mul_pos hε hpos
      have hlim : Tendsto (fun n => (((⨆ n, a n) - a n) / (ε * p) + ε * p) / (2 * ε)) atTop
          (𝓝 ((((⨆ n, a n) - (⨆ n, a n)) / (ε * p) + ε * p) / (2 * ε))) :=
        (((tendsto_const_nhds.sub ha_tend).div_const _).add_const _).div_const _
      have := ge_of_tendsto' hlim fun n => hBadle n (ε * p) hδ
      rw [sub_self, zero_div, zero_add] at this
      have : p ≤ p / 2 := by
        calc p ≤ ε * p / (2 * ε) := this
          _ = p / 2 := by field_simp
      linarith
    have hBadz : P Bad = 0 :=
      (measureReal_eq_zero_iff (measure_ne_top _ _)).1 (le_antisymm hBad0 measureReal_nonneg)
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hBadz] with ω hω
    simp only [hBad, mem_iInter, mem_iUnion, mem_ofPred_eq, not_forall, not_exists, not_le] at hω
    obtain ⟨n, hn⟩ := hω
    refine ⟨n, fun m hnm => ?_⟩
    have := hn (m - n)
    rwa [Nat.add_sub_cancel' hnm] at this
  -- the pathwise conclusions
  have hpath : ∀ ω, ω ∉ N0 → (∀ k : ℕ, ∃ n, ∀ m, n ≤ m → osc n m ω < 1 / ((k : ℝ) + 1)) →
      (swallowTime (Ito.rpath (W · ω)) z ≤ σ₀ ω →
        Tendsto (η ω) (𝓝[<] (swallowTime (Ito.rpath (W · ω)) z).toNNReal)
          (𝓝 (limUnder (𝓝[<] (swallowTime (Ito.rpath (W · ω)) z).toNNReal) (η ω)))) ∧
      ∀ t : ℝ≥0, Tendsto (fun n => η ω (min t (ρ n ω))) atTop
        (𝓝 (if ((min t (σ₀ ω) : ℝ≥0) : ℝ≥0∞) < swallowTime (Ito.rpath (W · ω)) z then
          η ω (min t (σ₀ ω)) else
          limUnder (𝓝[<] (swallowTime (Ito.rpath (W · ω)) z).toNNReal) (η ω))) := by
    intro ω hω hk
    have hg := hN0c ω hω
    refine tendsto_frozen_of_osc (f := η ω) (ρ := fun n => ρ n ω) (σ := σ₀ ω)
      (fun n => lt_swallowTime_of_path hg.1 (hg.2.1 n).1 hz (hg.2.1 n).2) (fun n => hle n ω)
      (fun t ht htS => hg.2.2.1 0 t ht ?_) ?_
    · refine QuantumZipper.exists_isForwardSol_of_not_mem_fwdHull t.coe_nonneg hz fun h => ?_
      have := h.2
      rw [ENNReal.ofReal_coe_nnreal] at this
      exact absurd htS (not_lt.2 this)
    · intro ε hε
      obtain ⟨k, hk'⟩ := exists_nat_one_div_lt hε
      obtain ⟨n, hn⟩ := hk k
      refine ⟨n, fun m r hr hrm => ?_⟩
      rcases le_or_gt n m with hnm | hmn
      · have hrN : r ≤ N := hrm.trans ((hle m ω).trans (hσ₀N ω))
        have h1 : Y m r ω = η ω r := by rw [hYval m r ω hω, min_eq_left hrm]
        have h2 : Y n r ω = η ω (ρ n ω) := by rw [hYval n r ω hω, min_eq_right hr]
        have hle' : |η ω r - η ω (ρ n ω)| ≤ osc n m ω := by
          rw [← h1, ← h2, ← Real.norm_eq_abs]
          exact le_ciSup (f := fun i : Iic N => ‖Y m i ω - Y n i ω‖) (hosc_bdd n m ω) ⟨r, hrN⟩
        exact hle'.trans_lt ((hn m hnm).trans hk')
      · have : r = ρ n ω := le_antisymm (hrm.trans (hmono ω hmn.le)) hr
        rw [this, sub_self, abs_zero]; exact hε
  -- the frozen martingale
  set G' : Set Ω := {ω | ω ∉ N0 ∧ ∀ k : ℕ, ∃ n, ∀ m, n ≤ m → osc n m ω < 1 / ((k : ℝ) + 1)}
    with hG'def
  have hG' : ∀ᵐ ω ∂P, ω ∈ G' := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN00, hosc_ae] with ω h1 h2
    exact ⟨h1, h2⟩
  set N1 := toMeasurable P G'ᶜ with hN1def
  have hN1c : ∀ ω, ω ∉ N1 → ω ∈ G' := fun ω hω => by
    by_contra h
    exact hω (subset_toMeasurable _ _ h)
  have hN10 : P N1 = 0 := by rw [hN1def, measure_toMeasurable]; exact ae_iff.1 hG'
  refine ⟨?_, ?_⟩
  · filter_upwards [hG'] with ω hω hS
    have hfr : frozenMean ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) (σ₀ ω) z =
        limUnder (𝓝[<] (swallowTime (Ito.rpath (W · ω)) z).toNNReal) (η ω) := by
      simp only [frozenMean, not_lt.2 hS, ↓reduceIte]
      rfl
    rw [hfr]
    exact ((hpath ω hω.1 hω.2).1 hS)
  set Y' : ℕ → ℝ≥0 → Ω → ℝ := fun n t => N1ᶜ.indicator (Y n t) with hY'def
  have hY'mart : ∀ n, Martingale (Y' n) (usualAugmentation 𝓕 P) P := fun n =>
    martingale_indicator_compl_toMeasurable (hYmart n) hG'
  set Mt : ℝ≥0 → Ω → ℝ := fun t => N1ᶜ.indicator (fun ω =>
    frozenMean ρL ρR (W · ω) (fun i => (VL i · ω)) (fun i => (VR i · ω)) (min t (σ₀ ω)) z)
    with hMtdef
  have hconv : ∀ t ω, Tendsto (fun n => Y' n t ω) atTop (𝓝 (Mt t ω)) := by
    intro t ω
    by_cases hω : ω ∈ N1
    · simp only [hY'def, hMtdef, Set.indicator_of_notMem (show ω ∉ N1ᶜ from fun h => h hω)]
      exact tendsto_const_nhds
    · have hg := hN1c ω hω
      simp only [hY'def, hMtdef, Set.indicator_of_mem (show ω ∈ N1ᶜ from hω)]
      have h := (hpath ω hg.1 hg.2).2 t
      refine (h.congr fun n => (hYval n t ω hg.1).symm).trans (le_of_eq ?_)
      rfl
  have hMtb : ∀ t ω, |Mt t ω| ≤ C := fun t ω =>
    le_of_tendsto ((continuous_abs.tendsto _).comp (hconv t ω)) (Eventually.of_forall fun n => by
      simp only [Function.comp, hY'def]
      by_cases hω : ω ∈ N1ᶜ
      · rw [Set.indicator_of_mem hω]; exact hYb n t ω
      · rw [Set.indicator_of_notMem hω, abs_zero]; exact hC0)
  have hMtad : ∀ t, StronglyMeasurable[usualAugmentation 𝓕 P t] (Mt t) := fun t =>
    stronglyMeasurable_of_tendsto atTop (fun n => (hY'mart n).1 t) (tendsto_pi_nhds.2 (hconv t))
  have hMti : ∀ t, Integrable (Mt t) P := fun t =>
    Integrable.of_bound ((hMtad t).mono (Filtration.le _ t)).aestronglyMeasurable C
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hMtb t ω)
  have hY'b : ∀ n t ω, ‖Y' n t ω‖ ≤ C := fun n t ω => by
    rw [Real.norm_eq_abs]
    simp only [hY'def]
    by_cases hω : ω ∈ N1ᶜ
    · rw [Set.indicator_of_mem hω]; exact hYb n t ω
    · rw [Set.indicator_of_notMem hω, abs_zero]; exact hC0
  have hsetlim : ∀ t (A : Set Ω), Tendsto (fun n => ∫ ω in A, Y' n t ω ∂P) atTop
      (𝓝 (∫ ω in A, Mt t ω ∂P)) := fun t A =>
    tendsto_integral_of_dominated_convergence (fun _ => C)
      (fun n => (((hY'mart n).1 t).mono (Filtration.le _ t)).aestronglyMeasurable)
      (integrable_const C) (fun n => Eventually.of_forall fun ω => hY'b n t ω)
      (Eventually.of_forall fun ω => hconv t ω)
  refine ⟨Mt, ⟨hMtad, fun s t hst => ?_⟩, ?_⟩
  · refine (ae_eq_condExp_of_forall_setIntegral_eq (Filtration.le _ s) (hMti t)
      (fun A _ _ => (hMti s).integrableOn) (fun A hA _ => ?_)
      ((hMtad s).aestronglyMeasurable)).symm
    refine tendsto_nhds_unique (hsetlim s A) ((hsetlim t A).congr fun n => ?_)
    exact ((hY'mart n).setIntegral_eq hst hA).symm
  · filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN10] with ω hω t
    simp only [hMtdef, Set.indicator_of_mem (show ω ∈ N1ᶜ from hω)]

end Frozen

end WangWu

end InteractingSLE
