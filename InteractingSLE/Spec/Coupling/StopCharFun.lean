import InteractingSLE.Spec.Coupling.SafeCompact
import InteractingSLE.Spec.Ito.Filtration

/-!
# The characteristic-function martingale at arbitrary stopping times

Packet PROVE-T11-L312 (Specification §3.3, L550–L586; graph nodes `SPEC.thm-1.1#charfn-martingale`,
`SPEC.lem-3.11`). For a test function `ψ` on `ℍ`, the process
`exp(iθ (𝔥_t, ψ) − θ² E_t(ψ)/2)` is a bounded martingale as long as `supp ψ` is not swallowed and `t < T_*`. Here this
is proved in the form of optional stopping between two arbitrary stopping times `σ ≤ τ` of the usual augmentation,
with `τ < ζ` and `supp ψ ∩ K_τ = ∅` almost surely (the source's `τ < τ_U ∧ T_*`, `supp ψ ⊆ U`):
`∫_S exp(iθ (𝔥_τ, ψ) − θ² E_τ(ψ)/2) = ∫_S exp(iθ (𝔥_σ, ψ) − θ² E_σ(ψ)/2)` for `S ∈ 𝓕_σ`.

Proof: at the safe stops `ρ_n` (`exists_safeSeq_of_seq`, below the truncations `τ ∧ n`) the identity between `σ ∧ ρ_n`
and `ρ_n` follows from the unconditional identity of PROVE-T11-L311 at the stopping time equal to `ρ_n` on
`S ∩ {σ ≤ ρ_n}` and to `σ ∧ ρ_n` elsewhere; then `ρ_n = τ` for large `n`, and dominated convergence applies since the
integrands have modulus at most one (`loewnerGreenEnergy_nonneg`).

## Main results

* `cfAt`: `exp(iθ (𝔥_r, φ) − θ² E_r(φ)/2)` at a random time `r`;
* `integral_cfAt_eq_of_safe`: `E[cfAt σ] = E[cfAt 0]` at a safe stop;
* `setIntegral_cfAt_eq_of_safe_le`: optional stopping between two safe stops;
* **`setIntegral_cfAt_eq_of_le`**: optional stopping between arbitrary stopping times `σ ≤ τ < ζ ∧ τ_{supp ψ}`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology QuantumZipper
open scoped NNReal ENNReal Classical

namespace InteractingSLE

namespace Coupling

open Ito

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {nL nR : ℕ}
  {κ : ℝ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {φ : ℂ → ℝ} {δ N : ℝ}

/-- `exp(iθ (𝔥_r, φ) − θ² E_r(φ)/2)` at the random time `r`. -/
def cfAt (κ : ℝ) (W : ℝ≥0 → Ω → ℝ) (u : Ω → ℝ≥0 → ℂ → ℝ) (φ : ℂ → ℝ) (θ : ℝ) (r : Ω → ℝ≥0)
    (ω : Ω) : ℂ :=
  Complex.exp (Complex.I * θ *
    ((∫ z, couplingMean κ (fun s : ℝ => W s.toNNReal ω) (r ω) (u ω (r ω)) z * φ z : ℝ) : ℂ) -
    θ ^ 2 * ((loewnerGreenEnergy (fun s : ℝ => W s.toNNReal ω) (r ω) φ : ℝ) : ℂ) / 2)

theorem cfTest_eq_cfAt (u : Ω → ℝ≥0 → ℂ → ℝ) (θ : ℝ) {σ : Ω → ℝ≥0} {t : ℝ≥0} {ω : Ω}
    (h : σ ω ≤ t) : cfTest κ W u φ σ θ t ω = cfAt κ W u φ θ σ ω := by
  simp only [cfTest, cfAt, min_eq_right h]

theorem cfTest_zero_eq_cfAt (u : Ω → ℝ≥0 → ℂ → ℝ) (θ : ℝ) (σ : Ω → ℝ≥0) (ω : Ω) :
    cfTest κ W u φ σ θ 0 ω = cfAt κ W u φ θ (fun _ => 0) ω := by
  simp only [cfTest, cfAt, min_eq_left (zero_le (a := σ ω))]

theorem cfAt_congr (u : Ω → ℝ≥0 → ℂ → ℝ) (θ : ℝ) {r r' : Ω → ℝ≥0} {ω : Ω} (h : r ω = r' ω) :
    cfAt κ W u φ θ r ω = cfAt κ W u φ θ r' ω := by
  simp only [cfAt, h]

/-- **`|cfAt| ≤ 1` while `supp ψ` is alive**: for a path continuous on `[0, r]` with `W 0 = 0` and every point of
`supp ψ` alive at `r`, `E_r(ψ) ≥ 0`. -/
theorem norm_cfAt_le_one (u : Ω → ℝ≥0 → ℂ → ℝ) (θ : ℝ) (ψ : LQGMetric.TestOn upperHalfPlaneOpens)
    {r : Ω → ℝ≥0} {ω : Ω} (hw : ContinuousOn (rpath (W · ω)) (Icc 0 (r ω : ℝ))) (hw0 : W 0 ω = 0)
    (halive : ∀ z ∈ tsupport ψ, ∃ v, IsForwardSol (rpath (W · ω)) z (r ω) v) :
    ‖cfAt κ W u ψ θ r ω‖ ≤ 1 := by
  have hc := continuous_clampDrv (r ω).coe_nonneg hw
  have h0 : clampDrv (rpath (W · ω)) (r ω) 0 = 0 := by
    simp [clampDrv, rpath, hw0]
  have hdis : Disjoint (tsupport ψ) (fwdHull (clampDrv (rpath (W · ω)) (r ω)) (r ω)) :=
    Set.disjoint_left.2 fun z hz =>
      (mem_diff_fwdHull_clampDrv (r ω).coe_nonneg hw (tsupport_subset_H ψ hz) (halive z hz)).2
  have hE := loewnerGreenEnergy_nonneg hc h0 (r ω).coe_nonneg ψ hdis
  have he : loewnerGreenEnergy (clampDrv (rpath (W · ω)) (r ω)) (r ω) ψ =
      loewnerGreenEnergy (fun s : ℝ => W s.toNNReal ω) (r ω) ψ := by
    simp only [loewnerGreenEnergy, fwdMap_clampDrv_of_le le_rfl]
    rfl
  rw [he] at hE
  exact norm_cexp_testMean_le_one θ _ hE

/-! ### Safe stops of the null-augmented filtration -/

section SafeMain

variable (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hκ : 0 < κ)
  (u : Ω → ℝ≥0 → ℂ → ℝ)
  (hu : ∀ ω s, IsBoundedHarmonicExtension
    (forceBoundaryData κ ρL ρR (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω))
    (forceJumpSet (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω)) (u ω s))
include hE hκ hu

/-- At a safe stop, `cfAt` is almost everywhere strongly measurable (an almost everywhere limit of the protected
stops of PROVE-T11-L311). -/
theorem aestronglyMeasurable_cfAt_of_safe {σ : Ω → ℝ≥0}
    (hσ : IsStoppingTime (nullAugmented 𝓕 P) fun ω => (σ ω : WithTop ℝ≥0))
    (hσs : ∀ᵐ ω ∂P, IsTestSafe W ζ φ σ δ N ω) (hφH : tsupport φ ⊆ H) (hφc : Continuous φ)
    (hφs : HasCompactSupport φ) (hδ : 0 < δ) (θ : ℝ) :
    AEStronglyMeasurable (cfAt κ W u φ θ σ) P := by
  obtain ⟨G, -, hGc, hG0, hGs⟩ := exists_goodSafeSet hE hσs
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by rw [ae_iff]; exact hGc
  set D₀ : ℝ := ∑ i, |xL i| + ∑ i, |xR i|
  set Nn : ℝ≥0 := N.toNNReal
  set σn : ℕ → Ω → ℝ≥0 := fun n => exitStop W VL VR B σ G n Nn with hσn_def
  have hσn : ∀ n : ℕ, IsStoppingTime (nullAugmented 𝓕 P) fun ω => (σn n ω : WithTop ℝ≥0) :=
    fun n => isStoppingTime_exitStop hE hσ hG0 hGs n Nn
  have hgood : ∀ n : ℕ, D₀ < n → ∀ ω ∈ G,
      IsGoodTest κ xL xR ρL ρR W VL VR B ζ φ (σn n) δ n N ω := fun n hn ω hω =>
    isGoodTest_of_le (hGs ω hω).1 (hGs ω hω).2.1 (hGs ω hω).2.2 hφH (exitStop_le _ _ ω)
      fun s hs => coordSize_le_of_le_exitStop hGs hω
        (by rw [(hGs ω hω).coordSize_zero hκ]; exact hn) hs
  have hprot : ∀ n : ℕ, D₀ < n → ∀ᵐ ω ∂P, IsTestProtected W VL VR B ζ φ (σn n) δ n N ω :=
    fun n hn => by filter_upwards [hGae] with ω hω; exact (hgood n hn ω hω).2.2
  have hσN : ∀ ω ∈ G, σ ω ≤ Nn := fun ω hω => by
    have h1 := Real.toNNReal_le_toNNReal (hGs ω hω).2.2.2.1
    rwa [Real.toNNReal_coe] at h1
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.1
    (tendsto_natCast_atTop_atTop.eventually_gt_atTop D₀ : ∀ᶠ n : ℕ in atTop, D₀ < n)
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable (cfAt κ W u φ θ (σn (n + a))) P := by
    intro n
    have hn := ha (n + a) (Nat.le_add_left a n)
    obtain ⟨hX, hEn⟩ := aemeasurable_testMean_energy hE hκ (hσn (n + a)) (hprot (n + a) hn) hφH hφc
      hφs hδ u hu Nn
    have hg : Measurable fun p : ℝ × ℝ =>
        Complex.exp (Complex.I * θ * (p.1 : ℂ) - θ ^ 2 * (p.2 : ℂ) / 2) := by fun_prop
    refine (hg.comp_aemeasurable (hX.prodMk hEn)).aestronglyMeasurable.congr ?_
    filter_upwards [hGae] with ω hω
    have hm : min Nn (σn (n + a) ω) = σn (n + a) ω :=
      min_eq_right ((exitStop_le _ _ ω).trans (hσN ω hω))
    simp only [Function.comp, cfAt, hm]
  refine aestronglyMeasurable_of_tendsto_ae atTop hmeas ?_
  filter_upwards [hGae] with ω hω
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [(tendsto_add_atTop_nat a).eventually (eventually_exitStop_eq hGs (G := G) (hσN ω hω))]
    with n hn
  exact cfAt_congr u θ hn.symm

/-- **The unconditional identity at a safe stop** (PROVE-T11-L311's `setIntegral_cexp_testMean_eq_of_safe` between
the times `0` and `N`): `E[cfAt σ] = E[cfAt 0]`. -/
theorem integral_cfAt_eq_of_safe {σ : Ω → ℝ≥0}
    (hσ : IsStoppingTime (nullAugmented 𝓕 P) fun ω => (σ ω : WithTop ℝ≥0))
    (hσs : ∀ᵐ ω ∂P, IsTestSafe W ζ φ σ δ N ω) (hφH : tsupport φ ⊆ H) (hφc : Continuous φ)
    (hφs : HasCompactSupport φ) (hδ : 0 < δ) (θ : ℝ) :
    ∫ ω, cfAt κ W u φ θ σ ω ∂P = ∫ ω, cfAt κ W u φ θ (fun _ => 0) ω ∂P := by
  have h := setIntegral_cexp_testMean_eq_of_safe hE hκ hσ hσs hφH hφc hφs hδ u hu
    (zero_le (a := N.toNNReal)) (S := univ) MeasurableSet.univ θ
  rw [setIntegral_univ, setIntegral_univ] at h
  have hl : ∀ᵐ ω ∂P, cfTest κ W u φ σ θ N.toNNReal ω = cfAt κ W u φ θ σ ω := by
    filter_upwards [hσs] with ω hω
    have h1 := Real.toNNReal_le_toNNReal hω.2.1
    rw [Real.toNNReal_coe] at h1
    exact cfTest_eq_cfAt u θ h1
  rw [← integral_congr_ae hl, h]
  exact integral_congr_ae (Eventually.of_forall fun ω => cfTest_zero_eq_cfAt u θ σ ω)

/-- **Optional stopping between two safe stops** `a ≤ b` (same height and horizon): for `S ∈ 𝓖_a`,
`∫_S cfAt b = ∫_S cfAt a`. The stopping time equal to `b` on `S` and to `a` off `S` is safe, and the three stops have
the same `E[cfAt ·] = E[cfAt 0]`. -/
theorem setIntegral_cfAt_eq_of_safe_le (ψ : LQGMetric.TestOn upperHalfPlaneOpens) {a b : Ω → ℝ≥0}
    (ha : IsStoppingTime (nullAugmented 𝓕 P) fun ω => (a ω : WithTop ℝ≥0))
    (hb : IsStoppingTime (nullAugmented 𝓕 P) fun ω => (b ω : WithTop ℝ≥0)) (hab : ∀ ω, a ω ≤ b ω)
    (has : ∀ᵐ ω ∂P, IsTestSafe W ζ ψ a δ N ω) (hbs : ∀ᵐ ω ∂P, IsTestSafe W ζ ψ b δ N ω)
    (hδ : 0 < δ) {S : Set Ω} (hS : MeasurableSet[ha.measurableSpace] S) (θ : ℝ) :
    ∫ ω in S, cfAt κ W u ψ θ b ω ∂P = ∫ ω in S, cfAt κ W u ψ θ a ω ∂P := by
  have hP : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  have hpath := hE.2.2.2.2
  have hφH := tsupport_subset_H ψ
  have hφc : Continuous ψ := ψ.continuous
  have hφs : HasCompactSupport ψ := ψ.hasCompactSupport
  have hSm : MeasurableSet S := ha.measurableSpace_le _ hS
  set c : Ω → ℝ≥0 := S.piecewise b a with hc_def
  have hc : IsStoppingTime (nullAugmented 𝓕 P) fun ω => (c ω : WithTop ℝ≥0) := by
    intro t
    have heq : {ω | ((c ω : ℝ≥0) : WithTop ℝ≥0) ≤ t} =
        (S ∩ {ω | (a ω : WithTop ℝ≥0) ≤ t}) ∩ {ω | (b ω : WithTop ℝ≥0) ≤ t} ∪
          (Sᶜ ∩ {ω | (a ω : WithTop ℝ≥0) ≤ t}) := by
      ext ω
      by_cases hω : ω ∈ S
      · simp only [hc_def, Set.piecewise_eq_of_mem _ _ _ hω, mem_ofPred_eq, mem_union, mem_inter_iff,
          hω, true_and, mem_compl_iff, not_true_eq_false, false_and, or_false]
        exact ⟨fun h => ⟨le_trans (by exact_mod_cast hab ω) h, h⟩, fun h => h.2⟩
      · simp only [hc_def, Set.piecewise_eq_of_notMem _ _ _ hω, mem_ofPred_eq, mem_union,
          mem_inter_iff, hω, false_and, mem_compl_iff, not_false_eq_true, true_and, false_or]
    rw [heq]
    exact ((((ha.measurableSet S).1 hS).2 t).inter (hb t)).union
      (((ha.measurableSet Sᶜ).1 hS.compl).2 t)
  have hcs : ∀ᵐ ω ∂P, IsTestSafe W ζ ψ c δ N ω := by
    filter_upwards [has, hbs] with ω h1 h2
    by_cases hω : ω ∈ S
    · have e : c ω = b ω := Set.piecewise_eq_of_mem _ _ _ hω
      unfold IsTestSafe; rw [e]; exact h2
    · have e : c ω = a ω := Set.piecewise_eq_of_notMem _ _ _ hω
      unfold IsTestSafe; rw [e]; exact h1
  have hint : ∀ r : Ω → ℝ≥0, IsStoppingTime (nullAugmented 𝓕 P) (fun ω => (r ω : WithTop ℝ≥0)) →
      (∀ᵐ ω ∂P, IsTestSafe W ζ ψ r δ N ω) → Integrable (cfAt κ W u ψ θ r) P := fun r hr hrs =>
    Integrable.of_bound (aestronglyMeasurable_cfAt_of_safe hE hκ u hu hr hrs hφH hφc hφs hδ θ) 1 (by
      filter_upwards [hrs, hpath] with ω hω hP
      exact norm_cfAt_le_one u θ ψ (continuousOn_rpath hP.2.2.2.1 hω.1) hP.1
        fun z hz => (hω.2.2 z hz).1)
  have e1 := integral_cfAt_eq_of_safe hE hκ u hu hc hcs hφH hφc hφs hδ θ
  have e2 := integral_cfAt_eq_of_safe hE hκ u hu ha has hφH hφc hφs hδ θ
  have hcpw : cfAt κ W u ψ θ c = S.piecewise (cfAt κ W u ψ θ b) (cfAt κ W u ψ θ a) := by
    funext ω
    by_cases hω : ω ∈ S
    · rw [Set.piecewise_eq_of_mem _ _ _ hω]
      exact cfAt_congr u θ (Set.piecewise_eq_of_mem _ _ _ hω)
    · rw [Set.piecewise_eq_of_notMem _ _ _ hω]
      exact cfAt_congr u θ (Set.piecewise_eq_of_notMem _ _ _ hω)
  rw [hcpw, integral_piecewise hSm (hint b hb hbs).integrableOn (hint a ha has).integrableOn] at e1
  rw [← integral_add_compl hSm (hint a ha has)] at e2
  linear_combination e1 - e2

end SafeMain

/-! ### Optional stopping at arbitrary stopping times -/

/-- A compact subset of `ℍ` lies above some positive height. -/
theorem exists_pos_le_im_of_isCompact {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ H) :
    ∃ m > 0, ∀ z ∈ K, m ≤ z.im := by
  rcases K.eq_empty_or_nonempty with he | hne
  · exact ⟨1, one_pos, fun z hz => by rw [he] at hz; exact absurd hz (notMem_empty z)⟩
  · obtain ⟨z₀, hz₀, hmin⟩ := hK.exists_isMinOn hne Complex.continuous_im.continuousOn
    exact ⟨z₀.im, hKH hz₀, fun z hz => hmin hz⟩

/-- Transport of a stopped σ-algebra along an equality of filtrations and stopping times. -/
theorem measurableSet_stopping_congr {𝓖₁ 𝓖₂ : Filtration ℝ≥0 mΩ} (h𝓖 : 𝓖₁ = 𝓖₂)
    {τ₁ τ₂ : Ω → WithTop ℝ≥0} (hτ : τ₁ = τ₂) (h1 : IsStoppingTime 𝓖₁ τ₁) (h2 : IsStoppingTime 𝓖₂ τ₂)
    {S : Set Ω} (hS : MeasurableSet[h1.measurableSpace] S) : MeasurableSet[h2.measurableSpace] S := by
  subst h𝓖 hτ; exact hS

theorem coe_min_fun (σ ρ : Ω → ℝ≥0) :
    (fun ω => ((min (σ ω) (ρ ω) : ℝ≥0) : WithTop ℝ≥0)) =
      fun ω => min (σ ω : WithTop ℝ≥0) (ρ ω : WithTop ℝ≥0) := by
  funext ω; exact WithTop.coe_min _ _

/-- **The characteristic-function martingale at arbitrary stopping times** (Specification L550–L586, the step "(by
(3.19))" of Lemma 3.11 at a general stop). Let `σ ≤ τ` be stopping times of the usual augmentation with, almost
surely, `τ < ζ` and `supp ψ ∩ K_τ = ∅`. Then for `S ∈ 𝓕_σ` and real `θ`,
`∫_S exp(iθ (𝔥_τ, ψ) − θ² E_τ(ψ)/2) = ∫_S exp(iθ (𝔥_σ, ψ) − θ² E_σ(ψ)/2)`. -/
theorem setIntegral_cfAt_eq_of_le (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hκ : 0 < κ) (u : Ω → ℝ≥0 → ℂ → ℝ)
    (hu : ∀ ω s, IsBoundedHarmonicExtension
      (forceBoundaryData κ ρL ρR (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω))
      (forceJumpSet (fun i => VL i s ω - W s ω) (fun i => VR i s ω - W s ω)) (u ω s))
    (ψ : LQGMetric.TestOn upperHalfPlaneOpens) {σ τ : Ω → ℝ≥0}
    (hσ : IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (σ ω : WithTop ℝ≥0))
    (hτ : IsStoppingTime (usualAugmentation 𝓕 P) fun ω => (τ ω : WithTop ℝ≥0))
    (hστ : ∀ ω, σ ω ≤ τ ω)
    (hτs : ∀ᵐ ω ∂P, (τ ω : ℝ≥0∞) < ζ ω ∧
      Disjoint (tsupport ψ) (fwdHull (fun s : ℝ => W s.toNNReal ω) (τ ω)))
    {S : Set Ω} (hS : MeasurableSet[hσ.measurableSpace] S) (θ : ℝ) :
    ∫ ω in S, cfAt κ W u ψ θ τ ω ∂P = ∫ ω in S, cfAt κ W u ψ θ σ ω ∂P := by
  have hP : IsProbabilityMeasure P := hE.1.isProbabilityMeasure'
  set 𝓖 := usualAugmentation 𝓕 P with h𝓖
  have hE' : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓖 W VL VR B ζ :=
    isIntegratedSLEEvolution_usualAugmentation hE
  have hnull : nullAugmented 𝓖 P = 𝓖 := nullAugmented_usualAugmentation 𝓕 P
  have hpath := hE.2.2.2.2
  have hKH : tsupport (ψ : ℂ → ℝ) ⊆ H := tsupport_subset_H ψ
  have hK : IsCompact (tsupport (ψ : ℂ → ℝ)) := ψ.hasCompactSupport.isCompact
  have hφc : Continuous ψ := ψ.continuous
  have hφs : HasCompactSupport ψ := ψ.hasCompactSupport
  have hSm : MeasurableSet S := hσ.measurableSpace_le _ hS
  obtain ⟨m, hm, hKm⟩ := exists_pos_le_im_of_isCompact hK hKH
  set σ₀ : ℕ → Ω → ℝ≥0 := fun n ω => min (τ ω) n with hσ₀_def
  have hσ₀ : ∀ n : ℕ, IsStoppingTime 𝓖 fun ω => (σ₀ n ω : WithTop ℝ≥0) := fun n => by
    have h := hτ.min_const (n : ℝ≥0)
    convert h using 2 with ω
    simp only [hσ₀_def, WithTop.coe_min]
  have hσ₀m : ∀ ω, Monotone fun n => σ₀ n ω := fun ω n n' h =>
    min_le_min le_rfl (by exact_mod_cast h)
  have hσ₀ζ : ∀ n, ∀ᵐ ω ∂P, (σ₀ n ω : ℝ≥0∞) < ζ ω := fun n => by
    filter_upwards [hτs] with ω h
    exact lt_of_le_of_lt (by exact_mod_cast min_le_left _ _) h.1
  obtain ⟨ρ, hρst, hρle, -, hρsafe, hρex⟩ := exists_safeSeq_of_seq hE hK hKH hm hKm hσ₀ hσ₀m hσ₀ζ
  have hev : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ρ n ω = τ ω := by
    filter_upwards [hρex, hτs] with ω hex hτω
    obtain ⟨j, hj⟩ : ∃ j : ℕ, (τ ω : ℝ) ≤ j := exists_nat_ge _
    have hτj : τ ω ≤ σ₀ j ω := le_min le_rfl (by exact_mod_cast hj)
    have halive : ∀ z ∈ tsupport (ψ : ℂ → ℝ), ∃ v, IsForwardSol (rpath (W · ω)) z (τ ω) v :=
      fun z hz => exists_isForwardSol_of_mem (τ ω).coe_nonneg
        ⟨hKH hz, fun h => hτω.2.ne_of_mem hz h rfl⟩
    filter_upwards [hex j (τ ω) hτj halive] with n hn
    exact le_antisymm ((hρle n ω).trans (min_le_left _ _)) hn
  have hδn : ∀ n : ℕ, 0 < m / ((n : ℝ) + 1) := fun n => by positivity
  have hbn : ∀ n, IsStoppingTime (nullAugmented 𝓖 P) fun ω => (ρ n ω : WithTop ℝ≥0) := fun n => by
    rw [hnull]; exact hρst n
  have hbs : ∀ n : ℕ, ∀ᵐ ω ∂P, IsTestSafe W ζ ψ (ρ n) (m / ((n : ℝ) + 1)) n ω := fun n => by
    filter_upwards [hρsafe n] with ω h; exact ⟨h.1, h.2.2.1, h.2.2.2⟩
  have ha𝓖 : ∀ n, IsStoppingTime 𝓖 fun ω => ((min (σ ω) (ρ n ω) : ℝ≥0) : WithTop ℝ≥0) :=
    fun n => by rw [coe_min_fun]; exact hσ.min (hρst n)
  have han : ∀ n, IsStoppingTime (nullAugmented 𝓖 P)
      fun ω => ((min (σ ω) (ρ n ω) : ℝ≥0) : WithTop ℝ≥0) := fun n => by rw [hnull]; exact ha𝓖 n
  have has : ∀ n : ℕ, ∀ᵐ ω ∂P,
      IsTestSafe W ζ ψ (fun ω => min (σ ω) (ρ n ω)) (m / ((n : ℝ) + 1)) n ω := fun n => by
    filter_upwards [hρsafe n, hpath] with ω h hP
    have h' := h.anti hP.2.2.2.1 hKH (min_le_right (σ ω) (ρ n ω))
    exact ⟨h'.1, h'.2.2.1, h'.2.2.2⟩
  have hint : ∀ r : Ω → ℝ≥0, ∀ n : ℕ,
      IsStoppingTime (nullAugmented 𝓖 P) (fun ω => (r ω : WithTop ℝ≥0)) →
      (∀ᵐ ω ∂P, IsTestSafe W ζ ψ r (m / ((n : ℝ) + 1)) n ω) →
      Integrable (cfAt κ W u ψ θ r) P := fun r n hr hrs =>
    Integrable.of_bound (aestronglyMeasurable_cfAt_of_safe hE' hκ u hu hr hrs hKH hφc hφs (hδn n) θ) 1
      (by
        filter_upwards [hrs, hpath] with ω hω hP
        exact norm_cfAt_le_one u θ ψ (continuousOn_rpath hP.2.2.2.1 hω.1) hP.1
          fun z hz => (hω.2.2 z hz).1)
  have hstep : ∀ n : ℕ, ∫ ω in S, cfAt κ W u ψ θ (ρ n) ω ∂P =
      ∫ ω in S, cfAt κ W u ψ θ (fun ω => min (σ ω) (ρ n ω)) ω ∂P := by
    intro n
    have hT : MeasurableSet {ω | σ ω ≤ ρ n ω} := by
      have h := (hσ.measurableSet_le_stopping_time (hρst n))
      have h' : MeasurableSet {ω | (σ ω : WithTop ℝ≥0) ≤ (ρ n ω : WithTop ℝ≥0)} :=
        hσ.measurableSpace_le _ h
      simpa only [WithTop.coe_le_coe] using h'
    have hS' : MeasurableSet[(han n).measurableSpace] (S ∩ {ω | σ ω ≤ ρ n ω}) := by
      have h := hσ.measurableSet_inter_le (hρst n) S hS
      simp only [WithTop.coe_le_coe] at h
      exact measurableSet_stopping_congr hnull.symm (coe_min_fun σ (ρ n)).symm _ (han n) h
    have h2 := setIntegral_cfAt_eq_of_safe_le hE' hκ u hu ψ (han n) (hbn n)
      (fun ω => min_le_right _ _) (has n) (hbs n) (hδn n) hS' θ
    rw [← integral_inter_add_sdiff hT (hint _ n (hbn n) (hbs n)).integrableOn,
      ← integral_inter_add_sdiff hT (hint _ n (han n) (has n)).integrableOn, h2]
    congr 1
    refine setIntegral_congr_fun (hSm.diff hT) fun ω hω => cfAt_congr u θ ?_
    exact (min_eq_right (le_of_lt (not_le.1 hω.2))).symm
  have hlim : ∀ (r : ℕ → Ω → ℝ≥0) (r₀ : Ω → ℝ≥0),
      (∀ n, IsStoppingTime (nullAugmented 𝓖 P) (fun ω => (r n ω : WithTop ℝ≥0))) →
      (∀ n : ℕ, ∀ᵐ ω ∂P, IsTestSafe W ζ ψ (r n) (m / ((n : ℝ) + 1)) n ω) →
      (∀ᵐ ω ∂P, ∀ᶠ n in atTop, r n ω = r₀ ω) →
      Tendsto (fun n => ∫ ω in S, cfAt κ W u ψ θ (r n) ω ∂P) atTop
        (𝓝 (∫ ω in S, cfAt κ W u ψ θ r₀ ω ∂P)) := by
    intro r r₀ hr hrs hre
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => 1)
      (Eventually.of_forall fun n => (hint (r n) n (hr n) (hrs n)).aestronglyMeasurable.restrict)
      (Eventually.of_forall fun n => ae_restrict_of_ae ?_) (integrable_const _) ?_
    · filter_upwards [hrs n, hpath] with ω hω hP
      exact norm_cfAt_le_one u θ ψ (continuousOn_rpath hP.2.2.2.1 hω.1) hP.1
        fun z hz => (hω.2.2 z hz).1
    · refine ae_restrict_of_ae ?_
      filter_upwards [hre] with ω hω
      exact tendsto_const_nhds.congr' (hω.mono fun n hn => cfAt_congr u θ hn.symm)
  have h1 := hlim ρ τ hbn hbs hev
  have h2 := hlim (fun n ω => min (σ ω) (ρ n ω)) σ han has (by
    filter_upwards [hev] with ω hω
    filter_upwards [hω] with n hn
    rw [hn]; exact min_eq_left (hστ ω))
  exact tendsto_nhds_unique (h1.congr hstep) h2

end Coupling

end InteractingSLE
