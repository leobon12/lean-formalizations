import Mathlib.Geometry.Manifold.PartitionOfUnity
import InteractingSLE.Stochastic.Martingale.OptionalSampling
import InteractingSLE.Spec.Ito.Dynkin

/-!
# Localized Itô formula

Packet PROVE-T11-ITO. `martingale_itoDynkin` needs a globally `C³` function with compact support and a path of
bounded variation on all of `[0, ∞)`. The processes of Section 3.3 (`log f_t(z)`, `𝔥_t(z)`, …) are smooth
functions of the coordinates only on an open set (`Im f_t(z) > 0`), and the coordinates only live before a random
time. This file localizes:

* `exists_cutoff`: for a compact `K` inside an open `U` of a finite-dimensional space there is a smooth
  compactly supported `χ` with `tsupport χ ⊆ U` and `χ = 1` near `K`;
* `itoGen_congr`: the Itô generator `itoGen F p v` only depends on the germ of `F` at `p`;
* `martingale_itoLocalized`: if `Φ` is `C³` on an open `U`, `σ` is a stopping time, the stopped path
  `(Λ_{t∧σ}, B_{t∧σ})` stays in a compact `K ⊆ U` and is absolutely continuous in `Λ` before `σ` with bounded
  variation, and `Λ_{·∧σ}` is adapted, then
  `Φ(Λ_{t∧σ}, B_{t∧σ}) − ∫₀^{t∧σ} itoGen Φ (Λ_s, B_s) λ_s ds` is a martingale.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Ito

section Cutoff

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]

/-- A smooth cutoff: for a compact `K` in an open `U` there is a smooth `χ` with compact support in `U`
and `χ = 1` on a neighbourhood of `K`. -/
theorem exists_cutoff {K U : Set G} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : G → ℝ, ContDiff ℝ 3 χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ U ∧
      ∀ᶠ x in 𝓝ˢ K, χ x = 1 := by
  obtain ⟨L, hL, hKL, hLU⟩ := exists_compact_between hK hU hKU
  obtain ⟨f, hf1, hf0, -⟩ := exists_contMDiffMap_one_nhds_of_subset_interior (modelWithCornersSelf ℝ G)
    (n := 3) hK.isClosed hKL
  have hsupp : tsupport f ⊆ L := by
    refine closure_minimal (fun x hx => ?_) hL.isClosed
    by_contra h
    exact hx (hf0 x h)
  refine ⟨f, contMDiff_iff_contDiff.1 f.contMDiff, ?_, hsupp.trans hLU, hf1⟩
  exact HasCompactSupport.intro hL fun x hx => hf0 x hx

omit [FiniteDimensional ℝ G] in
/-- A function that is `C³` on an open set, multiplied by a smooth cutoff supported in that set, is `C³`
everywhere. -/
theorem contDiff_mul_of_tsupport_subset {U : Set G} (hU : IsOpen U) {Φ χ : G → ℝ}
    (hΦ : ContDiffOn ℝ 3 Φ U) (hχ : ContDiff ℝ 3 χ) (hχU : tsupport χ ⊆ U) :
    ContDiff ℝ 3 fun x => χ x * Φ x := by
  refine contDiff_iff_contDiffAt.2 fun x => ?_
  by_cases hx : x ∈ U
  · exact hχ.contDiffAt.mul
      (hΦ.contDiffAt (hU.mem_nhds hx))
  · have hx' : x ∉ tsupport χ := fun h => hx (hχU h)
    have h0 : (fun x => χ x * Φ x) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx'] with y hy
      simp [hy]
    exact contDiffAt_const.congr_of_eventuallyEq h0

end Cutoff

/-- The Itô generator only depends on the germ of `F`. -/
theorem itoGen_congr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F Φ : E × ℝ → ℝ}
    {p : E × ℝ} (h : F =ᶠ[𝓝 p] Φ) (v : E) : itoGen F p v = itoGen Φ p v := by
  unfold itoGen partialFst partialSndSnd
  rw [h.fderiv_eq, h.fderiv.fderiv_eq]

section Localized

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {B : ℝ≥0 → Ω → ℝ}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Localized Itô formula.** Let `B` be an `𝓕`-Brownian motion with continuous paths, `σ` a finite
stopping time, `Φ` a `C³` function on an open `U ⊆ E × ℝ`, and `K ⊆ U` compact. Suppose that, along every
path, `Λ_t = Λ_0 + ∫₀ᵗ λ` for `t ≤ σ` with `∫₀^σ ‖λ‖ ≤ K_b`, that `(Λ_t, B_t) ∈ K` for `t ≤ σ`, and that
`Λ_{·∧σ}` is adapted. Then `Φ(Λ_{t∧σ}, B_{t∧σ}) − ∫₀^{t∧σ} itoGen Φ (Λ_s, B_s) λ_s ds` is an
`𝓕`-martingale. -/
theorem martingale_itoLocalized (hB : IsFilteredBrownianReal 𝓕 B P)
    (hBc : ∀ ω, Continuous (B · ω)) {U : Set (E × ℝ)} (hU : IsOpen U) {Φ : E × ℝ → ℝ}
    (hΦ : ContDiffOn ℝ 3 Φ U) {Kc : Set (E × ℝ)} (hKc : IsCompact Kc) (hKU : Kc ⊆ U)
    {σ : Ω → ℝ≥0} (hσ : IsStoppingTime 𝓕 fun ω => (σ ω : WithTop ℝ≥0))
    {Λ : ℝ≥0 → Ω → E} {lam : ℝ → Ω → E}
    (hΛm : ∀ t, Measurable[𝓕 t] fun ω => Λ (min t (σ ω)) ω)
    (hlam : ∀ ω, IntervalIntegrable (lam · ω) volume 0 (σ ω))
    (hΛ : ∀ ω (t : ℝ≥0), t ≤ σ ω → Λ t ω = Λ 0 ω + ∫ s in (0 : ℝ)..t, lam s ω)
    {Kb : ℝ} (hKb : ∀ ω, ∫ s in (0 : ℝ)..(σ ω), ‖lam s ω‖ ≤ Kb)
    (hK : ∀ ω (t : ℝ≥0), t ≤ σ ω → (Λ t ω, B t ω) ∈ Kc) :
    Martingale (fun t ω => Φ (Λ (min t (σ ω)) ω, B (min t (σ ω)) ω) -
      ∫ s in (0 : ℝ)..(min t (σ ω) : ℝ≥0), itoGen Φ (Λ s.toNNReal ω, B s.toNNReal ω) (lam s ω))
      𝓕 P := by
  have hP := hB.isProbabilityMeasure'
  obtain ⟨χ, hχ, hχc, hχU, hχ1⟩ := exists_cutoff hKc hU hKU
  set F : E × ℝ → ℝ := fun p => χ p * Φ p with hFdef
  have hF : ContDiff ℝ 3 F := contDiff_mul_of_tsupport_subset hU hΦ hχ hχU
  have hFc : HasCompactSupport F := hχc.mul_right
  have hFΦ : ∀ p ∈ Kc, F =ᶠ[𝓝 p] Φ := fun p hp => by
    filter_upwards [hχ1.filter_mono (nhds_le_nhdsSet hp)] with q hq
    simp [hFdef, hq]
  -- the frozen path and its density
  set Λt : ℝ≥0 → Ω → E := fun t ω => Λ (min t (σ ω)) ω with hΛt
  set lt : ℝ → Ω → E := fun s ω => (Ioc (0 : ℝ) (σ ω)).indicator (fun s => lam s ω) s with hlt
  have hlti : ∀ ω, Integrable (fun s => lt s ω) := fun ω => by
    have := (intervalIntegrable_iff_integrableOn_Ioc_of_le (σ ω).coe_nonneg).1 (hlam ω)
    exact (integrable_indicator_iff measurableSet_Ioc).2 this
  have hlt_int : ∀ ω (t : ℝ≥0), ∫ s in (0 : ℝ)..t, lt s ω = ∫ s in (0 : ℝ)..(min t (σ ω) : ℝ≥0),
      lam s ω := by
    intro ω t
    rw [intervalIntegral.integral_of_le t.coe_nonneg,
      intervalIntegral.integral_of_le (min t (σ ω)).coe_nonneg, setIntegral_indicator measurableSet_Ioc,
      Ioc_inter_Ioc, max_self, NNReal.coe_min]
  have hΛt_eq : ∀ ω (t : ℝ≥0), Λt t ω = Λt 0 ω + ∫ s in (0 : ℝ)..t, lt s ω := by
    intro ω t
    simp only [hΛt, zero_min, hlt_int]
    exact hΛ ω _ (min_le_right _ _)
  have hKt : ∀ ω, ∫ s, ‖lt s ω‖ ≤ Kb := by
    intro ω
    have : (fun s => ‖lt s ω‖) = (Ioc (0 : ℝ) (σ ω)).indicator (fun s => ‖lam s ω‖) := by
      funext s; simp only [hlt, norm_indicator_eq_indicator_norm]
    rw [this, integral_indicator measurableSet_Ioc, ← intervalIntegral.integral_of_le (σ ω).coe_nonneg]
    exact hKb ω
  have hM := martingale_itoDynkin hB hBc hF hFc hΛm hlti hΛt_eq hKt
  have hMc := continuous_itoDynkinProcess hBc hF hFc hlti hΛt_eq
  have hMs := Martingale.stoppedProcess_of_rightContinuous hM
    (fun ω t => (hMc ω).continuousWithinAt) hσ
  have heq : stoppedProcess (itoDynkinProcess F Λt lt B) (fun ω => (σ ω : WithTop ℝ≥0)) =
      fun t ω => Φ (Λ (min t (σ ω)) ω, B (min t (σ ω)) ω) -
        ∫ s in (0 : ℝ)..(min t (σ ω) : ℝ≥0), itoGen Φ (Λ s.toNNReal ω, B s.toNNReal ω) (lam s ω) := by
    funext t ω
    have hst : stoppedProcess (itoDynkinProcess F Λt lt B) (fun ω => (σ ω : WithTop ℝ≥0)) t ω =
        itoDynkinProcess F Λt lt B (min t (σ ω)) ω := by
      simp only [stoppedProcess, ← WithTop.coe_min]
      rfl
    rw [hst]
    simp only [itoDynkinProcess, hΛt]
    have hmm : min (min t (σ ω)) (σ ω) = min t (σ ω) := by rw [min_assoc, min_self]
    rw [hmm, (hFΦ _ (hK ω _ (min_le_right _ _))).eq_of_nhds]
    congr 1
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun s hs => ?_)
    rw [uIoc_of_le (min t (σ ω)).coe_nonneg] at hs
    have hs0 : 0 ≤ s := hs.1.le
    have hsσ : s.toNNReal ≤ σ ω := by
      rw [Real.toNNReal_le_iff_le_coe]
      exact hs.2.trans (by exact_mod_cast min_le_right t (σ ω))
    have hsσ' : s ∈ Ioc (0 : ℝ) (σ ω) := ⟨hs.1, (Real.toNNReal_le_iff_le_coe.1 hsσ)⟩
    simp only [min_eq_left hsσ, hlt, indicator_of_mem hsσ']
    exact itoGen_congr (hFΦ _ (hK ω _ hsσ)) _
  rw [← heq]
  exact hMs

end Localized

end Ito

end InteractingSLE
