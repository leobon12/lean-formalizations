import HigherDimLFPPAS.Localize.Basic
import HigherDimLFPPAS.Det.WeylLocalization
import HigherDimLFPPAS.Proper.Lemma22
import HigherDimLQGMetric.Thm13.ProbSubseq
import HigherDimLQGMetric.Thm13.ProbConvergence

/-!
# Lemma 2.4, first assertion: `M_ε → D` in probability, locally uniformly

Packet L24; planning audit MA1 §2.7 and Details A6.1–A6.2 (`source/…txt` l. 263–287).

* `tendsto_meps_of_tendsto_neps` (deterministic, A6.1 in Weyl form): along a sequence of cutoffs, if
  `N_{ε_n} → G` locally uniformly, `G` is a proper length metric and `ĥ*_{ε_n} − h*_{ε_n} → 0` locally
  uniformly, then `M_{ε_n} → G` locally uniformly. It is packet D1's
  `Det.eventually_weyl_metric_local_comparison` applied to `M_ε = e^{ξ(ĥ*_ε − h*_ε)} · N_ε`
  (`meps_eq_weylMetric`).
* `lemma24Conv_of_setting` (A6.2): the interface `Core.Lemma24Conv`, from `Core.Setting` and
  `Core.Lemma23i`. Along every sequence `ε_n ↓ 0` a subsequence has `N_{ε_n} → D` a.s. locally uniformly
  (`l8_exists_subseq_ae_of_prob`); on that event, the event of Lemma 2.3(i) and the properness event of
  Lemma 2.2, the deterministic step gives `M_{ε_n} → D`; `l8_tendstoInProbLU_of_ae` and the subsequence
  criterion `Filter.tendsto_of_subseq_tendsto` conclude.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLFPPAS.Localize

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- Uniform convergence along a filter transfers along a function tending to that filter. -/
theorem tendstoUniformlyOn_comp_tendsto {ι ι' α : Type*} {F : ι → α → ℝ} {f : α → ℝ}
    {p : Filter ι} {s : Set α} (hF : TendstoUniformlyOn F f p s) {l : Filter ι'} {g : ι' → ι}
    (hg : Tendsto g l p) : TendstoUniformlyOn (fun n => F (g n)) f l s := by
  rw [Metric.tendstoUniformlyOn_iff] at hF ⊢
  exact fun e he => hg.eventually (hF e he)

/-- `locRad ε > 0` for `ε ∈ (0, 1)`. -/
theorem locRad_pos_of_mem_Ioo {ε : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 1) : 0 < locRad ε := by
  have hlog : 0 < Real.log ε⁻¹ := Real.log_pos ((one_lt_inv₀ hε.1).2 hε.2)
  exact mul_pos hε.1 (pow_pos hlog 10)

/-- A compact subset of `ℝ^d × ℝ^d` lies in a product of centred closed balls of positive radius. -/
theorem exists_closedBall_prod_of_isCompact {K : Set (Rd d × Rd d)} (hK : IsCompact K) :
    ∃ r : ℝ, 0 < r ∧ K ⊆ closedBall (0 : Rd d) r ×ˢ closedBall (0 : Rd d) r := by
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall (0 : Rd d × Rd d)
  refine ⟨max r 1, by positivity, ?_⟩
  rw [closedBall_prod_same, Prod.mk_zero_zero]
  exact hr.trans (closedBall_subset_closedBall (le_max_left _ _))

/-- **Deterministic step of Lemma 2.4** (MA1 A6.1–A6.2, Weyl form): along a sequence of cutoffs with
`𝔞_{ε_n} > 0`, if `N_{ε_n}(g) → G` locally uniformly with `G` a proper length metric and
`ĥ*_{ε_n} − h*_{ε_n} → 0` uniformly on every centred ball, then `M_{ε_n}(g) → G` locally uniformly. -/
theorem tendsto_meps_of_tendsto_neps {κ : Rd d → ℝ} {ξ : ℝ} {g : DistRd d} {G : ContMetric d}
    (hG : G.IsLength) (hGp : IsProperFn G.1) (εs : ℕ → ℝ) (ha : ∀ n, 0 < aEps κ ξ (εs n))
    (hN : Tendsto (fun n => (Core.Neps κ ξ (εs n) g).1) atTop (𝓝 G.1))
    (hu : ∀ R : ℝ, 0 < R → TendstoUniformlyOn
      (fun n => ⇑(Core.locFieldC κ (εs n) g - Core.convFieldC κ (εs n) g)) 0 atTop
      (closedBall (0 : Rd d) R)) :
    Tendsto (fun n => (Core.Meps κ ξ (εs n) g).1) atTop (𝓝 G.1) := by
  have hNlu := ContinuousMap.tendsto_iff_tendstoLocallyUniformly.1 hN
  rw [tendstoLocallyUniformly_iff_forall_isCompact] at hNlu
  rw [ContinuousMap.tendsto_iff_tendstoLocallyUniformly,
    tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  obtain ⟨r, hr, hKr⟩ := exists_closedBall_prod_of_isCompact hK
  have hconvD : ∀ R : ℝ, 0 < R → TendstoUniformlyOn (fun n => ⇑(Core.Neps κ ξ (εs n) g).1) ⇑G.1
      atTop (closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R) := fun R _ =>
    hNlu _ ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
  obtain ⟨R, -, s, -, -, N, hN'⟩ := Det.eventually_weyl_metric_local_comparison ξ
    (fun n => Core.Neps κ ξ (εs n) g) G (fun n => neps_isLength κ ξ (εs n) g) hG hGp hconvD
    (fun n => Core.locFieldC κ (εs n) g - Core.convFieldC κ (εs n) g) hu
    (isCompact_closedBall (0 : Rd d) r)
  have h0 : (0 : Rd d) ∈ closedBall (0 : Rd d) r := mem_closedBall_self hr.le
  have hW := (hN' N le_rfl 0 h0 0 h0).2.2
  refine (hW.congr (Eventually.of_forall fun n p _ => ?_)).mono hKr
  exact (congrFun (congrArg DFunLike.coe (meps_eq_weylMetric g (ha n))) p).symm

/-- A.s., `h*_ε` is continuous for every `ε > 0` simultaneously (`SeedFacts.jointCont`). -/
theorem ae_continuous_convMollify {ξ Q : ℝ} {κ : Rd d → ℝ} {D : DistRd d → ContMetric d}
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hS : Core.Setting d ξ Q κ D P h) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → Continuous (convMollify κ ε (h ω)) := by
  filter_upwards [hS.seed.jointCont P h hS.field] with ω hω ε hε
  have hmaps : MapsTo (fun z : Rd d => (ε, z)) univ (Ioi (0 : ℝ) ×ˢ univ) :=
    fun z _ => ⟨hε, mem_univ z⟩
  have hc := hω.comp (continuous_const.prodMk continuous_id).continuousOn hmaps
  exact continuousOn_univ.1 hc

/-- **Lemma 2.4, first assertion** (MA1 A6.2): `M_ε → D` in probability, locally uniformly. -/
theorem lemma24Conv_of_setting {ξ Q : ℝ} {κ : Rd d → ℝ} {D : DistRd d → ContMetric d}
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hS : Core.Setting d ξ Q κ D P h) (h23 : Core.Lemma23i κ P h) :
    Core.Lemma24Conv κ ξ D P h := by
  have hcont := ae_continuous_convMollify hS
  have hlen : ∀ᵐ ω ∂P, (D (h ω)).IsLength := hS.strong.length P h hS.field.1.isLGFPlusCont
  have hprop := lemma22_ae_proper_and_geodesic hS.dim hS.xi_pos hS.subcrit P h hS.field D hS.strong
  have hY : Measurable fun ω => (D (h ω)).1 :=
    measurable_metric_comp hS.strong.measurable hS.field.1.measurable
  intro R hR δ hδ
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (hns (Ioo_mem_nhdsGT (zero_lt_one' ℝ)))
  let εs : ℕ → ℝ := fun n => ns (n + N₀)
  have hεs : ∀ n, εs n ∈ Ioo (0 : ℝ) 1 := fun n => hN₀ _ (Nat.le_add_left _ _)
  have hεsT : Tendsto εs atTop (𝓝[>] 0) := hns.comp (tendsto_add_atTop_nat N₀)
  have ha : ∀ n, 0 < aEps κ ξ (εs n) := fun n => hS.seed.aEps_pos ξ _ (hεs n).1
  -- `N_{ε_n} → D` in probability (Assumption 1.1 (v) along the sequence)
  have hNprob : TendstoInProbLU P (fun n ω => (Core.Neps κ ξ (εs n) (h ω)).1) atTop
      (fun ω => (D (h ω)).1) := by
    intro R' hR' δ' hδ'
    refine Tendsto.congr' (Eventually.of_forall fun n => ?_) ((hS.conv R' hR' δ' hδ').comp hεsT)
    simp only [Function.comp_apply]
    apply measure_congr
    filter_upwards [hcont] with ω hω
    have hfun : (aEps κ ξ (εs n))⁻¹ • lfppDist κ ξ (εs n) (h ω) =
        ⇑(Core.Neps κ ξ (εs n) (h ω)).1 :=
      funext fun p => (neps_apply_eq_lfppDist (ha n) (hω _ (hεs n).1) p).symm
    rw [hfun]
  obtain ⟨ms, hms, hae⟩ := l8_exists_subseq_ae_of_prob P
    (fun n ω => (Core.Neps κ ξ (εs n) (h ω)).1) (fun ω => (D (h ω)).1)
    (fun n => aemeasurable_neps (ha n) hS.field.1.measurable
      (hcont.mono fun ω hω => hω _ (hεs n).1)) hNprob
  -- along the subsequence, `M_{ε_n} → D` almost surely
  have hMae : ∀ᵐ ω ∂P,
      Tendsto (fun n => (Core.Meps κ ξ (εs (ms n)) (h ω)).1) atTop (𝓝 (D (h ω)).1) := by
    filter_upwards [hae, h23, hcont, hlen, hprop] with ω hω h23ω hcω hlω hpω
    refine tendsto_meps_of_tendsto_neps hlω (isProperFn_of_properSpace _ hpω.2.1)
      (fun n => εs (ms n)) (fun n => ha (ms n)) hω fun R' hR' => ?_
    have hT : Tendsto (fun n => εs (ms n)) atTop (𝓝[>] 0) :=
      hεsT.comp hms.tendsto_atTop
    refine (tendstoUniformlyOn_comp_tendsto (h23ω R' hR') hT).congr
      (Eventually.of_forall fun n x _ => ?_)
    have hloc := locFieldC_coe (κ := κ) (g := h ω)
      (continuous_locField hS.seed.kernelSmooth (locRad_pos_of_mem_Ioo (hεs (ms n))) (h ω))
    have hcv := convFieldC_coe (hcω _ (hεs (ms n)).1)
    simp only [ContinuousMap.coe_sub, Pi.sub_apply, hloc, hcv]
  have hMm : ∀ n, AEMeasurable (fun ω => (Core.Meps κ ξ (εs (ms n)) (h ω)).1) P := fun n =>
    (measurable_meps hS.seed.kernelSmooth (locRad_pos_of_mem_Ioo (hεs (ms n))) (ha (ms n))
      hS.field.1.measurable).aemeasurable
  have hprob := l8_tendstoInProbLU_of_ae P (fun n ω => (Core.Meps κ ξ (εs (ms n)) (h ω)).1)
    (fun ω => (D (h ω)).1) hMm hY hMae
  exact ⟨fun n => ms n + N₀, hprob R hR δ hδ⟩

end HigherDimLFPPAS.Localize
