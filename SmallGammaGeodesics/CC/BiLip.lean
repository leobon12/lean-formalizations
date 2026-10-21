import SmallGammaGeodesics.CC.BiLipChain
import SmallGammaGeodesics.CC.Lemma35Local
import SmallGammaGeodesics.CC.Cover
import SmallGammaGeodesics.CC.LocalGlobal
import SmallGammaGeodesics.Geodesic.Basic

/-!
# [3] Thm 3.4 / Prop 3.1 on the domain, one direction: `ConfBiLipLE` (track CC, packet CC8)

Source: `planning/audits/CC0-conformal-covariance-plan.md`, Details (a) **D13** (Gwynne–Miller,
arXiv:1905.00384 ([3]), Theorem 3.4 and Proposition 3.1, one direction, for the transported metric
`D^ϕ = confMetric D ϕ V h̄ f` of a conformal neighbourhood `(ϕ, W, V)`), with the interface
`ConfSmallScale` ([3] Prop 2.1, packet CC6b) as hypothesis (ruling G10).

* `ae_exists_small_of_measure_le`: if `P[Q_ε fails] ≤ c ε^q` for small `ε`, then a.s. `Q_ε` holds at
  arbitrarily small scales (outer measures; no measurability is needed).
* `ae_local_le_of_compact`: one constant `C > 0` (from `lemma35` at the probability `p` of
  `CoverLemma` with `c₀ = 4`, `s₁ = 1/16`, `s₂ = 1/2`, `N = 16`) such that for every coupling and
  every compact `K ⊆ V`, a.s. `D^ϕ(x, y) ≤ C · D_h(x, y)` for close `x, y ∈ K`. The covering lemma
  is applied to the annulus-local family `confLMEvent` on the `δ/4`-neighbourhood of `K`, and the
  deterministic steps are `local_le_of_covers`.
* `confBiLipLE_of_smallScale` (**target**): exhaust `V` by compacts and pass from local to global
  through lengths (`le_mul_internal_of_local`, ruling G26 with `C > 0`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace SmallGammaGeodesics.CC

open LQGMetric LQGMetric.Blueprint

/-- **Arbitrarily small good scales, a.s.**: if `P[Q_ε fails] ≤ c ε^q` (outer measure) for
`ε ∈ (0, ε₁)`, then a.s. for every `ε₀ > 0` some `ε ∈ (0, ε₀]` has `Q_ε`. (Along `ε_k → 0`, the
event "`Q_{ε_k}` fails for all large `k`" is a countable union of sets of outer measure `0`.) -/
lemma ae_exists_small_of_measure_le {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {Q : ℝ → Ω → Prop} {ε₁ c q : ℝ} (hε₁ : 0 < ε₁) (hq : 0 < q)
    (hb : ∀ ε ∈ Ioo (0 : ℝ) ε₁, P {ω | ¬ Q ε ω} ≤ ENNReal.ofReal (c * ε ^ q)) :
    ∀ᵐ ω ∂P, ∀ ε₀ : ℝ, 0 < ε₀ → ∃ ε : ℝ, 0 < ε ∧ ε ≤ ε₀ ∧ Q ε ω := by
  set e : ℕ → ℝ := fun k => ε₁ / 2 * (1 / ((k : ℝ) + 1)) with hedef
  have he0 : ∀ k, 0 < e k := fun k => by simp only [hedef]; positivity
  have he1 : ∀ k, e k < ε₁ := fun k => by
    have h1 : 1 / ((k : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have h2 : 0 < 1 / ((k : ℝ) + 1) := by positivity
    simp only [hedef]
    nlinarith
  have hlim : Tendsto e atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (ε₁ / 2)
    rwa [mul_zero] at this
  rw [ae_iff]
  have hsub : {ω | ¬ ∀ ε₀ : ℝ, 0 < ε₀ → ∃ ε : ℝ, 0 < ε ∧ ε ≤ ε₀ ∧ Q ε ω} ⊆
      ⋃ n : ℕ, ⋂ k : ℕ, ⋂ (_ : n ≤ k), {ω | ¬ Q (e k) ω} := by
    intro ω hω
    simp only [mem_ofPred_eq, not_forall, not_exists, not_and] at hω
    obtain ⟨ε₀, hε₀, hno⟩ := hω
    obtain ⟨n, hn⟩ := eventually_atTop.1 (hlim.eventually (gt_mem_nhds hε₀))
    exact mem_iUnion.2 ⟨n, mem_iInter₂.2 fun k hk => hno (e k) (he0 k) (hn k hk).le⟩
  refine measure_mono_null hsub (measure_iUnion_null fun n => ?_)
  refine le_antisymm ?_ zero_le
  have hb' : ∀ k, n ≤ k → P (⋂ k' : ℕ, ⋂ (_ : n ≤ k'), {ω | ¬ Q (e k') ω}) ≤
      ENNReal.ofReal (c * e k ^ q) :=
    fun k hk => (measure_mono (iInter₂_subset k hk)).trans (hb (e k) ⟨he0 k, he1 k⟩)
  have htend : Tendsto (fun k => ENNReal.ofReal (c * e k ^ q)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k => e k ^ q) atTop (𝓝 0) := by
      have := (Real.continuousAt_rpow_const 0 q (Or.inr hq.le)).tendsto.comp hlim
      rwa [Real.zero_rpow hq.ne'] at this
    have h2 := h1.const_mul c
    rw [mul_zero] at h2
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal h2
  exact ge_of_tendsto htend (eventually_atTop.2 ⟨n, hb'⟩)

/-- **The local comparison on compacts** (CC0 D13, steps 1–4): there is `C > 0` (depending only on
`γ` and `D`) such that for every conformal neighbourhood, every coupling and every compact
`K ⊆ V`, a.s. there is `ρ > 0` with `D^ϕ(x, y) ≤ C · D_h(x, y)` for `x, y ∈ K`, `|x − y| ≤ ρ`. -/
theorem ae_local_le_of_compact {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {D : DistC → ContMetric}
    (hD : IsStrongLQGMetric γ D) (hS : ConfSmallScale γ D) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ϕ : ℂ → ℂ) (W V : Set ℂ), IsConfNbhd ϕ W V →
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h hbar : Ω → DistC) (f : Ω → C(ℂ, ℝ)),
      IsWholePlaneGFF h P → IsWholePlaneGFF hbar P → Measurable f →
      (∀ᵐ ω ∂P, IsConfCoupling γ ϕ W V (h ω) (hbar ω) (f ω)) →
      ∀ K : Set ℂ, IsCompact K → K ⊆ V →
      ∀ᵐ ω ∂P, ∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ ρ →
        confMetric D ϕ V (hbar ω) (f ω) x y ≤ ENNReal.ofReal (C * (D (h ω)).1 (x, y)) := by
  obtain ⟨p, _, hp1, hcov⟩ := coverLemma 4 (1 / 16) (1 / 2) 16 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) 1 one_pos
  obtain ⟨C, hC, hL35⟩ := lemma35 hγ hD hS hp1
  refine ⟨C, hC, fun ϕ W V hϕ Ω _ P _ h hbar f hh hhb hf hc K hK hKV => ?_⟩
  obtain ⟨δ, hδ, hδV⟩ := hK.exists_cthickening_subset_open hϕ.isOpen_V hKV
  have hK₂ : IsCompact (cthickening (δ / 2) K) := hK.cthickening
  have hK₂V : cthickening (δ / 2) K ⊆ V := (cthickening_mono (by linarith) K).trans hδV
  obtain ⟨r₀, hr₀, H35⟩ := hL35 ϕ W V hϕ _ hK₂ hK₂V
  set act : ℂ → ℝ → Prop := fun w r => w ∈ cthickening (δ / 2) K ∧ closedBall w (2 * r) ⊆ V
    with hactdef
  have hloc := isAnnulusLocal_confLMEvent hD hϕ C (act := act) (fun w r ha => ha.2) hh hhb hf hc
  have hprob : ∀ w : ℂ, infDist w (cthickening (δ / 4) K) ≤ 1 → ∀ r ∈ Ioc (0 : ℝ) r₀,
      ENNReal.ofReal p ≤ P (confLMEvent D ϕ C act h hbar f w r) := by
    intro w _ r hr
    by_cases ha : act w r
    · rw [confLMEvent_of_act ha]
      exact H35 P h hbar f hh hhb hf hc w ha.1 r hr
    · rw [confLMEvent_of_not_act ha, measure_univ]
      exact ENNReal.ofReal_le_one.2 hp1.le
  obtain ⟨Cc, ε₁, hε₁, hcovb⟩ := hcov P h hh (confLMEvent D ϕ C act h hbar f) hloc
    (cthickening (δ / 4) K) hK.cthickening r₀ hr₀ hprob
  have hfreq := ae_exists_small_of_measure_le (P := P)
    (Q := fun ε ω => ∀ z ∈ cthickening (δ / 4) K, ∃ k : ℕ, ∃ m : ℤ × ℤ,
      ε ^ 2 ≤ ((16 : ℕ) : ℝ)⁻¹ ^ k * ε ∧
      ‖z - GM.gridPt (ε ^ 2 / 4) m‖ < ((16 : ℕ) : ℝ)⁻¹ ^ k * ε / 2 ∧
      ω ∈ confLMEvent D ϕ C act h hbar f (GM.gridPt (ε ^ 2 / 4) m) (((16 : ℕ) : ℝ)⁻¹ ^ k * ε))
    hε₁ one_pos hcovb
  filter_upwards [hfreq, ae_exists_geod01_all hγ hγ2 hD P h hh,
    ae_continuousOn_confMetric hD hhb hf] with ω hω hgeo hcont
  refine local_le_of_covers (D (h ω)) (d := confMetric D ϕ V (hbar ω) (f ω))
    confMetric_triangle hϕ.isOpen_V (hcont ϕ W V hϕ) (fun x hx => confMetric_self hx) hgeo hK hKV
    (δ := δ / 4) (by positivity) hC.le
    (fun w r => ConfLMGood D ϕ (h ω) (hbar ω) (f ω) C w r ∧ closedBall w (2 * r) ⊆ V) ?_ ?_
  · rintro w r ⟨hg, hwV⟩ u hu v hv
    have hAV : (annulus w (r / 2) (2 * r) : Set ℂ) ⊆ V :=
      fun y hy => hwV (mem_closedBall_iff_norm.2 (le_of_lt hy.2))
    exact (confMetric_anti hAV u v).trans (hg u hu v hv)
  · intro ε₀ hε₀
    obtain ⟨ε, hε, hεε₀, hQ⟩ := hω (min ε₀ (δ / 16)) (by positivity)
    have hεδ : ε ≤ δ / 16 := hεε₀.trans (min_le_right _ _)
    refine ⟨ε, hε, hεε₀.trans (min_le_left _ _), fun x hx => ?_⟩
    obtain ⟨k, m, hk1, hk2, hk3⟩ := hQ x hx
    have hrε : ((16 : ℕ) : ℝ)⁻¹ ^ k * ε ≤ ε := by
      have : ((16 : ℕ) : ℝ)⁻¹ ^ k ≤ 1 := pow_le_one₀ (by positivity) (by norm_num)
      nlinarith
    -- the activation condition holds at the covering annulus
    rw [hK.cthickening_eq_biUnion_closedBall (by positivity)] at hx
    obtain ⟨y₀, hy₀, hxy₀⟩ := mem_iUnion₂.1 hx
    rw [mem_closedBall] at hxy₀
    have hxw : dist (GM.gridPt (ε ^ 2 / 4) m) x < ε / 2 := by
      rw [dist_comm, dist_eq_norm]
      linarith
    have hact : act (GM.gridPt (ε ^ 2 / 4) m) (((16 : ℕ) : ℝ)⁻¹ ^ k * ε) := by
      refine ⟨mem_cthickening_of_dist_le _ y₀ (δ / 2) K hy₀ ?_, fun y hy => ?_⟩
      · have := dist_triangle (GM.gridPt (ε ^ 2 / 4) m) x y₀
        linarith
      · refine hδV (mem_cthickening_of_dist_le y y₀ δ K hy₀ ?_)
        have h1 := dist_triangle4 y (GM.gridPt (ε ^ 2 / 4) m) x y₀
        rw [mem_closedBall] at hy
        linarith
    exact ⟨_, _, hk1, hrε, hk2, (hk3 : act _ _ → _) hact, hact.2⟩

/-- **[3] Prop 3.1 on the domain, one direction** (CC0 D13; target of packet CC8): for the
canonical γ-LQG metric, `ConfSmallScale` ([3] Prop 2.1) implies `ConfBiLipLE`: for every
conformal neighbourhood `(ϕ, W, V)` there is `C > 0` such that for every coupling, a.s.
`D^ϕ(z, w) ≤ C · D_h(z, w; V)` for all `z, w ∈ V`. -/
theorem confBiLipLE_of_smallScale {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {D : DistC → ContMetric}
    (hD : GaussianLQG.IsCanonicalLQGMetric γ D) (hS : ConfSmallScale γ D) : ConfBiLipLE γ D := by
  obtain ⟨C, hC, H⟩ := ae_local_le_of_compact hγ hγ2 hD.1 hS
  intro ϕ W V hϕ
  refine ⟨C, hC, ?_⟩
  intro Ω _ P _ h hbar f hh hhb hf hc
  -- an exhaustion of `V` by compacts
  obtain ⟨R, hR⟩ := hϕ.isBounded_V.subset_closedBall 0
  set Kn : ℕ → Set ℂ := fun n => closedBall 0 R ∩ (thickening (1 / ((n : ℝ) + 1)) Vᶜ)ᶜ
    with hKndef
  have hKn : ∀ n, IsCompact (Kn n) := fun n =>
    (isCompact_closedBall 0 R).inter_right isOpen_thickening.isClosed_compl
  have hKnV : ∀ n, Kn n ⊆ V := fun n x hx => by
    by_contra hxV
    exact hx.2 (self_subset_thickening (by positivity) _ hxV)
  have hexh : ∀ K : Set ℂ, IsCompact K → K ⊆ V → ∃ n, K ⊆ Kn n := by
    intro K hK hKV
    obtain ⟨δ, hδ, hδV⟩ := hK.exists_thickening_subset_open hϕ.isOpen_V hKV
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
    refine ⟨n, fun x hx => ⟨hR (hKV hx), fun hxt => ?_⟩⟩
    obtain ⟨y, hyV, hxy⟩ := mem_thickening_iff.1 hxt
    exact hyV (hδV (mem_thickening_iff.2 ⟨x, hx, by rw [dist_comm]; linarith⟩))
  have hall : ∀ᵐ ω ∂P, ∀ n : ℕ, ∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ Kn n, ∀ y ∈ Kn n, ‖x - y‖ ≤ ρ →
      confMetric D ϕ V (hbar ω) (f ω) x y ≤ ENNReal.ofReal (C * (D (h ω)).1 (x, y)) :=
    ae_all_iff.2 fun n => H ϕ W V hϕ P h hbar f hh hhb hf hc (Kn n) (hKn n) (hKnV n)
  filter_upwards [hall] with ω hω z _ w _
  refine le_mul_internal_of_local (D (h ω)) (d := confMetric D ϕ V (hbar ω) (f ω))
    confMetric_triangle hC (fun K hK hKV => ?_) z w
  obtain ⟨n, hn⟩ := hexh K hK hKV
  obtain ⟨ρ, hρ, hρK⟩ := hω n
  exact ⟨ρ, hρ, fun x hx y hy hxy => hρK x (hn hx) y (hn hy) hxy⟩

end SmallGammaGeodesics.CC
