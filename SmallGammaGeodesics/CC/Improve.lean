import SmallGammaGeodesics.CC.ImproveDet
import SmallGammaGeodesics.Core.GoodAnnulusInput
import SmallGammaGeodesics.CC.Cover
import SmallGammaGeodesics.CC.LocalGlobal
import SmallGammaGeodesics.CC.ConfMetric
import SmallGammaGeodesics.Geodesic.Basic

/-!
# [3] Prop 3.6, the improvement step `ConfImprove` (track CC, packet CC10)

[3] = Gwynne–Miller, *Conformal covariance of the Liouville quantum gravity metric for
γ ∈ (0, 2)*, arXiv:1905.00384v2, Proposition 3.6, Steps 2–6, with the current a.s. bound `C` in
place of the optimal constant `C_*` (ruling G21). Plan:
`planning/audits/CC0-conformal-covariance-plan.md`, Details (a) **D15**; consumption recipe
`planning/handoffs/CC8a.md`, §5; ruling G29.

**Target.** `confImprove_of_goodAnnulus : IsCanonicalLQGMetric γ D → GoodAnnulusInput γ D →
ConfImprove γ D`. The good-annulus events of [3] Lemmas 3.8–3.10 enter only through the interface
`GoodAnnulusInput` (`Core/GoodAnnulusInput.lean`, proved by CC9a/CC9b). Only the strong-metric part
of `IsCanonicalLQGMetric` is used: `confImprove_of_goodAnnulus_strong` is the same statement for
every strong γ-LQG metric.

**Proof.**
1. *Constants.* `coverLemma_uniform 4 (1/16) (1/2) 16 … 1` (CC7) gives `p ∈ (0,1)` and `c > 0`;
   `GoodAnnulusInput` at `p` gives `α ∈ (1/2,1)` and `A ≥ 0`; `θ := A/(A+1) ∈ [0,1)`.
2. *One compact `K ⊆ V`* (`ae_local_improve`). Take `κ > 0` with `cthickening κ K ⊆ V`, and the
   good events `E` of `GoodAnnulusInput` for `K₂ := cthickening κ K`, valid for `r ≤ r₀`. Pad them
   with `univ` off `K₂ × (0, r₀]` (`padEv`): the padded family is annulus-local everywhere
   (`isAnnulusLocal_padEv`) and has probability `≥ p` for all `r ≤ r₀` (`prob_padEv`), so CC7's
   covering bound applies to `K₁ := cthickening (κ/2) K`: the covering fails at scale `ε` with
   probability `≤ c′ ε`. Along `ε_n = ε₁ 2^{-n}`, Borel–Cantelli gives a.s. coverings for all large
   `n` (`ae_eventually_notMem_of_le_geom`, `ae_eventually_cover`). For `ε_n ≤ min(r₀, κ)` every
   covering ball is a true good ball (centre in `K₂`, radius `≤ r₀`). On the a.s. events (geodesics
   for all pairs `GM.gm_S1_1`, uniqueness for rational pairs `GM.gm_S1_2_rat`, continuity of `D^ϕ`
   on `V × V`, the current bound, the D-forms of conditions 1 and 3), the pathwise lemma
   `local_improve_det` (`CC/ImproveDet.lean`) gives `ρ > 0` with `D^ϕ(x,y) ≤ C_δ D_h(x,y)` for
   `x, y ∈ K`, `‖x − y‖ ≤ ρ`.
3. *All compacts at once.* A countable compact exhaustion of `V` (`exists_compact_exhaustion`) and
   `ae_all_iff`.
4. *Local to global.* CC8a's `le_mul_internal_of_local` at `C_δ = 1 + δ + θ(C − 1 − δ) ≥ 1 + δ > 0`
   (ruling G26) turns the local bound into `D^ϕ ≤ C_δ D_h(·,·;V)` on `V`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace SmallGammaGeodesics.CC

open LQGMetric LQGMetric.Blueprint

/-! ## 1. A countable compact exhaustion of an open set -/

/-- **Compact exhaustion**: an open `V ⊆ ℂ` has compacts `K_n ⊆ V` such that every compact
`K ⊆ V` lies in some `K_n` (`K_n = B̄(0,n) ∩ {x : infEDist x Vᶜ ≥ 1/(n+1)}`). -/
theorem exists_compact_exhaustion {V : Set ℂ} (hV : IsOpen V) :
    ∃ Kn : ℕ → Set ℂ, (∀ n, IsCompact (Kn n)) ∧ (∀ n, Kn n ⊆ V) ∧
      ∀ K : Set ℂ, IsCompact K → K ⊆ V → ∃ n, K ⊆ Kn n := by
  refine ⟨fun n => closedBall (0 : ℂ) (n : ℝ) ∩
      {x | ENNReal.ofReal (1 / ((n : ℝ) + 1)) ≤ infEDist x Vᶜ},
    fun n => (isCompact_closedBall (0 : ℂ) (n : ℝ)).inter_right
      (isClosed_le continuous_const continuous_infEDist),
    fun n x hx => ?_, fun K hK hKV => ?_⟩
  · by_contra hxV
    have h1 := hx.2
    rw [mem_ofPred_eq, infEDist_zero_of_mem (show x ∈ Vᶜ from hxV)] at h1
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    exact not_le.2 (ENNReal.ofReal_pos.2 hpos) h1
  · obtain ⟨δ, hδ, hδV⟩ := hK.exists_cthickening_subset_open hV hKV
    obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
    obtain ⟨n₁, hn₁⟩ := exists_nat_one_div_lt hδ
    obtain ⟨n₂, hn₂⟩ := exists_nat_ge R
    have hn₂' : R ≤ ((max n₁ n₂ : ℕ) : ℝ) :=
      hn₂.trans ((Nat.cast_le (α := ℝ)).2 (le_max_right n₁ n₂))
    have hn₁' : 1 / (((max n₁ n₂ : ℕ) : ℝ) + 1) ≤ 1 / ((n₁ : ℝ) + 1) := by
      have h1 : (n₁ : ℝ) ≤ ((max n₁ n₂ : ℕ) : ℝ) := (Nat.cast_le (α := ℝ)).2 (le_max_left n₁ n₂)
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    refine ⟨max n₁ n₂, fun x hx => ⟨closedBall_subset_closedBall hn₂' (hR hx), ?_⟩⟩
    rw [mem_ofPred_eq, le_infEDist]
    intro y hy
    by_contra hlt
    rw [not_le] at hlt
    refine hy (hδV (mem_cthickening_of_edist_le y x δ K hx ?_))
    rw [edist_comm]
    exact hlt.le.trans (ENNReal.ofReal_le_ofReal (by linarith))

/-! ## 2. The good events, padded with `univ` -/

/-- the events `E w r` for `w ∈ K₂` and `r ≤ r₀`, padded with `univ` elsewhere (so that the
family is annulus-local at every centre and radius, as `coverLemma_uniform` requires) -/
def padEv {Ω : Type} (E : ℂ → ℝ → Set Ω) (K₂ : Set ℂ) (r₀ : ℝ) (w : ℂ) (r : ℝ) : Set Ω :=
  {ω | w ∈ K₂ → r ≤ r₀ → ω ∈ E w r}

theorem padEv_of_mem {Ω : Type} {E : ℂ → ℝ → Set Ω} {K₂ : Set ℂ} {r₀ : ℝ} {w : ℂ} {r : ℝ}
    (hw : w ∈ K₂) (hr : r ≤ r₀) : padEv E K₂ r₀ w r = E w r := by
  ext ω
  exact ⟨fun H => H hw hr, fun H _ _ => H⟩

theorem padEv_of_not {Ω : Type} {E : ℂ → ℝ → Set Ω} {K₂ : Set ℂ} {r₀ : ℝ} {w : ℂ} {r : ℝ}
    (h : ¬ (w ∈ K₂ ∧ r ≤ r₀)) : padEv E K₂ r₀ w r = univ := by
  ext ω
  exact ⟨fun _ => mem_univ ω, fun _ hw hr => absurd ⟨hw, hr⟩ h⟩

/-- the padded family is annulus-local with CC7's parameters `c₀ = 4`, `s₁ = 1/16`, `s₂ = 1/2` -/
theorem isAnnulusLocal_padEv {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}
    {E : ℂ → ℝ → Set Ω} {K₂ : Set ℂ} {r₀ : ℝ}
    (hE : ∀ z ∈ K₂, ∀ r ∈ Ioc (0 : ℝ) r₀,
      AEEventIn P (fieldSigma (fun ω => addConst (h ω) (-circleAvg (h ω) (4 * r) z))
        (annulus z ((1 / 16) * (4 * r)) ((1 / 2) * (4 * r)))) (E z r)) :
    IsAnnulusLocal P h (padEv E K₂ r₀) 4 (1 / 16) (1 / 2) := by
  intro w r hr
  by_cases hc : w ∈ K₂ ∧ r ≤ r₀
  · rw [padEv_of_mem hc.1 hc.2]
    exact hE w hc.1 r ⟨hr, hc.2⟩
  · rw [padEv_of_not hc]
    exact ⟨univ, MeasurableSet.univ, EventuallyEq.rfl⟩

/-- the padded family has probability `≥ p` at every centre, for `r ≤ r₀` -/
theorem prob_padEv {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {E : ℂ → ℝ → Set Ω} {K₂ : Set ℂ} {r₀ p : ℝ} (hp1 : p < 1)
    (hE : ∀ z ∈ K₂, ∀ r ∈ Ioc (0 : ℝ) r₀, ENNReal.ofReal p ≤ P (E z r))
    (w : ℂ) (r : ℝ) (hr : r ∈ Ioc (0 : ℝ) r₀) : ENNReal.ofReal p ≤ P (padEv E K₂ r₀ w r) := by
  by_cases hw : w ∈ K₂
  · rw [padEv_of_mem hw hr.2]
    exact hE w hw r hr
  · rw [padEv_of_not (fun hc => hw hc.1), measure_univ]
    exact ENNReal.ofReal_le_one.2 hp1.le

/-! ## 3. Borel–Cantelli for the covering events -/

/-- **Borel–Cantelli** with geometric bounds: if `P(B_n) ≤ a 2^{-n}`, then a.s. `ω ∉ B_n` for all
large `n`. No measurability of `B_n` is needed (`P` acts as an outer measure). -/
theorem ae_eventually_notMem_of_le_geom {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℕ → Set Ω} {a : ℝ} (ha : 0 ≤ a)
    (hB : ∀ n, P (B n) ≤ ENNReal.ofReal (a * (1 / 2) ^ n)) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∉ B n := by
  refine ae_eventually_notMem (ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hB))
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity)
    (summable_geometric_two.mul_left a)]
  exact ENNReal.ofReal_ne_top

/-- **The covering events at the scales `ε_n = ε₁ 2^{-n}`** (the covering-event Borel–Cantelli
step): if CC7's covering of `K₁` by the events `F` fails at scale `ε` with probability `≤ c′ ε`
for every `ε < min(r₀, 1/16)`, then a.s. it holds at `ε_n` for all large `n`. -/
theorem ae_eventually_cover {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {K₁ : Set ℂ}
    {F : ℂ → ℝ → Set Ω} {r₀ c' ε₁ : ℝ} (hc' : 0 ≤ c') (hε₁ : 0 < ε₁)
    (hε₁r : ε₁ < min r₀ ((16 : ℕ) : ℝ)⁻¹)
    (hbad : ∀ ε ∈ Ioo (0 : ℝ) (min r₀ ((16 : ℕ) : ℝ)⁻¹),
      P {ω | ¬ ∀ z ∈ K₁, ∃ k : ℕ, ∃ m : ℤ × ℤ, ε ^ 2 ≤ ((16 : ℕ) : ℝ)⁻¹ ^ k * ε ∧
        ‖z - GM.gridPt (ε ^ 2 / 4) m‖ < ((16 : ℕ) : ℝ)⁻¹ ^ k * ε / 2 ∧
        ω ∈ F (GM.gridPt (ε ^ 2 / 4) m) (((16 : ℕ) : ℝ)⁻¹ ^ k * ε)} ≤
        ENNReal.ofReal (c' * ε ^ (1 : ℝ))) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ z ∈ K₁, ∃ k : ℕ, ∃ m : ℤ × ℤ,
      (ε₁ * (1 / 2) ^ n) ^ 2 ≤ ((16 : ℕ) : ℝ)⁻¹ ^ k * (ε₁ * (1 / 2) ^ n) ∧
      ‖z - GM.gridPt ((ε₁ * (1 / 2) ^ n) ^ 2 / 4) m‖ <
        ((16 : ℕ) : ℝ)⁻¹ ^ k * (ε₁ * (1 / 2) ^ n) / 2 ∧
      ω ∈ F (GM.gridPt ((ε₁ * (1 / 2) ^ n) ^ 2 / 4) m)
        (((16 : ℕ) : ℝ)⁻¹ ^ k * (ε₁ * (1 / 2) ^ n)) := by
  have hmem : ∀ n : ℕ, ε₁ * (1 / 2) ^ n ∈ Ioo (0 : ℝ) (min r₀ ((16 : ℕ) : ℝ)⁻¹) := fun n =>
    ⟨by positivity, lt_of_le_of_lt (mul_le_of_le_one_right hε₁.le
      (pow_le_one₀ (by norm_num) (by norm_num))) hε₁r⟩
  have hBC := ae_eventually_notMem_of_le_geom (P := P) (mul_nonneg hc' hε₁.le) fun n =>
    (hbad _ (hmem n)).trans_eq (by rw [Real.rpow_one, mul_assoc])
  filter_upwards [hBC] with ω hω
  filter_upwards [hω] with n hn
  exact not_not.1 hn

/-! ## 4. One compact set -/

/-- **The improvement on one compact set, almost surely** ([3] Prop 3.6, Steps 2–6; CC0 D15). For
a compact `K` with `cthickening κ K ⊆ V`, the good events `E` of `GoodAnnulusInput` for
`K₂ = cthickening κ K` (radii `≤ r₀`), and CC7's covering bound for the padded events on
`K₁ = cthickening (κ/2) K`: a.s. there is `ρ > 0` with
`D^ϕ(x,y) ≤ (1 + δ + A/(A+1)(C − 1 − δ)) D_h(x,y)` for `x, y ∈ K`, `‖x − y‖ ≤ ρ`. -/
theorem ae_local_improve {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {D : DistC → ContMetric}
    (hD : IsStrongLQGMetric γ D) {α A δ C : ℝ} (hα : 1 / 2 < α) (hα1 : α < 1) (hA : 0 ≤ A)
    (hδ : 0 ≤ δ) (hC : 1 + δ ≤ C) {ϕ : ℂ → ℂ} {W V : Set ℂ} (hϕ : IsConfNbhd ϕ W V)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h hbar : Ω → DistC} {f : Ω → C(ℂ, ℝ)} (hh : IsWholePlaneGFF h P)
    (hhb : IsWholePlaneGFF hbar P) (hf : Measurable f)
    (hratio : ∀ᵐ ω ∂P, ∀ z ∈ V, ∀ w ∈ V,
      confMetric D ϕ V (hbar ω) (f ω) z w ≤ ENNReal.ofReal C * (D (h ω)).internal V z w)
    {K : Set ℂ} (hK : IsCompact K) {κ : ℝ} (hκ : 0 < κ) (hKV : cthickening κ K ⊆ V)
    {r₀ : ℝ} (hr₀ : 0 < r₀) (E : ℂ → ℝ → Set Ω)
    (hE3 : ∀ᵐ ω ∂P, ∀ z ∈ cthickening κ K, ∀ r ∈ Ioc (0 : ℝ) r₀, ω ∈ E z r →
        (∀ u ∈ sphere z (α * r), ∀ u' ∈ sphere z r,
          GM.UniqueGeodIn (D (h ω)) u u' (closure (annulus z (α * r) r : Set ℂ)) →
            confMetric D ϕ V (hbar ω) (f ω) u u' ≤
              ENNReal.ofReal ((1 + δ) * (D (h ω)).1 (u, u'))) ∧
        ∃ (a' b' : ℝ) (G : ℝ → ℂ),
          Disconnects (G '' Icc a' b') (sphere z (α * r)) (sphere z r) ∧
          (D (h ω)).len G a' b' ≤
            ENNReal.ofReal A * setDist (D (h ω)) (sphere z (α * r)) (sphere z r))
    {c' : ℝ} (hc' : 0 ≤ c')
    (hbad : ∀ ε ∈ Ioo (0 : ℝ) (min r₀ ((16 : ℕ) : ℝ)⁻¹),
      P {ω | ¬ ∀ z ∈ cthickening (κ / 2) K, ∃ k : ℕ, ∃ m : ℤ × ℤ,
        ε ^ 2 ≤ ((16 : ℕ) : ℝ)⁻¹ ^ k * ε ∧
        ‖z - GM.gridPt (ε ^ 2 / 4) m‖ < ((16 : ℕ) : ℝ)⁻¹ ^ k * ε / 2 ∧
        ω ∈ padEv E (cthickening κ K) r₀ (GM.gridPt (ε ^ 2 / 4) m)
          (((16 : ℕ) : ℝ)⁻¹ ^ k * ε)} ≤ ENNReal.ofReal (c' * ε ^ (1 : ℝ))) :
    ∀ᵐ ω ∂P, ∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ ρ →
      confMetric D ϕ V (hbar ω) (f ω) x y ≤
        ENNReal.ofReal ((1 + δ + A / (A + 1) * (C - 1 - δ)) * (D (h ω)).1 (x, y)) := by
  -- the scales `ε_n = ε₁ 2^{-n}`, `ε₁ ≤ min(r₀, 1/16, κ)/2`
  have hm0 : 0 < min (min r₀ ((16 : ℕ) : ℝ)⁻¹) κ := lt_min (lt_min hr₀ (by norm_num)) hκ
  set ε₁ : ℝ := min (min r₀ ((16 : ℕ) : ℝ)⁻¹) κ / 2 with hε₁
  have hε₁0 : 0 < ε₁ := half_pos hm0
  have hε₁r : ε₁ < min r₀ ((16 : ℕ) : ℝ)⁻¹ := by
    have := min_le_left (min r₀ ((16 : ℕ) : ℝ)⁻¹) κ
    linarith
  have hε₁κ : ε₁ ≤ κ := by
    have := min_le_right (min r₀ ((16 : ℕ) : ℝ)⁻¹) κ
    linarith
  have hε₁r₀ : ε₁ < r₀ := lt_of_lt_of_le hε₁r (min_le_left _ _)
  have hε0 : ∀ n : ℕ, 0 < ε₁ * (1 / 2) ^ n := fun n => by positivity
  have hεle : ∀ n : ℕ, ε₁ * (1 / 2) ^ n ≤ ε₁ := fun n =>
    mul_le_of_le_one_right hε₁0.le (pow_le_one₀ (by norm_num) (by norm_num))
  have hεlim : Tendsto (fun n : ℕ => ε₁ * (1 / 2) ^ n) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
      (by norm_num)).const_mul ε₁
    simpa only [mul_zero] using this
  filter_upwards [ae_exists_geod01_all hγ hγ2 hD P h hh,
    GM.gm_S1_2_rat mqThm1_2Weak_holds hγ hγ2 (GM.gm_eq1_15 hγ hD) P h hh,
    ae_continuousOn_confMetric hD hhb hf, hratio, hE3,
    ae_eventually_cover hc' hε₁0 hε₁r hbad] with ω hex hun hcont hrat hgood hcov
  refine local_improve_det (D (h ω)) (d' := confMetric D ϕ V (hbar ω) (f ω))
    confMetric_triangle (fun z hz => confMetric_self hz) (hcont ϕ W V hϕ) hex hun hα hα1 hA hδ
    hC hrat hK hκ hKV (fun v r => v ∈ cthickening κ K ∧ r ∈ Ioc (0 : ℝ) r₀ ∧ ω ∈ E v r)
    (fun v r hg => (hgood v hg.1 r hg.2.1 hg.2.2).1)
    (fun v r hg => (hgood v hg.1 r hg.2.1 hg.2.2).2) hε0 hεlim ?_
  filter_upwards [hcov] with n hn
  intro x hx
  obtain ⟨k, m, h1, h2, h3⟩ := hn x hx
  have hk1 : ((16 : ℕ) : ℝ)⁻¹ ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hk0 : 0 < ((16 : ℕ) : ℝ)⁻¹ ^ k := by positivity
  have hrε : ((16 : ℕ) : ℝ)⁻¹ ^ k * (ε₁ * (1 / 2) ^ n) ≤ ε₁ * (1 / 2) ^ n :=
    mul_le_of_le_one_left (hε0 n).le hk1
  have hr0 : 0 < ((16 : ℕ) : ℝ)⁻¹ ^ k * (ε₁ * (1 / 2) ^ n) := mul_pos hk0 (hε0 n)
  have hrr₀ : ((16 : ℕ) : ℝ)⁻¹ ^ k * (ε₁ * (1 / 2) ^ n) ≤ r₀ := by
    linarith [hεle n]
  have hv : GM.gridPt ((ε₁ * (1 / 2) ^ n) ^ 2 / 4) m ∈ cthickening κ K := by
    have hvx : edist (GM.gridPt ((ε₁ * (1 / 2) ^ n) ^ 2 / 4) m) x ≤ ENNReal.ofReal (κ / 2) := by
      rw [edist_dist, dist_eq_norm, norm_sub_rev]
      exact ENNReal.ofReal_le_ofReal (by linarith [hεle n])
    have h4 := cthickening_cthickening_subset (by linarith : (0 : ℝ) ≤ κ / 2)
      (by linarith : (0 : ℝ) ≤ κ / 2) K
      (mem_cthickening_of_edist_le _ x (κ / 2) (cthickening (κ / 2) K) hx hvx)
    rwa [add_halves] at h4
  refine ⟨GM.gridPt ((ε₁ * (1 / 2) ^ n) ^ 2 / 4) m, ((16 : ℕ) : ℝ)⁻¹ ^ k * (ε₁ * (1 / 2) ^ n),
    ⟨h1, hrε, hv, ⟨hr0, hrr₀⟩, h3 hv hrr₀⟩, ?_⟩
  rw [mem_ball, dist_eq_norm]
  exact h2

/-! ## 5. The improvement step -/

/-- **[3] Proposition 3.6, the improvement step, for a strong metric** (CC0 D15; rulings G21,
G29): the good-annulus input gives `ConfImprove` with `θ = A/(A+1)`, `A` from `GoodAnnulusInput`
at the probability `p` of CC7's covering lemma (`N = 16`, `q = 1`). -/
theorem confImprove_of_goodAnnulus_strong {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {D : DistC → ContMetric} (hD : IsStrongLQGMetric γ D) (hG : GoodAnnulusInput γ D) :
    ConfImprove γ D := by
  obtain ⟨p, c, -, hp1, hc0, Hcov⟩ := coverLemma_uniform 4 (1 / 16) (1 / 2) 16 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 1 one_pos
  obtain ⟨α, A, hα, hα1, hA, HG⟩ := hG p hp1
  refine ⟨A / (A + 1), div_nonneg hA (by linarith), (div_lt_one (by linarith)).2 (by linarith), ?_⟩
  intro δ hδ C hC ϕ W V hϕ Ω _ P _ h hbar f hh hhb hf hc hratio
  -- the local bound on every compact set, almost surely
  have hloc : ∀ K : Set ℂ, IsCompact K → K ⊆ V → ∀ᵐ ω ∂P, ∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ K, ∀ y ∈ K,
      ‖x - y‖ ≤ ρ → confMetric D ϕ V (hbar ω) (f ω) x y ≤
        ENNReal.ofReal ((1 + δ + A / (A + 1) * (C - 1 - δ)) * (D (h ω)).1 (x, y)) := by
    intro K hK hKV
    obtain ⟨κ, hκ, hκV⟩ := hK.exists_cthickening_subset_open hϕ.isOpen_V hKV
    obtain ⟨r₀, hr₀, HE⟩ := HG ϕ W V hϕ δ hδ (cthickening κ K) hK.cthickening hκV
    obtain ⟨E, hE1, hE2, hE3⟩ := HE P h hbar f hh hhb hf hc
    obtain ⟨R, hR⟩ := (hK.cthickening (r := κ / 2)).isBounded.subset_closedBall (0 : ℂ)
    have hR₀ : cthickening (κ / 2) K ⊆ closedBall (0 : ℂ) (max R 0) :=
      hR.trans (closedBall_subset_closedBall (le_max_left _ _))
    exact ae_local_improve hγ hγ2 hD hα hα1 hA hδ.le hC hϕ hh hhb hf hratio hK hκ hκV hr₀ E
      hE3 (mul_nonneg hc0.le (sq_nonneg _))
      (Hcov P h hh _ (isAnnulusLocal_padEv hE1) _ (max R 0) (le_max_right _ _) hR₀ r₀
        (fun w _ r hr => prob_padEv hp1 hE2 w r hr))
  -- all compacts at once, through a countable exhaustion of `V`
  obtain ⟨Kn, hKnc, hKnV, hKn⟩ := exists_compact_exhaustion hϕ.isOpen_V
  have hall : ∀ᵐ ω ∂P, ∀ n, ∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ Kn n, ∀ y ∈ Kn n, ‖x - y‖ ≤ ρ →
      confMetric D ϕ V (hbar ω) (f ω) x y ≤
        ENNReal.ofReal ((1 + δ + A / (A + 1) * (C - 1 - δ)) * (D (h ω)).1 (x, y)) :=
    ae_all_iff.2 fun n => hloc (Kn n) (hKnc n) (hKnV n)
  have hCδ : 0 < 1 + δ + A / (A + 1) * (C - 1 - δ) := by
    have : 0 ≤ A / (A + 1) * (C - 1 - δ) :=
      mul_nonneg (div_nonneg hA (by linarith)) (by linarith)
    linarith
  -- local to global (CC8a, ruling G26: `0 < C_δ`)
  filter_upwards [hall] with ω hω z _ w _
  refine le_mul_internal_of_local (D (h ω)) confMetric_triangle hCδ (fun K hK hKV => ?_) z w
  obtain ⟨n, hn⟩ := hKn K hK hKV
  obtain ⟨ρ, hρ, H⟩ := hω n
  exact ⟨ρ, hρ, fun x hx y hy hxy => H x (hn hx) y (hn hy) hxy⟩

/-- **[3] Proposition 3.6, the improvement step** (packet CC10; CC0 D15; rulings G21, G29): for the
canonical γ-LQG metric, the good-annulus input gives `ConfImprove`. -/
theorem confImprove_of_goodAnnulus {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {D : DistC → ContMetric}
    (hD : GaussianLQG.IsCanonicalLQGMetric γ D) (hG : GoodAnnulusInput γ D) : ConfImprove γ D :=
  confImprove_of_goodAnnulus_strong hγ hγ2 hD.1 hG

end SmallGammaGeodesics.CC
