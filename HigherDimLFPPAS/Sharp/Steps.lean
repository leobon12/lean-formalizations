import HigherDimLFPPAS.Sharp.Events
import HigherDimLFPPAS.Windows.ShrinkingBalls
import HigherDimLFPPAS.Proper.Lemma22

/-!
# Proposition 5.1, Steps 2–3: few low and few high windows (packet P51)

Source: `planning/audits/MA2-sections-4-6.md` §§2.14–2.15, Details D-B4 and D-B5; MA4 §2.5; paper §5,
Steps 2–3. Outer-measure form (MA2 §4.1 item 3): only monotonicity and subadditivity of the outer
measure are used, plus measurability of the evaluations `ω ↦ D_h(p)` of the limit metric (a measurable
assignment of a measurable field).

* **Step 2** (`p51_low_eventually`): for all small `ε`, fewer than `N` of the windows `1, …, 3N` are
  *low* (at least a quarter of the radii have `c_ε(r) ≤ 1 − t`). Otherwise, along `ε_k ↓ 0`, the forward
  contraction over the low windows gives `Comp(D → M_{ε_k}, λ₋, v_{3N})` with `λ₋ < 1` off an event of
  outer probability `→ 0`; applied to a unit-speed `D`-geodesic from `0` to `e₁` inside a deterministic
  ball (an event of positive outer probability, `p51_exists_geo_radius`), the `M_{ε_k}`-distance `Y_k`
  between the shrinking endpoint balls satisfies `Y_k ≤ λ₋ D(0, e₁)`, while `Y_k → D(0, e₁)` in
  probability (D-B5, `Windows.tendstoInProbLU_winShrinkInf`, from Lemma 2.4(i)) and `D(0, e₁) > 0`
  surely: contradiction (`p51_contra`).
* **Step 3** (`p51_high_eventually`): the same for *high* windows (a quarter with `c_ε(r) ≥ (1 − t)⁻¹`),
  with the reverse contraction (`c⁻¹ ≤ 1 − t`) along a unit-speed `M_{ε_k}`-geodesic from `0` to `e₁`,
  confined with outer probability `≥ 1/2` by Lemma 2.4(ii): `X_k ≤ λ₋ M_{ε_k}(0, e₁)`, where the
  `D`-distance `X_k` between the shrinking balls tends to `D(0, e₁)` and `M_{ε_k}(0, e₁) → D(0, e₁)` in
  probability.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLFPPAS.SharpComp

open HigherDimLQGMetric
open HigherDimLFPP (Rd e₁)
open HigherDimLFPPAS.Core
open HigherDimLFPPAS.Windows

variable {d : ℕ}

/-! ### Abstract limit lemmas -/

/-- If `c ≤ f_k + b + g_k` for all `k` with `f_k, g_k → 0`, then `c ≤ b`. -/
theorem p51_le_of_tendsto {c b : ℝ≥0∞} {f g : ℕ → ℝ≥0∞} (hf : Tendsto f atTop (𝓝 0))
    (hg : Tendsto g atTop (𝓝 0)) (hle : ∀ k, c ≤ f k + b + g k) : c ≤ b := by
  have hlim : Tendsto (fun k => f k + b + g k) atTop (𝓝 (0 + b + 0)) :=
    (hf.add tendsto_const_nhds).add hg
  rw [zero_add, add_zero] at hlim
  exact ge_of_tendsto' hlim hle

/-- A positive measurable random variable has `P(X < s) → 0` as `s ↓ 0`; hence no `c ≠ 0` is a lower
bound of all `P(X < s)`. -/
theorem p51_contra {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : Measurable X) (hpos : ∀ ω, 0 < X ω) {c : ℝ≥0∞} (hc : c ≠ 0)
    (hb : ∀ s : ℝ, 0 < s → c ≤ P {ω | X ω < s}) : False := by
  let A : ℕ → Set Ω := fun n => {ω | X ω < 1 / ((n : ℝ) + 1)}
  have hanti : Antitone A := by
    intro n m hnm ω hω
    have hω' : X ω < 1 / ((m : ℝ) + 1) := hω
    show X ω < 1 / ((n : ℝ) + 1)
    have hnm' : (n : ℝ) + 1 ≤ (m : ℝ) + 1 := by
      have : (n : ℝ) ≤ m := Nat.cast_le.2 hnm
      linarith
    exact lt_of_lt_of_le hω' (one_div_le_one_div_of_le (by positivity) hnm')
  have hlim := tendsto_measure_iInter_atTop (μ := P) (s := A)
    (fun n => (measurableSet_lt hX measurable_const).nullMeasurableSet) hanti
    ⟨0, measure_ne_top P _⟩
  have hempty : (⋂ n, A n) = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.2 fun ω hω => ?_
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (hpos ω)
    have hωn : X ω < 1 / ((n : ℝ) + 1) := Set.mem_iInter.1 hω n
    exact lt_asymm hωn hn
  rw [hempty, measure_empty] at hlim
  have hle : c ≤ 0 := ge_of_tendsto' hlim (fun n => hb _ (by positivity))
  exact hc (le_antisymm hle bot_le)

/-! ### Measurability, constant sequences, shrinking balls -/

/-- Evaluations of the limit metric are measurable (measurable assignment of a measurable field). -/
theorem p51_measurable_eval {κ : Rd d → ℝ} {ξ Q : ℝ} {D : DistRd d → ContMetric d}
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistRd d}
    (hS : Setting d ξ Q κ D P h) (p : Rd d × Rd d) : Measurable fun ω => (D (h ω)).1 p :=
  (continuous_eval_const p).measurable.comp
    (measurable_subtype_coe.comp (hS.strong.measurable.comp hS.field.1.measurable))

/-- A constant sequence converges in probability, locally uniformly, to its value. -/
theorem p51_tendstoInProbLU_const {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → Rd d × Rd d → ℝ) : TendstoInProbLU P (fun (_ : ℕ) => X) atTop X := by
  intro R _ δ hδ
  have hfalse : ∀ ω, ¬ ENNReal.ofReal δ ≤
      ⨆ p ∈ closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R, edist (X ω p) (X ω p) := by
    intro ω hle
    simp only [edist_self] at hle
    have h0 : (⨆ p ∈ closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R, (0 : ℝ≥0∞)) = 0 := by
      simp
    rw [h0, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at hle
    linarith
  have hset : {ω | ENNReal.ofReal δ ≤
      ⨆ p ∈ closedBall (0 : Rd d) R ×ˢ closedBall (0 : Rd d) R, edist (X ω p) (X ω p)} = ∅ :=
    Set.eq_empty_iff_forall_notMem.2 fun ω hω => hfalse ω hω
  simp only [hset, measure_empty]
  exact tendsto_const_nhds

/-- The infimum of `G` over a product of closed balls is at most the internal set distance between
the open balls (global `≤` internal). -/
theorem p51_ofReal_inf_le_setDistIn (G : ContMetric d) (x y : Rd d) (ρ : ℝ) (V : Set (Rd d)) :
    ENNReal.ofReal (⨅ p : winShrinkPair x y ρ, G.1 p.1) ≤ setDistIn G V (ball x ρ) (ball y ρ) := by
  unfold setDistIn
  refine le_iInf₂ fun u hu => le_iInf₂ fun v hv => ?_
  have hbdd : BddBelow (Set.range fun p : winShrinkPair x y ρ => G.1 p.1) :=
    ⟨0, by rintro _ ⟨p, rfl⟩; exact G.nonneg p.1.1 p.1.2⟩
  have hmem : (u, v) ∈ closedBall x ρ ×ˢ closedBall y ρ :=
    ⟨ball_subset_closedBall hu, ball_subset_closedBall hv⟩
  calc ENNReal.ofReal (⨅ p : winShrinkPair x y ρ, G.1 p.1)
      ≤ ENNReal.ofReal (G.1 (u, v)) := ENNReal.ofReal_le_ofReal (ciInf_le hbdd ⟨(u, v), hmem⟩)
    _ ≤ G.internal V u v := G.ofReal_le_internal V u v

/-! ### Geodesics -/

/-- The event that some unit-speed `G`-geodesic from `0` to `e₁` lies in `B_r`. -/
def p51GeoIn (G : ContMetric d) (r : ℝ) : Prop :=
  ∃ (γ : ℝ → Rd d) (T : ℝ), 0 ≤ T ∧ γ 0 = 0 ∧ γ T = e₁ d ∧ ContinuousOn γ (Icc 0 T) ∧
    MapsTo γ (Icc 0 T) (ball 0 r) ∧ ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, G.1 (γ s, γ t) = |t - s|

/-- There is a deterministic radius `r ≥ 2` such that, with positive outer probability, a unit-speed
`D`-geodesic from `0` to `e₁` lies in `B_r` (Lemma 2.2: a.s. `D` is a proper length metric, so a
unit-speed geodesic exists; its image is compact). -/
theorem p51_exists_geo_radius {κ : Rd d → ℝ} {ξ Q : ℝ} {D : DistRd d → ContMetric d}
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hS : Setting d ξ Q κ D P h) : ∃ r : ℝ, 2 ≤ r ∧ P {ω | p51GeoIn (D (h ω)) r} ≠ 0 := by
  have hae : ∀ᵐ ω ∂P, ∃ n : ℕ, p51GeoIn (D (h ω)) n := by
    filter_upwards [HigherDimLFPPAS.lemma22_ae_proper_and_geodesic hS.dim hS.xi_pos hS.subcrit P h
      hS.field D hS.strong, hS.strong.length P h hS.field.1.isLGFPlusCont] with ω hprop hlen
    have : ProperSpace (D (h ω)).Space := hprop.1
    obtain ⟨γ, h0, h1, hgeo, -, hunit⟩ := (D (h ω)).exists_geodesic hlen 0 (e₁ d)
    have hT : 0 ≤ (D (h ω)).1 (0, e₁ d) := (D (h ω)).nonneg _ _
    have hcont : ContinuousOn γ (Icc 0 ((D (h ω)).1 (0, e₁ d))) :=
      (D (h ω)).continuousOn_pt_comp_iff.1 hgeo.2.1
    obtain ⟨r, hr⟩ :=
      (isCompact_Icc.image_of_continuousOn hcont).isBounded.subset_ball (0 : Rd d)
    obtain ⟨n, hn⟩ := exists_nat_gt r
    exact ⟨n, γ, _, hT, h0, h1, hcont,
      fun t ht => ball_subset_ball hn.le (hr ⟨t, ht, rfl⟩), hunit⟩
  by_contra hcon
  push Not at hcon
  have hnull : ∀ n : ℕ, P {ω | p51GeoIn (D (h ω)) n} = 0 := by
    intro n
    refine measure_mono_null ?_ (hcon (max n 2) (le_max_right _ _))
    rintro ω ⟨γ, T, hT, h0, h1, hc, hmaps, hunit⟩
    exact ⟨γ, T, hT, h0, h1, hc, fun t ht => ball_subset_ball (le_max_left _ _) (hmaps ht), hunit⟩
  have hU : P (⋃ n : ℕ, {ω | p51GeoIn (D (h ω)) n}) = 0 := (measure_iUnion_null_iff (μ := P)).2 hnull
  have hC : P {ω | ¬ ∃ n : ℕ, p51GeoIn (D (h ω)) n} = 0 := ae_iff.1 hae
  have huniv : (Set.univ : Set Ω) ⊆ (⋃ n : ℕ, {ω | p51GeoIn (D (h ω)) n}) ∪
      {ω | ¬ ∃ n : ℕ, p51GeoIn (D (h ω)) n} := by
    intro ω _
    by_cases hω : ∃ n : ℕ, p51GeoIn (D (h ω)) n
    · exact Or.inl (Set.mem_iUnion.2 hω)
    · exact Or.inr hω
  have hle := (measure_mono (μ := P) huniv).trans (measure_union_le (μ := P) _ _)
  rw [hU, hC, add_zero, measure_univ] at hle
  exact one_ne_zero (le_antisymm hle bot_le)

/-- A unit-speed curve is a geodesic curve (its length is computed through `UnitSpeedAdmissible`
inside a ball containing its compact image). -/
theorem p51_isGeodesicCurve_of_unit (hus : UnitSpeedAdmissible d) {G : ContMetric d}
    {γ : ℝ → Rd d} {T : ℝ} (hT : 0 ≤ T) (hc : ContinuousOn γ (Icc 0 T))
    (hunit : ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, G.1 (γ s, γ t) = |t - s|) :
    LQGMetric.MetricGeometry.IsGeodesicCurve (G.pt ∘ γ) 0 T := by
  obtain ⟨r, hr⟩ := (isCompact_Icc.image_of_continuousOn hc).isBounded.subset_ball (0 : Rd d)
  obtain ⟨-, -, -, -, hlen⟩ := hus G r γ T hT hc (fun t ht => hr ⟨t, ht, rfl⟩) hunit
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  have hT' : T ∈ Icc 0 T := ⟨hT, le_rfl⟩
  refine ⟨hT, G.continuous_pt.comp_continuousOn hc, ?_⟩
  have hl : G.len γ 0 T = ENNReal.ofReal (T - 0) := hlen 0 h0 T hT' hT
  rw [G.len_def] at hl
  rw [hl, Function.comp_apply, Function.comp_apply, G.edist_pt, hunit 0 h0 T hT', sub_zero,
    abs_of_nonneg hT]

/-- For a unit-speed curve with image in `B_R`, the comparison property yields the bound of the set
distance between the endpoint balls by the constant times `T` (`len = T`). -/
theorem p51_comp_apply_unit (hus : UnitSpeedAdmissible d) {G G' : ContMetric d} {R ε q C : ℝ}
    (hcomp : Comp G G' R ε q C) {γ : ℝ → Rd d} {T : ℝ} (hT : 0 ≤ T) (hc : ContinuousOn γ (Icc 0 T))
    (hmaps : MapsTo γ (Icc 0 T) (ball 0 R))
    (hunit : ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, G.1 (γ s, γ t) = |t - s|) :
    setDistIn G' (ball 0 (R + 2)) (ball (γ 0) (8 * ε ^ q)) (ball (γ T) (8 * ε ^ q)) ≤
      ENNReal.ofReal C * ENNReal.ofReal T := by
  have hIG := hus G R γ T hT hc hmaps hunit
  have hlen : G.len γ 0 T = ENNReal.ofReal T := by
    obtain ⟨-, -, -, -, hl⟩ := hIG
    rw [hl 0 ⟨le_rfl, hT⟩ T ⟨hT, le_rfl⟩ hT, sub_zero]
  rw [← hlen]
  exact hcomp γ T hIG hmaps

/-! ### Step 2: few low windows -/

open Classical in
/-- **Step 2** (MA2 §2.14, D-B4): for all small `ε`, fewer than `N` of the windows `1, …, 3N` are low. -/
theorem p51_low_eventually {κ : Rd d → ℝ} {ξ Q : ℝ} {D : DistRd d → ContMetric d}
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hS : Setting d ξ Q κ D P h) (h41 : Prop41Stmt d) (hus : UnitSpeedAdmissible d)
    (h24c : Lemma24Conv κ ξ D P h) {A C₀ β₀ : ℝ} (hA : 1 ≤ A) (hC₀ : 2 ≤ C₀) (hβ₀ : 0 < β₀)
    (h33 : p51H33 κ ξ Q D P h A) (h27 : p51H27 κ ξ D P h C₀ β₀) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ1 : δ < 1) {N : ℕ} (hN : (A / (A + 1)) ^ N * C₀ < δ / 16) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ((Finset.Icc 1 (3 * N)).filter
      (fun i => winIsLow (p51W ε i) (cRatio κ ξ Q ε) (winMMinus δ))).card < N := by
  have hθ0 : 0 < A / (A + 1) := div_pos (by linarith) (by linarith)
  have hθ1 : A / (A + 1) < 1 := (div_lt_one (by linarith)).2 (by linarith)
  have hη : 0 < winEta δ (A / (A + 1)) := winEta_pos hδ0 hθ1
  have hm0 : 0 < winMMinus δ := p51_winMMinus_pos hδ1
  have hmC : winMMinus δ ≤ C₀ := by
    unfold winMMinus winT
    linarith
  set lam : ℝ := (A / (A + 1)) ^ N * C₀ + winMMinus δ * (1 + δ / 10) with hlam
  have hlam1 : lam < 1 := p51_lambda_minus_lt_one hδ0 hδ1 hθ1 hN
  have hlam0 : 0 ≤ lam := by
    have h1 : 0 ≤ (A / (A + 1)) ^ N * C₀ := mul_nonneg (pow_nonneg hθ0.le N) (by linarith)
    have h2 : 0 ≤ winMMinus δ * (1 + δ / 10) := mul_nonneg hm0.le (by linarith)
    linarith
  obtain ⟨RE, hRE, hEpos⟩ := p51_exists_geo_radius hS
  obtain ⟨K, hK⟩ := p51_failure h33 h27 hη (3 * N) (R := RE) (by linarith)
  have hP41 := p51_P41_eventually (by linarith [hS.dim] : 1 ≤ d) h41 hA hη (3 * N)
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  obtain ⟨εs, hεs, hεsP⟩ := Filter.exists_seq_forall_of_frequently
    ((hcon.and_eventually (hK.and hP41)).and_eventually (Ioo_mem_nhdsGT one_pos))
  -- the data along the sequence
  have hεpos : ∀ k, 0 < εs k := fun k => (hεsP k).2.1
  have hεle : ∀ k, εs k ≤ 1 := fun k => (hεsP k).2.2.le
  have hεs0 : Tendsto εs atTop (𝓝 0) := (tendsto_nhdsWithin_iff.1 hεs).1
  let ρ : ℕ → ℝ := fun k => 8 * εs k ^ winV (3 * N)
  have hρ : Tendsto ρ atTop (𝓝 0) := by
    have h1 : Tendsto (fun k => εs k ^ winV (3 * N)) atTop (𝓝 ((0 : ℝ) ^ winV (3 * N))) :=
      ((Real.continuousAt_rpow_const 0 (winV (3 * N))
        (Or.inr (p51_winV_pos _).le)).tendsto).comp hεs0
    rw [Real.zero_rpow (p51_winV_pos _).ne'] at h1
    simpa using h1.const_mul 8
  have hρpos : ∀ k, 0 < ρ k := fun k => mul_pos (by norm_num) (Real.rpow_pos_of_pos (hεpos k) _)
  let Xn : ℕ → Ω → Rd d × Rd d → ℝ := fun k ω => ⇑(Meps κ ξ (εs k) (h ω)).1
  let Xlim : Ω → Rd d × Rd d → ℝ := fun ω => ⇑(D (h ω)).1
  have hconv : TendstoInProbLU P Xn atTop Xlim := fun R hR δ' hδ' => (h24c R hR δ' hδ').comp hεs
  have hY := tendstoInProbLU_winShrinkInf P Xn Xlim hconv ρ hρ hρpos
    (fun p => p51_measurable_eval hS p) (fun ω => (D (h ω)).1.continuous) 0 (e₁ d)
  have hβ : 0 < min β₀ (winU (3 * N)) := lt_min hβ₀ (winU_pos _)
  have hKlim : Tendsto (fun k => ENNReal.ofReal (K * εs k ^ min β₀ (winU (3 * N)))) atTop
      (𝓝 0) := by
    have h1 : Tendsto (fun k => εs k ^ min β₀ (winU (3 * N))) atTop
        (𝓝 ((0 : ℝ) ^ min β₀ (winU (3 * N)))) :=
      ((Real.continuousAt_rpow_const 0 _ (Or.inr hβ.le)).tendsto).comp hεs0
    rw [Real.zero_rpow hβ.ne'] at h1
    simpa using ENNReal.tendsto_ofReal (h1.const_mul K)
  -- the low windows along the sequence and their low radii
  let S : ℕ → Finset ℕ := fun k => (Finset.Icc 1 (3 * N)).filter
    (fun i => winIsLow (p51W (εs k) i) (cRatio κ ξ Q (εs k)) (winMMinus δ))
  let Rs : ℕ → ℕ → Finset ℝ := fun k b =>
    winLowRadii (p51W (εs k) b) (cRatio κ ξ Q (εs k)) (winMMinus δ)
  have hεlt1 : ∀ k, εs k < 1 := fun k => (hεsP k).2.2
  have hSmem : ∀ k, ∀ b ∈ S k, (1 ≤ b ∧ b ≤ 3 * N) ∧
      winIsLow (p51W (εs k) b) (cRatio κ ξ Q (εs k)) (winMMinus δ) := by
    intro k b hb
    rw [Finset.mem_filter, Finset.mem_Icc] at hb
    exact hb
  have hScard : ∀ k, N ≤ (S k).card := fun k => not_lt.1 (hεsP k).1.1
  have hRsmem : ∀ k b r, r ∈ Rs k b →
      r ∈ p51W (εs k) b ∧ cRatio κ ξ Q (εs k) r ≤ winMMinus δ := fun k b r hr =>
    Finset.mem_filter.1 hr
  have hbad : ∀ k, P (p51Bad κ ξ Q D h A (winEta δ (A / (A + 1))) C₀ RE (εs k) (S k) (Rs k)) ≤
      ENNReal.ofReal (K * εs k ^ min β₀ (winU (3 * N))) := by
    intro k
    refine (hεsP k).1.2.1 (S k) (Rs k) ?_
    intro b hb
    obtain ⟨hbI, hlow⟩ := hSmem k b hb
    refine ⟨hbI.2, fun r hr => p51_mem_W (hεpos k) (hεlt1 k) (hRsmem k b r hr).1, ?_⟩
    rw [p51_ncard_W (hεpos k) (hεlt1 k)]
    exact hlow
  have hcomp : ∀ k, ∀ ω,
      ω ∉ p51Bad κ ξ Q D h A (winEta δ (A / (A + 1))) C₀ RE (εs k) (S k) (Rs k) →
      Comp (D (h ω)) (Meps κ ξ (εs k) (h ω)) RE (εs k) (winV (3 * N)) lam := by
    intro k ω hω
    obtain ⟨hinit, hcov⟩ := p51_not_bad hω
    have hc := p51_good_forward hA hη hRE (hεpos k) (hεle k) hm0.le hmC (hεsP k).1.2.2 (S k)
      (fun b hb => (hSmem k b hb).1) (Rs k)
      (fun b _ r hr => ⟨p51_mem_W (hεpos k) (hεlt1 k) (hRsmem k b r hr).1,
        p51_cRatio_pos (hS.seed.aEps_pos ξ) (hεpos k)
          (p51_pos_of_mem_window (p51_mem_W (hεpos k) (hεlt1 k) (hRsmem k b r hr).1)),
        (hRsmem k b r hr).2⟩) hinit hcov
    exact p51_comp_mono_C
      (p51_winIter_le_of_ge hθ0 hθ1 (by linarith) hm0.le hδ0.le (hScard k)) hc
  -- the limit variable and the shrinking-ball distances
  let X : Ω → ℝ := fun ω => (D (h ω)).1 (0, e₁ d)
  have hXmeas : Measurable X := p51_measurable_eval hS (0, e₁ d)
  have hd0 : 0 < d := by linarith [hS.dim]
  have hXpos : ∀ ω, 0 < X ω := fun ω =>
    (D (h ω)).apply_pos (HigherDimLFPP.e₁_ne_zero hd0).symm
  let Y : ℕ → Ω → ℝ := fun k ω => winShrinkInf (Xn k) 0 (e₁ d) ρ k ω
  have hincl : ∀ s : ℝ, 0 < s → ∀ k, {ω | p51GeoIn (D (h ω)) RE} ⊆
      ({ω | ENNReal.ofReal ((1 - lam) * s) ≤ edist (Y k ω) (X ω)} ∪ {ω | X ω < s}) ∪
        p51Bad κ ξ Q D h A (winEta δ (A / (A + 1))) C₀ RE (εs k) (S k) (Rs k) := by
    intro s _ k ω hω
    by_cases hb : ω ∈ p51Bad κ ξ Q D h A (winEta δ (A / (A + 1))) C₀ RE (εs k) (S k) (Rs k)
    · exact Or.inr hb
    · left
      obtain ⟨γ, T, hT, h0, h1, hc, hmaps, hunit⟩ := hω
      have hset := p51_comp_apply_unit hus (hcomp k ω hb) hT hc hmaps hunit
      rw [h0, h1] at hset
      have hTX : T = X ω := by
        have h2 := hunit 0 ⟨le_rfl, hT⟩ T ⟨hT, le_rfl⟩
        rw [h0, h1, sub_zero, abs_of_nonneg hT] at h2
        exact h2.symm
      have hYle : ENNReal.ofReal (Y k ω) ≤ ENNReal.ofReal (lam * X ω) := by
        have h2 := p51_ofReal_inf_le_setDistIn (Meps κ ξ (εs k) (h ω)) 0 (e₁ d) (ρ k)
          (ball 0 (RE + 2))
        rw [ENNReal.ofReal_mul hlam0, ← hTX]
        exact h2.trans hset
      have hYle' : Y k ω ≤ lam * X ω :=
        (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hlam0 (hXpos ω).le)).1 hYle
      by_cases hXs : X ω < s
      · exact Or.inr hXs
      · left
        push Not at hXs
        show ENNReal.ofReal ((1 - lam) * s) ≤ edist (Y k ω) (X ω)
        rw [edist_dist, Real.dist_eq, abs_sub_comm]
        apply ENNReal.ofReal_le_ofReal
        have h3 : (1 - lam) * s ≤ (1 - lam) * X ω := mul_le_mul_of_nonneg_left hXs (by linarith)
        calc (1 - lam) * s ≤ (1 - lam) * X ω := h3
          _ = X ω - lam * X ω := by ring
          _ ≤ X ω - Y k ω := by linarith
          _ ≤ |X ω - Y k ω| := le_abs_self _
  have hstep : ∀ s : ℝ, 0 < s → P {ω | p51GeoIn (D (h ω)) RE} ≤ P {ω | X ω < s} := by
    intro s hs
    have hα : 0 < (1 - lam) * s := mul_pos (by linarith) hs
    refine p51_le_of_tendsto (hY _ hα) hKlim (fun k => ?_)
    calc P {ω | p51GeoIn (D (h ω)) RE}
        ≤ P (({ω | ENNReal.ofReal ((1 - lam) * s) ≤ edist (Y k ω) (X ω)} ∪ {ω | X ω < s}) ∪
            p51Bad κ ξ Q D h A (winEta δ (A / (A + 1))) C₀ RE (εs k) (S k) (Rs k)) :=
          measure_mono (hincl s hs k)
      _ ≤ P {ω | ENNReal.ofReal ((1 - lam) * s) ≤ edist (Y k ω) (X ω)} + P {ω | X ω < s} +
            P (p51Bad κ ξ Q D h A (winEta δ (A / (A + 1))) C₀ RE (εs k) (S k) (Rs k)) :=
          (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
      _ ≤ P {ω | ENNReal.ofReal ((1 - lam) * s) ≤ edist (Y k ω) (X ω)} + P {ω | X ω < s} +
            ENNReal.ofReal (K * εs k ^ min β₀ (winU (3 * N))) := add_le_add le_rfl (hbad k)
  exact p51_contra P X hXmeas hXpos hEpos hstep

/-! ### Step 3: few high windows -/

theorem p51_winMPlus_inv (δ : ℝ) : (winMPlus δ)⁻¹ = winMMinus δ := by
  unfold winMPlus winMMinus
  rw [inv_inv]

open Classical in
/-- **Step 3** (MA2 §2.15, D-B4): for all small `ε`, fewer than `N` of the windows `1, …, 3N` are
high. -/
theorem p51_high_eventually {κ : Rd d → ℝ} {ξ Q : ℝ} {D : DistRd d → ContMetric d}
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistRd d}
    (hS : Setting d ξ Q κ D P h) (h41 : Prop41Stmt d) (hus : UnitSpeedAdmissible d)
    (h24c : Lemma24Conv κ ξ D P h) (h24f : Lemma24Confine κ ξ P h) {A C₀ β₀ : ℝ} (hA : 1 ≤ A)
    (hC₀ : 2 ≤ C₀) (hβ₀ : 0 < β₀) (h33 : p51H33 κ ξ Q D P h A) (h27 : p51H27 κ ξ D P h C₀ β₀)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) {N : ℕ} (hN : (A / (A + 1)) ^ N * C₀ < δ / 16) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ((Finset.Icc 1 (3 * N)).filter
      (fun i => winIsHigh (p51W ε i) (cRatio κ ξ Q ε) (winMPlus δ))).card < N := by
  have hθ0 : 0 < A / (A + 1) := div_pos (by linarith) (by linarith)
  have hθ1 : A / (A + 1) < 1 := (div_lt_one (by linarith)).2 (by linarith)
  have hη : 0 < winEta δ (A / (A + 1)) := winEta_pos hδ0 hθ1
  have hm0 : 0 < winMMinus δ := p51_winMMinus_pos hδ1
  have hmC : winMMinus δ ≤ C₀ := by
    unfold winMMinus winT
    linarith
  have hmp : 0 < winMPlus δ := winMPlus_pos hδ0 hδ1
  set lam : ℝ := (A / (A + 1)) ^ N * C₀ + winMMinus δ * (1 + δ / 10) with hlam
  have hlam1 : lam < 1 := p51_lambda_minus_lt_one hδ0 hδ1 hθ1 hN
  have hlam0 : 0 ≤ lam := by
    have h1 : 0 ≤ (A / (A + 1)) ^ N * C₀ := mul_nonneg (pow_nonneg hθ0.le N) (by linarith)
    have h2 : 0 ≤ winMMinus δ * (1 + δ / 10) := mul_nonneg hm0.le (by linarith)
    linarith
  have hF : IsCompact ({0, e₁ d} : Set (Rd d)) := (Set.toFinite _).isCompact
  obtain ⟨RF, _, hconf⟩ := h24f {0, e₁ d} hF (1 / 2) (by norm_num)
  have hRE : 2 ≤ max RF 2 := le_max_right _ _
  obtain ⟨K, hK⟩ := p51_failure h33 h27 hη (3 * N) (R := max RF 2) (by linarith)
  have hP41 := p51_P41_eventually (by linarith [hS.dim] : 1 ≤ d) h41 hA hη (3 * N)
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  obtain ⟨εs, hεs, hεsP⟩ := Filter.exists_seq_forall_of_frequently
    ((hcon.and_eventually ((hK.and hP41).and hconf)).and_eventually (Ioo_mem_nhdsGT one_pos))
  -- the data along the sequence
  have hεpos : ∀ k, 0 < εs k := fun k => (hεsP k).2.1
  have hεle : ∀ k, εs k ≤ 1 := fun k => (hεsP k).2.2.le
  have hεlt1 : ∀ k, εs k < 1 := fun k => (hεsP k).2.2
  have hεs0 : Tendsto εs atTop (𝓝 0) := (tendsto_nhdsWithin_iff.1 hεs).1
  let ρ : ℕ → ℝ := fun k => 8 * εs k ^ winV (3 * N)
  have hρ : Tendsto ρ atTop (𝓝 0) := by
    have h1 : Tendsto (fun k => εs k ^ winV (3 * N)) atTop (𝓝 ((0 : ℝ) ^ winV (3 * N))) :=
      ((Real.continuousAt_rpow_const 0 (winV (3 * N))
        (Or.inr (p51_winV_pos _).le)).tendsto).comp hεs0
    rw [Real.zero_rpow (p51_winV_pos _).ne'] at h1
    simpa using h1.const_mul 8
  have hρpos : ∀ k, 0 < ρ k := fun k => mul_pos (by norm_num) (Real.rpow_pos_of_pos (hεpos k) _)
  let Xlim : Ω → Rd d × Rd d → ℝ := fun ω => ⇑(D (h ω)).1
  have hXd := tendstoInProbLU_winShrinkInf P (fun _ => Xlim) Xlim
    (p51_tendstoInProbLU_const P Xlim) ρ hρ hρpos
    (fun p => p51_measurable_eval hS p) (fun ω => (D (h ω)).1.continuous) 0 (e₁ d)
  have hβ : 0 < min β₀ (winU (3 * N)) := lt_min hβ₀ (winU_pos _)
  have hKlim : Tendsto (fun k => ENNReal.ofReal (K * εs k ^ min β₀ (winU (3 * N)))) atTop
      (𝓝 0) := by
    have h1 : Tendsto (fun k => εs k ^ min β₀ (winU (3 * N))) atTop
        (𝓝 ((0 : ℝ) ^ min β₀ (winU (3 * N)))) :=
      ((Real.continuousAt_rpow_const 0 _ (Or.inr hβ.le)).tendsto).comp hεs0
    rw [Real.zero_rpow hβ.ne'] at h1
    simpa using ENNReal.tendsto_ofReal (h1.const_mul K)
  -- the high windows along the sequence and their high radii
  let S : ℕ → Finset ℕ := fun k => (Finset.Icc 1 (3 * N)).filter
    (fun i => winIsHigh (p51W (εs k) i) (cRatio κ ξ Q (εs k)) (winMPlus δ))
  let Rs : ℕ → ℕ → Finset ℝ := fun k b =>
    winHighRadii (p51W (εs k) b) (cRatio κ ξ Q (εs k)) (winMPlus δ)
  have hSmem : ∀ k, ∀ b ∈ S k, (1 ≤ b ∧ b ≤ 3 * N) ∧
      winIsHigh (p51W (εs k) b) (cRatio κ ξ Q (εs k)) (winMPlus δ) := by
    intro k b hb
    rw [Finset.mem_filter, Finset.mem_Icc] at hb
    exact hb
  have hScard : ∀ k, N ≤ (S k).card := fun k => not_lt.1 (hεsP k).1.1
  have hRsmem : ∀ k b r, r ∈ Rs k b →
      r ∈ p51W (εs k) b ∧ winMPlus δ ≤ cRatio κ ξ Q (εs k) r := fun k b r hr =>
    Finset.mem_filter.1 hr
  have hbad : ∀ k, P (p51Bad κ ξ Q D h A (winEta δ (A / (A + 1))) C₀ (max RF 2) (εs k) (S k)
      (Rs k)) ≤ ENNReal.ofReal (K * εs k ^ min β₀ (winU (3 * N))) := by
    intro k
    refine (hεsP k).1.2.1.1 (S k) (Rs k) ?_
    intro b hb
    obtain ⟨hbI, hhigh⟩ := hSmem k b hb
    refine ⟨hbI.2, fun r hr => p51_mem_W (hεpos k) (hεlt1 k) (hRsmem k b r hr).1, ?_⟩
    rw [p51_ncard_W (hεpos k) (hεlt1 k)]
    exact hhigh
  have hcomp : ∀ k, ∀ ω,
      ω ∉ p51Bad κ ξ Q D h A (winEta δ (A / (A + 1))) C₀ (max RF 2) (εs k) (S k) (Rs k) →
      Comp (Meps κ ξ (εs k) (h ω)) (D (h ω)) (max RF 2) (εs k) (winV (3 * N)) lam := by
    intro k ω hω
    obtain ⟨hinit, hcov⟩ := p51_not_bad hω
    have hc := p51_good_reverse hA hη hRE (hεpos k) (hεle k) hm0.le hmC (hεsP k).1.2.1.2 (S k)
      (fun b hb => (hSmem k b hb).1) (Rs k)
      (fun b _ r hr => ⟨p51_mem_W (hεpos k) (hεlt1 k) (hRsmem k b r hr).1,
        lt_of_lt_of_le hmp (hRsmem k b r hr).2,
        (p51_winMPlus_inv δ) ▸ inv_anti₀ hmp (hRsmem k b r hr).2⟩) hinit hcov
    exact p51_comp_mono_C
      (p51_winIter_le_of_ge hθ0 hθ1 (by linarith) hm0.le hδ0.le (hScard k)) hc
  -- the limit variable, the shrinking-ball `D`-distances and the `M_ε`-distances
  let X : Ω → ℝ := fun ω => (D (h ω)).1 (0, e₁ d)
  have hXmeas : Measurable X := p51_measurable_eval hS (0, e₁ d)
  have hd0 : 0 < d := by linarith [hS.dim]
  have hXpos : ∀ ω, 0 < X ω := fun ω =>
    (D (h ω)).apply_pos (HigherDimLFPP.e₁_ne_zero hd0).symm
  let Xd : ℕ → Ω → ℝ := fun k ω => winShrinkInf Xlim 0 (e₁ d) ρ k ω
  let Z : ℕ → Ω → ℝ := fun k ω => (Meps κ ξ (εs k) (h ω)).1 (0, e₁ d)
  have hZ : ∀ α : ℝ, 0 < α →
      Tendsto (fun k => P {ω | ENNReal.ofReal α ≤ edist (Z k ω) (X ω)}) atTop (𝓝 0) := by
    intro α hα
    have hR1 : (0 : ℝ) < ‖e₁ d‖ + 1 := by positivity
    have hmem : ((0 : Rd d), e₁ d) ∈
        closedBall (0 : Rd d) (‖e₁ d‖ + 1) ×ˢ closedBall (0 : Rd d) (‖e₁ d‖ + 1) := by
      refine ⟨mem_closedBall_self hR1.le, ?_⟩
      rw [mem_closedBall, dist_zero_right]
      linarith
    have hlim := (h24c (‖e₁ d‖ + 1) hR1 α hα).comp hεs
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ => zero_le) (fun k => measure_mono ?_)
    intro ω hω
    exact le_trans hω (le_iSup₂ (f := fun p (_ : p ∈
      closedBall (0 : Rd d) (‖e₁ d‖ + 1) ×ˢ closedBall (0 : Rd d) (‖e₁ d‖ + 1)) =>
        edist ((Meps κ ξ (εs k) (h ω)).1 p) ((D (h ω)).1 p)) _ hmem)
  have hstep : ∀ s : ℝ, 0 < s → ENNReal.ofReal (1 / 2) ≤ P {ω | X ω < s} := by
    intro s hs
    set α : ℝ := (1 - lam) * s / (1 + lam) with hα_def
    have hα : 0 < α := div_pos (mul_pos (by linarith) hs) (by linarith)
    have hαeq : (1 + lam) * α = (1 - lam) * s := by
      rw [hα_def]
      field_simp
    have hf : Tendsto (fun k => P {ω | ENNReal.ofReal α ≤ edist (Xd k ω) (X ω)} +
        P {ω | ENNReal.ofReal α ≤ edist (Z k ω) (X ω)}) atTop (𝓝 0) := by
      simpa using (hXd α hα).add (hZ α hα)
    refine p51_le_of_tendsto hf hKlim (fun k => ?_)
    refine (hεsP k).1.2.2.trans ((measure_mono (μ := P)
      (t := (({ω | ENNReal.ofReal α ≤ edist (Xd k ω) (X ω)} ∪
        {ω | ENNReal.ofReal α ≤ edist (Z k ω) (X ω)}) ∪ {ω | X ω < s}) ∪
        p51Bad κ ξ Q D h A (winEta δ (A / (A + 1))) C₀ (max RF 2) (εs k) (S k) (Rs k)) ?_).trans ?_)
    · intro ω hω
      obtain ⟨⟨γ, T, hT, h0, h1, hc, hunit⟩, hall⟩ :=
        hω 0 (Set.mem_insert _ _) (e₁ d) (Set.mem_insert_of_mem _ (Set.mem_singleton _))
      by_cases hb : ω ∈
          p51Bad κ ξ Q D h A (winEta δ (A / (A + 1))) C₀ (max RF 2) (εs k) (S k) (Rs k)
      · exact Or.inr hb
      · left
        have hgeo := p51_isGeodesicCurve_of_unit hus hT hc hunit
        have hmaps : MapsTo γ (Icc 0 T) (ball 0 (max RF 2)) := fun t ht =>
          ball_subset_ball (le_max_left _ _) (hall γ T h0 h1 hgeo ht)
        have hset := p51_comp_apply_unit hus (hcomp k ω hb) hT hc hmaps hunit
        rw [h0, h1] at hset
        have hTZ : T = Z k ω := by
          have h2 := hunit 0 ⟨le_rfl, hT⟩ T ⟨hT, le_rfl⟩
          rw [h0, h1, sub_zero, abs_of_nonneg hT] at h2
          exact h2.symm
        have hZnn : 0 ≤ Z k ω := (Meps κ ξ (εs k) (h ω)).nonneg _ _
        have hXdle : ENNReal.ofReal (Xd k ω) ≤ ENNReal.ofReal (lam * Z k ω) := by
          have h2 := p51_ofReal_inf_le_setDistIn (D (h ω)) 0 (e₁ d) (ρ k) (ball 0 (max RF 2 + 2))
          rw [ENNReal.ofReal_mul hlam0, ← hTZ]
          exact h2.trans hset
        have hXdle' : Xd k ω ≤ lam * Z k ω :=
          (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hlam0 hZnn)).1 hXdle
        by_cases h1' : ENNReal.ofReal α ≤ edist (Xd k ω) (X ω)
        · exact Or.inl (Or.inl h1')
        by_cases h2' : ENNReal.ofReal α ≤ edist (Z k ω) (X ω)
        · exact Or.inl (Or.inr h2')
        by_cases h3' : X ω < s
        · exact Or.inr h3'
        exfalso
        push Not at h1' h2' h3'
        rw [edist_dist, Real.dist_eq] at h1' h2'
        have e1 := abs_lt.1 ((ENNReal.ofReal_lt_ofReal_iff hα).1 h1')
        have e2 := abs_lt.1 ((ENNReal.ofReal_lt_ofReal_iff hα).1 h2')
        have hZup : lam * Z k ω ≤ lam * (X ω + α) :=
          mul_le_mul_of_nonneg_left (by linarith [e2.2]) hlam0
        have hkey : (1 - lam) * X ω < (1 - lam) * s := by
          nlinarith [e1.1, hXdle', hZup, hαeq]
        have hXs := lt_of_mul_lt_mul_left hkey (by linarith : (0 : ℝ) ≤ 1 - lam)
        linarith
    · calc P ((({ω | ENNReal.ofReal α ≤ edist (Xd k ω) (X ω)} ∪
            {ω | ENNReal.ofReal α ≤ edist (Z k ω) (X ω)}) ∪ {ω | X ω < s}) ∪
            p51Bad κ ξ Q D h A (winEta δ (A / (A + 1))) C₀ (max RF 2) (εs k) (S k) (Rs k))
          ≤ P {ω | ENNReal.ofReal α ≤ edist (Xd k ω) (X ω)} +
              P {ω | ENNReal.ofReal α ≤ edist (Z k ω) (X ω)} + P {ω | X ω < s} +
              P (p51Bad κ ξ Q D h A (winEta δ (A / (A + 1))) C₀ (max RF 2) (εs k) (S k)
                (Rs k)) :=
            (measure_union_le _ _).trans (add_le_add ((measure_union_le _ _).trans
              (add_le_add (measure_union_le _ _) le_rfl)) le_rfl)
        _ ≤ P {ω | ENNReal.ofReal α ≤ edist (Xd k ω) (X ω)} +
              P {ω | ENNReal.ofReal α ≤ edist (Z k ω) (X ω)} + P {ω | X ω < s} +
              ENNReal.ofReal (K * εs k ^ min β₀ (winU (3 * N))) := add_le_add le_rfl (hbad k)
  exact p51_contra P X hXmeas hXpos (by norm_num) hstep

end HigherDimLFPPAS.SharpComp
