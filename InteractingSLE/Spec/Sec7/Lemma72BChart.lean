/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma72BRec
import InteractingSLE.GFF.PushforwardMeas
import InteractingSLE.GFF.LocalSets.Characterization
import InteractingSLE.Spec.Sec7.Lemma71EDisc
import SupercriticalConformalCovariance.Reversal.Inverse

/-!
# Lemma 7.2, ingredient (i): the pocket field records the field inside the pocket

Packet PROVE-LEMMA72B. Specification §7.1 (`source/spec/p193-240.md` L626–L634, p. 226): "The outer curves determine
`C`, `ψ`, and its inherited argument branch. The pair `(Q, h_ψ)` determines `h` off `∂C`."

Inside the pocket, `h` is recorded by the pocket field `h_ψ = h ∘ ψ⁻¹ − χ arg (ψ⁻¹)′` (frozen `IsChartTransport`,
`σ = 1`) and the chart: a test `φ` supported in the chart domain is the push of the test
`invTest φ = |(ψ⁻¹)′|² (φ ∘ ψ⁻¹)` on `ℍ` (`pushTest_invTest`), so `h φ = h_ψ (invTest φ) − a ∫ invTest φ − k ∫ ℓ φ`
(`apply_eq_of_isChartTransport`). For a random chart measurable through its domain events, forward maps and lifts,
this is a measurable record:

* `invTest`, `pushTest_invTest`, `invTest_apply_of_mem`, `invTest_apply_of_notMem`;
* **`apply_eq_of_isChartTransport`**: the recovery identity;
* `measurable_inv_apply`, `measurable_deriv_inv_apply`: the inverse maps `ψ⁻¹(w)` and their derivatives are measurable
  in `ω` for each `w ∈ ℍ` (a measurable search along a dense sequence of the domain, then difference quotients);
* `measurableSet_subset_of_closedBall`, `measurableSet_disjoint_closure_of_mem`: for a compact `K`, the events
  `{K ⊆ C}` and `{K ∩ C̄ = ∅}` of a random open set with measurable closed-ball events;
* **`exists_record_in`**: the one-sided record of `h φ` on `{supp φ ⊆ C}` by `h_ψ` and the chart, for every test `φ`
  (the hypothesis `hin` of `Lemma72B.exists_version_of_recorded_sides`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped ENNReal

namespace InteractingSLE.Sec7.Lemma72B

open QuantumZipper (H isOpen_H)
open LQGMetric (DistOn TestOn)
open SupercriticalConformalCovariance (confPushTest IsConformalBijection)
open SupercriticalConformalCovariance.Reversal (inverse_conformal confPushTest_inverse_right
  confPushTest_inverse_eq_confPullFun)
open Chart

/-! ### The inverse transport of a test function supported in the chart domain -/

section Inv

variable {c : Chart}

/-- **The inverse transport** of a test `φ` supported in the chart domain: the test `|(ψ⁻¹)′|² (φ ∘ ψ⁻¹)` on `ℍ`
(`ψ⁻¹ = c.2.1`), SupercriticalConformalCovariance's `confPushTest` along the inverse bijection `dom → ℍ`. -/
def invTest (hc : c.IsConformal) (φ : TestOn upperHalfPlaneOpens) (hφ : tsupport φ ⊆ c.dom) :
    TestOn upperHalfPlaneOpens :=
  confPushTest (inverse_conformal hc.isConformalBijection) (LocalSets.testOnOfSubset φ hφ)

/-- The inverse transport is a right inverse of `pushTest`. -/
theorem pushTest_invTest (hc : c.IsConformal) (φ : TestOn upperHalfPlaneOpens) (hφ : tsupport φ ⊆ c.dom) :
    pushTest hc (invTest hc φ hφ) = φ := by
  change GFF.testIncl c.dom upperHalfPlaneOpens (confPushTest hc.isConformalBijection
    (confPushTest (inverse_conformal hc.isConformalBijection) (LocalSets.testOnOfSubset φ hφ))) = φ
  rw [confPushTest_inverse_right]
  exact LocalSets.testIncl_testOnOfSubset hc.dom_le φ hφ

theorem coe_invTest (hc : c.IsConformal) (φ : TestOn upperHalfPlaneOpens) (hφ : tsupport φ ⊆ c.dom) :
    ⇑(invTest hc φ hφ) = SmallGammaGeodesics.CC.confPullFun c.2.1 H φ :=
  confPushTest_inverse_eq_confPullFun hc.isConformalBijection (LocalSets.testOnOfSubset φ hφ)

theorem invTest_apply_of_mem (hc : c.IsConformal) (φ : TestOn upperHalfPlaneOpens) (hφ : tsupport φ ⊆ c.dom)
    {w : ℂ} (hw : w ∈ H) : invTest hc φ hφ w = ‖deriv c.2.1 w‖ ^ 2 * φ (c.2.1 w) := by
  rw [coe_invTest]
  exact SmallGammaGeodesics.CC.confPullFun_of_mem hw

theorem invTest_apply_of_notMem (hc : c.IsConformal) (φ : TestOn upperHalfPlaneOpens) (hφ : tsupport φ ⊆ c.dom)
    {w : ℂ} (hw : w ∉ H) : invTest hc φ hφ w = 0 := by
  rw [coe_invTest]
  exact SmallGammaGeodesics.CC.confPullFun_of_notMem hw

/-- **Recovery of `h` inside the chart domain from the transported field** (frozen `IsChartTransport` with `σ = 1`):
for a test `φ` supported in the domain, `h φ = h' (invTest φ) − a ∫ invTest φ − k ∫ ℓ φ`. -/
theorem apply_eq_of_isChartTransport (hc : c.IsConformal) (hℓ : ContinuousOn c.2.2 c.dom) {a k : ℝ}
    {h h' : DistOn upperHalfPlaneOpens} (ht : IsChartTransport c 1 a k h h') (φ : TestOn upperHalfPlaneOpens)
    (hφ : tsupport φ ⊆ c.dom) :
    h φ = h' (invTest hc φ hφ) - a * (∫ w, invTest hc φ hφ w) - k * ∫ z, c.2.2 z * φ z := by
  have he := ht.eq_chartTransport hc (locallyIntegrableOn_of_continuousOn (hc.continuousOn_lift_inv hℓ))
  rw [he, chartTransport_apply', pushTest_invTest, oneDist_apply, liftDist_eq_integral_pushTest hc hℓ,
    pushTest_invTest]
  ring

end Inv

/-! ### Measurability of a random chart's inverse maps -/

section RandomInv

variable {Ω : Type*} [MeasurableSpace Ω] {c : Ω → Chart}

/-- **The inverse maps of a random chart are measurable** at every point of `ℍ`, when the domain events and the masked
forward maps are: `ψ⁻¹(w)` is the limit of the first points `e_n` of a dense sequence in the domain with
`|ψ(e_n) − w| < 1/(m+1)`, each a measurable search. -/
theorem measurable_inv_apply (hc : ∀ ω, (c ω).IsConformal) (hdom : ∀ z, MeasurableSet {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z)) {w : ℂ} (hw : w ∈ H) :
    Measurable fun ω => (c ω).2.1 w := by
  classical
  obtain ⟨e, he⟩ := TopologicalSpace.exists_dense_seq ℂ
  set p : Ω → ℕ → ℕ → Prop := fun ω m n =>
    e n ∈ (c ω).dom ∧ dist ((c ω).1 (e n)) w < 1 / ((m : ℝ) + 1) with hp
  have hex : ∀ m ω, ∃ n, p ω m n := by
    intro m ω
    have hcont : ContinuousOn (c ω).1 (c ω).dom := (hc ω).differentiableOn_fwd.continuousOn
    have hopen : IsOpen (((c ω).dom : Set ℂ) ∩ (c ω).1 ⁻¹' ball w (1 / ((m : ℝ) + 1))) :=
      hcont.isOpen_inter_preimage (c ω).dom.isOpen isOpen_ball
    have hne : (((c ω).dom : Set ℂ) ∩ (c ω).1 ⁻¹' ball w (1 / ((m : ℝ) + 1))).Nonempty := by
      refine ⟨(c ω).2.1 w, (hc ω).inv_mem_dom hw, ?_⟩
      rw [mem_preimage, (hc ω).2.2 w hw]
      exact mem_ball_self (by positivity)
    obtain ⟨n, hn⟩ := he.exists_mem_open hopen hne
    exact ⟨n, hn.1, hn.2⟩
  have hpm : ∀ m n, MeasurableSet {ω | p ω m n} := by
    intro m n
    have e1 : {ω | p ω m n} = {ω | e n ∈ (c ω).dom} ∩
        {ω | dist ({ω | e n ∈ (c ω).dom}.indicator (fun ω => (c ω).1 (e n)) ω) w < 1 / ((m : ℝ) + 1)} := by
      ext ω
      simp only [hp, mem_ofPred_eq, mem_inter_iff]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by rwa [indicator_of_mem (show ω ∈ {ω | e n ∈ (c ω).dom} from h1)]⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by rwa [indicator_of_mem (show ω ∈ {ω | e n ∈ (c ω).dom} from h1)] at h2⟩
    rw [e1]
    exact (hdom (e n)).inter (measurableSet_lt ((hfwd (e n)).dist measurable_const) measurable_const)
  set N : ℕ → Ω → ℕ := fun m ω => Nat.find (hex m ω) with hN
  have hNm : ∀ m, Measurable (N m) := fun m => measurable_find (hex m) (hpm m)
  have hlim : ∀ ω, Tendsto (fun m => e (N m ω)) atTop (𝓝 ((c ω).2.1 w)) := by
    intro ω
    have hspec : ∀ m, p ω m (N m ω) := fun m => Nat.find_spec (hex m ω)
    have hfw : Tendsto (fun m => (c ω).1 (e (N m ω))) atTop (𝓝 w) := by
      refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg) (fun m => (hspec m).2.le)
        tendsto_one_div_add_atTop_nhds_zero_nat)
    have hinv : ContinuousAt (c ω).2.1 w := ((hc ω).1 w hw).differentiableAt (isOpen_H.mem_nhds hw)
      |>.continuousAt
    have h2 := hinv.tendsto.comp hfw
    refine h2.congr fun m => ?_
    exact (hc ω).inv_fwd (hspec m).1
  refine measurable_of_tendsto_metrizable (f := fun m ω => e (N m ω)) (fun m => ?_) (tendsto_pi_nhds.2 hlim)
  exact (measurable_from_nat (f := e)).comp (hNm m)

/-- **The derivatives of the inverse maps are measurable** at every point of `ℍ` (limits of difference quotients). -/
theorem measurable_deriv_inv_apply (hc : ∀ ω, (c ω).IsConformal) (hdom : ∀ z, MeasurableSet {ω | z ∈ (c ω).dom})
    (hfwd : ∀ z, Measurable ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z)) {w : ℂ} (hw : w ∈ H) :
    Measurable fun ω => deriv (c ω).2.1 w := by
  set t : ℕ → ℂ := fun n => (((n : ℂ) + 1))⁻¹ with ht
  have hwt : ∀ n, w + t n ∈ H := fun n => by
    change 0 < (w + t n).im
    have : (t n).im = 0 := by
      simp only [ht, Complex.inv_im, Complex.add_im, Complex.natCast_im, Complex.one_im, add_zero, neg_zero,
        zero_div]
    rw [Complex.add_im, this, add_zero]
    exact hw
  have ht0 : Tendsto t atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
    · have h1 : Tendsto (fun n : ℕ => ((n : ℂ) + 1)) atTop (Bornology.cobounded ℂ) := by
        refine tendsto_norm_atTop_iff_cobounded.1 ?_
        refine tendsto_atTop_mono (fun n => ?_) (tendsto_natCast_atTop_atTop (R := ℝ))
        have : ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
        rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
        linarith
      exact tendsto_inv₀_cobounded.comp h1
    · simp only [ht, mem_compl_iff, mem_singleton_iff, inv_eq_zero]
      exact_mod_cast Nat.succ_ne_zero n
  have hlim : ∀ ω, Tendsto (fun n => (t n)⁻¹ • ((c ω).2.1 (w + t n) - (c ω).2.1 w)) atTop
      (𝓝 (deriv (c ω).2.1 w)) := fun ω =>
    ((((hc ω).1 w hw).differentiableAt (isOpen_H.mem_nhds hw)).hasDerivAt.tendsto_slope_zero).comp ht0
  refine measurable_of_tendsto_metrizable (fun n => ?_) (tendsto_pi_nhds.2 hlim)
  exact Measurable.const_smul ((measurable_inv_apply hc hdom hfwd (hwt n)).sub
    (measurable_inv_apply hc hdom hfwd hw)) ((t n)⁻¹ : ℂ)

end RandomInv

/-! ### Events of a random open set at a compact set -/

section Events

variable {Ω : Type*} [MeasurableSpace Ω] {C : Ω → Set ℂ}

/-- **`{K ⊆ C}` is measurable** for a compact `K` and a random open set `C` with measurable closed-ball events:
`K ⊆ C` iff for some `m` every point of a countable dense subset of `K` has its closed `1/(m+1)`-ball in `C`. -/
theorem measurableSet_subset_of_closedBall (hCo : ∀ ω, IsOpen (C ω))
    (hCm : ∀ (z : ℂ) (r : ℝ), MeasurableSet {ω | closedBall z r ⊆ C ω}) {K : Set ℂ} (hK : IsCompact K) :
    MeasurableSet {ω | K ⊆ C ω} := by
  obtain ⟨D, hDK, hDc, hKD⟩ := hK.isSeparable.exists_countable_dense_subset
  have e : {ω | K ⊆ C ω} = ⋃ m : ℕ, ⋂ x ∈ D, {ω | closedBall x (1 / ((m : ℝ) + 1)) ⊆ C ω} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, mem_iInter]
    constructor
    · intro hKC
      obtain ⟨δ, hδ, hδC⟩ := hK.exists_thickening_subset_open (hCo ω) hKC
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
      refine ⟨m, fun x hx y hy => hδC ?_⟩
      rw [mem_thickening_iff]
      exact ⟨x, hDK hx, lt_of_le_of_lt (mem_closedBall.1 hy) hm⟩
    · rintro ⟨m, hm⟩ y hy
      have hpos : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
      obtain ⟨x, hx, hxy⟩ := Metric.mem_closure_iff.1 (hKD hy) _ hpos
      exact hm x hx (mem_closedBall.2 hxy.le)
  rw [e]
  exact MeasurableSet.iUnion fun m => MeasurableSet.biInter hDc fun x _ => hCm x _

/-- **`{K ∩ C̄ = ∅}` is measurable** for a compact `K` and a random open set `C` with measurable membership events:
for `K ≠ ∅`, `K ∩ C̄ = ∅` iff for some `m` every point of a dense sequence lying in `C` is at distance at least
`1/(m+1)` from `K`. -/
theorem measurableSet_disjoint_closure_of_mem (hCo : ∀ ω, IsOpen (C ω))
    (hmem : ∀ z, MeasurableSet {ω | z ∈ C ω}) {K : Set ℂ} (hK : IsCompact K) :
    MeasurableSet {ω | Disjoint K (closure (C ω))} := by
  classical
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · simp only [empty_disjoint, ofPred_true, MeasurableSet.univ]
  obtain ⟨e, he⟩ := TopologicalSpace.exists_dense_seq ℂ
  have eq : {ω | Disjoint K (closure (C ω))} =
      ⋃ m : ℕ, ⋂ n : ℕ, ({ω | e n ∈ C ω}ᶜ ∪ {_ω | 1 / ((m : ℝ) + 1) ≤ infDist (e n) K}) := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, mem_iInter, mem_union, mem_compl_iff]
    constructor
    · intro hd
      have hsub : K ⊆ (closure (C ω))ᶜ := fun x hx hxc => hd.ne_of_mem hx hxc rfl
      obtain ⟨δ, hδ, hδC⟩ := hK.exists_thickening_subset_open isClosed_closure.isOpen_compl hsub
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
      refine ⟨m, fun n => ?_⟩
      by_cases hn : e n ∈ C ω
      · right
        by_contra hlt
        push Not at hlt
        have hmemth : e n ∈ thickening δ K := by
          rw [mem_thickening_iff_infDist_lt hKne]
          linarith
        exact hδC hmemth (subset_closure hn)
      · exact Or.inl hn
    · rintro ⟨m, hm⟩
      refine Set.disjoint_left.2 fun x hx hxc => ?_
      have hpos : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
      obtain ⟨y, hyC, hxy⟩ := Metric.mem_closure_iff.1 hxc _ hpos
      have hopen : IsOpen (C ω ∩ ball x (1 / ((m : ℝ) + 1))) := (hCo ω).inter isOpen_ball
      obtain ⟨n, hn⟩ := he.exists_mem_open hopen ⟨y, hyC, by rw [mem_ball, dist_comm]; exact hxy⟩
      rcases hm n with h1 | h2
      · exact h1 hn.1
      · have h3 : infDist (e n) K ≤ dist (e n) x := infDist_le_dist_of_mem hx
        have h4 : dist (e n) x < 1 / ((m : ℝ) + 1) := hn.2
        linarith
  rw [eq]
  exact MeasurableSet.iUnion fun m => MeasurableSet.iInter fun n =>
    (hmem (e n)).compl.union (MeasurableSet.const _)

end Events

/-! ### The record inside the pocket -/

section Record

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {c : Ω → Chart}

/-- The inverse transport of `φ` on the event `{supp φ ⊆ dom}`, `0` off it. -/
def rInvTest (hc : ∀ ω, (c ω).IsConformal) (φ : TestOn upperHalfPlaneOpens) (ω : Ω) : TestOn upperHalfPlaneOpens :=
  open Classical in
  if hS : tsupport φ ⊆ (c ω).dom then invTest (hc ω) φ hS else 0

/-- **The record of `h` inside the pocket** (the hypothesis `hin` of `exists_version_of_recorded_sides`). For a random
conformal chart with measurable closed-ball events of its domain, measurable masked forward maps and lifts and lifts
continuous on the domain, all for a `σ`-algebra `𝓡`, and a transported field `h'` (`IsChartTransport (c ω) 1 a k (h ω)
(h' ω)` for every `ω`) that is `𝓡`-measurable, `h φ` is an `𝓡`-measurable variable on the `𝓡`-event
`{supp φ ⊆ dom}`. -/
theorem exists_record_in {𝓡 : MeasurableSpace Ω} (hc : ∀ ω, (c ω).IsConformal)
    (hCm : ∀ (z : ℂ) (r : ℝ), MeasurableSet[𝓡] {ω | closedBall z r ⊆ (c ω).dom})
    (hfwd : ∀ z, Measurable[𝓡] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).1 z))
    (hliftm : ∀ z, Measurable[𝓡] ({ω | z ∈ (c ω).dom}.indicator fun ω => (c ω).2.2 z))
    (hliftc : ∀ ω, ContinuousOn (c ω).2.2 (c ω).dom) {a k : ℝ} {h h' : Ω → DistOn upperHalfPlaneOpens}
    (hh' : Measurable[𝓡] h') (ht : ∀ ω, IsChartTransport (c ω) 1 a k (h ω) (h' ω))
    (φ : TestOn upperHalfPlaneOpens) :
    ∃ (S : Set Ω) (g : Ω → ℝ), MeasurableSet[𝓡] S ∧ StronglyMeasurable[𝓡] g ∧
      (∀ᵐ ω ∂P, tsupport φ ⊆ (c ω).dom → ω ∈ S) ∧ ∀ᵐ ω ∂P, ω ∈ S → h ω φ = g ω := by
  classical
  let _ : MeasurableSpace Ω := 𝓡
  have hCo : ∀ ω, IsOpen ((c ω).dom : Set ℂ) := fun ω => (c ω).dom.isOpen
  have hdom : ∀ z, MeasurableSet {ω | z ∈ (c ω).dom} :=
    Lemma71E.measurableSet_mem_of_closedBall (C := fun ω => ((c ω).dom : Set ℂ)) hCo hCm
  set S : Set Ω := {ω | tsupport φ ⊆ (c ω).dom} with hSdef
  have hSm : MeasurableSet S :=
    measurableSet_subset_of_closedBall (C := fun ω => ((c ω).dom : Set ℂ)) hCo hCm φ.hasCompactSupport
  set T : Ω → TestOn upperHalfPlaneOpens := rInvTest hc φ with hTdef
  have hTS : ∀ ω (hω : ω ∈ S), T ω = invTest (hc ω) φ hω := fun ω hω => by
    simp only [hTdef, rInvTest, show tsupport φ ⊆ (c ω).dom from hω, ↓reduceDIte]
  have hTn : ∀ ω, ω ∉ S → T ω = 0 := fun ω hω => by
    simp only [hTdef, rInvTest, show ¬ tsupport φ ⊆ (c ω).dom from hω, ↓reduceDIte]
  -- the inverse transport is pointwise measurable
  have hTm : ∀ w, Measurable fun ω => T ω w := by
    intro w
    by_cases hw : w ∈ H
    · have e : (fun ω => T ω w) = S.indicator fun ω => ‖deriv (c ω).2.1 w‖ ^ 2 * φ ((c ω).2.1 w) := by
        funext ω
        by_cases hω : ω ∈ S
        · rw [indicator_of_mem hω, hTS ω hω, invTest_apply_of_mem (hc ω) φ hω hw]
        · rw [indicator_of_notMem hω, hTn ω hω]
          rfl
      rw [e]
      refine Measurable.indicator ?_ hSm
      exact ((measurable_deriv_inv_apply hc hdom hfwd hw).norm.pow_const 2).mul
        (φ.continuous.measurable.comp (measurable_inv_apply hc hdom hfwd hw))
    · have e : (fun ω => T ω w) = fun _ => 0 := by
        funext ω
        by_cases hω : ω ∈ S
        · rw [hTS ω hω, invTest_apply_of_notMem (hc ω) φ hω hw]
        · rw [hTn ω hω]
          rfl
      rw [e]
      exact measurable_const
  -- the three terms of the record
  have h1 : Measurable fun ω => h' ω (T ω) := RandomTest.measurable_apply_of_forall_measurable hh' hTm
  have h2 : Measurable fun ω => ∫ w, T ω w := by
    have hu : Measurable (Function.uncurry fun (w : ℂ) (ω : Ω) => T ω w) :=
      measurable_uncurry_of_continuous_of_measurable (fun ω => (T ω).continuous) hTm
    exact (hu.stronglyMeasurable.integral_prod_left (μ := volume)).measurable
  set G : ℂ → Ω → ℝ := fun z ω => S.indicator (fun ω => (c ω).2.2 z * φ z) ω with hGdef
  have h3 : Measurable fun ω => ∫ z, G z ω := by
    have hGc : ∀ ω, Continuous fun z => G z ω := by
      intro ω
      by_cases hω : ω ∈ S
      · have e : (fun z => G z ω) = fun z => (c ω).2.2 z * pushTest (hc ω) (invTest (hc ω) φ hω) z := by
          funext z
          change S.indicator (fun ω => (c ω).2.2 z * φ z) ω = _
          rw [indicator_of_mem hω, pushTest_invTest]
        rw [e]
        exact continuous_lift_mul_pushTest (hc ω) (hliftc ω) _
      · have e : (fun z => G z ω) = fun _ => 0 := by
          funext z
          change S.indicator (fun ω => (c ω).2.2 z * φ z) ω = _
          rw [indicator_of_notMem hω]
        rw [e]
        exact continuous_const
    have hGm : ∀ z, Measurable (G z) := by
      intro z
      have e : G z = S.indicator fun ω => ({ω | z ∈ (c ω).dom}.indicator (fun ω => (c ω).2.2 z) ω) * φ z := by
        funext ω
        change S.indicator (fun ω => (c ω).2.2 z * φ z) ω = _
        by_cases hω : ω ∈ S
        · rw [indicator_of_mem hω, indicator_of_mem hω]
          by_cases hφz : φ z = 0
          · rw [hφz, mul_zero, mul_zero]
          · have hz : z ∈ (c ω).dom := hω (subset_tsupport _ hφz)
            rw [indicator_of_mem (show ω ∈ {ω | z ∈ (c ω).dom} from hz)]
        · rw [indicator_of_notMem hω, indicator_of_notMem hω]
      rw [e]
      exact ((hliftm z).mul_const _).indicator hSm
    have hu : Measurable (Function.uncurry G) := measurable_uncurry_of_continuous_of_measurable hGc hGm
    exact (hu.stronglyMeasurable.integral_prod_left (μ := volume)).measurable
  refine ⟨S, S.indicator fun ω => h' ω (T ω) - a * (∫ w, T ω w) - k * ∫ z, G z ω, hSm,
    (((h1.sub (h2.const_mul a)).sub (h3.const_mul k)).indicator hSm).stronglyMeasurable,
    Eventually.of_forall fun ω hω => hω, Eventually.of_forall fun ω hω => ?_⟩
  rw [indicator_of_mem hω, apply_eq_of_isChartTransport (hc ω) (hliftc ω) (ht ω) φ hω, hTS ω hω]
  congr 2
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [hGdef, indicator_of_mem hω]

end Record

end InteractingSLE.Sec7.Lemma72B
