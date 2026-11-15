/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RetZoneChart

/-!
# Proposition 3.8 in a chart (Aux. lemma 82's boundary-decay step)

Packet PROVE-T15-RET6. Specification supplement, Aux. lemma 82 (pp. 296–297): "Under `g_A` this is the same
statement for a zero-boundary field in `ℍ` … Every compact `J ⊂ I^R_A` has a collar of positive distance from the
closed additional range, by (OM2). The relative local-set boundary-decay argument in Proposition 3.8 consequently gives
continuous zero boundary values on `J`. The assertion is simultaneous: given `A`, take the probability-one boundary
statement for all rational compact subintervals and collars in this fixed half-plane chart".

**Main result (`ae_tendsto_zero_of_chart`).** Let `X(ψ) = h(ψ)` be conditionally Gaussian given `𝒢 ≤ 𝒥`, with
means `g₂(ψ)`, `g(ψ)` and variances `σ²_{ℍ∖A₂}(ψ)`, `σ²_{ℍ∖A}(ψ)` (`A₂ ⊆ A` relatively closed in `ℍ`; e.g. two nested
history-marked local sets, `Sec7.FlatClockProof.isCondGaussian_of_cover`), with `g`, `g₂` harmonic off `A`, `A₂`. Let
`D(ω)` be a union of components of `ℍ ∖ A₂(ω)` with a conformal chart `G(ω) : D(ω) → ℍ` of bounded displacement,
`𝒢`-measurable at fixed points. Then almost surely the harmonic representative `u` of `g − g₂` on `ℍ ∖ A` satisfies:
for every real `y` and `ρ > 0` such that no point of `A` in `D` has chart value in `B(y, ρ)` (the prime-end clearance
(OM2) of the added set), `u → 0` along every filter on `D` along which `G → y`.

**Proof.** Proposition 3.8's proof (`LocalSets.IsLocalSetMean.ae_tendsto_sub_of_union`) with chart patches in place of
Euclidean balls:
* the patch events (`clEv`, `refEv`) and the layer sets (`Lset`) are described by countably many verifiable chart
  balls (`RetZone.IsVerBall`), hence measurable (`measurableSet_verEv`, …);
* on a layer point `y`, the conformal disc of `D` at `y` lies in the chart patch, by the Beurling-type bound
  `Im G(y) ≲ dist(y, ∂D)^{1/C₂}` against a fixed reference point (`RetZone.im_le_of_ref`), so the variance gap is
  `≤ 4 τ_n (∫ψ)²` (`RetZone.zeroGFFTestCov_sub_le_of_chart`, `gap_of_patch`);
* the moment bound (`RetZone.lintegral_indicator_exp_mean_sub_le`) and Borel–Cantelli (`ae_eventually_abs_lt_of_sets`)
  give uniform smallness on the layers of every patch (`ae_patch`);
* along the filter, the points are bounded (displacement), approach `∂D` (compactness: `Im G` is bounded below on
  compact subsets of `D`), and their Whitney balls lie in the layer sets of a patch (chart oscillation
  `RetZone.IsChartSetting.norm_sub_lt`).

No Theorem 1.2/1.3 (R48).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric Complex
open scoped ENNReal ComplexConjugate

open QuantumZipper (H zeroGFFTestCov)
open SupercriticalConformalCovariance (IsConformalBijection)
open QuantumZipper.CA.Koebe (koebeCovConst koebeDistExp koebeCovConst_pos koebeDistExp_pos)
open LQGMetric (DistOn TestOn)
open InteractingSLE.LocalSets (relClosureH compDist tauHi tauLo bumpRad bumpTestH bumpPair)

namespace InteractingSLE

namespace RLC

namespace RetZone

open Sec6.Prop65

/-! ### The patch events -/

section Events

variable {Ω : Type*}

/-- The chart value at a fixed point `q`, as an indicator of `{q ∈ D}`. -/
def chartInd (D : Ω → Set ℂ) (G : Ω → ℂ → ℂ) (ω : Ω) (q : ℂ) : ℂ :=
  {ω' | q ∈ D ω'}.indicator (fun ω' => G ω' q) ω

theorem chartInd_of_mem {D : Ω → Set ℂ} {G : Ω → ℂ → ℂ} {ω : Ω} {q : ℂ} (hq : q ∈ D ω) :
    chartInd D G ω q = G ω q :=
  indicator_of_mem (show ω ∈ {ω' | q ∈ D ω'} from hq) _

/-- The event that `B(q_i, 1/(j+1))` is a verifiable chart ball for `K`. -/
def verEv (D A₂ : Ω → Set ℂ) (G : Ω → ℂ → ℂ) (K : Set ℂ) (i j : ℕ) : Set Ω :=
  {ω | IsVerBall (D ω) (H \ relClosureH (A₂ ω)) (chartInd D G ω) K i j}

/-- The random chart region: the union of the verifiable chart balls for `K`. -/
def regSet (D A₂ : Ω → Set ℂ) (G : Ω → ℂ → ℂ) (K : Set ℂ) : Set (Ω × ℂ) :=
  ⋃ i, ⋃ j, verEv D A₂ G K i j ×ˢ ball (qpt i) (qrad j)

/-- The clearance event: every verifiable chart ball for `K` misses `A`. -/
def clEv (D A₂ A : Ω → Set ℂ) (G : Ω → ℂ → ℂ) (K : Set ℂ) : Set Ω :=
  {ω | ∀ i j, ω ∈ verEv D A₂ G K i j → qrad j ≤ compDist (A ω) (qpt i)}

/-- The reference event: `q_{i₀} ∈ D` at distance `≥ 1/(k+1)` from `∂(ℍ ∖ A₂)`, with chart value of height
`≥ 1/(k+1)` and norm `≤ k`. -/
def refEv (D A₂ : Ω → Set ℂ) (G : Ω → ℂ → ℂ) (i₀ k : ℕ) : Set Ω :=
  {ω | qpt i₀ ∈ D ω ∧ qrad k ≤ compDist (A₂ ω) (qpt i₀) ∧ qrad k ≤ (chartInd D G ω (qpt i₀)).im ∧
    ‖chartInd D G ω (qpt i₀)‖ ≤ k}

/-- The layer sets of a patch: the clearance and reference events, the Euclidean dyadic layers of `ℍ ∖ A₂` in
`B(0, 3Rp)`, and the chart region for `B̄(c, 2R)`. -/
def Lset (D A₂ A : Ω → Set ℂ) (G : Ω → ℂ → ℂ) (c R : ℝ) (i₀ k Rp n : ℕ) : Set (Ω × ℂ) :=
  {p | p.1 ∈ clEv D A₂ A G (closedBall (c : ℂ) (4 * R)) ∩ refEv D A₂ G i₀ k ∧
    p.2 ∈ GFF.layerSet (H \ relClosureH (A₂ p.1)) 0 Rp n ∧ p ∈ regSet D A₂ G (closedBall (c : ℂ) (2 * R))}

variable {𝒢 : MeasurableSpace Ω} {D A₂ : Ω → Set ℂ} {G : Ω → ℂ → ℂ}

theorem measurable_compDist_of_le {S : Ω → Set ℂ} (hS : MeasurableSpace.comap S hittingSigma ≤ 𝒢) (q : ℂ) :
    Measurable[𝒢] fun ω => compDist (S ω) q :=
  (@LocalSets.measurable_compDist_left Ω (MeasurableSpace.comap S hittingSigma) S (comap_measurable S) q).mono
    hS le_rfl

theorem measurableSet_verEv (hA₂ : MeasurableSpace.comap A₂ hittingSigma ≤ 𝒢)
    (hDm : ∀ q, MeasurableSet[𝒢] {ω | q ∈ D ω}) (hGm : ∀ q, Measurable[𝒢] fun ω => chartInd D G ω q)
    {K : Set ℂ} (hK : MeasurableSet K) (i j : ℕ) : MeasurableSet[𝒢] (verEv D A₂ G K i j) := by
  have e : verEv D A₂ G K i j = {ω | qpt i ∈ D ω} ∩ {ω | qrad j ≤ compDist (A₂ ω) (qpt i)} ∩
      ⋂ i' : ℕ, {ω | qpt i' ∈ ball (qpt i) (qrad j) → chartInd D G ω (qpt i') ∈ K} := by
    ext ω
    simp only [verEv, IsVerBall, compDist, mem_ofPred_eq, mem_inter_iff, mem_iInter, and_assoc]
  rw [e]
  refine ((hDm _).inter (measurableSet_le measurable_const (measurable_compDist_of_le hA₂ _))).inter
    (MeasurableSet.iInter fun i' => ?_)
  by_cases hb : qpt i' ∈ ball (qpt i) (qrad j)
  · simp only [hb, true_implies]
    exact hGm _ hK
  · simp only [hb, false_implies, ofPred_true, MeasurableSet.univ]

theorem measurableSet_regSet [mΩ : MeasurableSpace Ω] (h𝒢 : 𝒢 ≤ mΩ)
    (hA₂ : MeasurableSpace.comap A₂ hittingSigma ≤ 𝒢)
    (hDm : ∀ q, MeasurableSet[𝒢] {ω | q ∈ D ω}) (hGm : ∀ q, Measurable[𝒢] fun ω => chartInd D G ω q)
    {K : Set ℂ} (hK : MeasurableSet K) : MeasurableSet (regSet D A₂ G K) :=
  MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun j =>
    (h𝒢 _ (measurableSet_verEv hA₂ hDm hGm hK i j)).prod measurableSet_ball

theorem measurableSet_clEv {𝒥 : MeasurableSpace Ω} (h𝒢𝒥 : 𝒢 ≤ 𝒥) {A : Ω → Set ℂ}
    (hA : MeasurableSpace.comap A hittingSigma ≤ 𝒥) (hA₂ : MeasurableSpace.comap A₂ hittingSigma ≤ 𝒢)
    (hDm : ∀ q, MeasurableSet[𝒢] {ω | q ∈ D ω}) (hGm : ∀ q, Measurable[𝒢] fun ω => chartInd D G ω q)
    {K : Set ℂ} (hK : MeasurableSet K) : MeasurableSet[𝒥] (clEv D A₂ A G K) := by
  have e : clEv D A₂ A G K = ⋂ i : ℕ, ⋂ j : ℕ,
      ((verEv D A₂ G K i j)ᶜ ∪ {ω | qrad j ≤ compDist (A ω) (qpt i)}) := by
    ext ω
    simp only [clEv, mem_ofPred_eq, mem_iInter, mem_union, mem_compl_iff]
    exact forall_congr' fun i => forall_congr' fun j => imp_iff_not_or
  rw [e]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
    (h𝒢𝒥 _ (measurableSet_verEv hA₂ hDm hGm hK i j)).compl.union
      (measurableSet_le measurable_const (measurable_compDist_of_le hA _))

theorem measurableSet_refEv (hA₂ : MeasurableSpace.comap A₂ hittingSigma ≤ 𝒢)
    (hDm : ∀ q, MeasurableSet[𝒢] {ω | q ∈ D ω}) (hGm : ∀ q, Measurable[𝒢] fun ω => chartInd D G ω q)
    (i₀ k : ℕ) : MeasurableSet[𝒢] (refEv D A₂ G i₀ k) := by
  have e : refEv D A₂ G i₀ k = {ω | qpt i₀ ∈ D ω} ∩ {ω | qrad k ≤ compDist (A₂ ω) (qpt i₀)} ∩
      {ω | qrad k ≤ (chartInd D G ω (qpt i₀)).im} ∩ {ω | ‖chartInd D G ω (qpt i₀)‖ ≤ k} := by
    ext ω
    simp only [refEv, mem_ofPred_eq, mem_inter_iff, and_assoc]
  rw [e]
  exact (((hDm _).inter (measurableSet_le measurable_const (measurable_compDist_of_le hA₂ _))).inter
    (measurableSet_le measurable_const (Complex.measurable_im.comp (hGm _)))).inter
      (measurableSet_le (continuous_norm.measurable.comp (hGm _)) measurable_const)

end Events

/-! ### Pathwise facts on a patch -/

section Pathwise

variable {S A D : Set ℂ} {G Gi : ℂ → ℂ}

/-- **The clearance event gives clearance**: no point of `A` in `D` has chart value in `B(c, R)`. -/
theorem notMem_of_clear (hc : IsChartSetting D (H \ S) G) (hGi : ∀ z ∈ D, Gi z = G z) (hA : A ⊆ H)
    {c : ℂ} {R : ℝ} (hcl : ∀ i j, IsVerBall D (H \ S) Gi (closedBall c R) i j → qrad j ≤ compDist A (qpt i))
    {z : ℂ} (hz : z ∈ D) (hGz : G z ∈ ball c R) : z ∉ A := by
  intro hzA
  have hGc : ContinuousAt G z := hc.continuousOn.continuousAt (hc.isOpen_D.mem_nhds hz)
  have h1 : ∀ᶠ y in 𝓝 z, G y ∈ ball c R := hGc.eventually (isOpen_ball.mem_nhds hGz)
  have h2 : ∀ᶠ y in 𝓝 z, y ∈ D := hc.isOpen_D.mem_nhds hz
  obtain ⟨ε, hε, hεs⟩ := Metric.eventually_nhds_iff_ball.1 (h1.and h2)
  obtain ⟨i, j, hzq, hv⟩ := hc.exists_verBall hGi (fun y hy => (hεs y hy).2)
    (fun y hy => ball_subset_closedBall (hεs y hy).1) (mem_ball_self hε)
  have hr := hcl i j hv
  have hball : ball (qpt i) (qrad j) ⊆ H \ relClosureH A :=
    (ball_subset_ball hr).trans ball_infDist_compl_subset
  have hzH : z ∈ H := hA hzA
  exact (hball hzq).2 ⟨hzH, subset_closure ⟨hzA, hzH⟩⟩

/-- **Clearance gives the clearance event.** -/
theorem clear_of_notMem (hc : IsChartSetting D (H \ S) G) (hGi : ∀ z ∈ D, Gi z = G z)
    (hA : A ⊆ H ∧ IsOpen (H \ A)) {y : ℂ} {ρ : ℝ} (hcl : ∀ z ∈ D, G z ∈ ball y ρ → z ∉ A) {c : ℂ} {R : ℝ}
    (hK : closedBall c R ⊆ ball y ρ) :
    ∀ i j, IsVerBall D (H \ S) Gi (closedBall c R) i j → qrad j ≤ compDist A (qpt i) := by
  intro i j hv
  obtain ⟨hB, hBK⟩ := hc.verBall_spec hGi isClosed_closedBall hv
  have hsub : ball (qpt i) (qrad j) ⊆ H \ relClosureH A := by
    rw [LocalSets.relClosureH_eq hA.1 hA.2]
    exact fun w hw => ⟨hc.subset_H (hB hw), hcl w (hB hw) (hK (hBK w hw))⟩
  exact GFF.le_infDist_of_ball_subset (LocalSets.H_diff_ne_univ _) hsub

/-- **The `τ` algebra of the Beurling-type bound**: with `R' = d₀ (R/(2B))^{C₂}`, the bound
`2B (2d/(c d₀))^{1/C₂} ≤ R τ_n(R')` holds on the `n`-th layer (`d ≤ 2 · 2^{-n}`). -/
theorem two_mul_le_mul_tauHi {B d₀ R d : ℝ} (hB : 0 < B) (hd₀ : 0 < d₀) (hR : 0 < R) (hd0 : 0 ≤ d) {n : ℕ}
    (hd : d ≤ 2 * (1 / 2 : ℝ) ^ n) :
    2 * (B * (2 * d / (koebeCovConst * d₀)) ^ koebeDistExp⁻¹) ≤
      R * tauHi (d₀ * (R / (2 * B)) ^ koebeDistExp) n := by
  have hc := koebeCovConst_pos
  have hC := koebeDistExp_pos
  set Y : ℝ := 2 * (2 * (1 / 2 : ℝ) ^ n) with hY
  have hY0 : 0 < Y := by positivity
  have hmono : (2 * d / (koebeCovConst * d₀)) ^ koebeDistExp⁻¹ ≤ (Y / (koebeCovConst * d₀)) ^ koebeDistExp⁻¹ :=
    Real.rpow_le_rpow (by positivity) (by gcongr; linarith) (inv_nonneg.2 hC.le)
  have hRB : 0 < R / (2 * B) := by positivity
  have hpow : 0 < (R / (2 * B)) ^ koebeDistExp := Real.rpow_pos_of_pos hRB _
  have e1 : Y / (koebeCovConst * (d₀ * (R / (2 * B)) ^ koebeDistExp)) =
      (Y / (koebeCovConst * d₀)) / (R / (2 * B)) ^ koebeDistExp := by
    field_simp
  have e2 : tauHi (d₀ * (R / (2 * B)) ^ koebeDistExp) n =
      (Y / (koebeCovConst * d₀)) ^ koebeDistExp⁻¹ / (R / (2 * B)) := by
    rw [tauHi, ← hY, e1, Real.div_rpow (by positivity) hpow.le, Real.rpow_rpow_inv hRB.le hC.ne']
  rw [e2]
  have e3 : R * ((Y / (koebeCovConst * d₀)) ^ koebeDistExp⁻¹ / (R / (2 * B))) =
      2 * (B * (Y / (koebeCovConst * d₀)) ^ koebeDistExp⁻¹) := by
    field_simp
  rw [e3]
  gcongr

/-- The bound on the reference factor `|G q − conj G y|² / (2 Im G q)` of a patch. -/
def refB (c R : ℝ) (k : ℕ) : ℝ := ((k : ℝ) + ‖(c : ℂ)‖ + 2 * R) ^ 2 / (2 * qrad k)

/-- The `τ`-radius of a patch. -/
def patchR (c R : ℝ) (k : ℕ) : ℝ := qrad k * (R / (2 * refB c R k)) ^ koebeDistExp

lemma refB_pos {c R : ℝ} (hR : 0 < R) (k : ℕ) : 0 < refB c R k := by
  have : 0 < (k : ℝ) + ‖(c : ℂ)‖ + 2 * R := by positivity
  unfold refB; have := qrad_pos k; positivity

lemma patchR_pos {c R : ℝ} (hR : 0 < R) (k : ℕ) : 0 < patchR c R k := by
  have := refB_pos (c := c) hR k
  unfold patchR
  exact mul_pos (qrad_pos k) (Real.rpow_pos_of_pos (by positivity) _)

/-- **The patch facts at a layer point**: the Beurling-type bound `2 Im G(y) ≤ R τ_n` and the Whitney bump ball
`B̄(y, δ_n)` lies in `D` with chart values in `B(c, 3R)`. -/
theorem patch_facts (hc : IsChartSetting D (H \ S) G) {c R : ℝ} (hR : 0 < R) {k : ℕ} {q : ℂ}
    (hq : q ∈ D) (hqd : qrad k ≤ infDist q (H \ S)ᶜ) (hqi : qrad k ≤ (G q).im) (hqn : ‖G q‖ ≤ k)
    {y : ℂ} (hyD : y ∈ D) (hyK : G y ∈ closedBall (c : ℂ) (2 * R)) {n : ℕ}
    (hd1 : (1 / 2 : ℝ) ^ (n + 2) ≤ infDist y (H \ S)ᶜ) (hd2 : infDist y (H \ S)ᶜ ≤ 2 * (1 / 2 : ℝ) ^ n)
    (hnk : 4 * (1 / 2 : ℝ) ^ n ≤ qrad k) (hτ : tauHi (patchR c R k) n ≤ 1 / 4) :
    2 * (G y).im ≤ R * tauHi (patchR c R k) n ∧
      ∀ ζ ∈ closedBall y (bumpRad (patchR c R k) n), ζ ∈ D ∧ ‖G ζ - c‖ < 3 * R := by
  have hc0 := koebeCovConst_pos
  have hC := koebeDistExp_pos
  have hR' := patchR_pos (c := c) hR k
  have hk := qrad_pos k
  have hdy := hc.infDist_eq hyD
  have hdq := hc.infDist_eq hq
  set d := infDist y Dᶜ with hd
  set d₀ := infDist q Dᶜ with hd₀
  rw [← hdy] at hd1 hd2
  rw [← hdq] at hqd
  have hd0 : 0 < d := lt_of_lt_of_le (by positivity) hd1
  have hdd : 2 * d ≤ d₀ := by linarith
  have hB := im_le_of_ref hc.isOpen_D hc.subset_H hc.conf hyD hq hdd
  have hw : G y ∈ H := hc.mapsTo hyD
  have hw₀ : G q ∈ H := hc.mapsTo hq
  -- the reference factor is at most `refB`
  have hnorm : ‖G q - conj (G y)‖ ≤ (k : ℝ) + ‖(c : ℂ)‖ + 2 * R := by
    have h1 : ‖G y‖ ≤ ‖(c : ℂ)‖ + 2 * R := by
      have := mem_closedBall.1 hyK
      rw [dist_eq_norm] at this
      linarith [norm_le_norm_add_norm_sub' (G y) (c : ℂ)]
    calc ‖G q - conj (G y)‖ ≤ ‖G q‖ + ‖conj (G y)‖ := norm_sub_le _ _
      _ ≤ (k : ℝ) + (‖(c : ℂ)‖ + 2 * R) := by rw [RCLike.norm_conj]; linarith
      _ = _ := by ring
  have hBfac : ‖G q - conj (G y)‖ ^ 2 / (2 * (G q).im) ≤ refB c R k := by
    unfold refB
    have : 0 ≤ ‖G q - conj (G y)‖ := norm_nonneg _
    exact div_le_div₀ (by positivity) (pow_le_pow_left₀ this hnorm 2) (by positivity) (by linarith)
  have hd₀0 : 0 < d₀ := by linarith
  have hnn : 0 ≤ 2 * d / (koebeCovConst * d₀) := div_nonneg (by positivity) (mul_nonneg hc0.le hd₀0.le)
  have hpow : (2 * d / (koebeCovConst * d₀)) ^ koebeDistExp⁻¹ ≤
      (2 * d / (koebeCovConst * qrad k)) ^ koebeDistExp⁻¹ :=
    Real.rpow_le_rpow hnn (div_le_div_of_nonneg_left (by positivity) (by positivity)
      (mul_le_mul_of_nonneg_left hqd hc0.le)) (inv_nonneg.2 hC.le)
  have him : (G y).im ≤ refB c R k * (2 * d / (koebeCovConst * qrad k)) ^ koebeDistExp⁻¹ :=
    hB.trans (mul_le_mul hBfac hpow (Real.rpow_nonneg hnn _) (refB_pos hR k).le)
  have htau := two_mul_le_mul_tauHi (refB_pos (c := c) hR k) hk hR hd0.le hd2
  have hfirst : 2 * (G y).im ≤ R * tauHi (patchR c R k) n := by
    have : 2 * (G y).im ≤ 2 * (refB c R k * (2 * d / (koebeCovConst * qrad k)) ^ koebeDistExp⁻¹) := by
      linarith
    exact this.trans htau
  refine ⟨hfirst, fun ζ hζ => ?_⟩
  have hlo := LocalSets.tauLo_le_tauHi hR' n
  have hlo0 := LocalSets.tauLo_pos hR' n
  have hδ : bumpRad (patchR c R k) n < 3 / 4 * d := by
    unfold bumpRad
    have : tauLo (patchR c R k) n * (1 / 2 : ℝ) ^ (n + 2) / 2 ≤ (1 / 4) * (1 / 2 : ℝ) ^ (n + 2) / 2 := by
      gcongr; linarith
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 2) (n + 2)]
  have hζd : dist ζ y < 3 / 4 * d := lt_of_le_of_lt (mem_closedBall.1 hζ) hδ
  refine ⟨hc.ball_three_quarters_subset hyD (mem_ball.2 hζd), ?_⟩
  have h1 := hc.norm_sub_lt hyD hζd
  have h2 : ‖G y - c‖ ≤ 2 * R := by rw [← dist_eq_norm]; exact mem_closedBall.1 hyK
  have h3 : R * tauHi (patchR c R k) n ≤ R / 4 := by nlinarith
  calc ‖G ζ - c‖ = ‖(G ζ - G y) + (G y - c)‖ := by ring_nf
    _ ≤ ‖G ζ - G y‖ + ‖G y - c‖ := norm_add_le _ _
    _ < 3 * R := by linarith

/-- **The variance gap at a layer point of a cleared patch**: for the bump `ψ` of radius `δ_n` at `y`,
`σ²_{ℍ∖S}(ψ) − σ²_{ℍ∖A}(ψ) ≤ 4 τ_n (∫ψ)²`. -/
theorem gap_of_patch (hc : IsChartSetting D (H \ S) G) (hS : S ⊆ H ∧ IsOpen (H \ S))
    (hA : A ⊆ H ∧ IsOpen (H \ A)) {c R : ℝ} (hR : 0 < R)
    (hcl : ∀ z ∈ D, G z ∈ ball (c : ℂ) (4 * R) → z ∉ A) {k : ℕ} {q : ℂ}
    (hq : q ∈ D) (hqd : qrad k ≤ infDist q (H \ S)ᶜ) (hqi : qrad k ≤ (G q).im) (hqn : ‖G q‖ ≤ k)
    {y : ℂ} (hyD : y ∈ D) (hyK : G y ∈ closedBall (c : ℂ) (2 * R)) {n : ℕ}
    (hd1 : (1 / 2 : ℝ) ^ (n + 2) ≤ infDist y (H \ S)ᶜ) (hd2 : infDist y (H \ S)ᶜ ≤ 2 * (1 / 2 : ℝ) ^ n)
    (hnk : 4 * (1 / 2 : ℝ) ^ n ≤ qrad k) (hτ : tauHi (patchR c R k) n ≤ 1 / 4) :
    zeroGFFTestCov (H \ S) (bumpTestH (bumpRad (patchR c R k) n)
        (LocalSets.bumpRad_pos (patchR_pos hR k) n) y)
      (bumpTestH (bumpRad (patchR c R k) n) (LocalSets.bumpRad_pos (patchR_pos hR k) n) y) -
    zeroGFFTestCov (H \ A) (bumpTestH (bumpRad (patchR c R k) n)
        (LocalSets.bumpRad_pos (patchR_pos hR k) n) y)
      (bumpTestH (bumpRad (patchR c R k) n) (LocalSets.bumpRad_pos (patchR_pos hR k) n) y) ≤
    4 * tauHi (patchR c R k) n * (∫ z, (bumpTestH (bumpRad (patchR c R k) n)
        (LocalSets.bumpRad_pos (patchR_pos hR k) n) y) z) ^ 2 := by
  have hR' := patchR_pos (c := c) hR k
  set δ := bumpRad (patchR c R k) n with hδdef
  have hδ0 : 0 < δ := LocalSets.bumpRad_pos hR' n
  obtain ⟨hIm, hball⟩ := patch_facts hc hR hq hqd hqi hqn hyD hyK hd1 hd2 hnk hτ
  have hBH : closedBall y δ ⊆ H := fun ζ hζ => hc.subset_H (hball ζ hζ).1
  have hy : δ < y.im := (LocalSets.closedBall_subset_H_iff hδ0.le).1 hBH
  have hψc := LocalSets.coe_bumpTestH_of_lt hδ0 hy
  have hdy := hc.infDist_eq hyD
  have hlo := LocalSets.tauLo_le_tauHi hR' n
  have hlo0 := LocalSets.tauLo_pos hR' n
  have ht0 : 0 < tauHi (patchR c R k) n := lt_of_lt_of_le hlo0 hlo
  refine zeroGFFTestCov_sub_le_of_chart hS.2 hc.isOpen_D hc.subset_O hc.comp hc.conf hA.2 sdiff_subset
    (fun z hz hGz => ⟨hc.subset_H hz, hcl z hz hGz⟩) hyD ht0 hτ ?_ _ ?_ ?_
  · have h1 : dist (G y) c ≤ 2 * R := mem_closedBall.1 hyK
    have h2 : 2 * (G y).im / tauHi (patchR c R k) n ≤ R := by rw [div_le_iff₀ ht0]; linarith
    linarith
  · intro z; rw [hψc]; exact GFF.bumpFun_nonneg y δ z
  · intro z hz
    rw [hψc] at hz
    have hzy : dist z y < δ := by
      by_contra hge
      exact hz (GFF.bumpFun_eq_zero hδ0 (not_lt.1 hge))
    rw [hdy]
    refine lt_of_lt_of_le hzy ?_
    rw [hδdef, LocalSets.bumpRad]
    have h0 : 0 < (1 / 2 : ℝ) ^ (n + 2) := by positivity
    calc tauLo (patchR c R k) n * (1 / 2 : ℝ) ^ (n + 2) / 2 ≤ tauLo (patchR c R k) n * (1 / 2 : ℝ) ^ (n + 2) := by
          linarith [mul_pos hlo0 h0]
      _ ≤ tauHi (patchR c R k) n * infDist y (H \ S)ᶜ := mul_le_mul hlo hd1 h0.le ht0.le

end Pathwise

/-! ### Borel–Cantelli on a patch -/

section Patch

/-- **The standing hypotheses of the chart form of Proposition 3.8.** The field paired with every test function is
conditionally Gaussian given `𝒥` (mean `g`, variance on `ℍ ∖ A`) and given `𝒢 ≤ 𝒥` (mean `g₂`, variance on
`ℍ ∖ A₂`); `A₂ ⊆ A` are relatively closed in `ℍ` with `σ(A₂) ≤ 𝒢`, `σ(A) ≤ 𝒥`; `g`, `g₂` are measurable and harmonic
off `A`, `A₂`; `D` is a union of components of `ℍ ∖ A₂` with a conformal chart `G : D → ℍ` of bounded displacement;
membership in `D` and the chart values at fixed points are `𝒢`-measurable. -/
structure IsChartData {Ω : Type*} (𝒢 𝒥 : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (h g g₂ : Ω → DistOn upperHalfPlaneOpens) (A A₂ D : Ω → Set ℂ) (G : Ω → ℂ → ℂ) : Prop where
  le : 𝒢 ≤ 𝒥
  law₁ : ∀ ψ : TestOn upperHalfPlaneOpens, IsCondGaussian 𝒥 P (fun ω => h ω ψ) (fun ω => g ω ψ)
    (fun ω => zeroGFFTestCov (H \ relClosureH (A ω)) ψ ψ) (zeroGFFTestCov H ψ ψ)
  law₂ : ∀ ψ : TestOn upperHalfPlaneOpens, IsCondGaussian 𝒢 P (fun ω => h ω ψ) (fun ω => g₂ ω ψ)
    (fun ω => zeroGFFTestCov (H \ relClosureH (A₂ ω)) ψ ψ) (zeroGFFTestCov H ψ ψ)
  meas_A : MeasurableSpace.comap A hittingSigma ≤ 𝒥
  meas_A₂ : MeasurableSpace.comap A₂ hittingSigma ≤ 𝒢
  meas_g : Measurable g
  meas_g₂ : Measurable g₂
  closed : ∀ᵐ ω ∂P, (A ω ⊆ H ∧ IsOpen (H \ A ω)) ∧ (A₂ ω ⊆ H ∧ IsOpen (H \ A₂ ω)) ∧ A₂ ω ⊆ A ω
  harm : ∀ᵐ ω ∂P, IsHarmonicDistOn (g ω) (H \ A ω) ∧ IsHarmonicDistOn (g₂ ω) (H \ A₂ ω)
  chart : ∀ᵐ ω ∂P, IsChartSetting (D ω) (H \ A₂ ω) (G ω) ∧ ∃ M : ℝ, ∀ z ∈ D ω, ‖G ω z - z‖ ≤ M
  meas_D : ∀ q : ℂ, MeasurableSet[𝒢] {ω | q ∈ D ω}
  meas_G : ∀ q : ℂ, Measurable[𝒢] fun ω => chartInd D G ω q

variable {Ω : Type*} {𝒢 𝒥 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {h g g₂ : Ω → DistOn upperHalfPlaneOpens} {A A₂ D : Ω → Set ℂ} {G : Ω → ℂ → ℂ}

omit mΩ [IsProbabilityMeasure P] in
theorem measurableSet_regSet_section (hA₂ : MeasurableSpace.comap A₂ hittingSigma ≤ 𝒢)
    (hDm : ∀ q, MeasurableSet[𝒢] {ω | q ∈ D ω}) (hGm : ∀ q, Measurable[𝒢] fun ω => chartInd D G ω q)
    {K : Set ℂ} (hK : MeasurableSet K) (y : ℂ) : MeasurableSet[𝒢] {ω | (ω, y) ∈ regSet D A₂ G K} := by
  have e : {ω | (ω, y) ∈ regSet D A₂ G K} =
      ⋃ i : ℕ, ⋃ j : ℕ, {ω | ω ∈ verEv D A₂ G K i j ∧ y ∈ ball (qpt i) (qrad j)} := by
    ext ω
    simp only [regSet, mem_ofPred_eq, mem_iUnion, mem_prod]
  rw [e]
  refine MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun j => ?_
  by_cases hy : y ∈ ball (qpt i) (qrad j)
  · simp only [hy, and_true]
    exact measurableSet_verEv hA₂ hDm hGm hK i j
  · simp only [hy, and_false, ofPred_false, MeasurableSet.empty]

omit mΩ [IsProbabilityMeasure P] in
/-- **The pathwise content of a layer set.** -/
theorem lset_facts {c R : ℝ} {i₀ k Rp n : ℕ} {ω : Ω} (hA : A ω ⊆ H ∧ IsOpen (H \ A ω))
    (hA₂ : A₂ ω ⊆ H ∧ IsOpen (H \ A₂ ω)) (hc : IsChartSetting (D ω) (H \ A₂ ω) (G ω)) {y : ℂ}
    (hy : (ω, y) ∈ Lset D A₂ A G c R i₀ k Rp n) :
    y ∈ D ω ∧ G ω y ∈ closedBall (c : ℂ) (2 * R) ∧ (∀ z ∈ D ω, G ω z ∈ ball (c : ℂ) (4 * R) → z ∉ A ω) ∧
      qpt i₀ ∈ D ω ∧ qrad k ≤ infDist (qpt i₀) (H \ A₂ ω)ᶜ ∧ qrad k ≤ (G ω (qpt i₀)).im ∧
      ‖G ω (qpt i₀)‖ ≤ k ∧ (1 / 2 : ℝ) ^ (n + 2) ≤ infDist y (H \ A₂ ω)ᶜ ∧
      infDist y (H \ A₂ ω)ᶜ ≤ 2 * (1 / 2 : ℝ) ^ n := by
  have hrc : relClosureH (A₂ ω) = A₂ ω := LocalSets.relClosureH_eq hA₂.1 hA₂.2
  have hGi : ∀ z ∈ D ω, chartInd D G ω z = G ω z := fun z hz => chartInd_of_mem hz
  obtain ⟨⟨hcl, href⟩, hlay, hreg⟩ := hy
  simp only [regSet, mem_iUnion, mem_prod] at hreg
  obtain ⟨i, j, hv, hyb⟩ := hreg
  have hv' : IsVerBall (D ω) (H \ A₂ ω) (chartInd D G ω) (closedBall (c : ℂ) (2 * R)) i j := by
    have := hv; simp only [verEv, mem_ofPred_eq, hrc] at this; exact this
  obtain ⟨hB, hBK⟩ := hc.verBall_spec hGi isClosed_closedBall hv'
  have hcl' : ∀ i j, IsVerBall (D ω) (H \ A₂ ω) (chartInd D G ω) (closedBall (c : ℂ) (4 * R)) i j →
      qrad j ≤ compDist (A ω) (qpt i) := fun i j hv => hcl i j (by
    simp only [verEv, mem_ofPred_eq, hrc]; exact hv)
  obtain ⟨hq, hqd, hqi, hqn⟩ := href
  simp only [compDist, hrc] at hqd
  rw [chartInd_of_mem hq] at hqi hqn
  have hlay' : y ∈ GFF.layerSet (H \ A₂ ω) 0 Rp n := by rw [← hrc]; exact hlay
  exact ⟨hB hyb, hBK y hyb, fun z hz hGz => notMem_of_clear hc hGi hA.1 hcl' hz hGz, hq, hqd, hqi, hqn,
    hlay'.1.2, hlay'.2⟩

/-- **Borel–Cantelli on a chart patch.** For every patch (chart centre `c`, chart radius `R`, reference point
`q_{i₀}` with bound `k`, physical radius `Rp`) and `η > 0`, almost surely, for all large `n`, `|u| < η` at every point
whose ball `B̄(w, 2^{-n-2})` lies in the `n`-th layer set of the patch. -/
theorem ae_patch (hd : IsChartData 𝒢 𝒥 P h g g₂ A A₂ D G) {u : Ω → ℂ → ℝ}
    (hu : ∀ᵐ ω ∂P, InnerProductSpace.HarmonicOnNhd (u ω) (H \ A ω) ∧
      ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω → g ω φ - g₂ ω φ = ∫ z, u ω z * φ z)
    (c : ℝ) {R : ℝ} (hR : 0 < R) (i₀ k Rp : ℕ) {η : ℝ} (hη : 0 < η) :
    ∀ᵐ ω ∂P, ∃ N : ℕ, ∀ n ≥ N, ∀ w : ℂ,
      closedBall w ((1 / 2 : ℝ) ^ (n + 2)) ⊆ {y | (ω, y) ∈ Lset D A₂ A G c R i₀ k Rp n} → |u ω w| < η := by
  classical
  have hR' := patchR_pos (c := c) hR k
  have h𝒥 : 𝒥 ≤ mΩ := (hd.law₁ 0).le
  have h𝒢 : 𝒢 ≤ mΩ := hd.le.trans h𝒥
  have hA₂m : Measurable[mΩ, hittingSigma] A₂ := Measurable.of_comap_le (hd.meas_A₂.trans h𝒢)
  set T : Ω → DistOn upperHalfPlaneOpens := fun ω => g ω - g₂ ω with hTdef
  have hTm : Measurable T := LQGMetric.measurable_distOn_iff.2 fun φ =>
    ((LQGMetric.measurable_distOn_apply φ).comp hd.meas_g).sub
      ((LQGMetric.measurable_distOn_apply φ).comp hd.meas_g₂)
  have h4 : ∀ᶠ n : ℕ in atTop, 4 * (1 / 2 : ℝ) ^ n ≤ qrad k := by
    have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)).const_mul 4
    rw [mul_zero] at ht
    exact (ht.eventually (gt_mem_nhds (qrad_pos k))).mono fun n hn => hn.le
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.1 ((GFF.eventually_params hR' 1).and h4)
  set E := clEv D A₂ A G (closedBall (c : ℂ) (4 * R)) ∩ refEv D A₂ G i₀ k with hEdef
  have hE : MeasurableSet[𝒥] E :=
    (measurableSet_clEv hd.le hd.meas_A hd.meas_A₂ hd.meas_D hd.meas_G measurableSet_closedBall).inter
      (hd.le _ (measurableSet_refEv hd.meas_A₂ hd.meas_D hd.meas_G i₀ k))
  refine ae_eventually_abs_lt_of_sets (L := fun n => Lset D A₂ A G c R i₀ k Rp n) (c := 0) (R := Rp)
    (U := fun ω => H \ A ω)
    (G := fun n p => bumpPair T (bumpRad (patchR c R k) n) (LocalSets.bumpRad_pos hR' n) p /
      (bumpRad (patchR c R k) n ^ 2 * GFF.bumpMass))
    (fun n => ?_) (fun n p hp => GFF.layerSet_subset_ball _ _ _ _ hp.2.1)
    (fun n => (LocalSets.measurable_bumpPair hTm _).div_const _) hR' (n₁ := n₁) ?_ ?_ hη
  · -- measurability of the layer sets
    have e : Lset D A₂ A G c R i₀ k Rp n = (E ×ˢ univ) ∩
        {p : Ω × ℂ | p.2 ∈ GFF.layerSet (H \ relClosureH (A₂ p.1)) 0 Rp n} ∩
        regSet D A₂ G (closedBall (c : ℂ) (2 * R)) := by
      ext p
      simp only [Lset, hEdef, mem_inter_iff, mem_prod, mem_univ, and_true, mem_ofPred_eq]
      tauto
    rw [e]
    exact (((h𝒥 _ hE).prod MeasurableSet.univ).inter
      (LocalSets.measurableSet_layerSet_compl hA₂m 0 Rp n)).inter
      (measurableSet_regSet h𝒢 hd.meas_A₂ hd.meas_D hd.meas_G measurableSet_closedBall)
  · -- the harmonic representative on the layer sets
    filter_upwards [hu, hd.closed, hd.chart] with ω ⟨huh, hur⟩ ⟨hAω, hA₂ω, _⟩ ⟨hcω, _⟩
    refine ⟨hAω.2, huh, fun n hn y hy => ?_⟩
    obtain ⟨hyD, hyK, hclz, hq, hqd, hqi, hqn, hd1, hd2⟩ := lset_facts hAω hA₂ω hcω hy
    obtain ⟨⟨-, hτ, -⟩, hn2⟩ := hn₁ n hn
    obtain ⟨-, hball⟩ := patch_facts hcω hR hq hqd hqi hqn hyD hyK hd1 hd2 hn2 hτ
    have hB : closedBall y (bumpRad (patchR c R k) n) ⊆ H \ A ω := fun ζ hζ =>
      ⟨hcω.subset_H (hball ζ hζ).1, hclz ζ (hball ζ hζ).1 (by
        rw [mem_ball, dist_eq_norm]; linarith [(hball ζ hζ).2])⟩
    refine ⟨hB (mem_closedBall_self (LocalSets.bumpRad_pos hR' n).le), ?_⟩
    exact LocalSets.bumpPair_eq_of_harmonic (T := T) (LocalSets.bumpRad_pos hR' n) hAω.2 huh
      (fun φ hφ => hur φ hφ) hB sdiff_subset
  · -- the moment bound on the layer sets
    intro n hn y l hl
    obtain ⟨⟨-, hτ, -⟩, hn2⟩ := hn₁ n hn
    set δ := bumpRad (patchR c R k) n with hδdef
    have hδ : 0 < δ := LocalSets.bumpRad_pos hR' n
    by_cases hy : δ < y.im
    · set ψ := bumpTestH δ hδ y with hψ
      have hψc : ⇑ψ = GFF.bumpFun y δ := LocalSets.coe_bumpTestH_of_lt hδ hy
      set m := δ ^ 2 * GFF.bumpMass with hm
      have hm0 : 0 < m := by have := GFF.bumpMass_pos; positivity
      have hint : ∫ z, ψ z = m := by rw [hψc]; exact GFF.integral_bumpFun hδ
      set F := {ω | y ∈ GFF.layerSet (H \ relClosureH (A₂ ω)) 0 Rp n} with hFdef
      have hF : MeasurableSet[𝒢] F := hd.meas_A₂ _ (LocalSets.measurableSet_mem_layerSet_compl A₂ 0 Rp n y)
      set E' := E ∩ {ω | (ω, y) ∈ regSet D A₂ G (closedBall (c : ℂ) (2 * R))} with hE'def
      have hE' : MeasurableSet[𝒥] E' := hE.inter (hd.le _ (measurableSet_regSet_section hd.meas_A₂ hd.meas_D
        hd.meas_G measurableSet_closedBall y))
      have hset : {ω | (ω, y) ∈ Lset D A₂ A G c R i₀ k Rp n} = E' ∩ F := by
        ext ω
        simp only [Lset, hE'def, hFdef, hEdef, mem_ofPred_eq, mem_inter_iff]
        tauto
      have hκ : ∀ᵐ ω ∂P, ω ∈ E' → ω ∈ F →
          zeroGFFTestCov (H \ relClosureH (A₂ ω)) ψ ψ - zeroGFFTestCov (H \ relClosureH (A ω)) ψ ψ ≤
            4 * tauHi (patchR c R k) n * m ^ 2 := by
        filter_upwards [hd.closed, hd.chart] with ω ⟨hAω, hA₂ω, _⟩ ⟨hcω, _⟩ hωE hωF
        have hmem : (ω, y) ∈ Lset D A₂ A G c R i₀ k Rp n := by
          have : ω ∈ {ω | (ω, y) ∈ Lset D A₂ A G c R i₀ k Rp n} := by rw [hset]; exact ⟨hωE, hωF⟩
          exact this
        obtain ⟨hyD, hyK, hclz, hq, hqd, hqi, hqn, hd1, hd2⟩ := lset_facts hAω hA₂ω hcω hmem
        have hgap := gap_of_patch hcω hA₂ω hAω hR hclz hq hqd hqi hqn hyD hyK hd1 hd2 hn2 hτ
        rw [LocalSets.relClosureH_eq hA₂ω.1 hA₂ω.2, LocalSets.relClosureH_eq hAω.1 hAω.2]
        rw [← hint]
        exact hgap
      have key := lintegral_indicator_exp_mean_sub_le hd.le (hd.law₁ ψ) (hd.law₂ ψ) hE' hF hκ (l / m)
      have e4 : ∀ ω, {ω | (ω, y) ∈ Lset D A₂ A G c R i₀ k Rp n}.indicator (fun ω => ENNReal.ofReal
          (Real.exp (l * (bumpPair T δ hδ (ω, y) / (δ ^ 2 * GFF.bumpMass))))) ω =
          (E' ∩ F).indicator (fun ω => ENNReal.ofReal (Real.exp (l / m * (g ω ψ - g₂ ω ψ)))) ω := by
        intro ω
        rw [hset]
        have : ∀ ω' : Ω, l * (bumpPair T δ hδ (ω', y) / (δ ^ 2 * GFF.bumpMass)) =
            l / m * (g ω' ψ - g₂ ω' ψ) := by
          intro ω'
          simp only [LocalSets.bumpPair, hy, ↓reduceIte, hm]
          rw [hTdef]
          simp only [sub_apply]
          ring
        simp only [this]
      rw [lintegral_congr e4]
      refine key.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
      have e3 : (l / m) ^ 2 * (4 * tauHi (patchR c R k) n * m ^ 2) / 2 = 2 * l ^ 2 * tauHi (patchR c R k) n := by
        field_simp
        ring
      rw [e3]; exact hl
    · have h0 : ∀ ω, {ω | (ω, y) ∈ Lset D A₂ A G c R i₀ k Rp n}.indicator (fun ω => ENNReal.ofReal
          (Real.exp (l * (bumpPair T δ hδ (ω, y) / (δ ^ 2 * GFF.bumpMass))))) ω = 0 := by
        intro ω
        refine indicator_of_notMem (fun hmem => hy ?_) _
        have hlay := hmem.2.1
        have hlt : δ < (1 / 2 : ℝ) ^ (n + 2) := LocalSets.bumpRad_lt hR' hτ
        have hB : closedBall y δ ⊆ H := fun ζ hζ =>
          (ball_infDist_compl_subset (mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 hζ)
            (lt_of_lt_of_le hlt hlay.1.2)))).1
        exact (LocalSets.closedBall_subset_H_iff hδ.le).1 hB
      calc _ = ∫⁻ _, (0 : ℝ≥0∞) ∂P := lintegral_congr h0
        _ = 0 := lintegral_zero
        _ ≤ _ := zero_le

end Patch

/-! ### The main theorem -/

section Main

/-- **Along a filter on `D` on which a chart of bounded displacement tends to a real point, the points approach
`∂D`**: `Im G` is bounded below on the compact sets `{dist(·, ∂D) ≥ δ} ∩ B̄(0, M')`. -/
theorem eventually_infDist_compl_lt {D O : Set ℂ} {G : ℂ → ℂ} (hc : IsChartSetting D O G) {M : ℝ}
    (hM : ∀ z ∈ D, ‖G z - z‖ ≤ M) {F : Filter ℂ} (hF : F ≤ 𝓟 D) {y : ℝ} (hT : Tendsto G F (𝓝 (y : ℂ)))
    {δ : ℝ} (hδ : 0 < δ) : ∀ᶠ z in F, infDist z Dᶜ < δ := by
  set M' := |y| + 1 + M with hM'
  have hev1 : ∀ᶠ z in F, z ∈ D := le_principal_iff.1 hF
  have hev2 : ∀ᶠ z in F, ‖G z - y‖ < 1 := by
    have := (Metric.tendsto_nhds.1 hT) 1 one_pos
    filter_upwards [this] with z hz
    rwa [dist_eq_norm] at hz
  have hbd : ∀ᶠ z in F, ‖z‖ ≤ M' := by
    filter_upwards [hev1, hev2] with z hzD hz
    have h1 := hM z hzD
    have h2 : ‖G z‖ ≤ |y| + 1 := by
      have := norm_le_norm_add_norm_sub' (G z) (y : ℂ)
      rw [Complex.norm_real, Real.norm_eq_abs] at this
      linarith
    have h3 : ‖z‖ ≤ ‖G z‖ + ‖G z - z‖ := by
      have := norm_sub_le (G z) (G z - z)
      rwa [sub_sub_cancel] at this
    linarith
  set K : Set ℂ := {ζ | δ ≤ infDist ζ Dᶜ} ∩ closedBall 0 M' with hKdef
  have hKc : IsCompact K :=
    (isCompact_closedBall 0 M').inter_left (isClosed_le continuous_const (continuous_infDist_pt _))
  have hKD : K ⊆ D := fun ζ hζ => by
    by_contra hζD
    have := infDist_zero_of_mem (show ζ ∈ Dᶜ from hζD)
    have := hζ.1
    simp only [mem_ofPred_eq] at this
    linarith
  by_cases hK : K.Nonempty
  · obtain ⟨ζ₀, hζ₀K, hmin⟩ := hKc.exists_isMinOn hK
      ((Complex.continuous_im.comp_continuousOn hc.continuousOn).mono hKD)
    have hm₀ : 0 < (G ζ₀).im := hc.mapsTo (hKD hζ₀K)
    have hev3 : ∀ᶠ z in F, ‖G z - y‖ < (G ζ₀).im := by
      have := (Metric.tendsto_nhds.1 hT) _ hm₀
      filter_upwards [this] with z hz
      rwa [dist_eq_norm] at hz
    filter_upwards [hev1, hbd, hev3] with z hzD hzb hz3
    by_contra hge
    push Not at hge
    have hzK : z ∈ K := ⟨hge, mem_closedBall_zero_iff.2 hzb⟩
    have h1 : (G ζ₀).im ≤ (G z).im := hmin hzK
    have h2 : (G z).im ≤ ‖G z - y‖ := by
      have := Complex.abs_im_le_norm (G z - y)
      simp only [sub_im, ofReal_im, sub_zero] at this
      exact (le_abs_self _).trans this
    linarith
  · filter_upwards [hbd] with z hzb
    by_contra hge
    push Not at hge
    exact hK ⟨z, hge, mem_closedBall_zero_iff.2 hzb⟩

variable {Ω : Type*} {𝒢 𝒥 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {h g g₂ : Ω → DistOn upperHalfPlaneOpens} {A A₂ D : Ω → Set ℂ} {G : Ω → ℂ → ℂ}

/-- **Proposition 3.8 in a chart** (Aux. lemma 82's boundary-decay step). Under the standing hypotheses
`IsChartData`, almost surely the harmonic representative `u` of `g − g₂` on `ℍ ∖ A` tends to `0` along every filter
on `D` along which the chart tends to a real point `y` whose chart ball `B(y, ρ)` receives no point of `A ∩ D`. -/
theorem ae_tendsto_zero_of_chart (hd : IsChartData 𝒢 𝒥 P h g g₂ A A₂ D G) :
    ∀ᵐ ω ∂P, ∃ u : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd u (H \ A ω) ∧
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω → g ω φ - g₂ ω φ = ∫ z, u z * φ z) ∧
      ∀ y ρ : ℝ, 0 < ρ → (∀ z ∈ D ω, G ω z ∈ ball (y : ℂ) ρ → z ∉ A ω) →
        ∀ F : Filter ℂ, F ≤ 𝓟 (D ω) → Tendsto (G ω) F (𝓝 (y : ℂ)) → Tendsto u F (𝓝 0) := by
  classical
  set T : Ω → DistOn upperHalfPlaneOpens := fun ω => g ω - g₂ ω with hTdef
  have hTh : ∀ᵐ ω ∂P, IsHarmonicDistOn (T ω) (H \ A ω) := by
    filter_upwards [hd.harm, hd.closed] with ω ⟨h1, h2⟩ ⟨⟨_, ho⟩, _, hs⟩
    exact LocalSets.IsHarmonicDistOn.sub' ho h1
      (LocalSets.IsHarmonicDistOn.mono h2 (fun z hz => ⟨hz.1, fun h' => hz.2 (hs h')⟩))
  set u : Ω → ℂ → ℝ := fun ω => if hω : IsHarmonicDistOn (T ω) (H \ A ω) then hω.choose else 0 with hudef
  have hu : ∀ᵐ ω ∂P, InnerProductSpace.HarmonicOnNhd (u ω) (H \ A ω) ∧
      ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω → g ω φ - g₂ ω φ = ∫ z, u ω z * φ z := by
    filter_upwards [hTh] with ω hω
    simp only [hudef, hω, dite_true]
    exact hω.choose_spec
  have hBC : ∀ p : ℚ × ℕ × ℕ × ℕ × ℕ × ℕ, ∀ᵐ ω ∂P, ∃ N : ℕ, ∀ n ≥ N, ∀ w : ℂ,
      closedBall w ((1 / 2 : ℝ) ^ (n + 2)) ⊆
        {y | (ω, y) ∈ Lset D A₂ A G p.1 (qrad p.2.1) p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 n} →
      |u ω w| < qrad p.2.2.2.2.2 :=
    fun p => ae_patch hd hu p.1 (qrad_pos _) _ _ _ (qrad_pos _)
  filter_upwards [ae_all_iff.2 hBC, hu, hd.closed, hd.chart] with ω hω ⟨huh, hur⟩ ⟨hAω, hA₂ω, _⟩ ⟨hcω, M, hM⟩
  refine ⟨u ω, huh, hur, fun y ρ hρ hclr F hF hT => ?_⟩
  have hrc : relClosureH (A₂ ω) = A₂ ω := LocalSets.relClosureH_eq hA₂ω.1 hA₂ω.2
  have hGi : ∀ z ∈ D ω, chartInd D G ω z = G ω z := fun z hz => chartInd_of_mem hz
  rw [Metric.tendsto_nhds]
  intro ε hε
  by_cases hDne : (D ω).Nonempty
  swap
  · have hF0 : F = ⊥ := le_bot_iff.1 (hF.trans (by rw [not_nonempty_iff_eq_empty.1 hDne, principal_empty]))
    rw [hF0]; exact eventually_bot
  -- the parameters of the patch
  obtain ⟨mm, hmm⟩ := exists_nat_one_div_lt hε
  obtain ⟨jR, hjR⟩ := exists_nat_one_div_lt (show 0 < ρ / 5 by positivity)
  set R := qrad jR with hRdef
  have hR : 0 < R := qrad_pos jR
  obtain ⟨qc, hqc1, hqc2⟩ := exists_rat_btwn (show y - R / 2 < y + R / 2 by linarith)
  have hcy : ‖((qc : ℝ) : ℂ) - (y : ℂ)‖ < R / 2 := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_lt]; constructor <;> linarith
  obtain ⟨z₀, hz₀⟩ := hDne
  have hDne' : D ω ≠ univ := ne_univ_of_subset_H hcω.subset_H
  have hz₀d : 0 < infDist z₀ (D ω)ᶜ := infDist_compl_pos hcω.isOpen_D hDne' hz₀
  obtain ⟨i₀, hi₀⟩ := Metric.denseRange_iff.1 (TopologicalSpace.denseRange_denseSeq ℂ) z₀ _ hz₀d
  have hq : qpt i₀ ∈ D ω := ball_infDist_compl_subset (by rw [mem_ball, dist_comm]; exact hi₀)
  have hqd0 : 0 < infDist (qpt i₀) (H \ A₂ ω)ᶜ := by
    rw [← hcω.infDist_eq hq]; exact infDist_compl_pos hcω.isOpen_D hDne' hq
  have hqi0 : 0 < (G ω (qpt i₀)).im := hcω.mapsTo hq
  obtain ⟨k₁, hk₁⟩ := exists_nat_one_div_lt (lt_min hqd0 hqi0)
  set k := max k₁ ⌈‖G ω (qpt i₀)‖⌉₊ with hkdef
  have hqk : qrad k ≤ qrad k₁ := by
    unfold qrad
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right (le_max_left _ _) 1)
  set Rp : ℕ := ⌈|y| + 2 + M⌉₊ + 1 with hRpdef
  -- `ω` is in the patch event
  have hK4 : closedBall ((qc : ℝ) : ℂ) (4 * R) ⊆ ball (y : ℂ) ρ := fun ζ hζ => by
    rw [mem_ball, dist_eq_norm]
    have h1 : ‖ζ - ((qc : ℝ) : ℂ)‖ ≤ 4 * R := by rw [← dist_eq_norm]; exact mem_closedBall.1 hζ
    have h2 : R < ρ / 5 := hjR
    calc ‖ζ - (y : ℂ)‖ ≤ ‖ζ - ((qc : ℝ) : ℂ)‖ + ‖((qc : ℝ) : ℂ) - (y : ℂ)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < ρ := by linarith
  have hcl : ω ∈ clEv D A₂ A G (closedBall ((qc : ℝ) : ℂ) (4 * R)) := by
    intro i j hv
    have hv' : IsVerBall (D ω) (H \ A₂ ω) (chartInd D G ω) (closedBall ((qc : ℝ) : ℂ) (4 * R)) i j := by
      have := hv; simp only [verEv, mem_ofPred_eq, hrc] at this; exact this
    exact clear_of_notMem hcω hGi hAω hclr hK4 i j hv'
  have href : ω ∈ refEv D A₂ G i₀ k := by
    refine ⟨hq, ?_, ?_, ?_⟩
    · show qrad k ≤ infDist (qpt i₀) (H \ relClosureH (A₂ ω))ᶜ
      rw [hrc]; exact hqk.trans (hk₁.le.trans (min_le_left _ _))
    · rw [hGi _ hq]; exact hqk.trans (hk₁.le.trans (min_le_right _ _))
    · rw [hGi _ hq]
      exact (Nat.le_ceil _).trans (by exact_mod_cast le_max_right _ _)
  obtain ⟨N, hN⟩ := hω (qc, jR, i₀, k, Rp, mm)
  -- eventually along the filter
  have ev1 : ∀ᶠ z in F, z ∈ D ω := le_principal_iff.1 hF
  have ev2 : ∀ᶠ z in F, ‖G ω z - y‖ < R / 16 := by
    filter_upwards [(Metric.tendsto_nhds.1 hT) (R / 16) (by positivity)] with z hz
    rwa [dist_eq_norm] at hz
  have ev3 : ∀ᶠ z in F, ‖G ω z - y‖ < 1 := by
    filter_upwards [(Metric.tendsto_nhds.1 hT) 1 one_pos] with z hz
    rwa [dist_eq_norm] at hz
  have ev4 : ∀ᶠ z in F, infDist z (D ω)ᶜ < (1 / 2 : ℝ) ^ N :=
    eventually_infDist_compl_lt hcω hM hF hT (by positivity)
  filter_upwards [ev1, ev2, ev3, ev4] with z hzD hz2 hz3 hz4
  set d := infDist z (D ω)ᶜ with hddef
  have hd0 : 0 < d := infDist_compl_pos hcω.isOpen_D hDne' hzD
  have hdO : infDist z (H \ relClosureH (A₂ ω))ᶜ = d := by rw [hrc, ← hcω.infDist_eq hzD]
  obtain ⟨n, hnN, hn1, hn2⟩ := GFF.exists_layer_index (D := H \ relClosureH (A₂ ω)) (x := z)
    (hdO ▸ hd0) (hdO ▸ hz4)
  have hball : closedBall z ((1 / 2 : ℝ) ^ (n + 2)) ⊆
      {w | (ω, w) ∈ Lset D A₂ A G (qc : ℝ) R i₀ k Rp n} := by
    intro w hw
    refine ⟨⟨hcl, href⟩, ?_, ?_⟩
    · have hRp1 : (1 : ℝ) ≤ Rp := by rw [hRpdef]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) ⌈|y| + 2 + M⌉₊]
      have hnR : (1 / 2 : ℝ) ^ (n + 2) ≤ Rp := (pow_le_one₀ (by norm_num) (by norm_num)).trans hRp1
      have hzc : dist z 0 < 2 * Rp := by
        rw [dist_zero_right]
        have h1 := hM z hzD
        have h2 : ‖G ω z‖ ≤ |y| + 1 := by
          have := norm_le_norm_add_norm_sub' (G ω z) (y : ℂ)
          rw [Complex.norm_real, Real.norm_eq_abs] at this
          linarith
        have h3 : ‖z‖ ≤ ‖G ω z‖ + ‖G ω z - z‖ := by
          have := norm_sub_le (G ω z) (G ω z - z)
          rwa [sub_sub_cancel] at this
        have h4 : |y| + 2 + M ≤ (⌈|y| + 2 + M⌉₊ : ℝ) := Nat.le_ceil _
        have h5 : (Rp : ℝ) = (⌈|y| + 2 + M⌉₊ : ℝ) + 1 := by rw [hRpdef]; push_cast; ring
        linarith
      exact GFF.closedBall_subset_layerSet hnR hzc hn1 hn2 hw
    · have hzε : ball z (3 / 4 * d) ⊆ D ω := hcω.ball_three_quarters_subset hzD
      have hIm : (G ω z).im < R / 16 := by
        have := Complex.abs_im_le_norm (G ω z - y)
        simp only [sub_im, ofReal_im, sub_zero] at this
        linarith [le_abs_self (G ω z).im]
      have hKz : ∀ ζ ∈ ball z (3 / 4 * d), G ω ζ ∈ closedBall ((qc : ℝ) : ℂ) (2 * R) := by
        intro ζ hζ
        have h1 := hcω.norm_sub_lt hzD (mem_ball.1 hζ)
        rw [mem_closedBall, dist_eq_norm]
        calc ‖G ω ζ - ((qc : ℝ) : ℂ)‖ ≤ ‖G ω ζ - G ω z‖ + ‖G ω z - (y : ℂ)‖ + ‖(y : ℂ) - ((qc : ℝ) : ℂ)‖ := by
              have := norm_sub_le_norm_sub_add_norm_sub (G ω ζ) (G ω z) ((qc : ℝ) : ℂ)
              have := norm_sub_le_norm_sub_add_norm_sub (G ω z) (y : ℂ) ((qc : ℝ) : ℂ)
              linarith
          _ ≤ 2 * R := by rw [norm_sub_rev] at hcy; linarith
      have hw' : w ∈ ball z (3 / 4 * d) := by
        rw [mem_ball]
        have h1 : dist w z ≤ (1 / 2 : ℝ) ^ (n + 2) := mem_closedBall.1 hw
        have h2 : (1 / 2 : ℝ) ^ (n + 2) = (1 / 2 : ℝ) ^ (n + 1) / 2 := by rw [pow_succ]; ring
        rw [hdO] at hn1
        linarith
      obtain ⟨i, j, hwq, hv⟩ := hcω.exists_verBall hGi hzε hKz hw'
      refine mem_iUnion.2 ⟨i, mem_iUnion.2 ⟨j, ⟨?_, hwq⟩⟩⟩
      show IsVerBall (D ω) (H \ relClosureH (A₂ ω)) (chartInd D G ω) _ i j
      rw [hrc]; exact hv
  have key := hN n hnN z hball
  rw [Real.dist_eq, sub_zero]
  exact key.trans hmm

end Main

end RetZone

end RLC

end InteractingSLE
