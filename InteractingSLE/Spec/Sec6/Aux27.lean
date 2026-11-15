/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.Growth
import InteractingSLE.GFF.LocalSets.GermVersion
import InteractingSLE.GFF.LocalSets.SubdomainLaw
import SupercriticalConformalCovariance.GM24.TVReduce

/-!
# Aux. lemma 27: subpower growth of a local-set conditional harmonic function

Packet PROVE-SEC6-A3 (specification §6.1, `source/spec/p145-192.md`, `#aux-27`, pp. 160–162).

**Aux. lemma 27.** Let `h = h⁰ + F` be a GFF in `D` with deterministic harmonic mean `F`, `A` a
local set, `h = h_A + h^A` the local-set decomposition (`h_A` harmonic in `D ∖ A`). Let `K` be bounded
with `F` bounded on `D ∩ K⁺` for an open neighbourhood `K⁺` of `K̄`. Then for every `ε > 0`, almost
surely there is a finite `C` with `|h_A(z)| ≤ C (1 + dist(z, A ∪ ∂D)^{−ε})` for `z ∈ K ∩ (D ∖ A)`.

## Formalization

* `D = ℍ` (local sets of the project live on `ℍ`, ruling R19 (5); subdomains are pulled back,
  ruling R34), so `∂D = ℝ`; `h` is a measurable random distribution on `ℍ` with `h − F` a
  zero-boundary GFF, `F` harmonic on `ℍ`.
* The local-set mean `h_A` is a random distribution `h₁` with `h₁(φ) = E[h(φ) | 𝒜]` almost surely
  for every test function (the conditional mean given the local-set information `𝒜`, which is what
  the decomposition gives: `E[h^A(φ) | 𝒜] = 0`) and harmonic on `ℍ ∖ A` (`IsHarmonicDistOn`); the
  conclusion holds for every harmonic representative `v` of `h₁` on `ℍ ∖ A`.
* The bound on `F` is assumed on `K ∩ ℍ` only (the source's bound on `ℍ ∩ K⁺` implies it).
* The conclusion is stronger than the source's: one null set serves all `ε > 0` (the source obtains
  this from rational `ε`).

## Proof

The source's proof (Gaussian moments of mollified fields, a scaled Sobolev inequality on `δ`-squares,
Borel–Cantelli along `δ = 2^{-n}`) proves a power bound. The project already has the stronger
logarithmic bound of Wang–Wu's Lemma 4.6 (`InteractingSLE.WangWu`, packet PROVE-WW-B2: a maximal
estimate for mollified GFF values and conditional Jensen), which is reused here:
* subtract the mean: `h⁰ = h − F` and `h₁⁰ = h₁ − F` (as distributions) satisfy
  `h₁⁰(φ) = E[h⁰(φ) | 𝒜]`, and `v − F` represents `h₁⁰`;
* the window bound `WangWu.ae_window_bound_of_condMean` and the deterministic step
  `WangWu.abs_le_log_of_window_bound`, applied on `(ℍ ∖ A) ∩ B(z, 1)`, give
  `|v(z) − F(z)| ≤ C' (1 + log(1/min(d, 1)))` with `d = dist(z, A ∪ ℝ)`;
* `log(1/m) ≤ m^{−ε}/ε` and `|F| ≤ M_F` on `K`.

## Main results

* `aux27_ae_forall`: Aux. lemma 27 (all `ε` on one null set);
* `aux27`: the source's form (`∀ ε > 0`, almost surely);
* `aux27_of_isLocalSetMean`: for a local set (`IsLocalSet`) of a zero-boundary GFF and its local-set
  mean in the sense of Lemma 3.6 (iii) (`IsLocalSetMean`, germ σ-algebra), through the germ version
  of PROVE-LS-B2 (`exists_germVersion`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal Real

namespace InteractingSLE.Sec6

open QuantumZipper (H)
open LQGMetric (DistOn TestOn)
open SupercriticalConformalCovariance.GM24 (smoothDist smoothDist_apply)

/-- The distance to `A ∪ ℝ` is at most the distance to the complement of `ℍ ∖ A` (for `z ∈ ℍ`). -/
theorem infDist_union_real_le {A : Set ℂ} {z : ℂ} (hz : 0 < z.im) :
    infDist z (A ∪ {w : ℂ | w.im = 0}) ≤ infDist z (H \ A)ᶜ := by
  have hne : ((H \ A)ᶜ).Nonempty := ⟨0, fun h0 => by simp [QuantumZipper.H] at h0⟩
  refine (le_infDist hne).2 fun w hw => ?_
  rw [compl_sdiff, mem_union] at hw
  rcases hw.symm with hw | hw
  · -- `w` below the real line: the real point under `z` is closer
    have hwim : w.im ≤ 0 := not_lt.1 hw
    have hr : ((z.re : ℂ)) ∈ A ∪ {w : ℂ | w.im = 0} := Or.inr (by simp)
    refine (infDist_le_dist_of_mem hr).trans ?_
    rw [dist_eq_norm, dist_eq_norm]
    have h1 : ‖z - (z.re : ℂ)‖ = z.im := by
      have : z - (z.re : ℂ) = (z.im : ℂ) * I := by
        apply Complex.ext <;> simp
      rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hz, Complex.norm_I,
        mul_one]
    rw [h1]
    have h2 := Complex.abs_im_le_norm (z - w)
    rw [Complex.sub_im] at h2
    linarith [le_abs_self (z.im - w.im)]
  · exact infDist_le_dist_of_mem (Or.inl hw)

/-- `log(1/m) ≤ m^{−ε}/ε` for `0 < m`. -/
theorem log_inv_le_rpow_neg_div {m ε : ℝ} (hm : 0 < m) (hε : 0 < ε) :
    Real.log (1 / m) ≤ m ^ (-ε) / ε := by
  have := Real.log_le_rpow_div (x := 1 / m) (by positivity) hε
  rw [one_div, Real.inv_rpow hm.le] at this
  rw [one_div, Real.rpow_neg hm.le]
  exact this

/-- **Aux. lemma 27** (all `ε > 0` on one null set). Let `h` be a measurable random distribution on
`ℍ` with `h − F` a zero-boundary GFF, `F` harmonic on `ℍ`; let `h₁` be the conditional mean of `h`
given a σ-algebra `𝒜` (the local-set information of `A`), harmonic on `ℍ ∖ A` (relatively closed `A`).
Let `K` be bounded with `|F| ≤ M_F` on `K ∩ ℍ`. Then almost surely, for every `ε > 0` there is a
finite `C` such that every harmonic representative `v` of `h₁` on `ℍ ∖ A` satisfies
`|v(z)| ≤ C (1 + dist(z, A ∪ ℝ)^{−ε})` for all `z ∈ K ∩ (ℍ ∖ A)`. -/
theorem aux27_ae_forall {Ω : Type*} {𝒜 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} (hhm : Measurable h)
    {F : ℂ → ℝ} (hF : InnerProductSpace.HarmonicOnNhd F H)
    (hh : LQGMetric.IsZBGFFProcess upperHalfPlaneOpens (fun φ ω => h ω φ - ∫ x, F x * φ x) P)
    (h𝒜 : 𝒜 ≤ mΩ) {A : Ω → Set ℂ} {h₁ : Ω → DistOn upperHalfPlaneOpens}
    (hmean : ∀ φ : TestOn upperHalfPlaneOpens, (fun ω => h₁ ω φ) =ᵐ[P] P[fun ω => h ω φ | 𝒜])
    (hopen : ∀ᵐ ω ∂P, IsOpen (H \ A ω)) {K : Set ℂ} (hK : Bornology.IsBounded K) {MF : ℝ}
    (hFK : ∀ z ∈ K ∩ H, |F z| ≤ MF) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ v : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd v (H \ A ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω → h₁ ω φ = ∫ x, v x * φ x) →
      ∀ z ∈ K ∩ (H \ A ω),
        |v z| ≤ C * (1 + infDist z (A ω ∪ {w : ℂ | w.im = 0}) ^ (-ε)) := by
  let _ : MeasurableSpace Ω := mΩ
  have hFc : ContinuousOn F H := fun z hz => (hF z hz).1.continuousAt.continuousWithinAt
  have hFc' : ContinuousOn F (upperHalfPlaneOpens : Set ℂ) := hFc
  -- the centred field and the centred conditional mean
  set Fd : DistOn upperHalfPlaneOpens := smoothDist upperHalfPlaneOpens F with hFd
  have hFd_apply : ∀ φ : TestOn upperHalfPlaneOpens, Fd φ = ∫ x, F x * φ x := fun φ => by
    rw [hFd, smoothDist_apply hFc']
    congr 1; funext x; ring
  set h0 : Ω → DistOn upperHalfPlaneOpens := fun ω => h ω - Fd with hh0
  set g0 : Ω → DistOn upperHalfPlaneOpens := fun ω => h₁ ω - Fd with hg0
  have hh0m : Measurable h0 := by
    refine LQGMetric.measurable_distOn_iff.2 fun φ => ?_
    have : (fun ω => h0 ω φ) = fun ω => h ω φ - Fd φ := by
      funext ω; simp [hh0]
    rw [this]
    exact (LQGMetric.measurable_distOn_apply φ |>.comp hhm).sub_const _
  have hh0z : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h0 P := by
    refine ⟨hh0m, ?_⟩
    have e : (fun φ ω => h0 ω φ) = fun φ ω => h ω φ - ∫ x, F x * φ x := by
      funext φ ω; simp [hh0, hFd_apply]
    rw [e]; exact hh
  have hmean0 : ∀ φ : TestOn upperHalfPlaneOpens,
      (fun ω => g0 ω φ) =ᵐ[P] P[fun ω => h0 ω φ | 𝒜] := by
    intro φ
    set c : ℝ := Fd φ
    have hXi : Integrable (fun ω => h ω φ) P := by
      have h1 : Integrable (fun ω => h ω φ - ∫ x, F x * φ x) P :=
        (hh.gaussian.hasGaussianLaw_eval φ).integrable
      refine (h1.add (integrable_const (∫ x, F x * φ x))).congr
        (Eventually.of_forall fun ω => ?_)
      simp
    have hsub := condExp_sub (m := 𝒜) hXi (integrable_const c)
    have hconst : P[fun _ : Ω => c | 𝒜] = fun _ => c := condExp_const h𝒜 c
    have e : (fun ω => h0 ω φ) = (fun ω => h ω φ) - fun _ => c := by
      funext ω; simp [hh0, c]
    rw [e]
    filter_upwards [hmean φ, hsub] with ω h1 h2
    rw [h2, Pi.sub_apply, hconst]
    simp [hg0, c, h1]
  -- the bound on `K`
  obtain ⟨R, hR⟩ := hK.subset_closedBall 0
  set R' : ℝ := |R| + 1 with hR'
  filter_upwards [WangWu.ae_window_bound_of_condMean hh0z hmean0 (R := R')
      (by rw [hR']; positivity),
    hopen] with ω hω hUo ε hε
  set Kω : ℝ := P[fun ω => (WangWu.windowSup h0 R' ω).toReal | 𝒜] ω with hKω
  refine ⟨MF + 4 * (|Kω| + |(0 : ℝ)|) * (2 + 2 * (1 / ε)), fun v hv hrep z hz => ?_⟩
  obtain ⟨hzK, hzU⟩ := hz
  have hzH : z ∈ H := hzU.1
  have hzim : 0 < z.im := hzH
  set U := H \ A ω with hU
  -- the centred representative on `U ∩ B(z, 1)`
  set U' := U ∩ ball z 1 with hU'
  have hU'o : IsOpen U' := hUo.inter isOpen_ball
  have hU'H : U' ⊆ H := fun w hw => hw.1.1
  have hzU' : z ∈ U' := ⟨hzU, mem_ball_self one_pos⟩
  have hv0 : InnerProductSpace.HarmonicOnNhd (fun w => v w - F w) U' :=
    fun w hw => (hv w hw.1).sub (hF w hw.1.1)
  have hrep0 : ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ U' →
      g0 ω φ = ∫ x, (v x - F x) * φ x := by
    intro φ hφ
    have hφU : tsupport φ ⊆ U := hφ.trans inter_subset_left
    have hvi : Integrable (fun x => v x * φ x) := by
      refine Continuous.integrable_of_hasCompactSupport ?_ (φ.hasCompactSupport.mul_left)
      refine continuous_of_tsupport fun x hx => ?_
      have hxU : x ∈ U := hφU ((tsupport_mul_subset_right) hx)
      exact (hv x hxU).1.continuousAt.mul φ.continuous.continuousAt
    have hFi : Integrable (fun x => F x * φ x) := by
      refine Continuous.integrable_of_hasCompactSupport ?_ (φ.hasCompactSupport.mul_left)
      refine continuous_of_tsupport fun x hx => ?_
      have hxU : x ∈ U := hφU ((tsupport_mul_subset_right) hx)
      exact (hF x hxU.1).1.continuousAt.mul φ.continuous.continuousAt
    have e : (fun x => (v x - F x) * φ x) = fun x => v x * φ x - F x * φ x := by
      funext x; ring
    rw [e, integral_sub hvi hFi, ← hrep φ hφU, ← hFd_apply]
    simp [hg0]
  have hzR : ‖z‖ ≤ R := by
    have := hR hzK
    rwa [mem_closedBall, dist_zero_right] at this
  -- distances
  set d := infDist z (A ω ∪ {w : ℂ | w.im = 0}) with hd
  have hdpos : 0 < d := by
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hUo z hzU
    have hne : (A ω ∪ {w : ℂ | w.im = 0}).Nonempty := ⟨0, Or.inr (by simp)⟩
    refine lt_of_lt_of_le hr ((le_infDist hne).2 fun w hw => ?_)
    by_contra hlt
    rw [not_le, dist_comm] at hlt
    have hwU := hball (mem_ball.2 hlt)
    rcases hw with hw | hw
    · exact hwU.2 hw
    · have h1 : (0 : ℝ) < w.im := hwU.1
      have h2 : w.im = 0 := hw
      linarith
  set d' := infDist z U'ᶜ with hd'
  have hd'1 : d' ≤ 1 := by
    have hw : z + 1 ∈ U'ᶜ := fun h => by
      have := h.2
      rw [mem_ball, dist_eq_norm] at this
      simp at this
    calc d' ≤ dist z (z + 1) := infDist_le_dist_of_mem hw
      _ = 1 := by rw [dist_eq_norm]; simp
  have hd'ge : min d 1 ≤ d' := by
    have hne : (U'ᶜ).Nonempty := ⟨z + 1, fun h => by
      have := h.2
      rw [mem_ball, dist_eq_norm] at this
      simp at this⟩
    refine (le_infDist hne).2 fun w hw => ?_
    rw [hU', compl_inter, mem_union] at hw
    rcases hw with hw | hw
    · exact (min_le_left _ _).trans ((infDist_union_real_le hzim).trans
        (infDist_le_dist_of_mem hw))
    · refine (min_le_right _ _).trans ?_
      rw [mem_compl_iff, mem_ball, not_lt, dist_comm] at hw
      exact hw
  have hm0 : 0 < min d 1 := lt_min hdpos one_pos
  -- the logarithmic bound for the centred representative
  have hlog := WangWu.abs_le_log_of_window_bound (R := R) hU'o hU'H (T := fun φ => g0 ω φ)
    (K := Kω) (K' := 0) hω hv0 hrep0 hzU' hzR hd'1
  have hlog' : Real.log (1 / d') ≤ 1 + 1 / ε * (1 + d ^ (-ε)) := by
    have h1 : Real.log (1 / d') ≤ Real.log (1 / min d 1) := by
      refine Real.log_le_log (one_div_pos.2 (hm0.trans_le hd'ge)) ?_
      exact one_div_le_one_div_of_le hm0 hd'ge
    have h2 := log_inv_le_rpow_neg_div hm0 hε
    have h3 : min d 1 ^ (-ε) ≤ 1 + d ^ (-ε) := by
      rcases le_total d 1 with hd1 | hd1
      · rw [min_eq_left hd1]; linarith [Real.rpow_nonneg hdpos.le (-ε)]
      · rw [min_eq_right hd1, Real.one_rpow]
        linarith [Real.rpow_nonneg hdpos.le (-ε)]
    have h4 : min d 1 ^ (-ε) / ε ≤ 1 / ε * (1 + d ^ (-ε)) := by
      rw [div_eq_inv_mul, one_div]
      exact mul_le_mul_of_nonneg_left h3 (inv_nonneg.2 hε.le)
    linarith
  have hF0 := hFK z ⟨hzK, hzH⟩
  have hKpos : 0 ≤ 4 * (|Kω| + |(0 : ℝ)|) := by positivity
  have hdε : 0 ≤ d ^ (-ε) := Real.rpow_nonneg hdpos.le _
  have hMF : 0 ≤ MF := (abs_nonneg _).trans hF0
  calc |v z| = |(v z - F z) + F z| := by ring_nf
    _ ≤ |v z - F z| + |F z| := abs_add_le _ _
    _ ≤ 4 * (|Kω| + |(0 : ℝ)|) * (1 + Real.log (1 / d')) + MF := add_le_add hlog hF0
    _ ≤ 4 * (|Kω| + |(0 : ℝ)|) * (1 + (1 + 1 / ε * (1 + d ^ (-ε)))) + MF := by
        gcongr
    _ ≤ (MF + 4 * (|Kω| + |(0 : ℝ)|) * (2 + 2 * (1 / ε))) * (1 + d ^ (-ε)) := by
        have hε' : 0 < 1 / ε := by positivity
        nlinarith [mul_nonneg hKpos hdε, mul_nonneg hMF hdε, mul_nonneg (mul_nonneg hKpos hdε) hε'.le,
          mul_nonneg hKpos hε'.le]

/-- **Aux. lemma 27** (the source's form): for every `ε > 0`, almost surely there is a finite `C` with
`|h_A(z)| ≤ C (1 + dist(z, A ∪ ∂ℍ)^{−ε})` for `z ∈ K ∩ (ℍ ∖ A)`, for every harmonic representative
`h_A` of the local-set mean on `ℍ ∖ A`. -/
theorem aux27 {Ω : Type*} {𝒜 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} (hhm : Measurable h)
    {F : ℂ → ℝ} (hF : InnerProductSpace.HarmonicOnNhd F H)
    (hh : LQGMetric.IsZBGFFProcess upperHalfPlaneOpens (fun φ ω => h ω φ - ∫ x, F x * φ x) P)
    (h𝒜 : 𝒜 ≤ mΩ) {A : Ω → Set ℂ} {h₁ : Ω → DistOn upperHalfPlaneOpens}
    (hmean : ∀ φ : TestOn upperHalfPlaneOpens, (fun ω => h₁ ω φ) =ᵐ[P] P[fun ω => h ω φ | 𝒜])
    (hopen : ∀ᵐ ω ∂P, IsOpen (H \ A ω)) {K : Set ℂ} (hK : Bornology.IsBounded K)
    {Kp : Set ℂ} (hKp : closure K ⊆ Kp) {MF : ℝ} (hFK : ∀ z ∈ H ∩ Kp, |F z| ≤ MF)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂P, ∃ C : ℝ, ∀ v : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd v (H \ A ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω → h₁ ω φ = ∫ x, v x * φ x) →
      ∀ z ∈ K ∩ (H \ A ω),
        |v z| ≤ C * (1 + infDist z (A ω ∪ {w : ℂ | w.im = 0}) ^ (-ε)) := by
  filter_upwards [aux27_ae_forall hhm hF hh h𝒜 hmean hopen hK
    (fun z hz => hFK z ⟨hz.2, hKp (subset_closure hz.1)⟩)] with ω hω
  exact hω ε hε

open LocalSets in
/-- **Aux. lemma 27 for the project's local-set mean.** For a zero-boundary GFF `h` on `ℍ`, a local set
`A` (`IsLocalSet`) and its local-set mean `g` (`IsLocalSetMean A h P g`, Lemma 3.6 (iii)), and a bounded
`K`: almost surely, for every `ε > 0` there is a finite `C` such that every harmonic representative
`v` of `g` on `ℍ ∖ A` satisfies `|v(z)| ≤ C (1 + dist(z, A ∪ ℝ)^{−ε})` on `K ∩ (ℍ ∖ A)`. -/
theorem aux27_of_isLocalSetMean {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h P) {A : Ω → Set ℂ}
    (hA : Measurable[mΩ, hittingSigma] A) (hloc : IsLocalSet A h P)
    {g : Ω → DistOn upperHalfPlaneOpens} (hg : IsLocalSetMean A h P g) {K : Set ℂ}
    (hK : Bornology.IsBounded K) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ v : ℂ → ℝ,
      InnerProductSpace.HarmonicOnNhd v (H \ A ω) →
      (∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω → g ω φ = ∫ x, v x * φ x) →
      ∀ z ∈ K ∩ (H \ A ω),
        |v z| ≤ C * (1 + infDist z (A ω ∪ {w : ℂ | w.im = 0}) ^ (-ε)) := by
  have hhm := hh.measurable
  have hAc : ∀ᵐ ω ∂P, A ω ⊆ H ∧ IsOpen (H \ A ω) := hloc.2.1
  have hav : IsAvoidanceLocal A h P := ((isLocalSet_tfae hh hA hAc).out 4 1).1 hloc
  obtain ⟨M, h₁, hM, hMlim, hh₁m, hh₁⟩ := exists_germVersion hh hA hav hAc
  have hharm := ae_isHarmonicDistOn_germVersion hh hA hav hAc hM hMlim hh₁
  have hg₁ : IsLocalSetMean A h P h₁ :=
    ⟨hh₁m, hharm, isCondZeroBoundaryGFF_germVersion hh hA hAc hM hh₁m hh₁⟩
  have hmean : ∀ φ : TestOn upperHalfPlaneOpens,
      (fun ω => h₁ ω φ) =ᵐ[P] P[fun ω => h ω φ | germSigma A h] :=
    fun φ => (hh₁ φ).trans (hM φ).2.1
  -- `g` and `h₁` agree on `ℍ ∖ A`
  have hagree : ∀ᵐ ω ∂P, ∀ φ : TestOn upperHalfPlaneOpens, tsupport φ ⊆ H \ A ω →
      g ω φ = h₁ ω φ :=
    ae_forall_apply_eq_of_bump (hAc.mono fun ω hω => ⟨hω.2, sdiff_subset⟩) hg.2.1 hharm
      fun x δ hδ hB => (IsLocalSetMean.ae_apply_eq hA hhm hg hg₁ _).mono fun ω hω _ => hω
  -- the zero-mean form of the hypothesis of `aux27_ae_forall`
  have hh' : LQGMetric.IsZBGFFProcess upperHalfPlaneOpens
      (fun φ ω => h ω φ - ∫ x, (0 : ℂ → ℝ) x * φ x) P := by
    have e : (fun φ ω => h ω φ - ∫ x, (0 : ℂ → ℝ) x * φ x) = fun φ ω => h ω φ := by
      funext φ ω; simp
    rw [e]; exact hh.process
  have hmain := aux27_ae_forall hhm (F := 0) (fun z _ => InnerProductSpace.harmonicAt_const 0) hh'
    (germSigma_le hA hhm) hmean (hAc.mono fun ω hω => hω.2) hK (MF := 0)
    (fun z _ => by simp)
  filter_upwards [hmain, hagree] with ω hω hag ε hε
  obtain ⟨C, hC⟩ := hω ε hε
  exact ⟨C, fun v hv hrep z hz => hC v hv (fun φ hφ => (hag φ hφ).symm.trans (hrep φ hφ)) z hz⟩

end InteractingSLE.Sec6
