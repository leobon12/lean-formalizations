/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.GB7aAbove4Cut
import InteractingSLE.Spec.Supplement.GB7aCmpPath
import InteractingSLE.Spec.Supplement.GB6LifeBase

/-!
# GB7a's pathwise half above `κ = 4`: the chart at a restart time

Packet PROVE-CFBARRIER2. PROVE-GB7A3's chart lemmas (`GB7aCmpChart.lean`) assume that the trace after the restart time
`q` stays off its past (`InjOn`, true for `κ ≤ 4`). Above `4` the trace after `q` may touch the past hull; in the chart
at `q` it then touches `ℝ` at images of the past hull. This file proves the chart facts without that hypothesis:

* `mem_closure_compl_fwdHull`: a later trace point lies in the closure of `ℍ \ K_q`;
* `exists_isForwardSol_at_restart_of_notMem`: the real limit point `y` of the trace at `T` is alive at `q` when it
  is not on the prefix `η([0, q])`;
* `tendsto_chart_of_restart`: the chart trace at `q` tends to the real flow `V` of `y`;
* `re_lt_of_chart_real`, `lt_re_of_chart_real`: a real point of the chart trace lies strictly between the alive real
  points on either side of `0` (a real point alive at a time is not the tip at that time);
* `exists_seedCut`: cut parameters with an asymmetric seed core containing every real point of the chart trace;
* `exists_energy_bound_of_restart_above4`: **the energy bound after the restart** (Aux. lemma 61 in the chart at `q`)
  with an asymmetric seed core.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric Finset
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Sec5.GB7aAbove4

open QuantumZipper (H Hbar fwdMap fwdHull fwdMapInv IsForwardSol)
open QuantumZipper.RS (shiftDrive)
open GB7a

section Restart

variable {U : ℝ → ℝ} {T : ℝ} {η : ℝ → ℂ} {q : ℝ}

/-- **A later trace point lies in the closure of the complement of an earlier hull.** -/
theorem mem_closure_compl_fwdHull (hη : IsLoewnerTraceLT U T η) (hU : Continuous U) (hU0 : U 0 = 0)
    (hq : 0 ≤ q) {s : ℝ} (hqs : q ≤ s) (hsT : s < T) : η s ∈ closure (H \ fwdHull U q) := by
  have hs0 : 0 ≤ s := hq.trans hqs
  have hlim := hη.tendsto_fwdMapInv_mul_I hU hU0 hs0 hsT
  refine mem_closure_of_tendsto hlim ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  have h1 : fwdMapInv U s (y * Complex.I) ∈ H \ fwdHull U s := by
    rw [← QuantumZipper.RS.image_fwdMapInv_H hU hU0 hs0]
    exact mem_image_of_mem _ (QuantumZipper.RS.mul_I_mem_H hy)
  exact ⟨h1.1, fun h => h1.2 (QuantumZipper.fwdHull_mono.1 hqs h)⟩

/-- **The real limit point is alive at the restart time** when it is not on the prefix. -/
theorem exists_isForwardSol_at_restart_of_notMem (hη : IsLoewnerTraceLT U T η) (hU : Continuous U)
    (hU0 : U 0 = 0) (hq : 0 ≤ q) (hqT : q < T) {y : ℝ} (hy0 : y ≠ 0)
    (hlim : Tendsto η (𝓝[<] T) (𝓝 (y : ℂ))) (hyq : (y : ℂ) ∉ η '' Icc 0 q) :
    ∃ v, IsForwardSol U (y : ℂ) q v := by
  refine exists_isForwardSol_of_mem_closure hU hU0 hη hq hqT hy0 hyq ?_
  refine isClosed_closure.mem_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsLT hqT] with s hs
  exact mem_closure_compl_fwdHull hη hU hU0 hq hs.1.le hs.2

/-- **The chart trace at the restart time tends to the real flow of the limit point.** If the trace is in `ℍ` on
`(q, T)` and tends to `y > 0`, alive at `q` and not on the prefix, the shifted tips `γ_q(u)` tend to `Re v(q)` as
`u ↑ T − q`. -/
theorem tendsto_chart_of_restart (hη : IsLoewnerTraceLT U T η) (hU : Continuous U) (hU0 : U 0 = 0)
    (hq : 0 ≤ q) (hqT : q < T) (hH : ∀ s ∈ Ioo q T, η s ∈ H) {y : ℝ}
    (hlim : Tendsto η (𝓝[<] T) (𝓝 (y : ℂ))) (hyq : (y : ℂ) ∉ η '' Icc 0 q) {v : ℝ → ℂ}
    (hv : IsForwardSol U (y : ℂ) q v) :
    Tendsto (loewnerTip (shiftDrive U q)) (𝓝[<] (T - q)) (𝓝 ((v q).re : ℂ)) := by
  set V := (v q).re with hVdef
  have hvq : v q = (V : ℂ) := Complex.ext (by simp [hVdef])
    (by rw [Complex.ofReal_im]; exact im_eq_zero_of_isForwardSol_real hU hv ⟨hq, le_rfl⟩)
  set τ := T - q with hτ
  have hτ0 : 0 < τ := sub_pos.2 hqT
  have hqτ : q + τ = T := by rw [hτ]; ring
  have hAc : IsClosed (η '' Icc 0 q) := (hη.isCompact_image hqT).isClosed
  obtain ⟨r, hr, hrA⟩ : ∃ r > 0, ball (y : ℂ) r ⊆ (η '' Icc 0 q)ᶜ :=
    Metric.isOpen_iff.1 hAc.isOpen_compl _ hyq
  have h1 : Tendsto (fun u => q + u) (𝓝[<] τ) (𝓝[<] T) := by
    have hc : Tendsto (fun u => q + u) (𝓝 τ) (𝓝 T) := by
      have : Tendsto (fun u : ℝ => q + u) (𝓝 τ) (𝓝 (q + τ)) :=
        ((continuous_const (y := q)).add continuous_id).tendsto τ
      rwa [hqτ] at this
    refine tendsto_nhdsWithin_iff.2 ⟨hc.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with u hu
    show q + u < T
    have : u < τ := hu
    linarith
  have h2 : Tendsto (fun u => η (q + u)) (𝓝[<] τ) (𝓝[H] (y : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hlim.comp h1, ?_⟩
    filter_upwards [Ioo_mem_nhdsLT hτ0] with u hu
    exact hH (q + u) ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have h3 := (tendsto_fwdMap_of_isForwardSol_real hU hU0 hq hv).comp h2
  rw [hvq] at h3
  refine h3.congr' ?_
  have hball : ∀ᶠ u in 𝓝[<] τ, η (q + u) ∈ ball (y : ℂ) r := (hlim.comp h1) (ball_mem_nhds _ hr)
  filter_upwards [Ioo_mem_nhdsLT hτ0, hball] with u hu hub
  have hquT : q + u < T := by linarith [hu.2]
  exact (hη.chart_of_mem_H hU hU0 hq hu.1.le hquT (hH (q + u) ⟨by linarith [hu.1], hquT⟩)
    (hrA hub)).2.1

end Restart

/-! ### Real points of a trace -/

section Real

variable {U : ℝ → ℝ} {τ : ℝ} {γ : ℝ → ℂ}

/-- **A real point alive at time `u` is not the tip at `u`.** -/
theorem trace_ne_of_isForwardSol (hS : IsLoewnerTraceLT U τ γ) (hU : Continuous U) (hU0 : U 0 = 0) {u : ℝ}
    (hu : u ∈ Ico 0 τ) {x : ℝ} {v : ℝ → ℂ} (hv : IsForwardSol U (x : ℂ) u v) : γ u ≠ x := by
  intro he
  have htip := hS.tendsto_fwdMapInv_tip hU hU0 hu.1 hu.2
  rw [he] at htip
  exact Supp8.GB6.not_isForwardSol_of_tip hU hU0 hu.1 htip hv

/-- **A real point of the trace lies left of every alive positive real point.** -/
theorem re_lt_of_chart_real (hS : IsLoewnerTraceLT U τ γ) (hU : Continuous U) (hU0 : U 0 = 0) {u : ℝ}
    (hu : u ∈ Ico 0 τ) (him : (γ u).im = 0) {x : ℝ} (hx : 0 < x) {v : ℝ → ℂ}
    (hv : IsForwardSol U (x : ℂ) u v) : (γ u).re < x := by
  by_contra hle
  push Not at hle
  have hγ : γ u = ((γ u).re : ℂ) := Complex.ext (by simp) (by simp [him])
  rcases hle.lt_or_eq with hlt | heq
  · obtain ⟨v', hv'⟩ := QuantumZipper.RS.exists_isForwardSol_of_lt hU hu.1 (by rw [hU0]; exact hx) hlt hv
    exact trace_ne_of_isForwardSol hS hU hU0 hu hv' hγ
  · rw [← heq] at hγ
    exact trace_ne_of_isForwardSol hS hU hU0 hu hv hγ

/-- **A real point of the trace lies right of every alive negative real point.** -/
theorem lt_re_of_chart_real (hS : IsLoewnerTraceLT U τ γ) (hU : Continuous U) (hU0 : U 0 = 0) {u : ℝ}
    (hu : u ∈ Ico 0 τ) (him : (γ u).im = 0) {x : ℝ} (hx : x < 0) {v : ℝ → ℂ}
    (hv : IsForwardSol U (x : ℂ) u v) : x < (γ u).re := by
  by_contra hle
  push Not at hle
  have hγ : γ u = ((γ u).re : ℂ) := Complex.ext (by simp) (by simp [him])
  rcases hle.lt_or_eq with hlt | heq
  · obtain ⟨v', hv'⟩ := Aux25.exists_isForwardSol_of_lt_left hU hu.1 (by rw [hU0]; exact hx) hlt hv
    exact trace_ne_of_isForwardSol hS hU hU0 hu hv' hγ
  · rw [heq] at hγ
    exact trace_ne_of_isForwardSol hS hU hU0 hu hv hγ

end Real

/-! ### Cut parameters with an asymmetric seed core -/

/-- **Cut parameters for a chart trace with real points.** Let `γ` be continuous on `[0, τ)` with `γ 0 = 0`, in `ℍ̄`,
with `γ(u) → V` as `u ↑ τ`, and let finitely many real marks `p` be off `0` and `V`, one of them in `(0, V)`. If every
real point of `γ` lies strictly right of the negative marks and strictly left of the positive ones, there are valid
parameters whose seed core contains every real point of `γ` (with margin `2μ`) and avoids the marks, whose target core
contains `V` and separates the marks below `V` from those above, and whose inner buffer contains `γ([0, τ))`. -/
theorem exists_seedCut {τ V : ℝ} (hτ : 0 < τ) {γ : ℝ → ℂ} (hγc : ContinuousOn γ (Ico 0 τ)) (hγ0 : γ 0 = 0)
    (hγH : ∀ u ∈ Ico 0 τ, γ u ∈ Hbar) (hγlim : Tendsto γ (𝓝[<] τ) (𝓝 (V : ℂ))) {ι : Type*} [Fintype ι]
    {p : ι → ℝ} (hp0 : ∀ j, p j ≠ 0) (hpV : ∀ j, p j ≠ V) {k : ι} (hk0 : 0 < p k) (hkV : p k < V)
    (hγR : ∀ u ∈ Ico 0 τ, (γ u).im = 0 → ∀ j, (p j < 0 → p j < (γ u).re) ∧ (0 < p j → (γ u).re < p j)) :
    ∃ P : SeedCut, P.Valid ∧ (∀ j, p j < P.l₀ - P.μ ∨ P.r₀ + P.μ < p j) ∧
      (∀ j, p j < V → p j < P.a₁ - P.μ) ∧ (∀ j, V < p j → P.b₁ + P.μ < p j) ∧ V < P.b₁ + P.μ ∧
      ∀ u ∈ Ico 0 τ, γ u ∈ seedU P ∧ ((γ u).im = 0 → (γ u).re ∈ Ioo (P.l₀ + 2 * P.μ) (P.r₀ - 2 * P.μ)) := by
  classical
  -- the separation scale `d` at the target
  obtain ⟨δ₀, hδ₀, hδ₀le⟩ := exists_pos_le_of_fintype (fun j => |p j - V|) fun j =>
    abs_pos.2 (sub_ne_zero.2 (hpV j))
  set d := min δ₀ (V - p k) with hd
  have hd0 : 0 < d := lt_min hδ₀ (by linarith)
  have hdV : d ≤ V - p k := min_le_right _ _
  have hdp : ∀ j, d ≤ |p j - V| := fun j => (min_le_left _ _).trans (hδ₀le j)
  have hV : 0 < V := hk0.trans hkV
  -- near `τ`
  obtain ⟨δ₂, hδ₂, h₂⟩ := Metric.tendsto_nhdsWithin_nhds.1 hγlim (d / 8) (by positivity)
  set τ' := max (τ - δ₂ / 2) (τ / 2) with hτ'
  have hτ'τ : τ' < τ := max_lt (by linarith) (by linarith)
  have hτ'0 : 0 < τ' := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hnear : ∀ u ∈ Ico 0 τ, τ' < u → dist (γ u) (V : ℂ) < d / 8 := fun u hu hτu => by
    refine h₂ (show u < τ from hu.2) ?_
    rw [Real.dist_eq, abs_of_neg (by linarith [hu.2])]
    linarith [le_max_left (τ - δ₂ / 2) (τ / 2)]
  have hnearRe : ∀ u ∈ Ico 0 τ, τ' < u → |(γ u).re - V| < d / 8 := fun u hu hτu => by
    have h := hnear u hu hτu
    rw [Complex.dist_eq] at h
    have := Complex.abs_re_le_norm (γ u - V)
    simp only [Complex.sub_re, Complex.ofReal_re] at this
    linarith
  have hIcc : Icc 0 τ' ⊆ Ico 0 τ := fun u hu => ⟨hu.1, hu.2.trans_lt hτ'τ⟩
  have hγc' : ContinuousOn γ (Icc 0 τ') := hγc.mono hIcc
  have hre' : ContinuousOn (fun u => (γ u).re) (Icc 0 τ') := Complex.continuous_re.comp_continuousOn hγc'
  -- the real points on `[0, τ']`
  set Z : Set ℝ := Icc 0 τ' ∩ γ ⁻¹' {z : ℂ | z.im = 0} with hZ
  have hZc : IsCompact Z := isCompact_Icc.of_isClosed_subset
    (hγc'.preimage_isClosed_of_isClosed isClosed_Icc (isClosed_eq Complex.continuous_im continuous_const))
    inter_subset_left
  have h0Z : (0 : ℝ) ∈ Z := ⟨⟨le_rfl, hτ'0.le⟩, by simp [hγ0]⟩
  obtain ⟨u₁, hu₁, hmin⟩ := hZc.exists_isMinOn ⟨0, h0Z⟩ (hre'.mono inter_subset_left)
  obtain ⟨u₂, hu₂, hmax⟩ := hZc.exists_isMaxOn ⟨0, h0Z⟩ (hre'.mono inter_subset_left)
  set α := (γ u₁).re with hα
  set β := (γ u₂).re with hβ
  have hα0 : α ≤ 0 := by have := hmin h0Z; simpa [hγ0] using this
  have hβ0 : 0 ≤ β := by have := hmax h0Z; simpa [hγ0] using this
  have hZab : ∀ u ∈ Z, (γ u).re ∈ Icc α β := fun u hu => ⟨hmin hu, hmax hu⟩
  have hαR := hγR u₁ (hIcc hu₁.1) hu₁.2
  have hβR := hγR u₂ (hIcc hu₂.1) hu₂.2
  -- the margin `m` of the marks from `[α, β]`
  obtain ⟨m, hm, hmle⟩ := exists_pos_le_of_fintype (fun j => if p j < 0 then α - p j else p j - β) fun j => by
    rcases lt_or_gt_of_ne (hp0 j) with h | h
    · simp only [h, ↓reduceIte]; linarith [(hαR j).1 h]
    · simp only [not_lt.2 h.le, ↓reduceIte]; linarith [(hβR j).2 h]
  have hmneg : ∀ j, p j < 0 → p j ≤ α - m := fun j h => by
    have := hmle j; simp only [h, ↓reduceIte] at this; linarith
  have hmpos : ∀ j, 0 < p j → β + m ≤ p j := fun j h => by
    have := hmle j; simp only [not_lt.2 h.le, ↓reduceIte] at this; linarith
  have hkβ := hmpos k hk0
  -- the points of `[0, τ']` off the inner seed interval stay above a height `h₀ > 0`
  set I₀ : Set ℝ := Ioo (α - m / 4) (β + m / 4) with hI₀
  set K : Set ℝ := Icc 0 τ' ∩ (fun u => (γ u).re) ⁻¹' I₀ᶜ with hK
  have hKc : IsCompact K := isCompact_Icc.of_isClosed_subset
    (hre'.preimage_isClosed_of_isClosed isClosed_Icc isOpen_Ioo.isClosed_compl) inter_subset_left
  have hKpos : ∀ u ∈ K, 0 < (γ u).im := by
    intro u hu
    rcases (show (0 : ℝ) ≤ (γ u).im from hγH u (hIcc hu.1)).lt_or_eq with h | h
    · exact h
    · have hab := hZab u ⟨hu.1, h.symm⟩
      exact absurd ⟨by linarith [hab.1], by linarith [hab.2]⟩ hu.2
  obtain ⟨h₀, hh₀, hh₀K⟩ : ∃ h₀ > 0, ∀ u ∈ K, h₀ ≤ (γ u).im := by
    rcases K.eq_empty_or_nonempty with hKe | hKn
    · exact ⟨1, one_pos, fun u hu => by rw [hKe] at hu; exact absurd hu (Set.notMem_empty u)⟩
    · obtain ⟨u₀, hu₀, hmin₀⟩ := hKc.exists_isMinOn hKn
        ((Complex.continuous_im.comp_continuousOn hγc').mono inter_subset_left)
      exact ⟨(γ u₀).im, hKpos u₀ hu₀, fun u hu => hmin₀ hu⟩
  -- a bound on `[0, τ']`
  obtain ⟨M₁, hM₁⟩ := (isCompact_Icc.image_of_continuousOn hγc').isBounded.exists_norm_le
  have hM₁' : ∀ u ∈ Icc 0 τ', ‖γ u‖ ≤ M₁ := fun u hu => hM₁ _ ⟨u, hu, rfl⟩
  have hM₁0 : 0 ≤ M₁ := (norm_nonneg _).trans (hM₁' 0 ⟨le_rfl, hτ'0.le⟩)
  -- the parameters
  set l₀ := α - m / 2 with hl₀
  set r₀ := β + m / 2 with hr₀
  set μ := min (min (m / 16) (d / 16)) (min (h₀ / 4) (min (-l₀ / 4) (r₀ / 4))) with hμ
  have hl₀neg : 0 < -l₀ := by rw [hl₀]; linarith
  have hr₀pos : 0 < r₀ := by rw [hr₀]; linarith
  have hμ0 : 0 < μ := lt_min (lt_min (by positivity) (by positivity))
    (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  have hμm : μ ≤ m / 16 := (min_le_left _ _).trans (min_le_left _ _)
  have hμd : μ ≤ d / 16 := (min_le_left _ _).trans (min_le_right _ _)
  have hμh : μ ≤ h₀ / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hμl : μ ≤ -l₀ / 4 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hμr : μ ≤ r₀ / 4 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  set a₁ := V - d / 2 with ha₁
  set b₁ := V + d / 2 with hb₁
  set Rc := M₁ + V + d + 1 + μ with hRc
  set P : SeedCut := ⟨l₀, r₀, a₁, b₁, μ, Rc⟩ with hP
  have hPV : P.Valid :=
    { μ_pos := hμ0
      l₀_lt := by show l₀ < -(3 * μ); linarith
      r₀_gt := by show 3 * μ < r₀; linarith
      r₀_lt := by show r₀ + μ < a₁ - μ; rw [hr₀, ha₁]; linarith
      core1 := by show a₁ + 3 * μ < b₁ - 3 * μ; rw [ha₁, hb₁]; linarith
      R_pos := by show 0 < Rc; rw [hRc]; linarith }
  have hI₀sub : ∀ x ∈ I₀, x ∈ Ioo (l₀ + 2 * μ) (r₀ - 2 * μ) := fun x hx =>
    ⟨by rw [hl₀]; linarith [hx.1], by rw [hr₀]; linarith [hx.2]⟩
  refine ⟨P, hPV, fun j => ?_, fun j hj => ?_, fun j hj => ?_, ?_, fun u hu => ?_⟩
  · rcases lt_or_gt_of_ne (hp0 j) with h | h
    · left; show p j < l₀ - μ; linarith [hmneg j h]
    · right; show r₀ + μ < p j; linarith [hmpos j h]
  · show p j < a₁ - μ
    have := hdp j
    rw [abs_of_neg (by linarith)] at this
    rw [ha₁]; linarith
  · show b₁ + μ < p j
    have := hdp j
    rw [abs_of_pos (by linarith)] at this
    rw [hb₁]; linarith
  · show V < b₁ + μ; rw [hb₁]; linarith
  · by_cases hτu : τ' < u
    · -- near the target
      have hr := hnearRe u hu hτu
      have hn := hnear u hu hτu
      have hnorm : ‖γ u‖ < V + d / 8 := by
        have := norm_sub_norm_le (γ u) (V : ℂ)
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hV] at this
        rw [Complex.dist_eq] at hn
        linarith
      refine ⟨⟨show ‖γ u‖ < Rc - μ by rw [hRc]; linarith, Or.inr (Or.inr ⟨?_, ?_⟩)⟩, fun him => ?_⟩
      · show a₁ + 2 * μ < (γ u).re; rw [ha₁]; linarith [neg_abs_le ((γ u).re - V)]
      · show (γ u).re < b₁ - 2 * μ; rw [hb₁]; linarith [le_abs_self ((γ u).re - V)]
      · have := (hγR u hu him k).2 hk0
        linarith [neg_abs_le ((γ u).re - V)]
    · push Not at hτu
      have huI : u ∈ Icc 0 τ' := ⟨hu.1, hτu⟩
      have hnorm : ‖γ u‖ < Rc - μ := by rw [hRc]; linarith [hM₁' u huI]
      refine ⟨⟨hnorm, ?_⟩, fun him => hI₀sub _ ?_⟩
      · by_cases hI : (γ u).re ∈ I₀
        · exact Or.inr (Or.inl (hI₀sub _ hI))
        · exact Or.inl (by linarith [hh₀K u ⟨huI, hI⟩])
      · have hab := hZab u ⟨huI, him⟩
        exact ⟨by linarith [hab.1], by linarith [hab.2]⟩

/-! ### The energy bound after the restart time -/

section Energy

variable {U : ℝ → ℝ} {T : ℝ} {η : ℝ → ℂ} {q : ℝ}

/-- **The drift energy after the restart time is bounded, above `κ = 4`** (Aux. lemma 61 in the chart at `q`, with
the asymmetric seed core). `GB7a.exists_energy_bound_of_restart` without its hypothesis that the trace after `q` stays
off the prefix: only the limit point `y` must be off the prefix, and some force coordinate must lie strictly between the
driver and the target at `q`. -/
theorem exists_energy_bound_of_restart_above4 (hη : IsLoewnerTraceLT U T η) (hU : Continuous U) (hU0 : U 0 = 0)
    (hq : 0 ≤ q) (hqT : q < T) (hH : ∀ s ∈ Ioo q T, η s ∈ H) {y : ℝ}
    (hlim : Tendsto η (𝓝[<] T) (𝓝 (y : ℂ))) (hyq : (y : ℂ) ∉ η '' Icc 0 q) {v : ℝ → ℂ}
    (hv : IsForwardSol U (y : ℂ) q v) {ι : Type*} [Fintype ι] (û : ι → ℝ → ℝ) (c : ι → ℝ)
    (hpkg : ∀ j, ∀ s ∈ Ico q T, ContinuousOn (û j) (Icc q s) ∧
      ∀ s₁ ∈ Icc q s, ∀ s₂ ∈ Icc q s, s₁ ≤ s₂ →
        û j s₂ - û j s₁ = -(U s₂ - U s₁) + ∫ r in s₁..s₂, 2 / û j r)
    (hne : ∀ j, ∀ s ∈ Ico q T, û j s ≠ 0) (hsep : ∀ j, û j q ≠ (v q).re) {k : ι} (hk0 : 0 < û k q)
    (hkV : û k q < (v q).re)
    (hcore : ∑ j ∈ univ.filter (fun j => 0 < û j q ∧ û j q < (v q).re), c j = 0) :
    ∃ C, ∀ t ∈ Ico q T, ∫ s in q..t, (∑ j, c j / û j s) ^ 2 ≤ C := by
  classical
  set V := (v q).re with hVdef
  set τ := T - q with hτ
  have hτ0 : 0 < τ := sub_pos.2 hqT
  set γ := loewnerTip (shiftDrive U q) with hγ
  have hS : IsLoewnerTraceLT (shiftDrive U q) τ γ := (hη.isLoewnerTraceLT_shift hU hU0 hq).1
  have hUS := QuantumZipper.RS.continuous_shiftDrive hU q
  have hUS0 := QuantumZipper.RS.shiftDrive_zero U q
  have hγlim : Tendsto γ (𝓝[<] τ) (𝓝 (V : ℂ)) := tendsto_chart_of_restart hη hU hU0 hq hqT hH hlim hyq hv
  set p : ι → ℝ := fun j => û j q with hp
  -- the force coordinates are alive in the chart before `τ`
  have hsolu : ∀ j, ∀ u ∈ Ico 0 τ, IsForwardSol (shiftDrive U q) (p j : ℂ) u (fun s => (û j (q + s) : ℂ)) := by
    intro j u hu
    have ht : q + u ∈ Ico q T := ⟨by linarith [hu.1], by linarith [hu.2]⟩
    obtain ⟨hc, heq⟩ := hpkg j (q + u) ht
    have h := isForwardSol_shift_of_centred ht.1 hc (fun s hs => hne j s ⟨hs.1, hs.2.trans_lt ht.2⟩) heq
    rwa [add_sub_cancel_left] at h
  have hp0 : ∀ j, p j ≠ 0 := fun j => hne j q ⟨le_rfl, hqT⟩
  have hγR : ∀ u ∈ Ico 0 τ, (γ u).im = 0 → ∀ j, (p j < 0 → p j < (γ u).re) ∧ (0 < p j → (γ u).re < p j) :=
    fun u hu him j => ⟨fun h => lt_re_of_chart_real hS hUS hUS0 hu him h (hsolu j u hu),
      fun h => re_lt_of_chart_real hS hUS hUS0 hu him h (hsolu j u hu)⟩
  have hγH : ∀ u ∈ Ico 0 τ, γ u ∈ Hbar := fun u hu => Sec7.IsLoewnerTraceLT.mem_Hbar hS hUS hUS0 hu.1 hu.2
  obtain ⟨P, hP, h0, hlo, hhi, hVb, hcut⟩ := exists_seedCut hτ0 hS.2.1 hS.1 hγH hγlim hp0 hsep
    (k := k) hk0 hkV hγR
  set c₀ := -(Real.pi * ∑ j ∈ univ.filter (fun j => 0 < p j), c j) with hc₀
  have hC : SeedConfig P p c c₀ :=
    { avoid0 := h0
      avoid1 := fun j => (lt_or_gt_of_ne (hsep j)).imp (hlo j) (hhi j)
      seed := by rw [hc₀]; ring
      core := by
        have hsplit := Finset.sum_filter_add_sum_filter_not (univ.filter (fun j => 0 < p j))
          (fun j => p j < V) c
        rw [Finset.filter_filter, Finset.filter_filter] at hsplit
        have e2 : univ.filter (fun j => 0 < p j ∧ ¬ p j < V) =
            univ.filter (fun j => P.b₁ + P.μ ≤ p j) := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨-, h2⟩
            exact (hhi j (lt_of_le_of_ne (not_lt.1 h2) (Ne.symm (hsep j)))).le
          · intro h
            exact ⟨by linarith [hP.μ_pos, hP.r₀_gt, hP.r₀_lt, hP.core1], not_lt.2 (by linarith)⟩
        rw [hcore, zero_add, e2] at hsplit
        rw [hc₀, ← hsplit]
        ring }
  obtain ⟨C, hCb⟩ := exists_markDrift_energy_le_seed hP hC
  refine ⟨max C 0, fun t ht => ?_⟩
  rcases ht.1.eq_or_lt with htq | htq
  · rw [← htq, intervalIntegral.integral_same]
    exact le_max_right _ _
  set t' := t - q with ht'def
  have ht' : 0 < t' := sub_pos.2 htq
  have ht'τ : t' < τ := by linarith [ht.2]
  have hbound := hCb (shiftDrive U q) t' γ hUS hUS0 ht'
    (hS.2.1.mono fun s hs => ⟨hs.1, hs.2.trans_lt ht'τ⟩)
    (fun s hs => hS.2.2 s hs.1.le (hs.2.trans_lt ht'τ))
    (by rintro _ ⟨s, hs, rfl⟩; exact (hcut s ⟨hs.1, hs.2.trans_lt ht'τ⟩).1)
    (fun s hs => ⟨hγH s ⟨hs.1, hs.2.trans_lt ht'τ⟩, (hcut s ⟨hs.1, hs.2.trans_lt ht'τ⟩).2⟩)
    (fun j => ⟨_, hsolu j t' ⟨ht'.le, ht'τ⟩⟩) t' ⟨ht'.le, le_rfl⟩
  have hdrift : ∀ s ∈ uIcc 0 t', markDrift (shiftDrive U q) p c s ^ 2 =
      (∑ j, c j / û j (q + s)) ^ 2 := by
    intro s hs
    rw [uIcc_of_le ht'.le] at hs
    simp only [markDrift]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [fwdMap_eq_of_isForwardSol hUS (hsolu j t' ⟨ht'.le, ht'τ⟩) hs, Complex.ofReal_re]
  rw [intervalIntegral.integral_congr hdrift] at hbound
  have e := intervalIntegral.integral_comp_add_left (fun s => (∑ j, c j / û j s) ^ 2) q (a := 0)
    (b := t')
  simp only [add_zero] at e
  rw [e, ht'def, add_sub_cancel] at hbound
  exact hbound.trans (le_max_left _ _)

end Energy

end Sec5.GB7aAbove4

end InteractingSLE
