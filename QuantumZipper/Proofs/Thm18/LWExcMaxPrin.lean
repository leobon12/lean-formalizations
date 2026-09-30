import Mathlib.Analysis.Complex.Harmonic.Analytic
import Mathlib.Analysis.Complex.AbsMax

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Weak maximum principle for harmonic functions on arbitrary open sets (task LW-EXC-MP)

We prove `lwExc_harm_le_zero`: a harmonic function `f` on an open set `U ⊆ ℂ` (possibly
unbounded, possibly disconnected) whose `limsup` at every finite frontier point and at `∞` is
`≤ 0` satisfies `f ≤ 0` on `U`.

Source: L. V. Ahlfors, *Complex Analysis*, 3rd ed., Ch. 4, §6.2, Theorem 21 (maximum principle
for harmonic functions), and S. Axler, P. Bourdon, W. Ramey, *Harmonic Function Theory*, 2nd ed.,
Corollary 1.10 (boundary limsup version on unbounded domains).
Route: the local strong maximum principle is reduced to mathlib's maximum modulus principle
(`Complex.eventually_eq_of_isLocalMax_norm`) applied to `exp ∘ F`, where `f = Re F` locally
(`InnerProductSpace.HarmonicOnNhd.exists_analyticOnNhd_ball_re_eq`), as in Ahlfors' proof.
For the global step we follow ABR Cor. 1.10 (the superlevel set `{f ≥ ε}` has compact closure in
`U`, so `f` attains its supremum); instead of passing to the connected component we note that the
maximum set is clopen in `ℂ` (closedness at frontier points of `U` uses the boundary hypothesis),
hence all of `ℂ`, contradicting the hypothesis at `∞`. This is a minor reorganisation of the
standard argument, not a change of statement.
-/

namespace QuantumZipper.Thm18Asm.LWFar

open Metric Set Filter Topology

/-- Local strong maximum principle: a harmonic function with a local maximum at an interior
point is constant near that point (Ahlfors, Ch. 4 §6.2, Thm 21, via maximum modulus). -/
theorem lwExc_harm_eventually_eq_of_isLocalMax {U : Set ℂ} {f : ℂ → ℝ} (hU : IsOpen U)
    (hf : InnerProductSpace.HarmonicOnNhd f U) {x : ℂ} (hx : x ∈ U) (hmax : IsLocalMax f x) :
    ∀ᶠ y in 𝓝 x, f y = f x := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU x hx
  have hfb : InnerProductSpace.HarmonicOnNhd f (ball x r) := fun y hy => hf y (hball hy)
  obtain ⟨F, hFa, hFe⟩ := hfb.exists_analyticOnNhd_ball_re_eq
  have hbn : ball x r ∈ 𝓝 x := Metric.ball_mem_nhds x hr
  have hd : ∀ᶠ z in 𝓝 x, DifferentiableAt ℂ (fun z => Complex.exp (F z)) z := by
    filter_upwards [hbn] with z hz
    exact (hFa z hz).differentiableAt.cexp
  have hnorm : ∀ z ∈ ball x r, ‖Complex.exp (F z)‖ = Real.exp (f z) := by
    intro z hz
    rw [Complex.norm_exp]
    exact congrArg Real.exp (hFe hz)
  have hxb : x ∈ ball x r := mem_ball_self hr
  have hloc : IsLocalMax (norm ∘ fun z => Complex.exp (F z)) x := by
    have hm : ∀ᶠ z in 𝓝 x, f z ≤ f x := hmax
    show ∀ᶠ z in 𝓝 x, ‖Complex.exp (F z)‖ ≤ ‖Complex.exp (F x)‖
    filter_upwards [hm, hbn] with z hz1 hz2
    rw [hnorm z hz2, hnorm x hxb]
    exact Real.exp_le_exp.2 hz1
  filter_upwards [Complex.eventually_eq_of_isLocalMax_norm hd hloc, hbn] with z hz1 hz2
  have h := congrArg norm hz1
  rw [hnorm z hz2, hnorm x hxb] at h
  exact Real.exp_injective h

/-- Weak maximum principle for harmonic functions on an arbitrary (possibly unbounded) open set,
with boundary limsup ≤ 0 at every finite frontier point and at ∞
(Ahlfors, *Complex Analysis*, 3rd ed., Ch. 4 §6.2, Thm 21; Axler–Bourdon–Ramey,
*Harmonic Function Theory*, Cor. 1.10). -/
theorem lwExc_harm_le_zero {U : Set ℂ} {f : ℂ → ℝ} (hU : IsOpen U)
    (hf : InnerProductSpace.HarmonicOnNhd f U)
    (hbd : ∀ x₀ ∈ frontier U, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ y ∈ U, dist y x₀ < δ → f y ≤ ε)
    (hinf : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ y ∈ U, R ≤ ‖y‖ → f y ≤ ε) :
    ∀ y ∈ U, f y ≤ 0 := by
  intro y₀ hy₀
  by_contra hpos
  push Not at hpos
  set ε : ℝ := f y₀ / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hεy : ε < f y₀ := by rw [hε]; linarith
  have hcont : ∀ y ∈ U, ContinuousAt f y := fun y hy => (hf y hy).1.continuousAt
  -- frontier points of `U` are closure points not in `U`
  have hfr : ∀ y ∈ closure U, y ∉ U → y ∈ frontier U := by
    intro y h1 h2
    rw [hU.frontier_eq]
    exact ⟨h1, h2⟩
  -- a set on which `f ≥ ε` has its closure inside `U`
  have hclos : ∀ S ⊆ U, (∀ s ∈ S, ε ≤ f s) → closure S ⊆ U := by
    intro S hSU hS y hy
    by_contra hyU
    have hyF := hfr y (closure_mono hSU hy) hyU
    obtain ⟨δ, hδ, hδf⟩ := hbd y hyF (ε / 2) (by linarith)
    obtain ⟨b, hbS, hb⟩ := Metric.mem_closure_iff.1 hy δ hδ
    have h1 := hδf b (hSU hbS) (by rw [dist_comm]; exact hb)
    have h2 := hS b hbS
    linarith
  -- the superlevel set `K`
  set K : Set ℂ := {y | y ∈ U ∧ ε ≤ f y} with hK
  have hKU : K ⊆ U := fun y hy => hy.1
  have hKc : closure K ⊆ U := hclos K hKU (fun s hs => hs.2)
  obtain ⟨R, hR⟩ := hinf (ε / 2) (by linarith)
  have hKb : K ⊆ closedBall 0 R := by
    intro y hy
    rw [mem_closedBall, dist_zero_right]
    by_contra h
    push Not at h
    have := hR y hy.1 h.le
    have := hy.2
    linarith
  have hKcpt : IsCompact (closure K) :=
    (isCompact_closedBall 0 R).of_isClosed_subset isClosed_closure
      (closure_minimal hKb isClosed_closedBall)
  have hy₀K : y₀ ∈ closure K := subset_closure ⟨hy₀, hεy.le⟩
  have hcontK : ContinuousOn f (closure K) :=
    fun y hy => (hcont y (hKc hy)).continuousWithinAt
  obtain ⟨xs, hxsK, hxsmax⟩ := hKcpt.exists_isMaxOn ⟨y₀, hy₀K⟩ hcontK
  have hxsU : xs ∈ U := hKc hxsK
  set M : ℝ := f xs with hM
  have hMy : f y₀ ≤ M := hxsmax hy₀K
  have hMε : ε < M := lt_of_lt_of_le hεy hMy
  -- `xs` is a global maximum of `f` on `U`
  have hglob : ∀ y ∈ U, f y ≤ M := by
    intro y hy
    by_cases h : ε ≤ f y
    · exact hxsmax (subset_closure ⟨hy, h⟩)
    · push Not at h
      linarith
  -- the maximum set is clopen in `ℂ`
  set S : Set ℂ := {y | y ∈ U ∧ f y = M} with hS
  have hSU : S ⊆ U := fun y hy => hy.1
  have hSopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro y hy
    have hloc : IsLocalMax f y := by
      filter_upwards [hU.mem_nhds hy.1] with z hz
      rw [hy.2]
      exact hglob z hz
    filter_upwards [lwExc_harm_eventually_eq_of_isLocalMax hU hf hy.1 hloc,
      hU.mem_nhds hy.1] with z hz1 hz2
    exact ⟨hz2, hz1.trans hy.2⟩
  have hSclosed : IsClosed S := by
    apply isClosed_of_closure_subset
    intro y hy
    have hyU : y ∈ U := hclos S hSU (fun s hs => by rw [hs.2]; exact hMε.le) hy
    refine ⟨hyU, le_antisymm (hglob y hyU) ?_⟩
    exact ContinuousWithinAt.closure_le hy continuousWithinAt_const
      (hcont y hyU).continuousWithinAt (fun s hs => hs.2.ge)
  have hSuniv : S = univ := IsClopen.eq_univ ⟨hSclosed, hSopen⟩ ⟨xs, hxsU, rfl⟩
  -- contradiction at `∞`
  obtain ⟨R', hR'⟩ := hinf ε hε0
  set w : ℂ := ((max R' 0 : ℝ) : ℂ) with hw
  have hwS : w ∈ S := by rw [hSuniv]; exact mem_univ w
  have hwn : R' ≤ ‖w‖ := by
    rw [hw, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact le_max_left _ _
  have := hR' w hwS.1 hwn
  rw [hwS.2] at this
  linarith

end QuantumZipper.Thm18Asm.LWFar
