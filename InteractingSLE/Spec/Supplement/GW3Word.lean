/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4KernelLife
import InteractingSLE.Spec.Supplement.GW2ConeData
import InteractingSLE.Spec.Sec5.Aux22ChartEFlow
import InteractingSLE.Foundations.Loewner.HullKernel
import InteractingSLE.Foundations.Loewner.YuanTrace
import QuantumZipper.Proofs.Complex.BasicsReflection

/-!
# Lemma GW3: the component counterflow words have every partial sum greater than `−2`

Packet PROVE-T14-GW5. Lemma GW3 (`source/spec/p625-671.md` L203–L225, pp. 636–637), the bounds (GW3.2):
"In the reversed counterflow chart their finite cumulative words are `S_L = (H_R + πχ)/Λ − 1`,
`S_R = (−H_L + πχ)/Λ − 1`, `−2 < S_L, S_R ≤ d`"; proof: "Apply the compatible inversion with the fixed frame
`F = −h − πχ` … On a flow flank `H_R = −Λ` or `H_L = Λ`, both formulas equal `c − 2 = d`. On a lower real connector,
its original ambient counterflow sum is `(H_R + πχ)/Λ − 1 > −2`". The named input `GW4.GW3WordBoundStatement`
(`GW4KernelLife`) is the lower bound `−2 < S_L, S_R`, used for the infinite relative lifetime of GW4.

## Proof

* The component counterflow word: by `GW2Cone.eq_counterflowData_off`, the data `b'` of the component counterflow
  field agree with `counterflowData κ bC` off a finite set, i.e. `b'(y) = −bC(−1/y) + πχ` for `y > 0` and
  `b'(y) = −bC(−1/y) − πχ` for `y < 0` (`counterflowData_of_pos`, `counterflowData_of_neg`; `χ(16/κ) = −χ`).
* Partial sums and data: every right (left) partial sum of a flow-line word exceeds `−2` iff the data exceed `−λ'`
  right of the seed (are below `λ'` left of it), `λ' = λ(16/κ) = Λ` (`neg_two_lt_sum_flowLineRhoR_of_forall`,
  `neg_lambda_lt_of_sum_flowLineRhoR` and the left versions).
* The ambient bounds: Lemma GW0's forward implication (named input `GW0.GW0ForwardStatement`) makes the ambient
  counterflow word admissible (`GW0.counterflow_admissible`), i.e. `b(t) < Λ + πχ` for `t < 0` and
  `b(t) > −Λ − πχ` for `t > 0` (off the jumps).
* The GW3.1 values: on an ordinary flank the component value is `±Λ`, which gives `πχ/Λ − 2 = d > −2` (`κ < 4`);
  on a connector of the left (right) walk, which lies on the original left (right) boundary (named input
  `WalkConnectorSideStatement`, GW4's proof: "Every nontrivial real interval in `R` is on the original right boundary,
  and every such interval in `L` is on the original left boundary"), the component value is the original value
  `b(t)`, and the ambient bound applies.
* Generic points (`exists_generic`): the bound is needed on whole intervals of the component word, while the GW3.1
  word reads `b` at the boundary point `p(x)` only, so `p(x)` must avoid the original jumps (where `b` is not read)
  and the root. The boundary map `x ↦ p(x)` of a component chart is continuous and **not constant on any interval**
  (`false_of_tendsto_const`: Schwarz reflection `QuantumZipper.CA.exists_reflection_extension` and the identity
  theorem; the inverse chart is injective, and holomorphic because the component is open,
  `differentiableOn_inv_of_isComponentChart`),
  so every interval contains a generic point. Openness of the component is the named input
  `BetweenComponentsOpenStatement` (a consequence of the between-region geometry `GW3.GW3GeometryStatement`, both of
  whose alternatives contain `IsOpen C`: `betweenComponentsOpenStatement_of_geometry`).

## Main results

* `gw3WordBoundStatement_of_inputs` : `GW4.GW3WordBoundStatement` from `BetweenComponentsOpenStatement`,
  `GW0.GW0ForwardStatement` and `WalkConnectorSideStatement`;
* `betweenComponentsOpenStatement_of_geometry` : `BetweenComponentsOpenStatement` from `GW3.GW3GeometryStatement`;
* `componentKernels_of_gw3Inputs` : the frozen component-kernel anchor's conclusion from these, GW3's field law,
  GW4's traversal core and Theorems 1.2–1.3;
* deterministic tools: `false_of_tendsto_const`, `exists_mem_Ioo_tendsto_ne`, `exists_generic`,
  `neg_two_lt_sum_flowLineRhoR_of_forall`, `neg_two_lt_sum_flowLineRhoL_of_forall`,
  `neg_lambda_lt_of_sum_flowLineRhoR`, `lt_lambda_of_sum_flowLineRhoL`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)
open SupercriticalConformalCovariance (IsConformalBijection)

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW3Word

/-- The inverse of a component chart of an open component is holomorphic on `ℍ` (it is the inverse of the conformal
bijection `fwd : C → ℍ`, `isConformalBijection_invFunOn`). -/
theorem differentiableOn_inv_of_isComponentChart {R L C : Set ℂ} {c : Chart}
    (hc : IsComponentChart R L C c) (hCo : IsOpen C) : DifferentiableOn ℂ c.2.1 H := by
  obtain ⟨hd, hmF, hmI, hinv, -, -, -⟩ := hc
  have hbij : BijOn c.1 C H := hinv.bijOn hmF hmI
  have heq : EqOn (Function.invFunOn c.1 C) c.2.1 H := fun w hw => by
    have h1 : c.2.1 w ∈ C := hmI hw
    have h2 : c.1 (c.2.1 w) = w := hinv.2 hw
    calc Function.invFunOn c.1 C w = Function.invFunOn c.1 C (c.1 (c.2.1 w)) := by rw [h2]
      _ = c.2.1 w := hbij.injOn.leftInvOn_invFunOn h1
  exact (isConformalBijection_invFunOn hCo ⟨hd, hbij⟩).1.congr fun w hw => (heq hw).symm

/-- A point of the ball `B(x₀, r)` has real part in `(x₀ − r, x₀ + r)`. -/
theorem mem_Ioo_of_mem_ball {x₀ r : ℝ} {z : ℂ} (hz : z ∈ ball (x₀ : ℂ) r) :
    z.re ∈ Ioo (x₀ - r) (x₀ + r) := by
  have h := mem_ball.1 hz
  rw [Complex.dist_eq] at h
  have hre : |z.re - x₀| ≤ ‖z - x₀‖ := by
    have := Complex.abs_re_le_norm (z - x₀)
    simpa using this
  have := lt_of_le_of_lt hre h
  rw [abs_lt] at this
  constructor <;> linarith

/-- **An injective holomorphic map on `ℍ` has no constant boundary value on an interval**: if `inv` is holomorphic and
injective on `ℍ` and tends to the same point `p₀` at every point of a nonempty open interval, we reach a contradiction
(Schwarz reflection of `inv − p₀`, whose boundary values `0` are real, and the identity theorem). -/
theorem false_of_tendsto_const {inv : ℂ → ℂ} (hd : DifferentiableOn ℂ inv H) (hinj : InjOn inv H) {a c : ℝ}
    {p₀ : ℂ} (hac : a < c) (hlim : ∀ x ∈ Ioo a c, Tendsto inv (𝓝[H] (x : ℂ)) (𝓝 p₀)) : False := by
  set x₀ : ℝ := (a + c) / 2 with hx₀
  set r : ℝ := (c - a) / 2 with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  have hIoo : Ioo (x₀ - r) (x₀ + r) = Ioo a c := by
    rw [hx₀, hr]; congr 1 <;> ring
  set f : ℂ → ℂ := fun w => inv w - p₀ with hf
  have hfc : ContinuousOn f H := (hd.continuousOn).sub continuousOn_const
  set g := extendFrom H f with hg
  have hlimf : ∀ z ∈ Hbar ∩ ball (x₀ : ℂ) r, ∃ y, Tendsto f (𝓝[H] z) (𝓝 y) := by
    rintro z ⟨hz, hzb⟩
    rcases (show (0 : ℝ) ≤ z.im from hz).lt_or_eq with hpos | hzero
    · exact ⟨f z, (hfc z hpos).tendsto⟩
    · refine ⟨0, ?_⟩
      have hzr : z = ((z.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [← hzero])
      have hx := mem_Ioo_of_mem_ball hzb
      rw [hIoo] at hx
      have := (hlim z.re hx).sub_const p₀
      rw [sub_self, ← hzr] at this
      exact this
  have hgc : ContinuousOn g (Hbar ∩ ball (x₀ : ℂ) r) :=
    continuousOn_extendFrom (fun z hz => by rw [closure_H]; exact hz.1) hlimf
  have hgf : ∀ w ∈ H, g w = f w := extendFrom_extends hfc
  have hgd : DifferentiableOn ℂ g (H ∩ ball (x₀ : ℂ) r) :=
    ((hd.sub_const p₀).mono inter_subset_left).congr fun w hw => hgf w hw.1
  have hg0 : ∀ z ∈ ball (x₀ : ℂ) r, z.im = 0 → g z = 0 := by
    intro z hz hz0
    obtain ⟨y, hy⟩ := hlimf z ⟨show (0 : ℝ) ≤ z.im from hz0.ge, hz⟩
    have hzr : z = ((z.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hz0])
    have hx := mem_Ioo_of_mem_ball hz
    rw [hIoo] at hx
    have h1 := (hlim z.re hx).sub_const p₀
    rw [sub_self, ← hzr] at h1
    have hNe : (𝓝[H] z).NeBot := FiniteEndpoint.neBot_nhdsWithin_H hz0
    have h2 := tendsto_extendFrom (A := H) (f := f) ⟨0, h1⟩
    exact tendsto_nhds_unique h2 h1
  obtain ⟨G, hGd, hGeq, -⟩ := QuantumZipper.CA.exists_reflection_extension hgd hgc
    (fun z hz hz0 => by rw [hg0 z hz hz0, Complex.zero_im])
  have hGan : AnalyticOnNhd ℂ G (ball (x₀ : ℂ) r) := hGd.analyticOnNhd isOpen_ball
  have hG0 : ∀ t : ℝ, |t| < r → G ((x₀ + t : ℝ) : ℂ) = 0 := by
    intro t ht
    have hzb : ((x₀ + t : ℝ) : ℂ) ∈ ball (x₀ : ℂ) r := by
      rw [mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      simpa using ht
    rw [hGeq ⟨show (0 : ℝ) ≤ ((x₀ + t : ℝ) : ℂ).im by simp, hzb⟩]
    exact hg0 _ hzb (by simp)
  have hfreq : ∃ᶠ z in 𝓝[≠] (x₀ : ℂ), G z = 0 := by
    set u : ℕ → ℂ := fun n => ((x₀ + r / (n + 2) : ℝ) : ℂ) with hu
    have hu0 : Tendsto (fun n : ℕ => r / ((n : ℝ) + 2)) atTop (𝓝 0) := by
      have : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
        tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
      exact tendsto_const_nhds.div_atTop this
    have hut : Tendsto u atTop (𝓝 (x₀ : ℂ)) := by
      have h0 : Tendsto (fun n : ℕ => x₀ + r / ((n : ℝ) + 2)) atTop (𝓝 x₀) := by
        simpa using (tendsto_const_nhds (x := x₀)).add hu0
      exact (Complex.continuous_ofReal.tendsto x₀).comp h0
    have hune : ∀ n : ℕ, u n ≠ (x₀ : ℂ) := fun n h => by
      have h' := Complex.ofReal_injective h
      have : 0 < r / ((n : ℝ) + 2) := div_pos hr0 (by positivity)
      linarith
    have hut' : Tendsto u atTop (𝓝[≠] (x₀ : ℂ)) :=
      tendsto_nhdsWithin_iff.2 ⟨hut, Eventually.of_forall hune⟩
    refine hut'.frequently (Frequently.of_forall fun n => hG0 _ ?_)
    have hpos : 0 < r / ((n : ℝ) + 2) := div_pos hr0 (by positivity)
    rw [abs_of_pos hpos, div_lt_iff₀ (by positivity)]
    nlinarith [show (0 : ℝ) ≤ n from n.cast_nonneg]
  have hzero := hGan.eqOn_zero_of_preconnected_of_frequently_eq_zero (convex_ball _ _).isPreconnected
    (mem_ball_self hr0) hfreq
  have hpt : ∀ t : ℝ, 0 < t → t < r → inv ((x₀ : ℂ) + (t : ℝ) * Complex.I) = p₀ ∧
      (x₀ : ℂ) + (t : ℝ) * Complex.I ∈ H := by
    intro t ht0 htr
    set w : ℂ := (x₀ : ℂ) + (t : ℝ) * Complex.I with hw
    have hwH : w ∈ H := by
      show 0 < w.im
      simp [hw, ht0]
    have hwb : w ∈ ball (x₀ : ℂ) r := by
      rw [mem_ball, Complex.dist_eq, hw, add_sub_cancel_left, norm_mul, Complex.norm_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
      exact htr
    have h1 : G w = 0 := hzero hwb
    rw [hGeq ⟨(show (0 : ℝ) < w.im from hwH).le, hwb⟩, hgf w hwH] at h1
    exact ⟨sub_eq_zero.1 h1, hwH⟩
  obtain ⟨e1, hw1⟩ := hpt (r / 2) (by linarith) (by linarith)
  obtain ⟨e2, hw2⟩ := hpt (r / 4) (by linarith) (by linarith)
  have heq := hinj hw1 hw2 (e1.trans e2.symm)
  have him := congrArg Complex.im heq
  simp at him
  linarith

/-- The boundary extension `x ↦ lim_{w → x} inv w` of a map continuous on `ℍ` with a limit at every real point is
continuous on `ℝ`, and is the limit at every real point. -/
theorem continuous_extendFrom_ofReal {inv : ℂ → ℂ} (hd : ContinuousOn inv H)
    (hlim : ∀ x : ℝ, ∃ p, Tendsto inv (𝓝[H] (x : ℂ)) (𝓝 p)) :
    Continuous (fun x : ℝ => extendFrom H inv (x : ℂ)) := by
  have hext : ContinuousOn (extendFrom H inv) Hbar := by
    refine continuousOn_extendFrom (by rw [closure_H]) fun z hz => ?_
    rcases (show (0 : ℝ) ≤ z.im from hz).lt_or_eq with hpos | hzero
    · exact ⟨inv z, (hd z hpos).tendsto⟩
    · have hzr : z = ((z.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [← hzero])
      rw [hzr]
      exact hlim z.re
  exact hext.comp_continuous Complex.continuous_ofReal fun x => show (0 : ℝ) ≤ (x : ℂ).im by simp

/-- **Generic boundary points**: for an injective holomorphic map on `ℍ` with a limit at every real point,
every nonempty open interval contains a point, off a given finite set, whose boundary limit is not one of finitely
many given real points. -/
theorem exists_mem_Ioo_tendsto_ne {inv : ℂ → ℂ} (hd : DifferentiableOn ℂ inv H) (hinj : InjOn inv H)
    (hlim : ∀ x : ℝ, ∃ p, Tendsto inv (𝓝[H] (x : ℂ)) (𝓝 p)) {a b : ℝ} (hab : a < b)
    {Ex E : Set ℝ} (hEx : Ex.Finite) (hE : E.Finite) :
    ∃ x ∈ Ioo a b, x ∉ Ex ∧ ∀ p : ℂ, Tendsto inv (𝓝[H] (x : ℂ)) (𝓝 p) → ∀ t ∈ E, p ≠ (t : ℂ) := by
  obtain ⟨m, ham, hmb, hdisj⟩ : ∃ m, a < m ∧ m ≤ b ∧ ∀ x ∈ Ioo a m, x ∉ Ex := by
    set S : Finset ℝ := insert b (hEx.toFinset.filter (fun x => a < x)) with hS
    have hSne : S.Nonempty := Finset.insert_nonempty _ _
    refine ⟨S.min' hSne, (Finset.lt_min'_iff S hSne).2 fun y hy => ?_, S.min'_le b (Finset.mem_insert_self _ _),
      fun x hx hxE => ?_⟩
    · rcases Finset.mem_insert.1 hy with rfl | hy
      · exact hab
      · exact (Finset.mem_filter.1 hy).2
    · have : x ∈ S := Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨hEx.mem_toFinset.2 hxE, hx.1⟩)
      exact absurd (S.min'_le x this) (not_le.2 hx.2)
  by_contra hcon
  push Not at hcon
  set q : ℝ → ℂ := fun x => extendFrom H inv (x : ℂ) with hq
  have hqc : Continuous q := continuous_extendFrom_ofReal hd.continuousOn hlim
  have hqlim : ∀ x : ℝ, Tendsto inv (𝓝[H] (x : ℂ)) (𝓝 (q x)) := fun x => tendsto_extendFrom (hlim x)
  have hmaps : MapsTo q (Ioo a m) (((↑) : ℝ → ℂ) '' E) := by
    intro x hx
    obtain ⟨p, hp, t, ht, hpt⟩ := hcon x ⟨hx.1, hx.2.trans_le hmb⟩ (hdisj x hx)
    have hNe : (𝓝[H] (x : ℂ)).NeBot := FiniteEndpoint.neBot_nhdsWithin_H (by simp)
    have := tendsto_nhds_unique (hqlim x) hp
    exact ⟨t, ht, by rw [this, hpt]⟩
  set x₀ := (a + m) / 2 with hx₀
  have hx₀m : x₀ ∈ Ioo a m := ⟨by rw [hx₀]; linarith, by rw [hx₀]; linarith⟩
  obtain ⟨t₀, -, ht₀⟩ := hmaps hx₀m
  have hconst : ∀ x ∈ Ioo a m, q x = (t₀ : ℂ) := fun x hx => by
    rw [ht₀]
    exact isPreconnected_Ioo.constant_of_mapsTo (hE.image _).isDiscrete hqc.continuousOn hmaps hx hx₀m
  exact false_of_tendsto_const hd hinj ham fun x hx => hconst x hx ▸ hqlim x

/-! ### Partial sums of a flow-line word and its boundary data -/

section Word

open Finset

variable {d : ℝ → ℝ} {J : Finset ℝ}

/-- The right marks of the flow-line word from `0` are nonnegative. -/
theorem flowLineXR_nonneg (d : ℝ → ℝ) (J : Finset ℝ) (i : Fin (flowLineNR d J 0)) : 0 ≤ flowLineXR d J 0 i := by
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
  · exact le_of_eq rfl
  · show 0 ≤ ((PiecewiseConstantBoundaryData.jumpSet d J).filter (0 < ·)).orderEmbOfFin rfl j - 0
    rw [sub_zero]
    have h := Finset.orderEmbOfFin_mem ((PiecewiseConstantBoundaryData.jumpSet d J).filter (0 < ·)) rfl j
    exact (Finset.mem_filter.1 h).2.le

/-- The left marks of the flow-line word from `0` are nonpositive. -/
theorem flowLineXL_nonpos (d : ℝ → ℝ) (J : Finset ℝ) (i : Fin (flowLineNL d J 0)) : flowLineXL d J 0 i ≤ 0 := by
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
  · exact le_of_eq rfl
  · show ((PiecewiseConstantBoundaryData.jumpSet d J).filter (· < 0)).orderEmbOfFin rfl (Fin.rev j) - 0 ≤ 0
    rw [sub_zero]
    have h := Finset.orderEmbOfFin_mem ((PiecewiseConstantBoundaryData.jumpSet d J).filter (· < 0)) rfl (Fin.rev j)
    exact (Finset.mem_filter.1 h).2.le

/-- Right partial sums by index are partial sums by position (the right marks increase strictly). -/
theorem filter_le_eq_filter_flowLineXR_le (d : ℝ → ℝ) (J : Finset ℝ) (i : Fin (flowLineNR d J 0)) :
    univ.filter (fun l => l ≤ i) = univ.filter (fun l => flowLineXR d J 0 l ≤ flowLineXR d J 0 i) := by
  have hm : StrictMono (flowLineXR d J 0) := fun _ _ h => GW0.flowLineXR_lt d J 0 h
  exact Finset.filter_congr fun l _ => hm.le_iff_le.symm

/-- Left partial sums by index are partial sums by position (the left marks decrease strictly). -/
theorem filter_le_eq_filter_le_flowLineXL (d : ℝ → ℝ) (J : Finset ℝ) (i : Fin (flowLineNL d J 0)) :
    univ.filter (fun l => l ≤ i) = univ.filter (fun l => flowLineXL d J 0 i ≤ flowLineXL d J 0 l) := by
  have hm : StrictAnti (flowLineXL d J 0) := fun _ _ h => GW0.flowLineXL_lt d J 0 h
  exact Finset.filter_congr fun l _ => hm.le_iff_ge.symm

/-- **Right partial sums from a pointwise bound**: if the data exceed `−λ` right of the seed (off the jumps), every
right partial sum of the flow-line word from `0` exceeds `−2`. -/
theorem neg_two_lt_sum_flowLineRhoR_of_forall {k : ℝ} (hk : 0 < k) (hd : IsPiecewiseConstantBoundaryData d J)
    (hR : ∀ y, 0 < y → y ∉ J → -sleLambda k < d y) (i : Fin (flowLineNR d J 0)) :
    -2 < ∑ l ∈ univ.filter (fun l => l ≤ i), flowLineRhoR k d J 0 0 l := by
  rw [filter_le_eq_filter_flowLineXR_le]
  obtain ⟨y, hy, hyJ, hS⟩ := Sec5.Aux22ChartE.exists_sum_flowLineRhoR_eq hk hd (flowLineXR_nonneg d J i)
  rw [hS, Sec4.cumWeightRight]
  have hl := Sec4.sleLambda_pos hk
  have := hR y (lt_of_le_of_lt (flowLineXR_nonneg d J i) hy) hyJ
  have h1 : -1 < d y / sleLambda k := by rw [lt_div_iff₀ hl]; linarith
  linarith

/-- **Left partial sums from a pointwise bound**: if the data are below `λ` left of the seed (off the jumps), every
left partial sum of the flow-line word from `0` exceeds `−2`. -/
theorem neg_two_lt_sum_flowLineRhoL_of_forall {k : ℝ} (hk : 0 < k) (hd : IsPiecewiseConstantBoundaryData d J)
    (hL : ∀ y, y < 0 → y ∉ J → d y < sleLambda k) (i : Fin (flowLineNL d J 0)) :
    -2 < ∑ l ∈ univ.filter (fun l => l ≤ i), flowLineRhoL k d J 0 0 l := by
  rw [filter_le_eq_filter_le_flowLineXL]
  obtain ⟨y, -, hy, hyJ, hS⟩ := Sec5.Aux22ChartE.exists_sum_flowLineRhoL_eq hk hd
    (lo := flowLineXL d J 0 i - 1) (by linarith) (flowLineXL_nonpos d J i)
  rw [hS, Sec4.cumWeightLeft]
  have hl := Sec4.sleLambda_pos hk
  have := hL y (lt_of_lt_of_le hy (flowLineXL_nonpos d J i)) hyJ
  have h1 : d y / sleLambda k < 1 := by rw [div_lt_iff₀ hl]; linarith
  have h2 : -d y / sleLambda k = -(d y / sleLambda k) := neg_div _ _
  linarith

/-- **A pointwise bound from the right partial sums**: if every right partial sum of the flow-line word from `0`
exceeds `−2`, the data exceed `−λ` right of the seed (off the jumps). -/
theorem neg_lambda_lt_of_sum_flowLineRhoR {k : ℝ} (hk : 0 < k) (hd : IsPiecewiseConstantBoundaryData d J)
    (hR : ∀ i : Fin (flowLineNR d J 0), -2 < ∑ l ∈ univ.filter (fun l => l ≤ i), flowLineRhoR k d J 0 0 l)
    {y : ℝ} (hy : 0 < y) (hyJ : y ∉ J) : -sleLambda k < d y := by
  set S := univ.filter (fun l => flowLineXR d J 0 l ≤ y) with hSdef
  have hne : S.Nonempty := by
    refine ⟨⟨0, by unfold flowLineNR; omega⟩, Finset.mem_filter.2 ⟨mem_univ _, ?_⟩⟩
    have : flowLineXR d J 0 ⟨0, by unfold flowLineNR; omega⟩ = 0 := rfl
    rw [this]; exact hy.le
  set m := S.max' hne with hm
  have hm' : flowLineXR d J 0 m ≤ y := (Finset.mem_filter.1 (S.max'_mem hne)).2
  have hmono : StrictMono (flowLineXR d J 0) := fun _ _ h => GW0.flowLineXR_lt d J 0 h
  have hSeq : S = univ.filter (fun l => l ≤ m) := Finset.filter_congr fun l _ =>
    ⟨fun h => S.le_max' l (Finset.mem_filter.2 ⟨mem_univ _, h⟩), fun h => (hmono.monotone h).trans hm'⟩
  have hsum := Sec4.cumWeightRight_forceBoundaryData hk (flowLineRhoL k d J 0 0) (flowLineRhoR k d J 0 0)
    (flowLineXL d J 0) (flowLineXR d J 0) hy.le
  rw [Sec4.forceBoundaryData_flowLine hk hd hy.ne' hyJ, ← hSdef, hSeq, Sec4.cumWeightRight] at hsum
  have h2 := hR m
  rw [← hsum] at h2
  have hl := Sec4.sleLambda_pos hk
  have h3 : -1 < d y / sleLambda k := by linarith
  rw [lt_div_iff₀ hl] at h3
  linarith

/-- **A pointwise bound from the left partial sums**: if every left partial sum of the flow-line word from `0`
exceeds `−2`, the data are below `λ` left of the seed (off the jumps). -/
theorem lt_lambda_of_sum_flowLineRhoL {k : ℝ} (hk : 0 < k) (hd : IsPiecewiseConstantBoundaryData d J)
    (hL : ∀ i : Fin (flowLineNL d J 0), -2 < ∑ l ∈ univ.filter (fun l => l ≤ i), flowLineRhoL k d J 0 0 l)
    {y : ℝ} (hy : y < 0) (hyJ : y ∉ J) : d y < sleLambda k := by
  set S := univ.filter (fun l => y < flowLineXL d J 0 l) with hSdef
  have hne : S.Nonempty := by
    refine ⟨⟨0, by unfold flowLineNL; omega⟩, Finset.mem_filter.2 ⟨mem_univ _, ?_⟩⟩
    have : flowLineXL d J 0 ⟨0, by unfold flowLineNL; omega⟩ = 0 := rfl
    rw [this]; exact hy
  set m := S.max' hne with hm
  have hm' : y < flowLineXL d J 0 m := (Finset.mem_filter.1 (S.max'_mem hne)).2
  have hanti : StrictAnti (flowLineXL d J 0) := fun _ _ h => GW0.flowLineXL_lt d J 0 h
  have hSeq : S = univ.filter (fun l => l ≤ m) := Finset.filter_congr fun l _ =>
    ⟨fun h => S.le_max' l (Finset.mem_filter.2 ⟨mem_univ _, h⟩), fun h => hm'.trans_le (hanti.antitone h)⟩
  have hfb := Sec4.forceBoundaryData_of_neg (κ := k) (flowLineRhoL k d J 0 0) (flowLineRhoR k d J 0 0)
    (flowLineXL d J 0) (flowLineXR d J 0) hy
  rw [Sec4.forceBoundaryData_flowLine hk hd hy.ne hyJ, ← hSdef, hSeq] at hfb
  have h2 := hL m
  have hl := Sec4.sleLambda_pos hk
  rw [hfb]
  nlinarith

end Word

/-! ### Elementary facts -/

/-- The map `x ↦ −1/x` sends `(−1/u, −1/v)` into `(u, v)` when `u < v` have the same sign. -/
theorem negInv_mem_Ioo {u v x : ℝ} (huv : u < v) (hs : 0 < u ∨ v < 0) (hx : x ∈ Ioo (-u⁻¹) (-v⁻¹)) :
    -x⁻¹ ∈ Ioo u v := by
  rcases hs with hu | hv
  · have hv : 0 < v := hu.trans huv
    have hx0 : x < 0 := hx.2.trans (neg_neg_of_pos (inv_pos.2 hv))
    have h1 : v⁻¹ < -x := by linarith [hx.2]
    have h2 : -x < u⁻¹ := by linarith [hx.1]
    have hnx : 0 < -x := by linarith
    have e : -x⁻¹ = (-x)⁻¹ := by rw [inv_neg]
    rw [e]
    constructor
    · rw [← inv_inv u]; exact (inv_lt_inv₀ (inv_pos.2 hu) hnx).2 h2
    · rw [← inv_inv v]; exact (inv_lt_inv₀ hnx (inv_pos.2 hv)).2 h1
  · have hu : u < 0 := huv.trans hv
    have hx0 : 0 < x := lt_trans (neg_pos.2 (inv_lt_zero.2 hu)) hx.1
    have h1 : (-u)⁻¹ < x := by rw [inv_neg]; exact hx.1
    have h2 : x < (-v)⁻¹ := by rw [inv_neg]; exact hx.2
    have hnu : 0 < -u := by linarith
    have hnv : 0 < -v := by linarith
    have h3 : x⁻¹ < -u := by rw [← inv_inv (-u)]; exact (inv_lt_inv₀ hx0 (inv_pos.2 hnu)).2 h1
    have h4 : -v < x⁻¹ := by rw [← inv_inv (-v)]; exact (inv_lt_inv₀ (inv_pos.2 hnv) hx0).2 h2
    constructor <;> linarith

/-- `x ↦ −1/x` is an involution. -/
theorem negInv_negInv (x : ℝ) : -(-x⁻¹)⁻¹ = x := by rw [inv_neg, inv_inv, neg_neg]

/-- `−1/t` avoids the exceptional set `{0} ∪ R(S)` when `t ≠ 0` avoids `S`. -/
theorem negInv_notMem_returnExcept {S : Finset ℝ} {t : ℝ} (ht0 : t ≠ 0) (htS : t ∉ S) :
    -t⁻¹ ∉ Sec7.StripSysField.returnExcept S := by
  intro h
  rcases Finset.mem_insert.1 h with h0 | hm
  · exact ht0 (inv_eq_zero.1 (neg_eq_zero.1 h0))
  · obtain ⟨w, hw, hwe⟩ := Finset.mem_image.1 hm
    have : w = t := inv_injective (neg_injective hwe)
    exact htS (this ▸ hw)

/-- The counterflow data right of `0`: `b'(y) = −g(−1/y) + πχ` (`χ(16/κ) = −χ`). -/
theorem counterflowData_of_pos {κ : ℝ} (hκ : 0 < κ) (g : ℝ → ℝ) {y : ℝ} (hy : 0 < y) :
    Sec7.StripSysField.counterflowData κ g y = -g (-y⁻¹) + Real.pi * QuantumZipper.chiC κ := by
  simp only [Sec7.StripSysField.counterflowData, Sec7.StripSysField.inverseData, Sec7.StripSysField.returnData,
    Sec7.StripSysField.cfOffset, Sec7.StripSysField.cfCoeff, Sec7.StripSysField.liftBoundary, not_lt.2 hy.le,
    ↓reduceIte, Sec4.chiC_sixteen_div hκ]
  ring

/-- The counterflow data left of `0`: `b'(y) = −g(−1/y) − πχ` (the inverse argument `2π` on the negative ray). -/
theorem counterflowData_of_neg {κ : ℝ} (hκ : 0 < κ) (g : ℝ → ℝ) {y : ℝ} (hy : y < 0) :
    Sec7.StripSysField.counterflowData κ g y = -g (-y⁻¹) - Real.pi * QuantumZipper.chiC κ := by
  simp only [Sec7.StripSysField.counterflowData, Sec7.StripSysField.inverseData, Sec7.StripSysField.returnData,
    Sec7.StripSysField.cfOffset, Sec7.StripSysField.cfCoeff, Sec7.StripSysField.liftBoundary, hy,
    ↓reduceIte, Sec4.chiC_sixteen_div hκ]
  ring

/-- A point of the physical set of a history that is not on an ordinary piece is its root or a point of a recorded
original-boundary connector. -/
theorem mem_physSet_cases {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {spec : ExplSpec}
    {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {p : ℂ} (hp : p ∈ ExplState.physSet κ b jumps spec D)
    (hpo : p ∉ ExplState.ordinarySet κ b jumps spec D) :
    p = (spec.1 : ℂ) ∨ ∃ a ∈ (ExplState.run κ b jumps spec D spec.2.2.length).2.1, ∃ t ∈ a, p = (t : ℂ) := by
  simp only [ExplState.physSet, mem_union, mem_singleton_iff, mem_iUnion] at hp
  rcases hp with (h | h) | ⟨a, ha, t, ht, rfl⟩
  · exact Or.inl h
  · exact absurd (by simpa only [ExplState.ordinarySet, mem_iUnion] using h) hpo
  · exact Or.inr ⟨a, ha, t, ht, rfl⟩

/-- **Generic boundary points of a component chart**: every nonempty open interval contains a point `x`, off a given
finite set, with a boundary limit `p` (on `R` if `x > 0`, on `L` if `x < 0`) that is not one of finitely many given
real points. -/
theorem exists_generic {R L C : Set ℂ} {c : Chart} (hch : IsComponentChart R L C c) (hCo : IsOpen C)
    {a b : ℝ} (hab : a < b) (Ex E : Finset ℝ) :
    ∃ x ∈ Ioo a b, x ∉ Ex ∧ ∃ p : ℂ, Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 p) ∧ (0 < x → p ∈ R) ∧
      (x < 0 → p ∈ L) ∧ ∀ t ∈ E, p ≠ (t : ℂ) := by
  have hlim := hch.2.2.2.2.1
  obtain ⟨x, hx, hxE, hgood⟩ := exists_mem_Ioo_tendsto_ne (differentiableOn_inv_of_isComponentChart hch hCo)
    hch.2.2.2.1.2.injOn (fun x => (hlim x).imp fun p hp => hp.1) hab Ex.finite_toSet E.finite_toSet
  obtain ⟨p, hp, hpR, hpL⟩ := hlim x
  exact ⟨x, hx, fun h => hxE (Finset.mem_coe.2 h), p, hp, hpR, hpL, fun t ht => hgood p hp t (Finset.mem_coe.2 ht)⟩

/-! ### The word bounds -/

/-- **Named input: the real connectors of the two walks lie on their own original sides** (Lemma GW1,
`source/spec/p577-624.md` L931–L932, p. 618: the right walk starts at `x = 0`, and "Every nontrivial real connector is
rightward, every restart uses a previously unpassed original right mark"; "Reflection gives the left boundary walk
`L`"; Theorem GW4, proof, p. 637: "Every nontrivial real interval in `R` is on the original right boundary, and every
such interval in `L` is on the original left boundary"). Binders of `GW4.GW3WordBoundStatement` up to the walks:
almost surely every recorded original-boundary connector of the right walk lies in `[0, ∞)` and every one of the left
walk in `(−∞, 0]`. (Every connector recorded by `ExplState.contStep` is a nontrivial interval.) -/
def WalkConnectorSideStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      let wR := boundaryWalkSpec b jumps (-(Real.pi / 2)) true
      let wL := boundaryWalkSpec b jumps (Real.pi / 2) false
      ∀ᵐ ω₀ ∂P,
        (∀ a ∈ (ExplState.run κ b jumps wR (fun k => E wR k ω₀) wR.2.2.length).2.1, a ⊆ Ici 0) ∧
        ∀ a ∈ (ExplState.run κ b jumps wL (fun k => E wL k ω₀) wL.2.2.length).2.1, a ⊆ Iic 0

/-- **Named input: the components between the walks are open** (Lemma GW3, p. 636: "a nondegenerate Jordan component";
both alternatives of `GW3.GW3GeometryStatement` contain it, `betweenComponentsOpenStatement_of_geometry`). Binders of
`GW3.GW3GeometryStatement`: almost surely every component between the walks is an open set. -/
def BetweenComponentsOpenStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      ∀ᵐ ω₀ ∂P,
        ∀ C ∈ betweenComponents
            (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
              (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω₀))
            (ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
              (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω₀)),
          IsOpen C

/-- The between-region geometry gives open components. -/
theorem betweenComponentsOpenStatement_of_geometry (hG : GW3.GW3GeometryStatement.{u}) :
    BetweenComponentsOpenStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE
  filter_upwards [hG κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE] with ω₀ hω C hC
  rcases hω C hC with hJ | hO
  · exact hJ.1
  · exact hO.1

/-- **Lemma GW3's word bounds (GW3.2), `−2 < S_L, S_R`**, from the openness of the between-components (named
input `BetweenComponentsOpenStatement`, a consequence of the geometry), Lemma GW0's forward implication (the ambient
counterflow word is admissible) and the side of the walks' real connectors (Lemma GW3, proof, p. 637: "On a flow
flank `H_R = −Λ` or `H_L = Λ`, both formulas equal `c − 2 = d`. On a lower real connector, its original ambient
counterflow sum is `(H_R + πχ)/Λ − 1 > −2`"). The component word is read at generic boundary points, where the
boundary limit is not an original jump or the root (`exists_generic`: the boundary map of a conformal chart is not
constant on an interval). -/
theorem gw3WordBoundStatement_of_inputs (hO : BetweenComponentsOpenStatement.{u})
    (hGW0 : GW0.GW0ForwardStatement.{u}) (hS : WalkConnectorSideStatement.{u}) : GW4.GW3WordBoundStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE wR wL
  have hχ := Sec4.chiC_pos hκ hκ4
  have hπχ : 0 < Real.pi * QuantumZipper.chiC κ := mul_pos Real.pi_pos hχ
  have hκ' : 0 < 16 / κ := div_pos (by norm_num) hκ
  have hΛ := Sec4.sleLambda_sixteen_div_eq_sub hκ
  -- the ambient counterflow word is admissible (GW0), so the original data obey the ambient bounds
  obtain ⟨h'a, -, hfla⟩ := GW2Cone.isFlowLineDriver_counterflowData hκ hb hh hcf
  obtain ⟨hAL, hAR⟩ := GW0.counterflow_admissible hGW0 hκ hκ4 hfla hζ'
  have hcfb := Sec7.StripSysField.isPiecewiseConstant_counterflowData κ hb
  have hbneg : ∀ t, t < 0 → t ∉ jumps →
      b t < sleLambda (16 / κ) + Real.pi * QuantumZipper.chiC κ := by
    intro t ht htJ
    have hy : 0 < -t⁻¹ := neg_pos.2 (inv_lt_zero.2 ht)
    have h1 := neg_lambda_lt_of_sum_flowLineRhoR hκ' hcfb hAR hy (negInv_notMem_returnExcept ht.ne htJ)
    rw [counterflowData_of_pos hκ b hy, negInv_negInv] at h1
    linarith
  have hbpos : ∀ t, 0 < t → t ∉ jumps →
      -sleLambda (16 / κ) - Real.pi * QuantumZipper.chiC κ < b t := by
    intro t ht htJ
    have hy : -t⁻¹ < 0 := neg_neg_of_pos (inv_pos.2 ht)
    have h1 := lt_lambda_of_sum_flowLineRhoL hκ' hcfb hAL hy (negInv_notMem_returnExcept ht.ne' htJ)
    rw [counterflowData_of_neg hκ b hy, negInv_negInv] at h1
    linarith
  filter_upwards [hO κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE,
    hS κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE] with ω₀ hOω hSω
  intro R L ν C hCm c hC bC jumpsC hch htr hpc hbd hgff b' J' h' WC ζC hb' htr' hfl
  have hν : IsProbabilityMeasure ν := by
    show IsProbabilityMeasure (condExpKernel P _ ω₀)
    infer_instance
  have hCo : IsOpen C := hOω C hCm
  -- the data `b'` of the component counterflow agree with the counterflow data of `bC` off a finite set
  have hgff' : IsGFFWithBoundaryData ν h' b' J' := by
    obtain ⟨h'', 𝓕, VL, VR, B, htac, hcoup⟩ := hfl
    have e : h'' = h' := funext fun ω => GW2Cone.eq_of_isTranslateAddConst_zero (zero_mul _) (htac ω)
    subst e
    exact Sec7.StripSysField.isGFFWithBoundaryData_of_flowLineGFF hκ' hb' ⟨hcoup.2.1, hcoup.2.2.1⟩
  have hoff := GW2Cone.eq_counterflowData_off hpc hb' hgff htr' hgff'
  set F1 := Sec7.StripSysField.returnExcept (jumpsC ∪ Sec7.StripSysField.returnExcept J') with hF1
  set Ex : Finset ℝ := jumpsC ∪ F1.image (fun z => -z⁻¹) with hEx
  set E0 : Finset ℝ := insert 0 jumps with hE0
  -- the generic-point argument on either side
  have key : ∀ y, y ≠ 0 → y ∉ J' → ∃ x : ℝ, x ≠ 0 ∧ x ∉ jumpsC ∧ b' y = Sec7.StripSysField.counterflowData κ bC (-x⁻¹) ∧
      (0 < y ↔ x < 0) ∧ ∃ p : ℂ, Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 p) ∧ (0 < x → p ∈ R) ∧ (x < 0 → p ∈ L) ∧
        ∀ t ∈ E0, p ≠ (t : ℂ) := by
    intro y hy0 hyJ
    obtain ⟨ε, hε, hloc⟩ := Metric.eventually_nhds_iff.1 (hb' y hyJ)
    set δ := min ε |y| / 2 with hδ
    have hya : 0 < |y| := abs_pos.2 hy0
    have hδ0 : 0 < δ := by rw [hδ]; exact half_pos (lt_min hε hya)
    have hδε : δ < ε := by rw [hδ]; linarith [min_le_left ε |y|]
    have hδy : δ < |y| := by rw [hδ]; linarith [min_le_right ε |y|]
    have hs : 0 < y - δ ∨ y + δ < 0 := by
      rcases lt_or_gt_of_ne hy0 with hn | hp
      · right; rw [abs_of_neg hn] at hδy; linarith
      · left; rw [abs_of_pos hp] at hδy; linarith
    have hlt : -(y - δ)⁻¹ < -(y + δ)⁻¹ := by
      rcases hs with hp | hn
      · exact neg_lt_neg ((inv_lt_inv₀ (by linarith) hp).2 (by linarith))
      · exact neg_lt_neg ((inv_lt_inv₀ (by linarith : 0 < -(y - δ)) (by linarith : 0 < -(y + δ))).2
          (by linarith) |> fun h => by rw [inv_neg, inv_neg] at h; linarith)
    obtain ⟨x, hx, hxE, p, hp, hpR, hpL, hpE⟩ := exists_generic hch hCo hlt Ex E0
    have hy'' := negInv_mem_Ioo (by linarith) hs hx
    have hx0 : x ≠ 0 := by
      intro h0
      rw [h0, inv_zero, neg_zero] at hy''
      rcases hs with hp' | hn'
      · linarith [hy''.1]
      · linarith [hy''.2]
    have hxJ : x ∉ jumpsC := fun h => hxE (Finset.mem_union_left _ h)
    have hF : -x⁻¹ ∉ F1 := fun h => hxE (Finset.mem_union_right _ (Finset.mem_image.2 ⟨_, h, negInv_negInv x⟩))
    have hdist : dist (-x⁻¹) y < ε := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hy''.1, hy''.2]
    refine ⟨x, hx0, hxJ, ?_, ?_, p, hp, hpR, hpL, hpE⟩
    · rw [← hloc hdist, hoff _ hF]
    · constructor
      · intro hy
        by_contra hxn
        have hxp : 0 < x := lt_of_le_of_ne (not_lt.1 hxn) (Ne.symm hx0)
        have : -x⁻¹ < 0 := neg_neg_of_pos (inv_pos.2 hxp)
        rcases hs with hp' | hn'
        · linarith [hy''.1]
        · linarith
      · intro hxn
        have : 0 < -x⁻¹ := neg_pos.2 (inv_lt_zero.2 hxn)
        rcases hs with hp' | hn'
        · linarith
        · linarith [hy''.2]
  have hR0 : (wR.1 : ℂ) = 0 := by simp [wR, boundaryWalkSpec]
  have hL0 : (wL.1 : ℂ) = 0 := by simp [wL, boundaryWalkSpec]
  have hR' : ∀ y, 0 < y → y ∉ J' → -sleLambda (16 / κ) < b' y := by
    intro y hy hyJ
    obtain ⟨x, hx0, hxJ, hb'x, hsign, p, hp, -, hpL, hpE⟩ := key y hy.ne' hyJ
    have hxn : x < 0 := hsign.1 hy
    rw [hb'x, counterflowData_of_pos hκ _ (neg_pos.2 (inv_lt_zero.2 hxn)), negInv_negInv,
      (hbd x hxJ p hp).2 hxn]
    split_ifs with hpo
    · rw [hΛ]; linarith
    · rcases mem_physSet_cases (hpL hxn) hpo with h0 | ⟨a, ha, t, ht, rfl⟩
      · exact absurd (h0.trans hL0) (hpE 0 (Finset.mem_insert_self _ _))
      · have ht0 : t ≤ 0 := hSω.2 a ha ht
        have htne : t ≠ 0 := fun h0 => hpE 0 (Finset.mem_insert_self _ _) (by rw [h0])
        have htJ : t ∉ jumps := fun hj => hpE t (Finset.mem_insert_of_mem hj) rfl
        rw [Complex.ofReal_re]
        linarith [hbneg t (lt_of_le_of_ne ht0 htne) htJ]
  have hL' : ∀ y, y < 0 → y ∉ J' → b' y < sleLambda (16 / κ) := by
    intro y hy hyJ
    obtain ⟨x, hx0, hxJ, hb'x, hsign, p, hp, hpR, -, hpE⟩ := key y hy.ne hyJ
    have hxp : 0 < x := lt_of_le_of_ne (not_lt.1 fun h => absurd (hsign.2 h) (not_lt.2 hy.le)) (Ne.symm hx0)
    rw [hb'x, counterflowData_of_neg hκ _ (neg_neg_of_pos (inv_pos.2 hxp)), negInv_negInv,
      (hbd x hxJ p hp).1 hxp]
    split_ifs with hpo
    · rw [hΛ]; linarith
    · rcases mem_physSet_cases (hpR hxp) hpo with h0 | ⟨a, ha, t, ht, rfl⟩
      · exact absurd (h0.trans hR0) (hpE 0 (Finset.mem_insert_self _ _))
      · have ht0 : 0 ≤ t := hSω.1 a ha ht
        have htne : t ≠ 0 := fun h0 => hpE 0 (Finset.mem_insert_self _ _) (by rw [h0])
        have htJ : t ∉ jumps := fun hj => hpE t (Finset.mem_insert_of_mem hj) rfl
        rw [Complex.ofReal_re]
        linarith [hbpos t (lt_of_le_of_ne ht0 (Ne.symm htne)) htJ]
  exact ⟨neg_two_lt_sum_flowLineRhoL_of_forall hκ' hb' hL', neg_two_lt_sum_flowLineRhoR_of_forall hκ' hb' hR'⟩

/-- **Theorem 1.4, component kernels** (Specification p. 5), with exactly the binders and conclusion of the frozen
`IsCenteredCounterflowDriver.componentKernels`, from the between-region geometry, GW3's field law, Lemma GW0's forward
implication, the sides of the walks' real connectors, GW4's traversal core and Theorems 1.2–1.3 (GW3's word bounds are
`gw3WordBoundStatement_of_inputs`). -/
theorem componentKernels_of_gw3Inputs (hG : GW3.GW3GeometryStatement.{u}) (hF : GW4.GW3FieldLawStatement.{u})
    (hGW0 : GW0.GW0ForwardStatement.{u}) (hS : WalkConnectorSideStatement.{u})
    (hT : GW4.GW4TraversalCoreStatement.{u}) (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u})
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (b : ℝ → ℝ) (jumps : Finset ℝ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hh : IsGFFWithBoundaryData P h b jumps)
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞}
    (hcf : IsCenteredCounterflowDriver κ P h W' ζ') (hζ' : ∀ᵐ ω ∂P, ζ' ω = ⊤)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
      IsStagedHistory κ b jumps P h spec (E spec)) :
    let wR := boundaryWalkSpec b jumps (-(Real.pi / 2)) true
    let wL := boundaryWalkSpec b jumps (Real.pi / 2) false
    ∀ᵐ ω₀ ∂P,
      let R := ExplState.physSet κ b jumps wR (fun k => E wR k ω₀)
      let L := ExplState.physSet κ b jumps wL (fun k => E wL k ω₀)
      let ν := condExpKernel P
        (pastSigma κ b jumps wR (E wR) wR.2.2.length ⊔ pastSigma κ b jumps wL (E wL) wL.2.2.length) ω₀
      (∀ C ∈ betweenComponents R L, ∃ c : Chart, IsComponentChart R L C c) ∧
      ∀ cs : Set ℂ → Chart, (∀ C ∈ betweenComponents R L, IsComponentChart R L C (cs C)) →
        ∃ (ℓ : Set ℂ → ℂ → ℝ) (hC : Set ℂ → Ω → LQGMetric.DistOn upperHalfPlaneOpens)
          (WC : Set ℂ → ℝ≥0 → Ω → ℝ) (ζC : Set ℂ → Ω → ℝ≥0∞),
          (∀ C ∈ betweenComponents R L,
            IsComponentChart R L C ((cs C).1, (cs C).2.1, ℓ C) ∧
            (∀ ω, IsChartTransport ((cs C).1, (cs C).2.1, ℓ C) 1 0 (QuantumZipper.chiC κ) (h ω)
              (hC C ω)) ∧
            (∃ (bC : ℝ → ℝ) (jumpsC : Finset ℝ), IsPiecewiseConstantBoundaryData bC jumpsC ∧
              IsComponentBoundaryData κ b (ExplState.ordinarySet κ b jumps wR (fun k => E wR k ω₀))
                (ExplState.ordinarySet κ b jumps wL (fun k => E wL k ω₀)) (cs C).2.1 bC jumpsC ∧
              IsGFFWithBoundaryData ν (hC C) bC jumpsC) ∧
            IsCenteredCounterflowDriver κ ν (hC C) (WC C) (ζC C) ∧
            ∀ᵐ ω ∂ν, ζC C ω = ⊤ ∧
              IsComponentTraversal (cs C).2.1 (fun t => W' t ω) (fun t => WC C t ω)) ∧
          iIndepFun (fun (C : betweenComponents R L) ω => (hC C ω, fun t => WC C t ω)) ν :=
  GW4.componentKernels_of_gw4Core hG hF
    (gw3WordBoundStatement_of_inputs (betweenComponentsOpenStatement_of_geometry hG) hGW0 hS) hT h12 h13 hκ hκ4 b
    jumps hb hh hcf hζ' E hE

end GW3Word

end Theorem14

end InteractingSLE
