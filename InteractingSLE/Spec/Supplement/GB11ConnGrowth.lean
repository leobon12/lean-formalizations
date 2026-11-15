/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB11RelParam
import InteractingSLE.Foundations.Topology.JaniszewskiHalfPlane

/-!
# Lemma GB11's relative active component: connectivity (GB11.2) from the chart's boundary correspondence

Packet PROVE-T14-GW4T4, item (1). Lemma GB11 (`source/spec/p529-576.md` L651–L679, p. 556): "Its relative active
component is exactly the original active component intersected with `C`" — in the form left open by PROVE-T14-GW4T3
(`GW4Reg.GB11RelConnGrowthStatement`, first conjunct): for every ambient time `t` of the traversal, `τ ≤ t < σ`, the
part `R⁻¹(C) \ K'_t` of the reversed pocket outside the ambient hull is preconnected. Source argument: "active access
of the unvisited incoming prefix".

## The boundary correspondence of the chart

The frozen `IsComponentChart` gives boundary limits of the inverse chart at every real point, on the right walk for
positive and on the left walk for negative points, but not the order in which the walls are traversed (Carathéodory's
boundary homeomorphism of a Jordan pocket). `ChartBdryCorr` records exactly that, read in the relative chart
`Φ = relMapC c` (`Φ(y_C) = 0`, `Φ(x_C) = ∞`; positive reals correspond to the left wall, negative reals to the right
wall): a boundary function `e : ℝ → ℂ` (the limits of `Φ⁻¹ = relInvC c`), with `e x = R⁻¹(α_L(r_L x))` for `x > 0`,
`r_L` antitone (from the entry `α_L(t₂)` near `0⁺` to the exit `α_L(t₁)` near `+∞`), `e x = R⁻¹(α_R(r_R x))` for
`x < 0`, `r_R` monotone, and `e 0` the entry (`0`, the chart image of the original source, for the unbounded pocket).
It concerns the pocket and its chart only, not the trace.

## The argument (`isPreconnected_relDom_diff_fwdHull`)

Work in `Φ`-coordinates: `B = Φ(K'_t ∩ R⁻¹(C))` is bounded (`GW4Reg.isBounded_relHull`), and `U = ℍ \ B` is the
image of `R⁻¹(C) \ K'_t`. All points of `ℍ` far out lie in one component of `U`
(`mem_connectedComponentIn_of_le_norm`), so it suffices that every component `V` of `U` has a far point. Suppose not.
* If the closure of `V` contains a real `x ≠ 0` whose wall point `e x` is not yet visited at `t`, then by the reverse
  first-visit order of the walls and the monotonicity of `r_L`, `r_R` every real point beyond `x` (on the same side)
  is unvisited; an unvisited wall point is not in the closure of `K'_t` (`GW4Reg.notMem_closure_fwdHull_of_lt`: it is
  visited later), so each such point has a half-disc neighbourhood in `U`; these half-discs propagate `V` out to
  infinity (`exists_far_mem_of_forall_halfDisc`).
* Otherwise every real point of the closure of `V` is visited (or is `0`, whose wall point is the entry, visited at
  `τ ≤ t`). Then `O = Φ⁻¹(V)` has its frontier in `ℍ` inside the trace `γ([0, t])`: inside `R⁻¹(C)` a frontier point
  of `O` lies in `K'_t` and in the closure of `ℍ \ K'_t`, hence on the trace (the filling property); outside it, it is
  a limit of `Φ⁻¹(v_n)` with `v_n → x ∈ ℝ`, i.e. the wall point `e x`, visited by `t`. So `O` is clopen in
  `ℍ \ γ([0, t])` and contains the active component `ℍ \ K'_t`; then `V = U`, which has far points.

## Main results

* `ChartBdryCorr`, **`isPreconnected_relDom_diff_fwdHull`** (deterministic);
* `GB11ChartBdryStatement` (named input: the boundary correspondence of the pocket charts in GB11's setting),
  `GB11RelLocalGrowthStatement` (the growth half of `GW4Reg.GB11RelConnGrowthStatement`, verbatim);
* **`gb11RelConnGrowthStatement_of_bdry`**: `GB11RelConnGrowthStatement` from these two;
  `gb11RelParamStatement_of_bdry`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull)

namespace InteractingSLE

namespace Theorem14

namespace GB11Conn

/-! ### Generic planar facts -/

/-- A point of the closure of a connected component of `F` that lies in `F` lies in the component. -/
theorem mem_connectedComponentIn_of_mem_closure {F : Set ℂ} {z q : ℂ}
    (hq : q ∈ closure (connectedComponentIn F z)) (hqF : q ∈ F) : q ∈ connectedComponentIn F z := by
  set S := connectedComponentIn F z with hS
  have hzF : z ∈ F := by
    by_contra hz
    rw [hS, connectedComponentIn_eq_empty hz, closure_empty] at hq
    exact hq
  have hsub : S ⊆ insert q S := subset_insert q S
  have hcl : insert q S ⊆ closure S := insert_subset hq subset_closure
  have hpre : IsPreconnected (insert q S) := isPreconnected_connectedComponentIn.subset_closure hsub hcl
  have hF : insert q S ⊆ F := insert_subset hqF (connectedComponentIn_subset F z)
  exact hpre.subset_connectedComponentIn (hsub (mem_connectedComponentIn hzF)) hF (mem_insert q S)

/-- **No bounded components.** If `U ⊆ ℍ` misses only a part of `ℍ` inside `ball 0 R` and every component of `U`
has a point of norm `≥ R`, then `U` is preconnected. -/
theorem isPreconnected_of_forall_far {U : Set ℂ} {R : ℝ} (hR : 0 < R) (hUH : U ⊆ H)
    (hB : H \ U ⊆ ball 0 R) (hfar : ∀ v ∈ U, ∃ z ∈ connectedComponentIn U v, R ≤ ‖z‖) : IsPreconnected U := by
  have hHU : H \ (H \ U) = U := by
    ext z
    exact ⟨fun hz => by_contra fun h => hz.2 ⟨hz.1, h⟩, fun hz => ⟨hUH hz, fun h => h.2 hz⟩⟩
  set a₀ : ℂ := (((R + 1 : ℝ) : ℂ) * Complex.I) with ha₀
  have hall : U ⊆ connectedComponentIn U a₀ := by
    intro v hv
    obtain ⟨z, hz, hzR⟩ := hfar v hv
    have hzH : z ∈ H := hUH (connectedComponentIn_subset U v hz)
    have hz₀ : z ∈ connectedComponentIn U a₀ := by
      have := mem_connectedComponentIn_of_le_norm hR hB hzH hzR
      rwa [hHU] at this
    rw [connectedComponentIn_eq hz₀, ← connectedComponentIn_eq hz]
    exact mem_connectedComponentIn hv
  have heq : connectedComponentIn U a₀ = U := (connectedComponentIn_subset U a₀).antisymm hall
  rw [← heq]
  exact isPreconnected_connectedComponentIn

/-- A point near which every upper point lies in `U ⊆ ℍ`, and which is in the closure of a component `V` of `U`:
the whole upper half of the disc lies in `V`. -/
theorem ball_inter_H_subset {U : Set ℂ} (hUH : U ⊆ H) {v y : ℂ} {ε : ℝ} (hU : ∀ w ∈ H, ‖w - y‖ < ε → w ∈ U)
    (hy : y ∈ closure (connectedComponentIn U v)) : ball y ε ∩ H ⊆ connectedComponentIn U v := by
  rcases le_or_gt ε 0 with hε | hε
  · intro w hw
    exact absurd (lt_of_lt_of_le (mem_ball.1 hw.1) hε) (not_lt.2 dist_nonneg)
  obtain ⟨w, hwV, hwd⟩ := Metric.mem_closure_iff.1 hy ε hε
  have hsubU : ball y ε ∩ H ⊆ U := fun w hw => hU w hw.2 (by rw [← dist_eq_norm]; exact hw.1)
  have hwH : w ∈ H := hUH (connectedComponentIn_subset U v hwV)
  have hwb : w ∈ ball y ε ∩ H := ⟨by rw [mem_ball, dist_comm]; exact hwd, hwH⟩
  have h1 := (HalfPlaneSep.isPreconnected_ball_inter_H y ε).subset_connectedComponentIn hwb hsubU
  rwa [← connectedComponentIn_eq hwV] at h1

/-- A real point near `y` is the limit of upper points of the disc `ball y ε`. -/
theorem ofReal_mem_closure_ball_inter_H {y y' : ℝ} {ε : ℝ} (h : |y' - y| < ε) :
    (y' : ℂ) ∈ closure (ball (y : ℂ) ε ∩ H) := by
  refine Metric.mem_closure_iff.2 fun r hr => ?_
  set δ : ℝ := min r (ε - |y' - y|) / 2 with hδ
  have hδ0 : 0 < δ := by
    have : 0 < min r (ε - |y' - y|) := lt_min hr (by linarith)
    positivity
  have hδr : δ < r := by
    have := min_le_left r (ε - |y' - y|)
    linarith
  have hδε : δ < ε - |y' - y| := by
    have := min_le_right r (ε - |y' - y|)
    have : 0 < min r (ε - |y' - y|) := lt_min hr (by linarith)
    linarith
  have hnI : ‖((δ : ℝ) : ℂ) * Complex.I‖ = δ := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_of_nonneg hδ0.le]
  refine ⟨(y' : ℂ) + (δ : ℂ) * Complex.I, ⟨?_, ?_⟩, ?_⟩
  · rw [mem_ball, dist_eq_norm]
    have h1 : (y' : ℂ) + (δ : ℂ) * Complex.I - (y : ℂ) = ((y' - y : ℝ) : ℂ) + (δ : ℂ) * Complex.I := by
      push_cast; ring
    rw [h1]
    calc ‖((y' - y : ℝ) : ℂ) + (δ : ℂ) * Complex.I‖ ≤ ‖((y' - y : ℝ) : ℂ)‖ + ‖(δ : ℂ) * Complex.I‖ :=
          norm_add_le _ _
      _ = |y' - y| + δ := by rw [Complex.norm_real, Real.norm_eq_abs, hnI]
      _ < ε := by linarith
  · show 0 < ((y' : ℂ) + (δ : ℂ) * Complex.I).im
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      Complex.I_re, mul_one, mul_zero, add_zero, zero_add]
    exact hδ0
  · rw [dist_eq_norm]
    have h1 : (y' : ℂ) - ((y' : ℂ) + (δ : ℂ) * Complex.I) = -((δ : ℂ) * Complex.I) := by ring
    rw [h1, norm_neg, hnI]
    exact hδr

/-- **Propagation along a real interval.** Let `U ⊆ ℍ`, `V` a component of `U`, and `I ⊆ ℝ` preconnected and
unbounded, every point of `I` having an upper half-disc neighbourhood in `U`. If some point of `I` is in the closure
of `V`, then `V` has points of arbitrarily large norm. -/
theorem exists_far_mem_of_forall_halfDisc {U : Set ℂ} (hUH : U ⊆ H) {v : ℂ} {I : Set ℝ} (hI : IsPreconnected I)
    (hIu : ∀ R : ℝ, ∃ y ∈ I, R ≤ |y|) (hhd : ∀ y ∈ I, ∃ ε > 0, ∀ w ∈ H, ‖w - (y : ℂ)‖ < ε → w ∈ U)
    {x : ℝ} (hxI : x ∈ I) (hx : (x : ℂ) ∈ closure (connectedComponentIn U v)) (R : ℝ) :
    ∃ z ∈ connectedComponentIn U v, R ≤ ‖z‖ := by
  set V := connectedComponentIn U v with hV
  set Cl : Set ℝ := (fun y : ℝ => (y : ℂ)) ⁻¹' closure V with hCl
  have hClc : IsClosed Cl := isClosed_closure.preimage Complex.continuous_ofReal
  have hint : ∀ y ∈ I, y ∈ Cl → y ∈ interior Cl := by
    intro y hy hyC
    obtain ⟨ε, hε, hU⟩ := hhd y hy
    have hsub := ball_inter_H_subset hUH hU hyC
    refine mem_interior_iff_mem_nhds.2 (Filter.mem_of_superset (Metric.ball_mem_nhds y hε) fun y' hy' => ?_)
    have h1 : |y' - y| < ε := by rw [← Real.dist_eq]; exact hy'
    exact closure_mono hsub (ofReal_mem_closure_ball_inter_H h1)
  have hIsub : I ⊆ interior Cl := by
    refine hI.subset_left_of_subset_union isOpen_interior hClc.isOpen_compl
      (disjoint_compl_right.mono_left interior_subset) (fun y hy => ?_) ⟨x, hxI, hint x hxI hx⟩
    by_cases hyC : y ∈ Cl
    · exact Or.inl (hint y hy hyC)
    · exact Or.inr hyC
  obtain ⟨y, hyI, hyR⟩ := hIu R
  obtain ⟨ε, hε, hU⟩ := hhd y hyI
  have hsub := ball_inter_H_subset hUH hU (interior_subset (hIsub hyI) : y ∈ Cl)
  set z : ℂ := (y : ℂ) + ((ε / 2 : ℝ) : ℂ) * Complex.I with hz
  have hzb : z ∈ ball (y : ℂ) ε ∩ H := by
    have hnI : ‖((ε / 2 : ℝ) : ℂ) * Complex.I‖ = ε / 2 := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_of_nonneg (by positivity)]
    refine ⟨?_, ?_⟩
    · rw [mem_ball, dist_eq_norm, hz, add_sub_cancel_left, hnI]
      linarith
    · show 0 < z.im
      simp only [hz, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
        Complex.I_re, mul_one, mul_zero, add_zero, zero_add]
      positivity
  refine ⟨z, hsub hzb, hyR.trans ?_⟩
  have h1 := Complex.abs_re_le_norm z
  have h2 : z.re = y := by
    simp [hz]
  rwa [h2] at h1

/-! ### The boundary correspondence of a pocket chart -/

open GW4Traverse GW4Reg ConformalImage

/-- **The boundary correspondence of a pocket chart** `c` (Carathéodory's boundary map of the pocket, in the relative
chart `Φ = relMapC c`, entry `↦ 0`, exit `↦ ∞`): the inverse `Φ⁻¹ = relInvC c` has the limit `e x` at every real
`x`; for `x > 0` it is the point `R⁻¹(α_L(r_L x))` of the left wall, `r_L` antitone (the left wall is run from the
entry to the exit as `x` increases); for `x < 0` the point `R⁻¹(α_R(r_R x))` of the right wall, `r_R` monotone; `e 0`
is the entry `R⁻¹(α_R(s₂))` of a bounded pocket and `0` (the original source) for the unbounded one. -/
def ChartBdryCorr (αR αL : ℝ≥0 → ℂ) (c : Chart) (s₂ : ℝ≥0∞) (e : ℝ → ℂ) (rR rL : ℝ → ℝ≥0) : Prop :=
  (∀ x : ℝ, Tendsto (relInvC c) (𝓝[H] (x : ℂ)) (𝓝 (e x))) ∧
    (∀ x : ℝ, 0 < x → αL (rL x) ≠ 0 ∧ e x = -(αL (rL x))⁻¹) ∧ AntitoneOn rL (Ioi 0) ∧
    (∀ x : ℝ, x < 0 → αR (rR x) ≠ 0 ∧ e x = -(αR (rR x))⁻¹) ∧ MonotoneOn rR (Iio 0) ∧
    (s₂ = ⊤ → e 0 = 0) ∧ (s₂ ≠ ⊤ → e 0 = -(αR s₂.toNNReal)⁻¹)

/-! ### Visited and unvisited wall points -/

section Visits

variable {W' : ℝ≥0 → ℝ} {γ α : ℝ≥0 → ℂ}

/-- A wall point other than the target is visited at a finite time (reverse first-visit order). -/
theorem firstVisit_lt_top_of_ne_zero (hα0 : α 0 = 0)
    (hrev : ∀ a a' : ℝ≥0, 0 < a → a < a' → GB11.firstVisit γ (α a') < GB11.firstVisit γ (α a)) {r : ℝ≥0}
    (hr : α r ≠ 0) : GB11.firstVisit γ (α r) < ⊤ := by
  have hr0 : r ≠ 0 := fun h => hr (h ▸ hα0)
  have hpos : 0 < r := pos_iff_ne_zero.2 hr0
  exact lt_of_lt_of_le (hrev (r / 2) r (half_pos hpos) (half_lt_self hpos)) le_top

/-- A wall point first visited by time `t` lies on the trace `γ([0, t])` (in the counterflow chart). -/
theorem negInv_mem_image_of_firstVisit_le (hγc : Continuous γ) {p : ℂ} (hfin : GB11.firstVisit γ p < ⊤)
    {t : ℝ≥0} (ht : GB11.firstVisit γ p ≤ t) : -p⁻¹ ∈ γ '' Icc 0 t := by
  obtain ⟨s₀, hs₀, hne, hp⟩ := exists_eq_firstVisit hγc hfin
  refine ⟨s₀, ⟨zero_le, ?_⟩, ?_⟩
  · rw [← hs₀] at ht
    exact ENNReal.coe_le_coe.1 ht
  · rw [← hp, negInv_negInv']

/-- **An unvisited wall point is not in the closure of the current hull** (it is visited later, off the trace so
far: `notMem_closure_fwdHull_of_lt`). -/
theorem negInv_notMem_closure_of_lt_firstVisit (hW' : Continuous W') (hW'0 : W' 0 = 0)
    (hγ : IsGeneratingTrace W' ⊤ γ) {p : ℂ} (hfin : GB11.firstVisit γ p < ⊤) {t : ℝ≥0}
    (ht : (t : ℝ≥0∞) < GB11.firstVisit γ p) :
    -p⁻¹ ∉ closure (fwdHull (fun r : ℝ => W' r.toNNReal) t) := by
  have hγc : Continuous γ := Sec5.continuous_of_isGeneratingTrace_top hγ
  obtain ⟨s₀, hs₀, hne, hp⟩ := exists_eq_firstVisit hγc hfin
  have hγs₀ : γ s₀ = -p⁻¹ := by rw [← hp, negInv_negInv']
  have hts : t < s₀ := by
    rw [← hs₀] at ht
    exact ENNReal.coe_lt_coe.1 ht
  have hnot : γ s₀ ∉ γ '' Icc 0 t := by
    rintro ⟨s', hs', he⟩
    have h1 : GB11.firstVisit γ p ≤ s' := iInf₂_le s' ⟨he ▸ hne, by rw [he]; exact hp⟩
    have h2 : (s' : ℝ≥0∞) ≤ t := ENNReal.coe_le_coe.2 hs'.2
    exact absurd (h1.trans h2) (not_le.2 ht)
  rw [← hγs₀]
  exact notMem_closure_fwdHull_of_lt hW' hW'0 hγ hts hnot

end Visits

/-! ### The relative active component is connected -/

section Conn

variable {W' : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {αR αL : ℝ≥0 → ℂ} {C : Set ℂ} {c : Chart} {s₁ t₁ : ℝ≥0}
  {s₂ t₂ : ℝ≥0∞} {e : ℝ → ℂ} {rR rL : ℝ → ℝ≥0}

/-- An upper half-disc around a real point whose boundary value is off the closure of `K` lies in the chart image
of `R⁻¹(C) \ K`. -/
theorem exists_halfDisc_of_notMem_closure {R L : Set ℂ} (hc : IsComponentChart R L C c) {K : Set ℂ} {x : ℝ}
    {p : ℂ} (hlim : Tendsto (relInvC c) (𝓝[H] (x : ℂ)) (𝓝 p)) (hp : p ∉ closure K) :
    ∃ ε > 0, ∀ w ∈ H, ‖w - (x : ℂ)‖ < ε → w ∈ relMapC c '' (relDom C \ K) := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl p hp
  have hev := hlim.eventually (Metric.ball_mem_nhds p hr)
  obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhdsWithin_iff.1 hev
  refine ⟨ε, hε, fun w hwH hw => ?_⟩
  have hw' : w ∈ ball (x : ℂ) ε ∩ H := ⟨by rw [mem_ball, dist_eq_norm]; exact hw, hwH⟩
  have h1 : relInvC c w ∉ K := fun hK => hball (hεs hw') (subset_closure hK)
  exact ⟨relInvC c w, ⟨relInvC_mem hc hwH, h1⟩, relMapC_relInvC hc hwH⟩

/-- **(GB11.2), connectivity: the relative active component is connected** (deterministic). Under GB11's barrier
input, for a shaped pocket `C` with a component chart `c` whose boundary correspondence is `ChartBdryCorr`, at every
ambient time `t` of the traversal (`τ ≤ t < σ`) the part `R⁻¹(C) \ K'_t` of the reversed pocket outside the
ambient hull is preconnected. -/
theorem isPreconnected_relDom_diff_fwdHull (hW' : Continuous W') (hW'0 : W' 0 = 0)
    (hγ : IsGeneratingTrace W' ⊤ γ) (hB : GB11.IsGB11Barrier αR αL γ) (hs : IsPocketShape αR αL C s₁ t₁ s₂ t₂)
    (hc : IsComponentChart (range αR) (range αL) C c) (hCo : IsOpen C) (hCH : C ⊆ H)
    (hxC : Tendsto c.2.1 (𝓝[H] 0) (𝓝 (αR s₁))) (hbc : ChartBdryCorr αR αL c s₂ e rR rL) {t : ℝ≥0}
    (hτt : entryTime γ αR s₂ ≤ t) (ht : (t : ℝ≥0∞) < GB11.firstVisit γ (αR s₁)) :
    IsPreconnected (relDom C \ fwdHull (fun r : ℝ => W' r.toNNReal) t) := by
  obtain ⟨hlim, hposL, hantiL, hnegR, hmonoR, he0top, he0⟩ := hbc
  have hγc : Continuous γ := Sec5.continuous_of_isGeneratingTrace_top hγ
  set K := fwdHull (fun r : ℝ => W' r.toNNReal) t with hK
  set A := γ '' Icc 0 t with hA
  have hWc : Continuous fun r : ℝ => W' r.toNNReal := hW'.comp continuous_real_toNNReal
  have hKh : IsHPHull K := isHPHull_fwdHull hWc (NNReal.coe_nonneg t)
  have hDo : IsOpen (relDom C) := isOpen_relDom hCo hCH
  have hDH : relDom C ⊆ H := relDom_subset_H hCH
  have hDKo : IsOpen (relDom C \ K) := by
    have hDKeq : relDom C \ K = relDom C ∩ (H \ K) := by
      ext x
      exact ⟨fun hx => ⟨hx.1, hDH hx.1, hx.2⟩, fun hx => ⟨hx.1, hx.2.2⟩⟩
    rw [hDKeq]
    exact hDo.inter hKh.isOpen
  set B := relMapC c '' (K ∩ relDom C) with hBdef
  set U := H \ B with hUdef
  have hUeq : U = relMapC c '' (relDom C \ K) := H_diff_relHull_eq hc K
  have hUH : U ⊆ H := sdiff_subset
  have hUo : IsOpen U := by
    rw [hUeq, image_relDom_diff_eq hc]
    exact (continuousOn_relInvC hc hCo hCH).isOpen_inter_preimage QuantumZipper.isOpen_H hDKo
  obtain ⟨R, hR, hBR⟩ := (isBounded_relHull hW' hW'0 hγ hB hc hxC ht).subset_ball_lt 0 0
  have hHU : H \ U ⊆ ball 0 R := fun z hz => hBR (by
    by_contra h
    exact hz.2 ⟨hz.1, h⟩)
  -- walls: the reverse first-visit orders
  have hrevR := hB.2.2.2.2.2.1
  have hrevL := hB.2.2.2.2.2.2
  have hαR0 : αR 0 = 0 := hB.1.2.2.1
  have hαL0 : αL 0 = 0 := hB.2.1.2.2.1
  -- a point with an unvisited wall value has a half-disc neighbourhood in `U`
  have hhd : ∀ y : ℝ, ∀ p : ℂ, e y = -p⁻¹ → GB11.firstVisit γ p < ⊤ → (t : ℝ≥0∞) < GB11.firstVisit γ p →
      ∃ ε > 0, ∀ w ∈ H, ‖w - (y : ℂ)‖ < ε → w ∈ U := by
    intro y p hy hfin hlt
    rw [hUeq]
    refine exists_halfDisc_of_notMem_closure hc (hlim y) ?_
    rw [hy]
    exact negInv_notMem_closure_of_lt_firstVisit hW' hW'0 hγ hfin hlt
  -- the far points: every component of `U` has one
  have hfar : ∀ v ∈ U, ∃ z ∈ connectedComponentIn U v, R ≤ ‖z‖ := by
    intro v hv
    set V := connectedComponentIn U v with hVdef
    by_contra hno
    push Not at hno
    by_cases hcase : ∃ x : ℝ, x ≠ 0 ∧ (x : ℂ) ∈ closure V ∧ e x ∉ A
    · obtain ⟨x, hx0, hxV, hxA⟩ := hcase
      rcases lt_or_gt_of_ne hx0 with hxn | hxp
      · -- the right wall side: propagate to `-∞`
        obtain ⟨hne, hex⟩ := hnegR x hxn
        have hfin := firstVisit_lt_top_of_ne_zero hαR0 hrevR hne
        have hlt : (t : ℝ≥0∞) < GB11.firstVisit γ (αR (rR x)) := by
          by_contra hle
          push Not at hle
          exact hxA (hex ▸ negInv_mem_image_of_firstVisit_le hγc hfin (by exact_mod_cast hle))
        obtain ⟨z, hz, hzR⟩ := exists_far_mem_of_forall_halfDisc hUH isPreconnected_Iic
          (fun R' => ⟨min x (-|R'|), mem_Iic.2 (min_le_left _ _), by
            have h1 : min x (-|R'|) ≤ -|R'| := min_le_right _ _
            have h2 : R' ≤ |R'| := le_abs_self R'
            rw [abs_of_neg (lt_of_le_of_lt (min_le_left _ _) hxn)]
            linarith⟩)
          (fun y hy => by
            have hyn : y < 0 := lt_of_le_of_lt hy hxn
            obtain ⟨hne', hey⟩ := hnegR y hyn
            have hfy := firstVisit_anti hαR0 hrevR (hmonoR hyn hxn hy)
            exact hhd y _ hey (firstVisit_lt_top_of_ne_zero hαR0 hrevR hne') (lt_of_lt_of_le hlt hfy))
          (mem_Iic.2 le_rfl) hxV R
        exact absurd hzR (not_le.2 (hno z hz))
      · -- the left wall side: propagate to `+∞`
        obtain ⟨hne, hex⟩ := hposL x hxp
        have hfin := firstVisit_lt_top_of_ne_zero hαL0 hrevL hne
        have hlt : (t : ℝ≥0∞) < GB11.firstVisit γ (αL (rL x)) := by
          by_contra hle
          push Not at hle
          exact hxA (hex ▸ negInv_mem_image_of_firstVisit_le hγc hfin (by exact_mod_cast hle))
        obtain ⟨z, hz, hzR⟩ := exists_far_mem_of_forall_halfDisc hUH isPreconnected_Ici
          (fun R' => ⟨max x |R'|, mem_Ici.2 (le_max_left _ _), by
            have h1 : |R'| ≤ max x |R'| := le_max_right _ _
            have h2 : R' ≤ |R'| := le_abs_self R'
            rw [abs_of_pos (lt_of_lt_of_le hxp (le_max_left _ _))]
            linarith⟩)
          (fun y hy => by
            have hyp : 0 < y := lt_of_lt_of_le hxp hy
            obtain ⟨hne', hey⟩ := hposL y hyp
            have hfy := firstVisit_anti hαL0 hrevL (hantiL hxp hyp hy)
            exact hhd y _ hey (firstVisit_lt_top_of_ne_zero hαL0 hrevL hne') (lt_of_lt_of_le hlt hfy))
          (mem_Ici.2 le_rfl) hxV R
        exact absurd hzR (not_le.2 (hno z hz))
    · push Not at hcase
      -- the entry is visited by `τ ≤ t`
      have he0A : e 0 ∈ H → e 0 ∈ A := by
        intro h0H
        by_cases h2 : s₂ = ⊤
        · rw [he0top h2] at h0H
          exact absurd (show (0 : ℝ) < (0 : ℂ).im from h0H) (lt_irrefl _)
        · rw [he0 h2]
          have hlt : s₁ < s₂.toNNReal := by
            have h := hs.lt
            rw [← ENNReal.coe_toNNReal h2] at h
            exact ENNReal.coe_lt_coe.1 h
          have hne : αR s₂.toNNReal ≠ 0 := fun h =>
            (ne_of_gt (lt_of_le_of_lt zero_le hlt)) (hB.1.2.1 (h.trans hαR0.symm))
          have hfin := firstVisit_lt_top_of_ne_zero hαR0 hrevR hne
          refine negInv_mem_image_of_firstVisit_le hγc hfin ?_
          have hent : entryTime γ αR s₂ = (GB11.firstVisit γ (αR s₂.toNNReal)).toNNReal := by
            simp only [entryTime, h2, ↓reduceIte]
          rw [hent] at hτt
          calc GB11.firstVisit γ (αR s₂.toNNReal)
              = ((GB11.firstVisit γ (αR s₂.toNNReal)).toNNReal : ℝ≥0∞) := (ENNReal.coe_toNNReal hfin.ne).symm
            _ ≤ t := ENNReal.coe_le_coe.2 hτt
      have hVU : V ⊆ U := connectedComponentIn_subset U v
      have hVo : IsOpen V := hUo.connectedComponentIn
      set O := relInvC c '' V with hOdef
      have hOsub : O ⊆ relDom C \ K := by
        rintro _ ⟨w, hw, rfl⟩
        have hwU := hVU hw
        rw [hUeq] at hwU
        obtain ⟨w', hw', rfl⟩ := hwU
        rw [relInvC_relMapC hc hw'.1]
        exact hw'
      have hOeq : O = relDom C ∩ relMapC c ⁻¹' V := by
        ext w
        constructor
        · rintro ⟨v', hv', rfl⟩
          refine ⟨relInvC_mem hc (hUH (hVU hv')), ?_⟩
          show relMapC c (relInvC c v') ∈ V
          rw [relMapC_relInvC hc (hUH (hVU hv'))]
          exact hv'
        · rintro ⟨hwD, hwV⟩
          exact ⟨relMapC c w, hwV, relInvC_relMapC hc hwD⟩
      have hOo : IsOpen O := by
        rw [hOeq]
        exact (continuousOn_relMapC hc hCo hCH).isOpen_inter_preimage hDo hVo
      have hmapO : relMapC c '' O = V := by
        ext u
        constructor
        · rintro ⟨_, ⟨v', hv', rfl⟩, rfl⟩
          rw [relMapC_relInvC hc (hUH (hVU hv'))]
          exact hv'
        · intro hu
          exact ⟨relInvC c u, ⟨u, hu, rfl⟩, relMapC_relInvC hc (hUH (hVU hu))⟩
      obtain ⟨⟨z₀, -, hcomp⟩, -⟩ := hγ.2.2 t ENNReal.coe_lt_top
      -- the frontier of `O` in `ℍ` lies on the trace
      have hfr : ∀ q ∈ H, q ∈ closure O → q ∉ O → q ∈ A := by
        intro q hqH hqcl hqO
        by_cases hqD : q ∈ relDom C
        · have hcont : ContinuousAt (relMapC c) q :=
            (continuousOn_relMapC hc hCo hCH).continuousAt (hDo.mem_nhds hqD)
          have h1 : relMapC c q ∈ closure V := by
            have := mem_closure_image hcont hqcl
            rwa [hmapO] at this
          have h2 : relMapC c q ∉ U := fun hU =>
            hqO ⟨relMapC c q, mem_connectedComponentIn_of_mem_closure h1 hU, relInvC_relMapC hc hqD⟩
          have h3 : relMapC c q ∈ B := by
            by_contra hb
            exact h2 ⟨relMapC_mem_H hc hqD, hb⟩
          obtain ⟨w, hw, hwq⟩ := h3
          have hqK : q ∈ K := (injOn_relMapC hc hw.2 hqD hwq) ▸ hw.1
          by_contra hqA
          have hcl : q ∈ closure (H \ K) :=
            closure_mono (fun w (hw : w ∈ O) => (⟨hDH (hOsub hw).1, (hOsub hw).2⟩ : w ∈ H \ K)) hqcl
          rw [← hcomp] at hcl
          have h4 := mem_connectedComponentIn_of_mem_closure hcl ⟨hqH, hqA⟩
          rw [hcomp] at h4
          exact h4.2 hqK
        · obtain ⟨o, ho, hlim'⟩ := mem_closure_iff_seq_limit.1 hqcl
          have hvn : ∀ n, relMapC c (o n) ∈ V := fun n => by
            rw [← hmapO]
            exact mem_image_of_mem _ (ho n)
          have hvb : ∀ n, relMapC c (o n) ∈ closedBall (0 : ℂ) R := fun n => by
            rw [mem_closedBall, dist_zero_right]
            exact (hno _ (hvn n)).le
          obtain ⟨v₀, -, φ, hφ, hlimv⟩ := (isCompact_closedBall (0 : ℂ) R).tendsto_subseq hvb
          have hv₀V : v₀ ∈ closure V :=
            mem_closure_of_tendsto hlimv (Eventually.of_forall fun n => hvn (φ n))
          have hoφ : Tendsto (o ∘ φ) atTop (𝓝 q) := hlim'.comp hφ.tendsto_atTop
          have hoeq : ∀ n, relInvC c (((fun n => relMapC c (o n)) ∘ φ) n) = (o ∘ φ) n := fun n => by
            simp only [Function.comp]
            rw [relInvC_relMapC hc (hOsub (ho (φ n))).1]
          by_cases hv₀H : v₀ ∈ H
          · have hcont : ContinuousAt (relInvC c) v₀ :=
              (continuousOn_relInvC hc hCo hCH).continuousAt (QuantumZipper.isOpen_H.mem_nhds hv₀H)
            have h1 : Tendsto (o ∘ φ) atTop (𝓝 (relInvC c v₀)) :=
              (hcont.tendsto.comp hlimv).congr hoeq
            have hq : q = relInvC c v₀ := tendsto_nhds_unique hoφ h1
            exact absurd (hq ▸ relInvC_mem hc hv₀H) hqD
          · have him0 : v₀.im = 0 := by
              have hge : 0 ≤ v₀.im := ge_of_tendsto ((Complex.continuous_im.tendsto v₀).comp hlimv)
                (Eventually.of_forall fun n => le_of_lt (show (0 : ℝ) < _ from hUH (hVU (hvn (φ n)))))
              exact le_antisymm (not_lt.1 hv₀H) hge
            set x := v₀.re with hxdef
            have hv₀x : v₀ = (x : ℂ) := Complex.ext (by simp [hxdef]) (by simp [him0])
            have hin : Tendsto ((fun n => relMapC c (o n)) ∘ φ) atTop (𝓝[H] (x : ℂ)) :=
              tendsto_nhdsWithin_iff.2 ⟨hv₀x ▸ hlimv, Eventually.of_forall fun n => hUH (hVU (hvn (φ n)))⟩
            have h1 : Tendsto (o ∘ φ) atTop (𝓝 (e x)) := ((hlim x).comp hin).congr hoeq
            have hq : q = e x := tendsto_nhds_unique hoφ h1
            by_cases hx0 : x = 0
            · have h0H : e 0 ∈ H := by
                rw [← hx0, ← hq]
                exact hqH
              rw [hq, hx0]
              exact he0A h0H
            · rw [hq]
              exact hcase x hx0 (hv₀x ▸ hv₀V)
      -- `O` is clopen in `ℍ \ γ([0, t])`, so it contains the active component `ℍ \ K'_t`
      have hHK : H \ K ⊆ O := by
        have hpre : IsPreconnected (H \ K) := hcomp ▸ isPreconnected_connectedComponentIn
        have hHKA : H \ K ⊆ H \ A := hcomp ▸ connectedComponentIn_subset _ _
        have hvO : relInvC c v ∈ O := ⟨v, mem_connectedComponentIn hv, rfl⟩
        refine hpre.subset_left_of_subset_union hOo isClosed_closure.isOpen_compl
          (disjoint_compl_right.mono_left subset_closure) (fun q hq => ?_)
          ⟨relInvC c v, ⟨hDH (hOsub hvO).1, (hOsub hvO).2⟩, hvO⟩
        by_cases hqO : q ∈ O
        · exact Or.inl hqO
        · exact Or.inr fun hqcl => (hHKA hq).2 (hfr q hq.1 hqcl hqO)
      -- hence `V = U`, which has a far point
      have hUV : U ⊆ V := by
        intro u hu
        rw [hUeq] at hu
        obtain ⟨w, hw, rfl⟩ := hu
        obtain ⟨v', hv', hv'w⟩ := hHK ⟨hDH hw.1, hw.2⟩
        rw [← hv'w, relMapC_relInvC hc (hUH (hVU hv'))]
        exact hv'
      have hnorm : ‖(((R + 1 : ℝ) : ℂ) * Complex.I)‖ = R + 1 := by
        rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
      have hfarU : (((R + 1 : ℝ) : ℂ) * Complex.I) ∈ U := by
        refine ⟨?_, fun hb => ?_⟩
        · show 0 < ((((R + 1 : ℝ) : ℂ) * Complex.I)).im
          simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_one,
            mul_zero, add_zero]
          linarith
        · have h1 := hBR hb
          rw [mem_ball, dist_zero_right, hnorm] at h1
          linarith
      have h1 := hno _ (hUV hfarU)
      rw [hnorm] at h1
      linarith
  have hpre : IsPreconnected U := isPreconnected_of_forall_far hR hUH hHU hfar
  have himg : relDom C \ K = relInvC c '' U := by
    rw [hUeq, image_image]
    ext w
    constructor
    · intro hw
      exact ⟨w, hw, relInvC_relMapC hc hw.1⟩
    · rintro ⟨w', hw', rfl⟩
      show relInvC c (relMapC c w') ∈ relDom C \ K
      rw [relInvC_relMapC hc hw'.1]
      exact hw'
  rw [himg]
  exact hpre.image _ ((continuousOn_relInvC hc hCo hCH).mono hUH)

end Conn

/-! ### GB11's analytic core from the boundary correspondence and the local growth -/

/-- **Named input: the boundary correspondence of the pocket charts in GB11's setting** (deterministic; Carathéodory's
boundary map of a two-arc pocket read in the relative chart, `ChartBdryCorr`). Hypotheses of
`GW4Reg.GB11RelConnGrowthStatement` up to the chart. It concerns the walls, the pocket and its chart; the trace enters
only through the barrier's wall clauses. -/
def GB11ChartBdryStatement : Prop :=
  ∀ (W' : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ), Continuous W' → W' 0 = 0 → IsGeneratingTrace W' ⊤ γ →
    GB10.NoSimpleArcInterval γ ⊤ →
    ∀ αR αL : ℝ≥0 → ℂ, GB11.IsGB11Barrier αR αL γ → WalkPocketShape αR αL →
    ∀ C ∈ betweenComponents (range αR) (range αL), ∀ (s₁ t₁ : ℝ≥0) (s₂ t₂ : ℝ≥0∞),
    IsPocketShape αR αL C s₁ t₁ s₂ t₂ →
    ∀ c : Chart, IsComponentChart (range αR) (range αL) C c → Tendsto c.2.1 (𝓝[H] 0) (𝓝 (αR s₁)) →
      ∃ (e : ℝ → ℂ) (rR rL : ℝ → ℝ≥0), ChartBdryCorr αR αL c s₂ e rR rL

/-- **Named input: the local growth of the relative hulls** — the second conjunct of
`GW4Reg.GB11RelConnGrowthStatement`, verbatim (one driving function `U`, `U 0 = 0`, continuous on every `[0, T]`,
`T < σ − τ`, with uniformly small increments `g_{B s}(B t \ B s)` around `U s`). -/
def GB11RelLocalGrowthStatement : Prop :=
  ∀ (W' : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ), Continuous W' → W' 0 = 0 → IsGeneratingTrace W' ⊤ γ →
    GB10.NoSimpleArcInterval γ ⊤ →
    ∀ αR αL : ℝ≥0 → ℂ, GB11.IsGB11Barrier αR αL γ → WalkPocketShape αR αL →
    ∀ C ∈ betweenComponents (range αR) (range αL), ∀ (s₁ t₁ : ℝ≥0) (s₂ t₂ : ℝ≥0∞),
    IsPocketShape αR αL C s₁ t₁ s₂ t₂ →
    ∀ c : Chart, IsComponentChart (range αR) (range αL) C c → Tendsto c.2.1 (𝓝[H] 0) (𝓝 (αR s₁)) →
    (∀ t : ℝ≥0, t < entryTime γ αR s₂ → γ t ≠ 0 → -(γ t)⁻¹ ∉ closure C) →
    (∀ t : ℝ≥0, entryTime γ αR s₂ ≤ t → (t : ℝ≥0∞) < GB11.firstVisit γ (αR s₁) → γ t ≠ 0 →
      -(γ t)⁻¹ ∈ closure C) →
    (∀ a b : ℝ≥0, entryTime γ αR s₂ ≤ a → a < b → (b : ℝ≥0∞) < GB11.firstVisit γ (αR s₁) →
      ∃ t ∈ Ioo a b, γ t ≠ 0 ∧ -(γ t)⁻¹ ∈ C) →
    ∃ U : ℝ → ℝ, U 0 = 0 ∧ ∀ T ∈ horizon (GB11.firstVisit γ (αR s₁) - entryTime γ αR s₂),
      ContinuousOn U (Icc 0 T) ∧ ∀ ε > 0, ∃ δ > 0, ∀ s ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc (0 : ℝ) T, s ≤ t → t - s ≤ δ →
        mapOut (relHull W' c C (entryTime γ αR s₂) s) ''
            (relHull W' c C (entryTime γ αR s₂) t \ relHull W' c C (entryTime γ αR s₂) s) ⊆
          Metric.closedBall (U s : ℂ) ε

/-- **(GB11.2) and the local growth from the boundary correspondence and the local growth** (conditional helper):
the connectivity conjunct of `GW4Reg.GB11RelConnGrowthStatement` is `isPreconnected_relDom_diff_fwdHull`. -/
theorem gb11RelConnGrowthStatement_of_bdry (hbd : GB11ChartBdryStatement) (hgr : GB11RelLocalGrowthStatement) :
    GW4Reg.GB11RelConnGrowthStatement := by
  intro W' γ hW' hW'0 hγ hno αR αL hB hP C hC s₁ t₁ s₂ t₂ hs c hc hxC hE hTr hD
  refine ⟨fun u hu => ?_, hgr W' γ hW' hW'0 hγ hno αR αL hB hP C hC s₁ t₁ s₂ t₂ hs c hc hxC hE hTr hD⟩
  obtain ⟨e, rR, rL, hbc⟩ := hbd W' γ hW' hW'0 hγ hno αR αL hB hP C hC s₁ t₁ s₂ t₂ hs c hc hxC
  have hCo : IsOpen C := isOpen_of_mem_betweenComponents (isClosed_range_of_isCompleteSimpleFlow hB.1)
    (isClosed_range_of_isCompleteSimpleFlow hB.2.1) hC
  have hCH : C ⊆ H := subset_H_of_mem_betweenComponents hC
  have hcu : ((entryTime γ αR s₂ + u.toNNReal : ℝ≥0) : ℝ) = (entryTime γ αR s₂ : ℝ) + u := by
    rw [NNReal.coe_add, Real.coe_toNNReal _ hu.1]
  rw [← hcu]
  exact isPreconnected_relDom_diff_fwdHull hW' hW'0 hγ hB hs hc hCo hCH hxC hbc le_self_add
    (coe_add_lt_of_mem_horizon hu)

/-- **Lemma GB11's relative parametrization from the boundary correspondence and the local growth** (conditional
helper). -/
theorem gb11RelParamStatement_of_bdry (hbd : GB11ChartBdryStatement) (hgr : GB11RelLocalGrowthStatement) :
    GW4Reg.GB11RelParamStatement :=
  gb11RelParamStatement_of_connGrowth (gb11RelConnGrowthStatement_of_bdry hbd hgr)

end GB11Conn

end Theorem14

end InteractingSLE
