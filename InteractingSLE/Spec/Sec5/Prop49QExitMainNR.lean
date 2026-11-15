/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.RealTip
import InteractingSLE.Spec.Restart.RetAux79Zone
import InteractingSLE.Foundations.Loewner.RealPoints

/-!
# A Loewner chain whose trace never returns to `0` has no extra prime end over `0`

Packet PROVE-GLUECOND11 (ruling R59: Proposition 4.9's pull-back needs "no return of the counterflow to its start").
Let `w` be a continuous driver from `0` with a continuous Loewner trace `η`, `s > 0`, and suppose `η(v) ≠ 0` for
`0 < v ≤ s`. Then the boundary extension `F̄_s` of the centred inverse map does not vanish at any coordinate strictly
between `0` and the image `x_R = f_s(0⁺)` of `0⁺` (**`extendFrom_ne_zero_of_noReturn`**): the only prime ends of
`ℍ ∖ K_s` over `0` are `0^±`.

## Proof

Suppose `F̄_s(x) = 0`, `0 < x < x_R`. The access arc `α = F̄_s(x + i(0, ∞))` joins `0` to `∞` in `ℍ ∖ K_s`; with the
real ray `[0, ∞)` and a Möbius map with a pole `x₀ < 0` far left (`ZhanGT4.accessCrosscut`) it bounds a Jordan domain
`J`. The connected set `S = η((0, s])` misses `α ∪ {0}` (`α ⊆ ℍ ∖ K_s`, no return), so in Möbius coordinates it lies
either in `J ∪ (0, ∞)` or in the outside `E` (a connected subset of `ℍ̄` cannot cross the real segment of the curve).
But the tip `η(s) = F̄_s(0)` is a limit of `F̄_s` over the second quadrant at `x`, which lies in `E`; and some
`F̄_s(u) ≠ 0`, `x < u < x_R` (`exists_ne_of_injOn`, Schwarz reflection), is a limit over the first quadrant, which
lies in `J`. That point is on the trace: a boundary value off the hull's closure would be an alive real point, whose
coordinate is `≥ x_R` (`isForwardSol_real_cases`, `tendsto_fwdMap_of_isForwardSol`); a point of the closure of the
hull that is a limit of the complement is a trace point (`mem_image_of_mem_closure_both`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Metric
open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv)

namespace InteractingSLE.Sec5.Prop49Exit

open ZhanGT4 MartChar.RealFlow

variable {W : ℝ → ℝ} {η : ℝ → ℂ}

/-- **A point of the closure of the hull that is a limit of the complement lies on the trace** (as
`ZhanGT4.mem_image_of_mem_fwdHull_of_mem_closure`, real points included): otherwise a disc around it misses the
trace, meets the hull, hence lies in a bounded component of `ℍ ∖ η([0, t])`, i.e. in `K_t`, and misses the
complement. -/
theorem mem_image_of_mem_closure_both (hη : IsLoewnerTrace W η) {t : ℝ} (ht : 0 ≤ t) {c : ℂ}
    (hcK : c ∈ closure (fwdHull W t)) (hcc : c ∈ closure (H \ fwdHull W t)) : c ∈ η '' Icc 0 t := by
  by_contra hcA
  set A := η '' Icc 0 t with hA
  have hAc : IsCompact A := hη.isCompact_image t
  have hAne : A.Nonempty := ⟨η 0, mem_image_of_mem _ ⟨le_rfl, ht⟩⟩
  have hd : 0 < infDist c A := (hAc.isClosed.notMem_iff_infDist_pos hAne).1 hcA
  set r := infDist c A with hr
  have hball : ball c r ∩ H ⊆ H \ A := by
    intro z ⟨hz, hzH⟩
    refine ⟨hzH, fun hzA => ?_⟩
    have := infDist_le_dist_of_mem hzA (x := c)
    rw [dist_comm] at this
    rw [mem_ball] at hz
    linarith
  obtain ⟨z, hzK, hzb⟩ := Metric.mem_closure_iff.1 hcK r hd
  have hzH : z ∈ H := hzK.1
  have hzK' := hzK
  rw [hη.2.2 t ht] at hzK'
  obtain ⟨-, hzF⟩ := hzK'
  rw [hAc.isClosed.closure_eq] at hzF
  have hzA : z ∉ A := (hball ⟨by rw [mem_ball, dist_comm]; exact hzb, hzH⟩).2
  have hbdd : Bornology.IsBounded (connectedComponentIn (H \ A) z) := hzF.resolve_left hzA
  have hconv : IsPreconnected (ball c r ∩ H) :=
    ((convex_ball c r).inter (convex_halfSpace_gt (f := fun z : ℂ => z.im) Complex.imLm.isLinear 0)).isPreconnected
  have hzb' : z ∈ ball c r ∩ H := ⟨by rw [mem_ball, dist_comm]; exact hzb, hzH⟩
  have hsub : ball c r ∩ H ⊆ connectedComponentIn (H \ A) z :=
    hconv.subset_connectedComponentIn hzb' hball
  obtain ⟨y, hyc, hyb⟩ := Metric.mem_closure_iff.1 hcc r hd
  have hyb' : y ∈ ball c r ∩ H := ⟨by rw [mem_ball, dist_comm]; exact hyb, hyc.1⟩
  refine hyc.2 ?_
  rw [hη.2.2 t ht]
  refine ⟨hyc.1, Or.inr ?_⟩
  rw [hAc.isClosed.closure_eq, ← connectedComponentIn_eq (hsub hyb')]
  exact hbdd

/-- The boundary value at a real coordinate is a limit of the complement of the hull. -/
theorem extendFrom_mem_closure_compl (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ}
    (ht : 0 ≤ t) (u : ℝ) : extendFrom H (fwdMapInv W t) u ∈ closure (H \ fwdHull W t) := by
  have hlim := (hη.hasBdryLimits hW hW0 ht).tendsto (ofReal_mem_Hbar u)
  have := FiniteEndpoint.neBot_nhdsWithin_H (z := (u : ℂ)) (by simp)
  exact mem_closure_of_tendsto hlim
    (eventually_nhdsWithin_of_forall fun w hw => QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hW hW0 ht hw)

/-- **A real boundary value off the closure of the hull is an alive point, and its coordinate is the coordinate of
that point**: if `F̄_t(u) = c ≠ 0` is real and has a forward solution, then `u` is `g_t(c) − w_t` (for `c > 0`) or
negative (for `c < 0`). -/
theorem coord_of_extendFrom_alive (hW : Continuous W) (hW0 : W 0 = 0) (hη : IsLoewnerTrace W η) {t : ℝ}
    (ht : 0 ≤ t) {u c : ℝ} (hc : extendFrom H (fwdMapInv W t) u = c) {v : ℝ → ℂ}
    (hv : QuantumZipper.IsForwardSol W (c : ℂ) t v) :
    (0 < c ∧ Alive W c t ∧ u = gImg W c t - W t) ∨ (c < 0 ∧ u < 0) := by
  set F := extendFrom H (fwdMapInv W t) with hF
  have hFc : ContinuousOn F Hbar := (hη.hasBdryLimits hW hW0 ht).continuousOn
  -- `u + i y → u` within `ℍ̄`, and `F` maps it into `ℍ`
  have h1 : Tendsto (fun y : ℝ => (u : ℂ) + I * y) (𝓝[>] 0) (𝓝[Hbar] (u : ℂ)) :=
    tendsto_add_I_mul_nhdsWithin_Hbar u
  have h2 : Tendsto (fun y : ℝ => F ((u : ℂ) + I * y)) (𝓝[>] 0) (𝓝[H] (c : ℂ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun y hy => ?_⟩
    · rw [← hc]
      exact (hFc _ (ofReal_mem_Hbar u)).tendsto.comp h1
    · have hyH : (u : ℂ) + I * y ∈ H := by
        show 0 < ((u : ℂ) + I * y).im
        have : (0 : ℝ) < y := hy
        simpa using this
      rw [hF, extendFrom_eq_fwdMapInv hW hW0 ht hyH]
      exact QuantumZipper.RS.fwdMapInv_mem_H hW hW0 ht hyH
  have h3 := (InteractingSLE.tendsto_fwdMap_of_isForwardSol hW ht hv).comp h2
  have h4 : Tendsto (fun y : ℝ => (u : ℂ) + I * y) (𝓝[>] 0) (𝓝 (u : ℂ)) := by
    have hc' : Continuous (fun y : ℝ => (u : ℂ) + I * y) := by fun_prop
    simpa using (hc'.tendsto 0).mono_left nhdsWithin_le_nhds
  have h5 : Tendsto (fun y : ℝ => (u : ℂ) + I * y) (𝓝[>] 0) (𝓝 (v t)) := by
    refine h3.congr' (eventually_nhdsWithin_of_forall fun y hy => ?_)
    have hyH : (u : ℂ) + I * y ∈ H := by
      show 0 < ((u : ℂ) + I * y).im
      have : (0 : ℝ) < y := hy
      simpa using this
    show fwdMap W t (F ((u : ℂ) + I * y)) = (u : ℂ) + I * y
    rw [hF, extendFrom_eq_fwdMapInv hW hW0 ht hyH, QuantumZipper.RS.fwdMap_fwdMapInv hW hW0 ht hyH]
  have hvu : v t = (u : ℂ) := tendsto_nhds_unique h5 h4
  rcases Restart.RetAux79.isForwardSol_real_cases hW hW0 ht hv with ⟨hc0, hca, hvt⟩ | ⟨hc0, -, hvt⟩
  · left
    refine ⟨hc0, hca, ?_⟩
    rw [hvu] at hvt
    exact_mod_cast hvt
  · right
    refine ⟨hc0, ?_⟩
    have hneg := ZhanGT4.re_fwdMap_neg hW hW0 hc0 hv ⟨ht, le_rfl⟩
    rw [InteractingSLE.fwdMap_eq_of_isForwardSol hW hv ⟨ht, le_rfl⟩, hvu, ofReal_re] at hneg
    exact hneg

/-- **Boundary values on the right junction interval lie on the trace**: for `0 < u < x_R = f_t(0⁺)`, a nonzero
boundary value `F̄_t(u)` is a point `η(v)`, `v ∈ [0, t]`. -/
theorem extendFrom_mem_image_of_lt (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ}
    (ht : 0 ≤ t) {u : ℝ} (hu0 : 0 < u) (huR : u < rightImg W 0 t - W t)
    (hne : extendFrom H (fwdMapInv W t) u ≠ 0) : extendFrom H (fwdMapInv W t) u ∈ η '' Icc 0 t := by
  set c := extendFrom H (fwdMapInv W t) u with hcdef
  refine mem_image_of_mem_closure_both hη ht ?_ (extendFrom_mem_closure_compl hη hW hW0 ht u)
  by_cases hcH : c ∈ H
  · exact subset_closure (extendFrom_mem_fwdHull hη hW hW0 ht hcH).1
  by_contra hcK
  have hcim : c.im = 0 := by
    refine le_antisymm (not_lt.1 hcH) ?_
    have h := (hη.hasBdryLimits hW hW0 ht).tendsto (ofReal_mem_Hbar u)
    have := FiniteEndpoint.neBot_nhdsWithin_H (z := (u : ℂ)) (by simp)
    exact ge_of_tendsto ((continuous_im.tendsto _).comp h)
      (eventually_nhdsWithin_of_forall fun w hw => (QuantumZipper.RS.fwdMapInv_mem_H hW hW0 ht hw).le)
  have hcr : c = ((c.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [hcim])
  obtain ⟨r, hr, hrK⟩ : ∃ r > 0, Disjoint (ball (c.re : ℂ) r) (fwdHull W t) := by
    obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl c hcK
    refine ⟨r, hr, Set.disjoint_left.2 fun z hz hzK => hsub (by rwa [← hcr] at hz) (subset_closure hzK)⟩
  have hc0 : c.re ≠ 0 := fun h => hne (by rw [hcr, h, ofReal_zero])
  obtain ⟨v, hv⟩ := exists_isForwardSol_of_disjoint_ball hW hW0 hc0 ht hr hrK
  rcases coord_of_extendFrom_alive hW hW0 hη ht (u := u) (c := c.re) (by rw [← hcr]) hv with
    ⟨hpos, hal, hu⟩ | ⟨-, hneg⟩
  · have := rightImg_le_gImg hW ht hpos hal
    linarith
  · linarith

/-- The boundary values of the inverse map lie in `ℍ̄`. -/
theorem extendFrom_mem_Hbar (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t)
    (u : ℝ) : extendFrom H (fwdMapInv W t) u ∈ Hbar := by
  have h := (hη.hasBdryLimits hW hW0 ht).tendsto (ofReal_mem_Hbar u)
  have := FiniteEndpoint.neBot_nhdsWithin_H (z := (u : ℂ)) (by simp)
  exact ge_of_tendsto ((continuous_im.tendsto _).comp h)
    (eventually_nhdsWithin_of_forall fun w hw => (QuantumZipper.RS.fwdMapInv_mem_H hW hW0 ht hw).le)

/-- The trace lies in `ℍ̄` (it is the boundary value at the driver coordinate). -/
theorem trace_mem_Hbar (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) :
    η t ∈ Hbar := by
  have h := extendFrom_mem_Hbar hη hW hW0 ht 0
  rwa [ofReal_zero, extendFrom_zero_eq hη hW hW0 ht] at h

/-- A trace point in `ℍ` is in the hull. -/
theorem trace_mem_fwdHull (hη : IsLoewnerTrace W η) {t v : ℝ} (ht : 0 ≤ t) (hv : v ∈ Icc 0 t) (hH : η v ∈ H) :
    η v ∈ fwdHull W t := by
  rw [hη.2.2 t ht]
  exact ⟨hH, Or.inl (subset_closure (mem_image_of_mem _ hv))⟩

/-- **Translating the coordinate of a boundary map.** -/
theorem isBoundaryMap_translate {F : ℂ → ℂ} (hF : IsBoundaryMap F) (x : ℝ) :
    IsBoundaryMap fun z => F (z + x) := by
  have hmaps : ∀ z : ℂ, z ∈ Hbar → z + x ∈ Hbar := fun z hz => by
    have h : 0 ≤ z.im := hz
    show 0 ≤ (z + x).im; simpa using h
  have hmapsH : ∀ z : ℂ, z ∈ H → z + x ∈ H := fun z hz => by
    have h : 0 < z.im := hz
    show 0 < (z + x).im; simpa using h
  refine ⟨hF.cont.comp (continuous_id.add continuous_const).continuousOn hmaps, fun z₁ h₁ z₂ h₂ he => ?_,
    fun z hz => hF.mapsTo (hmapsH z hz), ?_⟩
  · have := hF.inj (hmapsH z₁ h₁) (hmapsH z₂ h₂) he
    simpa using this
  · obtain ⟨C, hC⟩ := hF.bdd
    refine ⟨C + |x|, fun w hw => ?_⟩
    have h1 := hC _ (hmapsH w hw)
    calc ‖F (w + x) - w‖ = ‖(F (w + x) - (w + x)) + (x : ℂ)‖ := by ring_nf
      _ ≤ ‖F (w + x) - (w + x)‖ + ‖(x : ℂ)‖ := norm_add_le _ _
      _ ≤ C + |x| := by rw [Complex.norm_real, Real.norm_eq_abs]; linarith

/-- The real points strictly between the ends of a crosscut lie on its closed curve. -/
theorem mem_crosscutCurve_of_re {γ : ℝ → ℂ} (hγ : IsRealCrosscut γ) (hlt : (γ 0).re < (γ 1).re) {m : ℂ}
    (hm : m.im = 0) (h0 : (γ 0).re ≤ m.re) (h1 : m.re ≤ (γ 1).re) : m ∈ crosscutCurve γ := by
  refine Or.inr ⟨(m.re - (γ 0).re) / ((γ 1).re - (γ 0).re), ⟨div_nonneg (by linarith) (by linarith),
    (div_le_one (by linarith)).2 (by linarith)⟩, ?_⟩
  apply Complex.ext
  · rw [crosscutSeg_re, div_mul_cancel₀ _ (by linarith : (γ 1).re - (γ 0).re ≠ 0)]
    ring
  · rw [crosscutSeg_im hγ, hm]

/-- **No extra prime end over `0`** (ruling R59's deterministic step). For a continuous driver `W` from `0` with a
continuous Loewner trace `η` that does not return to `0` on `(0, s]`, the boundary extension of the centred inverse
map at time `s` does not vanish strictly between `0` and the image `x_R = f_s(0⁺)` of `0⁺`. -/
theorem extendFrom_ne_zero_of_noReturn (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) {s : ℝ}
    (hs : 0 < s) (hNR : ∀ v ∈ Ioc 0 s, η v ≠ 0) {x : ℝ} (hx0 : 0 < x) (hxR : x < rightImg W 0 s - W s) :
    extendFrom H (fwdMapInv W s) x ≠ 0 := by
  intro hFx
  set F := extendFrom H (fwdMapInv W s) with hFdef
  obtain ⟨hFd, hFc, hFinj, -⟩ := hη.fiber_hyps hW hW0 hs.le
  have hFb : IsBoundaryMap F := isBoundaryMap_extendFrom hη hW hW0 hs.le
  have hFimg : F '' H = H \ fwdHull W s := extendFrom_image_H hW hW0 hs.le
  have hSF : ∀ v ∈ Icc 0 s, η v ∉ F '' H := by
    intro v hv hvF
    rw [hFimg] at hvF
    exact hvF.2 (trace_mem_fwdHull hη hs.le hv hvF.1)
  -- the right point `F u`, on the trace
  obtain ⟨u, hu, hFu⟩ := exists_ne_of_injOn hFd hFc hFinj hxR 0
  obtain ⟨vu, hvu, hvue⟩ : ∃ v ∈ Ioc 0 s, η v = F u := by
    obtain ⟨v, hv, hve⟩ := extendFrom_mem_image_of_lt hη hW hW0 hs.le (hx0.trans hu.1) hu.2 hFu
    refine ⟨v, ⟨lt_of_le_of_ne hv.1 ?_, hv.2⟩, hve⟩
    intro h
    apply hFu
    rw [← hve, ← h]
    exact hη.1
  have htip : F 0 = η s := extendFrom_zero_eq hη hW hW0 hs.le
  -- a bound on the trace, real points far out, and the pole
  obtain ⟨Mb, hMb⟩ := (hη.isCompact_image s).isBounded.exists_norm_le
  obtain ⟨-, ⟨v₁, hv₁, hv₁im, hv₁re⟩⟩ := exists_coord_far hW hW0 hη hs (|Mb| + 1)
  obtain ⟨⟨v₂, hv₂, hv₂im, hv₂re⟩, -⟩ := exists_coord_far hW hW0 hη hs (-1)
  rw [← hFdef] at hv₁im hv₁re hv₂im hv₂re
  have hv₁x : x < v₁ := by
    by_contra hle
    push Not at hle
    have hne : F v₁ ≠ 0 := fun h => by rw [h, zero_re] at hv₁re; linarith [abs_nonneg Mb]
    obtain ⟨v, hv, hve⟩ := extendFrom_mem_image_of_lt hη hW hW0 hs.le hv₁ (hle.trans_lt hxR) hne
    have h1 := hMb _ ⟨v, hv, hve⟩
    have h2 : (F v₁).re ≤ ‖F v₁‖ := Complex.re_le_norm _
    linarith [le_abs_self Mb]
  set x₀ : ℝ := min (-(|Mb| + 1)) ((F v₂).re - 1) with hx₀def
  have hx₀neg : x₀ < 0 := lt_of_le_of_lt (min_le_left _ _) (by linarith [abs_nonneg Mb])
  have hx₀v₂ : x₀ < (F v₂).re := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hx₀S : ∀ v ∈ Icc 0 s, η v ≠ x₀ := fun v hv h => by
    have h1 := hMb _ (mem_image_of_mem η hv)
    rw [h, Complex.norm_real, Real.norm_eq_abs] at h1
    have h2 : |Mb| + 1 ≤ |x₀| := by
      rw [abs_of_neg hx₀neg]; linarith [min_le_left (-(|Mb| + 1)) ((F v₂).re - 1)]
    linarith [le_abs_self Mb]
  -- the translated boundary map and its access crosscut
  set G : ℂ → ℂ := fun z => F (z + x) with hGdef
  have hGb : IsBoundaryMap G := isBoundaryMap_translate hFb x
  have hG0 : G 0 = 0 := by simp only [hGdef, zero_add]; exact hFx
  have h0 : (G 0).im = 0 := by rw [hG0, zero_im]
  have hx₀' : x₀ < (G 0).re := by rw [hG0, zero_re]; exact hx₀neg
  set γ := accessCrosscut G x₀ with hγdef
  have hγ := isRealCrosscut_accessCrosscut hGb h0 hx₀'
  have hlt := accessCrosscut_re_lt (F := G) h0 hx₀'
  obtain ⟨J, E, hJo, hEo, -, -, -, -, hJH, hJE, hunion, hfr, -⟩ :=
    exists_inside_of_subset_Hbar (isJordanCurve_crosscutCurve hγ hlt) fun z hz => crosscutCurve_im_nonneg hγ hz
  have hγ0 : (γ 0).re = x₀⁻¹ := by
    rw [hγdef, accessCrosscut_zero h0, hG0, ofReal_re, zero_re, sub_zero]
  have hγ1 : (γ 1).re = 0 := by rw [hγdef, accessCrosscut_one, zero_re]
  set M := poleInv x₀ with hMdef
  set Γ := crosscutCurve γ with hΓdef
  have hf1 : ∀ z : ℂ, z ≠ x₀ → M z ∈ Γ → z ∈ accessArc G ∨ (z.im = 0 ∧ 0 ≤ z.re) := by
    intro z hz hzΓ
    have := mem_accessArc_or_of_poleInv_mem hGb h0 hx₀' hz hzΓ
    rwa [hG0, zero_re] at this
  have hαF : accessArc G ⊆ F '' H := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨I * y + x, ?_, rfl⟩
    show 0 < (I * (y : ℂ) + x).im
    have : (0 : ℝ) < y := hy
    simpa using this
  have hEΓ : ∀ z ∈ E, z ∉ Γ := fun z hz hzΓ => by
    have : z ∈ Γᶜ := by rw [hunion]; exact Or.inr hz
    exact this hzΓ
  have hJΓ : ∀ z ∈ J, z ∉ Γ := fun z hz hzΓ => by
    have : z ∈ Γᶜ := by rw [hunion]; exact Or.inl hz
    exact this hzΓ
  -- the open real segment of the curve
  set seg : Set ℂ := {m : ℂ | m.im = 0 ∧ x₀⁻¹ < m.re ∧ m.re < 0} with hsegdef
  have hsegΓ : seg ⊆ Γ := fun m hm =>
    mem_crosscutCurve_of_re hγ hlt hm.1 (by rw [hγ0]; exact hm.2.1.le) (by rw [hγ1]; exact hm.2.2.le)
  have hMpos : ∀ z : ℂ, z.im = 0 → 0 < z.re → M z ∈ seg := by
    intro z hzi hzr
    have hzr' : z = (z.re : ℂ) := Complex.ext rfl (by simp [hzi])
    have hlt' : x₀ - z.re < x₀ := by linarith
    have hneg : x₀ - z.re < 0 := by linarith
    rw [hzr', hMdef, poleInv_ofReal]
    refine ⟨by simp, ?_, ?_⟩
    · rw [ofReal_re]; exact (inv_lt_inv_of_neg hx₀neg hneg).2 hlt'
    · rw [ofReal_re]; exact inv_lt_zero.2 hneg
  have hball : ∀ m ∈ seg, ∃ ρ > 0, ball m ρ ∩ H ⊆ J := fun m hm => by
    have hmr : m = (m.re : ℂ) := Complex.ext rfl (by simp [hm.1])
    obtain ⟨ρ, hρ, hsub⟩ := exists_ball_inter_H_subset_of_frontier_eq hγ hlt hJo hJH hfr (x := m.re)
      ⟨by rw [hγ0]; exact hm.2.1, by rw [hγ1]; exact hm.2.2⟩
    refine ⟨ρ, hρ, ?_⟩
    rw [hmr]
    exact hsub
  have hseg_notE : ∀ m ∈ seg, m ∉ closure (E ∩ H) := fun m hm hmc => by
    obtain ⟨ρ, hρ, hsub⟩ := hball m hm
    obtain ⟨z, ⟨hzE, hzH⟩, hzm⟩ := Metric.mem_closure_iff.1 hmc ρ hρ
    exact Set.disjoint_left.1 hJE (hsub ⟨by rw [mem_ball, dist_comm]; exact hzm, hzH⟩) hzE
  -- the open set `U = J ∪ seg ∪ {Im < 0}`
  set U : Set ℂ := J ∪ seg ∪ lowerHalf with hUdef
  have hUo : IsOpen U := by
    refine Metric.isOpen_iff.2 fun m hm => ?_
    rcases hm with (hmJ | hmseg) | hmlow
    · obtain ⟨ρ, hρ, hsub⟩ := Metric.isOpen_iff.1 hJo m hmJ
      exact ⟨ρ, hρ, fun z hz => Or.inl (Or.inl (hsub hz))⟩
    · obtain ⟨ρ, hρ, hsub⟩ := hball m hmseg
      refine ⟨min ρ (min (m.re - x₀⁻¹) (-m.re)), lt_min hρ (lt_min (by linarith [hmseg.2.1])
        (by linarith [hmseg.2.2])), fun z hz => ?_⟩
      have hzρ : dist z m < ρ := lt_of_lt_of_le hz (min_le_left _ _)
      have hz2 : dist z m < min (m.re - x₀⁻¹) (-m.re) := lt_of_lt_of_le hz (min_le_right _ _)
      have hre : |z.re - m.re| ≤ dist z m := by
        rw [dist_eq_norm]; exact (Complex.abs_re_le_norm (z - m)).trans_eq' (by simp)
      rcases lt_trichotomy z.im 0 with hzi | hzi | hzi
      · exact Or.inr hzi
      · refine Or.inl (Or.inr ⟨hzi, ?_, ?_⟩)
        · have := (abs_lt.1 (hre.trans_lt (hz2.trans_le (min_le_left _ _)))).1
          linarith
        · have := (abs_lt.1 (hre.trans_lt (hz2.trans_le (min_le_right _ _)))).2
          linarith
      · exact Or.inl (Or.inl (hsub ⟨hzρ, hzi⟩))
    · obtain ⟨ρ, hρ, hsub⟩ := Metric.isOpen_iff.1 isOpen_lowerHalf m hmlow
      exact ⟨ρ, hρ, fun z hz => Or.inr (hsub hz)⟩
  have hMHbar : ∀ z ∈ Hbar, M z ∈ Hbar := fun z hz => by
    show 0 ≤ (M z).im
    rw [hMdef, poleInv_im]
    exact div_nonneg (show 0 ≤ z.im from hz) (normSq_nonneg _)
  have hUE : ∀ z ∈ Hbar, z ∈ U → z ∈ E → False := fun z hzb hzU hzE => by
    rcases hzU with (hzJ | hzseg) | hzlow
    · exact Set.disjoint_left.1 hJE hzJ hzE
    · exact hEΓ z hzE (hsegΓ hzseg)
    · exact absurd (show 0 ≤ z.im from hzb) (not_le.2 hzlow)
  -- the images of the two quadrants at `x` avoid the closed curve
  have hQsub : ∀ w : ℂ, w ∈ H → w.re ≠ 0 → M (G w) ∈ J ∪ E := by
    intro w hwH hwre
    have hGw : G w ∈ H := hGb.mapsTo hwH
    have hGx : G w ≠ x₀ := fun h => by
      have h1 : (0 : ℝ) < (G w).im := hGw
      rw [h, ofReal_im] at h1
      exact lt_irrefl _ h1
    rw [← hunion]
    intro hΓ
    rcases hf1 _ hGx hΓ with ⟨y, hy, hyw⟩ | ⟨him, -⟩
    · have := hGb.inj (I_mul_mem_H hy) hwH hyw
      apply hwre
      rw [← this]
      simp
    · have h1 : (0 : ℝ) < (G w).im := hGw
      linarith
  have hpre : ∀ Q : Set ℂ, IsPreconnected Q → Q ⊆ H → IsPreconnected (M '' (G '' Q)) := by
    intro Q hQ hQH
    have hGQH : G '' Q ⊆ H := image_subset_iff.2 fun w hw => hGb.mapsTo (hQH hw)
    exact (hQ.image G (hGb.cont.mono (hQH.trans H_subset_Hbar))).image M
      (continuousOn_poleInv fun h => not_mem_H_ofReal x₀ (hGQH h))
  have hlimM : ∀ a : ℝ, G a ≠ x₀ →
      Tendsto (fun y : ℝ => M (G ((a : ℂ) + I * y))) (𝓝[>] 0) (𝓝 (M (G a))) := fun a ha =>
    (continuousAt_poleInv ha).tendsto.comp
      ((hGb.cont _ (ofReal_mem_Hbar a)).tendsto.comp (tendsto_add_I_mul_nhdsWithin_Hbar a))
  have hQ1 : ∀ w : ℂ, 0 < w.re → 0 < w.im → M (G w) ∈ J := by
    set Q : Set ℂ := {w : ℂ | 0 < w.re ∧ 0 < w.im} with hQdef
    have hQ : IsPreconnected Q :=
      ((convex_halfSpace_gt (f := fun z : ℂ => z.re) Complex.reLm.isLinear 0).inter
        (convex_halfSpace_gt (f := fun z : ℂ => z.im) Complex.imLm.isLinear 0)).isPreconnected
    have hQH : Q ⊆ H := fun w hw => hw.2
    have hXsub : M '' (G '' Q) ⊆ J ∪ E := by
      rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      exact hQsub w (hQH hw) hw.1.ne'
    have hmeet : (M '' (G '' Q) ∩ J).Nonempty := by
      set x₁ : ℝ := v₁ - x with hx₁def
      have hx₁ : 0 < x₁ := by rw [hx₁def]; linarith
      have hGx₁ : G x₁ = F v₁ := by simp only [hGdef, hx₁def]; push_cast; ring_nf
      have hm := hMpos (G x₁) (by rw [hGx₁]; exact hv₁im) (by rw [hGx₁]; linarith [abs_nonneg Mb])
      obtain ⟨ρ, hρ, hsub⟩ := hball _ hm
      have hGx₁ne : G x₁ ≠ x₀ := fun h => by
        have := congrArg Complex.re h
        rw [hGx₁, ofReal_re] at this
        linarith [abs_nonneg Mb]
      obtain ⟨y, hyball, hy⟩ :=
        (((hlimM x₁ hGx₁ne).eventually (ball_mem_nhds _ hρ)).and self_mem_nhdsWithin).exists
      have hyQ : (x₁ : ℂ) + I * y ∈ Q := ⟨by simp [hx₁], by simpa using hy⟩
      exact ⟨_, ⟨_, ⟨_, hyQ, rfl⟩, rfl⟩, hsub ⟨hyball, poleInv_mem_H (hGb.mapsTo (hQH hyQ))⟩⟩
    have hXJ := (hpre Q hQ hQH).subset_left_of_subset_union hJo hEo hJE hXsub hmeet
    intro w hwre hwim
    exact hXJ ⟨_, ⟨w, ⟨hwre, hwim⟩, rfl⟩, rfl⟩
  have hQ2 : ∀ w : ℂ, w.re < 0 → 0 < w.im → M (G w) ∈ E := by
    set Q : Set ℂ := {w : ℂ | w.re < 0 ∧ 0 < w.im} with hQdef
    have hQ : IsPreconnected Q :=
      ((convex_halfSpace_lt (f := fun z : ℂ => z.re) Complex.reLm.isLinear 0).inter
        (convex_halfSpace_gt (f := fun z : ℂ => z.im) Complex.imLm.isLinear 0)).isPreconnected
    have hQH : Q ⊆ H := fun w hw => hw.2
    have hXsub : M '' (G '' Q) ⊆ J ∪ E := by
      rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      exact hQsub w (hQH hw) hw.1.ne
    have hmeet : (M '' (G '' Q) ∩ E).Nonempty := by
      set x₂ : ℝ := v₂ - x with hx₂def
      have hx₂ : x₂ < 0 := by rw [hx₂def]; linarith
      have hGx₂ : G x₂ = F v₂ := by simp only [hGdef, hx₂def]; push_cast; ring_nf
      have hGx₂r : G x₂ = (((F v₂).re : ℝ) : ℂ) := by
        rw [hGx₂]; exact Complex.ext rfl (by simp [hv₂im])
      have hGx₂ne : G x₂ ≠ x₀ := fun h => by
        have := congrArg Complex.re h
        rw [hGx₂, ofReal_re] at this
        linarith
      have hmE : M (G x₂) ∈ E := by
        have hnot : M (G x₂) ∉ Γ := by
          intro hΓ
          rcases hf1 _ hGx₂ne hΓ with hα | ⟨-, hre⟩
          · have hH' : G x₂ ∈ H := by
              obtain ⟨z, hz, hze⟩ := hαF hα
              rw [← hze]; exact hFb.mapsTo hz
            rw [hGx₂r] at hH'
            exact not_mem_H_ofReal _ hH'
          · rw [hGx₂] at hre; linarith
        have : M (G x₂) ∈ Γᶜ := hnot
        rw [hunion] at this
        refine this.resolve_left fun hJ => ?_
        have := hJH hJ
        rw [hGx₂r, hMdef, poleInv_ofReal] at this
        exact not_mem_H_ofReal _ this
      obtain ⟨ρ, hρ, hsub⟩ := Metric.isOpen_iff.1 hEo _ hmE
      obtain ⟨y, hyball, hy⟩ :=
        (((hlimM x₂ hGx₂ne).eventually (ball_mem_nhds _ hρ)).and self_mem_nhdsWithin).exists
      have hyQ : (x₂ : ℂ) + I * y ∈ Q := ⟨by simp [hx₂], by simpa using hy⟩
      exact ⟨_, ⟨_, ⟨_, hyQ, rfl⟩, rfl⟩, hsub hyball⟩
    have hXE := (hpre Q hQ hQH).subset_right_of_subset_union hJo hEo hJE hXsub hmeet
    intro w hwre hwim
    exact hXE ⟨_, ⟨w, ⟨hwre, hwim⟩, rfl⟩, rfl⟩
  -- the tip `η s = G(−x)` is on the outside
  have hsS : s ∈ Icc 0 s := ⟨hs.le, le_rfl⟩
  have hηs0 : η s ≠ 0 := hNR s ⟨hs, le_rfl⟩
  have hηsx : η s ≠ x₀ := hx₀S s hsS
  have hGtip : G (((-x : ℝ)) : ℂ) = η s := by rw [← htip]; simp only [hGdef]; push_cast; ring_nf
  have htipE : M (η s) ∈ E := by
    have hlim := hlimM (-x) (by rw [hGtip]; exact hηsx)
    rw [hGtip] at hlim
    have hcl : M (η s) ∈ closure (E ∩ H) := by
      refine mem_closure_of_tendsto hlim (eventually_nhdsWithin_of_forall fun y hy => ?_)
      have hy' : (0 : ℝ) < y := hy
      have hw : ((-x : ℝ) : ℂ) + I * y ∈ H := by show 0 < (((-x : ℝ) : ℂ) + I * y).im; simpa using hy'
      exact ⟨hQ2 _ (by simp; linarith) (by simpa using hy'), poleInv_mem_H (hGb.mapsTo hw)⟩
    by_contra hnE
    have hcl' : M (η s) ∈ closure E := closure_mono inter_subset_left hcl
    have hnJ : M (η s) ∉ J := fun hJ =>
      Set.disjoint_left.1 (hJE.closure_right hJo) hJ hcl'
    have hΓ : M (η s) ∈ Γ := by
      by_contra hnΓ
      have : M (η s) ∈ Γᶜ := hnΓ
      rw [hunion] at this
      exact this.elim hnJ hnE
    rcases hf1 _ hηsx hΓ with hα | ⟨him, hre⟩
    · exact hSF s hsS (hαF hα)
    · have hpos : 0 < (η s).re := lt_of_le_of_ne hre fun h =>
        hηs0 (Complex.ext (by rw [zero_re]; exact h.symm) (by rw [zero_im]; exact him))
      exact hseg_notE _ (hMpos _ him hpos) hcl
  -- the right point `F u = G(u − x)` is on the side `U`
  have huS : F u ≠ x₀ := by rw [← hvue]; exact hx₀S vu ⟨hvu.1.le, hvu.2⟩
  have hGu : G (((u - x : ℝ)) : ℂ) = F u := by simp only [hGdef]; push_cast; ring_nf
  have hrightU : M (F u) ∈ U := by
    have hlim := hlimM (u - x) (by rw [hGu]; exact huS)
    rw [hGu] at hlim
    have hcl : M (F u) ∈ closure J := by
      refine mem_closure_of_tendsto hlim (eventually_nhdsWithin_of_forall fun y hy => ?_)
      have hy' : (0 : ℝ) < y := hy
      exact hQ1 _ (by simp; linarith [hu.1]) (by simpa using hy')
    rw [closure_eq_self_union_frontier, hfr] at hcl
    rcases hcl with hJ | hΓ
    · exact Or.inl (Or.inl hJ)
    · rcases hf1 _ huS hΓ with hα | ⟨him, hre⟩
      · exact absurd (hαF hα) (by rw [← hvue]; exact hSF vu ⟨hvu.1.le, hvu.2⟩)
      · have hpos : 0 < (F u).re := lt_of_le_of_ne hre fun h =>
          hFu (Complex.ext (by rw [zero_re]; exact h.symm) (by rw [zero_im]; exact him))
        exact Or.inl (Or.inr (hMpos _ him hpos))
  -- the trace after time `0` lies on one side
  set S : Set ℂ := η '' Ioc 0 s with hSdef
  have hSc : ContinuousOn η (Ioc 0 s) := hη.2.1.mono fun v hv => (show (0 : ℝ) ≤ v from hv.1.le)
  have hSx : (x₀ : ℂ) ∉ S := by
    rintro ⟨v, hv, hve⟩
    exact hx₀S v ⟨hv.1.le, hv.2⟩ hve
  have hS' : IsPreconnected (M '' S) := (isPreconnected_Ioc.image η hSc).image M (continuousOn_poleInv hSx)
  have hS'sub : M '' S ⊆ U ∪ E := by
    rintro _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    have hvI : v ∈ Icc 0 s := ⟨hv.1.le, hv.2⟩
    by_cases hΓ : M (η v) ∈ Γ
    · rcases hf1 _ (hx₀S v hvI) hΓ with hα | ⟨him, hre⟩
      · exact absurd (hαF hα) (hSF v hvI)
      · have hpos : 0 < (η v).re := lt_of_le_of_ne hre fun h =>
          hNR v hv (Complex.ext (by rw [zero_re]; exact h.symm) (by rw [zero_im]; exact him))
        exact Or.inl (Or.inl (Or.inr (hMpos _ him hpos)))
    · have : M (η v) ∈ Γᶜ := hΓ
      rw [hunion] at this
      rcases this with hJ | hE
      · exact Or.inl (Or.inl (Or.inl hJ))
      · exact Or.inr hE
  have hS'disj : M '' S ∩ (U ∩ E) = ∅ := by
    refine Set.eq_empty_of_forall_notMem ?_
    rintro _ ⟨⟨_, ⟨v, hv, rfl⟩, rfl⟩, hzU, hzE⟩
    exact hUE _ (hMHbar _ (trace_mem_Hbar hη hW hW0 hv.1.le)) hzU hzE
  rcases isPreconnected_iff_subset_of_disjoint.1 hS' U E hUo hEo hS'sub hS'disj with hU | hE
  · exact hUE _ (hMHbar _ (trace_mem_Hbar hη hW hW0 hs.le))
      (hU ⟨_, ⟨s, ⟨hs, le_rfl⟩, rfl⟩, rfl⟩) htipE
  · have hFuS : M (F u) ∈ M '' S := ⟨_, ⟨vu, hvu, hvue⟩, rfl⟩
    exact hUE _ (hMHbar _ (by rw [← hvue]; exact trace_mem_Hbar hη hW hW0 hvu.1.le)) hrightU (hE hFuS)

end InteractingSLE.Sec5.Prop49Exit
