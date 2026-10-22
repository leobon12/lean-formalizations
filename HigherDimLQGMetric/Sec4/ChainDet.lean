import HigherDimLQGMetric.Sec4.Radii
import HigherDimLQGMetric.Shell.Chain

/-!
# The deterministic part of [1] Lemma 4.4 (packet L9b; MA6 P1, P10)

Given a family of "good" pairs `(u, r)` covering `U` (every `x ∈ U` has a good `(u, r)` with `ρ ≤ r ≤ ε'` and
`|x - u| < r/2`), and on each good pair the events (1)–(4) of [1] (4.5) in abstract form
(`A u r = c_r e^{ξ h_r(u)}`, `B u r = r 𝔞_{ε/r} e^{ξ h_r(u)}`):

* `l9b_chain_upper` ((4.9)): if `B ≤ M A` on good pairs, then
  `D̂(B_{10ε'}(z), B_{10ε'}(w); B_{10ε'}(U)) ≤ C² M D(z, w; U)`;
* `l9b_chain_lower` ((4.10)): if `m A ≤ B` on good pairs, then
  `D(B_{10ε'}(z), B_{10ε'}(w); B_{10ε'}(U)) ≤ (C²/m) D̂(z, w; U)`.

The chaining is W0's `sphere_chain` (port of LM's backward search; it repairs the "swallowed spheres" gap of
[1] Prop 3.13/Lemma 4.4, MA6 P1). The time increments are the `D`-length (resp. the LFPP length) of the path;
a crossing of `A_{r/2,r}(u)` during `[a, b]` costs at least the across distance (resp. the internal set
distance in `A_{r/3,3r}(u)`, DGZ's crossing lemma).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd e₁ lfppDistOn PcwJoined lfppLength)

variable {d : ℕ}

/-- `X ≤ c ⨅ f` from `X ≤ c f i` -/
theorem l9b_le_mul_iInf {ι : Sort*} {X c : ℝ≥0∞} (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    {f : ι → ℝ≥0∞} (h : ∀ i, X ≤ c * f i) : X ≤ c * ⨅ i, f i := by
  rw [ENNReal.mul_iInf_of_ne hc0 hct]
  exact le_iInf h

theorem l9b_ann_subset_thickening {U : Set (Rd d)} {x w : Rd d} {r ε' : ℝ} (hx : x ∈ U)
    (hxw : ‖x - w‖ < r / 2) (hr : r ≤ ε') : ann w (r / 2) (2 * r) ⊆ thickening (10 * ε') U := by
  intro y hy
  rw [mem_thickening_iff]
  refine ⟨x, hx, ?_⟩
  rw [dist_eq_norm]
  have h1 : ‖y - x‖ ≤ ‖y - w‖ + ‖x - w‖ := by
    calc ‖y - x‖ = ‖(y - w) - (x - w)‖ := by congr 1; abel
      _ ≤ _ := norm_sub_le _ _
  have := hy.2
  have hr0 : 0 < r := by
    have := norm_nonneg (x - w); linarith
  linarith

theorem l9b_ball_subset_thickening {U : Set (Rd d)} {z : Rd d} (hz : z ∈ U) (δ : ℝ) :
    ball z δ ⊆ thickening δ U :=
  fun _ hy => mem_thickening_iff.2 ⟨z, hz, hy⟩

/-- a path from `B_{r/2}(u)` to `∂B_r(u)` during `[a, b]` has `D`-length at least the across distance -/
theorem l9b_acrossDist_le_len (D₀ : ContMetric d) {P : ℝ → Rd d} {a b r : ℝ} {u : Rd d}
    (hab : a ≤ b) (hP : ContinuousOn P (Icc a b)) (ha : ‖P a - u‖ < r / 2) (hb : ‖P b - u‖ = r) :
    acrossDist D₀ u (r / 2) r ≤ D₀.len P a b := by
  have hcont : ContinuousOn (fun t => ‖P t - u‖) (Icc a b) := (hP.sub continuousOn_const).norm
  have hr0 : 0 ≤ r := hb ▸ norm_nonneg _
  obtain ⟨a', ha', ha'u⟩ := intermediate_value_Icc hab hcont
    ⟨ha.le, by rw [hb]; linarith⟩
  have hmem1 : P a' ∈ sphere u (r / 2) := by
    rw [mem_sphere, dist_eq_norm]; exact ha'u
  have hmem2 : P b ∈ sphere u r := by rw [mem_sphere, dist_eq_norm]; exact hb
  calc acrossDist D₀ u (r / 2) r ≤ ENNReal.ofReal (D₀.1 (P a', P b)) :=
        (iInf₂_le _ hmem1).trans (iInf₂_le _ hmem2)
    _ ≤ D₀.len P a' b := D₀.ofReal_le_len P ha'.2
    _ ≤ D₀.len P a b := D₀.len_mono P ha'.1 le_rfl

/-- **(4.9), deterministic** -/
theorem l9b_chain_upper (hd : 2 ≤ d) {ξ : ℝ} {ψ : Rd d → ℝ} (hψ : Continuous ψ)
    {D₀ : ContMetric d} {U : Set (Rd d)} {ρ ε' : ℝ} (hρ : 0 < ρ)
    (good : Rd d → ℝ → Prop) {A B : Rd d → ℝ → ℝ} {C M : ℝ} (hC : 0 < C) (hM : 0 < M)
    (hcov : ∀ x ∈ U, ∃ u r, ρ ≤ r ∧ r ≤ ε' ∧ ‖x - u‖ < r / 2 ∧ good u r)
    (hrε : ∀ u r, good u r → 0 < r ∧ r ≤ ε')
    (hA : ∀ u r, good u r → 0 ≤ A u r)
    (h1 : ∀ u r, good u r → ENNReal.ofReal (C⁻¹ * A u r) ≤ acrossDist D₀ u (r / 2) r)
    (h4 : ∀ u r, good u r → DGZ.lfppDiam ξ ψ (sphere u r) (ann u (r / 2) (2 * r)) ≤ C * B u r)
    (hBA : ∀ u r, good u r → B u r ≤ M * A u r) :
    ∀ z ∈ U, ∀ w ∈ U, fieldSetDistIn ξ ψ (thickening (10 * ε') U) (ball z (10 * ε'))
      (ball w (10 * ε')) ≤ ENNReal.ofReal (C ^ 2 * M) * D₀.internal U z w := by
  intro z hz w hw
  set V := thickening (10 * ε') U with hV
  set K := ENNReal.ofReal (C ^ 2 * M) with hKdef
  have hK0 : K ≠ 0 := by rw [hKdef]; exact (ENNReal.ofReal_pos.2 (by positivity)).ne'
  have hKt : K ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [D₀.internal_eq_iInf_len]
  refine l9b_le_mul_iInf hK0 hKt fun P => l9b_le_mul_iInf hK0 hKt fun hPc =>
    l9b_le_mul_iInf hK0 hKt fun hP0 => l9b_le_mul_iInf hK0 hKt fun hP1 =>
      l9b_le_mul_iInf hK0 hKt fun hPU => ?_
  by_cases hfin : D₀.len P 0 1 = ⊤
  · rw [hfin, ENNReal.mul_top hK0]; exact le_top
  -- the length clock
  have hlen_fin : ∀ t ∈ Icc (0 : ℝ) 1, D₀.len P 0 t ≠ ⊤ := fun t ht =>
    ne_top_of_le_ne_top hfin (D₀.len_mono P le_rfl ht.2)
  let ℓ : ℝ → ℝ := fun t => (D₀.len P 0 t).toReal
  have hℓ : MonotoneOn ℓ (Icc 0 1) := fun s hs t ht hst =>
    ENNReal.toReal_mono (hlen_fin t ht) (D₀.len_mono P le_rfl hst)
  have hinc : ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1, a ≤ b →
      ENNReal.ofReal (ℓ b - ℓ a) = D₀.len P a b := by
    intro a ha b hb hab
    have hadd := D₀.len_add P ha.1 hab
    have hfa := hlen_fin a ha
    have hfab : D₀.len P a b ≠ ⊤ := ne_top_of_le_ne_top (hlen_fin b hb)
      (D₀.len_mono P ha.1 le_rfl)
    have : ℓ b = ℓ a + (D₀.len P a b).toReal := by
      simp only [ℓ, ← hadd, ENNReal.toReal_add hfa hfab]
    rw [this, add_sub_cancel_left, ENNReal.ofReal_toReal hfab]
  -- the chain
  let δ : Rd d → Rd d → ℝ≥0∞ := diagPatch (fieldDistIn ξ ψ V)
  have hδ0 : ∀ x, δ x x = 0 := diagPatch_self _
  have hδt : ∀ x y z, δ x z ≤ δ x y + δ y z := diagPatch_triangle (fieldDistIn_triangle hψ)
  have hcov' : ∀ s ∈ Icc (0 : ℝ) 1, ∃ u r, ρ ≤ r ∧ r ≤ ε' ∧ ‖P s - u‖ < r / 2 ∧ good u r :=
    fun s hs => hcov (P s) (hPU hs)
  have hgood : ∀ u r, good u r → ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1, a ≤ b →
      ‖P a - u‖ < r / 2 → ‖P b - u‖ = r → ∀ x ∈ sphere u r, ∀ y ∈ sphere u r,
        δ x y ≤ K * ENNReal.ofReal (ℓ b - ℓ a) := by
    intro u r hg a ha b hb hab hPa hPb x hx y hy
    obtain ⟨hr, hrε'⟩ := hrε u r hg
    set Ann := ann u (r / 2) (2 * r)
    have hAnnV : Ann ⊆ V := l9b_ann_subset_thickening (hPU ha) hPa hrε'
    have hSA : sphere u r ⊆ Ann := l9b_sphere_subset_ann (by linarith) (by linarith)
    have hAo : IsOpen Ann := isOpen_ann _ _ _
    have hAc : IsPreconnected Ann := (config_isConnected_ann hd u (by positivity) (by linarith)).2
    have hj : PcwJoined Ann x y := DGZ.pcwJoined_of_isPreconnected hAo hAc (hSA hx) (hSA hy)
    have hbdd := DGZ.bddAbove_lfppDiam_of_isCompact hAo hAc hψ ξ (isCompact_sphere u r) hSA
      subset_rfl
    have hA0 := hA u r hg
    have hstep1 : δ x y ≤ ENNReal.ofReal (C * B u r) :=
      calc δ x y ≤ fieldDistIn ξ ψ V x y := diagPatch_le _ x y
        _ ≤ fieldDistIn ξ ψ Ann x y := fieldDistIn_mono hAnnV
        _ = ENNReal.ofReal (lfppDistOn ξ ψ Ann x y) := fieldDistIn_eq_ofReal hψ hj
        _ ≤ ENNReal.ofReal (DGZ.lfppDiam ξ ψ (sphere u r) Ann) :=
            ENNReal.ofReal_le_ofReal (DGZ.lfppDistOn_le_lfppDiam hbdd hx hy)
        _ ≤ ENNReal.ofReal (C * B u r) := ENNReal.ofReal_le_ofReal (h4 u r hg)
    have hstep2 : ENNReal.ofReal (C * B u r) ≤ K * ENNReal.ofReal (C⁻¹ * A u r) := by
      rw [hKdef, ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      have := hBA u r hg
      calc C * B u r ≤ C * (M * A u r) := by gcongr
        _ = C ^ 2 * M * (C⁻¹ * A u r) := by field_simp
    calc δ x y ≤ K * ENNReal.ofReal (C⁻¹ * A u r) := hstep1.trans hstep2
      _ ≤ K * acrossDist D₀ u (r / 2) r := by gcongr; exact h1 u r hg
      _ ≤ K * D₀.len P a b := by
          gcongr
          exact l9b_acrossDist_le_len D₀ hab (hPc.mono (Icc_subset_Icc ha.1 hb.2)) hPa hPb
      _ = K * ENNReal.ofReal (ℓ b - ℓ a) := by rw [hinc a ha b hb hab]
  obtain ⟨x, y, hx, hy, hxy⟩ := sphere_chain hd δ hδ0 hδt hρ P hPc ℓ hℓ good hcov' K hgood
  have hε'0 : 0 < ε' := by
    obtain ⟨u, r, -, hr, -, hg⟩ := hcov z hz
    exact (hrε u r hg).1.trans_le hr
  have hxB : x ∈ ball z (10 * ε') := by
    rw [mem_ball, dist_eq_norm, ← hP0]; linarith
  have hyB : y ∈ ball w (10 * ε') := by
    rw [mem_ball, dist_eq_norm, ← hP1]; linarith
  have hxV : x ∈ V := l9b_ball_subset_thickening hz _ hxB
  calc fieldSetDistIn ξ ψ V (ball z (10 * ε')) (ball w (10 * ε'))
      ≤ fieldDistIn ξ ψ V x y := (iInf₂_le x hxB).trans (iInf₂_le y hyB)
    _ ≤ δ x y := le_diagPatch fun hxy' => fieldDistIn_self hxV
    _ ≤ K * ENNReal.ofReal (ℓ 1 - ℓ 0) := hxy
    _ = K * D₀.len P 0 1 := by
        rw [hinc 0 ⟨le_rfl, zero_le_one⟩ 1 ⟨zero_le_one, le_rfl⟩ zero_le_one]

/-- **(4.10), deterministic** -/
theorem l9b_chain_lower (hd : 2 ≤ d) {ξ : ℝ} {ψ : Rd d → ℝ} (hψ : Continuous ψ)
    {D₀ : ContMetric d} {U : Set (Rd d)} {ρ ε' : ℝ} (hρ : 0 < ρ)
    (good : Rd d → ℝ → Prop) {A B : Rd d → ℝ → ℝ} {C m : ℝ} (hC : 0 < C) (hm : 0 < m)
    (hcov : ∀ x ∈ U, ∃ u r, ρ ≤ r ∧ r ≤ ε' ∧ ‖x - u‖ < r / 2 ∧ good u r)
    (hrε : ∀ u r, good u r → 0 < r ∧ r ≤ ε')
    (h2 : ∀ u r, good u r → sphereDiam D₀ u r ≤ ENNReal.ofReal (C * A u r))
    (h3 : ∀ u r, good u r → C⁻¹ * B u r ≤
      DGZ.lfppSetDist ξ ψ (ann u (r / 3) (3 * r)) (sphere u (r / 2)) (sphere u r))
    (hAB : ∀ u r, good u r → m * A u r ≤ B u r) :
    ∀ z ∈ U, ∀ w ∈ U, setDistIn D₀ (thickening (10 * ε') U) (ball z (10 * ε'))
      (ball w (10 * ε')) ≤ ENNReal.ofReal (C ^ 2 / m) * fieldDistIn ξ ψ U z w := by
  intro z hz w hw
  set V := thickening (10 * ε') U with hV
  set K := ENNReal.ofReal (C ^ 2 / m) with hKdef
  have hK0 : K ≠ 0 := by rw [hKdef]; exact (ENNReal.ofReal_pos.2 (by positivity)).ne'
  have hKt : K ≠ ⊤ := ENNReal.ofReal_ne_top
  refine l9b_le_mul_iInf hK0 hKt fun Pp => ?_
  obtain ⟨P, hPpath, hPU⟩ := Pp
  have hPc : ContinuousOn P (Icc 0 1) := hPpath.continuousOn
  -- the LFPP-length clock
  let ℓ : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, HigherDimLFPP.lfppIntegrand ξ ψ P s
  have hII := hPpath.intervalIntegrable_lfppIntegrand hψ ξ
  have hII' : ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1,
      IntervalIntegrable (HigherDimLFPP.lfppIntegrand ξ ψ P) volume a b := fun a ha b hb =>
    hII.mono_set (by
      rw [uIcc_of_le zero_le_one]
      exact uIcc_subset_Icc ha hb)
  have hinc : ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1,
      ℓ b - ℓ a = ∫ s in a..b, HigherDimLFPP.lfppIntegrand ξ ψ P s := by
    intro a ha b hb
    exact intervalIntegral.integral_interval_sub_left (hII' 0 ⟨le_rfl, zero_le_one⟩ b hb)
      (hII' 0 ⟨le_rfl, zero_le_one⟩ a ha)
  have hℓ : MonotoneOn ℓ (Icc 0 1) := by
    intro s hs t ht hst
    have := hinc s hs t ht
    have h0 : 0 ≤ ∫ u in s..t, HigherDimLFPP.lfppIntegrand ξ ψ P u :=
      intervalIntegral.integral_nonneg hst fun u _ => HigherDimLFPP.lfppIntegrand_nonneg ξ ψ P u
    linarith
  -- the chain
  let δ : Rd d → Rd d → ℝ≥0∞ := diagPatch (D₀.internal V)
  have hδ0 : ∀ x, δ x x = 0 := diagPatch_self _
  have hδt : ∀ x y z, δ x z ≤ δ x y + δ y z := diagPatch_triangle (D₀.internal_triangle V)
  have hcov' : ∀ s ∈ Icc (0 : ℝ) 1, ∃ u r, ρ ≤ r ∧ r ≤ ε' ∧ ‖P s - u‖ < r / 2 ∧ good u r :=
    fun s hs => hcov (P s) (hPU hs)
  have hgood : ∀ u r, good u r → ∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1, a ≤ b →
      ‖P a - u‖ < r / 2 → ‖P b - u‖ = r → ∀ x ∈ sphere u r, ∀ y ∈ sphere u r,
        δ x y ≤ K * ENNReal.ofReal (ℓ b - ℓ a) := by
    intro u r hg a ha b hb hab hPa hPb x hx y hy
    obtain ⟨hr, hrε'⟩ := hrε u r hg
    have hAnnV : ann u (r / 2) (2 * r) ⊆ V := l9b_ann_subset_thickening (hPU ha) hPa hrε'
    -- the crossing bound
    have hsh := DGZ.isShellPair_ball u (show r / 2 < r by linarith)
    have hshell : closedBall u r \ ball u (r / 2) ⊆ ann u (r / 3) (3 * r) := by
      intro v hv
      have h1 : ‖v - u‖ ≤ r := by rw [← dist_eq_norm]; exact hv.1
      have h2 : r / 2 ≤ ‖v - u‖ := by rw [← dist_eq_norm]; exact not_lt.1 hv.2
      exact ⟨by linarith, by linarith⟩
    have hcross := hsh.lfppSetDist_le_integral (ξ := ξ) hψ hshell hPpath ha.1 hab hb.2
      (Or.inl ⟨by rw [mem_closedBall, dist_eq_norm]; linarith,
        by rw [mem_ball, dist_eq_norm, hPb]; exact lt_irrefl r⟩)
    rw [closedBall_sdiff_ball, closedBall_sdiff_ball] at hcross
    have hB := (h3 u r hg).trans hcross
    have hA := hAB u r hg
    calc δ x y ≤ D₀.internal V x y := diagPatch_le _ x y
      _ ≤ D₀.internal (ann u (r / 2) (2 * r)) x y := D₀.internal_anti hAnnV x y
      _ ≤ sphereDiam D₀ u r := le_iSup₂_of_le x hx (le_iSup₂_of_le y hy le_rfl)
      _ ≤ ENNReal.ofReal (C * A u r) := h2 u r hg
      _ ≤ K * ENNReal.ofReal (ℓ b - ℓ a) := by
          rw [hKdef, ← ENNReal.ofReal_mul (by positivity), hinc a ha b hb]
          refine ENNReal.ofReal_le_ofReal ?_
          calc C * A u r ≤ C * (B u r / m) := by
                gcongr
                rw [le_div_iff₀ hm]; linarith
            _ = C ^ 2 / m * (C⁻¹ * B u r) := by field_simp
            _ ≤ C ^ 2 / m * ∫ s in a..b, HigherDimLFPP.lfppIntegrand ξ ψ P s := by
                gcongr
  obtain ⟨x, y, hx, hy, hxy⟩ := sphere_chain hd δ hδ0 hδt hρ P hPc ℓ hℓ good hcov' K hgood
  have hε'0 : 0 < ε' := by
    obtain ⟨u, r, -, hr, -, hg⟩ := hcov z hz
    exact (hrε u r hg).1.trans_le hr
  have hxB : x ∈ ball z (10 * ε') := by
    rw [mem_ball, dist_eq_norm, ← hPpath.source]; linarith
  have hyB : y ∈ ball w (10 * ε') := by
    rw [mem_ball, dist_eq_norm, ← hPpath.target]; linarith
  have hxV : x ∈ V := l9b_ball_subset_thickening hz _ hxB
  calc setDistIn D₀ V (ball z (10 * ε')) (ball w (10 * ε'))
      ≤ D₀.internal V x y := (iInf₂_le x hxB).trans (iInf₂_le y hyB)
    _ ≤ δ x y := le_diagPatch fun _ => D₀.internal_self hxV
    _ ≤ K * ENNReal.ofReal (ℓ 1 - ℓ 0) := hxy
    _ = K * lfppLen ξ ψ P := by
        rw [lfppLen_eq_ofReal hψ hPpath, hinc 0 ⟨le_rfl, zero_le_one⟩ 1 ⟨zero_le_one, le_rfl⟩,
          HigherDimLFPP.lfppLength_eq_integral]

end HigherDimLQGMetric
