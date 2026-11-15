/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Foundations.Loewner.YuanCorollary13Tip
import InteractingSLE.Foundations.SLE.SpaceFilling.SwallowReal
import InteractingSLE.Spec.Dimension.TraceBridge

/-!
# A real point swallowed at a finite time: the trace ends on the real line

Packet PROVE-ENDPOINT (the deterministic Loewner fact behind `Supp10.FiniteEndpointRealStatement`,
supplement p. 543: "a genuine finite continuation endpoint is original-real"). Conventions of
QuantumZipper: `U : ℝ → ℝ` is a continuous driver with `U 0 = 0`, `K_t = fwdHull U t`, and
`G_t = fwdMap U t` is the centred map `g_t − U_t`.

## Main results

* `not_tendsto_fwdMap_of_disjoint_ray`: let `y₀ > 0` be alive on `[0, r]` for every `r < σ`. If an
  `ε`-neighbourhood of the ray `[y₀, ∞)` avoids every hull `K_r`, `r < σ`, then `G_r(y₀) ↛ 0` as
  `r ↑ σ`: a real point is not swallowed at `σ` while a fixed neighbourhood of it stays off the
  hulls.
* `notMem_H_of_tendsto_fwdMap`: let `γ` be continuous on `[0, T]` with `K_t = fill(γ[0, t])` for
  `t < T`, and let a real point `y₀ > 0` be alive before `T` with `G_r(y₀) → 0` as `r ↑ T`. Then
  `γ(T) ∉ ℍ`.

## Proof

*The ray lemma.* For `r < σ` the maps `G_r` reflect across the real axis near the ray
(`centredRefl`, built from `YuanCorollary13.exists_centred_reflection`); the reflections are
uniformly Cauchy as `r ↑ σ` (`‖G_s − G_r‖ ≤ 24 M + 8 √(r − s)`, `M` the oscillation of `U` on
`[s, r]`), so they converge locally uniformly to a holomorphic `G` near the ray. Put
`c_n = y₀ + n ε/4`. If `G(c_n) = 0`, then either `G` has an isolated zero at `c_n` or `G ≡ 0` on
`B(c_n, ε/2)`. An isolated zero is impossible: by the maximum modulus principle every small value
`w ∈ ℍ` is a `G_r`-value on a small disc around `c_n` for `r` close to `σ`, while local and strict
growth (`YuanCorollary13.not_disjoint_of_ball_subset_image`) produce a point of `K_{r'} \ K_r`,
`r < r' < σ`, mapped by `G_r` near `0`, which would lie in `B(c_n, ε)` (this is the argument of
`YuanCorollary13.mem_closure_fwdHull_of_tendsto`, with the limit map in place of the map at the
final time). So `G ≡ 0` near `c_n` and `G(c_{n+1}) = 0`. By induction `G_r(c_n) → 0` for every
`n`, which is false for `c_n > 1 + sup |U|`: there `G_r(c_n) ≥ c_n − U_r ≥ 1` (the uncentred real
flow is nondecreasing).

*The endpoint.* Suppose `γ(T) ∈ ℍ`. Before `T` the trace does not meet `[y₀, ∞)`: a point `b ≥ y₀`
is alive at `t < T` (monotonicity of the real flow in its starting point), so a ball around `b`
avoids `K_t` (`not_mem_fwdHull_of_isForwardSol`), while the tip `γ(t)` lies in the closure of
`K_t` for `t > 0` (`IsLoewnerTraceLT.tendsto_fwdMapInv_tip`,
`YuanCorollary13.mem_closure_fwdHull_of_tendsto`). Hence `γ([0, T])` is at a positive distance
`d` from the ray. For `y ≥ y₀` and `t < T` the set `(B(y, d/2) ∩ ℍ) ∪ {y ≤ Re w, 0 < Im w < d/2}`
is connected, unbounded and avoids `γ([0, t])`, so it lies in the unbounded component of
`ℍ \ γ([0, t])`: `B(y, d/2)` avoids `K_t`. The ray lemma contradicts `G_r(y₀) → 0`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped ComplexConjugate

open QuantumZipper (H Hbar fwdHull fwdMap fwdMapInv IsForwardSol)
open QuantumZipper.RS (shiftDrive)

namespace InteractingSLE

namespace FiniteEndpoint

variable {U : ℝ → ℝ}

/-! ### The reflected centred map -/

open Classical in
/-- The centred map `G_s = fwdMap U s` reflected across the real axis: `G_s` on `ℍ`,
`z ↦ conj (G_s (conj z))` on the lower half-plane, and the boundary limit of `G_s` from `ℍ` at real
points. Near a real point whose neighbourhood avoids `K_s` it is the Schwarz reflection of `G_s`
(`centredRefl_spec`). -/
def centredRefl (U : ℝ → ℝ) (s : ℝ) (z : ℂ) : ℂ :=
  if 0 < z.im then fwdMap U s z
  else if z.im < 0 then conj (fwdMap U s (conj z))
  else limUnder (𝓝[H] z) (fwdMap U s)

theorem conj_mem_ball_ofReal {y r : ℝ} {z : ℂ} (hz : z ∈ ball (y : ℂ) r) :
    conj z ∈ ball (y : ℂ) r := by
  rw [mem_ball, dist_eq_norm, ← Complex.conj_ofReal, ← map_sub, Complex.norm_conj,
    ← dist_eq_norm]
  exact hz

theorem neBot_nhdsWithin_H {z : ℂ} (hz : z.im = 0) : (𝓝[H] z).NeBot := by
  rw [← mem_closure_iff_nhdsWithin_neBot, closure_H]
  show (0 : ℝ) ≤ z.im
  exact hz.ge

/-- `centredRefl` agrees with every Schwarz reflection of `G_s` on the ball. -/
theorem eqOn_centredRefl {s y κ : ℝ} {K : ℂ → ℂ}
    (hKeq : EqOn K (fwdMap U s) (ball (y : ℂ) (κ / 2) ∩ H))
    (hKc : ∀ z ∈ ball (y : ℂ) (κ / 2), K (conj z) = conj (K z))
    (hKt : ∀ z ∈ ball (y : ℂ) (κ / 2), z.im = 0 →
      Tendsto (fwdMap U s) (𝓝[ball (y : ℂ) (κ / 2) ∩ H] z) (𝓝 (K z))) :
    EqOn (centredRefl U s) K (ball (y : ℂ) (κ / 2)) := by
  intro z hz
  rcases lt_trichotomy z.im 0 with hneg | h0 | hpos
  · have hcz := conj_mem_ball_ofReal hz
    have hczH : 0 < (conj z).im := by rw [Complex.conj_im]; linarith
    have h2 := hKc (conj z) hcz
    rw [Complex.conj_conj] at h2
    rw [h2, hKeq ⟨hcz, hczH⟩]
    simp only [centredRefl, not_lt.2 hneg.le, hneg, ite_true, ite_false]
  · have ht := hKt z hz h0
    rw [nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds hz))] at ht
    have := neBot_nhdsWithin_H h0
    simp only [centredRefl, h0, lt_irrefl, ite_false]
    exact ht.limUnder_eq
  · simp only [centredRefl, hpos, ite_true]
    exact (hKeq ⟨hz, hpos⟩).symm

/-- **The reflected centred map.** If `B(y, κ)` (`y ∈ ℝ`) avoids `K_s`, then `centredRefl U s` is
holomorphic on `B(y, κ/2)`, equals `G_s` on the upper half-ball, is conjugation-symmetric, real on
the real diameter, and is the boundary limit of `G_s` at real points. -/
theorem centredRefl_spec (hU : Continuous U) (hU0 : U 0 = 0) {s y κ : ℝ} (hs : 0 ≤ s)
    (hd : Disjoint (ball (y : ℂ) κ) (fwdHull U s)) :
    DifferentiableOn ℂ (centredRefl U s) (ball (y : ℂ) (κ / 2)) ∧
      EqOn (centredRefl U s) (fwdMap U s) (ball (y : ℂ) (κ / 2) ∩ H) ∧
      (∀ z ∈ ball (y : ℂ) (κ / 2), centredRefl U s (conj z) = conj (centredRefl U s z)) ∧
      (∀ z ∈ ball (y : ℂ) (κ / 2), z.im = 0 → (centredRefl U s z).im = 0) ∧
      (∀ z ∈ ball (y : ℂ) (κ / 2), z.im = 0 →
        Tendsto (fwdMap U s) (𝓝[ball (y : ℂ) (κ / 2) ∩ H] z) (𝓝 (centredRefl U s z))) := by
  obtain ⟨K, hKd, hKeq, hKc, hKr, hKt⟩ := YuanCorollary13.exists_centred_reflection hU hU0 hs hd
  have he := eqOn_centredRefl hKeq hKc hKt
  refine ⟨hKd.congr he, fun z hz => (he hz.1).trans (hKeq hz), fun z hz => ?_,
    fun z hz h0 => ?_, fun z hz h0 => ?_⟩
  · rw [he (conj_mem_ball_ofReal hz), he hz]; exact hKc z hz
  · rw [he hz]; exact hKr z hz h0
  · rw [he hz]; exact hKt z hz h0

/-- At a real point alive at time `s`, the reflected map is the value of the real flow. -/
theorem centredRefl_eq_of_isForwardSol (hU : Continuous U) {s : ℝ} (hs : 0 ≤ s) {x : ℝ}
    {u : ℝ → ℂ} (hu : IsForwardSol U (x : ℂ) s u) : centredRefl U s x = fwdMap U s x := by
  have h0 : (x : ℂ).im = 0 := Complex.ofReal_im x
  have := neBot_nhdsWithin_H h0
  simp only [centredRefl, h0, lt_irrefl, ite_false]
  rw [(tendsto_fwdMap_of_isForwardSol hU hs hu).limUnder_eq,
    fwdMap_eq_of_isForwardSol hU hu ⟨hs, le_rfl⟩]

/-- **Uniform displacement of the reflections** between two times `s < r`. -/
theorem norm_centredRefl_sub_le (hU : Continuous U) (hU0 : U 0 = 0) {s r M y κ : ℝ}
    (hs : 0 ≤ s) (hsr : s < r) (hκ : 0 < κ) (hd : Disjoint (ball (y : ℂ) κ) (fwdHull U r))
    (hM : ∀ x ∈ Icc (0 : ℝ) (r - s), |shiftDrive U s x| ≤ M) :
    ∀ z ∈ ball (y : ℂ) (κ / 2),
      ‖centredRefl U s z - centredRefl U r z‖ ≤ 24 * M + 8 * Real.sqrt (r - s) := by
  have hds : Disjoint (ball (y : ℂ) κ) (fwdHull U s) := hd.mono_right (fwdHull_mono' hsr.le)
  obtain ⟨-, hseq, hsc, -, hst⟩ := centredRefl_spec hU hU0 hs hds
  obtain ⟨-, hreq, hrc, -, hrt⟩ := centredRefl_spec hU hU0 (hs.trans hsr.le) hd
  exact YuanCorollary13.norm_sub_le_of_reflections hseq hreq hsc hrc hst hrt fun z hz =>
    YuanCorollary13.norm_fwdMap_sub_fwdMap_le hU hs hsr hM
      ⟨hz.2, fun h => Set.disjoint_left.1 hd (ball_subset_ball (by linarith) hz.1) h⟩

/-- A family that is uniformly Cauchy on `S` as `r ↑ σ` converges uniformly on `S`. -/
theorem exists_tendstoUniformlyOn_nhdsLT {F : ℝ → ℂ → ℂ} {S : Set ℂ} {σ : ℝ}
    (hF : ∀ η > 0, ∃ a < σ, ∀ s r, a < s → s < σ → a < r → r < σ → ∀ z ∈ S,
      ‖F s z - F r z‖ ≤ η) :
    ∃ G : ℂ → ℂ, TendstoUniformlyOn F G (𝓝[<] σ) S := by
  have hlim : ∀ z ∈ S, ∃ g, Tendsto (fun r => F r z) (𝓝[<] σ) (𝓝 g) := by
    intro z hz
    refine cauchy_map_iff_exists_tendsto.1 ?_
    rw [Metric.cauchy_iff]
    refine ⟨map_neBot, fun η hη => ?_⟩
    obtain ⟨a, haσ, ha⟩ := hF (η / 2) (half_pos hη)
    refine ⟨(fun r => F r z) '' Ioo a σ, image_mem_map (Ioo_mem_nhdsLT haσ), ?_⟩
    rintro _ ⟨s, hs, rfl⟩ _ ⟨r, hr, rfl⟩
    rw [dist_eq_norm]
    exact (ha s r hs.1 hs.2 hr.1 hr.2 z hz).trans_lt (half_lt_self hη)
  choose! G hG using hlim
  refine ⟨G, Metric.tendstoUniformlyOn_iff.2 fun η hη => ?_⟩
  obtain ⟨a, haσ, ha⟩ := hF (η / 2) (half_pos hη)
  filter_upwards [Ioo_mem_nhdsLT haσ] with s hs z hz
  have h1 : Tendsto (fun r => ‖F s z - F r z‖) (𝓝[<] σ) (𝓝 ‖F s z - G z‖) :=
    ((hG z hz).const_sub _).norm
  have h2 : ‖F s z - G z‖ ≤ η / 2 := le_of_tendsto h1 (by
    filter_upwards [Ioo_mem_nhdsLT haσ] with r hr using ha s r hs.1 hs.2 hr.1 hr.2 z hz)
  rw [dist_eq_norm, norm_sub_rev]
  linarith

/-! ### The step: a zero of the limit map propagates -/

/-- **One step of the ray lemma.** Suppose `B(c, ε)` (`c ∈ ℝ`) avoids `K_r` for every `r < σ`
and the reflected maps at `c` tend to `0` as `r ↑ σ`. Then they tend to `0` at every point of
`B(c, ε/2)`. -/
theorem tendsto_centredRefl_of_tendsto (hU : Continuous U) (hU0 : U 0 = 0) {σ ε c : ℝ}
    (hσ : 0 < σ) (hε : 0 < ε)
    (hd : ∀ r ∈ Ico (0 : ℝ) σ, Disjoint (ball (c : ℂ) ε) (fwdHull U r))
    (h0 : Tendsto (fun r => centredRefl U r c) (𝓝[<] σ) (𝓝 0)) :
    ∀ z ∈ ball (c : ℂ) (ε / 2), Tendsto (fun r => centredRefl U r z) (𝓝[<] σ) (𝓝 0) := by
  set B := ball (c : ℂ) (ε / 2) with hB
  -- the reflections are uniformly Cauchy
  have hcauchy : ∀ η > 0, ∃ a < σ, ∀ s r, a < s → s < σ → a < r → r < σ → ∀ z ∈ B,
      ‖centredRefl U s z - centredRefl U r z‖ ≤ η := by
    intro η hη
    obtain ⟨δ, hδ, hδU⟩ := Metric.uniformContinuousOn_iff.1
      (isCompact_Icc.uniformContinuousOn_of_continuous (hU.continuousOn (s := Icc 0 σ)))
      (η / 48) (by positivity)
    set g := min (δ / 2) ((η / 16) ^ 2) with hg
    have hg0 : 0 < g := lt_min (by positivity) (by positivity)
    set a := max 0 (σ - g) with ha
    have haσ : a < σ := max_lt hσ (by linarith)
    refine ⟨a, haσ, ?_⟩
    have key : ∀ s r, a < s → s < r → r < σ → ∀ z ∈ B,
        ‖centredRefl U s z - centredRefl U r z‖ ≤ η := by
      intro s r has hsr hrσ z hz
      have hs0 : 0 ≤ s := (le_max_left _ _).trans has.le
      have hgap : r - s < g := by have := le_max_right 0 (σ - g); linarith
      have hM : ∀ x ∈ Icc (0 : ℝ) (r - s), |shiftDrive U s x| ≤ η / 48 := by
        intro x hx
        have h1 := hδU (s + x) ⟨by linarith [hx.1], by linarith [hx.2]⟩ s ⟨hs0, by linarith⟩
          (by
            rw [Real.dist_eq, show s + x - s = x by ring, abs_of_nonneg hx.1]
            linarith [min_le_left (δ / 2) ((η / 16) ^ 2), hx.2])
        rw [Real.dist_eq] at h1
        exact h1.le
      have hb := norm_centredRefl_sub_le hU hU0 hs0 hsr hε (hd r ⟨hs0.trans hsr.le, hrσ⟩) hM z hz
      have hsq : Real.sqrt (r - s) ≤ η / 16 := by
        calc Real.sqrt (r - s) ≤ Real.sqrt ((η / 16) ^ 2) :=
              Real.sqrt_le_sqrt (by linarith [min_le_right (δ / 2) ((η / 16) ^ 2)])
          _ = η / 16 := Real.sqrt_sq (by positivity)
      linarith
    intro s r has hsσ har hrσ z hz
    rcases lt_trichotomy s r with hsr | hsr | hrs
    · exact key s r has hsr hrσ z hz
    · rw [hsr, sub_self, norm_zero]; exact hη.le
    · rw [norm_sub_rev]; exact key r s har hrs hsσ z hz
  obtain ⟨G, hG⟩ := exists_tendstoUniformlyOn_nhdsLT hcauchy
  have hdiffG : DifferentiableOn ℂ G B := by
    refine hG.tendstoLocallyUniformlyOn.differentiableOn ?_ isOpen_ball
    filter_upwards [Ioo_mem_nhdsLT hσ] with r hr
    exact (centredRefl_spec hU hU0 hr.1.le (hd r ⟨hr.1.le, hr.2⟩)).1
  have hcB : (c : ℂ) ∈ B := mem_ball_self (by positivity)
  have hGc : G c = 0 := tendsto_nhds_unique (hG.tendsto_at hcB) h0
  rcases (hdiffG.analyticAt (isOpen_ball.mem_nhds hcB)).eventually_eq_zero_or_eventually_ne_zero
    with hzero | hne
  · have hEq := (hdiffG.analyticOnNhd isOpen_ball).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball _ _).isPreconnected hcB hzero
    intro z hz
    have := hG.tendsto_at hz
    rwa [hEq hz] at this
  · exfalso
    obtain ⟨ρ₁, hρ₁, hρ₁G⟩ : ∃ ρ₁ > 0, ∀ z : ℂ, dist z c < ρ₁ → z ≠ c → G z ≠ 0 := by
      rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hne
      obtain ⟨ρ₁, hρ₁, h⟩ := hne
      exact ⟨ρ₁, hρ₁, fun z hz hzc => h hz hzc⟩
    set ρ := min (ρ₁ / 2) (ε / 8) with hρ
    have hρ0 : 0 < ρ := lt_min (by positivity) (by positivity)
    have hρ1 : ρ ≤ ρ₁ / 2 := min_le_left _ _
    have hρε : ρ ≤ ε / 8 := min_le_right _ _
    have hsph_sub : sphere (c : ℂ) ρ ⊆ B := fun z hz => by
      rw [mem_sphere] at hz
      rw [hB, mem_ball, hz]
      linarith
    obtain ⟨z₀, hz₀, hmin⟩ := (isCompact_sphere (c : ℂ) ρ).exists_isMinOn
      (NormedSpace.sphere_nonempty.2 hρ0.le) ((hdiffG.mono hsph_sub).continuousOn.norm)
    set m₀ := ‖G z₀‖ with hm₀
    have hm₀pos : 0 < m₀ := by
      rw [mem_sphere] at hz₀
      refine norm_pos_iff.2 (hρ₁G z₀ (by rw [hz₀]; linarith) fun h => ?_)
      rw [h, dist_self] at hz₀
      linarith
    have hmin' : ∀ z ∈ sphere (c : ℂ) ρ, m₀ ≤ ‖G z‖ := fun z hz => hmin hz
    obtain ⟨r, hrclose, hr⟩ := ((Metric.tendstoUniformlyOn_iff.1 hG (m₀ / 5) (by positivity)).and
      (Ioo_mem_nhdsLT hσ)).exists
    have hdr := hd r ⟨hr.1.le, hr.2⟩
    obtain ⟨hKd, hKeq, hKc, hKr, -⟩ := centredRefl_spec hU hU0 hr.1.le hdr
    have himg : ∀ w ∈ ball (0 : ℂ) (m₀ / 4) ∩ H, ∃ z ∈ ball (c : ℂ) ε ∩ H, fwdMap U r z = w := by
      rintro w ⟨hw, hwH⟩
      rw [mem_ball, dist_zero_right] at hw
      obtain ⟨z, hz, hKz⟩ := YuanCorollary13.exists_eq_zero_of_norm_lt
        (f := fun z => centredRefl U r z - w) (c := (c : ℂ)) (ρ := ρ) (R := ε / 2) (m := m₀ / 2)
        hρ0 (by linarith) (hKd.sub_const w) (fun z hz => by
          have h1 := hmin' z hz
          have h2 := hrclose z (hsph_sub hz)
          rw [dist_eq_norm] at h2
          have h3 : ‖G z‖ ≤ ‖centredRefl U r z - w‖ + ‖G z - centredRefl U r z‖ + ‖w‖ := by
            calc ‖G z‖ = ‖(centredRefl U r z - w) + (G z - centredRefl U r z) + w‖ := by ring_nf
              _ ≤ ‖(centredRefl U r z - w) + (G z - centredRefl U r z)‖ + ‖w‖ := norm_add_le _ _
              _ ≤ ‖centredRefl U r z - w‖ + ‖G z - centredRefl U r z‖ + ‖w‖ := by
                gcongr; exact norm_add_le _ _
          show m₀ / 2 < ‖centredRefl U r z - w‖
          linarith)
        (by
          have h2 := hrclose c hcB
          rw [dist_eq_norm, hGc, zero_sub, norm_neg] at h2
          show ‖centredRefl U r c - w‖ < m₀ / 2
          calc ‖centredRefl U r c - w‖ ≤ ‖centredRefl U r c‖ + ‖w‖ := norm_sub_le _ _
            _ < m₀ / 2 := by linarith)
      have hKzw : centredRefl U r z = w := sub_eq_zero.1 hKz
      have hzb : z ∈ ball (c : ℂ) (ε / 2) := by
        rw [mem_closedBall] at hz
        rw [mem_ball]
        linarith
      have hz0 : z.im ≠ 0 := fun h0 => by
        have := hKr z hzb h0
        rw [hKzw] at this
        have hw0 : (0 : ℝ) < w.im := hwH
        linarith
      have hzH : 0 < z.im :=
        ((YuanCorollary13.im_pos_of_centred_reflection hU hr.1.le hdr hKeq hKc hzb hz0).1).2
          (by rw [hKzw]; exact hwH)
      exact ⟨z, ⟨ball_subset_ball (by linarith) hzb, hzH⟩, (hKeq ⟨hzb, hzH⟩).symm.trans hKzw⟩
    have hr' : (r + σ) / 2 ∈ Ico (0 : ℝ) σ := ⟨by linarith [hr.1], by linarith [hr.2]⟩
    exact YuanCorollary13.not_disjoint_of_ball_subset_image hU hU0 hr.1.le
      (by linarith [hr.2] : r < (r + σ) / 2) (by positivity) himg (hd _ hr')

/-! ### The ray lemma -/

/-- **A real point is not swallowed while a neighbourhood of its ray stays off the hulls.** Let
`y₀ > 0` be alive on `[0, r]` for every `r < σ`, and let the `ε`-neighbourhood of `[y₀, ∞)` avoid
every hull `K_r`, `r < σ`. Then `G_r(y₀) ↛ 0` as `r ↑ σ`. -/
theorem not_tendsto_fwdMap_of_disjoint_ray (hU : Continuous U) (hU0 : U 0 = 0) {σ y₀ ε : ℝ}
    (hσ : 0 < σ) (hy₀ : 0 < y₀) (hε : 0 < ε)
    (hd : ∀ r ∈ Ico (0 : ℝ) σ, ∀ y : ℝ, y₀ ≤ y → Disjoint (ball (y : ℂ) ε) (fwdHull U r))
    (halive : ∀ r ∈ Ico (0 : ℝ) σ, ∃ u, IsForwardSol U (y₀ : ℂ) r u) :
    ¬ Tendsto (fun r => fwdMap U r y₀) (𝓝[<] σ) (𝓝 0) := by
  intro hlim
  set y : ℕ → ℝ := fun n => y₀ + n * (ε / 4) with hy
  have hyn : ∀ n : ℕ, y n = y₀ + n * (ε / 4) := fun n => rfl
  have hyge : ∀ n, y₀ ≤ y n := fun n => by
    rw [hyn]
    have : 0 ≤ (n : ℝ) * (ε / 4) := by positivity
    linarith
  have halive' : ∀ n, ∀ r ∈ Ico (0 : ℝ) σ, ∃ u, IsForwardSol U (y n : ℂ) r u := by
    intro n r hr
    obtain ⟨u, hu⟩ := halive r hr
    rcases (hyge n).lt_or_eq with hlt | heq
    · exact QuantumZipper.RS.exists_isForwardSol_of_lt hU hr.1 (by rw [hU0]; exact hy₀) hlt hu
    · exact ⟨u, heq ▸ hu⟩
  have hev : ∀ n, (fun r => fwdMap U r (y n)) =ᶠ[𝓝[<] σ] fun r => centredRefl U r (y n) := by
    intro n
    filter_upwards [Ioo_mem_nhdsLT hσ] with r hr
    obtain ⟨u, hu⟩ := halive' n r ⟨hr.1.le, hr.2⟩
    exact (centredRefl_eq_of_isForwardSol hU hr.1.le hu).symm
  have hP : ∀ n : ℕ, Tendsto (fun r => fwdMap U r (y n)) (𝓝[<] σ) (𝓝 0) := by
    intro n
    induction n with
    | zero => simpa [hyn] using hlim
    | succ n ih =>
      have h1 : Tendsto (fun r => centredRefl U r (y n)) (𝓝[<] σ) (𝓝 0) := ih.congr' (hev n)
      have hmem : ((y (n + 1) : ℝ) : ℂ) ∈ ball ((y n : ℝ) : ℂ) (ε / 2) := by
        rw [mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
          hyn, hyn]
        push_cast
        rw [show y₀ + ((n : ℝ) + 1) * (ε / 4) - (y₀ + n * (ε / 4)) = ε / 4 by ring,
          abs_of_pos (by positivity)]
        linarith
      have h2 := tendsto_centredRefl_of_tendsto hU hU0 hσ hε
        (fun r hr => hd r hr (y n) (hyge n)) h1 _ hmem
      exact h2.congr' (hev (n + 1)).symm
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (hU.continuousOn (s := Icc 0 σ))
  obtain ⟨n, hn⟩ : ∃ n : ℕ, M + 1 ≤ n * (ε / 4) := by
    obtain ⟨n, hn⟩ := exists_nat_ge ((M + 1) / (ε / 4))
    exact ⟨n, by rwa [div_le_iff₀ (by positivity)] at hn⟩
  have hlow : ∀ r ∈ Ico (0 : ℝ) σ, 1 ≤ ‖fwdMap U r (y n)‖ := by
    intro r hr
    obtain ⟨v, hv⟩ := halive' n r hr
    have hy0n : 0 < y n := hy₀.trans_le (hyge n)
    have hmono := re_add_monotoneOn hU hU0 hy0n hr.1 hv
    have h0 : (v 0).re + U 0 = y n := by
      rw [(hv.2 0 ⟨le_rfl, hr.1⟩).2]
      simp [hU0]
    have hle := hmono ⟨le_rfl, hr.1⟩ ⟨hr.1, le_rfl⟩ hr.1
    simp only at hle
    rw [h0] at hle
    have hUr := hM r ⟨hr.1, hr.2.le⟩
    rw [Real.norm_eq_abs] at hUr
    rw [fwdMap_eq_of_isForwardSol hU hv ⟨hr.1, le_rfl⟩]
    have hab := le_abs_self (U r)
    have := hyn n
    calc (1 : ℝ) ≤ (v r).re := by linarith
      _ ≤ ‖v r‖ := Complex.re_le_norm _
  have hev2 := (hP n).eventually (Metric.ball_mem_nhds (0 : ℂ) one_pos)
  obtain ⟨r, hr1, hr2⟩ := (hev2.and (Ioo_mem_nhdsLT hσ)).exists
  rw [dist_zero_right] at hr1
  linarith [hlow r ⟨hr2.1.le, hr2.2⟩]

/-! ### The endpoint of the trace -/

/-- A point of `ℂ` whose real and imaginary parts are small has small norm. -/
theorem norm_lt_of_abs_re_add_abs_im_lt {z : ℂ} {a : ℝ} (h : |z.re| + |z.im| < a) : ‖z‖ < a :=
  (Complex.norm_le_abs_re_add_abs_im z).trans_lt h

/-- **The trace ends on the real line when a real point is swallowed.** Let `γ` be continuous on
`[0, T]` with `γ 0 = 0` and `K_t = fill(γ[0, t])` (the frozen `IsFilling`) for `t < T`, and let a
real point `y₀ > 0` be alive on every `[0, r]`, `r < T`, with `G_r(y₀) → 0` as `r ↑ T`. Then
`γ(T) ∉ ℍ`. -/
theorem notMem_H_of_tendsto_fwdMap (hU : Continuous U) (hU0 : U 0 = 0) {T y₀ : ℝ} (hT : 0 < T)
    (hy₀ : 0 < y₀) {γ : ℝ → ℂ} (hγ0 : γ 0 = 0) (hγc : ContinuousOn γ (Icc 0 T))
    (hfill : ∀ t ∈ Ico (0 : ℝ) T, IsFilling (fwdHull U t) (γ '' Icc 0 t))
    (halive : ∀ r ∈ Ico (0 : ℝ) T, ∃ u, IsForwardSol U (y₀ : ℂ) r u)
    (hlim : Tendsto (fun r => fwdMap U r y₀) (𝓝[<] T) (𝓝 0)) : γ T ∉ H := by
  intro hγT
  have hcpt : ∀ t ∈ Icc (0 : ℝ) T, IsCompact (γ '' Icc 0 t) := fun t ht =>
    isCompact_Icc.image_of_continuousOn (hγc.mono (Icc_subset_Icc le_rfl ht.2))
  have hfillH : ∀ t ∈ Ico (0 : ℝ) T, fwdHull U t = fillH (γ '' Icc 0 t) := fun t ht =>
    (fillH_eq_iff_isFilling_of_isClosed (hcpt t (Ico_subset_Icc_self ht)).isBounded
      (hcpt t (Ico_subset_Icc_self ht)).isClosed (fun z hz => hz.1)).1 (hfill t ht)
  have htrace : IsLoewnerTraceLT U T γ :=
    ⟨hγ0, hγc.mono Ico_subset_Icc_self, fun t ht htT => hfillH t ⟨ht, htT⟩⟩
  -- Step 1: the trace does not meet the ray `[y₀, ∞)`
  have hstep1 : ∀ t ∈ Icc (0 : ℝ) T, ∀ b : ℝ, y₀ ≤ b → γ t ≠ b := by
    intro t ht b hb heq
    rcases ht.2.lt_or_eq with htT | htT
    · rcases ht.1.lt_or_eq with ht0 | ht0
      · obtain ⟨u, hu⟩ := halive t ⟨ht.1, htT⟩
        obtain ⟨v, hv⟩ : ∃ v, IsForwardSol U (b : ℂ) t v := by
          rcases hb.lt_or_eq with hlt | hlt
          · exact QuantumZipper.RS.exists_isForwardSol_of_lt hU ht.1 (by rw [hU0]; exact hy₀) hlt hu
          · exact ⟨u, hlt ▸ hu⟩
        obtain ⟨δ, hδ, hδv⟩ := exists_two_mul_le_norm_of_isForwardSol ht.1 hv
        have htip := htrace.tendsto_fwdMapInv_tip hU hU0 ht.1 htT
        have hcl := YuanCorollary13.mem_closure_fwdHull_of_tendsto hU hU0 ht0 htip
        rw [heq] at hcl
        have hρ : 0 < δ / Real.exp (2 / δ ^ 2 * t) := div_pos hδ (Real.exp_pos _)
        obtain ⟨z, hzK, hzb⟩ := Metric.mem_closure_iff.1 hcl _ hρ
        have hzb' : ‖z - (b : ℂ)‖ < δ / Real.exp (2 / δ ^ 2 * t) := by
          rw [← dist_eq_norm, dist_comm]; exact hzb
        exact not_mem_fwdHull_of_isForwardSol hU hv hδ hδv hzK.1
          ((lt_div_iff₀ (Real.exp_pos _)).1 hzb') hzK
      · rw [← ht0, hγ0] at heq
        have := congrArg Complex.re heq
        simp only [Complex.zero_re, Complex.ofReal_re] at this
        linarith
    · have h' : γ T ∈ H := hγT
      rw [← htT, heq] at h'
      have : (0 : ℝ) < (b : ℂ).im := h'
      simp at this
  -- Step 2: a positive distance between the trace and the ray
  set F : Set ℂ := {z | z.im = 0 ∧ y₀ ≤ z.re} with hFdef
  have hFc : IsClosed F :=
    (isClosed_eq Complex.continuous_im continuous_const).inter
      (isClosed_le continuous_const Complex.continuous_re)
  have hFne : F.Nonempty := ⟨(y₀ : ℂ), by rw [hFdef]; exact ⟨by simp, by simp⟩⟩
  have hnotF : ∀ t ∈ Icc (0 : ℝ) T, γ t ∉ F := fun t ht hF =>
    hstep1 t ht (γ t).re hF.2 (Complex.ext (by simp) (by simp [hF.1]))
  obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hT.le)
    ((continuous_infDist_pt F).comp_continuousOn hγc)
  set d := infDist (γ t₀) F with hd
  have hdpos : 0 < d := (hFc.notMem_iff_infDist_pos hFne).1 (hnotF t₀ ht₀)
  have hdist : ∀ t ∈ Icc (0 : ℝ) T, ∀ b : ℝ, y₀ ≤ b → d ≤ dist (γ t) b := fun t ht b hb =>
    (hmin ht).trans (infDist_le_dist_of_mem (show (b : ℂ) ∈ F from ⟨by simp, by simpa using hb⟩))
  -- Step 3: the `d/2`-neighbourhood of the ray avoids every hull
  have hray : ∀ r ∈ Ico (0 : ℝ) T, ∀ y : ℝ, y₀ ≤ y →
      Disjoint (ball (y : ℂ) (d / 2)) (fwdHull U r) := by
    intro r hr y hy
    rw [Set.disjoint_left]
    intro z hzb hzK
    rw [hfillH r hr] at hzK
    have hAc : closure (γ '' Icc 0 r) = γ '' Icc 0 r :=
      (hcpt r (Ico_subset_Icc_self hr)).isClosed.closure_eq
    set C : Set ℂ := (ball (y : ℂ) (d / 2) ∩ H) ∪ {w | y ≤ w.re ∧ 0 < w.im ∧ w.im < d / 2}
      with hC
    have hzC : z ∈ C := Or.inl ⟨hzb, hzK.1⟩
    have hp1 : (⟨y, d / 4⟩ : ℂ) ∈ ball (y : ℂ) (d / 2) ∩ H := by
      refine ⟨?_, show (0 : ℝ) < d / 4 by positivity⟩
      rw [mem_ball, dist_eq_norm]
      refine norm_lt_of_abs_re_add_abs_im_lt ?_
      simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_self,
        abs_zero, sub_zero, zero_add]
      rw [abs_of_pos (by positivity)]
      linarith
    have hp2 : (⟨y, d / 4⟩ : ℂ) ∈ {w : ℂ | y ≤ w.re ∧ 0 < w.im ∧ w.im < d / 2} :=
      ⟨le_rfl, show (0 : ℝ) < d / 4 by positivity, show d / 4 < d / 2 by linarith⟩
    have hCpre : IsPreconnected C :=
      IsPreconnected.union _ hp1 hp2
        ((convex_ball _ _).inter (convex_halfSpace_im_gt 0)).isPreconnected
        ((convex_halfSpace_re_ge y).inter ((convex_halfSpace_im_gt 0).inter
          (convex_halfSpace_im_lt (d / 2)))).isPreconnected
    have hCsub : C ⊆ H \ closure (γ '' Icc 0 r) := by
      intro w hw
      have hwH : w ∈ H := by
        rcases hw with hw | hw
        · exact hw.2
        · exact hw.2.1
      refine ⟨hwH, ?_⟩
      rw [hAc]
      rintro ⟨t, ht, rfl⟩
      have htT : t ∈ Icc (0 : ℝ) T := ⟨ht.1, ht.2.trans hr.2.le⟩
      rcases hw with hw | hw
      · have := hdist t htT y hy
        have hw1 := hw.1
        rw [mem_ball] at hw1
        linarith
      · have := hdist t htT (γ t).re (hy.trans hw.1)
        have hle : dist (γ t) ((γ t).re : ℂ) < d / 2 := by
          rw [dist_eq_norm]
          refine norm_lt_of_abs_re_add_abs_im_lt ?_
          simp only [Complex.sub_re, Complex.ofReal_re, sub_self, abs_zero, Complex.sub_im,
            Complex.ofReal_im, sub_zero, zero_add]
          rw [abs_of_pos hw.2.1]
          exact hw.2.2
        linarith
    have hCunb : ¬ Bornology.IsBounded C := by
      intro hb
      obtain ⟨R, hR⟩ := (isBounded_iff_forall_norm_le).1 hb
      have hw : (⟨max y (R + 1), d / 4⟩ : ℂ) ∈ C :=
        Or.inr ⟨le_max_left _ _, show (0 : ℝ) < d / 4 by positivity,
          show d / 4 < d / 2 by linarith⟩
      have h1 := hR _ hw
      have h2 := Complex.abs_re_le_norm (⟨max y (R + 1), d / 4⟩ : ℂ)
      have h3 : R + 1 ≤ |(⟨max y (R + 1), d / 4⟩ : ℂ).re| :=
        (le_max_right _ _).trans (le_abs_self _)
      linarith
    rcases hzK.2 with hzA | hbdd
    · exact (hCsub hzC).2 hzA
    · exact hCunb (hbdd.subset (hCpre.subset_connectedComponentIn hzC hCsub))
  -- Step 4: the ray lemma
  exact not_tendsto_fwdMap_of_disjoint_ray hU hU0 hT hy₀ (half_pos hdpos) hray halive hlim

end FiniteEndpoint

end InteractingSLE
