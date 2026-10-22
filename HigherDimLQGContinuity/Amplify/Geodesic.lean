import HigherDimLQGContinuity.Witness.Basic
import HigherDimLQGMetric.Select.GeodRel
import Mathlib.Topology.Order.IntermediateValue

/-!
# Geodesics parametrized by length, crossings, and confinement by the escape event (packet P7)

Deterministic helpers for Lemma 3.2 and Proposition 3.3 (blueprint Part A, `a:lem32`, `a:prop33`):

* `p7_geodPath`: the length parametrization `u ↦ γ(u/ℓ)` of a constant-speed geodesic
  `γ : [0, 1] → ℝ^d` from `x` to `y` (`IsConstSpeedGeod`, clause (E6) of Lemma 2.1), with
  `G(P u, P v) = |u - v|` on `[0, ℓ]`, `ℓ = G(x, y)` (`p7_geodPath_spec`).
* `p7_len_le_of_isometry`: a path along which `G` grows at most linearly has `G`-length at most `b - a`.
* `p7_setDistIn_le_len`: a path from inside `B̄_{r₁}(z)` to outside `B_{r₂}(z)` pays the global set distance
  between the two spheres.
* `p7_geod_confined`: on the escape event of (E5) with `K = 1` at radius `R'`, every length-parametrized geodesic
  with endpoints in `B_{R'}` stays in `B_{S R'}` (the remark after `a:def-uniform`).
* `p7_internal_le_diamIn`, `p7_le_of_ofReal_le`: small `ℝ≥0∞` bridges.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGContinuity

open Set Metric
open HigherDimLFPP (Rd)
open HigherDimLQGMetric
open scoped ENNReal

variable {d : ℕ}

/-! ## Small bridges -/

/-- The internal distance of two points of `A` is at most the internal diameter of `A`. -/
theorem p7_internal_le_diamIn (G : ContMetric d) {V A : Set (Rd d)} {x y : Rd d} (hx : x ∈ A)
    (hy : y ∈ A) : G.internal V x y ≤ diamIn G V A :=
  le_iSup₂_of_le x hx (le_iSup₂_of_le y hy le_rfl)

/-- The global distance of two points of `A` is at most the internal diameter of `A`. -/
theorem p7_ofReal_le_diamIn (G : ContMetric d) {V A : Set (Rd d)} {x y : Rd d} (hx : x ∈ A)
    (hy : y ∈ A) : ENNReal.ofReal (G.1 (x, y)) ≤ diamIn G V A :=
  (G.ofReal_le_internal V x y).trans (p7_internal_le_diamIn G hx hy)

/-- `ofReal a ≤ ofReal b` with `0 ≤ b` gives `a ≤ b`. -/
theorem p7_le_of_ofReal_le {a b : ℝ} (hb : 0 ≤ b) (h : ENNReal.ofReal a ≤ ENNReal.ofReal b) :
    a ≤ b :=
  (ENNReal.ofReal_le_ofReal_iff hb).mp h

/-- A distance bounded through a diameter bound. -/
theorem p7_apply_le_of_diamIn_le (G : ContMetric d) {V A : Set (Rd d)} {x y : Rd d} (hx : x ∈ A)
    (hy : y ∈ A) {c : ℝ} (hc : 0 ≤ c) (h : diamIn G V A ≤ ENNReal.ofReal c) : G.1 (x, y) ≤ c :=
  p7_le_of_ofReal_le hc ((p7_ofReal_le_diamIn G hx hy).trans h)

/-! ## Length parametrization of a constant-speed geodesic -/

/-- The length parametrization `u ↦ γ(u / G(x, y))` of a path `γ : [0, 1] → ℝ^d`. -/
def p7_geodPath (G : ContMetric d) (x y : Rd d) (γ : C(unitInterval, Rd d)) : ℝ → Rd d :=
  fun u => witExt γ (u / G.1 (x, y))

theorem p7_continuous_geodPath (G : ContMetric d) (x y : Rd d) (γ : C(unitInterval, Rd d)) :
    Continuous (p7_geodPath G x y γ) :=
  (continuous_witExt γ).comp (continuous_id.div_const _)

/-- The length parametrization of a constant-speed geodesic is an isometric embedding of
`[0, G(x, y)]`, from `x` to `y`. -/
theorem p7_geodPath_spec (G : ContMetric d) {x y : Rd d} {γ : C(unitInterval, Rd d)}
    (hγ : IsConstSpeedGeod G x y γ) :
    p7_geodPath G x y γ 0 = x ∧ p7_geodPath G x y γ (G.1 (x, y)) = y ∧
      ∀ u ∈ Icc (0 : ℝ) (G.1 (x, y)), ∀ v ∈ Icc (0 : ℝ) (G.1 (x, y)),
        G.1 (p7_geodPath G x y γ u, p7_geodPath G x y γ v) = |u - v| := by
  obtain ⟨h0, h1, hspeed⟩ := hγ
  set ℓ := G.1 (x, y) with hℓ
  have hℓ0 : 0 ≤ ℓ := G.nonneg x y
  have hP0 : p7_geodPath G x y γ 0 = x := by
    simp only [p7_geodPath, zero_div, witExt_zero, h0]
  refine ⟨hP0, ?_, ?_⟩
  · rcases hℓ0.eq_or_lt with hzero | hpos
    · have hxy : x = y := G.eq_of_apply_eq_zero hzero.symm
      rw [← hzero, hP0, hxy]
    · simp only [p7_geodPath, ← hℓ, div_self hpos.ne', witExt_one, h1]
  · intro u hu v hv
    rcases hℓ0.eq_or_lt with hzero | hpos
    · have hu0 : u = 0 := le_antisymm (hzero ▸ hu.2) hu.1
      have hv0 : v = 0 := le_antisymm (hzero ▸ hv.2) hv.1
      subst hu0; subst hv0
      simp only [sub_self, abs_zero, G.apply_self]
    · have hu' : u / ℓ ∈ Icc (0 : ℝ) 1 :=
        ⟨div_nonneg hu.1 hpos.le, (div_le_one hpos).mpr hu.2⟩
      have hv' : v / ℓ ∈ Icc (0 : ℝ) 1 :=
        ⟨div_nonneg hv.1 hpos.le, (div_le_one hpos).mpr hv.2⟩
      simp only [p7_geodPath]
      rw [witExt_of_mem γ hu', witExt_of_mem γ hv', hspeed]
      rw [← sub_div, abs_div, abs_of_pos hpos, div_mul_cancel₀ _ hpos.ne']

/-! ## Lengths -/

/-- A path along which `G` is at most the parameter difference has length at most `b - a`. -/
theorem p7_len_le_of_isometry (G : ContMetric d) {P : ℝ → Rd d} {a b : ℝ}
    (hP : ∀ u ∈ Icc a b, ∀ v ∈ Icc a b, G.1 (P u, P v) ≤ |u - v|) :
    G.len P a b ≤ ENNReal.ofReal (b - a) := by
  have hlip : LipschitzOnWith 1 (G.pt ∘ P) (Icc a b) := by
    refine LipschitzOnWith.of_dist_le_mul fun u hu v hv => ?_
    change G.1 (P u, P v) ≤ _
    simpa only [NNReal.coe_one, one_mul, Real.dist_eq] using hP u hu v hv
  have hvar := hlip.comp_eVariationOn_le (g := id) (s := Icc a b) (fun t ht => ht)
  have hid : eVariationOn (id : ℝ → ℝ) (Icc a b) = ENNReal.ofReal (b - a) := by
    have h := (monotone_id (α := ℝ)).monotoneOn (univ : Set ℝ) |>.eVariationOn_eq
      (a := a) (b := b) (mem_univ _) (mem_univ _)
    simpa only [univ_inter, id_eq] using h
  rw [ContMetric.len_def, LQGMetric.MetricGeometry.curveLength]
  calc eVariationOn (G.pt ∘ P) (Icc a b) = eVariationOn ((G.pt ∘ P) ∘ id) (Icc a b) := rfl
    _ ≤ (1 : NNReal) * eVariationOn id (Icc a b) := hvar
    _ = ENNReal.ofReal (b - a) := by rw [hid, ENNReal.coe_one, one_mul]

/-! ## Crossings -/

/-- A path from inside the closed ball `B̄_{r₁}(z)` to outside the open ball `B_{r₂}(z)` (`r₁ ≤ r₂`) pays the global
set distance between the two spheres. -/
theorem p7_setDistIn_le_len (G : ContMetric d) {P : ℝ → Rd d} {a b : ℝ} (hab : a ≤ b)
    (hP : ContinuousOn P (Icc a b)) (z : Rd d) {r₁ r₂ : ℝ} (hr : r₁ ≤ r₂)
    (ha : ‖P a - z‖ ≤ r₁) (hb : r₂ ≤ ‖P b - z‖) :
    setDistIn G univ (sphere z r₁) (sphere z r₂) ≤ G.len P a b := by
  have hf : ContinuousOn (fun u => ‖P u - z‖) (Icc a b) :=
    (hP.sub continuousOn_const).norm
  obtain ⟨u, hu, hur⟩ := intermediate_value_Icc hab hf ⟨ha, hr.trans hb⟩
  have hfu : ContinuousOn (fun t => ‖P t - z‖) (Icc u b) := hf.mono (Icc_subset_Icc hu.1 le_rfl)
  obtain ⟨v, hv, hvr⟩ := intermediate_value_Icc hu.2 hfu
    ⟨(show ‖P u - z‖ ≤ r₂ by simp only at hur; rw [hur]; exact hr), hb⟩
  have huS : P u ∈ sphere z r₁ := by rw [mem_sphere, dist_eq_norm]; exact hur
  have hvS : P v ∈ sphere z r₂ := by rw [mem_sphere, dist_eq_norm]; exact hvr
  calc setDistIn G univ (sphere z r₁) (sphere z r₂) ≤ G.internal univ (P u) (P v) :=
        iInf₂_le_of_le (P u) huS (iInf₂_le_of_le (P v) hvS le_rfl)
    _ ≤ G.len P u v := G.internal_le_len hv.1 (hP.mono (Icc_subset_Icc hu.1 hv.2))
        (fun _ _ => mem_univ _)
    _ ≤ G.len P a b := G.len_mono P hu.1 hv.2

/-! ## Confinement by the escape event -/

/-- **Confinement** (remark after `a:def-uniform`): on the escape event
`diam_{B_{2R'}}(B_{R'}) < dist(∂B_{2R'}, ∂B_{SR'})` (with `S ≥ 2`), a length-parametrized `G`-geodesic
`P : [0, ℓ] → ℝ^d` (`G(P u, P v) = |u - v|`) with both endpoints in `B_{R'}` stays in the open ball `B_{SR'}`. -/
theorem p7_geod_confined (G : ContMetric d) {P : ℝ → Rd d} {ℓ R' S : ℝ} (hℓ : 0 ≤ ℓ)
    (hPc : Continuous P) (hS : 2 ≤ S) (hR' : 0 < R')
    (hgeo : ∀ u ∈ Icc (0 : ℝ) ℓ, ∀ v ∈ Icc (0 : ℝ) ℓ, G.1 (P u, P v) = |u - v|)
    (h0 : P 0 ∈ ball (0 : Rd d) R') (hℓmem : P ℓ ∈ ball (0 : Rd d) R')
    (hesc : diamIn G (ball (0 : Rd d) (2 * R')) (ball (0 : Rd d) R') <
      setDistIn G univ (sphere (0 : Rd d) (2 * R')) (sphere (0 : Rd d) (S * R'))) :
    ∀ u ∈ Icc (0 : ℝ) ℓ, ‖P u‖ < S * R' := by
  intro u hu
  by_contra hcon
  rw [not_lt] at hcon
  have h0n : ‖P 0 - 0‖ ≤ 2 * R' := by
    rw [sub_zero]
    have := mem_ball_zero_iff.mp h0
    linarith
  have hun : S * R' ≤ ‖P u - 0‖ := by rw [sub_zero]; exact hcon
  have hr : 2 * R' ≤ S * R' := by nlinarith
  have hcross := p7_setDistIn_le_len G hu.1 hPc.continuousOn 0 hr h0n hun
  have hlen : G.len P 0 u ≤ G.len P 0 ℓ := G.len_mono P le_rfl hu.2
  have hlenℓ : G.len P 0 ℓ ≤ ENNReal.ofReal (ℓ - 0) :=
    p7_len_le_of_isometry G fun a ha b hb => (hgeo a ha b hb).le
  have hℓeq : G.1 (P 0, P ℓ) = ℓ := by
    rw [hgeo 0 ⟨le_rfl, hℓ⟩ ℓ ⟨hℓ, le_rfl⟩, zero_sub, abs_neg, abs_of_nonneg hℓ]
  have hdiam : ENNReal.ofReal ℓ ≤ diamIn G (ball (0 : Rd d) (2 * R')) (ball (0 : Rd d) R') := by
    rw [← hℓeq]
    exact p7_ofReal_le_diamIn G h0 hℓmem
  have : setDistIn G univ (sphere (0 : Rd d) (2 * R')) (sphere (0 : Rd d) (S * R')) ≤
      diamIn G (ball (0 : Rd d) (2 * R')) (ball (0 : Rd d) R') := by
    calc _ ≤ G.len P 0 u := hcross
      _ ≤ G.len P 0 ℓ := hlen
      _ ≤ ENNReal.ofReal (ℓ - 0) := hlenℓ
      _ = ENNReal.ofReal ℓ := by rw [sub_zero]
      _ ≤ _ := hdiam
  exact absurd hesc (not_lt.mpr this)

end HigherDimLQGContinuity
