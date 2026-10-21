import SmallGammaGeodesics.CC.Telescope
import LQGMetric.Papers.GM.S3.AttainedP36Conf

/-!
# [3] Prop 3.6, the improvement step: the pathwise part (track CC, packet CC10)

[3] = Gwynne–Miller, *Conformal covariance of the Liouville quantum gravity metric for
γ ∈ (0, 2)*, arXiv:1905.00384v2, proof of Proposition 3.6, Steps 2–6. Plan:
`planning/audits/CC0-conformal-covariance-plan.md`, Details (a) **D15**, and the consumption
recipe in `planning/handoffs/CC8a.md`, §5.

Everything here is deterministic: one realization `D₀ = D_h(ω)` of the metric and one function
`d′ = D^ϕ(ω)` with the triangle inequality. The probabilistic assembly is in `CC/Improve.lean`.

* `exists_contMetric_modulus`: a uniform modulus of continuity of `D₀` on a compact set (the
  `ω_ε → 0` of [3] (3.24), CC8a §4.8).
* `exists_geod_confine`: **confinement** ([3] (3.16), CC0 D13.1 without probability). For a compact
  `K` and `0 ≤ a < b` there is `ρ > 0` such that every `D₀`-geodesic between points of the closed
  `a`-thickening of `K` at Euclidean distance `≤ ρ` stays in the closed `b`-thickening. It holds
  for every continuous metric and every geodesic, so in the random setting it holds surely.
* `le_ofReal_of_forall_pos_add`: `d ≤ ofReal (a + c η)` for every `η > 0` gives `d ≤ ofReal a`.
* `le_on_open_of_le_ratPt`: an inequality between two functions continuous on `T ⊆ ℂ × ℂ` that holds
  at the rational pairs of an open `O ⊆ T` holds on `O` ([3] and GM l. 1497–1499).
* `local_improve_det`: **the pathwise improvement on one compact set**. From the current bound
  `d′ ≤ C·D₀(·,·;V)`, geodesics for all pairs, unique geodesics between rational points, good
  balls with the D-forms of conditions 1 and 3, and coverings of the closed `κ/2`-thickening of
  `K` by good balls of radii in `[ε_n², ε_n]` for all large `n` (`ε_n → 0`), it gives `ρ > 0` with
  `d′(x,y) ≤ C_δ·D₀(x,y)` for `x, y ∈ K`, `‖x − y‖ ≤ ρ`, where `C_δ = 1 + δ + A/(A+1)(C − 1 − δ)`.
  The pair estimate is CC8a's `p36_pair_ext_improve` with `S` the closed `κ/2`-thickening.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Topology Set Metric
open scoped ENNReal

namespace SmallGammaGeodesics.CC

open LQGMetric LQGMetric.Blueprint

section Det

variable (D₀ : ContMetric)

/-- **A uniform modulus of continuity** of a continuous metric on a compact set: Euclidean-close
points of `S` are `D₀`-close. -/
theorem exists_contMetric_modulus {S : Set ℂ} (hS : IsCompact S) {η : ℝ} (hη : 0 < η) :
    ∃ e : ℝ, 0 < e ∧ ∀ x ∈ S, ∀ y ∈ S, ‖x - y‖ ≤ e → D₀.1 (x, y) ≤ η := by
  obtain ⟨e, he, H⟩ := Metric.uniformContinuousOn_iff.1
    (hS.uniformContinuousOn_of_continuous D₀.continuous_pt.continuousOn) η hη
  refine ⟨e / 2, half_pos he, fun x hx y hy hxy => ?_⟩
  have h1 : dist (D₀.pt x) (D₀.pt y) < η := H x hx y hy (by rw [dist_eq_norm]; linarith)
  exact h1.le

/-- **Confinement of short geodesics** ([3] (3.16); CC0 D13.1 without probability). For a compact
`K` and `0 ≤ a < b` there is `ρ > 0` such that every `D₀`-geodesic between points of the closed
`a`-thickening of `K` at Euclidean distance `≤ ρ` stays in the closed `b`-thickening of `K`.

Proof: `D₀.unpt` is uniformly continuous on the compact `D₀.pt '' cthickening b K`, and `D₀.pt` on
`cthickening b K`. If a geodesic `η` from `z` to `w` left `cthickening b K`, the intermediate value
theorem for `τ ↦ infEDist (η τ) K` would give a point `u = η τ` with `infEDist u K = b`; then
`D₀(z, u) = τ D₀(z, w) ≤ D₀(z, w)` is small, so `‖z − u‖ < b − a`, against
`b ≤ infEDist z K + ‖u − z‖ ≤ a + ‖u − z‖`. -/
theorem exists_geod_confine {K : Set ℂ} (hK : IsCompact K) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ z ∈ cthickening a K, ∀ w ∈ cthickening a K, ‖z - w‖ ≤ ρ →
      ∀ η, IsGeod01 D₀ z w η → range η ⊆ cthickening b K := by
  have hK₁ : IsCompact (cthickening b K) := hK.cthickening
  obtain ⟨δ, hδ, Hδ⟩ := Metric.uniformContinuousOn_iff.1
    ((hK₁.image D₀.continuous_pt).uniformContinuousOn_of_continuous
      D₀.continuous_unpt.continuousOn) (b - a) (by linarith)
  obtain ⟨ρ, hρ, Hρ⟩ := Metric.uniformContinuousOn_iff.1
    (hK₁.uniformContinuousOn_of_continuous D₀.continuous_pt.continuousOn) δ hδ
  refine ⟨ρ / 2, half_pos hρ, fun z hz w hw hzw η hη => ?_⟩
  have hsub : cthickening a K ⊆ cthickening b K := cthickening_mono hab.le K
  have hDzw : dist (D₀.pt z) (D₀.pt w) < δ :=
    Hρ z (hsub hz) w (hsub hw) (by rw [dist_eq_norm]; linarith)
  rintro _ ⟨t, rfl⟩
  by_contra hnt
  have hcont : Continuous fun τ : unitInterval => infEDist (η τ) K :=
    continuous_infEDist.comp η.continuous
  have h0 : infEDist (η 0) K ≤ ENNReal.ofReal b := by
    rw [hη.1]
    exact (mem_cthickening_iff.1 hz).trans (ENNReal.ofReal_le_ofReal hab.le)
  have h1 : ENNReal.ofReal b ≤ infEDist (η t) K := by
    rw [mem_cthickening_iff, not_le] at hnt
    exact hnt.le
  obtain ⟨τ, hτ⟩ := intermediate_value_univ 0 t hcont ⟨h0, h1⟩
  have hτ' : infEDist (η τ) K = ENNReal.ofReal b := hτ
  have huK₁ : η τ ∈ cthickening b K := mem_cthickening_iff.2 hτ'.le
  -- `D₀(z, η τ) = τ D₀(z, w) ≤ D₀(z, w) < δ`
  have hDzu : dist (D₀.pt z) (D₀.pt (η τ)) < δ := by
    have e := hη.2.2 0 τ
    rw [hη.1, Set.Icc.coe_zero, sub_zero, abs_of_nonneg τ.2.1] at e
    have hD0 : 0 ≤ D₀.1 (z, w) := D₀.nonneg z w
    have hle : D₀.1 (z, η τ) ≤ D₀.1 (z, w) := by
      rw [e]
      exact mul_le_of_le_one_left hD0 τ.2.2
    exact lt_of_le_of_lt hle hDzw
  have hzu : dist z (η τ) < b - a :=
    Hδ (D₀.pt z) ⟨z, hsub hz, rfl⟩ (D₀.pt (η τ)) ⟨η τ, huK₁, rfl⟩ hDzu
  -- but `b ≤ a + ‖η τ − z‖`
  have htri : infEDist (η τ) K ≤ infEDist z K + edist (η τ) z :=
    infEDist_le_infEDist_add_edist
  rw [hτ', edist_dist] at htri
  have h2 : ENNReal.ofReal b ≤ ENNReal.ofReal (a + dist (η τ) z) := by
    rw [ENNReal.ofReal_add ha dist_nonneg]
    exact htri.trans (add_le_add (mem_cthickening_iff.1 hz) le_rfl)
  rw [ENNReal.ofReal_le_ofReal_iff (add_nonneg ha dist_nonneg)] at h2
  rw [dist_comm] at hzu
  linarith

end Det

/-- `d ≤ ofReal (a + c η)` for every `η > 0` (with `c ≥ 0`) gives `d ≤ ofReal a`. -/
theorem le_ofReal_of_forall_pos_add {d : ℝ≥0∞} {a c : ℝ} (hc : 0 ≤ c)
    (h : ∀ η : ℝ, 0 < η → d ≤ ENNReal.ofReal (a + c * η)) : d ≤ ENNReal.ofReal a := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hε' : (0 : ℝ) < ε := NNReal.coe_pos.2 hε
  have hη : (0 : ℝ) < ε / (c + 1) := div_pos hε' (by linarith)
  refine (h _ hη).trans (ENNReal.ofReal_add_le.trans (add_le_add le_rfl ?_))
  rw [← ENNReal.ofReal_coe_nnreal]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [mul_div_assoc', div_le_iff₀ (by linarith)]
  nlinarith

/-- **From rational pairs to all pairs**: if two functions are continuous on `T ⊆ ℂ × ℂ` and
`f ≤ g` holds at the rational pairs of an open `O ⊆ T`, then `f ≤ g` on `O` ([3], end of the proof
of Prop 3.6; GM l. 1497–1499, `LQGMetric.GM.p36_ratio_le`). -/
theorem le_on_open_of_le_ratPt {f g : ℂ × ℂ → ℝ≥0∞} {T O : Set (ℂ × ℂ)} (hO : IsOpen O)
    (hOT : O ⊆ T) (hf : ContinuousOn f T) (hg : ContinuousOn g T)
    (hrat : ∀ a b : ℚ × ℚ, (ratPt a, ratPt b) ∈ O → f (ratPt a, ratPt b) ≤ g (ratPt a, ratPt b)) :
    ∀ q ∈ O, f q ≤ g q := by
  have hd : DenseRange (Prod.map ratPt ratPt) := GM.denseRange_ratPt.prodMap GM.denseRange_ratPt
  intro q hq
  have hcl : q ∈ closure (O ∩ range (Prod.map ratPt ratPt)) := hd.open_subset_closure_inter hO hq
  refine ContinuousWithinAt.closure_le hcl ((hf q (hOT hq)).mono (inter_subset_left.trans hOT))
    ((hg q (hOT hq)).mono (inter_subset_left.trans hOT)) ?_
  rintro _ ⟨hqO, ⟨a, b⟩, rfl⟩
  exact hrat a b hqO

section Local

variable (D₀ : ContMetric)

/-- **The pathwise improvement step on one compact set** ([3] Prop 3.6, Steps 2–6 with the current
bound `C` in place of `C_*`; CC0 D15). Let `κ > 0` with `cthickening κ K ⊆ V`, and suppose that
for all large `n` the closed `κ/2`-thickening of `K` is covered by balls `B(v, r/2)` with
`Good v r` and `r ∈ [ε_n², ε_n]`, where `ε_n → 0`. Then close points `x, y ∈ K` satisfy
`d′(x,y) ≤ (1 + δ + A/(A+1)(C − 1 − δ))·D₀(x,y)`.

Proof: confinement (`exists_geod_confine` from the `κ/4`- to the `κ/2`-thickening) gives `ρ`. For
rational `z ≠ w` in the `κ/4`-thickening with `‖z − w‖ ≤ ρ`, every `η > 0` and every large `n`,
CC8a's `p36_pair_ext_improve` (with `S` the `κ/2`-thickening, `e = ε_n`, `r_min = ε_n²` and the
modulus `ω = η`) gives `d′(z,w) ≤ C_δ D₀(z,w) + 3Cη`; let `η → 0`. Continuity of `d′` on `V × V`
and of `D₀` extends the bound to all pairs of `K` at distance `≤ ρ/2`. -/
theorem local_improve_det {d' : ℂ → ℂ → ℝ≥0∞} (htri : ∀ x y z, d' x z ≤ d' x y + d' y z)
    {V : Set ℂ} (hself : ∀ z ∈ V, d' z z = 0)
    (hcont : ContinuousOn (fun q : ℂ × ℂ => d' q.1 q.2) (V ×ˢ V))
    (hex : ∀ a b : ℂ, ∃ η, D₀.IsGeod01 a b η)
    (hun : ∀ a b : ℚ × ℚ, UniqueGeod D₀ (ratPt a) (ratPt b))
    {α A δ C : ℝ} (hα : 1 / 2 < α) (hα1 : α < 1) (hA : 0 ≤ A) (hδ : 0 ≤ δ) (hC : 1 + δ ≤ C)
    (hratio : ∀ x ∈ V, ∀ y ∈ V, d' x y ≤ ENNReal.ofReal C * D₀.internal V x y)
    {K : Set ℂ} (hK : IsCompact K) {κ : ℝ} (hκ : 0 < κ) (hKV : cthickening κ K ⊆ V)
    (Good : ℂ → ℝ → Prop)
    (hgood1 : ∀ v r, Good v r → ∀ u ∈ sphere v (α * r), ∀ u' ∈ sphere v r,
      GM.UniqueGeodIn D₀ u u' (closure (annulus v (α * r) r : Set ℂ)) →
        d' u u' ≤ ENNReal.ofReal ((1 + δ) * D₀.1 (u, u')))
    (hgood3 : ∀ v r, Good v r → ∃ (a' b' : ℝ) (G : ℝ → ℂ),
      Disconnects (G '' Icc a' b') (sphere v (α * r)) (sphere v r) ∧
      D₀.len G a' b' ≤ ENNReal.ofReal A * setDist D₀ (sphere v (α * r)) (sphere v r))
    {ε : ℕ → ℝ} (hε0 : ∀ n, 0 < ε n) (hεlim : Tendsto ε atTop (𝓝 0))
    (hcov : ∀ᶠ n in atTop, ∀ x ∈ cthickening (κ / 2) K, ∃ v r,
      (ε n ^ 2 ≤ r ∧ r ≤ ε n ∧ Good v r) ∧ x ∈ ball v (r / 2)) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ x ∈ K, ∀ y ∈ K, ‖x - y‖ ≤ ρ →
      d' x y ≤ ENNReal.ofReal ((1 + δ + A / (A + 1) * (C - 1 - δ)) * D₀.1 (x, y)) := by
  set Cδ := 1 + δ + A / (A + 1) * (C - 1 - δ) with hCδ
  have hK₁V : cthickening (κ / 2) K ⊆ V := (cthickening_mono (by linarith) K).trans hKV
  have hK'V : cthickening (κ / 4) K ⊆ V := (cthickening_mono (by linarith) K).trans hKV
  have hK₁c : IsCompact (cthickening (κ / 2) K) := hK.cthickening
  obtain ⟨ρ, hρ, hconf⟩ := exists_geod_confine D₀ hK (a := κ / 4) (b := κ / 2) (by linarith)
    (by linarith)
  -- rational pairs (more generally, pairs with a unique geodesic)
  have hpair : ∀ z ∈ cthickening (κ / 4) K, ∀ w ∈ cthickening (κ / 4) K, ‖z - w‖ ≤ ρ →
      UniqueGeod D₀ z w → d' z w ≤ ENNReal.ofReal (Cδ * D₀.1 (z, w)) := by
    intro z hz w hw hzw hu
    rcases eq_or_ne z w with rfl | hne
    · rw [hself z (hK'V hz)]
      exact zero_le
    have hzw0 : 0 < ‖z - w‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
    refine le_ofReal_of_forall_pos_add (c := 3 * C) (by linarith) fun η hη => ?_
    obtain ⟨e₀, he₀, hmod⟩ := exists_contMetric_modulus D₀ hK₁c hη
    have h4 : Tendsto (fun n => 4 * ε n) atTop (𝓝 0) := by
      simpa only [mul_zero] using hεlim.const_mul 4
    have hev : ∀ᶠ n in atTop, 4 * ε n < min e₀ ‖z - w‖ :=
      h4.eventually (gt_mem_nhds (lt_min he₀ hzw0))
    obtain ⟨n, hn1, hn2⟩ := (hcov.and hev).exists
    exact p36_pair_ext_improve D₀ htri hex hα hα1 hA hδ hC hratio hu hK₁V (pow_pos (hε0 n) 2)
      (lt_of_lt_of_le hn2 (min_le_right _ _)) (hconf z hz w hw hzw) Good hgood1 hgood3 hn1
      (fun x hx y hy hxy => hmod x hx y hy
        (hxy.trans (lt_of_lt_of_le hn2 (min_le_left _ _)).le))
  -- all pairs, by continuity
  refine ⟨ρ / 2, half_pos hρ, fun x hx y hy hxy => ?_⟩
  set O : Set (ℂ × ℂ) := {q | q.1 ∈ thickening (κ / 4) K ∧ q.2 ∈ thickening (κ / 4) K ∧
    ‖q.1 - q.2‖ < ρ} with hOdef
  have hO : IsOpen O :=
    (isOpen_thickening.preimage continuous_fst).inter ((isOpen_thickening.preimage
      continuous_snd).inter (isOpen_lt (continuous_fst.sub continuous_snd).norm continuous_const))
  have hOV : O ⊆ V ×ˢ V := fun q hq =>
    ⟨hK'V (thickening_subset_cthickening _ _ hq.1),
      hK'V (thickening_subset_cthickening _ _ hq.2.1)⟩
  have hg : ContinuousOn (fun q : ℂ × ℂ => ENNReal.ofReal (Cδ * D₀.1 q)) (V ×ˢ V) :=
    (ENNReal.continuous_ofReal.comp (continuous_const.mul D₀.1.continuous)).continuousOn
  have key := le_on_open_of_le_ratPt hO hOV hcont hg fun a b hab =>
    hpair _ (thickening_subset_cthickening _ _ hab.1) _
      (thickening_subset_cthickening _ _ hab.2.1) hab.2.2.le (hun a b)
  exact key (x, y) ⟨self_subset_thickening (by linarith) K hx,
    self_subset_thickening (by linarith) K hy, by linarith⟩

end Local

end SmallGammaGeodesics.CC
