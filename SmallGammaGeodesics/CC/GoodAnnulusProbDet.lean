import SmallGammaGeodesics.CC.GoodAnnulusLocal

/-!
# [3] Lemma 3.9, conditions 1 and 2: the deterministic cores (track CC, packet CC9b)

Source: Gwynne–Miller arXiv:1905.00384 ([3]), Lemma 3.9 (proof of conditions 1 and 2), in the
corrected form of `planning/audits/CC0-conformal-covariance-plan.md`, Details (a) **D14** (and
**D10** for [3] Lemma 2.2). The event is CC9a's `confGoodAnnulus` (GM's good-annulus event in
J-form for `J = D_h(·,·;𝔸)` and `J' = D^ϕ(·,·;𝔸)`, `𝔸 = 𝔸_{r/2,2r}(z)`).

The probabilistic inputs enter as the deterministic statements they give on their good events, at
the two scales `r` (normalization `σ = 𝔰_r(z)`) and `3r` (normalization `σ₃ = 𝔰_{3r}(z)`):
* `e1` (GM S2.4a at scale `r`): `D_h(u,y) > sσ` for `u` in the closed ring `{3r/4 ≤ |u−z| ≤ r}`
  and `y` in the collar `{r/2 ≤ |y−z| ≤ 3r/5} ∪ {19r/10 ≤ |y−z| ≤ 2r}` of `∂𝔸`;
* `e2` (GM S2.4c at scale `r`): the internal diameter of that closed ring in `𝔸` is `≤ Sσ`;
* `e3` (GM Lemma 2.11 on the closed annulus, `GM.L2_11c`): paths in `cl 𝔸_{αr,r}(z)` between
  points at `D_h`-distance `≥ (s/2)σ` have `D_h`-length `≥ (S+s)σ`;
* `e6` (`ConfSmallScale` = [3] Prop 2.1 at scale `3r`): `|D^ϕ − D_h| ≤ δ'σ₃` on `B_{3r}(z)`;
* `e7` (GM S2.4a, separated points, at scale `3r`): `D_h(u,v) > tσ₃` for `u, v ∈ B̄_r(z)` with
  `|u − v| ≥ (1−α)r` ([3] Lemma 2.2 in ratio form, CC0 D10);
* `e8`: condition 3 itself.

Contents:
* `gaLongI_of_bounds`: **condition 2** (GM's `mem_gaLong_of` with its global bi-Lipschitz
  hypothesis replaced by the local comparison `e6`, CC0 D14). Either alternative of the hypothesis
  of condition 2 gives `D_h(u,v) ≥ (s/2)σ` (for the `D^ϕ` alternative through CC9a's
  `bdFun_le_confMetric_of_lt` and the collar), and then `e2`, `e3` give the length bound;
* `gaCompareBI_of_bounds`: **condition 1** from condition 2 and `D^ϕ ≤ D_h + δ'σ₃ ≤ (1+δ)D_h` on
  `∂B_{αr}(z) × ∂B_r(z)` (CC9a's `gaCompareBI_of_confMetric_le`);
* `confGoodAnnulus_of_bounds`: the event `E_r(z)` with `C' = 1 + δ`, from `e1`–`e8`, once
  `δ' ≤ st/(4S)` and `δ' ≤ δt`. The two scales are compared through `e2` and `e7` themselves
  (`tσ₃ < D_h(z+r, z−r) ≤ Sσ`), so no Gaussian tail of `h_{3r}(z) − h_r(z)` is needed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Metric Topology
open scoped ENNReal

namespace SmallGammaGeodesics.CC

open LQGMetric LQGMetric.Blueprint

/-! ## 1. Geometry of the rings -/

/-- the closed ring `{a ≤ |w| ≤ b}` -/
def closedRing (a b : ℝ) : Set ℂ := {w | a ≤ ‖w‖ ∧ ‖w‖ ≤ b}

/-- the closed collar `{1/2 ≤ |w| ≤ 3/5} ∪ {19/10 ≤ |w| ≤ 2}` of `∂𝔸_{1/2,2}(0)` -/
def annulusCollar : Set ℂ := closedRing (1 / 2) (3 / 5) ∪ closedRing (19 / 10) 2

lemma isCompact_closedRing (a b : ℝ) : IsCompact (closedRing a b) :=
  (isCompact_closedBall (0 : ℂ) b).of_isClosed_subset
    ((isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const))
    fun w hw => by simpa using hw.2

lemma isCompact_annulusCollar : IsCompact annulusCollar :=
  (isCompact_closedRing _ _).union (isCompact_closedRing _ _)

lemma disjoint_closedRing_annulusCollar : Disjoint (closedRing (3 / 4) 1) annulusCollar := by
  rw [Set.disjoint_left]
  rintro w ⟨h1, h2⟩ (⟨h3, h4⟩ | ⟨h3, h4⟩) <;> linarith

lemma closedRing_subset_annulus : closedRing (3 / 4) 1 ⊆ (annulus (0 : ℂ) (1 / 2) 2 : Set ℂ) :=
  fun w hw => show (1 / 2 : ℝ) < ‖w - 0‖ ∧ ‖w - 0‖ < 2 by
    rw [sub_zero]; exact ⟨by linarith [hw.1], by linarith [hw.2]⟩

lemma isConnected_annulus_half_two : IsConnected (annulus (0 : ℂ) (1 / 2) 2 : Set ℂ) :=
  ⟨⟨1, show (1 / 2 : ℝ) < ‖(1 : ℂ) - 0‖ ∧ ‖(1 : ℂ) - 0‖ < 2 by norm_num⟩,
    GM.Bilip.isPreconnected_annulus_zero (by norm_num)⟩

/-- the image of `𝔸_{1/2,2}(0)` under `w ↦ rw + z` is `𝔸_{r/2,2r}(z)` -/
lemma image_affine_annulus {r : ℝ} (hr : 0 < r) (z : ℂ) :
    (fun w => (r : ℂ) * w + z) '' (annulus (0 : ℂ) (1 / 2) 2 : Set ℂ) =
      (annulus z (r / 2) (2 * r) : Set ℂ) := by
  rw [show ((fun w => (r : ℂ) * w + z) '' (annulus (0 : ℂ) (1 / 2) 2 : Set ℂ)) =
    scaleSet r z (annulus 0 (1 / 2) 2) from rfl, GM.Bilip.scaleSet_annulus hr,
    show r * (1 / 2) = r / 2 by ring, mul_comm r 2]

/-- rescaled membership in a closed ring -/
lemma div_mem_closedRing {r a b : ℝ} (hr : 0 < r) {z u : ℂ} (h1 : a * r ≤ ‖u - z‖)
    (h2 : ‖u - z‖ ≤ b * r) : (u - z) / (r : ℂ) ∈ closedRing a b := by
  refine ⟨?_, ?_⟩ <;> rw [GM.norm_unscale r hr]
  · rwa [le_div_iff₀ hr]
  · rwa [div_le_iff₀ hr]

/-- a bounded set containing a point has a nonempty frontier (in `ℂ`) -/
lemma frontier_nonempty_of_mem {U : Set ℂ} (hUb : Bornology.IsBounded U) {u : ℂ} (hu : u ∈ U) :
    (frontier U).Nonempty := by
  by_contra he
  rw [not_nonempty_iff_eq_empty, ← isClopen_iff_frontier_eq_empty] at he
  rcases isClopen_iff.1 he with h | h
  · rw [h] at hu; exact hu
  · rw [h] at hUb; exact NormedSpace.unbounded_univ ℝ ℂ hUb

/-- the frontier of `𝔸_{r/2,2r}(z)`, rescaled, lies in the collar -/
lemma div_mem_annulusCollar_of_frontier {z y : ℂ} {r : ℝ} (hr : 0 < r)
    (hy : y ∈ frontier (annulus z (r / 2) (2 * r) : Set ℂ)) :
    (y - z) / (r : ℂ) ∈ annulusCollar := by
  rcases GM.frontier_annulus_norm hy with e | e
  · exact Or.inl (div_mem_closedRing hr (by rw [e]; linarith) (by rw [e]; linarith))
  · exact Or.inr (div_mem_closedRing hr (by rw [e]; linarith) (by rw [e]))

/-- points of `𝔸_{r/2,2r}(z)` within `r/10` of its frontier, rescaled, lie in the collar -/
lemma div_mem_annulusCollar_of_nearFrontier {z y : ℂ} {r δ : ℝ} (hr : 0 < r) (hδ : δ ≤ r / 10)
    (hy : y ∈ GM.nearFrontier (annulus z (r / 2) (2 * r) : Set ℂ) δ) :
    (y - z) / (r : ℂ) ∈ annulusCollar := by
  obtain ⟨hyU, hyd⟩ := hy
  have hyn : r / 2 < ‖y - z‖ ∧ ‖y - z‖ < 2 * r := hyU
  obtain ⟨x, hx, hxy⟩ := (Metric.infDist_lt_iff
    (frontier_nonempty_of_mem (GM.isBounded_annulus _ _) hyU)).1 (hyd.trans_le hδ)
  rw [dist_eq_norm] at hxy
  have t1 := norm_sub_le_norm_sub_add_norm_sub y x z
  have t2 := norm_sub_le_norm_sub_add_norm_sub x y z
  rw [norm_sub_rev x y] at t2
  rcases GM.frontier_annulus_norm hx with e | e
  · exact Or.inl (div_mem_closedRing hr (by linarith) (by linarith))
  · exact Or.inr (div_mem_closedRing hr (by linarith) (by linarith))

/-! ## 2. Condition 2 -/

section Cond
variable {D : DistC → ContMetric} {ϕ : ℂ → ℂ} {W V : Set ℂ} {hbar : DistC} {f : C(ℂ, ℝ)}
  {d : ContMetric}

/-- **Condition 2, deterministic core** ([3] Lemma 3.9; CC0 D14). GM's `mem_gaLong_of` with its
global bi-Lipschitz hypothesis replaced by the local comparison `hcmp` of `D^ϕ` with `D_h` (`d`) on
`B_{3r}(z)`, with error `e ≤ (s/4)σ`. Either alternative of the hypothesis of condition 2 gives
`D_h(u,v) ≥ (s/2)σ`:
* `D_h(u,v) > D_h(u,∂𝔸) ≥ sσ` (GM's `setDist_frontier_lt_iff`, `setDist_frontier_eq_iSup`);
* `D^ϕ(u,v) ≥ bdFun J' 𝔸 u ≥ sσ − e` (CC9a's `bdFun_le_confMetric_of_lt`; `J' ≥ D^ϕ ≥ D_h − e` on
  the collar of `∂𝔸`), hence `D_h(u,v) ≥ D^ϕ(u,v) − e ≥ sσ − 2e`.

Then `J(u,v) ≤ Sσ < (S+s)σ ≤ D_h(u,v; cl 𝔸_{αr,r}) ≤ len(P; D_h)`. -/
theorem gaLongI_of_bounds (hL : d.IsLength) [ProperSpace d.Space] (hϕ : IsConfNbhd ϕ W V)
    {α r s S σ e : ℝ} {z : ℂ} (hα : 3 / 4 ≤ α) (hα1 : α < 1) (hr : 0 < r) (hs : 0 < s)
    (hS : 0 < S) (hσ : 0 < σ) (he0 : 0 ≤ e) (he : e ≤ s / 4 * σ)
    (hUV : (annulus z (r / 2) (2 * r) : Set ℂ) ⊆ V)
    (hlow : ∀ u ∈ closedRing (3 / 4) 1, ∀ v ∈ annulusCollar,
      s * σ < d.1 ((r : ℂ) * u + z, (r : ℂ) * v + z))
    (hdiam : ∀ u ∈ closedRing (3 / 4) 1, ∀ v ∈ closedRing (3 / 4) 1,
      d.internal (annulus z (r / 2) (2 * r)) ((r : ℂ) * u + z) ((r : ℂ) * v + z) ≤
        ENNReal.ofReal (S * σ))
    (hthin : ∀ u ∈ closure (annulus z (α * r) r : Set ℂ),
      ∀ v ∈ closure (annulus z (α * r) r : Set ℂ), s / 2 * σ ≤ d.1 (u, v) →
        ENNReal.ofReal ((S + s) * σ) ≤ d.internal (closure (annulus z (α * r) r : Set ℂ)) u v)
    (hcmp : ∀ u ∈ ball z (3 * r), ∀ v ∈ ball z (3 * r),
      confMetric D ϕ V hbar f u v ≤ ENNReal.ofReal (d.1 (u, v) + e) ∧
      ENNReal.ofReal (d.1 (u, v)) ≤ confMetric D ϕ V hbar f u v + ENNReal.ofReal e) :
    GM.gaLongI (d.internal (annulus z (r / 2) (2 * r)))
      (confMetric D ϕ (annulus z (r / 2) (2 * r)) hbar f) α r z := by
  -- the bounds in unscaled form
  have hlow' : ∀ u : ℂ, 3 / 4 * r ≤ ‖u - z‖ → ‖u - z‖ ≤ r → ∀ y : ℂ,
      (y - z) / (r : ℂ) ∈ annulusCollar → s * σ < d.1 (u, y) := by
    intro u hu1 hu2 y hy
    have := hlow _ (div_mem_closedRing hr hu1 (by rwa [one_mul])) _ hy
    rwa [GM.unscale r hr, GM.unscale r hr] at this
  have hdiam' : ∀ u v : ℂ, 3 / 4 * r ≤ ‖u - z‖ → ‖u - z‖ ≤ r → 3 / 4 * r ≤ ‖v - z‖ →
      ‖v - z‖ ≤ r → d.internal (annulus z (r / 2) (2 * r)) u v ≤ ENNReal.ofReal (S * σ) := by
    intro u v hu1 hu2 hv1 hv2
    have := hdiam _ (div_mem_closedRing hr hu1 (by rwa [one_mul]))
      _ (div_mem_closedRing hr hv1 (by rwa [one_mul]))
    rwa [GM.unscale r hr, GM.unscale r hr] at this
  intro u hu v hv hcase a b P hab hP hPa hPb hPK
  set U : Set ℂ := (annulus z (r / 2) (2 * r) : Set ℂ)
  have hUo : IsOpen U := (annulus z (r / 2) (2 * r)).isOpen
  have hUb : Bornology.IsBounded U := GM.isBounded_annulus _ _
  have hα2 : 1 / 2 < α := by linarith
  have huU : u ∈ U := sphere_inner_subset hα2 hα1 hr hu
  have hvU : v ∈ U := sphere_outer_subset hα2 hα1 hr hv
  have hun : ‖u - z‖ = α * r := mem_sphere_iff_norm.1 hu
  have hvn : ‖v - z‖ = r := mem_sphere_iff_norm.1 hv
  have hu1 : 3 / 4 * r ≤ ‖u - z‖ := by rw [hun]; nlinarith
  have hu2 : ‖u - z‖ ≤ r := by rw [hun]; nlinarith
  have hv1 : 3 / 4 * r ≤ ‖v - z‖ := by rw [hvn]; linarith
  have hub : u ∈ ball z (3 * r) := by rw [mem_ball_iff_norm]; linarith
  have hvb : v ∈ ball z (3 * r) := by rw [mem_ball_iff_norm]; linarith
  -- Step 1: either alternative gives `D_h(u,v) ≥ (s/2)σ`
  have key : s / 2 * σ ≤ d.1 (u, v) := by
    rcases hcase with h1 | h2
    · -- `D_h(u,v) > D_h(u, ∂𝔸) ≥ sσ`
      have h1' : setDist d {u} (frontier U) < ENNReal.ofReal (d.1 (u, v)) := by
        rw [GM.setDist_frontier_lt_iff d hL hUo huU hvU,
          GM.setDist_frontier_eq_iSup d hL hUo hUb huU]
        exact h1
      have hle : ENNReal.ofReal (s * σ) ≤ setDist d {u} (frontier U) := by
        unfold setDist
        refine MetricGeometry.le_setEDist.2 ?_
        rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
        rw [mem_singleton_iff] at hx
        subst hx
        rw [edist_dist]
        exact ENNReal.ofReal_le_ofReal
          (hlow' x hu1 hu2 y (div_mem_annulusCollar_of_frontier hr hy)).le
      have := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity)).1 (hle.trans_lt h1')
      nlinarith
    · -- `D^ϕ(u,v) ≥ bdFun J' 𝔸 u ≥ sσ − e` and `D_h(u,v) ≥ D^ϕ(u,v) − e`
      have hb := bdFun_le_confMetric_of_lt (D := D) hϕ hUo hUV huU hvU h2
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (by positivity : (0 : ℝ) < r / 10)
      have hsup : (⨅ y ∈ GM.nearFrontier U (1 / ((n : ℝ) + 1)), confMetric D ϕ U hbar f u y) ≤
          GM.bdFun (confMetric D ϕ U hbar f) U u :=
        le_iSup (fun n : ℕ => ⨅ y ∈ GM.nearFrontier U (1 / ((n : ℝ) + 1)),
          confMetric D ϕ U hbar f u y) n
      have hlowJ : ENNReal.ofReal (s * σ) ≤
          GM.bdFun (confMetric D ϕ U hbar f) U u + ENNReal.ofReal e := by
        refine le_trans ?_ (add_le_add hsup le_rfl)
        rw [ENNReal.iInf_add]
        refine le_iInf fun y => ?_
        rw [ENNReal.iInf_add]
        refine le_iInf fun hy => ?_
        have hyU : y ∈ U := hy.1
        have hyb : y ∈ ball z (3 * r) := by
          rw [mem_ball_iff_norm]
          have : ‖y - z‖ < 2 * r := hyU.2
          linarith
        calc ENNReal.ofReal (s * σ) ≤ ENNReal.ofReal (d.1 (u, y)) :=
              ENNReal.ofReal_le_ofReal
                (hlow' u hu1 hu2 y (div_mem_annulusCollar_of_nearFrontier hr hn.le hy)).le
          _ ≤ confMetric D ϕ V hbar f u y + ENNReal.ofReal e := (hcmp u hub y hyb).2
          _ ≤ confMetric D ϕ U hbar f u y + ENNReal.ofReal e :=
              add_le_add (confMetric_anti hUV u y) le_rfl
      have hchain : ENNReal.ofReal (s * σ) ≤ ENNReal.ofReal (d.1 (u, v) + e + e) := by
        calc ENNReal.ofReal (s * σ)
            ≤ GM.bdFun (confMetric D ϕ U hbar f) U u + ENNReal.ofReal e := hlowJ
          _ ≤ confMetric D ϕ V hbar f u v + ENNReal.ofReal e := add_le_add hb le_rfl
          _ ≤ ENNReal.ofReal (d.1 (u, v) + e) + ENNReal.ofReal e :=
              add_le_add (hcmp u hub v hvb).1 le_rfl
          _ = ENNReal.ofReal (d.1 (u, v) + e + e) :=
              (ENNReal.ofReal_add (add_nonneg (d.nonneg u v) he0) he0).symm
      have := (ENNReal.ofReal_le_ofReal_iff (by linarith [d.nonneg u v])).1 hchain
      linarith
  -- Step 2: the length bound
  have hcu : u ∈ closure (annulus z (α * r) r : Set ℂ) := hPa ▸ hPK ⟨a, left_mem_Icc.2 hab, rfl⟩
  have hcv : v ∈ closure (annulus z (α * r) r : Set ℂ) := hPb ▸ hPK ⟨b, right_mem_Icc.2 hab, rfl⟩
  have hmaps : MapsTo P (Icc a b) U := fun t ht =>
    GM.closure_annulus_subset hα2 hr (hPK ⟨t, ht, rfl⟩)
  rw [GM.lenFun_internal d hP hmaps]
  have hlen : d.internal (closure (annulus z (α * r) r : Set ℂ)) u v ≤ d.len P a b := by
    have := MetricGeometry.internalEDist_le_curveLength (X := d.Space) hab
      ((ContMetric.continuous_pt d).comp_continuousOn hP)
      (Y := d.pt '' closure (annulus z (α * r) r : Set ℂ))
      (fun t ht => ⟨P t, hPK ⟨t, ht, rfl⟩, rfl⟩)
    simpa [ContMetric.internal, ContMetric.len, hPa, hPb] using this
  calc d.internal U u v ≤ ENNReal.ofReal (S * σ) := hdiam' u v hu1 hu2 hv1 hvn.le
    _ < ENNReal.ofReal ((S + s) * σ) :=
        (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by nlinarith)
    _ ≤ _ := hthin u hcu v hcv key
    _ ≤ _ := hlen

/-! ## 3. Condition 1 -/

/-- **Condition 1, deterministic core** ([3] Lemma 3.9 with [3] Lemma 2.2 in ratio form; CC0 D10,
D14): on condition 2, if `D_h(u,v) > t` and `D^ϕ(u,v) ≤ D_h(u,v) + e` with `e ≤ δt` for all
`u ∈ ∂B_{αr}(z)`, `v ∈ ∂B_r(z)`, then condition 1 holds with `C' = 1 + δ`. -/
theorem gaCompareBI_of_bounds (hL : d.IsLength) [ProperSpace d.Space] (hϕ : IsConfNbhd ϕ W V)
    {α r δ t e : ℝ} {z : ℂ} (hα : 1 / 2 < α) (hα1 : α < 1) (hr : 0 < r) (hδ : 0 ≤ δ)
    (he : e ≤ δ * t) (hUV : (annulus z (r / 2) (2 * r) : Set ℂ) ⊆ V)
    (hlong : GM.gaLongI (d.internal (annulus z (r / 2) (2 * r)))
      (confMetric D ϕ (annulus z (r / 2) (2 * r)) hbar f) α r z)
    (hsep : ∀ u ∈ sphere z (α * r), ∀ v ∈ sphere z r, t < d.1 (u, v))
    (hcmp : ∀ u ∈ sphere z (α * r), ∀ v ∈ sphere z r,
      confMetric D ϕ V hbar f u v ≤ ENNReal.ofReal (d.1 (u, v) + e)) :
    GM.gaCompareBI (d.internal (annulus z (r / 2) (2 * r)))
      (confMetric D ϕ (annulus z (r / 2) (2 * r)) hbar f) α (1 + δ) r z := by
  refine gaCompareBI_of_confMetric_le hL hϕ (by linarith) hα hα1 hr hUV hlong fun u hu v hv => ?_
  refine (hcmp u hu v hv).trans (ENNReal.ofReal_le_ofReal ?_)
  have h1 : δ * t ≤ δ * d.1 (u, v) := mul_le_mul_of_nonneg_left (hsep u hu v hv).le hδ
  linarith

end Cond

/-! ## 4. The event `E_r(z)` -/

/-- **The event `E_r(z)` from the bounds** ([3] Lemma 3.9, deterministic part; CC0 D14, D10).
`σ = 𝔰_r(z)` and `σ₃ = 𝔰_{3r}(z)` are the normalizations of the bounds at the scales `r` and `3r`;
they are compared through `e2` and `e7` (`tσ₃ < D_h(z+r, z−r) ≤ Sσ`), so that the error `δ'σ₃` of
`e6` is at most `(s/4)σ` (condition 2) and at most `δ · tσ₃ < δ D_h(u,v)` (condition 1). -/
theorem confGoodAnnulus_of_bounds {D : DistC → ContMetric} {ϕ : ℂ → ℂ} {W V : Set ℂ}
    {h hbar : DistC} {f : C(ℂ, ℝ)} (hL : (D h).IsLength) [ProperSpace (D h).Space]
    (hϕ : IsConfNbhd ϕ W V) {α A δ δ' r s S t σ σ₃ : ℝ} {z : ℂ}
    (hα : 3 / 4 ≤ α) (hα1 : α < 1) (hr : 0 < r) (hs : 0 < s) (hS : 0 < S)
    (hσ : 0 < σ) (hσ₃ : 0 < σ₃) (hδ : 0 ≤ δ) (hδ'0 : 0 ≤ δ')
    (hδ's : δ' ≤ s * t / (4 * S)) (hδ'δ : δ' ≤ δ * t)
    (hUV : (annulus z (r / 2) (2 * r) : Set ℂ) ⊆ V)
    (e1 : ∀ u ∈ closedRing (3 / 4) 1, ∀ v ∈ annulusCollar,
      s * σ < (D h).1 ((r : ℂ) * u + z, (r : ℂ) * v + z))
    (e2 : ∀ u ∈ closedRing (3 / 4) 1, ∀ v ∈ closedRing (3 / 4) 1,
      (D h).internal (annulus z (r / 2) (2 * r)) ((r : ℂ) * u + z) ((r : ℂ) * v + z) ≤
        ENNReal.ofReal (S * σ))
    (e3 : ∀ u ∈ closure (annulus z (α * r) r : Set ℂ),
      ∀ v ∈ closure (annulus z (α * r) r : Set ℂ), s / 2 * σ ≤ (D h).1 (u, v) →
        ENNReal.ofReal ((S + s) * σ) ≤ (D h).internal (closure (annulus z (α * r) r : Set ℂ)) u v)
    (e6 : ∀ u ∈ ball z (3 * r), ∀ v ∈ ball z (3 * r),
      confMetric D ϕ V hbar f u v ≤ ENNReal.ofReal ((D h).1 (u, v) + δ' * σ₃) ∧
      ENNReal.ofReal ((D h).1 (u, v)) ≤ confMetric D ϕ V hbar f u v + ENNReal.ofReal (δ' * σ₃))
    (e7 : ∀ u ∈ closedBall (0 : ℂ) (1 / 3), ∀ v ∈ closedBall (0 : ℂ) (1 / 3),
      (1 - α) / 3 ≤ ‖u - v‖ →
        t * σ₃ < (D h).1 (((3 * r : ℝ) : ℂ) * u + z, ((3 * r : ℝ) : ℂ) * v + z))
    (e8 : GM.gaAroundI ((D h).internal (annulus z (r / 2) (2 * r))) α A r z) :
    confGoodAnnulus D ϕ α A (1 + δ) r z h hbar f := by
  have h3r : 0 < 3 * r := by linarith
  -- `e7` in unscaled form
  have e7' : ∀ u v : ℂ, ‖u - z‖ ≤ r → ‖v - z‖ ≤ r → (1 - α) * r ≤ ‖u - v‖ →
      t * σ₃ < (D h).1 (u, v) := by
    intro u v hu hv huv
    have hu' : (u - z) / ((3 * r : ℝ) : ℂ) ∈ closedBall (0 : ℂ) (1 / 3) := by
      rw [mem_closedBall_zero_iff, GM.norm_unscale _ h3r, div_le_iff₀ h3r]
      linarith
    have hv' : (v - z) / ((3 * r : ℝ) : ℂ) ∈ closedBall (0 : ℂ) (1 / 3) := by
      rw [mem_closedBall_zero_iff, GM.norm_unscale _ h3r, div_le_iff₀ h3r]
      linarith
    have huv' : (1 - α) / 3 ≤
        ‖(u - z) / ((3 * r : ℝ) : ℂ) - (v - z) / ((3 * r : ℝ) : ℂ)‖ := by
      rw [← sub_div, show u - z - (v - z) = u - v by ring, GM.Bilip.norm_div_ofReal h3r,
        le_div_iff₀ h3r]
      linarith
    have := e7 _ hu' _ hv' huv'
    rwa [GM.unscale _ h3r, GM.unscale _ h3r] at this
  -- the two scales: `tσ₃ < D_h(z+r, z−r) ≤ Sσ`
  have hratio : t * σ₃ < S * σ := by
    have hx₁ : ‖(z + (r : ℂ)) - z‖ = r := by
      rw [add_sub_cancel_left, Complex.norm_real, Real.norm_of_nonneg hr.le]
    have hx₂ : ‖(z - (r : ℂ)) - z‖ = r := by
      rw [sub_sub_cancel_left, norm_neg, Complex.norm_real, Real.norm_of_nonneg hr.le]
    have hx₁₂ : ‖(z + (r : ℂ)) - (z - (r : ℂ))‖ = 2 * r := by
      rw [show (z + (r : ℂ)) - (z - (r : ℂ)) = ((2 * r : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    have h1 := e7' _ _ hx₁.le hx₂.le (by rw [hx₁₂]; nlinarith)
    have h2 := e2 _ (div_mem_closedRing hr (by rw [hx₁]; linarith) (by rw [hx₁]; linarith))
      _ (div_mem_closedRing hr (by rw [hx₂]; linarith) (by rw [hx₂]; linarith))
    rw [GM.unscale r hr, GM.unscale r hr] at h2
    have h3 : ENNReal.ofReal ((D h).1 (z + (r : ℂ), z - (r : ℂ))) ≤ ENNReal.ofReal (S * σ) := by
      refine le_trans ?_ h2
      rw [← ContMetric.edist_pt]
      exact MetricGeometry.edist_le_internalEDist _ _ _
    have := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h3
    linarith
  -- the error of `e6` against both scales
  have he : δ' * σ₃ ≤ s / 4 * σ := by
    calc δ' * σ₃ ≤ s * t / (4 * S) * σ₃ := mul_le_mul_of_nonneg_right hδ's hσ₃.le
      _ = s / (4 * S) * (t * σ₃) := by ring
      _ ≤ s / (4 * S) * (S * σ) := mul_le_mul_of_nonneg_left hratio.le (by positivity)
      _ = s / 4 * σ := by field_simp
  have he' : δ' * σ₃ ≤ δ * (t * σ₃) := by
    calc δ' * σ₃ ≤ δ * t * σ₃ := mul_le_mul_of_nonneg_right hδ'δ hσ₃.le
      _ = δ * (t * σ₃) := by ring
  have hα2 : 1 / 2 < α := by linarith
  have hlong := gaLongI_of_bounds hL hϕ hα hα1 hr hs hS hσ (by positivity) he hUV e1 e2 e3 e6
  have hball : ∀ x ∈ closedBall z r, x ∈ ball z (3 * r) := fun x hx => by
    rw [mem_ball_iff_norm]
    rw [mem_closedBall_iff_norm] at hx
    linarith
  have hsph1 : ∀ u ∈ sphere z (α * r), ‖u - z‖ ≤ r := fun u hu => by
    rw [mem_sphere_iff_norm.1 hu]; nlinarith
  have hsph2 : ∀ v ∈ sphere z r, ‖v - z‖ ≤ r := fun v hv => (mem_sphere_iff_norm.1 hv).le
  have hsep : ∀ u ∈ sphere z (α * r), ∀ v ∈ sphere z r, t * σ₃ < (D h).1 (u, v) := by
    intro u hu v hv
    refine e7' u v (hsph1 u hu) (hsph2 v hv) ?_
    have t1 := norm_sub_le_norm_sub_add_norm_sub v u z
    rw [norm_sub_rev v u, mem_sphere_iff_norm.1 hu, mem_sphere_iff_norm.1 hv] at t1
    linarith
  have hcomp := gaCompareBI_of_bounds hL hϕ hα2 hα1 hr hδ he' hUV hlong hsep
    fun u hu v hv => (e6 u (hball u (mem_closedBall_iff_norm.2 (hsph1 u hu)))
      v (hball v (mem_closedBall_iff_norm.2 (hsph2 v hv)))).1
  unfold confGoodAnnulus GM.goodAnnulusI
  exact ⟨hcomp, hlong, e8⟩

end SmallGammaGeodesics.CC
