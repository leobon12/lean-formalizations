import LQGMetric.Papers.GM.S3.AttainedP36Det
import LQGMetric.Metric.Internal
import LQGMetric.Metric.InternalLimitC

/-!
# The telescoping argument of [3] Prop 3.6 for an extended-valued `d′` on `V`
(track CC, packet CC8a, target T3)

[3] = Gwynne–Miller, *Conformal covariance of the Liouville quantum gravity metric for
γ ∈ (0, 2)*, arXiv:1905.00384v2, proof of Proposition 3.6, Steps 4–6, (3.18)–(3.24). Plan:
`planning/audits/CC0-conformal-covariance-plan.md`, Details (a) **D15** steps 2–4 (CC10). This
generalizes the deterministic core of the GM proof formalized in LQGMetric (GM =
arXiv:1905.00383, Prop 3.6):
`LQGMetric.GM.tele_step`, `GM.tele_core` (`Papers/GM/S3/AttainedTele.lean`), `GM.gm_S3_8`
(`AttainedShortcut.lean`) and `GM.p36_pair` (`AttainedP36Det.lean`).

The changes from the GM versions are only those that the extended-valued `d′ := D^ϕ` on `V` needs:
* `D′ : ContMetric` becomes `d′ : ℂ → ℂ → ℝ≥0∞` with the triangle inequality; real bounds
  `D′(x,y) ≤ c` become `d′ x y ≤ ENNReal.ofReal c`;
* the global current bound `D′ ≤ C_* D` becomes the bound on `V` through the internal metric,
  `d′ x y ≤ C_s · D(x,y;V)` for `x, y ∈ V` (the hypothesis of `CC.ConfImprove`), and the geodesic
  `P` must stay in `V`. Along such a geodesic `D(P s, P t; V) ≤ t − s` (`internal_le_of_geod`), so
  the bad intervals cost `d′(P s, P t) ≤ C_s (t − s)` (`le_ofReal_of_ratio_geod`, [3] (3.20));
* the good balls are an abstract predicate `Good v r` with the `D`-forms of conditions 1 and 3 of
  [3]'s event `E_r(v)` as hypotheses (`p36_pair_ext`), instead of the field event
  `g ∈ GM.goodAnnulus D D' α A C' r v`;
* `0 ≤ C'` is assumed in `tele_step_ext` (`ENNReal.ofReal` truncates negative bounds).

`GM.gm_S3_8` does not involve `D′`; it applies verbatim to the `D_h`-geodesic. Here it is
restated in the form (3.21) that [3] uses (`sub_le_frac_of_shortcut`).

Contents:
* `curveLength_geod_le`, `internal_le_of_geod`, `le_ofReal_of_ratio_geod`: the geodesic in `V`;
* `sub_le_frac_of_shortcut`: [3] (3.21), `s_j − t_{j−1} ≤ A/(A+1) (t_j − t_{j−1})`;
* `tele_step_ext`: one step `t_{j−1} ↦ t_j`, [3] (3.20)–(3.22);
* `tele_core_ext`: the sum, [3] (3.23), with the end error `C_s ω`;
* `p36_pair_ext`: one pair `z, w` with a unique geodesic in `S ⊆ V`, [3] (3.18), (3.19), (3.24):
  `d′(z,w) ≤ (C' + A/(A+1)(C_s − C')) D(z,w) + 3 C_s ω`;
* `p36_pair_ext_improve`: the same with `C' = 1 + δ`, `C_s = C`, i.e. the improvement
  `C ↦ 1 + δ + θ(C − 1 − δ)`, `θ = A/(A+1)`, of `CC.ConfImprove`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace SmallGammaGeodesics.CC

open LQGMetric LQGMetric.Blueprint LQGMetric.MetricGeometry LQGMetric.GM

/-- `ofReal a + ofReal b ≤ ofReal c` from `a + b ≤ c` with `a, b ≥ 0` -/
private lemma ofReal_add_le_of_le {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a + b ≤ c) :
    ENNReal.ofReal a + ENNReal.ofReal b ≤ ENNReal.ofReal c := by
  rw [← ENNReal.ofReal_add ha hb]
  exact ENNReal.ofReal_le_ofReal h

section Geod

variable (D : ContMetric) {P : ℝ → ℂ} {L : ℝ}

/-- a `D`-geodesic parametrized by `D`-length is `1`-Lipschitz into `(ℂ, D)` -/
lemma lipschitzOnWith_geod (hgeo : ∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L, D.1 (P s, P t) = |t - s|) :
    LipschitzOnWith 1 (D.pt ∘ P) (Icc 0 L) := by
  intro s hs t ht
  rw [ENNReal.coe_one, one_mul, Function.comp_apply, Function.comp_apply, ContMetric.edist_pt,
    hgeo s hs t ht, edist_dist, Real.dist_eq, abs_sub_comm]

/-- the `D`-length of a `D`-geodesic on `[s, t] ⊆ [0, L]` is at most `t − s` -/
lemma curveLength_geod_le (hgeo : ∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L, D.1 (P s, P t) = |t - s|)
    {s t : ℝ} (hs : 0 ≤ s) (htL : t ≤ L) :
    curveLength (D.pt ∘ P) s t ≤ ENNReal.ofReal (t - s) := by
  have h1 := (lipschitzOnWith_geod D hgeo).comp_eVariationOn_le (g := id) (s := Icc s t)
    (fun τ hτ => ⟨hs.trans hτ.1, hτ.2.trans htL⟩)
  have h2 : eVariationOn (id : ℝ → ℝ) (Icc s t) = ENNReal.ofReal (t - s) := by
    have := (monotoneOn_id (s := (univ : Set ℝ))).eVariationOn_eq (mem_univ s) (mem_univ t)
    rwa [univ_inter] at this
  unfold curveLength
  calc eVariationOn (D.pt ∘ P) (Icc s t) = eVariationOn ((D.pt ∘ P) ∘ id) (Icc s t) := rfl
    _ ≤ ((1 : NNReal) : ℝ≥0∞) * eVariationOn id (Icc s t) := h1
    _ = ENNReal.ofReal (t - s) := by rw [ENNReal.coe_one, one_mul, h2]

/-- along a `D`-geodesic contained in `V`, `D(P s, P t; V) ≤ t − s` -/
lemma internal_le_of_geod (hP : ContinuousOn P (Icc 0 L))
    (hgeo : ∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L, D.1 (P s, P t) = |t - s|)
    {V : Set ℂ} (hPV : ∀ τ ∈ Icc 0 L, P τ ∈ V) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (htL : t ≤ L) : D.internal V (P s) (P t) ≤ ENNReal.ofReal (t - s) := by
  have hsub : Icc s t ⊆ Icc 0 L := Icc_subset_Icc hs htL
  have hc : ContinuousOn (D.pt ∘ P) (Icc s t) := D.continuous_pt.comp_continuousOn (hP.mono hsub)
  have hm : MapsTo (D.pt ∘ P) (Icc s t) (D.pt '' V) := fun τ hτ => ⟨P τ, hPV τ (hsub hτ), rfl⟩
  exact (internalEDist_le_curveLength hst hc hm).trans (curveLength_geod_le D hgeo hs htL)

/-- **The bad intervals** ([3] (3.20), right): if `d′ ≤ C_s · D(·,·;V)` on `V` and the
`D`-geodesic `P` stays in `V`, then `d′(P s, P t) ≤ C_s (t − s)` for `0 ≤ s ≤ t ≤ L`. -/
lemma le_ofReal_of_ratio_geod {d' : ℂ → ℂ → ℝ≥0∞} (hP : ContinuousOn P (Icc 0 L))
    (hgeo : ∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L, D.1 (P s, P t) = |t - s|)
    {V : Set ℂ} (hPV : ∀ τ ∈ Icc 0 L, P τ ∈ V) {Cs : ℝ} (hCs : 0 ≤ Cs)
    (hratio : ∀ x ∈ V, ∀ y ∈ V, d' x y ≤ ENNReal.ofReal Cs * D.internal V x y)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (htL : t ≤ L) :
    d' (P s) (P t) ≤ ENNReal.ofReal (Cs * (t - s)) := by
  rw [ENNReal.ofReal_mul hCs]
  exact (hratio _ (hPV s ⟨hs, hst.trans htL⟩) _ (hPV t ⟨hs.trans hst, htL⟩)).trans
    (mul_le_mul_right (internal_le_of_geod D hP hgeo hPV hs hst htL) _)

/-- **[3] (3.21)** (Step 5), from GM.S3.8 (`LQGMetric.GM.gm_S3_8`, `s − a ≤ A (t − s)`): the bad
interval `[a, s]` is at most the fraction `A/(A+1)` of `[a, t]`. Only the `D`-geodesic `P` and the
disconnecting path of condition 3 enter; `d′` does not. -/
theorem sub_le_frac_of_shortcut (hP : ContinuousOn P (Icc 0 L))
    (hgeo : ∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L, D.1 (P s, P t) = |t - s|)
    {w : ℂ} {α r A : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hA : 0 ≤ A)
    {a' b' : ℝ} {G : ℝ → ℂ}
    (hGd : Disconnects (G '' Icc a' b') (sphere w (α * r)) (sphere w r))
    (hGl : D.len G a' b' ≤ ENNReal.ofReal A * setDist D (sphere w (α * r)) (sphere w r))
    {a s t : ℝ} (ha0 : 0 ≤ a) (has : a ≤ s) (hst : s ≤ t) (htL : t ≤ L)
    (h0 : P 0 ∉ ball w r) (hPa : P a ∈ closedBall w (α * r)) (hPs : P s ∈ sphere w (α * r))
    (hPt : P t ∈ sphere w r) (hLr : P L ∉ ball w r) : s - a ≤ A / (A + 1) * (t - a) := by
  have h := gm_S3_8 D hP hgeo hα hα1 hA hGd hGl ha0 has hst htL h0 hPa hPs hPt hLr
  have hA1 : 0 < A + 1 := by linarith
  rw [div_mul_eq_mul_div, le_div_iff₀ hA1]
  nlinarith

end Geod

section Tele

variable (D : ContMetric) {P : ℝ → ℂ} {L : ℝ}

/-- **One step of the recursion** ([3] Step 4 and (3.20)–(3.22); generalizes
`LQGMetric.GM.tele_step` to an `ℝ≥0∞`-valued `d′` bounded by `C_s · D(·,·;V)` on `V`): from
`a = t_{j−1}` with `P(a) ∈ B_{r/2}(w)` for a good ball, the exit time `t = t_j` of `B_r(w)` and the
last visit `s = s_j ∈ [a, t]` of `∂B_{αr}(w)` satisfy `|P(t) − P(a)| ≥ r/2` and
`d′(P a, P t) ≤ (C' + A/(A+1)(C_s − C')) (t − a)`. -/
theorem tele_step_ext {d' : ℂ → ℂ → ℝ≥0∞} (htri : ∀ x y z, d' x z ≤ d' x y + d' y z)
    (hP : ContinuousOn P (Icc 0 L))
    (hgeo : ∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L, D.1 (P s, P t) = |t - s|)
    {V : Set ℂ} (hPV : ∀ τ ∈ Icc 0 L, P τ ∈ V)
    {α A Cs C' : ℝ} (hα : 1 / 2 < α) (hα1 : α < 1) (hA : 0 ≤ A) (hC0 : 0 ≤ C')
    (hCC : C' ≤ Cs) (hratio : ∀ x ∈ V, ∀ y ∈ V, d' x y ≤ ENNReal.ofReal Cs * D.internal V x y)
    {w : ℂ} {r : ℝ} (hr : 0 < r)
    (hround : ∃ (a' b' : ℝ) (G : ℝ → ℂ),
      Disconnects (G '' Icc a' b') (sphere w (α * r)) (sphere w r) ∧
      D.len G a' b' ≤ ENNReal.ofReal A * setDist D (sphere w (α * r)) (sphere w r))
    (hcomp : ∀ s t, 0 ≤ s → s ≤ t → t ≤ L → P s ∈ sphere w (α * r) → P t ∈ sphere w r →
      (∀ u ∈ Icc s t, P u ∈ closedBall w r ∧ P u ∉ ball w (α * r)) →
      d' (P s) (P t) ≤ ENNReal.ofReal (C' * (t - s)))
    {a b : ℝ} (ha0 : 0 ≤ a) (hab : a ≤ b) (hbL : b ≤ L)
    (hPa : P a ∈ ball w (r / 2)) (hPb : P b ∉ ball w r) (h0 : P 0 ∉ ball w r)
    (hL : P L ∉ ball w r) :
    ∃ t ∈ Ioc a b, r / 2 ≤ ‖P t - P a‖ ∧
      d' (P a) (P t) ≤ ENNReal.ofReal ((C' + A / (A + 1) * (Cs - C')) * (t - a)) := by
  have hPc : ContinuousOn P (Icc a b) := hP.mono (Icc_subset_Icc ha0 hbL)
  -- the exit time `t`
  set T := Icc a b ∩ P ⁻¹' (ball w r)ᶜ with hT
  have hTc : IsClosed T :=
    hPc.preimage_isClosed_of_isClosed isClosed_Icc isOpen_ball.isClosed_compl
  have hTne : T.Nonempty := ⟨b, ⟨hab, le_rfl⟩, hPb⟩
  have hTb : BddBelow T := ⟨a, fun u hu => hu.1.1⟩
  set t := sInf T with ht
  have htT : t ∈ T := hTc.csInf_mem hTne hTb
  have hat : a < t := by
    rcases eq_or_lt_of_le htT.1.1 with h | h
    · exact absurd (h ▸ hPa : P t ∈ ball w (r / 2)) fun h' =>
        htT.2 (ball_subset_ball (by linarith) h')
    · exact h
  have hbefore : ∀ u ∈ Ico a t, P u ∈ ball w r := fun u hu => by
    by_contra hn
    exact absurd (csInf_le hTb ⟨⟨hu.1, by linarith [hu.2, htT.1.2]⟩, hn⟩) (not_le.2 hu.2)
  have hPt_cl : P t ∈ closedBall w r := by
    have hS : IsClosed (Icc a t ∩ P ⁻¹' closedBall w r) :=
      (hPc.mono (Icc_subset_Icc le_rfl htT.1.2)).preimage_isClosed_of_isClosed isClosed_Icc
        isClosed_closedBall
    have hsub : Icc a t ⊆ Icc a t ∩ P ⁻¹' closedBall w r := by
      have := closure_minimal (s := Ico a t) (t := Icc a t ∩ P ⁻¹' closedBall w r)
        (fun u hu => ⟨Ico_subset_Icc_self hu, ball_subset_closedBall (hbefore u hu)⟩) hS
      rwa [closure_Ico hat.ne] at this
    exact (hsub ⟨hat.le, le_rfl⟩).2
  have hPt : P t ∈ sphere w r := by
    have h1 := mem_closedBall.1 hPt_cl
    have h2 : ¬ dist (P t) w < r := htT.2
    exact mem_sphere.2 (le_antisymm h1 (not_lt.1 h2))
  -- the last visit `s` of `cl B_{αr}(w)` before `t`
  have hαr : α * r < r := by nlinarith
  have hr2 : r / 2 < α * r := by nlinarith
  set S := Icc a t ∩ P ⁻¹' closedBall w (α * r) with hSdef
  have hSc : IsClosed S :=
    (hPc.mono (Icc_subset_Icc le_rfl htT.1.2)).preimage_isClosed_of_isClosed isClosed_Icc
      isClosed_closedBall
  have hSne : S.Nonempty := ⟨a, ⟨le_rfl, hat.le⟩, ball_subset_closedBall
    (ball_subset_ball hr2.le hPa)⟩
  have hSb : BddAbove S := ⟨t, fun u hu => hu.1.2⟩
  set s := sSup S with hs
  have hsS : s ∈ S := hSc.csSup_mem hSne hSb
  have hst : s < t := by
    rcases eq_or_lt_of_le hsS.1.2 with h | h
    · have := mem_closedBall.1 hsS.2
      rw [h, mem_sphere.1 hPt] at this
      linarith
    · exact h
  have has : a ≤ s := le_csSup hSb ⟨⟨le_rfl, hat.le⟩, ball_subset_closedBall
    (ball_subset_ball hr2.le hPa)⟩
  have hafter : ∀ u ∈ Ioc s t, P u ∉ closedBall w (α * r) := fun u hu hn =>
    absurd (le_csSup hSb ⟨⟨by linarith [hu.1], hu.2⟩, hn⟩) (not_le.2 hu.1)
  have hPs_out : P s ∉ ball w (α * r) := by
    have hS' : IsClosed (Icc s t ∩ P ⁻¹' (ball w (α * r))ᶜ) :=
      (hPc.mono (Icc_subset_Icc has htT.1.2)).preimage_isClosed_of_isClosed isClosed_Icc
        isOpen_ball.isClosed_compl
    have hsub : Icc s t ⊆ Icc s t ∩ P ⁻¹' (ball w (α * r))ᶜ := by
      have := closure_minimal (s := Ioc s t) (t := Icc s t ∩ P ⁻¹' (ball w (α * r))ᶜ)
        (fun u hu => ⟨Ioc_subset_Icc_self hu,
          fun h' => hafter u hu (ball_subset_closedBall h')⟩) hS'
      rwa [closure_Ioc hst.ne] at this
    exact (hsub ⟨le_rfl, hst.le⟩).2
  have hPs : P s ∈ sphere w (α * r) :=
    mem_sphere.2 (le_antisymm (mem_closedBall.1 hsS.2) (not_lt.1 hPs_out))
  -- (3.21)
  obtain ⟨a', b', G, hGd, hGl⟩ := hround
  have hfrac := sub_le_frac_of_shortcut D hP hgeo (by linarith) hα1.le hA hGd hGl ha0 has hst.le
    (htT.1.2.trans hbL) h0 (ball_subset_closedBall (ball_subset_ball hr2.le hPa)) hPs hPt hL
  -- (3.20): the good interval `[s, t]` and the bad interval `[a, s]`
  have hann : ∀ u ∈ Icc s t, P u ∈ closedBall w r ∧ P u ∉ ball w (α * r) := by
    intro u hu
    rcases eq_or_lt_of_le hu.1 with h | h
    · rw [← h]; exact ⟨hbefore s ⟨has, hst⟩ |> ball_subset_closedBall, hPs_out⟩
    · refine ⟨?_, fun h' => hafter u ⟨h, hu.2⟩ (ball_subset_closedBall h')⟩
      rcases eq_or_lt_of_le hu.2 with h2 | h2
      · rw [h2]; exact hPt_cl
      · exact ball_subset_closedBall (hbefore u ⟨by linarith, h2⟩)
  have hc1 := hcomp s t (ha0.trans has) hst.le (htT.1.2.trans hbL) hPs hPt hann
  have hCs0 : 0 ≤ Cs := hC0.trans hCC
  have hc2 : d' (P a) (P s) ≤ ENNReal.ofReal (Cs * (s - a)) :=
    le_ofReal_of_ratio_geod D hP hgeo hPV hCs0 hratio ha0 has (by linarith [htT.1.2])
  refine ⟨t, ⟨hat, htT.1.2⟩, ?_, ?_⟩
  · have h1 := mem_sphere.1 hPt
    have h2 := mem_ball.1 hPa
    rw [dist_eq_norm] at h1 h2
    have := norm_sub_norm_le (P t - w) (P a - w)
    rw [sub_sub_sub_cancel_right] at this
    linarith
  · -- (3.22)
    have hkey : (Cs - C') * (s - a) ≤ (Cs - C') * (A / (A + 1) * (t - a)) :=
      mul_le_mul_of_nonneg_left hfrac (sub_nonneg.2 hCC)
    calc d' (P a) (P t) ≤ d' (P a) (P s) + d' (P s) (P t) := htri _ _ _
      _ ≤ ENNReal.ofReal (Cs * (s - a)) + ENNReal.ofReal (C' * (t - s)) := add_le_add hc2 hc1
      _ ≤ ENNReal.ofReal ((C' + A / (A + 1) * (Cs - C')) * (t - a)) :=
        ofReal_add_le_of_le (mul_nonneg hCs0 (by linarith)) (mul_nonneg hC0 (by linarith))
          (by linarith)

/-- **The telescoping sum** ([3] (3.23); generalizes `LQGMetric.GM.tele_core` to an
`ℝ≥0∞`-valued `d′` bounded by `C_s · D(·,·;V)` on `V`): along a `D`-geodesic `P` in `V`, if every
`P(a)`, `a ∈ [a₀, b₀]`, lies in `B_{r/2}(w)` for a good ball (radius `≥ r_min`, with a short
disconnecting loop and the comparison of condition 1) not containing `P(0)`, `P(L)`, then
`d′(P(a₀), P(b₀)) ≤ (C' + A/(A+1)(C_s − C'))(b₀ − a₀) + C_s ω`, where `ω` bounds `b₀ − a`
whenever `P(b₀)` already lies in the good ball of `P(a)`. -/
theorem tele_core_ext {d' : ℂ → ℂ → ℝ≥0∞} (htri : ∀ x y z, d' x z ≤ d' x y + d' y z)
    (hP : ContinuousOn P (Icc 0 L))
    (hgeo : ∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L, D.1 (P s, P t) = |t - s|)
    {V : Set ℂ} (hPV : ∀ τ ∈ Icc 0 L, P τ ∈ V)
    {α A Cs C' : ℝ} (hα : 1 / 2 < α) (hα1 : α < 1) (hA : 0 ≤ A) (hC0 : 0 ≤ C')
    (hCC : C' ≤ Cs) (hratio : ∀ x ∈ V, ∀ y ∈ V, d' x y ≤ ENNReal.ofReal Cs * D.internal V x y)
    (Good : ℂ → ℝ → Prop) {rmin : ℝ} (hrmin : 0 < rmin) (hgr : ∀ w r, Good w r → rmin ≤ r)
    (hround : ∀ w r, Good w r → ∃ (a' b' : ℝ) (G : ℝ → ℂ),
      Disconnects (G '' Icc a' b') (sphere w (α * r)) (sphere w r) ∧
      D.len G a' b' ≤ ENNReal.ofReal A * setDist D (sphere w (α * r)) (sphere w r))
    (hcomp : ∀ w r, Good w r → ∀ s t, 0 ≤ s → s ≤ t → t ≤ L → P s ∈ sphere w (α * r) →
      P t ∈ sphere w r → (∀ u ∈ Icc s t, P u ∈ closedBall w r ∧ P u ∉ ball w (α * r)) →
      d' (P s) (P t) ≤ ENNReal.ofReal (C' * (t - s)))
    {a₀ b₀ ω : ℝ} (ha₀ : 0 ≤ a₀) (hab : a₀ ≤ b₀) (hbL : b₀ ≤ L) (hω : 0 ≤ ω)
    (hcov : ∀ a ∈ Icc a₀ b₀, ∃ w r, Good w r ∧ P a ∈ ball w (r / 2))
    (hfar : ∀ a ∈ Icc a₀ b₀, ∀ w r, Good w r → P a ∈ ball w (r / 2) →
      P 0 ∉ ball w r ∧ P L ∉ ball w r)
    (hnear : ∀ a ∈ Icc a₀ b₀, ∀ w r, Good w r → P a ∈ ball w (r / 2) → P b₀ ∈ ball w r →
      b₀ - a ≤ ω) :
    d' (P a₀) (P b₀) ≤
      ENNReal.ofReal ((C' + A / (A + 1) * (Cs - C')) * (b₀ - a₀) + Cs * ω) := by
  set K := C' + A / (A + 1) * (Cs - C') with hK
  have hK0 : 0 ≤ K := by
    have : 0 ≤ A / (A + 1) := div_nonneg hA (by linarith)
    have : 0 ≤ A / (A + 1) * (Cs - C') := mul_nonneg this (sub_nonneg.2 hCC)
    linarith
  have hCs0 : 0 ≤ Cs := hC0.trans hCC
  -- uniform continuity of `P` on `[0, L]`
  obtain ⟨δ₀, hδ₀, hδ⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hP) (rmin / 2) (by linarith)
  have main : ∀ n : ℕ, ∀ a ∈ Icc a₀ b₀, b₀ - a ≤ n * δ₀ →
      d' (P a) (P b₀) ≤ ENNReal.ofReal (K * (b₀ - a) + Cs * ω) := by
    intro n
    induction n with
    | zero =>
      intro a ha hn
      have hab0 : a = b₀ :=
        le_antisymm ha.2 (by simp only [CharP.cast_eq_zero, zero_mul] at hn; linarith)
      rw [hab0]
      refine (le_ofReal_of_ratio_geod D hP hgeo hPV hCs0 hratio (ha₀.trans hab) le_rfl hbL).trans
        (ENNReal.ofReal_le_ofReal ?_)
      rw [sub_self, mul_zero, mul_zero, zero_add]
      exact mul_nonneg hCs0 hω
    | succ n ih =>
      intro a ha hn
      obtain ⟨w, r, hg, hPa⟩ := hcov a ha
      have hr : 0 < r := hrmin.trans_le (hgr w r hg)
      by_cases hb : P b₀ ∈ ball w r
      · -- the last, incomplete step: `P(b₀)` is already in the good ball
        have h1 := hnear a ha w r hg hPa hb
        have h2 := le_ofReal_of_ratio_geod D hP hgeo hPV hCs0 hratio (ha₀.trans ha.1) ha.2 hbL
        refine h2.trans (ENNReal.ofReal_le_ofReal ?_)
        have h3 : 0 ≤ K * (b₀ - a) := mul_nonneg hK0 (by linarith [ha.2])
        have h4 : Cs * (b₀ - a) ≤ Cs * ω := mul_le_mul_of_nonneg_left h1 hCs0
        linarith
      · obtain ⟨h0, hL⟩ := hfar a ha w r hg hPa
        obtain ⟨t, ht, hdist, hstep⟩ := tele_step_ext D htri hP hgeo hPV hα hα1 hA hC0 hCC
          hratio hr (hround w r hg) (hcomp w r hg) (ha₀.trans ha.1) ha.2 hbL hPa hb h0 hL
        have htδ : δ₀ ≤ t - a := by
          by_contra hlt
          push Not at hlt
          have := hδ t ⟨by linarith [ha.1, ht.1], by linarith [ht.2]⟩ a
            ⟨ha₀.trans ha.1, by linarith [ha.2]⟩ (by
              rw [Real.dist_eq, abs_of_pos (by linarith [ht.1])]; exact hlt)
          rw [dist_eq_norm] at this
          linarith [hgr w r hg]
        have hIH := ih t ⟨by linarith [ha.1, ht.1], ht.2⟩ (by push_cast at hn; nlinarith)
        calc d' (P a) (P b₀) ≤ d' (P a) (P t) + d' (P t) (P b₀) := htri _ _ _
          _ ≤ ENNReal.ofReal (K * (t - a)) + ENNReal.ofReal (K * (b₀ - t) + Cs * ω) :=
            add_le_add hstep hIH
          _ ≤ ENNReal.ofReal (K * (b₀ - a) + Cs * ω) :=
            ofReal_add_le_of_le (mul_nonneg hK0 (by linarith [ht.1]))
              (add_nonneg (mul_nonneg hK0 (by linarith [ht.2])) (mul_nonneg hCs0 hω))
              (by linarith)
  obtain ⟨n, hn⟩ := exists_nat_ge ((b₀ - a₀) / δ₀)
  exact main n a₀ ⟨le_rfl, hab⟩ (by rwa [div_le_iff₀ hδ₀] at hn)

end Tele

section Pair

variable (D : ContMetric)

/-- **[3] Prop 3.6, Steps 4–6 for one pair `z, w`** (deterministic; generalizes the deterministic
part of `LQGMetric.GM.p36_pair` to an `ℝ≥0∞`-valued `d′` bounded by `C_s · D(·,·;V)` on `V`). Let
`z, w` have a unique `D`-geodesic, contained in `S ⊆ V`, with `|z − w| > 4e`. Suppose every
point of `S` lies in `B_{r/2}(v)` for a good ball, `r ∈ [r_min, e]`, where `Good v r` gives the
`D`-forms of conditions 1 (`hgood1`: `d′(u,u') ≤ C' D(u,u')` for `u ∈ ∂B_{αr}(v)`,
`u' ∈ ∂B_r(v)` whose `D`-geodesic is unique and stays in `cl A_{αr,r}(v)`) and 3 (`hgood3`: a
disconnecting path of `D`-length `≤ A · D(∂B_{αr}(v), ∂B_r(v))`). Suppose also `D(x,y) ≤ ω` for
`x, y ∈ S` with `|x − y| ≤ 4e`. Then
`d′(z,w) ≤ (C' + A/(A+1)(C_s − C')) D(z,w) + 3 C_s ω`.

`a₀` is the last time with `|P − z| ≤ 2e`, and `b₀` the first later time with `|P − w| ≤ 2e`
([3] (3.18), (3.19)). `tele_core_ext` runs on `[a₀, b₀]`. The three end pieces (`z → P(a₀)`, the
last incomplete step, `P(b₀) → w`) cost `≤ C_s ω` each; this replaces [3] (3.24). Sub-geodesics
of the unique geodesic are unique (`LQGMetric.GM.gm_S3_7`), which turns `hgood1` into the
comparison along `P`. -/
theorem p36_pair_ext {d' : ℂ → ℂ → ℝ≥0∞} (htri : ∀ x y z, d' x z ≤ d' x y + d' y z)
    (hex : ∀ a b : ℂ, ∃ η, D.IsGeod01 a b η)
    {α A Cs C' : ℝ} (hα : 1 / 2 < α) (hα1 : α < 1) (hA : 0 ≤ A) (hC0 : 0 ≤ C')
    (hCC : C' ≤ Cs) {V : Set ℂ}
    (hratio : ∀ x ∈ V, ∀ y ∈ V, d' x y ≤ ENNReal.ofReal Cs * D.internal V x y)
    {z w : ℂ} (hu : UniqueGeod D z w) {S : Set ℂ} (hSV : S ⊆ V) {e rmin ω : ℝ}
    (hrmin : 0 < rmin) (hzw : 4 * e < ‖z - w‖)
    (hconf : ∀ η, IsGeod01 D z w η → range η ⊆ S)
    (Good : ℂ → ℝ → Prop)
    (hgood1 : ∀ v r, Good v r → ∀ u ∈ sphere v (α * r), ∀ u' ∈ sphere v r,
      UniqueGeodIn D u u' (closure (annulus v (α * r) r : Set ℂ)) →
        d' u u' ≤ ENNReal.ofReal (C' * D.1 (u, u')))
    (hgood3 : ∀ v r, Good v r → ∃ (a' b' : ℝ) (G : ℝ → ℂ),
      Disconnects (G '' Icc a' b') (sphere v (α * r)) (sphere v r) ∧
      D.len G a' b' ≤ ENNReal.ofReal A * setDist D (sphere v (α * r)) (sphere v r))
    (hcov : ∀ x ∈ S, ∃ v r, (rmin ≤ r ∧ r ≤ e ∧ Good v r) ∧ x ∈ ball v (r / 2))
    (hmod : ∀ x ∈ S, ∀ y ∈ S, ‖x - y‖ ≤ 4 * e → D.1 (x, y) ≤ ω) :
    d' z w ≤ ENNReal.ofReal ((C' + A / (A + 1) * (Cs - C')) * D.1 (z, w) + 3 * Cs * ω) := by
  obtain ⟨η, hη, huη⟩ := hu
  have hu' : D.GeodUnique z w := fun a b ha hb => (huη a ha).trans (huη b hb).symm
  have hzw0 : z ≠ w := by
    intro h; rw [h, sub_self, norm_zero] at hzw
    have : 0 ≤ e := by
      by_contra hn; push Not at hn
      obtain ⟨v, r, ⟨h1, h2, -⟩, -⟩ := hcov z (hconf η hη ⟨0, hη.1⟩)
      linarith
    linarith
  set L := D.1 (z, w) with hL
  have hL0 : 0 < L := dist_pos_of_ne D hzw0
  set P : ℝ → ℂ := fun τ => η (pj (τ / L)) with hPdef
  have hP : ContinuousOn P (Icc 0 L) :=
    (η.continuous.comp (continuous_projIcc.comp (continuous_id.div_const L))).continuousOn
  have hpj : ∀ τ ∈ Icc 0 L, ((pj (τ / L) : unitInterval) : ℝ) = τ / L := fun τ hτ =>
    pj_coe_of_mem ⟨div_nonneg hτ.1 hL0.le, (div_le_one hL0).2 hτ.2⟩
  have hgeo : ∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L, D.1 (P s, P t) = |t - s| := by
    intro s hs t ht
    show D.1 (η (pj (s / L)), η (pj (t / L))) = _
    rw [hη.2.2, hpj s hs, hpj t ht, ← hL, ← sub_div, abs_div, abs_of_pos hL0,
      div_mul_cancel₀ _ hL0.ne']
  have hP0 : P 0 = z := by
    show η (pj (0 / L)) = z
    rw [zero_div, pj_eq_of_mem ⟨le_rfl, zero_le_one⟩]; exact hη.1
  have hPL : P L = w := by
    show η (pj (L / L)) = w
    rw [div_self hL0.ne', pj_eq_of_mem ⟨zero_le_one, le_rfl⟩]; exact hη.2.1
  have hPin : ∀ τ, P τ ∈ S := fun τ => hconf η hη ⟨_, rfl⟩
  have hPV : ∀ τ ∈ Icc 0 L, P τ ∈ V := fun τ _ => hSV (hPin τ)
  have he0 : 0 ≤ e := by
    obtain ⟨v, r, ⟨h1, h2, -⟩, -⟩ := hcov z (hP0 ▸ hPin 0)
    linarith
  have hω : 0 ≤ ω := by
    have := hmod z (hP0 ▸ hPin 0) z (hP0 ▸ hPin 0) (by rw [sub_self, norm_zero]; linarith)
    rwa [D.2.self_eq_zero] at this
  -- `a₀`: the last time with `|P − z| ≤ 2e` ([3] (3.18), `J̲`)
  set S₁ := Icc 0 L ∩ P ⁻¹' closedBall z (2 * e) with hS₁
  have hS₁c : IsClosed S₁ := hP.preimage_isClosed_of_isClosed isClosed_Icc isClosed_closedBall
  have h0S₁ : (0 : ℝ) ∈ S₁ := ⟨⟨le_rfl, hL0.le⟩, by
    show P 0 ∈ closedBall z (2 * e); rw [hP0]; exact mem_closedBall_self (by linarith)⟩
  have hS₁b : BddAbove S₁ := ⟨L, fun t ht => ht.1.2⟩
  set a₀ := sSup S₁ with ha₀
  have ha₀S : a₀ ∈ S₁ := hS₁c.csSup_mem ⟨0, h0S₁⟩ hS₁b
  have ha₀0 : 0 ≤ a₀ := ha₀S.1.1
  have hafter₁ : ∀ t ∈ Ioc a₀ L, 2 * e < ‖P t - z‖ := by
    intro t ht
    by_contra hn; push Not at hn
    exact absurd (le_csSup hS₁b ⟨⟨by linarith [ht.1], ht.2⟩, by
      rw [mem_preimage, mem_closedBall, dist_eq_norm]; exact hn⟩) (not_le.2 ht.1)
  have hPa₀z : ‖P a₀ - z‖ ≤ 2 * e := by
    have := ha₀S.2; rwa [mem_preimage, mem_closedBall, dist_eq_norm] at this
  have hPa₀w : 2 * e < ‖P a₀ - w‖ := by
    have := norm_sub_norm_le (z - w) (P a₀ - w)
    rw [sub_sub_sub_cancel_right] at this
    rw [norm_sub_rev z (P a₀)] at this
    linarith
  have ha₀L : a₀ < L := by
    rcases eq_or_lt_of_le ha₀S.1.2 with h | h
    · rw [h, hPL] at hPa₀w; rw [sub_self, norm_zero] at hPa₀w; linarith
    · exact h
  -- `b₀`: the first time after `a₀` with `|P − w| ≤ 2e` ([3] (3.18), `J̄`)
  set S₂ := Icc a₀ L ∩ P ⁻¹' closedBall w (2 * e) with hS₂
  have hS₂c : IsClosed S₂ := (hP.mono (Icc_subset_Icc ha₀0 le_rfl)).preimage_isClosed_of_isClosed
    isClosed_Icc isClosed_closedBall
  have hLS₂ : L ∈ S₂ := ⟨⟨ha₀L.le, le_rfl⟩, by
    show P L ∈ closedBall w (2 * e); rw [hPL]; exact mem_closedBall_self (by linarith)⟩
  have hS₂b : BddBelow S₂ := ⟨a₀, fun t ht => ht.1.1⟩
  set b₀ := sInf S₂ with hb₀
  have hb₀S : b₀ ∈ S₂ := hS₂c.csInf_mem ⟨L, hLS₂⟩ hS₂b
  have hb₀L : b₀ ≤ L := hb₀S.1.2
  have hPb₀w : ‖P b₀ - w‖ ≤ 2 * e := by
    have := hb₀S.2; rwa [mem_preimage, mem_closedBall, dist_eq_norm] at this
  have hab : a₀ < b₀ := by
    rcases eq_or_lt_of_le hb₀S.1.1 with h | h
    · rw [← h] at hPb₀w; linarith
    · exact h
  have hbefore₂ : ∀ t ∈ Ico a₀ b₀, 2 * e < ‖P t - w‖ := by
    intro t ht
    by_contra hn; push Not at hn
    exact absurd (csInf_le hS₂b ⟨⟨ht.1, by linarith [ht.2]⟩, by
      rw [mem_preimage, mem_closedBall, dist_eq_norm]; exact hn⟩) (not_le.2 ht.2)
  have hfz : ∀ a ∈ Icc a₀ b₀, 2 * e ≤ ‖P a - z‖ :=
    le_on_Icc_of_Ioo (g := fun t => ‖P t - z‖) hab
      ((hP.mono (Icc_subset_Icc ha₀0 hb₀L)).sub continuousOn_const).norm
      (fun t ht => (hafter₁ t ⟨ht.1, by linarith [ht.2]⟩).le)
  have hfw : ∀ a ∈ Icc a₀ b₀, 2 * e ≤ ‖P a - w‖ :=
    le_on_Icc_of_Ioo (g := fun t => ‖P t - w‖) hab
      ((hP.mono (Icc_subset_Icc ha₀0 hb₀L)).sub continuousOn_const).norm
      (fun t ht => (hbefore₂ t ⟨ht.1.le, ht.2⟩).le)
  -- the good balls with radius in `[r_min, e]`
  set Good' : ℂ → ℝ → Prop := fun v r => rmin ≤ r ∧ r ≤ e ∧ Good v r with hGood'
  have hfar1 : ∀ x : ℂ, ∀ a ∈ Icc a₀ b₀, ∀ v r, Good' v r → P a ∈ ball v (r / 2) →
      2 * e ≤ ‖P a - x‖ → x ∉ ball v r := by
    intro x a _ v r hg hPa hx hxv
    rw [mem_ball, dist_eq_norm] at hPa hxv
    have := norm_add_le (P a - v) (v - x)
    rw [sub_add_sub_cancel] at this
    rw [norm_sub_rev v x] at this
    linarith [hg.2.1]
  -- condition 1 along `P` (sub-geodesics of the unique geodesic are unique, GM.S3.7)
  have hcomp : ∀ v r, Good' v r → ∀ s t, 0 ≤ s → s ≤ t → t ≤ L → P s ∈ sphere v (α * r) →
      P t ∈ sphere v r → (∀ u ∈ Icc s t, P u ∈ closedBall v r ∧ P u ∉ ball v (α * r)) →
      d' (P s) (P t) ≤ ENNReal.ofReal (C' * (t - s)) := by
    intro v r hg s t hs hst htL hPs hPt hann
    have hr : 0 < r := hrmin.trans_le hg.1
    have hsI : s ∈ Icc 0 L := ⟨hs, hst.trans htL⟩
    have htI : t ∈ Icc 0 L := ⟨hs.trans hst, htL⟩
    have hle : pj (s / L) ≤ pj (t / L) :=
      monotone_projIcc _ (div_le_div_of_nonneg_right hst hL0.le)
    obtain ⟨hU, hR⟩ := gm_S3_7 hex hη hu' hle
    have hUG : UniqueGeodIn D (P s) (P t) (closure (annulus v (α * r) r : Set ℂ)) := by
      refine ⟨hU, fun γ hγ => (hR γ hγ).trans ?_⟩
      rintro _ ⟨x, ⟨hx1, hx2⟩, rfl⟩
      have hx1' : s / L ≤ (x : ℝ) := by rw [← hpj s hsI]; exact hx1
      have hx2' : (x : ℝ) ≤ t / L := by rw [← hpj t htI]; exact hx2
      have hu : (x : ℝ) * L ∈ Icc s t := by
        constructor
        · rwa [div_le_iff₀ hL0] at hx1'
        · rwa [le_div_iff₀ hL0] at hx2'
      have hxe : η x = P ((x : ℝ) * L) := by
        show η x = η (pj ((x : ℝ) * L / L))
        rw [mul_div_cancel_right₀ _ hL0.ne', pj_eq_of_mem x.2]
      obtain ⟨h1, h2⟩ := hann _ hu
      rw [hxe]
      rw [mem_closedBall, dist_eq_norm] at h1
      rw [mem_ball, dist_eq_norm, not_lt] at h2
      exact mem_closure_annulus_of (by nlinarith) (by nlinarith) h2 h1
    have := hgood1 v r hg.2.2 (P s) hPs (P t) hPt hUG
    rwa [hgeo s hsI t htI, abs_of_nonneg (sub_nonneg.2 hst)] at this
  -- the sum over `[a₀, b₀]` ([3] (3.23))
  have hK := tele_core_ext D htri hP hgeo hPV hα hα1 hA hC0 hCC hratio Good' hrmin
    (fun v r hg => hg.1) (fun v r hg => hgood3 v r hg.2.2) hcomp ha₀0 hab.le hb₀L hω
    (fun a _ => hcov (P a) (hPin a))
    (fun a ha v r hg hPa => ⟨by rw [hP0]; exact hfar1 z a ha v r hg hPa (hfz a ha),
      by rw [hPL]; exact hfar1 w a ha v r hg hPa (hfw a ha)⟩)
    (fun a ha v r hg hPa hPb => by
      have h1 := hgeo a ⟨ha₀0.trans ha.1, ha.2.trans hb₀L⟩ b₀ ⟨ha₀0.trans hab.le, hb₀L⟩
      rw [abs_of_nonneg (by linarith [ha.2])] at h1
      rw [← h1]
      refine hmod _ (hPin a) _ (hPin b₀) ?_
      rw [mem_ball, dist_eq_norm] at hPa hPb
      have := norm_add_le (P a - v) (v - P b₀)
      rw [sub_add_sub_cancel, norm_sub_rev v] at this
      linarith [hg.2.1])
  -- the two end pieces, through the current bound along `P`
  have hCs0 : 0 ≤ Cs := hC0.trans hCC
  have hend1 : d' z (P a₀) ≤ ENNReal.ofReal (Cs * ω) := by
    have h1 := le_ofReal_of_ratio_geod D hP hgeo hPV hCs0 hratio le_rfl ha₀0 ha₀L.le
    rw [hP0, sub_zero] at h1
    refine h1.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hCs0))
    have h2 := hgeo 0 ⟨le_rfl, hL0.le⟩ a₀ ⟨ha₀0, ha₀L.le⟩
    rw [sub_zero, abs_of_nonneg ha₀0, hP0] at h2
    rw [← h2]
    exact hmod _ (hP0 ▸ hPin 0) _ (hPin a₀) (by rw [norm_sub_rev]; linarith)
  have hend2 : d' (P b₀) w ≤ ENNReal.ofReal (Cs * ω) := by
    have h1 := le_ofReal_of_ratio_geod D hP hgeo hPV hCs0 hratio (ha₀0.trans hab.le) hb₀L le_rfl
    rw [hPL] at h1
    refine h1.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hCs0))
    have h2 := hgeo b₀ ⟨ha₀0.trans hab.le, hb₀L⟩ L ⟨hL0.le, le_rfl⟩
    rw [abs_of_nonneg (by linarith), hPL] at h2
    rw [← h2]
    exact hmod _ (hPin b₀) _ (hPL ▸ hPin L) (by linarith)
  set K := C' + A / (A + 1) * (Cs - C') with hKdef
  have hK0 : 0 ≤ K := by
    have : 0 ≤ A / (A + 1) := div_nonneg hA (by linarith)
    have : 0 ≤ A / (A + 1) * (Cs - C') := mul_nonneg this (sub_nonneg.2 hCC)
    linarith
  have hbl : K * (b₀ - a₀) ≤ K * L := mul_le_mul_of_nonneg_left (by linarith) hK0
  have hCω : 0 ≤ Cs * ω := mul_nonneg hCs0 hω
  calc d' z w ≤ d' z (P a₀) + d' (P a₀) w := htri _ _ _
    _ ≤ d' z (P a₀) + (d' (P a₀) (P b₀) + d' (P b₀) w) := add_le_add le_rfl (htri _ _ _)
    _ ≤ ENNReal.ofReal (Cs * ω) + (ENNReal.ofReal (K * (b₀ - a₀) + Cs * ω) +
          ENNReal.ofReal (Cs * ω)) := add_le_add hend1 (add_le_add hK hend2)
    _ ≤ ENNReal.ofReal (Cs * ω) + ENNReal.ofReal (K * (b₀ - a₀) + Cs * ω + Cs * ω) :=
      add_le_add le_rfl (ofReal_add_le_of_le
        (add_nonneg (mul_nonneg hK0 (by linarith)) hCω) hCω le_rfl)
    _ ≤ ENNReal.ofReal (K * L + 3 * Cs * ω) :=
      ofReal_add_le_of_le hCω (add_nonneg (add_nonneg (mul_nonneg hK0 (by linarith)) hCω) hCω)
        (by linarith)

/-- **The improvement step for one pair** ([3] (3.15), (3.22) with `C' = 1 + δ` and the current
bound `C_s = C`): the factor is `C_δ = 1 + δ + θ(C − 1 − δ)` with `θ = A/(A+1)`, the iteration of
`CC.ConfImprove`. -/
theorem p36_pair_ext_improve {d' : ℂ → ℂ → ℝ≥0∞} (htri : ∀ x y z, d' x z ≤ d' x y + d' y z)
    (hex : ∀ a b : ℂ, ∃ η, D.IsGeod01 a b η)
    {α A δ C : ℝ} (hα : 1 / 2 < α) (hα1 : α < 1) (hA : 0 ≤ A) (hδ : 0 ≤ δ) (hC : 1 + δ ≤ C)
    {V : Set ℂ} (hratio : ∀ x ∈ V, ∀ y ∈ V, d' x y ≤ ENNReal.ofReal C * D.internal V x y)
    {z w : ℂ} (hu : UniqueGeod D z w) {S : Set ℂ} (hSV : S ⊆ V) {e rmin ω : ℝ}
    (hrmin : 0 < rmin) (hzw : 4 * e < ‖z - w‖)
    (hconf : ∀ η, IsGeod01 D z w η → range η ⊆ S)
    (Good : ℂ → ℝ → Prop)
    (hgood1 : ∀ v r, Good v r → ∀ u ∈ sphere v (α * r), ∀ u' ∈ sphere v r,
      UniqueGeodIn D u u' (closure (annulus v (α * r) r : Set ℂ)) →
        d' u u' ≤ ENNReal.ofReal ((1 + δ) * D.1 (u, u')))
    (hgood3 : ∀ v r, Good v r → ∃ (a' b' : ℝ) (G : ℝ → ℂ),
      Disconnects (G '' Icc a' b') (sphere v (α * r)) (sphere v r) ∧
      D.len G a' b' ≤ ENNReal.ofReal A * setDist D (sphere v (α * r)) (sphere v r))
    (hcov : ∀ x ∈ S, ∃ v r, (rmin ≤ r ∧ r ≤ e ∧ Good v r) ∧ x ∈ ball v (r / 2))
    (hmod : ∀ x ∈ S, ∀ y ∈ S, ‖x - y‖ ≤ 4 * e → D.1 (x, y) ≤ ω) :
    d' z w ≤ ENNReal.ofReal ((1 + δ + A / (A + 1) * (C - 1 - δ)) * D.1 (z, w) + 3 * C * ω) := by
  have h := p36_pair_ext D htri hex hα hα1 hA (by linarith : (0 : ℝ) ≤ 1 + δ) hC hratio hu hSV
    hrmin hzw hconf Good hgood1 hgood3 hcov hmod
  have e : 1 + δ + A / (A + 1) * (C - (1 + δ)) = 1 + δ + A / (A + 1) * (C - 1 - δ) := by ring
  rwa [e] at h

end Pair

end SmallGammaGeodesics.CC
