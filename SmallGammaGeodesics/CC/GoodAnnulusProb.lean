import SmallGammaGeodesics.CC.GoodAnnulusProbDet
import SmallGammaGeodesics.CC.GoodAnnulusMeas
import SmallGammaGeodesics.Core.GoodAnnulusInput
import SmallGammaGeodesics.Core.GMInputs
import LQGMetric.Papers.GM.S2.TightC

/-!
# [3] Lemma 3.9 and the good-annulus input `GoodAnnulusInput` (track CC, packet CC9b)

Source: Gwynne–Miller arXiv:1905.00384 ([3]), Lemmas 3.8–3.10, in the corrected form of
`planning/audits/CC0-conformal-covariance-plan.md`, Details (a) **D14** (and **D10** for [3]
Lemma 2.2); ruling G29 (the interface `CC.GoodAnnulusInput`, `Core/GoodAnnulusInput.lean`) and
ruling G31 (the activated event family).

**`goodAnnulusInput_holds`**: `0 < γ → γ < 2 → IsCanonicalLQGMetric γ D → ConfSmallScale γ D →
GoodAnnulusInput γ D`. For `p < 1` put `p₁ = max p 0` and `ε = (1 − p₁)/6`. The constants are
chosen from `p` alone, in this order (all GM S2 tightness bounds hold uniformly in the field, the
scale and the centre; `D` is weak with `𝔠_r = r^{ξQ}` by `GM.gm_eq1_15`):
1. `s` (`GM.Tight.gm_S2_4a`, scale `r`): `D_h(u,y) > s𝔰_r(z)` for `u` in the closed ring
   `{3r/4 ≤ |u−z| ≤ r}` and `y` in the collar of `∂𝔸_{r/2,2r}(z)`;
2. `S` (`GM.Tight.gm_S2_4c`, scale `r`): internal diameter of that ring in `𝔸` at most `S𝔰_r(z)`;
3. `α₀` (GM Lemma 2.11 on the closed annulus, `GMInputs.l2_11c_holds`, with `(s/2, S+s)`), and
   `α = max α₀ (3/4) ∈ [3/4, 1)`: condition 2;
4. `t` (`GM.Tight.gm_S2_4a_sep`, scale `3r`, separation `(1−α)/3`): [3] Lemma 2.2 in ratio form;
5. `A` (CC9a's `exists_gaAroundI_prob`): condition 3.
For a conformal neighbourhood `(ϕ, W, V)`, `δ > 0` and a compact `K ⊆ V`: `ConfSmallScale` with
`δ' = min (st/(4S)) (δt)` and failure `ε` gives `r₁`, and `r₀ = min (r₁/3) (κ/2)` with
`cthickening κ K ⊆ V`. The event is CC9a's `confGoodEvent D ϕ α A (1+δ) act h h̄ f` with
`act w r := w ∈ K ∧ r ≤ r₀`; then
* annulus-locality is CC9a's `isAnnulusLocal_confGoodEvent_cc7` ([3] Lemma 3.8);
* `P[E_r(z)] ≥ p` is the union bound `ofReal_le_measure_of_six` over the six bad events above
  (with `ConfSmallScale` at scale `3r`) and the null event where `D_h` is not a proper length
  metric; the deterministic core is `confGoodAnnulus_of_bounds` (`CC/GoodAnnulusProbDet.lean`);
* the D-forms of conditions 1 and 3 are CC9a's `ae_hgood_confGoodEvent`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Metric Topology
open scoped ENNReal

namespace SmallGammaGeodesics.CC

open LQGMetric LQGMetric.Blueprint

/-- **union bound** for six bad events and an almost sure property: if `G` holds outside the six
events on the a.s. property, each of (outer) probability `≤ ε`, and `6ε ≤ 1 − p`, then
`P(G) ≥ p`. No measurability is needed. -/
lemma ofReal_le_measure_of_six {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {G B₁ B₂ B₃ B₄ B₅ B₆ : Set Ω} {Q : Ω → Prop}
    (hQ : ∀ᵐ ω ∂P, Q ω) {p ε : ℝ} (hp : p ≤ 1) (hε : 0 ≤ ε) (hpε : 6 * ε ≤ 1 - p)
    (h₁ : P B₁ ≤ ENNReal.ofReal ε) (h₂ : P B₂ ≤ ENNReal.ofReal ε)
    (h₃ : P B₃ ≤ ENNReal.ofReal ε) (h₄ : P B₄ ≤ ENNReal.ofReal ε)
    (h₅ : P B₅ ≤ ENNReal.ofReal ε) (h₆ : P B₆ ≤ ENNReal.ofReal ε)
    (hsub : ∀ ω, Q ω → ω ∉ B₁ → ω ∉ B₂ → ω ∉ B₃ → ω ∉ B₄ → ω ∉ B₅ → ω ∉ B₆ → ω ∈ G) :
    ENNReal.ofReal p ≤ P G := by
  have hN : P {ω | ¬ Q ω} = 0 := ae_iff.1 hQ
  have hc : Gᶜ ⊆ B₁ ∪ B₂ ∪ B₃ ∪ B₄ ∪ B₅ ∪ B₆ ∪ {ω | ¬ Q ω} := by
    intro ω hω
    by_contra hcon
    simp only [mem_union, mem_ofPred_eq, not_or, not_not] at hcon
    obtain ⟨⟨⟨⟨⟨⟨n₁, n₂⟩, n₃⟩, n₄⟩, n₅⟩, n₆⟩, hq⟩ := hcon
    exact hω (hsub ω hq n₁ n₂ n₃ n₄ n₅ n₆)
  refine ofReal_le_measure_of_compl_le hp ?_
  calc P Gᶜ ≤ P (B₁ ∪ B₂ ∪ B₃ ∪ B₄ ∪ B₅ ∪ B₆ ∪ {ω | ¬ Q ω}) := measure_mono hc
    _ ≤ P B₁ + P B₂ + P B₃ + P B₄ + P B₅ + P B₆ + P {ω | ¬ Q ω} := by
        refine (measure_union_le _ _).trans ?_
        gcongr
        refine (measure_union_le _ _).trans ?_
        gcongr
        refine (measure_union_le _ _).trans ?_
        gcongr
        refine (measure_union_le _ _).trans ?_
        gcongr
        refine (measure_union_le _ _).trans ?_
        gcongr
        exact measure_union_le _ _
    _ ≤ ENNReal.ofReal ε + ENNReal.ofReal ε + ENNReal.ofReal ε + ENNReal.ofReal ε +
          ENNReal.ofReal ε + ENNReal.ofReal ε + 0 := by
        rw [hN]
        gcongr
    _ = ENNReal.ofReal (6 * ε) := by
        rw [add_zero, ← ENNReal.ofReal_add hε hε, ← ENNReal.ofReal_add (by linarith) hε,
          ← ENNReal.ofReal_add (by linarith) hε, ← ENNReal.ofReal_add (by linarith) hε,
          ← ENNReal.ofReal_add (by linarith) hε]
        congr 1
        ring
    _ ≤ ENNReal.ofReal (1 - p) := ENNReal.ofReal_le_ofReal hpε

/-- **The good-annulus input** ([3] Lemmas 3.8–3.10 in the form [3] Prop 3.6 consumes; ruling G29;
CC0 D14, D10). `α ∈ [3/4, 1)` and `A > 1` depend only on `p` (and `γ`, `D`); `r₀` depends on the
map, `δ` and `K` through `ConfSmallScale` and the distance from `K` to `∂V`. -/
theorem goodAnnulusInput_holds {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {D : DistC → ContMetric}
    (hD : GaussianLQG.IsCanonicalLQGMetric γ D) (hS : ConfSmallScale γ D) :
    GoodAnnulusInput γ D := by
  intro p hp
  -- the failure budget `ε = (1 − p₁)/6`, `p₁ = max p 0`
  set p₁ : ℝ := max p 0
  have hp₁ : p₁ < 1 := max_lt hp one_pos
  have hp₁0 : 0 ≤ p₁ := le_max_right p 0
  set ε : ℝ := (1 - p₁) / 6 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  have hε1 : ε < 1 := by rw [hεdef]; linarith
  have hεe : (0 : ℝ≥0∞) < ENNReal.ofReal ε := ENNReal.ofReal_pos.2 hε
  have hW := GM.gm_eq1_15 hγ hD.1
  -- condition 2: crossing bound and internal diameter at scale `r`, GM Lemma 2.11 (closed)
  obtain ⟨s, hs, H1⟩ := GM.Tight.gm_S2_4a hW (isCompact_closedRing (3 / 4) 1)
    isCompact_annulusCollar disjoint_closedRing_annulusCollar hεe
  obtain ⟨S, hS0, H2⟩ := GM.Tight.gm_S2_4c hW (annulus (0 : ℂ) (1 / 2) 2).isOpen
    isConnected_annulus_half_two (GM.Bilip.isBounded_annulus_zero _ _)
    (isCompact_closedRing (3 / 4) 1) closedRing_subset_annulus hεe
  obtain ⟨α₀, -, hα₀1, H3⟩ := GMInputs.l2_11c_holds hγ hγ2 hW (s := s / 2) (S := S + s)
    (by linarith) (by linarith) (p := 1 - ε) (by linarith) (by linarith)
  set α : ℝ := max α₀ (3 / 4)
  have hα34 : 3 / 4 ≤ α := le_max_right _ _
  have hαα₀ : α₀ ≤ α := le_max_left _ _
  have hα1 : α < 1 := max_lt hα₀1 (by norm_num)
  have hα : 1 / 2 < α := by linarith
  -- condition 1: separated points at scale `3r` ([3] Lemma 2.2, ratio form)
  obtain ⟨t, ht, H7⟩ := GM.Tight.gm_S2_4a_sep hW (isCompact_closedBall (0 : ℂ) (1 / 3))
    (b := (1 - α) / 3) (by linarith) hεe
  -- condition 3
  obtain ⟨A, hA, H8⟩ := exists_gaAroundI_prob hγ hD.1 hα hα1 hεe
  refine ⟨α, A, hα, hα1, by linarith, ?_⟩
  intro ϕ W V hϕ δ hδ K hK hKV
  -- [3] Prop 2.1 at scale `3r`, with error `δ' 𝔰_{3r}(z)`
  set δ' : ℝ := min (s * t / (4 * S)) (δ * t)
  have hδ' : 0 < δ' := lt_min (div_pos (mul_pos hs ht) (by linarith)) (mul_pos hδ ht)
  obtain ⟨r₁, hr₁, H6⟩ := hS ϕ W V hϕ K hK hKV δ' hδ' ε hε
  obtain ⟨κ, hκ, hκV⟩ := hK.exists_cthickening_subset_open hϕ.isOpen_V hKV
  refine ⟨min (r₁ / 3) (κ / 2), lt_min (by linarith) (by linarith), ?_⟩
  intro Ω _ P _ h hbar f hh hhb hf hc
  set act : ℂ → ℝ → Prop := fun w r => w ∈ K ∧ r ≤ min (r₁ / 3) (κ / 2)
  have hact : ∀ w r, 0 < r → act w r → (annulus w (r / 2) (2 * r) : Set ℂ) ⊆ V := by
    rintro w r hr ⟨hw, hrr⟩ x hx
    refine hκV (closedBall_subset_cthickening hw κ ?_)
    rw [mem_closedBall, dist_eq_norm]
    have hx' : r / 2 < ‖x - w‖ ∧ ‖x - w‖ < 2 * r := hx
    have : r ≤ κ / 2 := hrr.trans (min_le_right _ _)
    linarith [hx'.2]
  refine ⟨confGoodEvent D ϕ α A (1 + δ) act h hbar f, ?_, ?_, ?_⟩
  · -- 1. annulus-locality ([3] Lemma 3.8; CC9a)
    intro z _ r hr
    exact isAnnulusLocal_confGoodEvent_cc7 hγ hγ2 hD.1 hϕ hh hhb hf hc hα hα1 A (1 + δ) hact z r
      hr.1
  · -- 2. the probability bound ([3] Lemma 3.9)
    intro z hz r hr
    have hr0 : 0 < r := hr.1
    have h3r : 0 < 3 * r := by linarith
    have hr₁' : 3 * r ≤ r₁ := by
      have := hr.2.trans (min_le_left _ _)
      linarith
    have hUV := hact z r hr0 ⟨hz, hr.2⟩
    rw [confGoodEvent_of_act (show act z r from ⟨hz, hr.2⟩)]
    refine (ENNReal.ofReal_le_ofReal (le_max_left p 0)).trans ?_
    refine ofReal_le_measure_of_six ((hD.1.length P h (isGFFPlusCont_of_wp hh)).and
        (GM.gm_S1_1_bcpt dfgpsLem3_8_holds hγ hγ2 hW P h hh)) hp₁.le hε.le
      (by rw [hεdef]; linarith)
      (H1 P h hh r hr0 z).le (H2 P h hh r hr0 z).le
      ((H3 α ⟨hαα₀, hα1⟩ z r hr0 P h hh).trans_eq (by rw [sub_sub_cancel]))
      (H6 P h hbar f hh hhb hf hc z hz (3 * r) ⟨h3r, hr₁'⟩)
      (H7 P h hh (3 * r) h3r z).le (H8 P h hh r hr0 z).le ?_
    rintro ω ⟨hL, hb⟩ n1 n2 n3 n6 n7 n8
    simp only [mem_ofPred_eq, mem_compl_iff, not_not] at n1 n2 n3 n6 n7 n8
    have := GM.properSpace_of_bcpt (D (h ω)) hb
    rw [image_affine_annulus hr0 z] at n2
    refine confGoodAnnulus_of_bounds hL hϕ
      (σ := r ^ (xiGamma γ * Q γ) * Real.exp (xiGamma γ * circleAvg (h ω) r z))
      (σ₃ := (3 * r) ^ (xiGamma γ * Q γ) * Real.exp (xiGamma γ * circleAvg (h ω) (3 * r) z))
      hα34 hα1 hr0 hs hS0 (mul_pos (Real.rpow_pos_of_pos hr0 _) (Real.exp_pos _))
      (mul_pos (Real.rpow_pos_of_pos h3r _) (Real.exp_pos _)) hδ.le hδ'.le
      (min_le_left _ _) (min_le_right _ _) hUV ?_ ?_ n3 ?_ ?_ n8
    · intro u hu v hv
      simpa only [mul_assoc] using n1 u hu v hv
    · intro u hu v hv
      simpa only [mul_assoc] using n2 u hu v hv
    · intro u hu v hv
      simpa only [mul_assoc] using n6 u hu v hv
    · intro u hu v hv huv
      simpa only [mul_assoc] using n7 u hu v hv huv
  · -- 3. the D-forms of conditions 1 and 3 (CC9a)
    filter_upwards [ae_hgood_confGoodEvent (C' := 1 + δ) (A := A) hγ hγ2 hD.1 hϕ hh hhb hf hα
      hα1 hact] with ω hω
    intro z hz r hr hE
    exact ⟨hω.1 z r ⟨hr.1, ⟨hz, hr.2⟩, hE⟩, hω.2 z r ⟨hr.1, ⟨hz, hr.2⟩, hE⟩⟩

end SmallGammaGeodesics.CC
