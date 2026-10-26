import HigherDimLFPPAS.Localize.Conv
import HigherDimLFPPAS.Bridge.Geodesic
import HigherDimLQGMetric.Weak.DetWeylChain

/-!
# Lemma 2.4, second assertion: confinement and existence of `M_ε`-geodesics

Packet L24; planning audit MA1 §2.7 and Details A6.3 (`source/…txt` l. 263–287); unit speed as in MA2
Details (c), note 2.

* `dist_eq_of_isGeodesicCurve_of_hasUnitSpeedOn`: a unit-speed geodesic `P` on `[0, L]` has
  `G(P s, P t) = |t − s|` for all `s, t ∈ [0, L]`.
* `dist_le_of_isGeodesicCurve`: along a geodesic from `x` to `y`, `G(x, γ t) ≤ G(x, y)`.
* `fieldLfppMetric_confine` (deterministic core): if `G = D^φ` has `G < 2T` on `F × F` and `G ≥ 9T` from
  `F` to the sphere `S_R ⊃` boundary of a ball containing `F`, then every pair of `F` has a unit-speed
  `G`-geodesic (packet D5's `Bridge.fieldLfppMetric_exists_geodesic_of_barrier`) and every `G`-geodesic
  between points of `F` stays in `B_R` (`dfl71_le_infEDist_compl_ball`).
* `exists_diam_bound`, `exists_exit_radius`: deterministic `T₀` and `R` from the laws of `diam(F; D)` and
  `D(F, S_R)` (outer probability `≤ η` of the bad events; the events are preimages of open subsets of
  `C(ℝ^d × ℝ^d, ℝ)` under the measurable `ω ↦ D_{h(ω)}`, and properness of `D` (Lemma 2.2)).
* `lemma24Confine_of_conv`: the interface `Core.Lemma24Confine` from `Core.Setting` and
  `Core.Lemma24Conv`.
* `lemma24_holds`: both interfaces from `Core.Setting` and `Core.Lemma23i` (packet target).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLFPPAS.Localize

open HigherDimLQGMetric
open HigherDimLFPP (Rd)
open LQGMetric.MetricGeometry

variable {d : ℕ}

/-! ## Geodesics: deterministic facts -/

/-- A unit-speed geodesic on `[0, L]` realizes `G(P s, P t) = |t − s|` for all `s, t ∈ [0, L]`. -/
theorem dist_eq_of_isGeodesicCurve_of_hasUnitSpeedOn (G : ContMetric d) {P : ℝ → Rd d} {L : ℝ}
    (hgeo : IsGeodesicCurve (G.pt ∘ P) 0 L) (hu : HasUnitSpeedOn (G.pt ∘ P) (Icc 0 L)) :
    ∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L, G.1 (P s, P t) = |t - s| := by
  have key : ∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L, s ≤ t → G.1 (P s, P t) = t - s := by
    intro s hs t ht hst
    have hlen : curveLength (G.pt ∘ P) s t = edist (G.pt (P s)) (G.pt (P t)) :=
      curveLength_eq_edist_of_subinterval hgeo.2.2 (edist_ne_top _ _) hs.1 hst ht.2
    have hvar := hu hs ht
    rw [Icc_inter_Icc, max_eq_right hs.1, min_eq_right ht.2, NNReal.coe_one, one_mul] at hvar
    have hE : ENNReal.ofReal (G.1 (P s, P t)) = ENNReal.ofReal (t - s) := by
      rw [← G.edist_pt, ← hlen]
      exact hvar
    exact (ENNReal.ofReal_eq_ofReal_iff (G.nonneg _ _) (sub_nonneg.2 hst)).1 hE
  intro s hs t ht
  rcases le_total s t with hst | hts
  · rw [key s hs t ht hst, abs_of_nonneg (sub_nonneg.2 hst)]
  · rw [G.apply_comm, key t ht s hs hts, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hts)]

/-- Along a geodesic, the distance from the starting point is at most the distance between the
endpoints. -/
theorem dist_le_of_isGeodesicCurve (G : ContMetric d) {γ : ℝ → Rd d} {T : ℝ}
    (hgeo : IsGeodesicCurve (G.pt ∘ γ) 0 T) {t : ℝ} (ht : t ∈ Icc 0 T) :
    G.1 (γ 0, γ t) ≤ G.1 (γ 0, γ T) := by
  have h1 : ENNReal.ofReal (G.1 (γ 0, γ t)) ≤ ENNReal.ofReal (G.1 (γ 0, γ T)) := by
    rw [← G.edist_pt, ← G.edist_pt]
    calc edist (G.pt (γ 0)) (G.pt (γ t)) ≤ curveLength (G.pt ∘ γ) 0 t :=
          edist_le_curveLength (G.pt ∘ γ) ht.1
      _ ≤ curveLength (G.pt ∘ γ) 0 T := curveLength_mono (G.pt ∘ γ) le_rfl ht.2
      _ = edist (G.pt (γ 0)) (G.pt (γ T)) := hgeo.2.2
  exact (ENNReal.ofReal_le_ofReal_iff (G.nonneg _ _)).1 h1

/-- **Deterministic confinement** (MA1 A6.3): if the LFPP metric `G = D^φ` satisfies `G < 2T` on `F × F`
and `G ≥ 9T` from `F` to the sphere `S_R`, where `F ⊆ B_R`, then every pair of `F` is joined by a
unit-speed `G`-geodesic and every `G`-geodesic between two points of `F` stays in `B_R`. -/
theorem fieldLfppMetric_confine {ξ : ℝ} (hξ : 0 < ξ) (φ : C(Rd d, ℝ)) {F : Set (Rd d)} {R T : ℝ}
    (hT : 0 < T) (hFR : F ⊆ ball (0 : Rd d) R)
    (hpair : ∀ x ∈ F, ∀ y ∈ F, (fieldLfppMetric ξ φ).1 (x, y) < 2 * T)
    (hexit : ∀ x ∈ F, ∀ z ∈ sphere (0 : Rd d) R, 9 * T ≤ (fieldLfppMetric ξ φ).1 (x, z)) :
    ∀ x ∈ F, ∀ y ∈ F,
      (∃ (γ : ℝ → Rd d) (T' : ℝ), 0 ≤ T' ∧ γ 0 = x ∧ γ T' = y ∧ ContinuousOn γ (Icc 0 T') ∧
          ∀ s ∈ Icc 0 T', ∀ t ∈ Icc 0 T', (fieldLfppMetric ξ φ).1 (γ s, γ t) = |t - s|) ∧
        ∀ (γ : ℝ → Rd d) (T' : ℝ), γ 0 = x → γ T' = y →
          IsGeodesicCurve ((fieldLfppMetric ξ φ).pt ∘ γ) 0 T' → MapsTo γ (Icc 0 T') (ball 0 R) := by
  set G := fieldLfppMetric ξ φ with hGdef
  intro x hx y hy
  have hxR : x ∈ ball (0 : Rd d) R := hFR hx
  have hyR : y ∈ ball (0 : Rd d) R := hFR hy
  have hxn : ‖x‖ < R := by simpa using hxR
  have hyn : ‖y‖ < R := by simpa using hyR
  have hR : 0 < R := lt_of_le_of_lt (norm_nonneg x) hxn
  refine ⟨?_, ?_⟩
  · -- existence (packet D5's barrier geodesic)
    have hbarrier : ∀ {P : ℝ → Rd d} {a b : ℝ}, a ≤ b → ContinuousOn P (Icc a b) → P a = x →
        ‖P b‖ = R → ENNReal.ofReal (G.1 (x, y) + T) < G.len P a b := by
      intro P a b hab _ hPa hPb
      have hlen := G.ofReal_le_len P hab
      rw [hPa] at hlen
      have hsph : P b ∈ sphere (0 : Rd d) R := by simpa using hPb
      have h9 := hexit x hx (P b) hsph
      have hlt : G.1 (x, y) + T < 9 * T := by linarith [hpair x hx y hy]
      calc ENNReal.ofReal (G.1 (x, y) + T) < ENNReal.ofReal (9 * T) :=
            (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 hlt
        _ ≤ ENNReal.ofReal (G.1 (x, P b)) := ENNReal.ofReal_le_ofReal h9
        _ ≤ G.len P a b := hlen
    obtain ⟨P, hP0, hPL, hgeo, hu, -⟩ :=
      Bridge.fieldLfppMetric_exists_geodesic_of_barrier hR hξ hT φ x y hxn hyn hbarrier
    refine ⟨P, G.1 (x, y), G.nonneg x y, hP0, hPL, ?_, ?_⟩
    · exact (G.continuousOn_unpt_comp_iff (P := G.pt ∘ P)).2 hgeo.2.1
    · exact dist_eq_of_isGeodesicCurve_of_hasUnitSpeedOn G hgeo hu
  · -- confinement of every geodesic
    intro γ T' hγ0 hγT hgeo t ht
    have hle := dist_le_of_isGeodesicCurve G hgeo ht
    rw [hγ0, hγT] at hle
    have hlt : G.1 (x, γ t) < 9 * T := by linarith [hpair x hx y hy]
    by_contra hnot
    have hbar := dfl71_le_infEDist_compl_ball (fieldLfppMetric_isLength ξ φ) hxR (hexit x hx)
    have hmem : G.pt (γ t) ∈ G.pt '' (ball (0 : Rd d) R)ᶜ := ⟨γ t, hnot, rfl⟩
    have h1 : ENNReal.ofReal (9 * T) ≤ ENNReal.ofReal (G.1 (x, γ t)) := by
      rw [← G.edist_pt]
      exact hbar.trans (infEDist_le_edist_of_mem hmem)
    have h2 := (ENNReal.ofReal_le_ofReal_iff (G.nonneg _ _)).1 h1
    linarith

end HigherDimLFPPAS.Localize
