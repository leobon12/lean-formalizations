import HigherDimLQGMetric.Sec8.Lemma82
import HigherDimLQGMetric.Proper.Proper

/-!
# Geodesics used by the Section 8 selector

The selector's endpoint and scalar-invariance properties require an actual
geodesic. This file converts the proper-length-space geodesic to the
constant-speed path on the unit interval expected by the selector.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Set Topology Metric unitInterval
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- A proper continuous length metric has a constant-speed geodesic on the
unit interval between any two points. -/
theorem sec8_exists_constSpeedGeod (D : ContMetric d) (hD : D.IsLength)
    [ProperSpace D.Space] (x y : Rd d) :
    ∃ η : C(unitInterval, Rd d), IsConstSpeedGeod D x y η := by
  obtain ⟨P, h0, h1, hgeo, -, hdist⟩ := D.exists_geodesic hD x y
  let L : ℝ := D.1 (x, y)
  let tval : unitInterval → ℝ := fun t => (t : ℝ) * L
  have hL : 0 ≤ L := by
    dsimp [L]
    rw [← D.dist_pt]
    exact dist_nonneg
  have htmap : MapsTo tval univ (Icc 0 L) := by
    intro t _
    have ht0 : (0 : ℝ) ≤ t := t.property.1
    have ht1 : (t : ℝ) ≤ 1 := t.property.2
    constructor <;> dsimp [tval] <;> nlinarith
  have htcont : Continuous tval := by
    dsimp [tval]
    fun_prop
  have hPcont : ContinuousOn P (Icc 0 L) :=
    D.continuousOn_pt_comp_iff.mp hgeo.2.1
  let η : C(unitInterval, Rd d) :=
    ⟨fun t => P (tval t), hPcont.comp_continuous htcont (fun t => htmap trivial)⟩
  refine ⟨η, ?_⟩
  change η 0 = x ∧ η 1 = y ∧ ∀ s t : unitInterval,
    D.1 (η s, η t) = |(s : ℝ) - t| * D.1 (x, y)
  refine ⟨?_, ?_, ?_⟩
  · simpa [η, tval] using h0
  · simpa [η, tval, L] using h1
  · intro s t
    have hs : tval s ∈ Icc 0 L := htmap trivial
    have ht : tval t ∈ Icc 0 L := htmap trivial
    have h := hdist (tval s) hs (tval t) ht
    change D.1 (P (tval s), P (tval t)) = |tval t - tval s| at h
    change D.1 (P (tval s), P (tval t)) = _
    rw [h]
    dsimp [tval, L]
    rw [← sub_mul, abs_mul, abs_of_nonneg hL]
    rw [abs_sub_comm]

/-- The Borel geodesic selector has the correct endpoints whenever the
metric is proper and a length metric. -/
theorem sec8Sel_endpoints (D : ContMetric d) (hD : D.IsLength)
    [ProperSpace D.Space] (x y : Rd d) :
    sec8Sel x y D.1 0 = x ∧ sec8Sel x y D.1 1 = y := by
  have h := (exists_measurable_geodSelector x y).choose_spec.2 D
    (sec8_exists_constSpeedGeod D hD x y)
  exact ⟨h.1.1, h.1.2.1⟩

/-- A uniform positive lower comparison transfers properness of continuous
metrics on Euclidean space. -/
theorem sec8_proper_of_metric_lower (D E : ContMetric d) [ProperSpace D.Space]
    {c : ℝ} (hc : 0 < c)
    (hDE : ∀ u v : Rd d, c * D.1 (u, v) ≤ E.1 (u, v)) :
    ProperSpace E.Space := by
  refine ProperSpace.of_isCompact_closedBall_of_le 0 ?_
  intro x R hR
  let K : Set (Rd d) :=
    D.unpt '' closedBall (D.pt (E.unpt x)) (R / c)
  have hK : IsCompact K :=
    (isCompact_closedBall (D.pt (E.unpt x)) (R / c)).image D.continuous_unpt
  have hEK : IsCompact (E.pt '' K) := hK.image E.continuous_pt
  refine hEK.of_isClosed_subset isClosed_closedBall ?_
  intro y hy
  have hE : E.1 (E.unpt x, E.unpt y) ≤ R := by
    simpa only [Metric.mem_closedBall, ← E.dist_pt, E.pt_unpt, dist_comm] using hy
  have hD : D.1 (E.unpt x, E.unpt y) ≤ R / c :=
    (le_div_iff₀ hc).2 (by rw [mul_comm]; exact (hDE _ _).trans hE)
  have hDball : D.pt (E.unpt y) ∈ closedBall (D.pt (E.unpt x)) (R / c) := by
    change dist (D.pt (E.unpt y)) (D.pt (E.unpt x)) ≤ R / c
    rw [dist_comm, D.dist_pt]
    exact hD
  exact ⟨E.unpt y, ⟨D.pt (E.unpt y), hDball, rfl⟩, E.pt_unpt y⟩

/-- A globally bounded Weyl perturbation of a proper length metric remains
proper. -/
theorem sec8_proper_of_bounded_weyl (D E : ContMetric d)
    (hD : D.IsLength) [ProperSpace D.Space]
    (ξ : ℝ) (f : C(Rd d, ℝ))
    (hW : IsWeylOf ξ f D E)
    {a b : ℝ} (ha : ∀ x, a ≤ ξ * f x)
    (hb : ∀ x, ξ * f x ≤ b) : ProperSpace E.Space := by
  apply sec8_proper_of_metric_lower D E (Real.exp_pos a)
  intro u v
  have hbound := (weylScale_mem_Icc_of_isLength (D := D) (ξ := ξ) (f := f)
    (z := u) (w := v) hD ha hb).1
  rw [← hW u v] at hbound
  exact (ENNReal.ofReal_le_ofReal_iff (E.nonneg u v)).mp hbound

/-- The selected geodesic after subtracting finitely many bounded bumps has
the intended endpoints on a common almost-sure event. -/
theorem lemma82_shifted_geod_exists {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistRd d)
    (hd : 3 ≤ d) (hh : IsWholeSpaceLGF h P)
    {ξ Q : ℝ} (hξ : 0 < ξ) (hQ : Real.sqrt (2 * d) < Q)
    {D : DistRd d → ContMetric d} (hD : IsSharpWeakExpMetric d ξ Q D)
    {f : ℕ → C(Rd d, ℝ)} {J : ℕ} {Mf : ℝ}
    (hf : ∀ j < J, (∀ x, 0 ≤ f j x) ∧ (∀ x, f j x ≤ Mf))
    (r : ℝ) {Z : Finset (Rd d × ℕ)} (hJ : ∀ q ∈ Z, q.2 < J)
    (x y : Rd d) :
    ∀ᵐ ω ∂P, ∃ η : C(unitInterval, Rd d),
      IsConstSpeedGeod (D (addFun (h ω) (-F_Z f r Z))) x y η := by
  have hshift : IsLGFPlusCont
      (fun ω => addFun (h ω) (-F_Z f r Z)) P :=
    hh.isLGFPlusCont.addFun measurable_const
  filter_upwards [hD.length P h hh.isLGFPlusCont,
    hD.length P (fun ω => addFun (h ω) (-F_Z f r Z)) hshift,
    lemma27_proper hd hξ hQ hD P h hh,
    hD.weyl P h hh.isLGFPlusCont] with ω hlen hlenShift hproper hweyl
  letI : ProperSpace (D (h ω)).Space := hproper
  have hW : IsWeylOf ξ (-F_Z f r Z) (D (h ω))
      (D (addFun (h ω) (-F_Z f r Z))) := by
    intro u v
    exact (hweyl (-F_Z f r Z) u v).symm
  have ha : ∀ u : Rd d, -(ξ * (Z.card * Mf)) ≤ ξ * (-F_Z f r Z) u := by
    intro u
    have hu := (F_Z_nonneg_le hf r hJ u).2
    simp only [ContinuousMap.neg_apply]
    nlinarith [mul_le_mul_of_nonneg_left hu hξ.le]
  have hb : ∀ u : Rd d, ξ * (-F_Z f r Z) u ≤ 0 := by
    intro u
    have hu := (F_Z_nonneg_le hf r hJ u).1
    simp only [ContinuousMap.neg_apply]
    nlinarith [mul_nonneg hξ.le hu]
  letI : ProperSpace (D (addFun (h ω) (-F_Z f r Z))).Space :=
    sec8_proper_of_bounded_weyl (D (h ω)) _ hlen ξ _ hW ha hb
  exact sec8_exists_constSpeedGeod _ hlenShift x y

/-- Endpoint form of the preceding geodesic-existence statement. -/
theorem lemma82_shifted_selector_endpoints {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistRd d)
    (hd : 3 ≤ d) (hh : IsWholeSpaceLGF h P)
    {ξ Q : ℝ} (hξ : 0 < ξ) (hQ : Real.sqrt (2 * d) < Q)
    {D : DistRd d → ContMetric d} (hD : IsSharpWeakExpMetric d ξ Q D)
    {f : ℕ → C(Rd d, ℝ)} {J : ℕ} {Mf : ℝ}
    (hf : ∀ j < J, (∀ x, 0 ≤ f j x) ∧ (∀ x, f j x ≤ Mf))
    (r : ℝ) {Z : Finset (Rd d × ℕ)} (hJ : ∀ q ∈ Z, q.2 < J)
    (x y : Rd d) :
    ∀ᵐ ω ∂P,
      sec8Sel x y (D (addFun (h ω) (-F_Z f r Z))).1 0 = x ∧
      sec8Sel x y (D (addFun (h ω) (-F_Z f r Z))).1 1 = y := by
  filter_upwards [lemma82_shifted_geod_exists P h hd hh hξ hQ hD hf r hJ x y]
    with ω hex
  have h := (exists_measurable_geodSelector x y).choose_spec.2 _ hex
  exact ⟨h.1.1, h.1.2.1⟩

end HigherDimLQGMetric
