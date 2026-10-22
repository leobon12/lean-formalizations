import HigherDimLQGMetric.Trap.Recovery

/-!
# Tools for the stability part of the trap ([S] Lemma 4.2, MA1 A17 "Stability")

Packet S3. Coordinate forms (a coordinate `ρ` on a metric space `X`, distance function
`fun u v => ENNReal.ofReal (ρ (u, v))`) of:

* `trap_coord_weighted_param`: parametrization of a curve at constant weighted speed on `[0, 1]`,
  with the correspondence of subcurves;
* `trap_coord_mapsTo`: confinement (C) — a curve from `closure V` of small `ρ`-weighted cost, for
  a coordinate `ρ` that is uniformly close to the base coordinate `ζ` on `closure A` and has a
  collar, stays in `Y₀` (measured with `ζ`);
* `trap_coord_weyl_eq`: for collector points, the base weighted distance confined to any set
  containing `Y₀` equals the one confined to `Y₀`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology BoundedContinuousFunction unitInterval
open scoped ENNReal

namespace HigherDimLQGMetric

open LQGMetric.MetricGeometry

/-- **Constant weighted speed on `[0, 1]`** for a coordinate. -/
theorem trap_coord_weighted_param {X : Type*} [MetricSpace X] {ρ : X × X → ℝ}
    (hρ : IsCoordinate ρ) {w : X → ℝ} (hwc : Continuous w) (hwpos : ∀ x, 0 < w x)
    {Q : ℝ → X} (hQ : ContinuousOn Q (Icc 0 1))
    (hfin : weightedLengthWith (fun u v => ENNReal.ofReal (ρ (u, v))) w Q 0 1 ≠ ⊤)
    (hpos : 0 < (weightedLengthWith (fun u v => ENNReal.ofReal (ρ (u, v))) w Q 0 1).toReal) :
    ∃ Q' : ℝ → X, ContinuousOn Q' (Icc 0 1) ∧ Q' 0 = Q 0 ∧ Q' 1 = Q 1 ∧
      MapsTo Q' (Icc 0 1) (Q '' Icc 0 1) ∧
      (∀ s t, 0 ≤ s → s ≤ t → t ≤ 1 →
        weightedLengthWith (fun u v => ENNReal.ofReal (ρ (u, v))) w Q' s t =
          ENNReal.ofReal
            ((weightedLengthWith (fun u v => ENNReal.ofReal (ρ (u, v))) w Q 0 1).toReal *
              (t - s))) ∧
      (∀ s t, 0 ≤ s → s ≤ t → t ≤ 1 → ∃ u v, 0 ≤ u ∧ u ≤ v ∧ v ≤ 1 ∧ Q' s = Q u ∧ Q' t = Q v ∧
        weightedLengthWith (fun u v => ENNReal.ofReal (ρ (u, v))) w Q u v =
          weightedLengthWith (fun u v => ENNReal.ofReal (ρ (u, v))) w Q' s t) := by
  set W := weightedLengthWith (fun u v => ENNReal.ofReal (ρ (u, v))) w Q 0 1 with hW
  set pt := MetricFunSpace.pt ρ hρ.metric with hpt
  set val := LQGMetric.metricFunSpaceVal ρ hρ.metric with hval
  have hwlZ : ∀ (P : ℝ → X) (a b : ℝ),
      weightedLengthWith (fun u v => ENNReal.ofReal (ρ (u, v))) w P a b =
        weightedLength (w ∘ val) (pt ∘ P) a b :=
    fun P a b => weightedLengthWith_metricFunSpace hρ.metric w P a b
  have hQZ : ContinuousOn (pt ∘ Q) (Icc 0 1) := hρ.trap_continuousOn_pt hQ
  have hwZ : ContinuousOn (w ∘ val) ((pt ∘ Q) '' Icc 0 1) :=
    (hwc.comp hρ.val_continuous).continuousOn
  have hWZ : weightedLength (w ∘ val) (pt ∘ Q) 0 1 = W := (hwlZ Q 0 1).symm
  obtain ⟨P, hPc, hP0, hP1, hPS, hPparam, hPcorr⟩ :=
    trap_exists_weighted_param (w := w ∘ val) (Q := pt ∘ Q) zero_le_one hQZ hwZ
      (fun t _ => hwpos _) hpos (by rw [hWZ]; exact hfin)
  rw [hWZ, div_self hpos.ne'] at hPc hP1 hPS hPparam hPcorr
  refine ⟨val ∘ P, hρ.trap_continuousOn_val hPc, ?_, ?_, ?_, ?_, ?_⟩
  · show val (P 0) = Q 0
    rw [hP0]
    rfl
  · show val (P 1) = Q 1
    rw [hP1]
    rfl
  · intro t ht
    obtain ⟨r, hr, hrP⟩ := hPS ht
    exact ⟨r, hr, by rw [Function.comp_apply, ← hrP]; rfl⟩
  · intro s t hs hst ht
    rw [hwlZ]
    exact hPparam s t hs hst ht
  · intro s t hs hst ht
    obtain ⟨u, v, hu, huv, hv, hPs, hPt, hwl⟩ := hPcorr s t hs hst ht
    refine ⟨u, v, hu, huv, hv, ?_, ?_, ?_⟩
    · show val (P s) = Q u
      rw [hPs]
      rfl
    · show val (P t) = Q v
      rw [hPt]
      rfl
    · rw [hwlZ, hwlZ]
      exact hwl

/-- **(C) in coordinate form**, measured against the base coordinate `ζ`: a curve from
`closure V` of `ρ`-weighted cost `< ofReal κ`, for a coordinate `ρ` with a collar of width `κ`
around `closure V` that is uniformly within `θ` of `ζ` on `closure A`, stays in
`Y_{κ + θ}` measured with `ζ`. -/
theorem trap_coord_mapsTo {X : Type*} [MetricSpace X] {ρ ζ : X × X → ℝ} (hρ : IsCoordinate ρ)
    (hζ : IsCoordinate ζ) {A V : Set X} (hA : IsOpen A) (hV : IsOpen V) (hVA : closure V ⊆ A)
    {w : X → ℝ} (hw1 : ∀ x, x ∉ V → w x = 1) {κ θ : ℝ}
    (hcol : ∀ x ∈ closure V, ∀ y ∈ frontier A, κ ≤ ρ (x, y))
    (hclose : ∀ x ∈ closure A, ∀ y ∈ closure A, |ρ (x, y) - ζ (x, y)| ≤ θ)
    {Q : ℝ → X} (hQ : ContinuousOn Q (Icc 0 1)) (hQ0 : Q 0 ∈ closure V)
    (hcost : weightedLengthWith (fun u v => ENNReal.ofReal (ρ (u, v))) w Q 0 1 <
      ENNReal.ofReal κ) :
    MapsTo Q (Icc 0 1) A ∧ MapsTo Q (Icc 0 1) (coordTrapSet hζ.metric A V (κ + θ)) := by
  have hE0 : ∀ x, ENNReal.ofReal (ρ (x, x)) = 0 := fun x => by
    rw [hρ.metric.self_eq_zero, ENNReal.ofReal_zero]
  have hcolE : ∀ x ∈ closure V, ∀ y ∈ frontier A,
      ENNReal.ofReal κ ≤ ENNReal.ofReal (ρ (x, y)) :=
    fun x hx y hy => ENNReal.ofReal_le_ofReal (hcol x hx y hy)
  have hmapsA := trap_confine hA hV hVA hE0 hw1 hcolE hQ hQ0 hcost
  refine ⟨hmapsA, fun t ht => ⟨subset_closure (hmapsA ht), ?_⟩⟩
  obtain ⟨s, hs, hsV, hst⟩ := trap_last_visit (E := fun u v => ENNReal.ofReal (ρ (u, v)))
    hV hE0 hw1 hQ hQ0 ht
  have hκ : 0 ≤ κ := by
    by_contra hneg
    push Not at hneg
    rw [ENNReal.ofReal_of_nonpos hneg.le] at hcost
    exact absurd hcost (not_lt.2 bot_le)
  have hρst : ρ (Q s, Q t) ≤ κ := by
    have h1 := hst.trans hcost.le
    exact (ENNReal.ofReal_le_ofReal_iff hκ).1 h1
  have hsA : Q s ∈ closure A := subset_closure (hmapsA ⟨hs.1, hs.2.trans ht.2⟩)
  have htA : Q t ∈ closure A := subset_closure (hmapsA ht)
  have hζst : ζ (Q t, Q s) ≤ κ + θ := by
    have h1 := hclose (Q s) hsA (Q t) htA
    rw [hζ.metric.symm]
    linarith [(abs_le.1 h1).1]
  show Metric.infDist _ _ ≤ κ + θ
  exact (infDist_pt_le hζ.metric hsV).trans hζst

/-- For collector points, the base weighted distance confined to any set `S ⊇ Y₀` equals the one
confined to `Y₀`, provided the latter is `< 3ε₀` and `3ε₀ ≤ a_col/2`. -/
theorem trap_coord_weyl_eq {X : Type*} [MetricSpace X] {ζ : X × X → ℝ} (hζ : IsCoordinate ζ)
    {A V : Set X} (hA : IsOpen A) (hV : IsOpen V) (hVA : closure V ⊆ A)
    {w : X → ℝ} (hw1 : ∀ x, x ∉ V → w x = 1) {acol ε₀ : ℝ}
    (hcol : ∀ x ∈ closure V, ∀ y ∈ frontier A, 4 * acol ≤ ζ (x, y))
    (hε₀ : 0 < ε₀) (hε₀col : 3 * ε₀ ≤ acol / 2)
    {S : Set X} (hS : coordTrapSet hζ.metric A V (acol / 2) ⊆ S) {a b : X} (ha : a ∈ closure V)
    (hY₀ : weylDistOnWith (fun u v => ENNReal.ofReal (ζ (u, v))) w
      (coordTrapSet hζ.metric A V (acol / 2)) a b < ENNReal.ofReal (3 * ε₀)) :
    weylDistOnWith (fun u v => ENNReal.ofReal (ζ (u, v))) w S a b =
      weylDistOnWith (fun u v => ENNReal.ofReal (ζ (u, v))) w
        (coordTrapSet hζ.metric A V (acol / 2)) a b := by
  apply le_antisymm (weylDistOnWith_anti_set _ _ hS a b)
  simp only [weylDistOnWith, le_iInf_iff]
  intro P hPc hP0 hP1 hPS
  by_cases hlt : weightedLengthWith (fun u v => ENNReal.ofReal (ζ (u, v))) w P 0 1 <
    ENNReal.ofReal (3 * ε₀)
  · have hcol3 : ∀ x ∈ closure V, ∀ y ∈ frontier A, 3 * ε₀ ≤ ζ (x, y) :=
      fun x hx y hy => le_trans (by linarith) (hcol x hx y hy)
    have hzero : ∀ x ∈ closure A, ∀ y ∈ closure A, |ζ (x, y) - ζ (x, y)| ≤ 0 := by
      intro x _ y _
      simp
    have hmaps := (trap_coord_mapsTo hζ hζ hA hV hVA hw1 hcol3 hzero hPc (hP0 ▸ ha) hlt).2
    have hmaps' : MapsTo P (Icc 0 1) (coordTrapSet hζ.metric A V (acol / 2)) :=
      hmaps.mono_right (coordTrapSet_mono hζ.metric (by linarith))
    exact iInf_le_of_le P <| iInf_le_of_le hPc <| iInf_le_of_le hP0 <| iInf_le_of_le hP1 <|
      iInf_le_of_le hmaps' le_rfl
  · push Not at hlt
    exact (hY₀.le.trans hlt)

end HigherDimLQGMetric
