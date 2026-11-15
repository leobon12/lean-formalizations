/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5LiftAmb
import InteractingSLE.Spec.Sec7.R5LiftReflect
import InteractingSLE.Spec.Sec7.R5SameClause

/-!
# Lemma R.5's common phase: one integer for all references, the exposed word, and `R7AmbientCover`

Packet PROVE-R5-LIFT. Lemma R.5's exposed heights in the current chart are `−Λ + δ`, `+Λ + δ` with ONE phase
`δ ∈ 2πχℤ` on both sides of the driver (Astra's follow-up 5, (3.1); spec pp. 474–475). With the ambient lifts of
`R5Same.ambLift` the phase is `χ · 2πn`, where `2πn` is the common limit of `current lift − arg f_{s_i}′` over all
references. This file proves:

* **`exists_int_common_of_link`** (one integer for all references): if each reference `i` has one integer `n_i` at
  all its good points, and any two references with good points have a common good point where their lift
  differences agree in the limit, then one integer serves for every reference and good point;
* **`exists_pos_tendsto_deriv_ambTransition`**: the ambient transition `f_s ∘ old⁻¹` of a chart whose domain avoids
  the ambient hull has a positive reflected derivative at a real point where it extends continuously to the base with
  real, injective boundary values (`R5Lift.exists_pos_tendsto_deriv_of_reflect_eqOn`);
* **`tendsto_ambLift_sub_ambLift`**: the link's limit for two ambient lifts (time compatibility of
  `R5Lift.tendsto_im_logDerivFwd_sub_of_notMem_closure`, read through any chart);
* **`exists_int_common_relChart_ambLift`**: the common integer of the current relative chart against the ambient lifts
  of a family of earlier relative references, each reflecting on a preconnected real set (its exposed interval), with
  the link geometry as hypotheses;
* **`forceBoundaryData_exposed`**, **`phaseData_exposed`**, **`word_identity_exposed`**: on the exposed interval of the
  current word, and at an ambient point on the same side of the ambient driver inside the ambient seeds, the word
  identity `β_s(x′) + χ·2πn = phaseData(χ·2πn + a)(ξ) − a` holds;
* **`forceBoundaryData_between`**, **`word_identity_exposed_indicator`**: the same identity with arbitrary seed
  indices, an explicit phase indicator and an offset (the form of the late `Wire.VisitReferenceAmbientCoverPosExc`);
* **`phase_mem_lattice`**: `χ·2πn + a ∈ ℤ·phaseStep` when `a ∈ ℤ·phaseStep`;
* `R7ExposedCover` (named pathwise input: `R5Same.R7AmbientCover`'s geometric conjuncts, the exposed-side position
  data and the common lift limit `2πn`) and **`r7AmbientCover_of_exposed`**: it gives `R5Same.R7AmbientCover` with the
  phase `δ ω = χ·2πn ω + a`, and **`r7AmbientCover_lattice`** its lattice clause.

**Scope.** `R5Same.R7AmbientCover` (and hence `R7ExposedCover`) asks for a counterflow-hull landing `z₀ ∈ C ∩ K_{s}`
at EVERY non-exceptional current coordinate; coordinates on the pocket walls (outside the exposed interval) land on
`∂C`, not in the open pocket `C`, so those statements can only hold when the walls are not seen in the current chart.
The wall coordinates need the initial (time-`0`) references instead (handoff).

Ruling R48: nothing here uses Theorem 1.2/1.3, `Theorem12ParamStatement`, `Theorem13Statement` or any result taking
them as hypotheses.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric Complex
open QuantumZipper (H fwdHull fwdMap logDerivFwd chiC)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5Lift

open PocketStop PocketTraversal Lemma71C PocketStopSide PhaseSel R5Phase R5Same

/-! ### One integer for all references -/

/-- **One integer for all references.** Each reference `i` has one integer `n_i` giving the limit `2πn_i` of its lift
difference `D i` at all its good points; any two references with good points share a good point at which
`D i − D j → 0`. Then one integer serves for every reference and every good point. -/
theorem exists_int_common_of_link {ι : Type*} {Good : ι → ℝ → Prop} {D : ι → ℂ → ℝ}
    (hlat : ∀ i, ∃ n : ℤ, ∀ ξ, Good i ξ → Tendsto (D i) (𝓝[H] (ξ : ℂ)) (𝓝 (2 * Real.pi * n)))
    (hlink : ∀ i j ξ ξ', Good i ξ → Good j ξ' → ∃ ζ, Good i ζ ∧ Good j ζ ∧
      Tendsto (fun y => D i y - D j y) (𝓝[H] (ζ : ℂ)) (𝓝 0)) :
    ∃ n : ℤ, ∀ i ξ, Good i ξ → Tendsto (D i) (𝓝[H] (ξ : ℂ)) (𝓝 (2 * Real.pi * n)) := by
  classical
  choose N hN using hlat
  by_cases hex : ∃ i ξ, Good i ξ
  · obtain ⟨i₀, ξ₀, h₀⟩ := hex
    refine ⟨N i₀, fun i ξ hξ => ?_⟩
    obtain ⟨ζ, hζ₀, hζ, hlim⟩ := hlink i₀ i ξ₀ ξ h₀ hξ
    have := nhdsWithin_H_neBot ζ
    have h2 := ((hN i₀ ζ hζ₀).sub (hN i ζ hζ))
    have heq := tendsto_nhds_unique h2 hlim
    have hπ : (2 * Real.pi) ≠ 0 := by positivity
    have hNN : (N i : ℝ) = N i₀ := by
      have : 2 * Real.pi * ((N i₀ : ℝ) - N i) = 0 := by rw [mul_sub]; exact heq
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hπ
      · linarith
    rw [← hNN]
    exact hN i ξ hξ
  · exact ⟨0, fun i ξ hξ => absurd ⟨i, ξ, hξ⟩ hex⟩

/-- **The link limit for two ambient lifts**: through any chart inverse staying off the ambient hull at `s'`, if the
`f_s`-image of the approach tends to a real point off the closed increment hull of `[s, s']`, the two lift
differences `lift − Im log f_s′` and `lift − Im log f_{s'}′` agree in the limit. -/
theorem tendsto_ambLift_sub_ambLift {cur : Chart} {W : ℝ → ℝ} (hW : Continuous W) {s s' : ℝ} (hs : 0 ≤ s)
    (hss' : s ≤ s') {ξ : ℂ} (hK : ∀ᶠ y in 𝓝[H] ξ, cur.2.1 y ∈ H \ fwdHull W s') {x : ℝ}
    (hFx : Tendsto (fun y => fwdMap W s (cur.2.1 y)) (𝓝[H] ξ) (𝓝 (x : ℂ)))
    (hx : (x : ℂ) ∉ closure (fwdHull (fun r => W (s + r) - W s) (s' - s))) :
    Tendsto (fun y => (cur.2.2 (cur.2.1 y) - (logDerivFwd W s (cur.2.1 y)).im) -
      (cur.2.2 (cur.2.1 y) - (logDerivFwd W s' (cur.2.1 y)).im)) (𝓝[H] ξ) (𝓝 0) := by
  refine (tendsto_im_logDerivFwd_sub_of_notMem_closure hW hs hss' hK hFx hx).congr fun y => ?_
  ring

/-- **The ambient transition reflects with positive derivative** at a real point `x` where it agrees on `ℍ ∩ B(x, r)`
with a map `g` continuous on `ℍ̄ ∩ B(x, r)`, real on the real diameter and injective on `ℍ̄ ∩ B(x, r)`; the chart's
domain must avoid the ambient hull at `s` (holomorphy and the values in `ℍ` are then automatic). -/
theorem exists_pos_tendsto_deriv_ambTransition {old : Chart} (hold : old.IsConformal) {W : ℝ → ℝ}
    (hW : Continuous W) {s : ℝ} (hs : 0 ≤ s) (hK : (old.dom : Set ℂ) ⊆ H \ fwdHull W s) {x r : ℝ} (hr : 0 < r)
    {g : ℂ → ℂ} (hSg : EqOn (fun y => fwdMap W s (old.2.1 y)) g (H ∩ ball (x : ℂ) r))
    (hc : ContinuousOn g (QuantumZipper.Hbar ∩ ball (x : ℂ) r))
    (hreal : ∀ z ∈ ball (x : ℂ) r, z.im = 0 → (g z).im = 0)
    (hinj : InjOn g (QuantumZipper.Hbar ∩ ball (x : ℂ) r)) :
    ∃ b : ℝ, 0 < b ∧ Tendsto (deriv fun y => fwdMap W s (old.2.1 y)) (𝓝[H] (x : ℂ)) (𝓝 (b : ℂ)) := by
  have hmapsK : ∀ y ∈ H ∩ ball (x : ℂ) r, old.2.1 y ∈ H \ fwdHull W s := fun y hy =>
    hK (hold.inv_mem_dom hy.1)
  have hSd : DifferentiableOn ℂ (fun y => fwdMap W s (old.2.1 y)) (H ∩ ball (x : ℂ) r) :=
    (QuantumZipper.FwdHolo.differentiableOn_fwdMap hW hs).comp (hold.1.mono inter_subset_left) hmapsK
  refine exists_pos_tendsto_deriv_of_reflect_eqOn hr hSg (hSd.congr fun y hy => (hSg hy).symm) hc hreal
    (fun y hy => ?_) hinj
  rw [← hSg hy]
  exact QuantumZipper.FwdHolo.mapsTo_fwdMap hW hs (hmapsK y hy)

/-! ### The common integer of the current relative chart -/

variable {Ω : Type*} {c : Ω → Chart} {γ : Ω → ℝ → ℂ} {ω : Ω}

/-- A current coordinate `ξ` is **good for the reference** (old chart `old`, real set `J`) when an unfilled
half-disc of the old chart about a point of `J` lies in the current domain and the transition tends to that point. -/
def IsGoodRef (old cur : Chart) (J : Set ℝ) (ξ : ℝ) : Prop :=
  ∃ x r : ℝ, x ∈ J ∧ 0 < r ∧ old.2.1 '' (H ∩ ball (x : ℂ) r) ⊆ (cur.dom : Set ℂ) ∧
    Tendsto (fun z => old.1 (cur.2.1 z)) (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ))

/-- **The common phase of the current relative chart** against a family of ambient lifts. References `i` are the
relative charts at capacities `p i ≤ q` with ambient times `s i`; each reference's domain avoids the ambient hull at
`s i` and its ambient transition reflects with positive derivative on a preconnected real set `J i` (its exposed
interval). If any two references with good current coordinates have a common good coordinate at which the earlier
one's ambient image tends to a real point off the closed increment hull, then ONE integer `n` gives the limit `2πn`
of `current lift − Im log f_{s i}′` at every good coordinate of every reference. -/
theorem exists_int_common_relChart_ambLift {ι : Type*} {p : ι → ℝ≥0} {q : ℝ≥0} (hc : (c ω).IsConformal)
    (hγ : IsDrivenCurve (γ ω)) (hq : (q : ℝ≥0∞) < capLife (γ ω)) (hpq : ∀ i, p i ≤ q) {ℓ : ℂ → ℂ}
    (hℓ : IsDerivLog (c ω).1 ℓ (c ω).dom) (hlift : ∀ z ∈ (c ω).dom, (c ω).2.2 z = (ℓ z).im)
    {W : ℝ → ℝ} (hW : Continuous W) {s : ι → ℝ} (hs : ∀ i, 0 ≤ s i)
    (hK : ∀ i, ((relChart c γ (p i) ω).dom : Set ℂ) ⊆ H \ fwdHull W (s i)) {J : ι → Set ℝ}
    (hJ : ∀ i, IsPreconnected (J i))
    (hrefl : ∀ i, ∀ x ∈ J i, ∃ b : ℝ, 0 < b ∧
      Tendsto (deriv fun y => fwdMap W (s i) ((relChart c γ (p i) ω).2.1 y)) (𝓝[H] (x : ℂ)) (𝓝 (b : ℂ)))
    (hlink : ∀ i j ξ ξ', IsGoodRef (relChart c γ (p i) ω) (relChart c γ q ω) (J i) ξ →
      IsGoodRef (relChart c γ (p j) ω) (relChart c γ q ω) (J j) ξ' → ∃ ζ : ℝ,
        IsGoodRef (relChart c γ (p i) ω) (relChart c γ q ω) (J i) ζ ∧
        IsGoodRef (relChart c γ (p j) ω) (relChart c γ q ω) (J j) ζ ∧
        ((s i ≤ s j ∧ ∃ x : ℝ, Tendsto (fun y => fwdMap W (s i) ((relChart c γ q ω).2.1 y)) (𝓝[H] (ζ : ℂ))
            (𝓝 (x : ℂ)) ∧ (x : ℂ) ∉ closure (fwdHull (fun r => W (s i + r) - W (s i)) (s j - s i))) ∨
          (s j ≤ s i ∧ ∃ x : ℝ, Tendsto (fun y => fwdMap W (s j) ((relChart c γ q ω).2.1 y)) (𝓝[H] (ζ : ℂ))
            (𝓝 (x : ℂ)) ∧ (x : ℂ) ∉ closure (fwdHull (fun r => W (s j + r) - W (s j)) (s i - s j))))) :
    ∃ n : ℤ, ∀ i ξ, IsGoodRef (relChart c γ (p i) ω) (relChart c γ q ω) (J i) ξ →
      Tendsto (fun y => (relChart c γ q ω).2.2 ((relChart c γ q ω).2.1 y) -
        (logDerivFwd W (s i) ((relChart c γ q ω).2.1 y)).im) (𝓝[H] (ξ : ℂ)) (𝓝 (2 * Real.pi * n)) := by
  have hcur : (relChart c γ q ω).IsConformal := isConformal_relChart_of_driven hγ hq hc
  -- the current inverse stays off every reference's ambient hull
  have hKcur : ∀ i, ∀ y ∈ H, (relChart c γ q ω).2.1 y ∈ H \ fwdHull W (s i) := fun i y hy =>
    hK i (relChart_dom_antitone hc hγ hq (hpq i) (hcur.inv_mem_dom hy))
  refine exists_int_common_of_link (Good := fun i ξ => IsGoodRef (relChart c γ (p i) ω) (relChart c γ q ω) (J i) ξ)
    (D := fun i y => (relChart c γ q ω).2.2 ((relChart c γ q ω).2.1 y) -
      (logDerivFwd W (s i) ((relChart c γ q ω).2.1 y)).im) (fun i => ?_) (fun i j ξ ξ' hξ hξ' => ?_)
  · obtain ⟨n, hn⟩ := exists_int_forall_tendsto_relChart_ambLift hc hγ hq (hpq i) hℓ hlift hW (hs i) (hK i) (hJ i)
      (hrefl i)
    exact ⟨n, fun ξ ⟨x, r, hx, hr, hCollar, hTransition⟩ => hn ξ x r hx hr hCollar hTransition⟩
  · obtain ⟨ζ, hζi, hζj, hcase⟩ := hlink i j ξ ξ' hξ hξ'
    refine ⟨ζ, hζi, hζj, ?_⟩
    rcases hcase with ⟨hij, x, hFx, hx⟩ | ⟨hji, x, hFx, hx⟩
    · exact tendsto_ambLift_sub_ambLift hW (hs i) hij (eventually_nhdsWithin_of_forall (hKcur j)) hFx hx
    · have h := tendsto_ambLift_sub_ambLift hW (hs j) hji (eventually_nhdsWithin_of_forall (hKcur i)) hFx hx
      have h' := h.neg
      rw [neg_zero] at h'
      refine h'.congr fun y => ?_
      ring

/-! ### The word identity on the exposed interval -/

section Word

variable {κ : ℝ}

/-- **The current word on its exposed interval** (the seeds are the innermost force points): `−Λ` left of the driver,
`+Λ` right of it. -/
theorem forceBoundaryData_exposed {nL nR : ℕ} (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ)
    {vL : Fin (nL + 1) → ℝ} {vR : Fin (nR + 1) → ℝ} (hL : ∀ i, vL i ≤ vL 0) (hR : ∀ j, vR 0 ≤ vR j) {ξ : ℝ}
    (hξ : ξ ∈ Ioo (vL 0) (vR 0)) :
    forceBoundaryData κ ρL ρR vL vR ξ = if ξ < 0 then -(Real.pi / Real.sqrt κ) else Real.pi / Real.sqrt κ := by
  unfold forceBoundaryData
  split_ifs with h
  · have hempty : Finset.univ.filter (fun i => ξ < vL i) = ∅ :=
      Finset.filter_eq_empty_iff.2 fun i _ => not_lt.2 ((hL i).trans hξ.1.le)
    rw [hempty, Finset.sum_empty, add_zero, mul_one]
  · have hempty : Finset.univ.filter (fun j => vR j ≤ ξ) = ∅ :=
      Finset.filter_eq_empty_iff.2 fun j _ => not_le.2 (hξ.2.trans_le (hR j))
    rw [hempty, Finset.sum_empty, add_zero, mul_one]

/-- **The ambient word inside the ambient seeds**: `−Λ` at a point left of the driver with no left force point to
its right, `+Λ` at a point right of it with every right force point beyond it. -/
theorem forceBoundaryData_inner {mL mR : ℕ} (ρL : Fin mL → ℝ) (ρR : Fin mR → ℝ) {VL : Fin mL → ℝ}
    {VR : Fin mR → ℝ} {x : ℝ} (hL : x < 0 → ∀ j, VL j ≤ x) (hR : 0 ≤ x → ∀ j, x < VR j) :
    forceBoundaryData κ ρL ρR VL VR x = if x < 0 then -(Real.pi / Real.sqrt κ) else Real.pi / Real.sqrt κ := by
  unfold forceBoundaryData
  split_ifs with h
  · have hempty : Finset.univ.filter (fun j => x < VL j) = ∅ :=
      Finset.filter_eq_empty_iff.2 fun j _ => not_lt.2 (hL h j)
    rw [hempty, Finset.sum_empty, add_zero, mul_one]
  · have hempty : Finset.univ.filter (fun j => VR j ≤ x) = ∅ :=
      Finset.filter_eq_empty_iff.2 fun j _ => not_le.2 (hR (not_lt.1 h) j)
    rw [hempty, Finset.sum_empty, add_zero, mul_one]

/-- **The phase-shifted word on the exposed interval** is the word plus the phase. -/
theorem phaseData_exposed {nL nR : ℕ} (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ)
    {vL : Fin (nL + 1) → ℝ} {vR : Fin (nR + 1) → ℝ} (δ : ℝ) {ξ : ℝ} (hξ : ξ ∈ Ioo (vL 0) (vR 0)) :
    phaseData κ ρL ρR vL vR δ ξ = forceBoundaryData κ ρL ρR vL vR ξ + δ := by
  unfold phaseData
  rw [indicator_of_mem hξ, Pi.one_apply, mul_one]

/-- **R.5's word identity on the exposed interval.** If the current coordinate `ξ` lies in the exposed interval and
the ambient coordinate `x′` lies on the same side of the ambient driver inside the ambient seeds, then with the
phase `δ = χ·2πn + a` the ambient height plus `χ·2πn` is the phase-shifted current word minus `a`. -/
theorem word_identity_exposed {nL nR mL mR : ℕ} (ρL : Fin (nL + 1) → ℝ) (ρR : Fin (nR + 1) → ℝ)
    (ρL' : Fin mL → ℝ) (ρR' : Fin mR → ℝ) {vL : Fin (nL + 1) → ℝ} {vR : Fin (nR + 1) → ℝ} {VL : Fin mL → ℝ}
    {VR : Fin mR → ℝ} (hvL : ∀ i, vL i ≤ vL 0) (hvR : ∀ j, vR 0 ≤ vR j) {ξ x : ℝ} (hξ : ξ ∈ Ioo (vL 0) (vR 0))
    (hVL : x < 0 → ∀ j, VL j ≤ x) (hVR : 0 ≤ x → ∀ j, x < VR j) (hside : ξ < 0 ↔ x < 0) (n : ℤ) (a : ℝ) :
    forceBoundaryData κ ρL' ρR' VL VR x + chiC κ * (2 * Real.pi * n) =
      phaseData κ ρL ρR vL vR (chiC κ * (2 * Real.pi * n) + a) ξ - a := by
  rw [phaseData_exposed ρL ρR _ hξ, forceBoundaryData_exposed ρL ρR hvL hvR hξ,
    forceBoundaryData_inner ρL' ρR' hVL hVR]
  by_cases h : ξ < 0
  · simp only [h, hside.1 h, ↓reduceIte]; ring
  · have hx : ¬ x < 0 := fun hx => h (hside.2 hx)
    simp only [h, hx, ↓reduceIte]; ring

/-- **The word between two seed coordinates** (arbitrary seed indices; the seeds are the innermost force points):
`−Λ` left of the driver, `+Λ` right of it. -/
theorem forceBoundaryData_between {nL nR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) {vL : Fin nL → ℝ}
    {vR : Fin nR → ℝ} {iL : Fin nL} {iR : Fin nR} (hL : ∀ i, vL i ≤ vL iL) (hR : ∀ j, vR iR ≤ vR j) {ξ : ℝ}
    (hξ : ξ ∈ Ioo (vL iL) (vR iR)) :
    forceBoundaryData κ ρL ρR vL vR ξ = if ξ < 0 then -(Real.pi / Real.sqrt κ) else Real.pi / Real.sqrt κ :=
  forceBoundaryData_inner ρL ρR (fun _ j => (hL j).trans hξ.1.le) (fun _ j => hξ.2.trans_le (hR j))

/-- **R.5's word identity in the indicator form** (the late side data's form: arbitrary seed indices, a supplied
phase on the seed interval and an offset `off`): with the phase `χ d + off`, the ambient height plus `χ d` is the
current word plus the phase on the seed interval minus `off`. -/
theorem word_identity_exposed_indicator {nL nR mL mR : ℕ} (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (ρL' : Fin mL → ℝ) (ρR' : Fin mR → ℝ) {vL : Fin nL → ℝ} {vR : Fin nR → ℝ} {VL : Fin mL → ℝ}
    {VR : Fin mR → ℝ} {iL : Fin nL} {iR : Fin nR} (hvL : ∀ i, vL i ≤ vL iL) (hvR : ∀ j, vR iR ≤ vR j)
    {ξ x : ℝ} (hξ : ξ ∈ Ioo (vL iL) (vR iR)) (hVL : x < 0 → ∀ j, VL j ≤ x) (hVR : 0 ≤ x → ∀ j, x < VR j)
    (hside : ξ < 0 ↔ x < 0) (d off : ℝ) :
    forceBoundaryData κ ρL' ρR' VL VR x + chiC κ * d =
      forceBoundaryData κ ρL ρR vL vR ξ + (chiC κ * d + off) * (Ioo (vL iL) (vR iR)).indicator 1 ξ - off := by
  rw [forceBoundaryData_between ρL ρR hvL hvR hξ, forceBoundaryData_inner ρL' ρR' hVL hVR,
    indicator_of_mem hξ, Pi.one_apply, mul_one]
  by_cases h : ξ < 0
  · simp only [h, hside.1 h, ↓reduceIte]; ring
  · have hx : ¬ x < 0 := fun hx => h (hside.2 hx)
    simp only [h, hx, ↓reduceIte]; ring

/-- **The phase is lattice-valued**: `χ·2πn + a ∈ ℤ·phaseStep` when `a ∈ ℤ·phaseStep` (`phaseStep = −2πχ`). -/
theorem phase_mem_lattice (n : ℤ) {a : ℝ} (ha : ∃ m : ℤ, a = m * phaseStep κ) :
    ∃ m : ℤ, chiC κ * (2 * Real.pi * n) + a = m * phaseStep κ := by
  obtain ⟨m, rfl⟩ := ha
  refine ⟨m - n, ?_⟩
  simp only [phaseStep, Int.cast_sub]
  ring

end Word

/-! ### `R5Same.R7AmbientCover` from the exposed data and the common lift limit -/

/-- **The exposed-side form of R.5's pathwise cover with a common lift integer** (named pathwise input): exactly the
geometric conjuncts of `R5Same.R7AmbientCover` (reference, collar, transition, hull landing, approach in the
reference complement, ambient image off the ambient jumps and its convergence), together with: the current seeds
are the innermost current force points and `ξ` lies in the exposed interval between them; the ambient image lies on
the same side of the ambient driver as `ξ`, inside the ambient seeds; and the limit of `current lift − ambient lift`
is `2π n ω` for the given integer field `n` (the common phase; `exists_int_common_relChart_ambLift`). -/
def R7ExposedCover [MeasurableSpace Ω] {nL nR : ℕ} {mL mR : ℕ} (P : Measure Ω) (A : Set Ω)
    (γ : Ω → ℝ → ℂ) (xL : Ω → Fin (nL + 1) → ℝ) (xR : Ω → Fin (nR + 1) → ℝ) (c : Ω → Chart) (C : Ω → Set ℂ)
    (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞) (VL : Fin mL → ℝ≥0 → Ω → ℝ) (VR : Fin mR → ℝ≥0 → Ω → ℝ)
    (X : Ω → Set ℂ) (M : ℕ → Set Ω) (old : ℕ → Ω → Chart) (n : Ω → ℤ) (q : ℝ≥0) : Prop :=
  ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) → ∀ ξ : ℝ, ξ ∉ forceJumpSet
      (fun i => geomLW (fun t ω => segDriver (γ ω) t) xL i q ω - segDriver (γ ω) q)
      (fun j => geomRW (fun t ω => segDriver (γ ω) t) xR j q ω - segDriver (γ ω) q) →
    extendFrom H (relChart c γ q ω).2.1 ξ ∉ X ω →
    ∃ (i : ℕ) (x r x' : ℝ) (z₀ : ℂ), let s := Wire.Current.SideTest.rationalOriginalTime i;
      ω ∈ M i ∧ 0 < r ∧
      (old i ω).2.1 '' (H ∩ ball (x : ℂ) r) ⊆ (relChart c γ q ω).dom ∧
      Tendsto (fun z => (old i ω).1 ((relChart c γ q ω).2.1 z)) (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ)) ∧
      z₀ ∈ C ω ∩ refHull W' ζ' i ω ∧
      Tendsto (relChart c γ q ω).2.1 (𝓝[H] (ξ : ℂ)) (𝓝 z₀) ∧
      (∀ᶠ y in 𝓝[H] (ξ : ℂ), (relChart c γ q ω).2.1 y ∈ H \ liveExt A γ C (refHull W' ζ' i) 0 ω) ∧
      x' ∉ forceJumpSet (fun j => VL j s ω - W' s ω) (fun j => VR j s ω - W' s ω) ∧
      Tendsto (fun y => fwdMap (fun t : ℝ => W' t.toNNReal ω) s ((relChart c γ q ω).2.1 y)) (𝓝[H] (ξ : ℂ))
        (𝓝 (x' : ℂ)) ∧
      (∀ i', geomLW (fun t ω => segDriver (γ ω) t) xL i' q ω ≤ geomLW (fun t ω => segDriver (γ ω) t) xL 0 q ω) ∧
      (∀ j', geomRW (fun t ω => segDriver (γ ω) t) xR 0 q ω ≤ geomRW (fun t ω => segDriver (γ ω) t) xR j' q ω) ∧
      ξ ∈ Ioo (geomLW (fun t ω => segDriver (γ ω) t) xL 0 q ω - segDriver (γ ω) q)
        (geomRW (fun t ω => segDriver (γ ω) t) xR 0 q ω - segDriver (γ ω) q) ∧
      (x' < 0 → ∀ j, VL j s ω - W' s ω ≤ x') ∧ (0 ≤ x' → ∀ j, x' < VR j s ω - W' s ω) ∧
      (ξ < 0 ↔ x' < 0) ∧
      Tendsto (fun y => (relChart c γ q ω).2.2 ((relChart c γ q ω).2.1 y) -
          ambLift W' i ω ((relChart c γ q ω).2.1 y)) (𝓝[H] (ξ : ℂ)) (𝓝 (2 * Real.pi * n ω))

/-- **`R5Same.R7AmbientCover` from the exposed cover with a common lift integer**: the lift-difference limit is
`d = 2π n ω` and the word identity holds with the phase `δ ω = χ·2π n ω + a` (`word_identity_exposed`). -/
theorem r7AmbientCover_of_exposed [MeasurableSpace Ω] {κ : ℝ} {nL nR : ℕ} {ρL : Fin (nL + 1) → ℝ}
    {ρR : Fin (nR + 1) → ℝ} {mL mR : ℕ} {ρL' : Fin mL → ℝ} {ρR' : Fin mR → ℝ} {P : Measure Ω} {A : Set Ω}
    {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ} {a : ℝ} {C : Ω → Set ℂ}
    {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} {VL : Fin mL → ℝ≥0 → Ω → ℝ} {VR : Fin mR → ℝ≥0 → Ω → ℝ}
    {X : Ω → Set ℂ} {M : ℕ → Set Ω} {old : ℕ → Ω → Chart} {n : Ω → ℤ} {q : ℝ≥0}
    (h : R7ExposedCover P A γ xL xR c C W' ζ' VL VR X M old n q) :
    R7AmbientCover κ ρL ρR ρL' ρR' P A γ xL xR c a C W' ζ' VL VR
      (fun ω => chiC κ * (2 * Real.pi * n ω) + a) X M old q := by
  filter_upwards [h] with ω hω hωA hlive ξ hξ hXξ
  obtain ⟨i, x, r, x', z₀, hM, hr, hcol, htr, hz₀, hinv, hev, hx', hfx, hvL, hvR, hξI, hVL, hVR, hside, hd⟩ :=
    hω hωA hlive ξ hξ hXξ
  have hvL' : ∀ i', (fun i => geomLW (fun t ω => segDriver (γ ω) t) xL i q ω - segDriver (γ ω) q) i' ≤
      (fun i => geomLW (fun t ω => segDriver (γ ω) t) xL i q ω - segDriver (γ ω) q) 0 := fun i' => by
    simp only; linarith [hvL i']
  have hvR' : ∀ j', (fun j => geomRW (fun t ω => segDriver (γ ω) t) xR j q ω - segDriver (γ ω) q) 0 ≤
      (fun j => geomRW (fun t ω => segDriver (γ ω) t) xR j q ω - segDriver (γ ω) q) j' := fun j' => by
    simp only; linarith [hvR j']
  exact ⟨i, x, r, x', 2 * Real.pi * n ω, z₀, hM, hr, hcol, htr, hz₀, hinv, hev, hx', hfx, hd,
    word_identity_exposed ρL ρR ρL' ρR' hvL' hvR' hξI hVL hVR hside (n ω) a⟩

/-- **The lattice clause for the phase `χ·2πn + a`** of `r7AmbientCover_of_exposed` (clause 2 of `R5Clauses`). -/
theorem r7AmbientCover_lattice [MeasurableSpace Ω] {κ : ℝ} {P : Measure Ω} {A : Set Ω} {q : ℝ≥0} (n : Ω → ℤ)
    {a : ℝ} (ha : ∃ m : ℤ, a = m * phaseStep κ) :
    ∀ᵐ ω ∂P, ω ∈ A → (q : ℝ≥0∞) < capLife (γ ω) →
      ∃ m : ℤ, (fun ω => chiC κ * (2 * Real.pi * n ω) + a) ω = m * phaseStep κ :=
  Eventually.of_forall fun ω _ _ => phase_mem_lattice (n ω) ha

end InteractingSLE.Sec7.R5Lift
