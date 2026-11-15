/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkWordsLand

/-!
# The left prime-end access of a common fresh arc: the incident-side identification

Packet PROVE-WALK-WORDS (Theorem GW4, proof, p. 637: "Every common contact is ordered the same way on the two
walks"; the left incident collars of the two walks at an interior common point). Two Loewner charts `c₀ʳ`, `c₀ˡ`
(launch charts, conformal) carry traces `ηʳ`, `ηˡ` that are simple up to times `τʳ`, `τˡ`, and fresh (in `ℍ`) from
times `tʳ`, `tˡ` on; their prefix charts are `cʳ = c₀ʳ.loewner Wʳ τʳ`, `cˡ = c₀ˡ.loewner Wˡ τˡ`. Suppose the two
traces pass through the same physical point `p = c₀ʳ⁻¹(ηʳ(tʳ)) = c₀ˡ⁻¹(ηˡ(tˡ))` **in the same direction** (later
points of `ηʳ` are later points of `ηˡ`), that near `p` the physical points of `ηʳ` are points of `ηˡ`, and that near
`p` the domain of `cʳ` lies in the domain of `cˡ`. If `yʳ < 0` is the left side point of `ηʳ(tʳ)` (with its time
orientation: `(yʳ, 0)` carries later points) and `yˡ < 0` any negative preimage of `ηˡ(tˡ)`, then the transition
`cˡ ∘ (cʳ)⁻¹` is an incident-side identification from `yʳ` to `yˡ` (`WalkIntBridge.SideIdentification`):
`nonempty_sideIdentification`.

## Proof

The transition is the chart `cʳ` landing, near `yʳ`, at `Λ(x) = c₀ʳ⁻¹(F̄ʳ(x))`, points of `ηˡ` (local hypothesis);
right of `yʳ` these are later points of `ηʳ` (`(yʳ, 0)` carries later points), hence later points of `ηˡ`. So
`nonempty_sideIdentification_of_later` (`WalkWordsLand`: the cluster-set lemma, the fibre lemma and the orientation of
the boundary correspondence) applies.

Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set Topology Complex Metric Bornology
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull)

namespace InteractingSLE.Theorem14.WalkWords

section Side

variable {c₀R c₀L : Chart} {WR WL : ℝ → ℝ} {ηR ηL : ℝ → ℂ} {tR τR tL τL yR yL : ℝ}

/-- **The incident-side identification of a common fresh arc traversed in the same direction** (see the module
docstring). -/
theorem nonempty_sideIdentification
    (hc₀R : c₀R.IsConformal) (hc₀L : c₀L.IsConformal)
    (hηR : IsLoewnerTrace WR ηR) (hWR : Continuous WR) (hWR0 : WR 0 = 0)
    (hηL : IsLoewnerTrace WL ηL) (hWL : Continuous WL) (hWL0 : WL 0 = 0)
    (htR : 0 ≤ tR) (htτR : tR < τR) (hHR : ∀ s ∈ Icc tR τR, ηR s ∈ H)
    (htL : 0 ≤ tL) (htτL : tL < τL) (hinjL : InjOn ηL (Icc 0 τL)) (hHL : ∀ s ∈ Icc tL τL, ηL s ∈ H)
    (hyR : yR < 0) (hFyR : extendFrom H (fwdMapInv WR τR) yR = ηR tR)
    (hlaterR : ∀ x ∈ Ioo yR 0, ∃ s ∈ Ioc tR τR, extendFrom H (fwdMapInv WR τR) x = ηR s)
    (hyL : yL < 0) (hFyL : extendFrom H (fwdMapInv WL τL) yL = ηL tL)
    (hp : c₀R.2.1 (ηR tR) = c₀L.2.1 (ηL tL))
    (hlater : ∀ s ∈ Ioc tR τR, ∃ s' ∈ Ioo tL τL, c₀R.2.1 (ηR s) = c₀L.2.1 (ηL s'))
    (hlocal : ∃ ρ > 0, ∀ s ∈ Icc 0 τR, ηR s ∈ H → c₀R.2.1 (ηR s) ∈ ball (c₀R.2.1 (ηR tR)) ρ →
      ∃ s' ∈ Icc 0 τL, ηL s' ∈ H ∧ c₀R.2.1 (ηR s) = c₀L.2.1 (ηL s'))
    (hdom : ∃ ρ > 0, ∀ z ∈ H, (c₀R.loewner WR τR).2.1 z ∈ ball (c₀R.2.1 (ηR tR)) ρ →
      (c₀R.loewner WR τR).2.1 z ∈ (c₀L.loewner WL τL).2.1 '' H) :
    Nonempty (WalkIntBridge.SideIdentification (c₀R.loewner WR τR) (c₀L.loewner WL τL) yR yL) := by
  set p : ℂ := c₀R.2.1 (ηR tR) with hpdef
  set FR : ℂ → ℂ := extendFrom H (fwdMapInv WR τR) with hFRdef
  have hτR0 : 0 ≤ τR := htR.trans htτR.le
  obtain ⟨-, hFRc, -, -⟩ := hηR.fiber_hyps hWR hWR0 hτR0
  obtain ⟨ρ₁, hρ₁, hloc⟩ := hlocal
  obtain ⟨ρ₂, hρ₂, hdom'⟩ := hdom
  set ρ : ℝ := min ρ₁ ρ₂ with hρdef
  have hρ : 0 < ρ := lt_min hρ₁ hρ₂
  have hreal : ∀ x : ℝ, (x : ℂ) ∈ Hbar := fun x => show (0 : ℝ) ≤ ((x : ℂ)).im by simp
  have hFRyH : FR yR ∈ H := by rw [hFyR]; exact hHR tR ⟨le_rfl, htτR.le⟩
  have hc₀Rcont : ∀ w ∈ H, ContinuousAt c₀R.2.1 w := fun w hw =>
    (hc₀R.1.differentiableAt (QuantumZipper.isOpen_H.mem_nhds hw)).continuousAt
  -- the physical landing of `cʳ` near `yʳ`
  have hev : ∀ᶠ w in 𝓝[Hbar] (yR : ℂ), FR w ∈ H ∧ c₀R.2.1 (FR w) ∈ ball p ρ := by
    have h1 : Tendsto FR (𝓝[Hbar] (yR : ℂ)) (𝓝 (FR yR)) := (hFRc _ (hreal yR)).tendsto
    have h2 : Tendsto (fun w => c₀R.2.1 (FR w)) (𝓝[Hbar] (yR : ℂ)) (𝓝 (c₀R.2.1 (FR yR))) :=
      (hc₀Rcont _ hFRyH).tendsto.comp h1
    have hpR : c₀R.2.1 (FR yR) = p := by rw [hFyR]
    rw [hpR] at h2
    filter_upwards [h1.eventually (QuantumZipper.isOpen_H.mem_nhds hFRyH), h2.eventually (ball_mem_nhds _ hρ)]
      with w hw1 hw2
    exact ⟨hw1, hw2⟩
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhdsWithin_iff.1 hev
  have hgood : ∀ w ∈ Hbar ∩ ball (yR : ℂ) δ, FR w ∈ H ∧ c₀R.2.1 (FR w) ∈ ball p ρ := fun w hw =>
    hδsub ⟨hw.2, hw.1⟩
  have hxball : ∀ x ∈ Ioo (yR - δ) (yR + δ), (x : ℂ) ∈ ball (yR : ℂ) δ := fun x hx => by
    rw [mem_ball, dist_eq_norm, ← ofReal_sub, norm_real, Real.norm_eq_abs, abs_lt]
    constructor <;> linarith [hx.1, hx.2]
  have hinvR : ∀ w ∈ H, (c₀R.loewner WR τR).2.1 w = c₀R.2.1 (FR w) := fun w hw => by
    show c₀R.2.1 (fwdMapInv WR τR w) = c₀R.2.1 (FR w)
    rw [hFRdef, ZhanGT4.extendFrom_eq_fwdMapInv hWR hWR0 hτR0 hw]
  refine nonempty_sideIdentification_of_later (Λ := fun z => c₀R.2.1 (FR z)) (hc₀R.loewner hWR hWR0 hτR0) hc₀L
    hηL hWL hWL0 htL htτL hinjL hHL hyL hFyL ⟨δ, hδ, fun x hx => ?_⟩ ⟨δ, hδ, fun x hx => ?_⟩
    ⟨δ, hδ, fun z hz => ?_⟩ (by show c₀R.2.1 (FR yR) = _; rw [hFyR]; exact hp) ⟨-yR, by linarith, fun x hx => ?_⟩
  · -- the landing
    have hgx := hgood x ⟨hreal x, hxball x hx⟩
    have h1 : Tendsto FR (𝓝[H] (x : ℂ)) (𝓝 (FR x)) :=
      ((hFRc _ (hreal x)).tendsto).mono_left (nhdsWithin_mono _ QuantumZipper.H_subset_Hbar)
    refine ((hc₀Rcont _ hgx.1).tendsto.comp h1).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact (hinvR w hw).symm
  · -- the landing points are trace points of `ηˡ`
    have hgx := hgood x ⟨hreal x, hxball x hx⟩
    obtain ⟨s, hs, hse⟩ : FR x ∈ ηR '' Icc 0 τR := by
      rcases WalkNorm.extendFrom_real_cases hηR hWR hWR0 hτR0 x with h | h
      · exact absurd hgx.1 (by show ¬ 0 < (FR x).im; rw [h]; exact lt_irrefl 0)
      · exact h
    have hsH : ηR s ∈ H := by rw [hse]; exact hgx.1
    obtain ⟨s', hs', hs'H, hs'e⟩ := hloc s hs hsH (by rw [hse]; exact ball_subset_ball (min_le_left _ _) hgx.2)
    exact ⟨s', hs', hs'H, by show c₀R.2.1 (FR x) = _; rw [← hse]; exact hs'e⟩
  · -- the domain
    have hb := (hgood z ⟨QuantumZipper.H_subset_Hbar hz.1, hz.2⟩).2
    exact hdom' z hz.1 (by rw [hinvR z hz.1]; exact ball_subset_ball (min_le_right _ _) hb)
  · -- later points
    obtain ⟨s, hs, hse⟩ := hlaterR x ⟨hx.1, by linarith [hx.2]⟩
    obtain ⟨s', hs', hs'e⟩ := hlater s hs
    exact ⟨s', hs', by show c₀R.2.1 (FR x) = _; rw [hse]; exact hs'e⟩

end Side

end InteractingSLE.Theorem14.WalkWords
