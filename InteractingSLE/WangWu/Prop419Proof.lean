/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.Prop419
import InteractingSLE.WangWu.PlanarDescent

/-!
# Wang–Wu Proposition 4.19 from the tail-contact facts of the seed lines

Packet PROVE-WW-B25. Source: Wang–Wu preprocessed document (ruling R31), Proposition 4.19 (L1655–L1708), route R2 of
`planning/handoffs/PROVE-WW-B21.md`.

For two heights `u₁ < u₂` with nonnegative words, let `β = γ_{u₁}` and `α = γ_{u₂}` be the seed lines of `h + u₁` and
`h + u₂`. In the slit domain `ℍ \ β[a, ∞)` the field `h + u₂` seen by `α` has right boundary data at least `λ`
(`b₀ + u₂ ≥ λ` on `ℝ₊`, `λ + (u₂ − u₁)` on the right side of `β`), so — through the two-slit chart of
`ℍ \ (α[0, t] ∪ β[a, ∞))`, in which the future of `α` is an `SLE₄(ρ)` word with nonnegative right cumulative weights —
`α` never first contacts the tail `β[a, ∞)` from the right side of `β` and never ends in it (Wang–Wu's Lemma 4.17
"forbidden boundary arcs", in the finite-word form of the two-slit chart).

* **`SeedTailStatement`** (named input; the probabilistic half): almost surely, for a dense set of heights `a`, the two
  seed lines satisfy `Descent.NoRightFirstContact` and `Descent.NoRightEscape` (hypotheses (H1)–(H2) of
  `Descent.disjoint_arcRange_rightSideOf_of_tails`).
* **`prop419Statement_of_seedTail`**: `SeedTailStatement → Prop419Statement` — the deterministic half is
  `Descent.disjoint_arcRange_rightSideOf_of_tails` (proved, `WangWu/PlanarDescent.lean`).
* **`SeedTailSmallStatement`** (named input, the same for gaps `u₂ − u₁ < λ` only) and
  **`prop419Statement_of_seedTailSmall`**: `SeedTailSmallStatement → Prop419Statement`. Couplings at intermediate
  heights exist on the same space (`exists_coupling_height`, from PROVE-WW-B20's
  `exists_isOptionalHullCoupling_twoSeed_of_field`), consecutive seed lines are ordered by the small case, and the order
  of proper arcs is transitive (`disjoint_rightSideOf_trans`, through the crosscut order). For gaps below `λ` the image
  word of the slit chart has all cumulative weights in `(−1, ∞)`.

`SeedTailStatement` is the exact remaining proposition of Proposition 4.19; its intended proof is the height-shifted
rerun of PROVE-WW-B12–B19's two-slit law (see `planning/handoffs/PROVE-WW-B25.md`). It is a conditional helper with a
distinct name and replaces no source theorem.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H)
open LQGMetric (DistOn TestOn)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.WangWu.SeedField

/-- **Named input: the tail-contact facts of two seed lines** (the probabilistic half of Proposition 4.19). For base
weights `(ρL; ρR)` and heights `u₁ < u₂` whose words are nonnegative, on every probability space carrying a field `h`
and optional hull couplings of these words with `h + u₁` and `h + u₂`: almost surely there is a set `D` of heights,
dense in `[0, ∞)`, such that for every `a ∈ D` the seed line `α` of height `u₂` neither first contacts the tail
`β([a, ∞))` of the seed line `β` of height `u₁` from the right side of `β` (away from the tip `β(a)`), nor ends in the
right side of `β` without meeting that tail. -/
def SeedTailStatement : Prop :=
  ∀ (rL rR u₁ u₂ : ℝ), u₁ < u₂ → 0 ≤ rL - u₂ / wwLambda → 0 ≤ rR + u₁ / wwLambda →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens)
      (𝓕₁ : Filtration ℝ≥0 mΩ) (W₁ : ℝ≥0 → Ω → ℝ) (VL₁ VR₁ : Fin 1 → ℝ≥0 → Ω → ℝ) (B₁ : ℝ≥0 → Ω → ℝ)
      (ζ₁ : Ω → ℝ≥0∞)
      (𝓕₂ : Filtration ℝ≥0 mΩ) (W₂ : ℝ≥0 → Ω → ℝ) (VL₂ VR₂ : Fin 1 → ℝ≥0 → Ω → ℝ) (B₂ : ℝ≥0 → Ω → ℝ)
      (ζ₂ : Ω → ℝ≥0∞),
      IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL - u₁ / wwLambda)
        (fun _ => rR + u₁ / wwLambda) P 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ (fun ω => Exist.flowField 0 u₁ (h ω)) →
      IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL - u₂ / wwLambda)
        (fun _ => rR + u₂ / wwLambda) P 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ (fun ω => Exist.flowField 0 u₂ (h ω)) →
      ∀ᵐ ω ∂P, ∃ D : Set ℝ, Descent.IsDenseAbove D ∧ ∀ a ∈ D,
        Descent.NoRightFirstContact (seedLine ζ₂ W₂ ω) (seedLine ζ₁ W₁ ω) a ∧
          Descent.NoRightEscape (seedLine ζ₂ W₂ ω) (seedLine ζ₁ W₁ ω) a

/-- **Proposition 4.19 from the tail-contact facts.** The seed line of the larger height lies to the left of the other
one: by `ae_isProperArc_seedLine` both are simple proper arcs, and the planar descent
`Descent.disjoint_arcRange_rightSideOf_of_tails` turns the tail-contact facts into the order. -/
theorem prop419Statement_of_seedTail (hS : SeedTailStatement.{u}) : Prop419Statement.{u} := by
  intro rL rR u₁ u₂ h12 hL hR Ω mΩ P _ h 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ hC₁ hC₂
  have hl : 0 < wwLambda := wwLambda_pos
  have hd : u₁ / wwLambda < u₂ / wwLambda := div_lt_div_of_pos_right h12 hl
  have hL₁ : 0 ≤ rL - u₁ / wwLambda := by linarith
  have hR₂ : 0 ≤ rR + u₂ / wwLambda := by linarith
  filter_upwards [ae_isProperArc_seedLine hL₁ hR hC₁, ae_isProperArc_seedLine hL hR₂ hC₂,
    hS rL rR u₁ u₂ h12 hL hR P h 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ hC₁ hC₂] with ω hβ hα hT
  obtain ⟨D, hD, hDa⟩ := hT
  exact Descent.disjoint_arcRange_rightSideOf_of_tails hα hβ hD (fun a ha => (hDa a ha).1)
    (fun a ha => (hDa a ha).2)


/-! ### Reduction to small height gaps -/

/-- **Named input for small gaps**: `SeedTailStatement` for heights `u₁ < u₂ < u₁ + λ` only. In the slit chart of
`ℍ \ β[a, ∞)` the field `h + u₂` then has the image word `(r_L', −r_L' − δ; r_R', −r_R' + δ)`,
`δ = (u₂ − u₁)/λ ∈ (0, 1)`, whose cumulative weights all exceed `−2` (`r_L', r_R' ≥ 0` the weights of `h + u₂`). -/
def SeedTailSmallStatement : Prop :=
  ∀ (rL rR u₁ u₂ : ℝ), u₁ < u₂ → u₂ - u₁ < wwLambda → 0 ≤ rL - u₂ / wwLambda → 0 ≤ rR + u₁ / wwLambda →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens)
      (𝓕₁ : Filtration ℝ≥0 mΩ) (W₁ : ℝ≥0 → Ω → ℝ) (VL₁ VR₁ : Fin 1 → ℝ≥0 → Ω → ℝ) (B₁ : ℝ≥0 → Ω → ℝ)
      (ζ₁ : Ω → ℝ≥0∞)
      (𝓕₂ : Filtration ℝ≥0 mΩ) (W₂ : ℝ≥0 → Ω → ℝ) (VL₂ VR₂ : Fin 1 → ℝ≥0 → Ω → ℝ) (B₂ : ℝ≥0 → Ω → ℝ)
      (ζ₂ : Ω → ℝ≥0∞),
      IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL - u₁ / wwLambda)
        (fun _ => rR + u₁ / wwLambda) P 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ (fun ω => Exist.flowField 0 u₁ (h ω)) →
      IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL - u₂ / wwLambda)
        (fun _ => rR + u₂ / wwLambda) P 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ (fun ω => Exist.flowField 0 u₂ (h ω)) →
      ∀ᵐ ω ∂P, ∃ D : Set ℝ, Descent.IsDenseAbove D ∧ ∀ a ∈ D,
        Descent.NoRightFirstContact (seedLine ζ₂ W₂ ω) (seedLine ζ₁ W₁ ω) a ∧
          Descent.NoRightEscape (seedLine ζ₂ W₂ ω) (seedLine ζ₁ W₁ ω) a

/-- The right side of a proper arc `β` lies in the right side of every proper arc `σ` to the left of `β`. -/
theorem rightSideOf_subset_of_disjoint {β σ : ℝ → ℂ} (hβ : IsProperArc β) (hσ : IsProperArc σ)
    (h : Disjoint (arcRange σ) (rightSideOf (arcRange β))) :
    rightSideOf (arcRange β) ⊆ rightSideOf (arcRange σ) := by
  intro z hz
  have hzH : z ∈ H := hz.1.1
  exact (hσ.mem_rightSideOf_iff hzH).2 (IsDiscCrosscut.crossSide_neg_subset_of_disjoint hβ.isDiscCrosscut_toDisc
    hσ.isDiscCrosscut_toDisc ((disjoint_rightSideOf_iff hβ hσ).1 h) ((hβ.mem_rightSideOf_iff hzH).1 hz))

/-- **The order of proper arcs is transitive.** -/
theorem disjoint_rightSideOf_trans {α σ β : ℝ → ℂ} (hβ : IsProperArc β) (hσ : IsProperArc σ)
    (hασ : Disjoint (arcRange α) (rightSideOf (arcRange σ))) (hσβ : Disjoint (arcRange σ) (rightSideOf (arcRange β))) :
    Disjoint (arcRange α) (rightSideOf (arcRange β)) :=
  hασ.mono_right (rightSideOf_subset_of_disjoint hβ hσ hσβ)

/-- An optional hull coupling at every height with a nonnegative word, on the space of a given one. -/
theorem exists_coupling_height {rL rR u₁ : ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
    (hh : IsGFFWithBoundaryData P (fun ω => Exist.flowField 0 u₁ (h ω))
      (forceBoundaryData 4 (fun _ : Fin 1 => rL - u₁ / wwLambda) (fun _ : Fin 1 => rR + u₁ / wwLambda)
        LP.twoSeedXL LP.twoSeedXR) (forceJumpSet LP.twoSeedXL LP.twoSeedXR))
    {v : ℝ} (hL : 0 ≤ rL - v / wwLambda) (hR : 0 ≤ rR + v / wwLambda) :
    ∃ (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL VR : Fin 1 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
      (ζ : Ω → ℝ≥0∞),
      IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL - v / wwLambda) (fun _ => rR + v / wwLambda)
        P 𝓕 W VL VR B ζ (fun ω => Exist.flowField 0 v (h ω)) := by
  have hs := isGFFWithBoundaryData_twoSeed_shift hh (v - u₁)
  have ef : (fun ω => Exist.flowField 0 (v - u₁) (Exist.flowField 0 u₁ (h ω))) =
      fun ω => Exist.flowField 0 v (h ω) := by
    funext ω
    rw [Sec5.GlueCond.flowField_zero_flowField_zero, sub_add_cancel]
  have eL : (fun _ : Fin 1 => rL - u₁ / wwLambda - (v - u₁) / wwLambda) = fun _ => rL - v / wwLambda := by
    funext _
    rw [sub_div]
    ring
  have eR : (fun _ : Fin 1 => rR + u₁ / wwLambda + (v - u₁) / wwLambda) = fun _ => rR + v / wwLambda := by
    funext _
    rw [sub_div]
    ring
  rw [ef, eL, eR] at hs
  exact exists_isOptionalHullCoupling_twoSeed_of_field hL hR hs

/-- **Proposition 4.19 from its small-gap case.** Couplings at intermediate heights exist on the same space
(`exists_coupling_height`), the small-gap case orders consecutive seed lines (planar descent), and the order is
transitive (`disjoint_rightSideOf_trans`). -/
theorem prop419Statement_of_seedTailSmall (hS : SeedTailSmallStatement.{u}) : Prop419Statement.{u} := by
  intro rL rR u₁ u₂ h12 hL hR Ω mΩ P _ h 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ hC₁ hC₂
  have hl : 0 < wwLambda := wwLambda_pos
  have hh₁ : IsGFFWithBoundaryData P (fun ω => Exist.flowField 0 u₁ (h ω))
      (forceBoundaryData 4 (fun _ : Fin 1 => rL - u₁ / wwLambda) (fun _ : Fin 1 => rR + u₁ / wwLambda)
        LP.twoSeedXL LP.twoSeedXR) (forceJumpSet LP.twoSeedXL LP.twoSeedXR) := ⟨hC₁.2.1, hC₁.2.2.1⟩
  have hdiv : ∀ {a b : ℝ}, a ≤ b → a / wwLambda ≤ b / wwLambda := fun hab => div_le_div_of_nonneg_right hab hl.le
  -- the chain statement, by induction on the number of steps
  have key : ∀ n : ℕ, ∀ a b : ℝ, a < b → b - a < (n + 1) * wwLambda → u₁ ≤ a → b ≤ u₂ →
      ∀ (𝓕a : Filtration ℝ≥0 mΩ) (Wa : ℝ≥0 → Ω → ℝ) (VLa VRa : Fin 1 → ℝ≥0 → Ω → ℝ) (Ba : ℝ≥0 → Ω → ℝ)
        (ζa : Ω → ℝ≥0∞)
        (𝓕b : Filtration ℝ≥0 mΩ) (Wb : ℝ≥0 → Ω → ℝ) (VLb VRb : Fin 1 → ℝ≥0 → Ω → ℝ) (Bb : ℝ≥0 → Ω → ℝ)
        (ζb : Ω → ℝ≥0∞),
        IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL - a / wwLambda)
          (fun _ => rR + a / wwLambda) P 𝓕a Wa VLa VRa Ba ζa (fun ω => Exist.flowField 0 a (h ω)) →
        IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL - b / wwLambda)
          (fun _ => rR + b / wwLambda) P 𝓕b Wb VLb VRb Bb ζb (fun ω => Exist.flowField 0 b (h ω)) →
        ∀ᵐ ω ∂P, Disjoint (arcRange (seedLine ζb Wb ω)) (rightSideOf (arcRange (seedLine ζa Wa ω))) := by
    -- the small step
    have small : ∀ a b : ℝ, a < b → b - a < wwLambda → u₁ ≤ a → b ≤ u₂ →
        ∀ (𝓕a : Filtration ℝ≥0 mΩ) (Wa : ℝ≥0 → Ω → ℝ) (VLa VRa : Fin 1 → ℝ≥0 → Ω → ℝ) (Ba : ℝ≥0 → Ω → ℝ)
          (ζa : Ω → ℝ≥0∞)
          (𝓕b : Filtration ℝ≥0 mΩ) (Wb : ℝ≥0 → Ω → ℝ) (VLb VRb : Fin 1 → ℝ≥0 → Ω → ℝ) (Bb : ℝ≥0 → Ω → ℝ)
          (ζb : Ω → ℝ≥0∞),
          IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL - a / wwLambda)
            (fun _ => rR + a / wwLambda) P 𝓕a Wa VLa VRa Ba ζa (fun ω => Exist.flowField 0 a (h ω)) →
          IsOptionalHullCoupling 4 LP.twoSeedXL LP.twoSeedXR (fun _ => rL - b / wwLambda)
            (fun _ => rR + b / wwLambda) P 𝓕b Wb VLb VRb Bb ζb (fun ω => Exist.flowField 0 b (h ω)) →
          ∀ᵐ ω ∂P, Disjoint (arcRange (seedLine ζb Wb ω)) (rightSideOf (arcRange (seedLine ζa Wa ω))) := by
      intro a b hab hsmall ha hb 𝓕a Wa VLa VRa Ba ζa 𝓕b Wb VLb VRb Bb ζb hCa hCb
      have hLa : 0 ≤ rL - a / wwLambda := by linarith [hdiv (hab.le.trans hb)]
      have hLb : 0 ≤ rL - b / wwLambda := by linarith [hdiv hb]
      have hRa : 0 ≤ rR + a / wwLambda := by linarith [hdiv ha]
      have hRb : 0 ≤ rR + b / wwLambda := by linarith [hdiv (ha.trans hab.le)]
      filter_upwards [ae_isProperArc_seedLine hLa hRa hCa, ae_isProperArc_seedLine hLb hRb hCb,
        hS rL rR a b hab hsmall hLb hRa P h 𝓕a Wa VLa VRa Ba ζa 𝓕b Wb VLb VRb Bb ζb hCa hCb] with ω hβ hα hT
      obtain ⟨D, hD, hDa⟩ := hT
      exact Descent.disjoint_arcRange_rightSideOf_of_tails hα hβ hD (fun a ha => (hDa a ha).1)
        (fun a ha => (hDa a ha).2)
    intro n
    induction n with
    | zero =>
      intro a b hab hba ha hb
      exact small a b hab (by simpa using hba) ha hb
    | succ n ih =>
      intro a b hab hba ha hb 𝓕a Wa VLa VRa Ba ζa 𝓕b Wb VLb VRb Bb ζb hCa hCb
      by_cases hsm : b - a < wwLambda
      · exact small a b hab hsm ha hb 𝓕a Wa VLa VRa Ba ζa 𝓕b Wb VLb VRb Bb ζb hCa hCb
      push Not at hsm
      -- an intermediate height `v`
      set e := max (b - a - (n + 1) * wwLambda) 0 with he
      have he0 : 0 ≤ e := le_max_right _ _
      have heL : e < wwLambda := max_lt (by push_cast at hba; linarith) hl
      set v := a + (wwLambda + e) / 2 with hv
      have hav : a < v := by rw [hv]; linarith
      have hvb : v < b := by rw [hv]; linarith
      have hva : v - a < wwLambda := by rw [hv]; linarith
      have hbv : b - v < (n + 1) * wwLambda := by
        have : b - a - (n + 1) * wwLambda ≤ e := le_max_left _ _
        rw [hv]; linarith
      have hLv : 0 ≤ rL - v / wwLambda := by linarith [hdiv (hvb.le.trans hb)]
      have hRv : 0 ≤ rR + v / wwLambda := by linarith [hdiv (ha.trans hav.le)]
      obtain ⟨𝓕v, Wv, VLv, VRv, Bv, ζv, hCv⟩ := exists_coupling_height hh₁ hLv hRv
      have hLa : 0 ≤ rL - a / wwLambda := by linarith [hdiv (hab.le.trans hb)]
      have hRa : 0 ≤ rR + a / wwLambda := by linarith [hdiv ha]
      filter_upwards [small a v hav hva ha (hvb.le.trans hb) 𝓕a Wa VLa VRa Ba ζa 𝓕v Wv VLv VRv Bv ζv hCa hCv,
        ih v b hvb hbv (ha.trans hav.le) hb 𝓕v Wv VLv VRv Bv ζv 𝓕b Wb VLb VRb Bb ζb hCv hCb,
        ae_isProperArc_seedLine hLa hRa hCa, ae_isProperArc_seedLine hLv hRv hCv] with ω hav' hvb' hβ hσ
      exact disjoint_rightSideOf_trans hβ hσ hvb' hav'
  obtain ⟨n, hn⟩ := exists_nat_gt ((u₂ - u₁) / wwLambda)
  have hn' : u₂ - u₁ < (n + 1) * wwLambda := by
    have := (div_lt_iff₀ hl).1 hn
    nlinarith
  exact key n u₁ u₂ h12 hn' le_rfl le_rfl 𝓕₁ W₁ VL₁ VR₁ B₁ ζ₁ 𝓕₂ W₂ VL₂ VR₂ B₂ ζ₂ hC₁ hC₂

end InteractingSLE.WangWu.SeedField
