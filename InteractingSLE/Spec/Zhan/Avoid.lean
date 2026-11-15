/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.AvoidClock
import InteractingSLE.Spec.Supplement.LPProbReflect

/-!
# Uniform avoidance of compact real intervals (`κ ≤ 4`)

Packet PROVE-ZHAN-B. Astra, *Formalization proofs and dependency audit* (`source/external/AstraIG1/`,
text dump L1336–1381, ruling R35), Lemma ("Uniform avoidance of compact real intervals"): **for separated
chordal force marks satisfying every side-prefix inequality `S_j ≥ c`, `c = κ/2 − 2 ≤ 0`, the entire trace
has positive distance from each compact interval `I ⊂ ℝ \ {0}`, almost surely.**

`IsIntegratedSLEEvolution.ae_avoid_compact`: for an integrated `SLE_κ(ρ)` evolution, `0 < κ ≤ 4`, of an
ordered word with every mark separated from the seed and admissible side partial sums, almost surely the
lifetime is infinite and every continuous generating trace `η` on `[0, ∞)` stays at a positive distance
from every compact `I ⊆ ℝ \ {0}`.

Proof: for `I` left of `0`, choose rationals `r₊ < r₋ < 0` with `I` and all left marks in between; the
strip clock is finite (`ae_stripClock_bounded`) and the height bound gives the distance
(`exists_pos_le_norm_sub_of_stripClock`). The right side follows by reflection (`z ↦ −z̄`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Finset
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Zhan

open QuantumZipper

variable {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}

/-- The reflected word is ordered. -/
theorem isOrderedForceWord_reflect (hF : IsOrderedForceWord xL xR) :
    IsOrderedForceWord (-xR) (-xL) :=
  ⟨fun _ _ h => neg_le_neg (hF.2.2.1 h), fun i => by simpa using hF.2.2.2 i,
    fun _ _ h => neg_le_neg (hF.1 h), fun i => by simpa using hF.2.1 i⟩

/-- **Admissibility is invariant under reflection.** -/
theorem hasAdmissiblePartialSums_reflect {k : ℝ} (hF : IsOrderedForceWord xL xR)
    (h : Sec4.HasAdmissiblePartialSums k ρL ρR xL xR) :
    Sec4.HasAdmissiblePartialSums k ρR ρL (-xR) (-xL) := by
  constructor
  · intro x hx hex
    -- the largest right mark strictly below `−x`
    have hne : (univ.filter fun i => xR i < -x).Nonempty := by
      obtain ⟨i, hi⟩ := hex
      exact ⟨i, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; simp only [Pi.neg_apply] at hi; linarith⟩
    obtain ⟨i₀, hi₀, hmax⟩ := (univ.filter fun i => xR i < -x).exists_max_image xR hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi₀ hmax
    have hset : (univ.filter fun i => x < (-xR) i) = univ.filter fun i => xR i ≤ xR i₀ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.neg_apply]
      constructor
      · intro hi; exact hmax i (by linarith)
      · intro hi; linarith
    rw [hset]
    exact h.2 (xR i₀) (hF.2.2.2 i₀) ⟨i₀, le_rfl⟩
  · intro x hx hex
    obtain ⟨i₁, hi₁⟩ := hex
    simp only [Pi.neg_apply] at hi₁
    by_cases hT : (univ.filter fun i => xL i < -x).Nonempty
    · obtain ⟨j₀, hj₀, hmax⟩ := (univ.filter fun i => xL i < -x).exists_max_image xL hT
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj₀ hmax
      have hset : (univ.filter fun i => (-xL) i ≤ x) = univ.filter fun i => xL j₀ < xL i := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.neg_apply]
        constructor
        · intro hi; linarith
        · intro hi
          by_contra hc
          push Not at hc
          have := hmax i (by linarith)
          linarith
      rw [hset]
      exact h.1 (xL j₀) (by linarith) ⟨i₁, by linarith⟩
    · have hall : ∀ i, -x ≤ xL i := fun i => by
        by_contra hc
        push Not at hc
        exact hT ⟨i, by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hc⟩
      have hset : (univ.filter fun i => (-xL) i ≤ x) = univ.filter fun i => -x - 1 < xL i := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.neg_apply]
        constructor
        · intro _; linarith [hall i]
        · intro _; linarith [hall i]
      rw [hset]
      exact h.1 (-x - 1) (by linarith) ⟨i₁, by linarith⟩

theorem exists_bound_of_neg {n : ℕ} (f : Fin n → ℝ) (hf : ∀ i, f i < 0) :
    ∃ b < 0, ∀ i, f i ≤ b := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0; exact ⟨-1, by norm_num, fun i => i.elim0⟩
  · have : Nonempty (Fin n) := ⟨⟨0, hpos⟩⟩
    obtain ⟨i₀, hi₀⟩ := Finite.exists_max f
    exact ⟨f i₀, hf i₀, hi₀⟩

theorem exists_lower_bound {n : ℕ} (f : Fin n → ℝ) : ∃ a, ∀ i, a ≤ f i := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0; exact ⟨0, fun i => i.elim0⟩
  · have : Nonempty (Fin n) := ⟨⟨0, hpos⟩⟩
    obtain ⟨i₀, hi₀⟩ := Finite.exists_min f
    exact ⟨f i₀, hi₀⟩

section Avoid

variable {κ : ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}

/-- **Uniform avoidance, left side.** -/
theorem IsIntegratedSLEEvolution.ae_avoid_neg [IsProbabilityMeasure P] (hκ : 0 < κ) (hκ4 : κ ≤ 4)
    (hF : IsOrderedForceWord xL xR) (hadm : Sec4.HasAdmissiblePartialSums κ ρL ρR xL xR)
    (hxL : ∀ i, xL i < 0) (hxR : ∀ i, 0 < xR i)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η →
      ∀ I : Set ℝ, IsCompact I → (∀ x ∈ I, x < 0) →
        ∃ d > 0, ∀ t : ℝ≥0, ∀ x ∈ I, d ≤ ‖η t - x‖ := by
  have hclock : ∀ q : ℚ × ℚ, ∀ᵐ ω ∂P, (q.1 : ℝ) < q.2 → (q.2 : ℝ) < 0 →
      (∀ i, (q.1 : ℝ) ≤ xL i ∧ xL i ≤ q.2) → ∃ S : ℝ, ∀ t : ℝ, 0 ≤ t →
        ∫ s in (0 : ℝ)..t, stripRate (fun s => fwdMap (fun s : ℝ => W s.toNNReal ω) s ((q.2 : ℝ) : ℂ))
          (fun s => fwdMap (fun s : ℝ => W s.toNNReal ω) s ((q.1 : ℝ) : ℂ)) s ≤ S := fun q => by
    by_cases h : (q.1 : ℝ) < q.2 ∧ (q.2 : ℝ) < 0 ∧ ∀ i, (q.1 : ℝ) ≤ xL i ∧ xL i ≤ q.2
    · filter_upwards [IsIntegratedSLEEvolution.ae_stripClock_bounded hκ hκ4 hF hadm hxL hxR hE
        h.2.1 h.1 h.2.2] with ω hω
        _ _ _ using hω
    · exact Eventually.of_forall fun ω h1 h2 h3 => absurd ⟨h1, h2, h3⟩ h
  filter_upwards [ae_all_iff.2 hclock,
    hE.ae_real_alive_of_hasAdmissiblePartialSums hκ hκ4 hF hadm hxL hxR, hE.2.2.2.2]
    with ω hcl hal hp
  refine ⟨hal.1, fun η hη I hI hIneg => ?_⟩
  have hwc : Continuous (W · ω) := by
    rw [← continuousOn_univ]
    exact hp.2.2.2.1.mono fun t _ => show (t : ℝ≥0∞) < ζ ω by rw [hal.1]; exact ENNReal.coe_lt_top
  have hw : Continuous fun s : ℝ => W s.toNNReal ω := hwc.comp continuous_real_toNNReal
  have hw0 : W 0 ω = 0 := hp.1
  -- an upper bound `< 0` for `I` and the left marks
  obtain ⟨b₂, hb₂, hxb⟩ := exists_bound_of_neg xL hxL
  obtain ⟨b₁, hb₁, hIb⟩ : ∃ b₁ < 0, ∀ x ∈ I, x ≤ b₁ := by
    rcases I.eq_empty_or_nonempty with he | hne
    · exact ⟨-1, by norm_num, fun x hx => by rw [he] at hx; exact hx.elim⟩
    · exact ⟨sSup I, hIneg _ (hI.sSup_mem hne), fun x hx => le_csSup hI.bddAbove hx⟩
  obtain ⟨q₂, hq₂l, hq₂r⟩ := exists_rat_btwn (max_lt hb₁ hb₂)
  -- a lower bound
  obtain ⟨a₁, ha₁⟩ := hI.bddBelow
  obtain ⟨a₂, ha₂⟩ := exists_lower_bound xL
  obtain ⟨q₁, hq₁⟩ := exists_rat_lt (min (min a₁ a₂) (q₂ : ℝ))
  have h12 : (q₁ : ℝ) < q₂ := lt_of_lt_of_le hq₁ (min_le_right _ _)
  have hq1a1 : (q₁ : ℝ) < a₁ := lt_of_lt_of_le hq₁ ((min_le_left _ _).trans (min_le_left _ _))
  have hq1a2 : (q₁ : ℝ) < a₂ := lt_of_lt_of_le hq₁ ((min_le_left _ _).trans (min_le_right _ _))
  have hmarks : ∀ i, (q₁ : ℝ) ≤ xL i ∧ xL i ≤ q₂ := fun i =>
    ⟨(hq1a2.trans_le (ha₂ i)).le, (hxb i).trans ((le_max_right _ _).trans hq₂l.le)⟩
  obtain ⟨S, hS⟩ := hcl (q₁, q₂) h12 hq₂r hmarks
  have hS' : ∀ t : ℝ, 0 ≤ t → ∫ s in (0 : ℝ)..t,
      stripRate (fun s => fwdMap (fun s : ℝ => W s.toNNReal ω) s ((q₂ : ℝ) : ℂ))
        (fun s => fwdMap (fun s : ℝ => W s.toNNReal ω) s ((q₁ : ℝ) : ℂ)) s ≤ S := hS
  have hA := hal.2 (q₂ : ℝ) (ne_of_lt hq₂r)
  have hC := hal.2 (q₁ : ℝ) (ne_of_lt (h12.trans hq₂r))
  refine exists_pos_le_norm_sub_of_stripClock (w := fun t => W t ω) hw hw0 h12 hq₂r hA hC hS' hη hI
    fun x hx => ⟨?_, ?_⟩
  · exact hq1a1.trans_le (ha₁ hx)
  · exact (hIb x hx).trans_lt ((le_max_left _ _).trans_lt hq₂l)

/-- **Uniform avoidance of compact real intervals** (`0 < κ ≤ 4`; Astra §3, Lemma "Uniform avoidance of
compact real intervals"). For an integrated `SLE_κ(ρ)` evolution of an ordered word with all marks
separated from the seed and admissible side partial sums, almost surely the lifetime is infinite and
every continuous generating trace on `[0, ∞)` has positive distance from every compact `I ⊆ ℝ \ {0}`. -/
theorem IsIntegratedSLEEvolution.ae_avoid_compact [IsProbabilityMeasure P] (hκ : 0 < κ)
    (hκ4 : κ ≤ 4) (hF : IsOrderedForceWord xL xR)
    (hadm : Sec4.HasAdmissiblePartialSums κ ρL ρR xL xR) (hxL : ∀ i, xL i < 0)
    (hxR : ∀ i, 0 < xR i) (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    ∀ᵐ ω ∂P, ζ ω = ⊤ ∧ ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) ⊤ η →
      ∀ I : Set ℝ, IsCompact I → (0 : ℝ) ∉ I →
        ∃ d > 0, ∀ t : ℝ≥0, ∀ x ∈ I, d ≤ ‖η t - x‖ := by
  have hL := IsIntegratedSLEEvolution.ae_avoid_neg hκ hκ4 hF hadm hxL hxR hE
  have hR := IsIntegratedSLEEvolution.ae_avoid_neg hκ hκ4 (isOrderedForceWord_reflect hF)
    (hasAdmissiblePartialSums_reflect hF hadm) (fun i => by simpa using hxR i)
    (fun i => by simpa using hxL i) hE.reflect
  filter_upwards [hL, hR] with ω hL hR
  refine ⟨hL.1, fun η hη I hI h0 => ?_⟩
  -- the left part
  obtain ⟨d₁, hd₁, h₁⟩ := hL.2 η hη (I ∩ Iic 0) (hI.inter_right isClosed_Iic) fun x hx =>
    lt_of_le_of_ne hx.2 fun h => h0 (h ▸ hx.1)
  -- the right part, by reflection
  set η' : ℝ≥0 → ℂ := fun t => LP.reflectC (η t) with hη'
  have hη'g : IsGeneratingTrace (fun t => (-W) t ω) ⊤ η' := LP.isGeneratingTrace_reflect hη
  set J : Set ℝ := (fun x => -x) '' (I ∩ Ici 0) with hJ
  have hJc : IsCompact J := (hI.inter_right isClosed_Ici).image continuous_neg
  obtain ⟨d₂, hd₂, h₂⟩ := hR.2 η' hη'g J hJc fun y hy => by
    obtain ⟨x, hx, rfl⟩ := hy
    have : 0 < x := lt_of_le_of_ne hx.2 fun h => h0 (h ▸ hx.1)
    linarith
  refine ⟨min d₁ d₂, lt_min hd₁ hd₂, fun t x hx => ?_⟩
  rcases le_total x 0 with hx0 | hx0
  · exact (min_le_left _ _).trans (h₁ t x ⟨hx, hx0⟩)
  · have hy : -x ∈ J := ⟨x, ⟨hx, hx0⟩, rfl⟩
    have h := h₂ t (-x) hy
    have hrefl : LP.reflectC (x : ℂ) = ((-x : ℝ) : ℂ) := by
      simp [LP.reflectC, Complex.conj_ofReal]
    have hiso : ‖η' t - ((-x : ℝ) : ℂ)‖ = ‖η t - x‖ := by
      rw [hη', ← hrefl, ← dist_eq_norm, ← dist_eq_norm, LP.isometry_reflectC.dist_eq]
    rw [hiso] at h
    exact (min_le_right _ _).trans h

end Avoid

end Zhan

end InteractingSLE
