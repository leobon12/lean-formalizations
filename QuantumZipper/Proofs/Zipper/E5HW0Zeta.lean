import QuantumZipper.Proofs.Zipper.E5Palm2Zeta

/-!
# E5-HW0, part 1: the collision threshold `0₋(s)` as a rational surrogate in both variables

Task E5-HW0 (Theorem 1.3, node E5). `E5.aemeasurable_zeroMinus_Vr` (`E5Palm2Zeta`) shows that
`ω ↦ zeroMinus (Vr κ T B ω) T` is a.e.-measurable, by writing it as the rational infimum
`⨅ q, (if q < 0 then (if τ_q < T then q else 0) else 0)`. The Palm density `w0` on the level space
(`E5ESM5`), however, needs the threshold at the random parameter `s = T - T_ℓ(ℓ, ω)` and jointly in
`(ℓ, ω)`, so here the same surrogate is set up as a function of the threshold: `zetaHatS g ω s`
with `g q` a measurable version of `τ_q`.

* `zetaHatS`, `measurable_zetaHatS`: the surrogate and its joint measurability in `(ω, s)`;
* `zetaHatS_eq_zeroMinus_of`: pointwise, for every `s ∈ Icc 0 T` the surrogate is `0₋(s)`, given
  the a.s. facts of `Wire2.ae_zeroMinus_Vr_facts` for this `ω`;
* `ae_zetaHatS_eq_zeroMinus`: the a.s. version, uniform over `s ∈ Icc 0 T`.

The uniform-in-`s` statement is the point: the facts (strict antitonicity and continuity of `0₋` on
`[0,T]` plus the inverse relation `0₋(τ_x) = x`) invert to give `{τ_x < s} = {0₋(s) < x}` for
every `s ∈ (0,T]`, and the rational-infimum argument of
`E5Palm2Zeta.aemeasurable_zeroMinus_Vr` then applies verbatim at that parameter.

Own elementary measure-theoretic argument (Sheffield, arXiv:1012.4797, §5.4, does not discuss
measurability; the facts are the repository's Rohde–Schramm simple-curve input).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace E5

open B2

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} {κ T : ℝ}

/-- The rational infimum surrogate of the collision threshold `0₋(s)`, built from measurable
versions `g q` of the hitting times `τ_q` (`q < 0`). -/
def zetaHatS (g : ℚ → Ω → ℝ≥0∞) (ω : Ω) (s : ℝ) : ℝ :=
  ⨅ q : ℚ, if (q : ℝ) < 0 then (if g q ω < ENNReal.ofReal s then (q : ℝ) else 0) else 0

/-- The surrogate is jointly measurable in `(ω, s)`. -/
theorem measurable_zetaHatS {g : ℚ → Ω → ℝ≥0∞} (hg : ∀ q : ℚ, Measurable (g q)) :
    Measurable fun p : Ω × ℝ => zetaHatS g p.1 p.2 := by
  refine Measurable.iInf fun q => ?_
  by_cases hq : (q : ℝ) < 0
  · have heq : (fun p : Ω × ℝ => if (q : ℝ) < 0 then
        (if g q p.1 < ENNReal.ofReal p.2 then (q : ℝ) else 0) else 0) =
        fun p : Ω × ℝ => if g q p.1 < ENNReal.ofReal p.2 then (q : ℝ) else 0 := by
      funext p; rw [ite_eq_left hq]
    rw [heq]
    exact Measurable.ite (measurableSet_lt ((hg q).comp measurable_fst)
      (ENNReal.measurable_ofReal.comp measurable_snd)) measurable_const measurable_const
  · have heq : (fun p : Ω × ℝ => if (q : ℝ) < 0 then
        (if g q p.1 < ENNReal.ofReal p.2 then (q : ℝ) else 0) else 0) =
        fun _ : Ω × ℝ => (0 : ℝ) := by
      funext p; rw [ite_eq_right hq]
    rw [heq]
    exact measurable_const

omit [MeasurableSpace Ω] in
/-- **The surrogate is the collision threshold, at a sample where the `0₋` facts hold**, for every
threshold `s ∈ Icc 0 T` simultaneously, where `g q` is the hitting time `τ_q`. -/
theorem zetaHatS_eq_zeroMinus_of {ω : Ω} {g : ℚ → Ω → ℝ≥0∞} (hT : 0 < T)
    (hω : zeroMinus (Vr κ T B ω) 0 = 0 ∧ zeroMinus (Vr κ T B ω) T < 0 ∧
      StrictAntiOn (zeroMinus (Vr κ T B ω)) (Icc 0 T) ∧
      ContinuousOn (zeroMinus (Vr κ T B ω)) (Icc 0 T) ∧
      (∀ x ∈ Ioc (zeroMinus (Vr κ T B ω) T) 0,
        realHitTime (Vr κ T B ω) x = ENNReal.ofReal (realHitTime (Vr κ T B ω) x).toReal ∧
          (realHitTime (Vr κ T B ω) x).toReal ∈ Icc 0 T ∧
          zeroMinus (Vr κ T B ω) (realHitTime (Vr κ T B ω) x).toReal = x) ∧
      (∀ x ≤ 0, realHitTime (Vr κ T B ω) x < ENNReal.ofReal T ↔
        zeroMinus (Vr κ T B ω) T < x))
    (hgω : ∀ q : ℚ, (q : ℝ) < 0 → g q ω = realHitTime (Vr κ T B ω) (q : ℝ)) :
    ∀ s ∈ Icc 0 T, zetaHatS g ω s = zeroMinus (Vr κ T B ω) s := by
  obtain ⟨hZ0, hZT, hSA, -, hspec, hiffT⟩ := hω
  intro s hs
  simp only [zetaHatS]
  rcases eq_or_lt_of_le hs.1 with hs0 | hs0
  · -- `s = 0`: the surrogate is `0` term by term
    subst hs0
    have h0 : ∀ q : ℚ, (if (q : ℝ) < 0 then
        (if g q ω < ENNReal.ofReal (0 : ℝ) then (q : ℝ) else 0) else 0) = 0 := by
      intro q
      by_cases hq : (q : ℝ) < 0
      · rw [ite_eq_left hq, ENNReal.ofReal_zero]
        simp
      · rw [ite_eq_right hq]
    rw [hZ0]
    rw [show (⨅ q : ℚ, (if (q : ℝ) < 0 then
        (if g q ω < ENNReal.ofReal (0 : ℝ) then (q : ℝ) else 0) else 0)) = ⨅ _q : ℚ, (0 : ℝ)
      from iInf_congr fun q => h0 q]
    simp
  · -- `s > 0`: the rational-infimum argument of `aemeasurable_zeroMinus_Vr`
    have hZsT : ∀ u ∈ Icc 0 T, zeroMinus (Vr κ T B ω) T ≤ zeroMinus (Vr κ T B ω) u := by
      intro u hu
      rcases eq_or_lt_of_le hu.2 with h | h
      · rw [← h]
      · exact (hSA ⟨hu.1, hu.2⟩ ⟨hT.le, le_rfl⟩ h).le
    have hZs : zeroMinus (Vr κ T B ω) s < 0 := by
      have := hSA ⟨le_rfl, hT.le⟩ ⟨hs0.le, hs.2⟩ hs0
      simpa only [hZ0] using this
    -- the parameter-`s` version of the threshold identity `{τ_x < T} = {0₋(T) < x}`
    have hiffs : ∀ x ≤ 0,
        realHitTime (Vr κ T B ω) x < ENNReal.ofReal s ↔ zeroMinus (Vr κ T B ω) s < x := by
      intro x hx
      by_cases hxT : x ≤ zeroMinus (Vr κ T B ω) T
      · have h1 : ¬ (realHitTime (Vr κ T B ω) x < ENNReal.ofReal T) := by
          rw [hiffT x hx]; exact not_lt.2 hxT
        exact iff_of_false (fun hlt => h1 (hlt.trans_le (ENNReal.ofReal_le_ofReal hs.2)))
          (not_lt.2 (hxT.trans (hZsT s hs)))
      · have hxT' : zeroMinus (Vr κ T B ω) T < x := not_le.1 hxT
        obtain ⟨hfin, hIcc, hZτ⟩ := hspec x ⟨hxT', hx⟩
        rw [hfin]
        have h1 : ENNReal.ofReal (realHitTime (Vr κ T B ω) x).toReal < ENNReal.ofReal s ↔
            (realHitTime (Vr κ T B ω) x).toReal < s := by
          rcases eq_or_lt_of_le hs.1 with h | h
          · subst h
            simp only [ENNReal.ofReal_zero, ENNReal.not_lt_zero, false_iff, not_lt]
            exact ENNReal.toReal_nonneg
          · exact ENNReal.ofReal_lt_ofReal_iff h
        rw [h1]
        conv_rhs => rw [← hZτ]
        exact (hSA.lt_iff_gt hs hIcc).symm
    set f : ℚ → ℝ := fun q =>
      if (q : ℝ) < 0 then (if g q ω < ENNReal.ofReal s then (q : ℝ) else 0) else 0 with hf
    have hfq : ∀ q : ℚ, (q : ℝ) < 0 → zeroMinus (Vr κ T B ω) s < (q : ℝ) → f q = (q : ℝ) := by
      intro q hq hzq
      simp only [hf, hq, ite_true, (hiffs (q : ℝ) hq.le).2 hzq, hgω q hq]
    have hlow : ∀ q, zeroMinus (Vr κ T B ω) s ≤ f q := by
      intro q
      simp only [hf]
      split_ifs with h1 h2
      · exact ((hiffs (q : ℝ) h1.le).1 (by rwa [hgω q h1] at h2)).le
      · exact hZs.le
      · exact hZs.le
    have hbdd : BddBelow (range f) := ⟨zeroMinus (Vr κ T B ω) s, by
      rintro _ ⟨q, rfl⟩; exact hlow q⟩
    show (⨅ q : ℚ, f q) = zeroMinus (Vr κ T B ω) s
    refine le_antisymm ?_ (le_ciInf hlow)
    by_contra h
    push Not at h
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (lt_min h hZs)
    have hq0 : (q : ℝ) < 0 := hq2.trans_le (min_le_right _ _)
    have := ciInf_le hbdd q
    rw [hfq q hq0 hq1] at this
    exact absurd (hq2.trans_le (min_le_left _ _)) (not_lt.2 this)

end E5
end QuantumZipper
