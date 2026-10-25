import SupercriticalLQGUniqueness.Uniqueness.Measurability.FiniteFieldEvents.StableCode




 
set_option autoImplicit false
noncomputable section
open Set unitInterval
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.Measurability.FiniteFieldEvents

def SourceStable (D : LSCMetric) (P : ℝ → ℂ) (T : ℝ)
    (W : Set ℂ) (V : TopologicalSpace.Opens ℂ) (L : ℝ≥0∞) : Prop :=
  ∃ a b c d : ℝ, EndSaving.Interfaces.Excursion P T W V a b c d ∧
    ∃ (hb : P b ∈ W) (hc : P c ∈ W),
      L ≤ D.internal W (⟨P b, hb⟩, ⟨P c, hc⟩)

theorem scaled_time_pos_of_unitExcursion
    (P : ℝ → ℂ) (T : ℝ) (R : Measurability.GeodesicCodes.Path) (hT : 0 ≤ T)
    (hscaled : ∀ q : unitInterval, R q = P (T * (q : ℝ)))
    (W : Set ℂ) (hW : IsOpen W) (V : TopologicalSpace.Opens ℂ)
    (hVW : closure (V : Set ℂ) ⊆ W) (q : Fin 5 → ℝ)
    (hcode : UnitExcursion W V (R, q)) : 0 < T := by
  by_contra hn
  have hzero : T = 0 := le_antisymm (le_of_not_gt hn) hT
  have hconst (t : ℝ) : (unitExtension R) t = P 0 := by
    change R (projIcc 0 1 zero_le_one t) = P 0
    rw [hscaled, hzero, zero_mul]
  have hcode' := hcode.2
  rcases hcode' with ⟨_, _, _, _, _, hf, _, _, hV, _, _, _⟩
  have hdisj : Disjoint (frontier W) W := (disjoint_frontier_iff_isOpen).2 hW
  have hsame : (unitExtension R) (q 1) = (unitExtension R) (q 2) := by
    rw [hconst, hconst]
  exact Set.disjoint_left.mp hdisj hf (hsame ▸ hVW hV)

theorem sourceStable_congr_on (D : LSCMetric) (P Q : ℝ → ℂ) (T : ℝ)
    (W : Set ℂ) (V : TopologicalSpace.Opens ℂ) (L : ℝ≥0∞)
    (h : Set.EqOn P Q (Icc 0 T)) :
    SourceStable D P T W V L ↔ SourceStable D Q T W V L := by
  have forward (A B : ℝ → ℂ) (hab : Set.EqOn A B (Icc 0 T)) :
      SourceStable D A T W V L → SourceStable D B T W V L := by
    rintro ⟨a, b, c, d, hex, hbW, hcW, hcost⟩
    rcases hex with ⟨h0, hab₁, hbc, hcd, hdT, hf1, hf2, hin, hV1, hV2, hno1, hno2⟩
    have hexA : EndSaving.Interfaces.Excursion A T W V a b c d :=
      ⟨h0, hab₁, hbc, hcd, hdT, hf1, hf2, hin, hV1, hV2, hno1, hno2⟩
    have hb : b ∈ Icc 0 T := ⟨h0.trans hab₁, hbc.trans (hcd.trans hdT)⟩
    have hc : c ∈ Icc 0 T := ⟨h0.trans (hab₁.trans hbc), hcd.trans hdT⟩
    have hAb : A b = B b := hab hb
    have hAc : A c = B c := hab hc
    have hBb : B b ∈ W := hAb ▸ hbW
    have hBc : B c ∈ W := hAc ▸ hcW
    refine ⟨a, b, c, d, (excursion_congr_on A B T W V a b c d hab).1 hexA,
      hBb, hBc, ?_⟩
    simpa only [← hAb, ← hAc] using hcost
  exact ⟨forward P Q h, forward Q P h.symm⟩

theorem sourceStable_iff_codedStable_of_scaled
    (D : LSCMetric) (hforget : Continuous (Measurability.SetGeodesicCodes.euclidForget D))
    (P : ℝ → ℂ) (T : ℝ) (R : Measurability.GeodesicCodes.Path) (hT : 0 < T)
    (hscaled : ∀ q : unitInterval, R q = P (T * (q : ℝ)))
    (W : Set ℂ) (hW : IsOpen W) (hWne : Wᶜ.Nonempty)
    (V : TopologicalSpace.Opens ℂ) (hVW : closure (V : Set ℂ) ⊆ W)
    (L : ℝ≥0∞) :
    SourceStable D P T W V L ↔ CodedStable W V L (D, R) := by
  constructor
  · rintro ⟨a, b, c, d, hex, hbW, hcW, hcost⟩
    have hbc : b ∈ Icc 0 T := by
      rcases hex with ⟨h0, hab, hbc, hcd, hdT, _⟩
      exact ⟨h0.trans hab, hbc.trans (hcd.trans hdT)⟩
    have hcc : c ∈ Icc 0 T := by
      rcases hex with ⟨h0, hab, hbc, hcd, hdT, _⟩
      exact ⟨h0.trans (hab.trans hbc), hcd.trans hdT⟩
    refine ⟨normalizedExcursionTimes T a b c d, ?_, ?_⟩
    · exact (excursion_iff_unitExcursion_of_scaled P T R hT hscaled W V a b c d).1 hex
    · rw [excursionInternalProxy_eq_internal_of_scaled D hforget hW hWne
        P T R hT hscaled a b c d hbc hcc hbW hcW]
      exact hcost
  · rintro ⟨q, hcode, hcost⟩
    let a : ℝ := T * q 1
    let b : ℝ := T * q 2
    let c : ℝ := T * q 3
    let d : ℝ := T * q 4
    have hdiv (x : ℝ) : T * x / T = x := by field_simp
    have hnorm : UnitExcursion W V (R, normalizedExcursionTimes T a b c d) := by
      have hq0 : q 0 = 1 := hcode.1
      have hx : EndSaving.Interfaces.Excursion (unitExtension R) 1 W V
          (q 1) (q 2) (q 3) (q 4) := by
        simpa only [hq0] using hcode.2
      change (1 : ℝ) = 1 ∧ EndSaving.Interfaces.Excursion (unitExtension R) 1 W V
        (a / T) (b / T) (c / T) (d / T)
      refine ⟨rfl, ?_⟩
      dsimp [a, b, c, d]
      simpa only [hdiv] using hx
    have hex := (excursion_iff_unitExcursion_of_scaled
      P T R hT hscaled W V a b c d).2 hnorm
    have hbW : P b ∈ W := hVW hex.2.2.2.2.2.2.2.2.1
    have hcW : P c ∈ W := hVW hex.2.2.2.2.2.2.2.2.2.1
    have hbc : b ∈ Icc 0 T := by
      rcases hex with ⟨h0, hab, hbc, hcd, hdT, _⟩
      exact ⟨h0.trans hab, hbc.trans (hcd.trans hdT)⟩
    have hcc : c ∈ Icc 0 T := by
      rcases hex with ⟨h0, hab, hbc, hcd, hdT, _⟩
      exact ⟨h0.trans (hab.trans hbc), hcd.trans hdT⟩
    refine ⟨a, b, c, d, hex, hbW, hcW, ?_⟩
    have hscalar := excursionInternalProxy_eq_internal_of_scaled
      D hforget hW hWne P T R hT hscaled a b c d hbc hcc hbW hcW
    have hq : q = normalizedExcursionTimes T a b c d := by
      funext i
      fin_cases i
      · exact hcode.1
      all_goals simp [normalizedExcursionTimes, a, b, c, d, hdiv]
    rw [hq] at hcost
    rw [hscalar] at hcost
    exact hcost

end SupercriticalLQGUniqueness.Uniqueness.Measurability.FiniteFieldEvents
