/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SxCap
import InteractingSLE.Spec.Supplement.GW2JDetR6Stop

/-!
# GW2's stage identity: the physical-time cap rule

Packet PROVE-GW2-RELDET, ruling R106. To stop a GB6 version at the physical time `Δ` of the explored curve, read
JOINTDET's attained physical-capacity level rule (`GW2JDetR3.physicalCapacityStop`) along the relative driver, which
never dies (`timeCapRule`). It is a measurable path rule.

Along one sample, write `a` for the relative clock and `T_c` for the first contact. Assume `a` is a clock before
`T_c`, the version is covered by `a` before `T_c`, and the rational prefix capacities of the relative driver below
the stop `V` read the physical times. Then (`min_timeCapRule`)
`min(V, timeCapRule Δ) = min(V, capClock Δ)`, where `capClock Δ = a(Δ)` if `Δ < T_c` and `⊤` otherwise. So capping
`V` at `timeCapRule Δ` stops it at the relative clock of the physical time `Δ`, or leaves it alone if `Δ` comes after
`T_c`. Above `V` the rule reads a frozen driver and is only bounded below (`le_levelRule_of_runSup_lt`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2Rd

open Exist.StagedLaw Supp8.GB6.HullId Sec7.Lemma71I GW2JDetR3

/-- An attained-level rule is at least `u` if every running supremum before `u` is below the level. -/
theorem le_levelRule_of_runSup_lt {X E : Type*} {f : ℚ≥0 → X → (ℚ≥0 → E) → ℝ≥0∞} {a : ℝ≥0∞} {x : X}
    {c : ℚ≥0 → E} {u : ℝ≥0∞}
    (h : ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < u → runSup f x c ((q : ℝ≥0) : ℝ≥0∞) < a) :
    u ≤ levelRule f a x c := by
  classical
  have hinf : u ≤ levelInf f a x c := by
    refine le_iInf fun q => ?_
    split_ifs with hq
    · by_contra hlt
      exact absurd hq (not_le.2 (h q (lt_of_not_ge hlt)))
    · exact le_top
  unfold levelRule
  split_ifs
  · exact hinf
  · exact le_top

/-- **The physical-time cap rule**: the attained physical-capacity level rule at level `Δ`, along a path that never
dies. -/
def timeCapRule (s : ℝ≥0) (Δ : ℝ≥0∞) (x : RecData × (ℝ≥0 → ℝ)) : ℝ≥0∞ :=
  physicalCapacityStop s Δ x.1 (x.2, ⊤)

theorem killedCode_live (w : ℝ≥0 → ℝ) (q : ℚ≥0) : killedCode (w, ⊤) q = w q := by
  simp only [killedCode, ENNReal.coe_lt_top, ↓reduceIte]

theorem measurable_timeCapRule (s : ℝ≥0) (Δ : ℝ≥0∞) : Measurable (timeCapRule s Δ) := by
  have hg : Measurable fun x : RecData × (ℝ≥0 → ℝ) => (x.1, (x.2, (⊤ : ℝ≥0∞))) :=
    measurable_fst.prodMk (measurable_snd.prodMk measurable_const)
  have h := (measurable_physicalCapacityStop s Δ).comp hg
  exact h

theorem isPathRule_timeCapRule (s : ℝ≥0) (Δ : ℝ≥0∞) : IsPathRule (timeCapRule s Δ) := by
  intro r w w' hag
  simp only [timeCapRule, physicalCapacityStop] at hag ⊢
  exact levelRule_galmarino (f := prefixCapacity s) (a := Δ) (prefixCapacity_local s) r (killedCode (w, ⊤))
    (killedCode (w', ⊤)) fun q hq => by rw [killedCode_live, killedCode_live]; exact hag q hq

/-- The relative clock of the physical time `Δ` if `Δ` precedes the first contact, `⊤` otherwise. -/
def capClock (Tc : ℝ≥0∞) (a : ℝ≥0 → ℝ) (Δ : ℝ≥0) : ℝ≥0∞ :=
  if (Δ : ℝ≥0∞) < Tc then ENNReal.ofReal (a Δ) else ⊤

/-- **The time cap along one sample.** -/
theorem min_timeCapRule {s : ℝ≥0} {r : RecData} {w : ℝ≥0 → ℝ} {V Tc : ℝ≥0∞} {a : ℝ≥0 → ℝ} (ha0 : a 0 = 0)
    (ham : StrictMonoOn a {t | (t : ℝ≥0∞) < Tc}) (hac : ContinuousOn a {t | (t : ℝ≥0∞) < Tc})
    (hread : ∀ (q : ℚ≥0) (t : ℝ≥0), (t : ℝ≥0∞) < Tc → a t = ((q : ℝ≥0) : ℝ) → ((q : ℝ≥0) : ℝ≥0∞) ≤ V →
      prefixCapacity s q r (killedCode (w, ⊤)) = t)
    (hcov : ∀ u : ℝ≥0, (u : ℝ≥0∞) < V → ∃ t : ℝ≥0, (t : ℝ≥0∞) < Tc ∧ (u : ℝ) < a t) (Δ : ℝ≥0) :
    min V (timeCapRule s Δ (r, w)) = min V (capClock Tc a Δ) := by
  have hclk : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc → Restart.IsClockOn a (t : ℝ≥0∞) := fun t ht =>
    ⟨ha0, ham.mono fun u hu => lt_of_le_of_lt hu ht, hac.mono fun u hu => lt_of_le_of_lt hu ht,
      fun h => (ENNReal.coe_ne_top h).elim⟩
  have hcap : ∀ t : ℝ≥0, Restart.capLife a (t : ℝ≥0∞) = ENNReal.ofReal (a t) := fun t => by
    simp only [Restart.capLife, ENNReal.coe_ne_top, ↓reduceIte, ENNReal.toNNReal_coe]
  by_cases h1 : (Δ : ℝ≥0∞) < Tc ∧ ENNReal.ofReal (a Δ) ≤ V
  · -- before the stop: JOINTDET's identification of the level rule
    obtain ⟨hΔ, haV⟩ := h1
    have hf : ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) ≤ Restart.capLife a Δ →
        prefixCapacity s q r (killedCode (w, ⊤)) = (Restart.invClock a Δ q : ℝ≥0∞) := by
      intro q hq
      obtain ⟨hle, heq⟩ := (hclk Δ hΔ).invClock_spec hq
      exact hread q _ (lt_of_le_of_lt hle hΔ) heq ((hq.trans_eq (hcap Δ)).trans haV)
    have e : timeCapRule s Δ (r, w) = ENNReal.ofReal (a Δ) :=
      GW2JDetR6.physicalCapacityStop_eq_of_clock_prefix s Δ r (w, ⊤) (hclk Δ hΔ) hf
    simp only [capClock, hΔ, ↓reduceIte, e]
  · -- after the stop: the level is not reached before `V`
    have hV : min V (capClock Tc a Δ) = V := by
      unfold capClock
      split_ifs with hΔ
      · exact min_eq_left (not_le.1 fun h => h1 ⟨hΔ, h⟩).le
      · exact min_eq_left le_top
    rw [hV]
    refine min_eq_left (le_levelRule_of_runSup_lt fun q hq => ?_)
    obtain ⟨t, htT, hqt⟩ := hcov q hq
    have hqcap : ((q : ℝ≥0) : ℝ≥0∞) ≤ Restart.capLife a t := by
      rw [hcap t, ← ENNReal.ofReal_coe_nnreal]
      exact ENNReal.ofReal_le_ofReal hqt.le
    obtain ⟨htq, hatq⟩ := (hclk t htT).invClock_spec hqcap
    have htqΔ : Restart.invClock a t q < Δ := by
      by_contra hge
      replace hge := le_of_not_gt hge
      have hΔT : (Δ : ℝ≥0∞) < Tc := ((ENNReal.coe_le_coe.2 hge).trans htq).trans_lt htT
      have hVa : V < ENNReal.ofReal (a Δ) := not_le.1 fun h => h1 ⟨hΔT, h⟩
      have haΔ : a Δ ≤ a (Restart.invClock a t q) := ham.monotoneOn hΔT (htq.trans_lt htT) hge
      rw [hatq] at haΔ
      have h2 : ENNReal.ofReal (a Δ) ≤ ((q : ℝ≥0) : ℝ≥0∞) := by
        rw [← ENNReal.ofReal_coe_nnreal]
        exact ENNReal.ofReal_le_ofReal haΔ
      exact absurd (hq.trans (hVa.trans_le h2)) (lt_irrefl _)
    have hle : runSup (prefixCapacity s) r (killedCode (w, ⊤)) ((q : ℝ≥0) : ℝ≥0∞) ≤
        (Restart.invClock a t q : ℝ≥0∞) := by
      refine iSup_le fun q' => ?_
      split_ifs with hq'
      · have hq'cap : ((q' : ℝ≥0) : ℝ≥0∞) ≤ Restart.capLife a t := hq'.trans hqcap
        obtain ⟨htq', hatq'⟩ := (hclk t htT).invClock_spec hq'cap
        rw [hread q' _ (htq'.trans_lt htT) hatq' (hq'.trans hq.le)]
        exact ENNReal.coe_le_coe.2 ((hclk t htT).strictMonoOn_invClock.monotoneOn hq'cap hqcap
          (ENNReal.coe_le_coe.1 hq'))
      · exact zero_le
    exact hle.trans_lt (ENNReal.coe_lt_coe.2 htqΔ)

end InteractingSLE.Theorem14.GW2Rd
