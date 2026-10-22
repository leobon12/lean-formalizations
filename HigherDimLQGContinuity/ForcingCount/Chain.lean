import HigherDimLQGContinuity.ForcingCount.Defs

/-!
# The chain bound along a path with disjoint special intervals

Packet Q9 (deterministic). A path `P` on `[a, c]` carries finitely many pairwise disjoint special time intervals
`[s i, t i]`; the distance between the end points of every special interval is bounded by a cost, and on every residual
interval (one whose open interior meets no special interval) by an additive length plus a constant error. The triangle
inequality along the alternating chain of residual and special intervals gives

`E(P a, P c) + ∑ len(special) ≤ len(a, c) + ∑ cost + (#T + 1) η`.

This one inequality is used twice: for the network saving of a selection (Part B `b:lem-lowmult`, (h1); `η = 0`) and
for the one source comparison (4.19) (`b:lem-upcount`, step (4)).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd e₁)

variable {d : ℕ}

/-- **The chain bound.** -/
theorem q9_chain {ι : Type*} [DecidableEq ι] (E : ContMetric d) (P : ℝ → Rd d)
    (len : ℝ → ℝ → ℝ≥0∞) (η : ℝ≥0∞) (s t : ι → ℝ) (cost : ι → ℝ≥0∞) :
    ∀ (T : Finset ι) (a c : ℝ), a ≤ c →
    (∀ i ∈ T, a ≤ s i ∧ s i ≤ t i ∧ t i ≤ c) →
    (∀ i ∈ T, ∀ j ∈ T, i ≠ j → t i < s j ∨ t j < s i) →
    (∀ u v w, a ≤ u → u ≤ v → v ≤ w → w ≤ c → len u v + len v w = len u w) →
    (∀ i ∈ T, ENNReal.ofReal (E.1 (P (s i), P (t i))) ≤ cost i) →
    (∀ u v, a ≤ u → u ≤ v → v ≤ c → (∀ i ∈ T, ∀ τ ∈ Ioo u v, τ ∉ Icc (s i) (t i)) →
        ENNReal.ofReal (E.1 (P u, P v)) ≤ len u v + η) →
    ENNReal.ofReal (E.1 (P a, P c)) + ∑ i ∈ T, len (s i) (t i) ≤
      len a c + ∑ i ∈ T, cost i + ((T.card : ℝ≥0∞) + 1) * η := by
  intro T
  induction T using Finset.strongInduction with
  | H T ih =>
    intro a c hac hT hdisj hadd hspec hres
    rcases T.eq_empty_or_nonempty with hTe | hTne
    · subst hTe
      have h := hres a c le_rfl hac le_rfl (by simp)
      simpa using h
    · obtain ⟨i₀, hi₀, hmin⟩ := T.exists_min_image s hTne
      obtain ⟨has, hst, htc⟩ := hT i₀ hi₀
      -- every other special interval starts after `t i₀`
      have hafter : ∀ j ∈ T.erase i₀, t i₀ < s j := by
        intro j hj
        have hjT := Finset.mem_of_mem_erase hj
        have hji : j ≠ i₀ := Finset.ne_of_mem_erase hj
        rcases hdisj i₀ hi₀ j hjT hji.symm with h | h
        · exact h
        · exfalso
          have h1 := hmin j hjT
          have h2 := (hT j hjT).2.1
          linarith
      have hsub : T.erase i₀ ⊂ T := Finset.erase_ssubset hi₀
      have hIH := ih (T.erase i₀) hsub (t i₀) c htc
        (fun j hj => ⟨(hafter j hj).le, (hT j (Finset.mem_of_mem_erase hj)).2⟩)
        (fun i hi j hj hij => hdisj i (Finset.mem_of_mem_erase hi) j (Finset.mem_of_mem_erase hj) hij)
        (fun u v w hu huv hvw hw => hadd u v w ((has.trans hst).trans hu) huv hvw hw)
        (fun i hi => hspec i (Finset.mem_of_mem_erase hi))
        (fun u v hu huv hv havoid => hres u v ((has.trans hst).trans hu) huv hv (by
          intro i hi τ hτ hτi
          by_cases hii : i = i₀
          · subst hii
            exact (not_le.2 (lt_of_le_of_lt hu hτ.1)) hτi.2
          · exact havoid i (Finset.mem_erase.2 ⟨hii, hi⟩) τ hτ hτi))
      -- the first residual interval `[a, s i₀]`
      have hres₀ := hres a (s i₀) le_rfl has (hst.trans htc) (by
        intro i hi τ hτ hτi
        have h1 := hmin i hi
        have h2 := hτi.1
        have h3 := hτ.2
        linarith)
      have hspec₀ := hspec i₀ hi₀
      -- the triangle inequality along `a → s i₀ → t i₀ → c`
      have htri : ENNReal.ofReal (E.1 (P a, P c)) ≤
          ENNReal.ofReal (E.1 (P a, P (s i₀))) + ENNReal.ofReal (E.1 (P (s i₀), P (t i₀))) +
            ENNReal.ofReal (E.1 (P (t i₀), P c)) := by
        have h1 := E.apply_triangle (P a) (P (s i₀)) (P c)
        have h2 := E.apply_triangle (P (s i₀)) (P (t i₀)) (P c)
        calc ENNReal.ofReal (E.1 (P a, P c))
            ≤ ENNReal.ofReal (E.1 (P a, P (s i₀)) + E.1 (P (s i₀), P (t i₀)) +
                E.1 (P (t i₀), P c)) := ENNReal.ofReal_le_ofReal (by linarith)
          _ ≤ _ := by
            refine (ENNReal.ofReal_add_le).trans ?_
            exact add_le_add ENNReal.ofReal_add_le le_rfl
      have hsumL : ∑ i ∈ T, len (s i) (t i) = len (s i₀) (t i₀) + ∑ i ∈ T.erase i₀, len (s i) (t i) :=
        (Finset.add_sum_erase T _ hi₀).symm
      have hsumC : ∑ i ∈ T, cost i = cost i₀ + ∑ i ∈ T.erase i₀, cost i :=
        (Finset.add_sum_erase T _ hi₀).symm
      have hcard : ((T.card : ℝ≥0∞) + 1) = ((T.erase i₀).card : ℝ≥0∞) + 1 + 1 := by
        rw [← Finset.card_erase_add_one hi₀]
        push_cast
        ring
      have hlen : len a c = len a (s i₀) + len (s i₀) (t i₀) + len (t i₀) c := by
        rw [hadd a (s i₀) (t i₀) le_rfl has hst htc, hadd a (t i₀) c le_rfl (has.trans hst) htc le_rfl]
      rw [hsumL, hsumC, hcard, hlen]
      calc ENNReal.ofReal (E.1 (P a, P c)) + (len (s i₀) (t i₀) + ∑ i ∈ T.erase i₀, len (s i) (t i))
          ≤ (len a (s i₀) + η) + cost i₀ + ENNReal.ofReal (E.1 (P (t i₀), P c)) +
              (len (s i₀) (t i₀) + ∑ i ∈ T.erase i₀, len (s i) (t i)) := by
            gcongr
            exact htri.trans (add_le_add (add_le_add hres₀ hspec₀) le_rfl)
        _ = (len a (s i₀) + len (s i₀) (t i₀) + η + cost i₀) +
              (ENNReal.ofReal (E.1 (P (t i₀), P c)) + ∑ i ∈ T.erase i₀, len (s i) (t i)) := by ring
        _ ≤ (len a (s i₀) + len (s i₀) (t i₀) + η + cost i₀) +
              (len (t i₀) c + ∑ i ∈ T.erase i₀, cost i + (((T.erase i₀).card : ℝ≥0∞) + 1) * η) := by
            gcongr
        _ = len a (s i₀) + len (s i₀) (t i₀) + len (t i₀) c + (cost i₀ + ∑ i ∈ T.erase i₀, cost i) +
              (((T.erase i₀).card : ℝ≥0∞) + 1 + 1) * η := by ring

/-- **The chain bound**, real-valued form (all costs and lengths finite). -/
theorem q9_chain_real {ι : Type*} [DecidableEq ι] (E : ContMetric d) (P : ℝ → Rd d)
    (len : ℝ → ℝ → ℝ) (η : ℝ) (s t : ι → ℝ) (cost : ι → ℝ) :
    ∀ (T : Finset ι) (a c : ℝ), a ≤ c →
    (∀ i ∈ T, a ≤ s i ∧ s i ≤ t i ∧ t i ≤ c) →
    (∀ i ∈ T, ∀ j ∈ T, i ≠ j → t i < s j ∨ t j < s i) →
    (∀ u v w, a ≤ u → u ≤ v → v ≤ w → w ≤ c → len u v + len v w = len u w) →
    (∀ i ∈ T, E.1 (P (s i), P (t i)) ≤ cost i) →
    (∀ u v, a ≤ u → u ≤ v → v ≤ c → (∀ i ∈ T, ∀ τ ∈ Ioo u v, τ ∉ Icc (s i) (t i)) →
        E.1 (P u, P v) ≤ len u v + η) →
    E.1 (P a, P c) + ∑ i ∈ T, len (s i) (t i) ≤ len a c + ∑ i ∈ T, cost i + ((T.card : ℝ) + 1) * η := by
  intro T
  induction T using Finset.strongInduction with
  | H T ih =>
    intro a c hac hT hdisj hadd hspec hres
    rcases T.eq_empty_or_nonempty with hTe | hTne
    · subst hTe
      have h := hres a c le_rfl hac le_rfl (by simp)
      simpa using h
    · obtain ⟨i₀, hi₀, hmin⟩ := T.exists_min_image s hTne
      obtain ⟨has, hst, htc⟩ := hT i₀ hi₀
      have hafter : ∀ j ∈ T.erase i₀, t i₀ < s j := by
        intro j hj
        have hjT := Finset.mem_of_mem_erase hj
        have hji : j ≠ i₀ := Finset.ne_of_mem_erase hj
        rcases hdisj i₀ hi₀ j hjT hji.symm with h | h
        · exact h
        · exfalso
          have h1 := hmin j hjT
          have h2 := (hT j hjT).2.1
          linarith
      have hsub : T.erase i₀ ⊂ T := Finset.erase_ssubset hi₀
      have hIH := ih (T.erase i₀) hsub (t i₀) c htc
        (fun j hj => ⟨(hafter j hj).le, (hT j (Finset.mem_of_mem_erase hj)).2⟩)
        (fun i hi j hj hij => hdisj i (Finset.mem_of_mem_erase hi) j (Finset.mem_of_mem_erase hj) hij)
        (fun u v w hu huv hvw hw => hadd u v w ((has.trans hst).trans hu) huv hvw hw)
        (fun i hi => hspec i (Finset.mem_of_mem_erase hi))
        (fun u v hu huv hv havoid => hres u v ((has.trans hst).trans hu) huv hv (by
          intro i hi τ hτ hτi
          by_cases hii : i = i₀
          · subst hii
            exact (not_le.2 (lt_of_le_of_lt hu hτ.1)) hτi.2
          · exact havoid i (Finset.mem_erase.2 ⟨hii, hi⟩) τ hτ hτi))
      have hres₀ := hres a (s i₀) le_rfl has (hst.trans htc) (by
        intro i hi τ hτ hτi
        have h1 := hmin i hi
        have h2 := hτi.1
        have h3 := hτ.2
        linarith)
      have hspec₀ := hspec i₀ hi₀
      have h1 := E.apply_triangle (P a) (P (s i₀)) (P c)
      have h2 := E.apply_triangle (P (s i₀)) (P (t i₀)) (P c)
      have hsumL : ∑ i ∈ T, len (s i) (t i) = len (s i₀) (t i₀) + ∑ i ∈ T.erase i₀, len (s i) (t i) :=
        (Finset.add_sum_erase T _ hi₀).symm
      have hsumC : ∑ i ∈ T, cost i = cost i₀ + ∑ i ∈ T.erase i₀, cost i :=
        (Finset.add_sum_erase T _ hi₀).symm
      have hcard : ((T.card : ℝ) + 1) = ((T.erase i₀).card : ℝ) + 1 + 1 := by
        rw [← Finset.card_erase_add_one hi₀]
        push_cast
        ring
      have hlen : len a c = len a (s i₀) + len (s i₀) (t i₀) + len (t i₀) c := by
        rw [hadd a (s i₀) (t i₀) le_rfl has hst htc, hadd a (t i₀) c le_rfl (has.trans hst) htc le_rfl]
      rw [hsumL, hsumC, hcard, hlen]
      nlinarith

end HigherDimLQGContinuity
