/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NbStmt

/-!
# F2b′'s successor: the stages without a piece, and the trivial version

Packet PROVE-AUX61-NOJUMP (round 21, D34). Two tools for `Nb.SB2LowerStageVersionStatement4`:

* `getElem?_replicate_pair`, **`flow_of_launch`**: the lower walk's program alternates flow instructions
  `(−π/2, ⊤)` (even indices) and connectors; a launch at `ℓ` happens only at a flow instruction, so the stage event at
  any other `ℓ` is empty (`stageEvent_eq_empty`);
* **`trivVersionS`**: the version with zero driver, clock and stops, which satisfies every clause of
  `Na.StageVersionS` on an empty live event.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC fwdHull)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Nc

open Restart Exist Exist.Staged Exist.StagedLaw Lv Ms Supp8.Q3Stop

/-! ### The walk program -/

theorem getElem?_replicate_pair {α : Type*} (a c : α) (n i : ℕ) :
    (List.replicate n [a, c]).flatten[i]? = if i < 2 * n then some (if i % 2 = 0 then a else c) else none := by
  induction n generalizing i with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, List.flatten_cons]
    rcases i with _ | _ | i
    · simp
    · simp; omega
    · have h := ih i
      simp only [List.cons_append, List.nil_append, List.getElem?_cons_succ]
      rw [h]
      have h2 : (i + 1 + 1) % 2 = i % 2 := by omega
      by_cases hi : i < 2 * n
      · have hi' : i + 1 + 1 < 2 * (n + 1) := by omega
        simp only [hi, hi', ↓reduceIte, h2]
      · have hi' : ¬ i + 1 + 1 < 2 * (n + 1) := by omega
        simp only [hi, hi', ↓reduceIte]

/-- **A launch of the lower walk happens only at a flow instruction `(θ, ⊤)`.** -/
theorem flow_of_launch {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {θ : ℝ} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {ℓ : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (ℓ + 1)).2.2.2.1 ℓ ≠ none) :
    ℓ < (boundaryWalkSpec b jumps θ true).2.2.length ∧
      (boundaryWalkSpec b jumps θ true).2.2[ℓ]? = some (Sum.inl (θ, ⊤)) := by
  obtain ⟨⟨c, θ'⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hl
  have h1 := (eq_launch_of_launches (κ := κ) (b := b) (jumps := jumps) _ D hcθ).1
  have hget : (boundaryWalkSpec b jumps θ true).2.2[ℓ]? =
      if ℓ < 2 * ((PiecewiseConstantBoundaryData.jumpSet b jumps).card + 1) then
        some (if ℓ % 2 = 0 then (Sum.inl (θ, ⊤) : Instr) else Sum.inr (Sum.inl true)) else none :=
    getElem?_replicate_pair _ _ _ _
  have hlen : ℓ < (boundaryWalkSpec b jumps θ true).2.2.length := by
    by_contra hn
    rw [not_lt, ← List.getElem?_eq_none_iff] at hn
    rw [hn] at h1
    exact (Option.some_ne_none _) h1.symm
  refine ⟨hlen, ?_⟩
  rw [hget] at h1 ⊢
  split_ifs at h1 ⊢ <;> simp_all

/-- **The stage event is empty at every stage that is not a flow instruction.** -/
theorem stageEvent_eq_empty {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u}
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (u : ℝ) (l : List (ℝ × ℝ≥0)) (k ℓ : ℕ)
    (hℓ : ¬ (ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length ∧
      (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤)))) :
    stageEvent κ b jumps E u l k ℓ = ∅ :=
  eq_empty_of_forall_notMem fun _ hω => hℓ (flow_of_launch hω.2)

/-! ### The trivial version on an empty live event -/

section Triv

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {κ ψ : ℝ} {P : Measure Ω} {𝓖 : Filtration ℝ≥0 mΩ}
  {A₁ A₂ : ℝ≥0 → Ω → Set ℂ} {Φ : Ω → Chart} {β₁ : Ω → BoundaryWord} {types : Set WordType} {pc : Ω → ℝ≥0 → ℂ}
  {tL : Ω → ℝ≥0} {L relLife : Ω → ℝ≥0∞}

omit mΩ in
theorem notMem_seedCell_empty {w : WordType} {ω : Ω} : ω ∉ seedCell κ ψ β₁ (∅ : Set Ω) w := fun h => h.1.1

/-- **The trivial version**: zero driver, clock and lifetime; every clause is vacuous or holds for constants. -/
def trivVersionG : Na.StageVersionG κ ψ P ∅ 𝓖 A₁ A₂ Φ β₁ types pc tL L where
  𝓗 := lineFiltC P 𝓖
  W := fun _ _ => 0
  a := fun _ _ => 0
  Λ := fun _ _ => 0
  marks_le := le_rfl
  W_zero := fun _ => rfl
  W_cont := fun _ => continuous_const
  W_adapted := fun _ => stronglyMeasurable_const
  clock_cont := fun _ => continuous_const
  clock_mono := fun _ => monotone_const
  clock_zero := fun _ => rfl
  clock_meas := fun _ => measurable_const
  timeChange := fun q D' hD' t => by
    by_cases hq : q = 0
    · subst hq
      have e : D' ∩ {ω | ((0 : ℝ≥0) : ℝ≥0∞) ≤ (0 : ℝ≥0∞)} = D' := by simp
      rw [e]
      exact (lineFiltC P 𝓖).mono (zero_le) _ hD'
    · have e : D' ∩ {ω | (q : ℝ≥0∞) ≤ (0 : ℝ≥0∞)} = ∅ := by
        ext ω
        simp only [mem_inter_iff, mem_ofPred_eq, nonpos_iff_eq_zero, ENNReal.coe_eq_zero, hq, and_false,
          mem_empty_iff_false]
      rw [e]
      exact @MeasurableSet.empty Ω (lineFiltC P 𝓖 t)
  reach := fun _ _ _ => Eventually.of_forall fun _ h => absurd h notMem_seedCell_empty
  reg := fun _ _ => Eventually.of_forall fun _ h => absurd h notMem_seedCell_empty
  safeS := fun _ _ _ t => by
    simp only [lt_self_iff_false, false_and, ofPred_false]; exact @MeasurableSet.empty Ω (lineFiltC P 𝓖 t)
  safeL := fun _ _ _ t => by
    simp only [lt_self_iff_false, false_and, ofPred_false]; exact @MeasurableSet.empty Ω (lineFiltC P 𝓖 t)
  hull := fun _ _ _ => Eventually.of_forall fun _ h => absurd h notMem_seedCell_empty
  trace := fun _ _ _ => Eventually.of_forall fun _ h => absurd h notMem_seedCell_empty
  alive := fun _ _ _ => Eventually.of_forall fun _ h => absurd h notMem_seedCell_empty
  Λ_le := fun _ _ => Eventually.of_forall fun _ h => absurd h notMem_seedCell_empty

/-- **The trivial versions at announced stops** on an empty live event. -/
def trivVersionS : Na.StageVersionS κ ψ P ∅ 𝓖 A₁ A₂ Φ β₁ types pc tL L relLife where
  ver := fun _ => trivVersionG
  V := fun _ _ => 0
  record := fun _ => (fun _ => 0, 0, true)
  record_meas := measurable_const
  ρ := fun _ _ => 0
  ρs := fun _ _ _ => 0
  ρ_meas := fun _ => measurable_const
  ρ_rule := fun _ _ _ _ _ => rfl
  ρs_meas := fun _ _ => measurable_const
  ρs_rule := fun _ _ _ _ _ _ => rfl
  ρs_fin := fun _ _ _ => ENNReal.zero_ne_top
  ρs_mono := fun _ _ => monotone_const
  Λ_eq := fun _ _ => rfl
  V_eq := fun _ _ => rfl
  ann := fun _ => Eventually.of_forall fun _ h => absurd h (notMem_empty _)
  V_lt := fun _ => Eventually.of_forall fun _ h => absurd h (notMem_empty _)
  V_mono := fun _ => monotone_const
  V_sup := Eventually.of_forall fun _ h => absurd h (notMem_empty _)
  W_eq := fun _ _ _ => Eventually.of_forall fun _ h => absurd h (notMem_empty _)

end Triv

end InteractingSLE.Theorem14.SB.Nc
