/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootW8Margins
import InteractingSLE.Spec.Supplement.GW2RootN4Family

/-!
# Near-crossing models from qualitative word data

Continuation of PROVE-T14-GW2ROOT2. Finite-word convergence and strict inner
partial sums at the limit suffice: the uniform DS1 constants are constructed
on a tail. Both orientations keep their exact far cutoffs and total weights.
The actual retained-law identification remains outside this construction.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootW8

open RootN4 Supp12.DSReach CS3Cross

/-- Qualitative finite-force family data. The uniform weight bound and
positive DS1 margin are deliberately absent: they are proved from the
strict limiting partial sums and convergence. No crossing estimate is a field. -/
structure QualitativeFamily (κ : ℝ) where
  nL : ℕ
  nR : ℕ
  hnL : 0 < nL
  hnR : 0 < nR
  xL : Fin nL → ℝ
  xR : Fin nR → ℝ
  ρLs : ℕ → Fin nL → ℝ
  ρRs : ℕ → Fin nR → ℝ
  ρL₀ : Fin nL → ℝ
  ρR₀ : Fin nR → ℝ
  sequence : ℕ → EvolutionData.{u} nL nR
  limit : EvolutionData.{u} nL nR
  mL : ℕ
  mR : ℕ
  η : ℝ
  goLeft : Bool
  hη : 0 < η
  hxL0 : xL ⟨0, hnL⟩ = 0
  hxR0 : xR ⟨0, hnR⟩ = 0
  hxL : ∀ i, xL i ≠ 0 → xL i ≤ -η
  hxR : ∀ j, xR j ≠ 0 → η ≤ xR j
  hF : IsOrderedForceWord xL xR
  hpsL : ∀ i : Fin nL, (i : ℕ) < mL →
    -2 < ∑ j ∈ Finset.univ.filter (fun j => j ≤ i), ρL₀ j
  hpsR : ∀ i : Fin nR, (i : ℕ) < mR →
    -2 < ∑ j ∈ Finset.univ.filter (fun j => j ≤ i), ρR₀ j
  hρL : Tendsto ρLs atTop (𝓝 ρL₀)
  hρR : Tendsto ρRs atTop (𝓝 ρR₀)
  hE : ∀ m, (sequence m).IsEvolution κ xL (ρLs m) xR (ρRs m)
  hE₀ : limit.IsEvolution κ xL ρL₀ xR ρR₀
  horientation :
    (goLeft = true ∧ mR = nR - 1 ∧
      0 < xR ⟨nR - 1, Nat.sub_lt hnR one_pos⟩ ∧
      xL ⟨nL - 1, Nat.sub_lt hnL one_pos⟩ ≤ -3 ∧
      (∀ i : Fin nL, mL ≤ (i : ℕ) → xL i ≤ -3) ∧
      (∑ i, ρL₀ i) = κ - 4 ∧ (∑ j, ρR₀ j) = κ / 2 - 2) ∨
    (goLeft = false ∧ mL = nL - 1 ∧
      xL ⟨nL - 1, Nat.sub_lt hnL one_pos⟩ < 0 ∧
      3 ≤ xR ⟨nR - 1, Nat.sub_lt hnR one_pos⟩ ∧
      (∀ j : Fin nR, mR ≤ (j : ℕ) → 3 ≤ xR j) ∧
      (∑ j, ρR₀ j) = κ - 4 ∧ (∑ i, ρL₀ i) = κ / 2 - 2)

/-- The actual open-buffer reach probability, before any tail is selected. -/
def QualitativeFamily.crossProb {κ : ℝ} (q : QualitativeFamily.{u} κ)
    (m n : ℕ) : ℝ≥0∞ :=
  let e := q.sequence m
  e.P (reachEvent (n : ℝ≥0)
    (if q.goLeft then leftTarget else rightTarget)
    (if q.goLeft then leftBuf q.mL q.nR n else rightBuf q.nL q.mR n)
    e.W e.VL e.VR e.lifetime)

/-- A tail of the qualitative family has all fields of the existing
quantitative near-crossing family. Every process, law, position, target
and buffer is preserved, with only the sequence index shifted. -/
theorem QualitativeFamily.exists_nearFamily {κ : ℝ} (q : QualitativeFamily.{u} κ) :
    ∃ (N : ℕ) (f : NearCrossingFamily.{u} κ),
      ∀ m n, f.crossProb m n = q.crossProb (m + N) n := by
  obtain ⟨Rw, ε, hε, hw₀, N, hN⟩ := exists_ds1_tail q.hF q.hpsL q.hpsR q.hρL q.hρR
  let f : NearCrossingFamily.{u} κ :=
    { nL := q.nL
      nR := q.nR
      hnL := q.hnL
      hnR := q.hnR
      xL := q.xL
      xR := q.xR
      ρLs := fun m => q.ρLs (m + N)
      ρRs := fun m => q.ρRs (m + N)
      ρL₀ := q.ρL₀
      ρR₀ := q.ρR₀
      sequence := fun m => q.sequence (m + N)
      limit := q.limit
      mL := q.mL
      mR := q.mR
      Rw := Rw
      ε := ε
      η := q.η
      goLeft := q.goLeft
      hε := hε
      hη := q.hη
      hxL0 := q.hxL0
      hxR0 := q.hxR0
      hxL := q.hxL
      hxR := q.hxR
      hw := fun m => hN _ (Nat.le_add_left _ _)
      hw₀ := hw₀
      hρL := q.hρL.comp (tendsto_add_atTop_nat N)
      hρR := q.hρR.comp (tendsto_add_atTop_nat N)
      hE := fun m => q.hE (m + N)
      hE₀ := q.hE₀
      horientation := q.horientation }
  exact ⟨N, f, fun _ _ => rfl⟩

/-- One open buffer works eventually along the original qualitative
sequence. No uniform DS1 constants are assumed in this statement. -/
theorem QualitativeFamily.exists_buffer_eventually_lt {κ : ℝ}
    (q : QualitativeFamily.{u} κ) (h13 : Exist.Theorem13Statement.{u})
    (hκ : 0 < κ) (hκ4 : κ < 4) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ n : ℕ, ∀ᶠ m in atTop, 1 - δ < q.crossProb m n := by
  obtain ⟨N, f, heq⟩ := q.exists_nearFamily
  obtain ⟨n, hn⟩ := f.exists_buffer_eventually_lt h13 hκ hκ4 hδ
  have htail : ∀ᶠ m in atTop, 1 - δ < q.crossProb (m + N) n := by
    simpa only [heq] using hn
  refine ⟨n, ?_⟩
  have hmap : ∀ᶠ m in Filter.map (fun m => m + N) atTop,
      1 - δ < q.crossProb m n := htail
  simpa only [map_add_atTop_eq_nat] using hmap

/-- Actual candidate domination can be transferred after constructing the
DS1 tail. The candidate may depend on both word and buffer. -/
theorem QualitativeFamily.exists_lt_of_domination {κ : ℝ}
    (q : QualitativeFamily.{u} κ) (h13 : Exist.Theorem13Statement.{u})
    (hκ : 0 < κ) (hκ4 : κ < 4) {p : ℕ → ℝ≥0∞}
    (hdom : ∀ n, ∀ᶠ m in atTop, ∃ a, q.crossProb m n ≤ p a)
    {δ : ℝ≥0∞} (hδ : 0 < δ) : ∃ a, 1 - δ < p a := by
  obtain ⟨N, f, heq⟩ := q.exists_nearFamily
  apply f.exists_lt_of_domination h13 hκ hκ4 ?_ hδ
  intro n
  filter_upwards [(tendsto_add_atTop_nat N).eventually (hdom n)] with m hm
  obtain ⟨a, ha⟩ := hm
  exact ⟨a, (heq m n).trans_le ha⟩

end InteractingSLE.Theorem14.GW2TipSystem.RootW8
