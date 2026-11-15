/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2TipStageCross

/-!
# Finite-force inputs for GW2 root crossing estimates

Continuation of PROVE-T14-GW2ROOT2. A `NearCrossingFamily` records integrated
evolutions and the concrete word hypotheses of TIP11, with either orientation.
Its construction for a retained root history remains a mathematical input.
The crossing probability estimate is proved from Theorem 1.3, rather than
included among those inputs. No assertion identifies these evolutions with
the actual next piece until the separate model identification is supplied.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootN4

open Supp12.DS2 Supp12.DSReach CS3Cross

/-- The processes and law of one finite-force evolution. The evolution
equations are stated separately in the family containing this data. -/
structure EvolutionData (nL nR : ℕ) where
  Ω : Type u
  mΩ : MeasurableSpace Ω
  P : @Measure Ω mΩ
  filtration : Filtration ℝ≥0 mΩ
  W : ℝ≥0 → Ω → ℝ
  VL : Fin nL → ℝ≥0 → Ω → ℝ
  VR : Fin nR → ℝ≥0 → Ω → ℝ
  B : ℝ≥0 → Ω → ℝ
  lifetime : Ω → ℝ≥0∞

/-- An evolution satisfies the integrated equations for the specified word. -/
def EvolutionData.IsEvolution {nL nR : ℕ} (e : EvolutionData.{u} nL nR)
    (κ : ℝ) (xL ρL : Fin nL → ℝ) (xR ρR : Fin nR → ℝ) : Prop :=
  @IsIntegratedSLEEvolution κ nL nR xL xR ρL ρR e.Ω e.mΩ
    e.P e.filtration e.W e.VL e.VR e.B e.lifetime

/-- Data and word bounds needed to apply the proved near-extreme estimates.
The orientation clause retains the distinct far-cutoff and total-weight
conditions on the two sides; bad far attracting groups are allowed. -/
structure NearCrossingFamily (κ : ℝ) where
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
  Rw : ℝ
  ε : ℝ
  η : ℝ
  goLeft : Bool
  hε : 0 < ε
  hη : 0 < η
  hxL0 : xL ⟨0, hnL⟩ = 0
  hxR0 : xR ⟨0, hnR⟩ = 0
  hxL : ∀ i, xL i ≠ 0 → xL i ≤ -η
  hxR : ∀ j, xR j ≠ 0 → η ≤ xR j
  hw : ∀ m, IsDS1Word mL mR Rw ε xL xR (ρLs m) (ρRs m)
  hw₀ : IsDS1Word mL mR Rw ε xL xR ρL₀ ρR₀
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

/-- Probability of the `n`-th inner-buffer reach event under the `m`-th word.
The buffer bounds all coordinates and separates every designated far label. -/
def NearCrossingFamily.crossProb {κ : ℝ} (f : NearCrossingFamily.{u} κ)
    (m n : ℕ) : ℝ≥0∞ :=
  let e := f.sequence m
  e.P (reachEvent (n : ℝ≥0)
    (if f.goLeft then leftTarget else rightTarget)
    (if f.goLeft then leftBuf f.mL f.nR n else rightBuf f.nL f.mR n)
    e.W e.VL e.VR e.lifetime)

/-- One buffer has probability arbitrarily close to one for all sufficiently
near-extreme words. This is TIP11 with its precise two orientation clauses. -/
theorem NearCrossingFamily.exists_buffer_eventually_lt {κ : ℝ}
    (f : NearCrossingFamily.{u} κ) (h13 : Exist.Theorem13Statement.{u})
    (hκ : 0 < κ) (hκ4 : κ < 4) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ n : ℕ, ∀ᶠ m in atTop, 1 - δ < f.crossProb m n := by
  let : ∀ m, MeasurableSpace (f.sequence m).Ω := fun m => (f.sequence m).mΩ
  rcases f.horientation with
    ⟨hleft, hcut, hxp, hxm, hfar, hsL, hsR⟩ |
    ⟨hright, hcut, hxm, hxp, hfar, hsR, hsL⟩
  · have hw : ∀ m, IsDS1Word f.mL (f.nR - 1) f.Rw f.ε
        f.xL f.xR (f.ρLs m) (f.ρRs m) := by
      simpa only [hcut] using f.hw
    have hw₀ : IsDS1Word f.mL (f.nR - 1) f.Rw f.ε
        f.xL f.xR f.ρL₀ f.ρR₀ := by
      simpa only [hcut] using f.hw₀
    obtain ⟨n, hn⟩ := GW2TipStage.exists_buffer_eventually_lt_left_far
      h13 hκ hκ4 f.hnL f.hnR f.hε f.hη f.hxL0 f.hxR0 f.hxL f.hxR
      hxp hxm hfar hsL hsR hw hw₀ f.hρL f.hρR f.hE f.hE₀ hδ
    exact ⟨n, by simpa only [NearCrossingFamily.crossProb, hleft,
      Bool.true_eq, ↓reduceIte] using hn⟩
  · have hw : ∀ m, IsDS1Word (f.nL - 1) f.mR f.Rw f.ε
        f.xL f.xR (f.ρLs m) (f.ρRs m) := by
      simpa only [hcut] using f.hw
    have hw₀ : IsDS1Word (f.nL - 1) f.mR f.Rw f.ε
        f.xL f.xR f.ρL₀ f.ρR₀ := by
      simpa only [hcut] using f.hw₀
    obtain ⟨n, hn⟩ := GW2TipStage.exists_buffer_eventually_lt_right_far
      h13 hκ hκ4 f.hnL f.hnR f.hε f.hη f.hxL0 f.hxR0 f.hxL f.hxR
      hxm hxp hfar hsR hsL hw hw₀ f.hρL f.hρR f.hE f.hE₀ hδ
    exact ⟨n, by simpa only [NearCrossingFamily.crossProb, hright,
      Bool.false_eq_true, ↓reduceIte] using hn⟩

/-- A single word and buffer suffice for a given positive error. -/
theorem NearCrossingFamily.exists_lt {κ : ℝ}
    (f : NearCrossingFamily.{u} κ) (h13 : Exist.Theorem13Statement.{u})
    (hκ : 0 < κ) (hκ4 : κ < 4) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ m n : ℕ, 1 - δ < f.crossProb m n := by
  obtain ⟨n, hn⟩ := f.exists_buffer_eventually_lt h13 hκ hκ4 hδ
  obtain ⟨m, hm⟩ := hn.exists
  exact ⟨m, n, hm⟩

/-- If each buffer's sufficiently near-extreme words are dominated by model
candidates, one candidate has probability greater than `1 - δ`. The candidate
may depend on both the word and the buffer; finitely many words may be omitted. -/
theorem NearCrossingFamily.exists_lt_of_domination {κ : ℝ}
    (f : NearCrossingFamily.{u} κ) (h13 : Exist.Theorem13Statement.{u})
    (hκ : 0 < κ) (hκ4 : κ < 4) {p : ℕ → ℝ≥0∞}
    (hdom : ∀ n, ∀ᶠ m in atTop, ∃ a, f.crossProb m n ≤ p a)
    {δ : ℝ≥0∞} (hδ : 0 < δ) : ∃ a, 1 - δ < p a := by
  obtain ⟨n, hn⟩ := f.exists_buffer_eventually_lt h13 hκ hκ4 hδ
  obtain ⟨m, hmn, a, ha⟩ := (hn.and (hdom n)).exists
  exact ⟨a, hmn.trans_le ha⟩

end InteractingSLE.Theorem14.GW2TipSystem.RootN4
