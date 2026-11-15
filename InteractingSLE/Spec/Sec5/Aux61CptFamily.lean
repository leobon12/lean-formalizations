/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61CptLandHeight
import InteractingSLE.Spec.Sec5.Aux61CptSeedAccess
import InteractingSLE.Spec.Sec5.Aux61GWindow19Real
import InteractingSLE.Spec.Sec5.Aux61GWindow19Capture
import InteractingSLE.Spec.Sec5.Aux61GWindow19Heights

/-!
# R103's per-outcome family

Packet PROVE-AUX61-CAPTURE (rulings R103, R103a). The family is installed through GLUEINST's thin-window constructor
`Aux61GWindow19.localizedRealChoices`. An index is a good retained time, a thin window, a rational landing parameter
`L = (v₀, ε₀, M, d)` and a rational seed parameter `P = (δ, δ', ε, d')` such that the landing interval
`(v₀ − ε₀, v₀ + ε₀)` lies on one side of the seed at distance at least the seed radius `ε`, and the window's closed buffer
meets `ℝ` inside `O₀ = (−ε, ε) ∪ (v₀ − ε₀, v₀ + ε₀)` (`CptIndex`). The word (`cptWord`) is `∓λ` at the seed and carries
NOJUMP's fixed eastern height `eastHeight S 1` on the landing interval (branch `n = 1`); it satisfies RefWin on either
side. The selected records are the window records passing the landing and seed tests.

Proved here: Borel selection (`cptChoices_selected_measurable`), the seed heights (`cptSeed`), and the access
hypothesis on the whole `O₀` — own collar points on the seed interval, counterflow accesses on the landing interval
(`cptAccess`, pinch-free forms of NOJUMP).

R48/R77 respected; nothing here replaces a source theorem.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H Hbar chiC fwdHull fwdMap fwdMapInv)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec5.Aux61Cpt
open WangWu GlueCond Cond44Ref Aux61GWord Aux61Cmp LawUnique Aux61Restart
open Aux61SlitW Aux61SlitW.SourceSetting Aux61GAlign Aux61R1C Aux61Asm2 Aux61SlitWX Aux61GWindow17
open Aux61GR1F Aux61GInst Aux61FibData Aux61GWindow19 Aux61WndCap
universe u

variable (S : SourceSetting.{u})

/-- The lower end of the landing interval. -/
def landLo (L : LandParam) : ℝ := (L.1.1 : ℝ) - L.1.2.1

/-- The upper end of the landing interval. -/
def landHi (L : LandParam) : ℝ := (L.1.1 : ℝ) + L.1.2.1

/-- The seed radius of a seed parameter. -/
def seedRad (P : SeedParam) : ℝ := P.1.2.2.1

theorem landLo_lt_landHi (L : LandParam) : landLo L < landHi L := by
  have : (0 : ℝ) < L.1.2.1 := by exact_mod_cast L.2.1
  unfold landLo landHi; linarith

theorem seedRad_pos (P : SeedParam) : 0 < seedRad P := by
  unfold seedRad; exact_mod_cast P.2.2.2.1

theorem mem_landInterval_iff {L : LandParam} {b : ℝ} :
    b ∈ Ioo (landLo L) (landHi L) ↔ |b - L.1.1| < L.1.2.1 := by
  rw [abs_lt]; unfold landLo landHi; constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- The real comparison set: the seed interval and the landing interval. -/
def cptReal (L : LandParam) (P : SeedParam) : Set ℝ :=
  Ioo (-seedRad P) (seedRad P) ∪ Ioo (landLo L) (landHi L)

theorem isOpen_cptReal (L : LandParam) (P : SeedParam) : IsOpen (cptReal L P) :=
  isOpen_Ioo.union isOpen_Ioo

/-- **Valid indices**: the landing interval lies on one side of the seed beyond the seed radius, and the window's
closed buffer meets the real line inside the comparison set. -/
def CptValid (k : GoodTime S × AllowedWindow × LandParam × SeedParam) : Prop :=
  (seedRad k.2.2.2 ≤ landLo k.2.2.1 ∨ landHi k.2.2.1 ≤ -seedRad k.2.2.2) ∧
    ∀ z ∈ closure (outerBuffer k.2.1.1.1), z.im = 0 → z.re ∈ cptReal k.2.2.1 k.2.2.2

/-- The index type of the family. -/
abbrev CptIndex := {k : GoodTime S × AllowedWindow × LandParam × SeedParam // CptValid S k}

/-! ### The word -/

theorem chiC_pos_S : 0 < chiC S.κ := Sec4.chiC_pos S.κ_pos S.κ_lt_four

theorem eastHeight_ge : sleLambda S.κ - Real.pi * chiC S.κ ≤ Aux61Nj.eastHeight S 1 := by
  have h1 := chiC_pos_S S
  have h2 : 0 < S.θ₂ - S.θ₁ := sub_pos.2 S.angle_lt
  unfold Aux61Nj.eastHeight
  push_cast
  nlinarith [Real.pi_pos]

theorem eastHeight_gt : sleLambda S.κ + Real.pi * chiC S.κ < Aux61Nj.eastHeight S 1 := by
  have h1 := chiC_pos_S S
  have h2 : 0 < S.θ₂ - S.θ₁ := sub_pos.2 S.angle_lt
  unfold Aux61Nj.eastHeight
  push_cast
  nlinarith [Real.pi_pos]

/-- **The landing word** of an index: the eastern height on the landing interval, `∓λ` at the seed. -/
def cptWord (k : CptIndex S) : ReferenceWord S.κ :=
  if h : 0 < landLo k.1.2.2.1 then
    positiveReference (v := Aux61Nj.eastHeight S 1) S.κ_pos S.κ_lt_four.le h
      (landLo_lt_landHi k.1.2.2.1) (eastHeight_ge S)
  else
    negativeReference (v := Aux61Nj.eastHeight S 1) S.κ_pos S.κ_lt_four (landLo_lt_landHi k.1.2.2.1)
      (by
        rcases k.2.1 with h' | h'
        · exact absurd ((seedRad_pos k.1.2.2.2).trans_le h') h
        · exact h'.trans_lt (neg_neg_of_pos (seedRad_pos k.1.2.2.2)))
      (eastHeight_gt S)

theorem cptWord_left (k : CptIndex S) : (cptWord S k).left = landLo k.1.2.2.1 := by
  unfold cptWord; split <;> rfl

theorem cptWord_right (k : CptIndex S) : (cptWord S k).right = landHi k.1.2.2.1 := by
  unfold cptWord; split <;> rfl

theorem cptWord_jumps (k : CptIndex S) :
    (cptWord S k).jumps = {landLo k.1.2.2.1, landHi k.1.2.2.1, 0} := by
  unfold cptWord; split <;> rfl

/-- The word is the eastern height on the landing interval. -/
theorem cptWord_land (k : CptIndex S) {z : ℝ} (hz : z ∈ Ioo (landLo k.1.2.2.1) (landHi k.1.2.2.1)) :
    (cptWord S k).boundary z = Aux61Nj.eastHeight S 1 := by
  unfold cptWord
  split
  · exact positiveBoundary_value ‹_› hz
  · change Aux61GPrime.negativeBoundary S.κ _ _ _ z = _
    have hb : landHi k.1.2.2.1 < 0 := by
      rcases k.2.1 with h' | h'
      · exact absurd ((seedRad_pos k.1.2.2.2).trans_le h') ‹_›
      · exact h'.trans_lt (neg_neg_of_pos (seedRad_pos k.1.2.2.2))
    simp only [Aux61GPrime.negativeBoundary, ite_eq_left (hz.2.trans hb), ite_eq_left hz.2,
      ite_eq_right (not_lt.2 hz.1.le)]
    ring

/-- The word is `∓λ` on the seed interval. -/
theorem cptWord_seed (k : CptIndex S) {z : ℝ} (hz : |z| < seedRad k.1.2.2.2) :
    (cptWord S k).boundary z = if z < 0 then -sleLambda S.κ else sleLambda S.κ := by
  rw [abs_lt] at hz
  unfold cptWord
  split
  · rename_i h
    have hza : z < landLo k.1.2.2.1 := by
      have h1 := seedRad_pos k.1.2.2.2
      have h2 := landLo_lt_landHi k.1.2.2.1
      rcases k.2.1 with h' | h'
      · linarith
      · linarith
    change Aux61GPrime.negativeBoundary S.κ _ _ _ z = _
    simp only [Aux61GPrime.negativeBoundary, ite_eq_left hza,
      ite_eq_left (hza.trans (landLo_lt_landHi k.1.2.2.1)), sub_self, mul_zero, add_zero]
  · rename_i h
    have hzb : landHi k.1.2.2.1 < z := by
      rcases k.2.1 with h' | h'
      · exact absurd ((seedRad_pos k.1.2.2.2).trans_le h') h
      · linarith
    change Aux61GPrime.negativeBoundary S.κ _ _ _ z = _
    simp only [Aux61GPrime.negativeBoundary, ite_eq_right (not_lt.2 hzb.le),
      ite_eq_right (not_lt.2 ((landLo_lt_landHi k.1.2.2.1).trans hzb).le), sub_self, mul_zero, add_zero]

theorem cptWord_seed_heights (k : CptIndex S) :
    PiecewiseConstantBoundaryData.leftLim (cptWord S k).boundary 0 = -sleLambda S.κ ∧
      PiecewiseConstantBoundaryData.rightLim (cptWord S k).boundary 0 = sleLambda S.κ := by
  unfold cptWord
  split
  · exact positiveBoundary_seed_heights ‹_› (landLo_lt_landHi k.1.2.2.1)
  · rename_i h
    exact negativeBoundary_seed_heights (landLo_lt_landHi k.1.2.2.1) (by
      rcases k.2.1 with h' | h'
      · exact absurd ((seedRad_pos k.1.2.2.2).trans_le h') h
      · exact h'.trans_lt (neg_neg_of_pos (seedRad_pos k.1.2.2.2)))

/-! ### The family -/

/-- The access tests of an index. -/
def cptTests (k : CptIndex S) : Set (SourceRecord S.nL S.nR) :=
  landRecords S k.1.1 k.1.2.2.1 ∩ seedRecords S k.1.1 k.1.2.2.2

/-- **R103's per-outcome family.** -/
def cptChoices : RestartChoices S :=
  localizedRealChoices S (fun k : CptIndex S => k.1.1) (fun k => k.1.2.1) (cptWord S)
    (fun k => cptReal k.1.2.2.1 k.1.2.2.2) (fun _ => isOpen_cptReal _ _) (fun k => k.2.2) (cptTests S)

theorem cptTests_measurable (k : CptIndex S) : MeasurableSet (cptTests S k) :=
  (measurableSet_landRecords S k.1.1 k.1.2.2.1).inter (measurableSet_seedRecords S k.1.1 k.1.2.2.2)

theorem cptChoices_selected_measurable : ∀ i, MeasurableSet ((cptChoices S).selected i) :=
  localizedReal_selected_measurable S _ _ _ _ _ _ _ (cptTests_measurable S)

/-- The seed heights of the installed words (the top's `hSeed`). -/
theorem cptSeed : ∀ i, PiecewiseConstantBoundaryData.leftLim ((finiteRestart (cptChoices S)).data i).bR 0 =
      -sleLambda ((finiteRestart (cptChoices S)).data i).κ ∧
    PiecewiseConstantBoundaryData.rightLim ((finiteRestart (cptChoices S)).data i).bR 0 =
      sleLambda ((finiteRestart (cptChoices S)).data i).κ :=
  localized_seed_heights S _ _ _ _ _ fun k => cptWord_seed_heights S k

end InteractingSLE.Sec5.Aux61Cpt
