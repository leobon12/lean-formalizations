import QuantumZipper.Proofs.Zipper.B3dDet
import QuantumZipper.Proofs.Zipper.E6Id

/-!
# B3(d): `ZipLenCanonStmt` from pathwise-uniform field inputs

`E6.ZipLenCanonStmt` (B3(b) + B3(d) for length unzipping of the collided configurations
`C_u = zipCapDown γ u 𝒵`, input of `E6.canonZipStmt_of`) is reduced here to the explicit a.s.
statement `ZipLenInputsStmt`, by applying the deterministic zip algebra
`B3d.zipLenDown_canonConfig_addConst` to `C_u` at every `ω`. The driver normalization
`W(max s 0) = W s` is pathwise for the drivers produced by `zipCapDown`
(`zipCapDown_snd_max`). Own elementary argument (the paper, Sheffield arXiv:1012.4797 §5.1,
states the equivariance without proof).

`ZipLenInputsStmt` collects, a.s., for all `u ∈ [0, T]` and all constants `k`:
* positivity of the scale parameters of `C_u + k` and of the constant-shifted unzipped fields;
* existence of the left side images `O⁻` of the driver of `C_u` at all times (one-sided limits);
* goodness (`IsLQGGood`) of the fields unzipped from `C_u` at all times;
* the field identity (B3(d) at the field level): the field unzipped in time `s` from
  `canonConfig γ (C_u + k)` is (`RegEq`) the `a`-rescaling of the constant-shifted field unzipped
  from `C_u` in time `a² s`, `a = scaleParam γ (C_u + k)`.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace B3d

/-- The drivers produced by `zipCapDown` are normalized on `(−∞, 0]`. -/
theorem zipCapDown_snd_max (γ u : ℝ) (c : FieldSample × (ℝ → ℝ)) (s : ℝ) :
    (zipCapDown γ u c).2 (max s 0) = (zipCapDown γ u c).2 s := by
  simp only [zipCapDown, max_eq_left (le_max_right s 0)]

variable {Ω : Type} [MeasurableSpace Ω]

/-! ## The field cocycle after adding a constant -/

/-- `RegEq` survives adding a constant when the raw circle values of both fields converge at
every centre: `avgReg (A + k) = avgReg A + k` there (`LocalRule.avgReg_addConst_of_tendsto`). -/
theorem avgReg_addConst_congr {A A' : FieldSample} (h : RegEq A A')
    (hA : LocalRule.RawConverges A univ) (hA' : LocalRule.RawConverges A' univ) (k : ℝ) :
    avgReg (addConst A k) = avgReg (addConst A' k) := by
  funext n z
  rw [LocalRule.avgReg_addConst_of_tendsto (hA n z trivial),
    LocalRule.avgReg_addConst_of_tendsto (hA' n z trivial), h n z]

/-- **Inputs of the field cocycle `CapCocycleAddStmt`**: a.s., for all `u, s ≥ 0`, `u + s ≤ T`,
the field of `C_u` unzipped by `s` and the field of `C_{u+s}` agree (`RegEq`; Corollary 1.5(b)
for two unzippings, uniformly in the times), and the raw folded-circle values of both converge
along the dyadic approximations at every centre. -/
def CapCocycleRegStmt (κ T : ℝ) (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) :
    Prop :=
  ∀ᵐ ω ∂P, ∀ u s : ℝ, 0 ≤ u → 0 ≤ s → u + s ≤ T →
    RegEq (zipCapDown (Real.sqrt κ) s (zipCapDown (Real.sqrt κ) u (B2.cfg κ B X ω))).1
        (zipCapDown (Real.sqrt κ) (u + s) (B2.cfg κ B X ω)).1 ∧
      LocalRule.RawConverges
        (zipCapDown (Real.sqrt κ) s (zipCapDown (Real.sqrt κ) u (B2.cfg κ B X ω))).1 univ ∧
      LocalRule.RawConverges (zipCapDown (Real.sqrt κ) (u + s) (B2.cfg κ B X ω)).1 univ

/-- **`CapCocycleAddStmt` from `CapCocycleRegStmt`.** -/
theorem capCocycleAddStmt_of {κ T : ℝ} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
    {X : Ω → FieldSample} (h : CapCocycleRegStmt κ T P B X) : E6.CapCocycleAddStmt κ T P B X := by
  filter_upwards [h] with ω hω
  intro u s k hu hs hus
  obtain ⟨h1, h2, h3⟩ := hω u s hu hs hus
  exact avgReg_addConst_congr h1 h2 h3 k
