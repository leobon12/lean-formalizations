import QuantumZipper.Proofs.Thm18.R18T6Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D82: the paper-form Theorem 1.8 with the unzipping map acting on the pieces

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Theorem 1.8 (p. 26,
`literature/1012.4797.txt` lines 1005–1045): `Z^LEN_{−t}` acts on the pair of quantum surfaces
`((D₁,h_{D₁}),(D₂,h_{D₂}))`, the restrictions of `h` to the two components of `ℍ ∖ η` (p. 17: "both
`h` and `η` are determined by the pair"; §4.1 p. 48: `h` may be defined arbitrarily on the
measure-zero set `η`); `Z^LEN_t` is the inverse of `Z^LEN_{−t}`, "a.s. uniquely defined via
conformal welding". Decision D82 (pre-approved paper alignment; refines D80 (a)).

In `theorem1_8Paper` the unzipping map `zipLenDownA` regularizes the field of the configuration
across its curve (`coordChange` through `evalReg` reads circles that cross `η`). Here the unzipping
map first reads the configuration **off its curve** (`offConfig`): the masked data `offData`
(circle coordinates of circles that stay off the curve, test pairings of test functions avoiding
it, the driver on `[0,∞)`), rebuilt as a field by `readOffField` (T6, R18T6Defs.lean) and the
area of the pieces by `areaOfData` (the local quantum area on `ℍ ∖ η`, T6). So `Z^LEN_{−ℓ}` is a
function of the pieces, as in the paper, and the round trip `Z_{−ℓ} ∘ Z_ℓ = id` becomes the
statement "`Z_{−ℓ}` inverts the welding" proved by Sheffield's argument (`Z_ℓ` is the inverse of
`Z_{−ℓ}`, law invariance under unzipping), see handoff/R18-PLAN.md §6.

The zipping map `zipLenUpA` is kept: it already reads the configuration only off its curve (the
pulled-back circles avoid the old curve), up to the boundary measure at the base point `0`.

These definitions are to be moved next to `theorem1_8Paper` in `Statements/Thm18Paper.lean` at the
next global rebuild (as D74 did for `Statements/Thm18Off.lean`); nothing else changes.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace R18

/-- The driver read from the data: its values on `[0,∞)`, extended by the value at `0`. -/
def drvOfData (d : E6.FullData) : ℝ → ℝ := fun s => d.2 ⟨max s 0, le_max_right _ _⟩

/-- The configuration read from masked data (D82): the field of the pieces read off the curve
(`readOffField`), the driver, and the area of the pieces (`areaOfData`, the curve carries none). -/
def configOfData (γ : ℝ) (d : E6.FullData) : AreaConfig :=
  ⟨readOffField d, drvOfData d, areaOfData γ d⟩

/-- **The pieces of a configuration** (D82): the configuration read off its own curve. -/
def offConfig (γ : ℝ) (c : AreaConfig) : AreaConfig :=
  configOfData γ (offData c.toPair)

/-- **`Z^LEN_{−ℓ}` on the pieces** (D82): unzip the configuration read off its curve. -/
def zipLenDownMA (γ ℓ : ℝ) (c : AreaConfig) : AreaConfig :=
  zipLenDownA γ ℓ (offConfig γ c)

/-- The length quantum zipper of D82: `Z^LEN_ℓ = zipLenUpA` for `ℓ ≥ 0` (welding) and
`Z^LEN_{−ℓ} = zipLenDownMA` (unzipping the pieces). -/
def zipLenMA (γ ℓ : ℝ) : AreaConfig → AreaConfig :=
  if 0 ≤ ℓ then zipLenUpA γ ℓ else zipLenDownMA γ (-ℓ)

/-- `Z^LEN_{−ℓ}` on the pieces depends on the configuration only through its masked data. -/
theorem zipLenDownMA_congr_offData {γ ℓ : ℝ} {c c' : AreaConfig}
    (h : offData c.toPair = offData c'.toPair) : zipLenDownMA γ ℓ c = zipLenDownMA γ ℓ c' := by
  unfold zipLenDownMA offConfig
  rw [h]

theorem zipLenMA_of_nonneg {γ ℓ : ℝ} (hℓ : 0 ≤ ℓ) : zipLenMA γ ℓ = zipLenUpA γ ℓ := by
  simp [zipLenMA, hℓ]

theorem zipLenMA_of_neg {γ ℓ : ℝ} (hℓ : ℓ < 0) : zipLenMA γ ℓ = zipLenDownMA γ (-ℓ) := by
  simp [zipLenMA, not_le.2 hℓ]

end R18
end QuantumZipper
