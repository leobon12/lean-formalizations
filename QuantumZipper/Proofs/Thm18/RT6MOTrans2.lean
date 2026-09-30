import QuantumZipper.Proofs.Thm18.RT6MOTrans
import QuantumZipper.Proofs.Thm18.R18T6Main

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D87: zipping up the pieces and zipping up the configuration have the same driver and area

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, p. 26: `Z^LEN_t`, `t > 0`,
re-welds the two pieces cut out by the curve along their boundary lengths (D86: open-arc lengths).
Here we prove the non-field part of the nodes N1/N2 of RT6MOTrans.lean: at the wedge `c₀` (for all
`ℓ`) and at `c₁ = Z^A_{−ℓ} c₀`, zipping up the pieces (`zipLenUpOA γ ℓ ∘ offConfig γ`) and zipping up
the configuration (`zipLenUpA γ ℓ`) produce the same driver and the same area measure a.s. This uses
the proved boundary identities of D86 (`ae_lenWeldDriverO_offConfig_wedge`,
`ae_lenWeldDriverO_offConfig_zipLenDownA`) and locality of the area (`ae_wedgeAConfig_area_eq`,
`ae_zipLenDownA_area_eq_and_good`). The driver of the zip-up only reads the old driver on `(0,∞)`
(own elementary bookkeeping). As a consequence, continuity of the drivers of `zipLenMO` holds
without N1 (`rt6_ae_contMO'`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace R18

open Thm18Asm

/-- **Deterministic**: if the pieces of `c` have the welding driver of `c` and the area of `c`,
zipping up the pieces and zipping up `c` give the same driver and area. -/
theorem rt6_zipLenUpOA_offConfig_drv_area {γ ℓ : ℝ} {c : AreaConfig}
    (hp : lenWeldDriverO γ (offConfig γ c).fld ℓ = lenWeldDriver γ c.fld ℓ)
    (ha : (offConfig γ c).area = c.area) :
    (zipLenUpOA γ ℓ (offConfig γ c)).drv = (zipLenUpA γ ℓ c).drv ∧
      (zipLenUpOA γ ℓ (offConfig γ c)).area = (zipLenUpA γ ℓ c).area := by
  have hA : (zipWeldUpA γ (lenWeldDriver γ c.fld ℓ).1 (lenWeldDriver γ c.fld ℓ).2
      (offConfig γ c)).area =
      (zipWeldUpA γ (lenWeldDriver γ c.fld ℓ).1 (lenWeldDriver γ c.fld ℓ).2 c).area := by
    simp only [zipWeldUpA, ha]
  unfold zipLenUpOA zipLenUpA
  rw [hp]
  refine ⟨?_, ?_⟩
  · simp only [canonAConfig, hA]
    funext s
    congr 1
    simp only [zipWeldUpA, zipWeldUp, AreaConfig.toPair]
    split_ifs with h
    · rfl
    · show (offConfig γ c).drv _ - _ = c.drv _ - _
      show c.drv (max _ 0) - _ = c.drv _ - _
      rw [max_eq_left (by linarith [not_le.1 h])]
  · simp only [canonAConfig, hA]

end R18
end QuantumZipper
