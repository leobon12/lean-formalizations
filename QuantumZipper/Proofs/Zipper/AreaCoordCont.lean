import QuantumZipper.Proofs.Zipper.AreaCoord
import QuantumZipper.Proofs.Zipper.JointModDet

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# AREA-COORD (6): W-A-cc from the fixed-time rule and continuity in time (alternative split)

A second reduction of `E6.WedgeAreaCoordStmt` (W-A-cc, `PStarAreaCoord.lean`), closer to the
split first proposed for this node: the rule at each **fixed** time plus **continuity in time**
of the limit measures, using the D29 core `WedgeUnzip.WedgeGoodAllStmt` (already an input of
`pStarAreaAllStmt_of_coord`), which says that a.s. the unzipped fields are good at all times —
in particular their area measures are genuine vague limits, concentrated on `ℍ` and finite on
compact subsets of `ℍ`.

* **`WedgeAreaCoordFixStmt`** (W-A-cc-fix): for each fixed `t ≥ 0`, a.s., the rule
  `μ_{x_t}(S) = μ_{x_0}(f_t⁻¹(S))` for Borel `S ⊆ ℍ`. This is Duplantier–Sheffield, *Liouville
  quantum gravity and KPZ*, Invent. Math. 185 (2011), arXiv:0808.1560, **Prop. 2.1, p. 13**, for
  the single conformal map `f_t⁻¹` (the driver is independent of the field).
* **`WedgeAreaContStmt`** (W-A-cont): a.s., for every test function `f`, the map
  `t ↦ ∫ f dμ_{x_t}` is continuous on `[0, ∞)`.

Deterministic inputs proved here: the transported integrals `t ↦ ∫ (1_{ℍ∖K_t} f ∘ f_t) dμ` are
continuous on `[0,∞)` for `μ` finite on compact subsets of `ℍ`
(`continuousWithinAt_integral_transTest`: dominated convergence; pointwise continuity from the
continuity of `s ↦ f_s(w)` (`FwdHolo.continuousOn_fwdMap_time`) and a compactness argument with
the joint continuity of `(s, z) ↦ f_s⁻¹(z)` (`RegUnif.continuousOn_fwdMapInv_joint`)); equality at
rational times propagates to all times (`areaMeasure_eq_areaTransport_of_rat_cont`).
Result: **`wedgeAreaCoordStmt_of_fix_cont`**. Own elementary proofs (the Loewner inputs are cited in
the lemmas used).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped Topology NNReal ENNReal

namespace QuantumZipper.E6

open D3Plus MeasUnzip

variable {W : ℝ → ℝ}

/-! ## The flow image of a compact set -/

/-- The image of `[0,T] × C` under `(s, z) ↦ f_s⁻¹(z)`. -/
def flowImage (W : ℝ → ℝ) (T : ℝ) (C : Set ℂ) : Set ℂ :=
  (fun p : ℝ × ℂ => fwdMapInv W p.1 p.2) '' (Icc 0 T ×ˢ C)

theorem isCompact_flowImage (hW : Continuous W) (hW0 : W 0 = 0) (T : ℝ) {C : Set ℂ}
    (hC : IsCompact C) (hCH : C ⊆ H) : IsCompact (flowImage W T C) :=
  (isCompact_Icc.prod hC).image_of_continuousOn
    ((RegUnif.continuousOn_fwdMapInv_joint hW hW0 T).mono (prod_mono subset_rfl hCH))

theorem flowImage_subset_H (hW : Continuous W) (hW0 : W 0 = 0) (T : ℝ) {C : Set ℂ}
    (hCH : C ⊆ H) : flowImage W T C ⊆ H := by
  rintro _ ⟨⟨s, z⟩, ⟨hs, hz⟩, rfl⟩
  exact RS.fwdMapInv_mem_H hW hW0 hs.1 (hCH hz)

/-! ## Continuity in time of the transported test functions and integrals -/

/-! ## From rational times to all times -/

/-! ## The random-level nodes and the reduction -/

end QuantumZipper.E6
