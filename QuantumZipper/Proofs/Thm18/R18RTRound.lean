import QuantumZipper.Proofs.Thm18.R18RTNodes
import QuantumZipper.Proofs.Thm18.R18ZipReg
import QuantumZipper.Proofs.Thm18.R18E6A
import QuantumZipper.Proofs.Thm18.R18Arc
import QuantumZipper.Proofs.Thm18.R18RTMeasTime
import QuantumZipper.Proofs.Thm18.R18ZipFacDefs
import QuantumZipper.Proofs.Thm18.R18T4bWeld
import QuantumZipper.Proofs.Thm18.R18T6Down
import QuantumZipper.Proofs.Thm18.R18RoundUpDet

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D82 RT4: `Z_{−ℓ} ∘ Z_ℓ = id` by Sheffield's inverse argument

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Theorem 1.8 (1), p. 26:
`Z^LEN_ℓ` is the inverse of `Z^LEN_{−ℓ}`, "a.s. uniquely defined via conformal welding"; p. 70:
the pair of surfaces "is invariant under zipping and unzipping by the boundary length measure".
The paper gets the round trip `Z_{−ℓ}(Z_ℓ c) = c` from the law invariance of unzipping and the
fact that welding undoes unzipping. Formally (D82, handoff/R18-PLAN.md §6):

* `x₀ = cfgData c₀`, `x₁ = cfgData (Z_{−ℓ} c₀)` have the same law (E6 on the full data,
  `map_cfgData_zipLenDownA`);
* `Z_ℓ` is read by a Borel map `Φ` of the full data at `c₀` and at `Z_{−ℓ} c₀` (D81,
  `G4ZipFactorFullAStmt`);
* the unzipping of the pieces is read by a Borel map `Dm` of the masked data on a Borel set `G`
  (`DownDataMeasCStmt`, RT3, for continuous drivers);
* at `x₁` the round trip holds: `Φ x₁` has the masked data of `c₀` (`Z_ℓ ∘ Z_{−ℓ} = id`, RT1),
  and unzipping the pieces of `c₀` gives the masked data of `Z_{−ℓ} c₀` (`MaskExactAStmt`, RT2);
* the round-trip event is Borel (drivers compared at rational times), so it transfers to `x₀`,
  where it says `Z_{−ℓ}^{pieces}(Z_ℓ c₀) = c₀` off the curve.

Main result: **`g4RoundUpDownMAStmt_of`**. The measure-theoretic bookkeeping is an own elementary
argument; the mathematics is the paper's.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace R18

open Thm18Asm Thm18Asm.G4Core

/-- The driver of `Z_ℓ c` is continuous when `c`'s is and the welding driver exists. -/
theorem continuous_zipLenUpA_drv {γ ℓ : ℝ} {c : AreaConfig} (hc : Continuous c.drv)
    (hc0 : c.drv 0 = 0) (hp : IsLenWeldingDriver γ c.fld ℓ (lenWeldDriver γ c.fld ℓ)) :
    Continuous (zipLenUpA γ ℓ c).drv := by
  have h := continuous_zipWeldUp_drv (γ := γ) hp.1 hp.2.1 hp.2.2.1 (c := c.toPair) hc hc0
  simp only [zipLenUpA, canonAConfig, zipWeldUpA]
  exact (h.comp (continuous_const.mul (continuous_id.max continuous_const))).div_const _

theorem continuous_drvOfData_offData {x : FieldSample × (ℝ → ℝ)} (hx : Continuous x.2) :
    Continuous (drvOfData (offData x)) := by
  show Continuous fun s : ℝ => x.2 (max s 0)
  exact hx.comp (continuous_id.max continuous_const)

/-- Two functions continuous on `ℝ` that agree at `max r 0` for all rationals `r` agree on
`[0,∞)`. -/
theorem eq_of_rat_max {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ r : ℚ, f (max (r : ℝ) 0) = g (max (r : ℝ) 0)) : ∀ u : ℝ, 0 ≤ u → f u = g u := by
  have hfg : (fun u : ℝ => f (max u 0)) = fun u => g (max u 0) :=
    Continuous.ext_on (Rat.denseRange_cast (𝕜 := ℝ)) (hf.comp (continuous_id.max continuous_const))
      (hg.comp (continuous_id.max continuous_const)) (by
        rintro _ ⟨r, rfl⟩
        exact h r)
  intro u hu
  have := congrFun hfg u
  simpa [max_eq_left hu] using this

/-- The nonnegative real `max r 0` of a rational `r`. -/
def ratNN (r : ℚ) : ℝ≥0 := ⟨max (r : ℝ) 0, le_max_right _ _⟩

/-- The round-trip event on the full data: the reading of `Z_ℓ` lies in `G`, and unzipping its
pieces gives back the masked circle coordinates and (at rational times) the driver. -/
def RTEvent (Φ : E6.FullData → E6.FullData) (G : Set ((ℕ → ℝ) × (ℝ≥0 → ℝ)))
    (Dm : (ℕ → ℝ) × (ℝ≥0 → ℝ) → (ℕ → ℝ) × (ℝ≥0 → ℝ)) : Set E6.FullData :=
  {x | πd (Φ x) ∈ G ∧ (∀ i : ℕ, (Dm (πd (Φ x))).1 i = (D74.maskSel x).1.1 i) ∧
    ∀ r : ℚ, (Dm (πd (Φ x))).2 (ratNN r) =
      x.2 (ratNN r)}

theorem measurableSet_rtEvent {Φ : E6.FullData → E6.FullData} (hΦ : Measurable Φ)
    {G : Set ((ℕ → ℝ) × (ℝ≥0 → ℝ))} (hG : MeasurableSet G)
    {Dm : (ℕ → ℝ) × (ℝ≥0 → ℝ) → (ℕ → ℝ) × (ℝ≥0 → ℝ)} (hDm : Measurable Dm) :
    MeasurableSet (RTEvent Φ G Dm) := by
  have h1 : Measurable fun x => πd (Φ x) := measurable_πd.comp hΦ
  have h2 : Measurable fun x => Dm (πd (Φ x)) := hDm.comp h1
  have hA2 : MeasurableSet (⋂ i : ℕ, {x : E6.FullData |
      (Dm (πd (Φ x))).1 i = (D74.maskSel x).1.1 i}) := by
    refine MeasurableSet.iInter fun i => measurableSet_eq_fun ?_ ?_
    · exact (measurable_pi_apply i).comp (measurable_fst.comp h2)
    · exact (measurable_pi_apply i).comp
        (measurable_fst.comp (measurable_fst.comp D74.measurable_maskSel))
  have hA3 : MeasurableSet (⋂ r : ℚ, {x : E6.FullData |
      (Dm (πd (Φ x))).2 (ratNN r) = x.2 (ratNN r)}) := by
    refine MeasurableSet.iInter fun r => measurableSet_eq_fun ?_ ?_
    · exact (measurable_pi_apply _).comp (measurable_snd.comp h2)
    · exact (measurable_pi_apply _).comp measurable_snd
  have e : RTEvent Φ G Dm = (fun x => πd (Φ x)) ⁻¹' G ∩
      ((⋂ i : ℕ, {x : E6.FullData | (Dm (πd (Φ x))).1 i = (D74.maskSel x).1.1 i}) ∩
        ⋂ r : ℚ, {x : E6.FullData | (Dm (πd (Φ x))).2 (ratNN r) = x.2 (ratNN r)}) := by
    ext x
    simp [RTEvent]
  rw [e]
  exact (h1 hG).inter (hA2.inter hA3)

end R18
end QuantumZipper
