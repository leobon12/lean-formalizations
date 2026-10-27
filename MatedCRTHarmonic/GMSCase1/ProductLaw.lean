import Mathlib

/-!
# Product-law identities for an independently rooted field

Measure-theoretic bookkeeping for [18] Proposition 4.10, Case 1
: a field `h` with law `ν`, an independent
auxiliary coordinate `w` with law `κ` (the imaginary-geometry field, its phase and the
space-filling SLE), and an independent root `z` with law `λ`. If the rooted field `R(h, z)` has
law `ν` weighted by `d` (DMS14 Lemma A.10),
then the rooted *pair* `(R(h, z), w)` has law `ν ⊗ κ` weighted by `d ∘ fst`: the field-space
identity lifts to every auxiliary coordinate independent of the field and the root.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace MatedCRTHarmonic.GMSCase1

section Rearrange

variable {F E : Type*} [MeasurableSpace F] [MeasurableSpace E]

/-- The rearrangement `((h, w), z) ↦ ((h, z), w)`. -/
def rearrange (x : (F × E) × ℂ) : (F × ℂ) × E := ((x.1.1, x.2), x.1.2)

theorem measurable_rearrange : Measurable (rearrange (F := F) (E := E)) :=
  ((measurable_fst.comp measurable_fst).prodMk measurable_snd).prodMk
    (measurable_snd.comp measurable_fst)

/-- `((h, w), z) ↦ ((h, z), w)` carries `(ν ⊗ κ) ⊗ λ` to `(ν ⊗ λ) ⊗ κ`. -/
theorem map_rearrange_prod (ν : Measure F) (κ : Measure E) (lam : Measure ℂ)
    [SFinite ν] [SFinite κ] [SFinite lam] :
    ((ν.prod κ).prod lam).map rearrange = (ν.prod lam).prod κ := by
  have h1 := measurePreserving_prodAssoc ν κ lam
  have h2 : MeasurePreserving (Prod.map id Prod.swap) (ν.prod (κ.prod lam))
      (ν.prod (lam.prod κ)) :=
    (MeasurePreserving.id ν).prod (Measure.measurePreserving_swap (μ := κ) (ν := lam))
  have h3 := (measurePreserving_prodAssoc ν lam κ).symm
  have h := h3.comp (h2.comp h1)
  have e : (MeasurableEquiv.prodAssoc.symm ∘ (Prod.map id Prod.swap) ∘
      MeasurableEquiv.prodAssoc : (F × E) × ℂ → (F × ℂ) × E) = rearrange := by
    funext x
    rfl
  rw [← e]
  exact h.map_eq

end Rearrange

section Rooted

variable {F E : Type*} [MeasurableSpace F] [MeasurableSpace E]

/-- **Lift of a rooted field law to an independent auxiliary coordinate.** If the rooted field
`R(h, z)` under `ν ⊗ λ` has law `ν.withDensity d`, then `(R(h, z), w)` under `(ν ⊗ κ) ⊗ λ` has law
`(ν ⊗ κ).withDensity (d ∘ fst)`. -/
theorem map_rootedPair_eq_withDensity (ν : Measure F) (κ : Measure E) (lam : Measure ℂ)
    [SFinite ν] [SFinite κ] [SFinite lam]
    {R : F × ℂ → F} (hR : Measurable R) {d : F → ℝ≥0∞} (hd : AEMeasurable d ν)
    (hlaw : (ν.prod lam).map R = ν.withDensity d) :
    ((ν.prod κ).prod lam).map (fun x : (F × E) × ℂ => (R (x.1.1, x.2), x.1.2)) =
      (ν.prod κ).withDensity (fun y => d y.1) := by
  have e : (fun x : (F × E) × ℂ => (R (x.1.1, x.2), x.1.2)) =
      Prod.map R id ∘ rearrange := by
    funext x
    rfl
  rw [e, ← Measure.map_map (hR.prodMap measurable_id) measurable_rearrange,
    map_rearrange_prod, ← Measure.map_prod_map _ _ hR measurable_id, hlaw, Measure.map_id,
    prod_withDensity_left₀ hd]

end Rooted

section DensityMap

variable {Ω F : Type*} [MeasurableSpace Ω] [MeasurableSpace F]

/-- Weighting by a function of a measurable observation commutes with taking its law. -/
theorem map_withDensity_comp_of_measurable {P : Measure Ω} {Y : Ω → F} (hY : Measurable Y)
    {d : F → ℝ≥0∞} (hd : Measurable d) :
    (P.withDensity (fun ω => d (Y ω))).map Y = (P.map Y).withDensity d := by
  ext s hs
  rw [Measure.map_apply hY hs, withDensity_apply _ (hY hs), withDensity_apply _ hs,
    setLIntegral_map hs hd hY]

/-- Weighting by a function of an a.e.-measurable observation commutes with taking its law. -/
theorem map_withDensity_comp {P : Measure Ω} {Y : Ω → F} (hY : AEMeasurable Y P)
    {d : F → ℝ≥0∞} (hd : Measurable d) :
    (P.withDensity (fun ω => d (Y ω))).map Y = (P.map Y).withDensity d := by
  have hw : P.withDensity (fun ω => d (Y ω)) = P.withDensity (fun ω => d (hY.mk Y ω)) :=
    withDensity_congr_ae (hY.ae_eq_mk.fun_comp d)
  have hmapw : (P.withDensity (fun ω => d (hY.mk Y ω))).map Y =
      (P.withDensity (fun ω => d (hY.mk Y ω))).map (hY.mk Y) :=
    Measure.map_congr ((withDensity_absolutelyContinuous _ _).ae_le hY.ae_eq_mk)
  rw [hw, hmapw, map_withDensity_comp_of_measurable hY.measurable_mk hd,
    Measure.map_congr hY.ae_eq_mk]

end DensityMap

end MatedCRTHarmonic.GMSCase1
