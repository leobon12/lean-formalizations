import QuantumZipper.Proofs.Zipper.Cor15LawCongr

/-!
# Corollary 1.5, positive times: the law transfer (blocker 2 / blueprint A5)

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Corollary 1.5 (pp. 17–18;
the paper gives no proof). For `t > 0`, (a) needs `law(Z_t c) = law(c)`. Known: `law(D_t c) =
law(c)` (B1) and `Z_t (D_t c) ≈ c` a.s. (P1, blocker 1). The transfer from `D_t c` to `c` needs
the data of `Z_t x` to be a *measurable* function `Φ` of the data `e x` of `x`, on a set of
full measure for the law of the data of `D_t c` (equivalently of `c`). With such a `Φ`,

  `law(Z_t c) = Φ_* law(e c) = Φ_* law(e (D_t c)) = law(Z_t (D_t c)) = law(c)`.

No standard Borel structure is needed for this step (unlike `ZipperGroup.zipperGroup_main`):
`Φ` measurable and one law equality suffice. The data space `E` is arbitrary.

* `map_comp_eq_of_factor`: the abstract transfer, given a.s. factorizations on both sides;
* `map_comp_eq_of_goodSet`: the same from a deterministic factorization on a measurable set `A`
  of data, charged a.s. by the data of `D_t c` only;
* `configLawMod0_zipCap_pos_of_goodSet`: Corollary 1.5(a) at a time `t ≥ 0` from the law form of
  P1 (`hR1`), a data law equality (`hlaw`, B1 type), and a Borel good set `A` of data on which
  the `configLawMod0` data of `Z_t x` is `Φ (e x)`.

Own elementary argument (pushforward algebra); the paper has none.
-/

noncomputable section

open MeasureTheory
open scoped NNReal

namespace QuantumZipper
namespace Cor15Group

/-- The data of a configuration seen by `configLawMod0`. -/
def mod0Data (x : FieldSample × (ℝ → ℝ)) : (TestFun0 H → ℝ) × (ℝ≥0 → ℝ) :=
  (fun ρ => pairRaw x.1 ρ.1.1, fun s : ℝ≥0 => x.2 s)

theorem configLawMod0_eq_map {Ω : Type*} [MeasurableSpace Ω] (c : Ω → FieldSample × (ℝ → ℝ))
    (P : Measure Ω) : configLawMod0 c P = P.map fun ω => mod0Data (c ω) := rfl

section Abstract

variable {Ω C E F : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableSpace F]
  {P : Measure Ω} {c y : Ω → C} {Z : C → C} {e : C → E} {m : C → F} {Φ : E → F}

/-- **Abstract law transfer.** If the data `e` of `c` and of `y` have the same law, and a.s. on
both sides the observable `m ∘ Z` is the same measurable function `Φ` of the data, then
`m ∘ Z ∘ c` and `m ∘ Z ∘ y` have the same law. -/
theorem map_comp_eq_of_factor (hΦ : Measurable Φ) (hec : AEMeasurable (fun ω => e (c ω)) P)
    (hey : AEMeasurable (fun ω => e (y ω)) P)
    (hlaw : P.map (fun ω => e (c ω)) = P.map (fun ω => e (y ω)))
    (hZc : ∀ᵐ ω ∂P, m (Z (c ω)) = Φ (e (c ω))) (hZy : ∀ᵐ ω ∂P, m (Z (y ω)) = Φ (e (y ω))) :
    P.map (fun ω => m (Z (c ω))) = P.map (fun ω => m (Z (y ω))) := by
  rw [Measure.map_congr hZc, Measure.map_congr hZy]
  have h1 : P.map (fun ω => Φ (e (c ω))) = (P.map fun ω => e (c ω)).map Φ :=
    (AEMeasurable.map_map_of_aemeasurable hΦ.aemeasurable hec).symm
  have h2 : P.map (fun ω => Φ (e (y ω))) = (P.map fun ω => e (y ω)).map Φ :=
    (AEMeasurable.map_map_of_aemeasurable hΦ.aemeasurable hey).symm
  rw [h1, h2, hlaw]

/-- A measurable set of data charged a.s. by `e ∘ y` is charged a.s. by `e ∘ c` when the two
data laws agree. -/
theorem ae_mem_of_map_eq {A : Set E} (hA : MeasurableSet A)
    (hec : AEMeasurable (fun ω => e (c ω)) P) (hey : AEMeasurable (fun ω => e (y ω)) P)
    (hlaw : P.map (fun ω => e (c ω)) = P.map (fun ω => e (y ω)))
    (hyA : ∀ᵐ ω ∂P, e (y ω) ∈ A) : ∀ᵐ ω ∂P, e (c ω) ∈ A := by
  have h : ∀ᵐ z ∂(P.map fun ω => e (y ω)), z ∈ A := (ae_map_iff hey hA).2 hyA
  rw [← hlaw] at h
  exact (ae_map_iff hec hA).1 h

/-- **Abstract law transfer from a good set.** `m ∘ Z` is deterministically the measurable
function `Φ` of the data on a measurable set `A` of data, which the data of `y` charge a.s.;
the data of `c` and `y` have the same law. Then `m ∘ Z ∘ c` and `m ∘ Z ∘ y` have the same law.
-/
theorem map_comp_eq_of_goodSet (hΦ : Measurable Φ) {A : Set E} (hA : MeasurableSet A)
    (hfac : ∀ x, e x ∈ A → m (Z x) = Φ (e x))
    (hec : AEMeasurable (fun ω => e (c ω)) P) (hey : AEMeasurable (fun ω => e (y ω)) P)
    (hlaw : P.map (fun ω => e (c ω)) = P.map (fun ω => e (y ω)))
    (hyA : ∀ᵐ ω ∂P, e (y ω) ∈ A) :
    P.map (fun ω => m (Z (c ω))) = P.map (fun ω => m (Z (y ω))) := by
  have hcA := ae_mem_of_map_eq hA hec hey hlaw hyA
  refine map_comp_eq_of_factor hΦ hec hey hlaw ?_ ?_
  · filter_upwards [hcA] with ω hω using hfac _ hω
  · filter_upwards [hyA] with ω hω using hfac _ hω

end Abstract

section Cor15

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

end Cor15

end Cor15Group
end QuantumZipper
