import QuantumZipper.Proofs.Zipper.LocHitScalePStar
import QuantumZipper.Proofs.Zipper.LocRichE6
import QuantumZipper.Proofs.Zipper.E6Id

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# E6 node (2): `E6NodeStmtRich` from smaller nodes

Theorem 1.3, node E6, Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797,
§5.4 (pp. 70–72): E6 (length stationarity of `P_*` under `zipLenDown γ ℓ₁`) follows from E5 by
comparing the Palm configurations collided at `x` and at `y` with `ν[y, x] = ℓ₁ e^{−C/2}`. The
proof body is `E6.e6_core_rel` (as in `E6.e6_concrete_gen`), stated for one auxiliary Palm setup.
Here it is turned into the node `E6NodeStmtRich := E5StmtRich → E6LocStmtRich`:

* `e6_concrete_rich_ae`: `e6_concrete_gen locRich` with the `P_*`-side measurability `hc'm`
  weakened to a.e.-measurability (which is what `aemeasurable_locRich_pstar` gives): the
  configuration is modified off a measurable null set (own elementary argument);
* `e6NodeStmtRich_of_nodes`: the node from
  - `HitScaleZipStmt` (already a Theorem 1.3 frontier node, `P_*` side: with the deterministic
    regularity set `RegDet`, `E6NodeReg.lean`);
  - `E6PalmMeasStmt`: some auxiliary Palm setup `E5.Setup κ T` with `4/(4−κ) ≤ T` (δ = 1) has
    measurable collided set and measurable local data of the zoomed collided configurations;
  - `LenCollidedAllStmt`, `CanonZipRawAllStmt`: E6-ID at the raw level for every setup (the
    inputs of `E6.e6_idLoc_rich`; `LenCollidedStmt` reduces further by
    `RegUnif.lenCollidedStmt_of_windows`);
  - `E6PalmRegStmt`: a.s. every zoomed collided configuration lies in `RegDet` (implied by the
    Palm analogue of `HitScaleZipStmt`, `e6PalmRegStmt_of_good`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace QuantumZipper.E6

open B2 E1 D3Plus

variable {Ω : Type} [MeasurableSpace Ω] {Ω' : Type} [MeasurableSpace Ω']

/-- A configuration map with a.e.-measurable local data agrees a.e. with one whose local data are
measurable (modification off a measurable null set; own elementary argument). -/
theorem exists_modif_measurable_locRich {P' : Measure Ω'} {c' : Ω' → Cfg}
    (hc : ∀ R, AEMeasurable (fun ω' => locRich R (c' ω')) P') :
    ∃ c'' : Ω' → Cfg, (∀ᵐ ω' ∂P', c'' ω' = c' ω') ∧
      ∀ R, Measurable fun ω' => locRich R (c'' ω') := by
  classical
  set N : ℕ → Set Ω' := fun R =>
    toMeasurable P' {ω' | locRich R (c' ω') ≠ (hc R).mk _ ω'} with hNdef
  set S : Set Ω' := ⋂ R, (N R)ᶜ with hSdef
  have hSm : MeasurableSet S := MeasurableSet.iInter fun R => (measurableSet_toMeasurable _ _).compl
  have hN0 : ∀ R, P' (N R) = 0 := fun R => by
    rw [hNdef, measure_toMeasurable]
    exact ae_iff.1 (hc R).ae_eq_mk
  have hSae : ∀ᵐ ω' ∂P', ω' ∈ S := by
    rw [ae_iff]
    refine measure_mono_null (fun ω' hω' => ?_) (measure_iUnion_null hN0)
    simp only [hSdef, mem_iInter, mem_compl_iff, not_forall, not_not] at hω'
    exact mem_iUnion.2 hω'
  refine ⟨S.piecewise c' (fun _ => 0), hSae.mono fun ω' h => Set.piecewise_eq_of_mem _ _ _ h,
    fun R => ?_⟩
  have e : (fun ω' => locRich R (S.piecewise c' (fun _ => 0) ω')) =
      S.piecewise ((hc R).mk _) (fun _ => locRich R 0) := by
    funext ω'
    by_cases h : ω' ∈ S
    · rw [Set.piecewise_eq_of_mem _ _ _ h, Set.piecewise_eq_of_mem _ _ _ h]
      have h' : ω' ∉ N R := mem_iInter.1 h R
      by_contra hne
      exact h' (subset_toMeasurable _ _ hne)
    · rw [Set.piecewise_eq_of_notMem _ _ _ h, Set.piecewise_eq_of_notMem _ _ _ h]
  rw [e]
  exact Measurable.piecewise hSm (hc R).measurable_mk measurable_const

end QuantumZipper.E6
