import MatedCRTHarmonic.GMSMain.MainResultsStatements
import MatedCRTHarmonic.GMSMain.T16DCorollary16
import MatedCRTHarmonic.GMSMain.T15BStatement
import MatedCRTHarmonic.GMSMain.T13Energy
import MatedCRTHarmonic.GMS3.Green
import MatedCRTHarmonic.Harmonic.Walk

/-!
# Adapters between the main-result definitions and their equivalent forms

Deterministic identities between the seven draft definitions (`MainResultsDraft`, verbatim copies of the draft surface v5)
and the vocabulary used in the [18] proofs:

* `energyOn_coe_finset`: `MainResults.energyOn G ↑S g = ofReal (GMS3.energy G S g)` for a `Finset S` (Definition 1.1);
* `exitGreen_coe_finset`: `MainResults.exitGreen G ↑U a a = GMS3.green G a U` (`rfl`; [18]);
* `dirichletEnergy_eq_eucEnergy`, `hasBoundedConvexity_iff`: `rfl` with `GMS3.eucEnergy` and T13I's
  `BoundedConvexityWith`;
* `cell_eq_cellAt`, `isHarmonicExtension_iff_t16d`, `isTutteEmbedding_iff_t16d`: `rfl` with T16D's local copies;
* `isHarmonicExtension_iff_t15b`: the `IsLUB` form is T15B's `sSup` form (compact cells, `f` continuous on `∂D`);
* `verticesMeeting_eq_vFin`, `isGMSDirichletSolution_of_isHarmonicExtension`: for a cellular embedding `H` and a
  bounded `D`, `V(D)` is the `Finset` `GMS3.vFin H D`, and every function `f_ε` of the draft (1.6) is a solution in
  T13I's sense (`IsGMSDirichletSolution`);
* `ofReal_le_div_deg`: the (1.8) normalizations `log ε⁻¹/A · deg(0) ≤ Gr` and `(1/A) log ε⁻¹ ≤ Gr / deg(0)` agree.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMSMain.MainResults

open MatedCRTHarmonic GMS3

section Graph

variable {V E : Type*} (G : LFMultigraph V E)

/-- **The draft energy on a finite vertex set is GMS3's energy**: `Energy(g; G(S))` of [18] Definition 1.1. -/
theorem energyOn_coe_finset (S : Finset V) (g : V → ℝ) :
    energyOn G (S : Set V) g = ENNReal.ofReal (GMS3.energy G S g) := by
  classical
  have hset : {e : E | G.src e ∈ (S : Set V) ∧ G.tgt e ∈ (S : Set V)} = ((edgesIn G S : Finset E) : Set E) := by
    ext e
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, mem_edgesIn]
  have h1 : energyOn G (S : Set V) g =
      ∑' e : ({e : E | G.src e ∈ (S : Set V) ∧ G.tgt e ∈ (S : Set V)} : Set E),
        ENNReal.ofReal ((g (G.src e.1) - g (G.tgt e.1)) ^ 2) := rfl
  rw [h1, hset, Finset.tsum_subtype' (edgesIn G S)
    (fun e => ENNReal.ofReal ((g (G.src e) - g (G.tgt e)) ^ 2)), GMS3.energy,
    ENNReal.ofReal_sum_of_nonneg (fun e _ => sq_nonneg _)]

/-- **The draft Green's function at the exit time is GMS3's Green function** (`rfl`). -/
theorem exitGreen_coe_finset (U : Finset V) (a : V) :
    exitGreen G (U : Set V) a a = GMS3.green G a U := rfl

/-- The draft energy vanishes for a function constant on `S`. -/
theorem energyOn_eq_zero_of_eqOn {S : Set V} {g : V → ℝ} {c : ℝ} (hg : ∀ x ∈ S, g x = c) :
    energyOn G S g = 0 := by
  refine ENNReal.tsum_eq_zero.mpr fun e => ?_
  rw [hg _ e.2.1, hg _ e.2.2, sub_self]
  simp

/-- `IsHarmonicExtension` is T16D's local copy (same body). -/
theorem isHarmonicExtension_iff_t16d (J : V → Set ℂ) (D : Set ℂ) (f : ℂ → ℝ) (g : V → ℝ) :
    IsHarmonicExtension G J D f g ↔ T16D.IsHarmonicExtension G J D f g := Iff.rfl

/-- `IsTutteEmbedding` is T16D's local copy (same body). -/
theorem isTutteEmbedding_iff_t16d (J : V → Set ℂ) (D : Set ℂ) (Φ : V → ℂ) :
    IsTutteEmbedding G J D Φ ↔ T16D.IsTutteEmbedding G J D Φ := Iff.rfl

/-- **The `IsLUB` form of (1.6) is T15B's `sSup` form** (compact cells, `f` continuous on `∂D`). -/
theorem isHarmonicExtension_iff_t15b {J : V → Set ℂ} (hJ : ∀ x, IsCompact (J x)) {D : Set ℂ} {f : ℂ → ℝ}
    (hf : ContinuousOn f (frontier D)) (g : V → ℝ) :
    IsHarmonicExtension G J D f g ↔ T15B.IsHarmonicExtension G J D f g :=
  T16D.isHarmonicExtension_iff_sSup hJ hf g

/-- The degree of a vertex of a locally finite multigraph without isolated vertices is nonzero. -/
theorem deg_ne_zero' (x : V) : (G.deg x : ℝ≥0∞) ≠ 0 := by
  exact_mod_cast Harmonic.deg_ne_zero G x

end Graph

/-- `dirichletEnergy` is GMS3's `eucEnergy` (`rfl`). -/
theorem dirichletEnergy_eq_eucEnergy (f : ℂ → ℝ) (D : Set ℂ) (hD : IsOpen D) (hf : DifferentiableOn ℝ f D) :
    dirichletEnergy f D hD hf = GMS3.eucEnergy f D := rfl

/-- `HasBoundedConvexity` is T13I's `BoundedConvexityWith` (`rfl`). -/
theorem hasBoundedConvexity_iff (C : ℝ) (D : Set ℂ) :
    HasBoundedConvexity C D ↔ GMSMain.BoundedConvexityWith C D := Iff.rfl

/-- `cell` is T16D's `cellAt` (`rfl`). -/
theorem cell_eq_cellAt (ε : ℝ) (η : C(ℝ, ℂ)) : cell ε η = T16D.cellAt ε η := rfl

/-- The cells `η([ε(x−1), εx])` are compact. -/
theorem isCompact_cell (ε : ℝ) (η : C(ℝ, ℂ)) (x : ℤ) : IsCompact (cell ε η x) :=
  isCompact_Icc.image η.continuous

section Embedding

variable {V E : Type*} {G : LFMultigraph V E} {o : V} (H : CellularEmbedding G o)

/-- For a bounded `D`, `V(D)` is GMS3's `Finset` `vFin H D`. -/
theorem verticesMeeting_eq_vFin {D : Set ℂ} (hDb : Bornology.IsBounded D) :
    verticesMeeting H.cell D = (vFin H D : Set V) := by
  ext x
  rw [Finset.mem_coe, mem_vFin H hDb]
  rfl

/-- **Every function `f_ε` of the draft (1.6) solves T13I's Dirichlet problem** (`IsGMSDirichletSolution`). -/
theorem isGMSDirichletSolution_of_isHarmonicExtension {D : Set ℂ} (hDb : Bornology.IsBounded D) {f : ℂ → ℝ}
    {g : V → ℝ} (hg : IsHarmonicExtension G H.cell D f g) : GMSMain.IsGMSDirichletSolution H D f g := by
  refine ⟨fun x hx hxB => ?_, fun x hx hxB => ?_⟩
  · have hx' : x ∈ verticesMeeting H.cell D := (mem_vFin H hDb).mp hx
    have hlub := (hg x hx').1 hxB
    exact (hlub.csSup_eq (hxB.image f)).symm
  · have hx' : x ∈ verticesMeeting H.cell D := (mem_vFin H hDb).mp hx
    exact (hg x hx').2 hxB

/-- **The draft energy on `V(D)` is GMS3's energy on `vFin H D`.** -/
theorem energyOn_verticesMeeting {D : Set ℂ} (hDb : Bornology.IsBounded D) (g : V → ℝ) :
    energyOn G (verticesMeeting H.cell D) g = ENNReal.ofReal (GMS3.energy G (vFin H D) g) := by
  rw [verticesMeeting_eq_vFin H hDb, energyOn_coe_finset]

/-- **The draft Green's function at the exit time from `V(D)` is GMS3's `green` on `vFin H D`.** -/
theorem exitGreen_verticesMeeting {D : Set ℂ} (hDb : Bornology.IsBounded D) (a : V) :
    exitGreen G (verticesMeeting H.cell D) a a = GMS3.green G a (vFin H D) := by
  rw [verticesMeeting_eq_vFin H hDb, exitGreen_coe_finset]

end Embedding

/-- **The two normalizations of (1.8)**: `log ε⁻¹/A · d ≤ x` gives `(1/A) log ε⁻¹ ≤ x / d` for `d ≠ 0`. -/
theorem ofReal_le_div_deg {A ε : ℝ} {d : ℕ} {x : ℝ≥0∞} (hd : (d : ℝ≥0∞) ≠ 0)
    (h : ENNReal.ofReal (Real.log ε⁻¹ / A * d) ≤ x) :
    ENNReal.ofReal (1 / A * Real.log ε⁻¹) ≤ x / (d : ℝ≥0∞) := by
  rw [ENNReal.le_div_iff_mul_le (Or.inl hd) (Or.inl (ENNReal.natCast_ne_top d))]
  by_cases hA : 0 ≤ Real.log ε⁻¹ / A
  · have h1 : ENNReal.ofReal (1 / A * Real.log ε⁻¹) * (d : ℝ≥0∞) = ENNReal.ofReal (Real.log ε⁻¹ / A * d) := by
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by rw [one_div_mul_eq_div]; exact hA)]
      congr 1
      ring
    rw [h1]
    exact h
  · have h0 : ENNReal.ofReal (1 / A * Real.log ε⁻¹) = 0 := by
      rw [ENNReal.ofReal_eq_zero, one_div_mul_eq_div]
      exact (lt_of_not_ge hA).le
    rw [h0, zero_mul]
    exact bot_le

end MatedCRTHarmonic.GMSMain.MainResults
