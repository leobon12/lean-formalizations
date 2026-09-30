import QuantumZipper.Proofs.Complex.JSLayerDecay
import QuantumZipper.Proofs.RS.HolderClosure
import QuantumZipper.Proofs.Thm14.FromThm13

/-!
# JS-ASSEMBLY: removability of the SLE doubled hull (DECISIONS D6, Option B)

For `κ ∈ (0,4)` and `T > 0`, almost surely the doubled reverse SLE hull
`Kd = closure K ∪ conj '' closure K`, `K = revHull (√κ B) T`, is conformally removable.

This is Jones–Smirnov, *Removability theorems for Sobolev functions and quasiconformal maps*,
Ark. Mat. 38 (2000), 263–279, Corollary 2 (p. 267: boundaries of Hölder domains are removable),
applied **through its proof** (blueprint `EXT_JS_BLUEPRINT.md` §2–§3, DECISIONS D6): the doubled
hull is covered by the images of `[-R,R]` under two half-plane charts, the Carathéodory extension
`F` of `revMap W T` and its Schwarz reflection `reflChart F` (`JS.charts_of_caratheodoryRevExt`);
both are Hölder on the chart box by Rohde–Schramm, *Basic properties of SLE*, Ann. of Math. 161
(2005), Thm 5.2 (p. 21), in the form `Blueprint.RevMapHolder` (proved: `RS.revMapHolder`);
Hölder charts have layer decay (node D, `JS.layerDecay_of_holder`), layer decay gives a finite
shadow sum (node C1), and finitely many charts with finite shadow sums covering `K` make `K`
removable (node C0, Jones–Smirnov's Lemma / proof of Thm 1 via the ACL criterion).

Nodes C0 (`removable_of_shadow`) and C1 (`shadowSum_lt_top_of_layerDecay`) are being finished in
other files; here they enter as the hypotheses `JS.C0Stmt` and `JS.C1Stmt`, which are **verbatim**
the blueprint §3 statements (with `ι : Type`), so that each is discharged by one line once proved.

## Main statements

* `JS.C0Stmt`, `JS.C1Stmt`: the blueprint statements of C0 and C1, as propositions;
* `JS.removable_doubledHull_of_car`: the deterministic assembly for one driver;
* `JS.ae_removable_doubledHull_of`: the TASKS §4 / D6 target, conditional on C0 and C1;
* `JS.ae_removable_doubledHull_optB`: the same with `RevMapHolder` discharged by `RS.revMapHolder`.
-/

noncomputable section

open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal ComplexConjugate

namespace QuantumZipper
namespace JS

/-- **Node C0** (blueprint §3, `removable_of_shadow`), as a proposition: a compact set covered by
the images of `[-R,R]` under finitely many charts with finite shadow sums is conformally
removable. -/
def C0Stmt : Prop :=
  ∀ {K : Set ℂ}, IsCompact K → ∀ {ι : Type} [Fintype ι] {R : ℝ} {F : ι → ℂ → ℂ},
    (∀ i, IsChart K R (F i)) → (∀ i, shadowSum R (F i) < ⊤) →
    K ⊆ ⋃ i, F i '' ((↑) '' Icc (-R) R) → IsConformallyRemovable K

/-- **Node C1** (blueprint §3, `shadowSum_lt_top_of_layerDecay`), as a proposition: layer decay
of a chart implies finiteness of its shadow sum. -/
def C1Stmt : Prop :=
  ∀ {K : Set ℂ} {R : ℝ} {F : ℂ → ℂ}, IsChart K R F → LayerDecay R F → shadowSum R F < ⊤

/-- Restriction of `IsHolderOn` to a subset. -/
theorem isHolderOn_mono {F : ℂ → ℂ} {S S' : Set ℂ} (h : IsHolderOn F S) (hS : S' ⊆ S) :
    IsHolderOn F S' := by
  obtain ⟨α, C, hα, hC⟩ := h
  exact ⟨α, C, hα, fun z hz w hw => hC z (hS hz) w (hS hw)⟩

/-- The chart box `[-2R,2R] × [0,4R]` lies in the square box `[-4R,4R] × [0,4R]`. -/
theorem chartBox_subset_square {R : ℝ} (hR : 0 < R) :
    Icc (-2 * R) (2 * R) ×ℂ Icc 0 (4 * R) ⊆ Icc (-(4 * R)) (4 * R) ×ℂ Icc 0 (4 * R) := by
  intro z hz
  rw [Complex.mem_reProdIm] at hz ⊢
  exact ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, hz.2⟩

/-- The doubled closure of a simple curve hull is compact. -/
theorem isCompact_doubledHull {K : Set ℂ} (hK : IsSimpleCurveHull K) :
    IsCompact (closure K ∪ conj '' closure K) := by
  obtain ⟨γ, hγc, -, -, -, hγK⟩ := hK
  have hc : IsCompact (γ '' Icc (0 : ℝ) 1) := isCompact_Icc.image_of_continuousOn hγc
  have hcl : IsCompact (closure K) := by
    refine hc.of_isClosed_subset isClosed_closure ?_
    rw [hγK]
    exact closure_minimal (image_mono Ioc_subset_Icc_self) hc.isClosed
  exact hcl.union (hcl.image Complex.continuous_conj)

/-- **Deterministic assembly (D6).** If the reverse hull of a continuous driver is a simple
curve hull and the Carathéodory extension `F` of `revMap W T` is Hölder on every box
`[-R,R] × [0,R]`, then (given nodes C0 and C1) the doubled hull is conformally removable. -/
theorem removable_doubledHull_of_car (hC0 : C0Stmt) (hC1 : C1Stmt) {W : ℝ → ℝ} {T : ℝ}
    (hW : Continuous W) (hT : 0 < T) (hK : IsSimpleCurveHull (revHull W T)) {F : ℂ → ℂ}
    (hF : Blueprint.IsCaratheodoryRevExt W T F)
    (hH : ∀ R : ℝ, 0 < R → IsHolderOn F (Icc (-R) R ×ℂ Icc 0 R)) :
    IsConformallyRemovable (closure (revHull W T) ∪ conj '' closure (revHull W T)) := by
  obtain ⟨R, -, hall⟩ := charts_of_caratheodoryRevExt hW hT hK hF
  obtain ⟨h1, h2, hcov⟩ := hall R le_rfl
  have hR : 0 < R := h1.pos
  have hHb := hH (4 * R) (by positivity)
  have hL1 : LayerDecay R F :=
    layerDecay_of_holder h1 (isHolderOn_mono hHb (chartBox_subset_square hR))
  have hL2 : LayerDecay R (reflChart F) :=
    layerDecay_of_holder h2 (isHolderOn_mono (isHolderOn_reflChart hHb) (chartBox_subset_square hR))
  refine hC0 (isCompact_doubledHull hK) (ι := Bool) (R := R)
    (F := fun b => cond b F (reflChart F)) (fun b => ?_) (fun b => ?_) ?_
  · cases b
    · exact h2
    · exact h1
  · cases b
    · exact hC1 h2 hL2
    · exact hC1 h1 hL1
  · intro z hz
    rcases hcov hz with hz | hz
    · exact mem_iUnion.2 ⟨true, hz⟩
    · exact mem_iUnion.2 ⟨false, hz⟩

/-- **`ae_removable_doubledHull`, conditional on C0 and C1** (TASKS §4 "EXT-JS / D6", DECISIONS
D6): `RevMapHolder → RevMapCaratheodory → RohdeSchrammSimple → ∀ κ ∈ (0,4), T > 0`, almost surely
the doubled reverse SLE hull `closure K ∪ conj '' closure K` is conformally removable. -/
theorem ae_removable_doubledHull_of (hC0 : C0Stmt) (hC1 : C1Stmt)
    (hRMH : Blueprint.RevMapHolder) (hCar : Blueprint.RevMapCaratheodory)
    (hRSS : Blueprint.RohdeSchrammSimple) :
    ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ T : ℝ, 0 < T → ∀ {Ω : Type} [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B P →
      ∀ᵐ ω ∂P, IsConformallyRemovable (closure (revHull (drive κ B ω) T) ∪
        conj '' closure (revHull (drive κ B ω) T)) := by
  intro κ hκ0 hκ4 T hT Ω _ P _ B hB
  filter_upwards [Thm14FromThm13.ae_isSimpleCurveHull_revHull hRSS hκ0 hκ4 hT P B hB,
    hRMH κ hκ0 hκ4 T hT P B hB, hB.cont, hB.eval_zero_ae_eq_zero] with ω hs hh hc h0
  have hWc : Continuous (drive κ B ω) := Thm14FromThm13.continuous_drive hc
  have hW0 : drive κ B ω 0 = 0 := by simp [drive, h0]
  obtain ⟨F, hF⟩ := hCar _ hWc hW0 T hT hs
  exact removable_doubledHull_of_car hC0 hC1 hWc hT hs hF (hh F hF)

/-- `ae_removable_doubledHull_of` with `Blueprint.RevMapHolder` discharged by `RS.revMapHolder`
(RS Thm 5.2, node RH3′). -/
theorem ae_removable_doubledHull_optB (hC0 : C0Stmt) (hC1 : C1Stmt)
    (hCar : Blueprint.RevMapCaratheodory) (hRSS : Blueprint.RohdeSchrammSimple) :
    ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ T : ℝ, 0 < T → ∀ {Ω : Type} [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B P →
      ∀ᵐ ω ∂P, IsConformallyRemovable (closure (revHull (drive κ B ω) T) ∪
        conj '' closure (revHull (drive κ B ω) T)) :=
  ae_removable_doubledHull_of hC0 hC1 RS.revMapHolder hCar hRSS

end JS
end QuantumZipper
