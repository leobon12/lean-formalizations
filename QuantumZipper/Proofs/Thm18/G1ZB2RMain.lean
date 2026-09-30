import QuantumZipper.Proofs.Thm18.G1ZB2RMeas

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1Z-B2R (2): `G1PalmConstStmt` from A, B0, B1-MEAS and the canonical-data identity

Theorem 1.8, G1 zoom, node B2-R. Sheffield, arXiv:1012.4797, proof of Proposition 1.7,
pp. 25–26 (rerooting at a point sampled from quantum length and zooming in by adding a constant;
the rerooted and the plain canonical field have the same law) and pp. 69–71.

Route (handoff/G1-ZSPLIT.md item 6): the functional `y ↦ Γ(loc(canonical(y + C)))` equals
`Θ(coordsFull(canonical y))` with `Θ` measurable (`g1zB2rPhi`, "`canonical(y + C) =
canonical(canonical y + C)`", the node `G1SideConstDataStmt`). Then

1. A (`G1RerootStmt`, all `R`, `Γ`) gives equal laws of the coordinates `coordsFull` of the
   rerooted and the plain canonical side field, for every `ℓ > 0` (`g1zB2r_map_eq`, π-λ);
2. the quantile change of variables of B1 (`g1_setLIntegral_lenLeft_eq_win`, B0) turns the
   Palm-window integral into `∫_{(0,U]} dℓ` of the rerooted functional (`g1zB2r_pathwise`);
3. Tonelli (joint measurability from B1-MEAS) and (1) make the `ℓ`-integrand constant.

Own bookkeeping on top of the cited nodes.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm

open D3Plus Factorization CoordsFull

/-- **B1, pathwise, for an arbitrary Borel integrand** (the proof of `g1PalmAvgStmt_of`): the
quantile change of variables onto the Palm window. -/
theorem g1zB2r_pathwise {γ : ℝ} (left : Bool) {x : FieldSample} {U : ℝ} (hU : 0 < U)
    (hreg : (∀ t : ℝ, g1SideNu γ left x {t} = 0) ∧
      (∀ u v : ℝ, u < v → Ioo u v ⊆ g1SideHalf left → 0 < g1SideNu γ left x (Ioo u v)) ∧
      (∀ b ∈ g1SideHalf left, g1SideNu γ left x (g1SideSeg left b) < ⊤) ∧
      g1SideNu γ left x (g1SideHalf left) = ⊤)
    {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ ℓ in Ioc 0 U, F (g1SidePt γ left x ℓ) =
      ∫⁻ b in g1Win γ left x U, F b ∂(g1SideNu γ left x) := by
  obtain ⟨hat, hpos, hfin, hinf⟩ := hreg
  cases left with
  | true =>
    set m := g1SideNu γ true x with hm
    have e1 : ∀ ℓ, g1SidePt γ true x ℓ = lenLeft m ℓ := fun _ => rfl
    have e2 : g1Win γ true x U = {b : ℝ | b < 0 ∧ m (Icc b 0) ≤ ENNReal.ofReal U} := rfl
    simp only [e1, e2]
    refine g1_setLIntegral_lenLeft_eq_win hU hat
      (fun u v huv hv => hpos u v huv fun y hy => (show y < 0 from hy.2.trans_le hv))
      (fun b => ?_) ?_ hF
    · by_cases hb : b < 0
      · exact (hfin b hb).ne
      · have hsub : Icc b 0 ⊆ {0} := fun y hy =>
          le_antisymm hy.2 ((not_lt.1 hb).trans hy.1)
        exact ne_top_of_le_ne_top ENNReal.zero_ne_top
          ((measure_mono hsub).trans (hat 0).le)
    · obtain ⟨n, hn⟩ := g1_exists_mass_gt (m := m) (S := Iio 0)
        (s := fun n : ℕ => Icc (-((n : ℝ) + 1)) 0)
        (fun a b hab => Icc_subset_Icc_left (by
          have : (a : ℝ) ≤ b := by exact_mod_cast hab
          linarith))
        (fun y hy => by
          obtain ⟨n, hn⟩ := exists_nat_gt (-y)
          exact mem_iUnion.2 ⟨n, ⟨by linarith, (show y < 0 from hy).le⟩⟩)
        hinf U
      exact ⟨(n : ℝ) + 1, by positivity, hn.le⟩
  | false =>
    set m := g1SideNu γ false x with hm
    have e1 : ∀ ℓ, g1SidePt γ false x ℓ = lenRight m ℓ := fun _ => rfl
    have e2 : g1Win γ false x U = {b : ℝ | 0 < b ∧ m (Icc 0 b) ≤ ENNReal.ofReal U} := rfl
    simp only [e1, e2]
    refine g1_setLIntegral_lenRight_eq_win hU hat
      (fun u v huv hu => hpos u v huv fun y hy => (show 0 < y from hu.trans_lt hy.1))
      (fun b => ?_) ?_ hF
    · by_cases hb : 0 < b
      · exact (hfin b hb).ne
      · have hsub : Icc 0 b ⊆ {0} := fun y hy =>
          le_antisymm (hy.2.trans (not_lt.1 hb)) hy.1
        exact ne_top_of_le_ne_top ENNReal.zero_ne_top
          ((measure_mono hsub).trans (hat 0).le)
    · obtain ⟨n, hn⟩ := g1_exists_mass_gt (m := m) (S := Ioi 0)
        (s := fun n : ℕ => Icc 0 ((n : ℝ) + 1))
        (fun a b hab => Icc_subset_Icc_right (by
          have : (a : ℝ) ≤ b := by exact_mod_cast hab
          linarith))
        (fun y hy => by
          obtain ⟨n, hn⟩ := exists_nat_gt y
          exact mem_iUnion.2 ⟨n, ⟨(show 0 < y from hy).le, by linarith⟩⟩)
        hinf U
      exact ⟨(n : ℝ) + 1, by positivity, hn.le⟩

/-- **Canonical data of the shifted side field** (node N′): a.s., for the side field `Z` and all
its real translates `y`, the data of `canonical (y + C)` are the measurable function
`g1zB2rPhi γ C` of the circle coordinates of `canonical y`
(`canonical (y + C) = canonical (canonical y + C)`; choice independence of the canonical
description for the shifted field, Sheffield (1.8) and pp. 25–26). -/
def G1SideConstDataStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (Y : Ω → FieldSample),
    Thm18Setting γ P B Y → Thm18Inputs γ P B Y → ∀ left : Bool, ∀ C : ℝ, ∀ᵐ ω ∂P,
      WedgeMeas.dataFull H (canonical γ (addConst (g1SideField γ B Y left ω) C)) =
        g1zB2rPhi γ C (coordsFull (canonical γ (g1SideField γ B Y left ω))) ∧
      ∀ b : ℝ, WedgeMeas.dataFull H (canonical γ
          (addConst (translate (g1SideField γ B Y left ω) (b : ℂ)) C)) =
        g1zB2rPhi γ C (coordsFull (canonical γ (translate (g1SideField γ B Y left ω) (b : ℂ))))

/-- **B2-R (`G1PalmConstStmt`) from A, B0, B1-MEAS and the canonical-data identity.** -/
theorem g1PalmConstStmt_of (hA : G1RerootStmt) (hB0 : G1SideBdryRegStmt)
    (hBM : G1SideTranslMeasStmt) (hN : G1SideConstDataStmt) : G1PalmConstStmt := by
  intro γ Ω _ P _ B Y hS hIn left U hU C R Γ hΓ hΓ1
  obtain ⟨hmeasZ, hrr⟩ := hA γ P B Y hS hIn left
  set Z := g1SideField γ B Y left with hZ
  set Θ : (ℕ → ℝ) → ℝ≥0∞ := fun c => Γ (g1zLocData R (g1zB2rPhi γ C c)) with hΘdef
  have hΘ : Measurable Θ :=
    hΓ.comp ((measurable_g1zLocData R).comp (measurable_g1zB2rPhi γ C))
  have hpt := hN γ P B Y hS hIn left C
  -- the right-hand side
  have hRHS : ∫⁻ ω, Γ (locFieldFull R (canonical γ (addConst (Z ω) C))) ∂P =
      ∫⁻ ω, Θ (coordsFull (canonical γ (Z ω))) ∂P := by
    refine lintegral_congr_ae (hpt.mono fun ω h => ?_)
    beta_reduce
    rw [locFieldFull_eq_g1zLocData, h.1]
  -- the left-hand side
  have hLHS : g1PalmIntC γ P Z left U C R Γ = ∫⁻ ω, ∫⁻ b in g1Win γ left (Z ω) U,
      Θ (coordsFull (canonical γ (translate (Z ω) (b : ℂ)))) ∂(g1SideNu γ left (Z ω)) ∂P := by
    unfold g1PalmIntC
    refine lintegral_congr_ae (hpt.mono fun ω h => ?_)
    refine lintegral_congr fun b => ?_
    rw [locFieldFull_eq_g1zLocData, h.2 b]
  have hm1 : ∀ᵐ ω ∂P, ∀ R' : ℕ,
      Measurable fun b : ℝ => locFieldFull R' (canonical γ (translate (Z ω) (b : ℂ))) := by
    rw [ae_all_iff]
    intro R'
    exact (hBM γ P B Y hS hIn left R').1
  have hjc : AEMeasurable (fun p : Ω × ℝ => coordsFull (canonical γ
      (translate (Z p.1) (g1SidePt γ left (Z p.1) p.2 : ℂ)))) (P.prod volume) :=
    g1zB2r_coordsFull_of_loc fun R' => (hBM γ P B Y hS hIn left R').2
  have hstep1 : ∫⁻ ω, ∫⁻ b in g1Win γ left (Z ω) U,
      Θ (coordsFull (canonical γ (translate (Z ω) (b : ℂ)))) ∂(g1SideNu γ left (Z ω)) ∂P =
      ∫⁻ ω, (∫⁻ ℓ in Ioc (0 : ℝ) U, Θ (coordsFull (canonical γ
        (translate (Z ω) (g1SidePt γ left (Z ω) ℓ : ℂ))))) ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [hB0 γ P B Y hS hIn left, hm1] with ω hreg hmω
    exact (g1zB2r_pathwise left hU hreg
      (hΘ.comp (g1zB2r_measurable_coordsFull_of_loc hmω))).symm
  have hjoint : AEMeasurable (Function.uncurry fun (ω : Ω) (ℓ : ℝ) => Θ (coordsFull
      (canonical γ (translate (Z ω) (g1SidePt γ left (Z ω) ℓ : ℂ)))))
      (P.prod (volume.restrict (Ioc (0 : ℝ) U))) := by
    have he : P.prod (volume.restrict (Ioc (0 : ℝ) U)) =
        (P.prod volume).restrict (univ ×ˢ Ioc 0 U) := by
      rw [← Measure.prod_restrict, Measure.restrict_univ]
    rw [he]
    exact hΘ.comp_aemeasurable hjc.restrict
  have hfix : ∀ᵐ ℓ ∂(volume : Measure ℝ), AEMeasurable (fun ω => coordsFull (canonical γ
      (translate (Z ω) (g1SidePt γ left (Z ω) ℓ : ℂ)))) P :=
    g1zB2r_ae_aemeasurable_snd hjc
  have hℓ : ∀ᵐ ℓ ∂(volume.restrict (Ioc (0 : ℝ) U)),
      ∫⁻ ω, Θ (coordsFull (canonical γ (translate (Z ω) (g1SidePt γ left (Z ω) ℓ : ℂ)))) ∂P =
        ∫⁻ ω, Θ (coordsFull (canonical γ (Z ω))) ∂P := by
    filter_upwards [ae_restrict_of_ae hfix, ae_restrict_mem measurableSet_Ioc] with ℓ hf hℓ
    have hpm : AEMeasurable (fun ω => coordsFull (canonical γ (Z ω))) P := hmeasZ.fst
    have hmap := g1zB2r_map_eq hf hpm (fun R' Γ' hΓ' hΓ'1 => by
      have := hrr ℓ hℓ.1 R' (fun y => Γ' y.1) (hΓ'.comp measurable_fst) (fun y => hΓ'1 y.1)
      simp only [g1RerootInt, locFieldFull_fst] at this
      exact this)
    rw [← lintegral_map' hΘ.aemeasurable hf, ← lintegral_map' hΘ.aemeasurable hpm, hmap]
  rw [hLHS, hstep1, lintegral_lintegral_swap hjoint, lintegral_congr_ae hℓ,
    g1z_inv_mul_setLIntegral_const hU, hRHS]

end Thm18Asm
end QuantumZipper
