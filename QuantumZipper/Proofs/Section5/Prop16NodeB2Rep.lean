import QuantumZipper.Proofs.Section5.Prop16NodeB2Mean

/-!
# Proposition 1.6, Palm node B′: the window Palm identity from a representation

`prop16PalmWinMaskStmt_of_rep`: the remaining window node `Prop16PalmWinMaskStmt`
(`Prop16NodeB2Law.lean`) from two exactly stated nodes:

* `Prop16PalmRepStmt` (items (6), (7) of the D30 list): a countable family `μ_j` of admissible
  measures, each carried by a compact subset of `D ∪ (a,b)` (`LocAdm`), and jointly measurable
  `Φ_C` with `palmCanonMask C (ω, x) = Φ_C((h0 + X ω)(μ_·), x)` for `prop16Q`-a.e. `(ω, x)`, and,
  for every `x ∈ (a,b)`, `palmFixedMask C x ω = Φ_C((h0 + X + (γ/2)G_D(x,·))(μ_·), x)` `P`-a.s.
  (the Palm-shifted field is good);
* `Prop16PalmGlobalStmt`: the Palm formula on windows for such *global* coordinate families, in
  the intensity form `∫_{(a',b')} … d(palmMean)` (for coordinates carried by the window set this is
  `palm_formula_prop16_window_mean`, `Prop16NodeB2Mean.lean`, modulo `Prop16ActRegStmt` and
  `Prop16BdryL1Stmt`; the global form needs the mixed covariance on compacts of `D ∪ (a,b)`).

The step itself is the Palm formula applied to `G = 1_A ∘ Φ_C` (Duplantier–Sheffield,
arXiv:0808.1560, §3.3, p. 22), as in the free-field case `compProd_map_zoomCoords`
(`Prop17PalmABMain.lean`); own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal

namespace QuantumZipper

namespace Prop16Asm

/-- The raw coordinates `((h0 + X ω)(μ_j))_j`. -/
def rawCoords (h0 : ℂ → ℝ) {Ω : Type} (X : Ω → FieldSample) (μ : ℕ → Measure ℂ) (ω : Ω) :
    ℕ → ℝ :=
  fun j => (ofFun h0 + X ω) (μ j)

/-- The Palm-shifted raw coordinates `((h0 + X ω + (γ/2) G_D(x,·))(μ_j))_j` at `p = (ω, x)`. -/
def palmRawCoords (γ : ℝ) (D : Set ℂ) (c d : ℝ) (h0 : ℂ → ℝ) {Ω : Type} (X : Ω → FieldSample)
    (μ : ℕ → Measure ℂ) (p : Ω × ℝ) : ℕ → ℝ :=
  fun j => (ofFun h0 + palmMixedField γ D (realSet (Icc c d)) X p.2 p.1) (μ j)

/-- Admissible and carried by a compact subset of `D ∪ (a,b)`. -/
def LocAdm (D : Set ℂ) (a b : ℝ) (μ : Measure ℂ) : Prop :=
  IsAdmissibleH μ ∧ ∃ L : Set ℂ, IsCompact L ∧ L ⊆ D ∪ realSet (Ioo a b) ∧ μ Lᶜ = 0

/-- **Remaining node (global window Palm formula).** -/
def Prop16PalmGlobalStmt : Prop :=
  ∀ (γ : ℝ) (D : Set ℂ) (c d a b : ℝ) (h0 : ℂ → ℝ) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → FieldSample), Prop16PalmHyp γ D c d a b h0 P X →
    ∀ μ : ℕ → Measure ℂ, (∀ j, LocAdm D a b (μ j)) →
      Measurable (palmRawCoords γ D c d h0 X μ) ∧
      ∀ a' b' : ℝ, a < a' → b' < b → ∀ G : (ℕ → ℝ) × ℝ → ℝ≥0∞, Measurable G →
        ∫⁻ ω, ∫⁻ x in Ioo a' b', G (rawCoords h0 X μ ω, x) ∂(prop16Nu γ h0 a b (X ω)) ∂P =
          ∫⁻ x in Ioo a' b', ∫⁻ ω, G (palmRawCoords γ D c d h0 X μ (ω, x), x) ∂P
            ∂palmMean P (fun ω => prop16Nu γ h0 a b (X ω)) a b

/-- **Remaining node (measurable representation of the masked zoom coordinates, items (6),
(7)).** -/
def Prop16PalmRepStmt : Prop :=
  ∀ (γ : ℝ) (D : Set ℂ) (c d a b : ℝ) (h0 : ℂ → ℝ) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : Ω → FieldSample), Prop16PalmHyp γ D c d a b h0 P X →
    (∀ C, AEMeasurable (palmCanonMask γ C D a b h0 X) (prop16Q γ h0 a b P X)) →
    ∃ (μ : ℕ → Measure ℂ) (Φ : ℝ → (ℕ → ℝ) × ℝ → (ℕ → ℝ)), (∀ j, LocAdm D a b (μ j)) ∧
      (∀ C, Measurable (Φ C)) ∧
      (∀ C, palmCanonMask γ C D a b h0 X =ᵐ[prop16Q γ h0 a b P X]
        fun p => Φ C (rawCoords h0 X μ p.1, p.2)) ∧
      ∀ x ∈ Ioo a b, ∀ C, ∀ᵐ ω ∂P,
        palmFixedMask γ C D c d a b h0 X x ω = Φ C (palmRawCoords γ D c d h0 X μ (ω, x), x)

theorem indicator_one_comp_eq {α β : Type*} (f : α → β) (A : Set β) :
    (fun x => A.indicator (1 : β → ℝ≥0∞) (f x)) = (f ⁻¹' A).indicator 1 := by
  funext x
  by_cases hx : f x ∈ A
  · rw [indicator_of_mem hx, indicator_of_mem (show x ∈ f ⁻¹' A from hx)]; rfl
  · rw [indicator_of_notMem hx, indicator_of_notMem (show x ∉ f ⁻¹' A from hx)]

/-- **The window node from the representation and the global Palm formula.** -/
theorem prop16PalmWinMaskStmt_of_rep (hRep : Prop16PalmRepStmt) (hGl : Prop16PalmGlobalStmt) :
    Prop16PalmWinMaskStmt := by
  intro γ D c d a b h0 Ω _ P X hH hmeas
  obtain ⟨μ, Φ, hμ, hΦ, hY, hpalm⟩ := hRep γ D c d a b h0 P X hH hmeas
  obtain ⟨hPm, hPG⟩ := hGl γ D c d a b h0 P X hH μ hμ
  obtain ⟨⟨-, -, -, -, -, -, -, -, hX, hpos, hfin⟩, hν, -⟩ := hH
  set ν : Ω → Measure ℝ := fun ω => prop16Nu γ h0 a b (X ω) with hνdef
  have hraw : Measurable (rawCoords h0 X μ) := measurable_coords_mixed hX h0 μ
  set F : ℝ → Ω × ℝ → (ℕ → ℝ) := fun C p => Φ C (palmRawCoords γ D c d h0 X μ p, p.2)
    with hFdef
  have hF : ∀ C, Measurable (F C) := fun C => (hΦ C).comp (hPm.prodMk measurable_snd)
  refine ⟨F, hF, ?_, ?_⟩
  · have hmem : ∀ᵐ x ∂palmMean P ν a b, x ∈ Ioo a b := ae_iff.2 (palmMean_compl hν)
    filter_upwards [hmem] with x hx C
    filter_upwards [hpalm x hx C] with ω hω
    exact hω.symm
  · intro C A hA a' b' ha' hb'
    have hpre : palmPre P ν a b = (∫⁻ ω, ν ω (Icc a b) ∂P) • prop16Q γ h0 a b P X := by
      rw [show prop16Q γ h0 a b P X = _ from prop16Law_eq_smul_palmPre, smul_smul,
        ENNReal.mul_inv_cancel hpos.ne' hfin.ne, one_smul]
    set Y' : Ω × ℝ → ℕ → ℝ := fun p => Φ C (rawCoords h0 X μ p.1, p.2) with hY'def
    have hY' : Measurable Y' := (hΦ C).comp ((hraw.comp measurable_fst).prodMk measurable_snd)
    have hae : palmCanonMask γ C D a b h0 X =ᵐ[palmPre P ν a b] Y' := by
      rw [hpre]; exact Measure.ae_smul_measure (hY C) _
    have hW : MeasurableSet (univ ×ˢ Ioo a' b' : Set (Ω × ℝ)) :=
      MeasurableSet.univ.prod measurableSet_Ioo
    have hS : MeasurableSet (Y' ⁻¹' A ∩ univ ×ˢ Ioo a' b') := (hY' hA).inter hW
    have hsub : Ioo a' b' ⊆ Icc a b := Ioo_subset_Icc_self.trans (Icc_subset_Icc ha'.le hb'.le)
    rw [measure_congr (hae.mono fun p hp =>
      show (p ∈ palmCanonMask γ C D a b h0 X ⁻¹' A ∩ univ ×ˢ Ioo a' b') =
        (p ∈ Y' ⁻¹' A ∩ univ ×ˢ Ioo a' b') by
        rw [mem_inter_iff, mem_inter_iff, mem_preimage, mem_preimage, hp]),
      palmPre, Measure.bind_apply hS (aemeasurable_prop16Kernel hν hfin)]
    have hG : Measurable fun q : (ℕ → ℝ) × ℝ => A.indicator (1 : (ℕ → ℝ) → ℝ≥0∞) (Φ C q) :=
      (measurable_one.indicator hA).comp (hΦ C)
    have hL : ∀ᵐ ω ∂P, (Measure.dirac ω).prod ((ν ω).restrict (Icc a b))
        (Y' ⁻¹' A ∩ univ ×ˢ Ioo a' b') =
        ∫⁻ x in Ioo a' b', A.indicator 1 (Φ C (rawCoords h0 X μ ω, x)) ∂(ν ω) := by
      filter_upwards [ae_nu_ne_top hν hfin] with ω hω
      have : IsFiniteMeasure ((ν ω).restrict (Icc a b)) := isFiniteMeasure_restrict.mpr hω
      have hT : MeasurableSet ((fun x => Φ C (rawCoords h0 X μ ω, x)) ⁻¹' A) :=
        ((hΦ C).comp (measurable_const.prodMk measurable_id)) hA
      have e : Prod.mk ω ⁻¹' (Y' ⁻¹' A ∩ univ ×ˢ Ioo a' b') =
          (fun x => Φ C (rawCoords h0 X μ ω, x)) ⁻¹' A ∩ Ioo a' b' := by
        ext x; simp [Y']
      rw [Measure.dirac_prod, Measure.map_apply measurable_prodMk_left hS, e,
        Measure.restrict_apply (hT.inter measurableSet_Ioo), inter_assoc,
        inter_eq_left.2 hsub, indicator_one_comp_eq (fun x => Φ C (rawCoords h0 X μ ω, x)) A,
        lintegral_indicator_one hT, Measure.restrict_apply hT]
    rw [lintegral_congr_ae hL, hPG a' b' ha' hb' _ hG]
    refine lintegral_congr fun x => ?_
    have hU : MeasurableSet ((fun ω => F C (ω, x)) ⁻¹' A) :=
      ((hF C).comp measurable_prodMk_right) hA
    rw [indicator_one_comp_eq (fun ω => Φ C (palmRawCoords γ D c d h0 X μ (ω, x), x)) A]
    exact lintegral_indicator_one hU

/-- **Node B′ from the representation node and the global window Palm formula.** -/
theorem prop16PalmIdMaskStmt_of_rep (hRep : Prop16PalmRepStmt) (hGl : Prop16PalmGlobalStmt) :
    Prop16PalmIdMaskStmt :=
  prop16PalmIdMaskStmt_of_win (prop16PalmWinMaskStmt_of_rep hRep hGl)

end Prop16Asm

end QuantumZipper
