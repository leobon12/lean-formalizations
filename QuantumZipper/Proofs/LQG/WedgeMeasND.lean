import QuantumZipper.Proofs.LQG.WedgeMeasCoord
import QuantumZipper.Proofs.LQG.WedgeCanonical4
import QuantumZipper.Proofs.Probability.BMLLN
import QuantumZipper.Proofs.Section5.Prop17FieldLaw

/-!
# WEDGE-MEAS: wedge data are a.e.-measurable, wedges are a.s. good, R23 (c)

At the pinned mathlib, `Measure.map f P` for a non-a.e.-measurable `f` and `P ≠ 0` is a Dirac
mass (`Measure.map_of_not_aemeasurable_of_ne_zero`). So `IsQuantumWedge` forces the data map of
`Y` to be a.e.-measurable as soon as the **reference wedge law is not a Dirac mass**
(`fieldLawFull_wedgeRef_ne_dirac`). Proof (own argument, no published source needed; it only uses
Sheffield, arXiv:1012.4797, §1.6: the semicircle average of the wedge field at radius `e^{-t}` is
`A_t + Q t`, and the last-exit description of `A` on `t < 0`):

* the radial averages about `0` of the canonical wedge field `canonical γ W` are read by the full
  coordinates (`CoordsFull.radAvgReg_congr_full`) and equal `Q(−log r) + A(−log r − log s)`,
  `s = scaleParam γ W > 0` (`WedgeMeasCoord.radAvgReg_rescale_wedgeField`);
* if the law were `δ_c`, two a.s.-typical samples `ω₁, ω₂` would give
  `A(t − ℓ₁)(ω₁) = A(t − ℓ₂)(ω₂)` for all `t`; since `A(0) = 0` and `A > 0` on `(−∞,0)` a.s.
  (the backward process `B̃_s = √2 b'_s + (Q−α)s → +∞` by the Brownian law of large numbers
  `BMLLN.ae_tendsto_div_atTop`, Le Gall 2016, Exercise 2.25, so after its last zero it is
  positive), `ℓ₁ = ℓ₂` (`shift_eq_of_pos`) and `A(1)` would be a.s. constant, contradicting
  `A(1) = √2 b_1 + α − Q` with `b_1 ∼ N(0,1)`.

`s > 0` a.s. is where the two analytic inputs `WedgeCan4.WedgeFiniteNearZero` /
`WedgeInfiniteTotal` enter (via `WedgeCan4.ae_wedge_canonical_spec_of_inputs`); without them the
canonicalization may degenerate (`scaleParam = 0`), and then the reference data can be
deterministic junk, so the inputs are genuinely needed for this route.

Main results (all conditional on the two analytic inputs, `0 < γ < 2`):
`aemeasurable_dataFull_of_isQuantumWedge`, `wedgeDataAEMeasStmt_of_inputs`,
`wedgeGoodStmt_of_inputs`, `IsQuantumWedge.ae_unitArea` (TASKS R23 (c) form, without `hm`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal

namespace QuantumZipper

namespace WedgeMeasND

/-! ## 1. Deterministic lemmas -/

/-- A continuous path with `g 0 = 0` and `g → +∞` is positive after its last zero. -/
theorem pos_of_lastZero_lt {g : ℝ → ℝ} (hg : Continuous g) (h0 : g 0 = 0)
    (hinf : Tendsto g atTop atTop) {s : ℝ} (hs : lastZero g < s) : 0 < g s := by
  obtain ⟨M, hM⟩ := (hinf.eventually_gt_atTop 0).exists_forall_of_atTop
  have hbdd : BddAbove {s | 0 ≤ s ∧ g s = 0} := ⟨M, fun t ht => by
    by_contra hlt; push Not at hlt; exact (hM t hlt.le).ne' ht.2⟩
  have hL0 : 0 ≤ lastZero g := le_csSup hbdd ⟨le_rfl, h0⟩
  have hnz : ∀ t, lastZero g < t → g t ≠ 0 := fun t ht hz =>
    absurd (le_csSup hbdd ⟨hL0.trans ht.le, hz⟩) (not_le.2 ht)
  rcases lt_or_gt_of_ne (hnz s hs) with hneg | hpos
  · exfalso
    set s' := max M s with hs'
    have hss' : s ≤ s' := le_max_right _ _
    have hgs' : 0 < g s' := hM s' (le_max_left _ _)
    obtain ⟨c, hc, hgc⟩ := intermediate_value_Icc hss' hg.continuousOn
      (show (0 : ℝ) ∈ Icc (g s) (g s') from ⟨hneg.le, hgs'.le⟩)
    exact hnz c (hs.trans_le hc.1) hgc
  · exact hpos

/-- **Landmark.** Two paths vanishing at `0` and positive on `(−∞,0)` that agree up to shifts
`a`, `b` have `a = b`. -/
theorem shift_eq_of_pos {f g : ℝ → ℝ} {a b : ℝ} (hf0 : f 0 = 0) (hg0 : g 0 = 0)
    (hf : ∀ u < 0, 0 < f u) (hg : ∀ u < 0, 0 < g u) (h : ∀ t, f (t - a) = g (t - b)) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · have := h a; rw [sub_self, hf0] at this
    exact absurd this.symm (hg _ (by linarith)).ne'
  · exact hab
  · have := h b; rw [sub_self, hg0] at this
    exact absurd this (hf _ (by linarith)).ne'

/-- The wedge path is positive on `(−∞,0)` when `b'` is continuous, starts at `0` and
`b'_t / t → 0`. -/
theorem wedgePath_pos_of_neg {α Q : ℝ} (hαQ : α < Q) {b b' : ℝ≥0 → ℝ} (hb' : Continuous b')
    (hb'0 : b' 0 = 0) (hlim : Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ * b' t) atTop (𝓝 0))
    {u : ℝ} (hu : u < 0) : 0 < wedgePath α Q b b' u := by
  set Bt : ℝ → ℝ := fun s => Real.sqrt 2 * b' s.toNNReal - (α - Q) * s with hBt
  have hc : Continuous Bt :=
    (continuous_const.mul (hb'.comp continuous_real_toNNReal)).sub
      (continuous_const.mul continuous_id)
  have h0 : Bt 0 = 0 := by simp [hBt, hb'0]
  have hinf : Tendsto Bt atTop atTop := by
    have he : Tendsto (fun s : ℝ => ((s.toNNReal : ℝ))⁻¹ * b' s.toNNReal) atTop (𝓝 0) :=
      hlim.comp tendsto_real_toNNReal_atTop
    have hl : Tendsto (fun s : ℝ => Real.sqrt 2 * (((s.toNNReal : ℝ))⁻¹ * b' s.toNNReal) +
        (Q - α)) atTop (𝓝 (Q - α)) := by
      simpa using (he.const_mul (Real.sqrt 2)).add_const (Q - α)
    refine (tendsto_id.atTop_mul_pos (by linarith) hl).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with s hs
    simp only [id, hBt, Real.coe_toNNReal _ hs.le]
    field_simp
    ring
  have hw : wedgePath α Q b b' u = Bt (-u + lastZero Bt) := by
    simp only [wedgePath, not_le.2 hu, ↓reduceIte, hBt]
  rw [hw]
  exact pos_of_lastZero_lt hc h0 hinf (by linarith)

/-! ## 2. Almost-sure properties of the wedge process -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

theorem ae_wedgeProcess_landmark {α Q : ℝ} (hαQ : α < Q) {A : ℝ → Ω → ℝ}
    (hA : IsWedgeProcess α Q A P) : ∀ᵐ ω ∂P, A 0 ω = 0 ∧ ∀ u < 0, 0 < A u ω := by
  obtain ⟨B, B', hB, hB', -, hAe⟩ := hA
  filter_upwards [hB.toIsPreBrownianReal.eval_zero_ae_eq_zero, hB'.cont,
    hB'.toIsPreBrownianReal.eval_zero_ae_eq_zero, BMLLN.ae_tendsto_div_atTop hB']
    with ω h0 h1 h2 h3
  refine ⟨?_, fun u hu => ?_⟩
  · rw [hAe]; exact wedgePath_zero_of_start h0
  · rw [hAe]; exact wedgePath_pos_of_neg hαQ h1 h2 h3 hu

/-- `A(1)` is not a.s. constant. -/
theorem not_ae_wedgeProcess_one_eq [IsProbabilityMeasure P] {α Q : ℝ} {A : ℝ → Ω → ℝ}
    (hA : IsWedgeProcess α Q A P) (a : ℝ) : ¬ ∀ᵐ ω ∂P, A 1 ω = a := by
  intro h
  obtain ⟨B, B', hB, -, -, hAe⟩ := hA
  set c : ℝ := (a - (α - Q)) / Real.sqrt 2 with hc
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  have h1 : ∀ᵐ ω ∂P, B 1 ω = c := by
    filter_upwards [h] with ω hω
    rw [hAe] at hω
    simp only [wedgePath, zero_le_one, ↓reduceIte, Real.toNNReal_one, mul_one] at hω
    rw [hc, ← hω]; field_simp; ring
  have hlaw := (hB.toIsPreBrownianReal.hasLaw_eval 1)
  have := nullSingletonClass_gaussianReal (μ := 0) (v := (1 : ℝ≥0)) one_ne_zero
  have hnull : P {ω | B 1 ω = c} = 0 := by
    have : P ((B 1) ⁻¹' {c}) = 0 := by
      rw [← Measure.map_apply_of_aemeasurable hlaw.aemeasurable (measurableSet_singleton c),
        hlaw.map_eq]
      exact measure_singleton c
    exact this
  have hfull : P {ω | B 1 ω = c}ᶜ = 0 := by
    rw [← ae_iff.1 h1]; rfl
  have := measure_union_le (μ := P) {ω | B 1 ω = c} {ω | B 1 ω = c}ᶜ
  rw [union_compl_self, measure_univ, hnull, hfull, add_zero] at this
  exact absurd this (by simp)

/-! ## 3. The reference wedge law is not a Dirac mass -/

open WedgeCan4 in
theorem fieldLawFull_wedgeRef_ne_dirac {γ α : ℝ} (hfin : WedgeFiniteNearZero γ α)
    (hinf : WedgeInfiniteTotal γ α) (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < Qc γ)
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {X : Ω' → FieldSample} {A : ℝ → Ω' → ℝ} (hX : IsFreeGFFModConstH X P')
    (hA : IsWedgeProcess α (Qc γ) A P') (hI : IndepFun X (fun ω t => A t ω) P')
    (c : (ℕ → ℝ) × (TestFun H → ℝ)) :
    fieldLawFull H (WedgeMeas.wedgeRef γ X A) P' ≠ Measure.dirac c := by
  intro hc
  have hm := WedgeMeas.aemeasurable_wedgeRefData hX hA
    (LogSingGood.wedgeRefGoodAS_holds hγ hγ2 hα Ω' _ P' X A inferInstance hX hA hI) H
  have hS : MeasurableSet (Prod.fst ⁻¹' {c.1} : Set ((ℕ → ℝ) × (TestFun H → ℝ))) :=
    measurable_fst (measurableSet_singleton c.1)
  have hcoord : ∀ᵐ ω ∂P', CoordsFull.coordsFull (WedgeMeas.wedgeRef γ X A ω) = c.1 := by
    have h1 : ∀ᵐ d ∂(fieldLawFull H (WedgeMeas.wedgeRef γ X A) P'),
        d ∈ (Prod.fst ⁻¹' {c.1} : Set ((ℕ → ℝ) × (TestFun H → ℝ))) := by
      rw [hc]; exact (ae_dirac_iff hS).2 rfl
    exact (ae_map_iff hm hS).1 h1
  obtain ⟨G, hG⟩ := WedgeTK.exists_isRegVersion hX
  have hspec := ae_wedge_canonical_spec_of_inputs hfin hinf hγ hγ2 hα hX hA hI
  have hE : ∀ᵐ ω ∂P', CoordsFull.coordsFull (WedgeMeas.wedgeRef γ X A ω) = c.1 ∧
      WedgeTK.GoodRad (X ω) (G ω) ∧
      (∀ (n : ℕ) (z : ℂ), z ∈ Hbar → ∀ k : ℕ,
        X ω (foldedCircle (dyadicRoundC n z) (radius k)) = G ω (dyadicRoundC n z, radius k)) ∧
      Continuous (fun t => A t ω) ∧ (A 0 ω = 0 ∧ ∀ u < 0, 0 < A u ω) ∧
      0 < scaleParam γ (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ)) := by
    filter_upwards [hcoord, hG.ae_good, WedgeCan.ae_raw_dyadic hG,
      ae_continuous_wedgeProcess hA, ae_wedgeProcess_landmark hα hA, hspec]
      with ω h1 h2 h3 h4 h5 h6
    exact ⟨h1, h2, h3, h4, h5, h6.1⟩
  -- the radial averages of the reference field
  have hrad : ∀ ω, (CoordsFull.coordsFull (WedgeMeas.wedgeRef γ X A ω) = c.1 ∧
      WedgeTK.GoodRad (X ω) (G ω) ∧
      (∀ (n : ℕ) (z : ℂ), z ∈ Hbar → ∀ k : ℕ,
        X ω (foldedCircle (dyadicRoundC n z) (radius k)) = G ω (dyadicRoundC n z, radius k)) ∧
      Continuous (fun t => A t ω) ∧ (A 0 ω = 0 ∧ ∀ u < 0, 0 < A u ω) ∧
      0 < scaleParam γ (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ))) →
      ∀ r : ℝ, 0 < r → radAvgReg (WedgeMeas.wedgeRef γ X A ω) r = Qc γ * -Real.log r +
        A (-Real.log r - Real.log
          (scaleParam γ (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ)))) ω :=
    fun ω hω r hr =>
      WedgeMeasCoord.radAvgReg_rescale_wedgeField (A := fun t => A t ω) hω.2.1 hω.2.2.1
        hω.2.2.2.1 hω.2.2.2.2.2 hr
  obtain ⟨ω₀, hω₀⟩ := hE.exists
  refine not_ae_wedgeProcess_one_eq hA (A 1 ω₀) ?_
  filter_upwards [hE] with ω hω
  set ℓ := Real.log (scaleParam γ (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ)))
  set ℓ₀ := Real.log (scaleParam γ (wedgeField (lateralPart (X ω₀)) (fun t => A t ω₀) (Qc γ)))
  have hshift : ∀ t, A (t - ℓ) ω = A (t - ℓ₀) ω₀ := by
    intro t
    have hr : 0 < Real.exp (-t) := Real.exp_pos _
    have e1 := hrad ω hω _ hr
    have e2 := hrad ω₀ hω₀ _ hr
    rw [CoordsFull.radAvgReg_congr_full (hω.1.trans hω₀.1.symm) hr.le, e2,
      Real.log_exp, neg_neg] at e1
    linarith
  have hℓ := shift_eq_of_pos hω.2.2.2.2.1.1 hω₀.2.2.2.2.1.1 hω.2.2.2.2.1.2 hω₀.2.2.2.2.1.2
    hshift
  have := hshift (1 + ℓ)
  rwa [add_sub_cancel_right, ← hℓ, add_sub_cancel_right] at this

/-! ## 4. Consequences -/

/-- **WEDGE-MEAS (1).** Every quantum wedge has a.e.-measurable data (given the two analytic
inputs of R23). -/
theorem aemeasurable_dataFull_of_isQuantumWedge {γ α : ℝ}
    (hfin : WedgeCan4.WedgeFiniteNearZero γ α) (hinf : WedgeCan4.WedgeInfiniteTotal γ α)
    (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Y : Ω → FieldSample} (h : IsQuantumWedge γ α Y P) :
    AEMeasurable (fun ω => WedgeMeas.dataFull H (Y ω)) P := by
  by_contra hnm
  obtain ⟨hα, Ω', _, P', X, A, hP', hX, hA, hI, hlaw⟩ := h
  by_cases hP : P = 0
  · exact hnm (by rw [hP]; exact aemeasurable_zero_measure)
  have hmap := Measure.map_of_not_aemeasurable_of_ne_zero hnm hP
  exact fieldLawFull_wedgeRef_ne_dirac hfin hinf hγ hγ2 hα hX hA hI _
    (hlaw.symm.trans hmap)

theorem wedgeDataAEMeasStmt_of_inputs {γ α : ℝ} (hfin : WedgeCan4.WedgeFiniteNearZero γ α)
    (hinf : WedgeCan4.WedgeInfiniteTotal γ α) (hγ : 0 < γ) (hγ2 : γ < 2) :
    S5.FieldLaw.WedgeDataAEMeasStmt γ α :=
  fun _ Y h => aemeasurable_dataFull_of_isQuantumWedge hfin hinf hγ hγ2 (Y := Y) h

/-- **R23 (c)** in its TASKS form (no measurability hypothesis), conditional on the two analytic
inputs `WedgeFiniteNearZero` / `WedgeInfiniteTotal`. -/
theorem IsQuantumWedge.ae_unitArea {γ α : ℝ} (hfin : WedgeCan4.WedgeFiniteNearZero γ α)
    (hinf : WedgeCan4.WedgeInfiniteTotal γ α) (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type*} [MeasurableSpace Ω] {Y : Ω → FieldSample} {P : Measure Ω}
    (h : IsQuantumWedge γ α Y P) :
    ∀ᵐ ω ∂P, IsLQGGood γ (Y ω) ∧ qAreaMeasure γ (Y ω) (Metric.ball 0 1 ∩ H) = 1 :=
  WedgeCan4.IsQuantumWedge.ae_unitArea_of_inputs hfin hinf hγ hγ2 h
    (aemeasurable_dataFull_of_isQuantumWedge hfin hinf hγ hγ2 h)

/-- **WEDGE-MEAS (2).** Every quantum wedge is a.s. good (given the two analytic inputs). -/
theorem wedgeGoodStmt_of_inputs {γ α : ℝ} (hfin : WedgeCan4.WedgeFiniteNearZero γ α)
    (hinf : WedgeCan4.WedgeInfiniteTotal γ α) (hγ : 0 < γ) (hγ2 : γ < 2) :
    S5.FieldLaw.WedgeGoodStmt γ α :=
  fun _ Y h => (IsQuantumWedge.ae_unitArea hfin hinf hγ hγ2 (Y := Y) h).mono fun _ h => h.1

end WedgeMeasND

end QuantumZipper
