import QuantumZipper.Proofs.Section5.Prop16D4WInGrow

/-!
# D4⁺ʷ inputs (part 6′): the area profile of an arbitrary quantum wedge

`ae_profileWeak_of_isQuantumWedge`: almost surely a `γ`-quantum wedge `W` (any sample with the
`fieldLawFull` law of the reference wedge `canonical γ (wedgeField …)`) is good and its half-ball
area profile `s ↦ μ_W(B_s ∩ ℍ)` is finite and strictly increasing on `[0, ∞)` (`ProfileWeak`).

Proof (own elementary argument, following the transfer `WedgeCan4.ae_unitArea_of_fieldLawFull_eq`):
the property is expressed through countably many radii (integers for finiteness, rationals for
strict monotonicity; the profile is monotone), hence as a measurable set `profSet` of full circle
coordinates; it holds a.s. for the reference wedge (its profile is that of the wedge field
rescaled by the positive scale, `Wire2.ae_hasAreaProfile_wedgeField`, R23 (a)), and transfers
through the equality of laws.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology ENNReal

namespace QuantumZipper

namespace Prop16Asm

open Prop16Area Factorization CoordsFull WedgeCan4 AreaProfile

/-- Finite and strictly increasing half-ball area profile. -/
def ProfileWeak (γ : ℝ) (x : FieldSample) : Prop :=
  (∀ s, profile (qAreaMeasure γ x) s ≠ ⊤) ∧ StrictMonoOn (profile (qAreaMeasure γ x)) (Ici 0)

/-- The countable form of `IsLQGGood ∧ ProfileWeak`. -/
def ProfProp (γ : ℝ) (x : FieldSample) : Prop :=
  IsLQGGood γ x ∧ (∀ n : ℕ, qAreaMeasure γ x (ball 0 n ∩ H) ≠ ⊤) ∧
    ∀ q1 q2 : ℚ, 0 ≤ q1 → q1 < q2 →
      qAreaMeasure γ x (ball 0 (q1 : ℝ) ∩ H) < qAreaMeasure γ x (ball 0 (q2 : ℝ) ∩ H)

/-- The area measure read off full coordinates (junk `0` off good samples). -/
def mgC (γ : ℝ) (c : ℕ → ℝ) : Measure ℂ := by
  classical
  exact if IsLQGGood γ (reconstruct (piC c)) then qAreaMeasure γ (reconstruct (piC c)) else 0

/-- `ProfProp` as a set of full coordinates. -/
def profSet (γ : ℝ) : Set (ℕ → ℝ) :=
  {c | IsLQGGood γ (reconstruct (piC c))} ∩ (⋂ n : ℕ, {c | mgC γ c (ball 0 n ∩ H) ≠ ⊤}) ∩
    ⋂ q1 : ℚ, ⋂ q2 : ℚ, {c | 0 ≤ q1 → q1 < q2 →
      mgC γ c (ball 0 (q1 : ℝ) ∩ H) < mgC γ c (ball 0 (q2 : ℝ) ∩ H)}

theorem measurableSet_profSet (γ : ℝ) : MeasurableSet (profSet γ) := by
  classical
  have hm : Measurable fun c : ℕ → ℝ => reconstruct (piC c) :=
    measurable_reconstruct.comp measurable_piC
  have hf : ∀ r : ℝ, Measurable fun c => mgC γ c (ball 0 r ∩ H) := fun r =>
    (Measure.measurable_coe (measurableSet_ball_inter_H r)).comp
      ((GoodMeas.measurable_qAreaMeasure_global γ).comp hm)
  refine ((hm (GoodMeas.measurableSet_isLQGGood γ)).inter (MeasurableSet.iInter fun n : ℕ =>
    (hf (n : ℝ)) (measurableSet_singleton ⊤).compl)).inter
    (MeasurableSet.iInter fun q1 => MeasurableSet.iInter fun q2 => ?_)
  rcases em (0 ≤ q1 ∧ q1 < q2) with h | h
  · convert measurableSet_lt (hf q1) (hf q2) using 1
    ext c; simp [h.1, h.2]
  · convert MeasurableSet.univ using 1
    ext c
    simp only [mem_ofPred_eq, mem_univ, iff_true]
    exact fun h1 h2 => absurd ⟨h1, h2⟩ h

theorem coordsFull_mem_profSet_iff (γ : ℝ) (x : FieldSample) :
    coordsFull x ∈ profSet γ ↔ ProfProp γ x := by
  classical
  have hg := GoodSample.isLQGGood_iff_reconstruct γ x
  have hq := qAreaMeasure_congr (avgReg_reconstruct_coords x) γ
  simp only [profSet, mgC, mem_inter_iff, mem_iInter, mem_ofPred_eq, piC_coordsFull, ProfProp]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    simp only [if_pos h1, hq] at h2 h3
    exact ⟨hg.1 h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    have h1' := hg.2 h1
    refine ⟨⟨h1', ?_⟩, ?_⟩ <;> simp only [if_pos h1', hq] <;> assumption

/-- Transfer of `ProfProp` through the equality of `fieldLawFull` laws. -/
theorem ae_profProp_of_fieldLawFull_eq {γ : ℝ} {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {Y : Ω → FieldSample} {P : Measure Ω} {Y' : Ω' → FieldSample}
    {P' : Measure Ω'} (hlaw : fieldLawFull H Y P = fieldLawFull H Y' P')
    (hY : AEMeasurable (fun ω => WedgeMeas.dataFull H (Y ω)) P)
    (hY' : AEMeasurable (fun ω => WedgeMeas.dataFull H (Y' ω)) P')
    (hgood : ∀ᵐ ω ∂P', ProfProp γ (Y' ω)) : ∀ᵐ ω ∂P, ProfProp γ (Y ω) := by
  set T : Set ((ℕ → ℝ) × (TestFun H → ℝ)) := (profSet γ)ᶜ ×ˢ Set.univ with hT
  have hTm : MeasurableSet T := (measurableSet_profSet γ).compl.prod MeasurableSet.univ
  have e1 : {ω | ¬ ProfProp γ (Y ω)} = (fun ω => WedgeMeas.dataFull H (Y ω)) ⁻¹' T := by
    ext ω; simp [hT, WedgeMeas.dataFull, coordsFull_mem_profSet_iff]
  have e2 : {ω | ¬ ProfProp γ (Y' ω)} = (fun ω => WedgeMeas.dataFull H (Y' ω)) ⁻¹' T := by
    ext ω; simp [hT, WedgeMeas.dataFull, coordsFull_mem_profSet_iff]
  rw [ae_iff, e1, ← Measure.map_apply_of_aemeasurable hY hTm]
  change fieldLawFull H Y P T = 0
  rw [hlaw]
  change P'.map (fun ω => WedgeMeas.dataFull H (Y' ω)) T = 0
  rw [Measure.map_apply_of_aemeasurable hY' hTm, ← e2]
  exact ae_iff.1 hgood

theorem profileWeak_of_profProp {γ : ℝ} {x : FieldSample} (h : ProfProp γ x) :
    IsLQGGood γ x ∧ ProfileWeak γ x := by
  obtain ⟨hg, hfin, hst⟩ := h
  refine ⟨hg, fun s => ?_, fun s hs t ht hst' => ?_⟩
  · obtain ⟨n, hn⟩ := exists_nat_ge s
    exact ne_top_of_le_ne_top (hfin n) (profile_mono _ hn)
  · obtain ⟨q1, h1, h1'⟩ := exists_rat_btwn hst'
    obtain ⟨q2, h2, h2'⟩ := exists_rat_btwn h1'
    have hq1 : (0 : ℚ) ≤ q1 := by exact_mod_cast (show (0 : ℝ) ≤ q1 from le_trans hs h1.le)
    exact (profile_mono _ h1.le).trans_lt ((hst q1 q2 hq1 (by exact_mod_cast h2)).trans_le
      (profile_mono _ h2'.le))

/-- **The area profile of an arbitrary `γ`-quantum wedge.** -/
theorem ae_profileWeak_of_isQuantumWedge {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {W : Ω → FieldSample} (hW : IsQuantumWedge γ γ W P) :
    ∀ᵐ ω ∂P, IsLQGGood γ (W ω) ∧ ProfileWeak γ (W ω) := by
  have hY := WedgeMeasND.aemeasurable_dataFull_of_isQuantumWedge
    (hfin := WedgeFinZero.wedgeFiniteNearZero_holds hγ hγ2 hW.1)
    (hinf := WedgeInf.wedgeInfiniteTotal hγ hγ2 hW.1) hγ hγ2 hW
  obtain ⟨hα, Ω', _, P', X, A, hP', hX, hA, hI, hlaw⟩ := hW
  have hgw := LogSingGood.wedgeRefGoodAS_holds hγ hγ2 hα Ω' _ P' X A hP' hX hA hI
  have hY' := WedgeMeas.aemeasurable_wedgeRefData hX hA hgw H
  have href : ∀ᵐ ω ∂P', ProfProp γ (WedgeMeas.wedgeRef γ X A ω) := by
    filter_upwards [Wire2.ae_hasAreaProfile_wedgeField hγ hγ2 hα hX hA hI,
      Wire2.ae_wedge_canonical_spec hγ hγ2 hα hX hA hI, hgw] with ω hp hc hg
    obtain ⟨hs, hcg, -⟩ := hc
    change ProfProp γ (canonical γ (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ)))
    set x := wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ)
    have e : ∀ r : ℝ, qAreaMeasure γ (canonical γ x) (ball 0 r ∩ H) =
        profile (qAreaMeasure γ x) (r * scaleParam γ x) := fun r => by
      rw [canonical, GoodTransforms.qAreaMeasure_rescale hg hγ hs,
        Measure.map_apply (show Measurable fun z : ℂ => z / (scaleParam γ x : ℂ) from
          measurable_id.div_const _) (isOpen_ball.inter isOpen_H).measurableSet,
        GoodTransforms.preimage_div_ball_inter_H hs, profile]
    refine ⟨hcg, fun n => by rw [e]; exact hp.1 _, fun q1 q2 hq1 hq12 => ?_⟩
    rw [e, e]
    have h1 : (0 : ℝ) ≤ q1 := by exact_mod_cast hq1
    have h12 : (q1 : ℝ) < q2 := by exact_mod_cast hq12
    exact hp.2.2.1 (mul_nonneg h1 hs.le) (mul_nonneg (h1.trans h12.le) hs.le)
      (mul_lt_mul_of_pos_right h12 hs)
  exact (ae_profProp_of_fieldLawFull_eq hlaw hY hY' href).mono fun _ h =>
    profileWeak_of_profProp h

end Prop16Asm

end QuantumZipper
