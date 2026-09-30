import QuantumZipper.Proofs.LQG.WedgeCanonical3
import QuantumZipper.Proofs.LQG.LogSingGood
import QuantumZipper.Proofs.LQG.PositivityArea
import QuantumZipper.Proofs.LQG.AreaExistenceAS
import QuantumZipper.Proofs.LQG.AreaOffsets
import QuantumZipper.Proofs.LQG.WedgeMeasurable
import QuantumZipper.Proofs.LQG.GoodMeasurable
import QuantumZipper.LQG.Wedge

/-!
# M4-A5-WEDGE (TASKS R23): assembly of (a), (b), (c) from the two analytic inputs

* `continuous_wedgePath`, `ae_continuous_wedgeProcess`: the wedge radial path is continuous for
  continuous driving paths started at `0` (the two branches glue at `t = 0` because the
  backward path vanishes at its last zero; if the zero set is unbounded, `lastZero` is the junk
  value `0` and the backward path vanishes there too).
* `ae_qAreaMeasure_wedgeField_eq`: the local density rule `μ_W = e^{γ g} μ_X` of
  `WedgeCan.qAreaMeasure_wedgeField_eq` holds almost surely, together with the free-field inputs
  (no circle atoms, positivity) and continuity of the profile `g` on `ℍ`.
* `ae_hasAreaProfile_wedgeField_of`: R23 (a) from the two analytic inputs (finite area of
  `B(0,a) ∩ ℍ`, infinite total area), via `AreaProfile.hasAreaProfile_of`.
* `ae_wedge_canonical_spec_of_profile`: R23 (b) from (a) (`CanonicalGood.scaleParam_spec`,
  `CanonicalGood.canonical_spec`, `LogSingGood.wedgeRefGoodAS_holds`).
* `ae_unitArea_of_fieldLawFull_eq`: transfer of the event
  `IsLQGGood γ x ∧ μ_x(B(0,1) ∩ ℍ) = 1` through an identity of `fieldLawFull` laws (the event
  is a measurable function of `coordsFull`).

Source: Sheffield, *Conformal weldings of random surfaces* (arXiv:1012.4797), §1.6, p. 21
("a finite amount of µ_h mass in each bounded neighborhood of 0 and an infinite amount in each
neighborhood of ∞", and the normalization `µ_h(B₁(0) ∩ ℍ) = 1`). The assembly steps are
elementary (own arguments).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace QuantumZipper

namespace WedgeCan4

/-! ## 1. Continuity of the wedge radial path -/

/-- A continuous path with `g 0 = 0` vanishes at its last zero (also in the junk case of an
unbounded zero set, where `lastZero g = 0`). -/
theorem apply_lastZero_eq_zero {g : ℝ → ℝ} (hg : Continuous g) (h0 : g 0 = 0) :
    g (lastZero g) = 0 := by
  unfold lastZero
  by_cases hb : BddAbove {s : ℝ | 0 ≤ s ∧ g s = 0}
  · have hc : IsClosed {s : ℝ | 0 ≤ s ∧ g s = 0} :=
      (isClosed_le continuous_const continuous_id).inter (isClosed_eq hg continuous_const)
    exact (hc.csSup_mem ⟨0, le_rfl, h0⟩ hb).2
  · rw [Real.sSup_of_not_bddAbove hb]; exact h0

/-- **The wedge radial path is continuous** for continuous driving paths started at `0`. -/
theorem continuous_wedgePath {α Q : ℝ} {b b' : ℝ≥0 → ℝ} (hb : Continuous b)
    (hb' : Continuous b') (h0 : b 0 = 0) (h0' : b' 0 = 0) :
    Continuous (wedgePath α Q b b') := by
  set Bt : ℝ → ℝ := fun s => Real.sqrt 2 * b' s.toNNReal - (α - Q) * s with hBt
  have hBtc : Continuous Bt :=
    (continuous_const.mul (hb'.comp continuous_real_toNNReal)).sub
      (continuous_const.mul continuous_id)
  have hBt0 : Bt 0 = 0 := by simp [hBt, h0']
  have hz : Bt (lastZero Bt) = 0 := apply_lastZero_eq_zero hBtc hBt0
  show Continuous fun t : ℝ => if 0 ≤ t then Real.sqrt 2 * b t.toNNReal + (α - Q) * t
    else Bt (-t + lastZero Bt)
  refine Continuous.if_le ?_ ?_ continuous_const continuous_id ?_
  · exact (continuous_const.mul (hb.comp continuous_real_toNNReal)).add
      (continuous_const.mul continuous_id)
  · exact hBtc.comp (continuous_neg.add continuous_const)
  · intro t ht
    have ht' : t = 0 := ht.symm
    subst ht'
    simp [h0, hz]

/-- **A wedge radial process has a.s. continuous paths.** -/
theorem ae_continuous_wedgeProcess {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {α Q : ℝ}
    {A : ℝ → Ω → ℝ} (hA : IsWedgeProcess α Q A P) : ∀ᵐ ω ∂P, Continuous fun t => A t ω := by
  obtain ⟨B, B', hB, hB', -, hAe⟩ := hA
  filter_upwards [hB.cont, hB'.cont, hB.toIsPreBrownianReal.eval_zero_ae_eq_zero,
    hB'.toIsPreBrownianReal.eval_zero_ae_eq_zero] with ω h1 h2 h3 h4
  have e : (fun t => A t ω) = wedgePath α Q (fun s => B s ω) (fun s => B' s ω) :=
    funext fun t => hAe ω t
  rw [e]
  exact continuous_wedgePath h1 h2 h3 h4

/-! ## 2. The density rule, almost surely -/

variable {γ α : ℝ} {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
  {X : Ω' → FieldSample} {A : ℝ → Ω' → ℝ}

/-- **Almost-sure form of the local density rule**, with the free-field inputs. Almost surely:
`μ_W = e^{γ g} μ_X` for the wedge field `W` (`g = WedgeCan.wedgeProfile`), `g` is continuous on
`ℍ`, `μ_X` has no mass on circles and charges every nonempty open subset of `ℍ`, and `μ_X` is
finite on `B(0,a) ∩ ℍ`. -/
theorem ae_qAreaMeasure_wedgeField_eq [IsProbabilityMeasure P'] (hX : IsFreeGFFModConstH X P')
    (hγ : 0 < γ) (hγ2 : γ < 2) {Q : ℝ} (hA : ∀ᵐ ω ∂P', Continuous fun t => A t ω) :
    ∀ᵐ ω ∂P',
      qAreaMeasure γ (wedgeField (lateralPart (X ω)) (fun t => A t ω) Q) =
        (qAreaMeasure γ (X ω)).withDensity (fun z => ENNReal.ofReal
          (Real.exp (γ * WedgeCan.wedgeProfile (X ω) (fun t => A t ω) Q z))) ∧
      ContinuousOn (WedgeCan.wedgeProfile (X ω) (fun t => A t ω) Q) H ∧
      (∀ a : ℝ, qAreaMeasure γ (X ω) (Metric.sphere 0 a ∩ H) = 0) ∧
      (∀ V : Set ℂ, IsOpen V → V ⊆ H → V.Nonempty → 0 < qAreaMeasure γ (X ω) V) ∧
      (∀ a : ℝ, qAreaMeasure γ (X ω) (Metric.ball 0 a ∩ H) < ⊤) := by
  obtain ⟨G, hG⟩ := WedgeTK.exists_isRegVersion hX (P := P')
  filter_upwards [hG.ae_good, WedgeCan.ae_raw_dyadic hG, hA,
    AreaExist.ae_isVagueLimitOn_qAreaMeasure hX (P := P') hγ hγ2,
    WedgeCan.ae_sphere_null_uncond hX (P := P') hγ hγ2,
    PositivityArea.ae_forall_pos_qAreaMeasure hX (P := P') hγ hγ2,
    FinArea.ae_qAreaMeasure_ball_lt_top hX (P := P') hγ hγ2] with ω hgood hraw hAc hv hs hp hf
  exact ⟨WedgeCan.qAreaMeasure_wedgeField_eq hgood hAc hraw ⟨_, hv⟩,
    WedgeCan.continuousOn_wedgeProfile_H hgood hAc Q, hs, hp, hf⟩

/-! ## 2b. Input (i) reduces to the unit half-disc -/

/-- The wedge profile is bounded on `{z ∈ closedBall 0 a | 1 ≤ ‖z‖}` (continuity away from `0`
on a compact set; own elementary argument). -/
theorem exists_bound_wedgeProfile_annulus {x : FieldSample} {F : ℂ × ℝ → ℝ} {A' : ℝ → ℝ}
    {Q : ℝ} (hG : WedgeTK.GoodRad x F) (hA : Continuous A') (a : ℝ) :
    ∃ C : ℝ, ∀ z ∈ Metric.closedBall (0 : ℂ) a ∩ {z : ℂ | 1 ≤ ‖z‖},
      WedgeCan.wedgeProfile x A' Q z ≤ C := by
  set K := Metric.closedBall (0 : ℂ) a ∩ {z : ℂ | 1 ≤ ‖z‖} with hK
  have hKc : IsCompact K :=
    (isCompact_closedBall 0 a).inter_right (isClosed_le continuous_const continuous_norm)
  have hpos : ∀ z ∈ K, 0 < ‖z‖ := fun z hz => lt_of_lt_of_le one_pos hz.2
  have hrad : ContinuousOn (fun z : ℂ => radAvgReg x ‖z‖) K :=
    ContinuousOn.congr (ContinuousOn.comp hG.1.1
        (continuousOn_const.prodMk continuous_norm.continuousOn)
        fun z hz => ⟨GaussTK.zero_mem_Hbar, hpos z hz⟩)
      fun z hz => hG.radAvgReg_eq (hpos z hz)
  have hlogc : ContinuousOn (fun z : ℂ => -Real.log ‖z‖) K := fun z hz =>
    ((Real.continuousAt_log (hpos z hz).ne').comp continuous_norm.continuousAt).neg.continuousWithinAt
  have hc : ContinuousOn (WedgeCan.wedgeProfile x A' Q) K := by
    unfold WedgeCan.wedgeProfile
    exact (hrad.neg.add (continuousOn_const.mul hlogc)).add (hA.comp_continuousOn hlogc)
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hc
  exact ⟨C, fun z hz => (Real.le_norm_self _).trans (hC z hz)⟩

/-- **Input (i) reduces to the unit half-disc.** Given the density rule and finiteness of the
free area on bounded sets, finiteness of the wedge area of `B(0,1) ∩ ℍ` gives finiteness on
every `B(0,a) ∩ ℍ` (the density `e^{γ g}` is bounded on `{1 ≤ ‖z‖ ≤ a}`). -/
theorem qAreaMeasure_wedgeField_ball_lt_top {γ : ℝ} {x : FieldSample} {F : ℂ × ℝ → ℝ}
    {A' : ℝ → ℝ} {Q : ℝ} (hG : WedgeTK.GoodRad x F) (hA : Continuous A')
    (hd : qAreaMeasure γ (wedgeField (lateralPart x) A' Q) =
      (qAreaMeasure γ x).withDensity
        (fun z => ENNReal.ofReal (Real.exp (γ * WedgeCan.wedgeProfile x A' Q z))))
    (hfx : ∀ a : ℝ, qAreaMeasure γ x (Metric.ball 0 a ∩ H) < ⊤)
    (h1 : qAreaMeasure γ (wedgeField (lateralPart x) A' Q) (Metric.ball 0 1 ∩ H) < ⊤)
    (hγ : 0 ≤ γ) (a : ℝ) :
    qAreaMeasure γ (wedgeField (lateralPart x) A' Q) (Metric.ball 0 a ∩ H) < ⊤ := by
  obtain ⟨C, hC⟩ := exists_bound_wedgeProfile_annulus (Q := Q) hG hA a
  set S := Metric.ball (0 : ℂ) a ∩ H ∩ {z : ℂ | 1 ≤ ‖z‖} with hS
  have hSm : MeasurableSet S :=
    (AreaProfile.measurableSet_ball_inter_H a).inter
      (measurableSet_le measurable_const measurable_norm)
  have hsub : Metric.ball (0 : ℂ) a ∩ H ⊆ (Metric.ball 0 1 ∩ H) ∪ S := by
    intro z hz
    by_cases h : ‖z‖ < 1
    · exact Or.inl ⟨by simpa [Metric.mem_ball, dist_zero_right] using h, hz.2⟩
    · exact Or.inr ⟨hz, le_of_not_gt h⟩
  have hS2 : qAreaMeasure γ (wedgeField (lateralPart x) A' Q) S < ⊤ := by
    rw [hd]
    have hb : ∀ w ∈ S, ENNReal.ofReal (Real.exp (γ * WedgeCan.wedgeProfile x A' Q w)) ≤
        ENNReal.ofReal (Real.exp (γ * C)) * (fun _ : ℂ => (1 : ℝ≥0∞)) w := by
      intro w hw
      rw [mul_one]
      refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ hγ))
      exact hC w ⟨Metric.ball_subset_closedBall hw.1.1, hw.2⟩
    refine (AreaLogSing.withDensity_le_const_mul hSm measurable_const hb).trans_lt ?_
    rw [withDensity_const, Measure.smul_apply, one_smul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      ((measure_mono (fun z hz => hz.1 : S ⊆ Metric.ball 0 a ∩ H)).trans_lt (hfx a))
  exact (measure_mono hsub).trans_lt
    ((measure_union_le _ _).trans_lt (ENNReal.add_lt_top.2 ⟨h1, hS2⟩))

/-- **Input (i), almost surely, from the unit half-disc.** -/
theorem ae_ball_lt_top_of_unit [IsProbabilityMeasure P'] (hX : IsFreeGFFModConstH X P')
    (hγ : 0 < γ) (hγ2 : γ < 2) {Q : ℝ} (hA : ∀ᵐ ω ∂P', Continuous fun t => A t ω)
    (h1 : ∀ᵐ ω ∂P', qAreaMeasure γ (wedgeField (lateralPart (X ω)) (fun t => A t ω) Q)
      (Metric.ball 0 1 ∩ H) < ⊤) :
    ∀ᵐ ω ∂P', ∀ a : ℝ, qAreaMeasure γ (wedgeField (lateralPart (X ω)) (fun t => A t ω) Q)
      (Metric.ball 0 a ∩ H) < ⊤ := by
  obtain ⟨G, hG⟩ := WedgeTK.exists_isRegVersion hX (P := P')
  filter_upwards [hG.ae_good, WedgeCan.ae_raw_dyadic hG, hA,
    AreaExist.ae_isVagueLimitOn_qAreaMeasure hX (P := P') hγ hγ2,
    FinArea.ae_qAreaMeasure_ball_lt_top hX (P := P') hγ hγ2, h1] with ω hgood hraw hAc hv hf h1ω
  exact qAreaMeasure_wedgeField_ball_lt_top hgood hAc
    (WedgeCan.qAreaMeasure_wedgeField_eq hgood hAc hraw ⟨_, hv⟩) hf h1ω hγ.le

/-- **R23 (a) from the two analytic inputs.** If almost surely the wedge field has finite area
on every `B(0,a) ∩ ℍ` and infinite total area, then almost surely it has an area profile. -/
theorem ae_hasAreaProfile_wedgeField_of [IsProbabilityMeasure P']
    (hX : IsFreeGFFModConstH X P') (hγ : 0 < γ) (hγ2 : γ < 2)
    (hA : IsWedgeProcess α (Qc γ) A P')
    (hfin : ∀ᵐ ω ∂P', ∀ a : ℝ,
      qAreaMeasure γ (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ))
        (Metric.ball 0 a ∩ H) < ⊤)
    (hH : ∀ᵐ ω ∂P',
      qAreaMeasure γ (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ)) H = ⊤) :
    ∀ᵐ ω ∂P', AreaProfile.HasAreaProfile γ
      (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ)) := by
  filter_upwards [ae_qAreaMeasure_wedgeField_eq hX hγ hγ2 (Q := Qc γ)
    (ae_continuous_wedgeProcess hA), hfin, hH] with ω ⟨hd, hc, hs, hp, _⟩ hf hh
  exact AreaProfile.hasAreaProfile_of hf
    (fun a => WedgeCan.qAreaMeasure_wedgeField_sphere_eq_zero hd (hs a))
    (fun V hV hVH hne => WedgeCan.qAreaMeasure_wedgeField_pos hd hc hp hV hVH hne) hh

/-- **R23 (b) from (a).** -/
theorem ae_wedge_canonical_spec_of_profile {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {X : Ω' → FieldSample} {A : ℝ → Ω' → ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < Qc γ)
    (hX : IsFreeGFFModConstH X P') (hA : IsWedgeProcess α (Qc γ) A P')
    (hI : IndepFun X (fun ω t => A t ω) P')
    (hprof : ∀ᵐ ω ∂P', AreaProfile.HasAreaProfile γ
      (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ))) :
    ∀ᵐ ω ∂P', 0 < scaleParam γ (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ)) ∧
      IsLQGGood γ (canonical γ (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ))) ∧
      qAreaMeasure γ (canonical γ (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ)))
        (Metric.ball 0 1 ∩ H) = 1 := by
  filter_upwards [hprof, LogSingGood.wedgeRefGoodAS_holds hγ hγ2 hα Ω' _ P' X A
    inferInstance hX hA hI] with ω hp hg
  exact ⟨(CanonicalGood.scaleParam_spec hp).1, CanonicalGood.canonical_spec hγ hg hp⟩

/-! ## 3. Transfer of the unit-area event through `fieldLawFull` -/

section Transfer

open Factorization CoordsFull

/-- Every coordinate read by `coords` is also read by `coordsFull` (radius `2^{-k} = 1/2^k`). -/
theorem exists_fullIndex_eq_dyadic (i : ℕ) :
    ∃ j, fullIndex j = ((dyadicIndex i).1, radius (dyadicIndex i).2) := by
  refine ⟨Encodable.encode (((Denumerable.ofNat (ℤ × ℤ × ℕ × ℕ) i).1,
    (Denumerable.ofNat (ℤ × ℤ × ℕ × ℕ) i).2.1, (Denumerable.ofNat (ℤ × ℤ × ℕ × ℕ) i).2.2.1, 0,
    (Denumerable.ofNat (ℤ × ℤ × ℕ × ℕ) i).2.2.2) : ℤ × ℤ × ℕ × ℕ × ℕ), ?_⟩
  simp only [fullIndex, Denumerable.ofNat_encode, dyadicIndex]
  rw [radius_eq_div]
  simp

/-- The measurable map `coordsFull x ↦ coords x`. -/
def piC (c : ℕ → ℝ) : ℕ → ℝ := fun i => c (Classical.choose (exists_fullIndex_eq_dyadic i))

theorem measurable_piC : Measurable piC :=
  measurable_pi_iff.2 fun _ => measurable_pi_apply _

theorem piC_coordsFull (x : FieldSample) : piC (coordsFull x) = coords x := by
  funext i
  simp only [piC, coordsFull, Classical.choose_spec (exists_fullIndex_eq_dyadic i), coords]

open Classical in
/-- The unit-area event, read on the full coordinates. -/
def unitSet (γ : ℝ) : Set (ℕ → ℝ) :=
  {c | IsLQGGood γ (reconstruct (piC c)) ∧
    (if IsLQGGood γ (reconstruct (piC c)) then qAreaMeasure γ (reconstruct (piC c)) else 0)
      (Metric.ball 0 1 ∩ H) = 1}

theorem measurableSet_unitSet (γ : ℝ) : MeasurableSet (unitSet γ) := by
  have hm : Measurable fun c : ℕ → ℝ => reconstruct (piC c) :=
    measurable_reconstruct.comp measurable_piC
  have h1 : MeasurableSet {c : ℕ → ℝ | IsLQGGood γ (reconstruct (piC c))} :=
    hm (GoodMeas.measurableSet_isLQGGood γ)
  have h2 := (Measure.measurable_coe (AreaProfile.measurableSet_ball_inter_H 1)).comp
    ((GoodMeas.measurable_qAreaMeasure_global γ).comp hm)
  exact h1.inter (h2 (measurableSet_singleton 1))

theorem coordsFull_mem_unitSet_iff (γ : ℝ) (x : FieldSample) :
    coordsFull x ∈ unitSet γ ↔
      IsLQGGood γ x ∧ qAreaMeasure γ x (Metric.ball 0 1 ∩ H) = 1 := by
  classical
  have hg := GoodSample.isLQGGood_iff_reconstruct γ x
  have hq := qAreaMeasure_congr (avgReg_reconstruct_coords x) γ
  simp only [unitSet, Set.mem_ofPred_eq, piC_coordsFull]
  constructor
  · rintro ⟨h1, h2⟩
    rw [if_pos h1, hq] at h2
    exact ⟨hg.1 h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨hg.2 h1, ?_⟩
    rw [if_pos (hg.2 h1), hq, h2]

/-- **Transfer.** If `Y` and `Y'` have the same `fieldLawFull` law, both data maps are
a.e.-measurable, and a.s. `Y'` is good with unit area in `B(0,1) ∩ ℍ`, then so is `Y`.
(The a.e.-measurability of the data of `Y` is needed: at the pinned mathlib the push-forward
under a non-a.e.-measurable map is a Dirac mass, `Measure.map_of_not_aemeasurable_of_ne_zero`.) -/
theorem ae_unitArea_of_fieldLawFull_eq {γ : ℝ} {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {Y : Ω → FieldSample} {P : Measure Ω} {Y' : Ω' → FieldSample}
    {P' : Measure Ω'} (hlaw : fieldLawFull H Y P = fieldLawFull H Y' P')
    (hY : AEMeasurable (fun ω => WedgeMeas.dataFull H (Y ω)) P)
    (hY' : AEMeasurable (fun ω => WedgeMeas.dataFull H (Y' ω)) P')
    (hgood : ∀ᵐ ω ∂P', IsLQGGood γ (Y' ω) ∧ qAreaMeasure γ (Y' ω) (Metric.ball 0 1 ∩ H) = 1) :
    ∀ᵐ ω ∂P, IsLQGGood γ (Y ω) ∧ qAreaMeasure γ (Y ω) (Metric.ball 0 1 ∩ H) = 1 := by
  set T : Set ((ℕ → ℝ) × (TestFun H → ℝ)) := (unitSet γ)ᶜ ×ˢ Set.univ with hT
  have hTm : MeasurableSet T := (measurableSet_unitSet γ).compl.prod MeasurableSet.univ
  have e1 : {ω | ¬ (IsLQGGood γ (Y ω) ∧ qAreaMeasure γ (Y ω) (Metric.ball 0 1 ∩ H) = 1)} =
      (fun ω => WedgeMeas.dataFull H (Y ω)) ⁻¹' T := by
    ext ω; simp [hT, WedgeMeas.dataFull, coordsFull_mem_unitSet_iff]
  have e2 : {ω | ¬ (IsLQGGood γ (Y' ω) ∧ qAreaMeasure γ (Y' ω) (Metric.ball 0 1 ∩ H) = 1)} =
      (fun ω => WedgeMeas.dataFull H (Y' ω)) ⁻¹' T := by
    ext ω; simp [hT, WedgeMeas.dataFull, coordsFull_mem_unitSet_iff]
  rw [ae_iff, e1, ← Measure.map_apply_of_aemeasurable hY hTm]
  change fieldLawFull H Y P T = 0
  rw [hlaw]
  change P'.map (fun ω => WedgeMeas.dataFull H (Y' ω)) T = 0
  rw [Measure.map_apply_of_aemeasurable hY' hTm, ← e2]
  exact ae_iff.1 hgood

end Transfer

/-! ## 4. (a), (b), (c) from the two analytic inputs -/

/-- **Analytic input (i)** of R23 (a): a.s. the wedge field has finite area on the unit half-disc
`B(0,1) ∩ ℍ` (Sheffield p. 21: "a finite amount of µ_h mass in each bounded neighborhood of 0";
the other bounded sets follow, `ae_ball_lt_top_of_unit`). -/
def WedgeFiniteNearZero (γ α : ℝ) : Prop :=
  ∀ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (X : Ω' → FieldSample)
    (A : ℝ → Ω' → ℝ), IsProbabilityMeasure P' → IsFreeGFFModConstH X P' →
    IsWedgeProcess α (Qc γ) A P' → IndepFun X (fun ω t => A t ω) P' →
    ∀ᵐ ω ∂P', qAreaMeasure γ (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ))
      (Metric.ball 0 1 ∩ H) < ⊤

/-- **Analytic input (ii)** of R23 (a): a.s. the wedge field has infinite total area
(Sheffield p. 21: "an infinite amount in each neighborhood of ∞"). -/
def WedgeInfiniteTotal (γ α : ℝ) : Prop :=
  ∀ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (X : Ω' → FieldSample)
    (A : ℝ → Ω' → ℝ), IsProbabilityMeasure P' → IsFreeGFFModConstH X P' →
    IsWedgeProcess α (Qc γ) A P' → IndepFun X (fun ω t => A t ω) P' →
    ∀ᵐ ω ∂P', qAreaMeasure γ (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ)) H = ⊤

/-- R23 (a), conditional on the two analytic inputs. -/
theorem ae_hasAreaProfile_wedgeField_of_inputs (hfin : WedgeFiniteNearZero γ α)
    (hinf : WedgeInfiniteTotal γ α) (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {X : Ω' → FieldSample} {A : ℝ → Ω' → ℝ} (hX : IsFreeGFFModConstH X P')
    (hA : IsWedgeProcess α (Qc γ) A P') (hI : IndepFun X (fun ω t => A t ω) P') :
    ∀ᵐ ω ∂P', AreaProfile.HasAreaProfile γ
      (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ)) :=
  ae_hasAreaProfile_wedgeField_of hX hγ hγ2 hA (ae_ball_lt_top_of_unit hX hγ hγ2
      (ae_continuous_wedgeProcess hA) (hfin Ω' _ P' X A inferInstance hX hA hI))
    (hinf Ω' _ P' X A inferInstance hX hA hI)

/-- R23 (b), conditional on the two analytic inputs. -/
theorem ae_wedge_canonical_spec_of_inputs (hfin : WedgeFiniteNearZero γ α)
    (hinf : WedgeInfiniteTotal γ α) (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < Qc γ)
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {X : Ω' → FieldSample} {A : ℝ → Ω' → ℝ} (hX : IsFreeGFFModConstH X P')
    (hA : IsWedgeProcess α (Qc γ) A P') (hI : IndepFun X (fun ω t => A t ω) P') :
    ∀ᵐ ω ∂P', 0 < scaleParam γ (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ)) ∧
      IsLQGGood γ (canonical γ (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ))) ∧
      qAreaMeasure γ (canonical γ (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ)))
        (Metric.ball 0 1 ∩ H) = 1 :=
  ae_wedge_canonical_spec_of_profile hγ hγ2 hα hX hA hI
    (ae_hasAreaProfile_wedgeField_of_inputs hfin hinf hγ hγ2 hX hA hI)

/-- R23 (c), conditional on the two analytic inputs and on the a.e.-measurability of the data
of `Y` (see `ae_unitArea_of_fieldLawFull_eq`; this is `S5.FieldLaw.WedgeDataAEMeasStmt`). -/
theorem IsQuantumWedge.ae_unitArea_of_inputs (hfin : WedgeFiniteNearZero γ α)
    (hinf : WedgeInfiniteTotal γ α) (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type*} [MeasurableSpace Ω] {Y : Ω → FieldSample} {P : Measure Ω}
    (h : IsQuantumWedge γ α Y P) (hm : AEMeasurable (fun ω => WedgeMeas.dataFull H (Y ω)) P) :
    ∀ᵐ ω ∂P, IsLQGGood γ (Y ω) ∧ qAreaMeasure γ (Y ω) (Metric.ball 0 1 ∩ H) = 1 := by
  obtain ⟨hα, Ω', _, P', X, A, hP', hX, hA, hI, hlaw⟩ := h
  have hprof := ae_hasAreaProfile_wedgeField_of_inputs hfin hinf hγ hγ2 hX hA hI
  have hb := ae_wedge_canonical_spec_of_profile hγ hγ2 hα hX hA hI hprof
  refine ae_unitArea_of_fieldLawFull_eq (Y' := WedgeMeas.wedgeRef γ X A) hlaw hm
    (WedgeMeas.aemeasurable_wedgeRefData hX hA
      (LogSingGood.wedgeRefGoodAS_holds hγ hγ2 hα Ω' _ P' X A hP' hX hA hI) H) ?_
  filter_upwards [hb] with ω hω
  exact ⟨hω.2.1, hω.2.2⟩

end WedgeCan4

end QuantumZipper
