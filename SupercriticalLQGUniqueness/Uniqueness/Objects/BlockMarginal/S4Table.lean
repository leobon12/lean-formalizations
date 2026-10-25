import SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal.S4Prob
import SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal.BlockInput




 












set_option autoImplicit false

noncomputable section

open Set MeasureTheory Metric Filter Real
open LQGMetric.Blueprint
open scoped ENNReal Topology

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal

open LQGMetric (DistC)

theorem exists_s4_table (pbar : Ioo (0 : ℝ) 1) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (Asp : ℝ) (hA : 0 < Asp) (hA1 : Asp ≤ 1) :
    ∃ n₀ : ℕ, ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC) (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D D' : DistC → LSCMetric),
      IsWeakLQGMetric ξ Q D → IsWeakLQGMetric ξ Q D' → IsNormalizedWholePlaneGFF h P →
      ∀ cMinus cPlus : ℝ≥0∞, 0 < cMinus → cMinus < ⊤ → 0 < cPlus → cPlus < ⊤ →
      (∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus) →
      (∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus) →
      ∀ (C : Objects.CorrectedEvent.Constants) (T : Objects.CorrectedEvent.TubeData), Objects.CorrectedEvent.DataMatch C T → ∀ (Ksh : ℕ) (Cmid0 : ℝ),
      C.A_sp = Asp → C.A_loc = 3 * 8 ^ Ksh → C.A_endpt ≤ 1 → 0 ≤ C.K_ann →
      C.lamConst ≤ 1 / 100 → C.lamConst * cPlus.toReal / cMinus.toReal < 1 →
      C.ρ ≤ C.lamConst / C.A_loc →
      n₀ ≤ ⌊C.lamConst * Asp / (16 * π * (C.A_loc * C.ρ))⌋₊ →
      ENNReal.ofReal p ≤ (P.map h) {g | Objects.Excursions.blockRaw C T Ksh Cmid0 D D' g} →
      (P.map h) {g | ¬ Objects.CorrectedEvent.S4 C T (fun z => Objects.Excursions.blockEvent C T Ksh Cmid0 D D' z g)} ≤
        ENNReal.ofReal ((1 - (pbar : ℝ)) / 10) := by
  obtain ⟨n₀, hn₀⟩ := exists_s4_bound pbar p hp hp1 Asp hA
  refine ⟨n₀, ?_⟩
  intro Ω _ P _ h ξ Q D D' hD hD' hGFF cMinus cPlus hm0 hmTop hp0 hpTop hMinus hPlus
    C T hData Ksh Cmid0 hCA hAloc hE hK0 hlam hSmall hρloc hcount hT51
  have hμ := Objects.ProbabilityS7S9.normalizedGFF_id_map' P h hGFF
  have : IsProbabilityMeasure (P.map h) :=
    (Measure.isProbabilityMeasure_map_iff hGFF.1.measurable.aemeasurable).2 inferInstance
  have hTr : T.r = C.r := hData.1
  have hTρ : T.rho = C.ρ := hData.2.1
  have hTK : T.K = ⌈C.lamConst / (C.A_loc * C.ρ)⌉₊ := hData.2.2.2.2.2.1
  have hr := C.rPos
  have hρp := C.rhoPos
  have hlamp := C.lamPos
  have hAlocp : 0 < C.A_loc := by rw [hAloc]; positivity
  set x : ℝ := C.lamConst / (C.A_loc * C.ρ) with hx
  have hx1 : 1 ≤ x := by
    rw [hx, le_div_iff₀ (by positivity), one_mul]
    rw [le_div_iff₀ hAlocp] at hρloc
    linarith
  have hKx : x ≤ T.K := by rw [hTK]; exact Nat.le_ceil x
  have hKx2 : (T.K : ℝ) ≤ 2 * x := by
    rw [hTK]
    have := Nat.ceil_lt_add_one (show 0 ≤ x by linarith)
    linarith
  have hKpos : (0 : ℝ) < T.K := by exact_mod_cast T.Kpos
  set R : ℝ := 3 * (3 * 8 ^ Ksh) * (T.rho * T.r) with hR
  have hRpos : 0 < R := by rw [hR, hTρ, hTr]; positivity
  have hRe : R = 3 * C.A_loc * (C.ρ * C.r) := by rw [hR, hAloc, hTρ, hTr]
  
  have hsep : 2 * (1 + 22 / 3) * R ≤ 8 * T.r / T.K := by
    rw [le_div_iff₀ hKpos, hRe, hTr]
    have h1 : (T.K : ℝ) * (C.A_loc * C.ρ) ≤ 2 * C.lamConst := by
      have := mul_le_mul_of_nonneg_right hKx2 (show (0:ℝ) ≤ C.A_loc * C.ρ by positivity)
      rw [hx, mul_assoc, div_mul_cancel₀ _ (by positivity)] at this
      exact this
    nlinarith
  
  have hcount' : n₀ ≤ blockCount T.K Asp := by
    refine hcount.trans (Nat.floor_le_floor ?_)
    have e : C.lamConst * Asp / (16 * π * (C.A_loc * C.ρ)) = x * Asp / (16 * π) := by
      rw [hx]; field_simp
    rw [e]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right hKx hA.le
  
  have hblock := aeEventIn_blockRaw_window P h ξ Q D D' hD hD' hGFF cMinus cPlus hm0 hmTop hp0 hpTop
    hMinus hPlus C T hData Ksh Cmid0 hE hK0 (by linarith) hSmall
  have hloc : ∀ k : Fin T.K, AEEventIn (P.map h) (fieldSigma0On (id : DistC → DistC)
      (ball (Objects.CorrectedEvent.site T k) R)) {g | Objects.Excursions.blockEvent C T Ksh Cmid0 D D' (Objects.CorrectedEvent.site T k) g} := by
    intro k
    have h1 := aeEventIn_normTranslate_sigma0 (P.map h) hμ (Objects.CorrectedEvent.site T k) _ hblock
    rwa [shiftSet_ball] at h1
  have hum : LQGMetric.UMeasurableSet {g : DistC | Objects.Excursions.blockRaw C T Ksh Cmid0 D D' g} :=
    Objects.BlockCoding.blockRaw_um C T Ksh Cmid0 D D' hD.1 hD'.1
      (Objects.Producer.blockRadius_bounds C T hData hE).1.le (by rw [hTρ, hTr]; positivity)
      (Objects.Producer.norm_orientation hData.2.2.2.2.2.2.1)
  have hnull0 : NullMeasurableSet {g : DistC | Objects.Excursions.blockRaw C T Ksh Cmid0 D D' g} (P.map h) :=
    hum (P.map h) inferInstance
  have hmarg : ∀ k : Fin T.K, ENNReal.ofReal p ≤
      (P.map h) {g | Objects.Excursions.blockEvent C T Ksh Cmid0 D D' (Objects.CorrectedEvent.site T k) g} := by
    intro k
    have hmp := measure_preserving_normTranslate (P.map h) hμ (Objects.CorrectedEvent.site T k)
    change ENNReal.ofReal p ≤ (P.map h) (Objects.Producer.normTranslate (Objects.CorrectedEvent.site T k) ⁻¹'
      {g | Objects.Excursions.blockRaw C T Ksh Cmid0 D D' g})
    rw [hmp.measure_preimage hnull0]
    exact hT51
  have hnull : ∀ k : Fin T.K,
      NullMeasurableSet {g | Objects.Excursions.blockEvent C T Ksh Cmid0 D D' (Objects.CorrectedEvent.site T k) g} (P.map h) := by
    intro k
    exact Objects.BlockCoding.blockEvent_um C T Ksh Cmid0 D D' hD.1 hD'.1
      (Objects.Producer.blockRadius_bounds C T hData hE).1.le (by rw [hTρ, hTr]; positivity)
      (Objects.Producer.norm_orientation hData.2.2.2.2.2.2.1) (Objects.CorrectedEvent.site T k) (P.map h) inferInstance
  exact hn₀ (P.map h) hμ.1 C T hCA hTr hA1 R hRpos hsep hcount'
    (fun z => {g | Objects.Excursions.blockEvent C T Ksh Cmid0 D D' z g}) hloc hmarg hnull

end SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal
