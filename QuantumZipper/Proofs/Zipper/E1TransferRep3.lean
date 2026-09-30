import QuantumZipper.Proofs.Zipper.E1TransferRep2

/-!
# TR-MEAS: the representation of both integrands through `(lawData (N ·), (V^t, W⁰))`

`handoff/E1-TR.md` (TR-MEAS). With `Hf0 (l, d) := trInt … (stopDrive d) d (fromC l.1)`:

* `ae_regShift_logAdd_frostman`, `ae_regShift_h0X_push`: for a fixed continuous driver `v`, a.s. in
  the free field, `RegShift (𝔥₀ + X) (μ.map (revMap v t))` (RC1 with a logarithmic mean,
  `CoordReg.ae_tendsto_integral_avgReg_logAdd_frostman`, and the continuity of the circle
  averages of the free field, `FrostmanReg.ae_circleAvg_tendsto_frostman`);
* `ae_trInt_eq_Hf0_left`: a.s. `trInt … (V) (D) (Y_t) = Hf0 (lawData (N Y_t), D)`;
* `ae_trInt_eq_Hf0_right`: for a.e. `ω` and a.e. `ω'`,
  `trInt … (V ω) (D ω) (𝔥₀ + X ω') = Hf0 (lawData (N (𝔥₀ + X)) ω', D ω)`.

Sources: Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.1 and §3 (RC1); Sheffield
arXiv:1012.4797, Lemma 5.6 (pp. 66–68), §5.2 (pp. 57–59). The reduction is own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace CoordReg

open FrostmanReg SmoothConv

/-- Raw circle averages of `ofFun (a log‖·‖ + g₁) + x` converge where those of `x` do. -/
theorem exists_tendsto_raw_ofFun_logAdd (a : ℝ) {g₁ : ℂ → ℝ} (hg₁ : ContinuousOn g₁ Hbar)
    {x : FieldSample} {k : ℕ} {z : ℂ}
    (hx : ∃ l, Tendsto (fun n => x (foldedCircle (dyadicRoundC n z) (radius k))) atTop (𝓝 l)) :
    ∃ l, Tendsto (fun n => (ofFun (fun v => a * Real.log ‖v‖ + g₁ v) + x)
      (foldedCircle (dyadicRoundC n z) (radius k))) atTop (𝓝 l) := by
  obtain ⟨l, hl⟩ := hx
  have hr := radius_pos k
  have ha : Tendsto (fun n => a * Real.log (max (radius k) ‖dyadicRoundC n z‖) +
      GoodSample.smoothFun g₁ (dyadicRoundC n z) (radius k)) atTop
      (𝓝 (a * Real.log (max (radius k) ‖z‖) + GoodSample.smoothFun g₁ z (radius k))) :=
    ((((continuous_log_max_norm hr).tendsto z).comp (RegClosure.tendsto_dyadicRoundC z)).const_mul
      a).add (((GoodSample.continuous_smoothFun hg₁ _).tendsto z).comp
        (RegClosure.tendsto_dyadicRoundC z))
  refine ⟨_, (ha.add hl).congr fun n => ?_⟩
  show _ = ofFun _ _ + x _
  simp only [ofFun]
  rw [integral_logAdd_foldedCircle a hg₁ _ hr]

/-- **`RegShift` for a free field with a logarithmic mean**, at a Frostman measure. -/
theorem ae_regShift_logAdd_frostman {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → FieldSample} (hX : IsFreeGFFModConstH X P)
    {ν : Measure ℂ} [IsProbabilityMeasure ν] {R α C : ℝ}
    (hsupp : ν (Metric.closedBall 0 R ∩ Hbar)ᶜ = 0) (h : IsFrostman ν α C) (hα : 0 < α)
    (a : ℝ) {g₁ : ℂ → ℝ} (hg₁ : ContinuousOn g₁ Hbar) :
    ∀ᵐ ω ∂P, E1.RegShift (ofFun (fun v => a * Real.log ‖v‖ + g₁ v) + X ω) ν := by
  set K := Metric.closedBall (0 : ℂ) R ∩ Hbar
  have hK : IsCompact K := (isCompact_closedBall 0 R).inter_right isClosed_Hbar
  have hKH : K ⊆ Hbar := Set.inter_subset_right
  have hae : ∀ᵐ z ∂ν, z ∈ K := ae_mem_of_compl_null_frostman hsupp
  filter_upwards [ae_all_iff.2 fun k => ae_circleAvg_tendsto_frostman hX k,
    ae_tendsto_integral_avgReg_logAdd_frostman hX hsupp h hα a hg₁] with ω hc ht
  refine ⟨hae.mono fun z hz k => exists_tendsto_raw_ofFun_logAdd a hg₁ ⟨_, (hc k).2 z (hKH hz)⟩,
    fun k => ?_, _, ht⟩
  have i1 : Integrable (fun z => Real.log (max (radius k) ‖z‖)) ν :=
    integrable_of_continuousOn_frostman hK hKH hsupp
      (continuous_log_max_norm (radius_pos k)).continuousOn
  have i2 : Integrable (fun z => GoodSample.smoothFun g₁ z (radius k)) ν :=
    integrable_of_continuousOn_frostman hK hKH hsupp
      (GoodSample.continuous_smoothFun hg₁ _).continuousOn
  have i3 : Integrable (fun z => avgReg (X ω) k z) ν :=
    integrable_of_continuousOn_frostman hK hKH hsupp (hc k).1
  refine (((i1.const_mul a).add i2).add i3).congr (hae.mono fun z hz => ?_)
  exact (avgReg_ofFun_logAdd_of_tendsto a hg₁ ((hc k).2 z (hKH hz))).symm

end CoordReg

namespace E1

open B2 CharFun UnzipInvariance UnzipFull CoordsFull CoordReg B1Full

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {κ T t : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

/-- **`RegShift` for `𝔥₀ + X` at a pushed measure, fixed driver.** -/
theorem ae_regShift_h0X_push (hX : IsFreeGFFModConstH X P) {v : ℝ → ℝ} (hv : Continuous v)
    (ht : 0 ≤ t) {μ : Measure ℂ} [IsProbabilityMeasure μ] {R : ℝ}
    (hμR : ∀ᵐ z ∂μ, z ∈ H ∧ ‖z‖ ≤ R) {α C : ℝ} (hF : IsFrostman (μ.map (revMap v t)) α C)
    (hα : 0 < α) :
    ∀ᵐ ω ∂P, RegShift (ofFun (h0rev κ) + X ω) (μ.map (revMap v t)) := by
  have hFm := TwoPoint.measurable_revMap hv ht
  obtain ⟨Bf, hBf⟩ := norm_revMap_le' hv ht R
  have hsupp : (μ.map (revMap v t)) (Metric.closedBall 0 Bf ∩ Hbar)ᶜ = 0 := by
    have hae : ∀ᵐ z ∂μ, revMap v t z ∈ Metric.closedBall 0 Bf ∩ Hbar :=
      hμR.mono fun z hz => ⟨by rw [Metric.mem_closedBall, dist_zero_right]; exact hBf z hz.1 hz.2,
        (TwoPoint.im_revMap_pos hv hz.1 ht).le⟩
    rw [Measure.map_apply hFm
      (Metric.isClosed_closedBall.inter isClosed_Hbar).measurableSet.compl,
      show revMap v t ⁻¹' (Metric.closedBall 0 Bf ∩ Hbar)ᶜ =
        {z : ℂ | revMap v t z ∈ Metric.closedBall 0 Bf ∩ Hbar}ᶜ from rfl]
    exact mem_ae_iff.1 hae
  rw [h0rev_eq_logAdd κ]
  exact ae_regShift_logAdd_frostman hX hsupp hF hα _ continuousOn_const

theorem ae_regShift_h0X_fc (hX : IsFreeGFFModConstH X P) {v : ℝ → ℝ} (hv : Continuous v)
    (ht : 0 ≤ t) (i : ℕ) : ∀ᵐ ω ∂P, RegShift (ofFun (h0rev κ) + X ω) (pfc v t i) := by
  have hr := UnzipFull.fullIndex_radius_pos i
  set w := (fullIndex i).1
  have hμR : ∀ᵐ z ∂foldedCircle w (fullIndex i).2, z ∈ H ∧ ‖z‖ ≤ ‖w‖ + (fullIndex i).2 := by
    filter_upwards [TwoPoint.foldedCircle_ae_mem_H w hr,
      TwoPoint.foldedCircle_ae_norm_le w hr.le] with z h1 h2 using ⟨h1, h2⟩
  have hF := TwoPoint.isFrostman_revMap_foldedCircle hv ht hr le_rfl
    (le_refl (‖w‖ + (fullIndex i).2))
  exact ae_regShift_h0X_push hX hv ht hμR (fun p ρ hρ => hF p ρ hρ) (by norm_num)

theorem ae_regShift_h0X_compact (hX : IsFreeGFFModConstH X P) {v : ℝ → ℝ} (hv : Continuous v)
    (ht : 0 ≤ t) {ϖ : Measure ℂ} [IsProbabilityMeasure ϖ] {K : Set ℂ} (hK : IsCompact K)
    (hKH : K ⊆ H) (hϖ : ϖ Kᶜ = 0) {α C : ℝ} (hFϖ : IsFrostman ϖ α C) (hα : 0 < α) :
    ∀ᵐ ω ∂P, RegShift (ofFun (h0rev κ) + X ω) (varpiT v t ϖ) := by
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn continuous_norm.continuousOn
  have hμR : ∀ᵐ z ∂ϖ, z ∈ H ∧ ‖z‖ ≤ M := (ae_iff.2 hϖ).mono fun z hz =>
    ⟨hKH hz, by simpa using hM z hz⟩
  have hF2 : TwoPoint.IsFrostman ϖ α C := fun p ρ hρ => hFϖ p ρ hρ
  obtain ⟨C₁, hF⟩ := B2.isFrostman_map_revMap_of_compact hv ht hK hKH hϖ hα.le hF2
  exact ae_regShift_h0X_push hX hv ht hμR (fun p ρ hρ => hF p ρ hρ) hα

/-- The transfer integrand as a function of `(lawData, (V^t, W⁰))`: the field rebuilt from the
coordinates, the driver read off `V^t`. TR-MEAS asks for a measurable modification of it. -/
def Hf0 (κ t δ : ℝ) (ϖ : Measure ℂ) (Ψ : ℝ → (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) → ℝ≥0∞)
    (Φ : (ℕ → ℝ) → ℝ≥0∞) (p : ((ℕ → ℝ) × (TestFun H → ℝ)) × ((ℝ≥0 → ℝ) × (ℝ≥0 → ℝ))) : ℝ≥0∞ :=
  trInt κ t δ ϖ Ψ Φ (stopDrive p.2) p.2 (fromC p.1.1)

/-- **TR-MEAS, left representation** (without measurability). -/
theorem ae_trInt_eq_Hf0_left (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P)
    (hind : IndepFun (pathOf B) X P) (ht : 0 ≤ t) (htT : t ≤ T) {ϖ : Measure ℂ}
    (hϖ : IsNormalizer ϖ) (δ : ℝ) (Ψ : ℝ → (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) → ℝ≥0∞)
    (Φ : (ℕ → ℝ) → ℝ≥0∞) :
    ∀ᵐ ω ∂P, trInt κ t δ ϖ Ψ Φ (Vr κ T B ω) (Vstop κ T t B ω, W0p κ T B ω) (Yf κ T t B X ω) =
      Hf0 κ t δ ϖ Ψ Φ (lawData (fun ω => nrm (Yf κ T t B X ω)) ω,
        (Vstop κ T t B ω, W0p κ T B ω)) := by
  have := hϖ.prob
  obtain ⟨K, hK, hKH, hϖK⟩ := hϖ.cpt
  obtain ⟨α, C, hα, hF⟩ := hϖ.frost
  filter_upwards [hB.cont, ae_regShift_Yf_compact κ hB hX hind ht htT hK hKH hϖK hF hα,
    ae_all_iff.2 (ae_regShift_Yf_fc κ hB hX hind ht htT)] with ω hc h1 h2
  rw [trInt_eq_fromC_nrm δ Ψ Φ _ h1 h2, trInt_eq_stopDrive δ Ψ Φ ht hc]
  rfl

/-- **TR-MEAS, right representation** (without measurability). -/
theorem ae_trInt_eq_Hf0_right (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P)
    (ht : 0 ≤ t) {ϖ : Measure ℂ} (hϖ : IsNormalizer ϖ) (δ : ℝ)
    (Ψ : ℝ → (ℝ≥0 → ℝ) × (ℝ≥0 → ℝ) → ℝ≥0∞) (Φ : (ℕ → ℝ) → ℝ≥0∞) :
    ∀ᵐ ω ∂P, ∀ᵐ ω' ∂P, trInt κ t δ ϖ Ψ Φ (Vr κ T B ω) (Vstop κ T t B ω, W0p κ T B ω)
        (ofFun (h0rev κ) + X ω') =
      Hf0 κ t δ ϖ Ψ Φ (lawData (fun ω => nrm (ofFun (h0rev κ) + X ω)) ω',
        (Vstop κ T t B ω, W0p κ T B ω)) := by
  have := hϖ.prob
  obtain ⟨K, hK, hKH, hϖK⟩ := hϖ.cpt
  obtain ⟨α, C, hα, hF⟩ := hϖ.frost
  filter_upwards [hB.cont] with ω hc
  have hV : Continuous (Vr κ T B ω) := continuous_vrev (drive_continuous hc) T
  filter_upwards [ae_regShift_h0X_compact hX hV ht hK hKH hϖK hF hα,
    ae_all_iff.2 (ae_regShift_h0X_fc hX hV ht)] with ω' h1 h2
  rw [trInt_eq_fromC_nrm δ Ψ Φ _ h1 h2, trInt_eq_stopDrive δ Ψ Φ ht hc]
  rfl

end E1
end QuantumZipper
