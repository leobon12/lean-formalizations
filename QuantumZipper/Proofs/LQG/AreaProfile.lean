import QuantumZipper.Proofs.LQG.AreaCircles
import QuantumZipper.Proofs.LQG.InfiniteMass
import QuantumZipper.Proofs.LQG.GoodTransforms
import QuantumZipper.Proofs.LQG.FiniteArea
import QuantumZipper.Proofs.LQG.PositivityArea

/-!
# M4-A4, part 2: the area profile `a ↦ μ(B(0,a) ∩ ℍ)`

Blueprint `M4_BLUEPRINT.md`, node M4-A4. For the free field `X` and `γ ∈ (0,2)`, almost surely
the profile `a ↦ μ_X(B(0,a) ∩ ℍ)` is finite (M4-A3, `FinArea.ae_qAreaMeasure_ball_lt_top`),
continuous (no mass on circles, `AreaCircles.ae_sphere_null`), strictly increasing on `[0,∞)`
(positivity, `PositivityArea.ae_forall_pos_qAreaMeasure`), tends to `0` at `0⁺` and to `∞` at
`∞` (`ae_qAreaMeasure_H_eq_top`).

* `ae_qAreaMeasure_H_eq_top`: a.s. `μ_X(ℍ) = ∞`. The blueprint's "P6 trick applied to area",
  i.e. the argument of `InfMass.ae_qBoundaryMeasure_cone_eq_top` with the cone `(0,∞)` replaced
  by the (scale-invariant) half-plane `ℍ`: `M = e^{−γ X(fc(0,1))} μ_X(ℍ)` is a measurable function
  of the normalized coordinates, whose law is invariant under the dyadic rescalings
  (`InfMass.map_normC_rescale`), while `μ_{rescale x Q 2ⁿ} = (·/2ⁿ)_* μ_x`
  (`GoodTransforms.qAreaMeasure_rescale`) gives `M'_n = e^{Y_n} M` with
  `Y_n = γ(X(fc(0,1)) − X(fc(0,2ⁿ)) − Q n log 2) → −∞` in probability
  (`InfMass.tendsto_prob_Y`, at level `L/2`); `InfMass.ae_zero_or_top_of_scaling` and
  positivity conclude. This is the scaling argument of Duplantier–Sheffield, *Liouville quantum
  gravity and KPZ* (arXiv:0808.1560), in the form used for the boundary in `InfiniteMass.lean`.
* `ae_hasAreaProfile`: the five properties above, a.s., under the hypothesis
  `AreaCircles.AreaLogSingNoAtom` (area M4-P4, used only for "no mass on circles").
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace QuantumZipper
namespace AreaProfile

open InfMass Factorization LQGMeas

/-! ## 1. The profile of a measure -/

/-- The profile `a ↦ μ(B(0,a) ∩ ℍ)`. -/
def profile (μ : Measure ℂ) (a : ℝ) : ℝ≥0∞ := μ (Metric.ball 0 a ∩ H)

theorem profile_mono (μ : Measure ℂ) : Monotone (profile μ) := fun _ _ h =>
  measure_mono (inter_subset_inter_left _ (Metric.ball_subset_ball h))

theorem profile_nonpos (μ : Measure ℂ) {a : ℝ} (ha : a ≤ 0) : profile μ a = 0 := by
  rw [profile, Metric.ball_eq_empty.2 ha, empty_inter, measure_empty]

theorem measurableSet_ball_inter_H (a : ℝ) : MeasurableSet (Metric.ball (0 : ℂ) a ∩ H) :=
  (Metric.isOpen_ball.inter isOpen_H).measurableSet

/-- Left continuity: `B(0,a) = ⋃_{b<a} B(0,b)`. -/
theorem profile_tendsto_left (μ : Measure ℂ) (a : ℝ) :
    Tendsto (profile μ) (𝓝[<] a) (𝓝 (profile μ a)) := by
  have e : profile μ a = sSup (profile μ '' Iio a) := by
    refine le_antisymm ?_ (sSup_le ?_)
    · have hU : Metric.ball (0 : ℂ) a ∩ H =
          ⋃ n : ℕ, Metric.ball (0 : ℂ) (a - 1 / ((n : ℝ) + 1)) ∩ H := by
        ext z
        simp only [mem_iUnion, mem_inter_iff, Metric.mem_ball, dist_zero_right]
        constructor
        · rintro ⟨h1, h2⟩
          obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 h1)
          exact ⟨n, by linarith, h2⟩
        · rintro ⟨n, h1, h2⟩
          have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
          exact ⟨by linarith, h2⟩
      have hmono : Monotone fun n : ℕ => Metric.ball (0 : ℂ) (a - 1 / ((n : ℝ) + 1)) ∩ H := by
        intro m n hmn
        refine inter_subset_inter_left _ (Metric.ball_subset_ball ?_)
        have : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := Nat.one_div_le_one_div hmn
        linarith
      rw [profile, hU, hmono.measure_iUnion]
      refine iSup_le fun n => le_sSup ⟨a - 1 / ((n : ℝ) + 1), ?_, rfl⟩
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      simp only [mem_Iio]; linarith
    · rintro _ ⟨b, hb, rfl⟩
      exact profile_mono μ (le_of_lt hb)
  rw [e]
  exact (profile_mono μ).tendsto_nhdsLT a

/-- Right continuity at `a`, when `μ` is finite on balls and does not charge `∂B(0,a) ∩ ℍ`. -/
theorem profile_tendsto_right (μ : Measure ℂ) (hfin : ∀ b, profile μ b ≠ ⊤) {a : ℝ}
    (hcirc : μ (Metric.sphere 0 a ∩ H) = 0) :
    Tendsto (profile μ) (𝓝[>] a) (𝓝 (profile μ a)) := by
  have e : profile μ a = sInf (profile μ '' Ioi a) := by
    refine le_antisymm (le_sInf ?_) ?_
    · rintro _ ⟨b, hb, rfl⟩
      exact profile_mono μ (le_of_lt hb)
    · have hanti : Antitone fun n : ℕ => Metric.ball (0 : ℂ) (a + 1 / ((n : ℝ) + 1)) ∩ H := by
        intro m n hmn
        refine inter_subset_inter_left _ (Metric.ball_subset_ball ?_)
        have : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) := Nat.one_div_le_one_div hmn
        linarith
      have hI := hanti.measure_iInter (μ := μ)
        (fun n => (measurableSet_ball_inter_H _).nullMeasurableSet) ⟨0, hfin _⟩
      have hsub : (⋂ n : ℕ, Metric.ball (0 : ℂ) (a + 1 / ((n : ℝ) + 1)) ∩ H) ⊆
          (Metric.ball (0 : ℂ) a ∩ H) ∪ (Metric.sphere 0 a ∩ H) := by
        intro z hz
        rw [mem_iInter] at hz
        have hzH : z ∈ H := (hz 0).2
        have hle : ‖z‖ ≤ a := by
          refine le_of_forall_pos_lt_add fun ε hε => ?_
          obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
          have := (hz n).1
          rw [Metric.mem_ball, dist_zero_right] at this
          linarith
        rcases hle.lt_or_eq with h | h
        · exact Or.inl ⟨by rw [Metric.mem_ball, dist_zero_right]; exact h, hzH⟩
        · exact Or.inr ⟨by rw [mem_sphere_zero_iff_norm]; exact h, hzH⟩
      calc sInf (profile μ '' Ioi a)
          ≤ ⨅ n : ℕ, profile μ (a + 1 / ((n : ℝ) + 1)) := by
            refine le_iInf fun n => sInf_le ⟨a + 1 / ((n : ℝ) + 1), ?_, rfl⟩
            have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
            simp only [mem_Ioi]; linarith
        _ = μ (⋂ n : ℕ, Metric.ball (0 : ℂ) (a + 1 / ((n : ℝ) + 1)) ∩ H) := hI.symm
        _ ≤ μ ((Metric.ball (0 : ℂ) a ∩ H) ∪ (Metric.sphere 0 a ∩ H)) := measure_mono hsub
        _ ≤ profile μ a + 0 := by
            rw [← hcirc]; exact measure_union_le _ _
        _ = profile μ a := add_zero _
  rw [e]
  exact (profile_mono μ).tendsto_nhdsGT a

theorem profile_continuousAt (μ : Measure ℂ) (hfin : ∀ b, profile μ b ≠ ⊤) {a : ℝ}
    (hcirc : μ (Metric.sphere 0 a ∩ H) = 0) : ContinuousAt (profile μ) a :=
  continuousAt_iff_continuous_left_right.2
    ⟨continuousWithinAt_Iio_iff_Iic.1 (profile_tendsto_left μ a),
      continuousWithinAt_Ioi_iff_Ici.1 (profile_tendsto_right μ hfin hcirc)⟩

theorem profile_tendsto_zero (μ : Measure ℂ) (hfin : ∀ b, profile μ b ≠ ⊤) :
    Tendsto (profile μ) (𝓝[>] 0) (𝓝 0) := by
  have hcirc : μ (Metric.sphere (0 : ℂ) 0 ∩ H) = 0 := by
    rw [Metric.sphere_zero]
    have : ({0} : Set ℂ) ∩ H = ∅ := by
      ext z
      simp only [mem_inter_iff, mem_singleton_iff, mem_empty_iff_false, iff_false, not_and]
      rintro rfl
      simp [H]
    rw [this, measure_empty]
  have h := profile_tendsto_right μ hfin hcirc
  rwa [profile_nonpos μ le_rfl] at h

theorem profile_tendsto_top (μ : Measure ℂ) (hH : μ H = ⊤) :
    Tendsto (profile μ) atTop (𝓝 ⊤) := by
  have e : (⨆ a, profile μ a) = ⊤ := by
    rw [← hH]
    refine le_antisymm (iSup_le fun a => measure_mono inter_subset_right) ?_
    have hU : H = ⋃ N : ℕ, Metric.ball (0 : ℂ) N ∩ H := by
      ext z
      simp only [mem_iUnion, mem_inter_iff, Metric.mem_ball, dist_zero_right]
      constructor
      · intro hz
        obtain ⟨N, hN⟩ := exists_nat_gt ‖z‖
        exact ⟨N, hN, hz⟩
      · rintro ⟨N, -, hz⟩; exact hz
    have hmono : Monotone fun N : ℕ => Metric.ball (0 : ℂ) N ∩ H := fun N N' h =>
      inter_subset_inter_left _ (Metric.ball_subset_ball (by exact_mod_cast h))
    conv_lhs => rw [hU]
    rw [hmono.measure_iUnion]
    exact iSup_le fun N => le_iSup (profile μ) (N : ℝ)
  rw [← e]
  exact tendsto_atTop_iSup (profile_mono μ)

theorem profile_strictMonoOn (μ : Measure ℂ) (hfin : ∀ b, profile μ b ≠ ⊤)
    (hpos : ∀ V : Set ℂ, IsOpen V → V ⊆ H → V.Nonempty → 0 < μ V) :
    StrictMonoOn (profile μ) (Ici 0) := by
  intro a ha b _ hab
  have ha0 : 0 ≤ a := ha
  set V := Metric.ball (0 : ℂ) b ∩ H ∩ (Metric.closedBall 0 a)ᶜ with hV
  have hVo : IsOpen V :=
    (Metric.isOpen_ball.inter isOpen_H).inter Metric.isClosed_closedBall.isOpen_compl
  have hVne : V.Nonempty := by
    refine ⟨(((a + b) / 2 : ℝ) : ℂ) * Complex.I, ?_⟩
    have hc : (0 : ℝ) ≤ (a + b) / 2 := by linarith
    have hn : ‖(((a + b) / 2 : ℝ) : ℂ) * Complex.I‖ = (a + b) / 2 := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_of_nonneg hc]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [Metric.mem_ball, dist_zero_right, hn]; linarith
    · show 0 < ((((a + b) / 2 : ℝ) : ℂ) * Complex.I).im
      rw [Complex.mul_I_im, Complex.ofReal_re]; linarith
    · rw [mem_compl_iff, Metric.mem_closedBall, dist_zero_right, hn, not_le]; linarith
  have hVpos := hpos V hVo (inter_subset_left.trans inter_subset_right) hVne
  have hdisj : Disjoint (Metric.ball (0 : ℂ) a ∩ H) V :=
    Set.disjoint_left.2 fun z hz hzV => hzV.2 (Metric.ball_subset_closedBall hz.1)
  have hle : profile μ a + μ V ≤ profile μ b := by
    rw [profile, ← measure_union hdisj hVo.measurableSet]
    refine measure_mono (union_subset ?_ fun z hz => hz.1)
    exact inter_subset_inter_left _ (Metric.ball_subset_ball hab.le)
  exact (ENNReal.lt_add_right (hfin a) hVpos.ne').trans_le hle

/-- **The area profile properties** (blueprint M4-A4) of a sample `x`. -/
def HasAreaProfile (γ : ℝ) (x : FieldSample) : Prop :=
  (∀ a, profile (qAreaMeasure γ x) a ≠ ⊤) ∧ Continuous (profile (qAreaMeasure γ x)) ∧
    StrictMonoOn (profile (qAreaMeasure γ x)) (Ici 0) ∧
    Tendsto (profile (qAreaMeasure γ x)) (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (profile (qAreaMeasure γ x)) atTop (𝓝 ⊤)

/-- Deterministic assembly of the profile properties. -/
theorem hasAreaProfile_of {γ : ℝ} {x : FieldSample}
    (hfin : ∀ a, qAreaMeasure γ x (Metric.ball 0 a ∩ H) < ⊤)
    (hcirc : ∀ a, qAreaMeasure γ x (Metric.sphere 0 a ∩ H) = 0)
    (hpos : ∀ V : Set ℂ, IsOpen V → V ⊆ H → V.Nonempty → 0 < qAreaMeasure γ x V)
    (hH : qAreaMeasure γ x H = ⊤) : HasAreaProfile γ x := by
  have hf : ∀ a, profile (qAreaMeasure γ x) a ≠ ⊤ := fun a => (hfin a).ne
  exact ⟨hf, continuous_iff_continuousAt.2 fun a => profile_continuousAt _ hf (hcirc a),
    profile_strictMonoOn _ hf hpos, profile_tendsto_zero _ hf, profile_tendsto_top _ hH⟩

/-! ## 2. Infinite total area -/

/-- The measurable functional `μ(ℍ)`, computed from `areaFun` against cut-offs of the bounded
open pieces `B(0,N) ∩ ℍ`. -/
def PsiA (γ : ℝ) (y : FieldSample) : ℝ≥0∞ :=
  ⨆ N : ℕ, ⨆ m : ℕ, ENNReal.ofReal (areaFun γ (openBump (Metric.ball (0 : ℂ) N ∩ H) m) y)

theorem measurable_PsiA (γ : ℝ) : Measurable (PsiA γ) :=
  Measurable.iSup fun _ => Measurable.iSup fun _ => ENNReal.measurable_ofReal.comp
    (measurable_areaFun γ (continuous_openBump _ _).measurable)

theorem PsiA_congr {γ : ℝ} {x x' : FieldSample} (h : avgReg x = avgReg x') :
    PsiA γ x = PsiA γ x' := by
  unfold PsiA areaFun; rw [areaApprox_congr h]

theorem PsiA_eq {γ : ℝ} {y : FieldSample} (hy : IsLQGGood γ y) :
    PsiA γ y = qAreaMeasure γ y H := by
  have hN : ∀ N : ℕ, qAreaMeasure γ y (Metric.ball 0 N ∩ H) =
      ⨆ m : ℕ, ENNReal.ofReal (areaFun γ (openBump (Metric.ball (0 : ℂ) N ∩ H) m) y) := by
    intro N
    set U := Metric.ball (0 : ℂ) N ∩ H with hUdef
    have hU : IsOpen U := Metric.isOpen_ball.inter isOpen_H
    have hUb : Bornology.IsBounded U := Metric.isBounded_ball.subset inter_subset_left
    have hUH : U ⊆ H := inter_subset_right
    have hUc : Uᶜ.Nonempty := ⟨0, fun h => by simpa [H] using hUH h⟩
    rw [measure_open_eq_iSup _ hU hUc]
    congr 1
    funext m
    have hsupp := (tsupport_openBump_subset U m).trans hUH
    rw [areaFun_eq hy (continuous_openBump U m) (hasCompactSupport_openBump hUb m) hsupp,
      ofReal_integral_eq_lintegral_ofReal _ (ae_of_all _ fun z => openBump_nonneg U m z)]
    exact GoodSample.integrable_of_tsupport hy.qAreaMeasure_spec.2.1 (continuous_openBump U m)
      (hasCompactSupport_openBump hUb m) hsupp
  have hU : H = ⋃ N : ℕ, Metric.ball (0 : ℂ) N ∩ H := by
    ext z
    simp only [mem_iUnion, mem_inter_iff, Metric.mem_ball, dist_zero_right]
    constructor
    · intro hz
      obtain ⟨N, hN⟩ := exists_nat_gt ‖z‖
      exact ⟨N, hN, hz⟩
    · rintro ⟨N, -, hz⟩; exact hz
  have hmono : Monotone fun N : ℕ => Metric.ball (0 : ℂ) N ∩ H := fun N N' h =>
    inter_subset_inter_left _ (Metric.ball_subset_ball (by exact_mod_cast h))
  unfold PsiA
  simp_rw [← hN]
  conv_rhs => rw [hU]
  rw [hmono.measure_iUnion]

theorem PsiA_normC {γ : ℝ} {y : FieldSample} (hy : IsLQGGood γ y) :
    PsiA γ (reconstruct (normC y)) =
      ENNReal.ofReal (Real.exp (γ * -(y fc01))) * qAreaMeasure γ y H := by
  rw [normC_eq, PsiA_congr (avgReg_reconstruct_add y _), PsiA_eq (hy.addConst _),
    GoodSample.qAreaMeasure_addConst hy, Measure.smul_apply, smul_eq_mul]

theorem qAreaMeasure_rescale_H {γ : ℝ} {y : FieldSample} (hy : IsLQGGood γ y) (hγ : 0 < γ)
    {b : ℝ} (hb : 0 < b) : qAreaMeasure γ (rescale y (Qc γ) b) H = qAreaMeasure γ y H := by
  rw [GoodTransforms.qAreaMeasure_rescale hy hγ hb,
    Measure.map_apply (show Measurable fun z : ℂ => z / (b : ℂ) from measurable_id.div_const _)
      isOpen_H.measurableSet]
  congr 1
  ext z
  show 0 < (z / (b : ℂ)).im ↔ 0 < z.im
  rw [Complex.div_ofReal_im]
  exact div_pos_iff_of_pos_right hb

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- **Infinite total area.** For the free field, a.s. `μ_X(ℍ) = ∞`. -/
theorem ae_qAreaMeasure_H_eq_top [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) : ∀ᵐ ω ∂P, qAreaMeasure γ (X ω) H = ⊤ := by
  obtain ⟨G, hG⟩ := WedgeTK.exists_isRegVersion hX
  have hXm : Measurable X := WedgeTK.measurable_X_pi hX
  set Φ : (ℕ → ℝ) → ℝ≥0∞ := fun c => PsiA γ (reconstruct c) with hΦ
  have hΦm : Measurable Φ := (measurable_PsiA γ).comp measurable_reconstruct
  have hNm : Measurable fun ω => normC (X ω) :=
    measurable_pi_iff.2 fun i => (hX.measurable_coord _).sub (hX.measurable_coord _)
  have hNm' : ∀ n : ℕ, Measurable fun ω => normC (rescale (X ω) (Qc γ) ((2 : ℝ) ^ n)) := by
    intro n
    have : IsProbabilityMeasure fc01 := by unfold fc01; infer_instance
    refine measurable_pi_iff.2 fun i => ?_
    have : IsProbabilityMeasure (fcI i) := by unfold fcI; infer_instance
    exact ((measurable_coordChange_apply (fun z : ℂ => (((2 : ℝ) ^ n : ℝ) : ℂ) * z) (Qc γ)
      (fcI i)).comp hXm).sub ((measurable_coordChange_apply
        (fun z : ℂ => (((2 : ℝ) ^ n : ℝ) : ℂ) * z) (Qc γ) fc01).comp hXm)
  set M : Ω → ℝ≥0∞ := fun ω => Φ (normC (X ω)) with hM
  set M' : ℕ → Ω → ℝ≥0∞ := fun n ω => Φ (normC (rescale (X ω) (Qc γ) ((2 : ℝ) ^ n))) with hM'
  set Y : ℕ → Ω → ℝ := fun n ω =>
    2 * (γ / 2 * (X ω fc01 - rescale (X ω) (Qc γ) ((2 : ℝ) ^ n) fc01)) with hY
  have hlaw : ∀ n, P.map (M' n) = P.map M := by
    intro n
    have e1 : M' n = Φ ∘ fun ω => normC (rescale (X ω) (Qc γ) ((2 : ℝ) ^ n)) := rfl
    have e2 : M = Φ ∘ fun ω => normC (X ω) := rfl
    rw [e1, e2, ← Measure.map_map hΦm (hNm' n), ← Measure.map_map hΦm hNm,
      map_normC_rescale hX hG (Qc γ) (by positivity)]
  have hgood := AreaOffsets.ae_isLQGGood hX (P := P) hγ hγ2
  have hformM : ∀ᵐ ω ∂P, M ω = ENNReal.ofReal (Real.exp (γ * -(X ω fc01))) *
      qAreaMeasure γ (X ω) H := by
    filter_upwards [hgood] with ω hω
    exact PsiA_normC hω
  have hrel : ∀ n, ∀ᵐ ω ∂P, M' n ω = ENNReal.ofReal (Real.exp (Y n ω)) * M ω := by
    intro n
    filter_upwards [hgood] with ω hω
    have hb : (0 : ℝ) < 2 ^ n := by positivity
    have hR := hω.rescale hγ hb
    show PsiA γ (reconstruct (normC (rescale (X ω) (Qc γ) ((2 : ℝ) ^ n)))) =
      ENNReal.ofReal (Real.exp (Y n ω)) * PsiA γ (reconstruct (normC (X ω)))
    rw [PsiA_normC hR, PsiA_normC hω, qAreaMeasure_rescale_H hω hγ hb, ← mul_assoc,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 3
    simp only [hY]
    ring
  have hYt : ∀ L : ℝ, Tendsto (fun n => P {ω | L ≤ Y n ω}) atTop (𝓝 0) := by
    intro L
    refine (tendsto_prob_Y hX hG hγ (L / 2)).congr fun n => ?_
    congr 1
    ext ω
    simp only [mem_setOf_eq, hY]
    constructor <;> intro h <;> linarith
  have hMm : Measurable M := hΦm.comp hNm
  have h01 := ae_zero_or_top_of_scaling hMm.aemeasurable
    (fun n => (hΦm.comp (hNm' n)).aemeasurable) hlaw hrel hYt
  filter_upwards [h01, hformM, PositivityArea.ae_forall_pos_qAreaMeasure hX hγ hγ2]
    with ω h01 hMω hpos
  have hp := hpos H isOpen_H subset_rfl ⟨Complex.I, by simp [H]⟩
  rw [hMω] at h01
  rcases h01 with h | h
  · exact absurd h (mul_ne_zero (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne' hp.ne')
  · rcases ENNReal.mul_eq_top.1 h with h' | h'
    · exact h'.2
    · exact absurd h'.1 ENNReal.ofReal_ne_top

/-! ## 3. The profile of the free field -/

end AreaProfile
end QuantumZipper
