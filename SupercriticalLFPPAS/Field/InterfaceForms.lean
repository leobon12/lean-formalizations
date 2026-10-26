import SupercriticalLFPPAS.Core.Interfaces
import SupercriticalLFPPAS.Field.HeatLogScaleContinuity
import SupercriticalLFPPAS.Field.LocalizedApproximation
import SupercriticalLFPPAS.Implementation.Exists_jointHeatVersion
import SupercriticalLFPPAS.Implementation.JointHeatVersion
import LQGMetric.Meas.CR

/-!
# Interface forms of the field estimates

The field estimates from Lemma 2.1, packaged in the common interface forms.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped ENNReal
open LQGMetric (DistC heatMollify)
open LQGMetric.DFGPS (tailK tailW)
open SupercriticalLQGUniqueness (IsNormalizedWholePlaneGFF IsHeatSmoothing)
open SupercriticalLQGUniqueness.B2.Polylog

namespace SupercriticalLFPPAS.Field

private def circleRatioR {Ω : Type*} (H : ℝ → ℂ → Ω → ℝ)
    (s : ℝ) (z : ℂ) (ω : Ω) : ℝ :=
  |H s z ω| * (1 + |Real.log s|)⁻¹

private abbrev circleBlockIndex (R : ℝ) (n : ℕ) :=
  {p : ℝ × ℂ // p.1 ∈ Set.Icc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1) ∧
    p.2 ∈ closedBall (0 : ℂ) R}

private def circleBlockValue {Ω : Type*} (H : ℝ → ℂ → Ω → ℝ) (R : ℝ)
    (n : ℕ) (p : circleBlockIndex R n) (ω : Ω) : ℝ≥0∞ :=
  ENNReal.ofReal (circleRatioR H p.1.1 p.1.2 ω)

private def circleBlockSup {Ω : Type*} (H : ℝ → ℂ → Ω → ℝ) (R : ℝ)
    (n : ℕ) (ω : Ω) : ℝ≥0∞ :=
  ⨆ p : circleBlockIndex R n, circleBlockValue H R n p ω

private def circleGlobalSup {Ω : Type*} (H : ℝ → ℂ → Ω → ℝ) (R : ℝ)
    (ω : Ω) : ℝ≥0∞ :=
  ⨆ n : ℕ, circleBlockSup H R n ω

/-- The circle-average supremum on a compact spatial region is a.e.-measurable. Positive
scales are covered by countably many compact scale blocks. -/
private theorem aemeasurable_circleGlobalSup {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistC} (hh : LQGMetric.IsWholePlaneGFF h P)
    {H : ℝ → ℂ → Ω → ℝ} (hH : LQGMetric.DFGPS.IsCircleAvgVersion h P H) (R : ℝ) :
    AEMeasurable (circleGlobalSup H R) P := by
  have hBlock : ∀ n : ℕ, AEMeasurable (circleBlockSup H R n) P := by
    intro n
    have hscale : ∀ p : circleBlockIndex R n, 0 < p.1.1 := by
      intro p
      exact lt_of_lt_of_le (by positivity) p.2.1.1
    have hcont : ∀ ω, Continuous fun p : circleBlockIndex R n =>
        circleBlockValue H R n p ω := by
      intro ω
      have hmap : Continuous fun p : circleBlockIndex R n => p.1 := continuous_subtype_val
      have hmapOn : ContinuousOn (fun p : circleBlockIndex R n => p.1)
          (Set.univ : Set (circleBlockIndex R n)) :=
        continuousOn_univ.mpr hmap
      have hHc : Continuous fun p : circleBlockIndex R n => H p.1.1 p.1.2 ω := by
        have hc := (hH.cont ω).comp hmapOn (fun p _ => ⟨hscale p, mem_univ _⟩)
        exact continuousOn_univ.mp hc
      have hcoord : Continuous fun p : circleBlockIndex R n => p.1.1 :=
        continuous_fst.comp continuous_subtype_val
      have hlog : Continuous fun p : circleBlockIndex R n => Real.log p.1.1 := by
        exact continuousOn_univ.mp <| Real.continuousOn_log.comp hcoord.continuousOn
          (fun p _ => by simpa using ne_of_gt (hscale p))
      have hden : Continuous fun p : circleBlockIndex R n => 1 + |Real.log p.1.1| :=
        continuous_const.add hlog.abs
      have hdenPos : ∀ p : circleBlockIndex R n, 1 + |Real.log p.1.1| ≠ 0 := by
        intro p
        positivity
      have hr : Continuous fun p : circleBlockIndex R n => circleRatioR H p.1.1 p.1.2 ω := by
        convert hHc.abs.mul (hden.inv₀ hdenPos) using 1 <;> rfl
      exact ENNReal.continuous_ofReal.comp hr
    have hmeas : ∀ p : circleBlockIndex R n, AEMeasurable (fun ω =>
        circleBlockValue H R n p ω) P := by
      intro p
      have hbase : Measurable (fun ω => LQGMetric.circleAvg (h ω) p.1.1 p.1.2) :=
        (LQGMetric.measurable_circleAvg_left p.1.1 p.1.2).comp hh.measurable
      have hm : Measurable (fun ω => ENNReal.ofReal
          (|LQGMetric.circleAvg (h ω) p.1.1 p.1.2| *
            (1 + |Real.log p.1.1|)⁻¹)) :=
        ENNReal.measurable_ofReal.comp (hbase.abs.mul_const _)
      have heq : (fun ω => circleBlockValue H R n p ω) =ᵐ[P]
          fun ω => ENNReal.ofReal
            (|LQGMetric.circleAvg (h ω) p.1.1 p.1.2| *
              (1 + |Real.log p.1.1|)⁻¹) := by
        filter_upwards [hH.ae_eq p.1.1 (hscale p) p.1.2] with ω hω
        change ENNReal.ofReal
          (|H p.1.1 p.1.2 ω| * (1 + |Real.log p.1.1|)⁻¹) = _
        rw [hω]
      exact AEMeasurable.congr hm.aemeasurable heq.symm
    obtain ⟨D, hDc, hDd⟩ :=
      TopologicalSpace.exists_countable_dense (Set.univ : Set (circleBlockIndex R n))
    letI : Countable D := hDc.to_subtype
    have hEq : circleBlockSup H R n = fun ω => ⨆ p : D,
        circleBlockValue H R n p.1 ω := by
      funext ω
      change (⨆ p : circleBlockIndex R n, circleBlockValue H R n p ω) = _
      simpa only [Set.mem_univ, iSup_true, iSup_subtype'] using
        (LQGMetric.biSup_eq_of_dense (hcont ω) (S := Set.univ) hDd)
    rw [hEq]
    exact AEMeasurable.iSup fun p => hmeas p.1.1
  exact AEMeasurable.iSup hBlock

/-- On the circle-average growth event, the measurable supremum over compact scale blocks
dominates the normalized circle averages at every positive scale. -/
private theorem ae_circleBound_by_circleGlobalSup {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistC} {H : ℝ → ℂ → Ω → ℝ} (R : ℝ)
    (hBound : ∀ᵐ ω ∂P, ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 0 < s →
      ∀ z ∈ closedBall (0 : ℂ) R, |H s z ω| ≤ C * (1 + |Real.log s|)) :
    ∀ᵐ ω ∂P, ∀ s : ℝ, 0 < s → ∀ z ∈ closedBall (0 : ℂ) R,
      |H s z ω| ≤ (circleGlobalSup H R ω).toReal * (1 + |Real.log s|) := by
  filter_upwards [hBound] with ω hω
  obtain ⟨C, hC, hCbound⟩ := hω
  have hblock : ∀ n : ℕ, circleBlockSup H R n ω ≤ ENNReal.ofReal C := by
    intro n
    apply iSup_le
    intro p
    have hs : 0 < p.1.1 := by
      exact lt_of_lt_of_le (by positivity) p.2.1.1
    have hden : 0 < 1 + |Real.log p.1.1| := by positivity
    have hratio : circleRatioR H p.1.1 p.1.2 ω ≤ C := by
      calc circleRatioR H p.1.1 p.1.2 ω
          = |H p.1.1 p.1.2 ω| * (1 + |Real.log p.1.1|)⁻¹ := rfl
        _ ≤ (C * (1 + |Real.log p.1.1|)) * (1 + |Real.log p.1.1|)⁻¹ :=
          mul_le_mul_of_nonneg_right (hCbound p.1.1 hs p.1.2 p.2.2)
            (inv_nonneg.mpr hden.le)
        _ = C := by field_simp [ne_of_gt hden]
    exact ENNReal.ofReal_le_ofReal hratio
  have hglobal : circleGlobalSup H R ω ≤ ENNReal.ofReal C := by
    unfold circleGlobalSup
    exact iSup_le hblock
  have hfinite : circleGlobalSup H R ω ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hglobal
  intro s hs z hz
  let n : ℕ := Nat.ceil (max s s⁻¹)
  have hncast : max s s⁻¹ ≤ (n : ℝ) := by
    exact Nat.le_ceil _
  have hupper : s ≤ (n : ℝ) + 1 := by
    exact (le_max_left _ _).trans (hncast.trans (by linarith))
  have hrecip : s⁻¹ ≤ (n : ℝ) + 1 := by
    exact (le_max_right _ _).trans (hncast.trans (by linarith))
  have hlower : 1 / ((n : ℝ) + 1) ≤ s := by
    apply (div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)).2
    have hmul := mul_le_mul_of_nonneg_left hrecip hs.le
    simpa [mul_comm, hs.ne'] using hmul
  let p : circleBlockIndex R n := ⟨(s, z), ⟨⟨hlower, hupper⟩, hz⟩⟩
  have hratioENN : ENNReal.ofReal (circleRatioR H s z ω) ≤ circleGlobalSup H R ω := by
    calc ENNReal.ofReal (circleRatioR H s z ω)
        = circleBlockValue H R n p ω := rfl
      _ ≤ circleBlockSup H R n ω := le_iSup_of_le p le_rfl
      _ ≤ circleGlobalSup H R ω := le_iSup_of_le n le_rfl
  have hratioNonneg : 0 ≤ circleRatioR H s z ω := by
    exact mul_nonneg (abs_nonneg _) (inv_nonneg.mpr (by positivity))
  have hratio : circleRatioR H s z ω ≤ (circleGlobalSup H R ω).toReal := by
    have h := ENNReal.toReal_mono hfinite hratioENN
    simpa [ENNReal.toReal_ofReal hratioNonneg] using h
  have hden : 0 < 1 + |Real.log s| := by positivity
  calc |H s z ω| = circleRatioR H s z ω * (1 + |Real.log s|) := by
        dsimp [circleRatioR]
        field_simp [ne_of_gt hden]
    _ ≤ (circleGlobalSup H R ω).toReal * (1 + |Real.log s|) :=
      mul_le_mul_of_nonneg_right hratio hden.le

private lemma abs_log_le_add_inv {s : ℝ} (hs : 0 < s) :
    |Real.log s| ≤ s + s⁻¹ := by
  by_cases h1 : 1 ≤ s
  · have hlog : 0 ≤ Real.log s := Real.log_nonneg h1
    have hle := Real.log_le_sub_one_of_pos hs
    rw [abs_of_nonneg hlog]
    have hrec : 0 ≤ s⁻¹ := inv_nonneg.mpr hs.le
    linarith
  · have hs1 : s ≤ 1 := le_of_not_ge h1
    have hlog : Real.log s ≤ 0 := Real.log_nonpos hs.le hs1
    have hle := Real.log_le_sub_one_of_pos (inv_pos.mpr hs)
    have hloginv : Real.log (s⁻¹) = -Real.log s := by
      rw [Real.log_inv]
    rw [hloginv] at hle
    rw [abs_of_nonpos hlog]
    nlinarith [hle]

/-- A measurable circle-average supremum gives the Gaussian error envelope needed for (2.3).
The rate proved here is `16 C_K tailK(1) exp(-(log δ⁻¹)^2/16)`. -/
private theorem ae_uniformLocalizedHeatField_error_circleGlobalSup {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P) (K : Set ℂ) (hK : IsCompact K)
    (R : ℝ) (hKR : K ⊆ closedBall (0 : ℂ) R) :
    ∃ H : ℝ → ℂ → Ω → ℝ, LQGMetric.DFGPS.IsCircleAvgVersion h P H ∧
      AEMeasurable (fun ω => circleGlobalSup H R ω) P ∧
      ∀ᵐ ω ∂P, ∀ δ : ℝ, ∀ hδ : δ ∈ Ioo (0 : ℝ) 1,
        16 ≤ Real.log δ⁻¹ → ∀ L : ℝ, Real.log δ⁻¹ ≤ L → ∀ z ∈ K,
          |uniformLocalizedHeatField δ L hδ (h ω) z - heatMollify δ (h ω) z| ≤
            (16 * (circleGlobalSup H R ω).toReal * tailK 1) *
              Real.exp (-(Real.log δ⁻¹) ^ 2 / 16) := by
  obtain ⟨H, hH, hPol⟩ := ae_plMollify_eq_polarInt_allExponent P h hh
  obtain ⟨H', hH', hBound⟩ := exists_circleAverage_log_bound P h hh
    (closedBall (0 : ℂ) R) (isCompact_closedBall _ _)
  have hEq := ae_circleAverageVersions_eq P h H H' hH hH'
  have hBoundH : ∀ᵐ ω ∂P, ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 0 < s →
      ∀ z ∈ closedBall (0 : ℂ) R, |H s z ω| ≤ C * (1 + |Real.log s|) := by
    filter_upwards [hBound, hEq] with ω hB hE
    obtain ⟨C, hC, hB⟩ := hB
    refine ⟨C, hC, fun s hs z hz => ?_⟩
    rw [hE s hs z]
    exact hB s hs z hz
  have hCmeas := aemeasurable_circleGlobalSup hh.1 hH R
  have hCircle := ae_circleBound_by_circleGlobalSup (h := h) R hBoundH
  have hHeat := ae_heatMollify_eq_polarInt_forVersion P h hh H hH
  have hKtail : 0 ≤ tailK 1 := by
    unfold tailK
    apply setIntegral_nonneg measurableSet_Ioi
    intro r hr
    have hr0 : 0 ≤ r := le_of_lt hr
    simp [tailW]
    positivity
  refine ⟨H, hH, hCmeas, ?_⟩
  filter_upwards [hPol, hHeat, hCircle] with ω hPolω hHeatω hCω
  let C : ℝ := (circleGlobalSup H R ω).toReal
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  have hA : 0 ≤ (1 : ℝ) := by norm_num
  intro δ hδ hℓ L hL z hz
  let ℓ : ℝ := Real.log δ⁻¹
  have hℓ' : 16 ≤ ℓ := hℓ
  have hℓ0 : 0 ≤ ℓ := by dsimp [ℓ]; linarith
  have hℓpos : 0 < ℓ := lt_of_lt_of_le (by norm_num) hℓ'
  have hL' : 0 < L := lt_of_lt_of_le hℓpos hL
  have hδInv : Real.exp ℓ = δ⁻¹ := by
    dsimp [ℓ]
    exact Real.exp_log (inv_pos.mpr hδ.1)
  have hExp16 : 17 ≤ Real.exp 16 := by
    have := Real.add_one_le_exp (16 : ℝ)
    linarith
  have hInv17 : 17 ≤ δ⁻¹ := by
    rw [← hδInv]
    exact hExp16.trans (Real.exp_le_exp.mpr hℓ')
  have hδhalf : δ ≤ 1 / 2 := by
    have hInv2 : 2 ≤ 1 / δ := by
      have hInv2' : 2 ≤ δ⁻¹ := by linarith
      simpa [one_div] using hInv2'
    have hmul : 2 * δ ≤ 1 := (le_div_iff₀ hδ.1).1 hInv2
    linarith
  let q : ℝ := uniformLocalizationExponent δ L
  have hrad : plRad q δ = δ * L :=
    plRad_uniform_eq δ L (by dsimp [ℓ] at hℓ'; linarith) hL
  have hlog : 1 < Real.log δ⁻¹ := by dsimp [ℓ] at hℓ'; linarith
  have hLoc : plZ q δ hδ * uniformLocalizedHeatField δ L hδ (h ω) z =
      polarInt (plProf q) (fun r z => H r z ω) (δ, z) := by
    simpa [uniformLocalizedHeatField, q] using hPolω δ hδ hlog z q
  have hHeat' : heatMollify δ (h ω) z =
      polarInt (fun _ _ => 1) (fun r z => H r z ω) (δ, z) := hHeatω δ hδ.1 z
  have hF : ∀ r : ℝ, 0 < r → |H r z ω| ≤ C * (1 / r + r + 1) := by
    intro r hr
    have hBase := hCω r hr z (hKR hz)
    have hLog := abs_log_le_add_inv hr
    have hGrowth : 1 + |Real.log r| ≤ 1 / r + r + 1 := by
      have h := add_le_add_left hLog 1
      simpa [one_div, add_comm, add_left_comm, add_assoc] using h
    calc |H r z ω| ≤ C * (1 + |Real.log r|) := hBase
      _ ≤ C * (1 / r + r + 1) := mul_le_mul_of_nonneg_left hGrowth hC
  have hprof : ∀ r : ℝ, |plProf q δ r| ≤ 1 := fun r => abs_plProf_le q δ r
  have htail : ∀ r : ℝ, |1 - plProf q δ r| ≤ 1 := by
    intro r
    have hp := plProf_mem_Icc q δ r
    rw [abs_le]
    constructor <;> linarith [hp.1, hp.2]
  let w : ℝ → ℝ → ℝ := fun _ r => 1 - plProf q δ r
  have hzero : ∀ r : ℝ, 0 < r → r ≤ δ * L / 2 → w δ r = 0 := by
    intro r hr hra
    have hn : ‖(r : ℂ)‖ = r := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    have hrad' : r ≤ plRad q δ / 2 := by rw [hrad]; linarith
    have hp : plProf q δ r = 1 := by
      rw [plProf_eq q δ hδ]
      exact plBump_eq_one q δ hδ (by rw [hn]; exact hrad')
    simp [w, hp]
  have hTailExp : Real.exp (-((δ * L / 2) ^ 2) / (2 * δ ^ 2)) =
      Real.exp (-L ^ 2 / 8) := by
    congr 1
    field_simp [ne_of_gt hδ.1]
    ring
  have ha : 0 < δ * L / 2 := by exact div_pos (mul_pos hδ.1 hL') (by norm_num)
  have hTail₀ := abs_polarInt_gauss_tail_le hδ.1 hδhalf ha hA hC hF htail hzero
  have hTailRaw : |polarInt w (fun r z => H r z ω) (δ, z)| ≤
      4 * Real.exp (-((δ * L / 2) ^ 2) / (2 * δ ^ 2)) *
        (C * (2 / (2 * δ) * tailK 1)) := by
    simpa [polarInt, w] using hTail₀
  have hTail : |polarInt w (fun r z => H r z ω) (δ, z)| ≤
      4 * Real.exp (-L ^ 2 / 8) * (C * (1 / δ * tailK 1)) := by
    calc |polarInt w (fun r z => H r z ω) (δ, z)|
        ≤ 4 * Real.exp (-((δ * L / 2) ^ 2) / (2 * δ ^ 2)) *
            (C * (2 / (2 * δ) * tailK 1)) := hTailRaw
      _ = 4 * Real.exp (-L ^ 2 / 8) * (C * (1 / δ * tailK 1)) := by
        rw [hTailExp]
        congr 2 <;> ring
  have hI : |polarInt (fun _ _ => 1) (fun r z => H r z ω) (δ, z)| ≤
      C * (2 / δ * tailK 1) := by
    have hI₀ := abs_polarInt_gauss_le (ε := δ) (A := 1) (C := C)
      hδ.1 hδ.2.le hA hC hF (F := fun r => H r z ω) (w := fun _ => 1)
      (fun _ => by norm_num)
    simpa [polarInt] using hI₀
  have hZtail₀ := one_sub_plZ_le q δ hδ
  have hradDiv : plRad q δ ^ 2 / (8 * δ ^ 2) = L ^ 2 / 8 := by
    rw [hrad]
    field_simp [ne_of_gt hδ.1]
  have hZtail : 1 - plZ q δ hδ ≤ 2 * Real.exp (-L ^ 2 / 8) := by
    rw [hradDiv] at hZtail₀
    convert hZtail₀ using 1 <;> congr 1 <;> ring
  have hExpTail : Real.exp (-L ^ 2 / 8) ≤ Real.exp (-8) := by
    apply Real.exp_le_exp.mpr
    have hL16 : 16 ≤ L := hℓ'.trans hL
    nlinarith [sq_nonneg (L - 16)]
  have hExpNeg : Real.exp (-8) ≤ 1 / 9 := by
    rw [Real.exp_neg, inv_eq_one_div]
    apply (div_le_iff₀ (Real.exp_pos (8 : ℝ))).2
    have := Real.add_one_le_exp (8 : ℝ)
    nlinarith
  have hZlow : 1 / 2 ≤ plZ q δ hδ := by
    have hmass := hZtail.trans (mul_le_mul_of_nonneg_left
      (hExpTail.trans hExpNeg) (by norm_num : (0 : ℝ) ≤ 2))
    linarith
  have hZpos : 0 < plZ q δ hδ := plZ_pos q δ hδ
  have hZinv : (plZ q δ hδ)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div, div_le_iff₀ hZpos]
    linarith
  have hZnonneg : 0 ≤ 1 - plZ q δ hδ := by
    linarith [plZ_le_one q δ hδ]
  have hZabs : |1 - plZ q δ hδ| ≤ 2 * Real.exp (-L ^ 2 / 8) := by
    rw [abs_of_nonneg hZnonneg]
    exact hZtail
  have hcontF : ContinuousOn (fun r : ℝ => H r z ω) (Ioi (0 : ℝ)) :=
    (hH.cont ω).comp (continuous_id.prodMk continuous_const).continuousOn
      (fun r hr => ⟨hr, mem_univ _⟩)
  have hcontProf : ContinuousOn (fun r : ℝ => plProf q δ r) (Ioi (0 : ℝ)) := by
    have hc := (contDiff_plBump q δ hδ).continuous.comp Complex.continuous_ofReal
    have heq : (fun r : ℝ => plProf q δ r) = fun r : ℝ => plBump q δ hδ (r : ℂ) := by
      funext r
      exact plProf_eq q δ hδ r
    rw [heq]
    exact hc.continuousOn
  have hcontTail : ContinuousOn (fun r : ℝ => w δ r) (Ioi (0 : ℝ)) := by
    dsimp [w]
    exact continuousOn_const.sub hcontProf
  have hIntProf := integrableOn_polarIntegrand_gauss hδ.1 hA hC hF hcontF hprof hcontProf
  have hIntTail := integrableOn_polarIntegrand_gauss hδ.1 hA hC hF hcontF
      (fun r => htail r) hcontTail
  have hsum : polarInt (plProf q) (fun r z => H r z ω) (δ, z) +
      polarInt w (fun r z => H r z ω) (δ, z) =
      polarInt (fun _ _ => 1) (fun r z => H r z ω) (δ, z) := by
    simp only [polarInt]
    rw [← mul_add, ← integral_add hIntProf hIntTail]
    congr 1
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    change r * H r z ω * plProf q δ r * Real.exp (-r ^ 2 / δ ^ 2) +
      r * H r z ω * (1 - plProf q δ r) * Real.exp (-r ^ 2 / δ ^ 2) =
      r * H r z ω * 1 * Real.exp (-r ^ 2 / δ ^ 2)
    ring
  let Z : ℝ := plZ q δ hδ
  let N : ℝ := polarInt (plProf q) (fun r z => H r z ω) (δ, z)
  let T : ℝ := polarInt w (fun r z => H r z ω) (δ, z)
  let I : ℝ := polarInt (fun _ _ => 1) (fun r z => H r z ω) (δ, z)
  have hNI : N - I = -T := by change N + T = I at hsum; linarith
  have hLocEq : uniformLocalizedHeatField δ L hδ (h ω) z = Z⁻¹ * N := by
    have hLocMul : Z * uniformLocalizedHeatField δ L hδ (h ω) z = N := by
      simpa [Z, N] using hLoc
    calc uniformLocalizedHeatField δ L hδ (h ω) z =
          uniformLocalizedHeatField δ L hδ (h ω) z * (Z * Z⁻¹) := by
            rw [mul_inv_cancel₀ hZpos.ne']
            ring
      _ = Z⁻¹ * (Z * uniformLocalizedHeatField δ L hδ (h ω) z) := by ring
      _ = Z⁻¹ * N := by rw [hLocMul]
  have hErrorDecomp : uniformLocalizedHeatField δ L hδ (h ω) z -
      heatMollify δ (h ω) z = Z⁻¹ * (-T + (1 - Z) * I) := by
    rw [hLocEq, hHeat']
    change Z⁻¹ * N - I = Z⁻¹ * (-T + (1 - Z) * I)
    have hZZ : Z⁻¹ * Z = 1 := inv_mul_cancel₀ hZpos.ne'
    calc Z⁻¹ * N - I = Z⁻¹ * (N - Z * I) := by
          rw [mul_sub, ← mul_assoc, hZZ]
          ring
      _ = Z⁻¹ * (N - I + (1 - Z) * I) := by congr 1 <;> ring
      _ = Z⁻¹ * (-T + (1 - Z) * I) := by rw [hNI]
  have hErrAbs : |uniformLocalizedHeatField δ L hδ (h ω) z -
      heatMollify δ (h ω) z| ≤ 2 * (|T| + |1 - Z| * |I|) := by
    rw [hErrorDecomp, abs_mul, abs_of_nonneg (inv_nonneg.mpr hZpos.le)]
    calc Z⁻¹ * |-T + (1 - Z) * I|
        ≤ 2 * (|-T| + |(1 - Z) * I|) :=
          mul_le_mul hZinv (abs_add_le _ _) (abs_nonneg _) (by norm_num)
      _ = 2 * (|T| + |1 - Z| * |I|) := by rw [abs_neg, abs_mul]
  have hB : 0 ≤ C * (2 / δ * tailK 1) :=
    mul_nonneg hC (mul_nonneg (div_nonneg (by norm_num) hδ.1.le) hKtail)
  have hTbound : |T| ≤ 2 * Real.exp (-L ^ 2 / 8) * (C * (2 / δ * tailK 1)) := by
    dsimp [T] at hTail ⊢
    have heq : 4 * Real.exp (-L ^ 2 / 8) * (C * (1 / δ * tailK 1)) =
        2 * Real.exp (-L ^ 2 / 8) * (C * (2 / δ * tailK 1)) := by ring
    rw [heq] at hTail
    exact hTail
  have hIbound : |I| ≤ C * (2 / δ * tailK 1) := by simpa [I] using hI
  have hErrBound : |uniformLocalizedHeatField δ L hδ (h ω) z -
      heatMollify δ (h ω) z| ≤
      8 * Real.exp (-L ^ 2 / 8) * (C * (2 / δ * tailK 1)) := by
    calc |uniformLocalizedHeatField δ L hδ (h ω) z -
          heatMollify δ (h ω) z|
        ≤ 2 * (|T| + |1 - Z| * |I|) := hErrAbs
      _ ≤ 2 * (2 * Real.exp (-L ^ 2 / 8) * (C * (2 / δ * tailK 1)) +
            (2 * Real.exp (-L ^ 2 / 8)) * (C * (2 / δ * tailK 1))) := by
          gcongr
      _ = 8 * Real.exp (-L ^ 2 / 8) * (C * (2 / δ * tailK 1)) := by ring
  have hδinvEq : 1 / δ = Real.exp ℓ := by
    simpa [one_div] using hδInv.symm
  have hErrBound' : |uniformLocalizedHeatField δ L hδ (h ω) z -
      heatMollify δ (h ω) z| ≤
      16 * C * tailK 1 * Real.exp (ℓ - L ^ 2 / 8) := by
    have hErrBound₁ := hErrBound
    rw [show 2 / δ = 2 * (1 / δ) by ring, hδinvEq] at hErrBound₁
    have hEq' : 8 * Real.exp (-L ^ 2 / 8) * (C * (2 * Real.exp ℓ * tailK 1)) =
        16 * C * tailK 1 * Real.exp (ℓ - L ^ 2 / 8) := by
      calc 8 * Real.exp (-L ^ 2 / 8) * (C * (2 * Real.exp ℓ * tailK 1))
          = 16 * C * tailK 1 * (Real.exp ℓ * Real.exp (-L ^ 2 / 8)) := by ring
        _ = 16 * C * tailK 1 * Real.exp (ℓ - L ^ 2 / 8) := by
          rw [← Real.exp_add]
          congr 1
          ring
    rw [hEq'] at hErrBound₁
    exact hErrBound₁
  have hLsq : ℓ ^ 2 ≤ L ^ 2 := (sq_le_sq₀ hℓ0 hL'.le).2 (by simpa [ℓ] using hL)
  have hExpArg : ℓ - L ^ 2 / 8 ≤ -(ℓ ^ 2) / 16 := by
    calc ℓ - L ^ 2 / 8 ≤ ℓ - ℓ ^ 2 / 8 := by nlinarith only [hLsq]
      _ ≤ -(ℓ ^ 2) / 16 := by
        have hm : 0 ≤ (ℓ - 16) * ℓ := mul_nonneg (by linarith [hℓ']) hℓ0
        nlinarith only [hm]
  have hExpCmp : Real.exp (ℓ - L ^ 2 / 8) ≤ Real.exp (-(ℓ ^ 2) / 16) :=
    Real.exp_le_exp.mpr hExpArg
  have hFactor : 0 ≤ 16 * C * tailK 1 := by positivity
  calc |uniformLocalizedHeatField δ L hδ (h ω) z - heatMollify δ (h ω) z|
      ≤ 16 * C * tailK 1 * Real.exp (ℓ - L ^ 2 / 8) := hErrBound'
    _ ≤ 16 * C * tailK 1 * Real.exp (-(ℓ ^ 2) / 16) :=
      mul_le_mul_of_nonneg_left hExpCmp hFactor

/-- A jointly continuous heat version agrees with the pointwise heat mollification at all
scales and points on one probability-one event. -/
theorem ae_jointHeatVersion_eq_heatMollify {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    (X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ ε, IsHeatSmoothing P h ε (X ε))
    (hXc : ∀ᵐ ω ∂P, Continuous fun p : Set.Ioi (0 : ℝ) × ℂ => X p.1 ω p.2) :
    ∀ᵐ ω ∂P, ∀ ε : Set.Ioi (0 : ℝ), ∀ z : ℂ,
      X ε ω z = heatMollify (ε : ℝ) (h ω) z := by
  obtain ⟨Y, hYpath, hYc⟩ :=
    SupercriticalLFPPAS.Implementation.exists_jointHeatVersion_pathwise P h hh.1
  have hY : ∀ ε, IsHeatSmoothing P h ε (Y ε) := by
    intro ε z
    filter_upwards [hYpath] with ω hω
    exact hω ε z
  have hXY := SupercriticalLFPPAS.ae_eq_of_jointHeatVersions hX hY hXc hYc
  have hYM : ∀ᵐ ω ∂P, ∀ ε : Set.Ioi (0 : ℝ), ∀ z : ℂ,
      Y ε ω z = heatMollify (ε : ℝ) (h ω) z := by
    have hJ := LQGMetric.DFGPS.lem2_1HeatJoint P h hh.1
    filter_upwards [hYpath, hJ] with ω hω hωJ
    intro ε z
    obtain ⟨L, hL⟩ := hωJ.1 (ε : ℝ) ε.2 z
    have hlim : Tendsto
        (fun n : ℕ => h ω (SupercriticalLQGUniqueness.positiveHeatTrunc
          ⟨(ε : ℝ) ^ 2 / 2, Set.mem_Ioi.mpr
            (div_pos (pow_pos ε.2 2) two_pos)⟩ z n)) atTop (𝓝 L) := by
      unfold SupercriticalLQGUniqueness.positiveHeatTrunc
      exact hL
    have huniq := tendsto_nhds_unique (hω ε z) hlim
    have hLmoll : heatMollify (ε : ℝ) (h ω) z = L := hL.limUnder_eq
    exact huniq.trans hLmoll.symm
  filter_upwards [hXY, hYM] with ω hXYω hYMω
  intro ε z
  exact (congrArg (fun f : C(ℂ, ℝ) => f z) (hXYω ε)).trans (hYMω ε z)

/-- Interface form of (2.1), simultaneously for all compact sets. -/
theorem locApprox_holds : SupercriticalLFPPAS.Core.LocApproxStmt := by
  unfold SupercriticalLFPPAS.Core.LocApproxStmt
  intro Ω _ P _ h hh X hXV
  rcases hXV with ⟨hX, hXc⟩
  have hLoc : ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ η : ℝ, 0 < η →
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ hε : ε ∈ Ioo (0 : ℝ) 1,
        ∀ z ∈ closedBall (0 : ℂ) n,
          |heatMollify ε (h ω) z - localizedHeatField ε hε (h ω) z| ≤ η := by
    have hAll : ∀ n : ℕ, ∀ᵐ ω ∂P, ∀ η : ℝ, 0 < η →
        ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ hε : ε ∈ Ioo (0 : ℝ) 1,
          ∀ z ∈ closedBall (0 : ℂ) n,
            |heatMollify ε (h ω) z - localizedHeatField ε hε (h ω) z| ≤ η := by
      intro n
      exact ae_localizedHeat_tendsto_uniform_on_compact P h hh
        (closedBall (0 : ℂ) n) (isCompact_closedBall _ _)
    exact ae_all_iff.2 hAll
  have hVer := ae_jointHeatVersion_eq_heatMollify P h hh X hX hXc
  filter_upwards [hLoc, hVer] with ω hLocω hVerω
  intro K hK η hη
  obtain ⟨R, hR⟩ := hK.isBounded.subset_ball (0 : ℂ)
  obtain ⟨n, hn⟩ := exists_nat_ge R
  filter_upwards [hLocω n η hη] with ε hεevent
  intro hε z hz
  have hz' : z ∈ closedBall (0 : ℂ) n := by
    rw [mem_closedBall, dist_zero_right]
    have hzR := hR hz
    rw [mem_ball, dist_zero_right] at hzR
    exact le_trans hzR.le hn
  have h := hεevent hε z hz'
  simpa [localizedHeatField, hVerω ⟨ε, hε.1⟩ z] using h

/-- Interface form of (2.2), with the audit's explicit log-window rate. -/
theorem meshOsc_holds : SupercriticalLFPPAS.Core.MeshOscStmt := by
  unfold SupercriticalLFPPAS.Core.MeshOscStmt
  intro Ω _ P _ h hh X hXV a ha
  rcases hXV with ⟨hX, hXc⟩
  have hMesh : ∀ᵐ ω ∂P, ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ a : ℝ, 0 < a → ∀ n : ℕ, 1 ≤ n →
        ∀ ε δ : Set.Ioi (0 : ℝ),
          (ε : ℝ) ∈ Icc (Real.rpow ((n : ℝ) + 1) (-a)) (Real.rpow (n : ℝ) (-a)) →
          (δ : ℝ) ∈ Icc (Real.rpow ((n : ℝ) + 1) (-a)) (Real.rpow (n : ℝ) (-a)) →
        ∀ z ∈ closedBall (0 : ℂ) m,
            |X ε ω z - X δ ω z| ≤
              2 * C * a * (2 + a * Real.log ((n : ℝ) + 1)) / (n : ℝ) := by
    have hAll : ∀ m : ℕ, ∀ᵐ ω ∂P, ∃ C : ℝ, 0 ≤ C ∧
        ∀ a : ℝ, 0 < a → ∀ n : ℕ, 1 ≤ n →
          ∀ ε δ : Set.Ioi (0 : ℝ),
            (ε : ℝ) ∈ Icc (Real.rpow ((n : ℝ) + 1) (-a)) (Real.rpow (n : ℝ) (-a)) →
            (δ : ℝ) ∈ Icc (Real.rpow ((n : ℝ) + 1) (-a)) (Real.rpow (n : ℝ) (-a)) →
            ∀ z ∈ closedBall (0 : ℂ) m,
              |X ε ω z - X δ ω z| ≤
                2 * C * a * (2 + a * Real.log ((n : ℝ) + 1)) / (n : ℝ) := by
      intro m
      exact ae_jointHeatVersion_logWindow_estimate P h hh X hX hXc
        (closedBall (0 : ℂ) m) (isCompact_closedBall _ _)
    exact ae_all_iff.2 hAll
  filter_upwards [hMesh] with ω hMeshω
  intro K hK η hη
  obtain ⟨R, hR⟩ := hK.isBounded.subset_ball (0 : ℂ)
  obtain ⟨m, hm⟩ := exists_nat_ge R
  obtain ⟨C, hC₀, hC⟩ := hMeshω m
  have hrate := tendsto_logWindowRate_zero C a
  have hrateEvent : ∀ᶠ n : ℕ in atTop,
      2 * C * a * (2 + a * Real.log ((n : ℝ) + 1)) / (n : ℝ) < η :=
    hrate.eventually (Iio_mem_nhds hη)
  filter_upwards [hrateEvent, Filter.eventually_atTop.2 ⟨1, fun n hn => hn⟩]
    with n hnrate hn
  intro ε δ hεlo hεhi hδlo hδhi z hz
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hz' : z ∈ closedBall (0 : ℂ) m := by
    rw [mem_closedBall, dist_zero_right]
    have hzR := hR hz
    rw [mem_ball, dist_zero_right] at hzR
    exact le_trans hzR.le hm
  apply (hC a ha n hn ε δ ?_ ?_ z hz').trans hnrate.le
  · exact ⟨hεlo, hεhi⟩
  · exact ⟨hδlo, hδhi⟩

/-- Interface form of (2.3): the uniform cutoff error vanishes in outer probability. -/
theorem unifLoc_holds : SupercriticalLFPPAS.Core.UnifLocStmt := by
  unfold SupercriticalLFPPAS.Core.UnifLocStmt
  intro Ω _ P _ h hh X hXV K hK σ hσ
  rcases hXV with ⟨hX, hXc⟩
  obtain ⟨R, hKR⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  obtain ⟨H, hH, hCae, hErr⟩ :=
    ae_uniformLocalizedHeatField_error_circleGlobalSup h hh K hK R hKR
  have hBridge := ae_jointHeatVersion_eq_heatMollify P h hh X hX hXc
  let C : Ω → ℝ := fun ω => (circleGlobalSup H R ω).toReal
  have hCmeas : AEMeasurable C P := hCae.ennreal_toReal
  let B : ℕ → Set Ω := fun n => {ω | (n : ℝ) < C ω}
  have hBm : ∀ n, NullMeasurableSet (B n) P := by
    intro n
    exact nullMeasurableSet_lt measurable_const.aemeasurable hCmeas
  have hBanti : Antitone B := by
    intro n m hnm ω hω
    change (m : ℝ) < C ω at hω
    change (n : ℝ) < C ω
    exact lt_of_le_of_lt (by exact_mod_cast hnm) hω
  have hBinter : P (⋂ n, B n) = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [] with ω
    intro hω
    obtain ⟨n, hn⟩ := exists_nat_gt (C ω)
    exact (lt_asymm hn (mem_iInter.1 hω n))
  have hBtail : Tendsto (fun n : ℕ => P (B n)) atTop (𝓝 0) := by
    have hlim := tendsto_measure_iInter_atTop hBm hBanti ⟨0, measure_ne_top P _⟩
    rw [hBinter] at hlim
    simpa [Function.comp_def] using hlim
  have hGood : ∀ᵐ ω ∂P,
      (∀ δ : ℝ, ∀ hδ : δ ∈ Ioo (0 : ℝ) 1, 16 ≤ Real.log δ⁻¹ →
        ∀ L : ℝ, Real.log δ⁻¹ ≤ L → ∀ z ∈ K,
          |uniformLocalizedHeatField δ L hδ (h ω) z - heatMollify δ (h ω) z| ≤
            (16 * C ω * tailK 1) * Real.exp (-(Real.log δ⁻¹) ^ 2 / 16)) ∧
      (∀ ε : Set.Ioi (0 : ℝ), ∀ z : ℂ,
          X ε ω z = heatMollify (ε : ℝ) (h ω) z) := by
    filter_upwards [hErr, hBridge] with ω hErrω hBridgeω
    exact ⟨by simpa [C] using hErrω, hBridgeω⟩
  let Good : Set Ω := {ω |
      (∀ δ : ℝ, ∀ hδ : δ ∈ Ioo (0 : ℝ) 1, 16 ≤ Real.log δ⁻¹ →
        ∀ L : ℝ, Real.log δ⁻¹ ≤ L → ∀ z ∈ K,
          |uniformLocalizedHeatField δ L hδ (h ω) z - heatMollify δ (h ω) z| ≤
            (16 * C ω * tailK 1) * Real.exp (-(Real.log δ⁻¹) ^ 2 / 16)) ∧
      (∀ ε : Set.Ioi (0 : ℝ), ∀ z : ℂ,
          X ε ω z = heatMollify (ε : ℝ) (h ω) z)}
  have hGoodAE : ∀ᵐ ω ∂P, ω ∈ Good := by simpa [Good] using hGood
  have hNull : P Goodᶜ = 0 := by
    apply (measure_eq_zero_iff_ae_notMem).2
    filter_upwards [hGoodAE] with ω hω
    simpa using hω
  have hTailK : 0 ≤ tailK 1 := by
    unfold tailK
    apply setIntegral_nonneg measurableSet_Ioi
    intro r hr
    have hr0 : 0 ≤ r := hr.le
    simp [tailW]
    positivity
  let M : ℝ := 1 + 16 * tailK 1
  have hMpos : 0 < M := by dsimp [M]; linarith [hTailK]
  let Bad : ℝ → Set Ω := fun δ₁ => {ω | ∃ (δ : ℝ) (hδ : δ ∈ Ioo (0 : ℝ) 1),
      δ < δ₁ ∧ ∃ L : ℝ, Real.log δ⁻¹ ≤ L ∧ ∃ z ∈ K,
        σ < |SupercriticalLFPPAS.Core.locFieldC δ L hδ (h ω) z -
          X ⟨δ, hδ.1⟩ ω z|}
  change Tendsto (fun δ₁ : ℝ => P (Bad δ₁)) (𝓝[>] (0 : ℝ)) (𝓝 0)
  rw [ENNReal.tendsto_nhds_zero]
  intro τ hτ
  obtain ⟨τ', hτ', hττ'⟩ : ∃ τ' : ℝ, 0 < τ' ∧ ENNReal.ofReal (5 * τ') ≤ τ := by
    by_cases htop : τ = ⊤
    · exact ⟨1, one_pos, by rw [htop]; exact le_top⟩
    · refine ⟨τ.toReal / 5, ?_, ?_⟩
      · have := ENNReal.toReal_pos hτ.ne' htop
        positivity
      · rw [show 5 * (τ.toReal / 5) = τ.toReal by ring,
          ENNReal.ofReal_toReal htop]
  have hτ'enn : 0 < ENNReal.ofReal τ' := ENNReal.ofReal_pos.2 hτ'
  obtain ⟨N, hN⟩ :=
    (hBtail.eventually (eventually_le_nhds hτ'enn)).exists
  let N' : ℝ := ((N + 1 : ℕ) : ℝ)
  have hN'pos : 0 < N' := by dsimp [N']; positivity
  have hden : 0 < N' * M := mul_pos hN'pos hMpos
  let r₀ : ℝ := min (Real.exp (-16)) (σ / (N' * M))
  have hr₀pos : 0 < r₀ := by
    dsimp [r₀]
    exact lt_min (Real.exp_pos _) (div_pos hσ hden)
  have hsmall : ∀ᶠ δ₁ in 𝓝[>] (0 : ℝ), δ₁ < r₀ := by
    have hid : Tendsto (fun δ₁ : ℝ => δ₁) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    exact hid.eventually (eventually_lt_nhds hr₀pos)
  have hδ₁positive : ∀ᶠ δ₁ in 𝓝[>] (0 : ℝ), 0 < δ₁ := self_mem_nhdsWithin
  filter_upwards [hsmall, hδ₁positive] with δ₁ hδ₁small hδ₁pos
  have hδ₁exp : δ₁ < Real.exp (-16) :=
    lt_of_lt_of_le hδ₁small (min_le_left _ _)
  have hδ₁ratio : δ₁ < σ / (N' * M) :=
    lt_of_lt_of_le hδ₁small (min_le_right _ _)
  have hN'Mδ₁ : N' * M * δ₁ < σ := by
    rw [lt_div_iff₀ hden] at hδ₁ratio
    calc N' * M * δ₁ = δ₁ * (N' * M) := by ring
      _ < σ := hδ₁ratio
  have hBadSub : Bad δ₁ ⊆ B (N + 1) ∪ Goodᶜ := by
    intro ω hω
    by_cases hωGood : ω ∈ Good
    · left
      by_contra hωB
      have hCbound : C ω ≤ N' := by
        have hnot : ¬ (N' < C ω) := by
          intro hgt
          apply hωB
          change ((N + 1 : ℕ) : ℝ) < C ω
          simpa [N'] using hgt
        exact le_of_not_gt hnot
      change (∃ (δ : ℝ) (hδ : δ ∈ Ioo (0 : ℝ) 1), δ < δ₁ ∧ ∃ L : ℝ,
        Real.log δ⁻¹ ≤ L ∧ ∃ z ∈ K,
          σ < |SupercriticalLFPPAS.Core.locFieldC δ L hδ (h ω) z -
            X ⟨δ, hδ.1⟩ ω z|) at hω
      obtain ⟨δ, hδ, hδδ₁, L, hL, z, hz, hviol⟩ := hω
      have hlog₁ : 16 ≤ Real.log δ₁⁻¹ := by
        have hlt := Real.log_lt_log hδ₁pos hδ₁exp
        have hlogexp : Real.log (Real.exp (-16)) = -16 := Real.log_exp _
        have hinv : Real.log (δ₁⁻¹) = -Real.log δ₁ := by rw [Real.log_inv]
        rw [hlogexp] at hlt
        rw [hinv]
        linarith
      have hlogOrder : Real.log δ < Real.log δ₁ := Real.log_lt_log hδ.1 hδδ₁
      have hinvδ : Real.log (δ⁻¹) = -Real.log δ := by rw [Real.log_inv]
      have hinvδ₁ : Real.log (δ₁⁻¹) = -Real.log δ₁ := by rw [Real.log_inv]
      have hℓ₁le : Real.log δ₁⁻¹ ≤ Real.log δ⁻¹ := by
        rw [hinvδ₁, hinvδ]
        linarith
      have hℓ : 16 ≤ Real.log δ⁻¹ := hlog₁.trans hℓ₁le
      have hℓ₁nonneg : 0 ≤ Real.log δ₁⁻¹ := by linarith [hlog₁]
      have hsq : (Real.log δ₁⁻¹) ^ 2 ≤ (Real.log δ⁻¹) ^ 2 := by
        nlinarith [sq_nonneg (Real.log δ⁻¹ - Real.log δ₁⁻¹)]
      have hExpCmp : Real.exp (-(Real.log δ⁻¹) ^ 2 / 16) ≤ δ₁ := by
        have hsq₁ : Real.log δ₁⁻¹ ≤ (Real.log δ₁⁻¹) ^ 2 / 16 := by
          have hprod : 0 ≤ Real.log δ₁⁻¹ * (Real.log δ₁⁻¹ - 16) :=
            mul_nonneg hℓ₁nonneg (by linarith [hlog₁])
          nlinarith [hprod]
        have hExp₁ : Real.exp (-(Real.log δ₁⁻¹) ^ 2 / 16) ≤
            Real.exp (-(Real.log δ₁⁻¹)) :=
          Real.exp_le_exp.mpr (by nlinarith [hsq₁])
        have hExpOrd : Real.exp (-(Real.log δ⁻¹) ^ 2 / 16) ≤
            Real.exp (-(Real.log δ₁⁻¹) ^ 2 / 16) :=
          Real.exp_le_exp.mpr (by nlinarith [hsq])
        have hExpId : Real.exp (-(Real.log δ₁⁻¹)) = δ₁ := by
          rw [hinvδ₁, neg_neg, Real.exp_log hδ₁pos]
        exact hExpOrd.trans (hExp₁.trans_eq hExpId)
      change (∀ δ : ℝ, ∀ hδ : δ ∈ Ioo (0 : ℝ) 1, 16 ≤ Real.log δ⁻¹ →
          ∀ L : ℝ, Real.log δ⁻¹ ≤ L → ∀ z ∈ K,
            |uniformLocalizedHeatField δ L hδ (h ω) z - heatMollify δ (h ω) z| ≤
              (16 * C ω * tailK 1) * Real.exp (-(Real.log δ⁻¹) ^ 2 / 16)) ∧
        (∀ ε : Set.Ioi (0 : ℝ), ∀ z : ℂ,
          X ε ω z = heatMollify (ε : ℝ) (h ω) z) at hωGood
      have hBound := hωGood.1 δ hδ hℓ L hL z hz
      have hBridgeω := hωGood.2 ⟨δ, hδ.1⟩ z
      have hLocEq : SupercriticalLFPPAS.Core.locFieldC δ L hδ (h ω) z =
          uniformLocalizedHeatField δ L hδ (h ω) z := by rfl
      rw [hLocEq, hBridgeω] at hviol
      have hCnonneg : 0 ≤ C ω := by
        dsimp [C]
        exact ENNReal.toReal_nonneg
      have hCoeff :
          (16 * C ω * tailK 1) * Real.exp (-(Real.log δ⁻¹) ^ 2 / 16) ≤ N' * M * δ₁ := by
        calc (16 * C ω * tailK 1) * Real.exp (-(Real.log δ⁻¹) ^ 2 / 16)
            = C ω * (16 * tailK 1) * Real.exp (-(Real.log δ⁻¹) ^ 2 / 16) := by ring
          _ ≤ N' * M * δ₁ := by
            dsimp [M]
            gcongr
            linarith [hTailK]
      have hcontra := lt_of_lt_of_le hviol (hBound.trans hCoeff)
      exact (lt_asymm hN'Mδ₁ hcontra).elim
    · exact Or.inr hωGood
  have hPbad : P (Bad δ₁) ≤ P (B (N + 1)) + P Goodᶜ := by
    calc P (Bad δ₁) ≤ P (B (N + 1) ∪ Goodᶜ) := measure_mono hBadSub
      _ ≤ P (B (N + 1)) + P Goodᶜ := measure_union_le _ _
  have hBmono : B (N + 1) ⊆ B N := by
    intro ω hω
    change ((N + 1 : ℕ) : ℝ) < C ω at hω
    change (N : ℝ) < C ω
    exact lt_trans (by exact_mod_cast Nat.lt_succ_self N) hω
  have hPbound : P (Bad δ₁) ≤ ENNReal.ofReal τ' := by
    calc P (Bad δ₁) ≤ P (B (N + 1)) + P Goodᶜ := hPbad
      _ = P (B (N + 1)) := by rw [hNull, add_zero]
      _ ≤ P (B N) := measure_mono hBmono
      _ ≤ ENNReal.ofReal τ' := hN
  have hτsmall : ENNReal.ofReal τ' < ENNReal.ofReal (5 * τ') :=
    (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith)
  exact ((hPbound.trans_lt hτsmall).trans_le hττ').le

end SupercriticalLFPPAS.Field
