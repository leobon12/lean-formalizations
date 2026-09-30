import QuantumZipper.Proofs.Zipper.D3PlusLSCCMain
import QuantumZipper.Proofs.Zipper.D3PlusLSCZLoc
import QuantumZipper.Proofs.Zipper.D3PlusN2Scale

/-!
# D3⁺(ii), constant part: from a deterministic correction to the model zoom (`LSCCHeartStmt`)

Task LSCCONST. `LSCCTmStmt` (`D3PlusLSCCCore.lean`) is reduced to the pure level-shift statement
for the **model** zoom (correction `0`):

* `LSCCHeartStmt`: for the free field `X` and a real `c`, the laws of the rich zoomed pair
  `pairN1 L (localZ, circData α 0)` and `pairN1 (L + c) (localZ, circData α 0)` are TV-close as
  `L → ∞`. (Radial part: the level enters only through the hitting time of a Brownian motion
  with drift, whose law is TV-insensitive to a bounded shift of a large level; lateral part:
  scale invariance. Sheffield arXiv:1012.4797, proof of Prop. 1.6, p. 25; Duplantier–Miller–
  Sheffield arXiv:1409.7055, Props. 4.7–4.8, pp. 77–79.)

Proved here (own elementary arguments, following `d3PlusIN2Tm_of_parts` of `D3PlusN2Tm.lean`):

* `tendsto_tvDist_pair_cm`: two admissible corrections agreeing at `0` give TV-close laws of the
  rich zoomed **pair** (the rich data and the log scale): locality on the `ε`-local circles
  (`zoomPairFull_eq_lsczG`), the local Cameron–Martin bound
  (`d3PlusIN2FixCMLoc_of_parts cmIncrStmt_holds n2Cutoff_holds`) and the scale going to `0`
  (`d3PlusIN2FixScale_of_harm d3PlusN2HarmPart_holds`), exactly as `tendsto_tvDist_tm_cm`.
* `lsccTm_of_heart : LSCCHeartStmt → LSCCTmStmt`: triangle inequality through the constant
  correction `φ(0)`, which is the level `L + γ φ(0)` of the model (`locModel_circData_const`).
* `lscConstGen_locFieldFull_of_heart : LSCCHeartStmt → LSCConstGen locFieldFull`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace D3Plus

/-- On the event of a small positive local scale, the fixed-correction rich pair is `pairN1`. -/
theorem pairN1_eq_n2 {γ α L r : ℝ} {R : ℕ} {φ : ℂ → ℝ} {s : LocIdx r → ℝ} {f : FieldSample}
    (hag : AgreeNear (extLoc r s + ofFun (n2Shift γ α L φ)) (locModel γ L r (s, f)) r)
    (h2 : 0 < scaleParamOn γ (extLoc r s + ofFun (n2Shift γ α L φ)) (halfDisc r))
    (h3 : scaleParamOn γ (extLoc r s + ofFun (n2Shift γ α L φ)) (halfDisc r) < r / (R + 1)) :
    (locFieldFull R (n2Canon γ α L r φ (extLoc r s)),
      Real.log (scaleParamOn γ (extLoc r s + ofFun (n2Shift γ α L φ)) (halfDisc r))) =
      pairN1 γ r R L (s, f) := by
  refine Prod.ext (n2Canon_eq_TmRichN1 hag h2 h3) ?_
  have hsc := scaleParamOn_halfDisc_congr (γ := γ) hag
  have hgood := mem_goodN1_of_pos (hsc ▸ h2)
  show Real.log _ = Real.log (scaleSur γ L r (s, f))
  rw [scaleSur_eq hgood, ← hsc]

/-- **Two admissible corrections agreeing at `0` give TV-close rich zoomed pairs** (N1 form). -/
theorem tendsto_tvDist_pair_cm (hCM : D3PlusIN2FixCMLocStmt) (hSc : D3PlusIN2FixScaleStmt)
    {γ α r : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : Ω → FieldSample} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < Qc γ) (hr : 0 < r)
    (hX : IsFreeGFFModConstH X P) {φ φ' : ℂ → ℝ} (hφ : AdmCorr r φ) (hφ' : AdmCorr r φ')
    (h0 : φ 0 = φ' 0) (R : ℕ) :
    Tendsto (fun L => TV.tvDist
      (P.map fun ω => pairN1 γ r R L (localZ X r ω, circData α φ))
      (P.map fun ω => pairN1 γ r R L (localZ X r ω, circData α φ'))) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro η hη
  have hη2 : 0 < η / 2 := ENNReal.half_pos hη.ne'
  have hh0 : (fun z => φ' z - φ z) 0 = 0 := by simp [h0]
  have hcm := hCM r P X _ hr hX (admCorr_sub hφ hφ') hh0
  obtain ⟨ε, hεt, hεpos, hεr⟩ := ((ENNReal.tendsto_nhds_zero.1 hcm _ hη2).and
    (Ioc_mem_nhdsGT hr)).exists
  have hδ : 0 < ε / (R + 2) := by positivity
  have hRr : ε / (R + 2) ≤ r / (R + 1) :=
    (div_le_div_of_nonneg_left hεpos.le (by positivity) (by linarith)).trans
      (div_le_div_of_nonneg_right hεr (by positivity))
  have hsum := (hSc γ α r P X φ hγ hγ2 hα hr hX hφ _ hδ).add
    (hSc γ α r P X φ' hγ hγ2 hα hr hX hφ' _ hδ)
  rw [add_zero] at hsum
  filter_upwards [ENNReal.tendsto_nhds_zero.1 hsum _ hη2] with L hL
  have hZ := measurable_localZ hX hr
  have hWm : Measurable fun ω => resField ε (locZField X r ω) :=
    (measurable_resField ε).comp ((measurable_extLoc r).comp hZ)
  set G : (LocIdx ε → ℝ) → ((ℕ → ℝ) × (TestFun H → ℝ)) × ℝ := lsczG γ ε R
  have hG : Measurable G := measurable_lsczG γ ε R
  have hA : ∀ ψ : ℂ → ℝ, Measurable fun ω => pairN1 γ r R L (localZ X r ω, circData α ψ) :=
    fun ψ => (measurable_pairN1 γ r R L).comp (hZ.prodMk measurable_const)
  have hB : ∀ ψ : ℂ → ℝ, AdmCorr r ψ → ∀ᵐ ω ∂P, ω ∉ {ω |
      ¬(0 < scaleParamOn γ (locZField X r ω + ofFun (n2Shift γ α L ψ)) (halfDisc r) ∧
        scaleParamOn γ (locZField X r ω + ofFun (n2Shift γ α L ψ)) (halfDisc r) <
          ε / (R + 2))} →
      pairN1 γ r R L (localZ X r ω, circData α ψ) =
        G (resField ε (locZField X r ω + ofFun (n2Shift γ α L ψ))) := by
    intro ψ hψ
    refine Eventually.of_forall fun ω hnot => ?_
    have hq := not_not.1 hnot
    have hag := agreeNear_n2 (γ := γ) (L := L) (s := localZ X r ω) (f := circData α ψ)
      fun μ hμ => ⟨integrable_circ hψ.1 hμ, rfl⟩
    rw [← pairN1_eq_n2 hag hq.1 (hq.2.trans_le hRr)]
    exact zoomPairFull_eq_lsczG hεpos hεr hq.1 hq.2
  have e1 : (fun ω => resField ε (locZField X r ω + ofFun (n2Shift γ α L φ))) =
      fun ω => resField ε (locZField X r ω) + pairShift ε (n2Shift γ α L φ) := rfl
  have e2 : (fun ω => resField ε (locZField X r ω + ofFun (n2Shift γ α L φ'))) =
      fun ω => resField ε (locZField X r ω) + pairShift ε (n2Shift γ α L φ) +
        pairShift ε (fun z => φ' z - φ z) :=
    funext fun ω => resField_n2_sub hεr hφ.1 hφ'.1 _
  have hρ1 : AEMeasurable
      (fun ω => resField ε (locZField X r ω + ofFun (n2Shift γ α L φ))) P := by
    rw [e1]; exact (hWm.add_const _).aemeasurable
  have hρ2 : AEMeasurable
      (fun ω => resField ε (locZField X r ω + ofFun (n2Shift γ α L φ'))) P := by
    rw [e2]; exact ((hWm.add_const _).add_const _).aemeasurable
  have hloc := tvDist_map_le_of_local (hA φ).aemeasurable (hA φ').aemeasurable hρ1 hρ2 hG
    (hB φ hφ) (hB φ' hφ')
  rw [e1, e2] at hloc
  calc _ ≤ _ := hloc
    _ ≤ η / 2 + η / 2 := add_le_add ((tvDist_map_add_le P hWm _ _).trans hεt) hL
    _ = η := ENNReal.add_halves η

/-- **Node LSCC-HEART (pure level shift of the model zoom).** For the free field `X` and a real
`c`, the laws of the rich zoomed pair of the model `Z + α(−log‖·‖) + L/γ` (`Z` the local part)
at the levels `L` and `L + c` are TV-close as `L → ∞`. -/
def LSCCHeartStmt : Prop :=
  ∀ (γ α r : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → FieldSample) (c : ℝ),
    0 < γ → γ < 2 → α < Qc γ → 0 < r → IsFreeGFFModConstH X P →
    ∀ R : ℕ, Tendsto (fun L => TV.tvDist
      (P.map fun ω => pairN1 γ r R L (localZ X r ω, circData α (fun _ => 0)))
      (P.map fun ω => pairN1 γ r R (L + c) (localZ X r ω, circData α (fun _ => 0))))
      atTop (𝓝 0)

/-- **`LSCCTmStmt` from the model level shift** (triangle inequality through the constant
correction `φ(0)`, i.e. the level `L + γ φ(0)`). -/
theorem lsccTm_of_heart (hH : LSCCHeartStmt) : LSCCTmStmt := by
  intro γ α r Ω _ P _ X φ c hγ hγ2 hα hr hX hφ R
  have hCM := d3PlusIN2FixCMLoc_of_parts cmIncrStmt_holds n2Cutoff_holds
  have hSc := d3PlusIN2FixScale_of_harm d3PlusN2HarmPart_holds
  set k := φ 0 with hk
  have h1 := tendsto_tvDist_pair_cm hCM hSc hγ hγ2 hα hr hX hφ (admCorr_const r k) rfl R
  have h3 := h1.comp (tendsto_atTop_add_const_right atTop c tendsto_id)
  have h2 := (hH γ α r P X c hγ hγ2 hα hr hX R).comp
    (tendsto_atTop_add_const_right atTop (γ * k) tendsto_id)
  have h2' : Tendsto (fun L => TV.tvDist
      (P.map fun ω => pairN1 γ r R L (localZ X r ω, circData α (fun _ => k)))
      (P.map fun ω => pairN1 γ r R (L + c) (localZ X r ω, circData α (fun _ => k))))
      atTop (𝓝 0) := by
    refine h2.congr fun L => ?_
    have ea : (fun ω => pairN1 γ r R (L + γ * k) (localZ X r ω, circData α fun _ => 0)) =
        fun ω => pairN1 γ r R L (localZ X r ω, circData α fun _ => k) :=
      funext fun ω => pairN1_congr (locModel_circData_const hγ.ne' α L r k _).symm
    have eb : (fun ω => pairN1 γ r R (L + γ * k + c) (localZ X r ω, circData α fun _ => 0)) =
        fun ω => pairN1 γ r R (L + c) (localZ X r ω, circData α fun _ => k) := by
      funext ω
      refine pairN1_congr ?_
      rw [show L + γ * k + c = L + c + γ * k by ring]
      exact (locModel_circData_const hγ.ne' α (L + c) r k _).symm
    show TV.tvDist (P.map fun ω => pairN1 γ r R (L + γ * k)
      (localZ X r ω, circData α fun _ => 0)) (P.map fun ω => pairN1 γ r R (L + γ * k + c)
      (localZ X r ω, circData α fun _ => 0)) = _
    rw [ea, eb]
  have hsum := (h1.add h2').add h3
  rw [add_zero, add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => bot_le) (fun L => ?_)
  dsimp only [Function.comp]
  refine TV.tvDist_triangle.trans (add_le_add TV.tvDist_triangle ?_)
  exact TV.tvDist_comm.le

/-- **The constant (level-shift) part of rich D3⁺(ii) from the model level shift.** -/
theorem lscConstGen_locFieldFull_of_heart (hH : LSCCHeartStmt) : LSCConstGen locFieldFull :=
  lscConstGen_locFieldFull_of_tm (lsccTm_of_heart hH)

end D3Plus
end QuantumZipper
