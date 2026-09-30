import QuantumZipper.Proofs.Zipper.LocLenStmtsF1Node
import QuantumZipper.Proofs.Zipper.LocLenF1Flow
import QuantumZipper.Proofs.Zipper.LocLenF2Step4

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Follow-the-paper campaign (D75), task R6e-A: F1a–F1b with open-arc lengths

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, §5.4, proof of Theorem 1.3,
p. 71 (the Jensen rigidity / scaling argument "`L⁺/L⁻` is a.s. constant"). Open-arc copies
(substitution `unzipLengths ↦ unzipLengthsArc`, `zipLenDown ↦ zipLenDownArc`,
`lenF/leftTime ↦ lenFArc/leftTimeArc`) of:

* F1ABJensen.lean: `lenF_congr`, `unzipLengths_eq_readCfg`, `lenF_eq_readCfg`,
  `zipLenDown_drv`, `f1ab_of_inputs`, `f1ABStmt_of_inputs` (reusing `F1.jensen_rigidity_ae`,
  `F1.map_eq_of_read` verbatim);
* F1LenBridge.lean: `leftTime_of_strictMonoOn`, `bridge_of_strictMonoOn`,
  `lenBridgeStmt_of_strictMono`. The old proofs used that closed-interval lengths are always
  finite; open-arc lengths carry junk-free finiteness only a.s., so finiteness is a hypothesis
  here, discharged by `ae_unzipLengthsArc_lt_top_all` (from `LenPairCocycleArcStmt`,
  `LenFiniteArcStmt`);
* F1LenRead.lean:177 `lenReadStmt_of` (reusing `F1.aemeasurable_firstPassage_eval`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace LocLen

open F1

/-! ## `F_c` with open arcs and its reading from the data -/

theorem lenFArc_congr {γ : ℝ} {c c' : FieldSample × (ℝ → ℝ)}
    (h : unzipLengthsArc γ c = unzipLengthsArc γ c') : lenFArc γ c = lenFArc γ c' := by
  funext s
  simp only [lenFArc, leftTimeArc, lenTimeArc, h]

/-- Copy of `F1.unzipLengths_eq_readCfg`. -/
theorem unzipLengthsArc_eq_readCfg (γ : ℝ) {c : FieldSample × (ℝ → ℝ)} (hW : Continuous c.2)
    (hW0 : ∀ s, c.2 s = c.2 (s.toNNReal : ℝ)) :
    unzipLengthsArc γ c = unzipLengthsArc γ (readCfg (cfgData c)) := by
  funext t
  unfold readCfg cfgData
  simp only
  rw [WedgeCan4.piC_coordsFull, readDrv_eq hW hW0,
    unzipLengthsArc_congr_avgReg γ (Factorization.avgReg_reconstruct_coords c.1) _ t]

theorem lenFArc_eq_readCfg (γ : ℝ) {c : FieldSample × (ℝ → ℝ)} (hW : Continuous c.2)
    (hW0 : ∀ s, c.2 s = c.2 (s.toNNReal : ℝ)) (s : ℝ) :
    lenFArc γ c s = lenFArc γ (readCfg (cfgData c)) s := by
  rw [lenFArc_congr (unzipLengthsArc_eq_readCfg γ hW hW0)]

/-- Copy of `F1.zipLenDown_drv`. -/
theorem zipLenDownArc_drv (γ ℓ : ℝ) {c : FieldSample × (ℝ → ℝ)} (hW : Continuous c.2) :
    Continuous (zipLenDownArc γ ℓ c).2 ∧
      ∀ s, (zipLenDownArc γ ℓ c).2 s = (zipLenDownArc γ ℓ c).2 (s.toNNReal : ℝ) := by
  refine ⟨?_, fun s => ?_⟩
  · simp only [zipLenDownArc]
    exact ((hW.comp (continuous_const.add (continuous_const.mul
      (continuous_id.max continuous_const)))).sub continuous_const).div_const _
  · simp only [zipLenDownArc, Real.coe_toNNReal', max_eq_left (le_max_right s 0)]

/-! ## F1a–F1b -/

/-- **F1a–F1b, probabilistic skeleton, open arcs** (copy of `F1.f1ab_of_inputs`; Sheffield
p. 71). -/
theorem f1abArc_of_inputs {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (γ : ℝ) {c : Ω → FieldSample × (ℝ → ℝ)}
    (hmc : AEMeasurable (fun ω => cfgData (c ω)) P)
    (hdrv : ∀ᵐ ω ∂P, Continuous (c ω).2 ∧ ∀ s, (c ω).2 s = (c ω).2 (s.toNNReal : ℝ))
    (hE6 : ∀ ℓ : ℝ, 0 < ℓ →
      configLawFull (fun ω => zipLenDownArc γ ℓ (c ω)) P = configLawFull c P)
    (hE6m : ∀ ℓ : ℝ, 0 < ℓ → AEMeasurable (fun ω => cfgData (zipLenDownArc γ ℓ (c ω))) P)
    (hcoc : ∀ᵐ ω ∂P, ∀ ℓ s : ℝ, 0 < ℓ → 0 ≤ s →
      lenFArc γ (c ω) (ℓ + s) - lenFArc γ (c ω) ℓ = lenFArc γ (zipLenDownArc γ ℓ (c ω)) s)
    (hscale : ∀ n : ℕ, 1 ≤ n → ∃ c' : Ω → FieldSample × (ℝ → ℝ),
      configLawFull c' P = configLawFull c P ∧ AEMeasurable (fun ω => cfgData (c' ω)) P ∧
      (∀ᵐ ω ∂P, Continuous (c' ω).2 ∧ ∀ s, (c' ω).2 s = (c' ω).2 (s.toNNReal : ℝ)) ∧
      ∀ᵐ ω ∂P, ∀ s, 0 ≤ s → lenFArc γ (c' ω) s = lenFArc γ (c ω) (n * s) / n)
    (hread : ∀ s, AEMeasurable (fun d => lenFArc γ (readCfg d) s) (configLawFull c P))
    (hreg : ∀ᵐ ω ∂P, ContinuousOn (lenFArc γ (c ω)) (Ici 0) ∧
      MonotoneOn (lenFArc γ (c ω)) (Ici 0) ∧ lenFArc γ (c ω) 0 = 0)
    (hbridge : ∀ᵐ ω ∂P, ∀ t, 0 ≤ t → (unzipLengthsArc γ (c ω) t).1 < ⊤ ∧
      (unzipLengthsArc γ (c ω) t).2 =
        ENNReal.ofReal (lenFArc γ (c ω) ((unzipLengthsArc γ (c ω) t).1.toReal))) :
    ∃ f : Ω → ℝ≥0∞, ∀ᵐ ω ∂P, ∀ t, 0 ≤ t →
      (unzipLengthsArc γ (c ω) t).2 = f ω * (unzipLengthsArc γ (c ω) t).1 := by
  have hrd : ∀ᵐ ω ∂P, ∀ s, lenFArc γ (c ω) s = lenFArc γ (readCfg (cfgData (c ω))) s := by
    filter_upwards [hdrv] with ω h s
    exact lenFArc_eq_readCfg γ h.1 h.2 s
  have hFm : ∀ s, AEMeasurable (fun ω => lenFArc γ (c ω) s) P := fun s =>
    (AEMeasurable.comp_aemeasurable (f := fun ω => cfgData (c ω))
      (g := fun d => lenFArc γ (readCfg d) s) (hread s) hmc).congr
      (by filter_upwards [hrd] with ω h; exact (h s).symm)
  have hinc : ∀ q : ℚ, 0 < q → ∀ k : ℕ, 1 ≤ k →
      P.map (fun ω => lenFArc γ (c ω) ((k : ℝ) * q) - lenFArc γ (c ω) (((k : ℝ) - 1) * q)) =
        P.map (fun ω => lenFArc γ (c ω) q) := by
    intro q hq k hk
    have hq' : (0 : ℝ) < q := by exact_mod_cast hq
    rcases Nat.eq_or_lt_of_le hk with rfl | hk2
    · apply Measure.map_congr
      filter_upwards [hreg] with ω h
      simp [h.2.2]
    · have hk2' : (1 : ℝ) < k := by exact_mod_cast hk2
      have hℓ : 0 < ((k : ℝ) - 1) * q := mul_pos (by linarith) hq'
      refine map_eq_of_read (hE6 _ hℓ) hmc (hE6m _ hℓ) (hread q) ?_ ?_
      · filter_upwards [hrd] with ω h
        exact h q
      · filter_upwards [hcoc, hdrv] with ω hc hd
        have e : (k : ℝ) * q = ((k : ℝ) - 1) * q + q := by ring
        rw [e, hc _ _ hℓ hq'.le]
        have hz := zipLenDownArc_drv γ (((k : ℝ) - 1) * q) hd.1
        exact lenFArc_eq_readCfg γ hz.1 hz.2 _
  have hsc : ∀ q : ℚ, 0 < q → ∀ n : ℕ, 1 ≤ n →
      P.map (fun ω => lenFArc γ (c ω) ((n : ℝ) * q) / n) =
        P.map (fun ω => lenFArc γ (c ω) q) := by
    intro q hq n hn
    obtain ⟨c', hlaw, hm', hd', hs'⟩ := hscale n hn
    refine map_eq_of_read hlaw hmc hm' (hread q) ?_ ?_
    · filter_upwards [hrd] with ω h
      exact h q
    · filter_upwards [hs', hd'] with ω h hd
      rw [← h q (by exact_mod_cast hq.le)]
      exact lenFArc_eq_readCfg γ hd.1 hd.2 _
  have hJ := jensen_rigidity_ae (fun ω s => lenFArc γ (c ω) s) hFm hreg hinc hsc
  refine ⟨fun ω => ENNReal.ofReal (lenFArc γ (c ω) 1), ?_⟩
  filter_upwards [hJ, hbridge] with ω hj hb t ht
  obtain ⟨hlt, heq⟩ := hb t ht
  rw [heq, hj _ ENNReal.toReal_nonneg, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal hlt.ne, mul_comm]

/-- **F1a–F1b with open arcs** (copy of `F1.f1ABStmt_of_inputs`; Sheffield p. 71). -/
theorem f1ABArc_of_inputs (hcoc : LenCocycleArcStmt) (hsc : LenScaleArcStmt)
    (hrd : LenReadArcStmt) (hreg : LenRegArcStmt) (hbr : LenBridgeArcStmt)
    (hum : UnzipMeasArcStmt) : F1ABArcStmt := by
  intro hE6 κ Ω' _ P' _ Y B' h
  have hS := thm18Setting_of_pstar h
  have hIn := Thm18Asm.thm18Inputs_of_setting hS
  have hB := h.2.2.2.1
  exact f1abArc_of_inputs (Real.sqrt κ) (c := pcfg κ Y B')
    (aemeasurable_cfgData_drive_bm κ hIn.2.1 hB)
    (hB.cont.mono fun ω hc => ⟨continuous_drive_of κ hc, drive_toNNReal κ B' ω⟩)
    (fun ℓ hℓ => hE6 κ P' Y B' h ℓ hℓ) (fun ℓ hℓ => hum κ P' Y B' h ℓ hℓ)
    (hcoc κ P' Y B' h) (fun n hn => hsc κ P' Y B' h n hn) (hrd κ P' Y B' h)
    (hreg κ P' Y B' h) (hbr κ P' Y B' h)

/-! ## The bridge from strict monotonicity of the left length -/

/-- Copy of `F1.leftTime_of_strictMonoOn`, with finiteness of `L⁻_t` as a hypothesis. -/
theorem leftTimeArc_of_strictMonoOn {γ : ℝ} {c : FieldSample × (ℝ → ℝ)}
    (hmono : StrictMonoOn (fun t => (unzipLengthsArc γ c t).1) (Ici 0)) {t : ℝ} (ht : 0 ≤ t)
    (hfin : (unzipLengthsArc γ c t).1 < ⊤) :
    leftTimeArc γ c ((unzipLengthsArc γ c t).1.toReal) = t := by
  unfold leftTimeArc lenTimeArc
  rw [ENNReal.ofReal_toReal hfin.ne]
  refine IsLeast.csInf_eq ⟨⟨ht, le_rfl⟩, fun u hu => ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  exact absurd hu.2 (not_le.2 (hmono (mem_Ici.2 hu.1) (mem_Ici.2 ht) hlt))

/-- Copy of `F1.bridge_of_strictMonoOn`, with finiteness of both lengths as hypotheses. -/
theorem bridgeArc_of_strictMonoOn {γ : ℝ} {c : FieldSample × (ℝ → ℝ)}
    (hmono : StrictMonoOn (fun t => (unzipLengthsArc γ c t).1) (Ici 0)) {t : ℝ} (ht : 0 ≤ t)
    (hfin1 : (unzipLengthsArc γ c t).1 < ⊤) (hfin2 : (unzipLengthsArc γ c t).2 < ⊤) :
    (unzipLengthsArc γ c t).1 < ⊤ ∧
      (unzipLengthsArc γ c t).2 =
        ENNReal.ofReal (lenFArc γ c ((unzipLengthsArc γ c t).1.toReal)) := by
  refine ⟨hfin1, ?_⟩
  rw [lenFArc, leftTimeArc_of_strictMonoOn hmono ht hfin1, ENNReal.ofReal_toReal hfin2.ne]

/-- **`LenBridgeArcStmt`** from strict monotonicity of the open-arc left length, additivity
along the flow and fixed-time finiteness (copy of `F1.lenBridgeStmt_of_strictMono`). -/
theorem lenBridgeArc_of_strictMono (hsm : LenStrictMonoArcStmt) (hC : LenPairCocycleArcStmt)
    (hF : LenFiniteArcStmt) : LenBridgeArcStmt := by
  intro κ Ω' _ P' _ Y B' hP
  filter_upwards [hsm κ P' Y B' hP, ae_unzipLengthsArc_lt_top_all hC hF κ P' Y B' hP]
    with ω hω hfin t ht
  exact bridgeArc_of_strictMonoOn hω ht (hfin t ht).1 (hfin t ht).2

/-! ## Reading measurability -/

/-- **`LenReadArcStmt`** from fixed-time reading and regularity in time (copy of
`F1.lenReadStmt_of`, F1LenRead.lean:177). -/
theorem lenReadArc_of (h1 : LenReadTimeArcStmt) (h2 : LenReadRegArcStmt) : LenReadArcStmt := by
  intro κ Ω' _ P' _ Y B' hP s
  exact aemeasurable_firstPassage_eval
    (fun d t => (unzipLengthsArc (Real.sqrt κ) (readCfg d) t).1)
    (fun d t => (unzipLengthsArc (Real.sqrt κ) (readCfg d) t).2) (ENNReal.ofReal s)
    (fun t ht => (h1 κ P' Y B' hP t ht).fst) (fun t ht => (h1 κ P' Y B' hP t ht).snd)
    (h2 κ P' Y B' hP)

end LocLen
end QuantumZipper
