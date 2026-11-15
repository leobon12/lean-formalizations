/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop59PiecesExp

/-!
# The root marks of Proposition 5.9's experiment and the initial dilation

Packet PROVE-PROP59-PIECES. Specification §5.2, proof of Proposition 5.9 (p. 143): "Map that component conformally to
`ℍ`, sending the initial flow-line tip to `0` and the counterflow tip `η′(r)` […] to `∞`. Denote this map by `ψ`.
Rescale it so that the marked points `z₋, z₊` in Figure 5.7 satisfy `z₋ ≤ −3` and `z₊ ≥ 3`."

The root word (PROVE-PROP59T4's `rootρL = jwL cL6 κ (flowLineRhoL …)`, `rootρR`) has the marks of the chart-`Q` flow
word followed by one junction on each side. Their positions in the joint chart `Ψ = R ∘ f′_r ∘ R` are PROVE-GLUECOND5's
`psiL`, `psiR` (images of real points) and the junctions `junL = Ψ(∞⁻)`, `junR = Ψ(∞⁺)` (`rootXL`, `rootXR`, the
pattern of CrossCond's `gXL`, `gXR`); the dilation `rootLam = 3 / min(−junL, junR)` puts the junctions beyond `∓3`.

* `ae_cfHistory_mem_goodSet49`: the counterflow history is in CrossCond's `goodSet49 r` (strict junction gaps), from
  the counterflow word's separation (Aux. lemma 6, `ZhanGT4.…ae_exists_isGeneratingTrace_top_of_admissible`) and the
  trace in `ℍ` (Part A);
* `rootXL`, `rootXR`, `rootLam`, `measurable_*`;
* `rootLam_mul_junL_le`, `le_rootLam_mul_junR`: the dilated junctions are beyond `∓3` on good histories;
* **`rootCandExpEx'`**, **`tip0UnboundedStatement_of_concretePieces'`**: the root experiment and Proposition 5.13's
  `htip0` with the canonical dilated root marks — the staged piece law is the only remaining input.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Function
open QuantumZipper (H fwdHull fwdMap)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec5.Prop59Pieces

open Prop513TreeExtract Prop513Schedule Prop513Target Exist.StagedLaw Exist.Staged LQGMetric Sec7.AdmCode Restart
open Sec4 Theorem14.StagedReg GlueCond CrossCond.Word49 WangWu LawUnique Prop59System Prop59Stage
open MartChar.RealFlow

/-! ### Strict junction gaps -/

/-- **The counterflow history has strict junction gaps** at every positive time `r`, almost surely. -/
theorem ae_cfHistory_mem_goodSet49 (hA : PartAInputsSixteenDiv) {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (hb : IsFig51Bounds κ a b a' b') {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ) {r : ℝ≥0} (hr : 0 < r) :
    ∀ᵐ ω ∂P, Cond44Ref.cfHistory W ζ ω ∈ goodSet49 r := by
  obtain ⟨b₀, J₀, _, _, hfl, hadm⟩ := exists_admissible_fig51_counterflow hκ hb hG hcf
  obtain ⟨_, 𝓕, VL, VR, B, _, hC⟩ := hfl
  have hk' : 0 < 16 / κ := by positivity
  have hreg := Prop513Wire.fig51_trace_mem_H_of_partA hA hκ hκ4 hb hG hcf
  filter_upwards [ZhanGT4.IsIntegratedSLEEvolution.ae_exists_isGeneratingTrace_top_of_admissible hk'
      (Theorem15.isOrderedForceWord_flowLine b₀ J₀ 0) hadm hC.1, hC.1.ae_isIntegratedSLEPath, hreg]
    with ω ⟨hζ, hsep, η, hη⟩ hp hω
  have hw : Continuous fun t => W t ω := by
    have := hp.2.2.2.1
    rw [hζ] at this
    exact continuousOn_univ.1 (this.mono fun t _ => ENNReal.coe_lt_top)
  refine cfHistory_mem_goodSet49 hp hζ hw hsep (iL := ⟨0, Nat.zero_lt_succ _⟩) rfl (iR := ⟨0, Nat.zero_lt_succ _⟩) rfl
    hη (fun t ht x _ he => ?_) hr
  have hH := hω.2 η hη t ht
  rw [he] at hH
  exact lt_irrefl _ (show (0 : ℝ) < ((x : ℂ)).im from hH) |>.elim

/-! ### The root marks -/

section Marks

variable {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ) (hb : IsFig51Bounds κ a b a' b')

/-- **The left root marks in the joint chart**: the images of the chart-`Q` flow word's left marks, then the left
junction. -/
def rootXL (x₀ : ℝ) (r : ℝ≥0) (y : HistorySpace 0 0) : Fin (rootNL (sourceWord (x₀ := x₀) hκ hb)) → ℝ :=
  Fin.snoc (fun i => psiL (cfDrv0 r y) r (flowLineXL (sourceWord (x₀ := x₀) hκ hb).fn
    (sourceWord (x₀ := x₀) hκ hb).jumps 0 i)) (junL (cfDrv0 r y) r)

/-- **The right root marks in the joint chart.** -/
def rootXR (x₀ : ℝ) (r : ℝ≥0) (y : HistorySpace 0 0) : Fin (rootNR (sourceWord (x₀ := x₀) hκ hb)) → ℝ :=
  Fin.snoc (fun j => psiR (cfDrv0 r y) r (flowLineXR (sourceWord (x₀ := x₀) hκ hb).fn
    (sourceWord (x₀ := x₀) hκ hb).jumps 0 j)) (junR (cfDrv0 r y) r)

open scoped Classical in
/-- **The initial dilation**: `3 / min(−junL, junR)` (`1` if a junction gap fails). -/
def rootLam (r : ℝ≥0) (y : HistorySpace 0 0) : ℝ :=
  if 0 < -junL (cfDrv0 r y) r ∧ 0 < junR (cfDrv0 r y) r then 3 / min (-junL (cfDrv0 r y) r) (junR (cfDrv0 r y) r)
  else 1

theorem rootLam_pos (r : ℝ≥0) (y : HistorySpace 0 0) : 0 < rootLam r y := by
  classical
  unfold rootLam
  split_ifs with hj
  · exact div_pos (by norm_num) (lt_min hj.1 hj.2)
  · exact one_pos

theorem measurable_rootLam (r : ℝ≥0) : Measurable (rootLam r) := by
  classical
  have hL := measurable_junL r
  have hR := measurable_junR r
  refine Measurable.ite ?_ (measurable_const.div (hL.neg.min hR)) measurable_const
  exact (measurableSet_lt measurable_const hL.neg).inter (measurableSet_lt measurable_const hR)

theorem measurable_rootXL (r : ℝ≥0) : Measurable (rootXL hκ hb x₀ r) :=
  measurable_snoc (measurable_pi_iff.2 fun _ => measurable_psiL r _) (measurable_junL r)

theorem measurable_rootXR (r : ℝ≥0) : Measurable (rootXR hκ hb x₀ r) :=
  measurable_snoc (measurable_pi_iff.2 fun _ => measurable_psiR r _) (measurable_junR r)

theorem farL_rootNL (c : BoundaryWord) :
    (farL (rootNL_pos c) : Fin (rootNL c)) = Fin.last (flowLineNL c.fn c.jumps 0) :=
  Fin.ext (by simp [farL, rootNL])

theorem farR_rootNR (c : BoundaryWord) :
    (farR (rootNR_pos c) : Fin (rootNR c)) = Fin.last (flowLineNR c.fn c.jumps 0) :=
  Fin.ext (by simp [farR, rootNR])

/-- The dilated left junction is at most `−3` on histories with strict junction gaps. -/
theorem rootLam_mul_junL_le {r : ℝ≥0} {y : HistorySpace 0 0} (hy : y ∈ goodSet49 r) :
    rootLam r y * rootXL hκ hb x₀ r y (farL (rootNL_pos _)) ≤ -3 := by
  classical
  obtain ⟨-, hgL, hgR⟩ := hy
  have hjL : 0 < -junL (cfDrv0 r y) r := by
    unfold junL; rw [neg_div, neg_neg]; exact one_div_pos.2 hgL
  have hjR : 0 < junR (cfDrv0 r y) r := by
    unfold junR; rw [neg_div]; exact neg_pos.2 (div_neg_of_pos_of_neg one_pos hgR)
  rw [farL_rootNL, rootXL, Fin.snoc_last]
  simp only [rootLam, hjL, hjR, and_self, ↓reduceIte]
  set m := min (-junL (cfDrv0 r y) r) (junR (cfDrv0 r y) r)
  have hm : 0 < m := lt_min hjL hjR
  have hmL : m ≤ -junL (cfDrv0 r y) r := min_le_left _ _
  rw [div_mul_eq_mul_div, div_le_iff₀ hm]
  nlinarith

/-- The dilated right junction is at least `3` on histories with strict junction gaps. -/
theorem le_rootLam_mul_junR {r : ℝ≥0} {y : HistorySpace 0 0} (hy : y ∈ goodSet49 r) :
    3 ≤ rootLam r y * rootXR hκ hb x₀ r y (farR (rootNR_pos _)) := by
  classical
  obtain ⟨-, hgL, hgR⟩ := hy
  have hjL : 0 < -junL (cfDrv0 r y) r := by
    unfold junL; rw [neg_div, neg_neg]; exact one_div_pos.2 hgL
  have hjR : 0 < junR (cfDrv0 r y) r := by
    unfold junR; rw [neg_div]; exact neg_pos.2 (div_neg_of_pos_of_neg one_pos hgR)
  rw [farR_rootNR, rootXR, Fin.snoc_last]
  simp only [rootLam, hjL, hjR, and_self, ↓reduceIte]
  set m := min (-junL (cfDrv0 r y) r) (junR (cfDrv0 r y) r)
  have hm : 0 < m := lt_min hjL hjR
  have hmR : m ≤ junR (cfDrv0 r y) r := min_le_right _ _
  rw [div_mul_eq_mul_div, le_div_iff₀ hm]
  nlinarith

end Marks

/-! ### The root experiment with the canonical marks -/

section Canon

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b')
  {Ω Ωa : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableSpace Ωa] [StandardBorelSpace Ωa]
  (P : Measure Ω) [IsProbabilityMeasure P] (Pa : Measure Ωa) [IsProbabilityMeasure Pa]
  (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (E : Schedule → ℕ → Ω → Driver)

/-- The canonical dilation of the root experiment at the counterflow time `q`. -/
def canonLam (q : ℚ) (ω : Ω) : ℝ := rootLam (q : ℝ).toNNReal (Cond44Ref.cfHistory W ζ ω)

/-- The canonical dilated left root marks. -/
def canonXL (q : ℚ) (ω : Ω) : Fin (rootNL (sourceWord (x₀ := x₀) hκ hb)) → ℝ :=
  fun i => canonLam W ζ q ω * rootXL hκ hb x₀ (q : ℝ).toNNReal (Cond44Ref.cfHistory W ζ ω) i

/-- The canonical dilated right root marks. -/
def canonXR (q : ℚ) (ω : Ω) : Fin (rootNR (sourceWord (x₀ := x₀) hκ hb)) → ℝ :=
  fun j => canonLam W ζ q ω * rootXR hκ hb x₀ (q : ℝ).toNNReal (Cond44Ref.cfHistory W ζ ω) j

/-- **The root experiment with the canonical dilated root marks** (`CandExpEx`): only the staged piece law of the
realized construction remains an input. -/
def rootCandExpEx' (hA : PartAInputsSixteenDiv) (hhm : Measurable h)
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ)
    (hE : ∀ s, IsStagedHistory κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
      (qField x₀ κ h) (scheduleSpec s) (E s))
    (hR : ∀ s, StagedPiecesRegular κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
      (scheduleSpec s) (E s))
    (noise : ℚ → (j : ℕ) → (Fin j → ℝ≥0) → ℝ≥0 → Ω → ℝ) (base : ℚ → MeasurableSpace (Ω × Ωa))
    (hbase : ∀ q, base q ≤ (inferInstance : MeasurableSpace (Ω × Ωa)))
    (hlaw : ∀ q : ℚ, 0 < q → Prop59StagePieceLawStatement κ (P.prod Pa) (rootρL κ (sourceWord (x₀ := x₀) hκ hb))
      (rootρR κ (sourceWord (x₀ := x₀) hκ hb))
      (histSys (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ)
        noise (Ωa := Ωa) q) ratGrid (rootNL_pos _) (rootNR_pos _)
        (rootStart x₀ hκ hb (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) q) univ (base q))) :
    CandExpEx κ P Pa (rootTarget W (extremeAngleTreeNode (capacityTree (driverTree E)) treeTime))
      fun _ => univ :=
  rootCandExpEx x₀ h44 hκ hκ4 hb P Pa h W ζ E (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) noise
    base hhm hG hcf hE hR
    (fun q => (measurable_rootLam _).comp (measurable_cfHistory_of_strip hcf))
    (fun q ω => rootLam_pos _ _)
    (fun q => measurable_pi_iff.2 fun i => ((measurable_rootLam _).comp (measurable_cfHistory_of_strip hcf)).mul
      ((measurable_pi_apply i).comp ((measurable_rootXL hκ hb _).comp (measurable_cfHistory_of_strip hcf))))
    (fun q => measurable_pi_iff.2 fun j => ((measurable_rootLam _).comp (measurable_cfHistory_of_strip hcf)).mul
      ((measurable_pi_apply j).comp ((measurable_rootXR hκ hb _).comp (measurable_cfHistory_of_strip hcf))))
    hbase
    (fun q hq => (ae_cfHistory_mem_goodSet49 hA hκ hκ4 hb hG hcf (r := (q : ℝ).toNNReal)
      (Real.toNNReal_pos.2 (by exact_mod_cast hq))).mono fun ω hω =>
        ⟨rootLam_mul_junL_le hκ hb hω, le_rootLam_mul_junR hκ hb hω⟩)
    hlaw

/-- **Proposition 5.13's root tip assertion from the concrete candidate pieces with the canonical root marks**:
`htip0` of `Prop513Wire.prop513_path_of_partA_reverseVisit` follows from the staged piece law of the realized
construction alone. -/
theorem tip0UnboundedStatement_of_concretePieces' (hA : PartAInputsSixteenDiv) (hhm : Measurable h)
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ)
    (hE : ∀ s, IsStagedHistory κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
      (qField x₀ κ h) (scheduleSpec s) (E s))
    (hR : ∀ s, StagedPiecesRegular κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
      (scheduleSpec s) (E s))
    (noise : ℚ → (j : ℕ) → (Fin j → ℝ≥0) → ℝ≥0 → Ω → ℝ) (base : ℚ → MeasurableSpace (Ω × Ωa))
    (hbase : ∀ q, base q ≤ (inferInstance : MeasurableSpace (Ω × Ωa)))
    (hlaw : ∀ q : ℚ, 0 < q → Prop59StagePieceLawStatement κ (P.prod Pa) (rootρL κ (sourceWord (x₀ := x₀) hκ hb))
      (rootρR κ (sourceWord (x₀ := x₀) hκ hb))
      (histSys (rootCand x₀ h44 hκ hκ4 hb P h W ζ (canonLam W ζ) (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ)
        noise (Ωa := Ωa) q) ratGrid (rootNL_pos _) (rootNR_pos _)
        (rootStart x₀ hκ hb (canonXL x₀ hκ hb W ζ) (canonXR x₀ hκ hb W ζ) q) univ (base q))) :
    Prop59Tips.Tip0UnboundedStatement P W (extremeAngleTreeNode (capacityTree (driverTree E)) treeTime) :=
  tip0UnboundedStatement_of_prodExp hκ hκ4
    (rootCandExpEx' x₀ h44 hκ hκ4 hb P Pa h W ζ E hA hhm hG hcf hE hR noise base hbase hlaw).toProdExp

end Canon

end InteractingSLE.Sec5.Prop59Pieces
