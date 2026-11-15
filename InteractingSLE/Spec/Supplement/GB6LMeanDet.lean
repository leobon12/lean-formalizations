/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GB6LMeanRet
import InteractingSLE.Spec.Supplement.GB6LMeanChain
import InteractingSLE.Spec.Restart.RetPlumbLine
import InteractingSLE.Spec.Sec5.CrossCondGenCloseMarks
import InteractingSLE.Spec.Sec6.DrivingCriterion

/-!
# GB6's union mean, part 4: deterministic identities

Packet PROVE-GB6-LINEMEAN. The deterministic steps between the union mean of `Q3Chain`/`GB6LMeanChain` (written with
the chain's relative driver `Wr` and GB6's retained chart `Ψ = relMap Uω s`) and the canonical relative mean of
`HasGB6UnionMean` (written with a version `R` of the relative driver, the relative chart of the record and the typed
geometric marks):

* `eqOn_bhe_of_eqOff`: bounded harmonic extensions of data agreeing off two finite jump sets agree on `ℍ`;
* `relMap_jointChart_inv`, `jointChart_inv_mem`, **`jointChart_lift_inv`**: `Ψ ∘ Ψ⁻¹ = id` and the lift of the
  relative chart is `Im relLog − 2π` (which is why the chart field carries the height shift `2πχ(16/κ)`);
* **`eqOn_of_hullsUpTo`**: two continuous drivers from `0` generating the same relative hulls at every relative clock
  value up to `a(t)` agree on `[0, a(t)]` (intermediate values of the continuous clock, `Sec6.eqOn_of_fwdHull_eq`);
* **`eqOn_bheProc_of_cfFlowed`**: the bounded harmonic extension of the chart field's word at the marks flowed by the
  relative driver is the `bheProc` of the typed geometric marks, on the type event;
* `relClosureH_eq_self`, `retSet_subset_H`, `isOpen_H_diff_retSet`, `not_isBounded_lowerUnion_retSet`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdMap fwdMapInv fwdHull logDerivFwd chiC)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Supp8.GB6LMean

open LocalSets

/-! ### Bounded harmonic extensions -/

/-- Bounded harmonic extensions of data agreeing off two finite jump sets agree on `ℍ`. -/
theorem eqOn_bhe_of_eqOff {g g' : ℝ → ℝ} {S S' : Set ℝ} (hS : S.Finite) (hS' : S'.Finite) {u v : ℂ → ℝ}
    (hu : IsBoundedHarmonicExtension g S u) (hv : IsBoundedHarmonicExtension g' S' v)
    (h : ∀ x, x ∉ S → x ∉ S' → g x = g' x) : EqOn v u H := by
  have hu' := LocalExt.IsBoundedHarmonicExtension.mono_set hu (subset_union_left : S ⊆ S ∪ S')
  have hv' := LocalExt.IsBoundedHarmonicExtension.mono_set hv (subset_union_right : S' ⊆ S ∪ S')
  have hv'' : IsBoundedHarmonicExtension g (S ∪ S') v :=
    WangWu.isBoundedHarmonicExtension_congr
      (fun x hx => (h x (fun h' => hx (Or.inl h')) (fun h' => hx (Or.inr h'))).symm) hv'
  exact Impl.eqOn_of_isBoundedHarmonicExtension (hS.union hS') hu' hv''

/-! ### The relative chart -/

section Chart

open GB6 Theorem14.GW2JointKernel

variable {w : ℝ → ℝ} {s : ℝ}

theorem relMap_jointChart_inv (hw : Continuous w) (hw0 : w 0 = 0) (hs : 0 ≤ s) {y : ℂ} (hy : y ∈ H) :
    relMap w s ((jointChart w s).2.1 y) = y := by
  rw [jointChart_inv]
  show -(fwdMap w s (-(-(fwdMapInv w s (-y⁻¹))⁻¹)⁻¹))⁻¹ = y
  rw [GB6.neg_inv_neg_inv, QuantumZipper.RS.fwdMap_fwdMapInv hw hw0 hs (GB6.neg_inv_mem_H hy),
    GB6.neg_inv_neg_inv]

theorem jointChart_inv_mem (hw : Continuous w) (hw0 : w 0 = 0) (hs : 0 ≤ s) {y : ℂ} (hy : y ∈ H) :
    (jointChart w s).2.1 y ∈ H ∧ -((jointChart w s).2.1 y)⁻¹ ∈ H \ fwdHull w s := by
  rw [jointChart_inv]
  have h1 := QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hw hw0 hs (GB6.neg_inv_mem_H hy)
  refine ⟨GB6.neg_inv_mem_H h1.1, ?_⟩
  rw [GB6.neg_inv_neg_inv]
  exact h1

/-- **The lift of the relative chart is `Im relLog − 2π`** on `ℍ`. -/
theorem jointChart_lift_inv (hw : Continuous w) (hw0 : w 0 = 0) (hs : 0 ≤ s) {y : ℂ} (hy : y ∈ H) :
    (jointChart w s).2.2 ((jointChart w s).2.1 y) = (Q3Rel.relLog w s ((jointChart w s).2.1 y)).im - 2 * Real.pi := by
  set z := (jointChart w s).2.1 y with hz
  have hzH : z ∈ H := (jointChart_inv_mem hw hw0 hs hy).1
  change infinitySourceChart.2.2 (fwdMap w s (-z⁻¹)) + ((logDerivFwd w s (-z⁻¹)).im + 0) +
    infinitySourceChart.2.2 z = _
  have hneg := infinitySourceChart_lift_negInv hzH
  rw [Q3Rel.im_relLog, Sec7.StripSysField.infinitySourceChart_lift (fwdMap w s (-z⁻¹))]
  rw [Sec7.StripSysField.infinitySourceChart_lift, Sec7.StripSysField.infinitySourceChart_lift] at hneg
  rw [Sec7.StripSysField.infinitySourceChart_lift z]
  linarith

end Chart

/-! ### Drivers with the same relative hulls -/

section Hulls

open GB6

/-- **Two continuous drivers from `0` with the same relative hulls up to `a(t)` agree on `[0, a(t)]`.** -/
theorem eqOn_of_hullsUpTo {U Wc Wr Rp : ℝ → ℝ} {s t : ℝ≥0} (hWr : Continuous Wr) (hWr0 : Wr 0 = 0)
    (hRp : Continuous Rp) (hRp0 : Rp 0 = 0) (ha0 : relClock U s Wc 0 = 0)
    (hac : ContinuousOn (fun t' : ℝ≥0 => relClock U s Wc t') (Icc 0 t))
    (hW : ∀ t' : ℝ≥0, t' ≤ t → relMap U s '' fwdHull Wc t' = fwdHull Wr (relClock U s Wc t'))
    (hR : ∀ t' : ℝ≥0, t' ≤ t → relMap U s '' fwdHull Wc t' = fwdHull Rp (relClock U s Wc t')) :
    EqOn Wr Rp (Icc 0 (relClock U s Wc t)) := by
  rcases lt_or_ge (relClock U s Wc t) 0 with hneg | hnn
  · intro x hx
    exact absurd (hx.1.trans hx.2) (not_le.2 hneg)
  refine Sec6.eqOn_of_fwdHull_eq hWr hRp hWr0 hRp0 hnn fun r hr => ?_
  have hIVT := intermediate_value_Icc (bot_le : (0 : ℝ≥0) ≤ t) hac
  have hsub : Icc (0 : ℝ) (relClock U s Wc t) ⊆ Icc (relClock U s Wc ((0 : ℝ≥0) : ℝ)) (relClock U s Wc t) := by
    rw [NNReal.coe_zero, ha0]
  obtain ⟨t', ht', hrt'⟩ := hIVT (hsub hr)
  rw [← hrt', ← hW t' ht'.2, hR t' ht'.2]

end Hulls

/-! ### The typed word at the flowed marks -/

section Typed

open GB6 GB6.RelDrv Q3Stop RelSafeS Sec7.PocketTraversal Q3Chain Exist.StagedLaw MartChar.RealFlow

/-- **The bounded harmonic extension of the chart field's word at the marks flowed by a version `R` of the relative
driver is the `bheProc` of the typed geometric marks** (on the type event). -/
theorem eqOn_bheProc_of_cfFlowed {κ θ : ℝ} {c : Restart.BoundaryWord} {w : WordType} {Ω : Type*}
    {Hc : Ω → DistOn upperHalfPlaneOpens} {R : ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞} {rec : Ω → RecData} {ω : Ω}
    (hw : wordType (16 / κ) (gb6WordOfRec κ θ c (rec ω)) = w) (hRc : Continuous fun t => R t ω)
    (hR0 : R 0 ω = 0) (Q : ℝ≥0) {G : ℂ → ℝ}
    (hG : IsBoundedHarmonicExtension
      (cfFlowedData (16 / κ) (gb6WordOfRec κ θ c (rec ω)).fn (gb6WordOfRec κ θ c (rec ω)).jumps
        (fun x : ℝ => R x.toNNReal ω) Q)
      (cfFlowedJumps (gb6WordOfRec κ θ c (rec ω)).fn (gb6WordOfRec κ θ c (rec ω)).jumps
        (fun x : ℝ => R x.toNNReal ω) Q) G) :
    EqOn G (Restart.DomainMarkov.bheProc (16 / κ) (typedRhoL w) (typedRhoR w) R
      (fun i t ω => geomLW canonDrv (typedL κ θ c w) i t (rec ω, relVar Hc R V ω))
      (fun j t ω => geomRW canonDrv (typedR κ θ c w) j t (rec ω, relVar Hc R V ω)) ω Q) H := by
  set β := gb6WordOfRec κ θ c (rec ω) with hβ
  have hy : ∀ t, canonDrv t (rec ω, relVar Hc R V ω) = R t ω := fun t => relDrv_relVar hRc hR0 t
  have hb := Restart.DomainMarkov.isBoundedHarmonicExtension_bheProc (κ := 16 / κ) (ρL := typedRhoL w)
    (ρR := typedRhoR w) (W := R) (VL := fun i t ω => geomLW canonDrv (typedL κ θ c w) i t (rec ω, relVar Hc R V ω))
    (VR := fun j t ω => geomRW canonDrv (typedR κ θ c w) j t (rec ω, relVar Hc R V ω)) ω Q
  have ht : Restart.FCDet.IsFlowType (16 / κ) 0 β (typedXL (16 / κ) w β) (typedXR (16 / κ) w β) (typedRhoL w)
      (typedRhoR w) := isFlowType_typed hw
  set Rp : ℝ → ℝ := fun x : ℝ => R x.toNNReal ω with hRp
  have hRpc : Continuous Rp := hRc.comp continuous_real_toNNReal
  have hRp0 : Rp 0 = 0 := by simp only [hRp, Real.toNNReal_zero, hR0]
  have hRQ : Rp Q = R Q ω := by simp only [hRp, Real.toNNReal_coe]
  have hfin₁ : (forceJumpSet (fun i => geomLW canonDrv (typedL κ θ c w) i Q (rec ω, relVar Hc R V ω) - R Q ω)
      (fun j => geomRW canonDrv (typedR κ θ c w) j Q (rec ω, relVar Hc R V ω) - R Q ω)).Finite := by
    rw [← coe_initJumps]
    exact Finset.finite_toSet _
  refine eqOn_bhe_of_eqOff hfin₁ (Finset.finite_toSet _) hb hG fun x _ _ => ?_
  have hL : ∀ i, geomLW canonDrv (typedL κ θ c w) i Q (rec ω, relVar Hc R V ω) - R Q ω =
      -rightImg (fun s : ℝ => -(fun t => R t ω) s.toNNReal) (-typedXL (16 / κ) w β i) Q - (fun t => R t ω) Q :=
    fun i => by
      show -rightImg (fun r : ℝ => -canonDrv r.toNNReal (rec ω, relVar Hc R V ω)) (-typedXL (16 / κ) w β i) Q -
        R Q ω = _
      simp only [hy]
  have hR : ∀ j, geomRW canonDrv (typedR κ θ c w) j Q (rec ω, relVar Hc R V ω) - R Q ω =
      rightImg (fun s : ℝ => (fun t => R t ω) s.toNNReal) (typedXR (16 / κ) w β j) Q - (fun t => R t ω) Q :=
    fun j => by
      show rightImg (fun r : ℝ => canonDrv r.toNNReal (rec ω, relVar Hc R V ω)) (typedXR (16 / κ) w β j) Q -
        R Q ω = _
      simp only [hy]
  have e₁ : (fun i => geomLW canonDrv (typedL κ θ c w) i Q (rec ω, relVar Hc R V ω) - R Q ω) =
      fun i => -rightImg (fun s : ℝ => -(fun t => R t ω) s.toNNReal) (-typedXL (16 / κ) w β i) Q -
        (fun t => R t ω) Q := funext hL
  have e₂ : (fun j => geomRW canonDrv (typedR κ θ c w) j Q (rec ω, relVar Hc R V ω) - R Q ω) =
      fun j => rightImg (fun s : ℝ => (fun t => R t ω) s.toNNReal) (typedXR (16 / κ) w β j) Q -
        (fun t => R t ω) Q := funext hR
  rw [e₁, e₂, Restart.RetAux79.forceBoundaryData_geom_of_isFlowType ht (fun t => R t ω) Q x]
  simp only [cfFlowedData, flowedData]
  have hmL : ∀ i, markPosL Rp Q (flowLineXL β.fn β.jumps 0 i) =
      -rightImg (fun s : ℝ => -(fun t => R t ω) s.toNNReal) (-flowLineXL β.fn β.jumps 0 i) Q - (fun t => R t ω) Q :=
    fun i => by
      rw [Sec5.CrossCond.Gen.markPosL_eq_rightImg_of_nonpos hRpc hRp0 Q.coe_nonneg
        (Theorem14.GW3Word.flowLineXL_nonpos _ _ i), hRQ]
  have hmR : ∀ j, markPos Rp Q (flowLineXR β.fn β.jumps 0 j) =
      rightImg (fun s : ℝ => (fun t => R t ω) s.toNNReal) (flowLineXR β.fn β.jumps 0 j) Q - (fun t => R t ω) Q :=
    fun j => by
      rw [Sec5.CrossCond.Gen.markPos_eq_rightImg_of_nonneg hRpc hRp0 Q.coe_nonneg
        (Theorem14.GW3Word.flowLineXR_nonneg _ _ j), hRQ]
  rw [funext hmL, funext hmR]

end Typed

/-! ### The retained set and relative closures -/

section RetSet

open GB6LineL

theorem relClosureH_eq_self {S : Set ℂ} (hSH : S ⊆ H) (hS : IsOpen (H \ S)) : relClosureH S = S := by
  refine Subset.antisymm (fun z ⟨hzH, hzc⟩ => ?_) fun z hz => ⟨hSH hz, subset_closure ⟨hz, hSH hz⟩⟩
  by_contra hzS
  have hn : H \ S ∈ 𝓝 z := hS.mem_nhds ⟨hzH, hzS⟩
  obtain ⟨y, hy, hyS⟩ := mem_closure_iff_nhds.1 hzc _ hn
  exact hy.2 hyS.1

theorem retSet_subset_H {Ω : Type*} (s : ℝ≥0) (Wα : ℝ≥0 → Ω → ℝ) (ζα : Ω → ℝ≥0∞) (ω : Ω) :
    retSet s Wα ζα ω ⊆ H := by
  unfold retSet retOfRec
  split_ifs
  · exact WangWu.image_negInv_subset_H (QuantumZipper.fwdHull_mono.2 _)
  · exact subset_rfl

theorem isOpen_H_diff_retSet {Ω : Type*} (s : ℝ≥0) (Wα : ℝ≥0 → Ω → ℝ) (ζα : Ω → ℝ≥0∞) (ω : Ω) :
    IsOpen (H \ retSet s Wα ζα ω) := by
  unfold retSet retOfRec
  split_ifs
  · rw [Q3Rel.compl_invHull]
    exact WangWu.isOpen_image_negInv (QuantumZipper.FwdHolo.isOpen_compl_fwdHull (Exist.StagedLaw.continuous_rdrv _)
      s.coe_nonneg) sdiff_subset
  · simp only [Set.sdiff_self, isOpen_empty]

theorem not_isBounded_lowerUnion_retSet {Ω : Type*} (s : ℝ≥0) (Wα : ℝ≥0 → Ω → ℝ) (ζα : Ω → ℝ≥0∞) (ω : Ω) :
    ∀ z ∈ lowerUnion (retSet s Wα ζα ω),
      ¬ Bornology.IsBounded (connectedComponentIn (lowerUnion (retSet s Wα ζα ω)) z) := by
  unfold retSet retOfRec
  split_ifs
  · exact Sec5.GlueCond.not_isBounded_lowerUnion_image_negInv
      (isHPHull_fwdHull (Exist.StagedLaw.continuous_rdrv _) s.coe_nonneg)
  · intro z _
    have e : lowerUnion H = univ := by
      ext w
      simp only [lowerUnion, mem_union, mem_univ, iff_true]
      by_cases hw : 0 < w.im
      · exact Or.inl hw
      · exact Or.inr (not_lt.1 hw)
    rw [e, connectedComponentIn_univ, PreconnectedSpace.connectedComponent_eq_univ]
    intro hb
    have : CompactSpace ℂ := Metric.compactSpace_iff_isBounded_univ.2 hb
    exact noncompact_univ ℂ isCompact_univ

end RetSet

end InteractingSLE.Supp8.GB6LMean
