/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop59PiecesRoot

/-!
# The root experiment of Proposition 5.9 from the concrete candidate pieces

Packet PROVE-PROP59-PIECES. This file turns the concrete root candidates (`Prop59PiecesRoot`) into PROVE-PROP59T4's
experiment data on the product extension `Ω × Ωa` (`CandExpEx`, `Prop59PiecesChain`):

* `IsChainFamEx.mono`: the chain data only see the node images at samples where some candidate is alive;
* `rootImage`, **`image_subset_rootTarget`**, **`isBounded_rootImage`**: on the good set the dilated node images lie in
  the dilation of PROVE-PROP59T4's `rootTarget` (the joint chart `Ψ = R ∘ f′_r ∘ R` read from the counterflow
  history is the own-component chart of the counterflow driver), so they are bounded whenever `rootTarget` is;
* `liftPiece`, `liftFam`, `isRegFam_liftFam`, `recStart_liftFam`, `IsChainFamEx.lift`: everything lifts to `Ω × Ωa`
  through the first coordinate;
* **`rootCandExpEx`**: the root experiment (`CandExpEx`) from the concrete candidates, given the remaining inputs that
  are not part of the pieces: the initial dilation (far marks beyond `∓3`) and the staged piece law of the realized
  construction.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Function
open QuantumZipper (H fwdHull fwdMap)
open scoped NNReal ENNReal Real

universe u

namespace InteractingSLE.Sec5.Prop59Pieces

open Prop513TreeExtract Prop513Schedule Prop513Target Exist.StagedLaw Exist.Staged LQGMetric Sec7.AdmCode Restart
open Sec4 Theorem14.StagedReg GlueCond CrossCond.Word49 WangWu LawUnique Prop59System Prop59Stage

/-! ### Monotonicity of the chain data in the node images -/

theorem IsChainFamEx.mono {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {nL₀ nR₀ : ℕ}
    {cand : CandFam Ω nL₀ nR₀} {hnL : 0 < nL₀} {hnR : 0 < nR₀} {C C' : Ω → Set ℂ}
    {start : (j : ℕ) → (Fin j → ℝ≥0) → Ω → ℝ} (h : IsChainFamEx P cand hnL hnR C start)
    (hC : ∀ ω, (∃ j t, (0 : ℝ≥0∞) < (cand j t).ζ ω) → C ω ⊆ C' ω) : IsChainFamEx P cand hnL hnR C' start where
  start_zero := h.start_zero
  step := h.step
  trace j t := by
    filter_upwards [h.trace j t] with ω hω s hs hgap
    obtain ⟨W', η, T, h1, h2, h3, h4, h5⟩ := hω s hs hgap
    exact ⟨W', η, T, h1, h2, h3, h4, h5.trans (closure_mono (hC ω ⟨j, t, lt_of_le_of_lt zero_le hs⟩))⟩

/-! ### The node images and Proposition 5.13's target -/

section Image

variable {Ω : Type*} {nL₀ nR₀ : ℕ}

open scoped Classical in
/-- The node images restricted to the good set. -/
def TreeData.imageG (D : TreeData Ω nL₀ nR₀) (Z : Ω → Set ℂ) (ω : Ω) : Set ℂ :=
  if ω ∈ D.G then D.image Z ω else ∅

theorem TreeData.zeta_pos_mem_G {D : TreeData Ω nL₀ nR₀} {j : ℕ} {t : Fin j → ℝ≥0} {ω : Ω}
    (h : (0 : ℝ≥0∞) < (D.cand j t).ζ ω) : ω ∈ D.G := by
  have h' : ((0 : ℝ≥0) : ℝ≥0∞) < arcζ (D.img j t) (D.pre j t) (D.startCap j t) (D.alive j t) ω := h
  exact (lt_arcζ_iff.1 h').1.1.2

theorem TreeData.isChainFamEx_imageG [MeasurableSpace Ω] {D : TreeData Ω nL₀ nR₀} {P : Measure Ω}
    {hnL : 0 < nL₀} {hnR : 0 < nR₀} {Z : Ω → Set ℂ} {start : (j : ℕ) → (Fin j → ℝ≥0) → Ω → ℝ}
    (h : IsChainFamEx P D.cand hnL hnR (D.image Z) start) : IsChainFamEx P D.cand hnL hnR (D.imageG Z) start := by
  classical
  refine h.mono fun ω ⟨j, t, hpos⟩ => ?_
  simp only [TreeData.imageG, TreeData.zeta_pos_mem_G hpos, ↓reduceIte, subset_refl]

end Image

section Target

variable {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {ω : Ω} {r : ℚ} {E : Schedule → ℕ → Ω → Driver}

/-- **The joint chart read from a good counterflow history is the own-component chart** of the counterflow driver
(on points of the chart `Q` off the counterflow obstacle). -/
theorem revChart_eq_ownComponentChart (hy : Cond44Ref.cfHistory W ζ ω ∈ goodHitSet) (hζ : ζ ω = ⊤)
    (hw : Continuous fun t => W t ω) (z : ℂ) :
    revChart (cfDrv0 ((r : ℝ).toNNReal) (Cond44Ref.cfHistory W ζ ω)) ((r : ℝ).toNNReal) z =
      (ownComponentChart (fun s : ℝ => W s.toNNReal ω) (r : ℝ).toNNReal).1 (negInv z) ∧
    fwdHull (cfDrv0 ((r : ℝ).toNNReal) (Cond44Ref.cfHistory W ζ ω)) ((r : ℝ).toNNReal) =
      fwdHull (fun s : ℝ => W s.toNNReal ω) (r : ℝ).toNNReal := by
  set y := Cond44Ref.cfHistory W ζ ω
  have hg : y ∈ CfRegQ.goodCfSet := hy.1
  have hEq : EqOn (cfDrv0 ((r : ℝ).toNNReal) y) (fun s : ℝ => W s.toNNReal ω) (Icc 0 ((r : ℝ).toNNReal : ℝ)) := by
    intro s hs
    rw [cfDrv0_eq_cfDrv hg hs]
    show CfRegQ.hDrv y s.toNNReal = W s.toNNReal ω
    rw [hDrv_cfHistory hζ hw]
  refine ⟨?_, YuanCorollary13.fwdHull_eq_of_eqOn_Icc (continuous_cfDrv0 _ y)
    (hw.comp continuous_real_toNNReal) ((r : ℝ).toNNReal).coe_nonneg hEq⟩
  simp only [revChart, ownComponentChart, Chart.trans, Chart.loewner, Chart.id, infinitySourceChart, negInv]
  rw [Ito.fwdMap_congr_of_eqOn hEq]

end Target


section RootImage

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b')
  {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistOn upperHalfPlaneOpens}
  {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {nL₀ nR₀ : ℕ} {lam : Ω → ℝ} {xL0 : Ω → Fin nL₀ → ℝ}
  {xR0 : Ω → Fin nR₀ → ℝ} {noise : (j : ℕ) → (Fin j → ℝ≥0) → ℝ≥0 → Ω → ℝ} {E : Schedule → ℕ → Ω → Driver}

/-- **On the good set the dilated node images lie in the dilation of Proposition 5.13's root target.** -/
theorem image_subset_rootTarget {q : ℚ} {ω : Ω}
    (hω : ω ∈ rootGood x₀ h44 hκ hκ4 hb P h W ζ (q : ℝ).toNNReal) :
    (rootData x₀ h44 hκ hκ4 hb P h W ζ (q : ℝ).toNNReal lam xL0 xR0 noise).image (nodeSet E) ω ⊆
      (fun w => (lam ω : ℂ) * w) '' Prop59System.rootTarget W
        (extremeAngleTreeNode (capacityTree (driverTree E)) treeTime) q ω := by
  obtain ⟨⟨hy, hζ, hw⟩, -⟩ := rootGood_spec x₀ h44 hκ hκ4 hb hω
  have hcg := cfGood_of_mem_goodHitSet hy (q : ℝ).toNNReal
  rintro _ ⟨x, ⟨n, rfl⟩, hxH, hxK, rfl⟩
  obtain ⟨hR, hK⟩ := revChart_eq_ownComponentChart (r := q) hy hζ hw (driverTree E n ω (treeTime n))
  refine ⟨_, ⟨negInv (driverTree E n ω (treeTime n)), ⟨⟨n, rfl⟩, negInv_mem_H hxH, fun hmem => hxK ?_⟩, rfl⟩, ?_⟩
  · show driverTree E n ω (treeTime n) ∈ cfHullQ ((q : ℝ).toNNReal) (Cond44Ref.cfHistory W ζ ω)
    rw [hcg.2]
    refine ⟨negInv (driverTree E n ω (treeTime n)), ?_, negInv_negInv' _⟩
    show negInv (driverTree E n ω (treeTime n)) ∈
      fwdHull (cfDrv0 ((q : ℝ).toNNReal) (Cond44Ref.cfHistory W ζ ω)) ((q : ℝ).toNNReal)
    rw [hK]; exact hmem
  · show (lam ω : ℂ) * _ = (lam ω : ℂ) * revChart (cfDrv0 ((q : ℝ).toNNReal) (Cond44Ref.cfHistory W ζ ω))
      (((q : ℝ).toNNReal : ℝ≥0) : ℝ) (driverTree E n ω (treeTime n))
    rw [hR]

/-- **The node images are bounded when Proposition 5.13's root target is** (at every sample). -/
theorem isBounded_rootImage (q : ℚ) (ω : Ω)
    (hD : Bornology.IsBounded (Prop59System.rootTarget W
      (extremeAngleTreeNode (capacityTree (driverTree E)) treeTime) q ω)) :
    Bornology.IsBounded
      ((rootData x₀ h44 hκ hκ4 hb P h W ζ (q : ℝ).toNNReal lam xL0 xR0 noise).imageG (nodeSet E) ω) := by
  classical
  by_cases hω : ω ∈ rootGood x₀ h44 hκ hκ4 hb P h W ζ (q : ℝ).toNNReal
  · have hG : ω ∈ (rootData x₀ h44 hκ hκ4 hb P h W ζ (q : ℝ).toNNReal lam xL0 xR0 noise).G := hω
    simp only [TreeData.imageG, hG, ↓reduceIte]
    exact (Prop59System.isBounded_image_mul _ hD).subset (image_subset_rootTarget x₀ h44 hκ hκ4 hb hω)
  · have hG : ω ∉ (rootData x₀ h44 hκ hκ4 hb P h W ζ (q : ℝ).toNNReal lam xL0 xR0 noise).G := hω
    simp only [TreeData.imageG, hG, ↓reduceIte]
    exact Bornology.isBounded_empty

end RootImage

/-! ### Lifting to the product extension -/

section Lift

variable {Ω Ωa : Type*} {nL₀ nR₀ : ℕ}

/-- A piece on `Ω` read on `Ω × Ωa` through the first coordinate. -/
def liftPiece {nL nR : ℕ} (p : Piece Ω nL nR) : Piece (Ω × Ωa) nL nR where
  W u ω' := p.W u ω'.1
  VL i u ω' := p.VL i u ω'.1
  VR k u ω' := p.VR k u ω'.1
  B u ω' := p.B u ω'.1
  ζ ω' := p.ζ ω'.1
  clk ω' := p.clk ω'.1

/-- A candidate family on `Ω` read on `Ω × Ωa`. -/
def liftFam (cand : CandFam Ω nL₀ nR₀) : CandFam (Ω × Ωa) nL₀ nR₀ := fun j t => liftPiece (cand j t)

theorem isRegPiece_liftPiece [MeasurableSpace Ω] [MeasurableSpace Ωa] {nL nR : ℕ} {p : Piece Ω nL nR}
    (hp : IsRegPiece p) : IsRegPiece (liftPiece (Ωa := Ωa) p) where
  W := hp.W.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  VL i := (hp.VL i).comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  VR k := (hp.VR k).comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  ζ := hp.ζ.comp measurable_fst
  clk s := (hp.clk s).comp measurable_fst
  clk_cont ω' := hp.clk_cont ω'.1
  clk_mono ω' := hp.clk_mono ω'.1
  W_cont ω' := hp.W_cont ω'.1
  VL_cont ω' i := hp.VL_cont ω'.1 i
  VR_cont ω' k := hp.VR_cont ω'.1 k

theorem isRegFam_liftFam [MeasurableSpace Ω] [MeasurableSpace Ωa] {cand : CandFam Ω nL₀ nR₀}
    (h : IsRegFam cand) : IsRegFam (liftFam (Ωa := Ωa) cand) := fun j t => isRegPiece_liftPiece (h j t)

theorem candInv_liftFam (cand : CandFam Ω nL₀ nR₀) (j : ℕ) (t : Fin j → ℝ≥0) (q : ℝ≥0) (ω' : Ω × Ωa) :
    candInv (liftFam (Ωa := Ωa) cand) j t q ω' = candInv cand j t q ω'.1 := rfl

theorem recStart_liftFam (cand : CandFam Ω nL₀ nR₀) :
    ∀ (j : ℕ) (t : Fin j → ℝ≥0) (ω' : Ω × Ωa), recStart (liftFam (Ωa := Ωa) cand) j t ω' = recStart cand j t ω'.1
  | 0, _, _ => rfl
  | j + 1, t, ω' => by
    rw [recStart, recStart, recStart_liftFam cand j (Fin.init t) ω', candInv_liftFam]

/-- **The per-switch chain data lift to the product extension.** -/
theorem IsChainFamEx.lift [MeasurableSpace Ω] [MeasurableSpace Ωa] {P : Measure Ω} [SFinite P] {Pa : Measure Ωa}
    [IsProbabilityMeasure Pa] {cand : CandFam Ω nL₀ nR₀} {hnL : 0 < nL₀} {hnR : 0 < nR₀} {C : Ω → Set ℂ}
    {start : (j : ℕ) → (Fin j → ℝ≥0) → Ω → ℝ} (h : IsChainFamEx P cand hnL hnR C start) :
    IsChainFamEx (P.prod Pa) (liftFam (Ωa := Ωa) cand) hnL hnR (fun ω' => C ω'.1)
      (fun j t ω' => start j t ω'.1) where
  start_zero := (measurePreserving_fst (μ := P) (ν := Pa)).quasiMeasurePreserving.ae h.start_zero
  step j t q := (measurePreserving_fst (μ := P) (ν := Pa)).quasiMeasurePreserving.ae (h.step j t q)
  trace j t := (measurePreserving_fst (μ := P) (ν := Pa)).quasiMeasurePreserving.ae (h.trace j t)

end Lift


/-! ### The root experiment -/

section Assembly

variable (x₀ : ℝ) (h44 : Theorem12ParamCond44Statement.{0}) {κ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  (hb : IsFig51Bounds κ a b a' b')
  {Ω Ωa : Type} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] [MeasurableSpace Ωa] [StandardBorelSpace Ωa]
  (P : Measure Ω) [IsProbabilityMeasure P] (Pa : Measure Ωa) [IsProbabilityMeasure Pa]
  (h : Ω → DistOn upperHalfPlaneOpens) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (E : Schedule → ℕ → Ω → Driver)
  (lam : ℚ → Ω → ℝ) (xL0 : ℚ → Ω → Fin (rootNL (sourceWord (x₀ := x₀) hκ hb)) → ℝ)
  (xR0 : ℚ → Ω → Fin (rootNR (sourceWord (x₀ := x₀) hκ hb)) → ℝ)
  (noise : ℚ → (j : ℕ) → (Fin j → ℝ≥0) → ℝ≥0 → Ω → ℝ) (base : ℚ → MeasurableSpace (Ω × Ωa))

/-- The concrete candidates of the root experiment at the counterflow time `q`, on the product extension. -/
def rootCand (q : ℚ) : CandFam (Ω × Ωa) (rootNL (sourceWord (x₀ := x₀) hκ hb)) (rootNR (sourceWord (x₀ := x₀) hκ hb)) :=
  liftFam (rootData x₀ h44 hκ hκ4 hb P h W ζ (q : ℝ).toNNReal (lam q) (xL0 q) (xR0 q) (noise q)).cand

/-- The initial start of the root experiment: the driver at `0` and the root marks. -/
def rootStart (q : ℚ) (ω' : Ω × Ωa) :
    Start (rootNL (sourceWord (x₀ := x₀) hκ hb) + 0) (rootNR (sourceWord (x₀ := x₀) hκ hb) + 0) :=
  (0, xL0 q ω'.1, xR0 q ω'.1)

/-- **The root experiment of Proposition 5.9 from the concrete candidate pieces** (`CandExpEx`). The pieces, their
regularity, their chain data and the bounded images are the concrete ones of this packet; the remaining inputs are
the root marks with the initial dilation (`hinit`: far marks beyond `∓3`) and the staged piece law of the realized
construction (`hlaw`, PROVE-CROSSCOND-STAGED's target). -/
def rootCandExpEx (hhm : Measurable h)
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ)
    (hE : ∀ s, IsStagedHistory κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
      (qField x₀ κ h) (scheduleSpec s) (E s))
    (hR : ∀ s, StagedPiecesRegular κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
      (scheduleSpec s) (E s))
    (hlam : ∀ q, Measurable (lam q)) (hpos : ∀ q ω, 0 < lam q ω) (hxL : ∀ q, Measurable (xL0 q))
    (hxR : ∀ q, Measurable (xR0 q)) (hbase : ∀ q, base q ≤ (inferInstance : MeasurableSpace (Ω × Ωa)))
    (hinit : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, xL0 q ω (farL (rootNL_pos _)) ≤ -3 ∧ 3 ≤ xR0 q ω (farR (rootNR_pos _)))
    (hlaw : ∀ q : ℚ, 0 < q → Prop59StagePieceLawStatement κ (P.prod Pa) (rootρL κ (sourceWord (x₀ := x₀) hκ hb))
      (rootρR κ (sourceWord (x₀ := x₀) hκ hb))
      (histSys (rootCand x₀ h44 hκ hκ4 hb P h W ζ lam xL0 xR0 noise (Ωa := Ωa) q) ratGrid (rootNL_pos _)
        (rootNR_pos _) (rootStart x₀ hκ hb xL0 xR0 q) univ (base q))) :
    CandExpEx κ P Pa (rootTarget W (extremeAngleTreeNode (capacityTree (driverTree E)) treeTime))
      fun _ => univ where
  nL _ := rootNL (sourceWord (x₀ := x₀) hκ hb)
  nR _ := rootNR (sourceWord (x₀ := x₀) hκ hb)
  posL _ := rootNL_pos _
  posR _ := rootNR_pos _
  rhoL _ := rootρL κ (sourceWord (x₀ := x₀) hκ hb)
  rhoR _ := rootρR κ (sourceWord (x₀ := x₀) hκ hb)
  grid _ := ratTimes
  mesh _ := ratMesh
  times _ := ratGrid
  grid_ok _ n := isSwitchGrid_ratGrid n
  mesh_ok _ := tendsto_ratMesh
  cand q := rootCand x₀ h44 hκ hκ4 hb P h W ζ lam xL0 xR0 noise q
  y₀ q := rootStart x₀ hκ hb xL0 xR0 q
  R₀ _ := univ
  base := base
  image q ω' := (rootData x₀ h44 hκ hκ4 hb P h W ζ (q : ℝ).toNNReal (lam q) (xL0 q) (xR0 q) (noise q)).imageG
    (nodeSet E) ω'.1
  start q j t ω' := recStart (rootData x₀ h44 hκ hκ4 hb P h W ζ (q : ℝ).toNNReal (lam q) (xL0 q) (xR0 q)
    (noise q)).cand j t ω'.1
  reg q _ := isRegFam_liftFam (isRegFam_rootData x₀ h44 hκ hκ4 hb hhm hcf (hlam q) (hpos q) (hxL q) (hxR q))
  y₀_meas q _ := measurable_const.prodMk (((hxL q).comp measurable_fst).prodMk ((hxR q).comp measurable_fst))
  base_le q _ := hbase q
  R₀_meas _ _ := MeasurableSet.univ
  init q hq := by
    have h1 := (measurePreserving_fst (μ := P) (ν := Pa)).quasiMeasurePreserving.ae (hinit q hq)
    filter_upwards [h1] with ω' hω' _
    refine ⟨rfl, ?_, ?_⟩
    · simp only [rootStart, zero_add]; exact hω'.1
    · simp only [rootStart, zero_add]; exact hω'.2
  chain q _ := IsChainFamEx.lift (TreeData.isChainFamEx_imageG
    (isChainFamEx_rootData x₀ h44 hκ hκ4 hb hhm hG hcf hE hR (hlam q) (hpos q) (hxL q) (hxR q) _ _))
  pieceLaw := hlaw
  initialWord _ _ := isStageInit_sourceWord hκ hb
  image_bdd q _ ω' hD := isBounded_rootImage x₀ h44 hκ hκ4 hb q ω'.1 hD
  active _ _ := Eventually.of_forall fun _ _ => mem_univ _


/-- **Proposition 5.13's root tip assertion from the concrete candidate pieces** (`htip0` of
`Prop513Wire.prop513_path_of_partA_reverseVisit`), given the initial dilation of the root marks and the staged piece
law of the realized construction (PROVE-PROP59T3's reduction `ae_not_isBounded_of_pieceLaw` through
PROVE-PROP59T4's `tip0UnboundedStatement_of_prodExp`). -/
theorem tip0UnboundedStatement_of_concretePieces (hhm : Measurable h)
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ)
    (hE : ∀ s, IsStagedHistory κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
      (qField x₀ κ h) (scheduleSpec s) (E s))
    (hR : ∀ s, StagedPiecesRegular κ (sourceWord (x₀ := x₀) hκ hb).fn (sourceWord (x₀ := x₀) hκ hb).jumps P
      (scheduleSpec s) (E s))
    (hlam : ∀ q, Measurable (lam q)) (hpos : ∀ q ω, 0 < lam q ω) (hxL : ∀ q, Measurable (xL0 q))
    (hxR : ∀ q, Measurable (xR0 q)) (hbase : ∀ q, base q ≤ (inferInstance : MeasurableSpace (Ω × Ωa)))
    (hinit : ∀ q : ℚ, 0 < q → ∀ᵐ ω ∂P, xL0 q ω (farL (rootNL_pos _)) ≤ -3 ∧ 3 ≤ xR0 q ω (farR (rootNR_pos _)))
    (hlaw : ∀ q : ℚ, 0 < q → Prop59StagePieceLawStatement κ (P.prod Pa) (rootρL κ (sourceWord (x₀ := x₀) hκ hb))
      (rootρR κ (sourceWord (x₀ := x₀) hκ hb))
      (histSys (rootCand x₀ h44 hκ hκ4 hb P h W ζ lam xL0 xR0 noise (Ωa := Ωa) q) ratGrid (rootNL_pos _)
        (rootNR_pos _) (rootStart x₀ hκ hb xL0 xR0 q) univ (base q))) :
    Prop59Tips.Tip0UnboundedStatement P W (extremeAngleTreeNode (capacityTree (driverTree E)) treeTime) :=
  tip0UnboundedStatement_of_prodExp hκ hκ4
    (rootCandExpEx x₀ h44 hκ hκ4 hb P Pa h W ζ E lam xL0 xR0 noise base hhm hG hcf hE hR hlam hpos hxL hxR hbase
      hinit hlaw).toProdExp

end Assembly

end InteractingSLE.Sec5.Prop59Pieces
