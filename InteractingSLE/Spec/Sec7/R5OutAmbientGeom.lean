import InteractingSLE.Spec.Sec7.R5OutFace
import InteractingSLE.Spec.Sec7.R5OutAmbientDefs

/-! # Source rational collars with protected old ambient half-discs (R98) -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology Metric
open QuantumZipper (H Hbar fwdHull fwdMap)
open scoped NNReal ENNReal
namespace InteractingSLE.Sec7.R5Out
open WangWu Lemma71I PocketCoord PocketJordan PocketMarks PocketTraversal PocketAdapt Lemma71C PocketCoupling
  PocketWordAssembly PocketSeedOpen PocketUnionPt PocketStop PocketStopField PocketStopSide PocketStopMarked
  PocketStopWallsFin Sec6 R5Phase R5Ref MartChar.RealFlow
open Theorem14.SB.FinRel (freeNear)
open Wire.Current.SideTest (rationalOriginalTime)
variable {Ω : Type*} {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ}
  {A : Set Ω} {c : Ω → Chart} {ω : Ω}

theorem exists_ambient_outer_cover {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hω : ω ∈ A)
    (hcfg : HOuter.IsOuterCfg (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : IsCfJordan (R ω) (L ω) r (ψ ω)) (hc : (c ω).IsConformal)
    (hdom : ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r) (heq : EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    (hζ : ζ' ω = ⊤) {mL mR : ℕ} {xL' : Fin mL → ℝ} {xR' : Fin mR → ℝ}
    {VL : Fin mL → ℝ≥0 → Ω → ℝ} {VR : Fin mR → ℝ≥0 → Ω → ℝ}
    (hVL : ∀ i t, VL i t ω = -rightImg (fun s : ℝ => -W' s.toNNReal ω) (-xL' i) t)
    (hVR : ∀ j t, VR j t ω = rightImg (fun s : ℝ => W' s.toNNReal ω) (xR' j) t)
    {nL nR : ℕ} {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ} (hxL : xL ω 0 = 0) (hxR : xR ω 0 = 0)
    {q : ℝ≥0} (hq : (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω)) (ξ : ℝ)
    (hX : extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ ∉ refExc R L r η ψ q ω)
    (hO : extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ ∉ R5Wall.outerExc R L r η ψ q ω)
    (hS : R5Wall.exposedOuterSel c (travAll R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r) xL xR q ω ξ) :
    ∃ (i : ℕ) (x ε x' ρ : ℝ),
      ω ∈ refEvent A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q i ∧
      η ω (rationalOriginalTime i) ∈ cfPocket (R ω) (L ω) r ∧
      IsRefCollar (refChart c R L r η ψ i ω) (relChart c (travAll R L r η ψ) q ω) ξ
        (extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ) x ε ∧
      extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ ∈ refHull W' ζ' i ω ∧
      Tendsto (relChart c (travAll R L r η ψ) q ω).2.1 (𝓝[H] (ξ : ℂ))
        (𝓝 (extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ)) ∧ 0 < ρ ∧
      QuantumZipper.fwdMapInv (fun t : ℝ => W' t.toNNReal ω) (rationalOriginalTime i) ''
        (H ∩ ball (x' : ℂ) ρ) ⊆ (relChart c (travAll R L r η ψ) q ω).dom ∧
      x' ∉ forceJumpSet (fun j => VL j (rationalOriginalTime i) ω - W' (rationalOriginalTime i) ω)
        (fun j => VR j (rationalOriginalTime i) ω - W' (rationalOriginalTime i) ω) ∧
      Tendsto (fun y => fwdMap (fun t : ℝ => W' t.toNNReal ω) (rationalOriginalTime i)
        ((relChart c (travAll R L r η ψ) q ω).2.1 y)) (𝓝[H] (ξ : ℂ)) (𝓝 (x' : ℂ)) ∧
      Tendsto (fun y => fwdMap (fun t : ℝ => W' t.toNNReal ω) (rationalOriginalTime i)
        ((refChart c R L r η ψ i ω).2.1 y)) (𝓝[H] (x : ℂ)) (𝓝 (x' : ℂ)) := by
  set p := extendFrom H (relChart c (travAll R L r η ψ) q ω).2.1 ξ with hpdef
  have hγ := (hcfg.props hψ).1
  have hP := hcfg.toPocket hψ
  have hTopo := hcfg.conf.isCfPocket (zero_notMem_closure_of_rightLo_pos hcfg.conf hcfg.bounded)
  have hNow := isConformal_relChart_of_driven (c := c) (γ := travAll R L r η ψ) hγ hq hc
  have hCH : cfPocket (R ω) (L ω) r ⊆ H := by
    rw [← hdom, hc.coe_dom]
    exact hc.2.1.image_subset
  obtain ⟨hLanding, hpcl, -⟩ :=
    current_landing (W := fun ω (s : ℝ) => W' s.toNNReal ω) hcfg hψ hc hdom heq hq ξ
  have hexp : ξ ∈ Ioo (geomLW (fun t ω => segDriver (travAll R L r η ψ ω) t) xL 0 q ω -
      segDriver (travAll R L r η ψ ω) q)
      (geomRW (fun t ω => segDriver (travAll R L r η ψ ω) t) xR 0 q ω - segDriver (travAll R L r η ψ ω) q) :=
    not_not.1 hS.1
  have hpC : p ∉ cfPocket (R ω) (L ω) r := hS.2
  -- positive capacity
  have hq0 : 0 < q := by
    rcases (show (0 : ℝ≥0) ≤ q from zero_le).eq_or_lt with h | h
    · have h0 := R5Wall.notMem_seed_interval_zero (γ := travAll R L r η ψ) (ω := ω) hγ hxL hxR ξ
      rw [h] at h0
      exact absurd hexp h0
    · exact h
  -- the landing is a wall point of `ℍ`
  have hpF : p ∈ frontier (cfPocket (R ω) (L ω) r) := by
    rw [hTopo.isOpen.frontier_eq]
    exact ⟨hpcl, hpC⟩
  simp only [R5Wall.outerExc, mem_insert_iff, mem_singleton_iff, not_or] at hO
  obtain ⟨hA₁, hA₂, hp0⟩ := hO
  have hpH : p ∈ H := by
    have hpF' := hpF
    rw [hTopo.frontier_eq] at hpF'
    rcases hpF' with ⟨v, hv, hpv⟩ | ⟨v, hv, hpv⟩
    · rcases hv.2.lt_or_eq with hlt | h1
      · exact hpv ▸ hTopo.mem_H₁ v ⟨hv.1, hlt⟩
      · subst h1
        rcases hTopo.mem_y with h | h
        · exact hpv ▸ h
        · exact absurd (hpv.symm.trans h) hp0
    · rcases hv.2.lt_or_eq with hlt | h1
      · exact hpv ▸ hTopo.mem_H₂ v ⟨hv.1, hlt⟩
      · subst h1
        rw [hTopo.seed] at hpv
        rcases hTopo.mem_y with h | h
        · exact hpv ▸ h
        · exact absurd (hpv.symm.trans h) hp0
  -- the landing is on the trace before the left stop, and near it the walls are visited
  have hExit : p ≠ cfPt (openPt (R ω) (L ω) r) := by
    intro he
    exact hX (Or.inr he)
  have hR := mem_trace_of_seed_interval (W := fun ω (s : ℝ) => W' s.toNNReal ω)
    hcfg hψ hc hdom heq hxL hxR hq hexp hExit
  -- the reference
  simp only [refExc, mem_insert_iff, mem_singleton_iff, not_or] at hX
  obtain ⟨s, hs0, hv, hQ, hne, hsT, ⟨ρ, hρ, hTail⟩, x, ε, hcol⟩ :=
    exists_visit_collar_tail (W := fun ω (s : ℝ) => W' s.toNNReal ω) hω hcfg hψ hc hdom heq hq0 hq ξ hX.1 hX.2
  set i := Denumerable.eqv ℚ s with hi
  set t := rationalOriginalTime i with htdef
  have hti : (t : ℝ) = s := coe_rationalOriginalTime_eqv hs0
  have hv' : η ω t ∈ cfPocket (R ω) (L ω) r := by rw [hti]; exact hv
  have hQ' : (visitCap R L r η ψ ω t).toNNReal ≤ q := by rw [hti]; exact hQ
  have hne' : η ω t ≠ p := by rw [hti]; exact hne
  have htT : (t : ℝ) ≤ leftStop R L r η ψ q ω := by rw [hti]; exact hsT.le
  have hcol' : IsRefCollar (refChart c R L r η ψ i ω) (relChart c (travAll R L r η ψ) q ω) ξ p x ε := by
    simp only [refChart, htdef ▸ hti]
    exact hcol
  have hHull : refHull W' ζ' i ω = fwdHull (fun s : ℝ => W' s.toNNReal ω) t :=
    refHull_eq_of_continuous hcfg.continuous_W hζ i
  obtain ⟨-, hOld0, hOldSub⟩ := visit_chart_subset
    (W := fun ω (s : ℝ) => W' s.toNNReal ω) hω hcfg hψ hc hdom heq t.coe_nonneg hv'
  have hOld : (refChart c R L r η ψ i ω).IsConformal := hOld0
  have hIncl := relChart_dom_antitone (c := c) (γ := travAll R L r η ψ) hc hγ hq hQ'
  have hOldDom' : ((refChart c R L r η ψ i ω).dom : Set ℂ) ⊆ H \ fwdHull (fun s : ℝ => W' s.toNNReal ω) t :=
    fun z hz => (hOldSub hz).2
  have hTail' : Disjoint (η ω '' Icc (t : ℝ) (leftStop R L r η ψ q ω)) (closedBall p ρ) := by
    rwa [hti]
  have hpK : p ∈ fwdHull (fun s : ℝ => W' s.toNNReal ω) t :=
    mem_old_hull_of_trace_near hcfg.trace t.coe_nonneg hTail' hR (mem_closedBall_self hρ.le) hpH
  -- the ambient image
  obtain ⟨x', hx'p, hlimOld⟩ := exists_ambient_access hcfg.trace hcfg.continuous_W hcfg.W_zero t.coe_nonneg hOld
    hOldDom' (tendsto_nhdsWithin_iff.1 hcol'.2.2.2.1).1 hpK
  have hlimCur : Tendsto (fun y => fwdMap (fun t : ℝ => W' t.toNNReal ω) t
      ((relChart c (travAll R L r η ψ) q ω).2.1 y)) (𝓝[H] (ξ : ℂ)) (𝓝 (x' : ℂ)) := by
    have htr : Tendsto (fun y => (refChart c R L r η ψ i ω).1 ((relChart c (travAll R L r η ψ) q ω).2.1 y))
        (𝓝[H] (ξ : ℂ)) (𝓝[H] (x : ℂ)) :=
      tendsto_nhdsWithin_iff.2 ⟨hcol'.2.2.1, eventually_nhdsWithin_of_forall fun y hy =>
        hOld.fwd_mem (hIncl (hNow.inv_mem_dom hy))⟩
    refine (hlimOld.comp htr).congr' (eventually_nhdsWithin_of_forall fun y hy => ?_)
    show fwdMap _ t ((refChart c R L r η ψ i ω).2.1 ((refChart c R L r η ψ i ω).1
      ((relChart c (travAll R L r η ψ) q ω).2.1 y))) = fwdMap _ t ((relChart c (travAll R L r η ψ) q ω).2.1 y)
    rw [hOld.inv_fwd (hIncl (hNow.inv_mem_dom hy))]
  obtain ⟨v, d, hd, hvlim, hHalf⟩ := exists_ambient_halfDisc_outer
    (W := fun ω (s : ℝ) => W' s.toNNReal ω) hcfg hψ hc hdom heq hxL hxR hq hexp hpH hExit
    t.coe_nonneg htT hρ hTail'
  have : NeBot (𝓝[H] (ξ : ℂ)) := R5Lift.nhdsWithin_H_neBot ξ
  have hvx : v = x' := by exact_mod_cast tendsto_nhds_unique hvlim hlimCur
  rw [hvx] at hHalf
  have hjump := notMem_forceJumpSet_of_extendFrom hcfg.trace hcfg.continuous_W hcfg.W_zero t.coe_nonneg xL' xR'
    hx'p hpH (Ne.symm hne')
  have hWt : W' t ω = (fun s : ℝ => W' s.toNNReal ω) (t : ℝ) := by simp only [Real.toNNReal_coe]
  have hJL : (fun j => VL j t ω - W' t ω) =
      fun j => -rightImg (fun s : ℝ => -(fun s : ℝ => W' s.toNNReal ω) s) (-xL' j) (t : ℝ) -
        (fun s : ℝ => W' s.toNNReal ω) (t : ℝ) := by
    funext j
    rw [hVL j t, hWt]
  have hJR : (fun j => VR j t ω - W' t ω) =
      fun j => rightImg (fun s : ℝ => W' s.toNNReal ω) (xR' j) (t : ℝ) - (fun s : ℝ => W' s.toNNReal ω) (t : ℝ) := by
    funext j
    rw [hVR j t, hWt]
  refine ⟨i, x, ε, x', d, ⟨hω, hq, Or.inl hv', hQ', hHull⟩, hv', hcol', by rw [hHull]; exact hpK,
    hLanding, hd, hHalf, ?_, hlimCur, hlimOld⟩
  rw [hJL, hJR]
  exact hjump


theorem exists_ambient_outer_coverInf {W' : ℝ≥0 → Ω → ℝ} {ζ' : Ω → ℝ≥0∞} (hω : ω ∈ A)
    (hcfg : HOuter.IsOuterCfgInf (R ω) (L ω) r (fun s : ℝ => W' s.toNNReal ω) (η ω))
    (hψ : IsCfJordanInf (R ω) (L ω) r (ψ ω)) (hc : (c ω).IsConformal)
    (hdom : ((c ω).dom : Set ℂ) = cfPocket (R ω) (L ω) r) (heq : EqOn (c ω).1 (ψ ω) (cfPocket (R ω) (L ω) r))
    (hζ : ζ' ω = ⊤) {mL mR : ℕ} {xL' : Fin mL → ℝ} {xR' : Fin mR → ℝ}
    {VL : Fin mL → ℝ≥0 → Ω → ℝ} {VR : Fin mR → ℝ≥0 → Ω → ℝ}
    (hVL : ∀ i t, VL i t ω = -rightImg (fun s : ℝ => -W' s.toNNReal ω) (-xL' i) t)
    (hVR : ∀ j t, VR j t ω = rightImg (fun s : ℝ => W' s.toNNReal ω) (xR' j) t)
    {nL nR : ℕ} {xL : Ω → Fin (nL + 1) → ℝ} {xR : Ω → Fin (nR + 1) → ℝ} (hxL : xL ω 0 = 0) (hxR : xR ω 0 = 0)
    {q : ℝ≥0} (hq : (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω)) (ξ : ℝ)
    (hX : extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ ∉ refExcInf R L r η ψ q ω)
    (hO : extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ ∉ R5Wall.outerExcInf R L r η ψ q ω)
    (hS : R5Wall.exposedOuterSel c (travAllInf R L r η ψ) (fun ω => cfPocket (R ω) (L ω) r) xL xR q ω ξ) :
    ∃ (i : ℕ) (x ε x' ρ : ℝ),
      ω ∈ refEventInf A R L r (fun ω (s : ℝ) => W' s.toNNReal ω) η ψ (refHull W' ζ') q i ∧
      η ω (rationalOriginalTime i) ∈ cfPocket (R ω) (L ω) r ∧
      IsRefCollar (refChartInf c R L r η ψ i ω) (relChart c (travAllInf R L r η ψ) q ω) ξ
        (extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ) x ε ∧
      extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ ∈ refHull W' ζ' i ω ∧
      Tendsto (relChart c (travAllInf R L r η ψ) q ω).2.1 (𝓝[H] (ξ : ℂ))
        (𝓝 (extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ)) ∧ 0 < ρ ∧
      QuantumZipper.fwdMapInv (fun t : ℝ => W' t.toNNReal ω) (rationalOriginalTime i) ''
        (H ∩ ball (x' : ℂ) ρ) ⊆ (relChart c (travAllInf R L r η ψ) q ω).dom ∧
      x' ∉ forceJumpSet (fun j => VL j (rationalOriginalTime i) ω - W' (rationalOriginalTime i) ω)
        (fun j => VR j (rationalOriginalTime i) ω - W' (rationalOriginalTime i) ω) ∧
      Tendsto (fun y => fwdMap (fun t : ℝ => W' t.toNNReal ω) (rationalOriginalTime i)
        ((relChart c (travAllInf R L r η ψ) q ω).2.1 y)) (𝓝[H] (ξ : ℂ)) (𝓝 (x' : ℂ)) ∧
      Tendsto (fun y => fwdMap (fun t : ℝ => W' t.toNNReal ω) (rationalOriginalTime i)
        ((refChartInf c R L r η ψ i ω).2.1 y)) (𝓝[H] (x : ℂ)) (𝓝 (x' : ℂ)) := by
  set p := extendFrom H (relChart c (travAllInf R L r η ψ) q ω).2.1 ξ with hpdef
  have hγ := (hcfg.props hψ).1
  have hP := hcfg.toPocketInf hψ
  have hTopo := hcfg.conf.isCfPocketInf hcfg.seed
  have hNow := isConformal_relChart_of_driven (c := c) (γ := travAllInf R L r η ψ) hγ hq hc
  have hCH : cfPocket (R ω) (L ω) r ⊆ H := by
    rw [← hdom, hc.coe_dom]
    exact hc.2.1.image_subset
  obtain ⟨hLanding, hpcl, -⟩ :=
    current_landingInf (W := fun ω (s : ℝ) => W' s.toNNReal ω) hcfg hψ hc hdom heq hq ξ
  have hexp : ξ ∈ Ioo (geomLW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) xL 0 q ω -
      segDriver (travAllInf R L r η ψ ω) q)
      (geomRW (fun t ω => segDriver (travAllInf R L r η ψ ω) t) xR 0 q ω - segDriver (travAllInf R L r η ψ ω) q) :=
    not_not.1 hS.1
  have hpC : p ∉ cfPocket (R ω) (L ω) r := hS.2
  -- positive capacity
  have hq0 : 0 < q := by
    rcases (show (0 : ℝ≥0) ≤ q from zero_le).eq_or_lt with h | h
    · have h0 := R5Wall.notMem_seed_interval_zero (γ := travAllInf R L r η ψ) (ω := ω) hγ hxL hxR ξ
      rw [h] at h0
      exact absurd hexp h0
    · exact h
  -- the landing is a wall point of `ℍ`
  have hpF : p ∈ frontier (cfPocket (R ω) (L ω) r) := by
    rw [hTopo.isOpen.frontier_eq]
    exact ⟨hpcl, hpC⟩
  simp only [R5Wall.outerExcInf, mem_insert_iff, mem_singleton_iff, not_or] at hO
  obtain ⟨hA₁, hA₂, hp0⟩ := hO
  have hpH : p ∈ H := by
    have hpF' := hpF
    rw [hTopo.frontier_eq] at hpF'
    rcases hpF' with ⟨v, hv, hpv⟩ | ⟨v, hv, hpv⟩
    · rcases (show (0 : ℝ) ≤ v from hv).lt_or_eq with hlt | h0
      · exact hpv ▸ hTopo.mem_H₁ v hlt
      · subst h0
        rcases hTopo.mem_y with h | h
        · exact hpv ▸ h
        · exact absurd (hpv.symm.trans h) hp0
    · rcases (show (0 : ℝ) ≤ v from hv).lt_or_eq with hlt | h0
      · exact hpv ▸ hTopo.mem_H₂ v hlt
      · subst h0
        rw [hTopo.seed] at hpv
        rcases hTopo.mem_y with h | h
        · exact hpv ▸ h
        · exact absurd (hpv.symm.trans h) hp0
  -- the landing is on the trace before the left stop, and near it the walls are visited
  have hR := mem_trace_of_seed_intervalInf (W := fun ω (s : ℝ) => W' s.toNNReal ω)
    hcfg hψ hc hdom heq hxL hxR hq hexp
  -- the reference
  simp only [refExcInf, mem_singleton_iff] at hX
  obtain ⟨s, hs0, hv, hQ, hne, hsT, ⟨ρ, hρ, hTail⟩, x, ε, hcol⟩ :=
    exists_visit_collarInf_tail (W := fun ω (s : ℝ) => W' s.toNNReal ω) hω hcfg hψ hc hdom heq hq0 hq ξ hX
  set i := Denumerable.eqv ℚ s with hi
  set t := rationalOriginalTime i with htdef
  have hti : (t : ℝ) = s := coe_rationalOriginalTime_eqv hs0
  have hv' : η ω t ∈ cfPocket (R ω) (L ω) r := by rw [hti]; exact hv
  have hQ' : (visitCapInf R L r η ψ ω t).toNNReal ≤ q := by rw [hti]; exact hQ
  have hne' : η ω t ≠ p := by rw [hti]; exact hne
  have htT : (t : ℝ) ≤ leftStopInf R L r η ψ q ω := by rw [hti]; exact hsT.le
  have hcol' : IsRefCollar (refChartInf c R L r η ψ i ω) (relChart c (travAllInf R L r η ψ) q ω) ξ p x ε := by
    simp only [refChartInf, htdef ▸ hti]
    exact hcol
  have hHull : refHull W' ζ' i ω = fwdHull (fun s : ℝ => W' s.toNNReal ω) t :=
    refHull_eq_of_continuous hcfg.continuous_W hζ i
  obtain ⟨-, hOld0, hOldSub⟩ := visit_chart_subsetInf
    (W := fun ω (s : ℝ) => W' s.toNNReal ω) hω hcfg hψ hc hdom heq t.coe_nonneg hv'
  have hOld : (refChartInf c R L r η ψ i ω).IsConformal := hOld0
  have hIncl := relChart_dom_antitone (c := c) (γ := travAllInf R L r η ψ) hc hγ hq hQ'
  have hOldDom' : ((refChartInf c R L r η ψ i ω).dom : Set ℂ) ⊆ H \ fwdHull (fun s : ℝ => W' s.toNNReal ω) t :=
    fun z hz => (hOldSub hz).2
  have hTail' : Disjoint (η ω '' Icc (t : ℝ) (leftStopInf R L r η ψ q ω)) (closedBall p ρ) := by
    rwa [hti]
  have hpK : p ∈ fwdHull (fun s : ℝ => W' s.toNNReal ω) t :=
    mem_old_hull_of_trace_near hcfg.trace t.coe_nonneg hTail' hR (mem_closedBall_self hρ.le) hpH
  -- the ambient image
  obtain ⟨x', hx'p, hlimOld⟩ := exists_ambient_access hcfg.trace hcfg.continuous_W hcfg.W_zero t.coe_nonneg hOld
    hOldDom' (tendsto_nhdsWithin_iff.1 hcol'.2.2.2.1).1 hpK
  have hlimCur : Tendsto (fun y => fwdMap (fun t : ℝ => W' t.toNNReal ω) t
      ((relChart c (travAllInf R L r η ψ) q ω).2.1 y)) (𝓝[H] (ξ : ℂ)) (𝓝 (x' : ℂ)) := by
    have htr : Tendsto (fun y => (refChartInf c R L r η ψ i ω).1 ((relChart c (travAllInf R L r η ψ) q ω).2.1 y))
        (𝓝[H] (ξ : ℂ)) (𝓝[H] (x : ℂ)) :=
      tendsto_nhdsWithin_iff.2 ⟨hcol'.2.2.1, eventually_nhdsWithin_of_forall fun y hy =>
        hOld.fwd_mem (hIncl (hNow.inv_mem_dom hy))⟩
    refine (hlimOld.comp htr).congr' (eventually_nhdsWithin_of_forall fun y hy => ?_)
    show fwdMap _ t ((refChartInf c R L r η ψ i ω).2.1 ((refChartInf c R L r η ψ i ω).1
      ((relChart c (travAllInf R L r η ψ) q ω).2.1 y))) = fwdMap _ t ((relChart c (travAllInf R L r η ψ) q ω).2.1 y)
    rw [hOld.inv_fwd (hIncl (hNow.inv_mem_dom hy))]
  obtain ⟨v, d, hd, hvlim, hHalf⟩ := exists_ambient_halfDisc_outerInf
    (W := fun ω (s : ℝ) => W' s.toNNReal ω) hcfg hψ hc hdom heq hxL hxR hq hexp hpH
    t.coe_nonneg htT hρ hTail'
  have : NeBot (𝓝[H] (ξ : ℂ)) := R5Lift.nhdsWithin_H_neBot ξ
  have hvx : v = x' := by exact_mod_cast tendsto_nhds_unique hvlim hlimCur
  rw [hvx] at hHalf
  have hjump := notMem_forceJumpSet_of_extendFrom hcfg.trace hcfg.continuous_W hcfg.W_zero t.coe_nonneg xL' xR'
    hx'p hpH (Ne.symm hne')
  have hWt : W' t ω = (fun s : ℝ => W' s.toNNReal ω) (t : ℝ) := by simp only [Real.toNNReal_coe]
  have hJL : (fun j => VL j t ω - W' t ω) =
      fun j => -rightImg (fun s : ℝ => -(fun s : ℝ => W' s.toNNReal ω) s) (-xL' j) (t : ℝ) -
        (fun s : ℝ => W' s.toNNReal ω) (t : ℝ) := by
    funext j
    rw [hVL j t, hWt]
  have hJR : (fun j => VR j t ω - W' t ω) =
      fun j => rightImg (fun s : ℝ => W' s.toNNReal ω) (xR' j) (t : ℝ) - (fun s : ℝ => W' s.toNNReal ω) (t : ℝ) := by
    funext j
    rw [hVR j t, hWt]
  refine ⟨i, x, ε, x', d, ⟨hω, hq, Or.inl hv', hQ', hHull⟩, hv', hcol', by rw [hHull]; exact hpK,
    hLanding, hd, hHalf, ?_, hlimCur, hlimOld⟩
  rw [hJL, hJR]
  exact hjump


end InteractingSLE.Sec7.R5Out
