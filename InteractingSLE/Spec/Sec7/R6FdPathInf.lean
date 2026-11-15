/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6FdArcInf
import InteractingSLE.Spec.Sec7.R6FdPath
import InteractingSLE.Spec.Sec7.R6FcWireInf

/-!
# The non-corner landing of the shared seed coordinate, outer pocket opening at the flow seed

Packet PROVE-R6-FACE3. `R6FdPath.nonCornerLanding_left/_right` for an outer pocket `C = cfPocket R L r` opening at the
flow seed (`IsOuterCfgInf`, `IsCfJordanInf`, the traversal `travAllInf`, the relative tip `relTipInf`) and a bounded
contained pocket `U` (`IsCfPocketConfig`). The argument is the same; `C` has no finite outgoing corner, so the
`≠ x₀ᶜ` side conditions disappear. Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull)
open SupercriticalConformalCovariance (IsConformalBijection)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R6Fd

open Sec6 PocketTraversal Lemma71C PocketJordan PocketCoord PocketCoupling PocketStop PocketStopField HOuter
  PocketWordAssembly R6Safe R6Nest PocketSeedOpen R7StopIn
open WangWu (chartAL chartAR)

variable {Ω : Type*}

/-- **The relative tip at an earlier relative time** (pocket opening at the flow seed): in `closure C` and visited by
the fibre end at the later time. -/
theorem relTip_factsInf {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {W : ℝ → ℝ} {η : Ω → ℝ → ℂ} {ω : Ω}
    (hcf : IsOuterCfgInf (R ω) (L ω) r W (η ω)) {u' u : ℝ} (hu' : 0 ≤ u') (huu : u' ≤ u) :
    relTipInf R L r η u' ω ∈ closure (cfPocket (R ω) (L ω) r) ∧
      relTipInf R L r η u' ω ∈ η ω '' Icc 0 (pocketFibreInf (η ω) (cfPocket (R ω) (L ω) r)
        (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0))
        (clockOf (clockEnd (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0))) u)) := by
  have hP := hcf.erase
  have hL₀ := hP.clockEnd_pos
  have hv' := clockOf_mem_Ico hL₀ hu'
  have hv := clockOf_mem_Ico hL₀ (hu'.trans huu)
  refine ⟨hP.erasedPath_mem hv', _, ⟨hP.fibre_nonneg hv', ?_⟩, rfl⟩
  exact hP.monotoneOn_fibre hv' hv
    ((strictMonoOn_clockOf hL₀).monotoneOn (mem_Ici.2 hu') (mem_Ici.2 (hu'.trans huu)) huu)

/-- **The non-corner landing of the right seed coordinate** (shared wall `L`, outer pocket opening at the flow seed,
bounded `U`; one realization). -/
theorem nonCornerLandingInf_left {A : Set Ω} {R L : Ω → ℝ≥0 → ℂ} {R' : ℝ≥0 → ℂ} {r r' : ℝ≥0} {W : Ω → ℝ → ℝ}
    {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {ψ' : ℂ → ℂ} {n : Ω → ℤ} {ω : Ω}
    (hcfg : ∀ ω ∈ A, IsOuterCfgInf (R ω) (L ω) r (W ω) (η ω)) (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω))
    (hω : ω ∈ A) (hcfg' : IsCfPocketConfig R' (L ω) r' (W ω) (η ω)) (hψ' : IsCfJordan R' (L ω) r' ψ')
    {q : ℝ≥0} (hq0 : 0 < q) (hq : (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω))
    (hsub : cfPocket R' (L ω) r' ⊆ cfPocket (R ω) (L ω) r)
    {u : ℝ} (hu0 : 0 ≤ u) (hcap : capClock (travAllInf R L r η ψ ω) u = q)
    (hrel : relTipInf R L r η u ω ∈ cfPocket R' (L ω) r')
    {u₁ : ℝ} (hu₁0 : 0 ≤ u₁) (hcap₁ : capClock (travAllInf R L r η ψ ω) u₁ ≤ q)
    (harc : relTipInf R L r η u₁ ω ∈ cfArcL R' (L ω) r' '' Ioo 0 1) :
    R6Fc.IsNonCornerLanding (R6Fc.curChartInf A R L r η ψ n q ω) (R6Fc.seedRInf R L r η ψ q ω)
      (cfPocket R' (L ω) r') (cfPocket (R ω) (L ω) r) (cfPt (openPt R' (L ω) r')) := by
  classical
  -- the outer pocket and its chart at `q`
  have hcf := hcfg ω hω
  have hG : ∀ ω ∈ A, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  have hCo : ∀ ω ∈ A, IsOpen (cfPocket (R ω) (L ω) r) := fun ω hω =>
    isOpen_image_negInv' (hG ω hω).isOpen_changePocket (hG ω hω).changePocket_subset_H
  have hCH : ∀ ω ∈ A, cfPocket (R ω) (L ω) r ⊆ H := fun ω hω =>
    PocketJordan.image_negInv_subset_H (hG ω hω).changePocket_subset_H
  have hψc : ∀ ω ∈ A, IsConformalBijection (ψ ω) (cfPocket (R ω) (L ω) r) H := fun ω hω => (hψ ω hω).2.2.2.1
  have hJ := hψ ω hω
  have hγ : IsDrivenCurve (travAllInf R L r η ψ ω) := (hcf.props hJ).1
  obtain ⟨t₁, hqt₁, ht₁⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hq
  have hqt₁' : q < t₁ := by exact_mod_cast hqt₁
  obtain ⟨E₀, hE₀, hE₀c, -, WC, hWC, hWC0, hWCeq, ηC, hηC, hηCeq, hCf⟩ :=
    R6Fc.chart_factsInf (n := n) hCo hCH hψc hJ hω hγ ht₁
  obtain ⟨-, -, -, hOE, hOEc⟩ := hCf q hqt₁'
  have hq0' : (0 : ℝ) < q := by exact_mod_cast hq0
  have hWCq : ∀ s ∈ Icc (0 : ℝ) q, segDriver (travAllInf R L r η ψ ω) s.toNNReal = WC s := fun s hs =>
    hWCeq s ⟨hs.1, hs.2.trans (by exact_mod_cast hqt₁'.le)⟩
  have hvR : R6Fc.seedRInf R L r η ψ q ω = chartAR WC q := R6Fc.seedR_eq hWC hWCq
  -- the trace points of the outer chart
  have hcapq : capInv (travAllInf R L r η ψ ω) (q : ℝ) = u := by rw [← hcap]; exact hγ.capInv_eq hu0
  have htr : ∀ t ∈ Icc (0 : ℝ) q, ηC t = ψ ω (relTipInf R L r η (capInv (travAllInf R L r η ψ ω) t) ω) ∧
      0 ≤ capInv (travAllInf R L r η ψ ω) t ∧ capInv (travAllInf R L r η ψ ω) t ≤ u := fun t ht => by
    refine ⟨hηCeq t ht.1 (ht.2.trans (by exact_mod_cast hqt₁'.le)), ?_, hγ.capInv_le hu0 ht.1 (ht.2.trans hcap.ge)⟩
    refine (hγ.capInv_spec ht.1 (lt_of_le_of_lt (ENNReal.ofReal_le_ofReal ht.2) ?_)).1
    rwa [ENNReal.ofReal_coe_nnreal]
  have hηCq : ηC q = ψ ω (relTipInf R L r η u ω) := by rw [(htr q ⟨hq0'.le, le_rfl⟩).1, hcapq]
  have h0cl : ((0 : ℝ) : ℂ) ∈ closure H := by
    rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]; exact R6Fc.real_mem_Hbar 0
  have htipC : extendFrom H (fwdMapInv WC q) ((0 : ℝ) : ℂ) ∈ H := by
    have h1 := hηC.tendsto_fwdMapInv_tip hWC hWC0 q.coe_nonneg
    rw [← Complex.ofReal_zero] at h1
    rw [extendFrom_eq h0cl h1, hηCq]
    exact (hψc ω hω).2.mapsTo (hsub hrel)
  have hlt : chartAL WC q < chartAR WC q :=
    (R6Fc.chartAL_neg_of_tip hηC hWC hWC0 q.coe_nonneg htipC).trans
      (R6Fc.chartAR_pos_of_tip hηC hWC hWC0 q.coe_nonneg htipC)
  obtain ⟨hb, ⟨t₂, ht₂, ht₂im, ht₂le⟩, hall⟩ := landR_spec hηC hWC hWC0 hq0' hlt
  have hland : extendFrom H (R6Fc.curChartInf A R L r η ψ n q ω).2.1 (R6Fc.seedRInf R L r η ψ q ω : ℂ) =
      E₀ (extendFrom H (fwdMapInv WC q) (chartAR WC q : ℂ)) := by
    have hvcl : ((chartAR WC q : ℝ) : ℂ) ∈ closure H := by
      rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]; exact R6Fc.real_mem_Hbar _
    rw [hvR]
    exact extendFrom_eq hvcl (R6Fc.tendsto_of_extension hOE hOEc (chartAR WC q))
  -- the contained pocket
  have hC := hcf.conf
  have hC0 := hcf.seed
  have hor := hcf.oriented
  have hU := hcfg'.conf
  have hU0 := PocketMarks.zero_notMem_closure_of_rightLo_pos hU hcfg'.bounded
  obtain ⟨hPU, -⟩ := R5Ref.pocket_of_cfg (Ω := Ω) (R := fun _ => R') (L := fun _ => L ω) (W := W) (η := η)
    (ψ := fun _ => ψ') (ω := ω) hcfg' hψ'
  obtain ⟨-, -, -, ha', hb', hab', hLa', -⟩ := hU.changeCorner_props
  have ha0' := hU.leftLo_pos hU0
  have hP := hcf.erase
  have hL₀ := hP.clockEnd_pos
  set T := pocketFibreInf (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0))
    (clockOf (clockEnd (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0))) u) with hTdef
  have hT0 : 0 ≤ T := hP.fibre_nonneg (clockOf_mem_Ico hL₀ hu0)
  have hηT : η ω T = relTipInf R L r η u ω := rfl
  have hTσ := (hPU.mem_Ioo_of_mem hT0 (hηT ▸ hrel)).2
  have hxU : wallPt (L ω) (leftLo R' (L ω) r') ∉ η ω '' Icc 0 T := by
    intro hm
    apply hPU.fresh_x
    have he : cfArcR R' (L ω) r' 0 = wallPt (L ω) (leftLo R' (L ω) r') := by
      rw [cfArcR_zero]
      show cfPt _ = cfPt (WangWu.toDisc (Lemma71I.realPath (L ω)) (leftLo R' (L ω) r'))
      rw [hLa']
    obtain ⟨t, ht, hte⟩ := hm
    exact ⟨t, ⟨ht.1, ht.2.trans_lt hTσ⟩, hte.trans he.symm⟩
  -- the lower witness
  obtain ⟨v₁, hv₁, hv₁e⟩ := harc
  set θ₁ := leftLo R' (L ω) r' + v₁ * (leftHi R' (L ω) r' - leftLo R' (L ω) r') with hθ₁def
  have hθ₁ : θ₁ ∈ Ioo (leftLo R' (L ω) r') (leftHi R' (L ω) r') := (IsChangeConfigInc.affine_mem hab').2.1 hv₁
  have hθ₁e : relTipInf R L r η u₁ ω = wallPt (L ω) θ₁ := hv₁e.symm
  have hs₁ : capClock (travAllInf R L r η ψ ω) u₁ ∈ Icc (0 : ℝ) q := ⟨hγ.capClock_nonneg hu₁0, hcap₁⟩
  have hηC₁ : ηC (capClock (travAllInf R L r η ψ ω) u₁) = ψ ω (wallPt (L ω) θ₁) := by
    rw [(htr _ hs₁).1, hγ.capInv_eq hu₁0, hθ₁e]
  have hθ₁cl := wallPt_left_mem_closure hU hU0 hsub ⟨hθ₁.1.le, hθ₁.2.le⟩
  have hθ₁nC : wallPt (L ω) θ₁ ∉ cfPocket (R ω) (L ω) r :=
    wallPt_notMem hC (Or.inr rfl) ⟨ha'.1.trans_lt hθ₁.1, hθ₁.2.le.trans hb'.2⟩
  have hθ₁fr : wallPt (L ω) θ₁ ∈ frontier (cfPocket (R ω) (L ω) r) :=
    ⟨hθ₁cl, by rw [(hCo ω hω).interior_eq]; exact hθ₁nC⟩
  have hreal₁ : (ψ ω (wallPt (L ω) θ₁)).im = 0 := hJ.2.2.2.2.1 _ hθ₁fr
  have hb₁ : (ψ ω (wallPt (L ω) θ₁)).re ≤ (extendFrom H (fwdMapInv WC q) (chartAR WC q : ℂ)).re := by
    have := hall _ hs₁ (by rw [hηC₁]; exact hreal₁)
    rwa [hηC₁] at this
  have hθ₁CI : θ₁ ∈ Ioo (leftLo (R ω) (L ω) r) (leftHi (R ω) (L ω) r) := by
    have hIl := le_leftHi_of_mem_closureInf hC hC0 ⟨ha'.1.trans_lt hab', hb'.2⟩
      (wallPt_left_mem_closure hU hU0 hsub ⟨hab'.le, le_rfl⟩)
    rw [hC.leftLo_eq_zero_of_rightLo_eq_zero hC0]
    exact ⟨ha'.1.trans_lt hθ₁.1, hθ₁.2.trans_le hIl⟩
  have hpos₁ : 0 < (ψ ω (wallPt (L ω) θ₁)).re := (SideAnc.jordanInf_sides hC hC0 hor hJ).2 θ₁ hθ₁CI
  -- the upper witness
  obtain ⟨hcI₂, hcI₂0, hcI₂u⟩ := htr t₂ ht₂
  set p₂ := relTipInf R L r η (capInv (travAllInf R L r η ψ ω) t₂) ω with hp₂def
  have hf₂ := relTip_factsInf hcf hcI₂0 hcI₂u
  have hp₂re : (ψ ω p₂).im = 0 := by rw [← hcI₂]; exact ht₂im
  have hp₂fr : p₂ ∈ frontier (cfPocket (R ω) (L ω) r) := by
    refine ⟨hf₂.1, fun hin => ?_⟩
    rw [(hCo ω hω).interior_eq] at hin
    have := (hψc ω hω).2.mapsTo hin
    exact (ne_of_gt (show (0 : ℝ) < (ψ ω p₂).im from this)) hp₂re
  have hb₂ : (extendFrom H (fwdMapInv WC q) (chartAR WC q : ℂ)).re ≤ (ψ ω p₂).re := by rw [← hcI₂]; exact ht₂le
  have hCc := hC.isCfPocketInf hC0
  obtain ⟨hu, hv, huv, ha, hbC, hab, hLa, hLb⟩ := hC.changeCorner_props
  have hhiR : 0 < rightHi (R ω) (L ω) r := hC0 ▸ huv
  have hhiL : 0 < leftHi (R ω) (L ω) r := (hC.leftLo_eq_zero_of_rightLo_eq_zero hC0) ▸ hab
  rw [hCc.frontier_eq] at hp₂fr
  rcases hp₂fr with ⟨w, hw, hwe⟩ | ⟨w, hw, hwe⟩
  · -- a right-wall point has a nonpositive coordinate
    exfalso
    have hsI := div_one_add_mem hhiR hw
    obtain ⟨-, -, hmono⟩ := right_arc_factsInf hC hC0 hor hJ
    have hle := hmono.monotoneOn hsI ⟨hhiR, le_rfl⟩ hsI.2
    have h0 : (ψ ω (wallPt (R ω) (rightHi (R ω) (L ω) r))).re = 0 := by
      have : wallPt (R ω) (rightHi (R ω) (L ω) r) = cfPt (closePt (R ω) (L ω) r) := rfl
      rw [this, hJ.2.2.2.2.2.1]; rfl
    have hp₂R : ψ ω p₂ = ψ ω (wallPt (R ω) (rightHi (R ω) (L ω) r / (1 + w))) := by rw [← hwe]; rfl
    have : (ψ ω p₂).re ≤ 0 := by rw [hp₂R]; exact hle.trans h0.le
    linarith
  · set θ₂ := leftHi (R ω) (L ω) r / (1 + w) with hθ₂def
    have hθ₂I := div_one_add_mem hhiL hw
    have hθ₂01 : θ₂ ∈ Ioc (0 : ℝ) 1 := ⟨hθ₂I.1, hθ₂I.2.trans hbC.2⟩
    have hp₂e : p₂ = wallPt (L ω) θ₂ := hwe.symm
    have hθ₂U : leftLo R' (L ω) r' < θ₂ := by
      by_contra hle
      push Not at hle
      apply hxU
      refine PocketJordan.wall_rev hcfg'.conf.left hcfg'.trace.1 hcfg'.revL hθ₂01 ⟨ha0', ha'.2⟩ hle ?_
      show wallPt (L ω) θ₂ ∈ _
      rw [← hp₂e]
      exact hf₂.2
    obtain ⟨θ, hθ, -, hψθ⟩ := exists_left_param_of_betweenInf hC hC0 hor hJ hU hU0 hsub hθ₁ hb₁
      ⟨hθ₂U, hθ₂01.2⟩ (hp₂e ▸ hf₂.1) (hp₂e ▸ hb₂)
    have hpF : extendFrom H (R6Fc.curChartInf A R L r η ψ n q ω).2.1 (R6Fc.seedRInf R L r η ψ q ω : ℂ) =
        wallPt (L ω) θ := by
      rw [hland, hb, ← hψθ]
      exact extension_psi_eqInf hJ hE₀ hE₀c (wallPt_left_mem_closure hU hU0 hsub ⟨hθ.1.le, hθ.2.le⟩)
    obtain ⟨h1, h2, h3⟩ := nonCorner_of_left_open hC hU hU0 hθ
    exact ⟨hpF ▸ h1, hpF ▸ h2, hpF ▸ h3⟩

/-- **The non-corner landing of the left seed coordinate** (shared wall `R`, outer pocket opening at the flow seed,
bounded `U`; one realization). -/
theorem nonCornerLandingInf_right {A : Set Ω} {R L : Ω → ℝ≥0 → ℂ} {L' : ℝ≥0 → ℂ} {r r' : ℝ≥0} {W : Ω → ℝ → ℝ}
    {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {ψ' : ℂ → ℂ} {n : Ω → ℤ} {ω : Ω}
    (hcfg : ∀ ω ∈ A, IsOuterCfgInf (R ω) (L ω) r (W ω) (η ω)) (hψ : ∀ ω ∈ A, IsCfJordanInf (R ω) (L ω) r (ψ ω))
    (hω : ω ∈ A) (hcfg' : IsCfPocketConfig (R ω) L' r' (W ω) (η ω)) (hψ' : IsCfJordan (R ω) L' r' ψ')
    {q : ℝ≥0} (hq0 : 0 < q) (hq : (q : ℝ≥0∞) < capLife (travAllInf R L r η ψ ω))
    (hsub : cfPocket (R ω) L' r' ⊆ cfPocket (R ω) (L ω) r)
    {u : ℝ} (hu0 : 0 ≤ u) (hcap : capClock (travAllInf R L r η ψ ω) u = q)
    (hrel : relTipInf R L r η u ω ∈ cfPocket (R ω) L' r')
    {u₁ : ℝ} (hu₁0 : 0 ≤ u₁) (hcap₁ : capClock (travAllInf R L r η ψ ω) u₁ ≤ q)
    (harc : relTipInf R L r η u₁ ω ∈ cfArcR (R ω) L' r' '' Ioo 0 1) :
    R6Fc.IsNonCornerLanding (R6Fc.curChartInf A R L r η ψ n q ω) (R6Fc.seedLInf R L r η ψ q ω)
      (cfPocket (R ω) L' r') (cfPocket (R ω) (L ω) r) (cfPt (openPt (R ω) L' r')) := by
  classical
  have hcf := hcfg ω hω
  have hG : ∀ ω ∈ A, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  have hCo : ∀ ω ∈ A, IsOpen (cfPocket (R ω) (L ω) r) := fun ω hω =>
    isOpen_image_negInv' (hG ω hω).isOpen_changePocket (hG ω hω).changePocket_subset_H
  have hCH : ∀ ω ∈ A, cfPocket (R ω) (L ω) r ⊆ H := fun ω hω =>
    PocketJordan.image_negInv_subset_H (hG ω hω).changePocket_subset_H
  have hψc : ∀ ω ∈ A, IsConformalBijection (ψ ω) (cfPocket (R ω) (L ω) r) H := fun ω hω => (hψ ω hω).2.2.2.1
  have hJ := hψ ω hω
  have hγ : IsDrivenCurve (travAllInf R L r η ψ ω) := (hcf.props hJ).1
  obtain ⟨t₁, hqt₁, ht₁⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hq
  have hqt₁' : q < t₁ := by exact_mod_cast hqt₁
  obtain ⟨E₀, hE₀, hE₀c, -, WC, hWC, hWC0, hWCeq, ηC, hηC, hηCeq, hCf⟩ :=
    R6Fc.chart_factsInf (n := n) hCo hCH hψc hJ hω hγ ht₁
  obtain ⟨-, -, -, hOE, hOEc⟩ := hCf q hqt₁'
  have hq0' : (0 : ℝ) < q := by exact_mod_cast hq0
  have hWCq : ∀ s ∈ Icc (0 : ℝ) q, segDriver (travAllInf R L r η ψ ω) s.toNNReal = WC s := fun s hs =>
    hWCeq s ⟨hs.1, hs.2.trans (by exact_mod_cast hqt₁'.le)⟩
  have hvL : R6Fc.seedLInf R L r η ψ q ω = chartAL WC q := R6Fc.seedL_eq hWC hWCq
  have hcapq : capInv (travAllInf R L r η ψ ω) (q : ℝ) = u := by rw [← hcap]; exact hγ.capInv_eq hu0
  have htr : ∀ t ∈ Icc (0 : ℝ) q, ηC t = ψ ω (relTipInf R L r η (capInv (travAllInf R L r η ψ ω) t) ω) ∧
      0 ≤ capInv (travAllInf R L r η ψ ω) t ∧ capInv (travAllInf R L r η ψ ω) t ≤ u := fun t ht => by
    refine ⟨hηCeq t ht.1 (ht.2.trans (by exact_mod_cast hqt₁'.le)), ?_, hγ.capInv_le hu0 ht.1 (ht.2.trans hcap.ge)⟩
    refine (hγ.capInv_spec ht.1 (lt_of_le_of_lt (ENNReal.ofReal_le_ofReal ht.2) ?_)).1
    rwa [ENNReal.ofReal_coe_nnreal]
  have hηCq : ηC q = ψ ω (relTipInf R L r η u ω) := by rw [(htr q ⟨hq0'.le, le_rfl⟩).1, hcapq]
  have h0cl : ((0 : ℝ) : ℂ) ∈ closure H := by
    rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]; exact R6Fc.real_mem_Hbar 0
  have htipC : extendFrom H (fwdMapInv WC q) ((0 : ℝ) : ℂ) ∈ H := by
    have h1 := hηC.tendsto_fwdMapInv_tip hWC hWC0 q.coe_nonneg
    rw [← Complex.ofReal_zero] at h1
    rw [extendFrom_eq h0cl h1, hηCq]
    exact (hψc ω hω).2.mapsTo (hsub hrel)
  have hlt : chartAL WC q < chartAR WC q :=
    (R6Fc.chartAL_neg_of_tip hηC hWC hWC0 q.coe_nonneg htipC).trans
      (R6Fc.chartAR_pos_of_tip hηC hWC hWC0 q.coe_nonneg htipC)
  obtain ⟨hb, ⟨t₂, ht₂, ht₂im, ht₂le⟩, hall⟩ := landL_spec hηC hWC hWC0 hq0' hlt
  have hland : extendFrom H (R6Fc.curChartInf A R L r η ψ n q ω).2.1 (R6Fc.seedLInf R L r η ψ q ω : ℂ) =
      E₀ (extendFrom H (fwdMapInv WC q) (chartAL WC q : ℂ)) := by
    have hvcl : ((chartAL WC q : ℝ) : ℂ) ∈ closure H := by
      rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]; exact R6Fc.real_mem_Hbar _
    rw [hvL]
    exact extendFrom_eq hvcl (R6Fc.tendsto_of_extension hOE hOEc (chartAL WC q))
  have hC := hcf.conf
  have hC0 := hcf.seed
  have hor := hcf.oriented
  have hU := hcfg'.conf
  have hU0 := PocketMarks.zero_notMem_closure_of_rightLo_pos hU hcfg'.bounded
  obtain ⟨hPU, -⟩ := R5Ref.pocket_of_cfg (Ω := Ω) (R := fun _ => R ω) (L := fun _ => L') (W := W) (η := η)
    (ψ := fun _ => ψ') (ω := ω) hcfg' hψ'
  obtain ⟨hu', hv', huv', -, -, -, -, -⟩ := hU.changeCorner_props
  have hu0' := hU.rightLo_pos hU0
  have hP := hcf.erase
  have hL₀ := hP.clockEnd_pos
  set T := pocketFibreInf (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0))
    (clockOf (clockEnd (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcRInf (R ω) (L ω) r 0))) u) with hTdef
  have hT0 : 0 ≤ T := hP.fibre_nonneg (clockOf_mem_Ico hL₀ hu0)
  have hηT : η ω T = relTipInf R L r η u ω := rfl
  have hTσ := (hPU.mem_Ioo_of_mem hT0 (hηT ▸ hrel)).2
  have hxU : wallPt (R ω) (rightLo (R ω) L' r') ∉ η ω '' Icc 0 T := by
    intro hm
    apply hPU.fresh_x
    have he : cfArcR (R ω) L' r' 0 = wallPt (R ω) (rightLo (R ω) L' r') := by rw [cfArcR_zero]; rfl
    obtain ⟨t, ht, hte⟩ := hm
    exact ⟨t, ⟨ht.1, ht.2.trans_lt hTσ⟩, hte.trans he.symm⟩
  obtain ⟨v₁, hv₁, hv₁e⟩ := harc
  set s₁ := rightLo (R ω) L' r' + v₁ * (rightHi (R ω) L' r' - rightLo (R ω) L' r') with hs₁def
  have hs₁ : s₁ ∈ Ioo (rightLo (R ω) L' r') (rightHi (R ω) L' r') := (IsChangeConfigInc.affine_mem huv').2.1 hv₁
  have hs₁e : relTipInf R L r η u₁ ω = wallPt (R ω) s₁ := hv₁e.symm
  have hc₁ : capClock (travAllInf R L r η ψ ω) u₁ ∈ Icc (0 : ℝ) q := ⟨hγ.capClock_nonneg hu₁0, hcap₁⟩
  have hηC₁ : ηC (capClock (travAllInf R L r η ψ ω) u₁) = ψ ω (wallPt (R ω) s₁) := by
    rw [(htr _ hc₁).1, hγ.capInv_eq hu₁0, hs₁e]
  have hs₁cl := wallPt_right_mem_closure hU hU0 hsub ⟨hs₁.1.le, hs₁.2.le⟩
  have hs₁nC : wallPt (R ω) s₁ ∉ cfPocket (R ω) (L ω) r :=
    wallPt_notMem hC (Or.inl rfl) ⟨hu'.1.trans_lt hs₁.1, hs₁.2.le.trans hv'.2⟩
  have hs₁fr : wallPt (R ω) s₁ ∈ frontier (cfPocket (R ω) (L ω) r) :=
    ⟨hs₁cl, by rw [(hCo ω hω).interior_eq]; exact hs₁nC⟩
  have hreal₁ : (ψ ω (wallPt (R ω) s₁)).im = 0 := hJ.2.2.2.2.1 _ hs₁fr
  have hb₁ : (extendFrom H (fwdMapInv WC q) (chartAL WC q : ℂ)).re ≤ (ψ ω (wallPt (R ω) s₁)).re := by
    have := hall _ hc₁ (by rw [hηC₁]; exact hreal₁)
    rwa [hηC₁] at this
  have hs₁CI : s₁ ∈ Ioo (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r) := by
    have hIl := le_rightHi_of_mem_closureInf hC hC0 ⟨hu'.1.trans_lt huv', hv'.2⟩
      (wallPt_right_mem_closure hU hU0 hsub ⟨huv'.le, le_rfl⟩)
    rw [hC0]
    exact ⟨hu'.1.trans_lt hs₁.1, hs₁.2.trans_le hIl⟩
  have hneg₁ : (ψ ω (wallPt (R ω) s₁)).re < 0 := (SideAnc.jordanInf_sides hC hC0 hor hJ).1 s₁ hs₁CI
  obtain ⟨hcI₂, hcI₂0, hcI₂u⟩ := htr t₂ ht₂
  set p₂ := relTipInf R L r η (capInv (travAllInf R L r η ψ ω) t₂) ω with hp₂def
  have hf₂ := relTip_factsInf hcf hcI₂0 hcI₂u
  have hp₂re : (ψ ω p₂).im = 0 := by rw [← hcI₂]; exact ht₂im
  have hp₂fr : p₂ ∈ frontier (cfPocket (R ω) (L ω) r) := by
    refine ⟨hf₂.1, fun hin => ?_⟩
    rw [(hCo ω hω).interior_eq] at hin
    have := (hψc ω hω).2.mapsTo hin
    exact (ne_of_gt (show (0 : ℝ) < (ψ ω p₂).im from this)) hp₂re
  have hb₂ : (ψ ω p₂).re ≤ (extendFrom H (fwdMapInv WC q) (chartAL WC q : ℂ)).re := by rw [← hcI₂]; exact ht₂le
  have hCc := hC.isCfPocketInf hC0
  obtain ⟨hu, hv, huv, ha, hbC, hab, hLa, hLb⟩ := hC.changeCorner_props
  have hhiR : 0 < rightHi (R ω) (L ω) r := hC0 ▸ huv
  have hhiL : 0 < leftHi (R ω) (L ω) r := (hC.leftLo_eq_zero_of_rightLo_eq_zero hC0) ▸ hab
  rw [hCc.frontier_eq] at hp₂fr
  rcases hp₂fr with ⟨w, hw, hwe⟩ | ⟨w, hw, hwe⟩
  · set s₂ := rightHi (R ω) (L ω) r / (1 + w) with hs₂def
    have hs₂I := div_one_add_mem hhiR hw
    have hs₂01 : s₂ ∈ Ioc (0 : ℝ) 1 := ⟨hs₂I.1, hs₂I.2.trans hv.2⟩
    have hp₂e : p₂ = wallPt (R ω) s₂ := hwe.symm
    have hs₂U : rightLo (R ω) L' r' < s₂ := by
      by_contra hle
      push Not at hle
      apply hxU
      refine PocketJordan.wall_rev hcfg'.conf.right hcfg'.trace.1 hcfg'.revR hs₂01 ⟨hu0', hu'.2⟩ hle ?_
      show wallPt (R ω) s₂ ∈ _
      rw [← hp₂e]
      exact hf₂.2
    obtain ⟨s, hs, -, hψs⟩ := exists_right_param_of_betweenInf hC hC0 hor hJ hU hU0 hsub hs₁ hb₁
      ⟨hs₂U, hs₂01.2⟩ (hp₂e ▸ hf₂.1) (hp₂e ▸ hb₂)
    have hpF : extendFrom H (R6Fc.curChartInf A R L r η ψ n q ω).2.1 (R6Fc.seedLInf R L r η ψ q ω : ℂ) =
        wallPt (R ω) s := by
      rw [hland, hb, ← hψs]
      exact extension_psi_eqInf hJ hE₀ hE₀c (wallPt_right_mem_closure hU hU0 hsub ⟨hs.1.le, hs.2.le⟩)
    obtain ⟨h1, h2, h3⟩ := nonCorner_of_right_open hC hU hU0 hs
    exact ⟨hpF ▸ h1, hpF ▸ h2, hpF ▸ h3⟩
  · exfalso
    have hθI := div_one_add_mem hhiL hw
    obtain ⟨-, -, hanti⟩ := left_arc_factsInf hC hC0 hor hJ
    have hge := hanti.antitoneOn hθI ⟨hhiL, le_rfl⟩ hθI.2
    have h0 : (ψ ω (wallPt (L ω) (leftHi (R ω) (L ω) r))).re = 0 := by
      have : wallPt (L ω) (leftHi (R ω) (L ω) r) = cfPt (closePt (R ω) (L ω) r) := by
        show cfPt (WangWu.toDisc _ _) = cfPt _; rw [hLb]
      rw [this, hJ.2.2.2.2.2.1]; rfl
    have hp₂L : ψ ω p₂ = ψ ω (wallPt (L ω) (leftHi (R ω) (L ω) r / (1 + w))) := by rw [← hwe]; rfl
    have : 0 ≤ (ψ ω p₂).re := by rw [hp₂L]; exact h0.ge.trans hge
    linarith

end InteractingSLE.Sec7.R6Fd
