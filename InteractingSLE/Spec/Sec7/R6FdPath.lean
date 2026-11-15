/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6FdArc
import InteractingSLE.Spec.Sec7.R6FcWire

/-!
# The non-corner landing of the shared seed coordinate, one realization

Packet PROVE-R6-FACE3. One realization of the bounded mixed shape: the outer pocket `C = cfPocket R L r`
(`IsOuterCfg`, Jordan coordinate `ψ`) at a live relative capacity `q > 0` whose relative tip lies in the contained
bounded pocket `U ⊆ C` (`IsCfPocketConfig`) sharing one wall with `C`. Assume that **the relative trace of `C` has
visited `U`'s open shared arc by the relative time `q`** (the corner exclusion). Then the physical landing `p_F` of
the outer current chart at the shared seed coordinate is a point of `U`'s open shared arc, hence a non-corner point
of `∂U` (`R6Fc.IsNonCornerLanding`):

1. (F1) `F̄_q(a_R)` is the largest real point `b` of the relative trace (`R6FdLand.landR_spec`), so
   `p_F = E₀(b)` (`extension_psi_eq`);
2. `b` is at least the coordinate of the visited point of `U`'s open shared arc, and at most the coordinate of
   some visited real trace point, which lies on the shared wall strictly beyond `U`'s outgoing corner `x₀ᵁ`:
   `x₀ᵁ` is unvisited before `U`'s exit time (`fresh_x`) and the shared wall is visited in reverse order (`U`'s own
   `revL`/`revR`, (F0)); a point on the other wall has a coordinate of the wrong sign;
3. the coordinate is monotone along the shared wall, so `b` is the coordinate of a point of `U`'s open shared arc
   (`exists_left_param_of_between`), a non-corner point (`nonCorner_of_left_open`).

`nonCornerLanding_left` (shared wall `L`, right seed) and `nonCornerLanding_right` (shared wall `R`, left seed).
Deterministic.
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
  PocketWordAssembly R6Safe R6Nest
open WangWu (chartAL chartAR)

variable {Ω : Type*}

/-- **The relative tip at an earlier relative time**: in `closure C ∖ {x₀}` and visited by the fibre end at the later
time. -/
theorem relTip_facts {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {W : ℝ → ℝ} {η : Ω → ℝ → ℂ} {ω : Ω}
    (hcf : IsOuterCfg (R ω) (L ω) r W (η ω)) {u' u : ℝ} (hu' : 0 ≤ u') (huu : u' ≤ u) :
    relTip R L r η u' ω ∈ closure (cfPocket (R ω) (L ω) r) \ {cfArcR (R ω) (L ω) r 0} ∧
      relTip R L r η u' ω ∈ η ω '' Icc 0 (pocketFibre (η ω) (cfPocket (R ω) (L ω) r)
        (firstHit (η ω) (cfArcR (R ω) (L ω) r 1)) (firstHit (η ω) (cfArcR (R ω) (L ω) r 0))
        (clockOf (pocketClock (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
          (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) (firstHit (η ω) (cfArcR (R ω) (L ω) r 0))) u)) := by
  have hP := hcf.erase
  have hL₀ := hP.clock_σ_pos
  refine ⟨hP.erasedPath_mem (clockOf_mem_Ico hL₀ hu'), _, ⟨hP.nonneg.trans (hP.fibre_mem _).1, ?_⟩, rfl⟩
  exact hP.monotone_fibre ((strictMonoOn_clockOf hL₀).monotoneOn (mem_Ici.2 hu') (mem_Ici.2 (hu'.trans huu)) huu)

/-- The outgoing corner of a change pocket is the start of its right arc. -/
theorem cfArcR_zero (R L : ℝ≥0 → ℂ) (r : ℝ≥0) : cfArcR R L r 0 = cfPt (openPt R L r) := by
  simp only [cfArcR, zero_mul, add_zero]
  rfl

/-- **The non-corner landing of the right seed coordinate** (shared wall `L`; one realization): if the relative trace
of the outer pocket has visited the open left arc of the contained pocket `U = cfPocket R' (L ω) r'` by the relative
time `q` at which its tip is in `U`, then the outer current chart lands at the right seed coordinate at a non-corner
point of `∂U`. -/
theorem nonCornerLanding_left {A : Set Ω} {R L : Ω → ℝ≥0 → ℂ} {R' : ℝ≥0 → ℂ} {r r' : ℝ≥0} {W : Ω → ℝ → ℝ}
    {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {ψ' : ℂ → ℂ} {n : Ω → ℤ} {ω : Ω}
    (hcfg : ∀ ω ∈ A, IsOuterCfg (R ω) (L ω) r (W ω) (η ω)) (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω))
    (hω : ω ∈ A) (hcfg' : IsCfPocketConfig R' (L ω) r' (W ω) (η ω)) (hψ' : IsCfJordan R' (L ω) r' ψ')
    {q : ℝ≥0} (hq0 : 0 < q) (hq : (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω))
    (hsub : cfPocket R' (L ω) r' ⊆ cfPocket (R ω) (L ω) r)
    {u : ℝ} (hu0 : 0 ≤ u) (hcap : capClock (travAll R L r η ψ ω) u = q)
    (hrel : relTip R L r η u ω ∈ cfPocket R' (L ω) r')
    {u₁ : ℝ} (hu₁0 : 0 ≤ u₁) (hcap₁ : capClock (travAll R L r η ψ ω) u₁ ≤ q)
    (harc : relTip R L r η u₁ ω ∈ cfArcL R' (L ω) r' '' Ioo 0 1) :
    R6Fc.IsNonCornerLanding (R6Fc.curChart A R L r η ψ n q ω) (R6Fc.seedR R L r η ψ q ω)
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
  have hC0 := PocketMarks.zero_notMem_closure_of_rightLo_pos hcf.conf hcf.bounded
  have hCb : Bornology.IsBounded (cfPocket (R ω) (L ω) r) := isBounded_image_negInv hC0
  have hx₀ : cfPt (openPt (R ω) (L ω) r) ∉ cfPocket (R ω) (L ω) r := hcf.conf.cfPt_openPt_notMem
  have hJ := hψ ω hω
  have hγ : IsDrivenCurve (travAll R L r η ψ ω) := (hcf.props hJ).1
  obtain ⟨t₁, hqt₁, ht₁⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hq
  have hqt₁' : q < t₁ := by exact_mod_cast hqt₁
  obtain ⟨E₀, hE₀, hE₀c, -, WC, hWC, hWC0, hWCeq, ηC, hηC, hηCeq, hCf⟩ :=
    R6Fc.chart_facts (n := n) hCo hCH hψc hCb hx₀ hJ hω hγ ht₁
  obtain ⟨-, -, -, hOE, hOEc⟩ := hCf q hqt₁'
  have hq0' : (0 : ℝ) < q := by exact_mod_cast hq0
  have hWCq : ∀ s ∈ Icc (0 : ℝ) q, segDriver (travAll R L r η ψ ω) s.toNNReal = WC s := fun s hs =>
    hWCeq s ⟨hs.1, hs.2.trans (by exact_mod_cast hqt₁'.le)⟩
  have hvR : R6Fc.seedR R L r η ψ q ω = chartAR WC q := R6Fc.seedR_eq hWC hWCq
  -- the trace points of the outer chart
  have hcapq : capInv (travAll R L r η ψ ω) (q : ℝ) = u := by rw [← hcap]; exact hγ.capInv_eq hu0
  have htr : ∀ t ∈ Icc (0 : ℝ) q, ηC t = ψ ω (relTip R L r η (capInv (travAll R L r η ψ ω) t) ω) ∧
      0 ≤ capInv (travAll R L r η ψ ω) t ∧ capInv (travAll R L r η ψ ω) t ≤ u := fun t ht => by
    refine ⟨hηCeq t ht.1 (ht.2.trans (by exact_mod_cast hqt₁'.le)), ?_, hγ.capInv_le hu0 ht.1 (ht.2.trans hcap.ge)⟩
    refine (hγ.capInv_spec ht.1 (lt_of_le_of_lt (ENNReal.ofReal_le_ofReal ht.2) ?_)).1
    rwa [ENNReal.ofReal_coe_nnreal]
  have hηCq : ηC q = ψ ω (relTip R L r η u ω) := by rw [(htr q ⟨hq0'.le, le_rfl⟩).1, hcapq]
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
  -- the landing is `E₀(b)`
  have hland : extendFrom H (R6Fc.curChart A R L r η ψ n q ω).2.1 (R6Fc.seedR R L r η ψ q ω : ℂ) =
      E₀ (extendFrom H (fwdMapInv WC q) (chartAR WC q : ℂ)) := by
    have hvcl : ((chartAR WC q : ℝ) : ℂ) ∈ closure H := by
      rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]; exact R6Fc.real_mem_Hbar _
    rw [hvR]
    exact extendFrom_eq hvcl (R6Fc.tendsto_of_extension hOE hOEc (chartAR WC q))
  -- the contained pocket
  have hC := hcf.conf
  have hor := hcf.oriented
  have hU := hcfg'.conf
  have hU0 := PocketMarks.zero_notMem_closure_of_rightLo_pos hU hcfg'.bounded
  obtain ⟨hPU, -⟩ := R5Ref.pocket_of_cfg (Ω := Ω) (R := fun _ => R') (L := fun _ => L ω) (W := W) (η := η)
    (ψ := fun _ => ψ') (ω := ω) hcfg' hψ'
  obtain ⟨-, -, -, ha', hb', hab', hLa', -⟩ := hU.changeCorner_props
  have ha0' := hU.leftLo_pos hU0
  set T := pocketFibre (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
    (firstHit (η ω) (cfArcR (R ω) (L ω) r 0))
    (clockOf (pocketClock (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
      (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) (firstHit (η ω) (cfArcR (R ω) (L ω) r 0))) u) with hTdef
  have hT0 : 0 ≤ T := hcf.erase.nonneg.trans (hcf.erase.fibre_mem _).1
  have hηT : η ω T = relTip R L r η u ω := rfl
  have hTσ := (hPU.mem_Ioo_of_mem hT0 (hηT ▸ hrel)).2
  -- `x₀ᵁ` is not visited by `T`
  have hxU : wallPt (L ω) (leftLo R' (L ω) r') ∉ η ω '' Icc 0 T := by
    intro hm
    apply hPU.fresh_x
    have he : cfArcR R' (L ω) r' 0 = wallPt (L ω) (leftLo R' (L ω) r') := by
      rw [cfArcR_zero]
      show cfPt _ = cfPt (WangWu.toDisc (Lemma71I.realPath (L ω)) (leftLo R' (L ω) r'))
      rw [hLa']
    obtain ⟨t, ht, hte⟩ := hm
    exact ⟨t, ⟨ht.1, ht.2.trans_lt hTσ⟩, hte.trans he.symm⟩
  -- the lower witness: a point of `U`'s open shared arc on the trace
  obtain ⟨v₁, hv₁, hv₁e⟩ := harc
  set θ₁ := leftLo R' (L ω) r' + v₁ * (leftHi R' (L ω) r' - leftLo R' (L ω) r') with hθ₁def
  have hθ₁ : θ₁ ∈ Ioo (leftLo R' (L ω) r') (leftHi R' (L ω) r') := (IsChangeConfigInc.affine_mem hab').2.1 hv₁
  have hθ₁e : relTip R L r η u₁ ω = wallPt (L ω) θ₁ := hv₁e.symm
  have hf₁ := relTip_facts hcf hu₁0 (by
    by_contra hlt'
    push Not at hlt'
    have := hγ.strictMonoOn_capClock (mem_Ici.2 hu0) (mem_Ici.2 hu₁0) hlt'
    linarith)
  have h₁x : wallPt (L ω) θ₁ ≠ cfPt (openPt (R ω) (L ω) r) := by
    rw [← hθ₁e, ← cfArcR_zero]; exact hf₁.1.2
  have hs₁ : capClock (travAll R L r η ψ ω) u₁ ∈ Icc (0 : ℝ) q := ⟨hγ.capClock_nonneg hu₁0, hcap₁⟩
  have hηC₁ : ηC (capClock (travAll R L r η ψ ω) u₁) = ψ ω (wallPt (L ω) θ₁) := by
    rw [(htr _ hs₁).1, hγ.capInv_eq hu₁0, hθ₁e]
  have hθ₁C : wallPt (L ω) θ₁ ∈ closure (cfPocket (R ω) (L ω) r) \ {cfPt (openPt (R ω) (L ω) r)} :=
    ⟨wallPt_left_mem_closure hU hU0 hsub ⟨hθ₁.1.le, hθ₁.2.le⟩, h₁x⟩
  have hθ₁nC : wallPt (L ω) θ₁ ∉ cfPocket (R ω) (L ω) r :=
    wallPt_notMem hC (Or.inr rfl) ⟨ha'.1.trans_lt hθ₁.1, hθ₁.2.le.trans hb'.2⟩
  have hθ₁fr : wallPt (L ω) θ₁ ∈ frontier (cfPocket (R ω) (L ω) r) \ {cfPt (openPt (R ω) (L ω) r)} :=
    ⟨⟨hθ₁C.1, by rw [(hCo ω hω).interior_eq]; exact hθ₁nC⟩, hθ₁C.2⟩
  have hreal₁ : (ψ ω (wallPt (L ω) θ₁)).im = 0 := hJ.2.2.2.2.1 _ hθ₁fr
  have hb₁ : (ψ ω (wallPt (L ω) θ₁)).re ≤ (extendFrom H (fwdMapInv WC q) (chartAR WC q : ℂ)).re := by
    have := hall _ hs₁ (by rw [hηC₁]; exact hreal₁)
    rwa [hηC₁] at this
  -- the coordinate of the lower witness is positive
  have hθ₁CI : θ₁ ∈ Ioo (leftLo (R ω) (L ω) r) (leftHi (R ω) (L ω) r) := by
    have hIl := mem_Icc_left_of_mem_closure hC hC0 ⟨ha'.1.trans_lt hθ₁.1, hθ₁.2.le.trans hb'.2⟩ hθ₁C.1
    have hIh := mem_Icc_left_of_mem_closure hC hC0 ⟨ha'.1.trans_lt hab', hb'.2⟩
      (wallPt_left_mem_closure hU hU0 hsub ⟨hab'.le, le_rfl⟩)
    obtain ⟨-, -, -, -, -, -, hLa, -⟩ := hC.changeCorner_props
    refine ⟨lt_of_le_of_ne hIl.1 fun he => h₁x ?_, hθ₁.2.trans_le hIh.2⟩
    show cfPt (WangWu.toDisc (Lemma71I.realPath (L ω)) θ₁) = _
    rw [← he, hLa]
  have hpos₁ : 0 < (ψ ω (wallPt (L ω) θ₁)).re := (SideAnc.jordan_sides hC hC0 hor hJ).2 θ₁ hθ₁CI
  -- the upper witness: a visited real trace point on the shared wall beyond `x₀ᵁ`
  obtain ⟨hcI₂, hcI₂0, hcI₂u⟩ := htr t₂ ht₂
  set p₂ := relTip R L r η (capInv (travAll R L r η ψ ω) t₂) ω with hp₂def
  have hf₂ := relTip_facts hcf hcI₂0 hcI₂u
  have hp₂re : (ψ ω p₂).im = 0 := by rw [← hcI₂]; exact ht₂im
  have hp₂fr : p₂ ∈ frontier (cfPocket (R ω) (L ω) r) := by
    refine ⟨hf₂.1.1, fun hin => ?_⟩
    rw [(hCo ω hω).interior_eq] at hin
    have := (hψc ω hω).2.mapsTo hin
    exact (ne_of_gt (show (0 : ℝ) < (ψ ω p₂).im from this)) hp₂re
  have hb₂ : (extendFrom H (fwdMapInv WC q) (chartAR WC q : ℂ)).re ≤ (ψ ω p₂).re := by rw [← hcI₂]; exact ht₂le
  have hCc := hC.isCfPocket hC0
  obtain ⟨hu, hv, huv, ha, hbC, hab, hLa, hLb⟩ := hC.changeCorner_props
  have hp₂x : p₂ ≠ cfPt (openPt (R ω) (L ω) r) := by rw [← cfArcR_zero]; exact hf₂.1.2
  rw [hCc.frontier_eq] at hp₂fr
  rcases hp₂fr with ⟨w, hw, hwe⟩ | ⟨w, hw, hwe⟩
  · -- a right-wall point has a nonpositive coordinate
    exfalso
    have hsI := (IsChangeConfigInc.affine_mem huv).1 hw
    have hsI' : rightLo (R ω) (L ω) r + w * (rightHi (R ω) (L ω) r - rightLo (R ω) (L ω) r) ∈
        Ioc (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r) := by
      refine ⟨lt_of_le_of_ne hsI.1 fun he => hp₂x ?_, hsI.2⟩
      rw [← hwe]
      show cfPt (WangWu.toDisc _ _) = cfPt (WangWu.toDisc _ _)
      rw [← he]
    obtain ⟨-, -, hmono⟩ := right_arc_facts hC hC0 hor hJ
    have hhi := (right_arc_facts hC hC0 hor hJ).1 _ ⟨huv, le_rfl⟩
    have hle := hmono.monotoneOn hsI' ⟨huv, le_rfl⟩ hsI'.2
    have h0 : (ψ ω (wallPt (R ω) (rightHi (R ω) (L ω) r))).re = 0 := by
      have : wallPt (R ω) (rightHi (R ω) (L ω) r) = cfPt (closePt (R ω) (L ω) r) := rfl
      rw [this, hJ.2.2.2.2.2.1]; rfl
    have hp₂R : ψ ω p₂ = ψ ω (wallPt (R ω)
        (rightLo (R ω) (L ω) r + w * (rightHi (R ω) (L ω) r - rightLo (R ω) (L ω) r))) := by rw [← hwe]; rfl
    have : (ψ ω p₂).re ≤ 0 := by rw [hp₂R]; exact hle.trans h0.le
    linarith
  · set θ₂ := leftLo (R ω) (L ω) r + w * (leftHi (R ω) (L ω) r - leftLo (R ω) (L ω) r) with hθ₂def
    have hθ₂I := (IsChangeConfigInc.affine_mem hab).1 hw
    have ha0 := hC.leftLo_pos hC0
    have hθ₂01 : θ₂ ∈ Ioc (0 : ℝ) 1 := ⟨ha0.trans_le hθ₂I.1, hθ₂I.2.trans hbC.2⟩
    have hp₂e : p₂ = wallPt (L ω) θ₂ := hwe.symm
    have hθ₂U : leftLo R' (L ω) r' < θ₂ := by
      by_contra hle
      push Not at hle
      apply hxU
      refine PocketJordan.wall_rev hcfg'.conf.left hcfg'.trace.1 hcfg'.revL hθ₂01 ⟨ha0', ha'.2⟩ hle ?_
      show wallPt (L ω) θ₂ ∈ _
      rw [← hp₂e]
      exact hf₂.2
    obtain ⟨θ, hθ, hθ₂θ, hψθ⟩ := exists_left_param_of_between hC hC0 hor hJ hU hU0 hsub hθ₁ h₁x hb₁
      ⟨hθ₂U, hθ₂01.2⟩ (hp₂e ▸ hf₂.1.1) (hp₂e ▸ hp₂x) (hp₂e ▸ hb₂)
    have hθC : wallPt (L ω) θ ∈ closure (cfPocket (R ω) (L ω) r) \ {cfPt (openPt (R ω) (L ω) r)} := by
      refine ⟨wallPt_left_mem_closure hU hU0 hsub ⟨hθ.1.le, hθ.2.le⟩, fun he => ?_⟩
      have hθ₂ne : θ₂ ≠ leftLo (R ω) (L ω) r := fun h2 => hp₂x (by
        rw [hp₂e]; show cfPt (WangWu.toDisc _ θ₂) = _; rw [h2, hLa])
      have hθI := mem_Icc_left_of_mem_closure hC hC0 ⟨ha'.1.trans_lt hθ.1, hθ.2.le.trans hb'.2⟩
        (wallPt_left_mem_closure hU hU0 hsub ⟨hθ.1.le, hθ.2.le⟩)
      have hθlo : θ = leftLo (R ω) (L ω) r := wallPt_injOn hC.left ⟨ha'.1.trans_lt hθ.1, hθ.2.le.trans hb'.2⟩
        ⟨ha0, hab.le.trans hbC.2⟩ (by rw [he]; show _ = cfPt (WangWu.toDisc _ _); rw [hLa])
      exact hθ₂ne (le_antisymm (hθlo ▸ hθ₂θ) hθ₂I.1)
    have hpF : extendFrom H (R6Fc.curChart A R L r η ψ n q ω).2.1 (R6Fc.seedR R L r η ψ q ω : ℂ) =
        wallPt (L ω) θ := by
      rw [hland, hb, ← hψθ]
      exact extension_psi_eq hJ hx₀ hE₀ hE₀c hθC
    obtain ⟨h1, h2, h3⟩ := nonCorner_of_left_open hC hU hU0 hθ
    exact ⟨hpF ▸ h1, hpF ▸ h2, hpF ▸ h3⟩

/-- **The non-corner landing of the left seed coordinate** (shared wall `R`; one realization): the mirror of
`nonCornerLanding_left` for `U = cfPocket (R ω) L' r'`. -/
theorem nonCornerLanding_right {A : Set Ω} {R L : Ω → ℝ≥0 → ℂ} {L' : ℝ≥0 → ℂ} {r r' : ℝ≥0} {W : Ω → ℝ → ℝ}
    {η : Ω → ℝ → ℂ} {ψ : Ω → ℂ → ℂ} {ψ' : ℂ → ℂ} {n : Ω → ℤ} {ω : Ω}
    (hcfg : ∀ ω ∈ A, IsOuterCfg (R ω) (L ω) r (W ω) (η ω)) (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω))
    (hω : ω ∈ A) (hcfg' : IsCfPocketConfig (R ω) L' r' (W ω) (η ω)) (hψ' : IsCfJordan (R ω) L' r' ψ')
    {q : ℝ≥0} (hq0 : 0 < q) (hq : (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω))
    (hsub : cfPocket (R ω) L' r' ⊆ cfPocket (R ω) (L ω) r)
    {u : ℝ} (hu0 : 0 ≤ u) (hcap : capClock (travAll R L r η ψ ω) u = q)
    (hrel : relTip R L r η u ω ∈ cfPocket (R ω) L' r')
    {u₁ : ℝ} (hu₁0 : 0 ≤ u₁) (hcap₁ : capClock (travAll R L r η ψ ω) u₁ ≤ q)
    (harc : relTip R L r η u₁ ω ∈ cfArcR (R ω) L' r' '' Ioo 0 1) :
    R6Fc.IsNonCornerLanding (R6Fc.curChart A R L r η ψ n q ω) (R6Fc.seedL R L r η ψ q ω)
      (cfPocket (R ω) L' r') (cfPocket (R ω) (L ω) r) (cfPt (openPt (R ω) L' r')) := by
  classical
  -- the outer pocket and its chart at `q`
  have hcf := hcfg ω hω
  have hG : ∀ ω ∈ A, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  have hCo : ∀ ω ∈ A, IsOpen (cfPocket (R ω) (L ω) r) := fun ω hω =>
    isOpen_image_negInv' (hG ω hω).isOpen_changePocket (hG ω hω).changePocket_subset_H
  have hCH : ∀ ω ∈ A, cfPocket (R ω) (L ω) r ⊆ H := fun ω hω =>
    PocketJordan.image_negInv_subset_H (hG ω hω).changePocket_subset_H
  have hψc : ∀ ω ∈ A, IsConformalBijection (ψ ω) (cfPocket (R ω) (L ω) r) H := fun ω hω => (hψ ω hω).2.2.2.1
  have hC0 := PocketMarks.zero_notMem_closure_of_rightLo_pos hcf.conf hcf.bounded
  have hCb : Bornology.IsBounded (cfPocket (R ω) (L ω) r) := isBounded_image_negInv hC0
  have hx₀ : cfPt (openPt (R ω) (L ω) r) ∉ cfPocket (R ω) (L ω) r := hcf.conf.cfPt_openPt_notMem
  have hJ := hψ ω hω
  have hγ : IsDrivenCurve (travAll R L r η ψ ω) := (hcf.props hJ).1
  obtain ⟨t₁, hqt₁, ht₁⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hq
  have hqt₁' : q < t₁ := by exact_mod_cast hqt₁
  obtain ⟨E₀, hE₀, hE₀c, -, WC, hWC, hWC0, hWCeq, ηC, hηC, hηCeq, hCf⟩ :=
    R6Fc.chart_facts (n := n) hCo hCH hψc hCb hx₀ hJ hω hγ ht₁
  obtain ⟨-, -, -, hOE, hOEc⟩ := hCf q hqt₁'
  have hq0' : (0 : ℝ) < q := by exact_mod_cast hq0
  have hWCq : ∀ s ∈ Icc (0 : ℝ) q, segDriver (travAll R L r η ψ ω) s.toNNReal = WC s := fun s hs =>
    hWCeq s ⟨hs.1, hs.2.trans (by exact_mod_cast hqt₁'.le)⟩
  have hvL : R6Fc.seedL R L r η ψ q ω = chartAL WC q := R6Fc.seedL_eq hWC hWCq
  -- the trace points of the outer chart
  have hcapq : capInv (travAll R L r η ψ ω) (q : ℝ) = u := by rw [← hcap]; exact hγ.capInv_eq hu0
  have htr : ∀ t ∈ Icc (0 : ℝ) q, ηC t = ψ ω (relTip R L r η (capInv (travAll R L r η ψ ω) t) ω) ∧
      0 ≤ capInv (travAll R L r η ψ ω) t ∧ capInv (travAll R L r η ψ ω) t ≤ u := fun t ht => by
    refine ⟨hηCeq t ht.1 (ht.2.trans (by exact_mod_cast hqt₁'.le)), ?_, hγ.capInv_le hu0 ht.1 (ht.2.trans hcap.ge)⟩
    refine (hγ.capInv_spec ht.1 (lt_of_le_of_lt (ENNReal.ofReal_le_ofReal ht.2) ?_)).1
    rwa [ENNReal.ofReal_coe_nnreal]
  have hηCq : ηC q = ψ ω (relTip R L r η u ω) := by rw [(htr q ⟨hq0'.le, le_rfl⟩).1, hcapq]
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
  -- the landing is `E₀(b)`
  have hland : extendFrom H (R6Fc.curChart A R L r η ψ n q ω).2.1 (R6Fc.seedL R L r η ψ q ω : ℂ) =
      E₀ (extendFrom H (fwdMapInv WC q) (chartAL WC q : ℂ)) := by
    have hvcl : ((chartAL WC q : ℝ) : ℂ) ∈ closure H := by
      rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]; exact R6Fc.real_mem_Hbar _
    rw [hvL]
    exact extendFrom_eq hvcl (R6Fc.tendsto_of_extension hOE hOEc (chartAL WC q))
  -- the contained pocket
  have hC := hcf.conf
  have hor := hcf.oriented
  have hU := hcfg'.conf
  have hU0 := PocketMarks.zero_notMem_closure_of_rightLo_pos hU hcfg'.bounded
  obtain ⟨hPU, -⟩ := R5Ref.pocket_of_cfg (Ω := Ω) (R := fun _ => R ω) (L := fun _ => L') (W := W) (η := η)
    (ψ := fun _ => ψ') (ω := ω) hcfg' hψ'
  obtain ⟨hu', hv', huv', -, -, -, -, -⟩ := hU.changeCorner_props
  have hu0' := hU.rightLo_pos hU0
  set T := pocketFibre (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
    (firstHit (η ω) (cfArcR (R ω) (L ω) r 0))
    (clockOf (pocketClock (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
      (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) (firstHit (η ω) (cfArcR (R ω) (L ω) r 0))) u) with hTdef
  have hT0 : 0 ≤ T := hcf.erase.nonneg.trans (hcf.erase.fibre_mem _).1
  have hηT : η ω T = relTip R L r η u ω := rfl
  have hTσ := (hPU.mem_Ioo_of_mem hT0 (hηT ▸ hrel)).2
  -- `x₀ᵁ` is not visited by `T`
  have hxU : wallPt (R ω) (rightLo (R ω) L' r') ∉ η ω '' Icc 0 T := by
    intro hm
    apply hPU.fresh_x
    have he : cfArcR (R ω) L' r' 0 = wallPt (R ω) (rightLo (R ω) L' r') := by rw [cfArcR_zero]; rfl
    obtain ⟨t, ht, hte⟩ := hm
    exact ⟨t, ⟨ht.1, ht.2.trans_lt hTσ⟩, hte.trans he.symm⟩
  -- the lower witness: a point of `U`'s open shared arc on the trace
  obtain ⟨v₁, hv₁, hv₁e⟩ := harc
  set s₁ := rightLo (R ω) L' r' + v₁ * (rightHi (R ω) L' r' - rightLo (R ω) L' r') with hs₁def
  have hs₁ : s₁ ∈ Ioo (rightLo (R ω) L' r') (rightHi (R ω) L' r') := (IsChangeConfigInc.affine_mem huv').2.1 hv₁
  have hs₁e : relTip R L r η u₁ ω = wallPt (R ω) s₁ := hv₁e.symm
  have hf₁ := relTip_facts hcf hu₁0 (by
    by_contra hlt'
    push Not at hlt'
    have := hγ.strictMonoOn_capClock (mem_Ici.2 hu0) (mem_Ici.2 hu₁0) hlt'
    linarith)
  have h₁x : wallPt (R ω) s₁ ≠ cfPt (openPt (R ω) (L ω) r) := by
    rw [← hs₁e, ← cfArcR_zero]; exact hf₁.1.2
  have hc₁ : capClock (travAll R L r η ψ ω) u₁ ∈ Icc (0 : ℝ) q := ⟨hγ.capClock_nonneg hu₁0, hcap₁⟩
  have hηC₁ : ηC (capClock (travAll R L r η ψ ω) u₁) = ψ ω (wallPt (R ω) s₁) := by
    rw [(htr _ hc₁).1, hγ.capInv_eq hu₁0, hs₁e]
  have hs₁C : wallPt (R ω) s₁ ∈ closure (cfPocket (R ω) (L ω) r) \ {cfPt (openPt (R ω) (L ω) r)} :=
    ⟨wallPt_right_mem_closure hU hU0 hsub ⟨hs₁.1.le, hs₁.2.le⟩, h₁x⟩
  have hs₁nC : wallPt (R ω) s₁ ∉ cfPocket (R ω) (L ω) r :=
    wallPt_notMem hC (Or.inl rfl) ⟨hu'.1.trans_lt hs₁.1, hs₁.2.le.trans hv'.2⟩
  have hs₁fr : wallPt (R ω) s₁ ∈ frontier (cfPocket (R ω) (L ω) r) \ {cfPt (openPt (R ω) (L ω) r)} :=
    ⟨⟨hs₁C.1, by rw [(hCo ω hω).interior_eq]; exact hs₁nC⟩, hs₁C.2⟩
  have hreal₁ : (ψ ω (wallPt (R ω) s₁)).im = 0 := hJ.2.2.2.2.1 _ hs₁fr
  have hb₁ : (extendFrom H (fwdMapInv WC q) (chartAL WC q : ℂ)).re ≤ (ψ ω (wallPt (R ω) s₁)).re := by
    have := hall _ hc₁ (by rw [hηC₁]; exact hreal₁)
    rwa [hηC₁] at this
  -- the coordinate of the lower witness is negative
  have hs₁CI : s₁ ∈ Ioo (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r) := by
    have hIl := mem_Icc_right_of_mem_closure hC hC0 ⟨hu'.1.trans_lt hs₁.1, hs₁.2.le.trans hv'.2⟩ hs₁C.1
    have hIh := mem_Icc_right_of_mem_closure hC hC0 ⟨hu'.1.trans_lt huv', hv'.2⟩
      (wallPt_right_mem_closure hU hU0 hsub ⟨huv'.le, le_rfl⟩)
    refine ⟨lt_of_le_of_ne hIl.1 fun he => h₁x ?_, hs₁.2.trans_le hIh.2⟩
    rw [← he]; rfl
  have hneg₁ : (ψ ω (wallPt (R ω) s₁)).re < 0 := (SideAnc.jordan_sides hC hC0 hor hJ).1 s₁ hs₁CI
  -- the far witness: a visited real trace point on the shared wall beyond `x₀ᵁ`
  obtain ⟨hcI₂, hcI₂0, hcI₂u⟩ := htr t₂ ht₂
  set p₂ := relTip R L r η (capInv (travAll R L r η ψ ω) t₂) ω with hp₂def
  have hf₂ := relTip_facts hcf hcI₂0 hcI₂u
  have hp₂re : (ψ ω p₂).im = 0 := by rw [← hcI₂]; exact ht₂im
  have hp₂fr : p₂ ∈ frontier (cfPocket (R ω) (L ω) r) := by
    refine ⟨hf₂.1.1, fun hin => ?_⟩
    rw [(hCo ω hω).interior_eq] at hin
    have := (hψc ω hω).2.mapsTo hin
    exact (ne_of_gt (show (0 : ℝ) < (ψ ω p₂).im from this)) hp₂re
  have hb₂ : (ψ ω p₂).re ≤ (extendFrom H (fwdMapInv WC q) (chartAL WC q : ℂ)).re := by rw [← hcI₂]; exact ht₂le
  have hCc := hC.isCfPocket hC0
  obtain ⟨hu, hv, huv, ha, hbC, hab, hLa, hLb⟩ := hC.changeCorner_props
  have hp₂x : p₂ ≠ cfPt (openPt (R ω) (L ω) r) := by rw [← cfArcR_zero]; exact hf₂.1.2
  rw [hCc.frontier_eq] at hp₂fr
  rcases hp₂fr with ⟨w, hw, hwe⟩ | ⟨w, hw, hwe⟩
  · set s₂ := rightLo (R ω) (L ω) r + w * (rightHi (R ω) (L ω) r - rightLo (R ω) (L ω) r) with hs₂def
    have hs₂I := (IsChangeConfigInc.affine_mem huv).1 hw
    have hu0 := hC.rightLo_pos hC0
    have hs₂01 : s₂ ∈ Ioc (0 : ℝ) 1 := ⟨hu0.trans_le hs₂I.1, hs₂I.2.trans hv.2⟩
    have hp₂e : p₂ = wallPt (R ω) s₂ := hwe.symm
    have hs₂U : rightLo (R ω) L' r' < s₂ := by
      by_contra hle
      push Not at hle
      apply hxU
      refine PocketJordan.wall_rev hcfg'.conf.right hcfg'.trace.1 hcfg'.revR hs₂01 ⟨hu0', hu'.2⟩ hle ?_
      show wallPt (R ω) s₂ ∈ _
      rw [← hp₂e]
      exact hf₂.2
    obtain ⟨s, hs, hs₂s, hψs⟩ := exists_right_param_of_between hC hC0 hor hJ hU hU0 hsub hs₁ h₁x hb₁
      ⟨hs₂U, hs₂01.2⟩ (hp₂e ▸ hf₂.1.1) (hp₂e ▸ hp₂x) (hp₂e ▸ hb₂)
    have hsC : wallPt (R ω) s ∈ closure (cfPocket (R ω) (L ω) r) \ {cfPt (openPt (R ω) (L ω) r)} := by
      refine ⟨wallPt_right_mem_closure hU hU0 hsub ⟨hs.1.le, hs.2.le⟩, fun he => ?_⟩
      have hs₂ne : s₂ ≠ rightLo (R ω) (L ω) r := fun h2 => hp₂x (by rw [hp₂e, h2]; rfl)
      have hslo : s = rightLo (R ω) (L ω) r := wallPt_injOn hC.right ⟨hu'.1.trans_lt hs.1, hs.2.le.trans hv'.2⟩
        ⟨hu0, huv.le.trans hv.2⟩ (by rw [he]; rfl)
      exact hs₂ne (le_antisymm (hslo ▸ hs₂s) hs₂I.1)
    have hpF : extendFrom H (R6Fc.curChart A R L r η ψ n q ω).2.1 (R6Fc.seedL R L r η ψ q ω : ℂ) =
        wallPt (R ω) s := by
      rw [hland, hb, ← hψs]
      exact extension_psi_eq hJ hx₀ hE₀ hE₀c hsC
    obtain ⟨h1, h2, h3⟩ := nonCorner_of_right_open hC hU hU0 hs
    exact ⟨hpF ▸ h1, hpF ▸ h2, hpF ▸ h3⟩
  · -- a left-wall point has a nonnegative coordinate
    exfalso
    have hθI := (IsChangeConfigInc.affine_mem hab).1 hw
    have hθI' : leftLo (R ω) (L ω) r + w * (leftHi (R ω) (L ω) r - leftLo (R ω) (L ω) r) ∈
        Ioc (leftLo (R ω) (L ω) r) (leftHi (R ω) (L ω) r) := by
      refine ⟨lt_of_le_of_ne hθI.1 fun he => hp₂x ?_, hθI.2⟩
      rw [← hwe]
      show cfPt (WangWu.toDisc _ _) = cfPt _
      rw [← he, hLa]
    obtain ⟨-, -, hanti⟩ := left_arc_facts hC hC0 hor hJ
    have hge := hanti.antitoneOn hθI' ⟨hab, le_rfl⟩ hθI'.2
    have h0 : (ψ ω (wallPt (L ω) (leftHi (R ω) (L ω) r))).re = 0 := by
      have : wallPt (L ω) (leftHi (R ω) (L ω) r) = cfPt (closePt (R ω) (L ω) r) := by
        show cfPt (WangWu.toDisc _ _) = cfPt _; rw [hLb]
      rw [this, hJ.2.2.2.2.2.1]; rfl
    have hp₂L : ψ ω p₂ = ψ ω (wallPt (L ω)
        (leftLo (R ω) (L ω) r + w * (leftHi (R ω) (L ω) r - leftLo (R ω) (L ω) r))) := by rw [← hwe]; rfl
    have : 0 ≤ (ψ ω p₂).re := by rw [hp₂L]; exact h0.ge.trans hge
    linarith

end InteractingSLE.Sec7.R6Fd
