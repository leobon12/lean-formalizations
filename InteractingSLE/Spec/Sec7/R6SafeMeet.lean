/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R6SafeIncl
import InteractingSLE.Spec.Sec7.PocketSideInPatchTip

/-!
# Lemma R.6's face: the common point of the two current domains (bounded mixed shape)

PROVE-R6-SAFE, round 4. For the outer pocket `C` at relative capacity `q` and a contained pocket `U ⊆ C` whose
interior holds the physical tip `η(T)`, `T = T_C(q)` the fibre end, every rational inner time `q'` slightly above the
relative capacity `c_U(T)` of `U` reached at `T` has

* the time ordering `T < T⁰_U(q')` (`R5Ref.leftStop`), and
* a common point of the two current domains `D_U(q') ∩ D_C(q)`:

the outer current inverse lands at the tip `η(T) ∈ U` (`PocketStopSide.tendsto_relative_inverse_tip`), so some
`z ∈ D_C(q)` lies in `U`; such `z` avoids `K_T = fill η([0, T])` (`HOuter.relDomain_subset_domain`), hence avoids
`K_{T₁}` for some `T₁ > T` (the swallowing time of `z` exceeds `T`); `c_U` increases strictly right after the visit
time `T` (`relCap_lt_relCap_of_visit`), and every `q' ∈ (c_U(T), c_U(T'))`, `T' ≤ T₁`, has `T⁰_U(q') ≤ T'`, so
`z ∈ U ∩ (ℍ ∖ fill η([0, T⁰_U(q')])) = D_U(q')` (`R5Ref.current_dom_eq`).

The face of shape `Mixed` is therefore reduced to `R6FaceR` for all rational `q'` in a right neighbourhood of `c_U(T)`
(`R6FaceSMixedRemaining`, which may also assume the time ordering and the inclusion of the current domains).

## Main results

* `relCap_lt_relCap_of_visit`, `exists_rat_meet_near_tip`;
* `R6FaceSMixedRemaining`, **`r6FaceQMixedRemaining_of_faceS`**.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology Metric
open QuantumZipper (H Hbar)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R6Safe

open Sec6 PocketTraversal Lemma71C PocketJordan PocketCoord PocketCoupling PocketStop PocketStopField HOuter
  PocketWordAssembly

/-! ### The relative capacity increases strictly after a visit time -/

section Strict

variable {W : ℝ → ℝ} {η : ℝ → ℂ} {C : Set ℂ} {α₁ α₂ β : ℝ → ℂ} {τ σ : ℝ} {ψ : ℂ → ℂ}

/-- **The relative capacity increases strictly after a visit**: if `η(a) ∈ C` and `a < b` in `[τ, σ)`, then
`c(a) < c(b)` (the clock grows on the visit interval around `a`, `erasureClock_eq_iff`). -/
theorem relCap_lt_relCap_of_visit (hP : IsReversePocket W η C α₁ α₂ β τ σ)
    (hAC : AttachmentConstancy η C α₁ α₂ τ σ) (hψ : IsJordanCoord C (α₁ 0) (α₁ 1) ψ) {a b : ℝ}
    (ha : a ∈ Ico τ σ) (hb : b ∈ Ico τ σ) (hab : a < b) (ha0 : 0 ≤ a) (hv : η a ∈ C) :
    PocketStopMarked.relCap η C τ σ ψ a < PocketStopMarked.relCap η C τ σ ψ b := by
  have haI : a ∈ visitSet η C τ σ := ⟨hP.mem_Ioo_of_mem ha0 hv, hv⟩
  obtain ⟨t', ht', ht'I⟩ := hP.exists_mem_Ioo_of_mem hab ⟨le_rfl, hab.le⟩ haI
  have hne : pocketClock η C τ σ a ≠ pocketClock η C τ σ b := fun h =>
    Set.disjoint_left.1 ((erasureClock_eq_iff hP.isOpen_visitSet hab).1 h) ht' ht'I
  have hlt : pocketClock η C τ σ a < pocketClock η C τ σ b := lt_of_le_of_ne (hP.monotone_clock hab.le) hne
  have hL : pocketClock η C τ σ b < pocketClock η C τ σ σ := hP.clock_lt_clock_σ hAC hb
  have h0 : 0 ≤ pocketClock η C τ σ a := hP.clock_nonneg ha.1
  have hrt : PocketStopMarked.relTime η C τ σ a < PocketStopMarked.relTime η C τ σ b := by
    unfold PocketStopMarked.relTime
    rw [div_lt_div_iff₀ (sub_pos.2 (hlt.trans hL)) (sub_pos.2 hL)]
    nlinarith
  exact (isDrivenCurve_relCurve_of_isReversePocket hP hAC hψ).strictMonoOn_capClock
    (PocketStopMarked.relTime_nonneg hP hAC ha) (PocketStopMarked.relTime_nonneg hP hAC hb) hrt

end Strict

/-! ### The common point near the outer tip -/

section Meet

variable {Ω : Type*} {A A' : Set Ω} {R L R' L' : Ω → ℝ≥0 → ℂ} {r r' : ℝ≥0} {W : Ω → ℝ → ℝ}
  {η : Ω → ℝ → ℂ} {ψ ψ' : Ω → ℂ → ℂ} {n n' : Ω → ℤ} {q : ℝ≥0} {ω : Ω}

/-- The fibre end `T_C(q)` of the bounded pocket `C = cfPocket R L r` at relative capacity `q`. -/
def outerFibreEnd (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (ψ : Ω → ℂ → ℂ) (q : ℝ≥0) (ω : Ω) : ℝ :=
  pocketFibre (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
    (firstHit (η ω) (cfArcR (R ω) (L ω) r 0))
    (clockOf (pocketClock (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
      (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)))
      (capInv (travAll R L r η ψ ω) q))

/-- The relative capacity of the bounded pocket `cfPocket R L r` reached at the ambient time `t`. -/
def innerRelCap (R L : Ω → ℝ≥0 → ℂ) (r : ℝ≥0) (η : Ω → ℝ → ℂ) (ψ : Ω → ℂ → ℂ) (t : ℝ) (ω : Ω) : ℝ :=
  PocketStopMarked.relCap (η ω) (cfPocket (R ω) (L ω) r) (firstHit (η ω) (cfArcR (R ω) (L ω) r 1))
    (firstHit (η ω) (cfArcR (R ω) (L ω) r 0)) (ψ ω) t

/-- **The inner half of (a3)** (contained bounded pocket `U`): if `η(T) ∈ U` and `z ∈ U` is outside the physical hull
`K_T`, every right neighbourhood of `c_U(T)` contains a rational live inner time `q'` with `T < T⁰_U(q')` and
`z ∈ D_U(q')`. -/
theorem exists_rat_mem_inner_dom (hcfg' : ∀ ω ∈ A', IsCfPocketConfig (R' ω) (L' ω) r' (W ω) (η ω))
    (hψ' : ∀ ω ∈ A', IsCfJordan (R' ω) (L' ω) r' (ψ' ω)) (hω' : ω ∈ A') {T : ℝ} (hT0 : 0 ≤ T)
    (htip : η ω T ∈ cfPocket (R' ω) (L' ω) r') {z : ℂ} (hzU : z ∈ cfPocket (R' ω) (L' ω) r')
    (hphys : z ∈ H \ QuantumZipper.fwdHull (W ω) T) {ε : ℝ} (hε : 0 < ε) :
    ∃ q' : ℚ, innerRelCap R' L' r' η ψ' T ω < q' ∧ (q' : ℝ) < innerRelCap R' L' r' η ψ' T ω + ε ∧
      ((StripSys.rt q' : ℝ≥0) : ℝ≥0∞) < capLife (travAll R' L' r' η ψ' ω) ∧
      T < R5Ref.leftStop R' L' r' η ψ' (StripSys.rt q') ω ∧
      z ∈ ((relChart (fun ω => shiftChart (pChart A' (fun ω => cfPocket (R' ω) (L' ω) r') ψ' ω) (n' ω))
          (travAll R' L' r' η ψ') (StripSys.rt q') ω).dom : Set ℂ) := by
  have hG' : ∀ ω ∈ A', IsChangeConfigInc (R' ω) (L' ω) r' := fun ω hω => (hcfg' ω hω).conf
  have hCo' : ∀ ω ∈ A', IsOpen (cfPocket (R' ω) (L' ω) r') := fun ω hω =>
    isOpen_image_negInv' (hG' ω hω).isOpen_changePocket (hG' ω hω).changePocket_subset_H
  have hCH' : ∀ ω ∈ A', cfPocket (R' ω) (L' ω) r' ⊆ H := fun ω hω =>
    PocketJordan.image_negInv_subset_H (hG' ω hω).changePocket_subset_H
  -- `z` is outside the physical hull at some `T₁ > T`
  have hswal : ENNReal.ofReal T < QuantumZipper.swallowTime (W ω) z := by
    by_contra hle
    exact hphys.2 ⟨hphys.1, not_lt.1 hle⟩
  obtain ⟨T₁, -, hTT₁, hT₁s⟩ := ENNReal.lt_iff_exists_real_btwn.1 hswal
  have hTT₁' : T < T₁ := (ENNReal.ofReal_lt_ofReal_iff'.1 hTT₁).1
  -- the inner relative capacity increases right after `T`
  obtain ⟨hP', hJ'⟩ := R5Ref.pocket_of_cfg (hcfg' ω hω') (hψ' ω hω')
  have hAC := (hcfg' ω hω').attach
  have hTI := hP'.mem_Ioo_of_mem hT0 htip
  set σ' := firstHit (η ω) (cfArcR (R' ω) (L' ω) r' 0) with hσ'
  set T' := min T₁ ((T + σ') / 2) with hT'def
  have hTT' : T < T' := lt_min hTT₁' (by linarith [hTI.2])
  have hT'σ : T' < σ' := (min_le_right _ _).trans_lt (by linarith [hTI.2])
  have hT'I : T' ∈ Ico (firstHit (η ω) (cfArcR (R' ω) (L' ω) r' 1)) σ' := ⟨hTI.1.le.trans hTT'.le, hT'σ⟩
  have hTIco : T ∈ Ico (firstHit (η ω) (cfArcR (R' ω) (L' ω) r' 1)) σ' := ⟨hTI.1.le, hTI.2⟩
  have hcapLT := relCap_lt_relCap_of_visit hP' hAC hJ' hTIco hT'I hTT' hT0 htip
  obtain ⟨q', hq'lo, hq'hi⟩ := exists_rat_btwn (lt_min hcapLT (lt_add_of_pos_right
    (innerRelCap R' L' r' η ψ' T ω) hε))
  have hc0 : 0 ≤ innerRelCap R' L' r' η ψ' T ω :=
    (isDrivenCurve_relCurve_of_isReversePocket hP' hAC hJ').capClock_nonneg
      (PocketStopMarked.relTime_nonneg hP' hAC hTIco)
  have hqpos : (0 : ℝ) < q' := hc0.trans_lt hq'lo
  have hrt : ((StripSys.rt q' : ℝ≥0) : ℝ) = q' := Real.coe_toNNReal _ hqpos.le
  have hq'0 : (0 : ℝ) ≤ ((StripSys.rt q' : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
  have hq'T' : (q' : ℝ) ≤ innerRelCap R' L' r' η ψ' T' ω := (hq'hi.trans_le (min_le_left _ _)).le
  have hlive : ENNReal.ofReal ((StripSys.rt q' : ℝ≥0) : ℝ) <
      capLife (PocketStopMarked.trav (η ω) (cfPocket (R' ω) (L' ω) r')
        (firstHit (η ω) (cfArcR (R' ω) (L' ω) r' 1)) σ' (ψ' ω)) := by
    rw [hrt]
    exact (ENNReal.ofReal_le_ofReal hq'T').trans_lt (PocketStopMarked.relCap_lt_capLife hP' hAC hJ' hT'I)
  have hlive' : ((StripSys.rt q' : ℝ≥0) : ℝ≥0∞) < capLife (travAll R' L' r' η ψ' ω) := by
    rw [← ENNReal.ofReal_coe_nnreal]
    exact hlive
  have hLSlt : T < R5Ref.leftStop R' L' r' η ψ' (StripSys.rt q') ω := by
    by_contra hle
    have h := (PocketStopMarked.ambTime0_le_iff hP' hAC hJ' hq'0 hlive hTIco).1 (not_lt.1 hle)
    rw [hrt] at h
    exact absurd hq'lo (not_lt.2 h)
  have hLSle : R5Ref.leftStop R' L' r' η ψ' (StripSys.rt q') ω ≤ T' :=
    (PocketStopMarked.ambTime0_le_iff hP' hAC hJ' hq'0 hlive hT'I).2 (by rw [hrt]; exact hq'T')
  -- `z` lies in the inner current domain
  obtain ⟨hcI, hdomI, heqI⟩ := R5Phase.shiftChart_dom_facts hCo' hCH' (fun ω hω => (hψ' ω hω).2.2.2.1) n' ω hω'
  have hLS0 : 0 ≤ R5Ref.leftStop R' L' r' η ψ' (StripSys.rt q') ω := hT0.trans hLSlt.le
  refine ⟨q', hq'lo, hq'hi.trans_le (min_le_right _ _), hlive', hLSlt, ?_⟩
  rw [R5Ref.current_dom_eq (c := fun ω => shiftChart (pChart A' (fun ω => cfPocket (R' ω) (L' ω) r') ψ' ω)
    (n' ω)) hω' (hcfg' ω hω') (hψ' ω hω') hcI hdomI heqI hlive', ← (hcfg' ω hω').trace.2.2 _ hLS0]
  refine ⟨hzU, hphys.1, fun hK => ?_⟩
  have h1 : QuantumZipper.swallowTime (W ω) z ≤ ENNReal.ofReal T₁ :=
    hK.2.trans (ENNReal.ofReal_le_ofReal (hLSle.trans (min_le_left _ _)))
  exact absurd hT₁s (not_lt.2 h1)

/-- **The outer half of (a3)** (bounded outer pocket `C` at `q`): every open `V ∋ η(T_C(q))` contains a point of the
current domain `D_C(q)` outside the physical hull `K_{T_C(q)}` (the current inverse lands at the tip,
`PocketStopSide.tendsto_relative_inverse_tip`; `HOuter.relDomain_subset_domain`). -/
theorem exists_outer_dom_near_tip (hcfg : ∀ ω ∈ A, IsOuterCfg (R ω) (L ω) r (W ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) (hω : ω ∈ A)
    (hq : (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω)) {V : Set ℂ} (hV : IsOpen V)
    (htip : η ω (outerFibreEnd R L r η ψ q ω) ∈ V)
    (htipC : η ω (outerFibreEnd R L r η ψ q ω) ∈ cfPocket (R ω) (L ω) r) :
    ∃ z ∈ V, z ∈ ((relChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω))
        (travAll R L r η ψ) q ω).dom : Set ℂ) ∧ z ∈ H \ QuantumZipper.fwdHull (W ω) (outerFibreEnd R L r η ψ q ω) := by
  have hG : ∀ ω ∈ A, IsChangeConfigInc (R ω) (L ω) r := fun ω hω => (hcfg ω hω).conf
  have hCo : ∀ ω ∈ A, IsOpen (cfPocket (R ω) (L ω) r) := fun ω hω =>
    isOpen_image_negInv' (hG ω hω).isOpen_changePocket (hG ω hω).changePocket_subset_H
  have hCH : ∀ ω ∈ A, cfPocket (R ω) (L ω) r ⊆ H := fun ω hω =>
    PocketJordan.image_negInv_subset_H (hG ω hω).changePocket_subset_H
  have hγ : IsDrivenCurve (travAll R L r η ψ ω) := ((hcfg ω hω).props (hψ ω hω)).1
  obtain ⟨hc, hdom, hfwd⟩ := R5Phase.shiftChart_dom_facts hCo hCH (fun ω hω => (hψ ω hω).2.2.2.1) n ω hω
  have hO : (relChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω))
      (travAll R L r η ψ) q ω).IsConformal := PocketStopSide.isConformal_relChart_of_driven hγ hq hc
  set T := outerFibreEnd R L r η ψ q ω with hTdef
  have hTrace : capTrace (travAll R L r η ψ ω) q =
      (shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω)).1 (η ω T) := by
    rw [hfwd htipC]
    rfl
  have hlim := PocketStopSide.tendsto_relative_inverse_tip hc hγ hq (p := η ω T)
    (by rw [hdom]; exact htipC) hTrace
  have hNe : (𝓝[H] (0 : ℂ)).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (by
    rw [QuantumZipper.CA.Car.closure_H_eq_Hbar]
    exact mem_Hbar_of_im_eq_zero (by simp))
  obtain ⟨w, hwV, hwH⟩ := ((hlim.eventually_mem (hV.mem_nhds htip)).and
    (self_mem_nhdsWithin : ∀ᶠ w in 𝓝[H] (0 : ℂ), w ∈ H)).exists
  have hzdom := hO.inv_mem_dom hwH
  have hzD : (relChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω))
      (travAll R L r η ψ) q ω).2.1 w ∈ _ := hzdom
  rw [SetLike.mem_coe.symm, relChart_dom_eq_inter (n := n) hCo hCH (fun ω hω => (hψ ω hω).2.2.2.1) hω hγ hq] at hzD
  have hc' := hcfg ω hω
  have hJ : IsJordanCoord (cfPocket (R ω) (L ω) r) (cfArcR (R ω) (L ω) r 0) (cfArcR (R ω) (L ω) r 1) (ψ ω) := by
    rw [IsChangeConfigInc.cfArcR_zero, IsChangeConfigInc.cfArcR_one]; exact hψ ω hω
  have hCb : Bornology.IsBounded (cfPocket (R ω) (L ω) r) :=
    isBounded_image_negInv (PocketMarks.zero_notMem_closure_of_rightLo_pos hc'.conf hc'.bounded)
  exact ⟨_, hwV, hzdom, relDomain_subset_domain hc'.erase hc'.trace hc'.continuous_W hc'.W_zero (hCH ω hω) hCb hJ hγ
    q.coe_nonneg (by rw [ENNReal.ofReal_coe_nnreal]; exact hq) hzD⟩

/-- **(a3) The common point of the two current domains** (outer pocket `C` at `q`, contained pocket `U ⊆ C` holding
the tip `η(T_C(q))`): every right neighbourhood of `c_U(T_C(q))` contains a rational live inner time `q'` with
`T_C(q) < T⁰_U(q')` and `D_U(q') ∩ D_C(q) ≠ ∅`. -/
theorem exists_rat_meet_near_tip (hcfg : ∀ ω ∈ A, IsOuterCfg (R ω) (L ω) r (W ω) (η ω))
    (hψ : ∀ ω ∈ A, IsCfJordan (R ω) (L ω) r (ψ ω)) (hω : ω ∈ A)
    (hq : (q : ℝ≥0∞) < capLife (travAll R L r η ψ ω))
    (hcfg' : ∀ ω ∈ A', IsCfPocketConfig (R' ω) (L' ω) r' (W ω) (η ω))
    (hψ' : ∀ ω ∈ A', IsCfJordan (R' ω) (L' ω) r' (ψ' ω)) (hω' : ω ∈ A')
    (hsub : cfPocket (R' ω) (L' ω) r' ⊆ cfPocket (R ω) (L ω) r)
    (htip : η ω (outerFibreEnd R L r η ψ q ω) ∈ cfPocket (R' ω) (L' ω) r') {ε : ℝ} (hε : 0 < ε) :
    ∃ q' : ℚ, innerRelCap R' L' r' η ψ' (outerFibreEnd R L r η ψ q ω) ω < q' ∧
      (q' : ℝ) < innerRelCap R' L' r' η ψ' (outerFibreEnd R L r η ψ q ω) ω + ε ∧
      ((StripSys.rt q' : ℝ≥0) : ℝ≥0∞) < capLife (travAll R' L' r' η ψ' ω) ∧
      outerFibreEnd R L r η ψ q ω < R5Ref.leftStop R' L' r' η ψ' (StripSys.rt q') ω ∧
      (((relChart (fun ω => shiftChart (pChart A' (fun ω => cfPocket (R' ω) (L' ω) r') ψ' ω) (n' ω))
          (travAll R' L' r' η ψ') (StripSys.rt q') ω).dom : Set ℂ) ∩
        (relChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω))
          (travAll R L r η ψ) q ω).dom).Nonempty := by
  have hG' : IsChangeConfigInc (R' ω) (L' ω) r' := (hcfg' ω hω').conf
  have hUo : IsOpen (cfPocket (R' ω) (L' ω) r') :=
    isOpen_image_negInv' hG'.isOpen_changePocket hG'.changePocket_subset_H
  obtain ⟨z, hzU, hzdom, hphys⟩ := exists_outer_dom_near_tip (n := n) hcfg hψ hω hq hUo htip (hsub htip)
  have hT0 : 0 ≤ outerFibreEnd R L r η ψ q ω :=
    (hcfg ω hω).erase.nonneg.trans ((hcfg ω hω).erase.fibre_mem _).1
  obtain ⟨q', hlo, hhi, hlive, hLS, hzI⟩ := exists_rat_mem_inner_dom (n' := n') hcfg' hψ' hω' hT0 htip hzU hphys hε
  exact ⟨q', hlo, hhi, hlive, hLS, z, hzI, hzdom⟩

end Meet

/-! ### The face of shape `Mixed` reduced to `R6FaceR` near the tip's inner relative time -/

section FaceS

open MeasureTheory ProbabilityTheory
open LQGMetric (DistOn)
open QuantumZipper (chiC)
open scoped Real
open WholeField R7Outer R7Leaves R6Nest R6Rel R6Cert HOuter PocketMarks PocketSeedOpen PocketStopWallsFin PocketStopSide

universe u

/-- **Named, unproved: R.6's face, shape `Mixed`, near the tip's inner relative time**: almost surely on the nested
event, for some `ε > 0`, every rational inner time `q'` with `c_U(T_C(q)) < q' < c_U(T_C(q)) + ε` (live, with the time
ordering `T_C(q) < T⁰_U(q')` and the inclusion of the current domains, all three proved in
`r6FaceQMixedRemaining_of_faceS`) has `R6FaceR`. The common point and the time ordering of `R6FaceQMixedRemaining`
are proved (`exists_rat_meet_near_tip`). -/
def R6FaceSMixedRemaining (k rL rR c c' : ℝ) : Prop :=
  (k / 2 - 4 < rL ∧ rR ≤ k / 2 - 4) ∨ (rL ≤ k / 2 - 4 ∧ k / 2 - 4 < rR) →
  ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞)
    (αR βR βL αL : Ω → ℝ≥0 → ℂ) (ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞),
    IsR7OuterConfig k rL rR c c' P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL →
    ∀ (R L : Ω → ℝ≥0 → ℂ) (η : Ω → ℝ → ℂ), IsR7Versions P W' αR αL R L η →
    ∀ MR ML : Ω → ℝ≥0 → ℂ, IsFrontierVersion P βR MR → IsFrontierVersion P βL ML →
    ∀ (r : ℝ≥0) (A A' : Set Ω) (ψ ψ' : Ω → ℂ → ℂ) (n n' : Ω → ℤ) (s q : ℚ),
      (∀ ω ∈ A, IsOuterCfg (R ω) (L ω) r (fun t : ℝ => W' t.toNNReal ω) (η ω) ∧
        IsCfJordan (R ω) (L ω) r (ψ ω)) →
      (∀ ω ∈ A', IsCfPocketConfig (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s)
          (fun t : ℝ => W' t.toNNReal ω) (η ω) ∧
        IsCfJordan (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s) (ψ' ω)) →
      ∀ᵐ ω ∂P, ω ∈ A → ω ∈ A' →
        ω ∈ nestRelEvent R L r η ψ MR ML (innerRight k rL R MR) (innerLeft k rR L ML) s q →
        ∃ ε : ℝ, 0 < ε ∧ ∀ q' : ℚ,
          innerRelCap (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ'
              (outerFibreEnd R L r η ψ (StripSys.rt q) ω) ω < q' →
          (q' : ℝ) < innerRelCap (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ'
              (outerFibreEnd R L r η ψ (StripSys.rt q) ω) ω + ε →
          ((StripSys.rt q' : ℝ≥0) : ℝ≥0∞) <
            capLife (travAll (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' ω) →
          outerFibreEnd R L r η ψ (StripSys.rt q) ω <
            R5Ref.leftStop (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' (StripSys.rt q') ω →
          ((relChart (fun ω => shiftChart (pChart A' (fun ω => cfPocket (innerRight k rL R MR ω)
                (innerLeft k rR L ML ω) (StripSys.rt s)) ψ' ω) (n' ω))
              (travAll (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ') (StripSys.rt q')
                ω).dom : Set ℂ) ⊆
            (relChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω))
              (travAll R L r η ψ) (StripSys.rt q) ω).dom →
          R6FaceR (fun _ : Fin 1 => rL) (fun _ : Fin 1 => rR) (fun _ : Fin 1 => innerRight k rL rL (k / 2 - 4))
            (fun _ : Fin 1 => innerLeft k rR rR (k / 2 - 4))
            (fun i => geomLW (fun t ω => segDriver (travAll R L r η ψ ω) t) (fun _ => LP.twoSeedXL) i
              (StripSys.rt q) ω - segDriver (travAll R L r η ψ ω) (StripSys.rt q))
            (fun j => geomRW (fun t ω => segDriver (travAll R L r η ψ ω) t) (fun _ => LP.twoSeedXR) j
              (StripSys.rt q) ω - segDriver (travAll R L r η ψ ω) (StripSys.rt q))
            (fun i => geomLW (fun t ω => segDriver (travAll (innerRight k rL R MR) (innerLeft k rR L ML)
                (StripSys.rt s) η ψ' ω) t) (fun _ => LP.twoSeedXL) i (StripSys.rt q') ω -
              segDriver (travAll (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' ω)
                (StripSys.rt q'))
            (fun j => geomRW (fun t ω => segDriver (travAll (innerRight k rL R MR) (innerLeft k rR L ML)
                (StripSys.rt s) η ψ' ω) t) (fun _ => LP.twoSeedXR) j (StripSys.rt q') ω -
              segDriver (travAll (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' ω)
                (StripSys.rt q'))
            (relChart (fun ω => shiftChart (pChart A (fun ω => cfPocket (R ω) (L ω) r) ψ ω) (n ω))
              (travAll R L r η ψ) (StripSys.rt q) ω)
            (relChart (fun ω => shiftChart (pChart A' (fun ω => cfPocket (innerRight k rL R MR ω)
                (innerLeft k rR L ML ω) (StripSys.rt s)) ψ' ω) (n' ω))
              (travAll (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ') (StripSys.rt q') ω)
            (pocketSet A R L r η ψ n (StripSys.rt q) ω)
            (pocketSet A' (innerRight k rL R MR) (innerLeft k rR L ML) (StripSys.rt s) η ψ' n' (StripSys.rt q') ω)

/-- **`R6FaceQMixedRemaining` from the face near the tip's inner relative time**: the tip `η(T_C(q))` is the nested
event's relative tip, in `U`; `exists_rat_meet_near_tip` gives a rational `q'` in the neighbourhood with the time
ordering and a common point, hence the inclusion (`inner_dom_subset_outer_dom`). -/
theorem r6FaceQMixedRemaining_of_faceS {k rL rR c c' : ℝ} (hS : R6FaceSMixedRemaining.{u} k rL rR c c') :
    R6FaceQMixedRemaining.{u} k rL rR c c' := by
  intro hmix Ω _ _ P _ h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hV MR ML hMR hML r A A' ψ ψ' n n' s q hA
    hA'
  filter_upwards [hS hmix P h W' ζ' αR βR βL αL ζαR ζβR ζβL ζαL hcfg R L η hV MR ML hMR hML r A A' ψ ψ' n n' s q
    hA hA'] with ω hω hωA hωA' hωN
  obtain ⟨ε, hε, hR⟩ := hω hωA hωA' hωN
  obtain ⟨hq0, hqlive, -, hsub, u, hu0, hcap, hrel, -⟩ := hωN
  have hγ : IsDrivenCurve (travAll R L r η ψ ω) := (((hA ω hωA).1).props (hA ω hωA).2).1
  have hrtq : ((StripSys.rt q : ℝ≥0) : ℝ) = q := Real.coe_toNNReal _ (by exact_mod_cast hq0.le)
  have hinv : capInv (travAll R L r η ψ ω) ((StripSys.rt q : ℝ≥0) : ℝ) = u := by
    rw [hrtq, ← hcap]
    exact hγ.capInv_eq hu0
  have htip : η ω (outerFibreEnd R L r η ψ (StripSys.rt q) ω) ∈
      cfPocket (innerRight k rL R MR ω) (innerLeft k rR L ML ω) (StripSys.rt s) := by
    unfold outerFibreEnd
    rw [hinv]
    exact hrel
  obtain ⟨q', hlo, hhi, hlive, hLS, hmeet⟩ := exists_rat_meet_near_tip (n := n) (n' := n')
    (fun ω hω => (hA ω hω).1) (fun ω hω => (hA ω hω).2) hωA hqlive (fun ω hω => (hA' ω hω).1)
    (fun ω hω => (hA' ω hω).2) hωA' hsub htip hε
  have hincl := inner_dom_subset_outer_dom (fun ω hω => (hA ω hω).1) (fun ω hω => (hA ω hω).2) hωA hqlive
    (fun ω hω => (hA' ω hω).1) (fun ω hω => (hA' ω hω).2) hωA' hlive hsub hLS.le hmeet
  exact ⟨q', hlive, hLS.le, hmeet, hR q' hlo hhi hlive hLS hincl⟩

end FaceS

end InteractingSLE.Sec7.R6Safe
