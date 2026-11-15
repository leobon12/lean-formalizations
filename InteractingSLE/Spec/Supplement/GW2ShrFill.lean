/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2ShrTips
import InteractingSLE.Spec.Supplement.GW2SwcChart
import InteractingSLE.Spec.Supplement.Q3RelGB6Chart
import InteractingSLE.Spec.Supplement.GW2StmTip
import InteractingSLE.Spec.Supplement.GB6LawTrace
import InteractingSLE.Spec.Supplement.GB6CoordBCurve
import InteractingSLE.Foundations.Loewner.HullFilling
import InteractingSLE.Spec.Sec5.CrossRestartTrace
import InteractingSLE.Spec.Ito.ExhaustPath

/-!
# GW2's stage stop `σ_k`, part 5: the stage's filled retained hull through the launch chart

Packet PROVE-GW2-STAGEMEAN, hull-reading round. The union mean at stage `k` (`GW2Stm.exists_unionMean_gw2_stop`) reads
the stage's retained set as the inverted hull `invHull W_k σ_k` of the conditional counterflow, in the launch chart's
coordinates. Its reading in the original coordinates is the original counterflow's inverted hull at `s = ℓ σ_k`. At
the level of physical points this is `GW2Shr.tipSet_eq_of_clock`; here it is proved for the FILLED hulls:

* **`fwdMapInv_image_invHull`**: for a continuous driver `J` from `0` with boundary limits at time `T`, counterflow
  drivers `W_k`, `W'` with generating traces, and a continuous monotone clock `ℓ` from `0` relating their tips
  through `Chart.id.loewner J T` and the inversion, if the closure of the old hull `K^J_T` misses that of
  `invHull W' (ℓ t₀)`, then `fwdMapInv J T '' invHull W_k t₀ = invHull W' (ℓ t₀)`. Route: both hulls are fillings
  of their traces; `Supp8.GB6.isFilling_relMap_image` carries the original filling by the relative map; the traces
  agree in `ℍ` point by point (`BW1Det.tipRel_iff_traces`; `bdry_notMem_of_real`: a real boundary value of the inverse
  Loewner map is never a free point); a filling of a compact set is unique (`isFilling_iff_inter_H_eq_fillH`).
* **`invHull_eq_launch`**: the same for the launch chart `succChart 0 Δ D k` of a GW2 run from the root `0` whose
  first `k` stopped pieces are continuous from `0` (`succChart_inv_eq`: its inverse is `fwdMapInv (joinDrv)
  (joinTime)` on `ℍ`).
* `bdry_eq_of_mem_H`, `bdry_notMem_of_real`, `tipAt_trans_congr`, `invHull_subset_H`: helpers.

Deterministic. Conditional helper with a distinct name; it replaces no source theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMapInv fwdHull)

namespace InteractingSLE.Theorem14.GW2Shr

open GW2Schedule GW2TipSystem.Swc Exist Staged StagedLaw

/-- At a point of `ℍ`, a boundary value of the inverse Loewner map is its value. -/
theorem bdry_eq_of_mem_H {J : ℝ → ℝ} (hJ : Continuous J) (hJ0 : J 0 = 0) {T : ℝ} (hT : 0 ≤ T) {p q : ℂ}
    (hp : p ∈ H) (hg : Tendsto (fwdMapInv J T) (𝓝[H] p) (𝓝 q)) : q = fwdMapInv J T p := by
  have h2 : Tendsto (fwdMapInv J T) (𝓝[H] p) (𝓝 (fwdMapInv J T p)) :=
    (QuantumZipper.RS.differentiableOn_fwdMapInv hJ hJ0 hT).continuousOn p hp
  have : (𝓝[H] p).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (subset_closure hp)
  exact tendsto_nhds_unique hg h2

/-- **A boundary value of the inverse Loewner map at a real point is not a free point**: were it in `ℍ \ K_T`, the
forward map would be continuous there and would carry it back to the real point. -/
theorem bdry_notMem_of_real {J : ℝ → ℝ} (hJ : Continuous J) (hJ0 : J 0 = 0) {T : ℝ} (hT : 0 ≤ T) {p q : ℂ}
    (hp : p ∈ Hbar) (hpH : p ∉ H) (hg : Tendsto (fwdMapInv J T) (𝓝[H] p) (𝓝 q)) :
    q ∉ H \ fwdHull J T := by
  intro hq
  have hopen := QuantumZipper.FwdHolo.isOpen_compl_fwdHull hJ hT
  have hcont : ContinuousAt (QuantumZipper.fwdMap J T) q :=
    (QuantumZipper.FwdHolo.differentiableOn_fwdMap hJ hT).continuousOn.continuousAt (hopen.mem_nhds hq)
  have h1 : Tendsto (fun z => QuantumZipper.fwdMap J T (fwdMapInv J T z)) (𝓝[H] p)
      (𝓝 (QuantumZipper.fwdMap J T q)) := hcont.tendsto.comp hg
  have h2 : Tendsto (fun z => QuantumZipper.fwdMap J T (fwdMapInv J T z)) (𝓝[H] p) (𝓝 p) := by
    refine (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (QuantumZipper.RS.fwdMap_fwdMapInv hJ hJ0 hT hz).symm
  have : (𝓝[H] p).NeBot := mem_closure_iff_nhdsWithin_neBot.1 (by rw [closure_H]; exact hp)
  have heq := tendsto_nhds_unique h1 h2
  exact hpH (heq ▸ QuantumZipper.FwdHolo.mapsTo_fwdMap hJ hT hq)

/-- **The filled retained hull through a Loewner launch chart.** For a continuous driver `J` from `0` with boundary
limits at time `T`, two counterflow drivers `W_k`, `W'` with generating traces and a continuous monotone clock `ℓ`
from `0` relating their tips through `Chart.id.loewner J T` and the inversion, if the closure of the old hull
`K^J_T` misses that of the original counterflow's inverted hull at `ℓ t₀`, then the inverse Loewner map carries
`invHull W_k t₀` onto `invHull W' (ℓ t₀)`. Both hulls are fillings of their traces; the relative map of the launch
chart carries the original filling to the filling of the image trace (`Supp8.GB6.isFilling_relMap_image`), and the
traces agree in `ℍ` point by point (the tip relation; a real boundary value of the inverse map is never free). -/
theorem fwdMapInv_image_invHull {J : ℝ → ℝ} {T : ℝ} {Wk W' : ℝ≥0 → ℝ} {γk γ' : ℝ≥0 → ℂ} {ℓ : ℝ≥0 → ℝ≥0}
    (hJ : Continuous J) (hJ0 : J 0 = 0) (hT : 0 ≤ T) (hB : HasBdryLimits (fwdMapInv J T))
    (hWk : Continuous Wk) (hWk0 : Wk 0 = 0) (hγk : IsGeneratingTrace Wk ⊤ γk)
    (hW' : Continuous W') (hW'0 : W' 0 = 0) (hγ' : IsGeneratingTrace W' ⊤ γ')
    (hℓc : Continuous ℓ) (hℓm : Monotone ℓ) (hℓ0 : ℓ 0 = 0)
    (hiff : ∀ (r : ℝ≥0) (z : ℂ), ((Chart.id.loewner J T).trans infinitySourceChart).tipAt Wk r z ↔
      infinitySourceChart.tipAt W' (ℓ r) z) {t₀ : ℝ≥0}
    (hd : Disjoint (closure (fwdHull J T))
      (closure (Supp8.Q3Rel.invHull (fun r : ℝ => W' r.toNNReal) (ℓ t₀ : ℝ)))) :
    fwdMapInv J T '' Supp8.Q3Rel.invHull (fun r : ℝ => Wk r.toNNReal) (t₀ : ℝ) =
      Supp8.Q3Rel.invHull (fun r : ℝ => W' r.toNNReal) (ℓ t₀ : ℝ) := by
  have hU' : Continuous fun r : ℝ => W' r.toNNReal := hW'.comp continuous_real_toNNReal
  have hUk : Continuous fun r : ℝ => Wk r.toNNReal := hWk.comp continuous_real_toNNReal
  -- the inverted points of the original hull are free for the old hull
  have hfree : ∀ w ∈ fwdHull (fun r : ℝ => W' r.toNNReal) (ℓ t₀ : ℝ), -w⁻¹ ∈ H \ fwdHull J T := fun w hw =>
    ⟨GW2aPiece.neg_inv_mem_H ((isHPHull_fwdHull hU' (ℓ t₀).coe_nonneg).1 hw),
      fun hK => hd.ne_of_mem (subset_closure hK) (subset_closure ⟨w, hw, rfl⟩) rfl⟩
  have hrm : ∀ x, Supp8.GB6.relMap J T x = WangWu.negInv (QuantumZipper.fwdMap J T (WangWu.negInv x)) :=
    fun _ => rfl
  have hrelH : ∀ w ∈ fwdHull (fun r : ℝ => W' r.toNNReal) (ℓ t₀ : ℝ), Supp8.GB6.relMap J T w ∈ H :=
    fun w hw => GW2aPiece.neg_inv_mem_H (QuantumZipper.FwdHolo.mapsTo_fwdMap hJ hT (hfree w hw))
  have hS' : IsFilling (fwdHull (fun r : ℝ => W' r.toNNReal) (ℓ t₀ : ℝ)) (γ' '' Icc 0 (ℓ t₀)) :=
    hγ'.2.2 (ℓ t₀) ENNReal.coe_lt_top
  -- (A) the relative map of the launch chart carries the original filling
  have hA : IsFilling (Supp8.GB6.relMap J T '' fwdHull (fun r : ℝ => W' r.toNNReal) (ℓ t₀ : ℝ))
      (Supp8.GB6.relMap J T '' (γ' '' Icc 0 (ℓ t₀) ∩ H)) := by
    rcases hT.eq_or_lt with hT0 | hTpos
    · subst hT0
      have hid : ∀ w ∈ H, Supp8.GB6.relMap J 0 w = w := fun w hw => by
        have hw' := GW2aPiece.neg_inv_mem_H hw
        show -(QuantumZipper.fwdMap J 0 (-w⁻¹))⁻¹ = w
        rw [Ito.fwdMap_zero_eq_sub J hw', hJ0]
        simp only [Complex.ofReal_zero, sub_zero, inv_neg, inv_inv, neg_neg]
      have hK : fwdHull (fun r : ℝ => W' r.toNNReal) (ℓ t₀ : ℝ) ⊆ H :=
        (isHPHull_fwdHull hU' (ℓ t₀).coe_nonneg).1
      rw [image_congr fun w hw => hid w (hK hw), image_congr fun w hw => hid w hw.2, image_id', image_id']
      exact Sec5.CrossRestart.isFilling_inter_H_iff.2 hS'
    · obtain ⟨p, hp⟩ := hB 0 (by simp [Hbar])
      exact Supp8.GB6.isFilling_relMap_image hU' hJ hJ0 hTpos (ℓ t₀).coe_nonneg hp hd
        ⟨(ℓ t₀).coe_nonneg, le_rfl⟩ hS'
  -- (B) the tip relation, read on the traces
  obtain ⟨g, C, hg, hC⟩ := BRLeaf.hasProperBdryExt_id.loewner hJ hJ0 hT hB
  have hg' : ∀ p ∈ Hbar, Tendsto (fwdMapInv J T) (𝓝[H] p) (𝓝 (g p)) := hg
  have hrel : ∀ r : ℝ≥0, (γk r = 0 ↔ γ' (ℓ r) = 0) ∧
      (γk r ≠ 0 → g (WangWu.negInv (γk r)) = WangWu.negInv (γ' (ℓ r))) :=
    fun r => (BW1Det.tipRel_iff_traces hg hC hγk hWk hWk0 hγ' hW' hW'0 r (ℓ r)).1 (hiff r)
  have hrelEq : ∀ r : ℝ≥0, WangWu.negInv (γk r) ∈ H →
      fwdMapInv J T (WangWu.negInv (γk r)) = WangWu.negInv (γ' (ℓ r)) →
      Supp8.GB6.relMap J T (γ' (ℓ r)) = γk r := fun r hnH e => by
    rw [hrm, ← e, QuantumZipper.RS.fwdMap_fwdMapInv hJ hJ0 hT hnH, GW2Sgk.negInv_negInv]
  have hnegH : ∀ x : ℂ, WangWu.negInv x ∈ H → x ∈ H := fun x hx => by
    have := GW2aPiece.neg_inv_mem_H hx
    rwa [← WangWu.negInv, GW2Sgk.negInv_negInv] at this
  have hne0 : ∀ x : ℂ, x ∈ H → x ≠ 0 := fun x hx h => by
    rw [h] at hx
    exact (lt_irrefl _ (show (0 : ℂ).im > 0 from hx))
  -- (C) the traces agree in `ℍ`
  have hC' : γk '' Icc 0 t₀ ∩ H = Supp8.GB6.relMap J T '' (γ' '' Icc 0 (ℓ t₀) ∩ H) ∩ H := by
    ext z
    constructor
    · rintro ⟨⟨r, hr, rfl⟩, hzH⟩
      have hnH : WangWu.negInv (γk r) ∈ H := GW2aPiece.neg_inv_mem_H hzH
      have e := (hrel r).2 (hne0 _ hzH)
      rw [bdry_eq_of_mem_H hJ hJ0 hT hnH (hg' _ (QuantumZipper.H_subset_Hbar hnH))] at e
      have hfr := QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hJ hJ0 hT hnH
      rw [e] at hfr
      exact ⟨⟨γ' (ℓ r), ⟨⟨ℓ r, ⟨zero_le, hℓm hr.2⟩, rfl⟩, hnegH _ hfr.1⟩, hrelEq r hnH e⟩, hzH⟩
    · rintro ⟨⟨_, ⟨⟨u, hu, rfl⟩, hγH⟩, rfl⟩, -⟩
      have hIcc : u ∈ Icc (ℓ 0) (ℓ t₀) := by rw [hℓ0]; exact hu
      obtain ⟨r, hrI, rfl⟩ := intermediate_value_Icc (zero_le : (0 : ℝ≥0) ≤ t₀) hℓc.continuousOn hIcc
      have hne : γk r ≠ 0 := fun h => hne0 _ hγH ((hrel r).1.1 h)
      have e := (hrel r).2 hne
      have hq : WangWu.negInv (γ' (ℓ r)) ∈ H \ fwdHull J T :=
        hfree _ (Sec5.CrossRestart.inter_H_subset_of_isFilling hS' ⟨⟨ℓ r, hu, rfl⟩, hγH⟩)
      have hHb : WangWu.negInv (γk r) ∈ Hbar :=
        GW4Traverse.negInv_mem_Hbar (GW2aPiece.trace_mem_Hbar hγk hWk hWk0 r)
      have hnH : WangWu.negInv (γk r) ∈ H := by
        by_contra hc
        exact bdry_notMem_of_real hJ hJ0 hT hHb hc (hg' _ hHb) (e ▸ hq)
      rw [bdry_eq_of_mem_H hJ hJ0 hT hnH (hg' _ hHb)] at e
      refine ⟨⟨r, hrI, (hrelEq r hnH e).symm⟩, ?_⟩
      rw [hrelEq r hnH e]
      exact hnegH _ hnH
  -- (D) both hulls fill the same compact trace, so they agree
  have hγkc : Continuous γk := by
    have := hγk.2.1
    simp only [le_top, ofPred_true] at this
    exact continuousOn_univ.1 this
  have hcpt : IsCompact (γk '' Icc 0 t₀) := isCompact_Icc.image hγkc
  have hAk : IsFilling (fwdHull (fun r : ℝ => Wk r.toNNReal) (t₀ : ℝ)) (γk '' Icc 0 t₀) :=
    hγk.2.2 t₀ ENNReal.coe_lt_top
  have hA' : IsFilling (Supp8.GB6.relMap J T '' fwdHull (fun r : ℝ => W' r.toNNReal) (ℓ t₀ : ℝ))
      (γk '' Icc 0 t₀) := (Supp8.GB6.CoordB.isFilling_congr_inter_H hC'.symm).1 hA
  have e1 := (isFilling_iff_inter_H_eq_fillH hcpt.isBounded hcpt.isClosed).1 hAk
  have e2 := (isFilling_iff_inter_H_eq_fillH hcpt.isBounded hcpt.isClosed).1 hA'
  have hsub : Supp8.GB6.relMap J T '' fwdHull (fun r : ℝ => W' r.toNNReal) (ℓ t₀ : ℝ) ⊆ H := by
    rintro _ ⟨w, hw, rfl⟩
    exact hrelH w hw
  have hKeq : fwdHull (fun r : ℝ => Wk r.toNNReal) (t₀ : ℝ) =
      Supp8.GB6.relMap J T '' fwdHull (fun r : ℝ => W' r.toNNReal) (ℓ t₀ : ℝ) := by
    rw [← inter_eq_left.2 (isHPHull_fwdHull hUk t₀.coe_nonneg).1, e1, ← e2, inter_eq_left.2 hsub]
  -- (E) invert
  show fwdMapInv J T '' ((fun z : ℂ => -z⁻¹) '' fwdHull (fun r : ℝ => Wk r.toNNReal) (t₀ : ℝ)) =
    (fun z : ℂ => -z⁻¹) '' fwdHull (fun r : ℝ => W' r.toNNReal) (ℓ t₀ : ℝ)
  rw [hKeq, image_image, image_image]
  refine image_congr fun w hw => ?_
  show fwdMapInv J T (-(-(QuantumZipper.fwdMap J T (-w⁻¹))⁻¹)⁻¹) = -w⁻¹
  rw [inv_neg, inv_inv, neg_neg]
  exact QuantumZipper.RS.fwdMapInv_fwdMap hJ hJ0 hT (hfree w hw)

/-- **Charts agreeing on `ℍ` have the same tips** (through the inversion). -/
theorem tipAt_trans_congr {c d : Chart} (hcd : ∀ z ∈ H, c.2.1 z = d.2.1 z) {W : ℝ≥0 → ℝ} (hW : Continuous W)
    (hW0 : W 0 = 0) (r : ℝ≥0) (z : ℂ) :
    (c.trans infinitySourceChart).tipAt W r z ↔ (d.trans infinitySourceChart).tipAt W r z := by
  have hU : Continuous fun s : ℝ => W s.toNNReal := hW.comp continuous_real_toNNReal
  have hU0 : (fun s : ℝ => W s.toNNReal) 0 = 0 := by simpa using hW0
  have heq : ∀ y : ℝ, 0 < y →
      (c.trans infinitySourceChart).2.1 (fwdMapInv (fun s : ℝ => W s.toNNReal) r (y * Complex.I)) =
        (d.trans infinitySourceChart).2.1 (fwdMapInv (fun s : ℝ => W s.toNNReal) r (y * Complex.I)) := by
    intro y hy
    have hmem : fwdMapInv (fun s : ℝ => W s.toNNReal) r (y * Complex.I) ∈ H :=
      QuantumZipper.RS.fwdMapInv_mem_H hU hU0 (NNReal.coe_nonneg r)
        (show 0 < ((y : ℂ) * Complex.I).im by simpa using hy)
    exact hcd _ (GW2aPiece.neg_inv_mem_H hmem)
  unfold Chart.tipAt
  constructor
  · intro h
    exact h.congr' (eventually_nhdsWithin_of_forall fun y hy => heq y hy)
  · intro h
    exact h.congr' (eventually_nhdsWithin_of_forall fun y hy => (heq y hy).symm)

/-- **Inverted hulls lie in `ℍ`.** -/
theorem invHull_subset_H {U : ℝ → ℝ} (hU : Continuous U) {σ : ℝ} (hσ : 0 ≤ σ) :
    Supp8.Q3Rel.invHull U σ ⊆ H := by
  rintro _ ⟨w, hw, rfl⟩
  exact GW2aPiece.neg_inv_mem_H ((isHPHull_fwdHull hU hσ).1 hw)

/-- **The stage's filled retained hull is the launch chart's image of the original one** (root `0`): the launch
chart's inverse carries the conditional counterflow's inverted hull at `t₀` onto the original counterflow's inverted
hull at `ℓ t₀`, as long as the latter's closure misses that of the launched pieces' hull. -/
theorem invHull_eq_launch {Δ : ℕ → ℝ≥0∞} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ}
    (hc : ∀ j < k, Continuous (stopDrv (Δ j) (D j)) ∧ stopDrv (Δ j) (D j) 0 = 0)
    (hext : GW1P.HasProperBdryExt (succChart 0 Δ D k)) {Wk W' : ℝ≥0 → ℝ} {γk γ' : ℝ≥0 → ℂ}
    (hWk : Continuous Wk) (hWk0 : Wk 0 = 0) (hγk : IsGeneratingTrace Wk ⊤ γk)
    (hW' : Continuous W') (hW'0 : W' 0 = 0) (hγ' : IsGeneratingTrace W' ⊤ γ')
    {ℓ : ℝ≥0 → ℝ≥0} (hℓc : Continuous ℓ) (hℓm : Monotone ℓ) (hℓ0 : ℓ 0 = 0)
    (hiff : ∀ (r : ℝ≥0) (z : ℂ), ((succChart 0 Δ D k).trans infinitySourceChart).tipAt Wk r z ↔
      infinitySourceChart.tipAt W' (ℓ r) z) {t₀ : ℝ≥0}
    (hd : Disjoint (closure (fwdHull (joinDrv Δ D k) (joinTime Δ D k)))
      (closure (Supp8.Q3Rel.invHull (fun r : ℝ => W' r.toNNReal) (ℓ t₀ : ℝ)))) :
    (succChart 0 Δ D k).2.1 '' Supp8.Q3Rel.invHull (fun r : ℝ => Wk r.toNNReal) (t₀ : ℝ) =
      Supp8.Q3Rel.invHull (fun r : ℝ => W' r.toNNReal) (ℓ t₀ : ℝ) := by
  obtain ⟨hJ, hJ0⟩ := continuous_joinDrv hc
  have hT := joinTime_nonneg Δ D k
  have hinv : ∀ z ∈ H, (succChart 0 Δ D k).2.1 z = (Chart.id.loewner (joinDrv Δ D k) (joinTime Δ D k)).2.1 z :=
    fun z hz => by
      rw [succChart_inv_eq 0 hc hz]
      simp only [Complex.ofReal_zero, zero_add]
      rfl
  have hiff' : ∀ (r : ℝ≥0) (z : ℂ),
      ((Chart.id.loewner (joinDrv Δ D k) (joinTime Δ D k)).trans infinitySourceChart).tipAt Wk r z ↔
        infinitySourceChart.tipAt W' (ℓ r) z := fun r z =>
    (tipAt_trans_congr hinv hWk hWk0 r z).symm.trans (hiff r z)
  have hB : HasBdryLimits (fwdMapInv (joinDrv Δ D k) (joinTime Δ D k)) := by
    obtain ⟨f, -, hf, -⟩ := hext
    intro p hp
    refine ⟨f p, (hf p hp).congr' (eventually_nhdsWithin_of_forall fun z hz => ?_)⟩
    rw [hinv z hz]
    rfl
  have hHull : Supp8.Q3Rel.invHull (fun r : ℝ => Wk r.toNNReal) (t₀ : ℝ) ⊆ H :=
    invHull_subset_H (hWk.comp continuous_real_toNNReal) t₀.coe_nonneg
  rw [image_congr fun z hz => hinv z (hHull hz)]
  exact fwdMapInv_image_invHull hJ hJ0 hT hB hWk hWk0 hγk hW' hW'0 hγ' hℓc hℓm hℓ0 hiff' hd

end InteractingSLE.Theorem14.GW2Shr
