/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4FixPhysGeom
import InteractingSLE.Spec.Supplement.RelSafeGB6Local
import InteractingSLE.Spec.Supplement.GB6CoordBMeasLocal

/-!
# GW4's local relative curves read from the physical driver: measurability

Packet PROVE-T14-GW4FIX (continuation). For a process `W'` on a space with a σ-algebra `m` that reads `W'` on `[0, t]`
and contains a good set `GT` on which every path is good (`Frame.IsPathOk`):

* `sTr`: the trace frozen at `t` on `GT` (`0` off it) — continuous for every sample, `m`-measurable at each time;
* deterministic hitting facts through GB6's compact gap `SourceC.prefixGap` (`firstVisit_le_iff`,
  `lt_firstVisit_iff`);
* `locEv F W' GT T = {ω ∈ GT | τ < T < σ}`, **`measurableSet_locEv`** (`T ≤ t`);
* `entV`: the entry time from countably many gap tests, `measurable_entV`, `entV_eq`;
* **`measurable_indicator_curve`**: on `locEv`, every evaluation of the local curve is `m`-measurable (the trace at the
  random time `τ + clockOf (T − τ) u ≤ T`, read through a Borel modification of `relPt` on the closed pocket);
* `locLife`, `locDrv` and their measurability (`CoordB.measurable_indicator_capLife`, `_drivenDriver`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull)

namespace InteractingSLE.Theorem14.GW4Fix

open GW4Traverse GW4Reg GB11Conn GB11Chart GW4Rel Sec7.PocketTraversal Sec7.Lemma71C Supp8.GB6.SourceC

/-! ### Hitting a point, read through the compact gap -/

section Hit

variable {X : ℝ≥0 → ℂ} {p : ℂ}

theorem hit_iff (z : ℂ) : (z ≠ 0 ∧ -z⁻¹ = p) ↔ z * p + 1 = 0 := by
  constructor
  · rintro ⟨hz, he⟩
    rw [← he]
    field_simp
    ring
  · intro h
    have hz : z ≠ 0 := by
      rintro rfl
      simp at h
    refine ⟨hz, ?_⟩
    field_simp
    linear_combination -h

/-- **No visit up to `x`** is a positive gap on `[0, x]`. -/
theorem lt_firstVisit_iff (hX : Continuous X) (x : ℝ≥0) :
    (x : ℝ≥0∞) < GB11.firstVisit X p ↔ 0 < prefixGap X (fun _ => p) x 0 := by
  rw [prefixGap_pos_iff hX continuous_const]
  constructor
  · intro hlt v hv u _ h0
    have hvx : GB11.firstVisit X p ≤ v := iInf₂_le v ((hit_iff _).2 h0)
    exact absurd (hvx.trans (ENNReal.coe_le_coe.2 hv.2)) (not_le.2 hlt)
  · intro hno
    by_contra hle
    have hfin : GB11.firstVisit X p < ⊤ := lt_of_le_of_lt (le_of_not_gt hle) ENNReal.coe_lt_top
    obtain ⟨s₀, hs₀, hne, hps⟩ := exists_eq_firstVisit hX hfin
    have hs₀x : s₀ ≤ x := by
      rw [← ENNReal.coe_le_coe, hs₀]
      exact le_of_not_gt hle
    exact hno s₀ ⟨zero_le, hs₀x⟩ 0 ⟨le_rfl, le_rfl⟩ ((hit_iff _).1 ⟨hne, hps⟩)

/-- **A first visit at or before `x`** is a zero gap on `[0, x]`. -/
theorem firstVisit_le_iff (hX : Continuous X) (x : ℝ≥0) :
    GB11.firstVisit X p ≤ x ↔ prefixGap X (fun _ => p) x 0 = 0 := by
  rw [← not_lt, lt_firstVisit_iff hX, pos_iff_ne_zero, not_not]

theorem firstVisit_zero (X : ℝ≥0 → ℂ) : GB11.firstVisit X 0 = ⊤ := by
  refine le_antisymm le_top (le_iInf₂ fun t ht => ?_)
  exact absurd ht.2 (neg_ne_zero.2 (inv_ne_zero ht.1))

/-- The gap only reads the path on `[0, x]`. -/
theorem prefixGap_congr {X Y : ℝ≥0 → ℂ} {x : ℝ≥0} (h : ∀ v ≤ x, X v = Y v) (α : ℝ≥0 → ℂ) :
    prefixGap X α x 0 = prefixGap Y α x 0 := by
  unfold prefixGap
  exact iInf_congr fun q => by rw [h q.1.val q.1.2.2]

end Hit

/-! ### A Borel reading of the relative point on the closed pocket -/

theorem measurableSet_relDomBar (C E : Set ℂ) (P : ℂ) : MeasurableSet (relDomBar C E P) := by
  have hf : Measurable fun w : ℂ => -w⁻¹ := measurable_inv.neg
  have h1 : MeasurableSet {w : ℂ | w = 0 ∧ E = ∅} := (measurableSet_singleton 0).inter (MeasurableSet.const _)
  have h2 : MeasurableSet {w : ℂ | w ≠ 0 ∧ -w⁻¹ ∈ closure C ∧ -w⁻¹ ≠ P} :=
    (measurableSet_singleton 0).compl.inter ((hf isClosed_closure.measurableSet).inter
      (hf (measurableSet_singleton P).compl))
  exact h1.union h2

open Classical in
/-- The relative point on the closed pocket, `0` elsewhere (Borel). -/
def relPtB (C E : Set ℂ) (P : ℂ) (ψ : ℂ → ℂ) (k : ℝ) : ℂ → ℂ := (relDomBar C E P).piecewise (relPt E ψ k) 0

namespace Frame

variable {F : Frame}

theorem measurable_relPtB (hF : F.IsOk) : Measurable (relPtB F.C F.E (F.αR F.s₁) F.ψ F.k) := by
  classical
  obtain ⟨hpc, hEcl, -, hψE, -, hψinf, -, -⟩ := hF.2.2.2.2.2
  exact (continuousOn_relPt hpc hEcl hψE hψinf).measurable_piecewise continuousOn_const
    (measurableSet_relDomBar _ _ _)

/-! ### The frozen trace and the local events -/

section Omega

variable {Ω : Type*} {W' : ℝ≥0 → Ω → ℝ} {GT : Set Ω}

open Classical in
/-- The trace frozen at `t` on the good set (`0` off it). -/
def sTr (W' : ℝ≥0 → Ω → ℝ) (GT : Set Ω) (t : ℝ≥0) (ω : Ω) : ℝ≥0 → ℂ :=
  if ω ∈ GT then fun v => trc (fun r => W' r ω) (min v t) else 0

variable (F) in
/-- **The local event at horizon `T`**: a good sample with `τ < T < σ`. -/
def locEv (W' : ℝ≥0 → Ω → ℝ) (GT : Set Ω) (T : ℝ≥0) : Set Ω :=
  {ω | ω ∈ GT ∧ F.ent (fun r => W' r ω) < T ∧ (T : ℝ≥0∞) < F.exit (fun r => W' r ω)}

theorem sTr_eq {t v : ℝ≥0} {ω : Ω} (hω : ω ∈ GT) (hv : v ≤ t) : sTr W' GT t ω v = trc (fun r => W' r ω) v := by
  simp only [sTr, hω, ↓reduceIte, min_eq_left hv]

variable (hGT : ∀ ω ∈ GT, F.IsPathOk (fun r => W' r ω))
include hGT

theorem isLoc_of_mem_locEv {T : ℝ≥0} {ω : Ω} (h : ω ∈ F.locEv W' GT T) : F.IsLoc (fun r => W' r ω) T :=
  ⟨hGT ω h.1, h.2.1, h.2.2⟩

theorem continuous_sTr (t : ℝ≥0) (ω : Ω) : Continuous (sTr W' GT t ω) := by
  classical
  by_cases hω : ω ∈ GT
  · simp only [sTr, hω, ↓reduceIte]
    exact (continuous_trc (hGT ω hω)).comp (continuous_id.min continuous_const)
  · simp only [sTr, hω, ↓reduceIte]
    exact continuous_const

variable {m : MeasurableSpace Ω} {t : ℝ≥0} (hW : ∀ r ≤ t, Measurable[m] (W' r)) (hGTm : MeasurableSet[m] GT)
include hW hGTm

omit hGT in
theorem measurable_sTr (v : ℝ≥0) : Measurable[m] fun ω => sTr W' GT t ω v := by
  classical
  have e : (fun ω => sTr W' GT t ω v) = fun ω => if ω ∈ GT then trc (fun r => W' r ω) (min v t) else 0 := by
    funext ω
    by_cases hω : ω ∈ GT <;> simp only [sTr, hω, ↓reduceIte, Pi.zero_apply]
  rw [e]
  exact Measurable.ite hGTm (Supp8.RelSafe.measurable_phTr (W := W') hW (min_le_right v t)) measurable_const

theorem measurable_gap (p : ℂ) (x : ℝ≥0) : Measurable[m] fun ω => prefixGap (sTr W' GT t ω) (fun _ => p) x 0 :=
  measurable_prefixGap (continuous_sTr hGT t) (fun _ => continuous_const) (measurable_sTr hW hGTm)
    (fun _ => measurable_const) x 0

omit hGT hW hGTm in
theorem gap_eq {ω : Ω} (hω : ω ∈ GT) {x : ℝ≥0} (hx : x ≤ t) (p : ℂ) :
    prefixGap (sTr W' GT t ω) (fun _ => p) x 0 = prefixGap (trc (fun r => W' r ω)) (fun _ => p) x 0 :=
  prefixGap_congr (fun _ hv => sTr_eq hω (hv.trans hx)) _

theorem measurableSet_lt_exit {T : ℝ≥0} (hT : T ≤ t) :
    MeasurableSet[m] {ω | ω ∈ GT ∧ (T : ℝ≥0∞) < F.exit (fun r => W' r ω)} := by
  have e : {ω | ω ∈ GT ∧ (T : ℝ≥0∞) < F.exit (fun r => W' r ω)} =
      GT ∩ {ω | 0 < prefixGap (sTr W' GT t ω) (fun _ => F.αR F.s₁) T 0} := by
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff]
    constructor
    · rintro ⟨hω, h⟩
      exact ⟨hω, by rw [gap_eq hω hT]; exact (lt_firstVisit_iff (continuous_trc (hGT ω hω)) T).1 h⟩
    · rintro ⟨hω, h⟩
      exact ⟨hω, (lt_firstVisit_iff (continuous_trc (hGT ω hω)) T).2 (by rwa [gap_eq hω hT] at h)⟩
  rw [e]
  exact hGTm.inter (measurableSet_lt measurable_const (measurable_gap hGT hW hGTm _ T))

end Omega

/-! ### The entry time -/

section Entry

theorem entryPt_ne_zero (hF : F.IsOk) (hs₂ : F.s₂ ≠ ⊤) : F.αR F.s₂.toNNReal ≠ 0 := by
  obtain ⟨-, -, hE0, -, -, -, -, hcase⟩ := hF.2.2.2.2.2
  rcases hcase with ⟨-, h⟩ | ⟨hEQ, -⟩
  · exact absurd h hs₂
  · intro h0
    exact hE0 (by rw [hEQ, h0]; exact mem_singleton _)

theorem ent_eq_zero {w : ℝ≥0 → ℝ} (hs₂ : F.s₂ = ⊤) : F.ent w = 0 := by
  simp only [ent, entryTime, hs₂, ↓reduceIte]

theorem coe_ent (hF : F.IsOk) {w : ℝ≥0 → ℝ} (hw : F.IsPathOk w) (hs₂ : F.s₂ ≠ ⊤) :
    (F.ent w : ℝ≥0∞) = GB11.firstVisit (trc w) (F.αR F.s₂.toNNReal) := by
  have hfin : GB11.firstVisit (trc w) (F.αR F.s₂.toNNReal) < ⊤ :=
    firstVisit_lt_top_of_ne_zero hw.2.2.2.2.1.2.2.1 hw.2.2.2.2.2.2.2.2.2.1 (entryPt_ne_zero hF hs₂)
  simp only [ent, entryTime, hs₂, ↓reduceIte, ENNReal.coe_toNNReal hfin.ne]

end Entry

section OmegaEnt

variable {Ω : Type*} {W' : ℝ≥0 → Ω → ℝ} {GT : Set Ω}

open Classical in
variable (F) in
/-- **The entry time read from countably many gap tests** (`0` for an unbounded pocket). -/
def entV (W' : ℝ≥0 → Ω → ℝ) (GT : Set Ω) (t : ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
  if F.s₂ = ⊤ then 0 else ⨅ r : ℚ, if 0 ≤ (r : ℝ) ∧ (r : ℝ) ≤ t ∧
    prefixGap (sTr W' GT t ω) (fun _ => F.αR F.s₂.toNNReal) (r : ℝ).toNNReal 0 = 0 then ENNReal.ofReal r else ⊤

variable (hF : F.IsOk) (hGT : ∀ ω ∈ GT, F.IsPathOk (fun r => W' r ω))
include hF hGT

/-- On the local event the gap tests read the entry time. -/
theorem entV_eq {t T : ℝ≥0} (hT : T ≤ t) {ω : Ω} (hω : ω ∈ F.locEv W' GT T) :
    F.entV W' GT t ω = F.ent (fun r => W' r ω) := by
  classical
  have hw := hGT ω hω.1
  by_cases hs₂ : F.s₂ = ⊤
  · simp only [entV, hs₂, ↓reduceIte, ent_eq_zero hs₂, ENNReal.coe_zero]
  simp only [entV, hs₂, ↓reduceIte]
  have hX := continuous_trc hw
  have hcond : ∀ r : ℚ, 0 ≤ (r : ℝ) → (r : ℝ) ≤ t →
      (prefixGap (sTr W' GT t ω) (fun _ => F.αR F.s₂.toNNReal) (r : ℝ).toNNReal 0 = 0 ↔
        (F.ent (fun r => W' r ω) : ℝ≥0∞) ≤ ENNReal.ofReal r) := fun r hr0 hrt => by
    rw [gap_eq hω.1 (Real.toNNReal_le_iff_le_coe.2 hrt), ← firstVisit_le_iff hX, coe_ent hF hw hs₂]
    rfl
  refine le_antisymm ?_ (le_iInf fun r => ?_)
  · refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
    have hlt : (F.ent (fun r => W' r ω) : ℝ≥0∞) < min c T :=
      lt_min hc (ENNReal.coe_lt_coe.2 hω.2.1)
    obtain ⟨q, hq0, hq1, hq2⟩ := ENNReal.lt_iff_exists_rat_btwn.1 hlt
    have hqT : ENNReal.ofReal q < T := hq2.trans_le (min_le_right _ _)
    have hqt : (q : ℝ) ≤ t := by
      have h1 := (ENNReal.ofReal_lt_iff_lt_toReal (by exact_mod_cast hq0) ENNReal.coe_ne_top).1 hqT
      rw [ENNReal.coe_toReal] at h1
      exact h1.le.trans (NNReal.coe_le_coe.2 hT)
    have hq0' : (0 : ℝ) ≤ q := by exact_mod_cast hq0
    refine (iInf_le _ q).trans ?_
    rw [ite_eq_left (show _ from ⟨hq0', hqt, (hcond q hq0' hqt).2 hq1.le⟩)]
    exact hq2.le.trans (min_le_left _ _)
  · split_ifs with h
    · exact (hcond r h.1 h.2.1).1 h.2.2
    · exact le_top

variable {m : MeasurableSpace Ω} {t : ℝ≥0} (hW : ∀ r ≤ t, Measurable[m] (W' r)) (hGTm : MeasurableSet[m] GT)
include hW hGTm

omit hF in
theorem measurable_entV : Measurable[m] (F.entV W' GT t) := by
  classical
  show Measurable fun ω => F.entV W' GT t ω
  by_cases hs₂ : F.s₂ = ⊤
  · simp only [entV, hs₂, ↓reduceIte]
    exact measurable_const
  · simp only [entV, hs₂, ↓reduceIte]
    refine Measurable.iInf fun r => Measurable.ite ?_ measurable_const measurable_const
    exact (MeasurableSet.const _).inter ((MeasurableSet.const _).inter
      (measurableSet_eq_fun (measurable_gap hGT hW hGTm _ _) measurable_const))

/-- The entry event `{τ < T}` is readable at `t ≥ T`. -/
theorem measurableSet_ent_lt {T : ℝ≥0} (hT : T ≤ t) :
    MeasurableSet[m] {ω | ω ∈ GT ∧ F.ent (fun r => W' r ω) < T} := by
  by_cases hs₂ : F.s₂ = ⊤
  · simp only [ent_eq_zero hs₂]
    exact hGTm.inter (MeasurableSet.const _)
  have e : {ω | ω ∈ GT ∧ F.ent (fun r => W' r ω) < T} = GT ∩ ⋃ (q : ℚ) (_ : 0 ≤ (q : ℝ) ∧ (q : ℝ) < T),
      {ω | prefixGap (sTr W' GT t ω) (fun _ => F.αR F.s₂.toNNReal) (q : ℝ).toNNReal 0 = 0} := by
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iUnion, exists_prop]
    constructor
    · rintro ⟨hω, h⟩
      refine ⟨hω, ?_⟩
      obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (NNReal.coe_lt_coe.2 h)
      have hq0 : (0 : ℝ) ≤ q := (NNReal.coe_nonneg _).trans hq1.le
      refine ⟨q, ⟨hq0, hq2⟩, ?_⟩
      rw [gap_eq hω ((Real.toNNReal_le_iff_le_coe.2 hq2.le).trans hT), ← firstVisit_le_iff
        (continuous_trc (hGT ω hω)), ← coe_ent hF (hGT ω hω) hs₂, ENNReal.coe_le_coe]
      exact Real.le_toNNReal_iff_coe_le hq0 |>.2 hq1.le
    · rintro ⟨hω, q, ⟨hq0, hqT⟩, hq⟩
      refine ⟨hω, ?_⟩
      rw [gap_eq hω ((Real.toNNReal_le_iff_le_coe.2 hqT.le).trans hT), ← firstVisit_le_iff
        (continuous_trc (hGT ω hω)), ← coe_ent hF (hGT ω hω) hs₂, ENNReal.coe_le_coe] at hq
      exact hq.trans_lt ((Real.toNNReal_lt_iff_lt_coe hq0).2 hqT)
  rw [e]
  exact hGTm.inter (MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun _ =>
    measurableSet_eq_fun (measurable_gap hGT hW hGTm _ _) measurable_const)

/-- **The local event is readable at `t ≥ T`.** -/
theorem measurableSet_locEv {T : ℝ≥0} (hT : T ≤ t) : MeasurableSet[m] (F.locEv W' GT T) := by
  have e : F.locEv W' GT T = {ω | ω ∈ GT ∧ F.ent (fun r => W' r ω) < T} ∩
      {ω | ω ∈ GT ∧ (T : ℝ≥0∞) < F.exit (fun r => W' r ω)} := by
    ext ω
    simp only [locEv, mem_ofPred_eq, mem_inter_iff]
    tauto
  rw [e]
  exact (measurableSet_ent_lt hF hGT hW hGTm hT).inter (measurableSet_lt_exit hGT hW hGTm hT)

end OmegaEnt

/-! ### The local curves and their drivers are readable -/

section OmegaCurve

variable {Ω : Type*} {W' : ℝ≥0 → Ω → ℝ} {GT : Set Ω}

variable (F) in
/-- The physical time read at the curve time `u`, from the measurable entry time. -/
def rtime (W' : ℝ≥0 → Ω → ℝ) (GT : Set Ω) (t T : ℝ≥0) (u : ℝ) (ω : Ω) : ℝ≥0 :=
  (F.entV W' GT t ω).toNNReal + (clockOf ((T : ℝ) - (F.entV W' GT t ω).toNNReal) u).toNNReal

variable (F) in
/-- The local lifetime with horizon `T` on its event (`0` off it). -/
def locLife (W' : ℝ≥0 → Ω → ℝ) (GT : Set Ω) (T : ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
  (F.locEv W' GT T).indicator (fun ω => capLife (F.curve (fun r => W' r ω) T)) ω

variable (F) in
/-- The local relative driver with horizon `T` on its event (`0` off it). -/
def locDrv (W' : ℝ≥0 → Ω → ℝ) (GT : Set Ω) (T u : ℝ≥0) (ω : Ω) : ℝ :=
  (F.locEv W' GT T).indicator (Supp8.GB6.CoordB.drivenDriver (fun ω => F.curve (fun r => W' r ω) T) u) ω

variable (hF : F.IsOk) (hGT : ∀ ω ∈ GT, F.IsPathOk (fun r => W' r ω))
include hF hGT

/-- On the local event the curve is the Borel relative point of the frozen trace at the read time. -/
theorem curve_eq {t T : ℝ≥0} (hT : T ≤ t) {ω : Ω} (hω : ω ∈ F.locEv W' GT T) {u : ℝ} (hu : 0 ≤ u) :
    F.curve (fun r => W' r ω) T u =
      relPtB F.C F.E (F.αR F.s₁) F.ψ F.k (sTr W' GT t ω (F.rtime W' GT t T u ω)) := by
  classical
  have hw := hGT ω hω.1
  have he : (F.entV W' GT t ω).toNNReal = F.ent (fun r => W' r ω) := by
    rw [entV_eq hF hGT hT hω, ENNReal.toNNReal_coe]
  have hL0 : (0 : ℝ) < (T : ℝ) - F.ent (fun r => W' r ω) := sub_pos.2 (NNReal.coe_lt_coe.2 hω.2.1)
  set ρ : ℝ≥0 := F.ent (fun r => W' r ω) + (clockOf ((T : ℝ) - F.ent (fun r => W' r ω)) u).toNNReal with hρ
  have hrt : F.rtime W' GT t T u ω = ρ := by simp only [rtime, he, hρ]
  have hρT : ρ < T := by
    rw [← NNReal.coe_lt_coe, hρ, NNReal.coe_add, Real.coe_toNNReal _ (clockOf_nonneg hL0 hu)]
    have := clockOf_lt hL0 hu
    linarith
  rw [hrt, sTr_eq hω.1 (hρT.le.trans hT)]
  have hmem := trc_mem_relDomBar hF hw (le_self_add : F.ent (fun r => W' r ω) ≤ ρ)
    (lt_trans (ENNReal.coe_lt_coe.2 hρT) hω.2.2)
  have hmem' : trc (fun r => W' r ω) ρ ∈ relDomBar F.C F.E (F.αR F.s₁) := hmem
  rw [relPtB, Set.piecewise_eq_of_mem _ _ _ hmem']
  rfl

variable {m : MeasurableSpace Ω} {t : ℝ≥0} (hW : ∀ r ≤ t, Measurable[m] (W' r)) (hGTm : MeasurableSet[m] GT)
include hW hGTm

omit hF in
theorem measurable_rtime (T : ℝ≥0) (u : ℝ) : Measurable[m] (F.rtime W' GT t T u) := by
  have hE : Measurable[m] fun ω => (F.entV W' GT t ω).toNNReal :=
    ENNReal.measurable_toNNReal.comp (measurable_entV hGT hW hGTm)
  have ha : Measurable[m] fun ω => ((F.entV W' GT t ω).toNNReal : ℝ) := measurable_coe_nnreal_real.comp hE
  show Measurable[m] fun ω => (F.entV W' GT t ω).toNNReal +
    (((T : ℝ) - (F.entV W' GT t ω).toNNReal) * (u / (1 + u))).toNNReal
  exact hE.add (measurable_real_toNNReal.comp ((measurable_const.sub ha).mul_const _))

/-- **Every evaluation of the local curve is readable on the local event.** -/
theorem measurable_indicator_curve {T : ℝ≥0} (hT : T ≤ t) (u : ℝ) (hu : 0 ≤ u) :
    Measurable[m] ((F.locEv W' GT T).indicator fun ω => F.curve (fun r => W' r ω) T u) := by
  have e : (F.locEv W' GT T).indicator (fun ω => F.curve (fun r => W' r ω) T u) =
      (F.locEv W' GT T).indicator (fun ω =>
        relPtB F.C F.E (F.αR F.s₁) F.ψ F.k (sTr W' GT t ω (F.rtime W' GT t T u ω))) :=
    indicator_congr fun ω hω => curve_eq hF hGT hT hω hu
  rw [e]
  refine Measurable.indicator ?_ (measurableSet_locEv hF hGT hW hGTm hT)
  have hj : Measurable (Function.uncurry fun (v : ℝ≥0) (ω : Ω) => sTr W' GT t ω v) :=
    measurable_uncurry_of_continuous_of_measurable (fun ω => continuous_sTr hGT t ω)
      (fun v => measurable_sTr hW hGTm v)
  exact (measurable_relPtB hF).comp (hj.comp ((measurable_rtime hGT hW hGTm T u).prodMk measurable_id))

theorem measurable_locLife {T : ℝ≥0} (hT : T ≤ t) : Measurable[m] (F.locLife W' GT T) :=
  Supp8.GB6.CoordB.measurable_indicator_capLife (measurableSet_locEv hF hGT hW hGTm hT)
    (fun _ hω => isDrivenCurve_curve hF (isLoc_of_mem_locEv hGT hω))
    (fun u hu => measurable_indicator_curve hF hGT hW hGTm hT u hu)

theorem measurable_locDrv {T : ℝ≥0} (hT : T ≤ t) (u : ℝ≥0) : Measurable[m] (F.locDrv W' GT T u) :=
  Supp8.GB6.CoordB.measurable_indicator_drivenDriver (measurableSet_locEv hF hGT hW hGTm hT)
    (fun _ hω => isDrivenCurve_curve hF (isLoc_of_mem_locEv hGT hω))
    (fun u hu => measurable_indicator_curve hF hGT hW hGTm hT u hu) u

end OmegaCurve

end Frame

end InteractingSLE.Theorem14.GW4Fix
