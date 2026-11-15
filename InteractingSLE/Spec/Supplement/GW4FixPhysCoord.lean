/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4FixPhysMeas
import InteractingSLE.Spec.Supplement.RelSafeGB6Drv

/-!
# GW4's measurable relative coordinates (`GW4RelCoordStatement` proved)

Packet PROVE-T14-GW4FIX (continuation). From the local curves of all rational horizons:

* **`segDrv_curve_eq`** (deterministic): the local drivers of two horizons agree below both lifetimes (Loewner
  uniqueness `eq_segDrv_of_clockHull` with a local driver of the first curve);
* `hzAll k`: the rational horizons; the coordinates `coordD` (the local driver of the first horizon whose curve lives
  past `u`) and `coordL` (the supremum of the local lifetimes), `0` and `∞` off the good set;
* their measurability, continuity, the hull clause and the exhaustion of the bounded relative hulls;
* **`gw4RelCoordStatement`**: `GW4RelCoordStatement` from Theorem 1.3 and the walks' barrier with its pocket shape —
  the measurability named input of `GW4Fix.gw4RelativeLawRegStatement_of_coord_relSafe` is discharged.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull)

universe u

namespace InteractingSLE.Theorem14.GW4Fix

open GW4Traverse GW4Reg GB11Conn GB11Chart GW4Rel Sec7.PocketTraversal Sec7.Lemma71C

namespace Frame

variable {F : Frame}

/-! ### Two horizons give the same driver -/

/-- **The local drivers of two horizons agree below both lifetimes.** -/
theorem segDrv_curve_eq (hF : F.IsOk) {w : ℝ≥0 → ℝ} {T₁ T₂ : ℝ≥0} (h₁ : F.IsLoc w T₁) (h₂ : F.IsLoc w T₂)
    {u : ℝ≥0} (hu₁ : (u : ℝ≥0∞) < capLife (F.curve w T₁)) (hu₂ : (u : ℝ≥0∞) < capLife (F.curve w T₂)) :
    segDrv (F.curve w T₂) u = segDrv (F.curve w T₁) u := by
  have hcv := isDrivenCurve_curve hF h₁
  have hu₁' : ENNReal.ofReal (u : ℝ) < capLife (F.curve w T₁) := by rwa [ENNReal.ofReal_coe_nnreal]
  obtain ⟨n, hn⟩ := exists_lt_capClock_of_lt_capLife hu₁'
  have hn0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  obtain ⟨W, hW, hW0, -, -, -, hK⟩ := hcv.localDriver ((n : ℝ) + 1) hn0
  have hnS : capClock (F.curve w T₁) n ≤ capClock (F.curve w T₁) ((n : ℝ) + 1) :=
    hcv.strictMonoOn_capClock.monotoneOn (mem_Ici.2 (Nat.cast_nonneg n)) (mem_Ici.2 hn0.le) (by linarith)
  have h1 : segDrv (F.curve w T₁) u = W u :=
    hcv.segDrv_eq hn0 hW hW0 (fun t ht => (hK t ht).2) u.coe_nonneg (hn.le.trans hnS)
  rw [h1]
  refine eq_segDrv_of_clockHull hF h₂ hW hW0 hu₂ fun t ht0 htT₂ htu => ?_
  have htT₁ : t < T₁ := by
    by_contra hle
    replace hle := le_of_not_gt hle
    obtain ⟨t', ht'0, ht'T, hlt⟩ := exists_lt_rcap_of_lt_capLife hF h₁ hu₁
    have hmono := rcap_mono hF h₂ ht'0 (ht'T.le.trans hle) htT₂
    have : ENNReal.ofReal (F.rcap w t') ≤ (u : ℝ≥0∞) := by
      rw [← ENNReal.ofReal_coe_nnreal]
      exact ENNReal.ofReal_le_ofReal (hmono.trans htu)
    exact absurd hlt (not_lt.2 this)
  obtain ⟨v, hv, hvt⟩ := exists_ent_add_clockOf_eq ht0 htT₁
  have hrc := capClock_curve hF h₁ hv
  rw [hvt] at hrc
  have hvS : v ≤ (n : ℝ) + 1 := by
    by_contra hlt
    have := hcv.strictMonoOn_capClock (mem_Ici.2 hn0.le) (mem_Ici.2 hv) (lt_of_not_ge hlt)
    rw [hrc] at this
    linarith
  rw [← hrc, (hK v ⟨hv, hvS⟩).2, fillH_curve hF h₁ hv, hvt]

/-- The inverse clock of a driven curve inverts its clock. -/
theorem capInv_capClock {γ : ℝ → ℂ} (hcv : IsDrivenCurve γ) {v : ℝ} (hv : 0 ≤ v) :
    capInv γ (capClock γ v) = v := by
  obtain ⟨hI0, hIs⟩ := hcv.capInv_spec (hcv.capClock_nonneg hv) (hcv.ofReal_capClock_lt hv)
  exact hcv.strictMonoOn_capClock.injOn (mem_Ici.2 hI0) (mem_Ici.2 hv) hIs

/-! ### The coordinates -/

/-- The nonnegative rational horizons. -/
def hzAll (k : ℕ) : ℝ≥0 := ((Denumerable.ofNat ℚ k : ℚ) : ℝ).toNNReal

theorem exists_hzAll_eq (q : ℚ) : ∃ k, hzAll k = (q : ℝ).toNNReal := by
  obtain ⟨k, hk⟩ : ∃ k, Denumerable.ofNat ℚ k = q := ⟨_, Denumerable.ofNat_encode q⟩
  exact ⟨k, by rw [hzAll, hk]⟩

section Coords

variable {Ω : Type*} {W' : ℝ≥0 → Ω → ℝ} {GT : Set Ω}

variable (F) in
/-- The horizons whose local curve lives past `u`. -/
def validA (W' : ℝ≥0 → Ω → ℝ) (GT : Set Ω) (u : ℝ≥0) (k : ℕ) : Set Ω :=
  {ω | (u : ℝ≥0∞) < F.locLife W' GT (hzAll k) ω}

open Classical in
variable (F) in
/-- **The coordinate life**: the supremum of the local lifetimes (`∞` off the good set). -/
def coordL (W' : ℝ≥0 → Ω → ℝ) (GT : Set Ω) (ω : Ω) : ℝ≥0∞ :=
  if ω ∈ GT then ⨆ k, F.locLife W' GT (hzAll k) ω else ⊤

open Classical in
variable (F) in
/-- **The coordinate driver**: the local driver of the first horizon whose curve lives past `u` (`0` off the good
set). -/
def coordD (W' : ℝ≥0 → Ω → ℝ) (GT : Set Ω) (u : ℝ≥0) (ω : Ω) : ℝ :=
  if ω ∈ GT then F.locDrv W' GT (hzAll (Supp8.RelSafe.selIdx (F.validA W' GT u) ω)) u ω else 0

theorem mem_of_lt_locLife {T u : ℝ≥0} {ω : Ω} (h : (u : ℝ≥0∞) < F.locLife W' GT T ω) :
    ω ∈ F.locEv W' GT T ∧ (u : ℝ≥0∞) < capLife (F.curve (fun r => W' r ω) T) := by
  by_cases hω : ω ∈ F.locEv W' GT T
  · rw [locLife, indicator_of_mem hω] at h
    exact ⟨hω, h⟩
  · rw [locLife, indicator_of_notMem hω] at h
    exact absurd h (not_lt_zero)

theorem locDrv_eq {T u : ℝ≥0} {ω : Ω} (hω : ω ∈ F.locEv W' GT T)
    (hu : (u : ℝ≥0∞) < capLife (F.curve (fun r => W' r ω) T)) :
    F.locDrv W' GT T u ω = segDrv (F.curve (fun r => W' r ω) T) u := by
  simp only [locDrv, indicator_of_mem hω, Supp8.GB6.CoordB.drivenDriver, hu, ↓reduceIte, segDriver]

variable (hF : F.IsOk) (hGT : ∀ ω ∈ GT, F.IsPathOk (fun r => W' r ω))
include hF hGT

/-- **The coordinate driver is the local driver of every horizon living past `u`.** -/
theorem coordD_eq {ω : Ω} (hω : ω ∈ GT) {u : ℝ≥0} {k : ℕ} (hk : (u : ℝ≥0∞) < F.locLife W' GT (hzAll k) ω) :
    F.coordD W' GT u ω = segDrv (F.curve (fun r => W' r ω) (hzAll k)) u := by
  have hv := Supp8.RelSafe.selIdx_mem (valid := F.validA W' GT u) (show ω ∈ F.validA W' GT u k from hk)
  set k' := Supp8.RelSafe.selIdx (F.validA W' GT u) ω
  obtain ⟨hm', hl'⟩ := mem_of_lt_locLife hv
  obtain ⟨hm, hl⟩ := mem_of_lt_locLife hk
  simp only [coordD, hω, ↓reduceIte]
  rw [locDrv_eq hm' hl']
  exact (segDrv_curve_eq hF (isLoc_of_mem_locEv hGT hm) (isLoc_of_mem_locEv hGT hm') hl hl').trans rfl

omit hF hGT in
theorem coordL_eq {ω : Ω} (hω : ω ∈ GT) : F.coordL W' GT ω = ⨆ k, F.locLife W' GT (hzAll k) ω := by
  simp only [coordL, hω, ↓reduceIte]

/-- A good sample has a local event at some rational horizon, with a positive lifetime. -/
theorem exists_pos_locLife {ω : Ω} (hω : ω ∈ GT) : ∃ k, (0 : ℝ≥0∞) < F.locLife W' GT (hzAll k) ω := by
  have hw := hGT ω hω
  obtain ⟨q, hq0, hq1, hq2⟩ := ENNReal.lt_iff_exists_rat_btwn.1 (ent_lt_exit hF hw)
  obtain ⟨k, hk⟩ := exists_hzAll_eq q
  have hT : F.ent (fun r => W' r ω) < hzAll k := by
    rw [hk, ← ENNReal.coe_lt_coe]
    exact hq1
  have hTe : ((hzAll k : ℝ≥0) : ℝ≥0∞) < F.exit (fun r => W' r ω) := by
    rw [hk]
    exact hq2
  have hmem : ω ∈ F.locEv W' GT (hzAll k) := ⟨hω, hT, hTe⟩
  have hcv := isDrivenCurve_curve hF (isLoc_of_mem_locEv hGT hmem)
  refine ⟨k, ?_⟩
  rw [locLife, indicator_of_mem hmem]
  have h1 : (0 : ℝ) < capClock (F.curve (fun r => W' r ω) (hzAll k)) 1 := by
    rw [← hcv.capClock_zero]
    exact hcv.strictMonoOn_capClock (mem_Ici.2 le_rfl) (mem_Ici.2 zero_le_one) zero_lt_one
  have h2 := hcv.ofReal_capClock_lt zero_le_one
  exact lt_of_lt_of_le (ENNReal.ofReal_pos.2 h1) h2.le

end Coords

/-! ### The coordinates are measurable relative coordinates -/

section Props

variable {Ω : Type*} [MeasurableSpace Ω] {W' : ℝ≥0 → Ω → ℝ} {GT : Set Ω}
  (hF : F.IsOk) (hGT : ∀ ω ∈ GT, F.IsPathOk (fun r => W' r ω)) (hWm : ∀ r, Measurable (W' r))
  (hGTm : MeasurableSet GT)
include hF hGT hWm hGTm

theorem measurable_locLife_all (k : ℕ) : Measurable (F.locLife W' GT (hzAll k)) :=
  measurable_locLife hF hGT (t := hzAll k) (fun r _ => hWm r) hGTm le_rfl

theorem measurable_coordD (u : ℝ≥0) : Measurable (F.coordD W' GT u) := by
  classical
  have hidx : Measurable (Supp8.RelSafe.selIdx (F.validA W' GT u)) :=
    Supp8.RelSafe.measurable_selIdx fun k => measurableSet_lt measurable_const
      (measurable_locLife_all hF hGT hWm hGTm k)
  show Measurable fun ω => F.coordD W' GT u ω
  simp only [coordD]
  exact Measurable.ite hGTm (Ito.measurable_comp_index (F := fun ω k => F.locDrv W' GT (hzAll k) u ω)
    (fun k => measurable_locDrv hF hGT (t := hzAll k) (fun r _ => hWm r) hGTm le_rfl u) hidx) measurable_const

theorem measurable_coordL : Measurable (F.coordL W' GT) := by
  classical
  show Measurable fun ω => F.coordL W' GT ω
  simp only [coordL]
  exact Measurable.ite hGTm (Measurable.iSup fun k => measurable_locLife_all hF hGT hWm hGTm k) measurable_const

omit [MeasurableSpace Ω] hWm hGTm in
theorem coordL_pos (ω : Ω) : 0 < F.coordL W' GT ω := by
  by_cases hω : ω ∈ GT
  · rw [coordL_eq hω]
    obtain ⟨k, hk⟩ := exists_pos_locLife hF hGT hω
    exact hk.trans_le (le_iSup (fun k => F.locLife W' GT (hzAll k) ω) k)
  · simp only [coordL, hω, ↓reduceIte, ENNReal.zero_lt_top]

omit [MeasurableSpace Ω] hWm hGTm in
theorem continuousOn_coordD (ω : Ω) :
    ContinuousOn (F.coordD W' GT · ω) {u | (u : ℝ≥0∞) < F.coordL W' GT ω} := by
  by_cases hω : ω ∈ GT
  · intro u₀ hu₀
    have hu₀' : (u₀ : ℝ≥0∞) < ⨆ k, F.locLife W' GT (hzAll k) ω := by rw [← coordL_eq hω]; exact hu₀
    obtain ⟨k, hk⟩ := lt_iSup_iff.1 hu₀'
    obtain ⟨hm, hl⟩ := mem_of_lt_locLife hk
    have hcv := isDrivenCurve_curve hF (isLoc_of_mem_locEv hGT hm)
    have hev : (F.coordD W' GT · ω) =ᶠ[𝓝 u₀] segDriver (F.curve (fun r => W' r ω) (hzAll k)) := by
      filter_upwards [(isOpen_lt ENNReal.continuous_coe continuous_const).mem_nhds hk] with u hu
      exact coordD_eq hF hGT hω hu
    have hca : ContinuousAt (segDriver (F.curve (fun r => W' r ω) (hzAll k))) u₀ :=
      (hcv.segDriver_spec.2.1 u₀ hl).continuousAt
        ((isOpen_lt ENNReal.continuous_coe continuous_const).mem_nhds hl)
    exact (hca.congr hev.symm).continuousWithinAt
  · have e : (F.coordD W' GT · ω) = fun _ => 0 := funext fun u => by simp only [coordD, hω, ↓reduceIte]
    rw [e]
    exact continuousOn_const

omit [MeasurableSpace Ω] hWm hGTm in
theorem coordD_zero (ω : Ω) : F.coordD W' GT 0 ω = 0 := by
  by_cases hω : ω ∈ GT
  · obtain ⟨k, hk⟩ := exists_pos_locLife hF hGT hω
    obtain ⟨hm, -⟩ := mem_of_lt_locLife (show ((0 : ℝ≥0) : ℝ≥0∞) < _ by rw [ENNReal.coe_zero]; exact hk)
    have hcv := isDrivenCurve_curve hF (isLoc_of_mem_locEv hGT hm)
    rw [coordD_eq hF hGT hω (show ((0 : ℝ≥0) : ℝ≥0∞) < _ by rw [ENNReal.coe_zero]; exact hk)]
    have h0 := hcv.segDriver_spec.1
    simp only [segDriver] at h0
    exact h0
  · simp only [coordD, hω, ↓reduceIte]

omit [MeasurableSpace Ω] hWm hGTm in
/-- The coordinate driver is the local driver of a horizon below that horizon's lifetime. -/
theorem coordD_eq_segDriver {ω : Ω} (hω : ω ∈ GT) {k : ℕ} (hm : ω ∈ F.locEv W' GT (hzAll k)) :
    ∀ u : ℝ≥0, (u : ℝ≥0∞) < capLife (F.curve (fun r => W' r ω) (hzAll k)) →
      F.coordD W' GT u ω = segDriver (F.curve (fun r => W' r ω) (hzAll k)) u := fun u hu =>
  coordD_eq hF hGT hω (by rw [locLife, indicator_of_mem hm]; exact hu)

omit [MeasurableSpace Ω] hWm hGTm in
/-- **The hull clause.** -/
theorem coord_hull {ω : Ω} (hω : ω ∈ GT) {s : ℝ≥0} (hs : (s : ℝ≥0∞) < F.coordL W' GT ω) :
    ∃ t : ℝ≥0, fwdHull (fun r : ℝ => F.coordD W' GT r.toNNReal ω) s = relHullFam F.c F.C (fun u => W' u ω) t := by
  have hs' : (s : ℝ≥0∞) < ⨆ k, F.locLife W' GT (hzAll k) ω := by rw [← coordL_eq hω]; exact hs
  obtain ⟨k, hk⟩ := lt_iSup_iff.1 hs'
  obtain ⟨hm, hl⟩ := mem_of_lt_locLife hk
  have hloc := isLoc_of_mem_locEv hGT hm
  have hcv := isDrivenCurve_curve hF hloc
  rw [fwdHull_eq_of_eq_segDriver hcv hl (coordD_eq_segDriver hF hGT hω hm),
    fillH_curve hF hloc (capInv_nonneg _ _)]
  exact ⟨_, rfl⟩

omit [MeasurableSpace Ω] hWm hGTm in
/-- **The exhaustion clause.** -/
theorem coord_exhaust {ω : Ω} (hω : ω ∈ GT) {t : ℝ≥0}
    (hb : Bornology.IsBounded (relHullFam F.c F.C (fun u => W' u ω) t)) :
    ∃ s : ℝ≥0, (s : ℝ≥0∞) < F.coordL W' GT ω ∧
      fwdHull (fun r : ℝ => F.coordD W' GT r.toNNReal ω) s = relHullFam F.c F.C (fun u => W' u ω) t := by
  have hw := hGT ω hω
  have hlt := lt_exit_of_isBounded hF hw hb
  set t' := max t (F.ent (fun r => W' r ω)) with ht'
  have hAt : F.hullAt (fun r => W' r ω) t = F.hullAt (fun r => W' r ω) t' := by
    rcases le_total t (F.ent (fun r => W' r ω)) with h | h
    · rw [hullAt_eq_empty_of_le hF hw h, hullAt_eq_empty_of_le hF hw (max_le h le_rfl)]
    · rw [ht', max_eq_left h]
  have ht'σ : (t' : ℝ≥0∞) < F.exit (fun r => W' r ω) := by
    rw [ht', ENNReal.coe_max]
    exact max_lt hlt (ent_lt_exit hF hw)
  obtain ⟨q, -, hq1, hq2⟩ := ENNReal.lt_iff_exists_rat_btwn.1 ht'σ
  obtain ⟨k, hk⟩ := exists_hzAll_eq q
  have ht'T : t' < hzAll k := by rw [hk, ← ENNReal.coe_lt_coe]; exact hq1
  have hm : ω ∈ F.locEv W' GT (hzAll k) :=
    ⟨hω, lt_of_le_of_lt (le_max_right _ _) ht'T, by rw [hk]; exact hq2⟩
  have hloc := isLoc_of_mem_locEv hGT hm
  have hcv := isDrivenCurve_curve hF hloc
  obtain ⟨v, hv, hvt⟩ := exists_ent_add_clockOf_eq (le_max_right t (F.ent (fun r => W' r ω))) ht'T
  set s : ℝ≥0 := (capClock (F.curve (fun r => W' r ω) (hzAll k)) v).toNNReal with hsdef
  have hsv : (s : ℝ) = capClock (F.curve (fun r => W' r ω) (hzAll k)) v := Real.coe_toNNReal _ (hcv.capClock_nonneg hv)
  have hsL : (s : ℝ≥0∞) < capLife (F.curve (fun r => W' r ω) (hzAll k)) := hcv.ofReal_capClock_lt hv
  have hle : capLife (F.curve (fun r => W' r ω) (hzAll k)) ≤ F.coordL W' GT ω := by
    rw [coordL_eq hω]
    refine le_trans (le_of_eq ?_) (le_iSup (fun k => F.locLife W' GT (hzAll k) ω) k)
    rw [locLife, indicator_of_mem hm]
  refine ⟨s, hsL.trans_le hle, ?_⟩
  rw [fwdHull_eq_of_eq_segDriver hcv hsL (coordD_eq_segDriver hF hGT hω hm), hsv, capInv_capClock hcv hv,
    fillH_curve hF hloc hv, hvt]
  exact hAt.symm

/-- **The coordinates are measurable relative coordinates** under any measure for which the good set is co-null. -/
theorem isGW4RelCoord_coord {ν : Measure Ω} (hGTae : ∀ᵐ ω ∂ν, ω ∈ GT) :
    IsGW4RelCoord ν W' F.c F.C (F.coordD W' GT) (F.coordL W' GT) :=
  ⟨measurable_coordD hF hGT hWm hGTm, measurable_coordL hF hGT hWm hGTm, coordL_pos hF hGT,
    continuousOn_coordD hF hGT, coordD_zero hF hGT,
    hGTae.mono fun _ hω _ hs => coord_hull hF hGT hω hs,
    hGTae.mono fun _ hω _ hb => coord_exhaust hF hGT hω hb⟩

end Props

end Frame

/-! ### `GW4RelCoordStatement` -/

/-- Coordinates for a driver almost surely equal to `W'` are coordinates for `W'`. -/
theorem IsGW4RelCoord.of_ae_eq {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} {V W' : ℝ≥0 → Ω → ℝ} {c : Chart}
    {C : Set ℂ} {D : ℝ≥0 → Ω → ℝ} {Λ : Ω → ℝ≥0∞} (h : IsGW4RelCoord ν V c C D Λ)
    (hVW : ∀ᵐ ω ∂ν, ∀ t, V t ω = W' t ω) : IsGW4RelCoord ν W' c C D Λ := by
  refine ⟨h.measurable, h.life_measurable, h.life_pos, h.continuous, h.zero, ?_, ?_⟩
  · filter_upwards [h.hull, hVW] with ω hω he
    have e : (fun u => V u ω) = fun u => W' u ω := funext he
    rw [← e]
    exact hω
  · filter_upwards [h.exhaust, hVW] with ω hω he
    have e : (fun u => V u ω) = fun u => W' u ω := funext he
    rw [← e]
    exact hω

/-- **A frame for every conditioning sample** (from Theorem 1.3 at universe `u` and the walks' barrier with its pocket
shape): in the setting of `GW4RelCoordStatement`, for almost every `ω₀`, every between-component `C` and chart `c`
have a frame `F` (the walks, `C`, `c`, a pocket shape and pocket data), a measurable continuous version `Wd` of the
counterflow driver (`ν`-almost surely equal to `W'`) and a measurable `ν`-co-null good set on which every path is good.
This is the input of the frame-level results (`Frame.isGW4RelCoord_coord`, `GW4FixPhysLine`). -/
theorem exists_frame (h13 : Exist.Theorem13Statement.{u}) (hB : GW4Reg.GW4BarrierPocketRegStatement.{u}) :
    ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
      let wR := boundaryWalkSpec b jumps (-(Real.pi / 2)) true
      let wL := boundaryWalkSpec b jumps (Real.pi / 2) false
      ∀ᵐ ω₀ ∂P,
        let R := ExplState.physSet κ b jumps wR (fun k => E wR k ω₀)
        let L := ExplState.physSet κ b jumps wL (fun k => E wL k ω₀)
        let ν := condExpKernel P
          (pastSigma κ b jumps wR (E wR) wR.2.2.length ⊔ pastSigma κ b jumps wL (E wL) wL.2.2.length) ω₀
        ∀ C ∈ betweenComponents R L, ∀ c : Chart, IsComponentChart R L C c →
          ∃ (F : Frame) (Wd : ℝ≥0 → Ω → ℝ) (GT : Set Ω), F.IsOk ∧ F.C = C ∧ F.c = c ∧
            (∀ ω ∈ GT, F.IsPathOk (fun r => Wd r ω)) ∧ (∀ r, Measurable (Wd r)) ∧ MeasurableSet GT ∧
            (∀ᵐ ω ∂ν, ω ∈ GT) ∧ ∀ᵐ ω ∂ν, ∀ t, Wd t ω = W' t ω := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg wR wL
  obtain ⟨b', J', h', -, -, hfl⟩ := id hcf
  have hreg0 := Supp8.GB6.ae_driver_zero_continuousOn hfl
  have hregV : ∀ᵐ ω ∂P, ζ' ω = ⊤ ∧ W' 0 ω = 0 ∧ Continuous (W' · ω) := by
    filter_upwards [hreg0, hζ'] with ω hr hz
    refine ⟨hz, hr.1, continuousOn_univ.1 (hr.2.mono fun t _ => ?_)⟩
    rw [mem_ofPred_eq, hz]
    exact ENNReal.coe_lt_top
  obtain ⟨_, 𝓕, _, _, _, _, hC⟩ := hfl
  obtain ⟨V, hVm, -, -, hVW⟩ := Supp8.GB6.SourceC.exists_top_driver_version hC.1.2.1 hregV
  have hamb := ae_ae_condExpKernel
    (m := pastSigma κ b jumps wR (E wR) wR.2.2.length ⊔ pastSigma κ b jumps wL (E wL) wL.2.2.length)
    (ae_trace_transient_noSimpleArc h13 hκ hκ4 hcf hζ')
  have hVWν := ae_ae_condExpKernel
    (m := pastSigma κ b jumps wR (E wR) wR.2.2.length ⊔ pastSigma κ b jumps wL (E wL) wL.2.2.length) hVW
  filter_upwards [hamb, hVWν, hB κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg] with ω₀ hambω hVWω hBω
  intro R L ν C hCm c hch
  have hν : IsProbabilityMeasure ν := by
    show IsProbabilityMeasure (condExpKernel P _ ω₀)
    infer_instance
  obtain ⟨αR, αL, hαR, hαL, hP, hbar⟩ := hBω
  have hCm' : C ∈ betweenComponents (range αR) (range αL) := by rw [hαR, hαL]; exact hCm
  have hch' : IsComponentChart (range αR) (range αL) C c := by rw [hαR, hαL]; exact hch
  have hpath : ∀ᵐ ω ∂ν, Continuous (fun r => V r ω) ∧ V 0 ω = 0 ∧
      IsGeneratingTrace (fun r => V r ω) ⊤ (trc (fun r => V r ω)) ∧
      GB10.NoSimpleArcInterval (trc (fun r => V r ω)) ⊤ ∧ GB11.IsGB11Barrier αR αL (trc (fun r => V r ω)) := by
    filter_upwards [hambω, hVWω, hbar] with ω h1 he h2
    obtain ⟨hW'c, hW'0, γ, hγ, -, hno⟩ := h1
    have e : (fun r => V r ω) = fun r => W' r ω := funext he
    have htr : trc (fun r => V r ω) = γ := by
      rw [e]
      funext v
      exact LP.traceAt_eq_of_isGeneratingTrace hγ hW'c.continuousOn hW'0 ENNReal.coe_lt_top
    rw [htr]
    refine ⟨e ▸ hW'c, (he 0).trans hW'0, e ▸ hγ, hno, h2 γ hγ⟩
  obtain ⟨ω₁, hω₁⟩ := hpath.exists
  have hB₁ := hω₁.2.2.2.2
  obtain ⟨s₁, t₁, s₂, t₂, hs⟩ := hP.1 C hCm'
  obtain ⟨xC, hxC, -, -⟩ := hch'.2.2.2.2.1 0
  have hxC' : Tendsto c.2.1 (𝓝[H] 0) (𝓝 xC) := by simpa only [Complex.ofReal_zero] using hxC
  have hx : xC = αR s₁ := hP.2.1 C hCm' s₁ t₁ s₂ t₂ hs c hch' xC hxC'
  rw [hx] at hxC'
  obtain ⟨E', ψ, G, k, hpd⟩ := exists_isPocketData hB₁.1 hB₁.2.1 hB₁.2.2.1 hCm' hs hch' hxC'
  let F : Frame := ⟨αR, αL, C, c, s₁, t₁, s₂, t₂, E', ψ, G, k⟩
  have hF : F.IsOk := ⟨hP, hCm', hs, hch', hxC', hpd⟩
  have hpath' : ∀ᵐ ω ∂ν, F.IsPathOk (fun r => V r ω) := hpath
  obtain ⟨GT, hGTm, hGTae, hGT⟩ := Supp8.GB6.SourceC.exists_measurable_good hpath'
  exact ⟨F, V, GT, hF, rfl, rfl, hGT, hVm, hGTm, hGTae, hVWω⟩


/-- **`GW4RelCoordStatement` PROVED** (from Theorem 1.3 at universe `u` and the walks' barrier with its pocket shape):
the coordinates `Frame.coordD`, `Frame.coordL` of a measurable continuous version of the counterflow driver, with the
frame of the conditioning sample's walks, component and chart (`exists_frame`). -/
theorem gw4RelCoordStatement (h13 : Exist.Theorem13Statement.{u}) (hB : GW4Reg.GW4BarrierPocketRegStatement.{u}) :
    GW4RelCoordStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg wR wL
  filter_upwards [exists_frame h13 hB κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg] with ω₀ hω₀
  intro R L ν C hCm c hch
  obtain ⟨F, Wd, GT, hF, hFC, hFc, hGT, hWm, hGTm, hGTae, hVW⟩ := hω₀ C hCm c hch
  subst hFC hFc
  exact ⟨_, _, (Frame.isGW4RelCoord_coord hF hGT hWm hGTm hGTae).of_ae_eq hVW⟩

/-- **Theorem GW4's component (Det) from the relative safe law alone** (with the walks' barrier and pocket shape,
GW3's word bounds and Theorems 1.2–1.3): the measurable relative coordinates are now proved. -/
theorem gw4RelativeLawRegStatement_of_relSafe' (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (hB : GW4Reg.GW4BarrierPocketRegStatement.{u})
    (hWB : GW4R51.GW3WordBoundRegStatement.{u}) (hS : GW4RelSafeStatement.{u}) :
    GW4Reg.GW4RelativeLawRegStatement.{u} :=
  gw4RelativeLawRegStatement_of_coord_relSafe h12 h13 h12₀ h13₀ hB hWB (gw4RelCoordStatement h13 hB) hS

end InteractingSLE.Theorem14.GW4Fix
