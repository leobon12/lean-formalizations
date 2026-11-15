/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2TnExport
import InteractingSLE.Spec.Sec5.CrossRestartLawMeas
import InteractingSLE.Spec.Sec5.Prop513

/-!
# The launch gauge at every root, part 1: readers built from a read-back physical curve

Packet PROVE-GW2-RELDET (round 27). Round 24's readers (`GW2TlRead`) used BUF's root-`0` physical-time rule
`timeCapRule`. Here the readers are built from ANY read-back of the physical curve `X t p` (a measurable causal
function of (record, relative path) that equals `γ (clock⁻¹ t)` along relative coordinates), so they work at every
root (`X = physicalTraceX x s · − x` at a root `x`):

* `capT X q p`: the physical time at the relative time `q`: half the grid capacity of the read-back points
  (`WholeField.hcapHit`); `relT X r p`: the first rational relative time whose physical time exceeds `r`;
  `trC X p r`: the physical curve at the physical time `r`; `drvC X p u`: its driver (`RootB23.traceDriverRead`);
  all Borel;
* along one sample (a regular clock `a` reading `γ` back, `γ` a generating trace of the explored driver `W`):
  **`capT_eq`** (the inverse clock), **`relT_eq`** (the clock), **`trC_eq`**, **`drvC_eq`** (the explored driver);
* frozen paths: the readers see only the path up to `t` (`capT_freeze`, `relT_freeze`, `drvC_freeze`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2Rd

open Exist.StagedLaw Supp8.GB6 Supp8.GB6.HullId
open Sec5.CrossRestart (ratGrid)

/-! ### The readers -/

section Readers

variable (X : ℝ≥0 → RecData × (ℝ≥0 → ℝ) → ℂ)

/-- **The physical time at the relative time `q`**: half the grid capacity of the read-back points on `[0, q]`. -/
def capT (q : ℝ≥0) (p : RecData × (ℝ≥0 → ℝ)) : ℝ :=
  (WholeField.hcapHit ((fun v => X v p) '' ratGrid q)).toReal / 2

open scoped Classical in
/-- **The relative time of the physical time `r`**: the first rational relative time whose physical time exceeds
`r`. -/
def relT (r : ℝ≥0) (p : RecData × (ℝ≥0 → ℝ)) : ℝ≥0∞ :=
  ⨅ q : ℚ≥0, if (r : ℝ) < capT X (q : ℝ≥0) p then ((q : ℝ≥0) : ℝ≥0∞) else ⊤

/-- **The physical curve at the physical time `r`.** -/
def trC (p : RecData × (ℝ≥0 → ℝ)) (r : ℝ≥0) : ℂ := evalDnC (fun u => X u p) (relT X r p).toNNReal

/-- **The physical driver**, read off the physical curve. -/
def drvC (p : RecData × (ℝ≥0 → ℝ)) (u : ℝ≥0) : ℝ := GW2TipSystem.RootB23.traceDriverRead (trC X p) u

variable {X}

theorem measurable_capT (hX : ∀ u, Measurable (X u)) (q : ℝ≥0) : Measurable (capT X q) :=
  (Sec5.CrossRestart.measurable_hcapHit_image_of_countable (Sec5.CrossRestart.countable_ratGrid q)
    (f := fun p v => X v p) fun v => hX v).ennreal_toReal.div_const 2

open scoped Classical in
theorem measurable_relT (hX : ∀ u, Measurable (X u)) (r : ℝ≥0) : Measurable (relT X r) :=
  Measurable.iInf fun _ =>
    Measurable.ite (measurableSet_lt measurable_const (measurable_capT hX _)) measurable_const measurable_const

theorem measurable_trC (hX : ∀ u, Measurable (X u)) (r : ℝ≥0) : Measurable fun p => trC X p r :=
  measurable_evalDnC (X := fun p u => X u p) hX (measurable_relT hX r).ennreal_toNNReal

theorem measurable_drvC_path (hX : ∀ u, Measurable (X u)) : Measurable fun p => drvC X p :=
  measurable_pi_iff.2 fun u =>
    (GW2TipSystem.RootB23.measurable_traceDriverRead u).comp (measurable_pi_iff.2 fun r => measurable_trC hX r)

end Readers

/-! ### Along one sample -/

section Sample

variable {X : ℝ≥0 → RecData × (ℝ≥0 → ℝ) → ℂ} {p : RecData × (ℝ≥0 → ℝ)} {a : ℝ≥0 → ℝ} {Tc L : ℝ≥0∞}
  {γ : ℝ≥0 → ℂ} {W : ℝ≥0 → ℝ}

/-- **The physical time reader inverts the clock.** -/
theorem capT_eq (hW : Continuous W) (hW0 : W 0 = 0) (hγ : IsGeneratingTrace W ⊤ γ)
    (ham : StrictMonoOn a {t | (t : ℝ≥0∞) < Tc})
    (hback : ∀ u : ℝ≥0, (u : ℝ≥0∞) < L → ∃ t : ℝ≥0, (t : ℝ≥0∞) < Tc ∧ a t = u)
    (hread : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc → X (a t).toNNReal p = γ t)
    (hXc : ContinuousOn (fun u => X u p) {u | (u : ℝ≥0∞) < L})
    {u t' : ℝ≥0} (huL : (u : ℝ≥0∞) < L) (ht' : (t' : ℝ≥0∞) < Tc) (hat : a t' = u) : capT X u p = t' := by
  have hcI : ContinuousOn (fun v => X v p) (Icc 0 u) :=
    hXc.mono fun v hv => (ENNReal.coe_le_coe.2 hv.2).trans_lt huL
  have himg : (fun v => X v p) '' Icc 0 u = γ '' Icc 0 t' := by
    ext z
    constructor
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨t₁, ht₁, hat₁⟩ := hback v ((ENNReal.coe_le_coe.2 hv.2).trans_lt huL)
      have h1 : t₁ ≤ t' := by
        by_contra hlt
        have := ham ht' ht₁ (lt_of_not_ge hlt)
        rw [hat, hat₁] at this
        exact absurd (NNReal.coe_le_coe.2 hv.2) (not_le.2 this)
      refine ⟨t₁, ⟨zero_le, h1⟩, ?_⟩
      have h := hread t₁ ht₁
      rw [hat₁, Real.toNNReal_coe] at h
      exact h.symm
    · rintro ⟨t₁, ht₁, rfl⟩
      have ht₁c : (t₁ : ℝ≥0∞) < Tc := (ENNReal.coe_le_coe.2 ht₁.2).trans_lt ht'
      refine ⟨(a t₁).toNNReal, ⟨zero_le, ?_⟩, hread t₁ ht₁c⟩
      rw [← Real.toNNReal_coe (r := u), ← hat]
      exact Real.toNNReal_le_toNNReal (ham.monotoneOn ht₁c ht' ht₁.2)
  unfold capT
  rw [Sec5.CrossRestart.hcapHit_image_ratGrid hcI, himg,
    Sec5.hcapHit_image_Icc_of_isGeneratingTrace hW hW0 hγ t', ENNReal.toReal_mul, ENNReal.coe_toReal]
  norm_num

open scoped Classical in
/-- **The relative time reader is the clock** before the first contact. -/
theorem relT_eq (hW : Continuous W) (hW0 : W 0 = 0) (hγ : IsGeneratingTrace W ⊤ γ)
    (ham : StrictMonoOn a {t | (t : ℝ≥0∞) < Tc})
    (haL : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc → 0 ≤ a t ∧ ENNReal.ofReal (a t) < L)
    (hback : ∀ u : ℝ≥0, (u : ℝ≥0∞) < L → ∃ t : ℝ≥0, (t : ℝ≥0∞) < Tc ∧ a t = u)
    (hread : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc → X (a t).toNNReal p = γ t)
    (hXc : ContinuousOn (fun u => X u p) {u | (u : ℝ≥0∞) < L})
    {r : ℝ≥0} (hr : (r : ℝ≥0∞) < Tc) : relT X r p = ENNReal.ofReal (a r) := by
  obtain ⟨h0r, hrL⟩ := haL r hr
  -- below `L` the condition reads the clock
  have hiff : ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < L → ((r : ℝ) < capT X (q : ℝ≥0) p ↔ a r < ((q : ℝ≥0) : ℝ)) := by
    intro q hqL
    obtain ⟨t₁, ht₁, hat₁⟩ := hback q hqL
    rw [capT_eq hW hW0 hγ ham hback hread hXc hqL ht₁ hat₁, ← hat₁]
    constructor
    · intro h; exact ham hr ht₁ (NNReal.coe_lt_coe.1 h)
    · intro h
      by_contra hle
      have := ham.monotoneOn ht₁ hr (NNReal.coe_le_coe.1 (not_lt.1 hle))
      exact absurd h (not_lt.2 this)
  unfold relT
  refine le_antisymm ?_ (le_iInf fun q => ?_)
  · refine le_of_forall_gt fun b hb => ?_
    obtain ⟨c, hc1, hc2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 (lt_min hb hrL)
    have hac : a r < (c : ℝ) := by
      have h := hc1
      rw [← ENNReal.ofReal_coe_nnreal] at h
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg h0r).1 h
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show max 0 (a r) < (c : ℝ) from max_lt (h0r.trans_lt hac) hac)
    have hq0 : (0 : ℚ) ≤ q := by exact_mod_cast (le_max_left _ _).trans hq1.le
    let q' : ℚ≥0 := ⟨q, hq0⟩
    have hq' : ((q' : ℝ≥0) : ℝ) = q := rfl
    have hqc : ((q' : ℝ≥0) : ℝ≥0∞) < c := ENNReal.coe_lt_coe.2 (NNReal.coe_lt_coe.1 (by rw [hq']; exact hq2))
    have hqL : ((q' : ℝ≥0) : ℝ≥0∞) < L := hqc.trans (hc2.trans_le (min_le_right _ _))
    have hin : (r : ℝ) < capT X (q' : ℝ≥0) p := (hiff q' hqL).2 (by rw [hq']; exact (le_max_right _ _).trans_lt hq1)
    refine (iInf_le _ q').trans_lt ?_
    simp only [hin, ↓reduceIte]
    exact hqc.trans (hc2.trans_le (min_le_left _ _))
  · split_ifs with h
    · by_cases hqL : ((q : ℝ≥0) : ℝ≥0∞) < L
      · have h1 := (hiff q hqL).1 h
        rw [← ENNReal.ofReal_coe_nnreal]
        exact ENNReal.ofReal_le_ofReal h1.le
      · exact hrL.le.trans (not_lt.1 hqL)
    · exact le_top

/-- **The physical curve reader** before the first contact. -/
theorem trC_eq (hW : Continuous W) (hW0 : W 0 = 0) (hγ : IsGeneratingTrace W ⊤ γ)
    (ham : StrictMonoOn a {t | (t : ℝ≥0∞) < Tc})
    (haL : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc → 0 ≤ a t ∧ ENNReal.ofReal (a t) < L)
    (hback : ∀ u : ℝ≥0, (u : ℝ≥0∞) < L → ∃ t : ℝ≥0, (t : ℝ≥0∞) < Tc ∧ a t = u)
    (hread : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc → X (a t).toNNReal p = γ t)
    (hXc : ContinuousOn (fun u => X u p) {u | (u : ℝ≥0∞) < L})
    {r : ℝ≥0} (hr : (r : ℝ≥0∞) < Tc) : trC X p r = γ r := by
  unfold trC
  rw [relT_eq hW hW0 hγ ham haL hback hread hXc hr, toNNReal_ofReal_eq]
  have hL : (((a r).toNNReal : ℝ≥0) : ℝ≥0∞) < L := (haL r hr).2
  have hcont : ContinuousAt (fun u => X u p) (a r).toNNReal := hXc.continuousAt ((isOpen_lt_life L).mem_nhds hL)
  rw [evalDnC_eq_of_continuousWithinAt hcont.continuousWithinAt, hread r hr]

/-- **The physical driver reader is the explored driver** before the first contact. -/
theorem drvC_eq (hW : Continuous W) (hW0 : W 0 = 0) (hγ : IsGeneratingTrace W ⊤ γ)
    (ham : StrictMonoOn a {t | (t : ℝ≥0∞) < Tc})
    (haL : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc → 0 ≤ a t ∧ ENNReal.ofReal (a t) < L)
    (hback : ∀ u : ℝ≥0, (u : ℝ≥0∞) < L → ∃ t : ℝ≥0, (t : ℝ≥0∞) < Tc ∧ a t = u)
    (hread : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc → X (a t).toNNReal p = γ t)
    (hXc : ContinuousOn (fun u => X u p) {u | (u : ℝ≥0∞) < L})
    {u : ℝ≥0} (hu : (u : ℝ≥0∞) < Tc) : drvC X p u = W u := by
  unfold drvC
  rw [GW2TipSystem.RootB23.traceDriverRead_congr_prefix (γ' := γ) fun r hr =>
    trC_eq hW hW0 hγ ham haL hback hread hXc ((ENNReal.coe_le_coe.2 hr.2).trans_lt hu)]
  exact GW2TipSystem.RootB23.traceDriverRead_eq hγ hW.continuousOn hW0 ENNReal.coe_lt_top

end Sample

/-! ### Frozen paths -/

section Freeze

variable {X : ℝ≥0 → RecData × (ℝ≥0 → ℝ) → ℂ}
  (hXc : ∀ u r w w', (∀ v ≤ u, w v = w' v) → X u (r, w) = X u (r, w')) (r : RecData) (w : ℝ≥0 → ℝ) (t : ℝ≥0)

include hXc in
theorem X_freeze {u : ℝ≥0} (hu : u ≤ t) : X u (r, LP.freezeAt t w) = X u (r, w) :=
  hXc u r _ _ fun _ hv => freezeAt_eq_of_le w t (hv.trans hu)

include hXc in
theorem capT_freeze {q : ℝ≥0} (hq : q ≤ t) : capT X q (r, LP.freezeAt t w) = capT X q (r, w) := by
  unfold capT
  congr 3
  refine image_congr fun v hv => X_freeze hXc r w t ?_
  exact ((Sec5.CrossRestart.ratGrid_subset_Icc q) hv).2.trans hq

open scoped Classical in
include hXc in
/-- **The relative time of a physical time sees the path only up to `t`**, when it is below `t`. -/
theorem relT_freeze {ρ : ℝ≥0} (hlt : relT X ρ (r, w) < t) : relT X ρ (r, LP.freezeAt t w) = relT X ρ (r, w) := by
  have hsame : ∀ q : ℚ≥0, (q : ℝ≥0) ≤ t →
      ((ρ : ℝ) < capT X (q : ℝ≥0) (r, LP.freezeAt t w) ↔ (ρ : ℝ) < capT X (q : ℝ≥0) (r, w)) := fun q hq => by
    rw [capT_freeze hXc r w t hq]
  unfold relT at hlt ⊢
  refine le_antisymm ?_ (le_iInf fun q => ?_)
  · refine le_of_forall_gt fun b hb => ?_
    obtain ⟨q, hq⟩ := iInf_lt_iff.1 (lt_min hb hlt)
    have hqb : (if (ρ : ℝ) < capT X (q : ℝ≥0) (r, w) then ((q : ℝ≥0) : ℝ≥0∞) else ⊤) < min b t := hq
    split_ifs at hqb with hin
    · have hqt : (q : ℝ≥0) ≤ t := ENNReal.coe_le_coe.1 (hqb.le.trans (min_le_right _ _))
      refine (iInf_le _ q).trans_lt ?_
      simp only [(hsame q hqt).2 hin, ↓reduceIte]
      exact hqb.trans_le (min_le_left _ _)
    · exact absurd hqb (not_lt.2 le_top)
  · by_cases hqt : (q : ℝ≥0) ≤ t
    · split_ifs with hin
      · exact iInf_le_of_le q (by simp only [(hsame q hqt).1 hin, ↓reduceIte, le_refl])
      · exact le_top
    · split_ifs
      · exact hlt.le.trans (ENNReal.coe_le_coe.2 (le_of_lt (not_le.1 hqt)))
      · exact le_top

include hXc in
theorem trC_freeze {ρ : ℝ≥0} (hlt : relT X ρ (r, w) < t) : trC X (r, LP.freezeAt t w) ρ = trC X (r, w) ρ := by
  unfold trC
  rw [relT_freeze hXc r w t hlt]
  refine evalDnC_congr fun u hu => X_freeze hXc r w t (hu.trans ?_)
  have hne : (t : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  simpa using ENNReal.toNNReal_mono hne hlt.le

include hXc in
/-- **The physical driver at `u` sees the path only up to `t`** once every relative time of a physical time `≤ u` is
below `t`. -/
theorem drvC_freeze {u : ℝ≥0} (hle : ∀ ρ ≤ u, relT X ρ (r, w) < t) :
    drvC X (r, LP.freezeAt t w) u = drvC X (r, w) u := by
  unfold drvC
  exact GW2TipSystem.RootB23.traceDriverRead_congr_prefix fun ρ hρ => trC_freeze hXc r w t (hle ρ hρ.2)

end Freeze

end InteractingSLE.Theorem14.GW2Rd
