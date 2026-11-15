/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2TlBad
import InteractingSLE.Spec.Supplement.GW2RootB23Prefix
import InteractingSLE.Spec.Supplement.GW2RdStgRule

/-!
# N4 item 1 in launch coordinates, part 2: the physical driver read from (record, relative path)

Packet PROVE-GW2-RELDET (decision D20). The death gauge must be a Borel function of GB6's (counterflow record,
relative path). The candidate's launch word and launch trace are functions of the PHYSICAL driver of the explored
curve. Here that driver is read from (record, relative path):

* `evalDnC`: the causal, jointly measurable evaluation of a complex path at a time (`evalDn` on both parts);
  `evalDnC_eq_of_continuousWithinAt`;
* `physTrR s p r`: GB6's physical trace read at the relative time `timeCapRule s r p` at which the physical capacity
  reaches `r`; `physDrvR s p u`: the driver of that trace (`RootB23.traceDriverRead`); `physTimeR s t p`: the physical
  time at the relative time `t` (the infimum of the rational physical times whose time rule exceeds `t`);
  all Borel (`measurable_physTrR`, `measurable_physDrvR`, `measurable_physTimeR`);
* along one sample of relative coordinates (GB6's clock and read-back, BUF's time rule):
  **`physTrR_eq`** (the explored trace), **`physDrvR_eq`** (the explored driver), **`physTimeR_eq`** (the inverse
  clock), before the first contact;
* frozen paths (`LP.freezeAt t`): the readers see only the path up to `t` (`physTimeR_freeze`, `physTrR_freeze`,
  `physDrvR_freeze`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2Rd

open Exist.StagedLaw Supp8.GB6 Supp8.GB6.HullId

/-! ### Causal evaluation of a complex path -/

/-- **Causal evaluation at continuity points from the left.** -/
theorem evalDn_eq_of_continuousWithinAt {p : ℝ≥0 → ℝ} {τ : ℝ≥0} (hp : ContinuousWithinAt p (Iic τ) τ) :
    evalDn p τ = p τ := by
  have ht : Tendsto (fun n => dyadLo n τ) atTop (𝓝[Iic τ] τ) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_dyadLo τ, Eventually.of_forall fun n => dyadLo_le n τ⟩
  exact (hp.tendsto.comp ht).limsup_eq

/-- The causal evaluation of a complex path (real and imaginary parts). -/
def evalDnC (X : ℝ≥0 → ℂ) (τ : ℝ≥0) : ℂ :=
  (evalDn (fun u => (X u).re) τ : ℂ) + (evalDn (fun u => (X u).im) τ : ℂ) * Complex.I

theorem evalDnC_eq_of_continuousWithinAt {X : ℝ≥0 → ℂ} {τ : ℝ≥0} (hX : ContinuousWithinAt X (Iic τ) τ) :
    evalDnC X τ = X τ := by
  unfold evalDnC
  have hre : ContinuousWithinAt (fun u => (X u).re) (Iic τ) τ :=
    Complex.continuous_re.continuousAt.comp_continuousWithinAt hX
  have him : ContinuousWithinAt (fun u => (X u).im) (Iic τ) τ :=
    Complex.continuous_im.continuousAt.comp_continuousWithinAt hX
  rw [evalDn_eq_of_continuousWithinAt hre, evalDn_eq_of_continuousWithinAt him]
  exact Complex.re_add_im (X τ)

theorem evalDnC_congr {X X' : ℝ≥0 → ℂ} {τ : ℝ≥0} (h : ∀ u ≤ τ, X u = X' u) : evalDnC X τ = evalDnC X' τ := by
  unfold evalDnC
  rw [evalDn_congr (p := fun u => (X u).re) (p' := fun u => (X' u).re) fun u hu => by rw [h u hu],
    evalDn_congr (p := fun u => (X u).im) (p' := fun u => (X' u).im) fun u hu => by rw [h u hu]]

theorem measurable_evalDnC {α : Type*} [MeasurableSpace α] {X : α → ℝ≥0 → ℂ} (hX : ∀ t, Measurable fun a => X a t)
    {τ : α → ℝ≥0} (hτ : Measurable τ) : Measurable fun a => evalDnC (X a) (τ a) := by
  have hre := measurable_evalDn (p := fun a u => (X a u).re) (fun t => Complex.measurable_re.comp (hX t)) hτ
  have him := measurable_evalDn (p := fun a u => (X a u).im) (fun t => Complex.measurable_im.comp (hX t)) hτ
  exact (Complex.measurable_ofReal.comp hre).add ((Complex.measurable_ofReal.comp him).mul_const _)

/-! ### The readers -/

/-- **The physical trace at physical time `r`**, read from (record, relative path) at the relative time at which the
physical capacity reaches `r`. -/
def physTrR (s : ℝ≥0) (p : RecData × (ℝ≥0 → ℝ)) (r : ℝ≥0) : ℂ :=
  evalDnC (fun u => ReadD.physicalTrace s u p) (timeCapRule s r p).toNNReal

/-- **The physical driver**, read from (record, relative path). -/
def physDrvR (s : ℝ≥0) (p : RecData × (ℝ≥0 → ℝ)) (u : ℝ≥0) : ℝ :=
  GW2TipSystem.RootB23.traceDriverRead (physTrR s p) u

open scoped Classical in
/-- **The physical time at relative time `t`**: the infimum of the rational physical times whose time rule exceeds
`t`. -/
def physTimeR (s t : ℝ≥0) (p : RecData × (ℝ≥0 → ℝ)) : ℝ≥0∞ :=
  ⨅ q : ℚ≥0, if (t : ℝ≥0∞) < timeCapRule s (q : ℝ≥0) p then ((q : ℝ≥0) : ℝ≥0∞) else ⊤

theorem measurable_physTrR (s r : ℝ≥0) : Measurable fun p => physTrR s p r :=
  measurable_evalDnC (X := fun p u => ReadD.physicalTrace s u p) (fun t => ReadD.measurable_physicalTrace s t)
    (measurable_timeCapRule s r).ennreal_toNNReal

theorem measurable_physTrR_path (s : ℝ≥0) : Measurable fun p => physTrR s p :=
  measurable_pi_iff.2 fun r => measurable_physTrR s r

theorem measurable_physDrvR (s u : ℝ≥0) : Measurable fun p => physDrvR s p u :=
  (GW2TipSystem.RootB23.measurable_traceDriverRead u).comp (measurable_physTrR_path s)

theorem measurable_physDrvR_path (s : ℝ≥0) : Measurable fun p => physDrvR s p :=
  measurable_pi_iff.2 fun u => measurable_physDrvR s u

open scoped Classical in
theorem measurable_physTimeR (s t : ℝ≥0) : Measurable (physTimeR s t) :=
  Measurable.iInf fun _ =>
    Measurable.ite (measurableSet_lt measurable_const (measurable_timeCapRule s _)) measurable_const measurable_const

/-! ### Along one sample of relative coordinates -/

section Sample

variable {s : ℝ≥0} {p : RecData × (ℝ≥0 → ℝ)} {a : ℝ≥0 → ℝ} {Tc L : ℝ≥0∞} {γ : ℝ≥0 → ℂ}

theorem toNNReal_ofReal_eq (x : ℝ) : (ENNReal.ofReal x).toNNReal = x.toNNReal := ENNReal.toNNReal_coe _

theorem isOpen_lt_life (L : ℝ≥0∞) : IsOpen {u : ℝ≥0 | (u : ℝ≥0∞) < L} :=
  isOpen_lt ENNReal.continuous_coe continuous_const

/-- **The physical trace reader is the explored trace** before the first contact. -/
theorem physTrR_eq (haL : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc → 0 ≤ a t ∧ ENNReal.ofReal (a t) < L)
    (hread : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc → ReadD.physicalTrace s (a t).toNNReal p = γ t)
    (hXc : ContinuousOn (fun u => ReadD.physicalTrace s u p) {u | (u : ℝ≥0∞) < L})
    (hrule : ∀ Δ : ℝ≥0, (Δ : ℝ≥0∞) < Tc → timeCapRule s Δ p = ENNReal.ofReal (a Δ))
    {r : ℝ≥0} (hr : (r : ℝ≥0∞) < Tc) : physTrR s p r = γ r := by
  unfold physTrR
  rw [hrule r hr, toNNReal_ofReal_eq]
  have hL : (((a r).toNNReal : ℝ≥0) : ℝ≥0∞) < L := (haL r hr).2
  have hcont : ContinuousAt (fun u => ReadD.physicalTrace s u p) (a r).toNNReal :=
    hXc.continuousAt ((isOpen_lt_life L).mem_nhds hL)
  rw [evalDnC_eq_of_continuousWithinAt hcont.continuousWithinAt, hread r hr]

/-- **The physical driver reader is the explored driver** before the first contact. -/
theorem physDrvR_eq {W : ℝ≥0 → ℝ} (hγ : IsGeneratingTrace W ⊤ γ) (hW : Continuous W) (hW0 : W 0 = 0)
    (haL : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc → 0 ≤ a t ∧ ENNReal.ofReal (a t) < L)
    (hread : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc → ReadD.physicalTrace s (a t).toNNReal p = γ t)
    (hXc : ContinuousOn (fun u => ReadD.physicalTrace s u p) {u | (u : ℝ≥0∞) < L})
    (hrule : ∀ Δ : ℝ≥0, (Δ : ℝ≥0∞) < Tc → timeCapRule s Δ p = ENNReal.ofReal (a Δ))
    {u : ℝ≥0} (hu : (u : ℝ≥0∞) < Tc) : physDrvR s p u = W u := by
  unfold physDrvR
  rw [GW2TipSystem.RootB23.traceDriverRead_congr_prefix (γ' := γ) fun r hr =>
    physTrR_eq haL hread hXc hrule ((ENNReal.coe_le_coe.2 hr.2).trans_lt hu)]
  exact GW2TipSystem.RootB23.traceDriverRead_eq hγ hW.continuousOn hW0 ENNReal.coe_lt_top

open scoped Classical in
/-- **The physical time reader inverts the clock** at every relative time before the life. -/
theorem physTimeR_eq (ham : StrictMonoOn a {t | (t : ℝ≥0∞) < Tc})
    (hrule : ∀ Δ : ℝ≥0, (Δ : ℝ≥0∞) < Tc → timeCapRule s Δ p = ENNReal.ofReal (a Δ))
    (hruleL : ∀ Δ : ℝ≥0, ¬ (Δ : ℝ≥0∞) < Tc → L ≤ timeCapRule s Δ p)
    {t t' : ℝ≥0} (htL : (t : ℝ≥0∞) < L) (ht' : (t' : ℝ≥0∞) < Tc) (hat : a t' = t) :
    physTimeR s t p = t' := by
  -- the rational physical times whose rule exceeds `t` are exactly those after `t'`
  have hiff : ∀ q : ℚ≥0, (t : ℝ≥0∞) < timeCapRule s (q : ℝ≥0) p ↔ t' < (q : ℝ≥0) := by
    intro q
    by_cases hq : ((q : ℝ≥0) : ℝ≥0∞) < Tc
    · rw [hrule _ hq, ← ENNReal.ofReal_coe_nnreal, ← hat]
      rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by rw [hat]; exact t.coe_nonneg)]
      exact (ham.lt_iff_lt ht' hq)
    · constructor
      · intro _
        by_contra hle
        exact hq ((ENNReal.coe_le_coe.2 (not_lt.1 hle)).trans_lt ht')
      · intro _
        exact htL.trans_le (hruleL _ hq)
  unfold physTimeR
  simp only [hiff]
  refine le_antisymm ?_ (le_iInf fun q => ?_)
  · refine le_of_forall_gt fun b hb => ?_
    -- a rational physical time strictly between `t'` and `b`
    obtain ⟨c, hc1, hc2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hb
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (NNReal.coe_lt_coe.2 (ENNReal.coe_lt_coe.1 hc1))
    have hq0 : (0 : ℚ) ≤ q := by exact_mod_cast (t'.coe_nonneg.trans hq1.le)
    let q' : ℚ≥0 := ⟨q, hq0⟩
    have hq' : ((q' : ℝ≥0) : ℝ) = q := rfl
    have h1 : t' < (q' : ℝ≥0) := NNReal.coe_lt_coe.1 (by rw [hq']; exact hq1)
    have h2 : ((q' : ℝ≥0) : ℝ≥0∞) < b := by
      refine lt_trans ?_ hc2
      exact ENNReal.coe_lt_coe.2 (NNReal.coe_lt_coe.1 (by rw [hq']; exact hq2))
    exact (iInf_le _ q').trans_lt (by simp only [h1, ↓reduceIte]; exact h2)
  · split_ifs with h
    · exact ENNReal.coe_le_coe.2 h.le
    · exact le_top

end Sample

/-! ### Frozen paths -/

section Freeze

variable (s : ℝ≥0) (r : RecData) (w : ℝ≥0 → ℝ) (t : ℝ≥0)

theorem freezeAt_eq_of_le {u : ℝ≥0} (hu : u ≤ t) : LP.freezeAt t w u = w u := by
  simp only [LP.freezeAt, min_eq_left hu]

theorem physicalTrace_freeze {u : ℝ≥0} (hu : u ≤ t) :
    ReadD.physicalTrace s u (r, LP.freezeAt t w) = ReadD.physicalTrace s u (r, w) :=
  ReadD.physicalTrace_congr s u r fun _ hv => freezeAt_eq_of_le w t (hv.trans hu)

theorem timeCapRule_freeze_lt_iff (Δ : ℝ≥0∞) :
    (t : ℝ≥0∞) < timeCapRule s Δ (r, LP.freezeAt t w) ↔ (t : ℝ≥0∞) < timeCapRule s Δ (r, w) := by
  have h := GW2Bh.pathRule_le_iff (isPathRule_timeCapRule s Δ) (r := r) (w := w) (w' := LP.freezeAt t w)
    (t := t) fun _ hu => (freezeAt_eq_of_le w t hu).symm
  rw [← not_le, ← not_le, h]

theorem timeCapRule_freeze_of_le {Δ : ℝ≥0∞} (hle : timeCapRule s Δ (r, w) ≤ t) :
    timeCapRule s Δ (r, LP.freezeAt t w) = timeCapRule s Δ (r, w) :=
  GW2Bh.pathRule_eq_of_le (isPathRule_timeCapRule s Δ) (fun _ hu => (freezeAt_eq_of_le w t hu).symm) hle

open scoped Classical in
/-- **The physical time at `t` sees the path only up to `t`.** -/
theorem physTimeR_freeze : physTimeR s t (r, LP.freezeAt t w) = physTimeR s t (r, w) := by
  unfold physTimeR
  simp only [timeCapRule_freeze_lt_iff]

theorem physTrR_freeze {ρ : ℝ≥0} (hle : timeCapRule s ρ (r, w) ≤ t) :
    physTrR s (r, LP.freezeAt t w) ρ = physTrR s (r, w) ρ := by
  unfold physTrR
  rw [timeCapRule_freeze_of_le s r w t hle]
  refine evalDnC_congr fun u hu => physicalTrace_freeze s r w t ?_
  refine hu.trans ?_
  have hne : (t : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
  simpa using ENNReal.toNNReal_mono hne hle

/-- **The physical driver at `u` sees the path only up to `t`** once the physical capacity reaches every `ρ ≤ u`
by the relative time `t`. -/
theorem physDrvR_freeze {u : ℝ≥0} (hle : ∀ ρ ≤ u, timeCapRule s ρ (r, w) ≤ t) :
    physDrvR s (r, LP.freezeAt t w) u = physDrvR s (r, w) u := by
  unfold physDrvR
  exact GW2TipSystem.RootB23.traceDriverRead_congr_prefix fun ρ hρ => physTrR_freeze s r w t (hle ρ hρ.2)

end Freeze

end InteractingSLE.Theorem14.GW2Rd
