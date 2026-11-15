/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4FixRelCurve
import InteractingSLE.Spec.Supplement.GW4FillDetProof

/-!
# GW4's local relative curves read from the physical driver: the deterministic geometry

Packet PROVE-T14-GW4FIX (continuation: PROVE-GB6-RELSAFE's recipe for GW4). Under the conditional law given the walks,
the walks, the component `C`, its chart `c`, the pocket shape and the pocket data are fixed: a **frame** `F`. For a
physical driver path `w` (trace `trc w v = LP.traceAt v w`, read from the driver at times `≤ v`):

* `F.ent w`, `F.exit w`: the entry time `τ` and the exit time `σ` of the traversal;
* `F.hullAt w t = Φ(K^w_t ∩ R⁻¹(C))` (`GW4Rel.relHullFam`) and its capacity clock `F.rcap w t = hcap(·)/2`;
* **`F.curve w T`**: the local relative curve with physical horizon `T`, the relative trace on `[0, T − τ)`
  reparametrized on `[0, ∞)` (`relCurve (relTrace E ψ k (trc w) τ) (T − τ)`); it reads the driver only before `T`;
* `F.IsLoc w T`: the path is good (`IsPathOk`) and `τ < T < σ`;
* **`isDrivenCurve_curve`**, **`fillH_curve`**, **`capClock_curve`**: on `IsLoc` the curve is a driven curve whose
  filled prefixes are the relative hulls at the physical times `τ + clockOf (T − τ) v`;
* `hullAt_eq_empty_of_le`, **`lt_exit_of_isBounded`** (a bounded relative hull occurs before the exit: the exit fills
  the pocket, `fill_of_exitShape`), `exists_ent_add_clockOf_eq`;
* **`eq_segDrv_of_clockHull`**: a continuous driver from `0` whose hulls at the relative clock are the relative hulls is
  the curve's driver below its lifetime (`IsDrivenCurve.segDrv_eq`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Bornology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull)

namespace InteractingSLE.Theorem14.GW4Fix

open GW4Traverse GW4Reg GB11Conn GB11Chart GW4Rel Sec7.PocketTraversal Sec7.Lemma71C

/-- The trace read from a driver path. -/
def trc (w : ℝ≥0 → ℝ) (v : ℝ≥0) : ℂ := LP.traceAt v w

/-- **A GW4 frame**: the walks, a between-component, its chart, the pocket shape and the pocket data. -/
structure Frame where
  αR : ℝ≥0 → ℂ
  αL : ℝ≥0 → ℂ
  C : Set ℂ
  c : Chart
  s₁ : ℝ≥0
  t₁ : ℝ≥0
  s₂ : ℝ≥0∞
  t₂ : ℝ≥0∞
  E : Set ℂ
  ψ : ℂ → ℂ
  G : ℂ → ℂ
  k : ℝ

namespace Frame

variable (F : Frame)

/-- The conditions on a frame (no counterflow involved). -/
def IsOk : Prop :=
  WalkPocketShape F.αR F.αL ∧ F.C ∈ betweenComponents (range F.αR) (range F.αL) ∧
    IsPocketShape F.αR F.αL F.C F.s₁ F.t₁ F.s₂ F.t₂ ∧ IsComponentChart (range F.αR) (range F.αL) F.C F.c ∧
    Tendsto F.c.2.1 (𝓝[H] 0) (𝓝 (F.αR F.s₁)) ∧ IsPocketData F.αR F.αL F.C F.c F.s₁ F.t₁ F.s₂ F.E F.ψ F.G F.k

/-- The pathwise conditions on a driver path: continuous from `0`, generating its trace, GB10's conclusion and GB11's
barrier input for the frame's walks. -/
def IsPathOk (w : ℝ≥0 → ℝ) : Prop :=
  Continuous w ∧ w 0 = 0 ∧ IsGeneratingTrace w ⊤ (trc w) ∧ GB10.NoSimpleArcInterval (trc w) ⊤ ∧
    GB11.IsGB11Barrier F.αR F.αL (trc w)

/-- The entry time of the traversal. -/
def ent (w : ℝ≥0 → ℝ) : ℝ≥0 := entryTime (trc w) F.αR F.s₂

/-- The exit time of the traversal. -/
def exit (w : ℝ≥0 → ℝ) : ℝ≥0∞ := GB11.firstVisit (trc w) (F.αR F.s₁)

/-- The relative hull at physical time `t`. -/
def hullAt (w : ℝ≥0 → ℝ) (t : ℝ≥0) : Set ℂ := relHullFam F.c F.C w t

/-- The relative capacity clock at physical time `t`. -/
def rcap (w : ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ := ConformalImage.hcapSet (F.hullAt w t) / 2

/-- **The local relative curve with physical horizon `T`.** -/
def curve (w : ℝ≥0 → ℝ) (T : ℝ≥0) : ℝ → ℂ :=
  relCurve (relTrace F.E F.ψ F.k (trc w) (F.ent w)) ((T : ℝ) - F.ent w)

/-- The local condition at horizon `T`: a good path with `τ < T < σ`. -/
def IsLoc (w : ℝ≥0 → ℝ) (T : ℝ≥0) : Prop := F.IsPathOk w ∧ F.ent w < T ∧ (T : ℝ≥0∞) < F.exit w

variable {F}

/-! ### The traversal clauses of a good path -/

section Clauses

variable (hF : F.IsOk) {w : ℝ≥0 → ℝ} (hw : F.IsPathOk w)
include hF hw

theorem clause_entry : ∀ t : ℝ≥0, t < F.ent w → trc w t ≠ 0 → -(trc w t)⁻¹ ∉ closure F.C :=
  notMem_closure_before_entry hw.2.2.1 hw.2.2.2.2 hF.2.1 hF.2.2.1

theorem clause_traversal : ∀ t : ℝ≥0, F.ent w ≤ t → (t : ℝ≥0∞) < F.exit w → trc w t ≠ 0 →
    -(trc w t)⁻¹ ∈ closure F.C :=
  mem_closure_of_traversal hw.1 hw.2.1 hw.2.2.1 hw.2.2.2.1 hw.2.2.2.2 hF.1 hF.2.1 hF.2.2.1

theorem clause_density : ∀ a b : ℝ≥0, F.ent w ≤ a → a < b → (b : ℝ≥0∞) < F.exit w →
    ∃ t ∈ Ioo a b, trc w t ≠ 0 ∧ -(trc w t)⁻¹ ∈ F.C :=
  exists_mem_of_traversal hw.1 hw.2.1 hw.2.2.1 hw.2.2.2.1 hw.2.2.2.2 hF.1 hF.2.1 hF.2.2.1

omit hF in
theorem continuous_trc : Continuous (trc w) := Sec5.continuous_of_isGeneratingTrace_top hw.2.2.1

theorem ent_lt_exit : (F.ent w : ℝ≥0∞) < F.exit w :=
  entryTime_lt_firstVisit hw.2.2.1.1 (continuous_trc hw) hw.2.2.2.2 hF.2.2.1

end Clauses

/-! ### The local curve -/

section Local

theorem ofReal_sub_lt {T τ : ℝ≥0} {σ : ℝ≥0∞} (h1 : τ < T) (h2 : (T : ℝ≥0∞) < σ) :
    ENNReal.ofReal ((T : ℝ) - τ) < σ - τ := by
  rw [← NNReal.coe_sub h1.le, ENNReal.ofReal_coe_nnreal]
  induction σ using ENNReal.recTopCoe with
  | top => rw [ENNReal.top_sub_coe]; exact ENNReal.coe_lt_top
  | coe s =>
    rw [← ENNReal.coe_sub, ENNReal.coe_lt_coe]
    exact tsub_lt_tsub_right_of_le h1.le (ENNReal.coe_lt_coe.1 h2)

/-- The relative horizon of a local condition. -/
theorem horizon_of_isLoc {w : ℝ≥0 → ℝ} {T : ℝ≥0} (h : F.IsLoc w T) :
    ((T : ℝ) - F.ent w) ∈ horizon (F.exit w - F.ent w) ∧ 0 < (T : ℝ) - F.ent w :=
  ⟨⟨sub_nonneg.2 (NNReal.coe_le_coe.2 h.2.1.le), ofReal_sub_lt h.2.1 h.2.2⟩,
    sub_pos.2 (NNReal.coe_lt_coe.2 h.2.1)⟩

variable (hF : F.IsOk) {w : ℝ≥0 → ℝ} {T : ℝ≥0} (h : F.IsLoc w T)
include hF h

/-- **The local curve is driven.** -/
theorem isDrivenCurve_curve : IsDrivenCurve (F.curve w T) :=
  isDrivenCurve_relTrace h.1.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2.1 h.1.2.2.2.2 hF.1 hF.2.1 hF.2.2.1 hF.2.2.2.1
    hF.2.2.2.2.1 (clause_entry hF h.1) (clause_traversal hF h.1) (clause_density hF h.1) hF.2.2.2.2.2
    (horizon_of_isLoc h).1 (horizon_of_isLoc h).2

/-- **The filled prefixes of the local curve are the relative hulls** at the physical times `τ + clockOf (T − τ) v`. -/
theorem fillH_curve {v : ℝ} (hv : 0 ≤ v) :
    fillH (F.curve w T '' Icc 0 v) =
      F.hullAt w (F.ent w + (clockOf ((T : ℝ) - F.ent w) v).toNNReal) := by
  obtain ⟨hL, hL0⟩ := horizon_of_isLoc h
  obtain ⟨-, -, -, hfill, -⟩ := exists_relCurve_of_data h.1.1 h.1.2.1 h.1.2.2.1 h.1.2.2.2.2 hF.2.1 hF.2.2.1
    hF.2.2.2.1 hF.2.2.2.2.1 (clause_entry hF h.1) (clause_traversal hF h.1) (clause_density hF h.1)
    hF.2.2.2.2.2 hL
  have hc0 := clockOf_nonneg hL0 hv
  have hcL := (clockOf_lt hL0 hv).le
  rw [curve, image_relCurve_Icc _ hL0 hv]
  refine (hfill _ ⟨hc0, hcL⟩).trans ?_
  simp only [relHull, hullAt, relHullFam, NNReal.coe_add, Real.coe_toNNReal _ hc0]
  rfl

/-- **The capacity clock of the local curve is the relative capacity clock.** -/
theorem capClock_curve {v : ℝ} (hv : 0 ≤ v) :
    capClock (F.curve w T) v = F.rcap w (F.ent w + (clockOf ((T : ℝ) - F.ent w) v).toNNReal) := by
  rw [capClock, fillH_curve hF h hv]
  rfl

omit hF h in
/-- Every physical time of `[τ, T)` is a time of the local curve. -/
theorem exists_ent_add_clockOf_eq {t : ℝ≥0} (h1 : F.ent w ≤ t) (h2 : t < T) :
    ∃ v : ℝ, 0 ≤ v ∧ F.ent w + (clockOf ((T : ℝ) - F.ent w) v).toNNReal = t := by
  set L : ℝ := (T : ℝ) - F.ent w with hL
  set x : ℝ := (t : ℝ) - F.ent w with hx
  have hx0 : 0 ≤ x := sub_nonneg.2 (NNReal.coe_le_coe.2 h1)
  have hxL : x < L := by simp only [hx, hL]; linarith [NNReal.coe_lt_coe.2 h2]
  have hLx : 0 < L - x := sub_pos.2 hxL
  refine ⟨x / (L - x), div_nonneg hx0 hLx.le, ?_⟩
  have hcl : clockOf L (x / (L - x)) = x := by
    unfold clockOf
    have hne : L - x ≠ 0 := hLx.ne'
    have hL' : L ≠ 0 := ne_of_gt (lt_of_le_of_lt hx0 hxL)
    have h1' : 1 + x / (L - x) = L / (L - x) := by field_simp; ring
    rw [h1', div_div_div_cancel_right₀ hne]
    field_simp
  apply NNReal.eq
  rw [hcl, NNReal.coe_add, Real.coe_toNNReal _ hx0, hx]
  ring

end Local

/-! ### Hulls before the entry and bounded hulls -/

section Hulls

variable (hF : F.IsOk) {w : ℝ≥0 → ℝ} (hw : F.IsPathOk w)
include hF hw

theorem isOpen_C : IsOpen F.C :=
  isOpen_of_mem_betweenComponents (isClosed_range_of_isCompleteSimpleFlow hw.2.2.2.2.1)
    (isClosed_range_of_isCompleteSimpleFlow hw.2.2.2.2.2.1) hF.2.1

/-- **Before the entry the relative hull is empty.** -/
theorem hullAt_eq_empty_of_le {t : ℝ≥0} (ht : t ≤ F.ent w) : F.hullAt w t = ∅ := by
  have hCH : F.C ⊆ H := subset_H_of_mem_betweenComponents hF.2.1
  have hCc : IsPreconnected F.C := by
    obtain ⟨z, -, -, -, hz⟩ := hF.2.1
    rw [hz]
    exact isPreconnected_connectedComponentIn
  have he := fwdHull_inter_relDom_eq_empty hw.1 hw.2.1 hw.2.2.1 (isOpen_C hF hw) hCH hCc (ent_lt_exit hF hw)
    (clause_entry hF hw) (clause_density hF hw)
  have hsub : fwdHull (fun r : ℝ => w r.toNNReal) (t : ℝ) ∩ relDom F.C ⊆
      fwdHull (fun r : ℝ => w r.toNNReal) (F.ent w : ℝ) ∩ relDom F.C :=
    inter_subset_inter_left _ (QuantumZipper.fwdHull_mono.1 (NNReal.coe_le_coe.2 ht))
  rw [he, subset_empty_iff] at hsub
  simp only [hullAt, relHullFam, hsub, image_empty]

/-- **A bounded relative hull occurs before the exit** (at the exit the pocket is filled, `fill_of_exitShape`, and the
chart image of the whole pocket is `ℍ`). -/
theorem lt_exit_of_isBounded {t : ℝ≥0} (hb : Bornology.IsBounded (F.hullAt w t)) : (t : ℝ≥0∞) < F.exit w := by
  by_contra hn
  have hle : F.exit w ≤ t := le_of_not_gt hn
  have hfin : F.exit w < ⊤ := lt_of_le_of_lt hle ENNReal.coe_lt_top
  have hfill := fill_of_exitShape hw.2.2.1 hw.2.2.2.2 hF.1.walkExitShape hF.2.1 hF.2.2.2.1 hF.2.2.2.2.1 hfin
  have hσt : (F.exit w).toNNReal ≤ t := by
    rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hfin.ne]
    exact hle
  have hsub : relDom F.C ⊆ fwdHull (fun r : ℝ => w r.toNNReal) (t : ℝ) :=
    hfill.trans (QuantumZipper.fwdHull_mono.1 (NNReal.coe_le_coe.2 hσt))
  have hH : H ⊆ F.hullAt w t := by
    intro v hv
    have hm := relInvC_mem hF.2.2.2.1 hv
    exact ⟨relInvC F.c v, ⟨hsub hm, hm⟩, relMapC_relInvC hF.2.2.2.1 hv⟩
  exact not_isBounded_H (hb.subset hH)

end Hulls

/-! ### Identification of a driver by its hulls at the relative clock -/

/-- **A driver generating the relative hulls at the relative clock is the local curve's driver** below its lifetime
(GB6-RELSAFE's `eq_localDrv_of_version` for GW4; `IsDrivenCurve.segDrv_eq`): if `R` is continuous from `0` and
`fwdHull R (rcap t) = hullAt t` at every physical time `t ∈ [τ, T)` with `rcap t ≤ u`, then `R u = segDrv (curve T) u`
for `u` below the curve's lifetime. -/
theorem eq_segDrv_of_clockHull (hF : F.IsOk) {w : ℝ≥0 → ℝ} {T : ℝ≥0} (h : F.IsLoc w T) {R : ℝ → ℝ}
    (hRc : Continuous R) (hR0 : R 0 = 0) {u : ℝ≥0} (hu : (u : ℝ≥0∞) < capLife (F.curve w T))
    (hK : ∀ t : ℝ≥0, F.ent w ≤ t → t < T → F.rcap w t ≤ u → fwdHull R (F.rcap w t) = F.hullAt w t) :
    segDrv (F.curve w T) u = R u := by
  have hcv := isDrivenCurve_curve hF h
  obtain ⟨-, hL0⟩ := horizon_of_isLoc h
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ u) with h0u | hu0
  · subst h0u
    have h0 := hcv.segDriver_spec.1
    simp only [segDriver] at h0
    rw [NNReal.coe_zero, hR0]
    exact_mod_cast h0
  have hu' : ENNReal.ofReal (u : ℝ) < capLife (F.curve w T) := by rwa [ENNReal.ofReal_coe_nnreal]
  obtain ⟨hS0, hSu⟩ := hcv.capInv_spec u.coe_nonneg hu'
  have hSpos : 0 < capInv (F.curve w T) u := by
    rcases eq_or_lt_of_le hS0 with h' | h'
    · exfalso
      rw [← h', hcv.capClock_zero] at hSu
      exact (ne_of_lt hu0) (by exact_mod_cast hSu)
    · exact h'
  have hK' : ∀ τ' ∈ Icc 0 (capInv (F.curve w T) u),
      fwdHull R (capClock (F.curve w T) τ') = fillH (F.curve w T '' Icc 0 τ') := by
    intro τ' hτ'
    set t : ℝ≥0 := F.ent w + (clockOf ((T : ℝ) - F.ent w) τ').toNNReal with ht
    have hc0 := clockOf_nonneg hL0 hτ'.1
    have hcL := clockOf_lt hL0 hτ'.1
    have htT : t < T := by
      rw [← NNReal.coe_lt_coe, ht, NNReal.coe_add, Real.coe_toNNReal _ hc0]
      linarith
    have hle : capClock (F.curve w T) τ' ≤ u := by
      rw [← hSu]
      exact hcv.strictMonoOn_capClock.monotoneOn hτ'.1 hS0 hτ'.2
    rw [capClock_curve hF h hτ'.1, fillH_curve hF h hτ'.1]
    rw [capClock_curve hF h hτ'.1] at hle
    exact hK t le_self_add htT hle
  exact hcv.segDrv_eq hSpos hRc hR0 hK' u.coe_nonneg hSu.ge

/-! ### The lifetime of a local curve and the relative clock -/

section Clock

variable (hF : F.IsOk) {w : ℝ≥0 → ℝ} {T : ℝ≥0} (h : F.IsLoc w T)
include hF h

theorem ofReal_rcap_lt_capLife {t : ℝ≥0} (h1 : F.ent w ≤ t) (h2 : t < T) :
    ENNReal.ofReal (F.rcap w t) < capLife (F.curve w T) := by
  obtain ⟨v, hv, hvt⟩ := exists_ent_add_clockOf_eq h1 h2
  rw [← hvt, ← capClock_curve hF h hv]
  exact (isDrivenCurve_curve hF h).ofReal_capClock_lt hv

theorem exists_lt_rcap_of_lt_capLife {x : ℝ≥0∞} (hx : x < capLife (F.curve w T)) :
    ∃ t : ℝ≥0, F.ent w ≤ t ∧ t < T ∧ x < ENNReal.ofReal (F.rcap w t) := by
  obtain ⟨-, hL0⟩ := horizon_of_isLoc h
  obtain ⟨n, hn⟩ := lt_iSup_iff.1 hx
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  refine ⟨F.ent w + (clockOf ((T : ℝ) - F.ent w) n).toNNReal, le_self_add, ?_, ?_⟩
  · rw [← NNReal.coe_lt_coe, NNReal.coe_add, Real.coe_toNNReal _ (clockOf_nonneg hL0 hn0)]
    have := clockOf_lt hL0 hn0
    linarith
  · rw [← capClock_curve hF h hn0]
    exact hn

/-- The relative clock is monotone on `[τ, T)`. -/
theorem rcap_mono {t t' : ℝ≥0} (h1 : F.ent w ≤ t) (htt' : t ≤ t') (h2 : t' < T) : F.rcap w t ≤ F.rcap w t' := by
  obtain ⟨-, hL0⟩ := horizon_of_isLoc h
  obtain ⟨v, hv, hvt⟩ := exists_ent_add_clockOf_eq h1 (htt'.trans_lt h2)
  obtain ⟨v', hv', hvt'⟩ := exists_ent_add_clockOf_eq (h1.trans htt') h2
  rw [← hvt, ← hvt', ← capClock_curve hF h hv, ← capClock_curve hF h hv']
  have hcc : clockOf ((T : ℝ) - F.ent w) v ≤ clockOf ((T : ℝ) - F.ent w) v' := by
    have h3 := NNReal.coe_le_coe.2 htt'
    rw [← hvt, ← hvt', NNReal.coe_add, NNReal.coe_add, Real.coe_toNNReal _ (clockOf_nonneg hL0 hv),
      Real.coe_toNNReal _ (clockOf_nonneg hL0 hv')] at h3
    linarith
  have hvv : v ≤ v' := (strictMonoOn_clockOf hL0).le_iff_le hv hv' |>.1 hcc
  exact (isDrivenCurve_curve hF h).strictMonoOn_capClock.monotoneOn hv hv' hvv

end Clock

/-! ### The hull of the curve's driver -/

/-- **The hull of a driver that is the curve's driver before its lifetime**, at a capacity time `s` before the
lifetime, is the filled prefix at the inverse clock. -/
theorem fwdHull_eq_of_eq_segDriver {γ : ℝ → ℂ} (hcv : IsDrivenCurve γ) {s : ℝ≥0} (hs : (s : ℝ≥0∞) < capLife γ)
    {R : ℝ≥0 → ℝ} (hR : ∀ u : ℝ≥0, (u : ℝ≥0∞) < capLife γ → R u = segDriver γ u) :
    fwdHull (fun r : ℝ => R r.toNNReal) s = fillH (γ '' Icc 0 (capInv γ s)) := by
  have hs' : ENNReal.ofReal (s : ℝ) < capLife γ := by rwa [ENNReal.ofReal_coe_nnreal]
  obtain ⟨n, hn⟩ := exists_lt_capClock_of_lt_capLife hs'
  have hn0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  obtain ⟨W, hW, hW0, -, hm, -, hK⟩ := hcv.localDriver ((n : ℝ) + 1) hn0
  have hnS : capClock γ n ≤ capClock γ ((n : ℝ) + 1) :=
    hcv.strictMonoOn_capClock.monotoneOn (mem_Ici.2 (Nat.cast_nonneg n)) (mem_Ici.2 hn0.le) (by linarith)
  have hsS : (s : ℝ) < capClock γ ((n : ℝ) + 1) := hn.trans_le hnS
  have hSL := hcv.ofReal_capClock_lt hn0.le
  have hagree : ∀ r ∈ Icc (0 : ℝ) (capClock γ ((n : ℝ) + 1)), R r.toNNReal = W r := by
    intro r hr
    have hrL : ((r.toNNReal : ℝ≥0) : ℝ≥0∞) < capLife γ := by
      refine lt_of_le_of_lt ?_ hSL
      rw [← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal _ hr.1]
      exact ENNReal.ofReal_le_ofReal hr.2
    rw [hR _ hrL, segDriver, Real.coe_toNNReal _ hr.1]
    exact hcv.segDrv_eq hn0 hW hW0 (fun t ht => (hK t ht).2) hr.1 hr.2
  rw [fwdHull_eq_of_eqOn_of_lt s.coe_nonneg hsS hagree]
  obtain ⟨hI0, hIs⟩ := hcv.capInv_spec s.coe_nonneg hs'
  have hIS : capInv γ s ≤ (n : ℝ) + 1 := by
    by_contra hlt
    have := hcv.strictMonoOn_capClock hn0.le hI0 (lt_of_not_ge hlt)
    rw [hIs] at this
    linarith
  rw [← (hK _ ⟨hI0, hIS⟩).2, hIs]

/-! ### The trace stays in the closed pocket during the traversal -/

theorem trc_mem_relDomBar (hF : F.IsOk) {w : ℝ≥0 → ℝ} (hw : F.IsPathOk w) {t : ℝ≥0} (h1 : F.ent w ≤ t)
    (h2 : (t : ℝ≥0∞) < F.exit w) : trc w t ∈ relDomBar F.C F.E (F.αR F.s₁) := by
  obtain ⟨-, -, -, -, -, -, -, hcase⟩ := hF.2.2.2.2.2
  by_cases h0 : trc w t = 0
  · refine Or.inl ⟨h0, ?_⟩
    rcases hcase with ⟨hE', -⟩ | ⟨-, hs₂⟩
    · exact hE'
    · exact absurd h0 (trace_ne_zero_of_isBounded (continuous_trc hw) (hF.2.2.1.entry hs₂).2.2
        (clause_density hF hw) h1 h2)
  · refine Or.inr ⟨h0, clause_traversal hF hw t h1 h2 h0, fun hP => ?_⟩
    have : F.exit w ≤ (t : ℝ≥0∞) := iInf₂_le t ⟨h0, hP⟩
    exact absurd h2 (not_lt.2 this)

end Frame

end InteractingSLE.Theorem14.GW4Fix
