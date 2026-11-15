/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2NiUncGlue
import InteractingSLE.Spec.Supplement.GW2NiBuf

/-!
# The kSel bound against the uncapped driver: caps past the exit, then buffers

Packet PROVE-GW2-NEARIMG2 (D50 (b)). Fix an angle index `i`. Suppose the uncapped exit `e` of the angle happens at a
physical time `t⋆` before the uncapped root-`x` contact and before the piece's death: `e + clock(T) < clock(t⋆)`
(clock of `uncW`). Then for every candidate `angCand i k` whose cap passes `t⋆ − T`, J32's gain of its buffer variants
eventually exceeds `e`. Below `T + cap` the capped candidate explores `uncW` and traces `uncTr` (D-b against the
uncapped driver), so its clock, contact and next record are the uncapped ones there; then the buffer limit
`eventually_lt_rootGain` applies.

* `clockX_congr`, `lt_contactX_congr` (clock and contact read the curve only up to the time);
* `nextRecord_time_angCand` (the next record's time is `min (cap, life)`);
* **`eventually_lt_rootGain_of_unc`** (one sample): the cap-level step of the kSel bound.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Ni

open Exist StagedLaw GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2Rz GW2Rd

section Congr

variable {Ω : Type*} (x : ℝ) (s : ℝ≥0) (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)

/-- The root-`x` clock at `t` reads the explored driver only up to `t`. -/
theorem clockX_congr {w w' : ℝ≥0 → Ω → ℝ} {ω : Ω} {t : ℝ≥0} (h : ∀ u ≤ t, w u ω = w' u ω) :
    clockX x s W ζ w t ω = clockX x s W ζ w' t ω := by
  unfold clockX recPair
  rw [GW2Wm.recOf_congr_top (f := fun u => w u ω) (g := fun u => w' u ω) h]

/-- Before the contact, read up to a time where two continuous traces agree. -/
theorem lt_contactX_congr {γ γ' α : Ω → ℝ≥0 → ℂ} {ω : Ω} (hγ : Continuous (γ ω)) (hγ' : Continuous (γ' ω))
    (hα : Continuous (α ω)) {t : ℝ≥0} (h : ∀ u ≤ t, γ ω u = γ' ω u) (ht : (t : ℝ≥0∞) < contactX x s γ α ω) :
    (t : ℝ≥0∞) < contactX x s γ' α ω := by
  unfold contactX at ht ⊢
  have h1 := (Gm.lt_firstContactTime_iff_noncontact (γ := fun u => (x : ℂ) + γ ω u)
    (continuous_const.add hγ) hα t s).1 ht
  refine (Gm.lt_firstContactTime_iff_noncontact (γ := fun u => (x : ℂ) + γ' ω u)
    (continuous_const.add hγ') hα t s).2 fun u hu v hv => ?_
  rw [← h u hu.2]
  exact h1 u hu v hv

end Congr

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (h13 : Exist.Theorem13Statement.{u})
  (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (i : ℕ)

omit [StandardBorelSpace Ω] in
/-- **The next record's time is `min (cap, life)`.** -/
theorem nextRecord_time_angCand (k : ℕ) (ω : Ω) :
    (nextRecord c r l (angCand i k) ω).2.1 = min ((timeEnumeration c r k : ℝ≥0) : ℝ≥0∞) (uncLife c r l i ω) := by
  rw [nextRecord_eq_of_angle c r l (a' := angCand i 0) (by rw [candidateAngle_angCand, candidateAngle_angCand]),
    candidateCap_angCand]
  rfl

/-- **The cap-level step of the kSel bound** (one sample). On the good set of the candidate `angCand i k`, with the
cover event and the history's success, let `e` be an exit with `e + clock(T) < clock(t⋆)` for the uncapped clock,
`t⋆` before the uncapped contact, before `T + ζ` and before `T + cap`, and let the capped candidate explore and trace
the uncapped curve up to `T + cap`. Then J32's gain of the buffer variants eventually exceeds `e`. -/
theorem eventually_lt_rootGain_of_unc (hx : 0 ≤ rootPt r.1) (k : ℕ) {ξ : Ω}
    (hξ : ξ ∈ schedGTX h13 c r l (angCand i k)) (hcov : ξ ∈ RootCv.coverEvent c r)
    (hold : oldSuccess c r l ξ)
    (hagW : ∀ t ≤ historyTime c r l + (timeEnumeration c r k : ℝ≥0),
      schedW c r l (angCand i k) t ξ = uncW c r l i t ξ)
    (hagT : ∀ t ≤ historyTime c r l + (timeEnumeration c r k : ℝ≥0),
      schedTr c r l (angCand i k) ξ t = uncTr c r l i ξ t)
    (hUc : Continuous (uncTr c r l i ξ)) {e : ℝ≥0∞} {t₀ : ℝ≥0}
    (ht₀c : t₀ < (timeEnumeration c r k : ℝ≥0)) (ht₀ζ : (t₀ : ℝ≥0∞) < uncLife c r l i ξ)
    (ht₀T : ((historyTime c r l + t₀ : ℝ≥0) : ℝ≥0∞) < contactX (rootPt r.1) c.s (uncTr c r l i) c.α ξ)
    (he : e + ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (uncW c r l i) (historyTime c r l) ξ) <
      ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (uncW c r l i) (historyTime c r l + t₀) ξ)) :
    ∀ᶠ b in atTop,
      e < (GW2Sdg.rootGain c r l (RootK32.candidateWithBuffer (angCand i k) b) ξ : ℝ≥0∞) := by
  set T := historyTime c r l with hT
  set q : ℝ≥0 := (timeEnumeration c r k : ℝ≥0) with hq
  obtain ⟨⟨-, -, hγ⟩, ⟨hα, -, -, -⟩, -, -, -⟩ := (schedGTX_spec h13 c r l (angCand i k)).1 ξ hξ
  have hγc : Continuous (schedTr c r l (angCand i k) ξ) := continuousOn_univ.1 (hγ.2.1.mono fun t _ =>
    show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  have hαc : Continuous (c.α ξ) := continuousOn_univ.1 (hα.2.1.mono fun t _ =>
    show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  have hTt : T + t₀ ≤ T + q := add_le_add le_rfl ht₀c.le
  -- the next record's time
  have hn : t₀ < (nextRecord c r l (angCand i k) ξ).2.1.toNNReal := by
    rw [nextRecord_time_angCand]
    have hfin : min ((q : ℝ≥0) : ℝ≥0∞) (uncLife c r l i ξ) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _)
    rw [← ENNReal.coe_lt_coe, ENNReal.coe_toNNReal hfin]
    exact lt_min (ENNReal.coe_lt_coe.2 ht₀c) ht₀ζ
  -- the contact
  have hcon : ((T + t₀ : ℝ≥0) : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l (angCand i k)) c.α ξ :=
    lt_contactX_congr (rootPt r.1) c.s (γ := uncTr c r l i) hUc hγc hαc
      (fun u hu => (hagT u (hu.trans hTt)).symm) ht₀T
  -- the clock
  have hcl : ∀ t ≤ T + q, clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l (angCand i k)) t ξ =
      clockX (rootPt r.1) c.s c.W c.ζ (uncW c r l i) t ξ := fun t ht =>
    clockX_congr _ _ _ _ fun u hu => hagW u (hu.trans ht)
  have he' : e + ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l (angCand i k)) T ξ) <
      ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l (angCand i k)) (T + t₀) ξ) := by
    rw [hcl _ le_self_add, hcl _ hTt]; exact he
  have hcap : t₀ < candidateCap c r (angCand i k) := by rw [candidateCap_angCand]; exact ht₀c
  exact eventually_lt_rootGain c r l (angCand i k) h13 hx hξ hcov hold hn hcap hcon he'

end InteractingSLE.Theorem14.GW2Ni
