/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BvShare

/-!
# The bad sets of the `kSel` bound

Packet PROVE-GW2-BUF (round 20; `hsrc`). NEARIMG2's `GW2Ni.exists_kSel` selects a candidate `Nat.pair i (Nat.pair q b)`
whose bad set `Z n i q b` has small conditional probability. The bad sets used here are independent of the version
index:

* `exitTerm n m a`: the exit rule on the killed stage path of the final near slot `(l, n, m, a)`;
* `Zb n i q b = ⋃ m, slotGood n m a ∩ {rootGain a < exitTerm n m a}` for `a = Nat.pair i (Nat.pair q b)`;
* **`measurableSet_Zb`** (with `measurable_rootGain`; the slots' stage data are measurable through the owners' instance
  inputs);
* **`srcBad_subset_Zb`**: the near stop is at most the exit term, so every source-buffer loss lies in `Zb`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Bh

open Restart Exist Exist.StagedLaw GW2TipSystem GW2TipSystem.RootC24 GW2Rz GW2Rd GW2Rv GW2Sde GW2Sdh GW2Sdx

/-- **J32's gain is measurable.** -/
theorem measurable_rootGain {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) :
    Measurable (GW2Sdg.rootGain c r l a) :=
  measurable_real_toNNReal.comp
    ((RootH29.measurable_forwardCapacity_random (rootPt r.1) c.s (RootJ31.measurable_futurePair c r l a)
      (measurable_const.add (RootJ31.measurable_sourceBuffer c r l a))).sub
    (RootH29.measurable_forwardCapacity_random (rootPt r.1) c.s (RootJ31.measurable_futurePair c r l a)
      measurable_const))

variable (h13 : Exist.Theorem13Statement.{u}) (h12 : Exist.Theorem12Statement.{u}) (K₀ : PkgFamily.{u})

section Sets

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
  (l : List (EntryIdx c.Θ c.Q))

/-- **The exit term of the final near slot** `(l, n, m, a)` at a nonnegative root: the exit rule on the killed stage
path of the instance of version `m`. -/
def exitTerm (hx : 0 ≤ rootPt r.1) (n m a : ℕ) (ξ : Ω) : ℝ≥0∞ :=
  exitB.{u} Ω c r l n a
    ((instX h13 (pkgVerF h13 h12) (pkgCh h13 h12 cwSrc) Ω c r l a m hx).srecX c r l (rootPt r.1) ξ,
      killPath ((fun t => (instX h13 (pkgVerF h13 h12) (pkgCh h13 h12 cwSrc) Ω c r l a m hx).drvX c (rootPt r.1) t ξ),
        (instX h13 (pkgVerF h13 h12) (pkgCh h13 h12 cwSrc) Ω c r l a m hx).capX c (rootPt r.1) ξ))

open Classical in
/-- **The bad set of the `kSel` bound** for level `n`, angle index `i`, cap index `q` and buffer `b`. -/
def Zb (n i q b : ℕ) : Set Ω :=
  if hg : GoodRoot c r then
    ⋃ m : ℕ, slotGood h13 h12 c r l n m (Nat.pair i (Nat.pair q b)) ∩
      {ξ | (GW2Sdg.rootGain c r l (Nat.pair i (Nat.pair q b)) ξ : ℝ≥0∞) <
        exitTerm h13 h12 c r l hg.1 n m (Nat.pair i (Nat.pair q b)) ξ}
  else ∅

theorem measurable_exitTerm (hI : InstInputsX h13 (pkgVerF h13 h12) (pkgCh h13 h12 cwSrc))
    (hTO : GW2Sdx.HistOrdered c r l) (hg : GoodRoot c r) (n m a : ℕ) :
    Measurable (exitTerm h13 h12 c r l hg.1 n m a) := by
  have hgood := hI.goodX hTO hg a m
  have hpre := hgood.measurable_pre
  have hrec : Measurable ((instX h13 (pkgVerF h13 h12) (pkgCh h13 h12 cwSrc) Ω c r l a m hg.1).srecX c r l
      (rootPt r.1)) :=
    measurable_augRec ((measurable_stageEncRec_sigma c r l).mono (sigma_le_ambient c r l) le_rfl) hpre
  have hS : Measurable (stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a)
      ((pkgVerF h13 h12 Ω c r l a).V m) (RootJ31.historyTime c r l)) := measurable_stgStartX_of_pre hpre
  have hD : ∀ t, Measurable ((instX h13 (pkgVerF h13 h12) (pkgCh h13 h12 cwSrc) Ω c r l a m hg.1).drvX c
      (rootPt r.1) t) := fun t => measurable_stgDrv hgood.version.1 hgood.version.2.1 hS t
  have hV : Measurable ((pkgVerF h13 h12 Ω c r l a).V m) := hgood.version.2.2.2.2.1
  have hcap : Measurable ((instX h13 (pkgVerF h13 h12) (pkgCh h13 h12 cwSrc) Ω c r l a m hg.1).capX c
      (rootPt r.1)) := hV.sub (measurable_coe_nnreal_ennreal.comp hS)
  exact (exitB_spec Ω c r l n a).2.comp (hrec.prodMk (measurable_killPath_comp hD hcap))

theorem measurableSet_slotGood (hg : GoodRoot c r) (n m a : ℕ) :
    MeasurableSet (slotGood h13 h12 c r l n m a) := by
  classical
  have e : slotGood h13 h12 c r l n m a = goodVer h13 (schedVerXDeathFamily h13) (pkgCh h13 h12 cwSrc) c r l hg.1
      (exitN c r l) n a (pkgPsi h13 (psiGoodFam h13 h12) Ω c r l a (m - 1) + (m - 1)) := by
    simp only [slotGood, hg, ↓reduceDIte]
  rw [e]
  exact measurableSet_goodVer_death h13 h12 c r l hg n a _

/-- **The bad sets are measurable.** -/
theorem measurableSet_Zb (hI : InstInputsX h13 (pkgVerF h13 h12) (pkgCh h13 h12 cwSrc))
    (hTO : GW2Sdx.HistOrdered c r l) (n i q b : ℕ) : MeasurableSet (Zb h13 h12 c r l n i q b) := by
  classical
  unfold Zb
  split_ifs with hg
  · exact MeasurableSet.iUnion fun m => (measurableSet_slotGood h13 h12 c r l hg n m _).inter
      (measurableSet_lt (measurable_coe_nnreal_ennreal.comp (measurable_rootGain c r l _))
        (measurable_exitTerm h13 h12 c r l hI hTO hg n m _))
  · exact MeasurableSet.empty

/-- **The near stop is at most the exit term.** -/
theorem nearStop_le_exitTerm (hg : GoodRoot c r) (n m a : ℕ) (ξ : Ω) :
    ((pkgX h13 (pkgVerF h13 h12) (pkgCh h13 h12 cwSrc) (pkgKbF h13 h12 K₀) Ω c r).nearVar l n m a).stop ξ ≤
      exitTerm h13 h12 c r l hg.1 n m a ξ := by
  rw [pkgNearVar_eq h13 h12 (psiGoodFam h13 h12) cwSrc exitB K₀ c r hg l n m a]
  change ((pkgKbF h13 h12 K₀ Ω c r).nearStop l n m a).stop ξ ≤ _
  simp only [pkgKbF, pkgKb, nearStopPkgX, hg, ↓reduceDIte]
  exact min_le_right _ _

/-- **Every source-buffer loss lies in the bad set** of its candidate's angle, cap and buffer indices. -/
theorem srcBad_subset_Zb (n m i q b : ℕ) :
    srcBad h13 h12 K₀ c r l n m (Nat.pair i (Nat.pair q b)) ⊆ Zb h13 h12 c r l n i q b := by
  classical
  intro ξ hξ
  by_cases hg : GoodRoot c r
  · have hZ : Zb h13 h12 c r l n i q b = ⋃ m : ℕ, slotGood h13 h12 c r l n m (Nat.pair i (Nat.pair q b)) ∩
        {ξ | (GW2Sdg.rootGain c r l (Nat.pair i (Nat.pair q b)) ξ : ℝ≥0∞) <
          exitTerm h13 h12 c r l hg.1 n m (Nat.pair i (Nat.pair q b)) ξ} := by
      simp only [Zb, hg, ↓reduceDIte]
    rw [hZ]
    exact mem_iUnion.2 ⟨m, hξ.1, lt_of_lt_of_le hξ.2 (nearStop_le_exitTerm h13 h12 K₀ c r l hg n m _ ξ)⟩
  · have h0 : slotGood h13 h12 c r l n m (Nat.pair i (Nat.pair q b)) = ∅ := by
      simp only [slotGood, hg, ↓reduceDIte]
    exact absurd hξ.1 (by rw [h0]; exact notMem_empty ξ)

end Sets

end InteractingSLE.Theorem14.GW2Bh
