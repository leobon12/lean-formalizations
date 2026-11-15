/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BvExit
import InteractingSLE.Spec.Supplement.GW2BvWord
import InteractingSLE.Spec.Supplement.GW2BuVer

/-!
# The goodness re-indexing of the package

Packet PROVE-GW2-BUF (round 19; the instance layer, the version loss). Round 18's good events (`goodVer`: the cell
exit plus the stage start below the cap) for RELDET's death family with the exit rules `exitB`. Their measurability
needs no instance inputs: the prefix record is measurable through ROOTX's physical filtration. Round 18's
`exists_reindex_kernel_loss` then gives one re-indexing making the version loss of every selected candidate vanish
under the kernel. It is the extra re-indexing `ψx` of the package.

* `exitN c r l n` (the exit rule of level `n`); **`measurableSet_goodVer_death`**;
* **`psiGood`**, `psiGoodFam` (the package's `ψx`), **`psiGood_spec`**: the kernel loss bound.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Bh

open Restart Exist Exist.StagedLaw GW2TipSystem GW2TipSystem.RootC24 GW2Rz GW2Rd GW2Rv GW2Sde GW2Sdh GW2Sdx

variable (h13 : Exist.Theorem13Statement.{u}) (h12 : Exist.Theorem12Statement.{u})

/-- The exit rule of level `n` at a history (`exitB` is independent of the candidate). -/
abbrev exitN {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (n : ℕ) : RecData × (ℝ≥0 → ℝ) → ℝ≥0∞ :=
  exitB.{u} Ω c r l n 0

section Meas

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
  (l : List (EntryIdx c.Θ c.Q))

/-- **The good events of the death family are measurable** (no instance inputs). -/
theorem measurableSet_goodVer_death (hg : GoodRoot c r) (n a j : ℕ) :
    MeasurableSet (goodVer h13 (schedVerXDeathFamily h13) (pkgCh h13 h12 cwSrc) c r l hg.1 (exitN c r l) n a j) := by
  obtain ⟨hx, hs⟩ := hg
  obtain ⟨hGT, hGTm, hGTae⟩ := schedGTX_spec h13 c r l a
  have hA := (schedVerXDeathFamily h13 Ω c r l a).isA hx j
  have hWm : ∀ t, Measurable (schedW c r l a t) := measurable_schedW c r l a
  have hpre : Measurable (stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a)
      ((schedVerXDeathFamily h13 Ω c r l a).V j) (RootJ31.historyTime c r l)
      ((schedVerXDeathFamily h13 Ω c r l a).R j)) :=
    (measurable_stgPreRecX hGT hs hx (measurable_gb6Rec_src c) hWm
      (measurableSet_goodSetX_physFilt (measurable_gb6Rec_src c) hWm hGTm hGTae) hA.1
      (RootJ31.historyTime c r l)).mono
      ((Supp8.RelSafe.physFilt (measurable_gb6Rec_src c) hWm c.P).le (RootJ31.historyTime c r l)) le_rfl
  have hrec : Measurable ((instX h13 (schedVerXDeathFamily h13) (pkgCh h13 h12 cwSrc) Ω c r l a j hx).srecX c r l
      (rootPt r.1)) :=
    measurable_augRec ((measurable_stageEncRec_sigma c r l).mono (sigma_le_ambient c r l) le_rfl) hpre
  have hS : Measurable (stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a)
      ((schedVerXDeathFamily h13 Ω c r l a).V j) (RootJ31.historyTime c r l)) := measurable_stgStartX_of_pre hpre
  have hpath : Measurable fun ξ => fun t =>
      (instX h13 (schedVerXDeathFamily h13) (pkgCh h13 h12 cwSrc) Ω c r l a j hx).drvX c (rootPt r.1) t ξ :=
    measurable_pi_iff.2 fun t => measurable_stgDrv hA.1.1.1 hA.1.1.2.1 hS t
  have hV : Measurable ((schedVerXDeathFamily h13 Ω c r l a).V j) := hA.1.1.2.2.2.2.1
  exact measurableSet_lt ((((exitB_spec Ω c r l n 0).2).comp (hrec.prodMk hpath)).add
    (measurable_coe_nnreal_ennreal.comp hS)) hV

theorem measurableSet_goodFrom_death (hg : GoodRoot c r) (n a k : ℕ) :
    MeasurableSet (goodFrom h13 (schedVerXDeathFamily h13) (pkgCh h13 h12 cwSrc) c r l hg.1 (exitN c r l) n a k) :=
  MeasurableSet.biInter (to_countable _) fun j _ => measurableSet_goodVer_death h13 h12 c r l hg n a j

end Meas

open Classical in
/-- **The goodness re-indexing** (round 18's kernel loss lemma on the death family's good events; the identity off
the good roots). -/
def psiGood (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) : ℕ → ℕ → ℕ :=
  if hg : GoodRoot c r then
    (exists_reindex_kernel_loss (P := c.P) (sigma_le_ambient c r l)
      (goodFrom h13 (schedVerXDeathFamily h13) (pkgCh h13 h12 cwSrc) c r l hg.1 (exitN c r l))
      (measurableSet_goodFrom_death h13 h12 c r l hg) monotone_goodFrom).choose
  else fun _ m => m

/-- The package's extra re-indexing. -/
def psiGoodFam : PsiFam.{u} := fun Ω _ _ c r l => psiGood h13 h12 Ω c r l

/-- **The kernel loss bound of the goodness re-indexing.** -/
theorem psiGood_spec {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (hg : GoodRoot c r) :
    ∀ᵐ ω₀ ∂c.P, ∀ (sel : ℕ → ℕ → ℕ) (n : ℕ) {ε : ℝ≥0∞}, 0 < ε → ∀ᶠ m in atTop,
      condExpKernel c.P (c.sigma r l) ω₀
        ({ξ | ∃ k, ξ ∈ goodFrom h13 (schedVerXDeathFamily h13) (pkgCh h13 h12 cwSrc) c r l hg.1 (exitN c r l) n
            (sel n m) k} \
          goodFrom h13 (schedVerXDeathFamily h13) (pkgCh h13 h12 cwSrc) c r l hg.1 (exitN c r l) n (sel n m)
            (psiGood h13 h12 Ω c r l (sel n m) m)) ≤ ε := by
  have e : psiGood h13 h12 Ω c r l = (exists_reindex_kernel_loss (P := c.P) (sigma_le_ambient c r l)
      (goodFrom h13 (schedVerXDeathFamily h13) (pkgCh h13 h12 cwSrc) c r l hg.1 (exitN c r l))
      (measurableSet_goodFrom_death h13 h12 c r l hg) monotone_goodFrom).choose := by
    simp only [psiGood, hg, ↓reduceDIte]
  rw [e]
  exact (exists_reindex_kernel_loss (P := c.P) (sigma_le_ambient c r l)
    (goodFrom h13 (schedVerXDeathFamily h13) (pkgCh h13 h12 cwSrc) c r l hg.1 (exitN c r l))
    (measurableSet_goodFrom_death h13 h12 c r l hg) monotone_goodFrom).choose_spec.2.2

end InteractingSLE.Theorem14.GW2Bh
