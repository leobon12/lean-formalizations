/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BuInstGood
import InteractingSLE.Spec.Supplement.GW2BuKer

/-!
# The good events of the versions and their re-indexing

Packet PROVE-GW2-BUF (round 18; the version loss). For an exit rule `E n` (measurable), a candidate `a` is good at
version `j` when its cell exit on the version's stage path plus the stage start is below the cap.

* `goodVer`: that event.
* `goodFrom`: being good from version `k` on (`⋂_{j ≥ k}`).
* **`measurableSet_goodVer`**, `measurableSet_goodFrom`, `monotone_goodFrom`. With the owners' instance inputs every
  instance is good (`InstInputsX.goodX`), so its prefix record and stage path are measurable
  (`StageInst.GoodX.measurable_pre`).
* **`exists_reindex_goodFrom`**: one re-indexing `ψ a m ≥ m` (monotone, independent of `n`) makes the kernel loss of
  every selected candidate vanish (`exists_reindex_kernel_loss`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Bh

open Exist Staged StagedLaw Restart GW2TipSystem GW2TipSystem.RootC24 GW2Rz GW2Rd GW2Rv GW2Sdh GW2Sde

variable (h13 : Exist.Theorem13Statement.{u}) (ver : SchedVerXFamily.{u}) (ch : SchedChoiceFamily.{u})
  {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
  (l : List (EntryIdx c.Θ c.Q)) (hx : 0 ≤ rootPt r.1) (E : ℕ → RecData × (ℝ≥0 → ℝ) → ℝ≥0∞)

/-- **Candidate `a` is good at version `j`**: its cell exit plus the stage start is below the cap. -/
def goodVer (n a j : ℕ) : Set Ω :=
  {ξ | E n ((instX h13 ver ch Ω c r l a j hx).srecX c r l (rootPt r.1) ξ,
      fun t => (instX h13 ver ch Ω c r l a j hx).drvX c (rootPt r.1) t ξ) +
    (stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a) ((ver Ω c r l a).V j)
      (RootJ31.historyTime c r l) ξ : ℝ≥0∞) < (ver Ω c r l a).V j ξ}

/-- Candidate `a` is good from version `k` on. -/
def goodFrom (n a k : ℕ) : Set Ω := ⋂ j ∈ Ici k, goodVer h13 ver ch c r l hx E n a j

omit [StandardBorelSpace Ω] in
/-- The retained σ-algebra is a sub-σ-algebra. -/
theorem sigma_le_ambient (l : List (EntryIdx c.Θ c.Q)) : c.sigma r l ≤ ‹MeasurableSpace Ω› :=
  stageSigma_le c.hβA.1 c.hh.1 c.hcf c.s _ _

variable {h13 ver ch c r l hx E}

theorem measurableSet_goodVer (hI : InstInputsX h13 ver ch) (hTO : GW2Sdx.HistOrdered c r l) (hg : GoodRoot c r)
    (hE : ∀ n, Measurable (E n)) (n a j : ℕ) : MeasurableSet (goodVer h13 ver ch c r l hx E n a j) := by
  have hI' := hI.goodX hTO hg a j
  have hpre := hI'.measurable_pre
  have hrec : Measurable ((instX h13 ver ch Ω c r l a j hx).srecX c r l (rootPt r.1)) :=
    measurable_augRec ((measurable_stageEncRec_sigma c r l).mono (sigma_le_ambient c r l) le_rfl) hpre
  have hS : Measurable (stgStartX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a)
      ((ver Ω c r l a).V j) (RootJ31.historyTime c r l)) := measurable_stgStartX_of_pre hpre
  have hpath : Measurable fun ξ => fun t => (instX h13 ver ch Ω c r l a j hx).drvX c (rootPt r.1) t ξ :=
    measurable_pi_iff.2 fun t => measurable_stgDrv hI'.version.1 hI'.version.2.1 hS t
  have hV : Measurable ((ver Ω c r l a).V j) := hI'.version.2.2.2.2.1
  exact measurableSet_lt (((hE n).comp (hrec.prodMk hpath)).add (measurable_coe_nnreal_ennreal.comp hS)) hV

theorem measurableSet_goodFrom (hI : InstInputsX h13 ver ch) (hTO : GW2Sdx.HistOrdered c r l)
    (hg : GoodRoot c r) (hE : ∀ n, Measurable (E n)) (n a k : ℕ) :
    MeasurableSet (goodFrom h13 ver ch c r l hx E n a k) :=
  MeasurableSet.biInter (to_countable _) fun j _ => measurableSet_goodVer hI hTO hg hE n a j

theorem monotone_goodFrom (n a : ℕ) : Monotone (goodFrom h13 ver ch c r l hx E n a) := fun k k' hkk ξ hξ => by
  simp only [goodFrom, mem_iInter] at hξ ⊢
  exact fun j hj => hξ j (le_trans hkk hj)

/-- **One re-indexing for the version loss of every selected candidate.** -/
theorem exists_reindex_goodFrom (hI : InstInputsX h13 ver ch) (hTO : GW2Sdx.HistOrdered c r l)
    (hg : GoodRoot c r) (hE : ∀ n, Measurable (E n)) :
    ∃ ψ : ℕ → ℕ → ℕ, (∀ a, Monotone (ψ a)) ∧ (∀ a m, m ≤ ψ a m) ∧
      ∀ᵐ ω₀ ∂c.P, ∀ (sel : ℕ → ℕ → ℕ) (n : ℕ) {ε : ℝ≥0∞}, 0 < ε → ∀ᶠ m in atTop,
        condExpKernel c.P (c.sigma r l) ω₀ ({ξ | ∃ k, ξ ∈ goodFrom h13 ver ch c r l hx E n (sel n m) k} \
          goodFrom h13 ver ch c r l hx E n (sel n m) (ψ (sel n m) m)) ≤ ε :=
  exists_reindex_kernel_loss (sigma_le_ambient c r l) (goodFrom h13 ver ch c r l hx E)
    (measurableSet_goodFrom hI hTO hg hE) monotone_goodFrom

end InteractingSLE.Theorem14.GW2Bh
