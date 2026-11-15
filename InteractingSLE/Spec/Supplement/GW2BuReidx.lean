/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RvPkg

/-!
# Re-indexed version families

Packet PROVE-GW2-BUF (round 18; the instance layer). The near candidate changes with the index `m`, so the near
losses need the versions re-indexed uniformly over the candidates (`GW2Bh.exists_reindex_uniform`). A strictly
increasing re-indexing `φ a` of each candidate's versions keeps every field of ROOTX's `SchedVerX`:
* the versions;
* finite monotone caps (`monotone_nat_of_le_succ`);
* strictness on the good records (strict monotonicity composed with `φ a`);
* the exhaustion of the gain (eventually in `n`, since `φ a n → ∞`).

The root-`x` instance of version `n` of the re-indexed family is, definitionally, the instance of version `φ a n`
of the original one. So the owners' `InstInputsX` transfer.

* **`SchedVerX.reindex`**, **`verReindex`**, `reindex_V`, `reindex_R`, `instX_reindex`;
* **`InstInputsX.reindex`**;
* `reindexPlus ψ a m = ψ a m + m` (strictly increasing for monotone `ψ a`) and `strictMono_reindexPlus`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Bh

open Exist.StagedLaw GW2TipSystem GW2TipSystem.RootC24 GW2Rd GW2Rz GW2Sde GW2Sdh GW2Rv

section One

variable {Ω : Type u} [MeasurableSpace Ω] {c : SourceData Ω} {r : ScaledRootIdx c.Θ c.Q}
  {l : List (EntryIdx c.Θ c.Q)} {a : ℕ}

/-- **A version family re-indexed by a strictly increasing map.** -/
def _root_.InteractingSLE.Theorem14.GW2Rv.SchedVerX.reindex (v : SchedVerX c r l a) (φ : ℕ → ℕ)
    (hφ : StrictMono φ) : SchedVerX c r l a where
  R n := v.R (φ n)
  V n := v.V (φ n)
  isA hx n := v.isA hx (φ n)
  mono n ω := by
    have hm : Monotone fun k => v.V k ω := monotone_nat_of_le_succ fun k => v.mono k ω
    exact hm (hφ.monotone (Nat.le_succ n))
  fin n ω := v.fin (φ n) ω
  strict hx := (v.strict hx).mono fun ω h hg n => by
    have hs : StrictMono fun k => v.V k ω := strictMono_nat_of_lt_succ (h hg)
    exact hs (hφ (Nat.lt_succ_self n))
  exhausts hx := (v.exhausts hx).mono fun ξ h u hu => by
    obtain ⟨N, hN⟩ := eventually_atTop.1 (h u hu)
    exact eventually_atTop.2 ⟨N, fun n hn => hN (φ n) (hn.trans (hφ.id_le n))⟩

theorem reindex_V (v : SchedVerX c r l a) {φ : ℕ → ℕ} (hφ : StrictMono φ) (n : ℕ) :
    (v.reindex φ hφ).V n = v.V (φ n) := rfl

theorem reindex_R (v : SchedVerX c r l a) {φ : ℕ → ℕ} (hφ : StrictMono φ) (n : ℕ) :
    (v.reindex φ hφ).R n = v.R (φ n) := rfl

end One

/-- **Version families re-indexed per candidate.** -/
def verReindex (ver : SchedVerXFamily.{u})
    (φ : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (_r : ScaledRootIdx c.Θ c.Q), List (EntryIdx c.Θ c.Q) → ℕ → ℕ → ℕ)
    (hφ : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), StrictMono (φ Ω c r l a)) :
    SchedVerXFamily.{u} :=
  fun Ω _ _ c r l a => (ver Ω c r l a).reindex (φ Ω c r l a) (hφ Ω c r l a)

/-- **The re-indexed instance is the original instance at the re-indexed version.** -/
theorem instX_reindex (h13 : Exist.Theorem13Statement.{u}) (ver : SchedVerXFamily.{u}) (ch : SchedChoiceFamily.{u})
    (φ : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (_r : ScaledRootIdx c.Θ c.Q), List (EntryIdx c.Θ c.Q) → ℕ → ℕ → ℕ)
    (hφ : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), StrictMono (φ Ω c r l a))
    (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a n : ℕ) (hx : 0 ≤ rootPt r.1) :
    instX h13 (verReindex ver φ hφ) ch Ω c r l a n hx = instX h13 ver ch Ω c r l a (φ Ω c r l a n) hx := rfl

/-- **The owners' instance inputs transfer to a re-indexed family.** -/
theorem InstInputsX.reindex {h13 : Exist.Theorem13Statement.{u}} {ver : SchedVerXFamily.{u}}
    {ch : SchedChoiceFamily.{u}} (hI : InstInputsX h13 ver ch)
    (φ : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (_r : ScaledRootIdx c.Θ c.Q), List (EntryIdx c.Θ c.Q) → ℕ → ℕ → ℕ)
    (hφ : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), StrictMono (φ Ω c r l a)) :
    InstInputsX h13 (verReindex ver φ hφ) ch where
  word := hI.word
  measurableSet_E₀ := hI.measurableSet_E₀
  u₀ := hI.u₀
  openLines Ω _ _ c r l hTO h a n := hI.openLines Ω c r l hTO h a (φ Ω c r l a n)

/-- `ψ a m + m`: strictly increasing when `ψ a` is monotone. -/
def reindexPlus (ψ : ℕ → ℕ) (m : ℕ) : ℕ := ψ m + m

theorem strictMono_reindexPlus {ψ : ℕ → ℕ} (hψ : Monotone ψ) : StrictMono (reindexPlus ψ) := fun m m' h => by
  unfold reindexPlus
  exact Nat.add_lt_add_of_le_of_lt (hψ h.le) h

theorem le_reindexPlus (ψ : ℕ → ℕ) (m : ℕ) : ψ m ≤ reindexPlus ψ m := Nat.le_add_right _ _

end InteractingSLE.Theorem14.GW2Bh
