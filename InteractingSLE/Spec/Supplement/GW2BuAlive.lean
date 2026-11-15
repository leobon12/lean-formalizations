/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BuVer
import InteractingSLE.Spec.Supplement.GW2BuStmt
import InteractingSLE.Spec.Supplement.GW2GmQTest
import InteractingSLE.Spec.Supplement.GW2GmQJ32
import InteractingSLE.Spec.Supplement.GW2SdqGap

/-!
# Kernel samples of an alive history are alive; the base word is fixed under the kernel

Packet PROVE-GW2-BUF (round 18; the kernel transfer). The alive events of COVER's scaled family over J32 read the
actual tests, which are retained by the next history only on alive histories (GEOM2's `RootJ32.observation_alive`).
Tests built from the retained observations agree with the actual tests there, so they give the same alive events
(`Gm.mem_aliveTests_iff_of_alive`), and those alive events are retained (`TestEvents.measurableSet_aliveTests`).

* **`exists_alive_version`**: the scaled-alive event agrees almost surely with a `c.sigma r l`-event (for a gap known
  at the stage start, e.g. `GW2Sdq.gapFam`);
* **`ae_kernel_alive`**: for almost every alive `ω₀`, the conditional law at `ω₀` is carried by the alive event;
* **`ae_kernel_base_eq`**: for a base word retained up to null sets (`BaseSigmaStatement`, D35 (D-c)), almost every
  `ω₀` has the conditional law at `ω₀` carried by `{base = base ω₀}`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.GW2Bh

open Restart GW2TipSystem GW2TipSystem.RootC24

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **The scaled-alive event agrees almost surely with a retained event.** -/
theorem exists_alive_version (h13 : Exist.Theorem13Statement.{u}) (gap : RootCv.GapFamily.{u}) (c : SourceData Ω)
    (hgap : ∀ r : ScaledRootIdx c.Θ c.Q, Measurable[c.sigma r []] (gap Ω c r.1)) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) :
    ∃ A : Set Ω, MeasurableSet[c.sigma r l] A ∧ ∀ᵐ ω ∂c.P,
      (ω ∈ A ↔ ω ∈ ((GW2Sdz.J32S gap Ω c).experiment r).data.alive ((GW2Sdz.J32S gap Ω c).G r) l) := by
  classical
  have : Countable c.Θ := c.hΘc.to_subtype
  have : Countable c.Q := c.hQc.to_subtype
  choose g hgm hgeq using fun (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (q : c.Q) =>
    RootJ32.observation_alive h13 c r l a q q le_rfl
  set D := ((GW2Sdz.J32S gap Ω c).experiment r).data with hD
  set G := (GW2Sdz.J32S gap Ω c).G r with hG
  let T' : List (EntryIdx c.Θ c.Q) → ℕ → c.Q → Set Ω := fun l a q => g l a q ⁻¹' (D.I l a ×ˢ H)
  have hHm : MeasurableSet H := measurableSet_lt measurable_const Complex.measurable_im
  have hT'm : ∀ l a q, MeasurableSet[c.sigma r ((D.ang a, q) :: l)] (T' l a q) := fun l a q =>
    hgm l a q (measurableSet_Ioo.prod hHm)
  have hGm : MeasurableSet[c.sigma r []] G := RootCv.measurableSet_scaledCoverEvent c hgap r
  have hmono := rootSigma_le_cons c.hκ c.h12p c.βA c.c₀ c.h c.W c.ζ c.s r
  refine ⟨TestEvents.aliveTests G D.ang T' l, TestEvents.measurableSet_aliveTests hmono hGm hT'm l, ?_⟩
  have hall : ∀ᵐ ω ∂c.P, ∀ (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (q : c.Q),
      ω ∈ (RootJ32.experiment c r).data.alive ((RootJ32.construction c).G r) l →
        (RootJ32.experiment c r).data.observation l a q ω = g l a q ω :=
    ae_all_iff.2 fun l => ae_all_iff.2 fun a => ae_all_iff.2 fun q => hgeq l a q
  filter_upwards [hall] with ω hω
  refine Gm.mem_aliveTests_iff_of_alive (T := D.tests) (fun l a q hal => ?_) l
  have e := hω l a q (GW2Sdz.alive_scaled_subset gap Ω c r l hal)
  rw [RootK3.StageModelData.tests_eq_preimage_observation]
  show g l a q ω ∈ D.I l a ×ˢ H ↔ (RootJ32.experiment c r).data.observation l a q ω ∈ D.I l a ×ˢ H
  rw [e]

/-- **Kernel samples of an alive history are alive.** -/
theorem ae_kernel_alive (h13 : Exist.Theorem13Statement.{u}) (gap : RootCv.GapFamily.{u}) (c : SourceData Ω)
    (hgap : ∀ r : ScaledRootIdx c.Θ c.Q, Measurable[c.sigma r []] (gap Ω c r.1)) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) :
    ∀ᵐ ω₀ ∂c.P, ω₀ ∈ ((GW2Sdz.J32S gap Ω c).experiment r).data.alive ((GW2Sdz.J32S gap Ω c).G r) l →
      ∀ᵐ ξ ∂condExpKernel c.P (c.sigma r l) ω₀,
        ξ ∈ ((GW2Sdz.J32S gap Ω c).experiment r).data.alive ((GW2Sdz.J32S gap Ω c).G r) l := by
  obtain ⟨A, hAm, hA⟩ := exists_alive_version h13 gap c hgap r l
  filter_upwards [hA, Sec7.Aux122Disint.ae_ae_condExpKernel (sigma_le_ambient c r l) hA,
    Sec7.Aux122Disint.ae_ae_condExpKernel_mem (sigma_le_ambient c r l) hAm] with ω₀ h1 h2 h3 halive
  filter_upwards [h2, h3 (h1.2 halive)] with ξ hξ hξA
  exact hξ.1 hξA

/-- **The gap family of the scaled cover in Theorem 1.4's assembly is known at the stage start.** -/
theorem ae_kernel_alive_gapFam (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) :
    ∀ᵐ ω₀ ∂c.P, ω₀ ∈ ((GW2Sdz.J32S GW2Sdq.gapFam Ω c).experiment r).data.alive
        ((GW2Sdz.J32S GW2Sdq.gapFam Ω c).G r) l →
      ∀ᵐ ξ ∂condExpKernel c.P (c.sigma r l) ω₀,
        ξ ∈ ((GW2Sdz.J32S GW2Sdq.gapFam Ω c).experiment r).data.alive ((GW2Sdz.J32S GW2Sdq.gapFam Ω c).G r) l :=
  ae_kernel_alive h13 GW2Sdq.gapFam c (GW2Sdq.measurable_gapFam Ω c) r l

/-- **A base word retained up to null sets is fixed under the conditional law.** -/
theorem ae_kernel_base_eq
    {base : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (_r : ScaledRootIdx c.Θ c.Q), List (EntryIdx c.Θ c.Q) → Ω → BoundaryWord}
    (hbase : BaseSigmaStatement base) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) :
    ∀ᵐ ω₀ ∂c.P, ∀ᵐ ξ ∂condExpKernel c.P (c.sigma r l) ω₀, base Ω c r l ξ = base Ω c r l ω₀ := by
  obtain ⟨g, hgm, hg⟩ := hbase Ω c r l
  filter_upwards [hg, Sec7.Aux122Disint.ae_ae_condExpKernel (sigma_le_ambient c r l) hg,
    Sec7.Aux122Disint.ae_ae_condExpKernel_eq (sigma_le_ambient c r l) hgm] with ω₀ h1 h2 h3
  filter_upwards [h2, h3] with ξ hξ hξ'
  rw [hξ, hξ', h1]

end InteractingSLE.Theorem14.GW2Bh
