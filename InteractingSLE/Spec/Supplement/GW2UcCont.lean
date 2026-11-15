/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2UcStmt
import InteractingSLE.Spec.Supplement.GW2TzStmt
import InteractingSLE.Spec.Supplement.GW2PvDthE

/-!
# The stopped stage law where the first contact is away from the counterflow's tip (pathwise)

Packet PROVE-GW2-RELDET (round 39, decision D84). At one sample of ROOTX's good set, if the first root-`x` contact `τ`
is finite and not at the retained tip, the canonical relative driver `Wc` of `CanonContactStatement` (proved by
NEARIMG2, `GW2Ni.canonContactStatement`) is a canonical stopped driver for every version family whose caps lie below
the clock before the contact (`IsRelVersionX`):

* `Wc` generates the re-centred relative hulls before the contact, so it is a version with cap `⊤`; every version
  agrees with it below its cap (`GW2Pv.versions_agree_below`, after lowering the cap below a clock value);
* the stopped life is at most the contact life (the time set is smaller), below `Wc`'s trace lifetime;
* the clock is bounded before the contact.

* **`isCanonXS_of_contact`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Rd

open Exist Staged StagedLaw Restart Supp8.GB6 GW2TipSystem GW2TipSystem.RootC24 GW2Rz GW2Rv GW2Sde GW2Sdh

variable {Ω : Type u} [MeasurableSpace Ω]

/-- **The stopped stage law at a first contact away from the tip** (one sample). -/
theorem isCanonXS_of_contact (hCC : CanonContactStatement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) {GT : Set Ω}
    (hGT : ∀ ω ∈ GT, PhysGoodX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α ω)
    (hs : 0 < c.s) (hx : 0 ≤ rootPt r.1) {R : ℕ → ℝ≥0 → Ω → ℝ} {V : ℕ → Ω → ℝ≥0∞} {ξ : Ω} (hξ : ξ ∈ GT)
    (hR : ∀ n, VersionAtX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α (R n) (V n) ξ)
    (hRcov : ∀ n (u : ℝ≥0), (u : ℝ≥0∞) < V n ξ → ∃ t : ℝ≥0,
      (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ ∧
        (u : ℝ) < clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ)
    {τ : ℝ≥0} (hτ : contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ = τ)
    (hne : sphereInv (((rootPt r.1 : ℂ) + schedTr c r l a ξ τ : ℂ) : OnePoint ℂ) ≠ ((c.α ξ c.s : ℂ) : OnePoint ℂ))
    (hαs : c.α ξ c.s ≠ 0) :
    ∃ Wc : ℝ≥0 → ℝ, IsCanonXS c r l a R V ξ Wc := by
  obtain ⟨⟨hwc, hw0, hγ⟩, ⟨hα, hW, hW0, hζ⟩, harc, -, -⟩ := hGT ξ hξ
  obtain ⟨Wc, hWc, hWc0, hhull, ⟨ζc, ηc, hgen, hlife⟩, M, hM⟩ :=
    hCC c.W c.ζ ξ hα hW hW0 hζ hs hx harc hwc hw0 hγ hαs τ hτ hne
  have hlt : ∀ t : ℝ≥0, (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ → t < τ := fun t ht => by
    rw [hτ] at ht
    exact_mod_cast ht
  -- the canonical driver is a version with cap `⊤`
  have hWcV : VersionAtX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α (fun t (_ : Ω) => Wc t) ⊤
      ξ := ⟨hWc, hWc0, fun t ht _ => hhull t (hlt t ht)⟩
  -- the contact life bounds the stopped life
  have hbdd : BddAbove ((fun t => clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ) ''
      {t : ℝ≥0 | (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ}) :=
    ⟨M, by rintro _ ⟨t, ht, rfl⟩; exact hM t (hlt t ht)⟩
  have h0c : ((0 : ℝ≥0) : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ := by
    rw [ENNReal.coe_zero]
    exact GW2Rz.contact_pos c.W ξ hα hx harc hγ (s := c.s)
  have hstop : stopLifeX c r l a ξ ≤ GW2Bh.contactLifeX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ξ)
      (fun t => schedW c r l a t ξ) (schedTr c r l a ξ) (c.α ξ) :=
    csSup_le_csSup hbdd ⟨_, ⟨0, ⟨h0c, zero_le⟩, rfl⟩⟩ (image_mono fun t ht => ht.1)
  refine ⟨Wc, hWc, hWc0, fun n q hq => ?_, ⟨ζc, ηc, hgen, (ENNReal.ofReal_le_ofReal hstop).trans hlife⟩, M,
    fun t ht _ => hM t (hlt t ht)⟩
  -- a version agrees with `Wc` below its cap
  obtain ⟨t₁, ht₁, hqt⟩ := hRcov n q hq
  have hq1 : (q : ℝ≥0∞) < ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t₁ ξ) := by
    rw [← ENNReal.ofReal_coe_nnreal]
    exact (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt q.coe_nonneg hqt)).2 hqt
  obtain ⟨y, hqy, hy⟩ := exists_between (lt_min hq1 hq)
  have hRy : VersionAtX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α (R n) (fun _ => y) ξ :=
    ⟨(hR n).1, (hR n).2.1, fun t ht hty => (hR n).2.2 t ht (hty.trans (hy.le.trans (min_le_right _ _)))⟩
  exact GW2Pv.versions_agree_below hGT hs hx hξ hRy hWcV ht₁ (hy.trans_le (min_le_left _ _)) q hqy
    ENNReal.coe_lt_top

end InteractingSLE.Theorem14.GW2Rd
