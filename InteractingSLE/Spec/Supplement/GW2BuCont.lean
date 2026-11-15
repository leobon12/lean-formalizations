/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BuAgree
import InteractingSLE.Spec.Supplement.GW2BuElig

/-!
# The root-`x` contact clause with the exhaustion read at the sample

Packet PROVE-GW2-BUF (round 18). The successor of round 17's `ae_gapVanishes_contactX_versions` where the
exhaustion of the pre-contact clock is a premise at the sample, not an almost-sure hypothesis. RELDET's death family
exhausts the pre-contact clock only below the death. So the contact clause is used only at samples where the contact
comes before the death, where the exhaustion holds.

* **`ae_gapVanishes_contactX_versions_at`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory Complex
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdHull)

universe u

namespace InteractingSLE.Theorem14.GW2Bh

open Exist Staged StagedLaw MartChar.RealFlow Supp8 Supp8.GB6 Supp8.GB6.CoordB Supp8.Q3Rel Restart GW2TipSystem
  GW2TipSystem.RootC24 GW2Rz GW2Rd

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **The contact clause almost surely at a root `x`, with the exhaustion read at the sample.** -/
theorem ae_gapVanishes_contactX_versions_at (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (hx : 0 ≤ rootPt r.1) (hs : 0 < c.s)
    {R : ℕ → ℝ≥0 → Ω → ℝ} {V : ℕ → Ω → ℝ≥0∞}
    (hver : ∀ n, IsRelVersionX (rootPt r.1) c.s c.P c.W c.ζ (schedW c r l a) (schedTr c r l a) c.α (R n) (V n)) :
    ∀ᵐ ξ ∂c.P, ξ ∈ schedGTX h13 c r l a →
      (∀ t : ℝ≥0, (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ →
        ∃ n, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ) < V n ξ) →
      ∀ (Wc : ℝ≥0 → ℝ) (ζc : ℝ≥0∞) (ηc : ℝ≥0 → ℂ), Continuous Wc → Wc 0 = 0 → IsGeneratingTrace Wc ζc ηc →
      (∀ (n : ℕ) (q : ℝ≥0), (q : ℝ≥0∞) < V n ξ → R n q ξ = Wc q) →
      (∃ M : ℝ, ∀ t : ℝ≥0, (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ →
        clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ ≤ M) →
      ENNReal.ofReal (contactLifeX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ξ) (schedW c r l a · ξ)
        (schedTr c r l a ξ) (c.α ξ)) ≤ ζc →
      (baseL (rp (c.W · ξ)) c.s < 0 ∧
          junctionR (rp (c.W · ξ)) c.s - (relBdry (rp (c.W · ξ)) c.s (rootPt r.1)).re ≤
            (ηc (contactLifeX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ξ) (schedW c r l a · ξ)
              (schedTr c r l a ξ) (c.α ξ)).toNNReal).re ∧
          ∀ y : ℝ, y ≤ (ηc (contactLifeX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ξ) (schedW c r l a · ξ)
              (schedTr c r l a ξ) (c.α ξ)).toNNReal).re →
            GapVanishes (rp Wc) y (contactLifeX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ξ) (schedW c r l a · ξ)
              (schedTr c r l a ξ) (c.α ξ))) ∨
        (0 < baseR (rp (c.W · ξ)) c.s ∧
          (ηc (contactLifeX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ξ) (schedW c r l a · ξ)
              (schedTr c r l a ξ) (c.α ξ)).toNNReal).re ≤
            junctionL (rp (c.W · ξ)) c.s - (relBdry (rp (c.W · ξ)) c.s (rootPt r.1)).re ∧
          ∀ y : ℝ, (ηc (contactLifeX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ξ) (schedW c r l a · ξ)
              (schedTr c r l a ξ) (c.α ξ)).toNNReal).re ≤ y →
            GapVanishes (fun q => -rp Wc q) (-y) (contactLifeX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ξ)
              (schedW c r l a · ξ) (schedTr c r l a ξ) (c.α ξ))) := by
  have hverae : ∀ᵐ ξ ∂c.P, ∀ n, cfRec c.s c.W c.ζ ξ ∈ goodX (rootPt r.1) c.s →
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ →
        ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ) ≤ V n ξ →
        fwdHull (fun q : ℝ => R n q.toNNReal ξ) (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ) =
          hullX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ :=
    ae_all_iff.2 fun n => (hver n).2.2.2.2.2.2.mono fun ξ h hg => (h hg).2.2
  filter_upwards [hverae, ae_schedW_regular h13 c r l a, (schedGTX_spec h13 c r l a).2.2] with ξ hvξ
    hsch hGT hξ hexξ Wc ζc ηc hWc hWc0 hη hagree hbdd hLζ
  obtain ⟨⟨hwc, hw0, hγ⟩, ⟨hα, hW, hW0, hζ⟩, harc, -, hcf⟩ := (schedGTX_spec h13 c r l a).1 ξ hξ
  obtain ⟨-, -, -, htr⟩ := hsch
  have hgood : cfRec c.s c.W c.ζ ξ ∈ goodX (rootPt r.1) c.s := hGT.1 hξ
  have hclk := GW2Rz.clock_props c.W c.ζ ξ hα hW hW0 hζ hs hx harc hwc hw0 hγ
  have hnn : ∀ t : ℝ≥0, (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ →
      0 ≤ clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ := by
    intro t ht
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with h | h
    · rw [← h]; exact hclk.1.ge
    · have h0 : ((0 : ℝ≥0) : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ :=
        lt_of_le_of_lt (by exact_mod_cast zero_le) ht
      have := hclk.2.1 h0 ht h
      exact le_of_lt (lt_of_eq_of_lt hclk.1.symm this)
  have hK := hullX_of_versions (a := fun t => clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ)
    (Tc := contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ)
    (K := fun t => hullX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ) (R := fun n q => R n q ξ)
    (V := fun n => V n ξ) (Wc := Wc) (fun n t ht hle => hvξ n hgood t ht hle) (hexξ) hagree hnn
  exact gapVanishes_contactX c.W c.ζ ξ hα hW hW0 hζ hs hx harc hwc hw0 hγ htr hWc hWc0 hη hK hbdd hLζ

end InteractingSLE.Theorem14.GW2Bh
