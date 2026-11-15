/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BnMain
import InteractingSLE.Spec.Supplement.GW2BiHull

/-!
# The contact clause almost surely at J32's schedule instance (decision D17 (B))

Packet PROVE-GW2-BUF (round 11). The instance is J32's schedule at root `0`: counterflow `(c.W, c.α)` read at
`c.s`, explored driver `schedW c r l a` with trace `schedTr c r l a`.

* **`ae_gapVanishes_contact_root0`**: almost surely at every live sample, the contact clause holds for every
  canonical driver with the relative hulls before contact.
  * The hypotheses on the canonical driver: continuous from `0`, with a generating trace of lifetime at least the
    relative life; together they are the stage law of D17 (B), STAGEMEAN/RELDET's input.
  * The conclusion is `gapVanishes_contact_gb6`'s.
  * The sample-level facts come from landed lemmas: the counterflow trace and its regularity (`c.hα`,
    `GW2Later.ae_counterflow_regular`), the explored trace with transience (`GW2Rd.ae_schedW_regular`), and the
    interior counterflow tip on live samples (`ae_exactPair_root0`).
* **`hullIdentity_of_versions`** (deterministic): the stage law in FABLE-4's form is "the versions `R n` equal `Wc`
  before their announced stops `V n`, which exhaust the pre-contact clock". It gives the hull form above, through
  the versions' own hull identities.
* **`ae_gapVanishes_contact_root0_versions`**: the same clause, with the stage law in that version form, for any
  family of GB6 versions (`IsGB6RelVersion`) of the schedule instance exhausting the pre-contact clock almost
  surely (e.g. RELDET's monotone family).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)

universe u

namespace InteractingSLE.Theorem14.GW2Bh

open Exist Staged StagedLaw Restart Supp8 Supp8.GB6 Supp8.GB6.CoordB Supp8.GB6.RelDrv GW2TipSystem
  GW2TipSystem.RootC24 GW2Rd

/-- **The stage law in version form gives the hull form.** If the versions `R n` agree with `Wc` before their stops
`V n`, satisfy their hull identities at clock values `≤ V n`, and the stops exhaust the pre-contact clock, then `Wc`
has the relative hulls at every time before contact. -/
theorem hullIdentity_of_versions {wα w : ℝ≥0 → ℝ} {α γ : ℝ≥0 → ℂ} {s : ℝ≥0} {R : ℕ → ℝ≥0 → ℝ}
    {V : ℕ → ℝ≥0∞} {Wc : ℝ≥0 → ℝ}
    (hver : ∀ n : ℕ, ∀ t : ℝ≥0, (t : ℝ≥0∞) < contactTc α γ s → ENNReal.ofReal (relClk wα w s t) ≤ V n →
      fwdHull (rp (R n)) (relClk wα w s t) = relMap (rp wα) s '' fwdHull (rp w) t)
    (hexh : ∀ t : ℝ≥0, (t : ℝ≥0∞) < contactTc α γ s → ∃ n, ENNReal.ofReal (relClk wα w s t) < V n)
    (hagree : ∀ (n : ℕ) (q : ℝ≥0), (q : ℝ≥0∞) < V n → R n q = Wc q)
    (hnn : ∀ t : ℝ≥0, (t : ℝ≥0∞) < contactTc α γ s → 0 ≤ relClk wα w s t) :
    ∀ t : ℝ≥0, (t : ℝ≥0∞) < contactTc α γ s →
      fwdHull (rp Wc) (relClk wα w s t) = relMap (rp wα) s '' fwdHull (rp w) t := by
  intro t ht
  obtain ⟨n, hn⟩ := hexh t ht
  obtain ⟨t₂, ht₂0, hut₂, ht₂V⟩ := ENNReal.lt_iff_exists_real_btwn.1 hn
  have hut₂' : relClk wα w s t < t₂ := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (hnn t ht)).1 hut₂
  rw [← hver n t ht hn.le]
  refine fwdHull_eq_of_eqOn (hnn t ht) hut₂' fun r hr => ?_
  show Wc r.toNNReal = R n r.toNNReal
  exact (hagree n r.toNNReal ((ENNReal.ofReal_le_ofReal hr.2).trans_lt ht₂V)).symm

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **The contact clause almost surely at J32's schedule instance, root `0`, hull form of the stage law.** -/
theorem ae_gapVanishes_contact_root0 (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (hroot : rootPt r.1 = 0) :
    ∀ᵐ ξ ∂c.P, 0 < (RootJ31.sourceSample c r l a ξ).1 →
      ∀ (Wc : ℝ≥0 → ℝ) (ζc : ℝ≥0∞) (ηc : ℝ≥0 → ℂ), Continuous Wc → Wc 0 = 0 → IsGeneratingTrace Wc ζc ηc →
      (∀ t : ℝ≥0, (t : ℝ≥0∞) < contactTc (c.α ξ) (schedTr c r l a ξ) c.s →
        fwdHull (rp Wc) (relClk (c.W · ξ) (schedW c r l a · ξ) c.s t) =
          relMap (rp (c.W · ξ)) c.s '' fwdHull (rp (schedW c r l a · ξ)) t) →
      (∃ M : ℝ, ∀ t : ℝ≥0, (t : ℝ≥0∞) < contactTc (c.α ξ) (schedTr c r l a ξ) c.s →
        relClk (c.W · ξ) (schedW c r l a · ξ) c.s t ≤ M) →
      ENNReal.ofReal (contactLife (c.W · ξ) (schedW c r l a · ξ) (c.α ξ) (schedTr c r l a ξ) c.s) ≤ ζc →
      (baseL (rp (c.W · ξ)) c.s < 0 ∧
          junctionR (rp (c.W · ξ)) c.s ≤
            (ηc (contactLife (c.W · ξ) (schedW c r l a · ξ) (c.α ξ) (schedTr c r l a ξ) c.s).toNNReal).re ∧
          ∀ x : ℝ, x ≤ (ηc (contactLife (c.W · ξ) (schedW c r l a · ξ) (c.α ξ) (schedTr c r l a ξ)
              c.s).toNNReal).re →
            GapVanishes (rp Wc) x (contactLife (c.W · ξ) (schedW c r l a · ξ) (c.α ξ) (schedTr c r l a ξ) c.s)) ∨
        (0 < baseR (rp (c.W · ξ)) c.s ∧
          (ηc (contactLife (c.W · ξ) (schedW c r l a · ξ) (c.α ξ) (schedTr c r l a ξ) c.s).toNNReal).re ≤
            junctionL (rp (c.W · ξ)) c.s ∧
          ∀ x : ℝ, (ηc (contactLife (c.W · ξ) (schedW c r l a · ξ) (c.α ξ) (schedTr c r l a ξ)
              c.s).toNNReal).re ≤ x →
            GapVanishes (fun q => -rp Wc q) (-x)
              (contactLife (c.W · ξ) (schedW c r l a · ξ) (c.α ξ) (schedTr c r l a ξ) c.s)) := by
  filter_upwards [c.hα, GW2Later.ae_counterflow_regular h13 c.hκ c.hcf c.hζ, ae_schedW_regular h13 c r l a,
    ae_exactPair_root0 h13 c r l a hroot] with ξ hα hreg hsch hpair hlive Wc ζc ηc hWc hWc0 hη hK hbdd hLζ
  obtain ⟨_, _, hW, hW0, _⟩ := hreg
  obtain ⟨hw, hw0, hγ, htr⟩ := hsch
  have hsH : c.α ξ c.s ∈ H := (hpair hlive).2.1
  exact gapVanishes_contact_gb6 (wα := (c.W · ξ)) (w := (schedW c r l a · ξ)) (α := c.α ξ)
    (γ := schedTr c r l a ξ) (s := c.s) (Wc := Wc) (ζc := ζc) (ηc := ηc) hW hW0 hα hsH hw hw0 hγ htr hWc hWc0 hη
    hK hbdd hLζ

/-- **The contact clause almost surely at J32's schedule instance, root `0`, version form of the stage law**
(FABLE-4 §D17: the identification at the announced stops `V n`, which exhaust the pre-contact clock). -/
theorem ae_gapVanishes_contact_root0_versions (h13 : Exist.Theorem13Statement.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (hroot : rootPt r.1 = 0)
    {R : ℕ → ℝ≥0 → Ω → ℝ} {V : ℕ → Ω → ℝ≥0∞}
    (hver : ∀ n, IsGB6RelVersion c.s c.P (schedW c r l a) c.W c.ζ (schedTr c r l a) c.α (R n) (V n))
    (hexh : ∀ᵐ ξ ∂c.P, ∀ t : ℝ≥0, (t : ℝ≥0∞) < gb6Tc c.s (schedTr c r l a) c.α ξ →
      ∃ n, ENNReal.ofReal (gb6Clock c.s (schedW c r l a) c.W ξ t) < V n ξ) :
    ∀ᵐ ξ ∂c.P, 0 < (RootJ31.sourceSample c r l a ξ).1 →
      ∀ (Wc : ℝ≥0 → ℝ) (ζc : ℝ≥0∞) (ηc : ℝ≥0 → ℂ), Continuous Wc → Wc 0 = 0 → IsGeneratingTrace Wc ζc ηc →
      (∀ (n : ℕ) (q : ℝ≥0), (q : ℝ≥0∞) < V n ξ → R n q ξ = Wc q) →
      (∃ M : ℝ, ∀ t : ℝ≥0, (t : ℝ≥0∞) < contactTc (c.α ξ) (schedTr c r l a ξ) c.s →
        relClk (c.W · ξ) (schedW c r l a · ξ) c.s t ≤ M) →
      ENNReal.ofReal (contactLife (c.W · ξ) (schedW c r l a · ξ) (c.α ξ) (schedTr c r l a ξ) c.s) ≤ ζc →
      (baseL (rp (c.W · ξ)) c.s < 0 ∧
          junctionR (rp (c.W · ξ)) c.s ≤
            (ηc (contactLife (c.W · ξ) (schedW c r l a · ξ) (c.α ξ) (schedTr c r l a ξ) c.s).toNNReal).re ∧
          ∀ x : ℝ, x ≤ (ηc (contactLife (c.W · ξ) (schedW c r l a · ξ) (c.α ξ) (schedTr c r l a ξ)
              c.s).toNNReal).re →
            GapVanishes (rp Wc) x (contactLife (c.W · ξ) (schedW c r l a · ξ) (c.α ξ) (schedTr c r l a ξ) c.s)) ∨
        (0 < baseR (rp (c.W · ξ)) c.s ∧
          (ηc (contactLife (c.W · ξ) (schedW c r l a · ξ) (c.α ξ) (schedTr c r l a ξ) c.s).toNNReal).re ≤
            junctionL (rp (c.W · ξ)) c.s ∧
          ∀ x : ℝ, (ηc (contactLife (c.W · ξ) (schedW c r l a · ξ) (c.α ξ) (schedTr c r l a ξ)
              c.s).toNNReal).re ≤ x →
            GapVanishes (fun q => -rp Wc q) (-x)
              (contactLife (c.W · ξ) (schedW c r l a · ξ) (c.α ξ) (schedTr c r l a ξ) c.s)) := by
  have hverae : ∀ᵐ ξ ∂c.P, ∀ n, (c.s : ℝ≥0∞) < c.ζ ξ → c.α ξ c.s ∈ H → 0 < V n ξ ∧
      (∀ u : ℝ≥0, (u : ℝ≥0∞) < V n ξ → ∃ t : ℝ≥0, (t : ℝ≥0∞) < gb6Tc c.s (schedTr c r l a) c.α ξ ∧
        (u : ℝ) < gb6Clock c.s (schedW c r l a) c.W ξ t) ∧
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < gb6Tc c.s (schedTr c r l a) c.α ξ →
        ENNReal.ofReal (gb6Clock c.s (schedW c r l a) c.W ξ t) ≤ V n ξ →
        QuantumZipper.fwdHull (fun q : ℝ => R n q.toNNReal ξ) (gb6Clock c.s (schedW c r l a) c.W ξ t) =
          relMap (fun q : ℝ => c.W q.toNNReal ξ) c.s ''
            QuantumZipper.fwdHull (fun q : ℝ => schedW c r l a q.toNNReal ξ) t :=
    ae_all_iff.2 fun n => (hver n).2.2.2.2.2.2
  filter_upwards [ae_gapVanishes_contact_root0 h13 c r l a hroot, hverae, hexh, c.hα,
    GW2Later.ae_counterflow_regular h13 c.hκ c.hcf c.hζ, ae_schedW_regular h13 c r l a,
    ae_exactPair_root0 h13 c r l a hroot] with ξ hmain hvξ hexξ hα hreg hsch hpair hlive Wc ζc ηc hWc hWc0 hη
    hagree hbdd hLζ
  obtain ⟨_, _, hW, hW0, _⟩ := hreg
  obtain ⟨hw, hw0, hγ, -⟩ := hsch
  obtain ⟨hsζ, hsH, -⟩ := hpair hlive
  obtain ⟨ha0, hsm, -⟩ := relClk_props (wα := (c.W · ξ)) (w := (schedW c r l a · ξ)) (α := c.α ξ)
    (γ := schedTr c r l a ξ) (s := c.s) hW hW0 hα hsH hw hw0 hγ
  have hnn : ∀ t : ℝ≥0, (t : ℝ≥0∞) < contactTc (c.α ξ) (schedTr c r l a ξ) c.s →
      0 ≤ relClk (c.W · ξ) (schedW c r l a · ξ) c.s t := fun t ht => by
    have h0 : ((0 : ℝ≥0) : ℝ≥0∞) < contactTc (c.α ξ) (schedTr c r l a ξ) c.s :=
      lt_of_le_of_lt (by simp) ht
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with h | h
    · rw [← h, ha0]
    · have := hsm h0 ht h
      rw [ha0] at this
      exact this.le
  have hK := hullIdentity_of_versions (wα := (c.W · ξ)) (w := (schedW c r l a · ξ)) (α := c.α ξ)
    (γ := schedTr c r l a ξ) (s := c.s) (R := fun n q => R n q ξ) (V := fun n => V n ξ) (Wc := Wc)
    (fun n t ht hle => ((hvξ n hsζ hsH).2.2 t ht hle)) hexξ hagree hnn
  exact hmain hlive Wc ζc ηc hWc hWc0 hη hK hbdd hLζ

end InteractingSLE.Theorem14.GW2Bh
