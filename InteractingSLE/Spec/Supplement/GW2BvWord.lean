/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2BvPkg
import InteractingSLE.Spec.Supplement.GW2RjBd
import InteractingSLE.Spec.Supplement.GW2RuLive
import InteractingSLE.Spec.Supplement.GW2TuBot
import InteractingSLE.Spec.Supplement.GW2SdsWords

/-!
# The words of the re-indexed package (SDE's `hwords`)

Packet PROVE-GW2-BUF (round 19; D45 (1)). For the package `pkgB` of `GW2BvPkg`:

* `pkgNearVar_eq`: at a good root, the near slot `(l, n, m, a)` is the root-`x` instance of version `m` of the
  re-indexed death family with BUF's near stop.
* **`ae_nearWords_pkg`** (the `hword` premise of `withNearSB`'s words, any gap family): almost surely on the alive
  event, eventually in `m`, EVERY candidate's near slot has its record in its record event and reads the word
  `upW (θ_a χ) (pkgNb ω)`. The slot passes the history's clock (the cover re-indexing). Its prefix record is then
  the reference one (SDE's `ae_stgPreRecX_sched_eq`). The record event is met by SDE's `ae_notMem_launchBadRec`,
  `augRec_mem_succRec_iff` and `mem_aliveRecX`.
* **`ae_nearStructBot_pkgNb`** (the `hstruct` premise, rightward form): on `J32S GW2Sdq.gapFam`'s alive event, the
  near base word has the lower structure (RELDET's `GW2Rd.ae_nearStructBot_junction` at the reference slot).
* **`vwordsX_pkgB`**: `hwords` for the package, with SDE's slow words (`GW2Sdt.frameNSlowWordN_baseWm`) and the
  coverage `hcov_pkgVer`, for every extra re-indexing `ψx`, exit rule family `Ex`, base `K₀` and selector `kSel`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)

universe u

namespace InteractingSLE.Theorem14.GW2Bh

open Restart Exist Exist.StagedLaw GW2TipSystem GW2TipSystem.RootC24 GW2Rz GW2Rd GW2Rv GW2Sde GW2Sdh GW2Sdx

/-- SDE's counterflow word of the source (`GW2Sds.cfWordSrc`) at every source setup and root. -/
def cwSrc : CfWordB.{u} := fun _ _ _ c _ => GW2Sds.cfWordSrc c

section Words

variable (h13 : Exist.Theorem13Statement.{u}) (h12 : Exist.Theorem12Statement.{u}) (ψx : PsiFam.{u})
  (cw : CfWordB.{u}) (Ex : ExitFam.{u}) (K₀ : PkgFamily.{u})

/-- At a good root the near slot is the root-`x` instance of version `m` with BUF's near stop. -/
theorem pkgNearVar_eq {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (hg : GoodRoot c r) (l : List (EntryIdx c.Θ c.Q)) (n m a : ℕ) :
    (pkgX h13 (pkgVer h13 ψx) (pkgCh h13 h12 cw) (pkgKb h13 h12 ψx cw Ex K₀) Ω c r).nearVar l n m a =
      (instX h13 (pkgVer h13 ψx) (pkgCh h13 h12 cw) Ω c r l a m hg.1).varX c r l (rootPt r.1)
        ((pkgKb h13 h12 ψx cw Ex K₀ Ω c r).nearStop l n m a) := by
  change nearSlotX h13 (pkgVer h13 ψx) (pkgCh h13 h12 cw) (pkgKb h13 h12 ψx cw Ex K₀) Ω c r l n m a = _
  unfold nearSlotX
  simp only [hg, ↓reduceDIte]

/-- **The near words of the package's slots** (the `hword` premise): almost surely on the alive event, eventually in
`m`, every candidate's near slot has its record in its record event and reads `upW (θ_a χ) (pkgNb ω)`. -/
theorem ae_nearWords_pkg (gap : RootCv.GapFamily.{u}) (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) :
    ∀ᵐ ω ∂c.P, ω ∈ ((GW2Sdz.J32S gap Ω c).experiment r).data.alive ((GW2Sdz.J32S gap Ω c).G r) l →
      ∀ n : ℕ, ∀ᶠ m in atTop, ∀ a : ℕ,
        ((pkgX h13 (pkgVer h13 ψx) (pkgCh h13 h12 cw) (pkgKb h13 h12 ψx cw Ex K₀) Ω c r).nearVar l n m a).record ω ∈
          ((pkgX h13 (pkgVer h13 ψx) (pkgCh h13 h12 cw) (pkgKb h13 h12 ψx cw Ex K₀) Ω c r).nearVar l n m a).E ∧
        ((pkgX h13 (pkgVer h13 ψx) (pkgCh h13 h12 cw) (pkgKb h13 h12 ψx cw Ex K₀) Ω c r).nearVar l n m a).β
            (((pkgX h13 (pkgVer h13 ψx) (pkgCh h13 h12 cw) (pkgKb h13 h12 ψx cw Ex K₀) Ω c r).nearVar l n m a).record
              ω) =
          GW2Rd.upW ((RootJ31.candidateAngle c r a : ℝ) * chiC c.κ) (pkgNb h13 cw Ω c r l ω) := by
  classical
  by_cases hg : GoodRoot c r
  swap
  · filter_upwards [GW2Sds.ae_goodRoot_of_alive h13 c r l] with ω hω halive
    exact absurd (hω (GW2Sdz.alive_scaled_subset gap Ω c r l halive)) hg
  obtain ⟨hx, hs⟩ := hg
  set T := RootJ31.historyTime c r l with hTdef
  set x₀ := rootPt r.1 with hx₀
  have hpair : ∀ᵐ ω ∂c.P, ∀ p q : ℕ × ℕ, cfRec c.s c.W c.ζ ω ∈ goodX x₀ c.s →
      ((T : ℝ≥0∞) < contactX x₀ c.s (schedTr c r l p.1) c.α ω ∧
        ENNReal.ofReal (clockX x₀ c.s c.W c.ζ (schedW c r l p.1) T ω) <
          (schedVerXDeathFamily h13 Ω c r l p.1).V p.2 ω) →
      ((T : ℝ≥0∞) < contactX x₀ c.s (schedTr c r l q.1) c.α ω ∧
        ENNReal.ofReal (clockX x₀ c.s c.W c.ζ (schedW c r l q.1) T ω) <
          (schedVerXDeathFamily h13 Ω c r l q.1).V q.2 ω) →
      stgPreRecX x₀ c.s c.W c.ζ (schedW c r l p.1) (schedGTX h13 c r l p.1)
          ((schedVerXDeathFamily h13 Ω c r l p.1).V p.2) T ((schedVerXDeathFamily h13 Ω c r l p.1).R p.2) ω =
        stgPreRecX x₀ c.s c.W c.ζ (schedW c r l q.1) (schedGTX h13 c r l q.1)
          ((schedVerXDeathFamily h13 Ω c r l q.1).V q.2) T ((schedVerXDeathFamily h13 Ω c r l q.1).R q.2) ω :=
    ae_all_iff.2 fun p => ae_all_iff.2 fun q =>
      GW2Sdo.ae_stgPreRecX_sched_eq h13 c r l p.1 q.1 hs hx ((schedVerXDeathFamily h13 Ω c r l p.1).isA hx p.2).1.1
        ((schedVerXDeathFamily h13 Ω c r l q.1).isA hx q.2).1.1
  have hρ : ∀ᵐ ω ∂c.P, ∀ p : ℕ × ℕ, (schedVerXDeathFamily h13 Ω c r l p.1).V p.2 ω =
      ((schedVerXDeathFamily h13 Ω c r l p.1).isA hx p.2).1.2.choose
        (cfRec c.s c.W c.ζ ω, fun u => (schedVerXDeathFamily h13 Ω c r l p.1).R p.2 u ω) :=
    ae_all_iff.2 fun p => ((schedVerXDeathFamily h13 Ω c r l p.1).isA hx p.2).1.2.choose_spec.2.2
  have hcovAll : ∀ᵐ ω ∂c.P, ∀ a : ℕ, ω ∈ (RootJ32.experiment c r).data.alive ((RootJ32.construction c).G r) l →
      cfRec c.s c.W c.ζ ω ∈ goodX x₀ c.s → (T : ℝ≥0∞) < contactX x₀ c.s (schedTr c r l a) c.α ω →
      ∀ᶠ k in atTop, ENNReal.ofReal (clockX x₀ c.s c.W c.ζ (schedW c r l a) T ω) <
        (schedVerXDeathFamily h13 Ω c r l a).V k ω :=
    ae_all_iff.2 fun a => GW2Sdt.hcov_death h13 Ω c r l a ⟨hx, hs⟩
  have hGTall : ∀ᵐ ω ∂c.P, ∀ a, ω ∈ schedGTX h13 c r l a ↔ cfRec c.s c.W c.ζ ω ∈ goodX x₀ c.s :=
    ae_all_iff.2 fun a => (schedGTX_spec h13 c r l a).2.2
  filter_upwards [hpair, hρ, hcovAll, hGTall, GW2Sdt.ae_notMem_launchBadRec h13 c r l,
    GW2Ru.ae_alive_goodEvent_scaled h13 gap c r, ae_eventually_cov_all h13 ψx Ω c r l hx]
    with ω hpω hρω hcovω hGTω hlaunch hgoodEv hcovm halive n
  have halive32 := GW2Sdz.alive_scaled_subset gap Ω c r l halive
  obtain ⟨hcf, hcon⟩ := hgoodEv l halive
  have hold := RootJ32.oldSuccess_of_alive c r l ω halive32
  have hex : ∀ a, ∃ k, ω ∈ covEv h13 c r l a k := fun a => (hcovω a halive32 hcf (hcon a)).exists
  filter_upwards [hcovm] with m hm a
  have hslot := hm a (hex a)
  set j := pkgPsi h13 ψx Ω c r l a m + m with hj
  have hslot' : ENNReal.ofReal (clockX x₀ c.s c.W c.ζ (schedW c r l a) T ω) <
      (schedVerXDeathFamily h13 Ω c r l a).V j ω := hslot
  have hex0 : ∃ p : ℕ, ω ∈ covEv h13 c r l (Nat.unpair p).1 (Nat.unpair p).2 :=
    ⟨Nat.pair a j, by simp only [Nat.unpair_pair]; exact hslot'⟩
  have hpre : stgPreRecX x₀ c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a)
      ((schedVerXDeathFamily h13 Ω c r l a).V j) T ((schedVerXDeathFamily h13 Ω c r l a).R j) ω =
      refPre h13 Ω c r l ω := by
    simp only [refPre, hex0, ↓reduceDIte]
    exact hpω (a, j) ((Nat.unpair (Nat.find hex0)).1, (Nat.unpair (Nat.find hex0)).2) hcf ⟨hcon a, hslot'⟩
      ⟨hcon _, Nat.find_spec hex0⟩
  rw [pkgNearVar_eq h13 h12 ψx cw Ex K₀ c r ⟨hx, hs⟩ l n m a]
  have hA := (schedVerXDeathFamily h13 Ω c r l a).isA hx j
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · -- the record event of the choice
    have hE₀ : (pkgCh h13 h12 cw Ω c r l a).E₀ = (GW2Rd.launchBadRec c r l a)ᶜ := by
      rw [GW2Sdt.schedChoiceLinesX_E₀]
      rfl
    show augRec (stageEncRec c r l) (stgPreRecX x₀ c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a)
      ((schedVerXDeathFamily h13 Ω c r l a).V j) T ((schedVerXDeathFamily h13 Ω c r l a).R j)) ω ∈
        (pkgCh h13 h12 cw Ω c r l a).E₀
    rw [hE₀]
    exact hlaunch halive32 a _
  · -- success of the history
    exact (GW2Sdi.augRec_mem_succRec_iff c r l _ ω).2 hold
  · -- the live record
    have hstart : (stgStartX x₀ c.s c.W c.ζ (schedW c r l a) (schedGTX h13 c r l a)
        ((schedVerXDeathFamily h13 Ω c r l a).V j) T ω : ℝ≥0∞) < (schedVerXDeathFamily h13 Ω c r l a).V j ω := by
      rw [GW2Sdo.stgStartX_eq_clockX (schedGTX_spec h13 c r l a).1 hs hx ((hGTω a).2 hcf) (hcon a) hslot']
      exact hslot'
    exact GW2Sdo.mem_aliveRecX hA.1.2.choose_spec.2.1 (stgRecDec_stageEncRec c r l ω) (hA.1.1.2.1 ω)
      (hA.1.1.2.2.1 ω) hcf (hρω (a, j)) hstart
  · -- the word
    have hβ : (pkgCh h13 h12 cw Ω c r l a).β = GW2Wm.schedWordMapX c.κ (cw Ω c r) x₀ c.s (RootJ31.historyProgram c r l)
        ((entryList l).length + 1) (length_historyProgram c r l) (candAngle c r l a) := by
      rw [GW2Sdt.schedChoiceLinesX_β]
      rfl
    show (pkgCh h13 h12 cw Ω c r l a).β (augRec (stageEncRec c r l) (stgPreRecX x₀ c.s c.W c.ζ (schedW c r l a)
      (schedGTX h13 c r l a) ((schedVerXDeathFamily h13 Ω c r l a).V j) T
      ((schedVerXDeathFamily h13 Ω c r l a).R j)) ω) = _
    rw [hβ]
    unfold GW2Wm.schedWordMapX pkgNb
    rw [GW2Rj.candAngle_eq]
    congr 2
    simp only [augRec, hpre]

/-- **The lower structure of the near base word** (the `hstruct` premise in the rightward form): on
`J32S GW2Sdq.gapFam`'s alive event, `pkgNb` for SDE's counterflow word has `NearStructBot` at the near scale. -/
theorem ae_nearStructBot_pkgNb (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) :
    ∀ᵐ ω ∂c.P, ω ∈ ((GW2Sdz.J32S GW2Sdq.gapFam Ω c).experiment r).data.alive ((GW2Sdz.J32S GW2Sdq.gapFam Ω c).G r) l →
      GW2Sdy.NearStructBot c.κ (nearRootScale r.2 (nearLam Ω c r l ω)) (GW2Sdf.flipOf l.length)
        (pkgNb h13 cwSrc Ω c r l ω) := by
  classical
  by_cases hg : GoodRoot c r
  swap
  · filter_upwards [GW2Sds.ae_goodRoot_of_alive h13 c r l] with ω hω halive
    exact absurd (hω (GW2Sdz.alive_scaled_subset GW2Sdq.gapFam Ω c r l halive)) hg
  obtain ⟨hx, hs⟩ := hg
  have hbot : ∀ᵐ ω ∂c.P, ∀ p : ℕ × ℕ, ω ∈ ((GW2Sdz.J32S GW2Sdq.gapFam Ω c).experiment r).data.alive
        ((GW2Sdz.J32S GW2Sdq.gapFam Ω c).G r) l →
      ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l p.1) (RootJ31.historyTime c r l) ω) <
        (schedVerXDeathFamily h13 Ω c r l p.1).V p.2 ω →
      GW2Sdy.NearStructBot c.κ (nearRootScale r.2 (nearLam Ω c r l ω)) (GW2Sdf.flipOf l.length)
        (GW2Wm.baseWordX c.κ (GW2Sds.cfWordSrc c) (rootPt r.1) c.s (RootJ31.historyProgram c r l)
          ((entryList l).length + 1) (GW2Ru.length_historyProgram c r l)
          (augRec (stageEncRec c r l) (stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l p.1)
            (schedGTX h13 c r l p.1) ((schedVerXDeathFamily h13 Ω c r l p.1).V p.2) (RootJ31.historyTime c r l)
            ((schedVerXDeathFamily h13 Ω c r l p.1).R p.2)) ω)) :=
    ae_all_iff.2 fun p => GW2Rd.ae_nearStructBot_junction c r l p.1 hx hs
      ((schedVerXDeathFamily h13 Ω c r l p.1).isA hx p.2).1.1 ((schedVerXDeathFamily h13 Ω c r l p.1).fin p.2)
  have hcovAll : ∀ᵐ ω ∂c.P, ∀ a : ℕ, ω ∈ (RootJ32.experiment c r).data.alive ((RootJ32.construction c).G r) l →
      cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s →
      (RootJ31.historyTime c r l : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω →
      ∀ᶠ k in atTop, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (RootJ31.historyTime c r l) ω) <
        (schedVerXDeathFamily h13 Ω c r l a).V k ω :=
    ae_all_iff.2 fun a => GW2Sdt.hcov_death h13 Ω c r l a ⟨hx, hs⟩
  filter_upwards [hbot, hcovAll, GW2Ru.ae_alive_goodEvent_scaled h13 GW2Sdq.gapFam c r] with ω hbω hcovω hgoodEv
    halive
  have halive32 := GW2Sdz.alive_scaled_subset GW2Sdq.gapFam Ω c r l halive
  obtain ⟨hcf, hcon⟩ := hgoodEv l halive
  obtain ⟨k, hk⟩ := (hcovω 0 halive32 hcf (hcon 0)).exists
  have hex0 : ∃ p : ℕ, ω ∈ covEv h13 c r l (Nat.unpair p).1 (Nat.unpair p).2 :=
    ⟨Nat.pair 0 k, by simp only [Nat.unpair_pair]; exact hk⟩
  have h1 := hbω ((Nat.unpair (Nat.find hex0)).1, (Nat.unpair (Nat.find hex0)).2) halive (Nat.find_spec hex0)
  have hpre : augRec (stageEncRec c r l) (fun ω' => refPre h13 Ω c r l ω') ω =
      augRec (stageEncRec c r l) (stgPreRecX (rootPt r.1) c.s c.W c.ζ (schedW c r l (Nat.unpair (Nat.find hex0)).1)
        (schedGTX h13 c r l (Nat.unpair (Nat.find hex0)).1)
        ((schedVerXDeathFamily h13 Ω c r l (Nat.unpair (Nat.find hex0)).1).V (Nat.unpair (Nat.find hex0)).2)
        (RootJ31.historyTime c r l)
        ((schedVerXDeathFamily h13 Ω c r l (Nat.unpair (Nat.find hex0)).1).R (Nat.unpair (Nat.find hex0)).2)) ω := by
    simp only [augRec, refPre, hex0, ↓reduceDIte]
  unfold pkgNb
  rw [hpre]
  exact h1

variable (kSel : NearSelB.{u})

/-- **`hwords` for the re-indexed package** (SDE's `VWordsX` on `J32S GW2Sdq.gapFam` with SDE's counterflow word):
the near words from `ae_nearWords_pkg` and the lower structure, the slow words from SDE's
`GW2Sdt.frameNSlowWordN_baseWm` with the coverage `hcov_pkgVer`. -/
theorem vwordsX_pkgB (k : ℕ) :
    VWordsX (GW2Sdz.J32S.{u} GW2Sdq.gapFam) (pkgB h13 h12 ψx cwSrc Ex K₀ kSel k) nearLam := by
  refine vwordsX_withNearSB _ nearLam (pkgNb h13 cwSrc) (kSel k) nearLam_ne (fun Ω _ _ c r l => ?_)
    (fun Ω _ _ c r l => ae_nearStructBot_pkgNb h13 Ω c r l)
    (GW2Sdt.frameNSlowWordN_baseWm h12 h13 GW2Sdq.gapFam nearLam (pkgVer h13 ψx) cwSrc (hcov_pkgVer h13 ψx) _
      (fun _ _ _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ _ _ => rfl))
  filter_upwards [ae_nearWords_pkg h13 h12 ψx cwSrc Ex K₀ GW2Sdq.gapFam Ω c r l] with ω hω halive n
  filter_upwards [hω halive n] with m hm i k'
  obtain ⟨h1, h2⟩ := hm (Nat.pair i k')
  refine ⟨h1, ?_⟩
  rw [h2, GW2Sdy.candidateAngle_pair]

end Words

end InteractingSLE.Theorem14.GW2Bh
