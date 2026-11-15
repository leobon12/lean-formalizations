/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2NiUncCongr
import InteractingSLE.Spec.Supplement.GW2NiUncTrans
import InteractingSLE.Spec.Supplement.GW2NtFrz

/-!
# The uncapped stage law from the capped one

Packet PROVE-GW2-NEARIMG2 (D50). `StageLawUXStatement` follows from the capped stage law `GW2Bh.StageLawXStatement`
(consumed as stated), the versions' exhaustion below the candidate's stop (`ExhStopStatement`: RELDET's death family,
D27, capped at the stop, D49), and `UncEndStatement` (the case no capped candidate sees). At a sample:
* **death first** (`ζ < ⊤`, `T + ζ` before the uncapped contact): a candidate whose cap is past `ζ` explores the
  uncapped curve on all of `[0, ∞)` (both are frozen after `T + ζ`: `GW2Nt.schedW_frozen`, `uncW_frozen`), so its
  contact, clock, hulls, death and relative life are the uncapped ones;
* **contact first, contact finite**: a candidate whose cap is past the contact explores the uncapped curve up to
  `T + cap`, past the contact (`contactX_eq_of_agree`, `contactLifeX_eq_of_agree`); the death clock is `⊤` for both;
* **no death, no contact**: `UncEndStatement`.
In the first two cases the capped canonical driver `Wc` is the uncapped one: its hull identity comes from the
versions (`hull_of_version`), its trace and clock bound from `IsCanonX`.

* `ExhStopStatement`, `hull_of_version`, `uncW_frozen`, **`isCanonUX_of_capped`**;
* **`stageLawUXStatement_of_capped`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (fwdHull)

universe u

namespace InteractingSLE.Theorem14.GW2Ni

open Exist StagedLaw GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2Rz GW2Rd

/-- **The versions exhaust the root-`x` clock below the candidate's stop** (before the contact, before `T + cap` and
below the death clock): the property of the version family the derivation uses (RELDET's death family, D27, with
D49's cap at the stop). -/
def ExhStopStatement (ver : GW2Rv.SchedVerXFamily.{u}) : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ), GW2Rv.GoodRoot c r → GW2Sdx.HistOrdered c r l →
    ∀ᵐ ω ∂c.P, cfRec c.s c.W c.ζ ω ∈ goodX (rootPt r.1) c.s → oldSuccess c r l ω → ∀ t : ℝ≥0,
      (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ω →
      t < historyTime c r l + candidateCap c r a →
      ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ω) < deathClockX c r l a ω →
      ∀ᶠ n in atTop, ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ω) <
        (ver Ω c r l a).V n ω

/-- A driver agreeing with a version below its cap generates the version's hull at a clock value below the cap. -/
theorem hull_of_version {u : ℝ} {R Wc : ℝ≥0 → ℝ} {V : ℝ≥0∞} {K : Set ℂ} (hnn : 0 ≤ u)
    (hver : fwdHull (fun q : ℝ => R q.toNNReal) u = K) (hlt : ENNReal.ofReal u < V)
    (hagree : ∀ q : ℝ≥0, (q : ℝ≥0∞) < V → R q = Wc q) : fwdHull (fun q : ℝ => Wc q.toNNReal) u = K := by
  obtain ⟨t₂, -, hut₂, ht₂V⟩ := ENNReal.lt_iff_exists_real_btwn.1 hlt
  have hut₂' : u < t₂ := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hnn).1 hut₂
  rw [← hver]
  refine InteractingSLE.fwdHull_eq_of_eqOn hnn hut₂' fun q hq => ?_
  exact (hagree q.toNNReal ((ENNReal.ofReal_le_ofReal hq.2).trans_lt ht₂V)).symm

section Sample

variable {Ω : Type u} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
  (l : List (EntryIdx c.Θ c.Q)) (i : ℕ)

/-- **The uncapped driver is frozen after a finite death** (one sample of a time-ordered history's success). -/
theorem uncW_frozen {ω : Ω} (hord : Sec5.Prop513Schedule.TimeOrdered 0 (historyProgram c r l))
    (hold : oldSuccess c r l ω)
    (hgood : ∀ a, ∀ (j : ℕ) (hj : j < (futureProgram c r l a).length), LocalExt.IsDrvGood
      (recHist (programRecords c (rootPt r.1) (futureProgram c r l a) ω ⟨j, hj⟩)))
    (hag : ∀ k k' (t : ℝ≥0), t ≤ historyTime c r l + (timeEnumeration c r k : ℝ≥0) →
      t ≤ historyTime c r l + (timeEnumeration c r k' : ℝ≥0) →
      schedW c r l (angCand i k) t ω = schedW c r l (angCand i k') t ω)
    (hfin : uncLife c r l i ω ≠ ⊤) {t : ℝ≥0}
    (ht : historyTime c r l + (uncLife c r l i ω).toNNReal ≤ t) :
    uncW c r l i t ω = uncW c r l i (historyTime c r l + (uncLife c r l i ω).toNNReal) ω := by
  set T := historyTime c r l with hT
  set ℓ := (uncLife c r l i ω).toNNReal with hℓ
  set a := angCand i (capIdx c r t) with ha
  have hang : candidateAngle c r a = candidateAngle c r (angCand i 0) := by
    rw [candidateAngle_angCand, candidateAngle_angCand]
  have hcap : t ≤ T + candidateCap c r a := by rw [candidateCap_angCand]; exact le_hist_capIdx c r l t
  have hζ : (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).2 = (ℓ : ℝ≥0∞) := by
    rw [futFam_eq_of_angle c r l hang ω, hℓ, ENNReal.coe_toNNReal hfin]
  have hmin : min (candidateCap c r a : ℝ≥0∞) (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).2 =
      (ℓ : ℝ≥0∞) := by
    rw [hζ]
    exact min_eq_right (ENNReal.coe_le_coe.2 (le_of_add_le_add_left (ht.trans hcap)))
  have hst : ∀ s, T + ℓ ≤ s → s ≤ T + candidateCap c r a →
      schedW c r l a s ω = Swc.joinDrv (GW2Tip.specDelta (schedSpec (rootPt r.1) (futureProgram c r l a)))
        (fun j => GW2Olm.futFam c r l a j ω) (GW2Olm.curIdx c r l) T +
        (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).1 ℓ := by
    intro s hs1 hs2
    rw [schedW_eq_stop c r l a hord hold (hgood a) (le_self_add.trans hs1) hs2, stopDrv_of_ge, hmin,
      ENNReal.toNNReal_coe]
    rw [hmin, Real.toNNReal_coe]
    exact ENNReal.coe_le_coe.2 (le_tsub_of_add_le_left hs1)
  have hTu : uncW c r l i (T + ℓ) ω = schedW c r l a (T + ℓ) ω :=
    hag _ _ (T + ℓ) (le_hist_capIdx c r l _) (ht.trans (le_hist_capIdx c r l t))
  change schedW c r l a t ω = _
  rw [hTu, hst t ht hcap, hst (T + ℓ) le_rfl (ht.trans hcap)]

end Sample

section Transfer

variable {Ω : Type u} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
  (l : List (EntryIdx c.Θ c.Q)) (i : ℕ)

/-- **A capped canonical driver whose candidate explores the uncapped curve before its contact is an uncapped
canonical driver**, when the contacts agree and the uncapped death region is inside the candidate's. -/
theorem isCanonUX_of_capped (a : ℕ) {ξ : Ω} {Wc : ℝ≥0 → ℝ} (hWc : Continuous Wc) (hWc0 : Wc 0 = 0)
    (hK : ∀ t : ℝ≥0, (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ →
      t < historyTime c r l + candidateCap c r a →
      ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ) < deathClockX c r l a ξ →
      fwdHull (fun q : ℝ => Wc q.toNNReal) (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ) =
        hullX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ)
    (htr : ∃ (ζc : ℝ≥0∞) (ηc : ℝ≥0 → ℂ), IsGeneratingTrace Wc ζc ηc ∧
      ENNReal.ofReal (GW2Bh.contactLifeX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ξ) (schedW c r l a · ξ)
        (schedTr c r l a ξ) (c.α ξ)) ≤ ζc)
    (hbd : ∃ M : ℝ, ∀ t : ℝ≥0, (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ →
      clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ ≤ M)
    (hc : contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ = contactX (rootPt r.1) c.s (uncTr c r l i) c.α ξ)
    (hw : ∀ t : ℝ≥0, (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (uncTr c r l i) c.α ξ →
      ∀ u ≤ t, schedW c r l a u ξ = uncW c r l i u ξ)
    (hd : ∀ t : ℝ≥0, (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (uncTr c r l i) c.α ξ →
      ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (uncW c r l i) t ξ) < uncDeathX c r l i ξ →
      t < historyTime c r l + candidateCap c r a ∧
        ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ) < deathClockX c r l a ξ) :
    IsCanonUX c r l i ξ Wc := by
  have hcl : ∀ t : ℝ≥0, (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (uncTr c r l i) c.α ξ →
      clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ = clockX (rootPt r.1) c.s c.W c.ζ (uncW c r l i) t ξ :=
    fun t ht => clockX_congr _ _ _ _ (hw t ht)
  refine ⟨hWc, hWc0, fun t ht hdt => ?_, ?_, ?_⟩
  · obtain ⟨htc, hdt'⟩ := hd t ht hdt
    rw [← hcl t ht, ← hullX_congr _ _ _ _ (hw t ht)]
    exact hK t (by rw [hc]; exact ht) htc hdt'
  · obtain ⟨ζc, ηc, hη, hle⟩ := htr
    refine ⟨ζc, ηc, hη, ?_⟩
    rwa [contactLifeX_eq_of_agree (rootPt r.1) c.s (cfRec c.s c.W c.ζ ξ) (w := fun u => uncW c r l i u ξ)
      (w' := fun u => schedW c r l a u ξ) (γ := uncTr c r l i ξ) (γ' := schedTr c r l a ξ) (α := c.α ξ) hc
      (fun t ht u hu => (hw t ht u hu).symm)]
  · obtain ⟨M, hM⟩ := hbd
    exact ⟨M, fun t ht => by rw [← hcl t ht]; exact hM t (by rw [hc]; exact ht)⟩

end Transfer

section Law

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (h13 : Exist.Theorem13Statement.{u})
  (ver : GW2Rv.SchedVerXFamily.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q))

include h13 in
/-- **The capped canonical driver of a candidate, with its hull identity below the stop** (almost surely). -/
theorem ae_capped_canon (hlaw : GW2Bh.StageLawXStatement h13 ver) (hexh : ExhStopStatement ver)
    (hg : GW2Rv.GoodRoot c r) (hord : GW2Sdx.HistOrdered c r l) (a : ℕ) :
    ∀ᵐ ξ ∂c.P, cfRec c.s c.W c.ζ ξ ∈ goodX (rootPt r.1) c.s → oldSuccess c r l ξ →
      ∃ Wc : ℝ≥0 → ℝ, Continuous Wc ∧ Wc 0 = 0 ∧
        (∀ t : ℝ≥0, (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ →
          t < historyTime c r l + candidateCap c r a →
          ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ) < deathClockX c r l a ξ →
          fwdHull (fun q : ℝ => Wc q.toNNReal) (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ) =
            hullX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ) ∧
        (∃ (ζc : ℝ≥0∞) (ηc : ℝ≥0 → ℂ), IsGeneratingTrace Wc ζc ηc ∧
          ENNReal.ofReal (GW2Bh.contactLifeX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ξ) (schedW c r l a · ξ)
            (schedTr c r l a ξ) (c.α ξ)) ≤ ζc) ∧
        ∃ M : ℝ, ∀ t : ℝ≥0, (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ →
          clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ ≤ M := by
  have : Countable ℕ := inferInstance
  have hV : ∀ᵐ ξ ∂c.P, ∀ n, cfRec c.s c.W c.ζ ξ ∈ goodX (rootPt r.1) c.s →
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ →
        ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ) ≤ (ver Ω c r l a).V n ξ →
        fwdHull (fun q : ℝ => (ver Ω c r l a).R n q.toNNReal ξ)
          (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ) =
          hullX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ :=
    ae_all_iff.2 fun n => (((ver Ω c r l a).isA hg.1 n).1.1.2.2.2.2.2.2).mono fun ξ h hgx => (h hgx).2.2
  filter_upwards [hlaw Ω c r l a hg hord, (schedGTX_spec h13 c r l a).2.2, hV, hexh Ω c r l a hg hord]
    with ξ hL hGT hVξ hE hgx hold
  have hξ : ξ ∈ schedGTX h13 c r l a := hGT.2 hgx
  obtain ⟨Wc, hWc, hWc0, hagree, htr, hbd⟩ := hL hξ hold
  obtain ⟨⟨hwc, hw0, hγ⟩, ⟨hα, hW, hW0, hζ⟩, harc, -, -⟩ := (schedGTX_spec h13 c r l a).1 ξ hξ
  obtain ⟨ha0, hsm, -⟩ := GW2Rz.clock_props c.W c.ζ ξ hα hW hW0 hζ hg.2 hg.1 harc hwc hw0 hγ
  refine ⟨Wc, hWc, hWc0, fun t ht htc hdt => ?_, htr, hbd⟩
  obtain ⟨n, hn⟩ := (hE hgx hold t ht htc hdt).exists
  have hnn : 0 ≤ clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ := by
    have h0 : ((0 : ℝ≥0) : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ :=
      lt_of_le_of_lt (ENNReal.coe_le_coe.2 zero_le) ht
    have h := hsm.monotoneOn h0 ht (zero_le : (0 : ℝ≥0) ≤ t)
    have h0' : clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) 0 ξ = 0 := ha0
    change clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) 0 ξ ≤ _ at h
    rwa [h0'] at h
  exact hull_of_version (R := fun q => (ver Ω c r l a).R n q ξ) (V := (ver Ω c r l a).V n ξ) hnn
    (hVξ n hgx t ht hn.le) hn (hagree n)

/-- **The uncapped stage law from the capped one** (D50): `GW2Bh.StageLawXStatement` (as stated), the versions'
exhaustion below the stop, and `UncEndStatement` give `StageLawUXStatement`. -/
theorem stageLawUXStatement_of_capped (h13 : Exist.Theorem13Statement.{u}) (ver : GW2Rv.SchedVerXFamily.{u})
    (hlaw : GW2Bh.StageLawXStatement h13 ver) (hexh : ExhStopStatement ver) (hend : UncEndStatement.{u}) :
    StageLawUXStatement.{u} := by
  intro Ω _ _ c r l i hg hord
  have : Countable ℕ := inferInstance
  filter_upwards [ae_all_iff.2 fun a => ae_capped_canon h13 ver c r l hlaw hexh hg hord a,
    uncAgreeStatement' h13 c r l i, ae_uncW_regular h13 c r l i,
    ae_all_iff.2 fun a => ae_schedW_regular h13 c r l a, Gm.ae_futureJoined_trace h13 c r,
    ae_angCand_facts h13 c r l i, hend Ω c r l i hg hord,
    ae_all_iff.2 fun a => (schedGTX_spec h13 c r l a).2.2] with ξ hcan hUA hU hreg hJ hAF hE hGT hgx hold
  obtain ⟨hag, -⟩ := hAF
  obtain ⟨hUc, hU0, hUη⟩ := hU
  set T := historyTime c r l with hT
  set Tc := contactX (rootPt r.1) c.s (uncTr c r l i) c.α ξ with hTc
  have hUtc : Continuous (uncTr c r l i ξ) := continuousOn_univ.1 (hUη.2.1.mono fun t _ =>
    show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  have hlifeA : ∀ a, candidateAngle c r a = angleEnumeration c r i → candLife c r l a ξ = uncLife c r l i ξ :=
    fun a ha => candLife_eq_of_angle c r l (by rw [ha, candidateAngle_angCand]) ξ
  -- data of a candidate of the angle at the sample
  have hdata : ∀ a, candidateAngle c r a = angleEnumeration c r i →
      Continuous (schedTr c r l a ξ) ∧ Continuous (c.α ξ) ∧
      StrictMonoOn (fun t => clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ)
        {t | (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ} := by
    intro a _
    have hξ : ξ ∈ schedGTX h13 c r l a := (hGT a).2 hgx
    obtain ⟨⟨hwc, hw0, hγ⟩, ⟨hα, hW, hW0, hζ⟩, harc, -, -⟩ := (schedGTX_spec h13 c r l a).1 ξ hξ
    refine ⟨continuousOn_univ.1 (hγ.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top),
      continuousOn_univ.1 (hα.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top), ?_⟩
    exact (GW2Rz.clock_props c.W c.ζ ξ hα hW hW0 hζ hg.2 hg.1 harc hwc hw0 hγ).2.1
  by_cases hD : uncLife c r l i ξ ≠ ⊤ ∧ ((T + (uncLife c r l i ξ).toNNReal : ℝ≥0) : ℝ≥0∞) < Tc
  · -- death first: a candidate past the death explores the uncapped curve everywhere
    obtain ⟨hfin, hTℓ⟩ := hD
    set ℓ := (uncLife c r l i ξ).toNNReal with hℓ
    set a := angCand i (capIdx c r ℓ) with ha
    have hang : candidateAngle c r a = angleEnumeration c r i := candidateAngle_angCand c r _ _
    have hℓc : ℓ ≤ candidateCap c r a := by rw [candidateCap_angCand]; exact le_capIdx c r ℓ
    have hW : ∀ u, schedW c r l a u ξ = uncW c r l i u ξ := by
      intro u
      by_cases hu : u ≤ T + candidateCap c r a
      · exact (hUA a hang u hu).1
      · have hu' : T + candidateCap c r a ≤ u := le_of_lt (not_le.1 hu)
        have hgood : ∀ a, ∀ (j : ℕ) (hj : j < (futureProgram c r l a).length), LocalExt.IsDrvGood
            (recHist (programRecords c (rootPt r.1) (futureProgram c r l a) ξ ⟨j, hj⟩)) := fun a => (hJ l a hold).1
        rw [GW2Nt.schedW_frozen c r l a hord hold hu', (hUA a hang _ le_rfl).1,
          uncW_frozen c r l i hord hold hgood hag hfin (add_le_add le_rfl hℓc),
          uncW_frozen c r l i hord hold hgood hag hfin ((add_le_add le_rfl hℓc).trans hu')]
    have hWf : (fun u => schedW c r l a u ξ) = fun u => uncW c r l i u ξ := funext hW
    have hTr : schedTr c r l a ξ = uncTr c r l i ξ := by
      funext t
      exact trace_eq_of_agree (hreg a).1 hUc (hreg a).2.1 hU0 (hreg a).2.2.1 hUη fun u _ => hW u
    have hc : contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ = Tc := by
      simp only [hTc, contactX, hTr]
    have hcl : ∀ t, clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ =
        clockX (rootPt r.1) c.s c.W c.ζ (uncW c r l i) t ξ := fun t => clockX_congr _ _ _ _ fun u _ => hW u
    have hdA : deathClockX c r l a ξ = uncDeathX c r l i ξ := by
      have hca : candLife c r l a ξ ≤ (candidateCap c r a : ℝ≥0∞) := by
        rw [hlifeA a hang, ← ENNReal.coe_toNNReal hfin]; exact ENNReal.coe_le_coe.2 hℓc
      unfold deathClockX uncDeathX
      rw [ite_eq_left ⟨hca, by rw [hlifeA a hang, hc]; exact hTℓ⟩, ite_eq_left ⟨hfin, hTℓ⟩, hlifeA a hang, hcl]
    obtain ⟨Wc, hWc, hWc0, hK, htr, hbd⟩ := hcan a hgx hold
    obtain ⟨-, -, hsm⟩ := hdata a hang
    refine ⟨Wc, isCanonUX_of_capped c r l i a hWc hWc0 hK htr hbd hc (fun t _ u _ => hW u) fun t ht hdt => ?_⟩
    rw [← hdA, ← hcl] at hdt
    refine ⟨?_, hdt⟩
    -- the clock reaches the death only at `T + ζ`
    have hdA' : deathClockX c r l a ξ =
        ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (T + ℓ) ξ) := by
      rw [hdA]; unfold uncDeathX; rw [ite_eq_left ⟨hfin, hTℓ⟩, ← hcl]
    rw [hdA'] at hdt
    have hlt : clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ <
        clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) (T + ℓ) ξ :=
      ((ENNReal.ofReal_lt_ofReal_iff').1 hdt).1
    have htℓ : t < T + ℓ := by
      by_contra hge
      rw [not_lt] at hge
      exact absurd (hsm.monotoneOn (by rw [hc]; exact hTℓ) (by rw [hc]; exact ht) hge) (not_le.2 hlt)
    exact htℓ.trans_le (add_le_add le_rfl hℓc)
  · by_cases hTop : Tc = ⊤
    · -- no death and no contact: the end statement
      have hℓ : uncLife c r l i ξ = ⊤ := by
        by_contra hfin
        exact hD ⟨hfin, by rw [hTop]; exact ENNReal.coe_lt_top⟩
      exact hE hgx hold hℓ hTop
    · -- the contact comes first: a candidate whose cap passes the contact
      set k := capIdx c r (Tc.toNNReal + 1) with hk
      set a := angCand i k with ha
      have hang : candidateAngle c r a = angleEnumeration c r i := candidateAngle_angCand c r _ _
      set τ := T + candidateCap c r a with hτ
      have hTcτ : Tc ≤ (τ : ℝ≥0∞) := by
        rw [← ENNReal.coe_toNNReal hTop]
        refine ENNReal.coe_le_coe.2 ?_
        rw [hτ, candidateCap_angCand]
        exact ((le_add_of_nonneg_right zero_le_one).trans (le_capIdx c r _)).trans le_add_self
      obtain ⟨hγa, hα, hsm⟩ := hdata a hang
      have hc : contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ = Tc :=
        contactX_eq_of_agree (rootPt r.1) c.s (γ := uncTr c r l i) (γ' := schedTr c r l a) hUtc hγa hα
          (fun u hu => ((hUA a hang u hu).2).symm) hTcτ
      have hle : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc → t ≤ τ := fun t ht =>
        ENNReal.coe_le_coe.1 (ht.le.trans hTcτ)
      have hdU : uncDeathX c r l i ξ = ⊤ := by unfold uncDeathX; rw [ite_eq_right hD]
      have hdA : deathClockX c r l a ξ = ⊤ := by
        unfold deathClockX
        rw [ite_eq_right]
        rintro ⟨hca, hcon⟩
        refine hD ⟨?_, ?_⟩
        · rw [← hlifeA a hang]; exact ne_top_of_le_ne_top ENNReal.coe_ne_top hca
        · rw [← hlifeA a hang, ← hc]; exact hcon
      obtain ⟨Wc, hWc, hWc0, hK, htr, hbd⟩ := hcan a hgx hold
      refine ⟨Wc, isCanonUX_of_capped c r l i a hWc hWc0 hK htr hbd hc
        (fun t ht u hu => (hUA a hang u (hu.trans (hle t ht))).1) fun t ht _ => ⟨?_, ?_⟩⟩
      · exact ENNReal.coe_lt_coe.1 (ht.trans_le hTcτ)
      · rw [hdA]; exact ENNReal.ofReal_lt_top

end Law

end InteractingSLE.Theorem14.GW2Ni
