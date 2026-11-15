/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2NhStmt
import InteractingSLE.Spec.Supplement.GW2NiUncLaw
import InteractingSLE.Spec.Supplement.GW2NxFam
import InteractingSLE.Spec.Supplement.GW2UaStmt

/-!
# The stopped uncapped stage law from RELDET's stopped capped law (D82)

Packet PROVE-GW2-NEARIMG2, decision D82 item 1. `StageLawUXSStatement` (the uncapped law read on the curve stopped
at its death, `GW2NhStmt`) follows from RELDET's stopped stage law `GW2Rd.StageLawXSStatement` on NOTHR's stop family
`GW2Nx.schedVerXStopFamily` (consumed as stated) and `UncEndStatement` (proved, `uncEndStatement_closed`).

* `ae_stopped_canon`: the stopped canonical driver of one candidate. It agrees with the stop family's versions below
  their caps, and the versions exhaust the clock below `schedStopLifeX` (NOTHR's `schedVerXStop_exhausts_stop`). So
  it generates the re-centred relative hulls there (`hull_of_version`).
* **`stageLawUXSStatement_of_stopped`**, by the cases of round 1's `stageLawUXStatement_of_capped`:
  * **death first**: a candidate whose cap passes the death explores the uncapped curve everywhere (both are frozen
    after the death). Its stop is the death, so its stopped life, stopped clock bound and death clock are the
    uncapped ones. The death clock is at most the stop life (`ae_deathClockX_le_stopLifeX`).
  * **contact first** (finite): a candidate whose cap passes the contact. Both stopped sets are everything before
    the contact. The stop life is `⊤`: the launch life is the infinite death clock (or `⊤` at zero lifetime), and the
    cap is past the contact.
  * **neither**: `UncEndStatement`.
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

section Law

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (h13 : Exist.Theorem13Statement.{u})
  (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q))

include h13 in
/-- **The stopped canonical driver of a candidate, with its hull identity below the stop life** (almost surely). -/
theorem ae_stopped_canon (hlaw : GW2Rd.StageLawXSStatement h13 (GW2Nx.schedVerXStopFamily h13))
    (hg : GW2Rv.GoodRoot c r) (hord : GW2Sdx.HistOrdered c r l) (a : ℕ) :
    ∀ᵐ ξ ∂c.P, cfRec c.s c.W c.ζ ξ ∈ goodX (rootPt r.1) c.s → oldSuccess c r l ξ →
      ∃ Wc : ℝ≥0 → ℝ, Continuous Wc ∧ Wc 0 = 0 ∧
        (∀ t : ℝ≥0, (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ →
          ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ) < GW2Nx.schedStopLifeX c r l a ξ →
          fwdHull (fun q : ℝ => Wc q.toNNReal) (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ) =
            hullX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ) ∧
        (∃ (ζc : ℝ≥0∞) (ηc : ℝ≥0 → ℂ), IsGeneratingTrace Wc ζc ηc ∧
          ENNReal.ofReal (GW2Rd.stopLifeX c r l a ξ) ≤ ζc) ∧
        ∃ M : ℝ, ∀ t : ℝ≥0, (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ →
          t ≤ historyTime c r l + GW2Psm.candStop c r l a ξ →
          clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ ≤ M := by
  have : Countable ℕ := inferInstance
  set ver := GW2Nx.schedVerXStopFamily h13 with hver
  have hV : ∀ᵐ ξ ∂c.P, ∀ n, cfRec c.s c.W c.ζ ξ ∈ goodX (rootPt r.1) c.s →
      ∀ t : ℝ≥0, (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ →
        ENNReal.ofReal (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ) ≤ (ver Ω c r l a).V n ξ →
        fwdHull (fun q : ℝ => (ver Ω c r l a).R n q.toNNReal ξ)
          (clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ) =
          hullX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ :=
    ae_all_iff.2 fun n => (((ver Ω c r l a).isA hg.1 n).1.1.2.2.2.2.2.2).mono fun ξ h hgx => (h hgx).2.2
  filter_upwards [hlaw Ω c r l a hg hord, (schedGTX_spec h13 c r l a).2.2, hV,
    GW2Nx.schedVerXStop_exhausts_stop h13 c r l a hg.1 hg.2 hord] with ξ hL hGT hVξ hE hgx hold
  have hξ : ξ ∈ schedGTX h13 c r l a := hGT.2 hgx
  obtain ⟨Wc, hWc, hWc0, hagree, htr, hbd⟩ := hL hξ hold
  obtain ⟨⟨hwc, hw0, hγ⟩, ⟨hα, hW, hW0, hζ⟩, harc, -, -⟩ := (schedGTX_spec h13 c r l a).1 ξ hξ
  obtain ⟨ha0, hsm, -⟩ := GW2Rz.clock_props c.W c.ζ ξ hα hW hW0 hζ hg.2 hg.1 harc hwc hw0 hγ
  refine ⟨Wc, hWc, hWc0, fun t ht hlt => ?_, htr, hbd⟩
  obtain ⟨n, hn⟩ := (hE hgx t ht hlt).exists
  have hnn : 0 ≤ clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ := by
    have h0 : ((0 : ℝ≥0) : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ :=
      lt_of_le_of_lt (ENNReal.coe_le_coe.2 zero_le) ht
    have h := hsm.monotoneOn h0 ht (zero_le : (0 : ℝ≥0) ≤ t)
    have h0' : clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) 0 ξ = 0 := ha0
    change clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) 0 ξ ≤ _ at h
    rwa [h0'] at h
  exact hull_of_version (R := fun q => (ver Ω c r l a).R n q ξ) (V := (ver Ω c r l a).V n ξ) hnn
    (hVξ n hgx t ht hn.le) hn (hagree n)

omit h13 in
/-- **The stopped uncapped stage law from RELDET's stopped capped law on the stop family** (D82 item 1). -/
theorem stageLawUXSStatement_of_stopped (h13 : Exist.Theorem13Statement.{u})
    (hlaw : GW2Rd.StageLawXSStatement h13 (GW2Nx.schedVerXStopFamily h13)) (hend : UncEndStatement.{u}) :
    StageLawUXSStatement.{u} := by
  intro Ω _ _ c r l i hg hord
  have : Countable ℕ := inferInstance
  filter_upwards [ae_all_iff.2 fun a => ae_stopped_canon h13 c r l hlaw hg hord a,
    uncAgreeStatement' h13 c r l i, ae_uncW_regular h13 c r l i,
    ae_all_iff.2 fun a => ae_schedW_regular h13 c r l a, Gm.ae_futureJoined_trace h13 c r,
    ae_angCand_facts h13 c r l i, hend Ω c r l i hg hord,
    ae_all_iff.2 fun a => (schedGTX_spec h13 c r l a).2.2,
    ae_all_iff.2 fun a => GW2Nx.ae_deathClockX_le_stopLifeX h13 c r l a hg.1 hg.2 hord,
    ae_all_iff.2 fun a => ae_schedLaunchLifeX_eq h13 c r l a hord,
    ae_all_iff.2 fun a => ae_schedLaunchLifeX_eq_top_of_zero h13 c r l a hord]
    with ξ hcan hUA hU hreg hJ hAF hE hGT hDle hLa hLz hgx hold
  obtain ⟨hag, -⟩ := hAF
  obtain ⟨hUc, hU0, hUη⟩ := hU
  set T := historyTime c r l with hT
  set Tc := contactX (rootPt r.1) c.s (uncTr c r l i) c.α ξ with hTc
  have hUtc : Continuous (uncTr c r l i ξ) := continuousOn_univ.1 (hUη.2.1.mono fun t _ =>
    show (t : ℝ≥0∞) ≤ ⊤ from le_top)
  have hlifeA : ∀ a, candidateAngle c r a = angleEnumeration c r i → candLife c r l a ξ = uncLife c r l i ξ :=
    fun a ha => candLife_eq_of_angle c r l (by rw [ha, candidateAngle_angCand]) ξ
  have hdata : ∀ a, candidateAngle c r a = angleEnumeration c r i →
      Continuous (schedTr c r l a ξ) ∧ Continuous (c.α ξ) := by
    intro a _
    have hξ : ξ ∈ schedGTX h13 c r l a := (hGT a).2 hgx
    obtain ⟨⟨-, -, hγ⟩, ⟨hα, -, -, -⟩, -, -, -⟩ := (schedGTX_spec h13 c r l a).1 ξ hξ
    exact ⟨continuousOn_univ.1 (hγ.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top),
      continuousOn_univ.1 (hα.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top)⟩
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
    have hdne : deathClockX c r l a ξ ≠ ⊤ := by
      rw [hdA]; unfold uncDeathX; rw [ite_eq_left ⟨hfin, hTℓ⟩]; exact ENNReal.ofReal_ne_top
    have hstop : GW2Psm.candStop c r l a ξ = ℓ := by
      unfold GW2Psm.candStop
      rw [hlifeA a hang, ← ENNReal.coe_toNNReal hfin, min_eq_right (ENNReal.coe_le_coe.2 hℓc),
        ENNReal.toNNReal_coe]
    have hset : uncStopSet c r l i ξ = {t : ℝ≥0 | (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ ∧
        t ≤ T + GW2Psm.candStop c r l a ξ} := by
      ext t
      simp only [uncStopSet, mem_ofPred_eq, hc, hstop]
      rw [← ENNReal.coe_toNNReal hfin, ← ENNReal.coe_add, ENNReal.coe_le_coe]
    obtain ⟨Wc, hWc, hWc0, hK, ⟨ζc, ηc, hη, hLζ⟩, M, hM⟩ := hcan a hgx hold
    refine ⟨Wc, hWc, hWc0, fun t ht hdt => ?_, ⟨ζc, ηc, hη, ?_⟩, M, fun t ht => ?_⟩
    · rw [← hcl t, ← hullX_congr _ _ _ _ (fun u _ => hW u)]
      refine hK t (by rw [hc]; exact ht) ?_
      rw [hcl t]
      have h := hDle a hgx hold hdne
      rw [hdA] at h
      exact hdt.trans_le h
    · have heq : uncStopLifeX c r l i ξ = GW2Rd.stopLifeX c r l a ξ := by
        rw [uncStopLifeX, GW2Rd.stopLifeX, hset]
        exact congrArg sSup (image_congr fun t _ => (hcl t).symm)
      rw [heq]
      exact hLζ
    · rw [hset] at ht
      rw [← hcl t]
      exact hM t ht.1 ht.2
  · by_cases hTop : Tc = ⊤
    · -- no death and no contact: the end statement
      have hℓ : uncLife c r l i ξ = ⊤ := by
        by_contra hfin
        exact hD ⟨hfin, by rw [hTop]; exact ENNReal.coe_lt_top⟩
      obtain ⟨Wc, hWc⟩ := hE hgx hold hℓ hTop
      exact ⟨Wc, hWc.isCanonUXS_of_top c r l i hℓ⟩
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
      obtain ⟨hγa, hα⟩ := hdata a hang
      have hc : contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ = Tc :=
        contactX_eq_of_agree (rootPt r.1) c.s (γ := uncTr c r l i) (γ' := schedTr c r l a) hUtc hγa hα
          (fun u hu => ((hUA a hang u hu).2).symm) hTcτ
      have hle : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc → t ≤ τ := fun t ht =>
        ENNReal.coe_le_coe.1 (ht.le.trans hTcτ)
      have hw : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc → ∀ u ≤ t, schedW c r l a u ξ = uncW c r l i u ξ :=
        fun t ht u hu => (hUA a hang u (hu.trans (hle t ht))).1
      have hcl : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc → clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ =
          clockX (rootPt r.1) c.s c.W c.ζ (uncW c r l i) t ξ := fun t ht => clockX_congr _ _ _ _ (hw t ht)
      have hdA : deathClockX c r l a ξ = ⊤ := by
        unfold deathClockX
        rw [ite_eq_right]
        rintro ⟨hca, hcon⟩
        refine hD ⟨?_, ?_⟩
        · rw [← hlifeA a hang]; exact ne_top_of_le_ne_top ENNReal.coe_ne_top hca
        · rw [← hlifeA a hang, ← hc]; exact hcon
      -- before the contact the uncapped curve has not died
      have hlife : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc → (t : ℝ≥0∞) ≤ (T : ℝ≥0∞) + uncLife c r l i ξ := by
        intro t ht
        by_cases hfin : uncLife c r l i ξ = ⊤
        · rw [hfin, add_top]; exact le_top
        · have h1 : Tc ≤ ((T + (uncLife c r l i ξ).toNNReal : ℝ≥0) : ℝ≥0∞) := not_lt.1 fun h => hD ⟨hfin, h⟩
          rw [ENNReal.coe_add, ENNReal.coe_toNNReal hfin] at h1
          exact ht.le.trans h1
      have hstopc : ∀ t : ℝ≥0, (t : ℝ≥0∞) < Tc → t ≤ T + GW2Psm.candStop c r l a ξ := by
        intro t ht
        have h1 : (t : ℝ≥0∞) ≤ (T : ℝ≥0∞) + (candidateCap c r a : ℝ≥0∞) := by
          rw [← ENNReal.coe_add]; exact ENNReal.coe_le_coe.2 (hle t ht)
        have h2 := hlife t ht
        have hmne : min (candidateCap c r a : ℝ≥0∞) (candLife c r l a ξ) ≠ ⊤ :=
          ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_left _ _)
        unfold GW2Psm.candStop
        rw [← ENNReal.coe_le_coe, ENNReal.coe_add, ENNReal.coe_toNNReal hmne, ← min_add_add_left,
          hlifeA a hang]
        exact le_min h1 h2
      have hset : uncStopSet c r l i ξ = {t : ℝ≥0 |
          (t : ℝ≥0∞) < contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ ∧ t ≤ T + GW2Psm.candStop c r l a ξ} := by
        ext t
        simp only [uncStopSet, mem_ofPred_eq, hc]
        exact ⟨fun h => ⟨h.1, hstopc t h.1⟩, fun h => ⟨h.1, hlife t h.1⟩⟩
      -- the stop life is infinite: the launch life is the infinite death clock, the cap is past the contact
      have hSL : GW2Nx.schedStopLifeX c r l a ξ = ⊤ := by
        rw [GW2Nx.schedStopLifeX_eq]
        have hlaunch : schedLaunchLifeX c r l a ξ = ⊤ := by
          rcases eq_zero_or_pos (candLife c r l a ξ) with h0 | h0
          · exact hLz a hold h0
          · rw [hLa a hold h0, hdA]
        have hcap : GW2Nx.capLife (historyTime c r l) (candidateCap c r a)
            (fun t => clockX (rootPt r.1) c.s c.W c.ζ (schedW c r l a) t ξ)
            (contactX (rootPt r.1) c.s (schedTr c r l a) c.α ξ) = ⊤ := by
          unfold GW2Nx.capLife
          rw [hc]
          exact ite_eq_right_iff.2 fun h => absurd h (not_lt.2 hTcτ)
        rw [hlaunch, hcap, min_self]
      obtain ⟨Wc, hWc, hWc0, hK, ⟨ζc, ηc, hη, hLζ⟩, M, hM⟩ := hcan a hgx hold
      refine ⟨Wc, hWc, hWc0, fun t ht _ => ?_, ⟨ζc, ηc, hη, ?_⟩, M, fun t ht => ?_⟩
      · rw [← hcl t ht, ← hullX_congr _ _ _ _ (hw t ht)]
        exact hK t (by rw [hc]; exact ht) (by rw [hSL]; exact ENNReal.ofReal_lt_top)
      · have heq : uncStopLifeX c r l i ξ = GW2Rd.stopLifeX c r l a ξ := by
          rw [uncStopLifeX, GW2Rd.stopLifeX, hset]
          exact congrArg sSup (image_congr fun t ht => (hcl t (by rw [← hc]; exact ht.1)).symm)
        rw [heq]
        exact hLζ
      · have ht' := ht
        rw [hset] at ht'
        rw [← hcl t ht.1]
        exact hM t ht'.1 ht'.2

end Law

end InteractingSLE.Theorem14.GW2Ni
