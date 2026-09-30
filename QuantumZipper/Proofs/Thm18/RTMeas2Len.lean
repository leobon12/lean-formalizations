import QuantumZipper.Proofs.Thm18.RTMeas2Wedge

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# RT-MEAS2, part 4: `PiecesLenRegStmt` holds

The good set of the pieces is carried by the dyadic driver code `k ∈ LCode` (a Polish space):
continuous drivers are recovered from their code (`phat_pcode`), and the gate and the length
reader at real times are Borel in `(code, time)`. "The gate holds at every time and the read
lengths are monotone" is a universal quantifier over the Polish parameter `(s,t) ∈ ℝ²` of a Borel
set, hence coanalytic and null-measurable for every finite law (`G4Core.nullMeasurableSet_forall`;
Kechris, *Classical Descriptive Set Theory*, Thm 21.10: analytic sets are universally measurable).
It holds a.s. along the wedge (`ae_wedge_pieces`), so it has full law, and a Borel subset of full
law is extracted with `toMeasurable`.

Own bookkeeping (measurability the paper leaves implicit).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace R18
namespace RTMeas

open Thm18Asm Thm18Asm.G4Core CoordsFull

/-- The data with the driver rebuilt from its dyadic code. -/
def phat (k : LCode) : PX := (k.1, fun r : ℝ≥0 => wg k.2 r)

theorem measurable_phat : Measurable phat :=
  measurable_fst.prodMk (measurable_pi_iff.2 fun r => (measurable_wg_apply (r : ℝ)).comp
    measurable_snd)

theorem phat_pcode {p : PX} (hc : Continuous p.2) (hg : GoodDrv (pcode p).2) :
    phat (pcode p) = p := by
  have h := wg_eq_drvOfData (d := dfull p) hc hg
  refine Prod.ext rfl (funext fun r => ?_)
  show wg (lcode (dfull p)).2 r = p.2 r
  rw [h]
  simp only [drvOfData, dfull]
  simp
  rfl

/-- The Borel relation: gate at `s` and monotone reading on `s ≤ t`. -/
def Rset (γ : ℝ) : Set (LCode × (ℝ × ℝ)) :=
  {x | (0 ≤ x.2.1 → bdryGate γ (phat x.1, x.2.1)) ∧
    (0 ≤ x.2.1 → x.2.1 ≤ x.2.2 → lenRdR γ (phat x.1, x.2.1) ≤ lenRdR γ (phat x.1, x.2.2))}

theorem measurableSet_Rset (γ : ℝ) : MeasurableSet (Rset γ) := by
  have h1 : Measurable fun x : LCode × (ℝ × ℝ) => (phat x.1, x.2.1) :=
    (measurable_phat.comp measurable_fst).prodMk measurable_snd.fst
  have h2 : Measurable fun x : LCode × (ℝ × ℝ) => (phat x.1, x.2.2) :=
    (measurable_phat.comp measurable_fst).prodMk measurable_snd.snd
  have hG : Measurable fun x : LCode × (ℝ × ℝ) => bdryGate γ (phat x.1, x.2.1) :=
    measurableSet_setOfPred.1 ((measurableSet_bdryGate γ).preimage h1)
  have hs : Measurable fun x : LCode × (ℝ × ℝ) => 0 ≤ x.2.1 :=
    measurableSet_setOfPred.1 (measurableSet_le measurable_const measurable_snd.fst)
  have hst : Measurable fun x : LCode × (ℝ × ℝ) => x.2.1 ≤ x.2.2 :=
    measurableSet_setOfPred.1 (measurableSet_le measurable_snd.fst measurable_snd.snd)
  have hL : Measurable fun x : LCode × (ℝ × ℝ) =>
      lenRdR γ (phat x.1, x.2.1) ≤ lenRdR γ (phat x.1, x.2.2) :=
    measurableSet_setOfPred.1 (measurableSet_le ((measurable_lenRdR γ).comp h1)
      ((measurable_lenRdR γ).comp h2))
  exact measurableSet_setOfPred.2 ((hs.imp hG).and (hs.imp (hst.imp hL)))

/-- **`PiecesLenRegStmt` holds** (from the proved RT2 core and the wedge length theory). -/
theorem piecesLenRegStmt_holds : PiecesLenRegStmt := by
  intro γ Ω _ P _ B Y hS hIn
  set g : Ω → PX := fun ω => πd (wd γ B Y ω) with hgdef
  have hg : AEMeasurable g P := measurable_πd.comp_aemeasurable (aemeasurable_offData_wedgeAConfig hS hIn)
  set μ : Measure PX := P.map g with hμ
  set S' : Set LCode := {k | ∀ θ : ℝ × ℝ, (k, θ) ∈ Rset γ} with hS'
  set S₀ : Set PX := {p | F1.PathGoodAll p.2 ∧ pcode p ∈ S'} with hS₀
  have hWP := ae_wedge_pieces hS hIn
  -- (a) the path certificate has full law
  have hpath : ∀ᵐ p ∂μ, F1.PathGoodAll p.2 := by
    have hBm := IsBrownianReal.aemeasurable_pathOf hS.2.2.1
    have h := F1.ae_pathGoodAll (κ := γ ^ 2) (by have := hS.1; positivity)
      (by nlinarith [hS.1, hS.2.1]) hS.2.2.1
    have e : μ.map Prod.snd = P.map fun ω => F1.drivePath (γ ^ 2) (pathOf B ω) := by
      rw [hμ, AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable hg]
      congr 1
      funext ω
      exact wd_snd γ B Y ω
    rw [← e] at h
    exact ae_of_ae_map measurable_snd.aemeasurable h
  -- (b) the coanalytic code condition has full law
  have hω : ∀ᵐ ω ∂P, pcode (g ω) ∈ S' := by
    filter_upwards [hWP] with ω ⟨hc, hp, hwin, hmono⟩
    intro θ
    have hph : phat (pcode (g ω)) = g ω := phat_pcode hc (goodDrv_of_pathGoodAll hp)
    show (0 ≤ θ.1 → bdryGate γ (phat (pcode (g ω)), θ.1)) ∧ _
    rw [hph]
    have hgate : ∀ s : ℝ, 0 ≤ s → bdryGate γ (g ω, s) := fun s hs =>
      (bdryGate_iff γ hc hp hs).2 (hwin s hs)
    refine ⟨hgate θ.1, fun hs hst => ?_⟩
    rw [lenRdR_eq γ hc hp hs (hgate _ hs), lenRdR_eq γ hc hp (hs.trans hst) (hgate _ (hs.trans hst))]
    exact hmono _ _ hs hst
  have hcode : ∀ᵐ p ∂μ, pcode p ∈ S' := by
    have hf : AEMeasurable (fun ω => pcode (g ω)) P := measurable_pcode.comp_aemeasurable hg
    have hmapeq : μ.map pcode = P.map fun ω => pcode (g ω) :=
      AEMeasurable.map_map_of_aemeasurable measurable_pcode.aemeasurable hg
    have hN : NullMeasurableSet S' (μ.map pcode) :=
      nullMeasurableSet_forall (measurableSet_Rset γ) _
    obtain ⟨T, hTS, hTm, hTeq⟩ := hN.exists_measurable_subset_ae_eq
    have hdiff : μ.map pcode (S' \ T) = 0 := (ae_eq_set.1 hTeq).2
    have hP0 : P ((fun ω => pcode (g ω)) ⁻¹' (S' \ T)) = 0 :=
      le_antisymm ((Measure.le_map_apply hf _).trans (by rw [← hmapeq, hdiff])) bot_le
    have hωT : ∀ᵐ ω ∂P, pcode (g ω) ∈ T := by
      filter_upwards [hω, measure_eq_zero_iff_ae_notMem.1 hP0] with ω h1 h2
      by_contra h
      exact h2 ⟨h1, h⟩
    have hT' : ∀ᵐ k ∂(μ.map pcode), k ∈ T := by
      rw [hmapeq]; exact (ae_map_iff hf hTm).2 hωT
    exact ae_of_ae_map measurable_pcode.aemeasurable (hT'.mono fun k hk => hTS hk)
  have hae : ∀ᵐ p ∂μ, p ∈ S₀ := hpath.and hcode
  -- the Borel set
  set G : Set PX := (toMeasurable μ S₀ᶜ)ᶜ with hG
  have hGm : MeasurableSet G := (measurableSet_toMeasurable _ _).compl
  have hGS : G ⊆ S₀ := fun p hp => by
    by_contra h
    exact hp (subset_toMeasurable _ _ h)
  have hG0 : μ Gᶜ = 0 := by
    rw [hG, compl_compl, measure_toMeasurable]
    exact ae_iff.1 hae
  refine ⟨G, hGm, fun d hd => ?_, (ae_map_iff hg hGm).1 (ae_iff.2 hG0)⟩
  obtain ⟨hp, hk⟩ := hGS hd
  refine ⟨hp, fun hc => ?_⟩
  have hph : phat (pcode (πd d)) = πd d := phat_pcode hc (goodDrv_of_pathGoodAll hp)
  have hR : ∀ θ : ℝ × ℝ, (0 ≤ θ.1 → bdryGate γ (πd d, θ.1)) ∧
      (0 ≤ θ.1 → θ.1 ≤ θ.2 → lenRdR γ (πd d, θ.1) ≤ lenRdR γ (πd d, θ.2)) := by
    intro θ
    have := hk θ
    simp only [Rset, mem_setOf_eq, hph] at this
    exact this
  refine ⟨fun q hq => ?_, fun s t hs hst => ?_⟩
  · have hq' : (0 : ℝ) ≤ q := by exact_mod_cast hq
    exact exists_lim_of_bdryGate γ hc hp hq' ((hR (q, q)).1 hq')
  · rw [← lenRdR_eq γ hc hp hs ((hR (s, t)).1 hs),
      ← lenRdR_eq γ hc hp (hs.trans hst) ((hR (t, t)).1 (hs.trans hst))]
    exact (hR (s, t)).2 hs hst

end RTMeas
end R18
end QuantumZipper
