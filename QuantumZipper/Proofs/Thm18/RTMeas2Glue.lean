import QuantumZipper.Proofs.Thm18.RTMeasScale

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# RT-MEAS2, part 1: a countable certificate for local boundary limits on an open arc,
without global finiteness

`LocLen.R2b.exists_lim_of_windows` builds the local vague limit on `(a,b)` from the countable
certificate `R2b.LCert` on the rational windows, but needs the approximations to be finite on all
compacts of `ℝ`. For the unzipped *pieces* the approximations are only known to be finite on each
window from some index on (their circles near the ends of the arc may meet the curve). Here the
certificate is: on every rational window `[p,q] ⊆ (a,b)`, eventual finiteness and `LCert`
(`WinCert`). The proof restricts the `k`-th approximation to the finite union `A k` of the windows
already certified at stage `k` (finite measures), applies `R2b.exists_lim_of_windows` to these, and
transfers back (compact supports are eventually inside `A k`).

`bdryGate γ p t`: the certificate for the coordinate field of the unzipped pieces on
`(O⁻_t, 0)`; Borel in `(p, t)`.

Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace R18
namespace RTMeas

open Thm18Asm Thm18Asm.G4Core

/-- The `n`-th rational window. -/
abbrev wp (n : ℕ) : ℝ := ((E1.winPQ n).1 : ℝ)
abbrev wq (n : ℕ) : ℝ := ((E1.winPQ n).2 : ℝ)

/-- The window certificate on `(a,b)`. -/
def WinCert (νs : ℕ → Measure ℝ) (a b : ℝ) : Prop :=
  ∀ n : ℕ, a < wp n → wq n < b → wp n < wq n →
    (∃ K : ℕ, ∀ k, K ≤ k → νs k (Icc (wp n) (wq n)) < ⊤) ∧ LocLen.R2b.LCert νs (wp n) (wq n)

theorem winCert_of_lim {νs : ℕ → Measure ℝ} {a b : ℝ} {ν : Measure ℝ}
    (hν : IsVagueLimitOnR (Ioo a b) νs ν)
    (hfin : ∀ n : ℕ, a < wp n → wq n < b → wp n < wq n →
      ∃ K : ℕ, ∀ k, K ≤ k → νs k (Icc (wp n) (wq n)) < ⊤) : WinCert νs a b := by
  intro n h1 h2 h3
  exact ⟨hfin n h1 h2 h3, LocLen.R2b.lCert_of_lim h3 (ν := ν.restrict (Ioo (wp n) (wq n)))
    (E1.isVagueLimitOnR_restrict_open hν isOpen_Ioo (Ioo_subset_Ioo h1.le h2.le))⟩

theorem exists_lim_of_winCert {νs : ℕ → Measure ℝ} {a b : ℝ} (hc : WinCert νs a b) :
    ∃ ν, IsVagueLimitOnR (Ioo a b) νs ν := by
  classical
  set Good : ℕ → Prop := fun n => a < wp n ∧ wq n < b ∧ wp n < wq n with hGood
  have hK : ∀ n, Good n → ∃ K : ℕ, ∀ k, K ≤ k → νs k (Icc (wp n) (wq n)) < ⊤ :=
    fun n hn => (hc n hn.1 hn.2.1 hn.2.2).1
  set Kf : ℕ → ℕ := fun n => if h : Good n then Classical.choose (hK n h) else 0 with hKf
  have hKf_spec : ∀ n, Good n → ∀ k, Kf n ≤ k → νs k (Icc (wp n) (wq n)) < ⊤ := by
    intro n hn k hk
    have := Classical.choose_spec (hK n hn) k (by simpa [hKf, hn] using hk)
    exact this
  set A : ℕ → Set ℝ := fun k => ⋃ n ∈ {n : ℕ | n ≤ k ∧ Good n ∧ Kf n ≤ k}, Icc (wp n) (wq n)
    with hA
  have hAm : ∀ k, MeasurableSet (A k) := fun k =>
    MeasurableSet.biUnion (to_countable _) fun _ _ => measurableSet_Icc
  set νs' : ℕ → Measure ℝ := fun k => (νs k).restrict (A k) with hνs'
  have hfinA : ∀ k, νs k (A k) < ⊤ := fun k =>
    measure_biUnion_lt_top ((finite_le_nat k).subset fun n hn => hn.1)
      fun n hn => hKf_spec n hn.2.1 k hn.2.2
  have hfin' : ∀ k, IsFiniteMeasureOnCompacts (νs' k) := fun k => by
    have : IsFiniteMeasure (νs' k) := ⟨by
      rw [hνs', Measure.restrict_apply_univ]; exact hfinA k⟩
    infer_instance
  -- compacts of `(a,b)` are eventually inside `A k`
  have hev : ∀ C : Set ℝ, IsCompact C → C ⊆ Ioo a b → ∀ᶠ k in atTop, C ⊆ A k := by
    intro C hC hCU
    obtain ⟨s, hs⟩ := hC.elim_finite_subcover (E1.winW (Ioo a b)) (E1.isOpen_winW _ )
      (by rw [E1.iUnion_winW isOpen_Ioo]; exact hCU)
    filter_upwards [eventually_ge_atTop (s.sup fun n => max n (Kf n))] with k hk
    intro x hx
    obtain ⟨n, hn, hxn⟩ := mem_iUnion₂.1 (hs hx)
    unfold E1.winW at hxn
    split_ifs at hxn with hsub
    · have hpq : wp n < wq n := hxn.1.trans hxn.2
      have hG : Good n := ⟨(hsub ⟨le_rfl, hpq.le⟩).1, (hsub ⟨hpq.le, le_rfl⟩).2, hpq⟩
      have hle : max n (Kf n) ≤ k := (Finset.le_sup (f := fun n => max n (Kf n)) hn).trans hk
      exact mem_biUnion (x := n) ⟨(le_max_left _ _).trans hle, hG, (le_max_right _ _).trans hle⟩
        (Ioo_subset_Icc_self hxn)
    · exact absurd hxn (notMem_empty x)
  have hint : ∀ f : ℝ → ℝ, HasCompactSupport f → tsupport f ⊆ Ioo a b →
      (fun k => ∫ t, f t ∂νs' k) =ᶠ[atTop] fun k => ∫ t, f t ∂νs k := by
    intro f hfc hfU
    filter_upwards [hev _ hfc hfU] with k hk
    exact setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht =>
      image_eq_zero_of_notMem_tsupport fun h => ht (hk h)
  -- the certificate for the restricted approximations
  have hc' : ∀ n : ℕ, a < wp n → wq n < b → wp n < wq n → LocLen.R2b.LCert νs' (wp n) (wq n) := by
    intro n h1 h2 h3
    obtain ⟨-, hL1, hL2⟩ := hc n h1 h2 h3
    have hsub : Ioo (wp n) (wq n) ⊆ Ioo a b := Ioo_subset_Ioo h1.le h2.le
    refine ⟨fun N m => ?_, fun N => ?_⟩
    · obtain ⟨l, hl⟩ := hL1 N m
      refine ⟨l, (tendsto_congr' (hint _ (LocLen.R2b.hasCompactSupport_glue h3
        (BdryVague.hasCompactSupport_testFam N m)) ((LocLen.R2b.tsupport_glue_Ioo h3
        (BdryVague.hasCompactSupport_testFam N m)).trans hsub))).2 hl⟩
    · obtain ⟨l, hl⟩ := hL2 N
      refine ⟨l, (tendsto_congr' (hint _ (LocLen.R2b.hasCompactSupport_glue h3
        (BdryVague.hasCompactSupport_bump N)) ((LocLen.R2b.tsupport_glue_Ioo h3
        (BdryVague.hasCompactSupport_bump N)).trans hsub))).2 hl⟩
  obtain ⟨ν, hν⟩ := LocLen.R2b.exists_lim_of_windows hfin' hc'
  exact ⟨ν, hν.1, hν.2.1, fun f hf hfc hfU =>
    (tendsto_congr' (hint f hfc hfU)).1 (hν.2.2 f hf hfc hfU)⟩

/-! ## The gate of the unzipped pieces -/

/-- The window certificate of the coordinate field of the unzipped pieces on `(O⁻_t, 0)`. -/
def bdryGate (γ : ℝ) (x : PX × ℝ) : Prop :=
  WinCert (bdryApprox γ (zfld γ x.1 x.2)) (sideR (pcode x.1).2 x.2).1 0

theorem measurableSet_bdryGate (γ : ℝ) : MeasurableSet {x : PX × ℝ | bdryGate γ x} := by
  have hZ := measurable_zfld γ
  have hs : Measurable fun x : PX × ℝ => (sideR (pcode x.1).2 x.2).1 :=
    (measurable_sideR.comp ((measurable_snd.comp (measurable_pcode.comp measurable_fst)).prodMk
      measurable_snd)).fst
  have hB : ∀ k : ℕ, Measurable fun x : PX × ℝ => bdryApprox γ (zfld γ x.1 x.2) k :=
    fun k => (measurable_bdryApprox γ k).comp hZ
  refine measurableSet_setOfPred.2 (Measurable.forall fun n => ?_)
  refine (measurableSet_setOfPred.1 (measurableSet_lt hs measurable_const)).imp
    (measurable_const.imp (measurable_const.imp ?_))
  refine Measurable.and (Measurable.exists fun K => Measurable.forall fun k =>
    measurable_const.imp (measurableSet_setOfPred.1 (measurableSet_lt
      ((Measure.measurable_coe measurableSet_Icc).comp (hB k)) measurable_const))) ?_
  exact measurableSet_setOfPred.1 ((LocLen.R2b.measurableSet_lCert γ _ _).preimage hZ)

end RTMeas
end R18
end QuantumZipper
