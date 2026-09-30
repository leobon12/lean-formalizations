import QuantumZipper.Proofs.Thm18.RTMeas2Glue
import QuantumZipper.Proofs.Thm18.RT5ODefs
import QuantumZipper.Proofs.Thm18.G4Read2Core

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# RT-MEAS3, part 1: open-arc lengths of a field off `0` from a countable certificate

For the pieces (the field read off the curve, junk near `0`) the open-arc lengths of D86
(`openArcLen`, `lenWeldPointO`, `weldHomRO`) only see the local boundary limit on `ℝ ∖ {0}`.
`CertO γ x` is a countable (Borel) certificate: the window certificate on `ℝ ∖ {0}` (eventual
finiteness and `R2b.LCert` on rational windows avoiding `0`), finiteness of the read lengths of
`(-N,0)` and `(0,N)`, no atoms (read on dyadic intervals avoiding `0`), and infinite length of
`(0,∞)`. On it there is a locally finite atomless measure `ν` with `ν(ℍ ∖ ...) `, `ν [0,∞) = ∞`
and `openArcLen γ x a b = ν [a,b]` for arcs not straddling `0` (`CertO.spec`), so that the
open-arc welding point and welding map are the closed-arc ones of `ν` and are read at the
rationals (`xmO_eq`, `wRO_eq`), as in `Thm18Asm.xmR_eq` / `Thm14WDG.weldReadF_eq`.

Own elementary bookkeeping (the paper's lengths are "well defined by unzipping", p. 26).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace R18
namespace RTMeas

open Thm18Asm

/-! ## The window certificate on an open set of reals -/

/-- The window certificate on an open set `U ⊆ ℝ`. -/
def WinCertU (νs : ℕ → Measure ℝ) (U : Set ℝ) : Prop :=
  ∀ n : ℕ, Icc (wp n) (wq n) ⊆ U → wp n < wq n →
    (∃ K : ℕ, ∀ k, K ≤ k → νs k (Icc (wp n) (wq n)) < ⊤) ∧ LocLen.R2b.LCert νs (wp n) (wq n)

theorem exists_lim_of_winCertU {νs : ℕ → Measure ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hc : WinCertU νs U) : ∃ ν, IsVagueLimitOnR U νs ν := by
  classical
  set Good : ℕ → Prop := fun n => Icc (wp n) (wq n) ⊆ U ∧ wp n < wq n with hGood
  have hK : ∀ n, Good n → ∃ K : ℕ, ∀ k, K ≤ k → νs k (Icc (wp n) (wq n)) < ⊤ :=
    fun n hn => (hc n hn.1 hn.2).1
  set Kf : ℕ → ℕ := fun n => if h : Good n then Classical.choose (hK n h) else 0 with hKf
  have hKf_spec : ∀ n, Good n → ∀ k, Kf n ≤ k → νs k (Icc (wp n) (wq n)) < ⊤ := by
    intro n hn k hk
    exact Classical.choose_spec (hK n hn) k (by simpa [hKf, hn] using hk)
  set A : ℕ → Set ℝ := fun k => ⋃ n ∈ {n : ℕ | n ≤ k ∧ Good n ∧ Kf n ≤ k}, Icc (wp n) (wq n)
    with hA
  set νs' : ℕ → Measure ℝ := fun k => (νs k).restrict (A k) with hνs'
  have hfinA : ∀ k, νs k (A k) < ⊤ := fun k =>
    measure_biUnion_lt_top ((finite_le_nat k).subset fun n hn => hn.1)
      fun n hn => hKf_spec n hn.2.1 k hn.2.2
  have hfin' : ∀ k, IsFiniteMeasureOnCompacts (νs' k) := fun k => by
    have : IsFiniteMeasure (νs' k) := ⟨by
      rw [hνs', Measure.restrict_apply_univ]; exact hfinA k⟩
    infer_instance
  have hev : ∀ C : Set ℝ, IsCompact C → C ⊆ U → ∀ᶠ k in atTop, C ⊆ A k := by
    intro C hC hCU
    obtain ⟨s, hs⟩ := hC.elim_finite_subcover (E1.winW U) (E1.isOpen_winW _)
      (by rw [E1.iUnion_winW hU]; exact hCU)
    filter_upwards [eventually_ge_atTop (s.sup fun n => max n (Kf n))] with k hk
    intro x hx
    obtain ⟨n, hn, hxn⟩ := mem_iUnion₂.1 (hs hx)
    unfold E1.winW at hxn
    split_ifs at hxn with hsub
    · have hpq : wp n < wq n := hxn.1.trans hxn.2
      have hG : Good n := ⟨hsub, hpq⟩
      have hle : max n (Kf n) ≤ k := (Finset.le_sup (f := fun n => max n (Kf n)) hn).trans hk
      exact mem_biUnion (x := n) ⟨(le_max_left _ _).trans hle, hG, (le_max_right _ _).trans hle⟩
        (Ioo_subset_Icc_self hxn)
    · exact absurd hxn (notMem_empty x)
  have hint : ∀ f : ℝ → ℝ, HasCompactSupport f → tsupport f ⊆ U →
      (fun k => ∫ t, f t ∂νs' k) =ᶠ[atTop] fun k => ∫ t, f t ∂νs k := by
    intro f hfc hfU
    filter_upwards [hev _ hfc hfU] with k hk
    exact setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht =>
      image_eq_zero_of_notMem_tsupport fun h => ht (hk h)
  have hc' : ∀ n : ℕ, Icc (wp n) (wq n) ⊆ U → wp n < wq n →
      LocLen.R2b.LCert νs' (wp n) (wq n) := by
    intro n hsub h3
    obtain ⟨-, hL1, hL2⟩ := hc n hsub h3
    have hsub' : Ioo (wp n) (wq n) ⊆ U := Ioo_subset_Icc_self.trans hsub
    refine ⟨fun N m => ?_, fun N => ?_⟩
    · obtain ⟨l, hl⟩ := hL1 N m
      refine ⟨l, (tendsto_congr' (hint _ (LocLen.R2b.hasCompactSupport_glue h3
        (BdryVague.hasCompactSupport_testFam N m)) ((LocLen.R2b.tsupport_glue_Ioo h3
        (BdryVague.hasCompactSupport_testFam N m)).trans hsub'))).2 hl⟩
    · obtain ⟨l, hl⟩ := hL2 N
      refine ⟨l, (tendsto_congr' (hint _ (LocLen.R2b.hasCompactSupport_glue h3
        (BdryVague.hasCompactSupport_bump N)) ((LocLen.R2b.tsupport_glue_Ioo h3
        (BdryVague.hasCompactSupport_bump N)).trans hsub'))).2 hl⟩
  obtain ⟨ν, hν⟩ := E1.exists_isVagueLimitOnR_of_winW hU hfin' fun n =>
    E1.exists_isVagueLimitOnR_winW n fun hsub => by
      by_cases hpq : wp n < wq n
      · exact LocLen.R2b.exists_lim_of_lCert hpq hfin' (hc' n hsub hpq)
      · exact LocLen.R2b.lim_Ioo_of_le (not_lt.1 hpq)
  exact ⟨ν, hν.1, hν.2.1, fun f hf hfc hfU =>
    (tendsto_congr' (hint f hfc hfU)).1 (hν.2.2 f hf hfc hfU)⟩

/-! ## The certificate off `0` -/

/-- `ℝ ∖ {0}`. -/
def U0 : Set ℝ := {t | t ≠ 0}

theorem isOpen_U0 : IsOpen U0 := isOpen_ne

/-- Dyadic interval ends avoiding `0`. -/
def dl (k j : ℕ) : ℝ := max 0 (((j : ℝ) - 1) / 2 ^ k)
def dr (k j : ℕ) : ℝ := ((j : ℝ) + 1) / 2 ^ k

/-- **The countable certificate of the open-arc lengths.** -/
def CertO (γ : ℝ) (x : FieldSample) : Prop :=
  WinCertU (bdryApprox γ x) U0 ∧
  (∀ N : ℕ, LocLen.arcRd γ x (-(N : ℝ)) 0 < ⊤ ∧ LocLen.arcRd γ x 0 N < ⊤) ∧
  (∀ n m : ℕ, ∃ k : ℕ, ∀ j : ℕ, j ≤ m * 2 ^ k →
    LocLen.arcRd γ x (dl k j) (dr k j) ≤ ((n : ℝ≥0∞) + 1)⁻¹ ∧
    LocLen.arcRd γ x (-dr k j) (-dl k j) ≤ ((n : ℝ≥0∞) + 1)⁻¹) ∧
  ∀ N : ℕ, ∃ r : ℕ, (N : ℝ≥0∞) ≤ LocLen.arcRd γ x 0 r

theorem measurableSet_certO (γ : ℝ) : MeasurableSet {x : FieldSample | CertO γ x} := by
  have hA : ∀ a b : ℝ, Measurable fun x : FieldSample => LocLen.arcRd γ x a b := fun a b =>
    LocLen.measurable_arcRd_comp γ measurable_id measurable_const measurable_const
  have hW : Measurable fun x : FieldSample => WinCertU (bdryApprox γ x) U0 := by
    refine Measurable.forall fun n => measurable_const.imp (measurable_const.imp ?_)
    refine Measurable.and (Measurable.exists fun K => Measurable.forall fun k =>
      measurable_const.imp (measurableSet_setOfPred.1 (measurableSet_lt
        ((Measure.measurable_coe measurableSet_Icc).comp (measurable_bdryApprox γ k))
        measurable_const))) ?_
    exact measurableSet_setOfPred.1 (LocLen.R2b.measurableSet_lCert γ _ _)
  refine measurableSet_setOfPred.2 (hW.and ((Measurable.forall fun N =>
    (measurableSet_setOfPred.1 (measurableSet_lt (hA _ _) measurable_const)).and
      (measurableSet_setOfPred.1 (measurableSet_lt (hA _ _) measurable_const))).and
    ((Measurable.forall fun n => Measurable.forall fun m => Measurable.exists fun k =>
      Measurable.forall fun j => measurable_const.imp
        ((measurableSet_setOfPred.1 (measurableSet_le (hA _ _) measurable_const)).and
          (measurableSet_setOfPred.1 (measurableSet_le (hA _ _) measurable_const)))).and
      (Measurable.forall fun N => Measurable.exists fun r =>
        measurableSet_setOfPred.1 (measurableSet_le measurable_const (hA _ _))))))

/-- The measure of the certified open-arc lengths. -/
structure OSpec (γ : ℝ) (x : FieldSample) (ν : Measure ℝ) : Prop where
  lf : IsLocallyFiniteMeasure ν
  atom : ∀ s : ℝ, ν {s} = 0
  inf : ν (Ici 0) = ⊤
  len : ∀ a b : ℝ, (b ≤ 0 ∨ 0 ≤ a) → openArcLen γ x a b = ν (Icc a b)
  rd : ∀ a b : ℝ, (b ≤ 0 ∨ 0 ≤ a) → LocLen.arcRd γ x a b = ν (Icc a b)

theorem CertO.spec {γ : ℝ} {x : FieldSample} (h : CertO γ x) : ∃ ν, OSpec γ x ν := by
  obtain ⟨hW, hfin, hat, hinf⟩ := h
  obtain ⟨ν, hν⟩ := exists_lim_of_winCertU isOpen_U0 hW
  have hsub : ∀ a b : ℝ, (b ≤ 0 ∨ 0 ≤ a) → Ioo a b ⊆ U0 := by
    rintro a b (hb | ha) t ht
    · exact (ht.2.trans_le hb).ne
    · exact (ha.trans_lt ht.1).ne'
  have hIoo : ∀ a b : ℝ, (b ≤ 0 ∨ 0 ≤ a) → LocLen.arcRd γ x a b = ν (Ioo a b) := fun a b hab =>
    (LocLen.arcRd_eq_arcLen isOpen_U0 hν (hsub a b hab)).trans
      (LocLen.arcLen_eq_of_isVagueLimitOnR hν (hsub a b hab))
  have h0 : ν {0} = 0 := by
    have : ({0} : Set ℝ) = U0ᶜ := by ext t; simp [U0]
    rw [this]; exact hν.1
  -- no atoms
  have hatom : ∀ s : ℝ, ν {s} = 0 := by
    intro s
    rcases eq_or_ne s 0 with rfl | hs
    · exact h0
    refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_) bot_le
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt (ENNReal.coe_ne_zero.2 hε.ne')
    obtain ⟨m, hm⟩ := exists_nat_ge |s|
    obtain ⟨k, hk⟩ := hat n m
    set j : ℕ := ⌊|s| * 2 ^ k⌋₊ with hj
    have hp : (0 : ℝ) < 2 ^ k := by positivity
    have hj1 : (j : ℝ) ≤ |s| * 2 ^ k := Nat.floor_le (by positivity)
    have hj2 : |s| * 2 ^ k < (j : ℝ) + 1 := Nat.lt_floor_add_one _
    have hjm : j ≤ m * 2 ^ k := by
      have : (j : ℝ) ≤ (m : ℝ) * 2 ^ k := hj1.trans (mul_le_mul_of_nonneg_right hm hp.le)
      exact_mod_cast this
    have hmem : |s| ∈ Ioo (dl k j) (dr k j) := by
      constructor
      · unfold dl
        refine max_lt (abs_pos.2 hs) ?_
        rw [div_lt_iff₀ hp]; linarith
      · unfold dr; rw [lt_div_iff₀ hp]; linarith
    have hle : ν {s} ≤ ((n : ℝ≥0∞) + 1)⁻¹ := by
      rcases lt_or_gt_of_ne hs with hneg | hpos
      · have hs' : s ∈ Ioo (-dr k j) (-dl k j) := by
          rw [abs_of_neg hneg] at hmem
          exact ⟨by linarith [hmem.2], by linarith [hmem.1]⟩
        have hdl : -dl k j ≤ 0 := by unfold dl; linarith [le_max_left 0 (((j : ℝ) - 1) / 2 ^ k)]
        calc ν {s} ≤ ν (Ioo (-dr k j) (-dl k j)) := measure_mono (singleton_subset_iff.2 hs')
          _ = LocLen.arcRd γ x (-dr k j) (-dl k j) := (hIoo _ _ (Or.inl hdl)).symm
          _ ≤ _ := (hk j hjm).2
      · have hs' : s ∈ Ioo (dl k j) (dr k j) := by rwa [abs_of_pos hpos] at hmem
        have hdl : 0 ≤ dl k j := le_max_left _ _
        calc ν {s} ≤ ν (Ioo (dl k j) (dr k j)) := measure_mono (singleton_subset_iff.2 hs')
          _ = LocLen.arcRd γ x (dl k j) (dr k j) := (hIoo _ _ (Or.inr hdl)).symm
          _ ≤ _ := (hk j hjm).1
    calc ν {s} ≤ ((n : ℝ≥0∞) + 1)⁻¹ := hle
      _ ≤ (n : ℝ≥0∞)⁻¹ := ENNReal.inv_le_inv.2 le_self_add
      _ ≤ 0 + ε := by rw [zero_add]; exact hn.le
  have hIcc : ∀ a b : ℝ, ν (Icc a b) = ν (Ioo a b) := by
    intro a b
    refine le_antisymm ?_ (measure_mono Ioo_subset_Icc_self)
    calc ν (Icc a b) ≤ ν (Ioo a b ∪ ({a} ∪ {b})) := measure_mono fun t ht => by
          rcases eq_or_ne t a with rfl | ha
          · exact Or.inr (Or.inl rfl)
          rcases eq_or_ne t b with rfl | hb
          · exact Or.inr (Or.inr rfl)
          exact Or.inl ⟨lt_of_le_of_ne ht.1 ha.symm, lt_of_le_of_ne ht.2 hb⟩
      _ ≤ ν (Ioo a b) + (ν {a} + ν {b}) := (measure_union_le _ _).trans
          (add_le_add le_rfl (measure_union_le _ _))
      _ = ν (Ioo a b) := by rw [hatom, hatom, add_zero, add_zero]
  have hrd : ∀ a b : ℝ, (b ≤ 0 ∨ 0 ≤ a) → LocLen.arcRd γ x a b = ν (Icc a b) := fun a b hab => by
    rw [hIcc]; exact hIoo a b hab
  have hlen : ∀ a b : ℝ, (b ≤ 0 ∨ 0 ≤ a) → openArcLen γ x a b = ν (Icc a b) := fun a b hab => by
    rw [hIcc]; exact LocLen.arcLen_eq_of_isVagueLimitOnR hν (hsub a b hab)
  refine ⟨ν, ⟨⟨fun t => ?_⟩, hatom, ?_, hlen, hrd⟩⟩
  · obtain ⟨N, hN⟩ := exists_nat_gt |t|
    refine ⟨Ioo (-(N : ℝ)) N, Ioo_mem_nhds (by linarith [neg_abs_le t]) (by linarith [le_abs_self t]),
      ?_⟩
    calc ν (Ioo (-(N : ℝ)) N) ≤ ν (Icc (-(N : ℝ)) 0 ∪ Icc 0 N) := measure_mono fun u hu => by
          rcases le_total u 0 with h | h
          · exact Or.inl ⟨hu.1.le, h⟩
          · exact Or.inr ⟨h, hu.2.le⟩
      _ ≤ ν (Icc (-(N : ℝ)) 0) + ν (Icc 0 N) := measure_union_le _ _
      _ < ⊤ := by
          rw [← hrd _ _ (Or.inl le_rfl), ← hrd _ _ (Or.inr le_rfl)]
          exact ENNReal.add_lt_top.2 ⟨(hfin N).1, (hfin N).2⟩
  · refine eq_top_iff.2 (le_of_forall_lt fun c hc => ?_)
    obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt hc.ne
    obtain ⟨r, hr⟩ := hinf N
    calc c < N := hN
      _ ≤ LocLen.arcRd γ x 0 r := hr
      _ = ν (Icc 0 r) := hrd _ _ (Or.inr le_rfl)
      _ ≤ ν (Ici 0) := measure_mono Icc_subset_Ici_self

/-! ## Reading the welding point and the welding map at the rationals -/

/-- The left welding point, read at the rationals. -/
def xmO (γ ℓ : ℝ) (x : FieldSample) : ℝ :=
  sSup (((↑) : ℚ → ℝ) '' {q : ℚ | (q : ℝ) ≤ 0 ∧ ENNReal.ofReal ℓ ≤ LocLen.arcRd γ x q 0})

theorem measurable_xmO (γ ℓ : ℝ) : Measurable (xmO γ ℓ) :=
  Thm14WeldingData.measurable_sSup_rat _
    (fun q => measurableSet_setOfPred.2 (measurable_const.and (measurableSet_setOfPred.1
      (measurableSet_le measurable_const
        (LocLen.measurable_arcRd_comp γ measurable_id measurable_const measurable_const)))))
    (fun _ => ⟨0, by rintro _ ⟨q, hq, rfl⟩; exact hq.1⟩)

theorem xmO_eq {γ ℓ : ℝ} {x : FieldSample} {ν : Measure ℝ} (hν : OSpec γ x ν) :
    xmO γ ℓ x = lenWeldPointO γ x ℓ := by
  unfold xmO lenWeldPointO
  have e1 : ∀ q : ℚ, (q : ℝ) ≤ 0 → LocLen.arcRd γ x q 0 = ν (Icc (q : ℝ) 0) :=
    fun q _ => hν.rd _ _ (Or.inl le_rfl)
  have e2 : {s : ℝ | s ≤ 0 ∧ ENNReal.ofReal ℓ ≤ openArcLen γ x s 0} =
      {s : ℝ | s ≤ 0 ∧ ENNReal.ofReal ℓ ≤ ν (Icc s 0)} := by
    ext s; simp only [mem_setOf_eq]
    exact and_congr_right fun _ => by rw [hν.len _ _ (Or.inl le_rfl)]
  have e3 : {q : ℚ | (q : ℝ) ≤ 0 ∧ ENNReal.ofReal ℓ ≤ LocLen.arcRd γ x q 0} =
      {q : ℚ | (q : ℝ) ≤ 0 ∧ ENNReal.ofReal ℓ ≤ ν (Icc (q : ℝ) 0)} := by
    ext q; simp only [mem_setOf_eq]
    exact and_congr_right fun h => by rw [e1 q h]
  rw [e2, e3]
  have hdown : ∀ s ∈ {s : ℝ | s ≤ 0 ∧ ENNReal.ofReal ℓ ≤ ν (Icc s 0)}, ∀ s' ≤ s,
      s' ∈ {s : ℝ | s ≤ 0 ∧ ENNReal.ofReal ℓ ≤ ν (Icc s 0)} := fun s hs s' h =>
    ⟨h.trans hs.1, hs.2.trans (measure_mono (Icc_subset_Icc_left h))⟩
  have hsub : ((↑) : ℚ → ℝ) '' {q : ℚ | (q : ℝ) ≤ 0 ∧ ENNReal.ofReal ℓ ≤ ν (Icc (q : ℝ) 0)} ⊆
      {s : ℝ | s ≤ 0 ∧ ENNReal.ofReal ℓ ≤ ν (Icc s 0)} := by
    rintro _ ⟨q, hq, rfl⟩
    exact hq
  rcases ({s : ℝ | s ≤ 0 ∧ ENNReal.ofReal ℓ ≤ ν (Icc s 0)}).eq_empty_or_nonempty with he | hne
  · have h2 := subset_empty_iff.1 (he ▸ hsub)
    rw [he, h2]
  · have hbdd : BddAbove {s : ℝ | s ≤ 0 ∧ ENNReal.ofReal ℓ ≤ ν (Icc s 0)} :=
      ⟨0, fun s hs => hs.1⟩
    obtain ⟨s0, hs0⟩ := hne
    obtain ⟨q0, hq0⟩ := exists_rat_lt s0
    have hne' : (((↑) : ℚ → ℝ) ''
        {q : ℚ | (q : ℝ) ≤ 0 ∧ ENNReal.ofReal ℓ ≤ ν (Icc (q : ℝ) 0)}).Nonempty :=
      ⟨q0, q0, hdown s0 hs0 q0 hq0.le, rfl⟩
    refine le_antisymm (csSup_le_csSup hbdd hne' hsub) ?_
    refine csSup_le ⟨s0, hs0⟩ fun s hs => le_of_forall_lt fun b hb => ?_
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hb
    exact lt_of_lt_of_le hq1 (le_csSup (hbdd.mono hsub) ⟨q, hdown s hs q hq2.le, rfl⟩)

/-- The welding map at a rational point, read from the arc readings. -/
def wRO (γ : ℝ) (q : ℚ) (x : FieldSample) : ℝ :=
  Thm14WDG.wRq (LocLen.arcRd γ x q 0) (fun r => LocLen.arcRd γ x 0 r)

theorem measurable_wRO (γ : ℝ) (q : ℚ) : Measurable (wRO γ q) := by
  unfold wRO Thm14WDG.wRq
  refine ENNReal.measurable_toReal.comp (Measurable.iInf fun r => ?_)
  refine Measurable.ite ?_ measurable_const measurable_const
  exact measurableSet_setOfPred.2 (measurable_const.and (measurableSet_setOfPred.1
    (measurableSet_le (LocLen.measurable_arcRd_comp γ measurable_id measurable_const
      measurable_const) (LocLen.measurable_arcRd_comp γ measurable_id measurable_const
      measurable_const))))

theorem weldHomRO_eq_wRm {γ : ℝ} {x : FieldSample} {ν : Measure ℝ} (hν : OSpec γ x ν) {s : ℝ}
    (hs : s ≤ 0) : weldHomRO γ x s = Thm14WDG.wRm ν s := by
  unfold weldHomRO Thm14WDG.wRm
  congr 1
  ext r
  simp only [mem_setOf_eq]
  exact and_congr_right fun hr => by
    rw [hν.len _ _ (Or.inl le_rfl), hν.len _ _ (Or.inr le_rfl)]

theorem wRO_eq {γ : ℝ} {x : FieldSample} {ν : Measure ℝ} (hν : OSpec γ x ν) {q : ℚ}
    (hq : (q : ℝ) ≤ 0) : wRO γ q x = Thm14WDG.wRm ν q := by
  rw [Thm14WDG.wRm_eq_wRq]
  unfold wRO
  have e1 : LocLen.arcRd γ x q 0 = ν (Icc (q : ℝ) 0) := hν.rd _ _ (Or.inl le_rfl)
  have e2 : (fun r : ℚ => LocLen.arcRd γ x 0 r) = fun r : ℚ => ν (Icc 0 (r : ℝ)) := by
    funext r
    rcases le_total 0 (r : ℝ) with h | h
    · exact hν.rd _ _ (Or.inr le_rfl)
    · exact hν.rd _ _ (Or.inl h)
  rw [e1, e2]

end RTMeas
end R18
end QuantumZipper
