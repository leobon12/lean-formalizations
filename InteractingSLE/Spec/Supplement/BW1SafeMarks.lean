/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BW1SafeMarksCore
import InteractingSLE.Spec.Supplement.BW1LifeMain
import InteractingSLE.Spec.Supplement.BW1InEnd

/-!
# BW1's retained set is marked local for BW1's record ((L1)(a) for BW1)

Packet PROVE-BW1-SAFELAW. BW1's retained set in the counterflow frame is the inverted TERMINAL hull of the first
piece, read from BW1's record `rec = recOf t e` (`e` the regularized first piece): `bRetOfRec TS rec` is
`−1/K_{min(t, ζ)}` on the record event `TS` and `ℍ` off it. With the marks `σ(rec) ∨ 𝒩`:

* **the record is determined** (`comap_bwRec_le_aeSigma`): on `{min(t, ζ) < N}` it is the record `rec_N` at the
  finite own time `min(t, N)` (deterministically), which is determined (`isHistoryAvoidanceLocal_recHull`); on
  `{min(t, ζ) = ∞}` (`t = ζ = ∞`) it reads the killed driver at the rational times;
* **the retained set is marked local** (`exists_bw1_retained_marks`): glue (`GB6LineL.isHistoryAvoidanceLocal_glue_det`)
  the pieces `P_N = {rec ∈ TS, min(t, ζ) < N}`, on which the retained set is the record hull of `rec_N`, marked local
  for `σ(rec_N) ∨ 𝒩` (the terminal record-hull lemma) and every mark `F ∩ P_N` is a mark of `rec_N`; off the pieces
  the record is almost surely outside `TS` (the threshold event has a finite stop), where the set is `ℍ`.

Theorems 1.2–1.3 enter through the field determination of the first piece (`Exist.Param12.hasFieldDeterminedHistories`;
allowed, R48: BW1 serves Theorem 1.4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull chiC)
open LQGMetric (TestOn DistOn)

universe u

namespace InteractingSLE.Theorem14.BW1Safe

open Exist Exist.Staged Exist.StagedLaw Supp8.GB6 LocalSets Restart BW1Ver BW1Life Theorem14.WalkLaw

open Classical in
/-- **BW1's retained set read from a record**: the inverted hull of the record driver at the record's own time on the
record event `TS`, `ℍ` off it. -/
def bRetOfRec (TS : Set RecData) (r : RecData) : Set ℂ :=
  if r ∈ TS then Supp8.Q3Rel.invHull (rdrv r) (recS r) else H

theorem measurable_bRetOfRec {TS : Set RecData} (hTS : MeasurableSet TS) :
    Measurable[inferInstance, hittingSigma] (bRetOfRec TS) := by
  classical
  let _ : MeasurableSpace (Set ℂ) := hittingSigma
  unfold bRetOfRec
  exact Measurable.ite hTS measurable_invHull_rec measurable_const

/-- **On `{min(t, ζ) < N}` the record at own time `t` is the record at own time `min(t, N)`.** -/
theorem recOf_eq_of_lt {t : ℝ≥0∞} {e : (ℝ≥0 → ℝ) × ℝ≥0∞} {N : ℕ} (hN : min t e.2 < N) :
    recOf t e = recOf (min t N) e := by
  have h1 : min (min t (N : ℝ≥0∞)) e.2 = min t e.2 := by
    rcases le_total t e.2 with hte | hte
    · rw [min_eq_left hte] at hN ⊢
      rw [min_eq_left hN.le, min_eq_left hte]
    · rw [min_eq_right hte] at hN ⊢
      exact min_eq_right (le_min hte hN.le)
  have h2 : decide (e.2 ≤ min t (N : ℝ≥0∞)) = decide (e.2 ≤ t) := by
    by_cases hte : e.2 ≤ t
    · have heN : e.2 ≤ (N : ℝ≥0∞) := by
        rw [min_eq_right hte] at hN
        exact hN.le
      simp only [hte, le_min hte heN, decide_true]
    · have hn : ¬ e.2 ≤ min t (N : ℝ≥0∞) := fun h => hte (h.trans (min_le_left _ _))
      simp only [hte, hn, decide_false]
  unfold recOf retOf
  rw [h1, h2]

/-- The life of the record at own time `min(t, N)` is below `N` exactly when `min(t, ζ)` is. -/
theorem recOf_life_lt_iff {t : ℝ≥0∞} {e : (ℝ≥0 → ℝ) × ℝ≥0∞} {N : ℕ} :
    (recOf (min t N) e).2.1 < N ↔ min t e.2 < N := by
  change min (min t (N : ℝ≥0∞)) e.2 < N ↔ min t e.2 < N
  constructor
  · intro h
    by_contra hc
    have hc' : (N : ℝ≥0∞) ≤ min t e.2 := not_lt.1 hc
    have hNt : (N : ℝ≥0∞) ≤ t := hc'.trans (min_le_left _ _)
    have hNe : (N : ℝ≥0∞) ≤ e.2 := hc'.trans (min_le_right _ _)
    rw [min_eq_right hNt, min_eq_left hNe] at h
    exact lt_irrefl _ h
  · intro h
    rw [min_right_comm]
    exact lt_of_le_of_lt (min_le_left _ _) h

/-- **BW1's record is field-determined and BW1's retained set is marked local for it.** In BW1's setting, with
Theorems 1.2–1.3 (field determination of the first piece), for the centred counterflow-frame field
`h₀ = R_*(h − 𝔥⁰)` and a record event `TS` of the threshold event: `σ(rec)` consists of field-determined events, and
`bRetOfRec TS ∘ rec` satisfies the history-marked avoidance criterion with the marks `σ(rec) ∨ 𝒩`. -/
theorem exists_bw1_retained_marks (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens} {W' : ℝ≥0 → Ω → ℝ}
    {ζ' : Ω → ℝ≥0∞} {θ : ℝ} {t : ℝ≥0∞} {gw2 : Bool} {rest : List Instr} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hset : IsBW1Setting κ b jumps P h W' ζ' θ t gw2 rest E) {c₀ : BoundaryWord}
    (hc₀ : ∀ y ∉ jumps, c₀.fn y = b y) {u₀ : ℂ → ℝ} (hu₀ : IsBoundedHarmonicExtension c₀.fn c₀.jumps u₀)
    {h₀ : Ω → DistOn upperHalfPlaneOpens} (hh₀ : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens h₀ P)
    (hcen : ∀ ω, h₀ ω = WangWu.reflectField (WholeField.centredField h u₀ ω)) {r : Bool} {TS : Set RecData}
    (hTS : MeasurableSet TS)
    (hFTS : ∀ᵐ ω ∂P, ω ∈ bwEvent κ b jumps (bwSpec gw2 θ t rest) E r ↔
      bwRec κ b jumps (bwSpec gw2 θ t rest) E ω ∈ TS) :
    MeasurableSpace.comap (bwRec κ b jumps (bwSpec gw2 θ t rest) E) inferInstance ≤
        aeSigma (MeasurableSpace.comap h₀ inferInstance) P ∧
      WholeField.IsHistoryAvoidanceLocal
        (MeasurableSpace.comap (bwRec κ b jumps (bwSpec gw2 θ t rest) E) inferInstance ⊔ Ito.nullSets P)
        (fun ω => bRetOfRec TS (bwRec κ b jumps (bwSpec gw2 θ t rest) E ω)) h₀ P := by
  classical
  obtain ⟨hκ, -, hb, hh, -, -, -, hS⟩ := hset
  set rec := bwRec κ b jumps (bwSpec gw2 θ t rest) E with hrecdef
  set e : Ω → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun ω => StagedReg.regularize t (E 0 ω) with hedef
  have hem : Measurable e := (StagedReg.measurable_regularize t).comp (hS.1 0)
  have hereg : ∀ ω, IsRegularDriver (e ω) := fun ω => StagedReg.isRegularDriver_regularize t _
  have hrece : ∀ ω, rec ω = recOf t (e ω) := fun ω => BW1In.bwRec_eq_recOf ω
  have hfl0 := hS.isFlowLineDriver_first hκ hb hh rfl rfl
  have eζ : (fun ω => (e ω).2) = fun ω => (E 0 ω).2 := funext fun ω => StagedReg.regularize_snd t _
  have hfl1 : IsFlowLineDriver κ b jumps θ P h (fun s ω => (e ω).1 s) (fun ω => (e ω).2) := by
    rw [eζ]
    refine StagedReg.isFlowLineDriver_congr_ae hfl0
      (fun s => (measurable_pi_apply s).comp (measurable_fst.comp hem)) ?_
    filter_upwards [ae_driver_zero_continuousOn hfl0] with ω hω
    exact ⟨StagedReg.regularize_zero t hω.1, fun s hs => StagedReg.regularize_eq_of_lt t hω.1 hω.2 hs⟩
  have hfl2 : IsFlowLineDriver κ c₀.fn c₀.jumps θ P h (fun s ω => (e ω).1 s) (fun ω => (e ω).2) :=
    (isFlowLineDriver_congr_of_eqOn hb c₀.isPiecewiseConstantBoundaryData jumps hc₀).2 hfl1
  have hdet : LP.HasFieldDeterminedHistories.{u} κ (flowLineXL c₀.fn c₀.jumps 0) (flowLineXR c₀.fn c₀.jumps 0)
      (flowLineRhoL κ c₀.fn c₀.jumps 0 θ) (flowLineRhoR κ c₀.fn c₀.jumps 0 θ) :=
    Exist.Param12.hasFieldDeterminedHistories h12 h13 hκ (Theorem15.isOrderedForceWord_flowLine c₀.fn c₀.jumps 0)
  -- the records at the finite own times `min(t, N)`
  set sN : ℕ → ℝ≥0 := fun N => (min t (N : ℝ≥0∞)).toNNReal with hsNdef
  have hsN : ∀ N : ℕ, ((sN N : ℝ≥0) : ℝ≥0∞) = min t N := fun N =>
    ENNReal.coe_toNNReal (ne_top_of_le_ne_top (ENNReal.natCast_ne_top N) (min_le_right _ _))
  have hcore := fun N : ℕ => isHistoryAvoidanceLocal_recHull hκ hem hereg hfl2 hdet hu₀ hh₀ hcen (sN N)
  set recN : ℕ → Ω → RecData := fun N ω => recOf ((sN N : ℝ≥0) : ℝ≥0∞) (e ω) with hrecNdef
  have hrecN : ∀ (N : ℕ) ω, min t (e ω).2 < N → rec ω = recN N ω := fun N ω hN => by
    rw [hrece, recOf_eq_of_lt hN, hrecNdef]
    simp only [hsN]
  have hlifeN : ∀ (N : ℕ) ω, (recN N ω).2.1 < N ↔ min t (e ω).2 < N := fun N ω => by
    simp only [hrecNdef, hsN]
    exact recOf_life_lt_iff
  have hlife : ∀ ω, (rec ω).2.1 = min t (e ω).2 := fun ω => by rw [hrece]; rfl
  have hkill := (hcore 0).1
  -- the record is determined
  have hlifeSet : ∀ N : ℕ, MeasurableSet {r : RecData | r.2.1 < (N : ℝ≥0∞)} := fun N =>
    measurableSet_lt (measurable_fst.comp measurable_snd) measurable_const
  have hinf : ∀ C : Set RecData, MeasurableSet C →
      MeasurableSet[aeSigma (MeasurableSpace.comap h₀ inferInstance) P] (rec ⁻¹' C ∩ {ω | min t (e ω).2 = ⊤}) := by
    intro C hC
    by_cases ht : t = ⊤
    · -- `t = ∞`: on `{ζ = ∞}` the record reads the killed driver at the rational times
      set Kp : Ω → (ℚ → ℝ) := fun ω q => if ((q : ℝ).toNNReal : ℝ≥0∞) < (e ω).2 then (e ω).1 (q : ℝ).toNNReal else 0
        with hKpdef
      have hKpm : Measurable[aeSigma (MeasurableSpace.comap h₀ inferInstance) P] Kp := by
        refine (@measurable_pi_iff Ω ℚ (fun _ => ℝ) (aeSigma (MeasurableSpace.comap h₀ inferInstance) P) _ _).2
          fun q A hA => ?_
        have e1 : (fun ω => Kp ω q) ⁻¹' A = {ω | (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < (e ω).2 ∧
            (e ω).1 (q : ℝ).toNNReal ∈ A} ∪ ({ω | (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < (e ω).2 ∧
              (e ω).1 (q : ℝ).toNNReal ∈ univ}ᶜ ∩ {_ω | (0 : ℝ) ∈ A}) := by
          ext ω
          simp only [hKpdef, mem_preimage, mem_union, mem_ofPred_eq, mem_inter_iff, mem_compl_iff, mem_univ,
            and_true]
          by_cases hq : (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < (e ω).2
          · simp [hq]
          · simp [hq]
        rw [e1]
        exact (hkill _ A hA).union ((hkill _ univ MeasurableSet.univ).compl.inter (MeasurableSet.const _))
      have hpm : Measurable fun k : ℚ → ℝ => ((k, (⊤ : ℝ≥0∞), true) : RecData) :=
        measurable_id.prodMk measurable_const
      have htop : {ω | min t (e ω).2 = ⊤} = ⋂ n : ℕ, {ω | ((n : ℝ≥0) : ℝ≥0∞) < (e ω).2 ∧ (e ω).1 n ∈ univ} := by
        ext ω
        simp only [ht, min_eq_right le_top, mem_ofPred_eq, mem_iInter, mem_univ, and_true]
        refine ⟨fun h n => by rw [h]; exact ENNReal.coe_lt_top, fun h => ?_⟩
        by_contra hne
        obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hne
        exact absurd (h n) (not_lt.2 (by exact_mod_cast hn.le))
      have hTm : MeasurableSet[aeSigma (MeasurableSpace.comap h₀ inferInstance) P] {ω | min t (e ω).2 = ⊤} := by
        rw [htop]
        exact MeasurableSet.iInter fun n => hkill _ univ MeasurableSet.univ
      have e2 : rec ⁻¹' C ∩ {ω | min t (e ω).2 = ⊤} =
          Kp ⁻¹' ((fun k : ℚ → ℝ => ((k, (⊤ : ℝ≥0∞), true) : RecData)) ⁻¹' C) ∩ {ω | min t (e ω).2 = ⊤} := by
        ext ω
        simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq]
        refine and_congr_left fun hω => ?_
        have hζ : (e ω).2 = ⊤ := by rw [ht] at hω; simpa using hω
        have hrec : rec ω = ((Kp ω, (⊤ : ℝ≥0∞), true) : RecData) := by
          rw [hrece, ht]
          unfold recOf retOf readRec
          simp only [hζ, min_self, min_top_right, ENNReal.toNNReal_coe, le_refl, decide_true, hKpdef,
            ENNReal.coe_lt_top, ↓reduceIte]
        rw [hrec]
      rw [e2]
      exact (hKpm (hpm hC)).inter hTm
    · have e0 : {ω | min t (e ω).2 = ⊤} = ∅ := by
        ext ω
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
        exact fun h => ht (min_eq_top.1 h).1
      rw [e0, inter_empty]
      exact @MeasurableSet.empty _ (aeSigma (MeasurableSpace.comap h₀ inferInstance) P)
  have hrecd : MeasurableSpace.comap rec inferInstance ≤ aeSigma (MeasurableSpace.comap h₀ inferInstance) P := by
    rintro _ ⟨C, hC, rfl⟩
    have hsplit : rec ⁻¹' C = (rec ⁻¹' C ∩ {ω | min t (e ω).2 = ⊤}) ∪
        ⋃ N : ℕ, recN N ⁻¹' (C ∩ {r : RecData | r.2.1 < (N : ℝ≥0∞)}) := by
      ext ω
      simp only [mem_union, mem_inter_iff, mem_preimage, mem_iUnion, mem_ofPred_eq]
      constructor
      · intro hω
        by_cases htop : min t (e ω).2 = ⊤
        · exact Or.inl ⟨hω, htop⟩
        · obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt htop
          exact Or.inr ⟨N, by rw [← hrecN N ω hN]; exact hω, (hlifeN N ω).2 hN⟩
      · rintro (⟨hω, -⟩ | ⟨N, hω, hN⟩)
        · exact hω
        · rw [hrecN N ω ((hlifeN N ω).1 hN)]
          exact hω
    rw [hsplit]
    exact (hinf C hC).union (MeasurableSet.iUnion fun N => (hcore N).2.1 _ ⟨_, hC.inter (hlifeSet N), rfl⟩)
  refine ⟨hrecd, ?_⟩
  -- the pieces `P_N = {rec ∈ TS, min(t, ζ) < N}`
  set Pn : ℕ → Set Ω := fun N => rec ⁻¹' (TS ∩ {r : RecData | r.2.1 < (N : ℝ≥0∞)}) with hPndef
  have hPn : ∀ N : ℕ, Pn N = recN N ⁻¹' (TS ∩ {r : RecData | r.2.1 < (N : ℝ≥0∞)}) := fun N => by
    ext ω
    simp only [hPndef, mem_preimage, mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩
      rw [hlife] at h2
      rw [← hrecN N ω h2]
      exact ⟨h1, by rw [hlife]; exact h2⟩
    · rintro ⟨h1, h2⟩
      have h3 := (hlifeN N ω).1 h2
      rw [hrecN N ω h3]
      exact ⟨h1, h2⟩
  have hℋ : MeasurableSpace.comap rec inferInstance ⊔ Ito.nullSets P ≤
      aeSigma (MeasurableSpace.comap h₀ inferInstance) P := sup_le hrecd nullSets_le_aeSigma
  refine Supp8.GB6LineL.isHistoryAvoidanceLocal_glue_det hh₀.measurable hℋ
    (fun N => hrecd _ ⟨_, hTS.inter (hlifeSet N), rfl⟩) (fun N => ?_) ?_
  · -- each piece is the record hull of `rec_N`, marked local for `σ(rec_N) ∨ 𝒩`
    have hPN𝒦 : MeasurableSet[MeasurableSpace.comap (recN N) inferInstance ⊔ Ito.nullSets P] (Pn N) :=
      le_sup_left (a := MeasurableSpace.comap (recN N) inferInstance) _ ⟨_, hTS.inter (hlifeSet N), (hPn N).symm⟩
    refine Supp8.GB6LineL.pieceDet_of_local hh₀.measurable hℋ (sup_le (hcore N).2.1 nullSets_le_aeSigma)
      (fun U hU hUH => hrecd _ ⟨_, measurable_bRetOfRec hTS (measurableSet_avoid hU hUH), rfl⟩) (hcore N).2.2
      (fun F hF => ?_) (Eventually.of_forall fun ω hω => ?_)
    · have hle : MeasurableSpace.comap rec inferInstance ⊔ Ito.nullSets P ≤
          WalkLaw.traceSigma (MeasurableSpace.comap (recN N) inferInstance ⊔ Ito.nullSets P) (Pn N) hPN𝒦 := by
        refine sup_le ?_ ?_
        · rintro _ ⟨C, hC, rfl⟩
          change MeasurableSet[MeasurableSpace.comap (recN N) inferInstance ⊔ Ito.nullSets P] (Pn N ∩ rec ⁻¹' C)
          have e : Pn N ∩ rec ⁻¹' C = recN N ⁻¹' ((TS ∩ {r : RecData | r.2.1 < (N : ℝ≥0∞)}) ∩ C) := by
            rw [preimage_inter, ← hPn N]
            ext ω
            simp only [mem_inter_iff, mem_preimage]
            constructor
            · rintro ⟨h1, h2⟩
              have h3 : min t (e ω).2 < N := by
                have := h1.2
                rw [mem_ofPred_eq, hlife] at this
                exact this
              exact ⟨h1, by rw [← hrecN N ω h3]; exact h2⟩
            · rintro ⟨h1, h2⟩
              have h3 : min t (e ω).2 < N := by
                have := h1.2
                rw [mem_ofPred_eq, hlife] at this
                exact this
              exact ⟨h1, by rw [hrecN N ω h3]; exact h2⟩
          rw [e]
          exact le_sup_left (a := MeasurableSpace.comap (recN N) inferInstance) _
            ⟨_, (hTS.inter (hlifeSet N)).inter hC, rfl⟩
        · intro S hS
          change MeasurableSet[MeasurableSpace.comap (recN N) inferInstance ⊔ Ito.nullSets P] (Pn N ∩ S)
          exact hPN𝒦.inter (le_sup_right (a := MeasurableSpace.comap (recN N) inferInstance) _ hS)
      have h1 := hle F hF
      change MeasurableSet[MeasurableSpace.comap (recN N) inferInstance ⊔ Ito.nullSets P] (Pn N ∩ F) at h1
      rwa [inter_comm] at h1
    · -- on the piece the retained set is the record hull of `rec_N`
      have hT : rec ω ∈ TS := hω.1
      have h3 : min t (e ω).2 < N := by
        have := hω.2
        rw [mem_ofPred_eq, hlife] at this
        exact this
      simp only [bRetOfRec, hT, ↓reduceIte]
      rw [hrecN N ω h3]
  · -- off the pieces the record is almost surely outside `TS`, where the retained set is `ℍ`
    filter_upwards [hFTS] with ω hω hnot
    by_cases hT : rec ω ∈ TS
    · exfalso
      have hfin : min t (E 0 ω).2 ≠ ⊤ := finStop_of_mem_bwEvent (hω.2 hT)
      have hfin' : min t (e ω).2 ≠ ⊤ := by rw [StagedReg.regularize_snd]; exact hfin
      obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt hfin'
      exact hnot N ⟨hT, by rw [mem_ofPred_eq, hlife]; exact hN⟩
    · simp only [bRetOfRec, hT, ↓reduceIte, subset_refl]

end InteractingSLE.Theorem14.BW1Safe
