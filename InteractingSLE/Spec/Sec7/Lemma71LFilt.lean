/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71LStop

/-!
# Lemma 7.1: the prefix filtration of the mapped segment inside the stopped three-curve histories (R3/G7)

Packet PROVE-LEMMA71L, item R3/G7. Specification §7.1 (`source/spec/p193-240.md` L590–L594, p. 224): "For each
bounded stopping time of this mapped path, the history-locality statement of Lemma 6.2 applies to the revealed outer
curves and the middle prefix."

The prefix filtration of the mapped segment `γ'` at capacity time `t` (`Lemma71E.prefixFiltrationOf σ(β, α) γ' t`) is
contained, up to null sets, in the σ-algebra of the labelled histories of the outer curves and of the middle curve
stopped at the capacity time `τ_t = capTime … t` (`prefixFiltrationOf_le_aeSigma`). On the good event every prefix
event `{r < capLife γ', Q ∩ γ'([0, capInv r]) ≠ ∅}` is an event of `(β, α, γ|[0, τ_t])`
(`mem_prefixEvent_iff`): the terminal capacity by `ofReal_lt_capLife_iff` (or `τ_t < ∞`), the meeting condition by
`inter_image_nonempty_iff`, read on the coordinates of `γ` before `τ_r ≤ τ_t`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric Complex Bornology
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.Lemma71L

open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley cayleyInv)
open Lemma71I Lemma71C Lemma71K Sec6 LocalSets

/-! ### The prefix events on the histories -/

section Hist

variable {G : (Hist × Hist) × ℂ → ℂ} {M : Set ((Hist × Hist) × ℂ)} {Y : Hist × Hist → ℂ}

/-- **The prefix event on the histories** `((x, y), (T, c))`: the terminal capacity exceeds `r` (automatic when the
stopping time `T` is finite; read on the complete coordinates otherwise), and chart values of rational coordinates in
the pocket before the level time of `2r` come arbitrarily close to `Q`. -/
def prefixSet (G : (Hist × Hist) × ℂ → ℂ) (M : Set ((Hist × Hist) × ℂ)) (Y : Hist × Hist → ℂ) (r : ℝ≥0)
    (Q : Set ℂ) : Set ((Hist × Hist) × Hist) :=
  {z | (z.2.1 < ⊤ ∨ ∃ q : ℚ≥0, EndOK (Y z.1) ((q : ℝ≥0) : ℝ≥0∞) z.2.2 ∧
      ENNReal.ofReal (2 * (r : ℝ)) < capFamily G M q z.1 z.2.2) ∧
    ∀ m : ℕ, ∃ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) ≤ levelRule (capFamily G M) (ENNReal.ofReal (2 * (r : ℝ))) z.1 z.2.2 ∧
      (z.1, z.2.2 q) ∈ M ∧ infDist (G (z.1, z.2.2 q)) Q < 1 / ((m : ℝ) + 1)}

theorem measurableSet_prefixSet (hG : Measurable G) (hM : MeasurableSet M) (hY : Measurable Y) (r : ℝ≥0)
    (Q : Set ℂ) : MeasurableSet (prefixSet G M Y r Q) := by
  have hπ : Measurable fun z : (Hist × Hist) × Hist => (z.1, z.2.2) :=
    measurable_fst.prodMk (measurable_snd.comp measurable_snd)
  have hcf : ∀ q, Measurable fun z : (Hist × Hist) × Hist => capFamily G M q z.1 z.2.2 := fun q => by
    have h2 := (measurable_capFamily hG hM q).comp hπ
    rw [Function.comp_def] at h2
    exact h2
  have hlr : Measurable fun z : (Hist × Hist) × Hist =>
      levelRule (capFamily G M) (ENNReal.ofReal (2 * (r : ℝ))) z.1 z.2.2 := by
    have h2 := (measurable_levelRule (a := ENNReal.ofReal (2 * (r : ℝ))) (measurable_capFamily hG hM)).comp hπ
    rw [Function.comp_def] at h2
    exact h2
  have hpt : ∀ q : ℚ≥0, Measurable fun z : (Hist × Hist) × Hist => (z.1, z.2.2 q) := fun q =>
    measurable_fst.prodMk ((measurable_pi_apply q).comp (measurable_snd.comp measurable_snd))
  have hE : ∀ q : ℚ≥0, MeasurableSet {z : (Hist × Hist) × Hist | EndOK (Y z.1) ((q : ℝ≥0) : ℝ≥0∞) z.2.2} :=
    fun q => hπ (measurableSet_endOK hY (T := fun _ => ((q : ℝ≥0) : ℝ≥0∞)) measurable_const)
  have hA : MeasurableSet {z : (Hist × Hist) × Hist | z.2.1 < ⊤ ∨ ∃ q : ℚ≥0,
      EndOK (Y z.1) ((q : ℝ≥0) : ℝ≥0∞) z.2.2 ∧ ENNReal.ofReal (2 * (r : ℝ)) < capFamily G M q z.1 z.2.2} := by
    have e : {z : (Hist × Hist) × Hist | z.2.1 < ⊤ ∨ ∃ q : ℚ≥0,
        EndOK (Y z.1) ((q : ℝ≥0) : ℝ≥0∞) z.2.2 ∧ ENNReal.ofReal (2 * (r : ℝ)) < capFamily G M q z.1 z.2.2} =
        {z : (Hist × Hist) × Hist | z.2.1 < ⊤} ∪ ⋃ q : ℚ≥0,
          ({z : (Hist × Hist) × Hist | EndOK (Y z.1) ((q : ℝ≥0) : ℝ≥0∞) z.2.2} ∩
            {z | ENNReal.ofReal (2 * (r : ℝ)) < capFamily G M q z.1 z.2.2}) := by
      ext z
      simp only [mem_ofPred_eq, mem_union, mem_iUnion, mem_inter_iff]
    rw [e]
    exact (measurableSet_lt (measurable_fst.comp measurable_snd) measurable_const).union
      (MeasurableSet.iUnion fun q => (hE q).inter (measurableSet_lt measurable_const (hcf q)))
  have hB : MeasurableSet {z : (Hist × Hist) × Hist | ∀ m : ℕ, ∃ q : ℚ≥0,
      ((q : ℝ≥0) : ℝ≥0∞) ≤ levelRule (capFamily G M) (ENNReal.ofReal (2 * (r : ℝ))) z.1 z.2.2 ∧
        (z.1, z.2.2 q) ∈ M ∧ infDist (G (z.1, z.2.2 q)) Q < 1 / ((m : ℝ) + 1)} := by
    have e : {z : (Hist × Hist) × Hist | ∀ m : ℕ, ∃ q : ℚ≥0,
        ((q : ℝ≥0) : ℝ≥0∞) ≤ levelRule (capFamily G M) (ENNReal.ofReal (2 * (r : ℝ))) z.1 z.2.2 ∧
          (z.1, z.2.2 q) ∈ M ∧ infDist (G (z.1, z.2.2 q)) Q < 1 / ((m : ℝ) + 1)} =
        ⋂ m : ℕ, ⋃ q : ℚ≥0, ({z : (Hist × Hist) × Hist | ((q : ℝ≥0) : ℝ≥0∞) ≤
            levelRule (capFamily G M) (ENNReal.ofReal (2 * (r : ℝ))) z.1 z.2.2} ∩
          ((fun z : (Hist × Hist) × Hist => (z.1, z.2.2 q)) ⁻¹' M ∩
            {z | infDist (G (z.1, z.2.2 q)) Q < 1 / ((m : ℝ) + 1)})) := by
      ext z
      simp only [mem_ofPred_eq, mem_iInter, mem_iUnion, mem_inter_iff, mem_preimage]
    rw [e]
    refine MeasurableSet.iInter fun m => MeasurableSet.iUnion fun q => ?_
    refine (measurableSet_le measurable_const hlr).inter ((hpt q hM).inter (measurableSet_lt ?_ measurable_const))
    exact (continuous_infDist_pt Q).measurable.comp (hG.comp (hpt q))
  exact hA.inter hB

end Hist

/-! ### The prefix events on the good event -/

section Space

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {β α γ : Ω → ℝ≥0 → ℂ} {C : Ω → Set ℂ} {c : Ω → Chart}
  {γ' : Ω → ℝ → ℂ} {G : (Hist × Hist) × ℂ → ℂ} {M : Set ((Hist × Hist) × ℂ)} {Y : Hist × Hist → ℂ}

omit mΩ in
/-- **On the good event, a prefix event of the mapped segment up to capacity time `t` is an event of the outer
histories and of the middle curve stopped at the capacity time `τ_t`.** -/
theorem mem_prefixEvent_iff {ω : Ω} (hg : PocketGood β α γ C c γ' ω) (hCo : IsOpen (C ω)) (hCH : C ω ⊆ H)
    (hc : (c ω).IsConformal) (hdom : ((c ω).dom : Set ℂ) = C ω) (hγH : ∀ t, γ ω t ∈ Hbar)
    (hγc : Continuous (γ ω)) (hΓ : IsSegCurve (γ' ω)) (hMiff : ∀ z, (outerHist β α ω, z) ∈ M ↔ z ∈ C ω)
    (hGeq : ∀ z ∈ C ω, G (outerHist β α ω, z) = (c ω).1 z) (hYeq : Y (outerHist β α ω) = closePt α C ω)
    {r t : ℝ≥0} (hr : 0 < r) (hrt : r ≤ t) (n : ℕ) (k : ℤ × ℤ) :
    ω ∈ Lemma71E.prefixEvent γ' r n k ↔
      (outerHist β α ω, histOf (pathCoord (γ ω)) (capTime G M Y β α γ t ω)) ∈
        prefixSet G M Y r (Restart.dyadicSquare n k) := by
  obtain ⟨hvc, -, -, hD1, hD2⟩ := hg.visit hCo hCH hc hdom hγH
  rw [← hYeq] at hD1 hD2
  have hFc : ContinuousOn (c ω).1 (C ω) := by rw [← hdom]; exact hc.differentiableOn_fwd.continuousOn
  set x := outerHist β α ω with hx
  set cγ := pathCoord (γ ω) with hcγ
  set T := capTime G M Y β α γ t ω with hTdef
  have hTx : T = capRule G M Y (ENNReal.ofReal (2 * (t : ℝ))) x cγ := rfl
  have hQc : IsCompact (Restart.dyadicSquare n k) := Restart.isCompact_dyadicSquare n k
  have hQne := Lemma71E.nonempty_dyadicSquare n k
  have hr' : (0 : ℝ) < r := hr
  have hF1 : T < ⊤ → ENNReal.ofReal (t : ℝ) < capLife (γ' ω) := fun hT =>
    lt_capLife_of_capRule_lt_top hMiff hGeq hFc hΓ hvc hD2 (hTx ▸ hT)
  have hF3 : ENNReal.ofReal (r : ℝ) < capLife (γ' ω) →
      levelRule (capFamily G M) (ENNReal.ofReal (2 * (r : ℝ))) x cγ ≤ T := by
    intro hrl
    have hvc' := hvc
    obtain ⟨hκc, hκm, hκ0, hlim, hcov, hdense⟩ := hvc'
    rw [Lemma71Pin.levelRule_capFamily_eq hMiff hGeq hCo hFc hγc hΓ hκc hκm hκ0 hlim hcov hdense hr' hrl]
    by_cases hT : T < ⊤
    · have htl := hF1 hT
      have ht' : (0 : ℝ) < t := lt_of_lt_of_le hr' (NNReal.coe_le_coe.2 hrt)
      rw [hTx, capRule_eq_visitClock hMiff hGeq hCo hFc hγc hΓ hvc hD1 ht' htl]
      refine ENNReal.ofReal_le_ofReal (hκm.monotoneOn (capInv_nonneg _ _) (capInv_nonneg _ _) ?_)
      obtain ⟨ht0, htt⟩ := hΓ.capInv_spec ht'.le htl
      exact hΓ.capInv_le ht0 hr'.le (by rw [htt]; exact_mod_cast hrt)
    · rw [not_lt, top_le_iff] at hT
      rw [hT]
      exact le_top
  have hstop : ∀ L, L ≤ T → ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) ≤ L → stopCoord cγ T q = cγ q :=
    fun L hL q hq => stopCoord_of_le (hq.trans hL)
  have hF4 : ENNReal.ofReal (r : ℝ) < capLife (γ' ω) →
      levelRule (capFamily G M) (ENNReal.ofReal (2 * (r : ℝ))) x (stopCoord cγ T) =
        levelRule (capFamily G M) (ENNReal.ofReal (2 * (r : ℝ))) x cγ := fun hrl =>
    levelRule_galmarino (capFamily_local G M) x cγ (stopCoord cγ T) fun q hq => (hstop _ (hF3 hrl) q hq).symm
  have htop : stopCoord cγ ⊤ = cγ := funext fun q => stopCoord_of_le le_top
  have hcap := ofReal_lt_capLife_iff hMiff hGeq hCo hFc hγc hΓ hvc hD1 hD2 hr'.le
  show ((r : ℝ≥0∞) < capLife (γ' ω) ∧ (Restart.dyadicSquare n k ∩ γ' ω '' Icc 0 (capInv (γ' ω) r)).Nonempty) ↔
    ((T < ⊤ ∨ ∃ q : ℚ≥0, EndOK (Y x) ((q : ℝ≥0) : ℝ≥0∞) (stopCoord cγ T) ∧
        ENNReal.ofReal (2 * (r : ℝ)) < capFamily G M q x (stopCoord cγ T)) ∧
      ∀ m : ℕ, ∃ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) ≤
          levelRule (capFamily G M) (ENNReal.ofReal (2 * (r : ℝ))) x (stopCoord cγ T) ∧
        (x, stopCoord cγ T q) ∈ M ∧ infDist (G (x, stopCoord cγ T q)) (Restart.dyadicSquare n k) <
          1 / ((m : ℝ) + 1))
  rw [← ENNReal.ofReal_coe_nnreal]
  constructor
  · rintro ⟨hrl, hne⟩
    refine ⟨?_, fun m => ?_⟩
    · by_cases hT : T < ⊤
      · exact Or.inl hT
      · right
        rw [not_lt, top_le_iff] at hT
        rw [hT, htop]
        exact hcap.1 hrl
    · obtain ⟨q, hq, hqM, hqd⟩ := (inter_image_nonempty_iff hMiff hGeq hCo hFc hγc hΓ hvc hr' hrl hQc hQne).1 hne m
      refine ⟨q, by rw [hF4 hrl]; exact hq, ?_⟩
      rw [hstop _ (hF3 hrl) q hq]
      exact ⟨hqM, hqd⟩
  · rintro ⟨hcp, himg⟩
    have hrl : ENNReal.ofReal (r : ℝ) < capLife (γ' ω) := by
      by_cases hT : T < ⊤
      · exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (NNReal.coe_le_coe.2 hrt)) (hF1 hT)
      · rw [not_lt, top_le_iff] at hT
        rcases hcp with h1 | h2
        · rw [hT] at h1
          exact absurd h1 (lt_irrefl _)
        · rw [hT, htop] at h2
          exact hcap.2 h2
    refine ⟨hrl, (inter_image_nonempty_iff hMiff hGeq hCo hFc hγc hΓ hvc hr' hrl hQc hQne).2 fun m => ?_⟩
    obtain ⟨q, hq, hqM, hqd⟩ := himg m
    rw [hF4 hrl] at hq
    rw [hstop _ (hF3 hrl) q hq] at hqM hqd
    exact ⟨q, hq, hqM, hqd⟩

/-- **R3/G7: the prefix filtration of the mapped segment at capacity time `t` is contained, up to null sets, in the
σ-algebra of the labelled histories `(β, α, γ|[0, τ_t])`**, `τ_t = capTime G M Y β α γ t` (`G`, `M`, `Y` from
`exists_capData`). -/
theorem prefixFiltrationOf_le_aeSigma {P : Measure Ω} {κ θ₁ θ₂ a b : ℝ}
    {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} {u₀ : ℂ → ℝ} {ζβ ζα ζγ : Ω → ℝ≥0∞}
    (hS : Lemma72B.IsThreeCurveSpace κ θ₁ θ₂ a b P h u₀ β α γ ζβ ζα ζγ)
    (hpc : IsPocketConstruction P β α γ C c γ') (hG : Measurable G) (hM : MeasurableSet M) (hY : Measurable Y)
    (hMiff : ∀ ω z, (outerHist β α ω, z) ∈ M ↔ z ∈ C ω)
    (hGeq : ∀ ω z, z ∈ C ω → G (outerHist β α ω, z) = (c ω).1 z)
    (hYeq : ∀ ω, Y (outerHist β α ω) = closePt α C ω) (t : ℝ≥0) :
    Lemma71E.prefixFiltrationOf (mΩ := mΩ) (MeasurableSpace.comap (fun ω => (β ω, α ω)) inferInstance) γ' t ≤
      aeSigma (stoppedHistSigma (Three.threeCurves β α γ) (Three.threeStops (capTime G M Y β α γ t))) P := by
  have hS' := hS
  obtain ⟨-, -, -, -, -, -, hβ62, hα62, hγ62, -⟩ := hS'
  have hpc' := hpc
  obtain ⟨hC, -, hconf, hdom, -, -, -, -, -, -, hseg, -, -⟩ := hpc'
  refine inf_le_left.trans (sup_le ?_ (MeasurableSpace.generateFrom_le ?_))
  · -- the outer curves are measurable for the labelled histories
    refine le_trans ?_ (le_aeSigma _ P)
    have hβm : ∀ s, Measurable[stoppedHistSigma (Three.threeCurves β α γ)
        (Three.threeStops (capTime G M Y β α γ t))] fun ω => β ω s := fun s =>
      Lemma71G.measurable_outer_stoppedHistSigma (i := 0) (by decide) hβ62.1 s
    have hαm : ∀ s, Measurable[stoppedHistSigma (Three.threeCurves β α γ)
        (Three.threeStops (capTime G M Y β α γ t))] fun ω => α ω s := fun s =>
      Lemma71G.measurable_outer_stoppedHistSigma (i := 1) (by decide) hα62.1 s
    let _ : MeasurableSpace Ω := stoppedHistSigma (Three.threeCurves β α γ)
      (Three.threeStops (capTime G M Y β α γ t))
    exact measurable_iff_comap_le.1 ((measurable_pi_iff.2 hβm).prodMk (measurable_pi_iff.2 hαm))
  · rintro s ⟨r, hrt, n, k, rfl⟩
    obtain rfl | hr0 := eq_or_lt_of_le (zero_le (a := r))
    · -- capacity time `0`: a deterministic event
      have he : Lemma71E.prefixEvent γ' 0 n k = {_ω | (0 : ℂ) ∈ Restart.dyadicSquare n k} := by
        ext ω
        have hΓ := hseg ω
        have hpos : ((0 : ℝ≥0) : ℝ≥0∞) < capLife (γ' ω) :=
          lt_of_le_of_lt bot_le (hΓ.ofReal_capClock_lt zero_le_one)
        have hinv : capInv (γ' ω) ((0 : ℝ≥0) : ℝ) = 0 := hΓ.capInv_of_nonpos le_rfl
        show ((0 : ℝ≥0) : ℝ≥0∞) < capLife (γ' ω) ∧
            (Restart.dyadicSquare n k ∩ γ' ω '' Icc 0 (capInv (γ' ω) ((0 : ℝ≥0) : ℝ))).Nonempty ↔
          (0 : ℂ) ∈ Restart.dyadicSquare n k
        rw [hinv, Icc_self, image_singleton, hΓ.2.2.2.1, inter_singleton_nonempty]
        exact ⟨fun h => h.2, fun h => ⟨hpos, h⟩⟩
      rw [he]
      exact ⟨_, MeasurableSet.const _, EventuallyEq.rfl⟩
    · refine ⟨(fun ω => (outerHist β α ω, histOf (pathCoord (γ ω)) (capTime G M Y β α γ t ω))) ⁻¹'
        prefixSet G M Y r (Restart.dyadicSquare n k), ?_, ?_⟩
      · have hY3 := comap_measurable (m := (inferInstance : MeasurableSpace (Fin 3 → Hist)))
          (fun ω i => histOf (pathCoord (Three.threeCurves β α γ i ω))
            (Three.threeStops (capTime G M Y β α γ t) i ω))
        have hrearr : Measurable fun v : Fin 3 → Hist => ((v 0, v 1), v 2) :=
          ((measurable_pi_apply 0).prodMk (measurable_pi_apply 1)).prodMk (measurable_pi_apply 2)
        exact (hrearr.comp hY3) (measurableSet_prefixSet hG hM hY r _)
      · filter_upwards [ae_pocketGood hS hpc] with ω hg
        exact propext (mem_prefixEvent_iff hg (hC ω).1 (hC ω).2.2.2 (hconf ω) (hdom ω)
          (fun s => hγ62.2.2.1 ω s) (hγ62.1 ω) (hseg ω) (hMiff ω) (hGeq ω) (hYeq ω) hr0 hrt n k)

end Space

end InteractingSLE.Sec7.Lemma71L
