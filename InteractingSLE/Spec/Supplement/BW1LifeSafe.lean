/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BW1LifeMain
import InteractingSLE.Spec.Supplement.BW1ChainMain

/-!
# Proposition BW1: the relative continuation threshold is never reached

Packet PROVE-BW1-LIFE. One of the four clauses of K2's input `Supp8.Q3Stop.HasRelSafe` for BW1's relative
exploration is deterministic: BW1's relative word (the counterflow word of the stop word) is admissible for every
record (`BW1LifeWord`: (BW1.2) and the ambient bounds), so every side partial sum of its flow-line word exceeds `−2`
and the relative continuation threshold is `∞` for every relative driver (`BW1Chain.thresholdTime_geom_eq_top`). The
stop therefore always precedes the threshold (`ae_canonStp_le_thr_bw`).

* **`BW1RelSafeSLStatement`** (named input, the marked union law): the other three clauses — K2's (S) and (L) for the
  relative exploration with lifetime the stop, and the integrability of the relative field;
* **`bw1RelSafeStatement_of_SL`**: `BW1RelSafeStatement` from it.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Finset
open scoped NNReal ENNReal
open QuantumZipper (chiC)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.BW1Life

open Exist Exist.StagedLaw Exist.Staged Restart Supp8.Q3Stop

/-- **The counterflow word of an admissible word has side partial sums above `−2`** (the computation of
`GW1Laws.ae_cfDrvOf_snd_eq_top`, through the counterflow data of the returned word). -/
theorem partialSums_cfWordOf {κ : ℝ} (hκ : 0 < κ) {c : BoundaryWord} (hg : GW1Laws.IsCfGoodWord κ c) :
    (∀ i : Fin (flowLineNL (GW1Laws.cfWordOf κ c).fn (GW1Laws.cfWordOf κ c).jumps 0),
      -2 < ∑ l ∈ univ.filter (fun l => l ≤ i),
        flowLineRhoL (16 / κ) (GW1Laws.cfWordOf κ c).fn (GW1Laws.cfWordOf κ c).jumps 0 0 l) ∧
    ∀ j : Fin (flowLineNR (GW1Laws.cfWordOf κ c).fn (GW1Laws.cfWordOf κ c).jumps 0),
      -2 < ∑ l ∈ univ.filter (fun l => l ≤ j),
        flowLineRhoR (16 / κ) (GW1Laws.cfWordOf κ c).fn (GW1Laws.cfWordOf κ c).jumps 0 0 l := by
  obtain ⟨hc, hL, hR⟩ := hg
  have hκ' : 0 < 16 / κ := GW4Traverse.sixteen_div_pos hκ
  have hΛ := Sec4.sleLambda_sixteen_div_eq_sub hκ
  set c' := GW1Laws.cfWordOf κ c with hc'
  have hpc' := c'.isPiecewiseConstantBoundaryData
  have hdR : ∀ y, 0 < y → y ∉ c'.jumps → -sleLambda (16 / κ) < c'.fn y := by
    intro y hy hyJ
    rw [GW1Laws.fn_cfWordOf κ hc hyJ, GW3Word.counterflowData_of_pos hκ c.fn hy, hΛ]
    rw [GW1Laws.jumps_cfWordOf κ hc] at hyJ
    have hx : -y⁻¹ < 0 := neg_neg_of_pos (inv_pos.2 hy)
    have := hL (-y⁻¹) hx (Sec7.StripSysField.negInv_notMem_of_notMem_returnExcept hyJ)
    linarith
  have hdL : ∀ y, y < 0 → y ∉ c'.jumps → c'.fn y < sleLambda (16 / κ) := by
    intro y hy hyJ
    rw [GW1Laws.fn_cfWordOf κ hc hyJ, GW3Word.counterflowData_of_neg hκ c.fn hy, hΛ]
    rw [GW1Laws.jumps_cfWordOf κ hc] at hyJ
    have hx : 0 < -y⁻¹ := neg_pos.2 (inv_lt_zero.2 hy)
    have := hR (-y⁻¹) hx (Sec7.StripSysField.negInv_notMem_of_notMem_returnExcept hyJ)
    linarith
  exact ⟨fun i => GW3Word.neg_two_lt_sum_flowLineRhoL_of_forall hκ' hpc' hdL i,
    fun j => GW3Word.neg_two_lt_sum_flowLineRhoR_of_forall hκ' hpc' hdR j⟩

/-- **The stop precedes the relative continuation threshold**: for every law on the canonical relative space, every
record event and every word type, BW1's relative threshold is `∞` on the type event (the typed weights of a type that
occurs are the flow-line weights of an admissible counterflow word; a type that does not occur has an empty event). -/
theorem ae_canonStp_le_thr_bw {κ θ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hθ : θ ∈ Icc (-(Real.pi / 2)) (Real.pi / 2))
    {c₀ : BoundaryWord}
    (hL : ∀ y, y < 0 → y ∉ c₀.jumps → c₀.fn y + -(Real.pi / 2) * chiC κ < sleLambda κ)
    (hR : ∀ y, 0 < y → y ∉ c₀.jumps → -sleLambda κ < c₀.fn y + Real.pi / 2 * chiC κ)
    (μ : Measure CanonSpace) (TS : Set RecData) (w : WordType) :
    ∀ᵐ y ∂(μ[|typeEvent (16 / κ) w (bwRelWord κ θ c₀) TS]), canonStp y ≤
      FCDet.thr (typedRhoL w) (typedRhoR w) canonDrv (fun y => typedXL (16 / κ) w (bwRelWord κ θ c₀ y.1))
        (fun y => typedXR (16 / κ) w (bwRelWord κ θ c₀ y.1)) y := by
  by_cases hw : ∃ r, wordType (16 / κ) (bwRelWord κ θ c₀ r) = w
  · obtain ⟨r, rfl⟩ := hw
    have hc₀w : BoundaryWord.shiftW 0 c₀ = c₀ := by
      obtain ⟨n, p, v⟩ := c₀
      simp [BoundaryWord.shiftW]
    have hgood : GW1Laws.IsCfGoodWord κ (stopWord κ (BoundaryWord.shiftW 0 c₀, θ, r)) := by
      rw [hc₀w]; exact isCfGoodWord_stopWord hκ hκ4 hθ hL hR r
    obtain ⟨hsL, hsR⟩ := partialSums_cfWordOf hκ hgood
    refine Eventually.of_forall fun y => ?_
    have hsL' : ∀ m : Fin (wordType (16 / κ) (bwRelWord κ θ c₀ r)).1, -2 < ∑ i ∈ univ.filter (fun i => i ≤ m),
        typedRhoL (wordType (16 / κ) (bwRelWord κ θ c₀ r)) i := fun m => by
      have e : ∀ i, typedRhoL (wordType (16 / κ) (bwRelWord κ θ c₀ r)) i =
          flowLineRhoL (16 / κ) (bwRelWord κ θ c₀ r).fn (bwRelWord κ θ c₀ r).jumps 0 0 i := fun i =>
        padFL_snd_fst_fin _ _ _ _ i
      simp only [e]
      exact hsL m
    have hsR' : ∀ m : Fin (wordType (16 / κ) (bwRelWord κ θ c₀ r)).2.1, -2 < ∑ i ∈ univ.filter (fun i => i ≤ m),
        typedRhoR (wordType (16 / κ) (bwRelWord κ θ c₀ r)) i := fun m => by
      have e : ∀ i, typedRhoR (wordType (16 / κ) (bwRelWord κ θ c₀ r)) i =
          flowLineRhoR (16 / κ) (bwRelWord κ θ c₀ r).fn (bwRelWord κ θ c₀ r).jumps 0 0 i := fun i =>
        padFL_snd_snd_fin _ _ _ _ i
      simp only [e]
      exact hsR m
    unfold FCDet.thr
    rw [BW1Chain.thresholdTime_geom_eq_top hsL' hsR' (fun y => antitone_typedXL _ _ _)
      (fun y => monotone_typedXR _ _ _) continuous_canonDrv y]
    exact le_top
  · have hS : typeEvent (16 / κ) w (bwRelWord κ θ c₀) TS = ∅ := by
      ext y
      simp only [typeEvent, Set.mem_preimage, mem_empty_iff_false, iff_false]
      exact fun h => hw ⟨_, h.2⟩
    rw [hS, ProbabilityTheory.cond_empty]
    exact ae_zero.symm ▸ Filter.eventually_bot

/-- **Named input: BW1's relative safe law, its probabilistic clauses** (the marked union law in the relative clock;
see `BW1RelSafeStatement`): K2's (S) and (L) for the relative exploration with lifetime the stop, and the
integrability of the relative field, under the joint law of the record and the relative variable conditioned on the
record event of each word type. (The fourth clause of `HasRelSafe`, the stop before the threshold, is proved:
`ae_canonStp_le_thr_bw`.) -/
def BW1RelSafeSLStatement : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens) (W' : ℝ≥0 → Ω → ℝ)
    (ζ' : Ω → ℝ≥0∞) (θ : ℝ) (t : ℝ≥0∞) (gw2 : Bool) (rest : List Instr) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞),
    IsBW1Setting κ b jumps P h W' ζ' θ t gw2 rest E → ∀ (r : Bool) (TS : Set RecData), MeasurableSet TS →
    (∀ᵐ ω ∂P, ω ∈ bwEvent κ b jumps (bwSpec gw2 θ t rest) E r ↔ bwRec κ b jumps (bwSpec gw2 θ t rest) E ω ∈ TS) →
    ∀ c₀ : BoundaryWord, c₀.jumps = jumps → (∀ y ∉ jumps, c₀.fn y = b y) →
    ∀ (R : ℕ → ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ≥0∞) (ℓ : Ω → ℝ≥0 → ℝ≥0),
      IsBW1RelVersion P (bwRec κ b jumps (bwSpec gw2 θ t rest) E) (bwEvent κ b jumps (bwSpec gw2 θ t rest) E r)
        (bwChart κ b jumps (bwSpec gw2 θ t rest) E) W' (bwContact κ b jumps (bwSpec gw2 θ t rest) W' E) R V ℓ →
      ∀ (m : ℕ) (w : WordType),
        Restart.DomainMarkov.K2.HasSafeLaw (16 / κ) (typedRhoL w) (typedRhoR w)
          ((P.map fun ω => (bwRec κ b jumps (bwSpec gw2 θ t rest) E ω,
            Supp8.GB6.RelDrv.relVar (bwRelField κ b jumps (bwSpec gw2 θ t rest) h E) (R m) (V m) ω))[|
              typeEvent (16 / κ) w (bwRelWord κ θ c₀) TS]) canonFilt univ canonStp canonDrv
          (Sec7.PocketTraversal.geomLW canonDrv fun y => typedXL (16 / κ) w (bwRelWord κ θ c₀ y.1))
          (Sec7.PocketTraversal.geomRW canonDrv fun y => typedXR (16 / κ) w (bwRelWord κ θ c₀ y.1)) canonFld ∧
        Restart.DomainMarkov.K2.HasSafeMembers
          ((P.map fun ω => (bwRec κ b jumps (bwSpec gw2 θ t rest) E ω,
            Supp8.GB6.RelDrv.relVar (bwRelField κ b jumps (bwSpec gw2 θ t rest) h E) (R m) (V m) ω))[|
              typeEvent (16 / κ) w (bwRelWord κ θ c₀) TS]) canonFilt univ canonStp canonDrv canonFld ∧
        ∀ φ : TestOn upperHalfPlaneOpens, Integrable (fun y => canonFld y φ)
          ((P.map fun ω => (bwRec κ b jumps (bwSpec gw2 θ t rest) E ω,
            Supp8.GB6.RelDrv.relVar (bwRelField κ b jumps (bwSpec gw2 θ t rest) h E) (R m) (V m) ω))[|
              typeEvent (16 / κ) w (bwRelWord κ θ c₀) TS])

/-- **`BW1RelSafeStatement` from its probabilistic clauses** (the threshold clause is `ae_canonStp_le_thr_bw`, with
the ambient bounds of the original counterflow word, `GW1Conn.ambient_bounds`, from Theorem 1.3 at universe `0`). -/
theorem bw1RelSafeStatement_of_SL (hT13₀ : Exist.Theorem13Statement.{0}) (hSL : BW1RelSafeSLStatement.{u}) :
    BW1RelSafeStatement.{u} := by
  intro κ b jumps Ω _ _ P _ h W' ζ' θ t gw2 rest E hset r TS hTS hFTS c₀ hc₀J hc₀ R V ℓ hver m w
  obtain ⟨hκ, hκ4, hb, hh, hcf, hζ', hθ, hS⟩ := hset
  obtain ⟨hambL, hambR⟩ := GW1Conn.ambient_bounds (BR3Ref.gw0ForwardStatement_of_theorem13 hT13₀) hκ hκ4 hb hh hcf
    hζ'
  have hL : ∀ y, y < 0 → y ∉ c₀.jumps → c₀.fn y + -(Real.pi / 2) * chiC κ < sleLambda κ := fun y hy hyJ => by
    rw [hc₀J] at hyJ; rw [hc₀ y hyJ]; exact hambL y hy hyJ
  have hR : ∀ y, 0 < y → y ∉ c₀.jumps → -sleLambda κ < c₀.fn y + Real.pi / 2 * chiC κ := fun y hy hyJ => by
    rw [hc₀J] at hyJ; rw [hc₀ y hyJ]; exact hambR y hy hyJ
  obtain ⟨hlaw, hmem, hint⟩ := hSL κ b jumps P h W' ζ' θ t gw2 rest E ⟨hκ, hκ4, hb, hh, hcf, hζ', hθ, hS⟩
    r TS hTS hFTS c₀ hc₀J hc₀ R V ℓ hver m w
  exact ⟨hlaw, hmem, ae_canonStp_le_thr_bw hκ hκ4 hθ hL hR _ TS w, hint⟩

end InteractingSLE.Theorem14.BW1Life
