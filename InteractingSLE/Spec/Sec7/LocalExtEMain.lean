/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.LocalExtERestart

/-!
# The restart statement from the restarted two-seed extension (cells, `σ`, (R3) at a restart)

Packet PROVE-LOCEXT-E. Specification p. 251 ("Aux. lemma 53 justifies applying the preceding local comparison
conditionally after every own-filtration stopping time strictly before the threshold. … Applying Aux. lemma 55
conditionally and using its countable reference family produces a strictly longer own-filtration stopped driving
history determined by `h`") and p. 252 ("The finitely many possible amalgamated seed-weight pairs and countably many
chosen radii supply a measurable restart rule").

* `RestartTwoSeedExtensionStatement κ` (**named input**: Aux. lemma 53 with the data-uniform time-`0` construction of
  Aux. lemma 55): for every finite stopping time `T` of the frozen driving filtration and every event `D ∈ 𝓓_T` of
  positive probability on which `T < ζ`, the seed pattern of the state at `T` is `(S_L, S_R)` (admissible weights) and
  `r` is an admissible seed radius of the current positions, a probability measure `Q` equivalent to `P|_D` carries an
  extended reference pair over `(h, K)` (`K` a measurable version of `𝒳_T` on `D`) recovering the **two-seed history of
  the path restarted at `T`**, stopped at its local stop of radius `r`;
* `codeFam`: families indexed by `ℕ` through the codes `Encodable.decode₂`;
* `exists_mem_cellEvent` (covering), `cellEvent_disjoint` (the cells are disjoint);
* **`restartCellExtensionStatement_of_restartTwoSeed`**: the corrected restart statement
  `RestartCellExtensionStatement κ` of `LocalExtEStmt.lean`, with `σ = spliceTime` of the cell stops
  `min(τ, N + 1) + S'` (a stopping time, strictly after `τ` on `{τ < ζ}`), the cells `cellSet c`, the weights of the
  pattern and the radius `2^{-k}`; the recovered history `𝒳_σ` is `concatHist 𝒳_τ (reindexHist c r Y')` of the
  two-seed history `Y'` ((R3) at a restart, `LocalExtEPath.lean`);
* **`exists_measurable_lifetime_trace_eq_comp_field_of_restartTwoSeed`**: the conclusion of the frozen Theorem 1.2
  for every `κ > 0` from the two-seed graph input and `RestartTwoSeedExtensionStatement κ`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace LocalExt

open Sec7 Sec5.Markov Coupling Determination

/-- **Named input: the restarted two-seed extension** (Aux. lemma 53 with the time-`0` construction of Aux. lemma 55
run with `𝓕_T`-measurable data; specification pp. 245–251). For every coupling of an ordered force word, every finite
stopping time `T` of the frozen driving filtration `𝓓`, every good event `G`, every admissible seed pattern
`(S_L, S_R)` (weights `> −2`) and radius `r`, and every event `D ∈ 𝓓_T` of positive probability on which `T < ζ`, the
marks at the driver at `T` are exactly `S_L`, `S_R`, and `r` is an admissible seed radius of the current positions
`V_T − W_T`: for every measurable `K` equal to the recorded history `𝒳_T` almost surely on `D`, there is a probability
measure `Q` equivalent to `P|_D` carrying an extended reference pair (`HasReferenceExtension`, seed weights the sums
over the pattern, radius `r`) over `(h, K)` that recovers the two-seed history (`twoSeedProj` with the current
positions) of the path restarted at `T` (`W_{T+·} − W_T`, `V_{T+·} − W_T`, `ζ − T`), stopped at its capped local stop
of radius `r`.

Conditionally on `D` the restarted field and driving process form a coupling with the current positions as random
`𝓕_T`-measurable initial data (Aux. lemma 53); the time-`0` construction of Aux. lemma 55 for that coupling ((HL3):
`Q = Z·P[·|D]`; (HL8)–(HL9): the recoded chart field; Aux. 54: the extension) gives the extended reference pair. -/
def RestartTwoSeedExtensionStatement (κ : ℝ) : Prop :=
  ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ),
    IsOrderedForceWord xL xR →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
      (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞) (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens),
      IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h →
      ∀ (hX : IsMeasurableKilledDriving W VL VR ζ) (T : Ω → ℝ≥0)
        (hT : IsStoppingTime (drivingFiltration P hX) fun ω => (T ω : WithTop ℝ≥0)) (G : Set Ω),
        MeasurableSet G → P Gᶜ = 0 → (∀ ω ∈ G, IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω) →
      ∀ (SL : Finset (Fin nL)) (SR : Finset (Fin nR)) (r : ℝ),
        -2 < ∑ i ∈ SL, ρL i → -2 < ∑ j ∈ SR, ρR j →
      ∀ D : Set Ω, MeasurableSet[hT.measurableSpace] D → P D ≠ 0 →
        (∀ ω ∈ D, ω ∈ G ∧ (T ω : ℝ≥0∞) < ζ ω ∧ (∀ i, VL i (T ω) ω = W (T ω) ω ↔ i ∈ SL) ∧
          (∀ j, VR j (T ω) ω = W (T ω) ω ↔ j ∈ SR) ∧ IsSeedRadius (curL VL W T ω) (curR VR W T ω) r) →
      ∀ K : Ω → DrivingHist nL nR, Measurable K →
        (∀ᵐ ω ∂P, ω ∈ D →
          K ω = stoppedHistory (completedState W VL VR ζ) (fun ω => (T ω : WithTop ℝ≥0)) ω) →
        ∃ Q : Measure Ω, IsProbabilityMeasure Q ∧ Q ≪ P.restrict D ∧ P.restrict D ≪ Q ∧
          HasReferenceExtension.{u} κ (∑ i ∈ SL, ρL i) (∑ j ∈ SR, ρR j) r Q (fun ω => (h ω, K ω))
            (fun ω => twoSeedProj (curL VL W T ω) (curR VR W T ω)
              (stoppedHistory (completedState (restartDrv W T) (fun i => restartMark (VL i) W T)
                (fun j => restartMark (VR j) W T) (restartLife ζ T))
                (capStop r G (restartLife ζ T) (restartDrv W T)) ω))

/-! ### Families indexed through the codes -/

section CodeFam

variable {nL nR : ℕ}

open Classical in
/-- The family `i ↦ f c` if `i` encodes a code `c` satisfying `p`, and `d` otherwise. -/
def codeFam {α : Sort*} (p : CellCode nL nR → Prop) (f : CellCode nL nR → α) (d : α) (i : ℕ) : α :=
  (Encodable.decode₂ (CellCode nL nR) i).elim d fun c => if p c then f c else d

theorem codeFam_of_decode₂ {α : Sort*} {p : CellCode nL nR → Prop} {f : CellCode nL nR → α} {d : α} {i : ℕ}
    {c : CellCode nL nR} (hi : Encodable.decode₂ (CellCode nL nR) i = some c) (hc : p c) : codeFam p f d i = f c := by
  classical
  simp only [codeFam, hi, Option.elim_some, hc, ↓reduceIte]

theorem codeFam_of_not {α : Sort*} {p : CellCode nL nR → Prop} {f : CellCode nL nR → α} {d : α} {i : ℕ}
    {c : CellCode nL nR} (hi : Encodable.decode₂ (CellCode nL nR) i = some c) (hc : ¬ p c) : codeFam p f d i = d := by
  classical
  simp only [codeFam, hi, Option.elim_some, hc, ↓reduceIte]

theorem codeFam_of_none {α : Sort*} {p : CellCode nL nR → Prop} {f : CellCode nL nR → α} {d : α} {i : ℕ}
    (hi : Encodable.decode₂ (CellCode nL nR) i = none) : codeFam p f d i = d := by
  simp only [codeFam, hi, Option.elim_none]

theorem codeFam_encode {α : Sort*} {p : CellCode nL nR → Prop} {f : CellCode nL nR → α} {d : α}
    {c : CellCode nL nR} (hc : p c) : codeFam p f d (Encodable.encode c) = f c :=
  codeFam_of_decode₂ (Encodable.decode₂_encode c) hc

/-- Every index encodes an admissible code or gives the default value. -/
theorem codeFam_cases (p : CellCode nL nR → Prop) (i : ℕ) :
    (∃ c, Encodable.decode₂ (CellCode nL nR) i = some c ∧ p c) ∨
      ∀ {α : Sort u} (f : CellCode nL nR → α) (d : α), codeFam p f d i = d := by
  rcases hi : Encodable.decode₂ (CellCode nL nR) i with _ | c
  · exact Or.inr fun f d => codeFam_of_none hi
  · by_cases hc : p c
    · exact Or.inl ⟨c, rfl, hc⟩
    · exact Or.inr fun f d => codeFam_of_not hi hc

end CodeFam

/-! ### Covering and disjointness of the cell events -/

section Cover

variable {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type*} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {τ : Ω → WithTop ℝ≥0} {G : Set Ω}

/-- **Covering**: a good point with `τ < ζ` lies in the cell event of an admissible code. -/
theorem exists_mem_cellEvent (hG : ∀ ω ∈ G, IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω) {ω : Ω} (hω : ω ∈ G)
    (hlt : τ ω < (ζ ω : WithTop ℝ≥0)) :
    ∃ c : CellCode nL nR, IsAdmCode ρL ρR c ∧ ω ∈ cellEvent τ G ζ W VL VR c := by
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_lt hlt)
  have htζ : (t : ℝ≥0∞) < ζ ω := by rw [← ht] at hlt; exact hlt
  have hg := hG ω hω
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hnot, -⟩ := hg.1
  obtain ⟨c, hcN, hc, hcell⟩ := exists_isCellState (ρL := ρL) (ρR := ρR) ⌊t⌋₊
    (x := drivingState W VL VR t ω) (hnot t htζ)
  have h1 : ((c.1 : ℝ≥0) : WithTop ℝ≥0) ≤ τ ω := by
    rw [← ht, hcN]; exact WithTop.coe_le_coe.2 (Nat.floor_le t.coe_nonneg |> fun h => by exact_mod_cast h)
  have h2 : τ ω < (((c.1 + 1 : ℕ) : ℝ≥0) : WithTop ℝ≥0) := by
    rw [← ht, hcN]
    refine WithTop.coe_lt_coe.2 ?_
    have := Nat.lt_floor_add_one t
    exact_mod_cast this
  have hT : cellTime τ c ω = t := WithTop.coe_injective ((coe_cellTime_of_lt h2).trans ht.symm)
  refine ⟨c, hc, hω, h1, h2, by rw [hT]; exact htζ, ?_⟩
  rw [hT, pvState_eq hg htζ]
  exact hcell

/-- **The cell events of distinct codes are disjoint.** -/
theorem cellEvent_disjoint {c c' : CellCode nL nR} (hcc : c ≠ c') :
    Disjoint (cellEvent τ G ζ W VL VR c) (cellEvent τ G ζ W VL VR c') := by
  refine Set.disjoint_left.2 fun ω hω hω' => hcc ?_
  have hN : c.1 = c'.1 := by
    have a1 := hω.2.1
    have a2 := hω.2.2.1
    have b1 := hω'.2.1
    have b2 := hω'.2.2.1
    have h1 : ((c.1 : ℝ≥0) : WithTop ℝ≥0) < (((c'.1 + 1 : ℕ) : ℝ≥0) : WithTop ℝ≥0) := lt_of_le_of_lt a1 b2
    have h2 : ((c'.1 : ℝ≥0) : WithTop ℝ≥0) < (((c.1 + 1 : ℕ) : ℝ≥0) : WithTop ℝ≥0) := lt_of_le_of_lt b1 a2
    have h1' : c.1 < c'.1 + 1 := by exact_mod_cast WithTop.coe_lt_coe.1 h1
    have h2' : c'.1 < c.1 + 1 := by exact_mod_cast WithTop.coe_lt_coe.1 h2
    omega
  have hT : cellTime τ c ω = cellTime τ c' ω :=
    WithTop.coe_injective ((coe_cellTime_of_mem hω).trans (coe_cellTime_of_mem hω').symm)
  have h3 := hω'.2.2.2.2
  rw [← hT] at h3
  exact eq_of_isCellState hN hω.2.2.2.2 h3

/-- With an inadmissible initial seed the lifetime of a good path is `0`. -/
theorem zeta_eq_zero_of_thresholdCondition {ω : Ω} (hg : IsGoodPath κ xL xR ρL ρR W VL VR B ζ ω)
    (hth : ForceWord.ThresholdCondition ρL ρR 0 xL xR) : ζ ω = 0 := by
  by_contra hne
  obtain ⟨hw0, hvL0, hvR0, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hnot, -⟩ := hg.1
  have h := hnot 0 (by simpa using pos_iff_ne_zero.2 hne)
  have eL : (fun i => VL i 0 ω) = xL := funext hvL0
  have eR : (fun i => VR i 0 ω) = xR := funext hvR0
  rw [hw0, eL, eR] at h
  exact h hth

end Cover

/-! ### The restart statement -/

section Main

variable {κ : ℝ}

/-- **The corrected restart statement from the restarted two-seed extension** (Aux. lemmas 53 and 55 at own-filtration
stops): the cells (seed pattern, least dyadic radius, integer part of `τ`), the restarted local stop `σ` (spliced over
the cells) and (R3) at a restart are proved here; the only input is the per-cell extended reference pair recovering
the restarted two-seed history. -/
theorem restartCellExtensionStatement_of_restartTwoSeed (hκ : 0 < κ)
    (hin : RestartTwoSeedExtensionStatement.{u} κ) : RestartCellExtensionStatement.{u} κ := by
  classical
  intro nL nR xL xR ρL ρR hF Ω mΩ P _ 𝓕 W VL VR B ζ h hC hX τ hτ hτζ
  set X := completedState W VL VR ζ with hXdef
  have hcont := ae_continuousOn_completedState hκ hC.1
  have hKae := aemeasurable_stoppedHistory hX hcont hτ.measurable' hτζ
  have hKm : Measurable (hKae.mk _) := hKae.measurable_mk
  have hKeq : hKae.mk _ =ᵐ[P] stoppedHistory X τ := hKae.ae_eq_mk.symm
  set K := hKae.mk _ with hKdef
  obtain ⟨G, hGm, hG0, hG⟩ := exists_goodEvent hC.1 hκ
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := ae_iff.2 hG0
  by_cases hseed : ForceWord.ThresholdCondition ρL ρR 0 xL xR
  · -- an inadmissible initial seed: `ζ = 0` on the good event, so `{τ < ζ}` is null
    have hnull : ∀ᵐ ω ∂P, ¬ τ ω < (ζ ω : WithTop ℝ≥0) := by
      filter_upwards [hGae] with ω hω hlt
      have h0 := zeta_eq_zero_of_thresholdCondition (hG ω hω) hseed
      rw [h0] at hlt
      exact not_lt_bot hlt
    refine ⟨τ, hτ, fun _ => le_rfl, hτζ, hnull.mono fun ω hω h => absurd h hω, K, hKm, hKeq,
      fun _ => ∅, fun _ => 0, fun _ => 0, fun _ => 1, fun _ => MeasurableSet.empty,
      fun _ => ⟨by norm_num, by norm_num⟩, hnull.mono fun ω hω h => absurd h hω, fun _ => Or.inl ?_⟩
    simp only [mem_empty_iff_false, ofPred_false, measure_empty]
  -- the cells, the cell events and the cell stops, indexed through the codes
  set E : ℕ → Set Ω := codeFam (IsAdmCode ρL ρR) (fun c => cellEvent τ G ζ W VL VR c) ∅ with hEdef
  set σs : ℕ → Ω → WithTop ℝ≥0 := codeFam (IsAdmCode ρL ρR) (fun c => cellStop τ G ζ W c) τ with hσsdef
  set σ := spliceTime τ σs E with hσdef
  have hdisj : Pairwise fun i j => Disjoint (E i) (E j) := by
    intro i j hij
    rcases codeFam_cases (IsAdmCode ρL ρR) i with ⟨c, hi, hc⟩ | hi
    · rcases codeFam_cases (IsAdmCode ρL ρR) j with ⟨c', hj, hc'⟩ | hj
      · rw [hEdef, codeFam_of_decode₂ hi hc, codeFam_of_decode₂ hj hc']
        refine cellEvent_disjoint fun hcc => hij ?_
        rw [← Encodable.mem_decode₂.1 hi, ← Encodable.mem_decode₂.1 hj, hcc]
      · rw [hEdef, hj]; exact disjoint_empty _
    · rw [hEdef, hi]; exact empty_disjoint _
  -- on a cell event, `σ` is the cell stop
  have hσc : ∀ c, IsAdmCode ρL ρR c → ∀ ω ∈ cellEvent τ G ζ W VL VR c, σ ω = cellStop τ G ζ W c ω := by
    intro c hc ω hω
    have hωE : ω ∈ E (Encodable.encode c) := by rw [hEdef, codeFam_encode hc]; exact hω
    rw [hσdef, spliceTime_of_mem hdisj hωE, hσsdef, codeFam_encode hc]
  have hEle : ∀ i, ∀ ω ∈ E i, τ ω ≤ σs i ω := by
    intro i ω hω
    rcases codeFam_cases (IsAdmCode ρL ρR) i with ⟨c, hi, hc⟩ | hi
    · rw [hEdef, codeFam_of_decode₂ hi hc] at hω
      rw [hσsdef, codeFam_of_decode₂ hi hc]
      exact (lt_cellStop_and_le hG hω).1.le
    · rw [hEdef, hi] at hω; exact absurd hω (notMem_empty ω)
  have hσst : IsStoppingTime (drivingFiltration P hX) σ := by
    refine isStoppingTime_spliceTime hτ (fun i => ?_) (fun i => ?_) hEle
    · rcases codeFam_cases (IsAdmCode ρL ρR) i with ⟨c, hi, hc⟩ | hi
      · rw [hσsdef, codeFam_of_decode₂ hi hc]
        exact isStoppingTime_cellStop hX hτ hGm hG0 hG c
      · rw [hσsdef, hi]; exact hτ
    · rcases codeFam_cases (IsAdmCode ρL ρR) i with ⟨c, hi, hc⟩ | hi
      · rw [hEdef, codeFam_of_decode₂ hi hc]
        exact IsStoppingTime.measurableSpace_mono (isStoppingTime_cellTime hτ c) hτ (cellTime_le c) _
          (measurableSet_cellEvent hX hτ hGm hG0 c)
      · rw [hEdef, hi]; exact @MeasurableSet.empty Ω hτ.measurableSpace
  -- `τ ≤ σ ≤ ζ`
  have hτσ : ∀ ω, τ ω ≤ σ ω := by
    intro ω
    by_cases hex : ∃ i, ω ∈ E i
    · obtain ⟨i, hi⟩ := hex
      rw [hσdef, spliceTime_of_mem hdisj hi]
      exact hEle i ω hi
    · rw [hσdef, spliceTime_of_forall_notMem fun i hi => hex ⟨i, hi⟩]
  have hσζ : ∀ ω, σ ω ≤ (ζ ω : WithTop ℝ≥0) := by
    intro ω
    by_cases hex : ∃ i, ω ∈ E i
    · obtain ⟨i, hi⟩ := hex
      rcases codeFam_cases (IsAdmCode ρL ρR) i with ⟨c, hic, hc⟩ | hic
      · have hω : ω ∈ cellEvent τ G ζ W VL VR c := by rw [hEdef, codeFam_of_decode₂ hic hc] at hi; exact hi
        rw [hσc c hc ω hω]
        exact (lt_cellStop_and_le hG hω).2
      · rw [hEdef, hic] at hi; exact absurd hi (notMem_empty ω)
    · rw [hσdef, spliceTime_of_forall_notMem fun i hi => hex ⟨i, hi⟩]
      exact hτζ ω
  refine ⟨σ, hσst, hτσ, hσζ, ?_, K, hKm, hKeq, codeFam (IsAdmCode ρL ρR) cellSet ∅,
    codeFam (IsAdmCode ρL ρR) (fun c => ∑ i ∈ c.2.1, ρL i) 0,
    codeFam (IsAdmCode ρL ρR) (fun c => ∑ j ∈ c.2.2.1, ρR j) 0,
    codeFam (IsAdmCode ρL ρR) CellCode.radius 1, fun i => ?_, fun i => ?_, ?_, fun i => ?_⟩
  · -- `τ < σ` on `{τ < ζ}`
    filter_upwards [hGae] with ω hω hlt
    obtain ⟨c, hc, hωc⟩ := exists_mem_cellEvent hG hω hlt
    rw [hσc c hc ω hωc]
    exact (lt_cellStop_and_le hG hωc).1
  · rcases codeFam_cases (IsAdmCode ρL ρR) i with ⟨c, hi, hc⟩ | hi
    · rw [codeFam_of_decode₂ hi hc]; exact measurableSet_cellSet c
    · rw [hi]; exact MeasurableSet.empty
  · rcases codeFam_cases (IsAdmCode ρL ρR) i with ⟨c, hi, hc⟩ | hi
    · rw [codeFam_of_decode₂ hi hc, codeFam_of_decode₂ hi hc]; exact hc
    · rw [hi, hi]; exact ⟨by norm_num, by norm_num⟩
  · -- covering
    filter_upwards [hGae, hKeq] with ω hω hK hlt
    obtain ⟨c, hc, hωc⟩ := exists_mem_cellEvent hG hω hlt
    refine ⟨Encodable.encode c, ?_⟩
    rw [codeFam_encode hc, hK]
    exact (mem_cellSet_iff hseed hG hτζ hc hω).2 hωc
  · -- the extended reference pair on each cell
    rcases codeFam_cases (IsAdmCode ρL ρR) i with ⟨c, hi, hc⟩ | hi
    · simp only [codeFam_of_decode₂ hi hc]
      by_cases hP : P {ω | K ω ∈ cellSet c} = 0
      · exact Or.inl hP
      refine Or.inr ?_
      set D := cellEvent τ G ζ W VL VR c with hDdef
      have hset : {ω | K ω ∈ cellSet c} =ᵐ[P] D := by
        filter_upwards [hGae, hKeq] with ω hω hK
        show (K ω ∈ cellSet c) = (ω ∈ D)
        rw [hK]
        exact propext (mem_cellSet_iff hseed hG hτζ hc hω)
      have hPD : P D ≠ 0 := by rwa [← measure_congr hset]
      have hDm := measurableSet_cellEvent hX hτ hGm hG0 c
      have hDm' : MeasurableSet D := (isStoppingTime_cellTime hτ c).measurableSpace_le _ hDm
      have hDsub : ∀ ω ∈ D, ω ∈ G ∧ (cellTime τ c ω : ℝ≥0∞) < ζ ω ∧
          (∀ i, VL i (cellTime τ c ω) ω = W (cellTime τ c ω) ω ↔ i ∈ c.2.1) ∧
          (∀ j, VR j (cellTime τ c ω) ω = W (cellTime τ c ω) ω ↔ j ∈ c.2.2.1) ∧
          IsSeedRadius (curL VL W (cellTime τ c) ω) (curR VR W (cellTime τ c) ω) c.radius := by
        intro ω hω
        have hcs := isCellState_of_mem hG hω
        exact ⟨hω.1, hω.2.2.2.1, hcs.1, hcs.2.1, isSeedRadius_of_mem hG hω⟩
      have hKT : ∀ᵐ ω ∂P, ω ∈ D →
          K ω = stoppedHistory X (fun ω => (cellTime τ c ω : WithTop ℝ≥0)) ω := by
        filter_upwards [hKeq] with ω hK hω
        rw [hK]
        exact stoppedHistory_congr (coe_cellTime_of_mem hω).symm
      obtain ⟨Q, hQ, hQP, hPQ, hext⟩ := hin xL xR ρL ρR hF P 𝓕 W VL VR B ζ h hC hX (cellTime τ c)
        (isStoppingTime_cellTime hτ c) G hGm hG0 hG c.2.1 c.2.2.1 c.radius hc.1 hc.2 D hDm hPD hDsub K hKm hKT
      refine ⟨Q, hQ, hQP.trans (Measure.absolutelyContinuous_of_le Measure.restrict_le_self), ?_, ?_⟩
      · rw [Measure.restrict_congr_set hset]; exact hPQ
      · -- (R3) at the restart and the concatenation recover `𝒳_σ`
        have hg : Measurable fun p : (LQGMetric.DistOn upperHalfPlaneOpens × DrivingHist nL nR) × TwoSeedHist =>
            concatHist p.1.2 (reindexHist (posL (histState p.1.2)) (posR (histState p.1.2)) c.radius p.2) := by
          have hst : Measurable fun p : (LQGMetric.DistOn upperHalfPlaneOpens × DrivingHist nL nR) × TwoSeedHist =>
              histState p.1.2 := measurable_histState.comp measurable_fst.snd
          have hre := (measurable_reindexHist_pos (nL := nL) (nR := nR) c.radius_pos).comp
            (((measurable_posL.comp hst).prodMk (measurable_posR.comp hst)).prodMk measurable_snd)
          have h2 := measurable_concatHist.comp (measurable_fst.snd.prodMk hre)
          exact h2
        refine hext.of_ae_eq _ hg ?_
        refine hQP.ae_le ((ae_restrict_iff' hDm').2 ?_)
        filter_upwards [hKeq] with ω hK hω
        have hgω := hG ω hω.1
        have hTζ := hω.2.2.2.1
        have hr := isSeedRadius_of_mem hG hω
        have hKω : K ω = stoppedHistory X (fun ω => (cellTime τ c ω : WithTop ℝ≥0)) ω := by
          rw [hK]; exact stoppedHistory_congr (coe_cellTime_of_mem hω).symm
        have hcur : histState (K ω) = drivingState W VL VR (cellTime τ c ω) ω := by
          rw [hKω]; exact histState_stoppedHistory_of_lt rfl hTζ
        rw [stoppedHistory_congr (hσc c hc ω hω)]
        show stoppedHistory X (restartTime (cellTime τ c) (capStop c.radius G (restartLife ζ (cellTime τ c))
          (restartDrv W (cellTime τ c)))) ω = _
        rw [stoppedHistory_restartTime_eq_concatHist hgω hTζ hω.1 hr, ← hKω, hcur]
        exact congrArg (concatHist (K ω)) (reindexHist_twoSeedProj_restart hgω hTζ hω.1 hr).symm
    · refine Or.inl ?_
      rw [hi]
      simp only [mem_empty_iff_false, ofPred_false, measure_empty]

/-- **The conclusion of the frozen Theorem 1.2 for every `κ > 0`** from the two-seed graph input and the restarted
two-seed extension (Aux. lemmas 53 and 55 at own-filtration stops). -/
theorem exists_measurable_lifetime_trace_eq_comp_field_of_restartTwoSeed {nL nR : ℕ} {xL : Fin nL → ℝ}
    {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {Ω : Type u} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
    {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens} (hκ : 0 < κ)
    (h2 : LP.TwoSeedGraphInput.{u} κ) (hin : RestartTwoSeedExtensionStatement.{u} κ)
    (hF : IsOrderedForceWord xL xR) [IsProbabilityMeasure P]
    (hC : IsOptionalHullCoupling κ xL xR ρL ρR P 𝓕 W VL VR B ζ h) :
    ∃ Φ : LQGMetric.DistOn upperHalfPlaneOpens → ℝ≥0∞ × (ℝ≥0 → ℂ), Measurable Φ ∧
      ∀ᵐ ω ∂P, (Φ (h ω)).1 = ζ ω ∧
        ∀ η : ℝ≥0 → ℂ, IsGeneratingTrace (fun t => W t ω) (ζ ω) η →
          ∀ t : ℝ≥0, (Φ (h ω)).2 t = η (min (t : ℝ≥0∞) (ζ ω)).toNNReal :=
  exists_measurable_lifetime_trace_eq_comp_field_of_restartCellExtension hκ h2
    (restartCellExtensionStatement_of_restartTwoSeed hκ hin) hF hC

/-- **Lemma 7.5 with Aux. 52–55** (LP11's input `LP.Lemma75DeterminationStatement`) from Proposition 7.3 and the
restarted two-seed extension for `0 < κ < 4`. -/
theorem lemma75DeterminationStatement_of_restartTwoSeed
    (h73d : Prop73DeterminationStatement.{u}) (h73t : Sec7.Prop73TraceStatement.{u})
    (hin : ∀ κ : ℝ, 0 < κ → κ < 4 → RestartTwoSeedExtensionStatement.{u} κ) :
    LP.Lemma75DeterminationStatement.{u} :=
  lemma75DeterminationStatement_of_restartCellExtension h73d h73t fun κ hκ hκ4 =>
    restartCellExtensionStatement_of_restartTwoSeed hκ (hin κ hκ hκ4)

end Main

end LocalExt

end InteractingSLE
