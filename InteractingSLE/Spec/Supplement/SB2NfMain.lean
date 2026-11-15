/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NfRVer
import InteractingSLE.Spec.Supplement.SB2NeRoot9E
import InteractingSLE.Spec.Supplement.SB2NeRoot8
import InteractingSLE.Spec.Supplement.SB2NcBase

/-!
# F2b′'s root variant, assembled

Packet PROVE-AUX61-NOJUMP (round 22, the root variant; D48, D51, D57, D63).

* **`sb2LowerRootVersionStatement9E_of_rel`**: `Ne.SB2LowerRootVersionStatement9E` from Theorems 1.2–1.3 and the root's
  relative facts at a sample (`RootRelFactsStatement`, owned by PROVE-T14-SB2LIFT, D77). The objects are the root
  objects (`exists_rootObj`), the versions are `RootStop.versionS` (`exists_rootStop`); the premise of F3's mean
  identity is not used. At a stage that is not a flow instruction the stage event is empty and the trivial versions
  (`trivRootVersionS`) serve;
* `sb2LowerRootVersionStatement8_of_9E`: the projection to `Ne.SB2LowerRootVersionStatement8`;
* `ae_tL_eq_rootEntry`: the version's entrance `tL = entrR.toNNReal` is `Na.rootEntry` on the root's good event
  (D79's reading).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar chiC fwdHull)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Nf

open Restart Restart.DomainMarkov Restart.DomainMarkov.K2 Exist Exist.Staged Exist.StagedLaw WalkSide LocalSets
  WholeField Supp8.Q3Stop Sec7.PocketTraversal Lv Supp9B Lx Lk Mf Ms Nb Nc Nd Vs Supp8.GB6 Supp8.GB6.HullId

/-! ### The trivial root versions on an empty root event -/

section Triv

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {κ ψ : ℝ} {P : Measure Ω} {𝓖 : Filtration ℝ≥0 mΩ}
  {A₁ A₂ : ℝ≥0 → Ω → Set ℂ} {Φ : Ω → Chart} {β₁ : Ω → BoundaryWord} {types : Set WordType} {pc : Ω → ℝ≥0 → ℂ}
  {tL : Ω → ℝ≥0} {L relLife : Ω → ℝ≥0∞}

/-- **The trivial root version**: zero driver, clock and lifetime. -/
def trivRootVersionG : Cr.RootVersionG κ ψ P ∅ 𝓖 A₁ A₂ Φ β₁ types pc tL L where
  𝓗 := lineFiltC P 𝓖
  W := fun _ _ => 0
  a := fun _ _ => 0
  Λ := fun _ _ => 0
  marks_le := le_rfl
  root_meas := @MeasurableSet.empty Ω (lineFiltC P 𝓖 0)
  W_zero := fun _ => rfl
  W_cont := fun _ => continuous_const
  W_adapted := fun _ => stronglyMeasurable_const
  clock_cont := fun _ => continuous_const
  clock_mono := fun _ => monotone_const
  clock_zero := fun _ => rfl
  clock_meas := fun _ => measurable_const
  clock_root := fun _ => Eventually.of_forall fun _ h => absurd h (lt_irrefl _)
  timeChange := fun q D' _ t => by
    have e : D' ∩ {ω | (q : ℝ≥0∞) < (0 : ℝ≥0∞)} = ∅ := by
      ext ω; simp only [mem_inter_iff, mem_ofPred_eq, not_lt_zero, and_false, mem_empty_iff_false]
    rw [e]
    exact @MeasurableSet.empty Ω (lineFiltC P 𝓖 t)
  reach := fun _ _ _ => Eventually.of_forall fun _ h => absurd h Nc.notMem_seedCell_empty
  reg := fun _ _ => Eventually.of_forall fun _ h => absurd h Nc.notMem_seedCell_empty
  safeS := fun _ _ _ t => by
    simp only [lt_self_iff_false, false_and, ofPred_false]; exact @MeasurableSet.empty Ω (lineFiltC P 𝓖 t)
  safeL := fun _ _ _ t => by
    simp only [lt_self_iff_false, false_and, ofPred_false]; exact @MeasurableSet.empty Ω (lineFiltC P 𝓖 t)
  hull := fun _ _ _ => Eventually.of_forall fun _ h => absurd h Nc.notMem_seedCell_empty
  trace := fun _ _ _ => Eventually.of_forall fun _ h => absurd h Nc.notMem_seedCell_empty
  alive := fun _ _ _ => Eventually.of_forall fun _ h => absurd h Nc.notMem_seedCell_empty
  Λ_le := fun _ _ => Eventually.of_forall fun _ h => absurd h Nc.notMem_seedCell_empty

/-- **The trivial root versions at announced stops.** -/
def trivRootVersionS : Cr.RootVersionS κ ψ P ∅ 𝓖 A₁ A₂ Φ β₁ types pc tL L relLife where
  ver := fun _ => trivRootVersionG
  V := fun _ _ => 0
  record := fun _ => (fun _ => 0, 0, true)
  record_meas := fun _ => measurable_const
  ρ := fun _ _ => 0
  ρs := fun _ _ _ => 0
  ρ_meas := fun _ => measurable_const
  ρ_rule := fun _ _ _ _ _ => rfl
  ρs_meas := fun _ _ => measurable_const
  ρs_rule := fun _ _ _ _ _ _ => rfl
  ρs_fin := fun _ _ _ => ENNReal.zero_ne_top
  ρs_mono := fun _ _ => monotone_const
  Λ_eq := fun _ _ => rfl
  V_eq := fun _ _ => rfl
  ann := fun _ => Eventually.of_forall fun _ h => absurd h (notMem_empty _)
  V_lt := fun _ => Eventually.of_forall fun _ h => absurd h (notMem_empty _)
  V_mono := fun _ => monotone_const
  V_sup := Eventually.of_forall fun _ h => absurd h (notMem_empty _)
  W_eq := fun _ _ _ => Eventually.of_forall fun _ h => absurd h (notMem_empty _)

end Triv

/-! ### The root variant -/

/-- **F2b′'s root variant with the offset identity, from Theorems 1.2–1.3 and the root's relative facts.** -/
theorem sb2LowerRootVersionStatement9E_of_rel (hrel : RootRelFactsStatement.{u})
    (h12 : Theorem12Statement.{u}) (h13 : Theorem13Statement.{u})
    (h12₀ : Theorem12Statement.{0}) (h13₀ : Theorem13Statement.{0}) : Ne.SB2LowerRootVersionStatement9E.{u} := by
  intro κ hκ hκ4 b jumps hb Ω mΩ hSB P hP h hh W' ζ' hcf hζ' E hE hER u l k hu hlpair hlθ hleftW hleft ℓ 𝓖 A₁ A₂
    h𝓖 hA β₁ types hβm hsorted htypes u₀ hu₀ hmean hheight
  classical
  by_cases hflow : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length ∧
      (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤))
  · obtain ⟨hℓ, hwℓ⟩ := hflow
    obtain ⟨S⟩ := exists_rootObj h12 h13 h12₀ h13₀ hκ hκ4 hb hh hcf hζ' hE hER hu hlθ k ℓ hleft hℓ hwℓ hu₀
    have h𝓖' : ∀ t, 𝓖 t = lineSigmaT κ b jumps E u l k ℓ t := h𝓖
    have h0 : lineSigma0 κ b jumps E u l k ℓ ≤ mΩ :=
      (lineSigma0_le_T hb hE hER hℓ hwℓ 0).trans (lineSigmaT_le hb hE hER hlθ hℓ hwℓ 0)
    have hC0 : lineC0 P κ b jumps E u l k ℓ ≤ lineFiltC P 𝓖 0 := by
      show mΩ ⊓ aeSigma (lineSigma0 κ b jumps E u l k ℓ) P ≤ mΩ ⊓ aeSigma (𝓖 0) P
      rw [h𝓖' 0]
    have h0C : lineSigma0 κ b jumps E u l k ℓ ≤ lineC0 P κ b jumps E u l k ℓ :=
      le_inf h0 fun s hs => ⟨s, hs, EventuallyEq.rfl⟩
    have hA0 : ∀ᵐ ω ∂P, A₁ 0 ω = stageFill κ b jumps E u l k ℓ ω := (hA 0).mono fun ω hω => hω.1
    refine ⟨S.K, S.x₀, bPc κ b jumps E ℓ, fun ω => Sec7.Lemma71C.capLife (S.ρM ω), S.FB, S.Eg,
      fun n k' => hC0 _ (S.hK n k'), S.hKc, S.hKp, ?_, S.hx₀.mono hC0 le_rfl, hC0 _ (h0C _ S.hFB),
      fun ω => rfl, Eventually.of_forall fun ω hω => (S.geo hω).entry,
      Eventually.of_forall fun ω hω => (S.good₀ ω hω.1).x0, S.hFBae, S.ae_mem_Eg_iff,
      Eventually.of_forall fun ω hω => S.hEg₀FB hω.1, ?_⟩
    · filter_upwards [S.hEg₀ae, hA0] with ω hEg hAω hF
      have hg := S.good₀ ω (hEg hF)
      rw [hg.fill, ← hg.stfill, hAω]
    · intro hcover
      obtain ⟨T, rfl, hcwe, htyp, hend⟩ := exists_rootStop hrel h13₀ hκ hκ4 hb hh hcf hζ' hE hER hlθ hℓ hwℓ S hA0
        hβm htypes hheight hcover
      exact ⟨T.versionS hE hER hlθ hℓ hwℓ h𝓖' hA hcwe types, fun m t => T.ae_a_zero t, fun t => T.ae_cover t,
        fun m w _ => T.ae_V_le_thr hcwe m w, fun w _ Wc hWc => T.toG.ae_thr_le hend hcwe w Wc hWc⟩
  · have hSE := stageEvent_eq_empty (κ := κ) E u l k ℓ hflow
    have hR : Ne.rootEv κ b jumps E u l k ℓ = ∅ :=
      eq_empty_of_forall_notMem fun ω hω => by have := hω.1; rw [hSE] at this; exact this
    refine ⟨fun _ => ∅, fun _ => 0, bPc κ b jumps E ℓ, fun _ => 0, ∅, ∅, fun n k' => by simp,
      fun _ => isCompact_empty, fun _ => by rw [empty_union]; exact Mf.isPreconnected_lowerHalf,
      Eventually.of_forall fun _ h => absurd h (notMem_empty _),
      (measurable_const : Measurable[lineFiltC P 𝓖 0] fun _ : Ω => (0 : ℝ)),
      @MeasurableSet.empty Ω (lineFiltC P 𝓖 0), fun _ => rfl,
      Eventually.of_forall fun _ h => absurd h (notMem_empty _),
      Eventually.of_forall fun _ h => absurd h (notMem_empty _),
      Eventually.of_forall fun ω => ?_, Eventually.of_forall fun ω => ?_,
      Eventually.of_forall fun _ h => absurd h (notMem_empty _), fun _ => ⟨trivRootVersionS, ?_, ?_, ?_, ?_⟩⟩
    · rw [hSE]; simp
    · rw [hR]
    · exact fun _ _ => Eventually.of_forall fun _ h => absurd h (notMem_empty _)
    · exact fun _ => Eventually.of_forall fun _ h => absurd h (notMem_empty _)
    · exact fun _ _ _ => Eventually.of_forall fun _ h => absurd h.1 (notMem_empty _)
    · exact fun _ _ _ _ => Eventually.of_forall fun _ h => absurd h Nc.notMem_seedCell_empty

/-- **Statement9E gives Statement8.** -/
theorem sb2LowerRootVersionStatement8_of_9E (h9 : Ne.SB2LowerRootVersionStatement9E.{u}) :
    Ne.SB2LowerRootVersionStatement8.{u} := by
  intro κ hκ hκ4 b jumps hb Ω mΩ hSB P hP h hh W' ζ' hcf hζ' E hE hER u l k hu hpair hlθ hlw hleft ℓ 𝓖 A₁ A₂ h𝓖 hA
    β₁ types hβm hsort htypes u₀ hu₀ hmean hheight
  obtain ⟨K, x₀, pc, relLife, FB, Fr, c1, c2, c3, c4, c5, c6, -, -, -, c8, c9, c10, c11⟩ :=
    h9 κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hER u l k hu hpair hlθ hlw hleft ℓ 𝓖 A₁ A₂ h𝓖 hA β₁ types
      hβm hsort htypes u₀ hu₀ hmean hheight
  exact ⟨K, x₀, pc, relLife, FB, Fr, c1, c2, c3, c4, c5, c6, c8, c9, c10, c11⟩

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {u : ℝ}
  {l : List (ℝ × ℝ≥0)} {k ℓ : ℕ}

/-- **The version's entrance is `Na.rootEntry` on the root event** (D79): there B's piece visits `R`, so the entrance
with the stopping convention is the first visit. -/
theorem tL_eq_rootEntry {ω : Ω} (hω : ω ∈ Ne.rootEv κ b jumps E u l k ℓ) :
    (Nd.entrR κ b jumps E u l k ℓ ω).toNNReal = Na.rootEntry κ b jumps E u l k ℓ ω := by
  classical
  have hvis : ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 ∧
      pcPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
        (fun i => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) i ω) ℓ)
        (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω) t =
          ((realMax (upperPrefix κ b jumps E u l k ω) : ℝ) : ℂ) := by
    by_contra hno
    have h1 : Nd.entrR κ b jumps E u l k ℓ ω = (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ ω).2 :=
      Ck.entrTime_eq_life hno
    have := hω.2.2.2
    rw [h1] at this
    exact lt_irrefl _ this
  unfold Nd.entrR
  rw [Ck.entrTime_eq_visitTime hvis]
  rfl

end InteractingSLE.Theorem14.SB.Nf
