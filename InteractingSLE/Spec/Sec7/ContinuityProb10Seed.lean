import InteractingSLE.Spec.Sec7.ContinuityProb10Stop
import InteractingSLE.Spec.Sec7.ContinuityProb10Retarget
import InteractingSLE.Spec.Sec7.ContinuityProb10Close

/-!
# LP9's two-sided seed: the trace of the retargeted driver (`Sec7.LP9SeedTraceStatement`), proved

Packet PROVE-TRACECLOSE. When an original left mark and an original right mark before the target both sit at the seed,
LP9's transformed word has marks `0` on both sides and the separated R5 (`Sec2.IsSLEEvolutionUpTo.ae_trace_of_complete`)
does not apply. Here:

* the retargeted local evolution comes with an announcing sequence `S_n` of its horizon
  (`Zhan.Retarget.exists_retarget_evolution_of_seed_stop`);
* its first positive member `T = firstPos S` is a positive stopping time, almost surely before the horizon
  (`firstPos_lt`), at which the word seen from the driver is good (`goodWord_of_isSLEPathUpTo`: a positive time before
  the horizon separates the sides, `Sec2.vL_lt_vR_of_pos`, and a local path has no threshold);
* `SeedStop.ae_trace_of_complete_of_stop` then gives the trace up to the horizon.

An inadmissible original seed makes the lifetime, hence the horizon, `0`, and the trace is trivial.

## Main results

* `Sec7.lp9SeedTraceStatement : LP9SeedTraceStatement κ` for every `κ > 0`;
* `Sec7.lp9PrefixStatement : LP9PrefixStatement κ` for every `κ > 0` (Theorem 1.3's LP9 input, unconditionally).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Sec7

open Zhan.Retarget Sec2 Sec2.Assembly2

/-! ### The first positive time of a sequence -/

section FirstPos

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

open Classical in
/-- The first positive member of a sequence of times (`1` if there is none). -/
def firstPos (S : ℕ → Ω → ℝ≥0) (ω : Ω) : ℝ≥0 :=
  if h : ∃ n, 0 < S n ω then S (Nat.find h) ω else 1

theorem firstPos_pos (S : ℕ → Ω → ℝ≥0) (ω : Ω) : 0 < firstPos S ω := by
  classical
  unfold firstPos
  split_ifs with h
  · exact Nat.find_spec h
  · exact one_pos

theorem firstPos_eq {S : ℕ → Ω → ℝ≥0} {ω : Ω} (h : ∃ n, 0 < S n ω) :
    firstPos S ω = S (Nat.find h) ω := by
  classical
  simp only [firstPos, h, ↓reduceDIte]

/-- The first positive member of a sequence of stopping times is a stopping time. -/
theorem isStoppingTime_firstPos {𝓕 : Filtration ℝ≥0 mΩ} {S : ℕ → Ω → ℝ≥0}
    (hS : ∀ n, IsStoppingTime 𝓕 fun ω => (S n ω : WithTop ℝ≥0)) :
    IsStoppingTime 𝓕 fun ω => (firstPos S ω : WithTop ℝ≥0) := by
  classical
  intro u
  have hz : ∀ k, MeasurableSet[𝓕 u] {ω | S k ω ≤ 0} := fun k => by
    have h := 𝓕.mono (zero_le (a := u)) _ (hS k 0)
    convert h using 1
    ext ω
    simp only [mem_ofPred_eq, WithTop.coe_le_coe]
  have hle : ∀ k, MeasurableSet[𝓕 u] {ω | S k ω ≤ u} := fun k => by
    convert hS k u using 1
    ext ω
    simp only [mem_ofPred_eq, WithTop.coe_le_coe]
  have e : {ω | (firstPos S ω : WithTop ℝ≥0) ≤ u} =
      (⋃ n, ((⋂ k, ⋂ (_ : k < n), {ω | S k ω ≤ 0}) ∩ ({ω | S n ω ≤ u} \ {ω | S n ω ≤ 0}))) ∪
        ((⋂ k, {ω | S k ω ≤ 0}) ∩ {_ω | (1 : ℝ≥0) ≤ u}) := by
    ext ω
    simp only [mem_ofPred_eq, mem_union, mem_iUnion, mem_inter_iff, mem_iInter, Set.mem_sdiff, WithTop.coe_le_coe]
    by_cases h : ∃ n, 0 < S n ω
    · rw [firstPos_eq h]
      have hn : ¬ ∀ k, S k ω ≤ 0 := fun hall => by
        obtain ⟨n, hn⟩ := h
        exact absurd (hall n) (not_le.2 hn)
      constructor
      · intro hu
        refine Or.inl ⟨Nat.find h, fun k hk => not_lt.1 (Nat.find_min h hk), hu, not_le.2 (Nat.find_spec h)⟩
      · rintro (⟨n, hk, hu, hpos⟩ | ⟨hall, -⟩)
        · have hpos' : 0 < S n ω := not_le.1 hpos
          have h1 : Nat.find h ≤ n := Nat.find_min' h hpos'
          have h2 : n ≤ Nat.find h := by
            by_contra hlt
            exact absurd (hk _ (not_le.1 hlt)) (not_le.2 (Nat.find_spec h))
          rwa [le_antisymm h1 h2]
        · exact absurd hall hn
    · have hall : ∀ k, S k ω ≤ 0 := fun k => not_lt.1 fun hk => h ⟨k, hk⟩
      have e1 : firstPos S ω = 1 := by simp only [firstPos, h, ↓reduceDIte]
      rw [e1]
      constructor
      · exact fun hu => Or.inr ⟨hall, hu⟩
      · rintro (⟨n, -, -, hpos⟩ | ⟨-, hu⟩)
        · exact absurd (hall n) hpos
        · exact hu
  rw [e]
  refine (MeasurableSet.iUnion fun n => ?_).union ((MeasurableSet.iInter hz).inter (MeasurableSet.const _))
  exact (MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ => hz k).inter ((hle n).diff (hz n))

/-- An announcing sequence of a horizon `τ` (before `τ`, exhausting it) has its first positive member before `τ`. -/
theorem firstPos_lt {S : ℕ → Ω → ℝ≥0} {τ : Ω → ℝ≥0∞} {ω : Ω} (hlt : ∀ n, (S n ω : ℝ≥0∞) < τ ω)
    (hex : ∀ r : ℝ≥0, (r : ℝ≥0∞) < τ ω → ∃ n, r ≤ S n ω) : (firstPos S ω : ℝ≥0∞) < τ ω := by
  by_cases h : ∃ n, 0 < S n ω
  · rw [firstPos_eq h]; exact hlt _
  · exfalso
    have hpos : (0 : ℝ≥0∞) < τ ω := lt_of_le_of_lt zero_le (hlt 0)
    obtain ⟨r, hr0, hrτ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hpos
    obtain ⟨n, hn⟩ := hex r hrτ
    exact h ⟨n, lt_of_lt_of_le (by exact_mod_cast hr0) hn⟩

end FirstPos

/-! ### A good word at a positive time before the horizon -/

/-- **At a positive time before its horizon, a local solution of an ordered word sees a good word**: the sides are
separated (`vL_lt_vR_of_pos`), the word is ordered, and a local path has no threshold. -/
theorem goodWord_of_isSLEPathUpTo {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ}
    {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {τ : ℝ≥0∞}
    (hp : IsSLEPathUpTo a xL xR ρL ρR w vL vR b τ) (hF : IsOrderedForceWord xL xR) {t : ℝ≥0} (ht0 : 0 < t)
    (ht : (t : ℝ≥0∞) < τ) : GoodWord ρL ρR (fun i => vL i t - w t, fun j => vR j t - w t) := by
  refine ⟨fun i j => sub_lt_sub_right (hp.vL_lt_vR_of_pos hF ht0 ht i j) _,
    ⟨fun i k hik => sub_le_sub_right (hp.antitone_vL ht hik) _, fun i => sub_nonpos.2 (hp.vL_le_w ht i),
      fun i k hik => sub_le_sub_right (hp.monotone_vR ht hik) _, fun j => sub_nonneg.2 (hp.w_le_vR ht j)⟩, ?_⟩
  intro hthr
  apply hp.not_threshold ht
  rw [← ForceWord.thresholdCondition_sub_iff ρL ρR (w t) (w t), sub_self]
  exact hthr

/-! ### LP9 at a two-sided seed -/

/-- **LP9's two-sided seed** (the named input of PROVE-SEC7-C10), proved for every `κ > 0`. -/
theorem lp9SeedTraceStatement {κ : ℝ} (hκ : 0 < κ) : LP9SeedTraceStatement.{u} κ := by
  intro nL j m xL xR ρL ρR hD hj _ hcT Ω mΩ P _ 𝓕 W VL VR B ζ hE
  by_cases hthr : ForceWord.ThresholdCondition ρL ρR 0 xL xR
  · -- an inadmissible seed: the lifetime, hence the horizon, is `0`
    have hζ0 : ∀ᵐ ω ∂P, ζ ω = 0 := by
      filter_upwards [hE.2.2.2.2] with ω hp
      by_contra hne
      have hpos : ((0 : ℝ≥0) : ℝ≥0∞) < ζ ω := by
        rw [ENNReal.coe_zero]; exact pos_iff_ne_zero.2 hne
      have hu := hp.isSLEPathUpTo le_rfl
      have h := hu.not_threshold hpos
      have e1 : (fun i => VL i 0 ω) = xL := funext hu.vL_zero
      have e2 : (fun i => VR i 0 ω) = xR := funext hu.vR_zero
      have e0 : W 0 ω = 0 := hu.w_zero
      simp only [e0] at h
      rw [e1, e2] at h
      exact h hthr
    filter_upwards [hζ0] with ω hω
    have h0 : newHorizon (LP.retargetPos xR) (fun t => W t ω) (fun t => VR (LP.retargetIdx j m) t ω)
        (sepTime (fun t => W t ω) (fun t => VR (LP.retargetIdx j m) t ω) (ζ ω)) = 0 := by
      simp only [sepTime, hω, zero_le, min_eq_left, newHorizon_zero]
    rw [h0]
    exact ⟨fun _ => 0, ⟨rfl, continuousOn_const, fun t ht => absurd ht (not_lt.2 zero_le)⟩,
      fun h => absurd h ENNReal.zero_ne_top⟩
  -- an admissible seed: the retargeted local evolution and its first positive localizing time
  obtain ⟨𝓘, β, τ, -, hτ, hloc, S, hSst, hSae⟩ := exists_retarget_evolution_of_seed_stop hκ hD hj hE hthr
  have hF := (LP.isDistinctForceWord_retarget hD hj).1
  have hTst : IsStoppingTime (usualAugmentation 𝓘 (P.prod P))
      fun p : Ω × Ω => (firstPos (fun n (q : Ω × Ω) => S n q.1) p : WithTop ℝ≥0) :=
    fun t => Ito.le_usualAugmentation 𝓘 (P.prod P) t _ (isStoppingTime_firstPos hSst t)
  have hT0 : ∀ p : Ω × Ω, 0 < firstPos (fun n (q : Ω × Ω) => S n q.1) p := fun p => firstPos_pos _ p
  have hTτ : ∀ᵐ p ∂(P.prod P), (firstPos (fun n (q : Ω × Ω) => S n q.1) p : ℝ≥0∞) < τ p.1 := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := P) (ν := P)).ae hSae] with p hp
    exact firstPos_lt (S := fun n (q : Ω × Ω) => S n q.1) (τ := fun q => τ q.1) hp.1 hp.2
  have hgood : ∀ᵐ p ∂(P.prod P), GoodWord (LP.retargetρL κ ρL ρR) (LP.retargetρR ρR)
      (contWord (fun u p => newW xR (fun t => W t p.1) (fun i t => VR i t p.1) u)
        (fun i u p => newVL xR (fun t => W t p.1) (fun i t => VL i t p.1) (fun i t => VR i t p.1) i u)
        (fun i u p => newVR xR (fun t => W t p.1) (fun i t => VR i t p.1) i u)
        (firstPos (fun n (q : Ω × Ω) => S n q.1)) p) := by
    filter_upwards [hloc.ae_path, hTτ] with p hp hpτ
    exact goodWord_of_isSLEPathUpTo hp hF (hT0 p) hpτ
  have htr := SeedStop.ae_trace_of_complete_of_stop hκ hloc hcT hTst hT0 hTτ hgood
  have hτ' := (Measure.quasiMeasurePreserving_fst (μ := P) (ν := P)).ae hτ
  refine ae_of_ae_prod_fst (Φ := fun ω => ∃ η : ℝ≥0 → ℂ,
      IsGeneratingTrace (newW xR (fun t => W t ω) (fun i t => VR i t ω))
        (newHorizon (LP.retargetPos xR) (fun t => W t ω) (fun t => VR (LP.retargetIdx j m) t ω)
          (sepTime (fun t => W t ω) (fun t => VR (LP.retargetIdx j m) t ω) (ζ ω))) η ∧
      (newHorizon (LP.retargetPos xR) (fun t => W t ω) (fun t => VR (LP.retargetIdx j m) t ω)
          (sepTime (fun t => W t ω) (fun t => VR (LP.retargetIdx j m) t ω) (ζ ω)) = ⊤ →
        Tendsto (fun t => ‖η t‖) atTop atTop)) ?_
  filter_upwards [htr, hτ'] with p hp hτp
  rw [← hτp]
  exact hp

/-- **Theorem 1.3's LP9 input**, `LP9PrefixStatement κ`, for every `κ > 0` (no named input left). -/
theorem lp9PrefixStatement {κ : ℝ} (hκ : 0 < κ) : LP9PrefixStatement.{u} κ :=
  lp9PrefixStatement_of_seed hκ (lp9SeedTraceStatement hκ)

end Sec7

end InteractingSLE
