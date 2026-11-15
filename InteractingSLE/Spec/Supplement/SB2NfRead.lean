/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NfClockL
import InteractingSLE.Spec.Supplement.SB2NdRead

/-!
# F2b′'s root: the canonical driver below the clock, read from the completed line filtration

Packet PROVE-AUX61-NOJUMP (round 22, the root variant). `Nd.measurable_segDrv_line` at the root: below the root clock
at `t` (so after the entrance, which is then frozen), the canonical driver of the root's relative curve is measurable
for the completed line filtration at `t` (**`RootObj.measurable_segDrv_line`**), by `Nd.segDrv_canon_congr` at the
shifted time `t − rSh` (**`RootObj.shift_data_of_frozen`**: the frozen data at `t` give the same entrance, the same
`min (t − rSh) (rLife)` and the same relative piece before it).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal NNRat
open QuantumZipper (H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Nf

open Restart Exist Exist.Staged Exist.StagedLaw Lv Ms Mf WalkSide LocalSets Sec7.PocketTraversal Lk LuM Nc Dv Nd
  Sec7.Lemma71C

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {u : ℝ} {l : List (ℝ × ℝ≥0)} {k ℓ : ℕ}

namespace RootObj

variable (S : RootObj P κ b jumps E u l k ℓ)

theorem a_le_capLife {ω : Ω} (hω : ω ∈ S.Eg) (t : ℝ≥0) : S.a t ω ≤ capLife (S.ρM ω) := by
  rw [S.a_eq hω]
  split_ifs with ht
  · exact ((S.driven_ρM ω).ofReal_capClock_lt (uOf_nonneg (beforeL_of_lt ht))).le
  · exact le_rfl

/-- A positive clock is after the entrance. -/
theorem rSh_lt_of_pos {ω : Ω} {t : ℝ≥0} (ha : 0 < S.a t ω) : rSh κ b jumps E u l k ℓ ω < t := by
  by_contra hle
  rw [not_lt] at hle
  rw [S.a_eq_zero_of_le t hle] at ha
  exact lt_irrefl _ ha

theorem mem_Eg_of_pos {ω : Ω} {t : ℝ≥0} (ha : 0 < S.a t ω) : ω ∈ S.Eg := by
  by_contra hn
  rw [S.a_of_notMem hn] at ha
  exact lt_irrefl _ ha

/-- **The shifted data at two good samples with the same frozen data at `t`, the entrance before `t`.** -/
theorem shift_data_of_frozen (hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length)
    (hwℓ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤)))
    {ω ω₀ : Ω} (hω : ω ∈ S.Eg) (hω₀ : ω₀ ∈ S.Eg) (t : ℝ≥0)
    (e4 : ∀ n, n ≤ ℓ + 1 → ExplState.run κ b jumps
          (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2)) (t : ℝ≥0∞))
          (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω) n =
        ExplState.run κ b jumps
          (capSpec (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) ℓ (-(Real.pi / 2)) (t : ℝ≥0∞))
          (fun j => StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) j ω₀) n)
    (e5 : ω ∈ capEvent κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ t ↔
        ω₀ ∈ capEvent κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
          (StagedReg.regFam E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)) ℓ t)
    (e6 : ∀ q : ℚ≥0, (q : ℝ≥0) ≤ t → (Cm.rootTime κ b jumps E u l k ℓ ω ≤ ((q : ℝ≥0) : ℝ≥0∞) ↔
        Cm.rootTime κ b jumps E u l k ℓ ω₀ ≤ ((q : ℝ≥0) : ℝ≥0∞)))
    (hτt : Nd.entrR κ b jumps E u l k ℓ ω₀ < t) :
    rSh κ b jumps E u l k ℓ ω = rSh κ b jumps E u l k ℓ ω₀ ∧ rSh κ b jumps E u l k ℓ ω₀ ≤ t ∧
      min (((t - rSh κ b jumps E u l k ℓ ω₀ : ℝ≥0)) : ℝ≥0∞) (rLife κ b jumps E u l k ℓ ω) =
        min (((t - rSh κ b jumps E u l k ℓ ω₀ : ℝ≥0)) : ℝ≥0∞) (rLife κ b jumps E u l k ℓ ω₀) ∧
      ∀ s : ℝ≥0, (s : ℝ≥0∞) ≤ min (((t - rSh κ b jumps E u l k ℓ ω₀ : ℝ≥0)) : ℝ≥0∞)
          (rLife κ b jumps E u l k ℓ ω) →
        rPc κ b jumps E u l k ℓ ω s = rPc κ b jumps E u l k ℓ ω₀ s := by
  have G := S.good₀ ω hω.1
  have G₀ := S.good₀ ω₀ hω₀.1
  obtain ⟨htL, hmin, hp⟩ := piece_eq_of_frozen₀ hℓ hwℓ G G₀ t e4 e5
  rw [S.rootTime_eq hω.1, S.rootTime_eq hω₀.1] at e6
  obtain ⟨-, heq⟩ := entr_eq_of_rat e6
  have hττ := heq hτt
  have hτfin : Nd.entrR κ b jumps E u l k ℓ ω₀ ≠ ⊤ := ne_top_of_lt hτt
  have hsh : rSh κ b jumps E u l k ℓ ω = rSh κ b jumps E u l k ℓ ω₀ := by unfold rSh; rw [hττ]
  set sh := rSh κ b jumps E u l k ℓ ω₀ with hshdef
  have hshτ : (sh : ℝ≥0∞) = Nd.entrR κ b jumps E u l k ℓ ω₀ := by rw [hshdef, rSh, ENNReal.coe_toNNReal hτfin]
  have hsht : sh ≤ t := by
    have := hτt.le; rw [← hshτ] at this; exact ENNReal.coe_le_coe.1 this
  have hshL' : (sh : ℝ≥0∞) < bLife b jumps E ℓ ω := by rw [hshτ, ← hττ]; exact S.entr_lt hω
  have hrLife : rLife κ b jumps E u l k ℓ ω = bLife b jumps E ℓ ω - sh := by simp only [rLife, hsh]
  have hrLife₀ : rLife κ b jumps E u l k ℓ ω₀ = bLife b jumps E ℓ ω₀ - sh := rfl
  have hiff : ∀ L : ℝ≥0∞, (((t - sh : ℝ≥0)) : ℝ≥0∞) < L - sh ↔ (t : ℝ≥0∞) < L := fun L => by
    rw [lt_tsub_iff_left, ← ENNReal.coe_add, add_tsub_cancel_of_le hsht]
  refine ⟨hsh, hsht, ?_, fun s hs => ?_⟩
  · rw [hrLife, hrLife₀]
    by_cases htl : (t : ℝ≥0∞) < bLife b jumps E ℓ ω
    · rw [min_eq_left ((hiff _).2 htl).le, min_eq_left ((hiff _).2 (htL.1 htl)).le]
    · have hL : bLife b jumps E ℓ ω = bLife b jumps E ℓ ω₀ := by
        have h1 : min (t : ℝ≥0∞) (bLife b jumps E ℓ ω) = bLife b jumps E ℓ ω := min_eq_right (not_lt.1 htl)
        have h2 : min (t : ℝ≥0∞) (bLife b jumps E ℓ ω₀) = bLife b jumps E ℓ ω₀ :=
          min_eq_right (not_lt.1 fun h' => htl (htL.2 h'))
        rw [← h1, ← h2, hmin]
      rw [hL]
  · have h1 : ((sh + s : ℝ≥0) : ℝ≥0∞) ≤ min (t : ℝ≥0∞) (bLife b jumps E ℓ ω) := by
      rw [hrLife] at hs
      refine le_min ?_ ?_
      · have := hs.trans (min_le_left _ _)
        rw [ENNReal.coe_le_coe] at this ⊢
        exact (le_tsub_iff_left hsht).1 this
      · have := hs.trans (min_le_right _ _)
        rw [ENNReal.coe_add]
        calc (sh : ℝ≥0∞) + s ≤ sh + (bLife b jumps E ℓ ω - sh) := add_le_add le_rfl this
          _ = bLife b jumps E ℓ ω := add_tsub_cancel_of_le hshL'.le
    simp only [rPc, hsh]
    exact hp _ h1

/-- **The canonical driver below the root clock at `t` is measurable for the completed line filtration at `t`.** -/
theorem measurable_segDrv_line (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hE : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → IsStagedHistory κ b jumps P h spec (E spec))
    (hER : ∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 → StagedPiecesRegular κ b jumps P spec (E spec))
    (hlθ : ∀ p ∈ l, p.1 ∈ Ioc (-(Real.pi / 2)) (Real.pi / 2))
    (hℓ : ℓ < (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2.length)
    (hwℓ : (boundaryWalkSpec b jumps (-(Real.pi / 2)) true).2.2[ℓ]? = some (Sum.inl (-(Real.pi / 2), ⊤)))
    (t r : ℝ≥0) :
    Measurable[mΩ ⊓ aeSigma (lineSigmaT κ b jumps E u l k ℓ t) P]
      ((S.Eg ∩ {ω | (r : ℝ≥0∞) < S.a t ω}).indicator fun ω => segDrv (S.ρM ω) r) := by
  classical
  have hm := fun s hs => S.measurable_ρM hb s hs
  have e : ((S.Eg ∩ {ω | (r : ℝ≥0∞) < S.a t ω}).indicator fun ω => segDrv (S.ρM ω) r) =
      (S.Eg ∩ {ω | (r : ℝ≥0∞) < S.a t ω}).indicator (Supp8.GB6.CoordB.drivenDriver S.ρM r) := by
    funext ω
    by_cases hω : ω ∈ S.Eg ∩ {ω | (r : ℝ≥0∞) < S.a t ω}
    · rw [indicator_of_mem hω, indicator_of_mem hω,
        Supp8.GB6.CoordB.drivenDriver_eq (lt_of_lt_of_le hω.2 (S.a_le_capLife hω.1 t))]
      rfl
    · rw [indicator_of_notMem hω, indicator_of_notMem hω]
  have hmeas : Measurable ((S.Eg ∩ {ω | (r : ℝ≥0∞) < S.a t ω}).indicator fun ω => segDrv (S.ρM ω) r) := by
    rw [e]
    exact (Supp8.GB6.CoordB.measurable_drivenDriver S.driven_ρM hm r).indicator
      (S.measurableSet_Eg.inter (measurableSet_lt measurable_const (S.measurable_a hb t)))
  refine measurable_inf_aeSigma_of_frozen (lineSigmaT_le (u := u) (k := k) hb hE hER hlθ hℓ hwℓ t) hmeas ?_
  filter_upwards [S.ae_ae_frozen hb hE hER hlθ hℓ hwℓ t] with ω₀ hfr
  filter_upwards [hfr] with ω ⟨e1, e2, e3, e4, e5, e6⟩
  by_cases hω₀ : ω₀ ∈ S.Eg₀
  · have hω' : ω ∈ S.Eg₀ := e1.2 hω₀
    have ha := S.a_eq_of_frozen hℓ hwℓ hω' hω₀ t e2 e3 e4 e5 e6
    by_cases hr : (r : ℝ≥0∞) < S.a t ω₀
    · have hpos₀ : 0 < S.a t ω₀ := lt_of_le_of_lt zero_le hr
      have hE₀ : ω₀ ∈ S.Eg := S.mem_Eg_of_pos hpos₀
      have hE : ω ∈ S.Eg := S.mem_Eg_of_pos (by rw [ha]; exact hpos₀)
      have hm1 : ω ∈ S.Eg ∩ {ω | (r : ℝ≥0∞) < S.a t ω} := ⟨hE, by rw [mem_ofPred_eq, ha]; exact hr⟩
      have hm0 : ω₀ ∈ S.Eg ∩ {ω | (r : ℝ≥0∞) < S.a t ω} := ⟨hE₀, hr⟩
      rw [indicator_of_mem hm1, indicator_of_mem hm0, S.ρM_eq hE, S.ρM_eq hE₀]
      have hτt : Nd.entrR κ b jumps E u l k ℓ ω₀ < t := by
        have h1 := S.rSh_lt_of_pos hpos₀
        have hfin : Nd.entrR κ b jumps E u l k ℓ ω₀ ≠ ⊤ := (S.entr_lt hE₀).ne_top
        rw [← ENNReal.coe_toNNReal hfin]
        exact ENNReal.coe_lt_coe.2 h1
      obtain ⟨hsh, -, hmin, hp⟩ := S.shift_data_of_frozen hℓ hwℓ hE hE₀ t e4 e5 e6 hτt
      have hd := S.driven_rRel hE
      have hd₀ := S.driven_rRel hE₀
      unfold rRel at hd hd₀ ⊢
      rw [e3] at hd ⊢
      refine segDrv_canon_congr (by rw [e2]) hd hd₀ (S.geo hE).pos _ hmin hp ?_
      rw [ENNReal.ofReal_coe_nnreal]
      have := hm1.2
      rw [mem_ofPred_eq, S.a_eq_shift hE, hsh] at this
      unfold rLift at this
      rwa [e3] at this
    · have hm1 : ω ∉ S.Eg ∩ {ω | (r : ℝ≥0∞) < S.a t ω} := fun h' => hr (by rw [← ha]; exact h'.2)
      have hm0 : ω₀ ∉ S.Eg ∩ {ω | (r : ℝ≥0∞) < S.a t ω} := fun h' => hr h'.2
      rw [indicator_of_notMem hm1, indicator_of_notMem hm0]
  · have hm1 : ω ∉ S.Eg ∩ {ω | (r : ℝ≥0∞) < S.a t ω} := fun h' => hω₀ (e1.1 h'.1.1)
    have hm0 : ω₀ ∉ S.Eg ∩ {ω | (r : ℝ≥0∞) < S.a t ω} := fun h' => hω₀ h'.1.1
    rw [indicator_of_notMem hm1, indicator_of_notMem hm0]

end RootObj

end InteractingSLE.Theorem14.SB.Nf
