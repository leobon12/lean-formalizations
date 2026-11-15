/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2NfObj
import InteractingSLE.Spec.Supplement.SB2NcClockP
import InteractingSLE.Spec.Supplement.SB2NcRhoM

/-!
# F2b′'s root: the relative curve and the clock in B's time, as processes

Packet PROVE-AUX61-NOJUMP (round 22, the root variant). For F2b′'s root objects `S` (`RootObj`):

* `measurable_canonCurve_rand` (generic; `Nc.measurable_bRel`'s proof for any piece read at measurable times): a
  canonical curve driven on a measurable event is measurable at every time;
* `S.ρM`: the root's relative curve on the good event `S.Eg`, the vertical ray off it — driven at every sample and
  measurable at every time (**`measurable_ρM`**);
* `S.a`: the relative clock in B's time, `Vc.clockOf (rLift) (rSh) (bLife)` on `S.Eg` (entrance `rSh`), `0` off it;
  `clockOf_shift`: it is the tail clock of the relative piece at `t − rSh` (**`a_eq_shift`**), hence continuous,
  monotone, `0` up to the entrance (**`a_eq_zero_of_le`**), equal to `capClock ρ (uOf (t − rSh))` before the
  lifetime and `capLife ρ` after (**`a_eq`**), and measurable (**`measurable_a`**).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

universe u

namespace InteractingSLE.Theorem14.SB.Nf

open Sec7.PocketTraversal Sec7.Lemma71C Dv Lk Exist Exist.Staged Exist.StagedLaw LuM GW1W GW1Bookkeep Restart Nc

/-! ### A canonical curve read at measurable times -/

open Classical in
/-- **A canonical curve, driven on a measurable event, is measurable at every time** (`Nc.measurable_bRel` for a
piece whose values at the reparametrized rational times are measurable). -/
theorem measurable_canonCurve_rand {Ω : Type*} [MeasurableSpace Ω] {K : Ω → Set ℂ} (hK : IsDyadicHitMeasurable K)
    (hKc : ∀ ω, IsCompact (K ω)) (hKp : ∀ ω, IsPreconnected (K ω ∪ lowerHalf)) {x₀ : Ω → ℝ} (hx₀ : Measurable x₀)
    {p : Ω → ℝ≥0 → ℂ} {L : Ω → ℝ≥0∞} {M : Set Ω} (hM : MeasurableSet M)
    (hzm : ∀ i : ℕ, Measurable fun ω => if ω ∈ M then p ω (cTime (L ω) (ratPt i : ℝ)) else 0)
    (hpc : ∀ ω ∈ M, ContinuousOn (p ω) {t : ℝ≥0 | (t : ℝ≥0∞) ≤ L ω}) (hL0 : ∀ ω ∈ M, L ω ≠ 0)
    (hMd : ∀ ω ∈ M, IsDrivenCurve (canonCurve (K ω) (x₀ ω) (p ω) (L ω))) (r : ℝ) (hr : 0 ≤ r) :
    Measurable fun ω => if ω ∈ M then canonCurve (K ω) (x₀ ω) (p ω) (L ω) r else 0 := by
  classical
  set zq : ℕ → Ω → ℂ := fun i ω => if ω ∈ M then p ω (cTime (L ω) (ratPt i : ℝ)) else 0 with hzq
  have hzqm : ∀ i, Measurable (zq i) := hzm
  set good : ℕ → Ω → Prop := fun i ω => ω ∈ M ∧ zq i ω ∈ H \ fillH (K ω) with hgood
  have hgoodm : ∀ i, MeasurableSet {ω | good i ω} := fun i =>
    hM.inter (measurableSet_mem_H_diff_fillH_rand hK hKc (hzqm i))
  set V : ℕ → Ω → ℂ := fun i => {ω | zq i ω ∈ H \ fillH (K ω)}.indicator
    fun ω => (Mo.hullChart (fillH (K ω)) (x₀ ω)).1 (zq i ω) with hV
  have hVm : ∀ i, Measurable (V i) := fun i => measurable_indicator_hullChart_rand hK hKc hKp hx₀ (hzqm i)
  have h := Lk.measurable_of_dense_good (ρ := fun ω (s : ℝ≥0) => canonCurve (K ω) (x₀ ω) (p ω) (L ω) s) hgoodm
    hVm hM (fun ω hω => (hMd ω hω).continuousOn.comp_continuous NNReal.continuous_coe fun s => s.2) ?_ ?_
    r.toNNReal
  · simp only [Real.coe_toNNReal _ hr] at h
    exact h
  · intro ω hω i hi
    have hzi : zq i ω = p ω (cTime (L ω) (ratPt i : ℝ)) := by simp only [hzq, hω, ↓reduceIte]
    show canonCurve (K ω) (x₀ ω) (p ω) (L ω) (ratPt i) = V i ω
    rw [canonCurve_eq]
    have hg : cTime (L ω) (ratPt i : ℝ) ∈ canonGood (K ω) (p ω) (L ω) :=
      ⟨cTime_le_any (NNReal.coe_nonneg _), hzi ▸ hi.2⟩
    unfold canonVal
    simp only [hg, ↓reduceIte, hV]
    rw [indicator_of_mem (show ω ∈ {ω | zq i ω ∈ H \ fillH (K ω)} from hi.2), hzi]
  · intro ω hω t ε hε
    have hXo : IsOpen (H \ fillH (K ω)) := isOpen_H_diff_fillH (hKc ω).isBounded
    obtain ⟨q, hq0, hqd, hqg⟩ := exists_rat_good hXo (hL0 ω hω) (hpc ω hω) (hMd ω hω) t hε
    obtain ⟨i, hi⟩ := Nv.exists_ofNat_eq q
    have hri : ratPt i = (q : ℝ).toNNReal := by rw [Nv.ratPt_eq_ofNat, hi]
    refine ⟨i, ⟨hω, ?_⟩, by rw [hri]; exact hqd⟩
    have hzi : zq i ω = p ω (cTime (L ω) (ratPt i : ℝ)) := by simp only [hzq, hω, ↓reduceIte]
    rw [hzi, hri]
    exact hqg.2

/-! ### The clock with an entrance -/

/-- **The clock with entrance `sh` is the clock from `0` of the lift, at `t − sh`.** -/
theorem clockOf_shift (γ : ℝ≥0 → ℂ) (sh : ℝ≥0) (L : ℝ≥0∞) {t : ℝ≥0} (ht : sh ≤ t) :
    Vc.clockOf γ sh L t = Vc.clockOf γ 0 (L - sh) (t - sh) := by
  unfold Vc.clockOf
  refine le_antisymm (iSup₂_le fun s hs => iSup_le fun hL => ?_) (iSup₂_le fun s hs => iSup_le fun hL => ?_)
  · refine le_iSup₂_of_le (f := fun (s : ℝ≥0) (_ : 0 + s ≤ t - sh) => ⨆ (_ : ((0 + s : ℝ≥0) : ℝ≥0∞) < L - sh),
      ENNReal.ofReal (capClock (fun r : ℝ => γ r.toNNReal) s)) s ?_ ?_
    · rw [zero_add]; exact le_tsub_of_add_le_left hs
    · refine le_iSup_of_le ?_ le_rfl
      rw [zero_add]
      rw [ENNReal.coe_add] at hL
      exact lt_tsub_iff_left.2 hL
  · refine le_iSup₂_of_le (f := fun (s : ℝ≥0) (_ : sh + s ≤ t) => ⨆ (_ : ((sh + s : ℝ≥0) : ℝ≥0∞) < L),
      ENNReal.ofReal (capClock (fun r : ℝ => γ r.toNNReal) s)) s ?_ ?_
    · rw [zero_add] at hs; exact (le_tsub_iff_left ht).1 hs
    · refine le_iSup_of_le ?_ le_rfl
      rw [zero_add] at hL
      rw [ENNReal.coe_add]
      exact lt_tsub_iff_left.1 hL

/-- The tail clock of a driven canonical curve vanishes at `0`. -/
theorem clockOf_canonVal_zero {X : Set ℂ} {x₀ : ℝ} {p : ℝ≥0 → ℂ} {L : ℝ≥0∞}
    (hd : IsDrivenCurve (canonCurve X x₀ p L)) (hL : L ≠ 0) : Vc.clockOf (canonVal X x₀ p L) 0 L 0 = 0 := by
  rw [clockOf_canonVal hd hL]
  have h0 : ((0 : ℝ≥0) : ℝ≥0∞) < L := by rw [ENNReal.coe_zero]; exact pos_iff_ne_zero.2 hL
  simp only [h0, ↓reduceIte, NNReal.coe_zero, uOf_zero, hd.capClock_zero, ENNReal.ofReal_zero]

/-- **The clock with entrance of a driven canonical curve, at every time.** -/
theorem clockOf_shift_canon {X : Set ℂ} {x₀ : ℝ} {p : ℝ≥0 → ℂ} {L : ℝ≥0∞}
    (hd : IsDrivenCurve (canonCurve X x₀ p (L - (0 : ℝ≥0∞)))) (sh : ℝ≥0) (L₁ : ℝ≥0∞) (hL : L₁ - sh = L)
    (hL0 : L ≠ 0) (t : ℝ≥0) :
    Vc.clockOf (canonVal X x₀ p L) sh L₁ t = Vc.clockOf (canonVal X x₀ p L) 0 L (t - sh) := by
  rw [tsub_zero] at hd
  rcases le_total sh t with ht | ht
  · rw [clockOf_shift _ _ _ ht, hL]
  · rw [tsub_eq_zero_of_le ht, clockOf_canonVal_zero hd hL0]
    rcases ht.lt_or_eq with hlt | heq
    · exact Vc.clockOf_eq_zero_of_lt hlt
    · rw [heq, clockOf_shift _ _ _ le_rfl, tsub_self, hL, clockOf_canonVal_zero hd hL0]

/-! ### The root's relative curve and clock -/

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {u : ℝ}
  {l : List (ℝ × ℝ≥0)} {k ℓ : ℕ}

namespace RootObj

variable (S : RootObj P κ b jumps E u l k ℓ)

/-- The measurable entrance shift. -/
def rShM (ω : Ω) : ℝ≥0 := (S.shM ω).toNNReal

theorem measurable_rShM : Measurable S.rShM := ENNReal.measurable_toNNReal.comp S.hshM

theorem rSh_eq {ω : Ω} (hω : ω ∈ S.Eg) : rSh κ b jumps E u l k ℓ ω = S.rShM ω := by
  unfold rSh rShM; rw [S.shM_eq ω hω.1]

theorem bLife_eq {ω : Ω} (hω : ω ∈ S.Eg) : bLife b jumps E ℓ ω = (S.Ê ℓ ω).2 := (S.good₀ ω hω.1).agree.2.1 ℓ

theorem bPc_eq {ω : Ω} (hω : ω ∈ S.Eg) :
    bPc κ b jumps E ℓ ω = pcPt (wRun κ (-(Real.pi / 2)) b jumps (fun j => S.Ê j ω) ℓ) (S.Ê ℓ ω) := by
  have hag := (S.good₀ ω hω.1).agree
  have hl := (S.good₀ ω hω.1).stage.2
  unfold bPc
  rw [Nv.pcPt_congr _ (hag.2.2 ℓ hl), hag.1 ℓ]

theorem launch_Ê {ω : Ω} (hω : ω ∈ S.Eg) :
    (wRun κ (-(Real.pi / 2)) b jumps (fun j => S.Ê j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none := by
  have hl := (S.good₀ ω hω.1).stage.2
  rw [show wRun κ (-(Real.pi / 2)) b jumps (fun j => S.Ê j ω) (ℓ + 1) = _ from
    ((S.good₀ ω hω.1).agree.1 (ℓ + 1)).symm]
  exact hl

/-- The relative piece through the regular version. -/
def pÊ (ω : Ω) : ℝ≥0 → ℂ :=
  fun t => pcPt (wRun κ (-(Real.pi / 2)) b jumps (fun j => S.Ê j ω) ℓ) (S.Ê ℓ ω) (S.rShM ω + t)

/-- Its lifetime. -/
def LÊ (ω : Ω) : ℝ≥0∞ := (S.Ê ℓ ω).2 - S.rShM ω

theorem measurable_LÊ : Measurable S.LÊ :=
  (measurable_snd.comp (S.hÊm ℓ)).sub (measurable_coe_nnreal_ennreal.comp S.measurable_rShM)

theorem rPc_eq {ω : Ω} (hω : ω ∈ S.Eg) : rPc κ b jumps E u l k ℓ ω = S.pÊ ω := by
  funext t; simp only [rPc, pÊ, S.bPc_eq hω, S.rSh_eq hω]

theorem rLife_eq {ω : Ω} (hω : ω ∈ S.Eg) : rLife κ b jumps E u l k ℓ ω = S.LÊ ω := by
  simp only [rLife, LÊ, S.bLife_eq hω, S.rSh_eq hω]

theorem driven_rRel {ω : Ω} (hω : ω ∈ S.Eg) : IsDrivenCurve (rRel κ b jumps E u l k ℓ S.K S.x₀ ω) := by
  unfold rRel
  rw [canonCurve_congr_fill (S.good₀ ω hω.1).fill]
  exact (S.geo hω).driven

open Classical in
/-- The root's relative curve on the good event, the vertical ray off it. -/
def ρM (ω : Ω) : ℝ → ℂ :=
  if ω ∈ S.Eg then rRel κ b jumps E u l k ℓ S.K S.x₀ ω else fun t : ℝ => (t : ℂ) * Complex.I

theorem ρM_eq {ω : Ω} (hω : ω ∈ S.Eg) : S.ρM ω = rRel κ b jumps E u l k ℓ S.K S.x₀ ω := by
  simp only [ρM, hω, ↓reduceIte]

theorem driven_ρM (ω : Ω) : IsDrivenCurve (S.ρM ω) := by
  by_cases hω : ω ∈ S.Eg
  · rw [S.ρM_eq hω]; exact S.driven_rRel hω
  · simp only [ρM, hω, ↓reduceIte]; exact isDrivenCurve_vert

theorem measurable_ρM (hb : IsPiecewiseConstantBoundaryData b jumps) (r : ℝ) (hr : 0 ≤ r) :
    Measurable fun ω => S.ρM ω r := by
  classical
  set θ : ℝ := -(Real.pi / 2) with hθ
  have hKm : Restart.IsDyadicHitMeasurable S.K := fun n q => (S.hK n q).1
  set LS : Set Ω := {ω | (wRun κ θ b jumps (fun j => S.Ê j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none} with hLS
  have hzm : ∀ i : ℕ, Measurable fun ω => if ω ∈ S.Eg then S.pÊ ω (cTime (S.LÊ ω) (ratPt i : ℝ)) else 0 := by
    intro i
    set σ : Ω → ℝ≥0 := fun ω => if (S.rShM ω : ℝ≥0∞) ≤ (S.Ê ℓ ω).2 then
      S.rShM ω + cTime (S.LÊ ω) (ratPt i : ℝ) else 0 with hσ
    have hσm : Measurable σ := Measurable.ite
      (measurableSet_le (measurable_coe_nnreal_ennreal.comp S.measurable_rShM) (measurable_snd.comp (S.hÊm ℓ)))
      (S.measurable_rShM.add (measurable_cTime S.measurable_LÊ _)) measurable_const
    have hσL : ∀ ω, (wRun κ θ b jumps (fun j => S.Ê j ω) (ℓ + 1)).2.2.2.1 ℓ ≠ none →
        (σ ω : ℝ≥0∞) ≤ (S.Ê ℓ ω).2 := fun ω _ => by
      simp only [hσ]
      split_ifs with hle
      · rw [ENNReal.coe_add]
        calc (S.rShM ω : ℝ≥0∞) + (cTime (S.LÊ ω) (ratPt i : ℝ) : ℝ≥0∞) ≤ (S.rShM ω : ℝ≥0∞) + S.LÊ ω :=
              add_le_add le_rfl (cTime_le_any (NNReal.coe_nonneg _))
          _ = (S.Ê ℓ ω).2 := add_tsub_cancel_of_le hle
      · exact zero_le
    have h := Nv.measurable_pcPt_at (κ := κ) (θ := θ) hb S.hÊm S.hÊreg S.hÊP ℓ hσm hσL
    have e : (fun ω => if ω ∈ S.Eg then S.pÊ ω (cTime (S.LÊ ω) (ratPt i : ℝ)) else 0) =
        fun ω => if ω ∈ S.Eg then (if ω ∈ LS then
          pcPt (wRun κ θ b jumps (fun j => S.Ê j ω) ℓ) (S.Ê ℓ ω) (σ ω) else 0) else 0 := by
      funext ω
      by_cases hω : ω ∈ S.Eg
      · have hle : (S.rShM ω : ℝ≥0∞) ≤ (S.Ê ℓ ω).2 := by
          rw [← S.rSh_eq hω, ← S.bLife_eq hω]; exact (S.geo hω).shlt.le
        simp only [hω, ↓reduceIte, show ω ∈ LS from S.launch_Ê hω, hσ, hle, pÊ]
        rfl
      · simp only [hω, ↓reduceIte]
    rw [e]
    exact Measurable.ite S.measurableSet_Eg h measurable_const
  have hpc : ∀ ω ∈ S.Eg, ContinuousOn (S.pÊ ω) {t : ℝ≥0 | (t : ℝ≥0∞) ≤ S.LÊ ω} := by
    intro ω hω
    have hc := continuousOn_pcPt_launch (S.hÊP ω) (S.launch_Ê hω)
    have hle : (S.rShM ω : ℝ≥0∞) ≤ (S.Ê ℓ ω).2 := by
      rw [← S.rSh_eq hω, ← S.bLife_eq hω]; exact (S.geo hω).shlt.le
    refine hc.comp (continuous_const.add continuous_id).continuousOn fun t ht => ?_
    show ((S.rShM ω + t : ℝ≥0) : ℝ≥0∞) ≤ (S.Ê ℓ ω).2
    rw [ENNReal.coe_add]
    calc (S.rShM ω : ℝ≥0∞) + t ≤ (S.rShM ω : ℝ≥0∞) + S.LÊ ω := add_le_add le_rfl ht
      _ = (S.Ê ℓ ω).2 := add_tsub_cancel_of_le hle
  have hL0 : ∀ ω ∈ S.Eg, S.LÊ ω ≠ 0 := fun ω hω => by rw [← S.rLife_eq hω]; exact (S.geo hω).pos
  have hMd : ∀ ω ∈ S.Eg, IsDrivenCurve (canonCurve (S.K ω) (S.x₀ ω) (S.pÊ ω) (S.LÊ ω)) := fun ω hω => by
    have := S.driven_rRel hω
    unfold rRel at this
    rwa [S.rPc_eq hω, S.rLife_eq hω] at this
  have h := measurable_canonCurve_rand hKm S.hKc S.hKp (S.hx₀.mono inf_le_left le_rfl) S.measurableSet_Eg hzm hpc
    hL0 hMd r hr
  have e : (fun ω => S.ρM ω r) = (fun ω => if ω ∈ S.Eg then canonCurve (S.K ω) (S.x₀ ω) (S.pÊ ω) (S.LÊ ω) r
      else 0) + S.Egᶜ.indicator fun _ => (r : ℂ) * Complex.I := by
    funext ω
    by_cases hω : ω ∈ S.Eg
    · simp [ρM, hω, rRel, S.rPc_eq hω, S.rLife_eq hω]
    · simp [ρM, hω]
  rw [e]
  exact h.add (measurable_const.indicator S.measurableSet_Eg.compl)

open Classical in
/-- **The root's relative clock** in B's time (entrance `rSh`; `0` off the good event). -/
def a (t : ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
  if ω ∈ S.Eg then Vc.clockOf (rLift κ b jumps E u l k ℓ S.K S.x₀ ω) (rSh κ b jumps E u l k ℓ ω)
    (bLife b jumps E ℓ ω) t else 0

theorem a_of_mem {ω : Ω} (hω : ω ∈ S.Eg) (t : ℝ≥0) :
    S.a t ω = Vc.clockOf (rLift κ b jumps E u l k ℓ S.K S.x₀ ω) (rSh κ b jumps E u l k ℓ ω)
      (bLife b jumps E ℓ ω) t := by
  simp only [a, hω, ↓reduceIte]

theorem a_of_notMem {ω : Ω} (hω : ω ∉ S.Eg) (t : ℝ≥0) : S.a t ω = 0 := by simp only [a, hω, ↓reduceIte]

/-- **The clock is the relative piece's tail clock at `t − rSh`.** -/
theorem a_eq_shift {ω : Ω} (hω : ω ∈ S.Eg) (t : ℝ≥0) :
    S.a t ω = Vc.clockOf (rLift κ b jumps E u l k ℓ S.K S.x₀ ω) 0 (rLife κ b jumps E u l k ℓ ω)
      (t - rSh κ b jumps E u l k ℓ ω) := by
  rw [S.a_of_mem hω]
  have hd := S.driven_rRel hω
  unfold rRel at hd
  rw [← tsub_zero (rLife κ b jumps E u l k ℓ ω)] at hd
  exact clockOf_shift_canon hd _ _ rfl (S.geo hω).pos t

theorem a_eq_zero_of_le {ω : Ω} (t : ℝ≥0) (ht : t ≤ rSh κ b jumps E u l k ℓ ω) : S.a t ω = 0 := by
  by_cases hω : ω ∈ S.Eg
  · rw [S.a_eq_shift hω, tsub_eq_zero_of_le ht]
    have hd := S.driven_rRel hω
    exact clockOf_canonVal_zero hd (S.geo hω).pos
  · exact S.a_of_notMem hω t

theorem a_eq {ω : Ω} (hω : ω ∈ S.Eg) (t : ℝ≥0) :
    S.a t ω = if ((t - rSh κ b jumps E u l k ℓ ω : ℝ≥0) : ℝ≥0∞) < rLife κ b jumps E u l k ℓ ω then
      ENNReal.ofReal (capClock (S.ρM ω) (uOf (rLife κ b jumps E u l k ℓ ω)
        ((t - rSh κ b jumps E u l k ℓ ω : ℝ≥0) : ℝ)))
      else capLife (S.ρM ω) := by
  rw [S.a_eq_shift hω, S.ρM_eq hω]
  have h := clockOf_canonVal (S.driven_rRel hω) (S.geo hω).pos (t - rSh κ b jumps E u l k ℓ ω)
  unfold rRel rLift
  exact h

theorem continuous_a (ω : Ω) : Continuous fun t => S.a t ω := by
  by_cases hω : ω ∈ S.Eg
  · simp only [S.a_eq_shift hω]
    exact (continuous_clockOf_canonVal (S.driven_rRel hω) (S.geo hω).pos).comp
      (continuous_id.sub continuous_const)
  · simp only [S.a_of_notMem hω]; exact continuous_const

theorem monotone_a (ω : Ω) : Monotone fun t => S.a t ω := by
  by_cases hω : ω ∈ S.Eg
  · simp only [S.a_of_mem hω]; exact Vc.monotone_clockOf _ _ _
  · simp only [S.a_of_notMem hω]; exact monotone_const

theorem a_zero (ω : Ω) : S.a 0 ω = 0 := S.a_eq_zero_of_le 0 zero_le

theorem measurable_uOf_rand {L : Ω → ℝ≥0∞} (hL : Measurable L) {s : Ω → ℝ} (hs : Measurable s) :
    Measurable fun ω => uOf (L ω) (s ω) := by
  classical
  unfold uOf
  exact Measurable.ite (hL (measurableSet_singleton ⊤)) hs (hs.div ((ENNReal.measurable_toReal.comp hL).sub hs))

theorem measurable_a (hb : IsPiecewiseConstantBoundaryData b jumps) (t : ℝ≥0) : Measurable (S.a t) := by
  classical
  have hρ := fun r hr => S.measurable_ρM hb r hr
  have hv : Measurable fun ω => (((t - S.rShM ω : ℝ≥0) : ℝ)) :=
    measurable_coe_nnreal_real.comp (measurable_const.sub S.measurable_rShM)
  have e : S.a t = fun ω => if ω ∈ S.Eg then (if (((t - S.rShM ω : ℝ≥0)) : ℝ≥0∞) < S.LÊ ω then
      ENNReal.ofReal (capClock (S.ρM ω) (max (uOf (S.LÊ ω) (t - S.rShM ω : ℝ≥0)) 0)) else capLife (S.ρM ω))
      else 0 := by
    funext ω
    by_cases hω : ω ∈ S.Eg
    · rw [S.a_eq hω, S.rSh_eq hω, S.rLife_eq hω]
      simp only [hω, ↓reduceIte]
      split_ifs with ht
      · rw [max_eq_left (uOf_nonneg (beforeL_of_lt ht))]
      · rfl
    · rw [S.a_of_notMem hω]; simp only [hω, ↓reduceIte]
  rw [e]
  refine Measurable.ite S.measurableSet_Eg (Measurable.ite
    (measurableSet_lt (measurable_coe_nnreal_ennreal.comp (measurable_const.sub S.measurable_rShM)) S.measurable_LÊ)
    ?_ (Supp8.GB6.CoordB.measurable_capLife S.driven_ρM hρ)) measurable_const
  exact measurable_ofReal_capClock_rand S.driven_ρM hρ ((measurable_uOf_rand S.measurable_LÊ hv).max
    measurable_const) fun ω => le_max_right _ _

end RootObj

end InteractingSLE.Theorem14.SB.Nf
