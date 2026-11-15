/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2VsAdapt
import InteractingSLE.Spec.Supplement.SB2ZsSucc

/-!
# SB2(1)'s per-stop versions and the successor structure (D19, step 4)

Packet PROVE-AUX61-NOJUMP (decision D19, option (b)).

* `exists_loewnerTrace_min` (deterministic): a driver stopped at `v` below its horizon has a global Loewner trace equal
  to its generating trace before `v`; `isForceReg_mono`: force regularity passes to an earlier horizon.
* On the good event of `SB2StopData`: the stop is below the relative lifetime (`Vstop_lt_relLife`), the clock is the
  relative lifetime from the lifetime on (`a_eq_relLife`), live times are before the lifetime (`lt_zeta_of_lt`), the
  clock reaches every level below the stop (`reach_of_mem`), the stop is at most the threshold of the frozen driver on
  its type cell (`V_le_thr_of_mem`, the relative collision core `le_thr_of_avoid`), and the stops are announced
  (`ann_of_mem`).
* **`chain_of_mem`**: the per-time chain record at every live time (the round-7 proof from the sample's geometric
  record `GoodAt.geom`, with a horizon `t₂` whose clock is below the stop, and the global trace of the frozen driver).
* The versions use only the stop data: Theorem 1.3 and Lemma S3 enter through `exists_stopData` alone.
* **`ver`**: the `m`-th version `Lv.SB2LineVersionG`; **`versionS`**: SB2DRV's successor structure
  `Lv.SB2LineVersionS`; **`nonempty_versionS`** / **`sb2LineVersionSStatement`**: it exists from Theorem 1.3, Lemma S3
  (SB2(1)'s form) and the relative seed `SB2RelSeedAdmStatement`.
* **`ae_seed_of_versionS`**: conversely, every `Lv.SB2LineVersionS` forces the relative seed (so the seed input is
  necessary for the interface).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.SB.Vs

open Vr Vq Exist.Staged Exist.StagedLaw Lv Sec7.PocketTraversal Supp8.Q3Stop Supp8.GB6.HullId Sec7.Lemma71C

/-! ### Deterministic helpers -/

/-- **A driver stopped at `v` below its horizon has a global Loewner trace** equal to `Γ` before `v`. -/
theorem exists_loewnerTrace_min {Wf : ℝ≥0 → ℝ} {Γ : ℝ≥0 → ℂ} {U : ℝ≥0∞} {v : ℝ≥0} (hv0 : 0 < v)
    (hvU : (v : ℝ≥0∞) < U) (hW0 : Wf 0 = 0) (hWc : ContinuousOn Wf {t | (t : ℝ≥0∞) < U})
    (hgen : ∀ T : ℝ≥0∞, T < U → IsGeneratingTrace Wf T Γ) :
    ∃ ηr : ℝ → ℂ, IsLoewnerTrace (fun r : ℝ => Wf (min r.toNNReal v)) ηr ∧
      ∀ q : ℝ≥0, (q : ℝ≥0∞) < v → ηr q = Γ q := by
  have hopen : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < U} := isOpen_lt ENNReal.continuous_coe continuous_const
  have hWv : ContinuousAt Wf v := hWc.continuousAt (hopen.mem_nhds hvU)
  have hΓv : ContinuousAt Γ v := (Vk.continuousOn_of_forall_lt hgen).continuousAt (hopen.mem_nhds hvU)
  obtain ⟨ηr, hLT, heq⟩ := Vk.exists_loewnerTrace_frz (V := (v : ℝ≥0∞)) (ENNReal.coe_pos.2 hv0) hW0
    (hWc.mono fun _ ht => lt_trans ht hvU) (fun T hT => hgen T (hT.trans hvU)) fun _ => by
      rw [ENNReal.toNNReal_coe]
      exact ⟨⟨_, hWv.tendsto.mono_left nhdsWithin_le_nhds⟩, ⟨_, hΓv.tendsto.mono_left nhdsWithin_le_nhds⟩⟩
  have : (𝓝[<] v).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hv0⟩
  have hfrz : ∀ q : ℝ≥0, Vk.frz Wf (v : ℝ≥0∞) q = Wf (min q v) := fun q => by
    rcases lt_or_ge q v with hq | hq
    · rw [Vk.frz_of_lt (ENNReal.coe_lt_coe.2 hq), min_eq_left hq.le]
    · rw [Vk.frz_of_le (ENNReal.coe_le_coe.2 hq), min_eq_right hq, ENNReal.toNNReal_coe]
      exact (hWv.tendsto.mono_left nhdsWithin_le_nhds).limUnder_eq
  refine ⟨ηr, ?_, heq⟩
  have e : (fun r : ℝ => Wf (min r.toNNReal v)) = fun r : ℝ => Vk.frz Wf (v : ℝ≥0∞) r.toNNReal :=
    funext fun r => (hfrz _).symm
  rw [e]; exact hLT

/-- **Force regularity passes to an earlier horizon.** -/
theorem isForceReg_mono {Ω : Type*} {nL nR : ℕ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {ζ ζ' : Ω → ℝ≥0∞} {ω : Ω}
    (h : Restart.DomainMarkov.Aux79.IsForceReg W VL VR ζ ω) (hle : ζ' ω ≤ ζ ω) :
    Restart.DomainMarkov.Aux79.IsForceReg W VL VR ζ' ω :=
  ⟨h.1, h.2.1.mono fun _ ht => lt_of_lt_of_le ht hle, fun i => (h.2.2.1 i).mono fun _ ht => lt_of_lt_of_le ht hle,
    fun j => (h.2.2.2.1 j).mono fun _ ht => lt_of_lt_of_le ht hle, fun t ht => h.2.2.2.2 t (lt_of_lt_of_le ht hle)⟩

section

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {Ω : Type u} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistOn upperHalfPlaneOpens}
  {E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {u ψ : ℝ} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
  {u₀ : ℂ → ℝ}

namespace SB2StopData

variable {HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ} {I : K2LaunchInputs κ b jumps P h E k u ψ}
  {D : EntranceUnion κ b jumps P h E k u η ζ u₀} (S : SB2StopData HP I D)

/-! ### The stops at a good sample -/

theorem Vstop_lt_relLife {m : ℕ} {ω : Ω} (hω : ω ∈ S.Gs) :
    S.Vstop m ω < Vk.relLife κ b jumps E k u η ζ ω := by
  rw [← (S.good hω).life]; exact (S.sample hω m).2.1

/-- From the lifetime on, the clock is the relative lifetime. -/
theorem a_eq_relLife {ω : Ω} (hω : ω ∈ S.Gs) {t : ℝ≥0} (ht : ζ ω ≤ t) :
    S.a t ω = Vk.relLife κ b jumps E k u η ζ ω := by
  rw [(S.good hω).clock, Vd.clockOf_eq_sup_of_le ht]; rfl

/-- **Live times are before the lifetime.** -/
theorem lt_zeta_of_lt {m : ℕ} {ω : Ω} (hω : ω ∈ S.Gs) {t : ℝ≥0} (ht : S.a t ω < S.V m ω) :
    (t : ℝ≥0∞) < ζ ω := by
  by_contra hζt
  rw [not_lt] at hζt
  rw [S.a_eq_relLife hω hζt, S.V_eq hω] at ht
  exact absurd (S.Vstop_lt_relLife hω) (not_lt.2 ht.le)

/-- **The clock reaches every level below the stop.** -/
theorem reach_of_mem {m : ℕ} {ω : Ω} (hω : ω ∈ S.Gs) {q : ℝ≥0} (hq : (q : ℝ≥0∞) < S.V m ω) :
    ∃ t, (q : ℝ≥0∞) ≤ S.a t ω := by
  rw [S.V_eq hω] at hq
  have hq' : (q : ℝ≥0∞) < Vk.relLife κ b jumps E k u η ζ ω := hq.trans (S.Vstop_lt_relLife hω)
  unfold Vk.relLife at hq'
  obtain ⟨s, hs⟩ := lt_iSup_iff.1 hq'
  obtain ⟨hsζ, hs'⟩ := lt_iSup_iff.1 hs
  refine ⟨(Ve.entT κ b jumps E k u η ζ ω).toNNReal + s, ?_⟩
  rw [(S.good hω).clock]
  unfold Vc.clockOf
  exact le_iSup₂_of_le s le_rfl (le_iSup_of_le hsζ hs'.le)

/-- **The stop is at most the threshold of the frozen driver on its type cell** (the relative collision core). -/
theorem V_le_thr_of_mem {m : ℕ} {ω : Ω} (hω : ω ∈ S.Gs) {w : WordType} (hw : angleWordType κ ψ (I.word ω) = w) :
    S.V m ω ≤ Restart.FCDet.thr (typedRhoL w) (typedRhoR w) (S.W m) (cellXL κ ψ I.word w)
      (cellXR κ ψ I.word w) ω := by
  obtain ⟨-, hlt, htop, -, -, hav⟩ := S.sample hω m
  subst hw
  have hρω := S.ρ'_eq hω
  have hg := S.isGeneratingTrace_Wr ω (T := S.Vstop m ω) (by rw [hρω]; exact hlt)
  rw [hρω] at hg
  rw [S.V_eq hω, ← ENNReal.coe_toNNReal htop]
  refine le_thr_of_avoid (S.continuous_W m) (S.W_zero m)
    (Restart.FCDet.isOrderedForceWord_typeXL (I.word ω)).2.1
    (Restart.FCDet.isOrderedForceWord_typeXL (I.word ω)).2.2.2 (Γ := capTrace (S.ρ ω)) ?_ fun t ht => hav t ?_
  · rw [ENNReal.coe_toNNReal htop]
    exact Sec5.CrossRestart.isGeneratingTrace_congr_drive (w := fun t => S.W m t ω) hg
      fun s hs => S.W_eq_Wr hω hs.le
  · exact (ENNReal.coe_lt_coe.2 ht).trans_eq (ENNReal.coe_toNNReal htop)

/-- **The stops are announced** by the record-path rules along the frozen driver. -/
theorem ann_of_mem {m : ℕ} {ω : Ω} (hω : ω ∈ S.Gs) :
    (∀ n, annRules gaugeRead m n (sb2Rec I ω, fun s => S.W m s ω) < S.V m ω) ∧
      ⨆ n, annRules gaugeRead m n (sb2Rec I ω, fun s => S.W m s ω) = S.V m ω := by
  obtain ⟨-, -, -, hann, hsup, -⟩ := S.sample hω m
  have he : ∀ n, annRules gaugeRead m n (sb2Rec I ω, fun s => S.W m s ω) =
      annRules gaugeRead m n (sb2Rec I ω, fun s => S.Wr s ω) := fun n =>
    isPathRule_annRules isCausal_gaugeRead m n _ _ _ fun q hq => (S.W_eq_Wr hω (hq.trans (hann n).le)).symm
  simp only [he, S.V_eq hω]
  exact ⟨hann, hsup⟩

/-! ### The chain record -/

/-- **The per-time chain record of the `m`-th version at every live time.** -/
theorem chain_of_mem (m : ℕ) (t : ℝ≥0) :
    ∀ᵐ ω ∂P, ω ∈ D.event → S.a t ω < S.V m ω →
      Tc.IsSB2LineChainAt (lowerPrefix κ b jumps E (k + 1) u ω) u (launchEntry κ b jumps E (k + 1) u ω)
        (Lv.launchChart κ b jumps E (k + 1) ω) (η ω) (ζ ω) (fun q => S.W m q ω) (fun t => S.a t ω) (S.V m ω) t := by
  filter_upwards [S.ae_mem_Gs, Ve.ae_flowDriver HP] with ω hG hfd hD hlt
  have hGω : ω ∈ S.Gs := hG hD
  have hg := S.good hGω
  have hrec := hg.geom
  have hl := hg.launch
  have hT := hg.ent
  have hclock := hg.clock
  have htζ : (t : ℝ≥0∞) < ζ ω := S.lt_zeta_of_lt hGω hlt
  obtain ⟨hv0, -, hvtop, -, -, -⟩ := S.sample hGω m
  rw [S.V_eq hGω] at hlt
  set TL := Ve.entT κ b jumps E k u η ζ ω with hTLdef
  set fl := Ve.flowLift κ b jumps E k u η ζ ω with hfldef
  have hTLtop : TL ≠ ⊤ := ne_top_of_lt hT
  have hTLc : ((TL.toNNReal : ℝ≥0) : ℝ≥0∞) = TL := ENNReal.coe_toNNReal hTLtop
  have hTLr : TL.toReal = (TL.toNNReal : ℝ) := rfl
  have h0 : capClock (fun r : ℝ => fl r.toNNReal) 0 = 0 := hg.c0
  -- a horizon `t₂` beyond `t` and the entrance whose clock is below the stop
  have hmax : S.a (max t TL.toNNReal) ω < S.Vstop m ω := by
    rcases le_total t TL.toNNReal with h1 | h1
    · rw [max_eq_right h1, hclock, Vc.clockOf_eq_zero_of_le le_rfl h0]; exact hv0
    · rw [max_eq_left h1]; exact hlt
  have hopen : IsOpen {s : ℝ≥0 | S.a s ω < S.Vstop m ω} := isOpen_lt (S.hac ω) continuous_const
  obtain ⟨c, hc, hsub⟩ := exists_Ico_subset_of_mem_nhds (hopen.mem_nhds hmax) ⟨max t TL.toNNReal + 1, lt_add_one _⟩
  obtain ⟨t₂, ht₂, ht₂c⟩ := exists_between hc
  have ht₂v : S.a t₂ ω < S.Vstop m ω := hsub ⟨ht₂.le, ht₂c⟩
  have ht₂ζ : (t₂ : ℝ≥0∞) < ζ ω := S.lt_zeta_of_lt hGω (m := m) (by rw [S.V_eq hGω]; exact ht₂v)
  obtain ⟨T, hmT, hTt₂⟩ := exists_between ht₂
  have hTζ : (T : ℝ≥0∞) < ζ ω := (ENNReal.coe_lt_coe.2 hTt₂).trans ht₂ζ
  have htT : (t : ℝ) < T := NNReal.coe_lt_coe.2 ((le_max_left _ _).trans_lt hmT)
  have hLT' : (TL.toNNReal : ℝ) < T := NNReal.coe_lt_coe.2 ((le_max_right _ _).trans_lt hmT)
  have hTLT' : TL < T := by rw [← hTLc]; exact ENNReal.coe_lt_coe.2 ((le_max_right _ _).trans_lt hmT)
  set mx : ℝ := max (t : ℝ) (TL.toNNReal : ℝ) with hmx
  have hmT' : mx < T := max_lt htT hLT'
  set S₁ : ℝ := (mx - TL.toNNReal + ((T : ℝ) - TL.toNNReal)) / 2 with hS₁
  have hS₁pos : 0 < S₁ := by rw [hS₁]; linarith [le_max_right (t : ℝ) (TL.toNNReal : ℝ)]
  have hS₁T : TL.toReal + S₁ < T := by rw [hTLr, hS₁]; linarith
  have htS : (t : ℝ) < (TL.toNNReal : ℝ) + S₁ := by
    rw [hS₁]; linarith [le_max_left (t : ℝ) (TL.toNNReal : ℝ)]
  obtain ⟨p, g, β', γ, tL, Wr₀, ηr₀, hp, hch, hw', hag, ⟨hchain, hnoR⟩, hγeq⟩ :=
    hrec T hTζ.le hTLT' S₁ hS₁pos hS₁T
  have htt : tL = TL.toNNReal := by
    rw [← ENNReal.coe_inj, hTLc]; exact hw'.2.2.2.2.1
  subst htt
  have hfl : ∀ s : ℝ≥0, (s : ℝ) < S₁ → γ s = fl s := hγeq
  have hcapEq : ∀ x : ℝ, 0 ≤ x → x < S₁ → capClock (fun r : ℝ => γ r.toNNReal) x =
      capClock (fun r : ℝ => fl r.toNNReal) x := fun x hx hxS =>
    Vc.capClock_congr fun r hr => hfl r (by
      have h1 := NNReal.coe_le_coe.2 hr
      rw [Real.coe_toNNReal _ hx] at h1
      linarith)
  have hTS : (TL.toNNReal : ℝ) + S₁ ≤ T := by rw [hTLr] at hS₁T; linarith
  obtain ⟨wf, hwfc, hwf0, hwfg⟩ := hfd
  obtain ⟨wP, ηw, hwPc, hwP0, hwPL, hηw⟩ := Ve.exists_physDriver hwfg hwfc hwf0 hTζ
  -- the global trace of the frozen driver
  have hρω := S.ρ'_eq hGω
  obtain ⟨ηn, hLTn, hηn⟩ := exists_loewnerTrace_min (Wf := (S.Wr · ω)) (Γ := capTrace (S.ρ' ω))
    (v := (S.Vstop m ω).toNNReal) (ENNReal.toNNReal_pos hv0.ne' hvtop) (S.Vstop_toNNReal_lt hGω) (S.Wr_zero ω)
    (S.continuousOn_Wr ω) fun T' hT' => S.isGeneratingTrace_Wr ω hT'
  have hWeq : (fun r : ℝ => S.W m r.toNNReal ω) =
      fun r : ℝ => S.Wr (min r.toNNReal (S.Vstop m ω).toNNReal) ω := funext fun r => S.W_of_mem hGω _
  rw [← hWeq] at hLTn
  -- it reads the lift in the capacity clock before the horizon `T`
  have hηfl : ∀ s : ℝ≥0, (TL.toNNReal : ℝ) + s < T → ηn (capClock (fun r : ℝ => fl r.toNNReal) s) = fl s := by
    intro s hs
    have hsT : TL.toNNReal + s ≤ t₂ := by
      have h1 : ((TL.toNNReal + s : ℝ≥0) : ℝ) < T := by rw [NNReal.coe_add]; exact hs
      exact (NNReal.coe_lt_coe.1 h1).le.trans hTt₂.le
    have hsζ : ((TL.toNNReal + s : ℝ≥0) : ℝ≥0∞) < ζ ω := (ENNReal.coe_le_coe.2 hsT).trans_lt ht₂ζ
    have hcl : S.a (TL.toNNReal + s) ω = ENNReal.ofReal (capClock (fun r : ℝ => fl r.toNNReal) s) := by
      rw [hclock, Vc.clockOf_eq le_self_add hsζ (hg.mono _ le_self_add hsζ), NNReal.coe_add, add_sub_cancel_left]
    have hcv : ENNReal.ofReal (capClock (fun r : ℝ => fl r.toNNReal) s) < S.Vstop m ω := by
      rw [← hcl]; exact (S.ham ω hsT).trans_lt ht₂v
    obtain ⟨hcap, -⟩ := Vk.capTrace_capClock hg.driven hT hg.fam1 hg.fam2 hsζ
    obtain ⟨r, hr0, hrc, -⟩ := Vk.exists_relTime hT hg.fam1 hg.fam2 hsζ
    have hnn : 0 ≤ capClock (Vd.liftR fl) s := hrc ▸ hg.driven.capClock_nonneg hr0
    have hq : (((capClock (Vd.liftR fl) s).toNNReal : ℝ≥0) : ℝ≥0∞) < ((S.Vstop m ω).toNNReal : ℝ≥0∞) := by
      rw [ENNReal.coe_toNNReal hvtop]; exact hcv
    have h1 := hηn _ hq
    have e : Vd.liftR fl (s : ℝ) = fl s := by simp only [Vd.liftR, Real.toNNReal_coe]
    rw [Real.coe_toNNReal _ hnn, hρω, hcap, e] at h1
    exact h1
  refine ⟨p, g, β', γ, TL.toNNReal, S₁, fun r => S.W m r.toNNReal ω, ηn, wP, ηw, htS, hp, hch, hw', hag,
    ⟨hS₁pos, fun S₀ hS₀ hS₀S => Ve.chain_with_driver (hchain S₀ hS₀ hS₀S)
      ((S.continuous_W m ω).comp continuous_real_toNNReal) (by simp [S.W_zero]) hLTn fun s hs => ?_, hnoR⟩,
    Ve.physClause hwPc hwP0 hwPL hTS hηw hag, fun q _ => by simp, fun t' ht' => ?_, fun t' ht1 ht2 => ?_⟩
  · -- the global trace reads the lift in the capacity clock
    have hs1 : s < S₁ := hs.2.trans_lt hS₀S
    rw [hcapEq s hs.1 hs1, hfl s.toNNReal (by rw [Real.coe_toNNReal _ hs.1]; exact hs1)]
    have h1 := hηfl s.toNNReal (by rw [Real.coe_toNNReal _ hs.1]; linarith)
    rw [Real.coe_toNNReal _ hs.1] at h1
    exact h1
  · -- the clock vanishes up to the entrance
    show S.a t' ω = 0
    rw [hclock]
    exact Vc.clockOf_eq_zero_of_le (NNReal.coe_le_coe.1 ht') h0
  · -- the clock is the capacity clock of the lift after the entrance
    have hx0 : 0 ≤ (t' : ℝ) - TL.toNNReal := by linarith
    have hxS : (t' : ℝ) - TL.toNNReal < S₁ := by linarith
    have ht'ζ : (t' : ℝ≥0∞) < ζ ω := by
      refine lt_of_lt_of_le (ENNReal.coe_lt_coe.2 (NNReal.coe_lt_coe.1 ?_)) hTζ.le
      linarith
    have hmono : MonotoneOn (capClock fun r : ℝ => fl r.toNNReal) (Icc 0 ((t' : ℝ) - TL.toNNReal)) :=
      ((hchain _ hx0 hxS).2.2.2.2.1.monotoneOn).congr fun y hy => hcapEq y hy.1 (hy.2.trans_lt hxS)
    show S.a t' ω = _
    rw [hclock, Vc.clockOf_eq (NNReal.coe_le_coe.1 ht1) ht'ζ hmono, ← hcapEq _ hx0 hxS]
    rfl

/-! ### The versions -/

/-- **The `m`-th version**: the driver frozen at the `m`-th stop, the version clock, the stop as horizon. -/
def ver (m : ℕ) : SB2LineVersionG HP I D where
  𝓗 := Tc.tcFilt (D.lineFiltC HP) S.a S.ha
  W := S.W m
  a := S.a
  Λ := fun _ => S.V m
  marks_le := Tc.le_tcFilt_zero (D.marks_le_lineFiltC HP)
  W_zero := S.W_zero m
  W_cont := S.continuous_W m
  W_adapted := S.stronglyAdapted_W m
  clock_cont := S.hac
  clock_mono := S.ham
  clock_zero := S.ha0
  clock_meas := S.ha
  timeChange := fun q D' hD' t => Tc.tcFilt_inter q D' hD' t
  reach := fun _ _ q => by
    filter_upwards [S.ae_mem_Gs] with ω hG hc hq using S.reach_of_mem (hG hc.1.1) hq
  reg := fun _ _ => by
    filter_upwards [S.ae_mem_Gs] with ω hG hc using isForceReg_mono
      (Vh.reg_of_continuous (S.W_zero m) (S.continuous_W m) _ _ _ _ ω) (S.V_le_thr_of_mem (hG hc.1.1) hc.1.2)
  safeS := fun _ _ _ t => S.measurableSet_safe_stop m (isClosed_tsupport _) t
  safeL := fun _ _ Fb t => S.measurableSet_safe_stop m
    (Set.Finite.isClosed_biUnion Fb.finite_toSet fun _ _ => isClosed_closedBall) t
  chain := fun _ _ t => by
    filter_upwards [S.chain_of_mem m t] with ω hω hc hlt using hω hc.1.1 hlt
  alive := fun _ _ t => by
    filter_upwards [S.ae_mem_Gs] with ω hG hc hlt using S.lt_zeta_of_lt (hG hc.1.1) hlt
  Λ_le := fun _ _ => by
    filter_upwards [S.ae_mem_Gs] with ω hG hc using S.V_le_thr_of_mem (hG hc.1.1) hc.1.2

/-- **SB2DRV's successor structure** from the stop data. -/
def versionS : SB2LineVersionS HP I D where
  ver := S.ver
  V := S.V
  record := sb2Rec I
  record_meas := (measurable_sb2Rec I).mono D.past_le_marks le_rfl
  ρ := stopRule
  ρs := annRules gaugeRead
  ρ_meas := measurable_stopRule
  ρ_rule := isPathRule_stopRule
  ρs_meas := measurable_annRules measurable_gaugeRead
  ρs_rule := isPathRule_annRules isCausal_gaugeRead
  ρs_fin := annRules_ne_top gaugeRead
  ρs_mono := monotone_annRules gaugeRead
  Λ_eq := fun _ _ => rfl
  V_eq := fun _ _ => rfl
  ann := fun _ => by
    filter_upwards [S.ae_mem_Gs] with ω hG hD using S.ann_of_mem (hG hD)
  V_le_thr := fun _ _ _ => by
    filter_upwards [S.ae_mem_Gs] with ω hG hc using S.V_le_thr_of_mem (hG hc.1) hc.2

end SB2StopData

/-- **SB2(1)'s successor versions exist** (D19, option (b)). -/
theorem nonempty_versionS (h13 : Exist.Theorem13Statement.{u}) (hS3 : Tc.SB2EntranceNoCommonArcStatement.{u})
    (hseedS : SB2RelSeedAdmStatement.{u}) (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ)
    (I : K2LaunchInputs κ b jumps P h E k u ψ) (D : EntranceUnion κ b jumps P h E k u η ζ u₀) :
    Nonempty (SB2LineVersionS HP I D) :=
  let ⟨S⟩ := exists_stopData h13 hS3 hseedS HP I D
  ⟨S.versionS⟩

/-- **Every successor structure forces the relative seed**: the stops are positive (`ann`) and at most the threshold
on the type cell (`V_le_thr`), and the threshold is `0` at a seed at its threshold (`Lv.not_seed_of_thr_pos`). -/
theorem ae_seed_of_versionS {HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ}
    {I : K2LaunchInputs κ b jumps P h E k u ψ} {D : EntranceUnion κ b jumps P h E k u η ζ u₀}
    (S : SB2LineVersionS HP I D) :
    ∀ w ∈ I.types, ∀ᵐ ω ∂P, ω ∈ wordTypeCell κ ψ I.word D.event w →
      ¬ ForceWord.ThresholdCondition (typedRhoL w) (typedRhoR w) 0 (cellXL κ ψ I.word w ω)
        (cellXR κ ψ I.word w ω) := by
  intro w hw
  filter_upwards [S.ann 0, S.V_le_thr 0 w hw] with ω hann hle hc
  have hpos : 0 < S.V 0 ω := lt_of_le_of_lt (zero_le) ((hann hc.1).1 0)
  exact Lv.not_seed_of_thr_pos (S.ver 0).W_zero (S.ver 0).W_cont
    (fun ω' i => (Restart.FCDet.isOrderedForceWord_typeXL (I.word ω')).2.1 i)
    (fun ω' j => (Restart.FCDet.isOrderedForceWord_typeXL (I.word ω')).2.2.2 j) (hpos.trans_le (hle hc))

end

/-- **SB2(1)'s successor versions for every launch problem.** -/
def SB2LineVersionSStatement : Prop :=
  ∀ (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens)
    (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (k : ℕ) (u ψ : ℝ) (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞)
    (HP : SB2LaunchProblem κ b jumps P h E k u ψ η ζ) (I : K2LaunchInputs κ b jumps P h E k u ψ) (u₀ : ℂ → ℝ)
    (D : EntranceUnion κ b jumps P h E k u η ζ u₀), Nonempty (SB2LineVersionS HP I D)

/-- **`SB2LineVersionSStatement` from Theorem 1.3, Lemma S3 (SB2(1)'s form) and the relative seed.** -/
theorem sb2LineVersionSStatement (h13 : Exist.Theorem13Statement.{u})
    (hS3 : Tc.SB2EntranceNoCommonArcStatement.{u}) (hseedS : SB2RelSeedAdmStatement.{u}) :
    SB2LineVersionSStatement.{u} := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HP I _ D =>
  nonempty_versionS h13 hS3 hseedS HP I D

/-- **The relative seed is equivalent to the successor versions** (given Theorem 1.3 and S3). -/
theorem sb2RelSeedAdmStatement_of_versionS (hV : SB2LineVersionSStatement.{u}) : SB2RelSeedAdmStatement.{u} :=
  fun κ b jumps _ _ _ P _ h E k u ψ η ζ HP I u₀ D =>
    ae_seed_of_versionS (hV κ b jumps P h E k u ψ η ζ HP I u₀ D).some

end InteractingSLE.Theorem14.SB.Vs
