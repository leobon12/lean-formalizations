/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2YaEnd
import InteractingSLE.Spec.Supplement.SB2JvRoot
import InteractingSLE.Spec.Supplement.SB2LsRec
import InteractingSLE.Spec.Supplement.SB2MaL
import InteractingSLE.Spec.Supplement.BW1TermRestart
import InteractingSLE.Spec.Supplement.SB2XtSample

/-!
# The relative root's end: its right end-hit, its record and no left end-hit

Packet PROVE-T14-SB2LIFT (round 31; item 4, the relative root fields of `PieceStartV`). The relative root is a piece
from `0` in the identity chart, whose stage curve is the tail lift `γ` read at the tail time (`stValp_eq_tail`):
* **`rel_trace_lift`**: before its end, every point of the relative trace is `γ s` at a tail time `s` of a point of
  the shifted actual piece before its end;
* **`rel_hit`**: if the actual piece has a right end-hit at `x` with end point `z` (`actual_end`), the relative root
  has a right end-hit at `ι z`;
* **`rel_lRecR`**: the relative root's new record is `ι z`;
* **`rel_noLeftHit`**: a relative root with a right end-hit has no left end-hit (`not_leftHit_of_lProf3`).
Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Lk

open Supp9B Exist Exist.Staged Exist.StagedLaw LuM GW1W GW1Bookkeep Sec7.PocketTraversal Sec7.Lemma71C

variable {c : Chart} {R m : ℝ} {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0} {s₁ s₂ : ExplState} {e₁ e₂ : Drv} {t₀ : ℝ≥0}

/-- **Before its end, the relative trace is the tail lift at the tail time of the shifted actual piece.** -/
theorem rel_trace_lift (hγ : IsTailLiftCurve c R m β₀ tL γ) (hβ : IsProperCurve β₀) (hU : UpperChartOK c)
    (hs₂ : stChart s₂ = Chart.id.recenter 0) (hF : Mn.StageFacts c m s₁ e₁ t₀ s₂ e₂) (hfin : e₁.2 - t₀ ≠ ⊤)
    (hPc : ContinuousOn (fun t => pcPt s₁ e₁ (t₀ + t)) {t : ℝ≥0 | (t : ℝ≥0∞) ≤ e₁.2 - t₀})
    (htl : ∀ t ∈ {t : ℝ≥0 | (t : ℝ≥0∞) ≤ e₁.2 - t₀}, pcPt s₁ e₁ (t₀ + t) ∈ β₀ '' Ici tL) :
    ∀ τ : ℝ≥0, (τ : ℝ≥0∞) < e₂.2 → ∃ s t : ℝ≥0, (t : ℝ≥0∞) < e₁.2 - t₀ ∧
      trOf e₂ τ = γ s ∧ β₀ (tL + s) = pcPt s₁ e₁ (t₀ + t) := by
  obtain ⟨hcH, hc1, hoff⟩ := hU
  obtain ⟨hρ, he₂, hgen, hrel, hdense, hL0, hpr₂⟩ := hF
  set p : ℝ≥0 → ℂ := fun t => pcPt s₁ e₁ (t₀ + t) with hp
  set L := e₁.2 - t₀ with hLdef
  set ρ := stCurvep c m p L s₂ with hρdef
  obtain ⟨σ, hσc, hσ⟩ := exists_tailTime hβ hPc htl
  have hs₂' : ∀ z, (stChart s₂).1 z = z := (root_chart_facts hs₂).1
  have hval := stValp_eq_tail hγ hcH hc1 hoff hs₂' hσc hσ hdense
  obtain ⟨-, hW, ⟨α, f, hαeq, hα0, hαc, -, -⟩, -, -, -⟩ := hrel.1 hfin
  have hαg : IsGeneratingTrace e₂.1 e₂.2 α := by
    refine ⟨hα0, hαc, fun t ht => ?_⟩
    obtain ⟨T', htT', hT'⟩ := exists_between ht
    have h := (hgen T' (by rw [← he₂]; exact hT')).2.2 t htT'
    rwa [image_congr fun s hs => hαeq s (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hs.2) ht)]
  have hWlt : ContinuousOn e₂.1 {t | (t : ℝ≥0∞) < e₂.2} :=
    hW.mono fun _ (hs : _ < e₂.2) => (le_of_lt hs : _ ≤ e₂.2)
  have hLpos : 0 < L.toReal := ENNReal.toReal_pos hL0 hfin
  intro τ hτ
  have htr : trOf e₂ τ = α τ :=
    GW4Leaf.eqOn_of_isGeneratingTrace hαg (isGeneratingTrace_trOf hpr₂) hWlt hpr₂.1 τ hτ.le
  have hu : 0 ≤ capInv ρ τ := capInv_nonneg _ _
  set t : ℝ≥0 := (clockOf L.toReal (capInv ρ τ)).toNNReal with htdef
  have htL : (t : ℝ≥0∞) < L := by
    have h1 := clockOf_lt hLpos hu
    have h2 : t < L.toNNReal := by
      rw [htdef]
      exact (Real.toNNReal_lt_toNNReal_iff hLpos).2 h1 |>.trans_eq (by simp)
    rw [← ENNReal.coe_toNNReal hfin]
    exact_mod_cast h2
  refine ⟨σ t, t, htL, ?_, hσ t htL.le⟩
  rw [htr, hαeq τ hτ]
  show ρ (capInv ρ τ) = γ (σ t)
  rw [hρdef, stCurvep_of_fin hfin]
  exact hval t htL


variable {b₁ b₂ : ℝ → ℝ} {J₁ J₂ : Finset ℝ} {ι : ℝ → ℝ}

theorem lt_of_lt_tsub_shift {t t₀ : ℝ≥0} {a : ℝ≥0∞} (h : (t : ℝ≥0∞) < a - t₀) : ((t₀ + t : ℝ≥0) : ℝ≥0∞) < a := by
  push_cast
  rw [add_comm]
  exact lt_tsub_iff_right.1 h

/-- A real relative point `γ s > 0` is the lift of an actual real point `> R`. -/
theorem back_of_real (hι : RayCorr b₁ J₁ b₂ J₂ R ι) (hD : LiftCurveData β₀ γ tL R ι) {s : ℝ≥0}
    (h0 : (γ s).im = 0) (hpos : 0 < (γ s).re) :
    ∃ y : ℝ, R < y ∧ ι y = (γ s).re ∧ β₀ (tL + s) = y := by
  obtain ⟨y, hyR, hy⟩ := hι.surj _ hpos.le
  have hyR' : R < y := by
    rcases eq_or_lt_of_le hyR with rfl | h
    · rw [hι.map_base] at hy; linarith
    · exact h
  have hγ : γ s = ι y := by rw [hy]; exact Complex.ext (by simp) (by simp [h0])
  exact ⟨y, hyR', hy, hD.back s y hyR' hγ⟩

/-- **The relative root has a right end-hit at `ι z`.** -/
theorem rel_hit (hι : RayCorr b₁ J₁ b₂ J₂ R ι) (hD : LiftCurveData β₀ γ tL R ι)
    (hs₂ : stChart s₂ = Chart.id.recenter 0) (hpr₂ : GW1P.PieceRegular e₂.1 e₂.2) (hfin₂ : e₂.2 ≠ ⊤)
    (hrel : ∀ τ : ℝ≥0, (τ : ℝ≥0∞) < e₂.2 → ∃ s t : ℝ≥0, (t : ℝ≥0∞) < e₁.2 - t₀ ∧
      trOf e₂ τ = γ s ∧ β₀ (tL + s) = pcPt s₁ e₁ (t₀ + t))
    {x z : ℝ} (hbefore : ∀ t : ℝ≥0, (t : ℝ≥0∞) < e₁.2 → ∀ y : ℝ, pcPt s₁ e₁ t = y → y < x)
    (hxz : x ≤ z) (hRz : R < z) (hend : ((ι z : ℝ) : ℂ) ∈ trOf e₂ '' Icc 0 e₂.2.toNNReal) :
    lHit (stChart s₂) ⊤ e₂ (ι z) := by
  have hc1 : ∀ w, (stChart s₂).1 w = w := (root_chart_facts hs₂).1
  have hιz : 0 < ι z := by
    have := hι.mono (mem_Ici.2 le_rfl) (mem_Ici.2 hRz.le) hRz
    rwa [hι.map_base] at this
  have hre : ((stChart s₂).1 (ι z : ℂ)).im = 0 := by rw [hc1]; simp
  have hne : (stChart s₂).1 (ι z : ℂ) ≠ 0 := by rw [hc1]; exact_mod_cast hιz.ne'
  have hαg := isGeneratingTrace_trOf hpr₂
  have hWlt : ContinuousOn e₂.1 {t | (t : ℝ≥0∞) < e₂.2} :=
    hpr₂.2.1.mono fun _ (hs : _ < e₂.2) => (le_of_lt hs : _ ≤ e₂.2)
  have hT : ((e₂.2.toNNReal : ℝ≥0) : ℝ≥0∞) = e₂.2 := ENNReal.coe_toNNReal hfin₂
  refine (lHit_iff_closure hpr₂ hfin₂ hre hne).2 ⟨fun r hr0 hrT hmem => ?_, ?_⟩
  · rw [hc1] at hmem
    have hrT' : r.toNNReal < e₂.2.toNNReal := by
      have : r < (e₂.2.toNNReal : ℝ) := by simpa [stopTime, min_eq_right le_top] using hrT
      exact (Real.toNNReal_lt_iff_lt_coe hr0).2 this
    have hK : IsCompact (trOf e₂ '' Icc 0 r.toNNReal) :=
      isCompact_Icc.image_of_continuousOn (hαg.2.1.mono fun τ hτ =>
        show (τ : ℝ≥0∞) ≤ e₂.2 from hT ▸ ENNReal.coe_le_coe.2 (hτ.2.trans hrT'.le))
    have hKH : trOf e₂ '' Icc 0 r.toNNReal ⊆ Hbar := by
      rintro _ ⟨τ, hτ, rfl⟩
      exact Sec7.IsGeneratingTrace.mem_Hbar hαg hWlt hpr₂.1
        (hT ▸ ENNReal.coe_le_coe.2 (hτ.2.trans hrT'.le))
    obtain ⟨w, ⟨τ, hτ, rfl⟩, hw0, hle⟩ := Sec7.R6Fd.exists_real_ge_of_mem_closure_fillH hK hKH hmem
    have hτl : (τ : ℝ≥0∞) < e₂.2 := hT ▸ ENNReal.coe_lt_coe.2 (lt_of_le_of_lt hτ.2 hrT')
    obtain ⟨s, t, ht, htr, hβs⟩ := hrel τ hτl
    rw [htr] at hw0 hle
    obtain ⟨y, hyR, hyι, hβy⟩ := back_of_real hι hD hw0 (by linarith)
    have hy := hbefore (t₀ + t) (lt_of_lt_tsub_shift ht) y (by rw [← hβs, hβy])
    have hlt := hι.mono (mem_Ici.2 hyR.le) (mem_Ici.2 hRz.le) (lt_of_lt_of_le hy hxz)
    linarith
  · have hna := not_lAlive_of_mem_trace hpr₂ hfin₂ hre hne (by rw [hc1]; exact hend)
    rwa [lAlive_iff_notMem_closure_fillH hpr₂ hfin₂ hre hne, not_not] at hna

/-- **The relative root's new record is `ι z`.** -/
theorem rel_lRecR (hι : RayCorr b₁ J₁ b₂ J₂ R ι) (hD : LiftCurveData β₀ γ tL R ι)
    (hs₂ : stChart s₂ = Chart.id.recenter 0) (hrec₂ : stRecR s₂ = 0) (hpr₂ : GW1P.PieceRegular e₂.1 e₂.2)
    (hfin₂ : e₂.2 ≠ ⊤) (hL : LiftRel β₀ tL γ (newPc s₁ e₁) (newPc s₂ e₂))
    (htip₂ : (newPc s₂ e₂).1.tipSet (newPc s₂ e₂).2.1 (newPc s₂ e₂).2.2 = trOf e₂ '' Icc 0 e₂.2.toNNReal)
    {z : ℝ} (hRz : R < z) (hend : ((ι z : ℝ) : ℂ) ∈ trOf e₂ '' Icc 0 e₂.2.toNNReal)
    (hmax : ∀ w ∈ (newPc s₁ e₁).1.tipSet (newPc s₁ e₁).2.1 (newPc s₁ e₁).2.2, w.im = 0 → w.re ≤ z) :
    lRecR s₂ ⊤ e₂ = ι z := by
  have hc1 : ∀ w, (stChart s₂).1 w = w := (root_chart_facts hs₂).1
  have hιz : 0 < ι z := by
    have := hι.mono (mem_Ici.2 le_rfl) (mem_Ici.2 hRz.le) hRz
    rwa [hι.map_base] at this
  have hαg := isGeneratingTrace_trOf hpr₂
  have hWlt : ContinuousOn e₂.1 {t | (t : ℝ≥0∞) < e₂.2} :=
    hpr₂.2.1.mono fun _ (hs : _ < e₂.2) => (le_of_lt hs : _ ≤ e₂.2)
  have hT : ((e₂.2.toNNReal : ℝ≥0) : ℝ≥0∞) = e₂.2 := ENNReal.coe_toNNReal hfin₂
  have hK : IsCompact (trOf e₂ '' Icc 0 e₂.2.toNNReal) :=
    isCompact_Icc.image_of_continuousOn (hαg.2.1.mono fun τ hτ =>
      show (τ : ℝ≥0∞) ≤ e₂.2 from hT ▸ ENNReal.coe_le_coe.2 hτ.2)
  have hKH : trOf e₂ '' Icc 0 e₂.2.toNNReal ⊆ Hbar := by
    rintro _ ⟨τ, hτ, rfl⟩
    exact Sec7.IsGeneratingTrace.mem_Hbar hαg hWlt hpr₂.1 (hT ▸ ENNReal.coe_le_coe.2 hτ.2)
  unfold lRecR
  rw [hrec₂]
  have hS : IsGreatest (insert 0 {y : ℝ | 0 < y ∧ ¬ lAlive (stChart s₂) ⊤ e₂ y}) (ι z) := by
    have hre : ∀ y : ℝ, ((stChart s₂).1 (y : ℂ)).im = 0 := fun y => by rw [hc1]; simp
    refine ⟨Or.inr ⟨hιz, not_lAlive_of_mem_trace hpr₂ hfin₂ (hre _) (by rw [hc1]; exact_mod_cast hιz.ne')
      (by rw [hc1]; exact hend)⟩, ?_⟩
    rintro y (rfl | ⟨hy0, hy⟩)
    · exact hιz.le
    · have hne : (stChart s₂).1 (y : ℂ) ≠ 0 := by rw [hc1]; exact_mod_cast hy0.ne'
      rw [lAlive_iff_notMem_closure_fillH hpr₂ hfin₂ (hre y) hne, not_not, hc1] at hy
      obtain ⟨w, hw, hw0, hyw⟩ := Sec7.R6Fd.exists_real_ge_of_mem_closure_fillH hK hKH hy
      rw [← htip₂, hL] at hw
      obtain ⟨s, hs, rfl⟩ := hw
      obtain ⟨y', hy'R, hy'ι, hβy⟩ := back_of_real hι hD hw0 (by linarith)
      have hle := hmax _ hs (by rw [hβy]; simp)
      rw [hβy] at hle
      simp only [Complex.ofReal_re] at hle
      have := hι.mono.monotoneOn (mem_Ici.2 hy'R.le) (mem_Ici.2 hRz.le) hle
      linarith
  exact hS.csSup_eq

/-- **A relative root with a right end-hit has no left end-hit.** -/
theorem rel_noLeftHit {θ : ℝ} (hreg : IsRegularDriver e₂)
    (hgood : e₂.2 ≠ ⊤ → LocalExt.IsDrvGood (recHist (recOf ⊤ e₂))) (hfin₂ : e₂.2 ≠ ⊤) (hpos₂ : e₂.2 ≠ 0)
    {y : ℝ} (hy : 0 < y) (hhit : lHit (stChart (ExplState.init 0)) ⊤ e₂ y) :
    ¬ ∃ x : ℝ, x < 0 ∧ lHit (stChart (ExplState.init 0)) ⊤ e₂ x := by
  have hthr : stStatus (ExplState.launch (ExplState.init 0) 0 e₂ θ ⊤) ≠ stThr (some false) := by
    obtain ⟨-, -, -, -, hst, -⟩ := launch_eq_of_ne_top (ExplState.init 0) 0 e₂ θ ⊤ (min_top_ne_top hfin₂)
    rw [hst]
    have hnlt : ¬ (⊤ : ℝ≥0∞) < e₂.2 := not_lt.2 le_top
    have hex : ∃ x : ℝ, stRecR (ExplState.init 0) < x ∧ lHit (stChart (ExplState.init 0)) ⊤ e₂ x := ⟨y, hy, hhit⟩
    unfold lStatus
    simp only [hnlt, hpos₂, hex, ↓reduceIte, ne_eq]
    intro h
    cases h
  exact not_leftHit_of_lProf3 (lProf3_init 0) BW1Term.rProf_init 0 θ hreg hgood hthr

end InteractingSLE.Theorem14.SB.Lk
