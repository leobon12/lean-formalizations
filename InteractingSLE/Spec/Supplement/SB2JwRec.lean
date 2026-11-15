/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JwRayUp
import InteractingSLE.Spec.Sec7.Lemma76EJunction
import InteractingSLE.WangWu.SideValues
import InteractingSLE.Spec.ZhanGT4.CrosscutRestart
import InteractingSLE.Spec.Dimension.TraceBridge
import InteractingSLE.Spec.Exist.StagedLaw3Path

/-!
# SB2(2): the right record of a tip-stopped piece (item 4a, deterministic)

Packet PROVE-SB2-LIFTSET (round 17). The ray correspondence needs the upper right record to be at most `R`. A record
grows only by swallowed real points, and:

* `exists_trace_real_ge`: a positive real point swallowed by a stop `T` strictly before the trace's horizon lies left
  of a real point of the trace on `[0, T]` (`Lemma76E.alive_of_trace_off`, contrapositive);
* `ginv_of_run`: beyond the record, the boundary map of a run chart inverts the real profile;
* **`rec_le_of_launch`**: through a piece stopped at an interior tip whose whole trace exists (beyond the stop), the new
  right record is at most any bound of the old record and of the new piece's real points.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.StagedLaw Exist.Staged Restart GW1W Lh

/-- A forward solution depends only on the driver on `[0, T]`. -/
theorem isForwardSol_congr_Icc {W W' : ℝ → ℝ} {z : ℂ} {T : ℝ} {u : ℝ → ℂ} (hu : QuantumZipper.IsForwardSol W z T u)
    (h : ∀ r ∈ Icc (0 : ℝ) T, W r = W' r) : QuantumZipper.IsForwardSol W' z T u :=
  ⟨hu.1, fun t ht => ⟨(hu.2 t ht).1, by rw [← h t ht]; exact (hu.2 t ht).2⟩⟩

/-- **A swallowed positive point lies left of a real point of the trace** (stop strictly before the horizon). -/
theorem exists_trace_real_ge {w : ℝ≥0 → ℝ} {ζ : ℝ≥0∞} {γ : ℝ≥0 → ℂ} (hg : IsGeneratingTrace w ζ γ)
    (hwc : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hw0 : w 0 = 0) {T : ℝ≥0} (hT : (T : ℝ≥0∞) < ζ) {y : ℝ}
    (hy : 0 < y) {W' : ℝ → ℝ} (hW' : ∀ r ∈ Icc (0 : ℝ) T, W' r = w r.toNNReal)
    (hsw : ¬ ∃ v, QuantumZipper.IsForwardSol W' (y : ℂ) T v) :
    ∃ s : ℝ≥0, s ≤ T ∧ ∃ r : ℝ, y ≤ r ∧ γ s = r := by
  by_contra hno
  push Not at hno
  obtain ⟨t₂, hTt₂, ht₂ζ⟩ := exists_real_btwn_of_lt hT
  have hal := Sec7.Lemma76E.alive_of_trace_off hg hwc hw0 ht₂ζ hTt₂ hy hno
  have hfc := continuous_frozenDrive_of_lt hwc ht₂ζ
  exact hsw ⟨_, isForwardSol_congr_Icc (WangWu.isForwardSol_of_alive hfc hal) fun r hr => by
    rw [hW' r hr, frozenDrive_eq ⟨hr.1, hr.2.trans hTt₂.le⟩]⟩

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **Beyond the record, the boundary map of a run chart inverts the real profile.** -/
theorem ginv_of_run (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hreg : ∀ k c θ', (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = some (c, θ') →
      GW1P.PieceRegular (D k).1 (min (instrTime spec k) (D k).2)) (n : ℕ)
    (hnot : stStatus (ExplState.run κ b jumps spec D n) ≠ GW1Conn.stDone) {u : ℝ}
    (hS : UState u (ExplState.run κ b jumps spec D n)) (hroot : spec.1 ≤ stRecR (ExplState.run κ b jumps spec D n)) :
    ∃ g : ℂ → ℂ, ContinuousOn g {z | 0 ≤ z.im} ∧ EqOn g (stChart (ExplState.run κ b jumps spec D n)).2.1 H ∧
      ∀ x : ℝ, stRecR (ExplState.run κ b jumps spec D n) < x →
        g (rProf (stChart (ExplState.run κ b jumps spec D n)) x) = x := by
  set s := ExplState.run κ b jumps spec D n with hsdef
  have hAc := Lx.isCompact_prefixPhysSet_run spec D hreg n hnot
  have hRA : ∀ y : ℝ, (y : ℂ) ∈ SB.prefixPhysSet κ b jumps spec D n → y ≤ stRecR s := by
    intro y hy
    obtain ⟨-, -, -, -, -, -, harc, hphys⟩ := hS
    rcases hy with (h1 | h2) | h3
    · have : y = spec.1 := by exact_mod_cast mem_singleton_iff.1 h1
      rw [this]; exact hroot
    · simp only [mem_iUnion, exists_prop] at h2
      obtain ⟨p, hp, hz⟩ := h2
      have := hphys p hp (y : ℂ) hz (by simp)
      simpa using this
    · simp only [mem_iUnion, exists_prop] at h3
      obtain ⟨a, ha, -⟩ := h3
      change a ∈ s.2.1 at ha
      rw [harc] at ha
      exact absurd ha (by simp)
  obtain ⟨-, -, he, ⟨g, hgc, hgi, -, hinv⟩, -⟩ := runRay_facts spec D hreg n hnot hAc rfl hRA
  obtain ⟨-, hc, -, -, hcontc, -⟩ := hS
  refine ⟨g, hgc, hgi, fun x hx => ?_⟩
  have heq : Lx.bdryValue (stChart s) x = rProf (stChart s) x := by
    have := GW1P.neBot_nhdsWithin_H (Lw.ofReal_mem_Hbar x)
    have h1 := (hcontc x hx).mono_right nhdsWithin_le_nhds
    rw [hc.eq_ofReal x] at h1
    exact_mod_cast tendsto_nhds_unique (he x hx) h1
  rw [← heq]
  exact hinv x hx

/-- **The new right record through a tip-stopped piece with a whole trace**: at most any bound of the old record and of
the new piece's real points. -/
theorem rec_le_of_launch {s : ExplState} {u : ℝ} (hs : UState u s) (k : ℕ) (θ : ℝ) {D : (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hreg : IsRegularDriver D) {t : ℝ≥0∞} (ht : t ≠ ⊤) (htD : t < D.2) (hfull : GW1P.PieceRegular D.1 D.2)
    {g : ℂ → ℂ} (hgc : ContinuousOn g {z | 0 ≤ z.im}) (hgi : EqOn g (stChart s).2.1 H)
    (hginv : ∀ x : ℝ, stRecR s < x → g (rProf (stChart s) x) = x) {y : ℝ} (hy : stRecR s ≤ y)
    (hpiece : ∀ x : ℝ, (x : ℂ) ∈ (stChart s).tipSet (fun r : ℝ≥0 => D.1 (min (r : ℝ≥0∞) (min t D.2)).toNNReal)
      (min t D.2) → x ≤ y) :
    stRecR (ExplState.launch s k D θ t) ≤ y := by
  obtain ⟨-, -, hsw, -⟩ := uState_launch hs k θ hreg ht htD
  obtain ⟨-, -, hm, hpos, -, -, -, -⟩ := hs
  by_contra hlt
  push Not at hlt
  obtain ⟨z, hyz, hzr⟩ := exists_between hlt
  have hrz : stRecR s < z := lt_of_le_of_lt hy hyz
  have hsz := hsw z hrz hzr
  -- the stop
  set T : ℝ≥0 := (min t D.2).toNNReal with hTdef
  have hmin : min t D.2 = t := min_eq_left htD.le
  have hTt : (T : ℝ≥0∞) = min t D.2 := by rw [hTdef, ENNReal.coe_toNNReal (by rw [hmin]; exact ht)]
  have hTζ : (T : ℝ≥0∞) < D.2 := by rw [hTt, hmin]; exact htD
  have hgood := isDrvGood_recOf_tip hreg ht htD
  have hfin : min t D.2 ≠ ⊤ := by rw [hmin]; exact ht
  have hrt : rtime (recOf t D) = (T : ℝ) := rtime_recOf_coe
  rw [hrt] at hsz
  have hW' : ∀ r ∈ Icc (0 : ℝ) T, rdrv (recOf t D) r = D.1 r.toNNReal := fun r hr =>
    rdrv_recOf_eq hreg hgood hfin (by rw [hrt]; exact hr.2)
  obtain ⟨hw0, hwc, α, hα, -⟩ := hfull
  have hwc' : ContinuousOn D.1 {w | (w : ℝ≥0∞) < D.2} := hwc.mono fun w hw =>
    le_of_lt (show (w : ℝ≥0∞) < D.2 from hw)
  obtain ⟨s', hs'T, r, hzr', hαs'⟩ := exists_trace_real_ge hα hwc' hw0 hTζ (hpos z hrz) hW' hsz
  -- the point of the ray with profile value `r`
  obtain ⟨x', hzx', hx'r⟩ : ∃ x', z ≤ x' ∧ rProf (stChart s) x' = r := by
    rcases eq_or_lt_of_le hzr' with heq | hlt'
    · exact ⟨z, le_rfl, heq⟩
    obtain ⟨x₁, hx₁, hrx₁⟩ := hm.2.2 r
    have hzx₁ : z < x₁ := by
      by_contra hle
      push Not at hle
      rcases eq_or_lt_of_le hle with h | h
      · rw [h] at hrx₁; linarith
      · linarith [hm.1 hx₁ hrz h]
    obtain ⟨x, hx, hxr⟩ := intermediate_value_Icc hzx₁.le (hm.2.1.mono fun w hw => lt_of_lt_of_le hrz hw.1)
      ⟨hlt'.le, hrx₁.le⟩
    exact ⟨x, hx.1, hxr⟩
  have hx'rec : stRecR s < x' := lt_of_lt_of_le hrz hzx'
  -- `x'` is a point of the new piece
  have hmem : (x' : ℂ) ∈ (stChart s).tipSet (fun r : ℝ≥0 => D.1 (min (r : ℝ≥0∞) (min t D.2)).toNNReal)
      (min t D.2) := by
    refine ⟨s', by rw [← hTt]; exact ENNReal.coe_le_coe.2 hs'T, ?_⟩
    obtain ⟨t₂, hTt₂, ht₂ζ⟩ := exists_real_btwn_of_lt hTζ
    have hs't₂ : (s' : ℝ) < t₂ := lt_of_le_of_lt (by exact_mod_cast hs'T) hTt₂
    -- the piece's driver is `D.1` frozen at the stop
    have hWs : (fun r : ℝ => D.1 (min (((r.toNNReal : ℝ≥0) : ℝ≥0∞)) (min t D.2)).toNNReal) =
        frozenDrive D.1 (T : ℝ) := by
      funext r
      rw [← hTt, frozenDrive]
      congr 1
      rw [← ENNReal.coe_min, ENNReal.toNNReal_coe, Monotone.map_min (fun _ _ h => Real.toNNReal_mono h),
        Real.toNNReal_coe]
    have hTc : ContinuousOn D.1 (Iic (T : ℝ).toNNReal) := hwc.mono fun w hw => by
      show (w : ℝ≥0∞) ≤ D.2
      rw [Real.toNNReal_coe] at hw
      exact (ENNReal.coe_le_coe.2 hw).trans hTζ.le
    have hcT : Continuous (frozenDrive D.1 (T : ℝ)) := continuous_frozenDrive hTc
    have hc₂ : Continuous (frozenDrive D.1 t₂) := continuous_frozenDrive_of_lt hwc' ht₂ζ
    have hT0 : frozenDrive D.1 (T : ℝ) 0 = 0 := by rw [frozenDrive_zero T.coe_nonneg, hw0]
    have ht₂0 : frozenDrive D.1 t₂ 0 = 0 := by
      rw [frozenDrive_zero ((NNReal.coe_nonneg s').trans hs't₂.le), hw0]
    have hsame : ∀ w ∈ H, QuantumZipper.fwdMapInv (frozenDrive D.1 (T : ℝ)) s' w =
        QuantumZipper.fwdMapInv (fun r : ℝ => D.1 r.toNNReal) s' w := by
      intro w hw
      rw [ZhanGT4.fwdMapInv_congr hcT hc₂ hT0 ht₂0 s'.coe_nonneg (fun r hr => by
        rw [frozenDrive_eq ⟨hr.1, hr.2.trans (by exact_mod_cast hs'T)⟩, frozenDrive_eq ⟨hr.1, hr.2.trans hs't₂.le⟩])
        hw]
      rw [fwdMapInv_eq_of_eqOn (W := frozenDrive D.1 t₂) (W' := fun r : ℝ => D.1 r.toNNReal) s'.coe_nonneg hs't₂
        (fun r hr => frozenDrive_eq hr)]
    have hlim := hα.tendsto_fwdMapInv_mul_I hwc' hw0 (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hs'T) hTζ)
    rw [hWs]
    have hIH : ∀ y : ℝ, 0 < y → (y : ℂ) * Complex.I ∈ H := fun y hy => by
      show 0 < ((y : ℂ) * Complex.I).im; simpa using hy
    have hinH : ∀ y : ℝ, 0 < y →
        QuantumZipper.fwdMapInv (frozenDrive D.1 (T : ℝ)) s' ((y : ℂ) * Complex.I) ∈ H := fun y hy =>
      QuantumZipper.RS.fwdMapInv_mem_H hcT hT0 s'.coe_nonneg (hIH y hy)
    have h1 : Tendsto (fun y : ℝ => QuantumZipper.fwdMapInv (frozenDrive D.1 (T : ℝ)) s' ((y : ℂ) * Complex.I))
        (𝓝[>] 0) (𝓝 (α s')) :=
      hlim.congr' (eventually_nhdsWithin_of_forall fun y hy => (hsame _ (hIH y hy)).symm)
    have hαH : α s' ∈ {z : ℂ | 0 ≤ z.im} := by rw [hαs']; simp
    have h2 : Tendsto (fun y : ℝ => g (QuantumZipper.fwdMapInv (frozenDrive D.1 (T : ℝ)) s' ((y : ℂ) * Complex.I)))
        (𝓝[>] 0) (𝓝 (g (α s'))) :=
      (hgc _ hαH).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨h1, eventually_nhdsWithin_of_forall fun y hy =>
        le_of_lt (show (0 : ℝ) < _ from hinH y hy)⟩)
    rw [hαs', ← hx'r, hginv x' hx'rec] at h2
    exact h2.congr' (eventually_nhdsWithin_of_forall fun y hy => hgi (hinH y hy))
  have := hpiece x' hmem
  linarith

end InteractingSLE.Theorem14.SB.Lk
