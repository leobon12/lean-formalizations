import InteractingSLE.Spec.Ito.Coordinates

/-!
# Exit times of the protection region: the pathwise part

Packet PROVE-T11-ITO2 (Specification §3.3 L519 and L550: "localize so that `inf Im g_t(z)` is bounded below by a
positive constant and the relevant continuous driving quantities are bounded … these localizations exhaust every
compact time interval"). For one path of the evolution and finitely many points `z_i ∈ ℍ`, `IsProtectedAt … t` says
that at time `t` the path is alive (`t < ζ`), `t ≤ σ₀`, `t ≤ N`, every `Im f_t(z_i) ≥ δ`, the coordinates `W_t, B_t,
V_t` are bounded by `R`, and the images `f_t(z_i)` are `ε`-separated. `protectedExitTime` is the infimum of the times
at which this fails.

* `isProtectedAt_of_lt_protectedExitTime`: the condition holds before the exit time;
* `isProtectedAt_of_le_protectedExitTime`: it holds at the exit time itself, if it holds at time `0` and `σ₀ < ζ`
  (a positive lower bound for `Im f_s(z)` on `[0, T)` keeps `z` alive at `T`, and the remaining conditions are
  closed);
* `eventually_nhdsGT_not_isProtectedAt`: the set of failure times is a right neighbourhood of each of its points,
  so the exit time is approached through any dense set of failure times (`protectedExitTime_lt_iff`);
* `le_protectedExitTime_of_forall`, `protectedExitTime_mono`: the exit time is at least every protected horizon and is
  monotone in the thresholds;
* `eventually_le_protectedExitTime`: every protected horizon lies below the exit times of all large levels.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology QuantumZipper
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Ito

/-! ### Loewner facts -/

/-- A point whose image has positive imaginary part has a forward solution (the junk value of `fwdMap` is `0`). -/
theorem exists_isForwardSol_of_im_pos {W : ℝ → ℝ} {T : ℝ} {z : ℂ} (h : 0 < (fwdMap W T z).im) :
    ∃ u, IsForwardSol W z T u := by
  by_contra hn
  have h0 : fwdMap W T z = 0 := by
    simp only [fwdMap, hn, ↓reduceDIte]
  rw [h0, Complex.zero_im] at h
  exact lt_irrefl 0 h

/-- At time `0` every point of `ℍ` has a forward solution. -/
theorem exists_isForwardSol_zero (W : ℝ → ℝ) {z : ℂ} (hz : 0 < z.im) : ∃ u, IsForwardSol W z 0 u := by
  refine ⟨fun _ => z - W 0, continuousOn_const, fun t ht => ?_⟩
  have ht0 : t = 0 := le_antisymm ht.2 ht.1
  subst ht0
  refine ⟨fun h => ?_, by simp⟩
  have := congrArg Complex.im h
  simp only [Complex.sub_im, Complex.ofReal_im, sub_zero, Complex.zero_im] at this
  exact hz.ne' this

/-- `f_0(z) = z − W_0`. -/
theorem fwdMap_zero_eq_sub (W : ℝ → ℝ) {z : ℂ} (hz : 0 < z.im) : fwdMap W 0 z = z - W 0 := by
  have h := fwdMap_eq_sub_add_integral_of_continuousOn (W := W) le_rfl
    (by rw [Icc_self]; exact continuousOn_singleton _ _) hz (exists_isForwardSol_zero W hz)
    (s := 0) ⟨le_rfl, le_rfl⟩
  rwa [intervalIntegral.integral_same, add_zero] at h

/-- **A positive lower bound for `Im f_s(z)` before `T` keeps `z` alive at `T`** (for a driver continuous on
`[0, T]`): otherwise `z` is swallowed by time `T`, and `inf_{s < τ(z)} Im f_s(z) = 0` (QuantumZipper's
`mem_fwdHull_iff_inf_im`, applied to the driver clamped to `[0, T]`). -/
theorem exists_isForwardSol_of_forall_lt {W : ℝ → ℝ} {T c : ℝ} {z : ℂ} (hT : 0 ≤ T)
    (hW : ContinuousOn W (Icc 0 T)) (hz : 0 < z.im) (hc : 0 < c)
    (h : ∀ s, 0 ≤ s → s < T → c ≤ (fwdMap W s z).im) : ∃ u, IsForwardSol W z T u := by
  by_contra hn
  have hWc := continuous_clampDrv hT hW
  have hmem : z ∈ fwdHull (clampDrv W T) T := by
    by_contra hmem
    obtain ⟨u, hu⟩ := exists_isForwardSol_of_mem hT ⟨hz, hmem⟩
    exact hn ⟨u, (isForwardSol_iff_of_eqOn (clampDrv_eqOn (W := W)) u).1 hu⟩
  obtain ⟨-, σ, hσT, -, hinf⟩ := (FwdClock.mem_fwdHull_iff_inf_im hWc).1 hmem
  obtain ⟨t, ht0, htσ, hlt⟩ := hinf c hc
  rw [fwdMap_clampDrv_of_le (htσ.le.trans hσT)] at hlt
  exact absurd (h t ht0 (htσ.trans_le hσT)) (not_le.2 hlt)

/-- Distinct points alive at time `T` have distinct images (QuantumZipper's `injOn_fwdMap`, applied to the driver
clamped to `[0, T]`). -/
theorem fwdMap_ne_of_ne {W : ℝ → ℝ} {T : ℝ} {y z : ℂ} (hT : 0 ≤ T) (hW : ContinuousOn W (Icc 0 T))
    (hy : 0 < y.im) (hz : 0 < z.im) (hyl : ∃ u, IsForwardSol W y T u) (hzl : ∃ u, IsForwardSol W z T u)
    (hyz : y ≠ z) : fwdMap W T y ≠ fwdMap W T z := by
  intro h
  refine hyz (FwdHolo.injOn_fwdMap (continuous_clampDrv hT hW) hT (mem_diff_fwdHull_clampDrv hT hW hy hyl)
    (mem_diff_fwdHull_clampDrv hT hW hz hzl) ?_)
  rwa [fwdMap_clampDrv_of_le le_rfl, fwdMap_clampDrv_of_le le_rfl]

/-! ### The protection condition and its exit time -/

section Protected

variable {nL nR k : ℕ} {zs : Fin k → ℂ} {δ ε R N : ℝ} {σ₀ : ℝ≥0} {ζ : ℝ≥0∞} {w : ℝ≥0 → ℝ}
  {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ}

/-- **The protection condition** of a path at time `t`, for the points `zs i`: `t < ζ`, `t ≤ σ₀`, `t ≤ N`, every
`Im f_t(z_i) ≥ δ` (so `z_i` is alive at `t`), `|W_t|, |B_t|, |V^{·,q}_t| ≤ R`, and the images `f_t(z_i)` are
pairwise at distance `≥ ε`. -/
def IsProtectedAt (zs : Fin k → ℂ) (δ ε R N : ℝ) (σ₀ : ℝ≥0) (ζ : ℝ≥0∞) (w : ℝ≥0 → ℝ)
    (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) (b : ℝ≥0 → ℝ) (t : ℝ≥0) : Prop :=
  (t : ℝ≥0∞) < ζ ∧ t ≤ σ₀ ∧ (t : ℝ) ≤ N ∧ (∀ i, δ ≤ (fwdMap (rpath w) t (zs i)).im) ∧
    |w t| ≤ R ∧ |b t| ≤ R ∧ (∀ i, |vL i t| ≤ R) ∧ (∀ i, |vR i t| ≤ R) ∧
    ∀ i j, i ≠ j → ε ≤ ‖fwdMap (rpath w) t (zs i) - fwdMap (rpath w) t (zs j)‖

/-- **The exit time** of the protection condition: the infimum of the times at which it fails. -/
def protectedExitTime (zs : Fin k → ℂ) (δ ε R N : ℝ) (σ₀ : ℝ≥0) (ζ : ℝ≥0∞) (w : ℝ≥0 → ℝ)
    (vL : Fin nL → ℝ≥0 → ℝ) (vR : Fin nR → ℝ≥0 → ℝ) (b : ℝ≥0 → ℝ) : ℝ≥0 :=
  sInf {t | ¬ IsProtectedAt zs δ ε R N σ₀ ζ w vL vR b t}

theorem IsProtectedAt.mono {t : ℝ≥0} (h : IsProtectedAt zs δ ε R N σ₀ ζ w vL vR b t) {δ' ε' R' N' : ℝ}
    (hδ : δ' ≤ δ) (hε : ε' ≤ ε) (hR : R ≤ R') (hN : N ≤ N') :
    IsProtectedAt zs δ' ε' R' N' σ₀ ζ w vL vR b t := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨h1, h2, h3.trans hN, fun i => hδ.trans (h4 i), h5.trans hR, h6.trans hR,
    fun i => (h7 i).trans hR, fun i => (h8 i).trans hR, fun i j hij => hε.trans (h9 i j hij)⟩

theorem IsProtectedAt.mono_sigma {t : ℝ≥0} (h : IsProtectedAt zs δ ε R N σ₀ ζ w vL vR b t) {σ₀' : ℝ≥0}
    (hσ : σ₀ ≤ σ₀') : IsProtectedAt zs δ ε R N σ₀' ζ w vL vR b t :=
  ⟨h.1, h.2.1.trans hσ, h.2.2⟩

theorem not_isProtectedAt_of_lt {t : ℝ≥0} (h : σ₀ < t) : ¬ IsProtectedAt zs δ ε R N σ₀ ζ w vL vR b t :=
  fun hp => not_le.2 h hp.2.1

theorem nonempty_not_isProtectedAt : {t | ¬ IsProtectedAt zs δ ε R N σ₀ ζ w vL vR b t}.Nonempty :=
  ⟨σ₀ + 1, not_isProtectedAt_of_lt (lt_add_one σ₀)⟩

theorem protectedExitTime_le_of_not {t : ℝ≥0} (h : ¬ IsProtectedAt zs δ ε R N σ₀ ζ w vL vR b t) :
    protectedExitTime zs δ ε R N σ₀ ζ w vL vR b ≤ t :=
  csInf_le (OrderBot.bddBelow _) h

theorem isProtectedAt_of_lt_protectedExitTime {t : ℝ≥0} (h : t < protectedExitTime zs δ ε R N σ₀ ζ w vL vR b) :
    IsProtectedAt zs δ ε R N σ₀ ζ w vL vR b t := by
  by_contra hn
  exact absurd (protectedExitTime_le_of_not hn) (not_le.2 h)

theorem protectedExitTime_le_sigma : protectedExitTime zs δ ε R N σ₀ ζ w vL vR b ≤ σ₀ :=
  le_of_forall_gt_imp_ge_of_dense fun _ hc => protectedExitTime_le_of_not (not_isProtectedAt_of_lt hc)

theorem le_protectedExitTime_of_forall {t : ℝ≥0} (h : ∀ s ≤ t, IsProtectedAt zs δ ε R N σ₀ ζ w vL vR b s) :
    t ≤ protectedExitTime zs δ ε R N σ₀ ζ w vL vR b := by
  refine le_csInf nonempty_not_isProtectedAt fun s hs => ?_
  by_contra hlt
  exact hs (h s (not_le.1 hlt).le)

theorem protectedExitTime_mono {δ' ε' R' N' : ℝ} (hδ : δ' ≤ δ) (hε : ε' ≤ ε) (hR : R ≤ R') (hN : N ≤ N') :
    protectedExitTime zs δ ε R N σ₀ ζ w vL vR b ≤ protectedExitTime zs δ' ε' R' N' σ₀ ζ w vL vR b :=
  csInf_le_csInf (OrderBot.bddBelow _) nonempty_not_isProtectedAt fun _ ht hp =>
    ht (hp.mono hδ hε hR hN)

theorem protectedExitTime_mono_sigma {σ₀' : ℝ≥0} (hσ : σ₀ ≤ σ₀') :
    protectedExitTime zs δ ε R N σ₀ ζ w vL vR b ≤ protectedExitTime zs δ ε R N σ₀' ζ w vL vR b :=
  csInf_le_csInf (OrderBot.bddBelow _) nonempty_not_isProtectedAt fun _ ht hp =>
    ht (hp.mono_sigma hσ)

/-- The protection condition at time `0`. -/
theorem isProtectedAt_zero (hz : ∀ i, 0 < (zs i).im) (hw0 : w 0 = 0) (hb0 : b 0 = 0)
    (hζ : 0 < ζ) (hδ : ∀ i, δ ≤ (zs i).im) (hε : ∀ i j, i ≠ j → ε ≤ ‖zs i - zs j‖) (hR : 0 ≤ R)
    (hvL : ∀ i, |vL i 0| ≤ R) (hvR : ∀ i, |vR i 0| ≤ R) (hN : 0 ≤ N) :
    IsProtectedAt zs δ ε R N σ₀ ζ w vL vR b 0 := by
  have hf : ∀ i, fwdMap (rpath w) ((0 : ℝ≥0) : ℝ) (zs i) = zs i := fun i => by
    rw [NNReal.coe_zero, fwdMap_zero_eq_sub _ (hz i)]
    simp [rpath, hw0]
  refine ⟨by simpa using hζ, zero_le, by simpa using hN, fun i => ?_, by simpa [hw0] using hR,
    by simpa [hb0] using hR, hvL, hvR, fun i j hij => ?_⟩
  · rw [hf i]; exact hδ i
  · rw [hf i, hf j]; exact hε i j hij

/-! ### Continuity: closedness of the condition, right-openness of its failure -/

/-- **The protection condition is closed along a protected stretch**: if `t₁` is alive (`t₁ < ζ`, every `z_i` alive
at `t₁`), `s ≤ t₁` satisfies the order conditions, and the condition holds frequently along a filter `l` that is
finer than the neighbourhoods of `s` within `[0, t₁]`, then it holds at `s`. -/
theorem isProtectedAt_of_frequently (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ})
    (hvL : ∀ i, ContinuousOn (vL i) {t | (t : ℝ≥0∞) < ζ})
    (hvR : ∀ i, ContinuousOn (vR i) {t | (t : ℝ≥0∞) < ζ}) (hb : Continuous b)
    (hz : ∀ i, 0 < (zs i).im) {l : Filter ℝ≥0} {s t₁ : ℝ≥0} (hst : s ≤ t₁) (hl : l ≤ 𝓝[Iic t₁] s)
    (hζ₁ : (t₁ : ℝ≥0∞) < ζ) (halive : ∀ i, ∃ u, IsForwardSol (rpath w) (zs i) t₁ u)
    (hsσ : s ≤ σ₀) (hsN : (s : ℝ) ≤ N) (hfreq : ∃ᶠ t in l, IsProtectedAt zs δ ε R N σ₀ ζ w vL vR b t) :
    IsProtectedAt zs δ ε R N σ₀ ζ w vL vR b s := by
  have hsub : Iic t₁ ⊆ {t | (t : ℝ≥0∞) < ζ} := fun t ht => lt_of_le_of_lt (by exact_mod_cast ht) hζ₁
  have hwc : ContinuousOn (rpath w) (Icc 0 (t₁ : ℝ)) := continuousOn_rpath hw hζ₁
  have hf : ∀ i, Tendsto (fun t : ℝ≥0 => fwdMap (rpath w) t (zs i)) l
      (𝓝 (fwdMap (rpath w) s (zs i))) := fun i => by
    have h1 := continuousOn_fwdMap_of_continuousOn t₁.coe_nonneg hwc (hz i) (halive i)
    have h2 : ContinuousOn (fun t : ℝ≥0 => fwdMap (rpath w) t (zs i)) (Iic t₁) :=
      h1.comp NNReal.continuous_coe.continuousOn fun t ht => ⟨t.coe_nonneg, by exact_mod_cast ht⟩
    exact (h2 s hst).tendsto.mono_left hl
  have hwt : Tendsto w l (𝓝 (w s)) := ((hw.mono hsub) s hst).tendsto.mono_left hl
  have hvLt : ∀ i, Tendsto (vL i) l (𝓝 (vL i s)) := fun i =>
    (((hvL i).mono hsub) s hst).tendsto.mono_left hl
  have hvRt : ∀ i, Tendsto (vR i) l (𝓝 (vR i s)) := fun i =>
    (((hvR i).mono hsub) s hst).tendsto.mono_left hl
  have hbt : Tendsto b l (𝓝 (b s)) := hb.continuousAt.tendsto.mono_left (hl.trans nhdsWithin_le_nhds)
  have habs : IsClosed {x : ℝ | |x| ≤ R} := isClosed_le continuous_abs continuous_const
  refine ⟨lt_of_le_of_lt (by exact_mod_cast hst) hζ₁, hsσ, hsN, fun i => ?_,
    habs.mem_of_frequently_of_tendsto (hfreq.mono fun t ht => ht.2.2.2.2.1) hwt,
    habs.mem_of_frequently_of_tendsto (hfreq.mono fun t ht => ht.2.2.2.2.2.1) hbt,
    fun i => habs.mem_of_frequently_of_tendsto (hfreq.mono fun t ht => ht.2.2.2.2.2.2.1 i) (hvLt i),
    fun i => habs.mem_of_frequently_of_tendsto (hfreq.mono fun t ht => ht.2.2.2.2.2.2.2.1 i) (hvRt i),
    fun i j hij => ?_⟩
  · exact (isClosed_le continuous_const Complex.continuous_im).mem_of_frequently_of_tendsto
      (hfreq.mono fun t ht => ht.2.2.2.1 i) (hf i)
  · exact (isClosed_le continuous_const continuous_norm).mem_of_frequently_of_tendsto
      (hfreq.mono fun t ht => ht.2.2.2.2.2.2.2.2 i j hij) ((hf i).sub (hf j))

/-- **The failure set is a right neighbourhood of each of its points.** -/
theorem eventually_nhdsGT_not_isProtectedAt (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ})
    (hvL : ∀ i, ContinuousOn (vL i) {t | (t : ℝ≥0∞) < ζ})
    (hvR : ∀ i, ContinuousOn (vR i) {t | (t : ℝ≥0∞) < ζ}) (hb : Continuous b)
    (hz : ∀ i, 0 < (zs i).im) (hδ : 0 < δ) {s : ℝ≥0}
    (hs : ¬ IsProtectedAt zs δ ε R N σ₀ ζ w vL vR b s) :
    ∀ᶠ t in 𝓝[>] s, ¬ IsProtectedAt zs δ ε R N σ₀ ζ w vL vR b t := by
  by_contra hcon
  rw [not_eventually] at hcon
  simp only [not_not] at hcon
  obtain ⟨t₁, ht₁, hst⟩ := (hcon.and_eventually self_mem_nhdsWithin).exists
  have halive : ∀ i, ∃ u, IsForwardSol (rpath w) (zs i) t₁ u := fun i =>
    exists_isForwardSol_of_im_pos (hδ.trans_le (ht₁.2.2.2.1 i))
  have hl : 𝓝[>] s ≤ 𝓝[Iic t₁] s := by
    rw [nhdsWithin_eq_nhds.2 (Iic_mem_nhds hst)]
    exact nhdsWithin_le_nhds
  exact hs (isProtectedAt_of_frequently hw hvL hvR hb hz hst.le hl ht₁.1 halive
    ((show s ≤ t₁ from hst.le).trans ht₁.2.1) (le_trans (by exact_mod_cast hst.le) ht₁.2.2.1) hcon)

/-- **The exit time is reached through any dense set of failure times.** -/
theorem protectedExitTime_lt_iff (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ})
    (hvL : ∀ i, ContinuousOn (vL i) {t | (t : ℝ≥0∞) < ζ})
    (hvR : ∀ i, ContinuousOn (vR i) {t | (t : ℝ≥0∞) < ζ}) (hb : Continuous b)
    (hz : ∀ i, 0 < (zs i).im) (hδ : 0 < δ) {D : Set ℝ≥0} (hD : Dense D) {t : ℝ≥0} :
    protectedExitTime zs δ ε R N σ₀ ζ w vL vR b < t ↔
      ∃ d ∈ D, d < t ∧ ¬ IsProtectedAt zs δ ε R N σ₀ ζ w vL vR b d := by
  constructor
  · intro h
    obtain ⟨s, hs, hst⟩ := exists_lt_of_csInf_lt nonempty_not_isProtectedAt h
    have hev := (eventually_nhdsGT_not_isProtectedAt hw hvL hvR hb hz hδ hs).and
      (Ioo_mem_nhdsGT hst)
    obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
    obtain ⟨d, hdD, hd⟩ := hD.exists_between hu
    exact ⟨d, hdD, (hsub hd).2.2, (hsub hd).1⟩
  · rintro ⟨d, -, hdt, hd⟩
    exact (protectedExitTime_le_of_not hd).trans_lt hdt

/-- **The protection condition holds up to and including the exit time**, when it holds at time `0` and
`σ₀ < ζ`. -/
theorem isProtectedAt_of_le_protectedExitTime (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ})
    (hvL : ∀ i, ContinuousOn (vL i) {t | (t : ℝ≥0∞) < ζ})
    (hvR : ∀ i, ContinuousOn (vR i) {t | (t : ℝ≥0∞) < ζ}) (hb : Continuous b)
    (hz : ∀ i, 0 < (zs i).im) (hδ : 0 < δ) (hσ₀ : (σ₀ : ℝ≥0∞) < ζ)
    (h0 : IsProtectedAt zs δ ε R N σ₀ ζ w vL vR b 0) {s : ℝ≥0}
    (hs : s ≤ protectedExitTime zs δ ε R N σ₀ ζ w vL vR b) : IsProtectedAt zs δ ε R N σ₀ ζ w vL vR b s := by
  rcases hs.lt_or_eq with hs | hs
  · exact isProtectedAt_of_lt_protectedExitTime hs
  subst hs
  set ρ := protectedExitTime zs δ ε R N σ₀ ζ w vL vR b with hρdef
  rcases (show (0 : ℝ≥0) ≤ ρ from zero_le).eq_or_lt with hρ | hρ
  · rw [← hρ]; exact h0
  have hρσ : ρ ≤ σ₀ := protectedExitTime_le_sigma
  have hρζ : (ρ : ℝ≥0∞) < ζ := lt_of_le_of_lt (by exact_mod_cast hρσ) hσ₀
  have hwc : ContinuousOn (rpath w) (Icc 0 (ρ : ℝ)) := continuousOn_rpath hw hρζ
  have hbefore : ∀ s < ρ, IsProtectedAt zs δ ε R N σ₀ ζ w vL vR b s := fun s hs =>
    isProtectedAt_of_lt_protectedExitTime hs
  have halive : ∀ i, ∃ u, IsForwardSol (rpath w) (zs i) ρ u := fun i =>
    exists_isForwardSol_of_forall_lt ρ.coe_nonneg hwc (hz i) hδ fun s hs0 hsρ => by
      have h := (hbefore s.toNNReal (by rwa [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hs0])).2.2.2.1 i
      rwa [Real.coe_toNNReal _ hs0] at h
  have hρN : (ρ : ℝ) ≤ N := by
    have hN0 : (0 : ℝ) ≤ N := by simpa using h0.2.2.1
    have hle : ρ ≤ N.toNNReal := le_of_forall_gt_imp_ge_of_dense fun c hc =>
      protectedExitTime_le_of_not fun hp => absurd hc (not_lt.2 ((Real.le_toNNReal_iff_coe_le hN0).2 hp.2.2.1))
    simpa [Real.coe_toNNReal _ hN0] using (NNReal.coe_le_coe.2 hle)
  have : (𝓝[<] ρ).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hρ⟩
  exact isProtectedAt_of_frequently hw hvL hvR hb hz le_rfl (nhdsWithin_mono _ Iio_subset_Iic_self)
    hρζ halive hρσ hρN (eventually_nhdsWithin_of_forall (s := Iio ρ) fun s hs => hbefore s hs).frequently

end Protected

/-! ### Exhaustion by levels -/

theorem eventually_div_succ_le (m : ℝ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, m / ((n : ℝ) + 1) ≤ c := by
  filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop (m / c)] with n hn
  rw [div_le_iff₀ (by positivity)]
  have := (div_le_iff₀ hc).1 hn
  nlinarith

theorem eventually_le_natCast_add (a C : ℝ) : ∀ᶠ n : ℕ in atTop, a ≤ (n : ℝ) + C := by
  filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop (a - C)] with n hn
  linarith

/-- **Every protected horizon is eventually inside the protection region of level `n`**, the level with thresholds
`δ = m/(n+1)`, `ε = e/(n+1)`, `R = n + C`, `N = n`: if `t ≤ σ₀`, `t < ζ` and the distinct points `z_i` are alive at
`t`, then `t ≤ protectedExitTime` for all large `n` (compactness of `[0, t]`: the coordinates are bounded there,
`Im f_s(z_i)` decreases in `s`, and the distances `|f_s(z_i) − f_s(z_j)|` are positive and continuous). -/
theorem eventually_le_protectedExitTime {nL nR k : ℕ} {zs : Fin k → ℂ} {σ₀ : ℝ≥0} {ζ : ℝ≥0∞} {w : ℝ≥0 → ℝ}
    {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ}
    (hw : ContinuousOn w {t | (t : ℝ≥0∞) < ζ}) (hvL : ∀ i, ContinuousOn (vL i) {t | (t : ℝ≥0∞) < ζ})
    (hvR : ∀ i, ContinuousOn (vR i) {t | (t : ℝ≥0∞) < ζ}) (hb : Continuous b)
    (hz : ∀ i, 0 < (zs i).im) (hinj : Function.Injective zs) (m e : ℝ)
    (C : ℝ) {t : ℝ≥0} (htσ : t ≤ σ₀) (htζ : (t : ℝ≥0∞) < ζ)
    (halive : ∀ i, ∃ u, IsForwardSol (rpath w) (zs i) t u) :
    ∀ᶠ n : ℕ in atTop, t ≤ protectedExitTime zs (m / ((n : ℝ) + 1)) (e / ((n : ℝ) + 1)) ((n : ℝ) + C) n σ₀ ζ
      w vL vR b := by
  have hsub : Iic t ⊆ {s | (s : ℝ≥0∞) < ζ} := fun s hs => lt_of_le_of_lt (by exact_mod_cast hs) htζ
  have hwc : ContinuousOn (rpath w) (Icc 0 (t : ℝ)) := continuousOn_rpath hw htζ
  have hK : IsCompact (Iic t) := by
    simpa only [Icc_bot] using (isCompact_Icc : IsCompact (Icc (⊥ : ℝ≥0) t))
  have hfc : ∀ i, ContinuousOn (fun s : ℝ≥0 => fwdMap (rpath w) s (zs i)) (Iic t) := fun i =>
    (continuousOn_fwdMap_of_continuousOn t.coe_nonneg hwc (hz i) (halive i)).comp
      NNReal.continuous_coe.continuousOn fun s hs => ⟨s.coe_nonneg, by exact_mod_cast hs⟩
  obtain ⟨Cw, hCw⟩ := hK.exists_bound_of_continuousOn (hw.mono hsub)
  obtain ⟨Cb, hCb⟩ := hK.exists_bound_of_continuousOn (s := Iic t) hb.continuousOn
  have hCL : ∀ i, ∃ C', ∀ s ∈ Iic t, ‖vL i s‖ ≤ C' := fun i =>
    hK.exists_bound_of_continuousOn ((hvL i).mono hsub)
  have hCR : ∀ i, ∃ C', ∀ s ∈ Iic t, ‖vR i s‖ ≤ C' := fun i =>
    hK.exists_bound_of_continuousOn ((hvR i).mono hsub)
  have hsep : ∀ i j, i ≠ j → ∃ c > 0, ∀ s ∈ Iic t,
      c ≤ ‖fwdMap (rpath w) s (zs i) - fwdMap (rpath w) s (zs j)‖ := by
    intro i j hij
    obtain ⟨s₀, hs₀, hmin⟩ := hK.exists_isMinOn nonempty_Iic (((hfc i).sub (hfc j)).norm)
    have hs₀t : (s₀ : ℝ) ≤ t := by exact_mod_cast hs₀
    have hal : ∀ l, ∃ u, IsForwardSol (rpath w) (zs l) s₀ u := fun l => by
      obtain ⟨u, hu⟩ := halive l
      exact ⟨u, isForwardSol_of_le hu s₀.coe_nonneg hs₀t⟩
    refine ⟨_, norm_pos_iff.2 (sub_ne_zero.2 (fwdMap_ne_of_ne s₀.coe_nonneg
      (hwc.mono (Icc_subset_Icc_right hs₀t)) (hz i) (hz j) (hal i) (hal j) (hinj.ne hij))),
      fun s hs => hmin hs⟩
  have him : ∀ i, 0 < (fwdMap (rpath w) t (zs i)).im := fun i =>
    im_fwdMap_pos_of_continuousOn t.coe_nonneg hwc (hz i) (halive i) ⟨t.coe_nonneg, le_rfl⟩
  have hanti : ∀ i, AntitoneOn (fun s => (fwdMap (rpath w) s (zs i)).im) (Icc 0 (t : ℝ)) := fun i =>
    antitoneOn_im_fwdMap_of_continuousOn t.coe_nonneg hwc (hz i) (halive i)
  have h1 : ∀ᶠ n : ℕ in atTop, (t : ℝ) ≤ n := tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  have h2 : ∀ᶠ n : ℕ in atTop, ∀ i, m / ((n : ℝ) + 1) ≤ (fwdMap (rpath w) t (zs i)).im :=
    eventually_all.2 fun i => eventually_div_succ_le m (him i)
  have h3 : ∀ᶠ n : ℕ in atTop, ∀ s ∈ Iic t, |w s| ≤ (n : ℝ) + C ∧ |b s| ≤ (n : ℝ) + C ∧
      (∀ i, |vL i s| ≤ (n : ℝ) + C) ∧ ∀ i, |vR i s| ≤ (n : ℝ) + C := by
    have hL : ∀ᶠ n : ℕ in atTop, ∀ i, ∀ s ∈ Iic t, |vL i s| ≤ (n : ℝ) + C :=
      eventually_all.2 fun i => by
        obtain ⟨C', hC'⟩ := hCL i
        filter_upwards [eventually_le_natCast_add C' C] with n hn s hs
        exact (hC' s hs).trans hn
    have hR : ∀ᶠ n : ℕ in atTop, ∀ i, ∀ s ∈ Iic t, |vR i s| ≤ (n : ℝ) + C :=
      eventually_all.2 fun i => by
        obtain ⟨C', hC'⟩ := hCR i
        filter_upwards [eventually_le_natCast_add C' C] with n hn s hs
        exact (hC' s hs).trans hn
    filter_upwards [eventually_le_natCast_add Cw C, eventually_le_natCast_add Cb C, hL, hR] with
      n hw' hb' hL' hR' s hs
    exact ⟨(hCw s hs).trans hw', (hCb s hs).trans hb', fun i => hL' i s hs, fun i => hR' i s hs⟩
  have h4 : ∀ᶠ n : ℕ in atTop, ∀ i j, i ≠ j → ∀ s ∈ Iic t,
      e / ((n : ℝ) + 1) ≤ ‖fwdMap (rpath w) s (zs i) - fwdMap (rpath w) s (zs j)‖ :=
    eventually_all.2 fun i => eventually_all.2 fun j => by
      by_cases hij : i = j
      · exact Eventually.of_forall fun _ h => absurd hij h
      obtain ⟨c, hc, hcs⟩ := hsep i j hij
      filter_upwards [eventually_div_succ_le e hc] with n hn _ s hs using hn.trans (hcs s hs)
  filter_upwards [h1, h2, h3, h4] with n hn1 hn2 hn3 hn4
  refine le_protectedExitTime_of_forall fun s hs => ?_
  have hst : (s : ℝ) ≤ t := by exact_mod_cast hs
  obtain ⟨hsw, hsb, hsL, hsR⟩ := hn3 s hs
  exact ⟨lt_of_le_of_lt (by exact_mod_cast hs) htζ, hs.trans htσ, hst.trans hn1,
    fun i => (hn2 i).trans (hanti i ⟨s.coe_nonneg, hst⟩ ⟨t.coe_nonneg, le_rfl⟩ hst), hsw, hsb, hsL, hsR,
    fun i j hij => hn4 i j hij s hs⟩

end Ito

end InteractingSLE
