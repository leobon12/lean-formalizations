import SupercriticalLQGUniqueness.B2.PfeAxioms.AroundSectorBound
import SupercriticalLQGUniqueness.B2.PfeLocal.AnnulusEvent

 















set_option autoImplicit false
noncomputable section

open Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeLocal

open SupercriticalLQGUniqueness.B2.Strong

 

 
def l1BoxShift (B : Box) (s : ℝ) : Box := ⟨B.x₀ + s, B.x₁ + s, B.y₀, B.y₁⟩

 
def l1BoxShrink (B : Box) (e : ℝ) : Box := ⟨B.x₀ + e, B.x₁ - e, B.y₀ + e, B.y₁ - e⟩

theorem l1_cfgU_shift (L Δ s : ℝ) (k : Fin 4) :
    cfgU (L + s) Δ k = l1BoxShift (cfgU L Δ k) s := by
  fin_cases k <;> simp only [cfgU, boxR, boxA, l1BoxShift] <;> congr 1 <;> ring

theorem l1_cfgK₁_shift (L Δ s : ℝ) (k : Fin 4) :
    cfgK₁ (L + s) Δ k = l1BoxShift (cfgK₁ L Δ k) s := by
  fin_cases k <;> simp only [cfgK₁, segR, segA, l1BoxShift] <;> congr 1 <;> ring

theorem l1_cfgK₂_shift (L Δ s : ℝ) (k : Fin 4) :
    cfgK₂ (L + s) Δ k = l1BoxShift (cfgK₂ L Δ k) s := by
  fin_cases k <;> simp only [cfgK₂, segR, segA, l1BoxShift] <;> congr 1 <;> ring

theorem l1_shrink_shift (B : Box) (e s : ℝ) :
    l1BoxShrink (l1BoxShift B s) e = l1BoxShift (l1BoxShrink B e) s := by
  simp only [l1BoxShrink, l1BoxShift]; congr 1 <;> ring

theorem l1_exp_shift (z : ℂ) {r : ℝ} (hr : 0 < r) (w : ℂ) :
    z + (r : ℂ) * expChart 0 w = expChart z (w + (Real.log r : ℂ)) := by
  simp only [expChart, zero_add, Complex.exp_add]
  rw [← Complex.ofReal_exp, Real.exp_log hr]
  ring

theorem l1_mem_shift_openSet {B : Box} {w : ℂ} (s : ℝ) (hw : w ∈ B.openSet) :
    w + (s : ℂ) ∈ (l1BoxShift B s).openSet := by
  obtain ⟨h1, h2, h3, h4⟩ := hw
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [l1BoxShift, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, add_zero] <;> linarith

theorem l1_mem_shift_closedSet {B : Box} {w : ℂ} (s : ℝ) (hw : w ∈ B.closedSet) :
    w + (s : ℂ) ∈ (l1BoxShift B s).closedSet := by
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hw
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    simp only [l1BoxShift, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, add_zero] <;> linarith

theorem l1_mem_unshift_openSet {B : Box} {w : ℂ} (s : ℝ)
    (hw : w ∈ (l1BoxShift B s).openSet) : w - (s : ℂ) ∈ B.openSet := by
  obtain ⟨h1, h2, h3, h4⟩ := hw
  simp only [l1BoxShift] at h1 h2 h3 h4
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, sub_zero] <;> linarith

theorem l1_mem_unshift_closedSet {B : Box} {w : ℂ} (s : ℝ)
    (hw : w ∈ (l1BoxShift B s).closedSet) : w - (s : ℂ) ∈ B.closedSet := by
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hw
  simp only [l1BoxShift] at h1 h2 h3 h4
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, sub_zero] <;> linarith

theorem l1_image_polarOpen (z : ℂ) {r : ℝ} (hr : 0 < r) (B : Box) :
    (fun u => z + (r : ℂ) * u) '' polarOpen 0 B =
      polarOpen z (l1BoxShift B (Real.log r)) := by
  ext x
  constructor
  · rintro ⟨u, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨w + (Real.log r : ℂ), l1_mem_shift_openSet _ hw,
      (l1_exp_shift z hr w).symm⟩
  · rintro ⟨w, hw, rfl⟩
    refine ⟨expChart 0 (w - (Real.log r : ℂ)),
      ⟨_, l1_mem_unshift_openSet _ hw, rfl⟩, ?_⟩
    simp only
    rw [l1_exp_shift z hr, sub_add_cancel]

theorem l1_image_polarClosed (z : ℂ) {r : ℝ} (hr : 0 < r) (B : Box) :
    (fun u => z + (r : ℂ) * u) '' polarClosed 0 B =
      polarClosed z (l1BoxShift B (Real.log r)) := by
  ext x
  constructor
  · rintro ⟨u, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨w + (Real.log r : ℂ), l1_mem_shift_closedSet _ hw,
      (l1_exp_shift z hr w).symm⟩
  · rintro ⟨w, hw, rfl⟩
    refine ⟨expChart 0 (w - (Real.log r : ℂ)),
      ⟨_, l1_mem_unshift_closedSet _ hw, rfl⟩, ?_⟩
    simp only
    rw [l1_exp_shift z hr, sub_add_cancel]

 

 
def l1Δ : ℝ := Real.log 2 / 16

theorem l1Δ_pos : 0 < l1Δ := by
  unfold l1Δ; have := Real.log_pos one_lt_two; positivity

theorem l1Δ_lt_wd : l1Δ < wd := by
  unfold l1Δ wd
  have h1 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  have h2 : 3 < Real.pi := Real.pi_gt_three
  linarith

theorem l1_annL_outer (z : ℂ) (r : ℝ) (hr : 0 < r) :
    annL (outerAnnulus z r hr) = Real.log r := rfl

theorem l1_annΔ_outer (z : ℂ) (r : ℝ) (hr : 0 < r) :
    annΔ (outerAnnulus z r hr) = l1Δ := by
  unfold annΔ l1Δ
  change (Real.log (2 * r) - Real.log r) / 16 = Real.log 2 / 16
  rw [Real.log_mul two_ne_zero hr.ne']
  ring

theorem l1_cfgOpens_outer (z : ℂ) (r : ℝ) (hr : 0 < r) (k : Fin 4) :
    (cfgOpens (outerAnnulus z r hr) k : Set ℂ) =
      polarOpen z (cfgU (Real.log r) l1Δ k) := by
  change polarOpen (outerAnnulus z r hr).center
      (cfgU (annL (outerAnnulus z r hr)) (annΔ (outerAnnulus z r hr)) k) = _
  rw [l1_annL_outer, l1_annΔ_outer]
  rfl

theorem l1_cfgSet₁_outer (z : ℂ) (r : ℝ) (hr : 0 < r) (k : Fin 4) :
    cfgSet₁ (outerAnnulus z r hr) k = polarClosed z (cfgK₁ (Real.log r) l1Δ k) := by
  change polarClosed (outerAnnulus z r hr).center
      (cfgK₁ (annL (outerAnnulus z r hr)) (annΔ (outerAnnulus z r hr)) k) = _
  rw [l1_annL_outer, l1_annΔ_outer]
  rfl

theorem l1_cfgSet₂_outer (z : ℂ) (r : ℝ) (hr : 0 < r) (k : Fin 4) :
    cfgSet₂ (outerAnnulus z r hr) k = polarClosed z (cfgK₂ (Real.log r) l1Δ k) := by
  change polarClosed (outerAnnulus z r hr).center
      (cfgK₂ (annL (outerAnnulus z r hr)) (annΔ (outerAnnulus z r hr)) k) = _
  rw [l1_annL_outer, l1_annΔ_outer]
  rfl

 

 
def l1AroundBox (L : ℝ) (k : Fin 4) : Box := l1BoxShrink (cfgU L l1Δ k) (l1Δ / 2)

 
def l1AroundOpen (z : ℂ) (r : ℝ) (k : Fin 4) : Set ℂ :=
  polarOpen z (l1AroundBox (Real.log r) k)

 
def l1AroundClosed (z : ℂ) (r : ℝ) (k : Fin 4) : Set ℂ :=
  polarClosed z (l1AroundBox (Real.log r) k)

 
def l1StartLog (k : Fin 4) : ℂ := ⟨(cfgK₁ 0 l1Δ k).x₀, (cfgK₁ 0 l1Δ k).y₀⟩

 
def l1EndLog (k : Fin 4) : ℂ := ⟨(cfgK₂ 0 l1Δ k).x₀, (cfgK₂ 0 l1Δ k).y₀⟩

 
def l1Start (z : ℂ) (r : ℝ) (k : Fin 4) : ℂ :=
  expChart z (l1StartLog k + (Real.log r : ℂ))

 
def l1End (z : ℂ) (r : ℝ) (k : Fin 4) : ℂ :=
  expChart z (l1EndLog k + (Real.log r : ℂ))

theorem l1_aroundBox_shift (L : ℝ) (k : Fin 4) :
    l1AroundBox L k = l1BoxShift (l1AroundBox 0 k) L := by
  unfold l1AroundBox
  rw [← l1_shrink_shift, ← l1_cfgU_shift, zero_add]

theorem l1_aroundBox_nondeg (L : ℝ) (k : Fin 4) :
    (l1AroundBox L k).x₀ < (l1AroundBox L k).x₁ ∧
      (l1AroundBox L k).y₀ < (l1AroundBox L k).y₁ := by
  have hΔ := l1Δ_pos
  have hw := l1Δ_lt_wd
  have := wd_pos
  have := Real.pi_pos
  fin_cases k <;> refine ⟨?_, ?_⟩ <;>
    simp [l1AroundBox, l1BoxShrink, cfgU, boxR, boxA] <;> linarith

theorem l1_aroundBox_closed_subset (L : ℝ) (k : Fin 4) :
    (l1AroundBox L k).closedSet ⊆ (cfgU L l1Δ k).openSet := by
  have hΔ := l1Δ_pos
  exact Box.closedSet_subset_openSet
    (by simp only [l1AroundBox, l1BoxShrink]; linarith)
    (by simp only [l1AroundBox, l1BoxShrink]; linarith)
    (by simp only [l1AroundBox, l1BoxShrink]; linarith)
    (by simp only [l1AroundBox, l1BoxShrink]; linarith)

theorem l1_cfgK₁_subset_aroundBox (L : ℝ) (k : Fin 4) :
    (cfgK₁ L l1Δ k).closedSet ⊆ (l1AroundBox L k).openSet := by
  have hΔ := l1Δ_pos
  have hw := l1Δ_lt_wd
  have := wd_pos
  have h8 : 8 * wd = Real.pi := by unfold wd; ring
  fin_cases k <;>
    exact Box.closedSet_subset_openSet
      (by simp [cfgK₁, l1AroundBox, l1BoxShrink, cfgU, boxR, segR, boxA, segA]; linarith)
      (by simp [cfgK₁, l1AroundBox, l1BoxShrink, cfgU, boxR, segR, boxA, segA]; linarith)
      (by simp [cfgK₁, l1AroundBox, l1BoxShrink, cfgU, boxR, segR, boxA, segA]; linarith)
      (by simp [cfgK₁, l1AroundBox, l1BoxShrink, cfgU, boxR, segR, boxA, segA]; linarith)

theorem l1_cfgK₂_subset_aroundBox (L : ℝ) (k : Fin 4) :
    (cfgK₂ L l1Δ k).closedSet ⊆ (l1AroundBox L k).openSet := by
  have hΔ := l1Δ_pos
  have hw := l1Δ_lt_wd
  have := wd_pos
  have h8 : 8 * wd = Real.pi := by unfold wd; ring
  fin_cases k <;>
    exact Box.closedSet_subset_openSet
      (by simp [cfgK₂, l1AroundBox, l1BoxShrink, cfgU, boxR, segR, boxA, segA]; linarith)
      (by simp [cfgK₂, l1AroundBox, l1BoxShrink, cfgU, boxR, segR, boxA, segA]; linarith)
      (by simp [cfgK₂, l1AroundBox, l1BoxShrink, cfgU, boxR, segR, boxA, segA]; linarith)
      (by simp [cfgK₂, l1AroundBox, l1BoxShrink, cfgU, boxR, segR, boxA, segA]; linarith)

theorem l1_startLog_mem (L : ℝ) (k : Fin 4) :
    l1StartLog k + (L : ℂ) ∈ (cfgK₁ L l1Δ k).closedSet := by
  have hle := cfgK₁_le 0 l1Δ l1Δ_pos k
  have hmem : l1StartLog k ∈ (cfgK₁ 0 l1Δ k).closedSet :=
    ⟨⟨le_rfl, hle.1⟩, ⟨le_rfl, hle.2⟩⟩
  have := l1_mem_shift_closedSet L hmem
  rwa [← l1_cfgK₁_shift, zero_add] at this

theorem l1_endLog_mem (L : ℝ) (k : Fin 4) :
    l1EndLog k + (L : ℂ) ∈ (cfgK₂ L l1Δ k).closedSet := by
  have hle := cfgK₂_le 0 l1Δ l1Δ_pos k
  have hmem : l1EndLog k ∈ (cfgK₂ 0 l1Δ k).closedSet :=
    ⟨⟨le_rfl, hle.1⟩, ⟨le_rfl, hle.2⟩⟩
  have := l1_mem_shift_closedSet L hmem
  rwa [← l1_cfgK₂_shift, zero_add] at this

theorem isOpen_l1AroundOpen (z : ℂ) (r : ℝ) (k : Fin 4) : IsOpen (l1AroundOpen z r k) :=
  isOpen_polarOpen _ _

theorem isConnected_l1AroundOpen (z : ℂ) (r : ℝ) (k : Fin 4) :
    IsConnected (l1AroundOpen z r k) :=
  isConnected_polarOpen _ _ (l1_aroundBox_nondeg _ k).1 (l1_aroundBox_nondeg _ k).2

theorem isCompact_l1AroundClosed (z : ℂ) (r : ℝ) (k : Fin 4) :
    IsCompact (l1AroundClosed z r k) :=
  isCompact_polarClosed _ _

theorem l1AroundOpen_subset_closed (z : ℂ) (r : ℝ) (k : Fin 4) :
    l1AroundOpen z r k ⊆ l1AroundClosed z r k := by
  rintro _ ⟨w, ⟨h1, h2, h3, h4⟩, rfl⟩
  exact ⟨w, ⟨⟨h1.le, h2.le⟩, ⟨h3.le, h4.le⟩⟩, rfl⟩

theorem l1AroundClosed_subset_cfgOpens (z : ℂ) (r : ℝ) (hr : 0 < r) (k : Fin 4) :
    l1AroundClosed z r k ⊆ (cfgOpens (outerAnnulus z r hr) k : Set ℂ) := by
  rw [l1_cfgOpens_outer]
  exact polarClosed_subset z (l1_aroundBox_closed_subset _ k)

theorem l1Start_mem_cfgSet₁ (z : ℂ) (r : ℝ) (hr : 0 < r) (k : Fin 4) :
    l1Start z r k ∈ cfgSet₁ (outerAnnulus z r hr) k := by
  rw [l1_cfgSet₁_outer]
  exact ⟨_, l1_startLog_mem _ k, rfl⟩

theorem l1End_mem_cfgSet₂ (z : ℂ) (r : ℝ) (hr : 0 < r) (k : Fin 4) :
    l1End z r k ∈ cfgSet₂ (outerAnnulus z r hr) k := by
  rw [l1_cfgSet₂_outer]
  exact ⟨_, l1_endLog_mem _ k, rfl⟩

theorem l1Start_mem_aroundOpen (z : ℂ) (r : ℝ) (k : Fin 4) :
    l1Start z r k ∈ l1AroundOpen z r k :=
  ⟨_, l1_cfgK₁_subset_aroundBox _ k (l1_startLog_mem _ k), rfl⟩

theorem l1End_mem_aroundOpen (z : ℂ) (r : ℝ) (k : Fin 4) :
    l1End z r k ∈ l1AroundOpen z r k :=
  ⟨_, l1_cfgK₂_subset_aroundBox _ k (l1_endLog_mem _ k), rfl⟩

theorem l1Start_ne_end (z : ℂ) (r : ℝ) (k : Fin 4) : l1Start z r k ≠ l1End z r k := by
  intro h
  have hinj := injOn_openSet z (cfgU (Real.log r) l1Δ k) (cfgU_height _ _ k)
  have h1 := cfgK₁_subset (Real.log r) l1Δ l1Δ_pos k (l1_startLog_mem (Real.log r) k)
  have h2 := cfgK₂_subset (Real.log r) l1Δ l1Δ_pos k (l1_endLog_mem (Real.log r) k)
  have heq := hinj h1 h2 h
  exact Set.disjoint_left.1 (cfgK_disjoint (Real.log r) l1Δ l1Δ_pos k)
    (l1_startLog_mem (Real.log r) k) (heq ▸ l1_endLog_mem (Real.log r) k)

 
theorem l1_image_aroundOpen (z : ℂ) {r : ℝ} (hr : 0 < r) (k : Fin 4) :
    (fun u => z + (r : ℂ) * u) '' l1AroundOpen 0 1 k = l1AroundOpen z r k := by
  unfold l1AroundOpen
  rw [Real.log_one, l1_image_polarOpen z hr, ← l1_aroundBox_shift]

theorem l1_image_start (z : ℂ) {r : ℝ} (hr : 0 < r) (k : Fin 4) :
    z + (r : ℂ) * l1Start 0 1 k = l1Start z r k := by
  unfold l1Start
  rw [Real.log_one, Complex.ofReal_zero, add_zero, l1_exp_shift z hr]

theorem l1_image_end (z : ℂ) {r : ℝ} (hr : 0 < r) (k : Fin 4) :
    z + (r : ℂ) * l1End 0 1 k = l1End z r k := by
  unfold l1End
  rw [Real.log_one, Complex.ofReal_zero, add_zero, l1_exp_shift z hr]

 

 
def l1Shell : Set ℂ := {u | 1 / 2 - 1 / 256 ≤ ‖u‖ ∧ ‖u‖ ≤ 1 / 2 + 1 / 256}

theorem isCompact_l1Shell : IsCompact l1Shell := by
  have hc : IsClosed l1Shell :=
    (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)
  exact (isCompact_closedBall (0 : ℂ) (1 / 2 + 1 / 256)).of_isClosed_subset hc
    (fun u hu => by rw [mem_closedBall, dist_zero_right]; exact hu.2)

 
theorem exists_l1AcrossNet :
    ∃ q : Finset ℂ, (∀ i ∈ q, i ∈ l1Shell) ∧
      l1Shell ⊆ ⋃ i ∈ q, ball i (1 / 128) := by
  obtain ⟨t, hts, htf, hcov⟩ :=
    finite_cover_balls_of_compact isCompact_l1Shell (by norm_num : (0 : ℝ) < 1 / 128)
  refine ⟨htf.toFinset, fun i hi => hts (htf.mem_toFinset.1 hi), ?_⟩
  intro u hu
  obtain ⟨i, hi, hui⟩ := mem_iUnion₂.1 (hcov hu)
  exact mem_iUnion₂.2 ⟨i, htf.mem_toFinset.2 hi, hui⟩

 
def l1d : ℝ := 1 / 8

 

theorem l1_net_cover (q : Finset ℂ) (hq : ∀ i ∈ q, i ∈ l1Shell)
    (hcov : l1Shell ⊆ ⋃ i ∈ q, ball i (1 / 128))
    (z : ℂ) {r : ℝ} (hr : 0 < r) {u v : ℂ}
    (hu : |‖u - z‖ - r / 2| ≤ r / 256) (hv : r * (1 - 1 / 256) ≤ ‖v - z‖) :
    ∃ i ∈ q, dist u (z + (r : ℂ) * i) < r * l1d / 16 ∧
      3 * (r * l1d) / 4 < dist v (z + (r : ℂ) * i) := by
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  set u' : ℂ := (u - z) / r
  have hnu : ‖u'‖ = ‖u - z‖ / r := by
    simp only [u', norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  have hu' : u' ∈ l1Shell := by
    obtain ⟨h1, h2⟩ := abs_le.1 hu
    refine ⟨?_, ?_⟩
    · rw [hnu, le_div_iff₀ hr]; linarith
    · rw [hnu, div_le_iff₀ hr]; linarith
  obtain ⟨i, hi, hui⟩ := mem_iUnion₂.1 (hcov hu')
  refine ⟨i, hi, ?_, ?_⟩
  · have : dist u (z + (r : ℂ) * i) = r * dist u' i := by
      rw [dist_eq_norm, dist_eq_norm]
      have e : u - (z + (r : ℂ) * i) = (r : ℂ) * (u' - i) := by
        simp only [u']; field_simp; ring
      rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    rw [this, l1d]
    have := mem_ball.1 hui
    nlinarith
  · have hi' := (hq i hi).2
    have hzi : ‖(r : ℂ) * i‖ = r * ‖i‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    have htri : ‖v - z‖ ≤ ‖v - (z + (r : ℂ) * i)‖ + ‖(r : ℂ) * i‖ := by
      calc ‖v - z‖ = ‖(v - (z + (r : ℂ) * i)) + (r : ℂ) * i‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    rw [dist_eq_norm, l1d]
    rw [hzi] at htri
    nlinarith

 
theorem l1_net_ball_subset (q : Finset ℂ) (hq : ∀ i ∈ q, i ∈ l1Shell)
    (z : ℂ) {r : ℝ} (hr : 0 < r) {i : ℂ} (hi : i ∈ q) :
    cthickening (r / 16) (closedBall (z + (r : ℂ) * i) (r * l1d)) ⊆
      {w | r / 4 < ‖w - z‖ ∧ ‖w - z‖ < 3 * r} := by
  intro w hw
  have hw' : dist w (z + (r : ℂ) * i) ≤ r * l1d + r / 16 := by
    rw [cthickening_closedBall (ε := r / 16) (δ := r * l1d) (by positivity)
      (mul_nonneg hr.le (by norm_num [l1d])) (z + (r : ℂ) * i), mem_closedBall] at hw
    linarith
  have hi' := hq i hi
  have hzi : ‖(r : ℂ) * i‖ = r * ‖i‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  rw [dist_eq_norm] at hw'
  have h1 : ‖(r : ℂ) * i‖ ≤ ‖w - z‖ + ‖w - (z + (r : ℂ) * i)‖ := by
    calc ‖(r : ℂ) * i‖ = ‖(w - z) - (w - (z + (r : ℂ) * i))‖ := by ring_nf
      _ ≤ _ := norm_sub_le _ _
  have h2 : ‖w - z‖ ≤ ‖w - (z + (r : ℂ) * i)‖ + ‖(r : ℂ) * i‖ := by
    calc ‖w - z‖ = ‖(w - (z + (r : ℂ) * i)) + (r : ℂ) * i‖ := by ring_nf
      _ ≤ _ := norm_add_le _ _
  rw [hzi] at h1 h2
  obtain ⟨hi1, hi2⟩ := hi'
  unfold l1d at hw'
  constructor <;> nlinarith

end SupercriticalLQGUniqueness.B2.PfeLocal
