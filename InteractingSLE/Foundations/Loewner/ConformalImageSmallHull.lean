import InteractingSLE.Foundations.Loewner.ConformalImageReflect
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# The expansion of the mapping-out function of a small hull

Packet GEO-LOC (`planning/INFRA-GEO.md` §4), third layer: [Law05] Proposition 3.46. If a compact
`ℍ`-hull `L` lies in `B̄(x, r)` with `x ∈ ℝ`, its mapping-out function satisfies

`|g_L(w) − w − hcap(L)/(w − x)| ≤ 12 r hcap(L) / |w − x|²` for `w ∈ ℍ`, `|w − x| ≥ 4r`

(`IsMapOut.norm_sub_sub_hcap_div_le`).

**Proof** (not Lawler's Brownian-motion proof). By Schwarz reflection (`IsMapOut.exists_reflection`)
`g_L − id` extends to a holomorphic function on `{|w − x| > r}`, real on the real axis there; in the
coordinate `ζ = 1/(w − x)` it becomes `k`, holomorphic on `B(0, 1/r)` (removable singularity at
`0`), with `k(0) = 0`, `k'(0) = hcap(L)` and `Im ζ · Im k(ζ) ≥ 0` (`k` is *typically real*, from
`Im g_L(w) ≤ Im w`). Robertson's transform `q(ζ) = (1 − ζ²/R²) k(ζ)/ζ` has `Re q = 2 Im ζ Im k / R²
≥ 0` on `|ζ| = R`, hence `Re q ≥ 0` on `B(0, R)` (maximum modulus for `exp(−q)`), and
`q(0) = hcap(L)`. The Borel–Carathéodory inequality gives
`|q(ζ) − hcap(L)| ≤ 2 hcap(L)|ζ|/(R − |ζ|)`,
and `k(ζ) = ζ q(ζ)/(1 − ζ²/R²)` gives the claim with `R = 1/(2r)`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open scoped ComplexConjugate

open SupercriticalConformalCovariance (IsConformalBijection)
open QuantumZipper (H Hbar)

namespace InteractingSLE

namespace ConformalImage

/-- The mapping-out function reflected across `ℝ`: `g` on `ℍ`, `conj ∘ g ∘ conj` on the lower
half-plane, and the boundary limit from `ℍ` on `ℝ`. -/
def reflectMapOut (g : ℂ → ℂ) (w : ℂ) : ℂ :=
  if 0 < w.im then g w else if w.im < 0 then conj (g (conj w)) else limUnder (𝓝[H] w) g

theorem reflectMapOut_of_pos (g : ℂ → ℂ) {w : ℂ} (hw : 0 < w.im) : reflectMapOut g w = g w := by
  simp [reflectMapOut, hw]

theorem reflectMapOut_of_neg (g : ℂ → ℂ) {w : ℂ} (hw : w.im < 0) :
    reflectMapOut g w = conj (g (conj w)) := by
  simp [reflectMapOut, hw, not_lt.2 hw.le]

theorem reflectMapOut_of_eq (g : ℂ → ℂ) {w : ℂ} (hw : w.im = 0) :
    reflectMapOut g w = limUnder (𝓝[H] w) g := by
  simp [reflectMapOut, hw]

theorem norm_conj_sub_ofReal (w : ℂ) (x : ℝ) : ‖conj w - x‖ = ‖w - x‖ := by
  have : conj w - (x : ℂ) = conj (w - x) := by simp [map_sub]
  rw [this, Complex.norm_conj]

theorem notMem_of_lt_norm_sub {L : Set ℂ} {x r : ℝ} (hLr : L ⊆ closedBall (x : ℂ) r) {w : ℂ}
    (hw : r < ‖w - x‖) : w ∉ L := fun h => by
  have := hLr h
  rw [mem_closedBall, dist_eq_norm] at this
  linarith

variable {L : Set ℂ} {g : ℂ → ℂ} {x r : ℝ}

/-- Near a real point outside `B̄(x, r)`, the reflected function agrees with the Schwarz reflection
of `g`. -/
theorem exists_eventuallyEq_reflectMapOut (hL : IsHPHull L) (hg : IsMapOut L g)
    (hLr : L ⊆ closedBall (x : ℂ) r) {w : ℂ} (hw0 : w.im = 0) (hwx : r < ‖w - x‖) :
    ∃ G : ℂ → ℂ, DifferentiableAt ℂ G w ∧ reflectMapOut g =ᶠ[𝓝 w] G ∧ (G w).im = 0 ∧
      Tendsto g (𝓝[H] w) (𝓝 (G w)) := by
  set ρ := ‖w - x‖ - r with hρ
  have hρpos : 0 < ρ := sub_pos.2 hwx
  have hwy : ((w.re : ℝ) : ℂ) = w := by
    apply Complex.ext <;> simp [hw0]
  have hd : Disjoint (ball ((w.re : ℝ) : ℂ) ρ) L := by
    rw [Set.disjoint_left]
    intro z hz hzL
    rw [hwy, mem_ball, dist_eq_norm] at hz
    have h1 := hLr hzL
    rw [mem_closedBall, dist_eq_norm] at h1
    have : ‖w - x‖ ≤ ‖w - z‖ + ‖z - x‖ := by
      calc ‖w - x‖ = ‖(w - z) + (z - x)‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    rw [← norm_neg, neg_sub] at hz
    linarith
  obtain ⟨G, hGd, hGS, hGsymm, hGreal, -, hGlim⟩ := hg.exists_reflection hL hd
  rw [hwy] at hGd hGS hGsymm hGreal hGlim
  have hball : ball w (ρ / 2) ∈ 𝓝 w := ball_mem_nhds w (by positivity)
  have hwb : w ∈ ball w (ρ / 2) := mem_ball_self (by positivity)
  have hnhds : ∀ z ∈ ball w (ρ / 2), z.im = 0 → 𝓝[ball w (ρ / 2) ∩ H] z = 𝓝[H] z := by
    intro z hz _
    exact nhdsWithin_inter_of_mem (mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds hz))
  have hneBot : ∀ z : ℂ, z.im = 0 → (𝓝[H] z).NeBot := by
    intro z hz
    refine mem_closure_iff_nhdsWithin_neBot.1 ?_
    have := subset_closure_ball_inter_H z 1 ⟨mem_ball_self one_pos, show 0 ≤ z.im from hz.ge⟩
    exact closure_mono inter_subset_right this
  refine ⟨G, hGd.differentiableAt hball, ?_, hGreal w hwb hw0, ?_⟩
  · filter_upwards [hball] with z hz
    rcases lt_trichotomy z.im 0 with hneg | hzero | hpos
    · rw [reflectMapOut_of_neg g hneg]
      have hcz : conj z ∈ ball w (ρ / 2) ∩ H := by
        refine ⟨?_, show 0 < (conj z).im by simp; linarith⟩
        have hcw : conj w = w := conj_eq_iff_im.2 hw0
        rw [mem_ball, ← hcw, dist_conj_conj]
        exact hz
      rw [← hGS hcz, hGsymm z hz, conj_conj]
    · rw [reflectMapOut_of_eq g hzero]
      have h := hGlim z hz hzero
      rw [hnhds z hz hzero] at h
      have := hneBot z hzero
      exact h.limUnder_eq
    · rw [reflectMapOut_of_pos g hpos]
      exact (hGS ⟨hz, hpos⟩).symm
  · have h := hGlim w hwb hw0
    rwa [hnhds w hwb hw0] at h

/-- The reflected mapping-out function is holomorphic outside `B̄(x, r)`. -/
theorem differentiableAt_reflectMapOut (hL : IsHPHull L) (hg : IsMapOut L g)
    (hLr : L ⊆ closedBall (x : ℂ) r) {w : ℂ} (hwx : r < ‖w - x‖) :
    DifferentiableAt ℂ (reflectMapOut g) w := by
  rcases lt_trichotomy w.im 0 with hneg | hzero | hpos
  · have hcw : conj w ∈ H \ L := ⟨show 0 < (conj w).im by simp; linarith,
      notMem_of_lt_norm_sub hLr (by rwa [norm_conj_sub_ofReal])⟩
    have hd : DifferentiableAt ℂ g (conj w) := hg.1.1.differentiableAt (hL.isOpen.mem_nhds hcw)
    have h2 := hd.conj_conj
    rw [conj_conj] at h2
    refine h2.congr_of_eventuallyEq ?_
    filter_upwards [(continuous_im.tendsto w).eventually (gt_mem_nhds hneg)] with z hz
    rw [reflectMapOut_of_neg g hz]
    rfl
  · obtain ⟨G, hGd, hGeq, -, -⟩ := exists_eventuallyEq_reflectMapOut hL hg hLr hzero hwx
    exact hGd.congr_of_eventuallyEq hGeq
  · have hw : w ∈ H \ L := ⟨hpos, notMem_of_lt_norm_sub hLr hwx⟩
    refine (hg.1.1.differentiableAt (hL.isOpen.mem_nhds hw)).congr_of_eventuallyEq ?_
    filter_upwards [(continuous_im.tendsto w).eventually (lt_mem_nhds hpos)] with z hz
    exact reflectMapOut_of_pos g hz

/-- The reflected mapping-out function is real on the real axis outside `B̄(x, r)`. -/
theorem im_reflectMapOut_eq_zero (hL : IsHPHull L) (hg : IsMapOut L g)
    (hLr : L ⊆ closedBall (x : ℂ) r) {w : ℂ} (hw0 : w.im = 0) (hwx : r < ‖w - x‖) :
    (reflectMapOut g w).im = 0 := by
  obtain ⟨G, -, hGeq, hGre, -⟩ := exists_eventuallyEq_reflectMapOut hL hg hLr hw0 hwx
  rw [hGeq.eq_of_nhds]
  exact hGre

/-- `Im (reflectMapOut g w) ≥ Im w` on the lower half-plane. -/
theorem im_le_im_reflectMapOut_of_neg (hL : IsHPHull L) (hg : IsMapOut L g)
    (hLr : L ⊆ closedBall (x : ℂ) r) {w : ℂ} (hw : w.im < 0) (hwx : r < ‖w - x‖) :
    w.im ≤ (reflectMapOut g w).im := by
  have hcw : conj w ∈ H \ L := ⟨show 0 < (conj w).im by simp; linarith,
    notMem_of_lt_norm_sub hLr (by rwa [norm_conj_sub_ofReal])⟩
  rw [reflectMapOut_of_neg g hw, conj_im]
  have := hg.im_le hL hcw
  simp only [conj_im] at this
  linarith

/-- **Decay at `∞`**: `reflectMapOut g w − w → 0` as `|w| → ∞`. -/
theorem exists_norm_reflectMapOut_sub_le (hL : IsHPHull L) (hg : IsMapOut L g)
    (hLr : L ⊆ closedBall (x : ℂ) r) {ε : ℝ} (hε : 0 < ε) :
    ∃ R, ∀ w : ℂ, R ≤ ‖w‖ → ‖reflectMapOut g w - w‖ ≤ ε := by
  have h := hg.2.eventually (closedBall_mem_nhds (0 : ℂ) hε)
  rw [Filter.eventually_inf_principal] at h
  obtain ⟨R₀, hR₀⟩ := isBounded_iff_forall_norm_le.1 (Bornology.isBounded_compl_iff.2 h)
  set R₁ := max R₀ (‖(x : ℂ)‖ + r) + 1 with hR₁def
  set R := R₁ + 1 with hRdef
  have hgood : ∀ z ∈ H, R₁ ≤ ‖z‖ → ‖g z - z‖ ≤ ε := by
    intro z hz hzR
    have hzL : z ∈ H \ L := by
      refine ⟨hz, notMem_of_lt_norm_sub hLr ?_⟩
      have := norm_sub_norm_le z (x : ℂ)
      have := le_max_right R₀ (‖(x : ℂ)‖ + r)
      linarith
    by_contra hcon
    have hz' : z ∈ {z | z ∈ H \ L → g z - z ∈ closedBall (0 : ℂ) ε}ᶜ := by
      intro h'
      have := h' hzL
      rw [mem_closedBall, dist_zero_right] at this
      exact hcon this
    have := hR₀ z hz'
    have := le_max_left R₀ (‖(x : ℂ)‖ + r)
    linarith
  refine ⟨R, fun w hwR => ?_⟩
  have hwx : r < ‖w - x‖ := by
    have := norm_sub_norm_le w (x : ℂ)
    have := le_max_right R₀ (‖(x : ℂ)‖ + r)
    linarith
  rcases lt_trichotomy w.im 0 with hneg | hzero | hpos
  · rw [reflectMapOut_of_neg g hneg]
    have h1 := hgood (conj w) (show 0 < (conj w).im by simp; linarith)
      (by rw [Complex.norm_conj]; linarith)
    rw [← Complex.norm_conj, map_sub, conj_conj]
    exact h1
  · obtain ⟨G, -, hGeq, -, hGlim⟩ := exists_eventuallyEq_reflectMapOut hL hg hLr hzero hwx
    rw [hGeq.eq_of_nhds]
    have hT : Tendsto (fun z => ‖g z - z‖) (𝓝[H] w) (𝓝 ‖G w - w‖) :=
      ((continuous_norm.tendsto _).comp (hGlim.sub (tendsto_nhdsWithin_of_tendsto_nhds
        (continuous_id.tendsto w))))
    have hne : (𝓝[H] w).NeBot := by
      refine mem_closure_iff_nhdsWithin_neBot.1 ?_
      have := subset_closure_ball_inter_H w 1 ⟨mem_ball_self one_pos,
        show 0 ≤ w.im from hzero.ge⟩
      exact closure_mono inter_subset_right this
    refine le_of_tendsto hT ?_
    have hopen : {z : ℂ | R - 1 < ‖z‖} ∈ 𝓝 w :=
      (isOpen_lt continuous_const continuous_norm).mem_nhds (show R - 1 < ‖w‖ by linarith)
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hopen] with z hz hz'
    exact hgood z hz (by
      have : R - 1 < ‖z‖ := hz'
      linarith)
  · rw [reflectMapOut_of_pos g hpos]
    exact hgood w hpos (by linarith)

/-- The mapping-out function in the coordinate `ζ = 1/(w − x)`:
`k(ζ) = g(w) − w` (reflected), `k(0) = 0`. -/
def kfun (g : ℂ → ℂ) (x : ℝ) (ζ : ℂ) : ℂ :=
  if ζ = 0 then 0 else reflectMapOut g (x + ζ⁻¹) - (x + ζ⁻¹)

theorem kfun_zero (g : ℂ → ℂ) (x : ℝ) : kfun g x 0 = 0 := by simp [kfun]

theorem kfun_of_ne (g : ℂ → ℂ) (x : ℝ) {ζ : ℂ} (hζ : ζ ≠ 0) :
    kfun g x ζ = reflectMapOut g (x + ζ⁻¹) - (x + ζ⁻¹) := by simp [kfun, hζ]

theorem lt_norm_add_inv_sub {ζ : ℂ} (hr : 0 < r) (hζ : ζ ∈ ball (0 : ℂ) r⁻¹) (hζ0 : ζ ≠ 0) :
    r < ‖((x : ℂ) + ζ⁻¹) - x‖ := by
  rw [add_sub_cancel_left, norm_inv]
  have := mem_ball_zero_iff.1 hζ
  rwa [lt_inv_comm₀ hr (norm_pos_iff.2 hζ0)]

/-- `k` is holomorphic on `B(0, 1/r)` (removable singularity at `0`). -/
theorem differentiableOn_kfun (hL : IsHPHull L) (hg : IsMapOut L g) (hr : 0 < r)
    (hLr : L ⊆ closedBall (x : ℂ) r) : DifferentiableOn ℂ (kfun g x) (ball 0 r⁻¹) := by
  rw [← differentiableOn_compl_singleton_and_continuousAt_iff
    (ball_mem_nhds 0 (inv_pos.2 hr))]
  constructor
  · intro ζ hζ
    have hζ0 : ζ ≠ 0 := hζ.2
    have h1 : DifferentiableAt ℂ (fun ζ : ℂ => (x : ℂ) + ζ⁻¹) ζ :=
      (differentiableAt_inv hζ0).const_add _
    have h2 : DifferentiableAt ℂ (reflectMapOut g) ((x : ℂ) + ζ⁻¹) :=
      differentiableAt_reflectMapOut hL hg hLr (lt_norm_add_inv_sub hr hζ.1 hζ0)
    have hd := (h2.comp ζ h1).sub h1
    refine (hd.congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [isOpen_ne.mem_nhds hζ0] with z hz
    rw [kfun_of_ne g x hz]
    rfl
  · rw [Metric.continuousAt_iff]
    intro ε hε
    obtain ⟨R, hR⟩ := exists_norm_reflectMapOut_sub_le hL hg hLr (half_pos hε)
    set R' := max R 1 + ‖(x : ℂ)‖ with hR'
    have hR'pos : 0 < R' := by positivity
    refine ⟨R'⁻¹, inv_pos.2 hR'pos, fun ζ hζ => ?_⟩
    rw [kfun_zero, dist_zero_right]
    by_cases hζ0 : ζ = 0
    · rw [hζ0, kfun_zero, norm_zero]; exact hε
    rw [dist_zero_right] at hζ
    rw [kfun_of_ne g x hζ0]
    refine lt_of_le_of_lt (hR _ ?_) (half_lt_self hε)
    have h1 : R' < ‖ζ⁻¹‖ := by
      rw [norm_inv]; exact (lt_inv_comm₀ (norm_pos_iff.2 hζ0) hR'pos).1 hζ
    have h2 := norm_sub_norm_le ζ⁻¹ (-(x : ℂ))
    rw [norm_neg, sub_neg_eq_add, add_comm] at h2
    have h3 := le_max_left R 1
    linarith

/-- `k'(0) = hcap(L)`. -/
theorem hasDerivAt_kfun_zero (hL : IsHPHull L) (hg : IsMapOut L g) (hr : 0 < r)
    (hLr : L ⊆ closedBall (x : ℂ) r) :
    HasDerivAt (kfun g x) (HPHull.hcap ⟨L, hL⟩ : ℂ) 0 := by
  have hd : HasDerivAt (kfun g x) (deriv (kfun g x) 0) 0 :=
    ((differentiableOn_kfun hL hg hr hLr).differentiableAt
      (ball_mem_nhds 0 (inv_pos.2 hr))).hasDerivAt
  suffices h : deriv (kfun g x) 0 = (HPHull.hcap ⟨L, hL⟩ : ℂ) by rwa [h] at hd
  have hslope := hasDerivAt_iff_tendsto_slope_zero.1 hd
  simp only [zero_add, kfun_zero, sub_zero, smul_eq_mul] at hslope
  -- along `t(y) = 1/(iy − x)`, `y → ∞`
  have hT := hL.tendsto_ofReal_mul_I
  have hcap := (HPHull.tendsto_hcap ⟨L, hL⟩ hg).comp hT
  have hsub := hg.2.comp hT
  have hlim : Tendsto (fun y : ℝ => ((y : ℂ) * I - x) * (g ((y : ℂ) * I) - (y : ℂ) * I)) atTop
      (𝓝 (HPHull.hcap ⟨L, hL⟩ : ℂ)) := by
    have := hcap.sub (hsub.const_mul (x : ℂ))
    rw [mul_zero, sub_zero] at this
    refine this.congr fun y => ?_
    simp only [Function.comp_apply]
    ring
  have hnorm : Tendsto (fun y : ℝ => ‖(y : ℂ) * I - x‖) atTop atTop := by
    refine tendsto_atTop_mono (fun y => ?_) (tendsto_abs_atTop_atTop.atTop_add
      (tendsto_const_nhds (x := -‖(x : ℂ)‖)))
    have h1 : ‖(y : ℂ) * I‖ = |y| := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have := norm_sub_norm_le ((y : ℂ) * I) (x : ℂ)
    linarith
  have ht0 : Tendsto (fun y : ℝ => ((y : ℂ) * I - x)⁻¹) atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨tendsto_inv₀_cobounded.comp
      (tendsto_norm_atTop_iff_cobounded.1 hnorm), ?_⟩
    filter_upwards [hnorm.eventually_gt_atTop 0] with y hy
    exact inv_ne_zero (norm_pos_iff.1 hy)
  have h1 := hslope.comp ht0
  refine tendsto_nhds_unique h1 (hlim.congr' ?_)
  filter_upwards [hnorm.eventually_gt_atTop 0, eventually_gt_atTop 0] with y hy hy0
  have hne : (y : ℂ) * I - x ≠ 0 := norm_pos_iff.1 hy
  simp only [Function.comp_apply, inv_inv]
  rw [kfun_of_ne g x (inv_ne_zero hne), inv_inv, add_sub_cancel,
    reflectMapOut_of_pos g (by simpa using hy0)]

/-- `k` is **typically real**: `Im ζ · Im k(ζ) ≥ 0` on `B(0, 1/r)`. -/
theorem im_mul_im_kfun_nonneg (hL : IsHPHull L) (hg : IsMapOut L g) (hr : 0 < r)
    (hLr : L ⊆ closedBall (x : ℂ) r) {ζ : ℂ} (hζ : ζ ∈ ball (0 : ℂ) r⁻¹) :
    0 ≤ ζ.im * (kfun g x ζ).im := by
  by_cases hζ0 : ζ = 0
  · simp [hζ0]
  rw [kfun_of_ne g x hζ0]
  have hwx := lt_norm_add_inv_sub (x := x) hr hζ hζ0
  set w := (x : ℂ) + ζ⁻¹ with hw
  have hwim : w.im = -ζ.im / normSq ζ := by simp [hw, inv_im]
  have hns : 0 < normSq ζ := normSq_pos.2 hζ0
  rcases lt_trichotomy ζ.im 0 with hneg | hzero | hpos
  · have hwpos : 0 < w.im := by rw [hwim]; exact div_pos (by linarith) hns
    have hwL : w ∈ H \ L := ⟨hwpos, notMem_of_lt_norm_sub hLr hwx⟩
    rw [reflectMapOut_of_pos g hwpos, sub_im]
    have := hg.im_le hL hwL
    nlinarith
  · rw [hzero, zero_mul]
  · have hwneg : w.im < 0 := by rw [hwim]; exact div_neg_of_neg_of_pos (by linarith) hns
    have := im_le_im_reflectMapOut_of_neg hL hg hLr hwneg hwx
    rw [sub_im]
    nlinarith

/-- Robertson's transform on the circle `|ζ| = R`. -/
theorem re_robertson_of_norm_eq (k : ℂ → ℂ) {R : ℝ} (hR : 0 < R) {ζ : ℂ} (hζ : ‖ζ‖ = R) :
    ((1 - ζ ^ 2 / (R : ℂ) ^ 2) * (ζ⁻¹ * k ζ)).re = 2 * ζ.im * (k ζ).im / R ^ 2 := by
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [norm_zero] at hζ
    linarith
  have hR0 : (R : ℂ) ≠ 0 := ofReal_ne_zero.2 hR.ne'
  have hmul : ζ * conj ζ = (R : ℂ) ^ 2 := by
    rw [mul_conj, normSq_eq_norm_sq, hζ]; push_cast; ring
  have hinv : ζ⁻¹ = conj ζ / (R : ℂ) ^ 2 := by
    rw [eq_div_iff (pow_ne_zero 2 hR0), ← hmul, ← mul_assoc, inv_mul_cancel₀ hζ0, one_mul]
  have hcz : conj ζ - ζ = ((-2 * ζ.im : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp; ring
  have key : (1 - ζ ^ 2 / (R : ℂ) ^ 2) * (ζ⁻¹ * k ζ) =
      ((-2 * ζ.im / R ^ 2 : ℝ) : ℂ) * (I * k ζ) := by
    rw [hinv]
    have : (1 - ζ ^ 2 / (R : ℂ) ^ 2) * (conj ζ / (R : ℂ) ^ 2 * k ζ) =
        (conj ζ - ζ) / (R : ℂ) ^ 2 * k ζ := by
      field_simp
      linear_combination (-(ζ * k ζ)) * hmul
    rw [this, hcz]
    push_cast
    field_simp
  rw [key, re_ofReal_mul, I_mul_re]
  ring

/-- Robertson's transform `q(ζ) = (1 − ζ²/R²) k(ζ)/ζ` (with `q(0) = k'(0)`). -/
def robertson (k : ℂ → ℂ) (R : ℝ) (ζ : ℂ) : ℂ := (1 - ζ ^ 2 / (R : ℂ) ^ 2) * dslope k 0 ζ

theorem differentiableOn_robertson (hL : IsHPHull L) (hg : IsMapOut L g) (hr : 0 < r)
    (hLr : L ⊆ closedBall (x : ℂ) r) (R : ℝ) :
    DifferentiableOn ℂ (robertson (kfun g x) R) (ball 0 r⁻¹) :=
  (differentiableOn_const _ |>.sub ((differentiableOn_id.pow 2).div_const _)).mul
    ((differentiableOn_dslope (ball_mem_nhds 0 (inv_pos.2 hr))).2
      (differentiableOn_kfun hL hg hr hLr))

theorem robertson_zero (hL : IsHPHull L) (hg : IsMapOut L g) (hr : 0 < r)
    (hLr : L ⊆ closedBall (x : ℂ) r) (R : ℝ) :
    robertson (kfun g x) R 0 = (HPHull.hcap ⟨L, hL⟩ : ℂ) := by
  rw [robertson, dslope_same, (hasDerivAt_kfun_zero hL hg hr hLr).deriv]
  simp

theorem robertson_of_ne (g : ℂ → ℂ) (x : ℝ) (R : ℝ) {ζ : ℂ} (hζ : ζ ≠ 0) :
    robertson (kfun g x) R ζ = (1 - ζ ^ 2 / (R : ℂ) ^ 2) * (ζ⁻¹ * kfun g x ζ) := by
  rw [robertson, dslope_of_ne _ hζ, slope_def_module, sub_zero, kfun_zero, sub_zero,
    smul_eq_mul]

/-- **`Re q ≥ 0`** on `B̄(0, R)` for `0 < R < 1/r` (maximum modulus for `exp(−q)`). -/
theorem re_robertson_nonneg (hL : IsHPHull L) (hg : IsMapOut L g) (hr : 0 < r)
    (hLr : L ⊆ closedBall (x : ℂ) r) {R : ℝ} (hR : 0 < R) (hRr : R < r⁻¹) {ζ : ℂ}
    (hζ : ζ ∈ closedBall (0 : ℂ) R) : 0 ≤ (robertson (kfun g x) R ζ).re := by
  have hqd := differentiableOn_robertson hL hg hr hLr R
  have hsub : closedBall (0 : ℂ) R ⊆ ball 0 r⁻¹ := closedBall_subset_ball hRr
  have hexp : DiffContOnCl ℂ (fun z => exp (-robertson (kfun g x) R z)) (ball 0 R) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball _ hR.ne']
    exact ((hqd.mono hsub).neg).cexp
  have hfront : ∀ z ∈ frontier (ball (0 : ℂ) R), ‖exp (-robertson (kfun g x) R z)‖ ≤ 1 := by
    intro z hz
    rw [frontier_ball _ hR.ne', mem_sphere, dist_zero_right] at hz
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [norm_zero] at hz
      linarith
    rw [Complex.norm_exp, neg_re, Real.exp_le_one_iff, neg_nonpos, robertson_of_ne g x R hz0,
      re_robertson_of_norm_eq _ hR hz]
    have := im_mul_im_kfun_nonneg hL hg hr hLr (hsub (mem_closedBall.2 (by
      rw [dist_zero_right, hz])))
    have h2 : 0 ≤ 2 * z.im * (kfun g x z).im := by nlinarith
    exact div_nonneg h2 (sq_nonneg R)
  have h := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hexp hfront
    (by rwa [closure_ball _ hR.ne'])
  rw [Complex.norm_exp, neg_re, Real.exp_le_one_iff, neg_nonpos] at h
  exact h

/-- **Borel–Carathéodory for `q`**: `|q(ζ) − hcap(L)| ≤ 2 hcap(L) |ζ| / (R − |ζ|)` on `B(0, R)`. -/
theorem norm_robertson_sub_le (hL : IsHPHull L) (hg : IsMapOut L g) (hr : 0 < r)
    (hLr : L ⊆ closedBall (x : ℂ) r) {R : ℝ} (hR : 0 < R) (hRr : R < r⁻¹) {ζ : ℂ}
    (hζ : ζ ∈ ball (0 : ℂ) R) :
    ‖(HPHull.hcap ⟨L, hL⟩ : ℂ) - robertson (kfun g x) R ζ‖ ≤
      2 * HPHull.hcap ⟨L, hL⟩ * ‖ζ‖ / (R - ‖ζ‖) := by
  set c := HPHull.hcap ⟨L, hL⟩ with hc
  have hc0 : 0 ≤ c := HPHull.hcap_nonneg _
  have hζR : ‖ζ‖ < R := mem_ball_zero_iff.1 hζ
  have hbound : ∀ ε : ℝ, 0 < ε →
      ‖(c : ℂ) - robertson (kfun g x) R ζ‖ ≤ 2 * (c + ε) * ‖ζ‖ / (R - ‖ζ‖) := by
    intro ε hε
    refine Complex.borelCaratheodory_zero (f := fun z => (c : ℂ) - robertson (kfun g x) R z)
      (by positivity) ?_ ?_ hR hζ ?_
    · exact (differentiableOn_const _).sub
        ((differentiableOn_robertson hL hg hr hLr R).mono (ball_subset_ball hRr.le))
    · intro z hz
      have := re_robertson_nonneg hL hg hr hLr hR hRr (ball_subset_closedBall hz)
      simp only [Set.mem_ofPred_eq, sub_re, ofReal_re]
      linarith
    · simp only [robertson_zero hL hg hr hLr R, hc, sub_self]
  have hT : Tendsto (fun ε : ℝ => 2 * (c + ε) * ‖ζ‖ / (R - ‖ζ‖)) (𝓝[>] 0)
      (𝓝 (2 * c * ‖ζ‖ / (R - ‖ζ‖))) := by
    have : Continuous fun ε : ℝ => 2 * (c + ε) * ‖ζ‖ / (R - ‖ζ‖) := by fun_prop
    have h := this.tendsto 0
    simp only [add_zero] at h
    exact h.mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hT (eventually_nhdsWithin_of_forall fun ε hε => hbound ε hε)

/-- The bound on `k`: `|k(ζ) − hcap(L) ζ| ≤ 6 hcap(L) |ζ|² / R` for `|ζ| ≤ R/2`. -/
theorem norm_kfun_sub_le (hL : IsHPHull L) (hg : IsMapOut L g) (hr : 0 < r)
    (hLr : L ⊆ closedBall (x : ℂ) r) {R : ℝ} (hR : 0 < R) (hRr : R < r⁻¹) {ζ : ℂ}
    (hζ : ‖ζ‖ ≤ R / 2) :
    ‖kfun g x ζ - (HPHull.hcap ⟨L, hL⟩ : ℂ) * ζ‖ ≤ 6 * HPHull.hcap ⟨L, hL⟩ * ‖ζ‖ ^ 2 / R := by
  set c := HPHull.hcap ⟨L, hL⟩ with hc
  have hc0 : 0 ≤ c := HPHull.hcap_nonneg _
  by_cases hζ0 : ζ = 0
  · simp [hζ0, kfun_zero]
  have hζpos : 0 < ‖ζ‖ := norm_pos_iff.2 hζ0
  have hζb : ζ ∈ ball (0 : ℂ) R := mem_ball_zero_iff.2 (by linarith)
  have hBC := norm_robertson_sub_le hL hg hr hLr hR hRr hζb
  rw [← hc] at hBC
  set q := robertson (kfun g x) R ζ with hq
  set D : ℂ := 1 - ζ ^ 2 / (R : ℂ) ^ 2 with hD
  have hR0 : (R : ℂ) ≠ 0 := ofReal_ne_zero.2 hR.ne'
  have hsmall : ‖ζ ^ 2 / (R : ℂ) ^ 2‖ ≤ 1 / 4 := by
    rw [norm_div, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR,
      div_le_iff₀ (by positivity)]
    nlinarith
  have hDnorm : 3 / 4 ≤ ‖D‖ := by
    have := norm_sub_norm_le (1 : ℂ) (ζ ^ 2 / (R : ℂ) ^ 2)
    rw [norm_one] at this
    rw [hD]
    linarith
  have hD0 : D ≠ 0 := by
    intro h
    rw [h, norm_zero] at hDnorm
    linarith
  have hqk : q = D * (ζ⁻¹ * kfun g x ζ) := robertson_of_ne g x R hζ0
  have hk : kfun g x ζ = ζ * q / D := by
    rw [hqk]; field_simp
  have hdiff : kfun g x ζ - (c : ℂ) * ζ = ζ * ((q - c) + c * (ζ ^ 2 / (R : ℂ) ^ 2)) / D := by
    rw [hk, eq_div_iff hD0, sub_mul, div_mul_cancel₀ _ hD0, hD]
    ring
  rw [hdiff, norm_div, norm_mul]
  have h1 : ‖q - c‖ ≤ 4 * c * ‖ζ‖ / R := by
    rw [← norm_neg, neg_sub]
    calc ‖(c : ℂ) - q‖ ≤ 2 * c * ‖ζ‖ / (R - ‖ζ‖) := hBC
      _ ≤ 4 * c * ‖ζ‖ / R := by
        rw [div_le_div_iff₀ (by linarith) hR]
        nlinarith [mul_nonneg hc0 hζpos.le]
  have h2 : ‖(c : ℂ) * (ζ ^ 2 / (R : ℂ) ^ 2)‖ ≤ c * ‖ζ‖ / (2 * R) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc0, norm_div, norm_pow,
      norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
    rw [show c * (‖ζ‖ ^ 2 / R ^ 2) = c * ‖ζ‖ * (‖ζ‖ / R ^ 2) by ring,
      show c * ‖ζ‖ / (2 * R) = c * ‖ζ‖ * (1 / (2 * R)) by ring]
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hc0 hζpos.le)
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have h3 : ‖(q - c) + c * (ζ ^ 2 / (R : ℂ) ^ 2)‖ ≤ 9 * c * ‖ζ‖ / (2 * R) := by
    calc _ ≤ ‖q - c‖ + ‖(c : ℂ) * (ζ ^ 2 / (R : ℂ) ^ 2)‖ := norm_add_le _ _
      _ ≤ 4 * c * ‖ζ‖ / R + c * ‖ζ‖ / (2 * R) := add_le_add h1 h2
      _ = 9 * c * ‖ζ‖ / (2 * R) := by field_simp; ring
  rw [div_le_div_iff₀ (by linarith) hR]
  calc ‖ζ‖ * ‖(q - c) + c * (ζ ^ 2 / (R : ℂ) ^ 2)‖ * R
      ≤ ‖ζ‖ * (9 * c * ‖ζ‖ / (2 * R)) * R := by gcongr
    _ = 9 / 2 * c * ‖ζ‖ ^ 2 := by field_simp
    _ ≤ 6 * c * ‖ζ‖ ^ 2 * ‖D‖ := by nlinarith [mul_nonneg hc0 (sq_nonneg ‖ζ‖)]

end ConformalImage

open ConformalImage in
/-- **[Law05] Proposition 3.46** (expansion of the mapping-out function of a small hull): if the
compact `ℍ`-hull `L` lies in `B̄(x, r)` (`x ∈ ℝ`, `r > 0`), then for `w ∈ ℍ` with `|w − x| ≥ 4r`,
`|g_L(w) − w − hcap(L)/(w − x)| ≤ 12 r hcap(L) / |w − x|²`. -/
theorem IsMapOut.norm_sub_sub_hcap_div_le {L : Set ℂ} {g : ℂ → ℂ} (hL : IsHPHull L)
    (hg : IsMapOut L g) {x r : ℝ} (hr : 0 < r) (hLr : L ⊆ closedBall (x : ℂ) r) {w : ℂ}
    (hw : w ∈ H) (hwx : 4 * r ≤ ‖w - x‖) :
    ‖g w - w - (HPHull.hcap ⟨L, hL⟩ : ℂ) / (w - x)‖ ≤
      12 * r * HPHull.hcap ⟨L, hL⟩ / ‖w - x‖ ^ 2 := by
  have hwx0 : 0 < ‖w - x‖ := by linarith
  have hne : w - x ≠ 0 := norm_pos_iff.1 hwx0
  set ζ := (w - x)⁻¹ with hζ
  have hζ0 : ζ ≠ 0 := inv_ne_zero hne
  have hR : 0 < (2 * r)⁻¹ := by positivity
  have hRr : (2 * r)⁻¹ < r⁻¹ := inv_strictAnti₀ hr (by linarith)
  have hζR : ‖ζ‖ ≤ (2 * r)⁻¹ / 2 := by
    rw [hζ, norm_inv, show (2 * r)⁻¹ / 2 = (4 * r)⁻¹ by ring]
    exact inv_anti₀ (by positivity) hwx
  have h := norm_kfun_sub_le hL hg hr hLr hR hRr hζR
  rw [kfun_of_ne g x hζ0, hζ, inv_inv, add_sub_cancel, reflectMapOut_of_pos g hw] at h
  rw [div_eq_mul_inv]
  calc _ ≤ _ := h
    _ = 12 * r * HPHull.hcap ⟨L, hL⟩ / ‖w - ↑x‖ ^ 2 := by
      rw [norm_inv]; field_simp; ring

end InteractingSLE
