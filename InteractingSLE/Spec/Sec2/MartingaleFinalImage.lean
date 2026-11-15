import InteractingSLE.Spec.Sec2.MartingaleFinalFlow

/-!
# Geometric force-point images: definition, monotonicity, continuity

Packet PROVE-SEC2-MART2 (step R3). Specification §2.3 (`source/spec/p001-048.md`, L815: "if `x^{i,q}` has
not yet been absorbed by the Loewner hull `K_t` then `V_t^{i,q} = g_t(x^{i,q})`, and otherwise `V_t^{i,R}`
is the `g_t` image of the right endpoint of `ℝ ∩ K_t`"; L940–L951, "Geometric force endpoints": "These
facts also follow by approaching an extreme prime end through unswallowed real points").

`rightImg w x t = inf {g_t(y) : y > x, y alive at t}` for a right force point `x ≥ 0` (`x = 0` is `0⁺`):
it is `g_t(x)` while `x` is alive (`rightImg_eq_gImg`) and the image of the right extreme point of the
swallowed real set otherwise, approached through unswallowed real points.

## Main results

* `rightImg_zero`, `le_rightImg`, `rightImg_mono_time`, `rightImg_mono_index`, `rightImg_eq_gImg`;
* `rightImg_le_add`: `V_t ≤ max(V_s, sup_{[s,t]} w) + ε + 2√(t − s)` (the source's deterministic bound);
* `continuousOn_rightImg`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE

namespace MartChar

namespace RealFlow

variable {w : ℝ → ℝ}

/-- The images `g_t(y)` of the alive points `y > x`. -/
def imgSet (w : ℝ → ℝ) (x t : ℝ) : Set ℝ := {g | ∃ y, x < y ∧ Alive w y t ∧ gImg w y t = g}

/-- **The geometric image of a right force point `x ≥ 0`** (`x = 0` stands for `0⁺`):
`inf {g_t(y) : y > x alive at t}`. -/
def rightImg (w : ℝ → ℝ) (x t : ℝ) : ℝ := sInf (imgSet w x t)

lemma imgSet_nonempty (hw : Continuous w) (x : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    (imgSet w x t).Nonempty := by
  obtain ⟨s₀, hs₀, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 ht) hw.continuousOn
  refine ⟨_, max x (w s₀) + 1, by linarith [le_max_left x (w s₀)],
    alive_of_forall_lt hw ht fun s hs => ?_, rfl⟩
  have := hmax hs
  simp only [mem_ofPred_eq] at this
  linarith [le_max_right x (w s₀)]

lemma imgSet_bddBelow (hw : Continuous w) (x : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    BddBelow (imgSet w x t) :=
  ⟨w t, fun _ ⟨_, _, hy, hg⟩ => hg ▸ (hy.lt_gImg hw ⟨ht, le_rfl⟩).le⟩

lemma rightImg_le_gImg (hw : Continuous w) {x y t : ℝ} (ht : 0 ≤ t) (hxy : x < y)
    (hy : Alive w y t) : rightImg w x t ≤ gImg w y t :=
  csInf_le (imgSet_bddBelow hw x ht) ⟨y, hxy, hy, rfl⟩

lemma le_rightImg (hw : Continuous w) (x : ℝ) {t : ℝ} (ht : 0 ≤ t) : w t ≤ rightImg w x t :=
  le_csInf (imgSet_nonempty hw x ht) fun _ ⟨_, _, hy, hg⟩ => hg ▸ (hy.lt_gImg hw ⟨ht, le_rfl⟩).le

lemma exists_lt_of_rightImg_lt (hw : Continuous w) {x t c : ℝ} (ht : 0 ≤ t)
    (hc : rightImg w x t < c) : ∃ y, x < y ∧ Alive w y t ∧ gImg w y t < c := by
  obtain ⟨_, ⟨y, hxy, hy, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt (imgSet_nonempty hw x ht) hc
  exact ⟨y, hxy, hy, hlt⟩

lemma rightImg_mono_index (hw : Continuous w) {x x' t : ℝ} (ht : 0 ≤ t) (hxx : x ≤ x') :
    rightImg w x t ≤ rightImg w x' t :=
  csInf_le_csInf (imgSet_bddBelow hw x ht) (imgSet_nonempty hw x' ht)
    fun _ ⟨y, hxy, hy, hg⟩ => ⟨y, hxx.trans_lt hxy, hy, hg⟩

lemma rightImg_mono_time (hw : Continuous w) (x : ℝ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    rightImg w x s ≤ rightImg w x t :=
  le_csInf (imgSet_nonempty hw x (hs.trans hst)) fun _ ⟨_y, hxy, hy, hg⟩ =>
    hg ▸ (rightImg_le_gImg hw hs hxy (hy.mono hst)).trans (hy.gImg_mono hw hs hst le_rfl)

lemma alive_zero_iff {y : ℝ} : Alive w y 0 ↔ 0 < y - w 0 := by
  constructor
  · rintro ⟨X, hX⟩
    have h := hX.2 0 ⟨le_rfl, le_rfl⟩
    rw [intervalIntegral.integral_same, add_zero] at h
    exact h.2 ▸ h.1
  · intro h
    refine ⟨fun _ => y - w 0, continuousOn_const, fun s hs => ?_⟩
    have hs0 : s = 0 := le_antisymm hs.2 hs.1
    subst hs0
    simp [h]

lemma gImg_zero (hw : Continuous w) {y : ℝ} (hy : Alive w y 0) : gImg w y 0 = y := by
  rw [hy.gImg_eq hw ⟨le_rfl, le_rfl⟩, intervalIntegral.integral_same, add_zero]

/-- The geometric image starts at the force point. -/
lemma rightImg_zero (hw : Continuous w) (hw0 : w 0 = 0) {x : ℝ} (hx : 0 ≤ x) :
    rightImg w x 0 = x := by
  have hset : imgSet w x 0 = Ioi x := by
    ext g
    simp only [imgSet, mem_ofPred_eq, mem_Ioi]
    constructor
    · rintro ⟨y, hxy, hy, rfl⟩
      rw [gImg_zero hw hy]
      exact hxy
    · intro hg
      have hA : Alive w g 0 := alive_zero_iff.2 (by rw [hw0, sub_zero]; linarith)
      exact ⟨g, hg, hA, gImg_zero hw hA⟩
  rw [rightImg, hset, csInf_Ioi]

/-- While `x` is alive, its geometric image is `g_t(x)`. -/
lemma rightImg_eq_gImg (hw : Continuous w) {x t : ℝ} (ht : 0 ≤ t) (hx : Alive w x t) :
    rightImg w x t = gImg w x t := by
  refine le_antisymm (le_of_forall_pos_le_add fun δ hδ => ?_) (le_csInf
    (imgSet_nonempty hw x ht) fun _ ⟨y, hxy, _, hg⟩ => hg ▸ ?_)
  · have hy : Alive w (x + δ) t := hx.of_le hw (by linarith) ht
    have h := (cflow_lt_and_sub_le hw hx (show x < x + δ by linarith) ht ⟨ht, le_rfl⟩).2
    refine (rightImg_le_gImg hw ht (by linarith) hy).trans ?_
    simp only [gImg]
    linarith
  · have h := (cflow_lt_and_sub_le hw hx hxy ht ⟨ht, le_rfl⟩).1
    simp only [gImg]
    linarith

/-- `y ↦ g_t(y)` is `1`-Lipschitz on the alive points. -/
lemma abs_gImg_sub_le (hw : Continuous w) {y y' t : ℝ} (ht : 0 ≤ t) (hy : Alive w y t)
    (hy' : Alive w y' t) : |gImg w y' t - gImg w y t| ≤ |y' - y| := by
  rcases lt_trichotomy y y' with hlt | rfl | hgt
  · have h := cflow_lt_and_sub_le hw hy hlt ht ⟨ht, le_rfl⟩
    simp only [gImg]
    rw [abs_of_pos (by linarith [h.1]), abs_of_pos (by linarith)]
    linarith [h.2]
  · simp
  · have h := cflow_lt_and_sub_le hw hy' hgt ht ⟨ht, le_rfl⟩
    simp only [gImg]
    rw [abs_of_neg (by linarith [h.1]), abs_of_neg (by linarith)]
    linarith [h.2]

lemma Alive.le_gImg (hw : Continuous w) {y t : ℝ} (ht : 0 ≤ t) (hy : Alive w y t) :
    y ≤ gImg w y t := by
  have h := hy.gImg_mono hw le_rfl ht le_rfl
  rwa [gImg_zero hw (hy.mono ht)] at h

/-! ### The deterministic bound and continuity -/

/-- An alive point `y > x` with `g_s(y)` in a prescribed window above `M ≥ V_s` (intermediate values
of the `1`-Lipschitz map `y ↦ g_s(y)`). -/
lemma exists_alive_gImg_mem (hw : Continuous w) {x s M ε : ℝ} (hs : 0 ≤ s) (hε : 0 < ε)
    (hM : rightImg w x s ≤ M) :
    ∃ y, x < y ∧ Alive w y s ∧ M < gImg w y s ∧ gImg w y s < M + ε := by
  obtain ⟨y₀, hxy₀, hy₀, hg₀⟩ := exists_lt_of_rightImg_lt hw hs (hM.trans_lt (by linarith : M < M + ε))
  by_cases hlt : M < gImg w y₀ s
  · exact ⟨y₀, hxy₀, hy₀, hlt, hg₀⟩
  push Not at hlt
  have hy₀M : y₀ ≤ M := (hy₀.le_gImg hw hs).trans hlt
  have hY : y₀ ≤ M + ε := by linarith
  have hcont : ContinuousOn (fun y => gImg w y s) (Icc y₀ (M + ε)) := by
    refine (LipschitzOnWith.of_dist_le_mul (K := 1) fun a ha b hb => ?_).continuousOn
    rw [Real.dist_eq, Real.dist_eq, NNReal.coe_one, one_mul]
    exact abs_gImg_sub_le hw hs (hy₀.of_le hw hb.1 hs) (hy₀.of_le hw ha.1 hs)
  have hYg : M + ε ≤ gImg w (M + ε) s := (hy₀.of_le hw hY hs).le_gImg hw hs
  obtain ⟨y, hy, hyg⟩ := intermediate_value_Icc hY hcont
    (show M + ε / 2 ∈ Icc (gImg w y₀ s) (gImg w (M + ε) s) from ⟨by linarith, by linarith⟩)
  exact ⟨y, hxy₀.trans_le hy.1, hy₀.of_le hw hy.1 hs, by simp only at hyg; linarith,
    by simp only at hyg; linarith⟩

/-- **The deterministic upper bound** (Specification p. 39):
`V_t ≤ M + ε + 2√(t − s)` whenever `M ≥ V_s` and `M ≥ w` on `[s, t]`. -/
lemma rightImg_le_add (hw : Continuous w) {x s t M ε : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (hε : 0 < ε) (hM1 : rightImg w x s ≤ M) (hM2 : ∀ u ∈ Icc s t, w u ≤ M) :
    rightImg w x t ≤ M + ε + 2 * Real.sqrt (t - s) := by
  obtain ⟨y, hxy, hy, hMy, hyM⟩ := exists_alive_gImg_mem hw hs hε hM1
  have hc : 0 < gImg w y s - M := by linarith
  -- `y` stays alive up to `t`
  have hyt : Alive w y t := hy.of_forall_le_cflow hw hs hc fun u hu hyu => by
    have h1 := hyu.gImg_mono hw hs hu.1 le_rfl
    have h2 := hM2 u hu
    simp only [gImg] at h1 ⊢
    linarith
  -- `(g − M)² − 4u` is non-increasing on `[s, t]`
  have hgc : ContinuousOn (fun u => gImg w y u) (Icc 0 t) :=
    hw.continuousOn.add (hyt.isPosSol hw).1
  have hanti : AntitoneOn (fun u => (gImg w y u - M) ^ 2 - 4 * u) (Icc s t) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc s t)
      (((hgc.mono (Icc_subset_Icc_left hs)).sub continuousOn_const).pow 2 |>.sub
        (continuousOn_const.mul continuousOn_id))
      (f' := fun u => 2 * (gImg w y u - M) * (2 / cflow w y u) - 4) (fun u hu => ?_)
      (fun u hu => ?_)
    · rw [interior_Icc] at hu
      have hd := hyt.hasDerivAt_gImg hw ⟨hs.trans_lt hu.1, hu.2⟩
      have := ((hd.sub_const M).pow 2).fun_sub ((hasDerivAt_id' u).const_mul 4)
      exact (this.congr_deriv (by ring)).hasDerivWithinAt
    · rw [interior_Icc] at hu
      have hu' : u ∈ Icc 0 t := ⟨hs.trans hu.1.le, hu.2.le⟩
      have hpos := hyt.cflow_pos hw hu'
      have hgm : gImg w y s ≤ gImg w y u := hyt.gImg_mono hw hs hu.1.le hu.2.le
      have hwu := hM2 u ⟨hu.1.le, hu.2.le⟩
      have hle : gImg w y u - M ≤ cflow w y u := by simp only [gImg] at hgm ⊢; linarith
      have h0 : 0 ≤ gImg w y u - M := by linarith
      have : 2 * (gImg w y u - M) * (2 / cflow w y u) ≤ 4 := by
        have he : 2 * (gImg w y u - M) * (2 / cflow w y u) = 4 * ((gImg w y u - M) / cflow w y u) :=
          by ring
        have : (gImg w y u - M) / cflow w y u ≤ 1 := (div_le_one hpos).2 hle
        rw [he]
        linarith
      linarith
  have hst' := hanti ⟨le_rfl, hst⟩ ⟨hst, le_rfl⟩ hst
  simp only at hst'
  have hsq : (gImg w y t - M) ^ 2 ≤ (ε + 2 * Real.sqrt (t - s)) ^ 2 := by
    have hd : 0 ≤ t - s := by linarith
    have h1 : (gImg w y s - M) ^ 2 ≤ ε ^ 2 := by nlinarith
    have h2 := Real.sq_sqrt hd
    have h3 := Real.sqrt_nonneg (t - s)
    nlinarith
  have hgt : M ≤ gImg w y t := by
    linarith [hyt.gImg_mono hw hs hst le_rfl]
  have := (pow_le_pow_iff_left₀ (by linarith) (by positivity) two_ne_zero).1 hsq
  linarith [rightImg_le_gImg hw (hs.trans hst) hxy hyt]

/-- **Continuity of the geometric image.** -/
lemma continuousOn_rightImg (hw : Continuous w) (x : ℝ) :
    ContinuousOn (rightImg w x) (Ici 0) := by
  -- one-sided estimate on a compact time window
  have key : ∀ T η : ℝ, 0 < η → ∃ δ > 0, ∀ s t, 0 ≤ s → s ≤ t → t ≤ T → t - s < δ →
      rightImg w x t - rightImg w x s < η := by
    intro T η hη
    obtain ⟨δ₁, hδ₁, hδw⟩ := Metric.uniformContinuousOn_iff.1
      ((isCompact_Icc (a := (0 : ℝ)) (b := T)).uniformContinuousOn_of_continuous hw.continuousOn)
      (η / 3) (by linarith)
    refine ⟨min δ₁ ((η / 6) ^ 2), lt_min hδ₁ (by positivity), fun s t hs hst htT hts => ?_⟩
    have hM2 : ∀ u ∈ Icc s t, w u ≤ rightImg w x s + η / 3 := fun u hu => by
      have h1 := hδw s ⟨hs, hst.trans htT⟩ u ⟨hs.trans hu.1, hu.2.trans htT⟩
        (by rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith [hu.1])]
            linarith [hu.2, min_le_left δ₁ ((η / 6) ^ 2)])
      rw [Real.dist_eq] at h1
      have h2 := le_rightImg hw x hs
      linarith [(abs_lt.1 h1).1]
    have hb := rightImg_le_add hw hs hst (ε := η / 3) (by linarith)
      (show rightImg w x s ≤ rightImg w x s + η / 3 by linarith) hM2
    have hsq : Real.sqrt (t - s) < η / 6 := by
      rw [Real.sqrt_lt' (by linarith)]
      linarith [min_le_right δ₁ ((η / 6) ^ 2)]
    linarith
  intro t₀ ht₀
  rw [Metric.continuousWithinAt_iff]
  intro η hη
  obtain ⟨δ, hδ, hk⟩ := key (t₀ + 1) η hη
  refine ⟨min δ 1, lt_min hδ one_pos, fun t ht htd => ?_⟩
  rw [Real.dist_eq] at htd ⊢
  have ht0 : (0 : ℝ) ≤ t := ht
  have hd1 := (abs_lt.1 htd)
  rcases le_total t t₀ with hle | hle
  · have h1 := hk t t₀ ht0 hle (by linarith) (by linarith [min_le_left δ 1])
    have h2 := rightImg_mono_time hw x ht0 hle
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  · have h1 := hk t₀ t ht₀ hle (by linarith [min_le_right δ 1]) (by linarith [min_le_left δ 1])
    have h2 := rightImg_mono_time hw x (show (0 : ℝ) ≤ t₀ from ht₀) hle
    rw [abs_of_nonneg (by linarith)]
    linarith

/-! ### The Loewner equation away from collisions -/

/-- Away from the driver, no point `y > x` is swallowed. -/
lemma Alive.of_rightImg_sub_gt (hw : Continuous w) {x y a b c : ℝ} (ha : 0 ≤ a) (hc : 0 < c)
    (hgap : ∀ u ∈ Icc a b, c < rightImg w x u - w u) (hxy : x < y) (hy : Alive w y a) :
    Alive w y b :=
  hy.of_forall_le_cflow hw ha hc fun u hu hyu => by
    have h1 := rightImg_le_gImg hw (ha.trans hu.1) hxy hyu
    have h2 := hgap u hu
    simp only [gImg] at h1
    linarith

/-- `g_u(y) − V_u ≤ y − y₀` for alive `y` when every alive point above `x` at time `u` is
`≥ y₀`. -/
lemma gImg_sub_rightImg_le (hw : Continuous w) {x y y₀ u : ℝ} (hu : 0 ≤ u) (hxy : x < y)
    (hy : Alive w y u) (hy₀ : ∀ y', x < y' → Alive w y' u → y₀ ≤ y') :
    gImg w y u - rightImg w x u ≤ y - y₀ := by
  refine le_of_forall_pos_le_add fun η hη => ?_
  obtain ⟨y', hxy', hy', hlt⟩ := exists_lt_of_rightImg_lt hw hu
    (show rightImg w x u < rightImg w x u + η by linarith)
  have h0 := hy₀ y' hxy' hy'
  rcases le_or_gt y' y with hle | hgt
  · have := abs_gImg_sub_le hw hu hy' hy
    rw [abs_of_nonneg (sub_nonneg.2 hle)] at this
    linarith [le_abs_self (gImg w y u - gImg w y' u)]
  · have := (cflow_lt_and_sub_le hw hy hgt hu ⟨hu, le_rfl⟩).1
    have hyy := hy₀ y hxy hy
    simp only [gImg] at hlt ⊢
    linarith

/-- **The integral equation on a window away from the driver.** -/
lemma rightImg_eq_add_integral (hw : Continuous w) {x a b c : ℝ} (ha0 : 0 < a) (hab : a ≤ b)
    (hc0 : 0 < c) (hgap : ∀ u ∈ Icc a b, c < rightImg w x u - w u) {u : ℝ} (hu : u ∈ Icc a b) :
    rightImg w x u = rightImg w x a + ∫ r in a..u, 2 / (rightImg w x r - w r) := by
  have hVc := continuousOn_rightImg hw x
  have hA : ∀ u ∈ Icc a b, ∀ y, x < y → (Alive w y u ↔ Alive w y b) := fun u hu y hxy =>
    ⟨fun h => (h.of_rightImg_sub_gt hw (ha0.le.trans hu.1) hc0
      (fun r hr => hgap r ⟨hu.1.trans hr.1, hr.2⟩) hxy), fun h => h.mono hu.2⟩
  set A := {y | x < y ∧ Alive w y b} with hAdef
  have hAne : A.Nonempty := by
    obtain ⟨_, ⟨y, hxy, hy, -⟩⟩ := imgSet_nonempty hw x (ha0.le.trans hab)
    exact ⟨y, hxy, hy⟩
  have hAbdd : BddBelow A := ⟨x, fun y hy => hy.1.le⟩
  set y₀ := sInf A with hy₀def
  have hy₀ : ∀ u ∈ Icc a b, ∀ y', x < y' → Alive w y' u → y₀ ≤ y' := fun u hu y' hxy' hy' =>
    csInf_le hAbdd ⟨hxy', (hA u hu y' hxy').1 hy'⟩
  have hyn : ∀ n : ℕ, x < y₀ + 1 / ((n : ℝ) + 1) ∧ Alive w (y₀ + 1 / ((n : ℝ) + 1)) b := by
    intro n
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    obtain ⟨y', hy'A, hy'lt⟩ := exists_lt_of_csInf_lt hAne (show y₀ < y₀ + 1 / ((n : ℝ) + 1) by
      linarith)
    exact ⟨hy'A.1.trans hy'lt, hy'A.2.of_le hw hy'lt.le (ha0.le.trans hab)⟩
  set f : ℝ → ℝ := fun r => 2 / (rightImg w x r - w r) with hf
  have hfc : ContinuousOn f (Icc a b) := continuousOn_const.div
    ((hVc.mono fun r hr => (ha0.le.trans hr.1)).sub hw.continuousOn) fun r hr => by
      linarith [hgap r hr]
  set K := 2 + 2 * (b - a) / c ^ 2 with hK
  have hbound : ∀ n : ℕ, |rightImg w x u - (rightImg w x a + ∫ r in a..u, f r)| ≤
      K / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨hxn, hyn'⟩ := hyn n
    set yn := y₀ + 1 / ((n : ℝ) + 1)
    have hb0 : 0 ≤ b := ha0.le.trans hab
    -- closeness of `g(yn)` to `V` on `[a, b]`
    have hclose : ∀ r ∈ Icc a b, 0 ≤ gImg w yn r - rightImg w x r ∧
        gImg w yn r - rightImg w x r ≤ 1 / ((n : ℝ) + 1) := fun r hr => by
      have hr0 : 0 ≤ r := ha0.le.trans hr.1
      have hyr : Alive w yn r := hyn'.mono hr.2
      refine ⟨sub_nonneg.2 (rightImg_le_gImg hw hr0 hxn hyr), ?_⟩
      have := gImg_sub_rightImg_le hw hr0 hxn hyr (hy₀ r hr)
      simp only [yn] at this ⊢
      linarith
    -- the integral equation for `g(yn)`
    have hgi : IntervalIntegrable (fun r => 2 / cflow w yn r) volume 0 b :=
      (hyn'.continuousOn_inv hw).intervalIntegrable_of_Icc hb0
    have hs1 : uIcc (0 : ℝ) u ⊆ uIcc 0 b := by
      rw [uIcc_of_le (ha0.le.trans hu.1), uIcc_of_le hb0]
      exact Icc_subset_Icc_right hu.2
    have hs2 : uIcc (0 : ℝ) a ⊆ uIcc 0 b := by
      rw [uIcc_of_le ha0.le, uIcc_of_le hb0]
      exact Icc_subset_Icc_right hab
    have hs3 : uIcc a u ⊆ uIcc 0 b := by
      rw [uIcc_of_le hu.1, uIcc_of_le hb0]
      exact Icc_subset_Icc ha0.le hu.2
    have hsub : gImg w yn u - gImg w yn a = ∫ r in a..u, 2 / cflow w yn r := by
      rw [hyn'.gImg_eq hw ⟨ha0.le.trans hu.1, hu.2⟩, hyn'.gImg_eq hw ⟨ha0.le, hab⟩]
      rw [← intervalIntegral.integral_interval_sub_left (hgi.mono_set hs1) (hgi.mono_set hs2)]
      ring
    have hI1 : IntervalIntegrable (fun r => 2 / cflow w yn r) volume a u := hgi.mono_set hs3
    have hI2 : IntervalIntegrable f volume a u :=
      (hfc.mono (Icc_subset_Icc_right hu.2)).intervalIntegrable_of_Icc hu.1
    have hdiff : ‖∫ r in a..u, (2 / cflow w yn r - f r)‖ ≤
        2 * (1 / ((n : ℝ) + 1)) / c ^ 2 * |u - a| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const
        (f := fun r => 2 / cflow w yn r - f r) fun r hr => ?_
      rw [uIoc_of_le hu.1] at hr
      have hr' : r ∈ Icc a b := ⟨hr.1.le, hr.2.trans hu.2⟩
      obtain ⟨h1, h2⟩ := hclose r hr'
      have hg := hgap r hr'
      have hcf : rightImg w x r - w r < cflow w yn r + 1 := by simp only [gImg] at h1; linarith
      have hpos1 : c < cflow w yn r := by simp only [gImg] at h1; linarith
      rw [Real.norm_eq_abs, hf]
      simp only
      rw [div_sub_div _ _ (by linarith) (by linarith), abs_div, abs_mul,
        abs_of_pos (by linarith : (0 : ℝ) < cflow w yn r),
        abs_of_pos (by linarith : (0 : ℝ) < rightImg w x r - w r)]
      have hnum : |2 * (rightImg w x r - w r) - cflow w yn r * 2| ≤ 2 * (1 / ((n : ℝ) + 1)) := by
        rw [abs_le]
        simp only [gImg] at h1 h2
        constructor <;> linarith
      have hden : c ^ 2 ≤ cflow w yn r * (rightImg w x r - w r) := by
        rw [sq]
        exact mul_le_mul hpos1.le hg.le hc0.le (by linarith)
      calc |2 * (rightImg w x r - w r) - cflow w yn r * 2| / (cflow w yn r * (rightImg w x r - w r))
          ≤ 2 * (1 / ((n : ℝ) + 1)) / (cflow w yn r * (rightImg w x r - w r)) :=
            div_le_div_of_nonneg_right hnum (mul_pos (by linarith) (by linarith)).le
        _ ≤ 2 * (1 / ((n : ℝ) + 1)) / c ^ 2 :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    rw [Real.norm_eq_abs, intervalIntegral.integral_sub hI1 hI2, ← hsub] at hdiff
    obtain ⟨hu1, hu2⟩ := hclose u hu
    obtain ⟨ha1, ha2⟩ := hclose a ⟨le_rfl, hab⟩
    have hua : |u - a| ≤ b - a := by rw [abs_of_nonneg (by linarith [hu.1])]; linarith [hu.2]
    have hdiff' : |gImg w yn u - gImg w yn a - ∫ r in a..u, f r| ≤
        2 * (1 / ((n : ℝ) + 1)) / c ^ 2 * (b - a) :=
      hdiff.trans (mul_le_mul_of_nonneg_left hua (by positivity))
    rw [abs_le] at hdiff' ⊢
    have hKn : K / ((n : ℝ) + 1) = 2 * (1 / ((n : ℝ) + 1)) + 2 * (1 / ((n : ℝ) + 1)) / c ^ 2 * (b - a) := by
      rw [hK]; field_simp
    rw [hKn]
    constructor <;> linarith [hdiff'.1, hdiff'.2]
  refine eq_of_forall_dist_le fun ε hε => ?_
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show 0 < ε / (K + 1) by
    have : 0 < K := by rw [hK]; positivity
    positivity)
  rw [Real.dist_eq]
  refine (hbound n).trans ?_
  have hK0 : 0 < K := by rw [hK]; positivity
  have h1 : K / ((n : ℝ) + 1) = K * (1 / ((n : ℝ) + 1)) := by ring
  rw [h1]
  calc K * (1 / ((n : ℝ) + 1)) ≤ (K + 1) * (1 / ((n : ℝ) + 1)) := by
        have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        nlinarith
    _ ≤ (K + 1) * (ε / (K + 1)) := mul_le_mul_of_nonneg_left hn.le (by linarith)
    _ = ε := by field_simp

/-- **The geometric image solves the Loewner equation away from the driver** (Specification
p. 35 and p. 39: "Away from `V_t^j = W_t`, they satisfy the ordinary Loewner equation"). -/
theorem hasDerivAt_rightImg (hw : Continuous w) {x t : ℝ} (ht : 0 < t)
    (hne : rightImg w x t ≠ w t) :
    HasDerivAt (rightImg w x) (2 / (rightImg w x t - w t)) t := by
  have hVc := continuousOn_rightImg hw x
  have hgt : w t < rightImg w x t := lt_of_le_of_ne (le_rightImg hw x ht.le) hne.symm
  set c := (rightImg w x t - w t) / 2 with hc
  have hc0 : 0 < c := by rw [hc]; linarith
  have hcontAt : ContinuousAt (fun u => rightImg w x u - w u) t :=
    ((hVc t ht.le).continuousAt (Ici_mem_nhds ht)).sub hw.continuousAt
  obtain ⟨δ₀, hδ₀, hball⟩ := Metric.eventually_nhds_iff.1
    (hcontAt.eventually (lt_mem_nhds (show c < rightImg w x t - w t by rw [hc]; linarith)))
  set δ := min (δ₀ / 2) (t / 2) with hδ
  have hδ0 : 0 < δ := lt_min (by linarith) (by linarith)
  have hδ1 : δ ≤ δ₀ / 2 := min_le_left _ _
  have hδ2 : δ ≤ t / 2 := min_le_right _ _
  have ha0 : 0 < t - δ := by linarith
  have hgap : ∀ u ∈ Icc (t - δ) (t + δ), c < rightImg w x u - w u := fun u hu => by
    have hd : dist u t < δ₀ := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [hu.1, hu.2]
    exact hball hd
  set f : ℝ → ℝ := fun r => 2 / (rightImg w x r - w r) with hf
  have hfc : ContinuousOn f (Icc (t - δ) (t + δ)) := continuousOn_const.div
    ((hVc.mono fun r hr => (ha0.le.trans hr.1)).sub hw.continuousOn) fun r hr => by
      linarith [hgap r hr]
  have hmem : Icc (t - δ) (t + δ) ∈ 𝓝 t := Icc_mem_nhds (by linarith) (by linarith)
  have hfcAt : ContinuousAt f t := hfc.continuousAt hmem
  have hintI : IntervalIntegrable f volume (t - δ) t :=
    (hfc.mono (Icc_subset_Icc_right (by linarith))).intervalIntegrable_of_Icc (by linarith)
  have hmeas : StronglyMeasurableAtFilter f (𝓝 t) volume :=
    (hfc.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t).filter_mono
      (by rw [nhdsWithin_eq_nhds.2 hmem])
  have hd := (intervalIntegral.integral_hasDerivAt_right hintI hmeas hfcAt).const_add
    (rightImg w x (t - δ))
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [hmem] with u hu
  exact rightImg_eq_add_integral hw ha0 (by linarith) hc0 hgap hu

/-! ### Merged images stay merged; left and right images are separated -/

/-- **Merged geometric images stay merged** (Specification p. 37: "Geometric force points which
merge remain together"). -/
theorem rightImg_eq_of_eq (hw : Continuous w) {x x' s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (hxx : x < x') (heq : rightImg w x s = rightImg w x' s) :
    rightImg w x t = rightImg w x' t := by
  have ht : 0 ≤ t := hs.trans hst
  have hnone : ∀ y, x < y → y < x' → ¬ Alive w y s := fun y hxy hyx hy => by
    set y₁ := (y + x') / 2
    have hyy₁ : y < y₁ := by simp only [y₁]; linarith
    have hy₁x : y₁ < x' := by simp only [y₁]; linarith
    have hy₁ : Alive w y₁ s := hy.of_le hw hyy₁.le hs
    have h1 : gImg w y₁ s ≤ rightImg w x' s := le_csInf (imgSet_nonempty hw x' hs)
      fun _ ⟨y', hxy', hy', hg⟩ => hg ▸ by
        have := (cflow_lt_and_sub_le hw hy₁ (hy₁x.trans hxy') hs ⟨hs, le_rfl⟩).1
        simp only [gImg]
        linarith
    have h2 := (cflow_lt_and_sub_le hw hy hyy₁ hs ⟨hs, le_rfl⟩).1
    have h3 := rightImg_le_gImg hw hs hxy hy
    simp only [gImg] at h1 h3
    linarith
  refine le_antisymm (rightImg_mono_index hw ht hxx.le) (le_csInf (imgSet_nonempty hw x ht)
    fun _ ⟨y, hxy, hy, hg⟩ => hg ▸ ?_)
  have hyx : x' ≤ y := by
    by_contra h
    push Not at h
    exact hnone y hxy h (hy.mono hst)
  rcases hyx.lt_or_eq with hlt | rfl
  · exact rightImg_le_gImg hw ht hlt hy
  · exact (rightImg_eq_gImg hw ht hy).le

/-- The gap between a right image and a reflected left image grows: `D_t² ≥ 16 t`
(`D' = 2/a + 2/b ≥ 8/D` with `D = a + b`). -/
lemma gImg_add_gImg_neg_ge (hw : Continuous w) {y y' t : ℝ} (ht : 0 ≤ t) (hy : Alive w y t)
    (hy' : Alive (fun s => -w s) y' t) :
    4 * Real.sqrt t ≤ gImg w y t + gImg (fun s => -w s) y' t := by
  have hw' : Continuous fun s => -w s := hw.neg
  set D : ℝ → ℝ := fun u => gImg w y u + gImg (fun s => -w s) y' u with hD
  have hDc : ContinuousOn D (Icc 0 t) :=
    (hw.continuousOn.add (hy.isPosSol hw).1).add (hw'.continuousOn.add (hy'.isPosSol hw').1)
  have hDpos : ∀ u ∈ Icc 0 t, D u = cflow w y u + cflow (fun s => -w s) y' u := fun u _ => by
    simp only [hD, gImg]
    ring
  have hmono : MonotoneOn (fun u => D u ^ 2 - 16 * u) (Icc 0 t) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 t)
      ((hDc.pow 2).sub (continuousOn_const.mul continuousOn_id))
      (f' := fun u => 2 * (gImg w y u + gImg (fun s => -w s) y' u) *
        (2 / cflow w y u + 2 / cflow (fun s => -w s) y' u) - 16)
      (fun u hu => ?_) (fun u hu => ?_)
    · rw [interior_Icc] at hu
      have h1 := hy.hasDerivAt_gImg hw hu
      have h2 := hy'.hasDerivAt_gImg hw' hu
      have := ((h1.fun_add h2).pow 2).fun_sub ((hasDerivAt_id' u).const_mul 16)
      exact (this.congr_deriv (by ring)).hasDerivWithinAt
    · rw [interior_Icc] at hu
      have hu' : u ∈ Icc 0 t := Ioo_subset_Icc_self hu
      have ha := hy.cflow_pos hw hu'
      have hb := hy'.cflow_pos hw' hu'
      have hDu := hDpos u hu'
      simp only [hD] at hDu
      rw [hDu]
      set a := cflow w y u
      set b := cflow (fun s => -w s) y' u
      have key : 2 * (a + b) * (2 / a + 2 / b) = 4 * (a + b) ^ 2 / (a * b) := by
        field_simp
        ring
      rw [key, sub_nonneg, le_div_iff₀ (mul_pos ha hb)]
      nlinarith [sq_nonneg (a - b)]
  have h0 : D 0 ^ 2 - 16 * 0 ≤ D t ^ 2 - 16 * t := hmono ⟨le_rfl, ht⟩ ⟨ht, le_rfl⟩ ht
  have hD0 : 0 < D 0 := by
    rw [hDpos 0 ⟨le_rfl, ht⟩]
    exact add_pos (hy.cflow_pos hw ⟨le_rfl, ht⟩) (hy'.cflow_pos hw' ⟨le_rfl, ht⟩)
  have hDt : 0 < D t := by
    rw [hDpos t ⟨ht, le_rfl⟩]
    exact add_pos (hy.cflow_pos hw ⟨ht, le_rfl⟩) (hy'.cflow_pos hw' ⟨ht, le_rfl⟩)
  have hsq : (4 * Real.sqrt t) ^ 2 ≤ D t ^ 2 := by
    rw [mul_pow, Real.sq_sqrt ht]
    nlinarith
  exact (pow_le_pow_iff_left₀ (by positivity) hDt.le two_ne_zero).1 hsq

/-- **Left and right images never meet the driver at the same positive time**
(Specification p. 37: "Left and right groups are strictly separated at positive times"). -/
theorem rightImg_add_rightImg_neg_ge (hw : Continuous w) (x x' : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    4 * Real.sqrt t ≤ rightImg w x t + rightImg (fun s => -w s) x' t := by
  have hw' : Continuous fun s => -w s := hw.neg
  have h1 : ∀ g ∈ imgSet w x t, 4 * Real.sqrt t - rightImg (fun s => -w s) x' t ≤ g :=
    fun _ ⟨y, _, hy, hg⟩ => hg ▸ by
      have : 4 * Real.sqrt t - gImg w y t ≤ rightImg (fun s => -w s) x' t :=
        le_csInf (imgSet_nonempty hw' x' ht) fun _ ⟨y', _, hy', hg'⟩ => hg' ▸ by
          linarith [gImg_add_gImg_neg_ge hw ht hy hy']
      linarith
  have := le_csInf (imgSet_nonempty hw x ht) h1
  rw [← rightImg] at this
  linarith

end RealFlow

end MartChar

end InteractingSLE
