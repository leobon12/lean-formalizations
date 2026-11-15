/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BR4a
import InteractingSLE.Spec.Sec5.CrossRestartMobius
import InteractingSLE.Spec.Sec5.CrossRestartExit
import InteractingSLE.Spec.Supplement.GW1RestartFinalContact
import InteractingSLE.Spec.Supplement.GB6Contact
import InteractingSLE.Spec.Dimension.TraceBridge
import InteractingSLE.Spec.Sec6.DrivingCriterion

/-!
# Corollary BR4a, pathwise: the retargeted chain at one sample

Packet PROVE-BR4A. Corollary BR4a (supplement p. 610) changes the target of the centred counterflow from `0` to a
real point `v ≠ 0`. In the counterflow coordinate `w = −1/z` (the frozen `infinitySourceChart`) the original
counterflow runs from `0` to `∞`; in the coordinate of the recentred field, `w̃ = −1/(z − v)`, and
`w̃ = w/(v w + 1)`: the target change is the real Möbius map

  `mob v : w ↦ w/(v w + 1)`,  pole `p = −1/v` (the new target), `mob v 0 = 0`.

This file is deterministic. For one sample: the original driver `W` (continuous, `W 0 = 0`) with a complete transient
generating trace `γ`, a continuous driver `U` from `0`, and the hull identity `K^U_{a(t)} = mob v (K^W_t)` before the
first visit `T_v` of `v` by the physical tip, with `a(t) = hcap(mob v (K^W_t))/2` (`clock`). Then:

* `tipAt_inf_iff`: the physical tip read through the inversion is `z` iff `γ(t) z = −1`;
* `firstTipTime_eq`: the first visit is attained, `γ(T_v) = p`, `T_v > 0`;
* `pole_notMem_closure_iff`: before `T_v` (and only then) the pole avoids the closed original hull
  (boundedness of `K^U`; the interior times of the trace are dense);
* **`isExhaustingClock_clock`**: `a` is an exhausting clock on `[0, T_v)` (Möbius image theorem
  `Sec5.CrossRestart.exists_loewner_mobius_image` on each `[0, T]`, `T < T_v`; unbounded because the trace reaches
  the pole);
* **`tipAt_newChart_iff`**: at `t < T_v` the tip of `U` at `a(t)`, read through `(id.recenter v).trans ∞`, is the
  tip of `W` at `t` read through the inversion (the map identity `g^U_{a(t)} ∘ mob v = nf_t ∘ g^W_t` of the Möbius
  image theorem, the drivers being equal by `Sec6.eqOn_of_fwdHull_eq`, and the full limit of `f_t⁻¹` at `0`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull fwdMap fwdMapInv)
open QuantumZipper.CA (realMobius)

namespace InteractingSLE.Theorem14.BR4aPath

/-! ### The retargeting map and the relative clock -/

/-- **The target change in counterflow coordinates**: `w ↦ w/(v w + 1)` (real Möbius, determinant `1`). It sends the
new target `−1/v` to `∞` and fixes the seed `0`. -/
def mob (v : ℝ) : ℂ → ℂ := realMobius 1 0 v 1

/-- The new target `−1/v` in the original counterflow coordinate. -/
def pole (v : ℝ) : ℝ := -v⁻¹

/-- **The relative clock**: half the capacity of the image of the original hull. -/
def clock (v : ℝ) (w : ℝ → ℝ) (t : ℝ) : ℝ := ConformalImage.hcapSet (mob v '' fwdHull w t) / 2

theorem mob_apply (v : ℝ) (z : ℂ) : mob v z = z / (v * z + 1) := by
  simp [mob, realMobius]

theorem mobPole_eq (v : ℝ) : Sec5.CrossRestart.mobPole v 1 = pole v := by
  simp [Sec5.CrossRestart.mobPole, pole, div_eq_mul_inv]

theorem newChart_inv (v : ℝ) (w : ℂ) :
    ((Chart.id.recenter v).trans infinitySourceChart).2.1 w = -w⁻¹ + v := rfl

theorem infChart_inv (w : ℂ) : infinitySourceChart.2.1 w = -w⁻¹ := rfl

theorem ne_zero_of_mem_H' {z : ℂ} (hz : z ∈ H) : z ≠ 0 := by
  rintro rfl
  exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from hz)

theorem mul_add_one_ne_zero {v : ℝ} (hv : v ≠ 0) {z : ℂ} (hz : z ∈ H) : (v : ℂ) * z + 1 ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
    Complex.one_im, Complex.zero_im] at him
  have hz' : (0 : ℝ) < z.im := hz
  rcases mul_eq_zero.1 him with h1 | h1
  · exact hv h1
  · exact lt_irrefl _ (h1 ▸ hz')

theorem neg_inv_mob_add {v : ℝ} {z : ℂ} (hz : z ≠ 0) :
    -(mob v z)⁻¹ + v = -z⁻¹ := by
  rw [mob_apply, inv_div]
  field_simp
  ring

theorem mul_I_mem_H {y : ℝ} (hy : 0 < y) : (y : ℂ) * Complex.I ∈ H := by
  show (0 : ℝ) < ((y : ℂ) * Complex.I).im
  simpa using hy

/-! ### Limits of `−1/F` -/

/-- **`−1/F` converges to `z` iff `c z = −1`**, for `F → c` with `F ≠ 0` eventually. -/
theorem tendsto_neg_inv_iff {l : Filter ℝ} [l.NeBot] {F : ℝ → ℂ} {c z : ℂ} (hF : Tendsto F l (𝓝 c))
    (hF0 : ∀ᶠ y in l, F y ≠ 0) : Tendsto (fun y => -(F y)⁻¹) l (𝓝 z) ↔ c * z = -1 := by
  constructor
  · intro h
    have h2 : Tendsto (fun y => F y * -(F y)⁻¹) l (𝓝 (c * z)) := hF.mul h
    have h3 : ∀ᶠ y in l, -1 = F y * -(F y)⁻¹ := hF0.mono fun y hy => by field_simp
    exact tendsto_nhds_unique (tendsto_const_nhds.congr' h3) h2 |>.symm
  · intro h
    have hc : c ≠ 0 := by
      rintro rfl
      simp at h
    have hz : z = -c⁻¹ := by
      field_simp
      linear_combination h
    rw [hz]
    exact (hF.inv₀ hc).neg

/-! ### The tip through the inversion -/

section Tip

variable {W : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ}

theorem continuous_rpath (hWc : Continuous W) : Continuous fun s : ℝ => W s.toNNReal :=
  hWc.comp continuous_real_toNNReal

theorem rpath_zero (hW0 : W 0 = 0) : (fun s : ℝ => W s.toNNReal) 0 = 0 := by
  simp [hW0]

/-- The radial inverse map is nonzero (it lies in `ℍ`). -/
theorem eventually_fwdMapInv_ne_zero (hWc : Continuous W) (hW0 : W 0 = 0) (t : ℝ≥0) :
    ∀ᶠ y : ℝ in 𝓝[>] (0 : ℝ), fwdMapInv (fun s : ℝ => W s.toNNReal) t ((y : ℂ) * Complex.I) ≠ 0 := by
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact ne_zero_of_mem_H' (QuantumZipper.RS.fwdMapInv_mem_H (continuous_rpath hWc) (rpath_zero hW0)
    t.coe_nonneg (mul_I_mem_H hy))

/-- **The physical tip through the inversion** at a time of a complete generating trace: `z` iff `γ(t) z = −1`. -/
theorem tipAt_inf_iff (hγ : IsGeneratingTrace W ⊤ γ) (hWc : Continuous W) (hW0 : W 0 = 0) (t : ℝ≥0) (z : ℂ) :
    infinitySourceChart.tipAt W t z ↔ γ t * z = -1 := by
  have hlim := IsGeneratingTrace.tendsto_fwdMapInv_mul_I hγ hWc.continuousOn hW0 (ENNReal.coe_lt_top (r := t))
  exact tendsto_neg_inv_iff hlim (eventually_fwdMapInv_ne_zero hWc hW0 t)

end Tip

/-- The inverse target change `w ↦ w/(1 − v w)`. -/
def mobInv (v : ℝ) : ℂ → ℂ := realMobius 1 0 (-v) 1

theorem mobInv_mem_H (v : ℝ) {w : ℂ} (hw : w ∈ H) : mobInv v w ∈ H :=
  (QuantumZipper.CA.bijOn_realMobius_H (a := 1) (b := 0) (c := -v) (d := 1) (by norm_num)).mapsTo hw

theorem mob_mobInv (v : ℝ) {w : ℂ} (hw : w ∈ H) : mob v (mobInv v w) = w := by
  have h := Sec5.CrossRestart.realMobius_mobInv (a := 1) (b := 0) (c := v) (d := 1) (by norm_num) hw
  simpa [mob, mobInv] using h

/-- **Bounded Möbius images keep away from the pole**: if `mob v` is bounded on `S ⊆ ℍ`, then the pole `−1/v` is
not in the closure of `S` (`‖z‖ ≤ R ‖v z + 1‖` on `S`, a closed condition failing at the pole). -/
theorem pole_notMem_closure_of_bounded {v : ℝ} (hv : v ≠ 0) {S : Set ℂ} (hS : S ⊆ H) {R : ℝ}
    (hR : ∀ z ∈ S, ‖mob v z‖ ≤ R) : ((pole v : ℝ) : ℂ) ∉ closure S := by
  have hC : IsClosed {z : ℂ | ‖z‖ ≤ R * ‖(v : ℂ) * z + 1‖} :=
    isClosed_le continuous_norm (continuous_const.mul ((continuous_const.mul continuous_id).add
      continuous_const).norm)
  have hsub : S ⊆ {z : ℂ | ‖z‖ ≤ R * ‖(v : ℂ) * z + 1‖} := by
    intro z hz
    have hd := mul_add_one_ne_zero hv (hS hz)
    have h1 := hR z hz
    rw [mob_apply, norm_div] at h1
    have hpos : 0 < ‖(v : ℂ) * z + 1‖ := norm_pos_iff.2 hd
    show ‖z‖ ≤ R * ‖(v : ℂ) * z + 1‖
    rwa [div_le_iff₀ hpos] at h1
  intro hp
  have hpC := closure_minimal hsub hC hp
  simp only [mem_ofPred_eq] at hpC
  have hv' : (v : ℂ) ≠ 0 := by exact_mod_cast hv
  have h0 : (v : ℂ) * ((pole v : ℝ) : ℂ) + 1 = 0 := by
    simp only [pole, Complex.ofReal_neg, Complex.ofReal_inv, mul_neg, mul_inv_cancel₀ hv', neg_add_cancel]
  rw [h0, norm_zero, mul_zero, norm_le_zero_iff] at hpC
  have : (pole v : ℝ) = 0 := by exact_mod_cast hpC
  simp only [pole, neg_eq_zero, inv_eq_zero] at this
  exact hv this

/-- **Before the first visit the pole avoids the closed original hull**: a hull identity `K^U_A = mob v (K_t)` with
`U` continuous bounds `mob v` on `K_t`. -/
theorem pole_notMem_closure_of_hull {v : ℝ} (hv : v ≠ 0) {w U : ℝ → ℝ} (hU : Continuous U) {t A : ℝ}
    (hK : fwdHull U A = mob v '' fwdHull w t) : ((pole v : ℝ) : ℂ) ∉ closure (fwdHull w t) := by
  obtain ⟨R, hR⟩ := (isBounded_fwdHull hU A).exists_norm_le
  refine pole_notMem_closure_of_bounded hv (QuantumZipper.fwdHull_mono.2 t) fun z hz => hR _ ?_
  rw [hK]
  exact mem_image_of_mem _ hz

/-! ### The first visit -/

section Visit

variable {W : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ}

theorem continuous_of_isGeneratingTrace_top (hγ : IsGeneratingTrace W ⊤ γ) : Continuous γ := by
  have := hγ.2.1
  simp only [le_top, ofPred_true] at this
  exact continuousOn_univ.1 this

theorem pole_mul_eq {v : ℝ} (hv : v ≠ 0) {x : ℂ} : x * v = -1 ↔ x = ((pole v : ℝ) : ℂ) := by
  have hv' : (v : ℂ) ≠ 0 := by exact_mod_cast hv
  simp only [pole, Complex.ofReal_neg, Complex.ofReal_inv]
  constructor
  · intro h
    field_simp
    linear_combination h
  · rintro rfl
    field_simp

/-- **The first visit of `v` is attained**: `T_v = T₀` finite and positive, `γ(T₀) = −1/v`, and `γ(t) ≠ −1/v`
before. -/
theorem exists_firstTipTime_eq (hγ : IsGeneratingTrace W ⊤ γ) (hWc : Continuous W) (hW0 : W 0 = 0) {v : ℝ}
    (hv : v ≠ 0) (hvis : (v : ℂ) ∈ infinitySourceChart.tipSet W ⊤) :
    ∃ T₀ : ℝ≥0, firstTipTime infinitySourceChart W {(v : ℂ)} = T₀ ∧ γ T₀ = ((pole v : ℝ) : ℂ) ∧ 0 < T₀ ∧
      ∀ t : ℝ≥0, t < T₀ → γ t ≠ ((pole v : ℝ) : ℂ) := by
  have hγc := continuous_of_isGeneratingTrace_top hγ
  have hset : {t : ℝ≥0 | ∃ z ∈ ({(v : ℂ)} : Set ℂ), infinitySourceChart.tipAt W t z} =
      {t : ℝ≥0 | γ t * v = -1} := by
    ext t
    simp only [mem_ofPred_eq, mem_singleton_iff, exists_eq_left, tipAt_inf_iff hγ hWc hW0]
  have hclosed : IsClosed {t : ℝ≥0 | ∃ z ∈ ({(v : ℂ)} : Set ℂ), infinitySourceChart.tipAt W t z} := by
    rw [hset]
    exact isClosed_eq (hγc.mul continuous_const) continuous_const
  have hle : ∀ t : ℝ≥0, infinitySourceChart.tipAt W t v →
      firstTipTime infinitySourceChart W {(v : ℂ)} ≤ t := fun t ht =>
    iInf₂_le t ⟨v, mem_singleton _, ht⟩
  have hfin : firstTipTime infinitySourceChart W {(v : ℂ)} ≠ ⊤ := by
    obtain ⟨t, -, ht⟩ := hvis
    exact ne_top_of_le_ne_top ENNReal.coe_ne_top (hle t ht)
  obtain ⟨T₀, hT₀, z, hz, hzT⟩ := GW1RestartFinal.exists_attained_firstTipTime hclosed hfin
  rw [mem_singleton_iff] at hz
  subst hz
  have hγT : γ T₀ = ((pole v : ℝ) : ℂ) := (pole_mul_eq hv).1 ((tipAt_inf_iff hγ hWc hW0 T₀ _).1 hzT)
  have hbefore : ∀ t : ℝ≥0, t < T₀ → γ t ≠ ((pole v : ℝ) : ℂ) := by
    intro t ht he
    have h1 := hle t ((tipAt_inf_iff hγ hWc hW0 t _).2 ((pole_mul_eq hv).2 he))
    rw [hT₀] at h1
    exact absurd (ENNReal.coe_le_coe.1 h1) (not_le.2 ht)
  refine ⟨T₀, hT₀, hγT, ?_, hbefore⟩
  rcases eq_or_lt_of_le (zero_le (a := T₀)) with h0 | h0
  · exfalso
    have hγ0 : γ 0 = 0 := hγ.1
    rw [← h0, hγ0] at hγT
    have : (pole v : ℝ) = 0 := by exact_mod_cast hγT.symm
    simp only [pole, neg_eq_zero, inv_eq_zero] at this
    exact hv this
  · exact h0

/-- **The trace point at a positive time is a limit of earlier interior trace points** (the interior times of a
transient generating trace are dense). -/
theorem mem_closure_interior_before (hγ : IsGeneratingTrace W ⊤ γ) (hWc : Continuous W) (hW0 : W 0 = 0)
    (htr : Tendsto (fun t => ‖γ t‖) atTop atTop) {T₀ : ℝ≥0} (hT₀ : 0 < T₀) :
    γ T₀ ∈ closure {x : ℂ | ∃ q : ℝ≥0, q < T₀ ∧ γ q = x ∧ γ q ∈ H} := by
  have hγc := continuous_of_isGeneratingTrace_top hγ
  have hD := Supp8.GB6.transientDenseQ_of_isGeneratingTrace hγ hWc hW0 htr
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := Metric.continuous_iff.1 hγc T₀ ε hε
  have hlo : max ((T₀ : ℝ) - δ) 0 < T₀ := max_lt (by linarith) (by exact_mod_cast hT₀)
  obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn hlo
  obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn ha2
  have ha0 : (0 : ℝ) ≤ a := le_trans (le_max_right _ _) ha1.le
  obtain ⟨q, hqa, hqb, hqH⟩ := hD.2 a b (by exact_mod_cast ha0) (by exact_mod_cast hb1)
  have hq0 : (0 : ℝ) ≤ q := le_trans ha0 (by exact_mod_cast hqa.le)
  have hqT : (q : ℝ) < T₀ := lt_trans (by exact_mod_cast hqb) hb2
  refine ⟨γ (q : ℝ).toNNReal, ⟨(q : ℝ).toNNReal, ?_, rfl, hqH⟩, ?_⟩
  · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hq0]
    exact hqT
  · rw [dist_comm]
    refine hδε _ ?_
    rw [NNReal.dist_eq, Real.coe_toNNReal _ hq0, abs_sub_lt_iff]
    have : (T₀ : ℝ) - δ < q := lt_of_le_of_lt (le_max_left _ _) (lt_trans ha1 (by exact_mod_cast hqa))
    constructor <;> linarith

/-- Interior trace points before `t` are in the hull at `t`. -/
theorem mem_fwdHull_of_trace (hγ : IsGeneratingTrace W ⊤ γ) {q t : ℝ≥0} (hqt : q ≤ t) (hqH : γ q ∈ H) :
    γ q ∈ fwdHull (fun s : ℝ => W s.toNNReal) t := by
  have h := Sec5.CrossRestart.inter_H_subset_of_isFilling (hγ.2.2 t ENNReal.coe_lt_top)
  exact h ⟨mem_image_of_mem _ ⟨zero_le (a := q), hqt⟩, hqH⟩

end Visit

/-! ### The relative clock is an exhausting clock -/

section Clock

theorem exists_disjoint_ball_of_notMem_closure {p : ℂ} {K : Set ℂ} (h : p ∉ closure K) :
    ∃ r > 0, Disjoint (ball p r) K := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl p h
  exact ⟨r, hr, Set.disjoint_left.2 fun z hz hzK => hball hz (subset_closure hzK)⟩

/-- **The Möbius image theorem on `[0, T]`** for the target change, when the pole avoids the closed hull at `T`. -/
theorem exists_mobius_image {v : ℝ} (hv : v ≠ 0) {w : ℝ → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {T : ℝ}
    (hT : 0 ≤ T) (hp : ((pole v : ℝ) : ℂ) ∉ closure (fwdHull w T)) :
    ∃ (σ W' α κ P : ℝ → ℝ), Continuous W' ∧ W' 0 = 0 ∧ σ 0 = 0 ∧ StrictMonoOn σ (Icc 0 T) ∧
      ContinuousOn σ (Icc 0 T) ∧ ∀ t ∈ Icc (0 : ℝ) T,
        σ t = clock v w t ∧ fwdHull W' (σ t) = mob v '' fwdHull w t ∧
        W' (σ t) = α t - κ t / (w t - P t) ∧ 0 < κ t ∧ (P t : ℂ) ≠ w t ∧
        ∀ z ∈ H \ fwdHull w t,
          ConformalImage.gmap W' (σ t) (mob v z) =
            Sec5.CrossRestart.nf (α t) (κ t) (P t) (ConformalImage.gmap w t z) := by
  obtain ⟨r, hr, hd⟩ := exists_disjoint_ball_of_notMem_closure hp
  have hpole : Sec5.CrossRestart.mobPole v 1 ≠ 0 := by
    rw [mobPole_eq]
    simpa [pole] using hv
  have hd' : Disjoint (ball (Sec5.CrossRestart.mobPole v 1 : ℂ) r) (fwdHull w T) := by
    rw [mobPole_eq]
    exact hd
  obtain ⟨σ, W', α, κ, P, hW', hW'0, hσ0, hσm, hσc, hall⟩ :=
    Sec5.CrossRestart.exists_loewner_mobius_image hw hw0 hT (a := 1) (b := 0) (c := v) (d := 1)
      (by norm_num) hv hpole hr hd'
  refine ⟨σ, W', α, κ, P, hW', by simpa using hW'0, hσ0, hσm, hσc, fun t ht => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hall t ht
  refine ⟨h1, h2, h3, h4, ?_, h6⟩
  rw [h5]
  have hd'' : Disjoint (ball ((pole v : ℝ) : ℂ) r) (fwdHull w T) := hd
  have := ConformalImageFull.bdryVal_ne hw hw0 hr hd'' (by simpa [pole] using hv) ht
  rw [← mobPole_eq] at this
  exact this

variable {W U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {v : ℝ}

/-- **The relative clock is an exhausting clock on `[0, T_v)`**: it vanishes at `0`, is continuous and strictly
increasing before `T_v` (Möbius image theorem on each `[0, T]`, `T < T_v`), and is unbounded (otherwise the images
`mob v (γ(q))` of the interior trace points before `T_v` would stay in one bounded hull of `U`, while
`γ(q) → γ(T_v) = −1/v`). -/
theorem isExhaustingClock_clock (hγ : IsGeneratingTrace W ⊤ γ) (hWc : Continuous W) (hW0 : W 0 = 0)
    (htr : Tendsto (fun t => ‖γ t‖) atTop atTop) (hUc : Continuous U) (hv : v ≠ 0) {T₀ : ℝ≥0} (hT₀ : 0 < T₀)
    (hγT : γ T₀ = ((pole v : ℝ) : ℂ))
    (hK : ∀ t : ℝ≥0, t < T₀ → fwdHull (fun s : ℝ => U s.toNNReal) (clock v (fun s : ℝ => W s.toNNReal) t) =
      mob v '' fwdHull (fun s : ℝ => W s.toNNReal) t) :
    Sec5.CrossRestart.IsExhaustingClock (fun t : ℝ≥0 => clock v (fun s : ℝ => W s.toNNReal) t) T₀ := by
  set w : ℝ → ℝ := fun s => W s.toNNReal with hwdef
  set u : ℝ → ℝ := fun s => U s.toNNReal with hudef
  have hw : Continuous w := continuous_rpath hWc
  have hw0 : w 0 = 0 := rpath_zero hW0
  have hu : Continuous u := continuous_rpath hUc
  have hpole : ∀ t : ℝ≥0, t < T₀ → ((pole v : ℝ) : ℂ) ∉ closure (fwdHull w t) := fun t ht =>
    pole_notMem_closure_of_hull hv hu (hK t ht)
  -- the clock on `[0, t]`, `t < T₀`
  have hloc : ∀ t : ℝ≥0, t < T₀ → clock v w 0 = 0 ∧ StrictMonoOn (clock v w) (Icc 0 (t : ℝ)) ∧
      ContinuousOn (clock v w) (Icc 0 (t : ℝ)) := by
    intro t ht
    obtain ⟨σ, _, _, _, _, -, -, hσ0, hσm, hσc, hall⟩ := exists_mobius_image hv hw hw0 t.coe_nonneg (hpole t ht)
    have heq : EqOn σ (clock v w) (Icc 0 (t : ℝ)) := fun s hs => (hall s hs).1
    refine ⟨?_, fun x hx y hy hxy => ?_, hσc.congr fun s hs => (heq hs).symm⟩
    · rw [← heq ⟨le_rfl, t.coe_nonneg⟩, hσ0]
    · rw [← heq hx, ← heq hy]
      exact hσm hx hy hxy
  refine ⟨by exact_mod_cast hT₀, (hloc 0 hT₀).1, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    have hy' : y < T₀ := by exact_mod_cast hy
    exact (hloc y hy').2.1 ⟨x.coe_nonneg, by exact_mod_cast hxy.le⟩ ⟨y.coe_nonneg, le_rfl⟩
      (by exact_mod_cast hxy)
  · intro t ht
    have ht' : t < T₀ := by exact_mod_cast ht
    obtain ⟨T₁, htT₁, hT₁⟩ := exists_between ht'
    have hc := (hloc T₁ hT₁).2.2
    have hcw : ContinuousWithinAt (clock v w) (Icc 0 (T₁ : ℝ)) (t : ℝ) :=
      hc (t : ℝ) ⟨t.coe_nonneg, by exact_mod_cast htT₁.le⟩
    have hmaps : MapsTo (fun s : ℝ≥0 => (s : ℝ)) (Iio T₁) (Icc 0 (T₁ : ℝ)) := fun s hs =>
      ⟨s.coe_nonneg, by exact_mod_cast (le_of_lt hs)⟩
    have h1 : ContinuousWithinAt (fun s : ℝ≥0 => clock v w s) (Iio T₁) t :=
      hcw.comp NNReal.continuous_coe.continuousWithinAt hmaps
    exact (h1.continuousAt (Iio_mem_nhds htT₁)).continuousWithinAt
  · intro u₀
    by_contra hcon
    push Not at hcon
    obtain ⟨R, hR⟩ := (isBounded_fwdHull hu u₀).exists_norm_le
    set S : Set ℂ := {x : ℂ | ∃ q : ℝ≥0, q < T₀ ∧ γ q = x ∧ γ q ∈ H} with hSdef
    have hSH : S ⊆ H := by
      rintro x ⟨q, -, rfl, hq⟩
      exact hq
    have hSR : ∀ z ∈ S, ‖mob v z‖ ≤ R := by
      rintro x ⟨q, hq, rfl, hqH⟩
      refine hR _ ?_
      have hqT : (q : ℝ≥0∞) < T₀ := by exact_mod_cast hq
      refine QuantumZipper.fwdHull_mono.1 (hcon q hqT).le ?_
      rw [hK q hq]
      exact mem_image_of_mem _ (mem_fwdHull_of_trace hγ le_rfl hqH)
    have hmem := mem_closure_interior_before hγ hWc hW0 htr hT₀
    rw [hγT] at hmem
    exact pole_notMem_closure_of_bounded hv hSH hSR hmem

/-- **The pole avoids the closed hull exactly before the first visit** (the condition used for measurability). -/
theorem pole_notMem_closure_iff (hγ : IsGeneratingTrace W ⊤ γ) (hWc : Continuous W) (hW0 : W 0 = 0)
    (htr : Tendsto (fun t => ‖γ t‖) atTop atTop) (hUc : Continuous U) (hv : v ≠ 0) {T₀ : ℝ≥0} (hT₀ : 0 < T₀)
    (hγT : γ T₀ = ((pole v : ℝ) : ℂ))
    (hK : ∀ t : ℝ≥0, t < T₀ → fwdHull (fun s : ℝ => U s.toNNReal) (clock v (fun s : ℝ => W s.toNNReal) t) =
      mob v '' fwdHull (fun s : ℝ => W s.toNNReal) t) (t : ℝ≥0) :
    ((pole v : ℝ) : ℂ) ∉ closure (fwdHull (fun s : ℝ => W s.toNNReal) t) ↔ t < T₀ := by
  constructor
  · intro hp
    by_contra hle
    push Not at hle
    apply hp
    have hmem := mem_closure_interior_before hγ hWc hW0 htr hT₀
    rw [hγT] at hmem
    refine closure_mono ?_ hmem
    rintro x ⟨q, hq, rfl, hqH⟩
    exact mem_fwdHull_of_trace hγ (hq.le.trans hle) hqH
  · intro ht
    exact pole_notMem_closure_of_hull hv (continuous_rpath hUc) (hK t ht)

end Clock

/-! ### The tips -/

section Tips

/-- Solving the Möbius relation `y i + (α − κ/D) = α − κ/(f + D)` for `f`. -/
theorem eq_of_nf_relation {α κ D y : ℝ} (hκ : 0 < κ) (hD : D ≠ 0) {f : ℂ} (hf : f ∈ H)
    (h : (y : ℂ) * Complex.I + ((α - κ / D : ℝ) : ℂ) = (α : ℂ) - (κ : ℂ) / (f + D)) :
    f = (y : ℂ) * Complex.I * (D : ℂ) ^ 2 / ((κ : ℂ) - (y : ℂ) * Complex.I * D) := by
  have hfD : f + (D : ℂ) ≠ 0 := by
    intro h0
    have := congrArg Complex.im h0
    simp only [Complex.add_im, Complex.ofReal_im, add_zero, Complex.zero_im] at this
    exact lt_irrefl _ (this ▸ (show (0 : ℝ) < f.im from hf))
  have hDc : (D : ℂ) ≠ 0 := by exact_mod_cast hD
  have hden : (κ : ℂ) - (y : ℂ) * Complex.I * D ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, zero_mul, sub_zero, mul_one, Complex.zero_re] at this
    linarith
  push_cast at h
  rw [eq_div_iff hden]
  field_simp at h
  linear_combination -h

variable {W U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {v : ℝ}

/-- **The tips at one relative time** (`t < T_v`): the tip of `U` at `a(t)` read through `(id.recenter v).trans ∞`
is the tip of `W` at `t` read through the inversion. Along `y ↓ 0` the radial points of the new chain are
`mob v (f_t⁻¹(F(y)))` with `F(y) = i y D²/(κ − i y D) → 0` in `ℍ` (the map identity of the Möbius image theorem;
`D = W_t − P_t ≠ 0`), so both readings are `−1/z(y)` for two families `z(y) → γ(t)`. -/
theorem tipAt_newChart_iff (hγ : IsGeneratingTrace W ⊤ γ) (hWc : Continuous W) (hW0 : W 0 = 0)
    (hUc : Continuous U) (hU0 : U 0 = 0) (hv : v ≠ 0) {T₀ : ℝ≥0}
    (hK : ∀ t : ℝ≥0, t < T₀ → fwdHull (fun s : ℝ => U s.toNNReal) (clock v (fun s : ℝ => W s.toNNReal) t) =
      mob v '' fwdHull (fun s : ℝ => W s.toNNReal) t) {t : ℝ≥0} (ht : t < T₀) (z₀ : ℂ) :
    ((Chart.id.recenter v).trans infinitySourceChart).tipAt U (clock v (fun s : ℝ => W s.toNNReal) t).toNNReal z₀ ↔
      infinitySourceChart.tipAt W t z₀ := by
  set w : ℝ → ℝ := fun s => W s.toNNReal with hwdef
  set u : ℝ → ℝ := fun s => U s.toNNReal with hudef
  have hw : Continuous w := continuous_rpath hWc
  have hw0 : w 0 = 0 := rpath_zero hW0
  have hu : Continuous u := continuous_rpath hUc
  have hu0 : u 0 = 0 := rpath_zero hU0
  have hp := pole_notMem_closure_of_hull hv hu (hK t ht)
  obtain ⟨σ, W'', α, κ, P, hW''c, hW''0, hσ0, hσm, hσc, hall⟩ := exists_mobius_image hv hw hw0 t.coe_nonneg hp
  have htt : (t : ℝ) ∈ Icc (0 : ℝ) t := ⟨t.coe_nonneg, le_rfl⟩
  obtain ⟨hσt, hhullt, hdrv, hκ, hPne, hmap⟩ := hall t htt
  set A : ℝ := clock v w t with hAdef
  have hA0 : 0 ≤ A := by
    rw [← hσt, ← hσ0]
    exact hσm.monotoneOn ⟨le_rfl, t.coe_nonneg⟩ htt t.coe_nonneg
  -- the drivers agree on `[0, A]`
  have hagree : EqOn W'' u (Icc 0 A) := by
    refine Sec6.eqOn_of_fwdHull_eq hW''c hu hW''0 hu0 hA0 fun s hs => ?_
    have hsub := intermediate_value_Icc t.coe_nonneg hσc
    rw [hσ0, hσt] at hsub
    obtain ⟨s', hs', rfl⟩ := hsub hs
    have hs't : s'.toNNReal < T₀ := lt_of_le_of_lt (by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs'.1]; exact hs'.2) ht
    have h1 := hK s'.toNNReal hs't
    rw [Real.coe_toNNReal _ hs'.1] at h1
    rw [(hall s' hs').2.1, ← h1, (hall s' hs').1]
  have hgmap : ∀ z, ConformalImage.gmap W'' A z = ConformalImage.gmap u A z := by
    intro z
    rw [ConformalImage.gmap, ConformalImage.gmap, fwdMap_eq_of_eqOn hA0 (fun r hr => hagree hr),
      hagree ⟨hA0, le_rfl⟩]
  have hD : w t - P t ≠ 0 := sub_ne_zero.2 fun h => hPne (by rw [h])
  -- the radial points of the new chain
  set ζ : ℝ → ℂ := fun y => fwdMapInv u A ((y : ℂ) * Complex.I) with hζdef
  set z : ℝ → ℂ := fun y => mobInv v (ζ y) with hzdef
  have hζmem : ∀ y : ℝ, 0 < y → ζ y ∈ H \ fwdHull u A := fun y hy =>
    QuantumZipper.RS.fwdMapInv_mem_compl_fwdHull hu hu0 hA0 (mul_I_mem_H hy)
  have hmobz : ∀ y : ℝ, 0 < y → mob v (z y) = ζ y := fun y hy => mob_mobInv v (hζmem y hy).1
  have hzmem : ∀ y : ℝ, 0 < y → z y ∈ H \ fwdHull w t := by
    intro y hy
    refine ⟨mobInv_mem_H v (hζmem y hy).1, fun hzK => (hζmem y hy).2 ?_⟩
    have hKt := hK t ht
    rw [← hAdef] at hKt
    rw [hKt, ← hmobz y hy]
    exact mem_image_of_mem _ hzK
  set f : ℝ → ℂ := fun y => fwdMap w t (z y) with hfdef
  have hfH : ∀ y : ℝ, 0 < y → f y ∈ H := fun y hy =>
    QuantumZipper.FwdHolo.mapsTo_fwdMap hw t.coe_nonneg (hzmem y hy)
  have hf_eq : ∀ y : ℝ, 0 < y →
      f y = (y : ℂ) * Complex.I * ((w t - P t : ℝ) : ℂ) ^ 2 / ((κ t : ℂ) - (y : ℂ) * Complex.I * (w t - P t : ℝ)) := by
    intro y hy
    refine eq_of_nf_relation (α := α t) hκ hD (hfH y hy) ?_
    have h1 := hmap (z y) (hzmem y hy)
    have hL : ConformalImage.gmap W'' (σ t) (mob v (z y)) =
        (y : ℂ) * Complex.I + ((α t - κ t / (w t - P t) : ℝ) : ℂ) := by
      rw [hmobz y hy, ConformalImage.gmap, hdrv, hσt, fwdMap_eq_of_eqOn hA0 (fun r hr => hagree hr),
        QuantumZipper.RS.fwdMap_fwdMapInv hu hu0 hA0 (mul_I_mem_H hy)]
    rw [hL, Sec5.CrossRestart.nf, ConformalImage.gmap] at h1
    rw [h1]
    congr 2
    push_cast
    ring
  -- `F(y) → 0` inside `ℍ`
  have hcont : Continuous fun y : ℝ =>
      (y : ℂ) * Complex.I * ((w t - P t : ℝ) : ℂ) ^ 2 / ((κ t : ℂ) - (y : ℂ) * Complex.I * (w t - P t : ℝ)) := by
    refine Continuous.div (by fun_prop) (by fun_prop) fun y h0 => ?_
    have := congrArg Complex.re h0
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, zero_mul, sub_zero, mul_one, Complex.zero_re] at this
    linarith
  have hf0 : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝[H] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have h1 := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simp only [Complex.ofReal_zero, zero_mul, zero_div] at h1
      refine h1.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (hf_eq y hy).symm
    · filter_upwards [self_mem_nhdsWithin] with y hy
      exact hfH y hy
  have hzlim : Tendsto z (𝓝[>] (0 : ℝ)) (𝓝 (γ t)) := by
    have h1 := (IsGeneratingTrace.tendsto_fwdMapInv_tip hγ hWc.continuousOn hW0
      (ENNReal.coe_lt_top (r := t))).comp hf0
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact QuantumZipper.RS.fwdMapInv_fwdMap hw hw0 t.coe_nonneg (hzmem y hy)
  have hz0 : ∀ᶠ y in 𝓝[>] (0 : ℝ), z y ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact ne_zero_of_mem_H' (hzmem y hy).1
  -- both readings
  have hnew : ((Chart.id.recenter v).trans infinitySourceChart).tipAt U A.toNNReal z₀ ↔
      Tendsto (fun y => -(z y)⁻¹) (𝓝[>] (0 : ℝ)) (𝓝 z₀) := by
    unfold Chart.tipAt
    rw [Real.coe_toNNReal _ hA0]
    refine tendsto_congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    rw [newChart_inv]
    show -(ζ y)⁻¹ + (v : ℂ) = -(z y)⁻¹
    rw [← hmobz y hy, neg_inv_mob_add (ne_zero_of_mem_H' (hzmem y hy).1)]
  rw [hnew, tendsto_neg_inv_iff hzlim hz0, tipAt_inf_iff hγ hWc hW0]

end Tips

/-! ### The measurable inverse clock and the conclusion at one sample -/

section Conclusion

/-- **The inverse clock read on rational times**: `ℓ(u) = sup {q ∈ ℚ≥0 : ok(q), a(q) < u}` (measurable in the sample
when `a(q)` and `ok(q)` are). -/
def invClk (a : ℝ≥0 → ℝ) (ok : ℝ≥0 → Prop) (u : ℝ≥0) : ℝ≥0 :=
  open scoped Classical in
  ⨆ q : ℚ, if 0 ≤ q ∧ ok (q : ℝ).toNNReal ∧ a (q : ℝ).toNNReal < u then (q : ℝ).toNNReal else 0

/-- On an exhausting clock with `ok(t) ↔ t < T`, the rational inverse clock is the inverse. -/
theorem invClk_eq_clockInv {a : ℝ≥0 → ℝ} {T₀ : ℝ≥0} (ha : Sec5.CrossRestart.IsExhaustingClock a T₀)
    {ok : ℝ≥0 → Prop} (hok : ∀ t, ok t ↔ t < T₀) (u : ℝ≥0) :
    invClk a ok u = Sec5.CrossRestart.clockInv a T₀ u := by
  classical
  set t₀ := Sec5.CrossRestart.clockInv a T₀ u with ht₀
  obtain ⟨ht₀T, ht₀u⟩ := ha.clockInv_spec u
  have ht₀T' : t₀ < T₀ := by exact_mod_cast ht₀T
  have hterm : ∀ q : ℚ, (if 0 ≤ q ∧ ok (q : ℝ).toNNReal ∧ a (q : ℝ).toNNReal < u then (q : ℝ).toNNReal
      else 0) ≤ t₀ := by
    intro q
    split_ifs with hq
    · obtain ⟨-, hqok, hqa⟩ := hq
      have hqT := (hok _).1 hqok
      by_contra hlt
      push Not at hlt
      have h1 := (ha.mono.le_iff_le (show ((t₀ : ℝ≥0) : ℝ≥0∞) < T₀ by exact_mod_cast ht₀T')
        (show (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < T₀ by exact_mod_cast hqT)).2 hlt.le
      rw [ht₀u] at h1
      exact absurd hqa (not_lt.2 h1)
    · exact zero_le
  have hbdd : BddAbove (range fun q : ℚ => (if 0 ≤ q ∧ ok (q : ℝ).toNNReal ∧ a (q : ℝ).toNNReal < u then
      (q : ℝ).toNNReal else 0)) := ⟨t₀, by rintro _ ⟨q, rfl⟩; exact hterm q⟩
  refine le_antisymm (ciSup_le hterm) ?_
  refine le_of_forall_lt fun c hc => ?_
  obtain ⟨q, hcq, hqt⟩ := exists_rat_btwn (show (c : ℝ) < t₀ from hc)
  have hq0 : (0 : ℝ) ≤ q := le_trans c.coe_nonneg hcq.le
  have hqt' : (q : ℝ).toNNReal < t₀ := by
    rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hq0]
    exact hqt
  have hqa : a (q : ℝ).toNNReal < u := by
    rw [← ht₀u]
    exact ha.mono (show (((q : ℝ).toNNReal : ℝ≥0) : ℝ≥0∞) < T₀ by exact_mod_cast hqt'.trans ht₀T')
      (show ((t₀ : ℝ≥0) : ℝ≥0∞) < T₀ by exact_mod_cast ht₀T') hqt'
  have hle := le_ciSup hbdd q
  simp only [show (0 : ℚ) ≤ q by exact_mod_cast hq0, (hok _).2 (hqt'.trans ht₀T'), hqa, and_self,
    ↓reduceIte] at hle
  refine lt_of_lt_of_le ?_ hle
  rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hq0]
  exact hcq

variable {W U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {v : ℝ}

/-- **Corollary BR4a's pathwise conclusion at one sample, from the hull identity.** With the original driver `W`
(continuous, `W 0 = 0`, complete transient generating trace `γ`), the continuous driver `U` from `0`, a visited
real point `v ≠ 0` and the hull identity before the first visit, the rational inverse clock
`ℓ = invClk a ok` (`a` the relative clock, `ok(q)`: the pole avoids the closed hull at `q`) is continuous, strictly
increasing, onto `[0, T_v)`, and reads the tips: `tip^U(r)` through `(id.recenter v).trans ∞` is `tip^W(ℓ(r))`
through `∞`. -/
theorem retarget_of_hulls (hγ : IsGeneratingTrace W ⊤ γ) (hWc : Continuous W) (hW0 : W 0 = 0)
    (htr : Tendsto (fun t => ‖γ t‖) atTop atTop) (hUc : Continuous U) (hU0 : U 0 = 0) (hv : v ≠ 0)
    (hvis : (v : ℂ) ∈ infinitySourceChart.tipSet W ⊤)
    (hK : ∀ t : ℝ≥0, (t : ℝ≥0∞) < firstTipTime infinitySourceChart W {(v : ℂ)} →
      fwdHull (fun s : ℝ => U s.toNNReal) (clock v (fun s : ℝ => W s.toNNReal) t) =
        mob v '' fwdHull (fun s : ℝ => W s.toNNReal) t) :
    Continuous (invClk (fun t : ℝ≥0 => clock v (fun s : ℝ => W s.toNNReal) t)
        (fun t => ((pole v : ℝ) : ℂ) ∉ closure (fwdHull (fun s : ℝ => W s.toNNReal) t))) ∧
      StrictMono (invClk (fun t : ℝ≥0 => clock v (fun s : ℝ => W s.toNNReal) t)
        (fun t => ((pole v : ℝ) : ℂ) ∉ closure (fwdHull (fun s : ℝ => W s.toNNReal) t))) ∧
      range (invClk (fun t : ℝ≥0 => clock v (fun s : ℝ => W s.toNNReal) t)
        (fun t => ((pole v : ℝ) : ℂ) ∉ closure (fwdHull (fun s : ℝ => W s.toNNReal) t))) =
          {t : ℝ≥0 | (t : ℝ≥0∞) < firstTipTime infinitySourceChart W {(v : ℂ)}} ∧
      ∀ (r : ℝ≥0) (z : ℂ), ((Chart.id.recenter v).trans infinitySourceChart).tipAt U r z ↔
        infinitySourceChart.tipAt W (invClk (fun t : ℝ≥0 => clock v (fun s : ℝ => W s.toNNReal) t)
          (fun t => ((pole v : ℝ) : ℂ) ∉ closure (fwdHull (fun s : ℝ => W s.toNNReal) t)) r) z := by
  obtain ⟨T₀, hT₀, hγT, hT₀pos, -⟩ := exists_firstTipTime_eq hγ hWc hW0 hv hvis
  have hK' : ∀ t : ℝ≥0, t < T₀ → fwdHull (fun s : ℝ => U s.toNNReal) (clock v (fun s : ℝ => W s.toNNReal) t) =
      mob v '' fwdHull (fun s : ℝ => W s.toNNReal) t := fun t ht => hK t (by rw [hT₀]; exact_mod_cast ht)
  have ha := isExhaustingClock_clock hγ hWc hW0 htr hUc hv hT₀pos hγT hK'
  have hok := pole_notMem_closure_iff hγ hWc hW0 htr hUc hv hT₀pos hγT hK'
  have heq : invClk (fun t : ℝ≥0 => clock v (fun s : ℝ => W s.toNNReal) t)
      (fun t => ((pole v : ℝ) : ℂ) ∉ closure (fwdHull (fun s : ℝ => W s.toNNReal) t)) =
      Sec5.CrossRestart.clockInv (fun t : ℝ≥0 => clock v (fun s : ℝ => W s.toNNReal) t) T₀ :=
    funext (invClk_eq_clockInv ha hok)
  rw [heq, hT₀]
  refine ⟨ha.continuous_clockInv, ha.strictMono_clockInv, ?_, fun r z => ?_⟩
  · rw [← image_univ]
    exact ha.image_clockInv
  · obtain ⟨h1, -⟩ := ha.clockInv_spec r
    have h2 := tipAt_newChart_iff hγ hWc hW0 hUc hU0 hv hK' (t := Sec5.CrossRestart.clockInv
      (fun t : ℝ≥0 => clock v (fun s : ℝ => W s.toNNReal) t) T₀ r) (by exact_mod_cast h1) z
    rw [ha.toNNReal_clockInv r] at h2
    exact h2

end Conclusion

end InteractingSLE.Theorem14.BR4aPath
