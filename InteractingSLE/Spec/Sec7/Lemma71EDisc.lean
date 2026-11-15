/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Lemma71ELog
import InteractingSLE.Spec.Sec7.Lemma71EPath

/-!
# Measurable disc charts of a random simply connected domain, with a random base point

Packet PROVE-LEMMA71E (PROVE-LEMMA71D's "What remains" C (ii)): `Foundations/Complex/Kernel.lean` gives measurable
normalized Riemann maps of a random simply connected domain `U ω` **with a fixed base point** `a ∈ U ω`. A random
pocket contains no fixed point, so the base point is chosen as the first point of a dense sequence `e` lying in the
domain (`baseIdx`, measurable), and the normalized maps for the base point `e j` are patched over `j` (the domain is
replaced by the ball `B(e j, 1)` where `e j` is not in it, `patchDom`).

## Main results

* `measurableSet_mem_of_closedBall`, `patchDom`, `baseIdx`, `measurable_baseIdx`, `measurable_comp_idx`;
* **`exists_measurable_discPair`**: measurable normalized charts `Φ ω : C ω → 𝔻` (extended by `0`) and their
  inverses `F ω : 𝔻 → C ω` (jointly measurable on `Ω × 𝔻`), with the random base point `a ω = F ω 0`.
* `discLog`, **`isDerivLog_discLog`**: the logarithm of `F′` with `discLog F 0 = log F′(0)` real, written through chain
  sums of `F′` (`Lemma71ELog.lean`), so that it is measurable in `ω` (**`measurable_discLog_comp`**);
* `exists_measurable_approach`, `exists_measurable_approach_infty`: measurable approach sequences (through a given
  dense sequence) to a measurable point of the closure and to `∞`, for the marked boundary points `x₀`, `y₀`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Filter Topology Metric Function MeasureTheory
open QuantumZipper (H)
open SupercriticalConformalCovariance (IsConformalBijection)
open scoped ComplexOrder

namespace InteractingSLE.Sec7.Lemma71E

variable {Ω : Type*}

section Index

open Classical in
/-- The index of the first point of the sequence `e` lying in `C ω` (`0` if there is none). -/
def baseIdx (C : Ω → Set ℂ) (e : ℕ → ℂ) (ω : Ω) : ℕ := if h : ∃ j, e j ∈ C ω then Nat.find h else 0

theorem baseIdx_mem {C : Ω → Set ℂ} {e : ℕ → ℂ} {ω : Ω} (h : ∃ j, e j ∈ C ω) : e (baseIdx C e ω) ∈ C ω := by
  classical
  unfold baseIdx
  rw [dite_eq_left h]
  exact Nat.find_spec h

theorem complex_inv_pos {z : ℂ} (hz : 0 < z) : 0 < z⁻¹ := by
  obtain ⟨hre, him⟩ := Complex.pos_iff.1 hz
  have hz' : z = ((z.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [← him])
  rw [hz', ← ofReal_inv]
  exact Complex.zero_lt_real.2 (inv_pos.2 hre)

end Index

variable [MeasurableSpace Ω]

/-! ### Random open sets observed through closed balls -/

/-- For a random open set observed through closed balls, the point events are measurable. -/
theorem measurableSet_mem_of_closedBall {C : Ω → Set ℂ} (hCo : ∀ ω, IsOpen (C ω))
    (hCm : ∀ (c : ℂ) (r : ℝ), MeasurableSet {ω | closedBall c r ⊆ C ω}) (z : ℂ) :
    MeasurableSet {ω | z ∈ C ω} := by
  have heq : {ω | z ∈ C ω} = ⋃ n : ℕ, {ω | closedBall z (1 / ((n : ℝ) + 1)) ⊆ C ω} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · intro hz
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (hCo ω) z hz
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
      exact ⟨n, (closedBall_subset_ball hn).trans hball⟩
    · rintro ⟨n, hn⟩
      exact hn (mem_closedBall_self (by positivity))
  rw [heq]
  exact MeasurableSet.iUnion fun n => hCm _ _

open Classical in
/-- The domain `C ω` where it contains `b`, the ball `B(b, 1)` elsewhere. -/
def patchDom (C : Ω → Set ℂ) (b : ℂ) (ω : Ω) : Set ℂ := if b ∈ C ω then C ω else ball b 1

section Patch

variable {C : Ω → Set ℂ} (hCo : ∀ ω, IsOpen (C ω)) (hCc : ∀ ω, IsConnected (C ω))
  (hCsc : ∀ ω, IsSimplyConnected (C ω)) (hCH : ∀ ω, C ω ⊆ H)
  (hCm : ∀ (c : ℂ) (r : ℝ), MeasurableSet {ω | closedBall c r ⊆ C ω})
include hCo hCc hCsc hCH

omit [MeasurableSpace Ω] in
theorem patchDom_props (b : ℂ) (ω : Ω) :
    IsOpen (patchDom C b ω) ∧ IsConnected (patchDom C b ω) ∧ IsSimplyConnected (patchDom C b ω) ∧
      patchDom C b ω ≠ univ ∧ b ∈ patchDom C b ω := by
  unfold patchDom
  split_ifs with hb
  · refine ⟨hCo ω, hCc ω, hCsc ω, fun h => ?_, hb⟩
    have h0 : (0 : ℂ) ∈ C ω := h ▸ mem_univ _
    exact lt_irrefl (0 : ℝ) (show (0 : ℝ) < (0 : ℂ).im from hCH ω h0)
  · refine ⟨isOpen_ball, isConnected_ball one_pos, isSimplyConnected_ball b one_pos, fun h => ?_,
      mem_ball_self one_pos⟩
    have : b + 1 ∈ ball b 1 := h ▸ mem_univ _
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_one] at this
    exact lt_irrefl _ this

omit hCc hCsc hCH in
include hCm in
theorem measurableSet_closedBall_subset_patchDom (b c : ℂ) (r : ℝ) :
    MeasurableSet {ω | closedBall c r ⊆ patchDom C b ω} := by
  have heq : {ω | closedBall c r ⊆ patchDom C b ω} =
      ({ω | b ∈ C ω} ∩ {ω | closedBall c r ⊆ C ω}) ∪ ({ω | b ∈ C ω}ᶜ ∩ {_ω | closedBall c r ⊆ ball b 1}) := by
    ext ω
    by_cases hb : b ∈ C ω <;> simp [patchDom, hb]
  rw [heq]
  have hb := measurableSet_mem_of_closedBall hCo hCm b
  exact (hb.inter (hCm c r)).union (hb.compl.inter (MeasurableSet.const _))

end Patch

theorem measurable_baseIdx {C : Ω → Set ℂ} {e : ℕ → ℂ} (hex : ∀ ω, ∃ j, e j ∈ C ω)
    (hmem : ∀ z, MeasurableSet {ω | z ∈ C ω}) : Measurable (baseIdx C e) := by
  classical
  have heq : baseIdx C e = fun ω => Nat.find (hex ω) := by
    funext ω
    unfold baseIdx
    rw [dite_eq_left (hex ω)]
  rw [heq]
  exact measurable_find hex fun k => hmem (e k)

/-- A random choice among countably many measurable functions, with a measurable index, is measurable. -/
theorem measurable_comp_idx {β : Type*} [MeasurableSpace β] {G : ℕ → Ω → β} (hG : ∀ j, Measurable (G j))
    {J : Ω → ℕ} (hJ : Measurable J) : Measurable fun ω => G (J ω) ω := by
  have : Measurable fun x : Ω × ℕ => G x.2 x.1 := measurable_from_prod_countable_left fun j => hG j
  exact this.comp (measurable_id.prodMk hJ)

/-! ### The disc pair -/

/-- **Measurable disc charts with a random base point.** For a random open, connected, simply connected `C ω ⊆ ℍ`
observed through closed balls, and a dense sequence `e`: normalized conformal maps `Φ ω : C ω → 𝔻` (`0` off `C ω`)
measurable at every point, their inverses `F ω : 𝔻 → C ω` measurable at every point of `𝔻`, `F ω 0 = a ω` with
`F ω′(0) > 0`, and `Φ ω = (F ω)⁻¹` on `C ω`. -/
theorem exists_measurable_discPair {C : Ω → Set ℂ} (hCo : ∀ ω, IsOpen (C ω)) (hCc : ∀ ω, IsConnected (C ω))
    (hCsc : ∀ ω, IsSimplyConnected (C ω)) (hCH : ∀ ω, C ω ⊆ H)
    (hCm : ∀ (c : ℂ) (r : ℝ), MeasurableSet {ω | closedBall c r ⊆ C ω}) {e : ℕ → ℂ} (he : DenseRange e) :
    ∃ (Φ F : Ω → ℂ → ℂ) (a : Ω → ℂ),
      (∀ ω, a ω ∈ C ω) ∧ (∀ ω, IsConformalBijection (Φ ω) (C ω) (ball 0 1) ∧ Φ ω (a ω) = 0) ∧
      (∀ ω, ∀ z ∉ C ω, Φ ω z = 0) ∧ (∀ z, Measurable fun ω => Φ ω z) ∧
      (∀ ω, IsConformalBijection (F ω) (ball 0 1) (C ω) ∧ F ω 0 = a ω ∧ 0 < deriv (F ω) 0) ∧
      (∀ w ∈ ball (0 : ℂ) 1, Measurable fun ω => F ω w) ∧
      (∀ ω, EqOn (Φ ω) (invFunOn (F ω) (ball 0 1)) (C ω)) := by
  have hmem := measurableSet_mem_of_closedBall hCo hCm
  have hex : ∀ ω, ∃ j, e j ∈ C ω := fun ω => by
    obtain ⟨z, hz⟩ := (hCc ω).nonempty
    exact he.exists_mem_open (hCo ω) ⟨z, hz⟩
  have hP := patchDom_props hCo hCc hCsc hCH
  have hPm := measurableSet_closedBall_subset_patchDom hCo hCm
  have hΦex : ∀ j : ℕ, ∃ Φ : Ω → ℂ → ℂ,
      (∀ ω, IsConformalBijection (Φ ω) (patchDom C (e j) ω) (ball 0 1) ∧ Φ ω (e j) = 0 ∧
        0 < deriv (Φ ω) (e j)) ∧
      (∀ ω, ∀ z ∉ patchDom C (e j) ω, Φ ω z = 0) ∧ ∀ z, Measurable fun ω => Φ ω z := fun j =>
    exists_measurable_normalizedChart (fun ω => (hP (e j) ω).1) (fun ω => (hP (e j) ω).2.1)
      (fun ω => (hP (e j) ω).2.2.1) (fun ω => (hP (e j) ω).2.2.2.1) (fun ω => (hP (e j) ω).2.2.2.2)
      (hPm (e j))
  have hFex : ∀ j : ℕ, ∃ F : Ω → ℂ → ℂ,
      (∀ ω, IsConformalBijection (F ω) (ball 0 1) (patchDom C (e j) ω) ∧ F ω 0 = e j ∧
        0 < deriv (F ω) 0) ∧
      (∀ z ∈ ball (0 : ℂ) 1, Measurable fun ω => F ω z) ∧
      Measurable fun p : Ω × ball (0 : ℂ) 1 => F p.1 p.2 := fun j =>
    exists_measurable_normalizedRiemannMap (fun ω => (hP (e j) ω).1) (fun ω => (hP (e j) ω).2.1)
      (fun ω => (hP (e j) ω).2.2.1) (fun ω => (hP (e j) ω).2.2.2.1) (fun ω => (hP (e j) ω).2.2.2.2)
      (hPm (e j))
  choose Φj hΦj using hΦex
  choose Fj hFj using hFex
  set J := baseIdx C e with hJdef
  have hJm : Measurable J := measurable_baseIdx hex hmem
  have hJC : ∀ ω, e (J ω) ∈ C ω := fun ω => baseIdx_mem (hex ω)
  have hU : ∀ ω, patchDom C (e (J ω)) ω = C ω := fun ω => ite_eq_left (hJC ω)
  refine ⟨fun ω => Φj (J ω) ω, fun ω => Fj (J ω) ω, fun ω => e (J ω), hJC, fun ω => ?_, fun ω z hz => ?_,
    fun z => measurable_comp_idx (fun j => (hΦj j).2.2 z) hJm, fun ω => ?_,
    fun w hw => measurable_comp_idx (fun j => (hFj j).2.1 w hw) hJm, fun ω => ?_⟩
  · have h := ((hΦj (J ω)).1 ω)
    rw [hU ω] at h
    exact ⟨h.1, h.2.1⟩
  · have h := (hΦj (J ω)).2.1 ω z
    rw [hU ω] at h
    exact h hz
  · have h := ((hFj (J ω)).1 ω)
    rw [hU ω] at h
    exact h
  · -- uniqueness of the normalized chart at the base point
    have hΦ := ((hΦj (J ω)).1 ω)
    have hF := ((hFj (J ω)).1 ω)
    rw [hU ω] at hΦ hF
    obtain ⟨hFc, hF0, hF'⟩ := hF
    have hinv := isConformalBijection_invFunOn isOpen_ball hFc
    have h0ball : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
    have hinv0 : invFunOn (Fj (J ω) ω) (ball 0 1) (e (J ω)) = 0 := by
      rw [← hF0]
      exact hFc.2.injOn.leftInvOn_invFunOn h0ball
    have hder : HasDerivAt (invFunOn (Fj (J ω) ω) (ball 0 1)) (deriv (Fj (J ω) ω) 0)⁻¹ (e (J ω)) := by
      rw [← hF0]
      exact QuantumZipper.CA.Koebe.hasDerivAt_invFunOn_of_injOn isOpen_ball hFc.1 hFc.2.injOn h0ball
    have hpos := Complex.pos_iff.1 (complex_inv_pos hF')
    have hΦpos := Complex.pos_iff.1 hΦ.2.2
    exact isConformalBijection_unique_of_deriv_pos (hCo ω) (hJC ω) hΦ.1 hinv hΦ.2.1 hinv0 hΦpos.1
      hΦpos.2.symm (by rw [hder.deriv]; exact hpos.1) (by rw [hder.deriv]; exact hpos.2.symm)

/-! ### The logarithm of the derivative of the inverse disc chart -/

/-- The logarithm of `F′` on the unit disc normalized by `log F′(0)` real (for `F′(0) > 0`), written through chain
sums of `F′` along the radius. -/
def discLog (F : ℂ → ℂ) (w : ℂ) : ℂ := (Real.log (deriv F 0).re : ℂ) + limUnder atTop (chainLogSum (deriv F) w)

/-- **`discLog F` is a derivative lift of `F` on the unit disc.** -/
theorem isDerivLog_discLog {F : ℂ → ℂ} {U : Set ℂ} (hF : IsConformalBijection F (ball 0 1) U)
    (hpos : 0 < deriv F 0) : IsDerivLog F (discLog F) (ball 0 1) := by
  have hne : ∀ w ∈ ball (0 : ℂ) 1, deriv F w ≠ 0 := fun w hw =>
    QuantumZipper.CA.deriv_ne_zero_of_injOn isOpen_ball hF.1 hF.2.injOn hw
  obtain ⟨L, hL⟩ := exists_isDerivLog isOpen_ball (isSimplyConnected_ball 0 one_pos) hF.1 hne
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  have hlim : ∀ w ∈ ball (0 : ℂ) 1, limUnder atTop (chainLogSum (deriv F) w) = L w - L 0 := fun w hw =>
    (tendsto_chainLogSum_of_convex (convex_ball 0 1) h0 hw hL.1.continuousOn hL.2).limUnder_eq
  set c : ℂ := (Real.log (deriv F 0).re : ℂ) with hc
  have heq : EqOn (discLog F) (fun w => (c - L 0) + L w) (ball 0 1) := fun w hw => by
    simp only [discLog, hlim w hw, hc]
    ring
  have hexp_c : exp (c - L 0) = 1 := by
    obtain ⟨hre, him⟩ := Complex.pos_iff.1 hpos
    rw [exp_sub, hL.2 0 h0]
    have : exp c = deriv F 0 := by
      rw [hc, ← ofReal_exp, Real.exp_log hre]
      exact Complex.ext (by simp) (by simp [← him])
    rw [this, div_self (hne 0 h0)]
  refine ⟨(hL.1.const_add _).congr heq, fun w hw => ?_⟩
  rw [heq hw, exp_add, hexp_c, one_mul, hL.2 w hw]

/-- **The disc logarithm of a random holomorphic map, read at a random point, is measurable**: `F ω` holomorphic on
the disc and measurable in `ω` at every point of it, `u` measurable with values in the disc. -/
theorem measurable_discLog_comp {F : Ω → ℂ → ℂ} (hFd : ∀ ω, DifferentiableOn ℂ (F ω) (ball 0 1))
    (hFm : ∀ w ∈ ball (0 : ℂ) 1, Measurable fun ω => F ω w) {u : Ω → ℂ} (hu : Measurable u)
    (hu1 : ∀ ω, u ω ∈ ball (0 : ℂ) 1) : Measurable fun ω => discLog (F ω) (u ω) := by
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  have hdm : ∀ w ∈ ball (0 : ℂ) 1, Measurable fun ω => deriv (F ω) w := fun w hw =>
    measurable_deriv_of_measurable isOpen_ball hw hFm fun ω => (hFd ω).differentiableAt (isOpen_ball.mem_nhds hw)
  have hjoint : Measurable (Function.uncurry fun (x : ball (0 : ℂ) 1) (ω : Ω) => deriv (F ω) x) := by
    refine MeasureTheory.measurable_uncurry_of_continuous_of_measurable (fun ω => ?_) fun x => hdm x x.2
    exact (((hFd ω).deriv isOpen_ball).continuousOn).comp_continuous continuous_subtype_val fun x => x.2
  have hpt : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → Measurable fun ω => deriv (F ω) ((t : ℂ) * u ω) := by
    intro t ht
    have hmem : ∀ ω, (t : ℂ) * u ω ∈ ball (0 : ℂ) 1 := fun ω => by
      rw [mem_ball_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
      exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) ht.2) (mem_ball_zero_iff.1 (hu1 ω))
    have hsub : Measurable fun ω => (⟨(t : ℂ) * u ω, hmem ω⟩ : ball (0 : ℂ) 1) :=
      (measurable_const.mul hu).subtype_mk
    exact hjoint.comp (hsub.prodMk measurable_id)
  have hfrac : ∀ (N j : ℕ), j < N → ((j : ℝ) / N) ∈ Icc (0 : ℝ) 1 ∧ (((j + 1 : ℕ) : ℝ) / N) ∈ Icc (0 : ℝ) 1 := by
    intro N j hj
    have hN : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_le j).trans_lt hj
    refine ⟨⟨by positivity, (div_le_one hN).2 (by exact_mod_cast hj.le)⟩,
      ⟨by positivity, (div_le_one hN).2 (by exact_mod_cast hj)⟩⟩
  have hsum : ∀ N : ℕ, Measurable fun ω => chainLogSum (deriv (F ω)) (u ω) N := by
    intro N
    unfold chainLogSum
    refine Finset.measurable_sum _ fun j hj => ?_
    obtain ⟨h₀, h₁⟩ := hfrac N j (Finset.mem_range.1 hj)
    exact Complex.measurable_log.comp ((hpt _ h₁).div (hpt _ h₀))
  have hlim : Measurable fun ω => limUnder atTop fun N => chainLogSum (deriv (F ω)) (u ω) N :=
    (StronglyMeasurable.limUnder fun N => (hsum N).stronglyMeasurable).measurable
  exact (Complex.measurable_ofReal.comp (Real.measurable_log.comp
    (Complex.measurable_re.comp (hdm 0 h0)))).add hlim

/-! ### Measurable approach sequences of the marked boundary points -/

/-- **A measurable approach sequence to a measurable point of the closure**, through a given dense sequence: the
first point of `e` in `C ω` within `1/(m+1)` of `x ω`. -/
theorem exists_measurable_approach {C : Ω → Set ℂ} (hCo : ∀ ω, IsOpen (C ω))
    (hCm : ∀ z, MeasurableSet {ω | z ∈ C ω}) {e : ℕ → ℂ} (he : DenseRange e) {x : Ω → ℂ} (hx : Measurable x)
    (hxC : ∀ ω, x ω ∈ closure (C ω)) :
    ∃ N : ℕ → Ω → ℕ, (∀ m, Measurable (N m)) ∧ (∀ m ω, e (N m ω) ∈ C ω) ∧
      ∀ ω, Tendsto (fun m => e (N m ω)) atTop (𝓝[C ω] (x ω)) := by
  classical
  have hex : ∀ (m : ℕ) (ω : Ω), ∃ j, e j ∈ C ω ∧ dist (e j) (x ω) < 1 / ((m : ℝ) + 1) := by
    intro m ω
    have hr : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    obtain ⟨y, hyC, hyx⟩ := Metric.mem_closure_iff.1 (hxC ω) _ hr
    obtain ⟨j, hj⟩ := he.exists_mem_open ((hCo ω).inter isOpen_ball)
      ⟨y, hyC, mem_ball.2 (by rw [dist_comm]; exact hyx)⟩
    exact ⟨j, hj.1, mem_ball.1 hj.2⟩
  refine ⟨fun m ω => Nat.find (hex m ω), fun m => ?_, fun m ω => (Nat.find_spec (hex m ω)).1, fun ω => ?_⟩
  · exact measurable_find (hex m) fun j =>
      (hCm (e j)).inter (measurableSet_lt (measurable_const.dist hx) measurable_const)
  · refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun m => (Nat.find_spec (hex m ω)).1⟩
    refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun m => dist_nonneg) (fun m => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat)
    exact (Nat.find_spec (hex m ω)).2.le

/-- **A measurable approach sequence to `∞`** inside an unbounded random open set: the first point of `e` in `C ω`
of norm larger than `m`. -/
theorem exists_measurable_approach_infty {C : Ω → Set ℂ} (hCo : ∀ ω, IsOpen (C ω))
    (hCm : ∀ z, MeasurableSet {ω | z ∈ C ω}) {e : ℕ → ℂ} (he : DenseRange e)
    (hunb : ∀ ω, ¬ Bornology.IsBounded (C ω)) :
    ∃ N : ℕ → Ω → ℕ, (∀ m, Measurable (N m)) ∧ (∀ m ω, e (N m ω) ∈ C ω) ∧
      ∀ ω, Tendsto (fun m => e (N m ω)) atTop (Bornology.cobounded ℂ ⊓ 𝓟 (C ω)) := by
  classical
  have hex : ∀ (m : ℕ) (ω : Ω), ∃ j, e j ∈ C ω ∧ (m : ℝ) < ‖e j‖ := by
    intro m ω
    obtain ⟨y, hyC, hy⟩ : ∃ y ∈ C ω, (m : ℝ) < ‖y‖ := by
      by_contra hcon
      push Not at hcon
      exact hunb ω ((isBounded_closedBall (x := (0 : ℂ)) (r := m)).subset fun y hy =>
        mem_closedBall_zero_iff.2 (hcon y hy))
    have hU : IsOpen (C ω ∩ {z : ℂ | (m : ℝ) < ‖z‖}) := (hCo ω).inter (isOpen_lt continuous_const continuous_norm)
    obtain ⟨j, hj⟩ := he.exists_mem_open hU ⟨y, hyC, hy⟩
    exact ⟨j, hj.1, hj.2⟩
  refine ⟨fun m ω => Nat.find (hex m ω), fun m => ?_, fun m ω => (Nat.find_spec (hex m ω)).1, fun ω => ?_⟩
  · exact measurable_find (hex m) fun j => (hCm (e j)).inter (MeasurableSet.const _)
  · refine tendsto_inf.2 ⟨?_, tendsto_principal.2 (Eventually.of_forall fun m => (Nat.find_spec (hex m ω)).1)⟩
    rw [← tendsto_norm_atTop_iff_cobounded]
    exact tendsto_atTop_mono (fun m => (Nat.find_spec (hex m ω)).2.le) tendsto_natCast_atTop_atTop

end InteractingSLE.Sec7.Lemma71E
