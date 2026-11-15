/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux50Ge8Pocket
import InteractingSLE.WangWu.BridgeTrace
import InteractingSLE.WangWu.NonBoundaryPartition

/-!
# Aux. lemma 50 for `κ ≥ 8`: the pathwise limit of the covariance exhaustion

Packet PROVE-AUX50C. Specification Aux. lemma 50, proof, (HGV4)–(HGV6) and the end of the proof (`source/spec/
p193-240.md` L851–L870, `p241-288.md` L1–L14): "These alternatives prove (HGV4) for distinct points; the diagonal is
irrelevant to Green pairings", "this variance identity rules out every additional component".

Along one continuous driver with a continuous generating trace (a fixed `ω`), for a test `φ` cut at scale `2⁻ⁿ` into
pieces `φ ψ_{n,k}` (`WangWu.pouTest`), each piece frozen at its safe exit time at level `n`:

* `isPoc` (the pocket points: swallowed by `N`, with a neighbourhood swallowed at the same time) and
  **`eq_of_not_isPoc`**: two distinct points swallowed at the same time `≤ N` cannot both be outside the pockets — each
  would be the tip of the trace at that time (QuantumZipper's bubble sets, `K3.GenTrace.isOpen_bubbleSet`);
* `pocW n a` (the weight of the pocket pieces at `a`) tends to `1_{isPoc}(a)` where `φ(a) ≠ 0`;
* **`tendsto_frozenKer`**: the frozen kernel `∑_{k,j} ψ_{n,k}(a) ψ_{n,j}(b) G_{τₖ ∨ τⱼ}(a, b)` tends to `V_N(a, b)`;
* **`tendsto_exhaust`**: the variance defect
  `∬ φφ (frozen kernel − G_N − (pocW(a) + pocW(b)) V_N + pocW(a) pocW(b) V_N)` tends to `0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal NNReal

namespace InteractingSLE

namespace Aux50Ge8

open QuantumZipper QuantumZipper.K3 LQGMetric Coupling Aux50Hit WangWu WholeField

variable {w : ℝ≥0 → ℝ}

/-! ### Pocket points and the trace -/

/-- **A pocket point at `N`**: swallowed by time `N`, with a neighbourhood swallowed at the same time. -/
def IsPoc (w : ℝ≥0 → ℝ) (N : ℝ≥0) (a : ℂ) : Prop :=
  swallowTime (Ito.rpath w) a ≤ ENNReal.ofReal (N : ℝ) ∧
    ∃ r > 0, ∀ u ∈ ball a r, swallowTime (Ito.rpath w) u = swallowTime (Ito.rpath w) a

/-- Two swallowing times that agree below `N` in the sense of hull membership agree at every time `β ≤ N`. -/
theorem eq_ofReal_iff_of_forall_le {x y : ℝ≥0∞} {N : ℝ} (hxy : ∀ t ∈ Icc (0 : ℝ) N,
    x ≤ ENNReal.ofReal t ↔ y ≤ ENNReal.ofReal t) {β : ℝ} (hβ0 : 0 ≤ β) (hβN : β ≤ N)
    (hx : x = ENNReal.ofReal β) : y = ENNReal.ofReal β := by
  have hyβ : y ≤ ENNReal.ofReal β := (hxy β ⟨hβ0, hβN⟩).1 hx.le
  refine le_antisymm hyβ ?_
  by_contra hlt
  push Not at hlt
  have hytop : y ≠ ⊤ := ne_top_of_lt hlt
  set γ := y.toReal
  have hγ : ENNReal.ofReal γ = y := ENNReal.ofReal_toReal hytop
  have hγβ : γ < β := by rw [← hγ] at hlt; exact (ENNReal.ofReal_lt_ofReal_iff'.1 hlt).1
  have h1 := (hxy γ ⟨ENNReal.toReal_nonneg, hγβ.le.trans hβN⟩).2 hγ.ge
  rw [hx] at h1
  have hγ0 : 0 ≤ γ := ENNReal.toReal_nonneg
  rcases ENNReal.ofReal_le_ofReal_iff'.1 h1 with h | h <;> linarith

/-- **The tip at a common swallowing time.** For a continuous driver with a continuous generating trace, a point
swallowed at `β ≤ N` that is not a pocket point is the tip `η(β)` of the trace; hence two distinct non-pocket points
have different swallowing times. -/
theorem eq_of_not_isPoc (hw : Continuous w) (hw0 : w 0 = 0) {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace w ⊤ η)
    {N : ℝ≥0} {a b : ℂ} (ha : a ∈ H) (hb : b ∈ H)
    (hab : swallowTime (Ito.rpath w) a = swallowTime (Ito.rpath w) b)
    (haN : swallowTime (Ito.rpath w) a ≤ ENNReal.ofReal (N : ℝ)) (hpa : ¬ IsPoc w N a) (hpb : ¬ IsPoc w N b) :
    a = b := by
  obtain ⟨W', η', T', hNT, hg, heq, -⟩ := hη.exists_genTrace hw.continuousOn hw0 (t := N) ENNReal.coe_lt_top
  have hW := continuous_rpath_of hw
  -- hull membership agrees up to `N`
  have hhull : ∀ t ∈ Icc (0 : ℝ) N, fwdHull (Ito.rpath w) t = fwdHull W' t := fun t ht =>
    YuanCorollary13.fwdHull_eq_of_eqOn_Icc hW hg.contW ht.1 fun r hr =>
      heq ⟨hr.1, hr.2.trans (ht.2.trans hNT.le)⟩
  have hsw : ∀ u ∈ H, ∀ t ∈ Icc (0 : ℝ) N,
      swallowTime (Ito.rpath w) u ≤ ENNReal.ofReal t ↔ swallowTime W' u ≤ ENNReal.ofReal t := by
    intro u hu t ht
    have := congrArg (fun S => u ∈ S) (hhull t ht)
    simp only [fwdHull, mem_ofPred_eq, eq_iff_iff] at this
    exact ⟨fun h => (this.1 ⟨hu, h⟩).2, fun h => (this.2 ⟨hu, h⟩).2⟩
  have htop : swallowTime (Ito.rpath w) a ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top haN
  set β := (swallowTime (Ito.rpath w) a).toReal with hβ
  have hβeq : swallowTime (Ito.rpath w) a = ENNReal.ofReal β := (ENNReal.ofReal_toReal htop).symm
  have hβ0 : 0 ≤ β := ENNReal.toReal_nonneg
  have hβN : β ≤ N := by rwa [hβeq, ENNReal.ofReal_le_ofReal_iff N.coe_nonneg] at haN
  -- a non-pocket point swallowed at `β` is the tip `η'(β)`
  have tip : ∀ x ∈ H, swallowTime (Ito.rpath w) x = ENNReal.ofReal β → ¬ IsPoc w N x → η' β = x := by
    intro x hx hxβ hpx
    have hx' : swallowTime W' x = ENNReal.ofReal β :=
      eq_ofReal_iff_of_forall_le (hsw x hx) hβ0 hβN hxβ
    by_cases hxη : x ∈ η' '' Icc 0 β
    · obtain ⟨s, hs, rfl⟩ := hxη
      have hK : η' s ∈ fwdHull W' s := by
        by_contra hn
        exact hg.not_mem_compl_fwdHull hs.1 le_rfl ⟨hx, hn⟩
      have hle : swallowTime W' (η' s) ≤ ENNReal.ofReal s := hK.2
      rw [hx'] at hle
      have hsβ : β ≤ s := (ENNReal.ofReal_le_ofReal_iff hs.1).1 hle
      rw [le_antisymm hs.2 hsβ]
    · exfalso
      have hmem : x ∈ bubbleSet W' η' β β := ⟨⟨hx, hxη⟩, hx'⟩
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (hg.isOpen_bubbleSet le_rfl) x hmem
      refine hpx ⟨hxβ.le.trans (ENNReal.ofReal_le_ofReal hβN), r, hr, fun u hu => ?_⟩
      have hu' := hball hu
      rw [hxβ]
      exact (eq_ofReal_iff_of_forall_le (fun t ht => (hsw u hu'.1.1 t ht).symm) hβ0 hβN hu'.2)
  rw [← tip a ha hβeq hpa, tip b hb (hab ▸ hβeq) hpb]

/-! ### The pieces of a test -/

/-- The index set of the pieces at scale `n`. -/
abbrev pIdx (φ : TestOn upperHalfPlaneOpens) (n : ℕ) : Finset (ℤ × ℤ) := pouIdx (scaleIdx (testRad φ) n)

theorem sum_pouSq_eq_one {φ : TestOn upperHalfPlaneOpens} {n : ℕ} {a : ℂ} (ha : a ∈ tsupport φ) :
    ∑ k ∈ pIdx φ n, pouSq n k a = 1 := by
  have haR : ‖a‖ ≤ testRad φ := by simpa using tsupport_subset_testRad φ ha
  have h2 : (0 : ℝ) < 2 ^ n := pow_pos two_pos n
  have hM : testRad φ * 2 ^ n ≤ (scaleIdx (testRad φ) n : ℝ) := Nat.le_ceil _
  refine sum_pouSq ?_ ?_
  · rw [abs_mul, abs_of_pos h2]
    exact (mul_le_mul_of_nonneg_right ((Complex.abs_re_le_norm a).trans haR) h2.le).trans hM
  · rw [abs_mul, abs_of_pos h2]
    exact (mul_le_mul_of_nonneg_right ((Complex.abs_im_le_norm a).trans haR) h2.le).trans hM

/-- A piece whose cut-off does not vanish at `a` is supported in `B̄(a, 4·2⁻ⁿ)`. -/
theorem tsupport_pouTest_subset_ball (φ : TestOn upperHalfPlaneOpens) {n : ℕ} {k : ℤ × ℤ} {a : ℂ}
    (hk : pouSq n k a ≠ 0) : tsupport (pouTest φ n k) ⊆ closedBall a (4 / 2 ^ n) := by
  have haC : a ∈ pouCell n k := by
    by_contra h; exact hk (pouSq_eq_zero_of_notMem h)
  intro z hz
  have hzC := ((tsupport_pouTest_subset φ n k) hz).2
  have h2 : (0 : ℝ) < 2 ^ n := pow_pos two_pos n
  have hre : |z.re - a.re| ≤ 2 / 2 ^ n := by
    have h1 : |z.re * 2 ^ n - a.re * 2 ^ n| ≤ 2 := by
      have := abs_sub_le (z.re * 2 ^ n) (k.1 : ℝ) (a.re * 2 ^ n)
      rw [abs_sub_comm (k.1 : ℝ)] at this
      linarith [hzC.1, haC.1]
    rw [le_div_iff₀ h2]
    calc |z.re - a.re| * 2 ^ n = |(z.re - a.re) * 2 ^ n| := by rw [abs_mul, abs_of_pos h2]
      _ = |z.re * 2 ^ n - a.re * 2 ^ n| := by ring_nf
      _ ≤ 2 := h1
  have him : |z.im - a.im| ≤ 2 / 2 ^ n := by
    have h1 : |z.im * 2 ^ n - a.im * 2 ^ n| ≤ 2 := by
      have := abs_sub_le (z.im * 2 ^ n) (k.2 : ℝ) (a.im * 2 ^ n)
      rw [abs_sub_comm (k.2 : ℝ)] at this
      linarith [hzC.2, haC.2]
    rw [le_div_iff₀ h2]
    calc |z.im - a.im| * 2 ^ n = |(z.im - a.im) * 2 ^ n| := by rw [abs_mul, abs_of_pos h2]
      _ = |z.im * 2 ^ n - a.im * 2 ^ n| := by ring_nf
      _ ≤ 2 := h1
  rw [mem_closedBall, dist_eq_norm]
  calc ‖z - a‖ ≤ |(z - a).re| + |(z - a).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 2 / 2 ^ n + 2 / 2 ^ n := by rw [Complex.sub_re, Complex.sub_im]; exact add_le_add hre him
    _ = 4 / 2 ^ n := by ring

/-- Where `φ(a) ≠ 0` and the cut-off does not vanish, `a` lies in the (open) support of the piece. -/
theorem mem_support_pouTest {φ : TestOn upperHalfPlaneOpens} {n : ℕ} {k : ℤ × ℤ} {a : ℂ} (hφa : φ a ≠ 0)
    (hk : pouSq n k a ≠ 0) : a ∈ Function.support (pouTest φ n k) := by
  rw [Function.mem_support, pouTest_apply]
  exact mul_ne_zero hφa hk

/-! ### The frozen times of the pieces -/

/-- **The frozen time of the piece `k` at scale `n`**: its safe exit time at level `n`, capped at `N`. -/
def frzT (w : ℝ≥0 → ℝ) (φ : TestOn upperHalfPlaneOpens) (N n : ℕ) (k : ℤ × ℤ) : ℝ≥0 :=
  safeExitTime (tsupport (pouTest φ n k)) (testLow (pouTest φ n k) / ((n : ℝ) + 1)) n N ⊤ w

theorem frzT_le (w : ℝ≥0 → ℝ) (φ : TestOn upperHalfPlaneOpens) (N n : ℕ) (k : ℤ × ℤ) : frzT w φ N n k ≤ N :=
  safeExitTime_le_sigma

/-- A point of the support of a piece is alive at the piece's frozen time. -/
theorem lt_swallowTime_frzT (hw : Continuous w) (hw0 : w 0 = 0) (φ : TestOn upperHalfPlaneOpens) (N n : ℕ)
    {k : ℤ × ℤ} {a : ℂ} (ha : a ∈ tsupport (pouTest φ n k)) :
    ENNReal.ofReal (frzT w φ N n k : ℝ) < swallowTime (Ito.rpath w) a := by
  have hKH := (pouTest φ n k).tsupport_subset
  have hδ : 0 < testLow (pouTest φ n k) / ((n : ℝ) + 1) := div_pos (testLow_pos _) (by positivity)
  have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [n.cast_nonneg (α := ℝ)]
  refine lt_swallowTime_of_safeExit hw hKH hδ ?_ ha
  exact isSafeAt_zero hKH (fun z hz => (div_le_self (testLow_pos _).le hn1).trans (testLow_le _ hz)) hw0
    ENNReal.zero_lt_top n.cast_nonneg

/-- **The frozen times of the pieces at `a` eventually pass every time at which `a` is alive.** -/
theorem eventually_le_frzT (hw : Continuous w) {φ : TestOn upperHalfPlaneOpens} {N : ℕ} {a : ℂ}
    (hφa : φ a ≠ 0) {t : ℝ≥0} (htN : t ≤ N) (halive : ENNReal.ofReal (t : ℝ) < swallowTime (Ito.rpath w) a) :
    ∀ᶠ n : ℕ in atTop, ∀ k, pouSq n k a ≠ 0 → t ≤ frzT w φ N n k := by
  have ha : a ∈ H := φ.tsupport_subset (subset_tsupport _ hφa)
  filter_upwards [eventually_le_safeExitTime_ball hw ha (N := (N : ℝ≥0)) htN halive] with n hn k hk
  have hsub := tsupport_pouTest_subset_ball φ hk
  have hm : testLow (pouTest φ n k) ≤ a.im + 4 :=
    (testLow_le _ (subset_tsupport _ (mem_support_pouTest hφa hk))).trans (by linarith)
  exact hn _ hsub _ hm

/-! ### The frozen kernel and the pocket weight -/

/-- **The frozen kernel at scale `n`**: `∑_{k,j} ψ_{n,k}(a) ψ_{n,j}(b) G_{τₖ ∨ τⱼ}(a, b)` (cut-offs only). -/
def frzKer (w : ℝ≥0 → ℝ) (φ : TestOn upperHalfPlaneOpens) (N n : ℕ) (a b : ℂ) : ℝ :=
  ∑ k ∈ pIdx φ n, ∑ j ∈ pIdx φ n,
    pouSq n k a * pouSq n j b * aGreen (Ito.rpath w) ((max (frzT w φ N n k) (frzT w φ N n j) : ℝ≥0) : ℝ) a b

open scoped Classical in
/-- **The pocket weight at scale `n`**: the total cut-off of the pieces that are pockets at `N`. -/
def pocW (w : ℝ≥0 → ℝ) (φ : TestOn upperHalfPlaneOpens) (N n : ℕ) (a : ℂ) : ℝ :=
  ∑ k ∈ pIdx φ n, (if IsPocketLabel w (tsupport (pouTest φ n k)) N ∧ (tsupport (pouTest φ n k)).Nonempty
    then (1 : ℝ) else 0) * pouSq n k a

theorem sum_sum_mul_mul {ι : Type*} (s : Finset ι) (f g : ι → ℝ) (c : ℝ) :
    ∑ k ∈ s, ∑ j ∈ s, f k * g j * c = (∑ k ∈ s, f k) * (∑ j ∈ s, g j) * c := by
  rw [Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_mul]

/-- **The frozen kernel converges to the retained kernel** where `φ(a) φ(b) ≠ 0`. -/
theorem tendsto_frzKer (hw : Continuous w) (hw0 : w 0 = 0) {φ : TestOn upperHalfPlaneOpens} {N : ℕ} {a b : ℂ}
    (hφa : φ a ≠ 0) (hφb : φ b ≠ 0) :
    Tendsto (fun n => frzKer w φ N n a b) atTop (𝓝 (VT (Ito.rpath w) N a b)) := by
  have ha : a ∈ H := φ.tsupport_subset (subset_tsupport _ hφa)
  have hb : b ∈ H := φ.tsupport_subset (subset_tsupport _ hφb)
  have haS : a ∈ tsupport φ := subset_tsupport _ hφa
  have hbS : b ∈ tsupport φ := subset_tsupport _ hφb
  set V := VT (Ito.rpath w) N a b with hV
  -- relevant pairs exist at every scale
  have hex : ∀ n, ∃ k ∈ pIdx φ n, pouSq n k a ≠ 0 := fun n => by
    by_contra hc; push Not at hc
    have := sum_pouSq_eq_one (n := n) haS
    rw [Finset.sum_eq_zero hc] at this; exact zero_ne_one this
  have hexb : ∀ n, ∃ j ∈ pIdx φ n, pouSq n j b ≠ 0 := fun n => by
    by_contra hc; push Not at hc
    have := sum_pouSq_eq_one (n := n) hbS
    rw [Finset.sum_eq_zero hc] at this; exact zero_ne_one this
  -- uniform convergence over the relevant pairs
  have key : ∀ ε > 0, ∀ᶠ n in atTop, ∀ k ∈ pIdx φ n, ∀ j ∈ pIdx φ n, pouSq n k a ≠ 0 → pouSq n j b ≠ 0 →
      |aGreen (Ito.rpath w) ((max (frzT w φ N n k) (frzT w φ N n j) : ℝ≥0) : ℝ) a b - V| < ε := by
    intro ε hε
    by_contra hc
    rw [not_eventually] at hc
    -- a choice of pairs, bad ones where possible
    have hch : ∀ n, ∃ p : (ℤ × ℤ) × (ℤ × ℤ), p.1 ∈ pIdx φ n ∧ p.2 ∈ pIdx φ n ∧ pouSq n p.1 a ≠ 0 ∧
        pouSq n p.2 b ≠ 0 ∧ ((∃ k ∈ pIdx φ n, ∃ j ∈ pIdx φ n, pouSq n k a ≠ 0 ∧ pouSq n j b ≠ 0 ∧
          ε ≤ |aGreen (Ito.rpath w) ((max (frzT w φ N n k) (frzT w φ N n j) : ℝ≥0) : ℝ) a b - V|) →
          ε ≤ |aGreen (Ito.rpath w) ((max (frzT w φ N n p.1) (frzT w φ N n p.2) : ℝ≥0) : ℝ) a b - V|) := by
      intro n
      by_cases hbad : ∃ k ∈ pIdx φ n, ∃ j ∈ pIdx φ n, pouSq n k a ≠ 0 ∧ pouSq n j b ≠ 0 ∧
          ε ≤ |aGreen (Ito.rpath w) ((max (frzT w φ N n k) (frzT w φ N n j) : ℝ≥0) : ℝ) a b - V|
      · obtain ⟨k, hk, j, hj, h1, h2, h3⟩ := hbad
        exact ⟨(k, j), hk, hj, h1, h2, fun _ => h3⟩
      · obtain ⟨k, hk, h1⟩ := hex n
        obtain ⟨j, hj, h2⟩ := hexb n
        exact ⟨(k, j), hk, hj, h1, h2, fun h => absurd h hbad⟩
    choose p hp1 hp2 hpa hpb hpbad using hch
    set s : ℕ → ℝ≥0 := fun n => max (frzT w φ N n (p n).1) (frzT w φ N n (p n).2) with hs
    have hconv : Tendsto (fun n => aGreen (Ito.rpath w) (s n) a b) atTop (𝓝 V) := by
      refine tendsto_aGreen_VT hw ha hb (N := (N : ℝ≥0)) (fun n => max_le (frzT_le w φ N n _) (frzT_le w φ N n _))
        (fun n => ?_) (fun t htN ht => ?_)
      · have h1 := lt_swallowTime_frzT hw hw0 φ N n (subset_tsupport _ (mem_support_pouTest hφa (hpa n)))
        have h2 := lt_swallowTime_frzT hw hw0 φ N n (subset_tsupport _ (mem_support_pouTest hφb (hpb n)))
        rcases le_total (frzT w φ N n (p n).1) (frzT w φ N n (p n).2) with hle | hle
        · rw [hs]; simp only [max_eq_right hle]; exact h2.trans_le (le_max_right _ _)
        · rw [hs]; simp only [max_eq_left hle]; exact h1.trans_le (le_max_left _ _)
      · rcases ht with ht | ht
        · filter_upwards [eventually_le_frzT hw hφa htN ht] with n hn
          exact (hn _ (hpa n)).trans (le_max_left _ _)
        · filter_upwards [eventually_le_frzT hw hφb htN ht] with n hn
          exact (hn _ (hpb n)).trans (le_max_right _ _)
    have hev := (Metric.tendsto_atTop.1 hconv) ε hε
    obtain ⟨n₀, hn₀⟩ := hev
    obtain ⟨n, hbadn, hn⟩ := (hc.and_eventually (eventually_ge_atTop n₀)).exists
    push Not at hbadn
    obtain ⟨k, hk, j, hj, h1, h2, h3⟩ := hbadn
    have := hpbad n ⟨k, hk, j, hj, h1, h2, h3⟩
    have h4 := hn₀ n hn
    rw [Real.dist_eq] at h4
    linarith
  -- the convex combination
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨n₀, hn₀⟩ := (key (ε / 2) (by positivity)).exists_forall_of_atTop
  refine ⟨n₀, fun n hn => ?_⟩
  have h1 := sum_pouSq_eq_one (n := n) haS
  have h2 := sum_pouSq_eq_one (n := n) hbS
  have hdiff : frzKer w φ N n a b - V = ∑ k ∈ pIdx φ n, ∑ j ∈ pIdx φ n,
      pouSq n k a * pouSq n j b *
        (aGreen (Ito.rpath w) ((max (frzT w φ N n k) (frzT w φ N n j) : ℝ≥0) : ℝ) a b - V) := by
    have : V = ∑ k ∈ pIdx φ n, ∑ j ∈ pIdx φ n, pouSq n k a * pouSq n j b * V := by
      rw [sum_sum_mul_mul, h1, h2, one_mul, one_mul]
    rw [frzKer]
    conv_lhs => rw [this]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [Real.dist_eq, hdiff]
  calc |∑ k ∈ pIdx φ n, ∑ j ∈ pIdx φ n,
        pouSq n k a * pouSq n j b *
          (aGreen (Ito.rpath w) ((max (frzT w φ N n k) (frzT w φ N n j) : ℝ≥0) : ℝ) a b - V)|
      ≤ ∑ k ∈ pIdx φ n, ∑ j ∈ pIdx φ n, pouSq n k a * pouSq n j b * (ε / 2) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk => ?_)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
        rw [abs_mul, abs_of_nonneg (mul_nonneg (pouSq_nonneg _ _ _) (pouSq_nonneg _ _ _))]
        by_cases hka : pouSq n k a = 0
        · simp [hka]
        by_cases hjb : pouSq n j b = 0
        · simp [hjb]
        exact mul_le_mul_of_nonneg_left (hn₀ n hn k hk j hj hka hjb).le
          (mul_nonneg (pouSq_nonneg _ _ _) (pouSq_nonneg _ _ _))
    _ = ε / 2 := by rw [sum_sum_mul_mul, h1, h2, one_mul, one_mul]
    _ < ε := half_lt_self hε

/-! ### The pocket weight -/

open scoped Classical in
/-- **The pocket weight is eventually the indicator of the pocket points** where `φ(a) ≠ 0`. -/
theorem eventually_pocW (φ : TestOn upperHalfPlaneOpens) (N : ℕ) {a : ℂ} (hφa : φ a ≠ 0) :
    ∀ᶠ n in atTop, pocW w φ N n a = if IsPoc w N a then 1 else 0 := by
  have haS : a ∈ tsupport φ := subset_tsupport _ hφa
  by_cases hp : IsPoc w N a
  · obtain ⟨haN, r, hr, hball⟩ := hp
    have h4 : ∀ᶠ n : ℕ in atTop, (4 : ℝ) / 2 ^ n < r := by
      have : Tendsto (fun n : ℕ => (4 : ℝ) / 2 ^ n) atTop (𝓝 0) := by
        have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)).const_mul 4
        simpa [div_eq_mul_inv, one_div, inv_pow] using this
      exact this.eventually (gt_mem_nhds hr)
    filter_upwards [h4] with n hn
    rw [ite_eq_left ⟨haN, r, hr, hball⟩, pocW]
    conv_rhs => rw [← sum_pouSq_eq_one (n := n) haS]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : pouSq n k a = 0
    · rw [hk, mul_zero]
    have hsub : tsupport (pouTest φ n k) ⊆ ball a r :=
      (tsupport_pouTest_subset_ball φ hk).trans (closedBall_subset_ball hn)
    have htop : swallowTime (Ito.rpath w) a ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top haN
    have hpl : IsPocketLabel w (tsupport (pouTest φ n k)) N ∧ (tsupport (pouTest φ n k)).Nonempty := by
      refine ⟨⟨(swallowTime (Ito.rpath w) a).toNNReal, ?_, fun z hz => ?_⟩,
        ⟨a, subset_tsupport _ (mem_support_pouTest hφa hk)⟩⟩
      · have h1 := haN
        rw [← ENNReal.coe_toNNReal htop, show ((N : ℝ≥0) : ℝ) = ((N : ℝ≥0) : ℝ) from rfl,
          ENNReal.ofReal_coe_nnreal, ENNReal.coe_le_coe] at h1
        exact h1
      · rw [hball z (hsub hz), ENNReal.coe_toNNReal htop]
    rw [ite_eq_left hpl, one_mul]
  · refine Eventually.of_forall fun n => ?_
    rw [ite_eq_right hp, pocW]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : pouSq n k a = 0
    · rw [hk, mul_zero]
    rw [ite_eq_right, zero_mul]
    rintro ⟨⟨β, hβN, hβ⟩, -⟩
    have hopen : IsOpen (Function.support (pouTest φ n k)) :=
      isOpen_ne_fun (pouTest φ n k).continuous continuous_const
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hopen a (mem_support_pouTest hφa hk)
    refine hp ⟨?_, r, hr, fun u hu => ?_⟩
    · rw [hβ a (subset_tsupport _ (mem_support_pouTest hφa hk))]
      rw [← ENNReal.ofReal_coe_nnreal]
      exact ENNReal.ofReal_le_ofReal (by exact_mod_cast hβN)
    · rw [hβ u (subset_tsupport _ (hball hu)), hβ a (subset_tsupport _ (mem_support_pouTest hφa hk))]

theorem pocW_nonneg (φ : TestOn upperHalfPlaneOpens) (N n : ℕ) (a : ℂ) : 0 ≤ pocW w φ N n a := by
  classical
  refine Finset.sum_nonneg fun k _ => mul_nonneg ?_ (pouSq_nonneg _ _ _)
  split_ifs <;> norm_num

theorem pocW_le_one {φ : TestOn upperHalfPlaneOpens} (N n : ℕ) {a : ℂ} (ha : a ∈ tsupport φ) :
    pocW w φ N n a ≤ 1 := by
  classical
  rw [← sum_pouSq_eq_one (n := n) ha, pocW]
  refine Finset.sum_le_sum fun k _ => ?_
  calc (if IsPocketLabel w (tsupport (pouTest φ n k)) N ∧ (tsupport (pouTest φ n k)).Nonempty then (1 : ℝ)
        else 0) * pouSq n k a ≤ 1 * pouSq n k a :=
        mul_le_mul_of_nonneg_right (by split_ifs <;> norm_num) (pouSq_nonneg _ _ _)
    _ = pouSq n k a := one_mul _

/-! ### The limit of the variance defect -/

/-- **The limit integrand vanishes off the diagonal**: for distinct `a, b ∈ ℍ` and pocket indicators `p_a, p_b`,
`V_N − G_N − (p_a + p_b) V_N + p_a p_b V_N = (1 − p_a)(1 − p_b) V_N − G_N = 0`. -/
theorem exhaust_limit_eq_zero (hw : Continuous w) (hw0 : w 0 = 0) {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace w ⊤ η)
    (N : ℕ) {a b : ℂ} (ha : a ∈ H) (hb : b ∈ H) (hab : a ≠ b) :
    letI := Classical.propDecidable
    VT (Ito.rpath w) N a b - aGreen (Ito.rpath w) N a b -
      ((if IsPoc w N a then 1 else 0) + (if IsPoc w N b then 1 else 0)) * VT (Ito.rpath w) N a b +
      (if IsPoc w N a then 1 else 0) * (if IsPoc w N b then 1 else 0) * VT (Ito.rpath w) N a b = 0 := by
  have hW := continuous_rpath_of hw
  by_cases hA : ENNReal.ofReal (N : ℝ) < swallowTime (Ito.rpath w) a ∧
      ENNReal.ofReal (N : ℝ) < swallowTime (Ito.rpath w) b
  · have hpa : ¬ IsPoc w N a := fun h => absurd h.1 (not_le.2 hA.1)
    have hpb : ¬ IsPoc w N b := fun h => absurd h.1 (not_le.2 hA.2)
    rw [aGreen_eq_VT hW (Nat.cast_nonneg N) (mem_actDom_iff.2 ⟨ha, hA.1⟩) (mem_actDom_iff.2 ⟨hb, hA.2⟩),
      ite_eq_right hpa, ite_eq_right hpb]
    ring
  have hmin : min (swallowTime (Ito.rpath w) a) (swallowTime (Ito.rpath w) b) ≤ ENNReal.ofReal (N : ℝ) := by
    by_contra hc
    exact hA ⟨lt_of_lt_of_le (not_le.1 hc) (min_le_left _ _), lt_of_lt_of_le (not_le.1 hc) (min_le_right _ _)⟩
  have hG : aGreen (Ito.rpath w) N a b = 0 := by
    rcases not_and_or.1 hA with h | h
    · exact aGreen_of_not_mem_left fun hD => h (mem_actDom_iff.1 hD).2
    · exact aGreen_of_not_mem_right fun hD => h (mem_actDom_iff.1 hD).2
  rw [hG]
  by_cases hpa : IsPoc w N a
  · rw [ite_eq_left hpa]; split_ifs <;> ring
  by_cases hpb : IsPoc w N b
  · rw [ite_eq_left hpb]; split_ifs; ring
  rw [ite_eq_right hpa, ite_eq_right hpb]
  by_cases hsw : swallowTime (Ito.rpath w) a = swallowTime (Ito.rpath w) b
  · exfalso
    have haN : swallowTime (Ito.rpath w) a ≤ ENNReal.ofReal (N : ℝ) := by
      have := hmin; rwa [← hsw, min_self] at this
    exact hab (eq_of_not_isPoc hw hw0 hη (N := (N : ℝ≥0)) ha hb hsw haN hpa hpb)
  · have : VT (Ito.rpath w) N a b = 0 := by
      unfold VT; rw [VTe_eq_zero_of_swallowTime_ne hW ha hb hsw hmin]; rfl
    rw [this]; ring

theorem measurable_aGreen {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {s : ℝ} (hs : 0 ≤ s) :
    Measurable fun q : ℂ × ℂ => aGreen W s q.1 q.2 := by
  have h := (measurable_kerDens (isConformalOnto_fwdMap hW hW0 hs) (u := fun _ => (1 : ℝ≥0∞))
    (v := fun _ => (1 : ℝ≥0∞)) measurable_const measurable_const).ennreal_toReal
  have e : (fun q : ℂ × ℂ => aGreen W s q.1 q.2) = fun q =>
      (kerDens (fwdMap W s) (actDom W s) (fun _ => (1 : ℝ≥0∞)) (fun _ => (1 : ℝ≥0∞)) q).toReal := by
    funext q
    have := kerDens_toReal_eq (W := W) (s := s) q.1 q.2 (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ))
    simp only [ENNReal.ofReal_one, max_eq_left zero_le_one, one_mul] at this
    exact this.symm
  rw [e]
  exact h


/-- At time `0` the kernel does not depend on the driver (any driver with `w 0 = 0`). -/
theorem aGreen_zero_eq {w' : ℝ≥0 → ℝ} (hw : Continuous w) (hw' : Continuous w') (hw0 : w 0 = 0)
    (hw'0 : w' 0 = 0) (a b : ℂ) : aGreen (Ito.rpath w) 0 a b = aGreen (Ito.rpath w') 0 a b := by
  have hW := continuous_rpath_of hw
  have hW' := continuous_rpath_of hw'
  by_cases hab : a ∈ H ∧ b ∈ H
  · have ha := mem_actDom_zero hW hab.1
    have hb := mem_actDom_zero hW hab.2
    have ha' := mem_actDom_zero hW' hab.1
    have hb' := mem_actDom_zero hW' hab.2
    unfold aGreen vtKer
    simp only [ha, hb, ha', hb', and_self, ↓reduceIte]
    rw [Ito.fwdMap_zero_eq_sub _ hab.1, Ito.fwdMap_zero_eq_sub _ hab.2, Ito.fwdMap_zero_eq_sub _ hab.1,
      Ito.fwdMap_zero_eq_sub _ hab.2]
    simp [Ito.rpath, hw0, hw'0]
  · rcases not_and_or.1 hab with h | h
    · rw [aGreen_of_not_mem_left fun hD => h hD.1, aGreen_of_not_mem_left fun hD => h hD.1]
    · rw [aGreen_of_not_mem_right fun hD => h hD.1, aGreen_of_not_mem_right fun hD => h hD.1]

/-- **The variance-defect constant** of a test: `5 ∬ |φ(a)| |φ(b)| G_ℍ(a, b)` (the time-`0` kernel of the zero
driver). -/
def exhaustBound (φ : TestOn upperHalfPlaneOpens) : ℝ :=
  5 * ∫ q, |φ q.1| * |φ q.2| * aGreen (Ito.rpath fun _ : ℝ≥0 => (0 : ℝ)) 0 q.1 q.2 ∂((volume : Measure ℂ).prod volume)

theorem frzKer_nonneg (φ : TestOn upperHalfPlaneOpens) (N n : ℕ) (a b : ℂ) : 0 ≤ frzKer w φ N n a b :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
    mul_nonneg (mul_nonneg (pouSq_nonneg _ _ _) (pouSq_nonneg _ _ _)) (aGreen_nonneg _ _ _ _)

theorem frzKer_le (hw : Continuous w) {φ : TestOn upperHalfPlaneOpens} (N n : ℕ) {a b : ℂ} (ha : a ∈ tsupport φ)
    (hb : b ∈ tsupport φ) : frzKer w φ N n a b ≤ aGreen (Ito.rpath w) 0 a b := by
  have hW := continuous_rpath_of hw
  calc frzKer w φ N n a b ≤ ∑ k ∈ pIdx φ n, ∑ j ∈ pIdx φ n, pouSq n k a * pouSq n j b *
        aGreen (Ito.rpath w) 0 a b :=
        Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (aGreen_le_zero hW (NNReal.coe_nonneg _) a b)
            (mul_nonneg (pouSq_nonneg _ _ _) (pouSq_nonneg _ _ _))
    _ = aGreen (Ito.rpath w) 0 a b := by
        rw [sum_sum_mul_mul, sum_pouSq_eq_one ha, sum_pouSq_eq_one hb, one_mul, one_mul]

/-- **The variance defect tends to `0`, pathwise** ((HGV5)–(HGV12) along one driver with a continuous trace):
`∬ φ(a) φ(b) (frozen kernel − G_N − (pocW(a) + pocW(b)) V_N + pocW(a) pocW(b) V_N) → 0`. -/
theorem tendsto_exhaust (hw : Continuous w) (hw0 : w 0 = 0) {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace w ⊤ η)
    (φ : TestOn upperHalfPlaneOpens) (N : ℕ) :
    Tendsto (fun n => ∫ q, φ q.1 * φ q.2 * (frzKer w φ N n q.1 q.2 - aGreen (Ito.rpath w) N q.1 q.2 -
        (pocW w φ N n q.1 + pocW w φ N n q.2) * VT (Ito.rpath w) N q.1 q.2 +
        pocW w φ N n q.1 * pocW w φ N n q.2 * VT (Ito.rpath w) N q.1 q.2) ∂((volume : Measure ℂ).prod volume))
      atTop (𝓝 0) := by
  classical
  have hW := continuous_rpath_of hw
  have hW0 : Ito.rpath w 0 = 0 := by simp [Ito.rpath, hw0]
  set W := Ito.rpath w with hWdef
  set F : ℕ → ℂ × ℂ → ℝ := fun n q => φ q.1 * φ q.2 * (frzKer w φ N n q.1 q.2 - aGreen W N q.1 q.2 -
    (pocW w φ N n q.1 + pocW w φ N n q.2) * VT W N q.1 q.2 + pocW w φ N n q.1 * pocW w φ N n q.2 * VT W N q.1 q.2)
    with hF
  -- a measurable form
  have hpouSq : ∀ n k, Continuous (pouSq n k) := fun n k => (contDiff_pouSq (m := 0) n k).continuous
  have hpocW : ∀ n, Measurable (pocW w φ N n) := fun n =>
    Finset.measurable_sum _ fun k _ => measurable_const.mul (hpouSq n k).measurable
  have hfrz : ∀ n, Measurable fun q : ℂ × ℂ => frzKer w φ N n q.1 q.2 := fun n =>
    Finset.measurable_sum _ fun k _ => Finset.measurable_sum _ fun j _ =>
      (((hpouSq n k).measurable.comp measurable_fst).mul ((hpouSq n j).measurable.comp measurable_snd)).mul
        (measurable_aGreen hW hW0 (NNReal.coe_nonneg _))
  have hVm := measurable_indicator_VTe hW hW0 (N : ℝ)
  have hFeq : ∀ n, F n = fun q => φ q.1 * φ q.2 * (frzKer w φ N n q.1 q.2 - aGreen W N q.1 q.2 -
      (pocW w φ N n q.1 + pocW w φ N n q.2) * (c5Vm W N q).toReal +
      pocW w φ N n q.1 * pocW w φ N n q.2 * (c5Vm W N q).toReal) := by
    intro n; funext q
    by_cases hq : q ∈ H ×ˢ H
    · simp only [hF, c5Vm, indicator_of_mem hq]; rfl
    · rcases not_and_or.1 hq with h | h
      · simp only [hF, image_eq_zero_of_notMem_tsupport fun hs => h (φ.tsupport_subset hs), zero_mul]
      · simp only [hF, image_eq_zero_of_notMem_tsupport fun hs => h (φ.tsupport_subset hs), mul_zero, zero_mul]
  have hFm : ∀ n, AEStronglyMeasurable (F n) ((volume : Measure ℂ).prod volume) := by
    intro n
    rw [hFeq n]
    refine Measurable.aestronglyMeasurable ?_
    have m1 : Measurable fun q : ℂ × ℂ => φ q.1 * φ q.2 :=
      (φ.continuous.measurable.comp measurable_fst).mul (φ.continuous.measurable.comp measurable_snd)
    have m2 : Measurable fun q : ℂ × ℂ => pocW w φ N n q.1 + pocW w φ N n q.2 :=
      ((hpocW n).comp measurable_fst).add ((hpocW n).comp measurable_snd)
    have m3 : Measurable fun q : ℂ × ℂ => pocW w φ N n q.1 * pocW w φ N n q.2 :=
      ((hpocW n).comp measurable_fst).mul ((hpocW n).comp measurable_snd)
    have m4 : Measurable fun q : ℂ × ℂ => (c5Vm W N q).toReal := ENNReal.measurable_toReal.comp hVm
    have m5 : Measurable fun q : ℂ × ℂ => aGreen W N q.1 q.2 := measurable_aGreen hW hW0 (Nat.cast_nonneg N)
    exact m1.mul ((((hfrz n).sub m5).sub (m2.mul m4)).add (m3.mul m4))
  -- the bound
  have hbound : ∀ n, ∀ᵐ q ∂((volume : Measure ℂ).prod volume),
      ‖F n q‖ ≤ 5 * (|φ q.1| * |φ q.2| * aGreen W 0 q.1 q.2) := by
    intro n
    refine Eventually.of_forall fun q => ?_
    by_cases hz : φ q.1 * φ q.2 = 0
    · simp only [hF, hz, zero_mul, norm_zero]
      exact mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (aGreen_nonneg _ _ _ _))
    have ha : q.1 ∈ tsupport φ := subset_tsupport _ (left_ne_zero_of_mul hz)
    have hb : q.2 ∈ tsupport φ := subset_tsupport _ (right_ne_zero_of_mul hz)
    have h0 := aGreen_nonneg W 0 q.1 q.2
    have k1 := frzKer_nonneg (w := w) φ N n q.1 q.2
    have k2 := frzKer_le hw N n ha hb
    have k3 := aGreen_nonneg W N q.1 q.2
    have k4 := aGreen_le_zero hW (Nat.cast_nonneg N) q.1 q.2
    have k5 := VT_nonneg W N q.1 q.2
    have k6 := VT_le_aGreen_zero hW (Nat.cast_nonneg (α := ℝ) N) (φ.tsupport_subset ha) (φ.tsupport_subset hb)
    have k7 := pocW_nonneg (w := w) φ N n q.1
    have k8 := pocW_le_one (w := w) N n ha
    have k9 := pocW_nonneg (w := w) φ N n q.2
    have k10 := pocW_le_one (w := w) N n hb
    have hin : |frzKer w φ N n q.1 q.2 - aGreen W N q.1 q.2 -
        (pocW w φ N n q.1 + pocW w φ N n q.2) * VT W N q.1 q.2 +
        pocW w φ N n q.1 * pocW w φ N n q.2 * VT W N q.1 q.2| ≤ 5 * aGreen W 0 q.1 q.2 := by
      have m1 : (pocW w φ N n q.1 + pocW w φ N n q.2) * VT W N q.1 q.2 ≤ 2 * aGreen W 0 q.1 q.2 := by
        nlinarith
      have m2 : 0 ≤ (pocW w φ N n q.1 + pocW w φ N n q.2) * VT W N q.1 q.2 := by positivity
      have m3 : pocW w φ N n q.1 * pocW w φ N n q.2 * VT W N q.1 q.2 ≤ aGreen W 0 q.1 q.2 := by
        have : pocW w φ N n q.1 * pocW w φ N n q.2 ≤ 1 := by nlinarith
        nlinarith
      have m4 : 0 ≤ pocW w φ N n q.1 * pocW w φ N n q.2 * VT W N q.1 q.2 := by positivity
      rw [abs_le]; constructor <;> linarith
    rw [hF, Real.norm_eq_abs, abs_mul, abs_mul]
    calc |φ q.1| * |φ q.2| * |frzKer w φ N n q.1 q.2 - aGreen W N q.1 q.2 -
          (pocW w φ N n q.1 + pocW w φ N n q.2) * VT W N q.1 q.2 +
          pocW w φ N n q.1 * pocW w φ N n q.2 * VT W N q.1 q.2|
        ≤ |φ q.1| * |φ q.2| * (5 * aGreen W 0 q.1 q.2) :=
          mul_le_mul_of_nonneg_left hin (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = 5 * (|φ q.1| * |φ q.2| * aGreen W 0 q.1 q.2) := by ring
  have hint : Integrable (fun q : ℂ × ℂ => 5 * (|φ q.1| * |φ q.2| * aGreen W 0 q.1 q.2))
      ((volume : Measure ℂ).prod volume) := (integrable_abs_test_aGreen_zero hW hW0 φ φ).const_mul 5
  -- the pointwise limit
  have hlim : ∀ᵐ q ∂((volume : Measure ℂ).prod volume), Tendsto (fun n => F n q) atTop (𝓝 0) := by
    filter_upwards [LQGMetric.ae_ne_diag] with q hq
    by_cases hz : φ q.1 * φ q.2 = 0
    · simp only [hF, hz, zero_mul]; exact tendsto_const_nhds
    have h1 : φ q.1 ≠ 0 := left_ne_zero_of_mul hz
    have h2 : φ q.2 ≠ 0 := right_ne_zero_of_mul hz
    have ha : q.1 ∈ H := φ.tsupport_subset (subset_tsupport _ h1)
    have hb : q.2 ∈ H := φ.tsupport_subset (subset_tsupport _ h2)
    have hK := tendsto_frzKer (N := N) hw hw0 h1 h2
    have hpa := eventually_pocW (w := w) φ N h1
    have hpb := eventually_pocW (w := w) φ N h2
    have hlim0 := exhaust_limit_eq_zero hw hw0 hη N ha hb hq
    have hc : Tendsto (fun n => frzKer w φ N n q.1 q.2 - aGreen W N q.1 q.2 -
        (pocW w φ N n q.1 + pocW w φ N n q.2) * VT W N q.1 q.2 +
        pocW w φ N n q.1 * pocW w φ N n q.2 * VT W N q.1 q.2) atTop (𝓝 0) := by
      rw [← hlim0]
      refine Tendsto.congr' ?_ (((hK.sub tendsto_const_nhds).sub tendsto_const_nhds).add tendsto_const_nhds)
      filter_upwards [hpa, hpb] with n e1 e2
      rw [e1, e2]
    have := hc.const_mul (φ q.1 * φ q.2)
    rw [mul_zero] at this
    exact this
  have := tendsto_integral_of_dominated_convergence _ hFm hint hbound hlim
  rw [integral_zero] at this
  exact this

/-- **The variance defect is bounded by `exhaustBound φ`**, uniformly in the scale and the driver. -/
theorem abs_exhaust_le (hw : Continuous w) (hw0 : w 0 = 0) (φ : TestOn upperHalfPlaneOpens) (N n : ℕ) :
    |∫ q, φ q.1 * φ q.2 * (frzKer w φ N n q.1 q.2 - aGreen (Ito.rpath w) N q.1 q.2 -
        (pocW w φ N n q.1 + pocW w φ N n q.2) * VT (Ito.rpath w) N q.1 q.2 +
        pocW w φ N n q.1 * pocW w φ N n q.2 * VT (Ito.rpath w) N q.1 q.2) ∂((volume : Measure ℂ).prod volume)|
      ≤ exhaustBound φ := by
  have hW := continuous_rpath_of hw
  have hW0 : Ito.rpath w 0 = 0 := by simp [Ito.rpath, hw0]
  have hz : Continuous fun _ : ℝ≥0 => (0 : ℝ) := continuous_const
  rw [exhaustBound, ← integral_const_mul]
  refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg (Eventually.of_forall fun q => abs_nonneg _)
    ((integrable_abs_test_aGreen_zero (continuous_rpath_of hz) (by simp [Ito.rpath]) φ φ).const_mul 5)
    (Eventually.of_forall fun q => ?_))
  dsimp only
  rw [← aGreen_zero_eq hw hz hw0 rfl]
  by_cases hzq : φ q.1 * φ q.2 = 0
  · simp only [hzq, zero_mul, abs_zero]
    exact mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (aGreen_nonneg _ _ _ _))
  have ha : q.1 ∈ tsupport φ := subset_tsupport _ (left_ne_zero_of_mul hzq)
  have hb : q.2 ∈ tsupport φ := subset_tsupport _ (right_ne_zero_of_mul hzq)
  have k1 := frzKer_nonneg (w := w) φ N n q.1 q.2
  have k2 := frzKer_le hw N n ha hb
  have k3 := aGreen_nonneg (Ito.rpath w) N q.1 q.2
  have k4 := aGreen_le_zero hW (Nat.cast_nonneg N) q.1 q.2
  have k5 := VT_nonneg (Ito.rpath w) N q.1 q.2
  have k6 := VT_le_aGreen_zero hW (Nat.cast_nonneg (α := ℝ) N) (φ.tsupport_subset ha) (φ.tsupport_subset hb)
  have k7 := pocW_nonneg (w := w) φ N n q.1
  have k8 := pocW_le_one (w := w) N n ha
  have k9 := pocW_nonneg (w := w) φ N n q.2
  have k10 := pocW_le_one (w := w) N n hb
  have m1 : (pocW w φ N n q.1 + pocW w φ N n q.2) * VT (Ito.rpath w) N q.1 q.2 ≤
      2 * aGreen (Ito.rpath w) 0 q.1 q.2 := by nlinarith
  have m2 : 0 ≤ (pocW w φ N n q.1 + pocW w φ N n q.2) * VT (Ito.rpath w) N q.1 q.2 := by positivity
  have m3 : pocW w φ N n q.1 * pocW w φ N n q.2 * VT (Ito.rpath w) N q.1 q.2 ≤ aGreen (Ito.rpath w) 0 q.1 q.2 := by
    have : pocW w φ N n q.1 * pocW w φ N n q.2 ≤ 1 := by nlinarith
    nlinarith
  have m4 : 0 ≤ pocW w φ N n q.1 * pocW w φ N n q.2 * VT (Ito.rpath w) N q.1 q.2 := by positivity
  have hin : |frzKer w φ N n q.1 q.2 - aGreen (Ito.rpath w) N q.1 q.2 -
      (pocW w φ N n q.1 + pocW w φ N n q.2) * VT (Ito.rpath w) N q.1 q.2 +
      pocW w φ N n q.1 * pocW w φ N n q.2 * VT (Ito.rpath w) N q.1 q.2| ≤ 5 * aGreen (Ito.rpath w) 0 q.1 q.2 := by
    rw [abs_le]; constructor <;> linarith
  rw [abs_mul, abs_mul]
  calc |φ q.1| * |φ q.2| * |frzKer w φ N n q.1 q.2 - aGreen (Ito.rpath w) N q.1 q.2 -
        (pocW w φ N n q.1 + pocW w φ N n q.2) * VT (Ito.rpath w) N q.1 q.2 +
        pocW w φ N n q.1 * pocW w φ N n q.2 * VT (Ito.rpath w) N q.1 q.2|
      ≤ |φ q.1| * |φ q.2| * (5 * aGreen (Ito.rpath w) 0 q.1 q.2) :=
        mul_le_mul_of_nonneg_left hin (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = 5 * (|φ q.1| * |φ q.2| * aGreen (Ito.rpath w) 0 q.1 q.2) := by ring

end Aux50Ge8

end InteractingSLE
