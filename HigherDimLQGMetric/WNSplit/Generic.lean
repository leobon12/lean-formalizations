import HigherDimLQGMetric.LGF.Exists
import HigherDimLFPP.Field.OscBlock

/-!
# Generic tools for white-noise fields on `ℝ^d` (packet S5a, D-WN′ (b), (1), (4))

Source: MA3 Details (a) **D-WN′** (`planning/audits/MA3-sections-5-6.md`), construction (b) and
(1), (4); blueprint `prop:wn-split`.

Let `W` be a white noise on `L²(ℝ × ℝ^d)` and `u : ℝ^d → L²` a family of vectors.

* `wns_exists_version`: if `‖u z − u w‖² ≤ c ‖z − w‖²`, the field `z ↦ W(u z)` has a version that is
  continuous for every `ω` and measurable at every point (Kolmogorov–Čentsov; the proof of
  HigherDimLFPP's `exists_isBandVersion` for a general family);
* `wns_integral_mul_inner` (deterministic Fubini): if `u x` has a jointly measurable representative
  `U x` with `‖u x‖` locally bounded, and `V` has representative `p ↦ ∫ ψ(x) U(x, p) dx`, then
  `∫ ψ(x) ⟪u x, g⟫ dx = ⟪V, g⟫` for every `g` (port of LQGMetric's
  `GFFExist.integral_d12_mul_inner_rectL2` to a general family);
* `wns_ae_integral_mul_eq` (stochastic Fubini): for a continuous version `Y` of `x ↦ W(u x)` and
  `V` as above (weak form), `∫ ψ(x) Y(x) dx = W(V)` almost surely (the computation of F2's
  `ae_lgfOf_apply`, `E[(A − B)²] = 0`);
* `wns_block_tail`: the chaining and Borell–TIS bound of HigherDimLFPP's `Osc.block_tail` for a
  continuous version of `x ↦ W(u x)` with `‖u z − u w‖² ≤ L ‖z − w‖² / a²` (no band structure
  needed).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped RealInnerProductSpace

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd WN)

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WN d → Ω → ℝ}

/-! ## Continuous versions -/

/-- **Continuous versions** (Kolmogorov–Čentsov): if `‖u z − u w‖² ≤ c ‖z − w‖²`, then
`z ↦ W(u z)` has a version that is continuous for every `ω` and measurable at every point. -/
theorem wns_exists_version (hW : HigherDimLFPP.IsWhiteNoise P W) {u : Rd d → WN d} {c : ℝ}
    (hc0 : 0 ≤ c) (hu : ∀ z w : Rd d, ‖u z - u w‖ ^ 2 ≤ c * ‖z - w‖ ^ 2) :
    ∃ Y : Rd d → Ω → ℝ, (∀ ω, Continuous fun z => Y z ω) ∧ (∀ z, Measurable (Y z)) ∧
      ∀ z, (fun ω => Y z ω) =ᵐ[P] W (u z) := by
  set Z : (Fin d → ℝ) → Ω → ℝ := fun q => W (u (WithLp.toLp 2 q)) with hZ
  have hZm : ∀ q, Measurable (Z q) := fun q => hW.measurable _
  set c' : ℝ := c * d with hc'
  have hc'0 : 0 ≤ c' := by positivity
  set M : ℝ := QuantumZipper.gaussianAbsMoment (2 * (d + 1)) with hM
  have hM0 : 0 ≤ M := QuantumZipper.gaussianAbsMoment_nonneg _
  have hmom : ∀ R : ℕ, ∃ K, 0 ≤ K ∧
      QuantumZipper.KolmG.MomentBoundG Z P (2 * (d + 1)) ((2 * (d + 1) : ℕ) : ℝ) K R := by
    intro R
    refine ⟨c' ^ (d + 1) * M, by positivity, fun q _ q' _ => ?_⟩
    have hlaw := hW.hasLaw_sub (u (WithLp.toLp 2 q)) (u (WithLp.toLp 2 q'))
    have hE := QuantumZipper.KolmG.lintegral_pow_two_mul_of_map_eq (P := P)
      ((hW.measurable _).sub (hW.measurable _)) (d + 1) hlaw.map_eq
    simp only [Pi.sub_apply] at hE
    simp only [hZ]
    rw [hE]
    refine ENNReal.ofReal_le_ofReal ?_
    set v : ℝ := ‖u (WithLp.toLp 2 q) - u (WithLp.toLp 2 q')‖ ^ 2 with hv
    have hv0 : 0 ≤ v := sq_nonneg _
    have hvc : v ≤ c' * ‖q - q'‖ ^ 2 := by
      have h1 := hu (WithLp.toLp 2 q) (WithLp.toLp 2 q')
      rw [← WithLp.toLp_sub] at h1
      have h2 := HigherDimLFPP.norm_toLp_sq_le_dim_mul (q - q')
      calc v ≤ c * ‖(WithLp.toLp 2 (q - q') : Rd d)‖ ^ 2 := h1
        _ ≤ c * (d * ‖q - q'‖ ^ 2) := by gcongr
        _ = c' * ‖q - q'‖ ^ 2 := by rw [hc']; ring
    have hcoe : ((v.toNNReal : NNReal) : ℝ) = v := Real.coe_toNNReal _ hv0
    rw [hcoe, Real.rpow_natCast]
    calc v ^ (d + 1) * M ≤ (c' * ‖q - q'‖ ^ 2) ^ (d + 1) * M := by gcongr
      _ = c' ^ (d + 1) * M * ‖q - q'‖ ^ (2 * (d + 1)) := by ring
  have hpos : (d : ℝ) < ((2 * (d + 1) : ℕ) : ℝ) := by push_cast; linarith
  obtain ⟨Y, hYc, hYm, hYZ⟩ := LQGMetric.WhiteNoise.exists_meas_continuous_modification_N
    (P := P) (Z := Z) hZm (p := 2 * (d + 1)) (by omega) hpos hmom
  refine ⟨fun z ω => Y (WithLp.ofLp z) ω, fun ω => (hYc ω).comp (PiLp.continuous_ofLp 2 _),
    fun z => hYm _, fun z => ?_⟩
  have h := hYZ (WithLp.ofLp z)
  simp only [hZ, WithLp.toLp_ofLp] at h
  exact h

/-! ## Deterministic Fubini against `L²` vectors -/

/-- `⟪f, g⟫ = ∫ f g` in `L²(ℝ × ℝ^d)`. -/
theorem wns_inner_eq_integral (f g : WN d) :
    ⟪f, g⟫ = ∫ q, (f : ℝ × Rd d → ℝ) q * (g : ℝ × Rd d → ℝ) q := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae (ae_of_all _ fun q => ?_)
  dsimp only
  rw [real_inner_eq_re_inner, RCLike.inner_apply]
  simp only [conj_trivial, mul_comm, RCLike.mul_re, RCLike.re_to_real, RCLike.im_to_real,
    mul_zero, sub_zero]

/-- **Deterministic Fubini**: if `u x =ᵐ U x` with `(x, p) ↦ U x p` measurable and `‖u x‖`
locally bounded, and `V =ᵐ (p ↦ ∫ ψ(x) U x p dx)` for a continuous compactly supported `ψ`, then
`∫ ψ(x) ⟪u x, g⟫ dx = ⟪V, g⟫` for every `g ∈ L²`. -/
theorem wns_integral_mul_inner {u : Rd d → WN d} {U : Rd d → ℝ × Rd d → ℝ}
    (hUm : Measurable fun q : Rd d × (ℝ × Rd d) => U q.1 q.2)
    (hU : ∀ x, (u x : ℝ × Rd d → ℝ) =ᵐ[volume] U x)
    (hv : ∀ R : ℝ, ∃ C : ℝ, ∀ x : Rd d, ‖x‖ ≤ R → ‖u x‖ ^ 2 ≤ C)
    {ψ : Rd d → ℝ} (hψc : Continuous ψ) (hψs : HasCompactSupport ψ) {V : WN d}
    (hV : (V : ℝ × Rd d → ℝ) =ᵐ[volume] fun p => ∫ x, ψ x * U x p) (g : WN d) :
    ∫ x, ψ x * ⟪u x, g⟫ = ⟪V, g⟫ := by
  obtain ⟨Mψ, R, hψ⟩ := exists_isBddSupp_of_continuous hψc hψs
  obtain ⟨Ck, hCk⟩ := hv R
  set G : ℝ × Rd d → ℝ := (g : ℝ × Rd d → ℝ) with hG
  have hG2 : Integrable fun q => G q ^ 2 := (Lp.memLp g).integrable_sq
  have hUL : ∀ x, MemLp (U x) 2 volume := fun x => (Lp.memLp (u x)).ae_eq (hU x)
  have hUx : ∀ x, ⟪u x, g⟫ = ∫ q, U x q * G q := fun x => by
    rw [wns_inner_eq_integral]
    exact integral_congr_ae ((hU x).mono fun q hq => by dsimp only; rw [hq])
  have hU2 : ∀ x, ∫ q, U x q ^ 2 = ‖u x‖ ^ 2 := fun x => by
    rw [← real_inner_self_eq_norm_sq, wns_inner_eq_integral]
    refine integral_congr_ae ((hU x).mono fun q hq => ?_)
    dsimp only
    rw [hq, sq]
  set F : Rd d × (ℝ × Rd d) → ℝ := fun p => ψ p.1 * U p.1 p.2 * G p.2 with hF
  have hFm : AEStronglyMeasurable F (volume.prod volume) :=
    (((hψc.measurable.comp measurable_fst).mul hUm).aestronglyMeasurable).mul
      (Lp.aestronglyMeasurable g).comp_snd
  have hslice : ∀ x, Integrable fun q => U x q * G q := fun x =>
    (hUL x).integrable_mul (Lp.memLp g)
  have hbd : ∀ x, ∫ q, ‖U x q‖ * ‖G q‖ ≤ ((∫ q, U x q ^ 2) + ∫ q, G q ^ 2) / 2 := by
    intro x
    have h1 := (hUL x).integrable_sq
    calc ∫ q, ‖U x q‖ * ‖G q‖
        ≤ ∫ q, (U x q ^ 2 + G q ^ 2) / 2 := by
          refine integral_mono ((hslice x).norm.congr
            (Eventually.of_forall fun q => norm_mul _ _)) ((h1.add hG2).div_const _) fun q => ?_
          simp only [Real.norm_eq_abs]
          nlinarith [sq_nonneg (|U x q| - |G q|), sq_abs (U x q), sq_abs (G q)]
      _ = _ := by rw [integral_div, integral_add h1 hG2]
  have hFi : Integrable F (volume.prod volume) := by
    rw [integrable_prod_iff hFm]
    refine ⟨Eventually.of_forall fun x => ?_, ?_⟩
    · simp only [hF, mul_assoc]
      exact (hslice x).const_mul _
    · refine Integrable.mono' (hψ.integrable.norm.mul_const ((Ck + ∫ q, G q ^ 2) / 2))
        hFm.norm.integral_prod_right' (Eventually.of_forall fun x => ?_)
      simp only [hF, mul_assoc, norm_mul, integral_const_mul, norm_norm]
      rw [Real.norm_of_nonneg (integral_nonneg fun q => by positivity)]
      by_cases hx : R < ‖x‖
      · rw [hψ.eq_zero x hx]
        simp only [norm_zero, zero_mul, le_refl]
      · push Not at hx
        refine mul_le_mul_of_nonneg_left ((hbd x).trans ?_) (norm_nonneg _)
        rw [hU2 x]
        gcongr
        exact hCk x hx
  have e1 : ∀ x, ψ x * ⟪u x, g⟫ = ∫ q, F (x, q) := fun x => by
    rw [hUx, ← integral_const_mul]
    congr 1
    funext q
    simp only [hF]
    ring
  simp_rw [e1]
  rw [integral_integral_swap (f := fun x q => F (x, q)) hFi, wns_inner_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [hV] with q hq
  simp only [hF]
  rw [integral_mul_const, ← hq]

/-! ## Stochastic Fubini -/

/-- **Stochastic Fubini**: for a continuous measurable version `Y` of `x ↦ W(u x)` (`‖u x‖` locally
bounded) and a vector `V` with `∫ ψ(x) ⟪u x, g⟫ dx = ⟪V, g⟫` for all `g`, almost surely
`∫ ψ(x) Y(x) dx = W(V)`. -/
theorem wns_ae_integral_mul_eq (hW : HigherDimLFPP.IsWhiteNoise P W) {u : Rd d → WN d}
    {Y : Rd d → Ω → ℝ} (hYc : ∀ ω, Continuous fun x => Y x ω) (hYm : ∀ x, Measurable (Y x))
    (hYW : ∀ x, (fun ω => Y x ω) =ᵐ[P] W (u x))
    (hv : ∀ R : ℝ, ∃ C : ℝ, ∀ x : Rd d, ‖x‖ ≤ R → ‖u x‖ ^ 2 ≤ C)
    {ψ : Rd d → ℝ} (hψc : Continuous ψ) (hψs : HasCompactSupport ψ) {V : WN d}
    (hV : ∀ g : WN d, ∫ x, ψ x * ⟪u x, g⟫ = ⟪V, g⟫) :
    (fun ω => ∫ x, ψ x * Y x ω) =ᵐ[P] W V := by
  have := hW.isProbabilityMeasure
  set A : Ω → ℝ := fun ω => ∫ x, ψ x * Y x ω with hA
  set B : Ω → ℝ := W V with hB
  set T : ℝ := ⟪V, V⟫ with hT
  have hAL : MemLp A 2 P := memLp_integral_mul_Y hW hYc hYm hYW hv hψc hψs
  have hBL : MemLp B 2 P := hW.memLp _ 2 (by norm_num)
  have hAW : ∀ g : WN d, ∫ ω, A ω * W g ω ∂P = ⟪V, g⟫ := fun g => by
    rw [hA, integral_integral_mul_Y_mul hW hYc hYm hYW hv hψc hψs (hW.memLp _ 2 (by norm_num))]
    simp_rw [integral_Y_mul_W hW hYW]
    exact hV g
  have hAB : ∫ ω, A ω * B ω ∂P = T := hAW V
  have hAA : ∫ ω, A ω * A ω ∂P = T := by
    rw [hA, integral_integral_mul_Y_mul hW hYc hYm hYW hv hψc hψs hAL]
    have e : ∀ x : Rd d, ψ x * ∫ ω, Y x ω * A ω ∂P = ψ x * ⟪u x, V⟫ := fun x => by
      rw [integral_Y_mul hYW x]
      have e2 : ∫ ω, W (u x) ω * A ω ∂P = ∫ ω, A ω * W (u x) ω ∂P := by
        congr 1
        funext ω
        ring
      rw [e2, hAW, real_inner_comm]
    simp_rw [e]
    exact hV V
  have hBB : ∫ ω, B ω * B ω ∂P = T := wn_integral_mul hW V V
  have hiAA : Integrable (fun ω => A ω * A ω) P := hAL.integrable_mul hAL
  have hiAB : Integrable (fun ω => A ω * B ω) P := hAL.integrable_mul hBL
  have hiBB : Integrable (fun ω => B ω * B ω) P := hBL.integrable_mul hBL
  have hsq : ∫ ω, (A ω - B ω) ^ 2 ∂P = 0 := by
    have e : ∀ ω, (A ω - B ω) ^ 2 = A ω * A ω - 2 * (A ω * B ω) + B ω * B ω :=
      fun ω => by ring
    simp_rw [e]
    have i1 : Integrable (fun ω => A ω * A ω - 2 * (A ω * B ω)) P := hiAA.sub (hiAB.const_mul _)
    rw [integral_add i1 hiBB, integral_sub hiAA (hiAB.const_mul _), integral_const_mul, hAA, hAB,
      hBB]
    ring
  have hint : Integrable (fun ω => (A ω - B ω) ^ 2) P := (hAL.sub hBL).integrable_sq
  have h0 := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg (A ω - B ω)) hint).mp hsq
  filter_upwards [h0] with ω hω
  have h1 : (A ω - B ω) ^ 2 = 0 := hω
  have h2 : A ω - B ω = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1
  exact sub_eq_zero.1 h2

/-! ## Block tails for continuous versions -/

section Block

variable {u : Rd d → WN d} {Y : Rd d → Ω → ℝ}

theorem wns_ae_sub (hW : HigherDimLFPP.IsWhiteNoise P W)
    (hYW : ∀ z, (fun ω => Y z ω) =ᵐ[P] W (u z)) (z w : Rd d) :
    (fun ω => Y z ω - Y w ω) =ᵐ[P] W (u z - u w) := by
  filter_upwards [hYW z, hYW w, hW.sub_ae (u z) (u w)] with ω h1 h2 h3
  rw [h3, ← h1, ← h2]

theorem wns_isGaussianProcess_sub (hW : HigherDimLFPP.IsWhiteNoise P W)
    (hYW : ∀ z, (fun ω => Y z ω) =ᵐ[P] W (u z)) {T : Type*} (p : T → Rd d) (g : Rd d) :
    IsGaussianProcess (fun t ω => Y (p t) ω - Y g ω) P :=
  (hW.isGaussianProcess_comp fun t => u (p t) - u g).congr fun t =>
    (wns_ae_sub hW hYW (p t) g).symm

theorem wns_integral_sub_eq_zero (hW : HigherDimLFPP.IsWhiteNoise P W)
    (hYW : ∀ z, (fun ω => Y z ω) =ᵐ[P] W (u z)) (z w : Rd d) :
    ∫ ω, (Y z ω - Y w ω) ∂P = 0 := by
  rw [integral_congr_ae (wns_ae_sub hW hYW z w), hW.integral_eq_zero]

theorem wns_integral_sub_sq (hW : HigherDimLFPP.IsWhiteNoise P W)
    (hYW : ∀ z, (fun ω => Y z ω) =ᵐ[P] W (u z)) (z w : Rd d) :
    ∫ ω, (Y z ω - Y w ω) ^ 2 ∂P = ‖u z - u w‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← wn_integral_mul hW]
  refine integral_congr_ae ((wns_ae_sub hW hYW z w).mono fun ω h => ?_)
  simp only at h
  dsimp only
  rw [h, sq]

theorem wns_variance_sub (hW : HigherDimLFPP.IsWhiteNoise P W)
    (hYW : ∀ z, (fun ω => Y z ω) =ᵐ[P] W (u z)) (z w : Rd d) :
    Var[fun ω => Y z ω - Y w ω; P] = ‖u z - u w‖ ^ 2 := by
  rw [variance_congr (wns_ae_sub hW hYW z w), hW.variance_eq]

/-- **Block bound** for a continuous version `Y` of `x ↦ W(u x)` with
`‖u z − u w‖² ≤ L ‖z − w‖² / a²` (HigherDimLFPP's `Osc.block_tail`, whose proof uses only these
facts): for `r ≥ 0`, `t ≥ 0`,
`P(∃ z ∈ B̄(g, r a), blockConst d L r + t < |Y z − Y g|) ≤ 2 exp(−t² / (2 r² L))`. -/
theorem wns_block_tail (hW : HigherDimLFPP.IsWhiteNoise P W)
    (hYc : ∀ ω, Continuous fun z => Y z ω) (hYW : ∀ z, (fun ω => Y z ω) =ᵐ[P] W (u z))
    {a : ℝ} (ha : 0 < a) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ z w : Rd d, ‖u z - u w‖ ^ 2 ≤ L * ‖z - w‖ ^ 2 / a ^ 2)
    (g : Rd d) {r : ℝ} (hr : 0 ≤ r) {t : ℝ} (ht : 0 ≤ t) :
    P {ω | ∃ z ∈ closedBall g (r * a), HigherDimLFPP.Osc.blockConst d L r + t < |Y z ω - Y g ω|}
      ≤ ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * (r ^ 2 * L)))) := by
  have := hW.isProbabilityMeasure
  set K : Set (Rd d) := closedBall g (r * a) with hK
  have : CompactSpace K := isCompact_iff_compactSpace.1 (isCompact_closedBall g _)
  have : Nonempty K := ⟨⟨g, mem_closedBall_self (by positivity)⟩⟩
  set X : K → Ω → ℝ := fun z ω => Y z ω - Y g ω with hXdef
  have hX : IsGaussianProcess X P := wns_isGaussianProcess_sub hW hYW (fun z : K => (z : Rd d)) g
  have h0 : ∀ z, ∫ ω, X z ω ∂P = 0 := fun z => wns_integral_sub_eq_zero hW hYW z g
  have hc : ∀ ω, Continuous fun z => X z ω := fun ω =>
    ((hYc ω).comp continuous_subtype_val).sub continuous_const
  have hnorm : ∀ z : K, ‖(z : Rd d) - g‖ ≤ r * a := fun z => by
    have h : (z : Rd d) ∈ closedBall g (r * a) := z.2
    rwa [mem_closedBall, dist_eq_norm] at h
  have hchain : ∀ X' : K → Ω → ℝ, IsGaussianProcess X' P → (∀ z, ∫ ω, X' z ω ∂P = 0) →
      (∀ z w : K, ∫ ω, (X' z ω - X' w ω) ^ 2 ∂P = ‖u z - u w‖ ^ 2) →
      ∀ (n : ℕ) (s : Fin (n + 1) → K), ∫ ω, ⨆ i, X' (s i) ω ∂P ≤
        HigherDimLFPP.Osc.blockConst d L r := by
    intro X' hX' hX'0 hX'inc n s
    have hdiam : ∀ z w : K, ‖(z : Rd d) - w‖ ≤ 2 * r * a := fun z w => by
      calc ‖(z : Rd d) - w‖ = ‖((z : Rd d) - g) - ((w : Rd d) - g)‖ := by
            rw [sub_sub_sub_cancel_right]
        _ ≤ ‖(z : Rd d) - g‖ + ‖(w : Rd d) - g‖ := norm_sub_le _ _
        _ ≤ 2 * r * a := by linarith [hnorm z, hnorm w]
    have h := LQGMetric.SupTail.integral_iSup_family_le hX' hX'0 (n := n + 1) (d := d)
      (Nat.succ_pos n) s (fun z => WithLp.ofLp (z : Rd d))
      (L := √(2 * r * L * √(d : ℝ) / a)) (a := 2 * r * a) (Real.sqrt_nonneg _)
      (fun i j => (HigherDimLFPP.Osc.norm_ofLp_sub_le _ _).trans (hdiam _ _)) (fun i j => ?_)
    · rwa [HigherDimLFPP.Osc.chain_identity hL0 hr ha] at h
    · rw [hX'inc]
      exact (hL _ _).trans (HigherDimLFPP.Osc.incr_le_chain hL0 hr ha (hdiam _ _))
  have hXinc : ∀ z w : K, ∫ ω, (X z ω - X w ω) ^ 2 ∂P = ‖u z - u w‖ ^ 2 := fun z w => by
    simp only [hXdef, sub_sub_sub_cancel_right]
    exact wns_integral_sub_sq hW hYW z w
  have hnX : IsGaussianProcess (fun z ω => -X z ω) P := LQGMetric.SupTail.isGaussianProcess_neg hX
  have hnX0 : ∀ z, ∫ ω, -X z ω ∂P = 0 := fun z => by rw [integral_neg, h0, neg_zero]
  have hnXinc : ∀ z w : K, ∫ ω, (-X z ω - -X w ω) ^ 2 ∂P = ‖u z - u w‖ ^ 2 := fun z w => by
    have e : ∀ ω, (-X z ω - -X w ω) ^ 2 = (X z ω - X w ω) ^ 2 := fun ω => by ring
    simp_rw [e]
    exact hXinc z w
  obtain ⟨hint, hM⟩ := LQGMetric.SupTail.integrable_iSup_of_continuous hX hc
    (hchain X hX h0 hXinc)
  obtain ⟨hint', hM'⟩ := LQGMetric.SupTail.integrable_iSup_of_continuous hnX
    (fun ω => (hc ω).neg) (hchain _ hnX hnX0 hnXinc)
  have hvar : ∀ z : K, Var[X z; P] ≤ (r * √L) ^ 2 := fun z => by
    rw [show X z = fun ω => Y z ω - Y g ω from rfl, wns_variance_sub hW hYW]
    refine (hL z g).trans ?_
    rw [mul_pow, Real.sq_sqrt hL0]
    have h1 : ‖(z : Rd d) - g‖ ^ 2 ≤ (r * a) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hnorm z) 2
    calc L * ‖(z : Rd d) - g‖ ^ 2 / a ^ 2 ≤ L * (r * a) ^ 2 / a ^ 2 := by gcongr
      _ = r ^ 2 * L := by field_simp
  have htail := LQGMetric.SupTail.tail_iSup_abs_le hX h0 hc hint hint' hM hM' hvar ht
  have hsub : {ω | ∃ z ∈ K, HigherDimLFPP.Osc.blockConst d L r + t < |Y z ω - Y g ω|} ⊆
      {ω | HigherDimLFPP.Osc.blockConst d L r + t ≤ ⨆ z, |X z ω|} := by
    rintro ω ⟨z, hz, hlt⟩
    have hb : BddAbove (range fun z : K => |X z ω|) :=
      (isCompact_range (continuous_abs.comp (hc ω))).bddAbove
    exact hlt.le.trans (le_ciSup (f := fun z : K => |X z ω|) hb ⟨z, hz⟩)
  calc P {ω | ∃ z ∈ K, HigherDimLFPP.Osc.blockConst d L r + t < |Y z ω - Y g ω|}
      ≤ P {ω | HigherDimLFPP.Osc.blockConst d L r + t ≤ ⨆ z, |X z ω|} := measure_mono hsub
    _ = ENNReal.ofReal (P.real {ω | HigherDimLFPP.Osc.blockConst d L r + t ≤ ⨆ z, |X z ω|}) :=
        (ofReal_measureReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal (2 * Real.exp (-t ^ 2 / (2 * (r ^ 2 * L)))) := by
        refine ENNReal.ofReal_le_ofReal (htail.trans_eq ?_)
        rw [mul_pow, Real.sq_sqrt hL0]

end Block

end HigherDimLQGMetric
