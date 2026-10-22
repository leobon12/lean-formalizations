import HigherDimLQGMetric.Sphere.Cov
import LQGMetric.Field.WhiteNoiseC1Proc

/-!
# A.s. existence of `h_r(z)` for all `(r, z)` at once, and joint continuity

Packet F3 (Phase A, block A1), target 4. MA0 Details (a) D-F3 ("`h_r(z)` has a version continuous in
`(r, z) ∈ (0,∞) × ℝ^d`"; route: Kolmogorov in `(z, log r)`); MA5 §3.3 note 4.

For an LGF (or an LGF plus a continuous function) `h`, `d ≥ 2`: almost surely the limit defining
`sphereAvg (h ω) r z` exists for **all** `r > 0` and `z` simultaneously, and
`(r, z) ↦ sphereAvg (h ω) r z` is continuous on `(0, ∞) × ℝ^d`
(`IsWholeSpaceLGF.ae_continuousOn_sphereAvg`, `IsLGFPlusCont.ae_continuousOn_sphereAvg`);
`(ω, r, z) ↦ sphereAvg (h ω) r z` is jointly measurable (`measurable_sphereAvg_uncurry`).

Proof (own route, extending MA0's "Kolmogorov in `(z, log r)`" by the mollification scale as an
extra parameter). Parametrize `q ∈ ℝ^{d+2}` by `ε = clamp_{[0,1]}(q₀)`, `r = e^{q₁}`,
`z = (q₂, …, q_{d+1})` and put `Z(q) = sphProc h ε r z` (`= h_r(z)` for `ε = 0`, the mollified
average `⟨h, σ_{r,z} * ψ_ε⟩` for `ε > 0`). The increments are centred Gaussian with
`Var(Z(q) - Z(q')) ≤ C (‖z - z'‖ + |r - r'| + |ε - ε'|) / min(r, r') ≤ C_R ‖q - q'‖` on
`[-R, R]^{d+2}` (transport bound, `exists_integral_sq_sphIncProc_le`), so
`E|Z(q) - Z(q')|^{2(d+3)} ≤ K_R ‖q - q'‖^{d+3}` and (QZ's Kolmogorov–Čentsov, `d + 3 > d + 2`) `Z`
has a modification `Y` continuous for every `ω`. A.s. `Y = Z` on the countable set
`{ε = 2^{-n}} × ℚ^{d+1}`; on each slice `ε = 2^{-n}` both are continuous in `(log r, z)`
(`continuous_sphereAvgSeq`), so they agree on the whole slice. Hence a.s., for all `(r, z)`:
`sphereAvgSeq (h ω) r z n = Y(2^{-n}, log r, z) → Y(0, log r, z)` by continuity of `Y`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ}

/-! ### Continuity of the mollified sphere averages in `(r, z)` -/

/-- `∫ g(r, z, u) dσ(u)` is continuous in `(r, z)` for jointly continuous `g`. -/
theorem continuous_integral_unitSphereProb {X : Type*} [TopologicalSpace X]
    [FirstCountableTopology X] [LocallyCompactSpace X] {g : X → Rd d → ℝ}
    (hg : Continuous (Function.uncurry g)) :
    Continuous fun x => ∫ u, g x u ∂(unitSphereProb d) := by
  have hσ := restrict_sphere_unitSphereProb d
  have e : (fun x => ∫ u, g x u ∂(unitSphereProb d)) =
      fun x => ∫ u in sphere (0 : Rd d) 1, g x u ∂(unitSphereProb d) := by
    funext x; rw [hσ]
  rw [e]
  exact continuous_parametric_integral_of_continuous hg (isCompact_sphere 0 1)

/-- **`(r, z) ↦ sphereAvgSeq g r z n` is continuous** for every distribution `g`. -/
theorem continuous_sphereAvgSeq (g : DistRd d) (n : ℕ) :
    Continuous fun p : ℝ × Rd d => sphereAvgSeq g p.1 p.2 n :=
  continuous_integral_unitSphereProb (g := fun (p : ℝ × Rd d) u => g (bumpTest n (p.2 + p.1 • u)))
    ((continuous_apply_bumpTest g n).comp (by fun_prop))

/-- The spherical mean of a continuous function is continuous in `(r, z)`. -/
theorem continuous_sphereMean (f : C(Rd d, ℝ)) :
    Continuous fun p : ℝ × Rd d => ∫ u, f (p.2 + p.1 • u) ∂(unitSphereProb d) :=
  continuous_integral_unitSphereProb (g := fun (p : ℝ × Rd d) u => f (p.2 + p.1 • u))
    (f.continuous.comp (by fun_prop))

/-! ### The parametrization `q ↦ (ε, r, z)` -/

/-- `q₀` clamped to `[0, 1]`. -/
def clampT (s : ℝ) : ℝ := max (min s 1) 0

theorem clampT_nonneg (s : ℝ) : 0 ≤ clampT s := le_max_right _ _

theorem clampT_of_mem {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) : clampT s = s := by
  rw [clampT, min_eq_left h1, max_eq_left h0]

theorem abs_clampT_sub_le (a b : ℝ) : |clampT a - clampT b| ≤ |a - b| := by
  refine (abs_max_sub_max_le_abs _ _ 0).trans ((abs_min_sub_min_le_max a 1 b 1).trans ?_)
  rw [sub_self, abs_zero, max_eq_left (abs_nonneg _)]

/-- The `ℝ^d` coordinates `(q₂, …, q_{d+1})`. -/
def kParZ (q : Fin (d + 2) → ℝ) : Rd d := WithLp.toLp 2 fun i : Fin d => q i.succ.succ

/-- The point `(clamp q₀, e^{q₁}, (q₂, …))` of the sphere-average process. -/
def kPt (q : Fin (d + 2) → ℝ) : SphPt d :=
  ⟨clampT (q 0), Real.exp (q 1), kParZ q, clampT_nonneg _, Real.exp_pos _⟩

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistRd d}

/-- The Kolmogorov process `Z(q) = sphProc h (clamp q₀) (e^{q₁}) (q₂, …)`. -/
def kolmProc (h : Ω → DistRd d) (q : Fin (d + 2) → ℝ) (ω : Ω) : ℝ :=
  sphProc (h ω) (kPt q).ε (kPt q).r (kPt q).z

/-- `‖v‖₂ ≤ d ‖v‖_∞` on `ℝ^d`. -/
theorem norm_toLp_le (v : Fin d → ℝ) : ‖WithLp.toLp 2 v‖ ≤ d * ‖v‖ := by
  have h1 := HigherDimLFPP.norm_toLp_sq_le_dim_mul v
  have hd2 : (d : ℝ) ≤ (d : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos d with h0 | hpos
    · simp [h0]
    · have : (1 : ℝ) ≤ d := by exact_mod_cast hpos
      nlinarith
  have h2 : ‖WithLp.toLp 2 v‖ ^ 2 ≤ ((d : ℝ) * ‖v‖) ^ 2 := by
    calc ‖WithLp.toLp 2 v‖ ^ 2 ≤ d * ‖v‖ ^ 2 := h1
      _ ≤ (d : ℝ) ^ 2 * ‖v‖ ^ 2 := mul_le_mul_of_nonneg_right hd2 (sq_nonneg _)
      _ = ((d : ℝ) * ‖v‖) ^ 2 := by rw [mul_pow]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h2

theorem norm_kParZ_sub_le (q q' : Fin (d + 2) → ℝ) : ‖kParZ q - kParZ q'‖ ≤ d * ‖q - q'‖ := by
  set v : Fin d → ℝ := fun i => (q - q') i.succ.succ with hv
  have e : kParZ q - kParZ q' = WithLp.toLp 2 v := by
    rw [kParZ, kParZ, ← WithLp.toLp_sub]; rfl
  have hv' : ‖v‖ ≤ ‖q - q'‖ :=
    (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => norm_le_pi_norm (q - q') _
  rw [e]
  exact (norm_toLp_le v).trans (mul_le_mul_of_nonneg_left hv' (Nat.cast_nonneg d))

theorem abs_apply_sub_le (q q' : Fin (d + 2) → ℝ) (i : Fin (d + 2)) : |q i - q' i| ≤ ‖q - q'‖ := by
  have := norm_le_pi_norm (q - q') i
  rwa [Pi.sub_apply, Real.norm_eq_abs] at this

/-- On the box `[-R, R]^{d+2}`: `dist(kPt q, kPt q') / min(r, r') ≤ e^R (d + e^R + 1) ‖q - q'‖`. -/
theorem kPt_dist_div_le {R : ℕ} {q q' : Fin (d + 2) → ℝ} (hq : q ∈ QuantumZipper.KolmD.boxD R)
    (hq' : q' ∈ QuantumZipper.KolmD.boxD R) :
    (kPt q).dist (kPt q') / min (kPt q).r (kPt q').r ≤
      Real.exp R * (d + Real.exp R + 1) * ‖q - q'‖ := by
  have hb : ∀ i, |q i| ≤ R := hq
  have hb' : ∀ i, |q' i| ≤ R := hq'
  have h1 : |Real.exp (q 1) - Real.exp (q' 1)| ≤ Real.exp R * ‖q - q'‖ :=
    (QuantumZipper.RegSample.abs_exp_sub_exp_le (abs_le.1 (hb 1)).2 (abs_le.1 (hb' 1)).2).trans
      (mul_le_mul_of_nonneg_left (abs_apply_sub_le q q' 1) (Real.exp_pos _).le)
  have h2 : |clampT (q 0) - clampT (q' 0)| ≤ ‖q - q'‖ :=
    (abs_clampT_sub_le _ _).trans (abs_apply_sub_le q q' 0)
  have h3 := norm_kParZ_sub_le q q'
  have hmin : Real.exp (-(R : ℝ)) ≤ min (Real.exp (q 1)) (Real.exp (q' 1)) :=
    le_min (Real.exp_le_exp.2 (by linarith [(abs_le.1 (hb 1)).1]))
      (Real.exp_le_exp.2 (by linarith [(abs_le.1 (hb' 1)).1]))
  have hdist : (kPt q).dist (kPt q') ≤ (d + Real.exp R + 1) * ‖q - q'‖ := by
    simp only [SphPt.dist, kPt]
    nlinarith
  have hpos : 0 < min (Real.exp (q 1)) (Real.exp (q' 1)) := lt_min (Real.exp_pos _) (Real.exp_pos _)
  calc (kPt q).dist (kPt q') / min (kPt q).r (kPt q').r
      ≤ (d + Real.exp R + 1) * ‖q - q'‖ / Real.exp (-(R : ℝ)) := by
        simp only [kPt]
        exact div_le_div₀ (by positivity) hdist (Real.exp_pos _) hmin
    _ = Real.exp R * (d + Real.exp R + 1) * ‖q - q'‖ := by
        rw [Real.exp_neg, div_inv_eq_mul]; ring1

/-- **The Kolmogorov moment bound** (`d ≥ 2`): on every box `[-R, R]^{d+2}`,
`E|Z(q) - Z(q')|^{2(d+3)} ≤ K_R ‖q - q'‖^{d+3}`. -/
theorem IsWholeSpaceLGF.momentBound_kolmProc (hd : 2 ≤ d) (hh : IsWholeSpaceLGF h P) (R : ℕ) :
    ∃ K, 0 ≤ K ∧ QuantumZipper.KolmG.MomentBoundG (kolmProc h) P (2 * (d + 3))
      ((d + 3 : ℕ) : ℝ) K R := by
  obtain ⟨C, hC0, hC⟩ := exists_integral_sq_sphIncProc_le hd
  set A : ℝ := C * (Real.exp R * (d + Real.exp R + 1)) with hA
  have hA0 : 0 ≤ A := by positivity
  set M : ℝ := QuantumZipper.gaussianAbsMoment (2 * (d + 3)) with hM
  have hM0 : 0 ≤ M := QuantumZipper.gaussianAbsMoment_nonneg _
  refine ⟨A ^ (d + 3) * M, by positivity, fun q hq q' hq' => ?_⟩
  obtain ⟨hG, h0, hvar, hle⟩ := hC hh (kPt q) (kPt q')
  set U := sphIncProc h (.inl (kPt q, kPt q')) with hU
  have hUm : Measurable U := measurable_sphIncProc hh.measurable _
  have hlaw : P.map U = gaussianReal 0 (Var[U; P]).toNNReal := by
    rw [hG.map_eq_gaussianReal, h0]
  have hE := QuantumZipper.KolmG.lintegral_pow_two_mul_of_map_eq hUm (d + 3) hlaw
  have hV : Var[U; P] ≤ A * ‖q - q'‖ := by
    rw [variance_eq_integral hG.aemeasurable, h0]
    simp only [sub_zero]
    rw [hvar]
    calc _ ≤ C * (kPt q).dist (kPt q') / min (kPt q).r (kPt q').r := hle
      _ = C * ((kPt q).dist (kPt q') / min (kPt q).r (kPt q').r) := by rw [mul_div_assoc]
      _ ≤ C * (Real.exp R * (d + Real.exp R + 1) * ‖q - q'‖) :=
          mul_le_mul_of_nonneg_left (kPt_dist_div_le hq hq') hC0
      _ = A * ‖q - q'‖ := by rw [hA]; ring1
  have hV0 : 0 ≤ Var[U; P] := variance_nonneg _ _
  have heq : (fun ω => ENNReal.ofReal (|kolmProc h q ω - kolmProc h q' ω| ^ (2 * (d + 3)))) =
      fun ω => ENNReal.ofReal (|U ω| ^ (2 * (d + 3))) := rfl
  show ∫⁻ ω, ENNReal.ofReal (|kolmProc h q ω - kolmProc h q' ω| ^ (2 * (d + 3))) ∂P ≤ _
  rw [heq, hE, Real.coe_toNNReal _ hV0, Real.rpow_natCast]
  refine ENNReal.ofReal_le_ofReal ?_
  calc Var[U; P] ^ (d + 3) * M ≤ (A * ‖q - q'‖) ^ (d + 3) * M :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hV0 hV _) hM0
    _ = A ^ (d + 3) * M * ‖q - q'‖ ^ (d + 3) := by rw [mul_pow]; ring1

/-! ### The continuous modification and the a.s. joint continuity -/

/-- `Fin.cons` with the non-dependent type `ℝ^{d+2}`. -/
def consPar (ε : ℝ) (v : Fin (d + 1) → ℝ) : Fin (d + 2) → ℝ := Fin.cons ε v

/-- The parameter of `(ε, log r, z)`. -/
def qPar (ε a : ℝ) (z : Rd d) : Fin (d + 2) → ℝ := consPar ε (Fin.cons a (WithLp.ofLp z))

theorem continuous_consPar : Continuous fun p : ℝ × (Fin (d + 1) → ℝ) => consPar p.1 p.2 := by
  refine continuous_pi fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · exact continuous_fst
  · exact (continuous_apply j).comp continuous_snd

theorem continuous_qPar : Continuous fun p : ℝ × ℝ × Rd d => qPar (d := d) p.1 p.2.1 p.2.2 := by
  refine continuous_pi fun i => ?_
  refine Fin.cases ?_ (fun j => ?_) i
  · exact continuous_fst
  · refine Fin.cases ?_ (fun k => ?_) j
    · exact continuous_snd.fst
    · exact (continuous_apply k).comp ((PiLp.continuous_ofLp 2 _).comp continuous_snd.snd)

theorem consPar_eq_qPar (ε : ℝ) (v : Fin (d + 1) → ℝ) :
    consPar ε v = qPar ε (v 0) (WithLp.toLp 2 fun i => v i.succ) := by
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  refine Fin.cases rfl (fun k => rfl) j

theorem qPar_zero (ε a : ℝ) (z : Rd d) : qPar ε a z 0 = ε := rfl

theorem qPar_one (ε a : ℝ) (z : Rd d) : qPar ε a z 1 = a := rfl

theorem kParZ_qPar (ε a : ℝ) (z : Rd d) : kParZ (qPar ε a z) = z := rfl

omit [MeasurableSpace Ω] in
theorem kolmProc_qPar_two_pow_inv (n : ℕ) (a : ℝ) (z : Rd d) (ω : Ω) :
    kolmProc h (qPar ((2 : ℝ) ^ n)⁻¹ a z) ω = sphereAvgSeq (h ω) (Real.exp a) z n := by
  have h0 : (0 : ℝ) ≤ ((2 : ℝ) ^ n)⁻¹ := by positivity
  have h1 : ((2 : ℝ) ^ n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  rw [kolmProc, sphereAvgSeq_eq_apply_sphMol]
  simp only [kPt, qPar_zero, qPar_one, kParZ_qPar, clampT_of_mem h0 h1]
  exact sphProc_of_ne _ (by positivity) _ _

/-- **Joint statement** (`d ≥ 2`, LGF): there is a process `Y`, continuous in `q` for every `ω`,
such that almost surely, for all `r > 0` and `z`, the mollified sphere averages converge to
`Y(0, log r, z)`. -/
theorem IsWholeSpaceLGF.exists_ae_tendsto_sphereAvgSeq (hd : 2 ≤ d) (hh : IsWholeSpaceLGF h P) :
    ∃ Y : (Fin (d + 2) → ℝ) → Ω → ℝ, (∀ ω, Continuous fun q => Y q ω) ∧
      (∀ q, Measurable (Y q)) ∧
      ∀ᵐ ω ∂P, ∀ r : ℝ, 0 < r → ∀ z : Rd d,
        Tendsto (sphereAvgSeq (h ω) r z) atTop (𝓝 (Y (qPar 0 (Real.log r) z) ω)) := by
  have hZm : ∀ q, Measurable (kolmProc h q) := fun q =>
    (measurable_sphProc _ _ _).comp hh.measurable
  have hpos : ((d + 2 : ℕ) : ℝ) < ((d + 3 : ℕ) : ℝ) := by push_cast; linarith
  obtain ⟨Y, hYc, hYm, hYZ⟩ := LQGMetric.WhiteNoise.exists_meas_continuous_modification_N
    (P := P) (Z := kolmProc h) hZm (p := 2 * (d + 3)) (by omega) hpos
    (hh.momentBound_kolmProc hd)
  refine ⟨Y, hYc, hYm, ?_⟩
  -- a.s. agreement on the countable set `{2^{-n}} × ℚ^{d+1}`
  have hcount : ∀ᵐ ω ∂P, ∀ n : ℕ, ∀ s : Fin (d + 1) → ℚ,
      Y (consPar ((2 : ℝ) ^ n)⁻¹ fun i => (s i : ℝ)) ω =
        kolmProc h (consPar ((2 : ℝ) ^ n)⁻¹ fun i => (s i : ℝ)) ω := by
    rw [ae_all_iff]; intro n
    rw [ae_all_iff]; intro s
    exact hYZ _
  filter_upwards [hcount] with ω hω r hr z
  -- agreement on the slices `ε = 2^{-n}`
  have hslice : ∀ n : ℕ, ∀ v : Fin (d + 1) → ℝ,
      Y (consPar ((2 : ℝ) ^ n)⁻¹ v) ω = kolmProc h (consPar ((2 : ℝ) ^ n)⁻¹ v) ω := by
    intro n
    have hdense : Dense (Set.pi univ fun _ : Fin (d + 1) => range ((↑) : ℚ → ℝ)) :=
      dense_pi univ fun i _ => Rat.denseRange_cast
    have hc1 : Continuous fun v : Fin (d + 1) → ℝ => Y (consPar ((2 : ℝ) ^ n)⁻¹ v) ω :=
      (hYc ω).comp (continuous_consPar.comp (continuous_const.prodMk continuous_id))
    have hc : Continuous fun v : Fin (d + 1) → ℝ =>
        ((Real.exp (v 0), WithLp.toLp 2 fun i => v i.succ) : ℝ × Rd d) :=
      (Real.continuous_exp.comp (continuous_apply 0)).prodMk
        ((PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => continuous_apply _))
    have e : (fun v : Fin (d + 1) → ℝ => kolmProc h (consPar ((2 : ℝ) ^ n)⁻¹ v) ω) =
        (fun p : ℝ × Rd d => sphereAvgSeq (h ω) p.1 p.2 n) ∘
          fun v : Fin (d + 1) → ℝ => ((Real.exp (v 0), WithLp.toLp 2 fun i => v i.succ) :
            ℝ × Rd d) := by
      funext v
      rw [Function.comp_apply, consPar_eq_qPar, kolmProc_qPar_two_pow_inv]
    have hc2 : Continuous fun v : Fin (d + 1) → ℝ =>
        kolmProc h (consPar ((2 : ℝ) ^ n)⁻¹ v) ω := by
      rw [e]
      exact (continuous_sphereAvgSeq (h ω) n).comp hc
    have hext := Continuous.ext_on hdense hc1 hc2 (fun v hv => by
      have hv' : ∀ i, ∃ q : ℚ, (q : ℝ) = v i := fun i => hv i (mem_univ i)
      choose s hs using hv'
      have ev : v = fun i => (s i : ℝ) := funext fun i => (hs i).symm
      subst ev
      exact hω n s)
    exact fun v => congrFun hext v
  -- the limit along `ε = 2^{-n} → 0`
  have hseq : ∀ n : ℕ, sphereAvgSeq (h ω) r z n =
      Y (qPar ((2 : ℝ) ^ n)⁻¹ (Real.log r) z) ω := by
    intro n
    have h1 : Y (qPar ((2 : ℝ) ^ n)⁻¹ (Real.log r) z) ω =
        kolmProc h (qPar ((2 : ℝ) ^ n)⁻¹ (Real.log r) z) ω := hslice n _
    rw [h1, kolmProc_qPar_two_pow_inv, Real.exp_log hr]
  have htend : Tendsto (fun n : ℕ => qPar (d := d) ((2 : ℝ) ^ n)⁻¹ (Real.log r) z) atTop
      (𝓝 (qPar 0 (Real.log r) z)) := by
    have h1 : Tendsto (fun n : ℕ => ((2 : ℝ) ^ n)⁻¹) atTop (𝓝 0) := by
      simp_rw [← inv_pow]
      exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have h2 : Continuous fun ε : ℝ => qPar (d := d) ε (Real.log r) z :=
      (continuous_qPar (d := d)).comp
        (continuous_id.prodMk (continuous_const (y := ((Real.log r, z) : ℝ × Rd d))))
    exact (h2.tendsto 0).comp h1
  refine (((hYc ω).tendsto _).comp htend).congr fun n => ?_
  exact (hseq n).symm

/-- **A.s. existence for all `(r, z)` and joint continuity** (`d ≥ 2`, LGF). -/
theorem IsWholeSpaceLGF.ae_continuousOn_sphereAvg (hd : 2 ≤ d) (hh : IsWholeSpaceLGF h P) :
    ∀ᵐ ω ∂P, (∀ r : ℝ, 0 < r → ∀ z : Rd d,
        Tendsto (sphereAvgSeq (h ω) r z) atTop (𝓝 (sphereAvg (h ω) r z))) ∧
      ContinuousOn (fun p : ℝ × Rd d => sphereAvg (h ω) p.1 p.2) (Ioi 0 ×ˢ univ) := by
  obtain ⟨Y, hYc, -, hY⟩ := hh.exists_ae_tendsto_sphereAvgSeq hd
  filter_upwards [hY] with ω hω
  refine ⟨fun r hr z => tendsto_sphereAvgSeq_sphereAvg ⟨_, hω r hr z⟩, ?_⟩
  have heq : EqOn (fun p : ℝ × Rd d => sphereAvg (h ω) p.1 p.2)
      (fun p => Y (qPar 0 (Real.log p.1) p.2) ω) (Ioi 0 ×ˢ univ) := fun p hp =>
    sphereAvg_eq_of_tendsto (hω p.1 hp.1 p.2)
  refine ContinuousOn.congr ?_ heq
  have hlog : ContinuousOn (fun p : ℝ × Rd d => ((0 : ℝ), Real.log p.1, p.2)) (Ioi 0 ×ˢ univ) :=
    continuousOn_const.prodMk ((Real.continuousOn_log.comp continuous_fst.continuousOn
      fun p hp => ne_of_gt hp.1).prodMk continuous_snd.continuousOn)
  exact ((hYc ω).comp continuous_qPar).comp_continuousOn hlog

/-- **The same for an LGF plus a continuous function** (`d ≥ 2`): almost surely the limits defining
`sphereAvg (h ω) r z` exist for all `r > 0`, `z` at once, and `(r, z) ↦ sphereAvg (h ω) r z` is
continuous on `(0, ∞) × ℝ^d`. -/
theorem IsLGFPlusCont.ae_continuousOn_sphereAvg (hd : 2 ≤ d) (hh : IsLGFPlusCont h P) :
    ∀ᵐ ω ∂P, (∀ r : ℝ, 0 < r → ∀ z : Rd d,
        Tendsto (sphereAvgSeq (h ω) r z) atTop (𝓝 (sphereAvg (h ω) r z))) ∧
      ContinuousOn (fun p : ℝ × Rd d => sphereAvg (h ω) p.1 p.2) (Ioi 0 ×ˢ univ) := by
  obtain ⟨-, f, -, hlgf⟩ := hh
  filter_upwards [hlgf.ae_continuousOn_sphereAvg hd] with ω ⟨hconv, hcont⟩
  set g := h ω - ofCont (f ω) with hg
  have e : h ω = HigherDimLQGMetric.addFun g (f ω) := by
    rw [addFun_def, hg, sub_add_cancel]
  have hlim : ∀ r : ℝ, 0 < r → ∀ z : Rd d, Tendsto (sphereAvgSeq (h ω) r z) atTop
      (𝓝 (sphereAvg g r z + ∫ u, f ω (z + r • u) ∂(unitSphereProb d))) := by
    intro r hr z
    have := (tendsto_sphereAvgSeq_addFun_iff g (f ω) r z _).2 (hconv r hr z)
    rwa [← e] at this
  refine ⟨fun r hr z => tendsto_sphereAvgSeq_sphereAvg ⟨_, hlim r hr z⟩, ?_⟩
  have heq : EqOn (fun p : ℝ × Rd d => sphereAvg (h ω) p.1 p.2)
      (fun p => sphereAvg g p.1 p.2 +
        ∫ u, f ω (p.2 + p.1 • u) ∂(unitSphereProb d)) (Ioi 0 ×ˢ univ) := fun p hp =>
    sphereAvg_eq_of_tendsto (hlim p.1 hp.1 p.2)
  exact (hcont.add (continuous_sphereMean (f ω)).continuousOn).congr heq

/-- **Joint measurability** of `(ω, r, z) ↦ sphereAvg (h ω) r z` for a measurable random
distribution. -/
theorem measurable_sphereAvg_uncurry (hm : Measurable h) :
    Measurable fun p : Ω × ℝ × Rd d => sphereAvg (h p.1) p.2.1 p.2.2 := by
  have h1 : Measurable fun p : Ω × ℝ × Rd d => ((h p.1, p.2.1, p.2.2) : DistRd d × ℝ × Rd d) :=
    (hm.comp measurable_fst).prodMk measurable_snd
  exact Measurable.comp (g := fun p : DistRd d × ℝ × Rd d => sphereAvg p.1 p.2.1 p.2.2)
    (f := fun p : Ω × ℝ × Rd d => ((h p.1, p.2.1, p.2.2) : DistRd d × ℝ × Rd d))
    measurable_sphereAvg h1

end HigherDimLQGMetric
