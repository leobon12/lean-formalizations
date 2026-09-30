import QuantumZipper.Proofs.GFF.ZeroRegBoundary

/-!
# RG-2 without admissibility of the limit measure

Blueprint `THM11_BLUEPRINT.md` §7, node RG-2, variant needed at `κ = 4`. Let `X` satisfy
`IsZeroBoundaryGFFH X P` and let `μ` be a finite measure with compact support in `Hbar`, a
bounded Green potential, a Frostman bound and log-log strip decay (`TameBdry μ`), but **not
necessarily** admissible (its singular log potential may be unbounded near `ℝ`). Then:

* `ae_tendsto_evalReg_NA` (1): almost surely `X(S_k μ) = ∫ avgReg X k dμ` converges, to
  `evalReg X μ`.
* `integral_cexp_evalReg_NA` (2): for finitely many such `μ_j`,
  `E exp(i Σ t_j evalReg X μ_j) = exp(−½ Σ t_j t_l kernelCov greenH μ_j μ_l)`.

Proof. `X μ` itself carries no information (the GFF hypotheses only constrain admissible
measures), so we compare with the admissible cut-offs `μ_m = μ|{Im ≥ 1/(m+1)}` (admissible by the
Frostman bound, `isAdmissibleH_cutM`). With `S_k` the folded-circle smoothing at radius `2^{-k}`:

* `Var(X(S_k μ) − X(S_k μ_m)) = 𝓔_G(S_k(μ − μ_m)) ≤ (U + 8μ(ℂ)) μ{Im < 1/(m+1)}`, since `G ≥ 0`
  and smoothed potentials are bounded (`kernelCov2_add_le`);
* `Var(X(S_k μ_m) − X(μ_m)) ≤ v_k` by RG-1 (`zrb_energy_le`) applied to `μ_m`;
* `Var(X(μ_{m'}) − X(μ_m)) ≤ U μ{Im < 1/(m+1)}` for `m ≤ m'`.

Choosing `m(k)` with `μ{Im < 1/(m(k)+1)} ≤ 8^{-k}`, `X(S_k μ) − X(μ_{m(k)}) → 0` a.s. by the
Gaussian Borel–Cantelli argument of RG-2, and `X(μ_{m(k)})` is a.s. Cauchy by Chebyshev. For (2),
`(X(μ_{j,m(k)}))_j` is jointly Gaussian with covariance `kernelCov greenH μ_{j,m(k)} μ_{l,m(k)}`,
which converges to `kernelCov greenH μ_j μ_l` by monotone convergence.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Complex
open scoped ENNReal NNReal

namespace QuantumZipper
namespace ZeroRegBdryNA

open FoldBound

/-! ## Definitions -/

/-- The cut-off region `{Im ≥ 1/(m+1)}`. -/
def cutS (m : ℕ) : Set ℂ := {z | 1 / ((m : ℝ) + 1) ≤ z.im}

/-- The cut-off measure `μ|{Im ≥ 1/(m+1)}`. -/
def cutM (m : ℕ) (μ : Measure ℂ) : Measure ℂ := μ.restrict (cutS m)

instance isFiniteMeasure_cutM (m : ℕ) (μ : Measure ℂ) [IsFiniteMeasure μ] :
    IsFiniteMeasure (cutM m μ) := by
  unfold cutM; infer_instance

/-- The folded-circle smoothing at radius `2^{-k}`. -/
def smoothM (k : ℕ) (μ : Measure ℂ) : Measure ℂ := μ.bind fun w => foldedCircle w (radius k)

/-- The hypotheses of RG-2 except admissibility. -/
structure TameBdry (μ : Measure ℂ) : Prop where
  finite : IsFiniteMeasure μ
  support : ∃ K, IsCompact K ∧ K ⊆ Hbar ∧ μ Kᶜ = 0
  pot : ∃ U : ℝ≥0, ∀ x ∈ H, ∫⁻ y, ENNReal.ofReal (greenH x y) ∂μ ≤ U
  frost : ∃ M p α : ℝ, 0 ≤ M ∧ 0 ≤ p ∧ 0 < α ∧ ∀ h' : ℝ, 0 < h' → ∀ x : ℂ, h' ≤ x.im →
    ∀ s : ℝ, 0 < s → s ≤ h' / 2 → μ (Metric.ball x s) ≤ ENNReal.ofReal (M * h' ^ (-p) * s ^ α)
  strip : ∃ C η : ℝ, 0 ≤ C ∧ 0 < η ∧ ∀ t : ℝ, 1 ≤ t →
    μ {z | z.im < Real.exp (-Real.exp t)} ≤ ENNReal.ofReal (C * t ^ (-(1 + η)))

/-! ## Elementary facts -/

theorem measurableSet_cutS (m : ℕ) : MeasurableSet (cutS m) :=
  measurableSet_le measurable_const Complex.measurable_im

theorem cutS_mono {m m' : ℕ} (h : m ≤ m') : cutS m ⊆ cutS m' := fun z (hz : _ ≤ _) =>
  (show 1 / ((m' : ℝ) + 1) ≤ z.im from (Nat.one_div_le_one_div h).trans hz)

theorem rle (μ : Measure ℂ) (s t : Set ℂ) : μ.restrict s t ≤ μ t :=
  Measure.le_iff'.1 Measure.restrict_le_self t

theorem TameBdry.im_nonpos {μ : Measure ℂ} (hμ : TameBdry μ) : μ {z | z.im ≤ 0} = 0 := by
  obtain ⟨C, η, -, hη, hS⟩ := hμ.strip
  exact ZeroRegBdry.zrb_measure_im_nonpos hη hS

theorem compl_Hbar_null {μ : Measure ℂ} (h : μ {z | z.im ≤ 0} = 0) : μ Hbarᶜ = 0 :=
  measure_mono_null (fun z hz => (not_le.mp (show ¬ (0 : ℝ) ≤ z.im from hz)).le) h

theorem TameBdry.atom {μ : Measure ℂ} (hμ : TameBdry μ) (x : ℂ) : μ {x} = 0 := by
  have := hμ.finite
  obtain ⟨U, hU⟩ := hμ.pot
  exact fb_measure_singleton hμ.im_nonpos hU x

theorem TameBdry.pot_le {μ : Measure ℂ} (hμ : TameBdry μ) :
    ∃ U : ℝ≥0, ∀ s : Set ℂ, ∀ x ∈ Hbar, fbPot (μ.restrict s) x ≤ U := by
  obtain ⟨U, hU⟩ := hμ.pot
  exact ⟨U, fun s x hx => (lintegral_mono' Measure.restrict_le_self le_rfl).trans
    (fb_pot_le hU hx)⟩

/-- Restrictions of a tame measure keep all the hypotheses (with the same constants). -/
theorem TameBdry.restrict {μ : Measure ℂ} (hμ : TameBdry μ) (s : Set ℂ) :
    TameBdry (μ.restrict s) := by
  have := hμ.finite
  obtain ⟨K, hK, hKH, hμK⟩ := hμ.support
  obtain ⟨U, hU⟩ := hμ.pot
  obtain ⟨M, p, α, hM, hp, hα, hF⟩ := hμ.frost
  obtain ⟨C, η, hC, hη, hS⟩ := hμ.strip
  exact ⟨inferInstance, ⟨K, hK, hKH, measure_mono_null_of_le (rle μ s Kᶜ) hμK⟩,
    ⟨U, fun x hx => (lintegral_mono' Measure.restrict_le_self le_rfl).trans (hU x hx)⟩,
    ⟨M, p, α, hM, hp, hα, fun h' hh x hx s' hs hsh => (rle μ s _).trans (hF h' hh x hx s' hs hsh)⟩,
    ⟨C, η, hC, hη, fun t ht => (rle μ s _).trans (hS t ht)⟩⟩
where
  measure_mono_null_of_le {a b : ℝ≥0∞} (h : a ≤ b) (hb : b = 0) : a = 0 :=
    le_antisymm (h.trans_eq hb) (zero_le)

/-! ## Smoothed measures -/

section Smooth

variable {ν : Measure ℂ} [IsFiniteMeasure ν]

instance isFiniteMeasure_smoothM (k : ℕ) : IsFiniteMeasure (smoothM k ν) :=
  CircleFubini.isFiniteMeasure_bind_circle ν

theorem smoothM_univ (k : ℕ) : smoothM k ν univ = ν univ := by
  rw [smoothM, fb_bind_apply ν _ MeasurableSet.univ]; simp

theorem smoothM_compl_Hbar (k : ℕ) : smoothM k ν Hbarᶜ = 0 := by
  rw [smoothM, fb_bind_apply ν _ isClosed_Hbar.measurableSet.compl]; simp [fb_fc_compl_Hbar]

theorem smoothM_atom (k : ℕ) (x : ℂ) : smoothM k ν {x} = 0 := by
  rw [smoothM, fb_bind_apply ν _ (measurableSet_singleton x)]
  simp [fb_fc_singleton _ (radius_pos k).ne' x]

theorem smoothM_pot_le (k : ℕ) (hH : ν {z | z.im ≤ 0} = 0) {U : ℝ≥0}
    (hU : ∀ x ∈ H, fbPot ν x ≤ U) {x : ℂ} (hx : x ∈ Hbar) :
    fbPot (smoothM k ν) x ≤ U + 8 * ν univ :=
  fb_pot_bind_le (radius_pos k) hH hU hx

theorem isAdmissibleH_smoothM (k : ℕ) {K : Set ℂ} (hK : IsCompact K) (hνK : ν Kᶜ = 0) :
    IsAdmissibleH (smoothM k ν) := by
  have hr : 0 < radius k := radius_pos k
  obtain ⟨R₀, hR₀⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  have hKR : ∀ z ∈ K, ‖z‖ ≤ R₀ := fun z hz => by
    have := hR₀ hz
    rwa [Metric.mem_closedBall, dist_zero_right] at this
  have hCct : 2 * ENNReal.ofReal (CircleFubini.potConst (radius k)) ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top
  exact CircleFubini.admissible_of_bounds
    (CircleFubini.bind_circle_support ν hr.le hνK hKR (le_refl _))
    (ENNReal.mul_ne_top (measure_ne_top _ _) hCct)
    (CircleFubini.bind_circle_pot ν fun z y => CircleFubini.foldedCircle_pot_le hr z y)

end Smooth

/-! ## Admissibility of the cut-offs -/

theorem isAdmissibleH_cutM {μ : Measure ℂ} (hμ : TameBdry μ) (m : ℕ) :
    IsAdmissibleH (cutM m μ) := by
  have := hμ.finite
  obtain ⟨K, hK, hKH, hμK⟩ := hμ.support
  obtain ⟨M, p, α, hM, hp, hα, hF⟩ := hμ.frost
  set h : ℝ := 1 / ((m : ℝ) + 1) with hh
  have hh0 : 0 < h := by positivity
  have hh1 : h ≤ 1 := by
    rw [hh, div_le_one (by positivity)]; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  set r : ℝ := h / 4 with hr
  have hr0 : 0 < r := by positivity
  have hr1 : r < 1 := by linarith
  set K' : ℝ := M * h ^ (-p) * 2 ^ α with hK'
  have hK'0 : 0 ≤ K' := by positivity
  refine ⟨inferInstance, ⟨K, hK, hKH, le_antisymm ((rle μ _ _).trans_eq hμK) (zero_le)⟩,
    ENNReal.ofReal (K' * r ^ α / α) + ENNReal.ofReal (-Real.log r) * μ univ,
    ENNReal.add_lt_top.2 ⟨ENNReal.ofReal_lt_top,
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)⟩, fun y => ?_⟩
  have hFy : ∀ s : ℝ, 0 < s → s ≤ r →
      cutM m μ (Metric.ball y s) ≤ ENNReal.ofReal (K' * s ^ α) := by
    intro s hs hsr
    rw [cutM, Measure.restrict_apply Metric.isOpen_ball.measurableSet]
    by_cases hne : (Metric.ball y s ∩ cutS m).Nonempty
    · obtain ⟨x1, hx1b, hx1S⟩ := hne
      have hsub : Metric.ball y s ∩ cutS m ⊆ Metric.ball x1 (2 * s) := fun z hz => by
        rw [Metric.mem_ball] at hx1b ⊢
        have hz1 : dist z y < s := hz.1
        calc dist z x1 ≤ dist z y + dist y x1 := dist_triangle _ _ _
          _ < s + s := add_lt_add hz1 (by rw [dist_comm]; exact hx1b)
          _ = 2 * s := by ring
      refine (measure_mono hsub).trans ((hF h hh0 x1 hx1S (2 * s) (by positivity)
        (by linarith)).trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_)))
      rw [Real.mul_rpow (by norm_num) hs.le, hK']; ring
    · rw [not_nonempty_iff_eq_empty.1 hne, measure_empty]; exact zero_le
  have hpt : ∀ x : ℂ, ENNReal.ofReal (-Real.log ‖x - y‖) ≤
      ENNReal.ofReal (Real.log (r / ‖x - y‖)) + ENNReal.ofReal (-Real.log r) := by
    intro x
    have : -Real.log ‖x - y‖ ≤ Real.log (r / ‖x - y‖) + -Real.log r := by
      rcases (norm_nonneg (x - y)).eq_or_lt with h0 | hpos
      · rw [← h0]
        have := Real.log_neg hr0 hr1
        simp only [Real.log_zero, neg_zero, div_zero, zero_add]
        linarith
      · rw [Real.log_div hr0.ne' hpos.ne']; linarith
    exact (ENNReal.ofReal_le_ofReal this).trans ENNReal.ofReal_add_le
  calc ∫⁻ x, ENNReal.ofReal (-Real.log ‖x - y‖) ∂cutM m μ
      ≤ ∫⁻ x, (ENNReal.ofReal (Real.log (r / ‖x - y‖)) + ENNReal.ofReal (-Real.log r))
          ∂cutM m μ := lintegral_mono hpt
    _ = ∫⁻ x, ENNReal.ofReal (Real.log (r / ‖x - y‖)) ∂cutM m μ +
          ENNReal.ofReal (-Real.log r) * cutM m μ univ := by
        rw [lintegral_add_right _ measurable_const, lintegral_const]
    _ ≤ ENNReal.ofReal (K' * r ^ α / α) + ENNReal.ofReal (-Real.log r) * μ univ := by
        gcongr
        · exact fb_lintegral_logPos_le_of_frostman hα hK'0 hr0 hFy
        · exact Measure.restrict_le_self

/-! ## The energy of a positive increment -/

theorem lintegral_pot_le {η₁ η₂ : Measure ℂ} (h1 : η₁ Hbarᶜ = 0) {B : ℝ≥0∞}
    (hp : ∀ x ∈ Hbar, fbPot η₂ x ≤ B) : ∫⁻ x, fbPot η₂ x ∂η₁ ≤ B * η₁ univ := by
  calc ∫⁻ x, fbPot η₂ x ∂η₁ ≤ ∫⁻ _, B ∂η₁ :=
        lintegral_mono_ae ((ae_iff.2 h1 : ∀ᵐ x ∂η₁, x ∈ Hbar).mono fun x hx => hp x hx)
    _ = B * η₁ univ := lintegral_const _

/-- **Energy of an increment.** For `b, d` finite, atomless, on `Hbar`, with bounded potentials,
`𝓔_G((b + d) − b) = 𝓔_G(d) ≤ sup P_d · d(ℂ)`. -/
theorem kernelCov2_add_le {b d : Measure ℂ} [IsFiniteMeasure b] [IsFiniteMeasure d]
    (hb : b Hbarᶜ = 0) (hd : d Hbarᶜ = 0) (hba : ∀ x, b {x} = 0) (hda : ∀ x, d {x} = 0)
    {Bb Bd : ℝ≥0∞} (hBb : Bb < ⊤) (hBd : Bd < ⊤) (hpb : ∀ x ∈ Hbar, fbPot b x ≤ Bb)
    (hpd : ∀ x ∈ Hbar, fbPot d x ≤ Bd) :
    kernelCov2 greenH (b + d, b) (b + d, b) ≤ Bd.toReal * (d univ).toReal := by
  have hs : (b + d) Hbarᶜ = 0 := by simp [hb, hd]
  have hat : ∀ x, (b + d) {x} = 0 := fun x => by simp [hba x, hda x]
  have hpadd : ∀ x, fbPot (b + d) x = fbPot b x + fbPot d x := fun x => by
    simp only [fbPot, lintegral_add_measure]
  have hpbd : ∀ x ∈ Hbar, fbPot (b + d) x ≤ Bb + Bd := fun x hx => by
    rw [hpadd]; exact add_le_add (hpb x hx) (hpd x hx)
  have e1 := fb_kernelCov_eq hs hs hat (ENNReal.add_lt_top.2 ⟨hBb, hBd⟩) hpbd
  have e2 := fb_kernelCov_eq hs hb hba hBb hpb
  have e3 := fb_kernelCov_eq hb hs hat (ENNReal.add_lt_top.2 ⟨hBb, hBd⟩) hpbd
  have e4 := fb_kernelCov_eq hb hb hba hBb hpb
  set a1 := ∫⁻ x, fbPot b x ∂b
  set a2 := ∫⁻ x, fbPot d x ∂b
  set a3 := ∫⁻ x, fbPot b x ∂d
  set a4 := ∫⁻ x, fbPot d x ∂d
  have f1 : a1 ≠ ⊤ := ((lintegral_pot_le hb hpb).trans_lt
    (ENNReal.mul_lt_top hBb (measure_lt_top _ _))).ne
  have f2 : a2 ≠ ⊤ := ((lintegral_pot_le hb hpd).trans_lt
    (ENNReal.mul_lt_top hBd (measure_lt_top _ _))).ne
  have f3 : a3 ≠ ⊤ := ((lintegral_pot_le hd hpb).trans_lt
    (ENNReal.mul_lt_top hBb (measure_lt_top _ _))).ne
  have h4 : a4 ≤ Bd * d univ := lintegral_pot_le hd hpd
  have f4 : a4 ≠ ⊤ := (h4.trans_lt (ENNReal.mul_lt_top hBd (measure_lt_top _ _))).ne
  have i1 : ∫⁻ x, fbPot (b + d) x ∂(b + d) = a1 + a2 + (a3 + a4) := by
    simp only [hpadd, lintegral_add_measure]
    rw [lintegral_add_left (fb_measurable_pot b), lintegral_add_left (fb_measurable_pot b)]
  have i2 : ∫⁻ x, fbPot b x ∂(b + d) = a1 + a3 := lintegral_add_measure _ _ _
  have i3 : ∫⁻ x, fbPot (b + d) x ∂b = a1 + a2 := by
    simp only [hpadd]; exact lintegral_add_left (fb_measurable_pot b) _
  unfold kernelCov2
  simp only
  rw [e1, e2, e3, e4, i1, i2, i3, ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨f1, f2⟩)
    (ENNReal.add_ne_top.2 ⟨f3, f4⟩), ENNReal.toReal_add f1 f2, ENNReal.toReal_add f3 f4,
    ENNReal.toReal_add f1 f3]
  have : a4.toReal ≤ Bd.toReal * (d univ).toReal := by
    rw [← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top hBd.ne (measure_ne_top _ _)) h4
  linarith

/-! ## Decompositions -/

theorem smoothM_add_cut (k m : ℕ) (μ : Measure ℂ) :
    smoothM k μ = smoothM k (cutM m μ) + smoothM k (μ.restrict (cutS m)ᶜ) := by
  ext s hs
  rw [Measure.add_apply, smoothM, smoothM, smoothM, fb_bind_apply _ _ hs, fb_bind_apply _ _ hs,
    fb_bind_apply _ _ hs, cutM]
  have e := Measure.restrict_add_restrict_compl (μ := μ) (measurableSet_cutS m)
  calc ∫⁻ w, foldedCircle w (radius k) s ∂μ
      = ∫⁻ w, foldedCircle w (radius k) s ∂(μ.restrict (cutS m) + μ.restrict (cutS m)ᶜ) := by
        rw [e]
    _ = _ := lintegral_add_measure _ _ _

theorem cutM_add_band {m m' : ℕ} (h : m ≤ m') (μ : Measure ℂ) :
    cutM m' μ = cutM m μ + μ.restrict (cutS m' \ cutS m) := by
  rw [cutM, cutM, ← Measure.restrict_union disjoint_sdiff_right
    ((measurableSet_cutS m').diff (measurableSet_cutS m)), union_diff_cancel (cutS_mono h)]

/-! ## Second moments of coordinate differences -/

section Moments

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

theorem integral_sq_sub_eq (hX : IsZeroBoundaryGFFH X P) {a b : Measure ℂ}
    (ha : IsAdmissibleH a) (hb : IsAdmissibleH b) :
    ∫ ω, (X ω a - X ω b) ^ 2 ∂P = kernelCov2 greenH (a, b) (a, b) := by
  have := ZeroReg.isProbabilityMeasure_of_zeroGFF hX
  have hm : AEMeasurable (fun ω => X ω a - X ω b) P :=
    ((hX.measurable_coord _).sub (hX.measurable_coord _)).aemeasurable
  have hA := ZeroReg.zg_memLp hX ha
  have hB := ZeroReg.zg_memLp hX hb
  have hc : P[fun ω => X ω a - X ω b] = 0 := by
    show ∫ ω, (X ω a - X ω b) ∂P = 0
    rw [integral_sub (hA.integrable one_le_two) (hB.integrable one_le_two), hX.centered _ ha,
      hX.centered _ hb, sub_zero]
  have hcov : cov[fun ω => X ω a - X ω b, fun ω => X ω a - X ω b; P] =
      kernelCov2 greenH (a, b) (a, b) := by
    rw [covariance_fun_sub_fun_sub hA hB hA hB, hX.covariance_eq _ _ ha ha,
      hX.covariance_eq _ _ ha hb, hX.covariance_eq _ _ hb ha, hX.covariance_eq _ _ hb hb]
    rfl
  rw [← hcov, covariance_self hm, variance_of_integral_eq_zero hm hc]

theorem integrable_sq_sub (hX : IsZeroBoundaryGFFH X P) {a b : Measure ℂ}
    (ha : IsAdmissibleH a) (hb : IsAdmissibleH b) :
    Integrable (fun ω => (X ω a - X ω b) ^ 2) P :=
  ((ZeroReg.zg_memLp hX ha).sub (ZeroReg.zg_memLp hX hb)).integrable_sq

/-- `𝓔(a − c) ≤ 2𝓔(a − b) + 2𝓔(b − c)` for admissible `a, b, c` (from the second moments). -/
theorem kernelCov2_triangle (hX : IsZeroBoundaryGFFH X P) {a b c : Measure ℂ}
    (ha : IsAdmissibleH a) (hb : IsAdmissibleH b) (hc : IsAdmissibleH c) :
    kernelCov2 greenH (a, c) (a, c) ≤
      2 * kernelCov2 greenH (a, b) (a, b) + 2 * kernelCov2 greenH (b, c) (b, c) := by
  rw [← integral_sq_sub_eq hX ha hc, ← integral_sq_sub_eq hX ha hb,
    ← integral_sq_sub_eq hX hb hc, ← integral_const_mul, ← integral_const_mul,
    ← integral_add ((integrable_sq_sub hX ha hb).const_mul _)
      ((integrable_sq_sub hX hb hc).const_mul _)]
  refine integral_mono (integrable_sq_sub hX ha hc)
    (((integrable_sq_sub hX ha hb).const_mul _).add ((integrable_sq_sub hX hb hc).const_mul _))
    fun ω => ?_
  simp only
  nlinarith [sq_nonneg (X ω a - 2 * X ω b + X ω c)]

end Moments

/-! ## Monotone convergence of the cut-offs -/

theorem tendsto_lintegral_cutS {ν : Measure ℂ} (hν : ν {z | z.im ≤ 0} = 0) {g : ℂ → ℝ≥0∞}
    (hg : Measurable g) :
    Tendsto (fun m => ∫⁻ y, (cutS m).indicator g y ∂ν) atTop (𝓝 (∫⁻ y, g y ∂ν)) := by
  refine lintegral_tendsto_of_tendsto_of_monotone
    (fun m => (hg.indicator (measurableSet_cutS m)).aemeasurable)
    (ae_of_all _ fun y m m' hmm' =>
      indicator_le_indicator_of_subset (cutS_mono hmm') (fun _ => zero_le) y) ?_
  have hpos : ∀ᵐ y ∂ν, 0 < y.im := by
    rw [ae_iff]; simpa only [not_lt] using hν
  filter_upwards [hpos] with y hy
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hy
  refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨N, fun m hm => ?_⟩)
  have hmem : y ∈ cutS m := (Nat.one_div_le_one_div hm).trans hN.le
  exact (indicator_of_mem hmem g).symm

theorem fbPot_cutM (m : ℕ) (ν : Measure ℂ) (x : ℂ) :
    fbPot (cutM m ν) x = ∫⁻ y, (cutS m).indicator (fun y => ENNReal.ofReal (greenH x y)) y ∂ν := by
  rw [fbPot, cutM, lintegral_indicator (measurableSet_cutS m)]

/-- **Convergence of the covariances of the cut-offs.** -/
theorem tendsto_kernelCov_cutM {μ ν : Measure ℂ} (hμ : TameBdry μ) (hν : TameBdry ν) :
    Tendsto (fun m => kernelCov greenH (cutM m μ) (cutM m ν)) atTop
      (𝓝 (kernelCov greenH μ ν)) := by
  have := hμ.finite
  have := hν.finite
  obtain ⟨Uν, hUν⟩ := hν.pot_le
  have hμH := compl_Hbar_null hμ.im_nonpos
  have hνH := compl_Hbar_null hν.im_nonpos
  have hpotν : ∀ x ∈ Hbar, fbPot ν x ≤ Uν := fun x hx => by
    simpa using hUν univ x hx
  have e0 := fb_kernelCov_eq hμH hνH hν.atom ENNReal.coe_lt_top hpotν
  have em : ∀ m, kernelCov greenH (cutM m μ) (cutM m ν) =
      (∫⁻ x, (cutS m).indicator (fbPot (cutM m ν)) x ∂μ).toReal := fun m => by
    have h1 : cutM m μ Hbarᶜ = 0 := le_antisymm ((rle μ _ _).trans_eq hμH) (zero_le)
    have h2 : cutM m ν Hbarᶜ = 0 := le_antisymm ((rle ν _ _).trans_eq hνH) (zero_le)
    have hat : ∀ x, cutM m ν {x} = 0 := fun x =>
      le_antisymm ((rle ν _ _).trans_eq (hν.atom x)) (zero_le)
    rw [fb_kernelCov_eq h1 h2 hat ENNReal.coe_lt_top (fun x hx => hUν _ x hx), cutM,
      lintegral_indicator (measurableSet_cutS m)]
  simp_rw [em]
  rw [e0]
  have hfin : ∫⁻ x, fbPot ν x ∂μ ≠ ⊤ :=
    ((lintegral_pot_le hμH hpotν).trans_lt
      (ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_lt_top _ _))).ne
  refine (ENNReal.tendsto_toReal hfin).comp ?_
  refine lintegral_tendsto_of_tendsto_of_monotone
    (fun m => ((fb_measurable_pot _).indicator (measurableSet_cutS m)).aemeasurable)
    (ae_of_all _ fun x m m' hmm' => by
      show (cutS m).indicator (fbPot (cutM m ν)) x ≤ (cutS m').indicator (fbPot (cutM m' ν)) x
      have h1 : fbPot (cutM m ν) x ≤ fbPot (cutM m' ν) x :=
        lintegral_mono' (Measure.restrict_mono (cutS_mono hmm') le_rfl) le_rfl
      exact (indicator_le_indicator h1).trans
        (indicator_le_indicator_of_subset (cutS_mono hmm') (fun _ => zero_le) x)) ?_
  · have hpos : ∀ᵐ x ∂μ, 0 < x.im := by
      rw [ae_iff]; simpa only [not_lt] using hμ.im_nonpos
    filter_upwards [hpos] with x hx
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hx
    have hinner : Tendsto (fun m => fbPot (cutM m ν) x) atTop (𝓝 (fbPot ν x)) := by
      simp_rw [fbPot_cutM]
      exact tendsto_lintegral_cutS hν.im_nonpos
        (ENNReal.measurable_ofReal.comp (measurable_greenH.comp
          (measurable_const.prodMk measurable_id)))
    refine hinner.congr' (eventually_atTop.2 ⟨N, fun m hm => ?_⟩)
    have hmem : x ∈ cutS m := (Nat.one_div_le_one_div hm).trans hN.le
    exact (indicator_of_mem hmem _).symm

/-! ## Variance bounds for the three comparisons -/

section Bounds

variable {μ : Measure ℂ}

/-- `𝓔(S_k μ − S_k μ_m) ≤ (U + 8μ(ℂ)) μ{Im < 1/(m+1)}`. -/
theorem var_smooth_cut_le (hμ : TameBdry μ) {U : ℝ≥0} (hU : ∀ x ∈ H, fbPot μ x ≤ U)
    (k m : ℕ) :
    kernelCov2 greenH (smoothM k μ, smoothM k (cutM m μ))
        (smoothM k μ, smoothM k (cutM m μ)) ≤
      ((U : ℝ) + 8 * (μ univ).toReal) * (μ (cutS m)ᶜ).toReal := by
  have := hμ.finite
  have hH := hμ.im_nonpos
  have hr : ∀ s : Set ℂ, (μ.restrict s) {z | z.im ≤ 0} = 0 := fun s =>
    le_antisymm ((rle μ _ _).trans_eq hH) zero_le
  have hUr : ∀ s : Set ℂ, ∀ x ∈ H, fbPot (μ.restrict s) x ≤ U := fun s x hx =>
    (lintegral_mono' Measure.restrict_le_self le_rfl).trans (hU x hx)
  have hB : (↑U + 8 * μ univ : ℝ≥0∞) < ⊤ :=
    ENNReal.add_lt_top.2 ⟨ENNReal.coe_lt_top, ENNReal.mul_lt_top (by simp) (measure_lt_top _ _)⟩
  have hpb : ∀ s : Set ℂ, ∀ x ∈ Hbar, fbPot (smoothM k (μ.restrict s)) x ≤ ↑U + 8 * μ univ :=
    fun s x hx => (smoothM_pot_le k (hr s) (hUr s) hx).trans (by gcongr; exact Measure.restrict_le_self)
  rw [smoothM_add_cut k m μ]
  refine (kernelCov2_add_le (smoothM_compl_Hbar k) (smoothM_compl_Hbar k) (smoothM_atom k)
    (smoothM_atom k) hB hB (hpb _) (hpb _)).trans (le_of_eq ?_)
  rw [smoothM_univ, Measure.restrict_apply_univ,
    ENNReal.toReal_add ENNReal.coe_ne_top (ENNReal.mul_ne_top (by simp) (measure_ne_top _ _)),
    ENNReal.toReal_mul]
  simp

/-- `𝓔(μ_{m'} − μ_m) ≤ U μ{Im < 1/(m+1)}` for `m ≤ m'`. -/
theorem var_band_le (hμ : TameBdry μ) {U : ℝ≥0} (hU : ∀ x ∈ H, fbPot μ x ≤ U) {m m' : ℕ}
    (h : m ≤ m') :
    kernelCov2 greenH (cutM m' μ, cutM m μ) (cutM m' μ, cutM m μ) ≤
      (U : ℝ) * (μ (cutS m)ᶜ).toReal := by
  have := hμ.finite
  have hμH := compl_Hbar_null hμ.im_nonpos
  have hs : ∀ s : Set ℂ, (μ.restrict s) Hbarᶜ = 0 := fun s =>
    le_antisymm ((rle μ _ _).trans_eq hμH) zero_le
  have ha : ∀ s : Set ℂ, ∀ x, (μ.restrict s) {x} = 0 := fun s x =>
    le_antisymm ((rle μ _ _).trans_eq (hμ.atom x)) zero_le
  have hp : ∀ s : Set ℂ, ∀ x ∈ Hbar, fbPot (μ.restrict s) x ≤ U := fun s x hx =>
    (lintegral_mono' Measure.restrict_le_self le_rfl).trans (fb_pot_le hU hx)
  rw [cutM_add_band h μ]
  refine (kernelCov2_add_le (hs _) (hs _) (ha _) (ha _) ENNReal.coe_lt_top ENNReal.coe_lt_top
    (hp _) (hp _)).trans ?_
  rw [ENNReal.coe_toReal, Measure.restrict_apply_univ]
  exact mul_le_mul_of_nonneg_left (ENNReal.toReal_mono (measure_ne_top _ _)
    (measure_mono fun z hz => hz.2)) U.2

end Bounds

/-! ## The core argument -/

section Core

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

theorem one_eighth_pow_le_exp {c₀ : ℝ} (hc : c₀ ≤ Real.log 8) (k : ℕ) :
    (1 / 8 : ℝ) ^ k ≤ Real.exp (-c₀ * k) := by
  have e : (1 / 8 : ℝ) ^ k = Real.exp (k * Real.log (1 / 8)) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  rw [e, Real.exp_le_exp, one_div, Real.log_inv]
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith

/-- **Core.** Along cut-off scales `m(k)` with `μ{Im < 1/(m(k)+1)} ≤ 8^{-k}`:
`X(S_k μ) − X(μ_{m(k)}) → 0` a.s., and `X(μ_{m(k)})` converges a.s. -/
theorem core (hX : IsZeroBoundaryGFFH X P) {μ : Measure ℂ} (hμ : TameBdry μ) {m : ℕ → ℕ}
    (hmono : Monotone m) (hw : ∀ k, μ (cutS (m k))ᶜ ≤ ENNReal.ofReal ((1 / 8 : ℝ) ^ k)) :
    (∀ᵐ ω ∂P, Tendsto (fun k => X ω (smoothM k μ) - X ω (cutM (m k) μ)) atTop (𝓝 0)) ∧
      (∀ᵐ ω ∂P, ∃ L, Tendsto (fun k => X ω (cutM (m k) μ)) atTop (𝓝 L)) := by
  have := ZeroReg.isProbabilityMeasure_of_zeroGFF hX
  have := hμ.finite
  obtain ⟨K, hK, hKH, hμK⟩ := hμ.support
  obtain ⟨U, hU⟩ := hμ.pot
  have hU' : ∀ x ∈ H, fbPot μ x ≤ U := hU
  obtain ⟨M, p, α, hM, hp, hα, hF⟩ := hμ.frost
  obtain ⟨C, η, hC, hη, hS⟩ := hμ.strip
  have hH := hμ.im_nonpos
  have hcutK : ∀ n, cutM n μ Kᶜ = 0 := fun n => le_antisymm ((rle μ _ _).trans_eq hμK) zero_le
  have hwr : ∀ k, (μ (cutS (m k))ᶜ).toReal ≤ (1 / 8 : ℝ) ^ k := fun k =>
    ENNReal.toReal_le_of_le_ofReal (by positivity) (hw k)
  constructor
  · -- `X(S_k μ) − X(μ_{m(k)}) → 0`
    set γ := α / (4 * (p + α)) with hγ_def
    have hpa : 0 < p + α := by linarith
    have hγ : 0 < γ := by positivity
    set A := 2 * (U : ℝ) + 8 * (μ univ).toReal with hA_def
    set B := (1 / α + 4 * 2 ^ α) * M * Real.exp (p * Real.log 2) * (μ univ).toReal with hB_def
    set Cw := (U : ℝ) + 8 * (μ univ).toReal with hCw
    have hA : 0 ≤ A := by positivity
    have hB : 0 ≤ B := by positivity
    have hCw0 : 0 ≤ Cw := by positivity
    set c₀ := min (α / 4) (Real.log 8) with hc₀
    have hc₀p : 0 < c₀ := lt_min (by positivity) (Real.log_pos (by norm_num))
    set v : ℕ → ℝ := fun k => (2 * A * C) * Real.log (γ * k) ^ (-(1 + η)) +
      (2 * (B + 1) + 2 * Cw) * Real.exp (-c₀ * k) with hv_def
    have hev : ∀ᶠ k : ℕ in atTop, 8 ≤ k ∧ 3 ≤ γ * k :=
      (eventually_ge_atTop 8).and
        ((tendsto_natCast_atTop_atTop.const_mul_atTop hγ).eventually_ge_atTop 3)
    have hpos : ∀ᶠ k in atTop, 0 < v k := by
      filter_upwards [hev] with k hk
      have h1 : 0 ≤ Real.log (γ * k) := Real.log_nonneg (by linarith [hk.2])
      have h2 : 0 ≤ (2 * A * C) * Real.log (γ * k) ^ (-(1 + η)) :=
        mul_nonneg (by positivity) (Real.rpow_nonneg h1 _)
      have h3 : 0 < (2 * (B + 1) + 2 * Cw) * Real.exp (-c₀ * k) := by positivity
      simp only [hv_def]
      linarith
    have hlim : Tendsto (fun k : ℕ => v k * Real.log k) atTop (𝓝 0) :=
      ZeroRegBdry.zrb_tendsto_rate hγ hη hc₀p
    have hb : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
        P.real {ω | ε ≤ |X ω (smoothM k μ) - X ω (cutM (m k) μ)|} ≤
          2 * Real.exp (-ε ^ 2 / (2 * v k)) := by
      intro ε hε
      filter_upwards [hev, hpos] with k hk hvk
      have ha1 : IsAdmissibleH (smoothM k μ) := isAdmissibleH_smoothM k hK hμK
      have ha2 : IsAdmissibleH (smoothM k (cutM (m k) μ)) :=
        isAdmissibleH_smoothM k hK (hcutK (m k))
      have ha3 : IsAdmissibleH (cutM (m k) μ) := isAdmissibleH_cutM hμ (m k)
      have hlaw := ZeroRegBdry.zrb_map_sub_eq_gaussianReal hX ha1 ha3
      -- the two pieces
      have hV1 := var_smooth_cut_le hμ hU' k (m k)
      have hr : (cutM (m k) μ) {z | z.im ≤ 0} = 0 := le_antisymm ((rle μ _ _).trans_eq hH) zero_le
      have hUc : ∀ x ∈ H, ∫⁻ y, ENNReal.ofReal (greenH x y) ∂(cutM (m k) μ) ≤ U :=
        fun x hx => (lintegral_mono' Measure.restrict_le_self le_rfl).trans (hU x hx)
      have hFc : ∀ h' : ℝ, 0 < h' → ∀ x : ℂ, h' ≤ x.im → ∀ s : ℝ, 0 < s → s ≤ h' / 2 →
          cutM (m k) μ (Metric.ball x s) ≤ ENNReal.ofReal (M * h' ^ (-p) * s ^ α) :=
        fun h' hh x hx s hs hsh => (rle μ _ _).trans (hF h' hh x hx s hs hsh)
      have hSc : ∀ t : ℝ, 1 ≤ t → cutM (m k) μ {z | z.im < Real.exp (-Real.exp t)} ≤
          ENNReal.ofReal (C * t ^ (-(1 + η))) := fun t ht => (rle μ _ _).trans (hS t ht)
      have hV2 := ZeroRegBdry.zrb_energy_le hr hUc hM hp hα hFc hC hSc hk.1 hk.2
      have hmass : (cutM (m k) μ univ).toReal ≤ (μ univ).toReal :=
        ENNReal.toReal_mono (measure_ne_top _ _) (rle μ _ _)
      have hL : 0 ≤ C * Real.log (γ * k) ^ (-(1 + η)) :=
        mul_nonneg hC (Real.rpow_nonneg (Real.log_nonneg (by linarith [hk.2])) _)
      have hcoef : 0 ≤ (1 / α + 4 * 2 ^ α) * M * Real.exp (p * Real.log 2) := by positivity
      have he1 : Real.exp (-(α / 4) * k) ≤ Real.exp (-c₀ * k) := by
        rw [Real.exp_le_exp]
        have : c₀ ≤ α / 4 := min_le_left _ _
        nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
      have he2 : (1 / 8 : ℝ) ^ k ≤ Real.exp (-c₀ * k) := one_eighth_pow_le_exp (min_le_right _ _) k
      have hV2' : kernelCov2 greenH (smoothM k (cutM (m k) μ), cutM (m k) μ)
          (smoothM k (cutM (m k) μ), cutM (m k) μ) ≤
          A * (C * Real.log (γ * k) ^ (-(1 + η))) + (B + 1) * Real.exp (-c₀ * k) := by
        refine hV2.trans ?_
        have t1 : (2 * (U : ℝ) + 8 * (cutM (m k) μ univ).toReal) *
            (C * Real.log (γ * k) ^ (-(1 + η))) ≤ A * (C * Real.log (γ * k) ^ (-(1 + η))) :=
          mul_le_mul_of_nonneg_right (by linarith) hL
        have t2 : (1 / α + 4 * 2 ^ α) * M * Real.exp (p * Real.log 2) *
            (cutM (m k) μ univ).toReal * Real.exp (-(α / 4) * k) ≤
            B * Real.exp (-c₀ * k) := by
          rw [hB_def]
          have := mul_le_mul_of_nonneg_left hmass hcoef
          have h0 : 0 ≤ (1 / α + 4 * 2 ^ α) * M * Real.exp (p * Real.log 2) *
              (cutM (m k) μ univ).toReal := mul_nonneg hcoef ENNReal.toReal_nonneg
          calc _ ≤ (1 / α + 4 * 2 ^ α) * M * Real.exp (p * Real.log 2) *
                (cutM (m k) μ univ).toReal * Real.exp (-c₀ * k) :=
                mul_le_mul_of_nonneg_left he1 h0
            _ ≤ _ := mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
        have := Real.exp_pos (-c₀ * k)
        linarith
      have hE : kernelCov2 greenH (smoothM k μ, cutM (m k) μ) (smoothM k μ, cutM (m k) μ) ≤
          v k := by
        refine (kernelCov2_triangle hX ha1 ha2 ha3).trans ?_
        have hw1 := mul_le_mul_of_nonneg_left ((hwr k).trans he2) hCw0
        simp only [hv_def]
        nlinarith
      have h := ZeroRegBdry.zrb_measureReal_abs_ge_le
        (Y := fun ω => X ω (smoothM k μ) - X ω (cutM (m k) μ))
        ((hX.measurable_coord _).sub (hX.measurable_coord _)) hlaw
        (Real.toNNReal_le_toNNReal hE) hε.le
      rwa [Real.coe_toNNReal _ hvk.le] at h
    exact ZeroRegBdry.zrb_ae_tendsto_zero hpos hlim hb
  · -- `X(μ_{m(k)})` is Cauchy
    set W : ℕ → Ω → ℝ := fun k ω => X ω (cutM (m (k + 1)) μ) - X ω (cutM (m k) μ) with hWdef
    have hvar : ∀ k, ∫ ω, W k ω ^ 2 ∂P ≤ U * (1 / 8 : ℝ) ^ k := fun k => by
      rw [hWdef, integral_sq_sub_eq hX (isAdmissibleH_cutM hμ _) (isAdmissibleH_cutM hμ _)]
      exact (var_band_le hμ hU' (hmono k.le_succ)).trans
        (mul_le_mul_of_nonneg_left (hwr k) U.2)
    have hprob : ∀ k, P.real {ω | (1 / 2 : ℝ) ^ k ≤ |W k ω|} ≤ U * (1 / 2 : ℝ) ^ k := by
      intro k
      have hint : Integrable (fun ω => W k ω ^ 2) P :=
        integrable_sq_sub hX (isAdmissibleH_cutM hμ _) (isAdmissibleH_cutM hμ _)
      have hm := mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun ω => sq_nonneg (W k ω)) hint
        ((1 / 4 : ℝ) ^ k)
      have e4 : (1 / 4 : ℝ) ^ k = ((1 / 2 : ℝ) ^ k) ^ 2 := by
        rw [← pow_mul, mul_comm k 2, pow_mul]; norm_num
      have hsub : {ω | (1 / 2 : ℝ) ^ k ≤ |W k ω|} ⊆ {ω | (1 / 4 : ℝ) ^ k ≤ W k ω ^ 2} := by
        intro ω hω
        show (1 / 4 : ℝ) ^ k ≤ W k ω ^ 2
        rw [e4, ← sq_abs (W k ω)]
        exact pow_le_pow_left₀ (by positivity) hω 2
      have h1 := measureReal_mono (μ := P) hsub
      have h4 : (0 : ℝ) < (1 / 4) ^ k := by positivity
      have e8 : (1 / 8 : ℝ) ^ k = (1 / 4) ^ k * (1 / 2) ^ k := by
        rw [← mul_pow]; norm_num
      have := (hm.trans (hvar k))
      rw [e8] at this
      have h5 : (1 / 4 : ℝ) ^ k * P.real {ω | (1 / 2 : ℝ) ^ k ≤ |W k ω|} ≤
          (1 / 4 : ℝ) ^ k * (U * (1 / 2) ^ k) := by
        nlinarith [mul_le_mul_of_nonneg_left h1 h4.le]
      exact le_of_mul_le_mul_left h5 h4
    have hsum : Summable fun k => P.real {ω | (1 / 2 : ℝ) ^ k ≤ |W k ω|} :=
      Summable.of_nonneg_of_le (fun k => measureReal_nonneg) hprob
        ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _)
    have hfin : (∑' k, P {ω | (1 / 2 : ℝ) ^ k ≤ |W k ω|}) ≠ ⊤ := by
      have e : ∀ k, P {ω | (1 / 2 : ℝ) ^ k ≤ |W k ω|} =
          ENNReal.ofReal (P.real {ω | (1 / 2 : ℝ) ^ k ≤ |W k ω|}) := fun k =>
        (ofReal_measureReal (measure_ne_top _ _)).symm
      simp_rw [e]
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => measureReal_nonneg) hsum]
      exact ENNReal.ofReal_ne_top
    filter_upwards [ae_eventually_notMem hfin] with ω hω
    have hs : Summable fun k => dist (X ω (cutM (m k) μ)) (X ω (cutM (m (k + 1)) μ)) := by
      refine Summable.of_norm_bounded_eventually_nat (g := fun k => (1 / 2 : ℝ) ^ k)
        (summable_geometric_of_lt_one (by norm_num) (by norm_num)) ?_
      filter_upwards [hω] with k hk
      simp only [not_le] at hk
      rw [Real.norm_eq_abs, abs_of_nonneg dist_nonneg, Real.dist_eq, abs_sub_comm]
      exact hk.le
    exact cauchySeq_tendsto_of_complete (cauchySeq_of_summable_dist hs)

end Core

/-! ## Choice of the cut-off scales -/

theorem tendsto_measure_cutS_compl {μ : Measure ℂ} (hμ : TameBdry μ) :
    Tendsto (fun n => μ (cutS n)ᶜ) atTop (𝓝 0) := by
  have := hμ.finite
  have h := tendsto_measure_iInter_atTop (μ := μ) (s := fun n => (cutS n)ᶜ)
    (fun n => (measurableSet_cutS n).compl.nullMeasurableSet)
    (fun a b hab => compl_subset_compl.2 (cutS_mono hab)) ⟨0, measure_ne_top _ _⟩
  have h0 : μ (⋂ n, (cutS n)ᶜ) = 0 := by
    refine measure_mono_null (fun z hz => ?_) hμ.im_nonpos
    show z.im ≤ 0
    by_contra hpos
    push_neg at hpos
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hpos
    exact (mem_iInter.1 hz N) hN.le
  rw [h0] at h
  exact h

theorem exists_cut_seq {ι : Type*} [Fintype ι] {μ : ι → Measure ℂ} (hμ : ∀ j, TameBdry (μ j)) :
    ∃ m : ℕ → ℕ, Monotone m ∧ (∀ k, k ≤ m k) ∧
      ∀ j k, μ j (cutS (m k))ᶜ ≤ ENNReal.ofReal ((1 / 8 : ℝ) ^ k) := by
  have hev : ∀ j k, ∃ N, ∀ n ≥ N, μ j (cutS n)ᶜ ≤ ENNReal.ofReal ((1 / 8 : ℝ) ^ k) :=
    fun j k => eventually_atTop.1 ((tendsto_measure_cutS_compl (hμ j)).eventually
      (Iic_mem_nhds (ENNReal.ofReal_pos.2 (by positivity))))
  choose N hN using hev
  refine ⟨fun k => (Finset.range (k + 1)).sup fun i => i + Finset.univ.sup fun j => N j i,
    fun a b hab => Finset.sup_mono (Finset.range_mono (Nat.succ_le_succ hab)),
    fun k => ?_, fun j k => hN j k _ ?_⟩
  · exact (Nat.le_add_right k _).trans
      (Finset.le_sup (f := fun i => i + Finset.univ.sup fun j => N j i)
        (Finset.self_mem_range_succ k))
  · exact ((Finset.le_sup (f := fun j => N j k) (Finset.mem_univ j)).trans
      (Nat.le_add_left _ k)).trans
      (Finset.le_sup (f := fun i => i + Finset.univ.sup fun j => N j i)
        (Finset.self_mem_range_succ k))

/-! ## (1) Almost-sure convergence -/

section Main

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- **(1)** For a tame (not necessarily admissible) `μ`, almost surely
`X(S_k μ) = ∫ avgReg X k dμ → evalReg X μ`. -/
theorem ae_tendsto_evalReg_NA (hX : IsZeroBoundaryGFFH X P) {μ : Measure ℂ} (hμ : TameBdry μ) :
    ∀ᵐ ω ∂P, Tendsto (fun k => X ω (smoothM k μ)) atTop (𝓝 (evalReg (X ω) μ)) ∧
      Tendsto (fun k => ∫ w, avgReg (X ω) k w ∂μ) atTop (𝓝 (evalReg (X ω) μ)) := by
  have := hμ.finite
  obtain ⟨K, hK, hKH, hμK⟩ := hμ.support
  obtain ⟨m, hmono, -, hw⟩ := exists_cut_seq (ι := Unit) (fun _ => hμ)
  obtain ⟨h1, h2⟩ := core hX hμ hmono (hw ())
  have hfub : ∀ᵐ ω ∂P, ∀ k, ∫ z, avgReg (X ω) k z ∂μ = X ω (smoothM k μ) :=
    ae_all_iff.2 fun k => ZeroReg.integral_avgReg_ae_eq_bind_zero hX k μ hK hKH hμK
  filter_upwards [h1, h2, hfub] with ω hD hZ hf
  obtain ⟨L, hL⟩ := hZ
  have hY : Tendsto (fun k => X ω (smoothM k μ)) atTop (𝓝 L) := by
    have := hD.add hL
    simpa using this
  have hI : Tendsto (fun k => ∫ w, avgReg (X ω) k w ∂μ) atTop (𝓝 L) := by
    simp_rw [hf]; exact hY
  have he : evalReg (X ω) μ = L := hI.limUnder_eq
  rw [he]
  exact ⟨hY, hI⟩

/-- **(1')** The cut-off coordinates converge to the same limit. -/
theorem ae_tendsto_cut_evalReg_NA (hX : IsZeroBoundaryGFFH X P) {μ : Measure ℂ}
    (hμ : TameBdry μ) {m : ℕ → ℕ} (hmono : Monotone m)
    (hw : ∀ k, μ (cutS (m k))ᶜ ≤ ENNReal.ofReal ((1 / 8 : ℝ) ^ k)) :
    ∀ᵐ ω ∂P, Tendsto (fun k => X ω (cutM (m k) μ)) atTop (𝓝 (evalReg (X ω) μ)) := by
  filter_upwards [(core hX hμ hmono hw).1, ae_tendsto_evalReg_NA hX hμ] with ω hD hY
  have := hY.1.sub hD
  simpa using this

/-! ## (2) The joint characteristic function -/

/-- Joint Gaussian characteristic function of admissible coordinates. -/
theorem integral_cexp_sum_adm (hX : IsZeroBoundaryGFFH X P) {ι : Type*} [Fintype ι]
    {a : ι → Measure ℂ} (ha : ∀ j, IsAdmissibleH (a j)) (t : ι → ℝ) :
    ∫ ω, cexp (I * ((∑ j, t j * X ω (a j) : ℝ) : ℂ)) ∂P =
      cexp (-((∑ j, ∑ l, t j * t l * kernelCov greenH (a j) (a l) : ℝ) : ℂ) / 2) := by
  have := ZeroReg.isProbabilityMeasure_of_zeroGFF hX
  set Y : Ω → ℝ := fun ω => ∑ j, t j * X ω (a j) with hY
  have hproc : IsGaussianProcess (fun (j : ι) (ω : Ω) => t j • X ω (a j)) P :=
    (hX.gaussian.comp_right fun j => (⟨a j, ha j⟩ : {μ : Measure ℂ // IsAdmissibleH μ})).smul t
  have hG : HasGaussianLaw Y P := by
    have := hproc.hasGaussianLaw_fun_sum (I := Finset.univ)
    simpa only [smul_eq_mul] using this
  have hmem : ∀ j, MemLp (fun ω => t j * X ω (a j)) 2 P := fun j =>
    (ZeroReg.zg_memLp hX (ha j)).const_mul (t j)
  have hmean : P[Y] = 0 := by
    show ∫ ω, ∑ j, t j * X ω (a j) ∂P = 0
    rw [integral_finset_sum _ (fun j _ => (hmem j).integrable one_le_two)]
    simp [integral_const_mul, hX.centered _ (ha _)]
  have hvar : Var[Y; P] = ∑ j, ∑ l, t j * t l * kernelCov greenH (a j) (a l) := by
    rw [hY, variance_fun_sum hmem]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    rw [covariance_const_mul_left, covariance_const_mul_right,
      hX.covariance_eq _ _ (ha j) (ha l)]
    ring
  have hvnn : 0 ≤ Var[Y; P] := variance_nonneg _ _
  calc ∫ ω, cexp (I * ((∑ j, t j * X ω (a j) : ℝ) : ℂ)) ∂P
      = ∫ x, cexp (I * (x : ℂ)) ∂(P.map Y) := by
        rw [integral_map hG.aemeasurable (by fun_prop)]
    _ = charFun (P.map Y) 1 := by rw [charFun_apply_real]; simp [mul_comm]
    _ = _ := by
        rw [hG.map_eq_gaussianReal, charFun_gaussianReal, hmean, Real.coe_toNNReal _ hvnn, hvar]
        congr 1
        push_cast
        ring

/-- **(2)** For finitely many tame (not necessarily admissible) `μ_j`,
`E exp(i Σ t_j evalReg X μ_j) = exp(−½ Σ t_j t_l kernelCov greenH μ_j μ_l)`. -/
theorem integral_cexp_evalReg_NA (hX : IsZeroBoundaryGFFH X P) {ι : Type*} [Fintype ι]
    {μ : ι → Measure ℂ} (hμ : ∀ j, TameBdry (μ j)) (t : ι → ℝ) :
    ∫ ω, cexp (I * ((∑ j, t j * evalReg (X ω) (μ j) : ℝ) : ℂ)) ∂P =
      cexp (-((∑ j, ∑ l, t j * t l * kernelCov greenH (μ j) (μ l) : ℝ) : ℂ) / 2) := by
  have := ZeroReg.isProbabilityMeasure_of_zeroGFF hX
  obtain ⟨m, hmono, hmk, hw⟩ := exists_cut_seq hμ
  have hall : ∀ᵐ ω ∂P, ∀ j, Tendsto (fun k => X ω (cutM (m k) (μ j))) atTop
      (𝓝 (evalReg (X ω) (μ j))) :=
    ae_all_iff.2 fun j => ae_tendsto_cut_evalReg_NA hX (hμ j) hmono (hw j)
  have hc : Continuous fun x : ℝ => cexp (I * (x : ℂ)) := by fun_prop
  have hlim : Tendsto (fun k => ∫ ω, cexp (I * ((∑ j, t j * X ω (cutM (m k) (μ j)) : ℝ) : ℂ)) ∂P)
      atTop (𝓝 (∫ ω, cexp (I * ((∑ j, t j * evalReg (X ω) (μ j) : ℝ) : ℂ)) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) (fun k => ?_)
      (integrable_const _) (fun k => ae_of_all _ fun ω => ?_) ?_
    · exact hc.comp_aestronglyMeasurable (Finset.measurable_sum Finset.univ
        fun j _ => (hX.measurable_coord _).const_mul _).aestronglyMeasurable
    · rw [mul_comm]; exact (Complex.norm_exp_ofReal_mul_I _).le
    · filter_upwards [hall] with ω hω
      exact (hc.tendsto _).comp (tendsto_finset_sum _ fun j _ => (hω j).const_mul (t j))
  have hval : ∀ k, ∫ ω, cexp (I * ((∑ j, t j * X ω (cutM (m k) (μ j)) : ℝ) : ℂ)) ∂P =
      cexp (-((∑ j, ∑ l, t j * t l * kernelCov greenH (cutM (m k) (μ j)) (cutM (m k) (μ l)) :
        ℝ) : ℂ) / 2) := fun k =>
    integral_cexp_sum_adm hX (fun j => isAdmissibleH_cutM (hμ j) (m k)) t
  have hm : Tendsto m atTop atTop := tendsto_atTop_mono hmk tendsto_id
  have hQ : Tendsto (fun k => (∑ j, ∑ l, t j * t l *
      kernelCov greenH (cutM (m k) (μ j)) (cutM (m k) (μ l)) : ℝ)) atTop
      (𝓝 (∑ j, ∑ l, t j * t l * kernelCov greenH (μ j) (μ l))) :=
    tendsto_finset_sum _ fun j _ => tendsto_finset_sum _ fun l _ =>
      ((tendsto_kernelCov_cutM (hμ j) (hμ l)).comp hm).const_mul _
  have hQc : Tendsto (fun k => cexp (-((∑ j, ∑ l, t j * t l *
      kernelCov greenH (cutM (m k) (μ j)) (cutM (m k) (μ l)) : ℝ) : ℂ) / 2)) atTop
      (𝓝 (cexp (-((∑ j, ∑ l, t j * t l * kernelCov greenH (μ j) (μ l) : ℝ) : ℂ) / 2))) := by
    have hcc : Continuous fun q : ℝ => cexp (-(q : ℂ) / 2) := by fun_prop
    exact (hcc.tendsto _).comp hQ
  simp_rw [hval] at hlim
  exact tendsto_nhds_unique hlim hQc

/-- **(2), two measures.** `E exp(i(evalReg X μ − evalReg X ν)) = exp(−𝓔_G(μ − ν)/2)`. -/
theorem integral_cexp_evalReg_sub_NA (hX : IsZeroBoundaryGFFH X P) {μ ν : Measure ℂ}
    (hμ : TameBdry μ) (hν : TameBdry ν) :
    ∫ ω, cexp (I * ((evalReg (X ω) μ - evalReg (X ω) ν : ℝ) : ℂ)) ∂P =
      cexp (-((kernelCov2 greenH (μ, ν) (μ, ν) : ℝ) : ℂ) / 2) := by
  have h := integral_cexp_evalReg_NA hX (μ := fun b : Bool => if b then μ else ν)
    (fun b => by cases b <;> simp [hμ, hν]) (fun b => if b then 1 else -1)
  simp only [Fintype.sum_bool, if_true, Bool.false_eq_true, if_false] at h
  convert h using 3
  · congr 3; ring
  · simp only [kernelCov2]; push_cast; ring

end Main

end ZeroRegBdryNA
end QuantumZipper
