import QuantumZipper.Proofs.RS.OnePointWeightedGen
import QuantumZipper.Proofs.Probability.Girsanov.HTransform
import QuantumZipper.Proofs.ItoLite.OptionalStopping

/-!
# RS S1-3P, part 2: the two-stage stopping argument for the tamed one-point state

Blueprint `blueprint/EXT_RS_BLUEPRINT.md`, §5, node S1-3P (Girsanov-free form of S1-Q/S1-3).

Fix the taming level `c > 0`, the target `r ≤ Im z / 2` and a horizon slack `δ ∈ (0,1]`. Write
`ℓ = log r`, `L₀ = log Im z`, `L₁ = min L₀ (ℓ + 4/κ)` (one unit of radial time before `ℓ`), and
let `τ` (resp. `ρ ≤ τ`) be the hitting time, capped at `T`, of `{Im Z ≤ c} ∪ {L ≤ ℓ}`
(resp. `{Im Z ≤ c} ∪ {L ≤ L₁}`) by the tamed one-point state `U = opProc κ B c z`.
* Stage 1 (S1-M, optional stopping; AUDIT9 P9-5): `E[φ_M(U_ρ)] = φ_M(z, L₀)`
  (GIR-D, equality form, for the zero-generator profile `phiMF`).
* Stage 2 (S1-W): the barrier `barF κ K δ ℓ` is a supersolution, so with `Y = 1{L_ρ ≤ L₁}`,
  `E[Y · barF(U_τ)] ≤ E[Y · barF(U_ρ)]` (GIR-D). At `ρ` on `{Y = 1}` the remaining radial time is
  `σ₁ ∈ [m, 2]`, `m = min((κ/4) log 2, 1)`, so `barF(U_ρ) ≤ e^{2K} C_W (1/√m)^β S_ρ^β` and
  `S_ρ^β = e^{(1−κ/8) L₁} φ_M(U_ρ)`.
* Terminal step: on `A_δ = {L_τ ≤ ℓ, Im Z_τ > c, S_τ ≥ √δ}` one has `Y = 1`, `L_τ = ℓ`, `σ = δ`
  and `barF(U_τ) ≥ barW_β(1)`.
The result is `barW_β(1) · P(A_δ) ≤ e^{2K} C_W (1/√m)^β e^{(1−κ/8)L₁} φ_M(z, L₀)`
(`opw_core`).

This is the fallback S1-3P of the blueprint: GIR-D applied under `P` to the barrier, together
with S1-M's optional stopping, following the structure of Lawler–Zhou, *SLE curves and natural
parametrization*, arXiv:1006.4936, proof of Prop. 2.3 (p. 16), with LZ Lemma 2.2 (26) replaced by
the own barrier S1-W. The Girsanov weighting of LZ is not needed: under `Q = (M_τ/M_0)·P` the
function `V = barrier/φ_M` is a `Q`-supersolution iff `barrier` is a `P`-supersolution (GIR-0), and
Bayes' rule (GIR-1) turns the `Q`-inequality back into exactly the `P`-inequality used here.
-/

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace RS

open FrozenMart FwdHolo

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The stopping region `{Im Z ≤ c} ∪ {L ≤ a}`. -/
def opCl (c a : ℝ) : Set (ℂ × ℝ) := {x | x.1.im ≤ c} ∪ {x | x.2 ≤ a}

/-- The state region `{Im Z ≥ c, a ≤ L ≤ L₀}`. -/
def opK (c a L₀ : ℝ) : Set (ℂ × ℝ) := {x | c ≤ x.1.im ∧ a ≤ x.2 ∧ x.2 ≤ L₀}

theorem isClosed_opCl (c a : ℝ) : IsClosed (opCl c a) :=
  (isClosed_le (Complex.continuous_im.comp continuous_fst) continuous_const).union
    (isClosed_le continuous_snd continuous_const)

theorem isClosed_opK (c a L₀ : ℝ) : IsClosed (opK c a L₀) :=
  (isClosed_le continuous_const (Complex.continuous_im.comp continuous_fst)).inter
    ((isClosed_le continuous_const continuous_snd).inter
      (isClosed_le continuous_snd continuous_const))

omit mΩ in
/-- A hitting time of a closed set by a continuous path is a hitting place (copy of
`Williams.mem_hittingBtwn_of_isClosed`, to keep the imports small). -/
theorem opw_mem_hit {β : Type*} [PseudoMetricSpace β] {u : ℝ≥0 → Ω → β}
    (hc : ∀ ω, Continuous (u · ω)) {S : Set β} (hS : IsClosed S) {m : ℝ≥0} {ω : Ω}
    (hex : ∃ j ∈ Set.Icc 0 m, u j ω ∈ S) : u (hittingBtwn u S 0 m ω) ω ∈ S := by
  set A : Set ℝ≥0 := Set.Icc 0 m ∩ {i | u i ω ∈ S} with hA
  have hAc : IsClosed A := isClosed_Icc.inter (hS.preimage (hc ω))
  have hne : A.Nonempty := by obtain ⟨j, hj, hjS⟩ := hex; exact ⟨j, hj, hjS⟩
  have hmem := hAc.csInf_mem hne (OrderBot.bddBelow A)
  have heq : hittingBtwn u S 0 m ω = sInf A := by
    simp only [hittingBtwn, hex, ↓reduceIte, hA]
  rw [heq]; exact hmem.2

theorem opProc_snd_le (hc : 0 < c) (κ : ℝ) (z : ℂ) (ω : Ω) (t : ℝ≥0) :
    (opProc κ B c z t ω).2 ≤ Real.log z.im := by
  show tamedLogCR _ c z t ≤ _
  rw [tamedLogCR]
  have e : (fun s => tamedLField c (tamedZ (drive κ B ω) c z s))
      = fun s => -((2 / proj c (tamedZ (drive κ B ω) c z s)).im ^ 2) :=
    funext fun s => tamedLField_eq_neg_sq hc _
  have h := intervalIntegral.integral_nonneg (μ := volume)
    (f := fun s => (2 / proj c (tamedZ (drive κ B ω) c z s)).im ^ 2) t.coe_nonneg
    (fun u _ => sq_nonneg _)
  rw [e, intervalIntegral.integral_neg]
  linarith

theorem opProc_zero (hBc : ∀ ω, Continuous (B · ω)) (hB0 : ∀ ω, B 0 ω = 0) (hc : 0 < c)
    (κ : ℝ) (z : ℂ) (ω : Ω) : opProc κ B c z 0 ω = (z, Real.log z.im) := by
  rw [opProc_integralEq hBc hc κ z ω 0, hB0 ω]
  simp

theorem continuous_opProc (hBc : ∀ ω, Continuous (B · ω)) (hc : 0 < c) (κ : ℝ) (z : ℂ)
    (ω : Ω) : Continuous fun s => opProc κ B c z s ω :=
  Dynkin.continuous_of_integralEq hBc (continuous_opDrift hc) (norm_opDrift_le hc)
    (opProc_integralEq hBc hc κ z) ω

/-- Before meeting `opCl c a`, the tamed state stays in `opK c a (log Im z)`. -/
theorem opProc_mem_opK (hBc : ∀ ω, Continuous (B · ω)) (hB0 : ∀ ω, B 0 ω = 0) (hc : 0 < c)
    (κ : ℝ) {z : ℂ} (hcz : c ≤ z.im) {a : ℝ} (ha : a ≤ Real.log z.im) (ω : Ω) (t : ℝ≥0)
    (hs : ∀ s < t, opProc κ B c z s ω ∉ opCl c a) :
    opProc κ B c z t ω ∈ opK c a (Real.log z.im) := by
  have hUc := continuous_opProc hBc hc κ z ω
  suffices h : c ≤ (opProc κ B c z t ω).1.im ∧ a ≤ (opProc κ B c z t ω).2 from
    ⟨h.1, h.2, opProc_snd_le hc κ z ω t⟩
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with h0 | hpos
  · rw [← h0, opProc_zero hBc hB0 hc κ z ω]
    exact ⟨hcz, ha⟩
  · have hS : IsClosed {s : ℝ≥0 | c ≤ (opProc κ B c z s ω).1.im ∧ a ≤ (opProc κ B c z s ω).2} :=
      (isClosed_le continuous_const (Complex.continuous_im.comp (continuous_fst.comp hUc))).inter
        (isClosed_le continuous_const (continuous_snd.comp hUc))
    have hsub : Iio t ⊆
        {s : ℝ≥0 | c ≤ (opProc κ B c z s ω).1.im ∧ a ≤ (opProc κ B c z s ω).2} := by
      intro s hst
      have h := hs s hst
      simp only [opCl, mem_union, mem_ofPred_eq, not_or, not_le] at h
      exact ⟨h.1.le, h.2.le⟩
    have := hS.closure_subset_iff.2 hsub
    rw [closure_Iio' (a := t) ⟨0, hpos⟩] at this
    exact this (le_refl t)

/-- Values of the barrier on the state space: `0 ≤ barF ≤ e^{Kσ}`. -/
theorem barF_nonneg_le {κ K t₀ L₀ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8) {x : ℂ × ℝ}
    (hx : 0 < x.1.im) :
    0 ≤ barF κ K t₀ L₀ x ∧ barF κ K t₀ L₀ x ≤ Real.exp (K * (t₀ + κ / 4 * (x.2 - L₀))) := by
  have hp : 0 < 8 / κ - 1 := by
    rw [sub_pos, lt_div_iff₀ hκ]; linarith
  have hξ : 0 ≤ Real.sin (Complex.arg x.1) / Real.sqrt (t₀ + κ / 4 * (x.2 - L₀)) :=
    div_nonneg (sin_arg_pos hx).le (Real.sqrt_nonneg _)
  have hW := barW_mem_Icc hp hξ
  have he := Real.exp_pos (K * (t₀ + κ / 4 * (x.2 - L₀)))
  refine ⟨mul_nonneg he.le hW.1, ?_⟩
  calc barF κ K t₀ L₀ x = Real.exp (K * (t₀ + κ / 4 * (x.2 - L₀)))
        * barW (8 / κ - 1) (Real.sin (Complex.arg x.1) / Real.sqrt (t₀ + κ / 4 * (x.2 - L₀))) :=
        rfl
    _ ≤ Real.exp (K * (t₀ + κ / 4 * (x.2 - L₀))) * 1 := mul_le_mul_of_nonneg_left hW.2 he.le
    _ = _ := mul_one _

theorem phiMF_nonneg {κ : ℝ} {x : ℂ × ℝ} (hx : 0 < x.1.im) : 0 ≤ phiMF κ x :=
  phiM_nonneg (arg_mem_Ioo_of_im_pos hx)

/-- `sin^β(arg Z) = e^{(1−κ/8) L} φ_M(Z, L)`. -/
theorem sin_rpow_eq_phiMF (κ : ℝ) (x : ℂ × ℝ) :
    Real.sin (Complex.arg x.1) ^ (8 / κ - 1) = Real.exp ((1 - κ / 8) * x.2) * phiMF κ x := by
  simp only [phiMF, phiM]
  rw [← mul_assoc, ← Real.exp_add,
    show (1 - κ / 8) * x.2 + (κ / 8 - 1) * x.2 = 0 by ring, Real.exp_zero, one_mul]

/-- The capped hitting time of `{Im Z ≤ c} ∪ {L ≤ a}` by the tamed one-point state. -/
def opTau (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (c : ℝ) (z : ℂ) (a : ℝ) (T : ℝ≥0) (ω : Ω) : ℝ≥0 :=
  hittingBtwn (opProc κ B c z) (opCl c a) 0 T ω

/-- The event of the core estimate: at `τ` the state has reached `L ≤ log r` with `Im Z > c`
and `sin arg Z ≥ √δ`. -/
def opEvt (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (c : ℝ) (z : ℂ) (r : ℝ) (T : ℝ≥0) (δ : ℝ) : Set Ω :=
  {ω | (opProc κ B c z (opTau κ B c z (Real.log r) T ω) ω).2 ≤ Real.log r
    ∧ c < (opProc κ B c z (opTau κ B c z (Real.log r) T ω) ω).1.im
    ∧ Real.sqrt δ ≤ Real.sin (Complex.arg (opProc κ B c z (opTau κ B c z (Real.log r) T ω) ω).1)}

/-- **S1-3P core (tamed state, fixed horizon slack `δ`).** See the module docstring. -/
theorem opw_core (hB : IsPreBrownianReal B P) (hBc : ∀ ω, Continuous (B · ω))
    (hBm : ∀ t, Measurable (B t)) (hB0 : ∀ ω, B 0 ω = 0) {κ : ℝ} (hκ : 0 < κ) (hκ8 : κ < 8)
    {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ ξ > 0, -K * barW (8 / κ - 1) ξ + ξ * deriv (barW (8 / κ - 1)) ξ * (ξ ^ 2 - 1) / 2 ≤ 0)
    {CW : ℝ} (hCW : ∀ ξ ≥ 0, barW (8 / κ - 1) ξ ≤ CW * ξ ^ (8 / κ - 1))
    {c : ℝ} (hc : 0 < c) (T : ℝ≥0) {z : ℂ} (hcz : c ≤ z.im) {r : ℝ} (hr : 0 < r)
    (hrz : r ≤ z.im / 2) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    P.real (opEvt κ B c z r T δ) * barW (8 / κ - 1) 1
      ≤ Real.exp (2 * K) * CW * (1 / Real.sqrt (min (κ / 4 * Real.log 2) 1)) ^ (8 / κ - 1)
        * Real.exp ((1 - κ / 8) * min (Real.log z.im) (Real.log r + 4 / κ))
        * phiMF κ (z, Real.log z.im) := by
  have hPm : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hp : 0 < 8 / κ - 1 := by rw [sub_pos, lt_div_iff₀ hκ]; linarith
  have hzim : 0 < z.im := hc.trans_le hcz
  set p := 8 / κ - 1 with hpdef
  set ℓ := Real.log r with hℓ
  set L₀ := Real.log z.im with hL₀
  set L₁ := min L₀ (ℓ + 4 / κ) with hL₁
  set m := min (κ / 4 * Real.log 2) 1 with hm
  set U := opProc κ B c z with hUdef
  have hU : ∀ ω (t : ℝ≥0), U t ω = (z, L₀) + (∫ r in (0 : ℝ)..t, opDrift c (U r.toNNReal ω))
      + B t ω • opNoise κ := fun ω t => opProc_integralEq hBc hc κ z ω t
  have hU0 : ∀ ω, U 0 ω = (z, L₀) := fun ω => opProc_zero hBc hB0 hc κ z ω
  have hb := lipschitzWith_opDrift hc
  have hbM := norm_opDrift_le hc
  have hUc : ∀ ω, Continuous (U · ω) := continuous_opProc hBc hc κ z
  set 𝓕 := NonSwallow.bmFilt hBm with h𝓕
  have hUm : ∀ t, Measurable[𝓕 t] (U t) :=
    Dynkin.measurable_of_integralEq 𝓕 (NonSwallow.bmFilt_adapted hBm) hBc hb hbM hU hUc
  have hprog : IsStronglyProgressive 𝓕 U :=
    StronglyAdapted.isStronglyProgressive_of_continuous (fun t => (hUm t).stronglyMeasurable) hUc
  -- levels
  have h4κ : 0 < 4 / κ := div_pos four_pos hκ
  have hℓL₀ : ℓ ≤ L₀ := Real.log_le_log hr (by linarith)
  have hL₀ℓ : Real.log 2 ≤ L₀ - ℓ := by
    rw [hL₀, hℓ, ← Real.log_div hzim.ne' hr.ne']
    exact Real.log_le_log two_pos (by rw [le_div_iff₀ hr]; linarith)
  have hℓL₁ : ℓ ≤ L₁ := le_min hℓL₀ (by linarith)
  have hL₁L₀ : L₁ ≤ L₀ := min_le_left _ _
  have hsub : opCl c ℓ ⊆ opCl c L₁ := fun x hx =>
    hx.elim Or.inl (fun h => Or.inr (le_trans h hℓL₁))
  -- stopping times
  set τ : Ω → ℝ≥0 := fun ω => hittingBtwn U (opCl c ℓ) 0 T ω with hτ
  set ρ : Ω → ℝ≥0 := fun ω => hittingBtwn U (opCl c L₁) 0 T ω with hρ
  have hτst : IsStoppingTime 𝓕 (fun ω => ((τ ω : ℝ≥0) : WithTop ℝ≥0)) :=
    ItoLite.isStoppingTime_hittingBtwn_of_isClosed hUm hUc (isClosed_opCl c ℓ) T
  have hρst : IsStoppingTime 𝓕 (fun ω => ((ρ ω : ℝ≥0) : WithTop ℝ≥0)) :=
    ItoLite.isStoppingTime_hittingBtwn_of_isClosed hUm hUc (isClosed_opCl c L₁) T
  have hρτ : ∀ ω, ρ ω ≤ τ ω := by
    intro ω
    by_cases hex : ∃ j ∈ Icc 0 T, U j ω ∈ opCl c ℓ
    · exact hittingBtwn_le_of_mem (zero_le) (hittingBtwn_le ω)
        (hsub (opw_mem_hit hUc (isClosed_opCl c ℓ) hex))
    · have : τ ω = T := by simp only [hτ, hittingBtwn, if_neg hex]
      rw [this]; exact hittingBtwn_le ω
  -- regions
  have hUK : ∀ a, a ≤ L₀ → ∀ ω (t : ℝ≥0), t ≤ T → (∀ s < t, U s ω ∉ opCl c a) →
      U t ω ∈ opK c a L₀ :=
    fun a ha ω t _ hs => opProc_mem_opK hBc hB0 hc κ hcz ha ω t hs
  have hKτ : ∀ ω, U (τ ω) ω ∈ opK c ℓ L₀ := fun ω =>
    hUK ℓ hℓL₀ ω _ (hittingBtwn_le ω) (fun s hs => notMem_of_lt_hittingBtwn hs zero_le)
  have hKρ₁ : ∀ ω, U (ρ ω) ω ∈ opK c L₁ L₀ := fun ω =>
    hUK L₁ hL₁L₀ ω _ (hittingBtwn_le ω) (fun s hs => notMem_of_lt_hittingBtwn hs zero_le)
  have hKρ : ∀ ω, U (ρ ω) ω ∈ opK c ℓ L₀ := fun ω =>
    ⟨(hKρ₁ ω).1, hℓL₁.trans (hKρ₁ ω).2.1, (hKρ₁ ω).2.2⟩
  -- measurability
  have hmτ' : Measurable[hτst.measurableSpace] fun ω => U (τ ω) ω :=
    measurable_stoppedValue hprog hτst
  have hmρ' : Measurable[hρst.measurableSpace] fun ω => U (ρ ω) ω :=
    measurable_stoppedValue hprog hρst
  have hmτ : Measurable fun ω => U (τ ω) ω := hmτ'.mono hτst.measurableSpace_le le_rfl
  have hmρ : Measurable fun ω => U (ρ ω) ω := hmρ'.mono hρst.measurableSpace_le le_rfl
  set Y : Ω → ℝ := fun ω => if (U (ρ ω) ω).2 ≤ L₁ then 1 else 0 with hY
  have hYm' : Measurable[hρst.measurableSpace] Y :=
    Measurable.ite (measurableSet_le (measurable_snd.comp hmρ') measurable_const)
      measurable_const measurable_const
  have hYm : Measurable Y := hYm'.mono hρst.measurableSpace_le le_rfl
  have hY0 : ∀ ω, 0 ≤ Y ω := fun ω => by simp only [hY]; split_ifs <;> norm_num
  have hY1 : ∀ ω, Y ω ≤ 1 := fun ω => by simp only [hY]; split_ifs <;> norm_num
  -- stage 2: the barrier
  set O : Set (ℂ × ℝ) := {x | 0 < x.1.im ∧ 0 < δ + κ / 4 * (x.2 - ℓ)} with hO
  have hOo : IsOpen O := (isOpen_lt continuous_const
    (Complex.continuous_im.comp continuous_fst)).inter (isOpen_lt continuous_const
    (show Continuous fun x : ℂ × ℝ => δ + κ / 4 * (x.2 - ℓ) by fun_prop))
  have hσK : ∀ x ∈ opK c ℓ L₀, δ ≤ δ + κ / 4 * (x.2 - ℓ) := fun x hx => by
    have : 0 ≤ κ / 4 * (x.2 - ℓ) := mul_nonneg (by positivity) (by linarith [hx.2.1])
    linarith
  have hKO : opK c ℓ L₀ ⊆ O := fun x hx => ⟨hc.trans_le hx.1, hδ.trans_le (hσK x hx)⟩
  set Mb : ℝ := Real.exp (K * (δ + κ / 4 * (L₀ - ℓ))) with hMb
  have hFM : ∀ x ∈ opK c ℓ L₀, |barF κ K δ ℓ x| ≤ Mb := by
    intro x hx
    obtain ⟨h0, h1⟩ := barF_nonneg_le (K := K) (t₀ := δ) (L₀ := ℓ) hκ hκ8 (hc.trans_le hx.1)
    rw [abs_of_nonneg h0]
    refine h1.trans (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ?_ hK0))
    have := hx.2.2
    have : κ / 4 * (x.2 - ℓ) ≤ κ / 4 * (L₀ - ℓ) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  have hLF : ∀ x ∈ opK c ℓ L₀, x ∉ opCl c ℓ →
      dynkinGen (opDrift c) (opNoise κ) (barF κ K δ ℓ) x ≤ 0 :=
    fun x hx _ => dynkinGen_barF_le hκ hκ8 hc hK hx.1 (hδ.trans_le (hσK x hx))
  have hstage2 : ∫ ω, Y ω * barF κ K δ ℓ (U (τ ω) ω) ∂P
      ≤ ∫ ω, Y ω * barF κ K δ ℓ (U (ρ ω) ω) ∂P :=
    Girsanov.integral_mul_localDynkin_stopped_le hB hBc 𝓕 (NonSwallow.bmFilt_adapted hBm)
      (NonSwallow.bmFilt_le_past hBm) hb hbM hU hOo (isClosed_opCl c ℓ) (isClosed_opK c ℓ L₀)
      hKO (contDiffOn_barF hκ hκ8) hLF T (hUK ℓ hℓL₀) hFM hρst hτst
      (fun ω => WithTop.coe_le_coe.2 (hρτ ω)) (fun ω => le_rfl) hYm' hY0 hY1
  -- stage 1: the martingale `M`
  have hFM1 : ∀ x ∈ opK c ℓ L₀, |phiMF κ x| ≤ Real.exp ((κ / 8 - 1) * ℓ) := by
    intro x hx
    have hxim : 0 < x.1.im := hc.trans_le hx.1
    rw [abs_of_nonneg (phiMF_nonneg hxim)]
    have hs1 : Real.sin (Complex.arg x.1) ^ p ≤ 1 :=
      Real.rpow_le_one (sin_arg_pos hxim).le (Real.sin_le_one _) hp.le
    have he : Real.exp ((κ / 8 - 1) * x.2) ≤ Real.exp ((κ / 8 - 1) * ℓ) := by
      refine Real.exp_le_exp.2 ?_
      have h8 : κ / 8 - 1 ≤ 0 := by linarith
      nlinarith [hx.2.1]
    calc phiMF κ x = Real.exp ((κ / 8 - 1) * x.2) * Real.sin (Complex.arg x.1) ^ p := rfl
      _ ≤ Real.exp ((κ / 8 - 1) * x.2) * 1 := mul_le_mul_of_nonneg_left hs1 (Real.exp_pos _).le
      _ ≤ _ := by rw [mul_one]; exact he
  have hstage1 := Girsanov.integral_mul_localDynkin_stopped_eq hB hBc 𝓕
    (NonSwallow.bmFilt_adapted hBm) (NonSwallow.bmFilt_le_past hBm) hb hbM hU
    (isOpen_lt continuous_const (Complex.continuous_im.comp continuous_fst)) (isClosed_opCl c ℓ)
    (isClosed_opK c ℓ L₀) (fun x hx => hc.trans_le hx.1) (contDiffOn_phiMF κ)
    (fun x hx _ => dynkinGen_phiMF hκ hc hx.1) T (hUK ℓ hℓL₀) hFM1
    (isStoppingTime_const 𝓕 (0 : ℝ≥0)) hρst (fun ω => WithTop.coe_le_coe.2 (zero_le))
    (fun ω => WithTop.coe_le_coe.2 (hρτ ω)) (Y := fun _ => 1) measurable_const
    (fun _ => zero_le_one) (CY := 1) (fun _ => le_rfl)
  have h1' : ∫ ω, phiMF κ (U (ρ ω) ω) ∂P = phiMF κ (z, L₀) := by
    have e : ∀ ω, (fun _ : Ω => (1 : ℝ)) ω
        * phiMF κ (stoppedValue U (fun _ => ((0 : ℝ≥0) : WithTop ℝ≥0)) ω) = phiMF κ (z, L₀) :=
      fun ω => by
        show 1 * phiMF κ (U 0 ω) = _
        rw [one_mul, hU0 ω]
    calc ∫ ω, phiMF κ (U (ρ ω) ω) ∂P
        = ∫ ω, (fun _ : Ω => (1 : ℝ)) ω
          * phiMF κ (stoppedValue U (fun ω => ((ρ ω : ℝ≥0) : WithTop ℝ≥0)) ω) ∂P := by
          simp only [one_mul]; rfl
      _ = _ := hstage1
      _ = ∫ ω, phiMF κ (z, L₀) ∂P := integral_congr_ae (ae_of_all _ e)
      _ = _ := by simp
  -- the pointwise bound at `ρ`
  set C₁ := Real.exp (2 * K) * CW * (1 / Real.sqrt m) ^ p * Real.exp ((1 - κ / 8) * L₁)
    with hC₁def
  have hCW0 : 0 ≤ CW := by
    have h1 := hCW 1 zero_le_one
    rw [Real.one_rpow, mul_one] at h1
    exact (barW_mem_Icc hp zero_le_one).1.trans h1
  have hm0 : 0 < m := lt_min (mul_pos (by positivity) (Real.log_pos one_lt_two)) one_pos
  have hC₁ : 0 ≤ C₁ := by positivity
  have hpt : ∀ ω, Y ω * barF κ K δ ℓ (U (ρ ω) ω) ≤ C₁ * phiMF κ (U (ρ ω) ω) := by
    intro ω
    have hx := hKρ₁ ω
    have hxim : 0 < (U (ρ ω) ω).1.im := hc.trans_le hx.1
    simp only [hY]
    split_ifs with hL
    · have hLeq : (U (ρ ω) ω).2 = L₁ := le_antisymm hL hx.2.1
      set x := U (ρ ω) ω with hx_def
      set σ₁ := δ + κ / 4 * (x.2 - ℓ) with hσ₁
      have hmL : m ≤ κ / 4 * (L₁ - ℓ) := by
        rcases min_choice L₀ (ℓ + 4 / κ) with h | h
        · rw [hL₁, h]
          exact (min_le_left _ _).trans
            (mul_le_mul_of_nonneg_left hL₀ℓ (by positivity))
        · rw [hL₁, h, show ℓ + 4 / κ - ℓ = 4 / κ by ring,
            show κ / 4 * (4 / κ) = 1 by field_simp]
          exact min_le_right _ _
      have hL1u : κ / 4 * (L₁ - ℓ) ≤ 1 := by
        have : L₁ - ℓ ≤ 4 / κ := by linarith [min_le_right L₀ (ℓ + 4 / κ)]
        calc κ / 4 * (L₁ - ℓ) ≤ κ / 4 * (4 / κ) := mul_le_mul_of_nonneg_left this (by positivity)
          _ = 1 := by field_simp
      have hσm : m ≤ σ₁ := by rw [hσ₁, hLeq]; linarith
      have hσ2 : σ₁ ≤ 2 := by rw [hσ₁, hLeq]; linarith
      set S := Real.sin (Complex.arg x.1) with hSdef
      have hS : 0 < S := sin_arg_pos hxim
      have hsq : 0 < Real.sqrt σ₁ := Real.sqrt_pos.2 (hm0.trans_le hσm)
      have hξ : 0 ≤ S / Real.sqrt σ₁ := div_nonneg hS.le hsq.le
      have hW1 : barW p (S / Real.sqrt σ₁) ≤ CW * (S / Real.sqrt σ₁) ^ p := hCW _ hξ
      have hW2 : (S / Real.sqrt σ₁) ^ p ≤ (S / Real.sqrt m) ^ p :=
        Real.rpow_le_rpow hξ (div_le_div_of_nonneg_left hS.le (Real.sqrt_pos.2 hm0)
          (Real.sqrt_le_sqrt hσm)) hp.le
      have hW3 : (S / Real.sqrt m) ^ p = S ^ p * (1 / Real.sqrt m) ^ p := by
        rw [div_eq_mul_one_div, Real.mul_rpow hS.le (by positivity)]
      have hSp : S ^ p = Real.exp ((1 - κ / 8) * L₁) * phiMF κ x := by
        rw [← hLeq]; exact sin_rpow_eq_phiMF κ x
      have he : Real.exp (K * σ₁) ≤ Real.exp (2 * K) :=
        Real.exp_le_exp.2 (by nlinarith)
      calc 1 * barF κ K δ ℓ x = Real.exp (K * σ₁) * barW p (S / Real.sqrt σ₁) := by
            rw [one_mul]; rfl
        _ ≤ Real.exp (2 * K) * (CW * (S / Real.sqrt m) ^ p) :=
            mul_le_mul he (hW1.trans (mul_le_mul_of_nonneg_left hW2 hCW0))
              (barW_mem_Icc hp hξ).1 (Real.exp_pos _).le
        _ = C₁ * phiMF κ x := by rw [hW3, hSp, hC₁def]; ring
    · rw [zero_mul]; exact mul_nonneg hC₁ (phiMF_nonneg hxim)
  -- the terminal step at `τ`
  set A := opEvt κ B c z r T δ with hA
  have hmτ2 : Measurable fun ω => (U (τ ω) ω).1.im :=
    Complex.measurable_im.comp (measurable_fst.comp hmτ)
  have hAm : MeasurableSet A := by
    have h1 : Measurable fun ω => (U (τ ω) ω).2 := measurable_snd.comp hmτ
    have h3 : Measurable fun ω => Real.sin (Complex.arg (U (τ ω) ω).1) := by
      simp_rw [Complex.sin_arg]
      exact hmτ2.div (measurable_norm.comp (measurable_fst.comp hmτ))
    exact (measurableSet_le h1 measurable_const).inter
      ((measurableSet_lt measurable_const hmτ2).inter (measurableSet_le measurable_const h3))
  have hterm : ∀ ω, A.indicator (fun _ => barW p 1) ω ≤ Y ω * barF κ K δ ℓ (U (τ ω) ω) := by
    intro ω
    have hx := hKτ ω
    have hxim : 0 < (U (τ ω) ω).1.im := hc.trans_le hx.1
    by_cases hωA : ω ∈ A
    · rw [indicator_of_mem hωA]
      obtain ⟨hL, hIm, hS⟩ := hωA
      change (U (τ ω) ω).2 ≤ ℓ at hL
      change c < (U (τ ω) ω).1.im at hIm
      change Real.sqrt δ ≤ Real.sin (Complex.arg (U (τ ω) ω).1) at hS
      have hYone : Y ω = 1 := by
        have hexρ : ∃ j ∈ Icc 0 T, U j ω ∈ opCl c L₁ :=
          ⟨τ ω, ⟨zero_le, hittingBtwn_le ω⟩, hsub (Or.inr hL)⟩
        have hρmem : U (ρ ω) ω ∈ opCl c L₁ := opw_mem_hit hUc (isClosed_opCl c L₁) hexρ
        simp only [hY]
        rcases hρmem with hIm' | hL'
        · exfalso
          have hle : τ ω ≤ ρ ω :=
            hittingBtwn_le_of_mem (zero_le) (hittingBtwn_le ω) (Or.inl hIm')
          have heq : τ ω = ρ ω := le_antisymm hle (hρτ ω)
          have h' : (U (τ ω) ω).1.im ≤ c := by rw [heq]; exact hIm'
          linarith
        · exact if_pos (show (U (ρ ω) ω).2 ≤ L₁ from hL')
      have hLeq : (U (τ ω) ω).2 = ℓ := le_antisymm hL hx.2.1
      rw [hYone, one_mul]
      have hσ : δ + κ / 4 * ((U (τ ω) ω).2 - ℓ) = δ := by rw [hLeq]; ring
      show barW p 1 ≤ Real.exp (K * (δ + κ / 4 * ((U (τ ω) ω).2 - ℓ)))
        * barW p (Real.sin (Complex.arg (U (τ ω) ω).1)
          / Real.sqrt (δ + κ / 4 * ((U (τ ω) ω).2 - ℓ)))
      rw [hσ]
      have hξ1 : 1 ≤ Real.sin (Complex.arg (U (τ ω) ω).1) / Real.sqrt δ := by
        rw [le_div_iff₀ (Real.sqrt_pos.2 hδ), one_mul]; exact hS
      have hW := barW_mono hp zero_le_one hξ1
      have he : 1 ≤ Real.exp (K * δ) := Real.one_le_exp (mul_nonneg hK0 hδ.le)
      calc barW p 1 = 1 * barW p 1 := (one_mul _).symm
        _ ≤ _ := mul_le_mul he hW (barW_mem_Icc hp zero_le_one).1 (by positivity)
    · rw [indicator_of_notMem hωA]
      exact mul_nonneg (hY0 ω) (barF_nonneg_le hκ hκ8 hxim).1
  -- integrability
  have hbarc : ContinuousOn (barF κ K δ ℓ) O := (contDiffOn_barF hκ hκ8).continuousOn
  have hphic : ContinuousOn (phiMF κ) {x : ℂ × ℝ | 0 < x.1.im} := (contDiffOn_phiMF κ).continuousOn
  have hmbτ : Measurable fun ω => barF κ K δ ℓ (U (τ ω) ω) :=
    Girsanov.measurable_comp_of_continuousOn hKO hbarc hmτ hKτ
  have hmbρ : Measurable fun ω => barF κ K δ ℓ (U (ρ ω) ω) :=
    Girsanov.measurable_comp_of_continuousOn hKO hbarc hmρ hKρ
  have hmpρ : Measurable fun ω => phiMF κ (U (ρ ω) ω) :=
    Girsanov.measurable_comp_of_continuousOn (fun x hx => hc.trans_le hx.1) hphic hmρ hKρ
  have hYb : ∀ ω (v : ℝ), |v| ≤ Mb → ‖Y ω * v‖ ≤ Mb := fun ω v hv => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hY0 ω)]
    calc Y ω * |v| ≤ 1 * Mb := mul_le_mul (hY1 ω) hv (abs_nonneg _) zero_le_one
      _ = Mb := one_mul _
  have hIτ : Integrable (fun ω => Y ω * barF κ K δ ℓ (U (τ ω) ω)) P :=
    Integrable.of_bound (hYm.mul hmbτ).aestronglyMeasurable Mb
      (ae_of_all _ fun ω => hYb ω _ (hFM _ (hKτ ω)))
  have hIρ : Integrable (fun ω => Y ω * barF κ K δ ℓ (U (ρ ω) ω)) P :=
    Integrable.of_bound (hYm.mul hmbρ).aestronglyMeasurable Mb
      (ae_of_all _ fun ω => hYb ω _ (hFM _ (hKρ ω)))
  have hIφ : Integrable (fun ω => phiMF κ (U (ρ ω) ω)) P :=
    Integrable.of_bound hmpρ.aestronglyMeasurable (Real.exp ((κ / 8 - 1) * ℓ))
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hFM1 _ (hKρ ω))
  have hIA : Integrable (A.indicator fun _ => barW p 1) P :=
    (integrable_const _).indicator hAm
  -- conclusion
  calc P.real A * barW p 1 = ∫ ω, A.indicator (fun _ => barW p 1) ω ∂P := by
        rw [integral_indicator_const _ hAm, smul_eq_mul]
    _ ≤ ∫ ω, Y ω * barF κ K δ ℓ (U (τ ω) ω) ∂P := integral_mono hIA hIτ hterm
    _ ≤ ∫ ω, Y ω * barF κ K δ ℓ (U (ρ ω) ω) ∂P := hstage2
    _ ≤ ∫ ω, C₁ * phiMF κ (U (ρ ω) ω) ∂P := integral_mono hIρ (hIφ.const_mul C₁) hpt
    _ = C₁ * phiMF κ (z, L₀) := by rw [integral_const_mul, h1']

end RS
end QuantumZipper
