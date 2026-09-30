import QuantumZipper.Proofs.LQG.WedgeMeasCoord
import QuantumZipper.Proofs.Field.PairAffBasic
import QuantumZipper.Proofs.LQG.LocalRule
import QuantumZipper.Proofs.LQG.IndepParams

/-!
# Proposition 1.7, node D5-e: raw pairings of rescaled/translated wedge fields (deterministic part)

Sheffield, arXiv:1012.4797, Proposition 1.7 (§1.6, pp. 21–23, 25–26) compares the laws of the
reference wedge `canonical γ W` and of the shifted field `canonical γ (translate (canonical γ W) y)`.
`fieldLawFull` reads raw test pairings (`pairRaw`), and for a rescaled field
`rescale S Q a` the raw pairing `rescale S Q a η = evalReg S (η ∘ (a·)⁻¹) + Q log a · |η|` is a
limit along the radii `2^{-k}` for `S`, while the regularized pairing `evalReg (rescale S Q a) η`
reads `S` along the radii `a·2^{-k}` (S5-PLAN, D5-c flag). This file shows that the two agree
whenever the circle-regularized pairings of the underlying witness have a **continuum limit**
(`s → 0⁺` along all radii), which is what PAIR-AFF provides a.s. for the free field.

* `RawRep S G t b c δ₀ r₀`: the raw circle values of `S` on `{Im > δ₀}` at radii `< r₀` are
  `G (t + b w, b r) + c` for a regular witness `G`;
* `RawRep.avgReg_eq`, `RawRep.evalReg_fc`, `RawRep.evalReg_eq`: regularized values of such `S`;
* `RawRep.translateRep`, `RawRep.rescaleRep`: stability under real translations and dilations;
* `RawRep.rescale_apply_eq`: **raw = regularized** for `rescale S Q a` at a compactly supported
  finite `η`, given the continuum limit of `s ↦ ∫ G (t + b a u, s) dη(u)`;
* `rawRep_wedgeField`: the wedge field `wedgeField (lateralPart x) A Q` (singular at `0`) has a
  raw representation on `{Im > ρ₀}` through the regular witness of `x + ofFun (gT … ρ₀)` (the
  radial profile truncated at modulus `ρ₀/4`), for a good free sample `x` and continuous `A`;
* `tendsto_integral_smooth_aff`: for continuous `g` and compactly supported finite `η` in `Hbar`,
  `∫∫ g d fc(t + b u, s) dη(u) → ∫ g (t + b u) dη(u)` as `s → 0⁺` (task item (i)).

Own elementary arguments (bookkeeping of circle averages under affine maps; AGENT_GUIDE cost
rule), on top of RegClosure / WedgeMeasCoord; the continuum limit itself is PAIR-AFF
(Duplantier–Sheffield 2011, §3.1, Prop. 3.1).
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace QuantumZipper
namespace S5
namespace FieldLaw
namespace Raw

open PairLim (aff continuous_aff measurable_aff)

variable {S : FieldSample} {G : ℂ × ℝ → ℝ} {x₀ : FieldSample} {t b c δ₀ r₀ : ℝ}

/-- Raw representation of `S` through `G` on `{Im > δ₀}` at radii `< r₀`, with affine
parameters `(t, b)` and additive constant `c`. -/
def RawRep (S : FieldSample) (G : ℂ × ℝ → ℝ) (t b c δ₀ r₀ : ℝ) : Prop :=
  ∀ w : ℂ, δ₀ < w.im → ∀ r : ℝ, 0 < r → r < r₀ →
    S (foldedCircle w r) = G (aff t b w, b * r) + c

theorem im_aff (t b : ℝ) (w : ℂ) : (aff t b w).im = b * w.im := by
  simp [aff]

theorem aff_mem_Hbar {t b : ℝ} (hb : 0 ≤ b) {w : ℂ} (hw : 0 ≤ w.im) : aff t b w ∈ Hbar := by
  show 0 ≤ (aff t b w).im
  rw [im_aff]; exact mul_nonneg hb hw

theorem tendsto_mul_radius {b : ℝ} (hb : 0 < b) :
    Tendsto (fun k => b * radius k) atTop (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun k => mul_pos hb (radius_pos k)⟩
  simpa using ((RegClosure.tendsto_radius_nhdsGT.mono_right nhdsWithin_le_nhds).const_mul b)

theorem integrable_of_continuousOn_compact {ν : Measure ℂ} [IsFiniteMeasure ν] {K : Set ℂ}
    (hK : IsCompact K) (hνK : ∀ᵐ u ∂ν, u ∈ K) {f : ℂ → ℝ} (hf : ContinuousOn f K) :
    Integrable f ν := by
  have h := hf.integrableOn_compact hK (μ := ν)
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hνK] at h

theorem continuousOn_slice_aff (hG : ContinuousOn G (Hbar ×ˢ Ioi 0)) (t : ℝ) {b : ℝ}
    (hb : 0 ≤ b) {s : ℝ} (hs : 0 < s) : ContinuousOn (fun u => G (aff t b u, s)) Hbar :=
  hG.comp ((continuous_aff t b).continuousOn.prodMk continuousOn_const) fun _ hu =>
    ⟨aff_mem_Hbar hb hu, hs⟩

/-- Folded circles under the affine map `u ↦ t + b u`. -/
theorem integral_fc_aff {g : ℂ → ℝ} (hg : ContinuousOn g Hbar) (t : ℝ) {b : ℝ} (hb : 0 < b)
    (w : ℂ) (r : ℝ) :
    ∫ u, g (aff t b u) ∂foldedCircle w r = ∫ v, g v ∂foldedCircle (aff t b w) (b * r) := by
  have hg1 : ContinuousOn (fun v : ℂ => g (v + t)) Hbar :=
    hg.comp (continuous_id.add continuous_const).continuousOn fun u (hu : 0 ≤ u.im) =>
      show 0 ≤ (u + t).im by simpa using hu
  have e1 : (fun u => g (aff t b u)) = fun u => g ((b : ℂ) * u + t) := by
    funext u; congr 1; unfold aff; ring
  have e2 : aff t b w = (b : ℂ) * w + t := by unfold aff; ring
  rw [e1, RegClosure.integral_fc_comp_mul hg1 w r hb, RegClosure.integral_fc_comp_add_real hg, e2]

/-! ## Regularized values of a raw-represented sample -/

theorem RawRep.avgReg_eq (h : RawRep S G t b c δ₀ r₀) (hG : ContinuousOn G (Hbar ×ˢ Ioi 0))
    (hb : 0 < b) (hδ₀ : 0 ≤ δ₀) {k : ℕ} (hk : radius k < r₀) {u : ℂ} (hu : δ₀ < u.im) :
    avgReg S k u = G (aff t b u, b * radius k) + c := by
  have hopen : IsOpen {v : ℂ | δ₀ < v.im} := isOpen_lt continuous_const Complex.continuous_im
  have hev : ∀ᶠ n : ℕ in atTop, δ₀ < (dyadicRoundC n u).im :=
    (RegClosure.tendsto_dyadicRoundC u).eventually (hopen.mem_nhds hu)
  have hmem : (aff t b u, b * radius k) ∈ Hbar ×ˢ Ioi (0 : ℝ) :=
    ⟨aff_mem_Hbar hb.le (hδ₀.trans hu.le), mul_pos hb (radius_pos k)⟩
  have hc : Tendsto (fun n : ℕ => G (aff t b (dyadicRoundC n u), b * radius k) + c) atTop
      (𝓝 (G (aff t b u, b * radius k) + c)) := by
    refine Tendsto.add_const c ?_
    refine (hG _ hmem).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩)
    · exact (((continuous_aff t b).tendsto u).comp
        (RegClosure.tendsto_dyadicRoundC u)).prodMk_nhds tendsto_const_nhds
    · filter_upwards [hev] with n hn
      exact ⟨aff_mem_Hbar hb.le (hδ₀.trans hn.le), mul_pos hb (radius_pos k)⟩
  unfold avgReg
  refine (hc.congr' ?_).limUnder_eq
  filter_upwards [hev] with n hn
  exact (h _ hn _ (radius_pos k) hk).symm

theorem eventually_radius_lt {r₀ : ℝ} (hr₀ : 0 < r₀) : ∀ᶠ k : ℕ in atTop, radius k < r₀ :=
  (tendsto_nhds_of_tendsto_nhdsWithin RegClosure.tendsto_radius_nhdsGT).eventually_lt_const hr₀

theorem RawRep.evalReg_fc (h : RawRep S G t b c δ₀ r₀) (hG : IsRegularWith x₀ G)
    (hb : 0 < b) (hδ₀ : 0 ≤ δ₀) (hr₀ : 0 < r₀) {w : ℂ} {r : ℝ} (hr : 0 < r)
    (hw : δ₀ + r < w.im) :
    evalReg S (foldedCircle w r) = G (aff t b w, b * r) + c := by
  have hwH : w ∈ Hbar := show 0 ≤ w.im by linarith
  have hae : ∀ᵐ u ∂foldedCircle w r, δ₀ < u.im := by
    filter_upwards [LocalRule.ae_fc_mem_closedBall hwH hr] with u hu
    have h1 : |(u - w).im| ≤ ‖u - w‖ := Complex.abs_im_le_norm _
    rw [Metric.mem_closedBall, dist_eq_norm] at hu
    rw [Complex.sub_im] at h1
    linarith [neg_abs_le (u.im - w.im)]
  have e : ∀ᶠ k : ℕ in atTop, ∫ u, avgReg S k u ∂foldedCircle w r =
      ∫ v, G (v, b * radius k) ∂foldedCircle (aff t b w) (b * r) + c := by
    filter_upwards [eventually_radius_lt hr₀] with k hk
    have hs : 0 < b * radius k := mul_pos hb (radius_pos k)
    rw [integral_congr_ae (hae.mono fun u hu => h.avgReg_eq hG.1 hb hδ₀ hk hu),
      integral_add (RegClosure.integrable_fc (continuousOn_slice_aff hG.1 t hb.le hs) w hr.le)
        (integrable_const c), integral_const, probReal_univ, one_smul,
      integral_fc_aff (g := fun v => G (v, b * radius k))
        (hG.1.comp (continuousOn_id.prodMk continuousOn_const) fun v hv => ⟨hv, hs⟩) t hb w r]
  have hp : (aff t b w, b * r) ∈ Hbar ×ˢ Ioi (0 : ℝ) :=
    ⟨aff_mem_Hbar hb.le hwH, mul_pos hb hr⟩
  have hlim := ((hG.2.2.tendsto_at hp).comp (tendsto_mul_radius hb)).add_const c
  unfold evalReg
  exact (hlim.congr' (e.mono fun k hk => hk.symm)).limUnder_eq

theorem RawRep.evalReg_eq (h : RawRep S G t b c δ₀ r₀) (hG : ContinuousOn G (Hbar ×ˢ Ioi 0))
    (hb : 0 < b) (hδ₀ : 0 ≤ δ₀) (hr₀ : 0 < r₀) {ν : Measure ℂ} [IsFiniteMeasure ν] {K : Set ℂ}
    (hK : IsCompact K) (hKδ : ∀ u ∈ K, δ₀ < u.im) (hνK : ∀ᵐ u ∂ν, u ∈ K) {L : ℝ}
    (hL : Tendsto (fun s => ∫ u, G (aff t b u, s) ∂ν) (𝓝[>] 0) (𝓝 L)) :
    evalReg S ν = L + c * ν.real univ := by
  have hKH : ∀ u ∈ K, u ∈ Hbar := fun u hu => show 0 ≤ u.im from hδ₀.trans (hKδ u hu).le
  have e : ∀ᶠ k : ℕ in atTop, ∫ u, avgReg S k u ∂ν =
      ∫ u, G (aff t b u, b * radius k) ∂ν + c * ν.real univ := by
    filter_upwards [eventually_radius_lt hr₀] with k hk
    have hs : 0 < b * radius k := mul_pos hb (radius_pos k)
    rw [integral_congr_ae (hνK.mono fun u hu => h.avgReg_eq hG hb hδ₀ hk (hKδ u hu)),
      integral_add (integrable_of_continuousOn_compact hK hνK
        ((continuousOn_slice_aff hG t hb.le hs).mono hKH)) (integrable_const c),
      integral_const, smul_eq_mul]
    ring
  unfold evalReg
  exact (((hL.comp (tendsto_mul_radius hb)).add_const _).congr'
    (e.mono fun k hk => hk.symm)).limUnder_eq

/-! ## Stability under real translations and dilations -/

theorem RawRep.translateRep (h : RawRep S G t b c δ₀ r₀) (hG : IsRegularWith x₀ G) (hb : 0 < b)
    (hδ₀ : 0 ≤ δ₀) (hr₀ : 0 < r₀) (y : ℝ) :
    RawRep (translate S y) G (t + b * y) b c (δ₀ + r₀) r₀ := by
  intro w hw r hr hrr
  show evalReg S ((foldedCircle w r).map (· + (y : ℂ))) = _
  rw [IndepParams.fc_map_add_real, h.evalReg_fc hG hb hδ₀ hr₀ hr (by simp; linarith),
    show aff t b (w + y) = aff (t + b * y) b w by simp only [aff]; push_cast; ring]

theorem integral_log_deriv_mul {a : ℝ} (ha : 0 < a) (μ : Measure ℂ) :
    ∫ z, Real.log ‖deriv (fun v : ℂ => (a : ℂ) * v) z‖ ∂μ = μ.real univ * Real.log a := by
  simp only [WedgeMeas.deriv_mul_left', Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha,
    integral_const, smul_eq_mul]

theorem rescale_apply (S : FieldSample) (Q : ℝ) {a : ℝ} (ha : 0 < a) (μ : Measure ℂ) :
    rescale S Q a μ = evalReg S (μ.map fun z => (a : ℂ) * z) + Q * (μ.real univ * Real.log a) := by
  show evalReg S (μ.map fun z => (a : ℂ) * z) +
    Q * ∫ z, Real.log ‖deriv (fun v : ℂ => (a : ℂ) * v) z‖ ∂μ = _
  rw [integral_log_deriv_mul ha]

theorem RawRep.rescaleRep (h : RawRep S G t b c δ₀ r₀) (hG : IsRegularWith x₀ G) (hb : 0 < b)
    (hδ₀ : 0 ≤ δ₀) (hr₀ : 0 < r₀) (Q : ℝ) {a : ℝ} (ha : 0 < a) :
    RawRep (rescale S Q a) G t (b * a) (c + Q * Real.log a) ((δ₀ + r₀) / a) (r₀ / a) := by
  intro w hw r hr hrr
  have h1 : δ₀ + r₀ < a * w.im := by
    have := (div_lt_iff₀ ha).1 hw; linarith [mul_comm w.im a]
  have h2 : a * r < r₀ := by
    have := (lt_div_iff₀ ha).1 hrr; linarith [mul_comm r a]
  have hw' : δ₀ + a * r < ((a : ℂ) * w).im := by simp; linarith
  rw [rescale_apply S Q ha, WedgeTK.fc_map_mul w r ha, probReal_univ, one_mul,
    h.evalReg_fc hG hb hδ₀ hr₀ (mul_pos ha hr) hw',
    show aff t b ((a : ℂ) * w) = aff t (b * a) w by simp only [aff]; push_cast; ring,
    show b * (a * r) = b * a * r by ring]
  ring

/-! ## Raw pairing = regularized pairing for rescaled fields -/

/-- **KEY.** For `S` raw-represented through a regular witness `G`, and `η` finite with compact
support in `{Im > (δ₀ + r₀)/a}`, if `s ↦ ∫ G (t + b a u, s) dη(u)` has a limit as `s → 0⁺`, then the
raw pairing of `rescale S Q a` with `η` equals its regularized pairing. -/
theorem RawRep.rescale_apply_eq (h : RawRep S G t b c δ₀ r₀) (hG : IsRegularWith x₀ G)
    (hb : 0 < b) (hδ₀ : 0 ≤ δ₀) (hr₀ : 0 < r₀) (Q : ℝ) {a : ℝ} (ha : 0 < a)
    {η : Measure ℂ} [IsFiniteMeasure η] {K : Set ℂ} (hK : IsCompact K)
    (hKδ : ∀ u ∈ K, (δ₀ + r₀) / a < u.im) (hηK : ∀ᵐ u ∂η, u ∈ K) {L : ℝ}
    (hL : Tendsto (fun s => ∫ u, G (aff t (b * a) u, s) ∂η) (𝓝[>] 0) (𝓝 L)) :
    rescale S Q a η = evalReg (rescale S Q a) η := by
  have hR := h.rescaleRep hG hb hδ₀ hr₀ Q ha
  have hδ₀' : 0 ≤ (δ₀ + r₀) / a := div_nonneg (by linarith) ha.le
  rw [hR.evalReg_eq hG.1 (mul_pos hb ha) hδ₀' (div_pos hr₀ ha) hK hKδ hηK hL, rescale_apply S Q ha]
  set m : ℂ → ℂ := fun z => (a : ℂ) * z with hmdef
  have hmc : Continuous m := continuous_const.mul continuous_id
  have hm : Measurable m := hmc.measurable
  have hK' : IsCompact (m '' K) := hK.image hmc
  have hK'δ : ∀ u ∈ m '' K, δ₀ < u.im := by
    rintro _ ⟨v, hv, rfl⟩
    have := (div_lt_iff₀ ha).1 (hKδ v hv)
    simp only [hmdef, Complex.im_ofReal_mul]
    linarith [mul_comm v.im a]
  have hK'H : ∀ u ∈ m '' K, u ∈ Hbar := fun u hu => show 0 ≤ u.im from hδ₀.trans (hK'δ u hu).le
  have hνK : ∀ᵐ u ∂η.map m, u ∈ m '' K :=
    (ae_map_iff hm.aemeasurable hK'.isClosed.measurableSet).2
      (hηK.mono fun v hv => mem_image_of_mem m hv)
  have hL' : Tendsto (fun s => ∫ u, G (aff t b u, s) ∂η.map m) (𝓝[>] 0) (𝓝 L) := by
    refine hL.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
    rw [integral_map hm.aemeasurable (integrable_of_continuousOn_compact hK' hνK
      ((continuousOn_slice_aff hG.1 t hb.le hs).mono hK'H)).aestronglyMeasurable]
    congr 1
    funext u
    rw [show aff t b (m u) = aff t (b * a) u by simp only [aff, hmdef]; push_cast; ring]
  have hmass : (η.map m).real univ = η.real univ := by
    simp [measureReal_def, Measure.map_apply hm MeasurableSet.univ]
  rw [h.evalReg_eq hG.1 hb hδ₀ hr₀ hK' hK'δ hνK hL', hmass]
  ring

/-! ## The wedge field -/

/-- **Regular away from `0`.** The wedge field is raw-represented, on `{Im > ρ₀}` at radii
`< ρ₀/2`, by the regular witness of `x + ofFun (gT F A Q ρ₀)` (radial profile truncated at
modulus `ρ₀/4`). -/
theorem rawRep_wedgeField {x : FieldSample} {F : ℂ × ℝ → ℝ} {A : ℝ → ℝ}
    (hG : WedgeTK.GoodRad x F) (hA : Continuous A) (Q : ℝ) {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) :
    RawRep (wedgeField (lateralPart x) A Q)
      (fun q => F q + ∫ v, WedgeMeasCoord.gT F A Q ρ₀ v ∂foldedCircle q.1 q.2) 0 1 0 ρ₀
      (ρ₀ / 2) := by
  intro w hw r hr hrr
  have hwH : w ∈ Hbar := show 0 ≤ w.im by linarith
  have him : w.im ≤ ‖w‖ := (le_abs_self _).trans (Complex.abs_im_le_norm w)
  have hne : ‖w‖ ≠ r := by intro h; linarith
  rw [WedgeCan.wedgeField_eq_evalReg_add_ofFun
      (WedgeCan.integrable_radAvgReg_foldedCircle hG hwH hr hne)
      (WedgeCan.integrable_logProfile_foldedCircle Q w r)
      (WedgeCan.integrable_Alog_foldedCircle hA hwH hr hne),
    hG.1.evalReg_fc_of_mem hwH hr,
    WedgeMeasCoord.integral_fc_profile_eq hG hρ₀ hr (by linarith)]
  simp [aff]

/-- The regular witness used in `rawRep_wedgeField`. -/
theorem isRegularWith_wedgeWitness {x : FieldSample} {F : ℂ × ℝ → ℝ} {A : ℝ → ℝ}
    (hG : WedgeTK.GoodRad x F) (hA : Continuous A) (Q : ℝ) {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) :
    IsRegularWith (x + ofFun (WedgeMeasCoord.gT F A Q ρ₀))
      (fun q => F q + ∫ v, WedgeMeasCoord.gT F A Q ρ₀ v ∂foldedCircle q.1 q.2) :=
  GoodSample.gs_add_ofFun hG.1 (WedgeMeasCoord.continuous_gT hG.1.1 hA hρ₀).continuousOn

/-! ## Item (i): the deterministic smoothing limit -/

theorem tendsto_integral_smooth_aff {g : ℂ → ℝ} (hg : Continuous g) {η : Measure ℂ}
    [IsFiniteMeasure η] {K : Set ℂ} (hK : IsCompact K) (hKH : ∀ u ∈ K, u ∈ Hbar)
    (hηK : ∀ᵐ u ∂η, u ∈ K) (t : ℝ) {b : ℝ} (hb : 0 < b) :
    Tendsto (fun s => ∫ u, (∫ v, g v ∂foldedCircle (aff t b u) s) ∂η) (𝓝[>] 0)
      (𝓝 (∫ u, g (aff t b u) ∂η)) := by
  have hΦ : Continuous fun q : ℂ × ℝ => ∫ v, g v ∂foldedCircle q.1 q.2 :=
    continuousOn_univ.1 (GoodSample.gs_continuousOn_integral_fc_fun hg.continuousOn)
  set f : ℂ × ℝ → ℝ := fun p => ∫ v, g v ∂foldedCircle (aff t b p.1) p.2 with hfdef
  have hf : Continuous f :=
    hΦ.comp (((continuous_aff t b).comp continuous_fst).prodMk continuous_snd)
  obtain ⟨C, hC⟩ := (hK.prod (isCompact_Icc (a := (0 : ℝ)) (b := 1))).exists_bound_of_continuousOn
    hf.continuousOn
  have hlim0 : ∀ u ∈ K, f (u, 0) = g (aff t b u) := by
    intro u hu
    simp only [hfdef]
    rw [RegSample.fc_zero, integral_dirac,
      CircleFubini.foldH_of_mem' (aff_mem_Hbar hb.le (hKH u hu))]
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => C) ?_ ?_ (integrable_const C) ?_
  · exact Eventually.of_forall fun s =>
      (hf.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with s hs
    filter_upwards [hηK] with u hu
    exact hC (u, s) ⟨hu, hs.1.le, hs.2.le⟩
  · filter_upwards [hηK] with u hu
    rw [← hlim0 u hu]
    exact ((hf.comp (continuous_const.prodMk continuous_id)).tendsto 0).mono_left
      nhdsWithin_le_nhds

end Raw
end FieldLaw
end S5
end QuantumZipper
