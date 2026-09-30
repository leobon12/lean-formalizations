import QuantumZipper.Proofs.RS.OnePointWeighted
import QuantumZipper.Proofs.RS.TraceMain
import QuantumZipper.Proofs.RS.TraceMeas
import QuantumZipper.Proofs.RS.GenerationBasic
import QuantumZipper.Proofs.RS.KoebeLoewnerTime
import QuantumZipper.Proofs.Thm11.NonSwallowing

/-!
# EXT-RS S1-2 and S1-4: from the conformal radius to the distance to the SLE trace

`blueprint/EXT_RS_BLUEPRINT.md` §5, nodes S1-2 and S1-4.

* **S1-2 (Koebe).** `koebe_logCR_le_dist`: if `z ∉ K_s` and the trace `η(s)` exists as the
  radial limit, then `c₀ Υ_s(z) ≤ dist(z, η(s))`, where `Υ_s(z) = Im g_s(z)/|g_s'(z)|`
  (`exp (fwdLogCR ..)`) and `c₀ = koebeCovConst = 1/48`. This is the Koebe one-quarter theorem
  in the half-plane form of Garnett–Marshall, *Harmonic Measure*, Thm I.4.3 / Cor I.4.4 (p. 19)
  and Pommerenke, *Boundary Behaviour of Conformal Maps*, Cor 1.4 (p. 9), applied to
  `f̂_s = g_s⁻¹` (EXT-CA K5a, `CA.Koebe.infDist_compl_image_ge`, non-sharp constant), together with
  TR5 (`η(s) ∈ K_s ∪ ℝ`). Cf. Lawler–Zhou, arXiv:1006.4936, (6); Lawler, *Conformally Invariant
  Processes*, Prop 4.36 (p. 90).
* **S1-4 (distance form, `ε ≤ (c₀/2) Im z`).** `prob_infDist_lt_small`: S1-3 (`prob_logCR_lt`,
  LZ Prop 2.3 upper bound) with `r = ε/c₀`, on the almost sure event where the trace exists (TR4)
  and `z` is never swallowed (DF-2, `κ ≤ 4`).
-/

noncomputable section

open Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace QuantumZipper.RS

open FwdClock

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}

/-- **S1-2 (Koebe), deterministic form.** `c₀ Υ_s(z) ≤ dist(z, η(s))` for `z ∈ H \ K_s`. -/
theorem koebe_logCR_le_dist {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {s : ℝ}
    (hs : 0 ≤ s)
    (hlim : Tendsto (fun y : ℝ => fwdMapInv W s (y * Complex.I)) (𝓝[>] 0) (𝓝 (trace W s)))
    {z : ℂ} (hz : z ∈ H \ fwdHull W s) :
    CA.Koebe.koebeCovConst * Real.exp (fwdLogCR W s z) ≤ dist z (trace W s) := by
  have hgz : fwdMap W s z ∈ H := FwdHolo.mapsTo_fwdMap hW hs hz
  have hfg : fwdMapInv W s (fwdMap W s z) = z := fwdMapInv_fwdMap hW hW0 hs hz
  have hg := FwdHolo.hasDerivAt_fwdMap hW hs hz
  have hf : HasDerivAt (fwdMapInv W s) (deriv (fwdMapInv W s) (fwdMap W s z)) (fwdMap W s z) :=
    (differentiableAt_fwdMapInv hW hW0 hs hgz).hasDerivAt
  have hopen : IsOpen (H \ fwdHull W s) := FwdHolo.isOpen_compl_fwdHull hW hs
  have hcomp : HasDerivAt (fwdMapInv W s ∘ fwdMap W s)
      (deriv (fwdMapInv W s) (fwdMap W s z) * Complex.exp (logDerivFwd W s z)) z := by
    exact hf.comp z hg
  have hid : HasDerivAt (fwdMapInv W s ∘ fwdMap W s) 1 z := by
    refine (hasDerivAt_id z).congr_of_eventuallyEq ?_
    filter_upwards [hopen.mem_nhds hz] with w hw
    exact fwdMapInv_fwdMap hW hW0 hs hw
  have hprod := hcomp.unique hid
  have hnorm : ‖deriv (fwdMapInv W s) (fwdMap W s z)‖ = Real.exp (-(logDerivFwd W s z).re) := by
    have h1 := congrArg norm hprod
    rw [norm_mul, Complex.norm_exp, norm_one] at h1
    rw [Real.exp_neg]; exact eq_inv_of_mul_eq_one_left h1
  have hK := CA.Koebe.infDist_compl_image_ge (differentiableOn_fwdMapInv hW hW0 hs)
    (injOn_fwdMapInv hW hW0 hs) (z := fwdMap W s z) hgz
  have himg : fwdMapInv W s '' {z : ℂ | 0 < z.im} = H \ fwdHull W s :=
    image_fwdMapInv_H hW hW0 hs
  rw [hfg, himg, hnorm] at hK
  have hexp : Real.exp (fwdLogCR W s z) = (fwdMap W s z).im * Real.exp (-(logDerivFwd W s z).re) := by
    rw [fwdLogCR, Real.exp_sub, Real.exp_log hgz, Real.exp_neg, div_eq_mul_inv]
  -- `η(s) ∉ H \ K_s` (TR5 and `K_s ⊆ H`)
  have hη : trace W s ∈ (H \ fwdHull W s)ᶜ := by
    rcases trace_mem_fwdHull_or_real hW hW0 hs hlim with h | h
    · exact fun h' => h'.2 h
    · intro h'; have := h'.1; simp only [H, mem_ofPred_eq] at this; linarith
  rw [hexp, ← mul_assoc]
  exact hK.trans (infDist_le_dist_of_mem hη)

/-- **DF-2, all integer times.** For `κ ∈ (0,4]` and fixed `z ∈ ℍ`, a.s. `z ∉ K_n` for every `n`. -/
theorem ae_forall_notMem_fwdHull [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) {z : ℂ} (hz : 0 < z.im) :
    ∀ᵐ ω ∂P, ∀ n : ℕ, z ∉ fwdHull (drive κ B ω) n := by
  obtain ⟨B', hB'm, hB'c, hB'eq⟩ := WedgeRes.exists_good_version hB
  set B'' : ℝ≥0 → Ω → ℝ := fun t ω => B' t ω - B' 0 ω with hB''
  have hB0 : ∀ᵐ ω ∂P, B 0 ω = 0 := hB.toIsPreBrownianReal.eval_zero_ae_eq_zero
  have hB''eq : ∀ᵐ ω ∂P, ∀ t, B'' t ω = B t ω := by
    filter_upwards [hB'eq, hB0] with ω h1 h2
    intro t
    simp only [hB'', h1, h2, sub_zero]
  have hB''pre : IsPreBrownianReal B'' P :=
    hB.toIsPreBrownianReal.congr fun t => hB''eq.mono fun ω h => (h t).symm
  have hB''m : ∀ t, Measurable (B'' t) := fun t =>
    (hB'm.comp measurable_prodMk_left).sub (hB'm.comp measurable_prodMk_left)
  have hB''c : ∀ ω, Continuous (B'' · ω) := fun ω => (hB'c ω).sub continuous_const
  rw [ae_all_iff]
  intro n
  have h0 := NonSwallow.prob_mem_fwdHull_eq_zero hB''pre hB''m hB''c hκ hκ4 hz (n : ℝ)
  have h1 : ∀ᵐ ω ∂P, ω ∉ {ω | z ∈ fwdHull (drive κ B'' ω) n} :=
    measure_eq_zero_iff_ae_notMem.1 h0
  filter_upwards [h1, hB''eq] with ω h1 hω
  have hdr : drive κ B'' ω = drive κ B ω := funext fun t => by simp only [drive, hω]
  simpa only [mem_ofPred_eq, hdr] using h1

/-- The Koebe constant of S1-4: `c₁ = c₀/2`. -/
def onePointC1 : ℝ := CA.Koebe.koebeCovConst / 2

theorem onePointC1_pos : 0 < onePointC1 := by
  unfold onePointC1; linarith [CA.Koebe.koebeCovConst_pos]

theorem onePointC1_le_half : onePointC1 ≤ 1 / 2 := by
  unfold onePointC1 CA.Koebe.koebeCovConst; norm_num

/-- **S1-4 (distance form for `ε ≤ c₁ Im z`).** The constant is explicit in the constant `C` of
S1-3, `C / c₀^{1−κ/8}`, so that it does not depend on the probability space. -/
theorem prob_infDist_lt_small [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ ≤ 4) {C : ℝ}
    (hC : ∀ z ∈ H, ∀ r : ℝ, 0 < r → r ≤ z.im / 2 →
      P {ω | ∃ t ≥ (0 : ℝ), z ∉ fwdHull (drive κ B ω) t ∧
        Real.exp (fwdLogCR (drive κ B ω) t z) < r}
      ≤ ENNReal.ofReal (C * (r / z.im) ^ (1 - κ / 8) * (z.im / ‖z‖) ^ (8 / κ - 1))) :
    ∀ z ∈ H, ∀ ε : ℝ, 0 < ε → ε ≤ onePointC1 * z.im →
      P {ω | infDist z (sleTrace κ B ω '' Ici 0) < ε}
        ≤ ENNReal.ofReal (C / CA.Koebe.koebeCovConst ^ (1 - κ / 8) * (ε / z.im) ^ (1 - κ / 8)
          * (z.im / ‖z‖) ^ (8 / κ - 1)) := by
  obtain ⟨δ, hδ, hgood⟩ := ae_sleTrace_good hB hκ (by linarith)
  set c := CA.Koebe.koebeCovConst with hc
  have hc0 : 0 < c := CA.Koebe.koebeCovConst_pos
  intro z hz ε hε hεz
  have hz' : 0 < z.im := hz
  have hr : 0 < ε / c := div_pos hε hc0
  have hrz : ε / c ≤ z.im / 2 := by
    rw [div_le_iff₀ hc0]; unfold onePointC1 at hεz; linarith
  have h := hC z hz (ε / c) hr hrz
  have heq : C * (ε / c / z.im) ^ (1 - κ / 8) * (z.im / ‖z‖) ^ (8 / κ - 1)
      = C / c ^ (1 - κ / 8) * (ε / z.im) ^ (1 - κ / 8) * (z.im / ‖z‖) ^ (8 / κ - 1) := by
    rw [show ε / c / z.im = (ε / z.im) / c by ring, Real.div_rpow (div_pos hε hz').le hc0.le]
    ring
  rw [heq] at h
  refine le_trans (measure_mono_ae ?_) h
  filter_upwards [hgood, ae_forall_notMem_fwdHull hB hκ hκ4 hz', hB.cont,
    hB.toIsPreBrownianReal.eval_zero_ae_eq_zero] with ω hω hns hcont h0
  intro hω'
  set W := drive κ B ω
  have hW : Continuous W := drive_continuous hcont
  have hW0 : W 0 = 0 := drive_zero h0
  have hne : (sleTrace κ B ω '' Ici 0).Nonempty := ⟨_, mem_image_of_mem _ (mem_Ici.2 le_rfl)⟩
  obtain ⟨q, ⟨s, hs, rfl⟩, hq⟩ := (infDist_lt_iff hne).1 hω'
  have hs0 : (0 : ℝ) ≤ s := hs
  obtain ⟨Cn, hCn⟩ := hω.2.2 ⌈s⌉₊
  have hlim : Tendsto (fun y : ℝ => fwdMapInv W s (y * Complex.I)) (𝓝[>] 0) (𝓝 (trace W s)) :=
    tendsto_fwdMapInv_of_rpow_bound hδ (hCn s ⟨hs0, Nat.le_ceil s⟩)
  have hzs : z ∈ H \ fwdHull W s :=
    ⟨hz, fun hmem => hns ⌈s⌉₊ (fwdHull_mono.1 (Nat.le_ceil s) hmem)⟩
  have hk := koebe_logCR_le_dist hW hW0 hs0 hlim hzs
  refine ⟨s, hs0, hzs.2, ?_⟩
  rw [lt_div_iff₀ hc0, mul_comm]
  exact lt_of_le_of_lt hk hq

end QuantumZipper.RS
