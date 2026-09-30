import QuantumZipper.Proofs.Zipper.WedgeAddConstPos
import QuantumZipper.Proofs.LQG.WedgeCRegCont

/-!
# WEDGE-ADDCONST (5): deterministic identities for the re-embedding node

Sheffield, arXiv:1012.4797, §1.6 (the canonical description (1.8) does not depend on the
embedding: `h ↦ h(a·) + Q log a` changes nothing after normalizing). For a regular sample `y`
(witness `G`), `s > 0`, `b > 0`:

* `avgReg_addConst_rescale`: `rescale y Q s + k` and `rescale (y + k) Q s` have the same raw
  folded-circle values, hence the same regularized averages;
* `rescale_rescale_fc`: `rescale (rescale y Q s) Q b` and `rescale y Q (s b)` agree on every folded
  circle;
* `rescale_rescale_eq_of_lim`: they agree on a finite measure `ν` carried by a compact subset of
  `ℍ̄`, provided the pairings `r ↦ ∫ G((s b) u, r) dν(u)` have a continuum limit as `r → 0⁺`
  (the regularized pairings on the two sides are limits along the radii `s·2^{-k}` and `2^{-k}`);
* `ae_contPair_plain`: the continuum limits hold a.s. for the wedge field, for each test function,
  for all dilations at once (the non-reflected form of `WedgeCReg.ae_contPair_wedge`, same proof:
  PAIR-AFF, Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.1).

Own elementary arguments, modelled on `F1.B4d.reflectH_rescale_eq_of_lim`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace QuantumZipper
namespace F1

open PairLim WedgeCReg

variable {y : FieldSample} {G : ℂ × ℝ → ℝ}

/-- Raw values: `rescale y Q s + k` and `rescale (y + k) Q s` agree on every folded circle. -/
theorem addConst_rescale_fc (hG : IsRegularWith y G) (Q k : ℝ) {s : ℝ} (hs : 0 < s) (d : ℂ)
    {r : ℝ} (hr : 0 < r) :
    addConst (rescale y Q s) k (foldedCircle d r) =
      rescale (addConst y k) Q s (foldedCircle d r) := by
  rw [RegClosure.rescale_fc_eq (hG.addConst' k) Q hs d hr]
  simp only [addConst, measure_univ, ENNReal.toReal_one, mul_one]
  rw [RegClosure.rescale_fc_eq hG Q hs d hr]
  ring

theorem avgReg_addConst_rescale (hG : IsRegularWith y G) (Q k : ℝ) {s : ℝ} (hs : 0 < s) :
    avgReg (addConst (rescale y Q s) k) = avgReg (rescale (addConst y k) Q s) := by
  funext j z
  unfold avgReg
  congr 1
  funext n
  exact addConst_rescale_fc hG Q k hs _ (radius_pos j)

theorem cast_mul_mul (s b : ℝ) (u : ℂ) : (s : ℂ) * ((b : ℂ) * u) = ((s * b : ℝ) : ℂ) * u := by
  push_cast; ring

/-- Circles: `rescale (rescale y Q s) Q b = rescale y Q (s b)`. -/
theorem rescale_rescale_fc (hG : IsRegularWith y G) (Q : ℝ) {s b : ℝ} (hs : 0 < s)
    (hb : 0 < b) (d : ℂ) {r : ℝ} (hr : 0 < r) :
    rescale (rescale y Q s) Q b (foldedCircle d r) = rescale y Q (s * b) (foldedCircle d r) := by
  rw [RegClosure.rescale_fc_eq (hG.rescale' Q hs) Q hb d hr,
    RegClosure.rescale_fc_eq hG Q (mul_pos hs hb) d hr]
  simp only
  rw [← RegClosure.foldH_mul_pos _ hs, cast_mul_mul, mul_assoc, Real.log_mul hs.ne' hb.ne']
  ring

theorem integrable_witness_mul (hG : IsRegularWith y G) {c : ℝ} (hc : 0 < c) {r : ℝ}
    (hr : 0 < r) {ν : Measure ℂ} [IsFiniteMeasure ν] {K : Set ℂ} (hK : IsCompact K)
    (hKH : K ⊆ Hbar) (hνK : ∀ᵐ u ∂ν, u ∈ K) :
    Integrable (fun u => G ((c : ℂ) * u, r)) ν := by
  have hcont : ContinuousOn (fun u => G ((c : ℂ) * u, r)) Hbar :=
    hG.1.comp (by fun_prop) (fun u hu => ⟨RegClosure.mapsTo_mul_pos hc hu, hr⟩)
  have := (hcont.mono hKH).integrableOn_compact (μ := ν) hK
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hνK] at this

theorem integral_log_deriv_mul_const {c : ℝ} (hc : 0 < c) (ν : Measure ℂ) :
    ∫ z, Real.log ‖deriv (fun w : ℂ => (c : ℂ) * w) z‖ ∂ν = Real.log c * ν.real univ := by
  have hd : ∀ z, Real.log ‖deriv (fun w : ℂ => (c : ℂ) * w) z‖ = Real.log c := fun z => by
    rw [WedgeMeas.deriv_mul_left', Complex.norm_real, Real.norm_of_nonneg hc.le]
  rw [integral_congr_ae (ae_of_all _ hd), integral_const, smul_eq_mul, mul_comm]

/-- Finite measures on a compact subset of `ℍ̄`, under a continuum limit. -/
theorem rescale_rescale_eq_of_lim (hG : IsRegularWith y G) (Q : ℝ) {s b : ℝ} (hs : 0 < s)
    (hb : 0 < b) (ν : Measure ℂ) [IsFiniteMeasure ν] {K : Set ℂ} (hK : IsCompact K)
    (hKH : K ⊆ Hbar) (hνK : ∀ᵐ u ∂ν, u ∈ K) {L : ℝ}
    (hlim : Tendsto (fun r => ∫ u, G (((s * b : ℝ) : ℂ) * u, r) ∂ν) (𝓝[>] 0) (𝓝 L)) :
    rescale (rescale y Q s) Q b ν = rescale y Q (s * b) ν := by
  have hνH : ∀ᵐ u ∂ν, u ∈ Hbar := hνK.mono fun u hu => hKH hu
  have hsb := mul_pos hs hb
  have hL : evalReg (rescale y Q s) (ν.map fun z => (b : ℂ) * z) =
      L + Q * Real.log s * ν.real univ := by
    refine (hG.rescale' Q hs).evalReg_map_eq (m := fun z => (b : ℂ) * z) (by fun_prop)
      (RegClosure.mapsTo_mul_pos hb) hνH
      (G := fun k => ∫ u, G (((s * b : ℝ) : ℂ) * u, s * radius k) ∂ν +
        Q * Real.log s * ν.real univ)
      (fun k => ?_) ((hlim.comp (F1.B4d.tendsto_mul_radius hs)).add_const _)
    show ∫ u, (G ((s : ℂ) * ((b : ℂ) * u), s * radius k) + Q * Real.log s) ∂ν = _
    simp only [cast_mul_mul]
    rw [integral_add (integrable_witness_mul hG hsb (mul_pos hs (radius_pos k)) hK hKH hνK)
      (integrable_const _), integral_const, smul_eq_mul, mul_comm (ν.real univ)]
  have hR : evalReg y (ν.map fun z => ((s * b : ℝ) : ℂ) * z) = L :=
    hG.evalReg_map_eq (m := fun z => ((s * b : ℝ) : ℂ) * z) (by fun_prop)
      (RegClosure.mapsTo_mul_pos hsb) hνH
      (G := fun k => ∫ u, G (((s * b : ℝ) : ℂ) * u, radius k) ∂ν) (fun k => rfl)
      (hlim.comp RegClosure.tendsto_radius_nhdsGT)
  show evalReg (rescale y Q s) (ν.map fun z => (b : ℂ) * z) +
      Q * ∫ z, Real.log ‖deriv (fun w : ℂ => (b : ℂ) * w) z‖ ∂ν =
    evalReg y (ν.map fun z => ((s * b : ℝ) : ℂ) * z) +
      Q * ∫ z, Real.log ‖deriv (fun w : ℂ => ((s * b : ℝ) : ℂ) * w) z‖ ∂ν
  rw [hL, hR, integral_log_deriv_mul_const hb, integral_log_deriv_mul_const hsb,
    Real.log_mul hs.ne' hb.ne']
  ring

/-! ## Continuum limits for the wedge field, non-reflected -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- **Continuum limits, per test function** (non-reflected form of
`WedgeCReg.ae_contPair_wedge`). -/
theorem ae_contPair_plain [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {A : ℝ → Ω → ℝ} (hA : ∀ᵐ ω ∂P, Continuous fun t => A t ω) (Q : ℝ) (ρ : TestFun H) :
    ∀ᵐ ω ∂P, ∀ b : ℝ, 0 < b → ∀ f ∈ ({ρ.1, -ρ.1} : Set (ℂ → ℝ)), ∃ L : ℝ,
      Tendsto (fun r => ∫ u, evalReg (wedgeField (lateralPart (X ω)) (fun t => A t ω) Q)
        (foldedCircle ((b : ℂ) * u) r)
          ∂(volume.withDensity fun z => ENNReal.ofReal (f z))) (𝓝[>] 0) (𝓝 L) := by
  obtain ⟨hs, hc, hH⟩ := ρ.2
  obtain ⟨M₁, R₁, δ₁, h₁⟩ := exists_setup_withDensity hs.continuous hc hH
  obtain ⟨M₂, R₂, δ₂, h₂⟩ := exists_setup_withDensity (g := fun z => -ρ.1 z) hs.continuous.neg
    hc.neg (by rw [show (fun z => -ρ.1 z) = -ρ.1 from rfl, tsupport_neg]; exact hH)
  obtain ⟨Gv, hGv⟩ := WedgeTK.exists_isRegVersion hX
  filter_upwards [hGv.ae_good, hA, ae_tendstoLocallyUniformlyOn_affPair hX h₁,
    ae_tendstoLocallyUniformlyOn_affPair hX h₂] with ω hg hcA hp1 hp2 b hb f hf
  rcases hf with rfl | hf
  · obtain ⟨L, hL⟩ := tendsto_wedge_aff hg hcA h₁ (fun t B hB =>
      ⟨_, hp1.2.tendsto_at (show (t, B) ∈ (univ : Set ℝ) ×ˢ Ioi (0 : ℝ) from ⟨trivial, hB⟩)⟩)
      hb (Q := Q)
    exact ⟨L, hL.congr fun r => by simp only [aff, Complex.ofReal_zero, zero_add]⟩
  · rw [Set.mem_singleton_iff] at hf
    subst hf
    obtain ⟨L, hL⟩ := tendsto_wedge_aff hg hcA h₂ (fun t B hB =>
      ⟨_, hp2.2.tendsto_at (show (t, B) ∈ (univ : Set ℝ) ×ˢ Ioi (0 : ℝ) from ⟨trivial, hB⟩)⟩)
      hb (Q := Q)
    exact ⟨L, hL.congr fun r => by simp only [aff, Complex.ofReal_zero, zero_add]; rfl⟩

/-! ## The area profile of `x + k` -/

open AreaProfile in
theorem hasAreaProfile_addConst {γ : ℝ} {x : FieldSample} (hg : IsLQGGood γ x)
    (hx : HasAreaProfile γ x) (c : ℝ) : HasAreaProfile γ (addConst x c) := by
  refine hasAreaProfile_smul_map_div (C := ENNReal.ofReal (Real.exp (γ * c)))
    (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne' ENNReal.ofReal_ne_top one_pos hx ?_
  rw [GoodSample.qAreaMeasure_addConst hg c]
  have e : (fun z : ℂ => z / ((1 : ℝ) : ℂ)) = id := by funext z; simp
  rw [e, Measure.map_id]

end F1
end QuantumZipper
