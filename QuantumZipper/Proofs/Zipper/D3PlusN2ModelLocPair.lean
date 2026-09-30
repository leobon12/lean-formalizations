import QuantumZipper.Proofs.Zipper.D3PlusN2ModelLocReg

/-!
# N2Z-MODELLOC reduced to continuum pairing limits of the free field

Task N2-MODELLOC.

* `exists_tendsto_pair_n2RegW` (deterministic): the continuum radius limits of the test pairings
  of the comparison witness `n2RegW = G + (circle averages of −H_ω∘retr + L/γ) + α circPot/2`
  exist as soon as they exist for `G`: the continuous part converges by continuity of parametric
  integrals (`continuous_parametric_integral_of_continuous`), the logarithmic part is eventually
  constant (the test function lives at positive distance from `0`).
* `n2ZModelReg_of_contPair : N2ZContPairGFFStmt → N2ZModelRegStmt` and
  **`n2ZModelLoc_of_contPair : N2ZContPairGFFStmt → N2ZModelLocStmt`**.

The remaining node `N2ZContPairGFFStmt`: for a free field `X` there is a regular version `G`
(`WedgeTK.IsRegVersion`) such that almost surely, for **all** scales `c > 0` and **all** test
functions `ρ ∈ TestFun H` simultaneously, `t ↦ ∫ G(c u, t) ρ^±(u) du` has a limit as `t → 0⁺`.
Mathematically this holds because the free field is a.s. a distribution whose circle averages are
`G` (for a distribution `h`, `∫ h_t(cu) ρ(u) du = (h, ρ_c * σ_t) → (h, ρ_c)` for every smooth `ρ`);
per test function it is `F1.ae_contPair_plain`-type (`ae_tendstoLocallyUniformlyOn_affPair`).

Own elementary arguments.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace QuantumZipper
namespace D3Plus

/-- **Node N2Z-CONTPAIR** (free field, all test functions at once). -/
def N2ZContPairGFFStmt : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → FieldSample), IsFreeGFFModConstH X P →
    ∃ G : Ω → ℂ × ℝ → ℝ, WedgeTK.IsRegVersion X P G ∧
      ∀ᵐ ω ∂P, ∀ c : ℝ, 0 < c → ∀ ρ : TestFun H, ∀ f ∈ ({ρ.1, -ρ.1} : Set (ℂ → ℝ)),
        ∃ L : ℝ, Tendsto (fun t => ∫ u, G ω ((c : ℂ) * u, t)
          ∂(volume.withDensity fun z => ENNReal.ofReal (f z))) (𝓝[>] 0) (𝓝 L)

variable {γ α L r : ℝ} {Hω : ℂ → ℝ}

/-- **Continuum pairing limits of the comparison witness.** -/
theorem exists_tendsto_pair_n2RegW {G : ℂ × ℝ → ℝ} (hGc : ContinuousOn G (Hbar ×ˢ Ioi 0))
    (hr : 0 < r) (hH : ContinuousOn Hω (Metric.ball (0 : ℂ) r ∩ Hbar)) {c : ℝ} (hc : 0 < c)
    {f : ℂ → ℝ} (hfc : Continuous f) (hfs : HasCompactSupport f) (hfH : tsupport f ⊆ H)
    (hG : ∃ L₀ : ℝ, Tendsto (fun t => ∫ u, G ((c : ℂ) * u, t)
      ∂(volume.withDensity fun z => ENNReal.ofReal (f z))) (𝓝[>] 0) (𝓝 L₀)) :
    ∃ L₀ : ℝ, Tendsto (fun t => ∫ u, n2RegW γ α L r Hω G ((c : ℂ) * u, t)
      ∂(volume.withDensity fun z => ENNReal.ofReal (f z))) (𝓝[>] 0) (𝓝 L₀) := by
  obtain ⟨hfin, hae⟩ := F1.B4d.withDensity_facts hfc hfs
  set ν := volume.withDensity fun z => ENNReal.ofReal (f z) with hν
  set K := tsupport f with hKdef
  have hK : IsCompact K := hfs
  have hKH : K ⊆ Hbar := hfH.trans F1.B4d.H_subset_Hbar
  have hint : ∀ {g : ℂ → ℝ}, ContinuousOn g K → Integrable g ν := fun hg => by
    rw [← Measure.restrict_eq_self_of_ae_mem hae]; exact hg.integrableOn_compact hK
  obtain ⟨ε, hε, hεK⟩ : ∃ ε > 0, ∀ u ∈ K, ε ≤ ‖u‖ := by
    have h0 : (0 : ℂ) ∈ Kᶜ := fun h => by have := hfH h; simp [H] at this
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hK.isClosed.isOpen_compl 0 h0
    refine ⟨ε, hε, fun u hu => not_lt.1 fun hlt => hball ?_ hu⟩
    rw [Metric.mem_ball, dist_zero_right]; exact hlt
  have hmulc : Continuous fun u : ℂ => (c : ℂ) * u := continuous_const.mul continuous_id
  -- the continuous part
  have hΦ : Continuous fun q : ℂ × ℝ => ∫ v, (-n2Hext r Hω v + L / γ) ∂foldedCircle q.1 q.2 :=
    continuousOn_univ.1 (RegClosure.continuousOn_integral_fc_fun
      ((continuous_n2Hext hr hH).neg.add continuous_const).continuousOn)
  have hΦc : Continuous fun p : ℝ × ℂ =>
      ∫ v, (-n2Hext r Hω v + L / γ) ∂foldedCircle ((c : ℂ) * p.2) p.1 :=
    hΦ.comp (continuous_const.mul continuous_snd |>.prodMk continuous_fst)
  have hΦlim : Tendsto (fun t => ∫ u, (∫ v, (-n2Hext r Hω v + L / γ)
      ∂foldedCircle ((c : ℂ) * u) t) ∂ν) (𝓝[>] 0)
      (𝓝 (∫ u, (∫ v, (-n2Hext r Hω v + L / γ) ∂foldedCircle ((c : ℂ) * u) 0) ∂ν)) := by
    have hcont := continuous_parametric_integral_of_continuous (μ := ν) (s := K)
      (f := fun t u => ∫ v, (-n2Hext r Hω v + L / γ) ∂foldedCircle ((c : ℂ) * u) t) hΦc hK
    rw [Measure.restrict_eq_self_of_ae_mem hae] at hcont
    exact (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  have hΦi : ∀ t : ℝ, Integrable (fun u => ∫ v, (-n2Hext r Hω v + L / γ)
      ∂foldedCircle ((c : ℂ) * u) t) ν := fun t =>
    hint (hΦ.comp (hmulc.prodMk continuous_const)).continuousOn
  -- the `G` part
  have hGi : ∀ t : ℝ, 0 < t → Integrable (fun u => G ((c : ℂ) * u, t)) ν := fun t ht =>
    hint (hGc.comp (hmulc.prodMk continuous_const).continuousOn
      fun u hu => ⟨RegClosure.mapsTo_mul_pos hc (hKH hu), ht⟩)
  -- the logarithmic part
  have heq : ∀ t : ℝ, t < c * ε → ∀ u ∈ K,
      α * (CircleCont.circPot t ((c : ℂ) * u) 0 / 2) = α * -Real.log ‖(c : ℂ) * u‖ := by
    intro t htc u hu
    have hn : t < ‖(c : ℂ) * u‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc.le]
      nlinarith [hεK u hu]
    simp only [CircleCont.circPot, map_zero, sub_zero, max_eq_right hn.le]
    ring
  have hlogc : ContinuousOn (fun u : ℂ => α * -Real.log ‖(c : ℂ) * u‖) K := by
    refine continuousOn_const.mul (ContinuousOn.neg ?_)
    refine Real.continuousOn_log.comp (continuous_norm.comp hmulc).continuousOn fun u hu => ?_
    have := hεK u hu
    show ‖(c : ℂ) * u‖ ∈ ({0}ᶜ : Set ℝ)
    rw [mem_compl_singleton_iff, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc.le]
    exact (mul_pos hc (hε.trans_le this)).ne'
  have hLi : ∀ t : ℝ, t < c * ε →
      Integrable (fun u => α * (CircleCont.circPot t ((c : ℂ) * u) 0 / 2)) ν := fun t htc =>
    (hint hlogc).congr (hae.mono fun u hu => (heq t htc u hu).symm)
  have hlog : ∀ t : ℝ, t < c * ε →
      ∫ u, α * (CircleCont.circPot t ((c : ℂ) * u) 0 / 2) ∂ν =
        ∫ u, α * -Real.log ‖(c : ℂ) * u‖ ∂ν := fun t htc =>
    integral_congr_ae (hae.mono fun u hu => heq t htc u hu)
  -- assembly
  obtain ⟨L₁, hL₁⟩ := hG
  refine ⟨L₁ + ∫ u, (∫ v, (-n2Hext r Hω v + L / γ) ∂foldedCircle ((c : ℂ) * u) 0) ∂ν +
    ∫ u, α * -Real.log ‖(c : ℂ) * u‖ ∂ν, ?_⟩
  have hsum := (hL₁.add hΦlim).add
    (tendsto_const_nhds (x := ∫ u, α * -Real.log ‖(c : ℂ) * u‖ ∂ν) (f := 𝓝[>] (0 : ℝ)))
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioo 0 (c * ε) := Ioo_mem_nhdsGT (by positivity)
  refine hsum.congr' (hev.mono fun t ht => ?_)
  simp only [n2RegW]
  have hGΦ : Integrable (fun u => G ((c : ℂ) * u, t) + ∫ v, (-n2Hext r Hω v + L / γ)
      ∂foldedCircle ((c : ℂ) * u) t) ν := (hGi t ht.1).add (hΦi t)
  rw [integral_add hGΦ (hLi t ht.2),
    integral_add (hGi t ht.1) (hΦi t), hlog t ht.2]

/-- **N2Z-MODELREG from the free-field continuum pairing node.** -/
theorem n2ZModelReg_of_contPair (hCP : N2ZContPairGFFStmt) : N2ZModelRegStmt := by
  intro γ α r Ω _ P _ X hγ hγ2 hα hr hX
  obtain ⟨G, hGv, hGlim⟩ := hCP P X hX
  filter_upwards [d3PlusN2HarmPart_holds r P X hr hX, AreaOffsets.ae_isLQGGood hX hγ hγ2,
    hGv.reg, hGlim] with ω hHP hg hreg hlim L
  obtain ⟨Hω, hH, -, hdec⟩ := hHP
  refine ⟨isLocallyGoodOn_n2Model hH hdec hg, n2Reg γ α L r Hω (X ω), n2RegW γ α L r Hω (G ω),
    agreeNear_n2Model_reg hr hH hdec, isRegularWith_n2Reg hr hH hreg, fun c hc ρ f hf => ?_⟩
  have hl := hlim c hc ρ f hf
  obtain ⟨hρs, hρc, hρH⟩ := ρ.2
  have hf' : Continuous f ∧ HasCompactSupport f ∧ tsupport f ⊆ H := by
    rcases hf with rfl | hf
    · exact ⟨hρs.continuous, hρc, hρH⟩
    · rw [mem_singleton_iff] at hf
      subst hf
      exact ⟨hρs.continuous.neg, hρc.neg, by rw [tsupport_neg]; exact hρH⟩
  exact exists_tendsto_pair_n2RegW (hGv.cont ω) hr hH hc hf'.1 hf'.2.1 hf'.2.2 hl

/-- **N2Z-MODELLOC from the free-field continuum pairing node.** -/
theorem n2ZModelLoc_of_contPair (hCP : N2ZContPairGFFStmt) : N2ZModelLocStmt :=
  n2ZModelLoc_of_reg (n2ZModelReg_of_contPair hCP)

end D3Plus
end QuantumZipper
