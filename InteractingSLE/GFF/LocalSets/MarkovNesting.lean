import InteractingSLE.GFF.LocalSets.Projection
import LQGMetric.Field.RandomDistVersion

/-!
# Nesting of the complementary Markov projections

Infrastructure for Lemma 3.6, (i) ⇒ (iii) (specification §3.2, pp. 52–54; transcription
`source/spec/p049-096.md#lem-3.6-proof`). The proof uses (i) for the avoidance events of open sets
`V ⊇ W` and needs: "By (i), its conditional probability given `h` is measurable with respect to the
projection onto `H^⊥(D∖F_m)`, hence with respect to `Q_C`" (p. 53). For open `W ⊆ V ⊆ ℍ`,
`H(W) ⊆ H(V)`, so `H^⊥(V) ⊆ H^⊥(W)` and the projection of `h` onto `H^⊥(V)` is a function of the
projection onto `H^⊥(W)`. Here the projections are versions `h − G_V h`, `h − G_W h` given by
Borel maps (Proposition 3.1), and the statement is proved for every pairing as an `L²` limit:
with `f_n ∈ C_c^∞(V)`, `g_n ∈ C_c^∞(W)` approximating the Gram vectors,
`(h − G_V h)(Φ) = lim [(h − G_W h)(Φ) + (h − G_W h)(Δ̃g_n) − (h − G_W h)(Δ̃f_n)]`,
the error being controlled by `‖covVec_W ψ‖ ≤ ‖covVec_V ψ‖` (`norm_covVec_le`).

## Main results

* `exists_measurable_ae_eq_of_tendsto_integral_sq` : an `L²` limit of `m`-measurable functions has
  an `m`-measurable version;
* `zeroGFFTestCov_mono`, `norm_covVec_le` : dual Dirichlet norms increase with the domain;
* `exists_measurable_markovCompl_apply`, `exists_measurable_markovCompl_comp` : nesting.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace
open scoped RealInnerProductSpace ENNReal

namespace InteractingSLE
namespace LocalSets

open QuantumZipper QuantumZipper.K3 QuantumZipper.Thm11Asm LQGMetric LQGMetric.MarkovZB

section L2

variable {Ω : Type*} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- An `L²` limit of `m`-measurable functions has an `m`-measurable version. -/
theorem exists_measurable_ae_eq_of_tendsto_integral_sq {f : Ω → ℝ}
    {F : ℕ → Ω → ℝ} (hF : ∀ n, Measurable[m] (F n)) (hm : m ≤ mΩ)
    (hf : AEStronglyMeasurable f P) (hint : ∀ n, Integrable (fun ω => (f ω - F n ω) ^ 2) P)
    (hlim : Tendsto (fun n => ∫ ω, (f ω - F n ω) ^ 2 ∂P) atTop (𝓝 0)) :
    ∃ g : Ω → ℝ, Measurable[m] g ∧ f =ᵐ[P] g := by
  have hFm : ∀ n, AEStronglyMeasurable (F n) P := fun n =>
    ((hF n).mono hm le_rfl).aestronglyMeasurable
  have hmem : ∀ n, MemLp (F n - f) 2 P := fun n => by
    refine (memLp_two_iff_integrable_sq ((hFm n).sub hf)).2 ((hint n).congr ?_)
    exact Eventually.of_forall fun ω => by simp only [Pi.sub_apply]; ring
  have hnorm : ∀ n, eLpNorm (F n - f) 2 P =
      ENNReal.ofReal ((∫ ω, (f ω - F n ω) ^ 2 ∂P) ^ (2 : ℝ)⁻¹) := fun n => by
    rw [(hmem n).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    congr 2
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only [Pi.sub_apply, Real.norm_eq_abs, ENNReal.toReal_ofNat]
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
    ring
  have hmeas : TendstoInMeasure P F atTop f := by
    refine tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num) hFm hf ?_
    simp_rw [hnorm]
    have h0 : ENNReal.ofReal ((0 : ℝ) ^ (2 : ℝ)⁻¹) = 0 := by simp
    rw [← h0]
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      ((Real.continuousAt_rpow_const _ _ (Or.inr (by norm_num))).tendsto.comp hlim)
  obtain ⟨ns, -, hns⟩ := hmeas.exists_seq_tendsto_ae
  refine ⟨fun ω => limsup (fun i => F (ns i) ω) atTop, Measurable.limsup fun i => hF (ns i), ?_⟩
  filter_upwards [hns] with ω hω
  exact (hω.limsup_eq).symm


end L2

section Nesting

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- Dual Dirichlet norms increase with the domain. -/
theorem zeroGFFTestCov_mono {W V : Set ℂ} (hW : IsOpen W) (hV : IsOpen V) (hWV : W ⊆ V)
    (hVH : V ⊆ H) (φ : TestOn upperHalfPlaneOpens) :
    zeroGFFTestCov W φ φ ≤ zeroGFFTestCov V φ φ := by
  have hWH := hWV.trans hVH
  have hle : ENNReal.ofReal (zeroGFFTestCov W φ φ) ≤ ENNReal.ofReal (zeroGFFTestCov V φ φ) := by
    rw [ofReal_zeroGFFTestCov_eq_iSup hW hWH φ, ofReal_zeroGFFTestCov_eq_iSup hV hVH φ]
    refine iSup₂_le fun f hf => le_iSup₂_of_le (f := fun f (_ : f ∈ {f | f ∈ zeroSpace V ∧
      0 < energyC f}) => ENNReal.ofReal ((∫ z, φ z * f z) ^ 2 / energyC f)) f ⟨?_, hf.2⟩ le_rfl
    exact ⟨hf.1.1, hf.1.2.1, hf.1.2.2.trans hWV⟩
  exact (ENNReal.ofReal_le_ofReal_iff (zeroGFFTestCov_self_nonneg hV hVH φ)).1 hle

theorem norm_covVec_le {W V : Set ℂ} (hW : IsOpen W) (hV : IsOpen V) (hWV : W ⊆ V)
    (hVH : V ⊆ H) (φ : TestOn upperHalfPlaneOpens) : ‖covVec W φ‖ ≤ ‖covVec V φ‖ := by
  have h := zeroGFFTestCov_mono hW hV hWV hVH φ
  rw [zeroGFFTestCov_eq_inner_covVec hW (hWV.trans hVH), zeroGFFTestCov_eq_inner_covVec hV hVH,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  exact pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero |>.1 h

lemma measurable_markovCompl_comp {h : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h)
    {G : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens} (hG : Measurable fun ω => G (h ω)) :
    Measurable fun ω => markovCompl G (h ω) :=
  measurable_distOn_iff.2 fun φ =>
    ((measurable_distOn_apply φ).comp hh).sub ((measurable_distOn_apply φ).comp hG)

/-- **Nesting of the complementary projections**, one pairing at a time: for open `W ⊆ V ⊆ ℍ`,
the projection of `h` onto `H^⊥(V)` is (almost surely) a function of the projection onto
`H^⊥(W)`, since `H^⊥(V) ⊆ H^⊥(W)`. -/
theorem exists_measurable_markovCompl_apply {W V : Opens ℂ} (hWV : W ≤ V)
    (hV : V ≤ upperHalfPlaneOpens) {h : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h)
    {GW GV : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens}
    (hdW : GFF.IsMarkovDecomposition W upperHalfPlaneOpens h (fun ω => GW (h ω)) P)
    (hdV : GFF.IsMarkovDecomposition V upperHalfPlaneOpens h (fun ω => GV (h ω)) P)
    (Φ : TestOn upperHalfPlaneOpens) :
    ∃ Z : Ω → ℝ, Measurable[MeasurableSpace.comap (fun ω => markovCompl GW (h ω)) inferInstance] Z ∧
      (fun ω => markovCompl GV (h ω) Φ) =ᵐ[P] Z := by
  have hW : W ≤ upperHalfPlaneOpens := hWV.trans hV
  have hWH : (W : Set ℂ) ⊆ H := hW
  have hVH : (V : Set ℂ) ⊆ H := hV
  obtain ⟨f, hf1, hf2⟩ := exists_tendsto_integral_sq_of_isMarkovDecomposition hV hdV Φ
  obtain ⟨g, hg1, hg2⟩ := exists_tendsto_integral_sq_of_isMarkovDecomposition hW hdW Φ
  set Y : Ω → DistOn upperHalfPlaneOpens := fun ω => markovCompl GW (h ω) with hYdef
  have hYm : Measurable Y := measurable_markovCompl_comp hh hdW.isZBGFFExtOn.measurable
  set F : ℕ → Ω → ℝ := fun n ω => Y ω Φ + Y ω (lapTest W (g n)) - Y ω (lapTest V (f n)) with hFdef
  have hF : ∀ n, Measurable[MeasurableSpace.comap Y inferInstance] (F n) := fun n =>
    (((measurable_distOn_apply Φ).comp (comap_measurable Y)).add
      ((measurable_distOn_apply _).comp (comap_measurable Y))).sub
      ((measurable_distOn_apply _).comp (comap_measurable Y))
  set a : ℕ → Ω → ℝ := fun n ω => GV (h ω) Φ - h ω (lapTest V (f n))
  set b : ℕ → Ω → ℝ := fun n ω => GW (h ω) Φ - h ω (lapTest W (g n))
  set c : ℕ → Ω → ℝ := fun n ω => GW (h ω) (lapTest W (g n) - lapTest V (f n))
  have he : ∀ n ω, markovCompl GV (h ω) Φ - F n ω = -a n ω + b n ω + c n ω := by
    intro n ω
    simp only [hFdef, hYdef, markovCompl, a, b, c, map_sub, sub_apply]
    ring
  have ha : ∀ n, MemLp (a n) 2 P := fun n => memLp_markov_sub_lapTest hV hdV Φ (f n)
  have hb : ∀ n, MemLp (b n) 2 P := fun n => memLp_markov_sub_lapTest hW hdW Φ (g n)
  have hc : ∀ n, MemLp (c n) 2 P := fun n =>
    (hdW.isZBGFFExtOn.gaussian.hasGaussianLaw_eval _).memLp_two
  have hc2 : ∀ n, ∫ ω, c n ω ^ 2 ∂P = ‖covVec W ⇑(lapTest W (g n) - lapTest V (f n))‖ ^ 2 :=
    fun n => integral_sq_of_isZBGFFExtOn hWH hdW.isZBGFFExtOn _
  have hcn : Tendsto (fun n => ‖covVec W ⇑(lapTest W (g n) - lapTest V (f n))‖) atTop (𝓝 0) := by
    have hb1 : ∀ n, ‖covVec W ⇑(lapTest W (g n) - lapTest V (f n))‖ ≤
        ‖gradFeat W (g n).1 - covVec W Φ‖ + ‖covVec V Φ - gradFeat V (f n).1‖ := by
      intro n
      rw [covVec_sub W.isOpen hWH, covVec_lapTest hW W.isOpen hWH subset_rfl]
      have e1 : gradFeat (W : Set ℂ) (g n).1 - covVec W (lapTest V (f n)) =
          (gradFeat W (g n).1 - covVec W Φ) + covVec W ⇑(Φ - lapTest V (f n)) := by
        rw [covVec_sub W.isOpen hWH]; abel
      have e2 : covVec V ⇑(Φ - lapTest V (f n)) = covVec V Φ - gradFeat V (f n).1 := by
        rw [covVec_sub V.isOpen hVH, covVec_lapTest hV V.isOpen hVH subset_rfl]
      rw [e1]
      refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
      rw [← e2]
      exact norm_covVec_le W.isOpen V.isOpen hWV hVH _
    refine squeeze_zero (fun _ => norm_nonneg _) hb1 ?_
    have t1 : Tendsto (fun n => ‖gradFeat (W : Set ℂ) (g n).1 - covVec W Φ‖) atTop (𝓝 0) :=
      (tendsto_iff_norm_sub_tendsto_zero).1 hg1
    have t2 : Tendsto (fun n => ‖covVec (V : Set ℂ) Φ - gradFeat V (f n).1‖) atTop (𝓝 0) := by
      have := (tendsto_iff_norm_sub_tendsto_zero).1 hf1
      simpa [norm_sub_rev] using this
    simpa using t1.add t2
  refine exists_measurable_ae_eq_of_tendsto_integral_sq hF hYm.comap_le ?_ ?_ ?_
  · exact ((measurable_distOn_apply Φ).comp (measurable_markovCompl_comp hh
      hdV.isZBGFFExtOn.measurable)).aestronglyMeasurable
  · intro n
    have : MemLp (fun ω => -a n ω + b n ω + c n ω) 2 P := ((ha n).neg.add (hb n)).add (hc n)
    exact (this.integrable_sq).congr (Eventually.of_forall fun ω => by simp only [he n ω])
  · have hbd : ∀ n, ∫ ω, (markovCompl GV (h ω) Φ - F n ω) ^ 2 ∂P ≤
        3 * (∫ ω, a n ω ^ 2 ∂P + ∫ ω, b n ω ^ 2 ∂P + ∫ ω, c n ω ^ 2 ∂P) := by
      intro n
      have i1 := integral_add (μ := P) (f := fun ω => a n ω ^ 2) (g := fun ω => b n ω ^ 2)
        (ha n).integrable_sq (hb n).integrable_sq
      have i2 := integral_add (μ := P) (f := fun ω => a n ω ^ 2 + b n ω ^ 2)
        (g := fun ω => c n ω ^ 2) (((ha n).integrable_sq).add (hb n).integrable_sq)
        (hc n).integrable_sq
      have i3 := integral_const_mul (μ := P) (3 : ℝ) fun ω => a n ω ^ 2 + b n ω ^ 2 + c n ω ^ 2
      rw [← i1, ← i2, ← i3]
      refine integral_mono ?_ ?_ fun ω => ?_
      · exact ((((ha n).neg.add (hb n)).add (hc n)).integrable_sq).congr
          (Eventually.of_forall fun ω => by simp only [he n ω, Pi.add_apply, Pi.neg_apply])
      · exact ((((ha n).integrable_sq).add ((hb n).integrable_sq)).add
          ((hc n).integrable_sq)).const_mul 3
      · simp only [he n ω]
        nlinarith [sq_nonneg (a n ω + b n ω), sq_nonneg (a n ω + c n ω), sq_nonneg (b n ω - c n ω)]
    refine squeeze_zero (fun n => integral_nonneg fun ω => sq_nonneg _) hbd ?_
    have : Tendsto (fun n => 3 * (∫ ω, a n ω ^ 2 ∂P + ∫ ω, b n ω ^ 2 ∂P + ∫ ω, c n ω ^ 2 ∂P))
        atTop (𝓝 (3 * (0 + 0 + 0))) := by
      refine tendsto_const_nhds.mul ((hf2.add hg2).add ?_)
      simp_rw [hc2]
      simpa using hcn.pow 2
    simpa using this

/-- **Nesting of the complementary projections** (distribution form): for open `W ⊆ V ⊆ ℍ` there
is a Borel map `Ψ` with `h − G_V h = Ψ (h − G_W h)` almost surely. -/
theorem exists_measurable_markovCompl_comp {W V : Opens ℂ} (hWV : W ≤ V)
    (hV : V ≤ upperHalfPlaneOpens) {h : Ω → DistOn upperHalfPlaneOpens} (hh : Measurable h)
    {GW GV : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens}
    (hdW : GFF.IsMarkovDecomposition W upperHalfPlaneOpens h (fun ω => GW (h ω)) P)
    (hdV : GFF.IsMarkovDecomposition V upperHalfPlaneOpens h (fun ω => GV (h ω)) P) :
    ∃ Ψ : DistOn upperHalfPlaneOpens → DistOn upperHalfPlaneOpens, Measurable Ψ ∧
      (fun ω => markovCompl GV (h ω)) =ᵐ[P] fun ω => Ψ (markovCompl GW (h ω)) := by
  have key : ∀ c : CoordJ, ∃ z : DistOn upperHalfPlaneOpens → ℝ, Measurable z ∧
      (fun ω => markovCompl GV (h ω) (comb upperHalfPlaneOpens c)) =ᵐ[P]
        fun ω => z (markovCompl GW (h ω)) := by
    intro c
    obtain ⟨Z, hZ, hZe⟩ := exists_measurable_markovCompl_apply hWV hV hh hdW hdV
      (comb upperHalfPlaneOpens c)
    obtain ⟨z, hz, rfl⟩ := hZ.stronglyMeasurable.exists_eq_measurable_comp
    exact ⟨z, hz.measurable, hZe⟩
  choose z hz hze using key
  refine ⟨fun T => pairJInv upperHalfPlaneOpens fun c => z c T,
    (measurable_pairJInv _).comp (Measurable.of_eval fun c => hz c), ?_⟩
  filter_upwards [ae_all_iff.2 hze] with ω hω
  rw [← pairJInv_pairJ upperHalfPlaneOpens (markovCompl GV (h ω))]
  congr 1
  funext c
  exact hω c

end Nesting

end LocalSets
end InteractingSLE
