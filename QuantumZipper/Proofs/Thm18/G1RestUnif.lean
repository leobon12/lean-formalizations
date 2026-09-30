import QuantumZipper.Proofs.Thm18.G1RestRC3Wire
import QuantumZipper.Proofs.Thm18.G1RestUnifDefs
import QuantumZipper.Proofs.Thm18.G1RestUnifFree

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1-REST-UNIF: the uniform Cauchy input `G1RestUnifStmt`

For a.e. path `a` and both sides, `ψ = Ψ left a` satisfies `PsiGood` and has a continuous
extension `ψe` with the Kolmogorov bounds (`PsiExt`). For a regular version `G` of the free field
`X` and a.e. `ω'` (good sample, canonical scale `S > 0`, growth bounds of the profile `g`), the
smoothings of `y = wedgeRep γ X A ω'` along `ψ` split, at every `q = (d, r)`, `r > 0`, as

  `PhiP y ψ k q = ∫ G(S ψe z, S 2^{-k}) dfc(q) + ∫ smoothFun (rp g) (S ψ z) (S 2^{-k}) dfc(q) + Q log S`

(`G1RC.AvgRegPsiStmt`). The first term converges uniformly on each compact box `kbox m`
(`G1RC.ae_unif_pushed`: joint continuity of the Kolmogorov–Čentsov modification down to radius
`0`, Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.1), the second by
`G1RC.UnifProfStmt`; uniformly convergent sequences are uniformly Cauchy, and the dyadic points
of `box m ∩ Sd` lie in `kbox m`. This gives `C2P` (`G1Rest.c2P_of_parts`).

Main result: `g1RestUnifStmt_of : G1RC.UnifProfStmt → G1RC.AvgRegPsiStmt → G1RestUnifStmt`.
Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function Metric
open scoped NNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G1Rest

open GoodMeas (Sd box qpt kbox box_inter_subset)

/-- **Deterministic core**: a splitting of the smoothings into two uniformly Cauchy parts
(on every compact box) and a constant gives `C2P`. -/
theorem c2P_of_parts {y : FieldSample} {ψ : ℂ → ℂ} {Fr Pr : ℕ → ℂ × ℝ → ℝ} (c : ℝ)
    (hid : ∀ q ∈ Sd, ∀ k : ℕ, PhiP y ψ k q = Fr k q + Pr k q + c)
    (hFr : ∀ M : ℕ, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ k, N ≤ k → ∀ k', N ≤ k' → ∀ q ∈ kbox M,
      |Fr k q - Fr k' q| < ε)
    (hPr : ∀ M : ℕ, ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ k, N ≤ k → ∀ k', N ≤ k' → ∀ q ∈ kbox M,
      |Pr k q - Pr k' q| < ε) :
    C2P y ψ := by
  intro M e
  have he : (0 : ℝ) < 1 / ((e : ℝ) + 1) / 2 := by positivity
  obtain ⟨N₁, h₁⟩ := hFr M _ he
  obtain ⟨N₂, h₂⟩ := hPr M _ he
  refine ⟨max N₁ N₂, fun i hi i' hi' j hjS hjB => ?_⟩
  have hq : qpt j ∈ kbox M := box_inter_subset M ⟨hjB, hjS⟩
  rw [hid _ hjS, hid _ hjS]
  have a1 := h₁ i (le_of_max_le_left hi) i' (le_of_max_le_left hi') _ hq
  have a2 := h₂ i (le_of_max_le_right hi) i' (le_of_max_le_right hi') _ hq
  have : Fr i (qpt j) + Pr i (qpt j) + c - (Fr i' (qpt j) + Pr i' (qpt j) + c) =
      (Fr i (qpt j) - Fr i' (qpt j)) + (Pr i (qpt j) - Pr i' (qpt j)) := by ring
  rw [this]
  refine (abs_add_le _ _).trans ?_
  linarith

/-- A sequence converging uniformly on every `kbox M` is uniformly Cauchy there. -/
theorem cauchy_of_unif {Fr : ℕ → ℂ × ℝ → ℝ} {V : ℂ × ℝ → ℝ}
    (h : ∀ M : ℕ, TendstoUniformlyOn Fr V atTop (kbox M)) (M : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ k, N ≤ k → ∀ k', N ≤ k' → ∀ q ∈ kbox M, |Fr k q - Fr k' q| < ε := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 (Metric.tendstoUniformlyOn_iff.1 (h M) (ε / 2)
    (half_pos hε))
  refine ⟨N, fun k hk k' hk' q hq => ?_⟩
  have a1 := hN k hk q hq
  have a2 := hN k' hk' q hq
  rw [Real.dist_eq] at a1 a2
  have : Fr k q - Fr k' q = -(V q - Fr k q) + (V q - Fr k' q) := by ring
  rw [this]
  refine (abs_add_le _ _).trans_lt ?_
  rw [abs_neg]
  linarith

/-- The free part is uniformly Cauchy along the scales `S 2^{-k}`. -/
theorem cauchy_of_eta {Fr : ℕ → ℂ × ℝ → ℝ} {W : ℝ → ℂ × ℝ → ℝ} {V : ℂ × ℝ → ℝ} {S : ℝ}
    (hS : 0 < S) (hFr : ∀ k q, Fr k q = W (S * radius k) q)
    (h : ∀ M : ℕ, ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∀ t : ℝ, 0 < t → t < η → ∀ q ∈ kbox M,
      |W t q - V q| < ε) (M : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ k, N ≤ k → ∀ k', N ≤ k' → ∀ q ∈ kbox M, |Fr k q - Fr k' q| < ε := by
  obtain ⟨η, hη, hW⟩ := h M (ε / 2) (half_pos hε)
  have ht : Tendsto (fun k : ℕ => S * radius k) atTop (𝓝 0) := by
    simpa using (RegClosure.tendsto_radius_nhdsGT.mono_right nhdsWithin_le_nhds).const_mul S
  obtain ⟨N, hN⟩ := eventually_atTop.1 (ht.eventually (gt_mem_nhds hη))
  refine ⟨N, fun k hk k' hk' q hq => ?_⟩
  have a1 := hW _ (mul_pos hS (radius_pos k)) (hN k hk) q hq
  have a2 := hW _ (mul_pos hS (radius_pos k')) (hN k' hk') q hq
  rw [hFr, hFr]
  have : W (S * radius k) q - W (S * radius k') q =
      (W (S * radius k) q - V q) - (W (S * radius k') q - V q) := by ring
  rw [this]
  refine (abs_sub _ _).trans_lt ?_
  linarith

open G1RC F1.RC3Two in
/-- **Splitting of the smoothings** of the rescaled wedge field along `ψ`. -/
theorem phiP_split (hAvg : AvgRegPsiStmt) {x : FieldSample} {F : ℂ × ℝ → ℝ} {A : ℝ → ℝ}
    (hW : WedgeGood x F A) {Q C : ℝ}
    (hbd : ∀ t, 0 < t → t ≤ 1 → |wg x A Q t| ≤ C * (1 - Real.log t)) {S : ℝ} (hS : 0 < S)
    {ψ ψe : ℂ → ℂ} (hψ : PsiGood ψ) (hψec : ContinuousOn ψe Hbar) (hψeH : MapsTo ψe Hbar Hbar)
    (heq : EqOn ψ ψe H) {q : ℂ × ℝ} (hq : 0 < q.2) (k : ℕ) :
    PhiP (rescale (wedgeField (lateralPart x) A Q) Q S) ψ k q =
      (∫ z, F ((S : ℂ) * ψe z, S * radius k) ∂foldedCircle q.1 q.2) +
        (∫ z, GoodSample.smoothFun (rp (wg x A Q)) ((S : ℂ) * ψ z) (S * radius k)
          ∂foldedCircle q.1 q.2) + Q * Real.log S := by
  have hSk : 0 < S * radius k := mul_pos hS (radius_pos k)
  have hmaps : MapsTo (fun z => (S : ℂ) * ψe z) Hbar Hbar := fun z hz =>
    show 0 ≤ ((S : ℂ) * ψe z).im by
      rw [Complex.im_ofReal_mul]; exact mul_nonneg hS.le (hψeH hz)
  have hSψ : ContinuousOn (fun z => (S : ℂ) * ψe z) Hbar := continuousOn_const.mul hψec
  have ha : ContinuousOn (fun z => F ((S : ℂ) * ψe z, S * radius k)) Hbar :=
    hW.good.1.1.comp (hSψ.prodMk continuousOn_const) fun z hz => ⟨hmaps hz, hSk⟩
  have hb : ContinuousOn (fun z => GoodSample.smoothFun (rp (wg x A Q)) ((S : ℂ) * ψe z)
      (S * radius k)) Hbar :=
    (continuous_smoothFun_rp (measurable_wg hW.cont) (continuousOn_wg hW.good hW.cont) hbd
      hSk).comp_continuousOn hSψ
  have ia := RegClosure.integrable_fc ha q.1 hq.le
  have ib := RegClosure.integrable_fc hb q.1 hq.le
  have hae : ∀ᵐ z ∂foldedCircle q.1 q.2,
      avgReg (rescale (wedgeField (lateralPart x) A Q) Q S) k (ψ z) =
        F ((S : ℂ) * ψe z, S * radius k) + GoodSample.smoothFun (rp (wg x A Q))
          ((S : ℂ) * ψe z) (S * radius k) + Q * Real.log S := by
    filter_upwards [hAvg x F A hW Q C hbd S hS ψ hψ q.1 q.2 hq k,
      TwoPoint.foldedCircle_ae_mem_H q.1 hq] with z h1 hz
    rw [h1, heq hz]
  have hae2 : ∀ᵐ z ∂foldedCircle q.1 q.2,
      GoodSample.smoothFun (rp (wg x A Q)) ((S : ℂ) * ψ z) (S * radius k) =
        GoodSample.smoothFun (rp (wg x A Q)) ((S : ℂ) * ψe z) (S * radius k) := by
    filter_upwards [TwoPoint.foldedCircle_ae_mem_H q.1 hq] with z hz
    rw [heq hz]
  unfold PhiP
  rw [integral_congr_ae hae, integral_add (f := fun z => F ((S : ℂ) * ψe z, S * radius k) +
      GoodSample.smoothFun (rp (wg x A Q)) ((S : ℂ) * ψe z) (S * radius k))
      (g := fun _ => Q * Real.log S) (ia.add ib) (integrable_const _), integral_add ia ib,
    integral_congr_ae hae2]
  simp

open G1RC F1.RC3Two in
/-- **`G1RestUnifStmt` from the two deterministic inputs.** -/
theorem g1RestUnifStmt_of (h1 : UnifProfStmt) (h2 : AvgRegPsiStmt) : G1RestUnifStmt := by
  intro γ hγ hγ2 Ω _ P _ B hB Ω' _ P' _ X A hX hA hXA Ψ hΨ
  obtain ⟨G, hG⟩ := WedgeTK.exists_isRegVersion hX
  have hg := ae_map_pathOf_of_chord g1RegPathChordStmt hγ hγ2 hB hΨ
    (fun f => ∀ left, PsiGood (f left)) fun a hc hs left => psiGood_of_sel hΨ hc hs left
  filter_upwards [hg, g1PsiExtStmt_of_holder_α g1GoodBMStmt_sideHolderGood
    γ hγ hγ2 P B hB P' X A hX hA hXA Ψ hΨ] with a hgood hext left
  obtain ⟨ψe, -, hψec, hψeH, heq, β, hβ, hPB⟩ := hext left
  obtain ⟨V, hV⟩ := ae_unif_pushed hψec hψeH hβ hPB hX hG
  filter_upwards [ae_wedgeGood hX hA hXA hG, ae_scale_pos hγ hγ2 hX hA hXA,
    F1.ae_growth_radAvgReg hX, F1.ae_growth_wedge hA, hV] with ω' hW hS hr hw hVω
  obtain ⟨K₁, M₁, hM₁, h₁⟩ := hr
  obtain ⟨K₂, M₂, hM₂, h₂⟩ := hw
  have hbd := bd_wg (x := X ω') (Q := Qc γ) (A := fun t => A t ω') hM₁ hM₂ h₁ h₂
  have hgm := measurable_wg (x := X ω') (Q := Qc γ) hW.cont
  have hgc := continuousOn_wg (Q := Qc γ) hW.good hW.cont
  set S := scaleParam γ (wedge0 γ X A ω') with hSdef
  show G1Rest.C2P (rescale (wedgeField (lateralPart (X ω')) (fun t => A t ω') (Qc γ)) (Qc γ) S)
    (Ψ left a)
  refine c2P_of_parts (Qc γ * Real.log S)
    (Fr := fun k q => ∫ z, G ω' ((S : ℂ) * ψe z, S * radius k) ∂foldedCircle q.1 q.2)
    (fun q hq k => phiP_split h2 hW hbd hS (hgood left) hψec hψeH heq hq.2 k)
    (cauchy_of_eta hS (W := fun t q => ∫ z, G ω' ((S : ℂ) * ψe z, t) ∂foldedCircle q.1 q.2)
      (fun k q => rfl) (fun M ε hε => hVω S hS M ε hε))
    (cauchy_of_unif (h1 _ (hgood left) S hS _ _ hgm hgc hbd))

end G1Rest
end Thm18Asm
end QuantumZipper
