import QuantumZipper.Proofs.Thm18.G1SSR2Asm

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1SSR2 (8): `G1SidePushUCRepStmt`, hence `G1SidePushContStmt` and `G1SideShiftRegAStmt`

Theorem 1.8, G1 zoom. Uniform continuity on compact parameter boxes of the split pushed pairing
(`gPush_split`) gives the countable Cauchy condition `UCond` (`ucond_of_split`); the a.s. inputs
are those of `G1ProfileStmt` (good free sample, positive canonical scale, logarithmic growth of the
radial part and of the wedge process) and the continuous modification of the free-field pairings
along the pushed circles of the continuous extension of the selected side map
(`G1RC.exists_pushed_joint`, Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.1).
Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function Metric
open scoped Topology NNReal

namespace QuantumZipper
namespace Thm18Asm
namespace G1SSR2

open F1.RC3Two G1RC

theorem continuousOn_snoc_qOf (S : ℝ) :
    ContinuousOn (fun p : ℂ × ℝ × ℝ => (Fin.snoc (qOf p.1 p.2.1 S) (S * p.2.2) : Fin 5 → ℝ))
      {p | 0 < p.2.1} := by
  refine continuousOn_pi.2 fun i => ?_
  fin_cases i
  · exact (Complex.continuous_re.comp continuous_fst).continuousOn
  · exact (Complex.continuous_im.comp continuous_fst).continuousOn
  · exact Real.continuousOn_log.comp continuous_snd.fst.continuousOn fun p hp =>
      ne_of_gt (show (0 : ℝ) < p.2.1 from hp)
  · exact continuousOn_const
  · exact (continuous_const.mul continuous_snd.snd).continuousOn

theorem isCompact_box (N : ℕ) : IsCompact {c : ℂ | |c.re| ≤ N ∧ |c.im| ≤ N} := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · exact (isClosed_le (continuous_abs.comp Complex.continuous_re) continuous_const).inter
      (isClosed_le (continuous_abs.comp Complex.continuous_im) continuous_const)
  · refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 2 * N)).subset fun c hc => ?_
    rw [Metric.mem_closedBall, dist_zero_right]
    linarith [Complex.norm_le_abs_re_add_abs_im c, hc.1, hc.2]

variable {x : FieldSample} {F : ℂ × ℝ → ℝ} {A : ℝ → ℝ} {C : ℝ}

/-- **The countable Cauchy condition from the split.** -/
theorem ucond_of_split (h : WedgeGood x F A) (Q : ℝ) {S : ℝ} (hS : 0 < S)
    (hbd : ∀ t, 0 < t → t ≤ 1 → |wg x A Q t| ≤ C * (1 - Real.log t))
    {ψ ψe : ℂ → ℂ} (hψ : PsiGood ψ) (heq : EqOn ψ ψe H) (hψem : Measurable ψe)
    (hψec : ContinuousOn ψe Hbar) (hψeH : MapsTo ψe Hbar Hbar)
    {Yf : (Fin 5 → ℝ) → ℝ} (hYc : Continuous Yf)
    (hYf : ∀ (d : ℂ) (r t : ℝ), 0 < r → 0 < t →
      ∫ u, F (u, t) ∂((foldedCircle d r).map fun z => (S : ℂ) * ψe z) =
        Yf (Fin.snoc (qOf d r S) t)) :
    UCond (rescale (wedgeField (lateralPart x) A Q) Q S) ψ := by
  have hgm : Measurable (wg x A Q) := measurable_wg h.cont
  have hgc : ContinuousOn (wg x A Q) (Ioi 0) := continuousOn_wg h.good h.cont
  intro N ε hε
  set T : ℂ × ℝ × ℝ → ℝ := fun p => Yf (Fin.snoc (qOf p.1 p.2.1 S) (S * p.2.2)) +
    ∫ u, profInt (wg x A Q) ψ S p.2.2 u ∂foldedCircle p.1 p.2.1 with hT
  set K : Set (ℂ × ℝ × ℝ) := {c : ℂ | |c.re| ≤ N ∧ |c.im| ≤ N} ×ˢ
    Icc (1 / ((N : ℝ) + 1)) N ×ˢ Icc 0 (1 / S) with hK
  have hKc : IsCompact K := (isCompact_box N).prod (isCompact_Icc.prod isCompact_Icc)
  have hN1 : (0 : ℝ) < 1 / ((N : ℝ) + 1) := by positivity
  have hKsub : K ⊆ {p : ℂ × ℝ × ℝ | 0 < p.2.1 ∧ p.2.2 ∈ Icc 0 (1 / S)} := fun p hp =>
    ⟨lt_of_lt_of_le hN1 hp.2.1.1, hp.2.2⟩
  have hTc : ContinuousOn T K := by
    refine ((hYc.comp_continuousOn (continuousOn_snoc_qOf S)).mono fun p hp =>
      (hKsub hp).1).add ((continuousOn_profPush hψ hS hgm hgc hbd).mono hKsub)
  obtain ⟨δ, hδ, hU⟩ := Metric.uniformContinuousOn_iff.1
    (hKc.uniformContinuousOn_of_continuous hTc) (ε : ℝ) (by exact_mod_cast hε)
  obtain ⟨δq, hδq0, hδq1⟩ := exists_rat_btwn (show (0 : ℝ) < min δ (1 / S) by positivity)
  refine ⟨δq, by exact_mod_cast hδq0, fun a b r σ σ' ha hb hr1 hr2 hσ0 hσδ hσ'0 hσ'δ => ?_⟩
  have hδqδ : (δq : ℝ) < δ := lt_of_lt_of_le hδq1 (min_le_left _ _)
  have hδqS : (δq : ℝ) < 1 / S := lt_of_lt_of_le hδq1 (min_le_right _ _)
  have hσ0' : (0 : ℝ) < σ := by exact_mod_cast hσ0
  have hσ'0' : (0 : ℝ) < σ' := by exact_mod_cast hσ'0
  have hσδ' : (σ : ℝ) < δq := by exact_mod_cast hσδ
  have hσ'δ' : (σ' : ℝ) < δq := by exact_mod_cast hσ'δ
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le hN1 hr1
  have hsplit : ∀ s : ℝ, 0 < s → s < δq →
      gPush (rescale (wedgeField (lateralPart x) A Q) Q S) ψ ⟨a, b⟩ r s =
        T ((⟨a, b⟩ : ℂ), (r : ℝ), s) + Q * Real.log S := fun s hs hsδ => by
    rw [gPush_split h Q hS hbd hψ heq hψem hψec hψeH _ hr0 hs (by linarith),
      hYf _ _ _ hr0 (mul_pos hS hs)]
  have hmem : ∀ s : ℝ, 0 < s → s < δq → ((⟨a, b⟩ : ℂ), (r : ℝ), s) ∈ K := fun s hs hsδ =>
    ⟨⟨ha, hb⟩, ⟨hr1, hr2⟩, ⟨hs.le, by linarith⟩⟩
  have hd := hU _ (hmem _ hσ0' hσδ') _ (hmem _ hσ'0' hσ'δ') (by
    rw [Prod.dist_eq, Prod.dist_eq, dist_self, dist_self, Real.dist_eq]
    refine max_lt hδ (max_lt hδ ?_)
    rw [abs_sub_lt_iff]; constructor <;> linarith)
  rw [hsplit _ hσ0' hσδ', hsplit _ hσ'0' hσ'δ']
  rw [Real.dist_eq] at hd
  have : T ((⟨a, b⟩ : ℂ), (r : ℝ), (σ : ℝ)) + Q * Real.log S -
      (T ((⟨a, b⟩ : ℂ), (r : ℝ), (σ' : ℝ)) + Q * Real.log S) =
      T ((⟨a, b⟩ : ℂ), (r : ℝ), (σ : ℝ)) - T ((⟨a, b⟩ : ℂ), (r : ℝ), (σ' : ℝ)) := by ring
  rw [this]
  exact hd.le

end G1SSR2

/-- **`G1SidePushUCRepStmt` holds.** -/
theorem g1SidePushUCRepStmt_holds : G1SidePushUCRepStmt := by
  intro γ hγ hγ2 Ω _ P _ B hB Ω' _ P' _ X A hX hA hXA Ψ hΨ
  obtain ⟨G, hG⟩ := WedgeTK.exists_isRegVersion hX
  have hQ := G1RC.ae_map_pathOf_of_chord G1RC.g1RegPathChordStmt hγ hγ2 hB hΨ
    (fun ms => ∀ left : Bool, G1RC.PsiExt (ms left) →
      ∀ᵐ ω' ∂P', G1SSR2.UCond (wedgeRep γ X A ω') (ms left)) ?_
  · filter_upwards [hQ, G1RC.g1PsiExtStmt_holds γ hγ hγ2 P B hB P' X A hX hA hXA Ψ hΨ]
      with a h1 h2 left
    exact h1 left (h2 left)
  intro a hc hs left hpe
  have hψ := G1RC.psiGood_of_sel hΨ hc hs left
  obtain ⟨ψe, hψem, hψec, hψeH, heq, β, hβ, hBd⟩ := hpe
  obtain ⟨Y, hYc, hY⟩ := G1RC.exists_pushed_joint hψem hψec hψeH hβ hBd hX hG
  filter_upwards [G1RC.ae_wedgeGood hX hA hXA hG, G1RC.ae_scale_pos hγ hγ2 hX hA hXA,
    F1.ae_growth_radAvgReg hX, F1.ae_growth_wedge hA, hY] with ω' hW hS hr hw hYω
  obtain ⟨K₁, M₁, hM₁, h₁⟩ := hr
  obtain ⟨K₂, M₂, hM₂, h₂⟩ := hw
  exact G1SSR2.ucond_of_split hW (Qc γ) hS
    (F1.RC3Two.bd_wg (Q := Qc γ) (A := fun t => A t ω') hM₁ hM₂ h₁ h₂) hψ heq hψem hψec hψeH
    (hYc ω') fun d r t hr ht => hYω d r _ t hr hS ht

/-- **`G1SidePushContStmt` holds.** -/
theorem g1SidePushContStmt_holds : G1SidePushContStmt :=
  g1SidePushContStmt_of_rep g1SidePushUCRepStmt_holds

/-- **`G1SideShiftRegAStmt` (D89) from the side area node alone.** -/
theorem g1SideShiftRegAStmt_of_good (hZ2 : G1Z2SideGoodStmt) : G1SideShiftRegAStmt :=
  g1SideShiftRegAStmt_of_pushCont hZ2 g1SidePushContStmt_holds

end Thm18Asm
end QuantumZipper
