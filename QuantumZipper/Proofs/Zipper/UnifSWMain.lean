import QuantumZipper.Proofs.Zipper.UnifSWDense

/-!
# UNIF-SW (4): AW from the countable-family statement `AnchorUnifFamStmt`

Task UNIF-SW (decision D26). Combining

* `anchorApproxContStmt_holds` (AC-cont, proved, `UnifSWCont`),
* `ucs_of_fam` (countable test family and rational times suffice, `UnifSWDense`),
* `anchorWindowStmt_of_cont_unif` (AW from AC-cont + AC-unif without UG, `UnifSWRat`),

the anchored windows AW reduce to **`AnchorUnifFamStmt`**: for each rational anchor `q`, rational
live window `(u,v)`, and each member `x^i · swTrap a b c d` (rational `u < a < b < c < d < v`) of
the countable test family, a.s. the transported integrals are uniformly Cauchy in `k` over the
**rational** times `s ∈ [q,T]`. This is the single-test-function form of the Sheffield–Wang
uniform convergence (arXiv:1605.06171, (3.5) p. 12, boundary version Thm 4.3), for the field
`h⁰_q` and the one-parameter family of maps `F_s` given by the driver after `q`.

Main results: `anchorUnifCauchyStmt_of_fam`, **`anchorWindowStmt_of_fam`**.
The bookkeeping is own (see the module docstrings of the imported files).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace RegUnif

open B2 B5 E1 E1.M4

variable {Ω : Type} [MeasurableSpace Ω]

/-- **AC-fam** (open analytic core): uniform Cauchy property of the transported integrals of one
test function of the countable family, over the rational times of `[q,T]`. -/
def AnchorUnifFamStmt (κ T : ℝ) (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) :
    Prop :=
  ∀ q : ℚ, (0 : ℝ) < q → (q : ℝ) ≤ T → ∀ u v : ℚ, ∀ i : ℕ, ∀ a b c d : ℚ, ∀ᵐ ω ∂P,
    zeroMinus (Vr κ T B ω) T < u → (u : ℝ) < a → a < b → b < c → c < d → (d : ℝ) < v →
    (v : ℝ) < zeroMinus (Vr κ T B ω) (T - q) →
      UniformCauchySeqOn (fun k s => awInt κ T B X ω u v (swFam i a b c d) s k) atTop
        (Icc (q : ℝ) T ∩ range ((↑) : ℚ → ℝ))

variable {P : Measure Ω} [IsProbabilityMeasure P] {κ T : ℝ} {B : ℝ≥0 → Ω → ℝ}
  {X : Ω → FieldSample}

/-- **AC-unif from AC-fam.** -/
theorem anchorUnifCauchyStmt_of_fam (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T)
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    (hF : AnchorUnifFamStmt κ T P B X) : AnchorUnifCauchyStmt κ T P B X := by
  intro q hq hqT u v
  have hall : ∀ᵐ ω ∂P, ∀ i : ℕ, ∀ a b c d : ℚ,
      zeroMinus (Vr κ T B ω) T < u → (u : ℝ) < a → a < b → b < c → c < d → (d : ℝ) < v →
      (v : ℝ) < zeroMinus (Vr κ T B ω) (T - q) →
        UniformCauchySeqOn (fun k s => awInt κ T B X ω u v (swFam i a b c d) s k) atTop
          (Icc (q : ℝ) T ∩ range ((↑) : ℚ → ℝ)) :=
    ae_all_iff.2 fun i => ae_all_iff.2 fun a => ae_all_iff.2 fun b => ae_all_iff.2 fun c =>
      ae_all_iff.2 fun d => hF q hq hqT u v i a b c d
  filter_upwards [hall, anchorApproxContStmt_holds hκ hκ4 hT hB hX hind q hq hqT u v,
    ae_forall_isRegularWith_joint (κ := κ) (γ := Real.sqrt κ) hB hX hind hT,
    ae_zeroMinus_Vr_facts RS.rohdeSchrammSimple hκ hκ4.le hT P B hB, hB.cont,
    ae_isSimpleCurveHull_revHull_Vr RS.rohdeSchrammSimple hκ hκ4.le hT P B hB]
    with ω hfam hAC hG hzm hcont hK hu huv hv f hf hfc hfs
  obtain ⟨G, hGc, hGr⟩ := hG
  obtain ⟨-, -, hanti, -, -, -⟩ := hzm
  set V := Vr κ T B ω with hVdef
  have hVc : Continuous V := continuous_vrev (drive_continuous hcont) T
  have hV0 : V 0 = 0 := vrev_zero hT.le
  set γ := Real.sqrt κ with hγ
  have hzmle : ∀ r ∈ Icc (q : ℝ) T, zeroMinus V (T - q) ≤ zeroMinus V (T - r) := fun r hr =>
    hanti.antitoneOn ⟨by linarith [hr.2], by linarith [hr.1, hq]⟩
      ⟨by linarith, by linarith⟩ (by linarith [hr.1])
  have hlive : ∀ r ∈ Icc (q : ℝ) T, ∀ x ∈ Icc (u : ℝ) v, IsLive V (T - r) x := fun r hr x hx =>
    (mem_liveNeg_of_lt_zeroMinus hVc hV0 hT hK (by linarith [hr.2]) (by linarith [hr.1, hq])
      ((hx.2.trans_lt hv).trans_le (hzmle r hr))).2
  have hΦ : ∀ s ∈ Icc (q : ℝ) T, ∃ Φ : ℝ ≃o ℝ, ∀ y ∈ Icc (u : ℝ) v,
      Φ y = realRevMap V (T - s) y := fun s hs =>
    exists_orderIso_eq_realRevMap hVc (by linarith [hs.2]) huv (hlive s hs)
  have hfin : ∀ s ∈ Icc (q : ℝ) T, ∀ k,
      IsLocallyFiniteMeasure (bdryApprox γ (h0f κ s B X ω) k) := by
    intro s hs k
    have hs0 : s ∈ Icc (0 : ℝ) T := ⟨hq.le.trans hs.1, hs.2⟩
    have havg : ∀ x : ℝ, avgReg (h0f κ s B X ω) k (x : ℂ) = G (s, ((x : ℂ), radius k)) := by
      intro x
      rw [h0f_eq_unzippedField]
      exact (hGr s hs0).avgReg_eq k (ofReal_mem_Hbar_ug x)
    have he : bdryApprox γ (h0f κ s B X ω) k = volume.withDensity fun t : ℝ =>
        ENNReal.ofReal (radius k ^ (γ ^ 2 / 4) * Real.exp (γ / 2 * G (s, ((t : ℂ), radius k)))) := by
      unfold bdryApprox
      simp_rw [havg]
    rw [he]
    have hc : Continuous fun t : ℝ => G (s, ((t : ℂ), radius k)) :=
      hGc.comp_continuous (continuous_const.prodMk (Complex.continuous_ofReal.prodMk
        continuous_const)) fun t => ⟨hs0, ofReal_mem_Hbar_ug t, radius_pos k⟩
    exact IsLocallyFiniteMeasure.withDensity_ofReal
      (continuous_const.mul ((continuous_const.mul hc).rexp))
  exact ucs_of_fam (F := fun s => realRevMap V (T - s))
    (A := fun s k => bdryApprox γ (h0f κ s B X ω) k) hΦ hfin
    (fun f hf hfc hfs k => hAC hu huv hv f hf hfc hfs k)
    (fun i a b c d h1 h2 h3 h4 h5 => hfam i a b c d hu h1 h2 h3 h4 h5 hv) hf hfc hfs

/-- **AW from AC-fam** (no UG, no AC-cont hypothesis). -/
theorem anchorWindowStmt_of_fam (hκ : 0 < κ) (hκ4 : κ < 4) (hT : 0 < T)
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    (hF : AnchorUnifFamStmt κ T P B X) : AnchorWindowStmt κ T P B X :=
  anchorWindowStmt_of_cont_unif hκ hκ4 hT hB hX hind
    (anchorApproxContStmt_holds hκ hκ4 hT hB hX hind)
    (anchorUnifCauchyStmt_of_fam hκ hκ4 hT hB hX hind hF)

end RegUnif
end QuantumZipper
