import QuantumZipper.Proofs.Thm18.A1RS3CD
import QuantumZipper.Proofs.Thm18.A1RS3ZCe

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A1RS3 (7): `A1RSRatCauchyStmt` from the free-field estimate along an independent Brownian driver

`A1RSFreeBrownStmt`: for a free field `X` and an independent Brownian motion `B`, a.s. the free
field satisfies the rational Cauchy estimate of the smeared-loop family of the driver `√κ B`
(and its dyadic pairings converge at the rational parameters), in some positively rescaled
parametrization `p ↦ ν_{parScale e p, ρ}` (the side map `g1zSideMap` is a choice made up to a
dilation, so only a rescaling-invariant form can be measurable in the driver). This is the
fixed-driver estimate
`ae_smear_fixed_all` (Duplantier–Sheffield, Invent. Math. 185 (2011), Prop. 3.1) along the
independent random driver.

**`a1rsRatCauchyStmt_of_freeBrown : A1RSFreeBrownStmt → A1RSRatCauchyStmt`.** The Theorem 1.8
field is realized as the canonical rescaling of `Z = X + α₀(−log|·|) + G` with the driver
`V = √κ B` of `Z` independent of `X` (`pStarRealizeStmt_holds`, `wedgeDecompStmt_holds`, as in
`ae_continuousOn_smearFam_pos`; Sheffield arXiv:1012.4797, §1.6). The free-field estimate gives
the one for `Z` (`ratCauchy_Z_of_X`), and the rescaling passes it to `Y`
(`ratCauchy_y_of_Z`), using (R3) and the continuum limits along the pushed side circles of `Y`.

Hence `a1rfSmearContStmt_of_freeBrown : A1RSFreeBrownStmt → A1RFSmearContStmt`.
Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped Topology NNReal

namespace QuantumZipper
namespace R18
namespace A1RS

open Thm18Asm F1 B3d.ZipLen

/-- **The free-field rational Cauchy estimate along an independent Brownian driver.** -/
def A1RSFreeBrownStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample),
    IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P → ∀ left : Bool,
    ∀ᵐ ω ∂P, ∃ e : Fin 4 → ℝ, (∀ i, 0 < e i) ∧
      (∀ a b : Fin 4 → ℚ, GenUC.ratBox a b ⊆ smearU → ∀ n : ℕ, ∃ N : ℕ, ∀ r : ℚ, 0 < r →
        (r : ℝ) < 1 / ((N : ℝ) + 1) → ∀ q : Fin 4 → ℚ, ratPt q ∈ GenUC.ratBox a b →
          |evalReg (X ω) (smearFam (drive κ B ω) left (parScale e (ratPt q)) r) -
            evalReg (X ω) (smearFam (drive κ B ω) left (parScale e (ratPt q)) 0)| <
              1 / ((n : ℝ) + 1)) ∧
      ∀ q : Fin 4 → ℚ, parScale e (ratPt q) ∈ smearU → ∀ r : ℚ, 0 ≤ r → r ≤ 1 →
        Tendsto (fun k : ℕ => ∫ w, avgReg (X ω) k w
            ∂(smearFam (drive κ B ω) left (parScale e (ratPt q)) r))
          atTop (𝓝 (evalReg (X ω) (smearFam (drive κ B ω) left (parScale e (ratPt q)) r)))

/-- **`A1RSRatCauchyStmt` from the free-field estimate along an independent driver.** -/
theorem a1rsRatCauchyStmt_of_freeBrown (hFB : A1RSFreeBrownStmt) : A1RSRatCauchyStmt := by
  intro γ Ω _ P _ B Y hS hIn left
  have hS0 := hS
  obtain ⟨hγ, hγ2, -, -, -⟩ := hS0
  have hMain : ∀ᵐ ω ∂P,
      (∀ t : ℝ, 0 < t → ∀ ρ : ℝ, 0 < ρ → ∀ R : ℝ,
        TendstoUniformlyOn (fun (k : ℕ) (z : ℂ) => ∫ u, avgReg (Y ω) k u
            ∂((foldedCircle z ρ).map (fwdMapInv (drive (γ ^ 2) B ω) t)))
          (fun z => evalReg (Y ω) ((foldedCircle z ρ).map (fwdMapInv (drive (γ ^ 2) B ω) t)))
          atTop (Hbar ∩ closedBall 0 R)) →
      G1zDrvGood (drive (γ ^ 2) B ω) → IsRegularSample (Y ω) →
      ContinuousOn (fun p => evalReg (Y ω) (smearFam (drive (γ ^ 2) B ω) left p 0)) smearU →
      (∀ (d : ℂ) (s : ℝ), 0 < s →
        ContData (Y ω) ((foldedCircle d s).map (g1zSideMap left (drive (γ ^ 2) B ω)))) →
      ∀ a b : Fin 4 → ℚ, GenUC.ratBox a b ⊆ smearU → ∀ n : ℕ, ∃ N : ℕ, ∀ r : ℚ, 0 < r →
        (r : ℝ) < 1 / ((N : ℝ) + 1) → ∀ q : Fin 4 → ℚ, ratPt q ∈ GenUC.ratBox a b →
          |evalReg (Y ω) (smearFam (drive (γ ^ 2) B ω) left (ratPt q) r) -
            evalReg (Y ω) (smearFam (drive (γ ^ 2) B ω) left (ratPt q) 0)| <
              1 / ((n : ℝ) + 1) := by
    have hP := isPStarSample_of_setting hS
    obtain ⟨hκ, hκ4, -⟩ := id hP
    obtain ⟨Ω₂, _, Q, _, X', A, B'', hX, hA, hInd, hB, hIB, hae⟩ :=
      WedgeUnzip.pStarRealizeStmt_holds (γ ^ 2) P Y B hP
    obtain ⟨Ω₃, _, Q₃, _, X'', G, hX'', hB2, hI2, hdec⟩ :=
      WedgeUnzip.WDec.wedgeDecompStmt_holds (γ ^ 2) hκ hκ4 (P.prod Q) X' A B'' hX hA hInd hB hIB
    have hγ' : 0 < Real.sqrt (γ ^ 2) := Real.sqrt_pos.2 hκ
    have hγ2' : Real.sqrt (γ ^ 2) < 2 := F2.sqrt_lt_two_of' hκ hκ4
    have hα := F2.alpha_lt_Qc' hγ' hγ2'
    have hspec := Wire2.ae_wedge_canonical_spec hγ' hγ2' hα hX hA hInd
    have lift2 : ∀ {p : Ω × Ω₂ → Prop}, (∀ᵐ ω ∂(P.prod Q), p ω) →
        ∀ᵐ ω ∂((P.prod Q).prod Q₃), p ω.1 := fun h =>
      ae_of_ae_map measurable_fst.aemeasurable (by rw [measurePreserving_fst.map_eq]; exact h)
    obtain ⟨δ, hδ, htrg⟩ := RS.ae_sleTrace_good hB2 hκ (by linarith)
    refine WedgeUnzip.ae_of_ae_prod_fst (Q := Q) (WedgeUnzip.ae_of_ae_prod_fst (Q := Q₃) ?_)
    filter_upwards [lift2 hae, lift2 hspec, hdec, RegSample.ae_isRegularSample hX'',
      A1RF.ae_flowPhiYc_tendstoUniformlyOn hκ hκ4 hB2 hX'' hI2,
      WedgeUnzip.ae_core2Y_inputs hκ hκ4 hB2 hX'' hI2, hB2.cont, hB2.eval_zero_ae_eq_zero,
      hFB (γ ^ 2) hκ hκ4 _ _ _ hB2 hX'' hI2 left, ae_g1zDrvGood_of_brownian hγ hγ2 hB2, htrg]
      with ω hR hsp hD hXreg hS1 hin hc h0 hfree hGV htr
    intro hl hGd hYreg hR3 hCD
    obtain ⟨havg, hcfg⟩ := hR
    obtain ⟨hGc, -, hZfc⟩ := hD
    obtain ⟨FX, hFX⟩ := hXreg
    obtain ⟨Fy, hFy⟩ := hYreg
    set s := Real.sqrt (γ ^ 2) with hs
    set Z := F2.zU s X' A ω.1 with hZ
    set b := scaleParam s Z with hbdef
    have hb : 0 < b := hsp.1
    set V : ℝ → ℝ := drive (γ ^ 2) (fun t (ω' : (Ω × Ω₂) × Ω₃) => B'' t ω'.1) ω with hVdef
    have hW : drive (γ ^ 2) B ω.1.1 = fun r => V (b ^ 2 * max r 0) / b := by
      have h2 : (canonConfig s (Z, drive (γ ^ 2) B'' ω.1)).2 = drive (γ ^ 2) B ω.1.1 :=
        congrArg Prod.snd hcfg
      rw [← h2]
      rfl
    have hy : avgReg (Y ω.1.1) = avgReg (rescale Z (Qc s) b) := havg
    have hex : ∀ t : ℝ, 0 ≤ t → ∃ p : ℂ,
        Tendsto (fun y : ℝ => fwdMapInv V t (y * Complex.I)) (𝓝[>] 0) (𝓝 p) := by
      intro t ht
      obtain ⟨C, hC⟩ := htr.2.2 ⌈t⌉₊
      exact ⟨_, RS.tendsto_fwdMapInv_of_rpow_bound hδ (hC t ⟨ht, Nat.le_ceil t⟩)⟩
    rw [hW, scaledDrv_eq hGV hb] at hl hGd hR3 hCD ⊢
    obtain ⟨e, he, hfree1, hfree2⟩ := hfree
    have hCX := ratCauchy_Z_of_X_e hFX hGc hZfc hGV left he hfree1 hfree2
    exact ratCauchy_y_of_Z hκ hFX hGc hZfc hGV hin.2.2.2.2.2.2 hS1 hb hy hFy hGd hl hex left
      hCD hR3 he hCX
  filter_upwards [hMain, A1RF.a1rfLoopUCStmt_holds γ P B Y hS hIn, ae_g1zDrvGood hS hIn, hIn.1,
    ae_continuousOn_smearFam_zero γ P B Y hS hIn left, ae_contData_sidePush γ P B Y hS hIn left]
    with ω hm h1 h2 h3 h4 h5
  exact hm h1 h2 h3.1.1 h4 h5

end A1RS
end R18
end QuantumZipper
