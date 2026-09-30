import QuantumZipper.Proofs.Thm14.WeldRead
import QuantumZipper.Proofs.Zipper.TReg

/-!
# FCR-PAIR, part 1: reduction of `FcRPairingLimit` to a fixed driver

`Thm14WDG.FcRPairingLimit` asks for one deterministic sequence of mass-zero test functions
`ρ j` whose pairings with `h = couplingFieldRev κ (√κ B) T X` converge in probability to the
balanced semicircle value `h(fc(d, 2^{-k})) - h(fc(0, 1))`.

Here we reduce it to the **fixed-driver** statement `FcRFixedLimit`: the same sequence `ρ`
(chosen before the driver) works for every deterministic continuous driver path
`f : C([0,T], ℝ)` (driver `W = Wof κ T hT f`) and every free field `X`.  The reduction
conditions on the driver: since `B` and `X` are independent, the law of `(pathC B, X)` is a
product, so `P(ε ≤ |D_j|) = ∫ P(ε ≤ |D_j(f, X)|) d(law of the path)(f)`, and dominated
convergence (bound `1`) gives the unconditional limit (`tendstoInMeasure_of_indep`).

Own elementary argument (Fubini/Tonelli for the product law plus dominated convergence); the
measurability of the events comes from `CharFun.measurable_pair_Y2f` and `TReg.measurable_valFC`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace Thm14WDG

open CharFun

/-- **Fixed-driver form of `FcRPairingLimit`.** The test sequence `ρ` is chosen before the driver
path `f`; for every deterministic continuous driver and every free field `X`, the pairings of
`h = couplingFieldRev κ (Wof κ T hT f) T X` with `ρ j` converge in probability to the balanced
semicircle value `h(fc(d, 2^{-k})) - h(fc(0, 1))`. -/
def FcRFixedLimit : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ T : ℝ, ∀ hT : 0 < T, ∀ (d : ℝ) (k : ℕ), ∃ ρ : ℕ → TestFun0 H,
    ∀ (f : C(Icc (0 : ℝ) T, ℝ)) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (X : Ω → FieldSample), IsFreeGFFModConstH X P →
      TendstoInMeasure P
        (fun j ω => pairRaw (couplingFieldRev κ (Wof κ T hT.le f) T (X ω)) (ρ j).1.1) atTop
        (fun ω => couplingFieldRev κ (Wof κ T hT.le f) T (X ω) (foldedCircle (d : ℂ) (radius k)) -
          couplingFieldRev κ (Wof κ T hT.le f) T (X ω) (foldedCircle 0 1))

/-- **Conditioning on an independent coordinate.** If `g` and `Y` are independent and, for every
fixed value `a` of `g`, `F j (a, Y) → G (a, Y)` in probability, then `F j (g, Y) → G (g, Y)` in
probability (Tonelli for the product law and dominated convergence with bound `1`). -/
theorem tendstoInMeasure_of_indep {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {g : Ω → α}
    {Y : Ω → β} (hg : Measurable g) (hY : Measurable Y) (hind : IndepFun g Y P)
    {F : ℕ → α × β → ℝ} {G : α × β → ℝ} (hF : ∀ j, Measurable (F j)) (hG : Measurable G)
    (h : ∀ a, TendstoInMeasure P (fun j ω => F j (a, Y ω)) atTop (fun ω => G (a, Y ω))) :
    TendstoInMeasure P (fun j ω => F j (g ω, Y ω)) atTop (fun ω => G (g ω, Y ω)) := by
  intro ε hε
  have hprod := (indepFun_iff_map_prod_eq_prod_map_map hg.aemeasurable hY.aemeasurable).1 hind
  set E : ℕ → Set (α × β) := fun j => {p | ε ≤ edist (F j p) (G p)} with hE
  have hEm : ∀ j, MeasurableSet (E j) := fun j =>
    measurableSet_le measurable_const ((hF j).edist hG)
  have key : ∀ j, P {ω | ε ≤ edist (F j (g ω, Y ω)) (G (g ω, Y ω))} =
      ∫⁻ a, P {ω | ε ≤ edist (F j (a, Y ω)) (G (a, Y ω))} ∂(P.map g) := by
    intro j
    have h1 : P {ω | ε ≤ edist (F j (g ω, Y ω)) (G (g ω, Y ω))} =
        (P.map fun ω => (g ω, Y ω)) (E j) := by
      rw [Measure.map_apply (hg.prodMk hY) (hEm j)]; rfl
    rw [h1, hprod, Measure.prod_apply (hEm j)]
    refine lintegral_congr fun a => ?_
    rw [Measure.map_apply hY (measurable_prodMk_left (hEm j))]
    rfl
  simp_rw [key]
  have hlim := tendsto_lintegral_of_dominated_convergence (μ := P.map g)
    (F := fun j a => P {ω | ε ≤ edist (F j (a, Y ω)) (G (a, Y ω))}) (f := fun _ => 0)
    (fun _ => 1) (fun j => ?_) (fun j => ae_of_all _ fun a => prob_le_one)
    (by simp) (ae_of_all _ fun a => h a ε hε)
  · simpa using hlim
  · have hm := measurable_measure_prodMk_left (ν := P.map Y) (hEm j)
    convert hm using 1
    funext a
    show _ = (P.map Y) (Prod.mk a ⁻¹' E j)
    rw [Measure.map_apply hY (measurable_prodMk_left (hEm j))]
    rfl

/-- **FCR-PAIR reduction.** The fixed-driver statement implies `FcRPairingLimit`. -/
theorem fcRPairingLimit_of_fixed (hF : FcRFixedLimit) : FcRPairingLimit := by
  intro κ hκ hκ4 T hT Ω _ P _ B X hB hX hind d k
  obtain ⟨ρ, hρ⟩ := hF κ hκ hκ4 T hT d k
  refine ⟨ρ, ?_⟩
  obtain ⟨B₁, hB₁m, hB₁c, hB₁eq⟩ := exists_good_version hB
  have hind₁ : IndepFun (pathOf B₁) X P :=
    hind.congr (hB₁eq.mono fun ω h => (funext fun s => (h s).symm : pathOf B ω = pathOf B₁ ω))
      (ae_eq_refl _)
  have hXm : Measurable X := measurable_pi_iff.2 hX.measurable_coord
  have hgm := measurable_pathC T hB₁m hB₁c
  have hig := indepFun_pathC T hind₁ hB₁c
  have hmain := tendstoInMeasure_of_indep (P := P) hgm hXm hig
    (F := fun j p => pairRaw (Y2f κ T hT.le p.1 p.2) (ρ j).1.1)
    (G := fun p => TReg.valFC κ T hT.le (d : ℂ) (radius k) p - TReg.valFC κ T hT.le 0 1 p)
    (fun j => measurable_pair_Y2f κ T hT.le (ρ j).1)
    ((TReg.measurable_valFC κ T hT.le _ _).sub (TReg.measurable_valFC κ T hT.le _ _))
    (fun f => by
      refine (hρ f P X hX).congr (fun j => ae_of_all _ fun ω => ?_) (ae_of_all _ fun ω => ?_)
      · show _ = pairRaw (Y2f κ T hT.le f (X ω)) (ρ j).1.1
        rw [TReg.Y2f_eq]
      · show _ = TReg.valFC κ T hT.le (d : ℂ) (radius k) (f, X ω) -
          TReg.valFC κ T hT.le 0 1 (f, X ω)
        rw [TReg.valFC_eq κ T hT.le _ (radius_pos k), TReg.valFC_eq κ T hT.le _ one_pos])
  have hfield : ∀ᵐ ω ∂P, couplingFieldRev κ (drive κ B ω) T (X ω) =
      Y2f κ T hT.le (pathC T B₁ hB₁c ω) (X ω) := by
    filter_upwards [hB₁eq] with ω hb
    have e : drive κ B ω = drive κ B₁ ω := funext fun s => by simp only [drive, hb]
    rw [TReg.Y2f_eq, e]
    unfold couplingFieldRev
    rw [revMap_drive_eq κ T hT.le B₁ hB₁c ω]
  refine hmain.congr (fun j => hfield.mono fun ω h => ?_) (hfield.mono fun ω h => ?_)
  · rw [TReg.Y2f_eq] at h
    simp only [h, TReg.Y2f_eq]
  · rw [TReg.Y2f_eq] at h
    simp only [h]
    rw [TReg.valFC_eq κ T hT.le _ (radius_pos k), TReg.valFC_eq κ T hT.le _ one_pos]

end Thm14WDG
end QuantumZipper
