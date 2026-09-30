import QuantumZipper.Proofs.Zipper.SWCoreB8FFib
import QuantumZipper.Proofs.Zipper.SWCoreB8UoMain
import QuantumZipper.Proofs.Zipper.SWCoreB7dMain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-B8F (6): offset AC-fam from a pair (generic assembly), continuity in the offset

* `pairJc`: the dilated transported integral along a pair `(B', Y')` (the quantity of
  `rand_uc_off`);
* `awIntOff_contC`: at fixed scale `k` and time `s`, the offset transported test integral
  `awIntOff … s (k, c)` is continuous in the offset `c ∈ [1,2]` (regular witness of `h⁰_s`,
  `continuousOn_integral_bdryR`);
* **`acfam_off_of_pair`**: if a.s. the offset integrals of `h⁰` at rational times and rational
  offsets are the pair integrals (`hident`), then `awIntOff` is Cauchy along `goodFilter`
  uniformly in the rational times (the conclusion of `RegUnif.AnchorUnifFamOffStmt`): Cauchy
  across rational offsets from `rand_uc_off`, then all offsets by continuity at fixed `k`
  (`RegUnif.le_of_rat_dense_off`), then `RegUnif.offCauchyOn_goodFilter_of_explicit`.

Own bookkeeping (as `acfam_of_pair`, SWCoreB7dMain.lean).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace SWCore

open CharFun B2 B5 E1 E1.M4 RevMapExtension RegUnif

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The dilated transported integral along a pair `(B', Y')`. -/
def pairJc (κ τ : ℝ) (B' : ℝ≥0 → Ω → ℝ) (Y' : Ω → FieldSample) (ω : Ω) (u v : ℝ)
    (f : ℝ → ℝ) (σ c : ℝ) (k : ℕ) : ℝ :=
  ∫ x, RegUnif.awTest (realRevMap (vrev (drive κ B' ω) τ) (τ - σ)) u v f (c * x)
    ∂bdryApprox (Real.sqrt κ) (coordChange (ofFun (h0rev κ) + Y' ω)
      (fun z => revMapExt (vrev (drive κ B' ω) σ) σ ((c : ℂ) * z)) (Qc (Real.sqrt κ))) k

/-- **Continuity in the offset** at fixed scale and time. -/
theorem awIntOff_contC {κ T : ℝ} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample} (hκ : 0 < κ)
    (hκ4 : κ < 4) (hT : 0 < T) (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P)
    (hind : IndepFun (pathOf B) X P) (q : ℚ) (hq : (0 : ℝ) ≤ q) (hqT : (q : ℝ) ≤ T) (u v : ℚ) :
    ∀ᵐ ω ∂P, (u : ℝ) < v → (v : ℝ) < zeroMinus (Vr κ T B ω) (T - q) →
      ∀ f : ℝ → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ Ioo (u : ℝ) v →
        ∀ s ∈ Icc (q : ℝ) T, ∀ k : ℕ,
          ContinuousOn (fun c => awIntOff κ T B X ω u v f s (k, c)) (Icc (1 : ℝ) 2) := by
  filter_upwards [ae_forall_isRegularWith_joint (κ := κ) (γ := Real.sqrt κ) hB hX hind hT,
    ae_zeroMinus_Vr_facts RS.rohdeSchrammSimple hκ hκ4.le hT P B hB, hB.cont,
    ae_isSimpleCurveHull_revHull_Vr RS.rohdeSchrammSimple hκ hκ4.le hT P B hB]
    with ω hG hzm hcont hK huv hv f hf hfc hfs s hs k
  obtain ⟨G, -, hGr⟩ := hG
  obtain ⟨-, -, hanti, -, -, -⟩ := hzm
  set V := Vr κ T B ω with hVdef
  have hVc : Continuous V := continuous_vrev (drive_continuous hcont) T
  have hV0 : V 0 = 0 := vrev_zero hT.le
  have hzmle : zeroMinus V (T - q) ≤ zeroMinus V (T - s) :=
    hanti.antitoneOn ⟨by linarith [hs.2], by linarith [hs.1, hq]⟩
      ⟨by linarith, by linarith⟩ (by linarith [hs.1])
  have hlive : ∀ x ∈ Icc (u : ℝ) v, IsLive V (T - s) x := fun x hx =>
    (mem_liveNeg_of_lt_zeroMinus hVc hV0 hT hK (by linarith [hs.2]) (by linarith [hs.1, hq])
      ((hx.2.trans_lt hv).trans_le hzmle)).2
  obtain ⟨Φ, hΦ⟩ := exists_orderIso_eq_realRevMap hVc (by linarith [hs.2]) huv hlive
  have hsΦ : ∀ y ∈ Icc (u : ℝ) v, Φ y = realRevMap V (T - s) y := hΦ
  have hg : awTest (realRevMap V (T - s)) u v f = f ∘ Φ.symm := awTest_eq hsΦ hfs
  have hgc : Continuous (f ∘ Φ.symm) := hf.comp Φ.symm.toHomeomorph.continuous
  have hgs : HasCompactSupport (f ∘ Φ.symm) := hfc.comp_homeomorph Φ.symm.toHomeomorph
  have hreg : IsRegularWith (h0f κ s B X ω) (fun p => G (s, p)) := by
    rw [h0f_eq_unzippedField]; exact hGr s ⟨hq.trans hs.1, hs.2⟩
  have hC := GoodMeas.continuousOn_integral_bdryR (γ := Real.sqrt κ) hreg hgc hgs
  have hm : MapsTo (fun c : ℝ => c * radius k) (Icc (1 : ℝ) 2) (Ioi 0) := fun c hc =>
    mul_pos (by linarith [hc.1]) (radius_pos k)
  refine (hC.comp (continuous_id.mul continuous_const).continuousOn hm).congr fun c hc => ?_
  simp only [awIntOff, Function.comp, goodRad]
  rw [hg]
  rfl

/-- **Offset AC-fam from a pair** (generic assembly). -/
theorem acfam_off_of_pair {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {B : ℝ≥0 → Ω → ℝ}
    {X : Ω → FieldSample} {T : ℝ} {q : ℚ} (hqT : (q : ℝ) < T) {u v : ℚ} {i : ℕ} {a b c d : ℚ}
    (hua : (u : ℝ) < a) (hab : (a : ℝ) < b) (hbc : (b : ℝ) < c) (hcd : (c : ℝ) < d)
    (hdv : (d : ℝ) < v) {B' : ℝ≥0 → Ω → ℝ} {Y' : Ω → FieldSample} (hB' : IsBrownianReal B' P)
    (hY' : IsFreeGFFModConstH Y' P) (hind' : IndepFun (pathOf B') Y' P)
    (hident : ∀ᵐ ω ∂P, ∀ σ : ℚ, (σ : ℝ) ∈ Icc (0 : ℝ) (T - q) → ∀ e : ℚ,
      (e : ℝ) ∈ Icc (1 : ℝ) 2 → ∀ k : ℕ,
      awIntOff κ T B X ω u v (swFam i a b c d) ((q : ℝ) + σ) (k, e) =
        pairJc κ (T - q) B' Y' ω u v (swFam i a b c d) σ e k)
    (hlv : ∀ᵐ ω ∂P, (v : ℝ) < zeroMinus (Vr κ T B ω) (T - q) →
      ENNReal.ofReal (T - q) < realHitTime (vrev (drive κ B' ω) (T - q)) v)
    (hcont : ∀ᵐ ω ∂P, (v : ℝ) < zeroMinus (Vr κ T B ω) (T - q) → ∀ s ∈ Icc (q : ℝ) T,
      ∀ k : ℕ, ContinuousOn (fun e => awIntOff κ T B X ω u v (swFam i a b c d) s (k, e))
        (Icc (1 : ℝ) 2)) :
    ∀ᵐ ω ∂P, (v : ℝ) < zeroMinus (Vr κ T B ω) (T - q) →
      OffCauchyOn goodFilter (fun j s => awIntOff κ T B X ω u v (swFam i a b c d) s j)
        (Icc (q : ℝ) T ∩ range ((↑) : ℚ → ℝ)) := by
  by_cases hv0 : (v : ℝ) < 0
  swap
  · exact ae_of_all _ fun ω h => absurd (h.trans_le (zeroMinus_nonpos _ _)) hv0
  have hT' : 0 < T - q := by linarith
  have hfs := RegUnif.tsupport_swFam_subset (i := i) hab hcd
  have hfc : Continuous (RegUnif.swFam i a b c d) := RegUnif.continuous_swFam _ _ _ _ _
  filter_upwards [rand_uc_off κ hB' hY' hind' hκ hκ4 hT' (u := u) (v := v) (by linarith) hv0 hua
      (by linarith) hdv hfc hfs, hident, hlv, hcont] with ω hω hid hl hc hvz
  have hU := hω (hl hvz)
  set A : ℕ × ℝ → ℝ → ℝ := fun j s => awIntOff κ T B X ω u v (swFam i a b c d) s j with hA
  refine offCauchyOn_goodFilter_of_explicit fun ε hε => ?_
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  obtain ⟨N, hN⟩ := hU n
  refine ⟨N, fun k hk k' hk' e he e' he' s hs => ?_⟩
  obtain ⟨r, hr⟩ := hs.2
  set σ : ℚ := r - q with hσdef
  have hσI : (σ : ℝ) ∈ Icc (0 : ℝ) (T - q) := by
    rw [hσdef]; push_cast
    exact ⟨by linarith [hs.1.1, hr.symm ▸ hs.1.1], by linarith [hs.1.2, hr.symm ▸ hs.1.2]⟩
  have hsσ : s = (q : ℝ) + σ := by rw [← hr, hσdef]; push_cast; ring
  have hrat : ∀ e₁ : ℚ, (e₁ : ℝ) ∈ Icc (1 : ℝ) 2 → ∀ e₂ : ℚ, (e₂ : ℝ) ∈ Icc (1 : ℝ) 2 →
      |A (k, e₁) s - A (k', e₂) s| ≤ 1 / ((n : ℝ) + 1) := by
    intro e₁ he₁ e₂ he₂
    simp only [hA]
    rw [hsσ, hid σ hσI e₁ he₁ k, hid σ hσI e₂ he₂ k']
    exact hN k hk k' hk' σ hσI e₁ he₁ e₂ he₂
  have hcs := hc hvz s hs.1
  have e1 : ((1 : ℚ) : ℝ) = 1 := Rat.cast_one
  have h1 : ∀ e₂ : ℚ, (e₂ : ℝ) ∈ Icc (1 : ℝ) 2 → ∀ e₁ ∈ Icc (1 : ℝ) 2,
      |A (k, e₁) s - A (k', e₂) s| ≤ 1 / ((n : ℝ) + 1) := by
    intro e₂ he₂ e₁ he₁
    have := le_of_rat_dense_off (q := 1) (T := 2)
      (g := fun e₁ => |A (k, e₁) s - A (k', e₂) s|) (δ := 1 / ((n : ℝ) + 1))
      (by rw [e1]; exact ((hcs k).sub continuousOn_const).abs)
      (fun r hr => hrat r (by rwa [e1] at hr) e₂ he₂)
    exact this e₁ (by rw [e1]; exact he₁)
  have h2 : ∀ e₁ ∈ Icc (1 : ℝ) 2, ∀ e₂ ∈ Icc (1 : ℝ) 2,
      |A (k, e₁) s - A (k', e₂) s| ≤ 1 / ((n : ℝ) + 1) := by
    intro e₁ he₁ e₂ he₂
    have := le_of_rat_dense_off (q := 1) (T := 2)
      (g := fun e₂ => |A (k, e₁) s - A (k', e₂) s|) (δ := 1 / ((n : ℝ) + 1))
      (by rw [e1]; exact (continuousOn_const.sub (hcs k')).abs)
      (fun r hr => h1 r (by rwa [e1] at hr) e₁ he₁)
    exact this e₂ (by rw [e1]; exact he₂)
  exact lt_of_le_of_lt (h2 e he e' he') hn

end SWCore
end QuantumZipper
