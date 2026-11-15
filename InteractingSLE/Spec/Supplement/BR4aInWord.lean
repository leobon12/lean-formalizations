/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.BR4aInWordThr
import InteractingSLE.Spec.Supplement.BR4aInClock
import InteractingSLE.Spec.Supplement.BR4aPath

/-!
# Corollary BR4a's relative words (`BR4aWordDetStatement`) and the relative chain

Packet PROVE-T14-BR4A3. Supplement p. 610, Corollary BR4a, (BR4a.1)–(BR4a.2) and "The original and transformed stopped
histories recover each other, every force label, and both half-plane-capacity clocks".

* `exists_conjData`: at every original time before the first visit, the relative chain of `BR4aChain.relDrv` is
  conjugated to the original one (`ConjData`, from `exists_conj` and `BR4aChain.relDrv_spec`);
* **`br4aWordDetStatement`**: `BR4aChain.BR4aWordDetStatement` is PROVED (no hypotheses): (2) no relative
  continuation threshold at any relative time (`ConjData.not_threshold` at the original time with the same clock
  value, `BR4aPath.isExhaustingClock_clock`); (1) is (2) at relative time `0`; (3) is `ConjData.mean_eq`;
* **`br4aRelChainStatement_of_theorem13`**: `Exist.Theorem13Statement.{u} → BR4aRelChainStatement.{u}` (with
  `BR4aIn.br4aClockStatement_of_theorem13`);
* `br4aHullDetStatement_of_thm12_thm13`, **`br4aStatement_of_thm12_thm13`**: Corollary BR4a (`BR4a.BR4aStatement`)
  from Theorems 1.2–1.3 (R48: permitted roots of Theorem 1.4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open QuantumZipper (H fwdHull chiC)
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.BR4aIn

open BR4aPath BR4aChain ConformalImage ConformalImageFull Supp8.HullDetGen Sec5.CrossRestart MartChar.RealFlow

/-- **The conjugation data of BR4a's relative chain** at an original time before the first visit. -/
theorem exists_conjData {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0) {γ : ℝ≥0 → ℂ}
    (hγ : IsGeneratingTrace w ⊤ γ) {v : ℝ} (hv : v ≠ 0) (hvis : (v : ℂ) ∈ infinitySourceChart.tipSet w ⊤)
    (hclk : ∀ M : ℝ, ∃ t : ℝ≥0, (t : ℝ≥0∞) < firstTipTime infinitySourceChart w {(v : ℂ)} ∧
      M ≤ clock v (fun s : ℝ => w s.toNNReal) t)
    {t : ℝ≥0} (ht : (t : ℝ≥0∞) < firstTipTime infinitySourceChart w {(v : ℂ)})
    (hq : 0 ≤ clock v (fun s : ℝ => w s.toNNReal) t) :
    ∃ α κN P : ℝ, ConjData (fun s : ℝ => w s.toNNReal) (fun s : ℝ => relDrv v w s.toNNReal) t
      (clock v (fun s : ℝ => w s.toNNReal) t) v α κN P := by
  obtain ⟨-, -, hrc, hr0, hhull⟩ := relDrv_spec hw hw0 hγ hv hvis hclk
  obtain ⟨-, -, -, hsep⟩ := exists_firstTipTime_notMem hw hw0 hγ hv hvis
  have hwr : Continuous fun s : ℝ => w s.toNNReal := hw.comp continuous_real_toNNReal
  have hwr0 : (fun s : ℝ => w s.toNNReal) 0 = 0 := by simp [hw0]
  have hur : Continuous fun s : ℝ => relDrv v w s.toNNReal := hrc.comp continuous_real_toNNReal
  have hur0 : (fun s : ℝ => relDrv v w s.toNNReal) 0 = 0 := by simp [hr0]
  have hK : ∀ s ∈ Icc (0 : ℝ) t,
      fwdHull (fun s : ℝ => relDrv v w s.toNNReal) (clock v (fun s : ℝ => w s.toNNReal) s) =
        mob v '' fwdHull (fun s : ℝ => w s.toNNReal) s := by
    intro s hs
    have hst : (s.toNNReal : ℝ≥0∞) < firstTipTime infinitySourceChart w {(v : ℂ)} := by
      refine lt_of_le_of_lt ?_ ht
      exact_mod_cast Real.toNNReal_le_iff_le_coe.2 hs.2
    have h1 := (hhull s.toNNReal hst).1
    rwa [Real.coe_toNNReal _ hs.1] at h1
  obtain ⟨α, κN, P, hκN, hP, hdrv, hconj⟩ := exists_conj hwr hwr0 hur hur0 hv t.coe_nonneg (hsep t ht) hK
  exact ⟨α, κN, P, ⟨hwr, hwr0, hur, hur0, t.coe_nonneg, hq, hv, hκN, ((hhull t ht).1).symm, hconj, hsep t ht, hP,
    hdrv⟩⟩

/-- **The words of BR4a's relative chain, one sample** (`BR4aWordDetStatement`): PROVED. -/
theorem br4aWordDetStatement : BR4aWordDetStatement := by
  intro κ hκ _ b' J' hb' v hv c _ h0 w vL vR bm hpath γ hγ htr hvis hclk
  have hκ' : 0 < 16 / κ := div_pos (by norm_num) hκ
  have hlt : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ⊤ := fun t => ENNReal.coe_lt_top
  have hw : Continuous w := continuousOn_univ.1 (hpath.isForcePath.continuousOn_w.mono fun t _ => hlt t)
  have hw0 : w 0 = 0 := hpath.1
  obtain ⟨-, -, hrc, hr0, hhull⟩ := relDrv_spec hw hw0 hγ hv hvis hclk
  obtain ⟨T₀, hT, hγT, hT0, -⟩ := exists_firstTipTime_eq hγ hw hw0 hv hvis
  have hEx := isExhaustingClock_clock hγ hw hw0 htr hrc hv hT0 hγT fun t ht =>
    (hhull t (by rw [hT]; exact_mod_cast ht)).1
  rw [hT] at hhull
  set wr : ℝ → ℝ := fun s => w s.toNNReal with hwrdef
  set ur : ℝ → ℝ := fun s => relDrv v w s.toNNReal with hurdef
  have hur : Continuous ur := hrc.comp continuous_real_toNNReal
  have hur0 : ur 0 = 0 := by simp [hurdef, hr0]
  have hconjAt : ∀ t : ℝ≥0, (t : ℝ≥0∞) < T₀ → ∃ α κN P : ℝ, ConjData wr ur t (clock v wr t) v α κN P := by
    intro t ht
    have ht' : (t : ℝ≥0∞) < firstTipTime infinitySourceChart w {(v : ℂ)} := by rw [hT]; exact ht
    exact exists_conjData hw hw0 hγ hv hvis hclk ht' (hEx.nonneg ht)
  -- the original force processes are the flows
  have hvL : ∀ (t : ℝ≥0) i, vL i t = -rightImg (fun s => -wr s) (-flowLineXL b' J' 0 i) t := fun t i =>
    WangWu.vL_eq_neg_rightImg hpath hw (hlt t) i
  have hvR : ∀ (t : ℝ≥0) j, vR j t = rightImg wr (flowLineXR b' J' 0 j) t := fun t j =>
    WangWu.vR_eq_rightImg hpath hw (hlt t) j
  have hwt : ∀ t : ℝ≥0, w t = wr t := fun t => by simp [hwrdef]
  have hut : ∀ q : ℝ≥0, relDrv v w q = ur q := fun q => by simp [hurdef]
  -- no relative threshold at any relative time
  have hnoThr : ∀ q : ℝ≥0, ¬ ForceWord.ThresholdCondition (flowLineRhoL (16 / κ) c.fn c.jumps 0 0)
      (flowLineRhoR (16 / κ) c.fn c.jumps 0 0) (relDrv v w q)
      (fun i => -rightImg (fun s : ℝ => -relDrv v w s.toNNReal) (-flowLineXL c.fn c.jumps 0 i) q)
      (fun j => rightImg (fun s : ℝ => relDrv v w s.toNNReal) (flowLineXR c.fn c.jumps 0 j) q) := by
    intro q
    obtain ⟨t, ht, hq⟩ := hEx.exists_eq q
    obtain ⟨α, κN, P, hc⟩ := hconjAt t ht
    have hnt0 := hpath.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 t (hlt t)
    have hnt : ¬ ForceWord.ThresholdCondition (flowLineRhoL (16 / κ) b' J' 0 0) (flowLineRhoR (16 / κ) b' J' 0 0)
        (wr t) (fun i => -rightImg (fun s => -wr s) (-flowLineXL b' J' 0 i) t)
        (fun j => rightImg wr (flowLineXR b' J' 0 j) t) := by
      have eL : (fun i => vL i t) = fun i => -rightImg (fun s => -wr s) (-flowLineXL b' J' 0 i) t :=
        funext fun i => hvL t i
      have eR : (fun j => vR j t) = fun j => rightImg wr (flowLineXR b' J' 0 j) t := funext fun j => hvR t j
      rw [eL, eR, hwt] at hnt0
      exact hnt0
    have h1 := hc.not_threshold hκ' hb' h0 hnt
    rw [hq] at h1
    rw [hut]
    exact h1
  refine ⟨?_, ?_, ?_⟩
  · -- (1): the seed, i.e. (2) at relative time `0`
    have hordc := Theorem15.isOrderedForceWord_flowLine c.fn c.jumps 0
    have h1 := hnoThr 0
    have hun : Continuous fun s => -ur s := hur.neg
    have eL : (fun i => -rightImg (fun s : ℝ => -relDrv v w s.toNNReal) (-flowLineXL c.fn c.jumps 0 i)
        ((0 : ℝ≥0) : ℝ)) = flowLineXL c.fn c.jumps 0 := funext fun i => by
      rw [NNReal.coe_zero, rightImg_zero (w := fun s => -ur s) hun (by simp [hur0]) (neg_nonneg.2 (hordc.2.1 i)),
        neg_neg]
    have eR : (fun j => rightImg (fun s : ℝ => relDrv v w s.toNNReal) (flowLineXR c.fn c.jumps 0 j)
        ((0 : ℝ≥0) : ℝ)) = flowLineXR c.fn c.jumps 0 := funext fun j => by
      rw [NNReal.coe_zero]
      exact rightImg_zero hur hur0 (hordc.2.2.2 j)
    rw [eL, eR, hr0] at h1
    exact h1
  · -- (2): no threshold at any relative time
    unfold MartChar.thresholdTime
    split_ifs with hne
    · obtain ⟨q, hq⟩ := hne
      exact absurd hq (hnoThr q)
    · rfl
  · -- (3): the coupling-mean identity
    intro t ht z hz
    have ht' : (t : ℝ≥0∞) < T₀ := by rw [← hT]; exact ht
    obtain ⟨α, κN, P, hc⟩ := hconjAt t ht'
    have hq0 : 0 ≤ clock v wr t := hEx.nonneg ht'
    rw [Real.coe_toNNReal _ hq0] at hz ⊢
    have hz' : mobInv v z ∈ H \ fwdHull wr t := by
      refine ⟨mobInv_mem_H v hz.1, fun hzK => hz.2 ?_⟩
      rw [← hc.hK, ← mob_mobInv v hz.1]
      exact mem_image_of_mem _ hzK
    have hmean := hc.mean_eq hκ' hb' h0 (mobInv v z) hz'
    rw [mob_mobInv v hz.1] at hmean
    have eO : LocalExt.bheAt (16 / κ) (flowLineRhoL (16 / κ) b' J' 0 0) (flowLineRhoR (16 / κ) b' J' 0 0)
        (fun i => vL i t - w t) (fun j => vR j t - w t) = flowExt (16 / κ) b' J' wr t := by
      unfold flowExt
      congr 1
      · exact funext fun i => by rw [hvL, hwt]
      · exact funext fun j => by rw [hvR, hwt]
    have eR : relDrv v w (clock v wr t).toNNReal = ur (clock v wr t) := rfl
    rw [eO, add_zero, eR]
    exact hmean.symm

/-- **BR4a's relative chain from Theorem 1.3** (`BR4aRelChainStatement`): the clock input from Theorem 1.3
(`br4aClockStatement_of_theorem13`) and the word input (`br4aWordDetStatement`, no hypotheses). -/
theorem br4aRelChainStatement_of_theorem13 (h13 : Exist.Theorem13Statement.{u}) :
    BR4aRelChainStatement.{u} :=
  br4aRelChainStatement_of_clock_det (br4aClockStatement_of_theorem13 h13) br4aWordDetStatement h13

/-- **BR4a's hull identity from Theorems 1.2–1.3** (at the sample space's universe and at `0`). -/
theorem br4aHullDetStatement_of_thm12_thm13 (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0}) : BR4aHullDetStatement.{u} :=
  br4aHullDetStatement_of_relChain (br4aRelChainStatement_of_theorem13 h13) h12 h13 h12₀ h13₀

/-- **Corollary BR4a from Theorems 1.2–1.3** (`BR4a.BR4aStatement`). -/
theorem br4aStatement_of_thm12_thm13 (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0}) : BR4a.BR4aStatement.{u} :=
  br4aStatement_of_hullDet (br4aHullDetStatement_of_thm12_thm13 h12 h13 h12₀ h13₀) h12 h13

end InteractingSLE.Theorem14.BR4aIn
