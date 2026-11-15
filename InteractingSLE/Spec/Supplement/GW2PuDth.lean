/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2PvDth
import InteractingSLE.Spec.Supplement.GW2RnWin
import InteractingSLE.Spec.Supplement.GW2PsmVer
import InteractingSLE.Spec.Supplement.GW2aPieceChart
import InteractingSLE.Spec.Supplement.GW1PieceChart
import InteractingSLE.Foundations.Loewner.YuanCorollary13Slit
import InteractingSLE.Spec.Supplement.GW2NuExp

/-!
# The death clause of D46's export at one sample, positive lifetime, at a root `x ≥ 0`

Packet PROVE-GW2-STAGEMEAN, R124 round (D72: STAGEMEAN ports its positive-lifetime death clause to the roots
`x ∈ lowerArcRoots`, with ROOTX's round-13 substitution table). `GW2Pv.sample_death_root0` at a root `x ≥ 0`: the
union `schedUnionX` and the chart `relChartX x s rec`, the explored trace read at `x + η`, GEOM2's
`sample_trace_corrX`, `sample_stage_geomX`, `isDomainChart_stgChart_relChartX`; the rest unchanged.

* **`sample_death_rootX`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMap fwdMapInv fwdHull chiC)

namespace InteractingSLE.Theorem14.GW2Pu

open GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2TipSystem.Swc GW2Schedule GW2Tip Exist Exist.Staged
  Exist.StagedLaw Sec5.Prop513Schedule GW2Omx Supp8.GB6LMean MartChar.RealFlow Restart Supp8.Q3Chain GW2Fb
  GW2JointKernel Sec5.CrossCond.StagedRepLater
open Supp8.GB6 (relMap gb6Rec relClock sphereInv firstContactTime)
open Supp8.Q3Rel (invHull relLog)

/-- **The death clause at one sample, positive lifetime** (root `x ≥ 0`). -/
theorem sample_death_rootX {Ω : Type*} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (hx0 : 0 ≤ rootPt r.1)
    (hord : (historyProgram c r l).Pairwise (fun p q => p.2 < q.2)) (hs0 : 0 < c.s) (ω : Ω)
    (hold : oldSuccess c r l ω)
    (hgood : ∀ (j : ℕ) (hj : j < (futureProgram c r l a).length), LocalExt.IsDrvGood
      (recHist (programRecords c (rootPt r.1) (futureProgram c r l a) ω ⟨j, hj⟩)))
    {cL : Chart} {θ : ℝ} (hl : GW2Olm.curLaunch c r l a ω = some (cL, θ))
    (hc : ∀ j < GW2Olm.curIdx c r l + 1, Continuous (stopDrv (specDelta (GW2Olm.futSpec c r l a) j)
        (GW2Olm.futFam c r l a j ω)) ∧ stopDrv (specDelta (GW2Olm.futSpec c r l a) j) (GW2Olm.futFam c r l a j ω) 0 = 0)
    (hconf : cL.IsConformal) (hext : GW1P.HasProperBdryExt cL)
    (hreg : IsRegularDriver (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω)) {α : ℝ≥0 → ℂ}
    (hα : IsGeneratingTrace (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).1
      (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).2 α)
    {Wk : ℝ≥0 → ℝ} {γk : ℝ≥0 → ℂ} (hWk : Continuous Wk) (hWk0 : Wk 0 = 0) (hγk : IsGeneratingTrace Wk ⊤ γk)
    (hγk0 : ∀ q : ℝ≥0, 0 < q → γk q ≠ 0)
    (hW' : Continuous fun u => c.W u ω) (hW'0 : c.W 0 ω = 0) (hcα : IsGeneratingTrace (fun u => c.W u ω) ⊤ (c.α ω))
    (hcα0 : ∀ v : ℝ≥0, 0 < v → c.α ω v ≠ 0) (hsζ : (c.s : ℝ≥0∞) < c.ζ ω)
    (hηe : IsGeneratingTrace (fun u => GW2Rd.schedW c r l a u ω) ⊤ (GW2Rd.schedTr c r l a ω))
    (hce : Continuous fun u => GW2Rd.schedW c r l a u ω) (h0e : GW2Rd.schedW c r l a 0 ω = 0)
    {ℓ : ℝ≥0 → ℝ≥0} (hℓc : Continuous ℓ) (hℓm : StrictMono ℓ)
    (hℓr : range ℓ = {q : ℝ≥0 | (q : ℝ≥0∞) < firstTipTime infinitySourceChart (fun u => c.W u ω)
      ((fun z : ℂ => (rootPt r.1 : ℂ) + z) '' (GW2Rd.schedTr c r l a ω '' Icc 0 (historyTime c r l)))})
    (hvis : 0 < rootPt r.1 → ∃ τ, (rootPt r.1 : ℂ) * c.α ω τ + 1 = 0)
    (hiff : ∀ (q : ℝ≥0) (z : ℂ), (cL.trans infinitySourceChart).tipAt Wk q z ↔
      infinitySourceChart.tipAt (fun u => c.W u ω) (ℓ q) z) {t₀ : ℝ≥0} (ht₀ : ℓ t₀ = c.s) (hγkH : γk t₀ ∈ H)
    {wr : ℝ≥0 → ℝ} {ηr : ℝ≥0 → ℂ} (hwr : Continuous wr) (hwr0 : wr 0 = 0)
    (hwrW : ∀ t : ℝ≥0, (t : ℝ≥0∞) < (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).2 →
      wr t = (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).1 t)
    (hηr : IsGeneratingTrace wr ⊤ ηr)
    (hηrα : ∀ u : ℝ≥0, (u : ℝ≥0∞) ≤ (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).2 → ηr u = α u)
    {ℓ₀ : ℝ≥0} (hℓ₀ : (ℓ₀ : ℝ≥0∞) = (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).2) (hℓ₀pos : 0 < ℓ₀)
    (hℓ₀cap : ℓ₀ ≤ candidateCap c r a)
    (hnc : ∀ v ∈ Icc 0 c.s, ∀ u' ≤ historyTime c r l + ℓ₀,
      c.α ω v * ((rootPt r.1 : ℂ) + GW2Rd.schedTr c r l a ω u') + 1 ≠ 0)
    {C : ℝ≥0 → ℝ} (hCc : ContinuousOn C (Icc 0 ℓ₀)) {S : ℝ≥0}
    {Rf : ℕ → ℝ≥0 → ℝ} {Vf : ℕ → ℝ≥0∞} (hRc : ∀ n, Continuous (Rf n)) (hR0 : ∀ n, Rf n 0 = 0)
    (hagree : ∀ (n m : ℕ) (q : ℝ≥0), (q : ℝ≥0∞) < Vf n → (q : ℝ≥0∞) < Vf m → Rf n q = Rf m q)
    {An : ℕ → ℝ≥0 → ℝ≥0} (hAn0 : ∀ n, (S : ℝ≥0∞) < Vf n → An n 0 = S) (hAm : ∀ n, Monotone (An n))
    (hAc : ∀ n, Continuous (An n)) (hreach : ∀ n, Vf n ≤ (An n ℓ₀ : ℝ≥0∞))
    (hAC : ∀ n u, (An n u : ℝ≥0∞) < Vf n → (An n u : ℝ) = C u)
    (hexh : ∀ u : ℝ≥0, 0 < u → u < ℓ₀ → ∃ n, (S : ℝ≥0∞) < Vf n ∧ (An n u : ℝ≥0∞) < Vf n)
    (hshape : ∀ n u, (An n u : ℝ≥0∞) < Vf n → H \ GW2Rd.schedUnionX c r l a (historyTime c r l) u ω =
      (GW2Rz.relChartX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω)).2.1 '' (H \ fwdHull (Ito.rpath (Rf n)) (An n u)))
    {j : ℕ} (hSj : (S : ℝ≥0∞) < Vf j) {lam : ℝ} (hlam : 0 < lam)
    (hdil : ∀ x ∈ ((GW2Rd.stgChart (GW2Rz.relChartX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω)) (Rf j) S).dom : Set ℂ),
      relMap (fun q : ℝ => Wk q.toNNReal) (t₀ : ℝ) (cL.1 x) =
        (lam : ℂ) * (GW2Rd.stgChart (GW2Rz.relChartX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω)) (Rf j) S).1 x) :
    (ℓ₀ : ℝ≥0∞) < firstContactTime (fun v => sphereInv (ηr v : OnePoint ℂ))
        ((fun v => (γk v : OnePoint ℂ)) '' Icc 0 t₀) ∧
      lam ^ 2 * (C ℓ₀ - S) = relClock (fun q : ℝ => Wk q.toNNReal) t₀ (fun q : ℝ => wr q.toNNReal) ℓ₀ ∧
      ∃ Wd : ℝ≥0 → ℝ, Continuous Wd ∧ Wd 0 = 0 ∧ (∀ (n : ℕ) (q : ℝ≥0), (q : ℝ≥0∞) < Vf n → Rf n q = Wd q) ∧
        ∀ t : ℝ≥0, t ≤ ℓ₀ →
          fwdHull (scD lam (fun q : ℝ => GW2Rd.stgDrv Wd S q.toNNReal))
              (relClock (fun q : ℝ => Wk q.toNNReal) t₀ (fun q : ℝ => wr q.toNNReal) t) =
            relMap (fun q : ℝ => Wk q.toNNReal) t₀ '' fwdHull (fun q : ℝ => wr q.toNNReal) t := by
  classical
  set ζ := (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).2 with hζdef
  set Uk : ℝ → ℝ := fun q : ℝ => Wk q.toNNReal with hUk
  set Wc : ℝ → ℝ := fun q : ℝ => (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).1 q.toNNReal with hWc
  set wr' : ℝ → ℝ := fun q : ℝ => wr q.toNNReal with hwr'
  have hUkc : Continuous Uk := hWk.comp continuous_real_toNNReal
  have hUk0 : Uk 0 = 0 := by simp [hUk, hWk0]
  have hℓ0 : ℓ 0 = 0 := GW2Sgk.clock_zero_of_range hℓm hℓr
  have hlt_ζ : ∀ u : ℝ≥0, u < ℓ₀ → (u : ℝ≥0∞) < ζ := fun u hu => by rw [← hℓ₀]; exact_mod_cast hu
  -- (a) the trace correspondence up to the death, and the contact after it
  obtain ⟨f, -, hf, -⟩ := id hext
  have hηrc : Continuous ηr := continuousOn_univ.1 (hηr.2.1.mono fun q _ => show (q : ℝ≥0∞) ≤ ⊤ from le_top)
  have hηrH : ∀ u, ηr u ∈ Hbar := GW2aPiece.trace_mem_Hbar hηr hwr hwr0
  have hfc : ContinuousOn f Hbar := GW1P.continuousOn_of_tendsto hf
  have htr_lt : ∀ u : ℝ≥0, u < ℓ₀ →
      (rootPt r.1 : ℂ) + GW2Rd.schedTr c r l a ω (historyTime c r l + u) = f (ηr u) := by
    intro u hu
    obtain ⟨f', hf', htr'⟩ := GW2Kx.sample_trace_corrX c r l a hord u ω hold hgood hl hc hext
      (hu.trans_le hℓ₀cap) (hlt_ζ u hu) hreg hα hηe
    rw [htr' u le_rfl, ← hηrα u (hlt_ζ u hu).le]
    have := GW1P.neBot_nhdsWithin_H (hηrH u)
    exact tendsto_nhds_unique (hf' _ (hηrH u)) (hf _ (hηrH u))
  have hηec : Continuous (GW2Rd.schedTr c r l a ω) :=
    continuousOn_univ.1 (hηe.2.1.mono fun q _ => show (q : ℝ≥0∞) ≤ ⊤ from le_top)
  have htr : ∀ u ≤ ℓ₀, (rootPt r.1 : ℂ) + GW2Rd.schedTr c r l a ω (historyTime c r l + u) = f (ηr u) := by
    intro u hu
    rcases hu.lt_or_eq with h | h
    · exact htr_lt u h
    subst h
    have : (𝓝[<] u).NeBot := mem_closure_iff_nhdsWithin_neBot.1
      (by rw [closure_Iio' (show (Iio u).Nonempty from ⟨0, hℓ₀pos⟩)]; exact Set.self_mem_Iic)
    have hlim1 : Tendsto (fun v => (rootPt r.1 : ℂ) + GW2Rd.schedTr c r l a ω (historyTime c r l + v)) (𝓝[<] u)
        (𝓝 ((rootPt r.1 : ℂ) + GW2Rd.schedTr c r l a ω (historyTime c r l + u))) :=
      ((continuous_const.add (hηec.comp (continuous_const.add continuous_id))).tendsto u).mono_left
        nhdsWithin_le_nhds
    have hlim2 : Tendsto (fun v => f (ηr v)) (𝓝[<] u) (𝓝 (f (ηr u))) := by
      have h1 : Tendsto ηr (𝓝[<] u) (𝓝[Hbar] (ηr u)) :=
        tendsto_nhdsWithin_iff.2 ⟨(hηrc.tendsto u).mono_left nhdsWithin_le_nhds, Eventually.of_forall hηrH⟩
      exact (hfc (ηr u) (hηrH u)).tendsto.comp h1
    exact tendsto_nhds_unique hlim1 (hlim2.congr' (eventually_nhdsWithin_of_forall fun v hv => (htr_lt v hv).symm))
  have hphys : ∀ u ≤ ℓ₀, ∀ v ≤ c.s, 0 < v →
      (rootPt r.1 : ℂ) + GW2Rd.schedTr c r l a ω (historyTime c r l + u) ≠ -(c.α ω v)⁻¹ := by
    intro u hu v hv hv0 heq
    apply hnc v ⟨zero_le, hv⟩ (historyTime c r l + u) (add_le_add le_rfl hu)
    rw [heq]
    field_simp [hcα0 v hv0]
    ring
  have hcontℓ := GW2Psm.lt_firstContactTime_launch (ηe := fun q => (rootPt r.1 : ℂ) + GW2Rd.schedTr c r l a ω q) hf
    hWk hWk0 hγk hγk0 hW' hW'0 hcα hcα0 hℓm hℓ0 hiff ht₀
    (t := ℓ₀) (t' := ℓ₀ + 1) (lt_add_one ℓ₀) hηrc.continuousOn htr hphys
  have hTc : (ℓ₀ : ℝ≥0∞) < firstContactTime (fun v => sphereInv (ηr v : OnePoint ℂ))
      ((fun v => (γk v : OnePoint ℂ)) '' Icc 0 t₀) := by
    rw [← GW2Kb.firstContactTime_swap]
    exact hcontℓ
  have hcontα : ∀ t : ℝ≥0, t < ℓ₀ → (t : ℝ≥0∞) < firstContactTime (fun u => (α u : OnePoint ℂ))
      ((fun u => sphereInv (γk u : OnePoint ℂ)) '' Icc 0 t₀) := by
    intro t ht
    refine GW2Fb.lt_firstContactTime_of_prefix ht (fun u hu => ?_) ((ENNReal.coe_lt_coe.2 ht).trans hcontℓ)
    show (α u : OnePoint ℂ) = (ηr u : OnePoint ℂ)
    rw [hηrα u (by rw [← hℓ₀]; exact_mod_cast hu)]
  -- GB6's relative chain of `wr` up to the death
  have ht₀pos : 0 < t₀ := by
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t₀) with h | h
    · rw [← h, hℓ0] at ht₀
      exact absurd ht₀.symm hs0.ne'
    · exact h
  have hαr := isLoewnerTrace_of_isGeneratingTrace hγk
  have hNR : ∀ v ∈ Ioc (0 : ℝ) t₀, (fun s : ℝ => γk s.toNNReal) v ≠ 0 :=
    fun v hv => hγk0 _ (Real.toNNReal_pos.2 hv.1)
  have hΨ := Supp8.Q3Rel.isRetainedChartOff_relMap hUkc hUk0 hαr (by exact_mod_cast ht₀pos) hNR
  obtain ⟨t₁, h1t, h2t⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hTc
  obtain ⟨Wr, -, hWr, hWr0, -, -, -, hKall, -, -⟩ := exists_relChain_tip_hull (wα := Wk) (Tα := ⊤) hγk
    hWk.continuousOn hWk0 (s := t₀) ENNReal.coe_lt_top hγkH hUkc hUk0 (t₂ := (t₀ : ℝ) + 1) (by linarith)
    (fun _ _ => rfl) hΨ hηr hwr hwr0 hℓ₀pos (by exact_mod_cast h1t) h2t
  -- the chain and the piece's driver agree before the death
  have hfeq : ∀ t' : ℝ≥0, t' < ℓ₀ → ∀ v : ℝ≥0, v ≤ t' → fwdHull wr' v = fwdHull Wc v := by
    intro t' ht' v hv
    obtain ⟨t₂, h2a, h2b⟩ := exists_between ht'
    refine LocalExt.fwdHull_congr_of_eqOn_of_lt v.coe_nonneg (t' := (t₂ : ℝ)) ?_ fun x hx => ?_
    · exact_mod_cast hv.trans_lt h2a
    · have hxle : x.toNNReal ≤ t₂ := by
        rw [Real.toNNReal_le_iff_le_coe]
        exact hx.2
      exact hwrW _ (hlt_ζ _ (hxle.trans_lt h2b))
  have hclk : ∀ t' : ℝ≥0, t' < ℓ₀ → relClock Uk t₀ wr' t' = relClock Uk t₀ Wc t' := by
    intro t' ht'
    unfold relClock
    rw [hfeq t' ht' t' le_rfl]
  -- each version is the Brownian rescaling of the chain below its cap
  have hcs : ∀ n, (S : ℝ≥0∞) < Vf n → GW2Rd.stgChart (GW2Rz.relChartX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω)) (Rf n) S =
      GW2Rd.stgChart (GW2Rz.relChartX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω)) (Rf j) S := fun n hSn =>
    GW2Psm.stgChart_congr _ (hRc n) (hRc j) fun u hu =>
      hagree n j u (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hu) hSn) (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hu) hSj)
  have hcsD := GW2Kx.isDomainChart_stgChart_relChartX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω) (hRc j) (hR0 j) S
  have hIH : Complex.I ∈ H := by show (0 : ℝ) < Complex.I.im; simp
  have hgeom : ∀ (n : ℕ) (t' : ℝ≥0), 0 < t' → (S : ℝ≥0∞) < Vf n → (An n t' : ℝ≥0∞) < Vf n →
      EqOn (Ito.rpath (GW2Rd.stgDrv (Rf n) S)) (fun s => Wr (lam ^ 2 * s) / lam) (Icc 0 ((An n t' : ℝ) - S)) ∧
        relClock Uk t₀ Wc t' = lam ^ 2 * ((An n t' : ℝ) - S) := by
    intro n t' ht'pos hSn ht'V
    have ht'ℓ : t' < ℓ₀ := lt_of_not_ge fun h =>
      absurd (lt_of_lt_of_le ht'V ((hreach n).trans (ENNReal.coe_le_coe.2 (hAm n h)))) (lt_irrefl _)
    have hhull : HullsUpTo Uk t₀ Wc Wr t' := by
      intro v hv
      have hvt : v < ℓ₀ := hv.trans_lt ht'ℓ
      rw [← hfeq t' ht'ℓ v hv, ← hclk v hvt]
      exact hKall v hvt.le
    have hdisj : ∀ v : ℝ≥0, v ≤ t' → fwdHull Wc v ⊆ H \ invHull Uk t₀ := by
      intro v hv x hx
      have hv' : (v : ℝ≥0∞) < ζ := hlt_ζ v (hv.trans_lt ht'ℓ)
      have hD := Supp8.GB6.disjoint_closure_fwdHull_inv_image hα hreg.1 hreg.2.1 hγk hWk.continuousOn hWk0 hv'
        (show ((t₀ : ℝ≥0) : ℝ≥0∞) < ⊤ from ENNReal.coe_lt_top) (fun w hw hw0 hmem => by
          obtain ⟨u', hu'm, hu'e⟩ := hmem
          have hlt := hcontα u' (lt_of_le_of_lt (hu'm.2.trans hv) ht'ℓ)
          refine Supp8.GB6.notMem_of_lt_firstContactTime hlt ⟨w, hw, ?_⟩
          show sphereInv (γk w : OnePoint ℂ) = (α u' : OnePoint ℂ)
          rw [Supp8.GB6.sphereInv_coe_of_ne hw0, hu'e])
      refine ⟨hx.1, fun hxI => ?_⟩
      exact Set.disjoint_left.1 hD (subset_closure hx) (subset_closure hxI)
    have hAa : ∀ v, S ≤ An n v := fun v => hAn0 n hSn ▸ hAm n (zero_le (a := v))
    obtain ⟨lam', hlam', hdil', -, -, -, hS, hq⟩ := GW2Kx.sample_stage_geomX c r l a hx0 hord t' ht'pos ω hold
      hgood hl hc hconf hext (ht'ℓ.trans_le hℓ₀cap) (hlt_ζ t' ht'ℓ) hWk hWk0 hγk hW' hW'0 hcα hsζ hηe hce h0e hℓc
      hℓm hℓr hvis hiff ht₀ (hRc n) (hR0 n) (hAn0 n hSn) hAa (hAc n)
      (fun v hv => hshape n v (lt_of_le_of_lt (ENNReal.coe_le_coe.2 (hAm n hv)) ht'V)) hWr hWr0 hhull hdisj
    rw [hcs n hSn] at hdil'
    have hy := hcsD.inv_mem hIH
    have hyz := hcsD.fwd_inv hIH
    have hll : lam' = lam := by
      have e := (hdil' _ hy).symm.trans (hdil _ hy)
      rw [hyz] at e
      exact_mod_cast mul_right_cancel₀ Complex.I_ne_zero e
    rw [hll] at hS hq
    exact ⟨hS, hq⟩
  -- (b) the clock identity at the death, by continuity
  obtain ⟨-, -, hcontc⟩ := Supp8.GB6.RelDrv.relClock_props_of_traces (wα := Wk) (Tα := ⊤) hγk hWk.continuousOn hWk0
    (s := t₀) ENNReal.coe_lt_top hγkH hηr hwr hwr0
  have hopen : IsOpen {t : ℝ≥0 | (t : ℝ≥0∞) < firstContactTime (fun v => sphereInv (ηr v : OnePoint ℂ))
      ((fun v => (γk v : OnePoint ℂ)) '' Icc 0 t₀)} := isOpen_lt ENNReal.continuous_coe continuous_const
  have : (𝓝[<] ℓ₀).NeBot := mem_closure_iff_nhdsWithin_neBot.1
    (by rw [closure_Iio' (show (Iio ℓ₀).Nonempty from ⟨0, hℓ₀pos⟩)]; exact Set.self_mem_Iic)
  have hlim1 : Tendsto (fun t : ℝ≥0 => relClock Uk t₀ wr' t) (𝓝[<] ℓ₀) (𝓝 (relClock Uk t₀ wr' ℓ₀)) :=
    ((hcontc ℓ₀ hTc).continuousAt (hopen.mem_nhds hTc)).tendsto.mono_left nhdsWithin_le_nhds
  have hCt : Tendsto C (𝓝[<] ℓ₀) (𝓝 (C ℓ₀)) :=
    ((hCc ℓ₀ ⟨zero_le, le_rfl⟩).mono fun x hx => ⟨zero_le, (le_of_lt hx)⟩).tendsto
  have hlim2 : Tendsto (fun t : ℝ≥0 => lam ^ 2 * (C t - S)) (𝓝[<] ℓ₀) (𝓝 (lam ^ 2 * (C ℓ₀ - S))) :=
    (hCt.sub_const _).const_mul _
  have hev : ∀ᶠ t : ℝ≥0 in 𝓝[<] ℓ₀, relClock Uk t₀ wr' t = lam ^ 2 * (C t - S) := by
    filter_upwards [Ioo_mem_nhdsLT hℓ₀pos] with t ht
    obtain ⟨n, hSn, htV⟩ := hexh t ht.1 ht.2
    obtain ⟨-, hq⟩ := hgeom n t ht.1 hSn htV
    rw [hclk t ht.2, hq, hAC n t htV]
  have hb : lam ^ 2 * (C ℓ₀ - S) = relClock Uk t₀ wr' ℓ₀ :=
    tendsto_nhds_unique (hlim2.congr' (hev.mono fun _ h => h.symm)) hlim1
  refine ⟨hTc, hb, ?_⟩
  -- (c) the driver through the death
  set Wd : ℝ≥0 → ℝ := fun q => Rf j (min q S) + Wr (lam ^ 2 * max ((q : ℝ) - S) 0) / lam with hWddef
  have hWdc : Continuous Wd :=
    ((hRc j).comp (continuous_id.min continuous_const)).add
      ((hWr.comp (continuous_const.mul ((NNReal.continuous_coe.sub continuous_const).max continuous_const))).div_const
        lam)
  have hWd0 : Wd 0 = 0 := by
    simp only [hWddef, zero_le, min_eq_left, hR0, NNReal.coe_zero, zero_sub]
    rw [max_eq_right (by simp), mul_zero, hWr0, zero_div, add_zero]
  have hWdS : ∀ q : ℝ≥0, Wd (S + q) = Rf j S + Wr (lam ^ 2 * q) / lam := by
    intro q
    simp only [hWddef, le_add_iff_nonneg_right, zero_le, min_eq_right, NNReal.coe_add, add_sub_cancel_left]
    rw [max_eq_left q.coe_nonneg]
  have hstg : ∀ q : ℝ≥0, GW2Rd.stgDrv Wd S q = Wr (lam ^ 2 * q) / lam := by
    intro q
    unfold GW2Rd.stgDrv
    rw [hWdS q]
    have h0 := hWdS 0
    rw [add_zero, NNReal.coe_zero, mul_zero, hWr0, zero_div, add_zero] at h0
    rw [h0]
    ring
  refine ⟨Wd, hWdc, hWd0, fun n q hq => ?_, fun t ht => ?_⟩
  · by_cases hqS : q ≤ S
    · have e : Wd q = Rf j q := by
        simp only [hWddef, min_eq_left hqS]
        have : ((q : ℝ) - S) ≤ 0 := sub_nonpos.2 (by exact_mod_cast hqS)
        rw [max_eq_right this, mul_zero, hWr0, zero_div, add_zero]
      rw [e]
      exact hagree n j q hq (lt_of_le_of_lt (ENNReal.coe_le_coe.2 hqS) hSj)
    · push Not at hqS
      have hSn : (S : ℝ≥0∞) < Vf n := lt_trans (ENNReal.coe_lt_coe.2 hqS) hq
      have hVtop : Vf n ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top (hreach n)
      set Vr : ℝ≥0 := (Vf n).toNNReal with hVrdef
      have hVr : (Vr : ℝ≥0∞) = Vf n := ENNReal.coe_toNNReal hVtop
      have hqV : q < Vr := by rw [← ENNReal.coe_lt_coe, hVr]; exact hq
      set m : ℝ≥0 := (q + Vr) / 2 with hm
      have hqm : q < m := by
        rw [hm, lt_div_iff₀ (by norm_num : (0 : ℝ≥0) < 2)]
        calc q * 2 = q + q := by ring
          _ < q + Vr := by gcongr
      have hmV : m < Vr := by
        rw [hm, div_lt_iff₀ (by norm_num : (0 : ℝ≥0) < 2)]
        calc q + Vr < Vr + Vr := by gcongr
          _ = Vr * 2 := by ring
      have hVrℓ : Vr ≤ An n ℓ₀ := by rw [← ENNReal.coe_le_coe, hVr]; exact hreach n
      obtain ⟨t', -, ht'⟩ := intermediate_value_Icc (zero_le (a := ℓ₀)) (hAc n).continuousOn
        ⟨by rw [hAn0 n hSn]; exact (hqS.trans hqm).le, hmV.le.trans hVrℓ⟩
      have ht'V : (An n t' : ℝ≥0∞) < Vf n := by rw [← hVr, ht']; exact ENNReal.coe_lt_coe.2 hmV
      have ht'pos : 0 < t' := by
        rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t') with h | h
        · rw [← h, hAn0 n hSn] at ht'
          exact absurd (hqS.trans hqm) (by rw [← ht']; exact lt_irrefl _)
        · exact h
      obtain ⟨hS', -⟩ := hgeom n t' ht'pos hSn ht'V
      have hmem : ((q : ℝ) - S) ∈ Icc (0 : ℝ) ((An n t' : ℝ) - S) := by
        refine ⟨sub_nonneg.2 (by exact_mod_cast hqS.le), ?_⟩
        rw [ht']
        have : (q : ℝ) ≤ m := by exact_mod_cast hqm.le
        linarith
      have e1 := hS' hmem
      simp only [Ito.rpath, GW2Rd.stgDrv] at e1
      have hqS' : ((q : ℝ) - S).toNNReal = q - S := by
        rw [← NNReal.coe_sub hqS.le, Real.toNNReal_coe]
      rw [hqS', add_tsub_cancel_of_le hqS.le] at e1
      have hRS : Rf n S = Rf j S := hagree n j S hSn hSj
      have e2 : Wd q = Rf j S + Wr (lam ^ 2 * ((q : ℝ) - S)) / lam := by
        simp only [hWddef, min_eq_right hqS.le]
        rw [max_eq_left (sub_nonneg.2 (by exact_mod_cast hqS.le))]
      rw [e2, ← hRS, ← e1]
      ring
  · rw [hKall t ht]
    have hT0 : 0 ≤ relClock Uk t₀ wr' t := GW2Pw.relClock_nonneg' _ _ _ _
    have hDc : Continuous (scD lam (fun q : ℝ => GW2Rd.stgDrv Wd S q.toNNReal)) :=
      GW2Nu.continuous_scD ((GW2Rd.continuous_stgDrv hWdc S).comp continuous_real_toNNReal)
    refine YuanCorollary13.fwdHull_eq_of_eqOn_Icc hDc hWr hT0 fun s hs => ?_
    have hl2 : 0 < lam ^ 2 := by positivity
    show lam * GW2Rd.stgDrv Wd S (s / lam ^ 2).toNNReal = Wr s
    rw [hstg, Real.coe_toNNReal _ (div_nonneg hs.1 hl2.le), mul_div_cancel₀ s hl2.ne']
    field_simp

end InteractingSLE.Theorem14.GW2Pu
