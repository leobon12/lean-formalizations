/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2PwWinS
import InteractingSLE.Spec.Supplement.GW2KxGeom
import InteractingSLE.Spec.Supplement.GW2KxTrace
import InteractingSLE.Spec.Supplement.GW2KxRead

/-!
# The window clause of D46's export at one sample at a root `x` (D65)

PROVE-GW2-ROOTX round 13. STAGEMEAN's `GW2Pw.sample_window_root0` at a root `x ≥ 0`, in the root-`x` stage chart
`stgChart (relChartX x s rec) R a₀`: GEOM2's `sample_trace_corrX`, `sample_stage_geomX` and
`isDomainChart_stgChart_relChartX` replace their root-`0` versions; the launch-frame contact reads the shifted trace
`x + η` (the product-form no-contact `α (x + η) + 1 ≠ 0`); the counterflow's visit to `x` enters as `hvis`.

* **`sample_window_rootX`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdMap fwdMapInv fwdHull chiC)

namespace InteractingSLE.Theorem14.GW2Rn

open GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2TipSystem.Swc GW2Schedule GW2Tip Exist Exist.Staged
  Exist.StagedLaw Sec5.Prop513Schedule GW2Omx Supp8.GB6LMean MartChar.RealFlow Restart Supp8.Q3Chain GW2Fb
  GW2JointKernel Sec5.CrossCond.StagedRepLater
open Supp8.GB6 (relMap gb6Rec relClock sphereInv firstContactTime)
open Supp8.Q3Rel (invHull relLog)

/-- **The window clause of D46's export at one sample** (root `x`). -/
theorem sample_window_rootX {Ω : Type*} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
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
    {R : ℝ≥0 → ℝ} (hR : Continuous R) (hR0 : R 0 = 0) {A : ℝ≥0 → ℝ≥0} {a₀ : ℝ≥0} (hA0 : A 0 = a₀)
    (hAm : Monotone A) (hAc : Continuous A) {V : ℝ≥0∞} {τ : ℝ≥0} (hτ : V ≤ (A τ : ℝ≥0∞))
    (hstop : ∀ u : ℝ≥0, (A u : ℝ≥0∞) < V →
      u < candidateCap c r a ∧ (u : ℝ≥0∞) < (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).2)
    (hshape : ∀ u : ℝ≥0, (A u : ℝ≥0∞) < V → H \ GW2Rd.schedUnionX c r l a (historyTime c r l) u ω =
      (GW2Rz.relChartX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω)).2.1 '' (H \ fwdHull (Ito.rpath R) (A u)))
    (hnc : ∀ u : ℝ≥0, (A u : ℝ≥0∞) < V →
      ∀ v ∈ Icc 0 c.s, ∀ u' ≤ historyTime c r l + u,
        c.α ω v * ((rootPt r.1 : ℂ) + GW2Rd.schedTr c r l a ω u') + 1 ≠ 0)
    {lam : ℝ} (hlam : 0 < lam)
    (hdil : ∀ x ∈ ((GW2Rd.stgChart (GW2Rz.relChartX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω)) R a₀).dom : Set ℂ),
      relMap (fun q : ℝ => Wk q.toNNReal) (t₀ : ℝ) (cL.1 x) =
        (lam : ℂ) * (GW2Rd.stgChart (GW2Rz.relChartX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω)) R a₀).1 x)
    (u : ℝ≥0) (hu : ((a₀ + u : ℝ≥0) : ℝ≥0∞) < V) :
    (∃ t : ℝ≥0, (t : ℝ≥0∞) < min (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).2
        (firstContactTime (fun v => (α v : OnePoint ℂ)) ((fun v => sphereInv (γk v : OnePoint ℂ)) '' Icc 0 t₀)) ∧
      lam ^ 2 * u < relClock (fun q : ℝ => Wk q.toNNReal) t₀
        (fun q : ℝ => (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).1 q.toNNReal) t) ∧
    ∀ t : ℝ≥0, (t : ℝ≥0∞) < firstContactTime (fun v => sphereInv (ηr v : OnePoint ℂ))
        ((fun v => (γk v : OnePoint ℂ)) '' Icc 0 t₀) →
      relClock (fun q : ℝ => Wk q.toNNReal) t₀ (fun q : ℝ => wr q.toNNReal) t ≤ lam ^ 2 * u →
      fwdHull (scD lam (Ito.rpath (GW2Rd.stgDrv R a₀)))
          (relClock (fun q : ℝ => Wk q.toNNReal) t₀ (fun q : ℝ => wr q.toNNReal) t) =
        relMap (fun q : ℝ => Wk q.toNNReal) t₀ '' fwdHull (fun q : ℝ => wr q.toNNReal) t := by
  classical
  set ζ := (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).2 with hζdef
  set Uk : ℝ → ℝ := fun q : ℝ => Wk q.toNNReal with hUk
  set Wc : ℝ → ℝ := fun q : ℝ => (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).1 q.toNNReal with hWc
  set wr' : ℝ → ℝ := fun q : ℝ => wr q.toNNReal with hwr'
  set S : ℝ → ℝ := Ito.rpath (GW2Rd.stgDrv R a₀) with hSdef
  have hUkc : Continuous Uk := hWk.comp continuous_real_toNNReal
  have hUk0 : Uk 0 = 0 := by simp [hUk, hWk0]
  have hSc : Continuous S := (GW2Rd.continuous_stgDrv hR a₀).comp continuous_real_toNNReal
  -- the cap is finite; two stage times below it
  have hVtop : V ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top hτ
  set Vr : ℝ≥0 := V.toNNReal with hVrdef
  have hVr : (Vr : ℝ≥0∞) = V := ENNReal.coe_toNNReal hVtop
  have hu' : a₀ + u < Vr := by rw [← ENNReal.coe_lt_coe, hVr]; exact hu
  have hVrτ : Vr ≤ A τ := by rw [← ENNReal.coe_le_coe, hVr]; exact hτ
  have hIVT : ∀ m : ℝ≥0, a₀ ≤ m → m ≤ Vr → ∃ t' : ℝ≥0, A t' = m := by
    intro m h1 h2
    obtain ⟨t', -, ht'⟩ := intermediate_value_Icc (zero_le (a := τ)) hAc.continuousOn
      ⟨by rw [hA0]; exact h1, h2.trans hVrτ⟩
    exact ⟨t', ht'⟩
  set m₁ : ℝ≥0 := (a₀ + u + Vr) / 2 with hm₁
  set m₂ : ℝ≥0 := (m₁ + Vr) / 2 with hm₂
  have hm₁a : a₀ + u < m₁ := by
    rw [hm₁, lt_div_iff₀ (by norm_num : (0 : ℝ≥0) < 2)]
    have := hu'
    calc (a₀ + u) * 2 = (a₀ + u) + (a₀ + u) := by ring
      _ < (a₀ + u) + Vr := by gcongr
  have hm₁V : m₁ < Vr := by
    rw [hm₁, div_lt_iff₀ (by norm_num : (0 : ℝ≥0) < 2)]
    calc a₀ + u + Vr < Vr + Vr := by gcongr
      _ = Vr * 2 := by ring
  have hm₂a : m₁ < m₂ := by
    rw [hm₂, lt_div_iff₀ (by norm_num : (0 : ℝ≥0) < 2)]
    calc m₁ * 2 = m₁ + m₁ := by ring
      _ < m₁ + Vr := by gcongr
  have hm₂V : m₂ < Vr := by
    rw [hm₂, div_lt_iff₀ (by norm_num : (0 : ℝ≥0) < 2)]
    calc m₁ + Vr < Vr + Vr := by gcongr
      _ = Vr * 2 := by ring
  have ha₀m₁ : a₀ ≤ m₁ := le_trans le_self_add hm₁a.le
  obtain ⟨t', ht'⟩ := hIVT m₁ ha₀m₁ hm₁V.le
  obtain ⟨t₂, ht₂⟩ := hIVT m₂ (ha₀m₁.trans hm₂a.le) hm₂V.le
  have hltV : ∀ v : ℝ≥0, A v < Vr → (A v : ℝ≥0∞) < V := fun v h => by rw [← hVr]; exact ENNReal.coe_lt_coe.2 h
  have ht'V : (A t' : ℝ≥0∞) < V := hltV t' (by rw [ht']; exact hm₁V)
  have ht₂V : (A t₂ : ℝ≥0∞) < V := hltV t₂ (by rw [ht₂]; exact hm₂V)
  have ht'2 : t' < t₂ := lt_of_not_ge fun h => by
    have := hAm h
    rw [ht', ht₂] at this
    exact absurd hm₂a (not_lt.2 this)
  have ht'pos : 0 < t' := by
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t') with h | h
    · rw [← h, hA0] at ht'
      exact absurd hm₁a (by rw [← ht']; exact not_lt.2 le_self_add)
    · exact h
  obtain ⟨htcap₂, htζ₂⟩ := hstop t₂ ht₂V
  have htcap' : t' < candidateCap c r a := ht'2.trans htcap₂
  have htζ' : (t' : ℝ≥0∞) < ζ := (ENNReal.coe_lt_coe.2 ht'2).trans htζ₂
  -- the launch-frame contact is after `t₂`
  obtain ⟨t'', h2'', h''ζ⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 htζ₂
  have h2''' : t₂ < t'' := by exact_mod_cast h2''
  obtain ⟨f, hf, htr⟩ := GW2Kx.sample_trace_corrX c r l a hord t₂ ω hold hgood hl hc hext htcap₂ htζ₂ hreg hα hηe
  have hαc : ContinuousOn α (Icc 0 t'') := hα.2.1.mono fun v hv => (ENNReal.coe_le_coe.2 hv.2).trans h''ζ.le
  have hphys : ∀ v ≤ t₂, ∀ w ≤ c.s, 0 < w →
      (rootPt r.1 : ℂ) + GW2Rd.schedTr c r l a ω (historyTime c r l + v) ≠ -(c.α ω w)⁻¹ := by
    intro v hv w hw hw0 heq
    apply hnc t₂ ht₂V w ⟨zero_le, hw⟩ (historyTime c r l + v) (add_le_add le_rfl hv)
    rw [heq]
    field_simp [hcα0 w hw0]
    ring
  have hℓ0 : ℓ 0 = 0 := GW2Sgk.clock_zero_of_range hℓm hℓr
  have hcont₂ := GW2Psm.lt_firstContactTime_launch (ηe := fun q => (rootPt r.1 : ℂ) + GW2Rd.schedTr c r l a ω q) hf
    hWk hWk0 hγk hγk0 hW' hW'0 hcα hcα0 hℓm hℓ0 hiff ht₀ h2''' hαc htr hphys
  -- GB6's contact of the extended trace is after `t₂`
  have hTc₂ : (t₂ : ℝ≥0∞) < firstContactTime (fun v => sphereInv (ηr v : OnePoint ℂ))
      ((fun v => (γk v : OnePoint ℂ)) '' Icc 0 t₀) := by
    have h1 : (t₂ : ℝ≥0∞) < firstContactTime (fun v => sphereInv (α v : OnePoint ℂ))
        ((fun v => (γk v : OnePoint ℂ)) '' Icc 0 t₀) := by
      rw [← GW2Kb.firstContactTime_swap]
      exact hcont₂
    refine GW2Fb.lt_firstContactTime_of_prefix h2''' (fun v hv => ?_) h1
    show sphereInv (ηr v : OnePoint ℂ) = sphereInv (α v : OnePoint ℂ)
    rw [hηrα v ((ENNReal.coe_le_coe.2 hv).trans h''ζ.le)]
  -- GB6's relative chain of `wr` up to `t'`
  have ht₀pos : 0 < t₀ := by
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t₀) with h | h
    · rw [← h, hℓ0] at ht₀
      exact absurd ht₀.symm hs0.ne'
    · exact h
  have hαr := isLoewnerTrace_of_isGeneratingTrace hγk
  have hNR : ∀ v ∈ Ioc (0 : ℝ) t₀, (fun s : ℝ => γk s.toNNReal) v ≠ 0 :=
    fun v hv => hγk0 _ (Real.toNNReal_pos.2 hv.1)
  have hΨ := Supp8.Q3Rel.isRetainedChartOff_relMap hUkc hUk0 hαr (by exact_mod_cast ht₀pos) hNR
  obtain ⟨Wr, -, hWr, hWr0, -, -, -, hKall, -, -⟩ := exists_relChain_tip_hull (wα := Wk) (Tα := ⊤) hγk
    hWk.continuousOn hWk0 (s := t₀) ENNReal.coe_lt_top hγkH hUkc hUk0 (t₂ := (t₀ : ℝ) + 1) (by linarith)
    (fun _ _ => rfl) hΨ hηr hwr hwr0 ht'pos ht'2 hTc₂
  -- the same chain for the piece's driver up to `t'`
  have hfeq : ∀ v : ℝ≥0, v ≤ t' → fwdHull wr' v = fwdHull Wc v := by
    intro v hv
    refine LocalExt.fwdHull_congr_of_eqOn_of_lt v.coe_nonneg (t' := (t₂ : ℝ)) ?_ fun x hx => ?_
    · exact_mod_cast hv.trans_lt ht'2
    · have hxle : x.toNNReal ≤ t₂ := by
        rw [Real.toNNReal_le_iff_le_coe]
        exact hx.2
      exact hwrW _ ((ENNReal.coe_le_coe.2 hxle).trans_lt htζ₂)
  have hclk : ∀ v : ℝ≥0, v ≤ t' → relClock Uk t₀ wr' v = relClock Uk t₀ Wc v := by
    intro v hv
    unfold relClock
    rw [hfeq v hv]
  have hhull : HullsUpTo Uk t₀ Wc Wr t' := by
    intro v hv
    rw [← hfeq v hv, ← hclk v hv]
    exact hKall v hv
  have hdisj : ∀ v : ℝ≥0, v ≤ t' → fwdHull Wc v ⊆ H \ invHull Uk t₀ := by
    intro v hv x hx
    have hv' : (v : ℝ≥0∞) < ζ := (ENNReal.coe_le_coe.2 hv).trans_lt htζ'
    have hD := Supp8.GB6.disjoint_closure_fwdHull_inv_image hα hreg.1 hreg.2.1 hγk hWk.continuousOn hWk0 hv'
      (show ((t₀ : ℝ≥0) : ℝ≥0∞) < ⊤ from ENNReal.coe_lt_top) (fun w hw hw0 hmem => by
        obtain ⟨u', hu'm, hu'e⟩ := hmem
        have hlt : ((u' : ℝ≥0) : ℝ≥0∞) < firstContactTime (fun u => (α u : OnePoint ℂ))
            ((fun u => sphereInv (γk u : OnePoint ℂ)) '' Icc 0 t₀) :=
          lt_of_le_of_lt (ENNReal.coe_le_coe.2 (hu'm.2.trans (hv.trans ht'2.le))) hcont₂
        refine Supp8.GB6.notMem_of_lt_firstContactTime hlt ⟨w, hw, ?_⟩
        show sphereInv (γk w : OnePoint ℂ) = (α u' : OnePoint ℂ)
        rw [Supp8.GB6.sphereInv_coe_of_ne hw0, hu'e])
    refine ⟨hx.1, fun hxI => ?_⟩
    exact Set.disjoint_left.1 hD (subset_closure hx) (subset_closure hxI)
  -- the stage geometry at `t'`
  have hAa : ∀ v, a₀ ≤ A v := fun v => hA0 ▸ hAm (zero_le (a := v))
  obtain ⟨lam', hlam', hdil', -, -, -, hS, hq⟩ := GW2Kx.sample_stage_geomX c r l a hx0 hord t' ht'pos ω hold hgood
    hl hc hconf hext htcap' htζ' hWk hWk0 hγk hW' hW'0 hcα hsζ hηe hce h0e hℓc hℓm hℓr hvis hiff ht₀ hR hR0 hA0 hAa
    hAc (fun v hv => hshape v (lt_of_le_of_lt (ENNReal.coe_le_coe.2 (hAm hv)) ht'V)) hWr hWr0 hhull hdisj
  -- the dilation is unique
  have hcsD := GW2Kx.isDomainChart_stgChart_relChartX (rootPt r.1) c.s (cfRec c.s c.W c.ζ ω) hR hR0 a₀
  have hIH : Complex.I ∈ H := by show (0 : ℝ) < Complex.I.im; simp
  have hy := hcsD.inv_mem hIH
  have hyz := hcsD.fwd_inv hIH
  have hll : lam' = lam := by
    have e := (hdil' _ hy).symm.trans (hdil _ hy)
    rw [hyz] at e
    exact_mod_cast mul_right_cancel₀ Complex.I_ne_zero e
  rw [hll] at hS hq
  set Q : ℝ := (A t' : ℝ) - a₀ with hQ
  have hQu : (u : ℝ) < Q := by
    rw [hQ, ht']
    have : ((a₀ + u : ℝ≥0) : ℝ) < (m₁ : ℝ) := by exact_mod_cast hm₁a
    push_cast at this
    linarith
  have hl2 : 0 < lam ^ 2 := by positivity
  have hlu : lam ^ 2 * u < lam ^ 2 * Q := mul_lt_mul_of_pos_left hQu hl2
  refine ⟨⟨t', lt_min htζ' ((ENNReal.coe_lt_coe.2 ht'2).trans hcont₂), by rw [hq]; exact hlu⟩, ?_⟩
  intro t ht hle
  -- the time is before `t'`
  obtain ⟨-, hsm, -⟩ := Supp8.GB6.RelDrv.relClock_props_of_traces (wα := Wk) (Tα := ⊤) hγk hWk.continuousOn hWk0
    (s := t₀) ENNReal.coe_lt_top hγkH hηr hwr hwr0
  have htt' : t ≤ t' := by
    by_contra hcon
    push Not at hcon
    have h1 : relClock Uk t₀ wr' t' < relClock Uk t₀ wr' t :=
      hsm ((ENNReal.coe_lt_coe.2 ht'2).trans hTc₂) ht hcon
    rw [hclk t' le_rfl, hq] at h1
    linarith
  rw [hKall t htt']
  exact GW2Pw.fwdHull_scD_eq_of_scale hlam hSc hWr hS (GW2Pw.relClock_nonneg' _ _ _ _) (hle.trans hlu.le)

end InteractingSLE.Theorem14.GW2Rn
