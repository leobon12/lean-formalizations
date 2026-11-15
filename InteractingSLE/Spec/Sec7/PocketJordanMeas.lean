/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketJordanInf

/-!
# The random change pocket's measurable Jordan coordinate in the counterflow chart

Packet PROVE-STRIPSYS17 (specification §7.4.1, Aux. lemma 125, p. 395: "The chart, including its positive scale and
analytic logarithm lift, is selected measurably from the initial marked `A` alone"; Aux. lemma 130, p. 409: "The event
and the selected component are measurable from their complete labeled incoming paths alone").

For random walls `R ω`, `L ω` with measurable coordinates and a measurable event `G` on which they satisfy Aux. lemma
130's configuration `IsChangeConfigInc` with the opening contact away from the flow seed, this file selects a Jordan
coordinate `ψ ω` of the change pocket in the counterflow chart (`m(x₀) ↦ ∞`, `m(y₀) ↦ 0`) **measurably**: its value at
any measurable random point of the closed pocket (other than `m(x₀)`) is a measurable function of `ω`.

Construction: the measurable marked-pocket chart `c ω` of PROVE-LEMMA71K (`Lemma71K.exists_markedPocketChart`, applied
to `PocketCoord.exists_measurable_changePocketInc`) is a positive multiple of `Ψ_ω ∘ cayley` for the two-point
uniformizer `Ψ_ω` of the Cayley image (`x₀ ↦ 0`, `y₀ ↦ ∞`; uniqueness clause of the chart, with the approach
sequences of the marked pocket, `IsChangeConfigInc.isMarkedPocket`). Hence on the inverted pocket the Jordan coordinate
`cfCoord a Ψ (cayley y₀)` equals `m ∘ c ∘ m`, measurable at every fixed point; its values on the closed pocket are
limits along measurable approach sequences (`Lemma71E.exists_measurable_approach`).

## Main results

* `measurable_negInv`, `measurableSet_mem_image_negInv`;
* **`exists_measurable_cfCoord`** (core, no boundedness): a measurable choice of the scale and of the two-point
  uniformizer, with measurable values of `cfCoord` at measurable points where it is continuous within the pocket;
* **`exists_measurable_cfJordanCoord`** (bounded case, `Sec6.IsJordanCoord`);
* **`exists_measurable_cfJordanCoordInf`** (the pocket opening at the flow seed, `Sec6.IsJordanCoordInf`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Complex Set Filter Topology Metric Function Bornology
open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley cayleyInv)
open SupercriticalConformalCovariance (IsConformalBijection)
open InteractingSLE.WangWu (negInv)
open scoped NNReal

namespace InteractingSLE.Sec7.PocketJordan

open WangWu PocketCoord Lemma71I

section Random

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {R L : Ω → ℝ≥0 → ℂ} {r : ℝ≥0} {G : Set Ω}

theorem measurable_negInv : Measurable negInv := by
  show Measurable fun z : ℂ => -z⁻¹
  exact measurable_inv.neg

/-- The membership events of the inverted random pocket `m(C ω)`. -/
theorem measurableSet_mem_image_negInv {C : Ω → Set ℂ} (hCo : ∀ ω, IsOpen (C ω)) (hCH : ∀ ω, C ω ⊆ H)
    (hCm : ∀ (c : ℂ) (ρ : ℝ), MeasurableSet {ω | closedBall c ρ ⊆ C ω}) (z : ℂ) :
    MeasurableSet {ω | z ∈ negInv '' C ω} := by
  have heq : {ω | z ∈ negInv '' C ω} = {_ω | z ∈ H} ∩ {ω | negInv z ∈ C ω} := by
    ext ω
    simp only [mem_ofPred_eq, mem_inter_iff]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨WangWu.negInv_mem_H (hCH ω hw), by rw [WangWu.negInv_negInv]; exact hw⟩
    · rintro ⟨-, hz⟩
      exact ⟨negInv z, hz, WangWu.negInv_negInv z⟩
  rw [heq]
  exact (MeasurableSet.const _).inter (Lemma71E.measurableSet_mem_of_closedBall hCo hCm (negInv z))

/-- **The measurable counterflow coordinate of the random change pocket (core).** For random walls with measurable
coordinates and a measurable event `G` on which they satisfy `IsChangeConfigInc`, there are a random scale `a ω > 0`
and a random two-point uniformizer `Ψ ω` of the Cayley image (on `G`) such that the counterflow coordinate
`cfCoord (a ω) (Ψ ω) (closePt …)` has measurable values at every measurable random point `p ω` of the closed inverted
pocket (on a measurable `A ⊆ G`) at which it is continuous within the pocket. No boundedness is assumed. -/
theorem exists_measurable_cfCoord (hRm : ∀ t, Measurable fun ω => R ω t)
    (hLm : ∀ t, Measurable fun ω => L ω t) (hGm : MeasurableSet G) (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r) :
    ∃ (a : Ω → ℝ) (Ψ : Ω → ℂ → ℂ),
      (∀ ω ∈ G, 0 < a ω ∧ IsBdryUniformizer (cayley '' changePocket (R ω) (L ω) r) (openPt (R ω) (L ω) r)
        (closePt (R ω) (L ω) r) (Ψ ω)) ∧
      ∀ A : Set Ω, MeasurableSet A → A ⊆ G → ∀ p : Ω → ℂ, Measurable p →
        (∀ ω ∈ A, p ω ∈ closure (cfPocket (R ω) (L ω) r) ∧
          ContinuousWithinAt (cfCoord (a ω) (Ψ ω) (closePt (R ω) (L ω) r)) (cfPocket (R ω) (L ω) r) (p ω)) →
        Measurable (A.indicator fun ω => cfCoord (a ω) (Ψ ω) (closePt (R ω) (L ω) r) (p ω)) := by
  classical
  obtain ⟨e, he⟩ := TopologicalSpace.exists_dense_seq ℂ
  obtain ⟨C, Np, hNp, hCp, hCm, hNpC, hCG, -⟩ :=
    PocketCoord.exists_measurable_changePocketInc hRm hLm hGm hG he
  -- walls continuous for every `ω`
  set R' : Ω → ℝ≥0 → ℂ := fun ω => if ω ∈ G then R ω else fun _ => 0 with hR'def
  have hR'c : ∀ ω, Continuous (R' ω) := fun ω => by
    by_cases hω : ω ∈ G
    · simp only [hR'def, hω, ↓reduceIte]; exact (hG ω hω).right.1
    · simp only [hR'def, hω, ↓reduceIte]; exact continuous_const
  have hR'm : ∀ t, Measurable fun ω => R' ω t := fun t => by
    have : (fun ω => R' ω t) = fun ω => if ω ∈ G then R ω t else 0 := by
      ext ω; by_cases hω : ω ∈ G <;> simp [hR'def, hω]
    rw [this]; exact Measurable.ite hGm (hRm t) measurable_const
  obtain ⟨Nx, Ny, c, -, -, -, -, -, hdom, -, -, hfm, -, -, -, -, huniq, happ⟩ :=
    Lemma71K.exists_markedPocketChart hCp hCm he hNp hNpC hR'c hR'm
  -- the pathwise uniformizer and the scale
  have hΨex : ∀ ω ∈ G, ∃ Ψ : ℂ → ℂ, IsBdryUniformizer (cayley '' changePocket (R ω) (L ω) r)
      (openPt (R ω) (L ω) r) (closePt (R ω) (L ω) r) Ψ := fun ω hω => (hG ω hω).exists_isBdryUniformizer
  set Ψ : Ω → ℂ → ℂ := fun ω => if hω : ω ∈ G then (hΨex ω hω).choose else 0 with hΨdef
  have hΨ : ∀ ω (hω : ω ∈ G), IsBdryUniformizer (cayley '' changePocket (R ω) (L ω) r)
      (openPt (R ω) (L ω) r) (closePt (R ω) (L ω) r) (Ψ ω) := fun ω hω => by
    simp only [hΨdef, hω, ↓reduceDIte]
    exact (hΨex ω hω).choose_spec
  have haex : ∀ ω ∈ G, ∃ a : ℝ, 0 < a ∧ EqOn (c ω).1 (fun z => (a : ℂ) * Ψ ω (cayley z)) (C ω) := by
    intro ω hω
    have h := hG ω hω
    have hU := hΨ ω hω
    have hCω := hCG ω hω
    have hR' : R' ω = R ω := by simp only [hR'def, hω, ↓reduceIte]
    have hM : Lemma71K.IsMarkedPocket (R' ω) (C ω) (rightLo (R ω) (L ω) r) (rightHi (R ω) (L ω) r) := by
      rw [hR', hCω]; exact h.isMarkedPocket
    obtain ⟨hx, hy⟩ := happ ω _ _ hM
    rw [hR', hCω] at hx hy
    have hDo := Lemma71F.isOpen_cayley_image h.isOpen_changePocket h.changePocket_subset_H
    have hqD : closePt (R ω) (L ω) r ∉ cayley '' changePocket (R ω) (L ω) r := by
      have := h.closePt_mem_frontier
      rw [hDo.frontier_eq] at this
      exact this.2
    have hsub : cayley '' changePocket (R ω) (L ω) r ⊆
        closure (cayley '' changePocket (R ω) (L ω) r) \ {closePt (R ω) (L ω) r} := fun w hw =>
      ⟨subset_closure hw, fun h' => hqD (h' ▸ hw)⟩
    have hp : openPt (R ω) (L ω) r ∈
        closure (cayley '' changePocket (R ω) (L ω) r) \ {closePt (R ω) (L ω) r} :=
      ⟨frontier_subset_closure h.openPt_mem_frontier, h.openPt_ne_closePt⟩
    refine huniq ω (fun z => Ψ ω (cayley z)) ?_ ?_ ?_
    · rw [hCω]
      exact isConformalBijection_comp hU.conf (Lemma71F.isConformalBijection_cayley_image h.changePocket_subset_H)
    · have := (hU.cont _ hp).tendsto.comp (hx.mono_right (nhdsWithin_mono _ hsub))
      rwa [hU.zero] at this
    · exact hU.tendsto.comp (hy.mono_right (nhdsWithin_mono _ hsub))
  set a : Ω → ℝ := fun ω => if hω : ω ∈ G then (haex ω hω).choose else 1 with hadef
  have ha : ∀ ω (hω : ω ∈ G), 0 < a ω ∧ EqOn (c ω).1 (fun z => (a ω : ℂ) * Ψ ω (cayley z)) (C ω) := fun ω hω => by
    simp only [hadef, hω, ↓reduceDIte]
    exact (haex ω hω).choose_spec
  refine ⟨a, Ψ, fun ω hω => ⟨(ha ω hω).1, hΨ ω hω⟩, ?_⟩
  intro A hA hAG p hp hpA
  -- the coordinate inside the inverted pocket is `m ∘ c ∘ m`
  have hin : ∀ ω (hω : ω ∈ G) (z : ℂ), z ∈ cfPocket (R ω) (L ω) r →
      cfCoord (a ω) (Ψ ω) (closePt (R ω) (L ω) r) z = negInv ((c ω).1 (negInv z)) := by
    intro ω hω z hz
    rw [(hG ω hω).cfCoord_of_mem hz]
    obtain ⟨w, hw, rfl⟩ := hz
    rw [WangWu.negInv_negInv, (ha ω hω).2 (by rw [hCG ω hω]; exact hw)]
  -- the inverted random pocket and the approach sequences
  set C' : Ω → Set ℂ := fun ω => negInv '' C ω with hC'def
  have hCH : ∀ ω, C ω ⊆ H := fun ω => (hCp ω).2.2.2
  have hC'o : ∀ ω, IsOpen (C' ω) := fun ω => isOpen_image_negInv' (hCp ω).1 (hCH ω)
  have hC'm : ∀ z, MeasurableSet {ω | z ∈ C' ω} := measurableSet_mem_image_negInv (fun ω => (hCp ω).1) hCH hCm
  have hC'G : ∀ ω ∈ G, C' ω = cfPocket (R ω) (L ω) r := fun ω hω => by
    simp only [hC'def, cfPocket, hCG ω hω]
  set x : Ω → ℂ := fun ω => if ω ∈ A then p ω else negInv (e (Np ω)) with hxdef
  have hxm : Measurable x := Measurable.ite hA hp (measurable_negInv.comp (measurable_of_countable e |>.comp hNp))
  have hxC : ∀ ω, x ω ∈ closure (C' ω) := fun ω => by
    by_cases hω : ω ∈ A
    · simp only [hxdef, hω, ↓reduceIte]
      rw [hC'G ω (hAG hω)]
      exact (hpA ω hω).1
    · simp only [hxdef, hω, ↓reduceIte]
      exact subset_closure (mem_image_of_mem _ (hNpC ω))
  obtain ⟨N, hN, hNC, hNt⟩ := Lemma71E.exists_measurable_approach hC'o hC'm he hxm hxC
  -- the approximations
  have hdomC : ∀ ω (j : ℕ), e j ∈ C' ω → negInv (e j) ∈ ((c ω).dom : Set ℂ) := fun ω j hj => by
    rw [hdom ω]
    obtain ⟨w, hw, hwe⟩ := hj
    rw [← hwe, WangWu.negInv_negInv]
    exact hw
  have hF : Measurable fun y : Ω × ℕ =>
      {ω | negInv (e y.2) ∈ (c ω).dom}.indicator (fun ω => (c ω).1 (negInv (e y.2))) y.1 :=
    measurable_from_prod_countable_left fun j => hfm (negInv (e j))
  have hcm : ∀ m, Measurable fun ω => (c ω).1 (negInv (e (N m ω))) := fun m => by
    convert hF.comp (measurable_id.prodMk (hN m)) using 1
    funext ω
    simp only [comp_apply, id_eq]
    exact (indicator_of_mem (show ω ∈ {ω' | negInv (e (N m ω)) ∈ (c ω').dom} from hdomC ω _ (hNC m ω))
      (fun ω' => (c ω').1 (negInv (e (N m ω))))).symm
  refine measurable_of_tendsto_metrizable (f := fun m => A.indicator fun ω => negInv ((c ω).1 (negInv (e (N m ω)))))
    (fun m => (measurable_negInv.comp (hcm m)).indicator hA) (tendsto_pi_nhds.2 fun ω => ?_)
  by_cases hω : ω ∈ A
  · simp only [indicator_of_mem hω]
    have hωG := hAG hω
    have hxω : x ω = p ω := by simp only [hxdef, hω, ↓reduceIte]
    have hNt' := hNt ω
    rw [hxω, hC'G ω hωG] at hNt'
    have ht := (hpA ω hω).2.tendsto.comp hNt'
    refine ht.congr fun m => ?_
    simp only [comp_apply]
    exact hin ω hωG _ (hC'G ω hωG ▸ hNC m ω)
  · simp only [indicator_of_notMem hω]
    exact tendsto_const_nhds

/-- **The measurable Jordan coordinate of the random change pocket in the counterflow chart** (bounded case). For
random walls with measurable coordinates and a measurable event `G` on which they satisfy `IsChangeConfigInc` with the
flow seed not adherent to the pocket, there is a random `ψ ω`, a Jordan coordinate of `cfPocket` (`m(x₀) ↦ ∞`,
`m(y₀) ↦ 0`) for `ω ∈ G`, whose value at a measurable random point `p ω` of the closed pocket other than `m(x₀)` (on a
measurable `A ⊆ G`) is measurable. -/
theorem exists_measurable_cfJordanCoord (hRm : ∀ t, Measurable fun ω => R ω t)
    (hLm : ∀ t, Measurable fun ω => L ω t) (hGm : MeasurableSet G) (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r)
    (hG0 : ∀ ω ∈ G, (0 : ℂ) ∉ closure (changePocket (R ω) (L ω) r)) :
    ∃ ψ : Ω → ℂ → ℂ,
      (∀ ω ∈ G, Sec6.IsJordanCoord (cfPocket (R ω) (L ω) r) (cfPt (openPt (R ω) (L ω) r))
        (cfPt (closePt (R ω) (L ω) r)) (ψ ω)) ∧
      ∀ A : Set Ω, MeasurableSet A → A ⊆ G → ∀ p : Ω → ℂ, Measurable p →
        (∀ ω ∈ A, p ω ∈ closure (cfPocket (R ω) (L ω) r) \ {cfPt (openPt (R ω) (L ω) r)}) →
        Measurable (A.indicator fun ω => ψ ω (p ω)) := by
  classical
  obtain ⟨a, Ψ, haΨ, hmeas⟩ := exists_measurable_cfCoord hRm hLm hGm hG
  have hJ : ∀ ω ∈ G, Sec6.IsJordanCoord (cfPocket (R ω) (L ω) r) (cfPt (openPt (R ω) (L ω) r))
      (cfPt (closePt (R ω) (L ω) r)) (cfCoord (a ω) (Ψ ω) (closePt (R ω) (L ω) r)) := fun ω hω =>
    (hG ω hω).isJordanCoord_cfCoord (hG0 ω hω) (haΨ ω hω).2 (haΨ ω hω).1
  refine ⟨fun ω => if ω ∈ G then cfCoord (a ω) (Ψ ω) (closePt (R ω) (L ω) r) else 0, fun ω hω => ?_, ?_⟩
  · simp only [hω, ↓reduceIte]
    exact hJ ω hω
  intro A hA hAG p hp hpA
  have h := hmeas A hA hAG p hp fun ω hω => ⟨(hpA ω hω).1, ((hJ ω (hAG hω)).1 _ (hpA ω hω)).mono
    fun z hz => ⟨subset_closure hz, fun h' => (hG ω (hAG hω)).cfPt_openPt_notMem (h' ▸ hz)⟩⟩
  convert h using 1
  funext ω
  by_cases hω : ω ∈ A
  · simp only [indicator_of_mem hω, hAG hω, ↓reduceIte]
  · simp only [indicator_of_notMem hω]

/-- **The measurable Jordan coordinate at infinity of the random change pocket opening at the flow seed** (the case
`x₀ = x` of Aux. lemma 130, `rightLo = 0`): a random `ψ ω`, a Jordan coordinate at infinity of `cfPocket`
(`m(y₀) ↦ 0`) for `ω ∈ G`, whose value at every measurable random point of the closed pocket (on a measurable
`A ⊆ G`) is measurable. -/
theorem exists_measurable_cfJordanCoordInf (hRm : ∀ t, Measurable fun ω => R ω t)
    (hLm : ∀ t, Measurable fun ω => L ω t) (hGm : MeasurableSet G) (hG : ∀ ω ∈ G, IsChangeConfigInc (R ω) (L ω) r)
    (hG0 : ∀ ω ∈ G, rightLo (R ω) (L ω) r = 0) :
    ∃ ψ : Ω → ℂ → ℂ,
      (∀ ω ∈ G, Sec6.IsJordanCoordInf (cfPocket (R ω) (L ω) r) (cfPt (closePt (R ω) (L ω) r)) (ψ ω)) ∧
      ∀ A : Set Ω, MeasurableSet A → A ⊆ G → ∀ p : Ω → ℂ, Measurable p →
        (∀ ω ∈ A, p ω ∈ closure (cfPocket (R ω) (L ω) r)) →
        Measurable (A.indicator fun ω => ψ ω (p ω)) := by
  classical
  obtain ⟨a, Ψ, haΨ, hmeas⟩ := exists_measurable_cfCoord hRm hLm hGm hG
  have hJ : ∀ ω ∈ G, Sec6.IsJordanCoordInf (cfPocket (R ω) (L ω) r) (cfPt (closePt (R ω) (L ω) r))
      (cfCoord (a ω) (Ψ ω) (closePt (R ω) (L ω) r)) := fun ω hω =>
    (hG ω hω).isJordanCoordInf_cfCoord ((hG ω hω).openPt_eq_neg_one_iff.2 (hG0 ω hω)) (haΨ ω hω).2
      (haΨ ω hω).1
  refine ⟨fun ω => if ω ∈ G then cfCoord (a ω) (Ψ ω) (closePt (R ω) (L ω) r) else 0, fun ω hω => ?_, ?_⟩
  · simp only [hω, ↓reduceIte]
    exact hJ ω hω
  intro A hA hAG p hp hpA
  have h := hmeas A hA hAG p hp fun ω hω => ⟨hpA ω hω, ((hJ ω (hAG hω)).1 _ (hpA ω hω)).mono subset_closure⟩
  convert h using 1
  funext ω
  by_cases hω : ω ∈ A
  · simp only [indicator_of_mem hω, hAG hω, ↓reduceIte]
  · simp only [indicator_of_notMem hω]

end Random

end InteractingSLE.Sec7.PocketJordan
