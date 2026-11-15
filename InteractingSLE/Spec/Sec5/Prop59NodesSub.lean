/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop59NodesFarWire

/-!
# Proposition 5.9's node experiments as subtrees of a tree of pieces

Packet PROVE-PROP59-NODES. Specification §5.2, proof of Proposition 5.13 (p. 148: the alternating construction is
also run from the terminal point of every allowed finite prefix). The candidate pieces of the experiment at a node
are the pieces of a tree of candidate pieces read **after a fixed prefix of switches** (the node's own schedule):
candidate `(j, t)` of the node is candidate `(m + j, pre ++ t)` of the tree, re-indexed (`subFam`). This file proves
that the node family inherits everything PROVE-PROP59T4's stage system needs:

* `reindexPiece`, **`subFam`**: the re-indexed family (`nL₀ + (m + j) = (nL₀ + m) + j` marks);
* `IsRegFam.subFam`: regularity passes to the subtree;
* `IsChainAll`: chain data **without the far-gap premise** (the trace of PROVE-PROP59-PIECES' chain lemma exists
  for every time before the lifetime); `TreeData.isChainAll` proves it for every tree of paths;
* **`IsChainAll.subFam`**: the node family has per-switch chain data `IsChainFamEx` with the start
  `start (m + j) (pre ++ t) − start m pre` and **the same chart and the same image set** — no Loewner shift is needed:
  the trace of the whole path over `[0, start′ + s]` is an initial part of its trace over `[0, start + s]` (the node
  prefix's own image is part of the image set, which only has to be bounded when the node target is);
* `subCandExpF`: the node experiment (`CandExpF`) from such a subtree and the node data.

The far-gap premise of `IsChainFamEx` depends on the parity of the depth, which differs between the node and the tree
when the prefix has odd length; the gap-free form `IsChainAll` makes the reduction parity-free.

Conditional helpers with distinct names; they replace no source theorem.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Function
open QuantumZipper (H fwdHull fwdMap)
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec5.Prop59Nodes

open Prop59Stage Prop59Tips Prop59System Prop59Pieces

/-! ### Re-indexed pieces and subtrees -/

section Sub

variable {Ω : Type*} {nL₀ nR₀ : ℕ}

/-- **A piece with re-indexed marks** (along equalities of the numbers of marks). -/
def reindexPiece {a b c d : ℕ} (h₁ : a = b) (h₂ : c = d) (p : Piece Ω a c) : Piece Ω b d where
  W := p.W
  VL i := p.VL (Fin.cast h₁.symm i)
  VR k := p.VR (Fin.cast h₂.symm k)
  B := p.B
  ζ := p.ζ
  clk := p.clk

/-- **The subtree after a prefix of switches**: candidate `(j, t)` is candidate `(m + j, pre ++ t)` of the tree. -/
def subFam (cand : CandFam Ω nL₀ nR₀) (m : ℕ) (pre : Fin m → ℝ≥0) : CandFam Ω (nL₀ + m) (nR₀ + m) :=
  fun j t => reindexPiece (Nat.add_assoc nL₀ m j).symm (Nat.add_assoc nR₀ m j).symm (cand (m + j) (Fin.append pre t))

theorem subFam_clk (cand : CandFam Ω nL₀ nR₀) (m : ℕ) (pre : Fin m → ℝ≥0) (j : ℕ) (t : Fin j → ℝ≥0) :
    (subFam cand m pre j t).clk = (cand (m + j) (Fin.append pre t)).clk := rfl

theorem subFam_ζ (cand : CandFam Ω nL₀ nR₀) (m : ℕ) (pre : Fin m → ℝ≥0) (j : ℕ) (t : Fin j → ℝ≥0) :
    (subFam cand m pre j t).ζ = (cand (m + j) (Fin.append pre t)).ζ := rfl

variable [MeasurableSpace Ω]

theorem isRegPiece_reindexPiece {a b c d : ℕ} (h₁ : a = b) (h₂ : c = d) {p : Piece Ω a c} (hp : IsRegPiece p) :
    IsRegPiece (reindexPiece h₁ h₂ p) where
  W := hp.W
  VL _ := hp.VL _
  VR _ := hp.VR _
  ζ := hp.ζ
  clk := hp.clk
  clk_cont := hp.clk_cont
  clk_mono := hp.clk_mono
  W_cont := hp.W_cont
  VL_cont ω _ := hp.VL_cont ω _
  VR_cont ω _ := hp.VR_cont ω _

/-- **Regularity passes to a subtree.** -/
theorem IsRegFam.subFam {cand : CandFam Ω nL₀ nR₀} (h : IsRegFam cand) (m : ℕ) (pre : Fin m → ℝ≥0) :
    IsRegFam (Prop59Nodes.subFam cand m pre) :=
  fun j t => isRegPiece_reindexPiece _ _ (h (m + j) (Fin.append pre t))

/-- **Chain data without the far-gap premise**: the start is `0` at the root and adds the piece time at each switch,
and before the lifetime of every candidate some Loewner trace from `0` covers its prefix inside the closure of `C`. -/
structure IsChainAll (P : Measure Ω) (cand : CandFam Ω nL₀ nR₀) (C : Ω → Set ℂ)
    (start : (j : ℕ) → (Fin j → ℝ≥0) → Ω → ℝ) : Prop where
  start_zero : ∀ᵐ ω ∂P, start 0 Fin.elim0 ω = 0
  step : ∀ j (t : Fin j → ℝ≥0) (q : ℝ≥0), ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (cand j t).clk ω s = q →
    (s : ℝ≥0∞) < (cand j t).ζ ω → start (j + 1) (Fin.snoc (α := fun _ => ℝ≥0) t q) ω = start j t ω + s
  trace : ∀ j (t : Fin j → ℝ≥0), ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ≥0∞) < (cand j t).ζ ω →
    ∃ (W' : ℝ → ℝ) (η : ℝ → ℂ) (T : ℝ), Continuous W' ∧ W' 0 = 0 ∧ IsLoewnerTraceLT W' T η ∧
      start j t ω + s < T ∧ η '' Icc 0 (start j t ω + s) ⊆ closure (C ω)

/-- Gap-free chain data are per-switch chain data (for every pair of far marks). -/
theorem IsChainAll.isChainFamEx {P : Measure Ω} {cand : CandFam Ω nL₀ nR₀} {C : Ω → Set ℂ}
    {start : (j : ℕ) → (Fin j → ℝ≥0) → Ω → ℝ} (h : IsChainAll P cand C start) (hnL : 0 < nL₀) (hnR : 0 < nR₀) :
    IsChainFamEx P cand hnL hnR C start where
  start_zero := h.start_zero
  step := h.step
  trace j t := (h.trace j t).mono fun _ hω s hs _ => hω s hs

/-- **The node family has per-switch chain data** in the same chart and with the same image set: the start of the
node candidate `(j, t)` is `start (m + j) (pre ++ t) − start m pre`, and the trace of the tree candidate covers the
shorter initial part. -/
theorem IsChainAll.subFam {P : Measure Ω} {cand : CandFam Ω nL₀ nR₀} {C : Ω → Set ℂ}
    {start : (j : ℕ) → (Fin j → ℝ≥0) → Ω → ℝ} (h : IsChainAll P cand C start) (m : ℕ) (pre : Fin m → ℝ≥0)
    (h0 : ∀ᵐ ω ∂P, 0 ≤ start m pre ω) (hnL : 0 < nL₀ + m) (hnR : 0 < nR₀ + m) :
    IsChainFamEx P (Prop59Nodes.subFam cand m pre) hnL hnR C
      (fun j t ω => start (m + j) (Fin.append pre t) ω - start m pre ω) where
  start_zero := ae_of_all _ fun ω => by
    show start (m + 0) (Fin.append pre Fin.elim0) ω - start m pre ω = 0
    rw [Fin.append_elim0]
    simp
  step j t q := (h.step (m + j) (Fin.append pre t) q).mono fun ω hω s hs hsζ => by
    show start (m + (j + 1)) (Fin.append pre (Fin.snoc t q)) ω - start m pre ω =
      start (m + j) (Fin.append pre t) ω - start m pre ω + s
    rw [Fin.append_snoc]
    have e : start (m + (j + 1)) (Fin.snoc (α := fun _ => ℝ≥0) (Fin.append pre t) q) ω =
        start (m + j) (Fin.append pre t) ω + s := hω s hs hsζ
    rw [e]
    ring
  trace j t := by
    filter_upwards [h.trace (m + j) (Fin.append pre t), h0] with ω hω h0ω s hs _
    obtain ⟨W', η, T, hc, hW0, hη, hT, himg⟩ := hω s hs
    refine ⟨W', η, T, hc, hW0, hη, by linarith, (image_mono (Icc_subset_Icc le_rfl ?_)).trans himg⟩
    linarith

end Sub

/-! ### Gap-free chain data of a tree of paths -/

section Tree

open WangWu WangWu.ImgWord GlueCond CrossCond.Word49 LawUnique CrossRestart
open Sec7.Lemma71C (capClock)

variable {Ω : Type*} [MeasurableSpace Ω] {nL₀ nR₀ : ℕ} (D : TreeData Ω nL₀ nR₀)

/-- **Gap-free chain data of a tree of paths** (PROVE-PROP59-PIECES' `TreeData.isChainFamEx`, whose trace does not use
the far-gap premise). -/
theorem TreeData.isChainAll (hD : D.IsReg) (hT : D.IsTree) {P : Measure Ω} {Z : Ω → Set ℂ}
    (hnode : ∀ᵐ ω ∂P, ∀ j t, D.valid j t → ∀ q : ℚ, 0 < (q : ℝ) → D.α j t ω q ∈ Z ω) :
    IsChainAll P D.cand (D.image Z) (recStart D.cand) where
  start_zero := ae_of_all _ fun _ => rfl
  step j t q := ae_of_all _ fun ω s hs _ =>
    recStart_step (fun j t ω => strictMono_arcClk (hD.isKilledFamily j t).arc ω) j t q ω s hs
  trace j t := by
    filter_upwards [hnode] with ω hZ s hs
    obtain ⟨hA, hlt⟩ := lt_arcζ_iff.1 hs
    have hγ := (hD.isKilledFamily j t).arc ω
    rw [D.recStart_eq hD hT j t ω hA]
    obtain ⟨S, hSP, hSlt⟩ := lt_kLife_iff.1 hlt
    rw [NNReal.coe_add] at hSlt
    have hS0 : 0 < S := by
      rcases (hγ.nonneg S hSP).eq_or_lt with h | h
      · rw [← h, hγ.capClock_zero] at hSlt
        exact absurd hSlt (not_lt.2 (add_nonneg (D.startCap j t ω).coe_nonneg s.coe_nonneg))
      · exact h
    obtain ⟨w, hw, hw0, -, η, hηL, -, hηγ⟩ := hγ.exists_traceDriver hSP hS0
    refine ⟨w, η, (D.startCap j t ω : ℝ) + s + 1, hw, hw0,
      ⟨hηL.1, hηL.2.1.mono Ico_subset_Ici_self, fun t' ht' _ => hηL.2.2 t' ht'⟩, by linarith, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    have hτle : x.toNNReal ≤ D.startCap j t ω + s := by
      rw [Real.toNNReal_le_iff_le_coe, NNReal.coe_add]; exact hx.2
    have hτ : ((x.toNNReal : ℝ≥0) : WithTop ℝ≥0) < kLife (D.img j t ω) (D.pre j t ω) :=
      lt_of_le_of_lt (WithTop.coe_le_coe.2 hτle) hlt
    obtain ⟨hm, he⟩ := hγ.kInv_spec hτ
    have hle : kInv (D.img j t ω) (D.pre j t ω) x.toNNReal ≤ S :=
      hγ.kInv_le hSP hτ (by rw [Real.coe_toNNReal _ hx.1]; linarith [hx.2])
    have hxe : x = capClock (D.img j t ω) (kInv (D.img j t ω) (D.pre j t ω) x.toNNReal) := by
      rw [he, Real.coe_toNNReal _ hx.1]
    rw [hxe, hηγ _ ⟨hγ.nonneg _ hm, hle⟩]
    exact D.mem_closure_image hD hA.1 (hZ j t hA.1.1) hm

omit [MeasurableSpace Ω] in
/-- The recursive start of a tree of pieces is nonnegative. -/
theorem recStart_nonneg (cand : CandFam Ω nL₀ nR₀) : ∀ (j : ℕ) (t : Fin j → ℝ≥0) (ω : Ω), 0 ≤ recStart cand j t ω
  | 0, _, _ => le_rfl
  | j + 1, t, ω => by
    simp only [recStart]
    exact add_nonneg (recStart_nonneg cand j _ ω) (candInv cand j (Fin.init t) (t (Fin.last j)) ω).coe_nonneg

end Tree

/-! ### Node experiments from subtrees -/

section Exp

variable {κ : ℝ} {Ω Ωa : Type} [MeasurableSpace Ω] [MeasurableSpace Ωa] {P : Measure Ω} [IsProbabilityMeasure P]
  {Pa : Measure Ωa} [IsProbabilityMeasure Pa]

/-- **A node experiment as a subtree** (at every positive rational counterflow time, on `Ω × Ωa`): a tree of candidate
pieces `cand r` with regularity and gap-free chain data in the image set `image r`, read after the deterministic prefix
`pre` of `m` switches (the node's own schedule); the node's initial start, event and revealed history; the killed
staged law of the realized node construction; the node's initial word; bounded images for bounded targets; and the
initial event. -/
structure SubExpF (κ : ℝ) (P : Measure Ω) (Pa : Measure Ωa) (D : ℚ → Ω → Set ℂ) (A : ℚ → Set Ω) where
  nL : ℚ → ℕ
  nR : ℚ → ℕ
  /-- The length of the node prefix. -/
  m : ℕ
  /-- The switching clock values of the node prefix. -/
  pre : Fin m → ℝ≥0
  posL : ∀ r, 0 < nL r + m
  posR : ∀ r, 0 < nR r + m
  rhoL : (r : ℚ) → Fin (nL r + m) → ℝ
  rhoR : (r : ℚ) → Fin (nR r + m) → ℝ
  grid : ℚ → Set ℝ≥0
  mesh : ℚ → ℕ → ℝ≥0
  times : ℚ → ℕ → ℕ → ℝ≥0
  grid_ok : ∀ r n, IsSwitchGrid (grid r) (mesh r n) (times r n)
  mesh_ok : ∀ r, Tendsto (mesh r) atTop (𝓝 0)
  /-- The tree of candidate pieces (in the dilated joint chart of the root). -/
  cand : (r : ℚ) → CandFam (Ω × Ωa) (nL r) (nR r)
  /-- The node's initial start. -/
  y₀ : (r : ℚ) → Ω × Ωa → Start (nL r + m + 0) (nR r + m + 0)
  R₀ : ℚ → Set (Ω × Ωa)
  base : ℚ → MeasurableSpace (Ω × Ωa)
  /-- The image set (node prefix and descendants) in the chart of the tree. -/
  image : ℚ → Ω × Ωa → Set ℂ
  start : (r : ℚ) → (j : ℕ) → (Fin j → ℝ≥0) → Ω × Ωa → ℝ
  reg : ∀ r : ℚ, 0 < r → IsRegFam (cand r)
  chain : ∀ r : ℚ, 0 < r → IsChainAll (P.prod Pa) (cand r) (image r) (start r)
  start_pre : ∀ r : ℚ, 0 < r → ∀ᵐ ω' ∂(P.prod Pa), 0 ≤ start r m pre ω'
  y₀_meas : ∀ r : ℚ, 0 < r → Measurable (y₀ r)
  base_le : ∀ r : ℚ, 0 < r → base r ≤ (inferInstance : MeasurableSpace (Ω × Ωa))
  R₀_meas : ∀ r : ℚ, 0 < r → MeasurableSet[base r] (R₀ r)
  init : ∀ r : ℚ, 0 < r → ∀ᵐ ω' ∂(P.prod Pa), ω' ∈ R₀ r → (y₀ r ω').1 = 0 ∧
    (y₀ r ω').1 + (y₀ r ω').2.1 (farL (by have := posL r; omega : 0 < nL r + m + 0)) ≤ -3 ∧
    3 ≤ (y₀ r ω').1 + (y₀ r ω').2.2 (farR (by have := posR r; omega : 0 < nR r + m + 0))
  /-- **The killed staged law of the realized node construction.** -/
  pieceLaw : ∀ r : ℚ, 0 < r → Prop59StageLawFarStatement κ (P.prod Pa) (posL r) (posR r) (rhoL r) (rhoR r)
    (histSys (subFam (cand r) m pre) (times r) (posL r) (posR r) (y₀ r) (R₀ r) (base r))
  initialWord : ∀ r : ℚ, 0 < r → IsStageInit κ (rhoL r) (rhoR r)
  image_bdd : ∀ r : ℚ, 0 < r → ∀ ω' : Ω × Ωa, Bornology.IsBounded (D r ω'.1) → Bornology.IsBounded (image r ω')
  active : ∀ r : ℚ, 0 < r → ∀ᵐ ω' ∂(P.prod Pa), ω'.1 ∈ A r → ω' ∈ R₀ r

/-- **A subtree experiment is a candidate experiment** (`IsChainAll.subFam`, `IsRegFam.subFam`). -/
def SubExpF.toCandExpF {D : ℚ → Ω → Set ℂ} {A : ℚ → Set Ω} (X : SubExpF κ P Pa D A) : CandExpF κ P Pa D A where
  nL r := X.nL r + X.m
  nR r := X.nR r + X.m
  posL := X.posL
  posR := X.posR
  rhoL := X.rhoL
  rhoR := X.rhoR
  grid := X.grid
  mesh := X.mesh
  times := X.times
  grid_ok := X.grid_ok
  mesh_ok := X.mesh_ok
  cand r := subFam (X.cand r) X.m X.pre
  y₀ := X.y₀
  R₀ := X.R₀
  base := X.base
  image := X.image
  start r j t ω' := X.start r (X.m + j) (Fin.append X.pre t) ω' - X.start r X.m X.pre ω'
  reg r hr := IsRegFam.subFam (X.reg r hr) X.m X.pre
  y₀_meas := X.y₀_meas
  base_le := X.base_le
  R₀_meas := X.R₀_meas
  init := X.init
  chain r hr := (X.chain r hr).subFam X.m X.pre (X.start_pre r hr) (X.posL r) (X.posR r)
  pieceLaw := X.pieceLaw
  initialWord := X.initialWord
  image_bdd := X.image_bdd
  active := X.active

end Exp

/-! ### Proposition 5.13 from the root experiment and the node subtrees -/

open Sec4 Prop513Schedule Prop513TreeExtract Prop513Target Prop513Wire Restart
open LQGMetric Exist Exist.Staged Exist.StagedLaw

/-- **Proposition 5.13 from the killed-law root experiment and the node subtree experiments.** -/
theorem prop513_path_of_partA_reverseVisit_subExpF
    (h44 : Sec7.AdmCode.Theorem12ParamCond44Statement.{0})
    (hA : PartAInputsSixteenDiv)
    {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hb : IsFig51Bounds κ a b a' b')
    {Ω : Type} {𝒢 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} (hh𝒢 : Measurable[𝒢] h)
    (hG : IsStripGFF κ P h (fig51Lower a b) (fig51Upper x₀ a' b') {0} {x₀})
    {W : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} {γ : Ω → ℝ≥0 → ℂ}
    (hcf : IsStripCounterflowDriver κ 0 (Real.exp (π * x₀)) P h W ζ)
    (htr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (γ ω))
    {E : Schedule → ℕ → Ω → Driver}
    (hE : ∀ s, IsStagedHistory κ (sourceWord (x₀ := x₀) hκ hb).fn
      (sourceWord (x₀ := x₀) hκ hb).jumps P
      (fun ω => targetField κ (Real.exp (π * x₀)) (Real.exp_pos _) (h ω)) (scheduleSpec s) (E s))
    (hR : ∀ s, StagedPiecesRegular κ (sourceWord (x₀ := x₀) hκ hb).fn
      (sourceWord (x₀ := x₀) hκ hb).jumps P (scheduleSpec s) (E s))
    (hVisit : StripReverseVisitLaw (Real.exp (π * x₀)) P E γ)
    {Ωa : Type} [MeasurableSpace Ωa] [StandardBorelSpace Ωa] {Pa : Measure Ωa} [IsProbabilityMeasure Pa]
    (X₀ : CandExpF κ P Pa (rootTarget W (extremeAngleTreeNode (capacityTree (driverTree E)) treeTime))
      fun _ => univ)
    (X : ∀ n, SubExpF κ P Pa
      (nodeTarget W (extremeAngleTreeDescendants (capacityTree (driverTree E)) treeTime descendantIndex n))
      (nodeActive γ (extremeAngleTreeNode (capacityTree (driverTree E)) treeTime n))) :
    ∃ Γ' : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[𝒢] fun ω => Γ' ω t) ∧
      ∀ᵐ ω ∂P, Γ' ω = γ ω :=
  prop513_path_of_partA_reverseVisit_candExpF h44 hA hκ hκ4 hb hh𝒢 hG hcf htr hE hR hVisit X₀
    fun n => (X n).toCandExpF

end InteractingSLE.Sec5.Prop59Nodes
