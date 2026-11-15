import InteractingSLE.Spec.Supplement.LPAssembly
import InteractingSLE.Spec.Sec4.RepulsionDrift

/-!
# Amalgamation of coincident force marks (trace form)

Packet PROVE-LP. Corollary LP11 applies Wang–Wu's Theorem 1.8 at `κ = 4` (ruling R31); its Definition 1.2 lists
**distinct** positions on each side, while a frozen ordered force word may repeat a position. The specification
handles this by "amalgamating coincident groups on the same side by adding their weights" (§7.3, p. 378; LP10's
proof, p. 486). This file proves that step for the trace statement, discharging `LP.CoincidentMarksTraceStatement`
for every `κ` (`coincidentMarksTraceStatement`).

* Coincident marks have equal force coordinates before the lifetime: reused from
  `IsIntegratedSLEPath.vL_eq_of_xL_eq`, `IsIntegratedSLEPath.vR_eq_of_xR_eq` (`Spec/Sec4/RepulsionDrift.lean`;
  Wang–Wu Lemma 2.1).
* `amPos`, `amCls`: the distinct positions of a side in increasing order and the class map of a mark.
* `amalgamate…`: the amalgamated word (summed weights, one representative coordinate per class) of an ordered word is
  a distinct ordered word (`isDistinctForceWord_amalgamate`), and every integrated evolution of the word is, with the
  same driver, Brownian motion and lifetime, an integrated evolution of the amalgamated word
  (`IsIntegratedSLEEvolution.amalgamate`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace LP

/-! ### The amalgamated word -/

section Amalgamate

variable {n m : ℕ}

/-- The distinct positions of a list of marks, in increasing order. -/
def amPos (x : Fin n → ℝ) : Fin (Finset.univ.image x).card → ℝ :=
  (Finset.univ.image x).orderEmbOfFin rfl

theorem strictMono_amPos (x : Fin n → ℝ) : StrictMono (amPos x) :=
  ((Finset.univ.image x).orderEmbOfFin rfl).strictMono

/-- The class of a mark: the index of its position among the distinct positions. -/
def amCls (x : Fin n → ℝ) (i : Fin n) : Fin (Finset.univ.image x).card :=
  ((Finset.univ.image x).orderIsoOfFin rfl).symm ⟨x i, Finset.mem_image_of_mem x (Finset.mem_univ i)⟩

theorem amPos_amCls (x : Fin n → ℝ) (i : Fin n) : amPos x (amCls x i) = x i := by
  unfold amPos amCls
  rw [← Finset.coe_orderIsoOfFin_apply, OrderIso.apply_symm_apply]

theorem amCls_surjective (x : Fin n → ℝ) : Function.Surjective (amCls x) := by
  intro j
  obtain ⟨i, -, hi⟩ := Finset.mem_image.1 (Finset.orderEmbOfFin_mem (Finset.univ.image x) rfl j)
  refine ⟨i, (strictMono_amPos x).injective ?_⟩
  rw [amPos_amCls]
  exact hi

/-- A representative mark of a class. -/
def amRep (x : Fin n → ℝ) (j : Fin (Finset.univ.image x).card) : Fin n :=
  Function.surjInv (amCls_surjective x) j

theorem amCls_amRep (x : Fin n → ℝ) (j : Fin (Finset.univ.image x).card) : amCls x (amRep x j) = j :=
  Function.surjInv_eq _ _

theorem apply_amRep (x : Fin n → ℝ) (j : Fin (Finset.univ.image x).card) : x (amRep x j) = amPos x j := by
  rw [← amPos_amCls x (amRep x j), amCls_amRep]

/-- The summed weight of a class. -/
def amWeight (cls : Fin n → Fin m) (ρ : Fin n → ℝ) (j : Fin m) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => cls i = j), ρ i

/-- Regrouping a weighted sum by classes. -/
theorem sum_mul_comp_eq (cls : Fin n → Fin m) (ρ : Fin n → ℝ) (I : Fin m → ℝ) :
    ∑ i, ρ i * I (cls i) = ∑ j, amWeight cls ρ j * I j := by
  rw [← Finset.sum_fiberwise Finset.univ cls]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [amWeight, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i hi => by rw [(Finset.mem_filter.1 hi).2]

/-- Regrouping the colliding sum of the threshold condition by classes. -/
theorem sum_filter_comp_eq (cls : Fin n → Fin m) (ρ : Fin n → ℝ) (u : Fin m → ℝ) (c : ℝ) :
    ∑ i ∈ Finset.univ.filter (fun i => u (cls i) = c), ρ i =
      ∑ j ∈ Finset.univ.filter (fun j => u j = c), amWeight cls ρ j := by
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_fiberwise Finset.univ cls]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with h
  · exact Finset.sum_congr rfl fun i hi => by
      rw [(Finset.mem_filter.1 hi).2, ite_eq_left_of_eq_true _ _ (eq_true h)]
  · exact Finset.sum_eq_zero fun i hi => by
      rw [(Finset.mem_filter.1 hi).2, ite_eq_right_of_eq_false _ _ (eq_false h)]

/-- The threshold condition only sees the summed weights of coincident marks. -/
theorem thresholdCondition_comp_iff {nL nR mL mR : ℕ} (clsL : Fin nL → Fin mL) (clsR : Fin nR → Fin mR)
    (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (c : ℝ) (uL : Fin mL → ℝ) (uR : Fin mR → ℝ) :
    ForceWord.ThresholdCondition ρL ρR c (fun i => uL (clsL i)) (fun i => uR (clsR i)) ↔
      ForceWord.ThresholdCondition (amWeight clsL ρL) (amWeight clsR ρR) c uL uR := by
  unfold ForceWord.ThresholdCondition
  rw [sum_filter_comp_eq clsL ρL uL c, sum_filter_comp_eq clsR ρR uR c]

/-- The amalgamated left positions, in the frozen order (decreasing away from the seed). -/
def amXL (xL : Fin n → ℝ) (j : Fin (Finset.univ.image xL).card) : ℝ := amPos xL (Fin.rev j)

/-- The class of a left mark in the amalgamated left word. -/
def amClsL (xL : Fin n → ℝ) (i : Fin n) : Fin (Finset.univ.image xL).card := Fin.rev (amCls xL i)

/-- A representative of an amalgamated left mark. -/
def amRepL (xL : Fin n → ℝ) (j : Fin (Finset.univ.image xL).card) : Fin n := amRep xL (Fin.rev j)

theorem amXL_amClsL (xL : Fin n → ℝ) (i : Fin n) : amXL xL (amClsL xL i) = xL i := by
  simp [amXL, amClsL, amPos_amCls]

theorem amClsL_amRepL (xL : Fin n → ℝ) (j : Fin (Finset.univ.image xL).card) :
    amClsL xL (amRepL xL j) = j := by
  simp [amClsL, amRepL, amCls_amRep]

theorem apply_amRepL (xL : Fin n → ℝ) (j : Fin (Finset.univ.image xL).card) :
    xL (amRepL xL j) = amXL xL j := by
  simp [amXL, amRepL, apply_amRep]

theorem strictAnti_amXL (xL : Fin n → ℝ) : StrictAnti (amXL xL) := fun _ _ h =>
  strictMono_amPos xL (Fin.rev_lt_rev.2 h)

/-- An ordered force word with its coincident marks amalgamated is a force word with distinct positions. -/
theorem isDistinctForceWord_amalgamate {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    (hF : IsOrderedForceWord xL xR) : IsDistinctForceWord (amXL xL) (amPos xR) := by
  refine ⟨⟨(strictAnti_amXL xL).antitone, fun j => ?_, (strictMono_amPos xR).monotone, fun j => ?_⟩,
    strictAnti_amXL xL, strictMono_amPos xR⟩
  · rw [← apply_amRepL]; exact hF.2.1 _
  · rw [← apply_amRep]; exact hF.2.2.2 _

end Amalgamate

/-! ### Transfer of an integrated evolution to the amalgamated word -/

section Transfer

theorem integral_div_eq_mul (c : ℝ) (g : ℝ → ℝ) (t : ℝ) :
    ∫ r in (0 : ℝ)..t, c / g r = c * ∫ r in (0 : ℝ)..t, (g r)⁻¹ := by
  simp_rw [div_eq_mul_inv]
  exact intervalIntegral.integral_const_mul c _

/-- The force drift of a side regroups by classes once coincident coordinates agree on `[0, t]`. -/
theorem sum_integral_regroup {n m : ℕ} (cls : Fin n → Fin m) (rep : Fin m → Fin n) (ρ : Fin n → ℝ)
    (v : Fin n → ℝ≥0 → ℝ) (w : ℝ≥0 → ℝ) {t : ℝ≥0}
    (hv : ∀ i, ∀ s : ℝ≥0, s ≤ t → v i s = v (rep (cls i)) s) :
    ∑ i, ∫ s in (0 : ℝ)..t, ρ i / (w s.toNNReal - v i s.toNNReal) =
      ∑ j, ∫ s in (0 : ℝ)..t, amWeight cls ρ j / (w s.toNNReal - v (rep j) s.toNNReal) := by
  have h1 : ∀ i, ∫ s in (0 : ℝ)..t, ρ i / (w s.toNNReal - v i s.toNNReal) =
      ρ i * (fun j => ∫ s in (0 : ℝ)..t, (w s.toNNReal - v (rep j) s.toNNReal)⁻¹) (cls i) := fun i => by
    rw [integral_div_eq_mul]
    congr 1
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le (NNReal.coe_nonneg t)] at hs
    rw [hv i s.toNNReal (Real.toNNReal_le_iff_le_coe.2 hs.2)]
  rw [Finset.sum_congr rfl fun i _ => h1 i]
  refine (sum_mul_comp_eq cls ρ
    (fun j => ∫ s in (0 : ℝ)..t, (w s.toNNReal - v (rep j) s.toNNReal)⁻¹)).trans ?_
  exact Finset.sum_congr rfl fun j _ =>
    (integral_div_eq_mul (amWeight cls ρ j) (fun s => w s.toNNReal - v (rep j) s.toNNReal) t).symm

variable {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ} {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}

/-- **Amalgamation of an integrated path.** The integrated path of an ordered force word is, with the same driver,
Brownian path and lifetime, an integrated path of the amalgamated word (summed weights, one coordinate per class). -/
theorem _root_.InteractingSLE.IsIntegratedSLEPath.amalgamate (hF : IsOrderedForceWord xL xR)
    (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) :
    IsIntegratedSLEPath a (amXL xL) (amPos xR) (amWeight (amClsL xL) ρL) (amWeight (amCls xR) ρR) w
      (fun j => vL (amRepL xL j)) (fun j => vR (amRep xR j)) b ζ := by
  have hcL : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → ∀ i, vL i t = vL (amRepL xL (amClsL xL i)) t := fun t ht i =>
    hp.vL_eq_of_xL_eq ht (by rw [apply_amRepL xL (amClsL xL i), amXL_amClsL])
  have hcR : ∀ t : ℝ≥0, (t : ℝ≥0∞) < ζ → ∀ i, vR i t = vR (amRep xR (amCls xR i)) t := fun t ht i =>
    hp.vR_eq_of_xR_eq ht (by rw [apply_amRep xR (amCls xR i), amPos_amCls])
  obtain ⟨hw0, hvL0, hvR0, hcw, hcvL, hcvR, hanti, hLw, hwR, hmono, hiL, hiR, hweq, heL, heR, hnL, hnR,
    hnt, hz, hlim⟩ := hp
  refine ⟨hw0, fun j => ?_, fun j => ?_, hcw, fun j => hcvL _, fun j => hcvR _, fun t ht => ?_,
    fun t ht j => hLw t ht _, fun t ht j => hwR t ht _, fun t ht => ?_, fun t ht j => hiL t ht _,
    fun t ht j => hiR t ht _, fun t ht => ?_, fun t ht j => ?_, fun t ht j => ?_, fun j => hnL _,
    fun j => hnR _, fun t ht => ?_, fun hζ0 => ?_, fun T hT hTζ w₀ vL₀ vR₀ hT' => ?_⟩
  · show vL (amRepL xL j) 0 = amXL xL j
    rw [hvL0, apply_amRepL xL j]
  · show vR (amRep xR j) 0 = amPos xR j
    rw [hvR0, apply_amRep xR j]
  · intro j j' hjj'
    rcases eq_or_lt_of_le hjj' with rfl | hlt
    · exact le_rfl
    have hx : xL (amRepL xL j') < xL (amRepL xL j) := by
      rw [apply_amRepL xL j', apply_amRepL xL j]; exact strictAnti_amXL xL hlt
    have hidx : amRepL xL j ≤ amRepL xL j' :=
      (lt_of_not_ge fun hge => absurd (hF.1 hge) (not_le.2 hx)).le
    exact hanti t ht hidx
  · intro j j' hjj'
    rcases eq_or_lt_of_le hjj' with rfl | hlt
    · exact le_rfl
    have hx : xR (amRep xR j) < xR (amRep xR j') := by
      rw [apply_amRep xR j, apply_amRep xR j']; exact strictMono_amPos xR hlt
    have hidx : amRep xR j ≤ amRep xR j' :=
      (lt_of_not_ge fun hge => absurd (hF.2.2.1 hge) (not_le.2 hx)).le
    exact hmono t ht hidx
  · have hle : ∀ s : ℝ≥0, s ≤ t → (s : ℝ≥0∞) < ζ := fun s hs =>
      lt_of_le_of_lt (ENNReal.coe_le_coe.2 hs) ht
    rw [hweq t ht, sum_integral_regroup (amClsL xL) (amRepL xL) ρL vL w
        (fun i s hs => hcL s (hle s hs) i),
      sum_integral_regroup (amCls xR) (amRep xR) ρR vR w (fun i s hs => hcR s (hle s hs) i)]
  · show vL (amRepL xL j) t = amXL xL j + _
    rw [heL t ht, apply_amRepL xL j]
  · show vR (amRep xR j) t = amPos xR j + _
    rw [heR t ht, apply_amRep xR j]
  · intro hthr
    apply hnt t ht
    have hsL : (fun i => vL i t) = fun i => (fun j => vL (amRepL xL j) t) (amClsL xL i) :=
      funext (hcL t ht)
    have hsR : (fun i => vR i t) = fun i => (fun j => vR (amRep xR j) t) (amCls xR i) :=
      funext (hcR t ht)
    rw [hsL, hsR]
    exact (thresholdCondition_comp_iff (amClsL xL) (amCls xR) ρL ρR (w t) (fun j => vL (amRepL xL j) t)
      (fun j => vR (amRep xR j) t)).2 hthr
  · have h := (thresholdCondition_comp_iff (amClsL xL) (amCls xR) ρL ρR 0 (amXL xL) (amPos xR)).1
    simp only [amXL_amClsL, amPos_amCls] at h
    exact h (hz hζ0)
  · have hev : ∀ᶠ t : ℝ≥0 in 𝓝[<] T, (t : ℝ≥0∞) < ζ := by
      rw [← hTζ]
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact ENNReal.coe_lt_coe.2 (show t < T from ht)
    have h1 : Tendsto (fun t => w t) (𝓝[<] T) (𝓝 w₀) := (continuous_fst.tendsto _).comp hT'
    have h2 : Tendsto (fun t => fun j => vL (amRepL xL j) t) (𝓝[<] T) (𝓝 vL₀) :=
      (continuous_fst.tendsto _).comp ((continuous_snd.tendsto _).comp hT')
    have h3 : Tendsto (fun t => fun j => vR (amRep xR j) t) (𝓝[<] T) (𝓝 vR₀) :=
      (continuous_snd.tendsto _).comp ((continuous_snd.tendsto _).comp hT')
    have h2' : Tendsto (fun t => fun i => vL i t) (𝓝[<] T) (𝓝 fun i => vL₀ (amClsL xL i)) :=
      tendsto_pi_nhds.2 fun i => ((tendsto_pi_nhds.1 h2) (amClsL xL i)).congr'
        (hev.mono fun t ht => (hcL t ht i).symm)
    have h3' : Tendsto (fun t => fun i => vR i t) (𝓝[<] T) (𝓝 fun i => vR₀ (amCls xR i)) :=
      tendsto_pi_nhds.2 fun i => ((tendsto_pi_nhds.1 h3) (amCls xR i)).congr'
        (hev.mono fun t ht => (hcR t ht i).symm)
    exact (thresholdCondition_comp_iff _ _ ρL ρR w₀ vL₀ vR₀).1
      (hlim T hT hTζ w₀ _ _ (h1.prodMk_nhds (h2'.prodMk_nhds h3')))

/-- **Amalgamation of an integrated evolution**: an integrated `SLE_a(ρ)` evolution of an ordered force word is, with
the same filtration, driver, Brownian motion and lifetime, an integrated evolution of the amalgamated word. -/
theorem _root_.InteractingSLE.IsIntegratedSLEEvolution.amalgamate {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (hF : IsOrderedForceWord xL xR)
    (hE : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ) :
    IsIntegratedSLEEvolution a (amXL xL) (amPos xR) (amWeight (amClsL xL) ρL) (amWeight (amCls xR) ρR)
      P 𝓕 W (fun j => VL (amRepL xL j)) (fun j => VR (amRep xR j)) B ζ :=
  ⟨hE.1, hE.2.1, fun _ => hE.2.2.1 _, fun _ => hE.2.2.2.1 _,
    hE.2.2.2.2.mono fun _ hω => hω.amalgamate hF⟩

end Transfer

/-- **The amalgamation obligation of LP11 at `κ = 4`, trace form, is discharged** (for every `κ`): if every force
word with distinct positions on each side is complete, so is every ordered force word. -/
theorem coincidentMarksTraceStatement (κ : ℝ) : CoincidentMarksTraceStatement.{u} κ := by
  intro hdist nL nR xL xR ρL ρR hF Ω mΩ P _ 𝓕 W VL VR B ζ hE
  exact hdist (amXL xL) (amPos xR) _ _ (isDistinctForceWord_amalgamate hF) P 𝓕 W _ _ B ζ
    (hE.amalgamate hF)

/-- **Wang–Wu's Theorem 1.8 for every ordered force word from its distinct-position form**, by amalgamation. -/
theorem wwTheorem18Statement_of_distinct (h : WWTheorem18DistinctStatement.{u}) : WWTheorem18Statement.{u} :=
  coincidentMarksTraceStatement 4 h

end LP

end InteractingSLE
