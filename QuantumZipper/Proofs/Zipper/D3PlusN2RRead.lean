import QuantumZipper.Proofs.Zipper.D3PlusN2RWin
import QuantumZipper.Proofs.Zipper.D3PlusN2ModelLocMain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# N2 reader on the restricted index (Decision D36): the direct map `gK'` and node N2Z-MODELLOC'

Task D36-IMPL, step (1) and (5) (model side). The window reader of N2-zero is
`gK γ K R v = TmRichN1 γ K R 0 (v, 0) = locFieldFull R (zoomN1 γ 0 K (v, 0))`
(`D3PlusN2TmZStmt.lean`), a function of the raw window datum `v : LocIdx K → ℝ`. On the restricted
index `WinIdx K` (Decision D36) the datum is `v : WinIdx K → ℝ`, read off a field as
`resFieldW K y := fun i => y (winIdx K i)`.

**The reader only needs circles.** `gK` reads `v` exclusively through
`locModel γ 0 K (v, 0) : FieldSample`, whose defining clause is
`if μ ∈ circSet K then v ⟨μ, _⟩ + 0 + 0 else 0` (`D3PlusN1Model.locModel`), i.e. only at the
folded circles of `circSet K` strictly inside the window — exactly the circle part `WinCirc K` of
the restricted index (the pairing part of `locFieldFull R` is read from `0 : FieldSample` here and
is unaffected). Hence:

* `liftWin K v`: the canonical extension of a restricted datum to `LocIdx K` (junk `0` off
  `circSet K`), measurable in `v` (`measurable_liftWin`);
* `gKW γ K R v := gK γ K R (liftWin K v)`, the primed reader (`measurable_gKW`);
* `locModel_liftWin`: the readers' `locModel` agree for `liftWin K (resFieldW K y)` and
  `resField K y`; `scaleSur_eq_of_locModel_eq` transfers this to the scale (`M`/`Psi` depend on
  `p` only through `locModel γ L r p`, `D3PlusN1Scale.scaleSur`), so
* `gKW_eq_gK_of_resField` : `gKW γ K R (resFieldW K y) = gK γ K R (resField K y)` for **every**
  field `y` — the restricted window data determine the same rich data, with no hypothesis.

Consequently the primed window event `n2GoodW` (`liftWin K · ∈ n2Good γ K R`) is equivalent to
`n2Good` on restricted data (`n2GoodW_resFieldW`), and node N2Z-MODELLOC restricted to the
restricted index (`N2ZModelLocWinStmt`) follows from the *same* almost-sure regularity node
`N2ZModelRegStmt` as the unrestricted one (`n2ZModelLocWin_of_reg`): the events are literally
equal, so no new probability input is needed.

Sources: Duplantier–Miller–Sheffield, arXiv:1409.7055, proof of Prop. 4.8, p. 79; the
factorization is an own elementary argument (definitional unfolding of `locModel`/`scaleSur`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace D3Plus

/-! ## The canonical extension of a restricted datum -/

theorem exists_circWin (K : ℕ) {μ : Measure ℂ} (h : μ ∈ circSet (K : ℝ)) :
    ∃ i : WinCirc K, winIdx K (Sum.inl i) = μ := by
  obtain ⟨d, ρ, hρ, hdρ, rfl⟩ := exists_of_mem_circSet h
  exact ⟨⟨(d, ρ), hρ, hdρ⟩, rfl⟩

/-- A canonical restricted circle index of a measure of `circSet K`. -/
noncomputable def circWin (K : ℕ) {μ : Measure ℂ} (h : μ ∈ circSet (K : ℝ)) : WinCirc K :=
  Classical.choose (exists_circWin K h)

theorem winIdx_circWin (K : ℕ) {μ : Measure ℂ} (h : μ ∈ circSet (K : ℝ)) :
    winIdx K (Sum.inl (circWin K h)) = μ :=
  Classical.choose_spec (exists_circWin K h)

open Classical in
/-- The canonical extension of a restricted window datum to the full window index: the reader's
view of the datum (junk `0` off the folded circles of `circSet K`). -/
def liftWin (K : ℕ) (v : WinIdx K → ℝ) : LocIdx (K : ℝ) → ℝ :=
  fun μ => if h : μ.1 ∈ circSet (K : ℝ) then v (Sum.inl (circWin K h)) else 0

theorem measurable_liftWin (K : ℕ) : Measurable (liftWin K) := by
  classical
  refine measurable_pi_iff.2 fun μ => ?_
  by_cases h : μ.1 ∈ circSet (K : ℝ)
  · simp only [liftWin, dif_pos h]
    exact measurable_pi_apply _
  · simp only [liftWin, dif_neg h]
    exact measurable_const

/-- The restricted window data of a field. -/
def resFieldW (K : ℕ) (y : FieldSample) : WinIdx K → ℝ := fun i => y (winIdx K i)

/-! ## The reader factors through the restricted datum -/

/-- The readers' `locModel` is the same for `liftWin K (resFieldW K y)` and `resField K y`: both
read the field only at the folded circles of `circSet K`. -/
theorem locModel_liftWin (γ : ℝ) {K : ℕ} {y : FieldSample} {v : WinIdx K → ℝ}
    (hv : ∀ i, v i = y (winIdx K i)) :
    locModel γ 0 (K : ℝ) (fun μ : LocIdx (K : ℝ) => y μ.1, 0) =
      locModel γ 0 (K : ℝ) (liftWin K v, 0) := by
  classical
  funext μ
  by_cases h : μ ∈ circSet (K : ℝ)
  · have h1 : liftWin K v ⟨μ, isLocalH_of_mem_circSet h⟩ = y μ := by
      simp only [liftWin, dif_pos h, hv, winIdx_circWin]
    have hL : locModel γ 0 (K : ℝ) (fun μ' : LocIdx (K : ℝ) => y μ'.1, 0) μ = y μ := by
      rw [locModel, dif_pos h]
      simp
    have hR : locModel γ 0 (K : ℝ) (liftWin K v, 0) μ = y μ := by
      rw [locModel, dif_pos h]
      simp [h1]
    rw [hL, hR]
  · rw [locModel, locModel, dif_neg h, dif_neg h]

/-- `M γ (locModel γ L r) (bumpHD r) p a` depends on `p` only through `locModel γ L r p`
(`Prop16Area.Meas.M` is a supremum of `Psi γ x g p`, and `Psi γ x g p` reads `p` only through
`x p` and `g p`; `bumpHD r` is independent of `p`). -/
theorem Psi_eq_of_eq {α : Type*} [MeasurableSpace α] {γ : ℝ} {x : α → FieldSample}
    {g : α → ℂ → ℝ} {p p' : α} (hx : x p = x p') (hg : g p = g p') :
    Prop16Area.Meas.Psi γ x g p = Prop16Area.Meas.Psi γ x g p' := by
  simp only [Prop16Area.Meas.Psi, hx, hg]

theorem M_eq_of_locModel_eq {γ L r : ℝ} {p p' : N1Idx r}
    (h : locModel γ L r p = locModel γ L r p') :
    Prop16Area.Meas.M γ (locModel γ L r) (bumpHD r) p =
      Prop16Area.Meas.M γ (locModel γ L r) (bumpHD r) p' := by
  funext a
  simp only [Prop16Area.Meas.M]
  refine iSup_congr fun n => ?_
  refine congrArg ENNReal.ofReal ?_
  refine Psi_eq_of_eq h ?_
  funext z
  simp only [bumpHD]

/-- The measurable surrogate of the local scale is the same for `liftWin K (resFieldW K y)` and
`resField K y`. -/
theorem scaleSur_eq_of_locModel_eq {γ L r : ℝ} {p p' : N1Idx r}
    (h : locModel γ L r p = locModel γ L r p') : scaleSur γ L r p = scaleSur γ L r p' := by
  have hM : ∀ a : ℝ, Prop16Area.Meas.M γ (locModel γ L r) (bumpHD r) p a =
      Prop16Area.Meas.M γ (locModel γ L r) (bumpHD r) p' a :=
    fun a => congrFun (M_eq_of_locModel_eq h) a
  have key : ∀ q : N1Idx r, scaleSur γ L r q =
      sInf {a : ℝ | ∃ q' : ℚ, 0 < (q' : ℝ) ∧ (q' : ℝ) ≤ a ∧
        1 ≤ Prop16Area.Meas.M γ (locModel γ L r) (bumpHD r) q q'} := fun q => rfl
  rw [key p, key p']
  exact congrArg sInf (Set.ext fun a => by simp only [Set.mem_setOf_eq, hM])

/-- **The reader on the restricted index.** `gKW γ K R v` reads the rich local data from the
restricted window datum `v`. -/
def gKW (γ : ℝ) (K R : ℕ) (v : WinIdx K → ℝ) : (ℕ → ℝ) × (TestFun H → ℝ) :=
  gK γ K R (liftWin K v)

theorem measurable_gKW (γ : ℝ) (K R : ℕ) : Measurable (gKW γ K R) :=
  (measurable_gK γ K R).comp (measurable_liftWin K)

/-- **The reader reads the same data from the restricted datum**: `gK` applied to the full window
data of a field is `gKW` applied to its restricted window data. No hypothesis: both read the field
only at the folded circles of `circSet K`, where `liftWin K (resFieldW K y)` agrees with
`resField K y`. -/
theorem gKW_eq_gK_of_resField (γ : ℝ) (K R : ℕ) (y : FieldSample) :
    gKW γ K R (resFieldW K y) = gK γ K R (resField K y) := by
  have hv : ∀ i, resFieldW K y i = y (winIdx K i) := fun i => rfl
  have hL : locModel γ 0 (K : ℝ) (liftWin K (resFieldW K y), 0) =
      locModel γ 0 (K : ℝ) (resField K y, 0) := (locModel_liftWin γ hv).symm.trans (by rfl)
  have hS : scaleSur γ 0 (K : ℝ) (liftWin K (resFieldW K y), 0) =
      scaleSur γ 0 (K : ℝ) (resField K y, 0) := scaleSur_eq_of_locModel_eq hL
  simp only [gKW, gK, TmRichN1, zoomN1, hL, hS]

/-! ## The restricted window event -/

/-- The window event on the restricted index: the reader's scale lies in `(0, K/(R+2))`. -/
def n2GoodW (γ : ℝ) (K R : ℕ) : Set (WinIdx K → ℝ) := {v | liftWin K v ∈ n2Good γ K R}

theorem measurableSet_n2GoodW (γ : ℝ) (K R : ℕ) : MeasurableSet (n2GoodW γ K R) :=
  (measurableSet_n2Good γ K R).preimage (measurable_liftWin K)

/-- On restricted data the primed window event is the window event of the full-index node. -/
theorem n2GoodW_resFieldW (γ : ℝ) (K R : ℕ) (y : FieldSample) :
    resFieldW K y ∈ n2GoodW γ K R ↔ resField K y ∈ n2Good γ K R := by
  have hv : ∀ i, resFieldW K y i = y (winIdx K i) := fun i => rfl
  have hL : locModel γ 0 (K : ℝ) (liftWin K (resFieldW K y), 0) =
      locModel γ 0 (K : ℝ) (resField K y, 0) := (locModel_liftWin γ hv).symm.trans (by rfl)
  have hS : scaleSur γ 0 (K : ℝ) (liftWin K (resFieldW K y), 0) =
      scaleSur γ 0 (K : ℝ) (resField K y, 0) := scaleSur_eq_of_locModel_eq hL
  simp only [n2GoodW, n2Good, Set.mem_setOf_eq, hS]

/-! ## Node N2Z-MODELLOC on the restricted index -/

/-- **Node N2Z-MODELLOC'** (restricted index, D36 form of `N2ZModelLocStmt`): the restricted
window data of the embedded model determine the zoomed rich data, off events of vanishing
probability. -/
def N2ZModelLocWinStmt : Prop :=
  ∀ (γ α r : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → FieldSample),
    0 < γ → γ < 2 → α < Qc γ → 0 < r → IsFreeGFFModConstH X P →
    ∀ K R : ℕ, 0 < K → Tendsto (fun L => P {ω |
      resFieldW K (n2Emb γ α L r X ω) ∈ n2GoodW γ K R ∧
      TmRichN1 γ r R L (localZ X r ω, circData α fun _ => 0) ≠
        gKW γ K R (resFieldW K (n2Emb γ α L r X ω))}) atTop (𝓝 0)

/-- **N2Z-MODELLOC' from the model's almost sure regularity** (the same node
`N2ZModelRegStmt` as the unrestricted `n2ZModelLoc_of_reg`): the two disagreement events are
literally equal (`n2GoodW_resFieldW`, `gKW_eq_gK_of_resField`). -/
theorem n2ZModelLocWin_of_reg (hReg : N2ZModelRegStmt) : N2ZModelLocWinStmt := by
  intro γ α r Ω _ P _ X hγ hγ2 hα hr hX K R hK
  have hset : ∀ L : ℝ,
      {ω | resFieldW K (n2Emb γ α L r X ω) ∈ n2GoodW γ K R ∧
        TmRichN1 γ r R L (localZ X r ω, circData α fun _ => 0) ≠
          gKW γ K R (resFieldW K (n2Emb γ α L r X ω))} =
      {ω | resField K (n2Emb γ α L r X ω) ∈ n2Good γ K R ∧
        TmRichN1 γ r R L (localZ X r ω, circData α fun _ => 0) ≠
          gK γ K R (resField K (n2Emb γ α L r X ω))} := by
    intro L
    ext ω
    simp only [Set.mem_setOf_eq, n2GoodW_resFieldW, gKW_eq_gK_of_resField]
  simp only [hset]
  exact n2ZModelLoc_of_reg hReg γ α r P X hγ hγ2 hα hr hX K R hK

end D3Plus
end QuantumZipper
