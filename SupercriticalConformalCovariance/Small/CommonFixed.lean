import Mathlib.Probability.Kernel.IonescuTulcea.Traj

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory

namespace SupercriticalConformalCovariance.Small

universe u v w

noncomputable def commonFixedKernel {F : Type u} {Y : Type v}
    [MeasurableSpace F] [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    {Ω : Type w} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (H : ℕ → Ω → F) (R : ℕ → Ω → Y) (n : ℕ) :
    Kernel (Π i : Finset.Iic n, F × Y) (F × Y) :=
  let fld : (Π i : Finset.Iic n, F × Y) → F :=
    fun x => (x ⟨0, Finset.mem_Iic.mpr (Nat.zero_le n)⟩).1
  (Kernel.deterministic fld ((measurable_pi_apply _).fst) ×ₖ
    (condDistrib (R n) (H n) P).comap fld ((measurable_pi_apply _).fst))

instance commonFixedKernel_markov {F : Type u} {Y : Type v}
    [MeasurableSpace F] [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    {Ω : Type w} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (H : ℕ → Ω → F) (R : ℕ → Ω → Y) :
    ∀ n, IsMarkovKernel (commonFixedKernel P H R n) :=
  fun n => by
    unfold commonFixedKernel
    infer_instance

noncomputable def commonFixedMeasure {F : Type u} {Y : Type v}
    [MeasurableSpace F] [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    {Ω : Type w} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (H : ℕ → Ω → F) (R : ℕ → Ω → Y) (μ : Measure F) [IsProbabilityMeasure μ]
    (y0 : Y) : Measure (Π i : ℕ, F × Y) :=
  Kernel.trajMeasure (μ.map (fun x => (x,y0))) (commonFixedKernel P H R)

theorem commonFixedKernel_fst {F : Type u} {Y : Type v}
    [MeasurableSpace F] [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    {Ω : Type w} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (H : ℕ → Ω → F) (R : ℕ → Ω → Y) (n : ℕ) :
    (commonFixedKernel P H R n).fst =
      Kernel.deterministic
        (fun (x : Π i : Finset.Iic n, F × Y) =>
          (x ⟨0, Finset.mem_Iic.mpr (Nat.zero_le n)⟩).1)
        ((measurable_pi_apply _).fst) := by
  unfold commonFixedKernel
  simp

theorem commonFixedMeasure_field {F : Type u} {Y : Type v}
    [MeasurableSpace F] [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    {Ω : Type w} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (H : ℕ → Ω → F) (R : ℕ → Ω → Y) (μ : Measure F) [IsProbabilityMeasure μ]
    (y0 : Y) :
    (commonFixedMeasure P H R μ y0).map (fun x => (x 0).1) = μ := by
  classical
  let κ := commonFixedKernel P H R
  let ev : (Π i : Finset.Iic 0, F × Y) → F :=
    fun x => (x ⟨0, Finset.mem_Iic.mpr le_rfl⟩).1
  have hev : Measurable ev := (measurable_pi_apply _).fst
  have hcoord : (fun x : Π i : ℕ, F × Y => (x 0).1) =
      ev ∘ Preorder.frestrictLe 0 := rfl
  have hker : (Kernel.traj κ 0).map (fun (x : ℕ → F × Y) => (x 0).1) =
      Kernel.deterministic ev hev := by
    rw [hcoord, Kernel.map_comp_right _ (Preorder.measurable_frestrictLe 0) hev,
      (Kernel.traj_map_frestrictLe_of_le (X := fun _ : ℕ => F × Y) (κ := κ) (show (0 : ℕ) ≤ 0 by omega))]
    ext x s hs
    simp only [Kernel.map_apply' _ hev _ hs, Kernel.deterministic_apply,
      Measure.dirac_apply' _ (hev hs), Measure.dirac_apply' _ hs]
    have hval : ev (Preorder.frestrictLe₂ (π := fun _ : ℕ => F × Y)
      (le_refl (0 : ℕ)) x) = ev x := by simp [ev]
    change (if ev (Preorder.frestrictLe₂ (π := fun _ : ℕ => F × Y)
      (le_refl (0 : ℕ)) x) ∈ s then 1 else 0) =
      (if ev x ∈ s then 1 else 0)
    rw [hval]
  unfold commonFixedMeasure Kernel.trajMeasure
  have hsymm : Measurable
      (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => F × Y)).symm :=
    (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => F × Y)).symm.measurable
  have hinit : Measurable (fun x : F => (x,y0)) := measurable_id.prodMk measurable_const
  rw [Measure.map_comp _ _ ((measurable_pi_apply 0).fst), hker,
    Measure.deterministic_comp_eq_map, Measure.map_map hev hsymm,
    Measure.map_map (hev.comp hsymm) hinit]
  have he : ev ∘ (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => F × Y)).symm ∘
      (fun x : F => (x,y0)) = id := by funext x; rfl
  change μ.map (ev ∘ (MeasurableEquiv.piUnique
    (fun _ : Finset.Iic 0 => F × Y)).symm ∘ (fun x : F => (x,y0))) = μ
  rw [he, Measure.map_id]

theorem commonFixedKernel_pair_law {F : Type u} {Y : Type v}
    [MeasurableSpace F] [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    {Ω : Type w} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (H : ℕ → Ω → F) (R : ℕ → Ω → Y) (n : ℕ)
    (hH : Measurable (H n)) (hR : Measurable (R n))
    (ν : Measure (Π i : Finset.Iic n, F × Y)) [SFinite ν]
    (hν : ν.map (fun x => (x ⟨0, Finset.mem_Iic.mpr (Nat.zero_le n)⟩).1) =
      P.map (H n)) :
    (ν ⊗ₘ commonFixedKernel P H R n).map
      (fun t => ((t.1 ⟨0, Finset.mem_Iic.mpr (Nat.zero_le n)⟩).1, t.2.2)) =
      P.map (fun ω => (H n ω, R n ω)) := by
  let f : (Π i : Finset.Iic n, F × Y) → F :=
    fun x => (x ⟨0, Finset.mem_Iic.mpr (Nat.zero_le n)⟩).1
  have hf : Measurable f := (measurable_pi_apply _).fst
  have hpair : Measurable (fun t : (Π i : Finset.Iic n, F × Y) × (F × Y) =>
      (f t.1, t.2.2)) := hf.comp measurable_fst |>.prodMk measurable_snd.snd
  ext s hs
  rw [Measure.map_apply hpair hs, Measure.compProd_apply (hpair hs)]
  simp only [commonFixedKernel]
  rw [← ProbabilityTheory.compProd_map_condDistrib hH.aemeasurable hR.aemeasurable,
    Measure.compProd_apply hs, ← hν,
    lintegral_map (Kernel.measurable_kernel_prodMk_left hs) hf]
  congr 1
  funext x
  rw [Kernel.deterministic_prod_apply' hf _ _ (measurable_prodMk_left (hpair hs))]
  rfl

theorem commonFixedMeasure_pair {F : Type u} {Y : Type v}
    [MeasurableSpace F] [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    {Ω : Type w} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (H : ℕ → Ω → F) (R : ℕ → Ω → Y) (μ : Measure F) [IsProbabilityMeasure μ]
    (y0 : Y) (n : ℕ) (hH : Measurable (H n)) (hR : Measurable (R n))
    (hμ : P.map (H n) = μ) :
    (commonFixedMeasure P H R μ y0).map
      (fun path => ((path 0).1, (path (n+1)).2)) =
      P.map (fun ω => (H n ω, R n ω)) := by
  let M := commonFixedMeasure P H R μ y0
  letI : IsProbabilityMeasure M := by dsimp [M, commonFixedMeasure]; infer_instance
  let ν := M.map (Preorder.frestrictLe n)
  letI : SFinite ν := by dsimp [ν]; infer_instance
  let f : (Π i : Finset.Iic n, F × Y) → F :=
    fun x => (x ⟨0, Finset.mem_Iic.mpr (Nat.zero_le n)⟩).1
  have hf : Measurable f := (measurable_pi_apply _).fst
  have hν : ν.map f = P.map (H n) := by
    rw [hμ]
    unfold ν
    rw [Measure.map_map hf (Preorder.measurable_frestrictLe n)]
    exact commonFixedMeasure_field P H R μ y0
  have hstep := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (X := fun _ : ℕ => F × Y)
    (μ₀ := μ.map (fun x => (x,y0))) (κ := commonFixedKernel P H R) (a := n)
  have hpair := commonFixedKernel_pair_law P H R n hH hR ν hν
  have hs' : ν ⊗ₘ commonFixedKernel P H R n =
      M.map (fun x => (Preorder.frestrictLe n x, x (n + 1))) := hstep
  calc
    M.map (fun path => ((path 0).1, (path (n+1)).2)) =
        (ν ⊗ₘ commonFixedKernel P H R n).map
          (fun t => (f t.1, t.2.2)) := by
            rw [hs']
            rw [Measure.map_map
              (show Measurable (fun t : (Π i : Finset.Iic n, F × Y) × (F × Y) =>
                (f t.1, t.2.2)) from (hf.comp measurable_fst).prodMk measurable_snd.snd)
              (show Measurable (fun x : ℕ → F × Y =>
                (Preorder.frestrictLe n x, x (n+1))) from
                (Preorder.measurable_frestrictLe n).prodMk (measurable_pi_apply (n+1)))]
            rfl
    _ = P.map (fun ω => (H n ω, R n ω)) := hpair

/-- Every Borel observable of a varying field and its realization mark has the
same law after the common-field construction. -/
theorem commonFixedMeasure_observable {F : Type u} {Y : Type v} {Z : Type w}
    [MeasurableSpace F] [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
    [MeasurableSpace Z] {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (H : ℕ → Ω → F) (R : ℕ → Ω → Y) (μ : Measure F)
    [IsProbabilityMeasure μ] (y0 : Y) (n : ℕ)
    (hH : Measurable (H n)) (hR : Measurable (R n))
    (hμ : P.map (H n) = μ) (T : F × Y → Z) (hT : Measurable T) :
    (commonFixedMeasure P H R μ y0).map
      (fun path => T ((path 0).1, (path (n+1)).2)) =
      P.map (fun ω => T (H n ω, R n ω)) := by
  have hpOld : Measurable (fun ω => (H n ω, R n ω)) := hH.prodMk hR
  have hpNew : Measurable (fun path : ℕ → F × Y =>
      ((path 0).1, (path (n+1)).2)) := by fun_prop
  change Measure.map (T ∘ (fun path : ℕ → F × Y =>
    ((path 0).1, (path (n+1)).2))) (commonFixedMeasure P H R μ y0) =
    Measure.map (T ∘ (fun ω => (H n ω, R n ω))) P
  rw [← Measure.map_map hT hpNew,
    commonFixedMeasure_pair P H R μ y0 n hH hR hμ,
    Measure.map_map hT hpOld]

end SupercriticalConformalCovariance.Small
