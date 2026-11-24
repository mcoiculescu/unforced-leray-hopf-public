import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1_2.Statements
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_8_2_1_2.NewtonConvFarDeriv
import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedProjectedNewtonComponent
import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedProjectedNewtonCurlPotential
import UnforcedLeray.Cons.L2.BackgroundConcrete.SelectedProjectedPotentialSourceCellL1

/-!
# `PartIII-b:C/ward/12/3/1/2/8/2/1/2/3` (`NewtonVectorPotentialFarDeriv`)

Uniform far-field derivative bound for the vector Newton potential `A = projectedTestNewtonVectorPotential φ`.
Components are scalar Newton potentials of spatial tests (`newtonConvFarDeriv`), the slice L¹ norms are
uniform in `τ` (periodicity), and the common support radius is `max R 0` from `bounded_support`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.SolApprox

open UnforcedLeray.PhaseSpace UnforcedLeray.Cons.C03.Concrete UnforcedLeray.RieszLp
open UnforcedLeray.B0411 UnforcedLeray.B0412

theorem newtonVectorPotentialFarDeriv :
    UnforcedLeray.Short.PartIIIb.Concrete.SolApprox.NewtonVectorPotentialFarDeriv := by
  intro P _ φ hφ
  have hP : 0 < P := Fact.out
  obtain ⟨R, hR⟩ := hφ.bounded_support
  -- uniform L¹ bounds on each component slice, for all τ (periodicity)
  have hL : ∀ i : Fin 3, ∃ L : ℝ, 0 ≤ L ∧ ∀ τ : ℝ, ∫ y, |φ (τ, y) i| ≤ L := by
    intro i
    obtain ⟨C, hC0, hC⟩ := exists_uniform_spatialL1_of_isPhaseTest
      (hφ.clm_comp (EuclideanSpace.proj i : Space →L[ℝ] ℝ))
    refine ⟨C, hC0, fun τ => ?_⟩
    have hper : Function.Periodic (fun t : ℝ => fun y : Space => φ (t, y) i) P := fun t => by
      funext y
      show φ (t + P, y) i = φ (t, y) i
      rw [hφ.periodic t y]
    obtain ⟨τ', hτ', hτeq⟩ := hper.exists_mem_Ico₀ hP τ
    have h2 : ∀ y : Space, φ (τ, y) i = φ (τ', y) i := fun y => congrFun hτeq y
    have h3 : (fun y : Space => |φ (τ, y) i|) = fun y => |φ (τ', y) i| :=
      funext fun y => by rw [h2 y]
    rw [h3]
    exact hC τ' (Ico_subset_Icc_self hτ')
  choose Li hLi0 hLi using hL
  set Lsum : ℝ := ∑ i : Fin 3, Li i with hLsum_def
  have hLsum : ∀ i : Fin 3, Li i ≤ Lsum := fun i =>
    Finset.single_le_sum (f := Li) (fun j _ => hLi0 j) (Finset.mem_univ i)
  have hLsum0 : 0 ≤ Lsum := Finset.sum_nonneg fun j _ => hLi0 j
  -- scalar Newton constants for k ≤ 4
  have hNC := newtonConvFarDeriv
  unfold NewtonConvFarDeriv at hNC
  choose Ck hCk0 hCk using hNC
  set Cmax : ℝ := ∑ j ∈ Finset.range 5, Ck j with hCmax_def
  have hCmax : ∀ k : ℕ, k ≤ 4 → Ck k ≤ Cmax := fun k hk =>
    Finset.single_le_sum (f := Ck) (fun j _ => hCk0 j) (Finset.mem_range.2 (by omega))
  have hCmax0 : 0 ≤ Cmax := Finset.sum_nonneg fun j _ => hCk0 j
  -- coordinate embeddings ℝ → ℝ³
  set L : Fin 3 → (ℝ →L[ℝ] Space) := fun i =>
    ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (coordinateVector i) with hL_def
  set K : ℝ := ∑ i : Fin 3, ‖L i‖ with hK_def
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun i _ => norm_nonneg _
  have hexp : ∀ v : Space, v = ∑ i : Fin 3, (v i) • coordinateVector i := by
    intro v
    ext j
    simp [sum_smul_coordinateVector_apply]
  refine ⟨2 * max R 0 + 1, K * (Cmax * Lsum), ?_, ?_, ?_⟩
  · have := le_max_right R 0
    linarith
  · exact mul_nonneg hK0 (mul_nonneg hCmax0 hLsum0)
  intro τ y hy k hk
  have hN : ContDiff ℝ ∞ (fun x : Space => projectedTestNewtonVectorPotential φ (τ, x)) :=
    (contDiff_projectedTestNewtonVectorPotential hφ).comp
      (ContDiff.prodMk contDiff_const contDiff_id)
  have hF : ∀ i : Fin 3, ContDiff ℝ ∞
      (fun x : Space => L i (projectedTestNewtonVectorPotential φ (τ, x) i)) := by
    intro i
    exact (L i).contDiff.comp ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.comp hN)
  have hsum : (fun x : Space => projectedTestNewtonVectorPotential φ (τ, x)) =
      ∑ i : Fin 3, (fun x : Space => L i (projectedTestNewtonVectorPotential φ (τ, x) i)) := by
    funext x
    rw [Finset.sum_apply]
    simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, one_smul]
    exact hexp _
  have hfi : ∀ i : Fin 3, IsSpatialTest (fun x : Space => φ (τ, x) i) := by
    intro i
    have hτs : ContDiff ℝ ∞ (fun x : Space => ((τ, x) : ℝ × Space)) :=
      ContDiff.prodMk contDiff_const contDiff_id
    have hφs : ContDiff ℝ ∞ (fun x : Space => φ (τ, x)) := hφ.smooth.comp hτs
    refine ⟨?_, ?_⟩
    · exact (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.comp hφs
    · exact HasCompactSupport.comp_left (g := fun v : Space => v i)
        (hφ.hasCompactSupport_slice τ) (by simp)
  have hcomp : ∀ i : Fin 3, (fun x : Space => projectedTestNewtonVectorPotential φ (τ, x) i) =
      newtonConv (fun x : Space => φ (τ, x) i) := fun i =>
    funext fun x => projectedTestNewtonVectorPotential_component hφ τ x i
  have hzero : ∀ i : Fin 3, ∀ x : Space, max R 0 < ‖x‖ →
      (fun x : Space => φ (τ, x) i) x = 0 := by
    intro i x hx
    have h0 : φ (τ, x) = 0 := hR τ x (lt_of_le_of_lt (le_max_left _ _) hx)
    simp [h0]
  have hbound : ∀ i : Fin 3,
      ‖iteratedFDeriv ℝ k (fun x : Space => projectedTestNewtonVectorPotential φ (τ, x) i) y‖ ≤
        Cmax * Lsum * ‖y‖ ^ (-((k : ℝ) + 1)) := by
    intro i
    rw [hcomp i]
    have h1 := hCk k (fun x : Space => φ (τ, x) i) (max R 0) (hfi i) (le_max_right _ _)
      (hzero i) y hy
    have hp : 0 ≤ ‖y‖ ^ (-((k : ℝ) + 1)) := Real.rpow_nonneg (norm_nonneg _) _
    have hIn : 0 ≤ ∫ x, |φ (τ, x) i| := integral_nonneg fun x => abs_nonneg _
    have h1' : ‖iteratedFDeriv ℝ k (newtonConv (fun x : Space => φ (τ, x) i)) y‖ ≤
        Ck k * (∫ x, |φ (τ, x) i|) * ‖y‖ ^ (-((k : ℝ) + 1)) := h1
    refine h1'.trans ?_
    apply mul_le_mul_of_nonneg_right _ hp
    exact mul_le_mul (hCmax k hk) ((hLi i τ).trans (hLsum i)) hIn hCmax0
  have hpt : ∀ i : Fin 3,
      ‖iteratedFDeriv ℝ k (fun x : Space => L i (projectedTestNewtonVectorPotential φ (τ, x) i)) y‖ ≤
        ‖L i‖ * (Cmax * Lsum * ‖y‖ ^ (-((k : ℝ) + 1))) := by
    intro i
    have hgs : ContDiff ℝ ∞ (fun x : Space => projectedTestNewtonVectorPotential φ (τ, x) i) :=
      (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.comp hN
    have h := ContinuousLinearMap.norm_iteratedFDeriv_comp_left (L i)
      (f := fun x : Space => projectedTestNewtonVectorPotential φ (τ, x) i) (x := y) (n := k)
      hgs.contDiffAt (by simp)
    exact h.trans (mul_le_mul_of_nonneg_left (hbound i) (norm_nonneg _))
  rw [hsum, iteratedFDeriv_sum_apply (fun i _ => ((hF i).of_le (by simp)).contDiffAt)]
  calc ‖∑ i : Fin 3, iteratedFDeriv ℝ k
          (fun x : Space => L i (projectedTestNewtonVectorPotential φ (τ, x) i)) y‖
      ≤ ∑ i : Fin 3, ‖iteratedFDeriv ℝ k
          (fun x : Space => L i (projectedTestNewtonVectorPotential φ (τ, x) i)) y‖ :=
        norm_sum_le _ _
    _ ≤ ∑ i : Fin 3, ‖L i‖ * (Cmax * Lsum * ‖y‖ ^ (-((k : ℝ) + 1))) :=
        Finset.sum_le_sum fun i _ => hpt i
    _ = K * (Cmax * Lsum) * ‖y‖ ^ (-((k : ℝ) + 1)) := by
        rw [← Finset.sum_mul, hK_def]
        ring

end UnforcedLeray.Short.PartIIIb.Concrete.SolApprox
