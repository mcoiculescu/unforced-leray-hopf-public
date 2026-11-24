import UnforcedLeray.Short.PartI.Sub.PartI_T08_4_1_1_1_2_2_1_3_2

/-!
# Part I, task `PartI:T08/4/1/1/1/2/2/1/3/2/1`: leaf `VelIntegrandDecomp`

Source of record: `the November 2 reference manuscript`, lines 273-288.
Target: `velIntegrandDecomp_proof : VelIntegrandDecomp` (`Short/PartI/Sub/PartI_T08_4_1_1_1_2_2_1_3_2.lean`).

Single-train analogue (`v' = 0`) of `Tasks/TrainCutoffEnergyProof/IntegrandDecomp.lean`.
For `s > 0` the momentum residual of the train vanishes, which gives pointwise
`∂_s v = -(v·∇)v + νΔv - ∇p`. Multiplying `2⟨v, ∂_s v⟩` by `φ_R` and integrating over the cell
splits the integral into three terms. Each integrand is continuous and vanishes for `|η| ≥ 2R`,
hence is integrable on the cell by `CellIntegrableOfSupport`.

The calculus helpers `cid_*`, `cid_bilin_cont`, `cid_vecLap_cont`, `cid_gradS_cont`,
`cid_etaCutoff_cont`, `cid_etaCutoff_eq_zero` come from the imported model module. The slice
smoothness is `trainSliceSmooth`. The helpers defined here are prefixed `vd`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec)

/-- The transport integrand `φ_R(η) ⟨v, (v·∇)v⟩` of a single train. -/
def vdA {ν c : ℝ} (tr : B0140.TrainSol ν c) (R s : ℝ) (z : Plane) : ℝ :=
  etaCutoff R z.2 * inner ℝ (tr.v s z) (bilinAdv (tr.v s) (tr.v s) z)

/-- The viscous integrand `φ_R(η) ⟨v, Δv⟩` of a single train. -/
def vdL {ν c : ℝ} (tr : B0140.TrainSol ν c) (R s : ℝ) (z : Plane) : ℝ :=
  etaCutoff R z.2 * inner ℝ (tr.v s z) (Train.vecLaplacian (tr.v s) z)

/-- The pressure integrand `φ_R(η) ⟨v, ∇p⟩` of a single train. -/
def vdGtr {ν c : ℝ} (tr : B0140.TrainSol ν c) (R s : ℝ) (z : Plane) : ℝ :=
  etaCutoff R z.2 * inner ℝ (tr.v s z) (Train.gradS (tr.p s) z)

/-- **Leaf `VelIntegrandDecomp`** (source lines 276-288). -/
theorem velIntegrandDecomp_proof : UnforcedLeray.Short.PartI.VelIntegrandDecomp := by
  intro ν c hν hc tr R hR s hs
  have hRpos : 0 < R := by linarith
  have hs0 : 0 ≤ s := hs.le
  obtain ⟨hv, hp⟩ := trainSliceSmooth ν c tr s hs0
  -- differentiability of a train in the age variable at `s > 0`
  have hdt : ∀ z : Plane, DifferentiableAt ℝ (fun t => tr.v t z) s := by
    intro z
    have h1 : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => tr.v x.1 x.2)
        (Ici (0 : ℝ) ×ˢ (univ : Set Plane)) := tr.isTrain.smooth_v
    have h2 : (Ici (0 : ℝ) ×ˢ (univ : Set Plane)) ∈ 𝓝 (s, z) :=
      prod_mem_nhds (Ici_mem_nhds hs) univ_mem
    have h3 : DifferentiableAt ℝ (fun x : ℝ × Plane => tr.v x.1 x.2) (s, z) :=
      (h1.differentiableOn (by norm_num)).differentiableAt h2
    have hline : DifferentiableAt ℝ (fun t : ℝ => ((t, z) : ℝ × Plane)) s :=
      (differentiableAt_id).prodMk (differentiableAt_const z)
    exact h3.comp s hline
  -- the pointwise equation for `v`
  have hpt : ∀ z : Plane, deriv (fun t => tr.v t z) s =
      -(bilinAdv (tr.v s) (tr.v s) z) + ν • Train.vecLaplacian (tr.v s) z -
        Train.gradS (tr.p s) z := by
    intro z
    have M := tr.isTrain.momentum s hs z
    unfold Train.momentumResidual at M
    have hadv : Train.advection (tr.v s) z = bilinAdv (tr.v s) (tr.v s) z := rfl
    rw [hadv] at M
    linear_combination (norm := module) M
  -- continuity of the three integrands
  have hcφ : Continuous (fun z : Plane => etaCutoff R z.2) := cid_etaCutoff_cont R
  have hvc : Continuous (tr.v s) := hv.continuous
  have hcA : Continuous (vdA tr R s) := hcφ.mul (hvc.inner (cid_bilin_cont hv hv))
  have hcL : Continuous (vdL tr R s) := hcφ.mul (hvc.inner (cid_vecLap_cont hv))
  have hcG : Continuous (vdGtr tr R s) := hcφ.mul (hvc.inner (cid_gradS_cont hp))
  -- support: the cutoff vanishes for `|η| ≥ 2R`
  have hsupp : ∀ z : Plane, 2 * R ≤ |z.2| → etaCutoff R z.2 = 0 :=
    fun z hz => cid_etaCutoff_eq_zero hRpos hz
  have iA : IntegrableOn (vdA tr R s) (Cyl.cell c) :=
    cellIntegrable_of_support c R hc hRpos _ hcA
      (fun z hz => by simp only [vdA, hsupp z hz, zero_mul])
  have iL : IntegrableOn (vdL tr R s) (Cyl.cell c) :=
    cellIntegrable_of_support c R hc hRpos _ hcL
      (fun z hz => by simp only [vdL, hsupp z hz, zero_mul])
  have iG : IntegrableOn (vdGtr tr R s) (Cyl.cell c) :=
    cellIntegrable_of_support c R hc hRpos _ hcG
      (fun z hz => by simp only [vdGtr, hsupp z hz, zero_mul])
  have jA : Integrable (fun z => (-2 : ℝ) * vdA tr R s z) (volume.restrict (Cyl.cell c)) :=
    iA.const_mul (-2)
  have jL : Integrable (fun z => (2 * ν) * vdL tr R s z) (volume.restrict (Cyl.cell c)) :=
    iL.const_mul (2 * ν)
  have jG : Integrable (fun z => (-2 : ℝ) * vdGtr tr R s z) (volume.restrict (Cyl.cell c)) :=
    iG.const_mul (-2)
  -- the integrand splits pointwise
  have hsplit : (∫ z in Cyl.cell c, etaCutoff R z.2 *
        (2 * inner ℝ (tr.v s z) (deriv (fun t => tr.v t z) s))) =
      ∫ z in Cyl.cell c, ((-2 : ℝ) * vdA tr R s z + (2 * ν) * vdL tr R s z +
        (-2 : ℝ) * vdGtr tr R s z) := by
    congr 1
    funext z
    rw [hpt z]
    simp only [vdA, vdL, vdGtr, inner_add_right, inner_sub_right, inner_neg_right,
      real_inner_smul_right]
    ring
  have k1 : Integrable (fun z => (-2 : ℝ) * vdA tr R s z + (2 * ν) * vdL tr R s z)
      (volume.restrict (Cyl.cell c)) := jA.add jL
  have e1 : (∫ z in Cyl.cell c, ((-2 : ℝ) * vdA tr R s z + (2 * ν) * vdL tr R s z +
        (-2 : ℝ) * vdGtr tr R s z)) =
      (∫ z in Cyl.cell c, ((-2 : ℝ) * vdA tr R s z + (2 * ν) * vdL tr R s z)) +
        ∫ z in Cyl.cell c, (-2 : ℝ) * vdGtr tr R s z :=
    integral_add k1 jG
  have e0 : (∫ z in Cyl.cell c, ((-2 : ℝ) * vdA tr R s z + (2 * ν) * vdL tr R s z)) =
      (∫ z in Cyl.cell c, (-2 : ℝ) * vdA tr R s z) +
        ∫ z in Cyl.cell c, (2 * ν) * vdL tr R s z :=
    integral_add jA jL
  rw [hsplit, e1, e0]
  simp only [integral_const_mul, vdA, vdL, vdGtr]
  unfold velCutoffViscous velCutoffTransport velCutoffPressure
  ring

end UnforcedLeray.Short.PartI
