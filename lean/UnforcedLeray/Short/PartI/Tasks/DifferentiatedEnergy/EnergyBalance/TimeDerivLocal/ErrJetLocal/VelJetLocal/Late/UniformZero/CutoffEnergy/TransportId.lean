import UnforcedLeray.Short.PartI.Sub.PartI_T08_4_1_1_1_2_2_1_3_2

/-!
# Part I, task `PartI:T08/4/1/1/1/2/2/1/3/2/4`: leaf `VelTransportIdentity`

Source of record: `the November 2 reference manuscript`, lines 273-288.
Target: `velTransportIdentity_proof : VelTransportIdentity` (`Short/PartI/Sub/PartI_T08_4_1_1_1_2_2_1_3_2.lean`).

Single-train analogue (`v' = 0`) of `Tasks/TrainCutoffEnergyProof/TransportIdentity.lean`.
With `f = |v|² = v_0² + v_1²`, `2⟨v, (v·∇)v⟩ = v_0 ∂_q f + v_1 ∂_η f`. Put
`G_1 = φ v_0 f` (differentiated in `q`) and `G_2 = φ v_1 f` (differentiated in `η`). Pointwise

`φ (v_0 ∂_q f + v_1 ∂_η f) = ∂_q G_1 + ∂_η G_2 - φ' v_1 f - φ f (∂_q v_0 + ∂_η v_1)`,

and the last term vanishes since `div v = 0`. Both `G_i` are `C¹`, `c`-periodic in `q`, and vanish
for `|η| ≥ 2R`, so `CellDerivZero` kills the first two integrals. Hence
`velCutoffTransport = -∫ φ (v_0 ∂_q f + v_1 ∂_η f) = ∫ φ' v_1 f = velTransportRhs`.

Helpers are prefixed `te`. The calculus helpers `vi_*` come from the imported model module.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane partialQ partialEta)
open UnforcedLeray.Train (Vec)

/-- `f = |v|² = v_0² + v_1²` for the velocity of a single train, as a scalar field. -/
def teF {ν c : ℝ} (tr : B0140.TrainSol ν c) (s : ℝ) : Plane → ℝ :=
  fun w => tr.v s w 0 * tr.v s w 0 + tr.v s w 1 * tr.v s w 1

/-- `G_1 = φ_R(η) v_0 f`, differentiated in `q`. -/
def teG1 {ν c : ℝ} (tr : B0140.TrainSol ν c) (R s : ℝ) : Plane → ℝ :=
  fun w => etaCutoff R w.2 * tr.v s w 0 * teF tr s w

/-- `G_2 = φ_R(η) v_1 f`, differentiated in `η`. -/
def teG2 {ν c : ℝ} (tr : B0140.TrainSol ν c) (R s : ℝ) : Plane → ℝ :=
  fun w => etaCutoff R w.2 * tr.v s w 1 * teF tr s w

/-- The `q`-derivative of a sum of differentiable functions. -/
theorem te_partialQ_add {g h : Plane → ℝ} (hg : Differentiable ℝ g) (hh : Differentiable ℝ h)
    (z : Plane) :
    partialQ (fun w => g w + h w) z = partialQ g z + partialQ h z := by
  obtain ⟨x, η⟩ := z
  have hg' : DifferentiableAt ℝ (fun y => g (y, η)) x :=
    (hg (x, η)).comp x ((differentiableAt_id).prodMk (differentiableAt_const η))
  have hh' : DifferentiableAt ℝ (fun y => h (y, η)) x :=
    (hh (x, η)).comp x ((differentiableAt_id).prodMk (differentiableAt_const η))
  show deriv (fun y => g (y, η) + h (y, η)) x = deriv (fun y => g (y, η)) x + deriv (fun y => h (y, η)) x
  exact deriv_add hg' hh'

/-- The `η`-derivative of a sum of differentiable functions. -/
theorem te_partialEta_add {g h : Plane → ℝ} (hg : Differentiable ℝ g) (hh : Differentiable ℝ h)
    (z : Plane) :
    partialEta (fun w => g w + h w) z = partialEta g z + partialEta h z := by
  obtain ⟨x, η⟩ := z
  have hg' : DifferentiableAt ℝ (fun y => g (x, y)) η :=
    (hg (x, η)).comp η ((differentiableAt_const x).prodMk differentiableAt_id)
  have hh' : DifferentiableAt ℝ (fun y => h (x, y)) η :=
    (hh (x, η)).comp η ((differentiableAt_const x).prodMk differentiableAt_id)
  show deriv (fun y => g (x, y) + h (x, y)) η = deriv (fun y => g (x, y)) η + deriv (fun y => h (x, y)) η
  exact deriv_add hg' hh'

/-- **Leaf `VelTransportIdentity`** (`velCutoffTransport = velTransportRhs` for `s ≥ 0`, `div v = 0`). -/
theorem velTransportIdentity_proof : UnforcedLeray.Short.PartI.VelTransportIdentity := by
  intro ν c hν hc tr R hR s hs
  have hR0 : 0 < R := by linarith
  -- the cutoff facts at radius `R`
  have hcutF : EtaCutoffFacts := etaCutoffFacts
  unfold EtaCutoffFacts at hcutF
  obtain ⟨_C₀, -, hcut⟩ := hcutF
  obtain ⟨hsm, -, -, hzero, hder⟩ := hcut R hR
  have hdzero : ∀ η : ℝ, 2 * R ≤ |η| → deriv (etaCutoff R) η = 0 := by
    intro η hη'
    have h := hder η
    rw [hzero η hη', Real.sqrt_zero, mul_zero] at h
    exact abs_nonpos_iff.mp h
  -- smoothness and periodicity of the velocity slice
  have hw : ContDiff ℝ ∞ (tr.v s) := (trainSliceSmooth ν c tr s hs).1
  have hwp : Cyl.IsPeriodic c (tr.v s) := tr.isTrain.periodic_v s hs
  have hdivz : ∀ z : Plane,
      partialQ (fun w => tr.v s w 0) z + partialEta (fun w => tr.v s w 1) z = 0 :=
    fun z => tr.isTrain.solenoidal s hs z
  have ha : ContDiff ℝ ∞ (fun w : Plane => tr.v s w 0) := cid_comp 0 hw
  have hb : ContDiff ℝ ∞ (fun w : Plane => tr.v s w 1) := cid_comp 1 hw
  have ha_d : Differentiable ℝ (fun w : Plane => tr.v s w 0) := ha.differentiable (by simp)
  have hb_d : Differentiable ℝ (fun w : Plane => tr.v s w 1) := hb.differentiable (by simp)
  have hF : ContDiff ℝ ∞ (teF tr s) := (ha.mul ha).add (hb.mul hb)
  have hF_d : Differentiable ℝ (teF tr s) := hF.differentiable (by simp)
  have hPsm : ContDiff ℝ ∞ (fun w : Plane => etaCutoff R w.2) := hsm.comp contDiff_snd
  have hPd : Differentiable ℝ (fun w : Plane => etaCutoff R w.2) :=
    (hsm.differentiable (by simp)).comp differentiable_snd
  have hsm1 : ContDiff ℝ 1 (etaCutoff R) := hsm.of_le (by simp)
  have hdc : Continuous (fun z : Plane => deriv (etaCutoff R) z.2) :=
    hsm1.continuous_deriv_one.comp continuous_snd
  -- the derivative formula of `f = |v|²`
  have hFq : ∀ z : Plane, partialQ (teF tr s) z =
      tr.v s z 0 * partialQ (fun w => tr.v s w 0) z + partialQ (fun w => tr.v s w 0) z * tr.v s z 0 +
        (tr.v s z 1 * partialQ (fun w => tr.v s w 1) z + partialQ (fun w => tr.v s w 1) z * tr.v s z 1) := by
    intro z
    unfold teF
    have hm1 : Differentiable ℝ (fun w : Plane => tr.v s w 0 * tr.v s w 0) := ha_d.mul ha_d
    have hm2 : Differentiable ℝ (fun w : Plane => tr.v s w 1 * tr.v s w 1) := hb_d.mul hb_d
    rw [te_partialQ_add hm1 hm2 z, vi_partialQ_mul ha_d ha_d z,
      vi_partialQ_mul hb_d hb_d z]
  have hFe : ∀ z : Plane, partialEta (teF tr s) z =
      tr.v s z 0 * partialEta (fun w => tr.v s w 0) z + partialEta (fun w => tr.v s w 0) z * tr.v s z 0 +
        (tr.v s z 1 * partialEta (fun w => tr.v s w 1) z + partialEta (fun w => tr.v s w 1) z * tr.v s z 1) := by
    intro z
    unfold teF
    have hm1 : Differentiable ℝ (fun w : Plane => tr.v s w 0 * tr.v s w 0) := ha_d.mul ha_d
    have hm2 : Differentiable ℝ (fun w : Plane => tr.v s w 1 * tr.v s w 1) := hb_d.mul hb_d
    rw [te_partialEta_add hm1 hm2 z, vi_partialEta_mul ha_d ha_d z,
      vi_partialEta_mul hb_d hb_d z]
  -- the transport term as a half combination of the `f`-derivatives
  have hinner : ∀ z : Plane,
      inner ℝ (tr.v s z) (bilinAdv (tr.v s) (tr.v s) z) =
        (1 / 2 : ℝ) * (tr.v s z 0 * partialQ (teF tr s) z + tr.v s z 1 * partialEta (teF tr s) z) := by
    intro z
    rw [hFq z, hFe z]
    simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial, bilinAdv,
      Train.toVec_zero, Train.toVec_one]
    ring
  -- norm of the velocity
  have hnorm : ∀ z : Plane, ‖tr.v s z‖ ^ 2 = teF tr s z := by
    intro z
    unfold teF
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    ring
  -- the two components of the integration by parts
  have hPer1 : Cyl.IsPeriodic c (teG1 tr R s) := by
    intro z
    simp only [teG1, teF, hwp z]
  have hPer2 : Cyl.IsPeriodic c (teG2 tr R s) := by
    intro z
    simp only [teG2, teF, hwp z]
  have hG1 : ContDiff ℝ 1 (teG1 tr R s) := ((hPsm.mul ha).mul hF).of_le (by simp)
  have hG2 : ContDiff ℝ 1 (teG2 tr R s) := ((hPsm.mul hb).mul hF).of_le (by simp)
  have hz1 : ∀ z : Plane, 2 * R ≤ |z.2| → teG1 tr R s z = 0 := by
    intro z hz
    simp only [teG1, hzero z.2 hz, zero_mul]
  have hz2 : ∀ z : Plane, 2 * R ≤ |z.2| → teG2 tr R s z = 0 := by
    intro z hz
    simp only [teG2, hzero z.2 hz, zero_mul]
  have hZ := cellDerivZero_of_periodic
  have hZ1 : ∫ z in Cyl.cell c, partialQ (teG1 tr R s) z = 0 :=
    (hZ c R hc hR0 (teG1 tr R s) hG1 hPer1 hz1).1
  have hZ2 : ∫ z in Cyl.cell c, partialEta (teG2 tr R s) z = 0 :=
    (hZ c R hc hR0 (teG2 tr R s) hG2 hPer2 hz2).2
  -- the derivatives of `G_1` and `G_2`
  have pQG1 : ∀ z : Plane, partialQ (teG1 tr R s) z =
      (etaCutoff R z.2 * tr.v s z 0) * partialQ (teF tr s) z +
        (etaCutoff R z.2 * partialQ (fun w => tr.v s w 0) z) * teF tr s z := by
    intro z
    unfold teG1
    have h1 := vi_partialQ_mul (f := fun w : Plane => etaCutoff R w.2 * tr.v s w 0)
      (g := teF tr s) (hPd.mul ha_d) hF_d z
    have h2 := vi_partialQ_mul (f := fun w : Plane => etaCutoff R w.2)
      (g := fun w : Plane => tr.v s w 0) hPd ha_d z
    rw [vi_partialQ_cutoff] at h2
    rw [h1, h2]
    ring
  have pEG2 : ∀ z : Plane, partialEta (teG2 tr R s) z =
      (etaCutoff R z.2 * tr.v s z 1) * partialEta (teF tr s) z +
        (etaCutoff R z.2 * partialEta (fun w => tr.v s w 1) z +
          deriv (etaCutoff R) z.2 * tr.v s z 1) * teF tr s z := by
    intro z
    unfold teG2
    have h1 := vi_partialEta_mul (f := fun w : Plane => etaCutoff R w.2 * tr.v s w 1)
      (g := teF tr s) (hPd.mul hb_d) hF_d z
    have h2 := vi_partialEta_mul (f := fun w : Plane => etaCutoff R w.2)
      (g := fun w : Plane => tr.v s w 1) hPd hb_d z
    rw [vi_partialEta_cutoff] at h2
    rw [h1, h2]
  -- the pointwise identity
  have hkey : ∀ z : Plane,
      etaCutoff R z.2 * inner ℝ (tr.v s z) (bilinAdv (tr.v s) (tr.v s) z) =
        (1 / 2 : ℝ) * (partialQ (teG1 tr R s) z + partialEta (teG2 tr R s) z -
          deriv (etaCutoff R) z.2 * (tr.v s z 1 * teF tr s z)) := by
    intro z
    rw [hinner z, pQG1 z, pEG2 z]
    linear_combination (-(1 / 2 : ℝ) * (etaCutoff R z.2 * teF tr s z)) * hdivz z
  -- integrability of the three pieces
  have hcY1 : Continuous (partialQ (teG1 tr R s)) := (Cyl.C1_partial_of_contDiff hG1).1
  have hcY2 : Continuous (partialEta (teG2 tr R s)) := (Cyl.C1_partial_of_contDiff hG2).2
  have hY1 : IntegrableOn (partialQ (teG1 tr R s)) (Cyl.cell c) := by
    refine cellIntegrable_of_support c R hc hR0 _ hcY1 (fun z hz => ?_)
    rw [pQG1 z, hzero z.2 hz]
    ring
  have hY2 : IntegrableOn (partialEta (teG2 tr R s)) (Cyl.cell c) := by
    refine cellIntegrable_of_support c R hc hR0 _ hcY2 (fun z hz => ?_)
    rw [pEG2 z, hzero z.2 hz, hdzero z.2 hz]
    ring
  have hcomp1 : Continuous (fun z : Plane => tr.v s z 1) := hb.continuous
  have hDd_c : Continuous (fun z : Plane =>
      deriv (etaCutoff R) z.2 * (tr.v s z 1 * teF tr s z)) :=
    hdc.mul (hcomp1.mul hF.continuous)
  have hDd : IntegrableOn (fun z : Plane =>
      deriv (etaCutoff R) z.2 * (tr.v s z 1 * teF tr s z)) (Cyl.cell c) := by
    refine cellIntegrable_of_support c R hc hR0 _ hDd_c (fun z hz => ?_)
    rw [hdzero z.2 hz, zero_mul]
  -- assemble
  unfold velCutoffTransport velTransportRhs
  have e1 : (∫ z in Cyl.cell c, etaCutoff R z.2 *
        inner ℝ (tr.v s z) (bilinAdv (tr.v s) (tr.v s) z)) =
      (1 / 2 : ℝ) * ∫ z in Cyl.cell c, (partialQ (teG1 tr R s) z + partialEta (teG2 tr R s) z -
          deriv (etaCutoff R) z.2 * (tr.v s z 1 * teF tr s z)) := by
    rw [← integral_const_mul]
    congr 1
    funext z
    exact hkey z
  have e2 : (∫ z in Cyl.cell c, (partialQ (teG1 tr R s) z + partialEta (teG2 tr R s) z -
          deriv (etaCutoff R) z.2 * (tr.v s z 1 * teF tr s z))) =
      (∫ z in Cyl.cell c, partialQ (teG1 tr R s) z) +
        (∫ z in Cyl.cell c, partialEta (teG2 tr R s) z) -
        ∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 * (tr.v s z 1 * teF tr s z) := by
    have hYs : Integrable (fun z : Plane => partialQ (teG1 tr R s) z + partialEta (teG2 tr R s) z)
        (volume.restrict (Cyl.cell c)) := hY1.add hY2
    rw [integral_sub hYs hDd, integral_add hY1 hY2]
  have e3 : (∫ z in Cyl.cell c, ‖tr.v s z‖ ^ 2 * tr.v s z 1 * deriv (etaCutoff R) z.2) =
      ∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 * (tr.v s z 1 * teF tr s z) := by
    congr 1
    funext z
    rw [hnorm z]
    ring
  rw [e1, e2, hZ1, hZ2, e3]
  ring

end UnforcedLeray.Short.PartI
