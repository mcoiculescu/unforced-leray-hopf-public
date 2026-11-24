import UnforcedLeray.Short.PartI.Sub.PartI_T04_9_1_2_2_2
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APEnstrophy.HasDeriv
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel2.CutIneqDiff.IBP.FrozenAlg.Helpers

/-!
# Part I, `APL2FrozenTransport`: transport integration by parts (source lines 285-288)

For `g = apL2G w = (∂_qω)² + (∂_ηω)²`, `χ = etaCutoff R` and a `c`-periodic divergence-free `w`,
`∫ χ(-(w_0 ∂_q g + w_1 ∂_η g)) = ∫ χ' w_1 g`.  Integrate by parts in `q` (periodicity) and in `η`
(compact support of `χ`), use `∂_q χ = 0`, then `div w = 0`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Short.PartI.FA

/-- **`PartI:T04/9/1/2/2/2/3`**: the transport integration by parts (`APL2FrozenTransport`,
source lines 285-288). -/
theorem aPL2FrozenTransport : UnforcedLeray.Short.PartI.APL2FrozenTransport := by
  intro c R w hc hR hw hper hdiv
  have hc0 : 0 < c := by linarith
  have hR0 : 0 < R := by linarith
  have hwd : Differentiable ℝ w := hw.differentiable (by simp)
  have hωc : ContDiff ℝ ∞ (Cyl.curl w) := curl_contDiff hw
  have hgC : ContDiff ℝ ∞ (apL2G w) :=
    ((Cyl.contDiff_partialQ hωc).pow 2).add ((Cyl.contDiff_partialEta hωc).pow 2)
  have hgd : Differentiable ℝ (apL2G w) := hgC.differentiable (by simp)
  have hgc : Continuous (apL2G w) := hgC.continuous
  have hPgc : Continuous (fun z : Plane => Cyl.partialQ (apL2G w) z) :=
    (Cyl.contDiff_partialQ (n := ∞) hgC).continuous
  have hEgc : Continuous (fun z : Plane => Cyl.partialEta (apL2G w) z) :=
    (Cyl.contDiff_partialEta (n := ∞) hgC).continuous
  -- periodicity
  have hw0p : Cyl.IsPeriodic c (fun y => w y 0) := hper.fun_comp (fun x : Vec => x 0)
  have hw1p : Cyl.IsPeriodic c (fun y => w y 1) := hper.fun_comp (fun x : Vec => x 1)
  have hωp : Cyl.IsPeriodic c (Cyl.curl w) := fun z => by
    show Cyl.partialQ (fun y => w y 1) (z.1 + c, z.2) - Cyl.partialEta (fun y => w y 0) (z.1 + c, z.2)
      = Cyl.partialQ (fun y => w y 1) z - Cyl.partialEta (fun y => w y 0) z
    rw [hw1p.partialQ z, hw0p.partialEta z]
  have hgp : Cyl.IsPeriodic c (apL2G w) := fun z => by
    unfold apL2G
    rw [hωp.partialQ z, hωp.partialEta z]
  -- the cutoff and its products with the components of `w`
  have hφ1 : ContDiff ℝ ∞ (fun z : Plane => etaCutoff R z.2) :=
    (ecContDiff R hR0).comp contDiff_snd
  have hφd : Differentiable ℝ (fun z : Plane => etaCutoff R z.2) := hφ1.differentiable (by simp)
  have hφc : Continuous (fun z : Plane => etaCutoff R z.2) := hφ1.continuous
  have hφ'c : Continuous (fun z : Plane => deriv (etaCutoff R) z.2) :=
    ((ecContDiff R hR0).continuous_deriv (by norm_num)).comp continuous_snd
  have hφv : ∀ x : ℝ, 2 * R < |x| → etaCutoff R x = 0 := fun x hx => apHD_eta_zero hR0 hx.le
  have hu0 : ContDiff ℝ ∞ (fun y => w y 0) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).contDiff.comp hw
  have hu1 : ContDiff ℝ ∞ (fun y => w y 1) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).contDiff.comp hw
  have hu0d : Differentiable ℝ (fun y => w y 0) := hu0.differentiable (by simp)
  have hu1d : Differentiable ℝ (fun y => w y 1) := hu1.differentiable (by simp)
  have hu1c : Continuous (fun y : Plane => w y 1) := hu1.continuous
  have hu0c : Continuous (fun y : Plane => w y 0) := hu0.continuous
  have hψ0 : ContDiff ℝ ∞ (fun z : Plane => etaCutoff R z.2 * w z 0) := hφ1.mul hu0
  have hψ1 : ContDiff ℝ ∞ (fun z : Plane => etaCutoff R z.2 * w z 1) := hφ1.mul hu1
  have hψ0d : Differentiable ℝ (fun z : Plane => etaCutoff R z.2 * w z 0) := hψ0.differentiable (by simp)
  have hψ1d : Differentiable ℝ (fun z : Plane => etaCutoff R z.2 * w z 1) := hψ1.differentiable (by simp)
  have hψ0p : Cyl.IsPeriodic c (fun z : Plane => etaCutoff R z.2 * w z 0) := fun z => by
    show etaCutoff R z.2 * w (z.1 + c, z.2) 0 = etaCutoff R z.2 * w z 0
    rw [hper z]
  have hψ1p : Cyl.IsPeriodic c (fun z : Plane => etaCutoff R z.2 * w z 1) := fun z => by
    show etaCutoff R z.2 * w (z.1 + c, z.2) 1 = etaCutoff R z.2 * w z 1
    rw [hper z]
  -- partial derivatives of the cutoff times components
  have hpq0 : ∀ z : Plane, Cyl.partialQ (fun z : Plane => etaCutoff R z.2 * w z 0) z
      = etaCutoff R z.2 * Cyl.partialQ (fun y => w y 0) z := by
    intro z
    rw [apHD_pq_mul _ _ hφd hu0d z]
    simp [apHD_pq_const]
  have hpe1 : ∀ z : Plane, Cyl.partialEta (fun z : Plane => etaCutoff R z.2 * w z 1) z
      = deriv (etaCutoff R) z.2 * w z 1 + etaCutoff R z.2 * Cyl.partialEta (fun y => w y 1) z := by
    intro z
    exact (apHD_pe_mul _ _ hφd hu1d z).trans rfl
  -- integrability
  have hPgcont : Continuous (fun z : Plane => Cyl.partialQ (apL2G w) z) := hPgc
  have h1 : IntegrableOn (fun z : Plane => Cyl.partialQ (apL2G w) z
      * (etaCutoff R z.2 * w z 0)) (Cyl.cell c) :=
    apHD_integ (c := c) (R0 := 2 * R) (hPgc.mul (hφc.mul hu0c))
      (fun z hz => by simp [apHD_eta_zero hR0 hz.le])
  have h2 : IntegrableOn (fun z : Plane => apL2G w z
      * Cyl.partialQ (fun z : Plane => etaCutoff R z.2 * w z 0) z) (Cyl.cell c) :=
    apHD_integ (c := c) (R0 := 2 * R)
      (hgc.mul (Continuous.comp (Cyl.contDiff_partialQ (n := ∞) hψ0).continuous continuous_id))
      (fun z hz => by simp [hpq0 z, apHD_eta_zero hR0 hz.le])
  have h0' : IntegrableOn (fun z : Plane => apL2G w z * (etaCutoff R z.2 * w z 1)) (Cyl.cell c) :=
    apHD_integ (c := c) (R0 := 2 * R) (hgc.mul (hφc.mul hu1c))
      (fun z hz => by simp [apHD_eta_zero hR0 hz.le])
  have h1' : IntegrableOn (fun z : Plane => Cyl.partialEta (apL2G w) z
      * (etaCutoff R z.2 * w z 1)) (Cyl.cell c) :=
    apHD_integ (c := c) (R0 := 2 * R) (hEgc.mul (hφc.mul hu1c))
      (fun z hz => by simp [apHD_eta_zero hR0 hz.le])
  have h2' : IntegrableOn (fun z : Plane => apL2G w z
      * Cyl.partialEta (fun z : Plane => etaCutoff R z.2 * w z 1) z) (Cyl.cell c) :=
    apHD_integ (c := c) (R0 := 2 * R)
      (hgc.mul (Continuous.comp (Cyl.contDiff_partialEta (n := ∞) hψ1).continuous continuous_id))
      (fun z hz => by simp [hpe1 z, apHD_deriv_zero hφv hz, apHD_eta_zero hR0 hz.le])
  -- integration by parts in `q` and in `η`
  have hq1 : ∫ z in Cyl.cell c, Cyl.partialQ (apL2G w) z * (etaCutoff R z.2 * w z 0)
      = -∫ z in Cyl.cell c, apL2G w z
          * Cyl.partialQ (fun z : Plane => etaCutoff R z.2 * w z 0) z :=
    Cyl.integral_cell_partialQ_mul hc0 hgd hψ0d hgp hψ0p h1 h2
  have he1 : ∫ z in Cyl.cell c, Cyl.partialEta (apL2G w) z * (etaCutoff R z.2 * w z 1)
      = -∫ z in Cyl.cell c, apL2G w z
          * Cyl.partialEta (fun z : Plane => etaCutoff R z.2 * w z 1) z :=
    Cyl.integral_cell_partialEta_mul hgd hψ1d h0' h1' h2'
  -- the divergence-free condition
  have hdz : ∀ z : Plane, Cyl.partialQ (fun y => w y 0) z
      + Cyl.partialEta (fun y => w y 1) z = 0 := fun z => hdiv z
  -- assembly
  have E0 : (∫ z in Cyl.cell c, etaCutoff R z.2 * (-(w z 0 * Cyl.partialQ (apL2G w) z
        + w z 1 * Cyl.partialEta (apL2G w) z)))
      = ∫ z in Cyl.cell c, (-(Cyl.partialQ (apL2G w) z * (etaCutoff R z.2 * w z 0))
          + -(Cyl.partialEta (apL2G w) z * (etaCutoff R z.2 * w z 1))) :=
    integral_congr_ae (ae_of_all _ fun z => by ring)
  have E1 : ∫ z in Cyl.cell c, (-(Cyl.partialQ (apL2G w) z * (etaCutoff R z.2 * w z 0))
          + -(Cyl.partialEta (apL2G w) z * (etaCutoff R z.2 * w z 1)))
      = (∫ z in Cyl.cell c, -(Cyl.partialQ (apL2G w) z * (etaCutoff R z.2 * w z 0)))
          + ∫ z in Cyl.cell c, -(Cyl.partialEta (apL2G w) z * (etaCutoff R z.2 * w z 1)) :=
    integral_add (Integrable.neg h1) (Integrable.neg h1')
  have E2a : ∫ z in Cyl.cell c, -(Cyl.partialQ (apL2G w) z * (etaCutoff R z.2 * w z 0))
      = -∫ z in Cyl.cell c, Cyl.partialQ (apL2G w) z * (etaCutoff R z.2 * w z 0) :=
    integral_neg _
  have E2b : ∫ z in Cyl.cell c, -(Cyl.partialEta (apL2G w) z * (etaCutoff R z.2 * w z 1))
      = -∫ z in Cyl.cell c, Cyl.partialEta (apL2G w) z * (etaCutoff R z.2 * w z 1) :=
    integral_neg _
  have E4a : (∫ z in Cyl.cell c, apL2G w z * Cyl.partialQ (fun z : Plane => etaCutoff R z.2 * w z 0) z)
      + ∫ z in Cyl.cell c, apL2G w z * Cyl.partialEta (fun z : Plane => etaCutoff R z.2 * w z 1) z
      = ∫ z in Cyl.cell c, (apL2G w z * Cyl.partialQ (fun z : Plane => etaCutoff R z.2 * w z 0) z
          + apL2G w z * Cyl.partialEta (fun z : Plane => etaCutoff R z.2 * w z 1) z) :=
    (integral_add h2 h2').symm
  have E4b : ∫ z in Cyl.cell c, (apL2G w z * Cyl.partialQ (fun z : Plane => etaCutoff R z.2 * w z 0) z
          + apL2G w z * Cyl.partialEta (fun z : Plane => etaCutoff R z.2 * w z 1) z)
      = ∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 * w z 1 * apL2G w z :=
    integral_congr_ae (ae_of_all _ fun z => by
      dsimp only
      rw [hpq0 z, hpe1 z]
      linear_combination (apL2G w z * etaCutoff R z.2) * hdz z)
  linarith [E0, E1, E2a, E2b, E4a, E4b, hq1, he1]

end UnforcedLeray.Short.PartI
