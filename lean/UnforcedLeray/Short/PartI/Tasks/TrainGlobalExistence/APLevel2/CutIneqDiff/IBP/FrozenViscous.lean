import UnforcedLeray.Short.PartI.Sub.PartI_T04_9_1_2_2_2
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APEnstrophy.HasDeriv
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel2.CutIneqDiff.IBP.FrozenAlg.Helpers

/-!
# Part I, `APL2FrozenViscous`: viscous integration by parts (source lines 285-288)

For a `C^∞`, `c`-periodic `h`, `χ = etaCutoff R`:
`∫ χ h Δh = -∫ χ((∂_q h)² + (∂_η h)²) - ∫ χ' h ∂_η h` (`fv_one`, integrating by parts once in
`q` and once in `η`).  Applied to `h = P = ∂_qω` and `h = Q = ∂_ηω` and summed, the squares give
`eucJet2 ω` by definition.
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

/-- One-function viscous integration by parts. -/
theorem fv_one {c R : ℝ} (hc : 1 ≤ c) (hR : 1 ≤ R) (h : Plane → ℝ) (hh : ContDiff ℝ ∞ h)
    (hp : Cyl.IsPeriodic c h) :
    ∫ z in Cyl.cell c, etaCutoff R z.2 * (h z * Train.lapS h z)
      = -(∫ z in Cyl.cell c, etaCutoff R z.2 * (Cyl.partialQ h z ^ 2 + Cyl.partialEta h z ^ 2))
        - ∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 * (h z * Cyl.partialEta h z) := by
  have hc0 : 0 < c := by linarith
  have hR0 : 0 < R := by linarith
  have hφ1 : ContDiff ℝ ∞ (fun z : Plane => etaCutoff R z.2) :=
    (ecContDiff R hR0).comp contDiff_snd
  have hφd : Differentiable ℝ (fun z : Plane => etaCutoff R z.2) := hφ1.differentiable (by simp)
  have hφc : Continuous (fun z : Plane => etaCutoff R z.2) := hφ1.continuous
  have hφ'c : Continuous (fun z : Plane => deriv (etaCutoff R) z.2) :=
    ((ecContDiff R hR0).continuous_deriv (by norm_num)).comp continuous_snd
  have hφv : ∀ x : ℝ, 2 * R < |x| → etaCutoff R x = 0 := fun x hx => apHD_eta_zero hR0 hx.le
  have hhd : Differentiable ℝ h := hh.differentiable (by simp)
  have hhc : Continuous h := hh.continuous
  have hqh : ContDiff ℝ ∞ (Cyl.partialQ h) := Cyl.contDiff_partialQ hh
  have heh : ContDiff ℝ ∞ (Cyl.partialEta h) := Cyl.contDiff_partialEta hh
  have hqhd : Differentiable ℝ (Cyl.partialQ h) := hqh.differentiable (by simp)
  have hehd : Differentiable ℝ (Cyl.partialEta h) := heh.differentiable (by simp)
  have hqhc : Continuous (Cyl.partialQ h) := hqh.continuous
  have hehc : Continuous (Cyl.partialEta h) := heh.continuous
  have hqqc : Continuous (fun z : Plane => Cyl.partialQ (Cyl.partialQ h) z) :=
    (Cyl.contDiff_partialQ (n := ∞) hqh).continuous
  have heec : Continuous (fun z : Plane => Cyl.partialEta (Cyl.partialEta h) z) :=
    (Cyl.contDiff_partialEta (n := ∞) heh).continuous
  have hψ : ContDiff ℝ ∞ (fun z : Plane => etaCutoff R z.2 * h z) := hφ1.mul hh
  have hψd : Differentiable ℝ (fun z : Plane => etaCutoff R z.2 * h z) :=
    hψ.differentiable (by simp)
  have hψc : Continuous (fun z : Plane => etaCutoff R z.2 * h z) := hψ.continuous
  have hψp : Cyl.IsPeriodic c (fun z : Plane => etaCutoff R z.2 * h z) := fun z => by
    show etaCutoff R z.2 * h (z.1 + c, z.2) = etaCutoff R z.2 * h z
    rw [hp z]
  have hψq : ∀ z : Plane, Cyl.partialQ (fun z : Plane => etaCutoff R z.2 * h z) z
      = etaCutoff R z.2 * Cyl.partialQ h z := by
    intro z
    rw [apHD_pq_mul _ _ hφd hhd z]
    simp [apHD_pq_const]
  have hψe : ∀ z : Plane, Cyl.partialEta (fun z : Plane => etaCutoff R z.2 * h z) z
      = deriv (etaCutoff R) z.2 * h z + etaCutoff R z.2 * Cyl.partialEta h z :=
    fun z => (apHD_pe_mul _ _ hφd hhd z).trans rfl
  have hψqc : Continuous (fun z : Plane =>
      Cyl.partialQ (fun z : Plane => etaCutoff R z.2 * h z) z) :=
    (Cyl.contDiff_partialQ (n := ∞) hψ).continuous
  have hψec : Continuous (fun z : Plane =>
      Cyl.partialEta (fun z : Plane => etaCutoff R z.2 * h z) z) :=
    (Cyl.contDiff_partialEta (n := ∞) hψ).continuous
  -- integrability
  have hI1 : IntegrableOn (fun z : Plane => Cyl.partialQ (Cyl.partialQ h) z
      * (etaCutoff R z.2 * h z)) (Cyl.cell c) :=
    apHD_integ (c := c) (R0 := 2 * R) (hqqc.mul hψc) (fun z hz => by simp [apHD_eta_zero hR0 hz.le])
  have hI2 : IntegrableOn (fun z : Plane => Cyl.partialQ h z
      * Cyl.partialQ (fun z : Plane => etaCutoff R z.2 * h z) z) (Cyl.cell c) :=
    apHD_integ (c := c) (R0 := 2 * R) (hqhc.mul hψqc)
      (fun z hz => by simp [hψq z, apHD_eta_zero hR0 hz.le])
  have hI3 : IntegrableOn (fun z : Plane => Cyl.partialEta h z
      * (etaCutoff R z.2 * h z)) (Cyl.cell c) :=
    apHD_integ (c := c) (R0 := 2 * R) (hehc.mul hψc) (fun z hz => by simp [apHD_eta_zero hR0 hz.le])
  have hI4 : IntegrableOn (fun z : Plane => Cyl.partialEta (Cyl.partialEta h) z
      * (etaCutoff R z.2 * h z)) (Cyl.cell c) :=
    apHD_integ (c := c) (R0 := 2 * R) (heec.mul hψc) (fun z hz => by simp [apHD_eta_zero hR0 hz.le])
  have hI5 : IntegrableOn (fun z : Plane => Cyl.partialEta h z
      * Cyl.partialEta (fun z : Plane => etaCutoff R z.2 * h z) z) (Cyl.cell c) :=
    apHD_integ (c := c) (R0 := 2 * R) (hehc.mul hψec)
      (fun z hz => by simp [hψe z, apHD_deriv_zero hφv hz, apHD_eta_zero hR0 hz.le])
  have I5a : IntegrableOn (fun z : Plane => deriv (etaCutoff R) z.2 * (h z * Cyl.partialEta h z))
      (Cyl.cell c) :=
    apHD_integ (c := c) (R0 := 2 * R) (hφ'c.mul (hhc.mul hehc))
      (fun z hz => by simp [apHD_deriv_zero hφv hz])
  have I5b : IntegrableOn (fun z : Plane => etaCutoff R z.2 * Cyl.partialEta h z ^ 2) (Cyl.cell c) :=
    apHD_integ (c := c) (R0 := 2 * R) (hφc.mul (hehc.pow 2))
      (fun z hz => by simp [apHD_eta_zero hR0 hz.le])
  have hA6 : IntegrableOn (fun z : Plane => etaCutoff R z.2 * Cyl.partialQ h z ^ 2) (Cyl.cell c) :=
    apHD_integ (c := c) (R0 := 2 * R) (hφc.mul (hqhc.pow 2))
      (fun z hz => by simp [apHD_eta_zero hR0 hz.le])
  have hB6 : IntegrableOn (fun z : Plane => etaCutoff R z.2 * Cyl.partialEta h z ^ 2) (Cyl.cell c) :=
    I5b
  -- integration by parts in `q` and `η`
  have hq : ∫ z in Cyl.cell c, Cyl.partialQ (Cyl.partialQ h) z * (etaCutoff R z.2 * h z)
      = -∫ z in Cyl.cell c, Cyl.partialQ h z
          * Cyl.partialQ (fun z : Plane => etaCutoff R z.2 * h z) z :=
    Cyl.integral_cell_partialQ_mul hc0 hqhd hψd hp.partialQ hψp hI1 hI2
  have he : ∫ z in Cyl.cell c, Cyl.partialEta (Cyl.partialEta h) z * (etaCutoff R z.2 * h z)
      = -∫ z in Cyl.cell c, Cyl.partialEta h z
          * Cyl.partialEta (fun z : Plane => etaCutoff R z.2 * h z) z :=
    Cyl.integral_cell_partialEta_mul hehd hψd hI3 hI4 hI5
  -- splitting
  have S0 : ∫ z in Cyl.cell c, etaCutoff R z.2 * (h z * Train.lapS h z)
      = ∫ z in Cyl.cell c, (Cyl.partialQ (Cyl.partialQ h) z * (etaCutoff R z.2 * h z)
          + Cyl.partialEta (Cyl.partialEta h) z * (etaCutoff R z.2 * h z)) :=
    integral_congr_ae (ae_of_all _ fun z => by simp only [Train.lapS]; ring)
  have S1 : ∫ z in Cyl.cell c, (Cyl.partialQ (Cyl.partialQ h) z * (etaCutoff R z.2 * h z)
          + Cyl.partialEta (Cyl.partialEta h) z * (etaCutoff R z.2 * h z))
      = (∫ z in Cyl.cell c, Cyl.partialQ (Cyl.partialQ h) z * (etaCutoff R z.2 * h z))
          + ∫ z in Cyl.cell c, Cyl.partialEta (Cyl.partialEta h) z * (etaCutoff R z.2 * h z) :=
    integral_add hI1 hI4
  have hpt4 : ∀ z : Plane, Cyl.partialQ h z
      * Cyl.partialQ (fun z : Plane => etaCutoff R z.2 * h z) z = etaCutoff R z.2 * Cyl.partialQ h z ^ 2 :=
    fun z => by rw [hψq z]; ring
  have S4 : ∫ z in Cyl.cell c, Cyl.partialQ h z
      * Cyl.partialQ (fun z : Plane => etaCutoff R z.2 * h z) z
      = ∫ z in Cyl.cell c, etaCutoff R z.2 * Cyl.partialQ h z ^ 2 :=
    integral_congr_ae (ae_of_all _ hpt4)
  have hpt5 : ∀ z : Plane, Cyl.partialEta h z
      * Cyl.partialEta (fun z : Plane => etaCutoff R z.2 * h z) z
      = deriv (etaCutoff R) z.2 * (h z * Cyl.partialEta h z)
        + etaCutoff R z.2 * Cyl.partialEta h z ^ 2 :=
    fun z => by rw [hψe z]; ring
  have S5a : ∫ z in Cyl.cell c, Cyl.partialEta h z
      * Cyl.partialEta (fun z : Plane => etaCutoff R z.2 * h z) z
      = ∫ z in Cyl.cell c, (deriv (etaCutoff R) z.2 * (h z * Cyl.partialEta h z)
        + etaCutoff R z.2 * Cyl.partialEta h z ^ 2) :=
    integral_congr_ae (ae_of_all _ hpt5)
  have S5b : ∫ z in Cyl.cell c, (deriv (etaCutoff R) z.2 * (h z * Cyl.partialEta h z)
        + etaCutoff R z.2 * Cyl.partialEta h z ^ 2)
      = (∫ z in Cyl.cell c, deriv (etaCutoff R) z.2 * (h z * Cyl.partialEta h z))
          + ∫ z in Cyl.cell c, etaCutoff R z.2 * Cyl.partialEta h z ^ 2 :=
    integral_add I5a I5b
  have hpt6 : ∀ z : Plane, etaCutoff R z.2 * (Cyl.partialQ h z ^ 2 + Cyl.partialEta h z ^ 2)
      = etaCutoff R z.2 * Cyl.partialQ h z ^ 2 + etaCutoff R z.2 * Cyl.partialEta h z ^ 2 :=
    fun z => by ring
  have S6a : ∫ z in Cyl.cell c, etaCutoff R z.2 * (Cyl.partialQ h z ^ 2 + Cyl.partialEta h z ^ 2)
      = ∫ z in Cyl.cell c, (etaCutoff R z.2 * Cyl.partialQ h z ^ 2
          + etaCutoff R z.2 * Cyl.partialEta h z ^ 2) :=
    integral_congr_ae (ae_of_all _ hpt6)
  have S6b : ∫ z in Cyl.cell c, (etaCutoff R z.2 * Cyl.partialQ h z ^ 2
          + etaCutoff R z.2 * Cyl.partialEta h z ^ 2)
      = (∫ z in Cyl.cell c, etaCutoff R z.2 * Cyl.partialQ h z ^ 2)
          + ∫ z in Cyl.cell c, etaCutoff R z.2 * Cyl.partialEta h z ^ 2 :=
    integral_add hA6 hB6
  linarith [S0, S1, hq, he, S4, S5a, S5b, S6a, S6b]

/-- **`PartI:T04/9/1/2/2/2/4`**: the viscous integration by parts (`APL2FrozenViscous`,
source lines 285-288). -/
theorem aPL2FrozenViscous : UnforcedLeray.Short.PartI.APL2FrozenViscous := by
  intro c R w hc hR hw hper
  have hc0 : 0 < c := by linarith
  have hR0 : 0 < R := by linarith
  have hωp : Cyl.IsPeriodic c (Cyl.curl w) := fun z => by
    have hw0p : Cyl.IsPeriodic c (fun y => w y 0) := hper.fun_comp (fun x : Vec => x 0)
    have hw1p : Cyl.IsPeriodic c (fun y => w y 1) := hper.fun_comp (fun x : Vec => x 1)
    show Cyl.partialQ (fun y => w y 1) (z.1 + c, z.2) - Cyl.partialEta (fun y => w y 0) (z.1 + c, z.2)
      = Cyl.partialQ (fun y => w y 1) z - Cyl.partialEta (fun y => w y 0) z
    rw [hw1p.partialQ z, hw0p.partialEta z]
  have hωc : ContDiff ℝ ∞ (Cyl.curl w) := curl_contDiff hw
  have hPc : ContDiff ℝ ∞ (Cyl.partialQ (Cyl.curl w)) := Cyl.contDiff_partialQ hωc
  have hQc : ContDiff ℝ ∞ (Cyl.partialEta (Cyl.curl w)) := Cyl.contDiff_partialEta hωc
  have hPp : Cyl.IsPeriodic c (Cyl.partialQ (Cyl.curl w)) := hωp.partialQ
  have hQp : Cyl.IsPeriodic c (Cyl.partialEta (Cyl.curl w)) := hωp.partialEta
  have hP := fv_one hc hR (Cyl.partialQ (Cyl.curl w)) hPc hPp
  have hQ := fv_one hc hR (Cyl.partialEta (Cyl.curl w)) hQc hQp
  have hφ1 : ContDiff ℝ ∞ (fun z : Plane => etaCutoff R z.2) :=
    (ecContDiff R hR0).comp contDiff_snd
  have hφc : Continuous (fun z : Plane => etaCutoff R z.2) := hφ1.continuous
  have hφ'c : Continuous (fun z : Plane => deriv (etaCutoff R) z.2) :=
    ((ecContDiff R hR0).continuous_deriv (by norm_num)).comp continuous_snd
  have hφv : ∀ x : ℝ, 2 * R < |x| → etaCutoff R x = 0 := fun x hx => apHD_eta_zero hR0 hx.le
  have hPq : Continuous (fun z : Plane => Cyl.partialQ (Cyl.partialQ (Cyl.curl w)) z) :=
    (Cyl.contDiff_partialQ (n := ∞) hPc).continuous
  have hPe : Continuous (fun z : Plane => Cyl.partialEta (Cyl.partialQ (Cyl.curl w)) z) :=
    (Cyl.contDiff_partialEta (n := ∞) hPc).continuous
  have hQq : Continuous (fun z : Plane => Cyl.partialQ (Cyl.partialEta (Cyl.curl w)) z) :=
    (Cyl.contDiff_partialQ (n := ∞) hQc).continuous
  have hQe : Continuous (fun z : Plane => Cyl.partialEta (Cyl.partialEta (Cyl.curl w)) z) :=
    (Cyl.contDiff_partialEta (n := ∞) hQc).continuous
  have hPf : Continuous (fun z : Plane => Cyl.partialQ (Cyl.curl w) z) := hPc.continuous
  have hQf : Continuous (fun z : Plane => Cyl.partialEta (Cyl.curl w) z) := hQc.continuous
  have hPL : Continuous (fun z : Plane =>
      Cyl.partialQ (Cyl.curl w) z * Train.lapS (Cyl.partialQ (Cyl.curl w)) z) :=
    hPf.mul (lapS_contDiff _ hPc).continuous
  have hQL : Continuous (fun z : Plane =>
      Cyl.partialEta (Cyl.curl w) z * Train.lapS (Cyl.partialEta (Cyl.curl w)) z) :=
    hQf.mul (lapS_contDiff _ hQc).continuous
  -- splitting the Laplacian term
  have hI : IntegrableOn (fun z : Plane => etaCutoff R z.2
      * (Cyl.partialQ (Cyl.curl w) z * Train.lapS (Cyl.partialQ (Cyl.curl w)) z)) (Cyl.cell c) :=
    apHD_integ (c := c) (R0 := 2 * R) (hφc.mul hPL)
      (fun z hz => by simp [apHD_eta_zero hR0 hz.le])
  have hJ : IntegrableOn (fun z : Plane => etaCutoff R z.2
      * (Cyl.partialEta (Cyl.curl w) z * Train.lapS (Cyl.partialEta (Cyl.curl w)) z)) (Cyl.cell c) :=
    apHD_integ (c := c) (R0 := 2 * R) (hφc.mul hQL)
      (fun z hz => by simp [apHD_eta_zero hR0 hz.le])
  have T0 : ∫ z in Cyl.cell c, etaCutoff R z.2 * (Cyl.partialQ (Cyl.curl w) z
        * Train.lapS (Cyl.partialQ (Cyl.curl w)) z
      + Cyl.partialEta (Cyl.curl w) z * Train.lapS (Cyl.partialEta (Cyl.curl w)) z)
      = (∫ z in Cyl.cell c, etaCutoff R z.2
          * (Cyl.partialQ (Cyl.curl w) z * Train.lapS (Cyl.partialQ (Cyl.curl w)) z))
        + ∫ z in Cyl.cell c, etaCutoff R z.2
          * (Cyl.partialEta (Cyl.curl w) z * Train.lapS (Cyl.partialEta (Cyl.curl w)) z) := by
    have pt : ∀ z : Plane, etaCutoff R z.2 * (Cyl.partialQ (Cyl.curl w) z
          * Train.lapS (Cyl.partialQ (Cyl.curl w)) z
        + Cyl.partialEta (Cyl.curl w) z * Train.lapS (Cyl.partialEta (Cyl.curl w)) z)
        = etaCutoff R z.2 * (Cyl.partialQ (Cyl.curl w) z * Train.lapS (Cyl.partialQ (Cyl.curl w)) z)
          + etaCutoff R z.2
            * (Cyl.partialEta (Cyl.curl w) z * Train.lapS (Cyl.partialEta (Cyl.curl w)) z) :=
      fun z => by ring
    exact (integral_congr_ae (ae_of_all _ pt)).trans (integral_add hI hJ)
  -- splitting the eucJet2 term
  have hA1 : Continuous (fun z : Plane => Cyl.partialQ (Cyl.partialQ (Cyl.curl w)) z ^ 2
      + Cyl.partialEta (Cyl.partialQ (Cyl.curl w)) z ^ 2) := (hPq.pow 2).add (hPe.pow 2)
  have hB1 : Continuous (fun z : Plane => Cyl.partialQ (Cyl.partialEta (Cyl.curl w)) z ^ 2
      + Cyl.partialEta (Cyl.partialEta (Cyl.curl w)) z ^ 2) := (hQq.pow 2).add (hQe.pow 2)
  have hIA : IntegrableOn (fun z : Plane => etaCutoff R z.2 * (Cyl.partialQ (Cyl.partialQ (Cyl.curl w)) z ^ 2
      + Cyl.partialEta (Cyl.partialQ (Cyl.curl w)) z ^ 2)) (Cyl.cell c) :=
    apHD_integ (c := c) (R0 := 2 * R) (hφc.mul hA1)
      (fun z hz => by simp [apHD_eta_zero hR0 hz.le])
  have hIB : IntegrableOn (fun z : Plane => etaCutoff R z.2 * (Cyl.partialQ (Cyl.partialEta (Cyl.curl w)) z ^ 2
      + Cyl.partialEta (Cyl.partialEta (Cyl.curl w)) z ^ 2)) (Cyl.cell c) :=
    apHD_integ (c := c) (R0 := 2 * R) (hφc.mul hB1)
      (fun z hz => by simp [apHD_eta_zero hR0 hz.le])
  have T1 : ∫ z in Cyl.cell c, etaCutoff R z.2 * eucJet2 (Cyl.curl w) z
      = (∫ z in Cyl.cell c, etaCutoff R z.2 * (Cyl.partialQ (Cyl.partialQ (Cyl.curl w)) z ^ 2
          + Cyl.partialEta (Cyl.partialQ (Cyl.curl w)) z ^ 2))
        + ∫ z in Cyl.cell c, etaCutoff R z.2 * (Cyl.partialQ (Cyl.partialEta (Cyl.curl w)) z ^ 2
          + Cyl.partialEta (Cyl.partialEta (Cyl.curl w)) z ^ 2) := by
    have pt : ∀ z : Plane, etaCutoff R z.2 * eucJet2 (Cyl.curl w) z
        = etaCutoff R z.2 * (Cyl.partialQ (Cyl.partialQ (Cyl.curl w)) z ^ 2
          + Cyl.partialEta (Cyl.partialQ (Cyl.curl w)) z ^ 2)
        + etaCutoff R z.2 * (Cyl.partialQ (Cyl.partialEta (Cyl.curl w)) z ^ 2
          + Cyl.partialEta (Cyl.partialEta (Cyl.curl w)) z ^ 2) := fun z => by
      unfold eucJet2
      ring
    exact (integral_congr_ae (ae_of_all _ pt)).trans (integral_add hIA hIB)
  -- splitting the transport term
  have hIC : IntegrableOn (fun z : Plane => deriv (etaCutoff R) z.2
      * (Cyl.partialQ (Cyl.curl w) z * Cyl.partialEta (Cyl.partialQ (Cyl.curl w)) z)) (Cyl.cell c) :=
    apHD_integ (c := c) (R0 := 2 * R) (hφ'c.mul (hPf.mul hPe))
      (fun z hz => by simp [apHD_deriv_zero hφv hz])
  have hID : IntegrableOn (fun z : Plane => deriv (etaCutoff R) z.2
      * (Cyl.partialEta (Cyl.curl w) z * Cyl.partialEta (Cyl.partialEta (Cyl.curl w)) z)) (Cyl.cell c) :=
    apHD_integ (c := c) (R0 := 2 * R) (hφ'c.mul (hQf.mul hQe))
      (fun z hz => by simp [apHD_deriv_zero hφv hz])
  have T2 : ∫ z in Cyl.cell c, deriv (etaCutoff R) z.2
        * (Cyl.partialQ (Cyl.curl w) z * Cyl.partialEta (Cyl.partialQ (Cyl.curl w)) z
          + Cyl.partialEta (Cyl.curl w) z * Cyl.partialEta (Cyl.partialEta (Cyl.curl w)) z)
      = (∫ z in Cyl.cell c, deriv (etaCutoff R) z.2
          * (Cyl.partialQ (Cyl.curl w) z * Cyl.partialEta (Cyl.partialQ (Cyl.curl w)) z))
        + ∫ z in Cyl.cell c, deriv (etaCutoff R) z.2
          * (Cyl.partialEta (Cyl.curl w) z * Cyl.partialEta (Cyl.partialEta (Cyl.curl w)) z) := by
    have pt : ∀ z : Plane, deriv (etaCutoff R) z.2
        * (Cyl.partialQ (Cyl.curl w) z * Cyl.partialEta (Cyl.partialQ (Cyl.curl w)) z
          + Cyl.partialEta (Cyl.curl w) z * Cyl.partialEta (Cyl.partialEta (Cyl.curl w)) z)
        = deriv (etaCutoff R) z.2
          * (Cyl.partialQ (Cyl.curl w) z * Cyl.partialEta (Cyl.partialQ (Cyl.curl w)) z)
        + deriv (etaCutoff R) z.2
          * (Cyl.partialEta (Cyl.curl w) z * Cyl.partialEta (Cyl.partialEta (Cyl.curl w)) z) :=
      fun z => by ring
    exact (integral_congr_ae (ae_of_all _ pt)).trans (integral_add hIC hID)
  linarith [T0, T1, T2, hP, hQ]

end UnforcedLeray.Short.PartI
