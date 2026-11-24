import UnforcedLeray.Short.PartI.Sub.PartI_T04_9_1_2_2_2
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APEnstrophy.HasDeriv
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel2.CutIneqDiff.IBP.FrozenAlg.Helpers

/-!
# Part I, `APL2FrozenAlg`: the pointwise algebra for a frozen field (source lines 285-288)

For a `C^∞`, `c`-periodic field `w` with `ω = curl w`, `P = ∂_qω`, `Q = ∂_ηω`, the vorticity
right-hand side `F = apL2F ν w` satisfies, pointwise,
`2(P ∂_qF + Q ∂_ηF) = -2 X - (w_0 ∂_q g + w_1 ∂_η g) + 2ν(P ΔP + Q ΔQ)` with `g = P² + Q²`
and `X` the trilinear integrand of `apL2X`.  The proof is the Leibniz rule for `F`, Schwarz symmetry
of mixed partials (`∂_η P = ∂_q Q`), commutation of `∂_q, ∂_η` with `Δ`, and integration over the
cell (the integrands are continuous and vanish for `|η| ≥ 2R`).
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

/-- **`PartI:T04/9/1/2/2/2/2`**: the integrated pointwise algebra for a frozen field
(`APL2FrozenAlg`, source lines 285-288). -/
theorem aPL2FrozenAlg : UnforcedLeray.Short.PartI.APL2FrozenAlg := by
  intro ν c R w hν hc hR hw hper hdiv
  have hR0 : 0 < R := by linarith
  have hwd : Differentiable ℝ w := hw.differentiable (by simp)
  have hωc : ContDiff ℝ ∞ (Cyl.curl w) := curl_contDiff hw
  have hP : ContDiff ℝ ∞ (Cyl.partialQ (Cyl.curl w)) := Cyl.contDiff_partialQ hωc
  have hQ : ContDiff ℝ ∞ (Cyl.partialEta (Cyl.curl w)) := Cyl.contDiff_partialEta hωc
  have hPd : Differentiable ℝ (Cyl.partialQ (Cyl.curl w)) := hP.differentiable (by simp)
  have hQd : Differentiable ℝ (Cyl.partialEta (Cyl.curl w)) := hQ.differentiable (by simp)
  have hLd : Differentiable ℝ (Train.lapS (Cyl.curl w)) :=
    (lapS_contDiff _ hωc).differentiable (by simp)
  have hu0 : ContDiff ℝ ∞ (fun y => w y 0) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).contDiff.comp hw
  have hu1 : ContDiff ℝ ∞ (fun y => w y 1) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).contDiff.comp hw
  have hu0d : Differentiable ℝ (fun y => w y 0) := hu0.differentiable (by simp)
  have hu1d : Differentiable ℝ (fun y => w y 1) := hu1.differentiable (by simp)
  have hPPd : Differentiable ℝ (fun y => Cyl.partialQ (Cyl.curl w) y * Cyl.partialQ (Cyl.curl w) y) :=
    fun y => (hPd y).mul (hPd y)
  have hQQd : Differentiable ℝ (fun y => Cyl.partialEta (Cyl.curl w) y * Cyl.partialEta (Cyl.curl w) y) :=
    fun y => (hQd y).mul (hQd y)
  have hLq := lapComm_q _ hωc
  have hLe := lapComm_e _ hωc
  -- Leibniz rules for `∂_q F` and `∂_η F`
  have hFq : ∀ z : Plane, Cyl.partialQ (apL2F ν w) z
      = -(Cyl.partialQ w z 0 * Cyl.partialQ (Cyl.curl w) z
          + w z 0 * Cyl.partialQ (Cyl.partialQ (Cyl.curl w)) z
          + (Cyl.partialQ w z 1 * Cyl.partialEta (Cyl.curl w) z
            + w z 1 * Cyl.partialQ (Cyl.partialEta (Cyl.curl w)) z))
        + ν * Train.lapS (Cyl.partialQ (Cyl.curl w)) z := by
    intro z
    have e := pqF4 (f := fun y => w y 0) (g := Cyl.partialQ (Cyl.curl w))
      (h := fun y => w y 1) (k := Cyl.partialEta (Cyl.curl w)) (m := Train.lapS (Cyl.curl w))
      hu0d hPd hu1d hQd hLd ν z
    rw [hLq, pqComp w hwd 0 z, pqComp w hwd 1 z] at e
    exact e
  have hFe : ∀ z : Plane, Cyl.partialEta (apL2F ν w) z
      = -(Cyl.partialEta w z 0 * Cyl.partialQ (Cyl.curl w) z
          + w z 0 * Cyl.partialEta (Cyl.partialQ (Cyl.curl w)) z
          + (Cyl.partialEta w z 1 * Cyl.partialEta (Cyl.curl w) z
            + w z 1 * Cyl.partialEta (Cyl.partialEta (Cyl.curl w)) z))
        + ν * Train.lapS (Cyl.partialEta (Cyl.curl w)) z := by
    intro z
    have e := peF4 (f := fun y => w y 0) (g := Cyl.partialQ (Cyl.curl w))
      (h := fun y => w y 1) (k := Cyl.partialEta (Cyl.curl w)) (m := Train.lapS (Cyl.curl w))
      hu0d hPd hu1d hQd hLd ν z
    rw [hLe, peComp w hwd 0 z, peComp w hwd 1 z] at e
    exact e
  -- Schwarz: `∂_q ∂_η ω = ∂_η ∂_q ω`
  have hS : ∀ z : Plane, Cyl.partialQ (Cyl.partialEta (Cyl.curl w)) z
      = Cyl.partialEta (Cyl.partialQ (Cyl.curl w)) z :=
    fun z => pqpe_comm _ hωc z
  -- gradient of the enstrophy density `g = P² + Q²`
  have hGq : ∀ z : Plane, Cyl.partialQ (apL2G w) z
      = 2 * Cyl.partialQ (Cyl.curl w) z * Cyl.partialQ (Cyl.partialQ (Cyl.curl w)) z
        + 2 * Cyl.partialEta (Cyl.curl w) z * Cyl.partialQ (Cyl.partialEta (Cyl.curl w)) z := by
    intro z
    have e : apL2G w = fun y => Cyl.partialQ (Cyl.curl w) y * Cyl.partialQ (Cyl.curl w) y
        + Cyl.partialEta (Cyl.curl w) y * Cyl.partialEta (Cyl.curl w) y :=
      funext fun y => by unfold apL2G; ring
    rw [e, pqAdd _ _ hPPd hQQd z, apHD_pq_mul _ _ hPd hPd z,
      apHD_pq_mul _ _ hQd hQd z]
    ring
  have hGe : ∀ z : Plane, Cyl.partialEta (apL2G w) z
      = 2 * Cyl.partialQ (Cyl.curl w) z * Cyl.partialEta (Cyl.partialQ (Cyl.curl w)) z
        + 2 * Cyl.partialEta (Cyl.curl w) z * Cyl.partialEta (Cyl.partialEta (Cyl.curl w)) z := by
    intro z
    have e : apL2G w = fun y => Cyl.partialQ (Cyl.curl w) y * Cyl.partialQ (Cyl.curl w) y
        + Cyl.partialEta (Cyl.curl w) y * Cyl.partialEta (Cyl.curl w) y :=
      funext fun y => by unfold apL2G; ring
    rw [e, peAdd _ _ hPPd hQQd z, apHD_pe_mul _ _ hPd hPd z,
      apHD_pe_mul _ _ hQd hQd z]
    ring
  -- smoothness and continuity
  have hGC : ContDiff ℝ ∞ (apL2G w) := (hP.pow 2).add (hQ.pow 2)
  have hGqc : Continuous (fun z : Plane => Cyl.partialQ (apL2G w) z) :=
    (Cyl.contDiff_partialQ (n := ∞) hGC).continuous
  have hGec : Continuous (fun z : Plane => Cyl.partialEta (apL2G w) z) :=
    (Cyl.contDiff_partialEta (n := ∞) hGC).continuous
  have hPc : Continuous (fun z : Plane => Cyl.partialQ (Cyl.curl w) z) := hP.continuous
  have hQc : Continuous (fun z : Plane => Cyl.partialEta (Cyl.curl w) z) := hQ.continuous
  have hPLc : Continuous (fun z : Plane => Train.lapS (Cyl.partialQ (Cyl.curl w)) z) :=
    (lapS_contDiff _ hP).continuous
  have hQLc : Continuous (fun z : Plane => Train.lapS (Cyl.partialEta (Cyl.curl w)) z) :=
    (lapS_contDiff _ hQ).continuous
  have hw0c : Continuous (fun z : Plane => w z 0) := hu0.continuous
  have hw1c : Continuous (fun z : Plane => w z 1) := hu1.continuous
  have hdw : ContDiff ℝ ∞ (Cyl.partialQ w) := Cyl.contDiff_partialQ hw
  have hew : ContDiff ℝ ∞ (Cyl.partialEta w) := Cyl.contDiff_partialEta hw
  have hA0 : Continuous (fun z : Plane => Cyl.partialQ w z 0) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).continuous.comp hdw.continuous
  have hA1 : Continuous (fun z : Plane => Cyl.partialQ w z 1) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous.comp hdw.continuous
  have hB0 : Continuous (fun z : Plane => Cyl.partialEta w z 0) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).continuous.comp hew.continuous
  have hB1 : Continuous (fun z : Plane => Cyl.partialEta w z 1) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).continuous.comp hew.continuous
  have hXc : Continuous (fun z : Plane =>
      Cyl.partialQ (Cyl.curl w) z * Cyl.partialQ w z 0 * Cyl.partialQ (Cyl.curl w) z
        + Cyl.partialQ (Cyl.curl w) z * Cyl.partialQ w z 1 * Cyl.partialEta (Cyl.curl w) z
        + Cyl.partialEta (Cyl.curl w) z * Cyl.partialEta w z 0 * Cyl.partialQ (Cyl.curl w) z
        + Cyl.partialEta (Cyl.curl w) z * Cyl.partialEta w z 1 * Cyl.partialEta (Cyl.curl w) z) :=
    ((((hPc.mul hA0).mul hPc).add ((hPc.mul hA1).mul hQc)).add ((hQc.mul hB0).mul hPc)).add
      ((hQc.mul hB1).mul hQc)
  have hwGc : Continuous (fun z : Plane =>
      -(w z 0 * Cyl.partialQ (apL2G w) z + w z 1 * Cyl.partialEta (apL2G w) z)) :=
    ((hw0c.mul hGqc).add (hw1c.mul hGec)).neg
  have hPQc : Continuous (fun z : Plane =>
      Cyl.partialQ (Cyl.curl w) z * Train.lapS (Cyl.partialQ (Cyl.curl w)) z
        + Cyl.partialEta (Cyl.curl w) z * Train.lapS (Cyl.partialEta (Cyl.curl w)) z) :=
    (hPc.mul hPLc).add (hQc.mul hQLc)
  -- the pointwise identity
  have hpt : ∀ z : Plane,
      etaCutoff R z.2 * (2 * (Cyl.partialQ (Cyl.curl w) z * Cyl.partialQ (apL2F ν w) z
          + Cyl.partialEta (Cyl.curl w) z * Cyl.partialEta (apL2F ν w) z))
        = (-2) * (etaCutoff R z.2 * (Cyl.partialQ (Cyl.curl w) z * Cyl.partialQ w z 0
              * Cyl.partialQ (Cyl.curl w) z
            + Cyl.partialQ (Cyl.curl w) z * Cyl.partialQ w z 1 * Cyl.partialEta (Cyl.curl w) z
            + Cyl.partialEta (Cyl.curl w) z * Cyl.partialEta w z 0 * Cyl.partialQ (Cyl.curl w) z
            + Cyl.partialEta (Cyl.curl w) z * Cyl.partialEta w z 1
              * Cyl.partialEta (Cyl.curl w) z))
          + etaCutoff R z.2 * (-(w z 0 * Cyl.partialQ (apL2G w) z
              + w z 1 * Cyl.partialEta (apL2G w) z))
          + (2 * ν) * (etaCutoff R z.2 * (Cyl.partialQ (Cyl.curl w) z
              * Train.lapS (Cyl.partialQ (Cyl.curl w)) z
            + Cyl.partialEta (Cyl.curl w) z * Train.lapS (Cyl.partialEta (Cyl.curl w)) z)) := by
    intro z
    rw [hFq z, hFe z, hGq z, hGe z, hS z]
    ring
  have hX : apL2X c (fun _ => w) R 0 = ∫ z in Cyl.cell c, etaCutoff R z.2 *
      (Cyl.partialQ (Cyl.curl w) z * Cyl.partialQ w z 0 * Cyl.partialQ (Cyl.curl w) z
        + Cyl.partialQ (Cyl.curl w) z * Cyl.partialQ w z 1 * Cyl.partialEta (Cyl.curl w) z
        + Cyl.partialEta (Cyl.curl w) z * Cyl.partialEta w z 0 * Cyl.partialQ (Cyl.curl w) z
        + Cyl.partialEta (Cyl.curl w) z * Cyl.partialEta w z 1 * Cyl.partialEta (Cyl.curl w) z) :=
    rfl
  have hI1 := Integrable.const_mul (intg_phi (c := c) hR0 hXc) (-2)
  have hI2 := intg_phi (c := c) hR0 hwGc
  have hI3 := Integrable.const_mul (intg_phi (c := c) hR0 hPQc) (2 * ν)
  refine (integral_congr_ae (ae_of_all _ hpt)).trans ?_
  rw [integral_add, integral_add, integral_const_mul (-2), integral_const_mul (2 * ν), hX]
  all_goals first
    | ring1
    | exact hI1
    | exact hI2
    | exact hI3
    | exact Integrable.add hI1 hI2
    | exact Integrable.add (Integrable.add hI1 hI2) hI3

end UnforcedLeray.Short.PartI
