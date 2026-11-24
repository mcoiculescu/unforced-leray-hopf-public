import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_6

/-!
# Part III-a, `PartIII-a:T21/2/6/8`: lattice representation of the periodized Gaussian vorticity

Source of record: `the November 2 reference manuscript` (SP), lines 262-264 and
327-336. The periodized unit Gaussian vortex `datum_d = P_d v₀` (`Train.datum`) has the
components `datum_d(z)_k = ∑_n U_k(z - n d e₁)` with the unit-width profiles `U_k = uc k 1`
(`Train.Vc_zero`, `Train.Vc_comp_eq`, `B0147.vcomp_periodicVelocity`). Hence
`curl datum_d = ∂_q(∑U₁) - ∂_η(∑U₀) = ∑_n g₀(· - nd e₁)` with
`g₀ = gx + (-1) gy` a `GP` profile, where `gx, gy` are the termwise derivatives of `U₁, U₀`
(`GP.derivWord_lattice`). Every word derivative of the curl is again such a lattice sum
(`GP.derivWord_lattice` applied to `g₀`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- **Lattice representation of the periodized unit Gaussian vorticity** (SP 262-264, 327-336):
for every word `w` there is a `GP` profile `g` with `D_w curl(datum_d) = Σ_n g(· - nd e₁)` for
every period `d ≠ 0`. -/
theorem datumCurlLattice : DatumCurlLattice := by
  unfold DatumCurlLattice
  intro w
  obtain ⟨gx, hgx, hdx⟩ := UnforcedLeray.B0147.GP.derivWord_lattice
    (UnforcedLeray.B0147.GP_U 1) [true]
  obtain ⟨gy, hgy, hdy⟩ := UnforcedLeray.B0147.GP.derivWord_lattice
    (UnforcedLeray.B0147.GP_U 0) [false]
  have hg0 : UnforcedLeray.B0147.GP (fun y => gx y + (-1) * gy y) :=
    UnforcedLeray.B0147.GP.add hgx (UnforcedLeray.B0147.GP.smul (-1) hgy)
  obtain ⟨g, hg, hw⟩ := UnforcedLeray.B0147.GP.derivWord_lattice hg0 w
  refine ⟨g, hg, fun d hd => ?_⟩
  -- components of the datum as lattice sums of the unit profiles
  have hheat : UnforcedLeray.B0113.heatWidth 1 0 = 1 := by
    unfold UnforcedLeray.B0113.heatWidth
    ring
  have hcomp : ∀ (k : Fin 2) (z : ℝ × ℝ),
      UnforcedLeray.Train.datum d z k =
        UnforcedLeray.B0146.latticeSum d (UnforcedLeray.B0147.U k) z := by
    intro k z
    have hVc : UnforcedLeray.Train.Vc 1 d 0 = UnforcedLeray.Train.datum d :=
      UnforcedLeray.Train.Vc_zero 1 d
    have hpt : UnforcedLeray.Train.Vc 1 d 0 z k =
        UnforcedLeray.B0146.vcomp (UnforcedLeray.B0146.periodicVelocity 1 d 0 z) k :=
      congrFun (UnforcedLeray.Train.Vc_comp_eq 1 d 0 k) z
    have hvel := UnforcedLeray.B0147.vcomp_periodicVelocity (ν := 1) (s := 0) hd
      (by rw [hheat]; exact one_pos) k z
    rw [hheat] at hvel
    rw [← hVc]
    exact hpt.trans hvel
  -- the curl is the lattice sum of `g₀`
  have hneg : ∀ z : ℝ × ℝ,
      UnforcedLeray.B0146.latticeSum d (fun y => (-1) * gy y) z =
        (-1) * UnforcedLeray.B0146.latticeSum d gy z := by
    intro z
    unfold UnforcedLeray.B0146.latticeSum
    exact tsum_mul_left
  have hcurl : UnforcedLeray.Cyl.curl (UnforcedLeray.Train.datum d) =
      UnforcedLeray.B0146.latticeSum d (fun y => gx y + (-1) * gy y) := by
    funext z
    have e1 : (fun w => UnforcedLeray.Train.datum d w 1) =
        UnforcedLeray.B0146.latticeSum d (UnforcedLeray.B0147.U 1) :=
      funext fun w => hcomp 1 w
    have e0 : (fun w => UnforcedLeray.Train.datum d w 0) =
        UnforcedLeray.B0146.latticeSum d (UnforcedLeray.B0147.U 0) :=
      funext fun w => hcomp 0 w
    unfold UnforcedLeray.Cyl.curl
    rw [e1, e0]
    have hX : UnforcedLeray.Cyl.partialQ
        (UnforcedLeray.B0146.latticeSum d (UnforcedLeray.B0147.U 1)) z =
          UnforcedLeray.B0146.latticeSum d gx z := by
      rw [UnforcedLeray.Cyl.partialQ_eq_partialX]
      exact congrFun (hdx d hd) z
    have hY : UnforcedLeray.Cyl.partialEta
        (UnforcedLeray.B0146.latticeSum d (UnforcedLeray.B0147.U 0)) z =
          UnforcedLeray.B0146.latticeSum d gy z := by
      rw [UnforcedLeray.Cyl.partialEta_eq_partialY]
      exact congrFun (hdy d hd) z
    rw [hX, hY]
    have hsum : UnforcedLeray.B0146.latticeSum d (fun y => gx y + (-1) * gy y) z =
        UnforcedLeray.B0146.latticeSum d gx z +
          UnforcedLeray.B0146.latticeSum d (fun y => (-1) * gy y) z :=
      UnforcedLeray.B0147.latticeSum_add hgx.xdecay
        (UnforcedLeray.B0147.GP.smul (-1) hgy).xdecay hd z
    rw [hsum, hneg z]
    ring
  rw [hcurl]
  exact hw d hd

end UnforcedLeray.Short.IIIa
