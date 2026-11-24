import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_1_2_4_1.PointDom.Defs

/-!
# Decomposition of `pdKerShifted` (`PartIII-b:C/rep/5/1/2/4/1/2/4`; source 4198-4201, 3600-3610, 3708-3709)

Source: `the November 2 reference manuscript`.

`PDKerShifted` follows (chain rule and coefficient algebra, proved here) from two kernel facts about
`F_t(x) = gradKCon t x M = ∇K_t(x) : M`:

* `GradKHeat`: the heat equation `∂_t F = Δ_x F` for `t > 0` (from `K_t = δG_t + ∂∂∫_t^∞G_a da`,
  `∂_tG = ΔG`, `∂_t∫_t^∞G_a = -G_t`, `Δ∫_t^∞G_a = -G_t`);
* `GradKEuler`: the parabolic homogeneity `x·∇F + 2t∂_tF = -4F` (from `K_t(x) = t^{-3/2}K_1(x/√t)`,
  `HeatLerayScale`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **Heat equation for the contracted kernel gradient** (source 3600-3610): for `t > 0`,
`∂_t (∇K_t(x) : M) = Δ_x (∇K_t : M)(x)`. -/
def GradKHeat : Prop :=
  ∀ (t : ℝ), 0 < t → ∀ (x : Space) (M : Matrix (Fin 3) (Fin 3) ℝ),
    HasDerivAt (fun t' => gradKCon t' x M) (physLap (fun y => gradKCon t y M) x) t

/-- **Parabolic homogeneity of the contracted kernel gradient** (source 3600-3610,
`K_t(x) = t^{-3/2}K_1(x/√t)`): `x·∇_x F + 2t ∂_tF = -4F` for `F = ∇K_t : M`, `t > 0`. -/
def GradKEuler : Prop :=
  ∀ (t : ℝ), 0 < t → ∀ (x : Space) (M : Matrix (Fin 3) (Fin 3) ℝ),
    fderiv ℝ (fun y => gradKCon t y M) x x =
      (-2 * t) • deriv (fun t' => gradKCon t' x M) t - (4 : ℝ) • gradKCon t x M

/-- **Heat equation for the partial derivatives of the heat-Leray kernel** (source 3600-3610,
`K_t = δ G_t + ∂_i∂_j ∫_t^∞ G_a da`, `∂_t G = ΔG`, `∂_t∫_t^∞G_a = -G_t`, `Δ∫_t^∞G_a = -G_t`): for
`t > 0`, `∂_t (∂_k K_t)_{ij}(x) = Δ_x (∂_k K_t)_{ij}(x)`. -/
def KernelPartialHeat : Prop :=
  ∀ (t : ℝ), 0 < t → ∀ (i j k : Fin 3) (x : Space),
    HasDerivAt (fun t' => fderiv ℝ (fun y => IIIa.heatLerayK t' i j y) x (coordinateVector k))
      (∑ l : Fin 3, fderiv ℝ (fun y => fderiv ℝ (fun y' =>
        fderiv ℝ (fun z => IIIa.heatLerayK t i j z) y' (coordinateVector k)) y (coordinateVector l))
        x (coordinateVector l)) t

lemma physLap_const_smul (c : ℝ) (F : Space → Space) (x : Space) :
    physLap (fun y => c • F y) x = c • physLap F x := by
  unfold physLap physPd2 physPd
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : fderiv ℝ (fun y => c • F y) = fun y => c • fderiv ℝ F y := by
    have := fderiv_const_smul_field (𝕜 := ℝ) (f := F) c
    funext y
    exact congrFun this y
  have h2 : (fun y' => fderiv ℝ (fun y => c • F y) y' (coordinateVector j))
      = fun y' => c • fderiv ℝ F y' (coordinateVector j) := by
    funext y'; rw [h1]; rfl
  rw [h2]
  have := fderiv_const_smul_field (𝕜 := ℝ)
    (f := fun y' => fderiv ℝ F y' (coordinateVector j)) c
  have h3 := congrFun this x
  exact congrArg (fun L => L (coordinateVector j)) h3

lemma fderiv_const_smul_apply (c : ℝ) (F : Space → Space) (x v : Space) :
    fderiv ℝ (fun y => c • F y) x v = c • fderiv ℝ F x v := by
  have := fderiv_const_smul_field (𝕜 := ℝ) (f := F) c
  exact congrArg (fun L => L v) (congrFun this x)

lemma pdLam_pow (h r : ℝ) : pdLam h ^ r = Real.exp (-(h / 2) * r) := by
  unfold pdLam
  rw [← Real.exp_mul]

theorem pdKerShifted_of (h1 : GradKHeat) (h2 : GradKEuler) : PDKerShifted := by
  intro ν μ h hν hh x M
  set A : ℝ := pdLam h ^ (2 * μ + 3) with hA
  set B : ℝ := pdLam h ^ (2 * μ + 5) with hB
  set T : ℝ := ν * (1 - pdLam h ^ 2) with hT
  have hlam2 : pdLam h ^ 2 = Real.exp (-h) := by
    unfold pdLam; rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hTpos : 0 < T := by
    rw [hT, hlam2]
    have : Real.exp (-h) < 1 := by
      have := Real.exp_lt_exp.2 (show -h < 0 by linarith)
      simpa using this
    exact mul_pos hν (by linarith)
  have hBA : B = Real.exp (-h) * A := by
    rw [hA, hB, pdLam_pow, pdLam_pow, ← Real.exp_add]; congr 1; ring
  -- derivatives of the scalar coefficients
  have dA : HasDerivAt (fun h' => pdLam h' ^ (2 * μ + 3)) (-(2 * μ + 3) / 2 * A) h := by
    have : (fun h' => pdLam h' ^ (2 * μ + 3)) = fun h' => Real.exp (-(h' / 2) * (2 * μ + 3)) := by
      funext h'; exact pdLam_pow _ _
    rw [this]
    have hd : HasDerivAt (fun h' : ℝ => -(h' / 2) * (2 * μ + 3)) (-(1 / 2) * (2 * μ + 3)) h := by
      have := ((hasDerivAt_id h).div_const 2).neg.mul_const (2 * μ + 3)
      simpa using this
    have := hd.exp
    convert this using 1
    rw [hA, pdLam_pow]; ring
  have dB : HasDerivAt (fun h' => pdLam h' ^ (2 * μ + 5)) (-(2 * μ + 5) / 2 * B) h := by
    have : (fun h' => pdLam h' ^ (2 * μ + 5)) = fun h' => Real.exp (-(h' / 2) * (2 * μ + 5)) := by
      funext h'; exact pdLam_pow _ _
    rw [this]
    have hd : HasDerivAt (fun h' : ℝ => -(h' / 2) * (2 * μ + 5)) (-(1 / 2) * (2 * μ + 5)) h := by
      have := ((hasDerivAt_id h).div_const 2).neg.mul_const (2 * μ + 5)
      simpa using this
    have := hd.exp
    convert this using 1
    rw [hB, pdLam_pow]; ring
  have dT : HasDerivAt (fun h' => ν * (1 - pdLam h' ^ 2)) (ν * Real.exp (-h)) h := by
    have : (fun h' => ν * (1 - pdLam h' ^ 2)) = fun h' => ν * (1 - Real.exp (-h')) := by
      funext h'
      unfold pdLam; rw [← Real.exp_nat_mul]; congr 3; push_cast; ring
    rw [this]
    have := (((hasDerivAt_id h).neg.exp).const_sub 1).const_mul ν
    exact this.congr_deriv (by simp)
  have da : HasDerivAt (fun h' => -(pdLam h' ^ (2 * μ + 3) - pdLam h' ^ (2 * μ + 5)))
      (-(-(2 * μ + 3) / 2 * A - -(2 * μ + 5) / 2 * B)) h := (dA.sub dB).neg
  have dG : HasDerivAt (fun h' => gradKCon (ν * (1 - pdLam h' ^ 2)) x M)
      ((ν * Real.exp (-h)) • physLap (fun y => gradKCon T y M) x) h := by
    have := (h1 T hTpos x M).scomp h dT
    exact this
  have dX := da.smul dG
  have hder : deriv (fun t => xKer ν μ t x M) h =
      (-(A - B)) • ((ν * Real.exp (-h)) • physLap (fun y => gradKCon T y M) x) +
        (-(-(2 * μ + 3) / 2 * A - -(2 * μ + 5) / 2 * B)) • gradKCon T x M := by
    have : (fun t => xKer ν μ t x M) =
        fun t => (-(pdLam t ^ (2 * μ + 3) - pdLam t ^ (2 * μ + 5))) •
          gradKCon (ν * (1 - pdLam t ^ 2)) x M := rfl
    rw [this]
    exact dX.deriv
  have hfd : fderiv ℝ (fun y => xKer ν μ h y M) x x = (-(A - B)) • fderiv ℝ (fun y => gradKCon T y M) x x := by
    exact fderiv_const_smul_apply (-(A - B)) (fun y => gradKCon T y M) x x
  have hlap : physLap (fun y => xKer ν μ h y M) x = (-(A - B)) • physLap (fun y => gradKCon T y M) x :=
    physLap_const_smul (-(A - B)) (fun y => gradKCon T y M) x
  have hE := h2 T hTpos x M
  have hheat := (h1 T hTpos x M).deriv
  unfold wKer
  unfold physDmu
  rw [hder, hfd, hlap, hE, hheat]
  show _ = (-A) • gradKCon T x M
  have hTe : T = ν * (1 - Real.exp (-h)) := by rw [hT, hlam2]
  set G := gradKCon T x M
  set L := physLap (fun y => gradKCon T y M) x
  have hxk : xKer ν μ h x M = (-(A - B)) • G := rfl
  beta_reduce
  rw [hxk, hBA, hTe]
  module
