import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.GradWeak.GWQ.Calc3

/-!
# `PartII-b:T10/7/1/2/4` (`GWQ`) helper: lift algebra and the coordinate transpose
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb.GWQ

open UnforcedLeray UnforcedLeray.PhaseSpace UnforcedLeray.Cons.C03.Concrete

theorem ctLift_half {c ε a : ℝ} (hε : 0 < ε) (φ : Coord → ℝ) {x : ℝ × Space}
    (hy : x.2 ∉ Axi.axis) :
    ctLift c ε a φ x * (Axi.ϱ x.2)⁻¹ = ε * ctLift c ε (a + 1 / 2) φ x := by
  have hR : 0 < ε⁻¹ := inv_pos.2 hε
  have hpos : 0 < Axi.age ε⁻¹ x.2 := Axi.age_pos hR.ne' hy
  have hρ := Axi.ϱ_ne_zero hy
  have h1 : ctLift c ε (a + 1 / 2) φ x = Real.sqrt (Axi.age ε⁻¹ x.2) * ctLift c ε a φ x := by
    unfold ctLift
    rw [← tsum_mul_left]
    congr 1
    funext n
    rw [Real.sqrt_eq_rpow, Real.rpow_add hpos]
    ring
  rw [h1, Axi.sqrt_age hR hy]
  field_simp

theorem coordT_zero_of_out {φ : Coord → ℝ} (ε : ℝ) {m : Coord} (hm : m ∉ tsupport φ) :
    cpd 1 φ m = 0 ∧ cpd 0 φ m = 0 ∧ cpd 2 φ m = 0 ∧ φ m = 0 := by
  obtain ⟨h0, hd⟩ := zero_of_nmem_tsupport hm
  simp [cpd, h0, hd]

theorem cpd_mul_lin (ℓ : Coord →L[ℝ] ℝ) {φ : Coord → ℝ} (hφ : Differentiable ℝ φ) (j : Fin 3)
    (m : Coord) :
    cpd j (fun y => ℓ y * φ y) m = ℓ m * cpd j φ m + ℓ (cdir j) * φ m := by
  have h : HasFDerivAt (fun y => ℓ y * φ y) (ℓ m • fderiv ℝ φ m + φ m • ℓ) m :=
    ℓ.hasFDerivAt.mul (hφ m).hasFDerivAt
  unfold cpd
  rw [h.fderiv]
  simp
  ring

theorem coordT_eq {φ : Coord → ℝ} (hφ : IsCoordTest φ) (ε : ℝ) (m : Coord) :
    coordTranspose (vQ ε) (dQ ε) φ m =
      -cpd 1 φ m + ε * (2 * m.1 * cpd 0 φ m + m.2.2 * cpd 2 φ m) + 2 * ε * φ m := by
  have hd : Differentiable ℝ φ := hφ.smooth.differentiable (by simp)
  have e0 : (fun y => vQ ε y 0 * φ y) =
      fun y => ((-2 * ε) • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) y * φ y := by
    funext y; simp [vQ]
  have e1 : (fun y => vQ ε y 1 * φ y) = φ := by
    funext y; simp [vQ]
  have e2 : (fun y => vQ ε y 2 * φ y) =
      fun y => ((-ε) • (ContinuousLinearMap.snd ℝ ℝ ℝ).comp
        (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) y * φ y := by
    funext y; simp [vQ]
  unfold coordTranspose
  rw [Fin.sum_univ_three, e0, e1, e2, cpd_mul_lin _ hd, cpd_mul_lin _ hd]
  simp [cdir, dQ]
  ring

theorem coordT_isCoordTest {φ : Coord → ℝ} (hφ : IsCoordTest φ) (ε : ℝ) :
    IsCoordTest (coordTranspose (vQ ε) (dQ ε) φ) := by
  have hcpd : ∀ j : Fin 3, ContDiff ℝ ∞ (cpd j φ) := fun j => by
    unfold cpd
    exact (hφ.smooth.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hform : coordTranspose (vQ ε) (dQ ε) φ = fun m =>
      -cpd 1 φ m + ε * (2 * m.1 * cpd 0 φ m + m.2.2 * cpd 2 φ m) + 2 * ε * φ m :=
    funext (coordT_eq hφ ε)
  have hout : ∀ m, m ∉ tsupport φ → coordTranspose (vQ ε) (dQ ε) φ m = 0 := by
    intro m hm
    obtain ⟨h1, h0, h2, hp⟩ := coordT_zero_of_out ε hm
    rw [coordT_eq hφ ε, h1, h0, h2, hp]; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hform]
    have h0 := hcpd 0
    have h1 := hcpd 1
    have h2 := hcpd 2
    exact (h1.neg.add ((contDiff_const.mul (((contDiff_const.mul contDiff_fst).mul h0).add
      (contDiff_snd.comp contDiff_snd |>.mul h2))))).add (contDiff_const.mul hφ.smooth)
  · exact HasCompactSupport.intro hφ.compact.isCompact (fun m hm => hout m hm)
  · have hsub : tsupport (coordTranspose (vQ ε) (dQ ε) φ) ⊆ tsupport φ := by
      refine closure_minimal ?_ (isClosed_tsupport φ)
      intro m hm
      by_contra hn
      exact hm (hout m hn)
    exact hsub.trans hφ.supp

end UnforcedLeray.Short.IIb.GWQ
