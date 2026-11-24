import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1.Homog
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1.FarOrg

/-!
# `PhaseJet` (organizer task `PartIII-b:C/ward/12/3/1/2/5/1/1/3/1/1/1/3`)

Source `the November 2 reference manuscript`,
lines 1208-1210: `q = R log(r/R)`. The phase is `Axi.phase R τ y = Rτ/2 - (R/2) log (age R y)`.
Its `τ`-dependence is an additive constant, so the jets are those of `Axi.phase R 0`, which is
homogeneous of degree `0` up to the additive term `R log λ` (`homogJets`, `d = 0`).
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem phaseJet : PhaseJet := by
  intro R hR m hm
  have hR0 : R ≠ 0 := hR.ne'
  have hA : ContDiffOn ℝ ∞ (fun y : UnforcedLeray.Space => R ^ 2 / Axi.ϱ y ^ 2) Axi.axisᶜ :=
    contDiffOn_const.div (Axi.contDiffOn_ϱ.pow 2)
      (fun y hy => pow_ne_zero 2 (Axi.ϱ_ne_zero hy))
  have hf : ContDiffOn ℝ ∞ (Axi.phase R 0) Axi.axisᶜ := by
    have hL : ContDiffOn ℝ ∞ (fun y : UnforcedLeray.Space => Real.log (Axi.age R y)) Axi.axisᶜ :=
      ContDiffOn.log hA (fun y hy => (Axi.age_pos hR0 hy).ne')
    have hphase : ContDiffOn ℝ ∞
        (fun y : UnforcedLeray.Space => R * 0 / 2 - (R / 2) * Real.log (Axi.age R y)) Axi.axisᶜ :=
      contDiffOn_const.sub (contDiffOn_const.mul hL)
    exact hphase
  have hinv : ∀ y : UnforcedLeray.Space, y ∉ Axi.axis → ∀ t : ℝ,
      Axi.phase R 0 (y + t • Axi.e3) = Axi.phase R 0 y := by
    intro y hy t
    have hϱ : Axi.ϱ (y + t • Axi.e3) = Axi.ϱ y := by
      unfold Axi.ϱ
      simp [Axi.e3_apply]
    unfold Axi.phase Axi.age
    rw [hϱ]
  have hscale : ∀ lam : ℝ, 0 < lam → ∀ z : UnforcedLeray.Space, z ∉ Axi.axis →
      Axi.phase R 0 (lam • z) = lam ^ (0 : ℝ) • Axi.phase R 0 z + R * Real.log lam := by
    intro lam hlam z hz
    have hz0 : Axi.ϱ z ≠ 0 := Axi.ϱ_ne_zero hz
    have hage : Axi.age R (lam • z) = Axi.age R z / lam ^ 2 := by
      unfold Axi.age
      rw [Axi.ϱ_smul, abs_of_pos hlam, mul_pow]
      field_simp
    have hagepos : Axi.age R z ≠ 0 := (Axi.age_pos hR0 hz).ne'
    unfold Axi.phase
    rw [hage, Real.log_div hagepos (pow_ne_zero 2 hlam.ne'), Real.log_pow, Real.rpow_zero,
      smul_eq_mul, one_mul]
    push_cast
    ring
  obtain ⟨C, hC0, hCb⟩ :=
    homogJets ℝ (Axi.phase R 0) 0 (fun lam => R * Real.log lam) hf hinv hscale m hm
  refine ⟨C, hC0, fun τ y hy => ?_⟩
  have hfun : Axi.phase R τ = fun y => Axi.phase R 0 y + R * τ / 2 := by
    funext y
    unfold Axi.phase
    ring
  have hm0 : m ≠ 0 := by omega
  have hder : iteratedFDeriv ℝ m (Axi.phase R τ) y = iteratedFDeriv ℝ m (Axi.phase R 0) y := by
    have hAt : ContDiffAt ℝ m (Axi.phase R 0) y :=
      (hf.contDiffAt (Axi.isOpen_compl_axis.mem_nhds hy)).of_le (hjLe m)
    have hc : iteratedFDeriv ℝ m (fun _ : UnforcedLeray.Space => R * τ / 2) y = 0 := by
      rw [iteratedFDeriv_const_of_ne hm0]
      rfl
    rw [hfun, show (fun y : UnforcedLeray.Space => Axi.phase R 0 y + R * τ / 2) =
      Axi.phase R 0 + (fun _ : UnforcedLeray.Space => R * τ / 2) from rfl,
      iteratedFDeriv_add_apply hAt contDiffAt_const, hc, add_zero]
  have h := hCb y hy
  rw [← hder, zero_sub] at h
  exact h

end UnforcedLeray.Short.PartIIIb.Concrete
