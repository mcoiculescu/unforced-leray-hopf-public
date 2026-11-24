import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_6_3
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PhaseGradient.Sub.L6_1_HRep

/-!
# Decomposition of `SepX0KerInt` (`PartIII-b:C/rep/2/6/3/1`)

Source `the November 2 reference manuscript`
lines 3603-3626 (`sep:kernel`, `sep:resolvent`), 4171-4174.  `X₀ = Re (W_μ - W_{μ+1})`, `sepWHRep`
turns each `W_m` into `kerInt (Gker m)`; the only missing input is the joint integrability of
the `(h,z)`-integrand of `Gker`, from which linearity of the iterated integral gives the claim.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- **Joint integrability of the `Gker` integrand** (source 3611-3621, 3631-3646, 3603-3610):
for `rOut < ϱ y` the function `(h,z) ↦ ∑ Gker ν m h y z i j k · T(τ-h,z) j k` is integrable on
`Ioi 0 × Space`.  Proof idea: `|Gker| ≤ e^{-(Re m+3/2)h}·|∇K_t(y - e^{-h/2}z)|`, kernel bound
`SepKernelBounds` (uniform in `t > 0`, `|x|^{-4}`) with `|y - e^{-h/2}z| ≥ ϱ y - rOut` on the
support of `T`, plus `SepMoment` (`L²_τ L²_z`) and periodicity of `T` in `τ`. -/
def GkerIntegrable : Prop :=
  ∀ (ν : ℝ) (m : ℂ), 0 < ν → -(1 / 4) < m.re → ∀ (rOut P : ℝ), 0 ≤ rOut → 0 < P →
    ∀ (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ), IIIa.IsSepSource P rOut T → SepMoment P T →
      ∀ (τ : ℝ) (y : Space), rOut < ϱ y → ∀ i : Fin 3,
        Integrable (fun p : ℝ × Space => ∑ j : Fin 3, ∑ k : Fin 3,
          Gker ν m p.1 y p.2 i j k * ((T (τ - p.1) p.2 j k : ℝ) : ℂ))
          ((volume.restrict (Ioi (0 : ℝ))).prod volume)

/-- Linearity of `kerInt` in the kernel, given joint integrability of both integrands. -/
theorem kerInt_sub_of_integrable (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (Φ Ψ : ℝ → Space → Space → Fin 3 → Fin 3 → Fin 3 → ℂ) (τ : ℝ) (y : Space) (i : Fin 3)
    (hΦ : Integrable (fun p : ℝ × Space => ∑ j : Fin 3, ∑ k : Fin 3,
      Φ p.1 y p.2 i j k * ((T (τ - p.1) p.2 j k : ℝ) : ℂ))
      ((volume.restrict (Ioi (0 : ℝ))).prod volume))
    (hΨ : Integrable (fun p : ℝ × Space => ∑ j : Fin 3, ∑ k : Fin 3,
      Ψ p.1 y p.2 i j k * ((T (τ - p.1) p.2 j k : ℝ) : ℂ))
      ((volume.restrict (Ioi (0 : ℝ))).prod volume)) :
    kerInt T (fun h y z i j k => Φ h y z i j k - Ψ h y z i j k) τ y i =
      kerInt T Φ τ y i - kerInt T Ψ τ y i := by
  have hpt : (fun p : ℝ × Space => ∑ j : Fin 3, ∑ k : Fin 3,
      (Φ p.1 y p.2 i j k - Ψ p.1 y p.2 i j k) * ((T (τ - p.1) p.2 j k : ℝ) : ℂ)) =
      (fun p : ℝ × Space => ∑ j : Fin 3, ∑ k : Fin 3,
        Φ p.1 y p.2 i j k * ((T (τ - p.1) p.2 j k : ℝ) : ℂ)) -
      (fun p : ℝ × Space => ∑ j : Fin 3, ∑ k : Fin 3,
        Ψ p.1 y p.2 i j k * ((T (τ - p.1) p.2 j k : ℝ) : ℂ)) := by
    funext p
    simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  have e1 := integral_prod _ hΦ
  have e2 := integral_prod _ hΨ
  have e3 := integral_prod _ (hpt ▸ hΦ.sub hΨ)
  unfold kerInt
  simp only [] at e1 e2 e3
  rw [← e1, ← e2]
  have e4 : (∫ p : ℝ × Space, ∑ j : Fin 3, ∑ k : Fin 3,
      (Φ p.1 y p.2 i j k - Ψ p.1 y p.2 i j k) * ((T (τ - p.1) p.2 j k : ℝ) : ℂ)
      ∂((volume.restrict (Ioi (0 : ℝ))).prod volume)) =
      (∫ p : ℝ × Space, ∑ j : Fin 3, ∑ k : Fin 3,
        Φ p.1 y p.2 i j k * ((T (τ - p.1) p.2 j k : ℝ) : ℂ)
        ∂((volume.restrict (Ioi (0 : ℝ))).prod volume)) -
      (∫ p : ℝ × Space, ∑ j : Fin 3, ∑ k : Fin 3,
        Ψ p.1 y p.2 i j k * ((T (τ - p.1) p.2 j k : ℝ) : ℂ)
        ∂((volume.restrict (Ioi (0 : ℝ))).prod volume)) := by
    rw [hpt]; exact integral_sub hΦ hΨ
  rw [← e3, e4]
  ring

/-- `SepX0KerInt` from the joint integrability of the `Gker` integrand and `sepWHRep`. -/
theorem sepX0KerInt_of (hG : GkerIntegrable) (hR : SepWHRep) : SepX0KerInt := by
  intro ν μ rOut P T hD τ y hy
  obtain ⟨hν, hμ, hr, hP, hT, hM⟩ := hD
  have hμ' : -(1 / 4) < ((μ : ℂ)).re := by simpa using hμ
  have hμ1 : -(1 / 4) < ((μ : ℂ) + 1).re := by simp; linarith
  have i1 := hG ν (μ : ℂ) hν hμ' rOut P hr hP T hT hM τ y hy
  have i2 := hG ν ((μ : ℂ) + 1) hν hμ1 rOut P hr hP T hT hM τ y hy
  ext i
  have := kerInt_sub_of_integrable T (Gker ν (μ : ℂ)) (Gker ν ((μ : ℂ) + 1)) τ y i (i1 i) (i2 i)
  show (IIIa.sepW ν (μ : ℂ) T y τ i - IIIa.sepW ν ((μ : ℂ) + 1) T y τ i).re =
    (kerInt T (Kd ν μ) τ y i).re
  rw [hR ν (μ : ℂ) rOut P hν hμ' hr hP T hT hM τ y i,
    hR ν ((μ : ℂ) + 1) rOut P hν hμ1 hr hP T hT hM τ y i]
  congr 1
  exact this.symm

end UnforcedLeray.Short.PartIIIb.Concrete
