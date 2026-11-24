import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.HeatExists.LeavesOf
import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.HeatExists.H6.FluxPairDuhamel

/-!
# Part III-a, `PartIII-a:T21/2/7/1/8/5/2`: the time identity of the smoothed tests (`AdjHeatS0Time`)

Source of record: `the November 2 reference manuscript` (SP), lines 2819-2836
and 3044-3050. The Duhamel identity `AdjFluxPairDuhamel` at the flux `y = (0, w)` (the zero flux
contributes nothing, since `⇑(0 : AdjX c m) = 0` almost everywhere on the cell), followed by the
substitution `η = ν r`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The flux pairing of a zero flux is the pairing of the source alone. -/
theorem adjS0Time_fluxPair_zero {c m : ℝ} (w : AdjX c m) (φ : ℝ × ℝ → ℝ) :
    adjFluxPair ((0 : Fin 2 → AdjX c m), w) φ = ∫ x in B0579.cell c, w x * (φ x : ℂ) := by
  have hae0 : ∀ᵐ x ∂(B0579.cellMeasure c (-m)), ⇑(0 : AdjX c m) x = 0 :=
    Lp.coeFn_zero ℂ 2 (B0579.cellMeasure c (-m))
  have hae : ∀ᵐ x ∂(volume.restrict (B0579.cell c)), ⇑(0 : AdjX c m) x = 0 :=
    (B0579.ac_cellMeasure c (-m)).ae_le hae0
  have hz : ∀ g : ℝ × ℝ → ℝ, ∫ x in B0579.cell c, ⇑(0 : AdjX c m) x * (g x : ℂ) = 0 := by
    intro g
    have hcongr : (fun x => ⇑(0 : AdjX c m) x * (g x : ℂ)) =ᵐ[volume.restrict (B0579.cell c)]
        fun _ => (0 : ℂ) := by
      filter_upwards [hae] with x hx
      simp only [hx, zero_mul]
    rw [integral_congr_ae hcongr]
    simp
  unfold adjFluxPair
  simp only [Pi.zero_apply, hz, zero_add]

/-- The substitution `η = ν r` in the time integral. -/
theorem adjS0Time_scale (G : ℝ → ℂ) (ν τ : ℝ) :
    ∫ η in (0 : ℝ)..(ν * τ), G η = ∫ r in (0 : ℝ)..τ, (ν : ℂ) * G (ν * r) := by
  have h1 := intervalIntegral.smul_integral_comp_mul_left (a := (0 : ℝ)) (b := τ) (f := G) ν
  rw [mul_zero, Complex.real_smul] at h1
  rw [intervalIntegral.integral_const_mul]
  exact h1.symm

/-- **(H5.2) The time identity of the smoothed tests** (SP 2819-2836):
`∫ f P_{ντ}ψ = ∫ f ψ + ν ∫_0^τ ∫ f P_{νr}Δψ dr` for `f ∈ X_{-m,c}`, `τ ∈ (0, 1]`
(`AdjFluxPairDuhamel` at `y = (0, f)`, `θ = ντ`, and the substitution `η = νr`). -/
theorem adjHeatS0Time (m : ℝ) (hm : 8 < m) : AdjHeatS0Time m := by
  intro ν c hν hc w ψ hψ τ hτ
  have hθ : (0 : ℝ) ≤ ν * τ := (mul_pos hν hτ.1).le
  have h := adjFluxPairDuhamel m hm c hc ((0 : Fin 2 → AdjX c m), w) ψ hψ (ν * τ) hθ
  simp only [adjS0Time_fluxPair_zero] at h
  have key := adjS0Time_scale
    (fun η => ∫ x in B0579.cell c, w x * (Exist.cylHeatSmooth c η (lapP ψ) x : ℂ)) ν τ
  beta_reduce at key
  rw [h, key]

end UnforcedLeray.Short.IIIa
