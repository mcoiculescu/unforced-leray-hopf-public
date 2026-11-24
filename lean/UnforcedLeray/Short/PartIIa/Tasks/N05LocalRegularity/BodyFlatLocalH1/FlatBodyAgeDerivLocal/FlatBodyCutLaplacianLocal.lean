import UnforcedLeray.Short.PartIIa.Tasks.N05LocalRegularity.BodyFlatLocalH1.FlatBodyAgeDerivLocal.FlatBodyCutLaplacianLocal.Final
import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.CylHeatMaxReg

/-!
# `PartII-a:N05/2/2/1`: `FlatBodyCutLaplacianLocal`

Source of record: `the November 2 reference manuscript`, lines 1794-1799:
"The flat body graph follows directly by cutting off its heat equation on dyadic intervals
`[a/2,4a]`: the Fourier heat estimate controls `νsΔb`, the equation controls `Sb`, and finite
overlap sums these bounds. Periodic extension over many cells followed by division by their number
gives constants independent of the number of cells."

## Proof

`w = T₀ b = R₀(μ)P₀b`. The weak flat equation of `w` against every smooth periodic band test
(not only solenoidal ones; `R₀` is the componentwise heat flow) is the complex form of the
transpose identity `⟨R₀g, (μ - A₀*)ζ⟩ = ⟨g, ζ⟩` with `ζ = s^{1/2}ψ`
(`FBCLL.r0_transpose_complex`, `FBCLL.weak_cell`). Each component of `u_i = θ(s) w̃_i`
(`θ = 1` on `[σ, H1]`, supported in `(σ/2, 2H1)`, `w̃` the periodic extension) then solves
`(∂_s - νΔ_{q,η}) u_i = f_i = (θ/s)(g̃_i - μw̃_i) + θ' w̃_i` on `ℝ × ℝ²` (`FBCLL.isCylHeat_uCut`).
The cylinder heat estimate `IIb.CylHeatMaxReg` (proved as `IIb.cylHeatMaxReg`: the Euclidean
estimate on a cutoff of `N` cells divided by `N`, "no period loss") gives the weak `∂_q²u_i`,
`∂_η²u_i` with `‖ν∂_j²u_i‖ ≤ C‖f_i‖` in one cell. Back on the cell they are the weak second
derivatives of `w_i` against periodic tests in `[σ, H1]` (`FBCLL.cell_rel`), so
`S_lap = s χ ν(∂_q² + ∂_η²)w` (periodically extended) satisfies the weak identity, and
`‖S_lap‖ ≤ 4C(8 + 6M₀) Γ⁶ ‖b‖` (`FBCLL.flatBodyCutLaplacianLocal_of`). A single age window
`[σ/2, 2H1]` replaces the dyadic windows (the constant may depend on `Γ`).

`cylHeatMaxRegL_of_IIb` identifies the local copy `FBCLL.CylHeatMaxRegL` with
`IIb.CylHeatMaxReg` (the definitions agree; only the test structure is repackaged).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIa

theorem cylHeatMaxRegL_of_IIb (h : UnforcedLeray.Short.IIb.CylHeatMaxReg) :
    FBCLL.CylHeatMaxRegL := by
  intro r hr
  obtain ⟨C, hC, hmain⟩ := h r hr
  refine ⟨C, hC, fun ν c hν hc u f hu hf hum hfm hun hfn hheat => ?_⟩
  have hheat' : UnforcedLeray.Short.IIb.IsCylHeat ν u f := fun φ hφ =>
    hheat φ ⟨hφ.smooth, hφ.compact⟩
  obtain ⟨Dt, D2, h1, h2, h3, h4, h5, h6⟩ := hmain ν c hν hc u f hu hf hum hfm hun hfn hheat'
  exact ⟨Dt, D2, h1, h2, fun φ hφ => h3 φ ⟨hφ.smooth, hφ.compact⟩,
    fun i j φ hφ => h4 i j φ ⟨hφ.smooth, hφ.compact⟩, h5, h6⟩

theorem flatBodyCutLaplacianLocal : UnforcedLeray.Short.PartIIa.FlatBodyCutLaplacianLocal :=
  FBCLL.flatBodyCutLaplacianLocal_of (cylHeatMaxRegL_of_IIb UnforcedLeray.Short.IIb.cylHeatMaxReg)

end UnforcedLeray.Short.PartIIa
