import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.HeatStream.Cpd
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.HeatStream.NiceClosure

/-!
# Part II-b, helper for leaf `PartII-b:T11/3/4` (`HeatConvEq`): the spatial side

Source of record: `the November 2 reference manuscript`, lines 1923-1927.

For `τ = x.1 > 0` the second spatial partial derivatives of the planar heat flow `H = heatStreamH ν ζ`
are the heat flows of `∂_q²ζ` and `∂_η²ζ`. The proof uses only `heatConvCpd` (the first-order
statement, applied to `ζ` and to `∂_qζ`, `∂_ηζ`), `niceStreamClosure`, and the fact that
`cpd 1 H` agrees with `heatStreamH ν (qDer ζ)` on the open slab `{x | 0 < x.1}`, so their Fréchet
derivatives agree at `x` (`Filter.EventuallyEq.fderiv_eq`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.IIb

/-- The open slab `{x : Coord | 0 < x.1}` (the set `τ > 0`). -/
theorem hce_isOpen_pos : IsOpen {x : Coord | 0 < x.1} :=
  isOpen_lt continuous_const continuous_fst

/-- The `q`-derivative of the `q`-derivative of the planar heat flow at `τ > 0`. -/
theorem hce_cpd1_cpd1 {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν) {ζ : ℝ × ℝ → ℝ}
    (hζ : NiceStream c ζ) {x : Coord} (hx : 0 < x.1) :
    cpd 1 (cpd 1 (heatStreamH ν ζ)) x = heatStreamH ν (qDer (qDer ζ)) x := by
  have hnq : NiceStream c (qDer ζ) := (niceStreamClosure c ζ ζ 0 hζ hζ).1
  have hev : cpd 1 (heatStreamH ν ζ) =ᶠ[𝓝 x] heatStreamH ν (qDer ζ) := by
    filter_upwards [hce_isOpen_pos.mem_nhds (show x ∈ {x : Coord | 0 < x.1} from hx)] with y hy
    exact (heatConvCpd c ν ζ hc hν hζ y hy).1
  have hfd : fderiv ℝ (cpd 1 (heatStreamH ν ζ)) x = fderiv ℝ (heatStreamH ν (qDer ζ)) x :=
    hev.fderiv_eq
  have h2 : cpd 1 (heatStreamH ν (qDer ζ)) x = heatStreamH ν (qDer (qDer ζ)) x :=
    (heatConvCpd c ν (qDer ζ) hc hν hnq x hx).1
  calc cpd 1 (cpd 1 (heatStreamH ν ζ)) x
      = fderiv ℝ (cpd 1 (heatStreamH ν ζ)) x (cdir 1) := rfl
    _ = fderiv ℝ (heatStreamH ν (qDer ζ)) x (cdir 1) := by rw [hfd]
    _ = cpd 1 (heatStreamH ν (qDer ζ)) x := rfl
    _ = heatStreamH ν (qDer (qDer ζ)) x := h2

/-- The `η`-derivative of the `η`-derivative of the planar heat flow at `τ > 0`. -/
theorem hce_cpd2_cpd2 {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν) {ζ : ℝ × ℝ → ℝ}
    (hζ : NiceStream c ζ) {x : Coord} (hx : 0 < x.1) :
    cpd 2 (cpd 2 (heatStreamH ν ζ)) x = heatStreamH ν (etaDer (etaDer ζ)) x := by
  have hne : NiceStream c (etaDer ζ) := (niceStreamClosure c ζ ζ 0 hζ hζ).2.1
  have hev : cpd 2 (heatStreamH ν ζ) =ᶠ[𝓝 x] heatStreamH ν (etaDer ζ) := by
    filter_upwards [hce_isOpen_pos.mem_nhds (show x ∈ {x : Coord | 0 < x.1} from hx)] with y hy
    exact (heatConvCpd c ν ζ hc hν hζ y hy).2
  have hfd : fderiv ℝ (cpd 2 (heatStreamH ν ζ)) x = fderiv ℝ (heatStreamH ν (etaDer ζ)) x :=
    hev.fderiv_eq
  have h2 : cpd 2 (heatStreamH ν (etaDer ζ)) x = heatStreamH ν (etaDer (etaDer ζ)) x :=
    (heatConvCpd c ν (etaDer ζ) hc hν hne x hx).2
  calc cpd 2 (cpd 2 (heatStreamH ν ζ)) x
      = fderiv ℝ (cpd 2 (heatStreamH ν ζ)) x (cdir 2) := rfl
    _ = fderiv ℝ (heatStreamH ν (etaDer ζ)) x (cdir 2) := by rw [hfd]
    _ = cpd 2 (heatStreamH ν (etaDer ζ)) x := rfl
    _ = heatStreamH ν (etaDer (etaDer ζ)) x := h2

/-- The spatial side of `HeatConvEq`: `ν (∂_q² + ∂_η²) H = ν (H_{∂_q²ζ} + H_{∂_η²ζ})` at `τ > 0`. -/
theorem hce_spatial_side {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν) {ζ : ℝ × ℝ → ℝ}
    (hζ : NiceStream c ζ) {x : Coord} (hx : 0 < x.1) :
    ν * (cpd 1 (cpd 1 (heatStreamH ν ζ)) x + cpd 2 (cpd 2 (heatStreamH ν ζ)) x) =
      ν * (heatStreamH ν (qDer (qDer ζ)) x + heatStreamH ν (etaDer (etaDer ζ)) x) := by
  rw [hce_cpd1_cpd1 hc hν hζ hx, hce_cpd2_cpd2 hc hν hζ hx]

end UnforcedLeray.Short.IIb
