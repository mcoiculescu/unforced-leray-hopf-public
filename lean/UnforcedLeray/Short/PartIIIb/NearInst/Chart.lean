import UnforcedLeray.Short.PartIIIb.Concrete.Spaces
import UnforcedLeray.Short.PartIIIa.FlatCausal
import UnforcedLeray.Short.PartIIIa.SeparatedKernels
import UnforcedLeray.Short.PartIIa.StatementsNear

/-!
# Chart dictionary for the near operators (source 1638-1690, 2664-2701, 3405-3424, 3611-3621, 3866-3920)

Pointwise objects used to pin the near operators of `NearInst.lean` to their source definitions.

* `zsum F` : the sum `T₁ + T₂` of the two components of `F ∈ Z` (source 3874, 2700: "The stress
  inverse always acts on the sum of the components").
* `nsSym T` : the symmetric axisymmetric-without-swirl part of a `3×3` tensor in the order
  `(r, φ, z)`: entries `rr, zz, φφ`, the symmetrised `rz = zr`, and zero for every component with
  exactly one azimuthal index (source 1645-1646, 2675: `H_T` is `Sym_3`-valued and tensors have no
  component with exactly one azimuthal index).  The ambient space `Ten3` of `Concrete/Spaces.lean`
  is all of `3×3`; the near operators act through this part, which is the identity on the source's
  tensor class.
* `merBlockC T` : the planar (meridional) block of `nsSym T` for the flat equations, planar indices
  `(0, 1) = (q, η) ↔ (r, z)` (source 3569-3571: "these flat maps act on its meridional block").
* `tv4`, `merC`, `cellPt` : the dictionary to the complex spaces of `PartII-a/StatementsNear.lean`
  (`HTSpace c` with components `(T_rr, T_rz, T_zz, T_φφ)`, `HSpace c MeridC`, cell `q ∈ (0, c]`,
  unnormalised `dq`), in which the curved and flat free inverses `S_ε`, `S_0`, `T_ε`, `T_0` of
  `near/free-comparison.tex` are defined.  `cellPt c` recentres `q ∈ (0, c]` onto the cell
  `q ∈ [-c/2, c/2)` of `Concrete/Spaces.lean`.
* `chartOf`, `cylFrame`, `cartLift` : the Cartesian lift `𝒩_T T = sT` of a chart tensor to the
  similarity variables `(z, τ)` (source 2666-2668, 2683), in Cartesian components.
* `chartY`, `chartTau`, `merRe` : the chart point `(s, q, η) ↦ (y, τ)` with `y = (R/√s, 0, η/√s)`,
  `τ = 2q/R + log s` (inverse chart, as in `IIIa.chartCoeff`) and the meridional real part of a
  Cartesian velocity on the half plane `φ = 0`.
* `sepWfar` : the kernel realization of the masked response (source 3905-3912): `sep:resolvent`
  (`IIIa.sepW`, source 3621, `W_μ = -S_μ T`) with the tensor at input age `t = R²/|z'|²` kept
  only for `t > e^δ s`, `s` the output age; the mask is applied to the tensor before the
  divergence ("tensor partitions before distributional divergence").
* `IsBoxTensor` : the dense class of bounded measurable chart tensors with compact age support in
  `(0, ∞)` and bounded transverse support, on which the kernel formula is pinned.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst

open UnforcedLeray.Short.PartIIIb.Concrete

/-! ## Tensor components -/

/-- The meridional indices `r ↦ 0`, `z ↦ 2` in the order `(r, φ, z)`. -/
def merIdx : Fin 2 → Fin 3 := ![0, 2]

/-- A `3×3` matrix as an element of `Ten3`. -/
def ten3Of (M : Matrix (Fin 3) (Fin 3) ℝ) : Ten3 := WithLp.toLp 2 fun ab => M ab.1 ab.2

/-- The symmetrised `rz` entry `(T_rz + T_zr)/2`. -/
def symRZ (T : Ten3) : ℝ := (T (0, 2) + T (2, 0)) / 2

/-- The symmetric axisymmetric-without-swirl part of `T` (source 1645-1646, 2675):
`rr, zz, φφ` kept, `rz = zr` symmetrised, the components with one azimuthal index removed. -/
def nsSym (T : Ten3) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![T (0, 0), 0, symRZ T; 0, T (1, 1), 0; symRZ T, 0, T (2, 2)]

/-- The sum `T₁ + T₂` of the two components of `F ∈ Z = Z₁ ⊕ ρ_b^{-1/2} H_T` (source 2700, 3874). -/
def zsum {c mZ ρb : ℝ} (F : Zsp c mZ ρb) : Chart → Ten3 :=
  fun p => (F.fst : Chart → Ten3) p + (F.snd : Chart → Ten3) p

/-- The planar meridional block of `nsSym T`, complexified, as the tensor input of the flat
equation `IIIa.IsCausalEnergySolution` (planar order `(q, η) ↔ (r, z)`, source 3424, 3569-3571). -/
def merBlockC (T : Chart → Ten3) : Chart → Fin 2 → Fin 2 → ℂ :=
  fun p i j => ((nsSym (T p) (merIdx i) (merIdx j) : ℝ) : ℂ)

/-- A meridional velocity field, complexified, in the format of `IIIa.IsCausalEnergySolution`. -/
def velC (b : Chart → Merid) : Chart → Fin 2 → ℂ := fun p i => ((b p i : ℝ) : ℂ)

/-! ## Dictionary to the complex spaces of `PartII-a/StatementsNear.lean` -/

/-- The components `(T_rr, T_rz, T_zz, T_φφ)` (`PartIIa.TensorVal`) of `nsSym T`. -/
def tv4 (T : Ten3) : UnforcedLeray.Short.PartIIa.TensorVal :=
  WithLp.toLp 2 ![((T (0, 0) : ℝ) : ℂ), ((symRZ T : ℝ) : ℂ), ((T (2, 2) : ℝ) : ℂ),
    ((T (1, 1) : ℝ) : ℂ)]

/-- A real meridional vector as a complex one (`B0223.MeridC`). -/
def merC (b : Merid) : UnforcedLeray.B0223.MeridC := WithLp.toLp 2 fun i => ((b i : ℝ) : ℂ)

/-- Recentring of the `PartII-a` cell `q ∈ (0, c]` onto the cell `q ∈ [-c/2, c/2)` of
`Concrete/Spaces.lean` (the fields are `c`-periodic in `q`, source 2667). -/
def cellPt (c : ℝ) (p : UnforcedLeray.B0220.Profile) : Chart :=
  (p.1, (if p.2.1 < c / 2 then p.2.1 else p.2.1 - c, p.2.2))

/-! ## The Cartesian lift and the masked kernel -/

/-- The horizontal radius `ϱ = |z'|` of a Cartesian similarity point. -/
def hRad (z : Space) : ℝ := Real.sqrt (z 0 ^ 2 + z 1 ^ 2)

/-- The chart point of `(z, τ)`: `s = R²/ϱ²`, `q = R log(ϱ/R) + Rτ/2` reduced into `[-c/2, c/2)`,
`η = R z₃/ϱ` (source 2666-2668). -/
def chartOf (R c : ℝ) (z : Space) (τ : ℝ) : Chart :=
  (R ^ 2 / hRad z ^ 2,
    (R * Real.log (hRad z / R) + R * τ / 2 - c * ⌊(R * Real.log (hRad z / R) + R * τ / 2) / c + 1 / 2⌋,
      R * z 2 / hRad z))

/-- The cylindrical frame at the azimuth of `z`: columns `e_r, e_φ, e_z` in Cartesian components. -/
def cylFrame (z : Space) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![z 0 / hRad z, -(z 1 / hRad z), 0; z 1 / hRad z, z 0 / hRad z, 0; 0, 0, 1]

/-- The physical tensor `𝒩_T T = sT` (source 2683) of the chart tensor field `T`, at the
similarity point `(z, τ)`, in Cartesian components (axisymmetric, no swirl: `nsSym`). -/
def cartLift (R c : ℝ) (T : Chart → Ten3) (τ : ℝ) (z : Space) : Matrix (Fin 3) (Fin 3) ℝ :=
  cylFrame z * ((chartOf R c z τ).1 • nsSym (T (chartOf R c z τ))) * (cylFrame z).transpose

/-- The similarity point `y = (R/√s, 0, η/√s)` of the chart point `(s, (q, η))` (azimuth `φ = 0`). -/
def chartY (R : ℝ) (p : Chart) : Space :=
  WithLp.toLp 2 ![R / Real.sqrt p.1, 0, p.2.2 / Real.sqrt p.1]

/-- The phase `τ = 2q/R + log s` of the chart point `(s, (q, η))`. -/
def chartTau (R : ℝ) (p : Chart) : ℝ := 2 * p.2.1 / R + Real.log p.1

/-- The meridional components `(w_r, w_z) = (Re w₀, Re w₂)` of a Cartesian velocity at `φ = 0`. -/
def merRe (w : Fin 3 → ℂ) : Merid := WithLp.toLp 2 ![(w 0).re, (w 2).re]

/-- The masked negative response (source 3905-3912 with `sep:resolvent`, 3621): the tensor at
input age `t = R²/|z'|²` is kept only for `t > e^δ s`, `s` the output age, before the divergence. -/
def sepWfar (ν : ℝ) (μ : ℂ) (R δ s : ℝ) (T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ)
    (y : Space) (τ : ℝ) : Fin 3 → ℂ :=
  UnforcedLeray.Short.IIIa.sepW ν μ
    (fun τ' z => if Real.exp δ * s < R ^ 2 / (z 0 ^ 2 + z 1 ^ 2) then T τ' z else 0) y τ

/-- The dense class of the kernel pins: a measurable chart tensor, bounded, supported in a band
`s₁ ≤ s ≤ s₂` with `0 < s₁`, `|η| ≤ L`. -/
structure IsBoxTensor (f : Chart → Ten3) : Prop where
  measurable : Measurable f
  bounded : ∃ B : ℝ, ∀ p, ‖f p‖ ≤ B
  band : ∃ s₁ s₂ L : ℝ, 0 < s₁ ∧ ∀ p, f p ≠ 0 → s₁ ≤ p.1 ∧ p.1 ≤ s₂ ∧ |p.2.2| ≤ L

/-! ## The flat train as a meridional coefficient -/

/-- The actual planar train `v` (`B0140.TrainSol`, `IIIa.trainVel`) as a meridional coefficient on
the chart, planar `(q, η) ↔ (r, z)` (source 3871-3872, 2763). -/
def trainMer {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) (p : Chart) : Merid :=
  WithLp.toLp 2 fun i => UnforcedLeray.Short.IIIa.trainVel tr p.1 p.2 i

end UnforcedLeray.Short.PartIIIb.NearInst
