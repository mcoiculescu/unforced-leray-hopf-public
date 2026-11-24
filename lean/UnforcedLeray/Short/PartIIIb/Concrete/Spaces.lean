import UnforcedLeray.Short.PartIIIa.StressSpaces
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.Normed.Lp.ProdLp

/-!
# Concrete cylinder Banach spaces `H`, `H_T`, `Z_1`, `Z` (source lines 2664-2701)

Genuine Banach spaces (`Lp` over weighted cylinder measures), matching the ENNReal norm
functionals `hNormSq`, `z1NormSq`, `htNormSq`, `zNorm` of `Short/PartIII-a/StressSpaces.lean`.
The ambient value space of `H_T` is all `3×3` tensors (`Ten3`, Frobenius norm); the symmetry
constraint `Sym_3` is a closed linear condition imposed by the operators that use the space.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- `3×3` tensors in the order `(r, φ, z)` with the Frobenius norm. -/
abbrev Ten3 := EuclideanSpace ℝ (Fin 3 × Fin 3)

/-- A function-valued tensor field as a matrix field (source `Sym_3 ⊂ Matrix`). -/
def Ten3.toMatrix (T : Ten3) : Matrix (Fin 3) (Fin 3) ℝ := fun a b => T (a, b)

/-- The cylinder chart space `(s, (q, η))` (source 2666-2668). -/
abbrev Chart := ℝ × (ℝ × ℝ)

/-- The measure `W² · s^{-1/2} dς` of `Z_1` (source 2697): `W = ⟨η/√(1+s)⟩^{m_Z}`. -/
def z1Measure (c mZ : ℝ) : Measure Chart :=
  (ageμ c (-1 / 2)).withDensity fun p => ENNReal.ofReal (UnforcedLeray.Short.IIIa.transWeight mZ p ^ 2)

/-- The measure of `ρ_b^{-1/2} H_T`: `ρ_b^{-1} s^{-1/2} dς` (so that the `L²` norm is
`ρ_b^{-1/2}‖·‖_{H_T}`, source 2698-2700). -/
def htRhoMeasure (c ρb : ℝ) : Measure Chart := ENNReal.ofReal ρb⁻¹ • ageμ c (-1 / 2)

/-- `H = L²(s^{-3/2} dς; ℝ²)` (source 2676-2679). -/
abbrev Hsp (c : ℝ) := Lp (α := Chart) (EuclideanSpace ℝ (Fin 2)) 2 (ageμ c (-3 / 2))

/-- `H_T = L²(s^{-1/2} dς; 3×3)` (source 2676-2679). -/
abbrev HTsp (c : ℝ) := Lp (α := Chart) Ten3 2 (ageμ c (-1 / 2))

/-- `Z_1 = L²(s^{-1/2} W² dς)` (source 2697). -/
abbrev Z1sp (c mZ : ℝ) := Lp (α := Chart) Ten3 2 (z1Measure c mZ)

/-- `ρ_b^{-1/2} H_T`. -/
abbrev HTrho (c ρb : ℝ) := Lp (α := Chart) Ten3 2 (htRhoMeasure c ρb)

instance : Fact ((1 : ℝ≥0∞) ≤ 1) := ⟨le_rfl⟩

/-- `Z = Z_1 ⊕ ρ_b^{-1/2} H_T` with the sum norm `‖T₁‖_{Z_1} + ρ_b^{-1/2}‖T₂‖_{H_T}`
(source 2698-2700). -/
abbrev Zsp (c mZ ρb : ℝ) := WithLp 1 (Z1sp c mZ × HTrho c ρb)

example (c mZ ρb : ℝ) : NormedAddCommGroup (Zsp c mZ ρb) := inferInstance
example (c mZ ρb : ℝ) : NormedSpace ℝ (Zsp c mZ ρb) := inferInstance
example (c mZ ρb : ℝ) : CompleteSpace (Zsp c mZ ρb) := inferInstance
example (c : ℝ) : CompleteSpace (Hsp c) := inferInstance

end UnforcedLeray.Short.PartIIIb.Concrete
