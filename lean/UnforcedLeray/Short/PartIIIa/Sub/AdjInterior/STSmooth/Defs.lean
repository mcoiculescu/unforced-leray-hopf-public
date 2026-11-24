import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.Defs
import UnforcedLeray.Lib.Sobolev.Space

/-!
# `PartIII-a:T21/2/7/2/1/1/8`: Sobolev embedding on an open set of space-time (vocabulary)

Source of record: `the November 2 reference manuscript` (SP), lines 3060-3061 (the
space-time smoothness of the reverse-time adjoint: a `C^∞` version of an `H^∞_loc` function).
Manuscript-independent generic Sobolev embedding `H^∞_loc(U) ⊂ C^∞(U)` for `U ⊆ ℝ × ℝ²` open.

## Route (`STSobolevSmoothRep`, `Sub/AdjInterior/Defs.lean`)

1. `STCutoffGlobal`: a `C_c^∞(U)` cutoff `ζ` of `F ∈ H^∞_loc(U)` is in `H^∞(ℝ × ℝ²)` (word Leibniz
   rule, extension by zero from `U`; `Lib/SobolevB/Leibniz.lean` is the `Eucl n` version);
2. `STGlobalEmbedding`: `H^∞(ℝ × ℝ²)` has `C^k` versions for every `k`: transfer along
   `toSpace : Eucl 3 ≃L ℝ × (ℝ × ℝ)` (`STGlobalToEucl`), then `EuclGlobalEmbedding`
   (`Sob.W.ofFields`, `Sob.W.exists_contDiff_rep`, `n = 3`);
3. `STLocalSmoothOfSob`: on a small ball `B ⋐ U` (`ζ = 1` on `B`, `ContDiffBump`), the `C^k`
   versions of `ζF` agree on `B` (continuous, a.e. equal), so one function is `C^k` on `B` for every
   `k`, i.e. `C^∞`, and equals `F` a.e.;
4. `STGlueLocal`: local `C^∞` versions on a countable cover by balls glue (`Nat.find` over a
   Lindelöf subcover; continuous functions a.e. equal on an open set agree there).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Metric
open scoped ContDiff

namespace UnforcedLeray.Short.IIIa

open UnforcedLeray.Sob

/-- Space-time `ℝ × ℝ²`. -/
abbrev STSpace : Type := ℝ × (ℝ × ℝ)

/-- The linear equivalence `Eucl 3 ≃L ℝ × (ℝ × ℝ)`, `y ↦ (y 0, (y 1, y 2))`. -/
def toSpace : Eucl 3 ≃L[ℝ] STSpace :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun y => (y 0, (y 1, y 2))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun p => (WithLp.toLp 2 ![p.1, p.2.1, p.2.2] : Eucl 3)
      left_inv := fun y => by
        ext i; fin_cases i <;> rfl
      right_inv := fun p => rfl }

/-- **`f ∈ H^∞(ℝ × ℝ²)`**: `f ∈ L²` and every weak derivative along every word in the coordinate
directions `stDir` (tests `C_c^∞(ℝ × ℝ²)`) lies in `L²`. -/
def IsSTSobolevGlobal (f : STSpace → ℂ) : Prop :=
  MemLp f 2 volume ∧ ∀ l : List (Fin 3), ∃ g : STSpace → ℂ, MemLp g 2 volume ∧
    HasWeakDeriv (wholeSpaceOf STSpace volume stDir) (l.map stDir) f g

/-- **`f ∈ H^∞(ℝ³)`** (`Eucl 3`, coordinate directions `e`). -/
def IsEuclSobolevGlobal (f : Eucl 3 → ℂ) : Prop :=
  MemLp f 2 volume ∧ ∀ l : List (Fin 3), ∃ g : Eucl 3 → ℂ, MemLp g 2 volume ∧
    HasWeakDeriv (wholeSpace 3) (l.map e) f g

/-- **(1) Cutoffs of `H^∞_loc(U)` are in `H^∞(ℝ × ℝ²)`**: `ζ ∈ C_c^∞`, `tsupport ζ ⊆ U`.  The weak
derivatives of `ζF` for the tests of `ℝ × ℝ²` are the Leibniz sums of the `L²_loc(U)` weak
derivatives of `F` against derivatives of `ζ` (word Leibniz rule; a test `φ` of `ℝ × ℝ²` is
replaced by `φχ ∈ C_c^∞(U)` with `χ = 1` near `tsupport ζ`). -/
def STCutoffGlobal : Prop :=
  ∀ (U : Set STSpace) (hU : IsOpen U) (F : STSpace → ℂ), IsSTSobolevLoc U hU F →
    ∀ ζ : STSpace → ℝ, ContDiff ℝ ∞ ζ → HasCompactSupport ζ → tsupport ζ ⊆ U →
      IsSTSobolevGlobal (fun p => ζ p • F p)

/-- **(2a) Transfer to `ℝ³`**: `f ∘ toSpace ∈ H^∞(ℝ³)` (measure-preserving linear equivalence;
`stDir ↦ e` under `toSpace.symm`, cf. `Sob.hasWeakDeriv_comp_toPlane`). -/
def STGlobalToEucl : Prop :=
  ∀ f : STSpace → ℂ, IsSTSobolevGlobal f → IsEuclSobolevGlobal (fun y => f (toSpace y))

/-- **(2b) `H^∞(ℝ³) ⊂ C^k` for every `k`**: `Sob.W.ofFields` from the fields `g l` (`l` a word of
length `≤ k + 2`) and `Sob.W.exists_contDiff_rep` with `n = 3`. -/
def EuclGlobalEmbedding : Prop :=
  ∀ f : Eucl 3 → ℂ, IsEuclSobolevGlobal f → ∀ k : ℕ,
    ∃ G : Eucl 3 → ℂ, ContDiff ℝ k G ∧ G =ᵐ[volume] f

/-- **(2) `H^∞(ℝ × ℝ²) ⊂ C^k` for every `k`** (from `STGlobalToEucl` and `EuclGlobalEmbedding`,
transporting a.e. equality along the measure-preserving `toSpace`). -/
def STGlobalEmbedding : Prop :=
  ∀ f : STSpace → ℂ, IsSTSobolevGlobal f → ∀ k : ℕ,
    ∃ G : STSpace → ℂ, ContDiff ℝ k G ∧ G =ᵐ[volume] f

/-- **A local `C^∞` version of `F` near every point of `U`**: a ball `B ⊆ U` around `p` and a
function `C^∞` on `B` and a.e. equal to `F` on `B`. -/
def STLocalSmooth (U : Set STSpace) (F : STSpace → ℂ) : Prop :=
  ∀ p ∈ U, ∃ r : ℝ, 0 < r ∧ ball p r ⊆ U ∧ ∃ G : STSpace → ℂ,
    ContDiffOn ℝ ∞ G (ball p r) ∧ ∀ᵐ q ∂volume, q ∈ ball p r → G q = F q

/-- **(3) Local smooth versions of `H^∞_loc(U)`** (from `STCutoffGlobal` and `STGlobalEmbedding`):
take `ζ ∈ C_c^∞(U)` (`ContDiffBump`) with `ζ = 1` on a ball `B = ball p r` with
`closedBall p (2r) ⊆ U`; for each `k` the `C^k` version `G_k` of `ζF` satisfies `G_k = F` a.e. on
`B`; two continuous functions a.e. equal on the open `B` agree on `B` (`Measure.eqOn_open_of_ae_eq`),
so `G_0 = G_k` on `B` and `G_0` is `C^k` on `B` for every `k` (`contDiffOn_infty`). -/
def STLocalSmoothOfSob : Prop :=
  ∀ (U : Set STSpace) (hU : IsOpen U) (F : STSpace → ℂ), IsSTSobolevLoc U hU F → STLocalSmooth U F

/-- **(4) Gluing of local versions** (`Nat.find` over a countable subcover by balls: `U` is
Lindelöf; on an overlap two continuous functions a.e. equal to `F` agree). -/
def STGlueLocal : Prop :=
  ∀ (U : Set STSpace) (_hU : IsOpen U) (F : STSpace → ℂ), STLocalSmooth U F →
    ∃ F' : STSpace → ℂ, ContDiffOn ℝ ∞ F' U ∧ ∀ᵐ p ∂volume, p ∈ U → F' p = F p

end UnforcedLeray.Short.IIIa
