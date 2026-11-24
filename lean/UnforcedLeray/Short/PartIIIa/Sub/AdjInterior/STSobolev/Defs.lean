import UnforcedLeray.Short.PartIIIa.Sub.AdjInterior.Defs
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_2_7_2_1_1_9

/-!
# `PartIII-a:T21/2/7/2/1/1/7`: space-time Sobolev regularity from the time jets (vocabulary, leaves)

Source of record: `the November 2 reference manuscript` (SP), lines 3060-3061 (the
smoothness used by the energies: `∂_r^j ∂_x^w φ ∈ C(I; X_{-m,c})`).

## The route (target `TimeJetsSTSobolev`)

1. `CohJetsExists`: coherent derivative fields `D j r w` of the jets (the fields of the cell jets of
   `Φ j r` for all orders, independent of the order `k`), by uniqueness of cell weak derivatives
   (`CellWeakUnique`).
2. Jointly measurable versions `G j w` of `(r, x) ↦ D j r w x`, equal to the slice for EVERY `r`
   (`MeasPathVersion` for the cell measure, then `MeasPlaneVersion` for Lebesgue measure).
3. `STLocL2Of`: `G j w ∈ L²_loc((t, s) × ℝ²)`.
4. One-letter integral identities: `STSpaceIdentity` (from `SliceIBP`, `PerTestCyl`,
   `PerTestUnfold`) and `STTimeIdentity` (from `PairBound`, `PairDeriv`).
5. The assembly `timeJetsSTSobolev_of` (`Assembly.lean`) chains the letters by
   `Sob.HasWeakDeriv.append`, `.perm`, `.of_append`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- `g` is `c`-periodic in the first variable. -/
def Periodic1 (c : ℝ) (g : ℝ × ℝ → ℂ) : Prop := ∀ x : ℝ × ℝ, g (x.1 + c, x.2) = g x

/-- The space-time slab `(t, s) × ℝ²`. -/
abbrev stSlab (t s : ℝ) : Set (ℝ × (ℝ × ℝ)) := Ioo t s ×ˢ univ

/-- `G ∈ L²_loc((t, s) × ℝ²)`: `L²` on every compact subset of the slab. -/
def STLocL2 (t s : ℝ) (G : ℝ × (ℝ × ℝ) → ℂ) : Prop :=
  ∀ K : Set (ℝ × (ℝ × ℝ)), IsCompact K → K ⊆ stSlab t s → MemLp G 2 (volume.restrict K)

/-- The one-letter weak-derivative identity on `U`, as plain integrals over space-time:
`∫ (∂_v Ψ) G = -∫ Ψ G'` for every `Ψ ∈ C_c^∞` with `tsupport Ψ ⊆ U`, with integrable integrands. -/
def STStepIdentity (U : Set (ℝ × (ℝ × ℝ))) (v : ℝ × (ℝ × ℝ)) (G G' : ℝ × (ℝ × ℝ) → ℂ) : Prop :=
  ∀ Ψ : ℝ × (ℝ × ℝ) → ℝ, ContDiff ℝ ∞ Ψ → HasCompactSupport Ψ → tsupport Ψ ⊆ U →
    Integrable (fun p => fderiv ℝ Ψ p v • G p) ∧ Integrable (fun p => Ψ p • G' p) ∧
      ∫ p, fderiv ℝ Ψ p v • G p = -∫ p, Ψ p • G' p

/-- The periodization `Σ_k θ(x₁ + kc, x₂)` of a compactly supported function in the first
variable (a locally finite sum). -/
def perTest (c : ℝ) (θ : ℝ × ℝ → ℝ) (x : ℝ × ℝ) : ℝ := ∑ᶠ k : ℤ, θ (x.1 + (k : ℝ) * c, x.2)

/-! ## Coherent jets -/

/-- Coherent derivative fields `D j r w` of the time jets `Φ j r` on `I`: every `D j r` is a cell
jet of `Φ j r` of every order, and every field is continuous into `X_{-m,c}` within `I`. -/
structure CohJets (c m : ℝ) (I : Set ℝ) (Φ : ℕ → ℝ → ℝ × ℝ → ℂ)
    (D : ℕ → ℝ → List (Fin 2) → ℝ × ℝ → ℂ) : Prop where
  jet : ∀ (j k : ℕ), ∀ r ∈ I, IsCellJet c m k (Φ j r) (D j r)
  cont : ∀ (j : ℕ) (w : List (Fin 2)), ∀ r ∈ I,
    Tendsto (fun r' => xNorm c (-m) (D j r' w - D j r w)) (𝓝[I] r) (𝓝 0)

/-- **Leaf 6a: uniqueness of the weak derivative on the cell** (SP 3060): if `g` and `g'` are both
weak `∂_j`-derivatives of `φ` on the cylinder (`HasWeakCellDerivC`), then `g = g'` almost
everywhere on the cell.  (`g - g'` integrates to zero against every cylinder test; cylinder tests
contain the periodizations of bumps supported in the open cell, `Sob.exists_isCylTest_eq`, and
`g - g'` is locally integrable in the open cell, since `∫ |g| ψ < ∞` for bumps `ψ ≥ 0`; the
fundamental lemma on the open cell, then the null boundary of the cell.) -/
def CellWeakUnique : Prop :=
  ∀ (c : ℝ) (j : Fin 2) (φ g g' : ℝ × ℝ → ℂ), 0 < c →
    HasWeakCellDerivC c j φ g → HasWeakCellDerivC c j φ g' →
      g =ᵐ[volume.restrict (B0579.cell c)] g'

/-- **Leaf 6: coherent jets** (SP 3060-3061): time jets have derivative fields independent of the
order.  For each `(j, w)` take `D^{(j,w)}` from `AdjHkOn c m |w| (Φ j)` (field `IsAdjTimeJets.1`)
and put `D j r w := D^{(j,w)} r w`; two cell jets of the same function have almost everywhere equal
fields up to the common order (induction on `w` by `CellWeakUnique` and `HasWeakCellDerivC.congr_ae`
of `Sub/T18_2_4_2.lean`), which gives the weak-derivative relations between the chosen fields. -/
def CohJetsExists : Prop :=
  ∀ (c m t s : ℝ) (Φ : ℕ → ℝ → ℝ × ℝ → ℂ), 0 < c → IsAdjTimeJets c m (Ioo t s) Φ →
    ∃ D : ℕ → ℝ → List (Fin 2) → ℝ × ℝ → ℂ, CohJets c m (Ioo t s) Φ D

/-! ## Measurable versions -/

/-- **Leaf 7a: a jointly measurable version of an `L²(μ)`-continuous path** (SP 3060-3061).  Step
approximants on partitions: with `f̃ r` a strongly measurable representative of `f r`, for each `n`
there is a jointly measurable `F_n` with `‖F_n(r, ·) - f r‖_{L²(μ)} ≤ 2^{-n}` for every
`r ∈ [t + (s-t)/(n+3), s - (s-t)/(n+3)]` (uniform continuity on that compact interval, a finite
partition, `F_n(r, ·) = f̃(r_i)` on the `i`-th piece); then for every `r` the errors are summable
from some `n` on, so `F_n(r, ·) → f r` `μ`-a.e. (Borel-Cantelli, `tendstoInMeasure` or the Cauchy
criterion in `L²`), and `F := lim F_n` where the limit exists and `0` elsewhere is jointly
measurable. -/
def MeasPathVersion : Prop :=
  ∀ (μ : Measure (ℝ × ℝ)) [SigmaFinite μ] (t s : ℝ) (f : ℝ → ℝ × ℝ → ℂ),
    (∀ r ∈ Ioo t s, MemLp (f r) 2 μ) →
    (∀ r ∈ Ioo t s, Tendsto (fun r' => eLpNorm (f r' - f r) 2 μ) (𝓝[Ioo t s] r) (𝓝 0)) →
      ∃ F : ℝ × (ℝ × ℝ) → ℂ, Measurable F ∧ ∀ r ∈ Ioo t s, (fun x => F (r, x)) =ᵐ[μ] f r

/-- **Leaf 7b: from the cell measure to Lebesgue measure by periodicity**: if `F(r, ·) = f r`
almost everywhere for the cell measure `X_{-m,c}` and every `f r` is `c`-periodic, then
`F'(r, x) := F(r, x - (kc, 0))`, with `k = ⌊(x₁ + c/2)/c⌋`, is jointly measurable and
`F'(r, ·) = f r` Lebesgue-almost everywhere (on each translate of the cell, by periodicity; the
cell measure and `volume.restrict cell` have the same null sets, `B0579.ac_cellMeasure`,
`B0579.cellMeasure_ac`). -/
def MeasPlaneVersion : Prop :=
  ∀ (c m t s : ℝ) (f : ℝ → ℝ × ℝ → ℂ) (F : ℝ × (ℝ × ℝ) → ℂ), 0 < c → Measurable F →
    (∀ r ∈ Ioo t s, Periodic1 c (f r)) →
    (∀ r ∈ Ioo t s, (fun x => F (r, x)) =ᵐ[B0579.cellMeasure c (-m)] f r) →
      ∃ F' : ℝ × (ℝ × ℝ) → ℂ, Measurable F' ∧
        ∀ r ∈ Ioo t s, (fun x => F' (r, x)) =ᵐ[volume] f r

/-- **Leaf 8: `L²_loc`** (SP 3060-3061): a jointly measurable version of a path of `c`-periodic
functions, continuous into `X_{-m,c}`, is in `L²_loc((t, s) × ℝ²)`.  A compact `K ⊆ (t,s) × ℝ²`
lies in `[a, b] × [-R, R]²`; `r ↦ xNorm (f r)` is bounded on `[a, b]` (continuity, compactness);
`PeriodicBoxBound` (Tasks/AdjSmooth/Interior/SliceAe/PeriodicBoxBound.lean, theorem
`periodicBoxBound`) bounds each slice in `L²(box)` by `M xNorm (f r)`; Tonelli over
`volume = volume.prod volume` on `ℝ × ℝ²` gives `∫_K |G|² ≤ (b - a) (M sup xNorm)²`. -/
def STLocL2Of : Prop :=
  ∀ (c m t s : ℝ) (f : ℝ → ℝ × ℝ → ℂ) (G : ℝ × (ℝ × ℝ) → ℂ), 0 < c → t < s →
    (∀ r ∈ Ioo t s, Periodic1 c (f r) ∧ MemLp (f r) 2 (B0579.cellMeasure c (-m))) →
    (∀ r ∈ Ioo t s, Tendsto (fun r' => xNorm c (-m) (f r' - f r)) (𝓝[Ioo t s] r) (𝓝 0)) →
    Measurable G → (∀ r ∈ Ioo t s, (fun x => G (r, x)) =ᵐ[volume] f r) → STLocL2 t s G

/-! ## The spatial letters -/

/-- **Leaf 4a: periodization gives cylinder tests** (S0 of `Lib/Sobolev/Cylinder.lean` is the
variant for tests supported in the open cell): for `θ ∈ C_c^∞(ℝ²)` (real) the sum `perTest c θ`
is locally finite, a cylinder test, and commutes with the partial derivatives
`B0579.pd i θ x = fderiv ℝ θ x (B0579.dir i)`. -/
def PerTestCyl : Prop :=
  ∀ (c : ℝ) (θ : ℝ × ℝ → ℝ), 0 < c → ContDiff ℝ ∞ θ → HasCompactSupport θ →
    B0579.IsCylTest c (perTest c θ) ∧ ∀ i : Fin 2, B0579.pd i (perTest c θ) = perTest c (B0579.pd i θ)

/-- **Leaf 4b: unfolding the plane integral onto the cell**: for `c`-periodic locally integrable
`h` and `θ ∈ C_c^∞(ℝ²)`, `∫_{ℝ²} h θ = ∫_cell h (perTest c θ)` (cut `ℝ²` into the translates
`cell + (kc, 0)` and use periodicity of `h`; finitely many translates meet `tsupport θ`). -/
def PerTestUnfold : Prop :=
  ∀ (c : ℝ) (θ : ℝ × ℝ → ℝ) (h : ℝ × ℝ → ℂ), 0 < c → ContDiff ℝ ∞ θ → HasCompactSupport θ →
    Periodic1 c h → LocallyIntegrable h volume →
      Integrable (fun x => h x * (θ x : ℂ)) ∧
        IntegrableOn (fun x => h x * (perTest c θ x : ℂ)) (B0579.cell c) ∧
        ∫ x, h x * (θ x : ℂ) = ∫ x in B0579.cell c, h x * (perTest c θ x : ℂ)

/-- **Leaf 4: integration by parts on a slice** (SP 3060): for `c`-periodic `f, g ∈ X_{-m,c}` with
`HasWeakCellDerivC c i f g` and a compactly supported smooth `θ` on the plane,
`∫_{ℝ²} f ∂_iθ = -∫_{ℝ²} g θ`.  (`f, g` are locally integrable: `PeriodicBoxBound`; apply the cell
identity to the cylinder test `perTest c θ`, `PerTestCyl`, `PerTestUnfold` for `θ` and `∂_iθ`.) -/
def SliceIBP : Prop :=
  ∀ (c m : ℝ) (i : Fin 2) (f g : ℝ × ℝ → ℂ), 0 < c → Periodic1 c f → Periodic1 c g →
    MemLp f 2 (B0579.cellMeasure c (-m)) → MemLp g 2 (B0579.cellMeasure c (-m)) →
    HasWeakCellDerivC c i f g → ∀ θ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      Integrable (fun x => f x * (B0579.pd i θ x : ℂ)) ∧ Integrable (fun x => g x * (θ x : ℂ)) ∧
        ∫ x, f x * (B0579.pd i θ x : ℂ) = -∫ x, g x * (θ x : ℂ)

/-- **Leaf 5: the spatial one-letter identity in space-time** (SP 3060): if for every `r ∈ (t, s)`
the slice `g r` is the periodic weak `∂_i`-derivative of `f r` in `X_{-m,c}`, and `Gf, Gg` are
jointly measurable `L²_loc` versions of `f, g` (equal to the slices a.e. for every `r`), then
`∫ (∂_{x_i}Ψ) Gf = -∫ Ψ Gg` for `Ψ ∈ C_c^∞((t,s) × ℝ²)`: `volume = volume.prod volume` on
`ℝ × ℝ²` (Fubini, integrability by `L²_loc` and compact support), for each `r` apply `SliceIBP`
to `θ = Ψ(r, ·)` (`fderiv ℝ Ψ (r, x) (0, dir i) = pd i θ x`), `Ψ(r, ·) = 0` for `r ∉ (t, s)`.
Here `stDir i.succ = (0, B0579.dir i)`. -/
def STSpaceIdentity : Prop :=
  ∀ (c m t s : ℝ) (i : Fin 2) (f g : ℝ → ℝ × ℝ → ℂ) (Gf Gg : ℝ × (ℝ × ℝ) → ℂ), 0 < c → t < s →
    (∀ r ∈ Ioo t s, Periodic1 c (f r) ∧ MemLp (f r) 2 (B0579.cellMeasure c (-m)) ∧
      Periodic1 c (g r) ∧ MemLp (g r) 2 (B0579.cellMeasure c (-m)) ∧
      HasWeakCellDerivC c i (f r) (g r)) →
    Measurable Gf → Measurable Gg → STLocL2 t s Gf → STLocL2 t s Gg →
    (∀ r ∈ Ioo t s, (fun x => Gf (r, x)) =ᵐ[volume] f r) →
    (∀ r ∈ Ioo t s, (fun x => Gg (r, x)) =ᵐ[volume] g r) →
      STStepIdentity (stSlab t s) (stDir i.succ) Gf Gg

/-! ## The time letter -/

/-- **Leaf 1: the pairing bound** (SP 3060-3061): for `c > 0`, `m`, `R` there is `C` with
`|∫_{ℝ²} θ h| ≤ C B ‖h‖_{X_{-m,c}}` for every `c`-periodic `h ∈ X_{-m,c}` and measurable
`θ` vanishing outside the box `[-R, R]²` with `|θ| ≤ B` (Cauchy-Schwarz on the box and
`PeriodicBoxBound`, `C = M |box|^{1/2}`). -/
def PairBound : Prop :=
  ∀ (c m R : ℝ), 0 < c → ∃ C : ℝ, ∀ (h θ : ℝ × ℝ → ℂ) (B : ℝ), Periodic1 c h →
    MemLp h 2 (B0579.cellMeasure c (-m)) → Measurable θ →
    (∀ x, x ∉ sliceBox R → θ x = 0) → (∀ x, ‖θ x‖ ≤ B) →
      Integrable (fun x => θ x * h x) ∧ ‖∫ x, θ x * h x‖ ≤ C * B * (xNorm c (-m) h).toReal

/-- **Leaf 2: the tested time derivative** (SP 3060): for time jets `Φ` on `(t, s)` and
`Θ ∈ C_c^∞` with `tsupport Θ ⊆ (t, s) × ℝ²`, the pairing `h(r) = ∫ Θ(r, x) Φ j r x dx` is
differentiable on `(t, s)` with derivative `∫ ∂_rΘ Φ j r + ∫ Θ Φ (j+1) r`, which is continuous on
`(t, s)`.  (Difference quotient: `Θ(r', ·) [ (Φ j r' - Φ j r)/(r' - r) - Φ (j+1) r ]` is `o(1)` by
`PairBound` with the `X_{-m,c}` limit of `IsAdjTimeJets.2`, the uniform bound of `Θ`, and the
support in a fixed box; `(Θ(r', ·) - Θ(r, ·))/(r' - r) → ∂_rΘ(r, ·)` uniformly, by uniform
continuity of `∂_rΘ`, again with `PairBound`; continuity of the derivative from continuity of
`r ↦ Φ j r`, `Φ (j+1) r` in `X_{-m,c}` (`IsAdjTimeJets.1` at `k = 0`) and uniform continuity of
`Θ, ∂_rΘ`.) -/
def PairDeriv : Prop :=
  ∀ (c m t s : ℝ) (Φ : ℕ → ℝ → ℝ × ℝ → ℂ) (j : ℕ) (Θ : ℝ × (ℝ × ℝ) → ℝ), 0 < c → t < s →
    IsAdjTimeJets c m (Ioo t s) Φ → ContDiff ℝ ∞ Θ → HasCompactSupport Θ →
    tsupport Θ ⊆ stSlab t s →
      (∀ r ∈ Ioo t s, HasDerivAt (fun r' => ∫ x : ℝ × ℝ, (Θ (r', x) : ℂ) * Φ j r' x)
        ((∫ x : ℝ × ℝ, (fderiv ℝ Θ (r, x) (1, (0, 0)) : ℂ) * Φ j r x) +
          ∫ x : ℝ × ℝ, (Θ (r, x) : ℂ) * Φ (j + 1) r x) r) ∧
      ContinuousOn (fun r => (∫ x : ℝ × ℝ, (fderiv ℝ Θ (r, x) (1, (0, 0)) : ℂ) * Φ j r x) +
          ∫ x : ℝ × ℝ, (Θ (r, x) : ℂ) * Φ (j + 1) r x) (Ioo t s)

/-- **Leaf 3: the time one-letter identity in space-time** (SP 3060): for time jets `Φ` and
jointly measurable `L²_loc` versions `G0, G1` of `Φ j, Φ (j+1)` (equal to the slices a.e. for
every `r`), `∫ (∂_rΨ) G0 = -∫ Ψ G1` for `Ψ ∈ C_c^∞((t,s) × ℝ²)`.  (`h(r) = ∫ Ψ(r,·) Φ j r` of
`PairDeriv` vanishes near the ends and is `C¹` on `(t, s)`, so `∫ h' = 0` (FTC on a compact
`[a, b] ⊂ (t, s)` containing the `r`-support); Fubini on `ℝ × ℝ²` with the a.e. slices.  `stDir 0 =
(1, (0, 0))`.) -/
def STTimeIdentity : Prop :=
  ∀ (c m t s : ℝ) (Φ : ℕ → ℝ → ℝ × ℝ → ℂ) (j : ℕ) (G0 G1 : ℝ × (ℝ × ℝ) → ℂ), 0 < c → t < s →
    IsAdjTimeJets c m (Ioo t s) Φ → Measurable G0 → Measurable G1 →
    STLocL2 t s G0 → STLocL2 t s G1 →
    (∀ r ∈ Ioo t s, (fun x => G0 (r, x)) =ᵐ[volume] Φ j r) →
    (∀ r ∈ Ioo t s, (fun x => G1 (r, x)) =ᵐ[volume] Φ (j + 1) r) →
      STStepIdentity (stSlab t s) (stDir 0) G0 G1

end UnforcedLeray.Short.IIIa
