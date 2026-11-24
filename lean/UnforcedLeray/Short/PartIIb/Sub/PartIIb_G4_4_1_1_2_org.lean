import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_4_1_1_2
import UnforcedLeray.Short.PartI.StatementsTrain
import UnforcedLeray.Units.B0191

/-!
# Part II-b, organizer `PartII-b:G4/4/1/1/2/1/org`: the parity form of `U_raw` from the heat expansion

Source of record: `the November 2 reference manuscript` (SP), lines 1205-1235
(Proposition `sct:lift`; line 1219 "smooth through the axis for positive time"), 1310-1319 (the
proof: "Smoothness at the axis follows term by term from the full heat expansion ... Thus `u_r/r`
and `u_z` are smooth functions of `(r², z, t)`"), 2548-2551 ("On `ϱ < R`, take the all-age heat
expansion to a sufficiently high finite order: its even radial powers extend smoothly through the
axis"), 438-459 (Lemma `sct:heat`), 429-435 (all orders at fixed parameters).

## Step (1): `RawParityForm` is true as stated

`RawParityForm` (`Sub/PartII-b_G4_4_1_1_2.lean`) asks for `G, H` smooth in `(τ, w, z)` on `w ≥ 0`
(`w = ϱ² = y₀² + y₁²`, `z = y₃`) for *all* phases `τ ∈ ℝ`. Here `τ` is the similarity phase
`τ = log t` (SP 135, 1287-1291): every `τ ∈ ℝ`, including `τ ≤ 0`, is the positive physical time
`t = e^τ`, and the axis `w → 0` is the large age `s = R²/w → ∞` at every phase. `U_raw` has no
cutoff (the age cutoff belongs to the inlet `E_ε`). Off the axis the field is smooth because the
train stream is smooth for `s > 0`; at the axis the source's argument (SP 1310-1319, transported to
the similarity variables, where `G(τ,w,z) = e^τ g(e^τ w, e^{τ/2} z, e^τ)` for the physical
`g = u_r/r`) applies at every phase. So no refutation: the statement is kept, and
`rawJointSmooth_of` (its only consumer) is unchanged.

## Step (2): the mechanism in the parity variables

With `x = (τ, (w, z))` and the parity chart `parChart R x = (s, (q, η)) = (R²/w, (Rτ/2 − (R/2) log s,
R z/√w))` (equal to `Axi.chart R τ y` off the axis, `chart_eq_parChart`), the ring lift is
`Nv R b τ y = parG R b x • hor y + parH R b x • e₃` with `parG = (R/w) b_r ∘ parChart`,
`parH = (R/√w) b_z ∘ parChart` (`Nv_eq_parity`). For the train, `b = rawProfile ε v ψ` is the ring
stream profile `ringStreamProfile R Ψ = (−Ψ_η, Ψ_q + ε(Ψ − 2sΨ_s − ηΨ_η))` of the stream
`Ψ(s,(q,η)) = ψ(s,(q,η))` (`RawStreamProfile`). Split `Ψ = ∑_{j≤N} a_{2j} ∂_η^{2j}G_{νs} + Φ_N`
(`heatRemainder`; for the train `Φ_N = R_N + ψ̃`, the mean remainder of `sct:expansion` plus the
fluctuation of `sct:fluctuation`):

* the heat terms give `parG = −R^{-(2j+1)} w^j g_ν^{(2j+1)}(z)`, `parH = (2j+2) R^{-(2j+1)} w^j
  g_ν^{(2j)}(z)` (`HeatTermParity`; SP 1310-1313 and the heat identity `K∂_η^jG = −(j+1)∂_η^jG`,
  SP 1267-1268): polynomials in `w`, smooth through `w = 0` ("its even radial powers extend
  smoothly through the axis");
* if all derivatives of `Φ_N` are `O(s^{-N-3/2})` (the remainder bound of `sct:expansion` with
  `m = 0`, `p = ∞`, and the exponential decay of `sct:fluctuation`), the parity coefficients of
  `Φ_N` extend by zero across `w = 0` to `C^k` functions, `N = 2k + 1` (`RemainderParity`; "the
  remainder after order `N` is `O(r^{2N+4-a})`", SP 1316-1317).

Taking `N` large gives `C^∞` (`parityOfExpansion_of`). The source fact on the train is
`TrainHeatExpansion`: the all-age heat expansion with remainder `O(s^{-N-3/2})` in `C^∞`, for every
order at fixed parameters (SP 429-435), uniformly below one smallness threshold `ν₀`.

**Why a new train Prop.** `PartI.TrainMeanExpansion` and `PartI.TrainFluctuationDecay`
(`Short/PartI/StatementsTrain.lean`) are the quantitative statements for a fixed finite collection of
orders (SP 247-258): their threshold `ν₀` depends on the orders. `C^∞` at a fixed `ν` needs every
order at that `ν`, which is SP 429-435 ("All higher-order versions of the argument therefore hold at
fixed parameters, without requiring a new smallness condition for each order"); this is
`TrainHeatExpansion`. It is a Part I fact (routed to an organizer task).

## Contents

Definitions: `parPos`, `parNonneg`, `parChart`, `parG`, `parH`, `zeroExtW`, `heatTerm`,
`heatRemainder`, `heatParG`, `heatParH`.

Leaf Props (each one task): `TrainHeatExpansion` (source fact, Part I), `RawStreamProfile`,
`HeatTermSmooth`, `HeatTermParity`, `HalfSpaceFlatExt`, `ParChartJet`, `ParWeightJet`,
`RingProfileJet`, `ParCompWeightJet`.

Proved here: `chart_eq_parChart`, `Nv_eq_parity`, `contDiff_heatParG`, `contDiff_heatParH`,
`remainderParity_of`, `parityOfExpansion_of`, `rawParityForm_of`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Blueprint

/-! ## The parity variables -/

/-- The parity variables `x = (τ, (w, z))`: the phase `τ`, `w = ϱ² = y₀² + y₁²` and `z = y₃`.
The open half space `w > 0` (the complement of the axis). -/
def parPos : Set (ℝ × (ℝ × ℝ)) := {x | 0 < x.2.1}

/-- The closed half space `w ≥ 0`, the domain of the parity coefficients of `RawParityForm`. -/
def parNonneg : Set (ℝ × (ℝ × ℝ)) := {x | 0 ≤ x.2.1}

/-- **The similarity ring chart in the parity variables** (SP 1207-1212, 1287-1291):
`(τ, (w, z)) ↦ (s, (q, η)) = (R²/w, (Rτ/2 − (R/2) log(R²/w), R z/√w))`. At `w = y₀² + y₁²`,
`z = y₃` it is `Axi.chart R τ y` (`chart_eq_parChart`). -/
def parChart (R : ℝ) (x : ℝ × (ℝ × ℝ)) : ℝ × (ℝ × ℝ) :=
  (R ^ 2 / x.2.1, (R * x.1 / 2 - (R / 2) * Real.log (R ^ 2 / x.2.1), R * x.2.2 / Real.sqrt x.2.1))

/-- **The radial parity coefficient** `G = (R/w) b_r ∘ parChart` of a meridional profile `b`
(chart order `(s, (q, η))`). Off the axis `√s e_r = (R/ϱ²)(y₀, y₁, 0)`, so
`Nv R b τ y = G • hor y + H • e₃` (`Nv_eq_parity`). -/
def parG (R : ℝ) (b : ℝ × (ℝ × ℝ) → UnforcedLeray.Axi.Merid) (x : ℝ × (ℝ × ℝ)) : ℝ :=
  R / x.2.1 * b (parChart R x) 0

/-- **The axial parity coefficient** `H = (R/√w) b_z ∘ parChart`. -/
def parH (R : ℝ) (b : ℝ × (ℝ × ℝ) → UnforcedLeray.Axi.Merid) (x : ℝ × (ℝ × ℝ)) : ℝ :=
  R / Real.sqrt x.2.1 * b (parChart R x) 1

/-- Extension by zero across the boundary `w = 0`: `f` on `w > 0`, `0` on `w ≤ 0`. -/
def zeroExtW {F : Type*} [Zero F] (f : ℝ × (ℝ × ℝ) → F) (x : ℝ × (ℝ × ℝ)) : F :=
  if 0 < x.2.1 then f x else 0

/-! ## The heat terms -/

/-- **The heat terms of `sct:expansion`** (SP 447-452) at the chart point `y = (s, (q, η))`:
`∂_η^{2j} G_{νs}(η)`, with `G_t = PartI.heatKernel1 t` the one-dimensional heat kernel. -/
def heatTerm (ν : ℝ) (j : ℕ) (y : ℝ × (ℝ × ℝ)) : ℝ :=
  iteratedDeriv (2 * j) (UnforcedLeray.Short.PartI.heatKernel1 (ν * y.1)) y.2.2

/-- The stream minus its first `N + 1` heat terms, `Ψ − ∑_{j ≤ N} a_j ∂_η^{2j} G_{νs}`. For the train
(`a = PartI.meanCoeff`) this is `R_N + ψ̃`: the remainder `R_N` of the mean stream in
`sct:expansion` (`PartI.meanRemainder`) plus the fluctuation `ψ̃ = ψ − \bar ψ`. -/
def heatRemainder (ν : ℝ) (a : ℕ → ℝ) (N : ℕ) (Ψ : ℝ × (ℝ × ℝ) → ℝ) (y : ℝ × (ℝ × ℝ)) : ℝ :=
  Ψ y - ∑ j ∈ Finset.range (N + 1), a j * heatTerm ν j y

/-- The radial parity coefficient of the `j`-th heat term (SP 1310-1313:
`r a_{2j}∂_η^{2j}G_{νs} = a_{2j} r^{2j+2} R^{-2j-1} ∂_z^{2j}G_{νt}(z)`), in the parity variables:
`−R^{-(2j+1)} w^j g_ν^{(2j+1)}(z)`, `g_ν = B0191.profile ν` the unit-age heat kernel `G_ν`. -/
def heatParG (ν R : ℝ) (j : ℕ) (x : ℝ × (ℝ × ℝ)) : ℝ :=
  -((R ^ (2 * j + 1))⁻¹ * x.2.1 ^ j * UnforcedLeray.B0191.profileDeriv ν (2 * j + 1) x.2.2)

/-- The axial parity coefficient of the `j`-th heat term:
`(2j+2) R^{-(2j+1)} w^j g_ν^{(2j)}(z)` (the factor `2j + 2` is `1 − K` on `∂_η^{2j}G_{νs}`,
SP 1267-1268). -/
def heatParH (ν R : ℝ) (j : ℕ) (x : ℝ × (ℝ × ℝ)) : ℝ :=
  (2 * (j : ℝ) + 2) * (R ^ (2 * j + 1))⁻¹ * x.2.1 ^ j *
    UnforcedLeray.B0191.profileDeriv ν (2 * j) x.2.2

/-! ## Leaf Props -/

/-- **The all-age heat expansion of the train stream, at fixed parameters** (source fact;
SP 438-459, Lemma `sct:heat`, with SP 429-435).

For `ρ > 1/2` there is one threshold `ν₀` such that for every train of the BUC class with
`c = ν^{-ρ}`, `ν ≤ ν₀`, and every order `N` and derivative order `i`, the stream minus its first
`N + 1` heat terms (`heatRemainder`, coefficients `a_{2j} = PartI.meanCoeff`) has
`‖D^i(ψ − ∑_{j≤N} a_{2j}∂_η^{2j}G_{νs})(s, q, η)‖ ≤ C s^{-N-3/2}` for `s ≥ 1`, all `q, η`, with
`C` depending on everything (fixed parameters). `D^i` is the full `i`-th derivative in
`(s, q, η)`, i.e. all mixed age/spatial derivatives of order `i` together.

This is the conjunction of: the remainder bound of `sct:expansion` (SP 455-458:
`‖η^m∂_η^b∂_s^ℓ R_N(s)‖_p ≤ P s^{(m−b−2N−3)/2−ℓ+1/(2p)}`, `s ≥ 1`) at `m = 0`, `p = ∞`, where
`s^{−b/2−ℓ} ≤ 1` (`R_N` does not depend on `q`); and `sct:fluctuation` (SP 440-445, "every fixed
mixed age/spatial derivative" of `ψ̃` is `≤ P e^{−κνs/c²}`), whose exponential decay is
`O(s^{-N-3/2})`. The weights `η^m` of the source (axial decay, used for the `W^{k,p}` bound at
SP 2549-2551) are not needed for smoothness, which is local in `z`. The threshold is fixed before
the orders: SP 429-435 ("All higher-order versions of the argument therefore hold at fixed
parameters, without requiring a new smallness condition for each order"). The quantitative Part I
statements `PartI.TrainMeanExpansion`, `PartI.TrainFluctuationDecay` have a threshold depending on
the orders (SP 247-258) and do not give this. -/
def TrainHeatExpansion : Prop :=
  ∀ ρ : ℝ, 1 / 2 < ρ → ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν c : ℝ, 0 < ν → ν ≤ ν₀ →
    c = UnforcedLeray.Short.PartI.trainPeriod ρ ν →
    ∀ tr : UnforcedLeray.B0140.TrainSol ν c, UnforcedLeray.Short.PartI.IsBUCTrain tr →
      ∀ N i : ℕ, ∃ C : ℝ, ∀ y : ℝ × (ℝ × ℝ), 1 ≤ y.1 →
        ‖iteratedFDeriv ℝ i
            (heatRemainder ν (UnforcedLeray.Short.PartI.meanCoeff tr) N
              (fun y => tr.ψ y.1 y.2)) y‖ ≤
          C * y.1 ^ (-(N : ℝ) - 3 / 2)

/-- **The raw profile is the ring stream profile of the train stream** (SP 1207-1212: the physical
stream `rψ` gives `u_r = (R/r)v₁`, `u_z = (R/r)(v₂ + εH)`, `H = (1 − K)ψ`): for `s > 0`, `ε = R⁻¹`
and a stream jointly smooth for positive age, `rawProfile ε v ψ = (v₁, v₂ + εH)` (one-variable
`deriv`s, `v = ∇^⊥ψ` by `IsTrain.stream`) equals `Axi.ringStreamProfile R Ψ =
(−Ψ_η, Ψ_q + R⁻¹(Ψ − 2sΨ_s − ηΨ_η))` (chart partials) of `Ψ(s, (q, η)) = ψ(s, (q, η))`. -/
def RawStreamProfile : Prop :=
  ∀ (ν c R : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c), 0 < R →
    ContDiffOn ℝ ∞ (fun x : ℝ × UnforcedLeray.Cyl.Plane => tr.ψ x.1 x.2) (Ioi 0 ×ˢ univ) →
    ∀ y : ℝ × (ℝ × ℝ), 0 < y.1 →
      UnforcedLeray.Cons.C03.rawProfile R⁻¹ tr.v tr.ψ y =
        UnforcedLeray.Axi.ringStreamProfile R (fun y => tr.ψ y.1 y.2) y

/-- **The heat terms are smooth for positive age** (`∂_η^{2j}G_{νs}(η) = s^{-(2j+1)/2}
g_ν^{(2j)}(η/√s)`, `B0191.heatDeriv_selfSimilar`). -/
def HeatTermSmooth : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ j : ℕ, ContDiffOn ℝ ∞ (heatTerm ν j) (Ioi 0 ×ˢ univ)

/-- **The parity coefficients of the heat terms** (SP 1310-1313, SP 1267-1268): on `w > 0`,
`parG R (ringStreamProfile R (heatTerm ν j)) = heatParG ν R j` and
`parH R (ringStreamProfile R (heatTerm ν j)) = heatParH ν R j`. (`∂_q` of a heat term is `0`;
`K ∂_η^{2j}G_{νs} = −(2j+1) ∂_η^{2j}G_{νs}`, `B0191.K_iteratedDeriv_heatKernel`; at the chart
point `√s = R/√w` and `η/√s = z`.) -/
def HeatTermParity : Prop :=
  ∀ ν R : ℝ, 0 < ν → 0 < R → ∀ (j : ℕ) (x : ℝ × (ℝ × ℝ)), 0 < x.2.1 →
    parG R (UnforcedLeray.Axi.ringStreamProfile R (heatTerm ν j)) x = heatParG ν R j x ∧
    parH R (UnforcedLeray.Axi.ringStreamProfile R (heatTerm ν j)) x = heatParH ν R j x

/-- **Flat extension across `w = 0`** (the half-space analogue of
`Axi.contDiff_of_tendsto_axis`, `Lib/AxisymmetricB/FlatExtension.lean`): a function `C^k` on
`w > 0` whose derivatives of order `≤ k` are `O(w)` near the boundary (locally uniformly in `z`,
uniformly in `τ`) extends by zero to a `C^k` function on `ℝ × (ℝ × ℝ)`. -/
def HalfSpaceFlatExt : Prop :=
  ∀ (k : ℕ) (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] (f : ℝ × (ℝ × ℝ) → F),
    ContDiffOn ℝ k f parPos →
    (∀ n ≤ k, ∀ M : ℝ, ∃ C : ℝ, ∀ x ∈ parPos, x.2.1 ≤ 1 → |x.2.2| ≤ M →
      ‖iteratedFDeriv ℝ n f x‖ ≤ C * x.2.1) →
    ContDiff ℝ k (zeroExtW f)

/-- **Jets of the parity chart**: `parChart R` is smooth on `w > 0`, and on `0 < w ≤ 1`, `|z| ≤ M`
its derivatives of order `1 ≤ i ≤ n` are `≤ (D/w²)^i` (`R²/w`, `log w`, `R z w^{-1/2}` have
`i`-th derivatives `O((1 + M) w^{-i-1})`). -/
def ParChartJet : Prop :=
  ∀ R : ℝ, 0 < R → ContDiffOn ℝ ∞ (parChart R) parPos ∧
    ∀ (n : ℕ) (M : ℝ), ∃ D : ℝ, 0 ≤ D ∧ ∀ x ∈ parPos, x.2.1 ≤ 1 → |x.2.2| ≤ M →
      ∀ i : ℕ, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i (parChart R) x‖ ≤ (D / x.2.1 ^ 2) ^ i

/-- **Jets of the weights** `R/w` and `R/√w` on `0 < w ≤ 1`: `O(w^{-1-i})` and `O(w^{-1/2-i})`. -/
def ParWeightJet : Prop :=
  ∀ R : ℝ, ContDiffOn ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => R / x.2.1) parPos ∧
    ContDiffOn ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => R / Real.sqrt x.2.1) parPos ∧
    ∀ n : ℕ, ∃ C : ℝ, ∀ x ∈ parPos, x.2.1 ≤ 1 → ∀ i ≤ n,
      ‖iteratedFDeriv ℝ i (fun x : ℝ × (ℝ × ℝ) => R / x.2.1) x‖ ≤
          C * x.2.1 ^ (-(1 : ℝ) - i) ∧
        ‖iteratedFDeriv ℝ i (fun x : ℝ × (ℝ × ℝ) => R / Real.sqrt x.2.1) x‖ ≤
          C * x.2.1 ^ (-(1 / 2 : ℝ) - i)

/-- **Jets of the ring stream profile**: for `Φ` smooth on `s > 0` the two components of
`ringStreamProfile R Φ = (−Φ_η, Φ_q + R⁻¹(Φ − 2sΦ_s − ηΦ_η))` are smooth on `s > 0`, with
`‖D^i(b_r)‖ ≤ C ∑_{l ≤ i+1} ‖D^lΦ‖` and `‖D^i(b_z)‖ ≤ C (1 + |s| + |η|) ∑_{l ≤ i+1} ‖D^lΦ‖`
(Leibniz; the coordinates `s`, `η` have derivatives of order `≥ 2` equal to `0`). -/
def RingProfileJet : Prop :=
  ∀ (R : ℝ) (Φ : ℝ × (ℝ × ℝ) → ℝ), ContDiffOn ℝ ∞ Φ (Ioi 0 ×ˢ univ) →
    ContDiffOn ℝ ∞ (fun y => UnforcedLeray.Axi.ringStreamProfile R Φ y 0) (Ioi 0 ×ˢ univ) ∧
    ContDiffOn ℝ ∞ (fun y => UnforcedLeray.Axi.ringStreamProfile R Φ y 1) (Ioi 0 ×ˢ univ) ∧
    ∀ i : ℕ, ∃ C : ℝ, ∀ y : ℝ × (ℝ × ℝ), 0 < y.1 →
      ‖iteratedFDeriv ℝ i (fun y => UnforcedLeray.Axi.ringStreamProfile R Φ y 0) y‖ ≤
          C * ∑ l ∈ Finset.range (i + 2), ‖iteratedFDeriv ℝ l Φ y‖ ∧
        ‖iteratedFDeriv ℝ i (fun y => UnforcedLeray.Axi.ringStreamProfile R Φ y 1) y‖ ≤
          C * (1 + |y.1| + |y.2.2|) * ∑ l ∈ Finset.range (i + 2), ‖iteratedFDeriv ℝ l Φ y‖

/-- **Weighted composition through the parity chart** (Leibniz and Faà di Bruno,
`norm_iteratedFDerivWithin_mul_le`, `norm_iteratedFDerivWithin_comp_le`, with `ParChartJet`): for a
weight `ω` with `‖D^iω‖ ≤ C w^{-a-i}` on `0 < w ≤ 1`, and `g` smooth on `s > 0` with
`‖D^i g(y)‖ ≤ C s^{-β}` on `s ≥ 1`, `|η| ≤ M√s` (the image of `0 < w ≤ 1`, `|z| ≤ M` when `R ≥ 1`),
the product `ω · g ∘ parChart` is smooth on `w > 0` with `‖D^n(ω · g ∘ parChart)‖ ≤ C w^{β−a−2n}`
on `0 < w ≤ 1`, `|z| ≤ M`. -/
def ParCompWeightJet : Prop :=
  ∀ (R a β : ℝ) (wt g : ℝ × (ℝ × ℝ) → ℝ), 1 ≤ R → 0 ≤ β →
    ContDiffOn ℝ ∞ wt parPos → ContDiffOn ℝ ∞ g (Ioi 0 ×ˢ univ) →
    (∀ n : ℕ, ∃ C : ℝ, ∀ x ∈ parPos, x.2.1 ≤ 1 → ∀ i ≤ n,
      ‖iteratedFDeriv ℝ i wt x‖ ≤ C * x.2.1 ^ (-a - i)) →
    (∀ (i : ℕ) (M : ℝ), ∃ C : ℝ, ∀ y : ℝ × (ℝ × ℝ), 1 ≤ y.1 → |y.2.2| ≤ M * Real.sqrt y.1 →
      ‖iteratedFDeriv ℝ i g y‖ ≤ C * y.1 ^ (-β)) →
    ContDiffOn ℝ ∞ (fun x => wt x * g (parChart R x)) parPos ∧
    ∀ (n : ℕ) (M : ℝ), ∃ C : ℝ, ∀ x ∈ parPos, x.2.1 ≤ 1 → |x.2.2| ≤ M →
      ‖iteratedFDeriv ℝ n (fun x => wt x * g (parChart R x)) x‖ ≤
        C * x.2.1 ^ (β - a - 2 * n)

/-! ## Intermediate Props -/

/-- **The remainder has `C^k` parity coefficients** (SP 1316-1318): if every derivative of `Φ` is
`O(s^{-(2k+1)-3/2})` on `s ≥ 1`, the parity coefficients of `ringStreamProfile R Φ` extend by zero
across `w = 0` to `C^k` functions. -/
def RemainderParity : Prop :=
  ∀ R : ℝ, 1 ≤ R → ∀ (k : ℕ) (Φ : ℝ × (ℝ × ℝ) → ℝ), ContDiffOn ℝ ∞ Φ (Ioi 0 ×ˢ univ) →
    (∀ i : ℕ, ∃ C : ℝ, ∀ y : ℝ × (ℝ × ℝ), 1 ≤ y.1 →
      ‖iteratedFDeriv ℝ i Φ y‖ ≤ C * y.1 ^ (-(2 * (k : ℝ) + 1) - 3 / 2)) →
    ContDiff ℝ k (zeroExtW (parG R (UnforcedLeray.Axi.ringStreamProfile R Φ))) ∧
      ContDiff ℝ k (zeroExtW (parH R (UnforcedLeray.Axi.ringStreamProfile R Φ)))

/-- **The parity form from a heat expansion** (SP 1310-1319, 2548-2551): a stream `Ψ`, smooth for
positive age, whose remainders after every order `N` have all derivatives `O(s^{-N-3/2})`, has
parity coefficients `G, H` smooth on `w ≥ 0`. -/
def ParityOfExpansion : Prop :=
  ∀ ν R : ℝ, 0 < ν → 1 ≤ R → ∀ (a : ℕ → ℝ) (Ψ : ℝ × (ℝ × ℝ) → ℝ),
    ContDiffOn ℝ ∞ Ψ (Ioi 0 ×ˢ univ) →
    (∀ N i : ℕ, ∃ C : ℝ, ∀ y : ℝ × (ℝ × ℝ), 1 ≤ y.1 →
      ‖iteratedFDeriv ℝ i (heatRemainder ν a N Ψ) y‖ ≤ C * y.1 ^ (-(N : ℝ) - 3 / 2)) →
    ∃ G H : ℝ × (ℝ × ℝ) → ℝ, ContDiffOn ℝ ∞ G parNonneg ∧ ContDiffOn ℝ ∞ H parNonneg ∧
      ∀ x ∈ parPos, G x = parG R (UnforcedLeray.Axi.ringStreamProfile R Ψ) x ∧
        H x = parH R (UnforcedLeray.Axi.ringStreamProfile R Ψ) x

/-! ## The ring lift in parity form -/

/-- The ring chart at `y` is the parity chart at `(τ, (y₀² + y₁², y₃))`. -/
theorem chart_eq_parChart (R τ : ℝ) (y : Space) :
    UnforcedLeray.Axi.chart R τ y = parChart R (τ, (y 0 ^ 2 + y 1 ^ 2, y 2)) := by
  simp only [UnforcedLeray.Axi.chart, UnforcedLeray.Axi.phase, UnforcedLeray.Axi.age,
    UnforcedLeray.Axi.trans, parChart, UnforcedLeray.Axi.ϱ_sq]
  rfl

/-- **The ring lift in parity form**: off the axis,
`Nv R b τ y = parG R b x • hor y + parH R b x • e₃` at `x = (τ, (y₀² + y₁², y₃))`. -/
theorem Nv_eq_parity {R : ℝ} (hR : 0 < R) (b : ℝ × (ℝ × ℝ) → UnforcedLeray.Axi.Merid) (τ : ℝ)
    {y : Space} (hy : y ∉ UnforcedLeray.Axi.axis) :
    UnforcedLeray.Axi.Nv R b τ y =
      parG R b (τ, (y 0 ^ 2 + y 1 ^ 2, y 2)) • UnforcedLeray.Axi.hor y +
        parH R b (τ, (y 0 ^ 2 + y 1 ^ 2, y 2)) • UnforcedLeray.Axi.e3 := by
  have hρ : 0 < UnforcedLeray.Axi.ϱ y := UnforcedLeray.Axi.ϱ_pos hy
  have hw : y 0 ^ 2 + y 1 ^ 2 = UnforcedLeray.Axi.ϱ y ^ 2 := (UnforcedLeray.Axi.ϱ_sq y).symm
  have hsq : Real.sqrt (y 0 ^ 2 + y 1 ^ 2) = UnforcedLeray.Axi.ϱ y := rfl
  rw [UnforcedLeray.Axi.Nv, UnforcedLeray.Axi.frameL_apply, UnforcedLeray.Axi.sqrt_age hR hy,
    chart_eq_parChart]
  simp only [parG, parH, UnforcedLeray.Axi.eR, smul_add, smul_smul]
  rw [hsq]
  congr 2
  rw [hw]
  field_simp

/-! ## The heat-term coefficients are smooth -/

theorem contDiff_profileDeriv (ν : ℝ) (n : ℕ) :
    ContDiff ℝ ∞ (UnforcedLeray.B0191.profileDeriv ν n) := by
  unfold UnforcedLeray.B0191.profileDeriv
  rw [iteratedDeriv_eq_iterate]
  exact ContDiff.iterate_deriv n ((UnforcedLeray.B0191.contDiff_profile ν).of_le le_top)

theorem contDiff_heatParG (ν R : ℝ) (j : ℕ) : ContDiff ℝ ∞ (heatParG ν R j) := by
  have h1 : ContDiff ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => x.2.1 ^ j) := by fun_prop
  have h2 : ContDiff ℝ ∞
      (fun x : ℝ × (ℝ × ℝ) => UnforcedLeray.B0191.profileDeriv ν (2 * j + 1) x.2.2) :=
    (contDiff_profileDeriv ν _).comp (contDiff_snd.comp contDiff_snd)
  exact ((contDiff_const.mul h1).mul h2).neg

theorem contDiff_heatParH (ν R : ℝ) (j : ℕ) : ContDiff ℝ ∞ (heatParH ν R j) := by
  have h1 : ContDiff ℝ ∞ (fun x : ℝ × (ℝ × ℝ) => x.2.1 ^ j) := by fun_prop
  have h2 : ContDiff ℝ ∞
      (fun x : ℝ × (ℝ × ℝ) => UnforcedLeray.B0191.profileDeriv ν (2 * j) x.2.2) :=
    (contDiff_profileDeriv ν _).comp (contDiff_snd.comp contDiff_snd)
  exact (contDiff_const.mul h1).mul h2

/-- At `w = 0` only the `j = 0` heat term survives. -/
theorem sum_heatParG_of_eq_zero (ν R : ℝ) (a : ℕ → ℝ) (N : ℕ) {x : ℝ × (ℝ × ℝ)}
    (hx : x.2.1 = 0) :
    ∑ j ∈ Finset.range (N + 1), a j * heatParG ν R j x =
      ∑ j ∈ Finset.range (0 + 1), a j * heatParG ν R j x := by
  rw [Finset.sum_range_succ', zero_add, Finset.sum_range_one]
  have : ∀ j ∈ Finset.range N, a (j + 1) * heatParG ν R (j + 1) x = 0 := by
    intro j _
    simp [heatParG, hx]
  rw [Finset.sum_eq_zero this, zero_add]

theorem sum_heatParH_of_eq_zero (ν R : ℝ) (a : ℕ → ℝ) (N : ℕ) {x : ℝ × (ℝ × ℝ)}
    (hx : x.2.1 = 0) :
    ∑ j ∈ Finset.range (N + 1), a j * heatParH ν R j x =
      ∑ j ∈ Finset.range (0 + 1), a j * heatParH ν R j x := by
  rw [Finset.sum_range_succ', zero_add, Finset.sum_range_one]
  have : ∀ j ∈ Finset.range N, a (j + 1) * heatParH ν R (j + 1) x = 0 := by
    intro j _
    simp [heatParH, hx]
  rw [Finset.sum_eq_zero this, zero_add]

/-! ## Linearity of the ring stream profile -/

theorem ringStreamProfile_apply_zero (R : ℝ) (φ : ℝ × (ℝ × ℝ) → ℝ) (m : ℝ × (ℝ × ℝ)) :
    UnforcedLeray.Axi.ringStreamProfile R φ m 0 = -(UnforcedLeray.Axi.dEta φ m) := by
  simp [UnforcedLeray.Axi.ringStreamProfile]

theorem ringStreamProfile_apply_one (R : ℝ) (φ : ℝ × (ℝ × ℝ) → ℝ) (m : ℝ × (ℝ × ℝ)) :
    UnforcedLeray.Axi.ringStreamProfile R φ m 1 =
      UnforcedLeray.Axi.dQ φ m + R⁻¹ * (φ m - 2 * m.1 * UnforcedLeray.Axi.dS φ m -
        m.2.2 * UnforcedLeray.Axi.dEta φ m) := by
  simp [UnforcedLeray.Axi.ringStreamProfile]

theorem sum_lin_aux (N : ℕ) (a X Y Z W : ℕ → ℝ) (r s e : ℝ) :
    ∑ j ∈ Finset.range (N + 1), a j * (X j + r * (Y j - 2 * s * Z j - e * W j)) =
      ∑ j ∈ Finset.range (N + 1), a j * X j + r * (∑ j ∈ Finset.range (N + 1), a j * Y j -
        2 * s * ∑ j ∈ Finset.range (N + 1), a j * Z j -
          e * ∑ j ∈ Finset.range (N + 1), a j * W j) := by
  have h : ∀ j, a j * (X j + r * (Y j - 2 * s * Z j - e * W j)) =
      a j * X j + (r * (a j * Y j) - (r * (2 * s)) * (a j * Z j) - (r * e) * (a j * W j)) :=
    fun j => by ring
  rw [Finset.sum_congr rfl (fun j _ => h j), Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

theorem hasFDerivAt_heatRemainder {ν : ℝ} {a : ℕ → ℝ} {N : ℕ} {Ψ : ℝ × (ℝ × ℝ) → ℝ}
    {y : ℝ × (ℝ × ℝ)} (hΨ : DifferentiableAt ℝ Ψ y)
    (hT : ∀ j, DifferentiableAt ℝ (heatTerm ν j) y) :
    HasFDerivAt (heatRemainder ν a N Ψ)
      (fderiv ℝ Ψ y - ∑ j ∈ Finset.range (N + 1), a j • fderiv ℝ (heatTerm ν j) y) y :=
  hΨ.hasFDerivAt.fun_sub
    (HasFDerivAt.fun_sum (A := fun j y => a j * heatTerm ν j y) fun j _ =>
      (hT j).hasFDerivAt.const_mul (a j))

/-- **Linearity**: at a point where `Ψ` and the heat terms are differentiable,
`ringStreamProfile R Ψ = ∑_{j ≤ N} a_j ringStreamProfile R (heatTerm ν j) +
ringStreamProfile R (heatRemainder ν a N Ψ)`, componentwise. -/
theorem ringStreamProfile_heatRemainder (R ν : ℝ) (a : ℕ → ℝ) (N : ℕ)
    {Ψ : ℝ × (ℝ × ℝ) → ℝ} {y : ℝ × (ℝ × ℝ)} (hΨ : DifferentiableAt ℝ Ψ y)
    (hT : ∀ j, DifferentiableAt ℝ (heatTerm ν j) y) (i : Fin 2) :
    UnforcedLeray.Axi.ringStreamProfile R Ψ y i =
      ∑ j ∈ Finset.range (N + 1), a j * UnforcedLeray.Axi.ringStreamProfile R (heatTerm ν j) y i +
        UnforcedLeray.Axi.ringStreamProfile R (heatRemainder ν a N Ψ) y i := by
  have hD := (hasFDerivAt_heatRemainder (a := a) (N := N) hΨ hT).fderiv
  have hv : heatRemainder ν a N Ψ y = Ψ y - ∑ j ∈ Finset.range (N + 1), a j * heatTerm ν j y :=
    rfl
  fin_cases i
  · simp only [Fin.zero_eta, ringStreamProfile_apply_zero, UnforcedLeray.Axi.dEta, hD]
    simp only [sub_apply, sum_apply, smul_apply, smul_eq_mul, mul_neg, Finset.sum_neg_distrib]
    ring
  · simp only [Fin.mk_one, ringStreamProfile_apply_one, UnforcedLeray.Axi.dEta,
      UnforcedLeray.Axi.dQ, UnforcedLeray.Axi.dS, hD, hv]
    simp only [sub_apply, sum_apply, smul_apply, smul_eq_mul]
    rw [sum_lin_aux]
    ring

/-! ## The remainder: `C^k` parity coefficients -/

/-- `w^e ≤ w` on `0 < w ≤ 1` for `e ≥ 1`, with a nonnegative constant. -/
theorem le_mul_of_rpow_bound {u C e : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) (he : 1 ≤ e) {X : ℝ}
    (hX : X ≤ C * u ^ e) : X ≤ max C 0 * u := by
  have h1 : u ^ e ≤ u := by
    have := Real.rpow_le_rpow_of_exponent_ge hu hu1 he
    rwa [Real.rpow_one] at this
  have h2 : C * u ^ e ≤ max C 0 * u ^ e :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hu.le _)
  have h3 : max C 0 * u ^ e ≤ max C 0 * u := mul_le_mul_of_nonneg_left h1 (le_max_right _ _)
  linarith

/-- **`RemainderParity` from the four analytic leaves** (SP 1316-1318): `b_r` and `b_z` of the
remainder are `O(s^{-(2k+5/2)})` and `O(s^{-(2k+3/2)})` on the chart image (`RingProfileJet`), the
weights cost `w^{-1}`, `w^{-1/2}` (`ParWeightJet`), so the parity coefficients have `n`-th
derivatives `O(w^{2k+3/2-2n})`, `O(w^{2k+1-2n})` (`ParCompWeightJet`), which are `O(w)` for
`n ≤ k`; `HalfSpaceFlatExt` extends them by zero. -/
theorem remainderParity_of (h5 : HalfSpaceFlatExt) (h7 : ParWeightJet) (h8 : RingProfileJet)
    (h9 : ParCompWeightJet) : RemainderParity := by
  intro R hR1 k Φ hΦ hbd
  choose CΦ hCΦ using hbd
  obtain ⟨hg0, hg1, hjet⟩ := h8 R Φ hΦ
  obtain ⟨hw1, hw2, hwjet⟩ := h7 R
  set e : ℝ := -(2 * (k : ℝ) + 1) - 3 / 2 with he
  have hsum : ∀ (i : ℕ) (y : ℝ × (ℝ × ℝ)), 1 ≤ y.1 →
      ∑ l ∈ Finset.range (i + 2), ‖iteratedFDeriv ℝ l Φ y‖ ≤
        (∑ l ∈ Finset.range (i + 2), |CΦ l|) * y.1 ^ e := by
    intro i y hy
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun l _ => (hCΦ l y hy).trans ?_
    exact mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg (by linarith) _)
  have hsum0 : ∀ (i : ℕ) (y : ℝ × (ℝ × ℝ)),
      0 ≤ ∑ l ∈ Finset.range (i + 2), ‖iteratedFDeriv ℝ l Φ y‖ :=
    fun i y => Finset.sum_nonneg fun _ _ => norm_nonneg _
  -- the radial component of the remainder profile on the chart image
  have hb0 : ∀ (i : ℕ) (M : ℝ), ∃ C : ℝ, ∀ y : ℝ × (ℝ × ℝ), 1 ≤ y.1 →
      |y.2.2| ≤ M * Real.sqrt y.1 →
      ‖iteratedFDeriv ℝ i (fun y => UnforcedLeray.Axi.ringStreamProfile R Φ y 0) y‖ ≤
        C * y.1 ^ (-(2 * (k : ℝ) + 5 / 2)) := by
    intro i M
    obtain ⟨C, hC⟩ := hjet i
    refine ⟨|C| * ∑ l ∈ Finset.range (i + 2), |CΦ l|, fun y hy _ => ?_⟩
    have h1 := (hC y (by linarith)).1
    have e' : -(2 * (k : ℝ) + 5 / 2) = e := by rw [he]; ring
    rw [e']
    calc _ ≤ C * ∑ l ∈ Finset.range (i + 2), ‖iteratedFDeriv ℝ l Φ y‖ := h1
      _ ≤ |C| * ∑ l ∈ Finset.range (i + 2), ‖iteratedFDeriv ℝ l Φ y‖ :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (hsum0 i y)
      _ ≤ |C| * ((∑ l ∈ Finset.range (i + 2), |CΦ l|) * y.1 ^ e) :=
          mul_le_mul_of_nonneg_left (hsum i y hy) (abs_nonneg _)
      _ = _ := by ring
  -- the axial component: the factor `1 + |s| + |η| ≤ (2 + |M|) s` costs one power of `s`
  have hb1 : ∀ (i : ℕ) (M : ℝ), ∃ C : ℝ, ∀ y : ℝ × (ℝ × ℝ), 1 ≤ y.1 →
      |y.2.2| ≤ M * Real.sqrt y.1 →
      ‖iteratedFDeriv ℝ i (fun y => UnforcedLeray.Axi.ringStreamProfile R Φ y 1) y‖ ≤
        C * y.1 ^ (-(2 * (k : ℝ) + 3 / 2)) := by
    intro i M
    obtain ⟨C, hC⟩ := hjet i
    refine ⟨|C| * (2 + |M|) * ∑ l ∈ Finset.range (i + 2), |CΦ l|, fun y hy hz => ?_⟩
    have hs0 : 0 < y.1 := by linarith
    have h1 := (hC y hs0).2
    have hsq : Real.sqrt y.1 ≤ y.1 := (Real.sqrt_le_left hs0.le).2 (by nlinarith)
    have hfac : 1 + |y.1| + |y.2.2| ≤ (2 + |M|) * y.1 := by
      rw [abs_of_pos hs0]
      have : |y.2.2| ≤ |M| * y.1 :=
        hz.trans ((mul_le_mul_of_nonneg_right (le_abs_self M) (Real.sqrt_nonneg _)).trans
          (mul_le_mul_of_nonneg_left hsq (abs_nonneg M)))
      nlinarith
    have hpow : y.1 * y.1 ^ e = y.1 ^ (-(2 * (k : ℝ) + 3 / 2)) := by
      rw [mul_comm, ← Real.rpow_add_one hs0.ne', he]
      ring_nf
    calc _ ≤ C * (1 + |y.1| + |y.2.2|) * ∑ l ∈ Finset.range (i + 2), ‖iteratedFDeriv ℝ l Φ y‖ :=
          h1
      _ ≤ |C| * (1 + |y.1| + |y.2.2|) * ∑ l ∈ Finset.range (i + 2), ‖iteratedFDeriv ℝ l Φ y‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)) (hsum0 i y)
      _ ≤ |C| * ((2 + |M|) * y.1) * ((∑ l ∈ Finset.range (i + 2), |CΦ l|) * y.1 ^ e) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hfac (abs_nonneg _)) (hsum i y hy) (hsum0 i y)
            (by positivity)
      _ = |C| * (2 + |M|) * (∑ l ∈ Finset.range (i + 2), |CΦ l|) * (y.1 * y.1 ^ e) := by ring
      _ = _ := by rw [hpow]
  have hk0 : (0 : ℝ) ≤ 2 * (k : ℝ) + 5 / 2 := by positivity
  have hk1 : (0 : ℝ) ≤ 2 * (k : ℝ) + 3 / 2 := by positivity
  obtain ⟨hGs, hGb⟩ := h9 R 1 (2 * (k : ℝ) + 5 / 2) (fun x => R / x.2.1)
    (fun y => UnforcedLeray.Axi.ringStreamProfile R Φ y 0) hR1 hk0 hw1 hg0
    (fun n => by
      obtain ⟨C, hC⟩ := hwjet n
      exact ⟨C, fun x hx hx1 i hi => (hC x hx hx1 i hi).1⟩) hb0
  obtain ⟨hHs, hHb⟩ := h9 R (1 / 2) (2 * (k : ℝ) + 3 / 2) (fun x => R / Real.sqrt x.2.1)
    (fun y => UnforcedLeray.Axi.ringStreamProfile R Φ y 1) hR1 hk1 hw2 hg1
    (fun n => by
      obtain ⟨C, hC⟩ := hwjet n
      exact ⟨C, fun x hx hx1 i hi => (hC x hx hx1 i hi).2⟩) hb1
  refine ⟨?_, ?_⟩
  · refine h5 k ℝ (parG R (UnforcedLeray.Axi.ringStreamProfile R Φ)) (contDiffOn_infty.1 hGs k) ?_
    intro n hn M
    obtain ⟨C, hC⟩ := hGb n M
    refine ⟨max C 0, fun x hx hx1 hz => ?_⟩
    have hn' : (n : ℝ) ≤ k := by exact_mod_cast hn
    exact le_mul_of_rpow_bound hx hx1 (by linarith) (hC x hx hx1 hz)
  · refine h5 k ℝ (parH R (UnforcedLeray.Axi.ringStreamProfile R Φ)) (contDiffOn_infty.1 hHs k) ?_
    intro n hn M
    obtain ⟨C, hC⟩ := hHb n M
    refine ⟨max C 0, fun x hx hx1 hz => ?_⟩
    have hn' : (n : ℝ) ≤ k := by exact_mod_cast hn
    exact le_mul_of_rpow_bound hx hx1 (by linarith) (hC x hx hx1 hz)

/-! ## The parity form from the expansion -/

/-- The parity chart lands in positive age. -/
theorem parChart_fst_pos {R : ℝ} (hR : 0 < R) {x : ℝ × (ℝ × ℝ)} (hx : 0 < x.2.1) :
    (parChart R x) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)) :=
  Set.mk_mem_prod (show 0 < R ^ 2 / x.2.1 by positivity) (Set.mem_univ _)

theorem differentiableAt_of_contDiffOn_pos {f : ℝ × (ℝ × ℝ) → ℝ}
    (hf : ContDiffOn ℝ ∞ f (Ioi 0 ×ˢ univ)) {y : ℝ × (ℝ × ℝ)}
    (hy : y ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ))) : DifferentiableAt ℝ f y :=
  (hf.contDiffAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds hy)).differentiableAt (by simp)

/-- **`ParityOfExpansion` from the heat-term and remainder leaves** (SP 1310-1319): for every `n`,
take `N = 2n + 1`; on `w > 0` the parity coefficients of `Ψ` are the polynomial heat parts plus
those of the remainder, at `w = 0` only the `j = 0` heat part survives, so `G` agrees on `w ≥ 0`
with a `C^n` function. -/
theorem parityOfExpansion_of (h3 : HeatTermSmooth) (h4 : HeatTermParity)
    (hR : RemainderParity) : ParityOfExpansion := by
  intro ν R hν hR1 a Ψ hΨ hbd
  have hR0 : 0 < R := lt_of_lt_of_le one_pos hR1
  -- the remainders are smooth for positive age
  have hrem : ∀ N, ContDiffOn ℝ ∞ (heatRemainder ν a N Ψ) (Ioi 0 ×ˢ univ) := fun N =>
    hΨ.sub (ContDiffOn.sum fun j _ => contDiffOn_const.mul (h3 ν hν j))
  -- the decomposition off the axis
  have hdec : ∀ (N : ℕ) (x : ℝ × (ℝ × ℝ)), 0 < x.2.1 →
      parG R (UnforcedLeray.Axi.ringStreamProfile R Ψ) x =
          ∑ j ∈ Finset.range (N + 1), a j * heatParG ν R j x +
            parG R (UnforcedLeray.Axi.ringStreamProfile R (heatRemainder ν a N Ψ)) x ∧
        parH R (UnforcedLeray.Axi.ringStreamProfile R Ψ) x =
          ∑ j ∈ Finset.range (N + 1), a j * heatParH ν R j x +
            parH R (UnforcedLeray.Axi.ringStreamProfile R (heatRemainder ν a N Ψ)) x := by
    intro N x hx
    have hy := parChart_fst_pos hR0 hx
    have hΨd : DifferentiableAt ℝ Ψ (parChart R x) := differentiableAt_of_contDiffOn_pos hΨ hy
    have hTd : ∀ j, DifferentiableAt ℝ (heatTerm ν j) (parChart R x) := fun j =>
      differentiableAt_of_contDiffOn_pos (h3 ν hν j) hy
    have hG : ∀ j ∈ Finset.range (N + 1), a j * heatParG ν R j x =
        R / x.2.1 * (a j * UnforcedLeray.Axi.ringStreamProfile R (heatTerm ν j) (parChart R x) 0) :=
      fun j _ => by rw [← (h4 ν R hν hR0 j x hx).1, parG]; ring
    have hH : ∀ j ∈ Finset.range (N + 1), a j * heatParH ν R j x =
        R / Real.sqrt x.2.1 *
          (a j * UnforcedLeray.Axi.ringStreamProfile R (heatTerm ν j) (parChart R x) 1) :=
      fun j _ => by rw [← (h4 ν R hν hR0 j x hx).2, parH]; ring
    refine ⟨?_, ?_⟩
    · rw [Finset.sum_congr rfl hG, ← Finset.mul_sum]
      simp only [parG]
      rw [ringStreamProfile_heatRemainder R ν a N hΨd hTd 0]
      ring
    · rw [Finset.sum_congr rfl hH, ← Finset.mul_sum]
      simp only [parH]
      rw [ringStreamProfile_heatRemainder R ν a N hΨd hTd 1]
      ring
  -- the remainder bounds at the odd orders `N = 2n + 1`
  have hbdN : ∀ n i : ℕ, ∃ C : ℝ, ∀ y : ℝ × (ℝ × ℝ), 1 ≤ y.1 →
      ‖iteratedFDeriv ℝ i (heatRemainder ν a (2 * n + 1) Ψ) y‖ ≤
        C * y.1 ^ (-(2 * (n : ℝ) + 1) - 3 / 2) := by
    intro n i
    obtain ⟨C, hC⟩ := hbd (2 * n + 1) i
    refine ⟨C, fun y hy => ?_⟩
    have e : (-((2 * n + 1 : ℕ) : ℝ) - 3 / 2) = -(2 * (n : ℝ) + 1) - 3 / 2 := by push_cast; ring
    rw [← e]
    exact hC y hy
  refine ⟨fun x => if 0 < x.2.1 then parG R (UnforcedLeray.Axi.ringStreamProfile R Ψ) x
      else ∑ j ∈ Finset.range (0 + 1), a j * heatParG ν R j x,
    fun x => if 0 < x.2.1 then parH R (UnforcedLeray.Axi.ringStreamProfile R Ψ) x
      else ∑ j ∈ Finset.range (0 + 1), a j * heatParH ν R j x, ?_, ?_, ?_⟩
  · rw [contDiffOn_infty]
    intro n
    have hP : ContDiff ℝ n (fun x => ∑ j ∈ Finset.range (2 * n + 1 + 1), a j * heatParG ν R j x) :=
      (ContDiff.sum fun j _ => contDiff_const.mul (contDiff_heatParG ν R j)).of_le
        (by exact_mod_cast le_top)
    have hE := (hR R hR1 n (heatRemainder ν a (2 * n + 1) Ψ) (hrem _) (hbdN n)).1
    refine (hP.add hE).contDiffOn.congr ?_
    intro x hx
    by_cases hw : 0 < x.2.1
    · simp only [hw, ↓reduceIte, zeroExtW]
      exact (hdec (2 * n + 1) x hw).1
    · have hw0 : x.2.1 = 0 := le_antisymm (not_lt.1 hw) hx
      simp only [hw, ↓reduceIte, zeroExtW, add_zero]
      exact (sum_heatParG_of_eq_zero ν R a (2 * n + 1) hw0).symm
  · rw [contDiffOn_infty]
    intro n
    have hP : ContDiff ℝ n (fun x => ∑ j ∈ Finset.range (2 * n + 1 + 1), a j * heatParH ν R j x) :=
      (ContDiff.sum fun j _ => contDiff_const.mul (contDiff_heatParH ν R j)).of_le
        (by exact_mod_cast le_top)
    have hE := (hR R hR1 n (heatRemainder ν a (2 * n + 1) Ψ) (hrem _) (hbdN n)).2
    refine (hP.add hE).contDiffOn.congr ?_
    intro x hx
    by_cases hw : 0 < x.2.1
    · simp only [hw, ↓reduceIte, zeroExtW]
      exact (hdec (2 * n + 1) x hw).2
    · have hw0 : x.2.1 = 0 := le_antisymm (not_lt.1 hw) hx
      simp only [hw, ↓reduceIte, zeroExtW, add_zero]
      exact (sum_heatParH_of_eq_zero ν R a (2 * n + 1) hw0).symm
  · intro x hx
    have hx' : 0 < x.2.1 := hx
    simp only [hx', ↓reduceIte, and_self]

/-! ## The parity form of `U_raw` -/

/-- In the regime `ε = e^{-d/ν}` with `d > 0`, `R = ε⁻¹ ≥ 1`. -/
theorem one_le_R_of_regime {p : Params} {d dm dp : ℝ} (hreg : BgRegime p d dm dp) : 1 ≤ p.R := by
  have hd : 0 < d := lt_of_lt_of_le hreg.dm_pos hreg.dm_le
  have hle : p.ε ≤ 1 := by
    rw [hreg.eps_eq, Real.exp_le_one_iff]
    exact (div_neg_of_neg_of_pos (neg_lt_zero.2 hd) p.ν_pos).le
  exact (one_le_inv₀ p.ε_pos).2 hle

/-- **`PartII-b:G4/4/1/1/2/1`, conditional form**: the parity form of `U_raw` from the all-age
heat expansion of the train (`TrainHeatExpansion` at `ρ = 2`, `c = ν⁻²`), the identification of
the raw profile with the ring stream profile (`RawStreamProfile`) and the analytic statement
`ParityOfExpansion`. -/
theorem rawParityForm_of (h1 : TrainHeatExpansion) (h2 : RawStreamProfile)
    (hP : ParityOfExpansion) : RawParityForm := by
  intro Sig lam q hSig hq dm dp hdm
  obtain ⟨ν₀, hν₀, H⟩ := h1 2 (by norm_num)
  refine ⟨ν₀, hν₀, ?_⟩
  intro p d hreg hν _ _ _
  have hR1 : 1 ≤ p.R := one_le_R_of_regime hreg
  have hR0 : 0 < p.R := p.R_pos
  have hc : p.c = UnforcedLeray.Short.PartI.trainPeriod 2 p.ν := by
    rw [hreg.c_eq, UnforcedLeray.Short.PartI.trainPeriod, Real.rpow_neg p.ν_pos.le, Real.rpow_two]
  have hΨ : ContDiffOn ℝ ∞ (fun y : ℝ × (ℝ × ℝ) => p.train.ψ y.1 y.2) (Ioi 0 ×ˢ univ) :=
    hreg.train_stream_smooth
  obtain ⟨G, Hh, hG, hH, hGH⟩ := hP p.ν p.R p.ν_pos hR1
    (UnforcedLeray.Short.PartI.meanCoeff p.train) (fun y => p.train.ψ y.1 y.2) hΨ
    (H p.ν p.c p.ν_pos hν hc p.train hreg.train_buc)
  refine ⟨G, Hh, hG, hH, ?_⟩
  intro τ y hy
  have hw : 0 < y 0 ^ 2 + y 1 ^ 2 := by
    rw [← UnforcedLeray.Axi.ϱ_sq]
    exact pow_pos (UnforcedLeray.Axi.ϱ_pos hy) 2
  have hxpos : ((τ, (y 0 ^ 2 + y 1 ^ 2, y 2)) : ℝ × (ℝ × ℝ)) ∈ parPos := hw
  have hε : p.ε = p.R⁻¹ := (inv_inv p.ε).symm
  have hb : UnforcedLeray.Cons.C03.rawProfile p.ε p.train.v p.train.ψ
        (parChart p.R (τ, (y 0 ^ 2 + y 1 ^ 2, y 2))) =
      UnforcedLeray.Axi.ringStreamProfile p.R (fun y => p.train.ψ y.1 y.2)
        (parChart p.R (τ, (y 0 ^ 2 + y 1 ^ 2, y 2))) := by
    rw [hε]
    exact h2 p.ν p.c p.R p.train hR0 hreg.train_stream_smooth _ (parChart_fst_pos hR0 hw).1
  obtain ⟨hGx, hHx⟩ := hGH _ hxpos
  rw [p.raw_eq_off_axis τ y hy]
  change UnforcedLeray.Axi.Nv p.R _ τ y = _
  rw [Nv_eq_parity hR0 _ τ hy, hGx, hHx]
  simp only [parG, parH, hb]

end UnforcedLeray.Short.IIb
