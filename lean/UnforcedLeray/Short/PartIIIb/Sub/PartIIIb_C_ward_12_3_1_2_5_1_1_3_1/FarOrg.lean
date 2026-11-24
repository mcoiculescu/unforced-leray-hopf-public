import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3

/-!
# Far field of the inlet source: corrected design (organizer task
`PartIII-b:C/ward/12/3/1/2/5/1/1/3/1/1`)

Source `the November 2 reference manuscript`
lines 1206-1222 (ring lift `u = (R/r)(v₁, v₂ + εH)` at `q = R log(r/R)`, `η = Rz/r`,
`s = R²t/r²`; smooth, discretely self-similar, globally bounded fixed derivatives),
2542-2549 (large radius: the *complete sources* have unprojected derivatives
`C_{k,N} ϱ^{-3-k}(1+|y₃|/ϱ)^{-N}`; uniform in phase), 2563-2569.

## Why the earlier leaf `InletEFarJets` is replaced

`InletEFarJets` (in `Sub/PartIII-b_C_ward_12_3_1_2_5_1_1_3_1.lean`) asks for
`‖D^k E‖ ≤ C ϱ^{-3-k}(1+|y₃|/ϱ)^{-N}` for the inlet `E = N_v e` itself.  That is false: for
`ϱ² > 4R²/H` the age cutoff is `1`, so the profile `e(s, ξ, η) = e₀(ξ, η)` does not depend on `s`
and `|E(τ, y)| = (R/ϱ) |e₀(ξ, η)|` with `ξ` sweeping a whole period as `τ` runs over `(0, P]`;
since the frozen stream is not identically zero, `sup_τ |E(τ, (ϱ,0,0))| ≥ c/ϱ`.  The `ϱ^{-3-k}`
bound of the source is for the *complete source* `L₀E + B_raw E`, and it comes from

* the homogeneity of degree `-1` of `E` (`InletEFarHom`: `‖D^k E‖ ≤ C ϱ^{-1-k}(1+|y₃|/ϱ)^{-N}`),
* the exact cancellation `(T₀ - ½)E = 0` of the drift on the far region, where `E` is
  `s`-independent (`InletDriftFar`; `T₀(√s b) = √s(s∂_s + ½)b`, source 3754-type identity), so
  that there `L₀E = -νΔE`,
* the same homogeneity for the raw field: `‖D^k raw‖ ≤ C ϱ^{-1-k}(1+|y₃|/ϱ)^M` (`RawFarJets`).

Then each term of `F = -∂_j(L₀E + (raw·∇)E + (E·∇)raw)` is `O(ϱ^{-4}(1+|y₃|/ϱ)^{M-N})`
(`InletFnFarOfHom`), which gives `InletFnFarDecay`.

## The chart-to-Cartesian comparison

`ChartLiftJets`: for a profile `b` smooth on `s > 0` and `ϱ ≥ R`, the Cartesian jets of the ring
lift `N_v b = √s (b_r e_r + b_z e_z)` at the chart point `(s, ξ, η) = (R²/ϱ², Rτ/2 + R log(ϱ/R),
Ry₃/ϱ)` satisfy `‖D^k N_v b‖ ≤ K ϱ^{-1-k}(1+|y₃|/ϱ)^k ∑_{l ≤ k} ‖D^l b‖`, `k ≤ 3`.  It is split
into a general homogeneity lemma (`HomogJets`), the chart jets (`AgeJet`, `PhaseJet`, `TransJet`,
`ChartJetBound`), the jets of the lift factor `√s · frame` (`LiftFactorJet`), Faà di Bruno
(`norm_iteratedFDerivWithin_comp_le`) and Leibniz (`norm_iteratedFDerivWithin_clm_apply`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ContDiff
open UnforcedLeray.Cons.C03.Concrete (Params)

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-! ## The chart-to-Cartesian comparison (pure calculus) -/

/-- The lift factor `y ↦ √s · frame_y`, `s = R²/ϱ²`, as a map into `Merid →L[ℝ] ℝ³`:
`N_v b (τ, y) = liftFactor R y (b (chart R τ y))` (`Nv_eq_liftFactor`). -/
def liftFactor (R : ℝ) (y : UnforcedLeray.Space) : Axi.Merid →L[ℝ] UnforcedLeray.Space :=
  √(Axi.age R y) • Axi.frameL y

theorem Nv_eq_liftFactor (R : ℝ) (b : ℝ × (ℝ × ℝ) → Axi.Merid) (τ : ℝ)
    (y : UnforcedLeray.Space) :
    Axi.Nv R b τ y = liftFactor R y (b (Axi.chart R τ y)) := by
  simp [liftFactor, Axi.Nv]

/-- **Homogeneous jets** (pure calculus; used for `s = R²/ϱ²`, `ξ`, `1/ϱ` and `√s·frame`, which
depend on `y` only through `(y₀, y₁)` and are homogeneous of degree `d` up to an additive
constant): if `f` is `C^∞` off the axis, invariant under axial translations off the axis, and
`f(λy) = λ^d f(y) + g(λ)` for `λ > 0` off the axis, then `‖D^m f(y)‖ ≤ C ϱ^{d-m}` for `m ≥ 1`.
(Proof: `D^m f(λy) = λ^{d-m} D^m f(y)` from the scaling identity on the open set `axisᶜ`
(`ContinuousLinearMap.iteratedFDerivWithin_comp_right` with `λ • id`, the constant `g λ` drops);
axial invariance moves `y` to `hor y`; `hor y = ϱ • u` with `u` on the unit circle of the plane
`y₂ = 0`, a compact subset of `axisᶜ` on which `D^m f` is continuous.) -/
def HomogJets : Prop :=
  ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] (f : UnforcedLeray.Space → F) (d : ℝ)
    (g : ℝ → F), ContDiffOn ℝ ∞ f Axi.axisᶜ →
    (∀ y : UnforcedLeray.Space, y ∉ Axi.axis → ∀ t : ℝ, f (y + t • Axi.e3) = f y) →
    (∀ lam : ℝ, 0 < lam → ∀ y : UnforcedLeray.Space, y ∉ Axi.axis →
      f (lam • y) = lam ^ d • f y + g lam) →
    ∀ m : ℕ, 1 ≤ m → ∃ C : ℝ, 0 ≤ C ∧ ∀ y : UnforcedLeray.Space, y ∉ Axi.axis →
      ‖iteratedFDeriv ℝ m f y‖ ≤ C * Axi.ϱ y ^ (d - m)

/-- **Jets of the age** `s = R²/ϱ²` (homogeneous of degree `-2`; source 1208-1210). -/
def AgeJet : Prop :=
  ∀ R : ℝ, 0 < R → ∀ m : ℕ, 1 ≤ m → ∃ C : ℝ, 0 ≤ C ∧ ∀ y : UnforcedLeray.Space, y ∉ Axi.axis →
    ‖iteratedFDeriv ℝ m (Axi.age R) y‖ ≤ C * Axi.ϱ y ^ (-(2 + (m : ℝ)))

/-- **Jets of the phase** `ξ = Rτ/2 - (R/2) log s = Rτ/2 + R log(ϱ/R)` (`ξ(λy) = ξ(y) + R log λ`;
source 1208-1210); the constant is uniform in `τ`. -/
def PhaseJet : Prop :=
  ∀ R : ℝ, 0 < R → ∀ m : ℕ, 1 ≤ m → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (τ : ℝ) (y : UnforcedLeray.Space), y ∉ Axi.axis →
      ‖iteratedFDeriv ℝ m (Axi.phase R τ) y‖ ≤ C * Axi.ϱ y ^ (-(m : ℝ))

/-- **Jets of the transverse coordinate** `η = R y₃/ϱ` (Leibniz: `y₃` is linear, `1/ϱ` is
homogeneous of degree `-1`; source 1208-1210). -/
def TransJet : Prop :=
  ∀ R : ℝ, 0 < R → ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ y : UnforcedLeray.Space, y ∉ Axi.axis →
    ‖iteratedFDeriv ℝ m (Axi.trans R) y‖ ≤
      C * Axi.ϱ y ^ (-(m : ℝ)) * (1 + |y 2| / Axi.ϱ y)

/-- **Jets of the chart** `y ↦ (s, ξ, η)` on `ϱ ≥ R`, in the form required by Faà di Bruno
(`norm_iteratedFDerivWithin_comp_le`): `‖D^m chart‖ ≤ D^m` with `D = K(1+|y₃|/ϱ)/ϱ`. -/
def ChartJetBound : Prop :=
  ∀ R : ℝ, 0 < R → ∃ K : ℝ, 0 < K ∧ ∀ (τ : ℝ) (y : UnforcedLeray.Space), R ≤ Axi.ϱ y →
    ∀ m : ℕ, 1 ≤ m → m ≤ 3 →
      ‖iteratedFDeriv ℝ m (Axi.chart R τ) y‖ ≤ (K * (1 + |y 2| / Axi.ϱ y) / Axi.ϱ y) ^ m

/-- **Jets of the lift factor** `√s · frame` (homogeneous of degree `-1`; source 1212-1216). -/
def LiftFactorJet : Prop :=
  ∀ R : ℝ, 0 < R → ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ y : UnforcedLeray.Space, y ∉ Axi.axis →
    ‖iteratedFDeriv ℝ m (liftFactor R) y‖ ≤ C * Axi.ϱ y ^ (-(1 + (m : ℝ)))

/-- **Chart-to-Cartesian comparison for the ring lift** (source 1206-1222, 2542-2546): for a
profile `b` that is `C^∞` on `s > 0`, and `ϱ ≥ R`,
`‖D^k (N_v b)(τ, y)‖ ≤ K ϱ^{-1-k}(1+|y₃|/ϱ)^k ∑_{l ≤ k} ‖D^l b (chart R τ y)‖`, `k ≤ 3`. -/
def ChartLiftJets : Prop :=
  ∀ R : ℝ, 0 < R → ∃ K : ℝ, 0 < K ∧
    ∀ (b : ℝ × (ℝ × ℝ) → Axi.Merid), ContDiffOn ℝ ∞ b {m : ℝ × (ℝ × ℝ) | 0 < m.1} →
    ∀ (τ : ℝ) (y : UnforcedLeray.Space), R ≤ Axi.ϱ y → ∀ k : ℕ, k ≤ 3 →
      ‖iteratedFDeriv ℝ k (Axi.Nv R b τ) y‖ ≤
        K * Axi.ϱ y ^ (-(1 + (k : ℝ))) * (1 + |y 2| / Axi.ϱ y) ^ k *
          ∑ l ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ l b (Axi.chart R τ y)‖

/-! ## The inlet -/

/-- **Chart jets of the inlet profile of every order, with transverse decay** (source 2347-2369;
all-order version of `IIb.InletJetDecay`, same proof as `IIb.inletJetDecay_of` with the order `2`
replaced by `j`, constants depending on `p`). -/
def InletJetAll : Prop :=
  ∀ (lam : ℂ) (q : UnforcedLeray.Blueprint.Planar.Profile),
    UnforcedLeray.Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ (p : Params), p.mode = q → 1 ≤ p.c → 1 ≤ p.R → ∀ (i : Fin 2) (j : ℕ),
    ∃ C κ : ℝ, 0 < κ ∧ ContDiff ℝ ∞ (p.inletProfile i) ∧
      ∀ l ≤ j, ∀ m : ℝ × (ℝ × ℝ),
        ‖iteratedFDeriv ℝ l (p.inletProfile i) m‖ ≤ C * Real.exp (-(κ * |m.2.2|))

/-- **Far-field jets of the inlet, homogeneity `-1`** (source 2542-2549, 1206-1222; corrected
form of `InletEFarJets`): spatial derivatives of order `k ≤ 3` of `E = p.Efun i` are bounded by
`C ϱ^{-1-k}(1+|y₃|/ϱ)^{-N}` for `ϱ > R₀`, for every phase `τ`. -/
def InletEFarHom : Prop := GERegime fun p _ _ =>
  ∀ (i : Fin 2) (N : ℕ), ∃ C R0 : ℝ, 0 < R0 ∧
    ∀ (τ : ℝ) (y : UnforcedLeray.Space), R0 < Axi.ϱ y → ∀ k : ℕ, k ≤ 3 →
      ‖iteratedFDeriv ℝ k (fun x : UnforcedLeray.Space => p.Efun i (τ, x)) y‖ ≤
        C * (Axi.ϱ y ^ (-(1 + (k : ℝ))) * (1 + |y 2| / Axi.ϱ y) ^ (-(N : ℝ)))

/-- **Exact drift cancellation in the far field** (source 2542-2549; the age cutoff equals one for
`s ≤ H/4`, i.e. `ϱ ≥ 2R/√H`, where the inlet profile is `s`-independent, so `E(τ + 2 log λ, y) =
λ E(τ, λy)` and `(T₀ - ½)E = ∂_τE - ½ y·∇E - ½E = 0`; equivalently `L₀E = -νΔE` there). -/
def InletDriftFar : Prop := GERegime fun p _ _ =>
  ∀ i : Fin 2, ∃ R0 : ℝ, 0 < R0 ∧ ∀ (τ : ℝ) (y : UnforcedLeray.Space), R0 < Axi.ϱ y →
    UnforcedLeray.PhaseSpace.dτ (p.Efun i) (τ, y) -
        (1 / 2 : ℝ) • UnforcedLeray.PhaseSpace.radialT (p.Efun i) (τ, y) -
        (1 / 2 : ℝ) • p.Efun i (τ, y) = 0

/-! ## The raw field -/

/-- **Chart jets of the raw profile near age zero** (source 1206-1222: `b_raw = (v₁, v₂ + εH)`,
`H = (1-K)ψ`; the train and its stream are smooth for `s > 0` (SP 397, 2049, `BgRegime`) with all
mixed age/space jets bounded at fixed parameters (SP 427-446, `PartI.TrainJetsBoundedFixed`,
`PartI.TrainFluctAgeJetFixed`), the weight `η` of `K = η∂_η + 2s∂_s` costing a polynomial
factor): `b_raw` is `C^∞` on `s > 0` and its jets of order `≤ 2` are `≤ C(1+|η|)^M` on
`0 < s ≤ s₀`. -/
def RawProfFarJet : Prop :=
  ∀ dm dp : ℝ, 0 < dm → ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      ContDiffOn ℝ ∞ (UnforcedLeray.Cons.C03.rawProfile p.ε p.train.v p.train.ψ)
          {m : ℝ × (ℝ × ℝ) | 0 < m.1} ∧
      ∃ (C s0 : ℝ) (M : ℕ), 0 < s0 ∧ ∀ m : ℝ × (ℝ × ℝ), 0 < m.1 → m.1 ≤ s0 → ∀ l ≤ 2,
        ‖iteratedFDeriv ℝ l (UnforcedLeray.Cons.C03.rawProfile p.ε p.train.v p.train.ψ) m‖ ≤
          C * (1 + |m.2.2|) ^ M

/-- **Far-field jets of the raw field, homogeneity `-1`** (source 1206-1222, 2542-2546): `raw` is
jointly `C^∞` on the far region and `‖D^k raw(τ)(y)‖ ≤ C ϱ^{-1-k}(1+|y₃|/ϱ)^M` for `k ≤ 2`,
`ϱ > R₀`, every `τ` (from `ChartLiftJets` and `RawProfFarJet`; `raw = N_v b_raw` off the axis). -/
def RawFarJets : Prop :=
  ∀ dm dp : ℝ, 0 < dm → ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      ∃ (C R0 : ℝ) (M : ℕ), 0 < R0 ∧
        ContDiffOn ℝ ∞ (fun x : ℝ × UnforcedLeray.Space => p.raw x.1 x.2)
          {x : ℝ × UnforcedLeray.Space | R0 < Axi.ϱ x.2} ∧
        ∀ (τ : ℝ) (y : UnforcedLeray.Space), R0 < Axi.ϱ y → ∀ k : ℕ, k ≤ 2 →
          ‖iteratedFDeriv ℝ k (p.raw τ) y‖ ≤
            C * (Axi.ϱ y ^ (-(1 + (k : ℝ))) * (1 + |y 2| / Axi.ϱ y) ^ M)

/-! ## The product rule and the assembly -/

/-- **Spatial phase-space derivatives are slice derivatives** (pure calculus): for `G` smooth on
an open set `U ∋ x`, `‖∂_jG(x)‖`, `‖∂_j∂_kG(x)‖`, `‖∂_j∂_k∂_lG(x)‖` are bounded by the norms of
the first, second, third derivatives of the slice `G(x.1, ·)` at `x.2`. -/
def SliceBridge : Prop :=
  ∀ (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F] (G : ℝ × UnforcedLeray.Space → F)
    (U : Set (ℝ × UnforcedLeray.Space)), IsOpen U → ContDiffOn ℝ ∞ G U →
    ∀ x ∈ U, ∀ j k l : Fin 3,
      ‖UnforcedLeray.PhaseSpace.dy j G x‖ ≤
          ‖iteratedFDeriv ℝ 1 (fun y => G (x.1, y)) x.2‖ ∧
        ‖UnforcedLeray.PhaseSpace.dy j (UnforcedLeray.PhaseSpace.dy k G) x‖ ≤
          ‖iteratedFDeriv ℝ 2 (fun y => G (x.1, y)) x.2‖ ∧
        ‖UnforcedLeray.PhaseSpace.dy j (UnforcedLeray.PhaseSpace.dy k
            (UnforcedLeray.PhaseSpace.dy l G)) x‖ ≤
          ‖iteratedFDeriv ℝ 3 (fun y => G (x.1, y)) x.2‖

/-- **Far product rule** (source 2542-2549, 2563-2569): on `ϱ > R₀`,
`F = -∂_j(L₀E + (raw·∇)E + (E·∇)raw)` with `∂_jL₀E = -ν∂_jΔE` (`InletDriftFar`, the drift vanishes
on an open set), and every term `O(ϱ^{-4}(1+|y₃|/ϱ)^{M-N})`; take `N = M + 2`. -/
def InletFnFarOfHom : Prop := InletEFarHom → InletDriftFar → RawFarJets → InletFnFarDecay

theorem inletFnFarDecay_of_hom (hP : InletFnFarOfHom) (h1 : InletEFarHom)
    (h2 : InletDriftFar) (h3 : RawFarJets) : InletFnFarDecay :=
  hP h1 h2 h3

end UnforcedLeray.Short.PartIIIb.Concrete
