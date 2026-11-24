import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEqSub

/-!
# `GELin`: concrete objects for the linear term (source 2525-2533, `U_raw` bounds 1217-1219)

Task `PartIII-b:C/ward/12/3/1/2/6/org`.  Source of record
`the November 2 reference manuscript`.

For `Ψ = ∂_jΦ` the linear term is `⟨convT raw Ψ, w⟩` with
`(convT V Ψ)_k = ∑ᵢ Ψᵢ ∂ₖVᵢ - ∑ₘ Vₘ ∂ₘΨₖ`.  Since `∂_j(convT V Φ) = convT (∂_jV) Φ + convT V ∂_jΦ`,
and for a smooth periodic real `V` and `v` with distributional derivatives `∂ₘv = v'ₘ`
(`HasPhaseOp (-dy m) v (v' m)`) one has `⟨convT V Φ, v⟩ = ⟨Φ, S(V, v, v')⟩` where
`S(V,v,v')ᵢ = ∑ₖ ∂ₖVᵢ vₖ + ∑ₘ (∂ₘVₘ vᵢ + Vₘ (v'ₘ)ᵢ)`, one gets (no use of `div V = 0`)
`⟨convT raw ∂_jΦ, w⟩ = -⟨Φ, S(raw, w, g)⟩`-type formula, precisely
`⟨convT raw ∂_jΦ, w⟩ = -⟨Φ, S(raw, g_j, h_j)⟩ - ⟨Φ, S(∂_j raw, w, g)⟩`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace MeasureTheory Set
open scoped ContDiff
open UnforcedLeray.Cons.C03.Concrete (Params IsSolTest pairF convT advT rep)

/-- `∂_k raw` at `(τ, y)`, as a real vector. -/
def rawD (p : Params) (k : Fin 3) (x : ℝ × UnforcedLeray.Space) : UnforcedLeray.Space :=
  fderiv ℝ (p.raw x.1) x.2 (EuclideanSpace.single k 1)

/-- `∂_j ∂_k raw` at `(τ, y)` (outer derivative `j`, inner `k`), as a real vector. -/
def rawDD (p : Params) (j k : Fin 3) (x : ℝ × UnforcedLeray.Space) : UnforcedLeray.Space :=
  fderiv ℝ (fun y => fderiv ℝ (p.raw x.1) y (EuclideanSpace.single k 1)) x.2
    (EuclideanSpace.single j 1)

/-- **Smoothness, periodicity and global bounds of the derivatives of `U_raw`** (source 1217-1219:
`U_R` has period `2c/R` and globally bounded fixed spatial derivatives; smooth through the
axis for positive time, 1214, 1305-1325): in the background regime, `(τ,y) ↦ raw τ y` is `C^∞`,
`p.period`-periodic in `τ`, and for each order `k = 0, 1, 2` (`k : Fin 3`: the orders that enter
`GELinField`, namely `raw`, `rawD`, `rawDD`) the `k`-th spatial derivative is bounded uniformly in
`(τ, y)`.  Only these orders are stated, so the fact follows from `RingBoundedDerivs` at the
single order `2` (one threshold `ν₀`). -/
def RawSmoothBdd : Prop :=
  ∀ dm dp : ℝ, 0 < dm → ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      ContDiff ℝ ∞ (fun x : ℝ × UnforcedLeray.Space => p.raw x.1 x.2) ∧
      (∀ τ y, p.raw (τ + p.period) y = p.raw τ y) ∧
      ∀ k : Fin 3, ∃ C : ℝ, ∀ (τ : ℝ) (y : UnforcedLeray.Space),
        ‖iteratedFDeriv ℝ (k : ℕ) (p.raw τ) y‖ ≤ C

/-- **The pointwise field of the linear term.**  With `G = rep (g j)`, `H m = rep (h j m)`,
`W = rep w`, `Gm = rep (g m)`:
`F_i = -[∑ₖ ∂ₖU_i G_k + ∑ₘ (∂ₘU_m G_i + U_m (H m)_i)]
       -[∑ₖ ∂ₖ∂_jU_i W_k + ∑ₘ (∂ₘ∂_jU_m W_i + ∂_jU_m (Gm)_i)]`. -/
def GELinField (p : Params) (z : p.Z)
    (g : Fin 3 → Yq p.period UnforcedLeray.B0412.q0E)
    (h : Fin 3 → Fin 3 → Yq p.period UnforcedLeray.B0412.q0E) (j : Fin 3)
    (x : ℝ × UnforcedLeray.Space) : UnforcedLeray.PhaseSpace.CVec3 :=
  WithLp.toLp 2 fun i =>
    -((∑ k : Fin 3, ((rawD p k x i : ℝ) : ℂ) * rep (g j) x.1 x.2 k +
        ∑ m : Fin 3, (((rawD p m x m : ℝ) : ℂ) * rep (g j) x.1 x.2 i +
          ((p.raw x.1 x.2 m : ℝ) : ℂ) * rep (h j m) x.1 x.2 i)) +
      (∑ k : Fin 3, ((rawDD p k j x i : ℝ) : ℂ) * rep (p.wOf z) x.1 x.2 k +
        ∑ m : Fin 3, (((rawDD p m j x m : ℝ) : ℂ) * rep (p.wOf z) x.1 x.2 i +
          ((rawD p j x m : ℝ) : ℂ) * rep (g m) x.1 x.2 i)))

end UnforcedLeray.Short.PartIIIb.Concrete
