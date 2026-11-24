import UnforcedLeray.Short.PartIIb.Defs
import UnforcedLeray.Short.PartIIb.StatementsFree
import UnforcedLeray.Lib.Train.PeriodizedVortex

/-!
# Part II-b, module `background/short-background.tex`, first half (SP 2026-2344): statements

The ordinary mixed solve and the completion for arbitrary body forces: elementary Hardy
estimates (`short-bg:hardy`), the graph-transform lemma (`short-bg:graphs`), the free cylinder
bound (`short-bg:free-cylinder`), and the flat augmented inverse (`short-bg:flat-inverse`) for the
actual flat interaction `K_0` and inlet column `𝒞_0`.

**Interface note (Part I frozen pair).** The cylinder block factorization, the intermediate-time
projections and the Green selector `short-bg:green`, `short-bg:green-bound`, together with the
estimates `short-bg:early`, `short-bg:global-energy`, `short-bg:tail-source` and the reconstruction
`short-bg:flat-reconstruction`, are statements about the frozen growing pair of Part I
(Corollary `cor:short-seed-dilation`: Euler generators `𝓛_a`, projections `𝓟_a`). They are the
proof of `FlatInverse` below; their statements require the Part I frozen-evolution API and are
listed as dependent tasks, not as free-data Props.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-! ## Elementary Hardy-type estimates (SP 2243-2257) -/

/-- The measure `s^b ds` on `(0, ∞)`. -/
def sMeas (b : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi (0 : ℝ))).withDensity fun s => ENNReal.ofReal (s ^ b)

/-- **`short-bg:hardy`, first line** (SP 2243-2244, 2254-2257; `p = 11/4`): Hölder,
`‖f‖_{L¹(0,T)} ≤ 14^{7/11}T^{1/22}‖f‖_{L^p(s^{13/8}ds)}`. Stated for the nonnegative norm function
`g = ‖f(·)‖` (the estimates "apply to norms of Banach-valued functions"). -/
def HardyL1 : Prop :=
  ∀ T : ℝ, 0 < T → ∀ g : ℝ → ℝ≥0∞, Measurable g →
    ∫⁻ s in Ioc 0 T, g s ≤
      ENNReal.ofReal (14 ^ (7 / 11 : ℝ) * T ^ (1 / 22 : ℝ)) *
        (∫⁻ s in Ioc 0 T, g s ^ bgp ∂sMeas (13 / 8)) ^ (4 / 11 : ℝ)

/-- **`short-bg:hardy`, second line** (SP 2245-2246, 2254-2257): `t = su`, Minkowski, `∫₀¹u^{-21/22}du = 22`:
`‖∫₀^s f‖_{L^p(s^{-9/8}ds)} ≤ 22‖f‖_{L^p(s^{13/8}ds)}`. -/
def HardyMean : Prop :=
  ∀ g : ℝ → ℝ≥0∞, Measurable g →
    (∫⁻ s, (∫⁻ t in Ioc 0 s, g t) ^ bgp ∂sMeas (-9 / 8)) ^ (4 / 11 : ℝ) ≤
      22 * (∫⁻ s, g s ^ bgp ∂sMeas (13 / 8)) ^ (4 / 11 : ℝ)

/-- **`short-bg:hardy`, third line** (SP 2247-2252, 2254-2257): factor `(1-u)^{-1/2}u^{-21/22}`:
`‖∫₀^s (s-t)^{-1/2}f(t)dt‖_{L^p(s^{13/8}ds)} ≤ C√T‖f‖_{L^p(s^{13/8}ds)}` on `(0, T)`. -/
def HardySingular : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → ∀ g : ℝ → ℝ≥0∞, Measurable g →
    (∫⁻ s in Ioc 0 T,
        (∫⁻ t in Ioc 0 s, ENNReal.ofReal ((s - t) ^ (-1 / 2 : ℝ)) * g t) ^ bgp
        ∂sMeas (13 / 8)) ^ (4 / 11 : ℝ) ≤
      ENNReal.ofReal (C * Real.sqrt T) * (∫⁻ s in Ioc 0 T, g s ^ bgp ∂sMeas (13 / 8)) ^ (4 / 11 : ℝ)

/-! ## The graph transform (SP 2172-2188, `short-bg:graphs` at 2177) -/

/-- **The graph-transform lemma** (SP 2172-2188). Blocks `(a b; c d)` on `E ⊕ F` with
`‖a⁻¹‖ ≤ A`, `‖d‖ ≤ D`, `‖b‖, ‖c‖ ≤ η`. On the ball of radius `r` with
`Aηr < 1` and `r(1 - AD) ≥ Aη(1 + r²)`, the forward map `ξ ↦ (c + dξ)(a + bξ)⁻¹` is defined,
preserves the ball and has Lipschitz constant `A(D + ηr)/(1 - Aηr)`; the backward map
`ζ ↦ (a - ζc)⁻¹(ζd - b)` likewise. -/
def GraphTransformLemma : Prop :=
  ∀ (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (a : E →L[ℝ] E) (b : F →L[ℝ] E) (c : E →L[ℝ] F) (d : F →L[ℝ] F) (ainv : E →L[ℝ] E)
    (A D η r : ℝ), ainv * a = 1 → a * ainv = 1 → ‖ainv‖ ≤ A → ‖d‖ ≤ D → ‖b‖ ≤ η → ‖c‖ ≤ η →
    0 ≤ η → 0 ≤ r → A * η * r < 1 → A * η * (1 + r ^ 2) ≤ r * (1 - A * D) →
    (∀ ξ : E →L[ℝ] F, ‖ξ‖ ≤ r → ∃ M : E →L[ℝ] E,
        M * (a + b.comp ξ) = 1 ∧ (a + b.comp ξ) * M = 1 ∧ ‖M‖ ≤ A / (1 - A * η * r) ∧
          ‖(c + d.comp ξ).comp M‖ ≤ r) ∧
    (∀ (ξ₁ ξ₂ : E →L[ℝ] F) (M₁ M₂ : E →L[ℝ] E), ‖ξ₁‖ ≤ r → ‖ξ₂‖ ≤ r →
        M₁ * (a + b.comp ξ₁) = 1 → (a + b.comp ξ₁) * M₁ = 1 →
        M₂ * (a + b.comp ξ₂) = 1 → (a + b.comp ξ₂) * M₂ = 1 →
        ‖(c + d.comp ξ₁).comp M₁ - (c + d.comp ξ₂).comp M₂‖ ≤
          A * (D + η * r) / (1 - A * η * r) * ‖ξ₁ - ξ₂‖) ∧
    (∀ ζ : F →L[ℝ] E, ‖ζ‖ ≤ r → ∃ M : E →L[ℝ] E,
        M * (a - ζ.comp c) = 1 ∧ (a - ζ.comp c) * M = 1 ∧ ‖M‖ ≤ A / (1 - A * η * r) ∧
          ‖M.comp (ζ.comp d - b)‖ ≤ r) ∧
    (∀ (ζ₁ ζ₂ : F →L[ℝ] E) (M₁ M₂ : E →L[ℝ] E), ‖ζ₁‖ ≤ r → ‖ζ₂‖ ≤ r →
        M₁ * (a - ζ₁.comp c) = 1 → (a - ζ₁.comp c) * M₁ = 1 →
        M₂ * (a - ζ₂.comp c) = 1 → (a - ζ₂.comp c) * M₂ = 1 →
        ‖M₁.comp (ζ₁.comp d - b) - M₂.comp (ζ₂.comp d - b)‖ ≤
          A * (D + η * r) / (1 - A * η * r) * ‖ζ₁ - ζ₂‖)

/-! ## The free cylinder bound (SP 2074-2118, `short-bg:free-cylinder` at 2101) -/

/-- The planar Laplacian of a test function on the cylinder. -/
def lapP (φ : B0579.Plane → ℝ) (x : B0579.Plane) : ℝ :=
  B0579.pd 0 (B0579.pd 0 φ) x + B0579.pd 1 (B0579.pd 1 φ) x

/-- The tested right-hand side of `ω_s + v_c·∇ω = νΔω` at age `r`. -/
def cylFreeIntegrand {ν c : ℝ} (tr : B0140.TrainSol ν c) (ω : B0579.Plane → ℝ) (r : ℝ)
    (φ : B0579.Plane → ℝ) (x : B0579.Plane) : ℝ :=
  ω x * (ν * lapP φ x + (tr.v r x 0 * B0579.pd 0 φ x + tr.v r x 1 * B0579.pd 1 φ x))

/-- `ω` is a weak solution in `C([t₀, ∞); X_{m,c})` of `ω_s = νΔω - v_c·∇ω` with datum `f`
at age `t₀` (the free cylinder evolution `S_{ν,c}(·, t₀)f`), `X_{m,c} = L²(C_c, (1+q²+η²)^m)`. -/
structure IsFreeCylFlow {ν c : ℝ} (m : ℝ) (tr : B0140.TrainSol ν c) (t₀ : ℝ)
    (f : B0579.Plane → ℝ) (ω : ℝ → B0579.Plane → ℝ) : Prop where
  initial : ω t₀ =ᵐ[volume.restrict (B0579.cell c)] f
  memX : ∀ s, t₀ ≤ s → MemLp (ω s) 2 (B0579.cellMeasure c m)
  strongCont : ∀ s, t₀ ≤ s →
    Tendsto (fun s' => eLpNorm (ω s' - ω s) 2 (B0579.cellMeasure c m)) (𝓝[Ici t₀] s) (𝓝 0)
  integrable : ∀ φ, B0579.IsCylTest c φ → ∀ r, t₀ ≤ r →
    IntegrableOn (cylFreeIntegrand tr (ω r) r φ) (B0579.cell c)
  timeIntegrable : ∀ φ, B0579.IsCylTest c φ → ∀ s, t₀ ≤ s →
    IntervalIntegrable (fun r => ∫ x in B0579.cell c, cylFreeIntegrand tr (ω r) r φ x) volume t₀ s
  weak : ∀ φ, B0579.IsCylTest c φ → ∀ s, t₀ ≤ s →
    ∫ x in B0579.cell c, ω s x * φ x =
      (∫ x in B0579.cell c, f x * φ x) +
        ∫ r in t₀..s, ∫ x in B0579.cell c, cylFreeIntegrand tr (ω r) r φ x

/-- The train comparison on `s ≤ Σ/ν` (SP 2085-2093): `v_c` and the periodized planar heat vortex
`V_c^p = Train.Vc ν c s` agree up to `δ` with their derivatives up to order 4 (so `E_c = curl v_c`
to order 3) in the weighted budget `⟨x⟩⁸ = (1 + q² + η²)⁴` on the centered cell `C_c`
(`x ∈ B0579.cell c`, `|q| ≤ c/2`), where the weight of `X_{m,c} = L²(C_c, (1+q²+η²)^m)` lives
(SP 2074-2076).

The weight is imposed on the cell only: both `v_c` and `V_c^p` are `c`-periodic in `q`, so a bound
with `⟨x⟩⁸` on the whole plane would force `v_c = V_c^p` exactly (the first version of this
definition did that; `Review/PartII-b/TrainCloseCollapse.lean`). By periodicity the cell bound
gives `‖D^j(v_c - V_c^p)‖ ≤ δ` on the whole plane (`TrainClose.plane_bound`,
`Sub/TrainCloseCell.lean`). -/
def TrainClose {ν c : ℝ} (tr : B0140.TrainSol ν c) (Sg δ : ℝ) : Prop :=
  ∀ s : ℝ, 0 ≤ s → s ≤ Sg / ν → ∀ x ∈ B0579.cell c, ∀ j ≤ 4,
    ‖iteratedFDeriv ℝ j (fun z => tr.v s z - Train.Vc ν c s z) x‖ * B0579.jb x ^ 4 ≤ δ

/-- **`short-bg:free-cylinder`** (SP 2074-2118): for `m > 8`, `Σ > 0` there are constants such
that for every parameter point of the regime, every `δ` with `‖v_c - V_c^p‖ + ‖E_c - E_c^p‖ ≤ δ`
on `s ≤ Σ/ν`, and `0 ≤ s ≤ t ≤ Σ/ν`, the free cylinder evolution exists, is unique, and
`‖S_{ν,c}(t,s)‖_{X_{m,c}→X_{m,c}} ≤ exp[(C_mν + Cδ + Ce^{-b c²})(t-s)]`. -/
def FreeCylinderBound : Prop :=
  ∀ m : ℝ, 8 < m → ∀ Sg : ℝ, 0 < Sg → ∃ (Cm C b : ℝ), 0 < Cm ∧ 0 < C ∧ 0 < b ∧
    ∀ (p : Params) (d dm dp : ℝ), BgRegime p d dm dp → ∀ δ : ℝ, 0 ≤ δ → TrainClose p.train Sg δ →
    ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ Sg / p.ν →
    ∀ f : B0579.Plane → ℝ, MemLp f 2 (B0579.cellMeasure p.c m) →
      ∃ ω : ℝ → B0579.Plane → ℝ, IsFreeCylFlow m p.train s f ω ∧
        (∀ ω' : ℝ → B0579.Plane → ℝ, IsFreeCylFlow m p.train s f ω' →
          ∀ t' : ℝ, s ≤ t' → ω' t' =ᵐ[volume.restrict (B0579.cell p.c)] ω t') ∧
        eLpNorm (ω t) 2 (B0579.cellMeasure p.c m) ≤
          ENNReal.ofReal (Real.exp ((Cm * p.ν + C * δ + C * Real.exp (-b * p.c ^ 2)) * (t - s))) *
            eLpNorm f 2 (B0579.cellMeasure p.c m)

/-! ## The real body space `H_p`, the row operators and the flat augmented inverse -/

instance factOneLeBgp : Fact (1 ≤ ENNReal.ofReal bgp) :=
  ⟨ENNReal.one_le_ofReal.2 (by norm_num [bgp])⟩

/-- The real class of `H_p` (`p = 11/4`) as a Banach space. -/
abbrev HpR (c : ℝ) : Type := Lp Axi.Merid (ENNReal.ofReal bgp) (hMeas c bgp)

/-- Wrapping `q` into the cell `[-c/2, c/2)`. -/
def qwrap (c q : ℝ) : ℝ := q - c * (⌊(q + c / 2) / c⌋ : ℝ)

/-- The `c`-periodic complex profile of an element of `H_p`. -/
def toProf (c : ℝ) (g : HpR c) : CProf := fun x =>
  WithLp.toLp 2 fun i => ((((g : Coord → Axi.Merid) (x.1, (qwrap c x.2.1, x.2.2))) i : ℝ) : ℂ)

/-- The state space `X × ℝ²` of the equation row, with norm `‖f‖ + |α|` (SP 2390-2400). -/
abbrev RowSpace (c : ℝ) : Type := WithLp 1 (HpR c × E2)

/-- The equation row `𝔄(f, α) = (I + K)f + 𝒞α` (SP 2390-2400, 2493-2504). -/
def rowOp {c : ℝ} (K : HpR c →L[ℝ] HpR c) (C : E2 →L[ℝ] HpR c) : RowSpace c →L[ℝ] HpR c :=
  (ContinuousLinearMap.id ℝ (HpR c) + K).comp (WithLp.fstL 1 ℝ (HpR c) E2) +
    C.comp (WithLp.sndL 1 ℝ (HpR c) E2)

/-- `K_ε = sB_εT_ε` as a bounded operator on `H_p` (`ε = p.ε`, shift `0`): for every `f` the
response `b = T_εf` exists and `K_εf` is the profile of `B_{U_raw}(N_v b)`. -/
def IsKop (p : Params) (K : HpR p.c →L[ℝ] HpR p.c) : Prop :=
  ∀ f : HpR p.c, ∃ b, InHr p.c bgp b ∧ IsResponse p.ν p.c p.ε 0 bgp (toProf p.c f) b ∧
    IsKOut p b (toProf p.c (K f))

/-- `K_0 = sB_vT_0` as a bounded operator on `H_p`: `K_0f = flatK(T_0f)`. -/
def IsK0op (p : Params) (K : HpR p.c →L[ℝ] HpR p.c) : Prop :=
  ∀ f : HpR p.c, ∃ b gq gη : CProf, InFlatClass p.c bgp b ∧ IsFlatResponse p.ν 0 (toProf p.c f) b ∧
    HasWeakVec vQ0 dZero b gq ∧ HasWeakVec vEta dZero b gη ∧
    toProf p.c (K f) =ᵐ[hMeas p.c bgp] flatK p.train b gq gη

/-- The real streams' flat inlet components `e_0 = (-ψ_η, ψ_q)` with `ψ = χ(s)ψ_i` the cutoff
frozen stream (SP 2347-2382, `ε = 0`). -/
def inletE0 (p : Params) (i : Fin 2) : Coord → Axi.Merid := fun m =>
  (-(Axi.dEta (p.cutStream i) m)) • Axi.m0 + (Axi.dQ (p.cutStream i) m) • Axi.m1

/-- A real profile as a complex one. -/
def cplx (e : Coord → Axi.Merid) : CProf := fun x => WithLp.toLp 2 fun i => (((e x) i : ℝ) : ℂ)

/-- The flat complete source column `𝒞_0` of the inlet `i` (SP 2370-2382, `ε = 0`):
`s[(∂_s - νΔ_{q,η})e_0 + B_0e_0]`. -/
def flatColumn (p : Params) (i : Fin 2) : CProf := fun x =>
  (x.1 : ℂ) • cplx (fun y => Axi.dS (inletE0 p i) y -
      p.ν • (Axi.dQ (Axi.dQ (inletE0 p i)) y + Axi.dEta (Axi.dEta (inletE0 p i)) y)) x +
    flatK p.train (cplx (inletE0 p i)) (cplx (Axi.dQ (inletE0 p i)))
      (cplx (Axi.dEta (inletE0 p i))) x

/-- `𝒞_ε : ℝ² → H_p`, `𝒞_εα` the profile of the complete unprojected source
`(A_0 + B_{U_raw})(E_εα)` of the affine inlet (SP 2370-2382). -/
def IsCop (p : Params) (C : E2 →L[ℝ] HpR p.c) : Prop :=
  ∀ (α : E2) (Φ : ℝ × Space → CVec3), IsPhaseTest p.period Φ →
    pairF p.period (fun x => L0T p.ν Φ x + convT p.raw Φ x)
        (fun x => ∑ i : Fin 2, ((α i : ℝ) : ℂ) • p.Efun i x) =
      pairF p.period Φ (NvC p.R (toProf p.c (C α)))

/-- `𝒞_0 : ℝ² → H_p`, `𝒞_0α = Σ α_i flatColumn i`. -/
def IsC0op (p : Params) (C : E2 →L[ℝ] HpR p.c) : Prop :=
  ∀ α : E2, toProf p.c (C α) =ᵐ[hMeas p.c bgp] fun x =>
    ∑ i : Fin 2, ((α i : ℝ) : ℂ) • flatColumn p i x

/-- **`short-bg:flat-inverse`** (SP 2326-2344, with the right inverse `R_0` of SP 2390-2410). Fix
the growing eigenpair `(λ, q)` (`Planar.IsGrowingEigenpair`; the frozen growing pair of
Corollary `cor:short-seed-dilation`, SP 2048-2049, whose Gaussian angular-two eigenstream gives
the inlet columns, SP 2347-2358); the level carries it as `p.mode = q`. For every fixed `m > 0`
(and fixed `d_±`) there is a slow age `Σ₀` such that for every terminal slow age `Σ ≥ Σ₀`
(`p.ageCut = Σ`, `H = Σ/ν`) there are `C, k, ν₀` such that, at every parameter point of the
regime with `ν ≤ ν₀`, the flat interaction `K_0` and the flat column `𝒞_0` exist as bounded
operators, and for them the flat equation row `𝔄_0(f, α) = (I + K_0)f + 𝒞_0α` has a bounded linear
right inverse `R_0 : H_p → H_p × ℝ²` with `‖f‖ + |α| ≤ Cν^{-k}e^{m/ν}‖F‖`.

Quantifier order. `𝒞_0` is linear in `p.mode` and depends on `p.ageCut` through the age cutoff
(`inletE0`, `flatColumn`), so the constants come after `(λ, q)` and `Σ` (for `p.mode = 0` the
column vanishes and no right inverse exists). `Σ` is chosen large from `m`: the global energy
carries `exp((a'Σ + C/(1+Σ))/ν)` (`short-bg:global-energy`, SP 2289-2294), and "Choosing `Σ`
large and then `a'` small" gives `e^{m/ν}` (SP 2337-2342); every larger `Σ` works as well. -/
def FlatInverse : Prop :=
  ∀ (lam : ℂ) (q : Blueprint.Planar.Profile), Blueprint.Planar.IsGrowingEigenpair lam q →
  ∀ m : ℝ, 0 < m → ∀ dm dp : ℝ, 0 < dm → ∃ Sig₀ : ℝ, 0 < Sig₀ ∧ ∀ Sig : ℝ, Sig₀ ≤ Sig →
    ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < C ∧ 0 < ν₀ ∧
    ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.ageCut = Sig → p.mode = q →
      (∃ K0 C0, IsK0op p K0 ∧ IsC0op p C0) ∧
      ∀ (K0 : HpR p.c →L[ℝ] HpR p.c) (C0 : E2 →L[ℝ] HpR p.c), IsK0op p K0 → IsC0op p C0 →
        ∃ R0 : HpR p.c →L[ℝ] RowSpace p.c, (∀ F, rowOp K0 C0 (R0 F) = F) ∧
          ‖R0‖ ≤ C * (p.ν ^ k)⁻¹ * Real.exp (m / p.ν)

end UnforcedLeray.Short.IIb
