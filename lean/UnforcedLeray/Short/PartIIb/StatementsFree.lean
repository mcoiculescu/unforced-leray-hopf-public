import UnforcedLeray.Short.PartIIb.Defs

/-!
# Part II-b, module `background/free-comparison.tex` (SP 1897-2024): statements

Each `def ... : Prop` below is the statement of one result of the source, stated for the concrete
objects of `Defs.lean`. Nothing here is assumed; everything is to be proved from the shared
Cartesian foundation (SP Lemma `bg:common-body-graph`, Part II-a) and the Hilbert free comparison
`near:compact-free-comparison`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411

/-- **`bg:profile-graph`, physical case `ε > 0`** (SP 1912-1938, label at 1914). For `1 < r < 3`
and a shift `μ` with `a_r = Re μ + (3/r - 1)/2 > 0`, there is `C = C_{r,μ}` such that, uniformly in
`ν, c` and `0 < ε ≤ 1` with `P = 2εc ≤ 1`: every `F ∈ H_r` has a response `b = T_εF` (the lift is
the Cartesian solution of `(μ + L)w = 𝔓 f` in the graph `D_r`), and every response satisfies
`‖b‖ + ‖Sb‖ + √ν‖√s(Q_ε b, ∂_η b)‖ ≤ C‖F‖` in `H_r`. -/
def ProfileGraphPhys : Prop :=
  ∀ r : ℝ, 1 < r → r < 3 → ∀ μ : ℂ, 0 < μ.re + (3 / r - 1) / 2 →
    ∃ C : ℝ, 0 < C ∧ ∀ ν c ε : ℝ, 0 < ν → 0 < c → 0 < ε → ε ≤ 1 → 2 * ε * c ≤ 1 →
      ∀ F : CProf, InHr c r F →
        (∃ b, InHr c r b ∧ IsResponse ν c ε μ r F b) ∧
        ∀ b, IsResponse ν c ε μ r F b → GraphBound ν c r ε C F b

/-- **`bg:profile-graph`, flat case `ε = 0`** (SP 1921-1938: "For `ε = 0` the same estimate follows
without a limiting argument", causal formula, `‖T_0‖ ≤ C_r/a_r`, dyadic windows, cylinder heat
estimate by `N` repeated cells): for every `F ∈ H_r` there is exactly one flat response `b = T_0F`
in the graph class, and it obeys the same graph bound (`Q_0 = ∂_q`). -/
def ProfileGraphFlat : Prop :=
  ∀ r : ℝ, 1 < r → r < 3 → ∀ μ : ℂ, 0 < μ.re + (3 / r - 1) / 2 →
    ∃ C : ℝ, 0 < C ∧ ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ F : CProf, InHr c r F →
      ∃ b, InFlatClass c r b ∧ IsFlatResponse ν μ F b ∧ GraphBound ν c r 0 C F b ∧
        ∀ b', InFlatClass c r b' → IsFlatResponse ν μ F b' → b' =ᵐ[hMeas c r] b

/-- **Hilbert version of `bg:lp-comparison-rate`** (SP 1955-1990, the first part of the proof of
`bg:lp-free-comparison`): exponent `2`, shift gap `1/4`, rate `ε^{1/28}`. -/
def HilbertBodyComparison : Prop := CompRate 2 (1 / 4) (1 / 28)

/-- **`bg:lp-free-comparison`** (SP 1940-1952, `bg:lp-comparison-rate` at 1945; proof 1954-2005): `p = 11/4`; on any compact
set of shifts with `inf(Re μ + 1/46) > 0`, for a first-order operator `B` in `(q, η)` with smooth
matrix coefficients supported in the observation box, `‖B(T_ε - T_0)‖_{H_p → H_p} ≤ CΓ^kε^{2/539}`.
Inputs have arbitrary age support. -/
def LpFreeComparison : Prop := CompRate bgp (1 / 46) (2 / 539)

/-- The cutoff `ϑ` of a localized interaction: smooth, supported in the observation box, derivatives
up to order 8 bounded by `Γ`. -/
structure ObsCut (σ H₁ L₁ Γ : ℝ) where
  ϑ : Coord → ℝ
  smooth : ContDiff ℝ ∞ ϑ
  supp : ∀ x, x ∉ obsBox σ H₁ L₁ → ϑ x = 0
  bounded : ∀ k ≤ 8, ∀ x, ‖iteratedFDeriv ℝ k ϑ x‖ ≤ Γ

/-- The physical interaction output: `g` is the profile of `B_{U_raw} (N_v b)`, i.e.
`N_v g = U_raw·∇(N_v b) + (N_v b)·∇U_raw` in distributions (`B_V` tested through
`convT V Φ = (∇V)ᵀΦ - (V·∇)Φ`, valid for solenoidal `V`). This is `g = K_ε f` for `b = T_εf`
(`K_ε = sB_εT_ε`, SP 2007-2010). -/
def IsKOut (p : Params) (b g : CProf) : Prop :=
  ∀ Φ, IsPhaseTest p.period Φ →
    pairF p.period (convT p.raw Φ) (NvC p.R b) = pairF p.period Φ (NvC p.R g)

/-- The flat interaction `K_0 b = s[(v·∇_{q,η}) b + (b·∇_{q,η}) v]` of the flat train `v = v_c(s)`
(SP 2007-2010: `K_0 = sB_0T_0`), with weak derivatives `gq = ∂_q b`, `gη = ∂_η b` supplied. -/
def flatK {ν c : ℝ} (tr : B0140.TrainSol ν c) (b gq gη : CProf) (x : Coord) : CMerid :=
  WithLp.toLp 2 fun i : Fin 2 =>
    (x.1 : ℂ) * (((tr.v x.1 x.2 0 : ℝ) : ℂ) * gq x i + ((tr.v x.1 x.2 1 : ℝ) : ℂ) * gη x i +
      b x 0 * ((fderiv ℝ (fun z => tr.v x.1 z i) x.2 ((1 : ℝ), (0 : ℝ)) : ℝ) : ℂ) +
      b x 1 * ((fderiv ℝ (fun z => tr.v x.1 z i) x.2 ((0 : ℝ), (1 : ℝ)) : ℝ) : ℂ))

/-- **The localized interaction comparison** (SP 2007-2023): with `K_ε = sB_εT_ε`,
`K_0 = sB_0T_0` the actual interactions, `K_ε - K_0 = sB_0(T_ε - T_0) + s(B_ε - B_0)T_ε`; the first
term is `bg:lp-comparison-rate`, the second is `ε` times polynomially bounded coefficients
multiplying `b, ∂_qb, ∂_ηb, Sb`, bounded by `bg:profile-graph` and its local consequence. Hence
`‖ϑ(K_ε - K_0)F‖_{H_p} ≤ CΓ^kε^{2/539}‖F‖_{H_p}` for a cutoff `ϑ` supported in the observation
box, at shift `μ = 0` of the ordinary solve. -/
def LocalInteractionComparison : Prop :=
  ∃ (k : ℕ) (C ν₀ : ℝ), 0 < C ∧ 0 < ν₀ ∧
    ∀ (p : Params) (d dm dp : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ → p.period ≤ 1 →
    ∀ (Γ σ H₁ L₁ : ℝ), 1 ≤ Γ → p.ν ≤ Γ → p.ν⁻¹ ≤ Γ → σ⁻¹ ≤ Γ → H₁ ≤ Γ → L₁ ≤ Γ → 0 < σ →
    ∀ ϑ : ObsCut σ H₁ L₁ Γ, ∀ F bε b0 gε : CProf,
      InHr p.c bgp F → InHr p.c bgp bε → IsResponse p.ν p.c p.ε 0 bgp F bε →
      IsFlatResponse p.ν 0 F b0 → InFlatClass p.c bgp b0 →
      InHr p.c bgp gε → IsKOut p bε gε →
      ∃ gq gη : CProf, HasWeakVec vQ0 dZero b0 gq ∧ HasWeakVec vEta dZero b0 gη ∧
        hNorm p.c bgp (fun x => (ϑ.ϑ x : ℂ) • (gε x - flatK p.train b0 gq gη x)) ≤
          ENNReal.ofReal (C * Γ ^ k * p.ε ^ (2 / 539 : ℝ)) * hNorm p.c bgp F

end UnforcedLeray.Short.IIb
