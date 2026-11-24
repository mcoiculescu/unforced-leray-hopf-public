import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_3_7
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G3

/-!
# Part II-b, task `PartII-b:G3/2`: the two leaves of the physical exterior tail

Source of record: `the November 2 reference manuscript` (SP), lines 2007-2023
(`K_ε = sB_εT_ε`, "Exact chart substitution"), 2419-2423 (raw coefficients), 463-467
(`sct:transverse`) and 2447-2455 (window choice `l = C_D(c/ν + √S + 1)`).

The physical half `PhysKopWindowTransverseTailBound` of `WindowTransverseTailBound` splits into

* `KOutChartAe` (identification): the weak output `g` of `IsKOut p b g` is a.e. on the strip
  `s > 0, |q| < c/2` the chart formula `kOutChart p b Qb Eb`
  `= s[b_raw,r Q_εb + b_raw,z ∂_ηb + b_r Q_εb_raw + b_z ∂_ηb_raw + (div_ε b_raw) b]`
  (`B_ε b = (b_raw·∇_ε)b + (b·∇_ε)b_raw`, `∇_ε = (Q_ε, ∂_η)`, SP 2007-2012; the last term is the
  chart divergence `(Q_ε + ε)b_raw,r + ∂_ηb_raw,z`, which vanishes for the solenoidal raw field and
  is kept so that the identity is the plain integration by parts of `(U_raw·∇)` against the test);
* `RawCoeffWindowTail` (coefficients): on the exterior slab `windowExtSet σ S L` the first-order
  chart jet of `b_raw = (v₁, v₂ + εH)` (`chartJet`) is `≤ e^{-D/ν}` after the weight `1 + s`
  (SP 2447-2455: "Increasing `C_D` makes all required coefficient tails at most `e^{-D/ν}`").
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace

/-- The chart divergence coefficient `(Q_ε + ε)u_r + ∂_ηu_z` of a real chart profile
(`div(N_v u) = s·(this)`, SP 1658-1660). -/
def chartDivR (ε : ℝ) (u : Coord → Axi.Merid) (x : Coord) : ℝ :=
  qEps ε u x 0 + ε * u x 0 + Axi.dEta u x 1

/-- **The chart formula of the physical interaction output** (SP 2007-2012): for `b` with weak
derivatives `Qb = Q_εb`, `Eb = ∂_ηb`,
`s[b_raw,r Qb + b_raw,z Eb + b_r Q_εb_raw + b_z ∂_ηb_raw + (chartDivR b_raw) b]`. -/
def kOutChart (p : Params) (b Qb Eb : CProf) (x : Coord) : CMerid :=
  ((x.1 : ℝ) : ℂ) •
    ((((rawProf p x 0 : ℝ) : ℂ) • Qb x + ((rawProf p x 1 : ℝ) : ℂ) • Eb x) +
      (b x 0 • cplx (qEps p.ε (rawProf p)) x + b x 1 • cplx (Axi.dEta (rawProf p)) x) +
      ((chartDivR p.ε (rawProf p) x : ℝ) : ℂ) • b x)

/-- **Leaf `KOutChartAe` (identification of the weak output, SP 2007-2012)**: if `g ∈ H_p` is the
output `IsKOut p b g` of `b ∈ H_p` with weak derivatives `Q_εb = Qb`, `∂_ηb = Eb`, then
`g = kOutChart p b Qb Eb` a.e. on the strip `s > 0, |q| < c/2`.  Route: window tests `χ`
(`IsWinTest`), their phase lifts `Φ = (winPer χ ∘ chart) e_j` (`windowPhaseVec`), the pointwise
chart identities `(N_vb·∇)U_raw = N_v(s[b_rQ_εb_raw + b_z∂_ηb_raw])` and
`U_raw·∇(φ∘chart) = s(b_raw,r vQ_ε + b_raw,z vEta)·∇φ` (`chartAdv_dRho_dz`), the change of
variables `windowChartIntegralGen`, the chart integration by parts `HasWeakVec` against the
coordinate tests `s⁻¹ b_raw,i χ`, and `fundWindow_proof`. -/
def KOutChartAe : Prop :=
  ∀ (p : Params) (d dm dp : ℝ), BgRegime p d dm dp →
  ∀ (b g Qb Eb : CProf), InHr p.c bgp b → InHr p.c bgp g →
    HasWeakVec (vQ p.ε) (dQ p.ε) b Qb → HasWeakVec vEta dZero b Eb → IsKOut p b g →
    ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ (Ioo (-p.c / 2) (p.c / 2) ×ˢ (univ : Set ℝ)))),
      g x = kOutChart p b Qb Eb x

/-- **Leaf `RawCoeffWindowTail` (raw coefficient tails on the exterior slab, SP 463-467,
2419-2423, 2447-2455)**: for `D, a, b > 0` there is `C_D₀ ≥ 1` such that for `C_D ≥ C_D₀` and
small `ν`, on `windowExtSet σ S L` (`σ = ε^a`, `S = ε^{-b}`, `L = C_D(c/ν + √S + 1)`) the jet
`‖b_raw‖ + ‖∂_qb_raw‖ + ‖∂_ηb_raw‖ + ‖Kb_raw‖` of `b_raw = v + εHe_z` satisfies
`(1 + s)·chartJet ≤ e^{-D/ν}` (`TrainChartBridge`, `RaisedChartBridge`, `sct:transverse` for
`v` and `ψ`, `TailAbsorb`). -/
def RawCoeffWindowTail : Prop :=
  ∀ D : ℝ, 0 < D → ∀ a b : ℝ, 0 < a → 0 < b → ∀ dm dp : ℝ, 0 < dm →
    ∃ (C_D₀ ν₀ : ℝ), 1 ≤ C_D₀ ∧ 0 < ν₀ ∧ ∀ C_D : ℝ, C_D₀ ≤ C_D →
      ∀ (p : Params) (d : ℝ), BgRegime p d dm dp → p.ν ≤ ν₀ →
        ∀ x ∈ windowExtSet (p.ε ^ a) (p.ε ^ (-b))
            (C_D * (p.c / p.ν + Real.sqrt (p.ε ^ (-b)) + 1)),
          (1 + x.1) * chartJet (rawProf p) x ≤ Real.exp (-D / p.ν)

end UnforcedLeray.Short.IIb

end
