import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T19_2_3

/-!
# Part III-a, `PartIII-a:T19/2/3/2`: decomposition of `CoreDuhamelVorticityBound`

Source: `the November 2 reference manuscript` (SP) lines 3456-3496.

The perturbation `w = b_sol - b₀` of the train and free causal solutions solves
`w_s + (μ/s) w - νΔw + P div(v⊗w + w⊗v) = -P div(v⊗b₀ + b₀⊗v)` (SP 3426-3440, 3462-3466).
Taking the curl and multiplying by `s^μ` removes the `μ/s` term: `Ω = s^μ g ω`
(`ω = corePerturbVort`, `g = gainG`) solves the linearised vorticity equation of `IsLinearisedFlow`
with zero entrance and source `s^μ g f`, `f = -curl advStretch(v, u₀, G̃₀)`, `u₀ = g⁻¹ b₀`.
The source `f` is only a distribution (in `Z^{-1}_{9,c}`), so it is carried as the functional
`coreSrcFun` of the weak gradient `g = ∇φ` of the test function:
`⟨-curl a, φ⟩ = ∫ (a_η ∂_qφ - a_q ∂_ηφ)`.

Three leaves:
* (a) `CoreVortWeakEq`: the weak sourced vorticity equation for `Ω` (SP 3462-3466, 3489-3491).
* (c) `CoreSourceNegBound`: `Z^{-1}_{9,c}` bound of the source functional by `C_dual A_m (‖u₀‖ + ‖G̃₀‖)`
  (SP 3456-3480; follows from the `C_dual` clause and Cauchy-Schwarz).
* (b) `CoreDuhamelFromClock`: Duhamel identification of `Ω` with the forward propagation of the
  source, density extension of `ClockBoundAt` to the weak source, and Minkowski (SP 3481-3496).
`coreDuhamelVorticityBound_of` assembles `CoreDuhamelVorticityBound` from them.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi UnforcedLeray.Blueprint.Planar
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-- The advection-stretching field `(v·∇)u₀ + (u₀·∇)v` at age `t`, `v = tr.v t`,
`u₀ = g⁻¹ b₀`, `G̃₀ = g⁻¹ G₀` (SP 3462-3463). -/
def coreAdvSlice {ν c : ℝ} (γ : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν c)
    (b₀ : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (G₀ : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (t : ℝ) :
    ℝ × ℝ → Fin 2 → ℂ :=
  advStretch (trainVel tr t) (fun x => gainConj γ ν b₀ (t, x)) (fun x => gainConj γ ν G₀ (t, x))

/-- The source `f = -curl a` as a functional of the weak gradient `g = ∇φ` of a test function:
`∫_{cell c} (a_η g_q - a_q g_η)` (components `0 = q`, `1 = η`). -/
def coreSrcFun (c : ℝ) (a : ℝ × ℝ → Fin 2 → ℂ) (g : Fin 2 → ℝ × ℝ → ℂ) : ℂ :=
  ∫ x in B0579.cell c, (a x 1 * g 0 x - a x 0 * g 1 x)

/-- `Z^{-1}_{m,c}` norm of the source functional `coreSrcFun c a`. -/
def coreSrcNorm (c m : ℝ) (a : ℝ × ℝ → Fin 2 → ℂ) : ℝ≥0∞ :=
  ⨆ (φ : ℝ × ℝ → ℂ) (g : Fin 2 → ℝ × ℝ → ℂ) (_ : ∀ j, HasWeakCellDerivC c j φ (g j))
    (_ : h1Norm c m φ g ≤ 1), ENNReal.ofReal ‖coreSrcFun c a g‖

/-- The curl-duality clause of `CoreDuhamelVorticityBound` (SP 3456-3480; `CoreCurlDuality`). -/
def CDualClause (C_dual : ℝ) : Prop :=
  ∀ (c A_m : ℝ), 0 < c → 0 ≤ A_m →
    ∀ (v : ℝ × ℝ → Fin 2 → ℝ), ContDiff ℝ 1 v →
      (∀ x ∈ B0579.cell c, B0579.bracket x ^ (9 : ℝ) * (‖v x‖ + ‖fderiv ℝ v x‖) ≤ A_m) →
      ∀ (u : ℝ × ℝ → Fin 2 → ℂ) (G : ℝ × ℝ → Fin 2 → Fin 2 → ℂ),
        (∀ i, Measurable fun x => u x i) → (∀ i j, Measurable fun x => G x i j) →
        (∫⁻ x in B0579.cell c,
            ENNReal.ofReal (B0579.bracket x ^ (18 : ℝ) * vnorm2 (advStretch v u G x) ^ 2)) ^
          (1 / 2 : ℝ) ≤
          ENNReal.ofReal (C_dual * A_m) *
            ((∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (u x) ^ 2)) ^ (1 / 2 : ℝ) +
              (∫⁻ x in B0579.cell c, ENNReal.ofReal (tnorm2 (G x) ^ 2)) ^ (1 / 2 : ℝ)) ∧
      ∀ (f : ℝ × ℝ → ℂ),
        (∀ (φ : ℝ × ℝ → ℂ) (g : Fin 2 → ℝ × ℝ → ℂ),
          (∀ j, HasWeakCellDerivC c j φ (g j)) → h1Norm c 9 φ g ≤ 1 →
          ENNReal.ofReal ‖∫ x in B0579.cell c, f x * φ x‖ ≤
            ∫⁻ x in B0579.cell c,
              ENNReal.ofReal (vnorm2 (advStretch v u G x) * vnorm2 (fun j => g j x))) →
        negNorm c 9 f ≤
          ENNReal.ofReal (C_dual * A_m) *
            ((∫⁻ x in B0579.cell c, ENNReal.ofReal (vnorm2 (u x) ^ 2)) ^ (1 / 2 : ℝ) +
              (∫⁻ x in B0579.cell c, ENNReal.ofReal (tnorm2 (G x) ^ 2)) ^ (1 / 2 : ℝ))

/-- Standing hypotheses on the data of the core vorticity bound (those of
`CoreDuhamelVorticityBound` after `ν`, `tr` are fixed). -/
def VortData (P : PlanarData) (K : Set ℂ) (b : ℝ) (ν : ℝ)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (μ : ℂ) (A_m : ℝ)
    (F : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (b₀ : ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
    (G₀ : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) (b_sol : ℝ × (ℝ × ℝ) → Fin 2 → ℂ)
    (G_sol : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) : Prop :=
  UnforcedLeray.Short.PartI.IsBUCTrain tr ∧ μ ∈ K ∧ 0 ≤ A_m ∧
    (∀ s ∈ Ioc (0 : ℝ) (coreEnd ν b), ∀ x ∈ B0579.cell (ν ^ (-2 : ℝ)),
      B0579.bracket x ^ (9 : ℝ) * (‖tr.v s x‖ + ‖fderiv ℝ (tr.v s) x‖) ≤ A_m) ∧
    (∀ p i j, F p i j = F p j i) ∧ (∀ i j, Measurable fun p => F p i j) ∧
    tCalNorm (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν F) < ⊤ ∧
    IsCausalEnergySolution (ν ^ (-2 : ℝ)) ν μ (fun _ _ _ => 0) F b₀ G₀ ∧
    IsCausalEnergySolution (ν ^ (-2 : ℝ)) ν μ (trainVel tr) F b_sol G_sol

/-- Conclusion of the weak sourced vorticity equation (a): with `Ω r = r^μ g(r) ω(r)`,
`U r = r^μ g(r) u₁(r)` and zero entrance, for a.e. `s ∈ (0, H)` and every cylinder test `φ`,
`∫ Ω(s) φ = ∫_0^s [∫ flowIntegrand tr (Ω r) (U r) r φ + r^μ g(r) ⟨-curl adv(r), φ⟩] dr`. -/
def CoreVortWeakEqAt (P : PlanarData) (b ν : ℝ)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (μ : ℂ)
    (b₀ : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (G₀ : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ)
    (b_sol : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (G_sol : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) : Prop :=
  ∀ᵐ s ∂volume, s ∈ Ioo (0 : ℝ) (coreEnd ν b) →
    ∀ φ : ℝ × ℝ → ℝ, B0579.IsCylTest (ν ^ (-2 : ℝ)) φ →
      IntervalIntegrable
        (fun r => (∫ x in B0579.cell (ν ^ (-2 : ℝ)),
            flowIntegrand tr
              (fun y => ((r : ℂ) ^ μ * (gainG P.eigenvalue.re ν r : ℂ)) *
                corePerturbVort P.eigenvalue.re ν G₀ G_sol r y)
              (fun y => ((r : ℂ) ^ μ * (gainG P.eigenvalue.re ν r : ℂ)) •
                corePerturbVel P.eigenvalue.re ν b₀ b_sol (r, y)) r φ x) +
          ((r : ℂ) ^ μ * (gainG P.eigenvalue.re ν r : ℂ)) *
            coreSrcFun (ν ^ (-2 : ℝ)) (coreAdvSlice P.eigenvalue.re tr b₀ G₀ r)
              (fun j x => (B0579.pd j φ x : ℂ))) volume 0 s ∧
      ∫ x in B0579.cell (ν ^ (-2 : ℝ)),
          ((s : ℂ) ^ μ * (gainG P.eigenvalue.re ν s : ℂ)) *
            corePerturbVort P.eigenvalue.re ν G₀ G_sol s x * (φ x : ℂ) =
        ∫ r in (0 : ℝ)..s,
          ((∫ x in B0579.cell (ν ^ (-2 : ℝ)),
            flowIntegrand tr
              (fun y => ((r : ℂ) ^ μ * (gainG P.eigenvalue.re ν r : ℂ)) *
                corePerturbVort P.eigenvalue.re ν G₀ G_sol r y)
              (fun y => ((r : ℂ) ^ μ * (gainG P.eigenvalue.re ν r : ℂ)) •
                corePerturbVel P.eigenvalue.re ν b₀ b_sol (r, y)) r φ x) +
          ((r : ℂ) ^ μ * (gainG P.eigenvalue.re ν r : ℂ)) *
            coreSrcFun (ν ^ (-2 : ℝ)) (coreAdvSlice P.eigenvalue.re tr b₀ G₀ r)
              (fun j x => (B0579.pd j φ x : ℂ)))

/-- Conclusion of the source bound (c): for a.e. `t ∈ (0, H)`,
`‖f(t)‖_{Z^{-1}_{9,c}} ≤ C_dual A_m (‖u₀(t)‖₂ + ‖G̃₀(t)‖₂)` (SP 3456-3480). -/
def CoreSrcBoundAt (C_dual A_m : ℝ) (P : PlanarData) (b ν : ℝ)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (b₀ : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (G₀ : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) : Prop :=
  ∀ᵐ t ∂volume, t ∈ Ioo (0 : ℝ) (coreEnd ν b) →
    coreSrcNorm (ν ^ (-2 : ℝ)) 9 (coreAdvSlice P.eigenvalue.re tr b₀ G₀ t) ≤
      ENNReal.ofReal (C_dual * A_m) *
        (unnormSliceVel (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν b₀) t +
          unnormSliceGrad (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν G₀) t)

/-- Conclusion of the core vorticity bound (SP 3489-3496). -/
def CoreVortConclusionAt (C_dual A_m C_clock : ℝ) (P : PlanarData) (b ν : ℝ) (μ : ℂ)
    (b₀ : ℝ × (ℝ × ℝ) → Fin 2 → ℂ) (G₀ G_sol : ℝ × (ℝ × ℝ) → Fin 2 → Fin 2 → ℂ) : Prop :=
  ∀ᵐ s ∂volume, s ∈ Ioo (0 : ℝ) (coreEnd ν b) →
    MemLp (corePerturbVort P.eigenvalue.re ν G₀ G_sol s) 2
      (B0579.cellMeasure (ν ^ (-2 : ℝ)) 9) ∧
    HasZeroCirculation (ν ^ (-2 : ℝ)) (corePerturbVort P.eigenvalue.re ν G₀ G_sol s) ∧
    xNorm (ν ^ (-2 : ℝ)) 9 (corePerturbVort P.eigenvalue.re ν G₀ G_sol s) ≤
      ∫⁻ t in Ioo (0 : ℝ) s,
        ENNReal.ofReal (|C_clock| * ν ^ (-(weakDegree 9 P.kappa : ℝ)) *
          (t / s) ^ μ.re * (1 + (s - t) ^ (-1 / 2 : ℝ))) *
          (ENNReal.ofReal (C_dual * A_m) *
            (unnormSliceVel (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν b₀) t +
              unnormSliceGrad (ν ^ (-2 : ℝ)) (gainConj P.eigenvalue.re ν G₀) t))

/-- **Leaf (a) `PartIII-a:T19/2/3/2/1`** (SP 3462-3466, 3489-3491): the gain-conjugated
perturbation vorticity is a weak solution of the sourced linearised vorticity equation with zero
entrance. -/
def CoreVortWeakEq : Prop :=
  ∀ P : PlanarData, IsPlanarReference P → ∀ K : Set ℂ, IsAdmissibleK K →
    ∀ b : ℝ, 1 ≤ b → ∀ ν : ℝ, 0 < ν →
      ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)), ∀ μ : ℂ, ∀ A_m : ℝ,
        ∀ F b₀ G₀ b_sol G_sol, VortData P K b ν tr μ A_m F b₀ G₀ b_sol G_sol →
          CoreVortWeakEqAt P b ν tr μ b₀ G₀ b_sol G_sol

/-- **Leaf (c) `PartIII-a:T19/2/3/2/2`** (SP 3456-3480): `Z^{-1}_{9,c}` bound of the source. -/
def CoreSourceNegBound : Prop :=
  ∀ C_dual : ℝ, 0 ≤ C_dual → CDualClause C_dual →
  ∀ P : PlanarData, IsPlanarReference P → ∀ K : Set ℂ, IsAdmissibleK K →
    ∀ b : ℝ, 1 ≤ b → ∀ ν : ℝ, 0 < ν →
      ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)), ∀ μ : ℂ, ∀ A_m : ℝ,
        ∀ F b₀ G₀ b_sol G_sol, VortData P K b ν tr μ A_m F b₀ G₀ b_sol G_sol →
          CoreSrcBoundAt C_dual A_m P b ν tr b₀ G₀

/-- **Leaf (b) `PartIII-a:T19/2/3/2/3`** (SP 3481-3496): Duhamel identification of the weak
solution `Ω` with the forward propagation `∫_0^s (t/s)^μ (g(t)/g(s)) U(s,t) f(t) dt`, the density
extension of `ClockBoundAt` (`FullClockWeakForward`) from `X_{9,c}` data to the weak source in
`Z^{-1}_{9,c}`, and Minkowski, given the weak equation and the source bound. -/
def CoreDuhamelFromClock : Prop :=
  ∀ C_dual : ℝ, 0 ≤ C_dual →
  ∀ P : PlanarData, IsPlanarReference P → ∀ K : Set ℂ, IsAdmissibleK K →
    ∀ b : ℝ, 1 ≤ b → ∃ ν_vort : ℝ, 0 < ν_vort ∧
      ∀ ν ∈ Ioc 0 ν_vort, ∀ tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)),
        ∀ μ : ℂ, ∀ A_m C_clock : ℝ, ClockBoundAt P 9 b C_clock ν tr →
          ∀ F b₀ G₀ b_sol G_sol, VortData P K b ν tr μ A_m F b₀ G₀ b_sol G_sol →
            CoreVortWeakEqAt P b ν tr μ b₀ G₀ b_sol G_sol →
            CoreSrcBoundAt C_dual A_m P b ν tr b₀ G₀ →
            CoreVortConclusionAt C_dual A_m C_clock P b ν μ b₀ G₀ G_sol

/-- Assembly (target of `PartIII-a:T19/2/3/2`, to be named `coreDuhamelVorticityBound`). -/
theorem coreDuhamelVorticityBound_of (hA : CoreVortWeakEq) (hC : CoreSourceNegBound)
    (hB : CoreDuhamelFromClock) : CoreDuhamelVorticityBound := by
  intro C_dual hC0 hdual P hP K hK b hb
  obtain ⟨ν_vort, hν, h⟩ := hB C_dual hC0 P hP K hK b hb
  refine ⟨ν_vort, hν, fun ν hν' tr hbuc μ hμ A_m C_clock hAm hbd hclock F hsym hmeas htc
    b₀ G₀ hfree b_sol G_sol hsol => ?_⟩
  have hd : VortData P K b ν tr μ A_m F b₀ G₀ b_sol G_sol :=
    ⟨hbuc, hμ, hAm, hbd, hsym, hmeas, htc, hfree, hsol⟩
  exact h ν hν' tr μ A_m C_clock hclock F b₀ G₀ b_sol G_sol hd
    (hA P hP K hK b hb ν hν'.1 tr μ A_m F b₀ G₀ b_sol G_sol hd)
    (hC C_dual hC0 hdual P hP K hK b hb ν hν'.1 tr μ A_m F b₀ G₀ b_sol G_sol hd)

end UnforcedLeray.Short.IIIa

end
