import UnforcedLeray.Short.PartIIIa.Sub.T21_2_7.HeatExists.CLM
import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_3_2_2_Smooth.Basic

/-!
# Part III-a, `PartIII-a:T21/2/7/1/8`: the leaves of `AdjHeatExists` (statements)

Source of record: `the November 2 reference manuscript` (SP), lines 2819-2836
(the full moving evolution on `C_c` at fixed `ν > 0`, `c > 0`: Volterra iteration whose free
part is the periodic heat semigroup of diffusivity `ν` and its heat-divergence response), lines
3044-3050 (the weights on the cell), line 3060 (the reverse-time adjoint on `X_{-m,c}`).

The concrete objects are in `HeatExists/Defs.lean` (`adjHeatKer`, `adjHeatGradKer`,
`adjKerOp`, `adjS0Fun`, `adjDivFun`, `adjSFun`) and `HeatExists/CLM.lean` (`KerYoung`,
`kerCLM`).  `Exist.cylHeatSmooth c θ ψ` is the cylinder heat flow `P_θ ψ = e^{θΔ}ψ` of a test
(`Sub/PartIIIa_T21_3_2_2_Smooth/Basic.lean`, with `cylHeatSmooth_duhamel`, `pd_cylHeatSmooth`,
`cylHeatSmooth_lapP` in `.../Age.lean`, `.../Basic.lean`).

Leaves (`HeatExists/Of.lean` assembles `AdjHeatExists m` from H1-H6; `HeatExists/LeavesOf.lean`
proves H1-H6 from the sub-leaves):
* (H1) `AdjHeatS0Young`: Young bound of `G_{ντ}` on `X_{-m,c}`, uniform on `(0, 1]`
  (from `AdjKerYoungMoment`, itself resting on `AdjCellYoung`, and `AdjHeatMoment`);
* (H2) `AdjHeatGradYoung`: Young bound `C τ^{-1/2}` of `∂_j G_{ντ}`
  (from `AdjKerYoungMoment`, `AdjHeatGradMoment`);
* (H3) `AdjHeatS0StrongZero`: `e^{ντΔ} f → f` in `X_{-m,c}` as `τ → 0+`
  (from H1, `AdjHeatS0TestLimit`, `AdjCylTestDense`);
* (H4) `AdjHeatSemigroup`: the Gaussian semigroup laws (`AdjHeatSemigroupS0`,
  `AdjHeatSemigroupGrad`);
* (H5) `AdjHeatS0Weak`: the weak heat equation of `e^{ντΔ} f` (from `AdjHeatS0Dual`, which
  rests on `AdjKerUnfold`, and `AdjHeatS0Time`, which rests on `AdjFluxPairDuhamel`);
* (H6) `AdjHeatDuhamelWeak`: the tested Duhamel identity of the response (from
  `AdjHeatRespDual` = H1, H2, `AdjHeatS0Dual`, `AdjHeatGradDual`, and `AdjHeatRespTime`, which
  rests on `AdjFluxPairDuhamel`, `AdjFluxPairContinuous`);
* `AdjSmoothDecay`: rapid `η`-decay of the smoothed tests `P_θ ψ`, uniform in `θ`, the
  integrability input of `AdjFluxPairDuhamel`, `AdjFluxPairContinuous`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIIa

/-! ## (H1), (H2): Young bounds on `X_{-m,c}` -/

/-- The axial moment `∫ |k(z)| ⟨z₂⟩^m dz` of a kernel, `⟨z₂⟩ = (1 + z₂²)^{1/2}`. -/
def kerAxialMoment (m : ℝ) (k : ℝ × ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ z, ‖k z‖ₑ * ENNReal.ofReal ((1 + z.2 ^ 2) ^ (m / 2))

/-- **(H1.0) Periodic Minkowski inequality on the centered cell** (SP 2819-2836; the cell
`C_c = [-c/2, c/2) × ℝ` of `B0579`): for a measurable finite kernel `K ≥ 0` and a
`c`-periodic, a.e.-strongly measurable `g`,
`‖x ↦ ∫ K(z) |g(x - z)| dz‖_{L²(C_c)} ≤ (∫ K) ‖g‖_{L²(C_c)}` (the centered-cell form of
`B0296.eLpNorm_kernelAbs_le'`, which is stated on B0284's normalized cell `(0, c] × ℝ`; both
cells are fundamental domains, `Cyl.isAddFundamentalDomain_cell`). -/
def AdjCellYoung : Prop :=
  ∀ c : ℝ, 0 < c → ∀ K : ℝ × ℝ → ℝ≥0∞, Measurable K → (∀ z, K z ≠ ⊤) →
    ∀ g : ℝ × ℝ → ℝ, (∀ x : ℝ × ℝ, g (x.1 + c, x.2) = g x) → AEStronglyMeasurable g volume →
      eLpNorm (fun x => ∫⁻ z, K z * ‖g (x - z)‖ₑ) 2 (volume.restrict (B0579.cell c)) ≤
        (∫⁻ z, K z) * eLpNorm g 2 (volume.restrict (B0579.cell c))

/-- **(H1.1) The weighted periodic Young inequality on `X_{-m,c}`** (SP 2819-2836; on the cell
`⟨x⟩ ≍_c ⟨η⟩`, SP 3044-3050): for `c > 0`, `m ≥ 0` and a continuous kernel `k` with axial
moment `∫ |k(z)| ⟨z₂⟩^m dz ≤ A`, the kernel operator `adjKerOp c k` has the Young bound
`KerYoung c m k ((2(1 + c²/4))^{m/2} A)`.  Route: `⟨x⟩^{-m} ≤ ⟨x₂⟩^{-m} ≤
2^{m/2} ⟨x₂ - y₂⟩^m ⟨y₂⟩^{-m}` (Peetre), Minkowski / periodic Young for the periodic function
`⟨y₂⟩^{-m} |f̃(y)|` (as `B0296.eLpNorm_kernelAbs_le'`, there on B0284's cell `(0, c] × ℝ`), and
`⟨y₂⟩^{-2m} ≤ (1 + c²/4)^m ⟨y⟩^{-2m}` on the cell `|y₁| ≤ c/2`. -/
def AdjKerYoungMoment : Prop :=
  ∀ c m : ℝ, 0 < c → 0 ≤ m → ∀ k : ℝ × ℝ → ℝ, Continuous k → ∀ A : ℝ, 0 ≤ A →
    kerAxialMoment m k ≤ ENNReal.ofReal A →
      KerYoung c m k ((2 * (1 + c ^ 2 / 4)) ^ (m / 2) * A)

/-- **(H1.2) The axial Gaussian moment, uniformly in the age** (SP 2819-2836): for `ν > 0`,
`m ≥ 0` there is `A` with `∫ G_{ντ}(z) ⟨z₂⟩^m dz ≤ A` for all `τ ∈ (0, 1]` (the `q`-integral of
the Gaussian is `1`; the substitution `z₂ = √τ u` bounds the `η`-moment by its value at
`τ = 1`, as `integral_axialHeatMomentDensity_le` of the forward model). -/
def AdjHeatMoment : Prop :=
  ∀ ν m : ℝ, 0 < ν → 0 ≤ m → ∃ A : ℝ, 0 ≤ A ∧
    ∀ τ ∈ Ioc (0 : ℝ) 1, kerAxialMoment m (adjHeatKer ν τ) ≤ ENNReal.ofReal A

/-- **(H1) The heat flow is bounded on `X_{-m,c}`, uniformly on `(0, 1]`** (SP 2819-2836): the
Gaussian convolution `adjS0Fun ν c τ` has a Young bound `M₀` independent of `τ ∈ (0, 1]`. -/
def AdjHeatS0Young (m : ℝ) : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∃ M₀ : ℝ, 0 ≤ M₀ ∧
    ∀ τ ∈ Ioc (0 : ℝ) 1, KerYoung c m (adjHeatKer ν τ) M₀

/-- **(H2.1) The axial moment of the kernel gradient** (SP 2819-2836): for `ν > 0`, `m ≥ 0`
there is `A` with `∫ |∂_j G_{ντ}(z)| ⟨z₂⟩^m dz ≤ A τ^{-1/2}` for `τ ∈ (0, 1]`, `j = 0, 1`
(`∂_j G_θ(z) = -(z_j/(2θ)) G_θ(z)`; product structure and the scaling `z = √θ u`, as
`B0296.lintegral_gradKernelAbs` and `gradKernelAxialMomentDensity` of the forward model). -/
def AdjHeatGradMoment : Prop :=
  ∀ ν m : ℝ, 0 < ν → 0 ≤ m → ∃ A : ℝ, 0 ≤ A ∧ ∀ τ ∈ Ioc (0 : ℝ) 1, ∀ j : Fin 2,
    kerAxialMoment m (adjHeatGradKer ν τ j) ≤ ENNReal.ofReal (A * τ ^ (-(1 / 2 : ℝ)))

/-- **(H2) The divergence response is bounded by `C₁ τ^{-1/2}`** (SP 2819-2836): each kernel
`∂_j G_{ντ}` of `adjDivFun` has a Young bound `C₁ τ^{-1/2}` on `X_{-m,c}`, `τ ∈ (0, 1]`. -/
def AdjHeatGradYoung (m : ℝ) : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ τ ∈ Ioc (0 : ℝ) 1, ∀ j : Fin 2,
    KerYoung c m (adjHeatGradKer ν τ j) (C₁ * τ ^ (-(1 / 2 : ℝ)))

/-! ## (H3): strong continuity at age zero -/

/-- A complexified cylinder test `g = ψ₁ + i ψ₂` (`ψ₁, ψ₂` cylinder tests). -/
def IsCylTestC (c : ℝ) (g : ℝ × ℝ → ℂ) : Prop :=
  ∃ ψ₁ ψ₂ : ℝ × ℝ → ℝ, B0579.IsCylTest c ψ₁ ∧ B0579.IsCylTest c ψ₂ ∧
    g = fun x => (ψ₁ x : ℂ) + Complex.I * (ψ₂ x : ℂ)

/-- **(H3.1) The heat flow of a test converges to it** (SP 2819-2836): for a complexified
cylinder test `g`, `e^{ντΔ} g → g` in `X_{-m,c}` as `τ → 0+` (`m > 8`: `|G_{ντ} * g - g| ≤
‖∇g‖_∞ ∫ G_{ντ}(z)|z| dz = O(√τ)` uniformly, and `cellMeasure c (-m)` is finite). -/
def AdjHeatS0TestLimit (m : ℝ) : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ g : ℝ × ℝ → ℂ, IsCylTestC c g →
    Tendsto (fun τ => eLpNorm (fun x => adjS0Fun ν c τ g x - g x) 2
      (B0579.cellMeasure c (-m))) (𝓝[>] 0) (𝓝 0)

/-- **(H3.2) Complexified cylinder tests are dense in `X_{-m,c}`** (SP 2819-2836; smooth
fields with compact support in the open cell `(-c/2, c/2) × ℝ` are dense in
`L²(⟨x⟩^{-2m} dx)` and extend to cylinder tests; cf. `Sob.W.cylinder_dense_smooth`). -/
def AdjCylTestDense (m : ℝ) : Prop :=
  ∀ c : ℝ, 0 < c → Dense {w : AdjX c m | ∃ g : ℝ × ℝ → ℂ, IsCylTestC c g ∧
    (⇑w : ℝ × ℝ → ℂ) =ᵐ[B0579.cellMeasure c (-m)] g}

/-- **(H3) Strong continuity of the heat flow at age zero** (SP 2819-2836): for every
`f ∈ X_{-m,c}`, `e^{ντΔ} f → f` in `X_{-m,c}` as `τ → 0+`. -/
def AdjHeatS0StrongZero (m : ℝ) : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ w : AdjX c m,
    Tendsto (fun τ => eLpNorm (fun x => adjS0Fun ν c τ (⇑w) x - w x) 2
      (B0579.cellMeasure c (-m))) (𝓝[>] 0) (𝓝 0)

/-! ## (H4): the semigroup laws -/

/-- **(H4.1) `e^{νaΔ} e^{νbΔ} = e^{ν(a+b)Δ}` on `X_{-m,c}`** (SP 2819-2836; Fubini and the
Gaussian convolution identity `G_{νa} * G_{νb} = G_{ν(a+b)}`, `B0289.heatKernel2_conv_eq`,
`B0289.integral_heatKernel2_conv`; the inner function is periodic, `perRep_adjKerOp`). -/
def AdjHeatSemigroupS0 (m : ℝ) : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ a b : ℝ, 0 < a → 0 < b → a + b ≤ 1 → ∀ w : AdjX c m,
    adjS0Fun ν c a (adjS0Fun ν c b ⇑w) =ᵐ[B0579.cellMeasure c (-m)] adjS0Fun ν c (a + b) ⇑w

/-- **(H4.2) `e^{νaΔ} ∂_j e^{νbΔ} = ∂_j e^{ν(a+b)Δ}` on `X_{-m,c}`** (SP 2819-2836; Fubini
and `G_{νa} * ∂_j G_{νb} = ∂_j G_{ν(a+b)}`,
`integral_heatKernel2_gradHeatKernel2_conv` of the forward model). -/
def AdjHeatSemigroupGrad (m : ℝ) : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ a b : ℝ, 0 < a → 0 < b → a + b ≤ 1 →
    ∀ (j : Fin 2) (w : AdjX c m),
      adjS0Fun ν c a (adjKerOp c (adjHeatGradKer ν b j) ⇑w) =ᵐ[B0579.cellMeasure c (-m)]
        adjKerOp c (adjHeatGradKer ν (a + b) j) ⇑w

/-- **(H4) The semigroup laws of the free part** (SP 2819-2836). -/
def AdjHeatSemigroup (m : ℝ) : Prop := AdjHeatSemigroupS0 m ∧ AdjHeatSemigroupGrad m

/-! ## The smoothed tests -/

/-- **Rapid `η`-decay of the smoothed tests, uniform in the age** (SP 2819-2836, the dual heat
flow of a cylinder test): for a cylinder test `ψ` (`|ψ| ≤ M`, `ψ = 0` for `|η| > R`),
`|P_θ ψ(x)| ≤ C (1 + x₂²)^{-k}` for `θ ∈ [0, Θ]` (Gaussian tail of `G_θ` in `η`). -/
def AdjSmoothDecay : Prop :=
  ∀ c : ℝ, 0 < c → ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest c ψ → ∀ Θ k : ℝ, 0 ≤ Θ → 0 ≤ k →
    ∃ C : ℝ, ∀ θ ∈ Icc (0 : ℝ) Θ, ∀ x : ℝ × ℝ,
      |Exist.cylHeatSmooth c θ ψ x| ≤ C * (1 + x.2 ^ 2) ^ (-k)

/-! ## (H5): the weak heat equation -/

/-- **Unfolding the periodic lift against a test** (SP 2819-2836; Fubini on `C_c × ℝ²`, the
substitution `y = x - z`, and the translation invariance of cell integrals of `c`-periodic
functions, `Cyl.integral_cell_comp_add`): if `adjKerOp c k` has a Young bound on `X_{-m,c}`,
then for `f ∈ X_{-m,c}` and a test `ψ`,
`∫_{C_c} (∫ k(x - y) f̃(y) dy) ψ(x) dx = ∫_{C_c} f(x) (∫ k(z) ψ(x + z) dz) dx` (absolute
convergence: `∫_{C_c} (∫ |k(x - y)| |f̃(y)| dy) |ψ(x)| dx < ∞` by `KerYoung` and weighted
Cauchy-Schwarz, `ψ` bounded with bounded `η`-support). -/
def AdjKerUnfold (m : ℝ) : Prop :=
  ∀ c : ℝ, 0 < c → ∀ k : ℝ × ℝ → ℝ, Continuous k → ∀ M : ℝ, KerYoung c m k M →
    ∀ (w : AdjX c m) (ψ : ℝ × ℝ → ℝ), B0579.IsCylTest c ψ →
      ∫ x in B0579.cell c, adjKerOp c k (⇑w) x * (ψ x : ℂ) =
        ∫ x in B0579.cell c, w x * ((∫ z, k z * ψ (x + z) : ℝ) : ℂ)

/-- **(H5.1) The dual identity of the heat flow** (SP 2819-2836):
`∫_{C_c} (e^{νθΔ} f) ψ = ∫_{C_c} f (P_{νθ} ψ)` for `θ ∈ (0, 1]` (`AdjKerUnfold` with the Young
bound of H1, then `∫ G(z) ψ(x + z) dz = ∫ G(w) ψ(x - w) dw = P_{νθ}ψ(x)`, `G` even). -/
def AdjHeatS0Dual (m : ℝ) : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ θ ∈ Ioc (0 : ℝ) 1, ∀ (w : AdjX c m) (ψ : ℝ × ℝ → ℝ),
    B0579.IsCylTest c ψ →
      ∫ x in B0579.cell c, adjS0Fun ν c θ (⇑w) x * (ψ x : ℂ) =
        ∫ x in B0579.cell c, w x * (Exist.cylHeatSmooth c (ν * θ) ψ x : ℂ)

/-- **(H5.2) The time identity of the smoothed tests** (SP 2819-2836):
`∫ f P_{ντ}ψ = ∫ f ψ + ν ∫_0^τ ∫ f P_{νr}Δψ dr` for `f ∈ X_{-m,c}`, `τ ∈ (0, 1]`
(`AdjFluxPairDuhamel` at `y = (0, f)`, `θ = ντ`, and the substitution `η = νr`). -/
def AdjHeatS0Time (m : ℝ) : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ (w : AdjX c m) (ψ : ℝ × ℝ → ℝ), B0579.IsCylTest c ψ →
    ∀ τ ∈ Ioc (0 : ℝ) 1,
      ∫ x in B0579.cell c, w x * (Exist.cylHeatSmooth c (ν * τ) ψ x : ℂ) =
        (∫ x in B0579.cell c, w x * (ψ x : ℂ)) +
          ∫ r in (0 : ℝ)..τ, (ν : ℂ) *
            ∫ x in B0579.cell c, w x * (Exist.cylHeatSmooth c (ν * r) (lapP ψ) x : ℂ)

/-- **(H5) The weak heat equation of the free flow** (SP 2819-2836, weak identity (a) of
`AdjHeatWeak` at the level of representatives): for `f ∈ X_{-m,c}`, a test `ψ`, `τ ∈ (0, 1]`,
`∫ (e^{ντΔ} f) ψ = ∫ f ψ + ∫_0^τ ν ∫ (e^{νrΔ} f) Δψ dr`. -/
def AdjHeatS0Weak (m : ℝ) : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ (w : AdjX c m) (ψ : ℝ × ℝ → ℝ), B0579.IsCylTest c ψ →
    ∀ τ ∈ Ioc (0 : ℝ) 1,
      ∫ x in B0579.cell c, adjS0Fun ν c τ (⇑w) x * (ψ x : ℂ) =
        (∫ x in B0579.cell c, w x * (ψ x : ℂ)) +
          ∫ r in (0 : ℝ)..τ, (ν : ℂ) *
            ∫ x in B0579.cell c, adjS0Fun ν c r (⇑w) x * (lapP ψ x : ℂ)

/-! ## (H6): the tested Duhamel identity of the response -/

/-- The tested response `Λ_θ(y; ψ) = ∫_{C_c} S(θ)(F, h) ψ` at the level of representatives
(`y = (F, h) ∈ AdjY`). -/
def adjRespPair {m : ℝ} (ν c θ : ℝ) (y : AdjY c m) (ψ : ℝ × ℝ → ℝ) : ℂ :=
  ∫ x in B0579.cell c, adjSFun ν c θ (fun j => ⇑(y.1 j)) (⇑y.2) x * (ψ x : ℂ)

/-- The flux pairing `ℓ(y; φ) = ∫ F₀ ∂₀φ + ∫ F₁ ∂₁φ + ∫ h φ` of `y = (F, h) ∈ AdjY` with a
smooth function `φ` (the source term of weak identity (b) of `AdjHeatWeak`). -/
def adjFluxPair {c m : ℝ} (y : AdjY c m) (φ : ℝ × ℝ → ℝ) : ℂ :=
  (∫ x in B0579.cell c, y.1 0 x * (B0579.pd 0 φ x : ℂ)) +
    (∫ x in B0579.cell c, y.1 1 x * (B0579.pd 1 φ x : ℂ)) +
      ∫ x in B0579.cell c, y.2 x * (φ x : ℂ)

/-- **(H6.1a) The dual identity of the kernel gradient** (SP 2819-2836): for `θ ∈ (0, 1]`,
`∫_{C_c} (∂_j G_{νθ} * f̃) ψ = -∫_{C_c} f ∂_j(P_{νθ}ψ)` (`AdjKerUnfold` with the Young bound of
H2, then `∫ ∂_j G(z) ψ(x + z) dz = -∫ G(z) ∂_jψ(x + z) dz = -P(∂_jψ)(x)` by one integration by
parts in `z_j` (`hasDerivAt_adjHeatKer_fst/snd`), `G` even, and `Exist.pd_cylHeatSmooth`). -/
def AdjHeatGradDual (m : ℝ) : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ θ ∈ Ioc (0 : ℝ) 1, ∀ (j : Fin 2) (w : AdjX c m)
    (ψ : ℝ × ℝ → ℝ), B0579.IsCylTest c ψ →
      ∫ x in B0579.cell c, adjKerOp c (adjHeatGradKer ν θ j) (⇑w) x * (ψ x : ℂ) =
        -∫ x in B0579.cell c, w x * (B0579.pd j (Exist.cylHeatSmooth c (ν * θ) ψ) x : ℂ)

/-- **(H6.1) The dual identity of the response** (SP 2819-2836): for `θ ∈ (0, 1]`,
`∫ S(θ)(F, h) ψ = ∫ F·∇(P_{νθ}ψ) + ∫ h P_{νθ}ψ` (the `h`-part is `AdjHeatS0Dual`; for the
divergence part `∫ ∂_jG(z) ψ(y + z) dz = -∂_j P_θ ψ(y)` by one integration by parts,
`hasDerivAt_adjHeatKer_fst/snd`). -/
def AdjHeatRespDual (m : ℝ) : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ θ ∈ Ioc (0 : ℝ) 1, ∀ (y : AdjY c m) (ψ : ℝ × ℝ → ℝ),
    B0579.IsCylTest c ψ → adjRespPair ν c θ y ψ = adjFluxPair y (Exist.cylHeatSmooth c (ν * θ) ψ)

/-- **(H6.2a) The Duhamel identity of the smoothed tests, paired with one source**
(SP 2819-2836): for `y ∈ AdjY`, a test `φ` and `θ ≥ 0`,
`ℓ(y; P_θφ) = ℓ(y; φ) + ∫_0^θ ℓ(y; P_ηΔφ) dη` (`Exist.cylHeatSmooth_duhamel`,
`Exist.pd_cylHeatSmooth_duhamel`, Fubini on `C_c × [0, θ]` with the decay `AdjSmoothDecay`;
forward analogue `Exist.FluxPairHeatDuhamel`). -/
def AdjFluxPairDuhamel (m : ℝ) : Prop :=
  ∀ c : ℝ, 0 < c → ∀ (y : AdjY c m) (φ : ℝ × ℝ → ℝ), B0579.IsCylTest c φ → ∀ θ : ℝ, 0 ≤ θ →
    adjFluxPair y (Exist.cylHeatSmooth c θ φ) =
      adjFluxPair y φ + ∫ η in (0 : ℝ)..θ, adjFluxPair y (Exist.cylHeatSmooth c η (lapP φ))

/-- **(H6.2b) Joint continuity of the smoothed source pairing** (SP 2819-2836): along a source
path `F` continuous on `[a, b]`, `(r, θ) ↦ ℓ(F(r); P_θ g)` is continuous on `[a, b] × [0, Θ]`
(dominated convergence with `AdjSmoothDecay` and `Exist.continuous_pd_cylHeatSmooth_joint`;
forward analogue `Exist.FluxPairHeatContinuous`). -/
def AdjFluxPairContinuous (m : ℝ) : Prop :=
  ∀ c : ℝ, 0 < c → ∀ (F : ℝ → AdjY c m) (a b : ℝ), ContinuousOn F (Icc a b) →
    ∀ g : ℝ × ℝ → ℝ, B0579.IsCylTest c g → ∀ Θ : ℝ, 0 ≤ Θ →
      ContinuousOn (fun p : ℝ × ℝ => adjFluxPair (F p.1) (Exist.cylHeatSmooth c p.2 g))
        (Icc a b ×ˢ Icc (0 : ℝ) Θ)

/-- **(H6.2) The Duhamel identity of the smoothed tests** (SP 2819-2836): for a continuous
source path `F` on `[a, b] ⊆ [a, a + 1]` and `τ ∈ [a, b]`,
`∫_a^τ ℓ(F(r); P_{ν(τ-r)}ψ) dr = ν ∫_a^τ ∫_a^r ℓ(F(σ); P_{ν(r-σ)}Δψ) dσ dr + ∫_a^τ ℓ(F(r); ψ) dr`
(`AdjFluxPairDuhamel` at `θ = ν(τ - r)`, the substitution `η = ν(u - r)`, and Fubini on the
triangle `a ≤ r ≤ u ≤ τ`, justified by `AdjFluxPairContinuous`; the forward analogue is
`Exist.UnitHeatDuhamel Exist.cylHeatSmooth`, proved in
`Clock/Existence/UnitHeatWeak/DuhamelOf.lean`). -/
def AdjHeatRespTime (m : ℝ) : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ (F : ℝ → AdjY c m) (a b : ℝ), a ≤ b → b ≤ a + 1 →
    ContinuousOn F (Icc a b) → ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest c ψ → ∀ τ ∈ Icc a b,
      ∫ r in a..τ, adjFluxPair (F r) (Exist.cylHeatSmooth c (ν * (τ - r)) ψ) =
        (∫ r in a..τ, (ν : ℂ) *
          ∫ σ in a..r, adjFluxPair (F σ) (Exist.cylHeatSmooth c (ν * (r - σ)) (lapP ψ))) +
          ∫ r in a..τ, adjFluxPair (F r) ψ

/-- **(H6) The tested Duhamel identity of the response** (SP 2819-2836, weak identity (b) of
`AdjHeatWeak` after pairing): for a continuous source path `F` on `[a, b] ⊆ [a, a + 1]` and
`τ ∈ [a, b]`, `∫_a^τ Λ_{τ-r}(F(r); ψ) dr = ν ∫_a^τ ∫_a^r Λ_{r-σ}(F(σ); Δψ) dσ dr +
∫_a^τ ℓ(F(r); ψ) dr`. -/
def AdjHeatDuhamelWeak (m : ℝ) : Prop :=
  ∀ ν c : ℝ, 0 < ν → 0 < c → ∀ (F : ℝ → AdjY c m) (a b : ℝ), a ≤ b → b ≤ a + 1 →
    ContinuousOn F (Icc a b) → ∀ ψ : ℝ × ℝ → ℝ, B0579.IsCylTest c ψ → ∀ τ ∈ Icc a b,
      ∫ r in a..τ, adjRespPair ν c (τ - r) (F r) ψ =
        (∫ r in a..τ, (ν : ℂ) * ∫ σ in a..r, adjRespPair ν c (r - σ) (F σ) (lapP ψ)) +
          ∫ r in a..τ, adjFluxPair (F r) ψ

end UnforcedLeray.Short.IIIa
