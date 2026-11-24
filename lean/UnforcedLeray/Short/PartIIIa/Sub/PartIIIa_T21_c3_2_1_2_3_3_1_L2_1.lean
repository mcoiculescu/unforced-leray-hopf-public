import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_c3_2_1_2_3_3_1
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.BlockContraction.CompactDuhamelGap.VariationOfConstants.RelLeafB1
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.BlockContraction.CompactDuhamelGap.VariationOfConstants.RelLeafB34
import UnforcedLeray.Short.PartIIIa.Clock.FrameStableProof.BlockContraction.CompactDuhamelGap.VariationOfConstants.ComplMildY.Dil
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T23

/-!
# `PartIII-a:T21/c3/2/1/2/3/3/1/2/1`: `FrameTestedDuhamel` by duality with the backward problem

Source of record: `the November 2 reference manuscript` (SP), lines 2898-2918
(frame identities, `(ΛW)' = H₀W`), 2937-2945 (`\bar F_{rel}(z,t) = I_z F(z,t) R_t + S(z,t)(I - Π_t)`),
and the duality of the free cylinder flow with its backward problem (SP 2074-2105).

`F_rel τ σ` is pinned only on data equal on the cell to `J_a⁻¹ f` for real cylinder tests `f`,
and the frame vectors `E_j` (Gaussian tails, not band limited) are not of this form.  The tested
Duhamel identity is therefore proved by duality.  For a real cylinder test `χ` at the age
`t = s(τ)` let `φ` solve the backward problem `∂_r φ = -(νΔφ + v·∇φ)` on `[t₁, t]`, `φ(t) = χ`
(`IIb.bwdSolve_of_buc`), and let `ψ_χ = I_{d(t)} (a(t)⁻¹ χ(√a(t) ·)) ⟨y⟩^{-2m}` (`testPsiFun`).
Then
* (`FrelDualRep`) `⟪ψ_χ, F_rel τ σ X⟫ = N(s,t)⁻¹ a(s)⁻¹ ∫_{C_{d(s)}} X(y) φ(s, √a(s) y) dy`
  (`dualPair`) for every `X`: on pinned data this is the cylinder duality
  `∫_{C_c} χ ω(t) = ∫_{C_c} f φ(s)` (`IIb.cylWeakTimeDep`, `IIb.cyl_rhs_zero`) after the scalings
  `x = √a y`; the exterior part of `\bar F` vanishes on `C_{d(t)}`; density (`RelB3s`).
* (`FrameDualCore`) `σ ↦ dualPair σ (I_d E_j)` is the primitive of `σ ↦ dualPair σ (I_d R_j)`,
  `R_j = E_z - (G_free - β₀) E_j`: in cylinder variables `dualPair σ (I_d E_j) = N⁻¹ ∫_{C_c} φ(s) g(s)`
  with `g(s, x) = a⁻² E_j(x/√a)`; differentiate (`ds/dσ = a²`, `(N⁻¹)' = β₀ N⁻¹`), use the backward
  equation and integrate by parts on the cylinder, and `J_a⁻¹(∂_σ g - a² L g) = E_z - G_free E_j`.
* (`FrelCellSupport`) `F_rel τ σ` maps data supported in `C_{d(s)}` to data supported in `C_{d(t)}`.
* (`DualTestSep`) the tests `ψ_χ` together with the tests vanishing on `C_{d(t)}` separate `L²_m`.
* (`FrameVecReg`) `I_d E_j(s(σ))`, `I_d R_j(s(σ))` lie in `L²_m`, and `σ ↦ I_d R_j` is continuous.

Proved here: `frameTestedDuhamel_of`, assembling `FrameTestedDuhamel κ` from the five leaves with
`relB1_leaf` (uniform bound of `F_rel`), `relB4s_leaf` (strong continuity), and
`IIb.bwdSolve_of_buc` (the backward problem); the leaf `FrelCellSupport` (`frelCellSupport`); and
`frameTestedDuhamel_of'`, which leaves the four leaves `FrameVecReg`, `FrelDualRep`,
`FrameDualCore`, `DualTestSep`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology Metric UnforcedLeray.Blueprint.Planar
open scoped ENNReal ComplexConjugate ContDiff InnerProductSpace

namespace UnforcedLeray.Short.IIIa

open FrameShortBlockSub FrameBlockContractSub CompactDuhamelGapSub BlockPropagatorSub
  VariationOfConstantsSub VariationOfConstantsMildSub

namespace ComplMildTestedSplit

namespace FrameDuhamelSub

/-- The cell length `d(s(σ)) = c/√a(s(σ))` at block moving time `σ`, `c = ν⁻²`. -/
abbrev dOf (ν t₁ σ : ℝ) : ℝ := cellLen (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))

/-- `φ` is the backward solution on `[t₁, t]` of the free cylinder problem with terminal datum `χ`
(`∂_r φ = -(νΔφ + v·∇φ)`, smooth, `c`-periodic, decaying in `η`; the output of
`IIb.bwdSolve_of_buc`, SP 2074-2105). -/
def IsBwdSol (ν : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t₁ t : ℝ)
    (χ : B0579.Plane → ℝ) (φ : ℝ → B0579.Plane → ℝ) : Prop :=
  φ t = χ ∧ UnforcedLeray.Short.IIb.CylEtaSpatial (ν ^ (-2 : ℝ)) t₁ t φ ∧
    ∀ r ∈ Ioo t₁ t, ∀ x : B0579.Plane,
      HasDerivAt (fun r' => φ r' x)
        (-(ν * UnforcedLeray.Short.IIb.lapP (φ r) x + (tr.v r x 0 * B0579.pd 0 (φ r) x +
          tr.v r x 1 * B0579.pd 1 (φ r) x))) r

/-- The moving-variable test `ψ_χ = I_{d} (a⁻¹ χ(√a ·)) ⟨y⟩^{-2m}` (`d = c/√a`), chosen so that
`⟪ψ_χ, Y⟫ = a⁻¹ ∫_{C_d} χ(√a y) Y(y) dy`. -/
def testPsiFun (m c a : ℝ) (χ : B0579.Plane → ℝ) (z : ℂ) : ℂ :=
  (((B0579.cell (cellLen c a)).indicator
      (fun y => a⁻¹ * χ (Real.sqrt a * y.1, Real.sqrt a * y.2)) (cToPlane z) /
    (1 + ‖z‖ ^ 2) ^ m : ℝ) : ℂ)

/-- The pairing `N(s,t)⁻¹ a(s)⁻¹ ∫_{C_{d(s)}} X(y) φ(s, √a(s) y) dy` of the backward solution `φ`
(terminal age `t = s(τ)`) with a moving datum `X` at block time `σ` (`s = s(σ)`). -/
def dualPair (P : PlanarData) (ν t₁ τ : ℝ) (φ : ℝ → B0579.Plane → ℝ) (σ : ℝ) (X : ℂ → ℂ) : ℂ :=
  (((clockN P ν (ageAt ν t₁ σ) (ageAt ν t₁ τ))⁻¹ * (clockA ν (ageAt ν t₁ σ))⁻¹ : ℝ) : ℂ) *
    ∫ z : ℂ, (B0579.cell (dOf ν t₁ σ)).indicator
      (fun y => ((φ (ageAt ν t₁ σ) (Real.sqrt (clockA ν (ageAt ν t₁ σ)) * y.1,
        Real.sqrt (clockA ν (ageAt ν t₁ σ)) * y.2) : ℝ) : ℂ)) (cToPlane z) * X z

/-- The zero-extended frame vector `I_d E_j(s(σ))` (right side of `ERep`). -/
def frameEFun (κ : PlanarFrameKernels) (ν t₁ : ℝ) (j : Fin 2) (σ : ℝ) (z : ℂ) : ℂ :=
  cellZeroExt (dOf ν t₁ σ) (perE κ (dOf ν t₁ σ) j) (cToPlane z)

/-- The zero-extended relative free residual `I_d (E_z - (G_free - β₀) E_j)` (right side of
`RRep`). -/
def frameRFun (κ : PlanarFrameKernels) (P : PlanarData) (ν : ℝ)
    (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ))) (t₁ : ℝ) (j : Fin 2) (σ : ℝ)
    (z : ℂ) : ℂ :=
  cellZeroExt (dOf ν t₁ σ)
    (fun y => movFreeRes κ tr (ageAt ν t₁ σ) j y +
      ((movBeta0 P ν (ageAt ν t₁ σ) : ℝ) : ℂ) * perE κ (dOf ν t₁ σ) j y) (cToPlane z)

/-! ## The five leaves -/

/-- **Leaf V (frame vectors, SP 2891-2905)**: the zero-extended frame vectors and relative free
residuals lie in `L²_m` along the block, and the residual is continuous in `σ` (Gaussian tails of
`E_j` and its derivatives, boundedness of the train velocity; the moving cell boundary is a null
set). -/
def FrameVecReg (κ : PlanarFrameKernels) : Prop :=
  ∀ (P : PlanarData) (m K B b ν : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (t₁ t₂ : ℝ), RelRegularityOrg.RelCtx κ P m K B b ν tr t₁ t₂ →
    ∀ j : Fin 2, ∃ Ej Rj : ℝ → Planar.L2w m,
      ERep κ m B ν t₁ j Ej ∧ RRep κ P m B ν tr t₁ j Rj ∧ ContinuousOn Rj (Icc (0 : ℝ) B)

/-- **Leaf S (cell support, SP 2941-2943)**: `F_rel τ σ` maps data vanishing outside `C_{d(s)}` to
data vanishing outside `C_{d(t)}` (pinned on the cell tests `testW`, whose exterior part is zero;
density `exists_test_approx_cell`; continuity of `F_rel τ σ`). -/
def FrelCellSupport (κ : PlanarFrameKernels) : Prop :=
  ∀ (P : PlanarData) (m K B b ν : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (t₁ t₂ : ℝ), RelRegularityOrg.RelCtx κ P m K B b ν tr t₁ t₂ →
    ∀ F_rel : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m,
      IsPeriodizedRelFreeBlockEvol P ν m tr t₁ B F_rel →
      ∀ σ τ : ℝ, 0 ≤ σ → σ ≤ τ → τ ≤ B → ∀ X ψ : Planar.L2w m,
        (∀ᵐ z ∂volume, cToPlane z ∉ B0579.cell (dOf ν t₁ σ) → (X : ℂ → ℂ) z = 0) →
        (∀ᵐ z ∂volume, cToPlane z ∈ B0579.cell (dOf ν t₁ τ) → (ψ : ℂ → ℂ) z = 0) →
        ⟪ψ, F_rel τ σ X⟫_ℂ = 0

/-- **Leaf D (duality representation, SP 2937-2945, 2074-2105)**: against the test `ψ_χ` of the
terminal age `t = s(τ)`, `F_rel τ σ` is represented by the backward solution `φ` with
`φ(t) = χ`.  On pinned data `X = J_{a(s)}⁻¹ f` on `C_{d(s)}` both sides equal
`N(s,t)⁻¹ ∫_{C_c} χ ω(t) = N(s,t)⁻¹ ∫_{C_c} f φ(s)` (scaling `x = √a y`, the exterior term of
`\bar F` vanishes on `C_{d(t)}`, cylinder duality `IIb.cylWeakTimeDep` + `IIb.cyl_rhs_zero`); both
sides are continuous in `X` and the pinned data are dense (`RelB3s`). -/
def FrelDualRep (κ : PlanarFrameKernels) : Prop :=
  ∀ (P : PlanarData) (m K B b ν : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (t₁ t₂ : ℝ), RelRegularityOrg.RelCtx κ P m K B b ν tr t₁ t₂ →
    ∀ F_rel : ℝ → ℝ → Planar.L2w m →L[ℂ] Planar.L2w m,
      IsPeriodizedRelFreeBlockEvol P ν m tr t₁ B F_rel →
      ∀ τ ∈ Icc (0 : ℝ) B, ∀ χ : B0579.Plane → ℝ, B0579.IsCylTest (ν ^ (-2 : ℝ)) χ →
        ∀ φ : ℝ → B0579.Plane → ℝ, IsBwdSol ν tr t₁ (ageAt ν t₁ τ) χ φ →
        ∀ ψ : Planar.L2w m,
          ⇑ψ =ᵐ[volume] testPsiFun m (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ τ)) χ →
          ∀ σ ∈ Icc (0 : ℝ) τ, ∀ X : Planar.L2w m,
            ⟪ψ, F_rel τ σ X⟫_ℂ = dualPair P ν t₁ τ φ σ ⇑X

/-- **Leaf C (frame Duhamel against the backward problem, SP 2898-2918)**: with
`g(s, x) = a(s)⁻² E_j(s)(x/√a(s))`, `dualPair σ (I_d E_j) = N(s,t)⁻¹ ∫_{C_c} φ(s) g(s)`; its
`σ`-derivative (`ds/dσ = a²`, `d/dσ N(s,t)⁻¹ = β₀ N(s,t)⁻¹`, `∂_s φ = -(νΔφ + v·∇φ)`, periodic
integration by parts on `C_c`, `div v = 0`) is `N⁻¹ ∫_{C_c} φ(s) (∂_σ g - a² L g + β₀ g)`, and
`J_a⁻¹ (∂_σ g - a² L g) = E_z - θ⁻¹ D E_j + V·∇E_j = movFreeRes` (SP 2861-2866, 2905). -/
def FrameDualCore (κ : PlanarFrameKernels) : Prop :=
  ∀ (P : PlanarData) (m K B b ν : ℝ) (tr : UnforcedLeray.B0140.TrainSol ν (ν ^ (-2 : ℝ)))
    (t₁ t₂ : ℝ), RelRegularityOrg.RelCtx κ P m K B b ν tr t₁ t₂ →
    ∀ τ ∈ Icc (0 : ℝ) B, ∀ χ : B0579.Plane → ℝ, B0579.IsCylTest (ν ^ (-2 : ℝ)) χ →
      ∀ φ : ℝ → B0579.Plane → ℝ, IsBwdSol ν tr t₁ (ageAt ν t₁ τ) χ φ →
      ∀ j : Fin 2, ∀ σ₀ ∈ Icc (0 : ℝ) τ,
        dualPair P ν t₁ τ φ σ₀ (frameEFun κ ν t₁ j σ₀) =
          dualPair P ν t₁ τ φ 0 (frameEFun κ ν t₁ j 0) +
            ∫ σ in (0 : ℝ)..σ₀, dualPair P ν t₁ τ φ σ (frameRFun κ P ν tr t₁ j σ)

/-- **Leaf T (separation)**: the tests `ψ_χ` (`χ` real cylinder tests of period `c`) and the tests
vanishing on `C_{c/√a}` separate `L²_m` (`⟪ψ_χ, V⟫ = a⁻¹ ∫_{C_d} χ(√a y) V(y) dy`; fundamental
lemma on the cylinder for the real and imaginary parts of `V(·/√a)`). -/
def DualTestSep : Prop :=
  ∀ m c a : ℝ, 8 < m → 0 < c → 0 < a → ∀ V : Planar.L2w m,
    (∀ χ : B0579.Plane → ℝ, B0579.IsCylTest c χ → ∀ ψ : Planar.L2w m,
      ⇑ψ =ᵐ[volume] testPsiFun m c a χ → ⟪ψ, V⟫_ℂ = 0) →
    (∀ ψ : Planar.L2w m,
      (∀ᵐ z ∂volume, cToPlane z ∈ B0579.cell (cellLen c a) → (ψ : ℂ → ℂ) z = 0) →
        ⟪ψ, V⟫_ℂ = 0) →
    V = 0

/-! ## Assembly -/

theorem dualPair_congr (P : PlanarData) {ν t₁ τ : ℝ} (φ : ℝ → B0579.Plane → ℝ) (σ : ℝ)
    {X Y : ℂ → ℂ} (h : X =ᵐ[volume] Y) :
    dualPair P ν t₁ τ φ σ X = dualPair P ν t₁ τ φ σ Y := by
  unfold dualPair
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [h] with z hz
  rw [hz]

theorem vanish_of_rep {d : ℝ} {X : ℂ → ℂ} {W : ℝ × ℝ → ℂ}
    (h : X =ᵐ[volume] fun z => cellZeroExt d W (cToPlane z)) :
    ∀ᵐ z ∂volume, cToPlane z ∉ B0579.cell d → X z = 0 := by
  filter_upwards [h] with z hz hmem
  rw [hz]
  unfold cellZeroExt
  exact Set.indicator_of_notMem hmem _

/-- Data vanishing on `C_d` are orthogonal to data vanishing off `C_d`. -/
theorem inner_eq_zero_of_supp {m d : ℝ} (ψ Z : Planar.L2w m)
    (hψ : ∀ᵐ z ∂volume, cToPlane z ∈ B0579.cell d → (ψ : ℂ → ℂ) z = 0)
    (hZ : ∀ᵐ z ∂volume, cToPlane z ∉ B0579.cell d → (Z : ℂ → ℂ) z = 0) :
    ⟪ψ, Z⟫_ℂ = 0 := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [(Planar.wMeasure_ac m).ae_le hψ, (Planar.wMeasure_ac m).ae_le hZ] with z h1 h2
  by_cases hmem : cToPlane z ∈ B0579.cell d
  · rw [h1 hmem]
    simp
  · rw [h2 hmem]
    simp

/-- **Leaf S is proved**: `F_rel τ σ` maps data supported in `C_{d(s)}` to data supported in
`C_{d(t)}`.  On `testW φ` the pinned output is `N⁻¹ I_{d(t)} J_{a(t)}⁻¹ ω(t)` (`b1c_pin_eq`, the
exterior part vanishes because `testW φ` is its own cell part); density of `testW φ₁ + i testW φ₂`
in the cell-supported data (`exists_test_approx_cell`) and continuity of `F_rel τ σ`. -/
theorem frelCellSupport (κ : PlanarFrameKernels) : FrelCellSupport κ := by
  intro P m K B b ν tr t₁ t₂ ctx F_rel hFr σ τ hσ hστ hτB X ψ hX hψ
  obtain ⟨_hκ, _hP, hm, _hB, _hb, hν, _hF, htr, ht₁, ht₁₂, _hbt, hBz⟩ := ctx
  have hm1 : 1 < m := by linarith
  have hc : 0 < ν ^ (-2 : ℝ) := Real.rpow_pos_of_pos hν _
  obtain ⟨hs1, hst, _ht2⟩ := RelB4locAux.ageAt_props hν ht₁ ht₁₂ hBz hσ hστ hτB
  have hs0 : 0 ≤ ageAt ν t₁ σ := ht₁.trans hs1
  have ht0 : 0 ≤ ageAt ν t₁ τ := hs0.trans hst
  have has : 0 < clockA ν (ageAt ν t₁ σ) := by unfold clockA; positivity
  have hat : 0 < clockA ν (ageAt ν t₁ τ) := by unfold clockA; positivity
  have hd : 0 < dOf ν t₁ σ := div_pos hc (Real.sqrt_pos.2 has)
  have htest : ∀ (φ : ℝ × ℝ → ℝ) (hφ : B0579.IsCylTest (dOf ν t₁ σ) φ),
      ⟪ψ, F_rel τ σ (RelBlockDiagonalSub.testW m hφ)⟫_ℂ = 0 := by
    intro φ hφ
    have hf := RelBlockDiagonalSub.isCylTest_rescale (c := ν ^ (-2 : ℝ)) has hφ
    obtain ⟨ω₀, hω, -, -⟩ := UnforcedLeray.Short.IIb.freeCylSmoothExists_proof m ν
      (ν ^ (-2 : ℝ)) hm hν hc tr htr (ageAt ν t₁ σ) hs0 _ hf
    have hV := RelBlockDiagonalSub.coeFn_testW m hφ
    have hXc : ∀ᵐ z ∂volume, cToPlane z ∈ B0579.cell (dOf ν t₁ σ) →
        (RelBlockDiagonalSub.testW m hφ : ℂ → ℂ) z =
          JscaleInv (clockA ν (ageAt ν t₁ σ)) (fun x =>
            (((clockA ν (ageAt ν t₁ σ) ^ 2)⁻¹ * φ (x.1 / Real.sqrt (clockA ν (ageAt ν t₁ σ)),
              x.2 / Real.sqrt (clockA ν (ageAt ν t₁ σ))) : ℝ) : ℂ)) (cToPlane z) := by
      filter_upwards [(Planar.volume_ac m).ae_le hV] with z hz hmem
      rw [hz, RelBlockDiagonalSub.jscaleInv_rescale has φ, cellZeroExt,
        Set.indicator_of_mem hmem]
    have hpin := hFr σ τ hσ hστ hτB _ hf ω₀ hω _ hXc
    have heq := RelRegularityOrg2.RelB1cAux.b1c_pin_eq hm1 hc has hat _ _ (hf.memLp m) hXc
      (ω₀ (ageAt ν t₁ τ)) (hω.memX _ hst) _ hpin
    have hcp : RelBlockDiagonalSub.testW m hφ - RelRegularityOrg2.RelB1cAux.b1cCellPart hm1
        (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ σ))
        (fun x => (clockA ν (ageAt ν t₁ σ) ^ 2)⁻¹ * φ (x.1 / Real.sqrt (clockA ν (ageAt ν t₁ σ)),
          x.2 / Real.sqrt (clockA ν (ageAt ν t₁ σ)))) = 0 := by
      rw [sub_eq_zero]
      apply Lp.ext
      filter_upwards [hV, RelRegularityOrg2.RelB1cAux.b1c_coeFn_cellPart hm1 hc has (hf.memLp m)]
        with z h1 h2
      rw [h1, h2]
      unfold cellZeroExt
      congr 1
      funext y
      rw [RelBlockDiagonalSub.jscaleInv_rescale has φ]
    rw [heq, hcp, map_zero, add_zero, inner_smul_right]
    have hZ := RelRegularityOrg2.RelB1cAux.b1c_coeFn_cellPart hm1 hc hat (hω.memX _ hst)
    rw [inner_eq_zero_of_supp (d := dOf ν t₁ τ) ψ _ hψ ?_, mul_zero]
    filter_upwards [(Planar.volume_ac m).ae_le hZ] with z hz hmem
    rw [RelRegularityOrg2.RelB1cAux.b1cCellPart] at hz
    rw [hz]
    unfold cellZeroExt
    exact Set.indicator_of_notMem hmem _
  refine eq_of_forall_dist_le fun ε hε => ?_
  have hδ : 0 < ε / ((‖ψ‖ + 1) * (‖F_rel τ σ‖ + 1)) := by positivity
  obtain ⟨φ₁, φ₂, h₁, h₂, happrox⟩ :=
    RelBlockDiagonalSub.exists_test_approx_cell (m := m) hd X hX hδ
  set A := RelBlockDiagonalSub.testW m h₁ + Complex.I • RelBlockDiagonalSub.testW m h₂ with hA
  have hA0 : ⟪ψ, F_rel τ σ A⟫_ℂ = 0 := by
    rw [hA, map_add, map_smul, inner_add_right, inner_smul_right, htest φ₁ h₁, htest φ₂ h₂]
    ring
  have hsplit : ⟪ψ, F_rel τ σ X⟫_ℂ = ⟪ψ, F_rel τ σ (X - A)⟫_ℂ := by
    rw [map_sub, inner_sub_right, hA0, sub_zero]
  rw [dist_zero_right, hsplit]
  have hn1 : ‖ψ‖ ≤ ‖ψ‖ + 1 := by linarith
  have hn2 : ‖F_rel τ σ‖ ≤ ‖F_rel τ σ‖ + 1 := by linarith
  calc ‖⟪ψ, F_rel τ σ (X - A)⟫_ℂ‖ ≤ ‖ψ‖ * ‖F_rel τ σ (X - A)‖ := norm_inner_le_norm _ _
    _ ≤ ‖ψ‖ * (‖F_rel τ σ‖ * ‖X - A‖) :=
        mul_le_mul_of_nonneg_left ((F_rel τ σ).le_opNorm _) (norm_nonneg _)
    _ ≤ (‖ψ‖ + 1) * ((‖F_rel τ σ‖ + 1) * (ε / ((‖ψ‖ + 1) * (‖F_rel τ σ‖ + 1)))) := by
        gcongr
    _ = ε := by field_simp

end FrameDuhamelSub

open FrameDuhamelSub in
/-- **`FrameTestedDuhamel` from the five leaves** (SP 2898-2918, 2937-2945). -/
theorem frameTestedDuhamel_of (κ : PlanarFrameKernels) (hV : FrameVecReg κ)
    (hS : FrelCellSupport κ) (hD : FrelDualRep κ) (hC : FrameDualCore κ) (hT : DualTestSep) :
    FrameTestedDuhamel κ := by
  intro hκ P hP m hm K B b hB hb ν hν hF tr htr t₁ t₂ ht₁ h12 hbt hBe F_rel hFr j
  have ctx : RelRegularityOrg.RelCtx κ P m K B b ν tr t₁ t₂ :=
    ⟨hκ, hP, hm, hB, hb, hν, hF, htr, ht₁, h12, hbt, hBe⟩
  obtain ⟨Ej, Rj, hE, hR, hRc⟩ := hV P m K B b ν tr t₁ t₂ ctx j
  obtain ⟨M, hM⟩ := relB1_leaf κ P m K B b ν tr t₁ t₂ ctx F_rel hFr
  have hcont4 := relB4s_leaf κ P m K B b ν tr t₁ t₂ ctx F_rel hFr ⟨M, hM⟩
  refine ⟨Ej, Rj, hE, hR, ?_⟩
  have hE' : ∀ σ ∈ Icc (0 : ℝ) B, ⇑(Ej σ) =ᵐ[volume] frameEFun κ ν t₁ j σ := hE
  intro τ hτ ψ _hψ
  have hFR : ContinuousOn (fun σ => F_rel τ σ (Rj σ)) (Icc 0 τ) := by
    intro σ hσ
    have hmap : MapsTo (fun x : ℝ => (τ, x)) (Icc 0 τ) (blockTriangle B) :=
      fun x hx => ⟨hx.1, hx.2, hτ.2⟩
    have h1 : ContinuousOn (fun x : ℝ => F_rel τ x (Rj σ)) (Icc 0 τ) :=
      (hcont4 (Rj σ)).comp (continuousOn_const.prodMk continuousOn_id) hmap
    exact ComplMildYAux.continuousWithinAt_clm_apply (C := M)
      (fun x hx => hM (τ, x) ⟨hx.1, hx.2, hτ.2⟩) (h1 σ hσ)
      ((hRc.mono (Icc_subset_Icc le_rfl hτ.2)) σ hσ)
  have hscal : ContinuousOn (fun σ => ⟪ψ, F_rel τ σ (Rj σ)⟫_ℂ) (Icc 0 τ) :=
    continuousOn_const.inner hFR
  refine ⟨hscal.intervalIntegrable_of_Icc hτ.1, ?_⟩
  intro σ₀ hσ₀
  have hsub0 : Icc (0 : ℝ) σ₀ ⊆ Icc 0 τ := Icc_subset_Icc le_rfl hσ₀.2
  have hIσ : IntervalIntegrable (fun σ => F_rel τ σ (Rj σ)) volume 0 σ₀ :=
    (hFR.mono hsub0).intervalIntegrable_of_Icc hσ₀.1
  set V : Planar.L2w m := F_rel τ σ₀ (Ej σ₀) - F_rel τ 0 (Ej 0) -
    ∫ σ in (0 : ℝ)..σ₀, F_rel τ σ (Rj σ) with hVdef
  have hinner : ∀ ψ' : Planar.L2w m, ⟪ψ', V⟫_ℂ = ⟪ψ', F_rel τ σ₀ (Ej σ₀)⟫_ℂ -
      ⟪ψ', F_rel τ 0 (Ej 0)⟫_ℂ - ∫ σ in (0 : ℝ)..σ₀, ⟪ψ', F_rel τ σ (Rj σ)⟫_ℂ := by
    intro ψ'
    rw [hVdef, inner_sub_right, inner_sub_right]
    congr 1
    have := (innerSL ℂ ψ').intervalIntegral_comp_comm hIσ
    simp only [innerSL_apply_apply] at this
    exact this.symm
  have hτ0 : (0 : ℝ) ∈ Icc (0 : ℝ) τ := ⟨le_rfl, hτ.1⟩
  have hB0 : (0 : ℝ) ∈ Icc (0 : ℝ) B := ⟨le_rfl, hB.le⟩
  have hσ₀B : σ₀ ∈ Icc (0 : ℝ) B := ⟨hσ₀.1, hσ₀.2.trans hτ.2⟩
  have huI : ∀ σ ∈ uIcc (0 : ℝ) σ₀, σ ∈ Icc (0 : ℝ) τ := fun σ hσ =>
    hsub0 (by rwa [uIcc_of_le hσ₀.1] at hσ)
  have huB : ∀ σ ∈ uIcc (0 : ℝ) σ₀, σ ∈ Icc (0 : ℝ) B := fun σ hσ =>
    ⟨(huI σ hσ).1, (huI σ hσ).2.trans hτ.2⟩
  have hage : t₁ ≤ ageAt ν t₁ τ := (ageAt_mem_Icc hν ht₁ h12 hBe hτ).1
  have ha : 0 < clockA ν (ageAt ν t₁ τ) := by
    unfold clockA
    have : 0 ≤ ageAt ν t₁ τ := ht₁.trans hage
    positivity
  have hV0 : V = 0 := by
    refine hT m (ν ^ (-2 : ℝ)) (clockA ν (ageAt ν t₁ τ)) hm (Real.rpow_pos_of_pos hν _) ha V
      ?_ ?_
    · intro χ hχ ψ' hψ'
      obtain ⟨φ, hφt, hφs, hφd⟩ := UnforcedLeray.Short.IIb.bwdSolve_of_buc hν
        (Real.rpow_pos_of_pos hν _) htr ht₁ hage hχ
      have hφ : IsBwdSol ν tr t₁ (ageAt ν t₁ τ) χ φ := ⟨hφt, hφs, hφd⟩
      have hrep := hD P m K B b ν tr t₁ t₂ ctx F_rel hFr τ hτ χ hχ φ hφ ψ' hψ'
      have hcore := hC P m K B b ν tr t₁ t₂ ctx τ hτ χ hχ φ hφ j σ₀ hσ₀
      rw [hinner, hrep σ₀ hσ₀ (Ej σ₀), hrep 0 hτ0 (Ej 0),
        intervalIntegral.integral_congr (g := fun σ => dualPair P ν t₁ τ φ σ ⇑(Rj σ))
          (fun σ hσ => hrep σ (huI σ hσ) (Rj σ)),
        dualPair_congr P φ σ₀ (hE' σ₀ hσ₀B), dualPair_congr P φ 0 (hE' 0 hB0),
        intervalIntegral.integral_congr (g := fun σ => dualPair P ν t₁ τ φ σ
            (frameRFun κ P ν tr t₁ j σ))
          (fun σ hσ => dualPair_congr P φ σ (hR σ (huB σ hσ)))]
      rw [hcore]
      ring
    · intro ψ' hψ'
      have hS' := hS P m K B b ν tr t₁ t₂ ctx F_rel hFr
      rw [hinner, hS' σ₀ τ hσ₀.1 hσ₀.2 hτ.2 (Ej σ₀) ψ' (vanish_of_rep (hE σ₀ hσ₀B)) hψ',
        hS' 0 τ le_rfl hτ.1 hτ.2 (Ej 0) ψ' (vanish_of_rep (hE 0 hB0)) hψ',
        intervalIntegral.integral_congr (g := fun _ => (0 : ℂ))
          (fun σ hσ => hS' σ τ (huI σ hσ).1 (huI σ hσ).2 hτ.2 (Rj σ) ψ'
            (vanish_of_rep (hR σ (huB σ hσ))) hψ')]
      simp
  have hfin := hinner ψ
  rw [hV0, inner_zero_right] at hfin
  linear_combination -hfin

open FrameDuhamelSub in
/-- **`FrameTestedDuhamel` from the four open leaves** (`FrelCellSupport` is `frelCellSupport`). -/
theorem frameTestedDuhamel_of' (κ : PlanarFrameKernels) (hV : FrameVecReg κ)
    (hD : FrelDualRep κ) (hC : FrameDualCore κ) (hT : DualTestSep) : FrameTestedDuhamel κ :=
  frameTestedDuhamel_of κ hV (frelCellSupport κ) hD hC hT

end ComplMildTestedSplit

end UnforcedLeray.Short.IIIa
