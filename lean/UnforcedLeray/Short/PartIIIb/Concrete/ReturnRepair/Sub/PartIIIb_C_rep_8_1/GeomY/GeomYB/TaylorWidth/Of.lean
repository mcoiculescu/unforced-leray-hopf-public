import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomY.GeomYB.TaylorWidth.Comm

/-!
# `PartIII-b:C/rep/8/1/1/2/5/2` (`GeomYB.TaylorWidth`): reduction to two commutator leaves

Source `the November 2 reference manuscript`
lines 5427-5432 ("For `Y` use the exact formula `Y = 𝒞_{χ_y}W_μ + [D_{μ+1},𝒞_{χ_y}](W_μ-W_{μ+1})`.
Apply the spatial kernel comparison to these terms separately"), 5383-5387 (the same commutator
formula for `Y^mt`; "the Laplacian of the stream-cutoff field is retained even though the uncut
fields are harmonic there"), 5415-5427 (finite transverse width by Taylor's formula with the first
transverse moment, strict radial gap, heat-to-Newton error), 4764-4791 (`Σ_M`, `V_{μ,M}`,
`W^mt = ε²V(ε·)`), 5376, 5141-5142, 4772-4774 (`ThinAziZero`: the swirl-free thin tensor).

`taylorWidthYBBound_of` proves `D.TaylorWidthYBBound` from two leaves, the Hessian-level analogues
of `SepMeanFar` (`GeomX/TaylorWidth/Leaf.lean`) and `TWBridge.NewtonBridge`
(`GeomX/TaylorWidth/Bridge.lean`) for the commutator `YBComm.comm = [D_{μ+1}, 𝒞_y]`:

* `SepCommMeanFar` (the analytic leaf): for a phase-free planar source `G` supported in
  `|x'| ≤ √(5ν/6)`, at every young receiver `ν ≤ |x_obs'|²`,
  `|D_y[D_{μ+1},𝒞_y]X₀(G)(ε⁻¹x_obs) - D_y[D_{μ+1},𝒞_y]X₀^mt(G)(ε⁻¹x_obs)|
  ≤ C(1 + ν⁻¹ + c)^k ε⁴ |x_obs'|^{-5} N₁(G)`, with `X₀(G) = YBComm.srcX0` the finite-width heat
  field and `X₀^mt(G) = YBComm.newtonX0` the zero-width Newton field;
* `NewtonCommBridge` (the identification of the Newton side): for swirl-free thin stresses with
  finite `N`, `D_y mnYB = D_y[D_{μ+1},𝒞_y]X₀^mt(Ḡ)` at the young receivers, `Ḡ = YBComm.meanSrc T`.

All bridges are proved (`YBComm`): `actYBMid T = [D_{μ+1},𝒞_y] zMid T` and
`zMid T = X₀(Ḡ)` (`zMid_eq_srcX0`), `N₁(meanLift Ḡ) ≤ πN` (`thinMoment_meanSrc_le`), the receiver
`|x_obs'|^{-5} = s^{5/2}`, `ν ≤ |x_obs'|²` (`receiver`) and `1 + ν⁻¹ + c ≤ 3ν⁻²` (`poly3`).

Why the leaf is the commutator and not the Hessian of `X₀` alone: `[D_{μ+1},𝒞_y]X₀` is
`-½(y·∇χ_y)X₀ - ν(Δχ_y X₀ + 2∇χ_y·∇X₀)` plus the stream-primitive terms
`((A - 1)a)Ψ_{X₀}e_z`, `[Δ, a]Ψ_{X₀}e_z` (`a = χ_y'/r`, `Ψ_{AZ} = AΨ_Z + Ψ_Z`,
`Ψ_{ΔZ} = (∂_r² - r⁻¹∂_r + ∂_z²)Ψ_Z`, 4207-4213), so its `D_y` needs the comparison of
`X₀, DX₀, D²X₀` and of the outward primitive `Ψ_{X₀}` with up to three derivatives, all on the
cutoff transition annulus `4/5 ≤ ν s ≤ 1` (outside it the commutator vanishes near the receiver).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace YBWidth

open YBComm PhasePrim

/-- **Leaf: finite width and heat-to-Newton for the commutator** (source 5427-5432, 5383-5387,
5415-5427; SP 3735-3766 with the degree `-5` of `D∇K` kept; Hessian level): for a measurable
phase-free planar source `G(x',Y)` supported in `|x'| ≤ √(5ν/6)`, at every young receiver
`|x_obs'|² ≥ ν`, the commutator `[D_{μ+1},𝒞_y]` of the finite-width heat field
`X₀(G) = Re(W_μ - W_{μ+1})(thinSource ε (meanLift G))` and that of the zero-width Newton field
`X₀^mt(G) = ε²Re(V_{μ,0} - V_{μ+1,0})(G)(ε·)` have `D_y` within
`C(1 + ν⁻¹ + c)^k ε⁴ |x_obs'|^{-5} N₁(meanLift G)` (transverse Taylor remainder along segments
with the strict radial gap, heat-to-Newton `|D^j(K_t - K_0)| ≤ Ct|x|^{-5-j}`, both one derivative
higher than `SepMeanFar`, and the same for the outward primitive `Ψ`). -/
def SepCommMeanFar : Prop :=
  ∀ χy : ℝ → ℝ, IsStreamCutoff χy → ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧
    ∀ ν c ε μ : ℝ, 0 < ν → ν ≤ 1 → 0 < c → 0 < ε → ε ≤ 1 →
      0 < μ → μ < 1 / 4 →
      ∀ G : ℝ × ℝ → ℝ → Matrix (Fin 3) (Fin 3) ℝ,
        (∀ i j, Measurable fun w : (ℝ × ℝ) × ℝ => G w.1 w.2 i j) →
        (∀ x' Y, Real.sqrt (5 * ν / 6) < Real.sqrt (x'.1 ^ 2 + x'.2 ^ 2) → G x' Y = 0) →
        ∀ (τ : ℝ) (xo : Space), ν ≤ xo 0 ^ 2 + xo 1 ^ 2 →
          ‖fderiv ℝ (comm ν μ ε⁻¹ χy (srcX0 ν μ (IIIa.thinSource ε (IIIa.meanLift G))) τ)
                (ε⁻¹ • xo) -
              fderiv ℝ (comm ν μ ε⁻¹ χy (newtonX0 ε μ G) τ) (ε⁻¹ • xo)‖ₑ ≤
            ENNReal.ofReal (C * (1 + ν⁻¹ + c) ^ k * ε ^ 4 *
              Real.sqrt (xo 0 ^ 2 + xo 1 ^ 2) ^ (-5 : ℝ)) * IIIa.thinMoment c (IIIa.meanLift G)

/-- **Leaf: the Newton side of the commutator** (source 4776-4791: `V_{μ,M}`, `W^mt = ε²V(ε·)`,
`𝒞_{χ_y}` with the outward primitive along the ray; 5383-5387: `Y^mt = 𝒞W^mt_μ +
[D_{μ+1},𝒞](W^mt_μ - W^mt_{μ+1})`; 4764-4775, 5141-5142, 5376: `Σ_M` of the swirl-free thin
tensor; SP 3753-3757: `V_{μ,0}`): for a swirl-free thin stress with finite `N`, at every young
receiver `ε⁻¹x_obs`, `|x_obs'|² ≥ ν`, `D_y mnYB = D_y[D_{μ+1},𝒞_y]X₀^mt(Ḡ)`, `Ḡ = meanSrc T`.
Proof sketch: on the open set `{5ν/6 < |x'|²}` (which contains the outward rays of the young
receivers), `youngW μ (thinRep T) = ε² Re V_{μ,0}(Ḡ)(ε·)` (the field form of
`TWBridge.NewtonBridge`: the kernel dictionary `∂_k(K₀)_{ij} = ∂_i∂_j∂_kN`, Fubini over `Y`,
the zero-width collapse `∫Ḡ dY = Sym Σ_M` with `ThinAziZero`); this field is axisymmetric
(`Σ_M` is rotation equivariant), so the ray primitive `streamPsi` equals the half-plane primitive
`outPrim` and `chiYr ν ε χ_y (r) = χ_y(ν age)`; `dmuFree` is `physDmu` of a phase-free field
(`vecLap` and `physLap` agree through `WithLp`). -/
def NewtonCommBridge : Prop :=
  ∀ (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ),
    LHyp (cOf L.ν) L.ν L.ε μ K.χo K.χy → 0 < K.C0 →
    ∀ T : LStr Pl K L, ThinAziZero Pl K L T → oldN1 Pl K L T ≠ ⊤ →
      ∀ (τ : ℝ) (xo : Space), L.ν ≤ xo 0 ^ 2 + xo 1 ^ 2 →
        fderiv ℝ (mnYB Pl K L μ T τ) (L.ε⁻¹ • xo) =
          fderiv ℝ (comm L.ν μ L.ε⁻¹ K.χy (newtonX0 L.ε μ (meanSrc Pl K L T)) τ) (L.ε⁻¹ • xo)

/-- **The regime form** of the reduction: one constant for every regime with `ε ≤ 1`. -/
theorem taylorWidthYBBoundAt_uniform (hA : SepCommMeanFar) (hB : NewtonCommBridge)
    (K : ReturnConsts) (hχy : IsStreamCutoff K.χy) :
    ∃ (C : ℝ) (k : ℕ), ∀ (Pl : PlanarData) (L : ReturnLevel) (μ : ℝ),
      L.ε ≤ 1 → 0 < K.C0 → 3 / 2 < K.mZ → TaylorWidthYBBoundAt Pl K L μ C k := by
  obtain ⟨C, k, hC, hlf⟩ := hA K.χy hχy
  refine ⟨Real.pi * (C + 1) * 3 ^ k, 2 * k, ?_⟩
  intro Pl L μ hε1 hC0 hmZ hL T hTz s hs η q
  have hν : 0 < L.ν := L.ν_pos
  have hε : 0 < L.ε := L.ε_pos
  have hc : 0 < cOf L.ν := cOf_pos hν
  have hs0 : 0 < s := hs.1
  set N := oldN1 Pl K L T with hN
  have hs52 : 0 < s ^ (5 / 2 : ℝ) := Real.rpow_pos_of_pos hs0 _
  have hcoef : 0 < Real.pi * (C + 1) * 3 ^ k * L.ν⁻¹ ^ (2 * k) * (L.ε ^ 4 * s ^ (5 / 2 : ℝ)) := by
    have := Real.pi_pos
    positivity
  by_cases hNtop : N = ⊤
  · rw [hNtop, ENNReal.mul_top (by simpa using hcoef)]
    exact le_top
  -- the receiver
  set y := NearInst.chartY L.ε⁻¹ (s, (q, η)) with hy
  set τ₀ := NearInst.chartTau L.ε⁻¹ (s, (q, η)) with hτ₀
  obtain ⟨hyx, hνx, hrad⟩ := receiver L.ν L.ε s q η hν hε hs
  rw [← hy] at hyx hνx hrad
  set xo := L.ε • y with hxo
  -- the Newton side
  have hBr := hB Pl K L μ hL hC0 T hTz hNtop τ₀ xo hνx
  rw [hyx] at hBr
  -- the leaf
  have hAl := hlf L.ν (cOf L.ν) L.ε μ hν hL.nu_le hc hε hε1 hL.mu_pos hL.mu_lt
    (meanSrc Pl K L T) (meanSrc_measurable Pl K L T) (meanSrc_support Pl K L T) τ₀ xo hνx
  rw [hyx, hrad] at hAl
  -- the heat side
  have hmid : actYBMid Pl K L μ T = comm L.ν μ L.ε⁻¹ K.χy
      (srcX0 L.ν μ (IIIa.thinSource L.ε (IIIa.meanLift (meanSrc Pl K L T)))) := by
    rw [actYBMid_eq_comm, zMid_eq_srcX0 Pl K L μ hC0 hmZ T]
  have hd : ENNReal.ofReal (dWidthYB Pl K L μ T τ₀ y) =
      ‖fderiv ℝ (comm L.ν μ L.ε⁻¹ K.χy
          (srcX0 L.ν μ (IIIa.thinSource L.ε (IIIa.meanLift (meanSrc Pl K L T)))) τ₀) y -
        fderiv ℝ (comm L.ν μ L.ε⁻¹ K.χy (newtonX0 L.ε μ (meanSrc Pl K L T)) τ₀) y‖ₑ := by
    unfold dWidthYB
    rw [hmid, hBr, ofReal_norm]
  -- the constants
  set M := 1 + L.ν⁻¹ + cOf L.ν with hM
  have hM0 : 0 ≤ M := by have := hc.le; have := inv_pos.2 hν; positivity
  have hMle : M ^ k ≤ 3 ^ k * L.ν⁻¹ ^ (2 * k) := by
    rw [pow_mul, ← mul_pow]
    exact pow_le_pow_left₀ hM0 (poly3 L.ν hν hL.nu_le) k
  set a := C * M ^ k * L.ε ^ 4 * s ^ (5 / 2 : ℝ) with ha
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have ha_le : a * Real.pi ≤ Real.pi * (C + 1) * 3 ^ k * L.ν⁻¹ ^ (2 * k) *
      (L.ε ^ 4 * s ^ (5 / 2 : ℝ)) := by
    have hpi := Real.pi_pos
    have h1 : C * M ^ k ≤ (C + 1) * (3 ^ k * L.ν⁻¹ ^ (2 * k)) :=
      mul_le_mul (by linarith) hMle (pow_nonneg hM0 _) (by linarith)
    have h2 : 0 ≤ L.ε ^ 4 * s ^ (5 / 2 : ℝ) := by positivity
    calc a * Real.pi = Real.pi * (C * M ^ k) * (L.ε ^ 4 * s ^ (5 / 2 : ℝ)) := by
          rw [ha]; ring
      _ ≤ Real.pi * ((C + 1) * (3 ^ k * L.ν⁻¹ ^ (2 * k))) * (L.ε ^ 4 * s ^ (5 / 2 : ℝ)) := by
          gcongr
      _ = _ := by ring
  rw [hd]
  calc _ ≤ ENNReal.ofReal a * IIIa.thinMoment (cOf L.ν) (IIIa.meanLift (meanSrc Pl K L T)) := hAl
    _ ≤ ENNReal.ofReal a * (ENNReal.ofReal Real.pi * N) := by
        gcongr
        exact thinMoment_meanSrc_le Pl K L hC0 T
    _ = ENNReal.ofReal (a * Real.pi) * N := by
        rw [ENNReal.ofReal_mul ha0, mul_assoc]
    _ ≤ _ := by gcongr

/-- **`D.TaylorWidthYBBound` from the two commutator leaves** (source 5427-5432, 5383-5387). -/
theorem taylorWidthYBBound_of (hA : SepCommMeanFar) (hB : NewtonCommBridge) (D : SeqData)
    {dm dp : ℝ} (hst : D.RepairStanding dm dp) : D.TaylorWidthYBBound := by
  obtain ⟨C, k, h⟩ := taylorWidthYBBoundAt_uniform hA hB D.K hst.chiY
  refine ⟨C, k, ?_⟩
  filter_upwards [retNu_retEps_eventually_le_one (σ₀ := D.σ₀) hst.omega_ne hst.gamma_pos
    D.coeff_ne] with n hνε z _
  exact h D.Pl (D.level n) (D.mu n z) hνε.2 hst.C0_pos hst.mZ_gt

end YBWidth

end UnforcedLeray.Short.PartIIIb.Concrete
