import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Defs
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.TensorTestDivMem
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Proofs.CompactWindow.Comparison.FlatStress.CellPtChangeAll

/-!
# Decomposition of `StressKernelRealization` (source 1548-1575, 1639-1689, 2681-2691, 3586-3626,
3893-3921)

Source of record: `the November 2 reference manuscript`.

`StressKernelRealization` (`NearInst/Masked/Lemmas.lean`): every real form `S` of a stress map `S'`
of `T_ε = (μ - A_ε)^{-1}P_ε` acts on box inputs by the unmasked kernel `fullOut ε⁻¹ c ν μ`.  The
source's route (3893-3895: "The finite-curvature free inverse is the conjugate of the Cartesian
weak-stress inverse"; 3621-3626 `sep:resolvent`; 1675 "The tensor map means completion from smooth
tensors"; 3916-3921 "exact kernel realization"):

1. `KernelFormulaSmooth` (3586-3626, `sep:resolvent`): on smooth Cartesian tensors `T`, the
   Cartesian weak-stress inverse `(μ - A)^{-1}P_3D div` (`CartStress`, of the outer field
   `T(τ, R x)`) is the kernel field `R · (-W_μ[T])(R x, τ)`, `W_μ = IIIa.sepW`.
2. `ChartConjSmooth` (3893-3906, 1639-1675, 2681-2691): for a smooth chart tensor test `m`,
   `T_ε (s div_ε m)` is the chart conjugate of the Cartesian weak-stress inverse of the tensor lift
   `𝒩_T m = s m` (`cartLift`): `J_ε T_ε(s div_ε m) = (2π)^{-1/2} CartStress(𝒩_T m)` with
   `J_ε = B0223.liftVec` (the velocity lift `𝒩_v b = √s b` up to the constant `(√(2π)ε)⁻¹`),
   `T_ε = J_ε†(μ - A)^{-1}J_ε P_ε` (`B0223.RepsVec = compress liftVec physRes`, `J_RepsVec`),
   `J_ε P_ε = P_3D J_ε` (`B0226.J_Peps`, `Peps_eq_starProjection`), and
   `J_ε(s div_ε m) = (2π)^{-1/2} div(𝒩_T m)` (the Cartesian differentiation of 1655-1665,
   including the hoop traction `-ε T_φφ`).  `𝒩_T m` is a smooth Cartesian tensor.
3. `DensityBox` (1675, 1688-1689, 3916-3921): a bounded `S' : H_T → H` acting on smooth tensor tests
   by the lifted kernel formula acts on box tensors by `fullOut` (the chart form
   `s^{-1/2} Re(-W_μ[𝒩_T f])_{r,z}` at `(chartY, chartTau)`, by axisymmetry of `W_μ` on
   axisymmetric no-swirl sources, then completion: box tensors are `H_T`-limits of smooth tests
   and the kernel is bounded `H_T → H` on box tensors, `‖∇K_t‖_{L¹} ≤ Ct^{-1/2}`, Young and
   normalized-phase Minkowski as in `FarKernelL2`).

`stressKernelRealization_of` assembles the target from the three Props, the recentring identities
`Delta.cellPtChangeAll` and `Masked.tensorTestDivMem`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Masked

/-! ## The three steps -/

/-- **`sep:resolvent` for smooth tensors** (source 3586-3626): for `ν, ε, c > 0`, `P = 2εc`,
`Re μ > -1/4` and a smooth `P`-periodic Cartesian tensor `T(τ, z)` with bounded spatial support
(`IsCartTest`; "We begin with smooth tensors", 3594), the Cartesian weak-stress inverse
`S_μ = D_μ^{-1}𝐏 div` (3587-3589; `CartStress = (μ - A)^{-1}P_3D div` of the outer field
`T(τ, R x)`, `R = ε⁻¹`, whose generator `A` is `-D_μ + μ` under `x = z/R`) equals
`-W_μ[T]`, `W_μ(y,τ) = -2∫_0^1 λ^{2μ+2}∫∇K_{ν(1-λ²)}(y - λz) : T(z, τ + 2 log λ) dz dλ`
(`IIIa.sepW`, 3622-3626), in the outer variables: the factor `R` is `∂_x = R ∂_z`
(`kernelField`).  Route (3613-3621): the Laplace integral of the semigroup
`e^{h/2}[e^{ν(e^h-1)Δ}f(τ-h)](e^{h/2}y)` with `λ = e^{-h/2}`; the heat-Leray kernel
`K_t = δG_t + ∂∂∫_t^∞G_a da` (3597-3601) of `e^{tΔ}𝐏`; integration of the divergence by parts. -/
def KernelFormulaSmooth : Prop :=
  ∀ (ν ε c P : ℝ) [Fact (0 < P)] (hν : 0 < ν), 0 < ε → 0 < c → ∀ (hP : P = 2 * ε * c)
    (μ : ℂ), -(1 / 4) < μ.re → ∀ T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ, IsCartTest P T →
    ∀ hM : MemLp (cartDiv (outerField ε⁻¹ T)) 2 (UnforcedLeray.B0220.physMeasure ε c),
      (CartStress hν hP μ (outerField ε⁻¹ T) hM :
          UnforcedLeray.B0223.PSpace P → UnforcedLeray.B0223.SpaceC) =ᵐ[volume]
        kernelField ν μ ε⁻¹ T

/-- **The chart conjugation on smooth tests** (source 3893-3906: "The finite-curvature free inverse
is the conjugate of the Cartesian weak-stress inverse ... its divergence and pressure are not
replaced by planar ones"; 1639-1675: chart `s = R²/ρ²`, `q = R log(ρ/R) + Rτ/2`, `η = Rz/ρ`,
`R = ε⁻¹`, `T_ε = (μ - A_ε)^{-1}P_ε` with `P_ε` the conjugated Cartesian Leray projection and the
divergence `div_ε` of 1661-1664; 2681-2691: lifts `𝒩_v b = √s b`, `𝒩_T T = sT`).  For a smooth
chart tensor test `m` (`PartIIa.IsTensorTest` of its components `tv4 ∘ m`):
* its tensor lift `𝒩_T m = cartLift ε⁻¹ c m` is a smooth Cartesian tensor (`IsCartTest`);
* the divergence of the outer field of `𝒩_T m` is in `L²(dx dτ)`, and for every representative
  `G` of `s div_ε m`,
  `J_ε T_ε G = (2π)^{-1/2} (μ - A)^{-1}P_3D div 𝒩_T m`, `J_ε = B0223.liftVec`
  (`B0223.RepsVec = compress liftVec physRes` and `J_RepsVec`; `B0226.J_Peps` with
  `PartIIa.PepsC` on real fields; `J_ε(s div_ε m) = (2π)^{-1/2} div 𝒩_T m`, the Cartesian
  differentiation of 1655-1665). -/
def ChartConjSmooth : Prop :=
  ∀ (ν ε c P : ℝ) [Fact (0 < P)] (hν : 0 < ν) (hε : 0 < ε) (hc : 0 < c) (hP : P = 2 * ε * c)
    (μ : ℂ), -(1 / 4) < μ.re → ∀ m : Chart → Ten3,
    UnforcedLeray.Short.PartIIa.IsTensorTest c (fun p => tv4 (m p)) →
    IsCartTest P (cartLift ε⁻¹ c m) ∧
    ∃ hM : MemLp (cartDiv (outerField ε⁻¹ (cartLift ε⁻¹ c m))) 2
        (UnforcedLeray.B0220.physMeasure ε c),
      ∀ G : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC,
        (G : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC)
            =ᵐ[UnforcedLeray.B0220.measureH c]
          (fun p => (p.1 : ℂ) • UnforcedLeray.Short.PartIIa.divEps ε (fun p => tv4 (m p)) p) →
        UnforcedLeray.B0223.liftVec hε hc hP
            (UnforcedLeray.Short.PartIIa.Teps hν hε hc hP μ G) =
          (((Real.sqrt (2 * Real.pi))⁻¹ : ℝ) : ℂ) •
            CartStress hν hP μ (outerField ε⁻¹ (cartLift ε⁻¹ c m)) hM

/-- **Completion from smooth tensors to box tensors** (source 1675: "The tensor map means
completion from smooth tensors"; 1688-1689 and 1572: bounded measurable partitions are allowed
before divergence; 3916-3921: the exact kernel realization; 2681-2691: the lifts).  For real
`μ > -1/4`, let `S' : H_T → H` be bounded and act on smooth chart tensor tests `m` by the lifted
kernel formula `J_ε S'm = (2π)^{-1/2}·R(-W_μ[𝒩_T m])(R x, τ)` (`kernelField`, the output of
`KernelFormulaSmooth` and `ChartConjSmooth`).  Then on every box tensor `f` (`IsBoxTensor`),
`S'f = s^{-1/2} Re(-W_μ[𝒩_T f])_{r,z}(chartY, chartTau)` (`fullOut`, transported to the cell
`(0, c]` by `cellPt`).  Route: (i) on tests, `J_ε` of the chart field `fullOut m` is the lifted
kernel field (`W_μ` of an axisymmetric no-swirl real source is rotation equivariant, without swirl
and real, and `P`-periodic in `τ`; the change of variables of `B0223.liftVec`), so `S'm = fullOut m`;
(ii) box tensors are `H_T`-limits of smooth tests (`Masked.TensorTestDense`, real parts), `S'` is
continuous, and `fullOut` is linear and bounded `H_T → H` on box tensors (Young and
normalized-phase Minkowski with `‖∇K_t‖_{L¹} ≤ C t^{-1/2}`, the `λ`-integral
`∫_0^1 λ^{2μ+1/2}(1-λ²)^{-1/2} dλ < ∞`, the lifts multiply both norms by `√πR`). -/
def DensityBox : Prop :=
  ∀ (ν ε c P : ℝ) [Fact (0 < P)], 0 < ν → ∀ (hε : 0 < ε) (hc : 0 < c) (hP : P = 2 * ε * c)
    (μ : ℝ), -(1 / 4) < μ →
    ∀ S' : UnforcedLeray.Short.PartIIa.HTSpace c →L[ℂ]
      UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC,
    (∀ m : Chart → Ten3, UnforcedLeray.Short.PartIIa.IsTensorTest c (fun p => tv4 (m p)) →
      ∀ F : UnforcedLeray.Short.PartIIa.HTSpace c,
        (F : UnforcedLeray.B0220.Profile → UnforcedLeray.Short.PartIIa.TensorVal)
            =ᵐ[UnforcedLeray.Short.PartIIa.measureHT c] (fun p => tv4 (m p)) →
        (UnforcedLeray.B0223.liftVec hε hc hP (S' F) :
            UnforcedLeray.B0223.PSpace P → UnforcedLeray.B0223.SpaceC) =ᵐ[volume]
          (((Real.sqrt (2 * Real.pi))⁻¹ : ℝ) : ℂ) •
            kernelField ν (μ : ℂ) ε⁻¹ (cartLift ε⁻¹ c m)) →
    ∀ f : Chart → Ten3, IsBoxTensor f → ∀ F' : UnforcedLeray.Short.PartIIa.HTSpace c,
      (F' : UnforcedLeray.B0220.Profile → UnforcedLeray.Short.PartIIa.TensorVal)
          =ᵐ[UnforcedLeray.Short.PartIIa.measureHT c] (fun p => tv4 (f (cellPt c p))) →
      (S' F' : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC)
          =ᵐ[UnforcedLeray.B0220.measureH c]
        fun p => merC (fullOut ε⁻¹ c ν μ f (cellPt c p))

/-! ## Auxiliary facts -/

/-- `cellPt ∘ cellPtInv = id` on the recentred cell `q ∈ [-c/2, c/2)`. -/
theorem skr_cellPt_cellPtInv {c : ℝ} {x : Chart} (hx : x.2.1 ∈ Ico (-c / 2) (c / 2)) :
    cellPt c (cellPtInv c x) = x := by
  obtain ⟨s, q, η⟩ := x
  simp only [mem_Ico] at hx
  obtain ⟨h1, h2⟩ := hx
  unfold cellPt cellPtInv
  by_cases hq : 0 < q
  · simp [hq, h2]
  · have hc' : ¬ (q + c < c / 2) := by linarith
    simp [hq, hc']

/-- A box tensor lies in `L²(s^{-1/2} ds dq/c dη)`. -/
theorem skr_memLp_box {c : ℝ} {f : Chart → Ten3} (hf : IsBoxTensor f) :
    MemLp f 2 (ageμ c (-1 / 2)) := by
  obtain ⟨B, hB⟩ := hf.bounded
  obtain ⟨s₁, s₂, L, hs₁, hband⟩ := hf.band
  set A : Set Chart := Icc s₁ s₂ ×ˢ ((univ : Set ℝ) ×ˢ Icc (-L) L) with hAdef
  have hA : MeasurableSet A := measurableSet_Icc.prod (MeasurableSet.univ.prod measurableSet_Icc)
  have hfA : A.indicator f = f := by
    funext p
    by_cases hp : p ∈ A
    · exact indicator_of_mem hp f
    · rw [indicator_of_notMem hp]
      by_contra h
      obtain ⟨h1, h2, h3⟩ := hband p (Ne.symm h)
      exact hp ⟨⟨h1, h2⟩, mem_univ _, abs_le.1 h3⟩
  have h1 : ((volume.restrict (Ioi (0 : ℝ))).withDensity
      fun s : ℝ => ENNReal.ofReal (s ^ (-1 / 2 : ℝ))) (Icc s₁ s₂) < ∞ := by
    rw [withDensity_apply _ measurableSet_Icc]
    refine lt_of_le_of_lt (setLIntegral_mono' measurableSet_Icc
      (g := fun _ => ENNReal.ofReal (s₁ ^ (-1 / 2 : ℝ))) fun s hs => ?_) ?_
    · exact ENNReal.ofReal_le_ofReal
        (Real.rpow_le_rpow_of_nonpos hs₁ hs.1 (by norm_num))
    · rw [setLIntegral_const]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        (lt_of_le_of_lt (Measure.restrict_apply_le _ _) measure_Icc_lt_top)
  have h2 : UnforcedLeray.Cyl.cellμ c ((univ : Set ℝ) ×ˢ Icc (-L) L) < ∞ := by
    unfold UnforcedLeray.Cyl.cellμ
    rw [Measure.restrict_apply (MeasurableSet.univ.prod measurableSet_Icc)]
    refine lt_of_le_of_lt (measure_mono ?_)
      ((isCompact_Icc (a := -c / 2) (b := c / 2)).prod
        (isCompact_Icc (a := -L) (b := L))).measure_lt_top
    rintro ⟨q, η⟩ ⟨⟨-, hη⟩, hq, -⟩
    exact ⟨⟨hq.1, hq.2.le⟩, hη⟩
  have hμA : ageμ c (-1 / 2) A ≠ ∞ := by
    rw [hAdef, ageμ, UnforcedLeray.Cyl.avgμ, Measure.prod_smul_right, Measure.smul_apply,
      smul_eq_mul, Measure.prod_prod]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_lt_top h1 h2).ne
  rw [← hfA, memLp_indicator_iff_restrict hA]
  have : IsFiniteMeasure ((ageμ c (-1 / 2)).restrict A) := isFiniteMeasure_restrict.2 hμA
  exact MemLp.of_bound hf.measurable.aestronglyMeasurable B (ae_of_all _ hB)

/-! ## The assembly -/

/-- **`StressKernelRealization` from the three steps.**  The lifted kernel formula on smooth tests
(`IsStressMap` with `tensorTestDivMem`, then `ChartConjSmooth` and `KernelFormulaSmooth`) feeds
`DensityBox`; the box input `tv4 ∘ f ∘ cellPt` represents `F₁ + F₂` (`CellPtHT`), `IsStressTransport`
identifies `S'` with `S` on it, and `CellPtInvH` returns to the recentred cell. -/
theorem stressKernelRealization_of (h1 : KernelFormulaSmooth) (h2 : ChartConjSmooth)
    (h3 : DensityBox) : StressKernelRealization := by
  intro ν ε c P _ hν hε hc hP μ hμ mZ ρb S' S hS' hST F f hf hFf
  obtain ⟨hHT, hInvH, -⟩ := UnforcedLeray.Short.PartIIIb.NearInst.Delta.cellPtChangeAll c hc
  have hμ' : -(1 / 4) < ((μ : ℂ)).re := by simpa using hμ
  -- the lifted kernel formula on smooth tensor tests
  have hyp : ∀ m : Chart → Ten3,
      UnforcedLeray.Short.PartIIa.IsTensorTest c (fun p => tv4 (m p)) →
      ∀ F₀ : UnforcedLeray.Short.PartIIa.HTSpace c,
        (F₀ : UnforcedLeray.B0220.Profile → UnforcedLeray.Short.PartIIa.TensorVal)
            =ᵐ[UnforcedLeray.Short.PartIIa.measureHT c] (fun p => tv4 (m p)) →
        (UnforcedLeray.B0223.liftVec hε hc hP (S' F₀) :
            UnforcedLeray.B0223.PSpace P → UnforcedLeray.B0223.SpaceC) =ᵐ[volume]
          (((Real.sqrt (2 * Real.pi))⁻¹ : ℝ) : ℂ) •
            kernelField ν (μ : ℂ) ε⁻¹ (cartLift ε⁻¹ c m) := by
    intro m hm F₀ hF₀
    obtain ⟨hcart, hM, hconj⟩ := h2 ν ε c P hν hε hc hP (μ : ℂ) hμ' m hm
    have hG := tensorTestDivMem c ε hc _ hm
    rw [hS' _ hm F₀ (hG.toLp _) hF₀ hG.coeFn_toLp, hconj _ hG.coeFn_toLp]
    filter_upwards [Lp.coeFn_smul ((((Real.sqrt (2 * Real.pi))⁻¹ : ℝ) : ℂ))
        (CartStress hν hP (μ : ℂ) (outerField ε⁻¹ (cartLift ε⁻¹ c m)) hM),
      h1 ν ε c P hν hε hc hP (μ : ℂ) hμ' _ hcart hM] with w hw1 hw2
    rw [hw1, Pi.smul_apply, Pi.smul_apply, hw2]
  -- the box tensor as an element of `H_T`
  have hfT : MemLp (fun p => tv4 (f (cellPt c p))) 2
      (UnforcedLeray.Short.PartIIa.measureHT c) := by
    have hm1 : MemLp (fun x => tv4L (f x)) 2 (ageμ c (-1 / 2)) :=
      tv4L.comp_memLp' (skr_memLp_box hf)
    have hm2 : MemLp (fun x => tv4L (f x)) 2
        (Measure.map (cellPt c) (UnforcedLeray.Short.PartIIa.measureHT c)) := by
      rw [hHT]
      exact hm1.smul_measure ENNReal.ofReal_ne_top
    exact (memLp_map_measure_iff hm2.1 (measurable_cellPt c).aemeasurable).1 hm2
  -- `F₁ + F₂ = f` on the cell `(0, c]`
  have hzf : ∀ᵐ p ∂UnforcedLeray.Short.PartIIa.measureHT c,
      zsum F (cellPt c p) = f (cellPt c p) := by
    have h0 : ∀ᵐ x ∂Measure.map (cellPt c) (UnforcedLeray.Short.PartIIa.measureHT c),
        zsum F x = f x := by
      rw [hHT]
      exact Measure.smul_absolutelyContinuous.ae_le hFf
    exact ae_of_ae_map (measurable_cellPt c).aemeasurable h0
  have hF'f := hfT.coeFn_toLp
  have hF'z : (hfT.toLp _ : UnforcedLeray.B0220.Profile → UnforcedLeray.Short.PartIIa.TensorVal)
      =ᵐ[UnforcedLeray.Short.PartIIa.measureHT c] fun p => tv4 (zsum F (cellPt c p)) := by
    filter_upwards [hF'f, hzf] with p hp1 hp2
    rw [hp1, hp2]
  have htr := hST F _ hF'z
  have hden := h3 ν ε c P hν hε hc hP μ hμ S' hyp f hf _ hF'f
  have hprof : ∀ᵐ p ∂UnforcedLeray.B0220.measureH c,
      (S F : Chart → Merid) (cellPt c p) = fullOut ε⁻¹ c ν μ f (cellPt c p) := by
    filter_upwards [htr, hden] with p hp1 hp2
    have h := congrArg merReL (hp1.symm.trans hp2)
    rwa [merReL_merC, merReL_merC] at h
  -- back to the recentred cell
  have h4 : ∀ᵐ x ∂Measure.map (cellPtInv c) (ageμ c (-3 / 2)),
      (S F : Chart → Merid) (cellPt c x) = fullOut ε⁻¹ c ν μ f (cellPt c x) := by
    rw [hInvH]
    exact Measure.smul_absolutelyContinuous.ae_le hprof
  have h5 := ae_of_ae_map (measurable_cellPtInv c).aemeasurable h4
  filter_upwards [h5, ae_ageμ_mem hc (-3 / 2)] with x hx hmem
  rwa [skr_cellPt_cellPtInv hmem.2.1] at hx

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization
