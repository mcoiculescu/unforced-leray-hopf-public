import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Sub.PartIIIb_C_near_delta_8_2_3
import UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst.Column
import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.PairFunctional.ChartTransport
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.TensorTestDivMem
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Lin
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.CausalLimitAE
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NullModification

/-!
# Decomposition of `FlatStressFree` (item `PartIII-b:C/near/delta/8/2/3/4`)

Source of record `the November 2 reference manuscript`:
1650-1656 (`A₀ = -S + νsΔ`, `T₀ = (μ - A₀)⁻¹P₀`, `S₀ = T₀ s div₀`), 1660-1665 (`div₀`),
1675-1679 ("the tensor map means completion from smooth tensors"), 1684-1689 (the flat equation
`(∂_s + μ/s - νΔ)b = P₀div₀M`; "pairing it with `s^{-1/2}b̄` gives the coercive constant
`Re μ + 1/4` and proves its completion"), 3420-3440 (the causal zero-entrance energy class),
3541-3552 (energy identity on `[δ_j, B]`), 3561-3571 (the flat maps act on the meridional block).

`FlatStressFree` (`Sub/PartIII-b_C_near_delta_8_2_3.lean`): the real form of a real stress map
`S'` of `T₀ = R₀P₀` satisfies `IsFreeStress`.  The proof, done here from six leaves:

1. *Smooth tests* (`BodyColumnTransport`, `TensorDivIBP`).  For a real smooth tensor test `M`,
   `S'M = T₀(s div₀M)` is the free body column of `PartIII-b:C/flatset/col/7` (`BodyColumnFlat`)
   with body force `div₀M`; integrating `div₀M · Φ` by parts in `(q, η)` turns it into a causal
   zero-entrance energy solution with tensor force the planar block of `M`
   (`smoothStressColumn_of`).
2. *Energy bound* (`FreeEnergyFlatSq`; square roots in `freeEnergyFlat_of`).  Every causal
   zero-entrance energy solution of the free equation obeys `‖b‖_𝓗 ≤ (2√((Re μ + 1/4)ν))⁻¹‖F‖_𝒯`,
   `‖∇b‖_𝒯 ≤ ν⁻¹‖F‖_𝒯` (the pairing with `s^{-1/2}b̄`, no gain).
3. *Passage to the limit* (`stressColumnAll_of`, proved here).  Real tests `M_n → F` in `H_T`
   (`RealTensorTestApprox`); by linearity (`IIIa.causalSolSub`) and step 2 the columns are Cauchy;
   `IIIa.causalLimitAE` and `IIIa.causalNullModification` give a causal energy solution with force
   the block of `F`; step 2 applied to the differences identifies it with `S'F`.  The transports
   between the `PartII-a` cell `(0, c]` and the recentred chart are bounded (`BlkNormLe`,
   `VelNormLe`).
4. *Real form* (`flatStressFree_of`, proved here): `velC (realForm S' F) = S'F'` (`S'` real) and the
   block of `F' = tv4 ∘ (F₁ + F₂) ∘ cellPt` is `merBlockC (F₁ + F₂)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Delta

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIa
open UnforcedLeray.B0220 (Profile HSpace measureH)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.Short.IIIa (IsCausalEnergySolution flatIntegrand IsFlatTest flatGrad vnorm2
  tnorm2 hCalNorm tCalNorm gainConj gainG)

/-! ## Transports to the recentred chart -/

/-- The planar block `[[T_rr, T_rz], [T_rz, T_zz]]` of a tensor value `(T_rr, T_rz, T_zz, T_φφ)`
(source 1660-1665 at `ε = 0`: `div₀` sees only this block; 3569-3571). -/
def tvBlk (v : TensorVal) : Fin 2 → Fin 2 → ℂ :=
  ![![v 0, v 1], ![v 1, v 2]]

/-- A tensor field on the `PartII-a` cell `q ∈ (0, c]` as the tensor force of the flat equation on
the recentred chart `q ∈ [-c/2, c/2)`: `x ↦ tvBlk (m (cellPtInv c x))`. -/
def tblkF (c : ℝ) (m : Profile → TensorVal) : Chart → Fin 2 → Fin 2 → ℂ :=
  fun x i j => tvBlk (m (Masked.cellPtInv c x)) i j

/-- A meridional field on the `PartII-a` cell as a velocity on the recentred chart. -/
def velF (c : ℝ) (g : Profile → MeridC) : Chart → Fin 2 → ℂ :=
  fun x i => g (Masked.cellPtInv c x) i

/-! ## The six leaves -/

/-- **(1) The smooth stress column is the free body column** (source 1650-1656, 1675-1679,
1684-1689; the body version is `FlatSettingInst.BodyColumnFlat`, task `PartIII-b:C/flatset/col/7`).
For a real smooth tensor test `M` and a representative `G` of `s div₀M`, `T₀G` (transported to the
recentred chart) has a representative that is a zero-entrance forced column of the free equation
`∂_sb + (μ/s)b - νΔb = P₀ div₀M` (body force `div₀M`; `M` is `c`-periodic, so no recentring of the
force is needed). -/
def BodyColumnTransport : Prop :=
  ∀ (c ν μ : ℝ) (hc : 0 < c), 0 < ν → 0 < μ + 1 / 4 →
    ∀ M : Profile → TensorVal, IsTensorTest c M → (∀ p k, (M p k).im = 0) →
    ∀ G : HSpace c MeridC,
      (G : Profile → MeridC) =ᵐ[measureH c] (fun p => (p.1 : ℂ) • divEps 0 M p) →
      ∃ (b : Chart → Fin 2 → ℂ) (Gr : Chart → Fin 2 → Fin 2 → ℂ),
        b =ᵐ[ageμ c (-3 / 2)] velF c (T0flat hc ν (μ : ℂ) G) ∧
          FlatSettingInst.IsForcedColumn c ν (μ : ℂ) (fun _ _ _ => 0)
            (fun x i => divEps 0 M x i) b Gr

/-- **(2) Integration by parts of `div₀M` against a flat test** (source 1660-1665, 3420-3424):
`∫∫ [Σ_i (div₀M)_i Φ_i + Σ_{ij} M_ij ∂_jΦ_i] = 0` over `(0,∞) × cell`, the integrand being a
divergence `Σ_{ij} ∂_j(M_ij Φ_i)` (`c`-periodic in `q`, compactly supported in `η`). -/
def TensorDivIBP : Prop :=
  ∀ c : ℝ, 0 < c → ∀ M : Profile → TensorVal, IsTensorTest c M → ∀ Φ, IsFlatTest c Φ →
    IntegrableOn (fun p : Chart => ∑ i : Fin 2, (divEps 0 M p i * (Φ p.1 p.2 i : ℂ) +
        ∑ j : Fin 2, tvBlk (M p) i j * (flatGrad Φ p.1 p.2 i j : ℂ)))
      (Ioi (0 : ℝ) ×ˢ B0579.cell c) ∧
    ∫ p in Ioi (0 : ℝ) ×ˢ B0579.cell c, ∑ i : Fin 2, (divEps 0 M p i * (Φ p.1 p.2 i : ℂ) +
        ∑ j : Fin 2, tvBlk (M p) i j * (flatGrad Φ p.1 p.2 i j : ℂ)) = 0

/-- **(3) The squared free energy inequalities without gain** (source 1686-1689: "pairing it with
`s^{-1/2}b̄` gives the coercive constant `Re μ + 1/4`"; 3541-3552: the energy identity on
`[δ_j, B]`, `δ_j^{-1/2}‖u(δ_j)‖² → 0`).  With `k = Re μ + 1/4 > 0`, every causal zero-entrance
energy solution of the free equation with measurable `F ∈ 𝒯` satisfies
`2k‖b‖²_𝓗 + ν‖G‖²_𝒯 ≤ ν⁻¹‖F‖²_𝒯` and `2k‖b‖²_𝓗 ≤ (2ν)⁻¹‖F‖²_𝒯`.  This is the `γ = 0`, single-`μ`
case of `IIIa.FreeEnergyInequalities` (`Sub/T18_3.lean`), from `IIIa.WeightedEnergyIdentity` at
`γ = 0` (where `gainConj 0 ν = id`) by the same cutoff argument. -/
def FreeEnergyFlatSq : Prop :=
  ∀ (c ν : ℝ) (μ : ℂ), 0 < c → 0 < ν → 0 < μ.re + 1 / 4 →
    ∀ F : Chart → Fin 2 → Fin 2 → ℂ, (∀ i j, Measurable fun p => F p i j) → tCalNorm c F < ⊤ →
    ∀ (b : Chart → Fin 2 → ℂ) (G : Chart → Fin 2 → Fin 2 → ℂ),
      IsCausalEnergySolution c ν μ (fun _ _ _ => 0) F b G →
        (ENNReal.ofReal (2 * (μ.re + 1 / 4)) * hCalNorm c b ^ 2 +
            ENNReal.ofReal ν * tCalNorm c G ^ 2 ≤ ENNReal.ofReal ν⁻¹ * tCalNorm c F ^ 2) ∧
          ENNReal.ofReal (2 * (μ.re + 1 / 4)) * hCalNorm c b ^ 2 ≤
            ENNReal.ofReal (2 * ν)⁻¹ * tCalNorm c F ^ 2

/-- **(4) Real smooth tensor tests are dense among real tensors** (source 1678, completion from
smooth tensors; `Masked.tensorTestDense` and the real-part replacement of `genericStressReal`). -/
def RealTensorTestApprox : Prop :=
  ∀ c : ℝ, 0 < c → ∀ F : HTSpace c, Masked.IsRealHT c F →
    ∃ (M : ℕ → Profile → TensorVal) (hM : ∀ n, MemLp (M n) 2 (measureHT c)),
      (∀ n, IsTensorTest c (M n)) ∧ (∀ n p k, (M n p k).im = 0) ∧
        Tendsto (fun n => ‖(hM n).toLp (M n) - F‖) atTop (𝓝 0)

/-- **(5) The tensor transport is bounded** (source 1641-1646, 2676-2679: `dq` versus `dq/c`):
`‖tblkF c m‖_𝒯 ≤ C ‖m‖_{H_T}`. -/
def BlkNormLe : Prop :=
  ∀ c : ℝ, 0 < c → Masked.CellPtHT c → ∃ C : ℝ, 0 ≤ C ∧
    ∀ m : Profile → TensorVal, AEStronglyMeasurable m (measureHT c) →
      tCalNorm c (tblkF c m) ≤ ENNReal.ofReal C * eLpNorm m 2 (measureHT c)

/-- **(6) The velocity transport is bounded** (source 1641-1646, 2676-2679):
`‖velF c g‖_𝓗 ≤ C ‖g‖_H`. -/
def VelNormLe : Prop :=
  ∀ c : ℝ, 0 < c → Masked.CellPtInvH c → ∃ C : ℝ, 0 ≤ C ∧
    ∀ g : Profile → MeridC, AEStronglyMeasurable g (measureH c) →
      hCalNorm c (velF c g) ≤ ENNReal.ofReal C * eLpNorm g 2 (measureH c)

/-! ## Intermediate statements -/

/-- The free energy bound without gain (source 1686-1689, 3541-3552): every causal zero-entrance
energy solution of the free equation with `F ∈ 𝒯` satisfies `‖b‖_𝓗 ≤ (2√((Re μ + 1/4)ν))⁻¹‖F‖_𝒯`
and `‖G‖_𝒯 ≤ ν⁻¹‖F‖_𝒯` (square roots of `FreeEnergyFlatSq`). -/
def FreeEnergyFlat : Prop :=
  ∀ (c ν : ℝ) (μ : ℂ), 0 < c → 0 < ν → 0 < μ.re + 1 / 4 →
    ∀ F : Chart → Fin 2 → Fin 2 → ℂ, (∀ i j, Measurable fun p => F p i j) → tCalNorm c F < ⊤ →
    ∀ (b : Chart → Fin 2 → ℂ) (G : Chart → Fin 2 → Fin 2 → ℂ),
      IsCausalEnergySolution c ν μ (fun _ _ _ => 0) F b G →
        hCalNorm c b ≤ ENNReal.ofReal ((2 * Real.sqrt ((μ.re + 1 / 4) * ν))⁻¹) * tCalNorm c F ∧
          tCalNorm c G ≤ ENNReal.ofReal ν⁻¹ * tCalNorm c F

/-- The smooth stress column in the causal class (source 1684-1689). -/
def SmoothStressColumn : Prop :=
  ∀ (c ν μ : ℝ) (hc : 0 < c), 0 < ν → 0 < μ + 1 / 4 →
    ∀ M : Profile → TensorVal, IsTensorTest c M → (∀ p k, (M p k).im = 0) →
    ∀ G : HSpace c MeridC,
      (G : Profile → MeridC) =ᵐ[measureH c] (fun p => (p.1 : ℂ) • divEps 0 M p) →
      ∃ (b : Chart → Fin 2 → ℂ) (Gr : Chart → Fin 2 → Fin 2 → ℂ),
        b =ᵐ[ageμ c (-3 / 2)] velF c (T0flat hc ν (μ : ℂ) G) ∧
          IsCausalEnergySolution c ν (μ : ℂ) (fun _ _ _ => 0) (tblkF c M) b Gr

/-- Every real tensor: `S'F` is the causal zero-entrance energy solution with force the planar block
of `F` (source 1675-1689, 3420-3440). -/
def StressColumnAll : Prop :=
  ∀ (c ν μ : ℝ) (hc : 0 < c), 0 < ν → 0 < μ + 1 / 4 → Masked.CellPtHT c → Masked.CellPtInvH c →
    ∀ S' : HTSpace c →L[ℂ] HSpace c MeridC, IsStressMap c 0 (T0flat hc ν (μ : ℂ)) S' →
    ∀ F : HTSpace c, Masked.IsRealHT c F →
      ∃ (b : Chart → Fin 2 → ℂ) (G : Chart → Fin 2 → Fin 2 → ℂ),
        b =ᵐ[ageμ c (-3 / 2)] velF c (S' F) ∧
          IsCausalEnergySolution c ν (μ : ℂ) (fun _ _ _ => 0) (tblkF c F) b G

/-! ## Elementary facts -/

theorem fsf_cellPtInv_periodic {E : Type*} {c : ℝ} {M : Profile → E}
    (hM : UnforcedLeray.B0220.QPeriodic c M) (x : Chart) : M (Masked.cellPtInv c x) = M x := by
  obtain ⟨s, q, η⟩ := x
  show M (s, (if 0 < q then q else q + c, η)) = M (s, q, η)
  split_ifs with hq
  · rfl
  · exact hM (s, q, η)

theorem fsf_tvBlk_tv4 (T : Ten3) (i j : Fin 2) :
    tvBlk (tv4 T) i j = ((nsSym T (merIdx i) (merIdx j) : ℝ) : ℂ) := by
  fin_cases i <;> fin_cases j <;> simp [tvBlk, tv4, nsSym, merIdx]

theorem fsf_tblkF_sub (c : ℝ) (m m' : Profile → TensorVal) :
    (fun x i j => tblkF c m x i j - tblkF c m' x i j) = tblkF c (fun p => m p - m' p) := by
  funext x i j
  simp only [tblkF]
  fin_cases i <;> fin_cases j <;> simp [tvBlk, PiLp.sub_apply]

theorem fsf_measurable_tblkF {c : ℝ} {m : Profile → TensorVal} (hm : Measurable m)
    (i j : Fin 2) : Measurable fun x => tblkF c m x i j := by
  have hk : ∀ k : Fin 4, Measurable fun x => m (Masked.cellPtInv c x) k := fun k =>
    ((PiLp.continuous_apply (p := 2) (β := fun _ : Fin 4 => ℂ) k).measurable).comp
      (hm.comp (Masked.measurable_cellPtInv c))
  simp only [tblkF]
  fin_cases i <;> fin_cases j
  · simpa [tvBlk] using hk 0
  · simpa [tvBlk] using hk 1
  · simpa [tvBlk] using hk 1
  · simpa [tvBlk] using hk 2

theorem fsf_measurable_velF {c : ℝ} {g : Profile → MeridC} (hg : Measurable g) (i : Fin 2) :
    Measurable fun x => velF c g x i :=
  ((PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 => ℂ) i).measurable).comp
    (hg.comp (Masked.measurable_cellPtInv c))

theorem fsf_gainConj_zero {E : Type*} [AddCommGroup E] [Module ℝ E] (ν : ℝ) (f : Chart → E) :
    gainConj 0 ν f = f := by
  funext p
  simp [gainConj, gainG]

theorem fsf_ageμ_ac (c a b : ℝ) : ageμ c a ≪ ageμ c b := by
  have h1 : ((volume : Measure ℝ).restrict (Ioi (0 : ℝ))).withDensity
        (fun s => ENNReal.ofReal (s ^ a)) ≪
      ((volume : Measure ℝ).restrict (Ioi (0 : ℝ))).withDensity
        (fun s => ENNReal.ofReal (s ^ b)) := by
    refine (withDensity_absolutelyContinuous _ _).trans ?_
    refine withDensity_absolutelyContinuous' (measurable_ofReal_rpow b).aemeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hs _)).ne'
  have : SFinite (UnforcedLeray.Cyl.avgμ c) := by
    unfold UnforcedLeray.Cyl.avgμ
    infer_instance
  unfold ageμ
  exact h1.prod Measure.AbsolutelyContinuous.rfl

theorem fsf_measureH_ac_measureHT (c : ℝ) : measureH c ≪ measureHT c := by
  have hcell : MeasurableSet (UnforcedLeray.B0220.cell c) :=
    measurableSet_Ioi.prod (measurableSet_Ioc.prod MeasurableSet.univ)
  unfold UnforcedLeray.B0220.measureH measureHT
  refine (withDensity_absolutelyContinuous _ _).trans ?_
  refine withDensity_absolutelyContinuous' ?_ ?_
  · exact (ENNReal.measurable_ofReal.comp (measurable_fst.pow_const _)).aemeasurable
  · unfold UnforcedLeray.B0220.cellMeasure
    filter_upwards [ae_restrict_mem hcell] with p hp
    exact (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hp.1 _)).ne'

/-- The causal class depends only on the a.e. class of the force. -/
theorem fsf_congr_F {c ν : ℝ} {μ : ℂ} {vel : ℝ → ℝ × ℝ → Fin 2 → ℝ}
    {F F' : Chart → Fin 2 → Fin 2 → ℂ} {b : Chart → Fin 2 → ℂ} {G : Chart → Fin 2 → Fin 2 → ℂ}
    (h : IsCausalEnergySolution c ν μ vel F b G)
    (hF : F =ᵐ[(volume : Measure Chart).restrict (Ioi (0 : ℝ) ×ˢ B0579.cell c)] F') :
    IsCausalEnergySolution c ν μ vel F' b G := by
  have key : ∀ Φ, flatIntegrand ν μ vel F b Φ =ᵐ[(volume : Measure Chart).restrict
      (Ioi (0 : ℝ) ×ˢ B0579.cell c)] flatIntegrand ν μ vel F' b Φ := by
    intro Φ
    filter_upwards [hF] with p hp
    unfold flatIntegrand
    rw [hp]
  exact
    { measurable := h.measurable
      gradMeasurable := h.gradMeasurable
      energyLoc := h.energyLoc
      zeroEntrance := h.zeroEntrance
      divFree := h.divFree
      weakGrad := h.weakGrad
      integrable := fun Φ hΦ => (h.integrable Φ hΦ).congr (key Φ)
      weak := fun Φ hΦ => by rw [← integral_congr_ae (key Φ)]; exact h.weak Φ hΦ }

/-! ## The `𝓗` norm -/

theorem fsf_vnorm2_eq_norm (v : Fin 2 → ℂ) :
    vnorm2 v = ‖(WithLp.toLp 2 v : EuclideanSpace ℂ (Fin 2))‖ := by
  unfold vnorm2
  rw [EuclideanSpace.norm_eq]

theorem fsf_vnorm2_nonneg (v : Fin 2 → ℂ) : 0 ≤ vnorm2 v := Real.sqrt_nonneg _

theorem fsf_vnorm2_sub_le (a b d : Fin 2 → ℂ) :
    vnorm2 (fun i => a i - d i) ≤ vnorm2 (fun i => a i - b i) + vnorm2 (fun i => b i - d i) := by
  rw [fsf_vnorm2_eq_norm, fsf_vnorm2_eq_norm, fsf_vnorm2_eq_norm]
  have h : (WithLp.toLp 2 (fun i => a i - d i) : EuclideanSpace ℂ (Fin 2)) =
      WithLp.toLp 2 (fun i => a i - b i) + WithLp.toLp 2 (fun i => b i - d i) := by
    ext i
    simp only [PiLp.add_apply]
    ring
  rw [h]
  exact norm_add_le _ _

theorem fsf_hCal_congr {c : ℝ} {x y : Chart → Fin 2 → ℂ} (h : x =ᵐ[ageμ c (-3 / 2)] y) :
    hCalNorm c x = hCalNorm c y := by
  unfold hCalNorm
  exact eLpNorm_congr_ae (h.mono fun p hp => by simp only [hp])

theorem fsf_hCal_sub_comm (c : ℝ) (x y : Chart → Fin 2 → ℂ) :
    hCalNorm c (fun p i => x p i - y p i) = hCalNorm c (fun p i => y p i - x p i) := by
  unfold hCalNorm
  congr 1
  funext p
  rw [fsf_vnorm2_eq_norm, fsf_vnorm2_eq_norm,
    ← norm_neg (WithLp.toLp 2 (fun i => y p i - x p i) : EuclideanSpace ℂ (Fin 2))]
  congr 1
  ext i
  simp

theorem fsf_hCal_tri (c : ℝ) {x y z : Chart → Fin 2 → ℂ} (hx : ∀ i, Measurable fun p => x p i)
    (hy : ∀ i, Measurable fun p => y p i) (hz : ∀ i, Measurable fun p => z p i) :
    hCalNorm c (fun p i => x p i - z p i) ≤
      hCalNorm c (fun p i => x p i - y p i) + hCalNorm c (fun p i => y p i - z p i) := by
  unfold hCalNorm
  have hm1 : Measurable fun p => vnorm2 (fun i => x p i - y p i) :=
    IIIa.causalLin_measurable_vnorm2 (f := fun p i => x p i - y p i) (fun i => (hx i).sub (hy i))
  have hm2 : Measurable fun p => vnorm2 (fun i => y p i - z p i) :=
    IIIa.causalLin_measurable_vnorm2 (f := fun p i => y p i - z p i) (fun i => (hy i).sub (hz i))
  calc eLpNorm (fun p => vnorm2 (fun i => x p i - z p i)) 2 (ageμ c (-3 / 2))
      ≤ eLpNorm (fun p => vnorm2 (fun i => x p i - y p i) + vnorm2 (fun i => y p i - z p i)) 2
          (ageμ c (-3 / 2)) := by
        refine eLpNorm_mono fun p => ?_
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (fsf_vnorm2_nonneg _),
          abs_of_nonneg (add_nonneg (fsf_vnorm2_nonneg _) (fsf_vnorm2_nonneg _))]
        exact fsf_vnorm2_sub_le _ _ _
    _ ≤ _ := eLpNorm_add_le hm1.aestronglyMeasurable hm2.aestronglyMeasurable one_le_two

theorem fsf_ae_eq_of_hCal_zero {c : ℝ} {x y : Chart → Fin 2 → ℂ}
    (hx : ∀ i, Measurable fun p => x p i) (hy : ∀ i, Measurable fun p => y p i)
    (h : hCalNorm c (fun p i => x p i - y p i) = 0) : x =ᵐ[ageμ c (-3 / 2)] y := by
  unfold hCalNorm at h
  have hm : Measurable fun p => vnorm2 (fun i => x p i - y p i) :=
    IIIa.causalLin_measurable_vnorm2 (f := fun p i => x p i - y p i) (fun i => (hx i).sub (hy i))
  have h0 := (eLpNorm_eq_zero_iff hm.aestronglyMeasurable two_ne_zero).1 h
  filter_upwards [h0] with p hp
  have hp' : vnorm2 (fun i => x p i - y p i) = 0 := hp
  rw [fsf_vnorm2_eq_norm, norm_eq_zero] at hp'
  funext i
  have := congrArg (fun v : EuclideanSpace ℂ (Fin 2) => v i) hp'
  simpa [sub_eq_zero] using this

/-! ## Transports of a.e. identities -/

theorem fsf_velF_sub_ae {c : ℝ} (hc : 0 < c) (g₁ g₂ : HSpace c MeridC) :
    velF c (g₁ - g₂ : HSpace c MeridC) =ᵐ[ageμ c (-3 / 2)]
      fun x i => velF c g₁ x i - velF c g₂ x i := by
  have hsub : ∀ᵐ q ∂measureH c, ((g₁ - g₂ : HSpace c MeridC) : Profile → MeridC) q =
      (g₁ : Profile → MeridC) q - (g₂ : Profile → MeridC) q := by
    filter_upwards [Lp.coeFn_sub g₁ g₂] with q hq
    rw [hq, Pi.sub_apply]
  have hK := ct_ae_transfer hc (fun q => ((g₁ - g₂ : HSpace c MeridC) : Profile → MeridC) q =
    (g₁ : Profile → MeridC) q - (g₂ : Profile → MeridC) q) hsub
  filter_upwards [hK] with x hx
  funext i
  simp only [velF, hx, PiLp.sub_apply]

theorem fsf_velC_reH_ae {c : ℝ} (hc : 0 < c) (hH : Masked.CellPtInvH c) (g : HSpace c MeridC)
    (hg : Masked.IsRealH c g) :
    velC (Masked.reH c hH g) =ᵐ[ageμ c (-3 / 2)] velF c g := by
  have hK := ct_ae_transfer hc (fun q => ∀ i, ((g : Profile → MeridC) q i).im = 0) hg
  filter_upwards [Masked.reH_ae c hH g, hK] with x h1 h2
  funext i
  simp only [velC, velF, h1, Masked.merReL_apply]
  exact Complex.ext (by simp) (by simp [h2 i])

theorem fsf_tblkF_cplxT_ae {c mZ ρb : ℝ} (hc : 0 < c) (hmZ : 0 ≤ mZ) (hρ : 0 < ρb)
    (hT : Masked.CellPtHT c) (F : Zsp c mZ ρb) :
    tblkF c (Masked.cplxT c hT (Masked.zsumL c mZ ρb hmZ hρ F) : Profile → TensorVal)
      =ᵐ[ageμ c (-3 / 2)] merBlockC (zsum F) := by
  have h1 : ∀ᵐ q ∂measureH c,
      (Masked.cplxT c hT (Masked.zsumL c mZ ρb hmZ hρ F) : Profile → TensorVal) q =
        tv4 ((Masked.zsumL c mZ ρb hmZ hρ F : Chart → Ten3) (cellPt c q)) := by
    filter_upwards [(fsf_measureH_ac_measureHT c).ae_le
      (Masked.cplxT_ae c hT (Masked.zsumL c mZ ρb hmZ hρ F))] with q hq
    exact hq
  have h2 := ct_ae_transfer hc (fun q =>
    (Masked.cplxT c hT (Masked.zsumL c mZ ρb hmZ hρ F) : Profile → TensorVal) q =
      tv4 ((Masked.zsumL c mZ ρb hmZ hρ F : Chart → Ten3) (cellPt c q))) h1
  have h3 := (fsf_ageμ_ac c (-3 / 2) (-1 / 2)).ae_le (Masked.zsumL_ae c mZ ρb hmZ hρ F)
  filter_upwards [h2, ct_cellPt_cellPtInv c hc, h3] with x hx2 hx3 hx4
  funext i j
  simp only [tblkF]
  rw [hx2, hx3, hx4]
  exact fsf_tvBlk_tv4 _ i j

/-! ## Step 2: the energy bound -/

theorem fsf_le_of_sq_le_sq {x y : ℝ≥0∞} (h : x ^ 2 ≤ y ^ 2) : x ≤ y :=
  (ENNReal.pow_le_pow_left_iff two_ne_zero).1 h

/-- **Square roots of the energy inequalities** (the arithmetic of `IIIa.freeCausalEnergyBound_of`
with `k = Re μ + 1/4`). -/
theorem freeEnergyFlat_of (hI : FreeEnergyFlatSq) : FreeEnergyFlat := by
  intro c ν μ hc hν hk F hm hF b G hsol
  obtain ⟨I1, I2⟩ := hI c ν μ hc hν hk F hm hF b G hsol
  set k : ℝ := μ.re + 1 / 4 with hkdef
  set a := hCalNorm c b with ha
  set g := tCalNorm c G with hg
  set f := tCalNorm c F with hf
  constructor
  · apply fsf_le_of_sq_le_sq
    have h2 : a ^ 2 ≤ ENNReal.ofReal (2 * k)⁻¹ * (ENNReal.ofReal (2 * ν)⁻¹ * f ^ 2) := by
      calc a ^ 2 = ENNReal.ofReal (2 * k)⁻¹ * (ENNReal.ofReal (2 * k) * a ^ 2) := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
              inv_mul_cancel₀ (by positivity), ENNReal.ofReal_one, one_mul]
        _ ≤ _ := by gcongr
    have h3 : ENNReal.ofReal (2 * k)⁻¹ * (ENNReal.ofReal (2 * ν)⁻¹ * f ^ 2) =
        (ENNReal.ofReal ((2 * Real.sqrt (k * ν))⁻¹) * f) ^ 2 := by
      rw [mul_pow, ← ENNReal.ofReal_pow (by positivity), ← mul_assoc,
        ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      have hs : Real.sqrt (k * ν) ^ 2 = k * ν := Real.sq_sqrt (by positivity)
      rw [inv_pow, mul_pow, hs]
      field_simp
    rw [← h3]
    exact h2
  · apply fsf_le_of_sq_le_sq
    have h1 : ENNReal.ofReal ν * g ^ 2 ≤ ENNReal.ofReal ν⁻¹ * f ^ 2 :=
      le_trans le_add_self I1
    have h2 : g ^ 2 ≤ ENNReal.ofReal ν⁻¹ * (ENNReal.ofReal ν⁻¹ * f ^ 2) := by
      calc g ^ 2 = ENNReal.ofReal ν⁻¹ * (ENNReal.ofReal ν * g ^ 2) := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
              inv_mul_cancel₀ hν.ne', ENNReal.ofReal_one, one_mul]
        _ ≤ _ := by gcongr
    have h3 : ENNReal.ofReal ν⁻¹ * (ENNReal.ofReal ν⁻¹ * f ^ 2) =
        (ENNReal.ofReal ν⁻¹ * f) ^ 2 := by
      rw [mul_pow, ← mul_assoc, ← pow_two]
    rw [← h3]
    exact h2

/-! ## Step 1: smooth tests -/

/-- **The smooth stress column is causal** from (1) and (2). -/
theorem smoothStressColumn_of (h1 : BodyColumnTransport) (h2 : TensorDivIBP) :
    SmoothStressColumn := by
  intro c ν μ hc hν hμ M hM hMr G hG
  obtain ⟨b, Gr, hb, hcol⟩ := h1 c ν μ hc hν hμ M hM hMr G hG
  refine ⟨b, Gr, hb, ?_⟩
  have hper : ∀ x : Chart, M (Masked.cellPtInv c x) = M x := fun x =>
    fsf_cellPtInv_periodic hM.periodic x
  have key : ∀ Φ p, flatIntegrand ν (μ : ℂ) (fun _ _ _ => 0) (tblkF c M) b Φ p =
      FlatSettingInst.forcedIntegrand ν (μ : ℂ) (fun _ _ _ => 0) (fun x i => divEps 0 M x i) b Φ p +
        ∑ i : Fin 2, (divEps 0 M p i * (Φ p.1 p.2 i : ℂ) +
          ∑ j : Fin 2, tvBlk (M p) i j * (flatGrad Φ p.1 p.2 i j : ℂ)) := by
    intro Φ p
    simp only [FlatSettingInst.forcedIntegrand, flatIntegrand, tblkF, hper p, Fin.sum_univ_two,
      Complex.ofReal_zero, zero_mul, mul_zero, add_zero, sub_zero]
    ring
  refine
    { measurable := hcol.measurable
      gradMeasurable := hcol.gradMeasurable
      energyLoc := hcol.energyLoc
      zeroEntrance := hcol.zeroEntrance
      divFree := hcol.divFree
      weakGrad := hcol.weakGrad
      integrable := fun Φ hΦ => ?_
      weak := fun Φ hΦ => ?_ }
  · refine ((hcol.integrable Φ hΦ).add (h2 c hc M hM Φ hΦ).1).congr
      (Eventually.of_forall fun p => ?_)
    simp only [Pi.add_apply]
    exact (key Φ p).symm
  · simp_rw [key Φ]
    rw [integral_add (hcol.integrable Φ hΦ) (h2 c hc M hM Φ hΦ).1, hcol.weak Φ hΦ,
      (h2 c hc M hM Φ hΦ).2, add_zero]

/-! ## Step 3: passage to the limit -/

/-- **Every real tensor** (source 1675-1689, 3420-3440, 3541-3552), from the smooth columns, the
energy bound, density of real tests and the two transport bounds. -/
theorem stressColumnAll_of (hS : SmoothStressColumn) (hE : FreeEnergyFlat)
    (hA : RealTensorTestApprox) (hB : BlkNormLe) (hV : VelNormLe) : StressColumnAll := by
  intro c ν μ hc hν hμ hT hH S' hS' F hF
  obtain ⟨M, hM, hMt, hMr, hlim⟩ := hA c hc F hF
  obtain ⟨X, hXdef⟩ : ∃ X : ℕ → HTSpace c, ∀ n, X n = (hM n).toLp (M n) := ⟨_, fun _ => rfl⟩
  have hXae : ∀ n, (X n : Profile → TensorVal) =ᵐ[measureHT c] M n := fun n => by
    rw [hXdef n]; exact (hM n).coeFn_toLp
  have hlim' : Tendsto (fun n => ‖X n - F‖) atTop (𝓝 0) := by
    simpa only [hXdef] using hlim
  have hGm : ∀ n, MemLp (fun p : Profile => (p.1 : ℂ) • divEps 0 (M n) p) 2 (measureH c) :=
    fun n => Masked.tensorTestDivMem c 0 hc (M n) (hMt n)
  have hSX : ∀ n, S' (X n) = T0flat hc ν (μ : ℂ) ((hGm n).toLp _) := fun n =>
    hS' (M n) (hMt n) (X n) ((hGm n).toLp _) (hXae n) (hGm n).coeFn_toLp
  choose β Γ hβ hsol using fun n =>
    hS c ν μ hc hν hμ (M n) (hMt n) (hMr n) ((hGm n).toLp _) (hGm n).coeFn_toLp
  have hβ' : ∀ n, β n =ᵐ[ageμ c (-3 / 2)] velF c (S' (X n)) := fun n => by
    rw [hSX n]; exact hβ n
  obtain ⟨CB, -, hCB⟩ := hB c hc hT
  obtain ⟨CV, -, hCV⟩ := hV c hc hH
  have hμ' : 0 < (μ : ℂ).re + 1 / 4 := by simpa using hμ
  have hMmeas : ∀ n, Measurable (M n) := fun n => (hMt n).smooth.continuous.measurable
  have hFmeas : Measurable (F : Profile → TensorVal) := (Lp.stronglyMeasurable F).measurable
  have hFnm : ∀ n i j, Measurable fun p => tblkF c (M n) p i j := fun n i j =>
    fsf_measurable_tblkF (hMmeas n) i j
  have hFm : ∀ i j, Measurable fun p => tblkF c (F : Profile → TensorVal) p i j := fun i j =>
    fsf_measurable_tblkF hFmeas i j
  -- the `𝒯` distances of the forces
  have hdist : ∀ n, tCalNorm c (fun p i j => tblkF c (M n) p i j -
      tblkF c (F : Profile → TensorVal) p i j) ≤
      ENNReal.ofReal CB * ENNReal.ofReal ‖X n - F‖ := by
    intro n
    have h2 : eLpNorm (fun p => M n p - (F : Profile → TensorVal) p) 2 (measureHT c) =
        ENNReal.ofReal ‖X n - F‖ := by
      rw [ofReal_norm, Lp.enorm_def]
      refine eLpNorm_congr_ae ?_
      filter_upwards [Lp.coeFn_sub (X n) F, hXae n] with p h1 h2
      rw [h1, Pi.sub_apply, h2]
    rw [fsf_tblkF_sub c (M n) F, ← h2]
    exact hCB _ ((hMmeas n).aestronglyMeasurable.sub (Lp.aestronglyMeasurable F))
  have hFfin : tCalNorm c (tblkF c (F : Profile → TensorVal)) < ⊤ :=
    lt_of_le_of_lt (hCB _ (Lp.aestronglyMeasurable F))
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (Lp.eLpNorm_lt_top F))
  have he : Tendsto (fun n => ENNReal.ofReal ‖X n - F‖) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal hlim'
  -- the difference bounds
  have hbd : ∀ n m, tCalNorm c (gainConj 0 ν (fun p i j => tblkF c (M n) p i j -
        tblkF c (M m) p i j)) < ⊤ →
      hCalNorm c (gainConj 0 ν (fun p i => β n p i - β m p i)) ≤
          ENNReal.ofReal ((2 * Real.sqrt (((μ : ℂ).re + 1 / 4) * ν))⁻¹) *
            tCalNorm c (gainConj 0 ν (fun p i j => tblkF c (M n) p i j - tblkF c (M m) p i j)) ∧
        tCalNorm c (gainConj 0 ν (fun p i j => Γ n p i j - Γ m p i j)) ≤
          ENNReal.ofReal ν⁻¹ *
            tCalNorm c (gainConj 0 ν (fun p i j => tblkF c (M n) p i j - tblkF c (M m) p i j)) := by
    intro n m hfin
    simp only [fsf_gainConj_zero] at hfin ⊢
    have hsub := IIIa.causalSolSub c ν (μ : ℂ) (fun _ _ _ => 0) _ _ _ _ _ _ (hsol n) (hsol m)
    exact hE c ν (μ : ℂ) hc hν hμ' _
      (fun i j => (hFnm n i j).sub (hFnm m i j)) hfin _ _ hsub
  have hTend : Tendsto (fun n => tCalNorm c (gainConj 0 ν (fun p i j => tblkF c (M n) p i j -
      tblkF c (F : Profile → TensorVal) p i j))) atTop (𝓝 0) := by
    simp only [fsf_gainConj_zero]
    have h0 : Tendsto (fun n => ENNReal.ofReal CB * ENNReal.ofReal ‖X n - F‖) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul he (Or.inr ENNReal.ofReal_ne_top)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h0
      (fun n => bot_le) (fun n => hdist n)
  -- the limit solution
  obtain ⟨b₀, G₀, hAE⟩ := IIIa.causalLimitAE c ν 0 (μ : ℂ) hc hν
    (tblkF c (F : Profile → TensorVal)) hFm (by simpa only [fsf_gainConj_zero] using hFfin)
    (fun n => tblkF c (M n)) β Γ ((2 * Real.sqrt (((μ : ℂ).re + 1 / 4) * ν))⁻¹) ν⁻¹
    hFnm hsol hbd hTend
  obtain ⟨b₁, G₁, hsol₁⟩ := IIIa.causalNullModification c ν (μ : ℂ) (fun _ _ _ => 0) hc
    (tblkF c (F : Profile → TensorVal)) b₀ G₀ hAE
  -- identification with `S'F`
  have hvm : ∀ i, Measurable fun x => velF c (S' F : Profile → MeridC) x i :=
    fsf_measurable_velF (Lp.stronglyMeasurable (S' F)).measurable
  have hbound : ∀ n, hCalNorm c (fun p i => b₁ p i - velF c (S' F : Profile → MeridC) p i) ≤
      ENNReal.ofReal ((2 * Real.sqrt (((μ : ℂ).re + 1 / 4) * ν))⁻¹) *
          (ENNReal.ofReal CB * ENNReal.ofReal ‖X n - F‖) +
        ENNReal.ofReal CV * (ENNReal.ofReal ‖S'‖ * ENNReal.ofReal ‖X n - F‖) := by
    intro n
    have htri := fsf_hCal_tri c hsol₁.measurable (hsol n).measurable hvm
    have hsub := IIIa.causalSolSub c ν (μ : ℂ) (fun _ _ _ => 0) _ _ _ _ _ _ (hsol n) hsol₁
    have hfinn : tCalNorm c (fun p i j => tblkF c (M n) p i j -
        tblkF c (F : Profile → TensorVal) p i j) < ⊤ :=
      lt_of_le_of_lt (hdist n) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
    have h1 := (hE c ν (μ : ℂ) hc hν hμ' _
      (fun i j => (hFnm n i j).sub (hFm i j)) hfinn _ _ hsub).1
    rw [fsf_hCal_sub_comm] at h1
    have h2 : hCalNorm c (fun p i => β n p i - velF c (S' F : Profile → MeridC) p i) ≤
        ENNReal.ofReal CV * (ENNReal.ofReal ‖S'‖ * ENNReal.ofReal ‖X n - F‖) := by
      have hae : (fun p i => β n p i - velF c (S' F : Profile → MeridC) p i) =ᵐ[ageμ c (-3 / 2)]
          velF c (S' (X n) - S' F : HSpace c MeridC) := by
        filter_upwards [hβ' n, fsf_velF_sub_ae hc (S' (X n)) (S' F)] with x hx1 hx2
        rw [hx2, hx1]
      rw [fsf_hCal_congr hae]
      refine (hCV _ (Lp.aestronglyMeasurable _)).trans ?_
      gcongr
      rw [← Lp.enorm_def, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _), ← map_sub]
      exact ENNReal.ofReal_le_ofReal (S'.le_opNorm _)
    calc hCalNorm c (fun p i => b₁ p i - velF c (S' F : Profile → MeridC) p i)
        ≤ hCalNorm c (fun p i => b₁ p i - β n p i) +
            hCalNorm c (fun p i => β n p i - velF c (S' F : Profile → MeridC) p i) := htri
      _ ≤ _ := add_le_add (h1.trans (by gcongr; exact hdist n)) h2
  have hzero : hCalNorm c (fun p i => b₁ p i - velF c (S' F : Profile → MeridC) p i) = 0 := by
    have hT0 : Tendsto (fun n => ENNReal.ofReal ((2 * Real.sqrt (((μ : ℂ).re + 1 / 4) * ν))⁻¹) *
          (ENNReal.ofReal CB * ENNReal.ofReal ‖X n - F‖) +
        ENNReal.ofReal CV * (ENNReal.ofReal ‖S'‖ * ENNReal.ofReal ‖X n - F‖)) atTop (𝓝 0) := by
      have hA1 := ENNReal.Tendsto.const_mul
        (a := ENNReal.ofReal ((2 * Real.sqrt (((μ : ℂ).re + 1 / 4) * ν))⁻¹))
        (ENNReal.Tendsto.const_mul (a := ENNReal.ofReal CB) he (Or.inr ENNReal.ofReal_ne_top))
        (Or.inr ENNReal.ofReal_ne_top)
      have hA2 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal CV)
        (ENNReal.Tendsto.const_mul (a := ENNReal.ofReal ‖S'‖) he (Or.inr ENNReal.ofReal_ne_top))
        (Or.inr ENNReal.ofReal_ne_top)
      simpa using hA1.add hA2
    exact le_antisymm (ge_of_tendsto' hT0 hbound) bot_le
  exact ⟨b₁, G₁, fsf_ae_eq_of_hCal_zero hsol₁.measurable hvm hzero, hsol₁⟩

/-! ## Step 4: the real form -/

/-- **`FlatStressFree` from the six leaves** (source 1650-1689, 3420-3440, 3541-3552,
3561-3571). -/
theorem flatStressFree_of (h1 : BodyColumnTransport) (h2 : TensorDivIBP) (h3 : FreeEnergyFlatSq)
    (h4 : RealTensorTestApprox) (h5 : BlkNormLe) (h6 : VelNormLe) : FlatStressFree := by
  have hAll := stressColumnAll_of (smoothStressColumn_of h1 h2) (freeEnergyFlat_of h3) h4 h5 h6
  intro ν c μ mZ ρb hc hmZ hρ hT hH hν _hcν hμ0 _hμ1 S' hS' hR F
  have hreal : Masked.IsRealHT c (Masked.cplxT c hT (Masked.zsumL c mZ ρb hmZ hρ F)) := by
    filter_upwards [Masked.cplxT_ae c hT (Masked.zsumL c mZ ρb hmZ hρ F)] with p hp i
    rw [hp]
    fin_cases i <;> simp [tv4]
  obtain ⟨b, G, hb, hsol⟩ := hAll c ν μ hc hν (by linarith) hT hH S' hS'
    (Masked.cplxT c hT (Masked.zsumL c mZ ρb hmZ hρ F)) hreal
  refine ⟨b, G, ?_, ?_⟩
  · have hS : Masked.realForm c mZ ρb hmZ hρ hT hH S' F =
        Masked.reH c hH (S' (Masked.cplxT c hT (Masked.zsumL c mZ ρb hmZ hρ F))) := rfl
    rw [hS]
    exact hb.trans (fsf_velC_reH_ae hc hH _ (hR _ hreal)).symm
  · exact fsf_congr_F hsol
      ((UnforcedLeray.Short.IIIa.restrict_ac_ageμ hc).ae_le (fsf_tblkF_cplxT_ae hc hmZ hρ hT F))

end UnforcedLeray.Short.PartIIIb.NearInst.Delta
