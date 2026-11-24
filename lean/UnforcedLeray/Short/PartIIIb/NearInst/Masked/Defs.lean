import UnforcedLeray.Short.PartIIIb.NearInst.Targets
import UnforcedLeray.Short.PartIIIb.NearInst.Delta.Defs

/-!
# The masked near free inverse: transports, kernels and pieces (source 1638-1690, 3888-3912,
3996-4031)

Source of record: `the November 2 reference manuscript`.  Concrete objects for the
decomposition of `MaskedNearExists` and `NearMaskedFreeBoundC` (`NearInst/Targets.lean`).

## The real form of the `PartII-a` stress map (source 1641-1646, 1675-1690, 2664-2683)

The curved free inverse `S_ε = T_ε s div_ε` is defined in `PartII-a/StatementsNear.lean` on the
complex spaces `HTSpace c = L²(s^{-1/2} ds dq dη; ℂ⁴)` (components `(T_rr, T_rz, T_zz, T_φφ)`) and
`HSpace c MeridC = L²(s^{-3/2} ds dq dη; ℂ²)` over the cell `q ∈ (0, c]` with unnormalised `dq`.
The near spaces of `Concrete/Spaces.lean` are real, over the recentred cell `q ∈ [-c/2, c/2)` with
`dq/c`.  The transports:

* `tv4L : Ten3 →L[ℝ] TensorVal` (the dictionary `tv4` of `Chart.lean`: `nsSym`, components
  `(T_rr, (T_rz + T_zr)/2, T_zz, T_φφ)`, complexified) and `merReL : MeridC →L[ℝ] Merid` (real
  parts);
* `cellPtInv c` : the inverse of the recentring `cellPt c` (`(0, c] → [-c/2, c/2)`);
* `zsumL` : `F ↦ F₁ + F₂ : Z → H_T` (`‖F₁ + F₂‖_{H_T} ≤ ‖F₁‖_{Z₁} + √ρ_b‖F₂‖_{ρ_b^{-1/2}H_T}`,
  `W ≥ 1`; source 2700, 3874 "the stress inverse always acts on the sum of the components");
* `cplxT h` : `T ↦ tv4 ∘ T ∘ cellPt : H_T → HTSpace c`, and `reH h` : `g ↦ Re g ∘ cellPtInv :
  HSpace c MeridC → H`, given the change-of-variables inequalities `CellPtHT c`, `CellPtInvH c`
  (`dq` versus `dq/c`: the norms change by the factor `√c`, which cancels in `S_ε`);
* `realForm hT hH S' = reH ∘ S' ∘ cplxT ∘ zsumL : Z → H` : the real form of a complex stress map
  `S'`.  When `S'` maps real tensors to real fields (`IsRealStress`), `realForm` satisfies the pin
  `IsStressTransport` (`isStressTransport_realForm`, proved here).

## The kernel realization (source 3611-3621 `sep:resolvent`, 3905-3912)

* `farOut R c ν μ δ S f` : the right side of the pin `IsFarMask` on a box tensor `f`,
  `1_{s<S} s^{-1/2} Re(-W_μ[1_{t>e^δ s}𝒩_T f])_{r,z}` at `(y, τ) = (chartY, chartTau)`.
* `fullOut R c ν μ f` : the same without mask and output cut: the kernel realization of `S_ε`
  (`sep:resolvent` for the conjugated Cartesian weak-stress inverse, 3888-3897).
* `IsMaskedPair p μ δ S Seps Sf` : `Seps` is the real form of a `PartIIa.IsStressMap` for
  `PartIIa.Teps` at the level `p`, and `Sf` has the far pin; `isMaskedNear_iff`.

## Output regions (source 3974-3977, 4011-4031)

* `ageBand l r = {l ≤ s < r}` (an output bin without transverse cut; the masked free bound
  imposes no transverse weight, 4023-4031).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Delta
  UnforcedLeray.Cons.C03.Concrete

/-! ## Pointwise dictionaries -/

/-- `tv4` as a real-linear map `Ten3 → TensorVal`. -/
def tv4Lin : Ten3 →ₗ[ℝ] UnforcedLeray.Short.PartIIa.TensorVal where
  toFun := tv4
  map_add' T T' := by
    ext i
    fin_cases i <;> simp [tv4, symRZ] <;> ring
  map_smul' a T := by
    ext i
    fin_cases i <;> simp [tv4, symRZ] <;> ring

/-- `tv4` as a continuous real-linear map. -/
def tv4L : Ten3 →L[ℝ] UnforcedLeray.Short.PartIIa.TensorVal :=
  LinearMap.toContinuousLinearMap tv4Lin

theorem tv4L_apply (T : Ten3) : tv4L T = tv4 T := rfl

/-- The real part of a complex meridional vector, as a real-linear map. -/
def merReLin : UnforcedLeray.B0223.MeridC →ₗ[ℝ] Merid where
  toFun g := WithLp.toLp 2 fun i => (g i).re
  map_add' g g' := by
    ext i
    simp
  map_smul' a g := by
    ext i
    simp

/-- The real part `MeridC → Merid`, continuous. -/
def merReL : UnforcedLeray.B0223.MeridC →L[ℝ] Merid :=
  LinearMap.toContinuousLinearMap merReLin

theorem merReL_apply (g : UnforcedLeray.B0223.MeridC) (i : Fin 2) : merReL g i = (g i).re := rfl

theorem merReL_merC (b : Merid) : merReL (merC b) = b := by
  ext i
  simp [merReL_apply, merC]

/-- A complex meridional vector with zero imaginary parts is `merC` of its real part. -/
theorem merC_merReL {g : UnforcedLeray.B0223.MeridC} (h : ∀ i, (g i).im = 0) :
    merC (merReL g) = g := by
  ext i
  apply Complex.ext
  · simp [merC, merReL_apply]
  · simp [merC, merReL_apply, h i]

/-! ## The recentring of the cell -/

/-- The inverse of `cellPt c`: `q ∈ (0, c/2) ↦ q`, `q ∈ [-c/2, 0] ↦ q + c`. -/
def cellPtInv (c : ℝ) (x : Chart) : UnforcedLeray.B0220.Profile :=
  (x.1, (if 0 < x.2.1 then x.2.1 else x.2.1 + c, x.2.2))

theorem measurable_cellPt (c : ℝ) : Measurable (cellPt c) := by
  unfold cellPt
  refine measurable_fst.prodMk (Measurable.prodMk ?_ (measurable_snd.comp measurable_snd))
  refine Measurable.ite ?_ (measurable_fst.comp measurable_snd)
    ((measurable_fst.comp measurable_snd).sub_const c)
  exact measurableSet_lt (measurable_fst.comp measurable_snd) measurable_const

theorem measurable_cellPtInv (c : ℝ) : Measurable (cellPtInv c) := by
  unfold cellPtInv
  refine measurable_fst.prodMk (Measurable.prodMk ?_ (measurable_snd.comp measurable_snd))
  refine Measurable.ite ?_ (measurable_fst.comp measurable_snd)
    ((measurable_fst.comp measurable_snd).add_const c)
  exact measurableSet_lt measurable_const (measurable_fst.comp measurable_snd)

/-- `cellPtInv ∘ cellPt = id` on the cell `q ∈ (0, c]`. -/
theorem cellPtInv_cellPt {c : ℝ} {p : UnforcedLeray.B0220.Profile} (h0 : 0 < p.2.1)
    (hc : p.2.1 ≤ c) : cellPtInv c (cellPt c p) = p := by
  obtain ⟨s, q, η⟩ := p
  simp only at h0 hc
  unfold cellPt cellPtInv
  by_cases hq : q < c / 2
  · simp [hq, h0]
  · have : ¬ (0 < q - c) := by linarith
    simp [hq, this]

/-! ## Change of variables (the measure inequalities used by the transports) -/

/-- `cellPt` carries `s^{-1/2} ds dq dη` on `(0, ∞) × (0, c] × ℝ` to `c · s^{-1/2} ds dq/c dη` on the
recentred cell (source 1641-1643 and 2676-2679: the two normalisations differ by `dq` versus
`dq/c`). -/
abbrev CellPtHT (c : ℝ) : Prop :=
  Measure.map (cellPt c) (UnforcedLeray.Short.PartIIa.measureHT c) =
    ENNReal.ofReal c • ageμ c (-1 / 2)

/-- The same for the velocity measure `s^{-3/2} ds dq dη`. -/
abbrev CellPtH (c : ℝ) : Prop :=
  Measure.map (cellPt c) (UnforcedLeray.B0220.measureH c) = ENNReal.ofReal c • ageμ c (-3 / 2)

/-- `cellPtInv` carries `s^{-3/2} ds dq/c dη` on the recentred cell to `c⁻¹ s^{-3/2} ds dq dη` on
`(0, ∞) × (0, c] × ℝ`. -/
abbrev CellPtInvH (c : ℝ) : Prop :=
  Measure.map (cellPtInv c) (ageμ c (-3 / 2)) =
    ENNReal.ofReal c⁻¹ • UnforcedLeray.B0220.measureH c

/-! ## The sum of the components -/

/-- `W ≥ 1` for `m_Z ≥ 0` (source 2696). -/
theorem one_le_transWeight {mZ : ℝ} (hmZ : 0 ≤ mZ) (p : Chart) :
    1 ≤ UnforcedLeray.Short.IIIa.transWeight mZ p := by
  unfold UnforcedLeray.Short.IIIa.transWeight
  exact Real.one_le_rpow (by nlinarith [sq_nonneg (p.2.2 / Real.sqrt (1 + p.1))])
    (by positivity)

theorem ageμ_le_z1Measure {c mZ : ℝ} (hmZ : 0 ≤ mZ) :
    ageμ c (-1 / 2) ≤ (1 : ℝ≥0∞) • z1Measure c mZ := by
  rw [one_smul, z1Measure]
  conv_lhs => rw [← withDensity_one (μ := ageμ c (-1 / 2))]
  refine withDensity_mono (Filter.Eventually.of_forall fun p => ?_)
  simp only [Pi.one_apply]
  have h1 := one_le_transWeight hmZ p
  rw [← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (by nlinarith)

theorem ageμ_le_htRho {c ρb : ℝ} (hρ : 0 < ρb) :
    ageμ c (-1 / 2) ≤ ENNReal.ofReal ρb • htRhoMeasure c ρb := by
  rw [htRhoMeasure, smul_smul, ← ENNReal.ofReal_mul hρ.le, mul_inv_cancel₀ hρ.ne',
    ENNReal.ofReal_one, one_smul]

/-- The inclusion `Z₁ → H_T` (`W ≥ 1`). -/
def inclZ1 (c mZ : ℝ) (hmZ : 0 ≤ mZ) : Z1sp c mZ →L[ℝ] HTsp c :=
  Lp.LpToLpOfMeasureLeSMul ENNReal.one_ne_top (ageμ_le_z1Measure hmZ)

/-- The inclusion `ρ_b^{-1/2}H_T → H_T` (norm `√ρ_b`). -/
def inclRho (c ρb : ℝ) (hρ : 0 < ρb) : HTrho c ρb →L[ℝ] HTsp c :=
  Lp.LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top (ageμ_le_htRho hρ)

/-- `F ↦ F₁ + F₂ : Z → H_T` (source 2700, 3874). -/
def zsumL (c mZ ρb : ℝ) (hmZ : 0 ≤ mZ) (hρ : 0 < ρb) : Zsp c mZ ρb →L[ℝ] HTsp c :=
  ((inclZ1 c mZ hmZ).comp (ContinuousLinearMap.fst ℝ (Z1sp c mZ) (HTrho c ρb)) +
      (inclRho c ρb hρ).comp (ContinuousLinearMap.snd ℝ (Z1sp c mZ) (HTrho c ρb))).comp
    (zEquiv c mZ ρb : Zsp c mZ ρb →L[ℝ] Z1sp c mZ × HTrho c ρb)

theorem zsumL_ae (c mZ ρb : ℝ) (hmZ : 0 ≤ mZ) (hρ : 0 < ρb) (F : Zsp c mZ ρb) :
    (zsumL c mZ ρb hmZ hρ F : Chart → Ten3) =ᵐ[ageμ c (-1 / 2)] zsum F := by
  have h1 := Lp.coeFn_LpToLpOfMeasureLeSMul ENNReal.one_ne_top (ageμ_le_z1Measure hmZ)
    (zEquiv c mZ ρb F).1
  have h2 := Lp.coeFn_LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top (ageμ_le_htRho hρ)
    (zEquiv c mZ ρb F).2
  filter_upwards [Lp.coeFn_add (inclZ1 c mZ hmZ (zEquiv c mZ ρb F).1)
    (inclRho c ρb hρ (zEquiv c mZ ρb F).2), h1, h2] with x hx hx1 hx2
  simp only [zsumL, ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', ContinuousLinearEquiv.coe_coe]
  rw [hx, Pi.add_apply]
  unfold inclZ1 inclRho
  rw [hx1, hx2]
  rfl

/-! ## The transports to the complex spaces of `PartII-a` -/

/-- `T ↦ tv4 ∘ T ∘ cellPt : H_T → HTSpace c` (source 1641-1646; the dictionary of `Chart.lean`). -/
def cplxT (c : ℝ) (h : CellPtHT c) : HTsp c →L[ℝ] UnforcedLeray.Short.PartIIa.HTSpace c :=
  (Lp.compMeasurePreservingₗᵢ ℝ (cellPt c)
      ((measurable_cellPt c).measurePreserving (UnforcedLeray.Short.PartIIa.measureHT c))).toContinuousLinearMap.comp
    ((Lp.LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top h.le).comp
      (tv4L.compLpL 2 (ageμ c (-1 / 2))))

/-- `g ↦ Re g ∘ cellPtInv : HSpace c MeridC → H`. -/
def reH (c : ℝ) (h : CellPtInvH c) : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC →L[ℝ] Hsp c :=
  (merReL.compLpL 2 (ageμ c (-3 / 2))).comp
    ((Lp.compMeasurePreservingₗᵢ ℝ (cellPtInv c)
        ((measurable_cellPtInv c).measurePreserving (ageμ c (-3 / 2)))).toContinuousLinearMap.comp
      (Lp.LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top h.le))

/-- The real form `reH ∘ S' ∘ cplxT ∘ zsumL : Z → H` of a complex stress map `S' : H_T → H`. -/
def realForm (c mZ ρb : ℝ) (hmZ : 0 ≤ mZ) (hρ : 0 < ρb) (hT : CellPtHT c) (hH : CellPtInvH c)
    (S' : UnforcedLeray.Short.PartIIa.HTSpace c →L[ℂ]
      UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC) : Zsp c mZ ρb →L[ℝ] Hsp c :=
  (reH c hH).comp ((S'.restrictScalars ℝ).comp ((cplxT c hT).comp (zsumL c mZ ρb hmZ hρ)))

/-! ## Real fields -/

/-- A complex tensor field with zero imaginary parts (a.e.). -/
def IsRealHT (c : ℝ) (F : UnforcedLeray.Short.PartIIa.HTSpace c) : Prop :=
  ∀ᵐ p ∂UnforcedLeray.Short.PartIIa.measureHT c, ∀ i, ((F : UnforcedLeray.B0220.Profile →
    UnforcedLeray.Short.PartIIa.TensorVal) p i).im = 0

/-- A complex meridional field with zero imaginary parts (a.e.). -/
def IsRealH (c : ℝ) (g : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC) : Prop :=
  ∀ᵐ p ∂UnforcedLeray.B0220.measureH c, ∀ i,
    ((g : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC) p i).im = 0

/-- `S'` maps real tensors to real fields. -/
def IsRealStress (c : ℝ) (S' : UnforcedLeray.Short.PartIIa.HTSpace c →L[ℂ]
    UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC) : Prop :=
  ∀ F, IsRealHT c F → IsRealH c (S' F)

/-! ## The real form satisfies the transport pin -/

theorem ae_mem_cell_H (c : ℝ) :
    ∀ᵐ p ∂UnforcedLeray.B0220.measureH c, p ∈ UnforcedLeray.B0220.cell c := by
  have hm : MeasurableSet (UnforcedLeray.B0220.cell c) :=
    measurableSet_Ioi.prod (measurableSet_Ioc.prod MeasurableSet.univ)
  exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hm)

theorem cplxT_ae (c : ℝ) (h : CellPtHT c) (T : HTsp c) :
    (cplxT c h T : UnforcedLeray.B0220.Profile → UnforcedLeray.Short.PartIIa.TensorVal)
      =ᵐ[UnforcedLeray.Short.PartIIa.measureHT c] fun p => tv4 ((T : Chart → Ten3) (cellPt c p)) := by
  have hmp := (measurable_cellPt c).measurePreserving (UnforcedLeray.Short.PartIIa.measureHT c)
  have hac := Measure.absolutelyContinuous_of_le_smul h.le
  have h1 := Lp.coeFn_compMeasurePreserving
    ((Lp.LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top h.le) (tv4L.compLpL 2 (ageμ c (-1 / 2)) T)) hmp
  have h2 := Lp.coeFn_LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top h.le
    (tv4L.compLpL 2 (ageμ c (-1 / 2)) T)
  have h3 : ∀ᵐ x ∂Measure.map (cellPt c) (UnforcedLeray.Short.PartIIa.measureHT c),
      (tv4L.compLpL 2 (ageμ c (-1 / 2)) T : Chart → _) x = tv4L ((T : Chart → Ten3) x) :=
    hac.ae_le (tv4L.coeFn_compLp T)
  have h4 := ae_of_ae_map hmp.aemeasurable (h2.and h3)
  have he : cplxT c h T = Lp.compMeasurePreserving (cellPt c) hmp
      ((Lp.LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top h.le) (tv4L.compLpL 2 (ageμ c (-1 / 2)) T)) :=
    rfl
  filter_upwards [h1, h4] with p hp1 hp4
  rw [he, hp1, Function.comp_apply, hp4.1, hp4.2, tv4L_apply]

theorem reH_ae (c : ℝ) (h : CellPtInvH c)
    (g : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC) :
    (reH c h g : Chart → Merid) =ᵐ[ageμ c (-3 / 2)] fun x =>
      merReL ((g : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC) (cellPtInv c x)) := by
  have hmp := (measurable_cellPtInv c).measurePreserving (ageμ c (-3 / 2))
  have hac := Measure.absolutelyContinuous_of_le_smul h.le
  have h0 := merReL.coeFn_compLp (Lp.compMeasurePreserving (cellPtInv c) hmp
      ((Lp.LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top h.le) g))
  have h1 := Lp.coeFn_compMeasurePreserving ((Lp.LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top h.le) g) hmp
  have h2 := Lp.coeFn_LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top h.le g
  have h4 := ae_of_ae_map hmp.aemeasurable h2
  have he : reH c h g = merReL.compLp (Lp.compMeasurePreserving (cellPtInv c) hmp
      ((Lp.LpToLpOfMeasureLeSMul ENNReal.ofReal_ne_top h.le) g)) := rfl
  filter_upwards [h0, h1, h4] with x hx0 hx1 hx4
  rw [he]
  rw [hx0, hx1, Function.comp_apply, hx4]

/-- **The real form is a transport** (source 1641-1646, 2676-2683): if `S'` maps real tensors to
real fields, then `realForm S'` is the real form of `S'` in the sense of `IsStressTransport`. -/
theorem isStressTransport_realForm {c mZ ρb : ℝ} (hmZ : 0 ≤ mZ) (hρ : 0 < ρb)
    (hT : CellPtHT c) (hH : CellPtInvH c) (hH' : CellPtH c)
    (S' : UnforcedLeray.Short.PartIIa.HTSpace c →L[ℂ]
      UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC) (hR : IsRealStress c S') :
    IsStressTransport (realForm c mZ ρb hmZ hρ hT hH S') S' := by
  intro F F' hF'
  -- the input is the transport of `F₁ + F₂`
  have hin : F' = cplxT c hT (zsumL c mZ ρb hmZ hρ F) := by
    apply Lp.ext
    have hmp := (measurable_cellPt c).measurePreserving (UnforcedLeray.Short.PartIIa.measureHT c)
    have hac := Measure.absolutelyContinuous_of_le_smul hT.le
    have hz := ae_of_ae_map hmp.aemeasurable (hac.ae_le (zsumL_ae c mZ ρb hmZ hρ F))
    filter_upwards [hF', cplxT_ae c hT (zsumL c mZ ρb hmZ hρ F), hz] with p h1 h2 h3
    rw [h1, h2, h3]
  -- it is real
  have hreal : IsRealHT c F' := by
    filter_upwards [hF'] with p hp i
    rw [hp]
    fin_cases i <;> simp [tv4]
  have hout := hR F' hreal
  -- the output
  have hmp' := (measurable_cellPt c).measurePreserving (UnforcedLeray.B0220.measureH c)
  have hac' := Measure.absolutelyContinuous_of_le_smul hH'.le
  have hre := ae_of_ae_map hmp'.aemeasurable (hac'.ae_le (reH_ae c hH (S' F')))
  filter_upwards [hout, hre, ae_mem_cell_H c] with p hp1 hp2 hp3
  have hS : realForm c mZ ρb hmZ hρ hT hH S' F = reH c hH (S' F') := by
    rw [hin]; rfl
  rw [hS, hp2, cellPtInv_cellPt hp3.2.1.1 hp3.2.1.2, merC_merReL hp1]

/-! ## Kernel realizations (source 3611-3621, 3888-3912) -/

/-- The right side of the far pin `IsFarMask` on a chart tensor `f` (source 3905-3912):
`1_{s<S} s^{-1/2} Re(-W_μ[1_{t>e^δ s}𝒩_T f])_{r,z}` at `(y, τ) = (chartY R x, chartTau R x)`. -/
def farOut (R c ν μ δ S : ℝ) (f : Chart → Ten3) (x : Chart) : Merid :=
  if x.1 < S then
    (Real.sqrt x.1)⁻¹ • merRe (-sepWfar ν (μ : ℂ) R δ x.1 (cartLift R c f) (chartY R x)
      (chartTau R x))
  else 0

/-- The unmasked kernel output `s^{-1/2} Re(-W_μ[𝒩_T f])_{r,z}` (`sep:resolvent`, source 3611-3621,
for the conjugated Cartesian weak-stress inverse, 3888-3897). -/
def fullOut (R c ν μ : ℝ) (f : Chart → Ten3) (x : Chart) : Merid :=
  (Real.sqrt x.1)⁻¹ • merRe (-UnforcedLeray.Short.IIIa.sepW ν (μ : ℂ) (cartLift R c f)
    (chartY R x) (chartTau R x))

theorem isFarMask_iff {c mZ ρb : ℝ} (R ν μ δ S : ℝ) (Sf : Zsp c mZ ρb →L[ℝ] Hsp c) :
    IsFarMask R ν μ δ S Sf ↔
      ∀ (F : Zsp c mZ ρb) (f : Chart → Ten3), IsBoxTensor f → zsum F =ᵐ[ageμ c (-1 / 2)] f →
        (Sf F : Chart → Merid) =ᵐ[ageμ c (-3 / 2)] farOut R c ν μ δ S f :=
  Iff.rfl

/-! ## The masked pair -/

/-- `Seps` is the real form of a `PartIIa.IsStressMap` for `PartIIa.Teps` at the level `p`
(source 1675-1679, 3888-3897) and `Sf` has the far pin with gap `δ` and output cut `S`
(source 3905-3912). -/
def IsMaskedPair {mZ ρb : ℝ} (p : Params) (μ δ S : ℝ) (Seps Sf : Zsp p.c mZ ρb →L[ℝ] Hsp p.c) :
    Prop :=
  (∃ Seps' : UnforcedLeray.Short.PartIIa.HTSpace p.c →L[ℂ]
      UnforcedLeray.B0220.HSpace p.c UnforcedLeray.B0223.MeridC,
    UnforcedLeray.Short.PartIIa.IsStressMap p.c p.ε
        (UnforcedLeray.Short.PartIIa.Teps (P := p.period) p.ν_pos p.ε_pos p.c_pos rfl (μ : ℂ))
        Seps' ∧ IsStressTransport Seps Seps') ∧
    IsFarMask p.R p.ν μ δ S Sf

theorem isMaskedNear_iff {mZ ρb : ℝ} (p : Params) (μ δ S : ℝ) (SN : Zsp p.c mZ ρb →L[ℝ] Hsp p.c) :
    IsMaskedNear p μ δ S SN ↔ ∃ Seps Sf, IsMaskedPair p μ δ S Seps Sf ∧ SN = Seps - Sf := by
  constructor
  · rintro ⟨Seps, Sf, Seps', h1, h2, h3, h4⟩
    exact ⟨Seps, Sf, ⟨⟨Seps', h1, h2⟩, h3⟩, h4⟩
  · rintro ⟨Seps, Sf, ⟨⟨Seps', h1, h2⟩, h3⟩, h4⟩
    exact ⟨Seps, Sf, Seps', h1, h2, h3, h4⟩

/-! ## Output regions -/

/-- The output band `{l ≤ s < r}` (a bin of source 3974-3977 without transverse cut). -/
def ageBand (l r : ℝ) : Set Chart := {p | l ≤ p.1 ∧ p.1 < r}

theorem measurableSet_ageBand (l r : ℝ) : MeasurableSet (ageBand l r) :=
  (measurableSet_le measurable_const measurable_fst).inter
    (measurableSet_lt measurable_fst measurable_const)

/-! ## The dense class -/

theorem IsBoxTensor.indicator {f : Chart → Ten3} (hf : IsBoxTensor f) {A : Set Chart}
    (hA : MeasurableSet A) : IsBoxTensor (A.indicator f) where
  measurable := hf.measurable.indicator hA
  bounded := by
    obtain ⟨B, hB⟩ := hf.bounded
    refine ⟨B, fun p => ?_⟩
    by_cases hp : p ∈ A
    · simpa [Set.indicator_of_mem hp] using hB p
    · simpa [Set.indicator_of_notMem hp] using (norm_nonneg (f p)).trans (hB p)
  band := by
    obtain ⟨s₁, s₂, L, hs₁, h⟩ := hf.band
    refine ⟨s₁, s₂, L, hs₁, fun p hp => h p ?_⟩
    by_cases hpA : p ∈ A
    · simpa [Set.indicator_of_mem hpA] using hp
    · exact absurd (Set.indicator_of_notMem hpA f) hp

end UnforcedLeray.Short.PartIIIb.NearInst.Masked
