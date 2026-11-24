import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Kflat
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AyDiffAt
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnOps.BmatLinear

/-!
# `PartIII-b:C/asrc/kflat/2` : decomposition of `frakTLinear`

Source of record: `the November 2 reference manuscript`.

`𝔗_{μ,ν}A = M_{B_{μ,ν}[A]}` (source 4605-4612, 4761-4763) is `S ↦ v ⊗ K_cξ_B + K_cξ_B ⊗ v` with
`ξ_B(s) = s^{-μ}∫₀^s t^μ 𝒰(s,t)g_B(t) dt` (4610); linearity in `A` (4985) factors through

* `DuhIntegrableProp` : the Duhamel integrands of `B = B_{μ,ν}[A]` are integrable on `(0,s]`
  (`g_B` bounded by `C t^{3/2}` by `bmatBound`, `𝒰` locally bounded and strongly continuous);
* `XiDLinearProp` : `ξ_B` is additive and homogeneous in `B` once the integrands are integrable
  (`g_B` is pointwise linear in `B`, 4605-4608);
* `KcMerLinearProp` : `K_cξ` (Lebesgue value of `kcLp`) is linear a.e. on the cell;
* `FrakTMeasProp` (shared with `PartIII-b:C/asrc/kflat/1/1`) : `𝔗A` is a.e. strongly measurable
  on the old region, used to pass from slice-wise a.e. equality to a.e. for the product measure.

`frakTLinear_of` assembles these.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open FlatSettingInst

/-- Product a.e. equality from slicewise a.e. equality for a.e.-strongly-measurable maps. -/
theorem ae_prod_eq_of_ae_ae {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν] [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {f g : α × β → E}
    (hf : AEStronglyMeasurable f (μ.prod ν)) (hg : AEStronglyMeasurable g (μ.prod ν))
    (h : ∀ᵐ a ∂μ, ∀ᵐ b ∂ν, f (a, b) = g (a, b)) : f =ᵐ[μ.prod ν] g := by
  have hf' : f =ᵐ[μ.prod ν] hf.mk f := hf.ae_eq_mk
  have hg' : g =ᵐ[μ.prod ν] hg.mk g := hg.ae_eq_mk
  have hfs := Measure.ae_ae_of_ae_prod hf'
  have hgs := Measure.ae_ae_of_ae_prod hg'
  have hmeas : MeasurableSet {z | hf.mk f z = hg.mk g z} :=
    measurableSet_eq_fun hf.stronglyMeasurable_mk.measurable hg.stronglyMeasurable_mk.measurable
  have key : ∀ᵐ z ∂μ.prod ν, hf.mk f z = hg.mk g z := by
    rw [Measure.ae_prod_iff_ae_ae hmeas]
    filter_upwards [h, hfs, hgs] with a ha hfa hga
    filter_upwards [ha, hfa, hga] with b hb hfb hgb
    rw [← hfb, ← hgb, hb]
  filter_upwards [hf', hg', key] with z h1 h2 h3
  rw [h1, h2, h3]

/-- The integrand `t ↦ t^μ 𝒰(s,t) g_B(t)` of the Duhamel integral defining `ξ_B(s)` (source 4610). -/
def DuhIntegrand {κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels} {ν m : ℝ} [Fact (1 < m)]
    [Fact (0 < cOf ν)] {tr : UnforcedLeray.B0140.TrainSol ν (cOf ν)}
    (FI : FlatInstData κ ν (cOf ν) m tr) (μ : ℝ) (B : ℝ → Matrix (Fin 3) (Fin 3) ℝ) (s t : ℝ) :
    Xmc (cOf ν) m :=
  ((t : ℂ) ^ (μ : ℂ)) • (FI.ev.U s t) (gBD FI B t)

/-- **Leaf 1.** The Duhamel integrands of `B_{μ,ν}[A]` are integrable on `(0,s]` for `A ∈ 𝒜`
(source 4637-4640, 4686-4693: `g_B` is supported in `t ≤ 1.1/ν` with `|B(t)| ≤ C t^{3/2}`). -/
def DuhIntegrableProp (as : ℝ) (χf : ℝ → ℝ) (m : ℝ) [Fact (1 < m)] : Prop :=
  IsSourceCutoffC χf → ∀ (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels) (ν μ : ℝ)
    (hν : 0 < ν), ν ≤ 1 → 0 ≤ μ → μ < 1 / 4 →
    ∀ (tr : UnforcedLeray.B0140.TrainSol ν (cOf ν))
      (FI : FlatInstData κ ν (cOf ν) m tr) (A : ℝ → Mat3), IsAffElem as A → ∀ s : ℝ,
      haveI : Fact (0 < cOf ν) := ⟨UnforcedLeray.Short.PartIIIb.Concrete.cOf_pos hν⟩
      IntegrableOn (DuhIntegrand FI μ (Bmat ν μ χf A) s) (Ioc 0 s)

/-- **Leaf 2.** `ξ_B` is linear in `B` for `B` with integrable Duhamel integrands, `B''` agreeing
with `B + B'` (resp. `r • B`) at ages `t > 0` (`g_B` is pointwise linear in `B`, 4605-4608). -/
def XiDLinearProp (m : ℝ) [Fact (1 < m)] : Prop :=
  ∀ (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels) (ν μ : ℝ) (hν : 0 < ν)
    (tr : UnforcedLeray.B0140.TrainSol ν (cOf ν)) (FI : FlatInstData κ ν (cOf ν) m tr)
    (B B' B'' : ℝ → Matrix (Fin 3) (Fin 3) ℝ) (r u : ℝ),
    haveI : Fact (0 < cOf ν) := ⟨UnforcedLeray.Short.PartIIIb.Concrete.cOf_pos hν⟩
    IntegrableOn (DuhIntegrand FI μ B u) (Ioc 0 u) →
    IntegrableOn (DuhIntegrand FI μ B' u) (Ioc 0 u) →
    ((∀ t, 0 < t → B'' t = B t + B' t) →
      xiD FI (μ : ℂ) B'' u = xiD FI (μ : ℂ) B u + xiD FI (μ : ℂ) B' u) ∧
    ((∀ t, 0 < t → B'' t = r • B t) → xiD FI (μ : ℂ) B'' u = (r : ℂ) • xiD FI (μ : ℂ) B u)

/-- **Leaf 3.** `K_cξ` (the Lebesgue value `kcMer` of `kcLp`) is linear a.e. on the cell
(`kcLp` is linear, `lebRep_ae`; source 4610-4612). -/
def KcMerLinearProp (m : ℝ) [Fact (1 < m)] : Prop :=
  ∀ (ν : ℝ) (hν : 0 < ν),
    haveI : Fact (0 < cOf ν) := ⟨UnforcedLeray.Short.PartIIIb.Concrete.cOf_pos hν⟩
    ∀ (ξ ξ' : Xmc (cOf ν) m) (r : ℝ),
      kcMer (ξ + ξ') =ᵐ[Cyl.avgμ (cOf ν)] kcMer ξ + kcMer ξ' ∧
      kcMer ((r : ℂ) • ξ) =ᵐ[Cyl.avgμ (cOf ν)] r • kcMer ξ

/-- **Leaf 4** (shared with `kflat/1/1`). `𝔗A` is a.e. strongly measurable on the old region. -/
def FrakTMeasProp (as : ℝ) (χf : ℝ → ℝ) (m : ℝ) [Fact (1 < m)] : Prop :=
  IsSourceCutoffC χf → ∀ (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels) (ν μ ε : ℝ)
    (χo : ℝ → ℝ) (hν : 0 < ν), ν ≤ 1 → 0 ≤ μ → μ < 1 / 4 →
    ∀ (tr : UnforcedLeray.B0140.TrainSol ν (cOf ν))
      (FI : FlatInstData κ ν (cOf ν) m tr) (A : ℝ → Mat3), IsAffElem as A →
      AEStronglyMeasurable (frakT (levelFlat hν FI χo ε) ν μ χf A) (oldMeasure (cOf ν) ν)

theorem frakT_levelFlat_apply {κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels} {ν m : ℝ}
    [Fact (1 < m)] {tr : UnforcedLeray.B0140.TrainSol ν (cOf ν)} (hν : 0 < ν)
    (FI : FlatInstData κ ν (cOf ν) m tr) (χo : ℝ → ℝ) (ε μ : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3)
    (u : ℝ) (x : ℝ × ℝ) :
    haveI : Fact (0 < cOf ν) := ⟨UnforcedLeray.Short.PartIIIb.Concrete.cOf_pos hν⟩
    frakT (levelFlat hν FI χo ε) ν μ χf A (u, x) =
      UnforcedLeray.Short.IIIa.symOuter (NearInst.trainMer tr (u, x))
        (kcMer (xiD FI (μ : ℂ) (Bmat ν μ χf A) u) x) := rfl

theorem symOuter_add_right' (a b b' : Merid) :
    UnforcedLeray.Short.IIIa.symOuter a (b + b') =
      UnforcedLeray.Short.IIIa.symOuter a b + UnforcedLeray.Short.IIIa.symOuter a b' := by
  ext i j
  simp only [UnforcedLeray.Short.IIIa.symOuter, UnforcedLeray.Short.IIIa.embedMerid,
    Matrix.add_apply]
  fin_cases i <;> fin_cases j <;> simp <;> ring

theorem symOuter_smul_right' (a b : Merid) (t : ℝ) :
    UnforcedLeray.Short.IIIa.symOuter a (t • b) = t • UnforcedLeray.Short.IIIa.symOuter a b := by
  ext i j
  simp only [UnforcedLeray.Short.IIIa.symOuter, UnforcedLeray.Short.IIIa.embedMerid,
    Matrix.smul_apply]
  fin_cases i <;> fin_cases j <;> simp <;> ring

/-- **`frakTLinear` from the four leaves.** -/
theorem frakTLinear_of (as : ℝ) (χf : ℝ → ℝ) (m : ℝ) [Fact (1 < m)]
    (hD : DuhIntegrableProp as χf m) (hX : XiDLinearProp m) (hK : KcMerLinearProp m)
    (hM : FrakTMeasProp as χf m) : FrakTLinear as χf m := by
  intro hχ κ ν μ ε χo hν hν1 hμ0 hμ1 tr FI A A' r hA hA'
  have hc : Fact (0 < cOf ν) := ⟨UnforcedLeray.Short.PartIIIb.Concrete.cOf_pos hν⟩
  have hAA' : IsAffElem as (A + A') := by
    have := affIota_mem as ((⟨A, hA⟩ : AffSp as) + ⟨A', hA'⟩)
    exact this
  have hrA : IsAffElem as (r • A) := by
    have := affIota_mem as (r • (⟨A, hA⟩ : AffSp as))
    exact this
  have : SFinite (Cyl.avgμ (cOf ν)) := by unfold Cyl.avgμ; infer_instance
  have hdiff : ∀ (A : ℝ → Mat3), IsAffElem as A → ∀ t, 0 < t →
      DifferentiableAt ℝ (Ay ν χf A) t := fun A hA t ht => ayDiffAt as χf hχ ν A hA t ht
  have hB1 : ∀ t, 0 < t → Bmat ν μ χf (A + A') t = Bmat ν μ χf A t + Bmat ν μ χf A' t :=
    fun t ht => (bmatLinear ν μ χf A A' r t (hdiff A hA t ht) (hdiff A' hA' t ht)).1
  have hB2 : ∀ t, 0 < t → Bmat ν μ χf (r • A) t = r • Bmat ν μ χf A t :=
    fun t ht => (bmatLinear ν μ χf A A' r t (hdiff A hA t ht) (hdiff A' hA' t ht)).2
  have mA := hM hχ κ ν μ ε χo hν hν1 hμ0 hμ1 tr FI A hA
  have mA' := hM hχ κ ν μ ε χo hν hν1 hμ0 hμ1 tr FI A' hA'
  have mAA' := hM hχ κ ν μ ε χo hν hν1 hμ0 hμ1 tr FI _ hAA'
  have mrA := hM hχ κ ν μ ε χo hν hν1 hμ0 hμ1 tr FI _ hrA
  have hI := fun (A : ℝ → Mat3) (hA : IsAffElem as A) (u : ℝ) =>
    hD hχ κ ν μ hν hν1 hμ0 hμ1 tr FI A hA u
  refine ⟨?_, ?_⟩
  · refine ae_prod_eq_of_ae_ae mAA' (mA.add mA') ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_)
    have hxi := (hX κ ν μ hν tr FI (Bmat ν μ χf A) (Bmat ν μ χf A') (Bmat ν μ χf (A + A')) r u
      (hI A hA u) (hI A' hA' u)).1 hB1
    filter_upwards [(hK ν hν (xiD FI (μ : ℂ) (Bmat ν μ χf A) u)
      (xiD FI (μ : ℂ) (Bmat ν μ χf A') u) r).1] with x hx
    show frakT (levelFlat hν FI χo ε) ν μ χf (A + A') (u, x) =
      frakT (levelFlat hν FI χo ε) ν μ χf A (u, x) +
        frakT (levelFlat hν FI χo ε) ν μ χf A' (u, x)
    rw [frakT_levelFlat_apply, frakT_levelFlat_apply, frakT_levelFlat_apply, hxi]
    have hx' : kcMer (xiD FI (μ : ℂ) (Bmat ν μ χf A) u + xiD FI (μ : ℂ) (Bmat ν μ χf A') u) x =
      kcMer (xiD FI (μ : ℂ) (Bmat ν μ χf A) u) x + kcMer (xiD FI (μ : ℂ) (Bmat ν μ χf A') u) x :=
      hx
    rw [hx', symOuter_add_right']
    try rfl
  · refine ae_prod_eq_of_ae_ae mrA (mA.const_smul r) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun u hu => ?_)
    have hxi := (hX κ ν μ hν tr FI (Bmat ν μ χf A) (Bmat ν μ χf A) (Bmat ν μ χf (r • A)) r u
      (hI A hA u) (hI A hA u)).2 hB2
    filter_upwards [(hK ν hν (xiD FI (μ : ℂ) (Bmat ν μ χf A) u)
      (xiD FI (μ : ℂ) (Bmat ν μ χf A) u) r).2] with x hx
    show frakT (levelFlat hν FI χo ε) ν μ χf (r • A) (u, x) =
      r • frakT (levelFlat hν FI χo ε) ν μ χf A (u, x)
    rw [frakT_levelFlat_apply, frakT_levelFlat_apply, hxi]
    have hx' : kcMer ((r : ℂ) • xiD FI (μ : ℂ) (Bmat ν μ χf A) u) x =
      r • kcMer (xiD FI (μ : ℂ) (Bmat ν μ χf A) u) x := hx
    rw [hx', symOuter_smul_right']
    try rfl

end UnforcedLeray.Short.PartIIIb.Concrete
