import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization.Sub
import UnforcedLeray.Short.PartIIIb.NearInst.Masked.Proofs.CellPtH

/-!
# Decomposition of `DensityBox` (source 1675, 1688-1689, 2681-2691, 3916-3921)

Source of record: `the November 2 reference manuscript`.

`DensityBox` (`Sub.lean`): a bounded `S' : H_T → H` that acts on smooth tensor tests by the lifted
kernel formula acts on box tensors by the unmasked kernel `fullOut` (3916-3921, 1675: "the tensor map
means completion from smooth tensors").  The route (a Lipschitz argument, no sequences):

* `FullOutMeas`, `FullOutLip` (1688-1689, 3996-4011 without the mask): on box tensors `fullOut` is
  a.e. strongly measurable and `‖fullOut f - fullOut g‖_{L²(s^{-3/2})} ≤ C ‖tv4 f - tv4 g‖_{L²(s^{-1/2})}`
  (`fullOut` depends on `f` only through `nsSym f`, hence through `tv4 f`: `cartLift` reads
  `nsSym`).  Linear in the tensor; Young and normalized-phase Minkowski as in `FarKernelL2`.
* `RealTestApprox` (1675, `Masked.TensorTestDense` and real parts): a real box tensor in `H_T` is
  approximated by smooth real tensor tests that are themselves box tensors.
* `LiftFullOutTest` (3916-3921, 2681-2691): for such a test `m`, the chart field
  `merC (fullOut m (cellPt p))` lies in `H` and its lift `J_ε` is the lifted kernel field (this
  is where axisymmetry/no-swirl/reality of `W_μ` and the change of variables of `B0223.liftVec`
  enter).

`liftVec` is a linear isometry, hence injective, so `S' m = merC ∘ fullOut m ∘ cellPt` on tests;
then for every test `m`
`‖S'F' - Φ f‖ ≤ ‖S'‖‖F' - F_m‖ + C‖F_m - F'‖`, which is arbitrarily small.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIIb.NearInst.Masked

/-! ## The leaves -/

/-- **Leaf 1: `fullOut` is a.e. strongly measurable on box tensors** (source 3916-3921, 1688-1689;
`sepW` of a bounded measurable band tensor is a measurable function of `(y, τ)`; compose with the
chart maps `chartY`, `chartTau`). -/
def FullOutMeas : Prop :=
  ∀ (R c ν μ : ℝ), 0 < R → 0 < c → 0 < ν → -(1 / 4) < μ → ∀ f : Chart → Ten3, IsBoxTensor f →
    AEStronglyMeasurable (fullOut R c ν μ f) (ageμ c (-3 / 2))

/-- **Leaf 2: `fullOut` is Lipschitz from `H_T` to `H` on box tensors** (source 1688-1689, 3916-3921;
the unmasked version of `FarKernelL2`: the positive majorant `‖∇K_t‖_{L¹} ≤ C t^{-1/2}`, the
dilation integral `∫_0^1 λ^{2μ+1/2}(1-λ²)^{-1/2} dλ < ∞` for `μ > -1/4`, Young and normalized-phase
Minkowski; the lifts multiply both norms by `√πR`; `sepW` is linear in the tensor and `cartLift`
reads only `nsSym`, so only `tv4 f - tv4 g` enters, cf. `nsSym_eq_of_tv4`). -/
def FullOutLip : Prop :=
  ∀ (R c ν μ : ℝ), 0 < R → 0 < c → 0 < ν → -(1 / 4) < μ →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f g : Chart → Ten3, IsBoxTensor f → IsBoxTensor g →
      eLpNorm (fun x => fullOut R c ν μ f x - fullOut R c ν μ g x) 2 (ageμ c (-3 / 2)) ≤
        ENNReal.ofReal C * eLpNorm (fun x => tv4 (f x) - tv4 (g x)) 2 (ageμ c (-1 / 2))

/-- **Leaf 3: approximation by real box tests** (source 1675, 1678: completion from smooth tensors;
`Masked.tensorTestDense` plus real parts: the real part of a test is a test, `tv4` of a real tensor
is real, and taking the real part is 1-Lipschitz in each component; the real tensor with components
`(Re M_rr, Re M_rz, Re M_zz, Re M_φφ)` is smooth with the band support of `M`, hence a box
tensor).  Every `F' ∈ H_T` that is a.e. `tv4 ∘ f ∘ cellPt` for a chart tensor `f` is the `H_T`-limit
of the classes of the tests `tv4 ∘ m` with `m` smooth real and an `IsBoxTensor`. -/
def RealTestApprox : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ (F' : UnforcedLeray.Short.PartIIa.HTSpace c) (f : Chart → Ten3),
    (F' : UnforcedLeray.B0220.Profile → UnforcedLeray.Short.PartIIa.TensorVal)
        =ᵐ[UnforcedLeray.Short.PartIIa.measureHT c] (fun p => tv4 (f (cellPt c p))) →
    ∀ η : ℝ, 0 < η → ∃ m : Chart → Ten3,
      UnforcedLeray.Short.PartIIa.IsTensorTest c (fun p => tv4 (m p)) ∧ IsBoxTensor m ∧
        ∃ hM : MemLp (fun p => tv4 (m p)) 2 (UnforcedLeray.Short.PartIIa.measureHT c),
          ‖F' - hM.toLp _‖ < η

/-- **Leaf 4: the lifted chart field of a box test** (source 3916-3921, 2681-2691, 3586-3626): for
`ν, ε, c > 0`, `P = 2εc`, real `μ > -1/4` and a smooth box tensor test `m`, the chart field
`p ↦ merC (fullOut ε⁻¹ c ν μ m (cellPt c p))` has a representative `G ∈ H` (`W_μ[𝒩_T m]` of an
axisymmetric no-swirl real source is rotation equivariant, without swirl and real, and `P`-periodic
in `τ`, and `s^{-1/2}Re(-W_μ)_{r,z}(chartY, chartTau)` is its meridional chart form), whose lift
`J_ε G = B0223.liftVec` (change of variables `x = z/R`, `J_ε b = (√(2π)ε)⁻¹ a (b_r e_r + b_z e_z)`)
equals `(2π)^{-1/2} · kernelField ν μ ε⁻¹ (cartLift ε⁻¹ c m)`. -/
def LiftFullOutTest : Prop :=
  ∀ (ν ε c P : ℝ) [Fact (0 < P)], 0 < ν → ∀ (hε : 0 < ε) (hc : 0 < c) (hP : P = 2 * ε * c)
    (μ : ℝ), -(1 / 4) < μ → ∀ m : Chart → Ten3,
    UnforcedLeray.Short.PartIIa.IsTensorTest c (fun p => tv4 (m p)) → IsBoxTensor m →
    ∃ G : UnforcedLeray.B0220.HSpace c UnforcedLeray.B0223.MeridC,
      (G : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC)
          =ᵐ[UnforcedLeray.B0220.measureH c] (fun p => merC (fullOut ε⁻¹ c ν μ m (cellPt c p))) ∧
        (UnforcedLeray.B0223.liftVec hε hc hP G :
            UnforcedLeray.B0223.PSpace P → UnforcedLeray.B0223.SpaceC) =ᵐ[volume]
          (((Real.sqrt (2 * Real.pi))⁻¹ : ℝ) : ℂ) • kernelField ν (μ : ℂ) ε⁻¹ (cartLift ε⁻¹ c m)

/-! ## Auxiliary facts -/

/-- A test is `c`-periodic in `q`, so recentring does not change `tv4 ∘ m`. -/
theorem tv4_cellPt_of_test {c : ℝ} {m : Chart → Ten3}
    (hm : UnforcedLeray.Short.PartIIa.IsTensorTest c (fun p => tv4 (m p)))
    (p : UnforcedLeray.B0220.Profile) : tv4 (m (cellPt c p)) = tv4 (m p) := by
  have hper := hm.periodic
  obtain ⟨s, q, η⟩ := p
  unfold cellPt
  by_cases hq : q < c / 2
  · simp [hq]
  · simp only [hq, ite_false]
    have := hper (s, q - c, η)
    simp only [sub_add_cancel] at this
    exact this.symm

/-- The map `cellPt` sends `measureH c` into `ageμ c (-3/2)` up to the factor `c`; a function
a.e. strongly measurable for `ageμ c (-3/2)` composed with `cellPt` is a.e. strongly measurable for
`measureH c`. -/
theorem aesm_comp_cellPtH {c : ℝ} (hCH : CellPtH c) {E : Type*} [NormedAddCommGroup E]
    {g : Chart → E} (hg : AEStronglyMeasurable g (ageμ c (-3 / 2))) (hc : 0 < c) :
    AEStronglyMeasurable (fun p => g (cellPt c p)) (UnforcedLeray.B0220.measureH c) := by
  have h1 : AEStronglyMeasurable g (Measure.map (cellPt c) (UnforcedLeray.B0220.measureH c)) := by
    rw [hCH]
    exact hg.smul_measure _
  exact h1.comp_aemeasurable (measurable_cellPt c).aemeasurable

theorem merC_sub (a b : Merid) : merC a - merC b = merC (a - b) := by
  ext i
  simp [merC]

theorem norm_merC' (b : Merid) : ‖merC b‖ = ‖b‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  simp [merC, Complex.norm_real]

/-- The transport of norms: for box tensors `f, g`,
`‖Φ f - Φ g‖_H ≤ C ‖F_f - F_g‖_{H_T}` (cell versions), with `Φ f = merC ∘ fullOut f ∘ cellPt`. -/
theorem phi_lip {c R ν μ C : ℝ} (hc : 0 < c) (hCH : CellPtH c)
    (hCHT : CellPtHT c) {f g : Chart → Ten3} (hf : IsBoxTensor f) (hg : IsBoxTensor g)
    (hmf : AEStronglyMeasurable (fullOut R c ν μ f) (ageμ c (-3 / 2)))
    (hmg : AEStronglyMeasurable (fullOut R c ν μ g) (ageμ c (-3 / 2)))
    (hlip : eLpNorm (fun x => fullOut R c ν μ f x - fullOut R c ν μ g x) 2 (ageμ c (-3 / 2)) ≤
        ENNReal.ofReal C * eLpNorm (fun x => tv4 (f x) - tv4 (g x)) 2 (ageμ c (-1 / 2))) :
    eLpNorm (fun p => merC (fullOut R c ν μ f (cellPt c p)) - merC (fullOut R c ν μ g (cellPt c p)))
        2 (UnforcedLeray.B0220.measureH c) ≤
      ENNReal.ofReal C * eLpNorm (fun p => tv4 (f (cellPt c p)) - tv4 (g (cellPt c p))) 2
        (UnforcedLeray.Short.PartIIa.measureHT c) := by
  set u : Chart → Merid := fun x => fullOut R c ν μ f x - fullOut R c ν μ g x with hu
  set b : Chart → UnforcedLeray.Short.PartIIa.TensorVal := fun x => tv4 (f x) - tv4 (g x) with hb
  have hmu : AEStronglyMeasurable u (ageμ c (-3 / 2)) := hmf.sub hmg
  have hmb : AEStronglyMeasurable b (ageμ c (-1 / 2)) := by
    have h1 : Measurable b := by
      have h2 : ∀ h : Chart → Ten3, Measurable h →
          Measurable fun x => tv4 (h x) := fun h hh => by
        have := tv4L.continuous.measurable.comp hh
        exact this
      exact (h2 f hf.measurable).sub (h2 g hg.measurable)
    exact h1.aestronglyMeasurable
  have hL : eLpNorm (fun p => merC (fullOut R c ν μ f (cellPt c p)) -
        merC (fullOut R c ν μ g (cellPt c p))) 2 (UnforcedLeray.B0220.measureH c) =
      eLpNorm (fun p => u (cellPt c p)) 2 (UnforcedLeray.B0220.measureH c) := by
    refine eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun p => ?_)
    rw [merC_sub, norm_merC']
  have hmap1 : Measure.map (cellPt c) (UnforcedLeray.B0220.measureH c) =
      ENNReal.ofReal c • ageμ c (-3 / 2) := hCH
  have hmap2 : Measure.map (cellPt c) (UnforcedLeray.Short.PartIIa.measureHT c) =
      ENNReal.ofReal c • ageμ c (-1 / 2) := hCHT
  have hA : eLpNorm (fun p => u (cellPt c p)) 2 (UnforcedLeray.B0220.measureH c) =
      ENNReal.ofReal c ^ (1 / (2 : ℝ≥0∞).toReal) * eLpNorm u 2 (ageμ c (-3 / 2)) := by
    have h1 := eLpNorm_map_measure (p := 2) (g := u) (μ := UnforcedLeray.B0220.measureH c)
      (by rw [hmap1]; exact hmu.smul_measure _) (measurable_cellPt c).aemeasurable
    rw [← Function.comp_def u (cellPt c), ← h1, hmap1,
      eLpNorm_smul_measure_of_ne_top (by norm_num)]
    simp [smul_eq_mul]
  have hB : eLpNorm (fun p => b (cellPt c p)) 2 (UnforcedLeray.Short.PartIIa.measureHT c) =
      ENNReal.ofReal c ^ (1 / (2 : ℝ≥0∞).toReal) * eLpNorm b 2 (ageμ c (-1 / 2)) := by
    have h1 := eLpNorm_map_measure (p := 2) (g := b)
      (μ := UnforcedLeray.Short.PartIIa.measureHT c)
      (by rw [hmap2]; exact hmb.smul_measure _) (measurable_cellPt c).aemeasurable
    rw [← Function.comp_def b (cellPt c), ← h1, hmap2,
      eLpNorm_smul_measure_of_ne_top (by norm_num)]
    simp [smul_eq_mul]
  rw [hL, hA]
  show _ ≤ ENNReal.ofReal C * eLpNorm (fun p => b (cellPt c p)) 2 _
  rw [hB, mul_left_comm]
  exact mul_le_mul' le_rfl hlip

theorem continuous_merC' : Continuous merC := by
  unfold merC
  exact (PiLp.continuous_toLp 2 _).comp
    (continuous_pi fun i => Complex.continuous_ofReal.comp (EuclideanSpace.proj i).continuous)

/-! ## The assembly -/

/-- **`DensityBox` from the four leaves.**  For a box tensor `f` and `F' ∈ H_T` representing
`tv4 ∘ f ∘ cellPt`: for every real box test `m` (`RealTestApprox`) close to `F'`, `S'` of the class
`F_m` of `tv4 ∘ m` is `merC ∘ fullOut m ∘ cellPt` (hypothesis on tests, `LiftFullOutTest`,
injectivity of the isometry `liftVec`), and `FullOutLip` with the transports `CellPtH`, `CellPtHT`
gives `‖S'F' - Φ f‖ ≤ (‖S'‖ + C)η`; `η` is arbitrary. -/
theorem densityBox_of (h1 : FullOutMeas) (h2 : FullOutLip) (h3 : RealTestApprox)
    (h4 : LiftFullOutTest) : DensityBox := by
  intro ν ε c P _ hν hε hc hP μ hμ S' hyp f hf F' hF'
  obtain ⟨hCHT, -, hCH⟩ := UnforcedLeray.Short.PartIIIb.NearInst.Delta.cellPtChangeAll c hc
  have hR : 0 < ε⁻¹ := inv_pos.2 hε
  obtain ⟨C, hC0, hCl⟩ := h2 ε⁻¹ c ν μ hR hc hν hμ
  have hmeas : ∀ g : Chart → Ten3, IsBoxTensor g →
      AEStronglyMeasurable (fun p => merC (fullOut ε⁻¹ c ν μ g (cellPt c p)))
        (UnforcedLeray.B0220.measureH c) := by
    intro g hg
    have := aesm_comp_cellPtH hCH (h1 ε⁻¹ c ν μ hR hc hν hμ g hg) hc
    exact continuous_merC'.comp_aestronglyMeasurable this
  set u : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC := ⇑(S' F') with hu
  set v : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC :=
    fun p => merC (fullOut ε⁻¹ c ν μ f (cellPt c p)) with hv
  have key : ∀ η : ℝ, 0 < η →
      eLpNorm (fun p => u p - v p) 2 (UnforcedLeray.B0220.measureH c) ≤
        ENNReal.ofReal ((‖S'‖ + C) * η) := by
    intro η hη
    obtain ⟨m, hmT, hmB, hM, hlt⟩ := h3 c hc F' f hF' η hη
    set Fm : UnforcedLeray.Short.PartIIa.HTSpace c := hM.toLp _ with hFm
    have hFmae : (Fm : UnforcedLeray.B0220.Profile → UnforcedLeray.Short.PartIIa.TensorVal)
        =ᵐ[UnforcedLeray.Short.PartIIa.measureHT c] fun p => tv4 (m p) := hM.coeFn_toLp
    obtain ⟨G, hG1, hG2⟩ := h4 ν ε c P hν hε hc hP μ hμ m hmT hmB
    have hSm : S' Fm = G := by
      apply (UnforcedLeray.B0223.liftVec hε hc hP).injective
      apply Lp.ext
      exact (hyp m hmT Fm hFmae).trans hG2.symm
    have hSmae : (S' Fm : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC)
        =ᵐ[UnforcedLeray.B0220.measureH c] fun p => merC (fullOut ε⁻¹ c ν μ m (cellPt c p)) := by
      rw [hSm]; exact hG1
    have h6 : S' (F' - Fm) = S' F' - S' Fm := map_sub S' F' Fm
    have hsub : (fun p => u p - v p) =ᵐ[UnforcedLeray.B0220.measureH c]
        fun p => (S' (F' - Fm) : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC) p +
          (merC (fullOut ε⁻¹ c ν μ m (cellPt c p)) - merC (fullOut ε⁻¹ c ν μ f (cellPt c p))) := by
      filter_upwards [hSmae, Lp.coeFn_sub (S' F') (S' Fm)] with p hp hs
      rw [h6, hs, Pi.sub_apply, hp]
      simp only [hu, hv]
      abel
    have hmm := hmeas m hmB
    have hmf := hmeas f hf
    have hba : AEStronglyMeasurable
        (fun p => merC (fullOut ε⁻¹ c ν μ m (cellPt c p)) -
          merC (fullOut ε⁻¹ c ν μ f (cellPt c p))) (UnforcedLeray.B0220.measureH c) :=
      hmm.sub hmf
    have hstep := eLpNorm_add_le (p := 2) (Lp.aestronglyMeasurable (S' (F' - Fm))) hba
      (by norm_num)
    rw [eLpNorm_congr_ae hsub]
    refine le_trans hstep ?_
    -- first term
    have ha : eLpNorm (S' (F' - Fm) : UnforcedLeray.B0220.Profile → UnforcedLeray.B0223.MeridC)
        2 (UnforcedLeray.B0220.measureH c) ≤ ENNReal.ofReal (‖S'‖ * η) := by
      rw [← Lp.enorm_def, ← ofReal_norm]
      apply ENNReal.ofReal_le_ofReal
      calc ‖S' (F' - Fm)‖ ≤ ‖S'‖ * ‖F' - Fm‖ := S'.le_opNorm _
        _ ≤ ‖S'‖ * η := mul_le_mul_of_nonneg_left hlt.le (norm_nonneg _)
    -- second term
    have hb := phi_lip (R := ε⁻¹) (ν := ν) (μ := μ) (C := C) hc hCH hCHT hmB hf
      (h1 ε⁻¹ c ν μ hR hc hν hμ m hmB) (h1 ε⁻¹ c ν μ hR hc hν hμ f hf) (hCl m f hmB hf)
    have hc2 : eLpNorm (fun p => tv4 (m (cellPt c p)) - tv4 (f (cellPt c p))) 2
        (UnforcedLeray.Short.PartIIa.measureHT c) ≤ ENNReal.ofReal η := by
      have : (fun p => tv4 (m (cellPt c p)) - tv4 (f (cellPt c p))) =ᵐ[
          UnforcedLeray.Short.PartIIa.measureHT c]
          (((Fm - F' : UnforcedLeray.Short.PartIIa.HTSpace c)) :
            UnforcedLeray.B0220.Profile → UnforcedLeray.Short.PartIIa.TensorVal) := by
        filter_upwards [hFmae, hF', Lp.coeFn_sub Fm F'] with p h1' h2' h3'
        rw [h3', Pi.sub_apply, h1', h2', tv4_cellPt_of_test hmT]
      rw [eLpNorm_congr_ae this, ← Lp.enorm_def, ← ofReal_norm, norm_sub_rev]
      exact ENNReal.ofReal_le_ofReal hlt.le
    have hb' : eLpNorm (fun p => merC (fullOut ε⁻¹ c ν μ m (cellPt c p)) -
          merC (fullOut ε⁻¹ c ν μ f (cellPt c p))) 2 (UnforcedLeray.B0220.measureH c) ≤
        ENNReal.ofReal C * ENNReal.ofReal η :=
      hb.trans (mul_le_mul' le_rfl hc2)
    calc _ ≤ ENNReal.ofReal (‖S'‖ * η) + ENNReal.ofReal C * ENNReal.ofReal η := add_le_add ha hb'
      _ = ENNReal.ofReal ((‖S'‖ + C) * η) := by
        rw [← ENNReal.ofReal_mul hC0, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring
  -- conclude
  have hmv : AEStronglyMeasurable (fun p => u p - v p) (UnforcedLeray.B0220.measureH c) :=
    (Lp.aestronglyMeasurable (S' F')).sub (hmeas f hf)
  have hz : eLpNorm (fun p => u p - v p) 2 (UnforcedLeray.B0220.measureH c) = 0 := by
    refine le_antisymm ?_ zero_le
    refine ENNReal.le_of_forall_pos_le_add fun e he _ => ?_
    have hK : (0 : ℝ) < ‖S'‖ + C + 1 := by positivity
    have := key ((e : ℝ) / (‖S'‖ + C + 1)) (by positivity)
    refine this.trans ?_
    rw [zero_add]
    have : (‖S'‖ + C) * ((e : ℝ) / (‖S'‖ + C + 1)) ≤ e := by
      rw [← mul_div_assoc, div_le_iff₀ hK]
      have : (0 : ℝ) ≤ e := e.2
      nlinarith [norm_nonneg S']
    calc ENNReal.ofReal _ ≤ ENNReal.ofReal e := ENNReal.ofReal_le_ofReal this
      _ = e := ENNReal.ofReal_coe_nnreal
  have h0 := (eLpNorm_eq_zero_iff hmv (by norm_num)).1 hz
  filter_upwards [h0] with p hp
  have : u p - v p = 0 := hp
  exact sub_eq_zero.1 this

end UnforcedLeray.Short.PartIIIb.NearInst.Masked.Realization
