import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.FlatPin
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.Levels
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Azimuthal
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.Linear.Helpers
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.XmtCongr
import UnforcedLeray.Short.PartI.TrainClass

/-!
# The pinned fixed-space flat return `𝒦^flat = 𝓛𝔗` at the levels (source 4761-4806, 4917-4937)

Source of record: `the November 2 reference manuscript` (73 pages).

Part (c) of `ORG:return-concrete/instance-3/affine-source`.  `𝒦^flat_{μ,ν} = 𝓛_{μ,ν}𝔗_{μ,ν}`
(source 4804-4806), `𝔗_{μ,ν}A` the complete flat stress of the zero-entrance forced column with
Gaussian age force `f_{B_{μ,ν}[A]}` (4761-4763, `frakT`), `𝓛` the old-thin-to-young-jet map
(4764-4796, `Lpt`).  The pin is `∃ Kf : 𝒜 →L 𝒜, ∀ A, ι(Kf A) = KflatFun (D.flat n) … (ιA)`
(hypothesis `hKf` of `concreteBase_isSourceLPinned`).

## `𝓛` on old thin tensors (proved here from the receiver-level facts)

For an old thin tensor `M` with finite `N₀` (`OldThinFinite`), `𝓛M ∈ 𝒜` (source 4797-4803:
`C^6` from `XmtSmooth`, trace free from `XmtSolenoidal`, no mixed azimuthal entry from
`XmtReflect`, finite `𝒜` norm from `source-class:ambient-L` = `SourceLAmbient`), with
`‖𝓛M‖_𝒜 ≤ C ε³ N₀(M)` (4924-4928); `𝓛` is linear on such tensors (`XmtLinear`) and sees only
the a.e. class on the old region (`XmtCongr`): `lpt_isAffElem_of`, `affNorm_lpt_le_of`.

`XmtSmooth` (`PartIII-b:C/srcL/6`), `XmtLinear` (`/8`) and `SourceLAmbient` (`/9`) are accepted,
`XmtSolenoidal` is `PartIII-b:C/srcL/7`; the first three are hypotheses because their files
import `Concrete/SourceL/Ambient/SigmaL1/Pointwise.lean`, whose `Concrete.frob_smul` clashes with
that of `Concrete/AffineEnvelope.lean` in the closure of `Concrete/ReturnInst.lean`.

## Leaves on `𝔗` at the actual flat setting (tasks)

For the actual flat setting `levelFlat hν FI χo ε` (`FlatPin.lean`) of a train at `c = ν⁻²`:

* `FrakTOldFinite` : `𝔗A` is an old thin tensor with finite `N₀` for `A ∈ 𝒜` (source 4605-4612,
  4637-4640, 4824-4827);
* `FrakTLinear` : `A ↦ 𝔗A` is linear a.e. on the old region (source 4605-4612: `g_B` is linear in
  `B`, `B_{μ,ν}[A]` in `A`, the Duhamel integral and the readout `v ⊗ K_cξ + K_cξ ⊗ v` in `ξ`);
* `FrakTN0Bound` : `N₀(𝔗A) ≤ C‖A‖_𝒜` at each regime (source 4637-4640 with
  `‖B_{μ,ν}[A]‖_{𝓑_{a_s}} ≤ C_K‖A‖_𝒜`, 4759-4760; earlier-old part 4855-4857).

`FrakTOldFinite` and `FrakTN0Bound` are the absolute old moment `flat-return:all-moments`
(4637-4640), whose proof (4677-4694) uses the full forward train estimate `prop:short-full-clock`
(2836-2860, "for all sufficiently small `ν`") and the later-age estimates (4432-4458, 3242-3289) of
the actual train with `m > 8` (2826, 4350).  They are therefore stated for `m > 8`, `ν ≤ ν₀` with some
`ν₀ > 0`, and trains in the source's BUC class (`PartI.IsBUCTrain`, source 270-288); the pin uses
them only at the large levels (`ν_n → 0`, `retNu_tendsto`).

## Proved here

`exists_kflatOp_of` (one regime, any flat setting with the three properties) and
`SeqData.eventually_exists_KflatOp` (all large levels, `z ∈ [-1,1]`, under the pin
`SeqData.IsActualFlat`, for `m > 8` and BUC trains at the large levels).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open UnforcedLeray.Short.PartIIIb.Concrete.XmtRefl

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

/-! ## 1. `𝓛` on old thin tensors -/

section Lpt

variable {c ν ε μ : ℝ} {χo χy : ℝ → ℝ}

/-- The receiver path `s ↦ (ε⁻¹/√s, 0, 0)` is `C^6` on `(0,∞)`. -/
theorem kfl_recvPt_contDiffOn (ε : ℝ) :
    ContDiffOn ℝ 6 (fun s : ℝ => (![ε⁻¹ / Real.sqrt s, 0, 0] : Vec3)) (Ioi 0) := by
  have hfun : (fun s : ℝ => (![ε⁻¹ / Real.sqrt s, 0, 0] : Vec3)) =
      fun s : ℝ => (ε⁻¹ / Real.sqrt s) • (![1, 0, 0] : Vec3) := by
    funext s
    ext k
    fin_cases k <;> simp
  rw [hfun]
  have hsq : ContDiffOn ℝ 6 (fun s : ℝ => Real.sqrt s) (Ioi 0) :=
    contDiffOn_id.sqrt (fun x hx => (Set.mem_Ioi.1 hx).ne')
  exact ContDiffOn.smul (contDiffOn_const.div hsq
    (fun x hx => (Real.sqrt_pos.2 (Set.mem_Ioi.1 hx)).ne')) contDiffOn_const

/-- `𝓛M` is `C^6` on `(0,∞)` (source 4797-4800). -/
theorem lpt_contDiffOn_of (hS : XmtSmooth) (h : LHyp c ν ε μ χo χy) {M : Chart → Mat3}
    (hM : OldThinFinite c ν M) : ContDiffOn ℝ 6 (Lpt c ν ε μ χo χy M) (Ioi 0) := by
  have hX : ContDiff ℝ 7 (Xmt c ν ε μ χo χy M) := hS c ν ε μ χo χy h M hM
  have hD : ContDiff ℝ 6 (fderiv ℝ (Xmt c ν ε μ χo χy M)) := hX.fderiv_right (by norm_num)
  have hDy : ContDiffOn ℝ 6
      (fun s : ℝ => fderiv ℝ (Xmt c ν ε μ χo χy M) ![ε⁻¹ / Real.sqrt s, 0, 0]) (Ioi 0) :=
    hD.contDiffOn.comp (kfl_recvPt_contDiffOn ε) (mapsTo_univ _ _)
  have hcol : ∀ j : Fin 3, ContDiffOn ℝ 6
      (fun s : ℝ => fderiv ℝ (Xmt c ν ε μ χo χy M) ![ε⁻¹ / Real.sqrt s, 0, 0]
        (Pi.single j 1)) (Ioi 0) :=
    fun j => hDy.clm_apply contDiffOn_const
  have hmat : ContDiffOn ℝ 6
      (fun s : ℝ => (fun i j => fderiv ℝ (Xmt c ν ε μ χo χy M)
        ![ε⁻¹ / Real.sqrt s, 0, 0] (Pi.single j 1) i : Mat3)) (Ioi 0) :=
    contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j => contDiffOn_pi.1 (hcol j) i
  refine hmat.congr ?_
  intro s hs
  show Lpt c ν ε μ χo χy M s = _
  unfold Lpt
  rw [if_pos (Set.mem_Ioi.1 hs)]

/-- The entries of `𝓛M(s)`, `s > 0`, are those of `D_yX^mt` at the receiver. -/
theorem lpt_apply_of_pos (M : Chart → Mat3) {s : ℝ} (hs : 0 < s) (i j : Fin 3) :
    Lpt c ν ε μ χo χy M s i j =
      fderiv ℝ (Xmt c ν ε μ χo χy M) ![ε⁻¹ / Real.sqrt s, 0, 0] (Pi.single j 1) i := by
  unfold Lpt
  rw [if_pos hs]

/-- `𝓛M` is trace free (source 4798: `tr D_yX = div X = 0`). -/
theorem lpt_traceFree_of (hSol : XmtSolenoidal) (h : LHyp c ν ε μ χo χy) {M : Chart → Mat3}
    (hM : OldThinFinite c ν M) {s : ℝ} (hs : 0 < s) :
    Lpt c ν ε μ χo χy M s 0 0 + Lpt c ν ε μ χo χy M s 1 1 + Lpt c ν ε μ χo χy M s 2 2 = 0 := by
  have h0 := hSol c ν ε μ χo χy h M hM ![ε⁻¹ / Real.sqrt s, 0, 0]
  rw [Fin.sum_univ_three] at h0
  rw [lpt_apply_of_pos M hs, lpt_apply_of_pos M hs, lpt_apply_of_pos M hs]
  exact h0

/-- `𝓛M` has no entry with exactly one azimuthal index (source 4798-4799). -/
theorem lpt_azimuthal (M : Chart → Mat3) {s : ℝ} (hs : 0 < s) :
    Lpt c ν ε μ χo χy M s 0 1 = 0 ∧ Lpt c ν ε μ χo χy M s 1 0 = 0 ∧
      Lpt c ν ε μ χo χy M s 1 2 = 0 ∧ Lpt c ν ε μ χo χy M s 2 1 = 0 := by
  have hX : ∀ y : Vec3, Xmt c ν ε μ χo χy M (reflY y) = reflY (Xmt c ν ε μ χo χy M y) :=
    fun y => xmtReflect c ν ε μ χo χy M y
  have hy0 : reflY (![ε⁻¹ / Real.sqrt s, 0, 0] : Vec3) = ![ε⁻¹ / Real.sqrt s, 0, 0] := by
    funext i
    fin_cases i <;> simp [reflY]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [lpt_apply_of_pos M hs]
    exact azimuthal_entry_zero _ hX _ hy0 0 1 (by rw [sg_zero, sg_one]; norm_num)
  · rw [lpt_apply_of_pos M hs]
    exact azimuthal_entry_zero _ hX _ hy0 1 0 (by rw [sg_one, sg_zero]; norm_num)
  · rw [lpt_apply_of_pos M hs]
    exact azimuthal_entry_zero _ hX _ hy0 1 2 (by rw [sg_one, sg_two]; norm_num)
  · rw [lpt_apply_of_pos M hs]
    exact azimuthal_entry_zero _ hX _ hy0 2 1 (by rw [sg_two, sg_one]; norm_num)

/-- **`𝓛M ∈ 𝒜`** for an old thin tensor with finite `N₀` (source 4797-4803, 4924-4928). -/
theorem lpt_isAffElem_of (hS : XmtSmooth) (hSol : XmtSolenoidal) {as : ℝ} (has : 0 < as)
    (hAmb : SourceLAmbient as {μ} χo χy) (h : LHyp c ν ε μ χo χy) {M : Chart → Mat3}
    (hM : OldThinFinite c ν M) : IsAffElem as (Lpt c ν ε μ χo χy M) := by
  have hK : ({μ} : Set ℝ) ⊆ Ioo 0 (1 / 4) := by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨h.mu_pos, h.mu_lt⟩
  obtain ⟨C, hC⟩ := hAmb has isCompact_singleton hK
  refine ⟨lpt_contDiffOn_of hS h hM, fun s hs => lpt_traceFree_of hSol h hM hs,
    fun s hs => lpt_azimuthal M hs, fun s hs => Lpt_of_nonpos c ν ε μ χo χy M hs,
    ⟨C * ε ^ 3 * oldN0 c ν M, ?_⟩⟩
  rintro _ ⟨s, hs, rfl⟩
  exact hC c ν ε μ h (Set.mem_singleton μ) M hM s hs

/-- **`source-class:ambient-L`** in norm form (source 4924-4928): `‖𝓛M‖_𝒜 ≤ C ε³ N₀(M)`. -/
theorem affNorm_lpt_le_of {as : ℝ} (has : 0 < as) (hAmb : SourceLAmbient as {μ} χo χy)
    (hμ : 0 < μ) (hμ' : μ < 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c ν ε : ℝ), LHyp c ν ε μ χo χy → ∀ M : Chart → Mat3,
      OldThinFinite c ν M → affNorm as (Lpt c ν ε μ χo χy M) ≤ C * ε ^ 3 * oldN0 c ν M := by
  have hK : ({μ} : Set ℝ) ⊆ Ioo 0 (1 / 4) := by
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨hμ, hμ'⟩
  obtain ⟨C, hC⟩ := hAmb has isCompact_singleton hK
  refine ⟨|C|, abs_nonneg C, fun c ν ε h M hM => ?_⟩
  have hN0 := oldN0_nonneg c ν h.nu_pos M
  have he : 0 ≤ ε ^ 3 := pow_nonneg h.eps_pos.le 3
  unfold affNorm
  refine csSup_le ⟨_, ⟨1, Set.mem_Ioi.2 one_pos, rfl⟩⟩ ?_
  rintro _ ⟨s, hs, rfl⟩
  refine (hC c ν ε μ h (Set.mem_singleton μ) M hM s hs).trans ?_
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C) he) hN0

end Lpt

/-! ## 2. The flat return at one regime -/

/-- **The `𝒦^flat` pin at one regime** (source 4804-4806, 4917-4937): for any flat setting whose
`𝔗` has finite `N₀`, is linear a.e. on the old region and has `N₀(𝔗(ιA)) ≤ C_b‖A‖`, the map
`A ↦ 𝓛(𝔗(ιA))` is a continuous linear map `𝒜 → 𝒜`. -/
theorem exists_kflatOp_of {as ν ε μ : ℝ} {χo χy χf : ℝ → ℝ} (S : ConcreteYF.FlatSetting)
    (hS : XmtSmooth) (hSol : XmtSolenoidal) (hLin : XmtLinear) (has : 0 < as)
    (hAmb : SourceLAmbient as {μ} χo χy) (h : LHyp (cOf ν) ν ε μ χo χy)
    (hfin : ∀ A : AffSp as, OldThinFinite (cOf ν) ν (frakT S ν μ χf (affIota as A)))
    (hadd : ∀ A A' : AffSp as, frakT S ν μ χf (affIota as (A + A')) =ᵐ[oldMeasure (cOf ν) ν]
      frakT S ν μ χf (affIota as A) + frakT S ν μ χf (affIota as A'))
    (hsmul : ∀ (r : ℝ) (A : AffSp as), frakT S ν μ χf (affIota as (r • A)) =ᵐ[oldMeasure (cOf ν) ν]
      r • frakT S ν μ χf (affIota as A))
    (Cb : ℝ) (hbd : ∀ A : AffSp as, oldN0 (cOf ν) ν (frakT S ν μ χf (affIota as A)) ≤ Cb * ‖A‖) :
    ∃ Kf : AffSp as →L[ℝ] AffSp as, ∀ A,
      affIota as (Kf A) = KflatFun S (cOf ν) ν ε μ χo χy χf (affIota as A) := by
  set c := cOf ν with hc
  have hdiff : ∀ A : AffSp as, ∀ y,
      DifferentiableAt ℝ (Xmt c ν ε μ χo χy (frakT S ν μ χf (affIota as A))) y := fun A y =>
    ((hS c ν ε μ χo χy h _ (hfin A)).differentiable (by norm_num)).differentiableAt
  have hmem : ∀ A : AffSp as, IsAffElem as (KflatFun S c ν ε μ χo χy χf (affIota as A)) :=
    fun A => lpt_isAffElem_of hS hSol has hAmb h (hfin A)
  obtain ⟨C, hC0, hC⟩ := affNorm_lpt_le_of has hAmb h.mu_pos h.mu_lt
  let f : AffSp as →ₗ[ℝ] AffSp as :=
    { toFun := fun A => ⟨KflatFun S c ν ε μ χo χy χf (affIota as A), hmem A⟩
      map_add' := fun A A' => by
        apply Subtype.ext
        show KflatFun S c ν ε μ χo χy χf (affIota as (A + A')) =
          KflatFun S c ν ε μ χo χy χf (affIota as A) + KflatFun S c ν ε μ χo χy χf (affIota as A')
        have hE : Xmt c ν ε μ χo χy (frakT S ν μ χf (affIota as (A + A'))) =
            Xmt c ν ε μ χo χy (frakT S ν μ χf (affIota as A)) +
              Xmt c ν ε μ χo χy (frakT S ν μ χf (affIota as A')) :=
          (xmtCongr c ν ε μ χo χy h.chiO h.nu_pos _ _ (hadd A A')).trans
            (hLin c ν ε μ χo χy h _ _ (hfin A) (hfin A') 1).1
        funext s
        exact Lpt_add_of (hdiff A) (hdiff A') hE s
      map_smul' := fun r A => by
        apply Subtype.ext
        show KflatFun S c ν ε μ χo χy χf (affIota as (r • A)) =
          r • KflatFun S c ν ε μ χo χy χf (affIota as A)
        have hE : Xmt c ν ε μ χo χy (frakT S ν μ χf (affIota as (r • A))) =
            r • Xmt c ν ε μ χo χy (frakT S ν μ χf (affIota as A)) :=
          (xmtCongr c ν ε μ χo χy h.chiO h.nu_pos _ _ (hsmul r A)).trans
            (hLin c ν ε μ χo χy h _ _ (hfin A) (hfin A) r).2
        funext s
        exact Lpt_smul_of r (hdiff A) hE s }
  refine ⟨f.mkContinuous (C * ε ^ 3 * Cb) fun A => ?_, fun A => rfl⟩
  show ‖(⟨KflatFun S c ν ε μ χo χy χf (affIota as A), hmem A⟩ : AffSp as)‖ ≤ C * ε ^ 3 * Cb * ‖A‖
  rw [AffSp.norm_def]
  have he : 0 ≤ C * ε ^ 3 := mul_nonneg hC0 (pow_nonneg h.eps_pos.le 3)
  calc affNorm as (KflatFun S c ν ε μ χo χy χf (affIota as A))
      ≤ C * ε ^ 3 * oldN0 c ν (frakT S ν μ χf (affIota as A)) := hC c ν ε h _ (hfin A)
    _ ≤ C * ε ^ 3 * (Cb * ‖A‖) := mul_le_mul_of_nonneg_left (hbd A) he
    _ = C * ε ^ 3 * Cb * ‖A‖ := by ring

/-! ## 3. The leaves on `𝔗` at the actual flat setting -/

/-- **`𝔗A` is an old thin tensor with finite `N₀`** (source 4605-4612, 4637-4640, 4677-4694,
4848-4857): for `m > 8` (2826, 4350) there is `ν₀ > 0` such that at the actual flat setting of a BUC train
(270-288) at `c = ν⁻²`, `0 < ν ≤ ν₀`, `0 ≤ μ < 1/4`, for `A ∈ 𝒜` the stress
`𝔗_{μ,ν}A = M_{B_{μ,ν}[A]}` is a.e. strongly measurable on the old region `u > 1.2/ν` with
`u^{-3/2}|𝔗A|` integrable there (`χ_f` the source cutoff; `𝔗` does not depend on `χ_o, ε`).  The
source proves the old moment bound only for all sufficiently small `ν` (2836-2860, 4432-4458). -/
def FrakTOldFinite (as : ℝ) (χf : ℝ → ℝ) (m : ℝ) [Fact (1 < m)] : Prop :=
  IsSourceCutoffC χf → 8 < m → ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels) (ν μ ε : ℝ)
    (χo : ℝ → ℝ) (hν : 0 < ν), ν ≤ ν₀ → 0 ≤ μ → μ < 1 / 4 →
    ∀ (tr : UnforcedLeray.B0140.TrainSol ν (cOf ν)), UnforcedLeray.Short.PartI.IsBUCTrain tr →
    ∀ (FI : FlatSettingInst.FlatInstData κ ν (cOf ν) m tr) (A : ℝ → Mat3), IsAffElem as A →
      OldThinFinite (cOf ν) ν (frakT (levelFlat hν FI χo ε) ν μ χf A)

/-- **`A ↦ 𝔗A` is linear a.e. on the old region** (source 4605-4612, 4985): `g_B` is linear in `B`,
`B_{μ,ν}[A]` is linear in `A ∈ 𝒜` at every `t > 0`, the Duhamel integral
`ξ_B(s) = s^{-μ}∫₀^s t^μ 𝒰(s,t)g_B(t) dt` converges and is linear, and the readout
`v ⊗ K_cξ + K_cξ ⊗ v` is linear in `ξ` (`K_cξ` is read through its Lebesgue value, linear a.e.). -/
def FrakTLinear (as : ℝ) (χf : ℝ → ℝ) (m : ℝ) [Fact (1 < m)] : Prop :=
  IsSourceCutoffC χf → ∀ (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels) (ν μ ε : ℝ)
    (χo : ℝ → ℝ) (hν : 0 < ν), ν ≤ 1 → 0 ≤ μ → μ < 1 / 4 →
    ∀ (tr : UnforcedLeray.B0140.TrainSol ν (cOf ν))
      (FI : FlatSettingInst.FlatInstData κ ν (cOf ν) m tr) (A A' : ℝ → Mat3) (r : ℝ),
      IsAffElem as A → IsAffElem as A' →
      frakT (levelFlat hν FI χo ε) ν μ χf (A + A') =ᵐ[oldMeasure (cOf ν) ν]
          frakT (levelFlat hν FI χo ε) ν μ χf A + frakT (levelFlat hν FI χo ε) ν μ χf A' ∧
        frakT (levelFlat hν FI χo ε) ν μ χf (r • A) =ᵐ[oldMeasure (cOf ν) ν]
          r • frakT (levelFlat hν FI χo ε) ν μ χf A

/-- **`N₀(𝔗A) ≤ C‖A‖_𝒜`** at each regime (source 4637-4640 `flat-return:all-moments`, with
`‖B_{μ,ν}[A]‖_{𝓑_{a_s}} ≤ C_K‖A‖_𝒜`, 4759-4760; the earlier-old part `1.2/ν < u < ν^{-3/2}` has
the bound `𝒜_ν P_ν e^{-γ'/√ν}‖B‖`, 4855-4857; `N₀(M) = ∫_{1.2/ν}^∞ u^{-3/2}(1/c)∫_cell|M|`). The
constant may depend on the regime.  As `FrakTOldFinite`: `m > 8`, `ν ≤ ν₀`, BUC trains
(2826, 2836-2860, 270-288). -/
def FrakTN0Bound (as : ℝ) (χf : ℝ → ℝ) (m : ℝ) [Fact (1 < m)] : Prop :=
  IsSourceCutoffC χf → 8 < m → ∃ ν₀ : ℝ, 0 < ν₀ ∧
    ∀ (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels) (ν μ ε : ℝ)
    (χo : ℝ → ℝ) (hν : 0 < ν), ν ≤ ν₀ → 0 ≤ μ → μ < 1 / 4 →
    ∀ (tr : UnforcedLeray.B0140.TrainSol ν (cOf ν)), UnforcedLeray.Short.PartI.IsBUCTrain tr →
    ∀ (FI : FlatSettingInst.FlatInstData κ ν (cOf ν) m tr),
      ∃ C : ℝ, ∀ A : ℝ → Mat3, IsAffElem as A →
        oldN0 (cOf ν) ν (frakT (levelFlat hν FI χo ε) ν μ χf A) ≤ C * affNorm as A

/-! ## 4. The pin along the sequence -/

/-- **The `𝒦^flat` pin at the levels** (source 4804-4806 at 5926-5950): if the flat setting of every
large level is the actual one (`SeqData.IsActualFlat`) and the train of every large level is in the
source's BUC class (270-288), then for `m > 8`, large `n` and `z ∈ [-1,1]`,
`∃ Kf : 𝒜 →L 𝒜, ∀ A, ι(Kf A) = KflatFun (D.flat n) … (ιA)`, the hypothesis `hKf` of
`concreteBase_isSourceLPinned` at `L = D.level n`, `μ = D.mu n z`.  The leaves `FrakTOldFinite`,
`FrakTN0Bound` hold below some `ν₀`, reached since `ν_n → 0` (`retNu_tendsto`). -/
theorem SeqData.eventually_exists_KflatOp (D : SeqData)
    (κ : UnforcedLeray.Short.IIIa.PlanarFrameKernels) (m : ℝ) [Fact (1 < m)]
    (hω : D.Pl.eigenvalue.im ≠ 0) (hγ : 0 < D.Pl.eigenvalue.re) (hσ0 : 0 < D.σ₀)
    (hσ1 : D.σ₀ < 1 / 4) (hχy : IsStreamCutoff D.K.χy) (hχf : IsSourceCutoffC D.K.χf)
    (has : 0 < D.K.as) (hflat : ∀ᶠ n : ℕ in atTop, D.IsActualFlat κ m n)
    (hS : XmtSmooth) (hSol : XmtSolenoidal) (hLin : XmtLinear)
    (hAmb : ∀ μ : ℝ, SourceLAmbient D.K.as {μ} D.K.χo D.K.χy)
    (h1 : FrakTOldFinite D.K.as D.K.χf m) (h2 : FrakTLinear D.K.as D.K.χf m)
    (h3 : FrakTN0Bound D.K.as D.K.χf m) (hm8 : 8 < m)
    (hbuc : ∀ᶠ n : ℕ in atTop, UnforcedLeray.Short.PartI.IsBUCTrain (D.train n)) :
    ∀ᶠ n : ℕ in atTop, ∀ z ∈ Icc (-1 : ℝ) 1,
      ∃ Kf : AffSp D.K.as →L[ℝ] AffSp D.K.as, ∀ A, affIota D.K.as (Kf A) =
        KflatFun (D.level n).flat (cOf (D.level n).ν) (D.level n).ν (D.level n).ε (D.mu n z)
          D.K.χo D.K.χy D.K.χf (affIota D.K.as A) := by
  obtain ⟨ν₁, hν₁, h1'⟩ := h1 hχf hm8
  obtain ⟨ν₃, hν₃, h3'⟩ := h3 hχf hm8
  have hsmall : ∀ᶠ n : ℕ in atTop, retNu D.Pl D.σ₀ n ≤ min ν₁ ν₃ :=
    ((retNu_tendsto D.σ₀ hω).eventually (gt_mem_nhds (lt_min hν₁ hν₃))).mono fun _ hn => hn.le
  filter_upwards [D.eventually_lHyp hω hγ hσ0 hσ1 hχy, hflat, hsmall, hbuc]
    with n hL hF hs hb z hz
  obtain ⟨FI, hFI⟩ := hF
  have hl := hL z hz
  have hν : 0 < retNu D.Pl D.σ₀ n := retNu_pos _ _ _
  have hs1 : retNu D.Pl D.σ₀ n ≤ ν₁ := hs.trans (min_le_left _ _)
  have hs3 : retNu D.Pl D.σ₀ n ≤ ν₃ := hs.trans (min_le_right _ _)
  have e : (D.level n).flat = levelFlat hν FI D.K.χo (retEps D.Pl D.σ₀ n) := hFI
  rw [e]
  obtain ⟨C, hC⟩ := h3' κ (retNu D.Pl D.σ₀ n) (D.mu n z) (retEps D.Pl D.σ₀ n) D.K.χo hν
    hs3 hl.mu_pos.le hl.mu_lt (D.train n) hb FI
  exact exists_kflatOp_of (levelFlat hν FI D.K.χo (retEps D.Pl D.σ₀ n)) hS hSol hLin has
    (hAmb _) hl
    (fun A => h1' κ _ _ _ D.K.χo hν hs1 hl.mu_pos.le hl.mu_lt (D.train n) hb FI _
      (affIota_mem _ A))
    (fun A A' => (h2 hχf κ _ _ _ D.K.χo hν hl.nu_le hl.mu_pos.le hl.mu_lt (D.train n) FI _ _ 1
      (affIota_mem _ A) (affIota_mem _ A')).1)
    (fun r A => (h2 hχf κ _ _ _ D.K.χo hν hl.nu_le hl.mu_pos.le hl.mu_lt (D.train n) FI _ _ r
      (affIota_mem _ A) (affIota_mem _ A)).2)
    C (fun A => (hC _ (affIota_mem _ A)).trans_eq (by rw [affNorm_affIota]))

end UnforcedLeray.Short.PartIIIb.Concrete
