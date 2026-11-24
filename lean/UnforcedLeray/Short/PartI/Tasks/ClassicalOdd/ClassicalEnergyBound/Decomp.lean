import UnforcedLeray.Short.PartI.Sub.T02_3_10
import UnforcedLeray.Lib.Cylinder.IBP

/-!
# Part I, task `PartI:T02/3/10`: the momentum decomposition `EbDecomp`

Source of record: `the November 2 reference manuscript`, lines 276-282.

Target: `ebDecomp : EtaCutoffFacts → EbSliceSmooth → CellIntegrableOfSupport → EbDecomp`
(`Short/PartI/Sub/T02_3_10.lean`, the leaf `EbDecomp`, line 146).

Mathematics. Fix `s ∈ (0, T)` and `φ = etaCutoff R`. The momentum residual vanishes, so
`∂_s v = ν Δv - (v·∇)v - ∇p` pointwise. Multiplying `2⟨v, ∂_s v⟩` by `φ` and integrating over the
cell splits the integral into three integrals, one for each term. Each integrand is continuous and
vanishes for `|η| ≥ 2R`, hence is integrable on the cell by `CellIntegrableOfSupport`.

Proof layout. The `ebd_*` helpers are the calculus facts used by the main theorem: the partial
derivatives of a smooth function are smooth, the vector Laplacian, gradient and transport are
continuous, and the cutoff vanishes for `|η| ≥ 2R`. The helpers are copies of the `cid_*` helpers of
`Tasks/TrainCutoffEnergyProof/IntegrandDecomp.lean`, renamed so the two files can be imported together.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec)

/-! ### Calculus helpers -/

theorem ebd_cd2 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Plane → E}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ 2 f :=
  hf.of_le (by norm_num)

theorem ebd_comp {u : Plane → Vec} (i : Fin 2) {n : WithTop ℕ∞} (hu : ContDiff ℝ n u) :
    ContDiff ℝ n (fun x => u x i) :=
  (ContinuousLinearMap.contDiff (EuclideanSpace.proj (𝕜 := ℝ) i)).comp hu

theorem ebd_pQ_cd {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ 1 (Cyl.partialQ f) := by
  have h2 : ContDiff ℝ (1 + 1 : WithTop ℕ∞) f := by
    rw [one_add_one_eq_two]; exact ebd_cd2 hf
  exact Cyl.contDiff_partialQ (n := 1) h2

theorem ebd_pE_cd {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ 1 (Cyl.partialEta f) := by
  have h2 : ContDiff ℝ (1 + 1 : WithTop ℕ∞) f := by
    rw [one_add_one_eq_two]; exact ebd_cd2 hf
  exact Cyl.contDiff_partialEta (n := 1) h2

theorem ebd_pQQ_cont {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) :
    Continuous (Cyl.partialQ (Cyl.partialQ f)) := by
  have h1 : ContDiff ℝ (0 + 1 : WithTop ℕ∞) (Cyl.partialQ f) := by
    rw [zero_add]; exact ebd_pQ_cd hf
  exact (Cyl.contDiff_partialQ (n := 0) h1).continuous

theorem ebd_pEE_cont {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) :
    Continuous (Cyl.partialEta (Cyl.partialEta f)) := by
  have h1 : ContDiff ℝ (0 + 1 : WithTop ℕ∞) (Cyl.partialEta f) := by
    rw [zero_add]; exact ebd_pE_cd hf
  exact (Cyl.contDiff_partialEta (n := 0) h1).continuous

theorem ebd_toVec_cont : Continuous (Train.toVec) :=
  Train.toVecL.continuous

theorem ebd_lapS_cont {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) :
    Continuous (fun z => Train.lapS f z) := by
  unfold Train.lapS
  exact (ebd_pQQ_cont hf).add (ebd_pEE_cont hf)

theorem ebd_vecLap_cont {u : Plane → Vec} (hu : ContDiff ℝ ∞ u) :
    Continuous (fun z => Train.vecLaplacian u z) := by
  unfold Train.vecLaplacian
  exact ebd_toVec_cont.comp ((ebd_lapS_cont (ebd_comp 0 hu)).prodMk
    (ebd_lapS_cont (ebd_comp 1 hu)))

theorem ebd_gradS_cont {π : Plane → ℝ} (hπ : ContDiff ℝ ∞ π) :
    Continuous (fun z => Train.gradS π z) := by
  unfold Train.gradS
  exact ebd_toVec_cont.comp ((ebd_pQ_cd hπ).continuous.prodMk (ebd_pE_cd hπ).continuous)

theorem ebd_bilin_cont {a b : Plane → Vec} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) :
    Continuous (fun z => bilinAdv a b z) := by
  have a0 : Continuous (fun z => a z 0) := (ebd_comp 0 ha).continuous
  have a1 : Continuous (fun z => a z 1) := (ebd_comp 1 ha).continuous
  have q0 : Continuous (fun z => Cyl.partialQ (fun w => b w 0) z) :=
    (ebd_pQ_cd (ebd_comp 0 hb)).continuous
  have e0 : Continuous (fun z => Cyl.partialEta (fun w => b w 0) z) :=
    (ebd_pE_cd (ebd_comp 0 hb)).continuous
  have q1 : Continuous (fun z => Cyl.partialQ (fun w => b w 1) z) :=
    (ebd_pQ_cd (ebd_comp 1 hb)).continuous
  have e1 : Continuous (fun z => Cyl.partialEta (fun w => b w 1) z) :=
    (ebd_pE_cd (ebd_comp 1 hb)).continuous
  unfold bilinAdv
  exact ebd_toVec_cont.comp (((a0.mul q0).add (a1.mul e0)).prodMk
    ((a0.mul q1).add (a1.mul e1)))

theorem ebd_etaCutoff_cont (R : ℝ) : Continuous (fun z : Plane => etaCutoff R z.2) := by
  unfold etaCutoff
  exact (Real.smoothTransition.continuous.comp
    (continuous_const.sub ((continuous_abs.comp continuous_snd).div_const R))).pow 2

theorem ebd_etaCutoff_eq_zero {R : ℝ} (hR : 0 < R) {η : ℝ} (h : 2 * R ≤ |η|) :
    etaCutoff R η = 0 := by
  have h2 : 2 - |η| / R ≤ 0 := by
    have h3 : 2 ≤ |η| / R := by
      rw [le_div_iff₀ hR]; linarith
    linarith
  unfold etaCutoff
  rw [Real.smoothTransition.zero_of_nonpos h2]
  norm_num

/-! ### The theorem -/

/-- **`PartI:T02/3/10`, `EbDecomp`.** Given the cutoff facts, the slice smoothness toolkit and the
cell integrability toolkit, the momentum equation gives the three-term decomposition of
`∫_cell φ_R · 2⟨v, ∂_s v⟩` for every `s ∈ (0, T)`. -/
theorem ebDecomp : EtaCutoffFacts → EbSliceSmooth → CellIntegrableOfSupport → EbDecomp := by
  intro _hF hS hI ν c T v p hc hcl R hR s hs
  have hRpos : 0 < R := by linarith
  have hs0 : s ∈ Icc (0 : ℝ) T := Ioo_subset_Icc_self hs
  obtain ⟨hv, hp⟩ := hS ν c T v p hcl s hs0
  -- the pointwise equation `∂_s v = νΔv - (v·∇)v - ∇p`
  have hpt : ∀ z : Plane,
      deriv (fun t => v t z) s =
        ν • Train.vecLaplacian (v s) z - Train.advection (v s) z - Train.gradS (p s) z := by
    intro z
    have M := hcl.momentum s hs z
    unfold Train.momentumResidual at M
    linear_combination (norm := module) M
  -- support of the cutoff
  have hsupp : ∀ z : Plane, 2 * R ≤ |z.2| → etaCutoff R z.2 = 0 :=
    fun z hz => ebd_etaCutoff_eq_zero hRpos hz
  -- continuity of the three integrands
  have hcφ : Continuous (fun z : Plane => etaCutoff R z.2) := ebd_etaCutoff_cont R
  have hvc : Continuous (v s) := hv.continuous
  have hadv : Continuous (fun z => Train.advection (v s) z) := ebd_bilin_cont hv hv
  have hcL : Continuous (fun z : Plane =>
      etaCutoff R z.2 * inner ℝ (v s z) (Train.vecLaplacian (v s) z)) :=
    hcφ.mul (hvc.inner (ebd_vecLap_cont hv))
  have hcA : Continuous (fun z : Plane =>
      etaCutoff R z.2 * inner ℝ (v s z) (Train.advection (v s) z)) :=
    hcφ.mul (hvc.inner hadv)
  have hcG : Continuous (fun z : Plane =>
      etaCutoff R z.2 * inner ℝ (v s z) (Train.gradS (p s) z)) :=
    hcφ.mul (hvc.inner (ebd_gradS_cont hp))
  -- integrability on the cell, from the support of the cutoff
  have iL : IntegrableOn (fun z : Plane =>
      etaCutoff R z.2 * inner ℝ (v s z) (Train.vecLaplacian (v s) z)) (Cyl.cell c) :=
    hI c R hc hRpos _ hcL (fun z hz => by simp only [hsupp z hz, zero_mul])
  have iA : IntegrableOn (fun z : Plane =>
      etaCutoff R z.2 * inner ℝ (v s z) (Train.advection (v s) z)) (Cyl.cell c) :=
    hI c R hc hRpos _ hcA (fun z hz => by simp only [hsupp z hz, zero_mul])
  have iG : IntegrableOn (fun z : Plane =>
      etaCutoff R z.2 * inner ℝ (v s z) (Train.gradS (p s) z)) (Cyl.cell c) :=
    hI c R hc hRpos _ hcG (fun z hz => by simp only [hsupp z hz, zero_mul])
  have jL : Integrable (fun z : Plane => (2 * ν) *
      (etaCutoff R z.2 * inner ℝ (v s z) (Train.vecLaplacian (v s) z)))
      (volume.restrict (Cyl.cell c)) := Integrable.const_mul iL (2 * ν)
  have jA : Integrable (fun z : Plane => (-2 : ℝ) *
      (etaCutoff R z.2 * inner ℝ (v s z) (Train.advection (v s) z)))
      (volume.restrict (Cyl.cell c)) := Integrable.const_mul iA (-2)
  have jG : Integrable (fun z : Plane => (-2 : ℝ) *
      (etaCutoff R z.2 * inner ℝ (v s z) (Train.gradS (p s) z)))
      (volume.restrict (Cyl.cell c)) := Integrable.const_mul iG (-2)
  -- the integrand splits pointwise
  have hsplit : (∫ z in Cyl.cell c, etaCutoff R z.2 *
        (2 * inner ℝ (v s z) (deriv (fun t => v t z) s))) =
      ∫ z in Cyl.cell c, (((2 * ν) *
          (etaCutoff R z.2 * inner ℝ (v s z) (Train.vecLaplacian (v s) z)) +
        (-2 : ℝ) * (etaCutoff R z.2 * inner ℝ (v s z) (Train.advection (v s) z))) +
        (-2 : ℝ) * (etaCutoff R z.2 * inner ℝ (v s z) (Train.gradS (p s) z))) := by
    congr 1
    funext z
    rw [hpt z]
    simp only [inner_sub_right, real_inner_smul_right]
    ring
  have k1 : Integrable (fun z : Plane => (2 * ν) *
      (etaCutoff R z.2 * inner ℝ (v s z) (Train.vecLaplacian (v s) z)) +
      (-2 : ℝ) * (etaCutoff R z.2 * inner ℝ (v s z) (Train.advection (v s) z)))
      (volume.restrict (Cyl.cell c)) := jL.add jA
  have e2 : (∫ z in Cyl.cell c, (((2 * ν) *
          (etaCutoff R z.2 * inner ℝ (v s z) (Train.vecLaplacian (v s) z)) +
        (-2 : ℝ) * (etaCutoff R z.2 * inner ℝ (v s z) (Train.advection (v s) z))) +
        (-2 : ℝ) * (etaCutoff R z.2 * inner ℝ (v s z) (Train.gradS (p s) z)))) =
      (∫ z in Cyl.cell c, ((2 * ν) *
          (etaCutoff R z.2 * inner ℝ (v s z) (Train.vecLaplacian (v s) z)) +
        (-2 : ℝ) * (etaCutoff R z.2 * inner ℝ (v s z) (Train.advection (v s) z)))) +
      ∫ z in Cyl.cell c, (-2 : ℝ) *
        (etaCutoff R z.2 * inner ℝ (v s z) (Train.gradS (p s) z)) :=
    integral_add k1 jG
  have e1 : (∫ z in Cyl.cell c, ((2 * ν) *
          (etaCutoff R z.2 * inner ℝ (v s z) (Train.vecLaplacian (v s) z)) +
        (-2 : ℝ) * (etaCutoff R z.2 * inner ℝ (v s z) (Train.advection (v s) z)))) =
      (∫ z in Cyl.cell c, (2 * ν) *
          (etaCutoff R z.2 * inner ℝ (v s z) (Train.vecLaplacian (v s) z))) +
      ∫ z in Cyl.cell c, (-2 : ℝ) *
        (etaCutoff R z.2 * inner ℝ (v s z) (Train.advection (v s) z)) :=
    integral_add jL jA
  unfold ebDtIntegral ebViscous ebConv ebPres
  rw [hsplit, e2, e1]
  simp only [integral_const_mul]

end UnforcedLeray.Short.PartI
