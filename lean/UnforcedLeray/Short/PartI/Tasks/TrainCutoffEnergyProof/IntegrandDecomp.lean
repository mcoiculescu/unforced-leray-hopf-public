import UnforcedLeray.Short.PartI.Sub.T05b_2
import UnforcedLeray.Lib.Cylinder.IBP

/-!
# Part I, task `PartI:T05b/2/6`: the integrand decomposition `CutoffIntegrandDecomp`

Source of record: `the November 2 reference manuscript`, lines 276-288.

Target: `cutoffIntegrandDecomp (hI : CellIntegrableOfSupport) (hS : TrainSliceSmooth) :
CutoffIntegrandDecomp` (`Short/PartI/Sub/T05b_2.lean`, the leaf `CutoffIntegrandDecomp`).

Mathematics. Fix `s > 0`, put `w = v - v'`, `π = p - p'` and `φ = etaCutoff R`. The momentum
equations of both trains give, at every point,
`∂_s w = -((v·∇)w + (w·∇)v') + ν Δw - ∇π`.
Multiplying `2⟨w, ∂_s w⟩` by `φ` and integrating over the cell splits the integral into four
integrals, one for each term; each integrand is continuous and vanishes for `|η| ≥ 2R`, hence is
integrable on the cell by `hI`.

Proof layout. Helpers (`cid_*`) give the calculus facts: componentwise partials of a difference,
the vector Laplacian and gradient of a difference, continuity of the transport, Laplacian and
gradient terms, and support of the cutoff. The main theorem then combines them.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec)

/-! ### Calculus helpers -/

section CidCalculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem cid_cd2 {f : Plane → E} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ 2 f :=
  hf.of_le (by norm_num)

theorem cid_diff {f : Plane → E} (hf : ContDiff ℝ ∞ f) : Differentiable ℝ f :=
  (cid_cd2 hf).differentiable (by norm_num)

theorem cid_comp {u : Plane → Vec} (i : Fin 2) {n : WithTop ℕ∞} (hu : ContDiff ℝ n u) :
    ContDiff ℝ n (fun x => u x i) :=
  (ContinuousLinearMap.contDiff (EuclideanSpace.proj (𝕜 := ℝ) i)).comp hu

theorem cid_pQ_cd {f : Plane → E} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ 1 (Cyl.partialQ f) := by
  have h2 : ContDiff ℝ (1 + 1 : WithTop ℕ∞) f := by
    rw [one_add_one_eq_two]; exact cid_cd2 hf
  exact Cyl.contDiff_partialQ (n := 1) h2

theorem cid_pE_cd {f : Plane → E} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ 1 (Cyl.partialEta f) := by
  have h2 : ContDiff ℝ (1 + 1 : WithTop ℕ∞) f := by
    rw [one_add_one_eq_two]; exact cid_cd2 hf
  exact Cyl.contDiff_partialEta (n := 1) h2

theorem cid_pQQ_cont {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) :
    Continuous (Cyl.partialQ (Cyl.partialQ f)) := by
  have h1 : ContDiff ℝ (0 + 1 : WithTop ℕ∞) (Cyl.partialQ f) := by
    rw [zero_add]; exact cid_pQ_cd hf
  exact (Cyl.contDiff_partialQ (n := 0) h1).continuous

theorem cid_pEE_cont {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) :
    Continuous (Cyl.partialEta (Cyl.partialEta f)) := by
  have h1 : ContDiff ℝ (0 + 1 : WithTop ℕ∞) (Cyl.partialEta f) := by
    rw [zero_add]; exact cid_pE_cd hf
  exact (Cyl.contDiff_partialEta (n := 0) h1).continuous

/-- Linearity of `∂_q` on a difference of two differentiable functions, pointwise. -/
theorem cid_pQ_sub {f g : Plane → E} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (z : Plane) :
    Cyl.partialQ (fun x => f x - g x) z = Cyl.partialQ f z - Cyl.partialQ g z := by
  unfold Cyl.partialQ
  have h1 : DifferentiableAt ℝ (fun q : ℝ => f (q, z.2)) z.1 :=
    (hf (z.1, z.2)).comp z.1 (differentiableAt_id.prodMk (differentiableAt_const z.2))
  have h2 : DifferentiableAt ℝ (fun q : ℝ => g (q, z.2)) z.1 :=
    (hg (z.1, z.2)).comp z.1 (differentiableAt_id.prodMk (differentiableAt_const z.2))
  exact deriv_sub h1 h2

/-- Linearity of `∂_η` on a difference of two differentiable functions, pointwise. -/
theorem cid_pE_sub {f g : Plane → E} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (z : Plane) :
    Cyl.partialEta (fun x => f x - g x) z = Cyl.partialEta f z - Cyl.partialEta g z := by
  unfold Cyl.partialEta
  have h1 : DifferentiableAt ℝ (fun η : ℝ => f (z.1, η)) z.2 :=
    (hf (z.1, z.2)).comp z.2 ((differentiableAt_const z.1).prodMk differentiableAt_id)
  have h2 : DifferentiableAt ℝ (fun η : ℝ => g (z.1, η)) z.2 :=
    (hg (z.1, z.2)).comp z.2 ((differentiableAt_const z.1).prodMk differentiableAt_id)
  exact deriv_sub h1 h2

end CidCalculus

/-- Components of a difference: `∂_q (v_j - v'_j) = ∂_q v_j - ∂_q v'_j`. -/
theorem cid_pQ_comp_sub {v v' : Plane → Vec} (hv : ContDiff ℝ ∞ v) (hv' : ContDiff ℝ ∞ v')
    (j : Fin 2) (z : Plane) :
    Cyl.partialQ (fun x => v x j - v' x j) z =
      Cyl.partialQ (fun x => v x j) z - Cyl.partialQ (fun x => v' x j) z :=
  cid_pQ_sub (cid_diff (cid_comp j hv)) (cid_diff (cid_comp j hv')) z

/-- Components of a difference: `∂_η (v_j - v'_j) = ∂_η v_j - ∂_η v'_j`. -/
theorem cid_pE_comp_sub {v v' : Plane → Vec} (hv : ContDiff ℝ ∞ v) (hv' : ContDiff ℝ ∞ v')
    (j : Fin 2) (z : Plane) :
    Cyl.partialEta (fun x => v x j - v' x j) z =
      Cyl.partialEta (fun x => v x j) z - Cyl.partialEta (fun x => v' x j) z :=
  cid_pE_sub (cid_diff (cid_comp j hv)) (cid_diff (cid_comp j hv')) z

/-- The scalar Laplacian of a difference. -/
theorem cid_lapS_sub {f g : Plane → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (z : Plane) :
    Train.lapS (fun x => f x - g x) z = Train.lapS f z - Train.lapS g z := by
  unfold Train.lapS
  have hQ : Cyl.partialQ (fun x => f x - g x) =
      fun x => Cyl.partialQ f x - Cyl.partialQ g x :=
    funext (cid_pQ_sub (cid_diff hf) (cid_diff hg))
  have hE : Cyl.partialEta (fun x => f x - g x) =
      fun x => Cyl.partialEta f x - Cyl.partialEta g x :=
    funext (cid_pE_sub (cid_diff hf) (cid_diff hg))
  rw [hQ, hE, cid_pQ_sub ((cid_pQ_cd hf).differentiable (by norm_num))
      ((cid_pQ_cd hg).differentiable (by norm_num)) z,
    cid_pE_sub ((cid_pE_cd hf).differentiable (by norm_num))
      ((cid_pE_cd hg).differentiable (by norm_num)) z]
  ring

/-- The gradient of a difference. -/
theorem cid_gradS_sub {p p' π : Plane → ℝ} (hp : ContDiff ℝ ∞ p) (hp' : ContDiff ℝ ∞ p')
    (hπ : π = fun x => p x - p' x) (z : Plane) :
    Train.gradS π z = Train.gradS p z - Train.gradS p' z := by
  subst hπ
  unfold Train.gradS
  rw [cid_pQ_sub (cid_diff hp) (cid_diff hp') z, cid_pE_sub (cid_diff hp) (cid_diff hp') z,
    ← Train.toVec_sub]
  rfl

/-- The vector Laplacian of a difference. -/
theorem cid_vecLaplacian_sub {v v' w : Plane → Vec} (hv : ContDiff ℝ ∞ v)
    (hv' : ContDiff ℝ ∞ v') (hw : w = fun x => v x - v' x) (z : Plane) :
    Train.vecLaplacian w z = Train.vecLaplacian v z - Train.vecLaplacian v' z := by
  subst hw
  apply Train.Vec.ext
  · simp only [Train.vecLaplacian, PiLp.sub_apply, Train.toVec_zero]
    exact cid_lapS_sub (cid_comp 0 hv) (cid_comp 0 hv') z
  · simp only [Train.vecLaplacian, PiLp.sub_apply, Train.toVec_one]
    exact cid_lapS_sub (cid_comp 1 hv) (cid_comp 1 hv') z

/-- The transport term of a difference: `(v·∇)v - (v'·∇)v' = (v·∇)w + (w·∇)v'`. -/
theorem cid_advection_sub {v v' w : Plane → Vec} (hv : ContDiff ℝ ∞ v)
    (hv' : ContDiff ℝ ∞ v') (hw : w = fun x => v x - v' x) (z : Plane) :
    Train.advection v z - Train.advection v' z =
      bilinAdv v w z + bilinAdv w v' z := by
  subst hw
  apply Train.Vec.ext
  · simp only [bilinAdv, Train.advection, PiLp.sub_apply, PiLp.add_apply, Train.toVec_zero]
    rw [cid_pQ_comp_sub hv hv' 0 z, cid_pE_comp_sub hv hv' 0 z]
    ring
  · simp only [bilinAdv, Train.advection, PiLp.sub_apply, PiLp.add_apply, Train.toVec_one]
    rw [cid_pQ_comp_sub hv hv' 1 z, cid_pE_comp_sub hv hv' 1 z]
    ring

/-! ### Continuity and support -/

theorem cid_toVec_cont : Continuous (Train.toVec) :=
  Train.toVecL.continuous

theorem cid_lapS_cont {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) :
    Continuous (fun z => Train.lapS f z) := by
  unfold Train.lapS
  exact (cid_pQQ_cont hf).add (cid_pEE_cont hf)

theorem cid_vecLap_cont {u : Plane → Vec} (hu : ContDiff ℝ ∞ u) :
    Continuous (fun z => Train.vecLaplacian u z) := by
  unfold Train.vecLaplacian
  exact cid_toVec_cont.comp ((cid_lapS_cont (cid_comp 0 hu)).prodMk
    (cid_lapS_cont (cid_comp 1 hu)))

theorem cid_gradS_cont {π : Plane → ℝ} (hπ : ContDiff ℝ ∞ π) :
    Continuous (fun z => Train.gradS π z) := by
  unfold Train.gradS
  exact cid_toVec_cont.comp ((cid_pQ_cd hπ).continuous.prodMk (cid_pE_cd hπ).continuous)

theorem cid_bilin_cont {a b : Plane → Vec} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) :
    Continuous (fun z => bilinAdv a b z) := by
  have a0 : Continuous (fun z => a z 0) := (cid_comp 0 ha).continuous
  have a1 : Continuous (fun z => a z 1) := (cid_comp 1 ha).continuous
  have q0 : Continuous (fun z => Cyl.partialQ (fun w => b w 0) z) :=
    (cid_pQ_cd (cid_comp 0 hb)).continuous
  have e0 : Continuous (fun z => Cyl.partialEta (fun w => b w 0) z) :=
    (cid_pE_cd (cid_comp 0 hb)).continuous
  have q1 : Continuous (fun z => Cyl.partialQ (fun w => b w 1) z) :=
    (cid_pQ_cd (cid_comp 1 hb)).continuous
  have e1 : Continuous (fun z => Cyl.partialEta (fun w => b w 1) z) :=
    (cid_pE_cd (cid_comp 1 hb)).continuous
  unfold bilinAdv
  exact cid_toVec_cont.comp (((a0.mul q0).add (a1.mul e0)).prodMk
    ((a0.mul q1).add (a1.mul e1)))

theorem cid_etaCutoff_cont (R : ℝ) : Continuous (fun z : Plane => etaCutoff R z.2) := by
  unfold etaCutoff
  exact (Real.smoothTransition.continuous.comp
    (continuous_const.sub ((continuous_abs.comp continuous_snd).div_const R))).pow 2

theorem cid_etaCutoff_eq_zero {R : ℝ} (hR : 0 < R) {η : ℝ} (h : 2 * R ≤ |η|) :
    etaCutoff R η = 0 := by
  have h2 : 2 - |η| / R ≤ 0 := by
    have h3 : 2 ≤ |η| / R := by
      rw [le_div_iff₀ hR]; linarith
    linarith
  unfold etaCutoff
  rw [Real.smoothTransition.zero_of_nonpos h2]
  norm_num

/-! ### The four integrands -/

/-- The transport integrand `φ_R(η) ⟨w, (v·∇)w⟩`. -/
def cidTermA {ν c : ℝ} (tr tr' : B0140.TrainSol ν c) (R s : ℝ) (z : Plane) : ℝ :=
  etaCutoff R z.2 * inner ℝ (diffV tr tr' s z) (bilinAdv (tr.v s) (diffV tr tr' s) z)

/-- The stretching integrand `φ_R(η) ⟨w, (w·∇)v'⟩`. -/
def cidTermB {ν c : ℝ} (tr tr' : B0140.TrainSol ν c) (R s : ℝ) (z : Plane) : ℝ :=
  etaCutoff R z.2 * inner ℝ (diffV tr tr' s z) (bilinAdv (diffV tr tr' s) (tr'.v s) z)

/-- The viscous integrand `φ_R(η) ⟨w, Δw⟩`. -/
def cidTermL {ν c : ℝ} (tr tr' : B0140.TrainSol ν c) (R s : ℝ) (z : Plane) : ℝ :=
  etaCutoff R z.2 * inner ℝ (diffV tr tr' s z) (Train.vecLaplacian (diffV tr tr' s) z)

/-- The pressure integrand `φ_R(η) ⟨w, ∇π⟩`. -/
def cidTermG {ν c : ℝ} (tr tr' : B0140.TrainSol ν c) (R s : ℝ) (z : Plane) : ℝ :=
  etaCutoff R z.2 * inner ℝ (diffV tr tr' s z) (Train.gradS (diffP tr tr' s) z)

/-! ### The theorem -/

/-- **`PartI:T05b/2/6`, `CutoffIntegrandDecomp`.** For `s > 0` the cutoff integral
`∫_cell φ_R · 2⟨w, ∂_s w⟩` is the sum of the viscous, transport, stretching and pressure terms. -/
theorem cutoffIntegrandDecomp (hI : CellIntegrableOfSupport) (hS : TrainSliceSmooth) :
    CutoffIntegrandDecomp := by
  intro ν c hν hc tr tr' R hR s hs
  have hRpos : 0 < R := by linarith
  have hs0 : 0 ≤ s := hs.le
  obtain ⟨hv, hp⟩ := hS ν c tr s hs0
  obtain ⟨hv', hp'⟩ := hS ν c tr' s hs0
  have hwd : ContDiff ℝ ∞ (diffV tr tr' s) := hv.sub hv'
  have hPd : ContDiff ℝ ∞ (diffP tr tr' s) := hp.sub hp'
  have hw_eq : diffV tr tr' s = fun x => tr.v s x - tr'.v s x := rfl
  have hP_eq : diffP tr tr' s = fun x => tr.p s x - tr'.p s x := rfl
  -- differentiability of a train in the age variable at `s > 0`
  have hdt : ∀ (T : B0140.TrainSol ν c) (z : Plane),
      DifferentiableAt ℝ (fun t => T.v t z) s := by
    intro T z
    have h1 : ContDiffOn ℝ ∞ (fun x : ℝ × Plane => T.v x.1 x.2)
        (Ici (0 : ℝ) ×ˢ (univ : Set Plane)) := T.isTrain.smooth_v
    have h2 : (Ici (0 : ℝ) ×ˢ (univ : Set Plane)) ∈ 𝓝 (s, z) :=
      prod_mem_nhds (Ici_mem_nhds hs) univ_mem
    have h3 : DifferentiableAt ℝ (fun x : ℝ × Plane => T.v x.1 x.2) (s, z) :=
      (h1.differentiableOn (by norm_num)).differentiableAt h2
    have hline : DifferentiableAt ℝ (fun t : ℝ => ((t, z) : ℝ × Plane)) s :=
      (differentiableAt_id).prodMk (differentiableAt_const z)
    exact h3.comp s hline
  -- the pointwise equation for `w`
  have hpt : ∀ z : Plane,
      deriv (fun t => diffV tr tr' t z) s =
        -(bilinAdv (tr.v s) (diffV tr tr' s) z + bilinAdv (diffV tr tr' s) (tr'.v s) z) +
          ν • Train.vecLaplacian (diffV tr tr' s) z - Train.gradS (diffP tr tr' s) z := by
    intro z
    have M := tr.isTrain.momentum s hs z
    have M' := tr'.isTrain.momentum s hs z
    unfold Train.momentumResidual at M M'
    have hD : deriv (fun t => diffV tr tr' t z) s =
        deriv (fun t => tr.v t z) s - deriv (fun t => tr'.v t z) s :=
      deriv_sub (hdt tr z) (hdt tr' z)
    rw [hD, cid_vecLaplacian_sub hv hv' hw_eq z, cid_gradS_sub hp hp' hP_eq z,
      ← cid_advection_sub hv hv' hw_eq z]
    linear_combination (norm := module) M - M'
  -- continuity of the four integrands
  have hcφ : Continuous (fun z : Plane => etaCutoff R z.2) := cid_etaCutoff_cont R
  have hwc : Continuous (diffV tr tr' s) := hwd.continuous
  have hcA : Continuous (cidTermA tr tr' R s) :=
    hcφ.mul (hwc.inner (cid_bilin_cont hv hwd))
  have hcB : Continuous (cidTermB tr tr' R s) :=
    hcφ.mul (hwc.inner (cid_bilin_cont hwd hv'))
  have hcL : Continuous (cidTermL tr tr' R s) :=
    hcφ.mul (hwc.inner (cid_vecLap_cont hwd))
  have hcG : Continuous (cidTermG tr tr' R s) :=
    hcφ.mul (hwc.inner (cid_gradS_cont hPd))
  -- support: the cutoff vanishes for `|η| ≥ 2R`
  have hsupp : ∀ z : Plane, 2 * R ≤ |z.2| → etaCutoff R z.2 = 0 :=
    fun z hz => cid_etaCutoff_eq_zero hRpos hz
  have iA : IntegrableOn (cidTermA tr tr' R s) (Cyl.cell c) :=
    hI c R hc hRpos _ hcA (fun z hz => by simp only [cidTermA, hsupp z hz, zero_mul])
  have iB : IntegrableOn (cidTermB tr tr' R s) (Cyl.cell c) :=
    hI c R hc hRpos _ hcB (fun z hz => by simp only [cidTermB, hsupp z hz, zero_mul])
  have iL : IntegrableOn (cidTermL tr tr' R s) (Cyl.cell c) :=
    hI c R hc hRpos _ hcL (fun z hz => by simp only [cidTermL, hsupp z hz, zero_mul])
  have iG : IntegrableOn (cidTermG tr tr' R s) (Cyl.cell c) :=
    hI c R hc hRpos _ hcG (fun z hz => by simp only [cidTermG, hsupp z hz, zero_mul])
  have jA : Integrable (fun z => (-2 : ℝ) * cidTermA tr tr' R s z)
      (volume.restrict (Cyl.cell c)) := Integrable.const_mul iA (-2)
  have jB : Integrable (fun z => (-2 : ℝ) * cidTermB tr tr' R s z)
      (volume.restrict (Cyl.cell c)) := Integrable.const_mul iB (-2)
  have jL : Integrable (fun z => (2 * ν) * cidTermL tr tr' R s z)
      (volume.restrict (Cyl.cell c)) := Integrable.const_mul iL (2 * ν)
  have jG : Integrable (fun z => (-2 : ℝ) * cidTermG tr tr' R s z)
      (volume.restrict (Cyl.cell c)) := Integrable.const_mul iG (-2)
  -- the integrand splits pointwise
  have hsplit : (∫ z in Cyl.cell c, etaCutoff R z.2 *
        (2 * inner ℝ (diffV tr tr' s z) (deriv (fun t => diffV tr tr' t z) s))) =
      ∫ z in Cyl.cell c, ((-2 : ℝ) * cidTermA tr tr' R s z + (-2 : ℝ) * cidTermB tr tr' R s z +
        (2 * ν) * cidTermL tr tr' R s z + (-2 : ℝ) * cidTermG tr tr' R s z) := by
    congr 1
    funext z
    rw [hpt z]
    simp only [cidTermA, cidTermB, cidTermL, cidTermG, inner_add_right, inner_sub_right,
      inner_neg_right, real_inner_smul_right]
    ring
  have k1 : Integrable (fun z => (-2 : ℝ) * cidTermA tr tr' R s z +
      (-2 : ℝ) * cidTermB tr tr' R s z) (volume.restrict (Cyl.cell c)) := jA.add jB
  have k2 : Integrable (fun z => (-2 : ℝ) * cidTermA tr tr' R s z +
      (-2 : ℝ) * cidTermB tr tr' R s z + (2 * ν) * cidTermL tr tr' R s z)
      (volume.restrict (Cyl.cell c)) := k1.add jL
  have e2 : (∫ z in Cyl.cell c, ((-2 : ℝ) * cidTermA tr tr' R s z +
        (-2 : ℝ) * cidTermB tr tr' R s z + (2 * ν) * cidTermL tr tr' R s z +
        (-2 : ℝ) * cidTermG tr tr' R s z)) =
      (∫ z in Cyl.cell c, ((-2 : ℝ) * cidTermA tr tr' R s z +
        (-2 : ℝ) * cidTermB tr tr' R s z + (2 * ν) * cidTermL tr tr' R s z)) +
      ∫ z in Cyl.cell c, (-2 : ℝ) * cidTermG tr tr' R s z :=
    integral_add k2 jG
  have e1 : (∫ z in Cyl.cell c, ((-2 : ℝ) * cidTermA tr tr' R s z +
        (-2 : ℝ) * cidTermB tr tr' R s z + (2 * ν) * cidTermL tr tr' R s z)) =
      (∫ z in Cyl.cell c, ((-2 : ℝ) * cidTermA tr tr' R s z +
        (-2 : ℝ) * cidTermB tr tr' R s z)) +
      ∫ z in Cyl.cell c, (2 * ν) * cidTermL tr tr' R s z :=
    integral_add k1 jL
  have e0 : (∫ z in Cyl.cell c, ((-2 : ℝ) * cidTermA tr tr' R s z +
        (-2 : ℝ) * cidTermB tr tr' R s z)) =
      (∫ z in Cyl.cell c, (-2 : ℝ) * cidTermA tr tr' R s z) +
      ∫ z in Cyl.cell c, (-2 : ℝ) * cidTermB tr tr' R s z :=
    integral_add jA jB
  rw [hsplit, e2, e1, e0]
  simp only [integral_const_mul, cutoffViscous, cutoffTransport, cutoffStretch,
    cutoffPressure, cidTermA, cidTermB, cidTermL, cidTermG]
  ring

end UnforcedLeray.Short.PartI
