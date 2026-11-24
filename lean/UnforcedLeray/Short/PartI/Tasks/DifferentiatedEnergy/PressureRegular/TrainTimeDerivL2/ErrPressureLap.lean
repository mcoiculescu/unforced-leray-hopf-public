import UnforcedLeray.Short.PartI.Sub.PartI_T08_3_3
import UnforcedLeray.Short.PartI.Tasks.TrainErrorEquation
import UnforcedLeray.Short.PartI.Tasks.DifferentiatedEnergy.ErrBasic.QcSmooth
import UnforcedLeray.Short.Spine.Proofs.EstVcRegularity
import UnforcedLeray.Short.PartI.Tasks.LerayPressureGauge.PressurePoisson

/-!
# Part I, task `PartI:T08/3/3/2` (`ErrPressureLap`): the pressure Poisson identity for the error

Source of record: `the November 2 reference manuscript`, lines 326-336.

For `s > 0` the pressure error `π = p - p_c` satisfies `Δπ + div(A + div Q_c) = 0`, where
`A = advDiff = v·∇v - V_c·∇V_c`.

Proof. Two identities, combined linearly.
(a) Train pressure Poisson `Δp + div(v·∇v) = 0`: take the divergence of the momentum equation
at age `s`. `div ∂ₛv = ∂ₛ div v = 0` and `div Δv = Δ div v = 0` (mixed partials commute, for
smooth `v`), and `div v = 0` for all ages.
(b) The periodized vortex satisfies `∇p_c = div Q_c - V_c·∇V_c` (`Vc_heat` and `Vc_residual`),
so `Δp_c = div(div Q_c - V_c·∇V_c)`.
Subtracting, `Δπ = -div(v·∇v) + div(V_c·∇V_c) - div div Q_c`, which is the claim.
The smoothness of `v`, `p`, `V_c`, `p_c`, `Q_c` makes all partials genuine.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartI.ErrPressureLapAux

open UnforcedLeray.Cyl (Plane partialQ partialEta)
open UnforcedLeray.Train (Vec toVec Vc pc Qc gradS lapS advection matDiv vecLaplacian momentumResidual width)
open UnforcedLeray.Short.PartI.TrainErrorEquation (LineQ LineE lineQ_of_contDiff lineE_of_contDiff partialQ_contDiff partialEta_contDiff G2_of_contDiff contDiff_slice lapS_sub_eq partialQ_sub_eq partialEta_sub_eq)
open UnforcedLeray.Short.PartI.PPoisson (dirP eT eQ eE SmU Fc smU_Fc sliceQ sliceE dirP_symm dirP_eq_zero dirP_add smU_dir smU_differentiableAt)

/-! ### Basic calculus on the plane -/

theorem comp_contDiff {u : Plane → Vec} (hu : ContDiff ℝ ∞ u) (k : Fin 2) :
    ContDiff ℝ ∞ (fun w => u w k) :=
  (EuclideanSpace.proj (𝕜 := ℝ) k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).contDiff.comp hu

/-- Symmetry of the second derivative, in the form needed for the Plane. -/
theorem fderiv_comm_plane (f : Plane → ℝ) (hf : ContDiff ℝ ∞ f) (x v w : Plane) :
    fderiv ℝ (fun y => fderiv ℝ f y v) x w = fderiv ℝ (fun y => fderiv ℝ f y w) x v := by
  have hfd : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (m := ∞) (by simp)
  have hD : DifferentiableAt ℝ (fderiv ℝ f) x := (hfd.differentiable (by simp)) x
  have hv : fderiv ℝ (fun y => fderiv ℝ f y v) x w = fderiv ℝ (fderiv ℝ f) x w v := by
    rw [fderiv_clm_apply hD (differentiableAt_const (x := x) v)]
    simp
  have hw : fderiv ℝ (fun y => fderiv ℝ f y w) x v = fderiv ℝ (fderiv ℝ f) x v w := by
    rw [fderiv_clm_apply hD (differentiableAt_const (x := x) w)]
    simp
  rw [hv, hw]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by simp)) w v

/-- Mixed partials of a smooth scalar field commute. -/
theorem partialQ_partialEta_comm (f : Plane → ℝ) (hf : ContDiff ℝ ∞ f) :
    partialQ (partialEta f) = partialEta (partialQ f) := by
  funext z
  have hfd : ContDiff ℝ ∞ (fderiv ℝ f) := hf.fderiv_right (m := ∞) (by simp)
  have hE : DifferentiableAt ℝ (fun w => fderiv ℝ f w ((0 : ℝ), (1 : ℝ))) z :=
    ((hfd.clm_apply contDiff_const).differentiable (by simp)) z
  have hQ : DifferentiableAt ℝ (fun w => fderiv ℝ f w ((1 : ℝ), (0 : ℝ))) z :=
    ((hfd.clm_apply contDiff_const).differentiable (by simp)) z
  have e1 : partialEta f = fun w => fderiv ℝ f w ((0 : ℝ), (1 : ℝ)) :=
    funext fun w => UnforcedLeray.B0238.partialEta_eq_fderiv (hf.differentiable (by simp) w)
  have e2 : partialQ f = fun w => fderiv ℝ f w ((1 : ℝ), (0 : ℝ)) :=
    funext fun w => UnforcedLeray.B0238.partialQ_eq_fderiv (hf.differentiable (by simp) w)
  have k1 : partialQ (partialEta f) z =
      fderiv ℝ (fun w => fderiv ℝ f w ((0 : ℝ), (1 : ℝ))) z ((1 : ℝ), (0 : ℝ)) := by
    rw [e1]; exact UnforcedLeray.B0238.partialQ_eq_fderiv hE
  have k2 : partialEta (partialQ f) z =
      fderiv ℝ (fun w => fderiv ℝ f w ((1 : ℝ), (0 : ℝ))) z ((0 : ℝ), (1 : ℝ)) := by
    rw [e2]; exact UnforcedLeray.B0238.partialEta_eq_fderiv hQ
  rw [k1, k2]
  exact fderiv_comm_plane f hf z ((0 : ℝ), (1 : ℝ)) ((1 : ℝ), (0 : ℝ))

theorem partialQ_add_eq' {f g : Plane → ℝ} (hf : LineQ f) (hg : LineQ g) (w : Plane) :
    partialQ (fun u => f u + g u) w = partialQ f w + partialQ g w :=
  ((hf w).hasDerivAt.add (hg w).hasDerivAt).deriv

theorem partialEta_add_eq' {f g : Plane → ℝ} (hf : LineE f) (hg : LineE g) (w : Plane) :
    partialEta (fun u => f u + g u) w = partialEta f w + partialEta g w :=
  ((hf w).hasDerivAt.add (hg w).hasDerivAt).deriv

theorem partialQ_add_pt {a b : Plane → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (z : Plane) : partialQ (fun w => a w + b w) z = partialQ a z + partialQ b z :=
  partialQ_add_eq' (lineQ_of_contDiff ha) (lineQ_of_contDiff hb) z

theorem partialEta_add_pt {a b : Plane → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (z : Plane) : partialEta (fun w => a w + b w) z = partialEta a z + partialEta b z :=
  partialEta_add_eq' (lineE_of_contDiff ha) (lineE_of_contDiff hb) z

theorem partialQ_add_fun {a b : Plane → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) :
    partialQ (fun w => a w + b w) = fun w => partialQ a w + partialQ b w :=
  funext fun z => partialQ_add_pt ha hb z

theorem partialEta_add_fun {a b : Plane → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) :
    partialEta (fun w => a w + b w) = fun w => partialEta a w + partialEta b w :=
  funext fun z => partialEta_add_pt ha hb z

theorem partialQ_sub_pt {a b : Plane → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (z : Plane) : partialQ (fun w => a w - b w) z = partialQ a z - partialQ b z :=
  partialQ_sub_eq (lineQ_of_contDiff ha) (lineQ_of_contDiff hb) z

theorem partialEta_sub_pt {a b : Plane → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b)
    (z : Plane) : partialEta (fun w => a w - b w) z = partialEta a z - partialEta b z :=
  partialEta_sub_eq (lineE_of_contDiff ha) (lineE_of_contDiff hb) z

theorem partialQ_const_mul_pt (c : ℝ) (f : Plane → ℝ) (z : Plane) :
    partialQ (fun w => c * f w) z = c * partialQ f z := by
  unfold partialQ
  rw [deriv_const_mul_field']

theorem partialEta_const_mul_pt (c : ℝ) (f : Plane → ℝ) (z : Plane) :
    partialEta (fun w => c * f w) z = c * partialEta f z := by
  unfold partialEta
  rw [deriv_const_mul_field']

/-! ### Divergence of vector fields -/

theorem div_add_fld {U1 U2 : Plane → Vec} (h1 : ContDiff ℝ ∞ U1) (h2 : ContDiff ℝ ∞ U2)
    (z : Plane) :
    UnforcedLeray.Cyl.divergence (fun w => U1 w + U2 w) z =
      UnforcedLeray.Cyl.divergence U1 z + UnforcedLeray.Cyl.divergence U2 z := by
  unfold UnforcedLeray.Cyl.divergence
  simp only [PiLp.add_apply]
  rw [partialQ_add_pt (comp_contDiff h1 0) (comp_contDiff h2 0) z,
    partialEta_add_pt (comp_contDiff h1 1) (comp_contDiff h2 1) z]
  ring

theorem div_sub_fld {U1 U2 : Plane → Vec} (h1 : ContDiff ℝ ∞ U1) (h2 : ContDiff ℝ ∞ U2)
    (z : Plane) :
    UnforcedLeray.Cyl.divergence (fun w => U1 w - U2 w) z =
      UnforcedLeray.Cyl.divergence U1 z - UnforcedLeray.Cyl.divergence U2 z := by
  unfold UnforcedLeray.Cyl.divergence
  simp only [PiLp.sub_apply]
  rw [partialQ_sub_pt (comp_contDiff h1 0) (comp_contDiff h2 0) z,
    partialEta_sub_pt (comp_contDiff h1 1) (comp_contDiff h2 1) z]
  ring

theorem div_smul_fld (c : ℝ) {U : Plane → Vec} (z : Plane) :
    UnforcedLeray.Cyl.divergence (fun w => c • U w) z =
      c * UnforcedLeray.Cyl.divergence U z := by
  unfold UnforcedLeray.Cyl.divergence
  simp only [PiLp.smul_apply, smul_eq_mul]
  rw [partialQ_const_mul_pt, partialEta_const_mul_pt]
  ring

/-! ### Smoothness of the operators -/

theorem lapS_contDiff {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (lapS f) :=
  (partialQ_contDiff (partialQ_contDiff hf)).add (partialEta_contDiff (partialEta_contDiff hf))

theorem vecLap_contDiff {u : Plane → Vec} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (vecLaplacian u) :=
  UnforcedLeray.Train.toVecL.contDiff.comp
    ((lapS_contDiff (comp_contDiff hu 0)).prodMk (lapS_contDiff (comp_contDiff hu 1)))

theorem gradS_contDiff {p : Plane → ℝ} (hp : ContDiff ℝ ∞ p) : ContDiff ℝ ∞ (gradS p) :=
  UnforcedLeray.Train.toVecL.contDiff.comp ((partialQ_contDiff hp).prodMk (partialEta_contDiff hp))

theorem advection_contDiff {u : Plane → Vec} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (advection u) := by
  have h0 := comp_contDiff hu 0
  have h1 := comp_contDiff hu 1
  have hA : ContDiff ℝ ∞ (fun z => u z 0 * partialQ (fun w => u w 0) z +
      u z 1 * partialEta (fun w => u w 0) z) :=
    (h0.mul (partialQ_contDiff h0)).add (h1.mul (partialEta_contDiff h0))
  have hB : ContDiff ℝ ∞ (fun z => u z 0 * partialQ (fun w => u w 1) z +
      u z 1 * partialEta (fun w => u w 1) z) :=
    (h0.mul (partialQ_contDiff h1)).add (h1.mul (partialEta_contDiff h1))
  exact UnforcedLeray.Train.toVecL.contDiff.comp (hA.prodMk hB)

theorem matDiv_contDiff {Q : Plane → Matrix (Fin 2) (Fin 2) ℝ}
    (hQ : ∀ k l : Fin 2, ContDiff ℝ ∞ (fun w => Q w k l)) : ContDiff ℝ ∞ (matDiv Q) :=
  UnforcedLeray.Train.toVecL.contDiff.comp
    (((partialQ_contDiff (hQ 0 0)).add (partialEta_contDiff (hQ 1 0))).prodMk
      ((partialQ_contDiff (hQ 0 1)).add (partialEta_contDiff (hQ 1 1))))

/-- The periodized pressure `p_c` is `C^∞` for `c > 0`, `s ≥ 0`, via the Gaussian profile
`pExp` (`Gaussian.contDiff_periodize`, as for `Q_c`). -/
theorem pExp_gauss (a : ℝ) (z : Plane) :
    UnforcedLeray.B0113.pExp a z =
      -(a⁻¹ ^ 3) * Real.exp (-((a⁻¹ / 2) * (z.1 ^ 2 + z.2 ^ 2))) := by
  unfold UnforcedLeray.B0113.pExp UnforcedLeray.B0113.gw UnforcedLeray.GaussianVortex.radiusSq
  rw [← Real.exp_add]
  congr 2
  ring

theorem pc_contDiff {ν c s : ℝ} (hν : 0 < ν) (hc : 0 < c) (hs : 0 ≤ s) :
    ContDiff ℝ ∞ (pc ν c s) := by
  have ha : 0 < UnforcedLeray.B0113.heatWidth ν s := UnforcedLeray.B0113.heatWidth_pos hν hs
  have hfun : pc ν c s = UnforcedLeray.B0146.latticeSum c
      (UnforcedLeray.B0113.pExp (UnforcedLeray.B0113.heatWidth ν s)) := by
    rw [UnforcedLeray.Train.pc_eq, UnforcedLeray.B0146.periodicPressure_eq]
  rw [hfun]
  set a := UnforcedLeray.B0113.heatWidth ν s with ha_def
  have hg := UnforcedLeray.Short.PartI.QcSmoothAux.SchFn.gauss
    (div_pos (inv_pos.2 ha) two_pos : (0 : ℝ) < a⁻¹ / 2)
  have hS := UnforcedLeray.Short.PartI.QcSmoothAux.SchFn.const_mul hg (-(a⁻¹ ^ 3))
  have hSp : UnforcedLeray.Short.PartI.QcSmoothAux.SchFn (UnforcedLeray.B0113.pExp a) := by
    have e : UnforcedLeray.B0113.pExp a = fun z : Plane =>
        -(a⁻¹ ^ 3) * Real.exp (-((a⁻¹ / 2) * (z.1 ^ 2 + z.2 ^ 2))) :=
      funext (pExp_gauss a)
    rw [e]
    exact hS
  have hL := UnforcedLeray.Short.PartI.LatticeProfileDecay_of_SchFn hSp
  exact UnforcedLeray.Gaussian.contDiff_periodize (N := ⊤) (s := 2) (by norm_num) hc.ne' hL.1
    (fun n _ => hL.2 n)

/-! ### The time derivative of the train, componentwise -/

theorem slice_contDiff {H : PPoisson.SpT → ℝ}
    (hH : ContDiffOn ℝ ∞ H (Ioi (0 : ℝ) ×ˢ (univ : Set Plane))) {s : ℝ} (hs : 0 < s) :
    ContDiff ℝ ∞ (fun w : Plane => H (s, w)) := by
  have hf : ContDiff ℝ ∞ (fun w : Plane => ((s, w) : PPoisson.SpT)) :=
    contDiff_const.prodMk contDiff_id
  have h := hH.comp hf.contDiffOn (s := univ) (fun w _ => ⟨hs, mem_univ w⟩)
  exact contDiffOn_univ.1 h

theorem sliceT {H : PPoisson.SpT → ℝ} {t : ℝ} {w : Plane}
    (hd : DifferentiableAt ℝ H (t, w)) : deriv (fun τ => H (τ, w)) t = dirP eT H (t, w) := by
  have h1 : HasDerivAt (fun τ : ℝ => ((τ, w) : PPoisson.SpT)) eT t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t w)
  exact (hd.hasFDerivAt.comp_hasDerivAt t h1).deriv

theorem deriv_comp_apply_vec {v : ℝ → Vec} {s : ℝ} (hd : DifferentiableAt ℝ v s) (k : Fin 2) :
    deriv (fun τ => v τ k) s = deriv v s k := by
  have h := (EuclideanSpace.proj (𝕜 := ℝ) k : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt
    s hd.hasDerivAt
  exact h.deriv

theorem diff_time_vec {v : ℝ → Plane → Vec}
    (hv : ContDiffOn ℝ ∞ (fun x : PPoisson.SpT => v x.1 x.2) (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)))
    {s : ℝ} (hs : 0 < s) (w : Plane) : DifferentiableAt ℝ (fun τ => v τ w) s := by
  have hU : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)) := isOpen_Ioi.prod isOpen_univ
  have hx : ((s, w) : PPoisson.SpT) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set Plane) := ⟨hs, mem_univ w⟩
  have hd : DifferentiableAt ℝ (fun x : PPoisson.SpT => v x.1 x.2) (s, w) :=
    (hv.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hf : DifferentiableAt ℝ (fun τ : ℝ => ((τ, w) : PPoisson.SpT)) s :=
    (differentiableAt_id (x := s)).prodMk (differentiableAt_const (c := w))
  exact hd.comp s hf

theorem dt_eq {v : ℝ → Plane → Vec}
    (hv : ContDiffOn ℝ ∞ (fun x : PPoisson.SpT => v x.1 x.2) (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)))
    {s : ℝ} (hs : 0 < s) (w : Plane) :
    deriv (fun τ => v τ w) s = toVec (dirP eT (Fc v 0) (s, w), dirP eT (Fc v 1) (s, w)) := by
  have hU : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)) := isOpen_Ioi.prod isOpen_univ
  have hx : ((s, w) : PPoisson.SpT) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set Plane) := ⟨hs, mem_univ w⟩
  apply UnforcedLeray.Train.Vec.ext
  · rw [← deriv_comp_apply_vec (diff_time_vec hv hs w) 0]
    exact sliceT (smU_differentiableAt hU (smU_Fc hv 0) hx)
  · rw [← deriv_comp_apply_vec (diff_time_vec hv hs w) 1]
    exact sliceT (smU_differentiableAt hU (smU_Fc hv 1) hx)

theorem dt_contDiff {v : ℝ → Plane → Vec}
    (hv : ContDiffOn ℝ ∞ (fun x : PPoisson.SpT => v x.1 x.2) (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)))
    {s : ℝ} (hs : 0 < s) : ContDiff ℝ ∞ (fun w => deriv (fun τ => v τ w) s) := by
  have hU : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)) := isOpen_Ioi.prod isOpen_univ
  have e : (fun w => deriv (fun τ => v τ w) s) = fun w =>
      toVec (dirP eT (Fc v 0) (s, w), dirP eT (Fc v 1) (s, w)) :=
    funext fun w => dt_eq hv hs w
  rw [e]
  exact UnforcedLeray.Train.toVecL.contDiff.comp
    ((slice_contDiff (smU_dir hU (smU_Fc hv 0) eT) hs).prodMk
      (slice_contDiff (smU_dir hU (smU_Fc hv 1) eT) hs))

/-- The time derivative of a train velocity is divergence free: `div ∂ₛv = ∂ₛ div v = 0`
(mixed partials commute, `div v = 0` on `(0, ∞)`). -/
theorem div_dt_zero {v : ℝ → Plane → Vec}
    (hv : ContDiffOn ℝ ∞ (fun x : PPoisson.SpT => v x.1 x.2) (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)))
    (hdiv : ∀ t, 0 < t → ∀ w, UnforcedLeray.Cyl.divergence (v t) w = 0)
    {s : ℝ} (hs : 0 < s) (z : Plane) :
    partialQ (fun w => deriv (fun τ => v τ w 0) s) z +
      partialEta (fun w => deriv (fun τ => v τ w 1) s) z = 0 := by
  have hU : IsOpen (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)) := isOpen_Ioi.prod isOpen_univ
  have hx : ((s, z) : PPoisson.SpT) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set Plane) := ⟨hs, mem_univ z⟩
  have S0 := smU_Fc hv 0
  have S1 := smU_Fc hv 1
  have e0 : (fun w => deriv (fun τ => v τ w 0) s) = fun w => dirP eT (Fc v 0) (s, w) :=
    funext fun w => sliceT (smU_differentiableAt hU S0 (⟨hs, mem_univ w⟩ :
      ((s, w) : PPoisson.SpT) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set Plane)))
  have e1 : (fun w => deriv (fun τ => v τ w 1) s) = fun w => dirP eT (Fc v 1) (s, w) :=
    funext fun w => sliceT (smU_differentiableAt hU S1 (⟨hs, mem_univ w⟩ :
      ((s, w) : PPoisson.SpT) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set Plane)))
  rw [e0, e1]
  have hd0 : DifferentiableAt ℝ (dirP eT (Fc v 0)) (s, z) :=
    smU_differentiableAt hU (smU_dir hU S0 eT) hx
  have hd1 : DifferentiableAt ℝ (dirP eT (Fc v 1)) (s, z) :=
    smU_differentiableAt hU (smU_dir hU S1 eT) hx
  rw [sliceQ hd0, sliceE hd1, dirP_symm hU S0 hx eQ eT, dirP_symm hU S1 hx eE eT]
  rw [← dirP_add hU (smU_dir hU S0 eQ) (smU_dir hU S1 eE) hx eT]
  refine dirP_eq_zero hU ?_ hx eT
  intro y hy
  show dirP eQ (Fc v 0) y + dirP eE (Fc v 1) y = 0
  obtain ⟨t, w⟩ := y
  have ht : 0 < t := hy.1
  have d0 : DifferentiableAt ℝ (Fc v 0) (t, w) := smU_differentiableAt hU S0 hy
  have d1 : DifferentiableAt ℝ (Fc v 1) (t, w) := smU_differentiableAt hU S1 hy
  rw [← sliceQ d0, ← sliceE d1]
  exact hdiv t ht w

/-! ### The divergence of the Laplacian of a divergence free field -/

/-- `∂_q(Δf) + ∂_η(Δg) = Δ(∂_q f + ∂_η g)` for smooth scalar fields. -/
theorem divLap (f g : Plane → ℝ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (z : Plane) :
    partialQ (fun w => lapS f w) z + partialEta (fun w => lapS g w) z =
      lapS (fun w => partialQ f w + partialEta g w) z := by
  have hQf := partialQ_contDiff hf
  have hEf := partialEta_contDiff hf
  have hQg := partialQ_contDiff hg
  have hEg := partialEta_contDiff hg
  have hQQf := partialQ_contDiff hQf
  have hEEf := partialEta_contDiff hEf
  have hQQg := partialQ_contDiff hQg
  have hEEg := partialEta_contDiff hEg
  have c1 : partialQ (partialEta (partialEta f)) = partialEta (partialEta (partialQ f)) := by
    rw [partialQ_partialEta_comm (partialEta f) hEf, partialQ_partialEta_comm f hf]
  have c2 : partialEta (partialQ (partialQ g)) = partialQ (partialQ (partialEta g)) := by
    rw [← partialQ_partialEta_comm (partialQ g) hQg, ← partialQ_partialEta_comm g hg]
  unfold lapS
  rw [partialQ_add_pt hQQf hEEf z, partialEta_add_pt hQQg hEEg z]
  rw [partialQ_add_fun hQf hEg, partialEta_add_fun hQf hEg]
  rw [partialQ_add_pt (partialQ_contDiff hQf) (partialQ_contDiff hEg) z,
    partialEta_add_pt (partialEta_contDiff hQf) (partialEta_contDiff hEg) z]
  rw [c1, c2]
  ring

theorem lapS_zero_fun (z : Plane) : lapS (fun _ : Plane => (0 : ℝ)) z = 0 := by
  simp [lapS, partialQ, partialEta]

/-- The second-derivative pieces of `div Δv` cancel for a divergence free `v`. -/
theorem div_vecLap_zero {v : ℝ → Plane → Vec} {s : ℝ}
    (hvs : ContDiff ℝ ∞ (v s)) (hdiv : ∀ w, UnforcedLeray.Cyl.divergence (v s) w = 0)
    (z : Plane) : UnforcedLeray.Cyl.divergence (vecLaplacian (v s)) z = 0 := by
  have e : UnforcedLeray.Cyl.divergence (vecLaplacian (v s)) z =
      partialQ (fun w => lapS (fun u => v s u 0) w) z +
        partialEta (fun w => lapS (fun u => v s u 1) w) z := rfl
  rw [e, divLap (fun u => v s u 0) (fun u => v s u 1) (comp_contDiff hvs 0)
    (comp_contDiff hvs 1) z]
  have hz : (fun w => partialQ (fun u => v s u 0) w + partialEta (fun u => v s u 1) w) =
      fun _ => (0 : ℝ) := funext fun w => hdiv w
  rw [hz]
  exact lapS_zero_fun z

/-! ### (a) The train pressure Poisson identity -/

theorem pressure_poisson_train {ν c : ℝ} (tr : UnforcedLeray.B0140.TrainSol ν c) {s : ℝ}
    (hs : 0 < s) (z : Plane) :
    lapS (tr.p s) z + UnforcedLeray.Cyl.divergence (advection (tr.v s)) z = 0 := by
  have hvU : ContDiffOn ℝ ∞ (fun x : PPoisson.SpT => tr.v x.1 x.2)
      (Ioi (0 : ℝ) ×ˢ (univ : Set Plane)) :=
    tr.isTrain.smooth_v.mono (Set.prod_mono Ioi_subset_Ici_self Subset.rfl)
  have hvs : ContDiff ℝ ∞ (tr.v s) := contDiff_slice (f := tr.v) tr.isTrain.smooth_v hs.le
  have hps : ContDiff ℝ ∞ (tr.p s) := contDiff_slice (f := tr.p) tr.isTrain.smooth_p hs.le
  have hdiv : ∀ t, 0 < t → ∀ w, UnforcedLeray.Cyl.divergence (tr.v t) w = 0 :=
    fun t ht w => tr.isTrain.solenoidal t ht.le w
  have D1 := div_dt_zero hvU hdiv hs z
  have hDsm : ContDiff ℝ ∞ (fun w => deriv (fun τ => tr.v τ w) s) := dt_contDiff hvU hs
  have hcomp0 : ∀ w, deriv (fun τ => tr.v τ w) s 0 = deriv (fun τ => tr.v τ w 0) s :=
    fun w => (deriv_comp_apply_vec (diff_time_vec hvU hs w) 0).symm
  have hcomp1 : ∀ w, deriv (fun τ => tr.v τ w) s 1 = deriv (fun τ => tr.v τ w 1) s :=
    fun w => (deriv_comp_apply_vec (diff_time_vec hvU hs w) 1).symm
  have hD_div : UnforcedLeray.Cyl.divergence (fun w => deriv (fun τ => tr.v τ w) s) z = 0 := by
    unfold UnforcedLeray.Cyl.divergence
    simp only [hcomp0, hcomp1]
    exact D1
  have hL := div_vecLap_zero hvs (fun w => hdiv s hs w) z
  have hMz : UnforcedLeray.Cyl.divergence
      (fun w => momentumResidual ν tr.v tr.p s w) z = 0 := by
    have hfun : (fun w => momentumResidual ν tr.v tr.p s w) = fun _ => (0 : Vec) :=
      funext fun w => tr.isTrain.momentum s hs w
    rw [hfun]
    simp [UnforcedLeray.Cyl.divergence, partialQ, partialEta]
  have hX : ContDiff ℝ ∞ (fun w => deriv (fun τ => tr.v τ w) s + advection (tr.v s) w -
      ν • vecLaplacian (tr.v s) w) :=
    ((hDsm.add (advection_contDiff hvs)).sub ((vecLap_contDiff hvs).const_smul ν))
  have hG := gradS_contDiff hps
  have hsplit : UnforcedLeray.Cyl.divergence (fun w => momentumResidual ν tr.v tr.p s w) z =
      UnforcedLeray.Cyl.divergence (fun w => deriv (fun τ => tr.v τ w) s + advection (tr.v s) w -
        ν • vecLaplacian (tr.v s) w) z + UnforcedLeray.Cyl.divergence (gradS (tr.p s)) z :=
    div_add_fld hX hG z
  have hDA : ContDiff ℝ ∞ (fun w => deriv (fun τ => tr.v τ w) s + advection (tr.v s) w) :=
    hDsm.add (advection_contDiff hvs)
  have hNL : ContDiff ℝ ∞ (fun w => ν • vecLaplacian (tr.v s) w) :=
    (vecLap_contDiff hvs).const_smul ν
  have hX_div : UnforcedLeray.Cyl.divergence (fun w => deriv (fun τ => tr.v τ w) s +
      advection (tr.v s) w - ν • vecLaplacian (tr.v s) w) z =
      UnforcedLeray.Cyl.divergence (fun w => deriv (fun τ => tr.v τ w) s) z +
        UnforcedLeray.Cyl.divergence (advection (tr.v s)) z -
        ν * UnforcedLeray.Cyl.divergence (vecLaplacian (tr.v s)) z := by
    have e2 := div_sub_fld hDA hNL z
    have e3 := div_add_fld hDsm (advection_contDiff hvs) z
    have e4 := div_smul_fld ν (U := vecLaplacian (tr.v s)) z
    rw [e2, e4, e3]
  have hGdiv : UnforcedLeray.Cyl.divergence (gradS (tr.p s)) z = lapS (tr.p s) z := rfl
  rw [hX_div, hL, hD_div, hGdiv] at hsplit
  rw [hMz] at hsplit
  linarith

/-! ### (b) The gradient of the periodized pressure -/

theorem gradS_pc_eq {ν c s : ℝ} (hν : 0 < ν) (hc : c ≠ 0) (hs : 0 ≤ s) (w : Plane) :
    gradS (pc ν c s) w = matDiv (Qc ν c s) w - advection (Vc ν c s) w := by
  have h1 := UnforcedLeray.Train.Vc_residual hν hc hs w
  have h2 := (UnforcedLeray.Train.Vc_heat hν hc hs w).deriv
  unfold momentumResidual at h1
  rw [h2] at h1
  linear_combination (norm := module) h1

end UnforcedLeray.Short.PartI.ErrPressureLapAux

open UnforcedLeray.Short.PartI.ErrPressureLapAux
open UnforcedLeray.Short.PartI.TrainErrorEquation (contDiff_slice G2_of_contDiff lapS_sub_eq)
open UnforcedLeray.Train (Vc pc Qc matDiv advection gradS lapS)
/-- **Target `PartI:T08/3/3/2`** (tex lines 326-336): the pressure Poisson identity for the error. -/
theorem errPressureLap_proof : UnforcedLeray.Short.PartI.ErrPressureLap := by
  intro ν c hν hc1 tr s hs z
  have hc0 : 0 < c := by linarith
  have hc : c ≠ 0 := hc0.ne'
  have hs0 : (0 : ℝ) ≤ s := hs.le
  have hw : 0 < UnforcedLeray.Train.width ν s := by
    unfold UnforcedLeray.Train.width
    nlinarith [mul_nonneg hν.le hs0]
  have hvs : ContDiff ℝ ∞ (tr.v s) := contDiff_slice (f := tr.v) tr.isTrain.smooth_v hs0
  have hps : ContDiff ℝ ∞ (tr.p s) := contDiff_slice (f := tr.p) tr.isTrain.smooth_p hs0
  have hVc : ContDiff ℝ ∞ (Vc ν c s) := UnforcedLeray.Short.Spine.vcReg_contDiff_Vc hc0 hw
  have hpc : ContDiff ℝ ∞ (pc ν c s) := pc_contDiff hν hc0 hs0
  have hQ : ContDiff ℝ ∞ (matDiv (Qc ν c s)) :=
    matDiv_contDiff (fun k l => UnforcedLeray.Short.PartI.qcSmooth_proof ν c s hν hc0 hs0 k l)
  have hAdv1 := advection_contDiff hvs
  have hAdv2 := advection_contDiff hVc
  have hAdvDiff : ContDiff ℝ ∞ (UnforcedLeray.Short.PartI.advDiff tr s) := hAdv1.sub hAdv2
  have hG2p : UnforcedLeray.Short.PartI.TrainErrorEquation.G2 (tr.p s) :=
    G2_of_contDiff hps
  have hG2pc : UnforcedLeray.Short.PartI.TrainErrorEquation.G2 (pc ν c s) :=
    G2_of_contDiff hpc
  have hA := pressure_poisson_train tr hs z
  have hGpc : gradS (pc ν c s) = fun w => matDiv (Qc ν c s) w - advection (Vc ν c s) w :=
    funext fun w => gradS_pc_eq hν hc hs0 w
  have hLP : lapS (pc ν c s) z = UnforcedLeray.Cyl.divergence (matDiv (Qc ν c s)) z -
      UnforcedLeray.Cyl.divergence (advection (Vc ν c s)) z := by
    have e : lapS (pc ν c s) z = UnforcedLeray.Cyl.divergence (gradS (pc ν c s)) z := rfl
    rw [e, hGpc, div_sub_fld hQ hAdv2 z]
  show lapS (fun u => tr.p s u - pc ν c s u) z +
    UnforcedLeray.Cyl.divergence (fun w => UnforcedLeray.Short.PartI.advDiff tr s w + matDiv (Qc ν c s) w) z = 0
  rw [div_add_fld hAdvDiff hQ z, lapS_sub_eq hG2p hG2pc z]
  have hAD : UnforcedLeray.Cyl.divergence (UnforcedLeray.Short.PartI.advDiff tr s) z =
      UnforcedLeray.Cyl.divergence (advection (tr.v s)) z -
        UnforcedLeray.Cyl.divergence (advection (Vc ν c s)) z :=
    div_sub_fld hAdv1 hAdv2 z
  rw [hAD, hLP]
  linarith
