import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F8_1_org_2.JointSmoothUpgrade.CylP0Smooth
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F8_1_org_2.JointSmoothUpgrade.TrainJets
import UnforcedLeray.Lib.Cylinder.IBP

/-!
# Smooth Cylinder Slice Calculus: Viscous IBP, Reynolds Cancellation, and Leibniz Commutators

Support module 2 for task `PartII-b:F8/1/org/2/2/2` (`RealCylOseenMildSpatialBootstrap`).
Proves on `IsCylSmoothHInf c` slices (`0 < c`):
1. Viscous cell integration by parts `⟪∂^β W, ∂_j² ∂^β W⟫ = -‖∂_j ∂^β W‖²`.
2. Schwarz commutation `slicePdR i (slicePdR j f) = slicePdR j (slicePdR i f)`.
3. Reynolds transport cancellation `∫_{cell c} ⟪G, (V t · ∇) G⟫ = 0` for any solenoidal smooth BUC
   drift `V` (`F8Ex.IsSmoothBUCDrift c V`).
4. All-order `IsCylSmoothHInf c` closure, Leibniz product bounds, and Kato-Ponce / Friedrichs
   transport commutator bounds for `F8Ex.realBvSlice (V t) W (slicePdR 0 W) (slicePdR 1 W)`,
   yielding an `m`-dependent (`W`-independent, `t`-independent) `L²` pairing bound controlled
   purely by derivatives of `W` of order `≤ m`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.IIb.F8MildBoot

open UnforcedLeray
open UnforcedLeray.Short.IIb
open UnforcedLeray.Short.IIb.F8JointUpgrade

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

/-! ## 1. Directional Slice Derivatives, Viscous IBP, and Schwarz Symmetry -/

private lemma hasDerivAt_sliceQ_slicePdR {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h : B0579.Plane → E} (hd : Differentiable ℝ h) (q η : ℝ) :
    HasDerivAt (fun q' => h (q', η)) (fderiv ℝ h (q, η) (B0579.dir 0)) q := by
  have hs := Cyl.hasDerivAt_sliceQ hd q η
  rwa [Cyl.partialQ_eq_fderiv hd (q, η)] at hs

private lemma hasDerivAt_sliceEta_slicePdR {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h : B0579.Plane → E} (hd : Differentiable ℝ h) (q η : ℝ) :
    HasDerivAt (fun η' => h (q, η')) (fderiv ℝ h (q, η) (B0579.dir 1)) η := by
  have hs := Cyl.hasDerivAt_sliceEta hd q η
  rwa [Cyl.partialEta_eq_fderiv hd (q, η)] at hs

private lemma integrableOn_inner_cylCell {c : ℝ} {f g : B0579.Plane → F8Ex.RMerid}
    (hf : MemLp f 2 (F8Ex.cellMeas c)) (hg : MemLp g 2 (F8Ex.cellMeas c)) :
    IntegrableOn (fun y => ⟪f y, g y⟫_ℝ) (Cyl.cell c) := by
  rw [← b0579_cell_eq_cyl_cell]
  exact F8Ex.integrableOn_innerR_cell hf hg

/-- Viscous integration by parts on `Cyl.cell c` for any `IsCylSmoothHInf c` vector field:
`⟪G, ∂_j² G⟫ + ‖∂_j G‖² = 0`. -/
lemma inner_slicePdR_self_ibp {c : ℝ} (hc : 0 < c)
    {G : B0579.Plane → F8Ex.RMerid} (hG : IsCylSmoothHInf c G) (j : Fin 2) :
    ⟪toLpCell (hG.memL2 0 Fin.elim0),
      toLpCell (((hG.slicePdR j).slicePdR j).memL2 0 Fin.elim0)⟫_ℝ =
        -‖toLpCell ((hG.slicePdR j).memL2 0 Fin.elim0)‖ ^ 2 := by
  let dG := F8Ex.slicePdR j G
  let ddG := F8Ex.slicePdR j dG
  let hdG : IsCylSmoothHInf c dG := hG.slicePdR j
  let hddG : IsCylSmoothHInf c ddG := hdG.slicePdR j
  have h1 : ⟪toLpCell (hG.memL2 0 Fin.elim0),
      toLpCell (((hG.slicePdR j).slicePdR j).memL2 0 Fin.elim0)⟫_ℝ =
        ∫ y in B0579.cell c, ⟪G y, ddG y⟫_ℝ :=
    inner_toLpCell_eq (hG.memL2 0 Fin.elim0) (((hG.slicePdR j).slicePdR j).memL2 0 Fin.elim0)
  have h2 : ‖toLpCell ((hG.slicePdR j).memL2 0 Fin.elim0)‖ ^ 2 =
      ∫ y in B0579.cell c, ⟪dG y, dG y⟫_ℝ := by
    rw [← real_inner_self_eq_norm_sq, inner_toLpCell_eq]
    rfl
  let F : B0579.Plane → ℝ := fun z => ⟪G z, dG z⟫_ℝ
  let F' : B0579.Plane → ℝ := fun z => ⟪G z, ddG z⟫_ℝ + ⟪dG z, dG z⟫_ℝ
  have hiF : IntegrableOn F (Cyl.cell c) :=
    integrableOn_inner_cylCell (hG.memL2 0 Fin.elim0) (hdG.memL2 0 Fin.elim0)
  have hi1 : IntegrableOn (fun z => ⟪dG z, dG z⟫_ℝ) (Cyl.cell c) :=
    integrableOn_inner_cylCell (hdG.memL2 0 Fin.elim0) (hdG.memL2 0 Fin.elim0)
  have hi2 : IntegrableOn (fun z => ⟪G z, ddG z⟫_ℝ) (Cyl.cell c) :=
    integrableOn_inner_cylCell (hG.memL2 0 Fin.elim0) (hddG.memL2 0 Fin.elim0)
  have hiF' : IntegrableOn F' (Cyl.cell c) := hi2.add hi1
  have hd_G : Differentiable ℝ G := hG.smooth.differentiable (by simp)
  have hd_dG : Differentiable ℝ dG := hdG.smooth.differentiable (by simp)
  have hint_zero : ∫ z in Cyl.cell c, F' z = 0 := by
    fin_cases j
    · have hper : Cyl.IsPeriodic c F := fun z => by
        dsimp [F]
        rw [hG.periodic z, hdG.periodic z]
      refine Cyl.integral_cell_deriv_q_of_periodic hc hper (fun q η => ?_) hiF'
      exact (hasDerivAt_sliceQ_slicePdR hd_G q η).inner ℝ
        (hasDerivAt_sliceQ_slicePdR hd_dG q η)
    · refine Cyl.integral_cell_deriv_eta (fun q η => ?_) hiF hiF'
      exact (hasDerivAt_sliceEta_slicePdR hd_G q η).inner ℝ
        (hasDerivAt_sliceEta_slicePdR hd_dG q η)
  rw [integral_add hi2 hi1] at hint_zero
  rw [b0579_cell_eq_cyl_cell] at h1 h2
  rw [h1, h2]
  linarith [hint_zero]

/-- Viscous integration by parts at arbitrary multi-index `β` on an `IsCylSmoothHInf c` field. -/
lemma inner_slicePdIterR_ibp {c : ℝ} (hc : 0 < c)
    {f : B0579.Plane → F8Ex.RMerid} (hf : IsCylSmoothHInf c f)
    {n : ℕ} (β : Fin n → Fin 2) (j : Fin 2) :
    ⟪toLpCell (hf.memL2 n β),
      toLpCell (hf.memL2 (n + 2) (Fin.cons j (Fin.cons j β)))⟫_ℝ =
        -‖toLpCell (hf.memL2 (n + 1) (Fin.cons j β))‖ ^ 2 := by
  have hibp := inner_slicePdR_self_ibp hc (hf.slicePdIterR β) j
  have heq0 : toLpCell ((hf.slicePdIterR β).memL2 0 Fin.elim0) = toLpCell (hf.memL2 n β) :=
    toLpCell_congr_ae _ _ (ae_of_all _ fun _ => rfl)
  have heq1 : toLpCell (((hf.slicePdIterR β).slicePdR j).memL2 0 Fin.elim0) =
      toLpCell (hf.memL2 (n + 1) (Fin.cons j β)) :=
    toLpCell_congr_ae _ _ (ae_of_all _ fun _ => rfl)
  have heq2 : toLpCell ((((hf.slicePdIterR β).slicePdR j).slicePdR j).memL2 0 Fin.elim0) =
      toLpCell (hf.memL2 (n + 2) (Fin.cons j (Fin.cons j β))) :=
    toLpCell_congr_ae _ _ (ae_of_all _ fun _ => rfl)
  rwa [heq0, heq1, heq2] at hibp

/-- Schwarz symmetry of spatial partial derivatives on `C^∞` slices. -/
lemma slicePdR_comm {f : B0579.Plane → F8Ex.RMerid} (hf : ContDiff ℝ ∞ f) (i j : Fin 2) :
    F8Ex.slicePdR i (F8Ex.slicePdR j f) = F8Ex.slicePdR j (F8Ex.slicePdR i f) := by
  funext y
  ext k
  have hk_sm : ContDiff ℝ ∞ (fun z => f z k) :=
    (EuclideanSpace.proj k : F8Ex.RMerid →L[ℝ] ℝ).contDiff.comp hf
  have hpd_coord : ∀ (d : Fin 2) {g : B0579.Plane → F8Ex.RMerid}, ContDiff ℝ ∞ g →
      (fun z => F8Ex.slicePdR d g z k) = B0579.pd d (fun z => g z k) := by
    intro d g hg
    funext z
    exact (PartI.csb_fderiv_comp_apply (hg.differentiable (by simp) z) k (B0579.dir d)).symm
  have h1 : F8Ex.slicePdR i (F8Ex.slicePdR j f) y k =
      B0579.pd i (B0579.pd j (fun z => f z k)) y := by
    rw [congrFun (hpd_coord i (contDiff_slicePdR hf j)) y, hpd_coord j hf]
  have h2 : F8Ex.slicePdR j (F8Ex.slicePdR i f) y k =
      B0579.pd j (B0579.pd i (fun z => f z k)) y := by
    rw [congrFun (hpd_coord j (contDiff_slicePdR hf i)) y, hpd_coord i hf]
  rw [h1, h2]
  have hp := Sob.iterDirDeriv_perm (List.Perm.swap (B0579.dir j) (B0579.dir i) []) hk_sm
  exact congrFun hp y

/-! ## 2. Smooth Periodic Scalars, Drift Slices, and Reynolds Transport Cancellation -/

private lemma contDiff_pd_scalar {φ : B0579.Plane → ℝ} (hφ : ContDiff ℝ ∞ φ) (d : Fin 2) :
    ContDiff ℝ ∞ (B0579.pd d φ) :=
  (ContDiff.fderiv_right (m := ∞) hφ (by simp)).clm_apply contDiff_const

private lemma periodic_pd_scalar {c : ℝ} {φ : B0579.Plane → ℝ}
    (hφ : Cyl.IsPeriodic c φ) (d : Fin 2) :
    Cyl.IsPeriodic c (B0579.pd d φ) := by
  intro z
  have hshift : (fun y : B0579.Plane => φ (y + (c, 0))) = φ := by
    funext y
    have hy : y + ((c, 0) : B0579.Plane) = (y.1 + c, y.2) := by ext <;> simp
    rw [hy]
    exact hφ y
  have h := fderiv_comp_add_right (𝕜 := ℝ) (f := φ) (x := z) ((c, 0) : B0579.Plane)
  rw [hshift] at h
  have hz : z + ((c, 0) : B0579.Plane) = (z.1 + c, z.2) := by ext <;> simp
  show fderiv ℝ φ (z.1 + c, z.2) (B0579.dir d) = fderiv ℝ φ z (B0579.dir d)
  rw [← hz, ← h]

lemma driftSlice_smooth {c : ℝ} {V : ℝ → B0579.Plane → F8Ex.RMerid}
    (hV : F8Ex.IsSmoothBUCDrift c V) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 2) :
    ContDiff ℝ ∞ (V t) := by
  have h := hV.smooth.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (s := univ) (fun y _ => ⟨ht, mem_univ y⟩)
  exact contDiffOn_univ.1 h

private lemma integrableOn_bdd_mul_cell {c : ℝ} {ψ φ : B0579.Plane → ℝ}
    (hψ_cont : Continuous ψ) {M : ℝ} (_hM_nn : 0 ≤ M) (hψ_bdd : ∀ y, |ψ y| ≤ M)
    (hφ : IntegrableOn φ (Cyl.cell c)) :
    IntegrableOn (fun y => ψ y * φ y) (Cyl.cell c) := by
  refine (hφ.norm.const_mul M).mono'
    (hψ_cont.aestronglyMeasurable.mul hφ.aestronglyMeasurable) ?_
  filter_upwards [] with y
  rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hψ_bdd y) (abs_nonneg _)

/-- **Reynolds transport cancellation** on `Cyl.cell c`: for any smooth solenoidal BUC drift `V`
(`t ∈ [0, 2]`) and any `IsCylSmoothHInf c` slice `G`,
`∫_{cell c} ⟪G, V_0 • ∂_0 G + V_1 • ∂_1 G⟫ = 0`. -/
lemma integral_inner_drift_transport_zero {c : ℝ} (hc : 0 < c)
    {V : ℝ → B0579.Plane → F8Ex.RMerid} (hV : F8Ex.IsSmoothBUCDrift c V)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 2)
    {G : B0579.Plane → F8Ex.RMerid} (hG : IsCylSmoothHInf c G) :
    ∫ z in Cyl.cell c,
      ⟪G z, V t z 0 • F8Ex.slicePdR 0 G z + V t z 1 • F8Ex.slicePdR 1 G z⟫_ℝ = 0 := by
  have hVt_sm : ContDiff ℝ ∞ (V t) := driftSlice_smooth hV ht
  have hVi_sm : ∀ i : Fin 2, ContDiff ℝ ∞ (fun z => V t z i) := fun i =>
    (EuclideanSpace.proj i : F8Ex.RMerid →L[ℝ] ℝ).contDiff.comp hVt_sm
  obtain ⟨M0, hM0_nn, hM0⟩ := hV.deriv_bound 0
  obtain ⟨M1, hM1_nn, hM1⟩ := hV.deriv_bound 1
  have hVi_bdd : ∀ (i : Fin 2) (z : B0579.Plane), |V t z i| ≤ M0 := fun i z => by
    have h := hM0 t ht z
    rw [norm_iteratedFDeriv_zero] at h
    exact (Real.norm_eq_abs _).symm.trans_le ((PiLp.norm_apply_le (V t z) i).trans h)
  have hdVi_bdd : ∀ (d i : Fin 2) (z : B0579.Plane),
      |B0579.pd d (fun w => V t w i) z| ≤ M1 := fun d i z => by
    have heq : B0579.pd d (fun w => V t w i) z = F8Ex.slicePdIterR (fun _ : Fin 1 => d) (V t) z i :=
      PartI.csb_fderiv_comp_apply (hVt_sm.differentiable (by simp) z) i (B0579.dir d)
    rw [heq]
    exact (Real.norm_eq_abs _).symm.trans_le
      ((PiLp.norm_apply_le _ i).trans
        ((norm_slicePdIterR_le_iteratedFDeriv (fun _ : Fin 1 => d) hVt_sm z).trans (hM1 t ht z)))
  have hiGG : IntegrableOn (fun z => ⟪G z, G z⟫_ℝ) (Cyl.cell c) :=
    integrableOn_inner_cylCell (hG.memL2 0 Fin.elim0) (hG.memL2 0 Fin.elim0)
  have hiGdG : ∀ d : Fin 2,
      IntegrableOn (fun z => 2 * ⟪G z, F8Ex.slicePdR d G z⟫_ℝ) (Cyl.cell c) :=
    fun d => (integrableOn_inner_cylCell (hG.memL2 0 Fin.elim0)
      ((hG.slicePdR d).memL2 0 Fin.elim0)).const_mul 2
  let Fq : B0579.Plane → ℝ := fun z => V t z 0 * ⟪G z, G z⟫_ℝ
  let Fq' : B0579.Plane → ℝ := fun z =>
    B0579.pd 0 (fun w => V t w 0) z * ⟪G z, G z⟫_ℝ +
      V t z 0 * (2 * ⟪G z, F8Ex.slicePdR 0 G z⟫_ℝ)
  let Fe : B0579.Plane → ℝ := fun z => V t z 1 * ⟪G z, G z⟫_ℝ
  let Fe' : B0579.Plane → ℝ := fun z =>
    B0579.pd 1 (fun w => V t w 1) z * ⟪G z, G z⟫_ℝ +
      V t z 1 * (2 * ⟪G z, F8Ex.slicePdR 1 G z⟫_ℝ)
  have hiFq' : IntegrableOn Fq' (Cyl.cell c) :=
    (integrableOn_bdd_mul_cell (contDiff_pd_scalar (hVi_sm 0) 0).continuous
      hM1_nn (hdVi_bdd 0 0) hiGG).add
      (integrableOn_bdd_mul_cell (hVi_sm 0).continuous hM0_nn (hVi_bdd 0) (hiGdG 0))
  have hiFe : IntegrableOn Fe (Cyl.cell c) :=
    integrableOn_bdd_mul_cell (hVi_sm 1).continuous hM0_nn (hVi_bdd 1) hiGG
  have hiFe' : IntegrableOn Fe' (Cyl.cell c) :=
    (integrableOn_bdd_mul_cell (contDiff_pd_scalar (hVi_sm 1) 1).continuous
      hM1_nn (hdVi_bdd 1 1) hiGG).add
      (integrableOn_bdd_mul_cell (hVi_sm 1).continuous hM0_nn (hVi_bdd 1) (hiGdG 1))
  have hd_G : Differentiable ℝ G := hG.smooth.differentiable (by simp)
  have hint_q : ∫ z in Cyl.cell c, Fq' z = 0 := by
    have hper : Cyl.IsPeriodic c Fq := fun z => by
      dsimp [Fq]
      rw [hV.periodic t ht z, hG.periodic z]
    refine Cyl.integral_cell_deriv_q_of_periodic hc hper (fun q η => ?_) hiFq'
    have hd_v := hasDerivAt_sliceQ_slicePdR ((hVi_sm 0).differentiable (by simp)) q η
    have hd_g := (hasDerivAt_sliceQ_slicePdR hd_G q η).inner ℝ
      (hasDerivAt_sliceQ_slicePdR hd_G q η)
    refine (hd_v.mul hd_g).congr_deriv ?_
    dsimp [Fq', B0579.pd, F8Ex.slicePdR]
    rw [real_inner_comm (fderiv ℝ G (q, η) (B0579.dir 0))]
    ring
  have hint_e : ∫ z in Cyl.cell c, Fe' z = 0 := by
    refine Cyl.integral_cell_deriv_eta (fun q η => ?_) hiFe hiFe'
    have hd_v := hasDerivAt_sliceEta_slicePdR ((hVi_sm 1).differentiable (by simp)) q η
    have hd_g := (hasDerivAt_sliceEta_slicePdR hd_G q η).inner ℝ
      (hasDerivAt_sliceEta_slicePdR hd_G q η)
    refine (hd_v.mul hd_g).congr_deriv ?_
    dsimp [Fe', B0579.pd, F8Ex.slicePdR]
    rw [real_inner_comm (fderiv ℝ G (q, η) (B0579.dir 1))]
    ring
  have hdiv : ∀ z : B0579.Plane,
      B0579.pd 0 (fun w => V t w 0) z + B0579.pd 1 (fun w => V t w 1) z = 0 := by
    intro z
    have hsol := hV.solenoidal t ht z
    unfold Cyl.divergence at hsol
    rw [Cyl.partialQ_eq_fderiv ((hVi_sm 0).differentiable (by simp)) z,
      Cyl.partialEta_eq_fderiv ((hVi_sm 1).differentiable (by simp)) z] at hsol
    exact hsol
  have hpt : ∀ z : B0579.Plane,
      Fq' z + Fe' z =
        2 * ⟪G z, V t z 0 • F8Ex.slicePdR 0 G z + V t z 1 • F8Ex.slicePdR 1 G z⟫_ℝ := by
    intro z
    dsimp [Fq', Fe']
    have hz0 := hdiv z
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
    linear_combination ⟪G z, G z⟫_ℝ * hz0
  have hsum : ∫ z in Cyl.cell c, (Fq' z + Fe' z) = 0 := by
    rw [integral_add hiFq' hiFe', hint_q, hint_e, add_zero]
  simp_rw [hpt, integral_const_mul] at hsum
  linarith

/-! ## 3. Iterated Scalar Partial Derivatives, `jetNormSum`, and Inductive Leibniz/Commutator Bounds -/

/-- Iterated spatial partial derivative of a scalar function on `Plane`. -/
def pdIterScalar : {n : ℕ} → (Fin n → Fin 2) → (B0579.Plane → ℝ) → B0579.Plane → ℝ
  | 0, _, ψ => ψ
  | _ + 1, γ, ψ => B0579.pd (γ 0) (pdIterScalar (Fin.tail γ) ψ)

private lemma pdIterScalar_pd :
    ∀ {n : ℕ} (γ : Fin n → Fin 2) (d : Fin 2) (ψ : B0579.Plane → ℝ),
      pdIterScalar γ (B0579.pd d ψ) = pdIterScalar (snocIdx γ d) ψ
  | 0, _, _, _ => rfl
  | _ + 1, γ, d, ψ => by
      change B0579.pd (γ 0) (pdIterScalar (Fin.tail γ) (B0579.pd d ψ)) =
        B0579.pd (snocIdx γ d 0) (pdIterScalar (Fin.tail (snocIdx γ d)) ψ)
      rw [pdIterScalar_pd (Fin.tail γ) d ψ]
      rfl

private lemma pdIterScalar_coord_eq :
    ∀ {n : ℕ} (γ : Fin n → Fin 2) {f : B0579.Plane → F8Ex.RMerid},
      ContDiff ℝ ∞ f → ∀ (i : Fin 2) (y : B0579.Plane),
        pdIterScalar γ (fun z => f z i) y = F8Ex.slicePdIterR γ f y i
  | 0, _, _, _, _, _ => rfl
  | _ + 1, γ, f, hf, i, y => by
      have ih : pdIterScalar (Fin.tail γ) (fun z => f z i) =
          fun z => F8Ex.slicePdIterR (Fin.tail γ) f z i :=
        funext (pdIterScalar_coord_eq (Fin.tail γ) hf i)
      dsimp only [pdIterScalar, F8Ex.slicePdIterR]
      rw [ih]
      exact PartI.csb_fderiv_comp_apply
        ((contDiff_slicePdIterR hf (Fin.tail γ)).differentiable (by simp) y)
        i (B0579.dir (γ 0))

private lemma memLp_bdd_smul_cell {c : ℝ} {ψ : B0579.Plane → ℝ} (hψ_cont : Continuous ψ)
    {B : ℝ} (_hB : 0 ≤ B) (hψ_bdd : ∀ y, |ψ y| ≤ B)
    {f : B0579.Plane → F8Ex.RMerid} (hf : MemLp f 2 (F8Ex.cellMeas c)) :
    MemLp (fun y => ψ y • f y) 2 (F8Ex.cellMeas c) := by
  have hbound : ∀ᵐ y ∂(F8Ex.cellMeas c), ‖ψ y • f y‖ ≤ B * ‖f y‖ :=
    ae_of_all _ fun y => by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hψ_bdd y) (norm_nonneg _)
  exact hf.of_le_mul (hψ_cont.aestronglyMeasurable.smul hf.1) hbound

private lemma norm_toLpCell_bdd_smul_cell_le {c : ℝ} {ψ : B0579.Plane → ℝ}
    {B : ℝ} (hB : 0 ≤ B) (hψ_bdd : ∀ y, |ψ y| ≤ B)
    {f : B0579.Plane → F8Ex.RMerid} (hf : MemLp f 2 (F8Ex.cellMeas c))
    (hsmul : MemLp (fun y => ψ y • f y) 2 (F8Ex.cellMeas c)) :
    ‖toLpCell hsmul‖ ≤ B * ‖toLpCell hf‖ := by
  have he : ENNReal.ofReal ‖toLpCell hsmul‖ ≤ ENNReal.ofReal (B * ‖toLpCell hf‖) := by
    rw [ofReal_norm_toLpCell, F8Ex.cellL2R]
    have hpt : ∀ y : B0579.Plane, ‖ψ y • f y‖ ≤ ‖B • f y‖ := fun y => by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_of_nonneg hB]
      exact mul_le_mul_of_nonneg_right (hψ_bdd y) (norm_nonneg _)
    have hle := eLpNorm_mono hpt (p := 2) (μ := F8Ex.cellMeas c)
    have hrhs : eLpNorm (fun y => B • f y) 2 (F8Ex.cellMeas c) =
        ENNReal.ofReal (B * ‖toLpCell hf‖) := by
      have hmB := hf.const_smul B
      have h1 : F8Ex.cellL2R c (B • f) = ENNReal.ofReal ‖toLpCell hmB‖ :=
        (ofReal_norm_toLpCell hmB).symm
      change F8Ex.cellL2R c (B • f) = _
      rw [h1, toLpCell_smul, norm_smul, Real.norm_of_nonneg hB]
    exact hle.trans_eq hrhs
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hB (norm_nonneg _))).mp he

private lemma slicePdR_smul_scalar_field (d : Fin 2) {ψ : B0579.Plane → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    {h : B0579.Plane → F8Ex.RMerid} (hh : ContDiff ℝ ∞ h) :
    F8Ex.slicePdR d (fun y => ψ y • h y) =
      (fun y => B0579.pd d ψ y • h y) + (fun y => ψ y • F8Ex.slicePdR d h y) := by
  funext y
  have h1 : DifferentiableAt ℝ ψ y := (hψ.differentiable (by simp)) y
  have h2 : DifferentiableAt ℝ h y := (hh.differentiable (by simp)) y
  change fderiv ℝ (ψ • h) y (B0579.dir d) = _
  rw [fderiv_smul h1 h2]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, Pi.add_apply, B0579.pd]
  rw [add_comm]
  rfl

/-- Sum of `L²(cell c)` norms of all spatial partial derivatives of `g` of order `≤ m`. -/
def jetNormSum {c : ℝ} (m : ℕ) {g : B0579.Plane → F8Ex.RMerid}
    (hg : IsCylSmoothHInf c g) : ℝ :=
  ∑ k : Fin (m + 1), ∑ γ : Fin k.1 → Fin 2, ‖toLpCell (hg.memL2 k.1 γ)‖

lemma jetNormSum_nonneg {c : ℝ} (m : ℕ) {g : B0579.Plane → F8Ex.RMerid}
    (hg : IsCylSmoothHInf c g) :
    0 ≤ jetNormSum m hg :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

lemma jetNormSum_zero_eq {c : ℝ} {g : B0579.Plane → F8Ex.RMerid}
    (hg : IsCylSmoothHInf c g) :
    jetNormSum 0 hg = ‖toLpCell (hg.memL2 0 Fin.elim0)‖ := by
  unfold jetNormSum
  rw [Fin.sum_univ_one]
  have huniq : (Finset.univ : Finset (Fin 0 → Fin 2)) = {Fin.elim0} := by
    ext γ
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    exact Subsingleton.elim γ Fin.elim0
  change ∑ γ : Fin 0 → Fin 2, ‖toLpCell (hg.memL2 0 γ)‖ = _
  rw [huniq, Finset.sum_singleton]

lemma jetNormSum_le_succ {c : ℝ} (m : ℕ) {g : B0579.Plane → F8Ex.RMerid}
    (hg : IsCylSmoothHInf c g) :
    jetNormSum m hg ≤ jetNormSum (m + 1) hg := by
  unfold jetNormSum
  rw [Fin.sum_univ_castSucc (n := m + 1)]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => norm_nonneg _)

lemma jetNormSum_mono {c : ℝ} {m₁ m₂ : ℕ} (hle : m₁ ≤ m₂)
    {g : B0579.Plane → F8Ex.RMerid} (hg : IsCylSmoothHInf c g) :
    jetNormSum m₁ hg ≤ jetNormSum m₂ hg := by
  induction hle with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (jetNormSum_le_succ _ hg)

private lemma snocIdx_injective (d : Fin 2) :
    ∀ {n : ℕ}, Function.Injective (fun γ : Fin n → Fin 2 => snocIdx γ d)
  | 0, γ₁, γ₂, _ => Subsingleton.elim γ₁ γ₂
  | _ + 1, γ₁, γ₂, h => by
      have h0 : γ₁ 0 = γ₂ 0 := congrFun h 0
      have htail : snocIdx (Fin.tail γ₁) d = snocIdx (Fin.tail γ₂) d :=
        congrArg Fin.tail h
      have h1 := snocIdx_injective d htail
      rw [← Fin.cons_self_tail γ₁, ← Fin.cons_self_tail γ₂, h0, h1]

lemma jetNormSum_slicePdR_le {c : ℝ} (m : ℕ) {g : B0579.Plane → F8Ex.RMerid}
    (hg : IsCylSmoothHInf c g) (d : Fin 2) :
    jetNormSum m (hg.slicePdR d) ≤ jetNormSum (m + 1) hg := by
  have hslice : ∀ n : ℕ,
      (∑ γ : Fin n → Fin 2, ‖toLpCell ((hg.slicePdR d).memL2 n γ)‖) ≤
        ∑ α : Fin (n + 1) → Fin 2, ‖toLpCell (hg.memL2 (n + 1) α)‖ := by
    intro n
    have hcongr : ∀ γ : Fin n → Fin 2,
        ‖toLpCell ((hg.slicePdR d).memL2 n γ)‖ =
          ‖toLpCell (hg.memL2 (n + 1) (snocIdx γ d))‖ := fun γ => by
      refine congrArg norm (toLpCell_congr_ae _ _ (ae_of_all _ fun y => ?_))
      exact congrFun (slicePdIterR_slicePdR γ d g) y
    simp_rw [hcongr]
    rw [← Finset.sum_image (f := fun α => ‖toLpCell (hg.memL2 (n + 1) α)‖)
      (fun _ _ _ _ h => snocIdx_injective d h)]
    exact Finset.sum_le_univ_sum_of_nonneg fun _ => norm_nonneg _
  unfold jetNormSum
  rw [Fin.sum_univ_succ (n := m + 1)]
  exact le_add_of_nonneg_of_le (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    (Finset.sum_le_sum fun k _ => hslice k.1)

/-- Recursive Leibniz constant for `n`-th derivatives of `ψ • g` given derivative bounds `Bψ`. -/
def leibnizCoeff : (ℕ → ℝ) → ℕ → ℝ
  | Bψ, 0 => Bψ 0
  | Bψ, n + 1 => leibnizCoeff (fun k => Bψ (k + 1)) n + leibnizCoeff Bψ n

lemma leibnizCoeff_nonneg :
    ∀ {Bψ : ℕ → ℝ}, (∀ k, 0 ≤ Bψ k) → ∀ n : ℕ, 0 ≤ leibnizCoeff Bψ n
  | _, hB, 0 => hB 0
  | _, hB, n + 1 =>
      add_nonneg (leibnizCoeff_nonneg (fun k => hB (k + 1)) n) (leibnizCoeff_nonneg hB n)

/-- Inductive `MemLp` closure and `L²` Leibniz estimate for `slicePdIterR α (ψ • g)`. -/
private lemma scalar_smul_iter_memLp_and_bound {c : ℝ} :
    ∀ (n : ℕ) {ψ : B0579.Plane → ℝ} (_hψ_sm : ContDiff ℝ ∞ ψ)
      {Bψ : ℕ → ℝ} (_hBψ_nn : ∀ k, 0 ≤ Bψ k)
      (_hBψ : ∀ (k : ℕ) (γ : Fin k → Fin 2) (y : B0579.Plane), |pdIterScalar γ ψ y| ≤ Bψ k)
      {g : B0579.Plane → F8Ex.RMerid} (hg : IsCylSmoothHInf c g)
      (α : Fin n → Fin 2),
      MemLp (F8Ex.slicePdIterR α (fun y => ψ y • g y)) 2 (F8Ex.cellMeas c) ∧
      ∀ hm : MemLp (F8Ex.slicePdIterR α (fun y => ψ y • g y)) 2 (F8Ex.cellMeas c),
        ‖toLpCell hm‖ ≤ leibnizCoeff Bψ n * jetNormSum n hg
  | 0, ψ, hψ_sm, Bψ, hBψ_nn, hBψ, g, hg, α => by
      have hα : α = Fin.elim0 := Subsingleton.elim _ _
      subst hα
      dsimp only [F8Ex.slicePdIterR, leibnizCoeff]
      have hm0 : MemLp (fun y => ψ y • g y) 2 (F8Ex.cellMeas c) :=
        memLp_bdd_smul_cell hψ_sm.continuous (hBψ_nn 0) (hBψ 0 Fin.elim0) (hg.memL2 0 Fin.elim0)
      refine ⟨hm0, fun hm => ?_⟩
      rw [jetNormSum_zero_eq]
      exact norm_toLpCell_bdd_smul_cell_le (hBψ_nn 0) (hBψ 0 Fin.elim0) (hg.memL2 0 Fin.elim0) hm
  | n + 1, ψ, hψ_sm, Bψ, hBψ_nn, hBψ, g, hg, α => by
      obtain ⟨β, j, rfl⟩ := exists_snocIdx α
      have hpd_sm : ContDiff ℝ ∞ (B0579.pd j ψ) := contDiff_pd_scalar hψ_sm j
      have hpd_bdd : ∀ (k : ℕ) (γ : Fin k → Fin 2) (y : B0579.Plane),
          |pdIterScalar γ (B0579.pd j ψ) y| ≤ Bψ (k + 1) := fun k γ y => by
        rw [pdIterScalar_pd γ j ψ]
        exact hBψ (k + 1) (snocIdx γ j) y
      obtain ⟨hm1, hb1⟩ := scalar_smul_iter_memLp_and_bound n hpd_sm
        (fun k => hBψ_nn (k + 1)) hpd_bdd hg β
      obtain ⟨hm2, hb2⟩ := scalar_smul_iter_memLp_and_bound n hψ_sm
        hBψ_nn hBψ (hg.slicePdR j) β
      have hsplit : F8Ex.slicePdIterR (snocIdx β j) (fun y => ψ y • g y) =
          F8Ex.slicePdIterR β (fun y => B0579.pd j ψ y • g y) +
            F8Ex.slicePdIterR β (fun y => ψ y • F8Ex.slicePdR j g y) := by
        rw [← slicePdIterR_slicePdR β j, slicePdR_smul_scalar_field j hψ_sm hg.smooth,
          slicePdIterR_add (f := fun y => B0579.pd j ψ y • g y)
            (g := fun y => ψ y • F8Ex.slicePdR j g y)
            (hpd_sm.smul hg.smooth) (hψ_sm.smul (contDiff_slicePdR hg.smooth j)) β]
      have hma : MemLp (F8Ex.slicePdIterR (snocIdx β j) (fun y => ψ y • g y))
          2 (F8Ex.cellMeas c) := by
        rw [hsplit]
        exact hm1.add hm2
      refine ⟨hma, fun hm => ?_⟩
      have heq : toLpCell hm = toLpCell hm1 + toLpCell hm2 := by
        rw [← toLpCell_add hm1 hm2]
        exact toLpCell_congr_ae _ _ (ae_of_all _ fun y => congrFun hsplit y)
      have hle1 : leibnizCoeff (fun k => Bψ (k + 1)) n * jetNormSum n hg ≤
          leibnizCoeff (fun k => Bψ (k + 1)) n * jetNormSum (n + 1) hg :=
        mul_le_mul_of_nonneg_left (jetNormSum_le_succ n hg)
          (leibnizCoeff_nonneg (fun k => hBψ_nn (k + 1)) n)
      have hle2 : leibnizCoeff Bψ n * jetNormSum n (hg.slicePdR j) ≤
          leibnizCoeff Bψ n * jetNormSum (n + 1) hg :=
        mul_le_mul_of_nonneg_left (jetNormSum_slicePdR_le n hg j)
          (leibnizCoeff_nonneg hBψ_nn n)
      rw [heq]
      calc ‖toLpCell hm1 + toLpCell hm2‖
          ≤ ‖toLpCell hm1‖ + ‖toLpCell hm2‖ := norm_add_le _ _
        _ ≤ leibnizCoeff (fun k => Bψ (k + 1)) n * jetNormSum (n + 1) hg +
              leibnizCoeff Bψ n * jetNormSum (n + 1) hg :=
            add_le_add ((hb1 hm1).trans hle1) ((hb2 hm2).trans hle2)
        _ = leibnizCoeff Bψ (n + 1) * jetNormSum (n + 1) hg := by
            dsimp only [leibnizCoeff]; ring

lemma _root_.UnforcedLeray.Short.IIb.F8JointUpgrade.IsCylSmoothHInf.bdd_smul
    {c : ℝ} {ψ : B0579.Plane → ℝ}
    (hψ_sm : ContDiff ℝ ∞ ψ) (hψ_per : Cyl.IsPeriodic c ψ)
    {Bψ : ℕ → ℝ} (hBψ_nn : ∀ k, 0 ≤ Bψ k)
    (hBψ : ∀ (k : ℕ) (γ : Fin k → Fin 2) (y : B0579.Plane), |pdIterScalar γ ψ y| ≤ Bψ k)
    {g : B0579.Plane → F8Ex.RMerid} (hg : IsCylSmoothHInf c g) :
    IsCylSmoothHInf c (fun y => ψ y • g y) where
  smooth := hψ_sm.smul hg.smooth
  periodic z := by simp [hψ_per z, hg.periodic z]
  memL2 n α := (scalar_smul_iter_memLp_and_bound n hψ_sm hBψ_nn hBψ hg α).1

/-- Recursive Kato-Ponce / Friedrichs commutator constant for `[∂^α, ψ ∂_d]`. -/
def commCoeff : (ℕ → ℝ) → ℕ → ℝ
  | _, 0 => 0
  | Bψ, n + 1 => leibnizCoeff (fun k => Bψ (k + 1)) n + commCoeff Bψ n

lemma commCoeff_nonneg :
    ∀ {Bψ : ℕ → ℝ}, (∀ k, 0 ≤ Bψ k) → ∀ n : ℕ, 0 ≤ commCoeff Bψ n
  | _, _, 0 => le_rfl
  | _, hB, n + 1 =>
      add_nonneg (leibnizCoeff_nonneg (fun k => hB (k + 1)) n) (commCoeff_nonneg hB n)

/-- Transport commutator slice `∂^α (ψ • ∂_d g) - ψ • ∂_d (∂^α g)`. -/
def commSlice (ψ : B0579.Plane → ℝ) (d : Fin 2) (g : B0579.Plane → F8Ex.RMerid)
    {n : ℕ} (α : Fin n → Fin 2) : B0579.Plane → F8Ex.RMerid :=
  fun y => F8Ex.slicePdIterR α (fun z => ψ z • F8Ex.slicePdR d g z) y -
    ψ y • F8Ex.slicePdR d (F8Ex.slicePdIterR α g) y

private lemma commSlice_memLp_and_bound {c : ℝ} (d : Fin 2) :
    ∀ (n : ℕ) {ψ : B0579.Plane → ℝ} (_hψ_sm : ContDiff ℝ ∞ ψ)
      {Bψ : ℕ → ℝ} (_hBψ_nn : ∀ k, 0 ≤ Bψ k)
      (_hBψ : ∀ (k : ℕ) (γ : Fin k → Fin 2) (y : B0579.Plane), |pdIterScalar γ ψ y| ≤ Bψ k)
      {g : B0579.Plane → F8Ex.RMerid} (hg : IsCylSmoothHInf c g)
      (α : Fin n → Fin 2),
      MemLp (commSlice ψ d g α) 2 (F8Ex.cellMeas c) ∧
      ∀ hm : MemLp (commSlice ψ d g α) 2 (F8Ex.cellMeas c),
        ‖toLpCell hm‖ ≤ commCoeff Bψ n * jetNormSum n hg
  | 0, ψ, _, Bψ, _, _, g, hg, α => by
      have hα : α = Fin.elim0 := Subsingleton.elim _ _
      subst hα
      have hz : commSlice ψ d g Fin.elim0 = 0 := by
        funext y
        simp [commSlice, F8Ex.slicePdIterR]
      refine ⟨hz ▸ MemLp.zero, fun hm => ?_⟩
      have h0 : toLpCell hm = 0 := by
        rw [← toLpCell_zero c]
        exact toLpCell_congr_ae _ _ (ae_of_all _ fun y => congrFun hz y)
      rw [h0, norm_zero]
      simp [commCoeff]
  | n + 1, ψ, hψ_sm, Bψ, hBψ_nn, hBψ, g, hg, α => by
      obtain ⟨β, j, rfl⟩ := exists_snocIdx α
      have hpd_sm : ContDiff ℝ ∞ (B0579.pd j ψ) := contDiff_pd_scalar hψ_sm j
      have hpd_bdd : ∀ (k : ℕ) (γ : Fin k → Fin 2) (y : B0579.Plane),
          |pdIterScalar γ (B0579.pd j ψ) y| ≤ Bψ (k + 1) := fun k γ y => by
        rw [pdIterScalar_pd γ j ψ]
        exact hBψ (k + 1) (snocIdx γ j) y
      obtain ⟨hm1, hb1⟩ := scalar_smul_iter_memLp_and_bound n hpd_sm
        (fun k => hBψ_nn (k + 1)) hpd_bdd (hg.slicePdR d) β
      obtain ⟨hm2, hb2⟩ := commSlice_memLp_and_bound d n hψ_sm
        hBψ_nn hBψ (hg.slicePdR j) β
      have hrec : commSlice ψ d g (snocIdx β j) =
          F8Ex.slicePdIterR β (fun y => B0579.pd j ψ y • F8Ex.slicePdR d g y) +
            commSlice ψ d (F8Ex.slicePdR j g) β := by
        have h1 : F8Ex.slicePdIterR (snocIdx β j) (fun z => ψ z • F8Ex.slicePdR d g z) =
            F8Ex.slicePdIterR β (fun y => B0579.pd j ψ y • F8Ex.slicePdR d g y) +
              F8Ex.slicePdIterR β (fun y => ψ y • F8Ex.slicePdR d (F8Ex.slicePdR j g) y) := by
          rw [← slicePdIterR_slicePdR β j,
            slicePdR_smul_scalar_field j hψ_sm (contDiff_slicePdR hg.smooth d)]
          simp_rw [slicePdR_comm hg.smooth j d]
          exact slicePdIterR_add
            (f := fun y => B0579.pd j ψ y • F8Ex.slicePdR d g y)
            (g := fun y => ψ y • F8Ex.slicePdR d (F8Ex.slicePdR j g) y)
            (hpd_sm.smul (contDiff_slicePdR hg.smooth d))
            (hψ_sm.smul (contDiff_slicePdR (contDiff_slicePdR hg.smooth j) d)) β
        have h2 : F8Ex.slicePdIterR (snocIdx β j) g =
            F8Ex.slicePdIterR β (F8Ex.slicePdR j g) :=
          (slicePdIterR_slicePdR β j g).symm
        funext y
        unfold commSlice
        rw [congrFun h1 y, h2]
        simp only [Pi.add_apply]
        abel
      have hma : MemLp (commSlice ψ d g (snocIdx β j)) 2 (F8Ex.cellMeas c) := by
        rw [hrec]
        exact hm1.add hm2
      refine ⟨hma, fun hm => ?_⟩
      have heq : toLpCell hm = toLpCell hm1 + toLpCell hm2 := by
        rw [← toLpCell_add hm1 hm2]
        exact toLpCell_congr_ae _ _ (ae_of_all _ fun y => congrFun hrec y)
      have hle1 : leibnizCoeff (fun k => Bψ (k + 1)) n * jetNormSum n (hg.slicePdR d) ≤
          leibnizCoeff (fun k => Bψ (k + 1)) n * jetNormSum (n + 1) hg :=
        mul_le_mul_of_nonneg_left (jetNormSum_slicePdR_le n hg d)
          (leibnizCoeff_nonneg (fun k => hBψ_nn (k + 1)) n)
      have hle2 : commCoeff Bψ n * jetNormSum n (hg.slicePdR j) ≤
          commCoeff Bψ n * jetNormSum (n + 1) hg :=
        mul_le_mul_of_nonneg_left (jetNormSum_slicePdR_le n hg j)
          (commCoeff_nonneg hBψ_nn n)
      rw [heq]
      calc ‖toLpCell hm1 + toLpCell hm2‖
          ≤ ‖toLpCell hm1‖ + ‖toLpCell hm2‖ := norm_add_le _ _
        _ ≤ leibnizCoeff (fun k => Bψ (k + 1)) n * jetNormSum (n + 1) hg +
              commCoeff Bψ n * jetNormSum (n + 1) hg :=
            add_le_add ((hb1 hm1).trans hle1) ((hb2 hm2).trans hle2)
        _ = commCoeff Bψ (n + 1) * jetNormSum (n + 1) hg := by
            dsimp only [commCoeff]; ring

/-! ## 4. Rank-1 Coordinate Operators and `realBvSlice` `H^m` Pairing Estimate -/

private def rank1R (j i : Fin 2) : F8Ex.RMerid →L[ℝ] F8Ex.RMerid :=
  (EuclideanSpace.proj j : F8Ex.RMerid →L[ℝ] ℝ).smulRight (EuclideanSpace.single i (1 : ℝ))

private lemma norm_rank1R_apply_le (j i : Fin 2) (v : F8Ex.RMerid) :
    ‖rank1R j i v‖ ≤ ‖v‖ := by
  dsimp [rank1R]
  rw [norm_smul, Real.norm_eq_abs, PiLp.norm_single, norm_one, mul_one]
  exact (Real.norm_eq_abs _).symm.trans_le (PiLp.norm_apply_le v j)

private lemma slicePdIterR_comp_clm (L : F8Ex.RMerid →L[ℝ] F8Ex.RMerid) :
    ∀ {n : ℕ} (α : Fin n → Fin 2) {g : B0579.Plane → F8Ex.RMerid},
      ContDiff ℝ ∞ g →
      F8Ex.slicePdIterR α (fun y => L (g y)) = fun y => L (F8Ex.slicePdIterR α g y)
  | 0, _, _, _ => rfl
  | _ + 1, α, g, hg => by
      dsimp only [F8Ex.slicePdIterR]
      rw [slicePdIterR_comp_clm L (Fin.tail α) hg]
      funext y
      have hd : DifferentiableAt ℝ (F8Ex.slicePdIterR (Fin.tail α) g) y :=
        ((contDiff_slicePdIterR hg (Fin.tail α)).differentiable (by simp)) y
      change fderiv ℝ (L ∘ F8Ex.slicePdIterR (Fin.tail α) g) y (B0579.dir (α 0)) = _
      rw [(L.hasFDerivAt.comp y hd.hasFDerivAt).fderiv, ContinuousLinearMap.comp_apply]
      rfl

private lemma _root_.UnforcedLeray.Short.IIb.F8JointUpgrade.IsCylSmoothHInf.comp_clm
    {c : ℝ} (L : F8Ex.RMerid →L[ℝ] F8Ex.RMerid)
    {g : B0579.Plane → F8Ex.RMerid} (hg : IsCylSmoothHInf c g) :
    IsCylSmoothHInf c (fun y => L (g y)) where
  smooth := L.contDiff.comp hg.smooth
  periodic z := by simp [hg.periodic z]
  memL2 n α := by
    rw [slicePdIterR_comp_clm L α hg.smooth]
    exact L.comp_memLp' (hg.memL2 n α)

private lemma norm_toLpCell_rank1R_le {c : ℝ} (j i : Fin 2)
    {f : B0579.Plane → F8Ex.RMerid} (hf : MemLp f 2 (F8Ex.cellMeas c))
    (hLf : MemLp (fun y => rank1R j i (f y)) 2 (F8Ex.cellMeas c)) :
    ‖toLpCell hLf‖ ≤ ‖toLpCell hf‖ := by
  have he : ENNReal.ofReal ‖toLpCell hLf‖ ≤ ENNReal.ofReal ‖toLpCell hf‖ := by
    rw [ofReal_norm_toLpCell, ofReal_norm_toLpCell]
    exact eLpNorm_mono (fun y => norm_rank1R_apply_le j i (f y))
  exact (ENNReal.ofReal_le_ofReal_iff (norm_nonneg _)).mp he

private lemma jetNormSum_rank1R_le {c : ℝ} (m : ℕ) (j i : Fin 2)
    {g : B0579.Plane → F8Ex.RMerid} (hg : IsCylSmoothHInf c g) :
    jetNormSum m (hg.comp_clm (rank1R j i)) ≤ jetNormSum m hg := by
  refine Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun γ _ => ?_
  have hcongr : toLpCell ((hg.comp_clm (rank1R j i)).memL2 k.1 γ) =
      toLpCell ((rank1R j i).comp_memLp' (hg.memL2 k.1 γ)) :=
    toLpCell_congr_ae _ _ (ae_of_all _ fun y =>
      congrFun (slicePdIterR_comp_clm (rank1R j i) γ hg.smooth) y)
  rw [hcongr]
  exact norm_toLpCell_rank1R_le j i (hg.memL2 k.1 γ) _

private lemma realBvSlice_eq_decomp {V : B0579.Plane → F8Ex.RMerid}
    {W : B0579.Plane → F8Ex.RMerid} :
    F8Ex.realBvSlice V W (F8Ex.slicePdR 0 W) (F8Ex.slicePdR 1 W) =
      ((fun y => V y 0 • F8Ex.slicePdR 0 W y) + (fun y => V y 1 • F8Ex.slicePdR 1 W y)) +
        (((fun y => B0579.pd 0 (fun z => V z 0) y • rank1R 0 0 (W y)) +
            (fun y => B0579.pd 0 (fun z => V z 1) y • rank1R 0 1 (W y))) +
          ((fun y => B0579.pd 1 (fun z => V z 0) y • rank1R 1 0 (W y)) +
            (fun y => B0579.pd 1 (fun z => V z 1) y • rank1R 1 1 (W y)))) := by
  funext y
  ext k
  have hd0 : B0579.dir 0 = ((1 : ℝ), (0 : ℝ)) := rfl
  have hd1 : B0579.dir 1 = ((0 : ℝ), (1 : ℝ)) := rfl
  fin_cases k <;>
    simp [F8Ex.realBvSlice, rank1R, B0579.pd, hd0, hd1] <;> ring

/-- Time-uniform spatial derivative bound sequence extracted from `F8Ex.IsSmoothBUCDrift`. -/
private def driftBoundSeq {c : ℝ} {V : ℝ → B0579.Plane → F8Ex.RMerid}
    (hV : F8Ex.IsSmoothBUCDrift c V) (k : ℕ) : ℝ :=
  (hV.deriv_bound k).choose

private lemma driftBoundSeq_nonneg {c : ℝ} {V : ℝ → B0579.Plane → F8Ex.RMerid}
    (hV : F8Ex.IsSmoothBUCDrift c V) (k : ℕ) :
    0 ≤ driftBoundSeq hV k :=
  (hV.deriv_bound k).choose_spec.1

private lemma pdIterScalar_drift_le {c : ℝ} {V : ℝ → B0579.Plane → F8Ex.RMerid}
    (hV : F8Ex.IsSmoothBUCDrift c V) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 2)
    (i : Fin 2) (k : ℕ) (γ : Fin k → Fin 2) (y : B0579.Plane) :
    |pdIterScalar γ (fun z => V t z i) y| ≤ driftBoundSeq hV k := by
  have hVt_sm : ContDiff ℝ ∞ (V t) := driftSlice_smooth hV ht
  rw [pdIterScalar_coord_eq γ hVt_sm i y]
  exact (Real.norm_eq_abs _).symm.trans_le
    ((PiLp.norm_apply_le _ i).trans
      ((norm_slicePdIterR_le_iteratedFDeriv γ hVt_sm y).trans
        ((hV.deriv_bound k).choose_spec.2 t ht y)))

/-- **Key `H^m` commutator + Reynolds cancellation pairing estimate for `realBvSlice`**:
for every `m : ℕ`, there exists `C_m ≥ 0` depending only on `(hV, m)` (`t`-independent and
`W`-independent) such that for all `t ∈ [0, 2]` and `hW : IsCylSmoothHInf c W`,
`B := realBvSlice (V t) W (∂_0 W) (∂_1 W)` belongs to `IsCylSmoothHInf c` and satisfies
`∑_{|α| ≤ m} |⟪∂^α W, ∂^α B⟫_{L²(cell c)}| ≤ C_m ∑_{|α| ≤ m} ‖∂^α W‖²_{L²(cell c)}`. -/
theorem exists_realBvSlice_pairing_bound {c : ℝ} (hc : 0 < c)
    {V : ℝ → B0579.Plane → F8Ex.RMerid} (hV : F8Ex.IsSmoothBUCDrift c V) (m : ℕ) :
    ∃ C_m : ℝ, 0 ≤ C_m ∧
      ∀ {t : ℝ}, t ∈ Icc (0 : ℝ) 2 →
      ∀ {W : B0579.Plane → F8Ex.RMerid} (hW : IsCylSmoothHInf c W),
        ∃ hB : IsCylSmoothHInf c
            (F8Ex.realBvSlice (V t) W (F8Ex.slicePdR 0 W) (F8Ex.slicePdR 1 W)),
          (∑ k : Fin (m + 1), ∑ α : Fin k.1 → Fin 2,
            |⟪toLpCell (hW.memL2 k.1 α), toLpCell (hB.memL2 k.1 α)⟫_ℝ|) ≤
          C_m * ∑ k : Fin (m + 1), ∑ α : Fin k.1 → Fin 2,
            ‖toLpCell (hW.memL2 k.1 α)‖ ^ 2 := by
  let B₀ : ℕ → ℝ := driftBoundSeq hV
  have hB₀_nn : ∀ k, 0 ≤ B₀ k := driftBoundSeq_nonneg hV
  let B₁ : ℕ → ℝ := fun k => B₀ (k + 1)
  have hB₁_nn : ∀ k, 0 ≤ B₁ k := fun k => hB₀_nn (k + 1)
  let K_lvl : ℕ → ℝ := fun k => 2 * commCoeff B₀ k + 4 * leibnizCoeff B₁ k
  have hK_lvl_nn : ∀ k, 0 ≤ K_lvl k := fun k =>
    add_nonneg (mul_nonneg zero_le_two (commCoeff_nonneg hB₀_nn k))
      (mul_nonneg (by norm_num) (leibnizCoeff_nonneg hB₁_nn k))
  let K_sum : ℝ := ∑ k : Fin (m + 1), ∑ _α : Fin k.1 → Fin 2, K_lvl k.1
  let N_card : ℝ := ∑ k : Fin (m + 1), ∑ _α : Fin k.1 → Fin 2, (1 : ℝ)
  have hK_sum_nn : 0 ≤ K_sum :=
    Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun _ _ => hK_lvl_nn k.1
  have hN_nn : 0 ≤ N_card :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => zero_le_one
  refine ⟨K_sum * N_card, mul_nonneg hK_sum_nn hN_nn, ?_⟩
  intro t ht W hW
  have hVt_sm : ContDiff ℝ ∞ (V t) := driftSlice_smooth hV ht
  have hVt_per : Cyl.IsPeriodic c (V t) := hV.periodic t ht
  have hVi_sm : ∀ i : Fin 2, ContDiff ℝ ∞ (fun z => V t z i) := fun i =>
    (EuclideanSpace.proj i : F8Ex.RMerid →L[ℝ] ℝ).contDiff.comp hVt_sm
  have hVi_per : ∀ i : Fin 2, Cyl.IsPeriodic c (fun z => V t z i) := fun i z =>
    congrArg (fun v : F8Ex.RMerid => v i) (hVt_per z)
  have hVi_bdd : ∀ (i : Fin 2) (k : ℕ) (γ : Fin k → Fin 2) (y : B0579.Plane),
      |pdIterScalar γ (fun z => V t z i) y| ≤ B₀ k :=
    pdIterScalar_drift_le hV ht
  have hdVi_sm : ∀ d i : Fin 2, ContDiff ℝ ∞ (B0579.pd d (fun z => V t z i)) :=
    fun d i => contDiff_pd_scalar (hVi_sm i) d
  have hdVi_per : ∀ d i : Fin 2, Cyl.IsPeriodic c (B0579.pd d (fun z => V t z i)) :=
    fun d i => periodic_pd_scalar (hVi_per i) d
  have hdVi_bdd : ∀ (d i : Fin 2) (k : ℕ) (γ : Fin k → Fin 2) (y : B0579.Plane),
      |pdIterScalar γ (B0579.pd d (fun z => V t z i)) y| ≤ B₁ k := fun d i k γ y => by
    rw [pdIterScalar_pd γ d]
    exact hVi_bdd i (k + 1) (snocIdx γ d) y
  -- Smooth periodic `H^∞` proofs for the 6 summands of `realBvSlice`
  have hT0 : IsCylSmoothHInf c (fun y => V t y 0 • F8Ex.slicePdR 0 W y) :=
    (hW.slicePdR 0).bdd_smul (hVi_sm 0) (hVi_per 0) hB₀_nn (hVi_bdd 0)
  have hT1 : IsCylSmoothHInf c (fun y => V t y 1 • F8Ex.slicePdR 1 W y) :=
    (hW.slicePdR 1).bdd_smul (hVi_sm 1) (hVi_per 1) hB₀_nn (hVi_bdd 1)
  have hS : ∀ j i : Fin 2,
      IsCylSmoothHInf c (fun y => B0579.pd j (fun z => V t z i) y • rank1R j i (W y)) :=
    fun j i => (hW.comp_clm (rank1R j i)).bdd_smul
      (hdVi_sm j i) (hdVi_per j i) hB₁_nn (hdVi_bdd j i)
  have hB : IsCylSmoothHInf c
      (F8Ex.realBvSlice (V t) W (F8Ex.slicePdR 0 W) (F8Ex.slicePdR 1 W)) := by
    rw [realBvSlice_eq_decomp]
    exact (hT0.add hT1).add (((hS 0 0).add (hS 0 1)).add ((hS 1 0).add (hS 1 1)))
  refine ⟨hB, ?_⟩
  set E_W : ℝ := ∑ k : Fin (m + 1), ∑ α : Fin k.1 → Fin 2, ‖toLpCell (hW.memL2 k.1 α)‖ ^ 2
  have hE_nn : 0 ≤ E_W :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hnorm_le_sqrt : ∀ (k : Fin (m + 1)) (α : Fin k.1 → Fin 2),
      ‖toLpCell (hW.memL2 k.1 α)‖ ≤ Real.sqrt E_W := by
    intro k α
    refine Real.le_sqrt_of_sq_le ?_
    have h1 : ‖toLpCell (hW.memL2 k.1 α)‖ ^ 2 ≤
        ∑ γ : Fin k.1 → Fin 2, ‖toLpCell (hW.memL2 k.1 γ)‖ ^ 2 :=
      Finset.single_le_sum
        (f := fun γ : Fin k.1 → Fin 2 => ‖toLpCell (hW.memL2 k.1 γ)‖ ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ α)
    exact h1.trans (Finset.single_le_sum
      (f := fun j : Fin (m + 1) => ∑ γ : Fin j.1 → Fin 2, ‖toLpCell (hW.memL2 j.1 γ)‖ ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ k))
  have hjet_le : jetNormSum m hW ≤ N_card * Real.sqrt E_W := by
    calc jetNormSum m hW
        ≤ ∑ k : Fin (m + 1), ∑ _α : Fin k.1 → Fin 2, Real.sqrt E_W :=
          Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun α _ => hnorm_le_sqrt k α
      _ = N_card * Real.sqrt E_W := by
          dsimp only [N_card]
          simp_rw [Finset.sum_mul, one_mul]
  -- Bound each `(k, α)` pairing using Reynolds cancellation + commutator + stretching bounds
  have hpair_each : ∀ (k : Fin (m + 1)) (α : Fin k.1 → Fin 2),
      |⟪toLpCell (hW.memL2 k.1 α), toLpCell (hB.memL2 k.1 α)⟫_ℝ| ≤
        K_lvl k.1 * (N_card * E_W) := by
    intro k α
    set G := F8Ex.slicePdIterR α W
    have hG : IsCylSmoothHInf c G := hW.slicePdIterR α
    have hG_lp : toLpCell (hG.memL2 0 Fin.elim0) = toLpCell (hW.memL2 k.1 α) :=
      toLpCell_congr_ae _ _ (ae_of_all _ fun _ => rfl)
    -- Transport leading part `Tr y := V_0 ∂_0 G + V_1 ∂_1 G`
    let Tr : B0579.Plane → F8Ex.RMerid :=
      fun y => V t y 0 • F8Ex.slicePdR 0 G y + V t y 1 • F8Ex.slicePdR 1 G y
    have hTr_hinf : IsCylSmoothHInf c Tr :=
      ((hG.slicePdR 0).bdd_smul (hVi_sm 0) (hVi_per 0) hB₀_nn (hVi_bdd 0)).add
        ((hG.slicePdR 1).bdd_smul (hVi_sm 1) (hVi_per 1) hB₀_nn (hVi_bdd 1))
    have hTr_zero : ⟪toLpCell (hW.memL2 k.1 α), toLpCell (hTr_hinf.memL2 0 Fin.elim0)⟫_ℝ = 0 := by
      rw [inner_toLpCell_eq, b0579_cell_eq_cyl_cell]
      exact integral_inner_drift_transport_zero hc hV ht hG
    -- Commutator and stretching pieces at `(k.1, α)`
    obtain ⟨hmC0, hbC0⟩ := commSlice_memLp_and_bound 0 k.1 (hVi_sm 0) hB₀_nn (hVi_bdd 0) hW α
    obtain ⟨hmC1, hbC1⟩ := commSlice_memLp_and_bound 1 k.1 (hVi_sm 1) hB₀_nn (hVi_bdd 1) hW α
    have hbS : ∀ j i : Fin 2,
        ‖toLpCell ((hS j i).memL2 k.1 α)‖ ≤ leibnizCoeff B₁ k.1 * jetNormSum m hW := by
      intro j i
      have hb := (scalar_smul_iter_memLp_and_bound k.1 (hdVi_sm j i) hB₁_nn (hdVi_bdd j i)
        (hW.comp_clm (rank1R j i)) α).2 ((hS j i).memL2 k.1 α)
      exact hb.trans (mul_le_mul_of_nonneg_left
        ((jetNormSum_rank1R_le k.1 j i hW).trans (jetNormSum_mono (Nat.lt_succ_iff.mp k.2) hW))
        (leibnizCoeff_nonneg hB₁_nn k.1))
    have hbC0' : ‖toLpCell hmC0‖ ≤ commCoeff B₀ k.1 * jetNormSum m hW :=
      (hbC0 hmC0).trans (mul_le_mul_of_nonneg_left
        (jetNormSum_mono (Nat.lt_succ_iff.mp k.2) hW) (commCoeff_nonneg hB₀_nn k.1))
    have hbC1' : ‖toLpCell hmC1‖ ≤ commCoeff B₀ k.1 * jetNormSum m hW :=
      (hbC1 hmC1).trans (mul_le_mul_of_nonneg_left
        (jetNormSum_mono (Nat.lt_succ_iff.mp k.2) hW) (commCoeff_nonneg hB₀_nn k.1))
    let Rem : B0579.Plane → F8Ex.RMerid :=
      (commSlice (fun z => V t z 0) 0 W α + commSlice (fun z => V t z 1) 1 W α) +
        ((F8Ex.slicePdIterR α (fun y => B0579.pd 0 (fun z => V t z 0) y • rank1R 0 0 (W y)) +
            F8Ex.slicePdIterR α (fun y => B0579.pd 0 (fun z => V t z 1) y • rank1R 0 1 (W y))) +
          (F8Ex.slicePdIterR α (fun y => B0579.pd 1 (fun z => V t z 0) y • rank1R 1 0 (W y)) +
            F8Ex.slicePdIterR α (fun y => B0579.pd 1 (fun z => V t z 1) y • rank1R 1 1 (W y))))
    have hmRem : MemLp Rem 2 (F8Ex.cellMeas c) :=
      (hmC0.add hmC1).add
        ((((hS 0 0).memL2 k.1 α).add ((hS 0 1).memL2 k.1 α)).add
          (((hS 1 0).memL2 k.1 α).add ((hS 1 1).memL2 k.1 α)))
    have hB_split : F8Ex.slicePdIterR α
        (F8Ex.realBvSlice (V t) W (F8Ex.slicePdR 0 W) (F8Ex.slicePdR 1 W)) = Tr + Rem := by
      have h1 := slicePdIterR_add (hT0.add hT1).smooth
        (((hS 0 0).add (hS 0 1)).add ((hS 1 0).add (hS 1 1))).smooth α
      have h2 := slicePdIterR_add hT0.smooth hT1.smooth α
      have h3 := slicePdIterR_add ((hS 0 0).add (hS 0 1)).smooth ((hS 1 0).add (hS 1 1)).smooth α
      have h4 := slicePdIterR_add (hS 0 0).smooth (hS 0 1).smooth α
      have h5 := slicePdIterR_add (hS 1 0).smooth (hS 1 1).smooth α
      funext y
      rw [realBvSlice_eq_decomp, h1, h2, h3, h4, h5]
      dsimp only [Tr, Rem, commSlice, G, Pi.add_apply]
      abel
    have hB_lp : toLpCell (hB.memL2 k.1 α) =
        toLpCell (hTr_hinf.memL2 0 Fin.elim0) + toLpCell hmRem := by
      rw [← toLpCell_add (hTr_hinf.memL2 0 Fin.elim0) hmRem]
      exact toLpCell_congr_ae _ _ (ae_of_all _ fun y => congrFun hB_split y)
    let hmS00 := (hS 0 0).memL2 k.1 α
    let hmS01 := (hS 0 1).memL2 k.1 α
    let hmS10 := (hS 1 0).memL2 k.1 α
    let hmS11 := (hS 1 1).memL2 k.1 α
    have hRem_lp : toLpCell hmRem =
        (toLpCell hmC0 + toLpCell hmC1) +
          ((toLpCell hmS00 + toLpCell hmS01) +
            (toLpCell hmS10 + toLpCell hmS11)) := by
      change toLpCell ((hmC0.add hmC1).add ((hmS00.add hmS01).add (hmS10.add hmS11))) = _
      rw [toLpCell_add (hmC0.add hmC1) ((hmS00.add hmS01).add (hmS10.add hmS11)),
        toLpCell_add hmC0 hmC1,
        toLpCell_add (hmS00.add hmS01) (hmS10.add hmS11),
        toLpCell_add hmS00 hmS01,
        toLpCell_add hmS10 hmS11]
    have hRem_norm : ‖toLpCell hmRem‖ ≤ K_lvl k.1 * jetNormSum m hW := by
      rw [hRem_lp]
      calc ‖(toLpCell hmC0 + toLpCell hmC1) +
              ((toLpCell ((hS 0 0).memL2 k.1 α) + toLpCell ((hS 0 1).memL2 k.1 α)) +
                (toLpCell ((hS 1 0).memL2 k.1 α) + toLpCell ((hS 1 1).memL2 k.1 α)))‖
          ≤ (‖toLpCell hmC0‖ + ‖toLpCell hmC1‖) +
              ((‖toLpCell ((hS 0 0).memL2 k.1 α)‖ + ‖toLpCell ((hS 0 1).memL2 k.1 α)‖) +
                (‖toLpCell ((hS 1 0).memL2 k.1 α)‖ + ‖toLpCell ((hS 1 1).memL2 k.1 α)‖)) := by
            refine (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) ?_)
            exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (norm_add_le _ _))
        _ ≤ (commCoeff B₀ k.1 * jetNormSum m hW + commCoeff B₀ k.1 * jetNormSum m hW) +
              ((leibnizCoeff B₁ k.1 * jetNormSum m hW + leibnizCoeff B₁ k.1 * jetNormSum m hW) +
                (leibnizCoeff B₁ k.1 * jetNormSum m hW + leibnizCoeff B₁ k.1 * jetNormSum m hW)) :=
            add_le_add (add_le_add hbC0' hbC1')
              (add_le_add (add_le_add (hbS 0 0) (hbS 0 1)) (add_le_add (hbS 1 0) (hbS 1 1)))
        _ = K_lvl k.1 * jetNormSum m hW := by dsimp only [K_lvl]; ring
    rw [hB_lp, inner_add_right, hTr_zero, zero_add]
    calc |⟪toLpCell (hW.memL2 k.1 α), toLpCell hmRem⟫_ℝ|
        ≤ ‖toLpCell (hW.memL2 k.1 α)‖ * ‖toLpCell hmRem‖ := abs_real_inner_le_norm _ _
      _ ≤ Real.sqrt E_W * (K_lvl k.1 * (N_card * Real.sqrt E_W)) := by
          refine mul_le_mul (hnorm_le_sqrt k α)
            (hRem_norm.trans (mul_le_mul_of_nonneg_left hjet_le (hK_lvl_nn k.1)))
            (norm_nonneg _) (Real.sqrt_nonneg _)
      _ = K_lvl k.1 * (N_card * (Real.sqrt E_W * Real.sqrt E_W)) := by ring
      _ = K_lvl k.1 * (N_card * E_W) := by rw [Real.mul_self_sqrt hE_nn]
  calc (∑ k : Fin (m + 1), ∑ α : Fin k.1 → Fin 2,
          |⟪toLpCell (hW.memL2 k.1 α), toLpCell (hB.memL2 k.1 α)⟫_ℝ|)
      ≤ ∑ k : Fin (m + 1), ∑ _α : Fin k.1 → Fin 2, (K_lvl k.1 * (N_card * E_W)) :=
        Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun α _ => hpair_each k α
    _ = K_sum * (N_card * E_W) := by
        dsimp only [K_sum]
        simp_rw [Finset.sum_mul]
    _ = (K_sum * N_card) * E_W := by ring

end UnforcedLeray.Short.IIb.F8MildBoot
