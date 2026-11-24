import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F8_1_org_2.SpatialBootstrap.MildHeatReg
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F8_1_org_2.SpatialBootstrap.SmoothSliceCalc

/-!
# Parabolic Spatial Bootstrap (`H¹_σ → H^∞_σ`) for the Cylinder Oseen Mild Evolution

Target module for task `PartII-b:F8/1/org/2/2/2` (`RealCylOseenMildSpatialBootstrap`).
Combines:
1. `SpatialBootstrap/MildHeatReg.lean`: the double-heat-regularized Volterra Oseen evolution
   `E_oseenReg` (`ε > 0`), its smooth spatial `L2v c` derivative tower `uReg`, exact `(0, 2)` ODE,
   and `[0, 2]` `H1Sol c` convergence `E_oseenReg ε t 0 u₀ → E_oseen t 0 u₀` as `ε → 0`.
2. `SpatialBootstrap/SmoothSliceCalc.lean`: viscous cell integration by parts, exact Reynolds
   cancellation `∫_{cell c} ⟪∂^α W, (V t · ∇) ∂^α W⟫ = 0`, and all-order `H^m` commutator +
   Leibniz pairing bounds for `F8Ex.realBvSlice`.
3. `CylP0Smooth.lean` (`PartI.csr_exists_rep` + `PartI.aePeriodicEq`): period-positive (`0 < c`)
   smooth `c`-periodic representative extraction, parabolic `H^m → H^{m+1}` time-weighted energy
   gain on `(0, 2)` uniform in `ε > 0`, Riesz weak-derivative limit `ε → 0⁺`, `C((0, 2); H^k)`
   slice continuity via interpolation, and assembly of `realCylOseenMildSpatialBootstrap_proof`.
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
open UnforcedLeray.Short.IIb.F8WeakEx (H1Sol val0CLM dqCLM detaCLM freeH1CLM bvCLM E_oseen
  oseenVolterraData val0_freeH1CLM dq_freeH1CLM deta_freeH1CLM
  norm_val0CLM_le norm_freeH1CLM_le bvCLM_ae_realBvSlice continuousOn_E_oseen
  isCylSmooth_single cylSmoothToL2 inner_cylSmooth_single
  hasWeakCellDerivR_of_vecH1 hasWeakCellDerivR_congr_ae memLp_of_cylSmooth)
open UnforcedLeray.Cyl (L2v cellμ divFree P0 Vec2)
open UnforcedLeray.GaussianVortex (Plane)
open UnforcedLeray.HeatCylinder

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

/-! ## 1. `IsCylSmoothHInf` ↔ `HasIterWeakDeriv` Bridge and Pointwise Solenoidality -/

private lemma weightedToCell_of_toLp {c : ℝ} (u : L2v c)
    {F : B0579.Plane → Vec2} (hF : MemLp F 2
      (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))))
    (hFae : (u : B0579.Plane → Vec2) =ᵐ[Cyl.cellμ c] F) :
    TrainB.weightedToCellL2Isometry c (hF.toLp F) = u := by
  apply Lp.ext
  let hMP : MeasurePreserving id (Cyl.cellμ c)
      (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))) := by
    rw [← TrainB.vecH1_measure_eq_cell c]
    exact MeasurePreserving.id _
  have hcomp := Lp.coeFn_compMeasurePreserving (hF.toLp F) hMP
  have hFcell := hMP.quasiMeasurePreserving.ae hF.coeFn_toLp
  filter_upwards [hcomp, hFcell, hFae] with z hzComp hzF hzU
  calc ((Lp.compMeasurePreserving id hMP (hF.toLp F) : L2v c) : B0579.Plane → Vec2) z
      = (hF.toLp F : Lp Vec2 2
          (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ)))) z := by
          simpa [Function.comp_id] using hzComp
    _ = F z := hzF
    _ = (u : B0579.Plane → Vec2) z := hzU.symm

private lemma cyl_word_eq_map_ofFn (c : ℝ) {m : ℕ} (α : Sob.Idx 2 m) :
    (Sob.cylinder c).word α = (List.ofFn α.2).map B0579.dir := by
  change List.ofFn (fun i => (Sob.cylinder c).dir (α.2 i)) = _
  simp_rw [cyl_dir_eq_b0579]
  exact List.ofFn_comp' α.2 B0579.dir

private lemma ofFn_zero_idx {n : ℕ} (f : Fin n → Fin 2) (hn : n = 0) :
    List.ofFn f = [] := by
  subst hn
  exact List.ofFn_zero

private noncomputable def sobOfWeakTower {c : ℝ} (M : ℕ)
    (u : L2v c) (g : ∀ n : ℕ, (Fin n → Fin 2) → L2v c)
    (hg : ∀ (n : ℕ) (β : Fin n → Fin 2), HasIterWeakDeriv c (List.ofFn β) u (g n β)) :
    Cyl.H ℝ Vec2 c 0 M :=
  Sob.W.ofFields
    (D := Sob.cylinder c) (ρ := Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := Vec2)
    (k := M) (p := 2)
    (fun α => (g α.1.1 α.2 : B0579.Plane → Vec2))
    (fun α => TrainB.memLp_cell_to_weighted (g α.1.1 α.2))
    (fun α => by
      let z : Sob.Idx 2 M := Sob.Idx.zero
      have hlist0 : List.ofFn z.2 = [] := ofFn_zero_idx z.2 rfl
      have hgz : g z.1.1 z.2 = u := by
        have h0 := hg z.1.1 z.2
        rw [hlist0] at h0
        exact h0.symm
      rw [hgz, cyl_word_eq_map_ofFn]
      exact (hg α.1.1 α.2).to_sobWeakDeriv)

private lemma cellDeriv_sobOfWeakTower_ae {c : ℝ} {M : ℕ} (α : Sob.Idx 2 M)
    (u : L2v c) (g : ∀ n : ℕ, (Fin n → Fin 2) → L2v c)
    (hg : ∀ (n : ℕ) (β : Fin n → Fin 2), HasIterWeakDeriv c (List.ofFn β) u (g n β)) :
    PartI.cellDeriv c α (sobOfWeakTower M u g hg) =ᵐ[Cyl.cellμ c]
      (g α.1.1 α.2 : B0579.Plane → Vec2) := by
  have heq : TrainB.weightedToCellL2Isometry c
      (Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Vec2 M 2 α
        (sobOfWeakTower M u g hg)) = g α.1.1 α.2 := by
    unfold sobOfWeakTower
    rw [Sob.W.deriv_ofFields]
    exact weightedToCell_of_toLp _ _ (ae_of_all _ fun _ => rfl)
  unfold PartI.cellDeriv
  rw [heq]

/-- Any `L2v c` vector field possessing weak cylinder cell derivatives of all orders admits a
unique smooth `c`-periodic `IsCylSmoothHInf c` representative realizing the entire derivative
tower almost everywhere and in `L2v c`. -/
lemma exists_smooth_rep_of_iterWeak {c : ℝ} (hc : 0 < c)
    (u : L2v c) (g : ∀ n : ℕ, (Fin n → Fin 2) → L2v c)
    (hg : ∀ (n : ℕ) (β : Fin n → Fin 2), HasIterWeakDeriv c (List.ofFn β) u (g n β)) :
    ∃ W : B0579.Plane → F8Ex.RMerid,
      IsCylSmoothHInf c W ∧
      (∀ (n : ℕ) (β : Fin n → Fin 2),
        F8Ex.slicePdIterR β W =ᵐ[F8Ex.cellMeas c] (g n β : B0579.Plane → F8Ex.RMerid)) ∧
      (∀ (hW : IsCylSmoothHInf c W) (n : ℕ) (β : Fin n → Fin 2),
        toLpCell (hW.memL2 n β) = g n β) := by
  have hrep : ∀ k : ℕ, ∃ G : B0579.Plane → F8Ex.RMerid,
      ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) G ∧ Cyl.IsPeriodic c G ∧
      ∀ β : Sob.Idx 2 (k + 1),
        PartI.cellDeriv c (Sob.Idx.castLE (by omega : k + 1 ≤ k + 3) β)
          (sobOfWeakTower (k + 3) u g hg) =ᵐ[Cyl.cellμ c]
            Sob.iterD ((Sob.cylinder c).word β) G := by
    intro k
    obtain ⟨G, hGc, hGper, hGae, _⟩ :=
      PartI.csr_exists_rep c hc k (2 * (32 * c⁻¹ + 64) * 2 ^ (k + 1))
        (cylSmoothSobolevBound_pos hc k) (sobOfWeakTower (k + 3) u g hg)
    exact ⟨G, hGc, hGper, hGae⟩
  choose G hG using hrep
  have hz_eq : ∀ M : ℕ,
      g (Sob.Idx.zero : Sob.Idx 2 M).1.1 (Sob.Idx.zero : Sob.Idx 2 M).2 = u := by
    intro M
    let z : Sob.Idx 2 M := Sob.Idx.zero
    have hlist0 : List.ofFn z.2 = [] := ofFn_zero_idx z.2 rfl
    have h0 := hg z.1.1 z.2
    rw [hlist0] at h0
    exact h0.symm
  have hG_eq : ∀ k : ℕ, G k = G 0 := by
    intro k
    have haek : G k =ᵐ[Cyl.cellμ c] (u : B0579.Plane → Vec2) := by
      have hk0 := (hG k).2.2 Sob.Idx.zero
      simp only [Sob.Idx.castLE_zero, Sob.TestDomain.word_zero, Sob.iterD_nil] at hk0
      have hcd := cellDeriv_sobOfWeakTower_ae (Sob.Idx.zero : Sob.Idx 2 (k + 3)) u g hg
      rw [hz_eq (k + 3)] at hcd
      exact hk0.symm.trans hcd
    have hae0 : G 0 =ᵐ[Cyl.cellμ c] (u : B0579.Plane → Vec2) := by
      have h00 := (hG 0).2.2 Sob.Idx.zero
      simp only [Sob.Idx.castLE_zero, Sob.TestDomain.word_zero, Sob.iterD_nil] at h00
      have hcd := cellDeriv_sobOfWeakTower_ae (Sob.Idx.zero : Sob.Idx 2 3) u g hg
      rw [hz_eq 3] at hcd
      exact h00.symm.trans hcd
    exact PartI.aePeriodicEq c hc (G k) (G 0) (hG k).1.continuous (hG 0).1.continuous
      (hG k).2.1 (hG 0).2.1 (haek.trans hae0.symm)
  have hG0_sm : ContDiff ℝ ∞ (G 0) :=
    contDiff_infty.mpr fun n => by
      rw [← hG_eq n]
      exact (hG n).1.of_le (by exact_mod_cast Nat.le_succ n)
  have hG0_ae_cellμ : ∀ (n : ℕ) (β : Fin n → Fin 2),
      F8Ex.slicePdIterR β (G 0) =ᵐ[Cyl.cellμ c] (g n β : B0579.Plane → Vec2) := by
    intro n β
    let idx : Sob.Idx 2 (n + 1) := ⟨⟨n, by omega⟩, β⟩
    have hn := (hG n).2.2 idx
    rw [iterD_word_eq_slicePdIterR, hG_eq n] at hn
    exact hn.symm.trans
      (cellDeriv_sobOfWeakTower_ae (Sob.Idx.castLE (by omega : n + 1 ≤ n + 3) idx) u g hg)
  have hG0_hinf : IsCylSmoothHInf c (G 0) :=
    ⟨hG0_sm, (hG 0).2.1, fun n β =>
      memLp_of_cellμ ((Lp.memLp (g n β)).ae_eq (hG0_ae_cellμ n β).symm)⟩
  refine ⟨G 0, hG0_hinf, fun n β => ?_, fun hW n β => ?_⟩
  · rw [F8JointUpgrade.cellMeas_eq_cellμ]
    exact hG0_ae_cellμ n β
  · apply Lp.ext
    exact (coeFn_toLpCell (hW.memL2 n β)).trans (hG0_ae_cellμ n β)

private lemma isCylSmooth_smul_test {c : ℝ} {u : B0579.Plane → F8Ex.RMerid}
    (hu_sm : ContDiff ℝ ∞ u) (hu_per : Cyl.IsPeriodic c u)
    {φ : B0579.Plane → ℝ} (hφ : Sob.IsCylTest c φ) :
    Sob.IsCylSmooth c (fun z => φ z • u z) where
  smooth := hφ.smooth.smul hu_sm
  periodic z := by
    have hz : z + ((c, 0) : B0579.Plane) = (z.1 + c, z.2) := by ext <;> simp
    rw [hφ.periodic z, hz, hu_per z]
  bounded := by
    obtain ⟨R, hR⟩ := hφ.bounded
    exact ⟨R, fun z hz => by rw [hR z hz, zero_smul]⟩

/-- Every `IsCylSmoothHInf c` slice has `slicePdR j G` as its weak `L2v c` cell derivative. -/
lemma hasWeakDeriv1_of_isCylSmoothHInf {c : ℝ} (hc : 0 < c)
    {G : B0579.Plane → F8Ex.RMerid} (hG : IsCylSmoothHInf c G) (j : Fin 2) :
    HasWeakDeriv1 c j (toLpCell (hG.memL2 0 Fin.elim0))
      (toLpCell ((hG.slicePdR j).memL2 0 Fin.elim0)) := by
  have hsob : Sob.HasWeakDeriv (Sob.cylinder c) [B0579.dir j] G (F8Ex.slicePdR j G) := by
    have hdG : IsCylSmoothHInf c (F8Ex.slicePdR j G) := hG.slicePdR j
    refine ⟨fun φ hφ =>
        (isCylSmooth_smul_test hG.smooth hG.periodic
          ((Sob.cylinder c).deriv_mem hφ (B0579.dir j))).integrableOn,
      fun φ hφ => (isCylSmooth_smul_test hdG.smooth hdG.periodic hφ).integrableOn,
      fun φ hφ => ?_⟩
    have hφ' : Sob.IsCylTest c φ := hφ
    have hd : ∀ z, fderiv ℝ (fun y => φ y • G y) z (B0579.dir j) =
        fderiv ℝ φ z (B0579.dir j) • G z + φ z • F8Ex.slicePdR j G z := by
      intro z
      have h1 : DifferentiableAt ℝ φ z := (hφ'.smooth.differentiable (by simp)) z
      have h2 : DifferentiableAt ℝ G z := (hG.smooth.differentiable (by simp)) z
      show fderiv ℝ (φ • G) z (B0579.dir j) = _
      rw [fderiv_smul h1 h2]
      simp only [_root_.add_apply, _root_.smul_apply,
        ContinuousLinearMap.smulRight_apply]
      rw [add_comm]
      rfl
    have h0 := Sob.integral_cylCell_fderiv_eq_zero hc
      (isCylSmooth_smul_test hG.smooth hG.periodic hφ') (B0579.dir j)
    simp_rw [hd] at h0
    have i1 : IntegrableOn (fun z => fderiv ℝ φ z (B0579.dir j) • G z) (Sob.cylCell c) :=
      (isCylSmooth_smul_test hG.smooth hG.periodic (hφ'.dirDeriv (B0579.dir j))).integrableOn
    have i2 : IntegrableOn (fun z => φ z • F8Ex.slicePdR j G z) (Sob.cylCell c) :=
      (isCylSmooth_smul_test hdG.smooth hdG.periodic hφ').integrableOn
    rw [integral_add i1 i2, add_eq_zero_iff_eq_neg] at h0
    simp only [Sob.iterDirDeriv_singleton, Sob.cylinder_μ, List.length_singleton, pow_one,
      neg_smul, one_smul]
    exact h0
  have hae0 : G =ᵐ[(Sob.cylinder c).μ]
      (toLpCell (hG.memL2 0 Fin.elim0) : B0579.Plane → Vec2) := by
    rw [Cyl.cylinder_μ_eq]
    exact (coeFn_toLpCell (hG.memL2 0 Fin.elim0)).symm
  have hae1 : F8Ex.slicePdR j G =ᵐ[(Sob.cylinder c).μ]
      (toLpCell ((hG.slicePdR j).memL2 0 Fin.elim0) : B0579.Plane → Vec2) := by
    rw [Cyl.cylinder_μ_eq]
    exact (coeFn_toLpCell ((hG.slicePdR j).memL2 0 Fin.elim0)).symm
  exact (hasWeakCellDerivR_of_vecH1 _ _ j).2 (hsob.congr_ae hae0 hae1)

/-- Iterated weak derivative compatibility for any `IsCylSmoothHInf c` slice. -/
lemma hasIterWeakDeriv_of_isCylSmoothHInf {c : ℝ} (hc : 0 < c)
    {G : B0579.Plane → F8Ex.RMerid} (hG : IsCylSmoothHInf c G) :
    ∀ {n : ℕ} (β : Fin n → Fin 2),
      HasIterWeakDeriv c (List.ofFn β)
        (toLpCell (hG.memL2 0 Fin.elim0)) (toLpCell (hG.memL2 n β))
  | 0, β => by
      have hsub : β = Fin.elim0 := Subsingleton.elim _ _
      subst hsub
      rfl
  | n + 1, β => by
      rw [List.ofFn_succ]
      refine ⟨toLpCell (hG.memL2 n (Fin.tail β)),
        hasIterWeakDeriv_of_isCylSmoothHInf hc hG (Fin.tail β), ?_⟩
      have hw := hasWeakDeriv1_of_isCylSmoothHInf hc (hG.slicePdIterR (Fin.tail β)) (β 0)
      have heq0 : toLpCell ((hG.slicePdIterR (Fin.tail β)).memL2 0 Fin.elim0) =
          toLpCell (hG.memL2 n (Fin.tail β)) :=
        toLpCell_congr_ae _ _ (ae_of_all _ fun _ => rfl)
      have heq1 : toLpCell (((hG.slicePdIterR (Fin.tail β)).slicePdR (β 0)).memL2 0 Fin.elim0) =
          toLpCell (hG.memL2 (n + 1) β) :=
        toLpCell_congr_ae _ _ (ae_of_all _ fun _ => rfl)
      rwa [heq0, heq1] at hw

/-- Any `IsCylSmoothHInf c` slice lying in `Cyl.divFree c` has pointwise zero divergence on `ℝ²`. -/
lemma div_free_of_isCylSmoothHInf {c : ℝ} (hc : 0 < c)
    {W : B0579.Plane → F8Ex.RMerid} (hW : IsCylSmoothHInf c W)
    (hdiv : toLpCell (hW.memL2 0 Fin.elim0) ∈ divFree c) :
    ∀ y : B0579.Plane, F8Ex.slicePdR 0 W y 0 + F8Ex.slicePdR 1 W y 1 = 0 := by
  have hsol : F8Ex.IsRealCellSolenoidal c W :=
    (toLpCell_mem_divFree_iff (hW.memL2 0 Fin.elim0)).mp hdiv
  have hw0 : F8Ex.HasWeakCellDerivR c 0 (fun y => W y 0) (fun y => F8Ex.slicePdR 0 W y 0) :=
    hasWeakCellDerivR_congr_ae
      ((coeFn_toLpCell_cellMeas (hW.memL2 0 Fin.elim0)).mono fun _ hy =>
        congrArg (fun v : F8Ex.RMerid => v 0) hy)
      ((coeFn_toLpCell_cellMeas ((hW.slicePdR 0).memL2 0 Fin.elim0)).mono fun _ hy =>
        congrArg (fun v : F8Ex.RMerid => v 0) hy)
      (hasWeakDeriv1_of_isCylSmoothHInf hc hW 0 0)
  have hw1 : F8Ex.HasWeakCellDerivR c 1 (fun y => W y 1) (fun y => F8Ex.slicePdR 1 W y 1) :=
    hasWeakCellDerivR_congr_ae
      ((coeFn_toLpCell_cellMeas (hW.memL2 0 Fin.elim0)).mono fun _ hy =>
        congrArg (fun v : F8Ex.RMerid => v 1) hy)
      ((coeFn_toLpCell_cellMeas ((hW.slicePdR 1).memL2 0 Fin.elim0)).mono fun _ hy =>
        congrArg (fun v : F8Ex.RMerid => v 1) hy)
      (hasWeakDeriv1_of_isCylSmoothHInf hc hW 1 1)
  let d : B0579.Plane → ℝ := fun y => F8Ex.slicePdR 0 W y 0 + F8Ex.slicePdR 1 W y 1
  have hm0 : MemLp (fun y => F8Ex.slicePdR 0 W y 0) 2 (Sob.cylinder c).μ := by
    rw [Cyl.cylinder_μ_eq, ← F8JointUpgrade.cellMeas_eq_cellμ]
    exact (EuclideanSpace.proj (0 : Fin 2) : Vec2 →L[ℝ] ℝ).comp_memLp'
      ((hW.slicePdR 0).memL2 0 Fin.elim0)
  have hm1 : MemLp (fun y => F8Ex.slicePdR 1 W y 1) 2 (Sob.cylinder c).μ := by
    rw [Cyl.cylinder_μ_eq, ← F8JointUpgrade.cellMeas_eq_cellμ]
    exact (EuclideanSpace.proj (1 : Fin 2) : Vec2 →L[ℝ] ℝ).comp_memLp'
      ((hW.slicePdR 1).memL2 0 Fin.elim0)
  have hd_ae : d =ᵐ[Cyl.cellμ c] 0 := by
    rw [← Cyl.cylinder_μ_eq]
    refine (Sob.cylinder c).ae_zero d ((hm0.add hm1).locallyIntegrable (by norm_num)) fun φ hφ => ?_
    have hφb : B0579.IsCylTest c φ := F8JointUpgrade.isCylTest_iff_b0579.mp hφ
    have hi_w0 := (hw0.1 φ hφb).1
    have hi_d0 := (hw0.1 φ hφb).2
    have hi_w1 := (hw1.1 φ hφb).1
    have hi_d1 := (hw1.1 φ hφb).2
    have heq0 := hw0.2 φ hφb
    have heq1 := hw1.2 φ hφb
    have heq_sol := (hsol φ hφb).2
    rw [integral_add hi_w0 hi_w1] at heq_sol
    have hsum_d : ∫ y in B0579.cell c, d y * φ y = 0 := by
      have hfn : (fun y => d y * φ y) =
          fun y => F8Ex.slicePdR 0 W y 0 * φ y + F8Ex.slicePdR 1 W y 1 * φ y := by
        funext y; dsimp [d]; ring
      rw [hfn, integral_add hi_d0 hi_d1]
      linarith [heq0, heq1, heq_sol]
    rw [Cyl.cylinder_μ_eq]
    change ∫ y in Cyl.cell c, φ y * d y = 0
    rw [← F8JointUpgrade.b0579_cell_eq_cyl_cell]
    have hcomm : (fun y => φ y * d y) = fun y => d y * φ y := by funext y; ring
    rwa [hcomm]
  let D : B0579.Plane → F8Ex.RMerid := fun y => d y • F8Ex.eR0
  have hD_cont : Continuous D := by
    have hc0 : Continuous (fun y => F8Ex.slicePdR 0 W y 0) :=
      (EuclideanSpace.proj (0 : Fin 2) : Vec2 →L[ℝ] ℝ).continuous.comp
        (hW.slicePdR 0).smooth.continuous
    have hc1 : Continuous (fun y => F8Ex.slicePdR 1 W y 1) :=
      (EuclideanSpace.proj (1 : Fin 2) : Vec2 →L[ℝ] ℝ).continuous.comp
        (hW.slicePdR 1).smooth.continuous
    exact (hc0.add hc1).smul continuous_const
  have hD_per : Cyl.IsPeriodic c D := fun y => by
    dsimp [D, d]
    rw [(hW.slicePdR 0).periodic y, (hW.slicePdR 1).periodic y]
  have hD_ae : D =ᵐ[Cyl.cellμ c] (0 : B0579.Plane → F8Ex.RMerid) := by
    filter_upwards [hd_ae] with y hy
    change d y • F8Ex.eR0 = 0
    have hy0 : d y = 0 := hy
    rw [hy0, zero_smul]
  have hD_zero : D = 0 :=
    PartI.aePeriodicEq c hc D 0 hD_cont continuous_const hD_per (fun _ => rfl) hD_ae
  intro y
  have hy := congrArg (fun v : F8Ex.RMerid => v 0) (congrFun hD_zero y)
  simpa [D, d, F8Ex.eR0] using hy

/-! ## 2. Regularized `H^m` Energy Inequality and Uniform Parabolic Gain on `(0, 2)` -/

/-- Squared `H^m(cell c)` norm of the regularized Oseen derivative tower `uReg` at `(ε, t)`. -/
def HkEnergy {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν)
    {V : ℝ → Plane → F8Ex.RMerid} (hV : F8Ex.IsSmoothBUCDrift c V)
    (u₀ : H1Sol c) (ε : ℝ) (m : ℕ) (t : ℝ) : ℝ :=
  ∑ k : Fin (m + 1), ∑ α : Fin k.1 → Fin 2,
    ‖uReg hc hν hV u₀ ε (List.ofFn α) t‖ ^ 2

lemma HkEnergy_nonneg {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν)
    {V : ℝ → Plane → F8Ex.RMerid} (hV : F8Ex.IsSmoothBUCDrift c V)
    (u₀ : H1Sol c) (ε : ℝ) (m : ℕ) (t : ℝ) :
    0 ≤ HkEnergy hc hν hV u₀ ε m t :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma norm_uReg_sq_le_HkEnergy {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν)
    {V : ℝ → Plane → F8Ex.RMerid} (hV : F8Ex.IsSmoothBUCDrift c V)
    (u₀ : H1Sol c) (ε : ℝ) (α : List (Fin 2)) (t : ℝ) :
    ‖uReg hc hν hV u₀ ε α t‖ ^ 2 ≤ HkEnergy hc hν hV u₀ ε α.length t := by
  have hl : uReg hc hν hV u₀ ε α t = uReg hc hν hV u₀ ε (List.ofFn α.get) t := by
    rw [List.ofFn_get]
  rw [hl]
  have h1 : ‖uReg hc hν hV u₀ ε (List.ofFn α.get) t‖ ^ 2 ≤
      ∑ γ : Fin α.length → Fin 2, ‖uReg hc hν hV u₀ ε (List.ofFn γ) t‖ ^ 2 :=
    Finset.single_le_sum
      (f := fun γ : Fin α.length → Fin 2 => ‖uReg hc hν hV u₀ ε (List.ofFn γ) t‖ ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ α.get)
  exact h1.trans (Finset.single_le_sum
    (f := fun k : Fin (α.length + 1) =>
      ∑ γ : Fin k.1 → Fin 2, ‖uReg hc hν hV u₀ ε (List.ofFn γ) t‖ ^ 2)
    (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
    (Finset.mem_univ (Fin.last α.length)))

private lemma sum_fin_zero_eq (g : ∀ n : ℕ, (Fin n → Fin 2) → ℝ)
    {z : ℕ} (hz : z = 0) :
    (∑ β : Fin z → Fin 2, g z β) = g 0 Fin.elim0 := by
  subst hz
  rw [Fintype.sum_unique]
  exact congrArg (g 0) (Subsingleton.elim _ _)

private lemma list_ofFn_cons {n : ℕ} (j : Fin 2) (β : Fin n → Fin 2) :
    List.ofFn (Fin.cons j β) = j :: List.ofFn β := by
  rw [List.ofFn_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

private lemma aeEq_cellμ_of_cellMeas {c : ℝ} {f₁ f₂ : Plane → Vec2}
    (h : f₁ =ᵐ[F8Ex.cellMeas c] f₂) : f₁ =ᵐ[Cyl.cellμ c] f₂ := by
  rwa [← F8JointUpgrade.cellMeas_eq_cellμ]

private lemma sum_cons_fin2 (g : ∀ n : ℕ, (Fin n → Fin 2) → ℝ) (m : ℕ) :
    (∑ k : Fin (m + 1), ∑ α : Fin k.1 → Fin 2,
      (g (k.1 + 1) (Fin.cons 0 α) + g (k.1 + 1) (Fin.cons 1 α))) =
    (∑ k : Fin (m + 2), ∑ β : Fin k.1 → Fin 2, g k.1 β) - g 0 Fin.elim0 := by
  have hstep : ∀ n : ℕ,
      (∑ β : Fin (n + 1) → Fin 2, g (n + 1) β) =
        ∑ α : Fin n → Fin 2, (g (n + 1) (Fin.cons 0 α) + g (n + 1) (Fin.cons 1 α)) := by
    intro n
    rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Fin 2)).sum_comp, Fintype.sum_prod_type]
    change (∑ j : Fin 2, ∑ α : Fin n → Fin 2, g (n + 1) (Fin.cons j α)) = _
    rw [Fin.sum_univ_two, ← Finset.sum_add_distrib]
  have htop : (∑ k : Fin (m + 2), ∑ β : Fin k.1 → Fin 2, g k.1 β) =
      g 0 Fin.elim0 + ∑ k : Fin (m + 1), ∑ β : Fin (k.1 + 1) → Fin 2, g (k.1 + 1) β := by
    rw [Fin.sum_univ_succ]
    congr 1
    exact sum_fin_zero_eq g (Fin.val_zero (m + 2))
  rw [htop]
  simp_rw [hstep]
  ring

private lemma egc_anti_Icc {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hc : ContinuousOn g (Icc a b))
    (hd : ∀ x ∈ Ioo a b, ∃ D : ℝ, HasDerivAt g D x ∧ D ≤ 0) : g b ≤ g a := by
  have hint : interior (Icc a b) = Ioo a b := interior_Icc
  have hanti : AntitoneOn g (Icc a b) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc a b) hc ?_ ?_
    · rw [hint]
      intro x hx
      obtain ⟨D, hD, _⟩ := hd x hx
      exact hD.differentiableAt.differentiableWithinAt
    · intro x hx
      rw [hint] at hx
      obtain ⟨D, hD, hle⟩ := hd x hx
      rw [hD.deriv]
      exact hle
  exact hanti ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab

/-- Exact `t`-differentiability and uniform-in-`ε` differential inequality for `HkEnergy` on `(0, 2)`:
for each `m : ℕ`, there exists `K_m ≥ 0` (independent of `ε, t, u₀`) such that for every `ε > 0`
and `t ∈ (0, 2)`, `HkEnergy ε m` has derivative `D` at `t` satisfying
`D ≤ -2 * ν * HkEnergy ε (m + 1) t + K_m * HkEnergy ε m t`. -/
lemma exists_hasDerivAt_HkEnergy_bound {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν)
    {V : ℝ → Plane → F8Ex.RMerid} (hV : F8Ex.IsSmoothBUCDrift c V)
    (u₀ : H1Sol c) (m : ℕ) :
    ∃ K_m : ℝ, 0 ≤ K_m ∧
      ∀ {ε : ℝ}, 0 < ε → ∀ {t : ℝ}, t ∈ Ioo (0 : ℝ) 2 →
        ∃ D : ℝ, HasDerivAt (HkEnergy hc hν hV u₀ ε m) D t ∧
          D ≤ -2 * ν * HkEnergy hc hν hV u₀ ε (m + 1) t +
            K_m * HkEnergy hc hν hV u₀ ε m t := by
  obtain ⟨C_m, hC_nn, hC_pair⟩ := exists_realBvSlice_pairing_bound hc hV m
  refine ⟨2 * C_m + 2 * ν, by positivity, ?_⟩
  intro ε hε t ht
  have ht_ioc : t ∈ Ioc (0 : ℝ) 2 := ⟨ht.1, ht.2.le⟩
  have ht_icc : t ∈ Icc (0 : ℝ) 2 := ⟨ht.1.le, ht.2.le⟩
  -- Differentiate each `‖uReg ε (List.ofFn α) s‖^2` on `(0, 2)`
  let rhs (α : List (Fin 2)) : L2v c :=
    ν • (uReg hc hν hV u₀ ε (0 :: 0 :: α) t + uReg hc hν hV u₀ ε (1 :: 1 :: α) t) -
      P0 c (iterDHeatCLM hc α ε (fReg hc hν hV u₀ ε t))
  have hd_term : ∀ (k : Fin (m + 1)) (α : Fin k.1 → Fin 2),
      HasDerivAt (fun s => ‖uReg hc hν hV u₀ ε (List.ofFn α) s‖ ^ 2)
        (2 * ⟪uReg hc hν hV u₀ ε (List.ofFn α) t, rhs (List.ofFn α)⟫_ℝ) t := by
    intro k α
    have hd_u := hasDerivAt_uReg hc hν hV u₀ hε (List.ofFn α) ht
    have hd_in := hd_u.inner ℝ hd_u
    have hfn : (fun s => ‖uReg hc hν hV u₀ ε (List.ofFn α) s‖ ^ 2) =
        fun s => ⟪uReg hc hν hV u₀ ε (List.ofFn α) s,
          uReg hc hν hV u₀ ε (List.ofFn α) s⟫_ℝ := by
      funext s
      exact (real_inner_self_eq_norm_sq _).symm
    rw [hfn]
    refine hd_in.congr_deriv ?_
    have hsym := real_inner_comm (rhs (List.ofFn α)) (uReg hc hν hV u₀ ε (List.ofFn α) t)
    dsimp only [rhs] at hsym ⊢
    linarith [hsym]
  have hd_E : HasDerivAt (HkEnergy hc hν hV u₀ ε m)
      (∑ k : Fin (m + 1), ∑ α : Fin k.1 → Fin 2,
        2 * ⟪uReg hc hν hV u₀ ε (List.ofFn α) t, rhs (List.ofFn α)⟫_ℝ) t := by
    unfold HkEnergy
    exact HasDerivAt.fun_sum fun k _ => HasDerivAt.fun_sum fun α _ => hd_term k α
  refine ⟨_, hd_E, ?_⟩
  -- 1. Viscous term identity via smooth representative `U_sm` of `uReg ε · t`
  obtain ⟨U_sm, hU_sm, _, hU_lp⟩ := exists_smooth_rep_of_iterWeak hc
    (val0CLM c (E_oseenReg hc hν hV ε t 0 u₀))
    (fun _ β => uReg hc hν hV u₀ ε (List.ofFn β) t)
    (fun _ β => hasIterWeakDeriv_uReg hc hν hV u₀ hε (List.ofFn β) ht_ioc)
  have hvisc_term : ∀ (k : Fin (m + 1)) (α : Fin k.1 → Fin 2) (j : Fin 2),
      ⟪uReg hc hν hV u₀ ε (List.ofFn α) t,
        uReg hc hν hV u₀ ε (j :: j :: List.ofFn α) t⟫_ℝ =
          -‖uReg hc hν hV u₀ ε (List.ofFn (Fin.cons j α)) t‖ ^ 2 := by
    intro k α j
    have hl1 : List.ofFn (Fin.cons j α) = j :: List.ofFn α := list_ofFn_cons j α
    have hl2 : List.ofFn (Fin.cons j (Fin.cons j α)) = j :: j :: List.ofFn α :=
      (list_ofFn_cons j _).trans (congrArg (j :: ·) hl1)
    rw [← hl2, ← hU_lp hU_sm k.1 α, ← hU_lp hU_sm (k.1 + 2) (Fin.cons j (Fin.cons j α)),
      ← hU_lp hU_sm (k.1 + 1) (Fin.cons j α)]
    exact inner_slicePdIterR_ibp hc hU_sm α j
  have hvisc_sum :
      (∑ k : Fin (m + 1), ∑ α : Fin k.1 → Fin 2,
        2 * ⟪uReg hc hν hV u₀ ε (List.ofFn α) t,
          ν • (uReg hc hν hV u₀ ε (0 :: 0 :: List.ofFn α) t +
            uReg hc hν hV u₀ ε (1 :: 1 :: List.ofFn α) t)⟫_ℝ) =
      -2 * ν * HkEnergy hc hν hV u₀ ε (m + 1) t +
        2 * ν * ‖uReg hc hν hV u₀ ε (List.ofFn (Fin.elim0 : Fin 0 → Fin 2)) t‖ ^ 2 := by
    have hpt : ∀ (k : Fin (m + 1)) (α : Fin k.1 → Fin 2),
        2 * ⟪uReg hc hν hV u₀ ε (List.ofFn α) t,
          ν • (uReg hc hν hV u₀ ε (0 :: 0 :: List.ofFn α) t +
            uReg hc hν hV u₀ ε (1 :: 1 :: List.ofFn α) t)⟫_ℝ =
        (-2 * ν) * (‖uReg hc hν hV u₀ ε (List.ofFn (Fin.cons 0 α)) t‖ ^ 2 +
          ‖uReg hc hν hV u₀ ε (List.ofFn (Fin.cons 1 α)) t‖ ^ 2) := by
      intro k α
      rw [real_inner_smul_right, inner_add_right, hvisc_term k α 0, hvisc_term k α 1]
      ring
    simp_rw [hpt, ← Finset.mul_sum]
    have hcomb := sum_cons_fin2
      (fun _ β => ‖uReg hc hν hV u₀ ε (List.ofFn β) t‖ ^ 2) m
    rw [hcomb]
    unfold HkEnergy
    ring
  have hnorm0_le : ‖uReg hc hν hV u₀ ε (List.ofFn (Fin.elim0 : Fin 0 → Fin 2)) t‖ ^ 2 ≤
      HkEnergy hc hν hV u₀ ε m t := by
    unfold HkEnergy
    have h0_mem : (⟨0, Nat.zero_lt_succ m⟩ : Fin (m + 1)) ∈ Finset.univ := Finset.mem_univ _
    have hs := Finset.single_le_sum
      (f := fun k : Fin (m + 1) =>
        ∑ α : Fin k.1 → Fin 2, ‖uReg hc hν hV u₀ ε (List.ofFn α) t‖ ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) h0_mem
    rwa [sum_fin_zero_eq (fun _ β => ‖uReg hc hν hV u₀ ε (List.ofFn β) t‖ ^ 2) rfl] at hs
  -- 2. Drift forcing term via smooth representative `W_ε` of `H_ε (uReg ε · t)`
  obtain ⟨W_ε, hW_ε, _, hW_lp⟩ := exists_smooth_rep_of_iterWeak hc
    (centeredHeatVecL2CLM hc ε (val0CLM c (E_oseenReg hc hν hV ε t 0 u₀)))
    (fun _ β => centeredHeatVecL2CLM hc ε (uReg hc hν hV u₀ ε (List.ofFn β) t))
    (fun _ β => (hasIterWeakDeriv_uReg hc hν hV u₀ hε (List.ofFn β) ht_ioc).centeredHeat hc ε)
  let p : H1Sol c := freeH1CLM hc ε (E_oseenReg hc hν hV ε t 0 u₀)
  have hW_val0 : toLpCell (hW_ε.memL2 0 Fin.elim0) = val0CLM c p := by
    rw [hW_lp hW_ε 0 Fin.elim0]
    have hl0 : List.ofFn (Fin.elim0 : Fin 0 → Fin 2) = [] := List.ofFn_zero
    rw [hl0, uReg_nil_eq hc hν hV u₀ hε ht_icc]
    exact (val0_freeH1CLM hc ε _).symm
  have hW_dq : toLpCell ((hW_ε.slicePdR 0).memL2 0 Fin.elim0) = dqCLM c p := by
    have hw1 := hasWeakDeriv1_of_isCylSmoothHInf hc hW_ε 0
    rw [hW_val0] at hw1
    exact hw1.unique hc (H1Sol.weak_q p)
  have hW_deta : toLpCell ((hW_ε.slicePdR 1).memL2 0 Fin.elim0) = detaCLM c p := by
    have hw1 := hasWeakDeriv1_of_isCylSmoothHInf hc hW_ε 1
    rw [hW_val0] at hw1
    exact hw1.unique hc (H1Sol.weak_eta p)
  obtain ⟨hB_ε, hB_bound⟩ := hC_pair ht_icc hW_ε
  have hB_fReg : toLpCell (hB_ε.memL2 0 Fin.elim0) = fReg hc hν hV u₀ ε t := by
    have hae_f := bvCLM_ae_realBvSlice hc hV ht_icc p
    have hae_0 : (val0CLM c p : Plane → F8Ex.RMerid) =ᵐ[F8Ex.cellMeas c] W_ε := by
      rw [← hW_val0]; exact coeFn_toLpCell_cellMeas (hW_ε.memL2 0 Fin.elim0)
    have hae_q : (dqCLM c p : Plane → F8Ex.RMerid) =ᵐ[F8Ex.cellMeas c] F8Ex.slicePdR 0 W_ε := by
      rw [← hW_dq]; exact coeFn_toLpCell_cellMeas ((hW_ε.slicePdR 0).memL2 0 Fin.elim0)
    have hae_e : (detaCLM c p : Plane → F8Ex.RMerid) =ᵐ[F8Ex.cellMeas c] F8Ex.slicePdR 1 W_ε := by
      rw [← hW_deta]; exact coeFn_toLpCell_cellMeas ((hW_ε.slicePdR 1).memL2 0 Fin.elim0)
    have hae_B : (fReg hc hν hV u₀ ε t : Plane → F8Ex.RMerid) =ᵐ[F8Ex.cellMeas c]
        F8Ex.realBvSlice (V t) W_ε (F8Ex.slicePdR 0 W_ε) (F8Ex.slicePdR 1 W_ε) := by
      filter_upwards [hae_f, hae_0, hae_q, hae_e] with y hyf hy0 hyq hye
      change (bvCLM hc hV t p : Plane → F8Ex.RMerid) y = _
      rw [hyf]
      unfold F8Ex.realBvSlice
      rw [hy0, hyq, hye]
    apply Lp.ext
    exact (coeFn_toLpCell (hB_ε.memL2 0 Fin.elim0)).trans (aeEq_cellμ_of_cellMeas hae_B.symm)
  have hdrift_id : ∀ (k : Fin (m + 1)) (α : Fin k.1 → Fin 2),
      ⟪uReg hc hν hV u₀ ε (List.ofFn α) t,
        P0 c (iterDHeatCLM hc (List.ofFn α) ε (fReg hc hν hV u₀ ε t))⟫_ℝ =
          ⟪toLpCell (hW_ε.memL2 k.1 α), toLpCell (hB_ε.memL2 k.1 α)⟫_ℝ := by
    intro k α
    have hdiv_u := uReg_mem_divFree hc hν hV u₀ hε (List.ofFn α) ht_icc
    have hw_B := hasIterWeakDeriv_of_isCylSmoothHInf hc hB_ε α
    rw [hB_fReg] at hw_B
    rw [← Cyl.inner_P0_comm, Cyl.P0_eq_self hdiv_u,
      iterDHeatCLM_eq_centeredHeat_of_hasIterWeakDeriv hc hε hw_B,
      ← inner_centeredHeatVecL2CLM_symm hc hε.le,
      hW_lp hW_ε k.1 α]
  have hEW_le :
      (∑ k : Fin (m + 1), ∑ α : Fin k.1 → Fin 2, ‖toLpCell (hW_ε.memL2 k.1 α)‖ ^ 2) ≤
        HkEnergy hc hν hV u₀ ε m t := by
    unfold HkEnergy
    refine Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun α _ => ?_
    rw [hW_lp hW_ε k.1 α]
    have hn : ‖centeredHeatVecL2CLM hc ε (uReg hc hν hV u₀ ε (List.ofFn α) t)‖ ≤
        ‖uReg hc hν hV u₀ ε (List.ofFn α) t‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_of_le_one_left (norm_nonneg _)
          (F8WeakEx.norm_centeredHeatVecL2CLM_le_one_all hc ε))
    exact pow_le_pow_left₀ (norm_nonneg _) hn 2
  have hsplit_sum :
      (∑ k : Fin (m + 1), ∑ α : Fin k.1 → Fin 2,
        2 * ⟪uReg hc hν hV u₀ ε (List.ofFn α) t, rhs (List.ofFn α)⟫_ℝ) =
      (∑ k : Fin (m + 1), ∑ α : Fin k.1 → Fin 2,
        2 * ⟪uReg hc hν hV u₀ ε (List.ofFn α) t,
          ν • (uReg hc hν hV u₀ ε (0 :: 0 :: List.ofFn α) t +
            uReg hc hν hV u₀ ε (1 :: 1 :: List.ofFn α) t)⟫_ℝ) -
      2 * ∑ k : Fin (m + 1), ∑ α : Fin k.1 → Fin 2,
        ⟪toLpCell (hW_ε.memL2 k.1 α), toLpCell (hB_ε.memL2 k.1 α)⟫_ℝ := by
    have hpt : ∀ (k : Fin (m + 1)) (α : Fin k.1 → Fin 2),
        2 * ⟪uReg hc hν hV u₀ ε (List.ofFn α) t, rhs (List.ofFn α)⟫_ℝ =
        2 * ⟪uReg hc hν hV u₀ ε (List.ofFn α) t,
          ν • (uReg hc hν hV u₀ ε (0 :: 0 :: List.ofFn α) t +
            uReg hc hν hV u₀ ε (1 :: 1 :: List.ofFn α) t)⟫_ℝ -
        2 * ⟪toLpCell (hW_ε.memL2 k.1 α), toLpCell (hB_ε.memL2 k.1 α)⟫_ℝ := by
      intro k α
      dsimp only [rhs]
      rw [inner_sub_right, hdrift_id k α]
      ring
    simp_rw [hpt, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hdr_abs :
      -(2 * ∑ k : Fin (m + 1), ∑ α : Fin k.1 → Fin 2,
          ⟪toLpCell (hW_ε.memL2 k.1 α), toLpCell (hB_ε.memL2 k.1 α)⟫_ℝ) ≤
        2 * C_m * HkEnergy hc hν hV u₀ ε m t := by
    have h1 : -(∑ k : Fin (m + 1), ∑ α : Fin k.1 → Fin 2,
        ⟪toLpCell (hW_ε.memL2 k.1 α), toLpCell (hB_ε.memL2 k.1 α)⟫_ℝ) ≤
        ∑ k : Fin (m + 1), ∑ α : Fin k.1 → Fin 2,
          |⟪toLpCell (hW_ε.memL2 k.1 α), toLpCell (hB_ε.memL2 k.1 α)⟫_ℝ| := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_le_sum fun k _ => ?_
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_le_sum fun α _ => neg_le_abs _
    have h2 := h1.trans (hB_bound.trans (mul_le_mul_of_nonneg_left hEW_le hC_nn))
    linarith
  rw [hsplit_sum, hvisc_sum]
  have hν0 : 2 * ν * ‖uReg hc hν hV u₀ ε (List.ofFn (Fin.elim0 : Fin 0 → Fin 2)) t‖ ^ 2 ≤
      2 * ν * HkEnergy hc hν hV u₀ ε m t :=
    mul_le_mul_of_nonneg_left hnorm0_le (by positivity)
  linarith

/-- **All-order `ε`-uniform interior `H^m` bound on `[a, 2)`**:
for every `m : ℕ` and `a ∈ (0, 2)`, there exists `B_m ≥ 0` independent of `ε` and `t` such that
`HkEnergy ε m t ≤ B_m` for all `ε > 0` and `t ∈ [a, 2)`. -/
theorem exists_HkEnergy_uniform_bound {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν)
    {V : ℝ → Plane → F8Ex.RMerid} (hV : F8Ex.IsSmoothBUCDrift c V)
    (u₀ : H1Sol c) :
    ∀ (m : ℕ) {a : ℝ}, a ∈ Ioo (0 : ℝ) 2 →
      ∃ B_m : ℝ, 0 ≤ B_m ∧
        ∀ {ε : ℝ}, 0 < ε → ∀ {t : ℝ}, t ∈ Ico a 2 →
          HkEnergy hc hν hV u₀ ε m t ≤ B_m
  | 0, _, ha => by
      let S : ℝ := (oseenVolterraData hc hν hV).stripBound * ‖u₀‖
      refine ⟨S ^ 2, sq_nonneg S, ?_⟩
      intro ε hε t ht
      have ht_icc : t ∈ Icc (0 : ℝ) 2 := ⟨(ha.1.trans_le ht.1).le, ht.2.le⟩
      have heq0 : HkEnergy hc hν hV u₀ ε 0 t = ‖uReg hc hν hV u₀ ε [] t‖ ^ 2 := by
        unfold HkEnergy
        change (∑ k : Fin 1, ∑ α : Fin k.1 → Fin 2,
          ‖uReg hc hν hV u₀ ε (List.ofFn α) t‖ ^ 2) = _
        rw [Fin.sum_univ_one,
          sum_fin_zero_eq (fun _ β => ‖uReg hc hν hV u₀ ε (List.ofFn β) t‖ ^ 2) (Fin.val_zero 1)]
        have hl0 : List.ofFn (Fin.elim0 : Fin 0 → Fin 2) = [] := List.ofFn_zero
        rw [hl0]
      rw [heq0, uReg_nil_eq hc hν hV u₀ hε ht_icc]
      have hn : ‖val0CLM c (E_oseenReg hc hν hV ε t 0 u₀)‖ ≤ S :=
        (norm_val0CLM_le _).trans (norm_E_oseenReg_le hc hν hV ε t 0 u₀)
      exact pow_le_pow_left₀ (norm_nonneg _) hn 2
  | m + 1, a, ha => by
      let a' : ℝ := a / 2
      have ha' : a' ∈ Ioo (0 : ℝ) 2 := ⟨half_pos ha.1, (half_lt_self ha.1).trans ha.2⟩
      obtain ⟨B_m, hBm_nn, hBm⟩ := exists_HkEnergy_uniform_bound hc hν hV u₀ m ha'
      obtain ⟨K_m, hKm_nn, hd0⟩ := exists_hasDerivAt_HkEnergy_bound hc hν hV u₀ m
      obtain ⟨K_1, hK1_nn, hd1⟩ := exists_hasDerivAt_HkEnergy_bound hc hν hV u₀ (m + 1)
      let B_next : ℝ := (Real.exp (2 * K_1) * (B_m + 2 * K_m * B_m)) / (ν * a)
      have hva_pos : 0 < ν * a := mul_pos hν ha.1
      have hBn_nn : 0 ≤ B_next := by
        dsimp only [B_next]
        positivity
      refine ⟨B_next, hBn_nn, ?_⟩
      intro ε hε t ht
      have ha'_lt_t : a' < t := lt_of_lt_of_le (half_lt_self ha.1) ht.1
      -- Time-weighted parabolic Lyapunov functional on `[a', t] ⊆ (0, 2)`
      let E0 : ℝ → ℝ := HkEnergy hc hν hV u₀ ε m
      let E1 : ℝ → ℝ := HkEnergy hc hν hV u₀ ε (m + 1)
      let Φ : ℝ → ℝ := fun s => E0 s + (2 * ν * (s - a')) * E1 s
      let Ψ : ℝ → ℝ := fun s => Real.exp (-K_1 * (s - a')) * Φ s - (K_m * B_m) * (s - a')
      have hd_Ψ : ∀ s ∈ Ioo (0 : ℝ) 2, ∃ DΨ : ℝ, HasDerivAt Ψ DΨ s ∧
          (a' ≤ s → DΨ ≤ 0) := by
        intro s hs
        obtain ⟨D0, hD0, hle0⟩ := hd0 hε hs
        obtain ⟨D1, hD1, hle1⟩ := hd1 hε hs
        have hd_sub : HasDerivAt (fun r : ℝ => r - a') 1 s :=
          (hasDerivAt_id s).sub_const a'
        have hd_lin : HasDerivAt (fun r : ℝ => 2 * ν * (r - a')) (2 * ν) s := by
          simpa only [mul_one] using hd_sub.const_mul (2 * ν)
        have hd_Φ : HasDerivAt Φ (D0 + ((2 * ν) * E1 s + (2 * ν * (s - a')) * D1)) s :=
          hD0.add (hd_lin.mul hD1)
        have hd_exp : HasDerivAt (fun r : ℝ => Real.exp (-K_1 * (r - a')))
            (Real.exp (-K_1 * (s - a')) * (-K_1)) s := by
          have h1 : HasDerivAt (fun r : ℝ => -K_1 * (r - a')) (-K_1) s := by
            simpa only [mul_one] using hd_sub.const_mul (-K_1)
          exact h1.exp
        have hd_rem : HasDerivAt (fun r : ℝ => (K_m * B_m) * (r - a')) (K_m * B_m) s := by
          simpa only [mul_one] using hd_sub.const_mul (K_m * B_m)
        have hd_all := (hd_exp.mul hd_Φ).sub hd_rem
        refine ⟨_, hd_all, fun hsa' => ?_⟩
        have hs_ico : s ∈ Ico a' 2 := ⟨hsa', hs.2⟩
        have hE0_le : E0 s ≤ B_m := hBm hε hs_ico
        have hE0_nn : 0 ≤ E0 s := HkEnergy_nonneg hc hν hV u₀ ε m s
        have hE1_nn : 0 ≤ E1 s := HkEnergy_nonneg hc hν hV u₀ ε (m + 1) s
        have hE2_nn : 0 ≤ HkEnergy hc hν hV u₀ ε (m + 2) s :=
          HkEnergy_nonneg hc hν hV u₀ ε (m + 2) s
        have hsa'_nn : 0 ≤ s - a' := sub_nonneg.mpr hsa'
        have hw_nn : 0 ≤ 2 * ν * (s - a') := mul_nonneg (by positivity) hsa'_nn
        have hw_D1 : (2 * ν * (s - a')) * D1 ≤ K_1 * ((2 * ν * (s - a')) * E1 s) := by
          have hm1 := mul_le_mul_of_nonneg_left hle1 hw_nn
          have hvisc2_nonpos : (2 * ν * (s - a')) * (-2 * ν * HkEnergy hc hν hV u₀ ε (m + 2) s) ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos hw_nn
              (mul_nonpos_of_nonpos_of_nonneg (by linarith) hE2_nn)
          linarith [hm1, hvisc2_nonpos]
        have hΦ'_le : D0 + ((2 * ν) * E1 s + (2 * ν * (s - a')) * D1) ≤
            K_m * B_m + K_1 * Φ s := by
          have hKm_step : K_m * E0 s ≤ K_m * B_m :=
            mul_le_mul_of_nonneg_left hE0_le hKm_nn
          have hK1_E0 : 0 ≤ K_1 * E0 s := mul_nonneg hK1_nn hE0_nn
          dsimp only [Φ]
          linarith [hle0, hw_D1, hKm_step, hK1_E0]
        have hexp_pos : 0 < Real.exp (-K_1 * (s - a')) := Real.exp_pos _
        have hexp_le1 : Real.exp (-K_1 * (s - a')) ≤ 1 :=
          Real.exp_le_one_iff.mpr (by nlinarith [hK1_nn, hsa'_nn])
        have hmul1 : Real.exp (-K_1 * (s - a')) *
            (D0 + ((2 * ν) * E1 s + (2 * ν * (s - a')) * D1) - K_1 * Φ s) ≤
              Real.exp (-K_1 * (s - a')) * (K_m * B_m) :=
          mul_le_mul_of_nonneg_left (by linarith [hΦ'_le]) hexp_pos.le
        have hmul2 : Real.exp (-K_1 * (s - a')) * (K_m * B_m) ≤ K_m * B_m :=
          mul_le_of_le_one_left (mul_nonneg hKm_nn hBm_nn) hexp_le1
        linarith [hmul1, hmul2]
      have hΨ_cont : ContinuousOn Ψ (Icc a' t) := by
        intro s hs
        have hs_ioo : s ∈ Ioo (0 : ℝ) 2 :=
          ⟨lt_of_lt_of_le ha'.1 hs.1, lt_of_le_of_lt hs.2 ht.2⟩
        obtain ⟨_, hDs, _⟩ := hd_Ψ s hs_ioo
        exact hDs.continuousAt.continuousWithinAt
      have hΨ_le : Ψ t ≤ Ψ a' :=
        egc_anti_Icc ha'_lt_t.le hΨ_cont fun s hs => by
          have hs_ioo : s ∈ Ioo (0 : ℝ) 2 :=
            ⟨lt_trans ha'.1 hs.1, lt_trans hs.2 ht.2⟩
          obtain ⟨DΨ, hDΨ, hle⟩ := hd_Ψ s hs_ioo
          exact ⟨DΨ, hDΨ, hle hs.1.le⟩
      have hΨ_a' : Ψ a' ≤ B_m := by
        dsimp only [Ψ, Φ]
        simp only [sub_self, mul_zero, zero_mul, Real.exp_zero, one_mul, add_zero, sub_zero]
        exact hBm hε ⟨le_rfl, ha'.2⟩
      have ht_sub_le2 : t - a' ≤ 2 := by linarith [ht.2, ha'.1]
      have ht_sub_ge : a / 2 ≤ t - a' := by dsimp only [a']; linarith [ht.1]
      have hΦt_le : Real.exp (-K_1 * (t - a')) * Φ t ≤ B_m + 2 * K_m * B_m := by
        have hrem_le : (K_m * B_m) * (t - a') ≤ 2 * K_m * B_m := by
          nlinarith [mul_nonneg hKm_nn hBm_nn, ht_sub_le2]
        dsimp only [Ψ] at hΨ_le
        linarith [hΨ_le, hΨ_a', hrem_le]
      have hΦt_bound : Φ t ≤ Real.exp (2 * K_1) * (B_m + 2 * K_m * B_m) := by
        have hm := mul_le_mul_of_nonneg_left hΦt_le (Real.exp_pos (K_1 * (t - a'))).le
        have hexp_cancel : Real.exp (K_1 * (t - a')) * (Real.exp (-K_1 * (t - a')) * Φ t) = Φ t := by
          rw [← mul_assoc, ← Real.exp_add]
          ring_nf
          rw [Real.exp_zero, one_mul]
        rw [hexp_cancel] at hm
        have hexp_mono : Real.exp (K_1 * (t - a')) ≤ Real.exp (2 * K_1) :=
          Real.exp_le_exp.mpr (by nlinarith [hK1_nn, ht_sub_le2])
        exact hm.trans (mul_le_mul_of_nonneg_right hexp_mono (by positivity))
      have hE1_nn : 0 ≤ E1 t := HkEnergy_nonneg hc hν hV u₀ ε (m + 1) t
      have hE0_nn : 0 ≤ E0 t := HkEnergy_nonneg hc hν hV u₀ ε m t
      have hva_E1 : (ν * a) * E1 t ≤ Φ t := by
        have hcoef : ν * a ≤ 2 * ν * (t - a') := by nlinarith [hν, ht_sub_ge]
        have hm1 : (ν * a) * E1 t ≤ (2 * ν * (t - a')) * E1 t :=
          mul_le_mul_of_nonneg_right hcoef hE1_nn
        dsimp only [Φ]
        linarith [hm1, hE0_nn]
      exact (le_div_iff₀ hva_pos).mpr (by rw [mul_comm]; exact hva_E1.trans hΦt_bound)

/-! ## 3. Riesz Limit `D_U α t : L2v c` as `ε → 0⁺` and `C((0, 2); H^k)` Continuity -/

private theorem exists_riesz_extension {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (S : Submodule ℝ H) (ℓ : S →ₗ[ℝ] ℝ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ s : S, |ℓ s| ≤ C * ‖(s : H)‖) :
    ∃ g : H, ‖g‖ ≤ C ∧ ∀ s : S, ℓ s = ⟪g, (s : H)⟫_ℝ := by
  let L : S →L[ℝ] ℝ := LinearMap.mkContinuous ℓ C (fun s => by
    rw [Real.norm_eq_abs]
    exact hC s)
  obtain ⟨G, hGext, hGnorm⟩ := exists_extension_norm_eq S L
  refine ⟨(InnerProductSpace.toDual ℝ H).symm G, ?_, ?_⟩
  · rw [LinearIsometryEquiv.norm_map]
    calc ‖G‖ = ‖L‖ := hGnorm
      _ ≤ C := LinearMap.mkContinuous_norm_le ℓ hC0 _
  · intro s
    rw [InnerProductSpace.toDual_symm_apply, hGext s]
    rfl

private theorem exists_riesz_of_linear {W H : Type*} [AddCommGroup W] [Module ℝ W]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (ι : W →ₗ[ℝ] H) (ℓ : W →ₗ[ℝ] ℝ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ w, |ℓ w| ≤ C * ‖ι w‖) :
    ∃ g : H, ‖g‖ ≤ C ∧ ∀ w, ℓ w = ⟪g, ι w⟫_ℝ := by
  have hker : LinearMap.ker ι ≤ LinearMap.ker ℓ := fun w hw => by
    have h0 : ι w = 0 := hw
    have := hC w
    rw [h0, norm_zero, mul_zero] at this
    exact abs_nonpos_iff.1 this
  let ℓ' : LinearMap.range ι →ₗ[ℝ] ℝ :=
    ((LinearMap.ker ι).liftQ ℓ hker).comp ι.quotKerEquivRange.symm.toLinearMap
  have hℓ' : ∀ w, ℓ' ⟨ι w, ⟨w, rfl⟩⟩ = ℓ w := fun w => by
    have : ι.quotKerEquivRange.symm ⟨ι w, ⟨w, rfl⟩⟩ = Submodule.Quotient.mk w := by
      rw [LinearEquiv.symm_apply_eq]
      exact Subtype.ext (LinearMap.quotKerEquivRange_apply_mk ι w).symm
    show ((LinearMap.ker ι).liftQ ℓ hker) (ι.quotKerEquivRange.symm ⟨ι w, ⟨w, rfl⟩⟩) = _
    rw [this]
    rfl
  obtain ⟨g, hg, hgs⟩ := exists_riesz_extension (LinearMap.range ι) ℓ' hC0 (fun s => by
    obtain ⟨_, w, hw⟩ := s
    have : (⟨_, ⟨w, hw⟩⟩ : LinearMap.range ι) = ⟨ι w, ⟨w, rfl⟩⟩ := by
      subst hw; rfl
    rw [this, hℓ']
    exact hC w)
  refine ⟨g, hg, fun w => ?_⟩
  rw [← hℓ' w, hgs]

/-- Subspace of smooth `c`-periodic compactly-supported scalar cylinder test functions. -/
def CylTestSub (c : ℝ) : Submodule ℝ (Plane → ℝ) where
  carrier := {ψ | B0579.IsCylTest c ψ}
  zero_mem' := ⟨contDiff_const, fun _ => rfl, ⟨0, fun _ _ => rfl⟩⟩
  add_mem' {ψ₁ ψ₂} h₁ h₂ := ⟨h₁.smooth.add h₂.smooth,
    fun x => by simp [h₁.periodic x, h₂.periodic x],
    by
      obtain ⟨R₁, hR₁⟩ := h₁.band
      obtain ⟨R₂, hR₂⟩ := h₂.band
      exact ⟨max R₁ R₂, fun x hx => by
        simp [hR₁ x (lt_of_le_of_lt (le_max_left _ _) hx),
          hR₂ x (lt_of_le_of_lt (le_max_right _ _) hx)]⟩⟩
  smul_mem' r {ψ} h := ⟨contDiff_const.smul h.smooth,
    fun x => by simp [h.periodic x],
    by
      obtain ⟨R, hR⟩ := h.band
      exact ⟨R, fun x hx => by simp [hR x hx]⟩⟩

private lemma cylTestSub_mem {c : ℝ} (ψ : CylTestSub c) : B0579.IsCylTest c ψ.1 := ψ.2

private lemma coeFn_cylSmoothToL2 {c : ℝ} {Φ : Plane → F8Ex.RMerid}
    (hΦ : Sob.IsCylSmooth c Φ) :
    (cylSmoothToL2 hΦ : Plane → Vec2) =ᵐ[cellμ c] Φ :=
  (memLp_of_cylSmooth hΦ).coeFn_toLp

private def singleToL2 (c : ℝ) (k : Fin 2) : CylTestSub c →ₗ[ℝ] L2v c where
  toFun ψ := cylSmoothToL2 (isCylSmooth_single (cylTestSub_mem ψ) k)
  map_add' ψ₁ ψ₂ := by
    apply Lp.ext
    have h12 := coeFn_cylSmoothToL2 (isCylSmooth_single (cylTestSub_mem (ψ₁ + ψ₂)) k)
    have h1 := coeFn_cylSmoothToL2 (isCylSmooth_single (cylTestSub_mem ψ₁) k)
    have h2 := coeFn_cylSmoothToL2 (isCylSmooth_single (cylTestSub_mem ψ₂) k)
    filter_upwards [h12, Lp.coeFn_add (cylSmoothToL2 (isCylSmooth_single (cylTestSub_mem ψ₁) k))
      (cylSmoothToL2 (isCylSmooth_single (cylTestSub_mem ψ₂) k)), h1, h2] with y hy12 hadd hy1 hy2
    rw [hy12, hadd, Pi.add_apply, hy1, hy2]
    change (ψ₁.1 y + ψ₂.1 y) • _ = _
    exact add_smul (ψ₁.1 y) (ψ₂.1 y) _
  map_smul' r ψ := by
    apply Lp.ext
    have hr := coeFn_cylSmoothToL2 (isCylSmooth_single (cylTestSub_mem (r • ψ)) k)
    have h1 := coeFn_cylSmoothToL2 (isCylSmooth_single (cylTestSub_mem ψ) k)
    filter_upwards [hr, Lp.coeFn_smul r (cylSmoothToL2 (isCylSmooth_single (cylTestSub_mem ψ) k)),
      h1] with y hyr hsm hy1
    rw [RingHom.id_apply, hyr, hsm, Pi.smul_apply, hy1]
    change (r * ψ.1 y) • _ = _
    exact mul_smul r (ψ.1 y) _

private def pdTestLinear (c : ℝ) (j : Fin 2) : CylTestSub c →ₗ[ℝ] CylTestSub c where
  toFun ψ := ⟨B0579.pd j ψ.1, (cylTestSub_mem ψ).pd j⟩
  map_add' ψ₁ ψ₂ := by
    apply Subtype.ext
    funext y
    change fderiv ℝ (ψ₁.1 + ψ₂.1) y (B0579.dir j) =
      fderiv ℝ ψ₁.1 y (B0579.dir j) + fderiv ℝ ψ₂.1 y (B0579.dir j)
    rw [fderiv_add ((cylTestSub_mem ψ₁).smooth.differentiable (by simp) y)
      ((cylTestSub_mem ψ₂).smooth.differentiable (by simp) y)]
    rfl
  map_smul' r ψ := by
    apply Subtype.ext
    funext y
    change fderiv ℝ (r • ψ.1) y (B0579.dir j) = r • (fderiv ℝ ψ.1 y (B0579.dir j))
    rw [fderiv_const_smul ((cylTestSub_mem ψ).smooth.differentiable (by simp) y) r]
    rfl

private def pdIterRevLinear (c : ℝ) : List (Fin 2) → (CylTestSub c →ₗ[ℝ] CylTestSub c)
  | [] => LinearMap.id
  | j :: α => (pdIterRevLinear c α).comp (pdTestLinear c j)

private lemma pdIterRevLinear_val {c : ℝ} :
    ∀ (α : List (Fin 2)) (ψ : CylTestSub c),
      (pdIterRevLinear c α ψ).1 = pdIterRev α ψ.1
  | [], _ => rfl
  | j :: α, ψ => pdIterRevLinear_val α ⟨B0579.pd j ψ.1, (cylTestSub_mem ψ).pd j⟩

private lemma singleToL2_pdIterRevLinear {c : ℝ} (α : List (Fin 2)) (ψ : CylTestSub c)
    (k : Fin 2) :
    singleToL2 c k (pdIterRevLinear c α ψ) =
      cylSmoothToL2 (isCylSmooth_single (isCylTest_pdIterRev α (cylTestSub_mem ψ)) k) := by
  apply Lp.ext
  have h1 := coeFn_cylSmoothToL2
    (isCylSmooth_single (cylTestSub_mem (pdIterRevLinear c α ψ)) k)
  have h2 := coeFn_cylSmoothToL2
    (isCylSmooth_single (isCylTest_pdIterRev α (cylTestSub_mem ψ)) k)
  filter_upwards [h1, h2] with y hy1 hy2
  change (cylSmoothToL2 (isCylSmooth_single (cylTestSub_mem (pdIterRevLinear c α ψ)) k) :
    Plane → Vec2) y = _
  rw [hy1, hy2, pdIterRevLinear_val]

private def ιPair (c : ℝ) : (CylTestSub c × CylTestSub c) →ₗ[ℝ] L2v c :=
  (singleToL2 c 0).comp (LinearMap.fst ℝ (CylTestSub c) (CylTestSub c)) +
    (singleToL2 c 1).comp (LinearMap.snd ℝ (CylTestSub c) (CylTestSub c))

private def pairFunctional {c : ℝ} (u : L2v c) (α : List (Fin 2)) :
    (CylTestSub c × CylTestSub c) →ₗ[ℝ] ℝ :=
  ((-1 : ℝ) ^ α.length) •
    ((innerSL ℝ u).toLinearMap.comp
      (((singleToL2 c 0).comp (pdIterRevLinear c α)).comp
          (LinearMap.fst ℝ (CylTestSub c) (CylTestSub c)) +
        ((singleToL2 c 1).comp (pdIterRevLinear c α)).comp
          (LinearMap.snd ℝ (CylTestSub c) (CylTestSub c))))

private lemma pairFunctional_apply {c : ℝ} (u : L2v c) (α : List (Fin 2))
    (p : CylTestSub c × CylTestSub c) :
    pairFunctional u α p =
      (-1 : ℝ) ^ α.length *
        (⟪u, cylSmoothToL2 (isCylSmooth_single (isCylTest_pdIterRev α (cylTestSub_mem p.1)) 0)⟫_ℝ +
          ⟪u, cylSmoothToL2 (isCylSmooth_single (isCylTest_pdIterRev α (cylTestSub_mem p.2)) 1)⟫_ℝ) := by
  dsimp [pairFunctional]
  rw [singleToL2_pdIterRevLinear, singleToL2_pdIterRevLinear, inner_add_right]

private lemma cylSmoothToL2_pdIterRev_zero {c : ℝ} (α : List (Fin 2)) (k : Fin 2) :
    cylSmoothToL2 (isCylSmooth_single (isCylTest_pdIterRev α (cylTestSub_mem (0 : CylTestSub c))) k) =
      0 := by
  have h0_rev : pdIterRev α (0 : Plane → ℝ) = 0 := by
    induction α with
    | nil => rfl
    | cons j β ih =>
        have hpd0 : B0579.pd j (0 : Plane → ℝ) = 0 := by
          funext y; simp [B0579.pd]
        dsimp only [pdIterRev]
        rw [hpd0, ih]
  apply Lp.ext
  have h1 := coeFn_cylSmoothToL2
    (isCylSmooth_single (isCylTest_pdIterRev α (cylTestSub_mem (0 : CylTestSub c))) k)
  filter_upwards [h1, Lp.coeFn_zero Vec2 2 (cellμ c)] with y hy1 hy0
  rw [hy1, hy0]
  change pdIterRev α (0 : Plane → ℝ) y • EuclideanSpace.single k 1 = 0
  rw [h0_rev, Pi.zero_apply, zero_smul]

/-- Existence and norm bound of the `α`-th weak `L2v c` derivative of `E_oseen t 0 u₀` via
passing `ε → 0⁺` in the uniform `HkEnergy` bound and applying Hahn-Banach / Riesz. -/
private lemma exists_weak_deriv_E_oseen {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν)
    {V : ℝ → Plane → F8Ex.RMerid} (hV : F8Ex.IsSmoothBUCDrift c V)
    (u₀ : H1Sol c) (α : List (Fin 2)) {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 2)
    {B : ℝ} (_hB_nn : 0 ≤ B)
    (hB : ∀ {ε : ℝ}, 0 < ε → ∀ {t : ℝ}, t ∈ Ico a 2 →
      HkEnergy hc hν hV u₀ ε α.length t ≤ B)
    {t : ℝ} (ht : t ∈ Ico a 2) :
    ∃ g : L2v c, ‖g‖ ≤ Real.sqrt B ∧
      ∀ (ψ : Plane → ℝ) (hψ : B0579.IsCylTest c ψ) (k : Fin 2),
        ⟪g, cylSmoothToL2 (isCylSmooth_single hψ k)⟫_ℝ =
          (-1 : ℝ) ^ α.length *
            ⟪val0CLM c (E_oseen hc hν hV t 0 u₀),
              cylSmoothToL2 (isCylSmooth_single (isCylTest_pdIterRev α hψ) k)⟫_ℝ := by
  let u_t : L2v c := val0CLM c (E_oseen hc hν hV t 0 u₀)
  have ht_icc : t ∈ Icc (0 : ℝ) 2 := ⟨by linarith [ha.1, ht.1], ht.2.le⟩
  have ht_ioc : t ∈ Ioc (0 : ℝ) 2 := ⟨lt_of_lt_of_le ha.1 ht.1, ht.2.le⟩
  have hbound : ∀ p : CylTestSub c × CylTestSub c,
      |pairFunctional u_t α p| ≤ Real.sqrt B * ‖ιPair c p‖ := by
    intro p
    let z0 := cylSmoothToL2 (isCylSmooth_single (isCylTest_pdIterRev α (cylTestSub_mem p.1)) 0)
    let z1 := cylSmoothToL2 (isCylSmooth_single (isCylTest_pdIterRev α (cylTestSub_mem p.2)) 1)
    have htend_E : Tendsto (fun ε : ℝ => val0CLM c (E_oseenReg hc hν hV ε t 0 u₀))
        (𝓝[>] (0 : ℝ)) (𝓝 u_t) :=
      ((val0CLM c).continuous.tendsto _).comp
        ((tendsto_E_oseenReg hc hν hV ht_icc u₀).mono_left nhdsWithin_le_nhds)
    have htend_pair : Tendsto
        (fun ε : ℝ => |(-1 : ℝ) ^ α.length *
          (⟪val0CLM c (E_oseenReg hc hν hV ε t 0 u₀), z0⟫_ℝ +
            ⟪val0CLM c (E_oseenReg hc hν hV ε t 0 u₀), z1⟫_ℝ)|)
        (𝓝[>] (0 : ℝ)) (𝓝 |pairFunctional u_t α p|) := by
      rw [pairFunctional_apply]
      have h0 : Tendsto (fun ε : ℝ => ⟪val0CLM c (E_oseenReg hc hν hV ε t 0 u₀), z0⟫_ℝ)
          (𝓝[>] (0 : ℝ)) (𝓝 ⟪u_t, z0⟫_ℝ) :=
        htend_E.inner tendsto_const_nhds
      have h1 : Tendsto (fun ε : ℝ => ⟪val0CLM c (E_oseenReg hc hν hV ε t 0 u₀), z1⟫_ℝ)
          (𝓝[>] (0 : ℝ)) (𝓝 ⟪u_t, z1⟫_ℝ) :=
        htend_E.inner tendsto_const_nhds
      exact ((h0.add h1).const_mul ((-1 : ℝ) ^ α.length)).abs
    have hev_le : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
        |(-1 : ℝ) ^ α.length *
          (⟪val0CLM c (E_oseenReg hc hν hV ε t 0 u₀), z0⟫_ℝ +
            ⟪val0CLM c (E_oseenReg hc hν hV ε t 0 u₀), z1⟫_ℝ)| ≤
          Real.sqrt B * ‖ιPair c p‖ := by
      filter_upwards [self_mem_nhdsWithin] with ε hε_mem
      have hε : 0 < ε := hε_mem
      have hw := hasIterWeakDeriv_uReg hc hν hV u₀ hε α ht_ioc
      have hp0 := hw.inner_single p.1.1 (cylTestSub_mem p.1) 0
      have hp1 := hw.inner_single p.2.1 (cylTestSub_mem p.2) 1
      have hsum_eq : (-1 : ℝ) ^ α.length *
          (⟪val0CLM c (E_oseenReg hc hν hV ε t 0 u₀), z0⟫_ℝ +
            ⟪val0CLM c (E_oseenReg hc hν hV ε t 0 u₀), z1⟫_ℝ) =
          ⟪uReg hc hν hV u₀ ε α t, ιPair c p⟫_ℝ := by
        dsimp only [ιPair, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.fst_apply,
          LinearMap.snd_apply, singleToL2, LinearMap.coe_mk, AddHom.coe_mk]
        rw [inner_add_right, hp0, hp1]
        dsimp only [z0, z1]
        ring
      rw [hsum_eq]
      have hn_le : ‖uReg hc hν hV u₀ ε α t‖ ≤ Real.sqrt B :=
        Real.le_sqrt_of_sq_le ((norm_uReg_sq_le_HkEnergy hc hν hV u₀ ε α t).trans (hB hε ht))
      exact (abs_real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right hn_le (norm_nonneg _))
    have : NeBot (𝓝[>] (0 : ℝ)) := nhdsWithin_Ioi_neBot le_rfl
    exact le_of_tendsto htend_pair hev_le
  obtain ⟨g, hg_norm, hg_pair⟩ :=
    exists_riesz_of_linear (ιPair c) (pairFunctional u_t α) (Real.sqrt_nonneg B) hbound
  refine ⟨g, hg_norm, fun ψ hψ k => ?_⟩
  let ψs : CylTestSub c := ⟨ψ, hψ⟩
  fin_cases k
  · have hp := hg_pair (ψs, 0)
    rw [pairFunctional_apply] at hp
    have hι0 : ιPair c (ψs, 0) = cylSmoothToL2 (isCylSmooth_single hψ 0) := by
      dsimp only [ιPair, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.fst_apply,
        LinearMap.snd_apply]
      rw [map_zero, add_zero]
      rfl
    rw [cylSmoothToL2_pdIterRev_zero α 1, inner_zero_right, add_zero, hι0] at hp
    exact hp.symm
  · have hp := hg_pair (0, ψs)
    rw [pairFunctional_apply] at hp
    have hι1 : ιPair c (0, ψs) = cylSmoothToL2 (isCylSmooth_single hψ 1) := by
      dsimp only [ιPair, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.fst_apply,
        LinearMap.snd_apply]
      rw [map_zero, zero_add]
      rfl
    rw [cylSmoothToL2_pdIterRev_zero α 0, inner_zero_right, zero_add, hι1] at hp
    exact hp.symm

/-- Canonical `L2v c` spatial derivative tower `D_U α t` of `E_oseen hc hν hV t 0 u₀` on `(0, 2)`. -/
def D_U {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν)
    {V : ℝ → Plane → F8Ex.RMerid} (hV : F8Ex.IsSmoothBUCDrift c V)
    (u₀ : H1Sol c) (α : List (Fin 2)) (t : ℝ) : L2v c :=
  open Classical in
  if ht : t ∈ Ioo (0 : ℝ) 2 then
    let ha : t / 2 ∈ Ioo (0 : ℝ) 2 := ⟨half_pos ht.1, by linarith [ht.1, ht.2]⟩
    let hB := exists_HkEnergy_uniform_bound hc hν hV u₀ α.length ha
    (exists_weak_deriv_E_oseen hc hν hV u₀ α ha hB.choose_spec.1 hB.choose_spec.2
      ⟨(half_lt_self ht.1).le, ht.2⟩).choose
  else
    0

lemma D_U_inner_single {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν)
    {V : ℝ → Plane → F8Ex.RMerid} (hV : F8Ex.IsSmoothBUCDrift c V)
    (u₀ : H1Sol c) (α : List (Fin 2)) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 2)
    (ψ : Plane → ℝ) (hψ : B0579.IsCylTest c ψ) (k : Fin 2) :
    ⟪D_U hc hν hV u₀ α t, cylSmoothToL2 (isCylSmooth_single hψ k)⟫_ℝ =
      (-1 : ℝ) ^ α.length *
        ⟪val0CLM c (E_oseen hc hν hV t 0 u₀),
          cylSmoothToL2 (isCylSmooth_single (isCylTest_pdIterRev α hψ) k)⟫_ℝ := by
  unfold D_U
  rw [dite_eq_left ht]
  let ha : t / 2 ∈ Ioo (0 : ℝ) 2 := ⟨half_pos ht.1, by linarith [ht.1, ht.2]⟩
  let hB := exists_HkEnergy_uniform_bound hc hν hV u₀ α.length ha
  exact (exists_weak_deriv_E_oseen hc hν hV u₀ α ha hB.choose_spec.1 hB.choose_spec.2
    ⟨(half_lt_self ht.1).le, ht.2⟩).choose_spec.2 ψ hψ k

lemma exists_D_U_norm_bound {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν)
    {V : ℝ → Plane → F8Ex.RMerid} (hV : F8Ex.IsSmoothBUCDrift c V)
    (u₀ : H1Sol c) (α : List (Fin 2)) {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 2) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ {t : ℝ}, t ∈ Ico a 2 → ‖D_U hc hν hV u₀ α t‖ ≤ M := by
  obtain ⟨B, hB_nn, hB⟩ := exists_HkEnergy_uniform_bound hc hν hV u₀ α.length ha
  refine ⟨Real.sqrt B, Real.sqrt_nonneg B, ?_⟩
  intro t ht
  have ht_ioo : t ∈ Ioo (0 : ℝ) 2 := ⟨lt_of_lt_of_le ha.1 ht.1, ht.2⟩
  obtain ⟨g, hg_norm, hg_pair⟩ := exists_weak_deriv_E_oseen hc hν hV u₀ α ha hB_nn hB ht
  have h_eq : D_U hc hν hV u₀ α t = g :=
    eq_of_inner_cylSmooth_single fun ψ hψ k => by
      rw [D_U_inner_single hc hν hV u₀ α ht_ioo ψ hψ k, hg_pair ψ hψ k]
  rwa [h_eq]

lemma D_U_nil_eq {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν)
    {V : ℝ → Plane → F8Ex.RMerid} (hV : F8Ex.IsSmoothBUCDrift c V)
    (u₀ : H1Sol c) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 2) :
    D_U hc hν hV u₀ [] t = val0CLM c (E_oseen hc hν hV t 0 u₀) :=
  eq_of_inner_cylSmooth_single fun ψ hψ k => by
    simpa [pdIterRev] using D_U_inner_single hc hν hV u₀ [] ht ψ hψ k

lemma hasWeakDeriv1_D_U {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν)
    {V : ℝ → Plane → F8Ex.RMerid} (hV : F8Ex.IsSmoothBUCDrift c V)
    (u₀ : H1Sol c) (j : Fin 2) (β : List (Fin 2)) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 2) :
    HasWeakDeriv1 c j (D_U hc hν hV u₀ β t) (D_U hc hν hV u₀ (j :: β) t) := by
  rw [hasWeakDeriv1_iff_inner]
  intro ψ hψ k
  rw [D_U_inner_single hc hν hV u₀ β ht (B0579.pd j ψ) (hψ.pd j) k,
    D_U_inner_single hc hν hV u₀ (j :: β) ht ψ hψ k,
    List.length_cons, pow_succ]
  dsimp only [pdIterRev]
  ring

lemma hasIterWeakDeriv_D_U {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν)
    {V : ℝ → Plane → F8Ex.RMerid} (hV : F8Ex.IsSmoothBUCDrift c V)
    (u₀ : H1Sol c) :
    ∀ (α : List (Fin 2)) {t : ℝ}, t ∈ Ioo (0 : ℝ) 2 →
      HasIterWeakDeriv c α (val0CLM c (E_oseen hc hν hV t 0 u₀)) (D_U hc hν hV u₀ α t)
  | [], _, ht => (D_U_nil_eq hc hν hV u₀ ht).symm
  | j :: β, t, ht =>
      ⟨D_U hc hν hV u₀ β t, hasIterWeakDeriv_D_U hc hν hV u₀ β ht,
        hasWeakDeriv1_D_U hc hν hV u₀ j β ht⟩

private lemma hasIterWeakDeriv_sub {c : ℝ} :
    ∀ {α : List (Fin 2)} {u₁ g₁ u₂ g₂ : L2v c},
      HasIterWeakDeriv c α u₁ g₁ → HasIterWeakDeriv c α u₂ g₂ →
        HasIterWeakDeriv c α (u₁ - u₂) (g₁ - g₂)
  | [], _, _, _, _, rfl, rfl => rfl
  | _ :: _, _, _, _, _, ⟨h₁, hα₁, hj₁⟩, ⟨h₂, hα₂, hj₂⟩ =>
      ⟨h₁ - h₂, hasIterWeakDeriv_sub hα₁ hα₂, hj₁.sub hj₂⟩

/-- `C((0, 2); L2v c)` continuity of every spatial derivative `D_U α`, proved by induction on `α`
via viscous cell IBP interpolation `‖∂_j g‖² = -⟪g, ∂_j² g⟫ ≤ ‖g‖ ‖∂_j² g‖`. -/
theorem continuousOn_D_U {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν)
    {V : ℝ → Plane → F8Ex.RMerid} (hV : F8Ex.IsSmoothBUCDrift c V)
    (u₀ : H1Sol c) :
    ∀ (α : List (Fin 2)), ContinuousOn (D_U hc hν hV u₀ α) (Ioo (0 : ℝ) 2)
  | [] => by
      have hcE : ContinuousOn (fun t => val0CLM c (E_oseen hc hν hV t 0 u₀)) (Ioo 0 2) :=
        (val0CLM c).continuous.comp_continuousOn
          ((continuousOn_E_oseen hc hν hV ⟨le_rfl, zero_le_two⟩ u₀).mono Ioo_subset_Icc_self)
      exact hcE.congr fun t ht => D_U_nil_eq hc hν hV u₀ ht
  | j :: β => by
      have ih := continuousOn_D_U hc hν hV u₀ β
      intro t₀ ht₀
      refine ContinuousAt.continuousWithinAt ?_
      have hβ_at : ContinuousAt (D_U hc hν hV u₀ β) t₀ :=
        ih.continuousAt (isOpen_Ioo.mem_nhds ht₀)
      let a : ℝ := t₀ / 2
      have ha : a ∈ Ioo (0 : ℝ) 2 := ⟨half_pos ht₀.1, (half_lt_self ht₀.1).trans ht₀.2⟩
      obtain ⟨M, _, hM⟩ := exists_D_U_norm_bound hc hν hV u₀ (j :: j :: β) ha
      have hsq_le : ∀ᶠ t : ℝ in 𝓝 t₀,
          ‖D_U hc hν hV u₀ (j :: β) t - D_U hc hν hV u₀ (j :: β) t₀‖ ^ 2 ≤
            (2 * M) * ‖D_U hc hν hV u₀ β t - D_U hc hν hV u₀ β t₀‖ := by
        filter_upwards [Ioo_mem_nhds (half_lt_self ht₀.1) ht₀.2] with t ht_sub
        have ht : t ∈ Ioo (0 : ℝ) 2 := ⟨lt_trans ha.1 ht_sub.1, ht_sub.2⟩
        obtain ⟨G_sm, hG_sm, _, hG_lp⟩ := exists_smooth_rep_of_iterWeak hc
          (val0CLM c (E_oseen hc hν hV t 0 u₀) - val0CLM c (E_oseen hc hν hV t₀ 0 u₀))
          (fun _ γ => D_U hc hν hV u₀ (List.ofFn γ) t - D_U hc hν hV u₀ (List.ofFn γ) t₀)
          (fun _ γ => hasIterWeakDeriv_sub
            (hasIterWeakDeriv_D_U hc hν hV u₀ (List.ofFn γ) ht)
            (hasIterWeakDeriv_D_U hc hν hV u₀ (List.ofFn γ) ht₀))
        have hibp := inner_slicePdIterR_ibp hc hG_sm β.get j
        have hl0 : List.ofFn β.get = β := List.ofFn_get β
        have hl1 : List.ofFn (Fin.cons j β.get) = j :: β :=
          (list_ofFn_cons j β.get).trans (congrArg (j :: ·) hl0)
        have hl2 : List.ofFn (Fin.cons j (Fin.cons j β.get)) = j :: j :: β :=
          (list_ofFn_cons j _).trans (congrArg (j :: ·) hl1)
        rw [hG_lp hG_sm β.length β.get,
          hG_lp hG_sm (β.length + 2) (Fin.cons j (Fin.cons j β.get)),
          hG_lp hG_sm (β.length + 1) (Fin.cons j β.get),
          hl0, hl1, hl2] at hibp
        have hcs := abs_real_inner_le_norm
          (D_U hc hν hV u₀ β t - D_U hc hν hV u₀ β t₀)
          (D_U hc hν hV u₀ (j :: j :: β) t - D_U hc hν hV u₀ (j :: j :: β) t₀)
        have htop_le : ‖D_U hc hν hV u₀ (j :: j :: β) t - D_U hc hν hV u₀ (j :: j :: β) t₀‖ ≤
            2 * M := by
          have hb_t : ‖D_U hc hν hV u₀ (j :: j :: β) t‖ ≤ M := hM ⟨ht_sub.1.le, ht_sub.2⟩
          have hb_0 : ‖D_U hc hν hV u₀ (j :: j :: β) t₀‖ ≤ M :=
            hM ⟨(half_lt_self ht₀.1).le, ht₀.2⟩
          exact (norm_sub_le _ _).trans (by linarith)
        have hsq_eq : ‖D_U hc hν hV u₀ (j :: β) t - D_U hc hν hV u₀ (j :: β) t₀‖ ^ 2 =
            -⟪D_U hc hν hV u₀ β t - D_U hc hν hV u₀ β t₀,
              D_U hc hν hV u₀ (j :: j :: β) t - D_U hc hν hV u₀ (j :: j :: β) t₀⟫_ℝ := by
          linarith [hibp]
        calc ‖D_U hc hν hV u₀ (j :: β) t - D_U hc hν hV u₀ (j :: β) t₀‖ ^ 2
            ≤ |⟪D_U hc hν hV u₀ β t - D_U hc hν hV u₀ β t₀,
                D_U hc hν hV u₀ (j :: j :: β) t - D_U hc hν hV u₀ (j :: j :: β) t₀⟫_ℝ| := by
              rw [hsq_eq]; exact neg_le_abs _
          _ ≤ ‖D_U hc hν hV u₀ β t - D_U hc hν hV u₀ β t₀‖ *
              ‖D_U hc hν hV u₀ (j :: j :: β) t - D_U hc hν hV u₀ (j :: j :: β) t₀‖ := hcs
          _ ≤ ‖D_U hc hν hV u₀ β t - D_U hc hν hV u₀ β t₀‖ * (2 * M) :=
              mul_le_mul_of_nonneg_left htop_le (norm_nonneg _)
          _ = (2 * M) * ‖D_U hc hν hV u₀ β t - D_U hc hν hV u₀ β t₀‖ := mul_comm _ _
      rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
      have htend_rhs : Tendsto
          (fun t => Real.sqrt ((2 * M) * ‖D_U hc hν hV u₀ β t - D_U hc hν hV u₀ β t₀‖))
          (𝓝 t₀) (𝓝 0) := by
        have h0 : Tendsto (fun t => ‖D_U hc hν hV u₀ β t - D_U hc hν hV u₀ β t₀‖) (𝓝 t₀) (𝓝 0) :=
          tendsto_iff_norm_sub_tendsto_zero.mp hβ_at
        have h1 : Tendsto (fun t => (2 * M) * ‖D_U hc hν hV u₀ β t - D_U hc hν hV u₀ β t₀‖)
            (𝓝 t₀) (𝓝 0) := by
          simpa only [mul_zero] using h0.const_mul (2 * M)
        have h2 := (Real.continuous_sqrt.tendsto 0).comp h1
        rwa [Real.sqrt_zero] at h2
      refine squeeze_zero_norm' ?_ htend_rhs
      filter_upwards [hsq_le] with t ht_le
      rw [Real.norm_of_nonneg (norm_nonneg _), ← Real.sqrt_sq (norm_nonneg _)]
      exact Real.sqrt_le_sqrt ht_le

/-! ## 4. Smooth Periodic Slice Extraction on `(0, 2)` -/

/-- Smooth `c`-periodic slice family `wSlice hc hν hV u₀` on `(0, 2)` (`0` outside `(0, 2)`). -/
def wSlice {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν)
    {V : ℝ → Plane → F8Ex.RMerid} (hV : F8Ex.IsSmoothBUCDrift c V)
    (u₀ : H1Sol c) (s : ℝ) : B0579.Plane → F8Ex.RMerid :=
  open Classical in
  if hs : s ∈ Ioo (0 : ℝ) 2 then
    (exists_smooth_rep_of_iterWeak hc
      (val0CLM c (E_oseen hc hν hV s 0 u₀))
      (fun _ α => D_U hc hν hV u₀ (List.ofFn α) s)
      (fun _ α => hasIterWeakDeriv_D_U hc hν hV u₀ (List.ofFn α) hs)).choose
  else
    0

lemma wSlice_spec {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν)
    {V : ℝ → Plane → F8Ex.RMerid} (hV : F8Ex.IsSmoothBUCDrift c V)
    (u₀ : H1Sol c) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 2) :
    IsCylSmoothHInf c (wSlice hc hν hV u₀ s) ∧
    (∀ (n : ℕ) (α : Fin n → Fin 2),
      F8Ex.slicePdIterR α (wSlice hc hν hV u₀ s) =ᵐ[F8Ex.cellMeas c]
        (D_U hc hν hV u₀ (List.ofFn α) s : B0579.Plane → F8Ex.RMerid)) ∧
    (∀ (hW : IsCylSmoothHInf c (wSlice hc hν hV u₀ s)) (n : ℕ) (α : Fin n → Fin 2),
      toLpCell (hW.memL2 n α) = D_U hc hν hV u₀ (List.ofFn α) s) := by
  unfold wSlice
  rw [dite_eq_left hs]
  exact (exists_smooth_rep_of_iterWeak hc
    (val0CLM c (E_oseen hc hν hV s 0 u₀))
    (fun _ α => D_U hc hν hV u₀ (List.ofFn α) s)
    (fun _ α => hasIterWeakDeriv_D_U hc hν hV u₀ (List.ofFn α) hs)).choose_spec

end UnforcedLeray.Short.IIb.F8MildBoot

namespace UnforcedLeray.Short.IIb

open F8MildBoot
open F8JointUpgrade

/-- **Target theorem** (`PartII-b:F8/1/org/2/2/2`, SP 2052–2053, 2213–2217, 2296–2301):
interior parabolic spatial bootstrap (`H¹_σ(C_c) → H^∞_σ(C_c)`) on `(0, 2)` for the canonical
Volterra mild cylinder Oseen evolution `F8WeakEx.E_oseen hc hν hV s 0 u₀`. -/
theorem realCylOseenMildSpatialBootstrap_proof :
    UnforcedLeray.Short.IIb.RealCylOseenMildSpatialBootstrap := by
  intro c ν hc hν V hV u₀
  refine ⟨wSlice hc hν hV u₀, ?_⟩
  refine
    { ae_val := fun s hs => ?_
      ae_dq := fun s hs => ?_
      ae_deta := fun s hs => ?_
      spatial_smooth := fun s hs => (wSlice_spec hc hν hV u₀ hs).1.smooth
      periodic := fun s hs => (wSlice_spec hc hν hV u₀ hs).1.periodic
      div_free := fun s hs => ?_
      memL2_all := fun s hs n α => (wSlice_spec hc hν hV u₀ hs).1.memL2 n α
      cont_all := fun s hs n α => ?_ }
  · -- `ae_val`
    have hae := (wSlice_spec hc hν hV u₀ hs).2.1 0 Fin.elim0
    have hl0 : List.ofFn (Fin.elim0 : Fin 0 → Fin 2) = [] := List.ofFn_zero
    rw [hl0, D_U_nil_eq hc hν hV u₀ hs] at hae
    exact hae
  · -- `ae_dq`
    have hae := (wSlice_spec hc hν hV u₀ hs).2.1 1 ![0]
    have hdu : D_U hc hν hV u₀ [0] s = F8WeakEx.dqCLM c (F8WeakEx.E_oseen hc hν hV s 0 u₀) := by
      have hw := hasWeakDeriv1_D_U hc hν hV u₀ 0 [] hs
      rw [D_U_nil_eq hc hν hV u₀ hs] at hw
      exact hw.unique hc (F8WeakEx.H1Sol.weak_q _)
    have hl1 : List.ofFn (![0] : Fin 1 → Fin 2) = [0] := by simp
    rw [hl1, hdu] at hae
    exact hae
  · -- `ae_deta`
    have hae := (wSlice_spec hc hν hV u₀ hs).2.1 1 ![1]
    have hdu : D_U hc hν hV u₀ [1] s = F8WeakEx.detaCLM c (F8WeakEx.E_oseen hc hν hV s 0 u₀) := by
      have hw := hasWeakDeriv1_D_U hc hν hV u₀ 1 [] hs
      rw [D_U_nil_eq hc hν hV u₀ hs] at hw
      exact hw.unique hc (F8WeakEx.H1Sol.weak_eta _)
    have hl1 : List.ofFn (![1] : Fin 1 → Fin 2) = [1] := by simp
    rw [hl1, hdu] at hae
    exact hae
  · -- `div_free`
    obtain ⟨hW, _, hlp⟩ := wSlice_spec hc hν hV u₀ hs
    refine div_free_of_isCylSmoothHInf hc hW ?_
    have hl0 : List.ofFn (Fin.elim0 : Fin 0 → Fin 2) = [] := List.ofFn_zero
    rw [hlp hW 0 Fin.elim0, hl0, D_U_nil_eq hc hν hV u₀ hs]
    exact F8WeakEx.H1Sol.mem_divFree _
  · -- `cont_all`
    have hc_at : ContinuousAt (D_U hc hν hV u₀ (List.ofFn α)) s :=
      (continuousOn_D_U hc hν hV u₀ (List.ofFn α)).continuousAt (isOpen_Ioo.mem_nhds hs)
    have htend_norm : Tendsto
        (fun t => ‖D_U hc hν hV u₀ (List.ofFn α) t - D_U hc hν hV u₀ (List.ofFn α) s‖)
        (𝓝 s) (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.mp hc_at
    have htend_enn : Tendsto
        (fun t => ENNReal.ofReal
          ‖D_U hc hν hV u₀ (List.ofFn α) t - D_U hc hν hV u₀ (List.ofFn α) s‖)
        (𝓝 s) (𝓝 0) := by
      have hcomp := (ENNReal.continuous_ofReal.tendsto 0).comp htend_norm
      rwa [ENNReal.ofReal_zero] at hcomp
    obtain ⟨hWs, _, hlp_s⟩ := wSlice_spec hc hν hV u₀ hs
    refine htend_enn.congr' ?_
    filter_upwards [isOpen_Ioo.mem_nhds hs] with t ht
    obtain ⟨hWt, _, hlp_t⟩ := wSlice_spec hc hν hV u₀ ht
    have hlp : D_U hc hν hV u₀ (List.ofFn α) t - D_U hc hν hV u₀ (List.ofFn α) s =
        toLpCell ((hWt.memL2 n α).sub (hWs.memL2 n α)) := by
      rw [← hlp_t hWt n α, ← hlp_s hWs n α, ← toLpCell_sub]
    rw [hlp, ofReal_norm_toLpCell]
    rfl

end UnforcedLeray.Short.IIb
