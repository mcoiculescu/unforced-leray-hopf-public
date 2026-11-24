import UnforcedLeray.Short.PartIIb.Sub.PartIIb_F8_1_org_2
import UnforcedLeray.Lib.TrainB.P0SmoothH3
import UnforcedLeray.Short.PartI.Tasks.CylinderInterpolation.Agmon
import UnforcedLeray.Short.PartI.Tasks.LocalClassicalBounded.SpatialRepFromPersistent.CylSobolevRep

/-!
# Smooth Cylinder Sobolev Spaces, `0 < c` Sup Estimates, Liouville Uniqueness, and `P₀` on `H^∞`

Support module 2 for task `PartII-b:F8/1/org/2/3` (`RealCylOseenJointSmoothUpgrade`).
Bridges `F8Ex` slice predicates with `Cyl.L2v c` / `Cyl.H ℝ Cyl.Vec2 c 0 m`, establishes
period-positive (`0 < c`) cylinder Sobolev sup bounds without assuming `1 ≤ c`, proves uniqueness
in `Cyl.divFree c` against divergence-free cylinder test fields via `Cyl.eq_zero_of_curl_div`, and
constructs the smooth Leray projection `P0Smooth c` on smooth periodic `H^∞(C_c)` slices.
-/

set_option autoImplicit false
set_option maxHeartbeats 300000

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff InnerProductSpace

namespace UnforcedLeray.Short.IIb.F8JointUpgrade

open UnforcedLeray
open UnforcedLeray.Short.IIb

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

/-! ## 1. Cell, Test-Function, and `Cyl.L2v c` Bridges -/

lemma b0579_cell_eq_cyl_cell (c : ℝ) : B0579.cell c = Cyl.cell c := by
  simp [B0579.cell, Cyl.cell, neg_div]

lemma cellMeas_eq_cellμ (c : ℝ) : F8Ex.cellMeas c = Cyl.cellμ c := by
  simp [F8Ex.cellMeas, Cyl.cellμ, b0579_cell_eq_cyl_cell]

lemma isCylTest_iff_b0579 {c : ℝ} {φ : B0579.Plane → ℝ} :
    Sob.IsCylTest c φ ↔ B0579.IsCylTest c φ := by
  constructor
  · intro h
    refine ⟨h.smooth, fun x => ?_, h.bounded⟩
    have hx : ((x.1 + c, x.2) : B0579.Plane) = x + (c, 0) := by ext <;> simp
    rw [hx]
    exact h.periodic x
  · intro h
    refine ⟨h.smooth, fun x => ?_, h.band⟩
    have hx : x + ((c, 0) : B0579.Plane) = (x.1 + c, x.2) := by ext <;> simp
    rw [hx]
    exact h.periodic x

lemma memLp_to_cellμ {c : ℝ} {f : B0579.Plane → F8Ex.RMerid}
    (hf : MemLp f 2 (F8Ex.cellMeas c)) : MemLp f 2 (Cyl.cellμ c) :=
  cellMeas_eq_cellμ c ▸ hf

lemma memLp_of_cellμ {c : ℝ} {f : B0579.Plane → F8Ex.RMerid}
    (hf : MemLp f 2 (Cyl.cellμ c)) : MemLp f 2 (F8Ex.cellMeas c) :=
  (cellMeas_eq_cellμ c).symm ▸ hf

/-- Representative-transparent embedding of a `MemLp · 2 (F8Ex.cellMeas c)` slice into `Cyl.L2v c`. -/
def toLpCell {c : ℝ} {f : B0579.Plane → F8Ex.RMerid}
    (hf : MemLp f 2 (F8Ex.cellMeas c)) : Cyl.L2v c :=
  (memLp_to_cellμ hf).toLp f

lemma coeFn_toLpCell {c : ℝ} {f : B0579.Plane → F8Ex.RMerid}
    (hf : MemLp f 2 (F8Ex.cellMeas c)) :
    (toLpCell hf : B0579.Plane → F8Ex.RMerid) =ᵐ[Cyl.cellμ c] f :=
  (memLp_to_cellμ hf).coeFn_toLp

lemma coeFn_toLpCell_cellMeas {c : ℝ} {f : B0579.Plane → F8Ex.RMerid}
    (hf : MemLp f 2 (F8Ex.cellMeas c)) :
    (toLpCell hf : B0579.Plane → F8Ex.RMerid) =ᵐ[F8Ex.cellMeas c] f := by
  rw [cellMeas_eq_cellμ]
  exact coeFn_toLpCell hf

lemma toLpCell_congr_ae {c : ℝ} {f g : B0579.Plane → F8Ex.RMerid}
    (hf : MemLp f 2 (F8Ex.cellMeas c)) (hg : MemLp g 2 (F8Ex.cellMeas c))
    (hfg : f =ᵐ[F8Ex.cellMeas c] g) :
    toLpCell hf = toLpCell hg := by
  apply Lp.ext
  have hfg' : f =ᵐ[Cyl.cellμ c] g := by rwa [← cellMeas_eq_cellμ]
  exact (coeFn_toLpCell hf).trans (hfg'.trans (coeFn_toLpCell hg).symm)

@[simp]
lemma toLpCell_zero (c : ℝ) :
    toLpCell (MemLp.zero : MemLp (0 : B0579.Plane → F8Ex.RMerid) 2 (F8Ex.cellMeas c)) = 0 :=
  MemLp.toLp_zero _

lemma toLpCell_add {c : ℝ} {f g : B0579.Plane → F8Ex.RMerid}
    (hf : MemLp f 2 (F8Ex.cellMeas c)) (hg : MemLp g 2 (F8Ex.cellMeas c)) :
    toLpCell (hf.add hg) = toLpCell hf + toLpCell hg :=
  MemLp.toLp_add (memLp_to_cellμ hf) (memLp_to_cellμ hg)

lemma toLpCell_sub {c : ℝ} {f g : B0579.Plane → F8Ex.RMerid}
    (hf : MemLp f 2 (F8Ex.cellMeas c)) (hg : MemLp g 2 (F8Ex.cellMeas c)) :
    toLpCell (hf.sub hg) = toLpCell hf - toLpCell hg :=
  MemLp.toLp_sub (memLp_to_cellμ hf) (memLp_to_cellμ hg)

lemma toLpCell_neg {c : ℝ} {f : B0579.Plane → F8Ex.RMerid}
    (hf : MemLp f 2 (F8Ex.cellMeas c)) :
    toLpCell hf.neg = -toLpCell hf :=
  MemLp.toLp_neg (memLp_to_cellμ hf)

lemma toLpCell_smul {c : ℝ} (r : ℝ) {f : B0579.Plane → F8Ex.RMerid}
    (hf : MemLp f 2 (F8Ex.cellMeas c)) :
    toLpCell (hf.const_smul r) = r • toLpCell hf :=
  MemLp.toLp_const_smul r (memLp_to_cellμ hf)

lemma ofReal_norm_toLpCell {c : ℝ} {f : B0579.Plane → F8Ex.RMerid}
    (hf : MemLp f 2 (F8Ex.cellMeas c)) :
    ENNReal.ofReal ‖toLpCell hf‖ = F8Ex.cellL2R c f := by
  rw [ofReal_norm, Lp.enorm_def, eLpNorm_congr_ae (coeFn_toLpCell hf), ← cellMeas_eq_cellμ]
  rfl

lemma inner_toLpCell_eq {c : ℝ} {f g : B0579.Plane → F8Ex.RMerid}
    (hf : MemLp f 2 (F8Ex.cellMeas c)) (hg : MemLp g 2 (F8Ex.cellMeas c)) :
    ⟪toLpCell hf, toLpCell hg⟫_ℝ = ∫ y in B0579.cell c, ⟪f y, g y⟫_ℝ := by
  rw [toLpCell, toLpCell, Cyl.inner_toLp_eq, b0579_cell_eq_cyl_cell]

lemma inner_toLpCell_left {c : ℝ} {f : B0579.Plane → F8Ex.RMerid}
    (hf : MemLp f 2 (F8Ex.cellMeas c)) (g : Cyl.L2v c) :
    ⟪toLpCell hf, g⟫_ℝ = ∫ y in Cyl.cell c, ⟪f y, (g : B0579.Plane → Cyl.Vec2) y⟫_ℝ :=
  Cyl.inner_toLp_left (memLp_to_cellμ hf) g

lemma toLpCell_mem_divFree_iff {c : ℝ} {f : B0579.Plane → F8Ex.RMerid}
    (hf : MemLp f 2 (F8Ex.cellMeas c)) :
    toLpCell hf ∈ Cyl.divFree c ↔ F8Ex.IsRealCellSolenoidal c f := by
  rw [Cyl.mem_divFree]
  have hpt : ∀ (φ : B0579.Plane → ℝ) (hφ : Sob.IsCylTest c φ) (y : B0579.Plane),
      ⟪Cyl.gradT φ y, f y⟫_ℝ = f y 0 * B0579.pd 0 φ y + f y 1 * B0579.pd 1 φ y := by
    intro φ hφ y
    have hd := hφ.differentiable
    rw [real_inner_comm, Cyl.gradT, Cyl.inner_vec,
      Cyl.partialQ_eq_fderiv hd y, Cyl.partialEta_eq_fderiv hd y]
    rfl
  constructor
  · intro h ψ hψ
    have hψ' : Sob.IsCylTest c ψ := isCylTest_iff_b0579.mpr hψ
    have hint : IntegrableOn (fun y => ⟪Cyl.gradT ψ y, f y⟫_ℝ) (B0579.cell c) :=
      F8Ex.integrableOn_innerR_cell (memLp_of_cellμ (Cyl.memLp_gradT hψ')) hf
    have hint' : IntegrableOn (fun y => f y 0 * B0579.pd 0 ψ y + f y 1 * B0579.pd 1 ψ y)
        (B0579.cell c) :=
      hint.congr_fun (fun y _ => hpt ψ hψ' y) (B0579.measurableSet_cell c)
    refine ⟨hint', ?_⟩
    rw [b0579_cell_eq_cyl_cell]
    have h0 := h ψ hψ'
    rw [Cyl.gradL, toLpCell, Cyl.inner_toLp_eq] at h0
    simpa only [hpt ψ hψ'] using h0
  · intro h φ hφ
    have hφ' : B0579.IsCylTest c φ := isCylTest_iff_b0579.mp hφ
    have h0 := (h φ hφ').2
    rw [b0579_cell_eq_cyl_cell] at h0
    rw [Cyl.gradL, toLpCell, Cyl.inner_toLp_eq]
    simpa only [hpt φ hφ] using h0

/-! ## 2. Uniqueness in `Cyl.divFree c` Against Solenoidal Cylinder Tests (`0 < c`) -/

lemma isRealSolCylTest_rotT {c : ℝ} {φ : B0579.Plane → ℝ}
    (hφ : Sob.IsCylTest c φ) : F8Ex.IsRealSolCylTest c (Cyl.rotT φ) where
  cyl_test k := by
    fin_cases k
    · exact isCylTest_iff_b0579.mp (Cyl.isCylTest_partialEta hφ)
    · have hq := Cyl.isCylTest_partialQ hφ
      have hneg : Sob.IsCylTest c (fun y => -Cyl.partialQ φ y) :=
        ⟨hq.smooth.neg, fun z => by simp [hq.periodic z],
          let ⟨R, hR⟩ := hq.bounded; ⟨R, fun z hz => by simp [hR z hz]⟩⟩
      exact isCylTest_iff_b0579.mp hneg
  div_free y := by
    have hdφ := hφ.differentiable
    have hη_sm := Cyl.isCylTest_partialEta hφ
    have hq_sm := Cyl.isCylTest_partialQ hφ
    have hfunη : Cyl.partialEta φ = fun w => fderiv ℝ φ w ((0 : ℝ), (1 : ℝ)) :=
      funext (Cyl.partialEta_eq_fderiv hdφ)
    have hfunq : (fun w => -Cyl.partialQ φ w) = fun w => -fderiv ℝ φ w ((1 : ℝ), (0 : ℝ)) := by
      funext w
      rw [Cyl.partialQ_eq_fderiv hdφ w]
    have h1 : Cyl.partialQ (fun w => Cyl.rotT φ w 0) y =
        Sob.iterDirDeriv [((1 : ℝ), (0 : ℝ)), ((0 : ℝ), (1 : ℝ))] φ y := by
      change Cyl.partialQ (Cyl.partialEta φ) y = _
      rw [Cyl.partialQ_eq_fderiv hη_sm.differentiable y, hfunη]
      rfl
    have h2 : Cyl.partialEta (fun w => Cyl.rotT φ w 1) y =
        -Sob.iterDirDeriv [((0 : ℝ), (1 : ℝ)), ((1 : ℝ), (0 : ℝ))] φ y := by
      change Cyl.partialEta (fun w => -Cyl.partialQ φ w) y = _
      rw [Cyl.partialEta_eq_fderiv hq_sm.differentiable.fun_neg y, fderiv_fun_neg, neg_apply]
      congr 1
      rw [funext (Cyl.partialQ_eq_fderiv hdφ)]
      rfl
    have hsymm : Sob.iterDirDeriv [((1 : ℝ), (0 : ℝ)), ((0 : ℝ), (1 : ℝ))] φ =
        Sob.iterDirDeriv [((0 : ℝ), (1 : ℝ)), ((1 : ℝ), (0 : ℝ))] φ :=
      Sob.iterDirDeriv_perm (List.Perm.swap ((0 : ℝ), (1 : ℝ)) ((1 : ℝ), (0 : ℝ)) []) hφ.smooth
    unfold Cyl.divergence
    rw [h1, h2, congrFun hsymm y, add_neg_cancel]

private noncomputable def pairH10 {c : ℝ} {h : B0579.Plane → ℝ}
    (hh0 : MemLp h 2 (Sob.wμ (Sob.cylinder c).μ (Cyl.ρ0 c))) : Cyl.Hneg c 0 1 :=
  (innerSL ℝ (hh0.toLp h)).comp
    (Sob.W.value (Sob.cylinder c) (Cyl.ρ0 c) ℝ ℝ 1 2)

private lemma pairH10_testH {c : ℝ} (hc : 0 < c) {h : B0579.Plane → ℝ}
    (hh0 : MemLp h 2 (Sob.wμ (Sob.cylinder c).μ (Cyl.ρ0 c)))
    {ψ : B0579.Plane → ℝ} (hψ : Sob.IsCylTest c ψ) :
    pairH10 hh0 (Cyl.testH hc hψ (Cyl.ρ0 c) 1) = ∫ z in Cyl.cell c, h z * ψ z := by
  simp only [pairH10, ContinuousLinearMap.comp_apply, innerSL_apply_apply]
  rw [L2.inner_def]
  have hcoe1 : (hh0.toLp h : Cyl.Plane → ℝ) =ᵐ[Cyl.cellμ c] h := by
    rw [← Cyl.wμ_ρwW_zero_inv c]
    exact hh0.coeFn_toLp
  have hcoe2 : (Sob.W.value (Sob.cylinder c) (Cyl.ρ0 c) ℝ ℝ 1 2
      (Cyl.testH hc hψ (Cyl.ρ0 c) 1) : Cyl.Plane → ℝ) =ᵐ[Cyl.cellμ c] ψ := by
    have hv := Cyl.ae_cell_of_cylinder (Cyl.coeFn_deriv_testH hc hψ (Cyl.ρ0 c) 1 Sob.Idx.zero)
    have h1 := Sob.W.deriv_zero (D := Sob.cylinder c) (ρ := Cyl.ρ0 c) (𝕜 := ℝ) (F := ℝ)
      (k := 1) (p := 2) (Cyl.testH hc hψ (Cyl.ρ0 c) 1)
    have h2 : Sob.iterDirDeriv ((Sob.cylinder c).word (Sob.Idx.zero : Sob.Idx 2 1)) ψ = ψ := by
      rw [Cyl.word_zero, Sob.iterDirDeriv_nil]
    rwa [h1, h2] at hv
  rw [Cyl.integral_wμ0]
  refine integral_congr_ae ?_
  filter_upwards [hcoe1, hcoe2] with z hz1 hz2
  simp only [RCLike.inner_apply, conj_trivial]
  rw [hz1, hz2, mul_comm]

/-- A divergence-free field in `Cyl.L2v c` (`0 < c`) orthogonal to every solenoidal cylinder test
field vanishes in `Cyl.L2v c`. -/
lemma eq_zero_of_divFree_and_ortho_solTest {c : ℝ} (hc : 0 < c) (g : Cyl.L2v c)
    (hg : g ∈ Cyl.divFree c)
    (horth : ∀ (Φ : B0579.Plane → F8Ex.RMerid) (hΦ : F8Ex.IsRealSolCylTest c Φ),
      ⟪toLpCell (F8Ex.memLp_realSolCylTest hΦ), g⟫_ℝ = 0) :
    g = 0 := by
  let g0 : B0579.Plane → ℝ := fun z => (g : B0579.Plane → Cyl.Vec2) z 0
  let g1 : B0579.Plane → ℝ := fun z => (g : B0579.Plane → Cyl.Vec2) z 1
  have hg0 : MemLp g0 2 (Cyl.cellμ c) :=
    (EuclideanSpace.proj (0 : Fin 2) : Cyl.Vec2 →L[ℝ] ℝ).comp_memLp' (Lp.memLp g)
  have hg1 : MemLp g1 2 (Cyl.cellμ c) :=
    (EuclideanSpace.proj (1 : Fin 2) : Cyl.Vec2 →L[ℝ] ℝ).comp_memLp' (Lp.memLp g)
  have hg0w : MemLp g0 2 (Sob.wμ (Sob.cylinder c).μ (Cyl.ρ0 c)) :=
    (Cyl.wμ_ρwW_zero_inv c).symm ▸ hg0
  have hg1w : MemLp g1 2 (Sob.wμ (Sob.cylinder c).μ (Cyl.ρ0 c)) :=
    (Cyl.wμ_ρwW_zero_inv c).symm ▸ hg1
  let D : Cyl.Hneg c 0 1 × Cyl.Hneg c 0 1 := (pairH10 hg0w, pairH10 hg1w)
  have hcurl : ∀ (φ : B0579.Plane → ℝ) (hφ : Sob.IsCylTest c φ),
      D.1 (Cyl.testH hc (hφ.dirDeriv ((0 : ℝ), (1 : ℝ))) (Cyl.ρ0 c) 1) -
        D.2 (Cyl.testH hc (hφ.dirDeriv ((1 : ℝ), (0 : ℝ))) (Cyl.ρ0 c) 1) = 0 := by
    intro φ hφ
    have hdφ := hφ.differentiable
    change pairH10 hg0w _ - pairH10 hg1w _ = 0
    rw [pairH10_testH hc hg0w (hφ.dirDeriv ((0 : ℝ), (1 : ℝ))),
      pairH10_testH hc hg1w (hφ.dirDeriv ((1 : ℝ), (0 : ℝ)))]
    have hi0 : IntegrableOn (fun z => g0 z * fderiv ℝ φ z ((0 : ℝ), (1 : ℝ))) (Cyl.cell c) :=
      Cyl.integrableOn_test_mul (hφ.dirDeriv ((0 : ℝ), (1 : ℝ))) hg0 |> fun h => by
        refine h.congr_fun (fun z _ => ?_) (Cyl.measurableSet_cell c)
        ring
    have hi1 : IntegrableOn (fun z => g1 z * fderiv ℝ φ z ((1 : ℝ), (0 : ℝ))) (Cyl.cell c) :=
      Cyl.integrableOn_test_mul (hφ.dirDeriv ((1 : ℝ), (0 : ℝ))) hg1 |> fun h => by
        refine h.congr_fun (fun z _ => ?_) (Cyl.measurableSet_cell c)
        ring
    rw [← integral_sub hi0 hi1]
    have hrot := horth (Cyl.rotT φ) (isRealSolCylTest_rotT hφ)
    rw [inner_toLpCell_left] at hrot
    refine Eq.trans ?_ hrot
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    dsimp only
    rw [real_inner_comm, Cyl.rotT, Cyl.inner_vec,
      Cyl.partialEta_eq_fderiv hdφ z, Cyl.partialQ_eq_fderiv hdφ z]
    simp only [g0, g1]
    ring
  have hdiv : ∀ (φ : B0579.Plane → ℝ) (hφ : Sob.IsCylTest c φ),
      D.1 (Cyl.testH hc (hφ.dirDeriv ((1 : ℝ), (0 : ℝ))) (Cyl.ρ0 c) 1) +
        D.2 (Cyl.testH hc (hφ.dirDeriv ((0 : ℝ), (1 : ℝ))) (Cyl.ρ0 c) 1) = 0 := by
    intro φ hφ
    have hdφ := hφ.differentiable
    change pairH10 hg0w _ + pairH10 hg1w _ = 0
    rw [pairH10_testH hc hg0w (hφ.dirDeriv ((1 : ℝ), (0 : ℝ))),
      pairH10_testH hc hg1w (hφ.dirDeriv ((0 : ℝ), (1 : ℝ)))]
    have hi0 : IntegrableOn (fun z => g0 z * fderiv ℝ φ z ((1 : ℝ), (0 : ℝ))) (Cyl.cell c) :=
      Cyl.integrableOn_test_mul (hφ.dirDeriv ((1 : ℝ), (0 : ℝ))) hg0 |> fun h => by
        refine h.congr_fun (fun z _ => ?_) (Cyl.measurableSet_cell c)
        ring
    have hi1 : IntegrableOn (fun z => g1 z * fderiv ℝ φ z ((0 : ℝ), (1 : ℝ))) (Cyl.cell c) :=
      Cyl.integrableOn_test_mul (hφ.dirDeriv ((0 : ℝ), (1 : ℝ))) hg1 |> fun h => by
        refine h.congr_fun (fun z _ => ?_) (Cyl.measurableSet_cell c)
        ring
    rw [← integral_add hi0 hi1]
    have hgr := Cyl.mem_divFree.mp hg φ hφ
    rw [Cyl.gradL, Cyl.inner_toLp_left] at hgr
    refine Eq.trans ?_ hgr
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    dsimp only
    rw [real_inner_comm, Cyl.gradT, Cyl.inner_vec,
      Cyl.partialQ_eq_fderiv hdφ z, Cyl.partialEta_eq_fderiv hdφ z]
  have hD0 := Cyl.eq_zero_of_curl_div hc D hcurl hdiv
  have hD1 : pairH10 hg0w = 0 := congrArg Prod.fst hD0
  have hD2 : pairH10 hg1w = 0 := congrArg Prod.snd hD0
  have hae_comp : ∀ (hi : B0579.Plane → ℝ) (hmi : MemLp hi 2 (Cyl.cellμ c))
      (hmiw : MemLp hi 2 (Sob.wμ (Sob.cylinder c).μ (Cyl.ρ0 c))),
      pairH10 hmiw = 0 → hi =ᵐ[Cyl.cellμ c] 0 := by
    intro hi hmi hmiw hp0
    have hmi' : MemLp hi 2 (Sob.cylinder c).μ := (Cyl.cylinder_μ_eq c).symm ▸ hmi
    have hae_cyl : hi =ᵐ[(Sob.cylinder c).μ] 0 := by
      refine (Sob.cylinder c).ae_zero hi (hmi'.locallyIntegrable (by norm_num)) (fun ψ hψ => ?_)
      have hp := congrArg (fun L : Cyl.Hneg c 0 1 => L (Cyl.testH hc hψ (Cyl.ρ0 c) 1)) hp0
      simp only [zero_apply] at hp
      rw [pairH10_testH hc hmiw hψ] at hp
      have hμ : (Sob.cylinder c).μ = volume.restrict (Cyl.cell c) := Cyl.cylinder_μ_eq c
      rw [hμ]
      simpa only [smul_eq_mul, mul_comm (ψ _)] using hp
    rwa [Cyl.cylinder_μ_eq c] at hae_cyl
  have hae0 := hae_comp g0 hg0 hg0w hD1
  have hae1 := hae_comp g1 hg1 hg1w hD2
  apply Lp.ext
  filter_upwards [hae0, hae1, Lp.coeFn_zero Cyl.Vec2 2 (Cyl.cellμ c)] with z hz0 hz1 hzZ
  rw [hzZ]
  ext i
  fin_cases i
  · exact hz0
  · exact hz1

/-! ## 3. `IsCylSmoothHInf`, Word Indexing, and `0 < c` Cylinder Sobolev Sup Bounds -/

/-- Append a direction `d : Fin 2` at the end of `β : Fin m → Fin 2` without index casts. -/
def snocIdx : {m : ℕ} → (Fin m → Fin 2) → Fin 2 → Fin (m + 1) → Fin 2
  | 0, _, d => fun _ => d
  | _ + 1, β, d => Fin.cons (β 0) (snocIdx (Fin.tail β) d)

private lemma snocIdx_zero {n : ℕ} (β : Fin (n + 1) → Fin 2) (d : Fin 2) :
    snocIdx β d 0 = β 0 := rfl

private lemma tail_snocIdx {n : ℕ} (β : Fin (n + 1) → Fin 2) (d : Fin 2) :
    Fin.tail (snocIdx β d) = snocIdx (Fin.tail β) d := rfl

lemma slicePdIterR_slicePdR :
    ∀ {m : ℕ} (β : Fin m → Fin 2) (d : Fin 2) (f : B0579.Plane → F8Ex.RMerid),
      F8Ex.slicePdIterR β (F8Ex.slicePdR d f) = F8Ex.slicePdIterR (snocIdx β d) f
  | 0, _, _, _ => rfl
  | _ + 1, β, d, f => by
      change F8Ex.slicePdR (β 0) (F8Ex.slicePdIterR (Fin.tail β) (F8Ex.slicePdR d f)) =
        F8Ex.slicePdR (snocIdx β d 0) (F8Ex.slicePdIterR (Fin.tail (snocIdx β d)) f)
      rw [snocIdx_zero, tail_snocIdx, slicePdIterR_slicePdR (Fin.tail β) d f]

lemma exists_snocIdx :
    ∀ {n : ℕ} (α : Fin (n + 1) → Fin 2), ∃ (β : Fin n → Fin 2) (d : Fin 2), α = snocIdx β d
  | 0, α => ⟨Fin.elim0, α 0, funext fun i => by fin_cases i; rfl⟩
  | n + 1, α => by
      obtain ⟨β', d, hβ'⟩ := exists_snocIdx (Fin.tail α)
      refine ⟨Fin.cons (α 0) β', d, ?_⟩
      change α = Fin.cons (α 0) (snocIdx β' d)
      rw [← hβ', Fin.cons_self_tail]

/-- Concatenation of spatial derivative multi-indices `α` (outer) and `β` (inner), typed on
`Fin (n + m)` so that `n + 0 = n` and `n + (m + 1) = (n + m) + 1` hold definitionally. -/
def appendIdx : {m n : ℕ} → (Fin m → Fin 2) → (Fin n → Fin 2) → Fin (n + m) → Fin 2
  | 0, _, _, β => β
  | _ + 1, _, α, β => Fin.cons (α 0) (appendIdx (Fin.tail α) β)

lemma slicePdIterR_slicePdIterR :
    ∀ {m n : ℕ} (α : Fin m → Fin 2) (β : Fin n → Fin 2) (f : B0579.Plane → F8Ex.RMerid),
      F8Ex.slicePdIterR α (F8Ex.slicePdIterR β f) = F8Ex.slicePdIterR (appendIdx α β) f
  | 0, _, _, _, _ => rfl
  | _ + 1, _, α, β, f => by
      simp only [F8Ex.slicePdIterR, appendIdx, Fin.cons_zero, Fin.tail_cons]
      rw [slicePdIterR_slicePdIterR (Fin.tail α) β f]

lemma cyl_dir_eq_b0579 (c : ℝ) (i : Fin 2) : (Sob.cylinder c).dir i = B0579.dir i := by
  fin_cases i <;> rfl

lemma iterD_ofFn_eq_slicePdIterR (c : ℝ) :
    ∀ {n : ℕ} (β : Fin n → Fin 2) (f : B0579.Plane → F8Ex.RMerid),
      Sob.iterD (List.ofFn fun i => (Sob.cylinder c).dir (β i)) f = F8Ex.slicePdIterR β f
  | 0, _, _ => rfl
  | _ + 1, β, f => by
      rw [List.ofFn_succ, Sob.iterD_cons]
      have ih := iterD_ofFn_eq_slicePdIterR c (Fin.tail β) f
      have hfn : (fun i => (Sob.cylinder c).dir (β i.succ)) =
          fun i => (Sob.cylinder c).dir (Fin.tail β i) := rfl
      change (fun x => fderiv ℝ _ x ((Sob.cylinder c).dir (β 0))) =
        F8Ex.slicePdR (β 0) (F8Ex.slicePdIterR (Fin.tail β) f)
      rw [hfn, ih, cyl_dir_eq_b0579]
      rfl

lemma iterD_word_eq_slicePdIterR (c : ℝ) {m : ℕ} (α : Sob.Idx 2 m)
    (f : B0579.Plane → F8Ex.RMerid) :
    Sob.iterD ((Sob.cylinder c).word α) f = F8Ex.slicePdIterR α.2 f :=
  iterD_ofFn_eq_slicePdIterR c α.2 f

lemma contDiff_slicePdR {f : B0579.Plane → F8Ex.RMerid} (hf : ContDiff ℝ ∞ f) (d : Fin 2) :
    ContDiff ℝ ∞ (F8Ex.slicePdR d f) :=
  (ContDiff.fderiv_right (m := ∞) hf (by simp)).clm_apply contDiff_const

lemma contDiff_slicePdIterR {f : B0579.Plane → F8Ex.RMerid} (hf : ContDiff ℝ ∞ f) :
    ∀ {n : ℕ} (α : Fin n → Fin 2), ContDiff ℝ ∞ (F8Ex.slicePdIterR α f)
  | 0, _ => hf
  | _ + 1, α => contDiff_slicePdR (contDiff_slicePdIterR hf (Fin.tail α)) (α 0)

lemma periodic_slicePdR {c : ℝ} {f : B0579.Plane → F8Ex.RMerid}
    (hf : Cyl.IsPeriodic c f) (d : Fin 2) :
    Cyl.IsPeriodic c (F8Ex.slicePdR d f) := by
  intro z
  have hshift : (fun y : B0579.Plane => f (y + (c, 0))) = f := by
    funext y
    have hy : y + ((c, 0) : B0579.Plane) = (y.1 + c, y.2) := by ext <;> simp
    rw [hy]
    exact hf y
  have h := fderiv_comp_add_right (𝕜 := ℝ) (f := f) (x := z) ((c, 0) : B0579.Plane)
  rw [hshift] at h
  have hz : z + ((c, 0) : B0579.Plane) = (z.1 + c, z.2) := by ext <;> simp
  show fderiv ℝ f (z.1 + c, z.2) (B0579.dir d) = fderiv ℝ f z (B0579.dir d)
  rw [← hz, ← h]

lemma periodic_slicePdIterR {c : ℝ} {f : B0579.Plane → F8Ex.RMerid}
    (hf : Cyl.IsPeriodic c f) :
    ∀ {n : ℕ} (α : Fin n → Fin 2), Cyl.IsPeriodic c (F8Ex.slicePdIterR α f)
  | 0, _ => hf
  | _ + 1, α => periodic_slicePdR (periodic_slicePdIterR hf (Fin.tail α)) (α 0)

lemma slicePdR_zero (d : Fin 2) :
    F8Ex.slicePdR d (0 : B0579.Plane → F8Ex.RMerid) = 0 := by
  funext y
  simp [F8Ex.slicePdR]

lemma slicePdIterR_zero :
    ∀ {n : ℕ} (α : Fin n → Fin 2),
      F8Ex.slicePdIterR α (0 : B0579.Plane → F8Ex.RMerid) = 0
  | 0, _ => rfl
  | _ + 1, α => by
      simp only [F8Ex.slicePdIterR]
      rw [slicePdIterR_zero (Fin.tail α), slicePdR_zero]

lemma slicePdR_add {f g : B0579.Plane → F8Ex.RMerid}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (d : Fin 2) :
    F8Ex.slicePdR d (f + g) = F8Ex.slicePdR d f + F8Ex.slicePdR d g := by
  funext y
  change fderiv ℝ (f + g) y (B0579.dir d) = _
  rw [fderiv_add (hf.differentiable (by simp) y) (hg.differentiable (by simp) y)]
  rfl

lemma slicePdIterR_add {f g : B0579.Plane → F8Ex.RMerid}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ∀ {n : ℕ} (α : Fin n → Fin 2),
      F8Ex.slicePdIterR α (f + g) = F8Ex.slicePdIterR α f + F8Ex.slicePdIterR α g
  | 0, _ => rfl
  | _ + 1, α => by
      simp only [F8Ex.slicePdIterR]
      rw [slicePdIterR_add hf hg (Fin.tail α),
        slicePdR_add (contDiff_slicePdIterR hf (Fin.tail α))
          (contDiff_slicePdIterR hg (Fin.tail α))]

lemma slicePdR_smul (r : ℝ) {f : B0579.Plane → F8Ex.RMerid}
    (hf : ContDiff ℝ ∞ f) (d : Fin 2) :
    F8Ex.slicePdR d (r • f) = r • F8Ex.slicePdR d f := by
  funext y
  change fderiv ℝ (r • f) y (B0579.dir d) = _
  rw [fderiv_const_smul (hf.differentiable (by simp) y)]
  rfl

lemma slicePdIterR_smul (r : ℝ) {f : B0579.Plane → F8Ex.RMerid}
    (hf : ContDiff ℝ ∞ f) :
    ∀ {n : ℕ} (α : Fin n → Fin 2),
      F8Ex.slicePdIterR α (r • f) = r • F8Ex.slicePdIterR α f
  | 0, _ => rfl
  | _ + 1, α => by
      simp only [F8Ex.slicePdIterR]
      rw [slicePdIterR_smul r hf (Fin.tail α),
        slicePdR_smul r (contDiff_slicePdIterR hf (Fin.tail α))]

lemma slicePdIterR_sub {f g : B0579.Plane → F8Ex.RMerid}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) {n : ℕ} (α : Fin n → Fin 2) :
    F8Ex.slicePdIterR α (f - g) = F8Ex.slicePdIterR α f - F8Ex.slicePdIterR α g := by
  have hsub : f - g = f + (-1 : ℝ) • g := by
    funext y
    simp [sub_eq_add_neg]
  have hng : ContDiff ℝ ∞ ((-1 : ℝ) • g) := contDiff_const.smul hg
  rw [hsub, slicePdIterR_add hf hng α, slicePdIterR_smul (-1) hg α]
  funext y
  simp [sub_eq_add_neg]

/-- Smooth `c`-periodic meridional slice whose spatial derivatives of all orders lie in `L²(cell)`. -/
structure IsCylSmoothHInf (c : ℝ) (f : B0579.Plane → F8Ex.RMerid) : Prop where
  smooth : ContDiff ℝ ∞ f
  periodic : Cyl.IsPeriodic c f
  memL2 : ∀ (n : ℕ) (α : Fin n → Fin 2), MemLp (F8Ex.slicePdIterR α f) 2 (F8Ex.cellMeas c)

namespace IsCylSmoothHInf

lemma zero (c : ℝ) : IsCylSmoothHInf c 0 where
  smooth := contDiff_const
  periodic _ := rfl
  memL2 _ α := by
    rw [slicePdIterR_zero]
    exact MemLp.zero

lemma add {c : ℝ} {f g : B0579.Plane → F8Ex.RMerid}
    (hf : IsCylSmoothHInf c f) (hg : IsCylSmoothHInf c g) :
    IsCylSmoothHInf c (f + g) where
  smooth := hf.smooth.add hg.smooth
  periodic z := by simp [hf.periodic z, hg.periodic z]
  memL2 n α := by
    rw [slicePdIterR_add hf.smooth hg.smooth α]
    exact (hf.memL2 n α).add (hg.memL2 n α)

lemma smul {c : ℝ} (r : ℝ) {f : B0579.Plane → F8Ex.RMerid}
    (hf : IsCylSmoothHInf c f) :
    IsCylSmoothHInf c (r • f) where
  smooth := contDiff_const.smul hf.smooth
  periodic z := by simp [hf.periodic z]
  memL2 n α := by
    rw [slicePdIterR_smul r hf.smooth α]
    exact (hf.memL2 n α).const_smul r

lemma sub {c : ℝ} {f g : B0579.Plane → F8Ex.RMerid}
    (hf : IsCylSmoothHInf c f) (hg : IsCylSmoothHInf c g) :
    IsCylSmoothHInf c (f - g) := by
  have h : f - g = f + (-1 : ℝ) • g := by
    funext y
    simp [sub_eq_add_neg]
  rw [h]
  exact hf.add (hg.smul (-1))

lemma slicePdR {c : ℝ} {f : B0579.Plane → F8Ex.RMerid}
    (hf : IsCylSmoothHInf c f) (d : Fin 2) :
    IsCylSmoothHInf c (F8Ex.slicePdR d f) where
  smooth := contDiff_slicePdR hf.smooth d
  periodic := periodic_slicePdR hf.periodic d
  memL2 n α := by
    rw [slicePdIterR_slicePdR]
    exact hf.memL2 (n + 1) (snocIdx α d)

lemma slicePdIterR {c : ℝ} {f : B0579.Plane → F8Ex.RMerid}
    (hf : IsCylSmoothHInf c f) :
    ∀ {n : ℕ} (β : Fin n → Fin 2), IsCylSmoothHInf c (F8Ex.slicePdIterR β f)
  | 0, _ => hf
  | _ + 1, β => (hf.slicePdIterR (Fin.tail β)).slicePdR (β 0)

end IsCylSmoothHInf

private lemma derivWord_append (v w : List Bool) (h : B0579.Plane → ℝ) :
    B0151.derivWord (v ++ w) h = B0151.derivWord v (B0151.derivWord w h) := by
  induction v with
  | nil => rfl
  | cons b v ih =>
      cases b <;> simp [B0151.derivWord, ih]

private lemma length_mem_wordsOfLength {l : ℕ} {v : List Bool}
    (hv : v ∈ PartI.wordsOfLength l) : v.length = l := by
  obtain ⟨r, -, rfl⟩ := Finset.mem_image.mp hv
  simp

private lemma card_wordsOfLength_le_four {l : ℕ} (hl : l ≤ 2) :
    (PartI.wordsOfLength l).card ≤ 4 := by
  have h1 : (PartI.wordsOfLength l).card ≤ (Finset.univ : Finset (Fin l → Bool)).card :=
    Finset.card_image_le
  have h2 : (Finset.univ : Finset (Fin l → Bool)).card = 2 ^ l := by
    simp
  have h3 : 2 ^ l ≤ 4 := by
    interval_cases l <;> norm_num
  omega

/-- Period-positive (`0 < c`) real sup bound on the cylinder cell from `PartI.cylAgmonL2_proof`
without assuming `1 ≤ c`. -/
lemma sup_word_real_pos {c : ℝ} (hc : 0 < c) {h : B0579.Plane → ℝ}
    (hh : ContDiff ℝ ∞ h) (hp : B0151.IsPeriodicQ c h) {m : ℕ} {N : ℝ} (hN : 0 ≤ N)
    (hM : ∀ u : List Bool, u.length ≤ m + 2 →
      eLpNorm (B0151.derivWord u h) 2 (Cyl.cellμ c) ≤ ENNReal.ofReal N)
    (w : List Bool) (hw : w.length ≤ m) (z : B0579.Plane) :
    |B0151.derivWord w h z| ≤ (32 * c⁻¹ + 64) * N := by
  set g : B0579.Plane → ℝ := B0151.derivWord w h
  have hg_sm : ContDiff ℝ ∞ g := B0151.contDiff_derivWord hh w
  have hg_per : Cyl.IsPeriodic c g := fun y => B0151.periodic_derivWord hp w y.1 y.2
  have hg_word : ∀ v : List Bool, v.length ≤ 2 →
      eLpNorm (B0151.derivWord v g) 2 (Cyl.cellμ c) ≤ ENNReal.ofReal N := by
    intro v hv
    rw [← derivWord_append v w h]
    exact hM (v ++ w) (by simp only [List.length_append]; omega)
  have hg_mem_word : ∀ v : List Bool, v.length ≤ 2 →
      MemLp (fun y => |B0151.derivWord v g y|) 2 (Cyl.cellμ c) := by
    intro v hv
    have hcont : Continuous (B0151.derivWord v g) :=
      (B0151.contDiff_derivWord hg_sm v).continuous
    have hm : MemLp (B0151.derivWord v g) 2 (Cyl.cellμ c) :=
      ⟨hcont.aestronglyMeasurable,
        lt_of_le_of_lt (hg_word v hv) ENNReal.ofReal_lt_top⟩
    simpa only [Real.norm_eq_abs] using hm.norm
  have hjet : ∀ l : ℕ, l ≤ 2 →
      MemLp (Train.jet l g) 2 (Cyl.cellμ c) ∧
        Train.cellL2 c (Train.jet l g) ≤ ENNReal.ofReal (4 * N) := by
    intro l hl
    let sumW : B0579.Plane → ℝ := ∑ v ∈ PartI.wordsOfLength l, fun y => |B0151.derivWord v g y|
    have hsum_mem : MemLp sumW 2 (Cyl.cellμ c) :=
      (memLp_finsetSum (PartI.wordsOfLength l) fun v hv =>
        hg_mem_word v (by rw [length_mem_wordsOfLength hv]; exact hl)).ae_eq
        (ae_of_all _ fun y =>
          (Finset.sum_apply y (PartI.wordsOfLength l) (fun v z => |B0151.derivWord v g z|)).symm)
    have hjet_cont : Continuous (Train.jet l g) :=
      hg_sm.continuous_iteratedFDeriv (by simp)
    have hpt_norm : ∀ y : B0579.Plane, ‖Train.jet l g y‖ ≤ ‖sumW y‖ := fun y => by
      rw [Real.norm_eq_abs]
      dsimp only [sumW]
      rw [Finset.sum_apply, abs_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)]
      exact PartI.cjw_norm_le_sum g hg_sm l y
    have hmem_jet : MemLp (Train.jet l g) 2 (Cyl.cellμ c) :=
      hsum_mem.of_le hjet_cont.aestronglyMeasurable (ae_of_all _ hpt_norm)
    have hnorm_sum : eLpNorm sumW 2 (Cyl.cellμ c) ≤
        ∑ v ∈ PartI.wordsOfLength l,
          eLpNorm (fun y => |B0151.derivWord v g y|) 2 (Cyl.cellμ c) :=
      eLpNorm_sum_le (f := fun v y => |B0151.derivWord v g y|)
        (fun v hv => (hg_mem_word v (by rw [length_mem_wordsOfLength hv]; exact hl)).1)
        (by norm_num)
    have hcard : (PartI.wordsOfLength l).card ≤ 4 := card_wordsOfLength_le_four hl
    have hle4 : Train.cellL2 c (Train.jet l g) ≤ ENNReal.ofReal (4 * N) := by
      calc Train.cellL2 c (Train.jet l g)
          ≤ eLpNorm sumW 2 (Cyl.cellμ c) := eLpNorm_mono hpt_norm
        _ ≤ ∑ v ∈ PartI.wordsOfLength l,
              eLpNorm (fun y => |B0151.derivWord v g y|) 2 (Cyl.cellμ c) := hnorm_sum
        _ ≤ ∑ _v ∈ PartI.wordsOfLength l, ENNReal.ofReal N := by
            refine Finset.sum_le_sum fun v hv => ?_
            have hvn : eLpNorm (fun y => |B0151.derivWord v g y|) 2 (Cyl.cellμ c) =
                eLpNorm (B0151.derivWord v g) 2 (Cyl.cellμ c) := by
              simpa only [Real.norm_eq_abs] using
                (eLpNorm_norm (B0151.derivWord v g) (p := 2) (μ := Cyl.cellμ c))
            rw [hvn]
            exact hg_word v (by rw [length_mem_wordsOfLength hv]; exact hl)
        _ = (PartI.wordsOfLength l).card • ENNReal.ofReal N := Finset.sum_const _
        _ ≤ (4 : ℕ) • ENNReal.ofReal N := nsmul_le_nsmul_left zero_le hcard
        _ = ENNReal.ofReal (4 * N) := by
            rw [nsmul_eq_mul, Nat.cast_ofNat,
              ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4), ENNReal.ofReal_ofNat]
    exact ⟨hmem_jet, hle4⟩
  have hmem0 : MemLp g 2 (Cyl.cellμ c) :=
    ⟨hg_sm.continuous.aestronglyMeasurable,
      lt_of_le_of_lt (hg_word [] (by simp)) ENNReal.ofReal_lt_top⟩
  have hle0 : Train.cellL2 c g ≤ ENNReal.ofReal (4 * N) := by
    refine (hg_word [] (by simp)).trans ?_
    exact ENNReal.ofReal_le_ofReal (by linarith)
  obtain ⟨hmem1, hle1⟩ := hjet 1 (by omega)
  obtain ⟨hmem2, hle2⟩ := hjet 2 (by omega)
  have hag := PartI.cylAgmonL2_proof c hc g hg_sm hg_per hmem0 hmem1 hmem2 z
  set E := ENNReal.ofReal (4 * N)
  have hstep1 : ‖g z‖ₑ ^ 2 ≤ 2 * (ENNReal.ofReal c⁻¹ * (E * E) + E ^ 2 + E * E) :=
    hag.trans (mul_le_mul_of_nonneg_left
      (add_le_add
        (add_le_add
          (mul_le_mul_of_nonneg_left (mul_le_mul' hle0 hle1) zero_le)
          (pow_le_pow_left' hle1 2))
        (mul_le_mul' hle0 hle2))
      zero_le)
  set K : ℝ := 32 * c⁻¹ + 64
  have hc_inv : 0 ≤ c⁻¹ := inv_nonneg.2 hc.le
  have hK_ge : 64 ≤ K := by dsimp [K]; linarith
  have hK0 : 0 ≤ K := by linarith
  have h4N : 0 ≤ 4 * N := by linarith
  have hE_eq : 2 * (ENNReal.ofReal c⁻¹ * (E * E) + E ^ 2 + E * E) =
      ENNReal.ofReal (K * N ^ 2) := by
    dsimp [E, K]
    rw [sq (ENNReal.ofReal (4 * N)), ← ENNReal.ofReal_mul h4N,
      ← ENNReal.ofReal_mul hc_inv,
      ← ENNReal.ofReal_add (mul_nonneg hc_inv (mul_nonneg h4N h4N)) (mul_nonneg h4N h4N),
      ← ENNReal.ofReal_add
        (add_nonneg (mul_nonneg hc_inv (mul_nonneg h4N h4N)) (mul_nonneg h4N h4N))
        (mul_nonneg h4N h4N),
      ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have hKN_sq : K * N ^ 2 ≤ (K * N) ^ 2 := by
    nlinarith [sq_nonneg N, mul_nonneg hc_inv (sq_nonneg N)]
  have hgz_sq : ENNReal.ofReal (|g z| ^ 2) ≤ ENNReal.ofReal ((K * N) ^ 2) := by
    have hlhs : ENNReal.ofReal (|g z| ^ 2) = ‖g z‖ₑ ^ 2 := by
      rw [Real.enorm_eq_ofReal_abs, sq, sq, ENNReal.ofReal_mul (abs_nonneg _)]
    rw [hlhs]
    exact (hstep1.trans_eq hE_eq).trans (ENNReal.ofReal_le_ofReal hKN_sq)
  have hreal_sq : |g z| ^ 2 ≤ (K * N) ^ 2 :=
    (ENNReal.ofReal_le_ofReal_iff (sq_nonneg (K * N))).mp hgz_sq
  exact (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hK0 hN)).mp hreal_sq

/-- Period-positive (`0 < c`) cylinder Sobolev embedding bound for `Sob.IsCylSmooth c` fields,
matching the hypothesis required by `PartI.csr_exists_rep c hc k`. -/
lemma cylSmoothSobolevBound_pos {c : ℝ} (hc : 0 < c) (k : ℕ) :
    ∀ (f : Cyl.Plane → Train.Vec) (hf : Sob.IsCylSmooth c f), ∀ j : ℕ, j ≤ k + 1 → ∀ z : Cyl.Plane,
      ‖iteratedFDeriv ℝ j f z‖ ≤
        (2 * (32 * c⁻¹ + 64) * 2 ^ (k + 1)) * ‖PartI.csrOf c hc k f hf‖ := by
  intro f hf j hj z
  have hsmooth : ContDiff ℝ ∞ f := hf.smooth
  have hci : ∀ i : Fin 2, ContDiff ℝ ∞ (fun y => f y i) := fun i =>
    (EuclideanSpace.proj i : Cyl.Vec2 →L[ℝ] ℝ).contDiff.comp hsmooth
  have hper : ∀ i : Fin 2, B0151.IsPeriodicQ c (fun y => f y i) := by
    intro i q η
    show f (q + c, η) i = f (q, η) i
    have e : ((q + c, η) : ℝ × ℝ) = (q, η) + (c, 0) := by ext <;> simp
    rw [e, hf.periodic]
  set N := ‖PartI.csrOf c hc k f hf‖
  have hN0 : 0 ≤ N := norm_nonneg _
  set K := 32 * c⁻¹ + 64
  have hK0 : 0 ≤ K := by
    have : 0 ≤ c⁻¹ := inv_nonneg.2 hc.le
    dsimp [K]
    linarith
  have hword : ∀ i : Fin 2, ∀ w : List Bool, w.length ≤ k + 1 → ∀ y : ℝ × ℝ,
      |B0151.derivWord w (fun y' => f y' i) y| ≤ K * N := fun i w hw y =>
    sup_word_real_pos hc (hci i) (hper i) hN0
      (fun u hu => PartI.csb_comp_bound hc k hf i u (by omega)) w hw y
  have hiter : ∀ i : Fin 2, ‖iteratedFDeriv ℝ j (fun y => f y i) z‖ ≤ 2 ^ j * (K * N) :=
    fun i => Short.Spine.norm_iteratedFDeriv_le_of_derivWord (hci i) j z
      (fun w hw => hword i w (by omega) z)
  have heuc := Short.Spine.norm_iteratedFDeriv_euclid2_le hsmooth j z
  have hpow : (2 : ℝ) ^ j ≤ 2 ^ (k + 1) := pow_le_pow_right₀ (by norm_num) hj
  calc ‖iteratedFDeriv ℝ j f z‖
      ≤ ‖iteratedFDeriv ℝ j (fun y => f y 0) z‖ + ‖iteratedFDeriv ℝ j (fun y => f y 1) z‖ := heuc
    _ ≤ 2 ^ j * (K * N) + 2 ^ j * (K * N) := add_le_add (hiter 0) (hiter 1)
    _ = 2 * K * 2 ^ j * N := by ring
    _ ≤ (2 * K * 2 ^ (k + 1)) * N :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow (mul_nonneg (by norm_num) hK0)) hN0

/-- Pointwise `L^∞` bound on any `IsCylSmoothHInf c` field (`0 < c`) in terms of the finite sum of
its cell `L²` derivative norms of order `≤ 2`. -/
lemma norm_le_H2_of_isCylSmoothHInf {c : ℝ} (hc : 0 < c)
    {f : B0579.Plane → F8Ex.RMerid} (hf : IsCylSmoothHInf c f) (z : B0579.Plane) :
    ‖f z‖ ≤ (2 * (32 * c⁻¹ + 64)) *
      ∑ m : Fin 3, ∑ β : Fin m.1 → Fin 2, ‖toLpCell (hf.memL2 m.1 β)‖ := by
  set S : ℝ := ∑ m : Fin 3, ∑ β : Fin m.1 → Fin 2, ‖toLpCell (hf.memL2 m.1 β)‖
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hci : ∀ i : Fin 2, ContDiff ℝ ∞ (fun y => f y i) := fun i =>
    (EuclideanSpace.proj i : Cyl.Vec2 →L[ℝ] ℝ).contDiff.comp hf.smooth
  have hper : ∀ i : Fin 2, B0151.IsPeriodicQ c (fun y => f y i) :=
    fun i q η => congrArg (fun v : Cyl.Vec2 => v i) (hf.periodic (q, η))
  have hcomp_S : ∀ (i : Fin 2) (u : List Bool), u.length ≤ 2 →
      eLpNorm (B0151.derivWord u (fun y => f y i)) 2 (Cyl.cellμ c) ≤ ENNReal.ofReal S := by
    intro i u hu
    obtain ⟨α, hα⟩ := PartI.csb_exists_idx c 2 u hu
    rw [PartI.csb_derivWord_comp hf.smooth i u, ← hα, iterD_word_eq_slicePdIterR]
    have hcoord : eLpNorm (fun y => F8Ex.slicePdIterR α.2 f y i) 2 (Cyl.cellμ c) ≤
        eLpNorm (F8Ex.slicePdIterR α.2 f) 2 (Cyl.cellμ c) :=
      eLpNorm_mono_enorm fun y => PartI.csb_enorm_apply_le _ i
    have heq_norm : eLpNorm (F8Ex.slicePdIterR α.2 f) 2 (Cyl.cellμ c) =
        ENNReal.ofReal ‖toLpCell (hf.memL2 α.1.1 α.2)‖ := by
      rw [ofReal_norm_toLpCell, F8Ex.cellL2R, cellMeas_eq_cellμ]
    have hle_inner : ‖toLpCell (hf.memL2 α.1.1 α.2)‖ ≤
        ∑ β : Fin α.1.1 → Fin 2, ‖toLpCell (hf.memL2 α.1.1 β)‖ :=
      Finset.single_le_sum
        (f := fun β : Fin α.1.1 → Fin 2 => ‖toLpCell (hf.memL2 α.1.1 β)‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_univ α.2)
    have hle_outer : ∑ β : Fin α.1.1 → Fin 2, ‖toLpCell (hf.memL2 α.1.1 β)‖ ≤ S :=
      Finset.single_le_sum
        (f := fun m : Fin 3 => ∑ β : Fin m.1 → Fin 2, ‖toLpCell (hf.memL2 m.1 β)‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ α.1)
    exact (hcoord.trans_eq heq_norm).trans (ENNReal.ofReal_le_ofReal (hle_inner.trans hle_outer))
  have hi : ∀ i : Fin 2, |f z i| ≤ (32 * c⁻¹ + 64) * S := fun i =>
    sup_word_real_pos hc (hci i) (hper i) hS0
      (fun u hu => hcomp_S i u (by omega)) [] (by simp) z
  have heuc0 := Short.Spine.norm_iteratedFDeriv_euclid2_le hf.smooth 0 z
  simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at heuc0
  calc ‖f z‖ ≤ |f z 0| + |f z 1| := heuc0
    _ ≤ (32 * c⁻¹ + 64) * S + (32 * c⁻¹ + 64) * S := add_le_add (hi 0) (hi 1)
    _ = (2 * (32 * c⁻¹ + 64)) * S := by ring

/-! ## 4. Embedding `IsCylSmoothHInf` into `Cyl.H ℝ Cyl.Vec2 c 0 m` -/

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

private lemma hasWeakDeriv_dir_of_smooth_periodic {c : ℝ} (hc : 0 < c)
    {u : B0579.Plane → F8Ex.RMerid} (hu_sm : ContDiff ℝ ∞ u) (hu_per : Cyl.IsPeriodic c u)
    (v : B0579.Plane) :
    Sob.HasWeakDeriv (Sob.cylinder c) [v] u (fun z => fderiv ℝ u z v) := by
  have hdu_sm : ContDiff ℝ ∞ (fun z => fderiv ℝ u z v) :=
    (ContDiff.fderiv_right (m := ∞) hu_sm (by simp)).clm_apply contDiff_const
  have hdu_per : Cyl.IsPeriodic c (fun z => fderiv ℝ u z v) := by
    intro z
    have hshift : (fun y : B0579.Plane => u (y + (c, 0))) = u := by
      funext y
      have hy : y + ((c, 0) : B0579.Plane) = (y.1 + c, y.2) := by ext <;> simp
      rw [hy]
      exact hu_per y
    have h := fderiv_comp_add_right (𝕜 := ℝ) (f := u) (x := z) ((c, 0) : B0579.Plane)
    rw [hshift] at h
    have hz : z + ((c, 0) : B0579.Plane) = (z.1 + c, z.2) := by ext <;> simp
    show fderiv ℝ u (z.1 + c, z.2) v = fderiv ℝ u z v
    rw [← hz, ← h]
  refine ⟨fun φ hφ => (isCylSmooth_smul_test hu_sm hu_per ((Sob.cylinder c).deriv_mem hφ v)).integrableOn,
    fun φ hφ => (isCylSmooth_smul_test hdu_sm hdu_per hφ).integrableOn, fun φ hφ => ?_⟩
  have hφ' : Sob.IsCylTest c φ := hφ
  have hd : ∀ z, fderiv ℝ (fun y => φ y • u y) z v =
      fderiv ℝ φ z v • u z + φ z • fderiv ℝ u z v := by
    intro z
    have h1 : DifferentiableAt ℝ φ z := (hφ'.smooth.differentiable (by simp)) z
    have h2 : DifferentiableAt ℝ u z := (hu_sm.differentiable (by simp)) z
    show fderiv ℝ (φ • u) z v = _
    rw [fderiv_smul h1 h2]
    simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
    rw [add_comm]
  have h0 := Sob.integral_cylCell_fderiv_eq_zero hc (isCylSmooth_smul_test hu_sm hu_per hφ') v
  simp_rw [hd] at h0
  have i1 : IntegrableOn (fun z => fderiv ℝ φ z v • u z) (Sob.cylCell c) :=
    (isCylSmooth_smul_test hu_sm hu_per (hφ'.dirDeriv v)).integrableOn
  have i2 : IntegrableOn (fun z => φ z • fderiv ℝ u z v) (Sob.cylCell c) :=
    (isCylSmooth_smul_test hdu_sm hdu_per hφ').integrableOn
  rw [integral_add i1 i2, add_eq_zero_iff_eq_neg] at h0
  simp only [Sob.iterDirDeriv_singleton, Sob.cylinder_μ, List.length_singleton, pow_one, neg_smul,
    one_smul]
  exact h0

private lemma hasWeakDeriv_of_smooth_periodic {c : ℝ} (hc : 0 < c)
    {u : B0579.Plane → F8Ex.RMerid} (hu_sm : ContDiff ℝ ∞ u) (hu_per : Cyl.IsPeriodic c u) :
    ∀ vs : List B0579.Plane, Sob.HasWeakDeriv (Sob.cylinder c) vs u (Sob.iterD vs u)
  | [] => Sob.HasWeakDeriv.nil fun _ hφ => (isCylSmooth_smul_test hu_sm hu_per hφ).integrableOn
  | v :: vs => by
      have ih := hasWeakDeriv_of_smooth_periodic hc hu_sm hu_per vs
      have hvs_per : Cyl.IsPeriodic c (Sob.iterD vs u) := by
        clear ih
        induction vs with
        | nil => exact hu_per
        | cons w ws ihw =>
            intro z
            have hshift : (fun y : B0579.Plane => Sob.iterD ws u (y + (c, 0))) =
                Sob.iterD ws u := by
              funext y
              have hy : y + ((c, 0) : B0579.Plane) = (y.1 + c, y.2) := by ext <;> simp
              rw [hy]
              exact ihw y
            have h := fderiv_comp_add_right (𝕜 := ℝ) (f := Sob.iterD ws u) (x := z)
              ((c, 0) : B0579.Plane)
            rw [hshift] at h
            have hz : z + ((c, 0) : B0579.Plane) = (z.1 + c, z.2) := by ext <;> simp
            show fderiv ℝ (Sob.iterD ws u) (z.1 + c, z.2) w = fderiv ℝ (Sob.iterD ws u) z w
            rw [← hz, ← h]
      exact ih.cons (hasWeakDeriv_dir_of_smooth_periodic hc (Sob.contDiff_iterD hu_sm vs) hvs_per v)

private lemma weightedToCell_of_toLp {c : ℝ} (u : Cyl.L2v c)
    {F : B0579.Plane → Cyl.Vec2} (hF : MemLp F 2
      (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))))
    (hFae : (u : B0579.Plane → Cyl.Vec2) =ᵐ[Cyl.cellμ c] F) :
    TrainB.weightedToCellL2Isometry c (hF.toLp F) = u := by
  apply Lp.ext
  let hMP : MeasurePreserving id (Cyl.cellμ c)
      (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ))) := by
    rw [← TrainB.vecH1_measure_eq_cell c]
    exact MeasurePreserving.id _
  have hcomp := Lp.coeFn_compMeasurePreserving (hF.toLp F) hMP
  have hFcell := hMP.quasiMeasurePreserving.ae hF.coeFn_toLp
  filter_upwards [hcomp, hFcell, hFae] with z hzComp hzF hzU
  calc ((Lp.compMeasurePreserving id hMP (hF.toLp F) : Cyl.L2v c) : B0579.Plane → Cyl.Vec2) z
      = (hF.toLp F : Lp Cyl.Vec2 2
          (Sob.wμ (Sob.cylinder c).μ (Cyl.ρwW c ^ (0 : ℝ)))) z := by
          simpa [Function.comp_id] using hzComp
    _ = F z := hzF
    _ = (u : B0579.Plane → Cyl.Vec2) z := hzU.symm

/-- Centered-cell `L²` realization of the `α`-th weak derivative on `Cyl.H ℝ Cyl.Vec2 c 0 m`. -/
def derivCellCLM (c : ℝ) {m : ℕ} (α : Sob.Idx 2 m) :
    Cyl.H ℝ Cyl.Vec2 c 0 m →L[ℝ] Cyl.L2v c :=
  (TrainB.weightedToCellL2Isometry c).toContinuousLinearMap.comp
    (Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Cyl.Vec2 m 2 α)

/-- Centered-cell `L²` realization of the order-`0` value on `Cyl.H ℝ Cyl.Vec2 c 0 m`. -/
def valueCellCLM (c : ℝ) (m : ℕ) :
    Cyl.H ℝ Cyl.Vec2 c 0 m →L[ℝ] Cyl.L2v c :=
  derivCellCLM c (Sob.Idx.zero : Sob.Idx 2 m)

lemma valueCellCLM_injective (c : ℝ) (m : ℕ) :
    Function.Injective (valueCellCLM c m) := by
  intro x y hxy
  have hval : Sob.W.value (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Cyl.Vec2 m 2 x =
      Sob.W.value (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Cyl.Vec2 m 2 y :=
    (TrainB.weightedToCellL2Isometry c).injective hxy
  exact Sob.W.value_injective hval

private lemma ofHInf_weak {c : ℝ} (hc : 0 < c) (m : ℕ) {f : B0579.Plane → F8Ex.RMerid}
    (hf : IsCylSmoothHInf c f) :
    ∀ α : Sob.Idx 2 m,
      Sob.HasWeakDeriv (F := Cyl.Vec2) (Sob.cylinder c) ((Sob.cylinder c).word α)
        (F8Ex.slicePdIterR (Sob.Idx.zero : Sob.Idx 2 m).2 f)
        (F8Ex.slicePdIterR α.2 f) := by
  intro α
  have hw := hasWeakDeriv_of_smooth_periodic hc hf.smooth hf.periodic ((Sob.cylinder c).word α)
  rw [iterD_word_eq_slicePdIterR] at hw
  exact hw

/-- Canonical element of `Cyl.H ℝ Cyl.Vec2 c 0 m` associated to `hf : IsCylSmoothHInf c f`. -/
def ofHInf {c : ℝ} (hc : 0 < c) (m : ℕ) {f : B0579.Plane → F8Ex.RMerid}
    (hf : IsCylSmoothHInf c f) : Cyl.H ℝ Cyl.Vec2 c 0 m :=
  Sob.W.ofFields
    (D := Sob.cylinder c) (ρ := Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := Cyl.Vec2)
    (k := m) (p := 2)
    (fun α => F8Ex.slicePdIterR α.2 f)
    (fun α => (TrainB.vecH1_measure_eq_cell c).symm ▸ memLp_to_cellμ (hf.memL2 α.1.1 α.2))
    (ofHInf_weak hc m hf)

lemma derivCellCLM_ofHInf {c : ℝ} (hc : 0 < c) {m : ℕ} (α : Sob.Idx 2 m)
    {f : B0579.Plane → F8Ex.RMerid} (hf : IsCylSmoothHInf c f) :
    derivCellCLM c α (ofHInf hc m hf) = toLpCell (hf.memL2 α.1.1 α.2) := by
  change TrainB.weightedToCellL2Isometry c
    (Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Cyl.Vec2 m 2 α (ofHInf hc m hf)) = _
  rw [ofHInf, Sob.W.deriv_ofFields]
  exact weightedToCell_of_toLp (toLpCell (hf.memL2 α.1.1 α.2)) _ (coeFn_toLpCell _)

lemma valueCellCLM_ofHInf {c : ℝ} (hc : 0 < c) (m : ℕ)
    {f : B0579.Plane → F8Ex.RMerid} (hf : IsCylSmoothHInf c f) :
    valueCellCLM c m (ofHInf hc m hf) = toLpCell (hf.memL2 0 Fin.elim0) :=
  derivCellCLM_ofHInf hc (Sob.Idx.zero : Sob.Idx 2 m) hf

/-! ## 5. Smooth Leray Projection `P0Smooth c` on `IsCylSmoothHInf c` -/

private lemma hasWeakDeriv_P0_ofHInf {c : ℝ} (hc : 0 < c)
    {f : B0579.Plane → F8Ex.RMerid} (hf : IsCylSmoothHInf c f) :
    ∀ {n : ℕ} (β : Fin n → Fin 2),
      Sob.HasWeakDeriv (Sob.cylinder c) (List.ofFn fun i => (Sob.cylinder c).dir (β i))
        (Cyl.P0 c (toLpCell (hf.memL2 0 Fin.elim0)) : B0579.Plane → Cyl.Vec2)
        (Cyl.P0 c (toLpCell (hf.memL2 n β)) : B0579.Plane → Cyl.Vec2)
  | 0, β => by
      have hsub : β = Fin.elim0 := Subsingleton.elim _ _
      subst hsub
      apply Sob.HasWeakDeriv.nil
      intro φ hφ
      exact Sob.integrable_smul_of_memLp (p := 2) (Sob.CompactlyBounded.of_adm hφ)
        (TrainB.memLp_cell_to_weighted (Cyl.P0 c (toLpCell (hf.memL2 0 Fin.elim0))))
  | n + 1, β => by
      rw [List.ofFn_succ]
      have ih := hasWeakDeriv_P0_ofHInf hc hf (Fin.tail β)
      let x : TrainB.VecH1 c := ofHInf hc 1 (hf.slicePdIterR (Fin.tail β))
      have hval : TrainB.vecH1ValueCellCLM_MP x = toLpCell (hf.memL2 n (Fin.tail β)) :=
        derivCellCLM_ofHInf hc (Sob.Idx.zero : Sob.Idx 2 1) (hf.slicePdIterR (Fin.tail β))
      have hstep : Sob.HasWeakDeriv (Sob.cylinder c) [(Sob.cylinder c).dir (β 0)]
          (Cyl.P0 c (toLpCell (hf.memL2 n (Fin.tail β))) : B0579.Plane → Cyl.Vec2)
          (Cyl.P0 c (toLpCell (hf.memL2 (n + 1) β)) : B0579.Plane → Cyl.Vec2) := by
        have hβ0 : β 0 = 0 ∨ β 0 = 1 := by
          have := (β 0).isLt
          rcases β 0 with ⟨v, hv⟩
          interval_cases v
          · exact Or.inl rfl
          · exact Or.inr rfl
        rcases hβ0 with h0 | h1
        · have hq : TrainB.vecH1DqCellCLM_MP x = toLpCell (hf.memL2 (n + 1) β) := by
            have hd := derivCellCLM_ofHInf hc (Sob.Idx.cons 0 Sob.Idx.zero : Sob.Idx 2 1)
              (hf.slicePdIterR (Fin.tail β))
            refine hd.trans (toLpCell_congr_ae _ _ (ae_of_all _ fun y => ?_))
            simp only [F8Ex.slicePdIterR, h0]
            rfl
          have hw := TrainB.hasWeakDeriv_P0_q_of_vecH1 hc x
          rw [hval, hq] at hw
          have hdir : (Sob.cylinder c).dir (β 0) = ((1 : ℝ), (0 : ℝ)) := by rw [h0]; rfl
          rw [hdir]
          exact hw
        · have he : TrainB.vecH1DetaCellCLM_MP x = toLpCell (hf.memL2 (n + 1) β) := by
            have hd := derivCellCLM_ofHInf hc (Sob.Idx.cons 1 Sob.Idx.zero : Sob.Idx 2 1)
              (hf.slicePdIterR (Fin.tail β))
            refine hd.trans (toLpCell_congr_ae _ _ (ae_of_all _ fun y => ?_))
            simp only [F8Ex.slicePdIterR, h1]
            rfl
          have hw := TrainB.hasWeakDeriv_P0_eta_of_vecH1 hc x
          rw [hval, he] at hw
          have hdir : (Sob.cylinder c).dir (β 0) = ((0 : ℝ), (1 : ℝ)) := by rw [h1]; rfl
          rw [hdir]
          exact hw
      exact ih.cons hstep

private lemma projHInf_weak {c : ℝ} (hc : 0 < c) (M : ℕ)
    {f : B0579.Plane → F8Ex.RMerid} (hf : IsCylSmoothHInf c f) :
    ∀ α : Sob.Idx 2 M,
      Sob.HasWeakDeriv (F := Cyl.Vec2) (Sob.cylinder c) ((Sob.cylinder c).word α)
        (Cyl.P0 c (toLpCell (hf.memL2 (Sob.Idx.zero : Sob.Idx 2 M).1.1
          (Sob.Idx.zero : Sob.Idx 2 M).2)) : B0579.Plane → Cyl.Vec2)
        (Cyl.P0 c (toLpCell (hf.memL2 α.1.1 α.2)) : B0579.Plane → Cyl.Vec2) :=
  fun α => hasWeakDeriv_P0_ofHInf hc hf α.2

private noncomputable def projHInf {c : ℝ} (hc : 0 < c) (M : ℕ)
    {f : B0579.Plane → F8Ex.RMerid} (hf : IsCylSmoothHInf c f) :
    Cyl.H ℝ Cyl.Vec2 c 0 M :=
  Sob.W.ofFields
    (D := Sob.cylinder c) (ρ := Cyl.ρwW c ^ (0 : ℝ)) (𝕜 := ℝ) (F := Cyl.Vec2)
    (k := M) (p := 2)
    (fun α => (Cyl.P0 c (toLpCell (hf.memL2 α.1.1 α.2)) : B0579.Plane → Cyl.Vec2))
    (fun α => TrainB.memLp_cell_to_weighted (Cyl.P0 c (toLpCell (hf.memL2 α.1.1 α.2))))
    (projHInf_weak hc M hf)

private lemma cellDeriv_projHInf_ae {c : ℝ} (hc : 0 < c) {M : ℕ} (α : Sob.Idx 2 M)
    {f : B0579.Plane → F8Ex.RMerid} (hf : IsCylSmoothHInf c f) :
    PartI.cellDeriv c α (projHInf hc M hf) =ᵐ[Cyl.cellμ c]
      (Cyl.P0 c (toLpCell (hf.memL2 α.1.1 α.2)) : B0579.Plane → Cyl.Vec2) := by
  have heq : TrainB.weightedToCellL2Isometry c
      (Sob.W.deriv (Sob.cylinder c) (Cyl.ρwW c ^ (0 : ℝ)) ℝ Cyl.Vec2 M 2 α (projHInf hc M hf)) =
      Cyl.P0 c (toLpCell (hf.memL2 α.1.1 α.2)) := by
    unfold projHInf
    rw [Sob.W.deriv_ofFields]
    exact weightedToCell_of_toLp _ _ (ae_of_all _ fun _ => rfl)
  unfold PartI.cellDeriv
  rw [heq]

private lemma exists_P0Smooth {c : ℝ} (hc : 0 < c)
    {f : B0579.Plane → F8Ex.RMerid} (hf : IsCylSmoothHInf c f) :
    ∃ G : B0579.Plane → F8Ex.RMerid,
      IsCylSmoothHInf c G ∧
      ∀ {n : ℕ} (β : Fin n → Fin 2),
        F8Ex.slicePdIterR β G =ᵐ[Cyl.cellμ c]
          (Cyl.P0 c (toLpCell (hf.memL2 n β)) : B0579.Plane → Cyl.Vec2) := by
  have hrep : ∀ k : ℕ, ∃ G : B0579.Plane → F8Ex.RMerid,
      ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) G ∧ Cyl.IsPeriodic c G ∧
      ∀ β : Sob.Idx 2 (k + 1),
        PartI.cellDeriv c (Sob.Idx.castLE (by omega : k + 1 ≤ k + 3) β)
          (projHInf hc (k + 3) hf) =ᵐ[Cyl.cellμ c]
            Sob.iterD ((Sob.cylinder c).word β) G := by
    intro k
    obtain ⟨G, hGc, hGper, hGae, _⟩ :=
      PartI.csr_exists_rep c hc k (2 * (32 * c⁻¹ + 64) * 2 ^ (k + 1))
        (cylSmoothSobolevBound_pos hc k) (projHInf hc (k + 3) hf)
    exact ⟨G, hGc, hGper, hGae⟩
  choose G hG using hrep
  have hG_eq : ∀ k : ℕ, G k = G 0 := by
    intro k
    have haek : G k =ᵐ[Cyl.cellμ c]
        (Cyl.P0 c (toLpCell (hf.memL2 0 Fin.elim0)) : B0579.Plane → Cyl.Vec2) := by
      have hk0 := (hG k).2.2 Sob.Idx.zero
      simp only [Sob.Idx.castLE_zero, Sob.TestDomain.word_zero, Sob.iterD_nil] at hk0
      exact hk0.symm.trans (cellDeriv_projHInf_ae hc (Sob.Idx.zero : Sob.Idx 2 (k + 3)) hf)
    have hae0 : G 0 =ᵐ[Cyl.cellμ c]
        (Cyl.P0 c (toLpCell (hf.memL2 0 Fin.elim0)) : B0579.Plane → Cyl.Vec2) := by
      have h00 := (hG 0).2.2 Sob.Idx.zero
      simp only [Sob.Idx.castLE_zero, Sob.TestDomain.word_zero, Sob.iterD_nil] at h00
      exact h00.symm.trans (cellDeriv_projHInf_ae hc (Sob.Idx.zero : Sob.Idx 2 3) hf)
    exact PartI.aePeriodicEq c hc (G k) (G 0) (hG k).1.continuous (hG 0).1.continuous
      (hG k).2.1 (hG 0).2.1 (haek.trans hae0.symm)
  have hG0_sm : ContDiff ℝ ∞ (G 0) :=
    contDiff_infty.mpr fun n => by
      rw [← hG_eq n]
      exact (hG n).1.of_le (by exact_mod_cast Nat.le_succ n)
  have hG0_ae : ∀ {n : ℕ} (β : Fin n → Fin 2),
      F8Ex.slicePdIterR β (G 0) =ᵐ[Cyl.cellμ c]
        (Cyl.P0 c (toLpCell (hf.memL2 n β)) : B0579.Plane → Cyl.Vec2) := by
    intro n β
    let idx : Sob.Idx 2 (n + 1) := ⟨⟨n, by omega⟩, β⟩
    have hn := (hG n).2.2 idx
    rw [iterD_word_eq_slicePdIterR, hG_eq n] at hn
    exact hn.symm.trans
      (cellDeriv_projHInf_ae hc (Sob.Idx.castLE (by omega : n + 1 ≤ n + 3) idx) hf)
  have hG0_hinf : IsCylSmoothHInf c (G 0) :=
    ⟨hG0_sm, (hG 0).2.1, fun n β =>
      memLp_of_cellμ ((Lp.memLp (Cyl.P0 c (toLpCell (hf.memL2 n β)))).ae_eq (hG0_ae β).symm)⟩
  exact ⟨G 0, hG0_hinf, hG0_ae⟩

/-- Smooth `c`-periodic representative of `Cyl.P0 c` on `IsCylSmoothHInf c` slices (`0 < c`). -/
def P0Smooth (c : ℝ) (f : B0579.Plane → F8Ex.RMerid) : B0579.Plane → F8Ex.RMerid :=
  open Classical in
  if h : 0 < c ∧ IsCylSmoothHInf c f then
    Classical.choose (exists_P0Smooth h.1 h.2)
  else
    0

lemma P0Smooth_isCylSmoothHInf {c : ℝ} (hc : 0 < c)
    {f : B0579.Plane → F8Ex.RMerid} (hf : IsCylSmoothHInf c f) :
    IsCylSmoothHInf c (P0Smooth c f) := by
  have h : 0 < c ∧ IsCylSmoothHInf c f := ⟨hc, hf⟩
  have hd : P0Smooth c f = Classical.choose (exists_P0Smooth h.1 h.2) := dite_eq_left h
  rw [hd]
  exact (Classical.choose_spec (exists_P0Smooth h.1 h.2)).1

lemma slicePdIterR_P0Smooth_ae {c : ℝ} (hc : 0 < c)
    {f : B0579.Plane → F8Ex.RMerid} (hf : IsCylSmoothHInf c f)
    {n : ℕ} (β : Fin n → Fin 2) :
    F8Ex.slicePdIterR β (P0Smooth c f) =ᵐ[Cyl.cellμ c]
      (Cyl.P0 c (toLpCell (hf.memL2 n β)) : B0579.Plane → Cyl.Vec2) := by
  have h : 0 < c ∧ IsCylSmoothHInf c f := ⟨hc, hf⟩
  have hd : P0Smooth c f = Classical.choose (exists_P0Smooth h.1 h.2) := dite_eq_left h
  rw [hd]
  exact (Classical.choose_spec (exists_P0Smooth h.1 h.2)).2 β

lemma toLpCell_slicePdIterR_P0Smooth {c : ℝ} (hc : 0 < c)
    {f : B0579.Plane → F8Ex.RMerid} (hf : IsCylSmoothHInf c f)
    {n : ℕ} (β : Fin n → Fin 2) :
    toLpCell ((P0Smooth_isCylSmoothHInf hc hf).memL2 n β) =
      Cyl.P0 c (toLpCell (hf.memL2 n β)) := by
  apply Lp.ext
  exact (coeFn_toLpCell _).trans (slicePdIterR_P0Smooth_ae hc hf β)

lemma toLpCell_P0Smooth {c : ℝ} (hc : 0 < c)
    {f : B0579.Plane → F8Ex.RMerid} (hf : IsCylSmoothHInf c f) :
    toLpCell ((P0Smooth_isCylSmoothHInf hc hf).memL2 0 Fin.elim0) =
      Cyl.P0 c (toLpCell (hf.memL2 0 Fin.elim0)) :=
  toLpCell_slicePdIterR_P0Smooth hc hf Fin.elim0

lemma slicePdIterR_P0Smooth {c : ℝ} (hc : 0 < c)
    {f : B0579.Plane → F8Ex.RMerid} (hf : IsCylSmoothHInf c f)
    {n : ℕ} (β : Fin n → Fin 2) :
    F8Ex.slicePdIterR β (P0Smooth c f) = P0Smooth c (F8Ex.slicePdIterR β f) := by
  have h1 := P0Smooth_isCylSmoothHInf hc hf
  have h2 := P0Smooth_isCylSmoothHInf hc (hf.slicePdIterR β)
  refine PartI.aePeriodicEq c hc _ _
    (contDiff_slicePdIterR h1.smooth β).continuous h2.smooth.continuous
    (periodic_slicePdIterR h1.periodic β) h2.periodic ?_
  have hae1 := slicePdIterR_P0Smooth_ae hc hf β
  have hae2 := slicePdIterR_P0Smooth_ae hc (hf.slicePdIterR β) Fin.elim0
  have hlp : toLpCell ((hf.slicePdIterR β).memL2 0 Fin.elim0) = toLpCell (hf.memL2 n β) :=
    toLpCell_congr_ae _ _ (ae_of_all _ fun _ => rfl)
  rw [hlp] at hae2
  exact hae1.trans hae2.symm

lemma P0Smooth_add {c : ℝ} (hc : 0 < c)
    {f g : B0579.Plane → F8Ex.RMerid} (hf : IsCylSmoothHInf c f) (hg : IsCylSmoothHInf c g) :
    P0Smooth c (f + g) = P0Smooth c f + P0Smooth c g := by
  have hfg := P0Smooth_isCylSmoothHInf hc (hf.add hg)
  have hf' := P0Smooth_isCylSmoothHInf hc hf
  have hg' := P0Smooth_isCylSmoothHInf hc hg
  refine PartI.aePeriodicEq c hc _ _ hfg.smooth.continuous
    (hf'.smooth.continuous.add hg'.smooth.continuous)
    hfg.periodic (PartI.csr_per_add hf'.periodic hg'.periodic) ?_
  have hae_fg := slicePdIterR_P0Smooth_ae hc (hf.add hg) Fin.elim0
  have hae_f := slicePdIterR_P0Smooth_ae hc hf Fin.elim0
  have hae_g := slicePdIterR_P0Smooth_ae hc hg Fin.elim0
  have hlp : toLpCell ((hf.add hg).memL2 0 Fin.elim0) =
      toLpCell (hf.memL2 0 Fin.elim0) + toLpCell (hg.memL2 0 Fin.elim0) := by
    rw [← toLpCell_add]
    exact toLpCell_congr_ae _ _ (ae_of_all _ fun _ => rfl)
  rw [hlp, map_add] at hae_fg
  exact (hae_fg.trans (Lp.coeFn_add _ _)).trans (hae_f.add hae_g).symm

lemma P0Smooth_smul {c : ℝ} (hc : 0 < c) (r : ℝ)
    {f : B0579.Plane → F8Ex.RMerid} (hf : IsCylSmoothHInf c f) :
    P0Smooth c (r • f) = r • P0Smooth c f := by
  have hrf := P0Smooth_isCylSmoothHInf hc (hf.smul r)
  have hf' := P0Smooth_isCylSmoothHInf hc hf
  refine PartI.aePeriodicEq c hc _ _ hrf.smooth.continuous
    (hf'.smooth.continuous.const_smul r)
    hrf.periodic (PartI.csr_per_smul r hf'.periodic) ?_
  have hae_rf := slicePdIterR_P0Smooth_ae hc (hf.smul r) Fin.elim0
  have hae_f := slicePdIterR_P0Smooth_ae hc hf Fin.elim0
  have hlp : toLpCell ((hf.smul r).memL2 0 Fin.elim0) = r • toLpCell (hf.memL2 0 Fin.elim0) := by
    rw [← toLpCell_smul]
    exact toLpCell_congr_ae _ _ (ae_of_all _ fun _ => rfl)
  rw [hlp, map_smul] at hae_rf
  exact (hae_rf.trans (Lp.coeFn_smul r _)).trans (hae_f.const_smul r).symm

lemma P0Smooth_sub {c : ℝ} (hc : 0 < c)
    {f g : B0579.Plane → F8Ex.RMerid} (hf : IsCylSmoothHInf c f) (hg : IsCylSmoothHInf c g) :
    P0Smooth c (f - g) = P0Smooth c f - P0Smooth c g := by
  have h : f - g = f + (-1 : ℝ) • g := by
    funext y
    simp [sub_eq_add_neg]
  rw [h, P0Smooth_add hc hf (hg.smul (-1)), P0Smooth_smul hc (-1) hg]
  funext y
  simp [sub_eq_add_neg]

end UnforcedLeray.Short.IIb.F8JointUpgrade
