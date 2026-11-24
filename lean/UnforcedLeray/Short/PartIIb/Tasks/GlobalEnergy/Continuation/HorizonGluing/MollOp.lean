import UnforcedLeray.Short.PartIIb.Tasks.GlobalEnergy.Continuation.LinearGlue
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.LionsMagenesCyl.Mollifier
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.EnergyBound.WeightedEnergy.LionsMagenesCyl.MollIdentity
import UnforcedLeray.Short.PartIIIa.T18_FreeCausal.Existence.NiceForceSolution.LerayProjectSlices.P0DivFreeC

/-!
# `HorizonGluing.MollOp`: Bounded cylinder mollifier and Leray operators on `LMH c`

Internal helper module for `MeridionalHorizonGluing` (`PartII-b:F7/2/2`).
Defines the isometric dictionary between `CMerid` and `EuclideanSpace ℝ (Fin 4)`, together with
continuous `ℝ`-linear operators on `IIIa.LMH c`:
* `opP0 c hc`: cylinder Leray projection (`P0C c`),
* `opJ c hc J hJ k`: cylinder mollifier `J_k`,
* `opDJ c hc J hJ k j`: differentiated cylinder mollifier `∂_j J_k`,
along with their commutation, self-adjointness / anti-symmetry, strong convergence, and smooth
cell integration-by-parts dissipation/drift estimates.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff RealInnerProductSpace

namespace UnforcedLeray.Short.IIb.HorizonGluingAux

open UnforcedLeray.Short.IIb
open UnforcedLeray.Short.IIIa

/-! ### 1. Isometric dictionary `CMerid ↔ EuclideanSpace ℝ (Fin 4)` and `LMH c` norms -/

def cmeridToLM (v : CMerid) : EuclideanSpace ℝ (Fin 4) :=
  lmReal (fun i => v i)

def lmToCMerid (v : EuclideanSpace ℝ (Fin 4)) : CMerid :=
  WithLp.toLp 2 (lmSp v)

lemma cmeridToLM_lmToCMerid (v : EuclideanSpace ℝ (Fin 4)) :
    cmeridToLM (lmToCMerid v) = v :=
  lmReal_lmSp v

lemma lmToCMerid_cmeridToLM (v : CMerid) :
    lmToCMerid (cmeridToLM v) = v := by
  ext i
  fin_cases i <;> simp [lmToCMerid, cmeridToLM, lmReal, lmSp]

lemma continuous_cmeridToLM : Continuous cmeridToLM := by
  unfold cmeridToLM
  exact lmReal_continuous.comp (continuous_pi fun i => PiLp.continuous_apply 2 _ i)

lemma continuous_lmToCMerid : Continuous lmToCMerid := by
  change Continuous (fun v => WithLp.toLp 2 (fun i => lmSp v i))
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => ?_)
  fin_cases i
  · simp only [lmSp]
    exact (Complex.continuous_ofReal.comp (EuclideanSpace.proj 0).continuous).add
      ((Complex.continuous_ofReal.comp (EuclideanSpace.proj 1).continuous).mul continuous_const)
  · simp only [lmSp]
    exact (Complex.continuous_ofReal.comp (EuclideanSpace.proj 2).continuous).add
      ((Complex.continuous_ofReal.comp (EuclideanSpace.proj 3).continuous).mul continuous_const)

lemma norm_cmeridToLM (v : CMerid) : ‖cmeridToLM v‖ = ‖v‖ := by
  have hsq : ‖cmeridToLM v‖ ^ 2 = ‖v‖ ^ 2 := by
    unfold cmeridToLM
    rw [norm_lmReal_sq, vnorm2_sq_eq, PiLp.norm_sq_eq_of_L2]
  nlinarith [norm_nonneg (cmeridToLM v), norm_nonneg v]

lemma norm_lmToCMerid (v : EuclideanSpace ℝ (Fin 4)) : ‖lmToCMerid v‖ = ‖v‖ := by
  rw [← norm_cmeridToLM (lmToCMerid v), cmeridToLM_lmToCMerid]

lemma cmeridToLM_add (u v : CMerid) :
    cmeridToLM (u + v) = cmeridToLM u + cmeridToLM v := by
  ext j
  fin_cases j <;> simp [cmeridToLM, lmReal]

lemma cmeridToLM_sub (u v : CMerid) :
    cmeridToLM (u - v) = cmeridToLM u - cmeridToLM v := by
  ext j
  fin_cases j <;> simp [cmeridToLM, lmReal]

lemma cmeridToLM_smul (r : ℝ) (v : CMerid) :
    cmeridToLM (r • v) = r • cmeridToLM v := by
  ext j
  fin_cases j <;> simp [cmeridToLM, lmReal]

lemma lmToCMerid_add (u v : EuclideanSpace ℝ (Fin 4)) :
    lmToCMerid (u + v) = lmToCMerid u + lmToCMerid v := by
  ext i
  fin_cases i <;> simp [lmToCMerid, lmSp] <;> ring

lemma lmToCMerid_sub (u v : EuclideanSpace ℝ (Fin 4)) :
    lmToCMerid (u - v) = lmToCMerid u - lmToCMerid v := by
  ext i
  fin_cases i <;> simp [lmToCMerid, lmSp] <;> ring

lemma lmToCMerid_smul (r : ℝ) (v : EuclideanSpace ℝ (Fin 4)) :
    lmToCMerid (r • v) = r • lmToCMerid v := by
  ext i
  fin_cases i <;> simp [lmToCMerid, lmSp] <;> ring

lemma lmReal_add (f g : Fin 2 → ℂ) :
    lmReal (fun i => f i + g i) = lmReal f + lmReal g := by
  ext j
  fin_cases j <;> simp [lmReal]

lemma lmReal_sub (f g : Fin 2 → ℂ) :
    lmReal (fun i => f i - g i) = lmReal f - lmReal g := by
  ext j
  fin_cases j <;> simp [lmReal]

lemma lmReal_neg (f : Fin 2 → ℂ) :
    lmReal (fun i => -f i) = -lmReal f := by
  ext j
  fin_cases j <;> simp [lmReal]

lemma lmReal_real_smul (r : ℝ) (f : Fin 2 → ℂ) :
    lmReal (fun i => (r : ℂ) * f i) = r • lmReal f := by
  ext j
  fin_cases j <;> simp [lmReal]

lemma memLp_lmReal_of_lmCellL2 {c : ℝ} {f : LMSpField} (hf : LMCellL2 c f) :
    MemLp (fun x => lmReal (f x)) 2 (volume.restrict (B0579.cell c)) := by
  have hm : AEStronglyMeasurable (fun x => lmReal (f x)) (volume.restrict (B0579.cell c)) := by
    have hcont : Continuous (fun p : ℂ × ℂ => lmReal ![p.1, p.2]) :=
      lmReal_continuous.comp (continuous_pi fun i => by
        fin_cases i
        · exact continuous_fst
        · exact continuous_snd)
    have hfun : (fun x => lmReal (f x)) = fun x => lmReal ![f x 0, f x 1] := by
      funext x; congr 1; ext i; fin_cases i <;> rfl
    rw [hfun]
    exact hcont.comp_aestronglyMeasurable ((hf 0).1.prodMk (hf 1).1)
  refine memLp_two_of_lintegral_lt hm ?_
  have hsq : Integrable (fun x => vnorm2 (f x) ^ 2) (volume.restrict (B0579.cell c)) :=
    integrable_vnorm2_sq hf
  have heq : (fun x => ‖lmReal (f x)‖ₑ ^ (2 : ℝ)) =
      fun x => ‖vnorm2 (f x) ^ 2‖ₑ := by
    funext x
    rw [enorm_lmReal_sq (f x), Real.enorm_eq_ofReal (sq_nonneg _)]
  rw [heq]
  exact hsq.hasFiniteIntegral

def toLMH {c : ℝ} (f : LMSpField) (hf : LMCellL2 c f) : LMH c :=
  (memLp_lmReal_of_lmCellL2 hf).toLp (fun x => lmReal (f x))

lemma toLMH_ae {c : ℝ} {f : LMSpField} (hf : LMCellL2 c f) :
    (toLMH f hf : ℝ × ℝ → EuclideanSpace ℝ (Fin 4)) =ᵐ[volume.restrict (B0579.cell c)]
      fun x => lmReal (f x) :=
  (memLp_lmReal_of_lmCellL2 hf).coeFn_toLp

lemma lmLift_toLMH_ae {c : ℝ} {f : LMSpField} (hf : LMCellL2 c f) :
    ∀ᵐ x ∂(volume.restrict (B0579.cell c)), ∀ i : Fin 2, lmLift (toLMH f hf) x i = f x i := by
  filter_upwards [toLMH_ae hf] with x hx i
  unfold lmLift
  rw [hx]
  fin_cases i <;> simp [lmSp, lmReal]

lemma norm_toLMH_sq {c : ℝ} {f : LMSpField} (hf : LMCellL2 c f) :
    ‖toLMH f hf‖ ^ 2 = ∫ x in B0579.cell c, ∑ i : Fin 2, ‖f x i‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  have hae : (fun x => ⟪(toLMH f hf : ℝ × ℝ → EuclideanSpace ℝ (Fin 4)) x,
        (toLMH f hf : ℝ × ℝ → EuclideanSpace ℝ (Fin 4)) x⟫) =ᵐ[volume.restrict (B0579.cell c)]
      fun x => ∑ i : Fin 2, ‖f x i‖ ^ 2 := by
    filter_upwards [toLMH_ae hf] with x hx
    rw [hx, real_inner_self_eq_norm_sq, norm_lmReal_sq, vnorm2_sq_eq]
  exact integral_congr_ae hae

lemma inner_toLMH {c : ℝ} {f g : LMSpField} (hf : LMCellL2 c f) (hg : LMCellL2 c g) :
    ⟪toLMH f hf, toLMH g hg⟫ = (LMIp c f g).re := by
  have hre : (LMIp c f g).re =
      ∫ x in B0579.cell c, (∑ i : Fin 2, starRingEnd ℂ (f x i) * g x i).re := by
    unfold LMIp
    exact (integral_re (integrable_finsetSum _ fun i _ => lmIp_integrable hf hg i)).symm
  rw [L2.inner_def, hre]
  refine integral_congr_ae ?_
  filter_upwards [toLMH_ae hf, toLMH_ae hg] with x hxf hxg
  rw [hxf, hxg, lmReal_inner]

lemma inner_lmH_eq_re_lmIp {c : ℝ} (X Y : LMH c) :
    ⟪X, Y⟫ = (LMIp c (lmLift X) (lmLift Y)).re := by
  have hX : X = toLMH (lmLift X) (lmLift_cellL2 X) := by
    apply Lp.ext_iff.2
    filter_upwards [toLMH_ae (lmLift_cellL2 X)] with x hx
    rw [hx, lmLift_real]
  have hY : Y = toLMH (lmLift Y) (lmLift_cellL2 Y) := by
    apply Lp.ext_iff.2
    filter_upwards [toLMH_ae (lmLift_cellL2 Y)] with x hx
    rw [hx, lmLift_real]
  conv_lhs => rw [hX, hY]
  exact inner_toLMH (lmLift_cellL2 X) (lmLift_cellL2 Y)

lemma norm_lmH_sq_eq_integral {c : ℝ} (X : LMH c) :
    ‖X‖ ^ 2 = ∫ x in B0579.cell c, ∑ i : Fin 2, ‖lmLift X x i‖ ^ 2 := by
  have hX : X = toLMH (lmLift X) (lmLift_cellL2 X) := by
    apply Lp.ext_iff.2
    filter_upwards [toLMH_ae (lmLift_cellL2 X)] with x hx
    rw [hx, lmLift_real]
  conv_lhs => rw [hX]
  exact norm_toLMH_sq (lmLift_cellL2 X)

lemma cylSliceL2_eq_ofReal_norm {c : ℝ} {u : B0579.Plane → CMerid} {X : LMH c}
    (hae : (fun y => u y) =ᵐ[volume.restrict (B0579.cell c)]
      fun y => lmToCMerid ((X : ℝ × ℝ → EuclideanSpace ℝ (Fin 4)) y)) :
    cylSliceL2 c u = ENNReal.ofReal ‖X‖ := by
  unfold cylSliceL2
  have heq : eLpNorm u 2 (volume.restrict (B0579.cell c)) =
      eLpNorm (X : ℝ × ℝ → EuclideanSpace ℝ (Fin 4)) 2 (volume.restrict (B0579.cell c)) := by
    refine eLpNorm_congr_norm_ae ?_
    filter_upwards [hae] with y hy
    rw [hy, norm_lmToCMerid]
  rw [heq, Lp.norm_def]
  exact (ENNReal.ofReal_toReal (Lp.eLpNorm_lt_top X).ne).symm

/-! ### 2. Cylinder Leray projection `opP0 : LMH c →L[ℝ] LMH c` -/

lemma p0C_add_ae {c : ℝ} {f g : LMSpField} (hf : LMCellL2 c f) (hg : LMCellL2 c g) :
    ∀ᵐ x ∂(volume.restrict (B0579.cell c)), ∀ i : Fin 2,
      P0C c (fun y j => f y j + g y j) x i = P0C c f x i + P0C c g x i := by
  have hfg : LMCellL2 c (fun y j => f y j + g y j) := fun j => (hf j).add (hg j)
  have hre_eq : toL2v c (reVec (fun y j => f y j + g y j)) =
      toL2v c (reVec f) + toL2v c (reVec g) := by
    apply Lp.ext_iff.2
    filter_upwards [lm_toL2v_ae (lm_reVec_memLp hfg), lm_toL2v_ae (lm_reVec_memLp hf),
      lm_toL2v_ae (lm_reVec_memLp hg), Lp.coeFn_add (toL2v c (reVec f)) (toL2v c (reVec g))]
      with x hx1 hx2 hx3 hx4
    rw [hx1, hx4, Pi.add_apply, hx2, hx3]
    ext i; fin_cases i <;> simp [reVec]
  have him_eq : toL2v c (imVec (fun y j => f y j + g y j)) =
      toL2v c (imVec f) + toL2v c (imVec g) := by
    apply Lp.ext_iff.2
    filter_upwards [lm_toL2v_ae (lm_imVec_memLp hfg), lm_toL2v_ae (lm_imVec_memLp hf),
      lm_toL2v_ae (lm_imVec_memLp hg), Lp.coeFn_add (toL2v c (imVec f)) (toL2v c (imVec g))]
      with x hx1 hx2 hx3 hx4
    rw [hx1, hx4, Pi.add_apply, hx2, hx3]
    ext i; fin_cases i <;> simp [imVec]
  have hp1 : P0re c (fun y j => f y j + g y j) = P0re c f + P0re c g := by
    simp only [P0re, hre_eq, map_add]
  have hp2 : P0im c (fun y j => f y j + g y j) = P0im c f + P0im c g := by
    simp only [P0im, him_eq, map_add]
  have ha1 : ∀ᵐ x ∂(volume.restrict (B0579.cell c)),
      (P0re c f + P0re c g) x = P0re c f x + P0re c g x := by
    rw [← cellμ_eq c]; exact Lp.coeFn_add (P0re c f) (P0re c g)
  have ha2 : ∀ᵐ x ∂(volume.restrict (B0579.cell c)),
      (P0im c f + P0im c g) x = P0im c f x + P0im c g x := by
    rw [← cellμ_eq c]; exact Lp.coeFn_add (P0im c f) (P0im c g)
  filter_upwards [ha1, ha2] with x hx1 hx2 i
  simp only [P0C, cplxOf, hp1, hp2, hx1, hx2, PiLp.add_apply, Complex.ofReal_add]
  ring

lemma p0C_real_smul_ae {c : ℝ} (r : ℝ) {f : LMSpField} (hf : LMCellL2 c f) :
    ∀ᵐ x ∂(volume.restrict (B0579.cell c)), ∀ i : Fin 2,
      P0C c (fun y j => (r : ℂ) * f y j) x i = (r : ℂ) * P0C c f x i := by
  have hrf : LMCellL2 c (fun y j => (r : ℂ) * f y j) := fun j => (hf j).const_mul _
  have hre_eq : toL2v c (reVec (fun y j => (r : ℂ) * f y j)) = r • toL2v c (reVec f) := by
    apply Lp.ext_iff.2
    filter_upwards [lm_toL2v_ae (lm_reVec_memLp hrf), lm_toL2v_ae (lm_reVec_memLp hf),
      Lp.coeFn_smul r (toL2v c (reVec f))] with x hx1 hx2 hx3
    rw [hx1, hx3, Pi.smul_apply, hx2]
    ext i; fin_cases i <;> simp [reVec]
  have him_eq : toL2v c (imVec (fun y j => (r : ℂ) * f y j)) = r • toL2v c (imVec f) := by
    apply Lp.ext_iff.2
    filter_upwards [lm_toL2v_ae (lm_imVec_memLp hrf), lm_toL2v_ae (lm_imVec_memLp hf),
      Lp.coeFn_smul r (toL2v c (imVec f))] with x hx1 hx2 hx3
    rw [hx1, hx3, Pi.smul_apply, hx2]
    ext i; fin_cases i <;> simp [imVec]
  have hp1 : P0re c (fun y j => (r : ℂ) * f y j) = r • P0re c f := by
    simp only [P0re, hre_eq, map_smul]
  have hp2 : P0im c (fun y j => (r : ℂ) * f y j) = r • P0im c f := by
    simp only [P0im, him_eq, map_smul]
  have ha1 : ∀ᵐ x ∂(volume.restrict (B0579.cell c)),
      (r • P0re c f) x = (r • (P0re c f : ℝ × ℝ → Cyl.Vec2)) x := by
    rw [← cellμ_eq c]; exact Lp.coeFn_smul r (P0re c f)
  have ha2 : ∀ᵐ x ∂(volume.restrict (B0579.cell c)),
      (r • P0im c f) x = (r • (P0im c f : ℝ × ℝ → Cyl.Vec2)) x := by
    rw [← cellμ_eq c]; exact Lp.coeFn_smul r (P0im c f)
  filter_upwards [ha1, ha2] with x hx1 hx2 i
  simp only [P0C, cplxOf, hp1, hp2, hx1, hx2, Pi.smul_apply, PiLp.smul_apply,
    smul_eq_mul, Complex.ofReal_mul]
  ring

def opP0 (c : ℝ) (hc : 0 < c) : LMH c →L[ℝ] LMH c :=
  LinearMap.mkContinuous
    { toFun := fun X => toLMH (P0C c (lmLift X)) (lmP0C_cellL2 c (lmLift X))
      map_add' := fun X Y => by
        apply Lp.ext_iff.2
        have hXY : ∀ᵐ x ∂(volume.restrict (B0579.cell c)), ∀ i : Fin 2,
            lmLift (X + Y) x i = lmLift X x i + lmLift Y x i := by
          filter_upwards [Lp.coeFn_add X Y] with x hx i
          unfold lmLift
          rw [hx, Pi.add_apply]
          fin_cases i <;> simp [lmSp] <;> ring
        have hXY_c : ∀ᵐ x ∂(Cyl.cellμ c), ∀ i : Fin 2,
            lmLift (X + Y) x i = lmLift X x i + lmLift Y x i := by
          rwa [cellμ_eq c]
        have hcongr : ∀ᵐ x ∂(volume.restrict (B0579.cell c)), ∀ i : Fin 2,
            P0C c (lmLift (X + Y)) x i = P0C c (fun y j => lmLift X y j + lmLift Y y j) x i := by
          have hre : toL2v c (reVec (lmLift (X + Y))) =
              toL2v c (reVec (fun y j => lmLift X y j + lmLift Y y j)) := by
            apply Lp.ext_iff.2
            filter_upwards [lm_toL2v_ae (lm_reVec_memLp (lmLift_cellL2 (X + Y))),
              lm_toL2v_ae (lm_reVec_memLp (f := fun y j => lmLift X y j + lmLift Y y j)
                (fun j => (lmLift_cellL2 X j).add (lmLift_cellL2 Y j))),
              hXY_c] with x hx1 hx2 hxy
            rw [hx1, hx2]
            ext i; fin_cases i <;> simp [reVec, hxy]
          have him : toL2v c (imVec (lmLift (X + Y))) =
              toL2v c (imVec (fun y j => lmLift X y j + lmLift Y y j)) := by
            apply Lp.ext_iff.2
            filter_upwards [lm_toL2v_ae (lm_imVec_memLp (lmLift_cellL2 (X + Y))),
              lm_toL2v_ae (lm_imVec_memLp (f := fun y j => lmLift X y j + lmLift Y y j)
                (fun j => (lmLift_cellL2 X j).add (lmLift_cellL2 Y j))),
              hXY_c] with x hx1 hx2 hxy
            rw [hx1, hx2]
            ext i; fin_cases i <;> simp [imVec, hxy]
          exact Eventually.of_forall fun x i => by simp [P0C, P0re, P0im, hre, him]
        filter_upwards [toLMH_ae (lmP0C_cellL2 c (lmLift (X + Y))),
          toLMH_ae (lmP0C_cellL2 c (lmLift X)),
          toLMH_ae (lmP0C_cellL2 c (lmLift Y)),
          Lp.coeFn_add (toLMH (P0C c (lmLift X)) (lmP0C_cellL2 c (lmLift X)))
            (toLMH (P0C c (lmLift Y)) (lmP0C_cellL2 c (lmLift Y))),
          hcongr, p0C_add_ae (lmLift_cellL2 X) (lmLift_cellL2 Y)] with x h1 h2 h3 h4 hc1 hp
        rw [h1, h4, Pi.add_apply, h2, h3, ← lmReal_add]
        congr 1; ext i; rw [hc1 i, hp i]
      map_smul' := fun r X => by
        apply Lp.ext_iff.2
        have hrX : ∀ᵐ x ∂(volume.restrict (B0579.cell c)), ∀ i : Fin 2,
            lmLift (r • X) x i = (r : ℂ) * lmLift X x i := by
          filter_upwards [Lp.coeFn_smul r X] with x hx i
          unfold lmLift
          rw [hx, Pi.smul_apply]
          fin_cases i <;> simp [lmSp] <;> ring
        have hrX_c : ∀ᵐ x ∂(Cyl.cellμ c), ∀ i : Fin 2,
            lmLift (r • X) x i = (r : ℂ) * lmLift X x i := by
          rwa [cellμ_eq c]
        have hcongr : ∀ᵐ x ∂(volume.restrict (B0579.cell c)), ∀ i : Fin 2,
            P0C c (lmLift (r • X)) x i = P0C c (fun y j => (r : ℂ) * lmLift X y j) x i := by
          have hre : toL2v c (reVec (lmLift (r • X))) =
              toL2v c (reVec (fun y j => (r : ℂ) * lmLift X y j)) := by
            apply Lp.ext_iff.2
            filter_upwards [lm_toL2v_ae (lm_reVec_memLp (lmLift_cellL2 (r • X))),
              lm_toL2v_ae (lm_reVec_memLp (f := fun y j => (r : ℂ) * lmLift X y j)
                (fun j => (lmLift_cellL2 X j).const_mul _)),
              hrX_c] with x hx1 hx2 hrx
            rw [hx1, hx2]
            ext i; fin_cases i <;> simp [reVec, hrx]
          have him : toL2v c (imVec (lmLift (r • X))) =
              toL2v c (imVec (fun y j => (r : ℂ) * lmLift X y j)) := by
            apply Lp.ext_iff.2
            filter_upwards [lm_toL2v_ae (lm_imVec_memLp (lmLift_cellL2 (r • X))),
              lm_toL2v_ae (lm_imVec_memLp (f := fun y j => (r : ℂ) * lmLift X y j)
                (fun j => (lmLift_cellL2 X j).const_mul _)),
              hrX_c] with x hx1 hx2 hrx
            rw [hx1, hx2]
            ext i; fin_cases i <;> simp [imVec, hrx]
          exact Eventually.of_forall fun x i => by simp [P0C, P0re, P0im, hre, him]
        filter_upwards [toLMH_ae (lmP0C_cellL2 c (lmLift (r • X))),
          toLMH_ae (lmP0C_cellL2 c (lmLift X)),
          Lp.coeFn_smul r (toLMH (P0C c (lmLift X)) (lmP0C_cellL2 c (lmLift X))),
          hcongr, p0C_real_smul_ae r (lmLift_cellL2 X)] with x h1 h2 h3 hc1 hp
        rw [RingHom.id_apply, h1, h3, Pi.smul_apply, h2, ← lmReal_real_smul]
        congr 1; ext i; rw [hc1 i, hp i] }
    1
    (fun X => by
      change ‖toLMH (P0C c (lmLift X)) (lmP0C_cellL2 c (lmLift X))‖ ≤ 1 * ‖X‖
      rw [one_mul]
      have hsq : ‖toLMH (P0C c (lmLift X)) (lmP0C_cellL2 c (lmLift X))‖ ^ 2 ≤ ‖X‖ ^ 2 := by
        rw [norm_toLMH_sq (lmP0C_cellL2 c (lmLift X)), norm_lmH_sq_eq_integral X]
        exact lmP0CContr c hc (lmLift X) (lmLift_cellL2 X)
      nlinarith [norm_nonneg (toLMH (P0C c (lmLift X)) (lmP0C_cellL2 c (lmLift X))), norm_nonneg X])

lemma opP0_ae {c : ℝ} (hc : 0 < c) (X : LMH c) :
    (opP0 c hc X : ℝ × ℝ → EuclideanSpace ℝ (Fin 4)) =ᵐ[volume.restrict (B0579.cell c)]
      fun x => lmReal (P0C c (lmLift X) x) :=
  toLMH_ae (lmP0C_cellL2 c (lmLift X))

lemma lmLift_opP0_ae {c : ℝ} (hc : 0 < c) (X : LMH c) :
    ∀ᵐ x ∂(volume.restrict (B0579.cell c)), ∀ i : Fin 2,
      lmLift (opP0 c hc X) x i = P0C c (lmLift X) x i :=
  lmLift_toLMH_ae (lmP0C_cellL2 c (lmLift X))

lemma norm_opP0_le {c : ℝ} (hc : 0 < c) (X : LMH c) : ‖opP0 c hc X‖ ≤ ‖X‖ := by
  calc ‖opP0 c hc X‖ ≤ ‖opP0 c hc‖ * ‖X‖ := (opP0 c hc).le_opNorm X
    _ ≤ 1 * ‖X‖ := mul_le_mul_of_nonneg_right
        (LinearMap.mkContinuous_norm_le _ zero_le_one _) (norm_nonneg X)
    _ = ‖X‖ := one_mul _

lemma inner_opP0_selfAdj {c : ℝ} (hc : 0 < c) (X Y : LMH c) :
    ⟪opP0 c hc X, Y⟫ = ⟪X, opP0 c hc Y⟫ := by
  rw [inner_lmH_eq_re_lmIp, inner_lmH_eq_re_lmIp]
  have e1 := lmIp_congr_left (g := lmLift Y) (lmLift_opP0_ae hc X)
  have e2 := lmIp_congr_right (f := lmLift X) (lmLift_opP0_ae hc Y)
  rw [e1, e2, lmP0CAdj c hc (lmLift X) (lmLift Y) (lmLift_cellL2 X) (lmLift_cellL2 Y)]

lemma opP0_weakDivFree {c : ℝ} (hc : 0 < c) (X : LMH c) :
    LMWeakDivFree c (lmLift (opP0 c hc X)) := by
  intro ψ hψ
  have h0 := p0DivFreeC c hc (lmLift X) ψ hψ
  rw [← h0]
  refine integral_congr_ae ?_
  filter_upwards [lmLift_opP0_ae hc X] with x hx
  rw [hx 0, hx 1]

lemma opP0_eq_self_of_weakDivFree {c : ℝ} (hc : 0 < c) {X : LMH c}
    (hdiv : LMWeakDivFree c (lmLift X)) :
    opP0 c hc X = X := by
  apply Lp.ext_iff.2
  filter_upwards [opP0_ae hc X, lmP0CFix c hc (lmLift X) (lmLift_cellL2 X) hdiv] with x hx hfix
  rw [hx]
  have hfun : P0C c (lmLift X) x = lmLift X x := funext hfix
  rw [hfun, lmLift_real]

lemma opP0_idem {c : ℝ} (hc : 0 < c) (X : LMH c) :
    opP0 c hc (opP0 c hc X) = opP0 c hc X :=
  opP0_eq_self_of_weakDivFree hc (opP0_weakDivFree hc X)

/-! ### 3. Cylinder mollifiers `opJ` and `opDJ` on `LMH c` -/

lemma j_congr_ae {c : ℝ} (hc : 0 < c) {J : ℕ → LMSpField → LMSpField} (hJ : IsLMMollifier c J)
    (k : ℕ) {f g : LMSpField} (hf : LMCellL2 c f) (hg : LMCellL2 c g)
    (hfg : ∀ᵐ x ∂(volume.restrict (B0579.cell c)), ∀ i : Fin 2, f x i = g x i) :
    ∀ x i, J k f x i = J k g x i := by
  have hdiff : LMCellL2 c (fun x i => f x i + (-1 : ℂ) * g x i) :=
    fun i => (hf i).add ((hg i).const_mul _)
  have hzero_int : ∫ x in B0579.cell c, ∑ i : Fin 2, ‖(f x i + (-1 : ℂ) * g x i)‖ ^ 2 = 0 := by
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hfg] with x hx
    simp [hx]
  have hcontr := hJ.contr k _ hdiff
  rw [hzero_int] at hcontr
  have hnn : 0 ≤ ∫ x in B0579.cell c,
      ∑ i : Fin 2, ‖J k (fun y j => f y j + (-1 : ℂ) * g y j) x i‖ ^ 2 :=
    integral_nonneg fun x => Finset.sum_nonneg fun i _ => sq_nonneg _
  have heq0 : ∫ x in B0579.cell c,
      ∑ i : Fin 2, ‖J k (fun y j => f y j + (-1 : ℂ) * g y j) x i‖ ^ 2 = 0 :=
    le_antisymm hcontr hnn
  have hint : Integrable
      (fun x => ∑ i : Fin 2, ‖J k (fun y j => f y j + (-1 : ℂ) * g y j) x i‖ ^ 2)
      (volume.restrict (B0579.cell c)) :=
    lm_vec_sq_integrable (hJ.memL2 k _ hdiff)
  have hae0 := (integral_eq_zero_iff_of_nonneg
    (fun x => Finset.sum_nonneg fun i _ => sq_nonneg _) hint).1 heq0
  have hlin : J k (fun y j => f y j + (-1 : ℂ) * g y j) =
      fun x i => J k f x i - J k g x i := by
    rw [hJ.add k f _ hf (fun i => (hg i).const_mul _), hJ.smul k (-1) g hg]
    funext x i; ring
  have hcell_open : IsOpen (Ioo (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ)) :=
    isOpen_Ioo.prod isOpen_univ
  have hsub : Ioo (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ) ⊆ B0579.cell c :=
    prod_mono Ioo_subset_Ico_self subset_rfl
  have hae_open : ∀ᵐ x ∂(volume.restrict (Ioo (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ))),
      ∀ i : Fin 2, J k f x i = J k g x i := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hae0] with x hx i
    rw [hlin] at hx
    have hi : ‖J k f x i - J k g x i‖ ^ 2 ≤
        ∑ l : Fin 2, ‖J k f x l - J k g x l‖ ^ 2 :=
      Finset.single_le_sum (f := fun l : Fin 2 => ‖J k f x l - J k g x l‖ ^ 2)
        (fun l _ => sq_nonneg _) (Finset.mem_univ i)
    have hsq0 : ‖J k f x i - J k g x i‖ ^ 2 = 0 := le_antisymm (hi.trans (le_of_eq hx)) (sq_nonneg _)
    exact sub_eq_zero.1 (norm_eq_zero.1 (sq_eq_zero_iff.1 hsq0))
  have hcont_eq : ∀ i : Fin 2, EqOn (fun x => J k f x i) (fun x => J k g x i)
      (Ioo (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ)) := by
    intro i
    have hae_i : (fun x => J k f x i) =ᵐ[volume.restrict (Ioo (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ))]
        fun x => J k g x i := hae_open.mono fun x hx => hx i
    exact Measure.eqOn_open_of_ae_eq hae_i hcell_open
      (hJ.smooth k f hf i).continuous.continuousOn
      (hJ.smooth k g hg i).continuous.continuousOn
  have hIcc : ∀ i : Fin 2, EqOn (fun x => J k f x i) (fun x => J k g x i)
      (Icc (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ)) := by
    intro i
    have hcl : closure (Ioo (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ)) =
        Icc (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ) := by
      rw [closure_prod_eq, closure_Ioo (by linarith : -(c / 2) ≠ c / 2), closure_univ]
    rw [← hcl]
    exact (hcont_eq i).closure (hJ.smooth k f hf i).continuous (hJ.smooth k g hg i).continuous
  have hper_nat : ∀ (h : LMSpField), LMCellL2 c h → ∀ (m : ℕ) (x : ℝ × ℝ) (i : Fin 2),
      J k h (x.1 + (m : ℝ) * c, x.2) i = J k h x i := by
    intro h hh m
    induction m with
    | zero => intro x i; simp
    | succ m ih =>
      intro x i
      have heq : x.1 + ((m + 1 : ℕ) : ℝ) * c = (x.1 + (m : ℝ) * c) + c := by push_cast; ring
      rw [heq, hJ.periodic k h hh (x.1 + (m : ℝ) * c, x.2) i, ih]
  have hper_int : ∀ (h : LMSpField), LMCellL2 c h → ∀ (n : ℤ) (x : ℝ × ℝ) (i : Fin 2),
      J k h (x.1 + (n : ℝ) * c, x.2) i = J k h x i := by
    intro h hh n x i
    rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
    · simpa using hper_nat h hh m x i
    · have h1 := hper_nat h hh m (x.1 - (m : ℝ) * c, x.2) i
      have heq1 : x.1 - (m : ℝ) * c + (m : ℝ) * c = x.1 := by ring
      rw [heq1] at h1
      push_cast
      rw [show x.1 + -(m : ℝ) * c = x.1 - (m : ℝ) * c by ring]
      exact h1.symm
  intro x i
  set m : ℤ := ⌊(x.1 + c / 2) / c⌋
  set q₀ : ℝ := x.1 - (m : ℝ) * c
  have hlo : -(c / 2) ≤ q₀ := by
    have := Int.floor_le ((x.1 + c / 2) / c)
    have hm := mul_le_mul_of_nonneg_right this hc.le
    have hd : (x.1 + c / 2) / c * c = x.1 + c / 2 := div_mul_cancel₀ _ hc.ne'
    linarith
  have hhi : q₀ ≤ c / 2 := by
    have := Int.lt_floor_add_one ((x.1 + c / 2) / c)
    have hm := mul_lt_mul_of_pos_right this hc
    have hd : (x.1 + c / 2) / c * c = x.1 + c / 2 := div_mul_cancel₀ _ hc.ne'
    linarith
  have hx_shift : x = (q₀ + (m : ℝ) * c, x.2) := by
    ext <;> simp [q₀]
  rw [hx_shift, hper_int f hf m (q₀, x.2) i, hper_int g hg m (q₀, x.2) i]
  exact hIcc i ⟨⟨hlo, hhi⟩, trivial⟩

def opJ (c : ℝ) (hc : 0 < c) (J : ℕ → LMSpField → LMSpField) (hJ : IsLMMollifier c J) (k : ℕ) :
    LMH c →L[ℝ] LMH c :=
  LinearMap.mkContinuous
    { toFun := fun X => toLMH (J k (lmLift X)) (hJ.memL2 k (lmLift X) (lmLift_cellL2 X))
      map_add' := fun X Y => by
        apply Lp.ext_iff.2
        have hXY : ∀ᵐ x ∂(volume.restrict (B0579.cell c)), ∀ i : Fin 2,
            lmLift (X + Y) x i = lmLift X x i + lmLift Y x i := by
          filter_upwards [Lp.coeFn_add X Y] with x hx i
          unfold lmLift
          rw [hx, Pi.add_apply]
          fin_cases i <;> simp [lmSp] <;> ring
        have hjXY := j_congr_ae hc hJ k
          (f := lmLift (X + Y)) (g := fun y l => lmLift X y l + lmLift Y y l)
          (lmLift_cellL2 (X + Y)) (fun l => (lmLift_cellL2 X l).add (lmLift_cellL2 Y l)) hXY
        have hadd := hJ.add k (lmLift X) (lmLift Y) (lmLift_cellL2 X) (lmLift_cellL2 Y)
        filter_upwards [toLMH_ae (hJ.memL2 k (lmLift (X + Y)) (lmLift_cellL2 (X + Y))),
          toLMH_ae (hJ.memL2 k (lmLift X) (lmLift_cellL2 X)),
          toLMH_ae (hJ.memL2 k (lmLift Y) (lmLift_cellL2 Y)),
          Lp.coeFn_add (toLMH (J k (lmLift X)) (hJ.memL2 k (lmLift X) (lmLift_cellL2 X)))
            (toLMH (J k (lmLift Y)) (hJ.memL2 k (lmLift Y) (lmLift_cellL2 Y)))] with x h1 h2 h3 h4
        rw [h1, h4, Pi.add_apply, h2, h3, ← lmReal_add]
        congr 1; ext i; rw [hjXY x i]; exact congr_fun (congr_fun hadd x) i
      map_smul' := fun r X => by
        apply Lp.ext_iff.2
        have hrX : ∀ᵐ x ∂(volume.restrict (B0579.cell c)), ∀ i : Fin 2,
            lmLift (r • X) x i = (r : ℂ) * lmLift X x i := by
          filter_upwards [Lp.coeFn_smul r X] with x hx i
          unfold lmLift
          rw [hx, Pi.smul_apply]
          fin_cases i <;> simp [lmSp] <;> ring
        have hjrX := j_congr_ae hc hJ k
          (f := lmLift (r • X)) (g := fun y l => (r : ℂ) * lmLift X y l)
          (lmLift_cellL2 (r • X)) (fun l => (lmLift_cellL2 X l).const_mul _) hrX
        have hsmul := hJ.smul k (r : ℂ) (lmLift X) (lmLift_cellL2 X)
        filter_upwards [toLMH_ae (hJ.memL2 k (lmLift (r • X)) (lmLift_cellL2 (r • X))),
          toLMH_ae (hJ.memL2 k (lmLift X) (lmLift_cellL2 X)),
          Lp.coeFn_smul r (toLMH (J k (lmLift X)) (hJ.memL2 k (lmLift X) (lmLift_cellL2 X)))]
          with x h1 h2 h3
        rw [RingHom.id_apply, h1, h3, Pi.smul_apply, h2, ← lmReal_real_smul]
        congr 1; ext i; rw [hjrX x i]; exact congr_fun (congr_fun hsmul x) i }
    1
    (fun X => by
      change ‖toLMH (J k (lmLift X)) (hJ.memL2 k (lmLift X) (lmLift_cellL2 X))‖ ≤ 1 * ‖X‖
      rw [one_mul]
      have hsq : ‖toLMH (J k (lmLift X)) (hJ.memL2 k (lmLift X) (lmLift_cellL2 X))‖ ^ 2 ≤
          ‖X‖ ^ 2 := by
        rw [norm_toLMH_sq, norm_lmH_sq_eq_integral X]
        exact hJ.contr k (lmLift X) (lmLift_cellL2 X)
      nlinarith [norm_nonneg (toLMH (J k (lmLift X)) (hJ.memL2 k (lmLift X) (lmLift_cellL2 X))),
        norm_nonneg X])

lemma opJ_ae {c : ℝ} (hc : 0 < c) {J : ℕ → LMSpField → LMSpField} (hJ : IsLMMollifier c J)
    (k : ℕ) (X : LMH c) :
    (opJ c hc J hJ k X : ℝ × ℝ → EuclideanSpace ℝ (Fin 4)) =ᵐ[volume.restrict (B0579.cell c)]
      fun x => lmReal (J k (lmLift X) x) :=
  toLMH_ae (hJ.memL2 k (lmLift X) (lmLift_cellL2 X))

lemma lmLift_opJ_ae {c : ℝ} (hc : 0 < c) {J : ℕ → LMSpField → LMSpField} (hJ : IsLMMollifier c J)
    (k : ℕ) (X : LMH c) :
    ∀ᵐ x ∂(volume.restrict (B0579.cell c)), ∀ i : Fin 2,
      lmLift (opJ c hc J hJ k X) x i = J k (lmLift X) x i :=
  lmLift_toLMH_ae (hJ.memL2 k (lmLift X) (lmLift_cellL2 X))

lemma norm_opJ_le {c : ℝ} (hc : 0 < c) {J : ℕ → LMSpField → LMSpField} (hJ : IsLMMollifier c J)
    (k : ℕ) (X : LMH c) : ‖opJ c hc J hJ k X‖ ≤ ‖X‖ := by
  calc ‖opJ c hc J hJ k X‖ ≤ ‖opJ c hc J hJ k‖ * ‖X‖ := (opJ c hc J hJ k).le_opNorm X
    _ ≤ 1 * ‖X‖ := mul_le_mul_of_nonneg_right
        (LinearMap.mkContinuous_norm_le _ zero_le_one _) (norm_nonneg X)
    _ = ‖X‖ := one_mul _

lemma inner_opJ_selfAdj {c : ℝ} (hc : 0 < c) {J : ℕ → LMSpField → LMSpField}
    (hJ : IsLMMollifier c J) (k : ℕ) (X Y : LMH c) :
    ⟪opJ c hc J hJ k X, Y⟫ = ⟪X, opJ c hc J hJ k Y⟫ := by
  rw [inner_lmH_eq_re_lmIp, inner_lmH_eq_re_lmIp]
  rw [lmIp_congr_left (lmLift_opJ_ae hc hJ k X), lmIp_congr_right (lmLift_opJ_ae hc hJ k Y)]
  unfold LMIp
  rw [hJ.selfAdj k (lmLift X) (lmLift Y) (lmLift_cellL2 X) (lmLift_cellL2 Y)]

lemma tendsto_opJ {c : ℝ} (hc : 0 < c) {J : ℕ → LMSpField → LMSpField}
    (hJ : IsLMMollifier c J) (X : LMH c) :
    Tendsto (fun k => opJ c hc J hJ k X) atTop (𝓝 X) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsq : Tendsto (fun k => ‖opJ c hc J hJ k X - X‖ ^ 2) atTop (𝓝 0) := by
    have heq : ∀ k : ℕ, ‖opJ c hc J hJ k X - X‖ ^ 2 =
        ∫ x in B0579.cell c, ∑ i : Fin 2, ‖J k (lmLift X) x i - lmLift X x i‖ ^ 2 := by
      intro k
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_sub (opJ c hc J hJ k X) X, opJ_ae hc hJ k X] with x hsub hjk
      rw [hsub, Pi.sub_apply, hjk, ← lmLift_real X x, ← lmReal_sub,
        real_inner_self_eq_norm_sq, norm_lmReal_sq, vnorm2_sq_eq]
    simp_rw [heq]
    exact hJ.tendsto (lmLift X) (lmLift_cellL2 X)
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsq
  rw [Real.sqrt_zero] at hsqrt
  exact hsqrt.congr fun k => Real.sqrt_sq (norm_nonneg _)

lemma tendsto_opJ_sq {c : ℝ} (hc : 0 < c) {J : ℕ → LMSpField → LMSpField}
    (hJ : IsLMMollifier c J) (X : LMH c) :
    Tendsto (fun k => opJ c hc J hJ k (opJ c hc J hJ k X)) atTop (𝓝 X) := by
  have h1 := Metric.tendsto_atTop.1 (tendsto_opJ hc hJ X)
  refine Metric.tendsto_atTop.2 fun ε hε => ?_
  obtain ⟨N, hN⟩ := h1 (ε / 2) (half_pos hε)
  refine ⟨N, fun k hk => ?_⟩
  rw [dist_eq_norm]
  set D : LMH c := opJ c hc J hJ k X - X
  have hk_lt : ‖D‖ < ε / 2 := by simpa [D, dist_eq_norm] using hN k hk
  have heq : opJ c hc J hJ k (opJ c hc J hJ k X) - X = opJ c hc J hJ k D + D := by
    simp [D, map_sub, sub_add_sub_cancel]
  have htri : ‖opJ c hc J hJ k D + D‖ ≤ ‖opJ c hc J hJ k D‖ + ‖D‖ := norm_add_le _ _
  have hn : ‖opJ c hc J hJ k D‖ ≤ ‖D‖ := norm_opJ_le hc hJ k D
  rw [heq]
  linarith

lemma dj_cellL2 {c : ℝ} {J : ℕ → LMSpField → LMSpField} (hJ : IsLMMollifier c J)
    (k : ℕ) (j : Fin 2) {f : LMSpField} (hf : LMCellL2 c f) :
    LMCellL2 c (fun x i => LMPd j (fun y => J k f y i) x) := by
  obtain ⟨C, hC⟩ := hJ.gradL2 k
  exact fun i => (hC f hf i j).1

def opDJ (c : ℝ) (hc : 0 < c) (J : ℕ → LMSpField → LMSpField) (hJ : IsLMMollifier c J)
    (k : ℕ) (j : Fin 2) : LMH c →L[ℝ] LMH c :=
  let Ck : ℝ := max 0 (Classical.choose (hJ.gradL2 k))
  LinearMap.mkContinuous
    { toFun := fun X =>
        toLMH (fun x i => LMPd j (fun y => J k (lmLift X) y i) x)
          (dj_cellL2 hJ k j (lmLift_cellL2 X))
      map_add' := fun X Y => by
        apply Lp.ext_iff.2
        have hXY : ∀ᵐ x ∂(volume.restrict (B0579.cell c)), ∀ i : Fin 2,
            lmLift (X + Y) x i = lmLift X x i + lmLift Y x i := by
          filter_upwards [Lp.coeFn_add X Y] with x hx i
          unfold lmLift
          rw [hx, Pi.add_apply]
          fin_cases i <;> simp [lmSp] <;> ring
        have hjXY := j_congr_ae hc hJ k
          (f := lmLift (X + Y)) (g := fun y l => lmLift X y l + lmLift Y y l)
          (lmLift_cellL2 (X + Y)) (fun l => (lmLift_cellL2 X l).add (lmLift_cellL2 Y l)) hXY
        have hadd := hJ.add k (lmLift X) (lmLift Y) (lmLift_cellL2 X) (lmLift_cellL2 Y)
        filter_upwards [
          toLMH_ae (dj_cellL2 hJ k j (lmLift_cellL2 (X + Y))),
          toLMH_ae (dj_cellL2 hJ k j (lmLift_cellL2 X)),
          toLMH_ae (dj_cellL2 hJ k j (lmLift_cellL2 Y)),
          Lp.coeFn_add
            (toLMH (fun x i => LMPd j (fun y => J k (lmLift X) y i) x)
              (dj_cellL2 hJ k j (lmLift_cellL2 X)))
            (toLMH (fun x i => LMPd j (fun y => J k (lmLift Y) y i) x)
              (dj_cellL2 hJ k j (lmLift_cellL2 Y)))] with x h1 h2 h3 h4
        rw [h1, h4, Pi.add_apply, h2, h3, ← lmReal_add]
        congr 1; ext i
        have hfun : (fun y => J k (lmLift (X + Y)) y i) =
            fun y => J k (lmLift X) y i + (1 : ℂ) * J k (lmLift Y) y i := by
          funext y; rw [hjXY y i, congr_fun (congr_fun hadd y) i, one_mul]
        rw [hfun, lmPd_add_const_mul
          ((hJ.smooth k (lmLift X) (lmLift_cellL2 X) i).differentiable (by simp))
          ((hJ.smooth k (lmLift Y) (lmLift_cellL2 Y) i).differentiable (by simp))]
        ring
      map_smul' := fun r X => by
        apply Lp.ext_iff.2
        have hrX : ∀ᵐ x ∂(volume.restrict (B0579.cell c)), ∀ i : Fin 2,
            lmLift (r • X) x i = (r : ℂ) * lmLift X x i := by
          filter_upwards [Lp.coeFn_smul r X] with x hx i
          unfold lmLift
          rw [hx, Pi.smul_apply]
          fin_cases i <;> simp [lmSp] <;> ring
        have hjrX := j_congr_ae hc hJ k
          (f := lmLift (r • X)) (g := fun y l => (r : ℂ) * lmLift X y l)
          (lmLift_cellL2 (r • X)) (fun l => (lmLift_cellL2 X l).const_mul _) hrX
        have hsmul := hJ.smul k (r : ℂ) (lmLift X) (lmLift_cellL2 X)
        filter_upwards [
          toLMH_ae (dj_cellL2 hJ k j (lmLift_cellL2 (r • X))),
          toLMH_ae (dj_cellL2 hJ k j (lmLift_cellL2 X)),
          Lp.coeFn_smul r
            (toLMH (fun x i => LMPd j (fun y => J k (lmLift X) y i) x)
              (dj_cellL2 hJ k j (lmLift_cellL2 X)))] with x h1 h2 h3
        rw [RingHom.id_apply, h1, h3, Pi.smul_apply, h2, ← lmReal_real_smul]
        congr 1; ext i
        have hfun : (fun y => J k (lmLift (r • X)) y i) =
            fun y => (0 : ℂ) + (r : ℂ) * J k (lmLift X) y i := by
          funext y; rw [hjrX y i, congr_fun (congr_fun hsmul y) i, zero_add]
        have hd0 : LMPd j (fun _ : ℝ × ℝ => (0 : ℂ)) x = 0 := by
          rw [lmPd_eq_fderiv (differentiableAt_const _)]; simp
        rw [hfun, lmPd_add_const_mul (differentiable_const _)
          ((hJ.smooth k (lmLift X) (lmLift_cellL2 X) i).differentiable (by simp)), hd0, zero_add] }
    (Real.sqrt (2 * Ck))
    (fun X => by
      change ‖toLMH (fun x i => LMPd j (fun y => J k (lmLift X) y i) x)
          (dj_cellL2 hJ k j (lmLift_cellL2 X))‖ ≤ Real.sqrt (2 * Ck) * ‖X‖
      have hC := Classical.choose_spec (hJ.gradL2 k) (lmLift X) (lmLift_cellL2 X)
      have hsq :
          ‖toLMH (fun x i => LMPd j (fun y => J k (lmLift X) y i) x)
              (dj_cellL2 hJ k j (lmLift_cellL2 X))‖ ^ 2 ≤
            (Real.sqrt (2 * Ck) * ‖X‖) ^ 2 := by
        rw [norm_toLMH_sq, mul_pow, Real.sq_sqrt (by positivity), norm_lmH_sq_eq_integral X]
        rw [integral_finsetSum _ fun i _ => lm_sq_integrable (hC i j).1, Fin.sum_univ_two]
        have h0 := (hC 0 j).2
        have h1 := (hC 1 j).2
        have hnnX : 0 ≤ ∫ x in B0579.cell c, ∑ l : Fin 2, ‖lmLift X x l‖ ^ 2 :=
          integral_nonneg fun x => Finset.sum_nonneg fun l _ => sq_nonneg _
        have hc_le : Classical.choose (hJ.gradL2 k) ≤ Ck := le_max_right 0 _
        nlinarith
      have hnonneg : 0 ≤ Real.sqrt (2 * Ck) * ‖X‖ := by positivity
      nlinarith [norm_nonneg
        (toLMH (fun x i => LMPd j (fun y => J k (lmLift X) y i) x)
          (dj_cellL2 hJ k j (lmLift_cellL2 X)))])

lemma opDJ_ae {c : ℝ} (hc : 0 < c) {J : ℕ → LMSpField → LMSpField} (hJ : IsLMMollifier c J)
    (k : ℕ) (j : Fin 2) (X : LMH c) :
    (opDJ c hc J hJ k j X : ℝ × ℝ → EuclideanSpace ℝ (Fin 4)) =ᵐ[volume.restrict (B0579.cell c)]
      fun x => lmReal (fun i => LMPd j (fun y => J k (lmLift X) y i) x) :=
  toLMH_ae (dj_cellL2 hJ k j (lmLift_cellL2 X))

lemma lmLift_opDJ_ae {c : ℝ} (hc : 0 < c) {J : ℕ → LMSpField → LMSpField}
    (hJ : IsLMMollifier c J) (k : ℕ) (j : Fin 2) (X : LMH c) :
    ∀ᵐ x ∂(volume.restrict (B0579.cell c)), ∀ i : Fin 2,
      lmLift (opDJ c hc J hJ k j X) x i = LMPd j (fun y => J k (lmLift X) y i) x :=
  lmLift_toLMH_ae (dj_cellL2 hJ k j (lmLift_cellL2 X))

lemma inner_opDJ_antiSymm {c : ℝ} (hc : 0 < c) {J : ℕ → LMSpField → LMSpField}
    (hJ : IsLMMollifier c J) (k : ℕ) (j : Fin 2) (X Y : LMH c) :
    ⟪opDJ c hc J hJ k j X, Y⟫ = -⟪X, opDJ c hc J hJ k j Y⟫ := by
  rw [inner_lmH_eq_re_lmIp, inner_lmH_eq_re_lmIp]
  rw [lmIp_congr_left (lmLift_opDJ_ae hc hJ k j X), lmIp_congr_right (lmLift_opDJ_ae hc hJ k j Y)]
  have hanti := lmAntiSymm c hc J hJ ⟨hJ.gradL2, hJ.divFreeWeak⟩ k j
    (lmLift X) (lmLift Y) (lmLift_cellL2 X) (lmLift_cellL2 Y)
  rw [hanti, Complex.neg_re, neg_neg]

lemma opDJ_eq_opJ_of_weakPd {c : ℝ} (hc : 0 < c) {J : ℕ → LMSpField → LMSpField}
    (hJ : IsLMMollifier c J) (k : ℕ) (j : Fin 2) {X Xd : LMH c}
    (hw : ∀ i : Fin 2, LMWeakPd c j (fun y => lmLift X y i) (fun y => lmLift Xd y i)) :
    opDJ c hc J hJ k j X = opJ c hc J hJ k Xd := by
  apply Lp.ext_iff.2
  filter_upwards [opDJ_ae hc hJ k j X, opJ_ae hc hJ k Xd] with x h1 h2
  rw [h1, h2]
  congr 1; ext i
  exact hJ.commute k (lmLift X) (lmLift Xd) j (lmLift_cellL2 X) (lmLift_cellL2 Xd) hw i x

lemma opDJ_comm_opJ {c : ℝ} (hc : 0 < c) {J : ℕ → LMSpField → LMSpField}
    (hJ : IsLMMollifier c J) (k m : ℕ) (j : Fin 2) (X : LMH c) :
    opDJ c hc J hJ k j (opJ c hc J hJ m X) = opJ c hc J hJ k (opDJ c hc J hJ m j X) := by
  apply Lp.ext_iff.2
  have hj1 := j_congr_ae hc hJ k (lmLift_cellL2 (opJ c hc J hJ m X))
    (hJ.memL2 m (lmLift X) (lmLift_cellL2 X)) (lmLift_opJ_ae hc hJ m X)
  have hj2 := j_congr_ae hc hJ k (lmLift_cellL2 (opDJ c hc J hJ m j X))
    (dj_cellL2 hJ m j (lmLift_cellL2 X)) (lmLift_opDJ_ae hc hJ m j X)
  have hw : ∀ i : Fin 2, LMWeakPd c j (fun y => J m (lmLift X) y i)
      (fun y => LMPd j (fun z => J m (lmLift X) z i) y) := fun i =>
    lmSmoothWeakPd c hc j _ (hJ.smooth m (lmLift X) (lmLift_cellL2 X) i)
      (fun x => hJ.periodic m (lmLift X) (lmLift_cellL2 X) x i)
      (hJ.memL2 m (lmLift X) (lmLift_cellL2 X) i)
      (dj_cellL2 hJ m j (lmLift_cellL2 X) i)
  filter_upwards [opDJ_ae hc hJ k j (opJ c hc J hJ m X),
    opJ_ae hc hJ k (opDJ c hc J hJ m j X)] with x h1 h2
  rw [h1, h2]
  congr 1; ext i
  have hfun : (fun y => J k (lmLift (opJ c hc J hJ m X)) y i) =
      fun y => J k (J m (lmLift X)) y i := funext fun y => hj1 y i
  rw [hfun, hJ.commute k (J m (lmLift X)) _ j
    (hJ.memL2 m (lmLift X) (lmLift_cellL2 X)) (dj_cellL2 hJ m j (lmLift_cellL2 X)) hw i x,
    hj2 x i]

/-! ### 4. Commutation of `opP0` with `opJ` and `opDJ` -/

lemma opJ_weakDivFree {c : ℝ} (hc : 0 < c) {J : ℕ → LMSpField → LMSpField}
    (hJ : IsLMMollifier c J) (k : ℕ) {X : LMH c} (hdiv : LMWeakDivFree c (lmLift X)) :
    LMWeakDivFree c (lmLift (opJ c hc J hJ k X)) := by
  intro ψ hψ
  have hjdiv := lmJWeakDiv c hc J hJ ⟨hJ.gradL2, hJ.divFreeWeak⟩ k (lmLift X)
    (lmLift_cellL2 X) hdiv ψ hψ
  rw [← hjdiv]
  refine integral_congr_ae ?_
  filter_upwards [lmLift_opJ_ae hc hJ k X] with x hx
  rw [hx 0, hx 1]

lemma opP0_comm_opJ {c : ℝ} (hc : 0 < c) {J : ℕ → LMSpField → LMSpField}
    (hJ : IsLMMollifier c J) (k : ℕ) (X : LMH c) :
    opP0 c hc (opJ c hc J hJ k X) = opJ c hc J hJ k (opP0 c hc X) := by
  apply ext_inner_right ℝ
  intro Y
  have hfixY : opP0 c hc (opJ c hc J hJ k (opP0 c hc Y)) = opJ c hc J hJ k (opP0 c hc Y) :=
    opP0_eq_self_of_weakDivFree hc (opJ_weakDivFree hc hJ k (opP0_weakDivFree hc Y))
  have hfixX : opP0 c hc (opJ c hc J hJ k (opP0 c hc X)) = opJ c hc J hJ k (opP0 c hc X) :=
    opP0_eq_self_of_weakDivFree hc (opJ_weakDivFree hc hJ k (opP0_weakDivFree hc X))
  calc ⟪opP0 c hc (opJ c hc J hJ k X), Y⟫
      = ⟪opJ c hc J hJ k X, opP0 c hc Y⟫ := inner_opP0_selfAdj hc _ _
    _ = ⟪X, opJ c hc J hJ k (opP0 c hc Y)⟫ := inner_opJ_selfAdj hc hJ k _ _
    _ = ⟪X, opP0 c hc (opJ c hc J hJ k (opP0 c hc Y))⟫ := by rw [hfixY]
    _ = ⟪opP0 c hc X, opJ c hc J hJ k (opP0 c hc Y)⟫ := (inner_opP0_selfAdj hc _ _).symm
    _ = ⟪opJ c hc J hJ k (opP0 c hc X), opP0 c hc Y⟫ := (inner_opJ_selfAdj hc hJ k _ _).symm
    _ = ⟪opP0 c hc (opJ c hc J hJ k (opP0 c hc X)), Y⟫ := (inner_opP0_selfAdj hc _ _).symm
    _ = ⟪opJ c hc J hJ k (opP0 c hc X), Y⟫ := by rw [hfixX]

lemma pd_comm_of_smooth {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (i j : Fin 2) (x : ℝ × ℝ) :
    B0579.pd i (B0579.pd j F) x = B0579.pd j (B0579.pd i F) x := by
  have hdf : Differentiable ℝ (fderiv ℝ F) :=
    (hF.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  have h1 : B0579.pd i (B0579.pd j F) x = fderiv ℝ (fderiv ℝ F) x (B0579.dir i) (B0579.dir j) := by
    have ha : HasFDerivAt (B0579.pd j F)
        ((ContinuousLinearMap.apply ℝ ℝ (B0579.dir j)).comp (fderiv ℝ (fderiv ℝ F) x)) x :=
      (ContinuousLinearMap.apply ℝ ℝ (B0579.dir j)).hasFDerivAt.comp x (hdf x).hasFDerivAt
    simp [B0579.pd, ha.fderiv]
  have h2 : B0579.pd j (B0579.pd i F) x = fderiv ℝ (fderiv ℝ F) x (B0579.dir j) (B0579.dir i) := by
    have ha : HasFDerivAt (B0579.pd i F)
        ((ContinuousLinearMap.apply ℝ ℝ (B0579.dir i)).comp (fderiv ℝ (fderiv ℝ F) x)) x :=
      (ContinuousLinearMap.apply ℝ ℝ (B0579.dir i)).hasFDerivAt.comp x (hdf x).hasFDerivAt
    simp [B0579.pd, ha.fderiv]
  rw [h1, h2]
  exact (hF.contDiffAt.isSymmSndFDerivAt (by simp)).eq (B0579.dir i) (B0579.dir j)

lemma lmPd_comm_of_smooth {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ ∞ F) (i j : Fin 2) (x : ℝ × ℝ) :
    LMPd i (LMPd j F) x = LMPd j (LMPd i F) x := by
  have hre : ContDiff ℝ ∞ (fun y => (F y).re) := Complex.reCLM.contDiff.comp hF
  have him : ContDiff ℝ ∞ (fun y => (F y).im) := Complex.imCLM.contDiff.comp hF
  have hre_d : ∀ k : Fin 2, (fun y => (LMPd k F y).re) = B0579.pd k (fun y => (F y).re) :=
    fun k => funext fun y => (lmPd_re k F y).symm
  have him_d : ∀ k : Fin 2, (fun y => (LMPd k F y).im) = B0579.pd k (fun y => (F y).im) :=
    fun k => funext fun y => (lmPd_im k F y).symm
  apply Complex.ext
  · rw [← lmPd_re, ← lmPd_re, hre_d j, hre_d i]
    exact pd_comm_of_smooth hre i j x
  · rw [← lmPd_im, ← lmPd_im, him_d j, him_d i]
    exact pd_comm_of_smooth him i j x

/-- Weak `∂_d`-derivative of a weakly divergence-free cell `L²` field is also weakly div-free. -/
lemma weakDivFree_of_weakPd {c : ℝ} (d : Fin 2) {X Xd : LMH c}
    (hdiv : LMWeakDivFree c (lmLift X))
    (hw : ∀ i : Fin 2, LMWeakPd c d (fun y => lmLift X y i) (fun y => lmLift Xd y i)) :
    LMWeakDivFree c (lmLift Xd) := by
  intro ψ hψ
  have hi_xd : ∀ i : Fin 2, Integrable
      (fun x => lmLift Xd x i * (B0579.pd i ψ x : ℂ))
      (volume.restrict (B0579.cell c)) := fun i => by
    obtain ⟨R, hR⟩ := (hψ.pd i).band
    exact lmSW_integrableOn (R := R) (lmLift_cellL2 Xd i)
      (Complex.continuous_ofReal.comp (hψ.pd i).continuous) (fun x hx => by simp [hR x hx])
  have hi_x : ∀ i : Fin 2, Integrable
      (fun x => lmLift X x i * (B0579.pd d (B0579.pd i ψ) x : ℂ))
      (volume.restrict (B0579.cell c)) := fun i => by
    obtain ⟨R, hR⟩ := ((hψ.pd i).pd d).band
    exact lmSW_integrableOn (R := R) (lmLift_cellL2 X i)
      (Complex.continuous_ofReal.comp ((hψ.pd i).pd d).continuous) (fun x hx => by simp [hR x hx])
  have e0 : ∫ x in B0579.cell c, lmLift Xd x 0 * (B0579.pd 0 ψ x : ℂ) =
      -∫ x in B0579.cell c, lmLift X x 0 * (B0579.pd d (B0579.pd 0 ψ) x : ℂ) := by
    have h := (hw 0).2.2 (B0579.pd 0 ψ) (hψ.pd 0).smooth (hψ.pd 0).periodic (hψ.pd 0).band
    rw [h, neg_neg]
  have e1 : ∫ x in B0579.cell c, lmLift Xd x 1 * (B0579.pd 1 ψ x : ℂ) =
      -∫ x in B0579.cell c, lmLift X x 1 * (B0579.pd d (B0579.pd 1 ψ) x : ℂ) := by
    have h := (hw 1).2.2 (B0579.pd 1 ψ) (hψ.pd 1).smooth (hψ.pd 1).periodic (hψ.pd 1).band
    rw [h, neg_neg]
  rw [integral_add (hi_xd 0) (hi_xd 1), e0, e1, ← neg_add, ← integral_add (hi_x 0) (hi_x 1)]
  have hcomm : ∫ x in B0579.cell c,
      (lmLift X x 0 * (B0579.pd d (B0579.pd 0 ψ) x : ℂ) +
        lmLift X x 1 * (B0579.pd d (B0579.pd 1 ψ) x : ℂ)) =
      ∫ x in B0579.cell c,
      (lmLift X x 0 * (B0579.pd 0 (B0579.pd d ψ) x : ℂ) +
        lmLift X x 1 * (B0579.pd 1 (B0579.pd d ψ) x : ℂ)) := by
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    dsimp only
    rw [pd_comm_of_smooth hψ.smooth d 0 x, pd_comm_of_smooth hψ.smooth d 1 x]
  rw [hcomm, hdiv (B0579.pd d ψ) (hψ.pd d), neg_zero]

lemma opDJ_weakDivFree {c : ℝ} (hc : 0 < c) {J : ℕ → LMSpField → LMSpField}
    (hJ : IsLMMollifier c J) (k : ℕ) (j : Fin 2) {X : LMH c}
    (hdiv : LMWeakDivFree c (lmLift X)) :
    LMWeakDivFree c (lmLift (opDJ c hc J hJ k j X)) := by
  intro ψ hψ
  have hw : ∀ i : Fin 2, LMWeakPd c j (fun y => J k (lmLift X) y i)
      (fun y => LMPd j (fun z => J k (lmLift X) z i) y) := fun i =>
    lmSmoothWeakPd c hc j _ (hJ.smooth k (lmLift X) (lmLift_cellL2 X) i)
      (fun x => hJ.periodic k (lmLift X) (lmLift_cellL2 X) x i)
      (hJ.memL2 k (lmLift X) (lmLift_cellL2 X) i)
      (dj_cellL2 hJ k j (lmLift_cellL2 X) i)
  have hi_dj : ∀ i : Fin 2, Integrable
      (fun x => LMPd j (fun z => J k (lmLift X) z i) x * (B0579.pd i ψ x : ℂ))
      (volume.restrict (B0579.cell c)) := fun i => by
    obtain ⟨R, hR⟩ := (hψ.pd i).band
    exact lmSW_integrableOn (R := R) (dj_cellL2 hJ k j (lmLift_cellL2 X) i)
      (Complex.continuous_ofReal.comp (hψ.pd i).continuous) (fun x hx => by simp [hR x hx])
  have hi_j : ∀ i : Fin 2, Integrable
      (fun x => J k (lmLift X) x i * (B0579.pd j (B0579.pd i ψ) x : ℂ))
      (volume.restrict (B0579.cell c)) := fun i => by
    obtain ⟨R, hR⟩ := ((hψ.pd i).pd j).band
    exact lmSW_integrableOn (R := R) (hJ.memL2 k (lmLift X) (lmLift_cellL2 X) i)
      (Complex.continuous_ofReal.comp ((hψ.pd i).pd j).continuous) (fun x hx => by simp [hR x hx])
  have hcongr : ∫ x in B0579.cell c,
      (lmLift (opDJ c hc J hJ k j X) x 0 * (B0579.pd 0 ψ x : ℂ) +
        lmLift (opDJ c hc J hJ k j X) x 1 * (B0579.pd 1 ψ x : ℂ)) =
      (∫ x in B0579.cell c, LMPd j (fun z => J k (lmLift X) z 0) x * (B0579.pd 0 ψ x : ℂ)) +
      (∫ x in B0579.cell c, LMPd j (fun z => J k (lmLift X) z 1) x * (B0579.pd 1 ψ x : ℂ)) := by
    rw [← integral_add (hi_dj 0) (hi_dj 1)]
    refine integral_congr_ae ?_
    filter_upwards [lmLift_opDJ_ae hc hJ k j X] with x hx
    rw [hx 0, hx 1]
  have e0 : ∫ x in B0579.cell c, LMPd j (fun z => J k (lmLift X) z 0) x * (B0579.pd 0 ψ x : ℂ) =
      -∫ x in B0579.cell c, J k (lmLift X) x 0 * (B0579.pd j (B0579.pd 0 ψ) x : ℂ) := by
    have h := (hw 0).2.2 (B0579.pd 0 ψ) (hψ.pd 0).smooth (hψ.pd 0).periodic (hψ.pd 0).band
    rw [h, neg_neg]
  have e1 : ∫ x in B0579.cell c, LMPd j (fun z => J k (lmLift X) z 1) x * (B0579.pd 1 ψ x : ℂ) =
      -∫ x in B0579.cell c, J k (lmLift X) x 1 * (B0579.pd j (B0579.pd 1 ψ) x : ℂ) := by
    have h := (hw 1).2.2 (B0579.pd 1 ψ) (hψ.pd 1).smooth (hψ.pd 1).periodic (hψ.pd 1).band
    rw [h, neg_neg]
  rw [hcongr, e0, e1, ← neg_add, ← integral_add (hi_j 0) (hi_j 1)]
  have hcomm : ∫ x in B0579.cell c,
      (J k (lmLift X) x 0 * (B0579.pd j (B0579.pd 0 ψ) x : ℂ) +
        J k (lmLift X) x 1 * (B0579.pd j (B0579.pd 1 ψ) x : ℂ)) =
      ∫ x in B0579.cell c,
      (J k (lmLift X) x 0 * (B0579.pd 0 (B0579.pd j ψ) x : ℂ) +
        J k (lmLift X) x 1 * (B0579.pd 1 (B0579.pd j ψ) x : ℂ)) := by
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    dsimp only
    rw [pd_comm_of_smooth hψ.smooth j 0 x, pd_comm_of_smooth hψ.smooth j 1 x]
  rw [hcomm, lmJWeakDiv c hc J hJ ⟨hJ.gradL2, hJ.divFreeWeak⟩ k (lmLift X)
    (lmLift_cellL2 X) hdiv (B0579.pd j ψ) (hψ.pd j), neg_zero]

lemma opP0_comm_opDJ {c : ℝ} (hc : 0 < c) {J : ℕ → LMSpField → LMSpField}
    (hJ : IsLMMollifier c J) (k : ℕ) (j : Fin 2) (X : LMH c) :
    opP0 c hc (opDJ c hc J hJ k j X) = opDJ c hc J hJ k j (opP0 c hc X) := by
  apply ext_inner_right ℝ
  intro Y
  have hfixY : opP0 c hc (opDJ c hc J hJ k j (opP0 c hc Y)) = opDJ c hc J hJ k j (opP0 c hc Y) :=
    opP0_eq_self_of_weakDivFree hc (opDJ_weakDivFree hc hJ k j (opP0_weakDivFree hc Y))
  have hfixX : opP0 c hc (opDJ c hc J hJ k j (opP0 c hc X)) = opDJ c hc J hJ k j (opP0 c hc X) :=
    opP0_eq_self_of_weakDivFree hc (opDJ_weakDivFree hc hJ k j (opP0_weakDivFree hc X))
  calc ⟪opP0 c hc (opDJ c hc J hJ k j X), Y⟫
      = ⟪opDJ c hc J hJ k j X, opP0 c hc Y⟫ := inner_opP0_selfAdj hc _ _
    _ = -⟪X, opDJ c hc J hJ k j (opP0 c hc Y)⟫ := inner_opDJ_antiSymm hc hJ k j _ _
    _ = -⟪X, opP0 c hc (opDJ c hc J hJ k j (opP0 c hc Y))⟫ := by rw [hfixY]
    _ = -⟪opP0 c hc X, opDJ c hc J hJ k j (opP0 c hc Y)⟫ := by rw [← inner_opP0_selfAdj hc]
    _ = ⟪opDJ c hc J hJ k j (opP0 c hc X), opP0 c hc Y⟫ := by
        rw [inner_opDJ_antiSymm hc hJ k j]
    _ = ⟪opP0 c hc (opDJ c hc J hJ k j (opP0 c hc X)), Y⟫ := (inner_opP0_selfAdj hc _ _).symm
    _ = ⟪opDJ c hc J hJ k j (opP0 c hc X), Y⟫ := by rw [hfixX]

/-! ### 5. Smooth cell integration-by-parts dissipation & drift estimates for `J_k² - J_m²` -/

/-- Smooth periodic `H²` field `u` satisfies `Re ⟨∂_j² u, u⟩_{cell} = -∫_{cell} ∑_i ‖∂_j u_i‖²`. -/
lemma smooth_lap_ibp_single {c : ℝ} (hc : 0 < c) (j : Fin 2) {u : LMSpField}
    (hsm : ∀ i : Fin 2, ContDiff ℝ ∞ (fun x => u x i))
    (hsm_d : ∀ i : Fin 2, ContDiff ℝ ∞ (fun x => LMPd j (fun y => u y i) x))
    (hper : ∀ (x : ℝ × ℝ) (i : Fin 2), u (x.1 + c, x.2) i = u x i)
    (hper_d : ∀ (x : ℝ × ℝ) (i : Fin 2),
      LMPd j (fun y => u y i) (x.1 + c, x.2) = LMPd j (fun y => u y i) x)
    (hl2 : LMCellL2 c u)
    (hl2_d : LMCellL2 c (fun x i => LMPd j (fun y => u y i) x))
    (hl2_d2 : LMCellL2 c (fun x i => LMPd j (fun y => LMPd j (fun z => u z i) y) x)) :
    (LMIp c (fun x i => LMPd j (fun y => LMPd j (fun z => u z i) y) x) u).re =
      -∫ x in B0579.cell c, ∑ i : Fin 2, ‖LMPd j (fun y => u y i) x‖ ^ 2 := by
  have hibp : ∀ i : Fin 2,
      ∫ x in B0579.cell c,
          starRingEnd ℂ (LMPd j (fun y => LMPd j (fun z => u z i) y) x) * u x i =
        -∫ x in B0579.cell c,
          starRingEnd ℂ (LMPd j (fun y => u y i) x) * LMPd j (fun y => u y i) x := by
    intro i
    have h := lmSmoothIBP c hc j (fun x => u x i)
      (fun x => LMPd j (fun y => u y i) x) (hsm i) (hsm_d i)
      (fun x => hper x i) (fun x => hper_d x i) (hl2 i) (hl2_d i) (hl2_d i) (hl2_d2 i)
    -- `h` has `conj(u) * ∂_j(∂_j u) = -∫ conj(∂_j u) * ∂_j u`; take complex conjugate!
    have hconj := congrArg (starRingEnd ℂ) h
    rw [← integral_conj, map_neg, ← integral_conj] at hconj
    simpa [map_mul, mul_comm, RingHomCompTriple.comp_apply] using hconj
  unfold LMIp
  rw [integral_finsetSum _ fun i _ => lmIp_integrable hl2_d2 hl2 i, Fin.sum_univ_two,
    hibp 0, hibp 1, ← neg_add, Complex.neg_re, Complex.add_re]
  congr 1
  rw [integral_finsetSum _ fun i _ => lm_sq_integrable (hl2_d i), Fin.sum_univ_two]
  have hre : ∀ i : Fin 2,
      (∫ x in B0579.cell c,
        starRingEnd ℂ (LMPd j (fun y => u y i) x) * LMPd j (fun y => u y i) x).re =
      ∫ x in B0579.cell c, ‖LMPd j (fun y => u y i) x‖ ^ 2 := by
    intro i
    have hre_int : (∫ x in B0579.cell c,
          starRingEnd ℂ (LMPd j (fun y => u y i) x) * LMPd j (fun y => u y i) x).re =
        ∫ x in B0579.cell c,
          (starRingEnd ℂ (LMPd j (fun y => u y i) x) * LMPd j (fun y => u y i) x).re :=
      (integral_re (lmIp_integrable hl2_d hl2_d i)).symm
    rw [hre_int]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    dsimp only
    rw [Complex.mul_re, Complex.conj_re, Complex.conj_im, neg_mul, sub_neg_eq_add,
      Complex.sq_norm, Complex.normSq_apply]
  rw [hre 0, hre 1]

lemma lmPd_smooth_of_smooth {f : ℝ × ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (j : Fin 2) :
    ContDiff ℝ ∞ (LMPd j f) := by
  have heq : LMPd j f = fun x => fderiv ℝ f x (B0579.dir j) :=
    funext fun x => lmPd_eq_fderiv ((hf.differentiable (by simp)) x) j
  rw [heq]
  exact (ContinuousLinearMap.apply ℝ ℂ (B0579.dir j)).contDiff.comp
    (hf.fderiv_right (m := ∞) (by simp))

lemma lmPd_periodic_of_periodic {c : ℝ} {f : ℝ × ℝ → ℂ} (hf : Differentiable ℝ f)
    (hper : ∀ x : ℝ × ℝ, f (x.1 + c, x.2) = f x) (j : Fin 2) (x : ℝ × ℝ) :
    LMPd j f (x.1 + c, x.2) = LMPd j f x := by
  have hpt : ∀ y : ℝ × ℝ, y + (c, (0 : ℝ)) = (y.1 + c, y.2) := fun y => by ext <;> simp
  have hcomp : HasFDerivAt (fun y : ℝ × ℝ => f (y + (c, (0 : ℝ))))
      (fderiv ℝ f (x.1 + c, x.2)) x := by
    have h1 := (hf (x + (c, (0 : ℝ)))).hasFDerivAt.comp x
      ((hasFDerivAt_id x).add_const (c, (0 : ℝ)))
    rwa [hpt x, ContinuousLinearMap.comp_id] at h1
  have heq : (fun y : ℝ × ℝ => f (y + (c, (0 : ℝ)))) = f :=
    funext fun y => by rw [hpt y]; exact hper y
  rw [heq] at hcomp
  rw [lmPd_eq_fderiv (hf (x.1 + c, x.2)) j, lmPd_eq_fderiv (hf x) j, ← hcomp.fderiv]

/-- `L²` viscous dissipation for `V_k - V_m`: on a good slice where `opDJ n j X = opJ n X_j` for
`n ∈ {k, m}`, `⟪∑_j (opJ k (opDJ k j X_j) - opJ m (opDJ m j X_j)), J_k² X - J_m² X⟫ ≤ 0`. -/
lemma inner_viscous_L2_nonpos {c : ℝ} (hc : 0 < c) {J : ℕ → LMSpField → LMSpField}
    (hJ : IsLMMollifier c J) (k m : ℕ) {X : LMH c} {Xd : Fin 2 → LMH c}
    (hw : ∀ j i : Fin 2, LMWeakPd c j (fun y => lmLift X y i) (fun y => lmLift (Xd j) y i)) :
    ⟪∑ j : Fin 2,
        (opJ c hc J hJ k (opDJ c hc J hJ k j (Xd j)) -
          opJ c hc J hJ m (opDJ c hc J hJ m j (Xd j))),
      opJ c hc J hJ k (opJ c hc J hJ k X) - opJ c hc J hJ m (opJ c hc J hJ m X)⟫ ≤ 0 := by
  rw [sum_inner]
  refine Finset.sum_nonpos fun j _ => ?_
  have hcomm_n : ∀ n : ℕ,
      opJ c hc J hJ n (opDJ c hc J hJ n j (Xd j)) =
        opDJ c hc J hJ n j (opDJ c hc J hJ n j X) := fun n => by
    rw [← opDJ_comm_opJ hc hJ n n j (Xd j), ← opDJ_eq_opJ_of_weakPd hc hJ n j (hw j)]
  rw [hcomm_n k, hcomm_n m]
  set f := lmLift X
  have hf : LMCellL2 c f := lmLift_cellL2 X
  let u : LMSpField := fun x i => J k (J k f) x i - J m (J m f) x i
  have hu_sm : ∀ i : Fin 2, ContDiff ℝ ∞ (fun x => u x i) := fun i =>
    (hJ.smooth k _ (hJ.memL2 k f hf) i).sub (hJ.smooth m _ (hJ.memL2 m f hf) i)
  have hu_per : ∀ (x : ℝ × ℝ) (i : Fin 2), u (x.1 + c, x.2) i = u x i := fun x i => by
    simp [u, hJ.periodic k _ (hJ.memL2 k f hf) x i, hJ.periodic m _ (hJ.memL2 m f hf) x i]
  have hu_l2 : LMCellL2 c u := fun i =>
    (hJ.memL2 k _ (hJ.memL2 k f hf) i).sub (hJ.memL2 m _ (hJ.memL2 m f hf) i)
  have hud_eq : ∀ (x : ℝ × ℝ) (i : Fin 2),
      LMPd j (fun y => u y i) x =
        LMPd j (fun y => J k (J k f) y i) x - LMPd j (fun y => J m (J m f) y i) x := fun x i => by
    have hfun : (fun y => u y i) =
        fun y => J k (J k f) y i + (-1 : ℂ) * J m (J m f) y i := by funext y; simp [u]; ring
    rw [hfun, lmPd_add_const_mul
      ((hJ.smooth k _ (hJ.memL2 k f hf) i).differentiable (by simp))
      ((hJ.smooth m _ (hJ.memL2 m f hf) i).differentiable (by simp))]
    ring
  have hud_l2 : LMCellL2 c (fun x i => LMPd j (fun y => u y i) x) := fun i => by
    have h1 := dj_cellL2 hJ k j (hJ.memL2 k f hf) i
    have h2 := dj_cellL2 hJ m j (hJ.memL2 m f hf) i
    have hfun : (fun x => LMPd j (fun y => u y i) x) =
        fun x => LMPd j (fun y => J k (J k f) y i) x - LMPd j (fun y => J m (J m f) y i) x :=
      funext fun x => hud_eq x i
    rw [hfun]; exact h1.sub h2
  have hp2_n : ∀ (n : ℕ) (x : ℝ × ℝ) (i : Fin 2),
      LMPd j (fun y => LMPd j (fun z => J n (J n f) z i) y) x =
        LMPd j (fun y => J n (fun z i' => LMPd j (fun w => J n f w i') z) y i) x := by
    intro n x i
    have hw1 : ∀ i' : Fin 2, LMWeakPd c j (fun z => J n f z i')
        (fun z => LMPd j (fun w => J n f w i') z) := fun i' =>
      lmSmoothWeakPd c hc j _ (hJ.smooth n f hf i') (fun z => hJ.periodic n f hf z i')
        (hJ.memL2 n f hf i') (dj_cellL2 hJ n j hf i')
    have hfun : (fun y => LMPd j (fun z => J n (J n f) z i) y) =
        fun y => J n (fun z i' => LMPd j (fun w => J n f w i') z) y i :=
      funext fun y => hJ.commute n (J n f) _ j (hJ.memL2 n f hf) (dj_cellL2 hJ n j hf) hw1 i y
    rw [hfun]
  have hud2_eq : ∀ (x : ℝ × ℝ) (i : Fin 2),
      LMPd j (fun y => LMPd j (fun z => u z i) y) x =
        LMPd j (fun y => J k (fun z i' => LMPd j (fun w => J k f w i') z) y i) x -
        LMPd j (fun y => J m (fun z i' => LMPd j (fun w => J m f w i') z) y i) x := by
    intro x i
    have hfun : (fun y => LMPd j (fun z => u z i) y) =
        fun y => LMPd j (fun z => J k (J k f) z i) y +
          (-1 : ℂ) * LMPd j (fun z => J m (J m f) z i) y := by
      funext y; rw [hud_eq y i]; ring
    rw [hfun, lmPd_add_const_mul
      ((lmPd_smooth_of_smooth (hJ.smooth k _ (hJ.memL2 k f hf) i) j).differentiable (by simp))
      ((lmPd_smooth_of_smooth (hJ.smooth m _ (hJ.memL2 m f hf) i) j).differentiable (by simp)),
      hp2_n k x i, hp2_n m x i]
    ring
  have hud2_l2 : LMCellL2 c (fun x i => LMPd j (fun y => LMPd j (fun z => u z i) y) x) := fun i => by
    have h1 := dj_cellL2 hJ k j (dj_cellL2 hJ k j hf) i
    have h2 := dj_cellL2 hJ m j (dj_cellL2 hJ m j hf) i
    have hfun : (fun x => LMPd j (fun y => LMPd j (fun z => u z i) y) x) =
        fun x => LMPd j (fun y => J k (fun z i' => LMPd j (fun w => J k f w i') z) y i) x -
          LMPd j (fun y => J m (fun z i' => LMPd j (fun w => J m f w i') z) y i) x :=
      funext fun x => hud2_eq x i
    rw [hfun]; exact h1.sub h2
  have hLHS_ae : ∀ᵐ x ∂(volume.restrict (B0579.cell c)), ∀ i : Fin 2,
      lmLift (opDJ c hc J hJ k j (opDJ c hc J hJ k j X) -
          opDJ c hc J hJ m j (opDJ c hc J hJ m j X)) x i =
        LMPd j (fun y => LMPd j (fun z => u z i) y) x := by
    have hsub : ∀ᵐ x ∂(volume.restrict (B0579.cell c)), ∀ i : Fin 2,
        lmLift (opDJ c hc J hJ k j (opDJ c hc J hJ k j X) -
            opDJ c hc J hJ m j (opDJ c hc J hJ m j X)) x i =
          lmLift (opDJ c hc J hJ k j (opDJ c hc J hJ k j X)) x i -
            lmLift (opDJ c hc J hJ m j (opDJ c hc J hJ m j X)) x i := by
      filter_upwards [Lp.coeFn_sub
        (opDJ c hc J hJ k j (opDJ c hc J hJ k j X))
        (opDJ c hc J hJ m j (opDJ c hc J hJ m j X))] with x hx i
      unfold lmLift; rw [hx, Pi.sub_apply]; fin_cases i <;> simp [lmSp] <;> ring
    have hjk := j_congr_ae hc hJ k (lmLift_cellL2 (opDJ c hc J hJ k j X))
      (dj_cellL2 hJ k j hf) (lmLift_opDJ_ae hc hJ k j X)
    have hjm := j_congr_ae hc hJ m (lmLift_cellL2 (opDJ c hc J hJ m j X))
      (dj_cellL2 hJ m j hf) (lmLift_opDJ_ae hc hJ m j X)
    filter_upwards [hsub,
      lmLift_opDJ_ae hc hJ k j (opDJ c hc J hJ k j X),
      lmLift_opDJ_ae hc hJ m j (opDJ c hc J hJ m j X)] with x hs hk hm i
    rw [hs i, hk i, hm i, hud2_eq x i]
    have hfk : (fun y => J k (lmLift (opDJ c hc J hJ k j X)) y i) =
        fun y => J k (fun z i' => LMPd j (fun w => J k f w i') z) y i := funext fun y => hjk y i
    have hfm : (fun y => J m (lmLift (opDJ c hc J hJ m j X)) y i) =
        fun y => J m (fun z i' => LMPd j (fun w => J m f w i') z) y i := funext fun y => hjm y i
    rw [hfk, hfm]
  have hRHS_ae : ∀ᵐ x ∂(volume.restrict (B0579.cell c)), ∀ i : Fin 2,
      lmLift (opJ c hc J hJ k (opJ c hc J hJ k X) -
          opJ c hc J hJ m (opJ c hc J hJ m X)) x i = u x i := by
    have hsub : ∀ᵐ x ∂(volume.restrict (B0579.cell c)), ∀ i : Fin 2,
        lmLift (opJ c hc J hJ k (opJ c hc J hJ k X) -
            opJ c hc J hJ m (opJ c hc J hJ m X)) x i =
          lmLift (opJ c hc J hJ k (opJ c hc J hJ k X)) x i -
            lmLift (opJ c hc J hJ m (opJ c hc J hJ m X)) x i := by
      filter_upwards [Lp.coeFn_sub
        (opJ c hc J hJ k (opJ c hc J hJ k X))
        (opJ c hc J hJ m (opJ c hc J hJ m X))] with x hx i
      unfold lmLift; rw [hx, Pi.sub_apply]; fin_cases i <;> simp [lmSp] <;> ring
    have hjk := j_congr_ae hc hJ k (lmLift_cellL2 (opJ c hc J hJ k X))
      (hJ.memL2 k f hf) (lmLift_opJ_ae hc hJ k X)
    have hjm := j_congr_ae hc hJ m (lmLift_cellL2 (opJ c hc J hJ m X))
      (hJ.memL2 m f hf) (lmLift_opJ_ae hc hJ m X)
    filter_upwards [hsub,
      lmLift_opJ_ae hc hJ k (opJ c hc J hJ k X),
      lmLift_opJ_ae hc hJ m (opJ c hc J hJ m X)] with x hs hk hm i
    rw [hs i, hk i, hm i, hjk x i, hjm x i]
  rw [inner_lmH_eq_re_lmIp, lmIp_congr_left hLHS_ae, lmIp_congr_right hRHS_ae,
    smooth_lap_ibp_single hc j hu_sm (fun i => lmPd_smooth_of_smooth (hu_sm i) j)
      hu_per (fun x i => lmPd_periodic_of_periodic ((hu_sm i).differentiable (by simp))
        (fun y => hu_per y i) j x) hu_l2 hud_l2 hud2_l2]
  exact neg_nonpos.2 (integral_nonneg fun x => Finset.sum_nonneg fun i _ => sq_nonneg _)

/-- Combined `H¹` viscous + drift estimate for `Vd_k - Vd_m` (`Vd_k = J_k² X_d`):
on a good slice where `X_j` is the weak `∂_j`-derivative of `X` for `j = 0, 1`, for any `Y : LMH c`
and `ν > 0`:
`2 * ⟪ν • ∑_j (opDJ k d (opDJ k j X_j) - opDJ m d (opDJ m j X_j)) - (opDJ k d (opJ k Y) - opDJ m d (opJ m Y)), J_k² X_d - J_m² X_d⟫ ≤ ν⁻¹ * ‖J_k² Y - J_m² Y‖ ^ 2`. -/
lemma inner_viscous_drift_H1_le {c ν : ℝ} (hc : 0 < c) (hν : 0 < ν)
    {J : ℕ → LMSpField → LMSpField} (hJ : IsLMMollifier c J) (k m : ℕ) (d : Fin 2)
    {X : LMH c} {Xd : Fin 2 → LMH c} (Y : LMH c)
    (hw : ∀ j i : Fin 2, LMWeakPd c j (fun y => lmLift X y i) (fun y => lmLift (Xd j) y i)) :
    2 * ⟪ν • (∑ j : Fin 2,
          (opDJ c hc J hJ k d (opDJ c hc J hJ k j (Xd j)) -
            opDJ c hc J hJ m d (opDJ c hc J hJ m j (Xd j)))) -
        (opDJ c hc J hJ k d (opJ c hc J hJ k Y) -
          opDJ c hc J hJ m d (opJ c hc J hJ m Y)),
      opJ c hc J hJ k (opJ c hc J hJ k (Xd d)) -
        opJ c hc J hJ m (opJ c hc J hJ m (Xd d))⟫ ≤
      ν⁻¹ * ‖opJ c hc J hJ k (opJ c hc J hJ k Y) - opJ c hc J hJ m (opJ c hc J hJ m Y)‖ ^ 2 := by
  set W : LMH c :=
    opJ c hc J hJ k (opJ c hc J hJ k (Xd d)) - opJ c hc J hJ m (opJ c hc J hJ m (Xd d))
  set fd : Fin 2 → LMSpField := fun j => lmLift (Xd j)
  have hfd : ∀ j, LMCellL2 c (fd j) := fun j => lmLift_cellL2 (Xd j)
  set f := lmLift X
  have hf : LMCellL2 c f := lmLift_cellL2 X
  let w : LMSpField := fun x i => J k (J k (fd d)) x i - J m (J m (fd d)) x i
  have hw_sm : ∀ i : Fin 2, ContDiff ℝ ∞ (fun x => w x i) := fun i =>
    (hJ.smooth k _ (hJ.memL2 k (fd d) (hfd d)) i).sub
      (hJ.smooth m _ (hJ.memL2 m (fd d) (hfd d)) i)
  have hw_per : ∀ (x : ℝ × ℝ) (i : Fin 2), w (x.1 + c, x.2) i = w x i := fun x i => by
    simp [w, hJ.periodic k _ (hJ.memL2 k (fd d) (hfd d)) x i,
      hJ.periodic m _ (hJ.memL2 m (fd d) (hfd d)) x i]
  have hw_l2 : LMCellL2 c w := fun i =>
    (hJ.memL2 k _ (hJ.memL2 k (fd d) (hfd d)) i).sub
      (hJ.memL2 m _ (hJ.memL2 m (fd d) (hfd d)) i)
  have hwd_eq : ∀ (j : Fin 2) (x : ℝ × ℝ) (i : Fin 2),
      LMPd j (fun y => w y i) x =
        LMPd j (fun y => J k (J k (fd d)) y i) x -
          LMPd j (fun y => J m (J m (fd d)) y i) x := fun j x i => by
    have hfun : (fun y => w y i) =
        fun y => J k (J k (fd d)) y i + (-1 : ℂ) * J m (J m (fd d)) y i := by
      funext y; simp [w]; ring
    rw [hfun, lmPd_add_const_mul
      ((hJ.smooth k _ (hJ.memL2 k (fd d) (hfd d)) i).differentiable (by simp))
      ((hJ.smooth m _ (hJ.memL2 m (fd d) (hfd d)) i).differentiable (by simp))]
    ring
  have hwd_l2 : ∀ j : Fin 2, LMCellL2 c (fun x i => LMPd j (fun y => w y i) x) := fun j i => by
    have h1 := dj_cellL2 hJ k j (hJ.memL2 k (fd d) (hfd d)) i
    have h2 := dj_cellL2 hJ m j (hJ.memL2 m (fd d) (hfd d)) i
    have hfun : (fun x => LMPd j (fun y => w y i) x) =
        fun x => LMPd j (fun y => J k (J k (fd d)) y i) x -
          LMPd j (fun y => J m (J m (fd d)) y i) x :=
      funext fun x => hwd_eq j x i
    rw [hfun]; exact h1.sub h2
  -- Key smooth commutation identity for each fixed index `n` and direction `j`:
  -- `LMPd j (LMPd j (J n (J n (fd d)))) = LMPd d (J n (LMPd j (J n (fd j))))`.
  have hp2_n : ∀ (n : ℕ) (j : Fin 2) (x : ℝ × ℝ) (i : Fin 2),
      LMPd j (fun y => LMPd j (fun z => J n (J n (fd d)) z i) y) x =
        LMPd d (fun y => J n (fun z i' => LMPd j (fun u => J n (fd j) u i') z) y i) x := by
    intro n j x i
    -- 1. `J n (fd d) = LMPd d (J n f)`
    have hc_d : J n (fd d) = fun z i' => LMPd d (fun u => J n f u i') z :=
      funext fun z => funext fun i' => (hJ.commute n f (fd d) d hf (hfd d) (hw d) i' z).symm
    -- 2. `J n (J n (fd d)) = LMPd d (J n (J n f))`
    have hw_Jnf_d : ∀ i' : Fin 2, LMWeakPd c d (fun z => J n f z i')
        (fun z => LMPd d (fun u => J n f u i') z) := fun i' =>
      lmSmoothWeakPd c hc d _ (hJ.smooth n f hf i') (fun z => hJ.periodic n f hf z i')
        (hJ.memL2 n f hf i') (dj_cellL2 hJ n d hf i')
    have hc_dd : ∀ z : ℝ × ℝ, J n (J n (fd d)) z i = LMPd d (fun u => J n (J n f) u i) z := by
      intro z
      rw [hc_d]
      exact (hJ.commute n (J n f) _ d (hJ.memL2 n f hf) (dj_cellL2 hJ n d hf) hw_Jnf_d i z).symm
    -- 3. `J n (fd j) = LMPd j (J n f)` and `J n (LMPd j (J n (fd j))) = LMPd j (LMPd j (J n (J n f)))`
    have hc_j : ∀ u i', J n (fd j) u i' = LMPd j (fun v => J n f v i') u :=
      fun u i' => (hJ.commute n f (fd j) j hf (hfd j) (hw j) i' u).symm
    have hl2_j2 : LMCellL2 c (fun z i' => LMPd j (fun u => J n (fd j) u i') z) :=
      dj_cellL2 hJ n j (hfd j)
    have hw_Jnf_j : ∀ i' : Fin 2, LMWeakPd c j (fun z => J n f z i')
        (fun z => LMPd j (fun u => J n f u i') z) := fun i' =>
      lmSmoothWeakPd c hc j _ (hJ.smooth n f hf i') (fun z => hJ.periodic n f hf z i')
        (hJ.memL2 n f hf i') (dj_cellL2 hJ n j hf i')
    have hw_Jnf_j2 : ∀ i' : Fin 2, LMWeakPd c j (fun z => J n (fd j) z i')
        (fun z => LMPd j (fun u => J n (fd j) u i') z) := fun i' =>
      lmSmoothWeakPd c hc j _ (hJ.smooth n (fd j) (hfd j) i')
        (fun z => hJ.periodic n (fd j) (hfd j) z i')
        (hJ.memL2 n (fd j) (hfd j) i') (hl2_j2 i')
    have hc_jj : ∀ y : ℝ × ℝ,
        J n (fun z i' => LMPd j (fun u => J n (fd j) u i') z) y i =
          LMPd j (fun z => LMPd j (fun u => J n (J n f) u i) z) y := by
      intro y
      rw [← hJ.commute n (J n (fd j)) _ j (hJ.memL2 n (fd j) (hfd j)) hl2_j2 hw_Jnf_j2 i y]
      have hfun_inner : (fun z => J n (J n (fd j)) z i) =
          fun z => LMPd j (fun u => J n (J n f) u i) z := by
        funext z
        have heq_j : J n (fd j) = fun u i' => LMPd j (fun v => J n f v i') u :=
          funext fun u => funext fun i' => hc_j u i'
        rw [heq_j]
        exact (hJ.commute n (J n f) _ j (hJ.memL2 n f hf) (dj_cellL2 hJ n j hf) hw_Jnf_j i z).symm
      rw [hfun_inner]
    -- 4. Commute `LMPd d` past two `LMPd j`'s on the smooth function `J n (J n f) · i`!
    have hsm_Jn2 : ContDiff ℝ ∞ (fun u => J n (J n f) u i) :=
      hJ.smooth n (J n f) (hJ.memL2 n f hf) i
    have hfun_d : (fun z => J n (J n (fd d)) z i) = fun z => LMPd d (fun u => J n (J n f) u i) z :=
      funext hc_dd
    have hfun_jj : (fun y => J n (fun z i' => LMPd j (fun u => J n (fd j) u i') z) y i) =
        fun y => LMPd j (fun z => LMPd j (fun u => J n (J n f) u i) z) y :=
      funext hc_jj
    rw [hfun_d, hfun_jj]
    have hcomm1 : (fun y => LMPd j (fun z => LMPd d (fun u => J n (J n f) u i) z) y) =
        fun y => LMPd d (fun z => LMPd j (fun u => J n (J n f) u i) z) y :=
      funext fun y => lmPd_comm_of_smooth hsm_Jn2 j d y
    rw [hcomm1]
    exact lmPd_comm_of_smooth (lmPd_smooth_of_smooth hsm_Jn2 j) j d x
  have hwd2_eq : ∀ (j : Fin 2) (x : ℝ × ℝ) (i : Fin 2),
      LMPd j (fun y => LMPd j (fun z => w z i) y) x =
        LMPd d (fun y => J k (fun z i' => LMPd j (fun u => J k (fd j) u i') z) y i) x -
          LMPd d (fun y => J m (fun z i' => LMPd j (fun u => J m (fd j) u i') z) y i) x := by
    intro j x i
    have hfun : (fun y => LMPd j (fun z => w z i) y) =
        fun y => LMPd j (fun z => J k (J k (fd d)) z i) y +
          (-1 : ℂ) * LMPd j (fun z => J m (J m (fd d)) z i) y := by
      funext y; rw [hwd_eq j y i]; ring
    rw [hfun, lmPd_add_const_mul
      ((lmPd_smooth_of_smooth (hJ.smooth k _ (hJ.memL2 k (fd d) (hfd d)) i) j).differentiable
        (by simp))
      ((lmPd_smooth_of_smooth (hJ.smooth m _ (hJ.memL2 m (fd d) (hfd d)) i) j).differentiable
        (by simp)),
      hp2_n k j x i, hp2_n m j x i]
    ring
  have hwd2_l2 : ∀ j : Fin 2,
      LMCellL2 c (fun x i => LMPd j (fun y => LMPd j (fun z => w z i) y) x) := fun j i => by
    have h1 := dj_cellL2 hJ k d (dj_cellL2 hJ k j (hfd j)) i
    have h2 := dj_cellL2 hJ m d (dj_cellL2 hJ m j (hfd j)) i
    have hfun : (fun x => LMPd j (fun y => LMPd j (fun z => w z i) y) x) =
        fun x => LMPd d (fun y => J k (fun z i' => LMPd j (fun u => J k (fd j) u i') z) y i) x -
          LMPd d (fun y => J m (fun z i' => LMPd j (fun u => J m (fd j) u i') z) y i) x :=
      funext fun x => hwd2_eq j x i
    rw [hfun]; exact h1.sub h2
  have hW_ae : ∀ᵐ x ∂(volume.restrict (B0579.cell c)), ∀ i : Fin 2, lmLift W x i = w x i := by
    have hsub : ∀ᵐ x ∂(volume.restrict (B0579.cell c)), ∀ i : Fin 2,
        lmLift W x i =
          lmLift (opJ c hc J hJ k (opJ c hc J hJ k (Xd d))) x i -
            lmLift (opJ c hc J hJ m (opJ c hc J hJ m (Xd d))) x i := by
      filter_upwards [Lp.coeFn_sub
        (opJ c hc J hJ k (opJ c hc J hJ k (Xd d)))
        (opJ c hc J hJ m (opJ c hc J hJ m (Xd d)))] with x hx i
      unfold lmLift; rw [hx, Pi.sub_apply]; fin_cases i <;> simp [lmSp] <;> ring
    have hjk := j_congr_ae hc hJ k (lmLift_cellL2 (opJ c hc J hJ k (Xd d)))
      (hJ.memL2 k (fd d) (hfd d)) (lmLift_opJ_ae hc hJ k (Xd d))
    have hjm := j_congr_ae hc hJ m (lmLift_cellL2 (opJ c hc J hJ m (Xd d)))
      (hJ.memL2 m (fd d) (hfd d)) (lmLift_opJ_ae hc hJ m (Xd d))
    filter_upwards [hsub,
      lmLift_opJ_ae hc hJ k (opJ c hc J hJ k (Xd d)),
      lmLift_opJ_ae hc hJ m (opJ c hc J hJ m (Xd d))] with x hs hk hm i
    rw [hs i, hk i, hm i, hjk x i, hjm x i]
  -- Evaluate viscous inner product for each `j`
  have hvisc_j : ∀ j : Fin 2,
      ⟪opDJ c hc J hJ k d (opDJ c hc J hJ k j (Xd j)) -
          opDJ c hc J hJ m d (opDJ c hc J hJ m j (Xd j)), W⟫ =
        -∫ x in B0579.cell c, ∑ i : Fin 2, ‖LMPd j (fun y => w y i) x‖ ^ 2 := by
    intro j
    have hLHS_ae : ∀ᵐ x ∂(volume.restrict (B0579.cell c)), ∀ i : Fin 2,
        lmLift (opDJ c hc J hJ k d (opDJ c hc J hJ k j (Xd j)) -
            opDJ c hc J hJ m d (opDJ c hc J hJ m j (Xd j))) x i =
          LMPd j (fun y => LMPd j (fun z => w z i) y) x := by
      have hsub : ∀ᵐ x ∂(volume.restrict (B0579.cell c)), ∀ i : Fin 2,
          lmLift (opDJ c hc J hJ k d (opDJ c hc J hJ k j (Xd j)) -
              opDJ c hc J hJ m d (opDJ c hc J hJ m j (Xd j))) x i =
            lmLift (opDJ c hc J hJ k d (opDJ c hc J hJ k j (Xd j))) x i -
              lmLift (opDJ c hc J hJ m d (opDJ c hc J hJ m j (Xd j))) x i := by
        filter_upwards [Lp.coeFn_sub
          (opDJ c hc J hJ k d (opDJ c hc J hJ k j (Xd j)))
          (opDJ c hc J hJ m d (opDJ c hc J hJ m j (Xd j)))] with x hx i
        unfold lmLift; rw [hx, Pi.sub_apply]; fin_cases i <;> simp [lmSp] <;> ring
      have hjk := j_congr_ae hc hJ k (lmLift_cellL2 (opDJ c hc J hJ k j (Xd j)))
        (dj_cellL2 hJ k j (hfd j)) (lmLift_opDJ_ae hc hJ k j (Xd j))
      have hjm := j_congr_ae hc hJ m (lmLift_cellL2 (opDJ c hc J hJ m j (Xd j)))
        (dj_cellL2 hJ m j (hfd j)) (lmLift_opDJ_ae hc hJ m j (Xd j))
      filter_upwards [hsub,
        lmLift_opDJ_ae hc hJ k d (opDJ c hc J hJ k j (Xd j)),
        lmLift_opDJ_ae hc hJ m d (opDJ c hc J hJ m j (Xd j))] with x hs hk hm i
      rw [hs i, hk i, hm i, hwd2_eq j x i]
      have hfk : (fun y => J k (lmLift (opDJ c hc J hJ k j (Xd j))) y i) =
          fun y => J k (fun z i' => LMPd j (fun u => J k (fd j) u i') z) y i :=
        funext fun y => hjk y i
      have hfm : (fun y => J m (lmLift (opDJ c hc J hJ m j (Xd j))) y i) =
          fun y => J m (fun z i' => LMPd j (fun u => J m (fd j) u i') z) y i :=
        funext fun y => hjm y i
      rw [hfk, hfm]
    rw [inner_lmH_eq_re_lmIp, lmIp_congr_left hLHS_ae, lmIp_congr_right hW_ae]
    exact smooth_lap_ibp_single hc j hw_sm (fun i => lmPd_smooth_of_smooth (hw_sm i) j)
      hw_per (fun x i => lmPd_periodic_of_periodic ((hw_sm i).differentiable (by simp))
        (fun y => hw_per y i) j x) hw_l2 (hwd_l2 j) (hwd2_l2 j)
  -- Evaluate drift inner product via `lmSmoothIBP` + `lmIp_young`
  set b := lmLift Y
  have hb : LMCellL2 c b := lmLift_cellL2 Y
  let β : LMSpField := fun x i => J k (J k b) x i - J m (J m b) x i
  have hβ_sm : ∀ i : Fin 2, ContDiff ℝ ∞ (fun x => β x i) := fun i =>
    (hJ.smooth k _ (hJ.memL2 k b hb) i).sub (hJ.smooth m _ (hJ.memL2 m b hb) i)
  have hβ_per : ∀ (x : ℝ × ℝ) (i : Fin 2), β (x.1 + c, x.2) i = β x i := fun x i => by
    simp [β, hJ.periodic k _ (hJ.memL2 k b hb) x i, hJ.periodic m _ (hJ.memL2 m b hb) x i]
  have hβ_l2 : LMCellL2 c β := fun i =>
    (hJ.memL2 k _ (hJ.memL2 k b hb) i).sub (hJ.memL2 m _ (hJ.memL2 m b hb) i)
  have hβd_eq : ∀ (x : ℝ × ℝ) (i : Fin 2),
      LMPd d (fun y => β y i) x =
        LMPd d (fun y => J k (J k b) y i) x - LMPd d (fun y => J m (J m b) y i) x := fun x i => by
    have hfun : (fun y => β y i) =
        fun y => J k (J k b) y i + (-1 : ℂ) * J m (J m b) y i := by funext y; simp [β]; ring
    rw [hfun, lmPd_add_const_mul
      ((hJ.smooth k _ (hJ.memL2 k b hb) i).differentiable (by simp))
      ((hJ.smooth m _ (hJ.memL2 m b hb) i).differentiable (by simp))]
    ring
  have hβd_l2 : LMCellL2 c (fun x i => LMPd d (fun y => β y i) x) := fun i => by
    have h1 := dj_cellL2 hJ k d (hJ.memL2 k b hb) i
    have h2 := dj_cellL2 hJ m d (hJ.memL2 m b hb) i
    have hfun : (fun x => LMPd d (fun y => β y i) x) =
        fun x => LMPd d (fun y => J k (J k b) y i) x - LMPd d (fun y => J m (J m b) y i) x :=
      funext fun x => hβd_eq x i
    rw [hfun]; exact h1.sub h2
  have hdrift_ibp :
      ⟪opDJ c hc J hJ k d (opJ c hc J hJ k Y) - opDJ c hc J hJ m d (opJ c hc J hJ m Y), W⟫ =
        -(LMIp c β (fun x i => LMPd d (fun y => w y i) x)).re := by
    have hLHS_ae : ∀ᵐ x ∂(volume.restrict (B0579.cell c)), ∀ i : Fin 2,
        lmLift (opDJ c hc J hJ k d (opJ c hc J hJ k Y) -
            opDJ c hc J hJ m d (opJ c hc J hJ m Y)) x i =
          LMPd d (fun y => β y i) x := by
      have hsub : ∀ᵐ x ∂(volume.restrict (B0579.cell c)), ∀ i : Fin 2,
          lmLift (opDJ c hc J hJ k d (opJ c hc J hJ k Y) -
              opDJ c hc J hJ m d (opJ c hc J hJ m Y)) x i =
            lmLift (opDJ c hc J hJ k d (opJ c hc J hJ k Y)) x i -
              lmLift (opDJ c hc J hJ m d (opJ c hc J hJ m Y)) x i := by
        filter_upwards [Lp.coeFn_sub
          (opDJ c hc J hJ k d (opJ c hc J hJ k Y))
          (opDJ c hc J hJ m d (opJ c hc J hJ m Y))] with x hx i
        unfold lmLift; rw [hx, Pi.sub_apply]; fin_cases i <;> simp [lmSp] <;> ring
      have hjk := j_congr_ae hc hJ k (lmLift_cellL2 (opJ c hc J hJ k Y))
        (hJ.memL2 k b hb) (lmLift_opJ_ae hc hJ k Y)
      have hjm := j_congr_ae hc hJ m (lmLift_cellL2 (opJ c hc J hJ m Y))
        (hJ.memL2 m b hb) (lmLift_opJ_ae hc hJ m Y)
      filter_upwards [hsub,
        lmLift_opDJ_ae hc hJ k d (opJ c hc J hJ k Y),
        lmLift_opDJ_ae hc hJ m d (opJ c hc J hJ m Y)] with x hs hk hm i
      rw [hs i, hk i, hm i, hβd_eq x i]
      have hfk : (fun y => J k (lmLift (opJ c hc J hJ k Y)) y i) =
          fun y => J k (J k b) y i := funext fun y => hjk y i
      have hfm : (fun y => J m (lmLift (opJ c hc J hJ m Y)) y i) =
          fun y => J m (J m b) y i := funext fun y => hjm y i
      rw [hfk, hfm]
    rw [inner_lmH_eq_re_lmIp, lmIp_congr_left hLHS_ae, lmIp_congr_right hW_ae]
    have hibp : ∀ i : Fin 2,
        ∫ x in B0579.cell c, starRingEnd ℂ (LMPd d (fun y => β y i) x) * w x i =
          -∫ x in B0579.cell c, starRingEnd ℂ (β x i) * LMPd d (fun y => w y i) x := fun i => by
      have h := lmSmoothIBP c hc d (fun x => w x i) (fun x => β x i)
        (hw_sm i) (hβ_sm i) (fun x => hw_per x i) (fun x => hβ_per x i)
        (hw_l2 i) (hβ_l2 i) (hwd_l2 d i) (hβd_l2 i)
      have hconj := congrArg (starRingEnd ℂ) h
      rw [← integral_conj, map_neg, ← integral_conj] at hconj
      simpa [map_mul, mul_comm, RingHomCompTriple.comp_apply] using hconj
    unfold LMIp
    rw [integral_finsetSum _ fun i _ => lmIp_integrable hβd_l2 hw_l2 i,
      integral_finsetSum _ fun i _ => lmIp_integrable hβ_l2 (hwd_l2 d) i,
      Fin.sum_univ_two, Fin.sum_univ_two, hibp 0, hibp 1, ← neg_add, Complex.neg_re]
  -- Young's inequality on `LMIp c β (LMPd d w)` with `l = ν⁻¹`
  have hβ_norm : ∫ x in B0579.cell c, ∑ i : Fin 2, ‖β x i‖ ^ 2 =
      ‖opJ c hc J hJ k (opJ c hc J hJ k Y) - opJ c hc J hJ m (opJ c hc J hJ m Y)‖ ^ 2 := by
    have hY_ae : ∀ᵐ x ∂(volume.restrict (B0579.cell c)), ∀ i : Fin 2,
        lmLift (opJ c hc J hJ k (opJ c hc J hJ k Y) -
            opJ c hc J hJ m (opJ c hc J hJ m Y)) x i = β x i := by
      have hsub : ∀ᵐ x ∂(volume.restrict (B0579.cell c)), ∀ i : Fin 2,
          lmLift (opJ c hc J hJ k (opJ c hc J hJ k Y) -
              opJ c hc J hJ m (opJ c hc J hJ m Y)) x i =
            lmLift (opJ c hc J hJ k (opJ c hc J hJ k Y)) x i -
              lmLift (opJ c hc J hJ m (opJ c hc J hJ m Y)) x i := by
        filter_upwards [Lp.coeFn_sub
          (opJ c hc J hJ k (opJ c hc J hJ k Y))
          (opJ c hc J hJ m (opJ c hc J hJ m Y))] with x hx i
        unfold lmLift; rw [hx, Pi.sub_apply]; fin_cases i <;> simp [lmSp] <;> ring
      have hjk := j_congr_ae hc hJ k (lmLift_cellL2 (opJ c hc J hJ k Y))
        (hJ.memL2 k b hb) (lmLift_opJ_ae hc hJ k Y)
      have hjm := j_congr_ae hc hJ m (lmLift_cellL2 (opJ c hc J hJ m Y))
        (hJ.memL2 m b hb) (lmLift_opJ_ae hc hJ m Y)
      filter_upwards [hsub,
        lmLift_opJ_ae hc hJ k (opJ c hc J hJ k Y),
        lmLift_opJ_ae hc hJ m (opJ c hc J hJ m Y)] with x hs hk hm i
      rw [hs i, hk i, hm i, hjk x i, hjm x i]
    rw [norm_lmH_sq_eq_integral]
    refine integral_congr_ae ?_
    filter_upwards [hY_ae] with x hx
    exact Finset.sum_congr rfl fun i _ => by rw [hx i]
  rw [inner_sub_left, real_inner_smul_left, sum_inner, Fin.sum_univ_two,
    hvisc_j 0, hvisc_j 1, hdrift_ibp, sub_neg_eq_add]
  set D0 : ℝ := ∫ x in B0579.cell c, ∑ i : Fin 2, ‖LMPd 0 (fun y => w y i) x‖ ^ 2
  set D1 : ℝ := ∫ x in B0579.cell c, ∑ i : Fin 2, ‖LMPd 1 (fun y => w y i) x‖ ^ 2
  have hD0_nn : 0 ≤ D0 := integral_nonneg fun x => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hD1_nn : 0 ≤ D1 := integral_nonneg fun x => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hDd_le : ∫ x in B0579.cell c, ∑ i : Fin 2, ‖LMPd d (fun y => w y i) x‖ ^ 2 ≤ D0 + D1 := by
    fin_cases d
    · change D0 ≤ D0 + D1; linarith
    · change D1 ≤ D0 + D1; linarith
  have hre_le : (LMIp c β (fun x i => LMPd d (fun y => w y i) x)).re ≤
      ‖LMIp c β (fun x i => LMPd d (fun y => w y i) x)‖ := Complex.re_le_norm _
  have hdiv_ν : 2 * ‖LMIp c β (fun x i => LMPd d (fun y => w y i) x)‖ ≤
      ν⁻¹ * ‖opJ c hc J hJ k (opJ c hc J hJ k Y) - opJ c hc J hJ m (opJ c hc J hJ m Y)‖ ^ 2 +
        ν * ∫ x in B0579.cell c, ∑ i : Fin 2, ‖LMPd d (fun y => w y i) x‖ ^ 2 := by
    have hy := lmIp_young hβ_l2 (hwd_l2 d) (inv_pos.2 hν)
    rw [hβ_norm] at hy
    have hm := mul_le_mul_of_nonneg_left hy hν.le
    have hlhs : ν * (2 * ν⁻¹ * ‖LMIp c β (fun x i => LMPd d (fun y => w y i) x)‖) =
        2 * ‖LMIp c β (fun x i => LMPd d (fun y => w y i) x)‖ := by field_simp [hν.ne']
    have hrhs : ν * (ν⁻¹ ^ 2 *
        ‖opJ c hc J hJ k (opJ c hc J hJ k Y) - opJ c hc J hJ m (opJ c hc J hJ m Y)‖ ^ 2 +
        ∫ x in B0579.cell c, ∑ i : Fin 2, ‖LMPd d (fun y => w y i) x‖ ^ 2) =
      ν⁻¹ * ‖opJ c hc J hJ k (opJ c hc J hJ k Y) - opJ c hc J hJ m (opJ c hc J hJ m Y)‖ ^ 2 +
        ν * ∫ x in B0579.cell c, ∑ i : Fin 2, ‖LMPd d (fun y => w y i) x‖ ^ 2 := by
      field_simp [hν.ne']
    linarith
  nlinarith

end UnforcedLeray.Short.IIb.HorizonGluingAux
