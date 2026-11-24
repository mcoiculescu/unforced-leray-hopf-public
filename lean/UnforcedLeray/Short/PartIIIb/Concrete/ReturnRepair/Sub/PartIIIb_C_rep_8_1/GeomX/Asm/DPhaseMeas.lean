import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_8_1.GeomX.Asm.Assembly
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_3_1.Sub.T8_1

/-!
# `PartIII-b:C/rep/8/1/1/1/asm/3`: joint measurability of the phase part on the clear region

Source `the November 2 reference manuscript`
lines 4171-4186.  Deterministic measure theory: `dPhaseMeas_of`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

namespace GeomXAsm.DPhaseMeasAux

open scoped Classical in
lemma measurable_fderiv_apply_on {F : ℝ → Space → Space} {S : Set Space} (hS : MeasurableSet S)
    (hF : Measurable fun p : ℝ × Space => F p.1 p.2)
    (hd : ∀ τ y, y ∈ S → DifferentiableAt ℝ (F τ) y) (v : Space) :
    Measurable fun p : ℝ × Space => if p.2 ∈ S then fderiv ℝ (F p.1) p.2 v else 0 := by
  have hq : ∀ n : ℕ, Measurable fun p : ℝ × Space =>
      if p.2 ∈ S then ((n : ℝ) + 1) • (F p.1 (p.2 + ((n : ℝ) + 1)⁻¹ • v) - F p.1 p.2)
      else (0 : Space) := by
    intro n
    have hsum : Measurable fun p : ℝ × Space => p.2 + ((n : ℝ) + 1)⁻¹ • v :=
      measurable_snd.add measurable_const
    have hA : Measurable fun p : ℝ × Space => F p.1 (p.2 + ((n : ℝ) + 1)⁻¹ • v) :=
      hF.comp (measurable_fst.prodMk hsum)
    have hS' : MeasurableSet {p : ℝ × Space | p.2 ∈ S} := measurable_snd hS
    exact Measurable.ite hS' ((hA.sub hF).const_smul (((n : ℝ) + 1))) measurable_const
  have hc : Tendsto (fun n : ℕ => ‖((n : ℝ) + 1)‖) atTop atTop := by
    have h1 : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    exact h1.congr (fun n => (Real.norm_of_nonneg (by positivity)).symm)
  refine measurable_of_tendsto_metrizable hq ?_
  rw [tendsto_pi_nhds]
  intro p
  by_cases hp : p.2 ∈ S
  · simp only [if_pos hp]
    exact (hd p.1 p.2 hp).hasFDerivAt.lim (c := fun n : ℕ => (n : ℝ) + 1) v hc
  · simp only [if_neg hp]
    exact tendsto_const_nhds

/-- The operator with columns `w j`. -/
def Gf (w : Fin 3 → Space) : Space →L[ℝ] Space :=
  ∑ j : Fin 3, (EuclideanSpace.proj j : Space →L[ℝ] ℝ).smulRight (w j)

lemma Gf_apply (w : Fin 3 → Space) (v : Space) : Gf w v = ∑ j, v j • w j := by
  simp [Gf]

lemma continuous_Gf : Continuous Gf := by
  let Φ : (Fin 3 → Space) →ₗ[ℝ] (Space →L[ℝ] Space) :=
    { toFun := Gf
      map_add' := fun a b => by
        ext v : 1
        simp [Gf_apply, smul_add, Finset.sum_add_distrib]
      map_smul' := fun c a => by
        ext v : 1
        simp [Gf_apply, Finset.smul_sum, smul_comm c] }
  exact LinearMap.continuous_of_finiteDimensional Φ

lemma Gf_coord (L : Space →L[ℝ] Space) : Gf (fun j => L (coordinateVector j)) = L := by
  ext v : 1
  rw [Gf_apply]
  have hv : v = ∑ j : Fin 3, v j • coordinateVector j := by
    ext k
    fin_cases k <;> simp [coordinateVector, Fin.sum_univ_three, EuclideanSpace.single_apply]
  conv_rhs => rw [hv]
  simp [map_sum]

lemma measurable_thinG (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel)
    (T : LStr Pl K L) : Measurable (thinG Pl K L T) := by
  unfold thinG
  have h1 := (Lp.stronglyMeasurable
    ((chiOStr (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.hχo (thinPart T)).fst)).measurable
  have h2 := (Lp.stronglyMeasurable
    ((chiOStr (cOf L.ν) K.mZ (L.ρb Pl K) (gRate Pl) L.ν K.hχo (thinPart T)).snd)).measurable
  exact h1.add h2

lemma measurable_meanQ (c : ℝ) {g : Chart → Ten3} (hg : Measurable g) :
    Measurable (meanQ c g) := by
  unfold meanQ
  have hm : Measurable fun x : Chart × ℝ => g (x.1.1, (x.2, x.1.2.2)) :=
    hg.comp ((measurable_fst.comp measurable_fst).prodMk
      (measurable_snd.prodMk (measurable_snd.comp (measurable_snd.comp measurable_fst))))
  have h : StronglyMeasurable fun p : Chart => ∫ q in Ico (-c / 2) (c / 2), g (p.1, (q, p.2.2)) :=
    StronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ico (-c / 2) (c / 2)))
      (f := fun x : Chart × ℝ => g (x.1.1, (x.2, x.1.2.2))) hm.stronglyMeasurable
  exact h.measurable.const_smul c⁻¹

lemma dPhase_measurable (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (μ : ℝ)
    (hR : ZRegularAt Pl K L μ) (T : LStr Pl K L) :
    Measurable fun p : ℝ × Space =>
      (clearSet L.ε L.ν).indicator (fun y => dPhase Pl K L μ T p.1 y) p.2 := by
  classical
  have hS : IsOpen (clearSet L.ε L.ν) := isOpen_clearSet _ _
  have hg := measurable_thinG Pl K L T
  have hgm := measurable_meanQ (cOf L.ν) hg
  have hA : Measurable fun p : ℝ × Space => zAct Pl K L μ T p.1 p.2 :=
    wardX0_measurable_of_measurable _ _ _ _ _ hg
  have hM : Measurable fun p : ℝ × Space => zMid Pl K L μ T p.1 p.2 :=
    wardX0_measurable_of_measurable _ _ _ _ _ hgm
  have hdA : ∀ τ y, y ∈ clearSet L.ε L.ν → DifferentiableAt ℝ (zAct Pl K L μ T τ) y := by
    intro τ y hy
    have h := (hR T τ).1 (zAct Pl K L μ T) (by simp)
    exact (h.differentiableOn one_ne_zero).differentiableAt (hS.mem_nhds hy)
  have hdM : ∀ τ y, y ∈ clearSet L.ε L.ν → DifferentiableAt ℝ (zMid Pl K L μ T τ) y := by
    intro τ y hy
    have h := (hR T τ).1 (zMid Pl K L μ T) (by simp)
    exact (h.differentiableOn one_ne_zero).differentiableAt (hS.mem_nhds hy)
  have hj : ∀ j : Fin 3, Measurable fun p : ℝ × Space =>
      if p.2 ∈ clearSet L.ε L.ν then
        (fderiv ℝ (zAct Pl K L μ T p.1) p.2 - fderiv ℝ (zMid Pl K L μ T p.1) p.2)
          (coordinateVector j) else 0 := by
    intro j
    have := (measurable_fderiv_apply_on hS.measurableSet hA hdA (coordinateVector j)).sub
      (measurable_fderiv_apply_on hS.measurableSet hM hdM (coordinateVector j))
    convert this using 1
    funext p
    by_cases hp : p.2 ∈ clearSet L.ε L.ν <;> simp [hp]
  have hnorm : Measurable fun p : ℝ × Space =>
      ‖Gf (fun j => if p.2 ∈ clearSet L.ε L.ν then
        (fderiv ℝ (zAct Pl K L μ T p.1) p.2 - fderiv ℝ (zMid Pl K L μ T p.1) p.2)
          (coordinateVector j) else 0)‖ :=
    continuous_norm.measurable.comp (continuous_Gf.measurable.comp (measurable_pi_lambda _ hj))
  convert hnorm using 1
  funext p
  by_cases hp : p.2 ∈ clearSet L.ε L.ν
  · rw [Set.indicator_of_mem hp]
    simp only [if_pos hp]
    rw [Gf_coord]
    rfl
  · rw [Set.indicator_of_notMem hp]
    simp only [if_neg hp]
    have : Gf (fun _ => (0 : Space)) = 0 := by
      ext v : 1
      simp [Gf_apply]
    rw [this]
    simp

end GeomXAsm.DPhaseMeasAux

open GeomXAsm.DPhaseMeasAux in
/-- **`DPhaseMeas` from `ZRegular`** (source 4171-4186). -/
theorem dPhaseMeas_of (D : SeqData) (hR : D.ZRegular) : D.DPhaseMeas := by
  filter_upwards [hR] with n hn z hz T
  exact dPhase_measurable D.Pl D.K (D.level n) (D.mu n z) (hn z hz) T

end UnforcedLeray.Short.PartIIIb.Concrete
