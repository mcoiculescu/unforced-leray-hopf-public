import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_2.Quad2.Defs
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1.CylMemLp
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1.EFar
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1.SliceBridge
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_1.ProdHom.Bound
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_5_1_1_3_2.Jets
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_7_2.InletWeak
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1.GradEq.GEQuadSub.GEQMem.Ddu

/-!
# Global `L^{q₀}` bound on `D³e` and `L^∞` bound on `De` (`PartIII-b:C/ward/12/3/2/2/4`)

Source `the November 2 reference manuscript`,
lines 2381-2387, 2542-2551, 2552-2559.

Combines the proved far-field homogeneity `inletEFarHom` (`EFar.lean`), near-axis jet bound
`inletENearJets` (`Jets.lean`), slice bridge `sliceBridge` (`SliceBridge.lean`), and cylindrical
profile integrability `cylProfile_memLp` (`CylMemLp.lean`) to prove that all third partial
derivatives `∂_m∂_l∂_j(p.eFun (p.coord z))` belong to `L^{q₀}` on the phase cell, and uses
`inlet_jetBdd` (`InletWeak.lean`) to bound `∂_j(p.eFun (p.coord z))` uniformly on `ℝ × ℝ³`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace MeasureTheory Set
open scoped ContDiff ENNReal
open UnforcedLeray.Cons.C03.Concrete (Params)

/-- Global `L^{q₀}` integrability of third derivatives and `L^∞` bound of first derivatives of the
affine inlet `e = p.eFun (p.coord z)` on the period cell (source 2381-2387, 2552-2559). -/
def GEQInletD3Global : Prop := GERegime fun p z _ => ∀ j l m : Fin 3,
  MemLp (fun x : ℝ × UnforcedLeray.Space =>
      dy m (dy l (dy j (p.eFun (p.coord z)))) x)
    UnforcedLeray.B0412.q0E
    ((volume.restrict (Ioc (0 : ℝ) p.period)).prod volume) ∧
  ∃ C : ℝ, ∀ x, ‖dy j (p.eFun (p.coord z)) x‖ ≤ C

namespace Quad2InletSub

theorem eFun_eq_linComb (p : Params) (α : Fin 2 → ℝ) :
    p.eFun α = fun x => α 0 • p.Efun 0 x + α 1 • p.Efun 1 x := by
  funext x
  ext k
  simp [Params.eFun, Params.Efun, Fin.sum_univ_two, UnforcedLeray.B0412.realC_apply,
    Complex.real_smul]

theorem dy1_linComb {f g : ℝ × UnforcedLeray.Space → CVec3}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (a b : ℝ) (j : Fin 3) :
    dy j (fun x => a • f x + b • g x) = fun x => a • dy j f x + b • dy j g x := by
  have df := hf.differentiable (by simp)
  have dg := hg.differentiable (by simp)
  have ha : dy j (a • f) = fun x => a • dy j f x := dy_smul' df a j
  have hb : dy j (b • g) = fun x => b • dy j g x := dy_smul' dg b j
  change dy j (fun x => (a • f) x + (b • g) x) = _
  rw [dy_add' (df.const_smul a) (dg.const_smul b) j, ha, hb]

theorem dy3_linComb {f g : ℝ × UnforcedLeray.Space → CVec3}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (a b : ℝ) (j l m : Fin 3) :
    dy m (dy l (dy j (fun x => a • f x + b • g x))) =
      fun x => a • dy m (dy l (dy j f)) x + b • dy m (dy l (dy j g)) x := by
  have hdf1 := contDiff_dy' hf j
  have hdg1 := contDiff_dy' hg j
  have hdf2 := contDiff_dy' hdf1 l
  have hdg2 := contDiff_dy' hdg1 l
  rw [dy1_linComb hf hg a b j, dy1_linComb hdf1 hdg1 a b l, dy1_linComb hdf2 hdg2 a b m]

theorem efun_d3_memLp_col : GERegime fun p _ _ => ∀ (i : Fin 2) (j l m : Fin 3),
    MemLp (dy m (dy l (dy j (p.Efun i)))) UnforcedLeray.B0412.q0E
      ((volume.restrict (Ioc (0 : ℝ) p.period)).prod volume) := by
  intro lam q hq dm dp hdm
  obtain ⟨ν1, hν1, Hfar⟩ := inletEFarHom lam q hq dm dp hdm
  obtain ⟨ν2, hν2, Hnear⟩ := inletENearJets lam q hq dm dp hdm
  refine ⟨min 1 (min ν1 ν2), lt_min one_pos (lt_min hν1 hν2), ?_⟩
  intro p d hreg hν hmode z g hd i j l m
  have e0 : p.ν ≤ 1 := hν.trans (min_le_left _ _)
  have e1 : p.ν ≤ ν1 := hν.trans ((min_le_right _ _).trans (min_le_left _ _))
  have e2 : p.ν ≤ ν2 := hν.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨Cf, R0, hR0, hfar⟩ := Hfar p d hreg e1 hmode z g hd i 2
  set R1 := max R0 1 with hR1_def
  have hR1 : 0 < R1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨Cn, hnear⟩ := Hnear p d hreg e2 hmode z g hd i 2 R1 hR1
  have hI := inlet_contDiff_joint lam q hq hreg e0 hmode i
  have hE : ContDiff ℝ ∞ (p.Efun i) := contDiff_realC.comp hI
  have hD3 : ContDiff ℝ ∞ (dy m (dy l (dy j (p.Efun i)))) :=
    contDiff_dyT (contDiff_dyT (contDiff_dyT hE j) l) m
  set C := max (max Cf Cn) 0 with hC_def
  have hC0 : 0 ≤ C := le_max_right _ _
  have hCfC : Cf ≤ C := (le_max_left _ _).trans (le_max_left _ _)
  have hCnC : Cn ≤ C := (le_max_right _ _).trans (le_max_left _ _)
  have hbd : ∀ τ ∈ Ioc (0 : ℝ) p.period, ∀ y : UnforcedLeray.Space,
      ‖dy m (dy l (dy j (p.Efun i))) (τ, y)‖ ≤ C * cylProfile R1 y := by
    intro τ hτ y
    have hsb := (sliceBridge CVec3 (p.Efun i) univ isOpen_univ hE.contDiffOn (τ, y) trivial m l j).2.2
    unfold cylProfile
    by_cases hy : Real.sqrt (y 0 ^ 2 + y 1 ^ 2) ≤ R1
    · simp only [hy, ↓reduceIte]
      have h1 := (hnear τ hτ y hy).1 3 (by norm_num)
      have hpos : 0 ≤ (1 + |y 2|) ^ (-2 : ℝ) := Real.rpow_nonneg (by positivity) _
      exact hsb.trans (h1.trans (by simpa using mul_le_mul_of_nonneg_right hCnC hpos))
    · simp only [hy, ↓reduceIte]
      have hy' : R1 < Real.sqrt (y 0 ^ 2 + y 1 ^ 2) := not_le.mp hy
      have hyR0 : R0 < UnforcedLeray.Axi.ϱ y :=
        lt_of_le_of_lt (le_max_left _ _) hy'
      have hy1 : 1 ≤ UnforcedLeray.Axi.ϱ y :=
        (le_max_right R0 1).trans hy'.le
      have hs1 : 1 ≤ 1 + |y 2| / UnforcedLeray.Axi.ϱ y := by
        have : 0 ≤ |y 2| / UnforcedLeray.Axi.ϱ y := div_nonneg (abs_nonneg _) (by linarith)
        linarith
      have hf3 := hfar τ y hyR0 3 (by norm_num)
      have hpos_f : 0 ≤ UnforcedLeray.Axi.ϱ y ^ (-(1 + ((3 : ℕ) : ℝ))) *
          (1 + |y 2| / UnforcedLeray.Axi.ϱ y) ^ (-((2 : ℕ) : ℝ)) := by
        have : 0 < UnforcedLeray.Axi.ϱ y := by linarith
        positivity
      have hf3' : ‖iteratedFDeriv ℝ 3 (fun x => p.Efun i (τ, x)) y‖ ≤
          C * (UnforcedLeray.Axi.ϱ y ^ (-(1 + ((3 : ℕ) : ℝ))) *
            (1 + |y 2| / UnforcedLeray.Axi.ϱ y) ^ (-((2 : ℕ) : ℝ))) :=
        hf3.trans (mul_le_mul_of_nonneg_right hCfC hpos_f)
      exact ProdHom.single_bound
        ‖dy m (dy l (dy j (p.Efun i))) (τ, y)‖ C (UnforcedLeray.Axi.ϱ y)
        (1 + |y 2| / UnforcedLeray.Axi.ϱ y) 2 le_rfl hy1 hs1 hC0 (hsb.trans hf3')
  have hμ : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) p.period)) := ⟨by simp⟩
  have hg1 : MemLp (fun x : ℝ × UnforcedLeray.Space => C * cylProfile R1 x.2)
      UnforcedLeray.B0412.q0E
      ((volume.restrict (Ioc (0 : ℝ) p.period)).prod volume) :=
    ((cylProfile_memLp R1 hR1).const_mul C).comp_snd (volume.restrict (Ioc (0 : ℝ) p.period))
  refine hg1.mono' hD3.continuous.aestronglyMeasurable ?_
  have hae : ∀ᵐ x ∂((volume.restrict (Ioc (0 : ℝ) p.period)).prod
      (volume : Measure UnforcedLeray.Space)), x.1 ∈ Ioc (0 : ℝ) p.period :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioc)
  filter_upwards [hae] with x hx
  exact hbd x.1 hx x.2

end Quad2InletSub

/-- **`gEQInletD3Global : GEQInletD3Global`** (source 2381-2387, 2542-2551, 2552-2559). -/
theorem gEQInletD3Global : GEQInletD3Global := by
  intro lam q hq dm dp hdm
  obtain ⟨ν1, hν1, H1⟩ := Quad2InletSub.efun_d3_memLp_col lam q hq dm dp hdm
  refine ⟨min 1 ν1, lt_min one_pos hν1, ?_⟩
  intro p d hreg hν hmode z g hd j l m
  have e0 : p.ν ≤ 1 := hν.trans (min_le_left _ _)
  have e1 : p.ν ≤ ν1 := hν.trans (min_le_right _ _)
  have hI0 := inlet_contDiff_joint lam q hq hreg e0 hmode 0
  have hI1 := inlet_contDiff_joint lam q hq hreg e0 hmode 1
  have hE0 : ContDiff ℝ ∞ (p.Efun 0) := contDiff_realC.comp hI0
  have hE1 : ContDiff ℝ ∞ (p.Efun 1) := contDiff_realC.comp hI1
  refine ⟨?_, ?_⟩
  · have hM0 := H1 p d hreg e1 hmode z g hd 0 j l m
    have hM1 := H1 p d hreg e1 hmode z g hd 1 j l m
    have heq : (fun x : ℝ × UnforcedLeray.Space =>
        dy m (dy l (dy j (p.eFun (p.coord z)))) x) =
        fun x => p.coord z 0 • dy m (dy l (dy j (p.Efun 0))) x +
          p.coord z 1 • dy m (dy l (dy j (p.Efun 1))) x := by
      rw [Quad2InletSub.eFun_eq_linComb]
      exact Quad2InletSub.dy3_linComb hE0 hE1 (p.coord z 0) (p.coord z 1) j l m
    rw [heq]
    exact (hM0.const_smul (p.coord z 0)).add (hM1.const_smul (p.coord z 1))
  · obtain ⟨C0, -, b0, -⟩ := inlet_jetBdd hq hreg e0 hmode 0
    obtain ⟨C1, -, b1, -⟩ := inlet_jetBdd hq hreg e0 hmode 1
    have hEf : ∀ i : Fin 2, p.Efun i =
        fun x => efarRealCLI.toContinuousLinearMap (p.inlet i x.1 x.2) := fun _ => rfl
    have hd0 : dy j (p.Efun 0) =
        fun x => efarRealCLI (dy j (fun x => p.inlet 0 x.1 x.2) x) := by
      rw [hEf 0]
      exact dy_clm efarRealCLI.toContinuousLinearMap (hI0.differentiable (by simp)) j
    have hd1 : dy j (p.Efun 1) =
        fun x => efarRealCLI (dy j (fun x => p.inlet 1 x.1 x.2) x) := by
      rw [hEf 1]
      exact dy_clm efarRealCLI.toContinuousLinearMap (hI1.differentiable (by simp)) j
    have heq1 : dy j (p.eFun (p.coord z)) =
        fun x => p.coord z 0 • dy j (p.Efun 0) x + p.coord z 1 • dy j (p.Efun 1) x := by
      rw [Quad2InletSub.eFun_eq_linComb]
      exact Quad2InletSub.dy1_linComb hE0 hE1 (p.coord z 0) (p.coord z 1) j
    refine ⟨|p.coord z 0| * C0 + |p.coord z 1| * C1, fun x => ?_⟩
    rw [heq1]
    calc ‖p.coord z 0 • dy j (p.Efun 0) x + p.coord z 1 • dy j (p.Efun 1) x‖
        ≤ ‖p.coord z 0 • dy j (p.Efun 0) x‖ + ‖p.coord z 1 • dy j (p.Efun 1) x‖ :=
          norm_add_le _ _
      _ = |p.coord z 0| * ‖dy j (p.Efun 0) x‖ + |p.coord z 1| * ‖dy j (p.Efun 1) x‖ := by
          simp [norm_smul]
      _ ≤ |p.coord z 0| * C0 + |p.coord z 1| * C1 := by
          rw [hd0, hd1, efarRealCLI.norm_map, efarRealCLI.norm_map]
          exact add_le_add
            (mul_le_mul_of_nonneg_left (b0 j x) (abs_nonneg _))
            (mul_le_mul_of_nonneg_left (b1 j x) (abs_nonneg _))

end UnforcedLeray.Short.PartIIIb.Concrete
