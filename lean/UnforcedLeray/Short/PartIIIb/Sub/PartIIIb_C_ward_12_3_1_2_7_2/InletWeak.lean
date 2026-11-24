import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_7_2.InletWeak.Calc
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_7_2.InletWeak.Bounds

/-!
# `gEQInletWeak` (source 2385-2387, 2525-2531)

For the affine inlet `e = realC (∑ αᵢ Eᵢ)`: `Eᵢ` is jointly smooth (ring lift of the smooth
cutoff stream, `NicePT.contDiff_Nv`) with bounded slice jets (`IIb.inlet_jet_bound_per`, the
per-parameter form of `InletJetBound`; the `GradEq` regime fixes `ν₀` before `p`, so no
age-cutoff-dependent threshold is available, and none is needed since bounds may depend on `p`).
Weak `y_j`-derivatives are classical (`weakDyS_of_smooth`); the second one uses
`dy_dy_comm`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace MeasureTheory Set
open UnforcedLeray.Cons.C03.Concrete (Params)
open scoped ContDiff

local notation "𝕊" => UnforcedLeray.Space

/-- `realC` as a continuous real-linear map. -/
private def realCL : 𝕊 →L[ℝ] CVec3 :=
  LinearMap.toContinuousLinearMap
    { toFun := UnforcedLeray.B0412.realC
      map_add' := fun x y => by
        ext i; simp [UnforcedLeray.B0412.realC_apply]
      map_smul' := fun c x => by
        ext i; simp [UnforcedLeray.B0412.realC_apply] }

private theorem realCL_apply (x : 𝕊) (i : Fin 3) : realCL x i = ((x i : ℝ) : ℂ) :=
  UnforcedLeray.B0412.realC_apply x i

/-- Coordinate `i` of a `Space`-valued field, as a continuous real-linear map into `ℂ`. -/
private def coordCL (i : Fin 3) : 𝕊 →L[ℝ] ℂ := Complex.ofRealCLM.comp (EuclideanSpace.proj i)

private theorem coordCL_apply (i : Fin 3) (x : 𝕊) : coordCL i x = ((x i : ℝ) : ℂ) := rfl

/-- Jet bound of a field: value, `dy`, `dy dy` bounded. -/
def JetBdd (G : ℝ × 𝕊 → 𝕊) : Prop :=
  ∃ C : ℝ, (∀ x, ‖G x‖ ≤ C) ∧ (∀ j x, ‖dy j G x‖ ≤ C) ∧ ∀ j k x, ‖dy j (dy k G) x‖ ≤ C

theorem jetBdd_add {f g : ℝ × 𝕊 → 𝕊} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (h1 : JetBdd f) (h2 : JetBdd g) : JetBdd (fun x => f x + g x) := by
  obtain ⟨C1, a1, b1, c1⟩ := h1
  obtain ⟨C2, a2, b2, c2⟩ := h2
  have df := hf.differentiable (by simp)
  have dg := hg.differentiable (by simp)
  have ddf : ∀ k, Differentiable ℝ (dy k f) := fun k =>
    (contDiff_dy' hf k).differentiable (by simp)
  have ddg : ∀ k, Differentiable ℝ (dy k g) := fun k =>
    (contDiff_dy' hg k).differentiable (by simp)
  refine ⟨C1 + C2, fun x => ?_, fun j x => ?_, fun j k x => ?_⟩
  · exact (norm_add_le _ _).trans (add_le_add (a1 x) (a2 x))
  · rw [dy_add' df dg]
    exact (norm_add_le _ _).trans (add_le_add (b1 j x) (b2 j x))
  · rw [dy_add' df dg, dy_add' (ddf k) (ddg k)]
    exact (norm_add_le _ _).trans (add_le_add (c1 j k x) (c2 j k x))

theorem jetBdd_smul {f : ℝ × 𝕊 → 𝕊} (hf : ContDiff ℝ ∞ f) (c : ℝ) (h1 : JetBdd f) :
    JetBdd (fun x => c • f x) := by
  obtain ⟨C1, a1, b1, c1⟩ := h1
  have df := hf.differentiable (by simp)
  have ddf : ∀ k, Differentiable ℝ (dy k f) := fun k =>
    (contDiff_dy' hf k).differentiable (by simp)
  refine ⟨|c| * C1, fun x => ?_, fun j x => ?_, fun j k x => ?_⟩
  · rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (a1 x) (abs_nonneg c)
  · rw [dy_smul' df]
    simp only
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (b1 j x) (abs_nonneg c)
  · rw [dy_smul' df, dy_smul' (ddf k)]
    simp only
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (c1 j k x) (abs_nonneg c)

theorem entry_of_bound {D : ℝ × 𝕊 → 𝕊} (hD : ContDiff ℝ ∞ D) {C : ℝ} (hb : ∀ x, ‖D x‖ ≤ C)
    (i : Fin 3) : GEQEntry (fun x => ((D x i : ℝ) : ℂ)) := by
  refine ⟨Complex.continuous_ofReal.comp
    ((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp hD.continuous), C, fun x => ?_⟩
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact (PiLp.norm_apply_le (D x) i).trans (hb x)

open UnforcedLeray.Short.IIb in
/-- Joint smoothness of an inlet column, for a single parameter with `ν ≤ 1`. -/
theorem inlet_joint_smooth {q : UnforcedLeray.Blueprint.Planar.Profile} {lam : ℂ}
    (hq : UnforcedLeray.Blueprint.Planar.IsGrowingEigenpair lam q) {dm dp d : ℝ} {p : Params}
    (hreg : BgRegime p d dm dp) (hν : p.ν ≤ 1) (hmode : p.mode = q) (i : Fin 2) :
    ContDiff ℝ ∞ (fun x : ℝ × 𝕊 => p.inlet i x.1 x.2) := by
  have hνpos : 0 < p.ν := p.ν_pos
  have hc1 : 1 ≤ p.c := by
    rw [hreg.c_eq, one_le_inv₀ (by positivity)]
    nlinarith
  obtain ⟨hB, hvan⟩ := inletProfile_smooth_vanish hq hc1 hmode i
  exact NicePT.contDiff_Nv p.R_pos hB (s1 := p.H / 2) hvan

open UnforcedLeray.Short.IIb in
theorem inlet_jetBdd {q : UnforcedLeray.Blueprint.Planar.Profile} {lam : ℂ}
    (hq : UnforcedLeray.Blueprint.Planar.IsGrowingEigenpair lam q) {dm dp d : ℝ} {p : Params}
    (hreg : BgRegime p d dm dp) (hν : p.ν ≤ 1) (hmode : p.mode = q) (i : Fin 2) :
    JetBdd (fun x : ℝ × 𝕊 => p.inlet i x.1 x.2) := by
  have hG := inlet_joint_smooth hq hreg hν hmode i
  obtain ⟨C0, h0⟩ := inlet_jet_bound_per hq hreg hν hmode i 0
  obtain ⟨C1, h1⟩ := inlet_jet_bound_per hq hreg hν hmode i 1
  obtain ⟨C2, h2⟩ := inlet_jet_bound_per hq hreg hν hmode i 2
  set C := max (max C0 C1) C2 with hC
  have hl : ∀ l ≤ 2, ∀ τ y, ‖iteratedFDeriv ℝ l (fun y' => p.inlet i τ y') y‖ ≤ C := by
    intro l hl τ y
    interval_cases l
    · exact (h0 τ y).trans ((le_max_left _ _).trans (le_max_left _ _))
    · exact (h1 τ y).trans ((le_max_right _ _).trans (le_max_left _ _))
    · exact (h2 τ y).trans (le_max_right _ _)
  exact ⟨C, fun x => (bdd_of_slice hG C hl 0 0).1 x, fun j x => (bdd_of_slice hG C hl j 0).2.1 x,
    fun j k x => (bdd_of_slice hG C hl j k).2.2 x⟩

open UnforcedLeray.Short.IIb in
/-- **`gEQInletWeak`** (source 2385-2387, 2525-2531). -/
theorem gEQInletWeak : GEQInletWeak := by
  intro lam q hq dm dp hdm
  refine ⟨1, one_pos, ?_⟩
  intro p d hreg hν hmode z g hd j k i
  set α := p.coord z with hα
  set E : ℝ × 𝕊 → 𝕊 := fun x => ∑ i : Fin 2, α i • p.inlet i x.1 x.2 with hE
  have hG := fun i => inlet_joint_smooth hq hreg hν hmode i
  have hJ := fun i => inlet_jetBdd hq hreg hν hmode i
  have hEeq : E = fun x => α 0 • p.inlet 0 x.1 x.2 + α 1 • p.inlet 1 x.1 x.2 := by
    funext x; simp [hE, Fin.sum_univ_two]
  have hE0 : ContDiff ℝ ∞ (fun x : ℝ × 𝕊 => α 0 • p.inlet 0 x.1 x.2) := (hG 0).const_smul _
  have hE1 : ContDiff ℝ ∞ (fun x : ℝ × 𝕊 => α 1 • p.inlet 1 x.1 x.2) := (hG 1).const_smul _
  have hEs : ContDiff ℝ ∞ E := by rw [hEeq]; exact hE0.add hE1
  have hEJ : JetBdd E := by
    rw [hEeq]
    exact jetBdd_add hE0 hE1 (jetBdd_smul (hG 0) _ (hJ 0)) (jetBdd_smul (hG 1) _ (hJ 1))
  obtain ⟨C, b0, b1, b2⟩ := hEJ
  have hdE : Differentiable ℝ E := hEs.differentiable (by simp)
  have hdE' : ∀ j, ContDiff ℝ ∞ (dy j E) := fun j => contDiff_dy' hEs j
  have hdEd : ∀ j, Differentiable ℝ (dy j E) := fun j => (hdE' j).differentiable (by simp)
  have heF : p.eFun α = fun x => realCL (E x) := by
    funext x; rfl
  have hd1 : ∀ j, dy j (p.eFun α) = fun x => realCL (dy j E x) := fun j => by
    rw [heF]; exact dy_clm realCL hdE j
  have hd2 : ∀ j k, dy j (dy k (p.eFun α)) = fun x => realCL (dy j (dy k E) x) := fun j k => by
    rw [hd1 k]; exact dy_clm realCL (hdEd k) j
  have hcoord : ∀ (D : ℝ × 𝕊 → 𝕊), Differentiable ℝ D → ∀ j,
      dy j (fun x => ((D x i : ℝ) : ℂ)) = fun x => ((dy j D x i : ℝ) : ℂ) := fun D hD j => by
    exact dy_clm (coordCL i) hD j
  have e0 : (fun x => p.eFun α x i) = fun x => ((E x i : ℝ) : ℂ) := by
    funext x; exact UnforcedLeray.B0412.realC_apply _ _
  have e1 : (fun x => dy j (p.eFun α) x i) = fun x => ((dy j E x i : ℝ) : ℂ) := by
    rw [hd1 j]; funext x; exact realCL_apply _ _
  have e2 : (fun x => dy j (dy k (p.eFun α)) x i) = fun x => ((dy j (dy k E) x i : ℝ) : ℂ) := by
    rw [hd2 j k]; funext x; exact realCL_apply _ _
  have hs0 : ContDiff ℝ ∞ (fun x => ((E x i : ℝ) : ℂ)) :=
    (coordCL i).contDiff.comp hEs
  have hs1 : ∀ j, ContDiff ℝ ∞ (fun x => ((dy j E x i : ℝ) : ℂ)) := fun j =>
    (coordCL i).contDiff.comp (hdE' j)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [e0]; exact entry_of_bound hEs b0 i
  · rw [e1]; exact entry_of_bound (hdE' j) (fun x => b1 j x) i
  · rw [e2]
    exact entry_of_bound (contDiff_dy' (hdE' k) j) (fun x => b2 j k x) i
  · rw [e0, e1]
    have := weakDyS_of_smooth p.period j hs0
    rwa [hcoord E hdE j] at this
  · have hef : ContDiff ℝ ∞ (p.eFun α) := by rw [heF]; exact realCL.contDiff.comp hEs
    have hdef : ContDiff ℝ ∞ (dy j (p.eFun α)) := contDiff_dy' hef j
    let cC : CVec3 →L[ℝ] ℂ := (EuclideanSpace.proj (𝕜 := ℂ) i).restrictScalars ℝ
    have hs : ContDiff ℝ ∞ (fun x => dy j (p.eFun α) x i) := cC.contDiff.comp hdef
    have h := weakDyS_of_smooth p.period k hs
    have hc : dy k (fun x => dy j (p.eFun α) x i) = fun x => dy k (dy j (p.eFun α)) x i :=
      dy_clm cC (hdef.differentiable (by simp)) k
    rw [hc, ← dy_dy_comm hef j k] at h
    exact h

end UnforcedLeray.Short.PartIIIb.Concrete
