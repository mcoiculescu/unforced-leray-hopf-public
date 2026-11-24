import UnforcedLeray.Lib.HeatR3.SimContinuity
import UnforcedLeray.Loc.Hyp.HeatProfileRegularity
import UnforcedLeray.Blueprint.Package
import UnforcedLeray.Loc.L01Coefficient.Operators
import UnforcedLeray.Loc.Hyp.H2ProductBound.L4

/-!
# The similarity heat profile as a continuous L⁴ path

The inverse-distance bound on the datum gives a uniform inverse-distance envelope for the
similarity heat profile. The phase Lipschitz estimate with the same envelope upgrades this to a
continuous path in L⁴. This is the value-space continuity needed when combining the heat profile
with the continuous H² remainder of a concrete background.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open UnforcedLeray.HeatProfileReg
open UnforcedLeray.Blueprint.L10.H2Prod
open UnforcedLeray.Blueprint.L01
open UnforcedLeray.SobolevGraph
open scoped ENNReal ContDiff

namespace UnforcedLeray.Cons.C03.Concrete

open UnforcedLeray.Heat

local instance fact_one_le_four_background : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩

/-- For inverse-distance data, the similarity heat profile has a canonical continuous L⁴ path. -/
theorem simHeat_continuous_L4 {t C : ℝ} (ht : 0 < t) {u : SpatialField}
    (hu : InvDistClass 3 C u) :
    ∃ W : ℝ → Lp Space 4 volume, Continuous W ∧
      ∀ τ, (W τ : Space → Space) =ᵐ[volume] simHeat t u τ := by
  have hu2 : InvDistClass 2 C u := hu.of_le (by norm_num)
  obtain ⟨K, hK⟩ := simHeat_decay ht hu2 (j := 0) (by norm_num)
  obtain ⟨L, hL0, hL⟩ := norm_iteratedFDeriv_simHeat_sub_le ht hu (j := 0) (by norm_num)
  have hw : MemLp (fun y : Space => (1 + ‖y‖) ^ (-(1 : ℝ))) 4 volume :=
    memLp_weight_rpow (by norm_num) (by norm_num) (by norm_num)
  have hsm : ∀ τ, ContDiff ℝ ∞ (simHeat t u τ) := fun τ =>
    simHeat_contDiff ht hu.heatAdmissible τ
  refine exists_continuous_Lp_of_lipschitz (K := K) hw
    (fun τ => (hsm τ).continuous.aestronglyMeasurable) hL0 ?_ ?_
  · intro τ y
    have h := hK τ y
    rw [norm_iteratedFDeriv_zero] at h
    have he : -((1 + 0 : ℕ) : ℝ) = (-1 : ℝ) := by norm_num
    have hweight : ‖(1 + ‖y‖) ^ (-1 : ℝ)‖ = (1 + ‖y‖) ^ (-1 : ℝ) :=
      Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)
    simpa only [he, hweight] using h
  · intro σ τ y
    have h := hL σ τ y
    rw [norm_iteratedFDeriv_zero] at h
    change ‖simHeat t u σ y - simHeat t u τ y‖ ≤ _ at h
    have he : -((1 + 0 : ℕ) : ℝ) = (-1 : ℝ) := by norm_num
    have hweight : ‖(1 + ‖y‖) ^ (-1 : ℝ)‖ = (1 + ‖y‖) ^ (-1 : ℝ) :=
      Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)
    simpa only [he, hweight] using h

/-- The weighted derivative bounds recorded for a concrete datum imply the inverse-distance
class required by HeatR3's phase estimates. -/
theorem exists_invDistClass3_of_datum_bounds {u : SpatialField}
    (hu : ContDiffOn ℝ ∞ u {0}ᶜ)
    (hb : ∀ k : ℕ, k ≤ 4 → ∃ C : ℝ, ∀ x : Space, x ≠ 0 →
      ‖iteratedFDeriv ℝ k u x‖ * ‖x‖ ^ (k + 1) ≤ C) :
    ∃ C : ℝ, InvDistClass 3 C u := by
  obtain ⟨C, hC0, hC⟩ := uniform_bound hb
  refine ⟨C, ⟨hu.of_le (by norm_num), ?_⟩⟩
  intro k hk x hx
  have h := hC k (by omega) x hx
  have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have he : (-(1 + (k : ℝ))) = -((k + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [he, Real.rpow_neg hxn.le, Real.rpow_natCast]
  rw [div_eq_mul_inv] at h
  exact h

/-- Applying the preceding result to the manuscript's datum bounds gives a continuous L⁴ path
for the actual heat profile used by the concrete background. -/
theorem exists_continuous_heatProfile_L4_of_datum {t : ℝ} (ht : 0 < t)
    {a : SpatialField} (ha : ContDiffOn ℝ ∞ a {0}ᶜ)
    (hb : ∀ k : ℕ, k ≤ 4 → ∃ C : ℝ, ∀ x : Space, x ≠ 0 →
      ‖iteratedFDeriv ℝ k a x‖ * ‖x‖ ^ (k + 1) ≤ C) :
    ∃ W : ℝ → Lp Space 4 volume, Continuous W ∧
      ∀ τ, (W τ : Space → Space) =ᵐ[volume] UnforcedLeray.Blueprint.heatProfile t a τ := by
  obtain ⟨C, hInv⟩ := exists_invDistClass3_of_datum_bounds ha hb
  obtain ⟨W, hWc, hW⟩ := simHeat_continuous_L4 ht hInv
  refine ⟨W, hWc, ?_⟩
  intro τ
  exact hW τ

/-- The value and first weak derivatives of an H² field form an H¹ field. -/
def h2ValueAmbient : SobolevGraph.H2 →L[ℝ] SobolevGraph.H1Ambient :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => L2Space)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi
      (Fin.cons (SobolevGraph.H2.valueCLM)
        (fun i => SobolevGraph.H2.firstCLM i) :
          Fin 4 → (SobolevGraph.H2 →L[ℝ] L2Space)))

theorem h2ValueAmbient_mem (F : SobolevGraph.H2) : h2ValueAmbient F ∈ H1Sub := by
  rw [mem_H1Sub_iff]
  intro i
  exact F.hasWeakFirst i

/-- The continuous inclusion of H² value fields into H¹. -/
def h2ValueToH1 : SobolevGraph.H2 →L[ℝ] SobolevGraph.H1 :=
  h2ValueAmbient.codRestrict H1Sub h2ValueAmbient_mem

@[simp] theorem h2ValueToH1_value (F : SobolevGraph.H2) :
    (h2ValueToH1 F).value = F.value := rfl

private def backgroundH1ToL4 (F : SobolevGraph.H1) : Lp Space 4 (volume : Measure Space) :=
  (h1_memLp_four F).toLp (F.value : SpatialField)

private theorem coeFn_backgroundH1ToL4 (F : SobolevGraph.H1) :
    (backgroundH1ToL4 F : SpatialField) =ᵐ[volume] (F.value : SpatialField) :=
  (h1_memLp_four F).coeFn_toLp

private def backgroundH1ToL4Linear :
    SobolevGraph.H1 →ₗ[ℝ] Lp Space 4 (volume : Measure Space) where
  toFun := backgroundH1ToL4
  map_add' F G := by
    apply Lp.ext
    filter_upwards [coeFn_backgroundH1ToL4 (F + G), coeFn_backgroundH1ToL4 F,
      coeFn_backgroundH1ToL4 G, Lp.coeFn_add (backgroundH1ToL4 F) (backgroundH1ToL4 G),
      Lp.coeFn_add F.value G.value] with x hsum hF hG hLp hval
    change backgroundH1ToL4 (F + G) x = (backgroundH1ToL4 F + backgroundH1ToL4 G) x
    rw [hsum, hLp]
    simp only [Pi.add_apply]
    rw [hF, hG]
    exact hval
  map_smul' c F := by
    apply Lp.ext
    filter_upwards [coeFn_backgroundH1ToL4 (c • F), coeFn_backgroundH1ToL4 F,
      Lp.coeFn_smul c (backgroundH1ToL4 F), Lp.coeFn_smul c F.value] with x hsmul hF hLp hval
    change backgroundH1ToL4 (c • F) x = (c • backgroundH1ToL4 F) x
    rw [hsmul, hLp]
    simp only [Pi.smul_apply]
    rw [hF]
    exact hval

private theorem backgroundH1ToL4_norm_le (F : SobolevGraph.H1) :
    ‖backgroundH1ToL4 F‖ ≤ l4Const * ‖F‖ := by
  rw [backgroundH1ToL4, Lp.norm_toLp]
  exact h1_l4Norm_le F

private def backgroundH1ToL4CLM :
    SobolevGraph.H1 →L[ℝ] Lp Space 4 (volume : Measure Space) :=
  backgroundH1ToL4Linear.mkContinuous l4Const backgroundH1ToL4_norm_le

/-- The canonical L⁴ class of the value field of an H² field. -/
def h2ValueL4 (F : SobolevGraph.H2) : Lp Space 4 (volume : Measure Space) :=
  backgroundH1ToL4CLM (h2ValueToH1 F)

/-- A continuous H² path gives a continuous L⁴ path of its value fields. -/
theorem continuous_h2Value_L4 (Q : ℝ → SobolevGraph.H2) (hQ : Continuous Q) :
    Continuous (fun τ => h2ValueL4 (Q τ)) :=
  backgroundH1ToL4CLM.continuous.comp (h2ValueToH1.continuous.comp hQ)

theorem h2Value_L4_ae (F : SobolevGraph.H2) :
    (h2ValueL4 F : SpatialField) =ᵐ[volume] F.value := by
  exact (coeFn_backgroundH1ToL4 (h2ValueToH1 F)).trans (by simp)

end UnforcedLeray.Cons.C03.Concrete
