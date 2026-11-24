import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_12_3_1_2_7_6_1.L2.Slice
import UnforcedLeray.Short.PartIIb.Sub.PartIIb_G4_5_2_1_2_org
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.RingLift.ChartJets.AgeJets
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.RingLift.ChartJets.PhaseJets
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.RingLift.ChartJets.TransJets
import UnforcedLeray.Short.PartIIb.Tasks.AffineColumnComparison.RingLift.SqrtFrameJets.FrameJets

/-!
# `ϱ⁻¹`-weighted jets of the ring chart (helper for `nvFirstPt`, `nvSecondPt`)

Source `the November 2 reference manuscript`
lines 2346-2366, 2385-2387: with `t = ϱ(y)⁻¹`, `s = age R y = R² t²`, `η = trans R y`,
every `y`-derivative of the amplitude `√s = R t`, the frame, and the chart `(s, ξ, η)` carries one
factor `t`, the chart derivatives additionally the factor `W = 1 + s + |η|`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray

theorem age_eq_sq (R : ℝ) (y : Space) : Axi.age R y = R ^ 2 * ((Axi.ϱ y)⁻¹) ^ 2 := by
  rw [Axi.age, div_eq_mul_inv, inv_pow]

theorem sqrt_age_eq {R : ℝ} (hR : 0 < R) :
    (fun z : Space => √(Axi.age R z)) = fun z => R * (Axi.ϱ z)⁻¹ := by
  funext z
  rw [age_eq_sq, ← mul_pow]
  exact Real.sqrt_sq (mul_nonneg hR.le (inv_nonneg.2 (Axi.ϱ_nonneg z)))

/-- Jets of the amplitude `√(age R ·) = R ϱ⁻¹`. -/
theorem amp_jet {R : ℝ} (hR : 0 < R) (n : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ y : Space, y ∉ Axi.axis →
    ‖iteratedFDeriv ℝ n (fun z : Space => √(Axi.age R z)) y‖ ≤
      C * R * ((Axi.ϱ y)⁻¹) ^ (n + 1) := by
  obtain ⟨C, hC, h⟩ := IIb.SqrtFrameJetsAux.varrho_inv_jet n
  refine ⟨C, hC, fun y hy => ?_⟩
  have hopen : IsOpen (Axi.axisᶜ : Set Space) := Axi.isOpen_compl_axis
  have hg : ContDiffOn ℝ ∞ (fun w : Space => (Axi.ϱ w)⁻¹) Axi.axisᶜ :=
    Axi.contDiffOn_ϱ.inv fun _ hw => Axi.ϱ_ne_zero hw
  have hdiff : ContDiffAt ℝ n (fun w : Space => (Axi.ϱ w)⁻¹) y :=
    ((hg.contDiffAt (hopen.mem_nhds hy)).of_le (by exact_mod_cast le_top))
  rw [sqrt_age_eq hR, show (fun z : Space => R * (Axi.ϱ z)⁻¹) = R • (fun z : Space => (Axi.ϱ z)⁻¹)
    from rfl, iteratedFDeriv_const_smul_apply hdiff, norm_smul, Real.norm_of_nonneg hR.le]
  calc R * ‖iteratedFDeriv ℝ n (fun z : Space => (Axi.ϱ z)⁻¹) y‖ ≤ R * (C * ((Axi.ϱ y)⁻¹) ^ (n + 1)) :=
        mul_le_mul_of_nonneg_left (h y hy) hR.le
    _ = C * R * ((Axi.ϱ y)⁻¹) ^ (n + 1) := by ring

/-- Jets of the frame. -/
theorem frame_jet (n : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ y : Space, y ∉ Axi.axis →
    ‖iteratedFDeriv ℝ n Axi.frameL y‖ ≤ C * ((Axi.ϱ y)⁻¹) ^ n :=
  IIb.SqrtFrameJetsAux.frameL_jet n

/-- Jets of the chart `(s, ξ, η)`, order `n ≥ 1`: `≲ t^n (1 + s + |η|)`. -/
theorem chart_jet {R : ℝ} (hR : 0 < R) (n : ℕ) (hn : 1 ≤ n) : ∃ a : ℝ, 0 < a ∧
    ∀ (τ : ℝ) (y : Space), y ∉ Axi.axis →
      ‖iteratedFDeriv ℝ n (Axi.chart R τ) y‖ ≤
        a * ((Axi.ϱ y)⁻¹) ^ n * (1 + Axi.age R y + |Axi.trans R y|) := by
  obtain ⟨CA, hCA, hA'⟩ := IIb.ageJets n
  obtain ⟨CP, hCP, hP'⟩ := IIb.phaseJets n hn
  obtain ⟨CT, hCT, hT'⟩ := IIb.transJets n hn
  refine ⟨CA + CP * R + CT * (1 + R), by positivity, ?_⟩
  intro τ y hy
  have hU : Axi.axisᶜ ∈ 𝓝 y := Axi.isOpen_compl_axis.mem_nhds hy
  have cA : ContDiffAt ℝ ∞ (Axi.age R) y := (IIb.ChartJetsAux.contDiffOn_age R).contDiffAt hU
  have cP : ContDiffAt ℝ ∞ (Axi.phase R τ) y :=
    (IIb.ChartJetsAux.contDiffOn_phase hR.ne' τ).contDiffAt hU
  have cT : ContDiffAt ℝ ∞ (Axi.trans R) y := (IIb.ChartJetsAux.contDiffOn_trans R).contDiffAt hU
  have hn' : ((n : ℕ) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have hD : iteratedFDeriv ℝ n (Axi.chart R τ) y =
      (iteratedFDeriv ℝ n (Axi.age R) y).prod
        ((iteratedFDeriv ℝ n (Axi.phase R τ) y).prod (iteratedFDeriv ℝ n (Axi.trans R) y)) := by
    rw [show Axi.chart R τ = fun x => (Axi.age R x, (Axi.phase R τ x, Axi.trans R x)) from rfl,
      iteratedFDeriv_prodMk cA (cP.prodMk cT) hn', iteratedFDeriv_prodMk cP cT hn']
  rw [hD, ContinuousMultilinearMap.opNorm_prod, ContinuousMultilinearMap.opNorm_prod]
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = (Axi.ϱ y)⁻¹ := ⟨_, rfl⟩
  have ht0 : 0 ≤ t := by rw [ht]; exact inv_nonneg.2 (Axi.ϱ_nonneg y)
  have hs : Axi.age R y = R ^ 2 * t ^ 2 := by rw [age_eq_sq, ht]
  have hη0 : 0 ≤ |Axi.trans R y| := abs_nonneg _
  have hs0 : 0 ≤ Axi.age R y := by rw [hs]; positivity
  set W : ℝ := 1 + Axi.age R y + |Axi.trans R y| with hW
  have hW1 : 1 ≤ W := by rw [hW]; linarith
  rw [← ht]
  have tn : 0 ≤ t ^ n := pow_nonneg ht0 n
  have bA : ‖iteratedFDeriv ℝ n (Axi.age R) y‖ ≤ CA * t ^ n * W := by
    have h := hA' R y hy
    rw [← ht] at h
    have e : CA * R ^ 2 * t ^ (n + 2) = CA * t ^ n * Axi.age R y := by rw [hs]; ring
    rw [e] at h
    refine h.trans ?_
    have : Axi.age R y ≤ W := by rw [hW]; linarith
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have bP : ‖iteratedFDeriv ℝ n (Axi.phase R τ) y‖ ≤ CP * R * t ^ n * W := by
    have h := hP' R τ y hR hy
    rw [← ht] at h
    refine h.trans ?_
    have : CP * R * t ^ n * 1 ≤ CP * R * t ^ n * W :=
      mul_le_mul_of_nonneg_left hW1 (by positivity)
    linarith
  have bT : ‖iteratedFDeriv ℝ n (Axi.trans R) y‖ ≤ CT * (1 + R) * t ^ n * W := by
    have h := hT' R y hR hy
    rw [← ht] at h
    refine h.trans ?_
    have h1 : |Axi.trans R y| + R ≤ (1 + R) * W := by rw [hW]; nlinarith
    calc CT * (|Axi.trans R y| + R) * t ^ n = CT * t ^ n * (|Axi.trans R y| + R) := by ring
      _ ≤ CT * t ^ n * ((1 + R) * W) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = CT * (1 + R) * t ^ n * W := by ring
  have hc : 0 ≤ t ^ n * W := by positivity
  have e1 : (CA + CP * R + CT * (1 + R)) * t ^ n * W =
      CA * t ^ n * W + CP * R * t ^ n * W + CT * (1 + R) * t ^ n * W := by ring
  have p1 : 0 ≤ CA * t ^ n * W := by positivity
  have p2 : 0 ≤ CP * R * t ^ n * W := by positivity
  have p3 : 0 ≤ CT * (1 + R) * t ^ n * W := by positivity
  refine max_le ?_ (max_le ?_ ?_)
  · rw [e1]; linarith
  · rw [e1]; linarith
  · rw [e1]; linarith

end UnforcedLeray.Short.PartIIIb.Concrete
