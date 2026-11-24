import UnforcedLeray.Short.PartIIIa.Sub.PartIIIa_T21_3_2_2_Smooth
import UnforcedLeray.Short.PartIIIa.Clock.Existence.UnitHeatWeak.FluxDuhamel.CellInt

/-!
# Part III-a, `PartIII-a:T21/3/2/2/3/1`: the flux pairing of the smoothed Duhamel identity

Source of record: `the November 2 reference manuscript`, lines 2819-2836.
Proves `FluxPairHeatDuhamel` (`Smooth/DuhamelSplit.lean`): for one flux `F`, a cylinder test `φ`
and `0 ≤ θ ≤ 1`, `⟨F, ∇P_θφ⟩ = ⟨F, ∇φ⟩ + ∫_0^θ ⟨F, ∇P_η Δφ⟩ dη`, by the pointwise Duhamel
identity `pd_cylHeatSmooth_duhamel` and Fubini on `cell × [0, θ]`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set MeasureTheory Filter Topology

namespace UnforcedLeray.Short.IIIa.Exist

open UnforcedLeray.Short.IIIa
open UnforcedLeray.Cons.L2.ReturnConcrete.MixedEvolution

/-- The integrand of `fluxPair`, as a function of the point. -/
def fluxInt {c m : ℝ} [Fact (0 < c)] (F : ActualFlux (c := c) (m := m))
    (ψ : ℝ × ℝ → ℝ) (x : ℝ × ℝ) : ℝ :=
  fluxFn F 0 x * UnforcedLeray.B0579.pd 0 ψ x + fluxFn F 1 x * UnforcedLeray.B0579.pd 1 ψ x

theorem fluxPair_eq_integral {c m : ℝ} [Fact (0 < c)] (hm : 1 ≤ m)
    (F : ActualFlux (c := c) (m := m)) (ψ : ℝ × ℝ → ℝ) :
    fluxPair hm F ψ = ∫ x in UnforcedLeray.B0579.cell c, fluxInt F ψ x := rfl

theorem abs_add_mul_le_aux (a b c d Q : ℝ) (h0 : |b| ≤ Q) (h1 : |d| ≤ Q) :
    |a * b + c * d| ≤ (|a| + |c|) * Q := by
  have hQ : 0 ≤ Q := (abs_nonneg _).trans h0
  calc |a * b + c * d| ≤ |a * b| + |c * d| := abs_add_le _ _
    _ = |a| * |b| + |c| * |d| := by rw [abs_mul, abs_mul]
    _ ≤ |a| * Q + |c| * Q :=
        add_le_add (mul_le_mul_of_nonneg_left h0 (abs_nonneg _))
          (mul_le_mul_of_nonneg_left h1 (abs_nonneg _))
    _ = (|a| + |c|) * Q := by ring

theorem fluxPairHeatDuhamel : FluxPairHeatDuhamel := by
  intro c m _ hm F φ hφ θ hθ
  have hc : 0 < c := Fact.out
  have hθ0 : 0 ≤ θ := hθ.1
  have hL : UnforcedLeray.B0579.IsCylTest c (lapP φ) := cylTest_lapP hφ
  obtain ⟨M0, hM0, hMb0⟩ := exists_bound_pdWord_cylHeatSmooth hc hL [0]
  obtain ⟨M1, hM1, hMb1⟩ := exists_bound_pdWord_cylHeatSmooth hc hL [1]
  have hQ : ∀ i : Fin 2, ∀ η x,
      |UnforcedLeray.B0579.pd i (cylHeatSmooth c η (lapP φ)) x| ≤ M0 + M1 := by
    intro i η x
    fin_cases i
    · exact (hMb0 η x).trans (by linarith)
    · exact (hMb1 η x).trans (by linarith)
  have hjoint : ∀ i : Fin 2, Continuous (fun p : ℝ × (ℝ × ℝ) =>
      UnforcedLeray.B0579.pd i (cylHeatSmooth c p.1 (lapP φ)) p.2) :=
    fun i => continuous_pd_cylHeatSmooth_joint hc hL i
  have hcont_eta : ∀ (i : Fin 2) (x : ℝ × ℝ),
      Continuous (fun η : ℝ => UnforcedLeray.B0579.pd i (cylHeatSmooth c η (lapP φ)) x) :=
    fun i x => (hjoint i).comp (continuous_id.prodMk continuous_const)
  have hQcont : ∀ i : Fin 2, Continuous (fun z : (ℝ × ℝ) × ℝ =>
      UnforcedLeray.B0579.pd i (cylHeatSmooth c z.2 (lapP φ)) z.1) :=
    fun i => (hjoint i).comp (continuous_snd.prodMk continuous_fst)
  -- integrability of the fluxes on the cell
  have hFint : ∀ i : Fin 2, Integrable (fun x => fluxFn F i x)
      (volume.restrict (UnforcedLeray.B0579.cell c)) := by
    intro i
    have h := integrableOn_mul_bdd_cont hm (F i) (g := fun _ : ℝ × ℝ => (1 : ℝ))
      continuous_const (M := 1) (fun x => by simp)
    have h2 : IntegrableOn (fun x => fluxFn F i x) (UnforcedLeray.B0579.cell c) := by
      simpa [fluxFn] using h
    exact h2
  have hFaesm : ∀ i : Fin 2, AEStronglyMeasurable (fun x => fluxFn F i x)
      (volume.restrict (UnforcedLeray.B0579.cell c)) := by
    intro i
    exact ((Lp.aestronglyMeasurable (F i)).mono_ac
      (UnforcedLeray.B0579.ac_cellMeasure c m))
  -- the time-integrand on cell × (0, θ]
  have hGint : Integrable (fun z : (ℝ × ℝ) × ℝ =>
      fluxFn F 0 z.1 * UnforcedLeray.B0579.pd 0 (cylHeatSmooth c z.2 (lapP φ)) z.1 +
        fluxFn F 1 z.1 * UnforcedLeray.B0579.pd 1 (cylHeatSmooth c z.2 (lapP φ)) z.1)
      ((volume.restrict (UnforcedLeray.B0579.cell c)).prod (volume.restrict (Ioc 0 θ))) := by
    have hF0 : Integrable (fun x => |fluxFn F 0 x| + |fluxFn F 1 x|)
        (volume.restrict (UnforcedLeray.B0579.cell c)) :=
      (hFint 0).abs.add (hFint 1).abs
    have hconst : Integrable (fun _ : ℝ => M0 + M1) (volume.restrict (Ioc 0 θ)) :=
      integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    have hbound := Integrable.mul_prod hF0 hconst
    refine Integrable.mono' hbound ?_ ?_
    · exact ((hFaesm 0).comp_fst.mul (hQcont 0).aestronglyMeasurable).add
        ((hFaesm 1).comp_fst.mul (hQcont 1).aestronglyMeasurable)
    · refine Eventually.of_forall fun z => ?_
      rw [Real.norm_eq_abs]
      exact abs_add_mul_le_aux _ _ _ _ _ (hQ 0 z.2 z.1) (hQ 1 z.2 z.1)
  -- the flux-integrand against the test `φ`
  have hA : Integrable (fun x => fluxInt F φ x)
      (volume.restrict (UnforcedLeray.B0579.cell c)) := by
    unfold fluxInt
    obtain ⟨B0, -, hB0⟩ := cylTest_exists_bound hc (hφ.pd 0)
    obtain ⟨B1, -, hB1⟩ := cylTest_exists_bound hc (hφ.pd 1)
    exact (integrableOn_mul_bdd_cont hm (F 0) (hφ.pd 0).continuous hB0).add
      (integrableOn_mul_bdd_cont hm (F 1) (hφ.pd 1).continuous hB1)
  -- pointwise Duhamel identity for the flux integrand
  have hsplit : ∀ x, fluxInt F (cylHeatSmooth c θ φ) x =
      fluxInt F φ x + ∫ η in (0 : ℝ)..θ, fluxInt F (cylHeatSmooth c η (lapP φ)) x := by
    intro x
    have e : ∫ η in (0 : ℝ)..θ, fluxInt F (cylHeatSmooth c η (lapP φ)) x =
        fluxFn F 0 x * (∫ η in (0 : ℝ)..θ, UnforcedLeray.B0579.pd 0
          (cylHeatSmooth c η (lapP φ)) x) +
        fluxFn F 1 x * (∫ η in (0 : ℝ)..θ, UnforcedLeray.B0579.pd 1
          (cylHeatSmooth c η (lapP φ)) x) := by
      unfold fluxInt
      rw [intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
      · exact (continuous_const.mul (hcont_eta 0 x)).intervalIntegrable _ _
      · exact (continuous_const.mul (hcont_eta 1 x)).intervalIntegrable _ _
    rw [e]
    unfold fluxInt
    rw [pd_cylHeatSmooth_duhamel hc hφ hθ0 0 x, pd_cylHeatSmooth_duhamel hc hφ hθ0 1 x]
    ring
  have step1 : fluxPair hm F (cylHeatSmooth c θ φ) =
      ∫ x in UnforcedLeray.B0579.cell c,
        (fluxInt F φ x + ∫ η in (0 : ℝ)..θ, fluxInt F (cylHeatSmooth c η (lapP φ)) x) := by
    rw [fluxPair_eq_integral]
    exact integral_congr_ae (Eventually.of_forall hsplit)
  have hI' : Integrable (fun x => ∫ η in (0 : ℝ)..θ,
      fluxInt F (cylHeatSmooth c η (lapP φ)) x)
      (volume.restrict (UnforcedLeray.B0579.cell c)) := by
    have h := hGint.integral_prod_left
    simp only [intervalIntegral.integral_of_le hθ0]
    exact h
  have step3 : ∫ x in UnforcedLeray.B0579.cell c, ∫ η in (0 : ℝ)..θ,
      fluxInt F (cylHeatSmooth c η (lapP φ)) x =
      ∫ η in (0 : ℝ)..θ, ∫ x in UnforcedLeray.B0579.cell c,
        fluxInt F (cylHeatSmooth c η (lapP φ)) x := by
    simp only [intervalIntegral.integral_of_le hθ0]
    exact integral_integral_swap hGint
  calc fluxPair hm F (cylHeatSmooth c θ φ)
      = ∫ x in UnforcedLeray.B0579.cell c,
          (fluxInt F φ x + ∫ η in (0 : ℝ)..θ, fluxInt F (cylHeatSmooth c η (lapP φ)) x) := step1
    _ = (∫ x in UnforcedLeray.B0579.cell c, fluxInt F φ x) +
          ∫ x in UnforcedLeray.B0579.cell c, ∫ η in (0 : ℝ)..θ,
            fluxInt F (cylHeatSmooth c η (lapP φ)) x :=
        integral_add hA hI'
    _ = fluxPair hm F φ + ∫ η in (0 : ℝ)..θ, fluxPair hm F (cylHeatSmooth c η (lapP φ)) := by
        rw [step3]
        rfl

end UnforcedLeray.Short.IIIa.Exist
