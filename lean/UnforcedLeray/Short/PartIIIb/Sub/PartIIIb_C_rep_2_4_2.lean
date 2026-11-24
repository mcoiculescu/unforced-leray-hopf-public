import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_4_1
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_4_4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_4_fub

/-!
# `PartIII-b:C/rep/2/4/2` : reduction to the vertical profile (`OutMajReduce`)

Source `the November 2 reference manuscript` 4181-4192 (`Ψ_Z` majorant), with the
gap-kernel `ρ`-integral `outMajRho` (`PartIII-b:C/rep/2/4/1`), Tonelli in `(ρ, λ, z')`, and the
horizontal integration of `z'` (`lintegral_space_xys`, `lintegral_xys_swap`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

theorem outRed_sepKd_meas (D : ℝ) : Measurable (IIIa.sepKd 0 D) := by
  unfold IIIa.sepKd
  exact Measurable.ite (measurableSet_le measurable_const measurable_norm)
    (ENNReal.measurable_ofReal.comp (measurable_norm.pow_const _)) measurable_const

theorem outRed_coord2 : Measurable (fun z : Space => z 2) := by
  have hc : Continuous (fun z : Space => z 2) := by
    fun_prop
  exact hc.measurable

/-- Horizontal integration of a function of the height coordinate (`dy dx` iterated integral). -/
theorem outRed_slice (F : ℝ → ℝ≥0∞) (hF : Measurable F) (G : Space → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ z' : Space, F (z' 2) * G z' = ∫⁻ s : ℝ, F s * ∫⁻ x : ℝ, ∫⁻ y : ℝ, G !₂[x, y, s] := by
  have hmeas : Measurable (fun z' : Space => F (z' 2) * G z') :=
    (hF.comp outRed_coord2).mul hG
  rw [lintegral_space_xys _ hmeas]
  have hm3 : Measurable (fun q : ℝ × ℝ × ℝ => F q.2.2 * G (!₂[q.1, q.2.1, q.2.2] : Space)) := by
    refine Measurable.mul (hF.comp measurable_snd.snd) ?_
    refine hG.comp ?_
    exact (by fun_prop : Continuous fun q : ℝ × ℝ × ℝ => (!₂[q.1, q.2.1, q.2.2] : Space)).measurable
  have hsw := lintegral_xys_swap _ hm3
  dsimp only at hsw
  have hL : ∫⁻ x : ℝ, ∫⁻ y : ℝ, ∫⁻ s : ℝ, F ((!₂[x, y, s] : Space) 2) * G !₂[x, y, s] =
      ∫⁻ x : ℝ, ∫⁻ y : ℝ, ∫⁻ s : ℝ, F s * G !₂[x, y, s] :=
    lintegral_congr fun x => lintegral_congr fun y => lintegral_congr fun s => by simp
  rw [hL, hsw]
  refine lintegral_congr fun s => ?_
  have h1 : ∀ x : ℝ, ∫⁻ y : ℝ, F s * G !₂[x, y, s] = F s * ∫⁻ y : ℝ, G !₂[x, y, s] := fun x =>
    lintegral_const_mul _ (hG.comp
      (by fun_prop : Continuous fun y : ℝ => (!₂[x, y, s] : Space)).measurable)
  simp only [h1]
  refine lintegral_const_mul _ ?_
  exact Measurable.lintegral_prod_right' (f := fun p : ℝ × ℝ => G !₂[p.1, p.2, s])
    (hG.comp (by fun_prop : Continuous fun p : ℝ × ℝ => (!₂[p.1, p.2, s] : Space)).measurable)

/-- Measurability of the `z'`-integral in `(ρ, λ)`. -/
theorem outRed_I_meas (rOut rIn z τ : ℝ) (g : ℝ → Space → ℝ≥0∞)
    (hg : Measurable (Function.uncurry g)) :
    Measurable (fun p : ℝ × ℝ => ∫⁻ z' : Space,
      IIIa.sepKd 0 (rIn - rOut) ((!₂[p.1, 0, z] : Space) - p.2 • z') * g (τ + 2 * Real.log p.2) z') := by
  refine Measurable.lintegral_prod_right' (f := fun q : (ℝ × ℝ) × Space =>
    IIIa.sepKd 0 (rIn - rOut) ((!₂[q.1.1, 0, z] : Space) - q.1.2 • q.2) *
      g (τ + 2 * Real.log q.1.2) q.2) ?_
  refine Measurable.mul ?_ ?_
  · refine (outRed_sepKd_meas _).comp ?_
    exact (by fun_prop : Continuous fun q : (ℝ × ℝ) × Space =>
      (!₂[q.1.1, 0, z] : Space) - q.1.2 • q.2).measurable
  · have hlog : Measurable (fun q : (ℝ × ℝ) × Space => τ + 2 * Real.log q.1.2) :=
      measurable_const.add (measurable_const.mul (Real.measurable_log.comp measurable_fst.snd))
    exact hg.comp (hlog.prodMk measurable_snd)

/-- The fibre bound at a fixed `λ ∈ (0,1)`: the `ρ`-integral of the gap kernel against the
source, with `OutMajRho` applied pointwise in `z'` and the horizontal integration. -/
theorem outRed_fiber (a rOut rIn : ℝ) (hrO : 0 ≤ rOut) (hrr : rOut < rIn)
    (g : ℝ → Space → ℝ≥0∞) (hg : Measurable (Function.uncurry g))
    (hsupp : ∀ τ z, rOut < ϱ z → g τ z = 0) (τ r z l : ℝ) (hr : rIn ≤ r) (hl0 : 0 < l) (hl1 : l < 1) :
    ∫⁻ ρ in Ioi r, ENNReal.ofReal ρ * (ENNReal.ofReal (l ^ a) *
        ∫⁻ z' : Space, IIIa.sepKd 0 (rIn - rOut) ((!₂[ρ, 0, z] : Space) - l • z') *
          g (τ + 2 * Real.log l) z')
      ≤ ENNReal.ofReal (l ^ a) *
        ∫⁻ s : ℝ, vertKern rIn (rIn - rOut) (z - l * s) * vprof g (τ + 2 * Real.log l) s := by
  have hGm : Measurable (fun z' : Space => g (τ + 2 * Real.log l) z') :=
    hg.comp (measurable_const.prodMk measurable_id)
  have hφ : Measurable (fun q : ℝ × Space => ENNReal.ofReal q.1 *
      (IIIa.sepKd 0 (rIn - rOut) ((!₂[q.1, 0, z] : Space) - l • q.2) *
        g (τ + 2 * Real.log l) q.2)) := by
    refine Measurable.mul (ENNReal.measurable_ofReal.comp measurable_fst) ?_
    refine Measurable.mul ?_ (hGm.comp measurable_snd)
    refine (outRed_sepKd_meas _).comp ?_
    exact (by fun_prop : Continuous fun q : ℝ × Space =>
      (!₂[q.1, 0, z] : Space) - l • q.2).measurable
  -- pointwise bound in `z'` from `OutMajRho` and the support hypothesis
  have hpt : ∀ z' : Space, ∫⁻ ρ in Ioi r, ENNReal.ofReal ρ *
      (IIIa.sepKd 0 (rIn - rOut) ((!₂[ρ, 0, z] : Space) - l • z') * g (τ + 2 * Real.log l) z')
      ≤ vertKern rIn (rIn - rOut) (z - l * z' 2) * g (τ + 2 * Real.log l) z' := by
    intro z'
    by_cases hG : g (τ + 2 * Real.log l) z' = 0
    · simp [hG]
    · have hz : ϱ z' ≤ rOut := by
        by_contra h
        exact hG (hsupp (τ + 2 * Real.log l) z' (not_le.1 h))
      have hK := outMajRho rOut rIn hrO hrr r z l z' hr hl0 hl1 hz
      have hmeas : Measurable (fun ρ : ℝ => ENNReal.ofReal ρ *
          IIIa.sepKd 0 (rIn - rOut) ((!₂[ρ, 0, z] : Space) - l • z')) := by
        refine Measurable.mul ENNReal.measurable_ofReal ?_
        refine (outRed_sepKd_meas _).comp ?_
        exact (by fun_prop : Continuous fun ρ : ℝ => (!₂[ρ, 0, z] : Space) - l • z').measurable
      calc ∫⁻ ρ in Ioi r, ENNReal.ofReal ρ *
            (IIIa.sepKd 0 (rIn - rOut) ((!₂[ρ, 0, z] : Space) - l • z') * g (τ + 2 * Real.log l) z')
          = ∫⁻ ρ in Ioi r, (ENNReal.ofReal ρ *
              IIIa.sepKd 0 (rIn - rOut) ((!₂[ρ, 0, z] : Space) - l • z')) * g (τ + 2 * Real.log l) z' :=
            lintegral_congr fun ρ => by ring
        _ = (∫⁻ ρ in Ioi r, ENNReal.ofReal ρ *
              IIIa.sepKd 0 (rIn - rOut) ((!₂[ρ, 0, z] : Space) - l • z')) * g (τ + 2 * Real.log l) z' :=
            lintegral_mul_const _ hmeas
        _ ≤ vertKern rIn (rIn - rOut) (z - l * z' 2) * g (τ + 2 * Real.log l) z' :=
            mul_le_mul' hK le_rfl
  have hswap : ∫⁻ ρ in Ioi r, ENNReal.ofReal ρ *
        (∫⁻ z' : Space, IIIa.sepKd 0 (rIn - rOut) ((!₂[ρ, 0, z] : Space) - l • z') *
          g (τ + 2 * Real.log l) z')
      ≤ ∫⁻ s : ℝ, vertKern rIn (rIn - rOut) (z - l * s) * vprof g (τ + 2 * Real.log l) s := by
    calc ∫⁻ ρ in Ioi r, ENNReal.ofReal ρ *
          (∫⁻ z' : Space, IIIa.sepKd 0 (rIn - rOut) ((!₂[ρ, 0, z] : Space) - l • z') *
            g (τ + 2 * Real.log l) z')
        = ∫⁻ ρ in Ioi r, ∫⁻ z' : Space, ENNReal.ofReal ρ *
            (IIIa.sepKd 0 (rIn - rOut) ((!₂[ρ, 0, z] : Space) - l • z') *
              g (τ + 2 * Real.log l) z') :=
          lintegral_congr fun ρ => (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ = ∫⁻ z' : Space, ∫⁻ ρ in Ioi r, ENNReal.ofReal ρ *
            (IIIa.sepKd 0 (rIn - rOut) ((!₂[ρ, 0, z] : Space) - l • z') *
              g (τ + 2 * Real.log l) z') :=
          lintegral_lintegral_swap hφ.aemeasurable
      _ ≤ ∫⁻ z' : Space, vertKern rIn (rIn - rOut) (z - l * z' 2) * g (τ + 2 * Real.log l) z' :=
          lintegral_mono fun z' => hpt z'
      _ = ∫⁻ s : ℝ, vertKern rIn (rIn - rOut) (z - l * s) * vprof g (τ + 2 * Real.log l) s :=
          outRed_slice (fun s => vertKern rIn (rIn - rOut) (z - l * s))
            ((vertKern_measurable rIn (rIn - rOut)).comp (measurable_const.sub (measurable_const.mul measurable_id)))
            (fun z' => g (τ + 2 * Real.log l) z') hGm
  calc ∫⁻ ρ in Ioi r, ENNReal.ofReal ρ * (ENNReal.ofReal (l ^ a) *
        ∫⁻ z' : Space, IIIa.sepKd 0 (rIn - rOut) ((!₂[ρ, 0, z] : Space) - l • z') *
          g (τ + 2 * Real.log l) z')
      = ENNReal.ofReal (l ^ a) * ∫⁻ ρ in Ioi r, ENNReal.ofReal ρ *
          (∫⁻ z' : Space, IIIa.sepKd 0 (rIn - rOut) ((!₂[ρ, 0, z] : Space) - l • z') *
            g (τ + 2 * Real.log l) z') := by
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact lintegral_congr fun ρ => by ring
    _ ≤ ENNReal.ofReal (l ^ a) *
        ∫⁻ s : ℝ, vertKern rIn (rIn - rOut) (z - l * s) * vprof g (τ + 2 * Real.log l) s :=
        mul_le_mul' le_rfl hswap

/-- **(2) Reduction to the vertical profile** (`OutMajReduce`, source 4181-4192). -/
theorem outMajReduce : OutMajReduce := by
  intro a rOut rIn hrO hrr g hg hsupp τ r z hr
  unfold outMaj vertRed vertRedH
  unfold IIIa.sepDom
  have hJ := outRed_I_meas rOut rIn z τ g hg
  have hF : Measurable (fun q : ℝ × ℝ => ENNReal.ofReal q.1 * (ENNReal.ofReal (q.2 ^ a) *
      ∫⁻ z' : Space, IIIa.sepKd 0 (rIn - rOut) ((!₂[q.1, 0, z] : Space) - q.2 • z') *
        g (τ + 2 * Real.log q.2) z')) :=
    Measurable.mul (ENNReal.measurable_ofReal.comp measurable_fst)
      (Measurable.mul (ENNReal.measurable_ofReal.comp (measurable_snd.pow_const a)) hJ)
  calc _ = ∫⁻ ρ in Ioi r, ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal ρ * (ENNReal.ofReal (l ^ a) *
        ∫⁻ z' : Space, IIIa.sepKd 0 (rIn - rOut) ((!₂[ρ, 0, z] : Space) - l • z') *
          g (τ + 2 * Real.log l) z') :=
        lintegral_congr fun ρ => (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
    _ = ∫⁻ l in Ioo (0 : ℝ) 1, ∫⁻ ρ in Ioi r, ENNReal.ofReal ρ * (ENNReal.ofReal (l ^ a) *
        ∫⁻ z' : Space, IIIa.sepKd 0 (rIn - rOut) ((!₂[ρ, 0, z] : Space) - l • z') *
          g (τ + 2 * Real.log l) z') :=
        lintegral_lintegral_swap hF.aemeasurable
    _ ≤ ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ a) *
        ∫⁻ s : ℝ, vertKern rIn (rIn - rOut) (z - l * s) * vprof g (τ + 2 * Real.log l) s :=
        setLIntegral_mono' measurableSet_Ioo
          (fun l hl => outRed_fiber a rOut rIn hrO hrr g hg hsupp τ r z l hr hl.1 hl.2)

end UnforcedLeray.Short.PartIIIb.Concrete
