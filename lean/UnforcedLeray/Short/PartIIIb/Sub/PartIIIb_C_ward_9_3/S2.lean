import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_ward_9_3
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.AnnulusFubiniL2
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.VertYoungL2.Phase
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Sub.PartIIIb_C_rep_5_2_2.VertYoungL2.Kern
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_4_2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_4_3
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_4_4
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_4_5.Of
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_4_5.L2
import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_rep_2_4_5.L3
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false

noncomputable section

open Filter Set MeasureTheory UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

namespace WardS2

theorem vk1_norm (rIn D : ℝ) (hr : 0 < rIn) (hD : 0 < D) :
    lqNorm1 1 (vertKern rIn D) = ENNReal.ofReal (Real.pi / 2 * (rIn / D) * D⁻¹) := by
  have hI : ∫⁻ u : ℝ, ENNReal.ofReal ((1 + u ^ 2)⁻¹) = ENNReal.ofReal Real.pi := by
    rw [← ofReal_integral_eq_lintegral_ofReal integrable_inv_one_add_sq
      (ae_of_all _ fun x => by positivity), integral_univ_inv_one_add_sq]
  have hpt : ∀ u : ℝ, vertKern rIn D (D * u) =
      ENNReal.ofReal (rIn / (2 * D ^ 3)) * ENNReal.ofReal ((1 + u ^ 2)⁻¹) := by
    intro u
    unfold vertKern
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  unfold lqNorm1
  simp only [ENNReal.rpow_one, div_one]
  rw [vk7_lintegral_scale hD _ (vertKern_measurable rIn D)]
  simp_rw [hpt]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hI, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul hD.le]
  congr 1
  field_simp

/-- Scaled Young `L² * L¹ → L²` for the vertical kernel. -/
theorem vertScaled1 (rIn D : ℝ) (hrIn : 0 < rIn) (hD0 : 0 < D) (l : ℝ) (hl0 : 0 < l)
    (g' : ℝ → ℝ≥0∞) (hg' : Measurable g') :
    lqNorm1 2 (fun z => ∫⁻ s : ℝ, vertKern rIn D (z - l * s) * g' s) ≤
      ENNReal.ofReal (Real.pi / 2 * (rIn / D) * D⁻¹) *
        (ENNReal.ofReal (l ^ (-(1 / 2) : ℝ)) * lqNorm1 2 g') := by
  have hepos : 0 < Real.pi / 2 * (rIn / D) * D⁻¹ := by positivity
  have hlpos : 0 < l ^ (-(1 / 2) : ℝ) := by positivity
  by_cases htop : lqNorm1 2 g' = ⊤
  · rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hlpos).ne',
      ENNReal.mul_top (ENNReal.ofReal_pos.mpr hepos).ne']
    exact le_top
  · obtain ⟨hD1, hD2⟩ := vertDil l hl0
    set S := vertKern rIn D with hS
    set gl : ℝ → ℝ≥0∞ := fun w => g' (l⁻¹ * w) with hgl
    have hglm : Measurable gl := hg'.comp (measurable_const.mul measurable_id)
    have hSm : Measurable S := vertKern_measurable rIn D
    have hSt : ∀ x, S x ≠ ⊤ := fun x => by rw [hS]; unfold vertKern; exact ENNReal.ofReal_ne_top
    have hdil : lqNorm1 2 gl = ENNReal.ofReal (l ^ (1 / (2 : ℝ))) * lqNorm1 2 g' :=
      hD2 _ (by norm_num) g'
    have hgltop : lqNorm1 2 gl ≠ ⊤ := by
      rw [hdil]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top htop
    have hfun : (fun z => ∫⁻ s : ℝ, S (z - l * s) * g' s) =
        fun z => ENNReal.ofReal l⁻¹ * ∫⁻ w : ℝ, S (z - w) * gl w := funext fun z => hD1 S g' z
    rw [hfun, lqNorm1_const_mul (by norm_num) ENNReal.ofReal_ne_top]
    have hy := vert1DYoung S gl hSm hSt hglm 1 2 2 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hgltop
    have hid : ENNReal.ofReal (l ^ (-(1 / 2) : ℝ)) =
        ENNReal.ofReal l⁻¹ * ENNReal.ofReal (l ^ (1 / (2 : ℝ))) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [← Real.rpow_neg_one, ← Real.rpow_add hl0]
      norm_num
    calc ENNReal.ofReal l⁻¹ * lqNorm1 2 (fun z => ∫⁻ w : ℝ, S (z - w) * gl w)
        ≤ ENNReal.ofReal l⁻¹ * (lqNorm1 1 S * lqNorm1 2 gl) := by gcongr
      _ = _ := by
        rw [hS, vk1_norm rIn D hrIn hD0, hdil, hid]
        ring

/-- Vertical Young `L² * L¹ → L²` with the dilation integral (`p = 2` analogue of `vertYoungL2`). -/
theorem vertYoungL2L2 (a rIn D P : ℝ) (ha : 1 < a) (hD0 : 0 < D) (hrIn : 0 < rIn) (hP : 0 < P)
    (h : ℝ → ℝ → ℝ≥0∞) (hhm : Measurable (Function.uncurry h))
    (hper : ∀ τ s, h (τ + P) s = h τ s) :
    ltauLq1 P 2 (vertRedH a rIn D h) ≤
      ENNReal.ofReal (Real.pi / 2 * (22 / 19) * (rIn / D) * D⁻¹) * ltauLq1 P 2 h := by
  set K : ℝ := Real.pi / 2 * (rIn / D) * D⁻¹ with hK
  have hGper : ∀ s, lqNorm1 2 (h (s + P)) = lqNorm1 2 (h s) := fun s => by
    rw [show h (s + P) = h s from funext (hper s)]
  have hGm : Measurable (fun σ => lqNorm1 2 (h σ)) := by
    have h1 : Measurable (fun σ => ∫⁻ y, h σ y ^ (2 : ℝ)) := by
      have h2 : Measurable (fun x : ℝ × ℝ => h x.1 x.2 ^ (2 : ℝ)) := hhm.pow_const _
      exact h2.lintegral_prod_right'
    unfold lqNorm1
    exact h1.pow_const _
  have hhτ : ∀ (τ l : ℝ), Measurable (h (τ + 2 * Real.log l)) := fun τ l =>
    hhm.comp (measurable_const.prodMk measurable_id)
  have hpt : ∀ τ, lqNorm1 2 (vertRedH a rIn D h τ) ≤ ∫⁻ l in Ioo (0 : ℝ) 1,
      (ENNReal.ofReal K * ENNReal.ofReal (l ^ (a + -(1 / 2)))) *
        lqNorm1 2 (h (τ + 2 * Real.log l)) := by
    intro τ
    refine (vertMinkowski a rIn D 2 (by norm_num) h hhm τ).trans ?_
    refine setLIntegral_mono' measurableSet_Ioo (fun l hl => ?_)
    have hY := vertScaled1 rIn D hrIn hD0 l hl.1 (h (τ + 2 * Real.log l)) (hhτ τ l)
    calc ENNReal.ofReal (l ^ a) * lqNorm1 2
          (fun z => ∫⁻ s : ℝ, vertKern rIn D (z - l * s) * h (τ + 2 * Real.log l) s)
        ≤ ENNReal.ofReal (l ^ a) * (ENNReal.ofReal K *
            (ENNReal.ofReal (l ^ (-(1 / 2) : ℝ)) * lqNorm1 2 (h (τ + 2 * Real.log l)))) :=
          mul_le_mul' le_rfl hY
      _ = (ENNReal.ofReal K * ENNReal.ofReal (l ^ (a + -(1 / 2)))) *
            lqNorm1 2 (h (τ + 2 * Real.log l)) := by
          rw [Real.rpow_add hl.1, ENNReal.ofReal_mul (Real.rpow_nonneg hl.1.le _)]
          ring
  have hBm : Measurable (Function.uncurry (fun (τ l : ℝ) =>
      (ENNReal.ofReal K * ENNReal.ofReal (l ^ (a + -(1 / 2)))) *
        lqNorm1 2 (h (τ + 2 * Real.log l)))) := by
    have m1 : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (p.2 ^ (a + -(1 / 2)))) :=
      ENNReal.measurable_ofReal.comp (measurable_snd.pow_const _)
    have m2 : Measurable (fun p : ℝ × ℝ => lqNorm1 2 (h (p.1 + 2 * Real.log p.2))) :=
      hGm.comp (measurable_fst.add (measurable_const.mul (Real.measurable_log.comp measurable_snd)))
    exact (measurable_const.mul m1).mul m2
  haveI : IsFiniteMeasure (Rep522Phase.muP P) := muP_finite hP
  have hMink := UnforcedLeray.PlanarBS.Conv.eLpNorm_lintegral_le (μ := Rep522Phase.muP P)
    (ν := volume.restrict (Ioo (0 : ℝ) 1))
    (F := fun (τ l : ℝ) => (ENNReal.ofReal K * ENNReal.ofReal (l ^ (a + -(1 / 2)))) *
        lqNorm1 2 (h (τ + 2 * Real.log l)))
    hBm.aemeasurable (p := 2) (by norm_num) (by norm_num)
  have hGl : ∀ l : ℝ, Measurable (fun τ => lqNorm1 2 (h (τ + 2 * Real.log l))) :=
    fun l => hGm.comp (measurable_id.add_const _)
  calc ltauLq1 P 2 (vertRedH a rIn D h)
      = eLpNorm (fun τ => lqNorm1 2 (vertRedH a rIn D h τ)) 2 (Rep522Phase.muP P) :=
        ltau_eq_eLp2 (P := P) (q := 2) (vertRedH a rIn D h)
    _ ≤ eLpNorm (fun τ => ∫⁻ l in Ioo (0 : ℝ) 1,
          (ENNReal.ofReal K * ENNReal.ofReal (l ^ (a + -(1 / 2)))) *
            lqNorm1 2 (h (τ + 2 * Real.log l))) 2 (Rep522Phase.muP P) :=
        eLpNorm_mono_enorm (fun τ => by
          rw [enorm_eq_self, enorm_eq_self]
          exact hpt τ)
    _ ≤ ∫⁻ l in Ioo (0 : ℝ) 1, eLpNorm (fun τ =>
          (ENNReal.ofReal K * ENNReal.ofReal (l ^ (a + -(1 / 2)))) *
            lqNorm1 2 (h (τ + 2 * Real.log l))) 2 (Rep522Phase.muP P) := hMink
    _ = ∫⁻ l in Ioo (0 : ℝ) 1, (ENNReal.ofReal K * ENNReal.ofReal (l ^ (a + -(1 / 2)))) *
          eLpNorm (fun σ => lqNorm1 2 (h σ)) 2 (Rep522Phase.muP P) := by
        refine lintegral_congr fun l => ?_
        rw [eLp2_const_mul P _ (fun τ => lqNorm1 2 (h (τ + 2 * Real.log l))) (hGl l)]
        rw [eLp2_shift hP (G := fun σ => lqNorm1 2 (h σ)) hGper (2 * Real.log l)]
    _ = (ENNReal.ofReal K * eLpNorm (fun σ => lqNorm1 2 (h σ)) 2 (Rep522Phase.muP P)) *
          ∫⁻ l in Ioo (0 : ℝ) 1, ENNReal.ofReal (l ^ (a + -(1 / 2))) := by
        have hm : Measurable (fun l : ℝ => ENNReal.ofReal (l ^ (a + -(1 / 2)))) :=
          ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)
        have e : ∀ l : ℝ, (ENNReal.ofReal K * ENNReal.ofReal (l ^ (a + -(1 / 2)))) *
              eLpNorm (fun σ => lqNorm1 2 (h σ)) 2 (Rep522Phase.muP P) =
            (ENNReal.ofReal K * eLpNorm (fun σ => lqNorm1 2 (h σ)) 2 (Rep522Phase.muP P)) *
              ENNReal.ofReal (l ^ (a + -(1 / 2))) := fun l => by ring
        simp_rw [e]
        exact lintegral_const_mul _ hm
    _ ≤ (ENNReal.ofReal K * eLpNorm (fun σ => lqNorm1 2 (h σ)) 2 (Rep522Phase.muP P)) *
          ENNReal.ofReal (22 / 19) := by
        gcongr
        exact phase_int_le (by linarith)
    _ = ENNReal.ofReal (Real.pi / 2 * (22 / 19) * (rIn / D) * D⁻¹) * ltauLq1 P 2 h := by
        rw [ltau_eq_eLp2 (P := P) (q := 2) h]
        have hcon : ENNReal.ofReal (Real.pi / 2 * (22 / 19) * (rIn / D) * D⁻¹) =
            ENNReal.ofReal K * ENNReal.ofReal (22 / 19) := by
          rw [← ENNReal.ofReal_mul (by positivity), hK]
          congr 1
          ring
        rw [hcon]
        ring

/-- Cauchy-Schwarz on one horizontal slice (exponent `2` analogue of `slice_holder`). -/
theorem slice_cs (G : Space → ℝ≥0∞) (hG : Measurable G) (r : ℝ) (hr : 0 ≤ r)
    (hs : ∀ z, r < ϱ z → G z = 0) (s : ℝ) :
    ∫⁻ x : ℝ, ∫⁻ y : ℝ, G !₂[x, y, s] ≤
      ENNReal.ofReal (Real.sqrt (Real.pi * r ^ 2)) *
        (∫⁻ q : ℝ × ℝ, G !₂[q.1, q.2, s] ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  set Gs : ℝ × ℝ → ℝ≥0∞ := fun q => G !₂[q.1, q.2, s] with hGs
  have hGsm : Measurable Gs := hG.comp (measurable_slab s)
  set D : Set (ℝ × ℝ) := {q | q.1 ^ 2 + q.2 ^ 2 ≤ r ^ 2} with hD
  have hDm : MeasurableSet D := measurableSet_le (by fun_prop) measurable_const
  have h1 : ∫⁻ x : ℝ, ∫⁻ y : ℝ, G !₂[x, y, s] = ∫⁻ q : ℝ × ℝ, (Gs * D.indicator (1 : ℝ × ℝ → ℝ≥0∞)) q := by
    rw [Measure.volume_eq_prod, lintegral_prod _ (hGsm.mul (measurable_one.indicator hDm : Measurable (D.indicator (1 : ℝ × ℝ → ℝ≥0∞)))).aemeasurable]
    refine lintegral_congr fun x => lintegral_congr fun y => ?_
    simp only [Pi.mul_apply, hGs]
    by_cases hq : (x, y) ∈ D
    · simp [Set.indicator_of_mem hq]
    · have : r < ϱ !₂[x, y, s] := by
        unfold ϱ
        have hq' : r ^ 2 < x ^ 2 + y ^ 2 := by simpa [hD] using hq
        simp only [PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
        exact (Real.lt_sqrt hr).2 hq'
      simp [Set.indicator_of_notMem hq, hs _ this]
  have hconj : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]; constructor <;> norm_num
  have hk : (∫⁻ q : ℝ × ℝ, (D.indicator (1 : ℝ × ℝ → ℝ≥0∞) q) ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) =
      ENNReal.ofReal (Real.sqrt (Real.pi * r ^ 2)) := by
    have e : (fun q : ℝ × ℝ => (D.indicator (1 : ℝ × ℝ → ℝ≥0∞) q) ^ (2 : ℝ)) =
        D.indicator 1 := by
      funext q
      by_cases hq : q ∈ D
      · simp [Set.indicator_of_mem hq]
      · simp [Set.indicator_of_notMem hq]
    rw [e, lintegral_indicator_one hDm, hD, volume_disk r hr,
      ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), Real.sqrt_eq_rpow]
  rw [h1]
  refine (ENNReal.lintegral_mul_le_Lp_mul_Lq volume hconj hGsm.aemeasurable
    (measurable_one.indicator hDm).aemeasurable).trans (le_of_eq ?_)
  rw [hk, mul_comm]

theorem slab_cs (G : Space → ℝ≥0∞) (hG : Measurable G) (r : ℝ) (hr : 0 ≤ r)
    (hs : ∀ z, r < ϱ z → G z = 0) :
    (∫⁻ s : ℝ, (∫⁻ x : ℝ, ∫⁻ y : ℝ, G !₂[x, y, s]) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (Real.sqrt (Real.pi * r ^ 2)) *
        (∫⁻ z : Space, G z ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  set A := ENNReal.ofReal (Real.sqrt (Real.pi * r ^ 2)) with hA
  set F : Space → ℝ≥0∞ := fun z => G z ^ (2 : ℝ) with hF
  have hFm : Measurable F := hG.pow_const _
  have hint : ∫⁻ s : ℝ, (∫⁻ q : ℝ × ℝ, F !₂[q.1, q.2, s]) = ∫⁻ z : Space, F z := by
    rw [lintegral_space_xys F hFm]
    have := lintegral_xys_swap (fun t => F !₂[t.1, t.2.1, t.2.2])
      (hFm.comp (by
        have : Continuous fun t : ℝ × ℝ × ℝ => (!₂[t.1, t.2.1, t.2.2] : Space) := by fun_prop
        exact this.measurable))
    simp only at this
    rw [this]
    refine lintegral_congr fun s => ?_
    rw [Measure.volume_eq_prod, lintegral_prod (fun q : ℝ × ℝ => F !₂[q.1, q.2, s]) ((hFm.comp (measurable_slab s)).aemeasurable)]
  have hpt : ∀ s : ℝ, (∫⁻ x : ℝ, ∫⁻ y : ℝ, G !₂[x, y, s]) ^ (2 : ℝ) ≤
      A ^ (2 : ℝ) * ∫⁻ q : ℝ × ℝ, F !₂[q.1, q.2, s] := by
    intro s
    have h := slice_cs G hG r hr hs s
    have h2 := ENNReal.rpow_le_rpow h (by norm_num : (0 : ℝ) ≤ 2)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul] at h2
    norm_num at h2
    simpa [hF] using h2
  calc (∫⁻ s : ℝ, (∫⁻ x : ℝ, ∫⁻ y : ℝ, G !₂[x, y, s]) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
      ≤ (∫⁻ s : ℝ, A ^ (2 : ℝ) * ∫⁻ q : ℝ × ℝ, F !₂[q.1, q.2, s]) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow (lintegral_mono hpt) (by norm_num)
    _ = A * (∫⁻ z : Space, G z ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
        rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
          ENNReal.ofReal_ne_top)]
        have := hint
        simp only [hF] at this
        rw [this, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul]
        norm_num [hA]

theorem vprofCS (rO P : ℝ) (hr : 0 ≤ rO) (hP : 0 < P) (g : ℝ → Space → ℝ≥0∞)
    (hg : Measurable (Function.uncurry g)) (hsupp : ∀ τ z, rO < ϱ z → g τ z = 0) :
    ltauLq1 P 2 (vprof g) ≤
      ENNReal.ofReal (Real.sqrt (Real.pi * rO ^ 2)) * IIIa.ltauLq P 2 g := by
  set A := ENNReal.ofReal (Real.sqrt (Real.pi * rO ^ 2)) with hA
  have hmeas : ∀ τ, Measurable (g τ) := fun τ => hg.comp (measurable_const.prodMk measurable_id)
  have hpt : ∀ τ : ℝ, (∫⁻ s : ℝ, vprof g τ s ^ (2 : ℝ)) ^ (2 / (2 : ℝ)) ≤
      A ^ (2 : ℝ) * (∫⁻ y : Space, g τ y ^ (2 : ℝ)) ^ (2 / (2 : ℝ)) := by
    intro τ
    have h := slab_cs (g τ) (hmeas τ) rO hr (hsupp τ)
    have h2 := ENNReal.rpow_le_rpow h (by norm_num : (0 : ℝ) ≤ 2)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul, ← ENNReal.rpow_mul] at h2
    have e : (1 / 2 : ℝ) * 2 = 2 / (2 : ℝ) := by norm_num
    rw [e] at h2
    exact h2
  unfold ltauLq1 IIIa.ltauLq
  calc ((ENNReal.ofReal P)⁻¹ * ∫⁻ τ in Ioc 0 P, (∫⁻ s : ℝ, vprof g τ s ^ (2 : ℝ)) ^ (2 / (2 : ℝ))) ^
        (1 / 2 : ℝ)
      ≤ ((ENNReal.ofReal P)⁻¹ * ∫⁻ τ in Ioc 0 P, A ^ (2 : ℝ) *
          (∫⁻ y : Space, g τ y ^ (2 : ℝ)) ^ (2 / (2 : ℝ))) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow (mul_le_mul' le_rfl (lintegral_mono hpt)) (by norm_num)
    _ = A * ((ENNReal.ofReal P)⁻¹ * ∫⁻ τ in Ioc 0 P,
          (∫⁻ y : Space, g τ y ^ (2 : ℝ)) ^ (2 / (2 : ℝ))) ^ (1 / 2 : ℝ) := by
        rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by norm_num)
          ENNReal.ofReal_ne_top), mul_left_comm, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
          ← ENNReal.rpow_mul]
        norm_num [hA]

end WardS2

/-- **Sub 2** (`p = 2` outward primitive majorant on the annulus). -/
theorem outMajAnnulusL2P2_proved : OutMajAnnulusL2P2 := by
  intro ν R a hν hR ha
  have hF := annulusFubiniL2
  unfold AnnulusFubiniL2 at hF
  have hs1 : Real.sqrt (5 / 6 : ℝ) < 1 := by
    have h := Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 5 / 6) (by norm_num : (5 / 6 : ℝ) < 1)
    rwa [Real.sqrt_one] at h
  have hs0 : 0 ≤ Real.sqrt (5 / 6 : ℝ) := Real.sqrt_nonneg _
  have hd0 : 0 < 1 - Real.sqrt (5 / 6 : ℝ) := by linarith
  have hsν : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have hrIn0 : 0 < R * Real.sqrt ν := mul_pos hR hsν
  have hsq : Real.sqrt (5 * ν / 6) = Real.sqrt (5 / 6 : ℝ) * Real.sqrt ν := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 5 / 6)]
    congr 1; ring
  have hrO : R * Real.sqrt (5 * ν / 6) = Real.sqrt (5 / 6 : ℝ) * (R * Real.sqrt ν) := by
    rw [hsq]; ring
  have hD : transGap ν R = (1 - Real.sqrt (5 / 6 : ℝ)) * (R * Real.sqrt ν) := by
    unfold transGap; rw [hrO]; ring
  have hD0 : 0 < transGap ν R := by rw [hD]; exact mul_pos hd0 hrIn0
  have hrO0 : 0 ≤ R * Real.sqrt (5 * ν / 6) := by
    rw [hrO]; exact mul_nonneg hs0 hrIn0.le
  have hrOlt : R * Real.sqrt (5 * ν / 6) < R * Real.sqrt ν := by
    have := mul_lt_mul_of_pos_right hs1 hrIn0
    rw [hrO]; linarith
  set A1 : ℝ := (Real.pi * ν * R ^ 2 / 4) ^ (1 / 2 : ℝ) with hA1
  set A2 : ℝ := Real.pi / 2 * (22 / 19) * ((R * Real.sqrt ν) / transGap ν R) * (transGap ν R)⁻¹
    with hA2
  set A3 : ℝ := Real.sqrt (Real.pi * (R * Real.sqrt (5 * ν / 6)) ^ 2) with hA3
  have hA10 : 0 ≤ A1 := Real.rpow_nonneg (by positivity) _
  have hA20 : 0 ≤ A2 := by positivity
  have hA30 : 0 ≤ A3 := Real.sqrt_nonneg _
  refine ⟨A1 * A2 * A3, by positivity, ?_⟩
  intro P hP0 g hg hper hsupp
  have hVM := vertMeasurable g hg
  have hunc : Measurable (Function.uncurry (vertRed a (R * Real.sqrt ν) (transGap ν R) g)) :=
    hVM.2 a (R * Real.sqrt ν) (transGap ν R)
  have hvm : Measurable (Function.uncurry (vprof g)) := hVM.1
  have hvper : ∀ τ' s, vprof g (τ' + P) s = vprof g τ' s := by
    intro τ' s
    simp only [vprof, hper]
  have stepA : IIIa.ltauLq P 2 (fun τ => (streamAnn ν R).indicator
      (fun y => outMaj a (transGap ν R) g τ (ϱ y) (y 2))) ≤
      IIIa.ltauLq P 2 (fun τ => (streamAnn ν R).indicator
      (fun y => vertRed a (R * Real.sqrt ν) (transGap ν R) g τ (y 2))) := by
    refine IIIa.ltauLq_mono P 2 (by norm_num) (fun τ y => ?_)
    dsimp only
    by_cases hy : y ∈ streamAnn ν R
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
      exact outMajReduce a (R * Real.sqrt (5 * ν / 6)) (R * Real.sqrt ν) hrO0 hrOlt g hg hsupp τ
        (ϱ y) (y 2) hy.1
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]
  have stepB := hF ν R P hν hR hP0 (vertRed a (R * Real.sqrt ν) (transGap ν R) g) hunc
  have stepC := WardS2.vertYoungL2L2 a (R * Real.sqrt ν) (transGap ν R) P ha hD0 hrIn0 hP0
    (vprof g) hvm hvper
  have stepD := WardS2.vprofCS (R * Real.sqrt (5 * ν / 6)) P hrO0 hP0 g hg hsupp
  calc IIIa.ltauLq P 2 (fun τ => (streamAnn ν R).indicator
        (fun y => outMaj a (transGap ν R) g τ (ϱ y) (y 2)))
      ≤ IIIa.ltauLq P 2 (fun τ => (streamAnn ν R).indicator
        (fun y => vertRed a (R * Real.sqrt ν) (transGap ν R) g τ (y 2))) := stepA
    _ = ENNReal.ofReal A1 * ltauLq1 P 2 (vertRed a (R * Real.sqrt ν) (transGap ν R) g) := stepB
    _ ≤ ENNReal.ofReal A1 * (ENNReal.ofReal A2 * ltauLq1 P 2 (vprof g)) :=
        mul_le_mul_of_nonneg_left stepC (by positivity)
    _ ≤ ENNReal.ofReal A1 * (ENNReal.ofReal A2 * (ENNReal.ofReal A3 * IIIa.ltauLq P 2 g)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left stepD (by positivity))
          (by positivity)
    _ = ENNReal.ofReal (A1 * A2 * A3) * IIIa.ltauLq P 2 g := by
        rw [ENNReal.ofReal_mul (mul_nonneg hA10 hA20), ENNReal.ofReal_mul hA10]
        ring

end UnforcedLeray.Short.PartIIIb.Concrete

end
