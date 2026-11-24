import UnforcedLeray.Short.PartI.Sub.PartI_T04_10_1
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel2.CutCont
import UnforcedLeray.Short.PartI.Tasks.TrainGlobalExistence.APLevel2.Static

/-!
# Part I, `PartI:T04/10/1/1`: qualitative jet bounds (`APLevel3Qual`)

Source of record: `the November 2 reference manuscript`, lines 285-288.

For a class solution, the cell integrals of the jets are measurable in `r` (joint continuity of the
jets on the strip, `apcc_jet_joint`, `apcc_curl_smooth`, and measurability of parameter integrals
over `[0,T] × cell`) and bounded (`jet_l2`, the curl estimate `iteratedFDeriv_curl_le`, the
uniform derivative bounds), hence integrable on `[0,T]`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.Short.PartI

open UnforcedLeray
open UnforcedLeray.Train (Vec)
open UnforcedLeray.Cyl (Plane)

/-- Integrability on `[0,T]` of a bounded cell-parameter integral of a jointly continuous
integrand. -/
theorem aq_integrableOn {c T : ℝ} (g : ℝ → Plane → ℝ)
    (hg : ContinuousOn (fun x : ℝ × Plane => g x.1 x.2) (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)))
    (K : ℝ) (hK : ∀ r ∈ Icc (0 : ℝ) T, ‖∫ z in Cyl.cell c, g r z‖ ≤ K) :
    IntegrableOn (fun r => ∫ z in Cyl.cell c, g r z) (Icc (0 : ℝ) T) := by
  have hsub : Icc (0 : ℝ) T ×ˢ Cyl.cell c ⊆ Icc (0 : ℝ) T ×ˢ (univ : Set Plane) :=
    prod_mono subset_rfl (subset_univ _)
  have h1 : AEStronglyMeasurable (fun x : ℝ × Plane => g x.1 x.2)
      (volume.restrict (Icc (0 : ℝ) T ×ˢ (univ : Set Plane))) :=
    hg.aestronglyMeasurable (measurableSet_Icc.prod MeasurableSet.univ)
  have h2 : AEStronglyMeasurable (fun x : ℝ × Plane => g x.1 x.2)
      ((volume.restrict (Icc (0 : ℝ) T)).prod (volume.restrict (Cyl.cell c))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact h1.mono_measure (Measure.restrict_mono hsub le_rfl)
  have h3 := h2.integral_prod_right'
  refine Integrable.mono' (integrableOn_const (C := K) (measure_Icc_lt_top.ne)) h3 ?_
  exact (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall hK)

theorem aq_vort_bound {ν c T : ℝ} {v : ℝ → Plane → Vec} {p : ℝ → Plane → ℝ}
    (hcls : IsAPrioriClass ν c T v p) (j : ℕ) :
    ∃ K : ℝ, ∀ r ∈ Icc (0 : ℝ) T, vortJet c j v r ≤ K := by
  obtain ⟨K, hK⟩ := hcls.jet_l2 (j + 1)
  refine ⟨‖APEllipticCaux.lam‖ ^ 2 * K, fun r hr => ?_⟩
  have hsm := hcls.classical.contDiff_slice hr
  have hint : ∀ i : ℕ, IntegrableOn (fun z => ‖iteratedFDeriv ℝ i (v r) z‖ ^ 2) (Cyl.cell c) :=
    fun i => ((hcls.jet_l2 i).choose_spec r hr).1
  unfold vortJet
  calc ∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ j (Cyl.curl (v r)) z‖ ^ 2
      ≤ ∫ z in Cyl.cell c, ‖APEllipticCaux.lam‖ ^ 2 * ‖iteratedFDeriv ℝ (j + 1) (v r) z‖ ^ 2 :=
        integral_mono (apL2s_curl_integrableOn hsm hint j) ((hK r hr).1.const_mul _)
          (fun z => by
            have h1 := APEllipticCaux.iteratedFDeriv_curl_le hsm j z
            have := pow_le_pow_left₀ (norm_nonneg _) h1 2
            simpa only [mul_pow] using this)
    _ = ‖APEllipticCaux.lam‖ ^ 2 * velJet c (j + 1) v r := integral_const_mul _ _
    _ ≤ ‖APEllipticCaux.lam‖ ^ 2 * K := mul_le_mul_of_nonneg_left (hK r hr).2 (sq_nonneg _)

theorem aq_vort_int {ν c T : ℝ} {v : ℝ → Plane → Vec} {p : ℝ → Plane → ℝ}
    (hcls : IsAPrioriClass ν c T v p) (j : ℕ) :
    IntegrableOn (fun r => vortJet c j v r) (Icc (0 : ℝ) T) := by
  obtain ⟨K, hK⟩ := aq_vort_bound hcls j
  have hv := hcls.classical.smooth_v
  have hjw : ContinuousOn (fun x : ℝ × Plane => iteratedFDeriv ℝ j (Cyl.curl (v x.1)) x.2)
      (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)) :=
    apcc_jet_joint hcls.pos (apcc_curl_smooth hcls.pos hv) j
  refine aq_integrableOn (c := c) (fun r z => ‖iteratedFDeriv ℝ j (Cyl.curl (v r)) z‖ ^ 2)
    (hjw.norm.pow 2) K (fun r hr => ?_)
  have hnn : 0 ≤ vortJet c j v r := integral_nonneg fun z => by positivity
  rw [show (∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ j (Cyl.curl (v r)) z‖ ^ 2) = vortJet c j v r from rfl,
    Real.norm_of_nonneg hnn]
  exact hK r hr

theorem aq_alg (a b c' e d3 L M1 M2 : ℝ) (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (_hc0 : 0 ≤ c')
    (he0 : 0 ≤ e) (hL : 0 ≤ L) (ha : a ≤ L * d3) (hc : c' ≤ L * b) (he : e ≤ M1) (hb : b ≤ M2) :
    a * (b * c' + 2 * (e * a)) ≤
      (L * M2 / 2 * L ^ 2 + 2 * M1 * L ^ 2) * d3 ^ 2 + (L * M2 / 2) * b ^ 2 := by
  have hM2 : 0 ≤ M2 := le_trans hb0 hb
  have hM1 : 0 ≤ M1 := le_trans he0 he
  have hd3 : 0 ≤ L * d3 := le_trans ha0 ha
  have h1 : a * (b * c') ≤ a * (b * (L * b)) := by gcongr
  have h2 : a * (b * (L * b)) ≤ a * b * (L * M2) := by
    have : b * (L * b) ≤ b * (L * M2) := by gcongr
    calc a * (b * (L * b)) ≤ a * (b * (L * M2)) := by gcongr
      _ = a * b * (L * M2) := by ring
  have h3 : a * b ≤ (a ^ 2 + b ^ 2) / 2 := by nlinarith [sq_nonneg (a - b)]
  have h4 : a ^ 2 ≤ L ^ 2 * d3 ^ 2 := by
    calc a ^ 2 ≤ (L * d3) ^ 2 := by gcongr
      _ = L ^ 2 * d3 ^ 2 := by ring
  have h5 : e * a * a ≤ M1 * (L ^ 2 * d3 ^ 2) := by
    calc e * a * a = e * a ^ 2 := by ring
      _ ≤ M1 * a ^ 2 := by gcongr
      _ ≤ M1 * (L ^ 2 * d3 ^ 2) := by gcongr
  have h6 : a * b * (L * M2) ≤ (a ^ 2 + b ^ 2) / 2 * (L * M2) := by gcongr
  have h7 : (a ^ 2 + b ^ 2) / 2 * (L * M2) ≤
      (L ^ 2 * d3 ^ 2 + b ^ 2) / 2 * (L * M2) := by gcongr
  have : a * (b * c' + 2 * (e * a)) = a * (b * c') + 2 * (e * a * a) := by ring
  rw [this]
  nlinarith [h1, h2, h6, h7, h5]

theorem aq_comm_int {ν c T : ℝ} {v : ℝ → Plane → Vec} {p : ℝ → Plane → ℝ}
    (hcls : IsAPrioriClass ν c T v p) :
    IntegrableOn (fun r => commJet2 c v r) (Icc (0 : ℝ) T) := by
  have hT := hcls.pos
  have hv := hcls.classical.smooth_v
  obtain ⟨M1, hM1⟩ := hcls.bounded 1
  obtain ⟨M2, hM2⟩ := hcls.bounded 2
  obtain ⟨K2, hK2⟩ := hcls.jet_l2 2
  obtain ⟨K3, hK3⟩ := hcls.jet_l2 3
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT.le⟩
  have hM1' : 0 ≤ M1 := le_trans (norm_nonneg _) (hM1 0 h0 0)
  have hM2' : 0 ≤ M2 := le_trans (norm_nonneg _) (hM2 0 h0 0)
  set L : ℝ := ‖APEllipticCaux.lam‖ with hLdef
  have hL : 0 ≤ L := norm_nonneg (APEllipticCaux.lam)
  set C0 : ℝ := L * M2 / 2 * L ^ 2 + 2 * M1 * L ^ 2 with hC0
  set C1 : ℝ := L * M2 / 2 with hC1
  have hC0' : 0 ≤ C0 := by positivity
  have hC1' : 0 ≤ C1 := by positivity
  have hjv : ∀ j : ℕ, ContinuousOn (fun x : ℝ × Plane => iteratedFDeriv ℝ j (v x.1) x.2)
      (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)) := fun j => apcc_jet_joint hT hv j
  have hjw : ∀ j : ℕ, ContinuousOn
      (fun x : ℝ × Plane => iteratedFDeriv ℝ j (Cyl.curl (v x.1)) x.2)
      (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)) :=
    fun j => apcc_jet_joint hT (apcc_curl_smooth hT hv) j
  have hcont : ContinuousOn (fun x : ℝ × Plane =>
      ‖iteratedFDeriv ℝ 2 (Cyl.curl (v x.1)) x.2‖ *
        (‖iteratedFDeriv ℝ 2 (v x.1) x.2‖ * ‖iteratedFDeriv ℝ 1 (Cyl.curl (v x.1)) x.2‖ +
          2 * (‖iteratedFDeriv ℝ 1 (v x.1) x.2‖ * ‖iteratedFDeriv ℝ 2 (Cyl.curl (v x.1)) x.2‖)))
      (Icc (0 : ℝ) T ×ˢ (univ : Set Plane)) :=
    (hjw 2).norm.mul (((hjv 2).norm.mul (hjw 1).norm).add
      (continuousOn_const.mul ((hjv 1).norm.mul (hjw 2).norm)))
  have hbound : ∀ r ∈ Icc (0 : ℝ) T,
      ∫ z in Cyl.cell c, ‖iteratedFDeriv ℝ 2 (Cyl.curl (v r)) z‖ *
        (‖iteratedFDeriv ℝ 2 (v r) z‖ * ‖iteratedFDeriv ℝ 1 (Cyl.curl (v r)) z‖ +
          2 * (‖iteratedFDeriv ℝ 1 (v r) z‖ * ‖iteratedFDeriv ℝ 2 (Cyl.curl (v r)) z‖))
      ≤ C0 * K3 + C1 * K2 := by
    intro r hr
    have hsm := hcls.classical.contDiff_slice hr
    have hi3 := (hK3 r hr).1
    have hi2 := (hK2 r hr).1
    have hb : Integrable (fun z => C0 * ‖iteratedFDeriv ℝ 3 (v r) z‖ ^ 2 +
        C1 * ‖iteratedFDeriv ℝ 2 (v r) z‖ ^ 2) (volume.restrict (Cyl.cell c)) :=
      (hi3.const_mul C0).add (hi2.const_mul C1)
    calc _ ≤ ∫ z in Cyl.cell c, (C0 * ‖iteratedFDeriv ℝ 3 (v r) z‖ ^ 2 +
              C1 * ‖iteratedFDeriv ℝ 2 (v r) z‖ ^ 2) := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => by positivity)
            hb (Filter.Eventually.of_forall fun z => ?_)
          have hca := APEllipticCaux.iteratedFDeriv_curl_le hsm 2 z
          have hcb := APEllipticCaux.iteratedFDeriv_curl_le hsm 1 z
          exact aq_alg _ _ _ _ (‖iteratedFDeriv ℝ 3 (v r) z‖) L M1 M2 (norm_nonneg _)
            (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hL
            hca (by simpa using hcb) (hM1 r hr z) (hM2 r hr z)
      _ = C0 * velJet c 3 v r + C1 * velJet c 2 v r := by
          rw [integral_add (hi3.const_mul C0) (hi2.const_mul C1), integral_const_mul,
            integral_const_mul]
          rfl
      _ ≤ C0 * K3 + C1 * K2 := by
          gcongr
          · exact (hK3 r hr).2
          · exact (hK2 r hr).2
  have hI := aq_integrableOn (c := c)
    (fun r z => ‖iteratedFDeriv ℝ 2 (Cyl.curl (v r)) z‖ *
        (‖iteratedFDeriv ℝ 2 (v r) z‖ * ‖iteratedFDeriv ℝ 1 (Cyl.curl (v r)) z‖ +
          2 * (‖iteratedFDeriv ℝ 1 (v r) z‖ * ‖iteratedFDeriv ℝ 2 (Cyl.curl (v r)) z‖)))
    hcont (C0 * K3 + C1 * K2) (fun r hr => by
      rw [Real.norm_of_nonneg (integral_nonneg fun z => by positivity)]
      exact hbound r hr)
  exact hI.const_mul 16

/-- **`APLevel3Qual`** (lines 285-288). -/
theorem apLevel3Qual : APLevel3Qual := by
  intro ν c T v p hν hc hcls
  refine ⟨aq_vort_int hcls 3, aq_comm_int hcls, aq_vort_int hcls 2, ?_⟩
  obtain ⟨K, hK⟩ := aq_vort_bound hcls 2
  exact ⟨K, hK⟩

end UnforcedLeray.Short.PartI
