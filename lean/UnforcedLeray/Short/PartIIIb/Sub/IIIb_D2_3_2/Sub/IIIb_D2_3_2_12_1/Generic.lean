import UnforcedLeray.Short.PartIIIb.NearInst.Link.Pins.Proofs.PairFunctional.PairLinear
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.WeakDmuAdd
import UnforcedLeray.Short.PartIIIb.Concrete.PhysLayer.Sub.PartIIIb_D2_4_1
import UnforcedLeray.Short.PartIIIb.Concrete.ReturnOps

/-!
# Generic continuity of the phase pairing of the physical velocity (source 2683-2689, 4284-4286)

For a phase test `H` (period `2εc`, bounded spatial support, no solenoidal condition) the map
`f ↦ ⟨H, 𝒩_v f⟩` is a continuous linear functional on `L²(m)` whenever `ageμ c (-3/2) ≤ K • m`
with `K ≠ 0, ∞`. The bound comes from Cauchy-Schwarz on the phase cell (as in `PairBound`,
which needs a solenoidal test and so cannot be reused), `eLpNorm_liftFun`, and
`fwuB_norm_velPhys`. Linearity is the `PairLinear` argument, applied to phase tests.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest phaseCell
  pairF_eq_restrictedProductIntegral pairF_add_right_of_integrable)

/-- The body measure dominates `ageμ c (-3/2)` up to a finite nonzero constant (the density
`π g⁻²` is bounded below, source 2683-2689). -/
theorem ageμ_le_body (c γ ν : ℝ) (hν : 0 < ν) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ K ≠ 0 ∧ ageμ c (-3 / 2) ≤ K • bodyMeasure c γ ν := by
  set e : ℝ := Real.exp (-(|γ| / ν)) with he
  have he0 : 0 < e := Real.exp_pos _
  set δ : ℝ≥0∞ := ENNReal.ofReal (Real.pi * e ^ 2) with hδdef
  have hδ0 : δ ≠ 0 := (ENNReal.ofReal_pos.2 (by positivity)).ne'
  have hδtop : δ ≠ ∞ := ENNReal.ofReal_ne_top
  have hlow : δ • ageμ c (-3 / 2) ≤ bodyMeasure c γ ν := by
    unfold bodyMeasure
    rw [← withDensity_const]
    refine withDensity_mono ?_
    filter_upwards with p
    refine ENNReal.ofReal_le_ofReal ?_
    have hg : |NearInst.gainFun γ ν p| ≤ Real.exp (|γ| / ν) := NearInst.gainFun_le hν p
    have hpos : 0 < NearInst.gainFun γ ν p := NearInst.gainFun_pos γ ν p
    have hgle : NearInst.gainFun γ ν p ≤ Real.exp (|γ| / ν) := by
      rwa [abs_of_pos hpos] at hg
    have hinv : e ≤ ginv γ ν p := by
      have h1 : (Real.exp (|γ| / ν))⁻¹ ≤ (NearInst.gainFun γ ν p)⁻¹ :=
        inv_anti₀ hpos hgle
      have h2 : ginv γ ν p = (NearInst.gainFun γ ν p)⁻¹ := rfl
      rw [h2, he, Real.exp_neg]
      exact h1
    have hsq : e ^ 2 ≤ ginv γ ν p ^ 2 := pow_le_pow_left₀ he0.le hinv 2
    exact mul_le_mul_of_nonneg_left hsq Real.pi_pos.le
  have hle : ageμ c (-3 / 2) ≤ δ⁻¹ • bodyMeasure c γ ν := by
    rw [Measure.le_iff]
    intro s hs
    have h1 := Measure.le_iff.1 hlow s hs
    rw [Measure.smul_apply, smul_eq_mul] at h1
    rw [Measure.smul_apply, smul_eq_mul]
    calc ageμ c (-3 / 2) s = δ⁻¹ * (δ * ageμ c (-3 / 2) s) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hδ0 hδtop, one_mul]
      _ ≤ δ⁻¹ * bodyMeasure c γ ν s := by gcongr
  exact ⟨δ⁻¹, ENNReal.inv_ne_top.2 hδ0, ENNReal.inv_ne_zero.2 hδtop, hle⟩

/-- Pointwise `3`-bound of the complex dot product. -/
theorem gen_norm_dotL_le (a b : CVec3) : ‖dotL a b‖ ≤ 3 * ‖a‖ * ‖b‖ :=
  NearInst.pb_norm_dotL_le a b

/-- Phase-test version of `PairBound`: a continuous phase test (bounded spatial support, no
solenoidal condition) pairs integrably with the physical velocity of an `L²(ageμ)` chart field and
the pairing is bounded by `C ‖f‖_{L²(ageμ c (-3/2))}`. -/
theorem phaseTest_pairBound {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) (Φ : ℝ × Space → CVec3)
    (hΦ : IsPhaseTest (2 * ε * c) Φ) :
    ∃ C : ℝ, ∀ f : Chart → Merid, Measurable f → MemLp f 2 (ageμ c (-3 / 2)) →
      Integrable (fun x : ℝ × Space => dotL (Φ x) (velPhys ε⁻¹ c f x))
        (volume.restrict (phaseCell (2 * ε * c))) ∧
      ‖pairF (2 * ε * c) Φ (velPhys ε⁻¹ c f)‖ ≤ C * (eLpNorm f 2 (ageμ c (-3 / 2))).toReal := by
  have hR : (0 : ℝ) < ε⁻¹ := inv_pos.2 hε
  have hP0 : 0 < 2 * ε * c := by positivity
  haveI : Fact (0 < 2 * ε * c) := ⟨hP0⟩
  have hPR : 2 * ε * c = 2 * c / ε⁻¹ := by rw [div_inv_eq_mul]; ring
  set P : ℝ := 2 * ε * c with hPdef
  obtain ⟨R0, hR0⟩ := hΦ.bounded_support
  have hΦc : Continuous Φ := hΦ.continuous
  set K : Set (ℝ × Space) := Icc (0 : ℝ) P ×ˢ Metric.closedBall (0 : Space) R0 with hKdef
  have hKc : IsCompact K := isCompact_Icc.prod (isCompact_closedBall _ _)
  have hKm : MeasurableSet K := hKc.measurableSet
  obtain ⟨C0, hC0⟩ := hKc.exists_bound_of_continuousOn hΦc.continuousOn
  set M : ℝ := max C0 0 with hMdef
  have hM0 : 0 ≤ M := le_max_right _ _
  set g : ℝ × Space → ℝ := K.indicator fun _ => M with hgdef
  have hgnn : ∀ x, 0 ≤ g x := fun x => Set.indicator_nonneg (fun _ _ => hM0) x
  have hcellm : MeasurableSet (Ioc (0 : ℝ) P ×ˢ (univ : Set Space)) :=
    measurableSet_Ioc.prod MeasurableSet.univ
  set μ : Measure (ℝ × Space) := volume.restrict (phaseCell P) with hμdef
  have hKfin : μ K ≠ ∞ := by
    rw [hμdef, Measure.restrict_apply hKm]
    exact (lt_of_le_of_lt (measure_mono inter_subset_left) hKc.measure_lt_top).ne
  have hgL : MemLp g 2 μ := memLp_indicator_const 2 hKm M (Or.inr hKfin)
  have hgw : ∀ᵐ x ∂μ, ‖Φ x‖ ≤ g x := by
    rw [hμdef]
    refine ae_restrict_of_forall_mem hcellm ?_
    intro x hx
    obtain ⟨hx1, -⟩ := hx
    by_cases hxK : x ∈ K
    · show ‖Φ x‖ ≤ K.indicator (fun _ => M) x
      rw [indicator_of_mem hxK]
      exact le_trans (hC0 x hxK) (le_max_left _ _)
    · have hx2 : R0 < ‖x.2‖ := by
        by_contra h
        push_neg at h
        exact hxK ⟨Ioc_subset_Icc_self hx1, mem_closedBall_zero_iff.2 h⟩
      have h0 : Φ x = 0 := hR0 x.1 x.2 hx2
      rw [h0, norm_zero]
      exact hgnn x
  set A : ℝ := (eLpNorm g 2 μ).toReal with hAdef
  set κ : ℝ := Real.sqrt Real.pi * ε⁻¹ * P ^ ((2 : ℝ)⁻¹) with hκdef
  refine ⟨P⁻¹ * (3 * A * κ), fun f hf hfL => ?_⟩
  have hfL' : MemLp (liftFun ε⁻¹ c f) 2 (phaseμ P) := fwuB_memLp_liftFun hR hc hPR hf hfL
  have hvel : MemLp (velPhys ε⁻¹ c f) 2 (phaseμ P) := fwuB_memLp_velPhys hR hf hfL'
  have hμeq : μ = ENNReal.ofReal P • phaseμ P := by
    rw [wda_phaseμ_eq P, smul_smul, ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.2 hP0).ne'
      ENNReal.ofReal_ne_top, one_smul]
  have hwμ : MemLp (velPhys ε⁻¹ c f) 2 μ := by
    rw [hμeq]
    exact hvel.smul_measure ENNReal.ofReal_ne_top
  have hwn : MemLp (fun x => ‖velPhys ε⁻¹ c f x‖) 2 μ := hwμ.norm
  have hint : Integrable (fun x : ℝ × Space => dotL (Φ x) (velPhys ε⁻¹ c f x)) μ :=
    fwuB_integrable_dotL hΦc ⟨R0, hR0⟩ hwμ
  have hI2 : Integrable (fun x => g x * ‖velPhys ε⁻¹ c f x‖) μ :=
    MemLp.integrable_mul hgL hwn
  refine ⟨hint, ?_⟩
  have hpair : pairF P Φ (velPhys ε⁻¹ c f) = P⁻¹ • ∫ x, dotL (Φ x) (velPhys ε⁻¹ c f x) ∂μ :=
    pairF_eq_restrictedProductIntegral hint
  have hdom : ∫ x, ‖dotL (Φ x) (velPhys ε⁻¹ c f x)‖ ∂μ ≤
      3 * ∫ x, g x * ‖velPhys ε⁻¹ c f x‖ ∂μ := by
    rw [← integral_const_mul]
    apply integral_mono_ae hint.norm (hI2.const_mul 3)
    filter_upwards [hgw] with x hx
    calc ‖dotL (Φ x) (velPhys ε⁻¹ c f x)‖ ≤ 3 * ‖Φ x‖ * ‖velPhys ε⁻¹ c f x‖ :=
          gen_norm_dotL_le _ _
      _ ≤ 3 * (g x * ‖velPhys ε⁻¹ c f x‖) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
            (by norm_num)
  have hH : ∫ x, g x * ‖velPhys ε⁻¹ c f x‖ ∂μ ≤
      A * (eLpNorm (velPhys ε⁻¹ c f) 2 μ).toReal := by
    have h2 : MemLp g (ENNReal.ofReal 2) μ := by rw [ENNReal.ofReal_ofNat]; exact hgL
    have h3 : MemLp (fun x => ‖velPhys ε⁻¹ c f x‖) (ENNReal.ofReal 2) μ := by
      rw [ENNReal.ofReal_ofNat]; exact hwn
    have hC := integral_mul_norm_le_Lp_mul_Lq (μ := μ) (p := 2) (q := 2)
      Real.HolderConjugate.two_two h2 h3
    have hgn : ∀ x, ‖g x‖ = g x := fun x => Real.norm_of_nonneg (hgnn x)
    have eA := NearInst.pb_toReal_eLpNorm hgL
    have eB := NearInst.pb_toReal_eLpNorm hwμ
    simp only [hgn, norm_norm, one_div] at hC eA
    rw [hAdef, eA, eB]
    exact hC
  have hn : eLpNorm (velPhys ε⁻¹ c f) 2 μ =
      ENNReal.ofReal (Real.sqrt Real.pi * ε⁻¹) * ((ENNReal.ofReal P) ^ ((1 : ℝ≥0∞) / 2).toReal *
        eLpNorm (liftFun ε⁻¹ c f) 2 (phaseμ P)) := by
    have e1 : eLpNorm (velPhys ε⁻¹ c f) 2 μ =
        eLpNorm (fun x => (Real.sqrt Real.pi * ε⁻¹) * ‖liftFun ε⁻¹ c f x‖) 2 μ := by
      apply eLpNorm_congr_norm_ae
      exact ae_of_all _ fun x => by
        rw [fwuB_norm_velPhys hR f x,
          Real.norm_of_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hR.le) (norm_nonneg _))]
    have e2 : eLpNorm (fun x => (Real.sqrt Real.pi * ε⁻¹) * ‖liftFun ε⁻¹ c f x‖) 2 μ =
        ‖Real.sqrt Real.pi * ε⁻¹‖ₑ * eLpNorm (fun x => ‖liftFun ε⁻¹ c f x‖) 2 μ :=
      eLpNorm_const_smul (Real.sqrt Real.pi * ε⁻¹) (fun x => ‖liftFun ε⁻¹ c f x‖) 2 μ
    rw [eLpNorm_norm] at e2
    rw [e1, e2, Real.enorm_eq_ofReal (mul_nonneg (Real.sqrt_nonneg _) hR.le), hμeq,
      eLpNorm_smul_measure_of_ne_zero (ENNReal.ofReal_pos.2 hP0).ne', smul_eq_mul]
  have hz : ((1 : ℝ≥0∞) / 2).toReal = 2⁻¹ := by
    norm_num [ENNReal.toReal_div]
  have hB : (eLpNorm (velPhys ε⁻¹ c f) 2 μ).toReal =
      κ * (eLpNorm f 2 (ageμ c (-3 / 2))).toReal := by
    rw [hn, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal
      (mul_nonneg (Real.sqrt_nonneg _) hR.le), ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hP0.le,
      hz, eLpNorm_liftFun hR hc hPR hf, hκdef]
    ring
  have hpn : ‖pairF P Φ (velPhys ε⁻¹ c f)‖ =
      P⁻¹ * ‖∫ x, dotL (Φ x) (velPhys ε⁻¹ c f x) ∂μ‖ := by
    rw [hpair, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hP0.le)]
  rw [hpn]
  have hI : ‖∫ x, dotL (Φ x) (velPhys ε⁻¹ c f x) ∂μ‖ ≤
      3 * (A * (κ * (eLpNorm f 2 (ageμ c (-3 / 2))).toReal)) := by
    rw [← hB]
    exact le_trans (norm_integral_le_integral_norm _)
      (hdom.trans (mul_le_mul_of_nonneg_left hH (by norm_num)))
  calc P⁻¹ * ‖∫ x, dotL (Φ x) (velPhys ε⁻¹ c f x) ∂μ‖
      ≤ P⁻¹ * (3 * (A * (κ * (eLpNorm f 2 (ageμ c (-3 / 2))).toReal))) :=
        mul_le_mul_of_nonneg_left hI (inv_nonneg.2 hP0.le)
    _ = P⁻¹ * (3 * A * κ) * (eLpNorm f 2 (ageμ c (-3 / 2))).toReal := by ring

/-- The pairing with the physical velocity depends only on the `ageμ c (-3/2)`-class of the chart
field (`liftFun_congr_ae_left`, then Fubini on the phase cell). -/
theorem pairF_congr_of_ae {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) (H : ℝ × Space → CVec3)
    {b b' : Chart → Merid} (hb : Measurable b) (h : b =ᵐ[ageμ c (-3 / 2)] b') :
    pairF (2 * ε * c) H (velPhys ε⁻¹ c b) = pairF (2 * ε * c) H (velPhys ε⁻¹ c b') := by
  have hR : (0 : ℝ) < ε⁻¹ := inv_pos.2 hε
  have hPR : 2 * ε * c = 2 * c / ε⁻¹ := by rw [div_inv_eq_mul]; ring
  have hl := liftFun_congr_ae_left hR hc hPR hb h
  rw [wda_ae_phaseμ] at hl
  apply NearInst.pl_pairF_congr_ae
  filter_upwards [hl] with x hx
  rw [fwuB_velPhys_eq ε⁻¹ c hR.ne' b x, fwuB_velPhys_eq ε⁻¹ c hR.ne' b' x, hx]

/-- **Generic continuity.** If `ageμ c (-3/2) ≤ K • m` with `K ≠ 0, ∞`, the phase pairing
`f ↦ ⟨H, 𝒩_v f⟩` is continuous on `L²(m)` for a phase test `H`. -/
theorem pairCont_of_le {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) {m : Measure Chart} {K : ℝ≥0∞}
    (hK : K ≠ ∞) (hK0 : K ≠ 0) (hle : ageμ c (-3 / 2) ≤ K • m) (H : ℝ × Space → CVec3)
    (hH : IsPhaseTest (2 * ε * c) H) :
    Continuous fun f : Lp (α := Chart) Merid 2 m =>
      pairF (2 * ε * c) H (velPhys ε⁻¹ c (f : Chart → Merid)) := by
  have hR : (0 : ℝ) < ε⁻¹ := inv_pos.2 hε
  have hP0 : 0 < 2 * ε * c := by positivity
  haveI : Fact (0 < 2 * ε * c) := ⟨hP0⟩
  have hac : ageμ c (-3 / 2) ≪ m := Measure.absolutelyContinuous_of_le_smul hle
  obtain ⟨C0, hC0⟩ := phaseTest_pairBound hc hε H hH
  have hmeas : ∀ f : Lp (α := Chart) Merid 2 m, Measurable (f : Chart → Merid) :=
    fun f => (Lp.stronglyMeasurable f).measurable
  have hMA : ∀ f : Lp (α := Chart) Merid 2 m, MemLp (f : Chart → Merid) 2 (ageμ c (-3 / 2)) :=
    fun f => MemLp.of_measure_le_smul hK hle (Lp.memLp f)
  have hKr1 : K ^ (1 / (2 : ℝ≥0∞)).toReal ≠ ∞ := by
    refine ENNReal.rpow_ne_top_of_nonneg (by positivity) hK
  set Kc : ℝ := (K ^ (1 / (2 : ℝ≥0∞)).toReal).toReal with hKc
  have hnorm : ∀ f : Lp (α := Chart) Merid 2 m,
      (eLpNorm (f : Chart → Merid) 2 (ageμ c (-3 / 2))).toReal ≤ Kc * ‖f‖ := by
    intro f
    rw [Lp.norm_def]
    have h1 := eLpNorm_le_of_measure_le_smul (p := 2) hle (f := (f : Chart → Merid))
    have hfin : eLpNorm (f : Chart → Merid) 2 m ≠ ∞ := (Lp.memLp f).eLpNorm_lt_top.ne
    calc (eLpNorm (f : Chart → Merid) 2 (ageμ c (-3 / 2))).toReal
        ≤ (K ^ (1 / (2 : ℝ≥0∞)).toReal • eLpNorm (f : Chart → Merid) 2 m).toReal :=
          ENNReal.toReal_mono (by rw [smul_eq_mul]; exact ENNReal.mul_ne_top hKr1 hfin) h1
      _ = Kc * (eLpNorm (f : Chart → Merid) 2 m).toReal := by
          rw [smul_eq_mul, ENNReal.toReal_mul]
  have hadd : ∀ f g : Lp (α := Chart) Merid 2 m,
      pairF (2 * ε * c) H (velPhys ε⁻¹ c ((f + g : Lp (α := Chart) Merid 2 m) : Chart → Merid)) =
        pairF (2 * ε * c) H (velPhys ε⁻¹ c (f : Chart → Merid)) +
          pairF (2 * ε * c) H (velPhys ε⁻¹ c (g : Chart → Merid)) := by
    intro f g
    have hgm : Measurable ((f : Chart → Merid) + (g : Chart → Merid)) :=
      (hmeas f).add (hmeas g)
    have e1 := (pairF_congr_of_ae hc hε H hgm (hac.ae_le (Lp.coeFn_add f g).symm)).symm
    rw [e1, NearInst.pl_velPhys_add]
    have hF := (hC0 _ (hmeas f) (hMA f)).1
    have hG := (hC0 _ (hmeas g) (hMA g)).1
    have hFG := (hC0 _ hgm ((hMA f).add (hMA g))).1
    rw [NearInst.pl_velPhys_add] at hFG
    exact pairF_add_right_of_integrable hF hG hFG
  have hsmul : ∀ (a : ℝ) (f : Lp (α := Chart) Merid 2 m),
      pairF (2 * ε * c) H (velPhys ε⁻¹ c ((a • f : Lp (α := Chart) Merid 2 m) : Chart → Merid)) =
        a • pairF (2 * ε * c) H (velPhys ε⁻¹ c (f : Chart → Merid)) := by
    intro a f
    have hm : Measurable (a • (f : Chart → Merid)) := (hmeas f).const_smul a
    have e1 := (pairF_congr_of_ae hc hε H hm (hac.ae_le (Lp.coeFn_smul a f).symm)).symm
    rw [e1, NearInst.pl_velPhys_smul]
    exact NearInst.pl_pairF_smul a H _
  let L : Lp (α := Chart) Merid 2 m →ₗ[ℝ] ℂ :=
    { toFun := fun f => pairF (2 * ε * c) H (velPhys ε⁻¹ c (f : Chart → Merid))
      map_add' := fun f g => hadd f g
      map_smul' := fun a f => by
        rw [RingHom.id_apply]
        exact hsmul a f }
  have hbd : ∀ f, ‖L f‖ ≤ (max C0 0 * Kc) * ‖f‖ := by
    intro f
    have hpb := (hC0 _ (hmeas f) (hMA f)).2
    have hX : 0 ≤ (eLpNorm (f : Chart → Merid) 2 (ageμ c (-3 / 2))).toReal :=
      ENNReal.toReal_nonneg
    calc ‖L f‖ ≤ C0 * (eLpNorm (f : Chart → Merid) 2 (ageμ c (-3 / 2))).toReal := hpb
      _ ≤ max C0 0 * (eLpNorm (f : Chart → Merid) 2 (ageμ c (-3 / 2))).toReal :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hX
      _ ≤ max C0 0 * (Kc * ‖f‖) := mul_le_mul_of_nonneg_left (hnorm f) (le_max_right _ _)
      _ = (max C0 0 * Kc) * ‖f‖ := by ring
  exact (LinearMap.mkContinuous L (max C0 0 * Kc) hbd).continuous

end UnforcedLeray.Short.PartIIIb.Concrete
