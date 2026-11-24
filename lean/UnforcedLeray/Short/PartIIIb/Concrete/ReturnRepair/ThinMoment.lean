import UnforcedLeray.Short.PartIIIb.Concrete.ReturnRepair.Estimates
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.N0CS
import UnforcedLeray.Short.PartIIIb.Concrete.SourceL.OldMeasureAC
import UnforcedLeray.Short.PartIIIa.T01_AgeCS
import UnforcedLeray.Short.PartIIIa.T02_TransverseCS
import UnforcedLeray.Short.PartIIIa.T10_StressMoment

/-!
# The thin moment (`PartIII-b:C/rep/10`, source 5162-5167, 5527; SP 2747-2753)

`thinMoment : D.ThinMoment`.  The proof: `N₁(χ_o T₁) ≤ 𝒩₁(1_{s>6/(5ν)} χ_o T₁)` (the cutoff
vanishes below `6/(5ν)`), the stress moment `stressMoment_of_parts` (`PartIII-a:T10`) with
`A = 6/(5ν) ≥ 1`, and the gain comparison `z1NormSq ≤ e^{2γ/ν} ‖g⁻¹T₁‖²_{Z_1}` (`slGain_lint`).
The thin component is replaced by its a.e. representative `Gm` (measurable), using that the
old region `oldMeasure` is absolutely continuous with respect to the gain measure.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.Blueprint.Planar (PlanarData)

/-! ### Elementary facts -/

theorem tm_frobSq_toMatrix (x : Ten3) : UnforcedLeray.Short.IIIa.frobSq (Ten3.toMatrix x) = ‖x‖ ^ 2 := by
  rw [← slFrob_toMatrix x]
  unfold frob UnforcedLeray.Short.IIIa.frobSq
  rw [Real.sq_sqrt (by positivity)]

theorem tm_frobSq_smul (a : ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ) :
    UnforcedLeray.Short.IIIa.frobSq (a • M) = a ^ 2 * UnforcedLeray.Short.IIIa.frobSq M := by
  unfold UnforcedLeray.Short.IIIa.frobSq
  simp [Finset.mul_sum, mul_pow]

theorem tm_frobSq_nonneg (M : Matrix (Fin 3) (Fin 3) ℝ) : 0 ≤ UnforcedLeray.Short.IIIa.frobSq M := by
  unfold UnforcedLeray.Short.IIIa.frobSq
  positivity

/-- `1 ≤ e^{2γ/ν}·ginv²` in the form used below. -/
theorem tm_one_le_ginv (γ ν : ℝ) (hγ : 0 < γ) (hν : 0 < ν) (p : Chart) :
    1 ≤ (ginv γ ν p) ^ 2 * Real.exp (γ / ν) ^ 2 := by
  have hg : 0 < UnforcedLeray.Short.IIIa.gainG γ ν (max p.1 0) := by
    unfold UnforcedLeray.Short.IIIa.gainG
    exact Real.exp_pos _
  have hle : UnforcedLeray.Short.IIIa.gainG γ ν (max p.1 0) ≤ Real.exp (γ / ν) :=
    slGainG_le hγ hν (le_max_right _ _)
  have h1 : 1 ≤ Real.exp (γ / ν) / UnforcedLeray.Short.IIIa.gainG γ ν (max p.1 0) :=
    (one_le_div hg).2 hle
  have h2 : (1 : ℝ) ≤ (Real.exp (γ / ν) / UnforcedLeray.Short.IIIa.gainG γ ν (max p.1 0)) ^ 2 :=
    one_le_pow₀ h1
  have h3 : (ginv γ ν p) ^ 2 * Real.exp (γ / ν) ^ 2 =
      (Real.exp (γ / ν) / UnforcedLeray.Short.IIIa.gainG γ ν (max p.1 0)) ^ 2 := by
    unfold ginv
    rw [div_pow, inv_pow]
    ring
  rw [h3]
  exact h2

/-! ### The gain comparison for `z1NormSq` -/

/-- `z1NormSq` of a measurable thin tensor is bounded by `e^{2γ/ν}` times its gain-weighted
`L²` norm (`slGain_lint`). -/
theorem tm_z1_le (c mZ γ ν : ℝ) (hγ : 0 < γ) (hν : 0 < ν) (Gm : Chart → Ten3)
    (hGm : Measurable Gm) :
    UnforcedLeray.Short.IIIa.z1NormSq c mZ (fun p => Ten3.toMatrix (Gm p)) ≤
      ENNReal.ofReal (Real.exp (γ / ν) ^ 2) *
        ∫⁻ p, ENNReal.ofReal (‖Gm p‖ ^ 2) ∂(gainZ1Measure c mZ γ ν) := by
  have hΨ : Measurable fun p : Chart => ENNReal.ofReal (‖Gm p‖ ^ 2) :=
    (hGm.norm.pow_const 2).ennreal_ofReal
  have key := slGain_lint c mZ γ ν (fun p => ENNReal.ofReal (‖Gm p‖ ^ 2)) hΨ
  rw [key, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  unfold UnforcedLeray.Short.IIIa.z1NormSq
  apply lintegral_mono
  intro p
  dsimp only
  rw [tm_frobSq_toMatrix]
  have hW : 0 ≤ UnforcedLeray.Short.IIIa.transWeight mZ p ^ 2 := sq_nonneg _
  have hn : 0 ≤ ‖Gm p‖ ^ 2 := sq_nonneg _
  have hE : 0 ≤ Real.exp (γ / ν) ^ 2 := sq_nonneg _
  have hG : 0 ≤ ginv γ ν p ^ 2 := sq_nonneg _
  have hP : 0 ≤ UnforcedLeray.Short.IIIa.transWeight mZ p ^ 2 * ‖Gm p‖ ^ 2 :=
    mul_nonneg hW hn
  have hreal : UnforcedLeray.Short.IIIa.transWeight mZ p ^ 2 * ‖Gm p‖ ^ 2 ≤
      Real.exp (γ / ν) ^ 2 * (UnforcedLeray.Short.IIIa.transWeight mZ p ^ 2 *
        (ginv γ ν p ^ 2 * ‖Gm p‖ ^ 2)) := by
    have e : Real.exp (γ / ν) ^ 2 * (UnforcedLeray.Short.IIIa.transWeight mZ p ^ 2 *
        (ginv γ ν p ^ 2 * ‖Gm p‖ ^ 2)) =
        (UnforcedLeray.Short.IIIa.transWeight mZ p ^ 2 * ‖Gm p‖ ^ 2) *
          (ginv γ ν p ^ 2 * Real.exp (γ / ν) ^ 2) := by ring
    rw [e]
    exact le_mul_of_one_le_right hP (by linarith [tm_one_le_ginv γ ν hγ hν p])
  calc ENNReal.ofReal (UnforcedLeray.Short.IIIa.transWeight mZ p ^ 2 * ‖Gm p‖ ^ 2)
      ≤ ENNReal.ofReal (Real.exp (γ / ν) ^ 2 * (UnforcedLeray.Short.IIIa.transWeight mZ p ^ 2 *
        (ginv γ ν p ^ 2 * ‖Gm p‖ ^ 2))) := ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal (Real.exp (γ / ν) ^ 2) * (ENNReal.ofReal (UnforcedLeray.Short.IIIa.transWeight mZ p ^ 2) *
        (ENNReal.ofReal (ginv γ ν p ^ 2) * ENNReal.ofReal (‖Gm p‖ ^ 2))) := by
      rw [ENNReal.ofReal_mul hE, ENNReal.ofReal_mul hW, ENNReal.ofReal_mul hG]

/-! ### Almost everywhere transfer from the old region -/

/-- A property holding almost everywhere is witnessed by a measurable set. -/
theorem tm_ae_measurable {α : Type*} [MeasurableSpace α] {μ : Measure α} {P : α → Prop}
    (h : ∀ᵐ x ∂μ, P x) : ∃ S : Set α, MeasurableSet S ∧ (∀ x ∈ S, P x) ∧ ∀ᵐ x ∂μ, x ∈ S := by
  have h0 : μ {x | ¬ P x} = 0 := ae_iff.1 h
  refine ⟨(toMeasurable μ {x | ¬ P x})ᶜ, (measurableSet_toMeasurable _ _).compl, ?_, ?_⟩
  · intro x hx
    by_contra hn
    exact hx (subset_toMeasurable μ _ hn)
  · rw [ae_iff]
    have e : {x | ¬ x ∈ (toMeasurable μ {x | ¬ P x})ᶜ} = toMeasurable μ {x | ¬ P x} := by
      ext x; simp
    rw [e, measure_toMeasurable]
    exact h0


/-! ### The integrand of `firstMoment` and its a.e. dependence -/

/-- The integrand of `IIIa.firstMoment` at the age `s`. -/
def tmInt (c : ℝ) (T : Chart → Matrix (Fin 3) (Fin 3) ℝ) (s : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) * ∫⁻ η : ℝ, ENNReal.ofReal (1 + |η| / Real.sqrt s) *
    (∫⁻ q in Ico (-(c / 2)) (c / 2),
      ENNReal.ofReal c⁻¹ * ENNReal.ofReal (UnforcedLeray.Short.IIIa.frobSq (T (s, (q, η)))))
      ^ (1 / 2 : ℝ)

theorem tm_firstMoment_eq (c A : ℝ) (T : Chart → Matrix (Fin 3) (Fin 3) ℝ) :
    UnforcedLeray.Short.IIIa.firstMoment c A T = ∫⁻ s in Ioi A, tmInt c T s := rfl

theorem tmInt_congr (c : ℝ) (T T' : Chart → Matrix (Fin 3) (Fin 3) ℝ) (s : ℝ)
    (h : ∀ᵐ η ∂(volume : Measure ℝ), ∀ᵐ q ∂(volume.restrict (Ico (-(c / 2)) (c / 2))),
      T (s, (q, η)) = T' (s, (q, η))) :
    tmInt c T s = tmInt c T' s := by
  unfold tmInt
  congr 1
  apply lintegral_congr_ae
  filter_upwards [h] with η hη
  have hq' : (∫⁻ q in Ico (-(c / 2)) (c / 2),
        ENNReal.ofReal c⁻¹ * ENNReal.ofReal (UnforcedLeray.Short.IIIa.frobSq (T (s, (q, η))))) =
      ∫⁻ q in Ico (-(c / 2)) (c / 2),
        ENNReal.ofReal c⁻¹ * ENNReal.ofReal (UnforcedLeray.Short.IIIa.frobSq (T' (s, (q, η)))) :=
    lintegral_congr_ae (by filter_upwards [hη] with q hq; rw [hq])
  rw [hq']

/-! ### The slice of the old region -/

theorem tm_slice (c ν : ℝ) (hc : 0 < c) (S : Set Chart) (hS : MeasurableSet S)
    (hae : ∀ᵐ p ∂(oldMeasure c ν), p ∈ S) :
    ∀ᵐ s ∂(volume.restrict (Ioi (6 / 5 / ν))), ∀ᵐ η ∂(volume : Measure ℝ),
      ∀ᵐ q ∂(volume.restrict (Ico (-(c / 2)) (c / 2))), (s, (q, η)) ∈ S := by
  unfold oldMeasure at hae
  have : SFinite (Cyl.avgμ c) := by
    unfold Cyl.avgμ
    infer_instance
  have h1 := Measure.ae_ae_of_ae_prod hae
  filter_upwards [h1] with s hs
  have hc' : ENNReal.ofReal c⁻¹ ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact inv_pos.2 hc
  have hs2 := hs
  unfold Cyl.avgμ at hs2
  rw [Cyl.cellμ_eq_prod, neg_div] at hs2
  have hs3 := (Measure.absolutelyContinuous_smul hc').ae_le hs2
  have hq := Measure.ae_ae_of_ae_prod hs3
  have hset : MeasurableSet {x : ℝ × ℝ | (s, (x.1, x.2)) ∈ S} :=
    hS.preimage (measurable_const.prodMk measurable_id)
  exact (Measure.ae_ae_comm (μ := volume.restrict (Ico (-(c / 2)) (c / 2))) (ν := (volume : Measure ℝ))
    (p := fun a b => (s, (a, b)) ∈ S) hset).1 hq

/-! ### The chain: old moment to the stress moment of the representative -/

theorem tm_z1_ite_le (c mZ A : ℝ) (F G : Chart → Matrix (Fin 3) (Fin 3) ℝ)
    (h : ∀ p, UnforcedLeray.Short.IIIa.frobSq (F p) ≤ UnforcedLeray.Short.IIIa.frobSq (G p)) :
    UnforcedLeray.Short.IIIa.z1NormSq c mZ (fun p => if A < p.1 then F p else 0) ≤
      UnforcedLeray.Short.IIIa.z1NormSq c mZ G := by
  unfold UnforcedLeray.Short.IIIa.z1NormSq
  apply lintegral_mono
  intro p
  apply ENNReal.ofReal_le_ofReal
  dsimp only
  by_cases hp : A < p.1
  · rw [if_pos hp]
    exact mul_le_mul_of_nonneg_left (h p) (sq_nonneg _)
  · rw [if_neg hp]
    have h0 : UnforcedLeray.Short.IIIa.frobSq (0 : Matrix (Fin 3) (Fin 3) ℝ) = 0 := by
      unfold UnforcedLeray.Short.IIIa.frobSq
      simp
    rw [h0, mul_zero]
    exact mul_nonneg (sq_nonneg _) (tm_frobSq_nonneg _)

theorem tm_chain (c ν : ℝ) (hc : 0 < c) (hν : 0 < ν) (χ : ℝ → ℝ)
    (hχz : ∀ t, t ≤ 6 / 5 → χ t = 0) (hχr : ∀ t, 0 ≤ χ t ∧ χ t ≤ 1)
    (M : Chart → Matrix (Fin 3) (Fin 3) ℝ) (Gm : Chart → Ten3) (S : Set Chart) (hS : MeasurableSet S)
    (hSsub : ∀ p ∈ S, M p = Ten3.toMatrix (Gm p))
    (hSae : ∀ᵐ p ∂(oldMeasure c ν), p ∈ S) :
    UnforcedLeray.Short.IIIa.firstMoment c 0 (fun p => χ (ν * p.1) • M p) ≤
      UnforcedLeray.Short.IIIa.firstMoment c (6 / 5 / ν)
        (fun p => χ (ν * p.1) • Ten3.toMatrix (Gm p)) := by
  have hA0 : 0 ≤ 6 / 5 / ν := div_nonneg (by norm_num) hν.le
  rw [tm_firstMoment_eq, tm_firstMoment_eq]
  calc ∫⁻ s in Ioi 0, tmInt c (fun p => χ (ν * p.1) • M p) s
      ≤ ∫⁻ s in Ioi 0, (Ioi (6 / 5 / ν)).indicator (tmInt c (fun p => χ (ν * p.1) • Ten3.toMatrix (Gm p))) s := by
        apply lintegral_mono_ae
        have hslice := tm_slice c ν hc S hS hSae
        have hall : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Ioi (6 / 5 / ν) →
            ∀ᵐ η ∂(volume : Measure ℝ), ∀ᵐ q ∂(volume.restrict (Ico (-(c / 2)) (c / 2))),
              (s, (q, η)) ∈ S :=
          (ae_restrict_iff' measurableSet_Ioi).1 hslice
        have hall0 := ae_restrict_of_ae (μ := (volume : Measure ℝ)) (s := Ioi (0 : ℝ)) hall
        filter_upwards [hall0, ae_restrict_mem measurableSet_Ioi] with s hs hs0
        by_cases hsA : s ∈ Ioi (6 / 5 / ν)
        · rw [Set.indicator_apply, if_pos hsA]
          apply le_of_eq
          apply tmInt_congr
          filter_upwards [hs hsA] with η hη
          filter_upwards [hη] with q hq
          have := hSsub _ hq
          simp only [this]
        · rw [Set.indicator_apply, if_neg hsA]
          have hsle : s ≤ 6 / 5 / ν := not_lt.1 hsA
          have hχs : χ (ν * s) = 0 := hχz _ (by
            rw [mul_comm]
            exact (le_div_iff₀ hν).1 hsle)
          have h0 : tmInt c (fun p => χ (ν * p.1) • M p) s = 0 := by
            unfold tmInt
            simp [hχs, UnforcedLeray.Short.IIIa.frobSq]
          rw [h0]
    _ = ∫⁻ s in Ioi (6 / 5 / ν), tmInt c (fun p => χ (ν * p.1) • Ten3.toMatrix (Gm p)) s := by
        rw [lintegral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
          Set.inter_eq_left.2 (Set.Ioi_subset_Ioi hA0)]


/-! ### The level bound and the sequence -/

theorem tm_level (Pl : PlanarData) (K : ReturnConsts) (L : ReturnLevel) (hγ : 0 < gRate Pl)
    (hν1 : L.ν ≤ 6 / 5) (C : ℝ) (hC0 : 0 ≤ C)
    (hCT : ∀ c : ℝ, 0 < c → ∀ A : ℝ, 1 ≤ A → ∀ T : Chart → Matrix (Fin 3) (Fin 3) ℝ,
      (∀ a b, Measurable fun p => T p a b) →
      UnforcedLeray.Short.IIIa.firstMoment c A T ≤
        ENNReal.ofReal (C * A ^ (-1 / 2 : ℝ)) *
          UnforcedLeray.Short.IIIa.z1NormSq c K.mZ (fun p => if A < p.1 then T p else 0) ^ (1 / 2 : ℝ)) :
    ThinMomentAt Pl K L C 0 := by
  intro T
  have hν0 : 0 < L.ν := L.ν_pos
  have hc : 0 < cOf L.ν := cOf_pos hν0
  obtain ⟨Gm, hGm, hRG⟩ : ∃ Gm : Chart → Ten3, Measurable Gm ∧
      (WithLp.ofLp T).1 =ᵐ[gainZ1Measure (cOf L.ν) K.mZ (gRate Pl) L.ν] Gm :=
    ⟨(Lp.aestronglyMeasurable (WithLp.ofLp T).1).mk _,
      (Lp.aestronglyMeasurable (WithLp.ofLp T).1).stronglyMeasurable_mk.measurable,
      (Lp.aestronglyMeasurable (WithLp.ofLp T).1).ae_eq_mk⟩
  have hold : ∀ᵐ p ∂(oldMeasure (cOf L.ν) L.ν), thinRep T p = Ten3.toMatrix (Gm p) := by
    filter_upwards [(oldMeasureAC (cOf L.ν) K.mZ (gRate Pl) L.ν hν0).ae_le hRG] with p hp
    unfold thinRep
    rw [hp]
  obtain ⟨S, hS, hSsub, hSae⟩ := tm_ae_measurable hold
  have hA1 : 1 ≤ 6 / 5 / L.ν := by
    rw [le_div_iff₀ hν0]
    linarith
  have hχm : Measurable K.χo := K.hχo.smooth.continuous.measurable
  have hcoord : ∀ a b : Fin 3, Measurable fun p : Chart => Gm p (a, b) := fun a b =>
    (EuclideanSpace.proj (a, b) : Ten3 →L[ℝ] ℝ).continuous.measurable.comp hGm
  have hmeas : ∀ a b : Fin 3, Measurable fun p : Chart =>
      (fun p : Chart => K.χo (L.ν * p.1) • Ten3.toMatrix (Gm p)) p a b := fun a b => by
    show Measurable fun p : Chart => K.χo (L.ν * p.1) * Gm p (a, b)
    exact (hχm.comp (measurable_const.mul measurable_fst)).mul (hcoord a b)
  have hChain := tm_chain (cOf L.ν) L.ν hc hν0 K.χo K.hχo.zero K.hχo.range
    (fun p => thinRep T p) (Gm) S hS hSsub hSae
  have hF2 := hCT (cOf L.ν) hc (6 / 5 / L.ν) hA1 (fun p : Chart => K.χo (L.ν * p.1) • Ten3.toMatrix (Gm p)) hmeas
  have hz1 : UnforcedLeray.Short.IIIa.z1NormSq (cOf L.ν) K.mZ
      (fun p => if 6 / 5 / L.ν < p.1 then K.χo (L.ν * p.1) • Ten3.toMatrix (Gm p) else 0) ≤
      ENNReal.ofReal (Real.exp (gRate Pl / L.ν) ^ 2 * ‖(WithLp.ofLp T).1‖ ^ 2) := by
    calc UnforcedLeray.Short.IIIa.z1NormSq (cOf L.ν) K.mZ
          (fun p => if 6 / 5 / L.ν < p.1 then K.χo (L.ν * p.1) • Ten3.toMatrix (Gm p) else 0)
        ≤ UnforcedLeray.Short.IIIa.z1NormSq (cOf L.ν) K.mZ (fun p => Ten3.toMatrix (Gm p)) := by
          apply tm_z1_ite_le
          intro p
          show UnforcedLeray.Short.IIIa.frobSq (K.χo (L.ν * p.1) • Ten3.toMatrix (Gm p)) ≤ _
          rw [tm_frobSq_smul]
          exact mul_le_of_le_one_left (tm_frobSq_nonneg _)
            (pow_le_one₀ (K.hχo.range _).1 (K.hχo.range _).2)
      _ ≤ ENNReal.ofReal (Real.exp (gRate Pl / L.ν) ^ 2) *
            ∫⁻ p, ENNReal.ofReal (‖Gm p‖ ^ 2) ∂(gainZ1Measure (cOf L.ν) K.mZ (gRate Pl) L.ν) :=
          tm_z1_le (cOf L.ν) K.mZ (gRate Pl) L.ν hγ hν0 Gm hGm
      _ = ENNReal.ofReal (Real.exp (gRate Pl / L.ν) ^ 2) * ENNReal.ofReal (‖(WithLp.ofLp T).1‖ ^ 2) := by
          rw [slLp_sq_eq _ Gm hRG]
      _ = ENNReal.ofReal (Real.exp (gRate Pl / L.ν) ^ 2 * ‖(WithLp.ofLp T).1‖ ^ 2) :=
          (ENNReal.ofReal_mul (sq_nonneg _)).symm
  have hthin : UnforcedLeray.Short.IIIa.firstMoment (cOf L.ν) 0
      (fun p => K.χo (L.ν * p.1) • thinRep T p) ≤
      ENNReal.ofReal (C * (6 / 5 / L.ν) ^ (-1 / 2 : ℝ)) *
        ENNReal.ofReal (Real.exp (gRate Pl / L.ν) * ‖(WithLp.ofLp T).1‖) := by
    refine le_trans hChain (le_trans hF2 ?_)
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine le_trans (ENNReal.rpow_le_rpow hz1 (by norm_num)) (le_of_eq ?_)
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
    congr 1
    rw [show Real.exp (gRate Pl / L.ν) ^ 2 * ‖(WithLp.ofLp T).1‖ ^ 2 =
        (Real.exp (gRate Pl / L.ν) * ‖(WithLp.ofLp T).1‖) ^ 2 by ring,
      ← Real.sqrt_eq_rpow, Real.sqrt_sq (by positivity)]
  refine le_trans hthin ?_
  rw [← ENNReal.ofReal_mul (mul_nonneg hC0 (Real.rpow_nonneg (by linarith) _))]
  apply ENNReal.ofReal_le_ofReal
  have hpow : (6 / 5 / L.ν) ^ (-1 / 2 : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hA1 (by norm_num)
  have hR : ‖(WithLp.ofLp T).1‖ ≤ ‖T‖ := by
    have h1 : ‖T‖ = ‖(WithLp.ofLp T).1‖ + ‖(WithLp.ofLp T).2‖ := WithLp.prod_norm_eq_of_L1 T
    linarith [norm_nonneg (WithLp.ofLp T).2]
  have hCE : 0 ≤ C * Real.exp (gRate Pl / L.ν) := mul_nonneg hC0 (Real.exp_pos _).le
  calc C * (6 / 5 / L.ν) ^ (-1 / 2 : ℝ) * (Real.exp (gRate Pl / L.ν) * ‖(WithLp.ofLp T).1‖)
      ≤ C * 1 * (Real.exp (gRate Pl / L.ν) * ‖(WithLp.ofLp T).1‖) := by
        gcongr
    _ = (C * Real.exp (gRate Pl / L.ν)) * ‖(WithLp.ofLp T).1‖ := by ring
    _ ≤ (C * Real.exp (gRate Pl / L.ν)) * ‖T‖ := mul_le_mul_of_nonneg_left hR hCE
    _ = C * L.ν⁻¹ ^ 0 * Real.exp (gRate Pl / L.ν) * ‖T‖ := by simp only [pow_zero]; ring

/-- **`thinMoment`** (`PartIII-b:C/rep/10`, source 5162-5167, 5527). -/
theorem thinMoment (D : SeqData) {dm dp : ℝ} (hst : D.RepairStanding dm dp) : D.ThinMoment := by
  obtain ⟨C, hC0, hCT⟩ := UnforcedLeray.Short.IIIa.stressMoment_of_parts
    UnforcedLeray.Short.IIIa.ageCS UnforcedLeray.Short.IIIa.transverseCS D.K.mZ hst.mZ_gt
  refine ⟨C, 0, ?_⟩
  have hν : ∀ᶠ n : ℕ in atTop, retNu D.Pl D.σ₀ n ≤ 6 / 5 :=
    ((retNu_tendsto D.σ₀ hst.omega_ne).eventually_lt_const (by norm_num : (0 : ℝ) < 6 / 5)).mono
      fun n h => h.le
  filter_upwards [hν] with n hn
  exact tm_level D.Pl D.K (D.level n) hst.gamma_pos hn C hC0 hCT

end UnforcedLeray.Short.PartIIIb.Concrete
