import UnforcedLeray.Short.PartIIIa.Targets

/-!
# Part III-a, task `PartIII-a:T10`: the stress moment from the two Cauchy-Schwarz steps

Source of record: `the November 2 reference manuscript`, display
`eq:stress-short:moment` (lines 2747-2762).

Proves `stressMoment_of_parts : StressMomentOfParts`, that is `AgeCS → TransverseCS → StressMoment`.

Proof. Write `G(s,η) = ∫_{Ico} c⁻¹ ‖T(s,(q,η))‖²_F dq` and `H(s) = (∫_η W² G(s,η)^{2/2}…)^{1/2}`
in the form of `TransverseCS`. Then `firstMoment = ∫_{s>A} s^{-3/2} ∫_η (1+|η|/√s) G^{1/2}`.
The transverse Cauchy-Schwarz bounds the inner η-integral by `C s^{1/4} H(s)`, so
`firstMoment ≤ C ∫_{s>A} s^{-5/4} H`. The age Cauchy-Schwarz bounds this by
`C A^{-1/2} (∫_{s>A} s^{-1/2} H²)^{1/2}`, and `∫_{s>A} s^{-1/2} H²` equals `z1NormSq` of the
indicator `1_{s>A} T` (Tonelli in the age measure `Axi.ageμ`, through `Axi.lintegral_ageμ`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-- Measurability of the Frobenius square of a measurable tensor field. -/
lemma measurable_frobSq_T {T : ℝ × (ℝ × ℝ) → Matrix (Fin 3) (Fin 3) ℝ}
    (hT : ∀ a b, Measurable fun p => T p a b) : Measurable fun p => frobSq (T p) := by
  unfold frobSq
  exact Finset.measurable_sum _ fun a _ => Finset.measurable_sum _ fun b _ => (hT a b).pow_const 2

/-- The indicator `1_{s > A} T` has measurable Frobenius square. -/
lemma measurable_frobSq_ite {T : ℝ × (ℝ × ℝ) → Matrix (Fin 3) (Fin 3) ℝ}
    (hT : ∀ a b, Measurable fun p => T p a b) (A : ℝ) :
    Measurable fun p : ℝ × (ℝ × ℝ) => frobSq (if A < p.1 then T p else 0) := by
  have e : (fun p : ℝ × (ℝ × ℝ) => frobSq (if A < p.1 then T p else 0)) =
      fun p => if A < p.1 then frobSq (T p) else 0 := by
    funext p
    split_ifs
    · rfl
    · simp [frobSq]
  rw [e]
  exact Measurable.ite (measurableSet_lt measurable_const measurable_fst)
    (measurable_frobSq_T hT) measurable_const

lemma measurable_transWeight_T (mZ : ℝ) : Measurable (transWeight mZ) := by
  unfold transWeight
  fun_prop

/-- The square of the transverse weight is the `TransverseCS` weight `(1 + (η/√(1+s))²)^{m_Z}`. -/
lemma transWeight_sq (mZ s q η : ℝ) :
    transWeight mZ (s, (q, η)) ^ 2 = (1 + (η / Real.sqrt (1 + s)) ^ 2) ^ mZ := by
  have key : ∀ B : ℝ, 0 < B → (B ^ (mZ / 2)) ^ 2 = B ^ mZ := by
    intro B hB
    rw [← Real.rpow_natCast, ← Real.rpow_mul hB.le]
    congr 1
    push_cast
    ring
  unfold transWeight
  exact key _ (by positivity)

/-- `(x^{1/2})^2 = x` in `ℝ≥0∞`. -/
lemma rpow_half_rpow_two (x : ℝ≥0∞) : (x ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = x := by
  rw [← ENNReal.rpow_mul]
  norm_num

/-- Joint measurability of the `q`-integral `∫_{Ico} c⁻¹‖T(s,(q,η))‖²_F dq` in `(s, η)`. -/
lemma measurable_innerQ {c : ℝ} {T : ℝ × (ℝ × ℝ) → Matrix (Fin 3) (Fin 3) ℝ}
    (hT : ∀ a b, Measurable fun p => T p a b) :
    Measurable fun x : ℝ × ℝ => ∫⁻ q in Ico (-(c / 2)) (c / 2),
      ENNReal.ofReal c⁻¹ * ENNReal.ofReal (frobSq (T (x.1, (q, x.2)))) := by
  have h1 : Measurable fun z : (ℝ × ℝ) × ℝ => (z.1.1, (z.2, z.1.2)) := by fun_prop
  have hf : Measurable fun z : (ℝ × ℝ) × ℝ =>
      ENNReal.ofReal c⁻¹ * ENNReal.ofReal (frobSq (T (z.1.1, (z.2, z.1.2)))) :=
    measurable_const.mul (ENNReal.measurable_ofReal.comp ((measurable_frobSq_T hT).comp h1))
  exact Measurable.lintegral_prod_right' (f := fun z : (ℝ × ℝ) × ℝ =>
      ENNReal.ofReal c⁻¹ * ENNReal.ofReal (frobSq (T (z.1.1, (z.2, z.1.2))))) hf

/-- Shift of the outer set integral from `Ioi 0` to `Ioi A` when the integrand vanishes on
`(0, A]`. -/
lemma setLIntegral_Ioi_zero_shift {f : ℝ → ℝ≥0∞} {A : ℝ} (hA : 0 < A)
    (hf : ∀ x, x ≤ A → f x = 0) :
    ∫⁻ x in Ioi (0 : ℝ), f x = ∫⁻ x in Ioi A, f x := by
  have hsub : Function.support f ⊆ Ioi A := by
    intro x hx
    rw [Set.mem_Ioi]
    by_contra h
    exact (Function.mem_support.1 hx) (hf x (not_lt.1 h))
  rw [setLIntegral_eq_of_support_subset (hsub.trans (Set.Ioi_subset_Ioi hA.le)),
    setLIntegral_eq_of_support_subset hsub]

/-- Tonelli in the age measure: the `z1NormSq` of the indicator `1_{s>A}T` equals the iterated
integral `∫_{s>A} s^{-1/2} ∫_η W² ∫_q c⁻¹‖T‖²_F`. -/
lemma z1_identity {c : ℝ} (hc : 0 < c) (mZ A : ℝ) (hA : 0 < A)
    {T : ℝ × (ℝ × ℝ) → Matrix (Fin 3) (Fin 3) ℝ} (hT : ∀ a b, Measurable fun p => T p a b) :
    ∫⁻ s in Ioi A, ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) *
        ∫⁻ η : ℝ, ENNReal.ofReal ((1 + (η / Real.sqrt (1 + s)) ^ 2) ^ mZ) *
          ∫⁻ q in Ico (-(c / 2)) (c / 2),
            ENNReal.ofReal c⁻¹ * ENNReal.ofReal (frobSq (T (s, (q, η)))) =
      z1NormSq c mZ (fun p => if A < p.1 then T p else 0) := by
  have hm : Measurable fun p : ℝ × (ℝ × ℝ) =>
      ENNReal.ofReal (transWeight mZ p ^ 2 * frobSq (if A < p.1 then T p else 0)) :=
    ENNReal.measurable_ofReal.comp
      (((measurable_transWeight_T mZ).pow_const 2).mul (measurable_frobSq_ite hT A))
  have hF0 : Measurable fun p : ℝ × (ℝ × ℝ) =>
      ENNReal.ofReal (c⁻¹ * p.1 ^ (-1 / 2 : ℝ)) *
        ENNReal.ofReal (transWeight mZ p ^ 2 * frobSq (if A < p.1 then T p else 0)) :=
    Measurable.mul (ENNReal.measurable_ofReal.comp (measurable_const.mul (measurable_fst.pow_const _)))
      hm
  have hq : qCell c = Ico (-(c / 2)) (c / 2) ×ˢ (univ : Set ℝ) := by
    unfold qCell
    rw [neg_div]
  simp only [z1NormSq]
  rw [lintegral_ageμ hc (-1 / 2) hm, hq, Measure.volume_eq_prod ℝ (ℝ × ℝ),
    setLIntegral_prod _ hF0.aemeasurable, setLIntegral_Ioi_zero_shift hA]
  · refine setLIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
    have hsA : A < s := hs
    have hs0 : 0 < s := lt_trans hA hsA
    have key : ∀ η : ℝ,
        ∫⁻ q in Ico (-(c / 2)) (c / 2), ENNReal.ofReal (c⁻¹ * s ^ (-1 / 2 : ℝ)) *
            ENNReal.ofReal (transWeight mZ (s, (q, η)) ^ 2 *
              frobSq (if A < s then T (s, (q, η)) else 0)) =
          ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) *
            (ENNReal.ofReal ((1 + (η / Real.sqrt (1 + s)) ^ 2) ^ mZ) *
              ∫⁻ q in Ico (-(c / 2)) (c / 2),
                ENNReal.ofReal c⁻¹ * ENNReal.ofReal (frobSq (T (s, (q, η))))) := by
      intro η
      have hW : (0 : ℝ) ≤ (1 + (η / Real.sqrt (1 + s)) ^ 2) ^ mZ := by positivity
      have hc' : (0 : ℝ) ≤ c⁻¹ := by positivity
      have e1 : ∀ q : ℝ,
          ENNReal.ofReal (c⁻¹ * s ^ (-1 / 2 : ℝ)) *
              ENNReal.ofReal (transWeight mZ (s, (q, η)) ^ 2 *
                frobSq (if A < s then T (s, (q, η)) else 0)) =
            ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) *
              (ENNReal.ofReal ((1 + (η / Real.sqrt (1 + s)) ^ 2) ^ mZ) *
                (ENNReal.ofReal c⁻¹ * ENNReal.ofReal (frobSq (T (s, (q, η)))))) := by
        intro q
        rw [if_pos hsA, transWeight_sq, ENNReal.ofReal_mul hc', ENNReal.ofReal_mul hW]
        ring
      rw [lintegral_congr e1, lintegral_const_mul' (ENNReal.ofReal (s ^ (-1 / 2 : ℝ)))
        _ ENNReal.ofReal_ne_top, lintegral_const_mul'
        (ENNReal.ofReal ((1 + (η / Real.sqrt (1 + s)) ^ 2) ^ mZ)) _ ENNReal.ofReal_ne_top]
    rw [← lintegral_const_mul' (ENNReal.ofReal (s ^ (-1 / 2 : ℝ))) _ ENNReal.ofReal_ne_top,
      Measure.volume_eq_prod ℝ ℝ, setLIntegral_prod_symm, Measure.restrict_univ]
    · exact lintegral_congr fun η => (key η).symm
    · exact (hF0.comp (measurable_const.prodMk measurable_id)).aemeasurable
  · intro x hx
    have hx' : ¬ A < x := not_lt.2 hx
    simp [hx', frobSq]

set_option maxHeartbeats 1000000 in
/-- The stress moment from the two Cauchy-Schwarz steps (`PartIII-a:T10`, SP 2747-2762). -/
theorem stressMoment_of_parts : UnforcedLeray.Short.IIIa.StressMomentOfParts := by
  intro hAge hTr mZ hmZ
  obtain ⟨C, hC0, hCT⟩ := hTr mZ hmZ
  refine ⟨C, hC0, fun c hc A hA1 T hTm => ?_⟩
  have hA0 : 0 < A := by linarith
  have hgm : ∀ s : ℝ, Measurable fun η : ℝ =>
      (∫⁻ q in Ico (-(c / 2)) (c / 2), ENNReal.ofReal c⁻¹ * ENNReal.ofReal (frobSq (T (s, (q, η)))))
        ^ (1 / 2 : ℝ) := fun s =>
    ((measurable_innerQ (c := c) hTm).comp (measurable_const.prodMk measurable_id)).pow_const _
  have hK : Measurable fun z : ℝ × ℝ =>
      ENNReal.ofReal ((1 + (z.2 / Real.sqrt (1 + z.1)) ^ 2) ^ mZ) *
        ((∫⁻ q in Ico (-(c / 2)) (c / 2),
          ENNReal.ofReal c⁻¹ * ENNReal.ofReal (frobSq (T (z.1, (q, z.2))))) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) := by
    refine Measurable.mul ?_ (((measurable_innerQ (c := c) hTm).pow_const _).pow_const _)
    exact ENNReal.measurable_ofReal.comp (by fun_prop)
  have hHm' : Measurable fun s : ℝ =>
      (∫⁻ η : ℝ, ENNReal.ofReal ((1 + (η / Real.sqrt (1 + s)) ^ 2) ^ mZ) *
        ((∫⁻ q in Ico (-(c / 2)) (c / 2),
          ENNReal.ofReal c⁻¹ * ENNReal.ofReal (frobSq (T (s, (q, η))))) ^ (1 / 2 : ℝ)) ^ (2 : ℝ)) ^
        (1 / 2 : ℝ) :=
    (Measurable.lintegral_prod_right' hK).pow_const _
  obtain ⟨H, hH⟩ : ∃ H : ℝ → ℝ≥0∞, ∀ s : ℝ, H s =
      (∫⁻ η : ℝ, ENNReal.ofReal ((1 + (η / Real.sqrt (1 + s)) ^ 2) ^ mZ) *
        ((∫⁻ q in Ico (-(c / 2)) (c / 2),
          ENNReal.ofReal c⁻¹ * ENNReal.ofReal (frobSq (T (s, (q, η))))) ^ (1 / 2 : ℝ)) ^ (2 : ℝ)) ^
        (1 / 2 : ℝ) :=
    ⟨fun s => (∫⁻ η : ℝ, ENNReal.ofReal ((1 + (η / Real.sqrt (1 + s)) ^ 2) ^ mZ) *
        ((∫⁻ q in Ico (-(c / 2)) (c / 2),
          ENNReal.ofReal c⁻¹ * ENNReal.ofReal (frobSq (T (s, (q, η))))) ^ (1 / 2 : ℝ)) ^ (2 : ℝ)) ^
        (1 / 2 : ℝ), fun s => rfl⟩
  have hHm : Measurable H := by
    have e : H = fun s : ℝ =>
        (∫⁻ η : ℝ, ENNReal.ofReal ((1 + (η / Real.sqrt (1 + s)) ^ 2) ^ mZ) *
          ((∫⁻ q in Ico (-(c / 2)) (c / 2),
            ENNReal.ofReal c⁻¹ * ENNReal.ofReal (frobSq (T (s, (q, η))))) ^ (1 / 2 : ℝ)) ^ (2 : ℝ)) ^
          (1 / 2 : ℝ) := funext hH
    rw [e]
    exact hHm'
  -- transverse Cauchy-Schwarz at each age `s ≥ 1`
  have hTH : ∀ s : ℝ, 1 ≤ s →
      ∫⁻ η : ℝ, ENNReal.ofReal (1 + |η| / Real.sqrt s) *
          (∫⁻ q in Ico (-(c / 2)) (c / 2), ENNReal.ofReal c⁻¹ * ENNReal.ofReal (frobSq (T (s, (q, η)))))
            ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal (C * s ^ (1 / 4 : ℝ)) * H s := fun s hs1 => by
    rw [hH s]
    exact hCT s hs1 _ (hgm s)
  -- the squared `H`
  have hHsq : ∀ s : ℝ, H s ^ (2 : ℝ) =
      ∫⁻ η : ℝ, ENNReal.ofReal ((1 + (η / Real.sqrt (1 + s)) ^ 2) ^ mZ) *
        ∫⁻ q in Ico (-(c / 2)) (c / 2),
          ENNReal.ofReal c⁻¹ * ENNReal.ofReal (frobSq (T (s, (q, η)))) := by
    intro s
    rw [hH s, rpow_half_rpow_two]
    simp only [rpow_half_rpow_two]
  have hz : ∫⁻ s in Ioi A, ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) * H s ^ (2 : ℝ) =
      z1NormSq c mZ (fun p => if A < p.1 then T p else 0) := by
    rw [← z1_identity hc mZ A hA0 hTm]
    refine setLIntegral_congr_fun measurableSet_Ioi (fun s _ => ?_)
    rw [hHsq s]
  have hFM : firstMoment c A T =
      ∫⁻ s in Ioi A, ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) *
        ∫⁻ η : ℝ, ENNReal.ofReal (1 + |η| / Real.sqrt s) *
          (∫⁻ q in Ico (-(c / 2)) (c / 2),
            ENNReal.ofReal c⁻¹ * ENNReal.ofReal (frobSq (T (s, (q, η))))) ^ (1 / 2 : ℝ) := rfl
  rw [hFM]
  calc ∫⁻ s in Ioi A, ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) *
        ∫⁻ η : ℝ, ENNReal.ofReal (1 + |η| / Real.sqrt s) *
          (∫⁻ q in Ico (-(c / 2)) (c / 2),
            ENNReal.ofReal c⁻¹ * ENNReal.ofReal (frobSq (T (s, (q, η))))) ^ (1 / 2 : ℝ)
      ≤ ∫⁻ s in Ioi A, ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) *
          (ENNReal.ofReal (C * s ^ (1 / 4 : ℝ)) * H s) :=
        setLIntegral_mono' measurableSet_Ioi (fun s hs => by
          have hs1 : 1 ≤ s := le_of_lt (lt_of_le_of_lt hA1 hs)
          gcongr
          exact hTH s hs1)
    _ = ∫⁻ s in Ioi A, ENNReal.ofReal C * (ENNReal.ofReal (s ^ (-5 / 4 : ℝ)) * H s) :=
        setLIntegral_congr_fun measurableSet_Ioi (fun s hs => by
          have hs0 : 0 < s := lt_trans hA0 hs
          have e : ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) * ENNReal.ofReal (s ^ (1 / 4 : ℝ)) =
              ENNReal.ofReal (s ^ (-5 / 4 : ℝ)) := by
            rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hs0.le (-3 / 2 : ℝ)), ← Real.rpow_add hs0]
            norm_num
          rw [ENNReal.ofReal_mul hC0, ← e]
          ring)
    _ = ENNReal.ofReal C * ∫⁻ s in Ioi A, ENNReal.ofReal (s ^ (-5 / 4 : ℝ)) * H s :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal (A ^ (-1 / 2 : ℝ)) *
          (∫⁻ s in Ioi A, ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) * H s ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) :=
        by
          gcongr
          exact hAge A hA0 H hHm
    _ = ENNReal.ofReal (C * A ^ (-1 / 2 : ℝ)) *
          z1NormSq c mZ (fun p => if A < p.1 then T p else 0) ^ (1 / 2 : ℝ) := by
        rw [hz, ENNReal.ofReal_mul hC0]
        ring

end UnforcedLeray.Short.IIIa
